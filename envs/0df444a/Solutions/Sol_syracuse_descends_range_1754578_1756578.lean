-- Prove2me | solution 1 for syracuse_descends_range_1754578_1756578
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:37:32.196455+00:00
-- url     : https://prove2.me/submissions/86a4aa5f-4d98-473f-b709-3c9e3e3a5214

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


theorem B1974289 : Blo 1754578 1974289 := bbase (se 2 (by rfl) ⟨740358, by rfl⟩ : syracuseStep 1974289 = 1480717) (by norm_num)
theorem B1974325 : Blo 1754578 1974325 := bbase (se 5 (by rfl) ⟨92546, by rfl⟩ : syracuseStep 1974325 = 185093) (by norm_num)
theorem B3948605 : Blo 1754578 3948605 := bbase (se 3 (by rfl) ⟨740363, by rfl⟩ : syracuseStep 3948605 = 1480727) (by norm_num)
theorem B1974361 : Blo 1754578 1974361 := bbase (se 2 (by rfl) ⟨740385, by rfl⟩ : syracuseStep 1974361 = 1480771) (by norm_num)
theorem B1974397 : Blo 1754578 1974397 := bbase (se 3 (by rfl) ⟨370199, by rfl⟩ : syracuseStep 1974397 = 740399) (by norm_num)
theorem B2498693 : Blo 1754578 2498693 := bbase (se 4 (by rfl) ⟨234252, by rfl⟩ : syracuseStep 2498693 = 468505) (by norm_num)
theorem B3948677 : Blo 1754578 3948677 := bbase (se 4 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 3948677 = 740377) (by norm_num)
theorem B8888453 : Blo 1754578 8888453 := bbase (se 4 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 8888453 = 1666585) (by norm_num)
theorem B1974433 : Blo 1754578 1974433 := bbase (se 2 (by rfl) ⟨740412, by rfl⟩ : syracuseStep 1974433 = 1480825) (by norm_num)
theorem B4997285 : Blo 1754578 4997285 := bbase (se 4 (by rfl) ⟨468495, by rfl⟩ : syracuseStep 4997285 = 936991) (by norm_num)
theorem B4505765 : Blo 1754578 4505765 := bbase (se 4 (by rfl) ⟨422415, by rfl⟩ : syracuseStep 4505765 = 844831) (by norm_num)
theorem B1974469 : Blo 1754578 1974469 := bbase (se 4 (by rfl) ⟨185106, by rfl⟩ : syracuseStep 1974469 = 370213) (by norm_num)
theorem B3948749 : Blo 1754578 3948749 := bbase (se 3 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 3948749 = 1480781) (by norm_num)
theorem B6004949 : Blo 1754578 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B1974505 : Blo 1754578 1974505 := bbase (se 2 (by rfl) ⟨740439, by rfl⟩ : syracuseStep 1974505 = 1480879) (by norm_num)
theorem B1974541 : Blo 1754578 1974541 := bbase (se 3 (by rfl) ⟨370226, by rfl⟩ : syracuseStep 1974541 = 740453) (by norm_num)
theorem B3948821 : Blo 1754578 3948821 := bbase (se 6 (by rfl) ⟨92550, by rfl⟩ : syracuseStep 3948821 = 185101) (by norm_num)
theorem B1974577 : Blo 1754578 1974577 := bbase (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) (by norm_num)
theorem B1974613 : Blo 1754578 1974613 := bbase (se 10 (by rfl) ⟨2892, by rfl⟩ : syracuseStep 1974613 = 5785) (by norm_num)
theorem B3948893 : Blo 1754578 3948893 := bbase (se 3 (by rfl) ⟨740417, by rfl⟩ : syracuseStep 3948893 = 1480835) (by norm_num)
theorem B4997477 : Blo 1754578 4997477 := bbase (se 4 (by rfl) ⟨468513, by rfl⟩ : syracuseStep 4997477 = 937027) (by norm_num)
theorem B1974649 : Blo 1754578 1974649 := bbase (se 2 (by rfl) ⟨740493, by rfl⟩ : syracuseStep 1974649 = 1480987) (by norm_num)
theorem B5923205 : Blo 1754578 5923205 := bbase (se 4 (by rfl) ⟨555300, by rfl⟩ : syracuseStep 5923205 = 1110601) (by norm_num)
theorem B8438165 : Blo 1754578 8438165 := bbase (se 6 (by rfl) ⟨197769, by rfl⟩ : syracuseStep 8438165 = 395539) (by norm_num)
theorem B1974685 : Blo 1754578 1974685 := bbase (se 3 (by rfl) ⟨370253, by rfl⟩ : syracuseStep 1974685 = 740507) (by norm_num)
theorem B3948965 : Blo 1754578 3948965 := bbase (se 4 (by rfl) ⟨370215, by rfl⟩ : syracuseStep 3948965 = 740431) (by norm_num)
theorem B1974721 : Blo 1754578 1974721 := bbase (se 2 (by rfl) ⟨740520, by rfl⟩ : syracuseStep 1974721 = 1481041) (by norm_num)
theorem B3334621 : Blo 1754578 3334621 := bbase (se 3 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 3334621 = 1250483) (by norm_num)
theorem B1974757 : Blo 1754578 1974757 := bbase (se 4 (by rfl) ⟨185133, by rfl⟩ : syracuseStep 1974757 = 370267) (by norm_num)
theorem B3949037 : Blo 1754578 3949037 := bbase (se 3 (by rfl) ⟨740444, by rfl⟩ : syracuseStep 3949037 = 1480889) (by norm_num)
theorem B1974793 : Blo 1754578 1974793 := bbase (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) (by norm_num)
theorem B1974829 : Blo 1754578 1974829 := bbase (se 3 (by rfl) ⟨370280, by rfl⟩ : syracuseStep 1974829 = 740561) (by norm_num)
theorem B3949109 : Blo 1754578 3949109 := bbase (se 5 (by rfl) ⟨185114, by rfl⟩ : syracuseStep 3949109 = 370229) (by norm_num)
theorem B1974865 : Blo 1754578 1974865 := bbase (se 2 (by rfl) ⟨740574, by rfl⟩ : syracuseStep 1974865 = 1481149) (by norm_num)
theorem B8438357 : Blo 1754578 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B1974901 : Blo 1754578 1974901 := bbase (se 5 (by rfl) ⟨92573, by rfl⟩ : syracuseStep 1974901 = 185147) (by norm_num)
theorem B3949181 : Blo 1754578 3949181 := bbase (se 3 (by rfl) ⟨740471, by rfl⟩ : syracuseStep 3949181 = 1480943) (by norm_num)
theorem B1974937 : Blo 1754578 1974937 := bbase (se 2 (by rfl) ⟨740601, by rfl⟩ : syracuseStep 1974937 = 1481203) (by norm_num)
theorem B1974973 : Blo 1754578 1974973 := bbase (se 3 (by rfl) ⟨370307, by rfl⟩ : syracuseStep 1974973 = 740615) (by norm_num)
theorem B3949253 : Blo 1754578 3949253 := bbase (se 4 (by rfl) ⟨370242, by rfl⟩ : syracuseStep 3949253 = 740485) (by norm_num)
theorem B7119557 : Blo 1754578 7119557 := bbase (se 4 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 7119557 = 1334917) (by norm_num)
theorem B6669013 : Blo 1754578 6669013 := bbase (se 7 (by rfl) ⟨78152, by rfl⟩ : syracuseStep 6669013 = 156305) (by norm_num)
theorem B1975009 : Blo 1754578 1975009 := bbase (se 2 (by rfl) ⟨740628, by rfl⟩ : syracuseStep 1975009 = 1481257) (by norm_num)
theorem B6324965 : Blo 1754578 6324965 := bbase (se 4 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 6324965 = 1185931) (by norm_num)
theorem B2220797 : Blo 1754578 2220797 := bbase (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) (by norm_num)
theorem B1975045 : Blo 1754578 1975045 := bbase (se 4 (by rfl) ⟨185160, by rfl⟩ : syracuseStep 1975045 = 370321) (by norm_num)
theorem B3949325 : Blo 1754578 3949325 := bbase (se 3 (by rfl) ⟨740498, by rfl⟩ : syracuseStep 3949325 = 1480997) (by norm_num)
theorem B9012005 : Blo 1754578 9012005 := bbase (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) (by norm_num)
theorem B1975081 : Blo 1754578 1975081 := bbase (se 2 (by rfl) ⟨740655, by rfl⟩ : syracuseStep 1975081 = 1481311) (by norm_num)
theorem B2220853 : Blo 1754578 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B5923637 : Blo 1754578 5923637 := bbase (se 5 (by rfl) ⟨277670, by rfl⟩ : syracuseStep 5923637 = 555341) (by norm_num)
theorem B1975117 : Blo 1754578 1975117 := bbase (se 3 (by rfl) ⟨370334, by rfl⟩ : syracuseStep 1975117 = 740669) (by norm_num)
theorem B3949397 : Blo 1754578 3949397 := bbase (se 9 (by rfl) ⟨11570, by rfl⟩ : syracuseStep 3949397 = 23141) (by norm_num)
theorem B2810717 : Blo 1754578 2810717 := bbase (se 3 (by rfl) ⟨527009, by rfl⟩ : syracuseStep 2810717 = 1054019) (by norm_num)
theorem B2196329 : Blo 1754578 2196329 := bbase (se 2 (by rfl) ⟨823623, by rfl⟩ : syracuseStep 2196329 = 1647247) (by norm_num)
theorem B1975153 : Blo 1754578 1975153 := bbase (se 2 (by rfl) ⟨740682, by rfl⟩ : syracuseStep 1975153 = 1481365) (by norm_num)
theorem B2499445 : Blo 1754578 2499445 := bbase (se 5 (by rfl) ⟨117161, by rfl⟩ : syracuseStep 2499445 = 234323) (by norm_num)
theorem B2220949 : Blo 1754578 2220949 := bbase (se 6 (by rfl) ⟨52053, by rfl⟩ : syracuseStep 2220949 = 104107) (by norm_num)
theorem B1975189 : Blo 1754578 1975189 := bbase (se 6 (by rfl) ⟨46293, by rfl⟩ : syracuseStep 1975189 = 92587) (by norm_num)
theorem B3949469 : Blo 1754578 3949469 := bbase (se 3 (by rfl) ⟨740525, by rfl⟩ : syracuseStep 3949469 = 1481051) (by norm_num)
theorem B4219813 : Blo 1754578 4219813 := bbase (se 4 (by rfl) ⟨395607, by rfl⟩ : syracuseStep 4219813 = 791215) (by norm_num)
theorem B1975225 : Blo 1754578 1975225 := bbase (se 2 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 1975225 = 1481419) (by norm_num)
theorem B25322453 : Blo 1754578 25322453 := bbase (se 7 (by rfl) ⟨296747, by rfl⟩ : syracuseStep 25322453 = 593495) (by norm_num)
theorem B1975261 : Blo 1754578 1975261 := bbase (se 3 (by rfl) ⟨370361, by rfl⟩ : syracuseStep 1975261 = 740723) (by norm_num)
theorem B3949541 : Blo 1754578 3949541 := bbase (se 4 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 3949541 = 740539) (by norm_num)
theorem B1975297 : Blo 1754578 1975297 := bbase (se 2 (by rfl) ⟨740736, by rfl⟩ : syracuseStep 1975297 = 1481473) (by norm_num)
theorem B6669317 : Blo 1754578 6669317 := bbase (se 4 (by rfl) ⟨625248, by rfl⟩ : syracuseStep 6669317 = 1250497) (by norm_num)
theorem B1975333 : Blo 1754578 1975333 := bbase (se 4 (by rfl) ⟨185187, by rfl⟩ : syracuseStep 1975333 = 370375) (by norm_num)
theorem B3949613 : Blo 1754578 3949613 := bbase (se 3 (by rfl) ⟨740552, by rfl⟩ : syracuseStep 3949613 = 1481105) (by norm_num)
theorem B2221121 : Blo 1754578 2221121 := bbase (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) (by norm_num)
theorem B1975369 : Blo 1754578 1975369 := bbase (se 2 (by rfl) ⟨740763, by rfl⟩ : syracuseStep 1975369 = 1481527) (by norm_num)
theorem B6759509 : Blo 1754578 6759509 := bbase (se 8 (by rfl) ⟨39606, by rfl⟩ : syracuseStep 6759509 = 79213) (by norm_num)
theorem B4220005 : Blo 1754578 4220005 := bbase (se 4 (by rfl) ⟨395625, by rfl⟩ : syracuseStep 4220005 = 791251) (by norm_num)
theorem B1975405 : Blo 1754578 1975405 := bbase (se 3 (by rfl) ⟨370388, by rfl⟩ : syracuseStep 1975405 = 740777) (by norm_num)
theorem B3949685 : Blo 1754578 3949685 := bbase (se 5 (by rfl) ⟨185141, by rfl⟩ : syracuseStep 3949685 = 370283) (by norm_num)
theorem B2221177 : Blo 1754578 2221177 := bbase (se 2 (by rfl) ⟨832941, by rfl⟩ : syracuseStep 2221177 = 1665883) (by norm_num)
theorem B4220045 : Blo 1754578 4220045 := bbase (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) (by norm_num)
theorem B1975441 : Blo 1754578 1975441 := bbase (se 2 (by rfl) ⟨740790, by rfl⟩ : syracuseStep 1975441 = 1481581) (by norm_num)
theorem B1975477 : Blo 1754578 1975477 := bbase (se 5 (by rfl) ⟨92600, by rfl⟩ : syracuseStep 1975477 = 185201) (by norm_num)
theorem B3949757 : Blo 1754578 3949757 := bbase (se 3 (by rfl) ⟨740579, by rfl⟩ : syracuseStep 3949757 = 1481159) (by norm_num)
theorem B4441301 : Blo 1754578 4441301 := bbase (se 7 (by rfl) ⟨52046, by rfl⟩ : syracuseStep 4441301 = 104093) (by norm_num)
theorem B2221273 : Blo 1754578 2221273 := bbase (se 2 (by rfl) ⟨832977, by rfl⟩ : syracuseStep 2221273 = 1665955) (by norm_num)
theorem B1975513 : Blo 1754578 1975513 := bbase (se 2 (by rfl) ⟨740817, by rfl⟩ : syracuseStep 1975513 = 1481635) (by norm_num)
theorem B1778917 : Blo 1754578 1778917 := bbase (se 4 (by rfl) ⟨166773, by rfl⟩ : syracuseStep 1778917 = 333547) (by norm_num)
theorem B5924069 : Blo 1754578 5924069 := bbase (se 4 (by rfl) ⟨555381, by rfl⟩ : syracuseStep 5924069 = 1110763) (by norm_num)
theorem B1975549 : Blo 1754578 1975549 := bbase (se 3 (by rfl) ⟨370415, by rfl⟩ : syracuseStep 1975549 = 740831) (by norm_num)
theorem B3949829 : Blo 1754578 3949829 := bbase (se 4 (by rfl) ⟨370296, by rfl⟩ : syracuseStep 3949829 = 740593) (by norm_num)
theorem B1803529 : Blo 1754578 1803529 := bbase (se 2 (by rfl) ⟨676323, by rfl⟩ : syracuseStep 1803529 = 1352647) (by norm_num)
theorem B4744469 : Blo 1754578 4744469 := bbase (se 6 (by rfl) ⟨111198, by rfl⟩ : syracuseStep 4744469 = 222397) (by norm_num)
theorem B1975585 : Blo 1754578 1975585 := bbase (se 2 (by rfl) ⟨740844, by rfl⟩ : syracuseStep 1975585 = 1481689) (by norm_num)
theorem B4998469 : Blo 1754578 4998469 := bbase (se 4 (by rfl) ⟨468606, by rfl⟩ : syracuseStep 4998469 = 937213) (by norm_num)
theorem B1975621 : Blo 1754578 1975621 := bbase (se 4 (by rfl) ⟨185214, by rfl⟩ : syracuseStep 1975621 = 370429) (by norm_num)
theorem B3949901 : Blo 1754578 3949901 := bbase (se 3 (by rfl) ⟨740606, by rfl⟩ : syracuseStep 3949901 = 1481213) (by norm_num)
theorem B1975657 : Blo 1754578 1975657 := bbase (se 2 (by rfl) ⟨740871, by rfl⟩ : syracuseStep 1975657 = 1481743) (by norm_num)
theorem B4744565 : Blo 1754578 4744565 := bbase (se 5 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 4744565 = 444803) (by norm_num)
theorem B2221445 : Blo 1754578 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B1975693 : Blo 1754578 1975693 := bbase (se 3 (by rfl) ⟨370442, by rfl⟩ : syracuseStep 1975693 = 740885) (by norm_num)
theorem B4441493 : Blo 1754578 4441493 := bbase (se 6 (by rfl) ⟨104097, by rfl⟩ : syracuseStep 4441493 = 208195) (by norm_num)
theorem B3949973 : Blo 1754578 3949973 := bbase (se 6 (by rfl) ⟨92577, by rfl⟩ : syracuseStep 3949973 = 185155) (by norm_num)
theorem B8889749 : Blo 1754578 8889749 := bbase (se 6 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 8889749 = 416707) (by norm_num)
theorem B4220333 : Blo 1754578 4220333 := bbase (se 3 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 4220333 = 1582625) (by norm_num)
theorem B1975729 : Blo 1754578 1975729 := bbase (se 2 (by rfl) ⟨740898, by rfl⟩ : syracuseStep 1975729 = 1481797) (by norm_num)
theorem B2221501 : Blo 1754578 2221501 := bbase (se 3 (by rfl) ⟨416531, by rfl⟩ : syracuseStep 2221501 = 833063) (by norm_num)
theorem B7497157 : Blo 1754578 7497157 := bbase (se 4 (by rfl) ⟨702858, by rfl⟩ : syracuseStep 7497157 = 1405717) (by norm_num)
theorem B7497173 : Blo 1754578 7497173 := bbase (se 7 (by rfl) ⟨87857, by rfl⟩ : syracuseStep 7497173 = 175715) (by norm_num)
theorem B1975765 : Blo 1754578 1975765 := bbase (se 7 (by rfl) ⟨23153, by rfl⟩ : syracuseStep 1975765 = 46307) (by norm_num)
theorem B3950045 : Blo 1754578 3950045 := bbase (se 3 (by rfl) ⟨740633, by rfl⟩ : syracuseStep 3950045 = 1481267) (by norm_num)
theorem B1975801 : Blo 1754578 1975801 := bbase (se 2 (by rfl) ⟨740925, by rfl⟩ : syracuseStep 1975801 = 1481851) (by norm_num)
theorem B2221597 : Blo 1754578 2221597 := bbase (se 3 (by rfl) ⟨416549, by rfl⟩ : syracuseStep 2221597 = 833099) (by norm_num)
theorem B1975837 : Blo 1754578 1975837 := bbase (se 3 (by rfl) ⟨370469, by rfl⟩ : syracuseStep 1975837 = 740939) (by norm_num)
theorem B3950117 : Blo 1754578 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B3163693 : Blo 1754578 3163693 := bbase (se 3 (by rfl) ⟨593192, by rfl⟩ : syracuseStep 3163693 = 1186385) (by norm_num)
theorem B1975873 : Blo 1754578 1975873 := bbase (se 2 (by rfl) ⟨740952, by rfl⟩ : syracuseStep 1975873 = 1481905) (by norm_num)
theorem B1975909 : Blo 1754578 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B3950189 : Blo 1754578 3950189 := bbase (se 3 (by rfl) ⟨740660, by rfl⟩ : syracuseStep 3950189 = 1481321) (by norm_num)
theorem B1975945 : Blo 1754578 1975945 := bbase (se 2 (by rfl) ⟨740979, by rfl⟩ : syracuseStep 1975945 = 1481959) (by norm_num)
theorem B2500237 : Blo 1754578 2500237 := bbase (se 3 (by rfl) ⟨468794, by rfl⟩ : syracuseStep 2500237 = 937589) (by norm_num)
theorem B5924501 : Blo 1754578 5924501 := bbase (se 6 (by rfl) ⟨138855, by rfl⟩ : syracuseStep 5924501 = 277711) (by norm_num)
theorem B1975981 : Blo 1754578 1975981 := bbase (se 3 (by rfl) ⟨370496, by rfl⟩ : syracuseStep 1975981 = 740993) (by norm_num)
theorem B9995957 : Blo 1754578 9995957 := bbase (se 5 (by rfl) ⟨468560, by rfl⟩ : syracuseStep 9995957 = 937121) (by norm_num)
theorem B3950261 : Blo 1754578 3950261 := bbase (se 5 (by rfl) ⟨185168, by rfl⟩ : syracuseStep 3950261 = 370337) (by norm_num)
theorem B2221769 : Blo 1754578 2221769 := bbase (se 2 (by rfl) ⟨833163, by rfl⟩ : syracuseStep 2221769 = 1666327) (by norm_num)
theorem B1976017 : Blo 1754578 1976017 := bbase (se 2 (by rfl) ⟨741006, by rfl⟩ : syracuseStep 1976017 = 1482013) (by norm_num)
theorem B4441837 : Blo 1754578 4441837 := bbase (se 3 (by rfl) ⟨832844, by rfl⟩ : syracuseStep 4441837 = 1665689) (by norm_num)
theorem B1976053 : Blo 1754578 1976053 := bbase (se 5 (by rfl) ⟨92627, by rfl⟩ : syracuseStep 1976053 = 185255) (by norm_num)
theorem B3950333 : Blo 1754578 3950333 := bbase (se 3 (by rfl) ⟨740687, by rfl⟩ : syracuseStep 3950333 = 1481375) (by norm_num)
theorem B2221825 : Blo 1754578 2221825 := bbase (se 2 (by rfl) ⟨833184, by rfl⟩ : syracuseStep 2221825 = 1666369) (by norm_num)
theorem B1976089 : Blo 1754578 1976089 := bbase (se 2 (by rfl) ⟨741033, by rfl⟩ : syracuseStep 1976089 = 1482067) (by norm_num)
theorem B1976125 : Blo 1754578 1976125 := bbase (se 3 (by rfl) ⟨370523, by rfl⟩ : syracuseStep 1976125 = 741047) (by norm_num)
theorem B3950405 : Blo 1754578 3950405 := bbase (se 4 (by rfl) ⟨370350, by rfl⟩ : syracuseStep 3950405 = 740701) (by norm_num)
theorem B12658517 : Blo 1754578 12658517 := bbase (se 9 (by rfl) ⟨37085, by rfl⟩ : syracuseStep 12658517 = 74171) (by norm_num)
theorem B4441949 : Blo 1754578 4441949 := bbase (se 3 (by rfl) ⟨832865, by rfl⟩ : syracuseStep 4441949 = 1665731) (by norm_num)
theorem B2221921 : Blo 1754578 2221921 := bbase (se 2 (by rfl) ⟨833220, by rfl⟩ : syracuseStep 2221921 = 1666441) (by norm_num)
theorem B3950477 : Blo 1754578 3950477 := bbase (se 3 (by rfl) ⟨740714, by rfl⟩ : syracuseStep 3950477 = 1481429) (by norm_num)
theorem B3950549 : Blo 1754578 3950549 := bbase (se 7 (by rfl) ⟨46295, by rfl⟩ : syracuseStep 3950549 = 92591) (by norm_num)
theorem B2500573 : Blo 1754578 2500573 := bbase (se 3 (by rfl) ⟨468857, by rfl⟩ : syracuseStep 2500573 = 937715) (by norm_num)
theorem B2222093 : Blo 1754578 2222093 := bbase (se 3 (by rfl) ⟨416642, by rfl⟩ : syracuseStep 2222093 = 833285) (by norm_num)
theorem B4442141 : Blo 1754578 4442141 := bbase (se 3 (by rfl) ⟨832901, by rfl⟩ : syracuseStep 4442141 = 1665803) (by norm_num)
theorem B3950621 : Blo 1754578 3950621 := bbase (se 3 (by rfl) ⟨740741, by rfl⟩ : syracuseStep 3950621 = 1481483) (by norm_num)
theorem B13510709 : Blo 1754578 13510709 := bbase (se 5 (by rfl) ⟨633314, by rfl⟩ : syracuseStep 13510709 = 1266629) (by norm_num)
theorem B5924933 : Blo 1754578 5924933 := bbase (se 4 (by rfl) ⟨555462, by rfl⟩ : syracuseStep 5924933 = 1110925) (by norm_num)
theorem B2222149 : Blo 1754578 2222149 := bbase (se 4 (by rfl) ⟨208326, by rfl⟩ : syracuseStep 2222149 = 416653) (by norm_num)
theorem B6006869 : Blo 1754578 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B3950693 : Blo 1754578 3950693 := bbase (se 4 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 3950693 = 740755) (by norm_num)
theorem B14993525 : Blo 1754578 14993525 := bbase (se 5 (by rfl) ⟨702821, by rfl⟩ : syracuseStep 14993525 = 1405643) (by norm_num)
theorem B3377309 : Blo 1754578 3377309 := bbase (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) (by norm_num)
theorem B2222245 : Blo 1754578 2222245 := bbase (se 4 (by rfl) ⟨208335, by rfl⟩ : syracuseStep 2222245 = 416671) (by norm_num)
theorem B3557549 : Blo 1754578 3557549 := bbase (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) (by norm_num)
theorem B3950765 : Blo 1754578 3950765 := bbase (se 3 (by rfl) ⟨740768, by rfl⟩ : syracuseStep 3950765 = 1481537) (by norm_num)
theorem B2500789 : Blo 1754578 2500789 := bbase (se 5 (by rfl) ⟨117224, by rfl⟩ : syracuseStep 2500789 = 234449) (by norm_num)
theorem B2631869 : Blo 1754578 2631869 := bbase (se 3 (by rfl) ⟨493475, by rfl⟩ : syracuseStep 2631869 = 986951) (by norm_num)
theorem B2631893 : Blo 1754578 2631893 := bbase (se 7 (by rfl) ⟨30842, by rfl⟩ : syracuseStep 2631893 = 61685) (by norm_num)
theorem B2812133 : Blo 1754578 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B2631917 : Blo 1754578 2631917 := bbase (se 3 (by rfl) ⟨493484, by rfl⟩ : syracuseStep 2631917 = 986969) (by norm_num)
theorem B3950837 : Blo 1754578 3950837 := bbase (se 5 (by rfl) ⟨185195, by rfl⟩ : syracuseStep 3950837 = 370391) (by norm_num)
theorem B2631941 : Blo 1754578 2631941 := bbase (se 4 (by rfl) ⟨246744, by rfl⟩ : syracuseStep 2631941 = 493489) (by norm_num)
theorem B2631965 : Blo 1754578 2631965 := bbase (se 3 (by rfl) ⟨493493, by rfl⟩ : syracuseStep 2631965 = 986987) (by norm_num)
theorem B2631989 : Blo 1754578 2631989 := bbase (se 5 (by rfl) ⟨123374, by rfl⟩ : syracuseStep 2631989 = 246749) (by norm_num)
theorem B3950909 : Blo 1754578 3950909 := bbase (se 3 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 3950909 = 1481591) (by norm_num)
theorem B2632013 : Blo 1754578 2632013 := bbase (se 3 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 2632013 = 987005) (by norm_num)
theorem B2222417 : Blo 1754578 2222417 := bbase (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) (by norm_num)
theorem B3164501 : Blo 1754578 3164501 := bbase (se 10 (by rfl) ⟨4635, by rfl⟩ : syracuseStep 3164501 = 9271) (by norm_num)
theorem B2632037 : Blo 1754578 2632037 := bbase (se 4 (by rfl) ⟨246753, by rfl⟩ : syracuseStep 2632037 = 493507) (by norm_num)
theorem B4442485 : Blo 1754578 4442485 := bbase (se 5 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 4442485 = 416483) (by norm_num)
theorem B2632061 : Blo 1754578 2632061 := bbase (se 3 (by rfl) ⟨493511, by rfl⟩ : syracuseStep 2632061 = 987023) (by norm_num)
theorem B3950981 : Blo 1754578 3950981 := bbase (se 4 (by rfl) ⟨370404, by rfl⟩ : syracuseStep 3950981 = 740809) (by norm_num)
theorem B2222473 : Blo 1754578 2222473 := bbase (se 2 (by rfl) ⟨833427, by rfl⟩ : syracuseStep 2222473 = 1666855) (by norm_num)
theorem B2632085 : Blo 1754578 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B4999573 : Blo 1754578 4999573 := bbase (se 6 (by rfl) ⟨117177, by rfl⟩ : syracuseStep 4999573 = 234355) (by norm_num)
theorem B2632109 : Blo 1754578 2632109 := bbase (se 3 (by rfl) ⟨493520, by rfl⟩ : syracuseStep 2632109 = 987041) (by norm_num)
theorem B2632133 : Blo 1754578 2632133 := bbase (se 4 (by rfl) ⟨246762, by rfl⟩ : syracuseStep 2632133 = 493525) (by norm_num)
theorem B2812357 : Blo 1754578 2812357 := bbase (se 4 (by rfl) ⟨263658, by rfl⟩ : syracuseStep 2812357 = 527317) (by norm_num)
theorem B3951053 : Blo 1754578 3951053 := bbase (se 3 (by rfl) ⟨740822, by rfl⟩ : syracuseStep 3951053 = 1481645) (by norm_num)
theorem B2632157 : Blo 1754578 2632157 := bbase (se 3 (by rfl) ⟨493529, by rfl⟩ : syracuseStep 2632157 = 987059) (by norm_num)
theorem B4442597 : Blo 1754578 4442597 := bbase (se 4 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 4442597 = 832987) (by norm_num)
theorem B2222569 : Blo 1754578 2222569 := bbase (se 2 (by rfl) ⟨833463, by rfl⟩ : syracuseStep 2222569 = 1666927) (by norm_num)
theorem B2632181 : Blo 1754578 2632181 := bbase (se 5 (by rfl) ⟨123383, by rfl⟩ : syracuseStep 2632181 = 246767) (by norm_num)
theorem B5925365 : Blo 1754578 5925365 := bbase (se 5 (by rfl) ⟨277751, by rfl⟩ : syracuseStep 5925365 = 555503) (by norm_num)
theorem B2632205 : Blo 1754578 2632205 := bbase (se 3 (by rfl) ⟨493538, by rfl⟩ : syracuseStep 2632205 = 987077) (by norm_num)
theorem B3951125 : Blo 1754578 3951125 := bbase (se 6 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 3951125 = 185209) (by norm_num)
theorem B2632229 : Blo 1754578 2632229 := bbase (se 4 (by rfl) ⟨246771, by rfl⟩ : syracuseStep 2632229 = 493543) (by norm_num)
theorem B2632253 : Blo 1754578 2632253 := bbase (se 3 (by rfl) ⟨493547, by rfl⟩ : syracuseStep 2632253 = 987095) (by norm_num)
theorem B2632277 : Blo 1754578 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B3951197 : Blo 1754578 3951197 := bbase (se 3 (by rfl) ⟨740849, by rfl⟩ : syracuseStep 3951197 = 1481699) (by norm_num)
theorem B2632301 : Blo 1754578 2632301 := bbase (se 3 (by rfl) ⟨493556, by rfl⟩ : syracuseStep 2632301 = 987113) (by norm_num)
theorem B2632325 : Blo 1754578 2632325 := bbase (se 4 (by rfl) ⟨246780, by rfl⟩ : syracuseStep 2632325 = 493561) (by norm_num)
theorem B2001541 : Blo 1754578 2001541 := bbase (se 4 (by rfl) ⟨187644, by rfl⟩ : syracuseStep 2001541 = 375289) (by norm_num)
theorem B8440453 : Blo 1754578 8440453 := bbase (se 4 (by rfl) ⟨791292, by rfl⟩ : syracuseStep 8440453 = 1582585) (by norm_num)
theorem B2222741 : Blo 1754578 2222741 := bbase (se 6 (by rfl) ⟨52095, by rfl⟩ : syracuseStep 2222741 = 104191) (by norm_num)
theorem B2632349 : Blo 1754578 2632349 := bbase (se 3 (by rfl) ⟨493565, by rfl⟩ : syracuseStep 2632349 = 987131) (by norm_num)
theorem B4442789 : Blo 1754578 4442789 := bbase (se 4 (by rfl) ⟨416511, by rfl⟩ : syracuseStep 4442789 = 833023) (by norm_num)
theorem B3951269 : Blo 1754578 3951269 := bbase (se 4 (by rfl) ⟨370431, by rfl⟩ : syracuseStep 3951269 = 740863) (by norm_num)
theorem B8891045 : Blo 1754578 8891045 := bbase (se 4 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 8891045 = 1667071) (by norm_num)
theorem B2632373 : Blo 1754578 2632373 := bbase (se 5 (by rfl) ⟨123392, by rfl⟩ : syracuseStep 2632373 = 246785) (by norm_num)
theorem B2632397 : Blo 1754578 2632397 := bbase (se 3 (by rfl) ⟨493574, by rfl⟩ : syracuseStep 2632397 = 987149) (by norm_num)
theorem B2222797 : Blo 1754578 2222797 := bbase (se 3 (by rfl) ⟨416774, by rfl⟩ : syracuseStep 2222797 = 833549) (by norm_num)
theorem B1780429 : Blo 1754578 1780429 := bbase (se 3 (by rfl) ⟨333830, by rfl⟩ : syracuseStep 1780429 = 667661) (by norm_num)
theorem B2632421 : Blo 1754578 2632421 := bbase (se 4 (by rfl) ⟨246789, by rfl⟩ : syracuseStep 2632421 = 493579) (by norm_num)
theorem B3951341 : Blo 1754578 3951341 := bbase (se 3 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 3951341 = 1481753) (by norm_num)
theorem B2632445 : Blo 1754578 2632445 := bbase (se 3 (by rfl) ⟨493583, by rfl⟩ : syracuseStep 2632445 = 987167) (by norm_num)
theorem B2632469 : Blo 1754578 2632469 := bbase (se 6 (by rfl) ⟨61698, by rfl⟩ : syracuseStep 2632469 = 123397) (by norm_num)
theorem B2632493 : Blo 1754578 2632493 := bbase (se 3 (by rfl) ⟨493592, by rfl⟩ : syracuseStep 2632493 = 987185) (by norm_num)
theorem B2222893 : Blo 1754578 2222893 := bbase (se 3 (by rfl) ⟨416792, by rfl⟩ : syracuseStep 2222893 = 833585) (by norm_num)
theorem B3951413 : Blo 1754578 3951413 := bbase (se 5 (by rfl) ⟨185222, by rfl⟩ : syracuseStep 3951413 = 370445) (by norm_num)
theorem B2632517 : Blo 1754578 2632517 := bbase (se 4 (by rfl) ⟨246798, by rfl⟩ : syracuseStep 2632517 = 493597) (by norm_num)
theorem B9997141 : Blo 1754578 9997141 := bbase (se 9 (by rfl) ⟨29288, by rfl⟩ : syracuseStep 9997141 = 58577) (by norm_num)
theorem B6327125 : Blo 1754578 6327125 := bbase (se 9 (by rfl) ⟨18536, by rfl⟩ : syracuseStep 6327125 = 37073) (by norm_num)
theorem B2632541 : Blo 1754578 2632541 := bbase (se 3 (by rfl) ⟨493601, by rfl⟩ : syracuseStep 2632541 = 987203) (by norm_num)
theorem B2632565 : Blo 1754578 2632565 := bbase (se 5 (by rfl) ⟨123401, by rfl⟩ : syracuseStep 2632565 = 246803) (by norm_num)
theorem B3951485 : Blo 1754578 3951485 := bbase (se 3 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 3951485 = 1481807) (by norm_num)
theorem B2632589 : Blo 1754578 2632589 := bbase (se 3 (by rfl) ⟨493610, by rfl⟩ : syracuseStep 2632589 = 987221) (by norm_num)
theorem B3165077 : Blo 1754578 3165077 := bbase (se 6 (by rfl) ⟨74181, by rfl⟩ : syracuseStep 3165077 = 148363) (by norm_num)
theorem B2632613 : Blo 1754578 2632613 := bbase (se 4 (by rfl) ⟨246807, by rfl⟩ : syracuseStep 2632613 = 493615) (by norm_num)
theorem B5925797 : Blo 1754578 5925797 := bbase (se 4 (by rfl) ⟨555543, by rfl⟩ : syracuseStep 5925797 = 1111087) (by norm_num)
theorem B2632637 : Blo 1754578 2632637 := bbase (se 3 (by rfl) ⟨493619, by rfl⟩ : syracuseStep 2632637 = 987239) (by norm_num)
theorem B3951557 : Blo 1754578 3951557 := bbase (se 4 (by rfl) ⟨370458, by rfl⟩ : syracuseStep 3951557 = 740917) (by norm_num)
theorem B2108369 : Blo 1754578 2108369 := bbase (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) (by norm_num)
theorem B2632661 : Blo 1754578 2632661 := bbase (se 7 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 2632661 = 61703) (by norm_num)
theorem B2223065 : Blo 1754578 2223065 := bbase (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) (by norm_num)
theorem B2632685 : Blo 1754578 2632685 := bbase (se 3 (by rfl) ⟨493628, by rfl⟩ : syracuseStep 2632685 = 987257) (by norm_num)
theorem B4443133 : Blo 1754578 4443133 := bbase (se 3 (by rfl) ⟨833087, by rfl⟩ : syracuseStep 4443133 = 1666175) (by norm_num)
theorem B2632709 : Blo 1754578 2632709 := bbase (se 4 (by rfl) ⟨246816, by rfl⟩ : syracuseStep 2632709 = 493633) (by norm_num)
theorem B3951629 : Blo 1754578 3951629 := bbase (se 3 (by rfl) ⟨740930, by rfl⟩ : syracuseStep 3951629 = 1481861) (by norm_num)
theorem B2223121 : Blo 1754578 2223121 := bbase (se 2 (by rfl) ⟨833670, by rfl⟩ : syracuseStep 2223121 = 1667341) (by norm_num)
theorem B2632733 : Blo 1754578 2632733 := bbase (se 3 (by rfl) ⟨493637, by rfl⟩ : syracuseStep 2632733 = 987275) (by norm_num)
theorem B2632757 : Blo 1754578 2632757 := bbase (se 5 (by rfl) ⟨123410, by rfl⟩ : syracuseStep 2632757 = 246821) (by norm_num)
theorem B8883269 : Blo 1754578 8883269 := bbase (se 4 (by rfl) ⟨832806, by rfl⟩ : syracuseStep 8883269 = 1665613) (by norm_num)
theorem B2632781 : Blo 1754578 2632781 := bbase (se 3 (by rfl) ⟨493646, by rfl⟩ : syracuseStep 2632781 = 987293) (by norm_num)
theorem B3951701 : Blo 1754578 3951701 := bbase (se 8 (by rfl) ⟨23154, by rfl⟩ : syracuseStep 3951701 = 46309) (by norm_num)
theorem B2632805 : Blo 1754578 2632805 := bbase (se 4 (by rfl) ⟨246825, by rfl⟩ : syracuseStep 2632805 = 493651) (by norm_num)
theorem B4443245 : Blo 1754578 4443245 := bbase (se 3 (by rfl) ⟨833108, by rfl⟩ : syracuseStep 4443245 = 1666217) (by norm_num)
theorem B6327413 : Blo 1754578 6327413 := bbase (se 5 (by rfl) ⟨296597, by rfl⟩ : syracuseStep 6327413 = 593195) (by norm_num)
theorem B2632829 : Blo 1754578 2632829 := bbase (se 3 (by rfl) ⟨493655, by rfl⟩ : syracuseStep 2632829 = 987311) (by norm_num)
theorem B2632853 : Blo 1754578 2632853 := bbase (se 6 (by rfl) ⟨61707, by rfl⟩ : syracuseStep 2632853 = 123415) (by norm_num)
theorem B3951773 : Blo 1754578 3951773 := bbase (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) (by norm_num)
theorem B2632877 : Blo 1754578 2632877 := bbase (se 3 (by rfl) ⟨493664, by rfl⟩ : syracuseStep 2632877 = 987329) (by norm_num)
theorem B2632901 : Blo 1754578 2632901 := bbase (se 4 (by rfl) ⟨246834, by rfl⟩ : syracuseStep 2632901 = 493669) (by norm_num)
theorem B2108629 : Blo 1754578 2108629 := bbase (se 7 (by rfl) ⟨24710, by rfl⟩ : syracuseStep 2108629 = 49421) (by norm_num)
theorem B2632925 : Blo 1754578 2632925 := bbase (se 3 (by rfl) ⟨493673, by rfl⟩ : syracuseStep 2632925 = 987347) (by norm_num)
theorem B3951845 : Blo 1754578 3951845 := bbase (se 4 (by rfl) ⟨370485, by rfl⟩ : syracuseStep 3951845 = 740971) (by norm_num)
theorem B2632949 : Blo 1754578 2632949 := bbase (se 5 (by rfl) ⟨123419, by rfl⟩ : syracuseStep 2632949 = 246839) (by norm_num)
theorem B2632973 : Blo 1754578 2632973 := bbase (se 3 (by rfl) ⟨493682, by rfl⟩ : syracuseStep 2632973 = 987365) (by norm_num)
theorem B3378461 : Blo 1754578 3378461 := bbase (se 3 (by rfl) ⟨633461, by rfl⟩ : syracuseStep 3378461 = 1266923) (by norm_num)
theorem B2632997 : Blo 1754578 2632997 := bbase (se 4 (by rfl) ⟨246843, by rfl⟩ : syracuseStep 2632997 = 493687) (by norm_num)
theorem B4443437 : Blo 1754578 4443437 := bbase (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) (by norm_num)
theorem B3951917 : Blo 1754578 3951917 := bbase (se 3 (by rfl) ⟨740984, by rfl⟩ : syracuseStep 3951917 = 1481969) (by norm_num)
theorem B2633021 : Blo 1754578 2633021 := bbase (se 3 (by rfl) ⟨493691, by rfl⟩ : syracuseStep 2633021 = 987383) (by norm_num)
theorem B25300309 : Blo 1754578 25300309 := bbase (se 11 (by rfl) ⟨18530, by rfl⟩ : syracuseStep 25300309 = 37061) (by norm_num)
theorem B2633045 : Blo 1754578 2633045 := bbase (se 11 (by rfl) ⟨1928, by rfl⟩ : syracuseStep 2633045 = 3857) (by norm_num)
theorem B5926229 : Blo 1754578 5926229 := bbase (se 11 (by rfl) ⟨4340, by rfl⟩ : syracuseStep 5926229 = 8681) (by norm_num)
theorem B2633069 : Blo 1754578 2633069 := bbase (se 3 (by rfl) ⟨493700, by rfl⟩ : syracuseStep 2633069 = 987401) (by norm_num)
theorem B3951989 : Blo 1754578 3951989 := bbase (se 5 (by rfl) ⟨185249, by rfl⟩ : syracuseStep 3951989 = 370499) (by norm_num)
theorem B2633093 : Blo 1754578 2633093 := bbase (se 4 (by rfl) ⟨246852, by rfl⟩ : syracuseStep 2633093 = 493705) (by norm_num)
theorem B2108821 : Blo 1754578 2108821 := bbase (se 6 (by rfl) ⟨49425, by rfl⟩ : syracuseStep 2108821 = 98851) (by norm_num)
theorem B2633117 : Blo 1754578 2633117 := bbase (se 3 (by rfl) ⟨493709, by rfl⟩ : syracuseStep 2633117 = 987419) (by norm_num)
theorem B2108845 : Blo 1754578 2108845 := bbase (se 3 (by rfl) ⟨395408, by rfl⟩ : syracuseStep 2108845 = 790817) (by norm_num)
theorem B2108849 : Blo 1754578 2108849 := bbase (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) (by norm_num)
theorem B2633141 : Blo 1754578 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B3952061 : Blo 1754578 3952061 := bbase (se 3 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 3952061 = 1482023) (by norm_num)
theorem B2633165 : Blo 1754578 2633165 := bbase (se 3 (by rfl) ⟨493718, by rfl⟩ : syracuseStep 2633165 = 987437) (by norm_num)
theorem B6663653 : Blo 1754578 6663653 := bbase (se 4 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 6663653 = 1249435) (by norm_num)
theorem B2633189 : Blo 1754578 2633189 := bbase (se 4 (by rfl) ⟨246861, by rfl⟩ : syracuseStep 2633189 = 493723) (by norm_num)
theorem B2633213 : Blo 1754578 2633213 := bbase (se 3 (by rfl) ⟨493727, by rfl⟩ : syracuseStep 2633213 = 987455) (by norm_num)
theorem B3952133 : Blo 1754578 3952133 := bbase (se 4 (by rfl) ⟨370512, by rfl⟩ : syracuseStep 3952133 = 741025) (by norm_num)
theorem B2633237 : Blo 1754578 2633237 := bbase (se 6 (by rfl) ⟨61716, by rfl⟩ : syracuseStep 2633237 = 123433) (by norm_num)
theorem B2960941 : Blo 1754578 2960941 := bbase (se 3 (by rfl) ⟨555176, by rfl⟩ : syracuseStep 2960941 = 1110353) (by norm_num)
theorem B2633261 : Blo 1754578 2633261 := bbase (se 3 (by rfl) ⟨493736, by rfl⟩ : syracuseStep 2633261 = 987473) (by norm_num)
theorem B2002489 : Blo 1754578 2002489 := bbase (se 2 (by rfl) ⟨750933, by rfl⟩ : syracuseStep 2002489 = 1501867) (by norm_num)
theorem B2633285 : Blo 1754578 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B3952205 : Blo 1754578 3952205 := bbase (se 3 (by rfl) ⟨741038, by rfl⟩ : syracuseStep 3952205 = 1482077) (by norm_num)
theorem B2633309 : Blo 1754578 2633309 := bbase (se 3 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 2633309 = 987491) (by norm_num)
theorem B2633333 : Blo 1754578 2633333 := bbase (se 5 (by rfl) ⟨123437, by rfl⟩ : syracuseStep 2633333 = 246875) (by norm_num)
theorem B2961029 : Blo 1754578 2961029 := bbase (se 4 (by rfl) ⟨277596, by rfl⟩ : syracuseStep 2961029 = 555193) (by norm_num)
theorem B4443781 : Blo 1754578 4443781 := bbase (se 4 (by rfl) ⟨416604, by rfl⟩ : syracuseStep 4443781 = 833209) (by norm_num)
theorem B2633357 : Blo 1754578 2633357 := bbase (se 3 (by rfl) ⟨493754, by rfl⟩ : syracuseStep 2633357 = 987509) (by norm_num)
theorem B5623445 : Blo 1754578 5623445 := bbase (se 6 (by rfl) ⟨131799, by rfl⟩ : syracuseStep 5623445 = 263599) (by norm_num)
theorem B3952277 : Blo 1754578 3952277 := bbase (se 6 (by rfl) ⟨92631, by rfl⟩ : syracuseStep 3952277 = 185263) (by norm_num)
theorem B3747485 : Blo 1754578 3747485 := bbase (se 3 (by rfl) ⟨702653, by rfl⟩ : syracuseStep 3747485 = 1405307) (by norm_num)
theorem B3747493 : Blo 1754578 3747493 := bbase (se 4 (by rfl) ⟨351327, by rfl⟩ : syracuseStep 3747493 = 702655) (by norm_num)
theorem B2633381 : Blo 1754578 2633381 := bbase (se 4 (by rfl) ⟨246879, by rfl⟩ : syracuseStep 2633381 = 493759) (by norm_num)
theorem B7499429 : Blo 1754578 7499429 := bbase (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) (by norm_num)
theorem B2633405 : Blo 1754578 2633405 := bbase (se 3 (by rfl) ⟨493763, by rfl⟩ : syracuseStep 2633405 = 987527) (by norm_num)
theorem B2166469 : Blo 1754578 2166469 := bbase (se 4 (by rfl) ⟨203106, by rfl⟩ : syracuseStep 2166469 = 406213) (by norm_num)
theorem B2633429 : Blo 1754578 2633429 := bbase (se 7 (by rfl) ⟨30860, by rfl⟩ : syracuseStep 2633429 = 61721) (by norm_num)
theorem B2633453 : Blo 1754578 2633453 := bbase (se 3 (by rfl) ⟨493772, by rfl⟩ : syracuseStep 2633453 = 987545) (by norm_num)
theorem B4443893 : Blo 1754578 4443893 := bbase (se 5 (by rfl) ⟨208307, by rfl⟩ : syracuseStep 4443893 = 416615) (by norm_num)
theorem B2961157 : Blo 1754578 2961157 := bbase (se 4 (by rfl) ⟨277608, by rfl⟩ : syracuseStep 2961157 = 555217) (by norm_num)
theorem B6663941 : Blo 1754578 6663941 := bbase (se 4 (by rfl) ⟨624744, by rfl⟩ : syracuseStep 6663941 = 1249489) (by norm_num)
theorem B2633477 : Blo 1754578 2633477 := bbase (se 4 (by rfl) ⟨246888, by rfl⟩ : syracuseStep 2633477 = 493777) (by norm_num)
theorem B5926661 : Blo 1754578 5926661 := bbase (se 4 (by rfl) ⟨555624, by rfl⟩ : syracuseStep 5926661 = 1111249) (by norm_num)
theorem B2633501 : Blo 1754578 2633501 := bbase (se 3 (by rfl) ⟨493781, by rfl⟩ : syracuseStep 2633501 = 987563) (by norm_num)
theorem B2633525 : Blo 1754578 2633525 := bbase (se 5 (by rfl) ⟨123446, by rfl⟩ : syracuseStep 2633525 = 246893) (by norm_num)
theorem B2633549 : Blo 1754578 2633549 := bbase (se 3 (by rfl) ⟨493790, by rfl⟩ : syracuseStep 2633549 = 987581) (by norm_num)
theorem B2961245 : Blo 1754578 2961245 := bbase (se 3 (by rfl) ⟨555233, by rfl⟩ : syracuseStep 2961245 = 1110467) (by norm_num)
theorem B2002781 : Blo 1754578 2002781 := bbase (se 3 (by rfl) ⟨375521, by rfl⟩ : syracuseStep 2002781 = 751043) (by norm_num)
theorem B2633573 : Blo 1754578 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B5001077 : Blo 1754578 5001077 := bbase (se 5 (by rfl) ⟨234425, by rfl⟩ : syracuseStep 5001077 = 468851) (by norm_num)
theorem B2633597 : Blo 1754578 2633597 := bbase (se 3 (by rfl) ⟨493799, by rfl⟩ : syracuseStep 2633597 = 987599) (by norm_num)
theorem B2633621 : Blo 1754578 2633621 := bbase (se 6 (by rfl) ⟨61725, by rfl⟩ : syracuseStep 2633621 = 123451) (by norm_num)
theorem B2109349 : Blo 1754578 2109349 := bbase (se 4 (by rfl) ⟨197751, by rfl⟩ : syracuseStep 2109349 = 395503) (by norm_num)
theorem B2633645 : Blo 1754578 2633645 := bbase (se 3 (by rfl) ⟨493808, by rfl⟩ : syracuseStep 2633645 = 987617) (by norm_num)
theorem B4444085 : Blo 1754578 4444085 := bbase (se 5 (by rfl) ⟨208316, by rfl⟩ : syracuseStep 4444085 = 416633) (by norm_num)
theorem B8892341 : Blo 1754578 8892341 := bbase (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) (by norm_num)
theorem B2633669 : Blo 1754578 2633669 := bbase (se 4 (by rfl) ⟨246906, by rfl⟩ : syracuseStep 2633669 = 493813) (by norm_num)
theorem B13332437 : Blo 1754578 13332437 := bbase (se 7 (by rfl) ⟨156239, by rfl⟩ : syracuseStep 13332437 = 312479) (by norm_num)
theorem B2961373 : Blo 1754578 2961373 := bbase (se 3 (by rfl) ⟨555257, by rfl⟩ : syracuseStep 2961373 = 1110515) (by norm_num)
theorem B2633693 : Blo 1754578 2633693 := bbase (se 3 (by rfl) ⟨493817, by rfl⟩ : syracuseStep 2633693 = 987635) (by norm_num)
theorem B2002909 : Blo 1754578 2002909 := bbase (se 3 (by rfl) ⟨375545, by rfl⟩ : syracuseStep 2002909 = 751091) (by norm_num)
theorem B2633717 : Blo 1754578 2633717 := bbase (se 5 (by rfl) ⟨123455, by rfl⟩ : syracuseStep 2633717 = 246911) (by norm_num)
theorem B2109445 : Blo 1754578 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B2633741 : Blo 1754578 2633741 := bbase (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) (by norm_num)
theorem B2633765 : Blo 1754578 2633765 := bbase (se 4 (by rfl) ⟨246915, by rfl⟩ : syracuseStep 2633765 = 493831) (by norm_num)
theorem B2961461 : Blo 1754578 2961461 := bbase (se 5 (by rfl) ⟨138818, by rfl⟩ : syracuseStep 2961461 = 277637) (by norm_num)
theorem B2633789 : Blo 1754578 2633789 := bbase (se 3 (by rfl) ⟨493835, by rfl⟩ : syracuseStep 2633789 = 987671) (by norm_num)
theorem B2633813 : Blo 1754578 2633813 := bbase (se 8 (by rfl) ⟨15432, by rfl⟩ : syracuseStep 2633813 = 30865) (by norm_num)
theorem B2633837 : Blo 1754578 2633837 := bbase (se 3 (by rfl) ⟨493844, by rfl⟩ : syracuseStep 2633837 = 987689) (by norm_num)
theorem B2404469 : Blo 1754578 2404469 := bbase (se 5 (by rfl) ⟨112709, by rfl⟩ : syracuseStep 2404469 = 225419) (by norm_num)
theorem B2633861 : Blo 1754578 2633861 := bbase (se 4 (by rfl) ⟨246924, by rfl⟩ : syracuseStep 2633861 = 493849) (by norm_num)
theorem B2633885 : Blo 1754578 2633885 := bbase (se 3 (by rfl) ⟨493853, by rfl⟩ : syracuseStep 2633885 = 987707) (by norm_num)
theorem B2961589 : Blo 1754578 2961589 := bbase (se 5 (by rfl) ⟨138824, by rfl⟩ : syracuseStep 2961589 = 277649) (by norm_num)
theorem B2633909 : Blo 1754578 2633909 := bbase (se 5 (by rfl) ⟨123464, by rfl⟩ : syracuseStep 2633909 = 246929) (by norm_num)
theorem B5927093 : Blo 1754578 5927093 := bbase (se 5 (by rfl) ⟨277832, by rfl⟩ : syracuseStep 5927093 = 555665) (by norm_num)
theorem B2633933 : Blo 1754578 2633933 := bbase (se 3 (by rfl) ⟨493862, by rfl⟩ : syracuseStep 2633933 = 987725) (by norm_num)
theorem B4002005 : Blo 1754578 4002005 := bbase (se 7 (by rfl) ⟨46898, by rfl⟩ : syracuseStep 4002005 = 93797) (by norm_num)
theorem B2633957 : Blo 1754578 2633957 := bbase (se 4 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 2633957 = 493867) (by norm_num)
theorem B2633981 : Blo 1754578 2633981 := bbase (se 3 (by rfl) ⟨493871, by rfl⟩ : syracuseStep 2633981 = 987743) (by norm_num)
theorem B2961677 : Blo 1754578 2961677 := bbase (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) (by norm_num)
theorem B4444429 : Blo 1754578 4444429 := bbase (se 3 (by rfl) ⟨833330, by rfl⟩ : syracuseStep 4444429 = 1666661) (by norm_num)
theorem B2634005 : Blo 1754578 2634005 := bbase (se 6 (by rfl) ⟨61734, by rfl⟩ : syracuseStep 2634005 = 123469) (by norm_num)
theorem B2634029 : Blo 1754578 2634029 := bbase (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) (by norm_num)
theorem B2634053 : Blo 1754578 2634053 := bbase (se 4 (by rfl) ⟨246942, by rfl⟩ : syracuseStep 2634053 = 493885) (by norm_num)
theorem B8884565 : Blo 1754578 8884565 := bbase (se 10 (by rfl) ⟨13014, by rfl⟩ : syracuseStep 8884565 = 26029) (by norm_num)
theorem B2634077 : Blo 1754578 2634077 := bbase (se 3 (by rfl) ⟨493889, by rfl⟩ : syracuseStep 2634077 = 987779) (by norm_num)
theorem B13324661 : Blo 1754578 13324661 := bbase (se 5 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 13324661 = 1249187) (by norm_num)
theorem B2634101 : Blo 1754578 2634101 := bbase (se 5 (by rfl) ⟨123473, by rfl⟩ : syracuseStep 2634101 = 246947) (by norm_num)
theorem B4444541 : Blo 1754578 4444541 := bbase (se 3 (by rfl) ⟨833351, by rfl⟩ : syracuseStep 4444541 = 1666703) (by norm_num)
theorem B2961805 : Blo 1754578 2961805 := bbase (se 3 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 2961805 = 1110677) (by norm_num)
theorem B2634125 : Blo 1754578 2634125 := bbase (se 3 (by rfl) ⟨493898, by rfl⟩ : syracuseStep 2634125 = 987797) (by norm_num)
theorem B2634149 : Blo 1754578 2634149 := bbase (se 4 (by rfl) ⟨246951, by rfl⟩ : syracuseStep 2634149 = 493903) (by norm_num)
theorem B2634173 : Blo 1754578 2634173 := bbase (se 3 (by rfl) ⟨493907, by rfl⟩ : syracuseStep 2634173 = 987815) (by norm_num)
theorem B2634197 : Blo 1754578 2634197 := bbase (se 7 (by rfl) ⟨30869, by rfl⟩ : syracuseStep 2634197 = 61739) (by norm_num)
theorem B2961893 : Blo 1754578 2961893 := bbase (se 4 (by rfl) ⟨277677, by rfl⟩ : syracuseStep 2961893 = 555355) (by norm_num)
theorem B2634221 : Blo 1754578 2634221 := bbase (se 3 (by rfl) ⟨493916, by rfl⟩ : syracuseStep 2634221 = 987833) (by norm_num)
theorem B2634245 : Blo 1754578 2634245 := bbase (se 4 (by rfl) ⟨246960, by rfl⟩ : syracuseStep 2634245 = 493921) (by norm_num)
theorem B4002317 : Blo 1754578 4002317 := bbase (se 3 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 4002317 = 1500869) (by norm_num)
theorem B2634269 : Blo 1754578 2634269 := bbase (se 3 (by rfl) ⟨493925, by rfl⟩ : syracuseStep 2634269 = 987851) (by norm_num)
theorem B2634293 : Blo 1754578 2634293 := bbase (se 5 (by rfl) ⟨123482, by rfl⟩ : syracuseStep 2634293 = 246965) (by norm_num)
theorem B4444733 : Blo 1754578 4444733 := bbase (se 3 (by rfl) ⟨833387, by rfl⟩ : syracuseStep 4444733 = 1666775) (by norm_num)
theorem B2634317 : Blo 1754578 2634317 := bbase (se 3 (by rfl) ⟨493934, by rfl⟩ : syracuseStep 2634317 = 987869) (by norm_num)
theorem B2962021 : Blo 1754578 2962021 := bbase (se 4 (by rfl) ⟨277689, by rfl⟩ : syracuseStep 2962021 = 555379) (by norm_num)
theorem B2634341 : Blo 1754578 2634341 := bbase (se 4 (by rfl) ⟨246969, by rfl⟩ : syracuseStep 2634341 = 493939) (by norm_num)
theorem B5927525 : Blo 1754578 5927525 := bbase (se 4 (by rfl) ⟨555705, by rfl⟩ : syracuseStep 5927525 = 1111411) (by norm_num)
theorem B2634365 : Blo 1754578 2634365 := bbase (se 3 (by rfl) ⟨493943, by rfl⟩ : syracuseStep 2634365 = 987887) (by norm_num)
theorem B2634389 : Blo 1754578 2634389 := bbase (se 6 (by rfl) ⟨61743, by rfl⟩ : syracuseStep 2634389 = 123487) (by norm_num)
theorem B3043997 : Blo 1754578 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B2372261 : Blo 1754578 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B2634413 : Blo 1754578 2634413 := bbase (se 3 (by rfl) ⟨493952, by rfl⟩ : syracuseStep 2634413 = 987905) (by norm_num)
theorem B2962109 : Blo 1754578 2962109 := bbase (se 3 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 2962109 = 1110791) (by norm_num)
theorem B2634437 : Blo 1754578 2634437 := bbase (se 4 (by rfl) ⟨246978, by rfl⟩ : syracuseStep 2634437 = 493957) (by norm_num)
theorem B2634461 : Blo 1754578 2634461 := bbase (se 3 (by rfl) ⟨493961, by rfl⟩ : syracuseStep 2634461 = 987923) (by norm_num)
theorem B2634485 : Blo 1754578 2634485 := bbase (se 5 (by rfl) ⟨123491, by rfl⟩ : syracuseStep 2634485 = 246983) (by norm_num)
theorem B3748621 : Blo 1754578 3748621 := bbase (se 3 (by rfl) ⟨702866, by rfl⟩ : syracuseStep 3748621 = 1405733) (by norm_num)
theorem B2634509 : Blo 1754578 2634509 := bbase (se 3 (by rfl) ⟨493970, by rfl⟩ : syracuseStep 2634509 = 987941) (by norm_num)
theorem B9999125 : Blo 1754578 9999125 := bbase (se 6 (by rfl) ⟨234354, by rfl⟩ : syracuseStep 9999125 = 468709) (by norm_num)
theorem B2634533 : Blo 1754578 2634533 := bbase (se 4 (by rfl) ⟨246987, by rfl⟩ : syracuseStep 2634533 = 493975) (by norm_num)
theorem B4502317 : Blo 1754578 4502317 := bbase (se 3 (by rfl) ⟨844184, by rfl⟩ : syracuseStep 4502317 = 1688369) (by norm_num)
theorem B2962237 : Blo 1754578 2962237 := bbase (se 3 (by rfl) ⟨555419, by rfl⟩ : syracuseStep 2962237 = 1110839) (by norm_num)
theorem B2634557 : Blo 1754578 2634557 := bbase (se 3 (by rfl) ⟨493979, by rfl⟩ : syracuseStep 2634557 = 987959) (by norm_num)
theorem B2634581 : Blo 1754578 2634581 := bbase (se 9 (by rfl) ⟨7718, by rfl⟩ : syracuseStep 2634581 = 15437) (by norm_num)
theorem B2634605 : Blo 1754578 2634605 := bbase (se 3 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 2634605 = 987977) (by norm_num)
theorem B2634629 : Blo 1754578 2634629 := bbase (se 4 (by rfl) ⟨246996, by rfl⟩ : syracuseStep 2634629 = 493993) (by norm_num)
theorem B2962325 : Blo 1754578 2962325 := bbase (se 6 (by rfl) ⟨69429, by rfl⟩ : syracuseStep 2962325 = 138859) (by norm_num)
theorem B4445077 : Blo 1754578 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B2634653 : Blo 1754578 2634653 := bbase (se 3 (by rfl) ⟨493997, by rfl⟩ : syracuseStep 2634653 = 987995) (by norm_num)
theorem B6665125 : Blo 1754578 6665125 := bbase (se 4 (by rfl) ⟨624855, by rfl⟩ : syracuseStep 6665125 = 1249711) (by norm_num)
theorem B2634677 : Blo 1754578 2634677 := bbase (se 5 (by rfl) ⟨123500, by rfl⟩ : syracuseStep 2634677 = 247001) (by norm_num)
theorem B2634701 : Blo 1754578 2634701 := bbase (se 3 (by rfl) ⟨494006, by rfl⟩ : syracuseStep 2634701 = 988013) (by norm_num)
theorem B3331037 : Blo 1754578 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B2634725 : Blo 1754578 2634725 := bbase (se 4 (by rfl) ⟨247005, by rfl⟩ : syracuseStep 2634725 = 494011) (by norm_num)
theorem B3560429 : Blo 1754578 3560429 := bbase (se 3 (by rfl) ⟨667580, by rfl⟩ : syracuseStep 3560429 = 1335161) (by norm_num)
theorem B4215797 : Blo 1754578 4215797 := bbase (se 5 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 4215797 = 395231) (by norm_num)
theorem B4060157 : Blo 1754578 4060157 := bbase (se 3 (by rfl) ⟨761279, by rfl⟩ : syracuseStep 4060157 = 1522559) (by norm_num)
theorem B2634749 : Blo 1754578 2634749 := bbase (se 3 (by rfl) ⟨494015, by rfl⟩ : syracuseStep 2634749 = 988031) (by norm_num)
theorem B7918597 : Blo 1754578 7918597 := bbase (se 4 (by rfl) ⟨742368, by rfl⟩ : syracuseStep 7918597 = 1484737) (by norm_num)
theorem B4445189 : Blo 1754578 4445189 := bbase (se 4 (by rfl) ⟨416736, by rfl⟩ : syracuseStep 4445189 = 833473) (by norm_num)
theorem B14996501 : Blo 1754578 14996501 := bbase (se 6 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 14996501 = 702961) (by norm_num)
theorem B2962453 : Blo 1754578 2962453 := bbase (se 6 (by rfl) ⟨69432, by rfl⟩ : syracuseStep 2962453 = 138865) (by norm_num)
theorem B5927957 : Blo 1754578 5927957 := bbase (se 6 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 5927957 = 277873) (by norm_num)
theorem B2634773 : Blo 1754578 2634773 := bbase (se 6 (by rfl) ⟨61752, by rfl⟩ : syracuseStep 2634773 = 123505) (by norm_num)
theorem B2634797 : Blo 1754578 2634797 := bbase (se 3 (by rfl) ⟨494024, by rfl⟩ : syracuseStep 2634797 = 988049) (by norm_num)
theorem B2634821 : Blo 1754578 2634821 := bbase (se 4 (by rfl) ⟨247014, by rfl⟩ : syracuseStep 2634821 = 494029) (by norm_num)
theorem B8008789 : Blo 1754578 8008789 := bbase (se 8 (by rfl) ⟨46926, by rfl⟩ : syracuseStep 8008789 = 93853) (by norm_num)
theorem B2634845 : Blo 1754578 2634845 := bbase (se 3 (by rfl) ⟨494033, by rfl⟩ : syracuseStep 2634845 = 988067) (by norm_num)
theorem B3331181 : Blo 1754578 3331181 := bbase (se 3 (by rfl) ⟨624596, by rfl⟩ : syracuseStep 3331181 = 1249193) (by norm_num)
theorem B2962541 : Blo 1754578 2962541 := bbase (se 3 (by rfl) ⟨555476, by rfl⟩ : syracuseStep 2962541 = 1110953) (by norm_num)
theorem B4502645 : Blo 1754578 4502645 := bbase (se 5 (by rfl) ⟨211061, by rfl⟩ : syracuseStep 4502645 = 422123) (by norm_num)
theorem B3748997 : Blo 1754578 3748997 := bbase (se 4 (by rfl) ⟨351468, by rfl⟩ : syracuseStep 3748997 = 702937) (by norm_num)
theorem B4445381 : Blo 1754578 4445381 := bbase (se 4 (by rfl) ⟨416754, by rfl⟩ : syracuseStep 4445381 = 833509) (by norm_num)
theorem B6665429 : Blo 1754578 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B2962669 : Blo 1754578 2962669 := bbase (se 3 (by rfl) ⟨555500, by rfl⟩ : syracuseStep 2962669 = 1111001) (by norm_num)
theorem B3044621 : Blo 1754578 3044621 := bbase (se 3 (by rfl) ⟨570866, by rfl⟩ : syracuseStep 3044621 = 1141733) (by norm_num)
theorem B2667797 : Blo 1754578 2667797 := bbase (se 6 (by rfl) ⟨62526, by rfl⟩ : syracuseStep 2667797 = 125053) (by norm_num)
theorem B2667821 : Blo 1754578 2667821 := bbase (se 3 (by rfl) ⟨500216, by rfl⟩ : syracuseStep 2667821 = 1000433) (by norm_num)
theorem B2667845 : Blo 1754578 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B2962757 : Blo 1754578 2962757 := bbase (se 4 (by rfl) ⟨277758, by rfl⟩ : syracuseStep 2962757 = 555517) (by norm_num)
theorem B3331469 : Blo 1754578 3331469 := bbase (se 3 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 3331469 = 1249301) (by norm_num)
theorem B2373013 : Blo 1754578 2373013 := bbase (se 6 (by rfl) ⟨55617, by rfl⟩ : syracuseStep 2373013 = 111235) (by norm_num)
theorem B4216229 : Blo 1754578 4216229 := bbase (se 4 (by rfl) ⟨395271, by rfl⟩ : syracuseStep 4216229 = 790543) (by norm_num)
theorem B2962885 : Blo 1754578 2962885 := bbase (se 4 (by rfl) ⟨277770, by rfl⟩ : syracuseStep 2962885 = 555541) (by norm_num)
theorem B2373061 : Blo 1754578 2373061 := bbase (se 4 (by rfl) ⟨222474, by rfl⟩ : syracuseStep 2373061 = 444949) (by norm_num)
theorem B5928389 : Blo 1754578 5928389 := bbase (se 4 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 5928389 = 1111573) (by norm_num)
theorem B2962973 : Blo 1754578 2962973 := bbase (se 3 (by rfl) ⟨555557, by rfl⟩ : syracuseStep 2962973 = 1111115) (by norm_num)
theorem B4445725 : Blo 1754578 4445725 := bbase (se 3 (by rfl) ⟨833573, by rfl⟩ : syracuseStep 4445725 = 1667147) (by norm_num)
theorem B3331621 : Blo 1754578 3331621 := bbase (se 4 (by rfl) ⟨312339, by rfl⟩ : syracuseStep 3331621 = 624679) (by norm_num)
theorem B22500949 : Blo 1754578 22500949 := bbase (se 8 (by rfl) ⟨131841, by rfl⟩ : syracuseStep 22500949 = 263683) (by norm_num)
theorem B8885861 : Blo 1754578 8885861 := bbase (se 4 (by rfl) ⟨833049, by rfl⟩ : syracuseStep 8885861 = 1666099) (by norm_num)
theorem B4445837 : Blo 1754578 4445837 := bbase (se 3 (by rfl) ⟨833594, by rfl⟩ : syracuseStep 4445837 = 1667189) (by norm_num)
theorem B2963101 : Blo 1754578 2963101 := bbase (se 3 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 2963101 = 1111163) (by norm_num)
theorem B16864949 : Blo 1754578 16864949 := bbase (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) (by norm_num)
theorem B36050645 : Blo 1754578 36050645 := bbase (se 7 (by rfl) ⟨422468, by rfl⟩ : syracuseStep 36050645 = 844937) (by norm_num)
theorem B2963189 : Blo 1754578 2963189 := bbase (se 5 (by rfl) ⟨138899, by rfl⟩ : syracuseStep 2963189 = 277799) (by norm_num)
theorem B4446029 : Blo 1754578 4446029 := bbase (se 3 (by rfl) ⟨833630, by rfl⟩ : syracuseStep 4446029 = 1667261) (by norm_num)
theorem B3331925 : Blo 1754578 3331925 := bbase (se 9 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 3331925 = 19523) (by norm_num)
theorem B4003685 : Blo 1754578 4003685 := bbase (se 4 (by rfl) ⟨375345, by rfl⟩ : syracuseStep 4003685 = 750691) (by norm_num)
theorem B2963317 : Blo 1754578 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B2373493 : Blo 1754578 2373493 := bbase (se 5 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 2373493 = 222515) (by norm_num)
theorem B4003757 : Blo 1754578 4003757 := bbase (se 3 (by rfl) ⟨750704, by rfl⟩ : syracuseStep 4003757 = 1501409) (by norm_num)
theorem B2963405 : Blo 1754578 2963405 := bbase (se 3 (by rfl) ⟨555638, by rfl⟩ : syracuseStep 2963405 = 1111277) (by norm_num)
theorem B4216853 : Blo 1754578 4216853 := bbase (se 6 (by rfl) ⟨98832, by rfl⟩ : syracuseStep 4216853 = 197665) (by norm_num)
theorem B2963533 : Blo 1754578 2963533 := bbase (se 3 (by rfl) ⟨555662, by rfl⟩ : syracuseStep 2963533 = 1111325) (by norm_num)
theorem B6330469 : Blo 1754578 6330469 := bbase (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) (by norm_num)
theorem B4274309 : Blo 1754578 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B2963621 : Blo 1754578 2963621 := bbase (se 4 (by rfl) ⟨277839, by rfl⟩ : syracuseStep 2963621 = 555679) (by norm_num)
theorem B5339317 : Blo 1754578 5339317 := bbase (se 5 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 5339317 = 500561) (by norm_num)
theorem B2963749 : Blo 1754578 2963749 := bbase (se 4 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 2963749 = 555703) (by norm_num)
theorem B1874225 : Blo 1754578 1874225 := bbase (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) (by norm_num)
theorem B2963837 : Blo 1754578 2963837 := bbase (se 3 (by rfl) ⟨555719, by rfl⟩ : syracuseStep 2963837 = 1111439) (by norm_num)
theorem B8436149 : Blo 1754578 8436149 := bbase (se 5 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 8436149 = 790889) (by norm_num)
theorem B5339573 : Blo 1754578 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B2963965 : Blo 1754578 2963965 := bbase (se 3 (by rfl) ⟨555743, by rfl⟩ : syracuseStep 2963965 = 1111487) (by norm_num)
theorem B2849293 : Blo 1754578 2849293 := bbase (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) (by norm_num)
theorem B3332677 : Blo 1754578 3332677 := bbase (se 4 (by rfl) ⟨312438, by rfl⟩ : syracuseStep 3332677 = 624877) (by norm_num)
theorem B2964053 : Blo 1754578 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B3332821 : Blo 1754578 3332821 := bbase (se 7 (by rfl) ⟨39056, by rfl⟩ : syracuseStep 3332821 = 78113) (by norm_num)
theorem B2964181 : Blo 1754578 2964181 := bbase (se 7 (by rfl) ⟨34736, by rfl⟩ : syracuseStep 2964181 = 69473) (by norm_num)
theorem B5626597 : Blo 1754578 5626597 := bbase (se 4 (by rfl) ⟨527493, by rfl⟩ : syracuseStep 5626597 = 1054987) (by norm_num)
theorem B1874669 : Blo 1754578 1874669 := bbase (se 3 (by rfl) ⟨351500, by rfl⟩ : syracuseStep 1874669 = 703001) (by norm_num)
theorem B3750637 : Blo 1754578 3750637 := bbase (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) (by norm_num)
theorem B8887157 : Blo 1754578 8887157 := bbase (se 5 (by rfl) ⟨416585, by rfl⟩ : syracuseStep 8887157 = 833171) (by norm_num)
theorem B3332981 : Blo 1754578 3332981 := bbase (se 5 (by rfl) ⟨156233, by rfl⟩ : syracuseStep 3332981 = 312467) (by norm_num)
theorem B10001333 : Blo 1754578 10001333 := bbase (se 5 (by rfl) ⟨468812, by rfl⟩ : syracuseStep 10001333 = 937625) (by norm_num)
theorem B1874917 : Blo 1754578 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B3333125 : Blo 1754578 3333125 := bbase (se 4 (by rfl) ⟨312480, by rfl⟩ : syracuseStep 3333125 = 624961) (by norm_num)
theorem B2669573 : Blo 1754578 2669573 := bbase (se 4 (by rfl) ⟨250272, by rfl⟩ : syracuseStep 2669573 = 500545) (by norm_num)
theorem B5069909 : Blo 1754578 5069909 := bbase (se 8 (by rfl) ⟨29706, by rfl⟩ : syracuseStep 5069909 = 59413) (by norm_num)
theorem B5921909 : Blo 1754578 5921909 := bbase (se 5 (by rfl) ⟨277589, by rfl⟩ : syracuseStep 5921909 = 555179) (by norm_num)
theorem B6667541 : Blo 1754578 6667541 := bbase (se 6 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 6667541 = 312541) (by norm_num)
theorem B3947813 : Blo 1754578 3947813 := bbase (se 4 (by rfl) ⟨370107, by rfl⟩ : syracuseStep 3947813 = 740215) (by norm_num)
theorem B3333413 : Blo 1754578 3333413 := bbase (se 4 (by rfl) ⟨312507, by rfl⟩ : syracuseStep 3333413 = 625015) (by norm_num)
theorem B3947885 : Blo 1754578 3947885 := bbase (se 3 (by rfl) ⟨740228, by rfl⟩ : syracuseStep 3947885 = 1480457) (by norm_num)
theorem B1875349 : Blo 1754578 1875349 := bbase (se 6 (by rfl) ⟨43953, by rfl⟩ : syracuseStep 1875349 = 87907) (by norm_num)
theorem B3947957 : Blo 1754578 3947957 := bbase (se 5 (by rfl) ⟨185060, by rfl⟩ : syracuseStep 3947957 = 370121) (by norm_num)
theorem B3333565 : Blo 1754578 3333565 := bbase (se 3 (by rfl) ⟨625043, by rfl⟩ : syracuseStep 3333565 = 1250087) (by norm_num)
theorem B1875421 : Blo 1754578 1875421 := bbase (se 3 (by rfl) ⟨351641, by rfl⟩ : syracuseStep 1875421 = 703283) (by norm_num)
theorem B3948029 : Blo 1754578 3948029 := bbase (se 3 (by rfl) ⟨740255, by rfl⟩ : syracuseStep 3948029 = 1480511) (by norm_num)
theorem B5922341 : Blo 1754578 5922341 := bbase (se 4 (by rfl) ⟨555219, by rfl⟩ : syracuseStep 5922341 = 1110439) (by norm_num)
theorem B6667829 : Blo 1754578 6667829 := bbase (se 5 (by rfl) ⟨312554, by rfl⟩ : syracuseStep 6667829 = 625109) (by norm_num)
theorem B3948101 : Blo 1754578 3948101 := bbase (se 4 (by rfl) ⟨370134, by rfl⟩ : syracuseStep 3948101 = 740269) (by norm_num)
theorem B3751525 : Blo 1754578 3751525 := bbase (se 4 (by rfl) ⟨351705, by rfl⟩ : syracuseStep 3751525 = 703411) (by norm_num)
theorem B4505213 : Blo 1754578 4505213 := bbase (se 3 (by rfl) ⟨844727, by rfl⟩ : syracuseStep 4505213 = 1689455) (by norm_num)
theorem B3948173 : Blo 1754578 3948173 := bbase (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) (by norm_num)
theorem B2670229 : Blo 1754578 2670229 := bbase (se 6 (by rfl) ⟨62583, by rfl⟩ : syracuseStep 2670229 = 125167) (by norm_num)
theorem B1973929 : Blo 1754578 1973929 := bbase (se 2 (by rfl) ⟨740223, by rfl⟩ : syracuseStep 1973929 = 1480447) (by norm_num)
theorem B1973965 : Blo 1754578 1973965 := bbase (se 3 (by rfl) ⟨370118, by rfl⟩ : syracuseStep 1973965 = 740237) (by norm_num)
theorem B3948245 : Blo 1754578 3948245 := bbase (se 7 (by rfl) ⟨46268, by rfl⟩ : syracuseStep 3948245 = 92537) (by norm_num)
theorem B3333869 : Blo 1754578 3333869 := bbase (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) (by norm_num)
theorem B1974001 : Blo 1754578 1974001 := bbase (se 2 (by rfl) ⟨740250, by rfl⟩ : syracuseStep 1974001 = 1480501) (by norm_num)
theorem B16228085 : Blo 1754578 16228085 := bbase (se 5 (by rfl) ⟨760691, by rfl⟩ : syracuseStep 16228085 = 1521383) (by norm_num)
theorem B4505357 : Blo 1754578 4505357 := bbase (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) (by norm_num)
theorem B1974037 : Blo 1754578 1974037 := bbase (se 6 (by rfl) ⟨46266, by rfl⟩ : syracuseStep 1974037 = 92533) (by norm_num)
theorem B4996885 : Blo 1754578 4996885 := bbase (se 6 (by rfl) ⟨117114, by rfl⟩ : syracuseStep 4996885 = 234229) (by norm_num)
theorem B3948317 : Blo 1754578 3948317 := bbase (se 3 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 3948317 = 1480619) (by norm_num)
theorem B4742965 : Blo 1754578 4742965 := bbase (se 5 (by rfl) ⟨222326, by rfl⟩ : syracuseStep 4742965 = 444653) (by norm_num)
theorem B9510709 : Blo 1754578 9510709 := bbase (se 5 (by rfl) ⟨445814, by rfl⟩ : syracuseStep 9510709 = 891629) (by norm_num)
theorem B1974073 : Blo 1754578 1974073 := bbase (se 2 (by rfl) ⟨740277, by rfl⟩ : syracuseStep 1974073 = 1480555) (by norm_num)
theorem B1875793 : Blo 1754578 1875793 := bbase (se 2 (by rfl) ⟨703422, by rfl⟩ : syracuseStep 1875793 = 1406845) (by norm_num)
theorem B1974109 : Blo 1754578 1974109 := bbase (se 3 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 1974109 = 740291) (by norm_num)
theorem B3948389 : Blo 1754578 3948389 := bbase (se 4 (by rfl) ⟨370161, by rfl⟩ : syracuseStep 3948389 = 740323) (by norm_num)
theorem B2744189 : Blo 1754578 2744189 := bbase (se 3 (by rfl) ⟨514535, by rfl⟩ : syracuseStep 2744189 = 1029071) (by norm_num)
theorem B1974145 : Blo 1754578 1974145 := bbase (se 2 (by rfl) ⟨740304, by rfl⟩ : syracuseStep 1974145 = 1480609) (by norm_num)
theorem B1974181 : Blo 1754578 1974181 := bbase (se 4 (by rfl) ⟨185079, by rfl⟩ : syracuseStep 1974181 = 370159) (by norm_num)
theorem B3948461 : Blo 1754578 3948461 := bbase (se 3 (by rfl) ⟨740336, by rfl⟩ : syracuseStep 3948461 = 1480673) (by norm_num)
theorem B4997045 : Blo 1754578 4997045 := bbase (se 5 (by rfl) ⟨234236, by rfl⟩ : syracuseStep 4997045 = 468473) (by norm_num)
theorem B1974217 : Blo 1754578 1974217 := bbase (se 2 (by rfl) ⟨740331, by rfl⟩ : syracuseStep 1974217 = 1480663) (by norm_num)
theorem B5922773 : Blo 1754578 5922773 := bbase (se 7 (by rfl) ⟨69407, by rfl⟩ : syracuseStep 5922773 = 138815) (by norm_num)
theorem B2670565 : Blo 1754578 2670565 := bbase (se 4 (by rfl) ⟨250365, by rfl⟩ : syracuseStep 2670565 = 500731) (by norm_num)
theorem B1974253 : Blo 1754578 1974253 := bbase (se 3 (by rfl) ⟨370172, by rfl⟩ : syracuseStep 1974253 = 740345) (by norm_num)
theorem B7495669 : Blo 1754578 7495669 := bbase (se 5 (by rfl) ⟨351359, by rfl⟩ : syracuseStep 7495669 = 702719) (by norm_num)
theorem B3948533 : Blo 1754578 3948533 := bbase (se 5 (by rfl) ⟨185087, by rfl⟩ : syracuseStep 3948533 = 370175) (by norm_num)
theorem B11247605 : Blo 1754578 11247605 := bbase (se 5 (by rfl) ⟨527231, by rfl⟩ : syracuseStep 11247605 = 1054463) (by norm_num)
theorem B1974307 : Blo 1754578 1974307 := bstep (se 1 (by rfl) ⟨1480730, by rfl⟩ : syracuseStep 1974307 = 2961461) B2961461
theorem B5922989 : Blo 1754578 5922989 := bstep (se 3 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 5922989 = 2221121) B2221121
theorem B1974451 : Blo 1754578 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B5923043 : Blo 1754578 5923043 := bstep (se 1 (by rfl) ⟨4442282, by rfl⟩ : syracuseStep 5923043 = 8884565) B8884565
theorem B3948785 : Blo 1754578 3948785 := bstep (se 2 (by rfl) ⟨1480794, by rfl⟩ : syracuseStep 3948785 = 2961589) B2961589
theorem B7119089 : Blo 1754578 7119089 := bstep (se 2 (by rfl) ⟨2669658, by rfl⟩ : syracuseStep 7119089 = 5339317) B5339317
theorem B3334385 : Blo 1754578 3334385 := bstep (se 2 (by rfl) ⟨1250394, by rfl⟩ : syracuseStep 3334385 = 2500789) B2500789
theorem B3948803 : Blo 1754578 3948803 := bstep (se 1 (by rfl) ⟨2961602, by rfl⟩ : syracuseStep 3948803 = 5923205) B5923205
theorem B36036917 : Blo 1754578 36036917 := bstep (se 5 (by rfl) ⟨1689230, by rfl⟩ : syracuseStep 36036917 = 3378461) B3378461
theorem B1974595 : Blo 1754578 1974595 := bstep (se 1 (by rfl) ⟨1480946, by rfl⟩ : syracuseStep 1974595 = 2961893) B2961893
theorem B1974739 : Blo 1754578 1974739 := bstep (se 1 (by rfl) ⟨1481054, by rfl⟩ : syracuseStep 1974739 = 2962109) B2962109
theorem B5923313 : Blo 1754578 5923313 := bstep (se 2 (by rfl) ⟨2221242, by rfl⟩ : syracuseStep 5923313 = 4442485) B4442485
theorem B3949073 : Blo 1754578 3949073 := bstep (se 2 (by rfl) ⟨1480902, by rfl⟩ : syracuseStep 3949073 = 2961805) B2961805
theorem B3949091 : Blo 1754578 3949091 := bstep (se 1 (by rfl) ⟨2961818, by rfl⟩ : syracuseStep 3949091 = 5923637) B5923637
theorem B1974883 : Blo 1754578 1974883 := bstep (se 1 (by rfl) ⟨1481162, by rfl⟩ : syracuseStep 1974883 = 2962325) B2962325
theorem B2220691 : Blo 1754578 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B2810531 : Blo 1754578 2810531 := bstep (se 1 (by rfl) ⟨2107898, by rfl⟩ : syracuseStep 2810531 = 4215797) B4215797
theorem B2220787 : Blo 1754578 2220787 := bstep (se 1 (by rfl) ⟨1665590, by rfl⟩ : syracuseStep 2220787 = 3331181) B3331181
theorem B1975027 : Blo 1754578 1975027 := bstep (se 1 (by rfl) ⟨1481270, by rfl⟩ : syracuseStep 1975027 = 2962541) B2962541
theorem B2499331 : Blo 1754578 2499331 := bstep (se 1 (by rfl) ⟨1874498, by rfl⟩ : syracuseStep 2499331 = 3748997) B3748997
theorem B8889101 : Blo 1754578 8889101 := bstep (se 3 (by rfl) ⟨1666706, by rfl⟩ : syracuseStep 8889101 = 3333413) B3333413
theorem B4997933 : Blo 1754578 4997933 := bstep (se 3 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 4997933 = 1874225) B1874225
theorem B3949361 : Blo 1754578 3949361 := bstep (se 2 (by rfl) ⟨1481010, by rfl⟩ : syracuseStep 3949361 = 2962021) B2962021
theorem B3949379 : Blo 1754578 3949379 := bstep (se 1 (by rfl) ⟨2962034, by rfl⟩ : syracuseStep 3949379 = 5924069) B5924069
theorem B1778531 : Blo 1754578 1778531 := bstep (se 1 (by rfl) ⟨1333898, by rfl⟩ : syracuseStep 1778531 = 2667797) B2667797
theorem B3162979 : Blo 1754578 3162979 := bstep (se 1 (by rfl) ⟨2372234, by rfl⟩ : syracuseStep 3162979 = 4744469) B4744469
theorem B1778563 : Blo 1754578 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B1975171 : Blo 1754578 1975171 := bstep (se 1 (by rfl) ⟨1481378, by rfl⟩ : syracuseStep 1975171 = 2962757) B2962757
theorem B3163043 : Blo 1754578 3163043 := bstep (se 1 (by rfl) ⟨2372282, by rfl⟩ : syracuseStep 3163043 = 4744565) B4744565
theorem B2810819 : Blo 1754578 2810819 := bstep (se 1 (by rfl) ⟨2108114, by rfl⟩ : syracuseStep 2810819 = 4216229) B4216229
theorem B4998115 : Blo 1754578 4998115 := bstep (se 1 (by rfl) ⟨3748586, by rfl⟩ : syracuseStep 4998115 = 7497173) B7497173
theorem B5923853 : Blo 1754578 5923853 := bstep (se 3 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 5923853 = 2221445) B2221445
theorem B4998161 : Blo 1754578 4998161 := bstep (se 2 (by rfl) ⟨1874310, by rfl⟩ : syracuseStep 4998161 = 3748621) B3748621
theorem B1975315 : Blo 1754578 1975315 := bstep (se 1 (by rfl) ⟨1481486, by rfl⟩ : syracuseStep 1975315 = 2962973) B2962973
theorem B5923907 : Blo 1754578 5923907 := bstep (se 1 (by rfl) ⟨4442930, by rfl⟩ : syracuseStep 5923907 = 8885861) B8885861
theorem B3949649 : Blo 1754578 3949649 := bstep (se 2 (by rfl) ⟨1481118, by rfl⟩ : syracuseStep 3949649 = 2962237) B2962237
theorem B3949667 : Blo 1754578 3949667 := bstep (se 1 (by rfl) ⟨2962250, by rfl⟩ : syracuseStep 3949667 = 5924501) B5924501
theorem B13329521 : Blo 1754578 13329521 := bstep (se 2 (by rfl) ⟨4998570, by rfl⟩ : syracuseStep 13329521 = 9997141) B9997141
theorem B1975459 : Blo 1754578 1975459 := bstep (se 1 (by rfl) ⟨1481594, by rfl⟩ : syracuseStep 1975459 = 2963189) B2963189
theorem B2221283 : Blo 1754578 2221283 := bstep (se 1 (by rfl) ⟨1665962, by rfl⟩ : syracuseStep 2221283 = 3331925) B3331925
theorem B8439011 : Blo 1754578 8439011 := bstep (se 1 (by rfl) ⟨6329258, by rfl⟩ : syracuseStep 8439011 = 12658517) B12658517
theorem B1975603 : Blo 1754578 1975603 := bstep (se 1 (by rfl) ⟨1481702, by rfl⟩ : syracuseStep 1975603 = 2963405) B2963405
theorem B5924177 : Blo 1754578 5924177 := bstep (se 2 (by rfl) ⟨2221566, by rfl⟩ : syracuseStep 5924177 = 4443133) B4443133
theorem B2811235 : Blo 1754578 2811235 := bstep (se 1 (by rfl) ⟨2108426, by rfl⟩ : syracuseStep 2811235 = 4216853) B4216853
theorem B3949937 : Blo 1754578 3949937 := bstep (se 2 (by rfl) ⟨1481226, by rfl⟩ : syracuseStep 3949937 = 2962453) B2962453
theorem B3949955 : Blo 1754578 3949955 := bstep (se 1 (by rfl) ⟨2962466, by rfl⟩ : syracuseStep 3949955 = 5924933) B5924933
theorem B9618821 : Blo 1754578 9618821 := bstep (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) B1803529
theorem B9995683 : Blo 1754578 9995683 := bstep (se 1 (by rfl) ⟨7496762, by rfl⟩ : syracuseStep 9995683 = 14993525) B14993525
theorem B1975747 : Blo 1754578 1975747 := bstep (se 1 (by rfl) ⟨1481810, by rfl⟩ : syracuseStep 1975747 = 2963621) B2963621
theorem B1754579 : Blo 1754578 1754579 := bstep (se 1 (by rfl) ⟨1315934, by rfl⟩ : syracuseStep 1754579 = 2631869) B2631869
theorem B1754595 : Blo 1754578 1754595 := bstep (se 1 (by rfl) ⟨1315946, by rfl⟩ : syracuseStep 1754595 = 2631893) B2631893
theorem B1754611 : Blo 1754578 1754611 := bstep (se 1 (by rfl) ⟨1315958, by rfl⟩ : syracuseStep 1754611 = 2631917) B2631917
theorem B1754627 : Blo 1754578 1754627 := bstep (se 1 (by rfl) ⟨1315970, by rfl⟩ : syracuseStep 1754627 = 2631941) B2631941
theorem B1754643 : Blo 1754578 1754643 := bstep (se 1 (by rfl) ⟨1315982, by rfl⟩ : syracuseStep 1754643 = 2631965) B2631965
theorem B1754659 : Blo 1754578 1754659 := bstep (se 1 (by rfl) ⟨1315994, by rfl⟩ : syracuseStep 1754659 = 2631989) B2631989
theorem B1754675 : Blo 1754578 1754675 := bstep (se 1 (by rfl) ⟨1316006, by rfl⟩ : syracuseStep 1754675 = 2632013) B2632013
theorem B1754691 : Blo 1754578 1754691 := bstep (se 1 (by rfl) ⟨1316018, by rfl⟩ : syracuseStep 1754691 = 2632037) B2632037
theorem B1754707 : Blo 1754578 1754707 := bstep (se 1 (by rfl) ⟨1316030, by rfl⟩ : syracuseStep 1754707 = 2632061) B2632061
theorem B1975891 : Blo 1754578 1975891 := bstep (se 1 (by rfl) ⟨1481918, by rfl⟩ : syracuseStep 1975891 = 2963837) B2963837
theorem B1754723 : Blo 1754578 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B2811505 : Blo 1754578 2811505 := bstep (se 2 (by rfl) ⟨1054314, by rfl⟩ : syracuseStep 2811505 = 2108629) B2108629
theorem B1754739 : Blo 1754578 1754739 := bstep (se 1 (by rfl) ⟨1316054, by rfl⟩ : syracuseStep 1754739 = 2632109) B2632109
theorem B1754755 : Blo 1754578 1754755 := bstep (se 1 (by rfl) ⟨1316066, by rfl⟩ : syracuseStep 1754755 = 2632133) B2632133
theorem B3950225 : Blo 1754578 3950225 := bstep (se 2 (by rfl) ⟨1481334, by rfl⟩ : syracuseStep 3950225 = 2962669) B2962669
theorem B1754771 : Blo 1754578 1754771 := bstep (se 1 (by rfl) ⟨1316078, by rfl⟩ : syracuseStep 1754771 = 2632157) B2632157
theorem B1754787 : Blo 1754578 1754787 := bstep (se 1 (by rfl) ⟨1316090, by rfl⟩ : syracuseStep 1754787 = 2632181) B2632181
theorem B3950243 : Blo 1754578 3950243 := bstep (se 1 (by rfl) ⟨2962682, by rfl⟩ : syracuseStep 3950243 = 5925365) B5925365
theorem B1754803 : Blo 1754578 1754803 := bstep (se 1 (by rfl) ⟨1316102, by rfl⟩ : syracuseStep 1754803 = 2632205) B2632205
theorem B1754819 : Blo 1754578 1754819 := bstep (se 1 (by rfl) ⟨1316114, by rfl⟩ : syracuseStep 1754819 = 2632229) B2632229
theorem B1754835 : Blo 1754578 1754835 := bstep (se 1 (by rfl) ⟨1316126, by rfl⟩ : syracuseStep 1754835 = 2632253) B2632253
theorem B1754851 : Blo 1754578 1754851 := bstep (se 1 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 1754851 = 2632277) B2632277
theorem B1976035 : Blo 1754578 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B1754867 : Blo 1754578 1754867 := bstep (se 1 (by rfl) ⟨1316150, by rfl⟩ : syracuseStep 1754867 = 2632301) B2632301
theorem B1754883 : Blo 1754578 1754883 := bstep (se 1 (by rfl) ⟨1316162, by rfl⟩ : syracuseStep 1754883 = 2632325) B2632325
theorem B6326029 : Blo 1754578 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B1754899 : Blo 1754578 1754899 := bstep (se 1 (by rfl) ⟨1316174, by rfl⟩ : syracuseStep 1754899 = 2632349) B2632349
theorem B1754915 : Blo 1754578 1754915 := bstep (se 1 (by rfl) ⟨1316186, by rfl⟩ : syracuseStep 1754915 = 2632373) B2632373
theorem B1754931 : Blo 1754578 1754931 := bstep (se 1 (by rfl) ⟨1316198, by rfl⟩ : syracuseStep 1754931 = 2632397) B2632397
theorem B1754947 : Blo 1754578 1754947 := bstep (se 1 (by rfl) ⟨1316210, by rfl⟩ : syracuseStep 1754947 = 2632421) B2632421
theorem B1754963 : Blo 1754578 1754963 := bstep (se 1 (by rfl) ⟨1316222, by rfl⟩ : syracuseStep 1754963 = 2632445) B2632445
theorem B1754979 : Blo 1754578 1754979 := bstep (se 1 (by rfl) ⟨1316234, by rfl⟩ : syracuseStep 1754979 = 2632469) B2632469
theorem B5924717 : Blo 1754578 5924717 := bstep (se 3 (by rfl) ⟨1110884, by rfl⟩ : syracuseStep 5924717 = 2221769) B2221769
theorem B2811761 : Blo 1754578 2811761 := bstep (se 2 (by rfl) ⟨1054410, by rfl⟩ : syracuseStep 2811761 = 2108821) B2108821
theorem B3164017 : Blo 1754578 3164017 := bstep (se 2 (by rfl) ⟨1186506, by rfl⟩ : syracuseStep 3164017 = 2373013) B2373013
theorem B1754995 : Blo 1754578 1754995 := bstep (se 1 (by rfl) ⟨1316246, by rfl⟩ : syracuseStep 1754995 = 2632493) B2632493
theorem B2500465 : Blo 1754578 2500465 := bstep (se 2 (by rfl) ⟨937674, by rfl⟩ : syracuseStep 2500465 = 1875349) B1875349
theorem B1755011 : Blo 1754578 1755011 := bstep (se 1 (by rfl) ⟨1316258, by rfl⟩ : syracuseStep 1755011 = 2632517) B2632517
theorem B1755027 : Blo 1754578 1755027 := bstep (se 1 (by rfl) ⟨1316270, by rfl⟩ : syracuseStep 1755027 = 2632541) B2632541
theorem B1755043 : Blo 1754578 1755043 := bstep (se 1 (by rfl) ⟨1316282, by rfl⟩ : syracuseStep 1755043 = 2632565) B2632565
theorem B5924771 : Blo 1754578 5924771 := bstep (se 1 (by rfl) ⟨4443578, by rfl⟩ : syracuseStep 5924771 = 8887157) B8887157
theorem B2221987 : Blo 1754578 2221987 := bstep (se 1 (by rfl) ⟨1666490, by rfl⟩ : syracuseStep 2221987 = 3332981) B3332981
theorem B9996209 : Blo 1754578 9996209 := bstep (se 2 (by rfl) ⟨3748578, by rfl⟩ : syracuseStep 9996209 = 7497157) B7497157
theorem B3950513 : Blo 1754578 3950513 := bstep (se 2 (by rfl) ⟨1481442, by rfl⟩ : syracuseStep 3950513 = 2962885) B2962885
theorem B1755059 : Blo 1754578 1755059 := bstep (se 1 (by rfl) ⟨1316294, by rfl⟩ : syracuseStep 1755059 = 2632589) B2632589
theorem B3164081 : Blo 1754578 3164081 := bstep (se 2 (by rfl) ⟨1186530, by rfl⟩ : syracuseStep 3164081 = 2373061) B2373061
theorem B1755075 : Blo 1754578 1755075 := bstep (se 1 (by rfl) ⟨1316306, by rfl⟩ : syracuseStep 1755075 = 2632613) B2632613
theorem B3950531 : Blo 1754578 3950531 := bstep (se 1 (by rfl) ⟨2962898, by rfl⟩ : syracuseStep 3950531 = 5925797) B5925797
theorem B2500561 : Blo 1754578 2500561 := bstep (se 2 (by rfl) ⟨937710, by rfl⟩ : syracuseStep 2500561 = 1875421) B1875421
theorem B1755091 : Blo 1754578 1755091 := bstep (se 1 (by rfl) ⟨1316318, by rfl⟩ : syracuseStep 1755091 = 2632637) B2632637
theorem B1755107 : Blo 1754578 1755107 := bstep (se 1 (by rfl) ⟨1316330, by rfl⟩ : syracuseStep 1755107 = 2632661) B2632661
theorem B1755123 : Blo 1754578 1755123 := bstep (se 1 (by rfl) ⟨1316342, by rfl⟩ : syracuseStep 1755123 = 2632685) B2632685
theorem B1755139 : Blo 1754578 1755139 := bstep (se 1 (by rfl) ⟨1316354, by rfl⟩ : syracuseStep 1755139 = 2632709) B2632709
theorem B2222083 : Blo 1754578 2222083 := bstep (se 1 (by rfl) ⟨1666562, by rfl⟩ : syracuseStep 2222083 = 3333125) B3333125
theorem B1779715 : Blo 1754578 1779715 := bstep (se 1 (by rfl) ⟨1334786, by rfl⟩ : syracuseStep 1779715 = 2669573) B2669573
theorem B1755155 : Blo 1754578 1755155 := bstep (se 1 (by rfl) ⟨1316366, by rfl⟩ : syracuseStep 1755155 = 2632733) B2632733
theorem B1755171 : Blo 1754578 1755171 := bstep (se 1 (by rfl) ⟨1316378, by rfl⟩ : syracuseStep 1755171 = 2632757) B2632757
theorem B4442161 : Blo 1754578 4442161 := bstep (se 2 (by rfl) ⟨1665810, by rfl⟩ : syracuseStep 4442161 = 3331621) B3331621
theorem B1755187 : Blo 1754578 1755187 := bstep (se 1 (by rfl) ⟨1316390, by rfl⟩ : syracuseStep 1755187 = 2632781) B2632781
theorem B1755203 : Blo 1754578 1755203 := bstep (se 1 (by rfl) ⟨1316402, by rfl⟩ : syracuseStep 1755203 = 2632805) B2632805
theorem B1755219 : Blo 1754578 1755219 := bstep (se 1 (by rfl) ⟨1316414, by rfl⟩ : syracuseStep 1755219 = 2632829) B2632829
theorem B1755235 : Blo 1754578 1755235 := bstep (se 1 (by rfl) ⟨1316426, by rfl⟩ : syracuseStep 1755235 = 2632853) B2632853
theorem B30001265 : Blo 1754578 30001265 := bstep (se 2 (by rfl) ⟨11250474, by rfl⟩ : syracuseStep 30001265 = 22500949) B22500949
theorem B1755251 : Blo 1754578 1755251 := bstep (se 1 (by rfl) ⟨1316438, by rfl⟩ : syracuseStep 1755251 = 2632877) B2632877
theorem B1755267 : Blo 1754578 1755267 := bstep (se 1 (by rfl) ⟨1316450, by rfl⟩ : syracuseStep 1755267 = 2632901) B2632901
theorem B1755283 : Blo 1754578 1755283 := bstep (se 1 (by rfl) ⟨1316462, by rfl⟩ : syracuseStep 1755283 = 2632925) B2632925
theorem B1755299 : Blo 1754578 1755299 := bstep (se 1 (by rfl) ⟨1316474, by rfl⟩ : syracuseStep 1755299 = 2632949) B2632949
theorem B5925041 : Blo 1754578 5925041 := bstep (se 2 (by rfl) ⟨2221890, by rfl⟩ : syracuseStep 5925041 = 4443781) B4443781
theorem B1755315 : Blo 1754578 1755315 := bstep (se 1 (by rfl) ⟨1316486, by rfl⟩ : syracuseStep 1755315 = 2632973) B2632973
theorem B2631875 : Blo 1754578 2631875 := bstep (se 1 (by rfl) ⟨1973906, by rfl⟩ : syracuseStep 2631875 = 3947813) B3947813
theorem B1755331 : Blo 1754578 1755331 := bstep (se 1 (by rfl) ⟨1316498, by rfl⟩ : syracuseStep 1755331 = 2632997) B2632997
theorem B3950801 : Blo 1754578 3950801 := bstep (se 2 (by rfl) ⟨1481550, by rfl⟩ : syracuseStep 3950801 = 2963101) B2963101
theorem B1755347 : Blo 1754578 1755347 := bstep (se 1 (by rfl) ⟨1316510, by rfl⟩ : syracuseStep 1755347 = 2633021) B2633021
theorem B2631905 : Blo 1754578 2631905 := bstep (se 2 (by rfl) ⟨986964, by rfl⟩ : syracuseStep 2631905 = 1973929) B1973929
theorem B1755363 : Blo 1754578 1755363 := bstep (se 1 (by rfl) ⟨1316522, by rfl⟩ : syracuseStep 1755363 = 2633045) B2633045
theorem B3950819 : Blo 1754578 3950819 := bstep (se 1 (by rfl) ⟨2963114, by rfl⟩ : syracuseStep 3950819 = 5926229) B5926229
theorem B2631923 : Blo 1754578 2631923 := bstep (se 1 (by rfl) ⟨1973942, by rfl⟩ : syracuseStep 2631923 = 3947885) B3947885
theorem B1755379 : Blo 1754578 1755379 := bstep (se 1 (by rfl) ⟨1316534, by rfl⟩ : syracuseStep 1755379 = 2633069) B2633069
theorem B1755395 : Blo 1754578 1755395 := bstep (se 1 (by rfl) ⟨1316546, by rfl⟩ : syracuseStep 1755395 = 2633093) B2633093
theorem B2631953 : Blo 1754578 2631953 := bstep (se 2 (by rfl) ⟨986982, by rfl⟩ : syracuseStep 2631953 = 1973965) B1973965
theorem B1755411 : Blo 1754578 1755411 := bstep (se 1 (by rfl) ⟨1316558, by rfl⟩ : syracuseStep 1755411 = 2633117) B2633117
theorem B2631971 : Blo 1754578 2631971 := bstep (se 1 (by rfl) ⟨1973978, by rfl⟩ : syracuseStep 2631971 = 3947957) B3947957
theorem B1755427 : Blo 1754578 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B1755443 : Blo 1754578 1755443 := bstep (se 1 (by rfl) ⟨1316582, by rfl⟩ : syracuseStep 1755443 = 2633165) B2633165
theorem B2632001 : Blo 1754578 2632001 := bstep (se 2 (by rfl) ⟨987000, by rfl⟩ : syracuseStep 2632001 = 1974001) B1974001
theorem B4442435 : Blo 1754578 4442435 := bstep (se 1 (by rfl) ⟨3331826, by rfl⟩ : syracuseStep 4442435 = 6663653) B6663653
theorem B1755459 : Blo 1754578 1755459 := bstep (se 1 (by rfl) ⟨1316594, by rfl⟩ : syracuseStep 1755459 = 2633189) B2633189
theorem B2632019 : Blo 1754578 2632019 := bstep (se 1 (by rfl) ⟨1974014, by rfl⟩ : syracuseStep 2632019 = 3948029) B3948029
theorem B1755475 : Blo 1754578 1755475 := bstep (se 1 (by rfl) ⟨1316606, by rfl⟩ : syracuseStep 1755475 = 2633213) B2633213
theorem B1755491 : Blo 1754578 1755491 := bstep (se 1 (by rfl) ⟨1316618, by rfl⟩ : syracuseStep 1755491 = 2633237) B2633237
theorem B2632049 : Blo 1754578 2632049 := bstep (se 2 (by rfl) ⟨987018, by rfl⟩ : syracuseStep 2632049 = 1974037) B1974037
theorem B6662513 : Blo 1754578 6662513 := bstep (se 2 (by rfl) ⟨2498442, by rfl⟩ : syracuseStep 6662513 = 4996885) B4996885
theorem B1755507 : Blo 1754578 1755507 := bstep (se 1 (by rfl) ⟨1316630, by rfl⟩ : syracuseStep 1755507 = 2633261) B2633261
theorem B2632067 : Blo 1754578 2632067 := bstep (se 1 (by rfl) ⟨1974050, by rfl⟩ : syracuseStep 2632067 = 3948101) B3948101
theorem B1755523 : Blo 1754578 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1755539 : Blo 1754578 1755539 := bstep (se 1 (by rfl) ⟨1316654, by rfl⟩ : syracuseStep 1755539 = 2633309) B2633309
theorem B2632097 : Blo 1754578 2632097 := bstep (se 2 (by rfl) ⟨987036, by rfl⟩ : syracuseStep 2632097 = 1974073) B1974073
theorem B1755555 : Blo 1754578 1755555 := bstep (se 1 (by rfl) ⟨1316666, by rfl⟩ : syracuseStep 1755555 = 2633333) B2633333
theorem B2632115 : Blo 1754578 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1755571 : Blo 1754578 1755571 := bstep (se 1 (by rfl) ⟨1316678, by rfl⟩ : syracuseStep 1755571 = 2633357) B2633357
theorem B2501057 : Blo 1754578 2501057 := bstep (se 2 (by rfl) ⟨937896, by rfl⟩ : syracuseStep 2501057 = 1875793) B1875793
theorem B1755587 : Blo 1754578 1755587 := bstep (se 1 (by rfl) ⟨1316690, by rfl⟩ : syracuseStep 1755587 = 2633381) B2633381
theorem B4999619 : Blo 1754578 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B2632145 : Blo 1754578 2632145 := bstep (se 2 (by rfl) ⟨987054, by rfl⟩ : syracuseStep 2632145 = 1974109) B1974109
theorem B1755603 : Blo 1754578 1755603 := bstep (se 1 (by rfl) ⟨1316702, by rfl⟩ : syracuseStep 1755603 = 2633405) B2633405
theorem B2632163 : Blo 1754578 2632163 := bstep (se 1 (by rfl) ⟨1974122, by rfl⟩ : syracuseStep 2632163 = 3948245) B3948245
theorem B1755619 : Blo 1754578 1755619 := bstep (se 1 (by rfl) ⟨1316714, by rfl⟩ : syracuseStep 1755619 = 2633429) B2633429
theorem B3951089 : Blo 1754578 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B1755635 : Blo 1754578 1755635 := bstep (se 1 (by rfl) ⟨1316726, by rfl⟩ : syracuseStep 1755635 = 2633453) B2633453
theorem B2222579 : Blo 1754578 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B2632193 : Blo 1754578 2632193 := bstep (se 2 (by rfl) ⟨987072, by rfl⟩ : syracuseStep 2632193 = 1974145) B1974145
theorem B4442627 : Blo 1754578 4442627 := bstep (se 1 (by rfl) ⟨3331970, by rfl⟩ : syracuseStep 4442627 = 6663941) B6663941
theorem B1755651 : Blo 1754578 1755651 := bstep (se 1 (by rfl) ⟨1316738, by rfl⟩ : syracuseStep 1755651 = 2633477) B2633477
theorem B3951107 : Blo 1754578 3951107 := bstep (se 1 (by rfl) ⟨2963330, by rfl⟩ : syracuseStep 3951107 = 5926661) B5926661
theorem B2632211 : Blo 1754578 2632211 := bstep (se 1 (by rfl) ⟨1974158, by rfl⟩ : syracuseStep 2632211 = 3948317) B3948317
theorem B1755667 : Blo 1754578 1755667 := bstep (se 1 (by rfl) ⟨1316750, by rfl⟩ : syracuseStep 1755667 = 2633501) B2633501
theorem B1755683 : Blo 1754578 1755683 := bstep (se 1 (by rfl) ⟨1316762, by rfl⟩ : syracuseStep 1755683 = 2633525) B2633525
theorem B5622317 : Blo 1754578 5622317 := bstep (se 3 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 5622317 = 2108369) B2108369
theorem B2632241 : Blo 1754578 2632241 := bstep (se 2 (by rfl) ⟨987090, by rfl⟩ : syracuseStep 2632241 = 1974181) B1974181
theorem B1755699 : Blo 1754578 1755699 := bstep (se 1 (by rfl) ⟨1316774, by rfl⟩ : syracuseStep 1755699 = 2633549) B2633549
theorem B2812465 : Blo 1754578 2812465 := bstep (se 2 (by rfl) ⟨1054674, by rfl⟩ : syracuseStep 2812465 = 2109349) B2109349
theorem B2632259 : Blo 1754578 2632259 := bstep (se 1 (by rfl) ⟨1974194, by rfl⟩ : syracuseStep 2632259 = 3948389) B3948389
theorem B1755715 : Blo 1754578 1755715 := bstep (se 1 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 1755715 = 2633573) B2633573
theorem B1755731 : Blo 1754578 1755731 := bstep (se 1 (by rfl) ⟨1316798, by rfl⟩ : syracuseStep 1755731 = 2633597) B2633597
theorem B1829459 : Blo 1754578 1829459 := bstep (se 1 (by rfl) ⟨1372094, by rfl⟩ : syracuseStep 1829459 = 2744189) B2744189
theorem B2632289 : Blo 1754578 2632289 := bstep (se 2 (by rfl) ⟨987108, by rfl⟩ : syracuseStep 2632289 = 1974217) B1974217
theorem B1755747 : Blo 1754578 1755747 := bstep (se 1 (by rfl) ⟨1316810, by rfl⟩ : syracuseStep 1755747 = 2633621) B2633621
theorem B2632307 : Blo 1754578 2632307 := bstep (se 1 (by rfl) ⟨1974230, by rfl⟩ : syracuseStep 2632307 = 3948461) B3948461
theorem B1755763 : Blo 1754578 1755763 := bstep (se 1 (by rfl) ⟨1316822, by rfl⟩ : syracuseStep 1755763 = 2633645) B2633645
theorem B1755779 : Blo 1754578 1755779 := bstep (se 1 (by rfl) ⟨1316834, by rfl⟩ : syracuseStep 1755779 = 2633669) B2633669
theorem B2632337 : Blo 1754578 2632337 := bstep (se 2 (by rfl) ⟨987126, by rfl⟩ : syracuseStep 2632337 = 1974253) B1974253
theorem B1755795 : Blo 1754578 1755795 := bstep (se 1 (by rfl) ⟨1316846, by rfl⟩ : syracuseStep 1755795 = 2633693) B2633693
theorem B2632355 : Blo 1754578 2632355 := bstep (se 1 (by rfl) ⟨1974266, by rfl⟩ : syracuseStep 2632355 = 3948533) B3948533
theorem B7498403 : Blo 1754578 7498403 := bstep (se 1 (by rfl) ⟨5623802, by rfl⟩ : syracuseStep 7498403 = 11247605) B11247605
theorem B1755811 : Blo 1754578 1755811 := bstep (se 1 (by rfl) ⟨1316858, by rfl⟩ : syracuseStep 1755811 = 2633717) B2633717
theorem B1755827 : Blo 1754578 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B2632385 : Blo 1754578 2632385 := bstep (se 2 (by rfl) ⟨987144, by rfl⟩ : syracuseStep 2632385 = 1974289) B1974289
theorem B1755843 : Blo 1754578 1755843 := bstep (se 1 (by rfl) ⟨1316882, by rfl⟩ : syracuseStep 1755843 = 2633765) B2633765
theorem B11250373 : Blo 1754578 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B5925581 : Blo 1754578 5925581 := bstep (se 3 (by rfl) ⟨1111046, by rfl⟩ : syracuseStep 5925581 = 2222093) B2222093
theorem B2632403 : Blo 1754578 2632403 := bstep (se 1 (by rfl) ⟨1974302, by rfl⟩ : syracuseStep 2632403 = 3948605) B3948605
theorem B1755859 : Blo 1754578 1755859 := bstep (se 1 (by rfl) ⟨1316894, by rfl⟩ : syracuseStep 1755859 = 2633789) B2633789
theorem B1755875 : Blo 1754578 1755875 := bstep (se 1 (by rfl) ⟨1316906, by rfl⟩ : syracuseStep 1755875 = 2633813) B2633813
theorem B2632433 : Blo 1754578 2632433 := bstep (se 2 (by rfl) ⟨987162, by rfl⟩ : syracuseStep 2632433 = 1974325) B1974325
theorem B1755891 : Blo 1754578 1755891 := bstep (se 1 (by rfl) ⟨1316918, by rfl⟩ : syracuseStep 1755891 = 2633837) B2633837
theorem B2632451 : Blo 1754578 2632451 := bstep (se 1 (by rfl) ⟨1974338, by rfl⟩ : syracuseStep 2632451 = 3948677) B3948677
theorem B5925635 : Blo 1754578 5925635 := bstep (se 1 (by rfl) ⟨4444226, by rfl⟩ : syracuseStep 5925635 = 8888453) B8888453
theorem B1755907 : Blo 1754578 1755907 := bstep (se 1 (by rfl) ⟨1316930, by rfl⟩ : syracuseStep 1755907 = 2633861) B2633861
theorem B3951377 : Blo 1754578 3951377 := bstep (se 2 (by rfl) ⟨1481766, by rfl⟩ : syracuseStep 3951377 = 2963533) B2963533
theorem B1755923 : Blo 1754578 1755923 := bstep (se 1 (by rfl) ⟨1316942, by rfl⟩ : syracuseStep 1755923 = 2633885) B2633885
theorem B2632481 : Blo 1754578 2632481 := bstep (se 2 (by rfl) ⟨987180, by rfl⟩ : syracuseStep 2632481 = 1974361) B1974361
theorem B1755939 : Blo 1754578 1755939 := bstep (se 1 (by rfl) ⟨1316954, by rfl⟩ : syracuseStep 1755939 = 2633909) B2633909
theorem B3951395 : Blo 1754578 3951395 := bstep (se 1 (by rfl) ⟨2963546, by rfl⟩ : syracuseStep 3951395 = 5927093) B5927093
theorem B8440625 : Blo 1754578 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B2632499 : Blo 1754578 2632499 := bstep (se 1 (by rfl) ⟨1974374, by rfl⟩ : syracuseStep 2632499 = 3948749) B3948749
theorem B1755955 : Blo 1754578 1755955 := bstep (se 1 (by rfl) ⟨1316966, by rfl⟩ : syracuseStep 1755955 = 2633933) B2633933
theorem B1755971 : Blo 1754578 1755971 := bstep (se 1 (by rfl) ⟨1316978, by rfl⟩ : syracuseStep 1755971 = 2633957) B2633957
theorem B2632529 : Blo 1754578 2632529 := bstep (se 2 (by rfl) ⟨987198, by rfl⟩ : syracuseStep 2632529 = 1974397) B1974397
theorem B1755987 : Blo 1754578 1755987 := bstep (se 1 (by rfl) ⟨1316990, by rfl⟩ : syracuseStep 1755987 = 2633981) B2633981
theorem B2632547 : Blo 1754578 2632547 := bstep (se 1 (by rfl) ⟨1974410, by rfl⟩ : syracuseStep 2632547 = 3948821) B3948821
theorem B1756003 : Blo 1754578 1756003 := bstep (se 1 (by rfl) ⟨1317002, by rfl⟩ : syracuseStep 1756003 = 2634005) B2634005
theorem B1756019 : Blo 1754578 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B2632577 : Blo 1754578 2632577 := bstep (se 2 (by rfl) ⟨987216, by rfl⟩ : syracuseStep 2632577 = 1974433) B1974433
theorem B1756035 : Blo 1754578 1756035 := bstep (se 1 (by rfl) ⟨1317026, by rfl⟩ : syracuseStep 1756035 = 2634053) B2634053
theorem B18025357 : Blo 1754578 18025357 := bstep (se 3 (by rfl) ⟨3379754, by rfl⟩ : syracuseStep 18025357 = 6759509) B6759509
theorem B13519757 : Blo 1754578 13519757 := bstep (se 3 (by rfl) ⟨2534954, by rfl⟩ : syracuseStep 13519757 = 5069909) B5069909
theorem B2632595 : Blo 1754578 2632595 := bstep (se 1 (by rfl) ⟨1974446, by rfl⟩ : syracuseStep 2632595 = 3948893) B3948893
theorem B1756051 : Blo 1754578 1756051 := bstep (se 1 (by rfl) ⟨1317038, by rfl⟩ : syracuseStep 1756051 = 2634077) B2634077
theorem B8883107 : Blo 1754578 8883107 := bstep (se 1 (by rfl) ⟨6662330, by rfl⟩ : syracuseStep 8883107 = 13324661) B13324661
theorem B1756067 : Blo 1754578 1756067 := bstep (se 1 (by rfl) ⟨1317050, by rfl⟩ : syracuseStep 1756067 = 2634101) B2634101
theorem B2632625 : Blo 1754578 2632625 := bstep (se 2 (by rfl) ⟨987234, by rfl⟩ : syracuseStep 2632625 = 1974469) B1974469
theorem B1756083 : Blo 1754578 1756083 := bstep (se 1 (by rfl) ⟨1317062, by rfl⟩ : syracuseStep 1756083 = 2634125) B2634125
theorem B2632643 : Blo 1754578 2632643 := bstep (se 1 (by rfl) ⟨1974482, by rfl⟩ : syracuseStep 2632643 = 3948965) B3948965
theorem B1756099 : Blo 1754578 1756099 := bstep (se 1 (by rfl) ⟨1317074, by rfl⟩ : syracuseStep 1756099 = 2634149) B2634149
theorem B1756115 : Blo 1754578 1756115 := bstep (se 1 (by rfl) ⟨1317086, by rfl⟩ : syracuseStep 1756115 = 2634173) B2634173
theorem B2632673 : Blo 1754578 2632673 := bstep (se 2 (by rfl) ⟨987252, by rfl⟩ : syracuseStep 2632673 = 1974505) B1974505
theorem B1756131 : Blo 1754578 1756131 := bstep (se 1 (by rfl) ⟨1317098, by rfl⟩ : syracuseStep 1756131 = 2634197) B2634197
theorem B2632691 : Blo 1754578 2632691 := bstep (se 1 (by rfl) ⟨1974518, by rfl⟩ : syracuseStep 2632691 = 3949037) B3949037
theorem B1756147 : Blo 1754578 1756147 := bstep (se 1 (by rfl) ⟨1317110, by rfl⟩ : syracuseStep 1756147 = 2634221) B2634221
theorem B1756163 : Blo 1754578 1756163 := bstep (se 1 (by rfl) ⟨1317122, by rfl⟩ : syracuseStep 1756163 = 2634245) B2634245
theorem B6663181 : Blo 1754578 6663181 := bstep (se 3 (by rfl) ⟨1249346, by rfl⟩ : syracuseStep 6663181 = 2498693) B2498693
theorem B11398157 : Blo 1754578 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B2632721 : Blo 1754578 2632721 := bstep (se 2 (by rfl) ⟨987270, by rfl⟩ : syracuseStep 2632721 = 1974541) B1974541
theorem B5925905 : Blo 1754578 5925905 := bstep (se 2 (by rfl) ⟨2222214, by rfl⟩ : syracuseStep 5925905 = 4444429) B4444429
theorem B1756179 : Blo 1754578 1756179 := bstep (se 1 (by rfl) ⟨1317134, by rfl⟩ : syracuseStep 1756179 = 2634269) B2634269
theorem B2632739 : Blo 1754578 2632739 := bstep (se 1 (by rfl) ⟨1974554, by rfl⟩ : syracuseStep 2632739 = 3949109) B3949109
theorem B1756195 : Blo 1754578 1756195 := bstep (se 1 (by rfl) ⟨1317146, by rfl⟩ : syracuseStep 1756195 = 2634293) B2634293
theorem B3951665 : Blo 1754578 3951665 := bstep (se 2 (by rfl) ⟨1481874, by rfl⟩ : syracuseStep 3951665 = 2963749) B2963749
theorem B1756211 : Blo 1754578 1756211 := bstep (se 1 (by rfl) ⟨1317158, by rfl⟩ : syracuseStep 1756211 = 2634317) B2634317
theorem B2632769 : Blo 1754578 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B1756227 : Blo 1754578 1756227 := bstep (se 1 (by rfl) ⟨1317170, by rfl⟩ : syracuseStep 1756227 = 2634341) B2634341
theorem B3951683 : Blo 1754578 3951683 := bstep (se 1 (by rfl) ⟨2963762, by rfl⟩ : syracuseStep 3951683 = 5927525) B5927525
theorem B9006157 : Blo 1754578 9006157 := bstep (se 3 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 9006157 = 3377309) B3377309
theorem B2632787 : Blo 1754578 2632787 := bstep (se 1 (by rfl) ⟨1974590, by rfl⟩ : syracuseStep 2632787 = 3949181) B3949181
theorem B1756243 : Blo 1754578 1756243 := bstep (se 1 (by rfl) ⟨1317182, by rfl⟩ : syracuseStep 1756243 = 2634365) B2634365
theorem B1756259 : Blo 1754578 1756259 := bstep (se 1 (by rfl) ⟨1317194, by rfl⟩ : syracuseStep 1756259 = 2634389) B2634389
theorem B2632817 : Blo 1754578 2632817 := bstep (se 2 (by rfl) ⟨987306, by rfl⟩ : syracuseStep 2632817 = 1974613) B1974613
theorem B1756275 : Blo 1754578 1756275 := bstep (se 1 (by rfl) ⟨1317206, by rfl⟩ : syracuseStep 1756275 = 2634413) B2634413
theorem B2632835 : Blo 1754578 2632835 := bstep (se 1 (by rfl) ⟨1974626, by rfl⟩ : syracuseStep 2632835 = 3949253) B3949253
theorem B4746371 : Blo 1754578 4746371 := bstep (se 1 (by rfl) ⟨3559778, by rfl⟩ : syracuseStep 4746371 = 7119557) B7119557
theorem B1756291 : Blo 1754578 1756291 := bstep (se 1 (by rfl) ⟨1317218, by rfl⟩ : syracuseStep 1756291 = 2634437) B2634437
theorem B1756307 : Blo 1754578 1756307 := bstep (se 1 (by rfl) ⟨1317230, by rfl⟩ : syracuseStep 1756307 = 2634461) B2634461
theorem B2632865 : Blo 1754578 2632865 := bstep (se 2 (by rfl) ⟨987324, by rfl⟩ : syracuseStep 2632865 = 1974649) B1974649
theorem B1756323 : Blo 1754578 1756323 := bstep (se 1 (by rfl) ⟨1317242, by rfl⟩ : syracuseStep 1756323 = 2634485) B2634485
theorem B2632883 : Blo 1754578 2632883 := bstep (se 1 (by rfl) ⟨1974662, by rfl⟩ : syracuseStep 2632883 = 3949325) B3949325
theorem B1756339 : Blo 1754578 1756339 := bstep (se 1 (by rfl) ⟨1317254, by rfl⟩ : syracuseStep 1756339 = 2634509) B2634509
theorem B6008003 : Blo 1754578 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B1756355 : Blo 1754578 1756355 := bstep (se 1 (by rfl) ⟨1317266, by rfl⟩ : syracuseStep 1756355 = 2634533) B2634533
theorem B20008133 : Blo 1754578 20008133 := bstep (se 4 (by rfl) ⟨1875762, by rfl⟩ : syracuseStep 20008133 = 3751525) B3751525
theorem B2632913 : Blo 1754578 2632913 := bstep (se 2 (by rfl) ⟨987342, by rfl⟩ : syracuseStep 2632913 = 1974685) B1974685
theorem B1756371 : Blo 1754578 1756371 := bstep (se 1 (by rfl) ⟨1317278, by rfl⟩ : syracuseStep 1756371 = 2634557) B2634557
theorem B2632931 : Blo 1754578 2632931 := bstep (se 1 (by rfl) ⟨1974698, by rfl⟩ : syracuseStep 2632931 = 3949397) B3949397
theorem B1756387 : Blo 1754578 1756387 := bstep (se 1 (by rfl) ⟨1317290, by rfl⟩ : syracuseStep 1756387 = 2634581) B2634581
theorem B1756403 : Blo 1754578 1756403 := bstep (se 1 (by rfl) ⟨1317302, by rfl⟩ : syracuseStep 1756403 = 2634605) B2634605
theorem B2632961 : Blo 1754578 2632961 := bstep (se 2 (by rfl) ⟨987360, by rfl⟩ : syracuseStep 2632961 = 1974721) B1974721
theorem B1756419 : Blo 1754578 1756419 := bstep (se 1 (by rfl) ⟨1317314, by rfl⟩ : syracuseStep 1756419 = 2634629) B2634629
theorem B2632979 : Blo 1754578 2632979 := bstep (se 1 (by rfl) ⟨1974734, by rfl⟩ : syracuseStep 2632979 = 3949469) B3949469
theorem B1756435 : Blo 1754578 1756435 := bstep (se 1 (by rfl) ⟨1317326, by rfl⟩ : syracuseStep 1756435 = 2634653) B2634653
theorem B1756451 : Blo 1754578 1756451 := bstep (se 1 (by rfl) ⟨1317338, by rfl⟩ : syracuseStep 1756451 = 2634677) B2634677
theorem B2633009 : Blo 1754578 2633009 := bstep (se 2 (by rfl) ⟨987378, by rfl⟩ : syracuseStep 2633009 = 1974757) B1974757
theorem B1756467 : Blo 1754578 1756467 := bstep (se 1 (by rfl) ⟨1317350, by rfl⟩ : syracuseStep 1756467 = 2634701) B2634701
theorem B2633027 : Blo 1754578 2633027 := bstep (se 1 (by rfl) ⟨1974770, by rfl⟩ : syracuseStep 2633027 = 3949541) B3949541
theorem B1756483 : Blo 1754578 1756483 := bstep (se 1 (by rfl) ⟨1317362, by rfl⟩ : syracuseStep 1756483 = 2634725) B2634725
theorem B3951953 : Blo 1754578 3951953 := bstep (se 2 (by rfl) ⟨1481982, by rfl⟩ : syracuseStep 3951953 = 2963965) B2963965
theorem B1756499 : Blo 1754578 1756499 := bstep (se 1 (by rfl) ⟨1317374, by rfl⟩ : syracuseStep 1756499 = 2634749) B2634749
theorem B2633057 : Blo 1754578 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B9997667 : Blo 1754578 9997667 := bstep (se 1 (by rfl) ⟨7498250, by rfl⟩ : syracuseStep 9997667 = 14996501) B14996501
theorem B3951971 : Blo 1754578 3951971 := bstep (se 1 (by rfl) ⟨2963978, by rfl⟩ : syracuseStep 3951971 = 5927957) B5927957
theorem B1756515 : Blo 1754578 1756515 := bstep (se 1 (by rfl) ⟨1317386, by rfl⟩ : syracuseStep 1756515 = 2634773) B2634773
theorem B2633075 : Blo 1754578 2633075 := bstep (se 1 (by rfl) ⟨1974806, by rfl⟩ : syracuseStep 2633075 = 3949613) B3949613
theorem B1756531 : Blo 1754578 1756531 := bstep (se 1 (by rfl) ⟨1317398, by rfl⟩ : syracuseStep 1756531 = 2634797) B2634797
theorem B1756547 : Blo 1754578 1756547 := bstep (se 1 (by rfl) ⟨1317410, by rfl⟩ : syracuseStep 1756547 = 2634821) B2634821
theorem B2633105 : Blo 1754578 2633105 := bstep (se 2 (by rfl) ⟨987414, by rfl⟩ : syracuseStep 2633105 = 1974829) B1974829
theorem B1756563 : Blo 1754578 1756563 := bstep (se 1 (by rfl) ⟨1317422, by rfl⟩ : syracuseStep 1756563 = 2634845) B2634845
theorem B3001763 : Blo 1754578 3001763 := bstep (se 1 (by rfl) ⟨2251322, by rfl⟩ : syracuseStep 3001763 = 4502645) B4502645
theorem B2633123 : Blo 1754578 2633123 := bstep (se 1 (by rfl) ⟨1974842, by rfl⟩ : syracuseStep 2633123 = 3949685) B3949685
theorem B4443569 : Blo 1754578 4443569 := bstep (se 2 (by rfl) ⟨1666338, by rfl⟩ : syracuseStep 4443569 = 3332677) B3332677
theorem B2813363 : Blo 1754578 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B2633153 : Blo 1754578 2633153 := bstep (se 2 (by rfl) ⟨987432, by rfl⟩ : syracuseStep 2633153 = 1974865) B1974865
theorem B14241221 : Blo 1754578 14241221 := bstep (se 4 (by rfl) ⟨1335114, by rfl⟩ : syracuseStep 14241221 = 2670229) B2670229
theorem B7114189 : Blo 1754578 7114189 := bstep (se 3 (by rfl) ⟨1333910, by rfl⟩ : syracuseStep 7114189 = 2667821) B2667821
theorem B2633171 : Blo 1754578 2633171 := bstep (se 1 (by rfl) ⟨1974878, by rfl⟩ : syracuseStep 2633171 = 3949757) B3949757
theorem B2960867 : Blo 1754578 2960867 := bstep (se 1 (by rfl) ⟨2220650, by rfl⟩ : syracuseStep 2960867 = 4441301) B4441301
theorem B4443619 : Blo 1754578 4443619 := bstep (se 1 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 4443619 = 6665429) B6665429
theorem B2633201 : Blo 1754578 2633201 := bstep (se 2 (by rfl) ⟨987450, by rfl⟩ : syracuseStep 2633201 = 1974901) B1974901
theorem B2633219 : Blo 1754578 2633219 := bstep (se 1 (by rfl) ⟨1974914, by rfl⟩ : syracuseStep 2633219 = 3949829) B3949829
theorem B2633249 : Blo 1754578 2633249 := bstep (se 2 (by rfl) ⟨987468, by rfl⟩ : syracuseStep 2633249 = 1974937) B1974937
theorem B5926445 : Blo 1754578 5926445 := bstep (se 3 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 5926445 = 2222417) B2222417
theorem B2633267 : Blo 1754578 2633267 := bstep (se 1 (by rfl) ⟨1974950, by rfl⟩ : syracuseStep 2633267 = 3949901) B3949901
theorem B2633297 : Blo 1754578 2633297 := bstep (se 2 (by rfl) ⟨987486, by rfl⟩ : syracuseStep 2633297 = 1974973) B1974973
theorem B2960995 : Blo 1754578 2960995 := bstep (se 1 (by rfl) ⟨2220746, by rfl⟩ : syracuseStep 2960995 = 4441493) B4441493
theorem B2633315 : Blo 1754578 2633315 := bstep (se 1 (by rfl) ⟨1974986, by rfl⟩ : syracuseStep 2633315 = 3949973) B3949973
theorem B5926499 : Blo 1754578 5926499 := bstep (se 1 (by rfl) ⟨4444874, by rfl⟩ : syracuseStep 5926499 = 8889749) B8889749
theorem B4443761 : Blo 1754578 4443761 := bstep (se 2 (by rfl) ⟨1666410, by rfl⟩ : syracuseStep 4443761 = 3332821) B3332821
theorem B8892017 : Blo 1754578 8892017 := bstep (se 2 (by rfl) ⟨3334506, by rfl⟩ : syracuseStep 8892017 = 6669013) B6669013
theorem B2813555 : Blo 1754578 2813555 := bstep (se 1 (by rfl) ⟨2110166, by rfl⟩ : syracuseStep 2813555 = 4220333) B4220333
theorem B3952241 : Blo 1754578 3952241 := bstep (se 2 (by rfl) ⟨1482090, by rfl⟩ : syracuseStep 3952241 = 2964181) B2964181
theorem B2633345 : Blo 1754578 2633345 := bstep (se 2 (by rfl) ⟨987504, by rfl⟩ : syracuseStep 2633345 = 1975009) B1975009
theorem B3952259 : Blo 1754578 3952259 := bstep (se 1 (by rfl) ⟨2964194, by rfl⟩ : syracuseStep 3952259 = 5928389) B5928389
theorem B5000849 : Blo 1754578 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B2633363 : Blo 1754578 2633363 := bstep (se 1 (by rfl) ⟨1975022, by rfl⟩ : syracuseStep 2633363 = 3950045) B3950045
theorem B2633393 : Blo 1754578 2633393 := bstep (se 2 (by rfl) ⟨987522, by rfl⟩ : syracuseStep 2633393 = 1975045) B1975045
theorem B2633411 : Blo 1754578 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B8883917 : Blo 1754578 8883917 := bstep (se 3 (by rfl) ⟨1665734, by rfl⟩ : syracuseStep 8883917 = 3331469) B3331469
theorem B2633441 : Blo 1754578 2633441 := bstep (se 2 (by rfl) ⟨987540, by rfl⟩ : syracuseStep 2633441 = 1975081) B1975081
theorem B2961137 : Blo 1754578 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B2633459 : Blo 1754578 2633459 := bstep (se 1 (by rfl) ⟨1975094, by rfl⟩ : syracuseStep 2633459 = 3950189) B3950189
theorem B2633489 : Blo 1754578 2633489 := bstep (se 2 (by rfl) ⟨987558, by rfl⟩ : syracuseStep 2633489 = 1975117) B1975117
theorem B11243299 : Blo 1754578 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B6663971 : Blo 1754578 6663971 := bstep (se 1 (by rfl) ⟨4997978, by rfl⟩ : syracuseStep 6663971 = 9995957) B9995957
theorem B2633507 : Blo 1754578 2633507 := bstep (se 1 (by rfl) ⟨1975130, by rfl⟩ : syracuseStep 2633507 = 3950261) B3950261
theorem B5623597 : Blo 1754578 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B2633537 : Blo 1754578 2633537 := bstep (se 2 (by rfl) ⟨987576, by rfl⟩ : syracuseStep 2633537 = 1975153) B1975153
theorem B2633555 : Blo 1754578 2633555 := bstep (se 1 (by rfl) ⟨1975166, by rfl⟩ : syracuseStep 2633555 = 3950333) B3950333
theorem B2961265 : Blo 1754578 2961265 := bstep (se 2 (by rfl) ⟨1110474, by rfl⟩ : syracuseStep 2961265 = 2220949) B2220949
theorem B2633585 : Blo 1754578 2633585 := bstep (se 2 (by rfl) ⟨987594, by rfl⟩ : syracuseStep 2633585 = 1975189) B1975189
theorem B5926769 : Blo 1754578 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B2633603 : Blo 1754578 2633603 := bstep (se 1 (by rfl) ⟨1975202, by rfl⟩ : syracuseStep 2633603 = 3950405) B3950405
theorem B2961299 : Blo 1754578 2961299 := bstep (se 1 (by rfl) ⟨2220974, by rfl⟩ : syracuseStep 2961299 = 4441949) B4441949
theorem B2633633 : Blo 1754578 2633633 := bstep (se 2 (by rfl) ⟨987612, by rfl⟩ : syracuseStep 2633633 = 1975225) B1975225
theorem B2633651 : Blo 1754578 2633651 := bstep (se 1 (by rfl) ⟨1975238, by rfl⟩ : syracuseStep 2633651 = 3950477) B3950477
theorem B2633681 : Blo 1754578 2633681 := bstep (se 2 (by rfl) ⟨987630, by rfl⟩ : syracuseStep 2633681 = 1975261) B1975261
theorem B2633699 : Blo 1754578 2633699 := bstep (se 1 (by rfl) ⟨1975274, by rfl⟩ : syracuseStep 2633699 = 3950549) B3950549
theorem B2633729 : Blo 1754578 2633729 := bstep (se 2 (by rfl) ⟨987648, by rfl⟩ : syracuseStep 2633729 = 1975297) B1975297
theorem B2961427 : Blo 1754578 2961427 := bstep (se 1 (by rfl) ⟨2221070, by rfl⟩ : syracuseStep 2961427 = 4442141) B4442141
theorem B2633747 : Blo 1754578 2633747 := bstep (se 1 (by rfl) ⟨1975310, by rfl⟩ : syracuseStep 2633747 = 3950621) B3950621
theorem B9007139 : Blo 1754578 9007139 := bstep (se 1 (by rfl) ⟨6755354, by rfl⟩ : syracuseStep 9007139 = 13510709) B13510709
theorem B2633777 : Blo 1754578 2633777 := bstep (se 2 (by rfl) ⟨987666, by rfl⟩ : syracuseStep 2633777 = 1975333) B1975333
theorem B2633795 : Blo 1754578 2633795 := bstep (se 1 (by rfl) ⟨1975346, by rfl⟩ : syracuseStep 2633795 = 3950693) B3950693
theorem B2633825 : Blo 1754578 2633825 := bstep (se 2 (by rfl) ⟨987684, by rfl⟩ : syracuseStep 2633825 = 1975369) B1975369
theorem B10678385 : Blo 1754578 10678385 := bstep (se 2 (by rfl) ⟨4004394, by rfl⟩ : syracuseStep 10678385 = 8008789) B8008789
theorem B2371699 : Blo 1754578 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B2633843 : Blo 1754578 2633843 := bstep (se 1 (by rfl) ⟨1975382, by rfl⟩ : syracuseStep 2633843 = 3950765) B3950765
theorem B2633873 : Blo 1754578 2633873 := bstep (se 2 (by rfl) ⟨987702, by rfl⟩ : syracuseStep 2633873 = 1975405) B1975405
theorem B2961569 : Blo 1754578 2961569 := bstep (se 2 (by rfl) ⟨1110588, by rfl⟩ : syracuseStep 2961569 = 2221177) B2221177
theorem B2633891 : Blo 1754578 2633891 := bstep (se 1 (by rfl) ⟨1975418, by rfl⟩ : syracuseStep 2633891 = 3950837) B3950837
theorem B2633921 : Blo 1754578 2633921 := bstep (se 2 (by rfl) ⟨987720, by rfl⟩ : syracuseStep 2633921 = 1975441) B1975441
theorem B2633939 : Blo 1754578 2633939 := bstep (se 1 (by rfl) ⟨1975454, by rfl⟩ : syracuseStep 2633939 = 3950909) B3950909
theorem B2109667 : Blo 1754578 2109667 := bstep (se 1 (by rfl) ⟨1582250, by rfl⟩ : syracuseStep 2109667 = 3164501) B3164501
theorem B2633969 : Blo 1754578 2633969 := bstep (se 2 (by rfl) ⟨987738, by rfl⟩ : syracuseStep 2633969 = 1975477) B1975477
theorem B2633987 : Blo 1754578 2633987 := bstep (se 1 (by rfl) ⟨1975490, by rfl⟩ : syracuseStep 2633987 = 3950981) B3950981
theorem B2961697 : Blo 1754578 2961697 := bstep (se 2 (by rfl) ⟨1110636, by rfl⟩ : syracuseStep 2961697 = 2221273) B2221273
theorem B2634017 : Blo 1754578 2634017 := bstep (se 2 (by rfl) ⟨987756, by rfl⟩ : syracuseStep 2634017 = 1975513) B1975513
theorem B5624099 : Blo 1754578 5624099 := bstep (se 1 (by rfl) ⟨4218074, by rfl⟩ : syracuseStep 5624099 = 8436149) B8436149
theorem B3559715 : Blo 1754578 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B2371889 : Blo 1754578 2371889 := bstep (se 2 (by rfl) ⟨889458, by rfl⟩ : syracuseStep 2371889 = 1778917) B1778917
theorem B2634035 : Blo 1754578 2634035 := bstep (se 1 (by rfl) ⟨1975526, by rfl⟩ : syracuseStep 2634035 = 3951053) B3951053
theorem B2961731 : Blo 1754578 2961731 := bstep (se 1 (by rfl) ⟨2221298, by rfl⟩ : syracuseStep 2961731 = 4442597) B4442597
theorem B2634065 : Blo 1754578 2634065 := bstep (se 2 (by rfl) ⟨987774, by rfl⟩ : syracuseStep 2634065 = 1975549) B1975549
theorem B2634083 : Blo 1754578 2634083 := bstep (se 1 (by rfl) ⟨1975562, by rfl⟩ : syracuseStep 2634083 = 3951125) B3951125
theorem B2634113 : Blo 1754578 2634113 := bstep (se 2 (by rfl) ⟨987792, by rfl⟩ : syracuseStep 2634113 = 1975585) B1975585
theorem B5927309 : Blo 1754578 5927309 := bstep (se 3 (by rfl) ⟨1111370, by rfl⟩ : syracuseStep 5927309 = 2222741) B2222741
theorem B2634131 : Blo 1754578 2634131 := bstep (se 1 (by rfl) ⟨1975598, by rfl⟩ : syracuseStep 2634131 = 3951197) B3951197
theorem B6664625 : Blo 1754578 6664625 := bstep (se 2 (by rfl) ⟨2499234, by rfl⟩ : syracuseStep 6664625 = 4998469) B4998469
theorem B2634161 : Blo 1754578 2634161 := bstep (se 2 (by rfl) ⟨987810, by rfl⟩ : syracuseStep 2634161 = 1975621) B1975621
theorem B2961859 : Blo 1754578 2961859 := bstep (se 1 (by rfl) ⟨2221394, by rfl⟩ : syracuseStep 2961859 = 4442789) B4442789
theorem B2634179 : Blo 1754578 2634179 := bstep (se 1 (by rfl) ⟨1975634, by rfl⟩ : syracuseStep 2634179 = 3951269) B3951269
theorem B5927363 : Blo 1754578 5927363 := bstep (se 1 (by rfl) ⟨4445522, by rfl⟩ : syracuseStep 5927363 = 8891045) B8891045
theorem B2634209 : Blo 1754578 2634209 := bstep (se 2 (by rfl) ⟨987828, by rfl⟩ : syracuseStep 2634209 = 1975657) B1975657
theorem B2634227 : Blo 1754578 2634227 := bstep (se 1 (by rfl) ⟨1975670, by rfl⟩ : syracuseStep 2634227 = 3951341) B3951341
theorem B2634257 : Blo 1754578 2634257 := bstep (se 2 (by rfl) ⟨987846, by rfl⟩ : syracuseStep 2634257 = 1975693) B1975693
theorem B2634275 : Blo 1754578 2634275 := bstep (se 1 (by rfl) ⟨1975706, by rfl⟩ : syracuseStep 2634275 = 3951413) B3951413
theorem B2634305 : Blo 1754578 2634305 := bstep (se 2 (by rfl) ⟨987864, by rfl⟩ : syracuseStep 2634305 = 1975729) B1975729
theorem B2962001 : Blo 1754578 2962001 := bstep (se 2 (by rfl) ⟨1110750, by rfl⟩ : syracuseStep 2962001 = 2221501) B2221501
theorem B4444753 : Blo 1754578 4444753 := bstep (se 2 (by rfl) ⟨1666782, by rfl⟩ : syracuseStep 4444753 = 3333565) B3333565
theorem B2634323 : Blo 1754578 2634323 := bstep (se 1 (by rfl) ⟨1975742, by rfl⟩ : syracuseStep 2634323 = 3951485) B3951485
theorem B2110051 : Blo 1754578 2110051 := bstep (se 1 (by rfl) ⟨1582538, by rfl⟩ : syracuseStep 2110051 = 3165077) B3165077
theorem B2634353 : Blo 1754578 2634353 := bstep (se 2 (by rfl) ⟨987882, by rfl⟩ : syracuseStep 2634353 = 1975765) B1975765
theorem B2634371 : Blo 1754578 2634371 := bstep (se 1 (by rfl) ⟨1975778, by rfl⟩ : syracuseStep 2634371 = 3951557) B3951557
theorem B43274893 : Blo 1754578 43274893 := bstep (se 3 (by rfl) ⟨8114042, by rfl⟩ : syracuseStep 43274893 = 16228085) B16228085
theorem B2634401 : Blo 1754578 2634401 := bstep (se 2 (by rfl) ⟨987900, by rfl⟩ : syracuseStep 2634401 = 1975801) B1975801
theorem B2634419 : Blo 1754578 2634419 := bstep (se 1 (by rfl) ⟨1975814, by rfl⟩ : syracuseStep 2634419 = 3951629) B3951629
theorem B2962129 : Blo 1754578 2962129 := bstep (se 2 (by rfl) ⟨1110798, by rfl⟩ : syracuseStep 2962129 = 2221597) B2221597
theorem B2634449 : Blo 1754578 2634449 := bstep (se 2 (by rfl) ⟨987918, by rfl⟩ : syracuseStep 2634449 = 1975837) B1975837
theorem B5927633 : Blo 1754578 5927633 := bstep (se 2 (by rfl) ⟨2222862, by rfl⟩ : syracuseStep 5927633 = 4445725) B4445725
theorem B2634467 : Blo 1754578 2634467 := bstep (se 1 (by rfl) ⟨1975850, by rfl⟩ : syracuseStep 2634467 = 3951701) B3951701
theorem B2962163 : Blo 1754578 2962163 := bstep (se 1 (by rfl) ⟨2221622, by rfl⟩ : syracuseStep 2962163 = 4443245) B4443245
theorem B2634497 : Blo 1754578 2634497 := bstep (se 2 (by rfl) ⟨987936, by rfl⟩ : syracuseStep 2634497 = 1975873) B1975873
theorem B2634515 : Blo 1754578 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B2634545 : Blo 1754578 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B2634563 : Blo 1754578 2634563 := bstep (se 1 (by rfl) ⟨1975922, by rfl⟩ : syracuseStep 2634563 = 3951845) B3951845
theorem B2634593 : Blo 1754578 2634593 := bstep (se 2 (by rfl) ⟨987972, by rfl⟩ : syracuseStep 2634593 = 1975945) B1975945
theorem B4445027 : Blo 1754578 4445027 := bstep (se 1 (by rfl) ⟨3333770, by rfl⟩ : syracuseStep 4445027 = 6667541) B6667541
theorem B2962291 : Blo 1754578 2962291 := bstep (se 1 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 2962291 = 4443437) B4443437
theorem B2634611 : Blo 1754578 2634611 := bstep (se 1 (by rfl) ⟨1975958, by rfl⟩ : syracuseStep 2634611 = 3951917) B3951917
theorem B2634641 : Blo 1754578 2634641 := bstep (se 2 (by rfl) ⟨987990, by rfl⟩ : syracuseStep 2634641 = 1975981) B1975981
theorem B2634659 : Blo 1754578 2634659 := bstep (se 1 (by rfl) ⟨1975994, by rfl⟩ : syracuseStep 2634659 = 3951989) B3951989
theorem B2634689 : Blo 1754578 2634689 := bstep (se 2 (by rfl) ⟨988008, by rfl⟩ : syracuseStep 2634689 = 1976017) B1976017
theorem B2634707 : Blo 1754578 2634707 := bstep (se 1 (by rfl) ⟨1976030, by rfl⟩ : syracuseStep 2634707 = 3952061) B3952061
theorem B2634737 : Blo 1754578 2634737 := bstep (se 2 (by rfl) ⟨988026, by rfl⟩ : syracuseStep 2634737 = 1976053) B1976053
theorem B2962433 : Blo 1754578 2962433 := bstep (se 2 (by rfl) ⟨1110912, by rfl⟩ : syracuseStep 2962433 = 2221825) B2221825
theorem B2634755 : Blo 1754578 2634755 := bstep (se 1 (by rfl) ⟨1976066, by rfl⟩ : syracuseStep 2634755 = 3952133) B3952133
theorem B2634785 : Blo 1754578 2634785 := bstep (se 2 (by rfl) ⟨988044, by rfl⟩ : syracuseStep 2634785 = 1976089) B1976089
theorem B4445219 : Blo 1754578 4445219 := bstep (se 1 (by rfl) ⟨3333914, by rfl⟩ : syracuseStep 4445219 = 6667829) B6667829
theorem B2634803 : Blo 1754578 2634803 := bstep (se 1 (by rfl) ⟨1976102, by rfl⟩ : syracuseStep 2634803 = 3952205) B3952205
theorem B2634833 : Blo 1754578 2634833 := bstep (se 2 (by rfl) ⟨988062, by rfl⟩ : syracuseStep 2634833 = 1976125) B1976125
theorem B3003475 : Blo 1754578 3003475 := bstep (se 1 (by rfl) ⟨2252606, by rfl⟩ : syracuseStep 3003475 = 4505213) B4505213
theorem B3748963 : Blo 1754578 3748963 := bstep (se 1 (by rfl) ⟨2811722, by rfl⟩ : syracuseStep 3748963 = 5623445) B5623445
theorem B2634851 : Blo 1754578 2634851 := bstep (se 1 (by rfl) ⟨1976138, by rfl⟩ : syracuseStep 2634851 = 3952277) B3952277
theorem B2962561 : Blo 1754578 2962561 := bstep (se 2 (by rfl) ⟨1110960, by rfl⟩ : syracuseStep 2962561 = 2221921) B2221921
theorem B2962595 : Blo 1754578 2962595 := bstep (se 1 (by rfl) ⟨2221946, by rfl⟩ : syracuseStep 2962595 = 4443893) B4443893
theorem B3003571 : Blo 1754578 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B9999557 : Blo 1754578 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B5928173 : Blo 1754578 5928173 := bstep (se 3 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 5928173 = 2223065) B2223065
theorem B3331363 : Blo 1754578 3331363 := bstep (se 1 (by rfl) ⟨2498522, by rfl⟩ : syracuseStep 3331363 = 4997045) B4997045
theorem B2962723 : Blo 1754578 2962723 := bstep (se 1 (by rfl) ⟨2222042, by rfl⟩ : syracuseStep 2962723 = 4444085) B4444085
theorem B5928227 : Blo 1754578 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B3560753 : Blo 1754578 3560753 := bstep (se 2 (by rfl) ⟨1335282, by rfl⟩ : syracuseStep 3560753 = 2670565) B2670565
theorem B43308341 : Blo 1754578 43308341 := bstep (se 5 (by rfl) ⟨2030078, by rfl⟩ : syracuseStep 43308341 = 4060157) B4060157
theorem B2962865 : Blo 1754578 2962865 := bstep (se 2 (by rfl) ⟨1111074, by rfl⟩ : syracuseStep 2962865 = 2222149) B2222149
theorem B3331523 : Blo 1754578 3331523 := bstep (se 1 (by rfl) ⟨2498642, by rfl⟩ : syracuseStep 3331523 = 4997285) B4997285
theorem B2962993 : Blo 1754578 2962993 := bstep (se 2 (by rfl) ⟨1111122, by rfl⟩ : syracuseStep 2962993 = 2222245) B2222245
theorem B2963027 : Blo 1754578 2963027 := bstep (se 1 (by rfl) ⟨2222270, by rfl⟩ : syracuseStep 2963027 = 4444541) B4444541
theorem B5625443 : Blo 1754578 5625443 := bstep (se 1 (by rfl) ⟨4219082, by rfl⟩ : syracuseStep 5625443 = 8438165) B8438165
theorem B10679941 : Blo 1754578 10679941 := bstep (se 4 (by rfl) ⟨1001244, by rfl⟩ : syracuseStep 10679941 = 2002489) B2002489
theorem B6411917 : Blo 1754578 6411917 := bstep (se 3 (by rfl) ⟨1202234, by rfl⟩ : syracuseStep 6411917 = 2404469) B2404469
theorem B2668211 : Blo 1754578 2668211 := bstep (se 1 (by rfl) ⟨2001158, by rfl⟩ : syracuseStep 2668211 = 4002317) B4002317
theorem B2963155 : Blo 1754578 2963155 := bstep (se 1 (by rfl) ⟨2222366, by rfl⟩ : syracuseStep 2963155 = 4444733) B4444733
theorem B12015373 : Blo 1754578 12015373 := bstep (se 3 (by rfl) ⟨2252882, by rfl⟩ : syracuseStep 12015373 = 4505765) B4505765
theorem B2029331 : Blo 1754578 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B4216643 : Blo 1754578 4216643 := bstep (se 1 (by rfl) ⟨3162482, by rfl⟩ : syracuseStep 4216643 = 6324965) B6324965
theorem B2963297 : Blo 1754578 2963297 := bstep (se 2 (by rfl) ⟨1111236, by rfl⟩ : syracuseStep 2963297 = 2222473) B2222473
theorem B6666083 : Blo 1754578 6666083 := bstep (se 1 (by rfl) ⟨4999562, by rfl⟩ : syracuseStep 6666083 = 9999125) B9999125
theorem B6666097 : Blo 1754578 6666097 := bstep (se 2 (by rfl) ⟨2499786, by rfl⟩ : syracuseStep 6666097 = 4999573) B4999573
theorem B10672013 : Blo 1754578 10672013 := bstep (se 3 (by rfl) ⟨2001002, by rfl⟩ : syracuseStep 10672013 = 4002005) B4002005
theorem B16013197 : Blo 1754578 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1873811 : Blo 1754578 1873811 := bstep (se 1 (by rfl) ⟨1405358, by rfl⟩ : syracuseStep 1873811 = 2810717) B2810717
theorem B3749809 : Blo 1754578 3749809 := bstep (se 2 (by rfl) ⟨1406178, by rfl⟩ : syracuseStep 3749809 = 2812357) B2812357
theorem B4446161 : Blo 1754578 4446161 := bstep (se 2 (by rfl) ⟨1667310, by rfl⟩ : syracuseStep 4446161 = 3334621) B3334621
theorem B2963425 : Blo 1754578 2963425 := bstep (se 2 (by rfl) ⟨1111284, by rfl⟩ : syracuseStep 2963425 = 2222569) B2222569
theorem B16881635 : Blo 1754578 16881635 := bstep (se 1 (by rfl) ⟨12661226, by rfl⟩ : syracuseStep 16881635 = 25322453) B25322453
theorem B2373619 : Blo 1754578 2373619 := bstep (se 1 (by rfl) ⟨1780214, by rfl⟩ : syracuseStep 2373619 = 3560429) B3560429
theorem B2963459 : Blo 1754578 2963459 := bstep (se 1 (by rfl) ⟨2222594, by rfl⟩ : syracuseStep 2963459 = 4445189) B4445189
theorem B4446211 : Blo 1754578 4446211 := bstep (se 1 (by rfl) ⟨3334658, by rfl⟩ : syracuseStep 4446211 = 6669317) B6669317
theorem B3799057 : Blo 1754578 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B2963587 : Blo 1754578 2963587 := bstep (se 1 (by rfl) ⟨2222690, by rfl⟩ : syracuseStep 2963587 = 4445381) B4445381
theorem B2668721 : Blo 1754578 2668721 := bstep (se 2 (by rfl) ⟨1000770, by rfl⟩ : syracuseStep 2668721 = 2001541) B2001541
theorem B11253937 : Blo 1754578 11253937 := bstep (se 2 (by rfl) ⟨4220226, by rfl⟩ : syracuseStep 11253937 = 8440453) B8440453
theorem B2029747 : Blo 1754578 2029747 := bstep (se 1 (by rfl) ⟨1522310, by rfl⟩ : syracuseStep 2029747 = 3044621) B3044621
theorem B13326605 : Blo 1754578 13326605 := bstep (se 3 (by rfl) ⟨2498738, by rfl⟩ : syracuseStep 13326605 = 4997477) B4997477
theorem B2963729 : Blo 1754578 2963729 := bstep (se 2 (by rfl) ⟨1111398, by rfl⟩ : syracuseStep 2963729 = 2222797) B2222797
theorem B2373905 : Blo 1754578 2373905 := bstep (se 2 (by rfl) ⟨890214, by rfl⟩ : syracuseStep 2373905 = 1780429) B1780429
theorem B7502129 : Blo 1754578 7502129 := bstep (se 2 (by rfl) ⟨2813298, by rfl⟩ : syracuseStep 7502129 = 5626597) B5626597
theorem B6003089 : Blo 1754578 6003089 := bstep (se 2 (by rfl) ⟨2251158, by rfl⟩ : syracuseStep 6003089 = 4502317) B4502317
theorem B2963857 : Blo 1754578 2963857 := bstep (se 2 (by rfl) ⟨1111446, by rfl⟩ : syracuseStep 2963857 = 2222893) B2222893
theorem B2963891 : Blo 1754578 2963891 := bstep (se 1 (by rfl) ⟨2222918, by rfl⟩ : syracuseStep 2963891 = 4445837) B4445837
theorem B24033763 : Blo 1754578 24033763 := bstep (se 1 (by rfl) ⟨18025322, by rfl⟩ : syracuseStep 24033763 = 36050645) B36050645
theorem B3332593 : Blo 1754578 3332593 := bstep (se 2 (by rfl) ⟨1249722, by rfl⟩ : syracuseStep 3332593 = 2499445) B2499445
theorem B8886833 : Blo 1754578 8886833 := bstep (se 2 (by rfl) ⟨3332562, by rfl⟩ : syracuseStep 8886833 = 6665125) B6665125
theorem B5626417 : Blo 1754578 5626417 := bstep (se 2 (by rfl) ⟨2109906, by rfl⟩ : syracuseStep 5626417 = 4219813) B4219813
theorem B2964019 : Blo 1754578 2964019 := bstep (se 1 (by rfl) ⟨2223014, by rfl⟩ : syracuseStep 2964019 = 4446029) B4446029
theorem B2669123 : Blo 1754578 2669123 := bstep (se 1 (by rfl) ⟨2001842, by rfl⟩ : syracuseStep 2669123 = 4003685) B4003685
theorem B2669171 : Blo 1754578 2669171 := bstep (se 1 (by rfl) ⟨2001878, by rfl⟩ : syracuseStep 2669171 = 4003757) B4003757
theorem B10558129 : Blo 1754578 10558129 := bstep (se 2 (by rfl) ⟨3959298, by rfl⟩ : syracuseStep 10558129 = 7918597) B7918597
theorem B2964161 : Blo 1754578 2964161 := bstep (se 2 (by rfl) ⟨1111560, by rfl⟩ : syracuseStep 2964161 = 2223121) B2223121
theorem B4004579 : Blo 1754578 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B46218005 : Blo 1754578 46218005 := bstep (se 6 (by rfl) ⟨1083234, by rfl⟩ : syracuseStep 46218005 = 2166469) B2166469
theorem B5626673 : Blo 1754578 5626673 := bstep (se 2 (by rfl) ⟨2110002, by rfl⟩ : syracuseStep 5626673 = 4220005) B4220005
theorem B1874755 : Blo 1754578 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B22502285 : Blo 1754578 22502285 := bstep (se 3 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 22502285 = 8438357) B8438357
theorem B25295813 : Blo 1754578 25295813 := bstep (se 4 (by rfl) ⟨2371482, by rfl⟩ : syracuseStep 25295813 = 4742965) B4742965
theorem B9993293 : Blo 1754578 9993293 := bstep (se 3 (by rfl) ⟨1873742, by rfl⟩ : syracuseStep 9993293 = 3747485) B3747485
theorem B33733745 : Blo 1754578 33733745 := bstep (se 2 (by rfl) ⟨12650154, by rfl⟩ : syracuseStep 33733745 = 25300309) B25300309
theorem B4218083 : Blo 1754578 4218083 := bstep (se 1 (by rfl) ⟨3163562, by rfl⟩ : syracuseStep 4218083 = 6327125) B6327125
theorem B6667555 : Blo 1754578 6667555 := bstep (se 1 (by rfl) ⟨5000666, by rfl⟩ : syracuseStep 6667555 = 10001333) B10001333
theorem B5922125 : Blo 1754578 5922125 := bstep (se 3 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 5922125 = 2220797) B2220797
theorem B5922179 : Blo 1754578 5922179 := bstep (se 1 (by rfl) ⟨4441634, by rfl⟩ : syracuseStep 5922179 = 8883269) B8883269
theorem B3947921 : Blo 1754578 3947921 := bstep (se 2 (by rfl) ⟨1480470, by rfl⟩ : syracuseStep 3947921 = 2960941) B2960941
theorem B4218257 : Blo 1754578 4218257 := bstep (se 2 (by rfl) ⟨1581846, by rfl⟩ : syracuseStep 4218257 = 3163693) B3163693
theorem B3947939 : Blo 1754578 3947939 := bstep (se 1 (by rfl) ⟨2960954, by rfl⟩ : syracuseStep 3947939 = 5921909) B5921909
theorem B4218275 : Blo 1754578 4218275 := bstep (se 1 (by rfl) ⟨3163706, by rfl⟩ : syracuseStep 4218275 = 6327413) B6327413
theorem B3333649 : Blo 1754578 3333649 := bstep (se 2 (by rfl) ⟨1250118, by rfl⟩ : syracuseStep 3333649 = 2500237) B2500237
theorem B4996657 : Blo 1754578 4996657 := bstep (se 2 (by rfl) ⟨1873746, by rfl⟩ : syracuseStep 4996657 = 3747493) B3747493
theorem B11247173 : Blo 1754578 11247173 := bstep (se 4 (by rfl) ⟨1054422, by rfl⟩ : syracuseStep 11247173 = 2108845) B2108845
theorem B5340749 : Blo 1754578 5340749 := bstep (se 3 (by rfl) ⟨1001390, by rfl⟩ : syracuseStep 5340749 = 2002781) B2002781
theorem B5856877 : Blo 1754578 5856877 := bstep (se 3 (by rfl) ⟨1098164, by rfl⟩ : syracuseStep 5856877 = 2196329) B2196329
theorem B5922449 : Blo 1754578 5922449 := bstep (se 2 (by rfl) ⟨2220918, by rfl⟩ : syracuseStep 5922449 = 4441837) B4441837
theorem B3948209 : Blo 1754578 3948209 := bstep (se 2 (by rfl) ⟨1480578, by rfl⟩ : syracuseStep 3948209 = 2961157) B2961157
theorem B3948227 : Blo 1754578 3948227 := bstep (se 1 (by rfl) ⟨2961170, by rfl⟩ : syracuseStep 3948227 = 5922341) B5922341
theorem B12680945 : Blo 1754578 12680945 := bstep (se 2 (by rfl) ⟨4755354, by rfl⟩ : syracuseStep 12680945 = 9510709) B9510709
theorem B1974019 : Blo 1754578 1974019 := bstep (se 1 (by rfl) ⟨1480514, by rfl⟩ : syracuseStep 1974019 = 2961029) B2961029
theorem B50634517 : Blo 1754578 50634517 := bstep (se 6 (by rfl) ⟨1186746, by rfl⟩ : syracuseStep 50634517 = 2373493) B2373493
theorem B19996469 : Blo 1754578 19996469 := bstep (se 5 (by rfl) ⟨937334, by rfl⟩ : syracuseStep 19996469 = 1874669) B1874669
theorem B1974163 : Blo 1754578 1974163 := bstep (se 1 (by rfl) ⟨1480622, by rfl⟩ : syracuseStep 1974163 = 2961245) B2961245
theorem B3334051 : Blo 1754578 3334051 := bstep (se 1 (by rfl) ⟨2500538, by rfl⟩ : syracuseStep 3334051 = 5001077) B5001077
theorem B3948497 : Blo 1754578 3948497 := bstep (se 2 (by rfl) ⟨1480686, by rfl⟩ : syracuseStep 3948497 = 2961373) B2961373
theorem B3334097 : Blo 1754578 3334097 := bstep (se 2 (by rfl) ⟨1250286, by rfl⟩ : syracuseStep 3334097 = 2500573) B2500573
theorem B2670545 : Blo 1754578 2670545 := bstep (se 2 (by rfl) ⟨1001454, by rfl⟩ : syracuseStep 2670545 = 2002909) B2002909
theorem B3948515 : Blo 1754578 3948515 := bstep (se 1 (by rfl) ⟨2961386, by rfl⟩ : syracuseStep 3948515 = 5922773) B5922773
theorem B8888291 : Blo 1754578 8888291 := bstep (se 1 (by rfl) ⟨6666218, by rfl⟩ : syracuseStep 8888291 = 13332437) B13332437
theorem B9994225 : Blo 1754578 9994225 := bstep (se 2 (by rfl) ⟨3747834, by rfl⟩ : syracuseStep 9994225 = 7495669) B7495669
theorem B3948569 : Blo 1754578 3948569 := bstep (se 2 (by rfl) ⟨1480713, by rfl⟩ : syracuseStep 3948569 = 2961427) B2961427
theorem B5922881 : Blo 1754578 5922881 := bstep (se 2 (by rfl) ⟨2221080, by rfl⟩ : syracuseStep 5922881 = 4442161) B4442161
theorem B7118923 : Blo 1754578 7118923 := bstep (se 1 (by rfl) ⟨5339192, by rfl⟩ : syracuseStep 7118923 = 10678385) B10678385
theorem B24019037 : Blo 1754578 24019037 := bstep (se 3 (by rfl) ⟨4503569, by rfl⟩ : syracuseStep 24019037 = 9007139) B9007139
theorem B1974379 : Blo 1754578 1974379 := bstep (se 1 (by rfl) ⟨1480784, by rfl⟩ : syracuseStep 1974379 = 2961569) B2961569
theorem B3948659 : Blo 1754578 3948659 := bstep (se 1 (by rfl) ⟨2961494, by rfl⟩ : syracuseStep 3948659 = 5922989) B5922989
theorem B3948695 : Blo 1754578 3948695 := bstep (se 1 (by rfl) ⟨2961521, by rfl⟩ : syracuseStep 3948695 = 5923043) B5923043
theorem B1974487 : Blo 1754578 1974487 := bstep (se 1 (by rfl) ⟨1480865, by rfl⟩ : syracuseStep 1974487 = 2961731) B2961731
theorem B14999813 : Blo 1754578 14999813 := bstep (se 4 (by rfl) ⟨1406232, by rfl⟩ : syracuseStep 14999813 = 2812465) B2812465
theorem B3948875 : Blo 1754578 3948875 := bstep (se 1 (by rfl) ⟨2961656, by rfl⟩ : syracuseStep 3948875 = 5923313) B5923313
theorem B12656989 : Blo 1754578 12656989 := bstep (se 3 (by rfl) ⟨2373185, by rfl⟩ : syracuseStep 12656989 = 4746371) B4746371
theorem B3948929 : Blo 1754578 3948929 := bstep (se 2 (by rfl) ⟨1480848, by rfl⟩ : syracuseStep 3948929 = 2961697) B2961697
theorem B1974667 : Blo 1754578 1974667 := bstep (se 1 (by rfl) ⟨1481000, by rfl⟩ : syracuseStep 1974667 = 2962001) B2962001
theorem B1974775 : Blo 1754578 1974775 := bstep (se 1 (by rfl) ⟨1481081, by rfl⟩ : syracuseStep 1974775 = 2962163) B2962163
theorem B3949145 : Blo 1754578 3949145 := bstep (se 2 (by rfl) ⟨1480929, by rfl⟩ : syracuseStep 3949145 = 2961859) B2961859
theorem B5923421 : Blo 1754578 5923421 := bstep (se 3 (by rfl) ⟨1110641, by rfl⟩ : syracuseStep 5923421 = 2221283) B2221283
theorem B12649061 : Blo 1754578 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B1974955 : Blo 1754578 1974955 := bstep (se 1 (by rfl) ⟨1481216, by rfl⟩ : syracuseStep 1974955 = 2962433) B2962433
theorem B3949235 : Blo 1754578 3949235 := bstep (se 1 (by rfl) ⟨2961926, by rfl⟩ : syracuseStep 3949235 = 5923853) B5923853
theorem B56959685 : Blo 1754578 56959685 := bstep (se 4 (by rfl) ⟨5339970, by rfl⟩ : syracuseStep 56959685 = 10679941) B10679941
theorem B3949271 : Blo 1754578 3949271 := bstep (se 1 (by rfl) ⟨2961953, by rfl⟩ : syracuseStep 3949271 = 5923907) B5923907
theorem B1975063 : Blo 1754578 1975063 := bstep (se 1 (by rfl) ⟨1481297, by rfl⟩ : syracuseStep 1975063 = 2962595) B2962595
theorem B6325037 : Blo 1754578 6325037 := bstep (se 3 (by rfl) ⟨1185944, by rfl⟩ : syracuseStep 6325037 = 2371889) B2371889
theorem B3949451 : Blo 1754578 3949451 := bstep (se 1 (by rfl) ⟨2962088, by rfl⟩ : syracuseStep 3949451 = 5924177) B5924177
theorem B15000497 : Blo 1754578 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B3949505 : Blo 1754578 3949505 := bstep (se 2 (by rfl) ⟨1481064, by rfl⟩ : syracuseStep 3949505 = 2962129) B2962129
theorem B1975243 : Blo 1754578 1975243 := bstep (se 1 (by rfl) ⟨1481432, by rfl⟩ : syracuseStep 1975243 = 2962865) B2962865
theorem B2221015 : Blo 1754578 2221015 := bstep (se 1 (by rfl) ⟨1665761, by rfl⟩ : syracuseStep 2221015 = 3331523) B3331523
theorem B1975351 : Blo 1754578 1975351 := bstep (se 1 (by rfl) ⟨1481513, by rfl⟩ : syracuseStep 1975351 = 2963027) B2963027
theorem B2499673 : Blo 1754578 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B8004701 : Blo 1754578 8004701 := bstep (se 3 (by rfl) ⟨1500881, by rfl⟩ : syracuseStep 8004701 = 3001763) B3001763
theorem B11248733 : Blo 1754578 11248733 := bstep (se 3 (by rfl) ⟨2109137, by rfl⟩ : syracuseStep 11248733 = 4218275) B4218275
theorem B1778807 : Blo 1754578 1778807 := bstep (se 1 (by rfl) ⟨1334105, by rfl⟩ : syracuseStep 1778807 = 2668211) B2668211
theorem B3949721 : Blo 1754578 3949721 := bstep (se 2 (by rfl) ⟨1481145, by rfl⟩ : syracuseStep 3949721 = 2962291) B2962291
theorem B6669485 : Blo 1754578 6669485 := bstep (se 3 (by rfl) ⟨1250528, by rfl⟩ : syracuseStep 6669485 = 2501057) B2501057
theorem B2811095 : Blo 1754578 2811095 := bstep (se 1 (by rfl) ⟨2108321, by rfl⟩ : syracuseStep 2811095 = 4216643) B4216643
theorem B1975531 : Blo 1754578 1975531 := bstep (se 1 (by rfl) ⟨1481648, by rfl⟩ : syracuseStep 1975531 = 2963297) B2963297
theorem B3949811 : Blo 1754578 3949811 := bstep (se 1 (by rfl) ⟨2962358, by rfl⟩ : syracuseStep 3949811 = 5924717) B5924717
theorem B3949847 : Blo 1754578 3949847 := bstep (se 1 (by rfl) ⟨2962385, by rfl⟩ : syracuseStep 3949847 = 5924771) B5924771
theorem B1975639 : Blo 1754578 1975639 := bstep (se 1 (by rfl) ⟨1481729, by rfl⟩ : syracuseStep 1975639 = 2963459) B2963459
theorem B3950027 : Blo 1754578 3950027 := bstep (se 1 (by rfl) ⟨2962520, by rfl⟩ : syracuseStep 3950027 = 5925041) B5925041
theorem B1754583 : Blo 1754578 1754583 := bstep (se 1 (by rfl) ⟨1315937, by rfl⟩ : syracuseStep 1754583 = 2631875) B2631875
theorem B4998617 : Blo 1754578 4998617 := bstep (se 2 (by rfl) ⟨1874481, by rfl⟩ : syracuseStep 4998617 = 3748963) B3748963
theorem B1754603 : Blo 1754578 1754603 := bstep (se 1 (by rfl) ⟨1315952, by rfl⟩ : syracuseStep 1754603 = 2631905) B2631905
theorem B1754615 : Blo 1754578 1754615 := bstep (se 1 (by rfl) ⟨1315961, by rfl⟩ : syracuseStep 1754615 = 2631923) B2631923
theorem B3950081 : Blo 1754578 3950081 := bstep (se 2 (by rfl) ⟨1481280, by rfl⟩ : syracuseStep 3950081 = 2962561) B2962561
theorem B1754635 : Blo 1754578 1754635 := bstep (se 1 (by rfl) ⟨1315976, by rfl⟩ : syracuseStep 1754635 = 2631953) B2631953
theorem B1975819 : Blo 1754578 1975819 := bstep (se 1 (by rfl) ⟨1481864, by rfl⟩ : syracuseStep 1975819 = 2963729) B2963729
theorem B1754647 : Blo 1754578 1754647 := bstep (se 1 (by rfl) ⟨1315985, by rfl⟩ : syracuseStep 1754647 = 2631971) B2631971
theorem B1754667 : Blo 1754578 1754667 := bstep (se 1 (by rfl) ⟨1316000, by rfl⟩ : syracuseStep 1754667 = 2632001) B2632001
theorem B1754679 : Blo 1754578 1754679 := bstep (se 1 (by rfl) ⟨1316009, by rfl⟩ : syracuseStep 1754679 = 2632019) B2632019
theorem B29992517 : Blo 1754578 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B1754699 : Blo 1754578 1754699 := bstep (se 1 (by rfl) ⟨1316024, by rfl⟩ : syracuseStep 1754699 = 2632049) B2632049
theorem B4441675 : Blo 1754578 4441675 := bstep (se 1 (by rfl) ⟨3331256, by rfl⟩ : syracuseStep 4441675 = 6662513) B6662513
theorem B1754711 : Blo 1754578 1754711 := bstep (se 1 (by rfl) ⟨1316033, by rfl⟩ : syracuseStep 1754711 = 2632067) B2632067
theorem B1754731 : Blo 1754578 1754731 := bstep (se 1 (by rfl) ⟨1316048, by rfl⟩ : syracuseStep 1754731 = 2632097) B2632097
theorem B1754743 : Blo 1754578 1754743 := bstep (se 1 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 1754743 = 2632115) B2632115
theorem B1975927 : Blo 1754578 1975927 := bstep (se 1 (by rfl) ⟨1481945, by rfl⟩ : syracuseStep 1975927 = 2963891) B2963891
theorem B1754763 : Blo 1754578 1754763 := bstep (se 1 (by rfl) ⟨1316072, by rfl⟩ : syracuseStep 1754763 = 2632145) B2632145
theorem B1754775 : Blo 1754578 1754775 := bstep (se 1 (by rfl) ⟨1316081, by rfl⟩ : syracuseStep 1754775 = 2632163) B2632163
theorem B1754795 : Blo 1754578 1754795 := bstep (se 1 (by rfl) ⟨1316096, by rfl⟩ : syracuseStep 1754795 = 2632193) B2632193
theorem B1754807 : Blo 1754578 1754807 := bstep (se 1 (by rfl) ⟨1316105, by rfl⟩ : syracuseStep 1754807 = 2632211) B2632211
theorem B1754827 : Blo 1754578 1754827 := bstep (se 1 (by rfl) ⟨1316120, by rfl⟩ : syracuseStep 1754827 = 2632241) B2632241
theorem B5924555 : Blo 1754578 5924555 := bstep (se 1 (by rfl) ⟨4443416, by rfl⟩ : syracuseStep 5924555 = 8886833) B8886833
theorem B17098445 : Blo 1754578 17098445 := bstep (se 3 (by rfl) ⟨3205958, by rfl⟩ : syracuseStep 17098445 = 6411917) B6411917
theorem B1754839 : Blo 1754578 1754839 := bstep (se 1 (by rfl) ⟨1316129, by rfl⟩ : syracuseStep 1754839 = 2632259) B2632259
theorem B4441817 : Blo 1754578 4441817 := bstep (se 2 (by rfl) ⟨1665681, by rfl⟩ : syracuseStep 4441817 = 3331363) B3331363
theorem B1779415 : Blo 1754578 1779415 := bstep (se 1 (by rfl) ⟨1334561, by rfl⟩ : syracuseStep 1779415 = 2669123) B2669123
theorem B3950297 : Blo 1754578 3950297 := bstep (se 2 (by rfl) ⟨1481361, by rfl⟩ : syracuseStep 3950297 = 2962723) B2962723
theorem B8890073 : Blo 1754578 8890073 := bstep (se 2 (by rfl) ⟨3333777, by rfl⟩ : syracuseStep 8890073 = 6667555) B6667555
theorem B1754859 : Blo 1754578 1754859 := bstep (se 1 (by rfl) ⟨1316144, by rfl⟩ : syracuseStep 1754859 = 2632289) B2632289
theorem B1754871 : Blo 1754578 1754871 := bstep (se 1 (by rfl) ⟨1316153, by rfl⟩ : syracuseStep 1754871 = 2632307) B2632307
theorem B1754891 : Blo 1754578 1754891 := bstep (se 1 (by rfl) ⟨1316168, by rfl⟩ : syracuseStep 1754891 = 2632337) B2632337
theorem B1754903 : Blo 1754578 1754903 := bstep (se 1 (by rfl) ⟨1316177, by rfl⟩ : syracuseStep 1754903 = 2632355) B2632355
theorem B4998935 : Blo 1754578 4998935 := bstep (se 1 (by rfl) ⟨3749201, by rfl⟩ : syracuseStep 4998935 = 7498403) B7498403
theorem B1754923 : Blo 1754578 1754923 := bstep (se 1 (by rfl) ⟨1316192, by rfl⟩ : syracuseStep 1754923 = 2632385) B2632385
theorem B1976107 : Blo 1754578 1976107 := bstep (se 1 (by rfl) ⟨1482080, by rfl⟩ : syracuseStep 1976107 = 2964161) B2964161
theorem B3950387 : Blo 1754578 3950387 := bstep (se 1 (by rfl) ⟨2962790, by rfl⟩ : syracuseStep 3950387 = 5925581) B5925581
theorem B1754935 : Blo 1754578 1754935 := bstep (se 1 (by rfl) ⟨1316201, by rfl⟩ : syracuseStep 1754935 = 2632403) B2632403
theorem B1754955 : Blo 1754578 1754955 := bstep (se 1 (by rfl) ⟨1316216, by rfl⟩ : syracuseStep 1754955 = 2632433) B2632433
theorem B1754967 : Blo 1754578 1754967 := bstep (se 1 (by rfl) ⟨1316225, by rfl⟩ : syracuseStep 1754967 = 2632451) B2632451
theorem B3950423 : Blo 1754578 3950423 := bstep (se 1 (by rfl) ⟨2962817, by rfl⟩ : syracuseStep 3950423 = 5925635) B5925635
theorem B30812003 : Blo 1754578 30812003 := bstep (se 1 (by rfl) ⟨23109002, by rfl⟩ : syracuseStep 30812003 = 46218005) B46218005
theorem B16869221 : Blo 1754578 16869221 := bstep (se 4 (by rfl) ⟨1581489, by rfl⟩ : syracuseStep 16869221 = 3162979) B3162979
theorem B1754987 : Blo 1754578 1754987 := bstep (se 1 (by rfl) ⟨1316240, by rfl⟩ : syracuseStep 1754987 = 2632481) B2632481
theorem B1754999 : Blo 1754578 1754999 := bstep (se 1 (by rfl) ⟨1316249, by rfl⟩ : syracuseStep 1754999 = 2632499) B2632499
theorem B1755019 : Blo 1754578 1755019 := bstep (se 1 (by rfl) ⟨1316264, by rfl⟩ : syracuseStep 1755019 = 2632529) B2632529
theorem B1755031 : Blo 1754578 1755031 := bstep (se 1 (by rfl) ⟨1316273, by rfl⟩ : syracuseStep 1755031 = 2632547) B2632547
theorem B1755051 : Blo 1754578 1755051 := bstep (se 1 (by rfl) ⟨1316288, by rfl⟩ : syracuseStep 1755051 = 2632577) B2632577
theorem B15001523 : Blo 1754578 15001523 := bstep (se 1 (by rfl) ⟨11251142, by rfl⟩ : syracuseStep 15001523 = 22502285) B22502285
theorem B1755063 : Blo 1754578 1755063 := bstep (se 1 (by rfl) ⟨1316297, by rfl⟩ : syracuseStep 1755063 = 2632595) B2632595
theorem B1755083 : Blo 1754578 1755083 := bstep (se 1 (by rfl) ⟨1316312, by rfl⟩ : syracuseStep 1755083 = 2632625) B2632625
theorem B1755095 : Blo 1754578 1755095 := bstep (se 1 (by rfl) ⟨1316321, by rfl⟩ : syracuseStep 1755095 = 2632643) B2632643
theorem B5924825 : Blo 1754578 5924825 := bstep (se 2 (by rfl) ⟨2221809, by rfl⟩ : syracuseStep 5924825 = 4443619) B4443619
theorem B1755115 : Blo 1754578 1755115 := bstep (se 1 (by rfl) ⟨1316336, by rfl⟩ : syracuseStep 1755115 = 2632673) B2632673
theorem B1755127 : Blo 1754578 1755127 := bstep (se 1 (by rfl) ⟨1316345, by rfl⟩ : syracuseStep 1755127 = 2632691) B2632691
theorem B1755147 : Blo 1754578 1755147 := bstep (se 1 (by rfl) ⟨1316360, by rfl⟩ : syracuseStep 1755147 = 2632721) B2632721
theorem B3950603 : Blo 1754578 3950603 := bstep (se 1 (by rfl) ⟨2962952, by rfl⟩ : syracuseStep 3950603 = 5925905) B5925905
theorem B1755159 : Blo 1754578 1755159 := bstep (se 1 (by rfl) ⟨1316369, by rfl⟩ : syracuseStep 1755159 = 2632739) B2632739
theorem B1755179 : Blo 1754578 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B6662195 : Blo 1754578 6662195 := bstep (se 1 (by rfl) ⟨4996646, by rfl⟩ : syracuseStep 6662195 = 9993293) B9993293
theorem B1755191 : Blo 1754578 1755191 := bstep (se 1 (by rfl) ⟨1316393, by rfl⟩ : syracuseStep 1755191 = 2632787) B2632787
theorem B6662209 : Blo 1754578 6662209 := bstep (se 2 (by rfl) ⟨2498328, by rfl⟩ : syracuseStep 6662209 = 4996657) B4996657
theorem B3950657 : Blo 1754578 3950657 := bstep (se 2 (by rfl) ⟨1481496, by rfl⟩ : syracuseStep 3950657 = 2962993) B2962993
theorem B85403717 : Blo 1754578 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B22489163 : Blo 1754578 22489163 := bstep (se 1 (by rfl) ⟨16866872, by rfl⟩ : syracuseStep 22489163 = 33733745) B33733745
theorem B1755211 : Blo 1754578 1755211 := bstep (se 1 (by rfl) ⟨1316408, by rfl⟩ : syracuseStep 1755211 = 2632817) B2632817
theorem B1755223 : Blo 1754578 1755223 := bstep (se 1 (by rfl) ⟨1316417, by rfl⟩ : syracuseStep 1755223 = 2632835) B2632835
theorem B1755243 : Blo 1754578 1755243 := bstep (se 1 (by rfl) ⟨1316432, by rfl⟩ : syracuseStep 1755243 = 2632865) B2632865
theorem B1755255 : Blo 1754578 1755255 := bstep (se 1 (by rfl) ⟨1316441, by rfl⟩ : syracuseStep 1755255 = 2632883) B2632883
theorem B13338755 : Blo 1754578 13338755 := bstep (se 1 (by rfl) ⟨10004066, by rfl⟩ : syracuseStep 13338755 = 20008133) B20008133
theorem B1755275 : Blo 1754578 1755275 := bstep (se 1 (by rfl) ⟨1316456, by rfl⟩ : syracuseStep 1755275 = 2632913) B2632913
theorem B7809169 : Blo 1754578 7809169 := bstep (se 2 (by rfl) ⟨2928438, by rfl⟩ : syracuseStep 7809169 = 5856877) B5856877
theorem B1755287 : Blo 1754578 1755287 := bstep (se 1 (by rfl) ⟨1316465, by rfl⟩ : syracuseStep 1755287 = 2632931) B2632931
theorem B2812055 : Blo 1754578 2812055 := bstep (se 1 (by rfl) ⟨2109041, by rfl⟩ : syracuseStep 2812055 = 4218083) B4218083
theorem B1755307 : Blo 1754578 1755307 := bstep (se 1 (by rfl) ⟨1316480, by rfl⟩ : syracuseStep 1755307 = 2632961) B2632961
theorem B1755319 : Blo 1754578 1755319 := bstep (se 1 (by rfl) ⟨1316489, by rfl⟩ : syracuseStep 1755319 = 2632979) B2632979
theorem B1755339 : Blo 1754578 1755339 := bstep (se 1 (by rfl) ⟨1316504, by rfl⟩ : syracuseStep 1755339 = 2633009) B2633009
theorem B1755351 : Blo 1754578 1755351 := bstep (se 1 (by rfl) ⟨1316513, by rfl⟩ : syracuseStep 1755351 = 2633027) B2633027
theorem B1755371 : Blo 1754578 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1755383 : Blo 1754578 1755383 := bstep (se 1 (by rfl) ⟨1316537, by rfl⟩ : syracuseStep 1755383 = 2633075) B2633075
theorem B2631947 : Blo 1754578 2631947 := bstep (se 1 (by rfl) ⟨1973960, by rfl⟩ : syracuseStep 2631947 = 3947921) B3947921
theorem B1755403 : Blo 1754578 1755403 := bstep (se 1 (by rfl) ⟨1316552, by rfl⟩ : syracuseStep 1755403 = 2633105) B2633105
theorem B2812171 : Blo 1754578 2812171 := bstep (se 1 (by rfl) ⟨2109128, by rfl⟩ : syracuseStep 2812171 = 4218257) B4218257
theorem B2631959 : Blo 1754578 2631959 := bstep (se 1 (by rfl) ⟨1973969, by rfl⟩ : syracuseStep 2631959 = 3947939) B3947939
theorem B1755415 : Blo 1754578 1755415 := bstep (se 1 (by rfl) ⟨1316561, by rfl⟩ : syracuseStep 1755415 = 2633123) B2633123
theorem B3950873 : Blo 1754578 3950873 := bstep (se 2 (by rfl) ⟨1481577, by rfl⟩ : syracuseStep 3950873 = 2963155) B2963155
theorem B1755435 : Blo 1754578 1755435 := bstep (se 1 (by rfl) ⟨1316576, by rfl⟩ : syracuseStep 1755435 = 2633153) B2633153
theorem B1755447 : Blo 1754578 1755447 := bstep (se 1 (by rfl) ⟨1316585, by rfl⟩ : syracuseStep 1755447 = 2633171) B2633171
theorem B1755467 : Blo 1754578 1755467 := bstep (se 1 (by rfl) ⟨1316600, by rfl⟩ : syracuseStep 1755467 = 2633201) B2633201
theorem B1755479 : Blo 1754578 1755479 := bstep (se 1 (by rfl) ⟨1316609, by rfl⟩ : syracuseStep 1755479 = 2633219) B2633219
theorem B2632025 : Blo 1754578 2632025 := bstep (se 2 (by rfl) ⟨987009, by rfl⟩ : syracuseStep 2632025 = 1974019) B1974019
theorem B1755499 : Blo 1754578 1755499 := bstep (se 1 (by rfl) ⟨1316624, by rfl⟩ : syracuseStep 1755499 = 2633249) B2633249
theorem B3950963 : Blo 1754578 3950963 := bstep (se 1 (by rfl) ⟨2963222, by rfl⟩ : syracuseStep 3950963 = 5926445) B5926445
theorem B67512689 : Blo 1754578 67512689 := bstep (se 2 (by rfl) ⟨25317258, by rfl⟩ : syracuseStep 67512689 = 50634517) B50634517
theorem B1755511 : Blo 1754578 1755511 := bstep (se 1 (by rfl) ⟨1316633, by rfl⟩ : syracuseStep 1755511 = 2633267) B2633267
theorem B7498115 : Blo 1754578 7498115 := bstep (se 1 (by rfl) ⟨5623586, by rfl⟩ : syracuseStep 7498115 = 11247173) B11247173
theorem B1755531 : Blo 1754578 1755531 := bstep (se 1 (by rfl) ⟨1316648, by rfl⟩ : syracuseStep 1755531 = 2633297) B2633297
theorem B1755543 : Blo 1754578 1755543 := bstep (se 1 (by rfl) ⟨1316657, by rfl⟩ : syracuseStep 1755543 = 2633315) B2633315
theorem B3950999 : Blo 1754578 3950999 := bstep (se 1 (by rfl) ⟨2963249, by rfl⟩ : syracuseStep 3950999 = 5926499) B5926499
theorem B1755563 : Blo 1754578 1755563 := bstep (se 1 (by rfl) ⟨1316672, by rfl⟩ : syracuseStep 1755563 = 2633345) B2633345
theorem B1755575 : Blo 1754578 1755575 := bstep (se 1 (by rfl) ⟨1316681, by rfl⟩ : syracuseStep 1755575 = 2633363) B2633363
theorem B2632139 : Blo 1754578 2632139 := bstep (se 1 (by rfl) ⟨1974104, by rfl⟩ : syracuseStep 2632139 = 3948209) B3948209
theorem B1755595 : Blo 1754578 1755595 := bstep (se 1 (by rfl) ⟨1316696, by rfl⟩ : syracuseStep 1755595 = 2633393) B2633393
theorem B2632151 : Blo 1754578 2632151 := bstep (se 1 (by rfl) ⟨1974113, by rfl⟩ : syracuseStep 2632151 = 3948227) B3948227
theorem B1755607 : Blo 1754578 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B1755627 : Blo 1754578 1755627 := bstep (se 1 (by rfl) ⟨1316720, by rfl⟩ : syracuseStep 1755627 = 2633441) B2633441
theorem B1755639 : Blo 1754578 1755639 := bstep (se 1 (by rfl) ⟨1316729, by rfl⟩ : syracuseStep 1755639 = 2633459) B2633459
theorem B1755659 : Blo 1754578 1755659 := bstep (se 1 (by rfl) ⟨1316744, by rfl⟩ : syracuseStep 1755659 = 2633489) B2633489
theorem B4442647 : Blo 1754578 4442647 := bstep (se 1 (by rfl) ⟨3331985, by rfl⟩ : syracuseStep 4442647 = 6663971) B6663971
theorem B1755671 : Blo 1754578 1755671 := bstep (se 1 (by rfl) ⟨1316753, by rfl⟩ : syracuseStep 1755671 = 2633507) B2633507
theorem B2632217 : Blo 1754578 2632217 := bstep (se 2 (by rfl) ⟨987081, by rfl⟩ : syracuseStep 2632217 = 1974163) B1974163
theorem B13330979 : Blo 1754578 13330979 := bstep (se 1 (by rfl) ⟨9998234, by rfl⟩ : syracuseStep 13330979 = 19996469) B19996469
theorem B1755691 : Blo 1754578 1755691 := bstep (se 1 (by rfl) ⟨1316768, by rfl⟩ : syracuseStep 1755691 = 2633537) B2633537
theorem B7121453 : Blo 1754578 7121453 := bstep (se 3 (by rfl) ⟨1335272, by rfl⟩ : syracuseStep 7121453 = 2670545) B2670545
theorem B1755703 : Blo 1754578 1755703 := bstep (se 1 (by rfl) ⟨1316777, by rfl⟩ : syracuseStep 1755703 = 2633555) B2633555
theorem B4999745 : Blo 1754578 4999745 := bstep (se 2 (by rfl) ⟨1874904, by rfl⟩ : syracuseStep 4999745 = 3749809) B3749809
theorem B1755723 : Blo 1754578 1755723 := bstep (se 1 (by rfl) ⟨1316792, by rfl⟩ : syracuseStep 1755723 = 2633585) B2633585
theorem B3951179 : Blo 1754578 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B1755735 : Blo 1754578 1755735 := bstep (se 1 (by rfl) ⟨1316801, by rfl⟩ : syracuseStep 1755735 = 2633603) B2633603
theorem B1755755 : Blo 1754578 1755755 := bstep (se 1 (by rfl) ⟨1316816, by rfl⟩ : syracuseStep 1755755 = 2633633) B2633633
theorem B1755767 : Blo 1754578 1755767 := bstep (se 1 (by rfl) ⟨1316825, by rfl⟩ : syracuseStep 1755767 = 2633651) B2633651
theorem B3951233 : Blo 1754578 3951233 := bstep (se 2 (by rfl) ⟨1481712, by rfl⟩ : syracuseStep 3951233 = 2963425) B2963425
theorem B2632331 : Blo 1754578 2632331 := bstep (se 1 (by rfl) ⟨1974248, by rfl⟩ : syracuseStep 2632331 = 3948497) B3948497
theorem B1755787 : Blo 1754578 1755787 := bstep (se 1 (by rfl) ⟨1316840, by rfl⟩ : syracuseStep 1755787 = 2633681) B2633681
theorem B2222731 : Blo 1754578 2222731 := bstep (se 1 (by rfl) ⟨1667048, by rfl⟩ : syracuseStep 2222731 = 3334097) B3334097
theorem B2632343 : Blo 1754578 2632343 := bstep (se 1 (by rfl) ⟨1974257, by rfl⟩ : syracuseStep 2632343 = 3948515) B3948515
theorem B5925527 : Blo 1754578 5925527 := bstep (se 1 (by rfl) ⟨4444145, by rfl⟩ : syracuseStep 5925527 = 8888291) B8888291
theorem B1755799 : Blo 1754578 1755799 := bstep (se 1 (by rfl) ⟨1316849, by rfl⟩ : syracuseStep 1755799 = 2633699) B2633699
theorem B3164825 : Blo 1754578 3164825 := bstep (se 2 (by rfl) ⟨1186809, by rfl⟩ : syracuseStep 3164825 = 2373619) B2373619
theorem B1755819 : Blo 1754578 1755819 := bstep (se 1 (by rfl) ⟨1316864, by rfl⟩ : syracuseStep 1755819 = 2633729) B2633729
theorem B1755831 : Blo 1754578 1755831 := bstep (se 1 (by rfl) ⟨1316873, by rfl⟩ : syracuseStep 1755831 = 2633747) B2633747
theorem B5065409 : Blo 1754578 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B1755851 : Blo 1754578 1755851 := bstep (se 1 (by rfl) ⟨1316888, by rfl⟩ : syracuseStep 1755851 = 2633777) B2633777
theorem B1755863 : Blo 1754578 1755863 := bstep (se 1 (by rfl) ⟨1316897, by rfl⟩ : syracuseStep 1755863 = 2633795) B2633795
theorem B2632409 : Blo 1754578 2632409 := bstep (se 2 (by rfl) ⟨987153, by rfl⟩ : syracuseStep 2632409 = 1974307) B1974307
theorem B1755883 : Blo 1754578 1755883 := bstep (se 1 (by rfl) ⟨1316912, by rfl⟩ : syracuseStep 1755883 = 2633825) B2633825
theorem B1755895 : Blo 1754578 1755895 := bstep (se 1 (by rfl) ⟨1316921, by rfl⟩ : syracuseStep 1755895 = 2633843) B2633843
theorem B1755915 : Blo 1754578 1755915 := bstep (se 1 (by rfl) ⟨1316936, by rfl⟩ : syracuseStep 1755915 = 2633873) B2633873
theorem B1755927 : Blo 1754578 1755927 := bstep (se 1 (by rfl) ⟨1316945, by rfl⟩ : syracuseStep 1755927 = 2633891) B2633891
theorem B1755947 : Blo 1754578 1755947 := bstep (se 1 (by rfl) ⟨1316960, by rfl⟩ : syracuseStep 1755947 = 2633921) B2633921
theorem B1755959 : Blo 1754578 1755959 := bstep (se 1 (by rfl) ⟨1316969, by rfl⟩ : syracuseStep 1755959 = 2633939) B2633939
theorem B2632523 : Blo 1754578 2632523 := bstep (se 1 (by rfl) ⟨1974392, by rfl⟩ : syracuseStep 2632523 = 3948785) B3948785
theorem B4746059 : Blo 1754578 4746059 := bstep (se 1 (by rfl) ⟨3559544, by rfl⟩ : syracuseStep 4746059 = 7119089) B7119089
theorem B1755979 : Blo 1754578 1755979 := bstep (se 1 (by rfl) ⟨1316984, by rfl⟩ : syracuseStep 1755979 = 2633969) B2633969
theorem B2632535 : Blo 1754578 2632535 := bstep (se 1 (by rfl) ⟨1974401, by rfl⟩ : syracuseStep 2632535 = 3948803) B3948803
theorem B1755991 : Blo 1754578 1755991 := bstep (se 1 (by rfl) ⟨1316993, by rfl⟩ : syracuseStep 1755991 = 2633987) B2633987
theorem B3951449 : Blo 1754578 3951449 := bstep (se 2 (by rfl) ⟨1481793, by rfl⟩ : syracuseStep 3951449 = 2963587) B2963587
theorem B1756011 : Blo 1754578 1756011 := bstep (se 1 (by rfl) ⟨1317008, by rfl⟩ : syracuseStep 1756011 = 2634017) B2634017
theorem B1756023 : Blo 1754578 1756023 := bstep (se 1 (by rfl) ⟨1317017, by rfl⟩ : syracuseStep 1756023 = 2634035) B2634035
theorem B1756043 : Blo 1754578 1756043 := bstep (se 1 (by rfl) ⟨1317032, by rfl⟩ : syracuseStep 1756043 = 2634065) B2634065
theorem B1756055 : Blo 1754578 1756055 := bstep (se 1 (by rfl) ⟨1317041, by rfl⟩ : syracuseStep 1756055 = 2634083) B2634083
theorem B2632601 : Blo 1754578 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B2706329 : Blo 1754578 2706329 := bstep (se 2 (by rfl) ⟨1014873, by rfl⟩ : syracuseStep 2706329 = 2029747) B2029747
theorem B1756075 : Blo 1754578 1756075 := bstep (se 1 (by rfl) ⟨1317056, by rfl⟩ : syracuseStep 1756075 = 2634113) B2634113
theorem B3951539 : Blo 1754578 3951539 := bstep (se 1 (by rfl) ⟨2963654, by rfl⟩ : syracuseStep 3951539 = 5927309) B5927309
theorem B1756087 : Blo 1754578 1756087 := bstep (se 1 (by rfl) ⟨1317065, by rfl⟩ : syracuseStep 1756087 = 2634131) B2634131
theorem B4443083 : Blo 1754578 4443083 := bstep (se 1 (by rfl) ⟨3332312, by rfl⟩ : syracuseStep 4443083 = 6664625) B6664625
theorem B1756107 : Blo 1754578 1756107 := bstep (se 1 (by rfl) ⟨1317080, by rfl⟩ : syracuseStep 1756107 = 2634161) B2634161
theorem B1756119 : Blo 1754578 1756119 := bstep (se 1 (by rfl) ⟨1317089, by rfl⟩ : syracuseStep 1756119 = 2634179) B2634179
theorem B3951575 : Blo 1754578 3951575 := bstep (se 1 (by rfl) ⟨2963681, by rfl⟩ : syracuseStep 3951575 = 5927363) B5927363
theorem B2812889 : Blo 1754578 2812889 := bstep (se 2 (by rfl) ⟨1054833, by rfl⟩ : syracuseStep 2812889 = 2109667) B2109667
theorem B1756139 : Blo 1754578 1756139 := bstep (se 1 (by rfl) ⟨1317104, by rfl⟩ : syracuseStep 1756139 = 2634209) B2634209
theorem B1756151 : Blo 1754578 1756151 := bstep (se 1 (by rfl) ⟨1317113, by rfl⟩ : syracuseStep 1756151 = 2634227) B2634227
theorem B2632715 : Blo 1754578 2632715 := bstep (se 1 (by rfl) ⟨1974536, by rfl⟩ : syracuseStep 2632715 = 3949073) B3949073
theorem B1756171 : Blo 1754578 1756171 := bstep (se 1 (by rfl) ⟨1317128, by rfl⟩ : syracuseStep 1756171 = 2634257) B2634257
theorem B2632727 : Blo 1754578 2632727 := bstep (se 1 (by rfl) ⟨1974545, by rfl⟩ : syracuseStep 2632727 = 3949091) B3949091
theorem B1756183 : Blo 1754578 1756183 := bstep (se 1 (by rfl) ⟨1317137, by rfl⟩ : syracuseStep 1756183 = 2634275) B2634275
theorem B1756203 : Blo 1754578 1756203 := bstep (se 1 (by rfl) ⟨1317152, by rfl⟩ : syracuseStep 1756203 = 2634305) B2634305
theorem B1756215 : Blo 1754578 1756215 := bstep (se 1 (by rfl) ⟨1317161, by rfl⟩ : syracuseStep 1756215 = 2634323) B2634323
theorem B1756235 : Blo 1754578 1756235 := bstep (se 1 (by rfl) ⟨1317176, by rfl⟩ : syracuseStep 1756235 = 2634353) B2634353
theorem B1756247 : Blo 1754578 1756247 := bstep (se 1 (by rfl) ⟨1317185, by rfl⟩ : syracuseStep 1756247 = 2634371) B2634371
theorem B2632793 : Blo 1754578 2632793 := bstep (se 2 (by rfl) ⟨987297, by rfl⟩ : syracuseStep 2632793 = 1974595) B1974595
theorem B1756267 : Blo 1754578 1756267 := bstep (se 1 (by rfl) ⟨1317200, by rfl⟩ : syracuseStep 1756267 = 2634401) B2634401
theorem B1756279 : Blo 1754578 1756279 := bstep (se 1 (by rfl) ⟨1317209, by rfl⟩ : syracuseStep 1756279 = 2634419) B2634419
theorem B1756299 : Blo 1754578 1756299 := bstep (se 1 (by rfl) ⟨1317224, by rfl⟩ : syracuseStep 1756299 = 2634449) B2634449
theorem B3951755 : Blo 1754578 3951755 := bstep (se 1 (by rfl) ⟨2963816, by rfl⟩ : syracuseStep 3951755 = 5927633) B5927633
theorem B1756311 : Blo 1754578 1756311 := bstep (se 1 (by rfl) ⟨1317233, by rfl⟩ : syracuseStep 1756311 = 2634467) B2634467
theorem B1756331 : Blo 1754578 1756331 := bstep (se 1 (by rfl) ⟨1317248, by rfl⟩ : syracuseStep 1756331 = 2634497) B2634497
theorem B5926067 : Blo 1754578 5926067 := bstep (se 1 (by rfl) ⟨4444550, by rfl⟩ : syracuseStep 5926067 = 8889101) B8889101
theorem B1756343 : Blo 1754578 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B3951809 : Blo 1754578 3951809 := bstep (se 2 (by rfl) ⟨1481928, by rfl⟩ : syracuseStep 3951809 = 2963857) B2963857
theorem B2632907 : Blo 1754578 2632907 := bstep (se 1 (by rfl) ⟨1974680, by rfl⟩ : syracuseStep 2632907 = 3949361) B3949361
theorem B1756363 : Blo 1754578 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B2632919 : Blo 1754578 2632919 := bstep (se 1 (by rfl) ⟨1974689, by rfl⟩ : syracuseStep 2632919 = 3949379) B3949379
theorem B1756375 : Blo 1754578 1756375 := bstep (se 1 (by rfl) ⟨1317281, by rfl⟩ : syracuseStep 1756375 = 2634563) B2634563
theorem B1756395 : Blo 1754578 1756395 := bstep (se 1 (by rfl) ⟨1317296, by rfl⟩ : syracuseStep 1756395 = 2634593) B2634593
theorem B1756407 : Blo 1754578 1756407 := bstep (se 1 (by rfl) ⟨1317305, by rfl⟩ : syracuseStep 1756407 = 2634611) B2634611
theorem B1756427 : Blo 1754578 1756427 := bstep (se 1 (by rfl) ⟨1317320, by rfl⟩ : syracuseStep 1756427 = 2634641) B2634641
theorem B1756439 : Blo 1754578 1756439 := bstep (se 1 (by rfl) ⟨1317329, by rfl⟩ : syracuseStep 1756439 = 2634659) B2634659
theorem B2632985 : Blo 1754578 2632985 := bstep (se 2 (by rfl) ⟨987369, by rfl⟩ : syracuseStep 2632985 = 1974739) B1974739
theorem B1756459 : Blo 1754578 1756459 := bstep (se 1 (by rfl) ⟨1317344, by rfl⟩ : syracuseStep 1756459 = 2634689) B2634689
theorem B8891693 : Blo 1754578 8891693 := bstep (se 3 (by rfl) ⟨1667192, by rfl⟩ : syracuseStep 8891693 = 3334385) B3334385
theorem B1756471 : Blo 1754578 1756471 := bstep (se 1 (by rfl) ⟨1317353, by rfl⟩ : syracuseStep 1756471 = 2634707) B2634707
theorem B4443457 : Blo 1754578 4443457 := bstep (se 2 (by rfl) ⟨1666296, by rfl⟩ : syracuseStep 4443457 = 3332593) B3332593
theorem B1756491 : Blo 1754578 1756491 := bstep (se 1 (by rfl) ⟨1317368, by rfl⟩ : syracuseStep 1756491 = 2634737) B2634737
theorem B1756503 : Blo 1754578 1756503 := bstep (se 1 (by rfl) ⟨1317377, by rfl⟩ : syracuseStep 1756503 = 2634755) B2634755
theorem B1756523 : Blo 1754578 1756523 := bstep (se 1 (by rfl) ⟨1317392, by rfl⟩ : syracuseStep 1756523 = 2634785) B2634785
theorem B1756535 : Blo 1754578 1756535 := bstep (se 1 (by rfl) ⟨1317401, by rfl⟩ : syracuseStep 1756535 = 2634803) B2634803
theorem B2633099 : Blo 1754578 2633099 := bstep (se 1 (by rfl) ⟨1974824, by rfl⟩ : syracuseStep 2633099 = 3949649) B3949649
theorem B1756555 : Blo 1754578 1756555 := bstep (se 1 (by rfl) ⟨1317416, by rfl⟩ : syracuseStep 1756555 = 2634833) B2634833
theorem B2633111 : Blo 1754578 2633111 := bstep (se 1 (by rfl) ⟨1974833, by rfl⟩ : syracuseStep 2633111 = 3949667) B3949667
theorem B1756567 : Blo 1754578 1756567 := bstep (se 1 (by rfl) ⟨1317425, by rfl⟩ : syracuseStep 1756567 = 2634851) B2634851
theorem B3952025 : Blo 1754578 3952025 := bstep (se 2 (by rfl) ⟨1482009, by rfl⟩ : syracuseStep 3952025 = 2964019) B2964019
theorem B5926337 : Blo 1754578 5926337 := bstep (se 2 (by rfl) ⟨2222376, by rfl⟩ : syracuseStep 5926337 = 4444753) B4444753
theorem B2633177 : Blo 1754578 2633177 := bstep (se 2 (by rfl) ⟨987441, by rfl⟩ : syracuseStep 2633177 = 1974883) B1974883
theorem B2813401 : Blo 1754578 2813401 := bstep (se 2 (by rfl) ⟨1055025, by rfl⟩ : syracuseStep 2813401 = 2110051) B2110051
theorem B3952115 : Blo 1754578 3952115 := bstep (se 1 (by rfl) ⟨2964086, by rfl⟩ : syracuseStep 3952115 = 5928173) B5928173
theorem B57699857 : Blo 1754578 57699857 := bstep (se 2 (by rfl) ⟨21637446, by rfl⟩ : syracuseStep 57699857 = 43274893) B43274893
theorem B3952151 : Blo 1754578 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B2960921 : Blo 1754578 2960921 := bstep (se 2 (by rfl) ⟨1110345, by rfl⟩ : syracuseStep 2960921 = 2220691) B2220691
theorem B28872227 : Blo 1754578 28872227 := bstep (se 1 (by rfl) ⟨21654170, by rfl⟩ : syracuseStep 28872227 = 43308341) B43308341
theorem B14077505 : Blo 1754578 14077505 := bstep (se 2 (by rfl) ⟨5279064, by rfl⟩ : syracuseStep 14077505 = 10558129) B10558129
theorem B2633291 : Blo 1754578 2633291 := bstep (se 1 (by rfl) ⟨1974968, by rfl⟩ : syracuseStep 2633291 = 3949937) B3949937
theorem B2633303 : Blo 1754578 2633303 := bstep (se 1 (by rfl) ⟨1974977, by rfl⟩ : syracuseStep 2633303 = 3949955) B3949955
theorem B16019045 : Blo 1754578 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B2961049 : Blo 1754578 2961049 := bstep (se 2 (by rfl) ⟨1110393, by rfl⟩ : syracuseStep 2961049 = 2220787) B2220787
theorem B2633369 : Blo 1754578 2633369 := bstep (se 2 (by rfl) ⟨987513, by rfl⟩ : syracuseStep 2633369 = 1975027) B1975027
theorem B2633483 : Blo 1754578 2633483 := bstep (se 1 (by rfl) ⟨1975112, by rfl⟩ : syracuseStep 2633483 = 3950225) B3950225
theorem B2633495 : Blo 1754578 2633495 := bstep (se 1 (by rfl) ⟨1975121, by rfl⟩ : syracuseStep 2633495 = 3950243) B3950243
theorem B2633561 : Blo 1754578 2633561 := bstep (se 2 (by rfl) ⟨987585, by rfl⟩ : syracuseStep 2633561 = 1975171) B1975171
theorem B4444055 : Blo 1754578 4444055 := bstep (se 1 (by rfl) ⟨3333041, by rfl⟩ : syracuseStep 4444055 = 6666083) B6666083
theorem B6664139 : Blo 1754578 6664139 := bstep (se 1 (by rfl) ⟨4998104, by rfl⟩ : syracuseStep 6664139 = 9996209) B9996209
theorem B2633675 : Blo 1754578 2633675 := bstep (se 1 (by rfl) ⟨1975256, by rfl⟩ : syracuseStep 2633675 = 3950513) B3950513
theorem B2633687 : Blo 1754578 2633687 := bstep (se 1 (by rfl) ⟨1975265, by rfl⟩ : syracuseStep 2633687 = 3950531) B3950531
theorem B6664153 : Blo 1754578 6664153 := bstep (se 2 (by rfl) ⟨2499057, by rfl⟩ : syracuseStep 6664153 = 4998115) B4998115
theorem B5926877 : Blo 1754578 5926877 := bstep (se 3 (by rfl) ⟨1111289, by rfl⟩ : syracuseStep 5926877 = 2222579) B2222579
theorem B8884241 : Blo 1754578 8884241 := bstep (se 2 (by rfl) ⟨3331590, by rfl⟩ : syracuseStep 8884241 = 6663181) B6663181
theorem B2633753 : Blo 1754578 2633753 := bstep (se 2 (by rfl) ⟨987657, by rfl⟩ : syracuseStep 2633753 = 1975315) B1975315
theorem B20000843 : Blo 1754578 20000843 := bstep (se 1 (by rfl) ⟨15000632, by rfl⟩ : syracuseStep 20000843 = 30001265) B30001265
theorem B2633867 : Blo 1754578 2633867 := bstep (se 1 (by rfl) ⟨1975400, by rfl⟩ : syracuseStep 2633867 = 3950801) B3950801
theorem B2633879 : Blo 1754578 2633879 := bstep (se 1 (by rfl) ⟨1975409, by rfl⟩ : syracuseStep 2633879 = 3950819) B3950819
theorem B8884403 : Blo 1754578 8884403 := bstep (se 1 (by rfl) ⟨6663302, by rfl⟩ : syracuseStep 8884403 = 13326605) B13326605
theorem B5001419 : Blo 1754578 5001419 := bstep (se 1 (by rfl) ⟨3751064, by rfl⟩ : syracuseStep 5001419 = 7502129) B7502129
theorem B14241997 : Blo 1754578 14241997 := bstep (se 3 (by rfl) ⟨2670374, by rfl⟩ : syracuseStep 14241997 = 5340749) B5340749
theorem B2961623 : Blo 1754578 2961623 := bstep (se 1 (by rfl) ⟨2221217, by rfl⟩ : syracuseStep 2961623 = 4442435) B4442435
theorem B2633945 : Blo 1754578 2633945 := bstep (se 2 (by rfl) ⟨987729, by rfl⟩ : syracuseStep 2633945 = 1975459) B1975459
theorem B4878557 : Blo 1754578 4878557 := bstep (se 3 (by rfl) ⟨914729, by rfl⟩ : syracuseStep 4878557 = 1829459) B1829459
theorem B4002059 : Blo 1754578 4002059 := bstep (se 1 (by rfl) ⟨3001544, by rfl⟩ : syracuseStep 4002059 = 6003089) B6003089
theorem B2634059 : Blo 1754578 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B2961751 : Blo 1754578 2961751 := bstep (se 1 (by rfl) ⟨2221313, by rfl⟩ : syracuseStep 2961751 = 4442627) B4442627
theorem B2634071 : Blo 1754578 2634071 := bstep (se 1 (by rfl) ⟨1975553, by rfl⟩ : syracuseStep 2634071 = 3951107) B3951107
theorem B3748211 : Blo 1754578 3748211 := bstep (se 1 (by rfl) ⟨2811158, by rfl⟩ : syracuseStep 3748211 = 5622317) B5622317
theorem B2634137 : Blo 1754578 2634137 := bstep (se 2 (by rfl) ⟨987801, by rfl⟩ : syracuseStep 2634137 = 1975603) B1975603
theorem B3748313 : Blo 1754578 3748313 := bstep (se 2 (by rfl) ⟨1405617, by rfl⟩ : syracuseStep 3748313 = 2811235) B2811235
theorem B2634251 : Blo 1754578 2634251 := bstep (se 1 (by rfl) ⟨1975688, by rfl⟩ : syracuseStep 2634251 = 3951377) B3951377
theorem B2634263 : Blo 1754578 2634263 := bstep (se 1 (by rfl) ⟨1975697, by rfl⟩ : syracuseStep 2634263 = 3951395) B3951395
theorem B2634329 : Blo 1754578 2634329 := bstep (se 2 (by rfl) ⟨987873, by rfl⟩ : syracuseStep 2634329 = 1975747) B1975747
theorem B10678877 : Blo 1754578 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B16863875 : Blo 1754578 16863875 := bstep (se 1 (by rfl) ⟨12647906, by rfl⟩ : syracuseStep 16863875 = 25295813) B25295813
theorem B7598771 : Blo 1754578 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B4444865 : Blo 1754578 4444865 := bstep (se 2 (by rfl) ⟨1666824, by rfl⟩ : syracuseStep 4444865 = 3333649) B3333649
theorem B2634443 : Blo 1754578 2634443 := bstep (se 1 (by rfl) ⟨1975832, by rfl⟩ : syracuseStep 2634443 = 3951665) B3951665
theorem B2634455 : Blo 1754578 2634455 := bstep (se 1 (by rfl) ⟨1975841, by rfl⟩ : syracuseStep 2634455 = 3951683) B3951683
theorem B5411549 : Blo 1754578 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B2634521 : Blo 1754578 2634521 := bstep (se 2 (by rfl) ⟨987945, by rfl⟩ : syracuseStep 2634521 = 1975891) B1975891
theorem B3748673 : Blo 1754578 3748673 := bstep (se 2 (by rfl) ⟨1405752, by rfl⟩ : syracuseStep 3748673 = 2811505) B2811505
theorem B2634635 : Blo 1754578 2634635 := bstep (se 1 (by rfl) ⟨1975976, by rfl⟩ : syracuseStep 2634635 = 3951953) B3951953
theorem B6665111 : Blo 1754578 6665111 := bstep (se 1 (by rfl) ⟨4998833, by rfl⟩ : syracuseStep 6665111 = 9997667) B9997667
theorem B2634647 : Blo 1754578 2634647 := bstep (se 1 (by rfl) ⟨1975985, by rfl⟩ : syracuseStep 2634647 = 3951971) B3951971
theorem B2962379 : Blo 1754578 2962379 := bstep (se 1 (by rfl) ⟨2221784, by rfl⟩ : syracuseStep 2962379 = 4443569) B4443569
theorem B2634713 : Blo 1754578 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B8434705 : Blo 1754578 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B16020497 : Blo 1754578 16020497 := bstep (se 2 (by rfl) ⟨6007686, by rfl⟩ : syracuseStep 16020497 = 12015373) B12015373
theorem B2962507 : Blo 1754578 2962507 := bstep (se 1 (by rfl) ⟨2221880, by rfl⟩ : syracuseStep 2962507 = 4443761) B4443761
theorem B5928011 : Blo 1754578 5928011 := bstep (se 1 (by rfl) ⟨4446008, by rfl⟩ : syracuseStep 5928011 = 8892017) B8892017
theorem B2634827 : Blo 1754578 2634827 := bstep (se 1 (by rfl) ⟨1976120, by rfl⟩ : syracuseStep 2634827 = 3952241) B3952241
theorem B2634839 : Blo 1754578 2634839 := bstep (se 1 (by rfl) ⟨1976129, by rfl⟩ : syracuseStep 2634839 = 3952259) B3952259
theorem B8434781 : Blo 1754578 8434781 := bstep (se 3 (by rfl) ⟨1581521, by rfl⟩ : syracuseStep 8434781 = 3163043) B3163043
theorem B2962649 : Blo 1754578 2962649 := bstep (se 2 (by rfl) ⟨1110993, by rfl⟩ : syracuseStep 2962649 = 2221987) B2221987
theorem B4445401 : Blo 1754578 4445401 := bstep (se 2 (by rfl) ⟨1667025, by rfl⟩ : syracuseStep 4445401 = 3334051) B3334051
theorem B13325633 : Blo 1754578 13325633 := bstep (se 2 (by rfl) ⟨4997112, by rfl⟩ : syracuseStep 13325633 = 9994225) B9994225
theorem B2962777 : Blo 1754578 2962777 := bstep (se 2 (by rfl) ⟨1111041, by rfl⟩ : syracuseStep 2962777 = 2222083) B2222083
theorem B5928281 : Blo 1754578 5928281 := bstep (se 2 (by rfl) ⟨2223105, by rfl⟩ : syracuseStep 5928281 = 4446211) B4446211
theorem B9491813 : Blo 1754578 9491813 := bstep (se 4 (by rfl) ⟨889857, by rfl⟩ : syracuseStep 9491813 = 1779715) B1779715
theorem B3749399 : Blo 1754578 3749399 := bstep (se 1 (by rfl) ⟨2812049, by rfl⟩ : syracuseStep 3749399 = 5624099) B5624099
theorem B2373143 : Blo 1754578 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B24024611 : Blo 1754578 24024611 := bstep (se 1 (by rfl) ⟨18018458, by rfl⟩ : syracuseStep 24024611 = 36036917) B36036917
theorem B15005249 : Blo 1754578 15005249 := bstep (se 2 (by rfl) ⟨5626968, by rfl⟩ : syracuseStep 15005249 = 11253937) B11253937
theorem B1873687 : Blo 1754578 1873687 := bstep (se 1 (by rfl) ⟨1405265, by rfl⟩ : syracuseStep 1873687 = 2810531) B2810531
theorem B7116589 : Blo 1754578 7116589 := bstep (se 3 (by rfl) ⟨1334360, by rfl⟩ : syracuseStep 7116589 = 2668721) B2668721
theorem B3331955 : Blo 1754578 3331955 := bstep (se 1 (by rfl) ⟨2498966, by rfl⟩ : syracuseStep 3331955 = 4997933) B4997933
theorem B2963351 : Blo 1754578 2963351 := bstep (se 1 (by rfl) ⟨2222513, by rfl⟩ : syracuseStep 2963351 = 4445027) B4445027
theorem B32045017 : Blo 1754578 32045017 := bstep (se 2 (by rfl) ⟨12016881, by rfl⟩ : syracuseStep 32045017 = 24033763) B24033763
theorem B3332107 : Blo 1754578 3332107 := bstep (se 1 (by rfl) ⟨2499080, by rfl⟩ : syracuseStep 3332107 = 4998161) B4998161
theorem B2963479 : Blo 1754578 2963479 := bstep (se 1 (by rfl) ⟨2222609, by rfl⟩ : syracuseStep 2963479 = 4445219) B4445219
theorem B6330413 : Blo 1754578 6330413 := bstep (se 3 (by rfl) ⟨1186952, by rfl⟩ : syracuseStep 6330413 = 2373905) B2373905
theorem B7501889 : Blo 1754578 7501889 := bstep (se 2 (by rfl) ⟨2813208, by rfl⟩ : syracuseStep 7501889 = 5626417) B5626417
theorem B8886347 : Blo 1754578 8886347 := bstep (se 1 (by rfl) ⟨6664760, by rfl⟩ : syracuseStep 8886347 = 13329521) B13329521
theorem B6666371 : Blo 1754578 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B5626007 : Blo 1754578 5626007 := bstep (se 1 (by rfl) ⟨4219505, by rfl⟩ : syracuseStep 5626007 = 8439011) B8439011
theorem B2373835 : Blo 1754578 2373835 := bstep (se 1 (by rfl) ⟨1780376, by rfl⟩ : syracuseStep 2373835 = 3560753) B3560753
theorem B6412547 : Blo 1754578 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B3332441 : Blo 1754578 3332441 := bstep (se 2 (by rfl) ⟨1249665, by rfl⟩ : syracuseStep 3332441 = 2499331) B2499331
theorem B3750295 : Blo 1754578 3750295 := bstep (se 1 (by rfl) ⟨2812721, by rfl⟩ : syracuseStep 3750295 = 5625443) B5625443
theorem B24033809 : Blo 1754578 24033809 := bstep (se 2 (by rfl) ⟨9012678, by rfl⟩ : syracuseStep 24033809 = 18025357) B18025357
theorem B1874507 : Blo 1754578 1874507 := bstep (se 1 (by rfl) ⟨1405880, by rfl⟩ : syracuseStep 1874507 = 2811761) B2811761
theorem B2964107 : Blo 1754578 2964107 := bstep (se 1 (by rfl) ⟨2223080, by rfl⟩ : syracuseStep 2964107 = 4446161) B4446161
theorem B11254423 : Blo 1754578 11254423 := bstep (se 1 (by rfl) ⟨8440817, by rfl⟩ : syracuseStep 11254423 = 16881635) B16881635
theorem B12008209 : Blo 1754578 12008209 := bstep (se 2 (by rfl) ⟨4503078, by rfl⟩ : syracuseStep 12008209 = 9006157) B9006157
theorem B4004633 : Blo 1754578 4004633 := bstep (se 2 (by rfl) ⟨1501737, by rfl⟩ : syracuseStep 4004633 = 3003475) B3003475
theorem B3333079 : Blo 1754578 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B7117789 : Blo 1754578 7117789 := bstep (se 3 (by rfl) ⟨1334585, by rfl⟩ : syracuseStep 7117789 = 2669171) B2669171
theorem B7502813 : Blo 1754578 7502813 := bstep (se 3 (by rfl) ⟨1406777, by rfl⟩ : syracuseStep 7502813 = 2813555) B2813555
theorem B3751115 : Blo 1754578 3751115 := bstep (se 1 (by rfl) ⟨2813336, by rfl⟩ : syracuseStep 3751115 = 5626673) B5626673
theorem B5627083 : Blo 1754578 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B13327577 : Blo 1754578 13327577 := bstep (se 2 (by rfl) ⟨4997841, by rfl⟩ : syracuseStep 13327577 = 9995683) B9995683
theorem B9485585 : Blo 1754578 9485585 := bstep (se 2 (by rfl) ⟨3557094, by rfl⟩ : syracuseStep 9485585 = 7114189) B7114189
theorem B5922071 : Blo 1754578 5922071 := bstep (se 1 (by rfl) ⟨4441553, by rfl⟩ : syracuseStep 5922071 = 8883107) B8883107
theorem B9485669 : Blo 1754578 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B4005335 : Blo 1754578 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B3947993 : Blo 1754578 3947993 := bstep (se 2 (by rfl) ⟨1480497, by rfl⟩ : syracuseStep 3947993 = 2960995) B2960995
theorem B3948083 : Blo 1754578 3948083 := bstep (se 1 (by rfl) ⟨2961062, by rfl⟩ : syracuseStep 3948083 = 5922125) B5922125
theorem B3948119 : Blo 1754578 3948119 := bstep (se 1 (by rfl) ⟨2961089, by rfl⟩ : syracuseStep 3948119 = 5922179) B5922179
theorem B4742749 : Blo 1754578 4742749 := bstep (se 3 (by rfl) ⟨889265, by rfl⟩ : syracuseStep 4742749 = 1778531) B1778531
theorem B1875575 : Blo 1754578 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B9494147 : Blo 1754578 9494147 := bstep (se 1 (by rfl) ⟨7120610, by rfl⟩ : syracuseStep 9494147 = 14241221) B14241221
theorem B1973911 : Blo 1754578 1973911 := bstep (se 1 (by rfl) ⟨1480433, by rfl⟩ : syracuseStep 1973911 = 2960867) B2960867
theorem B28458701 : Blo 1754578 28458701 := bstep (se 3 (by rfl) ⟨5336006, by rfl⟩ : syracuseStep 28458701 = 10672013) B10672013
theorem B36052685 : Blo 1754578 36052685 := bstep (se 3 (by rfl) ⟨6759878, by rfl⟩ : syracuseStep 36052685 = 13519757) B13519757
theorem B14991065 : Blo 1754578 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B4996829 : Blo 1754578 4996829 := bstep (se 3 (by rfl) ⟨936905, by rfl⟩ : syracuseStep 4996829 = 1873811) B1873811
theorem B13336325 : Blo 1754578 13336325 := bstep (se 4 (by rfl) ⟨1250280, by rfl⟩ : syracuseStep 13336325 = 2500561) B2500561
theorem B3948299 : Blo 1754578 3948299 := bstep (se 1 (by rfl) ⟨2961224, by rfl⟩ : syracuseStep 3948299 = 5922449) B5922449
theorem B3333899 : Blo 1754578 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B8437549 : Blo 1754578 8437549 := bstep (se 3 (by rfl) ⟨1582040, by rfl⟩ : syracuseStep 8437549 = 3164081) B3164081
theorem B5922611 : Blo 1754578 5922611 := bstep (se 1 (by rfl) ⟨4441958, by rfl⟩ : syracuseStep 5922611 = 8883917) B8883917
theorem B3948353 : Blo 1754578 3948353 := bstep (se 2 (by rfl) ⟨1480632, by rfl⟩ : syracuseStep 3948353 = 2961265) B2961265
theorem B8888129 : Blo 1754578 8888129 := bstep (se 2 (by rfl) ⟨3333048, by rfl⟩ : syracuseStep 8888129 = 6666097) B6666097
theorem B4218689 : Blo 1754578 4218689 := bstep (se 2 (by rfl) ⟨1582008, by rfl⟩ : syracuseStep 4218689 = 3164017) B3164017
theorem B3333953 : Blo 1754578 3333953 := bstep (se 2 (by rfl) ⟨1250232, by rfl⟩ : syracuseStep 3333953 = 2500465) B2500465
theorem B1974091 : Blo 1754578 1974091 := bstep (se 1 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 1974091 = 2961137) B2961137
theorem B8453963 : Blo 1754578 8453963 := bstep (se 1 (by rfl) ⟨6340472, by rfl⟩ : syracuseStep 8453963 = 12680945) B12680945
theorem B7495517 : Blo 1754578 7495517 := bstep (se 3 (by rfl) ⟨1405409, by rfl⟩ : syracuseStep 7495517 = 2810819) B2810819
theorem B1974199 : Blo 1754578 1974199 := bstep (se 1 (by rfl) ⟨1480649, by rfl⟩ : syracuseStep 1974199 = 2961299) B2961299
theorem B5922827 : Blo 1754578 5922827 := bstep (se 1 (by rfl) ⟨4442120, by rfl⟩ : syracuseStep 5922827 = 8884241) B8884241
theorem B3948587 : Blo 1754578 3948587 := bstep (se 1 (by rfl) ⟨2961440, by rfl⟩ : syracuseStep 3948587 = 5922881) B5922881
theorem B5922935 : Blo 1754578 5922935 := bstep (se 1 (by rfl) ⟨4442201, by rfl⟩ : syracuseStep 5922935 = 8884403) B8884403
theorem B3334279 : Blo 1754578 3334279 := bstep (se 1 (by rfl) ⟨2500709, by rfl⟩ : syracuseStep 3334279 = 5001419) B5001419
theorem B1974415 : Blo 1754578 1974415 := bstep (se 1 (by rfl) ⟨1480811, by rfl⟩ : syracuseStep 1974415 = 2961623) B2961623
theorem B3252371 : Blo 1754578 3252371 := bstep (se 1 (by rfl) ⟨2439278, by rfl⟩ : syracuseStep 3252371 = 4878557) B4878557
theorem B10412225 : Blo 1754578 10412225 := bstep (se 2 (by rfl) ⟨3904584, by rfl⟩ : syracuseStep 10412225 = 7809169) B7809169
theorem B2498807 : Blo 1754578 2498807 := bstep (se 1 (by rfl) ⟨1874105, by rfl⟩ : syracuseStep 2498807 = 3748211) B3748211
theorem B18989329 : Blo 1754578 18989329 := bstep (se 2 (by rfl) ⟨7120998, by rfl⟩ : syracuseStep 18989329 = 14241997) B14241997
theorem B4743485 : Blo 1754578 4743485 := bstep (se 3 (by rfl) ⟨889403, by rfl⟩ : syracuseStep 4743485 = 1778807) B1778807
theorem B3948947 : Blo 1754578 3948947 := bstep (se 1 (by rfl) ⟨2961710, by rfl⟩ : syracuseStep 3948947 = 5923421) B5923421
theorem B7119251 : Blo 1754578 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B3949001 : Blo 1754578 3949001 := bstep (se 2 (by rfl) ⟨1480875, by rfl⟩ : syracuseStep 3949001 = 2961751) B2961751
theorem B16875985 : Blo 1754578 16875985 := bstep (se 2 (by rfl) ⟨6328494, by rfl⟩ : syracuseStep 16875985 = 12656989) B12656989
theorem B10002973 : Blo 1754578 10002973 := bstep (se 3 (by rfl) ⟨1875557, by rfl⟩ : syracuseStep 10002973 = 3751115) B3751115
theorem B2222635 : Blo 1754578 2222635 := bstep (se 1 (by rfl) ⟨1666976, by rfl⟩ : syracuseStep 2222635 = 3333953) B3333953
theorem B2499115 : Blo 1754578 2499115 := bstep (se 1 (by rfl) ⟨1874336, by rfl⟩ : syracuseStep 2499115 = 3748673) B3748673
theorem B1974919 : Blo 1754578 1974919 := bstep (se 1 (by rfl) ⟨1481189, by rfl⟩ : syracuseStep 1974919 = 2962379) B2962379
theorem B5923529 : Blo 1754578 5923529 := bstep (se 2 (by rfl) ⟨2221323, by rfl⟩ : syracuseStep 5923529 = 4442647) B4442647
theorem B1975099 : Blo 1754578 1975099 := bstep (se 1 (by rfl) ⟨1481324, by rfl⟩ : syracuseStep 1975099 = 2962649) B2962649
theorem B2499599 : Blo 1754578 2499599 := bstep (se 1 (by rfl) ⟨1874699, by rfl⟩ : syracuseStep 2499599 = 3749399) B3749399
theorem B10003499 : Blo 1754578 10003499 := bstep (se 1 (by rfl) ⟨7502624, by rfl⟩ : syracuseStep 10003499 = 15005249) B15005249
theorem B3949703 : Blo 1754578 3949703 := bstep (se 1 (by rfl) ⟨2962277, by rfl⟩ : syracuseStep 3949703 = 5924555) B5924555
theorem B9995501 : Blo 1754578 9995501 := bstep (se 3 (by rfl) ⟨1874156, by rfl⟩ : syracuseStep 9995501 = 3748313) B3748313
theorem B1975567 : Blo 1754578 1975567 := bstep (se 1 (by rfl) ⟨1481675, by rfl⟩ : syracuseStep 1975567 = 2963351) B2963351
theorem B3949883 : Blo 1754578 3949883 := bstep (se 1 (by rfl) ⟨2962412, by rfl⟩ : syracuseStep 3949883 = 5924825) B5924825
theorem B4220275 : Blo 1754578 4220275 := bstep (se 1 (by rfl) ⟨3165206, by rfl⟩ : syracuseStep 4220275 = 6330413) B6330413
theorem B4441463 : Blo 1754578 4441463 := bstep (se 1 (by rfl) ⟨3331097, by rfl⟩ : syracuseStep 4441463 = 6662195) B6662195
theorem B56935811 : Blo 1754578 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B14992775 : Blo 1754578 14992775 := bstep (se 1 (by rfl) ⟨11244581, by rfl⟩ : syracuseStep 14992775 = 22489163) B22489163
theorem B5924231 : Blo 1754578 5924231 := bstep (se 1 (by rfl) ⟨4443173, by rfl⟩ : syracuseStep 5924231 = 8886347) B8886347
theorem B3950009 : Blo 1754578 3950009 := bstep (se 2 (by rfl) ⟨1481253, by rfl⟩ : syracuseStep 3950009 = 2962507) B2962507
theorem B18990541 : Blo 1754578 18990541 := bstep (se 3 (by rfl) ⟨3560726, by rfl⟩ : syracuseStep 18990541 = 7121453) B7121453
theorem B1754631 : Blo 1754578 1754631 := bstep (se 1 (by rfl) ⟨1315973, by rfl⟩ : syracuseStep 1754631 = 2631947) B2631947
theorem B1754639 : Blo 1754578 1754639 := bstep (se 1 (by rfl) ⟨1315979, by rfl⟩ : syracuseStep 1754639 = 2631959) B2631959
theorem B4998685 : Blo 1754578 4998685 := bstep (se 3 (by rfl) ⟨937253, by rfl⟩ : syracuseStep 4998685 = 1874507) B1874507
theorem B1754683 : Blo 1754578 1754683 := bstep (se 1 (by rfl) ⟨1316012, by rfl⟩ : syracuseStep 1754683 = 2632025) B2632025
theorem B45008459 : Blo 1754578 45008459 := bstep (se 1 (by rfl) ⟨33756344, by rfl⟩ : syracuseStep 45008459 = 67512689) B67512689
theorem B4998743 : Blo 1754578 4998743 := bstep (se 1 (by rfl) ⟨3749057, by rfl⟩ : syracuseStep 4998743 = 7498115) B7498115
theorem B1754759 : Blo 1754578 1754759 := bstep (se 1 (by rfl) ⟨1316069, by rfl⟩ : syracuseStep 1754759 = 2632139) B2632139
theorem B1754767 : Blo 1754578 1754767 := bstep (se 1 (by rfl) ⟨1316075, by rfl⟩ : syracuseStep 1754767 = 2632151) B2632151
theorem B1754811 : Blo 1754578 1754811 := bstep (se 1 (by rfl) ⟨1316108, by rfl⟩ : syracuseStep 1754811 = 2632217) B2632217
theorem B5924609 : Blo 1754578 5924609 := bstep (se 2 (by rfl) ⟨2221728, by rfl⟩ : syracuseStep 5924609 = 4443457) B4443457
theorem B1754887 : Blo 1754578 1754887 := bstep (se 1 (by rfl) ⟨1316165, by rfl⟩ : syracuseStep 1754887 = 2632331) B2632331
theorem B1976071 : Blo 1754578 1976071 := bstep (se 1 (by rfl) ⟨1482053, by rfl⟩ : syracuseStep 1976071 = 2964107) B2964107
theorem B1754895 : Blo 1754578 1754895 := bstep (se 1 (by rfl) ⟨1316171, by rfl⟩ : syracuseStep 1754895 = 2632343) B2632343
theorem B3950351 : Blo 1754578 3950351 := bstep (se 1 (by rfl) ⟨2962763, by rfl⟩ : syracuseStep 3950351 = 5925527) B5925527
theorem B3950369 : Blo 1754578 3950369 := bstep (se 2 (by rfl) ⟨1481388, by rfl⟩ : syracuseStep 3950369 = 2962777) B2962777
theorem B3376939 : Blo 1754578 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B1754939 : Blo 1754578 1754939 := bstep (se 1 (by rfl) ⟨1316204, by rfl⟩ : syracuseStep 1754939 = 2632409) B2632409
theorem B1755015 : Blo 1754578 1755015 := bstep (se 1 (by rfl) ⟨1316261, by rfl⟩ : syracuseStep 1755015 = 2632523) B2632523
theorem B3164039 : Blo 1754578 3164039 := bstep (se 1 (by rfl) ⟨2373029, by rfl⟩ : syracuseStep 3164039 = 4746059) B4746059
theorem B1755023 : Blo 1754578 1755023 := bstep (se 1 (by rfl) ⟨1316267, by rfl⟩ : syracuseStep 1755023 = 2632535) B2632535
theorem B1755067 : Blo 1754578 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B1804219 : Blo 1754578 1804219 := bstep (se 1 (by rfl) ⟨1353164, by rfl⟩ : syracuseStep 1804219 = 2706329) B2706329
theorem B1755143 : Blo 1754578 1755143 := bstep (se 1 (by rfl) ⟨1316357, by rfl⟩ : syracuseStep 1755143 = 2632715) B2632715
theorem B1755151 : Blo 1754578 1755151 := bstep (se 1 (by rfl) ⟨1316363, by rfl⟩ : syracuseStep 1755151 = 2632727) B2632727
theorem B8890397 : Blo 1754578 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B1755195 : Blo 1754578 1755195 := bstep (se 1 (by rfl) ⟨1316396, by rfl⟩ : syracuseStep 1755195 = 2632793) B2632793
theorem B13330493 : Blo 1754578 13330493 := bstep (se 3 (by rfl) ⟨2499467, by rfl⟩ : syracuseStep 13330493 = 4998935) B4998935
theorem B3950711 : Blo 1754578 3950711 := bstep (se 1 (by rfl) ⟨2963033, by rfl⟩ : syracuseStep 3950711 = 5926067) B5926067
theorem B1755271 : Blo 1754578 1755271 := bstep (se 1 (by rfl) ⟨1316453, by rfl⟩ : syracuseStep 1755271 = 2632907) B2632907
theorem B1755279 : Blo 1754578 1755279 := bstep (se 1 (by rfl) ⟨1316459, by rfl⟩ : syracuseStep 1755279 = 2632919) B2632919
theorem B11249837 : Blo 1754578 11249837 := bstep (se 3 (by rfl) ⟨2109344, by rfl⟩ : syracuseStep 11249837 = 4218689) B4218689
theorem B1755323 : Blo 1754578 1755323 := bstep (se 1 (by rfl) ⟨1316492, by rfl⟩ : syracuseStep 1755323 = 2632985) B2632985
theorem B2631881 : Blo 1754578 2631881 := bstep (se 2 (by rfl) ⟨986955, by rfl⟩ : syracuseStep 2631881 = 1973911) B1973911
theorem B1755399 : Blo 1754578 1755399 := bstep (se 1 (by rfl) ⟨1316549, by rfl⟩ : syracuseStep 1755399 = 2633099) B2633099
theorem B1755407 : Blo 1754578 1755407 := bstep (se 1 (by rfl) ⟨1316555, by rfl⟩ : syracuseStep 1755407 = 2633111) B2633111
theorem B3950891 : Blo 1754578 3950891 := bstep (se 1 (by rfl) ⟨2963168, by rfl⟩ : syracuseStep 3950891 = 5926337) B5926337
theorem B2631995 : Blo 1754578 2631995 := bstep (se 1 (by rfl) ⟨1973996, by rfl⟩ : syracuseStep 2631995 = 3947993) B3947993
theorem B1755451 : Blo 1754578 1755451 := bstep (se 1 (by rfl) ⟨1316588, by rfl⟩ : syracuseStep 1755451 = 2633177) B2633177
theorem B2632055 : Blo 1754578 2632055 := bstep (se 1 (by rfl) ⟨1974041, by rfl⟩ : syracuseStep 2632055 = 3948083) B3948083
theorem B1755527 : Blo 1754578 1755527 := bstep (se 1 (by rfl) ⟨1316645, by rfl⟩ : syracuseStep 1755527 = 2633291) B2633291
theorem B2632079 : Blo 1754578 2632079 := bstep (se 1 (by rfl) ⟨1974059, by rfl⟩ : syracuseStep 2632079 = 3948119) B3948119
theorem B1755535 : Blo 1754578 1755535 := bstep (se 1 (by rfl) ⟨1316651, by rfl⟩ : syracuseStep 1755535 = 2633303) B2633303
theorem B9488785 : Blo 1754578 9488785 := bstep (se 2 (by rfl) ⟨3558294, by rfl⟩ : syracuseStep 9488785 = 7116589) B7116589
theorem B11250065 : Blo 1754578 11250065 := bstep (se 2 (by rfl) ⟨4218774, by rfl⟩ : syracuseStep 11250065 = 8437549) B8437549
theorem B2632121 : Blo 1754578 2632121 := bstep (se 2 (by rfl) ⟨987045, by rfl⟩ : syracuseStep 2632121 = 1974091) B1974091
theorem B1755579 : Blo 1754578 1755579 := bstep (se 1 (by rfl) ⟨1316684, by rfl⟩ : syracuseStep 1755579 = 2633369) B2633369
theorem B8890883 : Blo 1754578 8890883 := bstep (se 1 (by rfl) ⟨6668162, by rfl⟩ : syracuseStep 8890883 = 13336325) B13336325
theorem B2632199 : Blo 1754578 2632199 := bstep (se 1 (by rfl) ⟨1974149, by rfl⟩ : syracuseStep 2632199 = 3948299) B3948299
theorem B1755655 : Blo 1754578 1755655 := bstep (se 1 (by rfl) ⟨1316741, by rfl⟩ : syracuseStep 1755655 = 2633483) B2633483
theorem B1755663 : Blo 1754578 1755663 := bstep (se 1 (by rfl) ⟨1316747, by rfl⟩ : syracuseStep 1755663 = 2633495) B2633495
theorem B2632235 : Blo 1754578 2632235 := bstep (se 1 (by rfl) ⟨1974176, by rfl⟩ : syracuseStep 2632235 = 3948353) B3948353
theorem B5925419 : Blo 1754578 5925419 := bstep (se 1 (by rfl) ⟨4444064, by rfl⟩ : syracuseStep 5925419 = 8888129) B8888129
theorem B1755707 : Blo 1754578 1755707 := bstep (se 1 (by rfl) ⟨1316780, by rfl⟩ : syracuseStep 1755707 = 2633561) B2633561
theorem B2632265 : Blo 1754578 2632265 := bstep (se 2 (by rfl) ⟨987099, by rfl⟩ : syracuseStep 2632265 = 1974199) B1974199
theorem B4442759 : Blo 1754578 4442759 := bstep (se 1 (by rfl) ⟨3332069, by rfl⟩ : syracuseStep 4442759 = 6664139) B6664139
theorem B1755783 : Blo 1754578 1755783 := bstep (se 1 (by rfl) ⟨1316837, by rfl⟩ : syracuseStep 1755783 = 2633675) B2633675
theorem B1755791 : Blo 1754578 1755791 := bstep (se 1 (by rfl) ⟨1316843, by rfl⟩ : syracuseStep 1755791 = 2633687) B2633687
theorem B3951251 : Blo 1754578 3951251 := bstep (se 1 (by rfl) ⟨2963438, by rfl⟩ : syracuseStep 3951251 = 5926877) B5926877
theorem B4442809 : Blo 1754578 4442809 := bstep (se 2 (by rfl) ⟨1666053, by rfl⟩ : syracuseStep 4442809 = 3332107) B3332107
theorem B2632379 : Blo 1754578 2632379 := bstep (se 1 (by rfl) ⟨1974284, by rfl⟩ : syracuseStep 2632379 = 3948569) B3948569
theorem B1755835 : Blo 1754578 1755835 := bstep (se 1 (by rfl) ⟨1316876, by rfl⟩ : syracuseStep 1755835 = 2633753) B2633753
theorem B3951305 : Blo 1754578 3951305 := bstep (se 2 (by rfl) ⟨1481739, by rfl⟩ : syracuseStep 3951305 = 2963479) B2963479
theorem B2632439 : Blo 1754578 2632439 := bstep (se 1 (by rfl) ⟨1974329, by rfl⟩ : syracuseStep 2632439 = 3948659) B3948659
theorem B8882945 : Blo 1754578 8882945 := bstep (se 2 (by rfl) ⟨3331104, by rfl⟩ : syracuseStep 8882945 = 6662209) B6662209
theorem B1755911 : Blo 1754578 1755911 := bstep (se 1 (by rfl) ⟨1316933, by rfl⟩ : syracuseStep 1755911 = 2633867) B2633867
theorem B2632463 : Blo 1754578 2632463 := bstep (se 1 (by rfl) ⟨1974347, by rfl⟩ : syracuseStep 2632463 = 3948695) B3948695
theorem B1755919 : Blo 1754578 1755919 := bstep (se 1 (by rfl) ⟨1316939, by rfl⟩ : syracuseStep 1755919 = 2633879) B2633879
theorem B2632505 : Blo 1754578 2632505 := bstep (se 2 (by rfl) ⟨987189, by rfl⟩ : syracuseStep 2632505 = 1974379) B1974379
theorem B1755963 : Blo 1754578 1755963 := bstep (se 1 (by rfl) ⟨1316972, by rfl⟩ : syracuseStep 1755963 = 2633945) B2633945
theorem B2632583 : Blo 1754578 2632583 := bstep (se 1 (by rfl) ⟨1974437, by rfl⟩ : syracuseStep 2632583 = 3948875) B3948875
theorem B1756039 : Blo 1754578 1756039 := bstep (se 1 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 1756039 = 2634059) B2634059
theorem B1756047 : Blo 1754578 1756047 := bstep (se 1 (by rfl) ⟨1317035, by rfl⟩ : syracuseStep 1756047 = 2634071) B2634071
theorem B2632619 : Blo 1754578 2632619 := bstep (se 1 (by rfl) ⟨1974464, by rfl⟩ : syracuseStep 2632619 = 3948929) B3948929
theorem B3165113 : Blo 1754578 3165113 := bstep (se 2 (by rfl) ⟨1186917, by rfl⟩ : syracuseStep 3165113 = 2373835) B2373835
theorem B1756091 : Blo 1754578 1756091 := bstep (se 1 (by rfl) ⟨1317068, by rfl⟩ : syracuseStep 1756091 = 2634137) B2634137
theorem B2632649 : Blo 1754578 2632649 := bstep (se 2 (by rfl) ⟨987243, by rfl⟩ : syracuseStep 2632649 = 1974487) B1974487
theorem B1756167 : Blo 1754578 1756167 := bstep (se 1 (by rfl) ⟨1317125, by rfl⟩ : syracuseStep 1756167 = 2634251) B2634251
theorem B1756175 : Blo 1754578 1756175 := bstep (se 1 (by rfl) ⟨1317131, by rfl⟩ : syracuseStep 1756175 = 2634263) B2634263
theorem B2632763 : Blo 1754578 2632763 := bstep (se 1 (by rfl) ⟨1974572, by rfl⟩ : syracuseStep 2632763 = 3949145) B3949145
theorem B1756219 : Blo 1754578 1756219 := bstep (se 1 (by rfl) ⟨1317164, by rfl⟩ : syracuseStep 1756219 = 2634329) B2634329
theorem B7498813 : Blo 1754578 7498813 := bstep (se 3 (by rfl) ⟨1406027, by rfl⟩ : syracuseStep 7498813 = 2812055) B2812055
theorem B8432707 : Blo 1754578 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B11242583 : Blo 1754578 11242583 := bstep (se 1 (by rfl) ⟨8431937, by rfl⟩ : syracuseStep 11242583 = 16863875) B16863875
theorem B5065847 : Blo 1754578 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B2632823 : Blo 1754578 2632823 := bstep (se 1 (by rfl) ⟨1974617, by rfl⟩ : syracuseStep 2632823 = 3949235) B3949235
theorem B37973123 : Blo 1754578 37973123 := bstep (se 1 (by rfl) ⟨28479842, by rfl⟩ : syracuseStep 37973123 = 56959685) B56959685
theorem B1756295 : Blo 1754578 1756295 := bstep (se 1 (by rfl) ⟨1317221, by rfl⟩ : syracuseStep 1756295 = 2634443) B2634443
theorem B2632847 : Blo 1754578 2632847 := bstep (se 1 (by rfl) ⟨1974635, by rfl⟩ : syracuseStep 2632847 = 3949271) B3949271
theorem B1756303 : Blo 1754578 1756303 := bstep (se 1 (by rfl) ⟨1317227, by rfl⟩ : syracuseStep 1756303 = 2634455) B2634455
theorem B2632889 : Blo 1754578 2632889 := bstep (se 2 (by rfl) ⟨987333, by rfl⟩ : syracuseStep 2632889 = 1974667) B1974667
theorem B1756347 : Blo 1754578 1756347 := bstep (se 1 (by rfl) ⟨1317260, by rfl⟩ : syracuseStep 1756347 = 2634521) B2634521
theorem B5000393 : Blo 1754578 5000393 := bstep (se 2 (by rfl) ⟨1875147, by rfl⟩ : syracuseStep 5000393 = 3750295) B3750295
theorem B2632967 : Blo 1754578 2632967 := bstep (se 1 (by rfl) ⟨1974725, by rfl⟩ : syracuseStep 2632967 = 3949451) B3949451
theorem B1756423 : Blo 1754578 1756423 := bstep (se 1 (by rfl) ⟨1317317, by rfl⟩ : syracuseStep 1756423 = 2634635) B2634635
theorem B4443407 : Blo 1754578 4443407 := bstep (se 1 (by rfl) ⟨3332555, by rfl⟩ : syracuseStep 4443407 = 6665111) B6665111
theorem B1756431 : Blo 1754578 1756431 := bstep (se 1 (by rfl) ⟨1317323, by rfl⟩ : syracuseStep 1756431 = 2634647) B2634647
theorem B2633003 : Blo 1754578 2633003 := bstep (se 1 (by rfl) ⟨1974752, by rfl⟩ : syracuseStep 2633003 = 3949505) B3949505
theorem B1756475 : Blo 1754578 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B2633033 : Blo 1754578 2633033 := bstep (se 2 (by rfl) ⟨987387, by rfl⟩ : syracuseStep 2633033 = 1974775) B1974775
theorem B3952007 : Blo 1754578 3952007 := bstep (se 1 (by rfl) ⟨2964005, by rfl⟩ : syracuseStep 3952007 = 5928011) B5928011
theorem B1756551 : Blo 1754578 1756551 := bstep (se 1 (by rfl) ⟨1317413, by rfl⟩ : syracuseStep 1756551 = 2634827) B2634827
theorem B1756559 : Blo 1754578 1756559 := bstep (se 1 (by rfl) ⟨1317419, by rfl⟩ : syracuseStep 1756559 = 2634839) B2634839
theorem B5623187 : Blo 1754578 5623187 := bstep (se 1 (by rfl) ⟨4217390, by rfl⟩ : syracuseStep 5623187 = 8434781) B8434781
theorem B7499155 : Blo 1754578 7499155 := bstep (se 1 (by rfl) ⟨5624366, by rfl⟩ : syracuseStep 7499155 = 11248733) B11248733
theorem B2633147 : Blo 1754578 2633147 := bstep (se 1 (by rfl) ⟨1974860, by rfl⟩ : syracuseStep 2633147 = 3949721) B3949721
theorem B2633207 : Blo 1754578 2633207 := bstep (se 1 (by rfl) ⟨1974905, by rfl⟩ : syracuseStep 2633207 = 3949811) B3949811
theorem B2633231 : Blo 1754578 2633231 := bstep (se 1 (by rfl) ⟨1974923, by rfl⟩ : syracuseStep 2633231 = 3949847) B3949847
theorem B8883755 : Blo 1754578 8883755 := bstep (se 1 (by rfl) ⟨6662816, by rfl⟩ : syracuseStep 8883755 = 13325633) B13325633
theorem B2633273 : Blo 1754578 2633273 := bstep (se 2 (by rfl) ⟨987477, by rfl⟩ : syracuseStep 2633273 = 1974955) B1974955
theorem B3952187 : Blo 1754578 3952187 := bstep (se 1 (by rfl) ⟨2964140, by rfl⟩ : syracuseStep 3952187 = 5928281) B5928281
theorem B6327875 : Blo 1754578 6327875 := bstep (se 1 (by rfl) ⟨4745906, by rfl⟩ : syracuseStep 6327875 = 9491813) B9491813
theorem B2633351 : Blo 1754578 2633351 := bstep (se 1 (by rfl) ⟨1975013, by rfl⟩ : syracuseStep 2633351 = 3950027) B3950027
theorem B2633387 : Blo 1754578 2633387 := bstep (se 1 (by rfl) ⟨1975040, by rfl⟩ : syracuseStep 2633387 = 3950081) B3950081
theorem B16010945 : Blo 1754578 16010945 := bstep (se 2 (by rfl) ⟨6004104, by rfl⟩ : syracuseStep 16010945 = 12008209) B12008209
theorem B2633417 : Blo 1754578 2633417 := bstep (se 2 (by rfl) ⟨987531, by rfl⟩ : syracuseStep 2633417 = 1975063) B1975063
theorem B9490213 : Blo 1754578 9490213 := bstep (se 4 (by rfl) ⟨889707, by rfl⟩ : syracuseStep 9490213 = 1779415) B1779415
theorem B11398963 : Blo 1754578 11398963 := bstep (se 1 (by rfl) ⟨8549222, by rfl⟩ : syracuseStep 11398963 = 17098445) B17098445
theorem B2961211 : Blo 1754578 2961211 := bstep (se 1 (by rfl) ⟨2220908, by rfl⟩ : syracuseStep 2961211 = 4441817) B4441817
theorem B2633531 : Blo 1754578 2633531 := bstep (se 1 (by rfl) ⟨1975148, by rfl⟩ : syracuseStep 2633531 = 3950297) B3950297
theorem B5926715 : Blo 1754578 5926715 := bstep (se 1 (by rfl) ⟨4445036, by rfl⟩ : syracuseStep 5926715 = 8890073) B8890073
theorem B2633591 : Blo 1754578 2633591 := bstep (se 1 (by rfl) ⟨1975193, by rfl⟩ : syracuseStep 2633591 = 3950387) B3950387
theorem B2633615 : Blo 1754578 2633615 := bstep (se 1 (by rfl) ⟨1975211, by rfl⟩ : syracuseStep 2633615 = 3950423) B3950423
theorem B20541335 : Blo 1754578 20541335 := bstep (se 1 (by rfl) ⟨15406001, by rfl⟩ : syracuseStep 20541335 = 30812003) B30812003
theorem B2633657 : Blo 1754578 2633657 := bstep (se 2 (by rfl) ⟨987621, by rfl⟩ : syracuseStep 2633657 = 1975243) B1975243
theorem B2961353 : Blo 1754578 2961353 := bstep (se 2 (by rfl) ⟨1110507, by rfl⟩ : syracuseStep 2961353 = 2221015) B2221015
theorem B4444105 : Blo 1754578 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B9490385 : Blo 1754578 9490385 := bstep (se 2 (by rfl) ⟨3558894, by rfl⟩ : syracuseStep 9490385 = 7117789) B7117789
theorem B2633735 : Blo 1754578 2633735 := bstep (se 1 (by rfl) ⟨1975301, by rfl⟩ : syracuseStep 2633735 = 3950603) B3950603
theorem B2633771 : Blo 1754578 2633771 := bstep (se 1 (by rfl) ⟨1975328, by rfl⟩ : syracuseStep 2633771 = 3950657) B3950657
theorem B5001259 : Blo 1754578 5001259 := bstep (se 1 (by rfl) ⟨3750944, by rfl⟩ : syracuseStep 5001259 = 7501889) B7501889
theorem B6328381 : Blo 1754578 6328381 := bstep (se 3 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 6328381 = 2373143) B2373143
theorem B2633801 : Blo 1754578 2633801 := bstep (se 2 (by rfl) ⟨987675, by rfl⟩ : syracuseStep 2633801 = 1975351) B1975351
theorem B4444247 : Blo 1754578 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B8892503 : Blo 1754578 8892503 := bstep (se 1 (by rfl) ⟨6669377, by rfl⟩ : syracuseStep 8892503 = 13338755) B13338755
theorem B64065629 : Blo 1754578 64065629 := bstep (se 3 (by rfl) ⟨12012305, by rfl⟩ : syracuseStep 64065629 = 24024611) B24024611
theorem B2633915 : Blo 1754578 2633915 := bstep (se 1 (by rfl) ⟨1975436, by rfl⟩ : syracuseStep 2633915 = 3950873) B3950873
theorem B2633975 : Blo 1754578 2633975 := bstep (se 1 (by rfl) ⟨1975481, by rfl⟩ : syracuseStep 2633975 = 3950963) B3950963
theorem B2633999 : Blo 1754578 2633999 := bstep (se 1 (by rfl) ⟨1975499, by rfl⟩ : syracuseStep 2633999 = 3950999) B3950999
theorem B5927201 : Blo 1754578 5927201 := bstep (se 2 (by rfl) ⟨2222700, by rfl⟩ : syracuseStep 5927201 = 4445401) B4445401
theorem B2634041 : Blo 1754578 2634041 := bstep (se 2 (by rfl) ⟨987765, by rfl⟩ : syracuseStep 2634041 = 1975531) B1975531
theorem B5001533 : Blo 1754578 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B2634119 : Blo 1754578 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B2634155 : Blo 1754578 2634155 := bstep (se 1 (by rfl) ⟨1975616, by rfl⟩ : syracuseStep 2634155 = 3951233) B3951233
theorem B2109883 : Blo 1754578 2109883 := bstep (se 1 (by rfl) ⟨1582412, by rfl⟩ : syracuseStep 2109883 = 3164825) B3164825
theorem B2634185 : Blo 1754578 2634185 := bstep (se 2 (by rfl) ⟨987819, by rfl⟩ : syracuseStep 2634185 = 1975639) B1975639
theorem B2634299 : Blo 1754578 2634299 := bstep (se 1 (by rfl) ⟨1975724, by rfl⟩ : syracuseStep 2634299 = 3951449) B3951449
theorem B14430797 : Blo 1754578 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B2634359 : Blo 1754578 2634359 := bstep (se 1 (by rfl) ⟨1975769, by rfl⟩ : syracuseStep 2634359 = 3951539) B3951539
theorem B2962055 : Blo 1754578 2962055 := bstep (se 1 (by rfl) ⟨2221541, by rfl⟩ : syracuseStep 2962055 = 4443083) B4443083
theorem B2634383 : Blo 1754578 2634383 := bstep (se 1 (by rfl) ⟨1975787, by rfl⟩ : syracuseStep 2634383 = 3951575) B3951575
theorem B5001875 : Blo 1754578 5001875 := bstep (se 1 (by rfl) ⟨3751406, by rfl⟩ : syracuseStep 5001875 = 7502813) B7502813
theorem B2634425 : Blo 1754578 2634425 := bstep (se 2 (by rfl) ⟨987909, by rfl⟩ : syracuseStep 2634425 = 1975819) B1975819
theorem B2634503 : Blo 1754578 2634503 := bstep (se 1 (by rfl) ⟨1975877, by rfl⟩ : syracuseStep 2634503 = 3951755) B3951755
theorem B2634539 : Blo 1754578 2634539 := bstep (se 1 (by rfl) ⟨1975904, by rfl⟩ : syracuseStep 2634539 = 3951809) B3951809
theorem B8885051 : Blo 1754578 8885051 := bstep (se 1 (by rfl) ⟨6663788, by rfl⟩ : syracuseStep 8885051 = 13327577) B13327577
theorem B2634569 : Blo 1754578 2634569 := bstep (se 2 (by rfl) ⟨987963, by rfl⟩ : syracuseStep 2634569 = 1975927) B1975927
theorem B5927795 : Blo 1754578 5927795 := bstep (se 1 (by rfl) ⟨4445846, by rfl⟩ : syracuseStep 5927795 = 8891693) B8891693
theorem B2634683 : Blo 1754578 2634683 := bstep (se 1 (by rfl) ⟨1976012, by rfl⟩ : syracuseStep 2634683 = 3952025) B3952025
theorem B8885213 : Blo 1754578 8885213 := bstep (se 3 (by rfl) ⟨1665977, by rfl⟩ : syracuseStep 8885213 = 3331955) B3331955
theorem B2634743 : Blo 1754578 2634743 := bstep (se 1 (by rfl) ⟨1976057, by rfl⟩ : syracuseStep 2634743 = 3952115) B3952115
theorem B38466571 : Blo 1754578 38466571 := bstep (se 1 (by rfl) ⟨28849928, by rfl⟩ : syracuseStep 38466571 = 57699857) B57699857
theorem B2634767 : Blo 1754578 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B19248151 : Blo 1754578 19248151 := bstep (se 1 (by rfl) ⟨14436113, by rfl⟩ : syracuseStep 19248151 = 28872227) B28872227
theorem B9385003 : Blo 1754578 9385003 := bstep (se 1 (by rfl) ⟨7038752, by rfl⟩ : syracuseStep 9385003 = 14077505) B14077505
theorem B2634809 : Blo 1754578 2634809 := bstep (se 2 (by rfl) ⟨988053, by rfl⟩ : syracuseStep 2634809 = 1976107) B1976107
theorem B10679363 : Blo 1754578 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B6329431 : Blo 1754578 6329431 := bstep (se 1 (by rfl) ⟨4747073, by rfl⟩ : syracuseStep 6329431 = 9494147) B9494147
theorem B3331219 : Blo 1754578 3331219 := bstep (se 1 (by rfl) ⟨2498414, by rfl⟩ : syracuseStep 3331219 = 4996829) B4996829
theorem B2962703 : Blo 1754578 2962703 := bstep (se 1 (by rfl) ⟨2222027, by rfl⟩ : syracuseStep 2962703 = 4444055) B4444055
theorem B8885537 : Blo 1754578 8885537 := bstep (se 2 (by rfl) ⟨3332076, by rfl⟩ : syracuseStep 8885537 = 6664153) B6664153
theorem B42726689 : Blo 1754578 42726689 := bstep (se 2 (by rfl) ⟨16022508, by rfl⟩ : syracuseStep 42726689 = 32045017) B32045017
theorem B13333895 : Blo 1754578 13333895 := bstep (se 1 (by rfl) ⟨10000421, by rfl⟩ : syracuseStep 13333895 = 20000843) B20000843
theorem B16012691 : Blo 1754578 16012691 := bstep (se 1 (by rfl) ⟨12009518, by rfl⟩ : syracuseStep 16012691 = 24019037) B24019037
theorem B9491897 : Blo 1754578 9491897 := bstep (se 2 (by rfl) ⟨3559461, by rfl⟩ : syracuseStep 9491897 = 7118923) B7118923
theorem B9999875 : Blo 1754578 9999875 := bstep (se 1 (by rfl) ⟨7499906, by rfl⟩ : syracuseStep 9999875 = 14999813) B14999813
theorem B2668039 : Blo 1754578 2668039 := bstep (se 1 (by rfl) ⟨2001029, by rfl⟩ : syracuseStep 2668039 = 4002059) B4002059
theorem B21345869 : Blo 1754578 21345869 := bstep (se 3 (by rfl) ⟨4002350, by rfl⟩ : syracuseStep 21345869 = 8004701) B8004701
theorem B3749561 : Blo 1754578 3749561 := bstep (se 2 (by rfl) ⟨1406085, by rfl⟩ : syracuseStep 3749561 = 2812171) B2812171
theorem B2963243 : Blo 1754578 2963243 := bstep (se 1 (by rfl) ⟨2222432, by rfl⟩ : syracuseStep 2963243 = 4444865) B4444865
theorem B4216691 : Blo 1754578 4216691 := bstep (se 1 (by rfl) ⟨3162518, by rfl⟩ : syracuseStep 4216691 = 6325037) B6325037
theorem B10000331 : Blo 1754578 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B10680331 : Blo 1754578 10680331 := bstep (se 1 (by rfl) ⟨8010248, by rfl⟩ : syracuseStep 10680331 = 16020497) B16020497
theorem B4446323 : Blo 1754578 4446323 := bstep (se 1 (by rfl) ⟨3334742, by rfl⟩ : syracuseStep 4446323 = 6669485) B6669485
theorem B1874063 : Blo 1754578 1874063 := bstep (se 1 (by rfl) ⟨1405547, by rfl⟩ : syracuseStep 1874063 = 2811095) B2811095
theorem B2963641 : Blo 1754578 2963641 := bstep (se 2 (by rfl) ⟨1111365, by rfl⟩ : syracuseStep 2963641 = 2222731) B2222731
theorem B15005897 : Blo 1754578 15005897 := bstep (se 2 (by rfl) ⟨5627211, by rfl⟩ : syracuseStep 15005897 = 11254423) B11254423
theorem B8886509 : Blo 1754578 8886509 := bstep (se 3 (by rfl) ⟨1666220, by rfl⟩ : syracuseStep 8886509 = 3332441) B3332441
theorem B3332411 : Blo 1754578 3332411 := bstep (se 1 (by rfl) ⟨2499308, by rfl⟩ : syracuseStep 3332411 = 4998617) B4998617
theorem B19995011 : Blo 1754578 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B10680893 : Blo 1754578 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B11246147 : Blo 1754578 11246147 := bstep (se 1 (by rfl) ⟨8434610, by rfl⟩ : syracuseStep 11246147 = 16869221) B16869221
theorem B10001015 : Blo 1754578 10001015 := bstep (se 1 (by rfl) ⟨7500761, by rfl⟩ : syracuseStep 10001015 = 15001523) B15001523
theorem B11246273 : Blo 1754578 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B3750671 : Blo 1754578 3750671 := bstep (se 1 (by rfl) ⟨2813003, by rfl⟩ : syracuseStep 3750671 = 5626007) B5626007
theorem B3332897 : Blo 1754578 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B4275031 : Blo 1754578 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B7502777 : Blo 1754578 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B16022539 : Blo 1754578 16022539 := bstep (se 1 (by rfl) ⟨12016904, by rfl⟩ : syracuseStep 16022539 = 24033809) B24033809
theorem B8887319 : Blo 1754578 8887319 := bstep (se 1 (by rfl) ⟨6665489, by rfl⟩ : syracuseStep 8887319 = 13330979) B13330979
theorem B3333163 : Blo 1754578 3333163 := bstep (se 1 (by rfl) ⟨2499872, by rfl⟩ : syracuseStep 3333163 = 4999745) B4999745
theorem B2669755 : Blo 1754578 2669755 := bstep (se 1 (by rfl) ⟨2002316, by rfl⟩ : syracuseStep 2669755 = 4004633) B4004633
theorem B3751201 : Blo 1754578 3751201 := bstep (se 2 (by rfl) ⟨1406700, by rfl⟩ : syracuseStep 3751201 = 2813401) B2813401
theorem B1875259 : Blo 1754578 1875259 := bstep (se 1 (by rfl) ⟨1406444, by rfl⟩ : syracuseStep 1875259 = 2812889) B2812889
theorem B5922233 : Blo 1754578 5922233 := bstep (se 2 (by rfl) ⟨2220837, by rfl⟩ : syracuseStep 5922233 = 4441675) B4441675
theorem B6323665 : Blo 1754578 6323665 := bstep (se 2 (by rfl) ⟨2371374, by rfl⟩ : syracuseStep 6323665 = 4742749) B4742749
theorem B6323723 : Blo 1754578 6323723 := bstep (se 1 (by rfl) ⟨4742792, by rfl⟩ : syracuseStep 6323723 = 9485585) B9485585
theorem B3948047 : Blo 1754578 3948047 := bstep (se 1 (by rfl) ⟨2961035, by rfl⟩ : syracuseStep 3948047 = 5922071) B5922071
theorem B3948065 : Blo 1754578 3948065 := bstep (se 2 (by rfl) ⟨1480524, by rfl⟩ : syracuseStep 3948065 = 2961049) B2961049
theorem B6323779 : Blo 1754578 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B1973947 : Blo 1754578 1973947 := bstep (se 1 (by rfl) ⟨1480460, by rfl⟩ : syracuseStep 1973947 = 2960921) B2960921
theorem B2498249 : Blo 1754578 2498249 := bstep (se 2 (by rfl) ⟨936843, by rfl⟩ : syracuseStep 2498249 = 1873687) B1873687
theorem B18972467 : Blo 1754578 18972467 := bstep (se 1 (by rfl) ⟨14229350, by rfl⟩ : syracuseStep 18972467 = 28458701) B28458701
theorem B24035123 : Blo 1754578 24035123 := bstep (se 1 (by rfl) ⟨18026342, by rfl⟩ : syracuseStep 24035123 = 36052685) B36052685
theorem B9994043 : Blo 1754578 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B3948407 : Blo 1754578 3948407 := bstep (se 1 (by rfl) ⟨2961305, by rfl⟩ : syracuseStep 3948407 = 5922611) B5922611
theorem B5635975 : Blo 1754578 5635975 := bstep (se 1 (by rfl) ⟨4226981, by rfl⟩ : syracuseStep 5635975 = 8453963) B8453963
theorem B4997011 : Blo 1754578 4997011 := bstep (se 1 (by rfl) ⟨3747758, by rfl⟩ : syracuseStep 4997011 = 7495517) B7495517
theorem B3948551 : Blo 1754578 3948551 := bstep (se 1 (by rfl) ⟨2961413, by rfl⟩ : syracuseStep 3948551 = 5922827) B5922827
theorem B14229541 : Blo 1754578 14229541 := bstep (se 4 (by rfl) ⟨1334019, by rfl⟩ : syracuseStep 14229541 = 2668039) B2668039
theorem B6668345 : Blo 1754578 6668345 := bstep (se 2 (by rfl) ⟨2500629, by rfl⟩ : syracuseStep 6668345 = 5001259) B5001259
theorem B3948623 : Blo 1754578 3948623 := bstep (se 1 (by rfl) ⟨2961467, by rfl⟩ : syracuseStep 3948623 = 5922935) B5922935
theorem B8437841 : Blo 1754578 8437841 := bstep (se 2 (by rfl) ⟨3164190, by rfl⟩ : syracuseStep 8437841 = 6328381) B6328381
theorem B3162323 : Blo 1754578 3162323 := bstep (se 1 (by rfl) ⟨2371742, by rfl⟩ : syracuseStep 3162323 = 4743485) B4743485
theorem B3334355 : Blo 1754578 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B4997501 : Blo 1754578 4997501 := bstep (se 3 (by rfl) ⟨937031, by rfl⟩ : syracuseStep 4997501 = 1874063) B1874063
theorem B1974703 : Blo 1754578 1974703 := bstep (se 1 (by rfl) ⟨1481027, by rfl⟩ : syracuseStep 1974703 = 2962055) B2962055
theorem B3334583 : Blo 1754578 3334583 := bstep (se 1 (by rfl) ⟨2500937, by rfl⟩ : syracuseStep 3334583 = 5001875) B5001875
theorem B3949019 : Blo 1754578 3949019 := bstep (se 1 (by rfl) ⟨2961764, by rfl⟩ : syracuseStep 3949019 = 5923529) B5923529
theorem B5923367 : Blo 1754578 5923367 := bstep (se 1 (by rfl) ⟨4442525, by rfl⟩ : syracuseStep 5923367 = 8885051) B8885051
theorem B5923475 : Blo 1754578 5923475 := bstep (se 1 (by rfl) ⟨4442606, by rfl⟩ : syracuseStep 5923475 = 8885213) B8885213
theorem B6668999 : Blo 1754578 6668999 := bstep (se 1 (by rfl) ⟨5001749, by rfl⟩ : syracuseStep 6668999 = 10003499) B10003499
theorem B13337297 : Blo 1754578 13337297 := bstep (se 2 (by rfl) ⟨5001486, by rfl⟩ : syracuseStep 13337297 = 10002973) B10002973
theorem B7119575 : Blo 1754578 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B1975135 : Blo 1754578 1975135 := bstep (se 1 (by rfl) ⟨1481351, by rfl⟩ : syracuseStep 1975135 = 2962703) B2962703
theorem B5923691 : Blo 1754578 5923691 := bstep (se 1 (by rfl) ⟨4442768, by rfl⟩ : syracuseStep 5923691 = 8885537) B8885537
theorem B28484459 : Blo 1754578 28484459 := bstep (se 1 (by rfl) ⟨21363344, by rfl⟩ : syracuseStep 28484459 = 42726689) B42726689
theorem B5923745 : Blo 1754578 5923745 := bstep (se 2 (by rfl) ⟨2221404, by rfl⟩ : syracuseStep 5923745 = 4442809) B4442809
theorem B9995183 : Blo 1754578 9995183 := bstep (se 1 (by rfl) ⟨7496387, by rfl⟩ : syracuseStep 9995183 = 14992775) B14992775
theorem B3949487 : Blo 1754578 3949487 := bstep (se 1 (by rfl) ⟨2962115, by rfl⟩ : syracuseStep 3949487 = 5924231) B5924231
theorem B8889263 : Blo 1754578 8889263 := bstep (se 1 (by rfl) ⟨6666947, by rfl⟩ : syracuseStep 8889263 = 13333895) B13333895
theorem B10675127 : Blo 1754578 10675127 := bstep (se 1 (by rfl) ⟨8006345, by rfl⟩ : syracuseStep 10675127 = 16012691) B16012691
theorem B14230579 : Blo 1754578 14230579 := bstep (se 1 (by rfl) ⟨10672934, by rfl⟩ : syracuseStep 14230579 = 21345869) B21345869
theorem B2499707 : Blo 1754578 2499707 := bstep (se 1 (by rfl) ⟨1874780, by rfl⟩ : syracuseStep 2499707 = 3749561) B3749561
theorem B3949739 : Blo 1754578 3949739 := bstep (se 1 (by rfl) ⟨2962304, by rfl⟩ : syracuseStep 3949739 = 5924609) B5924609
theorem B1975495 : Blo 1754578 1975495 := bstep (se 1 (by rfl) ⟨1481621, by rfl⟩ : syracuseStep 1975495 = 2963243) B2963243
theorem B2811127 : Blo 1754578 2811127 := bstep (se 1 (by rfl) ⟨2108345, by rfl⟩ : syracuseStep 2811127 = 4216691) B4216691
theorem B8439241 : Blo 1754578 8439241 := bstep (se 2 (by rfl) ⟨3164715, by rfl⟩ : syracuseStep 8439241 = 6329431) B6329431
theorem B1754587 : Blo 1754578 1754587 := bstep (se 1 (by rfl) ⟨1315940, by rfl⟩ : syracuseStep 1754587 = 2631881) B2631881
theorem B10003931 : Blo 1754578 10003931 := bstep (se 1 (by rfl) ⟨7502948, by rfl⟩ : syracuseStep 10003931 = 15005897) B15005897
theorem B5924339 : Blo 1754578 5924339 := bstep (se 1 (by rfl) ⟨4443254, by rfl⟩ : syracuseStep 5924339 = 8886509) B8886509
theorem B4441625 : Blo 1754578 4441625 := bstep (se 2 (by rfl) ⟨1665609, by rfl⟩ : syracuseStep 4441625 = 3331219) B3331219
theorem B1754663 : Blo 1754578 1754663 := bstep (se 1 (by rfl) ⟨1315997, by rfl⟩ : syracuseStep 1754663 = 2631995) B2631995
theorem B2221607 : Blo 1754578 2221607 := bstep (se 1 (by rfl) ⟨1666205, by rfl⟩ : syracuseStep 2221607 = 3332411) B3332411
theorem B1754703 : Blo 1754578 1754703 := bstep (se 1 (by rfl) ⟨1316027, by rfl⟩ : syracuseStep 1754703 = 2632055) B2632055
theorem B13330007 : Blo 1754578 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B1754719 : Blo 1754578 1754719 := bstep (se 1 (by rfl) ⟨1316039, by rfl⟩ : syracuseStep 1754719 = 2632079) B2632079
theorem B1754747 : Blo 1754578 1754747 := bstep (se 1 (by rfl) ⟨1316060, by rfl⟩ : syracuseStep 1754747 = 2632121) B2632121
theorem B1754799 : Blo 1754578 1754799 := bstep (se 1 (by rfl) ⟨1316099, by rfl⟩ : syracuseStep 1754799 = 2632199) B2632199
theorem B1754823 : Blo 1754578 1754823 := bstep (se 1 (by rfl) ⟨1316117, by rfl⟩ : syracuseStep 1754823 = 2632235) B2632235
theorem B3950279 : Blo 1754578 3950279 := bstep (se 1 (by rfl) ⟨2962709, by rfl⟩ : syracuseStep 3950279 = 5925419) B5925419
theorem B7120595 : Blo 1754578 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B7497431 : Blo 1754578 7497431 := bstep (se 1 (by rfl) ⟨5623073, by rfl⟩ : syracuseStep 7497431 = 11246147) B11246147
theorem B1754843 : Blo 1754578 1754843 := bstep (se 1 (by rfl) ⟨1316132, by rfl⟩ : syracuseStep 1754843 = 2632265) B2632265
theorem B2500345 : Blo 1754578 2500345 := bstep (se 2 (by rfl) ⟨937629, by rfl⟩ : syracuseStep 2500345 = 1875259) B1875259
theorem B1754919 : Blo 1754578 1754919 := bstep (se 1 (by rfl) ⟨1316189, by rfl⟩ : syracuseStep 1754919 = 2632379) B2632379
theorem B7497515 : Blo 1754578 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B1754959 : Blo 1754578 1754959 := bstep (se 1 (by rfl) ⟨1316219, by rfl⟩ : syracuseStep 1754959 = 2632439) B2632439
theorem B1754975 : Blo 1754578 1754975 := bstep (se 1 (by rfl) ⟨1316231, by rfl⟩ : syracuseStep 1754975 = 2632463) B2632463
theorem B2221931 : Blo 1754578 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B6661997 : Blo 1754578 6661997 := bstep (se 3 (by rfl) ⟨1249124, by rfl⟩ : syracuseStep 6661997 = 2498249) B2498249
theorem B1755003 : Blo 1754578 1755003 := bstep (se 1 (by rfl) ⟨1316252, by rfl⟩ : syracuseStep 1755003 = 2632505) B2632505
theorem B1755055 : Blo 1754578 1755055 := bstep (se 1 (by rfl) ⟨1316291, by rfl⟩ : syracuseStep 1755055 = 2632583) B2632583
theorem B8431553 : Blo 1754578 8431553 := bstep (se 2 (by rfl) ⟨3161832, by rfl⟩ : syracuseStep 8431553 = 6323665) B6323665
theorem B1755079 : Blo 1754578 1755079 := bstep (se 1 (by rfl) ⟨1316309, by rfl⟩ : syracuseStep 1755079 = 2632619) B2632619
theorem B1755099 : Blo 1754578 1755099 := bstep (se 1 (by rfl) ⟨1316324, by rfl⟩ : syracuseStep 1755099 = 2632649) B2632649
theorem B5924879 : Blo 1754578 5924879 := bstep (se 1 (by rfl) ⟨4443659, by rfl⟩ : syracuseStep 5924879 = 8887319) B8887319
theorem B1755175 : Blo 1754578 1755175 := bstep (se 1 (by rfl) ⟨1316381, by rfl⟩ : syracuseStep 1755175 = 2632763) B2632763
theorem B3377231 : Blo 1754578 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B1755215 : Blo 1754578 1755215 := bstep (se 1 (by rfl) ⟨1316411, by rfl⟩ : syracuseStep 1755215 = 2632823) B2632823
theorem B25315415 : Blo 1754578 25315415 := bstep (se 1 (by rfl) ⟨18986561, by rfl⟩ : syracuseStep 25315415 = 37973123) B37973123
theorem B8431705 : Blo 1754578 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B1755231 : Blo 1754578 1755231 := bstep (se 1 (by rfl) ⟨1316423, by rfl⟩ : syracuseStep 1755231 = 2632847) B2632847
theorem B1755259 : Blo 1754578 1755259 := bstep (se 1 (by rfl) ⟨1316444, by rfl⟩ : syracuseStep 1755259 = 2632889) B2632889
theorem B1755311 : Blo 1754578 1755311 := bstep (se 1 (by rfl) ⟨1316483, by rfl⟩ : syracuseStep 1755311 = 2632967) B2632967
theorem B1755335 : Blo 1754578 1755335 := bstep (se 1 (by rfl) ⟨1316501, by rfl⟩ : syracuseStep 1755335 = 2633003) B2633003
theorem B1755355 : Blo 1754578 1755355 := bstep (se 1 (by rfl) ⟨1316516, by rfl⟩ : syracuseStep 1755355 = 2633033) B2633033
theorem B2631929 : Blo 1754578 2631929 := bstep (se 2 (by rfl) ⟨986973, by rfl⟩ : syracuseStep 2631929 = 1973947) B1973947
theorem B1755431 : Blo 1754578 1755431 := bstep (se 1 (by rfl) ⟨1316573, by rfl⟩ : syracuseStep 1755431 = 2633147) B2633147
theorem B1755471 : Blo 1754578 1755471 := bstep (se 1 (by rfl) ⟨1316603, by rfl⟩ : syracuseStep 1755471 = 2633207) B2633207
theorem B2632031 : Blo 1754578 2632031 := bstep (se 1 (by rfl) ⟨1974023, by rfl⟩ : syracuseStep 2632031 = 3948047) B3948047
theorem B1755487 : Blo 1754578 1755487 := bstep (se 1 (by rfl) ⟨1316615, by rfl⟩ : syracuseStep 1755487 = 2633231) B2633231
theorem B2632043 : Blo 1754578 2632043 := bstep (se 1 (by rfl) ⟨1974032, by rfl⟩ : syracuseStep 2632043 = 3948065) B3948065
theorem B1755515 : Blo 1754578 1755515 := bstep (se 1 (by rfl) ⟨1316636, by rfl⟩ : syracuseStep 1755515 = 2633273) B2633273
theorem B15198617 : Blo 1754578 15198617 := bstep (se 2 (by rfl) ⟨5699481, by rfl⟩ : syracuseStep 15198617 = 11398963) B11398963
theorem B1755567 : Blo 1754578 1755567 := bstep (se 1 (by rfl) ⟨1316675, by rfl⟩ : syracuseStep 1755567 = 2633351) B2633351
theorem B1755591 : Blo 1754578 1755591 := bstep (se 1 (by rfl) ⟨1316693, by rfl⟩ : syracuseStep 1755591 = 2633387) B2633387
theorem B1755611 : Blo 1754578 1755611 := bstep (se 1 (by rfl) ⟨1316708, by rfl⟩ : syracuseStep 1755611 = 2633417) B2633417
theorem B8440301 : Blo 1754578 8440301 := bstep (se 3 (by rfl) ⟨1582556, by rfl⟩ : syracuseStep 8440301 = 3165113) B3165113
theorem B7514633 : Blo 1754578 7514633 := bstep (se 2 (by rfl) ⟨2817987, by rfl⟩ : syracuseStep 7514633 = 5635975) B5635975
theorem B6662681 : Blo 1754578 6662681 := bstep (se 2 (by rfl) ⟨2498505, by rfl⟩ : syracuseStep 6662681 = 4997011) B4997011
theorem B6662695 : Blo 1754578 6662695 := bstep (se 1 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 6662695 = 9994043) B9994043
theorem B1755687 : Blo 1754578 1755687 := bstep (se 1 (by rfl) ⟨1316765, by rfl⟩ : syracuseStep 1755687 = 2633531) B2633531
theorem B3951143 : Blo 1754578 3951143 := bstep (se 1 (by rfl) ⟨2963357, by rfl⟩ : syracuseStep 3951143 = 5926715) B5926715
theorem B2632271 : Blo 1754578 2632271 := bstep (se 1 (by rfl) ⟨1974203, by rfl⟩ : syracuseStep 2632271 = 3948407) B3948407
theorem B1755727 : Blo 1754578 1755727 := bstep (se 1 (by rfl) ⟨1316795, by rfl⟩ : syracuseStep 1755727 = 2633591) B2633591
theorem B5925473 : Blo 1754578 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B1755743 : Blo 1754578 1755743 := bstep (se 1 (by rfl) ⟨1316807, by rfl⟩ : syracuseStep 1755743 = 2633615) B2633615
theorem B1755771 : Blo 1754578 1755771 := bstep (se 1 (by rfl) ⟨1316828, by rfl⟩ : syracuseStep 1755771 = 2633657) B2633657
theorem B6326923 : Blo 1754578 6326923 := bstep (se 1 (by rfl) ⟨4745192, by rfl⟩ : syracuseStep 6326923 = 9490385) B9490385
theorem B1755823 : Blo 1754578 1755823 := bstep (se 1 (by rfl) ⟨1316867, by rfl⟩ : syracuseStep 1755823 = 2633735) B2633735
theorem B14240441 : Blo 1754578 14240441 := bstep (se 2 (by rfl) ⟨5340165, by rfl⟩ : syracuseStep 14240441 = 10680331) B10680331
theorem B2632391 : Blo 1754578 2632391 := bstep (se 1 (by rfl) ⟨1974293, by rfl⟩ : syracuseStep 2632391 = 3948587) B3948587
theorem B1755847 : Blo 1754578 1755847 := bstep (se 1 (by rfl) ⟨1316885, by rfl⟩ : syracuseStep 1755847 = 2633771) B2633771
theorem B1755867 : Blo 1754578 1755867 := bstep (se 1 (by rfl) ⟨1316900, by rfl⟩ : syracuseStep 1755867 = 2633801) B2633801
theorem B85453541 : Blo 1754578 85453541 := bstep (se 4 (by rfl) ⟨8011269, by rfl⟩ : syracuseStep 85453541 = 16022539) B16022539
theorem B1755943 : Blo 1754578 1755943 := bstep (se 1 (by rfl) ⟨1316957, by rfl⟩ : syracuseStep 1755943 = 2633915) B2633915
theorem B6941483 : Blo 1754578 6941483 := bstep (se 1 (by rfl) ⟨5206112, by rfl⟩ : syracuseStep 6941483 = 10412225) B10412225
theorem B1755983 : Blo 1754578 1755983 := bstep (se 1 (by rfl) ⟨1316987, by rfl⟩ : syracuseStep 1755983 = 2633975) B2633975
theorem B1755999 : Blo 1754578 1755999 := bstep (se 1 (by rfl) ⟨1316999, by rfl⟩ : syracuseStep 1755999 = 2633999) B2633999
theorem B2632553 : Blo 1754578 2632553 := bstep (se 2 (by rfl) ⟨987207, by rfl⟩ : syracuseStep 2632553 = 1974415) B1974415
theorem B3951467 : Blo 1754578 3951467 := bstep (se 1 (by rfl) ⟨2963600, by rfl⟩ : syracuseStep 3951467 = 5927201) B5927201
theorem B1756027 : Blo 1754578 1756027 := bstep (se 1 (by rfl) ⟨1317020, by rfl⟩ : syracuseStep 1756027 = 2634041) B2634041
theorem B3951521 : Blo 1754578 3951521 := bstep (se 2 (by rfl) ⟨1481820, by rfl⟩ : syracuseStep 3951521 = 2963641) B2963641
theorem B1756079 : Blo 1754578 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B2632631 : Blo 1754578 2632631 := bstep (se 1 (by rfl) ⟨1974473, by rfl⟩ : syracuseStep 2632631 = 3948947) B3948947
theorem B4746167 : Blo 1754578 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B1756103 : Blo 1754578 1756103 := bstep (se 1 (by rfl) ⟨1317077, by rfl⟩ : syracuseStep 1756103 = 2634155) B2634155
theorem B2632667 : Blo 1754578 2632667 := bstep (se 1 (by rfl) ⟨1974500, by rfl⟩ : syracuseStep 2632667 = 3949001) B3949001
theorem B1756123 : Blo 1754578 1756123 := bstep (se 1 (by rfl) ⟨1317092, by rfl⟩ : syracuseStep 1756123 = 2634185) B2634185
theorem B1756199 : Blo 1754578 1756199 := bstep (se 1 (by rfl) ⟨1317149, by rfl⟩ : syracuseStep 1756199 = 2634299) B2634299
theorem B9620531 : Blo 1754578 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B1756239 : Blo 1754578 1756239 := bstep (se 1 (by rfl) ⟨1317179, by rfl⟩ : syracuseStep 1756239 = 2634359) B2634359
theorem B1756255 : Blo 1754578 1756255 := bstep (se 1 (by rfl) ⟨1317191, by rfl⟩ : syracuseStep 1756255 = 2634383) B2634383
theorem B1756283 : Blo 1754578 1756283 := bstep (se 1 (by rfl) ⟨1317212, by rfl⟩ : syracuseStep 1756283 = 2634425) B2634425
theorem B1756335 : Blo 1754578 1756335 := bstep (se 1 (by rfl) ⟨1317251, by rfl⟩ : syracuseStep 1756335 = 2634503) B2634503
theorem B12651713 : Blo 1754578 12651713 := bstep (se 2 (by rfl) ⟨4744392, by rfl⟩ : syracuseStep 12651713 = 9488785) B9488785
theorem B1756359 : Blo 1754578 1756359 := bstep (se 1 (by rfl) ⟨1317269, by rfl⟩ : syracuseStep 1756359 = 2634539) B2634539
theorem B1756379 : Blo 1754578 1756379 := bstep (se 1 (by rfl) ⟨1317284, by rfl⟩ : syracuseStep 1756379 = 2634569) B2634569
theorem B3951863 : Blo 1754578 3951863 := bstep (se 1 (by rfl) ⟨2963897, by rfl⟩ : syracuseStep 3951863 = 5927795) B5927795
theorem B2813177 : Blo 1754578 2813177 := bstep (se 2 (by rfl) ⟨1054941, by rfl⟩ : syracuseStep 2813177 = 2109883) B2109883
theorem B1756455 : Blo 1754578 1756455 := bstep (se 1 (by rfl) ⟨1317341, by rfl⟩ : syracuseStep 1756455 = 2634683) B2634683
theorem B6663485 : Blo 1754578 6663485 := bstep (se 3 (by rfl) ⟨1249403, by rfl⟩ : syracuseStep 6663485 = 2498807) B2498807
theorem B1756495 : Blo 1754578 1756495 := bstep (se 1 (by rfl) ⟨1317371, by rfl⟩ : syracuseStep 1756495 = 2634743) B2634743
theorem B1756511 : Blo 1754578 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B1756539 : Blo 1754578 1756539 := bstep (se 1 (by rfl) ⟨1317404, by rfl⟩ : syracuseStep 1756539 = 2634809) B2634809
theorem B2633135 : Blo 1754578 2633135 := bstep (se 1 (by rfl) ⟨1974851, by rfl⟩ : syracuseStep 2633135 = 3949703) B3949703
theorem B6663667 : Blo 1754578 6663667 := bstep (se 1 (by rfl) ⟨4997750, by rfl⟩ : syracuseStep 6663667 = 9995501) B9995501
theorem B2633225 : Blo 1754578 2633225 := bstep (se 2 (by rfl) ⟨987459, by rfl⟩ : syracuseStep 2633225 = 1974919) B1974919
theorem B2633255 : Blo 1754578 2633255 := bstep (se 1 (by rfl) ⟨1974941, by rfl⟩ : syracuseStep 2633255 = 3949883) B3949883
theorem B2960975 : Blo 1754578 2960975 := bstep (se 1 (by rfl) ⟨2220731, by rfl⟩ : syracuseStep 2960975 = 4441463) B4441463
theorem B37957207 : Blo 1754578 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B2633339 : Blo 1754578 2633339 := bstep (se 1 (by rfl) ⟨1975004, by rfl⟩ : syracuseStep 2633339 = 3950009) B3950009
theorem B6327931 : Blo 1754578 6327931 := bstep (se 1 (by rfl) ⟨4745948, by rfl⟩ : syracuseStep 6327931 = 9491897) B9491897
theorem B14995165 : Blo 1754578 14995165 := bstep (se 3 (by rfl) ⟨2811593, by rfl⟩ : syracuseStep 14995165 = 5623187) B5623187
theorem B2633465 : Blo 1754578 2633465 := bstep (se 2 (by rfl) ⟨987549, by rfl⟩ : syracuseStep 2633465 = 1975099) B1975099
theorem B2633567 : Blo 1754578 2633567 := bstep (se 1 (by rfl) ⟨1975175, by rfl⟩ : syracuseStep 2633567 = 3950351) B3950351
theorem B2633579 : Blo 1754578 2633579 := bstep (se 1 (by rfl) ⟨1975184, by rfl⟩ : syracuseStep 2633579 = 3950369) B3950369
theorem B38490005 : Blo 1754578 38490005 := bstep (se 6 (by rfl) ⟨902109, by rfl⟩ : syracuseStep 38490005 = 1804219) B1804219
theorem B2109359 : Blo 1754578 2109359 := bstep (se 1 (by rfl) ⟨1582019, by rfl⟩ : syracuseStep 2109359 = 3164039) B3164039
theorem B5926931 : Blo 1754578 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B4444217 : Blo 1754578 4444217 := bstep (se 2 (by rfl) ⟨1666581, by rfl⟩ : syracuseStep 4444217 = 3333163) B3333163
theorem B12513337 : Blo 1754578 12513337 := bstep (se 2 (by rfl) ⟨4692501, by rfl⟩ : syracuseStep 12513337 = 9385003) B9385003
theorem B2633807 : Blo 1754578 2633807 := bstep (se 1 (by rfl) ⟨1975355, by rfl⟩ : syracuseStep 2633807 = 3950711) B3950711
theorem B9998417 : Blo 1754578 9998417 := bstep (se 2 (by rfl) ⟨3749406, by rfl⟩ : syracuseStep 9998417 = 7498813) B7498813
theorem B11243609 : Blo 1754578 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B7499891 : Blo 1754578 7499891 := bstep (se 1 (by rfl) ⟨5624918, by rfl⟩ : syracuseStep 7499891 = 11249837) B11249837
theorem B2633927 : Blo 1754578 2633927 := bstep (se 1 (by rfl) ⟨1975445, by rfl⟩ : syracuseStep 2633927 = 3950891) B3950891
theorem B3559673 : Blo 1754578 3559673 := bstep (se 2 (by rfl) ⟨1334877, by rfl⟩ : syracuseStep 3559673 = 2669755) B2669755
theorem B7500043 : Blo 1754578 7500043 := bstep (se 1 (by rfl) ⟨5625032, by rfl⟩ : syracuseStep 7500043 = 11250065) B11250065
theorem B5927255 : Blo 1754578 5927255 := bstep (se 1 (by rfl) ⟨4445441, by rfl⟩ : syracuseStep 5927255 = 8890883) B8890883
theorem B2634089 : Blo 1754578 2634089 := bstep (se 2 (by rfl) ⟨987783, by rfl⟩ : syracuseStep 2634089 = 1975567) B1975567
theorem B5001601 : Blo 1754578 5001601 := bstep (se 2 (by rfl) ⟨1875600, by rfl⟩ : syracuseStep 5001601 = 3751201) B3751201
theorem B2961839 : Blo 1754578 2961839 := bstep (se 1 (by rfl) ⟨2221379, by rfl⟩ : syracuseStep 2961839 = 4442759) B4442759
theorem B2634167 : Blo 1754578 2634167 := bstep (se 1 (by rfl) ⟨1975625, by rfl⟩ : syracuseStep 2634167 = 3951251) B3951251
theorem B2634203 : Blo 1754578 2634203 := bstep (se 1 (by rfl) ⟨1975652, by rfl⟩ : syracuseStep 2634203 = 3951305) B3951305
theorem B9998873 : Blo 1754578 9998873 := bstep (se 2 (by rfl) ⟨3749577, by rfl⟩ : syracuseStep 9998873 = 7499155) B7499155
theorem B5001851 : Blo 1754578 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B6664913 : Blo 1754578 6664913 := bstep (se 2 (by rfl) ⟨2499342, by rfl⟩ : syracuseStep 6664913 = 4998685) B4998685
theorem B2962271 : Blo 1754578 2962271 := bstep (se 1 (by rfl) ⟨2221703, by rfl⟩ : syracuseStep 2962271 = 4443407) B4443407
theorem B2634671 : Blo 1754578 2634671 := bstep (se 1 (by rfl) ⟨1976003, by rfl⟩ : syracuseStep 2634671 = 3952007) B3952007
theorem B4215815 : Blo 1754578 4215815 := bstep (se 1 (by rfl) ⟨3161861, by rfl⟩ : syracuseStep 4215815 = 6323723) B6323723
theorem B2634761 : Blo 1754578 2634761 := bstep (se 2 (by rfl) ⟨988035, by rfl⟩ : syracuseStep 2634761 = 1976071) B1976071
theorem B2634791 : Blo 1754578 2634791 := bstep (se 1 (by rfl) ⟨1976093, by rfl⟩ : syracuseStep 2634791 = 3952187) B3952187
theorem B12653617 : Blo 1754578 12653617 := bstep (se 2 (by rfl) ⟨4745106, by rfl⟩ : syracuseStep 12653617 = 9490213) B9490213
theorem B4502585 : Blo 1754578 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B54776893 : Blo 1754578 54776893 := bstep (se 3 (by rfl) ⟨10270667, by rfl⟩ : syracuseStep 54776893 = 20541335) B20541335
theorem B6665597 : Blo 1754578 6665597 := bstep (se 3 (by rfl) ⟨1249799, by rfl⟩ : syracuseStep 6665597 = 2499599) B2499599
theorem B2962831 : Blo 1754578 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B5928335 : Blo 1754578 5928335 := bstep (se 1 (by rfl) ⟨4446251, by rfl⟩ : syracuseStep 5928335 = 8892503) B8892503
theorem B42710419 : Blo 1754578 42710419 := bstep (se 1 (by rfl) ⟨32032814, by rfl⟩ : syracuseStep 42710419 = 64065629) B64065629
theorem B4445705 : Blo 1754578 4445705 := bstep (se 2 (by rfl) ⟨1667139, by rfl⟩ : syracuseStep 4445705 = 3334279) B3334279
theorem B25319105 : Blo 1754578 25319105 := bstep (se 2 (by rfl) ⟨9494664, by rfl⟩ : syracuseStep 25319105 = 18989329) B18989329
theorem B8672989 : Blo 1754578 8672989 := bstep (se 3 (by rfl) ⟨1626185, by rfl⟩ : syracuseStep 8672989 = 3252371) B3252371
theorem B13334381 : Blo 1754578 13334381 := bstep (se 3 (by rfl) ⟨2500196, by rfl⟩ : syracuseStep 13334381 = 5000393) B5000393
theorem B22501313 : Blo 1754578 22501313 := bstep (se 2 (by rfl) ⟨8437992, by rfl⟩ : syracuseStep 22501313 = 16875985) B16875985
theorem B3332153 : Blo 1754578 3332153 := bstep (se 2 (by rfl) ⟨1249557, by rfl⟩ : syracuseStep 3332153 = 2499115) B2499115
theorem B2963513 : Blo 1754578 2963513 := bstep (se 2 (by rfl) ⟨1111317, by rfl⟩ : syracuseStep 2963513 = 2222635) B2222635
theorem B6666583 : Blo 1754578 6666583 := bstep (se 1 (by rfl) ⟨4999937, by rfl⟩ : syracuseStep 6666583 = 9999875) B9999875
theorem B30005639 : Blo 1754578 30005639 := bstep (se 1 (by rfl) ⟨22504229, by rfl⟩ : syracuseStep 30005639 = 45008459) B45008459
theorem B3332495 : Blo 1754578 3332495 := bstep (se 1 (by rfl) ⟨2499371, by rfl⟩ : syracuseStep 3332495 = 4998743) B4998743
theorem B5700041 : Blo 1754578 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B6666887 : Blo 1754578 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B51288761 : Blo 1754578 51288761 := bstep (se 2 (by rfl) ⟨19233285, by rfl⟩ : syracuseStep 51288761 = 38466571) B38466571
theorem B25664201 : Blo 1754578 25664201 := bstep (se 2 (by rfl) ⟨9624075, by rfl⟩ : syracuseStep 25664201 = 19248151) B19248151
theorem B8886995 : Blo 1754578 8886995 := bstep (se 1 (by rfl) ⟨6665246, by rfl⟩ : syracuseStep 8886995 = 13330493) B13330493
theorem B2964215 : Blo 1754578 2964215 := bstep (se 1 (by rfl) ⟨2223161, by rfl⟩ : syracuseStep 2964215 = 4446323) B4446323
theorem B6667343 : Blo 1754578 6667343 := bstep (se 1 (by rfl) ⟨5000507, by rfl⟩ : syracuseStep 6667343 = 10001015) B10001015
theorem B5627033 : Blo 1754578 5627033 := bstep (se 2 (by rfl) ⟨2110137, by rfl⟩ : syracuseStep 5627033 = 4220275) B4220275
theorem B5921963 : Blo 1754578 5921963 := bstep (se 1 (by rfl) ⟨4441472, by rfl⟩ : syracuseStep 5921963 = 8882945) B8882945
theorem B25320721 : Blo 1754578 25320721 := bstep (se 2 (by rfl) ⟨9495270, by rfl⟩ : syracuseStep 25320721 = 18990541) B18990541
theorem B10001789 : Blo 1754578 10001789 := bstep (se 3 (by rfl) ⟨1875335, by rfl⟩ : syracuseStep 10001789 = 3750671) B3750671
theorem B7495055 : Blo 1754578 7495055 := bstep (se 1 (by rfl) ⟨5621291, by rfl⟩ : syracuseStep 7495055 = 11242583) B11242583
theorem B3948155 : Blo 1754578 3948155 := bstep (se 1 (by rfl) ⟨2961116, by rfl⟩ : syracuseStep 3948155 = 5922233) B5922233
theorem B5922503 : Blo 1754578 5922503 := bstep (se 1 (by rfl) ⟨4441877, by rfl⟩ : syracuseStep 5922503 = 8883755) B8883755
theorem B4218583 : Blo 1754578 4218583 := bstep (se 1 (by rfl) ⟨3163937, by rfl⟩ : syracuseStep 4218583 = 6327875) B6327875
theorem B3948281 : Blo 1754578 3948281 := bstep (se 2 (by rfl) ⟨1480605, by rfl⟩ : syracuseStep 3948281 = 2961211) B2961211
theorem B10673963 : Blo 1754578 10673963 := bstep (se 1 (by rfl) ⟨8005472, by rfl⟩ : syracuseStep 10673963 = 16010945) B16010945
theorem B12648311 : Blo 1754578 12648311 := bstep (se 1 (by rfl) ⟨9486233, by rfl⟩ : syracuseStep 12648311 = 18972467) B18972467
theorem B16023415 : Blo 1754578 16023415 := bstep (se 1 (by rfl) ⟨12017561, by rfl⟩ : syracuseStep 16023415 = 24035123) B24035123
theorem B1974235 : Blo 1754578 1974235 := bstep (se 1 (by rfl) ⟨1480676, by rfl⟩ : syracuseStep 1974235 = 2961353) B2961353
theorem B18972721 : Blo 1754578 18972721 := bstep (se 2 (by rfl) ⟨7114770, by rfl⟩ : syracuseStep 18972721 = 14229541) B14229541
theorem B7495739 : Blo 1754578 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B1974559 : Blo 1754578 1974559 := bstep (se 1 (by rfl) ⟨1480919, by rfl⟩ : syracuseStep 1974559 = 2961839) B2961839
theorem B3948911 : Blo 1754578 3948911 := bstep (se 1 (by rfl) ⟨2961683, by rfl⟩ : syracuseStep 3948911 = 5923367) B5923367
theorem B3948983 : Blo 1754578 3948983 := bstep (se 1 (by rfl) ⟨2961737, by rfl⟩ : syracuseStep 3948983 = 5923475) B5923475
theorem B8888777 : Blo 1754578 8888777 := bstep (se 2 (by rfl) ⟨3333291, by rfl⟩ : syracuseStep 8888777 = 6666583) B6666583
theorem B6668801 : Blo 1754578 6668801 := bstep (se 2 (by rfl) ⟨2500800, by rfl⟩ : syracuseStep 6668801 = 5001601) B5001601
theorem B1974847 : Blo 1754578 1974847 := bstep (se 1 (by rfl) ⟨1481135, by rfl⟩ : syracuseStep 1974847 = 2962271) B2962271
theorem B3949127 : Blo 1754578 3949127 := bstep (se 1 (by rfl) ⟨2961845, by rfl⟩ : syracuseStep 3949127 = 5923691) B5923691
theorem B18989639 : Blo 1754578 18989639 := bstep (se 1 (by rfl) ⟨14242229, by rfl⟩ : syracuseStep 18989639 = 28484459) B28484459
theorem B3949163 : Blo 1754578 3949163 := bstep (se 1 (by rfl) ⟨2961872, by rfl⟩ : syracuseStep 3949163 = 5923745) B5923745
theorem B2810543 : Blo 1754578 2810543 := bstep (se 1 (by rfl) ⟨2107907, by rfl⟩ : syracuseStep 2810543 = 4215815) B4215815
theorem B6669287 : Blo 1754578 6669287 := bstep (se 1 (by rfl) ⟨5001965, by rfl⟩ : syracuseStep 6669287 = 10003931) B10003931
theorem B3949559 : Blo 1754578 3949559 := bstep (se 1 (by rfl) ⟨2962169, by rfl⟩ : syracuseStep 3949559 = 5924339) B5924339
theorem B4998287 : Blo 1754578 4998287 := bstep (se 1 (by rfl) ⟨3748715, by rfl⟩ : syracuseStep 4998287 = 7497431) B7497431
theorem B4998343 : Blo 1754578 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B4441331 : Blo 1754578 4441331 := bstep (se 1 (by rfl) ⟨3330998, by rfl⟩ : syracuseStep 4441331 = 6661997) B6661997
theorem B8889587 : Blo 1754578 8889587 := bstep (se 1 (by rfl) ⟨6667190, by rfl⟩ : syracuseStep 8889587 = 13334381) B13334381
theorem B5621035 : Blo 1754578 5621035 := bstep (se 1 (by rfl) ⟨4215776, by rfl⟩ : syracuseStep 5621035 = 8431553) B8431553
theorem B15000875 : Blo 1754578 15000875 := bstep (se 1 (by rfl) ⟨11250656, by rfl⟩ : syracuseStep 15000875 = 22501313) B22501313
theorem B3949919 : Blo 1754578 3949919 := bstep (se 1 (by rfl) ⟨2962439, by rfl⟩ : syracuseStep 3949919 = 5924879) B5924879
theorem B20039021 : Blo 1754578 20039021 := bstep (se 3 (by rfl) ⟨3757316, by rfl⟩ : syracuseStep 20039021 = 7514633) B7514633
theorem B2221435 : Blo 1754578 2221435 := bstep (se 1 (by rfl) ⟨1666076, by rfl⟩ : syracuseStep 2221435 = 3332153) B3332153
theorem B1975675 : Blo 1754578 1975675 := bstep (se 1 (by rfl) ⟨1481756, by rfl⟩ : syracuseStep 1975675 = 2963513) B2963513
theorem B16876943 : Blo 1754578 16876943 := bstep (se 1 (by rfl) ⟨12657707, by rfl⟩ : syracuseStep 16876943 = 25315415) B25315415
theorem B18974105 : Blo 1754578 18974105 := bstep (se 2 (by rfl) ⟨7115289, by rfl⟩ : syracuseStep 18974105 = 14230579) B14230579
theorem B5924285 : Blo 1754578 5924285 := bstep (se 3 (by rfl) ⟨1110803, by rfl⟩ : syracuseStep 5924285 = 2221607) B2221607
theorem B1754619 : Blo 1754578 1754619 := bstep (se 1 (by rfl) ⟨1315964, by rfl⟩ : syracuseStep 1754619 = 2631929) B2631929
theorem B1754687 : Blo 1754578 1754687 := bstep (se 1 (by rfl) ⟨1316015, by rfl⟩ : syracuseStep 1754687 = 2632031) B2632031
theorem B1754695 : Blo 1754578 1754695 := bstep (se 1 (by rfl) ⟨1316021, by rfl⟩ : syracuseStep 1754695 = 2632043) B2632043
theorem B2221663 : Blo 1754578 2221663 := bstep (se 1 (by rfl) ⟨1666247, by rfl⟩ : syracuseStep 2221663 = 3332495) B3332495
theorem B13338269 : Blo 1754578 13338269 := bstep (se 3 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 13338269 = 5001851) B5001851
theorem B4441787 : Blo 1754578 4441787 := bstep (se 1 (by rfl) ⟨3331340, by rfl⟩ : syracuseStep 4441787 = 6662681) B6662681
theorem B33760961 : Blo 1754578 33760961 := bstep (se 2 (by rfl) ⟨12660360, by rfl⟩ : syracuseStep 33760961 = 25320721) B25320721
theorem B1754847 : Blo 1754578 1754847 := bstep (se 1 (by rfl) ⟨1316135, by rfl⟩ : syracuseStep 1754847 = 2632271) B2632271
theorem B3950315 : Blo 1754578 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B1754927 : Blo 1754578 1754927 := bstep (se 1 (by rfl) ⟨1316195, by rfl⟩ : syracuseStep 1754927 = 2632391) B2632391
theorem B5924663 : Blo 1754578 5924663 := bstep (se 1 (by rfl) ⟨4443497, by rfl⟩ : syracuseStep 5924663 = 8886995) B8886995
theorem B56969027 : Blo 1754578 56969027 := bstep (se 1 (by rfl) ⟨42726770, by rfl⟩ : syracuseStep 56969027 = 85453541) B85453541
theorem B1976143 : Blo 1754578 1976143 := bstep (se 1 (by rfl) ⟨1482107, by rfl⟩ : syracuseStep 1976143 = 2964215) B2964215
theorem B3950441 : Blo 1754578 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B1755035 : Blo 1754578 1755035 := bstep (se 1 (by rfl) ⟨1316276, by rfl⟩ : syracuseStep 1755035 = 2632553) B2632553
theorem B1755087 : Blo 1754578 1755087 := bstep (se 1 (by rfl) ⟨1316315, by rfl⟩ : syracuseStep 1755087 = 2632631) B2632631
theorem B3164111 : Blo 1754578 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B1755111 : Blo 1754578 1755111 := bstep (se 1 (by rfl) ⟨1316333, by rfl⟩ : syracuseStep 1755111 = 2632667) B2632667
theorem B4442323 : Blo 1754578 4442323 := bstep (se 1 (by rfl) ⟨3331742, by rfl⟩ : syracuseStep 4442323 = 6663485) B6663485
theorem B5925149 : Blo 1754578 5925149 := bstep (se 3 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 5925149 = 2221931) B2221931
theorem B1755423 : Blo 1754578 1755423 := bstep (se 1 (by rfl) ⟨1316567, by rfl⟩ : syracuseStep 1755423 = 2633135) B2633135
theorem B1755483 : Blo 1754578 1755483 := bstep (se 1 (by rfl) ⟨1316612, by rfl⟩ : syracuseStep 1755483 = 2633225) B2633225
theorem B1755503 : Blo 1754578 1755503 := bstep (se 1 (by rfl) ⟨1316627, by rfl⟩ : syracuseStep 1755503 = 2633255) B2633255
theorem B2632103 : Blo 1754578 2632103 := bstep (se 1 (by rfl) ⟨1974077, by rfl⟩ : syracuseStep 2632103 = 3948155) B3948155
theorem B1755559 : Blo 1754578 1755559 := bstep (se 1 (by rfl) ⟨1316669, by rfl⟩ : syracuseStep 1755559 = 2633339) B2633339
theorem B2632187 : Blo 1754578 2632187 := bstep (se 1 (by rfl) ⟨1974140, by rfl⟩ : syracuseStep 2632187 = 3948281) B3948281
theorem B1755643 : Blo 1754578 1755643 := bstep (se 1 (by rfl) ⟨1316732, by rfl⟩ : syracuseStep 1755643 = 2633465) B2633465
theorem B1755711 : Blo 1754578 1755711 := bstep (se 1 (by rfl) ⟨1316783, by rfl⟩ : syracuseStep 1755711 = 2633567) B2633567
theorem B1755719 : Blo 1754578 1755719 := bstep (se 1 (by rfl) ⟨1316789, by rfl⟩ : syracuseStep 1755719 = 2633579) B2633579
theorem B8432207 : Blo 1754578 8432207 := bstep (se 1 (by rfl) ⟨6324155, by rfl⟩ : syracuseStep 8432207 = 12648311) B12648311
theorem B25660003 : Blo 1754578 25660003 := bstep (se 1 (by rfl) ⟨19245002, by rfl⟩ : syracuseStep 25660003 = 38490005) B38490005
theorem B2632313 : Blo 1754578 2632313 := bstep (se 2 (by rfl) ⟨987117, by rfl⟩ : syracuseStep 2632313 = 1974235) B1974235
theorem B2632367 : Blo 1754578 2632367 := bstep (se 1 (by rfl) ⟨1974275, by rfl⟩ : syracuseStep 2632367 = 3948551) B3948551
theorem B3951287 : Blo 1754578 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B2632415 : Blo 1754578 2632415 := bstep (se 1 (by rfl) ⟨1974311, by rfl⟩ : syracuseStep 2632415 = 3948623) B3948623
theorem B1755871 : Blo 1754578 1755871 := bstep (se 1 (by rfl) ⟨1316903, by rfl⟩ : syracuseStep 1755871 = 2633807) B2633807
theorem B4999927 : Blo 1754578 4999927 := bstep (se 1 (by rfl) ⟨3749945, by rfl⟩ : syracuseStep 4999927 = 7499891) B7499891
theorem B1755951 : Blo 1754578 1755951 := bstep (se 1 (by rfl) ⟨1316963, by rfl⟩ : syracuseStep 1755951 = 2633927) B2633927
theorem B2108215 : Blo 1754578 2108215 := bstep (se 1 (by rfl) ⟨1581161, by rfl⟩ : syracuseStep 2108215 = 3162323) B3162323
theorem B2222903 : Blo 1754578 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B3951503 : Blo 1754578 3951503 := bstep (se 1 (by rfl) ⟨2963627, by rfl⟩ : syracuseStep 3951503 = 5927255) B5927255
theorem B1756059 : Blo 1754578 1756059 := bstep (se 1 (by rfl) ⟨1317044, by rfl⟩ : syracuseStep 1756059 = 2634089) B2634089
theorem B1756111 : Blo 1754578 1756111 := bstep (se 1 (by rfl) ⟨1317083, by rfl⟩ : syracuseStep 1756111 = 2634167) B2634167
theorem B2223055 : Blo 1754578 2223055 := bstep (se 1 (by rfl) ⟨1667291, by rfl⟩ : syracuseStep 2223055 = 3334583) B3334583
theorem B2632679 : Blo 1754578 2632679 := bstep (se 1 (by rfl) ⟨1974509, by rfl⟩ : syracuseStep 2632679 = 3949019) B3949019
theorem B1756135 : Blo 1754578 1756135 := bstep (se 1 (by rfl) ⟨1317101, by rfl⟩ : syracuseStep 1756135 = 2634203) B2634203
theorem B44969093 : Blo 1754578 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B4443275 : Blo 1754578 4443275 := bstep (se 1 (by rfl) ⟨3332456, by rfl⟩ : syracuseStep 4443275 = 6664913) B6664913
theorem B8891531 : Blo 1754578 8891531 := bstep (se 1 (by rfl) ⟨6668648, by rfl⟩ : syracuseStep 8891531 = 13337297) B13337297
theorem B4746383 : Blo 1754578 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B2632937 : Blo 1754578 2632937 := bstep (se 2 (by rfl) ⟨987351, by rfl⟩ : syracuseStep 2632937 = 1974703) B1974703
theorem B6663455 : Blo 1754578 6663455 := bstep (se 1 (by rfl) ⟨4997591, by rfl⟩ : syracuseStep 6663455 = 9995183) B9995183
theorem B2632991 : Blo 1754578 2632991 := bstep (se 1 (by rfl) ⟨1974743, by rfl⟩ : syracuseStep 2632991 = 3949487) B3949487
theorem B5926175 : Blo 1754578 5926175 := bstep (se 1 (by rfl) ⟨4444631, by rfl⟩ : syracuseStep 5926175 = 8889263) B8889263
theorem B1756447 : Blo 1754578 1756447 := bstep (se 1 (by rfl) ⟨1317335, by rfl⟩ : syracuseStep 1756447 = 2634671) B2634671
theorem B1756507 : Blo 1754578 1756507 := bstep (se 1 (by rfl) ⟨1317380, by rfl⟩ : syracuseStep 1756507 = 2634761) B2634761
theorem B1756527 : Blo 1754578 1756527 := bstep (se 1 (by rfl) ⟨1317395, by rfl⟩ : syracuseStep 1756527 = 2634791) B2634791
theorem B8883593 : Blo 1754578 8883593 := bstep (se 2 (by rfl) ⟨3331347, by rfl⟩ : syracuseStep 8883593 = 6662695) B6662695
theorem B2633159 : Blo 1754578 2633159 := bstep (se 1 (by rfl) ⟨1974869, by rfl⟩ : syracuseStep 2633159 = 3949739) B3949739
theorem B4443731 : Blo 1754578 4443731 := bstep (se 1 (by rfl) ⟨3332798, by rfl⟩ : syracuseStep 4443731 = 6665597) B6665597
theorem B3952223 : Blo 1754578 3952223 := bstep (se 1 (by rfl) ⟨2964167, by rfl⟩ : syracuseStep 3952223 = 5928335) B5928335
theorem B2961083 : Blo 1754578 2961083 := bstep (se 1 (by rfl) ⟨2220812, by rfl⟩ : syracuseStep 2961083 = 4441625) B4441625
theorem B40529645 : Blo 1754578 40529645 := bstep (se 3 (by rfl) ⟨7599308, by rfl⟩ : syracuseStep 40529645 = 15198617) B15198617
theorem B2633513 : Blo 1754578 2633513 := bstep (se 2 (by rfl) ⟨987567, by rfl⟩ : syracuseStep 2633513 = 1975135) B1975135
theorem B16879403 : Blo 1754578 16879403 := bstep (se 1 (by rfl) ⟨12659552, by rfl⟩ : syracuseStep 16879403 = 25319105) B25319105
theorem B2633519 : Blo 1754578 2633519 := bstep (se 1 (by rfl) ⟨1975139, by rfl⟩ : syracuseStep 2633519 = 3950279) B3950279
theorem B16871489 : Blo 1754578 16871489 := bstep (se 2 (by rfl) ⟨6326808, by rfl⟩ : syracuseStep 16871489 = 12653617) B12653617
theorem B73035857 : Blo 1754578 73035857 := bstep (se 2 (by rfl) ⟨27388446, by rfl⟩ : syracuseStep 73035857 = 54776893) B54776893
theorem B2633993 : Blo 1754578 2633993 := bstep (se 2 (by rfl) ⟨987747, by rfl⟩ : syracuseStep 2633993 = 1975495) B1975495
theorem B3748169 : Blo 1754578 3748169 := bstep (se 2 (by rfl) ⟨1405563, by rfl⟩ : syracuseStep 3748169 = 2811127) B2811127
theorem B2634095 : Blo 1754578 2634095 := bstep (se 1 (by rfl) ⟨1975571, by rfl⟩ : syracuseStep 2634095 = 3951143) B3951143
theorem B4444591 : Blo 1754578 4444591 := bstep (se 1 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 4444591 = 6666887) B6666887
theorem B17109467 : Blo 1754578 17109467 := bstep (se 1 (by rfl) ⟨12832100, by rfl⟩ : syracuseStep 17109467 = 25664201) B25664201
theorem B136770029 : Blo 1754578 136770029 := bstep (se 3 (by rfl) ⟨25644380, by rfl⟩ : syracuseStep 136770029 = 51288761) B51288761
theorem B56947225 : Blo 1754578 56947225 := bstep (se 2 (by rfl) ⟨21355209, by rfl⟩ : syracuseStep 56947225 = 42710419) B42710419
theorem B2634311 : Blo 1754578 2634311 := bstep (se 1 (by rfl) ⟨1975733, by rfl⟩ : syracuseStep 2634311 = 3951467) B3951467
theorem B11252321 : Blo 1754578 11252321 := bstep (se 2 (by rfl) ⟨4219620, by rfl⟩ : syracuseStep 11252321 = 8439241) B8439241
theorem B2634347 : Blo 1754578 2634347 := bstep (se 1 (by rfl) ⟨1975760, by rfl⟩ : syracuseStep 2634347 = 3951521) B3951521
theorem B8884889 : Blo 1754578 8884889 := bstep (se 2 (by rfl) ⟨3331833, by rfl⟩ : syracuseStep 8884889 = 6663667) B6663667
theorem B4444895 : Blo 1754578 4444895 := bstep (se 1 (by rfl) ⟨3333671, by rfl⟩ : syracuseStep 4444895 = 6667343) B6667343
theorem B8434475 : Blo 1754578 8434475 := bstep (se 1 (by rfl) ⟨6325856, by rfl⟩ : syracuseStep 8434475 = 12651713) B12651713
theorem B2634575 : Blo 1754578 2634575 := bstep (se 1 (by rfl) ⟨1975931, by rfl⟩ : syracuseStep 2634575 = 3951863) B3951863
theorem B5624777 : Blo 1754578 5624777 := bstep (se 2 (by rfl) ⟨2109291, by rfl⟩ : syracuseStep 5624777 = 4218583) B4218583
theorem B19993553 : Blo 1754578 19993553 := bstep (se 2 (by rfl) ⟨7497582, by rfl⟩ : syracuseStep 19993553 = 14995165) B14995165
theorem B11563985 : Blo 1754578 11563985 := bstep (se 2 (by rfl) ⟨4336494, by rfl⟩ : syracuseStep 11563985 = 8672989) B8672989
theorem B5624957 : Blo 1754578 5624957 := bstep (se 3 (by rfl) ⟨1054679, by rfl⟩ : syracuseStep 5624957 = 2109359) B2109359
theorem B7115975 : Blo 1754578 7115975 := bstep (se 1 (by rfl) ⟨5336981, by rfl⟩ : syracuseStep 7115975 = 10673963) B10673963
theorem B2962811 : Blo 1754578 2962811 := bstep (se 1 (by rfl) ⟨2222108, by rfl⟩ : syracuseStep 2962811 = 4444217) B4444217
theorem B4445563 : Blo 1754578 4445563 := bstep (se 1 (by rfl) ⟨3334172, by rfl⟩ : syracuseStep 4445563 = 6668345) B6668345
theorem B6665611 : Blo 1754578 6665611 := bstep (se 1 (by rfl) ⟨4999208, by rfl⟩ : syracuseStep 6665611 = 9998417) B9998417
theorem B5625227 : Blo 1754578 5625227 := bstep (se 1 (by rfl) ⟨4218920, by rfl⟩ : syracuseStep 5625227 = 8437841) B8437841
theorem B12006893 : Blo 1754578 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B3331667 : Blo 1754578 3331667 := bstep (se 1 (by rfl) ⟨2498750, by rfl⟩ : syracuseStep 3331667 = 4997501) B4997501
theorem B6665885 : Blo 1754578 6665885 := bstep (se 3 (by rfl) ⟨1249853, by rfl⟩ : syracuseStep 6665885 = 2499707) B2499707
theorem B10000057 : Blo 1754578 10000057 := bstep (se 2 (by rfl) ⟨3750021, by rfl⟩ : syracuseStep 10000057 = 7500043) B7500043
theorem B6665915 : Blo 1754578 6665915 := bstep (se 1 (by rfl) ⟨4999436, by rfl⟩ : syracuseStep 6665915 = 9998873) B9998873
theorem B4445999 : Blo 1754578 4445999 := bstep (se 1 (by rfl) ⟨3334499, by rfl⟩ : syracuseStep 4445999 = 6668999) B6668999
theorem B7116751 : Blo 1754578 7116751 := bstep (se 1 (by rfl) ⟨5337563, by rfl⟩ : syracuseStep 7116751 = 10675127) B10675127
theorem B9492461 : Blo 1754578 9492461 := bstep (se 3 (by rfl) ⟨1779836, by rfl⟩ : syracuseStep 9492461 = 3559673) B3559673
theorem B7501805 : Blo 1754578 7501805 := bstep (se 3 (by rfl) ⟨1406588, by rfl⟩ : syracuseStep 7501805 = 2813177) B2813177
theorem B8435897 : Blo 1754578 8435897 := bstep (se 2 (by rfl) ⟨3163461, by rfl⟩ : syracuseStep 8435897 = 6326923) B6326923
theorem B2963803 : Blo 1754578 2963803 := bstep (se 1 (by rfl) ⟨2222852, by rfl⟩ : syracuseStep 2963803 = 4445705) B4445705
theorem B8886671 : Blo 1754578 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B266951189 : Blo 1754578 266951189 := bstep (se 6 (by rfl) ⟨6256668, by rfl⟩ : syracuseStep 266951189 = 12513337) B12513337
theorem B2251487 : Blo 1754578 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B20003759 : Blo 1754578 20003759 := bstep (se 1 (by rfl) ⟨15002819, by rfl⟩ : syracuseStep 20003759 = 30005639) B30005639
theorem B3800027 : Blo 1754578 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B5626867 : Blo 1754578 5626867 := bstep (se 1 (by rfl) ⟨4220150, by rfl⟩ : syracuseStep 5626867 = 8440301) B8440301
theorem B9493627 : Blo 1754578 9493627 := bstep (se 1 (by rfl) ⟨7120220, by rfl⟩ : syracuseStep 9493627 = 14240441) B14240441
theorem B4627655 : Blo 1754578 4627655 := bstep (se 1 (by rfl) ⟨3470741, by rfl⟩ : syracuseStep 4627655 = 6941483) B6941483
theorem B18988253 : Blo 1754578 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B6413687 : Blo 1754578 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B3751355 : Blo 1754578 3751355 := bstep (se 1 (by rfl) ⟨2813516, by rfl⟩ : syracuseStep 3751355 = 5627033) B5627033
theorem B3947975 : Blo 1754578 3947975 := bstep (se 1 (by rfl) ⟨2960981, by rfl⟩ : syracuseStep 3947975 = 5921963) B5921963
theorem B50609609 : Blo 1754578 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B8437241 : Blo 1754578 8437241 := bstep (se 2 (by rfl) ⟨3163965, by rfl⟩ : syracuseStep 8437241 = 6327931) B6327931
theorem B6667859 : Blo 1754578 6667859 := bstep (se 1 (by rfl) ⟨5000894, by rfl⟩ : syracuseStep 6667859 = 10001789) B10001789
theorem B4996703 : Blo 1754578 4996703 := bstep (se 1 (by rfl) ⟨3747527, by rfl⟩ : syracuseStep 4996703 = 7495055) B7495055
theorem B3333793 : Blo 1754578 3333793 := bstep (se 2 (by rfl) ⟨1250172, by rfl⟩ : syracuseStep 3333793 = 2500345) B2500345
theorem B1973983 : Blo 1754578 1973983 := bstep (se 1 (by rfl) ⟨1480487, by rfl⟩ : syracuseStep 1973983 = 2960975) B2960975
theorem B3948335 : Blo 1754578 3948335 := bstep (se 1 (by rfl) ⟨2961251, by rfl⟩ : syracuseStep 3948335 = 5922503) B5922503
theorem B21364553 : Blo 1754578 21364553 := bstep (se 2 (by rfl) ⟨8011707, by rfl⟩ : syracuseStep 21364553 = 16023415) B16023415
theorem B4997159 : Blo 1754578 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B11247659 : Blo 1754578 11247659 := bstep (se 1 (by rfl) ⟨8435744, by rfl⟩ : syracuseStep 11247659 = 16871489) B16871489
theorem B25296961 : Blo 1754578 25296961 := bstep (se 2 (by rfl) ⟨9486360, by rfl⟩ : syracuseStep 25296961 = 18972721) B18972721
theorem B2498779 : Blo 1754578 2498779 := bstep (se 1 (by rfl) ⟨1874084, by rfl⟩ : syracuseStep 2498779 = 3748169) B3748169
theorem B5923097 : Blo 1754578 5923097 := bstep (se 2 (by rfl) ⟨2221161, by rfl⟩ : syracuseStep 5923097 = 4442323) B4442323
theorem B5923259 : Blo 1754578 5923259 := bstep (se 1 (by rfl) ⟨4442444, by rfl⟩ : syracuseStep 5923259 = 8884889) B8884889
theorem B13329035 : Blo 1754578 13329035 := bstep (se 1 (by rfl) ⟨9996776, by rfl⟩ : syracuseStep 13329035 = 19993553) B19993553
theorem B7709323 : Blo 1754578 7709323 := bstep (se 1 (by rfl) ⟨5781992, by rfl⟩ : syracuseStep 7709323 = 11563985) B11563985
theorem B4743983 : Blo 1754578 4743983 := bstep (se 1 (by rfl) ⟨3557987, by rfl⟩ : syracuseStep 4743983 = 7115975) B7115975
theorem B1975207 : Blo 1754578 1975207 := bstep (se 1 (by rfl) ⟨1481405, by rfl⟩ : syracuseStep 1975207 = 2962811) B2962811
theorem B12649403 : Blo 1754578 12649403 := bstep (se 1 (by rfl) ⟨9487052, by rfl⟩ : syracuseStep 12649403 = 18974105) B18974105
theorem B3949523 : Blo 1754578 3949523 := bstep (se 1 (by rfl) ⟨2962142, by rfl⟩ : syracuseStep 3949523 = 5924285) B5924285
theorem B8004595 : Blo 1754578 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B2221111 : Blo 1754578 2221111 := bstep (se 1 (by rfl) ⟨1665833, by rfl⟩ : syracuseStep 2221111 = 3331667) B3331667
theorem B2810953 : Blo 1754578 2810953 := bstep (se 2 (by rfl) ⟨1054107, by rfl⟩ : syracuseStep 2810953 = 2108215) B2108215
theorem B3949775 : Blo 1754578 3949775 := bstep (se 1 (by rfl) ⟨2962331, by rfl⟩ : syracuseStep 3949775 = 5924663) B5924663
theorem B37979351 : Blo 1754578 37979351 := bstep (se 1 (by rfl) ⟨28484513, by rfl⟩ : syracuseStep 37979351 = 56969027) B56969027
theorem B12658169 : Blo 1754578 12658169 := bstep (se 2 (by rfl) ⟨4746813, by rfl⟩ : syracuseStep 12658169 = 9493627) B9493627
theorem B3950099 : Blo 1754578 3950099 := bstep (se 1 (by rfl) ⟨2962574, by rfl⟩ : syracuseStep 3950099 = 5925149) B5925149
theorem B5924447 : Blo 1754578 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B1754735 : Blo 1754578 1754735 := bstep (se 1 (by rfl) ⟨1316051, by rfl⟩ : syracuseStep 1754735 = 2632103) B2632103
theorem B1754791 : Blo 1754578 1754791 := bstep (se 1 (by rfl) ⟨1316093, by rfl⟩ : syracuseStep 1754791 = 2632187) B2632187
theorem B5621471 : Blo 1754578 5621471 := bstep (se 1 (by rfl) ⟨4216103, by rfl⟩ : syracuseStep 5621471 = 8432207) B8432207
theorem B1754875 : Blo 1754578 1754875 := bstep (se 1 (by rfl) ⟨1316156, by rfl⟩ : syracuseStep 1754875 = 2632313) B2632313
theorem B1754911 : Blo 1754578 1754911 := bstep (se 1 (by rfl) ⟨1316183, by rfl⟩ : syracuseStep 1754911 = 2632367) B2632367
theorem B1754943 : Blo 1754578 1754943 := bstep (se 1 (by rfl) ⟨1316207, by rfl⟩ : syracuseStep 1754943 = 2632415) B2632415
theorem B2533351 : Blo 1754578 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B1755119 : Blo 1754578 1755119 := bstep (se 1 (by rfl) ⟨1316339, by rfl⟩ : syracuseStep 1755119 = 2632679) B2632679
theorem B3164255 : Blo 1754578 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B12658835 : Blo 1754578 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B1755291 : Blo 1754578 1755291 := bstep (se 1 (by rfl) ⟨1316468, by rfl⟩ : syracuseStep 1755291 = 2632937) B2632937
theorem B4442303 : Blo 1754578 4442303 := bstep (se 1 (by rfl) ⟨3331727, by rfl⟩ : syracuseStep 4442303 = 6663455) B6663455
theorem B1755327 : Blo 1754578 1755327 := bstep (se 1 (by rfl) ⟨1316495, by rfl⟩ : syracuseStep 1755327 = 2632991) B2632991
theorem B3950783 : Blo 1754578 3950783 := bstep (se 1 (by rfl) ⟨2963087, by rfl⟩ : syracuseStep 3950783 = 5926175) B5926175
theorem B2500903 : Blo 1754578 2500903 := bstep (se 1 (by rfl) ⟨1875677, by rfl⟩ : syracuseStep 2500903 = 3751355) B3751355
theorem B2631977 : Blo 1754578 2631977 := bstep (se 2 (by rfl) ⟨986991, by rfl⟩ : syracuseStep 2631977 = 1973983) B1973983
theorem B2631983 : Blo 1754578 2631983 := bstep (se 1 (by rfl) ⟨1973987, by rfl⟩ : syracuseStep 2631983 = 3947975) B3947975
theorem B1755439 : Blo 1754578 1755439 := bstep (se 1 (by rfl) ⟨1316579, by rfl⟩ : syracuseStep 1755439 = 2633159) B2633159
theorem B27019763 : Blo 1754578 27019763 := bstep (se 1 (by rfl) ⟨20264822, by rfl⟩ : syracuseStep 27019763 = 40529645) B40529645
theorem B1755675 : Blo 1754578 1755675 := bstep (se 1 (by rfl) ⟨1316756, by rfl⟩ : syracuseStep 1755675 = 2633513) B2633513
theorem B2632223 : Blo 1754578 2632223 := bstep (se 1 (by rfl) ⟨1974167, by rfl⟩ : syracuseStep 2632223 = 3948335) B3948335
theorem B1755679 : Blo 1754578 1755679 := bstep (se 1 (by rfl) ⟨1316759, by rfl⟩ : syracuseStep 1755679 = 2633519) B2633519
theorem B9489001 : Blo 1754578 9489001 := bstep (se 2 (by rfl) ⟨3558375, by rfl⟩ : syracuseStep 9489001 = 7116751) B7116751
theorem B1755995 : Blo 1754578 1755995 := bstep (se 1 (by rfl) ⟨1316996, by rfl⟩ : syracuseStep 1755995 = 2633993) B2633993
theorem B2632607 : Blo 1754578 2632607 := bstep (se 1 (by rfl) ⟨1974455, by rfl⟩ : syracuseStep 2632607 = 3948911) B3948911
theorem B1756063 : Blo 1754578 1756063 := bstep (se 1 (by rfl) ⟨1317047, by rfl⟩ : syracuseStep 1756063 = 2634095) B2634095
theorem B2632655 : Blo 1754578 2632655 := bstep (se 1 (by rfl) ⟨1974491, by rfl⟩ : syracuseStep 2632655 = 3948983) B3948983
theorem B5925851 : Blo 1754578 5925851 := bstep (se 1 (by rfl) ⟨4444388, by rfl⟩ : syracuseStep 5925851 = 8888777) B8888777
theorem B11406311 : Blo 1754578 11406311 := bstep (se 1 (by rfl) ⟨8554733, by rfl⟩ : syracuseStep 11406311 = 17109467) B17109467
theorem B91180019 : Blo 1754578 91180019 := bstep (se 1 (by rfl) ⟨68385014, by rfl⟩ : syracuseStep 91180019 = 136770029) B136770029
theorem B2632745 : Blo 1754578 2632745 := bstep (se 2 (by rfl) ⟨987279, by rfl⟩ : syracuseStep 2632745 = 1974559) B1974559
theorem B2632751 : Blo 1754578 2632751 := bstep (se 1 (by rfl) ⟨1974563, by rfl⟩ : syracuseStep 2632751 = 3949127) B3949127
theorem B1756207 : Blo 1754578 1756207 := bstep (se 1 (by rfl) ⟨1317155, by rfl⟩ : syracuseStep 1756207 = 2634311) B2634311
theorem B12659759 : Blo 1754578 12659759 := bstep (se 1 (by rfl) ⟨9494819, by rfl⟩ : syracuseStep 12659759 = 18989639) B18989639
theorem B2632775 : Blo 1754578 2632775 := bstep (se 1 (by rfl) ⟨1974581, by rfl⟩ : syracuseStep 2632775 = 3949163) B3949163
theorem B1756231 : Blo 1754578 1756231 := bstep (se 1 (by rfl) ⟨1317173, by rfl⟩ : syracuseStep 1756231 = 2634347) B2634347
theorem B3951737 : Blo 1754578 3951737 := bstep (se 2 (by rfl) ⟨1481901, by rfl⟩ : syracuseStep 3951737 = 2963803) B2963803
theorem B5622983 : Blo 1754578 5622983 := bstep (se 1 (by rfl) ⟨4217237, by rfl⟩ : syracuseStep 5622983 = 8434475) B8434475
theorem B1756383 : Blo 1754578 1756383 := bstep (se 1 (by rfl) ⟨1317287, by rfl⟩ : syracuseStep 1756383 = 2634575) B2634575
theorem B5926121 : Blo 1754578 5926121 := bstep (se 2 (by rfl) ⟨2222295, by rfl⟩ : syracuseStep 5926121 = 4444591) B4444591
theorem B2633039 : Blo 1754578 2633039 := bstep (se 1 (by rfl) ⟨1974779, by rfl⟩ : syracuseStep 2633039 = 3949559) B3949559
theorem B2633129 : Blo 1754578 2633129 := bstep (se 2 (by rfl) ⟨987423, by rfl⟩ : syracuseStep 2633129 = 1974847) B1974847
theorem B34213337 : Blo 1754578 34213337 := bstep (se 2 (by rfl) ⟨12830001, by rfl⟩ : syracuseStep 34213337 = 25660003) B25660003
theorem B2960887 : Blo 1754578 2960887 := bstep (se 1 (by rfl) ⟨2220665, by rfl⟩ : syracuseStep 2960887 = 4441331) B4441331
theorem B5926391 : Blo 1754578 5926391 := bstep (se 1 (by rfl) ⟨4444793, by rfl⟩ : syracuseStep 5926391 = 8889587) B8889587
theorem B2633279 : Blo 1754578 2633279 := bstep (se 1 (by rfl) ⟨1974959, by rfl⟩ : syracuseStep 2633279 = 3949919) B3949919
theorem B11251295 : Blo 1754578 11251295 := bstep (se 1 (by rfl) ⟨8438471, by rfl⟩ : syracuseStep 11251295 = 16876943) B16876943
theorem B4443923 : Blo 1754578 4443923 := bstep (se 1 (by rfl) ⟨3332942, by rfl⟩ : syracuseStep 4443923 = 6665885) B6665885
theorem B8892179 : Blo 1754578 8892179 := bstep (se 1 (by rfl) ⟨6669134, by rfl⟩ : syracuseStep 8892179 = 13338269) B13338269
theorem B2961191 : Blo 1754578 2961191 := bstep (se 1 (by rfl) ⟨2220893, by rfl⟩ : syracuseStep 2961191 = 4441787) B4441787
theorem B4443943 : Blo 1754578 4443943 := bstep (se 1 (by rfl) ⟨3332957, by rfl⟩ : syracuseStep 4443943 = 6665915) B6665915
theorem B22507307 : Blo 1754578 22507307 := bstep (se 1 (by rfl) ⟨16880480, by rfl⟩ : syracuseStep 22507307 = 33760961) B33760961
theorem B2633543 : Blo 1754578 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B2633627 : Blo 1754578 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B2109407 : Blo 1754578 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B22499309 : Blo 1754578 22499309 := bstep (se 3 (by rfl) ⟨4218620, by rfl⟩ : syracuseStep 22499309 = 8437241) B8437241
theorem B6328307 : Blo 1754578 6328307 := bstep (se 1 (by rfl) ⟨4746230, by rfl⟩ : syracuseStep 6328307 = 9492461) B9492461
theorem B5001203 : Blo 1754578 5001203 := bstep (se 1 (by rfl) ⟨3750902, by rfl⟩ : syracuseStep 5001203 = 7501805) B7501805
theorem B5623931 : Blo 1754578 5623931 := bstep (se 1 (by rfl) ⟨4217948, by rfl⟩ : syracuseStep 5623931 = 8435897) B8435897
theorem B6664457 : Blo 1754578 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B177967459 : Blo 1754578 177967459 := bstep (se 1 (by rfl) ⟨133475594, by rfl⟩ : syracuseStep 177967459 = 266951189) B266951189
theorem B2634191 : Blo 1754578 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B2961913 : Blo 1754578 2961913 := bstep (se 2 (by rfl) ⟨1110717, by rfl⟩ : syracuseStep 2961913 = 2221435) B2221435
theorem B2634233 : Blo 1754578 2634233 := bstep (se 2 (by rfl) ⟨987837, by rfl⟩ : syracuseStep 2634233 = 1975675) B1975675
theorem B5927417 : Blo 1754578 5927417 := bstep (se 2 (by rfl) ⟨2222781, by rfl⟩ : syracuseStep 5927417 = 4445563) B4445563
theorem B2634335 : Blo 1754578 2634335 := bstep (se 1 (by rfl) ⟨1975751, by rfl⟩ : syracuseStep 2634335 = 3951503) B3951503
theorem B29979395 : Blo 1754578 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B2962183 : Blo 1754578 2962183 := bstep (se 1 (by rfl) ⟨2221637, by rfl⟩ : syracuseStep 2962183 = 4443275) B4443275
theorem B5927687 : Blo 1754578 5927687 := bstep (se 1 (by rfl) ⟨4445765, by rfl⟩ : syracuseStep 5927687 = 8891531) B8891531
theorem B2962217 : Blo 1754578 2962217 := bstep (se 2 (by rfl) ⟨1110831, by rfl⟩ : syracuseStep 2962217 = 2221663) B2221663
theorem B3085103 : Blo 1754578 3085103 := bstep (se 1 (by rfl) ⟨2313827, by rfl⟩ : syracuseStep 3085103 = 4627655) B4627655
theorem B5927741 : Blo 1754578 5927741 := bstep (se 3 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 5927741 = 2222903) B2222903
theorem B4445057 : Blo 1754578 4445057 := bstep (se 2 (by rfl) ⟨1666896, by rfl⟩ : syracuseStep 4445057 = 3333793) B3333793
theorem B13333409 : Blo 1754578 13333409 := bstep (se 2 (by rfl) ⟨5000028, by rfl⟩ : syracuseStep 13333409 = 10000057) B10000057
theorem B33739739 : Blo 1754578 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B2962487 : Blo 1754578 2962487 := bstep (se 1 (by rfl) ⟨2221865, by rfl⟩ : syracuseStep 2962487 = 4443731) B4443731
theorem B4445239 : Blo 1754578 4445239 := bstep (se 1 (by rfl) ⟨3333929, by rfl⟩ : syracuseStep 4445239 = 6667859) B6667859
theorem B3331135 : Blo 1754578 3331135 := bstep (se 1 (by rfl) ⟨2498351, by rfl⟩ : syracuseStep 3331135 = 4996703) B4996703
theorem B2634815 : Blo 1754578 2634815 := bstep (se 1 (by rfl) ⟨1976111, by rfl⟩ : syracuseStep 2634815 = 3952223) B3952223
theorem B2634857 : Blo 1754578 2634857 := bstep (se 2 (by rfl) ⟨988071, by rfl⟩ : syracuseStep 2634857 = 1976143) B1976143
theorem B11252935 : Blo 1754578 11252935 := bstep (se 1 (by rfl) ⟨8439701, by rfl⟩ : syracuseStep 11252935 = 16879403) B16879403
theorem B14243035 : Blo 1754578 14243035 := bstep (se 1 (by rfl) ⟨10682276, by rfl⟩ : syracuseStep 14243035 = 21364553) B21364553
theorem B48690571 : Blo 1754578 48690571 := bstep (se 1 (by rfl) ⟨36517928, by rfl⟩ : syracuseStep 48690571 = 73035857) B73035857
theorem B4445867 : Blo 1754578 4445867 := bstep (se 1 (by rfl) ⟨3334400, by rfl⟩ : syracuseStep 4445867 = 6668801) B6668801
theorem B7501547 : Blo 1754578 7501547 := bstep (se 1 (by rfl) ⟨5626160, by rfl⟩ : syracuseStep 7501547 = 11252321) B11252321
theorem B2963263 : Blo 1754578 2963263 := bstep (se 1 (by rfl) ⟨2222447, by rfl⟩ : syracuseStep 2963263 = 4444895) B4444895
theorem B3749851 : Blo 1754578 3749851 := bstep (se 1 (by rfl) ⟨2812388, by rfl⟩ : syracuseStep 3749851 = 5624777) B5624777
theorem B4446191 : Blo 1754578 4446191 := bstep (se 1 (by rfl) ⟨3334643, by rfl⟩ : syracuseStep 4446191 = 6669287) B6669287
theorem B75929633 : Blo 1754578 75929633 := bstep (se 2 (by rfl) ⟨28473612, by rfl⟩ : syracuseStep 75929633 = 56947225) B56947225
theorem B3749971 : Blo 1754578 3749971 := bstep (se 1 (by rfl) ⟨2812478, by rfl⟩ : syracuseStep 3749971 = 5624957) B5624957
theorem B3332191 : Blo 1754578 3332191 := bstep (se 1 (by rfl) ⟨2499143, by rfl⟩ : syracuseStep 3332191 = 4998287) B4998287
theorem B10000583 : Blo 1754578 10000583 := bstep (se 1 (by rfl) ⟨7500437, by rfl⟩ : syracuseStep 10000583 = 15000875) B15000875
theorem B13359347 : Blo 1754578 13359347 := bstep (se 1 (by rfl) ⟨10019510, by rfl⟩ : syracuseStep 13359347 = 20039021) B20039021
theorem B3750151 : Blo 1754578 3750151 := bstep (se 1 (by rfl) ⟨2812613, by rfl⟩ : syracuseStep 3750151 = 5625227) B5625227
theorem B6666569 : Blo 1754578 6666569 := bstep (se 2 (by rfl) ⟨2499963, by rfl⟩ : syracuseStep 6666569 = 4999927) B4999927
theorem B2963999 : Blo 1754578 2963999 := bstep (se 1 (by rfl) ⟨2222999, by rfl⟩ : syracuseStep 2963999 = 4445999) B4445999
theorem B2964073 : Blo 1754578 2964073 := bstep (se 2 (by rfl) ⟨1111527, by rfl⟩ : syracuseStep 2964073 = 2223055) B2223055
theorem B7502489 : Blo 1754578 7502489 := bstep (se 2 (by rfl) ⟨2813433, by rfl⟩ : syracuseStep 7502489 = 5626867) B5626867
theorem B7494713 : Blo 1754578 7494713 := bstep (se 2 (by rfl) ⟨2810517, by rfl⟩ : syracuseStep 7494713 = 5621035) B5621035
theorem B7494781 : Blo 1754578 7494781 := bstep (se 3 (by rfl) ⟨1405271, by rfl⟩ : syracuseStep 7494781 = 2810543) B2810543
theorem B8887481 : Blo 1754578 8887481 := bstep (se 2 (by rfl) ⟨3332805, by rfl⟩ : syracuseStep 8887481 = 6665611) B6665611
theorem B6003965 : Blo 1754578 6003965 := bstep (se 3 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 6003965 = 2251487) B2251487
theorem B13335839 : Blo 1754578 13335839 := bstep (se 1 (by rfl) ⟨10001879, by rfl⟩ : syracuseStep 13335839 = 20003759) B20003759
theorem B4275791 : Blo 1754578 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B5922395 : Blo 1754578 5922395 := bstep (se 1 (by rfl) ⟨4441796, by rfl⟩ : syracuseStep 5922395 = 8883593) B8883593
theorem B1974055 : Blo 1754578 1974055 := bstep (se 1 (by rfl) ⟨1480541, by rfl⟩ : syracuseStep 1974055 = 2961083) B2961083
theorem B3948731 : Blo 1754578 3948731 := bstep (se 1 (by rfl) ⟨2961548, by rfl⟩ : syracuseStep 3948731 = 5923097) B5923097
theorem B3948839 : Blo 1754578 3948839 := bstep (se 1 (by rfl) ⟨2961629, by rfl⟩ : syracuseStep 3948839 = 5923259) B5923259
theorem B14991749 : Blo 1754578 14991749 := bstep (se 4 (by rfl) ⟨1405476, by rfl⟩ : syracuseStep 14991749 = 2810953) B2810953
theorem B3334537 : Blo 1754578 3334537 := bstep (se 2 (by rfl) ⟨1250451, by rfl⟩ : syracuseStep 3334537 = 2500903) B2500903
theorem B237289945 : Blo 1754578 237289945 := bstep (se 2 (by rfl) ⟨88983729, by rfl⟩ : syracuseStep 237289945 = 177967459) B177967459
theorem B1974811 : Blo 1754578 1974811 := bstep (se 1 (by rfl) ⟨1481108, by rfl⟩ : syracuseStep 1974811 = 2962217) B2962217
theorem B3162655 : Blo 1754578 3162655 := bstep (se 1 (by rfl) ⟨2371991, by rfl⟩ : syracuseStep 3162655 = 4743983) B4743983
theorem B2056735 : Blo 1754578 2056735 := bstep (se 1 (by rfl) ⟨1542551, by rfl⟩ : syracuseStep 2056735 = 3085103) B3085103
theorem B8888939 : Blo 1754578 8888939 := bstep (se 1 (by rfl) ⟨6666704, by rfl⟩ : syracuseStep 8888939 = 13333409) B13333409
theorem B3949217 : Blo 1754578 3949217 := bstep (se 2 (by rfl) ⟨1480956, by rfl⟩ : syracuseStep 3949217 = 2961913) B2961913
theorem B1974991 : Blo 1754578 1974991 := bstep (se 1 (by rfl) ⟨1481243, by rfl⟩ : syracuseStep 1974991 = 2962487) B2962487
theorem B8438779 : Blo 1754578 8438779 := bstep (se 1 (by rfl) ⟨6329084, by rfl⟩ : syracuseStep 8438779 = 12658169) B12658169
theorem B3949577 : Blo 1754578 3949577 := bstep (se 2 (by rfl) ⟨1481091, by rfl⟩ : syracuseStep 3949577 = 2962183) B2962183
theorem B3949631 : Blo 1754578 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B50619755 : Blo 1754578 50619755 := bstep (se 1 (by rfl) ⟨37964816, by rfl⟩ : syracuseStep 50619755 = 75929633) B75929633
theorem B4441513 : Blo 1754578 4441513 := bstep (se 2 (by rfl) ⟨1665567, by rfl⟩ : syracuseStep 4441513 = 3331135) B3331135
theorem B8439223 : Blo 1754578 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B8906231 : Blo 1754578 8906231 := bstep (se 1 (by rfl) ⟨6679673, by rfl⟩ : syracuseStep 8906231 = 13359347) B13359347
theorem B1754651 : Blo 1754578 1754651 := bstep (se 1 (by rfl) ⟨1315988, by rfl⟩ : syracuseStep 1754651 = 2631977) B2631977
theorem B1754655 : Blo 1754578 1754655 := bstep (se 1 (by rfl) ⟨1315991, by rfl⟩ : syracuseStep 1754655 = 2631983) B2631983
theorem B18990713 : Blo 1754578 18990713 := bstep (se 2 (by rfl) ⟨7121517, by rfl⟩ : syracuseStep 18990713 = 14243035) B14243035
theorem B1754815 : Blo 1754578 1754815 := bstep (se 1 (by rfl) ⟨1316111, by rfl⟩ : syracuseStep 1754815 = 2632223) B2632223
theorem B1975999 : Blo 1754578 1975999 := bstep (se 1 (by rfl) ⟨1481999, by rfl⟩ : syracuseStep 1975999 = 2963999) B2963999
theorem B1755071 : Blo 1754578 1755071 := bstep (se 1 (by rfl) ⟨1316303, by rfl⟩ : syracuseStep 1755071 = 2632607) B2632607
theorem B1755103 : Blo 1754578 1755103 := bstep (se 1 (by rfl) ⟨1316327, by rfl⟩ : syracuseStep 1755103 = 2632655) B2632655
theorem B3950567 : Blo 1754578 3950567 := bstep (se 1 (by rfl) ⟨2962925, by rfl⟩ : syracuseStep 3950567 = 5925851) B5925851
theorem B7604207 : Blo 1754578 7604207 := bstep (se 1 (by rfl) ⟨5703155, by rfl⟩ : syracuseStep 7604207 = 11406311) B11406311
theorem B60786679 : Blo 1754578 60786679 := bstep (se 1 (by rfl) ⟨45590009, by rfl⟩ : syracuseStep 60786679 = 91180019) B91180019
theorem B1755163 : Blo 1754578 1755163 := bstep (se 1 (by rfl) ⟨1316372, by rfl⟩ : syracuseStep 1755163 = 2632745) B2632745
theorem B1755167 : Blo 1754578 1755167 := bstep (se 1 (by rfl) ⟨1316375, by rfl⟩ : syracuseStep 1755167 = 2632751) B2632751
theorem B8439839 : Blo 1754578 8439839 := bstep (se 1 (by rfl) ⟨6329879, by rfl⟩ : syracuseStep 8439839 = 12659759) B12659759
theorem B1755183 : Blo 1754578 1755183 := bstep (se 1 (by rfl) ⟨1316387, by rfl⟩ : syracuseStep 1755183 = 2632775) B2632775
theorem B5924987 : Blo 1754578 5924987 := bstep (se 1 (by rfl) ⟨4443740, by rfl⟩ : syracuseStep 5924987 = 8887481) B8887481
theorem B3950747 : Blo 1754578 3950747 := bstep (se 1 (by rfl) ⟨2963060, by rfl⟩ : syracuseStep 3950747 = 5926121) B5926121
theorem B8890559 : Blo 1754578 8890559 := bstep (se 1 (by rfl) ⟨6667919, by rfl⟩ : syracuseStep 8890559 = 13335839) B13335839
theorem B1755359 : Blo 1754578 1755359 := bstep (se 1 (by rfl) ⟨1316519, by rfl⟩ : syracuseStep 1755359 = 2633039) B2633039
theorem B1755419 : Blo 1754578 1755419 := bstep (se 1 (by rfl) ⟨1316564, by rfl⟩ : syracuseStep 1755419 = 2633129) B2633129
theorem B22808891 : Blo 1754578 22808891 := bstep (se 1 (by rfl) ⟨17106668, by rfl⟩ : syracuseStep 22808891 = 34213337) B34213337
theorem B3950927 : Blo 1754578 3950927 := bstep (se 1 (by rfl) ⟨2963195, by rfl⟩ : syracuseStep 3950927 = 5926391) B5926391
theorem B1755519 : Blo 1754578 1755519 := bstep (se 1 (by rfl) ⟨1316639, by rfl⟩ : syracuseStep 1755519 = 2633279) B2633279
theorem B2632073 : Blo 1754578 2632073 := bstep (se 2 (by rfl) ⟨987027, by rfl⟩ : syracuseStep 2632073 = 1974055) B1974055
theorem B5925257 : Blo 1754578 5925257 := bstep (se 2 (by rfl) ⟨2221971, by rfl⟩ : syracuseStep 5925257 = 4443943) B4443943
theorem B3951017 : Blo 1754578 3951017 := bstep (se 2 (by rfl) ⟨1481631, by rfl⟩ : syracuseStep 3951017 = 2963263) B2963263
theorem B1755695 : Blo 1754578 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B1755751 : Blo 1754578 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B4999801 : Blo 1754578 4999801 := bstep (se 2 (by rfl) ⟨1874925, by rfl⟩ : syracuseStep 4999801 = 3749851) B3749851
theorem B3377801 : Blo 1754578 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B7498439 : Blo 1754578 7498439 := bstep (se 1 (by rfl) ⟨5623829, by rfl⟩ : syracuseStep 7498439 = 11247659) B11247659
theorem B33729281 : Blo 1754578 33729281 := bstep (se 2 (by rfl) ⟨12648480, by rfl⟩ : syracuseStep 33729281 = 25296961) B25296961
theorem B4999961 : Blo 1754578 4999961 := bstep (se 2 (by rfl) ⟨1874985, by rfl⟩ : syracuseStep 4999961 = 3749971) B3749971
theorem B4442921 : Blo 1754578 4442921 := bstep (se 2 (by rfl) ⟨1666095, by rfl⟩ : syracuseStep 4442921 = 3332191) B3332191
theorem B4442971 : Blo 1754578 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B1756127 : Blo 1754578 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B1756155 : Blo 1754578 1756155 := bstep (se 1 (by rfl) ⟨1317116, by rfl⟩ : syracuseStep 1756155 = 2634233) B2634233
theorem B3951611 : Blo 1754578 3951611 := bstep (se 1 (by rfl) ⟨2963708, by rfl⟩ : syracuseStep 3951611 = 5927417) B5927417
theorem B5000201 : Blo 1754578 5000201 := bstep (se 2 (by rfl) ⟨1875075, by rfl⟩ : syracuseStep 5000201 = 3750151) B3750151
theorem B1756223 : Blo 1754578 1756223 := bstep (se 1 (by rfl) ⟨1317167, by rfl⟩ : syracuseStep 1756223 = 2634335) B2634335
theorem B3951791 : Blo 1754578 3951791 := bstep (se 1 (by rfl) ⟨2963843, by rfl⟩ : syracuseStep 3951791 = 5927687) B5927687
theorem B3951827 : Blo 1754578 3951827 := bstep (se 1 (by rfl) ⟨2963870, by rfl⟩ : syracuseStep 3951827 = 5927741) B5927741
theorem B2633015 : Blo 1754578 2633015 := bstep (se 1 (by rfl) ⟨1974761, by rfl⟩ : syracuseStep 2633015 = 3949523) B3949523
theorem B1756543 : Blo 1754578 1756543 := bstep (se 1 (by rfl) ⟨1317407, by rfl⟩ : syracuseStep 1756543 = 2634815) B2634815
theorem B1756571 : Blo 1754578 1756571 := bstep (se 1 (by rfl) ⟨1317428, by rfl⟩ : syracuseStep 1756571 = 2634857) B2634857
theorem B2633183 : Blo 1754578 2633183 := bstep (se 1 (by rfl) ⟨1974887, by rfl⟩ : syracuseStep 2633183 = 3949775) B3949775
theorem B12652001 : Blo 1754578 12652001 := bstep (se 2 (by rfl) ⟨4744500, by rfl⟩ : syracuseStep 12652001 = 9489001) B9489001
theorem B3952097 : Blo 1754578 3952097 := bstep (se 2 (by rfl) ⟨1482036, by rfl⟩ : syracuseStep 3952097 = 2964073) B2964073
theorem B2633399 : Blo 1754578 2633399 := bstep (se 1 (by rfl) ⟨1975049, by rfl⟩ : syracuseStep 2633399 = 3950099) B3950099
theorem B3747647 : Blo 1754578 3747647 := bstep (se 1 (by rfl) ⟨2810735, by rfl⟩ : syracuseStep 3747647 = 5621471) B5621471
theorem B5001031 : Blo 1754578 5001031 := bstep (se 1 (by rfl) ⟨3750773, by rfl⟩ : syracuseStep 5001031 = 7501547) B7501547
theorem B2633609 : Blo 1754578 2633609 := bstep (se 2 (by rfl) ⟨987603, by rfl⟩ : syracuseStep 2633609 = 1975207) B1975207
theorem B2109503 : Blo 1754578 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B2961481 : Blo 1754578 2961481 := bstep (se 2 (by rfl) ⟨1110555, by rfl⟩ : syracuseStep 2961481 = 2221111) B2221111
theorem B5926985 : Blo 1754578 5926985 := bstep (se 2 (by rfl) ⟨2222619, by rfl⟩ : syracuseStep 5926985 = 4445239) B4445239
theorem B2961535 : Blo 1754578 2961535 := bstep (se 1 (by rfl) ⟨2221151, by rfl⟩ : syracuseStep 2961535 = 4442303) B4442303
theorem B2633855 : Blo 1754578 2633855 := bstep (se 1 (by rfl) ⟨1975391, by rfl⟩ : syracuseStep 2633855 = 3950783) B3950783
theorem B4444379 : Blo 1754578 4444379 := bstep (se 1 (by rfl) ⟨3333284, by rfl⟩ : syracuseStep 4444379 = 6666569) B6666569
theorem B15003913 : Blo 1754578 15003913 := bstep (se 2 (by rfl) ⟨5626467, by rfl⟩ : syracuseStep 15003913 = 11252935) B11252935
theorem B5001659 : Blo 1754578 5001659 := bstep (se 1 (by rfl) ⟨3751244, by rfl⟩ : syracuseStep 5001659 = 7502489) B7502489
theorem B2634491 : Blo 1754578 2634491 := bstep (se 1 (by rfl) ⟨1975868, by rfl⟩ : syracuseStep 2634491 = 3951737) B3951737
theorem B3748655 : Blo 1754578 3748655 := bstep (se 1 (by rfl) ⟨2811491, by rfl⟩ : syracuseStep 3748655 = 5622983) B5622983
theorem B4002643 : Blo 1754578 4002643 := bstep (se 1 (by rfl) ⟨3001982, by rfl⟩ : syracuseStep 4002643 = 6003965) B6003965
theorem B7500863 : Blo 1754578 7500863 := bstep (se 1 (by rfl) ⟨5625647, by rfl⟩ : syracuseStep 7500863 = 11251295) B11251295
theorem B33731741 : Blo 1754578 33731741 := bstep (se 3 (by rfl) ⟨6324701, by rfl⟩ : syracuseStep 33731741 = 12649403) B12649403
theorem B2962615 : Blo 1754578 2962615 := bstep (se 1 (by rfl) ⟨2221961, by rfl⟩ : syracuseStep 2962615 = 4443923) B4443923
theorem B5928119 : Blo 1754578 5928119 := bstep (se 1 (by rfl) ⟨4446089, by rfl⟩ : syracuseStep 5928119 = 8892179) B8892179
theorem B15004871 : Blo 1754578 15004871 := bstep (se 1 (by rfl) ⟨11253653, by rfl⟩ : syracuseStep 15004871 = 22507307) B22507307
theorem B5625085 : Blo 1754578 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B3331439 : Blo 1754578 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B3331705 : Blo 1754578 3331705 := bstep (se 2 (by rfl) ⟨1249389, by rfl⟩ : syracuseStep 3331705 = 2498779) B2498779
theorem B14997149 : Blo 1754578 14997149 := bstep (se 3 (by rfl) ⟨2811965, by rfl⟩ : syracuseStep 14997149 = 5623931) B5623931
theorem B3334135 : Blo 1754578 3334135 := bstep (se 1 (by rfl) ⟨2500601, by rfl⟩ : syracuseStep 3334135 = 5001203) B5001203
theorem B8886023 : Blo 1754578 8886023 := bstep (se 1 (by rfl) ⟨6664517, by rfl⟩ : syracuseStep 8886023 = 13329035) B13329035
theorem B19986263 : Blo 1754578 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B2963371 : Blo 1754578 2963371 := bstep (se 1 (by rfl) ⟨2222528, by rfl⟩ : syracuseStep 2963371 = 4445057) B4445057
theorem B22493159 : Blo 1754578 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B25319567 : Blo 1754578 25319567 := bstep (se 1 (by rfl) ⟨18989675, by rfl⟩ : syracuseStep 25319567 = 37979351) B37979351
theorem B10279097 : Blo 1754578 10279097 := bstep (se 2 (by rfl) ⟨3854661, by rfl⟩ : syracuseStep 10279097 = 7709323) B7709323
theorem B2963911 : Blo 1754578 2963911 := bstep (se 1 (by rfl) ⟨2222933, by rfl⟩ : syracuseStep 2963911 = 4445867) B4445867
theorem B10672793 : Blo 1754578 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B2964127 : Blo 1754578 2964127 := bstep (se 1 (by rfl) ⟨2223095, by rfl⟩ : syracuseStep 2964127 = 4446191) B4446191
theorem B6667055 : Blo 1754578 6667055 := bstep (se 1 (by rfl) ⟨5000291, by rfl⟩ : syracuseStep 6667055 = 10000583) B10000583
theorem B9993041 : Blo 1754578 9993041 := bstep (se 2 (by rfl) ⟨3747390, by rfl⟩ : syracuseStep 9993041 = 7494781) B7494781
theorem B18013175 : Blo 1754578 18013175 := bstep (se 1 (by rfl) ⟨13509881, by rfl⟩ : syracuseStep 18013175 = 27019763) B27019763
theorem B64920761 : Blo 1754578 64920761 := bstep (se 2 (by rfl) ⟨24345285, by rfl⟩ : syracuseStep 64920761 = 48690571) B48690571
theorem B3947849 : Blo 1754578 3947849 := bstep (se 2 (by rfl) ⟨1480443, by rfl⟩ : syracuseStep 3947849 = 2960887) B2960887
theorem B4996475 : Blo 1754578 4996475 := bstep (se 1 (by rfl) ⟨3747356, by rfl⟩ : syracuseStep 4996475 = 7494713) B7494713
theorem B2850527 : Blo 1754578 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B3948263 : Blo 1754578 3948263 := bstep (se 1 (by rfl) ⟨2961197, by rfl⟩ : syracuseStep 3948263 = 5922395) B5922395
theorem B1974127 : Blo 1754578 1974127 := bstep (se 1 (by rfl) ⟨1480595, by rfl⟩ : syracuseStep 1974127 = 2961191) B2961191
theorem B16875485 : Blo 1754578 16875485 := bstep (se 3 (by rfl) ⟨3164153, by rfl⟩ : syracuseStep 16875485 = 6328307) B6328307
theorem B14999539 : Blo 1754578 14999539 := bstep (se 1 (by rfl) ⟨11249654, by rfl⟩ : syracuseStep 14999539 = 22499309) B22499309
theorem B3948641 : Blo 1754578 3948641 := bstep (se 2 (by rfl) ⟨1480740, by rfl⟩ : syracuseStep 3948641 = 2961481) B2961481
theorem B10969253 : Blo 1754578 10969253 := bstep (se 4 (by rfl) ⟨1028367, by rfl⟩ : syracuseStep 10969253 = 2056735) B2056735
theorem B3948713 : Blo 1754578 3948713 := bstep (se 2 (by rfl) ⟨1480767, by rfl⟩ : syracuseStep 3948713 = 2961535) B2961535
theorem B9994499 : Blo 1754578 9994499 := bstep (se 1 (by rfl) ⟨7495874, by rfl⟩ : syracuseStep 9994499 = 14991749) B14991749
theorem B3334439 : Blo 1754578 3334439 := bstep (se 1 (by rfl) ⟨2500829, by rfl⟩ : syracuseStep 3334439 = 5001659) B5001659
theorem B20005217 : Blo 1754578 20005217 := bstep (se 2 (by rfl) ⟨7501956, by rfl⟩ : syracuseStep 20005217 = 15003913) B15003913
theorem B2499103 : Blo 1754578 2499103 := bstep (se 1 (by rfl) ⟨1874327, by rfl⟩ : syracuseStep 2499103 = 3748655) B3748655
theorem B22487827 : Blo 1754578 22487827 := bstep (se 1 (by rfl) ⟨16865870, by rfl⟩ : syracuseStep 22487827 = 33731741) B33731741
theorem B10003247 : Blo 1754578 10003247 := bstep (se 1 (by rfl) ⟨7502435, by rfl⟩ : syracuseStep 10003247 = 15004871) B15004871
theorem B2220959 : Blo 1754578 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B5923961 : Blo 1754578 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B5924015 : Blo 1754578 5924015 := bstep (se 1 (by rfl) ⟨4443011, by rfl⟩ : syracuseStep 5924015 = 8886023) B8886023
theorem B23749949 : Blo 1754578 23749949 := bstep (se 3 (by rfl) ⟨4453115, by rfl⟩ : syracuseStep 23749949 = 8906231) B8906231
theorem B3949991 : Blo 1754578 3949991 := bstep (se 1 (by rfl) ⟨2962493, by rfl⟩ : syracuseStep 3949991 = 5924987) B5924987
theorem B15205927 : Blo 1754578 15205927 := bstep (se 1 (by rfl) ⟨11404445, by rfl⟩ : syracuseStep 15205927 = 22808891) B22808891
theorem B3950153 : Blo 1754578 3950153 := bstep (se 2 (by rfl) ⟨1481307, by rfl⟩ : syracuseStep 3950153 = 2962615) B2962615
theorem B1754715 : Blo 1754578 1754715 := bstep (se 1 (by rfl) ⟨1316036, by rfl⟩ : syracuseStep 1754715 = 2632073) B2632073
theorem B3950171 : Blo 1754578 3950171 := bstep (se 1 (by rfl) ⟨2962628, by rfl⟩ : syracuseStep 3950171 = 5925257) B5925257
theorem B4998959 : Blo 1754578 4998959 := bstep (se 1 (by rfl) ⟨3749219, by rfl⟩ : syracuseStep 4998959 = 7498439) B7498439
theorem B6662027 : Blo 1754578 6662027 := bstep (se 1 (by rfl) ⟨4996520, by rfl⟩ : syracuseStep 6662027 = 9993041) B9993041
theorem B43280507 : Blo 1754578 43280507 := bstep (se 1 (by rfl) ⟨32460380, by rfl⟩ : syracuseStep 43280507 = 64920761) B64920761
theorem B4442273 : Blo 1754578 4442273 := bstep (se 2 (by rfl) ⟨1665852, by rfl⟩ : syracuseStep 4442273 = 3331705) B3331705
theorem B1755343 : Blo 1754578 1755343 := bstep (se 1 (by rfl) ⟨1316507, by rfl⟩ : syracuseStep 1755343 = 2633015) B2633015
theorem B2631899 : Blo 1754578 2631899 := bstep (se 1 (by rfl) ⟨1973924, by rfl⟩ : syracuseStep 2631899 = 3947849) B3947849
theorem B1755455 : Blo 1754578 1755455 := bstep (se 1 (by rfl) ⟨1316591, by rfl⟩ : syracuseStep 1755455 = 2633183) B2633183
theorem B1755599 : Blo 1754578 1755599 := bstep (se 1 (by rfl) ⟨1316699, by rfl⟩ : syracuseStep 1755599 = 2633399) B2633399
theorem B2632169 : Blo 1754578 2632169 := bstep (se 2 (by rfl) ⟨987063, by rfl⟩ : syracuseStep 2632169 = 1974127) B1974127
theorem B2632175 : Blo 1754578 2632175 := bstep (se 1 (by rfl) ⟨1974131, by rfl⟩ : syracuseStep 2632175 = 3948263) B3948263
theorem B3951161 : Blo 1754578 3951161 := bstep (se 2 (by rfl) ⟨1481685, by rfl⟩ : syracuseStep 3951161 = 2963371) B2963371
theorem B1755739 : Blo 1754578 1755739 := bstep (se 1 (by rfl) ⟨1316804, by rfl⟩ : syracuseStep 1755739 = 2633609) B2633609
theorem B11250323 : Blo 1754578 11250323 := bstep (se 1 (by rfl) ⟨8437742, by rfl⟩ : syracuseStep 11250323 = 16875485) B16875485
theorem B19999385 : Blo 1754578 19999385 := bstep (se 2 (by rfl) ⟨7499769, by rfl⟩ : syracuseStep 19999385 = 14999539) B14999539
theorem B3951323 : Blo 1754578 3951323 := bstep (se 1 (by rfl) ⟨2963492, by rfl⟩ : syracuseStep 3951323 = 5926985) B5926985
theorem B1755903 : Blo 1754578 1755903 := bstep (se 1 (by rfl) ⟨1316927, by rfl⟩ : syracuseStep 1755903 = 2633855) B2633855
theorem B2632487 : Blo 1754578 2632487 := bstep (se 1 (by rfl) ⟨1974365, by rfl⟩ : syracuseStep 2632487 = 3948731) B3948731
theorem B2632559 : Blo 1754578 2632559 := bstep (se 1 (by rfl) ⟨1974419, by rfl⟩ : syracuseStep 2632559 = 3948839) B3948839
theorem B5925959 : Blo 1754578 5925959 := bstep (se 1 (by rfl) ⟨4444469, by rfl⟩ : syracuseStep 5925959 = 8888939) B8888939
theorem B2632811 : Blo 1754578 2632811 := bstep (se 1 (by rfl) ⟨1974608, by rfl⟩ : syracuseStep 2632811 = 3949217) B3949217
theorem B1756327 : Blo 1754578 1756327 := bstep (se 1 (by rfl) ⟨1317245, by rfl⟩ : syracuseStep 1756327 = 2634491) B2634491
theorem B3951881 : Blo 1754578 3951881 := bstep (se 2 (by rfl) ⟨1481955, by rfl⟩ : syracuseStep 3951881 = 2963911) B2963911
theorem B316386593 : Blo 1754578 316386593 := bstep (se 2 (by rfl) ⟨118644972, by rfl⟩ : syracuseStep 316386593 = 237289945) B237289945
theorem B2633051 : Blo 1754578 2633051 := bstep (se 1 (by rfl) ⟨1974788, by rfl⟩ : syracuseStep 2633051 = 3949577) B3949577
theorem B2633081 : Blo 1754578 2633081 := bstep (se 2 (by rfl) ⟨987405, by rfl⟩ : syracuseStep 2633081 = 1974811) B1974811
theorem B2633087 : Blo 1754578 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B3952079 : Blo 1754578 3952079 := bstep (se 1 (by rfl) ⟨2964059, by rfl⟩ : syracuseStep 3952079 = 5928119) B5928119
theorem B3952169 : Blo 1754578 3952169 := bstep (se 2 (by rfl) ⟨1482063, by rfl⟩ : syracuseStep 3952169 = 2964127) B2964127
theorem B33746503 : Blo 1754578 33746503 := bstep (se 1 (by rfl) ⟨25309877, by rfl⟩ : syracuseStep 33746503 = 50619755) B50619755
theorem B2633321 : Blo 1754578 2633321 := bstep (se 2 (by rfl) ⟨987495, by rfl⟩ : syracuseStep 2633321 = 1974991) B1974991
theorem B12660475 : Blo 1754578 12660475 := bstep (se 1 (by rfl) ⟨9495356, by rfl⟩ : syracuseStep 12660475 = 18990713) B18990713
theorem B9998099 : Blo 1754578 9998099 := bstep (se 1 (by rfl) ⟨7498574, by rfl⟩ : syracuseStep 9998099 = 14997149) B14997149
theorem B5336857 : Blo 1754578 5336857 := bstep (se 2 (by rfl) ⟨2001321, by rfl⟩ : syracuseStep 5336857 = 4002643) B4002643
theorem B13324175 : Blo 1754578 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B14995439 : Blo 1754578 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B2633711 : Blo 1754578 2633711 := bstep (se 1 (by rfl) ⟨1975283, by rfl⟩ : syracuseStep 2633711 = 3950567) B3950567
theorem B11251705 : Blo 1754578 11251705 := bstep (se 2 (by rfl) ⟨4219389, by rfl⟩ : syracuseStep 11251705 = 8438779) B8438779
theorem B16879711 : Blo 1754578 16879711 := bstep (se 1 (by rfl) ⟨12659783, by rfl⟩ : syracuseStep 16879711 = 25319567) B25319567
theorem B2633831 : Blo 1754578 2633831 := bstep (se 1 (by rfl) ⟨1975373, by rfl⟩ : syracuseStep 2633831 = 3950747) B3950747
theorem B6852731 : Blo 1754578 6852731 := bstep (se 1 (by rfl) ⟨5139548, by rfl⟩ : syracuseStep 6852731 = 10279097) B10279097
theorem B5927039 : Blo 1754578 5927039 := bstep (se 1 (by rfl) ⟨4445279, by rfl⟩ : syracuseStep 5927039 = 8890559) B8890559
theorem B2633951 : Blo 1754578 2633951 := bstep (se 1 (by rfl) ⟨1975463, by rfl⟩ : syracuseStep 2633951 = 3950927) B3950927
theorem B2634011 : Blo 1754578 2634011 := bstep (se 1 (by rfl) ⟨1975508, by rfl⟩ : syracuseStep 2634011 = 3951017) B3951017
theorem B7500113 : Blo 1754578 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B7115195 : Blo 1754578 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B2961947 : Blo 1754578 2961947 := bstep (se 1 (by rfl) ⟨2221460, by rfl⟩ : syracuseStep 2961947 = 4442921) B4442921
theorem B4444703 : Blo 1754578 4444703 := bstep (se 1 (by rfl) ⟨3333527, by rfl⟩ : syracuseStep 4444703 = 6667055) B6667055
theorem B11252297 : Blo 1754578 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B2634407 : Blo 1754578 2634407 := bstep (se 1 (by rfl) ⟨1975805, by rfl⟩ : syracuseStep 2634407 = 3951611) B3951611
theorem B2634527 : Blo 1754578 2634527 := bstep (se 1 (by rfl) ⟨1975895, by rfl⟩ : syracuseStep 2634527 = 3951791) B3951791
theorem B2634551 : Blo 1754578 2634551 := bstep (se 1 (by rfl) ⟨1975913, by rfl⟩ : syracuseStep 2634551 = 3951827) B3951827
theorem B3330983 : Blo 1754578 3330983 := bstep (se 1 (by rfl) ⟨2498237, by rfl⟩ : syracuseStep 3330983 = 4996475) B4996475
theorem B2634665 : Blo 1754578 2634665 := bstep (se 2 (by rfl) ⟨987999, by rfl⟩ : syracuseStep 2634665 = 1975999) B1975999
theorem B8434667 : Blo 1754578 8434667 := bstep (se 1 (by rfl) ⟨6326000, by rfl⟩ : syracuseStep 8434667 = 12652001) B12652001
theorem B2634731 : Blo 1754578 2634731 := bstep (se 1 (by rfl) ⟨1976048, by rfl⟩ : syracuseStep 2634731 = 3952097) B3952097
theorem B81048905 : Blo 1754578 81048905 := bstep (se 2 (by rfl) ⟨30393339, by rfl⟩ : syracuseStep 81048905 = 60786679) B60786679
theorem B4445513 : Blo 1754578 4445513 := bstep (se 2 (by rfl) ⟨1667067, by rfl⟩ : syracuseStep 4445513 = 3334135) B3334135
theorem B2962919 : Blo 1754578 2962919 := bstep (se 1 (by rfl) ⟨2222189, by rfl⟩ : syracuseStep 2962919 = 4444379) B4444379
theorem B5625341 : Blo 1754578 5625341 := bstep (se 3 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 5625341 = 2109503) B2109503
theorem B20002301 : Blo 1754578 20002301 := bstep (se 3 (by rfl) ⟨3750431, by rfl⟩ : syracuseStep 20002301 = 7500863) B7500863
theorem B4446049 : Blo 1754578 4446049 := bstep (se 2 (by rfl) ⟨1667268, by rfl⟩ : syracuseStep 4446049 = 3334537) B3334537
theorem B4216873 : Blo 1754578 4216873 := bstep (se 2 (by rfl) ⟨1581327, by rfl⟩ : syracuseStep 4216873 = 3162655) B3162655
theorem B6666401 : Blo 1754578 6666401 := bstep (se 2 (by rfl) ⟨2499900, by rfl⟩ : syracuseStep 6666401 = 4999801) B4999801
theorem B5069471 : Blo 1754578 5069471 := bstep (se 1 (by rfl) ⟨3802103, by rfl⟩ : syracuseStep 5069471 = 7604207) B7604207
theorem B5626559 : Blo 1754578 5626559 := bstep (se 1 (by rfl) ⟨4219919, by rfl⟩ : syracuseStep 5626559 = 8439839) B8439839
theorem B2251867 : Blo 1754578 2251867 := bstep (se 1 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 2251867 = 3377801) B3377801
theorem B22486187 : Blo 1754578 22486187 := bstep (se 1 (by rfl) ⟨16864640, by rfl⟩ : syracuseStep 22486187 = 33729281) B33729281
theorem B3333307 : Blo 1754578 3333307 := bstep (se 1 (by rfl) ⟨2499980, by rfl⟩ : syracuseStep 3333307 = 4999961) B4999961
theorem B5922017 : Blo 1754578 5922017 := bstep (se 2 (by rfl) ⟨2220756, by rfl⟩ : syracuseStep 5922017 = 4441513) B4441513
theorem B12008783 : Blo 1754578 12008783 := bstep (se 1 (by rfl) ⟨9006587, by rfl⟩ : syracuseStep 12008783 = 18013175) B18013175
theorem B3333467 : Blo 1754578 3333467 := bstep (se 1 (by rfl) ⟨2500100, by rfl⟩ : syracuseStep 3333467 = 5000201) B5000201
theorem B9993725 : Blo 1754578 9993725 := bstep (se 3 (by rfl) ⟨1873823, by rfl⟩ : syracuseStep 9993725 = 3747647) B3747647
theorem B6668041 : Blo 1754578 6668041 := bstep (se 2 (by rfl) ⟨2500515, by rfl⟩ : syracuseStep 6668041 = 5001031) B5001031
theorem B1900351 : Blo 1754578 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B13328549 : Blo 1754578 13328549 := bstep (se 4 (by rfl) ⟨1249551, by rfl⟩ : syracuseStep 13328549 = 2499103) B2499103
theorem B13336811 : Blo 1754578 13336811 := bstep (se 1 (by rfl) ⟨10002608, by rfl⟩ : syracuseStep 13336811 = 20005217) B20005217
theorem B4743463 : Blo 1754578 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B1974631 : Blo 1754578 1974631 := bstep (se 1 (by rfl) ⟨1480973, by rfl⟩ : syracuseStep 1974631 = 2961947) B2961947
theorem B6668831 : Blo 1754578 6668831 := bstep (se 1 (by rfl) ⟨5001623, by rfl⟩ : syracuseStep 6668831 = 10003247) B10003247
theorem B3949307 : Blo 1754578 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B3949343 : Blo 1754578 3949343 := bstep (se 1 (by rfl) ⟨2962007, by rfl⟩ : syracuseStep 3949343 = 5924015) B5924015
theorem B63333197 : Blo 1754578 63333197 := bstep (se 3 (by rfl) ⟨11874974, by rfl⟩ : syracuseStep 63333197 = 23749949) B23749949
theorem B32023421 : Blo 1754578 32023421 := bstep (se 3 (by rfl) ⟨6004391, by rfl⟩ : syracuseStep 32023421 = 12008783) B12008783
theorem B1975279 : Blo 1754578 1975279 := bstep (se 1 (by rfl) ⟨1481459, by rfl⟩ : syracuseStep 1975279 = 2962919) B2962919
theorem B29983769 : Blo 1754578 29983769 := bstep (se 2 (by rfl) ⟨11243913, by rfl⟩ : syracuseStep 29983769 = 22487827) B22487827
theorem B4441351 : Blo 1754578 4441351 := bstep (se 1 (by rfl) ⟨3331013, by rfl⟩ : syracuseStep 4441351 = 6662027) B6662027
theorem B28853671 : Blo 1754578 28853671 := bstep (se 1 (by rfl) ⟨21640253, by rfl⟩ : syracuseStep 28853671 = 43280507) B43280507
theorem B1754599 : Blo 1754578 1754599 := bstep (se 1 (by rfl) ⟨1315949, by rfl⟩ : syracuseStep 1754599 = 2631899) B2631899
theorem B1754779 : Blo 1754578 1754779 := bstep (se 1 (by rfl) ⟨1316084, by rfl⟩ : syracuseStep 1754779 = 2632169) B2632169
theorem B1754783 : Blo 1754578 1754783 := bstep (se 1 (by rfl) ⟨1316087, by rfl⟩ : syracuseStep 1754783 = 2632175) B2632175
theorem B10135205 : Blo 1754578 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B13518589 : Blo 1754578 13518589 := bstep (se 3 (by rfl) ⟨2534735, by rfl⟩ : syracuseStep 13518589 = 5069471) B5069471
theorem B1754991 : Blo 1754578 1754991 := bstep (se 1 (by rfl) ⟨1316243, by rfl⟩ : syracuseStep 1754991 = 2632487) B2632487
theorem B1755039 : Blo 1754578 1755039 := bstep (se 1 (by rfl) ⟨1316279, by rfl⟩ : syracuseStep 1755039 = 2632559) B2632559
theorem B3950639 : Blo 1754578 3950639 := bstep (se 1 (by rfl) ⟨2962979, by rfl⟩ : syracuseStep 3950639 = 5925959) B5925959
theorem B1755207 : Blo 1754578 1755207 := bstep (se 1 (by rfl) ⟨1316405, by rfl⟩ : syracuseStep 1755207 = 2632811) B2632811
theorem B1755367 : Blo 1754578 1755367 := bstep (se 1 (by rfl) ⟨1316525, by rfl⟩ : syracuseStep 1755367 = 2633051) B2633051
theorem B2222311 : Blo 1754578 2222311 := bstep (se 1 (by rfl) ⟨1666733, by rfl⟩ : syracuseStep 2222311 = 3333467) B3333467
theorem B1755387 : Blo 1754578 1755387 := bstep (se 1 (by rfl) ⟨1316540, by rfl⟩ : syracuseStep 1755387 = 2633081) B2633081
theorem B1755391 : Blo 1754578 1755391 := bstep (se 1 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 1755391 = 2633087) B2633087
theorem B6662483 : Blo 1754578 6662483 := bstep (se 1 (by rfl) ⟨4996862, by rfl⟩ : syracuseStep 6662483 = 9993725) B9993725
theorem B8890721 : Blo 1754578 8890721 := bstep (se 2 (by rfl) ⟨3334020, by rfl⟩ : syracuseStep 8890721 = 6668041) B6668041
theorem B1755547 : Blo 1754578 1755547 := bstep (se 1 (by rfl) ⟨1316660, by rfl⟩ : syracuseStep 1755547 = 2633321) B2633321
theorem B8882621 : Blo 1754578 8882621 := bstep (se 3 (by rfl) ⟨1665491, by rfl⟩ : syracuseStep 8882621 = 3330983) B3330983
theorem B8882783 : Blo 1754578 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B9996959 : Blo 1754578 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B1755807 : Blo 1754578 1755807 := bstep (se 1 (by rfl) ⟨1316855, by rfl⟩ : syracuseStep 1755807 = 2633711) B2633711
theorem B15002273 : Blo 1754578 15002273 := bstep (se 2 (by rfl) ⟨5625852, by rfl⟩ : syracuseStep 15002273 = 11251705) B11251705
theorem B5622497 : Blo 1754578 5622497 := bstep (se 2 (by rfl) ⟨2108436, by rfl⟩ : syracuseStep 5622497 = 4216873) B4216873
theorem B2632427 : Blo 1754578 2632427 := bstep (se 1 (by rfl) ⟨1974320, by rfl⟩ : syracuseStep 2632427 = 3948641) B3948641
theorem B1755887 : Blo 1754578 1755887 := bstep (se 1 (by rfl) ⟨1316915, by rfl⟩ : syracuseStep 1755887 = 2633831) B2633831
theorem B3951359 : Blo 1754578 3951359 := bstep (se 1 (by rfl) ⟨2963519, by rfl⟩ : syracuseStep 3951359 = 5927039) B5927039
theorem B2632475 : Blo 1754578 2632475 := bstep (se 1 (by rfl) ⟨1974356, by rfl⟩ : syracuseStep 2632475 = 3948713) B3948713
theorem B22506281 : Blo 1754578 22506281 := bstep (se 2 (by rfl) ⟨8439855, by rfl⟩ : syracuseStep 22506281 = 16879711) B16879711
theorem B1755967 : Blo 1754578 1755967 := bstep (se 1 (by rfl) ⟨1316975, by rfl⟩ : syracuseStep 1755967 = 2633951) B2633951
theorem B6662999 : Blo 1754578 6662999 := bstep (se 1 (by rfl) ⟨4997249, by rfl⟩ : syracuseStep 6662999 = 9994499) B9994499
theorem B1756007 : Blo 1754578 1756007 := bstep (se 1 (by rfl) ⟨1317005, by rfl⟩ : syracuseStep 1756007 = 2634011) B2634011
theorem B2222959 : Blo 1754578 2222959 := bstep (se 1 (by rfl) ⟨1667219, by rfl⟩ : syracuseStep 2222959 = 3334439) B3334439
theorem B5000075 : Blo 1754578 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B1756271 : Blo 1754578 1756271 := bstep (se 1 (by rfl) ⟨1317203, by rfl⟩ : syracuseStep 1756271 = 2634407) B2634407
theorem B1756351 : Blo 1754578 1756351 := bstep (se 1 (by rfl) ⟨1317263, by rfl⟩ : syracuseStep 1756351 = 2634527) B2634527
theorem B1756367 : Blo 1754578 1756367 := bstep (se 1 (by rfl) ⟨1317275, by rfl⟩ : syracuseStep 1756367 = 2634551) B2634551
theorem B1756443 : Blo 1754578 1756443 := bstep (se 1 (by rfl) ⟨1317332, by rfl⟩ : syracuseStep 1756443 = 2634665) B2634665
theorem B5623111 : Blo 1754578 5623111 := bstep (se 1 (by rfl) ⟨4217333, by rfl⟩ : syracuseStep 5623111 = 8434667) B8434667
theorem B1756487 : Blo 1754578 1756487 := bstep (se 1 (by rfl) ⟨1317365, by rfl⟩ : syracuseStep 1756487 = 2634731) B2634731
theorem B2633327 : Blo 1754578 2633327 := bstep (se 1 (by rfl) ⟨1974995, by rfl⟩ : syracuseStep 2633327 = 3949991) B3949991
theorem B2633435 : Blo 1754578 2633435 := bstep (se 1 (by rfl) ⟨1975076, by rfl⟩ : syracuseStep 2633435 = 3950153) B3950153
theorem B2633447 : Blo 1754578 2633447 := bstep (se 1 (by rfl) ⟨1975085, by rfl⟩ : syracuseStep 2633447 = 3950171) B3950171
theorem B2961515 : Blo 1754578 2961515 := bstep (se 1 (by rfl) ⟨2221136, by rfl⟩ : syracuseStep 2961515 = 4442273) B4442273
theorem B4444267 : Blo 1754578 4444267 := bstep (se 1 (by rfl) ⟨3333200, by rfl⟩ : syracuseStep 4444267 = 6666401) B6666401
theorem B3002489 : Blo 1754578 3002489 := bstep (se 2 (by rfl) ⟨1125933, by rfl⟩ : syracuseStep 3002489 = 2251867) B2251867
theorem B28463237 : Blo 1754578 28463237 := bstep (se 4 (by rfl) ⟨2668428, by rfl⟩ : syracuseStep 28463237 = 5336857) B5336857
theorem B4444409 : Blo 1754578 4444409 := bstep (se 2 (by rfl) ⟨1666653, by rfl⟩ : syracuseStep 4444409 = 3333307) B3333307
theorem B2634107 : Blo 1754578 2634107 := bstep (se 1 (by rfl) ⟨1975580, by rfl⟩ : syracuseStep 2634107 = 3951161) B3951161
theorem B7500215 : Blo 1754578 7500215 := bstep (se 1 (by rfl) ⟨5625161, by rfl⟩ : syracuseStep 7500215 = 11250323) B11250323
theorem B13332923 : Blo 1754578 13332923 := bstep (se 1 (by rfl) ⟨9999692, by rfl⟩ : syracuseStep 13332923 = 19999385) B19999385
theorem B2634215 : Blo 1754578 2634215 := bstep (se 1 (by rfl) ⟨1975661, by rfl⟩ : syracuseStep 2634215 = 3951323) B3951323
theorem B44995337 : Blo 1754578 44995337 := bstep (se 2 (by rfl) ⟨16873251, by rfl⟩ : syracuseStep 44995337 = 33746503) B33746503
theorem B2634587 : Blo 1754578 2634587 := bstep (se 1 (by rfl) ⟨1975940, by rfl⟩ : syracuseStep 2634587 = 3951881) B3951881
theorem B210924395 : Blo 1754578 210924395 := bstep (se 1 (by rfl) ⟨158193296, by rfl⟩ : syracuseStep 210924395 = 316386593) B316386593
theorem B2634719 : Blo 1754578 2634719 := bstep (se 1 (by rfl) ⟨1976039, by rfl⟩ : syracuseStep 2634719 = 3952079) B3952079
theorem B16880633 : Blo 1754578 16880633 := bstep (se 2 (by rfl) ⟨6330237, by rfl⟩ : syracuseStep 16880633 = 12660475) B12660475
theorem B2634779 : Blo 1754578 2634779 := bstep (se 1 (by rfl) ⟨1976084, by rfl⟩ : syracuseStep 2634779 = 3952169) B3952169
theorem B5928065 : Blo 1754578 5928065 := bstep (se 2 (by rfl) ⟨2223024, by rfl⟩ : syracuseStep 5928065 = 4446049) B4446049
theorem B6665399 : Blo 1754578 6665399 := bstep (se 1 (by rfl) ⟨4999049, by rfl⟩ : syracuseStep 6665399 = 9998099) B9998099
theorem B7312835 : Blo 1754578 7312835 := bstep (se 1 (by rfl) ⟨5484626, by rfl⟩ : syracuseStep 7312835 = 10969253) B10969253
theorem B2963135 : Blo 1754578 2963135 := bstep (se 1 (by rfl) ⟨2222351, by rfl⟩ : syracuseStep 2963135 = 4444703) B4444703
theorem B7501531 : Blo 1754578 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B54032603 : Blo 1754578 54032603 := bstep (se 1 (by rfl) ⟨40524452, by rfl⟩ : syracuseStep 54032603 = 81048905) B81048905
theorem B2963675 : Blo 1754578 2963675 := bstep (se 1 (by rfl) ⟨2222756, by rfl⟩ : syracuseStep 2963675 = 4445513) B4445513
theorem B3750227 : Blo 1754578 3750227 := bstep (se 1 (by rfl) ⟨2812670, by rfl⟩ : syracuseStep 3750227 = 5625341) B5625341
theorem B13334867 : Blo 1754578 13334867 := bstep (se 1 (by rfl) ⟨10001150, by rfl⟩ : syracuseStep 13334867 = 20002301) B20002301
theorem B3332639 : Blo 1754578 3332639 := bstep (se 1 (by rfl) ⟨2499479, by rfl⟩ : syracuseStep 3332639 = 4998959) B4998959
theorem B73095797 : Blo 1754578 73095797 := bstep (se 5 (by rfl) ⟨3426365, by rfl⟩ : syracuseStep 73095797 = 6852731) B6852731
theorem B3751039 : Blo 1754578 3751039 := bstep (se 1 (by rfl) ⟨2813279, by rfl⟩ : syracuseStep 3751039 = 5626559) B5626559
theorem B20274569 : Blo 1754578 20274569 := bstep (se 2 (by rfl) ⟨7602963, by rfl⟩ : syracuseStep 20274569 = 15205927) B15205927
theorem B14990791 : Blo 1754578 14990791 := bstep (se 1 (by rfl) ⟨11243093, by rfl⟩ : syracuseStep 14990791 = 22486187) B22486187
theorem B3948011 : Blo 1754578 3948011 := bstep (se 1 (by rfl) ⟨2961008, by rfl⟩ : syracuseStep 3948011 = 5922017) B5922017
theorem B5922557 : Blo 1754578 5922557 := bstep (se 3 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 5922557 = 2220959) B2220959
theorem B1974343 : Blo 1754578 1974343 := bstep (se 1 (by rfl) ⟨1480757, by rfl⟩ : syracuseStep 1974343 = 2961515) B2961515
theorem B8888615 : Blo 1754578 8888615 := bstep (se 1 (by rfl) ⟨6666461, by rfl⟩ : syracuseStep 8888615 = 13332923) B13332923
theorem B6324617 : Blo 1754578 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B42222131 : Blo 1754578 42222131 := bstep (se 1 (by rfl) ⟨31666598, by rfl⟩ : syracuseStep 42222131 = 63333197) B63333197
theorem B140616263 : Blo 1754578 140616263 := bstep (se 1 (by rfl) ⟨105462197, by rfl⟩ : syracuseStep 140616263 = 210924395) B210924395
theorem B21348947 : Blo 1754578 21348947 := bstep (se 1 (by rfl) ⟨16011710, by rfl⟩ : syracuseStep 21348947 = 32023421) B32023421
theorem B19989179 : Blo 1754578 19989179 := bstep (se 1 (by rfl) ⟨14991884, by rfl⟩ : syracuseStep 19989179 = 29983769) B29983769
theorem B4875223 : Blo 1754578 4875223 := bstep (se 1 (by rfl) ⟨3656417, by rfl⟩ : syracuseStep 4875223 = 7312835) B7312835
theorem B1975423 : Blo 1754578 1975423 := bstep (se 1 (by rfl) ⟨1481567, by rfl⟩ : syracuseStep 1975423 = 2963135) B2963135
theorem B1975783 : Blo 1754578 1975783 := bstep (se 1 (by rfl) ⟨1481837, by rfl⟩ : syracuseStep 1975783 = 2963675) B2963675
theorem B4441655 : Blo 1754578 4441655 := bstep (se 1 (by rfl) ⟨3331241, by rfl⟩ : syracuseStep 4441655 = 6662483) B6662483
theorem B2500151 : Blo 1754578 2500151 := bstep (se 1 (by rfl) ⟨1875113, by rfl⟩ : syracuseStep 2500151 = 3750227) B3750227
theorem B8889911 : Blo 1754578 8889911 := bstep (se 1 (by rfl) ⟨6667433, by rfl⟩ : syracuseStep 8889911 = 13334867) B13334867
theorem B194922125 : Blo 1754578 194922125 := bstep (se 3 (by rfl) ⟨36547898, by rfl⟩ : syracuseStep 194922125 = 73095797) B73095797
theorem B2221759 : Blo 1754578 2221759 := bstep (se 1 (by rfl) ⟨1666319, by rfl⟩ : syracuseStep 2221759 = 3332639) B3332639
theorem B7497481 : Blo 1754578 7497481 := bstep (se 2 (by rfl) ⟨2811555, by rfl⟩ : syracuseStep 7497481 = 5623111) B5623111
theorem B1754951 : Blo 1754578 1754951 := bstep (se 1 (by rfl) ⟨1316213, by rfl⟩ : syracuseStep 1754951 = 2632427) B2632427
theorem B1754983 : Blo 1754578 1754983 := bstep (se 1 (by rfl) ⟨1316237, by rfl⟩ : syracuseStep 1754983 = 2632475) B2632475
theorem B38471561 : Blo 1754578 38471561 := bstep (se 2 (by rfl) ⟨14426835, by rfl⟩ : syracuseStep 38471561 = 28853671) B28853671
theorem B4441999 : Blo 1754578 4441999 := bstep (se 1 (by rfl) ⟨3331499, by rfl⟩ : syracuseStep 4441999 = 6662999) B6662999
theorem B2632007 : Blo 1754578 2632007 := bstep (se 1 (by rfl) ⟨1974005, by rfl⟩ : syracuseStep 2632007 = 3948011) B3948011
theorem B18024785 : Blo 1754578 18024785 := bstep (se 2 (by rfl) ⟨6759294, by rfl⟩ : syracuseStep 18024785 = 13518589) B13518589
theorem B1755551 : Blo 1754578 1755551 := bstep (se 1 (by rfl) ⟨1316663, by rfl⟩ : syracuseStep 1755551 = 2633327) B2633327
theorem B1755623 : Blo 1754578 1755623 := bstep (se 1 (by rfl) ⟨1316717, by rfl⟩ : syracuseStep 1755623 = 2633435) B2633435
theorem B1755631 : Blo 1754578 1755631 := bstep (se 1 (by rfl) ⟨1316723, by rfl⟩ : syracuseStep 1755631 = 2633447) B2633447
theorem B18975491 : Blo 1754578 18975491 := bstep (se 1 (by rfl) ⟨14231618, by rfl⟩ : syracuseStep 18975491 = 28463237) B28463237
theorem B5925689 : Blo 1754578 5925689 := bstep (se 2 (by rfl) ⟨2222133, by rfl⟩ : syracuseStep 5925689 = 4444267) B4444267
theorem B8891207 : Blo 1754578 8891207 := bstep (se 1 (by rfl) ⟨6668405, by rfl⟩ : syracuseStep 8891207 = 13336811) B13336811
theorem B1756071 : Blo 1754578 1756071 := bstep (se 1 (by rfl) ⟨1317053, by rfl⟩ : syracuseStep 1756071 = 2634107) B2634107
theorem B5000143 : Blo 1754578 5000143 := bstep (se 1 (by rfl) ⟨3750107, by rfl⟩ : syracuseStep 5000143 = 7500215) B7500215
theorem B1756143 : Blo 1754578 1756143 := bstep (se 1 (by rfl) ⟨1317107, by rfl⟩ : syracuseStep 1756143 = 2634215) B2634215
theorem B2632841 : Blo 1754578 2632841 := bstep (se 2 (by rfl) ⟨987315, by rfl⟩ : syracuseStep 2632841 = 1974631) B1974631
theorem B2632871 : Blo 1754578 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B2632895 : Blo 1754578 2632895 := bstep (se 1 (by rfl) ⟨1974671, by rfl⟩ : syracuseStep 2632895 = 3949343) B3949343
theorem B1756391 : Blo 1754578 1756391 := bstep (se 1 (by rfl) ⟨1317293, by rfl⟩ : syracuseStep 1756391 = 2634587) B2634587
theorem B1756479 : Blo 1754578 1756479 := bstep (se 1 (by rfl) ⟨1317359, by rfl⟩ : syracuseStep 1756479 = 2634719) B2634719
theorem B1756519 : Blo 1754578 1756519 := bstep (se 1 (by rfl) ⟨1317389, by rfl⟩ : syracuseStep 1756519 = 2634779) B2634779
theorem B3952043 : Blo 1754578 3952043 := bstep (se 1 (by rfl) ⟨2964032, by rfl⟩ : syracuseStep 3952043 = 5928065) B5928065
theorem B4443599 : Blo 1754578 4443599 := bstep (se 1 (by rfl) ⟨3332699, by rfl⟩ : syracuseStep 4443599 = 6665399) B6665399
theorem B32026549 : Blo 1754578 32026549 := bstep (se 5 (by rfl) ⟨1501244, by rfl⟩ : syracuseStep 32026549 = 3002489) B3002489
theorem B2633705 : Blo 1754578 2633705 := bstep (se 2 (by rfl) ⟨987639, by rfl⟩ : syracuseStep 2633705 = 1975279) B1975279
theorem B2633759 : Blo 1754578 2633759 := bstep (se 1 (by rfl) ⟨1975319, by rfl⟩ : syracuseStep 2633759 = 3950639) B3950639
theorem B5001385 : Blo 1754578 5001385 := bstep (se 2 (by rfl) ⟨1875519, by rfl⟩ : syracuseStep 5001385 = 3751039) B3751039
theorem B5927147 : Blo 1754578 5927147 := bstep (se 1 (by rfl) ⟨4445360, by rfl⟩ : syracuseStep 5927147 = 8890721) B8890721
theorem B6664639 : Blo 1754578 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B3748331 : Blo 1754578 3748331 := bstep (se 1 (by rfl) ⟨2811248, by rfl⟩ : syracuseStep 3748331 = 5622497) B5622497
theorem B2634239 : Blo 1754578 2634239 := bstep (se 1 (by rfl) ⟨1975679, by rfl⟩ : syracuseStep 2634239 = 3951359) B3951359
theorem B15004187 : Blo 1754578 15004187 := bstep (se 1 (by rfl) ⟨11253140, by rfl⟩ : syracuseStep 15004187 = 22506281) B22506281
theorem B8885699 : Blo 1754578 8885699 := bstep (se 1 (by rfl) ⟨6664274, by rfl⟩ : syracuseStep 8885699 = 13328549) B13328549
theorem B2962939 : Blo 1754578 2962939 := bstep (se 1 (by rfl) ⟨2222204, by rfl⟩ : syracuseStep 2962939 = 4444409) B4444409
theorem B2963081 : Blo 1754578 2963081 := bstep (se 2 (by rfl) ⟨1111155, by rfl⟩ : syracuseStep 2963081 = 2222311) B2222311
theorem B4445887 : Blo 1754578 4445887 := bstep (se 1 (by rfl) ⟨3334415, by rfl⟩ : syracuseStep 4445887 = 6668831) B6668831
theorem B29996891 : Blo 1754578 29996891 := bstep (se 1 (by rfl) ⟨22497668, by rfl⟩ : syracuseStep 29996891 = 44995337) B44995337
theorem B144086941 : Blo 1754578 144086941 := bstep (se 3 (by rfl) ⟨27016301, by rfl⟩ : syracuseStep 144086941 = 54032603) B54032603
theorem B11253755 : Blo 1754578 11253755 := bstep (se 1 (by rfl) ⟨8440316, by rfl⟩ : syracuseStep 11253755 = 16880633) B16880633
theorem B6756803 : Blo 1754578 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B2963945 : Blo 1754578 2963945 := bstep (se 2 (by rfl) ⟨1111479, by rfl⟩ : syracuseStep 2963945 = 2222959) B2222959
theorem B5921747 : Blo 1754578 5921747 := bstep (se 1 (by rfl) ⟨4441310, by rfl⟩ : syracuseStep 5921747 = 8882621) B8882621
theorem B5921801 : Blo 1754578 5921801 := bstep (se 2 (by rfl) ⟨2220675, by rfl⟩ : syracuseStep 5921801 = 4441351) B4441351
theorem B5921855 : Blo 1754578 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B10001515 : Blo 1754578 10001515 := bstep (se 1 (by rfl) ⟨7501136, by rfl⟩ : syracuseStep 10001515 = 15002273) B15002273
theorem B3333383 : Blo 1754578 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B19987721 : Blo 1754578 19987721 := bstep (se 2 (by rfl) ⟨7495395, by rfl⟩ : syracuseStep 19987721 = 14990791) B14990791
theorem B13516379 : Blo 1754578 13516379 := bstep (se 1 (by rfl) ⟨10137284, by rfl⟩ : syracuseStep 13516379 = 20274569) B20274569
theorem B10002041 : Blo 1754578 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B3948371 : Blo 1754578 3948371 := bstep (se 1 (by rfl) ⟨2961278, by rfl⟩ : syracuseStep 3948371 = 5922557) B5922557
theorem B6668513 : Blo 1754578 6668513 := bstep (se 2 (by rfl) ⟨2500692, by rfl⟩ : syracuseStep 6668513 = 5001385) B5001385
theorem B2498887 : Blo 1754578 2498887 := bstep (se 1 (by rfl) ⟨1874165, by rfl⟩ : syracuseStep 2498887 = 3748331) B3748331
theorem B10002791 : Blo 1754578 10002791 := bstep (se 1 (by rfl) ⟨7502093, by rfl⟩ : syracuseStep 10002791 = 15004187) B15004187
theorem B28148087 : Blo 1754578 28148087 := bstep (se 1 (by rfl) ⟨21111065, by rfl⟩ : syracuseStep 28148087 = 42222131) B42222131
theorem B5923799 : Blo 1754578 5923799 := bstep (se 1 (by rfl) ⟨4442849, by rfl⟩ : syracuseStep 5923799 = 8885699) B8885699
theorem B1975387 : Blo 1754578 1975387 := bstep (se 1 (by rfl) ⟨1481540, by rfl⟩ : syracuseStep 1975387 = 2963081) B2963081
theorem B19997927 : Blo 1754578 19997927 := bstep (se 1 (by rfl) ⟨14998445, by rfl⟩ : syracuseStep 19997927 = 29996891) B29996891
theorem B1754671 : Blo 1754578 1754671 := bstep (se 1 (by rfl) ⟨1316003, by rfl⟩ : syracuseStep 1754671 = 2632007) B2632007
theorem B1975963 : Blo 1754578 1975963 := bstep (se 1 (by rfl) ⟨1481972, by rfl⟩ : syracuseStep 1975963 = 2963945) B2963945
theorem B12650327 : Blo 1754578 12650327 := bstep (se 1 (by rfl) ⟨9487745, by rfl⟩ : syracuseStep 12650327 = 18975491) B18975491
theorem B3950459 : Blo 1754578 3950459 := bstep (se 1 (by rfl) ⟨2962844, by rfl⟩ : syracuseStep 3950459 = 5925689) B5925689
theorem B3950585 : Blo 1754578 3950585 := bstep (se 2 (by rfl) ⟨1481469, by rfl⟩ : syracuseStep 3950585 = 2962939) B2962939
theorem B1755227 : Blo 1754578 1755227 := bstep (se 1 (by rfl) ⟨1316420, by rfl⟩ : syracuseStep 1755227 = 2632841) B2632841
theorem B1755247 : Blo 1754578 1755247 := bstep (se 1 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 1755247 = 2632871) B2632871
theorem B1755263 : Blo 1754578 1755263 := bstep (se 1 (by rfl) ⟨1316447, by rfl⟩ : syracuseStep 1755263 = 2632895) B2632895
theorem B2222255 : Blo 1754578 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B9996641 : Blo 1754578 9996641 := bstep (se 2 (by rfl) ⟨3748740, by rfl⟩ : syracuseStep 9996641 = 7497481) B7497481
theorem B2632247 : Blo 1754578 2632247 := bstep (se 1 (by rfl) ⟨1974185, by rfl⟩ : syracuseStep 2632247 = 3948371) B3948371
theorem B1755803 : Blo 1754578 1755803 := bstep (se 1 (by rfl) ⟨1316852, by rfl⟩ : syracuseStep 1755803 = 2633705) B2633705
theorem B30010013 : Blo 1754578 30010013 := bstep (se 3 (by rfl) ⟨5626877, by rfl⟩ : syracuseStep 30010013 = 11253755) B11253755
theorem B1755839 : Blo 1754578 1755839 := bstep (se 1 (by rfl) ⟨1316879, by rfl⟩ : syracuseStep 1755839 = 2633759) B2633759
theorem B2632457 : Blo 1754578 2632457 := bstep (se 2 (by rfl) ⟨987171, by rfl⟩ : syracuseStep 2632457 = 1974343) B1974343
theorem B3951431 : Blo 1754578 3951431 := bstep (se 1 (by rfl) ⟨2963573, by rfl⟩ : syracuseStep 3951431 = 5927147) B5927147
theorem B5925743 : Blo 1754578 5925743 := bstep (se 1 (by rfl) ⟨4444307, by rfl⟩ : syracuseStep 5925743 = 8888615) B8888615
theorem B1756159 : Blo 1754578 1756159 := bstep (se 1 (by rfl) ⟨1317119, by rfl⟩ : syracuseStep 1756159 = 2634239) B2634239
theorem B14232631 : Blo 1754578 14232631 := bstep (se 1 (by rfl) ⟨10674473, by rfl⟩ : syracuseStep 14232631 = 21348947) B21348947
theorem B2961103 : Blo 1754578 2961103 := bstep (se 1 (by rfl) ⟨2220827, by rfl⟩ : syracuseStep 2961103 = 4441655) B4441655
theorem B5926607 : Blo 1754578 5926607 := bstep (se 1 (by rfl) ⟨4444955, by rfl⟩ : syracuseStep 5926607 = 8889911) B8889911
theorem B6500297 : Blo 1754578 6500297 := bstep (se 2 (by rfl) ⟨2437611, by rfl⟩ : syracuseStep 6500297 = 4875223) B4875223
theorem B2633897 : Blo 1754578 2633897 := bstep (se 2 (by rfl) ⟨987711, by rfl⟩ : syracuseStep 2633897 = 1975423) B1975423
theorem B374976701 : Blo 1754578 374976701 := bstep (se 3 (by rfl) ⟨70308131, by rfl⟩ : syracuseStep 374976701 = 140616263) B140616263
theorem B5927471 : Blo 1754578 5927471 := bstep (se 1 (by rfl) ⟨4445603, by rfl⟩ : syracuseStep 5927471 = 8891207) B8891207
theorem B2634377 : Blo 1754578 2634377 := bstep (se 2 (by rfl) ⟨987891, by rfl⟩ : syracuseStep 2634377 = 1975783) B1975783
theorem B13325147 : Blo 1754578 13325147 := bstep (se 1 (by rfl) ⟨9993860, by rfl⟩ : syracuseStep 13325147 = 19987721) B19987721
theorem B2962345 : Blo 1754578 2962345 := bstep (se 2 (by rfl) ⟨1110879, by rfl⟩ : syracuseStep 2962345 = 2221759) B2221759
theorem B5927849 : Blo 1754578 5927849 := bstep (se 2 (by rfl) ⟨2222943, by rfl⟩ : syracuseStep 5927849 = 4445887) B4445887
theorem B2634695 : Blo 1754578 2634695 := bstep (se 1 (by rfl) ⟨1976021, by rfl⟩ : syracuseStep 2634695 = 3952043) B3952043
theorem B2962399 : Blo 1754578 2962399 := bstep (se 1 (by rfl) ⟨2221799, by rfl⟩ : syracuseStep 2962399 = 4443599) B4443599
theorem B192115921 : Blo 1754578 192115921 := bstep (se 2 (by rfl) ⟨72043470, by rfl⟩ : syracuseStep 192115921 = 144086941) B144086941
theorem B42702065 : Blo 1754578 42702065 := bstep (se 2 (by rfl) ⟨16013274, by rfl⟩ : syracuseStep 42702065 = 32026549) B32026549
theorem B4216411 : Blo 1754578 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B13326119 : Blo 1754578 13326119 := bstep (se 1 (by rfl) ⟨9994589, by rfl⟩ : syracuseStep 13326119 = 19989179) B19989179
theorem B8886185 : Blo 1754578 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B129948083 : Blo 1754578 129948083 := bstep (se 1 (by rfl) ⟨97461062, by rfl⟩ : syracuseStep 129948083 = 194922125) B194922125
theorem B25647707 : Blo 1754578 25647707 := bstep (se 1 (by rfl) ⟨19235780, by rfl⟩ : syracuseStep 25647707 = 38471561) B38471561
theorem B6666857 : Blo 1754578 6666857 := bstep (se 2 (by rfl) ⟨2500071, by rfl⟩ : syracuseStep 6666857 = 5000143) B5000143
theorem B13335353 : Blo 1754578 13335353 := bstep (se 2 (by rfl) ⟨5000757, by rfl⟩ : syracuseStep 13335353 = 10001515) B10001515
theorem B6667069 : Blo 1754578 6667069 := bstep (se 3 (by rfl) ⟨1250075, by rfl⟩ : syracuseStep 6667069 = 2500151) B2500151
theorem B12016523 : Blo 1754578 12016523 := bstep (se 1 (by rfl) ⟨9012392, by rfl⟩ : syracuseStep 12016523 = 18024785) B18024785
theorem B4504535 : Blo 1754578 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B3947831 : Blo 1754578 3947831 := bstep (se 1 (by rfl) ⟨2960873, by rfl⟩ : syracuseStep 3947831 = 5921747) B5921747
theorem B3947867 : Blo 1754578 3947867 := bstep (se 1 (by rfl) ⟨2960900, by rfl⟩ : syracuseStep 3947867 = 5921801) B5921801
theorem B3947903 : Blo 1754578 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B9010919 : Blo 1754578 9010919 := bstep (se 1 (by rfl) ⟨6758189, by rfl⟩ : syracuseStep 9010919 = 13516379) B13516379
theorem B6668027 : Blo 1754578 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B5922665 : Blo 1754578 5922665 := bstep (se 2 (by rfl) ⟨2220999, by rfl⟩ : syracuseStep 5922665 = 4441999) B4441999
theorem B6668527 : Blo 1754578 6668527 := bstep (se 1 (by rfl) ⟨5001395, by rfl⟩ : syracuseStep 6668527 = 10002791) B10002791
theorem B3949199 : Blo 1754578 3949199 := bstep (se 1 (by rfl) ⟨2961899, by rfl⟩ : syracuseStep 3949199 = 5923799) B5923799
theorem B28468043 : Blo 1754578 28468043 := bstep (se 1 (by rfl) ⟨21351032, by rfl⟩ : syracuseStep 28468043 = 42702065) B42702065
theorem B8889425 : Blo 1754578 8889425 := bstep (se 2 (by rfl) ⟨3333534, by rfl⟩ : syracuseStep 8889425 = 6667069) B6667069
theorem B3949793 : Blo 1754578 3949793 := bstep (se 2 (by rfl) ⟨1481172, by rfl⟩ : syracuseStep 3949793 = 2962345) B2962345
theorem B5924123 : Blo 1754578 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B3949865 : Blo 1754578 3949865 := bstep (se 2 (by rfl) ⟨1481199, by rfl⟩ : syracuseStep 3949865 = 2962399) B2962399
theorem B86632055 : Blo 1754578 86632055 := bstep (se 1 (by rfl) ⟨64974041, by rfl⟩ : syracuseStep 86632055 = 129948083) B129948083
theorem B1754831 : Blo 1754578 1754831 := bstep (se 1 (by rfl) ⟨1316123, by rfl⟩ : syracuseStep 1754831 = 2632247) B2632247
theorem B17098471 : Blo 1754578 17098471 := bstep (se 1 (by rfl) ⟨12823853, by rfl⟩ : syracuseStep 17098471 = 25647707) B25647707
theorem B20006675 : Blo 1754578 20006675 := bstep (se 1 (by rfl) ⟨15005006, by rfl⟩ : syracuseStep 20006675 = 30010013) B30010013
theorem B1754971 : Blo 1754578 1754971 := bstep (se 1 (by rfl) ⟨1316228, by rfl⟩ : syracuseStep 1754971 = 2632457) B2632457
theorem B8890235 : Blo 1754578 8890235 := bstep (se 1 (by rfl) ⟨6667676, by rfl⟩ : syracuseStep 8890235 = 13335353) B13335353
theorem B3950495 : Blo 1754578 3950495 := bstep (se 1 (by rfl) ⟨2962871, by rfl⟩ : syracuseStep 3950495 = 5925743) B5925743
theorem B5621881 : Blo 1754578 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B2631887 : Blo 1754578 2631887 := bstep (se 1 (by rfl) ⟨1973915, by rfl⟩ : syracuseStep 2631887 = 3947831) B3947831
theorem B2631911 : Blo 1754578 2631911 := bstep (se 1 (by rfl) ⟨1973933, by rfl⟩ : syracuseStep 2631911 = 3947867) B3947867
theorem B2631935 : Blo 1754578 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B3951071 : Blo 1754578 3951071 := bstep (se 1 (by rfl) ⟨2963303, by rfl⟩ : syracuseStep 3951071 = 5926607) B5926607
theorem B6007279 : Blo 1754578 6007279 := bstep (se 1 (by rfl) ⟨4505459, by rfl⟩ : syracuseStep 6007279 = 9010919) B9010919
theorem B1755931 : Blo 1754578 1755931 := bstep (se 1 (by rfl) ⟨1316948, by rfl⟩ : syracuseStep 1755931 = 2633897) B2633897
theorem B3951647 : Blo 1754578 3951647 := bstep (se 1 (by rfl) ⟨2963735, by rfl⟩ : syracuseStep 3951647 = 5927471) B5927471
theorem B1756251 : Blo 1754578 1756251 := bstep (se 1 (by rfl) ⟨1317188, by rfl⟩ : syracuseStep 1756251 = 2634377) B2634377
theorem B5926013 : Blo 1754578 5926013 := bstep (se 3 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 5926013 = 2222255) B2222255
theorem B8883431 : Blo 1754578 8883431 := bstep (se 1 (by rfl) ⟨6662573, by rfl⟩ : syracuseStep 8883431 = 13325147) B13325147
theorem B3951899 : Blo 1754578 3951899 := bstep (se 1 (by rfl) ⟨2963924, by rfl⟩ : syracuseStep 3951899 = 5927849) B5927849
theorem B1756463 : Blo 1754578 1756463 := bstep (se 1 (by rfl) ⟨1317347, by rfl⟩ : syracuseStep 1756463 = 2634695) B2634695
theorem B13331951 : Blo 1754578 13331951 := bstep (se 1 (by rfl) ⟨9998963, by rfl⟩ : syracuseStep 13331951 = 19997927) B19997927
theorem B8884079 : Blo 1754578 8884079 := bstep (se 1 (by rfl) ⟨6663059, by rfl⟩ : syracuseStep 8884079 = 13326119) B13326119
theorem B8433551 : Blo 1754578 8433551 := bstep (se 1 (by rfl) ⟨6325163, by rfl⟩ : syracuseStep 8433551 = 12650327) B12650327
theorem B2633639 : Blo 1754578 2633639 := bstep (se 1 (by rfl) ⟨1975229, by rfl⟩ : syracuseStep 2633639 = 3950459) B3950459
theorem B2633723 : Blo 1754578 2633723 := bstep (se 1 (by rfl) ⟨1975292, by rfl⟩ : syracuseStep 2633723 = 3950585) B3950585
theorem B18976841 : Blo 1754578 18976841 := bstep (se 2 (by rfl) ⟨7116315, by rfl⟩ : syracuseStep 18976841 = 14232631) B14232631
theorem B2633849 : Blo 1754578 2633849 := bstep (se 2 (by rfl) ⟨987693, by rfl⟩ : syracuseStep 2633849 = 1975387) B1975387
theorem B6664427 : Blo 1754578 6664427 := bstep (se 1 (by rfl) ⟨4998320, by rfl⟩ : syracuseStep 6664427 = 9996641) B9996641
theorem B4444571 : Blo 1754578 4444571 := bstep (se 1 (by rfl) ⟨3333428, by rfl⟩ : syracuseStep 4444571 = 6666857) B6666857
theorem B2634287 : Blo 1754578 2634287 := bstep (se 1 (by rfl) ⟨1975715, by rfl⟩ : syracuseStep 2634287 = 3951431) B3951431
theorem B3003023 : Blo 1754578 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B2634617 : Blo 1754578 2634617 := bstep (se 2 (by rfl) ⟨987981, by rfl⟩ : syracuseStep 2634617 = 1975963) B1975963
theorem B32044061 : Blo 1754578 32044061 := bstep (se 3 (by rfl) ⟨6008261, by rfl⟩ : syracuseStep 32044061 = 12016523) B12016523
theorem B4445351 : Blo 1754578 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B249984467 : Blo 1754578 249984467 := bstep (se 1 (by rfl) ⟨187488350, by rfl⟩ : syracuseStep 249984467 = 374976701) B374976701
theorem B4445675 : Blo 1754578 4445675 := bstep (se 1 (by rfl) ⟨3334256, by rfl⟩ : syracuseStep 4445675 = 6668513) B6668513
theorem B18765391 : Blo 1754578 18765391 := bstep (se 1 (by rfl) ⟨14074043, by rfl⟩ : syracuseStep 18765391 = 28148087) B28148087
theorem B3331849 : Blo 1754578 3331849 := bstep (se 2 (by rfl) ⟨1249443, by rfl⟩ : syracuseStep 3331849 = 2498887) B2498887
theorem B256154561 : Blo 1754578 256154561 := bstep (se 2 (by rfl) ⟨96057960, by rfl⟩ : syracuseStep 256154561 = 192115921) B192115921
theorem B3948137 : Blo 1754578 3948137 := bstep (se 2 (by rfl) ⟨1480551, by rfl⟩ : syracuseStep 3948137 = 2961103) B2961103
theorem B17334125 : Blo 1754578 17334125 := bstep (se 3 (by rfl) ⟨3250148, by rfl⟩ : syracuseStep 17334125 = 6500297) B6500297
theorem B3948443 : Blo 1754578 3948443 := bstep (se 1 (by rfl) ⟨2961332, by rfl⟩ : syracuseStep 3948443 = 5922665) B5922665
theorem B7495841 : Blo 1754578 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B3949415 : Blo 1754578 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B57754703 : Blo 1754578 57754703 := bstep (se 1 (by rfl) ⟨43316027, by rfl⟩ : syracuseStep 57754703 = 86632055) B86632055
theorem B13337783 : Blo 1754578 13337783 := bstep (se 1 (by rfl) ⟨10003337, by rfl⟩ : syracuseStep 13337783 = 20006675) B20006675
theorem B1754591 : Blo 1754578 1754591 := bstep (se 1 (by rfl) ⟨1315943, by rfl⟩ : syracuseStep 1754591 = 2631887) B2631887
theorem B1754607 : Blo 1754578 1754607 := bstep (se 1 (by rfl) ⟨1315955, by rfl⟩ : syracuseStep 1754607 = 2631911) B2631911
theorem B1754623 : Blo 1754578 1754623 := bstep (se 1 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 1754623 = 2631935) B2631935
theorem B3950675 : Blo 1754578 3950675 := bstep (se 1 (by rfl) ⟨2963006, by rfl⟩ : syracuseStep 3950675 = 5926013) B5926013
theorem B25020521 : Blo 1754578 25020521 := bstep (se 2 (by rfl) ⟨9382695, by rfl⟩ : syracuseStep 25020521 = 18765391) B18765391
theorem B4442465 : Blo 1754578 4442465 := bstep (se 2 (by rfl) ⟨1665924, by rfl⟩ : syracuseStep 4442465 = 3331849) B3331849
theorem B2632091 : Blo 1754578 2632091 := bstep (se 1 (by rfl) ⟨1974068, by rfl⟩ : syracuseStep 2632091 = 3948137) B3948137
theorem B5622367 : Blo 1754578 5622367 := bstep (se 1 (by rfl) ⟨4216775, by rfl⟩ : syracuseStep 5622367 = 8433551) B8433551
theorem B2632295 : Blo 1754578 2632295 := bstep (se 1 (by rfl) ⟨1974221, by rfl⟩ : syracuseStep 2632295 = 3948443) B3948443
theorem B1755759 : Blo 1754578 1755759 := bstep (se 1 (by rfl) ⟨1316819, by rfl⟩ : syracuseStep 1755759 = 2633639) B2633639
theorem B1755815 : Blo 1754578 1755815 := bstep (se 1 (by rfl) ⟨1316861, by rfl⟩ : syracuseStep 1755815 = 2633723) B2633723
theorem B12651227 : Blo 1754578 12651227 := bstep (se 1 (by rfl) ⟨9488420, by rfl⟩ : syracuseStep 12651227 = 18976841) B18976841
theorem B1755899 : Blo 1754578 1755899 := bstep (se 1 (by rfl) ⟨1316924, by rfl⟩ : syracuseStep 1755899 = 2633849) B2633849
theorem B4442951 : Blo 1754578 4442951 := bstep (se 1 (by rfl) ⟨3332213, by rfl⟩ : syracuseStep 4442951 = 6664427) B6664427
theorem B8891369 : Blo 1754578 8891369 := bstep (se 2 (by rfl) ⟨3334263, by rfl⟩ : syracuseStep 8891369 = 6668527) B6668527
theorem B1756191 : Blo 1754578 1756191 := bstep (se 1 (by rfl) ⟨1317143, by rfl⟩ : syracuseStep 1756191 = 2634287) B2634287
theorem B2632799 : Blo 1754578 2632799 := bstep (se 1 (by rfl) ⟨1974599, by rfl⟩ : syracuseStep 2632799 = 3949199) B3949199
theorem B2002015 : Blo 1754578 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B1756411 : Blo 1754578 1756411 := bstep (se 1 (by rfl) ⟨1317308, by rfl⟩ : syracuseStep 1756411 = 2634617) B2634617
theorem B5926283 : Blo 1754578 5926283 := bstep (se 1 (by rfl) ⟨4444712, by rfl⟩ : syracuseStep 5926283 = 8889425) B8889425
theorem B2633195 : Blo 1754578 2633195 := bstep (se 1 (by rfl) ⟨1974896, by rfl⟩ : syracuseStep 2633195 = 3949793) B3949793
theorem B2633243 : Blo 1754578 2633243 := bstep (se 1 (by rfl) ⟨1974932, by rfl⟩ : syracuseStep 2633243 = 3949865) B3949865
theorem B5926823 : Blo 1754578 5926823 := bstep (se 1 (by rfl) ⟨4445117, by rfl⟩ : syracuseStep 5926823 = 8890235) B8890235
theorem B2633663 : Blo 1754578 2633663 := bstep (se 1 (by rfl) ⟨1975247, by rfl⟩ : syracuseStep 2633663 = 3950495) B3950495
theorem B2634047 : Blo 1754578 2634047 := bstep (se 1 (by rfl) ⟨1975535, by rfl⟩ : syracuseStep 2634047 = 3951071) B3951071
theorem B2634431 : Blo 1754578 2634431 := bstep (se 1 (by rfl) ⟨1975823, by rfl⟩ : syracuseStep 2634431 = 3951647) B3951647
theorem B2634599 : Blo 1754578 2634599 := bstep (se 1 (by rfl) ⟨1975949, by rfl⟩ : syracuseStep 2634599 = 3951899) B3951899
theorem B11556083 : Blo 1754578 11556083 := bstep (se 1 (by rfl) ⟨8667062, by rfl⟩ : syracuseStep 11556083 = 17334125) B17334125
theorem B2963047 : Blo 1754578 2963047 := bstep (se 1 (by rfl) ⟨2222285, by rfl⟩ : syracuseStep 2963047 = 4444571) B4444571
theorem B18978695 : Blo 1754578 18978695 := bstep (se 1 (by rfl) ⟨14234021, by rfl⟩ : syracuseStep 18978695 = 28468043) B28468043
theorem B8009705 : Blo 1754578 8009705 := bstep (se 2 (by rfl) ⟨3003639, by rfl⟩ : syracuseStep 8009705 = 6007279) B6007279
theorem B21362707 : Blo 1754578 21362707 := bstep (se 1 (by rfl) ⟨16022030, by rfl⟩ : syracuseStep 21362707 = 32044061) B32044061
theorem B2963567 : Blo 1754578 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B166656311 : Blo 1754578 166656311 := bstep (se 1 (by rfl) ⟨124992233, by rfl⟩ : syracuseStep 166656311 = 249984467) B249984467
theorem B2963783 : Blo 1754578 2963783 := bstep (se 1 (by rfl) ⟨2222837, by rfl⟩ : syracuseStep 2963783 = 4445675) B4445675
theorem B91191845 : Blo 1754578 91191845 := bstep (se 4 (by rfl) ⟨8549235, by rfl⟩ : syracuseStep 91191845 = 17098471) B17098471
theorem B170769707 : Blo 1754578 170769707 := bstep (se 1 (by rfl) ⟨128077280, by rfl⟩ : syracuseStep 170769707 = 256154561) B256154561
theorem B5922287 : Blo 1754578 5922287 := bstep (se 1 (by rfl) ⟨4441715, by rfl⟩ : syracuseStep 5922287 = 8883431) B8883431
theorem B8887967 : Blo 1754578 8887967 := bstep (se 1 (by rfl) ⟨6665975, by rfl⟩ : syracuseStep 8887967 = 13331951) B13331951
theorem B5922719 : Blo 1754578 5922719 := bstep (se 1 (by rfl) ⟨4442039, by rfl⟩ : syracuseStep 5922719 = 8884079) B8884079
theorem B28483609 : Blo 1754578 28483609 := bstep (se 2 (by rfl) ⟨10681353, by rfl⟩ : syracuseStep 28483609 = 21362707) B21362707
theorem B4997227 : Blo 1754578 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B38503135 : Blo 1754578 38503135 := bstep (se 1 (by rfl) ⟨28877351, by rfl⟩ : syracuseStep 38503135 = 57754703) B57754703
theorem B7496489 : Blo 1754578 7496489 := bstep (se 2 (by rfl) ⟨2811183, by rfl⟩ : syracuseStep 7496489 = 5622367) B5622367
theorem B16680347 : Blo 1754578 16680347 := bstep (se 1 (by rfl) ⟨12510260, by rfl⟩ : syracuseStep 16680347 = 25020521) B25020521
theorem B1975711 : Blo 1754578 1975711 := bstep (se 1 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 1975711 = 2963567) B2963567
theorem B1975855 : Blo 1754578 1975855 := bstep (se 1 (by rfl) ⟨1481891, by rfl⟩ : syracuseStep 1975855 = 2963783) B2963783
theorem B1754727 : Blo 1754578 1754727 := bstep (se 1 (by rfl) ⟨1316045, by rfl⟩ : syracuseStep 1754727 = 2632091) B2632091
theorem B60794563 : Blo 1754578 60794563 := bstep (se 1 (by rfl) ⟨45595922, by rfl⟩ : syracuseStep 60794563 = 91191845) B91191845
theorem B1754863 : Blo 1754578 1754863 := bstep (se 1 (by rfl) ⟨1316147, by rfl⟩ : syracuseStep 1754863 = 2632295) B2632295
theorem B1755199 : Blo 1754578 1755199 := bstep (se 1 (by rfl) ⟨1316399, by rfl⟩ : syracuseStep 1755199 = 2632799) B2632799
theorem B3950729 : Blo 1754578 3950729 := bstep (se 2 (by rfl) ⟨1481523, by rfl⟩ : syracuseStep 3950729 = 2963047) B2963047
theorem B113846471 : Blo 1754578 113846471 := bstep (se 1 (by rfl) ⟨85384853, by rfl⟩ : syracuseStep 113846471 = 170769707) B170769707
theorem B3950855 : Blo 1754578 3950855 := bstep (se 1 (by rfl) ⟨2963141, by rfl⟩ : syracuseStep 3950855 = 5926283) B5926283
theorem B1755463 : Blo 1754578 1755463 := bstep (se 1 (by rfl) ⟨1316597, by rfl⟩ : syracuseStep 1755463 = 2633195) B2633195
theorem B1755495 : Blo 1754578 1755495 := bstep (se 1 (by rfl) ⟨1316621, by rfl⟩ : syracuseStep 1755495 = 2633243) B2633243
theorem B5925311 : Blo 1754578 5925311 := bstep (se 1 (by rfl) ⟨4443983, by rfl⟩ : syracuseStep 5925311 = 8887967) B8887967
theorem B21359213 : Blo 1754578 21359213 := bstep (se 3 (by rfl) ⟨4004852, by rfl⟩ : syracuseStep 21359213 = 8009705) B8009705
theorem B3951215 : Blo 1754578 3951215 := bstep (se 1 (by rfl) ⟨2963411, by rfl⟩ : syracuseStep 3951215 = 5926823) B5926823
theorem B1755775 : Blo 1754578 1755775 := bstep (se 1 (by rfl) ⟨1316831, by rfl⟩ : syracuseStep 1755775 = 2633663) B2633663
theorem B1756031 : Blo 1754578 1756031 := bstep (se 1 (by rfl) ⟨1317023, by rfl⟩ : syracuseStep 1756031 = 2634047) B2634047
theorem B1756287 : Blo 1754578 1756287 := bstep (se 1 (by rfl) ⟨1317215, by rfl⟩ : syracuseStep 1756287 = 2634431) B2634431
theorem B10677413 : Blo 1754578 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B2632943 : Blo 1754578 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B1756399 : Blo 1754578 1756399 := bstep (se 1 (by rfl) ⟨1317299, by rfl⟩ : syracuseStep 1756399 = 2634599) B2634599
theorem B8891855 : Blo 1754578 8891855 := bstep (se 1 (by rfl) ⟨6668891, by rfl⟩ : syracuseStep 8891855 = 13337783) B13337783
theorem B7704055 : Blo 1754578 7704055 := bstep (se 1 (by rfl) ⟨5778041, by rfl⟩ : syracuseStep 7704055 = 11556083) B11556083
theorem B12652463 : Blo 1754578 12652463 := bstep (se 1 (by rfl) ⟨9489347, by rfl⟩ : syracuseStep 12652463 = 18978695) B18978695
theorem B2633783 : Blo 1754578 2633783 := bstep (se 1 (by rfl) ⟨1975337, by rfl⟩ : syracuseStep 2633783 = 3950675) B3950675
theorem B111104207 : Blo 1754578 111104207 := bstep (se 1 (by rfl) ⟨83328155, by rfl⟩ : syracuseStep 111104207 = 166656311) B166656311
theorem B2961643 : Blo 1754578 2961643 := bstep (se 1 (by rfl) ⟨2221232, by rfl⟩ : syracuseStep 2961643 = 4442465) B4442465
theorem B8434151 : Blo 1754578 8434151 := bstep (se 1 (by rfl) ⟨6325613, by rfl⟩ : syracuseStep 8434151 = 12651227) B12651227
theorem B2961967 : Blo 1754578 2961967 := bstep (se 1 (by rfl) ⟨2221475, by rfl⟩ : syracuseStep 2961967 = 4442951) B4442951
theorem B5927579 : Blo 1754578 5927579 := bstep (se 1 (by rfl) ⟨4445684, by rfl⟩ : syracuseStep 5927579 = 8891369) B8891369
theorem B3948191 : Blo 1754578 3948191 := bstep (se 1 (by rfl) ⟨2961143, by rfl⟩ : syracuseStep 3948191 = 5922287) B5922287
theorem B3948479 : Blo 1754578 3948479 := bstep (se 1 (by rfl) ⟨2961359, by rfl⟩ : syracuseStep 3948479 = 5922719) B5922719
theorem B37978145 : Blo 1754578 37978145 := bstep (se 2 (by rfl) ⟨14241804, by rfl⟩ : syracuseStep 37978145 = 28483609) B28483609
theorem B3948857 : Blo 1754578 3948857 := bstep (se 2 (by rfl) ⟨1480821, by rfl⟩ : syracuseStep 3948857 = 2961643) B2961643
theorem B3949289 : Blo 1754578 3949289 := bstep (se 2 (by rfl) ⟨1480983, by rfl⟩ : syracuseStep 3949289 = 2961967) B2961967
theorem B3950207 : Blo 1754578 3950207 := bstep (se 1 (by rfl) ⟨2962655, by rfl⟩ : syracuseStep 3950207 = 5925311) B5925311
theorem B14239475 : Blo 1754578 14239475 := bstep (se 1 (by rfl) ⟨10679606, by rfl⟩ : syracuseStep 14239475 = 21359213) B21359213
theorem B19990637 : Blo 1754578 19990637 := bstep (se 3 (by rfl) ⟨3748244, by rfl⟩ : syracuseStep 19990637 = 7496489) B7496489
theorem B1755295 : Blo 1754578 1755295 := bstep (se 1 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 1755295 = 2632943) B2632943
theorem B2632127 : Blo 1754578 2632127 := bstep (se 1 (by rfl) ⟨1974095, by rfl⟩ : syracuseStep 2632127 = 3948191) B3948191
theorem B2632319 : Blo 1754578 2632319 := bstep (se 1 (by rfl) ⟨1974239, by rfl⟩ : syracuseStep 2632319 = 3948479) B3948479
theorem B1755855 : Blo 1754578 1755855 := bstep (se 1 (by rfl) ⟨1316891, by rfl⟩ : syracuseStep 1755855 = 2633783) B2633783
theorem B6662969 : Blo 1754578 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B5622767 : Blo 1754578 5622767 := bstep (se 1 (by rfl) ⟨4217075, by rfl⟩ : syracuseStep 5622767 = 8434151) B8434151
theorem B3951719 : Blo 1754578 3951719 := bstep (se 1 (by rfl) ⟨2963789, by rfl⟩ : syracuseStep 3951719 = 5927579) B5927579
theorem B11120231 : Blo 1754578 11120231 := bstep (se 1 (by rfl) ⟨8340173, by rfl⟩ : syracuseStep 11120231 = 16680347) B16680347
theorem B2633819 : Blo 1754578 2633819 := bstep (se 1 (by rfl) ⟨1975364, by rfl⟩ : syracuseStep 2633819 = 3950729) B3950729
theorem B2633903 : Blo 1754578 2633903 := bstep (se 1 (by rfl) ⟨1975427, by rfl⟩ : syracuseStep 2633903 = 3950855) B3950855
theorem B2634143 : Blo 1754578 2634143 := bstep (se 1 (by rfl) ⟨1975607, by rfl⟩ : syracuseStep 2634143 = 3951215) B3951215
theorem B2634281 : Blo 1754578 2634281 := bstep (se 2 (by rfl) ⟨987855, by rfl⟩ : syracuseStep 2634281 = 1975711) B1975711
theorem B2634473 : Blo 1754578 2634473 := bstep (se 2 (by rfl) ⟨987927, by rfl⟩ : syracuseStep 2634473 = 1975855) B1975855
theorem B5927903 : Blo 1754578 5927903 := bstep (se 1 (by rfl) ⟨4445927, by rfl⟩ : syracuseStep 5927903 = 8891855) B8891855
theorem B8434975 : Blo 1754578 8434975 := bstep (se 1 (by rfl) ⟨6326231, by rfl⟩ : syracuseStep 8434975 = 12652463) B12652463
theorem B41088293 : Blo 1754578 41088293 := bstep (se 4 (by rfl) ⟨3852027, by rfl⟩ : syracuseStep 41088293 = 7704055) B7704055
theorem B74069471 : Blo 1754578 74069471 := bstep (se 1 (by rfl) ⟨55552103, by rfl⟩ : syracuseStep 74069471 = 111104207) B111104207
theorem B51337513 : Blo 1754578 51337513 := bstep (se 2 (by rfl) ⟨19251567, by rfl⟩ : syracuseStep 51337513 = 38503135) B38503135
theorem B75897647 : Blo 1754578 75897647 := bstep (se 1 (by rfl) ⟨56923235, by rfl⟩ : syracuseStep 75897647 = 113846471) B113846471
theorem B7118275 : Blo 1754578 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B81059417 : Blo 1754578 81059417 := bstep (se 2 (by rfl) ⟨30397281, by rfl⟩ : syracuseStep 81059417 = 60794563) B60794563
theorem B1754751 : Blo 1754578 1754751 := bstep (se 1 (by rfl) ⟨1316063, by rfl⟩ : syracuseStep 1754751 = 2632127) B2632127
theorem B1754879 : Blo 1754578 1754879 := bstep (se 1 (by rfl) ⟨1316159, by rfl⟩ : syracuseStep 1754879 = 2632319) B2632319
theorem B4441979 : Blo 1754578 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1755879 : Blo 1754578 1755879 := bstep (se 1 (by rfl) ⟨1316909, by rfl⟩ : syracuseStep 1755879 = 2633819) B2633819
theorem B1755935 : Blo 1754578 1755935 := bstep (se 1 (by rfl) ⟨1316951, by rfl⟩ : syracuseStep 1755935 = 2633903) B2633903
theorem B2632571 : Blo 1754578 2632571 := bstep (se 1 (by rfl) ⟨1974428, by rfl⟩ : syracuseStep 2632571 = 3948857) B3948857
theorem B1756095 : Blo 1754578 1756095 := bstep (se 1 (by rfl) ⟨1317071, by rfl⟩ : syracuseStep 1756095 = 2634143) B2634143
theorem B1756187 : Blo 1754578 1756187 := bstep (se 1 (by rfl) ⟨1317140, by rfl⟩ : syracuseStep 1756187 = 2634281) B2634281
theorem B2632859 : Blo 1754578 2632859 := bstep (se 1 (by rfl) ⟨1974644, by rfl⟩ : syracuseStep 2632859 = 3949289) B3949289
theorem B1756315 : Blo 1754578 1756315 := bstep (se 1 (by rfl) ⟨1317236, by rfl⟩ : syracuseStep 1756315 = 2634473) B2634473
theorem B3951935 : Blo 1754578 3951935 := bstep (se 1 (by rfl) ⟨2963951, by rfl⟩ : syracuseStep 3951935 = 5927903) B5927903
theorem B2633471 : Blo 1754578 2633471 := bstep (se 1 (by rfl) ⟨1975103, by rfl⟩ : syracuseStep 2633471 = 3950207) B3950207
theorem B50598431 : Blo 1754578 50598431 := bstep (se 1 (by rfl) ⟨37948823, by rfl⟩ : syracuseStep 50598431 = 75897647) B75897647
theorem B9491033 : Blo 1754578 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B3748511 : Blo 1754578 3748511 := bstep (se 1 (by rfl) ⟨2811383, by rfl⟩ : syracuseStep 3748511 = 5622767) B5622767
theorem B2634479 : Blo 1754578 2634479 := bstep (se 1 (by rfl) ⟨1975859, by rfl⟩ : syracuseStep 2634479 = 3951719) B3951719
theorem B54039611 : Blo 1754578 54039611 := bstep (se 1 (by rfl) ⟨40529708, by rfl⟩ : syracuseStep 54039611 = 81059417) B81059417
theorem B25318763 : Blo 1754578 25318763 := bstep (se 1 (by rfl) ⟨18989072, by rfl⟩ : syracuseStep 25318763 = 37978145) B37978145
theorem B68450017 : Blo 1754578 68450017 := bstep (se 2 (by rfl) ⟨25668756, by rfl⟩ : syracuseStep 68450017 = 51337513) B51337513
theorem B27392195 : Blo 1754578 27392195 := bstep (se 1 (by rfl) ⟨20544146, by rfl⟩ : syracuseStep 27392195 = 41088293) B41088293
theorem B49379647 : Blo 1754578 49379647 := bstep (se 1 (by rfl) ⟨37034735, by rfl⟩ : syracuseStep 49379647 = 74069471) B74069471
theorem B9492983 : Blo 1754578 9492983 := bstep (se 1 (by rfl) ⟨7119737, by rfl⟩ : syracuseStep 9492983 = 14239475) B14239475
theorem B13327091 : Blo 1754578 13327091 := bstep (se 1 (by rfl) ⟨9995318, by rfl⟩ : syracuseStep 13327091 = 19990637) B19990637
theorem B11246633 : Blo 1754578 11246633 := bstep (se 2 (by rfl) ⟨4217487, by rfl⟩ : syracuseStep 11246633 = 8434975) B8434975
theorem B7413487 : Blo 1754578 7413487 := bstep (se 1 (by rfl) ⟨5560115, by rfl⟩ : syracuseStep 7413487 = 11120231) B11120231
theorem B2499007 : Blo 1754578 2499007 := bstep (se 1 (by rfl) ⟨1874255, by rfl⟩ : syracuseStep 2499007 = 3748511) B3748511
theorem B18261463 : Blo 1754578 18261463 := bstep (se 1 (by rfl) ⟨13696097, by rfl⟩ : syracuseStep 18261463 = 27392195) B27392195
theorem B1755047 : Blo 1754578 1755047 := bstep (se 1 (by rfl) ⟨1316285, by rfl⟩ : syracuseStep 1755047 = 2632571) B2632571
theorem B7497755 : Blo 1754578 7497755 := bstep (se 1 (by rfl) ⟨5623316, by rfl⟩ : syracuseStep 7497755 = 11246633) B11246633
theorem B1755239 : Blo 1754578 1755239 := bstep (se 1 (by rfl) ⟨1316429, by rfl⟩ : syracuseStep 1755239 = 2632859) B2632859
theorem B1755647 : Blo 1754578 1755647 := bstep (se 1 (by rfl) ⟨1316735, by rfl⟩ : syracuseStep 1755647 = 2633471) B2633471
theorem B1756319 : Blo 1754578 1756319 := bstep (se 1 (by rfl) ⟨1317239, by rfl⟩ : syracuseStep 1756319 = 2634479) B2634479
theorem B16879175 : Blo 1754578 16879175 := bstep (se 1 (by rfl) ⟨12659381, by rfl⟩ : syracuseStep 16879175 = 25318763) B25318763
theorem B39538597 : Blo 1754578 39538597 := bstep (se 4 (by rfl) ⟨3706743, by rfl⟩ : syracuseStep 39538597 = 7413487) B7413487
theorem B2961319 : Blo 1754578 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B25309421 : Blo 1754578 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B6328655 : Blo 1754578 6328655 := bstep (se 1 (by rfl) ⟨4746491, by rfl⟩ : syracuseStep 6328655 = 9492983) B9492983
theorem B8884727 : Blo 1754578 8884727 := bstep (se 1 (by rfl) ⟨6663545, by rfl⟩ : syracuseStep 8884727 = 13327091) B13327091
theorem B2634623 : Blo 1754578 2634623 := bstep (se 1 (by rfl) ⟨1975967, by rfl⟩ : syracuseStep 2634623 = 3951935) B3951935
theorem B33732287 : Blo 1754578 33732287 := bstep (se 1 (by rfl) ⟨25299215, by rfl⟩ : syracuseStep 33732287 = 50598431) B50598431
theorem B36026407 : Blo 1754578 36026407 := bstep (se 1 (by rfl) ⟨27019805, by rfl⟩ : syracuseStep 36026407 = 54039611) B54039611
theorem B1053432469 : Blo 1754578 1053432469 := bstep (se 6 (by rfl) ⟨24689823, by rfl⟩ : syracuseStep 1053432469 = 49379647) B49379647
theorem B91266689 : Blo 1754578 91266689 := bstep (se 2 (by rfl) ⟨34225008, by rfl⟩ : syracuseStep 91266689 = 68450017) B68450017
theorem B4219103 : Blo 1754578 4219103 := bstep (se 1 (by rfl) ⟨3164327, by rfl⟩ : syracuseStep 4219103 = 6328655) B6328655
theorem B5923151 : Blo 1754578 5923151 := bstep (se 1 (by rfl) ⟨4442363, by rfl⟩ : syracuseStep 5923151 = 8884727) B8884727
theorem B1404576625 : Blo 1754578 1404576625 := bstep (se 2 (by rfl) ⟨526716234, by rfl⟩ : syracuseStep 1404576625 = 1053432469) B1053432469
theorem B22488191 : Blo 1754578 22488191 := bstep (se 1 (by rfl) ⟨16866143, by rfl⟩ : syracuseStep 22488191 = 33732287) B33732287
theorem B4998503 : Blo 1754578 4998503 := bstep (se 1 (by rfl) ⟨3748877, by rfl⟩ : syracuseStep 4998503 = 7497755) B7497755
theorem B24348617 : Blo 1754578 24348617 := bstep (se 2 (by rfl) ⟨9130731, by rfl⟩ : syracuseStep 24348617 = 18261463) B18261463
theorem B60844459 : Blo 1754578 60844459 := bstep (se 1 (by rfl) ⟨45633344, by rfl⟩ : syracuseStep 60844459 = 91266689) B91266689
theorem B52718129 : Blo 1754578 52718129 := bstep (se 2 (by rfl) ⟨19769298, by rfl⟩ : syracuseStep 52718129 = 39538597) B39538597
theorem B1756415 : Blo 1754578 1756415 := bstep (se 1 (by rfl) ⟨1317311, by rfl⟩ : syracuseStep 1756415 = 2634623) B2634623
theorem B11252783 : Blo 1754578 11252783 := bstep (se 1 (by rfl) ⟨8439587, by rfl⟩ : syracuseStep 11252783 = 16879175) B16879175
theorem B48035209 : Blo 1754578 48035209 := bstep (se 2 (by rfl) ⟨18013203, by rfl⟩ : syracuseStep 48035209 = 36026407) B36026407
theorem B16872947 : Blo 1754578 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B3332009 : Blo 1754578 3332009 := bstep (se 2 (by rfl) ⟨1249503, by rfl⟩ : syracuseStep 3332009 = 2499007) B2499007
theorem B3948425 : Blo 1754578 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B3948767 : Blo 1754578 3948767 := bstep (se 1 (by rfl) ⟨2961575, by rfl⟩ : syracuseStep 3948767 = 5923151) B5923151
theorem B81125945 : Blo 1754578 81125945 := bstep (se 2 (by rfl) ⟨30422229, by rfl⟩ : syracuseStep 81125945 = 60844459) B60844459
theorem B14992127 : Blo 1754578 14992127 := bstep (se 1 (by rfl) ⟨11244095, by rfl⟩ : syracuseStep 14992127 = 22488191) B22488191
theorem B11248631 : Blo 1754578 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B2221339 : Blo 1754578 2221339 := bstep (se 1 (by rfl) ⟨1666004, by rfl⟩ : syracuseStep 2221339 = 3332009) B3332009
theorem B35145419 : Blo 1754578 35145419 := bstep (se 1 (by rfl) ⟨26359064, by rfl⟩ : syracuseStep 35145419 = 52718129) B52718129
theorem B64046945 : Blo 1754578 64046945 := bstep (se 2 (by rfl) ⟨24017604, by rfl⟩ : syracuseStep 64046945 = 48035209) B48035209
theorem B2632283 : Blo 1754578 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B2812735 : Blo 1754578 2812735 := bstep (se 1 (by rfl) ⟨2109551, by rfl⟩ : syracuseStep 2812735 = 4219103) B4219103
theorem B1872768833 : Blo 1754578 1872768833 := bstep (se 2 (by rfl) ⟨702288312, by rfl⟩ : syracuseStep 1872768833 = 1404576625) B1404576625
theorem B16232411 : Blo 1754578 16232411 := bstep (se 1 (by rfl) ⟨12174308, by rfl⟩ : syracuseStep 16232411 = 24348617) B24348617
theorem B7501855 : Blo 1754578 7501855 := bstep (se 1 (by rfl) ⟨5626391, by rfl⟩ : syracuseStep 7501855 = 11252783) B11252783
theorem B3332335 : Blo 1754578 3332335 := bstep (se 1 (by rfl) ⟨2499251, by rfl⟩ : syracuseStep 3332335 = 4998503) B4998503
theorem B10002473 : Blo 1754578 10002473 := bstep (se 2 (by rfl) ⟨3750927, by rfl⟩ : syracuseStep 10002473 = 7501855) B7501855
theorem B54083963 : Blo 1754578 54083963 := bstep (se 1 (by rfl) ⟨40562972, by rfl⟩ : syracuseStep 54083963 = 81125945) B81125945
theorem B9994751 : Blo 1754578 9994751 := bstep (se 1 (by rfl) ⟨7496063, by rfl⟩ : syracuseStep 9994751 = 14992127) B14992127
theorem B42697963 : Blo 1754578 42697963 := bstep (se 1 (by rfl) ⟨32023472, by rfl⟩ : syracuseStep 42697963 = 64046945) B64046945
theorem B1754855 : Blo 1754578 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B374884469 : Blo 1754578 374884469 := bstep (se 5 (by rfl) ⟨17572709, by rfl⟩ : syracuseStep 374884469 = 35145419) B35145419
theorem B1248512555 : Blo 1754578 1248512555 := bstep (se 1 (by rfl) ⟨936384416, by rfl⟩ : syracuseStep 1248512555 = 1872768833) B1872768833
theorem B2632511 : Blo 1754578 2632511 := bstep (se 1 (by rfl) ⟨1974383, by rfl⟩ : syracuseStep 2632511 = 3948767) B3948767
theorem B4443113 : Blo 1754578 4443113 := bstep (se 2 (by rfl) ⟨1666167, by rfl⟩ : syracuseStep 4443113 = 3332335) B3332335
theorem B7499087 : Blo 1754578 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B2961785 : Blo 1754578 2961785 := bstep (se 2 (by rfl) ⟨1110669, by rfl⟩ : syracuseStep 2961785 = 2221339) B2221339
theorem B3750313 : Blo 1754578 3750313 := bstep (se 2 (by rfl) ⟨1406367, by rfl⟩ : syracuseStep 3750313 = 2812735) B2812735
theorem B10821607 : Blo 1754578 10821607 := bstep (se 1 (by rfl) ⟨8116205, by rfl⟩ : syracuseStep 10821607 = 16232411) B16232411
theorem B6668315 : Blo 1754578 6668315 := bstep (se 1 (by rfl) ⟨5001236, by rfl⟩ : syracuseStep 6668315 = 10002473) B10002473
theorem B1974523 : Blo 1754578 1974523 := bstep (se 1 (by rfl) ⟨1480892, by rfl⟩ : syracuseStep 1974523 = 2961785) B2961785
theorem B249922979 : Blo 1754578 249922979 := bstep (se 1 (by rfl) ⟨187442234, by rfl⟩ : syracuseStep 249922979 = 374884469) B374884469
theorem B832341703 : Blo 1754578 832341703 := bstep (se 1 (by rfl) ⟨624256277, by rfl⟩ : syracuseStep 832341703 = 1248512555) B1248512555
theorem B1755007 : Blo 1754578 1755007 := bstep (se 1 (by rfl) ⟨1316255, by rfl⟩ : syracuseStep 1755007 = 2632511) B2632511
theorem B4999391 : Blo 1754578 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B57715237 : Blo 1754578 57715237 := bstep (se 4 (by rfl) ⟨5410803, by rfl⟩ : syracuseStep 57715237 = 10821607) B10821607
theorem B36055975 : Blo 1754578 36055975 := bstep (se 1 (by rfl) ⟨27041981, by rfl⟩ : syracuseStep 36055975 = 54083963) B54083963
theorem B6663167 : Blo 1754578 6663167 := bstep (se 1 (by rfl) ⟨4997375, by rfl⟩ : syracuseStep 6663167 = 9994751) B9994751
theorem B5000417 : Blo 1754578 5000417 := bstep (se 2 (by rfl) ⟨1875156, by rfl⟩ : syracuseStep 5000417 = 3750313) B3750313
theorem B56930617 : Blo 1754578 56930617 := bstep (se 2 (by rfl) ⟨21348981, by rfl⟩ : syracuseStep 56930617 = 42697963) B42697963
theorem B2962075 : Blo 1754578 2962075 := bstep (se 1 (by rfl) ⟨2221556, by rfl⟩ : syracuseStep 2962075 = 4443113) B4443113
theorem B75907489 : Blo 1754578 75907489 := bstep (se 2 (by rfl) ⟨28465308, by rfl⟩ : syracuseStep 75907489 = 56930617) B56930617
theorem B3949433 : Blo 1754578 3949433 := bstep (se 2 (by rfl) ⟨1481037, by rfl⟩ : syracuseStep 3949433 = 2962075) B2962075
theorem B4442111 : Blo 1754578 4442111 := bstep (se 1 (by rfl) ⟨3331583, by rfl⟩ : syracuseStep 4442111 = 6663167) B6663167
theorem B1109788937 : Blo 1754578 1109788937 := bstep (se 2 (by rfl) ⟨416170851, by rfl⟩ : syracuseStep 1109788937 = 832341703) B832341703
theorem B2632697 : Blo 1754578 2632697 := bstep (se 2 (by rfl) ⟨987261, by rfl⟩ : syracuseStep 2632697 = 1974523) B1974523
theorem B48074633 : Blo 1754578 48074633 := bstep (se 2 (by rfl) ⟨18027987, by rfl⟩ : syracuseStep 48074633 = 36055975) B36055975
theorem B4445543 : Blo 1754578 4445543 := bstep (se 1 (by rfl) ⟨3334157, by rfl⟩ : syracuseStep 4445543 = 6668315) B6668315
theorem B76953649 : Blo 1754578 76953649 := bstep (se 2 (by rfl) ⟨28857618, by rfl⟩ : syracuseStep 76953649 = 57715237) B57715237
theorem B166615319 : Blo 1754578 166615319 := bstep (se 1 (by rfl) ⟨124961489, by rfl⟩ : syracuseStep 166615319 = 249922979) B249922979
theorem B3332927 : Blo 1754578 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B3333611 : Blo 1754578 3333611 := bstep (se 1 (by rfl) ⟨2500208, by rfl⟩ : syracuseStep 3333611 = 5000417) B5000417
theorem B102604865 : Blo 1754578 102604865 := bstep (se 2 (by rfl) ⟨38476824, by rfl⟩ : syracuseStep 102604865 = 76953649) B76953649
theorem B1755131 : Blo 1754578 1755131 := bstep (se 1 (by rfl) ⟨1316348, by rfl⟩ : syracuseStep 1755131 = 2632697) B2632697
theorem B2222407 : Blo 1754578 2222407 := bstep (se 1 (by rfl) ⟨1666805, by rfl⟩ : syracuseStep 2222407 = 3333611) B3333611
theorem B32049755 : Blo 1754578 32049755 := bstep (se 1 (by rfl) ⟨24037316, by rfl⟩ : syracuseStep 32049755 = 48074633) B48074633
theorem B2632955 : Blo 1754578 2632955 := bstep (se 1 (by rfl) ⟨1974716, by rfl⟩ : syracuseStep 2632955 = 3949433) B3949433
theorem B2961407 : Blo 1754578 2961407 := bstep (se 1 (by rfl) ⟨2221055, by rfl⟩ : syracuseStep 2961407 = 4442111) B4442111
theorem B101209985 : Blo 1754578 101209985 := bstep (se 2 (by rfl) ⟨37953744, by rfl⟩ : syracuseStep 101209985 = 75907489) B75907489
theorem B444307517 : Blo 1754578 444307517 := bstep (se 3 (by rfl) ⟨83307659, by rfl⟩ : syracuseStep 444307517 = 166615319) B166615319
theorem B2963695 : Blo 1754578 2963695 := bstep (se 1 (by rfl) ⟨2222771, by rfl⟩ : syracuseStep 2963695 = 4445543) B4445543
theorem B739859291 : Blo 1754578 739859291 := bstep (se 1 (by rfl) ⟨554894468, by rfl⟩ : syracuseStep 739859291 = 1109788937) B1109788937
theorem B8887805 : Blo 1754578 8887805 := bstep (se 3 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 8887805 = 3332927) B3332927
theorem B273612973 : Blo 1754578 273612973 := bstep (se 3 (by rfl) ⟨51302432, by rfl⟩ : syracuseStep 273612973 = 102604865) B102604865
theorem B21366503 : Blo 1754578 21366503 := bstep (se 1 (by rfl) ⟨16024877, by rfl⟩ : syracuseStep 21366503 = 32049755) B32049755
theorem B1755303 : Blo 1754578 1755303 := bstep (se 1 (by rfl) ⟨1316477, by rfl⟩ : syracuseStep 1755303 = 2632955) B2632955
theorem B5925203 : Blo 1754578 5925203 := bstep (se 1 (by rfl) ⟨4443902, by rfl⟩ : syracuseStep 5925203 = 8887805) B8887805
theorem B3951593 : Blo 1754578 3951593 := bstep (se 2 (by rfl) ⟨1481847, by rfl⟩ : syracuseStep 3951593 = 2963695) B2963695
theorem B67473323 : Blo 1754578 67473323 := bstep (se 1 (by rfl) ⟨50604992, by rfl⟩ : syracuseStep 67473323 = 101209985) B101209985
theorem B2963209 : Blo 1754578 2963209 := bstep (se 2 (by rfl) ⟨1111203, by rfl⟩ : syracuseStep 2963209 = 2222407) B2222407
theorem B296205011 : Blo 1754578 296205011 := bstep (se 1 (by rfl) ⟨222153758, by rfl⟩ : syracuseStep 296205011 = 444307517) B444307517
theorem B493239527 : Blo 1754578 493239527 := bstep (se 1 (by rfl) ⟨369929645, by rfl⟩ : syracuseStep 493239527 = 739859291) B739859291
theorem B1974271 : Blo 1754578 1974271 := bstep (se 1 (by rfl) ⟨1480703, by rfl⟩ : syracuseStep 1974271 = 2961407) B2961407
theorem B3950135 : Blo 1754578 3950135 := bstep (se 1 (by rfl) ⟨2962601, by rfl⟩ : syracuseStep 3950135 = 5925203) B5925203
theorem B197470007 : Blo 1754578 197470007 := bstep (se 1 (by rfl) ⟨148102505, by rfl⟩ : syracuseStep 197470007 = 296205011) B296205011
theorem B3950945 : Blo 1754578 3950945 := bstep (se 2 (by rfl) ⟨1481604, by rfl⟩ : syracuseStep 3950945 = 2963209) B2963209
theorem B2632361 : Blo 1754578 2632361 := bstep (se 2 (by rfl) ⟨987135, by rfl⟩ : syracuseStep 2632361 = 1974271) B1974271
theorem B364817297 : Blo 1754578 364817297 := bstep (se 2 (by rfl) ⟨136806486, by rfl⟩ : syracuseStep 364817297 = 273612973) B273612973
theorem B2634395 : Blo 1754578 2634395 := bstep (se 1 (by rfl) ⟨1975796, by rfl⟩ : syracuseStep 2634395 = 3951593) B3951593
theorem B14244335 : Blo 1754578 14244335 := bstep (se 1 (by rfl) ⟨10683251, by rfl⟩ : syracuseStep 14244335 = 21366503) B21366503
theorem B328826351 : Blo 1754578 328826351 := bstep (se 1 (by rfl) ⟨246619763, by rfl⟩ : syracuseStep 328826351 = 493239527) B493239527
theorem B44982215 : Blo 1754578 44982215 := bstep (se 1 (by rfl) ⟨33736661, by rfl⟩ : syracuseStep 44982215 = 67473323) B67473323
theorem B131646671 : Blo 1754578 131646671 := bstep (se 1 (by rfl) ⟨98735003, by rfl⟩ : syracuseStep 131646671 = 197470007) B197470007
theorem B9496223 : Blo 1754578 9496223 := bstep (se 1 (by rfl) ⟨7122167, by rfl⟩ : syracuseStep 9496223 = 14244335) B14244335
theorem B1754907 : Blo 1754578 1754907 := bstep (se 1 (by rfl) ⟨1316180, by rfl⟩ : syracuseStep 1754907 = 2632361) B2632361
theorem B1756263 : Blo 1754578 1756263 := bstep (se 1 (by rfl) ⟨1317197, by rfl⟩ : syracuseStep 1756263 = 2634395) B2634395
theorem B2633423 : Blo 1754578 2633423 := bstep (se 1 (by rfl) ⟨1975067, by rfl⟩ : syracuseStep 2633423 = 3950135) B3950135
theorem B2633963 : Blo 1754578 2633963 := bstep (se 1 (by rfl) ⟨1975472, by rfl⟩ : syracuseStep 2633963 = 3950945) B3950945
theorem B29988143 : Blo 1754578 29988143 := bstep (se 1 (by rfl) ⟨22491107, by rfl⟩ : syracuseStep 29988143 = 44982215) B44982215
theorem B876870269 : Blo 1754578 876870269 := bstep (se 3 (by rfl) ⟨164413175, by rfl⟩ : syracuseStep 876870269 = 328826351) B328826351
theorem B243211531 : Blo 1754578 243211531 := bstep (se 1 (by rfl) ⟨182408648, by rfl⟩ : syracuseStep 243211531 = 364817297) B364817297
theorem B324282041 : Blo 1754578 324282041 := bstep (se 2 (by rfl) ⟨121605765, by rfl⟩ : syracuseStep 324282041 = 243211531) B243211531
theorem B1755615 : Blo 1754578 1755615 := bstep (se 1 (by rfl) ⟨1316711, by rfl⟩ : syracuseStep 1755615 = 2633423) B2633423
theorem B1755975 : Blo 1754578 1755975 := bstep (se 1 (by rfl) ⟨1316981, by rfl⟩ : syracuseStep 1755975 = 2633963) B2633963
theorem B87764447 : Blo 1754578 87764447 := bstep (se 1 (by rfl) ⟨65823335, by rfl⟩ : syracuseStep 87764447 = 131646671) B131646671
theorem B19992095 : Blo 1754578 19992095 := bstep (se 1 (by rfl) ⟨14994071, by rfl⟩ : syracuseStep 19992095 = 29988143) B29988143
theorem B6330815 : Blo 1754578 6330815 := bstep (se 1 (by rfl) ⟨4748111, by rfl⟩ : syracuseStep 6330815 = 9496223) B9496223
theorem B584580179 : Blo 1754578 584580179 := bstep (se 1 (by rfl) ⟨438435134, by rfl⟩ : syracuseStep 584580179 = 876870269) B876870269
theorem B216188027 : Blo 1754578 216188027 := bstep (se 1 (by rfl) ⟨162141020, by rfl⟩ : syracuseStep 216188027 = 324282041) B324282041
theorem B4220543 : Blo 1754578 4220543 := bstep (se 1 (by rfl) ⟨3165407, by rfl⟩ : syracuseStep 4220543 = 6330815) B6330815
theorem B389720119 : Blo 1754578 389720119 := bstep (se 1 (by rfl) ⟨292290089, by rfl⟩ : syracuseStep 389720119 = 584580179) B584580179
theorem B58509631 : Blo 1754578 58509631 := bstep (se 1 (by rfl) ⟨43882223, by rfl⟩ : syracuseStep 58509631 = 87764447) B87764447
theorem B13328063 : Blo 1754578 13328063 := bstep (se 1 (by rfl) ⟨9996047, by rfl⟩ : syracuseStep 13328063 = 19992095) B19992095
theorem B519626825 : Blo 1754578 519626825 := bstep (se 2 (by rfl) ⟨194860059, by rfl⟩ : syracuseStep 519626825 = 389720119) B389720119
theorem B312051365 : Blo 1754578 312051365 := bstep (se 4 (by rfl) ⟨29254815, by rfl⟩ : syracuseStep 312051365 = 58509631) B58509631
theorem B144125351 : Blo 1754578 144125351 := bstep (se 1 (by rfl) ⟨108094013, by rfl⟩ : syracuseStep 144125351 = 216188027) B216188027
theorem B8885375 : Blo 1754578 8885375 := bstep (se 1 (by rfl) ⟨6664031, by rfl⟩ : syracuseStep 8885375 = 13328063) B13328063
theorem B11254781 : Blo 1754578 11254781 := bstep (se 3 (by rfl) ⟨2110271, by rfl⟩ : syracuseStep 11254781 = 4220543) B4220543
theorem B5923583 : Blo 1754578 5923583 := bstep (se 1 (by rfl) ⟨4442687, by rfl⟩ : syracuseStep 5923583 = 8885375) B8885375
theorem B346417883 : Blo 1754578 346417883 := bstep (se 1 (by rfl) ⟨259813412, by rfl⟩ : syracuseStep 346417883 = 519626825) B519626825
theorem B208034243 : Blo 1754578 208034243 := bstep (se 1 (by rfl) ⟨156025682, by rfl⟩ : syracuseStep 208034243 = 312051365) B312051365
theorem B7503187 : Blo 1754578 7503187 := bstep (se 1 (by rfl) ⟨5627390, by rfl⟩ : syracuseStep 7503187 = 11254781) B11254781
theorem B96083567 : Blo 1754578 96083567 := bstep (se 1 (by rfl) ⟨72062675, by rfl⟩ : syracuseStep 96083567 = 144125351) B144125351
theorem B3949055 : Blo 1754578 3949055 := bstep (se 1 (by rfl) ⟨2961791, by rfl⟩ : syracuseStep 3949055 = 5923583) B5923583
theorem B10004249 : Blo 1754578 10004249 := bstep (se 2 (by rfl) ⟨3751593, by rfl⟩ : syracuseStep 10004249 = 7503187) B7503187
theorem B64055711 : Blo 1754578 64055711 := bstep (se 1 (by rfl) ⟨48041783, by rfl⟩ : syracuseStep 64055711 = 96083567) B96083567
theorem B230945255 : Blo 1754578 230945255 := bstep (se 1 (by rfl) ⟨173208941, by rfl⟩ : syracuseStep 230945255 = 346417883) B346417883
theorem B138689495 : Blo 1754578 138689495 := bstep (se 1 (by rfl) ⟨104017121, by rfl⟩ : syracuseStep 138689495 = 208034243) B208034243
theorem B6669499 : Blo 1754578 6669499 := bstep (se 1 (by rfl) ⟨5002124, by rfl⟩ : syracuseStep 6669499 = 10004249) B10004249
theorem B153963503 : Blo 1754578 153963503 := bstep (se 1 (by rfl) ⟨115472627, by rfl⟩ : syracuseStep 153963503 = 230945255) B230945255
theorem B2632703 : Blo 1754578 2632703 := bstep (se 1 (by rfl) ⟨1974527, by rfl⟩ : syracuseStep 2632703 = 3949055) B3949055
theorem B92459663 : Blo 1754578 92459663 := bstep (se 1 (by rfl) ⟨69344747, by rfl⟩ : syracuseStep 92459663 = 138689495) B138689495
theorem B42703807 : Blo 1754578 42703807 := bstep (se 1 (by rfl) ⟨32027855, by rfl⟩ : syracuseStep 42703807 = 64055711) B64055711
theorem B1755135 : Blo 1754578 1755135 := bstep (se 1 (by rfl) ⟨1316351, by rfl⟩ : syracuseStep 1755135 = 2632703) B2632703
theorem B61639775 : Blo 1754578 61639775 := bstep (se 1 (by rfl) ⟨46229831, by rfl⟩ : syracuseStep 61639775 = 92459663) B92459663
theorem B56938409 : Blo 1754578 56938409 := bstep (se 2 (by rfl) ⟨21351903, by rfl⟩ : syracuseStep 56938409 = 42703807) B42703807
theorem B8892665 : Blo 1754578 8892665 := bstep (se 2 (by rfl) ⟨3334749, by rfl⟩ : syracuseStep 8892665 = 6669499) B6669499
theorem B102642335 : Blo 1754578 102642335 := bstep (se 1 (by rfl) ⟨76981751, by rfl⟩ : syracuseStep 102642335 = 153963503) B153963503
theorem B68428223 : Blo 1754578 68428223 := bstep (se 1 (by rfl) ⟨51321167, by rfl⟩ : syracuseStep 68428223 = 102642335) B102642335
theorem B41093183 : Blo 1754578 41093183 := bstep (se 1 (by rfl) ⟨30819887, by rfl⟩ : syracuseStep 41093183 = 61639775) B61639775
theorem B37958939 : Blo 1754578 37958939 := bstep (se 1 (by rfl) ⟨28469204, by rfl⟩ : syracuseStep 37958939 = 56938409) B56938409
theorem B5928443 : Blo 1754578 5928443 := bstep (se 1 (by rfl) ⟨4446332, by rfl⟩ : syracuseStep 5928443 = 8892665) B8892665
theorem B25305959 : Blo 1754578 25305959 := bstep (se 1 (by rfl) ⟨18979469, by rfl⟩ : syracuseStep 25305959 = 37958939) B37958939
theorem B27395455 : Blo 1754578 27395455 := bstep (se 1 (by rfl) ⟨20546591, by rfl⟩ : syracuseStep 27395455 = 41093183) B41093183
theorem B3952295 : Blo 1754578 3952295 := bstep (se 1 (by rfl) ⟨2964221, by rfl⟩ : syracuseStep 3952295 = 5928443) B5928443
theorem B45618815 : Blo 1754578 45618815 := bstep (se 1 (by rfl) ⟨34214111, by rfl⟩ : syracuseStep 45618815 = 68428223) B68428223
theorem B16870639 : Blo 1754578 16870639 := bstep (se 1 (by rfl) ⟨12652979, by rfl⟩ : syracuseStep 16870639 = 25305959) B25305959
theorem B30412543 : Blo 1754578 30412543 := bstep (se 1 (by rfl) ⟨22809407, by rfl⟩ : syracuseStep 30412543 = 45618815) B45618815
theorem B2634863 : Blo 1754578 2634863 := bstep (se 1 (by rfl) ⟨1976147, by rfl⟩ : syracuseStep 2634863 = 3952295) B3952295
theorem B36527273 : Blo 1754578 36527273 := bstep (se 2 (by rfl) ⟨13697727, by rfl⟩ : syracuseStep 36527273 = 27395455) B27395455
theorem B1756575 : Blo 1754578 1756575 := bstep (se 1 (by rfl) ⟨1317431, by rfl⟩ : syracuseStep 1756575 = 2634863) B2634863
theorem B24351515 : Blo 1754578 24351515 := bstep (se 1 (by rfl) ⟨18263636, by rfl⟩ : syracuseStep 24351515 = 36527273) B36527273
theorem B22494185 : Blo 1754578 22494185 := bstep (se 2 (by rfl) ⟨8435319, by rfl⟩ : syracuseStep 22494185 = 16870639) B16870639
theorem B40550057 : Blo 1754578 40550057 := bstep (se 2 (by rfl) ⟨15206271, by rfl⟩ : syracuseStep 40550057 = 30412543) B30412543
theorem B14996123 : Blo 1754578 14996123 := bstep (se 1 (by rfl) ⟨11247092, by rfl⟩ : syracuseStep 14996123 = 22494185) B22494185
theorem B16234343 : Blo 1754578 16234343 := bstep (se 1 (by rfl) ⟨12175757, by rfl⟩ : syracuseStep 16234343 = 24351515) B24351515
theorem B27033371 : Blo 1754578 27033371 := bstep (se 1 (by rfl) ⟨20275028, by rfl⟩ : syracuseStep 27033371 = 40550057) B40550057
theorem B10822895 : Blo 1754578 10822895 := bstep (se 1 (by rfl) ⟨8117171, by rfl⟩ : syracuseStep 10822895 = 16234343) B16234343
theorem B9997415 : Blo 1754578 9997415 := bstep (se 1 (by rfl) ⟨7498061, by rfl⟩ : syracuseStep 9997415 = 14996123) B14996123
theorem B18022247 : Blo 1754578 18022247 := bstep (se 1 (by rfl) ⟨13516685, by rfl⟩ : syracuseStep 18022247 = 27033371) B27033371
theorem B6664943 : Blo 1754578 6664943 := bstep (se 1 (by rfl) ⟨4998707, by rfl⟩ : syracuseStep 6664943 = 9997415) B9997415
theorem B12014831 : Blo 1754578 12014831 := bstep (se 1 (by rfl) ⟨9011123, by rfl⟩ : syracuseStep 12014831 = 18022247) B18022247
theorem B7215263 : Blo 1754578 7215263 := bstep (se 1 (by rfl) ⟨5411447, by rfl⟩ : syracuseStep 7215263 = 10822895) B10822895
theorem B32039549 : Blo 1754578 32039549 := bstep (se 3 (by rfl) ⟨6007415, by rfl⟩ : syracuseStep 32039549 = 12014831) B12014831
theorem B4810175 : Blo 1754578 4810175 := bstep (se 1 (by rfl) ⟨3607631, by rfl⟩ : syracuseStep 4810175 = 7215263) B7215263
theorem B4443295 : Blo 1754578 4443295 := bstep (se 1 (by rfl) ⟨3332471, by rfl⟩ : syracuseStep 4443295 = 6664943) B6664943
theorem B5924393 : Blo 1754578 5924393 := bstep (se 2 (by rfl) ⟨2221647, by rfl⟩ : syracuseStep 5924393 = 4443295) B4443295
theorem B21359699 : Blo 1754578 21359699 := bstep (se 1 (by rfl) ⟨16019774, by rfl⟩ : syracuseStep 21359699 = 32039549) B32039549
theorem B3206783 : Blo 1754578 3206783 := bstep (se 1 (by rfl) ⟨2405087, by rfl⟩ : syracuseStep 3206783 = 4810175) B4810175
theorem B3949595 : Blo 1754578 3949595 := bstep (se 1 (by rfl) ⟨2962196, by rfl⟩ : syracuseStep 3949595 = 5924393) B5924393
theorem B14239799 : Blo 1754578 14239799 := bstep (se 1 (by rfl) ⟨10679849, by rfl⟩ : syracuseStep 14239799 = 21359699) B21359699
theorem B8551421 : Blo 1754578 8551421 := bstep (se 3 (by rfl) ⟨1603391, by rfl⟩ : syracuseStep 8551421 = 3206783) B3206783
theorem B2633063 : Blo 1754578 2633063 := bstep (se 1 (by rfl) ⟨1974797, by rfl⟩ : syracuseStep 2633063 = 3949595) B3949595
theorem B9493199 : Blo 1754578 9493199 := bstep (se 1 (by rfl) ⟨7119899, by rfl⟩ : syracuseStep 9493199 = 14239799) B14239799
theorem B5700947 : Blo 1754578 5700947 := bstep (se 1 (by rfl) ⟨4275710, by rfl⟩ : syracuseStep 5700947 = 8551421) B8551421
theorem B1755375 : Blo 1754578 1755375 := bstep (se 1 (by rfl) ⟨1316531, by rfl⟩ : syracuseStep 1755375 = 2633063) B2633063
theorem B6328799 : Blo 1754578 6328799 := bstep (se 1 (by rfl) ⟨4746599, by rfl⟩ : syracuseStep 6328799 = 9493199) B9493199
theorem B15202525 : Blo 1754578 15202525 := bstep (se 3 (by rfl) ⟨2850473, by rfl⟩ : syracuseStep 15202525 = 5700947) B5700947
theorem B4219199 : Blo 1754578 4219199 := bstep (se 1 (by rfl) ⟨3164399, by rfl⟩ : syracuseStep 4219199 = 6328799) B6328799
theorem B20270033 : Blo 1754578 20270033 := bstep (se 2 (by rfl) ⟨7601262, by rfl⟩ : syracuseStep 20270033 = 15202525) B15202525
theorem B2812799 : Blo 1754578 2812799 := bstep (se 1 (by rfl) ⟨2109599, by rfl⟩ : syracuseStep 2812799 = 4219199) B4219199
theorem B13513355 : Blo 1754578 13513355 := bstep (se 1 (by rfl) ⟨10135016, by rfl⟩ : syracuseStep 13513355 = 20270033) B20270033
theorem B9008903 : Blo 1754578 9008903 := bstep (se 1 (by rfl) ⟨6756677, by rfl⟩ : syracuseStep 9008903 = 13513355) B13513355
theorem B1875199 : Blo 1754578 1875199 := bstep (se 1 (by rfl) ⟨1406399, by rfl⟩ : syracuseStep 1875199 = 2812799) B2812799
theorem B6005935 : Blo 1754578 6005935 := bstep (se 1 (by rfl) ⟨4504451, by rfl⟩ : syracuseStep 6005935 = 9008903) B9008903
theorem B2500265 : Blo 1754578 2500265 := bstep (se 2 (by rfl) ⟨937599, by rfl⟩ : syracuseStep 2500265 = 1875199) B1875199
theorem B8007913 : Blo 1754578 8007913 := bstep (se 2 (by rfl) ⟨3002967, by rfl⟩ : syracuseStep 8007913 = 6005935) B6005935
theorem B6667373 : Blo 1754578 6667373 := bstep (se 3 (by rfl) ⟨1250132, by rfl⟩ : syracuseStep 6667373 = 2500265) B2500265
theorem B10677217 : Blo 1754578 10677217 := bstep (se 2 (by rfl) ⟨4003956, by rfl⟩ : syracuseStep 10677217 = 8007913) B8007913
theorem B4444915 : Blo 1754578 4444915 := bstep (se 1 (by rfl) ⟨3333686, by rfl⟩ : syracuseStep 4444915 = 6667373) B6667373
theorem B5926553 : Blo 1754578 5926553 := bstep (se 2 (by rfl) ⟨2222457, by rfl⟩ : syracuseStep 5926553 = 4444915) B4444915
theorem B14236289 : Blo 1754578 14236289 := bstep (se 2 (by rfl) ⟨5338608, by rfl⟩ : syracuseStep 14236289 = 10677217) B10677217
theorem B3951035 : Blo 1754578 3951035 := bstep (se 1 (by rfl) ⟨2963276, by rfl⟩ : syracuseStep 3951035 = 5926553) B5926553
theorem B9490859 : Blo 1754578 9490859 := bstep (se 1 (by rfl) ⟨7118144, by rfl⟩ : syracuseStep 9490859 = 14236289) B14236289
theorem B6327239 : Blo 1754578 6327239 := bstep (se 1 (by rfl) ⟨4745429, by rfl⟩ : syracuseStep 6327239 = 9490859) B9490859
theorem B2634023 : Blo 1754578 2634023 := bstep (se 1 (by rfl) ⟨1975517, by rfl⟩ : syracuseStep 2634023 = 3951035) B3951035
theorem B1756015 : Blo 1754578 1756015 := bstep (se 1 (by rfl) ⟨1317011, by rfl⟩ : syracuseStep 1756015 = 2634023) B2634023
theorem B16872637 : Blo 1754578 16872637 := bstep (se 3 (by rfl) ⟨3163619, by rfl⟩ : syracuseStep 16872637 = 6327239) B6327239
theorem B22496849 : Blo 1754578 22496849 := bstep (se 2 (by rfl) ⟨8436318, by rfl⟩ : syracuseStep 22496849 = 16872637) B16872637
theorem B14997899 : Blo 1754578 14997899 := bstep (se 1 (by rfl) ⟨11248424, by rfl⟩ : syracuseStep 14997899 = 22496849) B22496849
theorem B9998599 : Blo 1754578 9998599 := bstep (se 1 (by rfl) ⟨7498949, by rfl⟩ : syracuseStep 9998599 = 14997899) B14997899
theorem B13331465 : Blo 1754578 13331465 := bstep (se 2 (by rfl) ⟨4999299, by rfl⟩ : syracuseStep 13331465 = 9998599) B9998599
theorem B8887643 : Blo 1754578 8887643 := bstep (se 1 (by rfl) ⟨6665732, by rfl⟩ : syracuseStep 8887643 = 13331465) B13331465
theorem B5925095 : Blo 1754578 5925095 := bstep (se 1 (by rfl) ⟨4443821, by rfl⟩ : syracuseStep 5925095 = 8887643) B8887643
theorem B3950063 : Blo 1754578 3950063 := bstep (se 1 (by rfl) ⟨2962547, by rfl⟩ : syracuseStep 3950063 = 5925095) B5925095
theorem B2633375 : Blo 1754578 2633375 := bstep (se 1 (by rfl) ⟨1975031, by rfl⟩ : syracuseStep 2633375 = 3950063) B3950063
theorem B1755583 : Blo 1754578 1755583 := bstep (se 1 (by rfl) ⟨1316687, by rfl⟩ : syracuseStep 1755583 = 2633375) B2633375

theorem C0 (j : ℕ) (h1 : 438644 ≤ j) (h2 : j ≤ 439143) : Blo 1754578 (4 * j + 3) := by
  interval_cases j
  · exact B1754579
  · exact B1754583
  · exact B1754587
  · exact B1754591
  · exact B1754595
  · exact B1754599
  · exact B1754603
  · exact B1754607
  · exact B1754611
  · exact B1754615
  · exact B1754619
  · exact B1754623
  · exact B1754627
  · exact B1754631
  · exact B1754635
  · exact B1754639
  · exact B1754643
  · exact B1754647
  · exact B1754651
  · exact B1754655
  · exact B1754659
  · exact B1754663
  · exact B1754667
  · exact B1754671
  · exact B1754675
  · exact B1754679
  · exact B1754683
  · exact B1754687
  · exact B1754691
  · exact B1754695
  · exact B1754699
  · exact B1754703
  · exact B1754707
  · exact B1754711
  · exact B1754715
  · exact B1754719
  · exact B1754723
  · exact B1754727
  · exact B1754731
  · exact B1754735
  · exact B1754739
  · exact B1754743
  · exact B1754747
  · exact B1754751
  · exact B1754755
  · exact B1754759
  · exact B1754763
  · exact B1754767
  · exact B1754771
  · exact B1754775
  · exact B1754779
  · exact B1754783
  · exact B1754787
  · exact B1754791
  · exact B1754795
  · exact B1754799
  · exact B1754803
  · exact B1754807
  · exact B1754811
  · exact B1754815
  · exact B1754819
  · exact B1754823
  · exact B1754827
  · exact B1754831
  · exact B1754835
  · exact B1754839
  · exact B1754843
  · exact B1754847
  · exact B1754851
  · exact B1754855
  · exact B1754859
  · exact B1754863
  · exact B1754867
  · exact B1754871
  · exact B1754875
  · exact B1754879
  · exact B1754883
  · exact B1754887
  · exact B1754891
  · exact B1754895
  · exact B1754899
  · exact B1754903
  · exact B1754907
  · exact B1754911
  · exact B1754915
  · exact B1754919
  · exact B1754923
  · exact B1754927
  · exact B1754931
  · exact B1754935
  · exact B1754939
  · exact B1754943
  · exact B1754947
  · exact B1754951
  · exact B1754955
  · exact B1754959
  · exact B1754963
  · exact B1754967
  · exact B1754971
  · exact B1754975
  · exact B1754979
  · exact B1754983
  · exact B1754987
  · exact B1754991
  · exact B1754995
  · exact B1754999
  · exact B1755003
  · exact B1755007
  · exact B1755011
  · exact B1755015
  · exact B1755019
  · exact B1755023
  · exact B1755027
  · exact B1755031
  · exact B1755035
  · exact B1755039
  · exact B1755043
  · exact B1755047
  · exact B1755051
  · exact B1755055
  · exact B1755059
  · exact B1755063
  · exact B1755067
  · exact B1755071
  · exact B1755075
  · exact B1755079
  · exact B1755083
  · exact B1755087
  · exact B1755091
  · exact B1755095
  · exact B1755099
  · exact B1755103
  · exact B1755107
  · exact B1755111
  · exact B1755115
  · exact B1755119
  · exact B1755123
  · exact B1755127
  · exact B1755131
  · exact B1755135
  · exact B1755139
  · exact B1755143
  · exact B1755147
  · exact B1755151
  · exact B1755155
  · exact B1755159
  · exact B1755163
  · exact B1755167
  · exact B1755171
  · exact B1755175
  · exact B1755179
  · exact B1755183
  · exact B1755187
  · exact B1755191
  · exact B1755195
  · exact B1755199
  · exact B1755203
  · exact B1755207
  · exact B1755211
  · exact B1755215
  · exact B1755219
  · exact B1755223
  · exact B1755227
  · exact B1755231
  · exact B1755235
  · exact B1755239
  · exact B1755243
  · exact B1755247
  · exact B1755251
  · exact B1755255
  · exact B1755259
  · exact B1755263
  · exact B1755267
  · exact B1755271
  · exact B1755275
  · exact B1755279
  · exact B1755283
  · exact B1755287
  · exact B1755291
  · exact B1755295
  · exact B1755299
  · exact B1755303
  · exact B1755307
  · exact B1755311
  · exact B1755315
  · exact B1755319
  · exact B1755323
  · exact B1755327
  · exact B1755331
  · exact B1755335
  · exact B1755339
  · exact B1755343
  · exact B1755347
  · exact B1755351
  · exact B1755355
  · exact B1755359
  · exact B1755363
  · exact B1755367
  · exact B1755371
  · exact B1755375
  · exact B1755379
  · exact B1755383
  · exact B1755387
  · exact B1755391
  · exact B1755395
  · exact B1755399
  · exact B1755403
  · exact B1755407
  · exact B1755411
  · exact B1755415
  · exact B1755419
  · exact B1755423
  · exact B1755427
  · exact B1755431
  · exact B1755435
  · exact B1755439
  · exact B1755443
  · exact B1755447
  · exact B1755451
  · exact B1755455
  · exact B1755459
  · exact B1755463
  · exact B1755467
  · exact B1755471
  · exact B1755475
  · exact B1755479
  · exact B1755483
  · exact B1755487
  · exact B1755491
  · exact B1755495
  · exact B1755499
  · exact B1755503
  · exact B1755507
  · exact B1755511
  · exact B1755515
  · exact B1755519
  · exact B1755523
  · exact B1755527
  · exact B1755531
  · exact B1755535
  · exact B1755539
  · exact B1755543
  · exact B1755547
  · exact B1755551
  · exact B1755555
  · exact B1755559
  · exact B1755563
  · exact B1755567
  · exact B1755571
  · exact B1755575
  · exact B1755579
  · exact B1755583
  · exact B1755587
  · exact B1755591
  · exact B1755595
  · exact B1755599
  · exact B1755603
  · exact B1755607
  · exact B1755611
  · exact B1755615
  · exact B1755619
  · exact B1755623
  · exact B1755627
  · exact B1755631
  · exact B1755635
  · exact B1755639
  · exact B1755643
  · exact B1755647
  · exact B1755651
  · exact B1755655
  · exact B1755659
  · exact B1755663
  · exact B1755667
  · exact B1755671
  · exact B1755675
  · exact B1755679
  · exact B1755683
  · exact B1755687
  · exact B1755691
  · exact B1755695
  · exact B1755699
  · exact B1755703
  · exact B1755707
  · exact B1755711
  · exact B1755715
  · exact B1755719
  · exact B1755723
  · exact B1755727
  · exact B1755731
  · exact B1755735
  · exact B1755739
  · exact B1755743
  · exact B1755747
  · exact B1755751
  · exact B1755755
  · exact B1755759
  · exact B1755763
  · exact B1755767
  · exact B1755771
  · exact B1755775
  · exact B1755779
  · exact B1755783
  · exact B1755787
  · exact B1755791
  · exact B1755795
  · exact B1755799
  · exact B1755803
  · exact B1755807
  · exact B1755811
  · exact B1755815
  · exact B1755819
  · exact B1755823
  · exact B1755827
  · exact B1755831
  · exact B1755835
  · exact B1755839
  · exact B1755843
  · exact B1755847
  · exact B1755851
  · exact B1755855
  · exact B1755859
  · exact B1755863
  · exact B1755867
  · exact B1755871
  · exact B1755875
  · exact B1755879
  · exact B1755883
  · exact B1755887
  · exact B1755891
  · exact B1755895
  · exact B1755899
  · exact B1755903
  · exact B1755907
  · exact B1755911
  · exact B1755915
  · exact B1755919
  · exact B1755923
  · exact B1755927
  · exact B1755931
  · exact B1755935
  · exact B1755939
  · exact B1755943
  · exact B1755947
  · exact B1755951
  · exact B1755955
  · exact B1755959
  · exact B1755963
  · exact B1755967
  · exact B1755971
  · exact B1755975
  · exact B1755979
  · exact B1755983
  · exact B1755987
  · exact B1755991
  · exact B1755995
  · exact B1755999
  · exact B1756003
  · exact B1756007
  · exact B1756011
  · exact B1756015
  · exact B1756019
  · exact B1756023
  · exact B1756027
  · exact B1756031
  · exact B1756035
  · exact B1756039
  · exact B1756043
  · exact B1756047
  · exact B1756051
  · exact B1756055
  · exact B1756059
  · exact B1756063
  · exact B1756067
  · exact B1756071
  · exact B1756075
  · exact B1756079
  · exact B1756083
  · exact B1756087
  · exact B1756091
  · exact B1756095
  · exact B1756099
  · exact B1756103
  · exact B1756107
  · exact B1756111
  · exact B1756115
  · exact B1756119
  · exact B1756123
  · exact B1756127
  · exact B1756131
  · exact B1756135
  · exact B1756139
  · exact B1756143
  · exact B1756147
  · exact B1756151
  · exact B1756155
  · exact B1756159
  · exact B1756163
  · exact B1756167
  · exact B1756171
  · exact B1756175
  · exact B1756179
  · exact B1756183
  · exact B1756187
  · exact B1756191
  · exact B1756195
  · exact B1756199
  · exact B1756203
  · exact B1756207
  · exact B1756211
  · exact B1756215
  · exact B1756219
  · exact B1756223
  · exact B1756227
  · exact B1756231
  · exact B1756235
  · exact B1756239
  · exact B1756243
  · exact B1756247
  · exact B1756251
  · exact B1756255
  · exact B1756259
  · exact B1756263
  · exact B1756267
  · exact B1756271
  · exact B1756275
  · exact B1756279
  · exact B1756283
  · exact B1756287
  · exact B1756291
  · exact B1756295
  · exact B1756299
  · exact B1756303
  · exact B1756307
  · exact B1756311
  · exact B1756315
  · exact B1756319
  · exact B1756323
  · exact B1756327
  · exact B1756331
  · exact B1756335
  · exact B1756339
  · exact B1756343
  · exact B1756347
  · exact B1756351
  · exact B1756355
  · exact B1756359
  · exact B1756363
  · exact B1756367
  · exact B1756371
  · exact B1756375
  · exact B1756379
  · exact B1756383
  · exact B1756387
  · exact B1756391
  · exact B1756395
  · exact B1756399
  · exact B1756403
  · exact B1756407
  · exact B1756411
  · exact B1756415
  · exact B1756419
  · exact B1756423
  · exact B1756427
  · exact B1756431
  · exact B1756435
  · exact B1756439
  · exact B1756443
  · exact B1756447
  · exact B1756451
  · exact B1756455
  · exact B1756459
  · exact B1756463
  · exact B1756467
  · exact B1756471
  · exact B1756475
  · exact B1756479
  · exact B1756483
  · exact B1756487
  · exact B1756491
  · exact B1756495
  · exact B1756499
  · exact B1756503
  · exact B1756507
  · exact B1756511
  · exact B1756515
  · exact B1756519
  · exact B1756523
  · exact B1756527
  · exact B1756531
  · exact B1756535
  · exact B1756539
  · exact B1756543
  · exact B1756547
  · exact B1756551
  · exact B1756555
  · exact B1756559
  · exact B1756563
  · exact B1756567
  · exact B1756571
  · exact B1756575

theorem solution (m : ℕ) (hlo : 1754578 ≤ m) (hhi : m ≤ 1756578) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 438644 ≤ j := by omega
    have hj2 : j ≤ 439143 := by omega
    have hb : Blo 1754578 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
