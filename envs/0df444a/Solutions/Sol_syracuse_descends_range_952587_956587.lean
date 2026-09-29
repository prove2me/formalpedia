-- Prove2me | solution 1 for syracuse_descends_range_952587_956587
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:00.127227+00:00
-- url     : https://prove2.me/submissions/8c69061d-83a8-474a-b143-ea1098abf186

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


theorem B1146901 : Blo 952587 1146901 := bbase (se 6 (by rfl) ⟨26880, by rfl⟩ : syracuseStep 1146901 = 53761) (by norm_num)
theorem B1835045 : Blo 952587 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B8257589 : Blo 952587 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B3440789 : Blo 952587 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B1147073 : Blo 952587 1147073 := bbase (se 2 (by rfl) ⟨430152, by rfl⟩ : syracuseStep 1147073 = 860305) (by norm_num)
theorem B1147189 : Blo 952587 1147189 := bbase (se 5 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 1147189 = 107549) (by norm_num)
theorem B1933645 : Blo 952587 1933645 := bbase (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) (by norm_num)
theorem B1147285 : Blo 952587 1147285 := bbase (se 6 (by rfl) ⟨26889, by rfl⟩ : syracuseStep 1147285 = 53779) (by norm_num)
theorem B1147429 : Blo 952587 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B1835789 : Blo 952587 1835789 := bbase (se 3 (by rfl) ⟨344210, by rfl⟩ : syracuseStep 1835789 = 688421) (by norm_num)
theorem B6128693 : Blo 952587 6128693 := bbase (se 5 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 6128693 = 574565) (by norm_num)
theorem B2721221 : Blo 952587 2721221 := bbase (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) (by norm_num)
theorem B4589045 : Blo 952587 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B1017365 : Blo 952587 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B14714389 : Blo 952587 14714389 := bbase (se 6 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 14714389 = 689737) (by norm_num)
theorem B3868325 : Blo 952587 3868325 := bbase (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) (by norm_num)
theorem B2066165 : Blo 952587 2066165 := bbase (se 5 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 2066165 = 193703) (by norm_num)
theorem B1017613 : Blo 952587 1017613 := bbase (se 3 (by rfl) ⟨190802, by rfl⟩ : syracuseStep 1017613 = 381605) (by norm_num)
theorem B3868517 : Blo 952587 3868517 := bbase (se 4 (by rfl) ⟨362673, by rfl⟩ : syracuseStep 3868517 = 725347) (by norm_num)
theorem B1607573 : Blo 952587 1607573 := bbase (se 6 (by rfl) ⟨37677, by rfl⟩ : syracuseStep 1607573 = 75355) (by norm_num)
theorem B6522869 : Blo 952587 6522869 := bbase (se 5 (by rfl) ⟨305759, by rfl⟩ : syracuseStep 6522869 = 611519) (by norm_num)
theorem B1607701 : Blo 952587 1607701 := bbase (se 6 (by rfl) ⟨37680, by rfl⟩ : syracuseStep 1607701 = 75361) (by norm_num)
theorem B7243829 : Blo 952587 7243829 := bbase (se 5 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 7243829 = 679109) (by norm_num)
theorem B1607789 : Blo 952587 1607789 := bbase (se 3 (by rfl) ⟨301460, by rfl⟩ : syracuseStep 1607789 = 602921) (by norm_num)
theorem B9799829 : Blo 952587 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B1018045 : Blo 952587 1018045 := bbase (se 3 (by rfl) ⟨190883, by rfl⟩ : syracuseStep 1018045 = 381767) (by norm_num)
theorem B1149149 : Blo 952587 1149149 := bbase (se 3 (by rfl) ⟨215465, by rfl⟩ : syracuseStep 1149149 = 430931) (by norm_num)
theorem B1607917 : Blo 952587 1607917 := bbase (se 3 (by rfl) ⟨301484, by rfl⟩ : syracuseStep 1607917 = 602969) (by norm_num)
theorem B1018117 : Blo 952587 1018117 := bbase (se 4 (by rfl) ⟨95448, by rfl⟩ : syracuseStep 1018117 = 190897) (by norm_num)
theorem B1608005 : Blo 952587 1608005 := bbase (se 4 (by rfl) ⟨150750, by rfl⟩ : syracuseStep 1608005 = 301501) (by norm_num)
theorem B1608133 : Blo 952587 1608133 := bbase (se 4 (by rfl) ⟨150762, by rfl⟩ : syracuseStep 1608133 = 301525) (by norm_num)
theorem B1608221 : Blo 952587 1608221 := bbase (se 3 (by rfl) ⟨301541, by rfl⟩ : syracuseStep 1608221 = 603083) (by norm_num)
theorem B2722405 : Blo 952587 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B1018489 : Blo 952587 1018489 := bbase (se 2 (by rfl) ⟨381933, by rfl⟩ : syracuseStep 1018489 = 763867) (by norm_num)
theorem B2296453 : Blo 952587 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B1608349 : Blo 952587 1608349 := bbase (se 3 (by rfl) ⟨301565, by rfl⟩ : syracuseStep 1608349 = 603131) (by norm_num)
theorem B1608437 : Blo 952587 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B2722565 : Blo 952587 2722565 := bbase (se 4 (by rfl) ⟨255240, by rfl⟩ : syracuseStep 2722565 = 510481) (by norm_num)
theorem B1608565 : Blo 952587 1608565 := bbase (se 5 (by rfl) ⟨75401, by rfl⟩ : syracuseStep 1608565 = 150803) (by norm_num)
theorem B1608653 : Blo 952587 1608653 := bbase (se 3 (by rfl) ⟨301622, by rfl⟩ : syracuseStep 1608653 = 603245) (by norm_num)
theorem B1018865 : Blo 952587 1018865 := bbase (se 2 (by rfl) ⟨382074, by rfl⟩ : syracuseStep 1018865 = 764149) (by norm_num)
theorem B2722805 : Blo 952587 2722805 := bbase (se 5 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 2722805 = 255263) (by norm_num)
theorem B2296829 : Blo 952587 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B1018937 : Blo 952587 1018937 := bbase (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) (by norm_num)
theorem B1608781 : Blo 952587 1608781 := bbase (se 3 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 1608781 = 603293) (by norm_num)
theorem B2329733 : Blo 952587 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B1608869 : Blo 952587 1608869 := bbase (se 4 (by rfl) ⟨150831, by rfl⟩ : syracuseStep 1608869 = 301663) (by norm_num)
theorem B2722997 : Blo 952587 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B1019125 : Blo 952587 1019125 := bbase (se 5 (by rfl) ⟨47771, by rfl⟩ : syracuseStep 1019125 = 95543) (by norm_num)
theorem B1608997 : Blo 952587 1608997 := bbase (se 4 (by rfl) ⟨150843, by rfl⟩ : syracuseStep 1608997 = 301687) (by norm_num)
theorem B1609085 : Blo 952587 1609085 := bbase (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) (by norm_num)
theorem B3444133 : Blo 952587 3444133 := bbase (se 4 (by rfl) ⟨322887, by rfl⟩ : syracuseStep 3444133 = 645775) (by norm_num)
theorem B1019309 : Blo 952587 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B2297261 : Blo 952587 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B1609213 : Blo 952587 1609213 := bbase (se 3 (by rfl) ⟨301727, by rfl⟩ : syracuseStep 1609213 = 603455) (by norm_num)
theorem B1609301 : Blo 952587 1609301 := bbase (se 8 (by rfl) ⟨9429, by rfl⟩ : syracuseStep 1609301 = 18859) (by norm_num)
theorem B3214997 : Blo 952587 3214997 := bbase (se 6 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 3214997 = 150703) (by norm_num)
theorem B1740461 : Blo 952587 1740461 := bbase (se 3 (by rfl) ⟨326336, by rfl⟩ : syracuseStep 1740461 = 652673) (by norm_num)
theorem B1412813 : Blo 952587 1412813 := bbase (se 3 (by rfl) ⟨264902, by rfl⟩ : syracuseStep 1412813 = 529805) (by norm_num)
theorem B1609429 : Blo 952587 1609429 := bbase (se 7 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 1609429 = 37721) (by norm_num)
theorem B1609517 : Blo 952587 1609517 := bbase (se 3 (by rfl) ⟨301784, by rfl⟩ : syracuseStep 1609517 = 603569) (by norm_num)
theorem B6885269 : Blo 952587 6885269 := bbase (se 6 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 6885269 = 322747) (by norm_num)
theorem B1609645 : Blo 952587 1609645 := bbase (se 3 (by rfl) ⟨301808, by rfl⟩ : syracuseStep 1609645 = 603617) (by norm_num)
theorem B2297837 : Blo 952587 2297837 := bbase (se 3 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 2297837 = 861689) (by norm_num)
theorem B1609733 : Blo 952587 1609733 := bbase (se 4 (by rfl) ⟨150912, by rfl⟩ : syracuseStep 1609733 = 301825) (by norm_num)
theorem B3215429 : Blo 952587 3215429 := bbase (se 4 (by rfl) ⟨301446, by rfl⟩ : syracuseStep 3215429 = 602893) (by norm_num)
theorem B2789477 : Blo 952587 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B1609861 : Blo 952587 1609861 := bbase (se 4 (by rfl) ⟨150924, by rfl⟩ : syracuseStep 1609861 = 301849) (by norm_num)
theorem B2723989 : Blo 952587 2723989 := bbase (se 6 (by rfl) ⟨63843, by rfl⟩ : syracuseStep 2723989 = 127687) (by norm_num)
theorem B1020061 : Blo 952587 1020061 := bbase (se 3 (by rfl) ⟨191261, by rfl⟩ : syracuseStep 1020061 = 382523) (by norm_num)
theorem B4591829 : Blo 952587 4591829 := bbase (se 7 (by rfl) ⟨53810, by rfl⟩ : syracuseStep 4591829 = 107621) (by norm_num)
theorem B1609949 : Blo 952587 1609949 := bbase (se 3 (by rfl) ⟨301865, by rfl⟩ : syracuseStep 1609949 = 603731) (by norm_num)
theorem B1020133 : Blo 952587 1020133 := bbase (se 4 (by rfl) ⟨95637, by rfl⟩ : syracuseStep 1020133 = 191275) (by norm_num)
theorem B2036029 : Blo 952587 2036029 := bbase (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) (by norm_num)
theorem B1610077 : Blo 952587 1610077 := bbase (se 3 (by rfl) ⟨301889, by rfl⟩ : syracuseStep 1610077 = 603779) (by norm_num)
theorem B1020313 : Blo 952587 1020313 := bbase (se 2 (by rfl) ⟨382617, by rfl⟩ : syracuseStep 1020313 = 765235) (by norm_num)
theorem B1610165 : Blo 952587 1610165 := bbase (se 5 (by rfl) ⟨75476, by rfl⟩ : syracuseStep 1610165 = 150953) (by norm_num)
theorem B3215861 : Blo 952587 3215861 := bbase (se 5 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 3215861 = 301487) (by norm_num)
theorem B1610293 : Blo 952587 1610293 := bbase (se 5 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 1610293 = 150965) (by norm_num)
theorem B1610381 : Blo 952587 1610381 := bbase (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) (by norm_num)
theorem B1610509 : Blo 952587 1610509 := bbase (se 3 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 1610509 = 603941) (by norm_num)
theorem B3674965 : Blo 952587 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B1020757 : Blo 952587 1020757 := bbase (se 9 (by rfl) ⟨2990, by rfl⟩ : syracuseStep 1020757 = 5981) (by norm_num)
theorem B1610597 : Blo 952587 1610597 := bbase (se 4 (by rfl) ⟨150993, by rfl⟩ : syracuseStep 1610597 = 301987) (by norm_num)
theorem B3216293 : Blo 952587 3216293 := bbase (se 4 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 3216293 = 603055) (by norm_num)
theorem B1020881 : Blo 952587 1020881 := bbase (se 2 (by rfl) ⟨382830, by rfl⟩ : syracuseStep 1020881 = 765661) (by norm_num)
theorem B1610725 : Blo 952587 1610725 := bbase (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) (by norm_num)
theorem B1610813 : Blo 952587 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B2036917 : Blo 952587 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B1610941 : Blo 952587 1610941 := bbase (se 3 (by rfl) ⟨302051, by rfl⟩ : syracuseStep 1610941 = 604103) (by norm_num)
theorem B1021133 : Blo 952587 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B1611029 : Blo 952587 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B8262965 : Blo 952587 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B3216725 : Blo 952587 3216725 := bbase (se 14 (by rfl) ⟨294, by rfl⟩ : syracuseStep 3216725 = 589) (by norm_num)
theorem B13079893 : Blo 952587 13079893 := bbase (se 14 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 13079893 = 2395) (by norm_num)
theorem B1611157 : Blo 952587 1611157 := bbase (se 6 (by rfl) ⟨37761, by rfl⟩ : syracuseStep 1611157 = 75523) (by norm_num)
theorem B1611245 : Blo 952587 1611245 := bbase (se 3 (by rfl) ⟨302108, by rfl⟩ : syracuseStep 1611245 = 604217) (by norm_num)
theorem B3053045 : Blo 952587 3053045 := bbase (se 5 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 3053045 = 286223) (by norm_num)
theorem B9180661 : Blo 952587 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B1611373 : Blo 952587 1611373 := bbase (se 3 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 1611373 = 604265) (by norm_num)
theorem B3053173 : Blo 952587 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B1939061 : Blo 952587 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B2037413 : Blo 952587 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B1611461 : Blo 952587 1611461 := bbase (se 4 (by rfl) ⟨151074, by rfl⟩ : syracuseStep 1611461 = 302149) (by norm_num)
theorem B3217157 : Blo 952587 3217157 := bbase (se 4 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 3217157 = 603217) (by norm_num)
theorem B1611589 : Blo 952587 1611589 := bbase (se 4 (by rfl) ⟨151086, by rfl⟩ : syracuseStep 1611589 = 302173) (by norm_num)
theorem B4822901 : Blo 952587 4822901 := bbase (se 5 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 4822901 = 452147) (by norm_num)
theorem B3053429 : Blo 952587 3053429 := bbase (se 5 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 3053429 = 286259) (by norm_num)
theorem B1611677 : Blo 952587 1611677 := bbase (se 3 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 1611677 = 604379) (by norm_num)
theorem B1611805 : Blo 952587 1611805 := bbase (se 3 (by rfl) ⟨302213, by rfl⟩ : syracuseStep 1611805 = 604427) (by norm_num)
theorem B1611893 : Blo 952587 1611893 := bbase (se 5 (by rfl) ⟨75557, by rfl⟩ : syracuseStep 1611893 = 151115) (by norm_num)
theorem B3217589 : Blo 952587 3217589 := bbase (se 5 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 3217589 = 301649) (by norm_num)
theorem B1808581 : Blo 952587 1808581 := bbase (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) (by norm_num)
theorem B1612021 : Blo 952587 1612021 := bbase (se 5 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 1612021 = 151127) (by norm_num)
theorem B1612109 : Blo 952587 1612109 := bbase (se 3 (by rfl) ⟨302270, by rfl⟩ : syracuseStep 1612109 = 604541) (by norm_num)
theorem B1808725 : Blo 952587 1808725 := bbase (se 10 (by rfl) ⟨2649, by rfl⟩ : syracuseStep 1808725 = 5299) (by norm_num)
theorem B2070893 : Blo 952587 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B956845 : Blo 952587 956845 := bbase (se 3 (by rfl) ⟨179408, by rfl⟩ : syracuseStep 956845 = 358817) (by norm_num)
theorem B1612237 : Blo 952587 1612237 := bbase (se 3 (by rfl) ⟨302294, by rfl⟩ : syracuseStep 1612237 = 604589) (by norm_num)
theorem B1808885 : Blo 952587 1808885 := bbase (se 5 (by rfl) ⟨84791, by rfl⟩ : syracuseStep 1808885 = 169583) (by norm_num)
theorem B2038277 : Blo 952587 2038277 := bbase (se 4 (by rfl) ⟨191088, by rfl⟩ : syracuseStep 2038277 = 382177) (by norm_num)
theorem B1612325 : Blo 952587 1612325 := bbase (se 4 (by rfl) ⟨151155, by rfl⟩ : syracuseStep 1612325 = 302311) (by norm_num)
theorem B3218021 : Blo 952587 3218021 := bbase (se 4 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 3218021 = 603379) (by norm_num)
theorem B1809029 : Blo 952587 1809029 := bbase (se 4 (by rfl) ⟨169596, by rfl⟩ : syracuseStep 1809029 = 339193) (by norm_num)
theorem B2038421 : Blo 952587 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B1612453 : Blo 952587 1612453 := bbase (se 4 (by rfl) ⟨151167, by rfl⟩ : syracuseStep 1612453 = 302335) (by norm_num)
theorem B1612541 : Blo 952587 1612541 := bbase (se 3 (by rfl) ⟨302351, by rfl⟩ : syracuseStep 1612541 = 604703) (by norm_num)
theorem B4070213 : Blo 952587 4070213 := bbase (se 4 (by rfl) ⟨381582, by rfl⟩ : syracuseStep 4070213 = 763165) (by norm_num)
theorem B1612669 : Blo 952587 1612669 := bbase (se 3 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 1612669 = 604751) (by norm_num)
theorem B1809317 : Blo 952587 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B1612757 : Blo 952587 1612757 := bbase (se 7 (by rfl) ⟨18899, by rfl⟩ : syracuseStep 1612757 = 37799) (by norm_num)
theorem B3218453 : Blo 952587 3218453 := bbase (se 6 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 3218453 = 150865) (by norm_num)
theorem B1088569 : Blo 952587 1088569 := bbase (se 2 (by rfl) ⟨408213, by rfl⟩ : syracuseStep 1088569 = 816427) (by norm_num)
theorem B1809469 : Blo 952587 1809469 := bbase (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) (by norm_num)
theorem B1612885 : Blo 952587 1612885 := bbase (se 8 (by rfl) ⟨9450, by rfl⟩ : syracuseStep 1612885 = 18901) (by norm_num)
theorem B4824197 : Blo 952587 4824197 := bbase (se 4 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 4824197 = 904537) (by norm_num)
theorem B1612973 : Blo 952587 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B1613101 : Blo 952587 1613101 := bbase (se 3 (by rfl) ⟨302456, by rfl⟩ : syracuseStep 1613101 = 604913) (by norm_num)
theorem B5446997 : Blo 952587 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B1809773 : Blo 952587 1809773 := bbase (se 3 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 1809773 = 678665) (by norm_num)
theorem B2039165 : Blo 952587 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1613189 : Blo 952587 1613189 := bbase (se 4 (by rfl) ⟨151236, by rfl⟩ : syracuseStep 1613189 = 302473) (by norm_num)
theorem B3218885 : Blo 952587 3218885 := bbase (se 4 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 3218885 = 603541) (by norm_num)
theorem B1613317 : Blo 952587 1613317 := bbase (se 4 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 1613317 = 302497) (by norm_num)
theorem B1613405 : Blo 952587 1613405 := bbase (se 3 (by rfl) ⟨302513, by rfl⟩ : syracuseStep 1613405 = 605027) (by norm_num)
theorem B1089221 : Blo 952587 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1613533 : Blo 952587 1613533 := bbase (se 3 (by rfl) ⟨302537, by rfl⟩ : syracuseStep 1613533 = 605075) (by norm_num)
theorem B1548077 : Blo 952587 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B1613621 : Blo 952587 1613621 := bbase (se 5 (by rfl) ⟨75638, by rfl⟩ : syracuseStep 1613621 = 151277) (by norm_num)
theorem B3219317 : Blo 952587 3219317 := bbase (se 5 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 3219317 = 301811) (by norm_num)
theorem B1089445 : Blo 952587 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1613749 : Blo 952587 1613749 := bbase (se 5 (by rfl) ⟨75644, by rfl⟩ : syracuseStep 1613749 = 151289) (by norm_num)
theorem B1613837 : Blo 952587 1613837 := bbase (se 3 (by rfl) ⟨302594, by rfl⟩ : syracuseStep 1613837 = 605189) (by norm_num)
theorem B1810525 : Blo 952587 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B2039917 : Blo 952587 2039917 := bbase (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) (by norm_num)
theorem B1613965 : Blo 952587 1613965 := bbase (se 3 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 1613965 = 605237) (by norm_num)
theorem B1614053 : Blo 952587 1614053 := bbase (se 4 (by rfl) ⟨151317, by rfl⟩ : syracuseStep 1614053 = 302635) (by norm_num)
theorem B1810669 : Blo 952587 1810669 := bbase (se 3 (by rfl) ⟨339500, by rfl⟩ : syracuseStep 1810669 = 679001) (by norm_num)
theorem B2040061 : Blo 952587 2040061 := bbase (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) (by norm_num)
theorem B3055877 : Blo 952587 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B3219749 : Blo 952587 3219749 := bbase (se 4 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 3219749 = 603703) (by norm_num)
theorem B1614181 : Blo 952587 1614181 := bbase (se 4 (by rfl) ⟨151329, by rfl⟩ : syracuseStep 1614181 = 302659) (by norm_num)
theorem B1810829 : Blo 952587 1810829 := bbase (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) (by norm_num)
theorem B4825493 : Blo 952587 4825493 := bbase (se 6 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 4825493 = 226195) (by norm_num)
theorem B1450477 : Blo 952587 1450477 := bbase (se 3 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 1450477 = 543929) (by norm_num)
theorem B1810973 : Blo 952587 1810973 := bbase (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) (by norm_num)
theorem B27927125 : Blo 952587 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B2040437 : Blo 952587 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B3220181 : Blo 952587 3220181 := bbase (se 7 (by rfl) ⟨37736, by rfl⟩ : syracuseStep 3220181 = 75473) (by norm_num)
theorem B1811261 : Blo 952587 1811261 := bbase (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) (by norm_num)
theorem B8168309 : Blo 952587 8168309 := bbase (se 5 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 8168309 = 765779) (by norm_num)
theorem B1811413 : Blo 952587 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B2040805 : Blo 952587 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B3220613 : Blo 952587 3220613 := bbase (se 4 (by rfl) ⟨301932, by rfl⟩ : syracuseStep 3220613 = 603865) (by norm_num)
theorem B1811717 : Blo 952587 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B1287517 : Blo 952587 1287517 := bbase (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) (by norm_num)
theorem B3221045 : Blo 952587 3221045 := bbase (se 5 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 3221045 = 301973) (by norm_num)
theorem B3057221 : Blo 952587 3057221 := bbase (se 4 (by rfl) ⟨286614, by rfl⟩ : syracuseStep 3057221 = 573229) (by norm_num)
theorem B6530645 : Blo 952587 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B9184853 : Blo 952587 9184853 := bbase (se 8 (by rfl) ⟨53817, by rfl⟩ : syracuseStep 9184853 = 107635) (by norm_num)
theorem B7251605 : Blo 952587 7251605 := bbase (se 6 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 7251605 = 339919) (by norm_num)
theorem B4826789 : Blo 952587 4826789 := bbase (se 4 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 4826789 = 905023) (by norm_num)
theorem B1287949 : Blo 952587 1287949 := bbase (se 3 (by rfl) ⟨241490, by rfl⟩ : syracuseStep 1287949 = 482981) (by norm_num)
theorem B3221477 : Blo 952587 3221477 := bbase (se 4 (by rfl) ⟨302013, by rfl⟩ : syracuseStep 3221477 = 604027) (by norm_num)
theorem B1812469 : Blo 952587 1812469 := bbase (se 5 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 1812469 = 169919) (by norm_num)
theorem B1812613 : Blo 952587 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B1812773 : Blo 952587 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B3221909 : Blo 952587 3221909 := bbase (se 6 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 3221909 = 151027) (by norm_num)
theorem B1812917 : Blo 952587 1812917 := bbase (se 5 (by rfl) ⟨84980, by rfl⟩ : syracuseStep 1812917 = 169961) (by norm_num)
theorem B2042309 : Blo 952587 2042309 := bbase (se 4 (by rfl) ⟨191466, by rfl⟩ : syracuseStep 2042309 = 382933) (by norm_num)
theorem B2042453 : Blo 952587 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B1813205 : Blo 952587 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B4074245 : Blo 952587 4074245 := bbase (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) (by norm_num)
theorem B3222341 : Blo 952587 3222341 := bbase (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) (by norm_num)
theorem B3877733 : Blo 952587 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B1813357 : Blo 952587 1813357 := bbase (se 3 (by rfl) ⟨340004, by rfl⟩ : syracuseStep 1813357 = 680009) (by norm_num)
theorem B2173853 : Blo 952587 2173853 := bbase (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) (by norm_num)
theorem B4828085 : Blo 952587 4828085 := bbase (se 5 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 4828085 = 452633) (by norm_num)
theorem B2042813 : Blo 952587 2042813 := bbase (se 3 (by rfl) ⟨383027, by rfl⟩ : syracuseStep 2042813 = 766055) (by norm_num)
theorem B1813661 : Blo 952587 1813661 := bbase (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) (by norm_num)
theorem B3222773 : Blo 952587 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B8138069 : Blo 952587 8138069 := bbase (se 11 (by rfl) ⟨5960, by rfl⟩ : syracuseStep 8138069 = 11921) (by norm_num)
theorem B6106549 : Blo 952587 6106549 := bbase (se 5 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 6106549 = 572489) (by norm_num)
theorem B1453493 : Blo 952587 1453493 := bbase (se 5 (by rfl) ⟨68132, by rfl⟩ : syracuseStep 1453493 = 136265) (by norm_num)
theorem B1224157 : Blo 952587 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B3059221 : Blo 952587 3059221 := bbase (se 6 (by rfl) ⟨71700, by rfl⟩ : syracuseStep 3059221 = 143401) (by norm_num)
theorem B10333781 : Blo 952587 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B3223205 : Blo 952587 3223205 := bbase (se 4 (by rfl) ⟨302175, by rfl⟩ : syracuseStep 3223205 = 604351) (by norm_num)
theorem B5812021 : Blo 952587 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B1814413 : Blo 952587 1814413 := bbase (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) (by norm_num)
theorem B1224661 : Blo 952587 1224661 := bbase (se 7 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 1224661 = 28703) (by norm_num)
theorem B1814557 : Blo 952587 1814557 := bbase (se 3 (by rfl) ⟨340229, by rfl⟩ : syracuseStep 1814557 = 680459) (by norm_num)
theorem B3223637 : Blo 952587 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B3616933 : Blo 952587 3616933 := bbase (se 4 (by rfl) ⟨339087, by rfl⟩ : syracuseStep 3616933 = 678175) (by norm_num)
theorem B1814717 : Blo 952587 1814717 := bbase (se 3 (by rfl) ⟨340259, by rfl⟩ : syracuseStep 1814717 = 680519) (by norm_num)
theorem B4829381 : Blo 952587 4829381 := bbase (se 4 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 4829381 = 905509) (by norm_num)
theorem B1454357 : Blo 952587 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B1814861 : Blo 952587 1814861 := bbase (se 3 (by rfl) ⟨340286, by rfl⟩ : syracuseStep 1814861 = 680573) (by norm_num)
theorem B3617237 : Blo 952587 3617237 := bbase (se 7 (by rfl) ⟨42389, by rfl⟩ : syracuseStep 3617237 = 84779) (by norm_num)
theorem B4076021 : Blo 952587 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B3224069 : Blo 952587 3224069 := bbase (se 4 (by rfl) ⟨302256, by rfl⟩ : syracuseStep 3224069 = 604513) (by norm_num)
theorem B1356373 : Blo 952587 1356373 := bbase (se 8 (by rfl) ⟨7947, by rfl⟩ : syracuseStep 1356373 = 15895) (by norm_num)
theorem B1815149 : Blo 952587 1815149 := bbase (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) (by norm_num)
theorem B1815301 : Blo 952587 1815301 := bbase (se 4 (by rfl) ⟨170184, by rfl⟩ : syracuseStep 1815301 = 340369) (by norm_num)
theorem B3224501 : Blo 952587 3224501 := bbase (se 5 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 3224501 = 302297) (by norm_num)
theorem B1717237 : Blo 952587 1717237 := bbase (se 5 (by rfl) ⟨80495, by rfl⟩ : syracuseStep 1717237 = 160991) (by norm_num)
theorem B1815605 : Blo 952587 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B1160281 : Blo 952587 1160281 := bbase (se 2 (by rfl) ⟨435105, by rfl⟩ : syracuseStep 1160281 = 870211) (by norm_num)
theorem B2143349 : Blo 952587 2143349 := bbase (se 5 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 2143349 = 200939) (by norm_num)
theorem B2143421 : Blo 952587 2143421 := bbase (se 3 (by rfl) ⟨401891, by rfl⟩ : syracuseStep 2143421 = 803783) (by norm_num)
theorem B1717453 : Blo 952587 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B2143493 : Blo 952587 2143493 := bbase (se 4 (by rfl) ⟨200952, by rfl⟩ : syracuseStep 2143493 = 401905) (by norm_num)
theorem B2143565 : Blo 952587 2143565 := bbase (se 3 (by rfl) ⟨401918, by rfl⟩ : syracuseStep 2143565 = 803837) (by norm_num)
theorem B3224933 : Blo 952587 3224933 := bbase (se 4 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 3224933 = 604675) (by norm_num)
theorem B1357165 : Blo 952587 1357165 := bbase (se 3 (by rfl) ⟨254468, by rfl⟩ : syracuseStep 1357165 = 508937) (by norm_num)
theorem B2143637 : Blo 952587 2143637 := bbase (se 6 (by rfl) ⟨50241, by rfl⟩ : syracuseStep 2143637 = 100483) (by norm_num)
theorem B4830677 : Blo 952587 4830677 := bbase (se 7 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 4830677 = 113219) (by norm_num)
theorem B4077013 : Blo 952587 4077013 := bbase (se 7 (by rfl) ⟨47777, by rfl⟩ : syracuseStep 4077013 = 95555) (by norm_num)
theorem B2143709 : Blo 952587 2143709 := bbase (se 3 (by rfl) ⟨401945, by rfl⟩ : syracuseStep 2143709 = 803891) (by norm_num)
theorem B2143781 : Blo 952587 2143781 := bbase (se 4 (by rfl) ⟨200979, by rfl⟩ : syracuseStep 2143781 = 401959) (by norm_num)
theorem B2143853 : Blo 952587 2143853 := bbase (se 3 (by rfl) ⟨401972, by rfl⟩ : syracuseStep 2143853 = 803945) (by norm_num)
theorem B2143925 : Blo 952587 2143925 := bbase (se 5 (by rfl) ⟨100496, by rfl⟩ : syracuseStep 2143925 = 200993) (by norm_num)
theorem B1357501 : Blo 952587 1357501 := bbase (se 3 (by rfl) ⟨254531, by rfl⟩ : syracuseStep 1357501 = 509063) (by norm_num)
theorem B2143997 : Blo 952587 2143997 := bbase (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) (by norm_num)
theorem B3225365 : Blo 952587 3225365 := bbase (se 6 (by rfl) ⟨75594, by rfl⟩ : syracuseStep 3225365 = 151189) (by norm_num)
theorem B1292069 : Blo 952587 1292069 := bbase (se 4 (by rfl) ⟨121131, by rfl⟩ : syracuseStep 1292069 = 242263) (by norm_num)
theorem B2144069 : Blo 952587 2144069 := bbase (se 4 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 2144069 = 402013) (by norm_num)
theorem B2144141 : Blo 952587 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B1357717 : Blo 952587 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B2144213 : Blo 952587 2144213 := bbase (se 7 (by rfl) ⟨25127, by rfl⟩ : syracuseStep 2144213 = 50255) (by norm_num)
theorem B1718261 : Blo 952587 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B2144285 : Blo 952587 2144285 := bbase (se 3 (by rfl) ⟨402053, by rfl⟩ : syracuseStep 2144285 = 804107) (by norm_num)
theorem B2144357 : Blo 952587 2144357 := bbase (se 4 (by rfl) ⟨201033, by rfl⟩ : syracuseStep 2144357 = 402067) (by norm_num)
theorem B2144429 : Blo 952587 2144429 := bbase (se 3 (by rfl) ⟨402080, by rfl⟩ : syracuseStep 2144429 = 804161) (by norm_num)
theorem B3225797 : Blo 952587 3225797 := bbase (se 4 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 3225797 = 604837) (by norm_num)
theorem B2144501 : Blo 952587 2144501 := bbase (se 5 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 2144501 = 201047) (by norm_num)
theorem B1358093 : Blo 952587 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B2144573 : Blo 952587 2144573 := bbase (se 3 (by rfl) ⟨402107, by rfl⟩ : syracuseStep 2144573 = 804215) (by norm_num)
theorem B2144645 : Blo 952587 2144645 := bbase (se 4 (by rfl) ⟨201060, by rfl⟩ : syracuseStep 2144645 = 402121) (by norm_num)
theorem B2144717 : Blo 952587 2144717 := bbase (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) (by norm_num)
theorem B3062245 : Blo 952587 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B1161745 : Blo 952587 1161745 := bbase (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) (by norm_num)
theorem B2144789 : Blo 952587 2144789 := bbase (se 6 (by rfl) ⟨50268, by rfl⟩ : syracuseStep 2144789 = 100537) (by norm_num)
theorem B3619349 : Blo 952587 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B2144861 : Blo 952587 2144861 := bbase (se 3 (by rfl) ⟨402161, by rfl⟩ : syracuseStep 2144861 = 804323) (by norm_num)
theorem B3226229 : Blo 952587 3226229 := bbase (se 5 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 3226229 = 302459) (by norm_num)
theorem B2144933 : Blo 952587 2144933 := bbase (se 4 (by rfl) ⟨201087, by rfl⟩ : syracuseStep 2144933 = 402175) (by norm_num)
theorem B4831973 : Blo 952587 4831973 := bbase (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) (by norm_num)
theorem B2145005 : Blo 952587 2145005 := bbase (se 3 (by rfl) ⟨402188, by rfl⟩ : syracuseStep 2145005 = 804377) (by norm_num)
theorem B3619637 : Blo 952587 3619637 := bbase (se 5 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 3619637 = 339341) (by norm_num)
theorem B2145077 : Blo 952587 2145077 := bbase (se 5 (by rfl) ⟨100550, by rfl⟩ : syracuseStep 2145077 = 201101) (by norm_num)
theorem B1260353 : Blo 952587 1260353 := bbase (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) (by norm_num)
theorem B2145149 : Blo 952587 2145149 := bbase (se 3 (by rfl) ⟨402215, by rfl⟩ : syracuseStep 2145149 = 804431) (by norm_num)
theorem B2145221 : Blo 952587 2145221 := bbase (se 4 (by rfl) ⟨201114, by rfl⟩ : syracuseStep 2145221 = 402229) (by norm_num)
theorem B2145293 : Blo 952587 2145293 := bbase (se 3 (by rfl) ⟨402242, by rfl⟩ : syracuseStep 2145293 = 804485) (by norm_num)
theorem B2178085 : Blo 952587 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B3226661 : Blo 952587 3226661 := bbase (se 4 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 3226661 = 604999) (by norm_num)
theorem B2145365 : Blo 952587 2145365 := bbase (se 8 (by rfl) ⟨12570, by rfl⟩ : syracuseStep 2145365 = 25141) (by norm_num)
theorem B2145437 : Blo 952587 2145437 := bbase (se 3 (by rfl) ⟨402269, by rfl⟩ : syracuseStep 2145437 = 804539) (by norm_num)
theorem B2145509 : Blo 952587 2145509 := bbase (se 4 (by rfl) ⟨201141, by rfl⟩ : syracuseStep 2145509 = 402283) (by norm_num)
theorem B2178341 : Blo 952587 2178341 := bbase (se 4 (by rfl) ⟨204219, by rfl⟩ : syracuseStep 2178341 = 408439) (by norm_num)
theorem B2145581 : Blo 952587 2145581 := bbase (se 3 (by rfl) ⟨402296, by rfl⟩ : syracuseStep 2145581 = 804593) (by norm_num)
theorem B2145653 : Blo 952587 2145653 := bbase (se 5 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 2145653 = 201155) (by norm_num)
theorem B2833829 : Blo 952587 2833829 := bbase (se 4 (by rfl) ⟨265671, by rfl⟩ : syracuseStep 2833829 = 531343) (by norm_num)
theorem B2145725 : Blo 952587 2145725 := bbase (se 3 (by rfl) ⟨402323, by rfl⟩ : syracuseStep 2145725 = 804647) (by norm_num)
theorem B3227093 : Blo 952587 3227093 := bbase (se 7 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 3227093 = 75635) (by norm_num)
theorem B2145797 : Blo 952587 2145797 := bbase (se 4 (by rfl) ⟨201168, by rfl⟩ : syracuseStep 2145797 = 402337) (by norm_num)
theorem B2145869 : Blo 952587 2145869 := bbase (se 3 (by rfl) ⟨402350, by rfl⟩ : syracuseStep 2145869 = 804701) (by norm_num)
theorem B3096181 : Blo 952587 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B2145941 : Blo 952587 2145941 := bbase (se 6 (by rfl) ⟨50295, by rfl⟩ : syracuseStep 2145941 = 100591) (by norm_num)
theorem B1359517 : Blo 952587 1359517 := bbase (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) (by norm_num)
theorem B2146013 : Blo 952587 2146013 := bbase (se 3 (by rfl) ⟨402377, by rfl⟩ : syracuseStep 2146013 = 804755) (by norm_num)
theorem B2146085 : Blo 952587 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B2146157 : Blo 952587 2146157 := bbase (se 3 (by rfl) ⟨402404, by rfl⟩ : syracuseStep 2146157 = 804809) (by norm_num)
theorem B6537077 : Blo 952587 6537077 := bbase (se 5 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 6537077 = 612851) (by norm_num)
theorem B3227525 : Blo 952587 3227525 := bbase (se 4 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 3227525 = 605161) (by norm_num)
theorem B3260341 : Blo 952587 3260341 := bbase (se 5 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 3260341 = 305657) (by norm_num)
theorem B2146229 : Blo 952587 2146229 := bbase (se 5 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 2146229 = 201209) (by norm_num)
theorem B3620821 : Blo 952587 3620821 := bbase (se 7 (by rfl) ⟨42431, by rfl⟩ : syracuseStep 3620821 = 84863) (by norm_num)
theorem B4833269 : Blo 952587 4833269 := bbase (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) (by norm_num)
theorem B2146301 : Blo 952587 2146301 := bbase (se 3 (by rfl) ⟨402431, by rfl⟩ : syracuseStep 2146301 = 804863) (by norm_num)
theorem B2146373 : Blo 952587 2146373 := bbase (se 4 (by rfl) ⟨201222, by rfl⟩ : syracuseStep 2146373 = 402445) (by norm_num)
theorem B2900053 : Blo 952587 2900053 := bbase (se 8 (by rfl) ⟨16992, by rfl⟩ : syracuseStep 2900053 = 33985) (by norm_num)
theorem B6701173 : Blo 952587 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B966773 : Blo 952587 966773 := bbase (se 5 (by rfl) ⟨45317, by rfl⟩ : syracuseStep 966773 = 90635) (by norm_num)
theorem B2146445 : Blo 952587 2146445 := bbase (se 3 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 2146445 = 804917) (by norm_num)
theorem B966805 : Blo 952587 966805 := bbase (se 6 (by rfl) ⟨22659, by rfl⟩ : syracuseStep 966805 = 45319) (by norm_num)
theorem B2179253 : Blo 952587 2179253 := bbase (se 5 (by rfl) ⟨102152, by rfl⟩ : syracuseStep 2179253 = 204305) (by norm_num)
theorem B2146517 : Blo 952587 2146517 := bbase (se 7 (by rfl) ⟨25154, by rfl⟩ : syracuseStep 2146517 = 50309) (by norm_num)
theorem B1360109 : Blo 952587 1360109 := bbase (se 3 (by rfl) ⟨255020, by rfl⟩ : syracuseStep 1360109 = 510041) (by norm_num)
theorem B3621125 : Blo 952587 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B2146589 : Blo 952587 2146589 := bbase (se 3 (by rfl) ⟨402485, by rfl⟩ : syracuseStep 2146589 = 804971) (by norm_num)
theorem B3227957 : Blo 952587 3227957 := bbase (se 5 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 3227957 = 302621) (by norm_num)
theorem B1360189 : Blo 952587 1360189 := bbase (se 3 (by rfl) ⟨255035, by rfl⟩ : syracuseStep 1360189 = 510071) (by norm_num)
theorem B2146661 : Blo 952587 2146661 := bbase (se 4 (by rfl) ⟨201249, by rfl⟩ : syracuseStep 2146661 = 402499) (by norm_num)
theorem B2146733 : Blo 952587 2146733 := bbase (se 3 (by rfl) ⟨402512, by rfl⟩ : syracuseStep 2146733 = 805025) (by norm_num)
theorem B1360309 : Blo 952587 1360309 := bbase (se 5 (by rfl) ⟨63764, by rfl⟩ : syracuseStep 1360309 = 127529) (by norm_num)
theorem B5816789 : Blo 952587 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B2146805 : Blo 952587 2146805 := bbase (se 5 (by rfl) ⟨100631, by rfl⟩ : syracuseStep 2146805 = 201263) (by norm_num)
theorem B15483413 : Blo 952587 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B1360405 : Blo 952587 1360405 := bbase (se 6 (by rfl) ⟨31884, by rfl⟩ : syracuseStep 1360405 = 63769) (by norm_num)
theorem B2146877 : Blo 952587 2146877 := bbase (se 3 (by rfl) ⟨402539, by rfl⟩ : syracuseStep 2146877 = 805079) (by norm_num)
theorem B2146949 : Blo 952587 2146949 := bbase (se 4 (by rfl) ⟨201276, by rfl⟩ : syracuseStep 2146949 = 402553) (by norm_num)
theorem B1721029 : Blo 952587 1721029 := bbase (se 4 (by rfl) ⟨161346, by rfl⟩ : syracuseStep 1721029 = 322693) (by norm_num)
theorem B2147021 : Blo 952587 2147021 := bbase (se 3 (by rfl) ⟨402566, by rfl⟩ : syracuseStep 2147021 = 805133) (by norm_num)
theorem B3228389 : Blo 952587 3228389 := bbase (se 4 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 3228389 = 605323) (by norm_num)
theorem B1721101 : Blo 952587 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B2147093 : Blo 952587 2147093 := bbase (se 6 (by rfl) ⟨50322, by rfl⟩ : syracuseStep 2147093 = 100645) (by norm_num)
theorem B2147165 : Blo 952587 2147165 := bbase (se 3 (by rfl) ⟨402593, by rfl⟩ : syracuseStep 2147165 = 805187) (by norm_num)
theorem B1721245 : Blo 952587 1721245 := bbase (se 3 (by rfl) ⟨322733, by rfl⟩ : syracuseStep 1721245 = 645467) (by norm_num)
theorem B2147237 : Blo 952587 2147237 := bbase (se 4 (by rfl) ⟨201303, by rfl⟩ : syracuseStep 2147237 = 402607) (by norm_num)
theorem B967645 : Blo 952587 967645 := bbase (se 3 (by rfl) ⟨181433, by rfl⟩ : syracuseStep 967645 = 362867) (by norm_num)
theorem B2147309 : Blo 952587 2147309 := bbase (se 3 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 2147309 = 805241) (by norm_num)
theorem B1360901 : Blo 952587 1360901 := bbase (se 4 (by rfl) ⟨127584, by rfl⟩ : syracuseStep 1360901 = 255169) (by norm_num)
theorem B2147381 : Blo 952587 2147381 := bbase (se 5 (by rfl) ⟨100658, by rfl⟩ : syracuseStep 2147381 = 201317) (by norm_num)
theorem B2147453 : Blo 952587 2147453 := bbase (se 3 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 2147453 = 805295) (by norm_num)
theorem B2147525 : Blo 952587 2147525 := bbase (se 4 (by rfl) ⟨201330, by rfl⟩ : syracuseStep 2147525 = 402661) (by norm_num)
theorem B7259381 : Blo 952587 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B4834565 : Blo 952587 4834565 := bbase (se 4 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 4834565 = 906481) (by norm_num)
theorem B2147597 : Blo 952587 2147597 := bbase (se 3 (by rfl) ⟨402674, by rfl⟩ : syracuseStep 2147597 = 805349) (by norm_num)
theorem B6112597 : Blo 952587 6112597 := bbase (se 12 (by rfl) ⟨2238, by rfl⟩ : syracuseStep 6112597 = 4477) (by norm_num)
theorem B2147669 : Blo 952587 2147669 := bbase (se 12 (by rfl) ⟨786, by rfl⟩ : syracuseStep 2147669 = 1573) (by norm_num)
theorem B2147741 : Blo 952587 2147741 := bbase (se 3 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 2147741 = 805403) (by norm_num)
theorem B2147813 : Blo 952587 2147813 := bbase (se 4 (by rfl) ⟨201357, by rfl⟩ : syracuseStep 2147813 = 402715) (by norm_num)
theorem B2147885 : Blo 952587 2147885 := bbase (se 3 (by rfl) ⟨402728, by rfl⟩ : syracuseStep 2147885 = 805457) (by norm_num)
theorem B1361453 : Blo 952587 1361453 := bbase (se 3 (by rfl) ⟨255272, by rfl⟩ : syracuseStep 1361453 = 510545) (by norm_num)
theorem B2147957 : Blo 952587 2147957 := bbase (se 5 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 2147957 = 201371) (by norm_num)
theorem B2148029 : Blo 952587 2148029 := bbase (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) (by norm_num)
theorem B1722053 : Blo 952587 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B1722109 : Blo 952587 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B2148101 : Blo 952587 2148101 := bbase (se 4 (by rfl) ⟨201384, by rfl⟩ : syracuseStep 2148101 = 402769) (by norm_num)
theorem B968521 : Blo 952587 968521 := bbase (se 2 (by rfl) ⟨363195, by rfl⟩ : syracuseStep 968521 = 726391) (by norm_num)
theorem B2148173 : Blo 952587 2148173 := bbase (se 3 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 2148173 = 805565) (by norm_num)
theorem B1722197 : Blo 952587 1722197 := bbase (se 9 (by rfl) ⟨5045, by rfl⟩ : syracuseStep 1722197 = 10091) (by norm_num)
theorem B2148245 : Blo 952587 2148245 := bbase (se 6 (by rfl) ⟨50349, by rfl⟩ : syracuseStep 2148245 = 100699) (by norm_num)
theorem B2148317 : Blo 952587 2148317 := bbase (se 3 (by rfl) ⟨402809, by rfl⟩ : syracuseStep 2148317 = 805619) (by norm_num)
theorem B4900837 : Blo 952587 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B2148389 : Blo 952587 2148389 := bbase (se 4 (by rfl) ⟨201411, by rfl⟩ : syracuseStep 2148389 = 402823) (by norm_num)
theorem B2148461 : Blo 952587 2148461 := bbase (se 3 (by rfl) ⟨402836, by rfl⟩ : syracuseStep 2148461 = 805673) (by norm_num)
theorem B1722485 : Blo 952587 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B2148533 : Blo 952587 2148533 := bbase (se 5 (by rfl) ⟨100712, by rfl⟩ : syracuseStep 2148533 = 201425) (by norm_num)
theorem B2148605 : Blo 952587 2148605 := bbase (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) (by norm_num)
theorem B1722629 : Blo 952587 1722629 := bbase (se 4 (by rfl) ⟨161496, by rfl⟩ : syracuseStep 1722629 = 322993) (by norm_num)
theorem B3623237 : Blo 952587 3623237 := bbase (se 4 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 3623237 = 679357) (by norm_num)
theorem B2148677 : Blo 952587 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B4082021 : Blo 952587 4082021 := bbase (se 4 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 4082021 = 765379) (by norm_num)
theorem B2148749 : Blo 952587 2148749 := bbase (se 3 (by rfl) ⟨402890, by rfl⟩ : syracuseStep 2148749 = 805781) (by norm_num)
theorem B2148821 : Blo 952587 2148821 := bbase (se 7 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 2148821 = 50363) (by norm_num)
theorem B4835861 : Blo 952587 4835861 := bbase (se 6 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 4835861 = 226681) (by norm_num)
theorem B2148893 : Blo 952587 2148893 := bbase (se 3 (by rfl) ⟨402917, by rfl⟩ : syracuseStep 2148893 = 805835) (by norm_num)
theorem B1722917 : Blo 952587 1722917 := bbase (se 4 (by rfl) ⟨161523, by rfl⟩ : syracuseStep 1722917 = 323047) (by norm_num)
theorem B3623525 : Blo 952587 3623525 := bbase (se 4 (by rfl) ⟨339705, by rfl⟩ : syracuseStep 3623525 = 679411) (by norm_num)
theorem B2148965 : Blo 952587 2148965 := bbase (se 4 (by rfl) ⟨201465, by rfl⟩ : syracuseStep 2148965 = 402931) (by norm_num)
theorem B1722989 : Blo 952587 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B4082309 : Blo 952587 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B2149037 : Blo 952587 2149037 := bbase (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) (by norm_num)
theorem B1526509 : Blo 952587 1526509 := bbase (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) (by norm_num)
theorem B2149109 : Blo 952587 2149109 := bbase (se 5 (by rfl) ⟨100739, by rfl⟩ : syracuseStep 2149109 = 201479) (by norm_num)
theorem B1035017 : Blo 952587 1035017 := bbase (se 2 (by rfl) ⟨388131, by rfl⟩ : syracuseStep 1035017 = 776263) (by norm_num)
theorem B2411309 : Blo 952587 2411309 := bbase (se 3 (by rfl) ⟨452120, by rfl⟩ : syracuseStep 2411309 = 904241) (by norm_num)
theorem B2149181 : Blo 952587 2149181 := bbase (se 3 (by rfl) ⟨402971, by rfl⟩ : syracuseStep 2149181 = 805943) (by norm_num)
theorem B1035109 : Blo 952587 1035109 := bbase (se 4 (by rfl) ⟨97041, by rfl⟩ : syracuseStep 1035109 = 194083) (by norm_num)
theorem B2149253 : Blo 952587 2149253 := bbase (se 4 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 2149253 = 402985) (by norm_num)
theorem B2149325 : Blo 952587 2149325 := bbase (se 3 (by rfl) ⟨402998, by rfl⟩ : syracuseStep 2149325 = 805997) (by norm_num)
theorem B2149397 : Blo 952587 2149397 := bbase (se 6 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 2149397 = 100753) (by norm_num)
theorem B2149469 : Blo 952587 2149469 := bbase (se 3 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 2149469 = 806051) (by norm_num)
theorem B2411653 : Blo 952587 2411653 := bbase (se 4 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 2411653 = 452185) (by norm_num)
theorem B1526933 : Blo 952587 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B2149541 : Blo 952587 2149541 := bbase (se 4 (by rfl) ⟨201519, by rfl⟩ : syracuseStep 2149541 = 403039) (by norm_num)
theorem B2149613 : Blo 952587 2149613 := bbase (se 3 (by rfl) ⟨403052, by rfl⟩ : syracuseStep 2149613 = 806105) (by norm_num)
theorem B2411765 : Blo 952587 2411765 := bbase (se 5 (by rfl) ⟨113051, by rfl⟩ : syracuseStep 2411765 = 226103) (by norm_num)
theorem B9784597 : Blo 952587 9784597 := bbase (se 6 (by rfl) ⟨229326, by rfl⟩ : syracuseStep 9784597 = 458653) (by norm_num)
theorem B2149685 : Blo 952587 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B4083061 : Blo 952587 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B2149757 : Blo 952587 2149757 := bbase (se 3 (by rfl) ⟨403079, by rfl⟩ : syracuseStep 2149757 = 806159) (by norm_num)
theorem B1428893 : Blo 952587 1428893 := bbase (se 3 (by rfl) ⟨267917, by rfl⟩ : syracuseStep 1428893 = 535835) (by norm_num)
theorem B1428917 : Blo 952587 1428917 := bbase (se 5 (by rfl) ⟨66980, by rfl⟩ : syracuseStep 1428917 = 133961) (by norm_num)
theorem B2411957 : Blo 952587 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B1527221 : Blo 952587 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B2149829 : Blo 952587 2149829 := bbase (se 4 (by rfl) ⟨201546, by rfl⟩ : syracuseStep 2149829 = 403093) (by norm_num)
theorem B1428941 : Blo 952587 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B1428965 : Blo 952587 1428965 := bbase (se 4 (by rfl) ⟨133965, by rfl⟩ : syracuseStep 1428965 = 267931) (by norm_num)
theorem B1428989 : Blo 952587 1428989 := bbase (se 3 (by rfl) ⟨267935, by rfl⟩ : syracuseStep 1428989 = 535871) (by norm_num)
theorem B2149901 : Blo 952587 2149901 := bbase (se 3 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 2149901 = 806213) (by norm_num)
theorem B1429013 : Blo 952587 1429013 := bbase (se 6 (by rfl) ⟨33492, by rfl⟩ : syracuseStep 1429013 = 66985) (by norm_num)
theorem B1429037 : Blo 952587 1429037 := bbase (se 3 (by rfl) ⟨267944, by rfl⟩ : syracuseStep 1429037 = 535889) (by norm_num)
theorem B5164597 : Blo 952587 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B1429061 : Blo 952587 1429061 := bbase (se 4 (by rfl) ⟨133974, by rfl⟩ : syracuseStep 1429061 = 267949) (by norm_num)
theorem B2149973 : Blo 952587 2149973 := bbase (se 8 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 2149973 = 25195) (by norm_num)
theorem B1429085 : Blo 952587 1429085 := bbase (se 3 (by rfl) ⟨267953, by rfl⟩ : syracuseStep 1429085 = 535907) (by norm_num)
theorem B1429109 : Blo 952587 1429109 := bbase (se 5 (by rfl) ⟨66989, by rfl⟩ : syracuseStep 1429109 = 133979) (by norm_num)
theorem B1429133 : Blo 952587 1429133 := bbase (se 3 (by rfl) ⟨267962, by rfl⟩ : syracuseStep 1429133 = 535925) (by norm_num)
theorem B5426837 : Blo 952587 5426837 := bbase (se 6 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 5426837 = 254383) (by norm_num)
theorem B1527445 : Blo 952587 1527445 := bbase (se 6 (by rfl) ⟨35799, by rfl⟩ : syracuseStep 1527445 = 71599) (by norm_num)
theorem B2150045 : Blo 952587 2150045 := bbase (se 3 (by rfl) ⟨403133, by rfl⟩ : syracuseStep 2150045 = 806267) (by norm_num)
theorem B1429157 : Blo 952587 1429157 := bbase (se 4 (by rfl) ⟨133983, by rfl⟩ : syracuseStep 1429157 = 267967) (by norm_num)
theorem B1429181 : Blo 952587 1429181 := bbase (se 3 (by rfl) ⟨267971, by rfl⟩ : syracuseStep 1429181 = 535943) (by norm_num)
theorem B1429205 : Blo 952587 1429205 := bbase (se 7 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 1429205 = 33497) (by norm_num)
theorem B2150117 : Blo 952587 2150117 := bbase (se 4 (by rfl) ⟨201573, by rfl⟩ : syracuseStep 2150117 = 403147) (by norm_num)
theorem B1429229 : Blo 952587 1429229 := bbase (se 3 (by rfl) ⟨267980, by rfl⟩ : syracuseStep 1429229 = 535961) (by norm_num)
theorem B1429253 : Blo 952587 1429253 := bbase (se 4 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 1429253 = 267985) (by norm_num)
theorem B3624709 : Blo 952587 3624709 := bbase (se 4 (by rfl) ⟨339816, by rfl⟩ : syracuseStep 3624709 = 679633) (by norm_num)
theorem B2903813 : Blo 952587 2903813 := bbase (se 4 (by rfl) ⟨272232, by rfl⟩ : syracuseStep 2903813 = 544465) (by norm_num)
theorem B2412301 : Blo 952587 2412301 := bbase (se 3 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 2412301 = 904613) (by norm_num)
theorem B1429277 : Blo 952587 1429277 := bbase (se 3 (by rfl) ⟨267989, by rfl⟩ : syracuseStep 1429277 = 535979) (by norm_num)
theorem B4837157 : Blo 952587 4837157 := bbase (se 4 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 4837157 = 906967) (by norm_num)
theorem B2150189 : Blo 952587 2150189 := bbase (se 3 (by rfl) ⟨403160, by rfl⟩ : syracuseStep 2150189 = 806321) (by norm_num)
theorem B1429301 : Blo 952587 1429301 := bbase (se 5 (by rfl) ⟨66998, by rfl⟩ : syracuseStep 1429301 = 133997) (by norm_num)
theorem B1429325 : Blo 952587 1429325 := bbase (se 3 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 1429325 = 535997) (by norm_num)
theorem B13782869 : Blo 952587 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B1429349 : Blo 952587 1429349 := bbase (se 4 (by rfl) ⟨134001, by rfl⟩ : syracuseStep 1429349 = 268003) (by norm_num)
theorem B2150261 : Blo 952587 2150261 := bbase (se 5 (by rfl) ⟨100793, by rfl⟩ : syracuseStep 2150261 = 201587) (by norm_num)
theorem B1429373 : Blo 952587 1429373 := bbase (se 3 (by rfl) ⟨268007, by rfl⟩ : syracuseStep 1429373 = 536015) (by norm_num)
theorem B2412413 : Blo 952587 2412413 := bbase (se 3 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 2412413 = 904655) (by norm_num)
theorem B1429397 : Blo 952587 1429397 := bbase (se 6 (by rfl) ⟨33501, by rfl⟩ : syracuseStep 1429397 = 67003) (by norm_num)
theorem B1429421 : Blo 952587 1429421 := bbase (se 3 (by rfl) ⟨268016, by rfl⟩ : syracuseStep 1429421 = 536033) (by norm_num)
theorem B2150333 : Blo 952587 2150333 := bbase (se 3 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 2150333 = 806375) (by norm_num)
theorem B1429445 : Blo 952587 1429445 := bbase (se 4 (by rfl) ⟨134010, by rfl⟩ : syracuseStep 1429445 = 268021) (by norm_num)
theorem B1429469 : Blo 952587 1429469 := bbase (se 3 (by rfl) ⟨268025, by rfl⟩ : syracuseStep 1429469 = 536051) (by norm_num)
theorem B1429493 : Blo 952587 1429493 := bbase (se 5 (by rfl) ⟨67007, by rfl⟩ : syracuseStep 1429493 = 134015) (by norm_num)
theorem B2150405 : Blo 952587 2150405 := bbase (se 4 (by rfl) ⟨201600, by rfl⟩ : syracuseStep 2150405 = 403201) (by norm_num)
theorem B1429517 : Blo 952587 1429517 := bbase (se 3 (by rfl) ⟨268034, by rfl⟩ : syracuseStep 1429517 = 536069) (by norm_num)
theorem B1429541 : Blo 952587 1429541 := bbase (se 4 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 1429541 = 268039) (by norm_num)
theorem B3625013 : Blo 952587 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B1429565 : Blo 952587 1429565 := bbase (se 3 (by rfl) ⟨268043, by rfl⟩ : syracuseStep 1429565 = 536087) (by norm_num)
theorem B2412605 : Blo 952587 2412605 := bbase (se 3 (by rfl) ⟨452363, by rfl⟩ : syracuseStep 2412605 = 904727) (by norm_num)
theorem B2150477 : Blo 952587 2150477 := bbase (se 3 (by rfl) ⟨403214, by rfl⟩ : syracuseStep 2150477 = 806429) (by norm_num)
theorem B1429589 : Blo 952587 1429589 := bbase (se 8 (by rfl) ⟨8376, by rfl⟩ : syracuseStep 1429589 = 16753) (by norm_num)
theorem B4083797 : Blo 952587 4083797 := bbase (se 8 (by rfl) ⟨23928, by rfl⟩ : syracuseStep 4083797 = 47857) (by norm_num)
theorem B1429613 : Blo 952587 1429613 := bbase (se 3 (by rfl) ⟨268052, by rfl⟩ : syracuseStep 1429613 = 536105) (by norm_num)
theorem B6115445 : Blo 952587 6115445 := bbase (se 5 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 6115445 = 573323) (by norm_num)
theorem B1429637 : Blo 952587 1429637 := bbase (se 4 (by rfl) ⟨134028, by rfl⟩ : syracuseStep 1429637 = 268057) (by norm_num)
theorem B3100805 : Blo 952587 3100805 := bbase (se 4 (by rfl) ⟨290700, by rfl⟩ : syracuseStep 3100805 = 581401) (by norm_num)
theorem B1101961 : Blo 952587 1101961 := bbase (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) (by norm_num)
theorem B2150549 : Blo 952587 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B1429661 : Blo 952587 1429661 := bbase (se 3 (by rfl) ⟨268061, by rfl⟩ : syracuseStep 1429661 = 536123) (by norm_num)
theorem B2576549 : Blo 952587 2576549 := bbase (se 4 (by rfl) ⟨241551, by rfl⟩ : syracuseStep 2576549 = 483103) (by norm_num)
theorem B1429685 : Blo 952587 1429685 := bbase (se 5 (by rfl) ⟨67016, by rfl⟩ : syracuseStep 1429685 = 134033) (by norm_num)
theorem B1429709 : Blo 952587 1429709 := bbase (se 3 (by rfl) ⟨268070, by rfl⟩ : syracuseStep 1429709 = 536141) (by norm_num)
theorem B14110933 : Blo 952587 14110933 := bbase (se 7 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 14110933 = 330725) (by norm_num)
theorem B2150621 : Blo 952587 2150621 := bbase (se 3 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 2150621 = 806483) (by norm_num)
theorem B1429733 : Blo 952587 1429733 := bbase (se 4 (by rfl) ⟨134037, by rfl⟩ : syracuseStep 1429733 = 268075) (by norm_num)
theorem B1429757 : Blo 952587 1429757 := bbase (se 3 (by rfl) ⟨268079, by rfl⟩ : syracuseStep 1429757 = 536159) (by norm_num)
theorem B1429781 : Blo 952587 1429781 := bbase (se 6 (by rfl) ⟨33510, by rfl⟩ : syracuseStep 1429781 = 67021) (by norm_num)
theorem B2150693 : Blo 952587 2150693 := bbase (se 4 (by rfl) ⟨201627, by rfl⟩ : syracuseStep 2150693 = 403255) (by norm_num)
theorem B1429805 : Blo 952587 1429805 := bbase (se 3 (by rfl) ⟨268088, by rfl⟩ : syracuseStep 1429805 = 536177) (by norm_num)
theorem B1429829 : Blo 952587 1429829 := bbase (se 4 (by rfl) ⟨134046, by rfl⟩ : syracuseStep 1429829 = 268093) (by norm_num)
theorem B1429853 : Blo 952587 1429853 := bbase (se 3 (by rfl) ⟨268097, by rfl⟩ : syracuseStep 1429853 = 536195) (by norm_num)
theorem B2150765 : Blo 952587 2150765 := bbase (se 3 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 2150765 = 806537) (by norm_num)
theorem B1429877 : Blo 952587 1429877 := bbase (se 5 (by rfl) ⟨67025, by rfl⟩ : syracuseStep 1429877 = 134051) (by norm_num)
theorem B1429901 : Blo 952587 1429901 := bbase (se 3 (by rfl) ⟨268106, by rfl⟩ : syracuseStep 1429901 = 536213) (by norm_num)
theorem B2412949 : Blo 952587 2412949 := bbase (se 6 (by rfl) ⟨56553, by rfl⟩ : syracuseStep 2412949 = 113107) (by norm_num)
theorem B1429925 : Blo 952587 1429925 := bbase (se 4 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 1429925 = 268111) (by norm_num)
theorem B2150837 : Blo 952587 2150837 := bbase (se 5 (by rfl) ⟨100820, by rfl⟩ : syracuseStep 2150837 = 201641) (by norm_num)
theorem B1429949 : Blo 952587 1429949 := bbase (se 3 (by rfl) ⟨268115, by rfl⟩ : syracuseStep 1429949 = 536231) (by norm_num)
theorem B1429973 : Blo 952587 1429973 := bbase (se 7 (by rfl) ⟨16757, by rfl⟩ : syracuseStep 1429973 = 33515) (by norm_num)
theorem B1429997 : Blo 952587 1429997 := bbase (se 3 (by rfl) ⟨268124, by rfl⟩ : syracuseStep 1429997 = 536249) (by norm_num)
theorem B2150909 : Blo 952587 2150909 := bbase (se 3 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 2150909 = 806591) (by norm_num)
theorem B2413061 : Blo 952587 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B1430021 : Blo 952587 1430021 := bbase (se 4 (by rfl) ⟨134064, by rfl⟩ : syracuseStep 1430021 = 268129) (by norm_num)
theorem B1430045 : Blo 952587 1430045 := bbase (se 3 (by rfl) ⟨268133, by rfl⟩ : syracuseStep 1430045 = 536267) (by norm_num)
theorem B1430069 : Blo 952587 1430069 := bbase (se 5 (by rfl) ⟨67034, by rfl⟩ : syracuseStep 1430069 = 134069) (by norm_num)
theorem B2150981 : Blo 952587 2150981 := bbase (se 4 (by rfl) ⟨201654, by rfl⟩ : syracuseStep 2150981 = 403309) (by norm_num)
theorem B1430093 : Blo 952587 1430093 := bbase (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) (by norm_num)
theorem B24498773 : Blo 952587 24498773 := bbase (se 8 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 24498773 = 287095) (by norm_num)
theorem B1430117 : Blo 952587 1430117 := bbase (se 4 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 1430117 = 268147) (by norm_num)
theorem B1430141 : Blo 952587 1430141 := bbase (se 3 (by rfl) ⟨268151, by rfl⟩ : syracuseStep 1430141 = 536303) (by norm_num)
theorem B2151053 : Blo 952587 2151053 := bbase (se 3 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 2151053 = 806645) (by norm_num)
theorem B1430165 : Blo 952587 1430165 := bbase (se 6 (by rfl) ⟨33519, by rfl⟩ : syracuseStep 1430165 = 67039) (by norm_num)
theorem B1430189 : Blo 952587 1430189 := bbase (se 3 (by rfl) ⟨268160, by rfl⟩ : syracuseStep 1430189 = 536321) (by norm_num)
theorem B2413253 : Blo 952587 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B1430213 : Blo 952587 1430213 := bbase (se 4 (by rfl) ⟨134082, by rfl⟩ : syracuseStep 1430213 = 268165) (by norm_num)
theorem B2151125 : Blo 952587 2151125 := bbase (se 7 (by rfl) ⟨25208, by rfl⟩ : syracuseStep 2151125 = 50417) (by norm_num)
theorem B1430237 : Blo 952587 1430237 := bbase (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) (by norm_num)
theorem B1430261 : Blo 952587 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B1528573 : Blo 952587 1528573 := bbase (se 3 (by rfl) ⟨286607, by rfl⟩ : syracuseStep 1528573 = 573215) (by norm_num)
theorem B1430285 : Blo 952587 1430285 := bbase (se 3 (by rfl) ⟨268178, by rfl⟩ : syracuseStep 1430285 = 536357) (by norm_num)
theorem B2151197 : Blo 952587 2151197 := bbase (se 3 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 2151197 = 806699) (by norm_num)
theorem B1430309 : Blo 952587 1430309 := bbase (se 4 (by rfl) ⟨134091, by rfl⟩ : syracuseStep 1430309 = 268183) (by norm_num)
theorem B1430333 : Blo 952587 1430333 := bbase (se 3 (by rfl) ⟨268187, by rfl⟩ : syracuseStep 1430333 = 536375) (by norm_num)
theorem B1430357 : Blo 952587 1430357 := bbase (se 9 (by rfl) ⟨4190, by rfl⟩ : syracuseStep 1430357 = 8381) (by norm_num)
theorem B2151269 : Blo 952587 2151269 := bbase (se 4 (by rfl) ⟨201681, by rfl⟩ : syracuseStep 2151269 = 403363) (by norm_num)
theorem B1430381 : Blo 952587 1430381 := bbase (se 3 (by rfl) ⟨268196, by rfl⟩ : syracuseStep 1430381 = 536393) (by norm_num)
theorem B1430405 : Blo 952587 1430405 := bbase (se 4 (by rfl) ⟨134100, by rfl⟩ : syracuseStep 1430405 = 268201) (by norm_num)
theorem B1430429 : Blo 952587 1430429 := bbase (se 3 (by rfl) ⟨268205, by rfl⟩ : syracuseStep 1430429 = 536411) (by norm_num)
theorem B2151341 : Blo 952587 2151341 := bbase (se 3 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 2151341 = 806753) (by norm_num)
theorem B1430453 : Blo 952587 1430453 := bbase (se 5 (by rfl) ⟨67052, by rfl⟩ : syracuseStep 1430453 = 134105) (by norm_num)
theorem B1430477 : Blo 952587 1430477 := bbase (se 3 (by rfl) ⟨268214, by rfl⟩ : syracuseStep 1430477 = 536429) (by norm_num)
theorem B1430501 : Blo 952587 1430501 := bbase (se 4 (by rfl) ⟨134109, by rfl⟩ : syracuseStep 1430501 = 268219) (by norm_num)
theorem B2151413 : Blo 952587 2151413 := bbase (se 5 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 2151413 = 201695) (by norm_num)
theorem B1430525 : Blo 952587 1430525 := bbase (se 3 (by rfl) ⟨268223, by rfl⟩ : syracuseStep 1430525 = 536447) (by norm_num)
theorem B1430549 : Blo 952587 1430549 := bbase (se 6 (by rfl) ⟨33528, by rfl⟩ : syracuseStep 1430549 = 67057) (by norm_num)
theorem B2413597 : Blo 952587 2413597 := bbase (se 3 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 2413597 = 905099) (by norm_num)
theorem B1430573 : Blo 952587 1430573 := bbase (se 3 (by rfl) ⟨268232, by rfl⟩ : syracuseStep 1430573 = 536465) (by norm_num)
theorem B4838453 : Blo 952587 4838453 := bbase (se 5 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 4838453 = 453605) (by norm_num)
theorem B2151485 : Blo 952587 2151485 := bbase (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) (by norm_num)
theorem B1430597 : Blo 952587 1430597 := bbase (se 4 (by rfl) ⟨134118, by rfl⟩ : syracuseStep 1430597 = 268237) (by norm_num)
theorem B1430621 : Blo 952587 1430621 := bbase (se 3 (by rfl) ⟨268241, by rfl⟩ : syracuseStep 1430621 = 536483) (by norm_num)
theorem B1430645 : Blo 952587 1430645 := bbase (se 5 (by rfl) ⟨67061, by rfl⟩ : syracuseStep 1430645 = 134123) (by norm_num)
theorem B2151557 : Blo 952587 2151557 := bbase (se 4 (by rfl) ⟨201708, by rfl⟩ : syracuseStep 2151557 = 403417) (by norm_num)
theorem B2413709 : Blo 952587 2413709 := bbase (se 3 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 2413709 = 905141) (by norm_num)
theorem B1430669 : Blo 952587 1430669 := bbase (se 3 (by rfl) ⟨268250, by rfl⟩ : syracuseStep 1430669 = 536501) (by norm_num)
theorem B1430693 : Blo 952587 1430693 := bbase (se 4 (by rfl) ⟨134127, by rfl⟩ : syracuseStep 1430693 = 268255) (by norm_num)
theorem B1430717 : Blo 952587 1430717 := bbase (se 3 (by rfl) ⟨268259, by rfl⟩ : syracuseStep 1430717 = 536519) (by norm_num)
theorem B1529021 : Blo 952587 1529021 := bbase (se 3 (by rfl) ⟨286691, by rfl⟩ : syracuseStep 1529021 = 573383) (by norm_num)
theorem B2151629 : Blo 952587 2151629 := bbase (se 3 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 2151629 = 806861) (by norm_num)
theorem B1430741 : Blo 952587 1430741 := bbase (se 7 (by rfl) ⟨16766, by rfl⟩ : syracuseStep 1430741 = 33533) (by norm_num)
theorem B4412645 : Blo 952587 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B1430765 : Blo 952587 1430765 := bbase (se 3 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 1430765 = 536537) (by norm_num)
theorem B1430789 : Blo 952587 1430789 := bbase (se 4 (by rfl) ⟨134136, by rfl⟩ : syracuseStep 1430789 = 268273) (by norm_num)
theorem B2446613 : Blo 952587 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B2151701 : Blo 952587 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B1430813 : Blo 952587 1430813 := bbase (se 3 (by rfl) ⟨268277, by rfl⟩ : syracuseStep 1430813 = 536555) (by norm_num)
theorem B1430837 : Blo 952587 1430837 := bbase (se 5 (by rfl) ⟨67070, by rfl⟩ : syracuseStep 1430837 = 134141) (by norm_num)
theorem B2413901 : Blo 952587 2413901 := bbase (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) (by norm_num)
theorem B1430861 : Blo 952587 1430861 := bbase (se 3 (by rfl) ⟨268286, by rfl⟩ : syracuseStep 1430861 = 536573) (by norm_num)
theorem B11621717 : Blo 952587 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B2151773 : Blo 952587 2151773 := bbase (se 3 (by rfl) ⟨403457, by rfl⟩ : syracuseStep 2151773 = 806915) (by norm_num)
theorem B1430885 : Blo 952587 1430885 := bbase (se 4 (by rfl) ⟨134145, by rfl⟩ : syracuseStep 1430885 = 268291) (by norm_num)
theorem B1430909 : Blo 952587 1430909 := bbase (se 3 (by rfl) ⟨268295, by rfl⟩ : syracuseStep 1430909 = 536591) (by norm_num)
theorem B2446733 : Blo 952587 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B1430933 : Blo 952587 1430933 := bbase (se 6 (by rfl) ⟨33537, by rfl⟩ : syracuseStep 1430933 = 67075) (by norm_num)
theorem B2151845 : Blo 952587 2151845 := bbase (se 4 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 2151845 = 403471) (by norm_num)
theorem B1430957 : Blo 952587 1430957 := bbase (se 3 (by rfl) ⟨268304, by rfl⟩ : syracuseStep 1430957 = 536609) (by norm_num)
theorem B1430981 : Blo 952587 1430981 := bbase (se 4 (by rfl) ⟨134154, by rfl⟩ : syracuseStep 1430981 = 268309) (by norm_num)
theorem B1431005 : Blo 952587 1431005 := bbase (se 3 (by rfl) ⟨268313, by rfl⟩ : syracuseStep 1431005 = 536627) (by norm_num)
theorem B2151917 : Blo 952587 2151917 := bbase (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) (by norm_num)
theorem B1431029 : Blo 952587 1431029 := bbase (se 5 (by rfl) ⟨67079, by rfl⟩ : syracuseStep 1431029 = 134159) (by norm_num)
theorem B1431053 : Blo 952587 1431053 := bbase (se 3 (by rfl) ⟨268322, by rfl⟩ : syracuseStep 1431053 = 536645) (by norm_num)
theorem B1431077 : Blo 952587 1431077 := bbase (se 4 (by rfl) ⟨134163, by rfl⟩ : syracuseStep 1431077 = 268327) (by norm_num)
theorem B2151989 : Blo 952587 2151989 := bbase (se 5 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 2151989 = 201749) (by norm_num)
theorem B1431101 : Blo 952587 1431101 := bbase (se 3 (by rfl) ⟨268331, by rfl⟩ : syracuseStep 1431101 = 536663) (by norm_num)
theorem B1431125 : Blo 952587 1431125 := bbase (se 8 (by rfl) ⟨8385, by rfl⟩ : syracuseStep 1431125 = 16771) (by norm_num)
theorem B1431149 : Blo 952587 1431149 := bbase (se 3 (by rfl) ⟨268340, by rfl⟩ : syracuseStep 1431149 = 536681) (by norm_num)
theorem B2152061 : Blo 952587 2152061 := bbase (se 3 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 2152061 = 807023) (by norm_num)
theorem B1431173 : Blo 952587 1431173 := bbase (se 4 (by rfl) ⟨134172, by rfl⟩ : syracuseStep 1431173 = 268345) (by norm_num)
theorem B4347541 : Blo 952587 4347541 := bbase (se 6 (by rfl) ⟨101895, by rfl⟩ : syracuseStep 4347541 = 203791) (by norm_num)
theorem B1431197 : Blo 952587 1431197 := bbase (se 3 (by rfl) ⟨268349, by rfl⟩ : syracuseStep 1431197 = 536699) (by norm_num)
theorem B2414245 : Blo 952587 2414245 := bbase (se 4 (by rfl) ⟨226335, by rfl⟩ : syracuseStep 2414245 = 452671) (by norm_num)
theorem B1431221 : Blo 952587 1431221 := bbase (se 5 (by rfl) ⟨67088, by rfl⟩ : syracuseStep 1431221 = 134177) (by norm_num)
theorem B2152133 : Blo 952587 2152133 := bbase (se 4 (by rfl) ⟨201762, by rfl⟩ : syracuseStep 2152133 = 403525) (by norm_num)
theorem B1431245 : Blo 952587 1431245 := bbase (se 3 (by rfl) ⟨268358, by rfl⟩ : syracuseStep 1431245 = 536717) (by norm_num)
theorem B1431269 : Blo 952587 1431269 := bbase (se 4 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 1431269 = 268363) (by norm_num)
theorem B1431293 : Blo 952587 1431293 := bbase (se 3 (by rfl) ⟨268367, by rfl⟩ : syracuseStep 1431293 = 536735) (by norm_num)
theorem B2152205 : Blo 952587 2152205 := bbase (se 3 (by rfl) ⟨403538, by rfl⟩ : syracuseStep 2152205 = 807077) (by norm_num)
theorem B2414357 : Blo 952587 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B1431317 : Blo 952587 1431317 := bbase (se 6 (by rfl) ⟨33546, by rfl⟩ : syracuseStep 1431317 = 67093) (by norm_num)
theorem B1431341 : Blo 952587 1431341 := bbase (se 3 (by rfl) ⟨268376, by rfl⟩ : syracuseStep 1431341 = 536753) (by norm_num)
theorem B5429045 : Blo 952587 5429045 := bbase (se 5 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 5429045 = 508973) (by norm_num)
theorem B1431365 : Blo 952587 1431365 := bbase (se 4 (by rfl) ⟨134190, by rfl⟩ : syracuseStep 1431365 = 268381) (by norm_num)
theorem B2152277 : Blo 952587 2152277 := bbase (se 9 (by rfl) ⟨6305, by rfl⟩ : syracuseStep 2152277 = 12611) (by norm_num)
theorem B1431389 : Blo 952587 1431389 := bbase (se 3 (by rfl) ⟨268385, by rfl⟩ : syracuseStep 1431389 = 536771) (by norm_num)
theorem B2578277 : Blo 952587 2578277 := bbase (se 4 (by rfl) ⟨241713, by rfl⟩ : syracuseStep 2578277 = 483427) (by norm_num)
theorem B1431413 : Blo 952587 1431413 := bbase (se 5 (by rfl) ⟨67097, by rfl⟩ : syracuseStep 1431413 = 134195) (by norm_num)
theorem B1431437 : Blo 952587 1431437 := bbase (se 3 (by rfl) ⟨268394, by rfl⟩ : syracuseStep 1431437 = 536789) (by norm_num)
theorem B1431461 : Blo 952587 1431461 := bbase (se 4 (by rfl) ⟨134199, by rfl⟩ : syracuseStep 1431461 = 268399) (by norm_num)
theorem B1431485 : Blo 952587 1431485 := bbase (se 3 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 1431485 = 536807) (by norm_num)
theorem B10311637 : Blo 952587 10311637 := bbase (se 7 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 10311637 = 241679) (by norm_num)
theorem B2414549 : Blo 952587 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B1431509 : Blo 952587 1431509 := bbase (se 7 (by rfl) ⟨16775, by rfl⟩ : syracuseStep 1431509 = 33551) (by norm_num)
theorem B1431533 : Blo 952587 1431533 := bbase (se 3 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 1431533 = 536825) (by norm_num)
theorem B1431557 : Blo 952587 1431557 := bbase (se 4 (by rfl) ⟨134208, by rfl⟩ : syracuseStep 1431557 = 268417) (by norm_num)
theorem B1431581 : Blo 952587 1431581 := bbase (se 3 (by rfl) ⟨268421, by rfl⟩ : syracuseStep 1431581 = 536843) (by norm_num)
theorem B1431605 : Blo 952587 1431605 := bbase (se 5 (by rfl) ⟨67106, by rfl⟩ : syracuseStep 1431605 = 134213) (by norm_num)
theorem B1431629 : Blo 952587 1431629 := bbase (se 3 (by rfl) ⟨268430, by rfl⟩ : syracuseStep 1431629 = 536861) (by norm_num)
theorem B1431653 : Blo 952587 1431653 := bbase (se 4 (by rfl) ⟨134217, by rfl⟩ : syracuseStep 1431653 = 268435) (by norm_num)
theorem B3627125 : Blo 952587 3627125 := bbase (se 5 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 3627125 = 340043) (by norm_num)
theorem B1431677 : Blo 952587 1431677 := bbase (se 3 (by rfl) ⟨268439, by rfl⟩ : syracuseStep 1431677 = 536879) (by norm_num)
theorem B1431701 : Blo 952587 1431701 := bbase (se 6 (by rfl) ⟨33555, by rfl⟩ : syracuseStep 1431701 = 67111) (by norm_num)
theorem B1431725 : Blo 952587 1431725 := bbase (se 3 (by rfl) ⟨268448, by rfl⟩ : syracuseStep 1431725 = 536897) (by norm_num)
theorem B1431749 : Blo 952587 1431749 := bbase (se 4 (by rfl) ⟨134226, by rfl⟩ : syracuseStep 1431749 = 268453) (by norm_num)
theorem B24762581 : Blo 952587 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B1431773 : Blo 952587 1431773 := bbase (se 3 (by rfl) ⟨268457, by rfl⟩ : syracuseStep 1431773 = 536915) (by norm_num)
theorem B1431797 : Blo 952587 1431797 := bbase (se 5 (by rfl) ⟨67115, by rfl⟩ : syracuseStep 1431797 = 134231) (by norm_num)
theorem B1431821 : Blo 952587 1431821 := bbase (se 3 (by rfl) ⟨268466, by rfl⟩ : syracuseStep 1431821 = 536933) (by norm_num)
theorem B1431845 : Blo 952587 1431845 := bbase (se 4 (by rfl) ⟨134235, by rfl⟩ : syracuseStep 1431845 = 268471) (by norm_num)
theorem B2414893 : Blo 952587 2414893 := bbase (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) (by norm_num)
theorem B1431869 : Blo 952587 1431869 := bbase (se 3 (by rfl) ⟨268475, by rfl⟩ : syracuseStep 1431869 = 536951) (by norm_num)
theorem B4839749 : Blo 952587 4839749 := bbase (se 4 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 4839749 = 907453) (by norm_num)
theorem B18340181 : Blo 952587 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B1431893 : Blo 952587 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1431917 : Blo 952587 1431917 := bbase (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) (by norm_num)
theorem B1431941 : Blo 952587 1431941 := bbase (se 4 (by rfl) ⟨134244, by rfl⟩ : syracuseStep 1431941 = 268489) (by norm_num)
theorem B3627413 : Blo 952587 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B2415005 : Blo 952587 2415005 := bbase (se 3 (by rfl) ⟨452813, by rfl⟩ : syracuseStep 2415005 = 905627) (by norm_num)
theorem B1431965 : Blo 952587 1431965 := bbase (se 3 (by rfl) ⟨268493, by rfl⟩ : syracuseStep 1431965 = 536987) (by norm_num)
theorem B1431989 : Blo 952587 1431989 := bbase (se 5 (by rfl) ⟨67124, by rfl⟩ : syracuseStep 1431989 = 134249) (by norm_num)
theorem B1432013 : Blo 952587 1432013 := bbase (se 3 (by rfl) ⟨268502, by rfl⟩ : syracuseStep 1432013 = 537005) (by norm_num)
theorem B1432037 : Blo 952587 1432037 := bbase (se 4 (by rfl) ⟨134253, by rfl⟩ : syracuseStep 1432037 = 268507) (by norm_num)
theorem B1432061 : Blo 952587 1432061 := bbase (se 3 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 1432061 = 537023) (by norm_num)
theorem B2578949 : Blo 952587 2578949 := bbase (se 4 (by rfl) ⟨241776, by rfl⟩ : syracuseStep 2578949 = 483553) (by norm_num)
theorem B1432085 : Blo 952587 1432085 := bbase (se 6 (by rfl) ⟨33564, by rfl⟩ : syracuseStep 1432085 = 67129) (by norm_num)
theorem B1071661 : Blo 952587 1071661 := bbase (se 3 (by rfl) ⟨200936, by rfl⟩ : syracuseStep 1071661 = 401873) (by norm_num)
theorem B1432109 : Blo 952587 1432109 := bbase (se 3 (by rfl) ⟨268520, by rfl⟩ : syracuseStep 1432109 = 537041) (by norm_num)
theorem B1432133 : Blo 952587 1432133 := bbase (se 4 (by rfl) ⟨134262, by rfl⟩ : syracuseStep 1432133 = 268525) (by norm_num)
theorem B1071697 : Blo 952587 1071697 := bbase (se 2 (by rfl) ⟨401886, by rfl⟩ : syracuseStep 1071697 = 803773) (by norm_num)
theorem B2415197 : Blo 952587 2415197 := bbase (se 3 (by rfl) ⟨452849, by rfl⟩ : syracuseStep 2415197 = 905699) (by norm_num)
theorem B1432157 : Blo 952587 1432157 := bbase (se 3 (by rfl) ⟨268529, by rfl⟩ : syracuseStep 1432157 = 537059) (by norm_num)
theorem B1071733 : Blo 952587 1071733 := bbase (se 5 (by rfl) ⟨50237, by rfl⟩ : syracuseStep 1071733 = 100475) (by norm_num)
theorem B1432181 : Blo 952587 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B1432205 : Blo 952587 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1071769 : Blo 952587 1071769 := bbase (se 2 (by rfl) ⟨401913, by rfl⟩ : syracuseStep 1071769 = 803827) (by norm_num)
theorem B1530533 : Blo 952587 1530533 := bbase (se 4 (by rfl) ⟨143487, by rfl⟩ : syracuseStep 1530533 = 286975) (by norm_num)
theorem B1432229 : Blo 952587 1432229 := bbase (se 4 (by rfl) ⟨134271, by rfl⟩ : syracuseStep 1432229 = 268543) (by norm_num)
theorem B7756469 : Blo 952587 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B1071805 : Blo 952587 1071805 := bbase (se 3 (by rfl) ⟨200963, by rfl⟩ : syracuseStep 1071805 = 401927) (by norm_num)
theorem B1432253 : Blo 952587 1432253 := bbase (se 3 (by rfl) ⟨268547, by rfl⟩ : syracuseStep 1432253 = 537095) (by norm_num)
theorem B1432277 : Blo 952587 1432277 := bbase (se 7 (by rfl) ⟨16784, by rfl⟩ : syracuseStep 1432277 = 33569) (by norm_num)
theorem B1071841 : Blo 952587 1071841 := bbase (se 2 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 1071841 = 803881) (by norm_num)
theorem B1432301 : Blo 952587 1432301 := bbase (se 3 (by rfl) ⟨268556, by rfl⟩ : syracuseStep 1432301 = 537113) (by norm_num)
theorem B1071877 : Blo 952587 1071877 := bbase (se 4 (by rfl) ⟨100488, by rfl⟩ : syracuseStep 1071877 = 200977) (by norm_num)
theorem B1432325 : Blo 952587 1432325 := bbase (se 4 (by rfl) ⟨134280, by rfl⟩ : syracuseStep 1432325 = 268561) (by norm_num)
theorem B1432349 : Blo 952587 1432349 := bbase (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) (by norm_num)
theorem B1530661 : Blo 952587 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B1071913 : Blo 952587 1071913 := bbase (se 2 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 1071913 = 803935) (by norm_num)
theorem B1432373 : Blo 952587 1432373 := bbase (se 5 (by rfl) ⟨67142, by rfl⟩ : syracuseStep 1432373 = 134285) (by norm_num)
theorem B1071949 : Blo 952587 1071949 := bbase (se 3 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 1071949 = 401981) (by norm_num)
theorem B1432397 : Blo 952587 1432397 := bbase (se 3 (by rfl) ⟨268574, by rfl⟩ : syracuseStep 1432397 = 537149) (by norm_num)
theorem B1104725 : Blo 952587 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B1432421 : Blo 952587 1432421 := bbase (se 4 (by rfl) ⟨134289, by rfl⟩ : syracuseStep 1432421 = 268579) (by norm_num)
theorem B1071985 : Blo 952587 1071985 := bbase (se 2 (by rfl) ⟨401994, by rfl⟩ : syracuseStep 1071985 = 803989) (by norm_num)
theorem B1432445 : Blo 952587 1432445 := bbase (se 3 (by rfl) ⟨268583, by rfl⟩ : syracuseStep 1432445 = 537167) (by norm_num)
theorem B1072021 : Blo 952587 1072021 := bbase (se 6 (by rfl) ⟨25125, by rfl⟩ : syracuseStep 1072021 = 50251) (by norm_num)
theorem B1432469 : Blo 952587 1432469 := bbase (se 6 (by rfl) ⟨33573, by rfl⟩ : syracuseStep 1432469 = 67147) (by norm_num)
theorem B1432493 : Blo 952587 1432493 := bbase (se 3 (by rfl) ⟨268592, by rfl⟩ : syracuseStep 1432493 = 537185) (by norm_num)
theorem B2415541 : Blo 952587 2415541 := bbase (se 5 (by rfl) ⟨113228, by rfl⟩ : syracuseStep 2415541 = 226457) (by norm_num)
theorem B1072057 : Blo 952587 1072057 := bbase (se 2 (by rfl) ⟨402021, by rfl⟩ : syracuseStep 1072057 = 804043) (by norm_num)
theorem B1432517 : Blo 952587 1432517 := bbase (se 4 (by rfl) ⟨134298, by rfl⟩ : syracuseStep 1432517 = 268597) (by norm_num)
theorem B1072093 : Blo 952587 1072093 := bbase (se 3 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 1072093 = 402035) (by norm_num)
theorem B1432541 : Blo 952587 1432541 := bbase (se 3 (by rfl) ⟨268601, by rfl⟩ : syracuseStep 1432541 = 537203) (by norm_num)
theorem B1432565 : Blo 952587 1432565 := bbase (se 5 (by rfl) ⟨67151, by rfl⟩ : syracuseStep 1432565 = 134303) (by norm_num)
theorem B1072129 : Blo 952587 1072129 := bbase (se 2 (by rfl) ⟨402048, by rfl⟩ : syracuseStep 1072129 = 804097) (by norm_num)
theorem B1432589 : Blo 952587 1432589 := bbase (se 3 (by rfl) ⟨268610, by rfl⟩ : syracuseStep 1432589 = 537221) (by norm_num)
theorem B1072165 : Blo 952587 1072165 := bbase (se 4 (by rfl) ⟨100515, by rfl⟩ : syracuseStep 1072165 = 201031) (by norm_num)
theorem B2415653 : Blo 952587 2415653 := bbase (se 4 (by rfl) ⟨226467, by rfl⟩ : syracuseStep 2415653 = 452935) (by norm_num)
theorem B1432613 : Blo 952587 1432613 := bbase (se 4 (by rfl) ⟨134307, by rfl⟩ : syracuseStep 1432613 = 268615) (by norm_num)
theorem B1432637 : Blo 952587 1432637 := bbase (se 3 (by rfl) ⟨268619, by rfl⟩ : syracuseStep 1432637 = 537239) (by norm_num)
theorem B1072201 : Blo 952587 1072201 := bbase (se 2 (by rfl) ⟨402075, by rfl⟩ : syracuseStep 1072201 = 804151) (by norm_num)
theorem B1432661 : Blo 952587 1432661 := bbase (se 8 (by rfl) ⟨8394, by rfl⟩ : syracuseStep 1432661 = 16789) (by norm_num)
theorem B1072237 : Blo 952587 1072237 := bbase (se 3 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 1072237 = 402089) (by norm_num)
theorem B1432685 : Blo 952587 1432685 := bbase (se 3 (by rfl) ⟨268628, by rfl⟩ : syracuseStep 1432685 = 537257) (by norm_num)
theorem B1432709 : Blo 952587 1432709 := bbase (se 4 (by rfl) ⟨134316, by rfl⟩ : syracuseStep 1432709 = 268633) (by norm_num)
theorem B1072273 : Blo 952587 1072273 := bbase (se 2 (by rfl) ⟨402102, by rfl⟩ : syracuseStep 1072273 = 804205) (by norm_num)
theorem B1432733 : Blo 952587 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B1072309 : Blo 952587 1072309 := bbase (se 5 (by rfl) ⟨50264, by rfl⟩ : syracuseStep 1072309 = 100529) (by norm_num)
theorem B1432757 : Blo 952587 1432757 := bbase (se 5 (by rfl) ⟨67160, by rfl⟩ : syracuseStep 1432757 = 134321) (by norm_num)
theorem B1432781 : Blo 952587 1432781 := bbase (se 3 (by rfl) ⟨268646, by rfl⟩ : syracuseStep 1432781 = 537293) (by norm_num)
theorem B1072345 : Blo 952587 1072345 := bbase (se 2 (by rfl) ⟨402129, by rfl⟩ : syracuseStep 1072345 = 804259) (by norm_num)
theorem B2415845 : Blo 952587 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B1432805 : Blo 952587 1432805 := bbase (se 4 (by rfl) ⟨134325, by rfl⟩ : syracuseStep 1432805 = 268651) (by norm_num)
theorem B1072381 : Blo 952587 1072381 := bbase (se 3 (by rfl) ⟨201071, by rfl⟩ : syracuseStep 1072381 = 402143) (by norm_num)
theorem B1432829 : Blo 952587 1432829 := bbase (se 3 (by rfl) ⟨268655, by rfl⟩ : syracuseStep 1432829 = 537311) (by norm_num)
theorem B1432853 : Blo 952587 1432853 := bbase (se 6 (by rfl) ⟨33582, by rfl⟩ : syracuseStep 1432853 = 67165) (by norm_num)
theorem B1072417 : Blo 952587 1072417 := bbase (se 2 (by rfl) ⟨402156, by rfl⟩ : syracuseStep 1072417 = 804313) (by norm_num)
theorem B1432877 : Blo 952587 1432877 := bbase (se 3 (by rfl) ⟨268664, by rfl⟩ : syracuseStep 1432877 = 537329) (by norm_num)
theorem B1072453 : Blo 952587 1072453 := bbase (se 4 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 1072453 = 201085) (by norm_num)
theorem B1432901 : Blo 952587 1432901 := bbase (se 4 (by rfl) ⟨134334, by rfl⟩ : syracuseStep 1432901 = 268669) (by norm_num)
theorem B1432925 : Blo 952587 1432925 := bbase (se 3 (by rfl) ⟨268673, by rfl⟩ : syracuseStep 1432925 = 537347) (by norm_num)
theorem B1072489 : Blo 952587 1072489 := bbase (se 2 (by rfl) ⟨402183, by rfl⟩ : syracuseStep 1072489 = 804367) (by norm_num)
theorem B1432949 : Blo 952587 1432949 := bbase (se 5 (by rfl) ⟨67169, by rfl⟩ : syracuseStep 1432949 = 134339) (by norm_num)
theorem B1072525 : Blo 952587 1072525 := bbase (se 3 (by rfl) ⟨201098, by rfl⟩ : syracuseStep 1072525 = 402197) (by norm_num)
theorem B1432973 : Blo 952587 1432973 := bbase (se 3 (by rfl) ⟨268682, by rfl⟩ : syracuseStep 1432973 = 537365) (by norm_num)
theorem B1432997 : Blo 952587 1432997 := bbase (se 4 (by rfl) ⟨134343, by rfl⟩ : syracuseStep 1432997 = 268687) (by norm_num)
theorem B1072561 : Blo 952587 1072561 := bbase (se 2 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 1072561 = 804421) (by norm_num)
theorem B1433021 : Blo 952587 1433021 := bbase (se 3 (by rfl) ⟨268691, by rfl⟩ : syracuseStep 1433021 = 537383) (by norm_num)
theorem B1072597 : Blo 952587 1072597 := bbase (se 7 (by rfl) ⟨12569, by rfl⟩ : syracuseStep 1072597 = 25139) (by norm_num)
theorem B1433045 : Blo 952587 1433045 := bbase (se 7 (by rfl) ⟨16793, by rfl⟩ : syracuseStep 1433045 = 33587) (by norm_num)
theorem B1433069 : Blo 952587 1433069 := bbase (se 3 (by rfl) ⟨268700, by rfl⟩ : syracuseStep 1433069 = 537401) (by norm_num)
theorem B1072633 : Blo 952587 1072633 := bbase (se 2 (by rfl) ⟨402237, by rfl⟩ : syracuseStep 1072633 = 804475) (by norm_num)
theorem B1433093 : Blo 952587 1433093 := bbase (se 4 (by rfl) ⟨134352, by rfl⟩ : syracuseStep 1433093 = 268705) (by norm_num)
theorem B1105429 : Blo 952587 1105429 := bbase (se 6 (by rfl) ⟨25908, by rfl⟩ : syracuseStep 1105429 = 51817) (by norm_num)
theorem B1072669 : Blo 952587 1072669 := bbase (se 3 (by rfl) ⟨201125, by rfl⟩ : syracuseStep 1072669 = 402251) (by norm_num)
theorem B1433117 : Blo 952587 1433117 := bbase (se 3 (by rfl) ⟨268709, by rfl⟩ : syracuseStep 1433117 = 537419) (by norm_num)
theorem B1629733 : Blo 952587 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B1433141 : Blo 952587 1433141 := bbase (se 5 (by rfl) ⟨67178, by rfl⟩ : syracuseStep 1433141 = 134357) (by norm_num)
theorem B3628597 : Blo 952587 3628597 := bbase (se 5 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 3628597 = 340181) (by norm_num)
theorem B2416189 : Blo 952587 2416189 := bbase (se 3 (by rfl) ⟨453035, by rfl⟩ : syracuseStep 2416189 = 906071) (by norm_num)
theorem B1072705 : Blo 952587 1072705 := bbase (se 2 (by rfl) ⟨402264, by rfl⟩ : syracuseStep 1072705 = 804529) (by norm_num)
theorem B1433165 : Blo 952587 1433165 := bbase (se 3 (by rfl) ⟨268718, by rfl⟩ : syracuseStep 1433165 = 537437) (by norm_num)
theorem B4841045 : Blo 952587 4841045 := bbase (se 8 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 4841045 = 56731) (by norm_num)
theorem B1072741 : Blo 952587 1072741 := bbase (se 4 (by rfl) ⟨100569, by rfl⟩ : syracuseStep 1072741 = 201139) (by norm_num)
theorem B1433189 : Blo 952587 1433189 := bbase (se 4 (by rfl) ⟨134361, by rfl⟩ : syracuseStep 1433189 = 268723) (by norm_num)
theorem B1433213 : Blo 952587 1433213 := bbase (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) (by norm_num)
theorem B1072777 : Blo 952587 1072777 := bbase (se 2 (by rfl) ⟨402291, by rfl⟩ : syracuseStep 1072777 = 804583) (by norm_num)
theorem B1433237 : Blo 952587 1433237 := bbase (se 6 (by rfl) ⟨33591, by rfl⟩ : syracuseStep 1433237 = 67183) (by norm_num)
theorem B1072813 : Blo 952587 1072813 := bbase (se 3 (by rfl) ⟨201152, by rfl⟩ : syracuseStep 1072813 = 402305) (by norm_num)
theorem B2416301 : Blo 952587 2416301 := bbase (se 3 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 2416301 = 906113) (by norm_num)
theorem B1433261 : Blo 952587 1433261 := bbase (se 3 (by rfl) ⟨268736, by rfl⟩ : syracuseStep 1433261 = 537473) (by norm_num)
theorem B1433285 : Blo 952587 1433285 := bbase (se 4 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 1433285 = 268741) (by norm_num)
theorem B1072849 : Blo 952587 1072849 := bbase (se 2 (by rfl) ⟨402318, by rfl⟩ : syracuseStep 1072849 = 804637) (by norm_num)
theorem B1433309 : Blo 952587 1433309 := bbase (se 3 (by rfl) ⟨268745, by rfl⟩ : syracuseStep 1433309 = 537491) (by norm_num)
theorem B1072885 : Blo 952587 1072885 := bbase (se 5 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 1072885 = 100583) (by norm_num)
theorem B1433333 : Blo 952587 1433333 := bbase (se 5 (by rfl) ⟨67187, by rfl⟩ : syracuseStep 1433333 = 134375) (by norm_num)
theorem B1433357 : Blo 952587 1433357 := bbase (se 3 (by rfl) ⟨268754, by rfl⟩ : syracuseStep 1433357 = 537509) (by norm_num)
theorem B1072921 : Blo 952587 1072921 := bbase (se 2 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 1072921 = 804691) (by norm_num)
theorem B1433381 : Blo 952587 1433381 := bbase (se 4 (by rfl) ⟨134379, by rfl⟩ : syracuseStep 1433381 = 268759) (by norm_num)
theorem B4644661 : Blo 952587 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B1072957 : Blo 952587 1072957 := bbase (se 3 (by rfl) ⟨201179, by rfl⟩ : syracuseStep 1072957 = 402359) (by norm_num)
theorem B1433405 : Blo 952587 1433405 := bbase (se 3 (by rfl) ⟨268763, by rfl⟩ : syracuseStep 1433405 = 537527) (by norm_num)
theorem B1433429 : Blo 952587 1433429 := bbase (se 9 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 1433429 = 8399) (by norm_num)
theorem B1072993 : Blo 952587 1072993 := bbase (se 2 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 1072993 = 804745) (by norm_num)
theorem B3628901 : Blo 952587 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B2416493 : Blo 952587 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B1433453 : Blo 952587 1433453 := bbase (se 3 (by rfl) ⟨268772, by rfl⟩ : syracuseStep 1433453 = 537545) (by norm_num)
theorem B1073029 : Blo 952587 1073029 := bbase (se 4 (by rfl) ⟨100596, by rfl⟩ : syracuseStep 1073029 = 201193) (by norm_num)
theorem B1433477 : Blo 952587 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1433501 : Blo 952587 1433501 := bbase (se 3 (by rfl) ⟨268781, by rfl⟩ : syracuseStep 1433501 = 537563) (by norm_num)
theorem B1073065 : Blo 952587 1073065 := bbase (se 2 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 1073065 = 804799) (by norm_num)
theorem B1433525 : Blo 952587 1433525 := bbase (se 5 (by rfl) ⟨67196, by rfl⟩ : syracuseStep 1433525 = 134393) (by norm_num)
theorem B1073101 : Blo 952587 1073101 := bbase (se 3 (by rfl) ⟨201206, by rfl⟩ : syracuseStep 1073101 = 402413) (by norm_num)
theorem B1433549 : Blo 952587 1433549 := bbase (se 3 (by rfl) ⟨268790, by rfl⟩ : syracuseStep 1433549 = 537581) (by norm_num)
theorem B1433573 : Blo 952587 1433573 := bbase (se 4 (by rfl) ⟨134397, by rfl⟩ : syracuseStep 1433573 = 268795) (by norm_num)
theorem B1073137 : Blo 952587 1073137 := bbase (se 2 (by rfl) ⟨402426, by rfl⟩ : syracuseStep 1073137 = 804853) (by norm_num)
theorem B1007605 : Blo 952587 1007605 := bbase (se 5 (by rfl) ⟨47231, by rfl⟩ : syracuseStep 1007605 = 94463) (by norm_num)
theorem B1433597 : Blo 952587 1433597 := bbase (se 3 (by rfl) ⟨268799, by rfl⟩ : syracuseStep 1433597 = 537599) (by norm_num)
theorem B1073173 : Blo 952587 1073173 := bbase (se 6 (by rfl) ⟨25152, by rfl⟩ : syracuseStep 1073173 = 50305) (by norm_num)
theorem B1433621 : Blo 952587 1433621 := bbase (se 6 (by rfl) ⟨33600, by rfl⟩ : syracuseStep 1433621 = 67201) (by norm_num)
theorem B1433645 : Blo 952587 1433645 := bbase (se 3 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 1433645 = 537617) (by norm_num)
theorem B1073209 : Blo 952587 1073209 := bbase (se 2 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 1073209 = 804907) (by norm_num)
theorem B1433669 : Blo 952587 1433669 := bbase (se 4 (by rfl) ⟨134406, by rfl⟩ : syracuseStep 1433669 = 268813) (by norm_num)
theorem B1073245 : Blo 952587 1073245 := bbase (se 3 (by rfl) ⟨201233, by rfl⟩ : syracuseStep 1073245 = 402467) (by norm_num)
theorem B1433693 : Blo 952587 1433693 := bbase (se 3 (by rfl) ⟨268817, by rfl⟩ : syracuseStep 1433693 = 537635) (by norm_num)
theorem B1433717 : Blo 952587 1433717 := bbase (se 5 (by rfl) ⟨67205, by rfl⟩ : syracuseStep 1433717 = 134411) (by norm_num)
theorem B1073281 : Blo 952587 1073281 := bbase (se 2 (by rfl) ⟨402480, by rfl⟩ : syracuseStep 1073281 = 804961) (by norm_num)
theorem B4907141 : Blo 952587 4907141 := bbase (se 4 (by rfl) ⟨460044, by rfl⟩ : syracuseStep 4907141 = 920089) (by norm_num)
theorem B1433741 : Blo 952587 1433741 := bbase (se 3 (by rfl) ⟨268826, by rfl⟩ : syracuseStep 1433741 = 537653) (by norm_num)
theorem B1532045 : Blo 952587 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B1073317 : Blo 952587 1073317 := bbase (se 4 (by rfl) ⟨100623, by rfl⟩ : syracuseStep 1073317 = 201247) (by norm_num)
theorem B1433765 : Blo 952587 1433765 := bbase (se 4 (by rfl) ⟨134415, by rfl⟩ : syracuseStep 1433765 = 268831) (by norm_num)
theorem B1433789 : Blo 952587 1433789 := bbase (se 3 (by rfl) ⟨268835, by rfl⟩ : syracuseStep 1433789 = 537671) (by norm_num)
theorem B1630405 : Blo 952587 1630405 := bbase (se 4 (by rfl) ⟨152850, by rfl⟩ : syracuseStep 1630405 = 305701) (by norm_num)
theorem B2416837 : Blo 952587 2416837 := bbase (se 4 (by rfl) ⟨226578, by rfl⟩ : syracuseStep 2416837 = 453157) (by norm_num)
theorem B1073353 : Blo 952587 1073353 := bbase (se 2 (by rfl) ⟨402507, by rfl⟩ : syracuseStep 1073353 = 805015) (by norm_num)
theorem B1433813 : Blo 952587 1433813 := bbase (se 7 (by rfl) ⟨16802, by rfl⟩ : syracuseStep 1433813 = 33605) (by norm_num)
theorem B1073389 : Blo 952587 1073389 := bbase (se 3 (by rfl) ⟨201260, by rfl⟩ : syracuseStep 1073389 = 402521) (by norm_num)
theorem B1433837 : Blo 952587 1433837 := bbase (se 3 (by rfl) ⟨268844, by rfl⟩ : syracuseStep 1433837 = 537689) (by norm_num)
theorem B1433861 : Blo 952587 1433861 := bbase (se 4 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 1433861 = 268849) (by norm_num)
theorem B1073425 : Blo 952587 1073425 := bbase (se 2 (by rfl) ⟨402534, by rfl⟩ : syracuseStep 1073425 = 805069) (by norm_num)
theorem B1433885 : Blo 952587 1433885 := bbase (se 3 (by rfl) ⟨268853, by rfl⟩ : syracuseStep 1433885 = 537707) (by norm_num)
theorem B1073461 : Blo 952587 1073461 := bbase (se 5 (by rfl) ⟨50318, by rfl⟩ : syracuseStep 1073461 = 100637) (by norm_num)
theorem B2416949 : Blo 952587 2416949 := bbase (se 5 (by rfl) ⟨113294, by rfl⟩ : syracuseStep 2416949 = 226589) (by norm_num)
theorem B1433909 : Blo 952587 1433909 := bbase (se 5 (by rfl) ⟨67214, by rfl⟩ : syracuseStep 1433909 = 134429) (by norm_num)
theorem B1433933 : Blo 952587 1433933 := bbase (se 3 (by rfl) ⟨268862, by rfl⟩ : syracuseStep 1433933 = 537725) (by norm_num)
theorem B1073497 : Blo 952587 1073497 := bbase (se 2 (by rfl) ⟨402561, by rfl⟩ : syracuseStep 1073497 = 805123) (by norm_num)
theorem B1433957 : Blo 952587 1433957 := bbase (se 4 (by rfl) ⟨134433, by rfl⟩ : syracuseStep 1433957 = 268867) (by norm_num)
theorem B1073533 : Blo 952587 1073533 := bbase (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) (by norm_num)
theorem B1433981 : Blo 952587 1433981 := bbase (se 3 (by rfl) ⟨268871, by rfl⟩ : syracuseStep 1433981 = 537743) (by norm_num)
theorem B1434005 : Blo 952587 1434005 := bbase (se 6 (by rfl) ⟨33609, by rfl⟩ : syracuseStep 1434005 = 67219) (by norm_num)
theorem B1073569 : Blo 952587 1073569 := bbase (se 2 (by rfl) ⟨402588, by rfl⟩ : syracuseStep 1073569 = 805177) (by norm_num)
theorem B1434029 : Blo 952587 1434029 := bbase (se 3 (by rfl) ⟨268880, by rfl⟩ : syracuseStep 1434029 = 537761) (by norm_num)
theorem B1073605 : Blo 952587 1073605 := bbase (se 4 (by rfl) ⟨100650, by rfl⟩ : syracuseStep 1073605 = 201301) (by norm_num)
theorem B1434053 : Blo 952587 1434053 := bbase (se 4 (by rfl) ⟨134442, by rfl⟩ : syracuseStep 1434053 = 268885) (by norm_num)
theorem B1434077 : Blo 952587 1434077 := bbase (se 3 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 1434077 = 537779) (by norm_num)
theorem B1073641 : Blo 952587 1073641 := bbase (se 2 (by rfl) ⟨402615, by rfl⟩ : syracuseStep 1073641 = 805231) (by norm_num)
theorem B2417141 : Blo 952587 2417141 := bbase (se 5 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 2417141 = 226607) (by norm_num)
theorem B1434101 : Blo 952587 1434101 := bbase (se 5 (by rfl) ⟨67223, by rfl⟩ : syracuseStep 1434101 = 134447) (by norm_num)
theorem B1073677 : Blo 952587 1073677 := bbase (se 3 (by rfl) ⟨201314, by rfl⟩ : syracuseStep 1073677 = 402629) (by norm_num)
theorem B1434125 : Blo 952587 1434125 := bbase (se 3 (by rfl) ⟨268898, by rfl⟩ : syracuseStep 1434125 = 537797) (by norm_num)
theorem B1434149 : Blo 952587 1434149 := bbase (se 4 (by rfl) ⟨134451, by rfl⟩ : syracuseStep 1434149 = 268903) (by norm_num)
theorem B1073713 : Blo 952587 1073713 := bbase (se 2 (by rfl) ⟨402642, by rfl⟩ : syracuseStep 1073713 = 805285) (by norm_num)
theorem B1434173 : Blo 952587 1434173 := bbase (se 3 (by rfl) ⟨268907, by rfl⟩ : syracuseStep 1434173 = 537815) (by norm_num)
theorem B1073749 : Blo 952587 1073749 := bbase (se 8 (by rfl) ⟨6291, by rfl⟩ : syracuseStep 1073749 = 12583) (by norm_num)
theorem B1434197 : Blo 952587 1434197 := bbase (se 8 (by rfl) ⟨8403, by rfl⟩ : syracuseStep 1434197 = 16807) (by norm_num)
theorem B1434221 : Blo 952587 1434221 := bbase (se 3 (by rfl) ⟨268916, by rfl⟩ : syracuseStep 1434221 = 537833) (by norm_num)
theorem B1073785 : Blo 952587 1073785 := bbase (se 2 (by rfl) ⟨402669, by rfl⟩ : syracuseStep 1073785 = 805339) (by norm_num)
theorem B4579973 : Blo 952587 4579973 := bbase (se 4 (by rfl) ⟨429372, by rfl⟩ : syracuseStep 4579973 = 858745) (by norm_num)
theorem B1434245 : Blo 952587 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B1073821 : Blo 952587 1073821 := bbase (se 3 (by rfl) ⟨201341, by rfl⟩ : syracuseStep 1073821 = 402683) (by norm_num)
theorem B1434269 : Blo 952587 1434269 := bbase (se 3 (by rfl) ⟨268925, by rfl⟩ : syracuseStep 1434269 = 537851) (by norm_num)
theorem B1434293 : Blo 952587 1434293 := bbase (se 5 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 1434293 = 134465) (by norm_num)
theorem B1073857 : Blo 952587 1073857 := bbase (se 2 (by rfl) ⟨402696, by rfl⟩ : syracuseStep 1073857 = 805393) (by norm_num)
theorem B1434317 : Blo 952587 1434317 := bbase (se 3 (by rfl) ⟨268934, by rfl⟩ : syracuseStep 1434317 = 537869) (by norm_num)
theorem B1073893 : Blo 952587 1073893 := bbase (se 4 (by rfl) ⟨100677, by rfl⟩ : syracuseStep 1073893 = 201355) (by norm_num)
theorem B1434341 : Blo 952587 1434341 := bbase (se 4 (by rfl) ⟨134469, by rfl⟩ : syracuseStep 1434341 = 268939) (by norm_num)
theorem B1434365 : Blo 952587 1434365 := bbase (se 3 (by rfl) ⟨268943, by rfl⟩ : syracuseStep 1434365 = 537887) (by norm_num)
theorem B1073929 : Blo 952587 1073929 := bbase (se 2 (by rfl) ⟨402723, by rfl⟩ : syracuseStep 1073929 = 805447) (by norm_num)
theorem B1434389 : Blo 952587 1434389 := bbase (se 6 (by rfl) ⟨33618, by rfl⟩ : syracuseStep 1434389 = 67237) (by norm_num)
theorem B1073965 : Blo 952587 1073965 := bbase (se 3 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 1073965 = 402737) (by norm_num)
theorem B1434413 : Blo 952587 1434413 := bbase (se 3 (by rfl) ⟨268952, by rfl⟩ : syracuseStep 1434413 = 537905) (by norm_num)
theorem B1434437 : Blo 952587 1434437 := bbase (se 4 (by rfl) ⟨134478, by rfl⟩ : syracuseStep 1434437 = 268957) (by norm_num)
theorem B2417485 : Blo 952587 2417485 := bbase (se 3 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 2417485 = 906557) (by norm_num)
theorem B1074001 : Blo 952587 1074001 := bbase (se 2 (by rfl) ⟨402750, by rfl⟩ : syracuseStep 1074001 = 805501) (by norm_num)
theorem B1434461 : Blo 952587 1434461 := bbase (se 3 (by rfl) ⟨268961, by rfl⟩ : syracuseStep 1434461 = 537923) (by norm_num)
theorem B4842341 : Blo 952587 4842341 := bbase (se 4 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 4842341 = 907939) (by norm_num)
theorem B1074037 : Blo 952587 1074037 := bbase (se 5 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 1074037 = 100691) (by norm_num)
theorem B1434485 : Blo 952587 1434485 := bbase (se 5 (by rfl) ⟨67241, by rfl⟩ : syracuseStep 1434485 = 134483) (by norm_num)
theorem B1434509 : Blo 952587 1434509 := bbase (se 3 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 1434509 = 537941) (by norm_num)
theorem B1074073 : Blo 952587 1074073 := bbase (se 2 (by rfl) ⟨402777, by rfl⟩ : syracuseStep 1074073 = 805555) (by norm_num)
theorem B1434533 : Blo 952587 1434533 := bbase (se 4 (by rfl) ⟨134487, by rfl⟩ : syracuseStep 1434533 = 268975) (by norm_num)
theorem B1074109 : Blo 952587 1074109 := bbase (se 3 (by rfl) ⟨201395, by rfl⟩ : syracuseStep 1074109 = 402791) (by norm_num)
theorem B2417597 : Blo 952587 2417597 := bbase (se 3 (by rfl) ⟨453299, by rfl⟩ : syracuseStep 2417597 = 906599) (by norm_num)
theorem B1434557 : Blo 952587 1434557 := bbase (se 3 (by rfl) ⟨268979, by rfl⟩ : syracuseStep 1434557 = 537959) (by norm_num)
theorem B1434581 : Blo 952587 1434581 := bbase (se 7 (by rfl) ⟨16811, by rfl⟩ : syracuseStep 1434581 = 33623) (by norm_num)
theorem B1074145 : Blo 952587 1074145 := bbase (se 2 (by rfl) ⟨402804, by rfl⟩ : syracuseStep 1074145 = 805609) (by norm_num)
theorem B1434605 : Blo 952587 1434605 := bbase (se 3 (by rfl) ⟨268988, by rfl⟩ : syracuseStep 1434605 = 537977) (by norm_num)
theorem B2450429 : Blo 952587 2450429 := bbase (se 3 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 2450429 = 918911) (by norm_num)
theorem B1074181 : Blo 952587 1074181 := bbase (se 4 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 1074181 = 201409) (by norm_num)
theorem B1434629 : Blo 952587 1434629 := bbase (se 4 (by rfl) ⟨134496, by rfl⟩ : syracuseStep 1434629 = 268993) (by norm_num)
theorem B1434653 : Blo 952587 1434653 := bbase (se 3 (by rfl) ⟨268997, by rfl⟩ : syracuseStep 1434653 = 537995) (by norm_num)
theorem B1074217 : Blo 952587 1074217 := bbase (se 2 (by rfl) ⟨402831, by rfl⟩ : syracuseStep 1074217 = 805663) (by norm_num)
theorem B1434677 : Blo 952587 1434677 := bbase (se 5 (by rfl) ⟨67250, by rfl⟩ : syracuseStep 1434677 = 134501) (by norm_num)
theorem B1074253 : Blo 952587 1074253 := bbase (se 3 (by rfl) ⟨201422, by rfl⟩ : syracuseStep 1074253 = 402845) (by norm_num)
theorem B1434701 : Blo 952587 1434701 := bbase (se 3 (by rfl) ⟨269006, by rfl⟩ : syracuseStep 1434701 = 538013) (by norm_num)
theorem B1434725 : Blo 952587 1434725 := bbase (se 4 (by rfl) ⟨134505, by rfl⟩ : syracuseStep 1434725 = 269011) (by norm_num)
theorem B1074289 : Blo 952587 1074289 := bbase (se 2 (by rfl) ⟨402858, by rfl⟩ : syracuseStep 1074289 = 805717) (by norm_num)
theorem B2417789 : Blo 952587 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B1434749 : Blo 952587 1434749 := bbase (se 3 (by rfl) ⟨269015, by rfl⟩ : syracuseStep 1434749 = 538031) (by norm_num)
theorem B1074325 : Blo 952587 1074325 := bbase (se 6 (by rfl) ⟨25179, by rfl⟩ : syracuseStep 1074325 = 50359) (by norm_num)
theorem B1434773 : Blo 952587 1434773 := bbase (se 6 (by rfl) ⟨33627, by rfl⟩ : syracuseStep 1434773 = 67255) (by norm_num)
theorem B1434797 : Blo 952587 1434797 := bbase (se 3 (by rfl) ⟨269024, by rfl⟩ : syracuseStep 1434797 = 538049) (by norm_num)
theorem B1074361 : Blo 952587 1074361 := bbase (se 2 (by rfl) ⟨402885, by rfl⟩ : syracuseStep 1074361 = 805771) (by norm_num)
theorem B1434821 : Blo 952587 1434821 := bbase (se 4 (by rfl) ⟨134514, by rfl⟩ : syracuseStep 1434821 = 269029) (by norm_num)
theorem B1074397 : Blo 952587 1074397 := bbase (se 3 (by rfl) ⟨201449, by rfl⟩ : syracuseStep 1074397 = 402899) (by norm_num)
theorem B1434845 : Blo 952587 1434845 := bbase (se 3 (by rfl) ⟨269033, by rfl⟩ : syracuseStep 1434845 = 538067) (by norm_num)
theorem B1434869 : Blo 952587 1434869 := bbase (se 5 (by rfl) ⟨67259, by rfl⟩ : syracuseStep 1434869 = 134519) (by norm_num)
theorem B1074433 : Blo 952587 1074433 := bbase (se 2 (by rfl) ⟨402912, by rfl⟩ : syracuseStep 1074433 = 805825) (by norm_num)
theorem B16540949 : Blo 952587 16540949 := bbase (se 6 (by rfl) ⟨387678, by rfl⟩ : syracuseStep 16540949 = 775357) (by norm_num)
theorem B1074469 : Blo 952587 1074469 := bbase (se 4 (by rfl) ⟨100731, by rfl⟩ : syracuseStep 1074469 = 201463) (by norm_num)
theorem B1074505 : Blo 952587 1074505 := bbase (se 2 (by rfl) ⟨402939, by rfl⟩ : syracuseStep 1074505 = 805879) (by norm_num)
theorem B1074541 : Blo 952587 1074541 := bbase (se 3 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 1074541 = 402953) (by norm_num)
theorem B1074577 : Blo 952587 1074577 := bbase (se 2 (by rfl) ⟨402966, by rfl⟩ : syracuseStep 1074577 = 805933) (by norm_num)
theorem B1074613 : Blo 952587 1074613 := bbase (se 5 (by rfl) ⟨50372, by rfl⟩ : syracuseStep 1074613 = 100745) (by norm_num)
theorem B1205705 : Blo 952587 1205705 := bbase (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) (by norm_num)
theorem B2418133 : Blo 952587 2418133 := bbase (se 7 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 2418133 = 56675) (by norm_num)
theorem B1074649 : Blo 952587 1074649 := bbase (se 2 (by rfl) ⟨402993, by rfl⟩ : syracuseStep 1074649 = 805987) (by norm_num)
theorem B1074685 : Blo 952587 1074685 := bbase (se 3 (by rfl) ⟨201503, by rfl⟩ : syracuseStep 1074685 = 403007) (by norm_num)
theorem B1205761 : Blo 952587 1205761 := bbase (se 2 (by rfl) ⟨452160, by rfl⟩ : syracuseStep 1205761 = 904321) (by norm_num)
theorem B1074721 : Blo 952587 1074721 := bbase (se 2 (by rfl) ⟨403020, by rfl⟩ : syracuseStep 1074721 = 806041) (by norm_num)
theorem B2451005 : Blo 952587 2451005 := bbase (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) (by norm_num)
theorem B1074757 : Blo 952587 1074757 := bbase (se 4 (by rfl) ⟨100758, by rfl⟩ : syracuseStep 1074757 = 201517) (by norm_num)
theorem B2418245 : Blo 952587 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B1205857 : Blo 952587 1205857 := bbase (se 2 (by rfl) ⟨452196, by rfl⟩ : syracuseStep 1205857 = 904393) (by norm_num)
theorem B1074793 : Blo 952587 1074793 := bbase (se 2 (by rfl) ⟨403047, by rfl⟩ : syracuseStep 1074793 = 806095) (by norm_num)
theorem B1074829 : Blo 952587 1074829 := bbase (se 3 (by rfl) ⟨201530, by rfl⟩ : syracuseStep 1074829 = 403061) (by norm_num)
theorem B1074865 : Blo 952587 1074865 := bbase (se 2 (by rfl) ⟨403074, by rfl⟩ : syracuseStep 1074865 = 806149) (by norm_num)
theorem B1074901 : Blo 952587 1074901 := bbase (se 7 (by rfl) ⟨12596, by rfl⟩ : syracuseStep 1074901 = 25193) (by norm_num)
theorem B1074937 : Blo 952587 1074937 := bbase (se 2 (by rfl) ⟨403101, by rfl⟩ : syracuseStep 1074937 = 806203) (by norm_num)
theorem B1632005 : Blo 952587 1632005 := bbase (se 4 (by rfl) ⟨153000, by rfl⟩ : syracuseStep 1632005 = 306001) (by norm_num)
theorem B2418437 : Blo 952587 2418437 := bbase (se 4 (by rfl) ⟨226728, by rfl⟩ : syracuseStep 2418437 = 453457) (by norm_num)
theorem B1206029 : Blo 952587 1206029 := bbase (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) (by norm_num)
theorem B1074973 : Blo 952587 1074973 := bbase (se 3 (by rfl) ⟨201557, by rfl⟩ : syracuseStep 1074973 = 403115) (by norm_num)
theorem B1075009 : Blo 952587 1075009 := bbase (se 2 (by rfl) ⟨403128, by rfl⟩ : syracuseStep 1075009 = 806257) (by norm_num)
theorem B1206085 : Blo 952587 1206085 := bbase (se 4 (by rfl) ⟨113070, by rfl⟩ : syracuseStep 1206085 = 226141) (by norm_num)
theorem B2713429 : Blo 952587 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B1075045 : Blo 952587 1075045 := bbase (se 4 (by rfl) ⟨100785, by rfl⟩ : syracuseStep 1075045 = 201571) (by norm_num)
theorem B1075081 : Blo 952587 1075081 := bbase (se 2 (by rfl) ⟨403155, by rfl⟩ : syracuseStep 1075081 = 806311) (by norm_num)
theorem B1206181 : Blo 952587 1206181 := bbase (se 4 (by rfl) ⟨113079, by rfl⟩ : syracuseStep 1206181 = 226159) (by norm_num)
theorem B3631013 : Blo 952587 3631013 := bbase (se 4 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 3631013 = 680815) (by norm_num)
theorem B1075117 : Blo 952587 1075117 := bbase (se 3 (by rfl) ⟨201584, by rfl⟩ : syracuseStep 1075117 = 403169) (by norm_num)
theorem B1075153 : Blo 952587 1075153 := bbase (se 2 (by rfl) ⟨403182, by rfl⟩ : syracuseStep 1075153 = 806365) (by norm_num)
theorem B1075189 : Blo 952587 1075189 := bbase (se 5 (by rfl) ⟨50399, by rfl⟩ : syracuseStep 1075189 = 100799) (by norm_num)
theorem B1075225 : Blo 952587 1075225 := bbase (se 2 (by rfl) ⟨403209, by rfl⟩ : syracuseStep 1075225 = 806419) (by norm_num)
theorem B1075261 : Blo 952587 1075261 := bbase (se 3 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 1075261 = 403223) (by norm_num)
theorem B1206353 : Blo 952587 1206353 := bbase (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) (by norm_num)
theorem B2418781 : Blo 952587 2418781 := bbase (se 3 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 2418781 = 907043) (by norm_num)
theorem B1075297 : Blo 952587 1075297 := bbase (se 2 (by rfl) ⟨403236, by rfl⟩ : syracuseStep 1075297 = 806473) (by norm_num)
theorem B1075333 : Blo 952587 1075333 := bbase (se 4 (by rfl) ⟨100812, by rfl⟩ : syracuseStep 1075333 = 201625) (by norm_num)
theorem B1206409 : Blo 952587 1206409 := bbase (se 2 (by rfl) ⟨452403, by rfl⟩ : syracuseStep 1206409 = 904807) (by norm_num)
theorem B1075369 : Blo 952587 1075369 := bbase (se 2 (by rfl) ⟨403263, by rfl⟩ : syracuseStep 1075369 = 806527) (by norm_num)
theorem B3631301 : Blo 952587 3631301 := bbase (se 4 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 3631301 = 680869) (by norm_num)
theorem B2418893 : Blo 952587 2418893 := bbase (se 3 (by rfl) ⟨453542, by rfl⟩ : syracuseStep 2418893 = 907085) (by norm_num)
theorem B1075405 : Blo 952587 1075405 := bbase (se 3 (by rfl) ⟨201638, by rfl⟩ : syracuseStep 1075405 = 403277) (by norm_num)
theorem B1206505 : Blo 952587 1206505 := bbase (se 2 (by rfl) ⟨452439, by rfl⟩ : syracuseStep 1206505 = 904879) (by norm_num)
theorem B1075441 : Blo 952587 1075441 := bbase (se 2 (by rfl) ⟨403290, by rfl⟩ : syracuseStep 1075441 = 806581) (by norm_num)
theorem B1075477 : Blo 952587 1075477 := bbase (se 6 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 1075477 = 50413) (by norm_num)
theorem B1075513 : Blo 952587 1075513 := bbase (se 2 (by rfl) ⟨403317, by rfl⟩ : syracuseStep 1075513 = 806635) (by norm_num)
theorem B1075549 : Blo 952587 1075549 := bbase (se 3 (by rfl) ⟨201665, by rfl⟩ : syracuseStep 1075549 = 403331) (by norm_num)
theorem B1075585 : Blo 952587 1075585 := bbase (se 2 (by rfl) ⟨403344, by rfl⟩ : syracuseStep 1075585 = 806689) (by norm_num)
theorem B2419085 : Blo 952587 2419085 := bbase (se 3 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 2419085 = 907157) (by norm_num)
theorem B1206677 : Blo 952587 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B1075621 : Blo 952587 1075621 := bbase (se 4 (by rfl) ⟨100839, by rfl⟩ : syracuseStep 1075621 = 201679) (by norm_num)
theorem B1075657 : Blo 952587 1075657 := bbase (se 2 (by rfl) ⟨403371, by rfl⟩ : syracuseStep 1075657 = 806743) (by norm_num)
theorem B1206733 : Blo 952587 1206733 := bbase (se 3 (by rfl) ⟨226262, by rfl⟩ : syracuseStep 1206733 = 452525) (by norm_num)
theorem B7236053 : Blo 952587 7236053 := bbase (se 7 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 7236053 = 169595) (by norm_num)
theorem B5302741 : Blo 952587 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B1075693 : Blo 952587 1075693 := bbase (se 3 (by rfl) ⟨201692, by rfl⟩ : syracuseStep 1075693 = 403385) (by norm_num)
theorem B1075729 : Blo 952587 1075729 := bbase (se 2 (by rfl) ⟨403398, by rfl⟩ : syracuseStep 1075729 = 806797) (by norm_num)
theorem B1206829 : Blo 952587 1206829 := bbase (se 3 (by rfl) ⟨226280, by rfl⟩ : syracuseStep 1206829 = 452561) (by norm_num)
theorem B1075765 : Blo 952587 1075765 := bbase (se 5 (by rfl) ⟨50426, by rfl⟩ : syracuseStep 1075765 = 100853) (by norm_num)
theorem B1075801 : Blo 952587 1075801 := bbase (se 2 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 1075801 = 806851) (by norm_num)
theorem B1075837 : Blo 952587 1075837 := bbase (se 3 (by rfl) ⟨201719, by rfl⟩ : syracuseStep 1075837 = 403439) (by norm_num)
theorem B1075873 : Blo 952587 1075873 := bbase (se 2 (by rfl) ⟨403452, by rfl⟩ : syracuseStep 1075873 = 806905) (by norm_num)
theorem B1075909 : Blo 952587 1075909 := bbase (se 4 (by rfl) ⟨100866, by rfl⟩ : syracuseStep 1075909 = 201733) (by norm_num)
theorem B1207001 : Blo 952587 1207001 := bbase (se 2 (by rfl) ⟨452625, by rfl⟩ : syracuseStep 1207001 = 905251) (by norm_num)
theorem B2419429 : Blo 952587 2419429 := bbase (se 4 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 2419429 = 453643) (by norm_num)
theorem B1075945 : Blo 952587 1075945 := bbase (se 2 (by rfl) ⟨403479, by rfl⟩ : syracuseStep 1075945 = 806959) (by norm_num)
theorem B1075981 : Blo 952587 1075981 := bbase (se 3 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 1075981 = 403493) (by norm_num)
theorem B1207057 : Blo 952587 1207057 := bbase (se 2 (by rfl) ⟨452646, by rfl⟩ : syracuseStep 1207057 = 905293) (by norm_num)
theorem B1076017 : Blo 952587 1076017 := bbase (se 2 (by rfl) ⟨403506, by rfl⟩ : syracuseStep 1076017 = 807013) (by norm_num)
theorem B2419541 : Blo 952587 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B1076053 : Blo 952587 1076053 := bbase (se 9 (by rfl) ⟨3152, by rfl⟩ : syracuseStep 1076053 = 6305) (by norm_num)
theorem B1207153 : Blo 952587 1207153 := bbase (se 2 (by rfl) ⟨452682, by rfl⟩ : syracuseStep 1207153 = 905365) (by norm_num)
theorem B1076089 : Blo 952587 1076089 := bbase (se 2 (by rfl) ⟨403533, by rfl⟩ : syracuseStep 1076089 = 807067) (by norm_num)
theorem B1633181 : Blo 952587 1633181 := bbase (se 3 (by rfl) ⟨306221, by rfl⟩ : syracuseStep 1633181 = 612443) (by norm_num)
theorem B1076125 : Blo 952587 1076125 := bbase (se 3 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 1076125 = 403547) (by norm_num)
theorem B1076161 : Blo 952587 1076161 := bbase (se 2 (by rfl) ⟨403560, by rfl⟩ : syracuseStep 1076161 = 807121) (by norm_num)
theorem B2419733 : Blo 952587 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B1207325 : Blo 952587 1207325 := bbase (se 3 (by rfl) ⟨226373, by rfl⟩ : syracuseStep 1207325 = 452747) (by norm_num)
theorem B1207381 : Blo 952587 1207381 := bbase (se 8 (by rfl) ⟨7074, by rfl⟩ : syracuseStep 1207381 = 14149) (by norm_num)
theorem B8154229 : Blo 952587 8154229 := bbase (se 5 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 8154229 = 764459) (by norm_num)
theorem B1207477 : Blo 952587 1207477 := bbase (se 5 (by rfl) ⟨56600, by rfl⟩ : syracuseStep 1207477 = 113201) (by norm_num)
theorem B2714933 : Blo 952587 2714933 := bbase (se 5 (by rfl) ⟨127262, by rfl⟩ : syracuseStep 2714933 = 254525) (by norm_num)
theorem B1207649 : Blo 952587 1207649 := bbase (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) (by norm_num)
theorem B4582757 : Blo 952587 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B2420077 : Blo 952587 2420077 := bbase (se 3 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 2420077 = 907529) (by norm_num)
theorem B1207705 : Blo 952587 1207705 := bbase (se 2 (by rfl) ⟨452889, by rfl⟩ : syracuseStep 1207705 = 905779) (by norm_num)
theorem B2420189 : Blo 952587 2420189 := bbase (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) (by norm_num)
theorem B3141109 : Blo 952587 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B1207801 : Blo 952587 1207801 := bbase (se 2 (by rfl) ⟨452925, by rfl⟩ : syracuseStep 1207801 = 905851) (by norm_num)
theorem B2289149 : Blo 952587 2289149 := bbase (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) (by norm_num)
theorem B2420381 : Blo 952587 2420381 := bbase (se 3 (by rfl) ⟨453821, by rfl⟩ : syracuseStep 2420381 = 907643) (by norm_num)
theorem B1207973 : Blo 952587 1207973 := bbase (se 4 (by rfl) ⟨113247, by rfl⟩ : syracuseStep 1207973 = 226495) (by norm_num)
theorem B2289341 : Blo 952587 2289341 := bbase (se 3 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 2289341 = 858503) (by norm_num)
theorem B1208029 : Blo 952587 1208029 := bbase (se 3 (by rfl) ⟨226505, by rfl⟩ : syracuseStep 1208029 = 453011) (by norm_num)
theorem B1208125 : Blo 952587 1208125 := bbase (se 3 (by rfl) ⟨226523, by rfl⟩ : syracuseStep 1208125 = 453047) (by norm_num)
theorem B2322245 : Blo 952587 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B1208297 : Blo 952587 1208297 := bbase (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) (by norm_num)
theorem B2420725 : Blo 952587 2420725 := bbase (se 5 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 2420725 = 226943) (by norm_num)
theorem B1208353 : Blo 952587 1208353 := bbase (se 2 (by rfl) ⟨453132, by rfl⟩ : syracuseStep 1208353 = 906265) (by norm_num)
theorem B2617381 : Blo 952587 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B2420837 : Blo 952587 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B2322557 : Blo 952587 2322557 := bbase (se 3 (by rfl) ⟨435479, by rfl⟩ : syracuseStep 2322557 = 870959) (by norm_num)
theorem B1208449 : Blo 952587 1208449 := bbase (se 2 (by rfl) ⟨453168, by rfl⟩ : syracuseStep 1208449 = 906337) (by norm_num)
theorem B2421029 : Blo 952587 2421029 := bbase (se 4 (by rfl) ⟨226971, by rfl⟩ : syracuseStep 2421029 = 453943) (by norm_num)
theorem B1208621 : Blo 952587 1208621 := bbase (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) (by norm_num)
theorem B10875221 : Blo 952587 10875221 := bbase (se 10 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 10875221 = 31861) (by norm_num)
theorem B1208677 : Blo 952587 1208677 := bbase (se 4 (by rfl) ⟨113313, by rfl⟩ : syracuseStep 1208677 = 226627) (by norm_num)
theorem B1208773 : Blo 952587 1208773 := bbase (se 4 (by rfl) ⟨113322, by rfl⟩ : syracuseStep 1208773 = 226645) (by norm_num)
theorem B1208945 : Blo 952587 1208945 := bbase (se 2 (by rfl) ⟨453354, by rfl⟩ : syracuseStep 1208945 = 906709) (by norm_num)
theorem B2323109 : Blo 952587 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B1209001 : Blo 952587 1209001 := bbase (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) (by norm_num)
theorem B5501621 : Blo 952587 5501621 := bbase (se 5 (by rfl) ⟨257888, by rfl⟩ : syracuseStep 5501621 = 515777) (by norm_num)
theorem B2585317 : Blo 952587 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B1209097 : Blo 952587 1209097 := bbase (se 2 (by rfl) ⟨453411, by rfl⟩ : syracuseStep 1209097 = 906823) (by norm_num)
theorem B2716517 : Blo 952587 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B1209269 : Blo 952587 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B1209325 : Blo 952587 1209325 := bbase (se 3 (by rfl) ⟨226748, by rfl⟩ : syracuseStep 1209325 = 453497) (by norm_num)
theorem B8156213 : Blo 952587 8156213 := bbase (se 5 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 8156213 = 764645) (by norm_num)
theorem B1209421 : Blo 952587 1209421 := bbase (se 3 (by rfl) ⟨226766, by rfl⟩ : syracuseStep 1209421 = 453533) (by norm_num)
theorem B1569949 : Blo 952587 1569949 := bbase (se 3 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 1569949 = 588731) (by norm_num)
theorem B1209593 : Blo 952587 1209593 := bbase (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) (by norm_num)
theorem B1209649 : Blo 952587 1209649 := bbase (se 2 (by rfl) ⟨453618, by rfl⟩ : syracuseStep 1209649 = 907237) (by norm_num)
theorem B1209745 : Blo 952587 1209745 := bbase (se 2 (by rfl) ⟨453654, by rfl⟩ : syracuseStep 1209745 = 907309) (by norm_num)
theorem B2717189 : Blo 952587 2717189 := bbase (se 4 (by rfl) ⟨254736, by rfl⟩ : syracuseStep 2717189 = 509473) (by norm_num)
theorem B2094653 : Blo 952587 2094653 := bbase (se 3 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 2094653 = 785495) (by norm_num)
theorem B1209917 : Blo 952587 1209917 := bbase (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) (by norm_num)
theorem B1209973 : Blo 952587 1209973 := bbase (se 5 (by rfl) ⟨56717, by rfl⟩ : syracuseStep 1209973 = 113435) (by norm_num)
theorem B2291341 : Blo 952587 2291341 := bbase (se 3 (by rfl) ⟨429626, by rfl⟩ : syracuseStep 2291341 = 859253) (by norm_num)
theorem B1210069 : Blo 952587 1210069 := bbase (se 7 (by rfl) ⟨14180, by rfl⟩ : syracuseStep 1210069 = 28361) (by norm_num)
theorem B1144633 : Blo 952587 1144633 := bbase (se 2 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 1144633 = 858475) (by norm_num)
theorem B1210241 : Blo 952587 1210241 := bbase (se 2 (by rfl) ⟨453840, by rfl⟩ : syracuseStep 1210241 = 907681) (by norm_num)
theorem B2717621 : Blo 952587 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B1210297 : Blo 952587 1210297 := bbase (se 2 (by rfl) ⟨453861, by rfl⟩ : syracuseStep 1210297 = 907723) (by norm_num)
theorem B1144801 : Blo 952587 1144801 := bbase (se 2 (by rfl) ⟨429300, by rfl⟩ : syracuseStep 1144801 = 858601) (by norm_num)
theorem B1210393 : Blo 952587 1210393 := bbase (se 2 (by rfl) ⟨453897, by rfl⟩ : syracuseStep 1210393 = 907795) (by norm_num)
theorem B2619461 : Blo 952587 2619461 := bbase (se 4 (by rfl) ⟨245574, by rfl⟩ : syracuseStep 2619461 = 491149) (by norm_num)
theorem B1931357 : Blo 952587 1931357 := bbase (se 3 (by rfl) ⟨362129, by rfl⟩ : syracuseStep 1931357 = 724259) (by norm_num)
theorem B1144997 : Blo 952587 1144997 := bbase (se 4 (by rfl) ⟨107343, by rfl⟩ : syracuseStep 1144997 = 214687) (by norm_num)
theorem B1308853 : Blo 952587 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1210565 : Blo 952587 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B2291917 : Blo 952587 2291917 := bbase (se 3 (by rfl) ⟨429734, by rfl⟩ : syracuseStep 2291917 = 859469) (by norm_num)
theorem B13760725 : Blo 952587 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B1210621 : Blo 952587 1210621 := bbase (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) (by norm_num)
theorem B2292245 : Blo 952587 2292245 := bbase (se 6 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 2292245 = 107449) (by norm_num)
theorem B2292301 : Blo 952587 2292301 := bbase (se 3 (by rfl) ⟨429806, by rfl⟩ : syracuseStep 2292301 = 859613) (by norm_num)
theorem B2718373 : Blo 952587 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B2292533 : Blo 952587 2292533 := bbase (se 5 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 2292533 = 214925) (by norm_num)
theorem B1375133 : Blo 952587 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B2948069 : Blo 952587 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B2292725 : Blo 952587 2292725 := bbase (se 5 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 2292725 = 214943) (by norm_num)
theorem B1965485 : Blo 952587 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B5438933 : Blo 952587 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B982561 : Blo 952587 982561 := bbase (se 2 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 982561 = 736921) (by norm_num)
theorem B5504597 : Blo 952587 5504597 := bbase (se 8 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 5504597 = 64507) (by norm_num)
theorem B1146569 : Blo 952587 1146569 := bbase (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) (by norm_num)
theorem B2326229 : Blo 952587 2326229 := bbase (se 7 (by rfl) ⟨27260, by rfl⟩ : syracuseStep 2326229 = 54521) (by norm_num)
theorem B1146593 : Blo 952587 1146593 := bbase (se 2 (by rfl) ⟨429972, by rfl⟩ : syracuseStep 1146593 = 859945) (by norm_num)
theorem B3440357 : Blo 952587 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B1834805 : Blo 952587 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B2293685 : Blo 952587 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B4358069 : Blo 952587 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B5505059 : Blo 952587 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B2293859 : Blo 952587 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B3866737 : Blo 952587 3866737 := bstep (se 2 (by rfl) ⟨1450026, by rfl⟩ : syracuseStep 3866737 = 2900053) B2900053
theorem B2719889 : Blo 952587 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B2720081 : Blo 952587 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B10322275 : Blo 952587 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B1933969 : Blo 952587 1933969 := bstep (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) B1450477
theorem B2294705 : Blo 952587 2294705 := bstep (se 2 (by rfl) ⟨860514, by rfl⟩ : syracuseStep 2294705 = 1721029) B1721029
theorem B2294801 : Blo 952587 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1148035 : Blo 952587 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B1377443 : Blo 952587 1377443 := bstep (se 1 (by rfl) ⟨1033082, by rfl⟩ : syracuseStep 1377443 = 2066165) B2066165
theorem B5440709 : Blo 952587 5440709 := bstep (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) B1020133
theorem B2294993 : Blo 952587 2294993 := bstep (se 2 (by rfl) ⟨860622, by rfl⟩ : syracuseStep 2294993 = 1721245) B1721245
theorem B1148131 : Blo 952587 1148131 := bstep (se 1 (by rfl) ⟨861098, by rfl⟩ : syracuseStep 1148131 = 1722197) B1722197
theorem B2721073 : Blo 952587 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B1148419 : Blo 952587 1148419 := bstep (se 1 (by rfl) ⟨861314, by rfl⟩ : syracuseStep 1148419 = 1722629) B1722629
theorem B2721347 : Blo 952587 2721347 := bstep (se 1 (by rfl) ⟨2041010, by rfl⟩ : syracuseStep 2721347 = 4082021) B4082021
theorem B5441165 : Blo 952587 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B1148611 : Blo 952587 1148611 := bstep (se 1 (by rfl) ⟨861458, by rfl⟩ : syracuseStep 1148611 = 1722917) B1722917
theorem B2721539 : Blo 952587 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B1607539 : Blo 952587 1607539 := bstep (se 1 (by rfl) ⟨1205654, by rfl⟩ : syracuseStep 1607539 = 2411309) B2411309
theorem B1607681 : Blo 952587 1607681 := bstep (se 2 (by rfl) ⟨602880, by rfl⟩ : syracuseStep 1607681 = 1205761) B1205761
theorem B1017955 : Blo 952587 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B1607809 : Blo 952587 1607809 := bstep (se 2 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 1607809 = 1205857) B1205857
theorem B1607843 : Blo 952587 1607843 := bstep (se 1 (by rfl) ⟨1205882, by rfl⟩ : syracuseStep 1607843 = 2411765) B2411765
theorem B952595 : Blo 952587 952595 := bstep (se 1 (by rfl) ⟨714446, by rfl⟩ : syracuseStep 952595 = 1428893) B1428893
theorem B952611 : Blo 952587 952611 := bstep (se 1 (by rfl) ⟨714458, by rfl⟩ : syracuseStep 952611 = 1428917) B1428917
theorem B1607971 : Blo 952587 1607971 := bstep (se 1 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 1607971 = 2411957) B2411957
theorem B952627 : Blo 952587 952627 := bstep (se 1 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 952627 = 1428941) B1428941
theorem B952643 : Blo 952587 952643 := bstep (se 1 (by rfl) ⟨714482, by rfl⟩ : syracuseStep 952643 = 1428965) B1428965
theorem B2296145 : Blo 952587 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B952659 : Blo 952587 952659 := bstep (se 1 (by rfl) ⟨714494, by rfl⟩ : syracuseStep 952659 = 1428989) B1428989
theorem B952675 : Blo 952587 952675 := bstep (se 1 (by rfl) ⟨714506, by rfl⟩ : syracuseStep 952675 = 1429013) B1429013
theorem B952691 : Blo 952587 952691 := bstep (se 1 (by rfl) ⟨714518, by rfl⟩ : syracuseStep 952691 = 1429037) B1429037
theorem B952707 : Blo 952587 952707 := bstep (se 1 (by rfl) ⟨714530, by rfl⟩ : syracuseStep 952707 = 1429061) B1429061
theorem B952723 : Blo 952587 952723 := bstep (se 1 (by rfl) ⟨714542, by rfl⟩ : syracuseStep 952723 = 1429085) B1429085
theorem B952739 : Blo 952587 952739 := bstep (se 1 (by rfl) ⟨714554, by rfl⟩ : syracuseStep 952739 = 1429109) B1429109
theorem B1608113 : Blo 952587 1608113 := bstep (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) B1206085
theorem B952755 : Blo 952587 952755 := bstep (se 1 (by rfl) ⟨714566, by rfl⟩ : syracuseStep 952755 = 1429133) B1429133
theorem B952771 : Blo 952587 952771 := bstep (se 1 (by rfl) ⟨714578, by rfl⟩ : syracuseStep 952771 = 1429157) B1429157
theorem B952787 : Blo 952587 952787 := bstep (se 1 (by rfl) ⟨714590, by rfl⟩ : syracuseStep 952787 = 1429181) B1429181
theorem B952803 : Blo 952587 952803 := bstep (se 1 (by rfl) ⟨714602, by rfl⟩ : syracuseStep 952803 = 1429205) B1429205
theorem B952819 : Blo 952587 952819 := bstep (se 1 (by rfl) ⟨714614, by rfl⟩ : syracuseStep 952819 = 1429229) B1429229
theorem B952835 : Blo 952587 952835 := bstep (se 1 (by rfl) ⟨714626, by rfl⟩ : syracuseStep 952835 = 1429253) B1429253
theorem B1935875 : Blo 952587 1935875 := bstep (se 1 (by rfl) ⟨1451906, by rfl⟩ : syracuseStep 1935875 = 2903813) B2903813
theorem B952851 : Blo 952587 952851 := bstep (se 1 (by rfl) ⟨714638, by rfl⟩ : syracuseStep 952851 = 1429277) B1429277
theorem B952867 : Blo 952587 952867 := bstep (se 1 (by rfl) ⟨714650, by rfl⟩ : syracuseStep 952867 = 1429301) B1429301
theorem B2722349 : Blo 952587 2722349 := bstep (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) B1020881
theorem B1608241 : Blo 952587 1608241 := bstep (se 2 (by rfl) ⟨603090, by rfl⟩ : syracuseStep 1608241 = 1206181) B1206181
theorem B952883 : Blo 952587 952883 := bstep (se 1 (by rfl) ⟨714662, by rfl⟩ : syracuseStep 952883 = 1429325) B1429325
theorem B952899 : Blo 952587 952899 := bstep (se 1 (by rfl) ⟨714674, by rfl⟩ : syracuseStep 952899 = 1429349) B1429349
theorem B952915 : Blo 952587 952915 := bstep (se 1 (by rfl) ⟨714686, by rfl⟩ : syracuseStep 952915 = 1429373) B1429373
theorem B1608275 : Blo 952587 1608275 := bstep (se 1 (by rfl) ⟨1206206, by rfl⟩ : syracuseStep 1608275 = 2412413) B2412413
theorem B952931 : Blo 952587 952931 := bstep (se 1 (by rfl) ⟨714698, by rfl⟩ : syracuseStep 952931 = 1429397) B1429397
theorem B4590179 : Blo 952587 4590179 := bstep (se 1 (by rfl) ⟨3442634, by rfl⟩ : syracuseStep 4590179 = 6885269) B6885269
theorem B952947 : Blo 952587 952947 := bstep (se 1 (by rfl) ⟨714710, by rfl⟩ : syracuseStep 952947 = 1429421) B1429421
theorem B952963 : Blo 952587 952963 := bstep (se 1 (by rfl) ⟨714722, by rfl⟩ : syracuseStep 952963 = 1429445) B1429445
theorem B952979 : Blo 952587 952979 := bstep (se 1 (by rfl) ⟨714734, by rfl⟩ : syracuseStep 952979 = 1429469) B1429469
theorem B952995 : Blo 952587 952995 := bstep (se 1 (by rfl) ⟨714746, by rfl⟩ : syracuseStep 952995 = 1429493) B1429493
theorem B953011 : Blo 952587 953011 := bstep (se 1 (by rfl) ⟨714758, by rfl⟩ : syracuseStep 953011 = 1429517) B1429517
theorem B953027 : Blo 952587 953027 := bstep (se 1 (by rfl) ⟨714770, by rfl⟩ : syracuseStep 953027 = 1429541) B1429541
theorem B953043 : Blo 952587 953043 := bstep (se 1 (by rfl) ⟨714782, by rfl⟩ : syracuseStep 953043 = 1429565) B1429565
theorem B1608403 : Blo 952587 1608403 := bstep (se 1 (by rfl) ⟨1206302, by rfl⟩ : syracuseStep 1608403 = 2412605) B2412605
theorem B953059 : Blo 952587 953059 := bstep (se 1 (by rfl) ⟨714794, by rfl⟩ : syracuseStep 953059 = 1429589) B1429589
theorem B2722531 : Blo 952587 2722531 := bstep (se 1 (by rfl) ⟨2041898, by rfl⟩ : syracuseStep 2722531 = 4083797) B4083797
theorem B953075 : Blo 952587 953075 := bstep (se 1 (by rfl) ⟨714806, by rfl⟩ : syracuseStep 953075 = 1429613) B1429613
theorem B953091 : Blo 952587 953091 := bstep (se 1 (by rfl) ⟨714818, by rfl⟩ : syracuseStep 953091 = 1429637) B1429637
theorem B2067203 : Blo 952587 2067203 := bstep (se 1 (by rfl) ⟨1550402, by rfl⟩ : syracuseStep 2067203 = 3100805) B3100805
theorem B6195973 : Blo 952587 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B953107 : Blo 952587 953107 := bstep (se 1 (by rfl) ⟨714830, by rfl⟩ : syracuseStep 953107 = 1429661) B1429661
theorem B953123 : Blo 952587 953123 := bstep (se 1 (by rfl) ⟨714842, by rfl⟩ : syracuseStep 953123 = 1429685) B1429685
theorem B953139 : Blo 952587 953139 := bstep (se 1 (by rfl) ⟨714854, by rfl⟩ : syracuseStep 953139 = 1429709) B1429709
theorem B953155 : Blo 952587 953155 := bstep (se 1 (by rfl) ⟨714866, by rfl⟩ : syracuseStep 953155 = 1429733) B1429733
theorem B953171 : Blo 952587 953171 := bstep (se 1 (by rfl) ⟨714878, by rfl⟩ : syracuseStep 953171 = 1429757) B1429757
theorem B1608545 : Blo 952587 1608545 := bstep (se 2 (by rfl) ⟨603204, by rfl⟩ : syracuseStep 1608545 = 1206409) B1206409
theorem B953187 : Blo 952587 953187 := bstep (se 1 (by rfl) ⟨714890, by rfl⟩ : syracuseStep 953187 = 1429781) B1429781
theorem B953203 : Blo 952587 953203 := bstep (se 1 (by rfl) ⟨714902, by rfl⟩ : syracuseStep 953203 = 1429805) B1429805
theorem B953219 : Blo 952587 953219 := bstep (se 1 (by rfl) ⟨714914, by rfl⟩ : syracuseStep 953219 = 1429829) B1429829
theorem B953235 : Blo 952587 953235 := bstep (se 1 (by rfl) ⟨714926, by rfl⟩ : syracuseStep 953235 = 1429853) B1429853
theorem B953251 : Blo 952587 953251 := bstep (se 1 (by rfl) ⟨714938, by rfl⟩ : syracuseStep 953251 = 1429877) B1429877
theorem B953267 : Blo 952587 953267 := bstep (se 1 (by rfl) ⟨714950, by rfl⟩ : syracuseStep 953267 = 1429901) B1429901
theorem B953283 : Blo 952587 953283 := bstep (se 1 (by rfl) ⟨714962, by rfl⟩ : syracuseStep 953283 = 1429925) B1429925
theorem B953299 : Blo 952587 953299 := bstep (se 1 (by rfl) ⟨714974, by rfl⟩ : syracuseStep 953299 = 1429949) B1429949
theorem B1608673 : Blo 952587 1608673 := bstep (se 2 (by rfl) ⟨603252, by rfl⟩ : syracuseStep 1608673 = 1206505) B1206505
theorem B953315 : Blo 952587 953315 := bstep (se 1 (by rfl) ⟨714986, by rfl⟩ : syracuseStep 953315 = 1429973) B1429973
theorem B953331 : Blo 952587 953331 := bstep (se 1 (by rfl) ⟨714998, by rfl⟩ : syracuseStep 953331 = 1429997) B1429997
theorem B1608707 : Blo 952587 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B953347 : Blo 952587 953347 := bstep (se 1 (by rfl) ⟨715010, by rfl⟩ : syracuseStep 953347 = 1430021) B1430021
theorem B953363 : Blo 952587 953363 := bstep (se 1 (by rfl) ⟨715022, by rfl⟩ : syracuseStep 953363 = 1430045) B1430045
theorem B953379 : Blo 952587 953379 := bstep (se 1 (by rfl) ⟨715034, by rfl⟩ : syracuseStep 953379 = 1430069) B1430069
theorem B953395 : Blo 952587 953395 := bstep (se 1 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 953395 = 1430093) B1430093
theorem B953411 : Blo 952587 953411 := bstep (se 1 (by rfl) ⟨715058, by rfl⟩ : syracuseStep 953411 = 1430117) B1430117
theorem B953427 : Blo 952587 953427 := bstep (se 1 (by rfl) ⟨715070, by rfl⟩ : syracuseStep 953427 = 1430141) B1430141
theorem B953443 : Blo 952587 953443 := bstep (se 1 (by rfl) ⟨715082, by rfl⟩ : syracuseStep 953443 = 1430165) B1430165
theorem B953459 : Blo 952587 953459 := bstep (se 1 (by rfl) ⟨715094, by rfl⟩ : syracuseStep 953459 = 1430189) B1430189
theorem B1608835 : Blo 952587 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B953475 : Blo 952587 953475 := bstep (se 1 (by rfl) ⟨715106, by rfl⟩ : syracuseStep 953475 = 1430213) B1430213
theorem B953491 : Blo 952587 953491 := bstep (se 1 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 953491 = 1430237) B1430237
theorem B953507 : Blo 952587 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B953523 : Blo 952587 953523 := bstep (se 1 (by rfl) ⟨715142, by rfl⟩ : syracuseStep 953523 = 1430285) B1430285
theorem B953539 : Blo 952587 953539 := bstep (se 1 (by rfl) ⟨715154, by rfl⟩ : syracuseStep 953539 = 1430309) B1430309
theorem B2723021 : Blo 952587 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B953555 : Blo 952587 953555 := bstep (se 1 (by rfl) ⟨715166, by rfl⟩ : syracuseStep 953555 = 1430333) B1430333
theorem B953571 : Blo 952587 953571 := bstep (se 1 (by rfl) ⟨715178, by rfl⟩ : syracuseStep 953571 = 1430357) B1430357
theorem B953587 : Blo 952587 953587 := bstep (se 1 (by rfl) ⟨715190, by rfl⟩ : syracuseStep 953587 = 1430381) B1430381
theorem B953603 : Blo 952587 953603 := bstep (se 1 (by rfl) ⟨715202, by rfl⟩ : syracuseStep 953603 = 1430405) B1430405
theorem B1608977 : Blo 952587 1608977 := bstep (se 2 (by rfl) ⟨603366, by rfl⟩ : syracuseStep 1608977 = 1206733) B1206733
theorem B953619 : Blo 952587 953619 := bstep (se 1 (by rfl) ⟨715214, by rfl⟩ : syracuseStep 953619 = 1430429) B1430429
theorem B953635 : Blo 952587 953635 := bstep (se 1 (by rfl) ⟨715226, by rfl⟩ : syracuseStep 953635 = 1430453) B1430453
theorem B953651 : Blo 952587 953651 := bstep (se 1 (by rfl) ⟨715238, by rfl⟩ : syracuseStep 953651 = 1430477) B1430477
theorem B953667 : Blo 952587 953667 := bstep (se 1 (by rfl) ⟨715250, by rfl⟩ : syracuseStep 953667 = 1430501) B1430501
theorem B953683 : Blo 952587 953683 := bstep (se 1 (by rfl) ⟨715262, by rfl⟩ : syracuseStep 953683 = 1430525) B1430525
theorem B953699 : Blo 952587 953699 := bstep (se 1 (by rfl) ⟨715274, by rfl⟩ : syracuseStep 953699 = 1430549) B1430549
theorem B953715 : Blo 952587 953715 := bstep (se 1 (by rfl) ⟨715286, by rfl⟩ : syracuseStep 953715 = 1430573) B1430573
theorem B953731 : Blo 952587 953731 := bstep (se 1 (by rfl) ⟨715298, by rfl⟩ : syracuseStep 953731 = 1430597) B1430597
theorem B1609105 : Blo 952587 1609105 := bstep (se 2 (by rfl) ⟨603414, by rfl⟩ : syracuseStep 1609105 = 1206829) B1206829
theorem B953747 : Blo 952587 953747 := bstep (se 1 (by rfl) ⟨715310, by rfl⟩ : syracuseStep 953747 = 1430621) B1430621
theorem B953763 : Blo 952587 953763 := bstep (se 1 (by rfl) ⟨715322, by rfl⟩ : syracuseStep 953763 = 1430645) B1430645
theorem B1609139 : Blo 952587 1609139 := bstep (se 1 (by rfl) ⟨1206854, by rfl⟩ : syracuseStep 1609139 = 2413709) B2413709
theorem B953779 : Blo 952587 953779 := bstep (se 1 (by rfl) ⟨715334, by rfl⟩ : syracuseStep 953779 = 1430669) B1430669
theorem B953795 : Blo 952587 953795 := bstep (se 1 (by rfl) ⟨715346, by rfl⟩ : syracuseStep 953795 = 1430693) B1430693
theorem B953811 : Blo 952587 953811 := bstep (se 1 (by rfl) ⟨715358, by rfl⟩ : syracuseStep 953811 = 1430717) B1430717
theorem B1019347 : Blo 952587 1019347 := bstep (se 1 (by rfl) ⟨764510, by rfl⟩ : syracuseStep 1019347 = 1529021) B1529021
theorem B953827 : Blo 952587 953827 := bstep (se 1 (by rfl) ⟨715370, by rfl⟩ : syracuseStep 953827 = 1430741) B1430741
theorem B953843 : Blo 952587 953843 := bstep (se 1 (by rfl) ⟨715382, by rfl⟩ : syracuseStep 953843 = 1430765) B1430765
theorem B953859 : Blo 952587 953859 := bstep (se 1 (by rfl) ⟨715394, by rfl⟩ : syracuseStep 953859 = 1430789) B1430789
theorem B953875 : Blo 952587 953875 := bstep (se 1 (by rfl) ⟨715406, by rfl⟩ : syracuseStep 953875 = 1430813) B1430813
theorem B953891 : Blo 952587 953891 := bstep (se 1 (by rfl) ⟨715418, by rfl⟩ : syracuseStep 953891 = 1430837) B1430837
theorem B5508643 : Blo 952587 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1609267 : Blo 952587 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B953907 : Blo 952587 953907 := bstep (se 1 (by rfl) ⟨715430, by rfl⟩ : syracuseStep 953907 = 1430861) B1430861
theorem B953923 : Blo 952587 953923 := bstep (se 1 (by rfl) ⟨715442, by rfl⟩ : syracuseStep 953923 = 1430885) B1430885
theorem B953939 : Blo 952587 953939 := bstep (se 1 (by rfl) ⟨715454, by rfl⟩ : syracuseStep 953939 = 1430909) B1430909
theorem B953955 : Blo 952587 953955 := bstep (se 1 (by rfl) ⟨715466, by rfl⟩ : syracuseStep 953955 = 1430933) B1430933
theorem B953971 : Blo 952587 953971 := bstep (se 1 (by rfl) ⟨715478, by rfl⟩ : syracuseStep 953971 = 1430957) B1430957
theorem B953987 : Blo 952587 953987 := bstep (se 1 (by rfl) ⟨715490, by rfl⟩ : syracuseStep 953987 = 1430981) B1430981
theorem B954003 : Blo 952587 954003 := bstep (se 1 (by rfl) ⟨715502, by rfl⟩ : syracuseStep 954003 = 1431005) B1431005
theorem B2035363 : Blo 952587 2035363 := bstep (se 1 (by rfl) ⟨1526522, by rfl⟩ : syracuseStep 2035363 = 3053045) B3053045
theorem B954019 : Blo 952587 954019 := bstep (se 1 (by rfl) ⟨715514, by rfl⟩ : syracuseStep 954019 = 1431029) B1431029
theorem B954035 : Blo 952587 954035 := bstep (se 1 (by rfl) ⟨715526, by rfl⟩ : syracuseStep 954035 = 1431053) B1431053
theorem B1609409 : Blo 952587 1609409 := bstep (se 2 (by rfl) ⟨603528, by rfl⟩ : syracuseStep 1609409 = 1207057) B1207057
theorem B954051 : Blo 952587 954051 := bstep (se 1 (by rfl) ⟨715538, by rfl⟩ : syracuseStep 954051 = 1431077) B1431077
theorem B6524621 : Blo 952587 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B954067 : Blo 952587 954067 := bstep (se 1 (by rfl) ⟨715550, by rfl⟩ : syracuseStep 954067 = 1431101) B1431101
theorem B954083 : Blo 952587 954083 := bstep (se 1 (by rfl) ⟨715562, by rfl⟩ : syracuseStep 954083 = 1431125) B1431125
theorem B954099 : Blo 952587 954099 := bstep (se 1 (by rfl) ⟨715574, by rfl⟩ : syracuseStep 954099 = 1431149) B1431149
theorem B954115 : Blo 952587 954115 := bstep (se 1 (by rfl) ⟨715586, by rfl⟩ : syracuseStep 954115 = 1431173) B1431173
theorem B954131 : Blo 952587 954131 := bstep (se 1 (by rfl) ⟨715598, by rfl⟩ : syracuseStep 954131 = 1431197) B1431197
theorem B954147 : Blo 952587 954147 := bstep (se 1 (by rfl) ⟨715610, by rfl⟩ : syracuseStep 954147 = 1431221) B1431221
theorem B1380145 : Blo 952587 1380145 := bstep (se 2 (by rfl) ⟨517554, by rfl⟩ : syracuseStep 1380145 = 1035109) B1035109
theorem B954163 : Blo 952587 954163 := bstep (se 1 (by rfl) ⟨715622, by rfl⟩ : syracuseStep 954163 = 1431245) B1431245
theorem B1609537 : Blo 952587 1609537 := bstep (se 2 (by rfl) ⟨603576, by rfl⟩ : syracuseStep 1609537 = 1207153) B1207153
theorem B954179 : Blo 952587 954179 := bstep (se 1 (by rfl) ⟨715634, by rfl⟩ : syracuseStep 954179 = 1431269) B1431269
theorem B954195 : Blo 952587 954195 := bstep (se 1 (by rfl) ⟨715646, by rfl⟩ : syracuseStep 954195 = 1431293) B1431293
theorem B1609571 : Blo 952587 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B954211 : Blo 952587 954211 := bstep (se 1 (by rfl) ⟨715658, by rfl⟩ : syracuseStep 954211 = 1431317) B1431317
theorem B3215213 : Blo 952587 3215213 := bstep (se 3 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 3215213 = 1205705) B1205705
theorem B954227 : Blo 952587 954227 := bstep (se 1 (by rfl) ⟨715670, by rfl⟩ : syracuseStep 954227 = 1431341) B1431341
theorem B954243 : Blo 952587 954243 := bstep (se 1 (by rfl) ⟨715682, by rfl⟩ : syracuseStep 954243 = 1431365) B1431365
theorem B954259 : Blo 952587 954259 := bstep (se 1 (by rfl) ⟨715694, by rfl⟩ : syracuseStep 954259 = 1431389) B1431389
theorem B3215267 : Blo 952587 3215267 := bstep (se 1 (by rfl) ⟨2411450, by rfl⟩ : syracuseStep 3215267 = 4822901) B4822901
theorem B2035619 : Blo 952587 2035619 := bstep (se 1 (by rfl) ⟨1526714, by rfl⟩ : syracuseStep 2035619 = 3053429) B3053429
theorem B954275 : Blo 952587 954275 := bstep (se 1 (by rfl) ⟨715706, by rfl⟩ : syracuseStep 954275 = 1431413) B1431413
theorem B954291 : Blo 952587 954291 := bstep (se 1 (by rfl) ⟨715718, by rfl⟩ : syracuseStep 954291 = 1431437) B1431437
theorem B954307 : Blo 952587 954307 := bstep (se 1 (by rfl) ⟨715730, by rfl⟩ : syracuseStep 954307 = 1431461) B1431461
theorem B954323 : Blo 952587 954323 := bstep (se 1 (by rfl) ⟨715742, by rfl⟩ : syracuseStep 954323 = 1431485) B1431485
theorem B1609699 : Blo 952587 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B954339 : Blo 952587 954339 := bstep (se 1 (by rfl) ⟨715754, by rfl⟩ : syracuseStep 954339 = 1431509) B1431509
theorem B954355 : Blo 952587 954355 := bstep (se 1 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 954355 = 1431533) B1431533
theorem B954371 : Blo 952587 954371 := bstep (se 1 (by rfl) ⟨715778, by rfl⟩ : syracuseStep 954371 = 1431557) B1431557
theorem B954387 : Blo 952587 954387 := bstep (se 1 (by rfl) ⟨715790, by rfl⟩ : syracuseStep 954387 = 1431581) B1431581
theorem B954403 : Blo 952587 954403 := bstep (se 1 (by rfl) ⟨715802, by rfl⟩ : syracuseStep 954403 = 1431605) B1431605
theorem B954419 : Blo 952587 954419 := bstep (se 1 (by rfl) ⟨715814, by rfl⟩ : syracuseStep 954419 = 1431629) B1431629
theorem B954435 : Blo 952587 954435 := bstep (se 1 (by rfl) ⟨715826, by rfl⟩ : syracuseStep 954435 = 1431653) B1431653
theorem B954451 : Blo 952587 954451 := bstep (se 1 (by rfl) ⟨715838, by rfl⟩ : syracuseStep 954451 = 1431677) B1431677
theorem B954467 : Blo 952587 954467 := bstep (se 1 (by rfl) ⟨715850, by rfl⟩ : syracuseStep 954467 = 1431701) B1431701
theorem B1609841 : Blo 952587 1609841 := bstep (se 2 (by rfl) ⟨603690, by rfl⟩ : syracuseStep 1609841 = 1207381) B1207381
theorem B954483 : Blo 952587 954483 := bstep (se 1 (by rfl) ⟨715862, by rfl⟩ : syracuseStep 954483 = 1431725) B1431725
theorem B954499 : Blo 952587 954499 := bstep (se 1 (by rfl) ⟨715874, by rfl⟩ : syracuseStep 954499 = 1431749) B1431749
theorem B954515 : Blo 952587 954515 := bstep (se 1 (by rfl) ⟨715886, by rfl⟩ : syracuseStep 954515 = 1431773) B1431773
theorem B954531 : Blo 952587 954531 := bstep (se 1 (by rfl) ⟨715898, by rfl⟩ : syracuseStep 954531 = 1431797) B1431797
theorem B3215537 : Blo 952587 3215537 := bstep (se 2 (by rfl) ⟨1205826, by rfl⟩ : syracuseStep 3215537 = 2411653) B2411653
theorem B954547 : Blo 952587 954547 := bstep (se 1 (by rfl) ⟨715910, by rfl⟩ : syracuseStep 954547 = 1431821) B1431821
theorem B954563 : Blo 952587 954563 := bstep (se 1 (by rfl) ⟨715922, by rfl⟩ : syracuseStep 954563 = 1431845) B1431845
theorem B954579 : Blo 952587 954579 := bstep (se 1 (by rfl) ⟨715934, by rfl⟩ : syracuseStep 954579 = 1431869) B1431869
theorem B12226787 : Blo 952587 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B954595 : Blo 952587 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B1609969 : Blo 952587 1609969 := bstep (se 2 (by rfl) ⟨603738, by rfl⟩ : syracuseStep 1609969 = 1207477) B1207477
theorem B954611 : Blo 952587 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B954627 : Blo 952587 954627 := bstep (se 1 (by rfl) ⟨715970, by rfl⟩ : syracuseStep 954627 = 1431941) B1431941
theorem B1610003 : Blo 952587 1610003 := bstep (se 1 (by rfl) ⟨1207502, by rfl⟩ : syracuseStep 1610003 = 2415005) B2415005
theorem B954643 : Blo 952587 954643 := bstep (se 1 (by rfl) ⟨715982, by rfl⟩ : syracuseStep 954643 = 1431965) B1431965
theorem B954659 : Blo 952587 954659 := bstep (se 1 (by rfl) ⟨715994, by rfl⟩ : syracuseStep 954659 = 1431989) B1431989
theorem B954675 : Blo 952587 954675 := bstep (se 1 (by rfl) ⟨716006, by rfl⟩ : syracuseStep 954675 = 1432013) B1432013
theorem B954691 : Blo 952587 954691 := bstep (se 1 (by rfl) ⟨716018, by rfl⟩ : syracuseStep 954691 = 1432037) B1432037
theorem B954707 : Blo 952587 954707 := bstep (se 1 (by rfl) ⟨716030, by rfl⟩ : syracuseStep 954707 = 1432061) B1432061
theorem B954723 : Blo 952587 954723 := bstep (se 1 (by rfl) ⟨716042, by rfl⟩ : syracuseStep 954723 = 1432085) B1432085
theorem B13046129 : Blo 952587 13046129 := bstep (se 2 (by rfl) ⟨4892298, by rfl⟩ : syracuseStep 13046129 = 9784597) B9784597
theorem B954739 : Blo 952587 954739 := bstep (se 1 (by rfl) ⟨716054, by rfl⟩ : syracuseStep 954739 = 1432109) B1432109
theorem B954755 : Blo 952587 954755 := bstep (se 1 (by rfl) ⟨716066, by rfl⟩ : syracuseStep 954755 = 1432133) B1432133
theorem B1610131 : Blo 952587 1610131 := bstep (se 1 (by rfl) ⟨1207598, by rfl⟩ : syracuseStep 1610131 = 2415197) B2415197
theorem B954771 : Blo 952587 954771 := bstep (se 1 (by rfl) ⟨716078, by rfl⟩ : syracuseStep 954771 = 1432157) B1432157
theorem B954787 : Blo 952587 954787 := bstep (se 1 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 954787 = 1432181) B1432181
theorem B954803 : Blo 952587 954803 := bstep (se 1 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 954803 = 1432205) B1432205
theorem B954819 : Blo 952587 954819 := bstep (se 1 (by rfl) ⟨716114, by rfl⟩ : syracuseStep 954819 = 1432229) B1432229
theorem B954835 : Blo 952587 954835 := bstep (se 1 (by rfl) ⟨716126, by rfl⟩ : syracuseStep 954835 = 1432253) B1432253
theorem B954851 : Blo 952587 954851 := bstep (se 1 (by rfl) ⟨716138, by rfl⟩ : syracuseStep 954851 = 1432277) B1432277
theorem B5444081 : Blo 952587 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B954867 : Blo 952587 954867 := bstep (se 1 (by rfl) ⟨716150, by rfl⟩ : syracuseStep 954867 = 1432301) B1432301
theorem B954883 : Blo 952587 954883 := bstep (se 1 (by rfl) ⟨716162, by rfl⟩ : syracuseStep 954883 = 1432325) B1432325
theorem B954899 : Blo 952587 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B1610273 : Blo 952587 1610273 := bstep (se 2 (by rfl) ⟨603852, by rfl⟩ : syracuseStep 1610273 = 1207705) B1207705
theorem B954915 : Blo 952587 954915 := bstep (se 1 (by rfl) ⟨716186, by rfl⟩ : syracuseStep 954915 = 1432373) B1432373
theorem B4592177 : Blo 952587 4592177 := bstep (se 2 (by rfl) ⟨1722066, by rfl⟩ : syracuseStep 4592177 = 3444133) B3444133
theorem B954931 : Blo 952587 954931 := bstep (se 1 (by rfl) ⟨716198, by rfl⟩ : syracuseStep 954931 = 1432397) B1432397
theorem B954947 : Blo 952587 954947 := bstep (se 1 (by rfl) ⟨716210, by rfl⟩ : syracuseStep 954947 = 1432421) B1432421
theorem B954963 : Blo 952587 954963 := bstep (se 1 (by rfl) ⟨716222, by rfl⟩ : syracuseStep 954963 = 1432445) B1432445
theorem B954979 : Blo 952587 954979 := bstep (se 1 (by rfl) ⟨716234, by rfl⟩ : syracuseStep 954979 = 1432469) B1432469
theorem B954995 : Blo 952587 954995 := bstep (se 1 (by rfl) ⟨716246, by rfl⟩ : syracuseStep 954995 = 1432493) B1432493
theorem B955011 : Blo 952587 955011 := bstep (se 1 (by rfl) ⟨716258, by rfl⟩ : syracuseStep 955011 = 1432517) B1432517
theorem B955027 : Blo 952587 955027 := bstep (se 1 (by rfl) ⟨716270, by rfl⟩ : syracuseStep 955027 = 1432541) B1432541
theorem B1610401 : Blo 952587 1610401 := bstep (se 2 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 1610401 = 1207801) B1207801
theorem B955043 : Blo 952587 955043 := bstep (se 1 (by rfl) ⟨716282, by rfl⟩ : syracuseStep 955043 = 1432565) B1432565
theorem B955059 : Blo 952587 955059 := bstep (se 1 (by rfl) ⟨716294, by rfl⟩ : syracuseStep 955059 = 1432589) B1432589
theorem B1610435 : Blo 952587 1610435 := bstep (se 1 (by rfl) ⟨1207826, by rfl⟩ : syracuseStep 1610435 = 2415653) B2415653
theorem B955075 : Blo 952587 955075 := bstep (se 1 (by rfl) ⟨716306, by rfl⟩ : syracuseStep 955075 = 1432613) B1432613
theorem B3216077 : Blo 952587 3216077 := bstep (se 3 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 3216077 = 1206029) B1206029
theorem B955091 : Blo 952587 955091 := bstep (se 1 (by rfl) ⟨716318, by rfl⟩ : syracuseStep 955091 = 1432637) B1432637
theorem B955107 : Blo 952587 955107 := bstep (se 1 (by rfl) ⟨716330, by rfl⟩ : syracuseStep 955107 = 1432661) B1432661
theorem B6886129 : Blo 952587 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B955123 : Blo 952587 955123 := bstep (se 1 (by rfl) ⟨716342, by rfl⟩ : syracuseStep 955123 = 1432685) B1432685
theorem B3216131 : Blo 952587 3216131 := bstep (se 1 (by rfl) ⟨2412098, by rfl⟩ : syracuseStep 3216131 = 4824197) B4824197
theorem B955139 : Blo 952587 955139 := bstep (se 1 (by rfl) ⟨716354, by rfl⟩ : syracuseStep 955139 = 1432709) B1432709
theorem B3445517 : Blo 952587 3445517 := bstep (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) B1292069
theorem B955155 : Blo 952587 955155 := bstep (se 1 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 955155 = 1432733) B1432733
theorem B955171 : Blo 952587 955171 := bstep (se 1 (by rfl) ⟨716378, by rfl⟩ : syracuseStep 955171 = 1432757) B1432757
theorem B955187 : Blo 952587 955187 := bstep (se 1 (by rfl) ⟨716390, by rfl⟩ : syracuseStep 955187 = 1432781) B1432781
theorem B1610563 : Blo 952587 1610563 := bstep (se 1 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 1610563 = 2415845) B2415845
theorem B955203 : Blo 952587 955203 := bstep (se 1 (by rfl) ⟨716402, by rfl⟩ : syracuseStep 955203 = 1432805) B1432805
theorem B955219 : Blo 952587 955219 := bstep (se 1 (by rfl) ⟨716414, by rfl⟩ : syracuseStep 955219 = 1432829) B1432829
theorem B955235 : Blo 952587 955235 := bstep (se 1 (by rfl) ⟨716426, by rfl⟩ : syracuseStep 955235 = 1432853) B1432853
theorem B2036593 : Blo 952587 2036593 := bstep (se 2 (by rfl) ⟨763722, by rfl⟩ : syracuseStep 2036593 = 1527445) B1527445
theorem B955251 : Blo 952587 955251 := bstep (se 1 (by rfl) ⟨716438, by rfl⟩ : syracuseStep 955251 = 1432877) B1432877
theorem B955267 : Blo 952587 955267 := bstep (se 1 (by rfl) ⟨716450, by rfl⟩ : syracuseStep 955267 = 1432901) B1432901
theorem B955283 : Blo 952587 955283 := bstep (se 1 (by rfl) ⟨716462, by rfl⟩ : syracuseStep 955283 = 1432925) B1432925
theorem B955299 : Blo 952587 955299 := bstep (se 1 (by rfl) ⟨716474, by rfl⟩ : syracuseStep 955299 = 1432949) B1432949
theorem B955315 : Blo 952587 955315 := bstep (se 1 (by rfl) ⟨716486, by rfl⟩ : syracuseStep 955315 = 1432973) B1432973
theorem B955331 : Blo 952587 955331 := bstep (se 1 (by rfl) ⟨716498, by rfl⟩ : syracuseStep 955331 = 1432997) B1432997
theorem B1610705 : Blo 952587 1610705 := bstep (se 2 (by rfl) ⟨604014, by rfl⟩ : syracuseStep 1610705 = 1208029) B1208029
theorem B955347 : Blo 952587 955347 := bstep (se 1 (by rfl) ⟨716510, by rfl⟩ : syracuseStep 955347 = 1433021) B1433021
theorem B955363 : Blo 952587 955363 := bstep (se 1 (by rfl) ⟨716522, by rfl⟩ : syracuseStep 955363 = 1433045) B1433045
theorem B955379 : Blo 952587 955379 := bstep (se 1 (by rfl) ⟨716534, by rfl⟩ : syracuseStep 955379 = 1433069) B1433069
theorem B955395 : Blo 952587 955395 := bstep (se 1 (by rfl) ⟨716546, by rfl⟩ : syracuseStep 955395 = 1433093) B1433093
theorem B3216401 : Blo 952587 3216401 := bstep (se 2 (by rfl) ⟨1206150, by rfl⟩ : syracuseStep 3216401 = 2412301) B2412301
theorem B955411 : Blo 952587 955411 := bstep (se 1 (by rfl) ⟨716558, by rfl⟩ : syracuseStep 955411 = 1433117) B1433117
theorem B955427 : Blo 952587 955427 := bstep (se 1 (by rfl) ⟨716570, by rfl⟩ : syracuseStep 955427 = 1433141) B1433141
theorem B955443 : Blo 952587 955443 := bstep (se 1 (by rfl) ⟨716582, by rfl⟩ : syracuseStep 955443 = 1433165) B1433165
theorem B955459 : Blo 952587 955459 := bstep (se 1 (by rfl) ⟨716594, by rfl⟩ : syracuseStep 955459 = 1433189) B1433189
theorem B1610833 : Blo 952587 1610833 := bstep (se 2 (by rfl) ⟨604062, by rfl⟩ : syracuseStep 1610833 = 1208125) B1208125
theorem B955475 : Blo 952587 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B955491 : Blo 952587 955491 := bstep (se 1 (by rfl) ⟨716618, by rfl⟩ : syracuseStep 955491 = 1433237) B1433237
theorem B1610867 : Blo 952587 1610867 := bstep (se 1 (by rfl) ⟨1208150, by rfl⟩ : syracuseStep 1610867 = 2416301) B2416301
theorem B955507 : Blo 952587 955507 := bstep (se 1 (by rfl) ⟨716630, by rfl⟩ : syracuseStep 955507 = 1433261) B1433261
theorem B955523 : Blo 952587 955523 := bstep (se 1 (by rfl) ⟨716642, by rfl⟩ : syracuseStep 955523 = 1433285) B1433285
theorem B955539 : Blo 952587 955539 := bstep (se 1 (by rfl) ⟨716654, by rfl⟩ : syracuseStep 955539 = 1433309) B1433309
theorem B955555 : Blo 952587 955555 := bstep (se 1 (by rfl) ⟨716666, by rfl⟩ : syracuseStep 955555 = 1433333) B1433333
theorem B955571 : Blo 952587 955571 := bstep (se 1 (by rfl) ⟨716678, by rfl⟩ : syracuseStep 955571 = 1433357) B1433357
theorem B955587 : Blo 952587 955587 := bstep (se 1 (by rfl) ⟨716690, by rfl⟩ : syracuseStep 955587 = 1433381) B1433381
theorem B955603 : Blo 952587 955603 := bstep (se 1 (by rfl) ⟨716702, by rfl⟩ : syracuseStep 955603 = 1433405) B1433405
theorem B955619 : Blo 952587 955619 := bstep (se 1 (by rfl) ⟨716714, by rfl⟩ : syracuseStep 955619 = 1433429) B1433429
theorem B1610995 : Blo 952587 1610995 := bstep (se 1 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 1610995 = 2416493) B2416493
theorem B955635 : Blo 952587 955635 := bstep (se 1 (by rfl) ⟨716726, by rfl⟩ : syracuseStep 955635 = 1433453) B1433453
theorem B955651 : Blo 952587 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B955667 : Blo 952587 955667 := bstep (se 1 (by rfl) ⟨716750, by rfl⟩ : syracuseStep 955667 = 1433501) B1433501
theorem B955683 : Blo 952587 955683 := bstep (se 1 (by rfl) ⟨716762, by rfl⟩ : syracuseStep 955683 = 1433525) B1433525
theorem B955699 : Blo 952587 955699 := bstep (se 1 (by rfl) ⟨716774, by rfl⟩ : syracuseStep 955699 = 1433549) B1433549
theorem B955715 : Blo 952587 955715 := bstep (se 1 (by rfl) ⟨716786, by rfl⟩ : syracuseStep 955715 = 1433573) B1433573
theorem B955731 : Blo 952587 955731 := bstep (se 1 (by rfl) ⟨716798, by rfl⟩ : syracuseStep 955731 = 1433597) B1433597
theorem B955747 : Blo 952587 955747 := bstep (se 1 (by rfl) ⟨716810, by rfl⟩ : syracuseStep 955747 = 1433621) B1433621
theorem B955763 : Blo 952587 955763 := bstep (se 1 (by rfl) ⟨716822, by rfl⟩ : syracuseStep 955763 = 1433645) B1433645
theorem B1611137 : Blo 952587 1611137 := bstep (se 2 (by rfl) ⟨604176, by rfl⟩ : syracuseStep 1611137 = 1208353) B1208353
theorem B955779 : Blo 952587 955779 := bstep (se 1 (by rfl) ⟨716834, by rfl⟩ : syracuseStep 955779 = 1433669) B1433669
theorem B955795 : Blo 952587 955795 := bstep (se 1 (by rfl) ⟨716846, by rfl⟩ : syracuseStep 955795 = 1433693) B1433693
theorem B955811 : Blo 952587 955811 := bstep (se 1 (by rfl) ⟨716858, by rfl⟩ : syracuseStep 955811 = 1433717) B1433717
theorem B955827 : Blo 952587 955827 := bstep (se 1 (by rfl) ⟨716870, by rfl⟩ : syracuseStep 955827 = 1433741) B1433741
theorem B955843 : Blo 952587 955843 := bstep (se 1 (by rfl) ⟨716882, by rfl⟩ : syracuseStep 955843 = 1433765) B1433765
theorem B955859 : Blo 952587 955859 := bstep (se 1 (by rfl) ⟨716894, by rfl⟩ : syracuseStep 955859 = 1433789) B1433789
theorem B955875 : Blo 952587 955875 := bstep (se 1 (by rfl) ⟨716906, by rfl⟩ : syracuseStep 955875 = 1433813) B1433813
theorem B955891 : Blo 952587 955891 := bstep (se 1 (by rfl) ⟨716918, by rfl⟩ : syracuseStep 955891 = 1433837) B1433837
theorem B1611265 : Blo 952587 1611265 := bstep (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) B1208449
theorem B2037251 : Blo 952587 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B955907 : Blo 952587 955907 := bstep (se 1 (by rfl) ⟨716930, by rfl⟩ : syracuseStep 955907 = 1433861) B1433861
theorem B955923 : Blo 952587 955923 := bstep (se 1 (by rfl) ⟨716942, by rfl⟩ : syracuseStep 955923 = 1433885) B1433885
theorem B1611299 : Blo 952587 1611299 := bstep (se 1 (by rfl) ⟨1208474, by rfl⟩ : syracuseStep 1611299 = 2416949) B2416949
theorem B955939 : Blo 952587 955939 := bstep (se 1 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 955939 = 1433909) B1433909
theorem B3216941 : Blo 952587 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B4822577 : Blo 952587 4822577 := bstep (se 2 (by rfl) ⟨1808466, by rfl⟩ : syracuseStep 4822577 = 3616933) B3616933
theorem B955955 : Blo 952587 955955 := bstep (se 1 (by rfl) ⟨716966, by rfl⟩ : syracuseStep 955955 = 1433933) B1433933
theorem B10851893 : Blo 952587 10851893 := bstep (se 5 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 10851893 = 1017365) B1017365
theorem B955971 : Blo 952587 955971 := bstep (se 1 (by rfl) ⟨716978, by rfl⟩ : syracuseStep 955971 = 1433957) B1433957
theorem B955987 : Blo 952587 955987 := bstep (se 1 (by rfl) ⟨716990, by rfl⟩ : syracuseStep 955987 = 1433981) B1433981
theorem B3216995 : Blo 952587 3216995 := bstep (se 1 (by rfl) ⟨2412746, by rfl⟩ : syracuseStep 3216995 = 4825493) B4825493
theorem B956003 : Blo 952587 956003 := bstep (se 1 (by rfl) ⟨717002, by rfl⟩ : syracuseStep 956003 = 1434005) B1434005
theorem B18814577 : Blo 952587 18814577 := bstep (se 2 (by rfl) ⟨7055466, by rfl⟩ : syracuseStep 18814577 = 14110933) B14110933
theorem B956019 : Blo 952587 956019 := bstep (se 1 (by rfl) ⟨717014, by rfl⟩ : syracuseStep 956019 = 1434029) B1434029
theorem B956035 : Blo 952587 956035 := bstep (se 1 (by rfl) ⟨717026, by rfl⟩ : syracuseStep 956035 = 1434053) B1434053
theorem B5805701 : Blo 952587 5805701 := bstep (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) B1088569
theorem B4593293 : Blo 952587 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B956051 : Blo 952587 956051 := bstep (se 1 (by rfl) ⟨717038, by rfl⟩ : syracuseStep 956051 = 1434077) B1434077
theorem B1611427 : Blo 952587 1611427 := bstep (se 1 (by rfl) ⟨1208570, by rfl⟩ : syracuseStep 1611427 = 2417141) B2417141
theorem B956067 : Blo 952587 956067 := bstep (se 1 (by rfl) ⟨717050, by rfl⟩ : syracuseStep 956067 = 1434101) B1434101
theorem B956083 : Blo 952587 956083 := bstep (se 1 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 956083 = 1434125) B1434125
theorem B956099 : Blo 952587 956099 := bstep (se 1 (by rfl) ⟨717074, by rfl⟩ : syracuseStep 956099 = 1434149) B1434149
theorem B956115 : Blo 952587 956115 := bstep (se 1 (by rfl) ⟨717086, by rfl⟩ : syracuseStep 956115 = 1434173) B1434173
theorem B18618083 : Blo 952587 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B956131 : Blo 952587 956131 := bstep (se 1 (by rfl) ⟨717098, by rfl⟩ : syracuseStep 956131 = 1434197) B1434197
theorem B956147 : Blo 952587 956147 := bstep (se 1 (by rfl) ⟨717110, by rfl⟩ : syracuseStep 956147 = 1434221) B1434221
theorem B3053315 : Blo 952587 3053315 := bstep (se 1 (by rfl) ⟨2289986, by rfl⟩ : syracuseStep 3053315 = 4579973) B4579973
theorem B956163 : Blo 952587 956163 := bstep (se 1 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 956163 = 1434245) B1434245
theorem B956179 : Blo 952587 956179 := bstep (se 1 (by rfl) ⟨717134, by rfl⟩ : syracuseStep 956179 = 1434269) B1434269
theorem B956195 : Blo 952587 956195 := bstep (se 1 (by rfl) ⟨717146, by rfl⟩ : syracuseStep 956195 = 1434293) B1434293
theorem B1611569 : Blo 952587 1611569 := bstep (se 2 (by rfl) ⟨604338, by rfl⟩ : syracuseStep 1611569 = 1208677) B1208677
theorem B956211 : Blo 952587 956211 := bstep (se 1 (by rfl) ⟨717158, by rfl⟩ : syracuseStep 956211 = 1434317) B1434317
theorem B956227 : Blo 952587 956227 := bstep (se 1 (by rfl) ⟨717170, by rfl⟩ : syracuseStep 956227 = 1434341) B1434341
theorem B956243 : Blo 952587 956243 := bstep (se 1 (by rfl) ⟨717182, by rfl⟩ : syracuseStep 956243 = 1434365) B1434365
theorem B956259 : Blo 952587 956259 := bstep (se 1 (by rfl) ⟨717194, by rfl⟩ : syracuseStep 956259 = 1434389) B1434389
theorem B3217265 : Blo 952587 3217265 := bstep (se 2 (by rfl) ⟨1206474, by rfl⟩ : syracuseStep 3217265 = 2412949) B2412949
theorem B956275 : Blo 952587 956275 := bstep (se 1 (by rfl) ⟨717206, by rfl⟩ : syracuseStep 956275 = 1434413) B1434413
theorem B956291 : Blo 952587 956291 := bstep (se 1 (by rfl) ⟨717218, by rfl⟩ : syracuseStep 956291 = 1434437) B1434437
theorem B956307 : Blo 952587 956307 := bstep (se 1 (by rfl) ⟨717230, by rfl⟩ : syracuseStep 956307 = 1434461) B1434461
theorem B5445539 : Blo 952587 5445539 := bstep (se 1 (by rfl) ⟨4084154, by rfl⟩ : syracuseStep 5445539 = 8168309) B8168309
theorem B956323 : Blo 952587 956323 := bstep (se 1 (by rfl) ⟨717242, by rfl⟩ : syracuseStep 956323 = 1434485) B1434485
theorem B1611697 : Blo 952587 1611697 := bstep (se 2 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 1611697 = 1208773) B1208773
theorem B956339 : Blo 952587 956339 := bstep (se 1 (by rfl) ⟨717254, by rfl⟩ : syracuseStep 956339 = 1434509) B1434509
theorem B956355 : Blo 952587 956355 := bstep (se 1 (by rfl) ⟨717266, by rfl⟩ : syracuseStep 956355 = 1434533) B1434533
theorem B1611731 : Blo 952587 1611731 := bstep (se 1 (by rfl) ⟨1208798, by rfl⟩ : syracuseStep 1611731 = 2417597) B2417597
theorem B956371 : Blo 952587 956371 := bstep (se 1 (by rfl) ⟨717278, by rfl⟩ : syracuseStep 956371 = 1434557) B1434557
theorem B956387 : Blo 952587 956387 := bstep (se 1 (by rfl) ⟨717290, by rfl⟩ : syracuseStep 956387 = 1434581) B1434581
theorem B956403 : Blo 952587 956403 := bstep (se 1 (by rfl) ⟨717302, by rfl⟩ : syracuseStep 956403 = 1434605) B1434605
theorem B956419 : Blo 952587 956419 := bstep (se 1 (by rfl) ⟨717314, by rfl⟩ : syracuseStep 956419 = 1434629) B1434629
theorem B956435 : Blo 952587 956435 := bstep (se 1 (by rfl) ⟨717326, by rfl⟩ : syracuseStep 956435 = 1434653) B1434653
theorem B956451 : Blo 952587 956451 := bstep (se 1 (by rfl) ⟨717338, by rfl⟩ : syracuseStep 956451 = 1434677) B1434677
theorem B956467 : Blo 952587 956467 := bstep (se 1 (by rfl) ⟨717350, by rfl⟩ : syracuseStep 956467 = 1434701) B1434701
theorem B956483 : Blo 952587 956483 := bstep (se 1 (by rfl) ⟨717362, by rfl⟩ : syracuseStep 956483 = 1434725) B1434725
theorem B1611859 : Blo 952587 1611859 := bstep (se 1 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 1611859 = 2417789) B2417789
theorem B956499 : Blo 952587 956499 := bstep (se 1 (by rfl) ⟨717374, by rfl⟩ : syracuseStep 956499 = 1434749) B1434749
theorem B956515 : Blo 952587 956515 := bstep (se 1 (by rfl) ⟨717386, by rfl⟩ : syracuseStep 956515 = 1434773) B1434773
theorem B1808497 : Blo 952587 1808497 := bstep (se 2 (by rfl) ⟨678186, by rfl⟩ : syracuseStep 1808497 = 1356373) B1356373
theorem B956531 : Blo 952587 956531 := bstep (se 1 (by rfl) ⟨717398, by rfl⟩ : syracuseStep 956531 = 1434797) B1434797
theorem B956547 : Blo 952587 956547 := bstep (se 1 (by rfl) ⟨717410, by rfl⟩ : syracuseStep 956547 = 1434821) B1434821
theorem B956563 : Blo 952587 956563 := bstep (se 1 (by rfl) ⟨717422, by rfl⟩ : syracuseStep 956563 = 1434845) B1434845
theorem B956579 : Blo 952587 956579 := bstep (se 1 (by rfl) ⟨717434, by rfl⟩ : syracuseStep 956579 = 1434869) B1434869
theorem B1612001 : Blo 952587 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B3447089 : Blo 952587 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B2038097 : Blo 952587 2038097 := bstep (se 2 (by rfl) ⟨764286, by rfl⟩ : syracuseStep 2038097 = 1528573) B1528573
theorem B1612129 : Blo 952587 1612129 := bstep (se 2 (by rfl) ⟨604548, by rfl⟩ : syracuseStep 1612129 = 1209097) B1209097
theorem B1612163 : Blo 952587 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B3217805 : Blo 952587 3217805 := bstep (se 3 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 3217805 = 1206677) B1206677
theorem B3217859 : Blo 952587 3217859 := bstep (se 1 (by rfl) ⟨2413394, by rfl⟩ : syracuseStep 3217859 = 4826789) B4826789
theorem B1088003 : Blo 952587 1088003 := bstep (se 1 (by rfl) ⟨816002, by rfl⟩ : syracuseStep 1088003 = 1632005) B1632005
theorem B1612291 : Blo 952587 1612291 := bstep (se 1 (by rfl) ⟨1209218, by rfl⟩ : syracuseStep 1612291 = 2418437) B2418437
theorem B1612433 : Blo 952587 1612433 := bstep (se 2 (by rfl) ⟨604662, by rfl⟩ : syracuseStep 1612433 = 1209325) B1209325
theorem B3218129 : Blo 952587 3218129 := bstep (se 2 (by rfl) ⟨1206798, by rfl⟩ : syracuseStep 3218129 = 2413597) B2413597
theorem B1612561 : Blo 952587 1612561 := bstep (se 2 (by rfl) ⟨604710, by rfl⟩ : syracuseStep 1612561 = 1209421) B1209421
theorem B1547041 : Blo 952587 1547041 := bstep (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) B1160281
theorem B1612595 : Blo 952587 1612595 := bstep (se 1 (by rfl) ⟨1209446, by rfl⟩ : syracuseStep 1612595 = 2418893) B2418893
theorem B5446541 : Blo 952587 5446541 := bstep (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) B2042453
theorem B1612723 : Blo 952587 1612723 := bstep (se 1 (by rfl) ⟨1209542, by rfl⟩ : syracuseStep 1612723 = 2419085) B2419085
theorem B4594637 : Blo 952587 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B4824035 : Blo 952587 4824035 := bstep (se 1 (by rfl) ⟨3618026, by rfl⟩ : syracuseStep 4824035 = 7236053) B7236053
theorem B1612865 : Blo 952587 1612865 := bstep (se 2 (by rfl) ⟨604824, by rfl⟩ : syracuseStep 1612865 = 1209649) B1209649
theorem B17439857 : Blo 952587 17439857 := bstep (se 2 (by rfl) ⟨6539946, by rfl⟩ : syracuseStep 17439857 = 13079893) B13079893
theorem B1809553 : Blo 952587 1809553 := bstep (se 2 (by rfl) ⟨678582, by rfl⟩ : syracuseStep 1809553 = 1357165) B1357165
theorem B1612993 : Blo 952587 1612993 := bstep (se 2 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 1612993 = 1209745) B1209745
theorem B1613027 : Blo 952587 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B3218669 : Blo 952587 3218669 := bstep (se 3 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 3218669 = 1207001) B1207001
theorem B1449235 : Blo 952587 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B3218723 : Blo 952587 3218723 := bstep (se 1 (by rfl) ⟨2414042, by rfl⟩ : syracuseStep 3218723 = 4828085) B4828085
theorem B1613155 : Blo 952587 1613155 := bstep (se 1 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 1613155 = 2419733) B2419733
theorem B4070897 : Blo 952587 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B1613297 : Blo 952587 1613297 := bstep (se 2 (by rfl) ⟨604986, by rfl⟩ : syracuseStep 1613297 = 1209973) B1209973
theorem B3055121 : Blo 952587 3055121 := bstep (se 2 (by rfl) ⟨1145670, by rfl⟩ : syracuseStep 3055121 = 2291341) B2291341
theorem B1809955 : Blo 952587 1809955 := bstep (se 1 (by rfl) ⟨1357466, by rfl⟩ : syracuseStep 1809955 = 2714933) B2714933
theorem B3218993 : Blo 952587 3218993 := bstep (se 2 (by rfl) ⟨1207122, by rfl⟩ : syracuseStep 3218993 = 2414245) B2414245
theorem B3055171 : Blo 952587 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B1810001 : Blo 952587 1810001 := bstep (se 2 (by rfl) ⟨678750, by rfl⟩ : syracuseStep 1810001 = 1357501) B1357501
theorem B1613425 : Blo 952587 1613425 := bstep (se 2 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 1613425 = 1210069) B1210069
theorem B1613459 : Blo 952587 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B6889187 : Blo 952587 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B4824845 : Blo 952587 4824845 := bstep (se 3 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 4824845 = 1809317) B1809317
theorem B1613587 : Blo 952587 1613587 := bstep (se 1 (by rfl) ⟨1210190, by rfl⟩ : syracuseStep 1613587 = 2420381) B2420381
theorem B1810289 : Blo 952587 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1548163 : Blo 952587 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1613729 : Blo 952587 1613729 := bstep (se 2 (by rfl) ⟨605148, by rfl⟩ : syracuseStep 1613729 = 1210297) B1210297
theorem B16752581 : Blo 952587 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B1613857 : Blo 952587 1613857 := bstep (se 2 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 1613857 = 1210393) B1210393
theorem B1613891 : Blo 952587 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B3219533 : Blo 952587 3219533 := bstep (se 3 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 3219533 = 1207325) B1207325
theorem B1548371 : Blo 952587 1548371 := bstep (se 1 (by rfl) ⟨1161278, by rfl⟩ : syracuseStep 1548371 = 2322557) B2322557
theorem B3219587 : Blo 952587 3219587 := bstep (se 1 (by rfl) ⟨2414690, by rfl⟩ : syracuseStep 3219587 = 4829381) B4829381
theorem B1614019 : Blo 952587 1614019 := bstep (se 1 (by rfl) ⟨1210514, by rfl⟩ : syracuseStep 1614019 = 2421029) B2421029
theorem B7250147 : Blo 952587 7250147 := bstep (se 1 (by rfl) ⟨5437610, by rfl⟩ : syracuseStep 7250147 = 10875221) B10875221
theorem B1745137 : Blo 952587 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B3055889 : Blo 952587 3055889 := bstep (se 2 (by rfl) ⟨1145958, by rfl⟩ : syracuseStep 3055889 = 2291917) B2291917
theorem B1614161 : Blo 952587 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B3219857 : Blo 952587 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B1548739 : Blo 952587 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1811011 : Blo 952587 1811011 := bstep (se 1 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 1811011 = 2716517) B2716517
theorem B3056401 : Blo 952587 3056401 := bstep (se 2 (by rfl) ⟨1146150, by rfl⟩ : syracuseStep 3056401 = 2292301) B2292301
theorem B3220397 : Blo 952587 3220397 := bstep (se 3 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 3220397 = 1207649) B1207649
theorem B3220451 : Blo 952587 3220451 := bstep (se 1 (by rfl) ⟨2415338, by rfl⟩ : syracuseStep 3220451 = 4830677) B4830677
theorem B1811459 : Blo 952587 1811459 := bstep (se 1 (by rfl) ⟨1358594, by rfl⟩ : syracuseStep 1811459 = 2717189) B2717189
theorem B2040881 : Blo 952587 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B4072589 : Blo 952587 4072589 := bstep (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) B1527221
theorem B3220721 : Blo 952587 3220721 := bstep (se 2 (by rfl) ⟨1207770, by rfl⟩ : syracuseStep 3220721 = 2415541) B2415541
theorem B1811747 : Blo 952587 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1746307 : Blo 952587 1746307 := bstep (se 1 (by rfl) ⟨1309730, by rfl⟩ : syracuseStep 1746307 = 2619461) B2619461
theorem B1287571 : Blo 952587 1287571 := bstep (se 1 (by rfl) ⟨965678, by rfl⟩ : syracuseStep 1287571 = 1931357) B1931357
theorem B3221261 : Blo 952587 3221261 := bstep (se 3 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 3221261 = 1207973) B1207973
theorem B3221315 : Blo 952587 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B6104909 : Blo 952587 6104909 := bstep (se 3 (by rfl) ⟨1144670, by rfl⟩ : syracuseStep 6104909 = 2289341) B2289341
theorem B3057517 : Blo 952587 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B3057581 : Blo 952587 3057581 := bstep (se 3 (by rfl) ⟨573296, by rfl⟩ : syracuseStep 3057581 = 1146593) B1146593
theorem B2172977 : Blo 952587 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B3221585 : Blo 952587 3221585 := bstep (se 2 (by rfl) ⟨1208094, by rfl⟩ : syracuseStep 3221585 = 2416189) B2416189
theorem B1452227 : Blo 952587 1452227 := bstep (se 1 (by rfl) ⟨1089170, by rfl⟩ : syracuseStep 1452227 = 2178341) B2178341
theorem B1812689 : Blo 952587 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B1550819 : Blo 952587 1550819 := bstep (se 1 (by rfl) ⟨1163114, by rfl⟩ : syracuseStep 1550819 = 2326229) B2326229
theorem B1223203 : Blo 952587 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B1452593 : Blo 952587 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B3222125 : Blo 952587 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B4827761 : Blo 952587 4827761 := bstep (se 2 (by rfl) ⟨1810410, by rfl⟩ : syracuseStep 4827761 = 3620821) B3620821
theorem B3222179 : Blo 952587 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B1223363 : Blo 952587 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B1452835 : Blo 952587 1452835 := bstep (se 1 (by rfl) ⟨1089626, by rfl⟩ : syracuseStep 1452835 = 2179253) B2179253
theorem B2173873 : Blo 952587 2173873 := bstep (se 2 (by rfl) ⟨815202, by rfl⟩ : syracuseStep 2173873 = 1630405) B1630405
theorem B3222449 : Blo 952587 3222449 := bstep (se 2 (by rfl) ⟨1208418, by rfl⟩ : syracuseStep 3222449 = 2416837) B2416837
theorem B3877859 : Blo 952587 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B1813585 : Blo 952587 1813585 := bstep (se 2 (by rfl) ⟨680094, by rfl⟩ : syracuseStep 1813585 = 1360189) B1360189
theorem B1813745 : Blo 952587 1813745 := bstep (se 2 (by rfl) ⟨680154, by rfl⟩ : syracuseStep 1813745 = 1360309) B1360309
theorem B5156293 : Blo 952587 5156293 := bstep (se 4 (by rfl) ⟨483402, by rfl⟩ : syracuseStep 5156293 = 966805) B966805
theorem B3222989 : Blo 952587 3222989 := bstep (se 3 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 3222989 = 1208621) B1208621
theorem B3223043 : Blo 952587 3223043 := bstep (se 1 (by rfl) ⟨2417282, by rfl⟩ : syracuseStep 3223043 = 4834565) B4834565
theorem B1814147 : Blo 952587 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B3059363 : Blo 952587 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B3223313 : Blo 952587 3223313 := bstep (se 2 (by rfl) ⟨1208742, by rfl⟩ : syracuseStep 3223313 = 2417485) B2417485
theorem B4829219 : Blo 952587 4829219 := bstep (se 1 (by rfl) ⟨3621914, by rfl⟩ : syracuseStep 4829219 = 7243829) B7243829
theorem B6533219 : Blo 952587 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B3223853 : Blo 952587 3223853 := bstep (se 3 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 3223853 = 1208945) B1208945
theorem B3223907 : Blo 952587 3223907 := bstep (se 1 (by rfl) ⟨2417930, by rfl⟩ : syracuseStep 3223907 = 4835861) B4835861
theorem B1716689 : Blo 952587 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B1815043 : Blo 952587 1815043 := bstep (se 1 (by rfl) ⟨1361282, by rfl⟩ : syracuseStep 1815043 = 2722565) B2722565
theorem B3224177 : Blo 952587 3224177 := bstep (se 2 (by rfl) ⟨1209066, by rfl⟩ : syracuseStep 3224177 = 2418133) B2418133
theorem B1815203 : Blo 952587 1815203 := bstep (se 1 (by rfl) ⟨1361402, by rfl⟩ : syracuseStep 1815203 = 2722805) B2722805
theorem B12235445 : Blo 952587 12235445 := bstep (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) B1147073
theorem B4895437 : Blo 952587 4895437 := bstep (se 3 (by rfl) ⟨917894, by rfl⟩ : syracuseStep 4895437 = 1835789) B1835789
theorem B4830029 : Blo 952587 4830029 := bstep (se 3 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 4830029 = 1811261) B1811261
theorem B1717265 : Blo 952587 1717265 := bstep (se 2 (by rfl) ⟨643974, by rfl⟩ : syracuseStep 1717265 = 1287949) B1287949
theorem B1291361 : Blo 952587 1291361 := bstep (se 2 (by rfl) ⟨484260, by rfl⟩ : syracuseStep 1291361 = 968521) B968521
theorem B2143331 : Blo 952587 2143331 := bstep (se 1 (by rfl) ⟨1607498, by rfl⟩ : syracuseStep 2143331 = 3214997) B3214997
theorem B3617891 : Blo 952587 3617891 := bstep (se 1 (by rfl) ⟨2713418, by rfl⟩ : syracuseStep 3617891 = 5426837) B5426837
theorem B3617905 : Blo 952587 3617905 := bstep (se 2 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 3617905 = 2713429) B2713429
theorem B3224717 : Blo 952587 3224717 := bstep (se 3 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 3224717 = 1209269) B1209269
theorem B3224771 : Blo 952587 3224771 := bstep (se 1 (by rfl) ⟨2418578, by rfl⟩ : syracuseStep 3224771 = 4837157) B4837157
theorem B9188579 : Blo 952587 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B6534449 : Blo 952587 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B2143601 : Blo 952587 2143601 := bstep (se 2 (by rfl) ⟨803850, by rfl⟩ : syracuseStep 2143601 = 1607701) B1607701
theorem B2143619 : Blo 952587 2143619 := bstep (se 1 (by rfl) ⟨1607714, by rfl⟩ : syracuseStep 2143619 = 3215429) B3215429
theorem B4076963 : Blo 952587 4076963 := bstep (se 1 (by rfl) ⟨3057722, by rfl⟩ : syracuseStep 4076963 = 6115445) B6115445
theorem B1717699 : Blo 952587 1717699 := bstep (se 1 (by rfl) ⟨1288274, by rfl⟩ : syracuseStep 1717699 = 2576549) B2576549
theorem B7255493 : Blo 952587 7255493 := bstep (se 4 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 7255493 = 1360405) B1360405
theorem B3225041 : Blo 952587 3225041 := bstep (se 2 (by rfl) ⟨1209390, by rfl⟩ : syracuseStep 3225041 = 2418781) B2418781
theorem B1357393 : Blo 952587 1357393 := bstep (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) B1018045
theorem B2143889 : Blo 952587 2143889 := bstep (se 2 (by rfl) ⟨803958, by rfl⟩ : syracuseStep 2143889 = 1607917) B1607917
theorem B2143907 : Blo 952587 2143907 := bstep (se 1 (by rfl) ⟨1607930, by rfl⟩ : syracuseStep 2143907 = 3215861) B3215861
theorem B1357489 : Blo 952587 1357489 := bstep (se 2 (by rfl) ⟨509058, by rfl⟩ : syracuseStep 1357489 = 1018117) B1018117
theorem B16332515 : Blo 952587 16332515 := bstep (se 1 (by rfl) ⟨12249386, by rfl⟩ : syracuseStep 16332515 = 24498773) B24498773
theorem B2144177 : Blo 952587 2144177 := bstep (se 2 (by rfl) ⟨804066, by rfl⟩ : syracuseStep 2144177 = 1608133) B1608133
theorem B2144195 : Blo 952587 2144195 := bstep (se 1 (by rfl) ⟨1608146, by rfl⟩ : syracuseStep 2144195 = 3216293) B3216293
theorem B3225581 : Blo 952587 3225581 := bstep (se 3 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 3225581 = 1209593) B1209593
theorem B3225635 : Blo 952587 3225635 := bstep (se 1 (by rfl) ⟨2419226, by rfl⟩ : syracuseStep 3225635 = 4838453) B4838453
theorem B1357985 : Blo 952587 1357985 := bstep (se 2 (by rfl) ⟨509244, by rfl⟩ : syracuseStep 1357985 = 1018489) B1018489
theorem B3061937 : Blo 952587 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B2144465 : Blo 952587 2144465 := bstep (se 2 (by rfl) ⟨804174, by rfl⟩ : syracuseStep 2144465 = 1608349) B1608349
theorem B2144483 : Blo 952587 2144483 := bstep (se 1 (by rfl) ⟨1608362, by rfl⟩ : syracuseStep 2144483 = 3216725) B3216725
theorem B7747811 : Blo 952587 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B3225905 : Blo 952587 3225905 := bstep (se 2 (by rfl) ⟨1209714, by rfl⟩ : syracuseStep 3225905 = 2419429) B2419429
theorem B1292707 : Blo 952587 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B2144753 : Blo 952587 2144753 := bstep (se 2 (by rfl) ⟨804282, by rfl⟩ : syracuseStep 2144753 = 1608565) B1608565
theorem B2144771 : Blo 952587 2144771 := bstep (se 1 (by rfl) ⟨1608578, by rfl⟩ : syracuseStep 2144771 = 3217157) B3217157
theorem B3619363 : Blo 952587 3619363 := bstep (se 1 (by rfl) ⟨2714522, by rfl⟩ : syracuseStep 3619363 = 5429045) B5429045
theorem B8141381 : Blo 952587 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B2145041 : Blo 952587 2145041 := bstep (se 2 (by rfl) ⟨804390, by rfl⟩ : syracuseStep 2145041 = 1608781) B1608781
theorem B2145059 : Blo 952587 2145059 := bstep (se 1 (by rfl) ⟨1608794, by rfl⟩ : syracuseStep 2145059 = 3217589) B3217589
theorem B3226445 : Blo 952587 3226445 := bstep (se 3 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 3226445 = 1209917) B1209917
theorem B3226499 : Blo 952587 3226499 := bstep (se 1 (by rfl) ⟨2419874, by rfl⟩ : syracuseStep 3226499 = 4839749) B4839749
theorem B1719299 : Blo 952587 1719299 := bstep (se 1 (by rfl) ⟨1289474, by rfl⟩ : syracuseStep 1719299 = 2578949) B2578949
theorem B1358851 : Blo 952587 1358851 := bstep (se 1 (by rfl) ⟨1019138, by rfl⟩ : syracuseStep 1358851 = 2038277) B2038277
theorem B2145329 : Blo 952587 2145329 := bstep (se 2 (by rfl) ⟨804498, by rfl⟩ : syracuseStep 2145329 = 1608997) B1608997
theorem B2145347 : Blo 952587 2145347 := bstep (se 1 (by rfl) ⟨1609010, by rfl⟩ : syracuseStep 2145347 = 3218021) B3218021
theorem B1358947 : Blo 952587 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B3226769 : Blo 952587 3226769 := bstep (se 2 (by rfl) ⟨1210038, by rfl⟩ : syracuseStep 3226769 = 2420077) B2420077
theorem B8142065 : Blo 952587 8142065 := bstep (se 2 (by rfl) ⟨3053274, by rfl⟩ : syracuseStep 8142065 = 6106549) B6106549
theorem B2145617 : Blo 952587 2145617 := bstep (se 2 (by rfl) ⟨804606, by rfl⟩ : syracuseStep 2145617 = 1609213) B1609213
theorem B2145635 : Blo 952587 2145635 := bstep (se 1 (by rfl) ⟨1609226, by rfl⟩ : syracuseStep 2145635 = 3218453) B3218453
theorem B4078961 : Blo 952587 4078961 := bstep (se 2 (by rfl) ⟨1529610, by rfl⟩ : syracuseStep 4078961 = 3059221) B3059221
theorem B1359443 : Blo 952587 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B2145905 : Blo 952587 2145905 := bstep (se 2 (by rfl) ⟨804714, by rfl⟩ : syracuseStep 2145905 = 1609429) B1609429
theorem B2145923 : Blo 952587 2145923 := bstep (se 1 (by rfl) ⟨1609442, by rfl⟩ : syracuseStep 2145923 = 3218885) B3218885
theorem B3227309 : Blo 952587 3227309 := bstep (se 3 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 3227309 = 1210241) B1210241
theorem B4832945 : Blo 952587 4832945 := bstep (se 2 (by rfl) ⟨1812354, by rfl⟩ : syracuseStep 4832945 = 3624709) B3624709
theorem B3227363 : Blo 952587 3227363 := bstep (se 1 (by rfl) ⟨2420522, by rfl⟩ : syracuseStep 3227363 = 4841045) B4841045
theorem B7749361 : Blo 952587 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B5160773 : Blo 952587 5160773 := bstep (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) B967645
theorem B2146193 : Blo 952587 2146193 := bstep (se 2 (by rfl) ⟨804822, by rfl⟩ : syracuseStep 2146193 = 1609645) B1609645
theorem B2146211 : Blo 952587 2146211 := bstep (se 1 (by rfl) ⟨1609658, by rfl⟩ : syracuseStep 2146211 = 3219317) B3219317
theorem B3227633 : Blo 952587 3227633 := bstep (se 2 (by rfl) ⟨1210362, by rfl⟩ : syracuseStep 3227633 = 2420725) B2420725
theorem B3489841 : Blo 952587 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B2146481 : Blo 952587 2146481 := bstep (se 2 (by rfl) ⟨804930, by rfl⟩ : syracuseStep 2146481 = 1609861) B1609861
theorem B2146499 : Blo 952587 2146499 := bstep (se 1 (by rfl) ⟨1609874, by rfl⟩ : syracuseStep 2146499 = 3219749) B3219749
theorem B1360081 : Blo 952587 1360081 := bstep (se 2 (by rfl) ⟨510030, by rfl⟩ : syracuseStep 1360081 = 1020061) B1020061
theorem B2146769 : Blo 952587 2146769 := bstep (se 2 (by rfl) ⟨805038, by rfl⟩ : syracuseStep 2146769 = 1610077) B1610077
theorem B2146787 : Blo 952587 2146787 := bstep (se 1 (by rfl) ⟨1610090, by rfl⟩ : syracuseStep 2146787 = 3220181) B3220181
theorem B3228173 : Blo 952587 3228173 := bstep (se 3 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 3228173 = 1210565) B1210565
theorem B1360417 : Blo 952587 1360417 := bstep (se 2 (by rfl) ⟨510156, by rfl⟩ : syracuseStep 1360417 = 1020313) B1020313
theorem B3228227 : Blo 952587 3228227 := bstep (se 1 (by rfl) ⟨2421170, by rfl⟩ : syracuseStep 3228227 = 4842341) B4842341
theorem B3064397 : Blo 952587 3064397 := bstep (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) B1149149
theorem B3621581 : Blo 952587 3621581 := bstep (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) B1358093
theorem B2147057 : Blo 952587 2147057 := bstep (se 2 (by rfl) ⟨805146, by rfl⟩ : syracuseStep 2147057 = 1610293) B1610293
theorem B2147075 : Blo 952587 2147075 := bstep (se 1 (by rfl) ⟨1610306, by rfl⟩ : syracuseStep 2147075 = 3220613) B3220613
theorem B8373061 : Blo 952587 8373061 := bstep (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) B1569949
theorem B11027299 : Blo 952587 11027299 := bstep (se 1 (by rfl) ⟨8270474, by rfl⟩ : syracuseStep 11027299 = 16540949) B16540949
theorem B10863557 : Blo 952587 10863557 := bstep (se 4 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 10863557 = 2036917) B2036917
theorem B5522381 : Blo 952587 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B2147345 : Blo 952587 2147345 := bstep (se 2 (by rfl) ⟨805254, by rfl⟩ : syracuseStep 2147345 = 1610509) B1610509
theorem B2147363 : Blo 952587 2147363 := bstep (se 1 (by rfl) ⟨1610522, by rfl⟩ : syracuseStep 2147363 = 3221045) B3221045
theorem B9159749 : Blo 952587 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B4834403 : Blo 952587 4834403 := bstep (se 1 (by rfl) ⟨3625802, by rfl⟩ : syracuseStep 4834403 = 7251605) B7251605
theorem B4899953 : Blo 952587 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B1361009 : Blo 952587 1361009 := bstep (se 2 (by rfl) ⟨510378, by rfl⟩ : syracuseStep 1361009 = 1020757) B1020757
theorem B2147633 : Blo 952587 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B2147651 : Blo 952587 2147651 := bstep (se 1 (by rfl) ⟨1610738, by rfl⟩ : syracuseStep 2147651 = 3221477) B3221477
theorem B2147921 : Blo 952587 2147921 := bstep (se 2 (by rfl) ⟨805470, by rfl⟩ : syracuseStep 2147921 = 1610941) B1610941
theorem B2147939 : Blo 952587 2147939 := bstep (se 1 (by rfl) ⟨1610954, by rfl⟩ : syracuseStep 2147939 = 3221909) B3221909
theorem B1361539 : Blo 952587 1361539 := bstep (se 1 (by rfl) ⟨1021154, by rfl⟩ : syracuseStep 1361539 = 2042309) B2042309
theorem B4081421 : Blo 952587 4081421 := bstep (se 3 (by rfl) ⟨765266, by rfl⟩ : syracuseStep 4081421 = 1530533) B1530533
theorem B2148209 : Blo 952587 2148209 := bstep (se 2 (by rfl) ⟨805578, by rfl⟩ : syracuseStep 2148209 = 1611157) B1611157
theorem B2148227 : Blo 952587 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B4835213 : Blo 952587 4835213 := bstep (se 3 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 4835213 = 1813205) B1813205
theorem B1361875 : Blo 952587 1361875 := bstep (se 1 (by rfl) ⟨1021406, by rfl⟩ : syracuseStep 1361875 = 2042813) B2042813
theorem B12240881 : Blo 952587 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B2148497 : Blo 952587 2148497 := bstep (se 2 (by rfl) ⟨805686, by rfl⟩ : syracuseStep 2148497 = 1611373) B1611373
theorem B2148515 : Blo 952587 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B3360941 : Blo 952587 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B5425379 : Blo 952587 5425379 := bstep (se 1 (by rfl) ⟨4069034, by rfl⟩ : syracuseStep 5425379 = 8138069) B8138069
theorem B968995 : Blo 952587 968995 := bstep (se 1 (by rfl) ⟨726746, by rfl⟩ : syracuseStep 968995 = 1453493) B1453493
theorem B1526099 : Blo 952587 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B1526177 : Blo 952587 1526177 := bstep (se 2 (by rfl) ⟨572316, by rfl⟩ : syracuseStep 1526177 = 1144633) B1144633
theorem B2148785 : Blo 952587 2148785 := bstep (se 2 (by rfl) ⟨805794, by rfl⟩ : syracuseStep 2148785 = 1611589) B1611589
theorem B2148803 : Blo 952587 2148803 := bstep (se 1 (by rfl) ⟨1611602, by rfl⟩ : syracuseStep 2148803 = 3223205) B3223205
theorem B13748849 : Blo 952587 13748849 := bstep (se 2 (by rfl) ⟨5155818, by rfl⟩ : syracuseStep 13748849 = 10311637) B10311637
theorem B1526401 : Blo 952587 1526401 := bstep (se 2 (by rfl) ⟨572400, by rfl⟩ : syracuseStep 1526401 = 1144801) B1144801
theorem B2149073 : Blo 952587 2149073 := bstep (se 2 (by rfl) ⟨805902, by rfl⟩ : syracuseStep 2149073 = 1611805) B1611805
theorem B2149091 : Blo 952587 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B969571 : Blo 952587 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B2411441 : Blo 952587 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B2411491 : Blo 952587 2411491 := bstep (se 1 (by rfl) ⟨1808618, by rfl⟩ : syracuseStep 2411491 = 3617237) B3617237
theorem B2149361 : Blo 952587 2149361 := bstep (se 2 (by rfl) ⟨806010, by rfl⟩ : syracuseStep 2149361 = 1612021) B1612021
theorem B2149379 : Blo 952587 2149379 := bstep (se 1 (by rfl) ⟨1612034, by rfl⟩ : syracuseStep 2149379 = 3224069) B3224069
theorem B6212621 : Blo 952587 6212621 := bstep (se 3 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 6212621 = 2329733) B2329733
theorem B2411633 : Blo 952587 2411633 := bstep (se 2 (by rfl) ⟨904362, by rfl⟩ : syracuseStep 2411633 = 1808725) B1808725
theorem B7261325 : Blo 952587 7261325 := bstep (se 3 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 7261325 = 2722997) B2722997
theorem B2149649 : Blo 952587 2149649 := bstep (se 2 (by rfl) ⟨806118, by rfl⟩ : syracuseStep 2149649 = 1612237) B1612237
theorem B2149667 : Blo 952587 2149667 := bstep (se 1 (by rfl) ⟨1612250, by rfl⟩ : syracuseStep 2149667 = 3224501) B3224501
theorem B4082993 : Blo 952587 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B1428881 : Blo 952587 1428881 := bstep (se 2 (by rfl) ⟨535830, by rfl⟩ : syracuseStep 1428881 = 1071661) B1071661
theorem B1428899 : Blo 952587 1428899 := bstep (se 1 (by rfl) ⟨1071674, by rfl⟩ : syracuseStep 1428899 = 2143349) B2143349
theorem B1428929 : Blo 952587 1428929 := bstep (se 2 (by rfl) ⟨535848, by rfl⟩ : syracuseStep 1428929 = 1071697) B1071697
theorem B1428947 : Blo 952587 1428947 := bstep (se 1 (by rfl) ⟨1071710, by rfl⟩ : syracuseStep 1428947 = 2143421) B2143421
theorem B1428977 : Blo 952587 1428977 := bstep (se 2 (by rfl) ⟨535866, by rfl⟩ : syracuseStep 1428977 = 1071733) B1071733
theorem B1428995 : Blo 952587 1428995 := bstep (se 1 (by rfl) ⟨1071746, by rfl⟩ : syracuseStep 1428995 = 2143493) B2143493
theorem B1429025 : Blo 952587 1429025 := bstep (se 2 (by rfl) ⟨535884, by rfl⟩ : syracuseStep 1429025 = 1071769) B1071769
theorem B3624497 : Blo 952587 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B2149937 : Blo 952587 2149937 := bstep (se 2 (by rfl) ⟨806226, by rfl⟩ : syracuseStep 2149937 = 1612453) B1612453
theorem B1429043 : Blo 952587 1429043 := bstep (se 1 (by rfl) ⟨1071782, by rfl⟩ : syracuseStep 1429043 = 2143565) B2143565
theorem B2149955 : Blo 952587 2149955 := bstep (se 1 (by rfl) ⟨1612466, by rfl⟩ : syracuseStep 2149955 = 3224933) B3224933
theorem B1429073 : Blo 952587 1429073 := bstep (se 2 (by rfl) ⟨535902, by rfl⟩ : syracuseStep 1429073 = 1071805) B1071805
theorem B1429091 : Blo 952587 1429091 := bstep (se 1 (by rfl) ⟨1071818, by rfl⟩ : syracuseStep 1429091 = 2143637) B2143637
theorem B1429121 : Blo 952587 1429121 := bstep (se 2 (by rfl) ⟨535920, by rfl⟩ : syracuseStep 1429121 = 1071841) B1071841
theorem B1429139 : Blo 952587 1429139 := bstep (se 1 (by rfl) ⟨1071854, by rfl⟩ : syracuseStep 1429139 = 2143709) B2143709
theorem B1429169 : Blo 952587 1429169 := bstep (se 2 (by rfl) ⟨535938, by rfl⟩ : syracuseStep 1429169 = 1071877) B1071877
theorem B1429187 : Blo 952587 1429187 := bstep (se 1 (by rfl) ⟨1071890, by rfl⟩ : syracuseStep 1429187 = 2143781) B2143781
theorem B1396435 : Blo 952587 1396435 := bstep (se 1 (by rfl) ⟨1047326, by rfl⟩ : syracuseStep 1396435 = 2094653) B2094653
theorem B1429217 : Blo 952587 1429217 := bstep (se 2 (by rfl) ⟨535956, by rfl⟩ : syracuseStep 1429217 = 1071913) B1071913
theorem B1429235 : Blo 952587 1429235 := bstep (se 1 (by rfl) ⟨1071926, by rfl⟩ : syracuseStep 1429235 = 2143853) B2143853
theorem B1429265 : Blo 952587 1429265 := bstep (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) B1071949
theorem B1429283 : Blo 952587 1429283 := bstep (se 1 (by rfl) ⟨1071962, by rfl⟩ : syracuseStep 1429283 = 2143925) B2143925
theorem B1429313 : Blo 952587 1429313 := bstep (se 2 (by rfl) ⟨535992, by rfl⟩ : syracuseStep 1429313 = 1071985) B1071985
theorem B2150225 : Blo 952587 2150225 := bstep (se 2 (by rfl) ⟨806334, by rfl⟩ : syracuseStep 2150225 = 1612669) B1612669
theorem B1429331 : Blo 952587 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B2150243 : Blo 952587 2150243 := bstep (se 1 (by rfl) ⟨1612682, by rfl⟩ : syracuseStep 2150243 = 3225365) B3225365
theorem B1429361 : Blo 952587 1429361 := bstep (se 2 (by rfl) ⟨536010, by rfl⟩ : syracuseStep 1429361 = 1072021) B1072021
theorem B1429379 : Blo 952587 1429379 := bstep (se 1 (by rfl) ⟨1072034, by rfl⟩ : syracuseStep 1429379 = 2144069) B2144069
theorem B1429409 : Blo 952587 1429409 := bstep (se 2 (by rfl) ⟨536028, by rfl⟩ : syracuseStep 1429409 = 1072057) B1072057
theorem B1429427 : Blo 952587 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B1429457 : Blo 952587 1429457 := bstep (se 2 (by rfl) ⟨536046, by rfl⟩ : syracuseStep 1429457 = 1072093) B1072093
theorem B1429475 : Blo 952587 1429475 := bstep (se 1 (by rfl) ⟨1072106, by rfl⟩ : syracuseStep 1429475 = 2144213) B2144213
theorem B1429505 : Blo 952587 1429505 := bstep (se 2 (by rfl) ⟨536064, by rfl⟩ : syracuseStep 1429505 = 1072129) B1072129
theorem B1429523 : Blo 952587 1429523 := bstep (se 1 (by rfl) ⟨1072142, by rfl⟩ : syracuseStep 1429523 = 2144285) B2144285
theorem B1429553 : Blo 952587 1429553 := bstep (se 2 (by rfl) ⟨536082, by rfl⟩ : syracuseStep 1429553 = 1072165) B1072165
theorem B2904113 : Blo 952587 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B1429571 : Blo 952587 1429571 := bstep (se 1 (by rfl) ⟨1072178, by rfl⟩ : syracuseStep 1429571 = 2144357) B2144357
theorem B5427269 : Blo 952587 5427269 := bstep (se 4 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 5427269 = 1017613) B1017613
theorem B2412625 : Blo 952587 2412625 := bstep (se 2 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 2412625 = 1809469) B1809469
theorem B1429601 : Blo 952587 1429601 := bstep (se 2 (by rfl) ⟨536100, by rfl⟩ : syracuseStep 1429601 = 1072201) B1072201
theorem B2150513 : Blo 952587 2150513 := bstep (se 2 (by rfl) ⟨806442, by rfl⟩ : syracuseStep 2150513 = 1612885) B1612885
theorem B1429619 : Blo 952587 1429619 := bstep (se 1 (by rfl) ⟨1072214, by rfl⟩ : syracuseStep 1429619 = 2144429) B2144429
theorem B2150531 : Blo 952587 2150531 := bstep (se 1 (by rfl) ⟨1612898, by rfl⟩ : syracuseStep 2150531 = 3225797) B3225797
theorem B1429649 : Blo 952587 1429649 := bstep (se 2 (by rfl) ⟨536118, by rfl⟩ : syracuseStep 1429649 = 1072237) B1072237
theorem B1429667 : Blo 952587 1429667 := bstep (se 1 (by rfl) ⟨1072250, by rfl⟩ : syracuseStep 1429667 = 2144501) B2144501
theorem B1429697 : Blo 952587 1429697 := bstep (se 2 (by rfl) ⟨536136, by rfl⟩ : syracuseStep 1429697 = 1072273) B1072273
theorem B1429715 : Blo 952587 1429715 := bstep (se 1 (by rfl) ⟨1072286, by rfl⟩ : syracuseStep 1429715 = 2144573) B2144573
theorem B1429745 : Blo 952587 1429745 := bstep (se 2 (by rfl) ⟨536154, by rfl⟩ : syracuseStep 1429745 = 1072309) B1072309
theorem B1429763 : Blo 952587 1429763 := bstep (se 1 (by rfl) ⟨1072322, by rfl⟩ : syracuseStep 1429763 = 2144645) B2144645
theorem B1429793 : Blo 952587 1429793 := bstep (se 2 (by rfl) ⟨536172, by rfl⟩ : syracuseStep 1429793 = 1072345) B1072345
theorem B1429811 : Blo 952587 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B1429841 : Blo 952587 1429841 := bstep (se 2 (by rfl) ⟨536190, by rfl⟩ : syracuseStep 1429841 = 1072381) B1072381
theorem B1429859 : Blo 952587 1429859 := bstep (se 1 (by rfl) ⟨1072394, by rfl⟩ : syracuseStep 1429859 = 2144789) B2144789
theorem B2412899 : Blo 952587 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B1528163 : Blo 952587 1528163 := bstep (se 1 (by rfl) ⟨1146122, by rfl⟩ : syracuseStep 1528163 = 2292245) B2292245
theorem B1429889 : Blo 952587 1429889 := bstep (se 2 (by rfl) ⟨536208, by rfl⟩ : syracuseStep 1429889 = 1072417) B1072417
theorem B2150801 : Blo 952587 2150801 := bstep (se 2 (by rfl) ⟨806550, by rfl⟩ : syracuseStep 2150801 = 1613101) B1613101
theorem B1429907 : Blo 952587 1429907 := bstep (se 1 (by rfl) ⟨1072430, by rfl⟩ : syracuseStep 1429907 = 2144861) B2144861
theorem B2150819 : Blo 952587 2150819 := bstep (se 1 (by rfl) ⟨1613114, by rfl⟩ : syracuseStep 2150819 = 3226229) B3226229
theorem B1429937 : Blo 952587 1429937 := bstep (se 2 (by rfl) ⟨536226, by rfl⟩ : syracuseStep 1429937 = 1072453) B1072453
theorem B1429955 : Blo 952587 1429955 := bstep (se 1 (by rfl) ⟨1072466, by rfl⟩ : syracuseStep 1429955 = 2144933) B2144933
theorem B4641229 : Blo 952587 4641229 := bstep (se 3 (by rfl) ⟨870230, by rfl⟩ : syracuseStep 4641229 = 1740461) B1740461
theorem B1429985 : Blo 952587 1429985 := bstep (se 2 (by rfl) ⟨536244, by rfl⟩ : syracuseStep 1429985 = 1072489) B1072489
theorem B1430003 : Blo 952587 1430003 := bstep (se 1 (by rfl) ⟨1072502, by rfl⟩ : syracuseStep 1430003 = 2145005) B2145005
theorem B2904589 : Blo 952587 2904589 := bstep (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) B1089221
theorem B1430033 : Blo 952587 1430033 := bstep (se 2 (by rfl) ⟨536262, by rfl⟩ : syracuseStep 1430033 = 1072525) B1072525
theorem B2413091 : Blo 952587 2413091 := bstep (se 1 (by rfl) ⟨1809818, by rfl⟩ : syracuseStep 2413091 = 3619637) B3619637
theorem B1430051 : Blo 952587 1430051 := bstep (se 1 (by rfl) ⟨1072538, by rfl⟩ : syracuseStep 1430051 = 2145077) B2145077
theorem B1528355 : Blo 952587 1528355 := bstep (se 1 (by rfl) ⟨1146266, by rfl⟩ : syracuseStep 1528355 = 2292533) B2292533
theorem B1430081 : Blo 952587 1430081 := bstep (se 2 (by rfl) ⟨536280, by rfl⟩ : syracuseStep 1430081 = 1072561) B1072561
theorem B1430099 : Blo 952587 1430099 := bstep (se 1 (by rfl) ⟨1072574, by rfl⟩ : syracuseStep 1430099 = 2145149) B2145149
theorem B1430129 : Blo 952587 1430129 := bstep (se 2 (by rfl) ⟨536298, by rfl⟩ : syracuseStep 1430129 = 1072597) B1072597
theorem B1430147 : Blo 952587 1430147 := bstep (se 1 (by rfl) ⟨1072610, by rfl⟩ : syracuseStep 1430147 = 2145221) B2145221
theorem B1430177 : Blo 952587 1430177 := bstep (se 2 (by rfl) ⟨536316, by rfl⟩ : syracuseStep 1430177 = 1072633) B1072633
theorem B1528483 : Blo 952587 1528483 := bstep (se 1 (by rfl) ⟨1146362, by rfl⟩ : syracuseStep 1528483 = 2292725) B2292725
theorem B2151089 : Blo 952587 2151089 := bstep (se 2 (by rfl) ⟨806658, by rfl⟩ : syracuseStep 2151089 = 1613317) B1613317
theorem B1430195 : Blo 952587 1430195 := bstep (se 1 (by rfl) ⟨1072646, by rfl⟩ : syracuseStep 1430195 = 2145293) B2145293
theorem B2151107 : Blo 952587 2151107 := bstep (se 1 (by rfl) ⟨1613330, by rfl⟩ : syracuseStep 2151107 = 3226661) B3226661
theorem B1430225 : Blo 952587 1430225 := bstep (se 2 (by rfl) ⟨536334, by rfl⟩ : syracuseStep 1430225 = 1072669) B1072669
theorem B1430243 : Blo 952587 1430243 := bstep (se 1 (by rfl) ⟨1072682, by rfl⟩ : syracuseStep 1430243 = 2145365) B2145365
theorem B4838129 : Blo 952587 4838129 := bstep (se 2 (by rfl) ⟨1814298, by rfl⟩ : syracuseStep 4838129 = 3628597) B3628597
theorem B1430273 : Blo 952587 1430273 := bstep (se 2 (by rfl) ⟨536352, by rfl⟩ : syracuseStep 1430273 = 1072705) B1072705
theorem B1430291 : Blo 952587 1430291 := bstep (se 1 (by rfl) ⟨1072718, by rfl⟩ : syracuseStep 1430291 = 2145437) B2145437
theorem B1430321 : Blo 952587 1430321 := bstep (se 2 (by rfl) ⟨536370, by rfl⟩ : syracuseStep 1430321 = 1072741) B1072741
theorem B1430339 : Blo 952587 1430339 := bstep (se 1 (by rfl) ⟨1072754, by rfl⟩ : syracuseStep 1430339 = 2145509) B2145509
theorem B1430369 : Blo 952587 1430369 := bstep (se 2 (by rfl) ⟨536388, by rfl⟩ : syracuseStep 1430369 = 1072777) B1072777
theorem B1430387 : Blo 952587 1430387 := bstep (se 1 (by rfl) ⟨1072790, by rfl⟩ : syracuseStep 1430387 = 2145581) B2145581
theorem B1430417 : Blo 952587 1430417 := bstep (se 2 (by rfl) ⟨536406, by rfl⟩ : syracuseStep 1430417 = 1072813) B1072813
theorem B1430435 : Blo 952587 1430435 := bstep (se 1 (by rfl) ⟨1072826, by rfl⟩ : syracuseStep 1430435 = 2145653) B2145653
theorem B1430465 : Blo 952587 1430465 := bstep (se 2 (by rfl) ⟨536424, by rfl⟩ : syracuseStep 1430465 = 1072849) B1072849
theorem B1889219 : Blo 952587 1889219 := bstep (se 1 (by rfl) ⟨1416914, by rfl⟩ : syracuseStep 1889219 = 2833829) B2833829
theorem B2151377 : Blo 952587 2151377 := bstep (se 2 (by rfl) ⟨806766, by rfl⟩ : syracuseStep 2151377 = 1613533) B1613533
theorem B1430483 : Blo 952587 1430483 := bstep (se 1 (by rfl) ⟨1072862, by rfl⟩ : syracuseStep 1430483 = 2145725) B2145725
theorem B3625955 : Blo 952587 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B2151395 : Blo 952587 2151395 := bstep (se 1 (by rfl) ⟨1613546, by rfl⟩ : syracuseStep 2151395 = 3227093) B3227093
theorem B1430513 : Blo 952587 1430513 := bstep (se 2 (by rfl) ⟨536442, by rfl⟩ : syracuseStep 1430513 = 1072885) B1072885
theorem B1430531 : Blo 952587 1430531 := bstep (se 1 (by rfl) ⟨1072898, by rfl⟩ : syracuseStep 1430531 = 2145797) B2145797
theorem B1430561 : Blo 952587 1430561 := bstep (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) B1072921
theorem B1430579 : Blo 952587 1430579 := bstep (se 1 (by rfl) ⟨1072934, by rfl⟩ : syracuseStep 1430579 = 2145869) B2145869
theorem B1430609 : Blo 952587 1430609 := bstep (se 2 (by rfl) ⟨536478, by rfl⟩ : syracuseStep 1430609 = 1072957) B1072957
theorem B1430627 : Blo 952587 1430627 := bstep (se 1 (by rfl) ⟨1072970, by rfl⟩ : syracuseStep 1430627 = 2145941) B2145941
theorem B1430657 : Blo 952587 1430657 := bstep (se 2 (by rfl) ⟨536496, by rfl⟩ : syracuseStep 1430657 = 1072993) B1072993
theorem B1430675 : Blo 952587 1430675 := bstep (se 1 (by rfl) ⟨1073006, by rfl⟩ : syracuseStep 1430675 = 2146013) B2146013
theorem B1430705 : Blo 952587 1430705 := bstep (se 2 (by rfl) ⟨536514, by rfl⟩ : syracuseStep 1430705 = 1073029) B1073029
theorem B1430723 : Blo 952587 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B1430753 : Blo 952587 1430753 := bstep (se 2 (by rfl) ⟨536532, by rfl⟩ : syracuseStep 1430753 = 1073065) B1073065
theorem B4347121 : Blo 952587 4347121 := bstep (se 2 (by rfl) ⟨1630170, by rfl⟩ : syracuseStep 4347121 = 3260341) B3260341
theorem B2151665 : Blo 952587 2151665 := bstep (se 2 (by rfl) ⟨806874, by rfl⟩ : syracuseStep 2151665 = 1613749) B1613749
theorem B1430771 : Blo 952587 1430771 := bstep (se 1 (by rfl) ⟨1073078, by rfl⟩ : syracuseStep 1430771 = 2146157) B2146157
theorem B2151683 : Blo 952587 2151683 := bstep (se 1 (by rfl) ⟨1613762, by rfl⟩ : syracuseStep 2151683 = 3227525) B3227525
theorem B1430801 : Blo 952587 1430801 := bstep (se 2 (by rfl) ⟨536550, by rfl⟩ : syracuseStep 1430801 = 1073101) B1073101
theorem B1430819 : Blo 952587 1430819 := bstep (se 1 (by rfl) ⟨1073114, by rfl⟩ : syracuseStep 1430819 = 2146229) B2146229
theorem B1529123 : Blo 952587 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B2905379 : Blo 952587 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B1430849 : Blo 952587 1430849 := bstep (se 2 (by rfl) ⟨536568, by rfl⟩ : syracuseStep 1430849 = 1073137) B1073137
theorem B1430867 : Blo 952587 1430867 := bstep (se 1 (by rfl) ⟨1073150, by rfl⟩ : syracuseStep 1430867 = 2146301) B2146301
theorem B1430897 : Blo 952587 1430897 := bstep (se 2 (by rfl) ⟨536586, by rfl⟩ : syracuseStep 1430897 = 1073173) B1073173
theorem B1529201 : Blo 952587 1529201 := bstep (se 2 (by rfl) ⟨573450, by rfl⟩ : syracuseStep 1529201 = 1146901) B1146901
theorem B1430915 : Blo 952587 1430915 := bstep (se 1 (by rfl) ⟨1073186, by rfl⟩ : syracuseStep 1430915 = 2146373) B2146373
theorem B1430945 : Blo 952587 1430945 := bstep (se 2 (by rfl) ⟨536604, by rfl⟩ : syracuseStep 1430945 = 1073209) B1073209
theorem B1430963 : Blo 952587 1430963 := bstep (se 1 (by rfl) ⟨1073222, by rfl⟩ : syracuseStep 1430963 = 2146445) B2146445
theorem B2414033 : Blo 952587 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B1430993 : Blo 952587 1430993 := bstep (se 2 (by rfl) ⟨536622, by rfl⟩ : syracuseStep 1430993 = 1073245) B1073245
theorem B1431011 : Blo 952587 1431011 := bstep (se 1 (by rfl) ⟨1073258, by rfl⟩ : syracuseStep 1431011 = 2146517) B2146517
theorem B1431041 : Blo 952587 1431041 := bstep (se 2 (by rfl) ⟨536640, by rfl⟩ : syracuseStep 1431041 = 1073281) B1073281
theorem B2414083 : Blo 952587 2414083 := bstep (se 1 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 2414083 = 3621125) B3621125
theorem B2151953 : Blo 952587 2151953 := bstep (se 2 (by rfl) ⟨806982, by rfl⟩ : syracuseStep 2151953 = 1613965) B1613965
theorem B1431059 : Blo 952587 1431059 := bstep (se 1 (by rfl) ⟨1073294, by rfl⟩ : syracuseStep 1431059 = 2146589) B2146589
theorem B2151971 : Blo 952587 2151971 := bstep (se 1 (by rfl) ⟨1613978, by rfl⟩ : syracuseStep 2151971 = 3227957) B3227957
theorem B1431089 : Blo 952587 1431089 := bstep (se 2 (by rfl) ⟨536658, by rfl⟩ : syracuseStep 1431089 = 1073317) B1073317
theorem B1431107 : Blo 952587 1431107 := bstep (se 1 (by rfl) ⟨1073330, by rfl⟩ : syracuseStep 1431107 = 2146661) B2146661
theorem B1431137 : Blo 952587 1431137 := bstep (se 2 (by rfl) ⟨536676, by rfl⟩ : syracuseStep 1431137 = 1073353) B1073353
theorem B1431155 : Blo 952587 1431155 := bstep (se 1 (by rfl) ⟨1073366, by rfl⟩ : syracuseStep 1431155 = 2146733) B2146733
theorem B2578061 : Blo 952587 2578061 := bstep (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) B966773
theorem B2414225 : Blo 952587 2414225 := bstep (se 2 (by rfl) ⟨905334, by rfl⟩ : syracuseStep 2414225 = 1810669) B1810669
theorem B1431185 : Blo 952587 1431185 := bstep (se 2 (by rfl) ⟨536694, by rfl⟩ : syracuseStep 1431185 = 1073389) B1073389
theorem B1431203 : Blo 952587 1431203 := bstep (se 1 (by rfl) ⟨1073402, by rfl⟩ : syracuseStep 1431203 = 2146805) B2146805
theorem B1431233 : Blo 952587 1431233 := bstep (se 2 (by rfl) ⟨536712, by rfl⟩ : syracuseStep 1431233 = 1073425) B1073425
theorem B4085453 : Blo 952587 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B1431251 : Blo 952587 1431251 := bstep (se 1 (by rfl) ⟨1073438, by rfl⟩ : syracuseStep 1431251 = 2146877) B2146877
theorem B1431281 : Blo 952587 1431281 := bstep (se 2 (by rfl) ⟨536730, by rfl⟩ : syracuseStep 1431281 = 1073461) B1073461
theorem B1529585 : Blo 952587 1529585 := bstep (se 2 (by rfl) ⟨573594, by rfl⟩ : syracuseStep 1529585 = 1147189) B1147189
theorem B1431299 : Blo 952587 1431299 := bstep (se 1 (by rfl) ⟨1073474, by rfl⟩ : syracuseStep 1431299 = 2146949) B2146949
theorem B2578193 : Blo 952587 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B1431329 : Blo 952587 1431329 := bstep (se 2 (by rfl) ⟨536748, by rfl⟩ : syracuseStep 1431329 = 1073497) B1073497
theorem B2152241 : Blo 952587 2152241 := bstep (se 2 (by rfl) ⟨807090, by rfl⟩ : syracuseStep 2152241 = 1614181) B1614181
theorem B1431347 : Blo 952587 1431347 := bstep (se 1 (by rfl) ⟨1073510, by rfl⟩ : syracuseStep 1431347 = 2147021) B2147021
theorem B2152259 : Blo 952587 2152259 := bstep (se 1 (by rfl) ⟨1614194, by rfl⟩ : syracuseStep 2152259 = 3228389) B3228389
theorem B1431377 : Blo 952587 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B1431395 : Blo 952587 1431395 := bstep (se 1 (by rfl) ⟨1073546, by rfl⟩ : syracuseStep 1431395 = 2147093) B2147093
theorem B1529713 : Blo 952587 1529713 := bstep (se 2 (by rfl) ⟨573642, by rfl⟩ : syracuseStep 1529713 = 1147285) B1147285
theorem B1431425 : Blo 952587 1431425 := bstep (se 2 (by rfl) ⟨536784, by rfl⟩ : syracuseStep 1431425 = 1073569) B1073569
theorem B12244877 : Blo 952587 12244877 := bstep (se 3 (by rfl) ⟨2295914, by rfl⟩ : syracuseStep 12244877 = 4591829) B4591829
theorem B1431443 : Blo 952587 1431443 := bstep (se 1 (by rfl) ⟨1073582, by rfl⟩ : syracuseStep 1431443 = 2147165) B2147165
theorem B1431473 : Blo 952587 1431473 := bstep (se 2 (by rfl) ⟨536802, by rfl⟩ : syracuseStep 1431473 = 1073605) B1073605
theorem B1431491 : Blo 952587 1431491 := bstep (se 1 (by rfl) ⟨1073618, by rfl⟩ : syracuseStep 1431491 = 2147237) B2147237
theorem B35739589 : Blo 952587 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B3626957 : Blo 952587 3626957 := bstep (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) B1360109
theorem B1431521 : Blo 952587 1431521 := bstep (se 2 (by rfl) ⟨536820, by rfl⟩ : syracuseStep 1431521 = 1073641) B1073641
theorem B1431539 : Blo 952587 1431539 := bstep (se 1 (by rfl) ⟨1073654, by rfl⟩ : syracuseStep 1431539 = 2147309) B2147309
theorem B1431569 : Blo 952587 1431569 := bstep (se 2 (by rfl) ⟨536838, by rfl⟩ : syracuseStep 1431569 = 1073677) B1073677
theorem B1431587 : Blo 952587 1431587 := bstep (se 1 (by rfl) ⟨1073690, by rfl⟩ : syracuseStep 1431587 = 2147381) B2147381
theorem B4085795 : Blo 952587 4085795 := bstep (se 1 (by rfl) ⟨3064346, by rfl⟩ : syracuseStep 4085795 = 6128693) B6128693
theorem B1431617 : Blo 952587 1431617 := bstep (se 2 (by rfl) ⟨536856, by rfl⟩ : syracuseStep 1431617 = 1073713) B1073713
theorem B1431635 : Blo 952587 1431635 := bstep (se 1 (by rfl) ⟨1073726, by rfl⟩ : syracuseStep 1431635 = 2147453) B2147453
theorem B1431665 : Blo 952587 1431665 := bstep (se 2 (by rfl) ⟨536874, by rfl⟩ : syracuseStep 1431665 = 1073749) B1073749
theorem B1431683 : Blo 952587 1431683 := bstep (se 1 (by rfl) ⟨1073762, by rfl⟩ : syracuseStep 1431683 = 2147525) B2147525
theorem B1431713 : Blo 952587 1431713 := bstep (se 2 (by rfl) ⟨536892, by rfl⟩ : syracuseStep 1431713 = 1073785) B1073785
theorem B4839587 : Blo 952587 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B1431731 : Blo 952587 1431731 := bstep (se 1 (by rfl) ⟨1073798, by rfl⟩ : syracuseStep 1431731 = 2147597) B2147597
theorem B1431761 : Blo 952587 1431761 := bstep (se 2 (by rfl) ⟨536910, by rfl⟩ : syracuseStep 1431761 = 1073821) B1073821
theorem B1431779 : Blo 952587 1431779 := bstep (se 1 (by rfl) ⟨1073834, by rfl⟩ : syracuseStep 1431779 = 2147669) B2147669
theorem B1431809 : Blo 952587 1431809 := bstep (se 2 (by rfl) ⟨536928, by rfl⟩ : syracuseStep 1431809 = 1073857) B1073857
theorem B1431827 : Blo 952587 1431827 := bstep (se 1 (by rfl) ⟨1073870, by rfl⟩ : syracuseStep 1431827 = 2147741) B2147741
theorem B1431857 : Blo 952587 1431857 := bstep (se 2 (by rfl) ⟨536946, by rfl⟩ : syracuseStep 1431857 = 1073893) B1073893
theorem B1431875 : Blo 952587 1431875 := bstep (se 1 (by rfl) ⟨1073906, by rfl⟩ : syracuseStep 1431875 = 2147813) B2147813
theorem B1431905 : Blo 952587 1431905 := bstep (se 2 (by rfl) ⟨536964, by rfl⟩ : syracuseStep 1431905 = 1073929) B1073929
theorem B1431923 : Blo 952587 1431923 := bstep (se 1 (by rfl) ⟨1073942, by rfl⟩ : syracuseStep 1431923 = 2147885) B2147885
theorem B1431953 : Blo 952587 1431953 := bstep (se 2 (by rfl) ⟨536982, by rfl⟩ : syracuseStep 1431953 = 1073965) B1073965
theorem B1431971 : Blo 952587 1431971 := bstep (se 1 (by rfl) ⟨1073978, by rfl⟩ : syracuseStep 1431971 = 2147957) B2147957
theorem B1432001 : Blo 952587 1432001 := bstep (se 2 (by rfl) ⟨537000, by rfl⟩ : syracuseStep 1432001 = 1074001) B1074001
theorem B2578883 : Blo 952587 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B1432019 : Blo 952587 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B1432049 : Blo 952587 1432049 := bstep (se 2 (by rfl) ⟨537018, by rfl⟩ : syracuseStep 1432049 = 1074037) B1074037
theorem B1432067 : Blo 952587 1432067 := bstep (se 1 (by rfl) ⟨1074050, by rfl⟩ : syracuseStep 1432067 = 2148101) B2148101
theorem B1432097 : Blo 952587 1432097 := bstep (se 2 (by rfl) ⟨537036, by rfl⟩ : syracuseStep 1432097 = 1074073) B1074073
theorem B1432115 : Blo 952587 1432115 := bstep (se 1 (by rfl) ⟨1074086, by rfl⟩ : syracuseStep 1432115 = 2148173) B2148173
theorem B1432145 : Blo 952587 1432145 := bstep (se 2 (by rfl) ⟨537054, by rfl⟩ : syracuseStep 1432145 = 1074109) B1074109
theorem B1071715 : Blo 952587 1071715 := bstep (se 1 (by rfl) ⟨803786, by rfl⟩ : syracuseStep 1071715 = 1607573) B1607573
theorem B1432163 : Blo 952587 1432163 := bstep (se 1 (by rfl) ⟨1074122, by rfl⟩ : syracuseStep 1432163 = 2148245) B2148245
theorem B2415217 : Blo 952587 2415217 := bstep (se 2 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 2415217 = 1811413) B1811413
theorem B1432193 : Blo 952587 1432193 := bstep (se 2 (by rfl) ⟨537072, by rfl⟩ : syracuseStep 1432193 = 1074145) B1074145
theorem B10869389 : Blo 952587 10869389 := bstep (se 3 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 10869389 = 4076021) B4076021
theorem B1432211 : Blo 952587 1432211 := bstep (se 1 (by rfl) ⟨1074158, by rfl⟩ : syracuseStep 1432211 = 2148317) B2148317
theorem B4348579 : Blo 952587 4348579 := bstep (se 1 (by rfl) ⟨3261434, by rfl⟩ : syracuseStep 4348579 = 6522869) B6522869
theorem B1432241 : Blo 952587 1432241 := bstep (se 2 (by rfl) ⟨537090, by rfl⟩ : syracuseStep 1432241 = 1074181) B1074181
theorem B1432259 : Blo 952587 1432259 := bstep (se 1 (by rfl) ⟨1074194, by rfl⟩ : syracuseStep 1432259 = 2148389) B2148389
theorem B1432289 : Blo 952587 1432289 := bstep (se 2 (by rfl) ⟨537108, by rfl⟩ : syracuseStep 1432289 = 1074217) B1074217
theorem B1071859 : Blo 952587 1071859 := bstep (se 1 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 1071859 = 1607789) B1607789
theorem B1432307 : Blo 952587 1432307 := bstep (se 1 (by rfl) ⟨1074230, by rfl⟩ : syracuseStep 1432307 = 2148461) B2148461
theorem B1432337 : Blo 952587 1432337 := bstep (se 2 (by rfl) ⟨537126, by rfl⟩ : syracuseStep 1432337 = 1074253) B1074253
theorem B1432355 : Blo 952587 1432355 := bstep (se 1 (by rfl) ⟨1074266, by rfl⟩ : syracuseStep 1432355 = 2148533) B2148533
theorem B1432385 : Blo 952587 1432385 := bstep (se 2 (by rfl) ⟨537144, by rfl⟩ : syracuseStep 1432385 = 1074289) B1074289
theorem B1432403 : Blo 952587 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B1432433 : Blo 952587 1432433 := bstep (se 2 (by rfl) ⟨537162, by rfl⟩ : syracuseStep 1432433 = 1074325) B1074325
theorem B1072003 : Blo 952587 1072003 := bstep (se 1 (by rfl) ⟨804002, by rfl⟩ : syracuseStep 1072003 = 1608005) B1608005
theorem B2415491 : Blo 952587 2415491 := bstep (se 1 (by rfl) ⟨1811618, by rfl⟩ : syracuseStep 2415491 = 3623237) B3623237
theorem B1432451 : Blo 952587 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1432481 : Blo 952587 1432481 := bstep (se 2 (by rfl) ⟨537180, by rfl⟩ : syracuseStep 1432481 = 1074361) B1074361
theorem B1432499 : Blo 952587 1432499 := bstep (se 1 (by rfl) ⟨1074374, by rfl⟩ : syracuseStep 1432499 = 2148749) B2148749
theorem B4840397 : Blo 952587 4840397 := bstep (se 3 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 4840397 = 1815149) B1815149
theorem B1432529 : Blo 952587 1432529 := bstep (se 2 (by rfl) ⟨537198, by rfl⟩ : syracuseStep 1432529 = 1074397) B1074397
theorem B1432547 : Blo 952587 1432547 := bstep (se 1 (by rfl) ⟨1074410, by rfl⟩ : syracuseStep 1432547 = 2148821) B2148821
theorem B1432577 : Blo 952587 1432577 := bstep (se 2 (by rfl) ⟨537216, by rfl⟩ : syracuseStep 1432577 = 1074433) B1074433
theorem B1072147 : Blo 952587 1072147 := bstep (se 1 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 1072147 = 1608221) B1608221
theorem B1432595 : Blo 952587 1432595 := bstep (se 1 (by rfl) ⟨1074446, by rfl⟩ : syracuseStep 1432595 = 2148893) B2148893
theorem B1432625 : Blo 952587 1432625 := bstep (se 2 (by rfl) ⟨537234, by rfl⟩ : syracuseStep 1432625 = 1074469) B1074469
theorem B12213301 : Blo 952587 12213301 := bstep (se 5 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 12213301 = 1144997) B1144997
theorem B2415683 : Blo 952587 2415683 := bstep (se 1 (by rfl) ⟨1811762, by rfl⟩ : syracuseStep 2415683 = 3623525) B3623525
theorem B1432643 : Blo 952587 1432643 := bstep (se 1 (by rfl) ⟨1074482, by rfl⟩ : syracuseStep 1432643 = 2148965) B2148965
theorem B1432673 : Blo 952587 1432673 := bstep (se 2 (by rfl) ⟨537252, by rfl⟩ : syracuseStep 1432673 = 1074505) B1074505
theorem B8150129 : Blo 952587 8150129 := bstep (se 2 (by rfl) ⟨3056298, by rfl⟩ : syracuseStep 8150129 = 6112597) B6112597
theorem B1432691 : Blo 952587 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B14670989 : Blo 952587 14670989 := bstep (se 3 (by rfl) ⟨2750810, by rfl⟩ : syracuseStep 14670989 = 5501621) B5501621
theorem B1432721 : Blo 952587 1432721 := bstep (se 2 (by rfl) ⟨537270, by rfl⟩ : syracuseStep 1432721 = 1074541) B1074541
theorem B1072291 : Blo 952587 1072291 := bstep (se 1 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 1072291 = 1608437) B1608437
theorem B1432739 : Blo 952587 1432739 := bstep (se 1 (by rfl) ⟨1074554, by rfl⟩ : syracuseStep 1432739 = 2149109) B2149109
theorem B1432769 : Blo 952587 1432769 := bstep (se 2 (by rfl) ⟨537288, by rfl⟩ : syracuseStep 1432769 = 1074577) B1074577
theorem B1432787 : Blo 952587 1432787 := bstep (se 1 (by rfl) ⟨1074590, by rfl⟩ : syracuseStep 1432787 = 2149181) B2149181
theorem B1432817 : Blo 952587 1432817 := bstep (se 2 (by rfl) ⟨537306, by rfl⟩ : syracuseStep 1432817 = 1074613) B1074613
theorem B1432835 : Blo 952587 1432835 := bstep (se 1 (by rfl) ⟨1074626, by rfl⟩ : syracuseStep 1432835 = 2149253) B2149253
theorem B1432865 : Blo 952587 1432865 := bstep (se 2 (by rfl) ⟨537324, by rfl⟩ : syracuseStep 1432865 = 1074649) B1074649
theorem B1072435 : Blo 952587 1072435 := bstep (se 1 (by rfl) ⟨804326, by rfl⟩ : syracuseStep 1072435 = 1608653) B1608653
theorem B1432883 : Blo 952587 1432883 := bstep (se 1 (by rfl) ⟨1074662, by rfl⟩ : syracuseStep 1432883 = 2149325) B2149325
theorem B1432913 : Blo 952587 1432913 := bstep (se 2 (by rfl) ⟨537342, by rfl⟩ : syracuseStep 1432913 = 1074685) B1074685
theorem B1531219 : Blo 952587 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B1432931 : Blo 952587 1432931 := bstep (se 1 (by rfl) ⟨1074698, by rfl⟩ : syracuseStep 1432931 = 2149397) B2149397
theorem B19619185 : Blo 952587 19619185 := bstep (se 2 (by rfl) ⟨7357194, by rfl⟩ : syracuseStep 19619185 = 14714389) B14714389
theorem B1432961 : Blo 952587 1432961 := bstep (se 2 (by rfl) ⟨537360, by rfl⟩ : syracuseStep 1432961 = 1074721) B1074721
theorem B1432979 : Blo 952587 1432979 := bstep (se 1 (by rfl) ⟨1074734, by rfl⟩ : syracuseStep 1432979 = 2149469) B2149469
theorem B1433009 : Blo 952587 1433009 := bstep (se 2 (by rfl) ⟨537378, by rfl⟩ : syracuseStep 1433009 = 1074757) B1074757
theorem B1072579 : Blo 952587 1072579 := bstep (se 1 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 1072579 = 1608869) B1608869
theorem B1433027 : Blo 952587 1433027 := bstep (se 1 (by rfl) ⟨1074770, by rfl⟩ : syracuseStep 1433027 = 2149541) B2149541
theorem B1433057 : Blo 952587 1433057 := bstep (se 2 (by rfl) ⟨537396, by rfl⟩ : syracuseStep 1433057 = 1074793) B1074793
theorem B1433075 : Blo 952587 1433075 := bstep (se 1 (by rfl) ⟨1074806, by rfl⟩ : syracuseStep 1433075 = 2149613) B2149613
theorem B1433105 : Blo 952587 1433105 := bstep (se 2 (by rfl) ⟨537414, by rfl⟩ : syracuseStep 1433105 = 1074829) B1074829
theorem B1433123 : Blo 952587 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1433153 : Blo 952587 1433153 := bstep (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) B1074865
theorem B5103173 : Blo 952587 5103173 := bstep (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) B956845
theorem B1072723 : Blo 952587 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B1433171 : Blo 952587 1433171 := bstep (se 1 (by rfl) ⟨1074878, by rfl⟩ : syracuseStep 1433171 = 2149757) B2149757
theorem B1433201 : Blo 952587 1433201 := bstep (se 2 (by rfl) ⟨537450, by rfl⟩ : syracuseStep 1433201 = 1074901) B1074901
theorem B1433219 : Blo 952587 1433219 := bstep (se 1 (by rfl) ⟨1074914, by rfl⟩ : syracuseStep 1433219 = 2149829) B2149829
theorem B1433249 : Blo 952587 1433249 := bstep (se 2 (by rfl) ⟨537468, by rfl⟩ : syracuseStep 1433249 = 1074937) B1074937
theorem B1433267 : Blo 952587 1433267 := bstep (se 1 (by rfl) ⟨1074950, by rfl⟩ : syracuseStep 1433267 = 2149901) B2149901
theorem B1433297 : Blo 952587 1433297 := bstep (se 2 (by rfl) ⟨537486, by rfl⟩ : syracuseStep 1433297 = 1074973) B1074973
theorem B1072867 : Blo 952587 1072867 := bstep (se 1 (by rfl) ⟨804650, by rfl⟩ : syracuseStep 1072867 = 1609301) B1609301
theorem B1433315 : Blo 952587 1433315 := bstep (se 1 (by rfl) ⟨1074986, by rfl⟩ : syracuseStep 1433315 = 2149973) B2149973
theorem B1433345 : Blo 952587 1433345 := bstep (se 2 (by rfl) ⟨537504, by rfl⟩ : syracuseStep 1433345 = 1075009) B1075009
theorem B1433363 : Blo 952587 1433363 := bstep (se 1 (by rfl) ⟨1075022, by rfl⟩ : syracuseStep 1433363 = 2150045) B2150045
theorem B1433393 : Blo 952587 1433393 := bstep (se 2 (by rfl) ⟨537522, by rfl⟩ : syracuseStep 1433393 = 1075045) B1075045
theorem B1433411 : Blo 952587 1433411 := bstep (se 1 (by rfl) ⟨1075058, by rfl⟩ : syracuseStep 1433411 = 2150117) B2150117
theorem B1433441 : Blo 952587 1433441 := bstep (se 2 (by rfl) ⟨537540, by rfl⟩ : syracuseStep 1433441 = 1075081) B1075081
theorem B1073011 : Blo 952587 1073011 := bstep (se 1 (by rfl) ⟨804758, by rfl⟩ : syracuseStep 1073011 = 1609517) B1609517
theorem B1433459 : Blo 952587 1433459 := bstep (se 1 (by rfl) ⟨1075094, by rfl⟩ : syracuseStep 1433459 = 2150189) B2150189
theorem B1433489 : Blo 952587 1433489 := bstep (se 2 (by rfl) ⟨537558, by rfl⟩ : syracuseStep 1433489 = 1075117) B1075117
theorem B1433507 : Blo 952587 1433507 := bstep (se 1 (by rfl) ⟨1075130, by rfl⟩ : syracuseStep 1433507 = 2150261) B2150261
theorem B1433537 : Blo 952587 1433537 := bstep (se 2 (by rfl) ⟨537576, by rfl⟩ : syracuseStep 1433537 = 1075153) B1075153
theorem B1433555 : Blo 952587 1433555 := bstep (se 1 (by rfl) ⟨1075166, by rfl⟩ : syracuseStep 1433555 = 2150333) B2150333
theorem B2416625 : Blo 952587 2416625 := bstep (se 2 (by rfl) ⟨906234, by rfl⟩ : syracuseStep 2416625 = 1812469) B1812469
theorem B1433585 : Blo 952587 1433585 := bstep (se 2 (by rfl) ⟨537594, by rfl⟩ : syracuseStep 1433585 = 1075189) B1075189
theorem B1531891 : Blo 952587 1531891 := bstep (se 1 (by rfl) ⟨1148918, by rfl⟩ : syracuseStep 1531891 = 2297837) B2297837
theorem B1073155 : Blo 952587 1073155 := bstep (se 1 (by rfl) ⟨804866, by rfl⟩ : syracuseStep 1073155 = 1609733) B1609733
theorem B1433603 : Blo 952587 1433603 := bstep (se 1 (by rfl) ⟨1075202, by rfl⟩ : syracuseStep 1433603 = 2150405) B2150405
theorem B3629069 : Blo 952587 3629069 := bstep (se 3 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 3629069 = 1360901) B1360901
theorem B1433633 : Blo 952587 1433633 := bstep (se 2 (by rfl) ⟨537612, by rfl⟩ : syracuseStep 1433633 = 1075225) B1075225
theorem B2416675 : Blo 952587 2416675 := bstep (se 1 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 2416675 = 3625013) B3625013
theorem B1433651 : Blo 952587 1433651 := bstep (se 1 (by rfl) ⟨1075238, by rfl⟩ : syracuseStep 1433651 = 2150477) B2150477
theorem B1859651 : Blo 952587 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B1433681 : Blo 952587 1433681 := bstep (se 2 (by rfl) ⟨537630, by rfl⟩ : syracuseStep 1433681 = 1075261) B1075261
theorem B83845205 : Blo 952587 83845205 := bstep (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) B982561
theorem B1433699 : Blo 952587 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B1433729 : Blo 952587 1433729 := bstep (se 2 (by rfl) ⟨537648, by rfl⟩ : syracuseStep 1433729 = 1075297) B1075297
theorem B1073299 : Blo 952587 1073299 := bstep (se 1 (by rfl) ⟨804974, by rfl⟩ : syracuseStep 1073299 = 1609949) B1609949
theorem B1433747 : Blo 952587 1433747 := bstep (se 1 (by rfl) ⟨1075310, by rfl⟩ : syracuseStep 1433747 = 2150621) B2150621
theorem B2416817 : Blo 952587 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B1433777 : Blo 952587 1433777 := bstep (se 2 (by rfl) ⟨537666, by rfl⟩ : syracuseStep 1433777 = 1075333) B1075333
theorem B1433795 : Blo 952587 1433795 := bstep (se 1 (by rfl) ⟨1075346, by rfl⟩ : syracuseStep 1433795 = 2150693) B2150693
theorem B6119621 : Blo 952587 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B1433825 : Blo 952587 1433825 := bstep (se 2 (by rfl) ⟨537684, by rfl⟩ : syracuseStep 1433825 = 1075369) B1075369
theorem B1433843 : Blo 952587 1433843 := bstep (se 1 (by rfl) ⟨1075382, by rfl⟩ : syracuseStep 1433843 = 2150765) B2150765
theorem B1433873 : Blo 952587 1433873 := bstep (se 2 (by rfl) ⟨537702, by rfl⟩ : syracuseStep 1433873 = 1075405) B1075405
theorem B1073443 : Blo 952587 1073443 := bstep (se 1 (by rfl) ⟨805082, by rfl⟩ : syracuseStep 1073443 = 1610165) B1610165
theorem B1433891 : Blo 952587 1433891 := bstep (se 1 (by rfl) ⟨1075418, by rfl⟩ : syracuseStep 1433891 = 2150837) B2150837
theorem B1433921 : Blo 952587 1433921 := bstep (se 2 (by rfl) ⟨537720, by rfl⟩ : syracuseStep 1433921 = 1075441) B1075441
theorem B1433939 : Blo 952587 1433939 := bstep (se 1 (by rfl) ⟨1075454, by rfl⟩ : syracuseStep 1433939 = 2150909) B2150909
theorem B1433969 : Blo 952587 1433969 := bstep (se 2 (by rfl) ⟨537738, by rfl⟩ : syracuseStep 1433969 = 1075477) B1075477
theorem B1433987 : Blo 952587 1433987 := bstep (se 1 (by rfl) ⟨1075490, by rfl⟩ : syracuseStep 1433987 = 2150981) B2150981
theorem B1434017 : Blo 952587 1434017 := bstep (se 2 (by rfl) ⟨537756, by rfl⟩ : syracuseStep 1434017 = 1075513) B1075513
theorem B1073587 : Blo 952587 1073587 := bstep (se 1 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 1073587 = 1610381) B1610381
theorem B1434035 : Blo 952587 1434035 := bstep (se 1 (by rfl) ⟨1075526, by rfl⟩ : syracuseStep 1434035 = 2151053) B2151053
theorem B1434065 : Blo 952587 1434065 := bstep (se 2 (by rfl) ⟨537774, by rfl⟩ : syracuseStep 1434065 = 1075549) B1075549
theorem B1434083 : Blo 952587 1434083 := bstep (se 1 (by rfl) ⟨1075562, by rfl⟩ : syracuseStep 1434083 = 2151125) B2151125
theorem B1434113 : Blo 952587 1434113 := bstep (se 2 (by rfl) ⟨537792, by rfl⟩ : syracuseStep 1434113 = 1075585) B1075585
theorem B1434131 : Blo 952587 1434131 := bstep (se 1 (by rfl) ⟨1075598, by rfl⟩ : syracuseStep 1434131 = 2151197) B2151197
theorem B1434161 : Blo 952587 1434161 := bstep (se 2 (by rfl) ⟨537810, by rfl⟩ : syracuseStep 1434161 = 1075621) B1075621
theorem B1073731 : Blo 952587 1073731 := bstep (se 1 (by rfl) ⟨805298, by rfl⟩ : syracuseStep 1073731 = 1610597) B1610597
theorem B1434179 : Blo 952587 1434179 := bstep (se 1 (by rfl) ⟨1075634, by rfl⟩ : syracuseStep 1434179 = 2151269) B2151269
theorem B1434209 : Blo 952587 1434209 := bstep (se 2 (by rfl) ⟨537828, by rfl⟩ : syracuseStep 1434209 = 1075657) B1075657
theorem B7070321 : Blo 952587 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B1434227 : Blo 952587 1434227 := bstep (se 1 (by rfl) ⟨1075670, by rfl⟩ : syracuseStep 1434227 = 2151341) B2151341
theorem B1434257 : Blo 952587 1434257 := bstep (se 2 (by rfl) ⟨537846, by rfl⟩ : syracuseStep 1434257 = 1075693) B1075693
theorem B1434275 : Blo 952587 1434275 := bstep (se 1 (by rfl) ⟨1075706, by rfl⟩ : syracuseStep 1434275 = 2151413) B2151413
theorem B1434305 : Blo 952587 1434305 := bstep (se 2 (by rfl) ⟨537864, by rfl⟩ : syracuseStep 1434305 = 1075729) B1075729
theorem B1073875 : Blo 952587 1073875 := bstep (se 1 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 1073875 = 1610813) B1610813
theorem B1434323 : Blo 952587 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1434353 : Blo 952587 1434353 := bstep (se 2 (by rfl) ⟨537882, by rfl⟩ : syracuseStep 1434353 = 1075765) B1075765
theorem B1434371 : Blo 952587 1434371 := bstep (se 1 (by rfl) ⟨1075778, by rfl⟩ : syracuseStep 1434371 = 2151557) B2151557
theorem B1434401 : Blo 952587 1434401 := bstep (se 2 (by rfl) ⟨537900, by rfl⟩ : syracuseStep 1434401 = 1075801) B1075801
theorem B3629873 : Blo 952587 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1434419 : Blo 952587 1434419 := bstep (se 1 (by rfl) ⟨1075814, by rfl⟩ : syracuseStep 1434419 = 2151629) B2151629
theorem B2941763 : Blo 952587 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1434449 : Blo 952587 1434449 := bstep (se 2 (by rfl) ⟨537918, by rfl⟩ : syracuseStep 1434449 = 1075837) B1075837
theorem B1631075 : Blo 952587 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1074019 : Blo 952587 1074019 := bstep (se 1 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 1074019 = 1611029) B1611029
theorem B1434467 : Blo 952587 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B1434497 : Blo 952587 1434497 := bstep (se 2 (by rfl) ⟨537936, by rfl⟩ : syracuseStep 1434497 = 1075873) B1075873
theorem B1434515 : Blo 952587 1434515 := bstep (se 1 (by rfl) ⟨1075886, by rfl⟩ : syracuseStep 1434515 = 2151773) B2151773
theorem B1434545 : Blo 952587 1434545 := bstep (se 2 (by rfl) ⟨537954, by rfl⟩ : syracuseStep 1434545 = 1075909) B1075909
theorem B1434563 : Blo 952587 1434563 := bstep (se 1 (by rfl) ⟨1075922, by rfl⟩ : syracuseStep 1434563 = 2151845) B2151845
theorem B1434593 : Blo 952587 1434593 := bstep (se 2 (by rfl) ⟨537972, by rfl⟩ : syracuseStep 1434593 = 1075945) B1075945
theorem B1074163 : Blo 952587 1074163 := bstep (se 1 (by rfl) ⟨805622, by rfl⟩ : syracuseStep 1074163 = 1611245) B1611245
theorem B1434611 : Blo 952587 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B1434641 : Blo 952587 1434641 := bstep (se 2 (by rfl) ⟨537990, by rfl⟩ : syracuseStep 1434641 = 1075981) B1075981
theorem B1434659 : Blo 952587 1434659 := bstep (se 1 (by rfl) ⟨1075994, by rfl⟩ : syracuseStep 1434659 = 2151989) B2151989
theorem B1434689 : Blo 952587 1434689 := bstep (se 2 (by rfl) ⟨538008, by rfl⟩ : syracuseStep 1434689 = 1076017) B1076017
theorem B1434707 : Blo 952587 1434707 := bstep (se 1 (by rfl) ⟨1076030, by rfl⟩ : syracuseStep 1434707 = 2152061) B2152061
theorem B1434737 : Blo 952587 1434737 := bstep (se 2 (by rfl) ⟨538026, by rfl⟩ : syracuseStep 1434737 = 1076053) B1076053
theorem B1074307 : Blo 952587 1074307 := bstep (se 1 (by rfl) ⟨805730, by rfl⟩ : syracuseStep 1074307 = 1611461) B1611461
theorem B1434755 : Blo 952587 1434755 := bstep (se 1 (by rfl) ⟨1076066, by rfl⟩ : syracuseStep 1434755 = 2152133) B2152133
theorem B2417809 : Blo 952587 2417809 := bstep (se 2 (by rfl) ⟨906678, by rfl⟩ : syracuseStep 2417809 = 1813357) B1813357
theorem B1434785 : Blo 952587 1434785 := bstep (se 2 (by rfl) ⟨538044, by rfl⟩ : syracuseStep 1434785 = 1076089) B1076089
theorem B1434803 : Blo 952587 1434803 := bstep (se 1 (by rfl) ⟨1076102, by rfl⟩ : syracuseStep 1434803 = 2152205) B2152205
theorem B1434833 : Blo 952587 1434833 := bstep (se 2 (by rfl) ⟨538062, by rfl⟩ : syracuseStep 1434833 = 1076125) B1076125
theorem B1434851 : Blo 952587 1434851 := bstep (se 1 (by rfl) ⟨1076138, by rfl⟩ : syracuseStep 1434851 = 2152277) B2152277
theorem B1434881 : Blo 952587 1434881 := bstep (se 2 (by rfl) ⟨538080, by rfl⟩ : syracuseStep 1434881 = 1076161) B1076161
theorem B1074451 : Blo 952587 1074451 := bstep (se 1 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 1074451 = 1611677) B1611677
theorem B1074595 : Blo 952587 1074595 := bstep (se 1 (by rfl) ⟨805946, by rfl⟩ : syracuseStep 1074595 = 1611893) B1611893
theorem B2418083 : Blo 952587 2418083 := bstep (se 1 (by rfl) ⟨1813562, by rfl⟩ : syracuseStep 2418083 = 3627125) B3627125
theorem B3630541 : Blo 952587 3630541 := bstep (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) B1361453
theorem B16508387 : Blo 952587 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B10872305 : Blo 952587 10872305 := bstep (se 2 (by rfl) ⟨4077114, by rfl⟩ : syracuseStep 10872305 = 8154229) B8154229
theorem B8152589 : Blo 952587 8152589 := bstep (se 3 (by rfl) ⟨1528610, by rfl⟩ : syracuseStep 8152589 = 3057221) B3057221
theorem B1074739 : Blo 952587 1074739 := bstep (se 1 (by rfl) ⟨806054, by rfl⟩ : syracuseStep 1074739 = 1612109) B1612109
theorem B2418275 : Blo 952587 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B1205923 : Blo 952587 1205923 := bstep (se 1 (by rfl) ⟨904442, by rfl⟩ : syracuseStep 1205923 = 1808885) B1808885
theorem B1074883 : Blo 952587 1074883 := bstep (se 1 (by rfl) ⟨806162, by rfl⟩ : syracuseStep 1074883 = 1612325) B1612325
theorem B1206019 : Blo 952587 1206019 := bstep (se 1 (by rfl) ⟨904514, by rfl⟩ : syracuseStep 1206019 = 1809029) B1809029
theorem B5433101 : Blo 952587 5433101 := bstep (se 3 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 5433101 = 2037413) B2037413
theorem B5170979 : Blo 952587 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B1075027 : Blo 952587 1075027 := bstep (se 1 (by rfl) ⟨806270, by rfl⟩ : syracuseStep 1075027 = 1612541) B1612541
theorem B2713475 : Blo 952587 2713475 := bstep (se 1 (by rfl) ⟨2035106, by rfl⟩ : syracuseStep 2713475 = 4070213) B4070213
theorem B1632209 : Blo 952587 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B1075171 : Blo 952587 1075171 := bstep (se 1 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 1075171 = 1612757) B1612757
theorem B1075315 : Blo 952587 1075315 := bstep (se 1 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 1075315 = 1612973) B1612973
theorem B3631331 : Blo 952587 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B1206515 : Blo 952587 1206515 := bstep (se 1 (by rfl) ⟨904886, by rfl⟩ : syracuseStep 1206515 = 1809773) B1809773
theorem B1075459 : Blo 952587 1075459 := bstep (se 1 (by rfl) ⟨806594, by rfl⟩ : syracuseStep 1075459 = 1613189) B1613189
theorem B6875405 : Blo 952587 6875405 := bstep (se 3 (by rfl) ⟨1289138, by rfl⟩ : syracuseStep 6875405 = 2578277) B2578277
theorem B10316045 : Blo 952587 10316045 := bstep (se 3 (by rfl) ⟨1934258, by rfl⟩ : syracuseStep 10316045 = 3868517) B3868517
theorem B1075603 : Blo 952587 1075603 := bstep (se 1 (by rfl) ⟨806702, by rfl⟩ : syracuseStep 1075603 = 1613405) B1613405
theorem B2419217 : Blo 952587 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B1075747 : Blo 952587 1075747 := bstep (se 1 (by rfl) ⟨806810, by rfl⟩ : syracuseStep 1075747 = 1613621) B1613621
theorem B2419267 : Blo 952587 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B1632881 : Blo 952587 1632881 := bstep (se 2 (by rfl) ⟨612330, by rfl⟩ : syracuseStep 1632881 = 1224661) B1224661
theorem B1075891 : Blo 952587 1075891 := bstep (se 1 (by rfl) ⟨806918, by rfl⟩ : syracuseStep 1075891 = 1613837) B1613837
theorem B2419409 : Blo 952587 2419409 := bstep (se 2 (by rfl) ⟨907278, by rfl⟩ : syracuseStep 2419409 = 1814557) B1814557
theorem B3271427 : Blo 952587 3271427 := bstep (se 1 (by rfl) ⟨2453570, by rfl⟩ : syracuseStep 3271427 = 4907141) B4907141
theorem B1076035 : Blo 952587 1076035 := bstep (se 1 (by rfl) ⟨807026, by rfl⟩ : syracuseStep 1076035 = 1614053) B1614053
theorem B1469281 : Blo 952587 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B3631985 : Blo 952587 3631985 := bstep (se 2 (by rfl) ⟨1361994, by rfl⟩ : syracuseStep 3631985 = 2723989) B2723989
theorem B1207219 : Blo 952587 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1207315 : Blo 952587 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B2714705 : Blo 952587 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B1633619 : Blo 952587 1633619 := bstep (se 1 (by rfl) ⟨1225214, by rfl⟩ : syracuseStep 1633619 = 2450429) B2450429
theorem B1207811 : Blo 952587 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B2420401 : Blo 952587 2420401 := bstep (se 2 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 2420401 = 1815301) B1815301
theorem B1634003 : Blo 952587 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B4353763 : Blo 952587 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B6123235 : Blo 952587 6123235 := bstep (se 1 (by rfl) ⟨4592426, by rfl⟩ : syracuseStep 6123235 = 9184853) B9184853
theorem B2420675 : Blo 952587 2420675 := bstep (se 1 (by rfl) ⟨1815506, by rfl⟩ : syracuseStep 2420675 = 3631013) B3631013
theorem B5435333 : Blo 952587 5435333 := bstep (se 4 (by rfl) ⟨509562, by rfl⟩ : syracuseStep 5435333 = 1019125) B1019125
theorem B2289649 : Blo 952587 2289649 := bstep (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) B1717237
theorem B2420867 : Blo 952587 2420867 := bstep (se 1 (by rfl) ⟨1815650, by rfl⟩ : syracuseStep 2420867 = 3631301) B3631301
theorem B1208515 : Blo 952587 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B1208611 : Blo 952587 1208611 := bstep (se 1 (by rfl) ⟨906458, by rfl⟩ : syracuseStep 1208611 = 1812917) B1812917
theorem B2716163 : Blo 952587 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B2585155 : Blo 952587 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B5436017 : Blo 952587 5436017 := bstep (se 2 (by rfl) ⟨2038506, by rfl⟩ : syracuseStep 5436017 = 4077013) B4077013
theorem B1209107 : Blo 952587 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B5796721 : Blo 952587 5796721 := bstep (se 2 (by rfl) ⟨2173770, by rfl⟩ : syracuseStep 5796721 = 4347541) B4347541
theorem B2945933 : Blo 952587 2945933 := bstep (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) B1104725
theorem B3667021 : Blo 952587 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B4355149 : Blo 952587 4355149 := bstep (se 3 (by rfl) ⟨816590, by rfl⟩ : syracuseStep 4355149 = 1633181) B1633181
theorem B2716973 : Blo 952587 2716973 := bstep (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) B1018865
theorem B11040181 : Blo 952587 11040181 := bstep (se 5 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 11040181 = 1035017) B1035017
theorem B1209811 : Blo 952587 1209811 := bstep (se 1 (by rfl) ⟨907358, by rfl⟩ : syracuseStep 1209811 = 1814717) B1814717
theorem B2717165 : Blo 952587 2717165 := bstep (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) B1018937
theorem B1209907 : Blo 952587 1209907 := bstep (se 1 (by rfl) ⟨907430, by rfl⟩ : syracuseStep 1209907 = 1814861) B1814861
theorem B18347633 : Blo 952587 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B16512821 : Blo 952587 16512821 := bstep (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) B1548077
theorem B5437475 : Blo 952587 5437475 := bstep (se 1 (by rfl) ⟨4078106, by rfl⟩ : syracuseStep 5437475 = 8156213) B8156213
theorem B1210403 : Blo 952587 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B2718157 : Blo 952587 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B6126029 : Blo 952587 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B5241293 : Blo 952587 5241293 := bstep (se 3 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 5241293 = 1965485) B1965485
theorem B1145507 : Blo 952587 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B3767501 : Blo 952587 3767501 := bstep (se 3 (by rfl) ⟨706406, by rfl⟩ : syracuseStep 3767501 = 1412813) B1412813
theorem B1965379 : Blo 952587 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B1473905 : Blo 952587 1473905 := bstep (se 2 (by rfl) ⟨552714, by rfl⟩ : syracuseStep 1473905 = 1105429) B1105429
theorem B4128241 : Blo 952587 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B3669731 : Blo 952587 3669731 := bstep (se 1 (by rfl) ⟨2752298, by rfl⟩ : syracuseStep 3669731 = 5504597) B5504597
theorem B6192881 : Blo 952587 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B2293571 : Blo 952587 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B4358051 : Blo 952587 4358051 := bstep (se 1 (by rfl) ⟨3268538, by rfl⟩ : syracuseStep 4358051 = 6537077) B6537077
theorem B1343473 : Blo 952587 1343473 := bstep (se 2 (by rfl) ⟨503802, by rfl⟩ : syracuseStep 1343473 = 1007605) B1007605
theorem B3670039 : Blo 952587 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B4653121 : Blo 952587 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B2326849 : Blo 952587 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B13763033 : Blo 952587 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B7242371 : Blo 952587 7242371 := bstep (se 1 (by rfl) ⟨5431778, by rfl⟩ : syracuseStep 7242371 = 10863557) B10863557
theorem B2720947 : Blo 952587 2720947 := bstep (se 1 (by rfl) ⟨2040710, by rfl⟩ : syracuseStep 2720947 = 4081421) B4081421
theorem B8160587 : Blo 952587 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B1017451 : Blo 952587 1017451 := bstep (se 1 (by rfl) ⟨763088, by rfl⟩ : syracuseStep 1017451 = 1526177) B1526177
theorem B1378135 : Blo 952587 1378135 := bstep (se 1 (by rfl) ⟨1033601, by rfl⟩ : syracuseStep 1378135 = 2067203) B2067203
theorem B2328409 : Blo 952587 2328409 := bstep (se 2 (by rfl) ⟨873153, by rfl⟩ : syracuseStep 2328409 = 1746307) B1746307
theorem B1607627 : Blo 952587 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B1607755 : Blo 952587 1607755 := bstep (se 1 (by rfl) ⟨1205816, by rfl⟩ : syracuseStep 1607755 = 2411633) B2411633
theorem B2721995 : Blo 952587 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B1607897 : Blo 952587 1607897 := bstep (se 2 (by rfl) ⟨602961, by rfl⟩ : syracuseStep 1607897 = 1205923) B1205923
theorem B952587 : Blo 952587 952587 := bstep (se 1 (by rfl) ⟨714440, by rfl⟩ : syracuseStep 952587 = 1428881) B1428881
theorem B952599 : Blo 952587 952599 := bstep (se 1 (by rfl) ⟨714449, by rfl⟩ : syracuseStep 952599 = 1428899) B1428899
theorem B952619 : Blo 952587 952619 := bstep (se 1 (by rfl) ⟨714464, by rfl⟩ : syracuseStep 952619 = 1428929) B1428929
theorem B952631 : Blo 952587 952631 := bstep (se 1 (by rfl) ⟨714473, by rfl⟩ : syracuseStep 952631 = 1428947) B1428947
theorem B952651 : Blo 952587 952651 := bstep (se 1 (by rfl) ⟨714488, by rfl⟩ : syracuseStep 952651 = 1428977) B1428977
theorem B952663 : Blo 952587 952663 := bstep (se 1 (by rfl) ⟨714497, by rfl⟩ : syracuseStep 952663 = 1428995) B1428995
theorem B1608025 : Blo 952587 1608025 := bstep (se 2 (by rfl) ⟨603009, by rfl⟩ : syracuseStep 1608025 = 1206019) B1206019
theorem B8259941 : Blo 952587 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B952683 : Blo 952587 952683 := bstep (se 1 (by rfl) ⟨714512, by rfl⟩ : syracuseStep 952683 = 1429025) B1429025
theorem B952695 : Blo 952587 952695 := bstep (se 1 (by rfl) ⟨714521, by rfl⟩ : syracuseStep 952695 = 1429043) B1429043
theorem B952715 : Blo 952587 952715 := bstep (se 1 (by rfl) ⟨714536, by rfl⟩ : syracuseStep 952715 = 1429073) B1429073
theorem B952727 : Blo 952587 952727 := bstep (se 1 (by rfl) ⟨714545, by rfl⟩ : syracuseStep 952727 = 1429091) B1429091
theorem B952747 : Blo 952587 952747 := bstep (se 1 (by rfl) ⟨714560, by rfl⟩ : syracuseStep 952747 = 1429121) B1429121
theorem B952759 : Blo 952587 952759 := bstep (se 1 (by rfl) ⟨714569, by rfl⟩ : syracuseStep 952759 = 1429139) B1429139
theorem B952779 : Blo 952587 952779 := bstep (se 1 (by rfl) ⟨714584, by rfl⟩ : syracuseStep 952779 = 1429169) B1429169
theorem B952791 : Blo 952587 952791 := bstep (se 1 (by rfl) ⟨714593, by rfl⟩ : syracuseStep 952791 = 1429187) B1429187
theorem B952811 : Blo 952587 952811 := bstep (se 1 (by rfl) ⟨714608, by rfl⟩ : syracuseStep 952811 = 1429217) B1429217
theorem B952823 : Blo 952587 952823 := bstep (se 1 (by rfl) ⟨714617, by rfl⟩ : syracuseStep 952823 = 1429235) B1429235
theorem B952843 : Blo 952587 952843 := bstep (se 1 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 952843 = 1429265) B1429265
theorem B952855 : Blo 952587 952855 := bstep (se 1 (by rfl) ⟨714641, by rfl⟩ : syracuseStep 952855 = 1429283) B1429283
theorem B952875 : Blo 952587 952875 := bstep (se 1 (by rfl) ⟨714656, by rfl⟩ : syracuseStep 952875 = 1429313) B1429313
theorem B952887 : Blo 952587 952887 := bstep (se 1 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 952887 = 1429331) B1429331
theorem B952907 : Blo 952587 952907 := bstep (se 1 (by rfl) ⟨714680, by rfl⟩ : syracuseStep 952907 = 1429361) B1429361
theorem B952919 : Blo 952587 952919 := bstep (se 1 (by rfl) ⟨714689, by rfl⟩ : syracuseStep 952919 = 1429379) B1429379
theorem B952939 : Blo 952587 952939 := bstep (se 1 (by rfl) ⟨714704, by rfl⟩ : syracuseStep 952939 = 1429409) B1429409
theorem B952951 : Blo 952587 952951 := bstep (se 1 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 952951 = 1429427) B1429427
theorem B952971 : Blo 952587 952971 := bstep (se 1 (by rfl) ⟨714728, by rfl⟩ : syracuseStep 952971 = 1429457) B1429457
theorem B952983 : Blo 952587 952983 := bstep (se 1 (by rfl) ⟨714737, by rfl⟩ : syracuseStep 952983 = 1429475) B1429475
theorem B953003 : Blo 952587 953003 := bstep (se 1 (by rfl) ⟨714752, by rfl⟩ : syracuseStep 953003 = 1429505) B1429505
theorem B953015 : Blo 952587 953015 := bstep (se 1 (by rfl) ⟨714761, by rfl⟩ : syracuseStep 953015 = 1429523) B1429523
theorem B953035 : Blo 952587 953035 := bstep (se 1 (by rfl) ⟨714776, by rfl⟩ : syracuseStep 953035 = 1429553) B1429553
theorem B953047 : Blo 952587 953047 := bstep (se 1 (by rfl) ⟨714785, by rfl⟩ : syracuseStep 953047 = 1429571) B1429571
theorem B953067 : Blo 952587 953067 := bstep (se 1 (by rfl) ⟨714800, by rfl⟩ : syracuseStep 953067 = 1429601) B1429601
theorem B953079 : Blo 952587 953079 := bstep (se 1 (by rfl) ⟨714809, by rfl⟩ : syracuseStep 953079 = 1429619) B1429619
theorem B953099 : Blo 952587 953099 := bstep (se 1 (by rfl) ⟨714824, by rfl⟩ : syracuseStep 953099 = 1429649) B1429649
theorem B953111 : Blo 952587 953111 := bstep (se 1 (by rfl) ⟨714833, by rfl⟩ : syracuseStep 953111 = 1429667) B1429667
theorem B953131 : Blo 952587 953131 := bstep (se 1 (by rfl) ⟨714848, by rfl⟩ : syracuseStep 953131 = 1429697) B1429697
theorem B5442349 : Blo 952587 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B953143 : Blo 952587 953143 := bstep (se 1 (by rfl) ⟨714857, by rfl⟩ : syracuseStep 953143 = 1429715) B1429715
theorem B953163 : Blo 952587 953163 := bstep (se 1 (by rfl) ⟨714872, by rfl⟩ : syracuseStep 953163 = 1429745) B1429745
theorem B953175 : Blo 952587 953175 := bstep (se 1 (by rfl) ⟨714881, by rfl⟩ : syracuseStep 953175 = 1429763) B1429763
theorem B953195 : Blo 952587 953195 := bstep (se 1 (by rfl) ⟨714896, by rfl⟩ : syracuseStep 953195 = 1429793) B1429793
theorem B953207 : Blo 952587 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B953227 : Blo 952587 953227 := bstep (se 1 (by rfl) ⟨714920, by rfl⟩ : syracuseStep 953227 = 1429841) B1429841
theorem B953239 : Blo 952587 953239 := bstep (se 1 (by rfl) ⟨714929, by rfl⟩ : syracuseStep 953239 = 1429859) B1429859
theorem B1608599 : Blo 952587 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B1018775 : Blo 952587 1018775 := bstep (se 1 (by rfl) ⟨764081, by rfl⟩ : syracuseStep 1018775 = 1528163) B1528163
theorem B953259 : Blo 952587 953259 := bstep (se 1 (by rfl) ⟨714944, by rfl⟩ : syracuseStep 953259 = 1429889) B1429889
theorem B3443629 : Blo 952587 3443629 := bstep (se 3 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 3443629 = 1291361) B1291361
theorem B953271 : Blo 952587 953271 := bstep (se 1 (by rfl) ⟨714953, by rfl⟩ : syracuseStep 953271 = 1429907) B1429907
theorem B953291 : Blo 952587 953291 := bstep (se 1 (by rfl) ⟨714968, by rfl⟩ : syracuseStep 953291 = 1429937) B1429937
theorem B953303 : Blo 952587 953303 := bstep (se 1 (by rfl) ⟨714977, by rfl⟩ : syracuseStep 953303 = 1429955) B1429955
theorem B953323 : Blo 952587 953323 := bstep (se 1 (by rfl) ⟨714992, by rfl⟩ : syracuseStep 953323 = 1429985) B1429985
theorem B953335 : Blo 952587 953335 := bstep (se 1 (by rfl) ⟨715001, by rfl⟩ : syracuseStep 953335 = 1430003) B1430003
theorem B953355 : Blo 952587 953355 := bstep (se 1 (by rfl) ⟨715016, by rfl⟩ : syracuseStep 953355 = 1430033) B1430033
theorem B1608727 : Blo 952587 1608727 := bstep (se 1 (by rfl) ⟨1206545, by rfl⟩ : syracuseStep 1608727 = 2413091) B2413091
theorem B953367 : Blo 952587 953367 := bstep (se 1 (by rfl) ⟨715025, by rfl⟩ : syracuseStep 953367 = 1430051) B1430051
theorem B1018903 : Blo 952587 1018903 := bstep (se 1 (by rfl) ⟨764177, by rfl⟩ : syracuseStep 1018903 = 1528355) B1528355
theorem B953387 : Blo 952587 953387 := bstep (se 1 (by rfl) ⟨715040, by rfl⟩ : syracuseStep 953387 = 1430081) B1430081
theorem B953399 : Blo 952587 953399 := bstep (se 1 (by rfl) ⟨715049, by rfl⟩ : syracuseStep 953399 = 1430099) B1430099
theorem B953419 : Blo 952587 953419 := bstep (se 1 (by rfl) ⟨715064, by rfl⟩ : syracuseStep 953419 = 1430129) B1430129
theorem B953431 : Blo 952587 953431 := bstep (se 1 (by rfl) ⟨715073, by rfl⟩ : syracuseStep 953431 = 1430147) B1430147
theorem B3673181 : Blo 952587 3673181 := bstep (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) B1377443
theorem B953451 : Blo 952587 953451 := bstep (se 1 (by rfl) ⟨715088, by rfl⟩ : syracuseStep 953451 = 1430177) B1430177
theorem B953463 : Blo 952587 953463 := bstep (se 1 (by rfl) ⟨715097, by rfl⟩ : syracuseStep 953463 = 1430195) B1430195
theorem B953483 : Blo 952587 953483 := bstep (se 1 (by rfl) ⟨715112, by rfl⟩ : syracuseStep 953483 = 1430225) B1430225
theorem B953495 : Blo 952587 953495 := bstep (se 1 (by rfl) ⟨715121, by rfl⟩ : syracuseStep 953495 = 1430243) B1430243
theorem B953515 : Blo 952587 953515 := bstep (se 1 (by rfl) ⟨715136, by rfl⟩ : syracuseStep 953515 = 1430273) B1430273
theorem B2297011 : Blo 952587 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B953527 : Blo 952587 953527 := bstep (se 1 (by rfl) ⟨715145, by rfl⟩ : syracuseStep 953527 = 1430291) B1430291
theorem B953547 : Blo 952587 953547 := bstep (se 1 (by rfl) ⟨715160, by rfl⟩ : syracuseStep 953547 = 1430321) B1430321
theorem B953559 : Blo 952587 953559 := bstep (se 1 (by rfl) ⟨715169, by rfl⟩ : syracuseStep 953559 = 1430339) B1430339
theorem B953579 : Blo 952587 953579 := bstep (se 1 (by rfl) ⟨715184, by rfl⟩ : syracuseStep 953579 = 1430369) B1430369
theorem B953591 : Blo 952587 953591 := bstep (se 1 (by rfl) ⟨715193, by rfl⟩ : syracuseStep 953591 = 1430387) B1430387
theorem B953611 : Blo 952587 953611 := bstep (se 1 (by rfl) ⟨715208, by rfl⟩ : syracuseStep 953611 = 1430417) B1430417
theorem B953623 : Blo 952587 953623 := bstep (se 1 (by rfl) ⟨715217, by rfl⟩ : syracuseStep 953623 = 1430435) B1430435
theorem B953643 : Blo 952587 953643 := bstep (se 1 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 953643 = 1430465) B1430465
theorem B953655 : Blo 952587 953655 := bstep (se 1 (by rfl) ⟨715241, by rfl⟩ : syracuseStep 953655 = 1430483) B1430483
theorem B953675 : Blo 952587 953675 := bstep (se 1 (by rfl) ⟨715256, by rfl⟩ : syracuseStep 953675 = 1430513) B1430513
theorem B953687 : Blo 952587 953687 := bstep (se 1 (by rfl) ⟨715265, by rfl⟩ : syracuseStep 953687 = 1430531) B1430531
theorem B953707 : Blo 952587 953707 := bstep (se 1 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 953707 = 1430561) B1430561
theorem B953719 : Blo 952587 953719 := bstep (se 1 (by rfl) ⟨715289, by rfl⟩ : syracuseStep 953719 = 1430579) B1430579
theorem B953739 : Blo 952587 953739 := bstep (se 1 (by rfl) ⟨715304, by rfl⟩ : syracuseStep 953739 = 1430609) B1430609
theorem B953751 : Blo 952587 953751 := bstep (se 1 (by rfl) ⟨715313, by rfl⟩ : syracuseStep 953751 = 1430627) B1430627
theorem B953771 : Blo 952587 953771 := bstep (se 1 (by rfl) ⟨715328, by rfl⟩ : syracuseStep 953771 = 1430657) B1430657
theorem B953783 : Blo 952587 953783 := bstep (se 1 (by rfl) ⟨715337, by rfl⟩ : syracuseStep 953783 = 1430675) B1430675
theorem B953803 : Blo 952587 953803 := bstep (se 1 (by rfl) ⟨715352, by rfl⟩ : syracuseStep 953803 = 1430705) B1430705
theorem B953815 : Blo 952587 953815 := bstep (se 1 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 953815 = 1430723) B1430723
theorem B953835 : Blo 952587 953835 := bstep (se 1 (by rfl) ⟨715376, by rfl⟩ : syracuseStep 953835 = 1430753) B1430753
theorem B953847 : Blo 952587 953847 := bstep (se 1 (by rfl) ⟨715385, by rfl⟩ : syracuseStep 953847 = 1430771) B1430771
theorem B2035201 : Blo 952587 2035201 := bstep (se 2 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 2035201 = 1526401) B1526401
theorem B953867 : Blo 952587 953867 := bstep (se 1 (by rfl) ⟨715400, by rfl⟩ : syracuseStep 953867 = 1430801) B1430801
theorem B953879 : Blo 952587 953879 := bstep (se 1 (by rfl) ⟨715409, by rfl⟩ : syracuseStep 953879 = 1430819) B1430819
theorem B1936919 : Blo 952587 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B953899 : Blo 952587 953899 := bstep (se 1 (by rfl) ⟨715424, by rfl⟩ : syracuseStep 953899 = 1430849) B1430849
theorem B953911 : Blo 952587 953911 := bstep (se 1 (by rfl) ⟨715433, by rfl⟩ : syracuseStep 953911 = 1430867) B1430867
theorem B953931 : Blo 952587 953931 := bstep (se 1 (by rfl) ⟨715448, by rfl⟩ : syracuseStep 953931 = 1430897) B1430897
theorem B1019467 : Blo 952587 1019467 := bstep (se 1 (by rfl) ⟨764600, by rfl⟩ : syracuseStep 1019467 = 1529201) B1529201
theorem B953943 : Blo 952587 953943 := bstep (se 1 (by rfl) ⟨715457, by rfl⟩ : syracuseStep 953943 = 1430915) B1430915
theorem B953963 : Blo 952587 953963 := bstep (se 1 (by rfl) ⟨715472, by rfl⟩ : syracuseStep 953963 = 1430945) B1430945
theorem B953975 : Blo 952587 953975 := bstep (se 1 (by rfl) ⟨715481, by rfl⟩ : syracuseStep 953975 = 1430963) B1430963
theorem B1609355 : Blo 952587 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B953995 : Blo 952587 953995 := bstep (se 1 (by rfl) ⟨715496, by rfl⟩ : syracuseStep 953995 = 1430993) B1430993
theorem B954007 : Blo 952587 954007 := bstep (se 1 (by rfl) ⟨715505, by rfl⟩ : syracuseStep 954007 = 1431011) B1431011
theorem B954027 : Blo 952587 954027 := bstep (se 1 (by rfl) ⟨715520, by rfl⟩ : syracuseStep 954027 = 1431041) B1431041
theorem B8261297 : Blo 952587 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B954039 : Blo 952587 954039 := bstep (se 1 (by rfl) ⟨715529, by rfl⟩ : syracuseStep 954039 = 1431059) B1431059
theorem B3215051 : Blo 952587 3215051 := bstep (se 1 (by rfl) ⟨2411288, by rfl⟩ : syracuseStep 3215051 = 4822577) B4822577
theorem B954059 : Blo 952587 954059 := bstep (se 1 (by rfl) ⟨715544, by rfl⟩ : syracuseStep 954059 = 1431089) B1431089
theorem B954071 : Blo 952587 954071 := bstep (se 1 (by rfl) ⟨715553, by rfl⟩ : syracuseStep 954071 = 1431107) B1431107
theorem B954091 : Blo 952587 954091 := bstep (se 1 (by rfl) ⟨715568, by rfl⟩ : syracuseStep 954091 = 1431137) B1431137
theorem B954103 : Blo 952587 954103 := bstep (se 1 (by rfl) ⟨715577, by rfl⟩ : syracuseStep 954103 = 1431155) B1431155
theorem B3870467 : Blo 952587 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B1609483 : Blo 952587 1609483 := bstep (se 1 (by rfl) ⟨1207112, by rfl⟩ : syracuseStep 1609483 = 2414225) B2414225
theorem B954123 : Blo 952587 954123 := bstep (se 1 (by rfl) ⟨715592, by rfl⟩ : syracuseStep 954123 = 1431185) B1431185
theorem B954135 : Blo 952587 954135 := bstep (se 1 (by rfl) ⟨715601, by rfl⟩ : syracuseStep 954135 = 1431203) B1431203
theorem B954155 : Blo 952587 954155 := bstep (se 1 (by rfl) ⟨715616, by rfl⟩ : syracuseStep 954155 = 1431233) B1431233
theorem B2723635 : Blo 952587 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B954167 : Blo 952587 954167 := bstep (se 1 (by rfl) ⟨715625, by rfl⟩ : syracuseStep 954167 = 1431251) B1431251
theorem B954187 : Blo 952587 954187 := bstep (se 1 (by rfl) ⟨715640, by rfl⟩ : syracuseStep 954187 = 1431281) B1431281
theorem B1019723 : Blo 952587 1019723 := bstep (se 1 (by rfl) ⟨764792, by rfl⟩ : syracuseStep 1019723 = 1529585) B1529585
theorem B2035543 : Blo 952587 2035543 := bstep (se 1 (by rfl) ⟨1526657, by rfl⟩ : syracuseStep 2035543 = 3053315) B3053315
theorem B954199 : Blo 952587 954199 := bstep (se 1 (by rfl) ⟨715649, by rfl⟩ : syracuseStep 954199 = 1431299) B1431299
theorem B954219 : Blo 952587 954219 := bstep (se 1 (by rfl) ⟨715664, by rfl⟩ : syracuseStep 954219 = 1431329) B1431329
theorem B954231 : Blo 952587 954231 := bstep (se 1 (by rfl) ⟨715673, by rfl⟩ : syracuseStep 954231 = 1431347) B1431347
theorem B954251 : Blo 952587 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B954263 : Blo 952587 954263 := bstep (se 1 (by rfl) ⟨715697, by rfl⟩ : syracuseStep 954263 = 1431395) B1431395
theorem B1609625 : Blo 952587 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B954283 : Blo 952587 954283 := bstep (se 1 (by rfl) ⟨715712, by rfl⟩ : syracuseStep 954283 = 1431425) B1431425
theorem B8163251 : Blo 952587 8163251 := bstep (se 1 (by rfl) ⟨6122438, by rfl⟩ : syracuseStep 8163251 = 12244877) B12244877
theorem B954295 : Blo 952587 954295 := bstep (se 1 (by rfl) ⟨715721, by rfl⟩ : syracuseStep 954295 = 1431443) B1431443
theorem B954315 : Blo 952587 954315 := bstep (se 1 (by rfl) ⟨715736, by rfl⟩ : syracuseStep 954315 = 1431473) B1431473
theorem B7245773 : Blo 952587 7245773 := bstep (se 3 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 7245773 = 2717165) B2717165
theorem B954327 : Blo 952587 954327 := bstep (se 1 (by rfl) ⟨715745, by rfl⟩ : syracuseStep 954327 = 1431491) B1431491
theorem B3215321 : Blo 952587 3215321 := bstep (se 2 (by rfl) ⟨1205745, by rfl⟩ : syracuseStep 3215321 = 2411491) B2411491
theorem B954347 : Blo 952587 954347 := bstep (se 1 (by rfl) ⟨715760, by rfl⟩ : syracuseStep 954347 = 1431521) B1431521
theorem B954359 : Blo 952587 954359 := bstep (se 1 (by rfl) ⟨715769, by rfl⟩ : syracuseStep 954359 = 1431539) B1431539
theorem B954379 : Blo 952587 954379 := bstep (se 1 (by rfl) ⟨715784, by rfl⟩ : syracuseStep 954379 = 1431569) B1431569
theorem B954391 : Blo 952587 954391 := bstep (se 1 (by rfl) ⟨715793, by rfl⟩ : syracuseStep 954391 = 1431587) B1431587
theorem B2723863 : Blo 952587 2723863 := bstep (se 1 (by rfl) ⟨2042897, by rfl⟩ : syracuseStep 2723863 = 4085795) B4085795
theorem B1609753 : Blo 952587 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B954411 : Blo 952587 954411 := bstep (se 1 (by rfl) ⟨715808, by rfl⟩ : syracuseStep 954411 = 1431617) B1431617
theorem B954423 : Blo 952587 954423 := bstep (se 1 (by rfl) ⟨715817, by rfl⟩ : syracuseStep 954423 = 1431635) B1431635
theorem B954443 : Blo 952587 954443 := bstep (se 1 (by rfl) ⟨715832, by rfl⟩ : syracuseStep 954443 = 1431665) B1431665
theorem B954455 : Blo 952587 954455 := bstep (se 1 (by rfl) ⟨715841, by rfl⟩ : syracuseStep 954455 = 1431683) B1431683
theorem B954475 : Blo 952587 954475 := bstep (se 1 (by rfl) ⟨715856, by rfl⟩ : syracuseStep 954475 = 1431713) B1431713
theorem B954487 : Blo 952587 954487 := bstep (se 1 (by rfl) ⟨715865, by rfl⟩ : syracuseStep 954487 = 1431731) B1431731
theorem B954507 : Blo 952587 954507 := bstep (se 1 (by rfl) ⟨715880, by rfl⟩ : syracuseStep 954507 = 1431761) B1431761
theorem B954519 : Blo 952587 954519 := bstep (se 1 (by rfl) ⟨715889, by rfl⟩ : syracuseStep 954519 = 1431779) B1431779
theorem B954539 : Blo 952587 954539 := bstep (se 1 (by rfl) ⟨715904, by rfl⟩ : syracuseStep 954539 = 1431809) B1431809
theorem B954551 : Blo 952587 954551 := bstep (se 1 (by rfl) ⟨715913, by rfl⟩ : syracuseStep 954551 = 1431827) B1431827
theorem B954571 : Blo 952587 954571 := bstep (se 1 (by rfl) ⟨715928, by rfl⟩ : syracuseStep 954571 = 1431857) B1431857
theorem B2298059 : Blo 952587 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B954583 : Blo 952587 954583 := bstep (se 1 (by rfl) ⟨715937, by rfl⟩ : syracuseStep 954583 = 1431875) B1431875
theorem B954603 : Blo 952587 954603 := bstep (se 1 (by rfl) ⟨715952, by rfl⟩ : syracuseStep 954603 = 1431905) B1431905
theorem B954615 : Blo 952587 954615 := bstep (se 1 (by rfl) ⟨715961, by rfl⟩ : syracuseStep 954615 = 1431923) B1431923
theorem B954635 : Blo 952587 954635 := bstep (se 1 (by rfl) ⟨715976, by rfl⟩ : syracuseStep 954635 = 1431953) B1431953
theorem B954647 : Blo 952587 954647 := bstep (se 1 (by rfl) ⟨715985, by rfl⟩ : syracuseStep 954647 = 1431971) B1431971
theorem B954667 : Blo 952587 954667 := bstep (se 1 (by rfl) ⟨716000, by rfl⟩ : syracuseStep 954667 = 1432001) B1432001
theorem B50172205 : Blo 952587 50172205 := bstep (se 3 (by rfl) ⟨9407288, by rfl⟩ : syracuseStep 50172205 = 18814577) B18814577
theorem B954679 : Blo 952587 954679 := bstep (se 1 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 954679 = 1432019) B1432019
theorem B954699 : Blo 952587 954699 := bstep (se 1 (by rfl) ⟨716024, by rfl⟩ : syracuseStep 954699 = 1432049) B1432049
theorem B954711 : Blo 952587 954711 := bstep (se 1 (by rfl) ⟨716033, by rfl⟩ : syracuseStep 954711 = 1432067) B1432067
theorem B954731 : Blo 952587 954731 := bstep (se 1 (by rfl) ⟨716048, by rfl⟩ : syracuseStep 954731 = 1432097) B1432097
theorem B954743 : Blo 952587 954743 := bstep (se 1 (by rfl) ⟨716057, by rfl⟩ : syracuseStep 954743 = 1432115) B1432115
theorem B954763 : Blo 952587 954763 := bstep (se 1 (by rfl) ⟨716072, by rfl⟩ : syracuseStep 954763 = 1432145) B1432145
theorem B954775 : Blo 952587 954775 := bstep (se 1 (by rfl) ⟨716081, by rfl⟩ : syracuseStep 954775 = 1432163) B1432163
theorem B954795 : Blo 952587 954795 := bstep (se 1 (by rfl) ⟨716096, by rfl⟩ : syracuseStep 954795 = 1432193) B1432193
theorem B7246259 : Blo 952587 7246259 := bstep (se 1 (by rfl) ⟨5434694, by rfl⟩ : syracuseStep 7246259 = 10869389) B10869389
theorem B954807 : Blo 952587 954807 := bstep (se 1 (by rfl) ⟨716105, by rfl⟩ : syracuseStep 954807 = 1432211) B1432211
theorem B954827 : Blo 952587 954827 := bstep (se 1 (by rfl) ⟨716120, by rfl⟩ : syracuseStep 954827 = 1432241) B1432241
theorem B954839 : Blo 952587 954839 := bstep (se 1 (by rfl) ⟨716129, by rfl⟩ : syracuseStep 954839 = 1432259) B1432259
theorem B954859 : Blo 952587 954859 := bstep (se 1 (by rfl) ⟨716144, by rfl⟩ : syracuseStep 954859 = 1432289) B1432289
theorem B954871 : Blo 952587 954871 := bstep (se 1 (by rfl) ⟨716153, by rfl⟩ : syracuseStep 954871 = 1432307) B1432307
theorem B954891 : Blo 952587 954891 := bstep (se 1 (by rfl) ⟨716168, by rfl⟩ : syracuseStep 954891 = 1432337) B1432337
theorem B954903 : Blo 952587 954903 := bstep (se 1 (by rfl) ⟨716177, by rfl⟩ : syracuseStep 954903 = 1432355) B1432355
theorem B954923 : Blo 952587 954923 := bstep (se 1 (by rfl) ⟨716192, by rfl⟩ : syracuseStep 954923 = 1432385) B1432385
theorem B954935 : Blo 952587 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B954955 : Blo 952587 954955 := bstep (se 1 (by rfl) ⟨716216, by rfl⟩ : syracuseStep 954955 = 1432433) B1432433
theorem B1610327 : Blo 952587 1610327 := bstep (se 1 (by rfl) ⟨1207745, by rfl⟩ : syracuseStep 1610327 = 2415491) B2415491
theorem B954967 : Blo 952587 954967 := bstep (se 1 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 954967 = 1432451) B1432451
theorem B954987 : Blo 952587 954987 := bstep (se 1 (by rfl) ⟨716240, by rfl⟩ : syracuseStep 954987 = 1432481) B1432481
theorem B954999 : Blo 952587 954999 := bstep (se 1 (by rfl) ⟨716249, by rfl⟩ : syracuseStep 954999 = 1432499) B1432499
theorem B955019 : Blo 952587 955019 := bstep (se 1 (by rfl) ⟨716264, by rfl⟩ : syracuseStep 955019 = 1432529) B1432529
theorem B3216023 : Blo 952587 3216023 := bstep (se 1 (by rfl) ⟨2412017, by rfl⟩ : syracuseStep 3216023 = 4824035) B4824035
theorem B955031 : Blo 952587 955031 := bstep (se 1 (by rfl) ⟨716273, by rfl⟩ : syracuseStep 955031 = 1432547) B1432547
theorem B955051 : Blo 952587 955051 := bstep (se 1 (by rfl) ⟨716288, by rfl⟩ : syracuseStep 955051 = 1432577) B1432577
theorem B955063 : Blo 952587 955063 := bstep (se 1 (by rfl) ⟨716297, by rfl⟩ : syracuseStep 955063 = 1432595) B1432595
theorem B955083 : Blo 952587 955083 := bstep (se 1 (by rfl) ⟨716312, by rfl⟩ : syracuseStep 955083 = 1432625) B1432625
theorem B1610455 : Blo 952587 1610455 := bstep (se 1 (by rfl) ⟨1207841, by rfl⟩ : syracuseStep 1610455 = 2415683) B2415683
theorem B955095 : Blo 952587 955095 := bstep (se 1 (by rfl) ⟨716321, by rfl⟩ : syracuseStep 955095 = 1432643) B1432643
theorem B7344857 : Blo 952587 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B955115 : Blo 952587 955115 := bstep (se 1 (by rfl) ⟨716336, by rfl⟩ : syracuseStep 955115 = 1432673) B1432673
theorem B955127 : Blo 952587 955127 := bstep (se 1 (by rfl) ⟨716345, by rfl⟩ : syracuseStep 955127 = 1432691) B1432691
theorem B955147 : Blo 952587 955147 := bstep (se 1 (by rfl) ⟨716360, by rfl⟩ : syracuseStep 955147 = 1432721) B1432721
theorem B955159 : Blo 952587 955159 := bstep (se 1 (by rfl) ⟨716369, by rfl⟩ : syracuseStep 955159 = 1432739) B1432739
theorem B955179 : Blo 952587 955179 := bstep (se 1 (by rfl) ⟨716384, by rfl⟩ : syracuseStep 955179 = 1432769) B1432769
theorem B955191 : Blo 952587 955191 := bstep (se 1 (by rfl) ⟨716393, by rfl⟩ : syracuseStep 955191 = 1432787) B1432787
theorem B955211 : Blo 952587 955211 := bstep (se 1 (by rfl) ⟨716408, by rfl⟩ : syracuseStep 955211 = 1432817) B1432817
theorem B955223 : Blo 952587 955223 := bstep (se 1 (by rfl) ⟨716417, by rfl⟩ : syracuseStep 955223 = 1432835) B1432835
theorem B955243 : Blo 952587 955243 := bstep (se 1 (by rfl) ⟨716432, by rfl⟩ : syracuseStep 955243 = 1432865) B1432865
theorem B955255 : Blo 952587 955255 := bstep (se 1 (by rfl) ⟨716441, by rfl⟩ : syracuseStep 955255 = 1432883) B1432883
theorem B955275 : Blo 952587 955275 := bstep (se 1 (by rfl) ⟨716456, by rfl⟩ : syracuseStep 955275 = 1432913) B1432913
theorem B955287 : Blo 952587 955287 := bstep (se 1 (by rfl) ⟨716465, by rfl⟩ : syracuseStep 955287 = 1432931) B1432931
theorem B955307 : Blo 952587 955307 := bstep (se 1 (by rfl) ⟨716480, by rfl⟩ : syracuseStep 955307 = 1432961) B1432961
theorem B955319 : Blo 952587 955319 := bstep (se 1 (by rfl) ⟨716489, by rfl⟩ : syracuseStep 955319 = 1432979) B1432979
theorem B955339 : Blo 952587 955339 := bstep (se 1 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 955339 = 1433009) B1433009
theorem B955351 : Blo 952587 955351 := bstep (se 1 (by rfl) ⟨716513, by rfl⟩ : syracuseStep 955351 = 1433027) B1433027
theorem B5805017 : Blo 952587 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B8164313 : Blo 952587 8164313 := bstep (se 2 (by rfl) ⟨3061617, by rfl⟩ : syracuseStep 8164313 = 6123235) B6123235
theorem B955371 : Blo 952587 955371 := bstep (se 1 (by rfl) ⟨716528, by rfl⟩ : syracuseStep 955371 = 1433057) B1433057
theorem B955383 : Blo 952587 955383 := bstep (se 1 (by rfl) ⟨716537, by rfl⟩ : syracuseStep 955383 = 1433075) B1433075
theorem B2036747 : Blo 952587 2036747 := bstep (se 1 (by rfl) ⟨1527560, by rfl⟩ : syracuseStep 2036747 = 3055121) B3055121
theorem B955403 : Blo 952587 955403 := bstep (se 1 (by rfl) ⟨716552, by rfl⟩ : syracuseStep 955403 = 1433105) B1433105
theorem B955415 : Blo 952587 955415 := bstep (se 1 (by rfl) ⟨716561, by rfl⟩ : syracuseStep 955415 = 1433123) B1433123
theorem B955435 : Blo 952587 955435 := bstep (se 1 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 955435 = 1433153) B1433153
theorem B955447 : Blo 952587 955447 := bstep (se 1 (by rfl) ⟨716585, by rfl⟩ : syracuseStep 955447 = 1433171) B1433171
theorem B1840193 : Blo 952587 1840193 := bstep (se 2 (by rfl) ⟨690072, by rfl⟩ : syracuseStep 1840193 = 1380145) B1380145
theorem B955467 : Blo 952587 955467 := bstep (se 1 (by rfl) ⟨716600, by rfl⟩ : syracuseStep 955467 = 1433201) B1433201
theorem B955479 : Blo 952587 955479 := bstep (se 1 (by rfl) ⟨716609, by rfl⟩ : syracuseStep 955479 = 1433219) B1433219
theorem B955499 : Blo 952587 955499 := bstep (se 1 (by rfl) ⟨716624, by rfl⟩ : syracuseStep 955499 = 1433249) B1433249
theorem B955511 : Blo 952587 955511 := bstep (se 1 (by rfl) ⟨716633, by rfl⟩ : syracuseStep 955511 = 1433267) B1433267
theorem B955531 : Blo 952587 955531 := bstep (se 1 (by rfl) ⟨716648, by rfl⟩ : syracuseStep 955531 = 1433297) B1433297
theorem B955543 : Blo 952587 955543 := bstep (se 1 (by rfl) ⟨716657, by rfl⟩ : syracuseStep 955543 = 1433315) B1433315
theorem B4592791 : Blo 952587 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B955563 : Blo 952587 955563 := bstep (se 1 (by rfl) ⟨716672, by rfl⟩ : syracuseStep 955563 = 1433345) B1433345
theorem B3216563 : Blo 952587 3216563 := bstep (se 1 (by rfl) ⟨2412422, by rfl⟩ : syracuseStep 3216563 = 4824845) B4824845
theorem B955575 : Blo 952587 955575 := bstep (se 1 (by rfl) ⟨716681, by rfl⟩ : syracuseStep 955575 = 1433363) B1433363
theorem B955595 : Blo 952587 955595 := bstep (se 1 (by rfl) ⟨716696, by rfl⟩ : syracuseStep 955595 = 1433393) B1433393
theorem B955607 : Blo 952587 955607 := bstep (se 1 (by rfl) ⟨716705, by rfl⟩ : syracuseStep 955607 = 1433411) B1433411
theorem B955627 : Blo 952587 955627 := bstep (se 1 (by rfl) ⟨716720, by rfl⟩ : syracuseStep 955627 = 1433441) B1433441
theorem B955639 : Blo 952587 955639 := bstep (se 1 (by rfl) ⟨716729, by rfl⟩ : syracuseStep 955639 = 1433459) B1433459
theorem B955659 : Blo 952587 955659 := bstep (se 1 (by rfl) ⟨716744, by rfl⟩ : syracuseStep 955659 = 1433489) B1433489
theorem B955671 : Blo 952587 955671 := bstep (se 1 (by rfl) ⟨716753, by rfl⟩ : syracuseStep 955671 = 1433507) B1433507
theorem B955691 : Blo 952587 955691 := bstep (se 1 (by rfl) ⟨716768, by rfl⟩ : syracuseStep 955691 = 1433537) B1433537
theorem B955703 : Blo 952587 955703 := bstep (se 1 (by rfl) ⟨716777, by rfl⟩ : syracuseStep 955703 = 1433555) B1433555
theorem B3052865 : Blo 952587 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B1611083 : Blo 952587 1611083 := bstep (se 1 (by rfl) ⟨1208312, by rfl⟩ : syracuseStep 1611083 = 2416625) B2416625
theorem B955723 : Blo 952587 955723 := bstep (se 1 (by rfl) ⟨716792, by rfl⟩ : syracuseStep 955723 = 1433585) B1433585
theorem B955735 : Blo 952587 955735 := bstep (se 1 (by rfl) ⟨716801, by rfl⟩ : syracuseStep 955735 = 1433603) B1433603
theorem B955755 : Blo 952587 955755 := bstep (se 1 (by rfl) ⟨716816, by rfl⟩ : syracuseStep 955755 = 1433633) B1433633
theorem B955767 : Blo 952587 955767 := bstep (se 1 (by rfl) ⟨716825, by rfl⟩ : syracuseStep 955767 = 1433651) B1433651
theorem B955787 : Blo 952587 955787 := bstep (se 1 (by rfl) ⟨716840, by rfl⟩ : syracuseStep 955787 = 1433681) B1433681
theorem B955799 : Blo 952587 955799 := bstep (se 1 (by rfl) ⟨716849, by rfl⟩ : syracuseStep 955799 = 1433699) B1433699
theorem B955819 : Blo 952587 955819 := bstep (se 1 (by rfl) ⟨716864, by rfl⟩ : syracuseStep 955819 = 1433729) B1433729
theorem B955831 : Blo 952587 955831 := bstep (se 1 (by rfl) ⟨716873, by rfl⟩ : syracuseStep 955831 = 1433747) B1433747
theorem B3216833 : Blo 952587 3216833 := bstep (se 2 (by rfl) ⟨1206312, by rfl⟩ : syracuseStep 3216833 = 2412625) B2412625
theorem B1611211 : Blo 952587 1611211 := bstep (se 1 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 1611211 = 2416817) B2416817
theorem B955851 : Blo 952587 955851 := bstep (se 1 (by rfl) ⟨716888, by rfl⟩ : syracuseStep 955851 = 1433777) B1433777
theorem B955863 : Blo 952587 955863 := bstep (se 1 (by rfl) ⟨716897, by rfl⟩ : syracuseStep 955863 = 1433795) B1433795
theorem B955883 : Blo 952587 955883 := bstep (se 1 (by rfl) ⟨716912, by rfl⟩ : syracuseStep 955883 = 1433825) B1433825
theorem B955895 : Blo 952587 955895 := bstep (se 1 (by rfl) ⟨716921, by rfl⟩ : syracuseStep 955895 = 1433843) B1433843
theorem B2037259 : Blo 952587 2037259 := bstep (se 1 (by rfl) ⟨1527944, by rfl⟩ : syracuseStep 2037259 = 3055889) B3055889
theorem B955915 : Blo 952587 955915 := bstep (se 1 (by rfl) ⟨716936, by rfl⟩ : syracuseStep 955915 = 1433873) B1433873
theorem B955927 : Blo 952587 955927 := bstep (se 1 (by rfl) ⟨716945, by rfl⟩ : syracuseStep 955927 = 1433891) B1433891
theorem B955947 : Blo 952587 955947 := bstep (se 1 (by rfl) ⟨716960, by rfl⟩ : syracuseStep 955947 = 1433921) B1433921
theorem B955959 : Blo 952587 955959 := bstep (se 1 (by rfl) ⟨716969, by rfl⟩ : syracuseStep 955959 = 1433939) B1433939
theorem B955979 : Blo 952587 955979 := bstep (se 1 (by rfl) ⟨716984, by rfl⟩ : syracuseStep 955979 = 1433969) B1433969
theorem B955991 : Blo 952587 955991 := bstep (se 1 (by rfl) ⟨716993, by rfl⟩ : syracuseStep 955991 = 1433987) B1433987
theorem B1611353 : Blo 952587 1611353 := bstep (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) B1208515
theorem B956011 : Blo 952587 956011 := bstep (se 1 (by rfl) ⟨717008, by rfl⟩ : syracuseStep 956011 = 1434017) B1434017
theorem B956023 : Blo 952587 956023 := bstep (se 1 (by rfl) ⟨717017, by rfl⟩ : syracuseStep 956023 = 1434035) B1434035
theorem B956043 : Blo 952587 956043 := bstep (se 1 (by rfl) ⟨717032, by rfl⟩ : syracuseStep 956043 = 1434065) B1434065
theorem B956055 : Blo 952587 956055 := bstep (se 1 (by rfl) ⟨717041, by rfl⟩ : syracuseStep 956055 = 1434083) B1434083
theorem B956075 : Blo 952587 956075 := bstep (se 1 (by rfl) ⟨717056, by rfl⟩ : syracuseStep 956075 = 1434113) B1434113
theorem B956087 : Blo 952587 956087 := bstep (se 1 (by rfl) ⟨717065, by rfl⟩ : syracuseStep 956087 = 1434131) B1434131
theorem B956107 : Blo 952587 956107 := bstep (se 1 (by rfl) ⟨717080, by rfl⟩ : syracuseStep 956107 = 1434161) B1434161
theorem B956119 : Blo 952587 956119 := bstep (se 1 (by rfl) ⟨717089, by rfl⟩ : syracuseStep 956119 = 1434179) B1434179
theorem B1611481 : Blo 952587 1611481 := bstep (se 2 (by rfl) ⟨604305, by rfl⟩ : syracuseStep 1611481 = 1208611) B1208611
theorem B956139 : Blo 952587 956139 := bstep (se 1 (by rfl) ⟨717104, by rfl⟩ : syracuseStep 956139 = 1434209) B1434209
theorem B956151 : Blo 952587 956151 := bstep (se 1 (by rfl) ⟨717113, by rfl⟩ : syracuseStep 956151 = 1434227) B1434227
theorem B956171 : Blo 952587 956171 := bstep (se 1 (by rfl) ⟨717128, by rfl⟩ : syracuseStep 956171 = 1434257) B1434257
theorem B956183 : Blo 952587 956183 := bstep (se 1 (by rfl) ⟨717137, by rfl⟩ : syracuseStep 956183 = 1434275) B1434275
theorem B956203 : Blo 952587 956203 := bstep (se 1 (by rfl) ⟨717152, by rfl⟩ : syracuseStep 956203 = 1434305) B1434305
theorem B956215 : Blo 952587 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B956235 : Blo 952587 956235 := bstep (se 1 (by rfl) ⟨717176, by rfl⟩ : syracuseStep 956235 = 1434353) B1434353
theorem B956247 : Blo 952587 956247 := bstep (se 1 (by rfl) ⟨717185, by rfl⟩ : syracuseStep 956247 = 1434371) B1434371
theorem B3872605 : Blo 952587 3872605 := bstep (se 3 (by rfl) ⟨726113, by rfl⟩ : syracuseStep 3872605 = 1452227) B1452227
theorem B7247717 : Blo 952587 7247717 := bstep (se 4 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 7247717 = 1358947) B1358947
theorem B956267 : Blo 952587 956267 := bstep (se 1 (by rfl) ⟨717200, by rfl⟩ : syracuseStep 956267 = 1434401) B1434401
theorem B956279 : Blo 952587 956279 := bstep (se 1 (by rfl) ⟨717209, by rfl⟩ : syracuseStep 956279 = 1434419) B1434419
theorem B956299 : Blo 952587 956299 := bstep (se 1 (by rfl) ⟨717224, by rfl⟩ : syracuseStep 956299 = 1434449) B1434449
theorem B956311 : Blo 952587 956311 := bstep (se 1 (by rfl) ⟨717233, by rfl⟩ : syracuseStep 956311 = 1434467) B1434467
theorem B956331 : Blo 952587 956331 := bstep (se 1 (by rfl) ⟨717248, by rfl⟩ : syracuseStep 956331 = 1434497) B1434497
theorem B956343 : Blo 952587 956343 := bstep (se 1 (by rfl) ⟨717257, by rfl⟩ : syracuseStep 956343 = 1434515) B1434515
theorem B956363 : Blo 952587 956363 := bstep (se 1 (by rfl) ⟨717272, by rfl⟩ : syracuseStep 956363 = 1434545) B1434545
theorem B956375 : Blo 952587 956375 := bstep (se 1 (by rfl) ⟨717281, by rfl⟩ : syracuseStep 956375 = 1434563) B1434563
theorem B3217373 : Blo 952587 3217373 := bstep (se 3 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 3217373 = 1206515) B1206515
theorem B956395 : Blo 952587 956395 := bstep (se 1 (by rfl) ⟨717296, by rfl⟩ : syracuseStep 956395 = 1434593) B1434593
theorem B956407 : Blo 952587 956407 := bstep (se 1 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 956407 = 1434611) B1434611
theorem B956427 : Blo 952587 956427 := bstep (se 1 (by rfl) ⟨717320, by rfl⟩ : syracuseStep 956427 = 1434641) B1434641
theorem B3872785 : Blo 952587 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B956439 : Blo 952587 956439 := bstep (se 1 (by rfl) ⟨717329, by rfl⟩ : syracuseStep 956439 = 1434659) B1434659
theorem B956459 : Blo 952587 956459 := bstep (se 1 (by rfl) ⟨717344, by rfl⟩ : syracuseStep 956459 = 1434689) B1434689
theorem B956471 : Blo 952587 956471 := bstep (se 1 (by rfl) ⟨717353, by rfl⟩ : syracuseStep 956471 = 1434707) B1434707
theorem B956491 : Blo 952587 956491 := bstep (se 1 (by rfl) ⟨717368, by rfl⟩ : syracuseStep 956491 = 1434737) B1434737
theorem B956503 : Blo 952587 956503 := bstep (se 1 (by rfl) ⟨717377, by rfl⟩ : syracuseStep 956503 = 1434755) B1434755
theorem B3446873 : Blo 952587 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B956523 : Blo 952587 956523 := bstep (se 1 (by rfl) ⟨717392, by rfl⟩ : syracuseStep 956523 = 1434785) B1434785
theorem B956535 : Blo 952587 956535 := bstep (se 1 (by rfl) ⟨717401, by rfl⟩ : syracuseStep 956535 = 1434803) B1434803
theorem B956555 : Blo 952587 956555 := bstep (se 1 (by rfl) ⟨717416, by rfl⟩ : syracuseStep 956555 = 1434833) B1434833
theorem B956567 : Blo 952587 956567 := bstep (se 1 (by rfl) ⟨717425, by rfl⟩ : syracuseStep 956567 = 1434851) B1434851
theorem B956587 : Blo 952587 956587 := bstep (se 1 (by rfl) ⟨717440, by rfl⟩ : syracuseStep 956587 = 1434881) B1434881
theorem B2037977 : Blo 952587 2037977 := bstep (se 2 (by rfl) ⟨764241, by rfl⟩ : syracuseStep 2037977 = 1528483) B1528483
theorem B4069597 : Blo 952587 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B6527249 : Blo 952587 6527249 := bstep (se 2 (by rfl) ⟨2447718, by rfl⟩ : syracuseStep 6527249 = 4895437) B4895437
theorem B1612055 : Blo 952587 1612055 := bstep (se 1 (by rfl) ⟨1209041, by rfl⟩ : syracuseStep 1612055 = 2418083) B2418083
theorem B9181505 : Blo 952587 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B7248203 : Blo 952587 7248203 := bstep (se 1 (by rfl) ⟨5436152, by rfl⟩ : syracuseStep 7248203 = 10872305) B10872305
theorem B1612183 : Blo 952587 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B4069939 : Blo 952587 4069939 := bstep (se 1 (by rfl) ⟨3052454, by rfl⟩ : syracuseStep 4069939 = 6104909) B6104909
theorem B1808983 : Blo 952587 1808983 := bstep (se 1 (by rfl) ⟨1356737, by rfl⟩ : syracuseStep 1808983 = 2713475) B2713475
theorem B2038387 : Blo 952587 2038387 := bstep (se 1 (by rfl) ⟨1528790, by rfl⟩ : syracuseStep 2038387 = 3057581) B3057581
theorem B1448651 : Blo 952587 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B5806865 : Blo 952587 5806865 := bstep (se 2 (by rfl) ⟨2177574, by rfl⟩ : syracuseStep 5806865 = 4355149) B4355149
theorem B3873581 : Blo 952587 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B4823873 : Blo 952587 4823873 := bstep (se 2 (by rfl) ⟨1808952, by rfl⟩ : syracuseStep 4823873 = 3617905) B3617905
theorem B1612811 : Blo 952587 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B3218507 : Blo 952587 3218507 := bstep (se 1 (by rfl) ⟨2413880, by rfl⟩ : syracuseStep 3218507 = 4827761) B4827761
theorem B1088587 : Blo 952587 1088587 := bstep (se 1 (by rfl) ⟨816440, by rfl⟩ : syracuseStep 1088587 = 1632881) B1632881
theorem B3054685 : Blo 952587 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B1612939 : Blo 952587 1612939 := bstep (se 1 (by rfl) ⟨1209704, by rfl⟩ : syracuseStep 1612939 = 2419409) B2419409
theorem B1613081 : Blo 952587 1613081 := bstep (se 2 (by rfl) ⟨604905, by rfl⟩ : syracuseStep 1613081 = 1209811) B1209811
theorem B3218777 : Blo 952587 3218777 := bstep (se 2 (by rfl) ⟨1207041, by rfl⟩ : syracuseStep 3218777 = 2414083) B2414083
theorem B1809803 : Blo 952587 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B1613209 : Blo 952587 1613209 := bstep (se 2 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 1613209 = 1209907) B1209907
theorem B1809857 : Blo 952587 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B2039575 : Blo 952587 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1089335 : Blo 952587 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B2039617 : Blo 952587 2039617 := bstep (se 2 (by rfl) ⟨764856, by rfl⟩ : syracuseStep 2039617 = 1529713) B1529713
theorem B47652785 : Blo 952587 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B1613783 : Blo 952587 1613783 := bstep (se 1 (by rfl) ⟨1210337, by rfl⟩ : syracuseStep 1613783 = 2420675) B2420675
theorem B3219479 : Blo 952587 3219479 := bstep (se 1 (by rfl) ⟨2414609, by rfl⟩ : syracuseStep 3219479 = 4829219) B4829219
theorem B1613911 : Blo 952587 1613911 := bstep (se 1 (by rfl) ⟨1210433, by rfl⟩ : syracuseStep 1613911 = 2420867) B2420867
theorem B1810775 : Blo 952587 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B3220019 : Blo 952587 3220019 := bstep (se 1 (by rfl) ⟨2415014, by rfl⟩ : syracuseStep 3220019 = 4830029) B4830029
theorem B4825817 : Blo 952587 4825817 := bstep (se 2 (by rfl) ⟨1809681, by rfl⟩ : syracuseStep 4825817 = 3619363) B3619363
theorem B3220289 : Blo 952587 3220289 := bstep (se 2 (by rfl) ⟨1207608, by rfl⟩ : syracuseStep 3220289 = 2415217) B2415217
theorem B1811315 : Blo 952587 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B12231755 : Blo 952587 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B10888343 : Blo 952587 10888343 := bstep (se 1 (by rfl) ⟨8166257, by rfl⟩ : syracuseStep 10888343 = 16332515) B16332515
theorem B41329925 : Blo 952587 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B1811801 : Blo 952587 1811801 := bstep (se 2 (by rfl) ⟨679425, by rfl⟩ : syracuseStep 1811801 = 1358851) B1358851
theorem B3220829 : Blo 952587 3220829 := bstep (se 3 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 3220829 = 1207811) B1207811
theorem B2041291 : Blo 952587 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B13608461 : Blo 952587 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B2041625 : Blo 952587 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B26158913 : Blo 952587 26158913 := bstep (se 2 (by rfl) ⟨9809592, by rfl⟩ : syracuseStep 26158913 = 19619185) B19619185
theorem B4073561 : Blo 952587 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B17410229 : Blo 952587 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B4827437 : Blo 952587 4827437 := bstep (se 3 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 4827437 = 1810289) B1810289
theorem B3221963 : Blo 952587 3221963 := bstep (se 1 (by rfl) ⟨2416472, by rfl⟩ : syracuseStep 3221963 = 4832945) B4832945
theorem B8170085 : Blo 952587 8170085 := bstep (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) B1531891
theorem B3222233 : Blo 952587 3222233 := bstep (se 2 (by rfl) ⟨1208337, by rfl⟩ : syracuseStep 3222233 = 2416675) B2416675
theorem B1813259 : Blo 952587 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B7744301 : Blo 952587 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5155649 : Blo 952587 5155649 := bstep (se 2 (by rfl) ⟨1933368, by rfl⟩ : syracuseStep 5155649 = 3866737) B3866737
theorem B1813441 : Blo 952587 1813441 := bstep (se 2 (by rfl) ⟨680040, by rfl⟩ : syracuseStep 1813441 = 1360081) B1360081
theorem B3681587 : Blo 952587 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B1813889 : Blo 952587 1813889 := bstep (se 2 (by rfl) ⟨680208, by rfl⟩ : syracuseStep 1813889 = 1360417) B1360417
theorem B6106499 : Blo 952587 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B3222935 : Blo 952587 3222935 := bstep (se 1 (by rfl) ⟨2417201, by rfl⟩ : syracuseStep 3222935 = 4834403) B4834403
theorem B7253549 : Blo 952587 7253549 := bstep (se 3 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 7253549 = 2720081) B2720081
theorem B4075201 : Blo 952587 4075201 := bstep (se 2 (by rfl) ⟨1528200, by rfl⟩ : syracuseStep 4075201 = 3056401) B3056401
theorem B1814231 : Blo 952587 1814231 := bstep (se 1 (by rfl) ⟨1360673, by rfl⟩ : syracuseStep 1814231 = 2721347) B2721347
theorem B3223475 : Blo 952587 3223475 := bstep (se 1 (by rfl) ⟨2417606, by rfl⟩ : syracuseStep 3223475 = 4835213) B4835213
theorem B2240627 : Blo 952587 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B3616919 : Blo 952587 3616919 := bstep (se 1 (by rfl) ⟨2712689, by rfl⟩ : syracuseStep 3616919 = 5425379) B5425379
theorem B3223745 : Blo 952587 3223745 := bstep (se 2 (by rfl) ⟨1208904, by rfl⟩ : syracuseStep 3223745 = 2417809) B2417809
theorem B8171725 : Blo 952587 8171725 := bstep (se 3 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 8171725 = 3064397) B3064397
theorem B1290583 : Blo 952587 1290583 := bstep (se 1 (by rfl) ⟨967937, by rfl⟩ : syracuseStep 1290583 = 1935875) B1935875
theorem B1814899 : Blo 952587 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B3060119 : Blo 952587 3060119 := bstep (se 1 (by rfl) ⟨2295089, by rfl⟩ : syracuseStep 3060119 = 4590179) B4590179
theorem B1716761 : Blo 952587 1716761 := bstep (se 2 (by rfl) ⟨643785, by rfl⟩ : syracuseStep 1716761 = 1287571) B1287571
theorem B4141747 : Blo 952587 4141747 := bstep (se 1 (by rfl) ⟨3106310, by rfl⟩ : syracuseStep 4141747 = 6212621) B6212621
theorem B3224285 : Blo 952587 3224285 := bstep (se 3 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 3224285 = 1209107) B1209107
theorem B1815347 : Blo 952587 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B1815385 : Blo 952587 1815385 := bstep (se 2 (by rfl) ⟨680769, by rfl⟩ : syracuseStep 1815385 = 1361539) B1361539
theorem B7844701 : Blo 952587 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B4076689 : Blo 952587 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B2143385 : Blo 952587 2143385 := bstep (se 2 (by rfl) ⟨803769, by rfl⟩ : syracuseStep 2143385 = 1607539) B1607539
theorem B2143475 : Blo 952587 2143475 := bstep (se 1 (by rfl) ⟨1607606, by rfl⟩ : syracuseStep 2143475 = 3215213) B3215213
theorem B2143511 : Blo 952587 2143511 := bstep (se 1 (by rfl) ⟨1607633, by rfl⟩ : syracuseStep 2143511 = 3215267) B3215267
theorem B1357079 : Blo 952587 1357079 := bstep (se 1 (by rfl) ⟨1017809, by rfl⟩ : syracuseStep 1357079 = 2035619) B2035619
theorem B1815833 : Blo 952587 1815833 := bstep (se 2 (by rfl) ⟨680937, by rfl⟩ : syracuseStep 1815833 = 1361875) B1361875
theorem B3618179 : Blo 952587 3618179 := bstep (se 1 (by rfl) ⟨2713634, by rfl⟩ : syracuseStep 3618179 = 5427269) B5427269
theorem B2143691 : Blo 952587 2143691 := bstep (se 1 (by rfl) ⟨1607768, by rfl⟩ : syracuseStep 2143691 = 3215537) B3215537
theorem B1357273 : Blo 952587 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B2143745 : Blo 952587 2143745 := bstep (se 2 (by rfl) ⟨803904, by rfl⟩ : syracuseStep 2143745 = 1607809) B1607809
theorem B8697419 : Blo 952587 8697419 := bstep (se 1 (by rfl) ⟨6523064, by rfl⟩ : syracuseStep 8697419 = 13046129) B13046129
theorem B3061451 : Blo 952587 3061451 := bstep (se 1 (by rfl) ⟨2296088, by rfl⟩ : syracuseStep 3061451 = 4592177) B4592177
theorem B2143961 : Blo 952587 2143961 := bstep (se 2 (by rfl) ⟨803985, by rfl⟩ : syracuseStep 2143961 = 1607971) B1607971
theorem B1291993 : Blo 952587 1291993 := bstep (se 2 (by rfl) ⟨484497, by rfl⟩ : syracuseStep 1291993 = 968995) B968995
theorem B2144051 : Blo 952587 2144051 := bstep (se 1 (by rfl) ⟨1608038, by rfl⟩ : syracuseStep 2144051 = 3216077) B3216077
theorem B3225419 : Blo 952587 3225419 := bstep (se 1 (by rfl) ⟨2419064, by rfl⟩ : syracuseStep 3225419 = 4838129) B4838129
theorem B2144087 : Blo 952587 2144087 := bstep (se 1 (by rfl) ⟨1608065, by rfl⟩ : syracuseStep 2144087 = 3216131) B3216131
theorem B1259479 : Blo 952587 1259479 := bstep (se 1 (by rfl) ⟨944609, by rfl⟩ : syracuseStep 1259479 = 1889219) B1889219
theorem B2144267 : Blo 952587 2144267 := bstep (se 1 (by rfl) ⟨1608200, by rfl⟩ : syracuseStep 2144267 = 3216401) B3216401
theorem B2144321 : Blo 952587 2144321 := bstep (se 2 (by rfl) ⟨804120, by rfl⟩ : syracuseStep 2144321 = 1608241) B1608241
theorem B3225689 : Blo 952587 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B4831325 : Blo 952587 4831325 := bstep (se 3 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 4831325 = 1811747) B1811747
theorem B2144537 : Blo 952587 2144537 := bstep (se 2 (by rfl) ⟨804201, by rfl⟩ : syracuseStep 2144537 = 1608403) B1608403
theorem B2144627 : Blo 952587 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B2144663 : Blo 952587 2144663 := bstep (se 1 (by rfl) ⟨1608497, by rfl⟩ : syracuseStep 2144663 = 3216995) B3216995
theorem B1718707 : Blo 952587 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B3062195 : Blo 952587 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B1292761 : Blo 952587 1292761 := bstep (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) B969571
theorem B1718795 : Blo 952587 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B2898497 : Blo 952587 2898497 := bstep (se 2 (by rfl) ⟨1086936, by rfl⟩ : syracuseStep 2898497 = 2173873) B2173873
theorem B2144843 : Blo 952587 2144843 := bstep (se 1 (by rfl) ⟨1608632, by rfl⟩ : syracuseStep 2144843 = 3217265) B3217265
theorem B44022365 : Blo 952587 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B2144897 : Blo 952587 2144897 := bstep (se 2 (by rfl) ⟨804336, by rfl⟩ : syracuseStep 2144897 = 1608673) B1608673
theorem B3226391 : Blo 952587 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B2145113 : Blo 952587 2145113 := bstep (se 2 (by rfl) ⟨804417, by rfl⟩ : syracuseStep 2145113 = 1608835) B1608835
theorem B7748453 : Blo 952587 7748453 := bstep (se 4 (by rfl) ⟨726417, by rfl⟩ : syracuseStep 7748453 = 1452835) B1452835
theorem B1358731 : Blo 952587 1358731 := bstep (se 1 (by rfl) ⟨1019048, by rfl⟩ : syracuseStep 1358731 = 2038097) B2038097
theorem B2145203 : Blo 952587 2145203 := bstep (se 1 (by rfl) ⟨1608902, by rfl⟩ : syracuseStep 2145203 = 3217805) B3217805
theorem B2145239 : Blo 952587 2145239 := bstep (se 1 (by rfl) ⟨1608929, by rfl⟩ : syracuseStep 2145239 = 3217859) B3217859
theorem B2145419 : Blo 952587 2145419 := bstep (se 1 (by rfl) ⟨1609064, by rfl⟩ : syracuseStep 2145419 = 3218129) B3218129
theorem B2145473 : Blo 952587 2145473 := bstep (se 2 (by rfl) ⟨804552, by rfl⟩ : syracuseStep 2145473 = 1609105) B1609105
theorem B3226931 : Blo 952587 3226931 := bstep (se 1 (by rfl) ⟨2420198, by rfl⟩ : syracuseStep 3226931 = 4840397) B4840397
theorem B3063091 : Blo 952587 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B7257437 : Blo 952587 7257437 := bstep (se 3 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 7257437 = 2721539) B2721539
theorem B2145689 : Blo 952587 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B9780659 : Blo 952587 9780659 := bstep (se 1 (by rfl) ⟨7335494, by rfl⟩ : syracuseStep 9780659 = 14670989) B14670989
theorem B2145779 : Blo 952587 2145779 := bstep (se 1 (by rfl) ⟨1609334, by rfl⟩ : syracuseStep 2145779 = 3218669) B3218669
theorem B2145815 : Blo 952587 2145815 := bstep (se 1 (by rfl) ⟨1609361, by rfl⟩ : syracuseStep 2145815 = 3218723) B3218723
theorem B3227201 : Blo 952587 3227201 := bstep (se 2 (by rfl) ⟨1210200, by rfl⟩ : syracuseStep 3227201 = 2420401) B2420401
theorem B2145995 : Blo 952587 2145995 := bstep (se 1 (by rfl) ⟨1609496, by rfl⟩ : syracuseStep 2145995 = 3218993) B3218993
theorem B2146049 : Blo 952587 2146049 := bstep (se 2 (by rfl) ⟨804768, by rfl⟩ : syracuseStep 2146049 = 1609537) B1609537
theorem B2146265 : Blo 952587 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B2146355 : Blo 952587 2146355 := bstep (se 1 (by rfl) ⟨1609766, by rfl⟩ : syracuseStep 2146355 = 3219533) B3219533
theorem B1032247 : Blo 952587 1032247 := bstep (se 1 (by rfl) ⟨774185, by rfl⟩ : syracuseStep 1032247 = 1548371) B1548371
theorem B2146391 : Blo 952587 2146391 := bstep (se 1 (by rfl) ⟨1609793, by rfl⟩ : syracuseStep 2146391 = 3219587) B3219587
theorem B3227741 : Blo 952587 3227741 := bstep (se 3 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 3227741 = 1210403) B1210403
theorem B4079747 : Blo 952587 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B4833431 : Blo 952587 4833431 := bstep (se 1 (by rfl) ⟨3625073, by rfl⟩ : syracuseStep 4833431 = 7250147) B7250147
theorem B2146571 : Blo 952587 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B2146625 : Blo 952587 2146625 := bstep (se 2 (by rfl) ⟨804984, by rfl⟩ : syracuseStep 2146625 = 1609969) B1609969
theorem B3621293 : Blo 952587 3621293 := bstep (se 3 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 3621293 = 1357985) B1357985
theorem B2146841 : Blo 952587 2146841 := bstep (se 2 (by rfl) ⟨805065, by rfl⟩ : syracuseStep 2146841 = 1610131) B1610131
theorem B2146931 : Blo 952587 2146931 := bstep (se 1 (by rfl) ⟨1610198, by rfl⟩ : syracuseStep 2146931 = 3220397) B3220397
theorem B2146967 : Blo 952587 2146967 := bstep (se 1 (by rfl) ⟨1610225, by rfl⟩ : syracuseStep 2146967 = 3220451) B3220451
theorem B27509453 : Blo 952587 27509453 := bstep (se 3 (by rfl) ⟨5158022, by rfl⟩ : syracuseStep 27509453 = 10316045) B10316045
theorem B2147147 : Blo 952587 2147147 := bstep (se 1 (by rfl) ⟨1610360, by rfl⟩ : syracuseStep 2147147 = 3220721) B3220721
theorem B2147201 : Blo 952587 2147201 := bstep (se 2 (by rfl) ⟨805200, by rfl⟩ : syracuseStep 2147201 = 1610401) B1610401
theorem B2147417 : Blo 952587 2147417 := bstep (se 2 (by rfl) ⟨805281, by rfl⟩ : syracuseStep 2147417 = 1610563) B1610563
theorem B3622067 : Blo 952587 3622067 := bstep (se 1 (by rfl) ⟨2716550, by rfl⟩ : syracuseStep 3622067 = 5433101) B5433101
theorem B2147507 : Blo 952587 2147507 := bstep (se 1 (by rfl) ⟨1610630, by rfl⟩ : syracuseStep 2147507 = 3221261) B3221261
theorem B2147543 : Blo 952587 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B2901341 : Blo 952587 2901341 := bstep (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) B1088003
theorem B2147723 : Blo 952587 2147723 := bstep (se 1 (by rfl) ⟨1610792, by rfl⟩ : syracuseStep 2147723 = 3221585) B3221585
theorem B2147777 : Blo 952587 2147777 := bstep (se 2 (by rfl) ⟨805416, by rfl⟩ : syracuseStep 2147777 = 1610833) B1610833
theorem B1033879 : Blo 952587 1033879 := bstep (se 1 (by rfl) ⟨775409, by rfl⟩ : syracuseStep 1033879 = 1550819) B1550819
theorem B2147993 : Blo 952587 2147993 := bstep (se 2 (by rfl) ⟨805497, by rfl⟩ : syracuseStep 2147993 = 1610995) B1610995
theorem B2148083 : Blo 952587 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B2148119 : Blo 952587 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B2180951 : Blo 952587 2180951 := bstep (se 1 (by rfl) ⟨1635713, by rfl⟩ : syracuseStep 2180951 = 3271427) B3271427
theorem B3262301 : Blo 952587 3262301 := bstep (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) B1223363
theorem B2148299 : Blo 952587 2148299 := bstep (se 1 (by rfl) ⟨1611224, by rfl⟩ : syracuseStep 2148299 = 3222449) B3222449
theorem B2148353 : Blo 952587 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B2148569 : Blo 952587 2148569 := bstep (se 2 (by rfl) ⟨805713, by rfl⟩ : syracuseStep 2148569 = 1611427) B1611427
theorem B2148659 : Blo 952587 2148659 := bstep (se 1 (by rfl) ⟨1611494, by rfl⟩ : syracuseStep 2148659 = 3222989) B3222989
theorem B2148695 : Blo 952587 2148695 := bstep (se 1 (by rfl) ⟨1611521, by rfl⟩ : syracuseStep 2148695 = 3223043) B3223043
theorem B2148875 : Blo 952587 2148875 := bstep (se 1 (by rfl) ⟨1611656, by rfl⟩ : syracuseStep 2148875 = 3223313) B3223313
theorem B2148929 : Blo 952587 2148929 := bstep (se 2 (by rfl) ⟨805848, by rfl⟩ : syracuseStep 2148929 = 1611697) B1611697
theorem B3623555 : Blo 952587 3623555 := bstep (se 1 (by rfl) ⟨2717666, by rfl⟩ : syracuseStep 3623555 = 5435333) B5435333
theorem B2149145 : Blo 952587 2149145 := bstep (se 2 (by rfl) ⟨805929, by rfl⟩ : syracuseStep 2149145 = 1611859) B1611859
theorem B2411329 : Blo 952587 2411329 := bstep (se 2 (by rfl) ⟨904248, by rfl⟩ : syracuseStep 2411329 = 1808497) B1808497
theorem B2149235 : Blo 952587 2149235 := bstep (se 1 (by rfl) ⟨1611926, by rfl⟩ : syracuseStep 2149235 = 3223853) B3223853
theorem B2149271 : Blo 952587 2149271 := bstep (se 1 (by rfl) ⟨1611953, by rfl⟩ : syracuseStep 2149271 = 3223907) B3223907
theorem B2149451 : Blo 952587 2149451 := bstep (se 1 (by rfl) ⟨1612088, by rfl⟩ : syracuseStep 2149451 = 3224177) B3224177
theorem B3624011 : Blo 952587 3624011 := bstep (se 1 (by rfl) ⟨2718008, by rfl⟩ : syracuseStep 3624011 = 5436017) B5436017
theorem B2149505 : Blo 952587 2149505 := bstep (se 2 (by rfl) ⟨806064, by rfl⟩ : syracuseStep 2149505 = 1612129) B1612129
theorem B1723609 : Blo 952587 1723609 := bstep (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) B1292707
theorem B3624209 : Blo 952587 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B2149721 : Blo 952587 2149721 := bstep (se 2 (by rfl) ⟨806145, by rfl⟩ : syracuseStep 2149721 = 1612291) B1612291
theorem B1428887 : Blo 952587 1428887 := bstep (se 1 (by rfl) ⟨1071665, by rfl⟩ : syracuseStep 1428887 = 2143331) B2143331
theorem B2411927 : Blo 952587 2411927 := bstep (se 1 (by rfl) ⟨1808945, by rfl⟩ : syracuseStep 2411927 = 3617891) B3617891
theorem B2149811 : Blo 952587 2149811 := bstep (se 1 (by rfl) ⟨1612358, by rfl⟩ : syracuseStep 2149811 = 3224717) B3224717
theorem B2149847 : Blo 952587 2149847 := bstep (se 1 (by rfl) ⟨1612385, by rfl⟩ : syracuseStep 2149847 = 3224771) B3224771
theorem B1428953 : Blo 952587 1428953 := bstep (se 2 (by rfl) ⟨535857, by rfl⟩ : syracuseStep 1428953 = 1071715) B1071715
theorem B1429067 : Blo 952587 1429067 := bstep (se 1 (by rfl) ⟨1071800, by rfl⟩ : syracuseStep 1429067 = 2143601) B2143601
theorem B1429079 : Blo 952587 1429079 := bstep (se 1 (by rfl) ⟨1071809, by rfl⟩ : syracuseStep 1429079 = 2143619) B2143619
theorem B4836995 : Blo 952587 4836995 := bstep (se 1 (by rfl) ⟨3627746, by rfl⟩ : syracuseStep 4836995 = 7255493) B7255493
theorem B2150027 : Blo 952587 2150027 := bstep (se 1 (by rfl) ⟨1612520, by rfl⟩ : syracuseStep 2150027 = 3225041) B3225041
theorem B1429145 : Blo 952587 1429145 := bstep (se 2 (by rfl) ⟨535929, by rfl⟩ : syracuseStep 1429145 = 1071859) B1071859
theorem B2150081 : Blo 952587 2150081 := bstep (se 2 (by rfl) ⟨806280, by rfl⟩ : syracuseStep 2150081 = 1612561) B1612561
theorem B1429259 : Blo 952587 1429259 := bstep (se 1 (by rfl) ⟨1071944, by rfl⟩ : syracuseStep 1429259 = 2143889) B2143889
theorem B235523861 : Blo 952587 235523861 := bstep (se 6 (by rfl) ⟨5520090, by rfl⟩ : syracuseStep 235523861 = 11040181) B11040181
theorem B1429271 : Blo 952587 1429271 := bstep (se 1 (by rfl) ⟨1071953, by rfl⟩ : syracuseStep 1429271 = 2143907) B2143907
theorem B1429337 : Blo 952587 1429337 := bstep (se 2 (by rfl) ⟨536001, by rfl⟩ : syracuseStep 1429337 = 1072003) B1072003
theorem B2150297 : Blo 952587 2150297 := bstep (se 2 (by rfl) ⟨806361, by rfl⟩ : syracuseStep 2150297 = 1612723) B1612723
theorem B1429451 : Blo 952587 1429451 := bstep (se 1 (by rfl) ⟨1072088, by rfl⟩ : syracuseStep 1429451 = 2144177) B2144177
theorem B1429463 : Blo 952587 1429463 := bstep (se 1 (by rfl) ⟨1072097, by rfl⟩ : syracuseStep 1429463 = 2144195) B2144195
theorem B2150387 : Blo 952587 2150387 := bstep (se 1 (by rfl) ⟨1612790, by rfl⟩ : syracuseStep 2150387 = 3225581) B3225581
theorem B3624983 : Blo 952587 3624983 := bstep (se 1 (by rfl) ⟨2718737, by rfl⟩ : syracuseStep 3624983 = 5437475) B5437475
theorem B2150423 : Blo 952587 2150423 := bstep (se 1 (by rfl) ⟨1612817, by rfl⟩ : syracuseStep 2150423 = 3225635) B3225635
theorem B1429529 : Blo 952587 1429529 := bstep (se 2 (by rfl) ⟨536073, by rfl⟩ : syracuseStep 1429529 = 1072147) B1072147
theorem B1429643 : Blo 952587 1429643 := bstep (se 1 (by rfl) ⟨1072232, by rfl⟩ : syracuseStep 1429643 = 2144465) B2144465
theorem B1429655 : Blo 952587 1429655 := bstep (se 1 (by rfl) ⟨1072241, by rfl⟩ : syracuseStep 1429655 = 2144483) B2144483
theorem B5165207 : Blo 952587 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B2412737 : Blo 952587 2412737 := bstep (se 2 (by rfl) ⟨904776, by rfl⟩ : syracuseStep 2412737 = 1809553) B1809553
theorem B2150603 : Blo 952587 2150603 := bstep (se 1 (by rfl) ⟨1612952, by rfl⟩ : syracuseStep 2150603 = 3225905) B3225905
theorem B1429721 : Blo 952587 1429721 := bstep (se 2 (by rfl) ⟨536145, by rfl⟩ : syracuseStep 1429721 = 1072291) B1072291
theorem B3625181 : Blo 952587 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B2150657 : Blo 952587 2150657 := bstep (se 2 (by rfl) ⟨806496, by rfl⟩ : syracuseStep 2150657 = 1612993) B1612993
theorem B4084019 : Blo 952587 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B3494195 : Blo 952587 3494195 := bstep (se 1 (by rfl) ⟨2620646, by rfl⟩ : syracuseStep 3494195 = 5241293) B5241293
theorem B1429835 : Blo 952587 1429835 := bstep (se 1 (by rfl) ⟨1072376, by rfl⟩ : syracuseStep 1429835 = 2144753) B2144753
theorem B1429847 : Blo 952587 1429847 := bstep (se 1 (by rfl) ⟨1072385, by rfl⟩ : syracuseStep 1429847 = 2144771) B2144771
theorem B5427587 : Blo 952587 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B1429913 : Blo 952587 1429913 := bstep (se 2 (by rfl) ⟨536217, by rfl⟩ : syracuseStep 1429913 = 1072435) B1072435
theorem B2150873 : Blo 952587 2150873 := bstep (se 2 (by rfl) ⟨806577, by rfl⟩ : syracuseStep 2150873 = 1613155) B1613155
theorem B1430027 : Blo 952587 1430027 := bstep (se 1 (by rfl) ⟨1072520, by rfl⟩ : syracuseStep 1430027 = 2145041) B2145041
theorem B1430039 : Blo 952587 1430039 := bstep (se 1 (by rfl) ⟨1072529, by rfl⟩ : syracuseStep 1430039 = 2145059) B2145059
theorem B2150963 : Blo 952587 2150963 := bstep (se 1 (by rfl) ⟨1613222, by rfl⟩ : syracuseStep 2150963 = 3226445) B3226445
theorem B2150999 : Blo 952587 2150999 := bstep (se 1 (by rfl) ⟨1613249, by rfl⟩ : syracuseStep 2150999 = 3226499) B3226499
theorem B1430105 : Blo 952587 1430105 := bstep (se 2 (by rfl) ⟨536289, by rfl⟩ : syracuseStep 1430105 = 1072579) B1072579
theorem B1430219 : Blo 952587 1430219 := bstep (se 1 (by rfl) ⟨1072664, by rfl⟩ : syracuseStep 1430219 = 2145329) B2145329
theorem B1430231 : Blo 952587 1430231 := bstep (se 1 (by rfl) ⟨1072673, by rfl⟩ : syracuseStep 1430231 = 2145347) B2145347
theorem B2413273 : Blo 952587 2413273 := bstep (se 2 (by rfl) ⟨904977, by rfl⟩ : syracuseStep 2413273 = 1809955) B1809955
theorem B2151179 : Blo 952587 2151179 := bstep (se 1 (by rfl) ⟨1613384, by rfl⟩ : syracuseStep 2151179 = 3226769) B3226769
theorem B1430297 : Blo 952587 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B2511667 : Blo 952587 2511667 := bstep (se 1 (by rfl) ⟨1883750, by rfl⟩ : syracuseStep 2511667 = 3767501) B3767501
theorem B2151233 : Blo 952587 2151233 := bstep (se 2 (by rfl) ⟨806712, by rfl⟩ : syracuseStep 2151233 = 1613425) B1613425
theorem B5428043 : Blo 952587 5428043 := bstep (se 1 (by rfl) ⟨4071032, by rfl⟩ : syracuseStep 5428043 = 8142065) B8142065
theorem B1430411 : Blo 952587 1430411 := bstep (se 1 (by rfl) ⟨1072808, by rfl⟩ : syracuseStep 1430411 = 2145617) B2145617
theorem B1430423 : Blo 952587 1430423 := bstep (se 1 (by rfl) ⟨1072817, by rfl⟩ : syracuseStep 1430423 = 2145635) B2145635
theorem B1430489 : Blo 952587 1430489 := bstep (se 2 (by rfl) ⟨536433, by rfl⟩ : syracuseStep 1430489 = 1072867) B1072867
theorem B2151449 : Blo 952587 2151449 := bstep (se 2 (by rfl) ⟨806793, by rfl⟩ : syracuseStep 2151449 = 1613587) B1613587
theorem B1430603 : Blo 952587 1430603 := bstep (se 1 (by rfl) ⟨1072952, by rfl⟩ : syracuseStep 1430603 = 2145905) B2145905
theorem B1430615 : Blo 952587 1430615 := bstep (se 1 (by rfl) ⟨1072961, by rfl⟩ : syracuseStep 1430615 = 2145923) B2145923
theorem B2151539 : Blo 952587 2151539 := bstep (se 1 (by rfl) ⟨1613654, by rfl⟩ : syracuseStep 2151539 = 3227309) B3227309
theorem B2446487 : Blo 952587 2446487 := bstep (se 1 (by rfl) ⟨1834865, by rfl⟩ : syracuseStep 2446487 = 3669731) B3669731
theorem B2151575 : Blo 952587 2151575 := bstep (se 1 (by rfl) ⟨1613681, by rfl⟩ : syracuseStep 2151575 = 3227363) B3227363
theorem B1430681 : Blo 952587 1430681 := bstep (se 2 (by rfl) ⟨536505, by rfl⟩ : syracuseStep 1430681 = 1073011) B1073011
theorem B1529047 : Blo 952587 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B7165189 : Blo 952587 7165189 := bstep (se 4 (by rfl) ⟨671736, by rfl⟩ : syracuseStep 7165189 = 1343473) B1343473
theorem B1430795 : Blo 952587 1430795 := bstep (se 1 (by rfl) ⟨1073096, by rfl⟩ : syracuseStep 1430795 = 2146193) B2146193
theorem B1430807 : Blo 952587 1430807 := bstep (se 1 (by rfl) ⟨1073105, by rfl⟩ : syracuseStep 1430807 = 2146211) B2146211
theorem B2905367 : Blo 952587 2905367 := bstep (se 1 (by rfl) ⟨2179025, by rfl⟩ : syracuseStep 2905367 = 4358051) B4358051
theorem B2151755 : Blo 952587 2151755 := bstep (se 1 (by rfl) ⟨1613816, by rfl⟩ : syracuseStep 2151755 = 3227633) B3227633
theorem B1430873 : Blo 952587 1430873 := bstep (se 2 (by rfl) ⟨536577, by rfl⟩ : syracuseStep 1430873 = 1073155) B1073155
theorem B2151809 : Blo 952587 2151809 := bstep (se 2 (by rfl) ⟨806928, by rfl⟩ : syracuseStep 2151809 = 1613857) B1613857
theorem B1430987 : Blo 952587 1430987 := bstep (se 1 (by rfl) ⟨1073240, by rfl⟩ : syracuseStep 1430987 = 2146481) B2146481
theorem B1430999 : Blo 952587 1430999 := bstep (se 1 (by rfl) ⟨1073249, by rfl⟩ : syracuseStep 1430999 = 2146499) B2146499
theorem B1431065 : Blo 952587 1431065 := bstep (se 2 (by rfl) ⟨536649, by rfl⟩ : syracuseStep 1431065 = 1073299) B1073299
theorem B2152025 : Blo 952587 2152025 := bstep (se 2 (by rfl) ⟨807009, by rfl⟩ : syracuseStep 2152025 = 1614019) B1614019
theorem B6116957 : Blo 952587 6116957 := bstep (se 3 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 6116957 = 2293859) B2293859
theorem B1431179 : Blo 952587 1431179 := bstep (se 1 (by rfl) ⟨1073384, by rfl⟩ : syracuseStep 1431179 = 2146769) B2146769
theorem B1431191 : Blo 952587 1431191 := bstep (se 1 (by rfl) ⟨1073393, by rfl⟩ : syracuseStep 1431191 = 2146787) B2146787
theorem B2152115 : Blo 952587 2152115 := bstep (se 1 (by rfl) ⟨1614086, by rfl⟩ : syracuseStep 2152115 = 3228173) B3228173
theorem B2152151 : Blo 952587 2152151 := bstep (se 1 (by rfl) ⟨1614113, by rfl⟩ : syracuseStep 2152151 = 3228227) B3228227
theorem B1431257 : Blo 952587 1431257 := bstep (se 2 (by rfl) ⟨536721, by rfl⟩ : syracuseStep 1431257 = 1073443) B1073443
theorem B2414387 : Blo 952587 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B1431371 : Blo 952587 1431371 := bstep (se 1 (by rfl) ⟨1073528, by rfl⟩ : syracuseStep 1431371 = 2147057) B2147057
theorem B1431383 : Blo 952587 1431383 := bstep (se 1 (by rfl) ⟨1073537, by rfl⟩ : syracuseStep 1431383 = 2147075) B2147075
theorem B1431449 : Blo 952587 1431449 := bstep (se 2 (by rfl) ⟨536793, by rfl⟩ : syracuseStep 1431449 = 1073587) B1073587
theorem B1529803 : Blo 952587 1529803 := bstep (se 1 (by rfl) ⟨1147352, by rfl⟩ : syracuseStep 1529803 = 2294705) B2294705
theorem B1431563 : Blo 952587 1431563 := bstep (se 1 (by rfl) ⟨1073672, by rfl⟩ : syracuseStep 1431563 = 2147345) B2147345
theorem B1529867 : Blo 952587 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B1431575 : Blo 952587 1431575 := bstep (se 1 (by rfl) ⟨1073681, by rfl⟩ : syracuseStep 1431575 = 2147363) B2147363
theorem B2414681 : Blo 952587 2414681 := bstep (se 2 (by rfl) ⟨905505, by rfl⟩ : syracuseStep 2414681 = 1811011) B1811011
theorem B1431641 : Blo 952587 1431641 := bstep (se 2 (by rfl) ⟨536865, by rfl⟩ : syracuseStep 1431641 = 1073731) B1073731
theorem B3627139 : Blo 952587 3627139 := bstep (se 1 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 3627139 = 5440709) B5440709
theorem B1529995 : Blo 952587 1529995 := bstep (se 1 (by rfl) ⟨1147496, by rfl⟩ : syracuseStep 1529995 = 2294993) B2294993
theorem B2578625 : Blo 952587 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B1431755 : Blo 952587 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B1431767 : Blo 952587 1431767 := bstep (se 1 (by rfl) ⟨1073825, by rfl⟩ : syracuseStep 1431767 = 2147651) B2147651
theorem B1431833 : Blo 952587 1431833 := bstep (se 2 (by rfl) ⟨536937, by rfl⟩ : syracuseStep 1431833 = 1073875) B1073875
theorem B1431947 : Blo 952587 1431947 := bstep (se 1 (by rfl) ⟨1073960, by rfl⟩ : syracuseStep 1431947 = 2147921) B2147921
theorem B1431959 : Blo 952587 1431959 := bstep (se 1 (by rfl) ⟨1073969, by rfl⟩ : syracuseStep 1431959 = 2147939) B2147939
theorem B11164081 : Blo 952587 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B3627443 : Blo 952587 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B1432025 : Blo 952587 1432025 := bstep (se 2 (by rfl) ⟨537009, by rfl⟩ : syracuseStep 1432025 = 1074019) B1074019
theorem B14703065 : Blo 952587 14703065 := bstep (se 2 (by rfl) ⟨5513649, by rfl⟩ : syracuseStep 14703065 = 11027299) B11027299
theorem B1432139 : Blo 952587 1432139 := bstep (se 1 (by rfl) ⟨1074104, by rfl⟩ : syracuseStep 1432139 = 2148209) B2148209
theorem B1432151 : Blo 952587 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B1432217 : Blo 952587 1432217 := bstep (se 2 (by rfl) ⟨537081, by rfl⟩ : syracuseStep 1432217 = 1074163) B1074163
theorem B1071787 : Blo 952587 1071787 := bstep (se 1 (by rfl) ⟨803840, by rfl⟩ : syracuseStep 1071787 = 1607681) B1607681
theorem B1432331 : Blo 952587 1432331 := bstep (se 1 (by rfl) ⟨1074248, by rfl⟩ : syracuseStep 1432331 = 2148497) B2148497
theorem B1071895 : Blo 952587 1071895 := bstep (se 1 (by rfl) ⟨803921, by rfl⟩ : syracuseStep 1071895 = 1607843) B1607843
theorem B1432343 : Blo 952587 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1432409 : Blo 952587 1432409 := bstep (se 2 (by rfl) ⟨537153, by rfl⟩ : syracuseStep 1432409 = 1074307) B1074307
theorem B1530713 : Blo 952587 1530713 := bstep (se 2 (by rfl) ⟨574017, by rfl⟩ : syracuseStep 1530713 = 1148035) B1148035
theorem B1072075 : Blo 952587 1072075 := bstep (se 1 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 1072075 = 1608113) B1608113
theorem B1432523 : Blo 952587 1432523 := bstep (se 1 (by rfl) ⟨1074392, by rfl⟩ : syracuseStep 1432523 = 2148785) B2148785
theorem B1432535 : Blo 952587 1432535 := bstep (se 1 (by rfl) ⟨1074401, by rfl⟩ : syracuseStep 1432535 = 2148803) B2148803
theorem B1530841 : Blo 952587 1530841 := bstep (se 2 (by rfl) ⟨574065, by rfl⟩ : syracuseStep 1530841 = 1148131) B1148131
theorem B1432601 : Blo 952587 1432601 := bstep (se 2 (by rfl) ⟨537225, by rfl⟩ : syracuseStep 1432601 = 1074451) B1074451
theorem B1072183 : Blo 952587 1072183 := bstep (se 1 (by rfl) ⟨804137, by rfl⟩ : syracuseStep 1072183 = 1608275) B1608275
theorem B3628097 : Blo 952587 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B9165899 : Blo 952587 9165899 := bstep (se 1 (by rfl) ⟨6874424, by rfl⟩ : syracuseStep 9165899 = 13748849) B13748849
theorem B1432715 : Blo 952587 1432715 := bstep (se 1 (by rfl) ⟨1074536, by rfl⟩ : syracuseStep 1432715 = 2149073) B2149073
theorem B1432727 : Blo 952587 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B1432793 : Blo 952587 1432793 := bstep (se 2 (by rfl) ⟨537297, by rfl⟩ : syracuseStep 1432793 = 1074595) B1074595
theorem B1072363 : Blo 952587 1072363 := bstep (se 1 (by rfl) ⟨804272, by rfl⟩ : syracuseStep 1072363 = 1608545) B1608545
theorem B4840721 : Blo 952587 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B1432907 : Blo 952587 1432907 := bstep (se 1 (by rfl) ⟨1074680, by rfl⟩ : syracuseStep 1432907 = 2149361) B2149361
theorem B1072471 : Blo 952587 1072471 := bstep (se 1 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 1072471 = 1608707) B1608707
theorem B1432919 : Blo 952587 1432919 := bstep (se 1 (by rfl) ⟨1074689, by rfl⟩ : syracuseStep 1432919 = 2149379) B2149379
theorem B1531225 : Blo 952587 1531225 := bstep (se 2 (by rfl) ⟨574209, by rfl⟩ : syracuseStep 1531225 = 1148419) B1148419
theorem B1432985 : Blo 952587 1432985 := bstep (se 2 (by rfl) ⟨537369, by rfl⟩ : syracuseStep 1432985 = 1074739) B1074739
theorem B4840883 : Blo 952587 4840883 := bstep (se 1 (by rfl) ⟨3630662, by rfl⟩ : syracuseStep 4840883 = 7261325) B7261325
theorem B1072651 : Blo 952587 1072651 := bstep (se 1 (by rfl) ⟨804488, by rfl⟩ : syracuseStep 1072651 = 1608977) B1608977
theorem B1433099 : Blo 952587 1433099 := bstep (se 1 (by rfl) ⟨1074824, by rfl⟩ : syracuseStep 1433099 = 2149649) B2149649
theorem B1433111 : Blo 952587 1433111 := bstep (se 1 (by rfl) ⟨1074833, by rfl⟩ : syracuseStep 1433111 = 2149667) B2149667
theorem B1433177 : Blo 952587 1433177 := bstep (se 2 (by rfl) ⟨537441, by rfl⟩ : syracuseStep 1433177 = 1074883) B1074883
theorem B1531481 : Blo 952587 1531481 := bstep (se 2 (by rfl) ⟨574305, by rfl⟩ : syracuseStep 1531481 = 1148611) B1148611
theorem B4349533 : Blo 952587 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B1072759 : Blo 952587 1072759 := bstep (se 1 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 1072759 = 1609139) B1609139
theorem B2416331 : Blo 952587 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B1433291 : Blo 952587 1433291 := bstep (se 1 (by rfl) ⟨1074968, by rfl⟩ : syracuseStep 1433291 = 2149937) B2149937
theorem B1433303 : Blo 952587 1433303 := bstep (se 1 (by rfl) ⟨1074977, by rfl⟩ : syracuseStep 1433303 = 2149955) B2149955
theorem B1433369 : Blo 952587 1433369 := bstep (se 2 (by rfl) ⟨537513, by rfl⟩ : syracuseStep 1433369 = 1075027) B1075027
theorem B1072939 : Blo 952587 1072939 := bstep (se 1 (by rfl) ⟨804704, by rfl⟩ : syracuseStep 1072939 = 1609409) B1609409
theorem B4349747 : Blo 952587 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B1433483 : Blo 952587 1433483 := bstep (se 1 (by rfl) ⟨1075112, by rfl⟩ : syracuseStep 1433483 = 2150225) B2150225
theorem B1073047 : Blo 952587 1073047 := bstep (se 1 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 1073047 = 1609571) B1609571
theorem B1433495 : Blo 952587 1433495 := bstep (se 1 (by rfl) ⟨1075121, by rfl⟩ : syracuseStep 1433495 = 2150243) B2150243
theorem B1433561 : Blo 952587 1433561 := bstep (se 2 (by rfl) ⟨537585, by rfl⟩ : syracuseStep 1433561 = 1075171) B1075171
theorem B4579373 : Blo 952587 4579373 := bstep (se 3 (by rfl) ⟨858632, by rfl⟩ : syracuseStep 4579373 = 1717265) B1717265
theorem B1073227 : Blo 952587 1073227 := bstep (se 1 (by rfl) ⟨804920, by rfl⟩ : syracuseStep 1073227 = 1609841) B1609841
theorem B1433675 : Blo 952587 1433675 := bstep (se 1 (by rfl) ⟨1075256, by rfl⟩ : syracuseStep 1433675 = 2150513) B2150513
theorem B1433687 : Blo 952587 1433687 := bstep (se 1 (by rfl) ⟨1075265, by rfl⟩ : syracuseStep 1433687 = 2150531) B2150531
theorem B8151191 : Blo 952587 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1433753 : Blo 952587 1433753 := bstep (se 2 (by rfl) ⟨537657, by rfl⟩ : syracuseStep 1433753 = 1075315) B1075315
theorem B1073335 : Blo 952587 1073335 := bstep (se 1 (by rfl) ⟨805001, by rfl⟩ : syracuseStep 1073335 = 1610003) B1610003
theorem B1433867 : Blo 952587 1433867 := bstep (se 1 (by rfl) ⟨1075400, by rfl⟩ : syracuseStep 1433867 = 2150801) B2150801
theorem B1433879 : Blo 952587 1433879 := bstep (se 1 (by rfl) ⟨1075409, by rfl⟩ : syracuseStep 1433879 = 2150819) B2150819
theorem B13066541 : Blo 952587 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B3629357 : Blo 952587 3629357 := bstep (se 3 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 3629357 = 1361009) B1361009
theorem B3629387 : Blo 952587 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B1433945 : Blo 952587 1433945 := bstep (se 2 (by rfl) ⟨537729, by rfl⟩ : syracuseStep 1433945 = 1075459) B1075459
theorem B1073515 : Blo 952587 1073515 := bstep (se 1 (by rfl) ⟨805136, by rfl⟩ : syracuseStep 1073515 = 1610273) B1610273
theorem B16310645 : Blo 952587 16310645 := bstep (se 5 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 16310645 = 1529123) B1529123
theorem B1434059 : Blo 952587 1434059 := bstep (se 1 (by rfl) ⟨1075544, by rfl⟩ : syracuseStep 1434059 = 2151089) B2151089
theorem B1073623 : Blo 952587 1073623 := bstep (se 1 (by rfl) ⟨805217, by rfl⟩ : syracuseStep 1073623 = 1610435) B1610435
theorem B1434071 : Blo 952587 1434071 := bstep (se 1 (by rfl) ⟨1075553, by rfl⟩ : syracuseStep 1434071 = 2151107) B2151107
theorem B1434137 : Blo 952587 1434137 := bstep (se 2 (by rfl) ⟨537801, by rfl⟩ : syracuseStep 1434137 = 1075603) B1075603
theorem B1073803 : Blo 952587 1073803 := bstep (se 1 (by rfl) ⟨805352, by rfl⟩ : syracuseStep 1073803 = 1610705) B1610705
theorem B1434251 : Blo 952587 1434251 := bstep (se 1 (by rfl) ⟨1075688, by rfl⟩ : syracuseStep 1434251 = 2151377) B2151377
theorem B2417303 : Blo 952587 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B1434263 : Blo 952587 1434263 := bstep (se 1 (by rfl) ⟨1075697, by rfl⟩ : syracuseStep 1434263 = 2151395) B2151395
theorem B1630937 : Blo 952587 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B1434329 : Blo 952587 1434329 := bstep (se 2 (by rfl) ⟨537873, by rfl⟩ : syracuseStep 1434329 = 1075747) B1075747
theorem B1073911 : Blo 952587 1073911 := bstep (se 1 (by rfl) ⟨805433, by rfl⟩ : syracuseStep 1073911 = 1610867) B1610867
theorem B1434443 : Blo 952587 1434443 := bstep (se 1 (by rfl) ⟨1075832, by rfl⟩ : syracuseStep 1434443 = 2151665) B2151665
theorem B1434455 : Blo 952587 1434455 := bstep (se 1 (by rfl) ⟨1075841, by rfl⟩ : syracuseStep 1434455 = 2151683) B2151683
theorem B1434521 : Blo 952587 1434521 := bstep (se 2 (by rfl) ⟨537945, by rfl⟩ : syracuseStep 1434521 = 1075891) B1075891
theorem B1074091 : Blo 952587 1074091 := bstep (se 1 (by rfl) ⟨805568, by rfl⟩ : syracuseStep 1074091 = 1611137) B1611137
theorem B3630041 : Blo 952587 3630041 := bstep (se 2 (by rfl) ⟨1361265, by rfl⟩ : syracuseStep 3630041 = 2722531) B2722531
theorem B1434635 : Blo 952587 1434635 := bstep (se 1 (by rfl) ⟨1075976, by rfl⟩ : syracuseStep 1434635 = 2151953) B2151953
theorem B1074199 : Blo 952587 1074199 := bstep (se 1 (by rfl) ⟨805649, by rfl⟩ : syracuseStep 1074199 = 1611299) B1611299
theorem B1434647 : Blo 952587 1434647 := bstep (se 1 (by rfl) ⟨1075985, by rfl⟩ : syracuseStep 1434647 = 2151971) B2151971
theorem B7234595 : Blo 952587 7234595 := bstep (se 1 (by rfl) ⟨5425946, by rfl⟩ : syracuseStep 7234595 = 10851893) B10851893
theorem B1434713 : Blo 952587 1434713 := bstep (se 2 (by rfl) ⟨538017, by rfl⟩ : syracuseStep 1434713 = 1076035) B1076035
theorem B1959041 : Blo 952587 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B12412055 : Blo 952587 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B1074379 : Blo 952587 1074379 := bstep (se 1 (by rfl) ⟨805784, by rfl⟩ : syracuseStep 1074379 = 1611569) B1611569
theorem B1434827 : Blo 952587 1434827 := bstep (se 1 (by rfl) ⟨1076120, by rfl⟩ : syracuseStep 1434827 = 2152241) B2152241
theorem B1434839 : Blo 952587 1434839 := bstep (se 1 (by rfl) ⟨1076129, by rfl⟩ : syracuseStep 1434839 = 2152259) B2152259
theorem B3630359 : Blo 952587 3630359 := bstep (se 1 (by rfl) ⟨2722769, by rfl⟩ : syracuseStep 3630359 = 5445539) B5445539
theorem B2417971 : Blo 952587 2417971 := bstep (se 1 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 2417971 = 3626957) B3626957
theorem B1074487 : Blo 952587 1074487 := bstep (se 1 (by rfl) ⟨805865, by rfl⟩ : syracuseStep 1074487 = 1611731) B1611731
theorem B5432669 : Blo 952587 5432669 := bstep (se 3 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 5432669 = 2037251) B2037251
theorem B2418113 : Blo 952587 2418113 := bstep (se 2 (by rfl) ⟨906792, by rfl⟩ : syracuseStep 2418113 = 1813585) B1813585
theorem B1074667 : Blo 952587 1074667 := bstep (se 1 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 1074667 = 1612001) B1612001
theorem B1074775 : Blo 952587 1074775 := bstep (se 1 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 1074775 = 1612163) B1612163
theorem B1074955 : Blo 952587 1074955 := bstep (se 1 (by rfl) ⟨806216, by rfl⟩ : syracuseStep 1074955 = 1612433) B1612433
theorem B1075063 : Blo 952587 1075063 := bstep (se 1 (by rfl) ⟨806297, by rfl⟩ : syracuseStep 1075063 = 1612595) B1612595
theorem B6875057 : Blo 952587 6875057 := bstep (se 2 (by rfl) ⟨2578146, by rfl⟩ : syracuseStep 6875057 = 5156293) B5156293
theorem B3631027 : Blo 952587 3631027 := bstep (se 1 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 3631027 = 5446541) B5446541
theorem B1075243 : Blo 952587 1075243 := bstep (se 1 (by rfl) ⟨806432, by rfl⟩ : syracuseStep 1075243 = 1612865) B1612865
theorem B5433419 : Blo 952587 5433419 := bstep (se 1 (by rfl) ⟨4075064, by rfl⟩ : syracuseStep 5433419 = 8150129) B8150129
theorem B11626571 : Blo 952587 11626571 := bstep (se 1 (by rfl) ⟨8719928, by rfl⟩ : syracuseStep 11626571 = 17439857) B17439857
theorem B13789277 : Blo 952587 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B1075351 : Blo 952587 1075351 := bstep (se 1 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 1075351 = 1613027) B1613027
theorem B2713817 : Blo 952587 2713817 := bstep (se 2 (by rfl) ⟨1017681, by rfl⟩ : syracuseStep 2713817 = 2035363) B2035363
theorem B1861913 : Blo 952587 1861913 := bstep (se 2 (by rfl) ⟨698217, by rfl⟩ : syracuseStep 1861913 = 1396435) B1396435
theorem B2713931 : Blo 952587 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B1075531 : Blo 952587 1075531 := bstep (se 1 (by rfl) ⟨806648, by rfl⟩ : syracuseStep 1075531 = 1613297) B1613297
theorem B1206667 : Blo 952587 1206667 := bstep (se 1 (by rfl) ⟨905000, by rfl⟩ : syracuseStep 1206667 = 1810001) B1810001
theorem B1075639 : Blo 952587 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B1075819 : Blo 952587 1075819 := bstep (se 1 (by rfl) ⟨806864, by rfl⟩ : syracuseStep 1075819 = 1613729) B1613729
theorem B11168387 : Blo 952587 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B2419379 : Blo 952587 2419379 := bstep (se 1 (by rfl) ⟨1814534, by rfl⟩ : syracuseStep 2419379 = 3629069) B3629069
theorem B1239767 : Blo 952587 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B1075927 : Blo 952587 1075927 := bstep (se 1 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 1075927 = 1613891) B1613891
theorem B55896803 : Blo 952587 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B1076107 : Blo 952587 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B19557445 : Blo 952587 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B4713547 : Blo 952587 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B2419915 : Blo 952587 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B6188305 : Blo 952587 6188305 := bstep (se 2 (by rfl) ⟨2320614, by rfl⟩ : syracuseStep 6188305 = 4641229) B4641229
theorem B1207639 : Blo 952587 1207639 := bstep (se 1 (by rfl) ⟨905729, by rfl⟩ : syracuseStep 1207639 = 1811459) B1811459
theorem B2420057 : Blo 952587 2420057 := bstep (se 2 (by rfl) ⟨907521, by rfl⟩ : syracuseStep 2420057 = 1815043) B1815043
theorem B2715059 : Blo 952587 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B6123053 : Blo 952587 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B5435059 : Blo 952587 5435059 := bstep (se 1 (by rfl) ⟨4076294, by rfl⟩ : syracuseStep 5435059 = 8152589) B8152589
theorem B7728961 : Blo 952587 7728961 := bstep (se 2 (by rfl) ⟨2898360, by rfl⟩ : syracuseStep 7728961 = 5796721) B5796721
theorem B2715457 : Blo 952587 2715457 := bstep (se 2 (by rfl) ⟨1018296, by rfl⟩ : syracuseStep 2715457 = 2036593) B2036593
theorem B6877021 : Blo 952587 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B7729253 : Blo 952587 7729253 := bstep (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) B1449235
theorem B1208459 : Blo 952587 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B2420887 : Blo 952587 2420887 := bstep (se 1 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 2420887 = 3631331) B3631331
theorem B4583603 : Blo 952587 4583603 := bstep (se 1 (by rfl) ⟨3437702, by rfl⟩ : syracuseStep 4583603 = 6875405) B6875405
theorem B5796161 : Blo 952587 5796161 := bstep (se 2 (by rfl) ⟨2173560, by rfl⟩ : syracuseStep 5796161 = 4347121) B4347121
theorem B2421323 : Blo 952587 2421323 := bstep (se 1 (by rfl) ⟨1815992, by rfl⟩ : syracuseStep 2421323 = 3631985) B3631985
theorem B2290265 : Blo 952587 2290265 := bstep (se 2 (by rfl) ⟨858849, by rfl⟩ : syracuseStep 2290265 = 1717699) B1717699
theorem B2585239 : Blo 952587 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B1209163 : Blo 952587 1209163 := bstep (se 1 (by rfl) ⟨906872, by rfl⟩ : syracuseStep 1209163 = 1813745) B1813745
theorem B1209431 : Blo 952587 1209431 := bstep (se 1 (by rfl) ⟨907073, by rfl⟩ : syracuseStep 1209431 = 1814147) B1814147
theorem B5436517 : Blo 952587 5436517 := bstep (se 4 (by rfl) ⟨509673, by rfl⟩ : syracuseStep 5436517 = 1019347) B1019347
theorem B4355479 : Blo 952587 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B1144459 : Blo 952587 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B1210135 : Blo 952587 1210135 := bstep (se 1 (by rfl) ⟨907601, by rfl⟩ : syracuseStep 1210135 = 1815203) B1815203
theorem B8156963 : Blo 952587 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B1963955 : Blo 952587 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B6125719 : Blo 952587 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B4356299 : Blo 952587 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B5798105 : Blo 952587 5798105 := bstep (se 2 (by rfl) ⟨2174289, by rfl⟩ : syracuseStep 5798105 = 4348579) B4348579
theorem B4356317 : Blo 952587 4356317 := bstep (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) B1633619
theorem B7239941 : Blo 952587 7239941 := bstep (se 4 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 7239941 = 1357489) B1357489
theorem B2717975 : Blo 952587 2717975 := bstep (se 1 (by rfl) ⟨2038481, by rfl⟩ : syracuseStep 2717975 = 4076963) B4076963
theorem B2062721 : Blo 952587 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B11008547 : Blo 952587 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B16284401 : Blo 952587 16284401 := bstep (se 2 (by rfl) ⟨6106650, by rfl⟩ : syracuseStep 16284401 = 12213301) B12213301
theorem B2620505 : Blo 952587 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B5504321 : Blo 952587 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B1146199 : Blo 952587 1146199 := bstep (se 1 (by rfl) ⟨859649, by rfl⟩ : syracuseStep 1146199 = 1719299) B1719299
theorem B13762061 : Blo 952587 13762061 := bstep (se 3 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 13762061 = 5160773) B5160773
theorem B2719307 : Blo 952587 2719307 := bstep (se 1 (by rfl) ⟨2039480, by rfl⟩ : syracuseStep 2719307 = 4078961) B4078961
theorem B982603 : Blo 952587 982603 := bstep (se 1 (by rfl) ⟨736952, by rfl⟩ : syracuseStep 982603 = 1473905) B1473905
theorem B4128587 : Blo 952587 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B2064217 : Blo 952587 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B2719831 : Blo 952587 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B5505317 : Blo 952587 5505317 := bstep (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) B1032247
theorem B9175355 : Blo 952587 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B5440391 : Blo 952587 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B1934227 : Blo 952587 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B5506627 : Blo 952587 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B1378505 : Blo 952587 1378505 := bstep (se 2 (by rfl) ⟨516939, by rfl⟩ : syracuseStep 1378505 = 1033879) B1033879
theorem B952591 : Blo 952587 952591 := bstep (se 1 (by rfl) ⟨714443, by rfl⟩ : syracuseStep 952591 = 1428887) B1428887
theorem B1607951 : Blo 952587 1607951 := bstep (se 1 (by rfl) ⟨1205963, by rfl⟩ : syracuseStep 1607951 = 2411927) B2411927
theorem B952635 : Blo 952587 952635 := bstep (se 1 (by rfl) ⟨714476, by rfl⟩ : syracuseStep 952635 = 1428953) B1428953
theorem B952711 : Blo 952587 952711 := bstep (se 1 (by rfl) ⟨714533, by rfl⟩ : syracuseStep 952711 = 1429067) B1429067
theorem B952719 : Blo 952587 952719 := bstep (se 1 (by rfl) ⟨714539, by rfl⟩ : syracuseStep 952719 = 1429079) B1429079
theorem B952763 : Blo 952587 952763 := bstep (se 1 (by rfl) ⟨714572, by rfl⟩ : syracuseStep 952763 = 1429145) B1429145
theorem B1837513 : Blo 952587 1837513 := bstep (se 2 (by rfl) ⟨689067, by rfl⟩ : syracuseStep 1837513 = 1378135) B1378135
theorem B5507531 : Blo 952587 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B952839 : Blo 952587 952839 := bstep (se 1 (by rfl) ⟨714629, by rfl⟩ : syracuseStep 952839 = 1429259) B1429259
theorem B952847 : Blo 952587 952847 := bstep (se 1 (by rfl) ⟨714635, by rfl⟩ : syracuseStep 952847 = 1429271) B1429271
theorem B952891 : Blo 952587 952891 := bstep (se 1 (by rfl) ⟨714668, by rfl⟩ : syracuseStep 952891 = 1429337) B1429337
theorem B5442167 : Blo 952587 5442167 := bstep (se 1 (by rfl) ⟨4081625, by rfl⟩ : syracuseStep 5442167 = 8163251) B8163251
theorem B952967 : Blo 952587 952967 := bstep (se 1 (by rfl) ⟨714725, by rfl⟩ : syracuseStep 952967 = 1429451) B1429451
theorem B952975 : Blo 952587 952975 := bstep (se 1 (by rfl) ⟨714731, by rfl⟩ : syracuseStep 952975 = 1429463) B1429463
theorem B953019 : Blo 952587 953019 := bstep (se 1 (by rfl) ⟨714764, by rfl⟩ : syracuseStep 953019 = 1429529) B1429529
theorem B953095 : Blo 952587 953095 := bstep (se 1 (by rfl) ⟨714821, by rfl⟩ : syracuseStep 953095 = 1429643) B1429643
theorem B953103 : Blo 952587 953103 := bstep (se 1 (by rfl) ⟨714827, by rfl⟩ : syracuseStep 953103 = 1429655) B1429655
theorem B3443471 : Blo 952587 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B1608491 : Blo 952587 1608491 := bstep (se 1 (by rfl) ⟨1206368, by rfl⟩ : syracuseStep 1608491 = 2412737) B2412737
theorem B953147 : Blo 952587 953147 := bstep (se 1 (by rfl) ⟨714860, by rfl⟩ : syracuseStep 953147 = 1429721) B1429721
theorem B2722679 : Blo 952587 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B2329463 : Blo 952587 2329463 := bstep (se 1 (by rfl) ⟨1747097, by rfl⟩ : syracuseStep 2329463 = 3494195) B3494195
theorem B953223 : Blo 952587 953223 := bstep (se 1 (by rfl) ⟨714917, by rfl⟩ : syracuseStep 953223 = 1429835) B1429835
theorem B953231 : Blo 952587 953231 := bstep (se 1 (by rfl) ⟨714923, by rfl⟩ : syracuseStep 953231 = 1429847) B1429847
theorem B953275 : Blo 952587 953275 := bstep (se 1 (by rfl) ⟨714956, by rfl⟩ : syracuseStep 953275 = 1429913) B1429913
theorem B953351 : Blo 952587 953351 := bstep (se 1 (by rfl) ⟨715013, by rfl⟩ : syracuseStep 953351 = 1430027) B1430027
theorem B953359 : Blo 952587 953359 := bstep (se 1 (by rfl) ⟨715019, by rfl⟩ : syracuseStep 953359 = 1430039) B1430039
theorem B953403 : Blo 952587 953403 := bstep (se 1 (by rfl) ⟨715052, by rfl⟩ : syracuseStep 953403 = 1430105) B1430105
theorem B953479 : Blo 952587 953479 := bstep (se 1 (by rfl) ⟨715109, by rfl⟩ : syracuseStep 953479 = 1430219) B1430219
theorem B953487 : Blo 952587 953487 := bstep (se 1 (by rfl) ⟨715115, by rfl⟩ : syracuseStep 953487 = 1430231) B1430231
theorem B55151765 : Blo 952587 55151765 := bstep (se 6 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 55151765 = 2585239) B2585239
theorem B1608889 : Blo 952587 1608889 := bstep (se 2 (by rfl) ⟨603333, by rfl⟩ : syracuseStep 1608889 = 1206667) B1206667
theorem B953531 : Blo 952587 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B953607 : Blo 952587 953607 := bstep (se 1 (by rfl) ⟨715205, by rfl⟩ : syracuseStep 953607 = 1430411) B1430411
theorem B953615 : Blo 952587 953615 := bstep (se 1 (by rfl) ⟨715211, by rfl⟩ : syracuseStep 953615 = 1430423) B1430423
theorem B953659 : Blo 952587 953659 := bstep (se 1 (by rfl) ⟨715244, by rfl⟩ : syracuseStep 953659 = 1430489) B1430489
theorem B3870011 : Blo 952587 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B5442875 : Blo 952587 5442875 := bstep (se 1 (by rfl) ⟨4082156, by rfl⟩ : syracuseStep 5442875 = 8164313) B8164313
theorem B953735 : Blo 952587 953735 := bstep (se 1 (by rfl) ⟨715301, by rfl⟩ : syracuseStep 953735 = 1430603) B1430603
theorem B953743 : Blo 952587 953743 := bstep (se 1 (by rfl) ⟨715307, by rfl⟩ : syracuseStep 953743 = 1430615) B1430615
theorem B953787 : Blo 952587 953787 := bstep (se 1 (by rfl) ⟨715340, by rfl⟩ : syracuseStep 953787 = 1430681) B1430681
theorem B953863 : Blo 952587 953863 := bstep (se 1 (by rfl) ⟨715397, by rfl⟩ : syracuseStep 953863 = 1430795) B1430795
theorem B953871 : Blo 952587 953871 := bstep (se 1 (by rfl) ⟨715403, by rfl⟩ : syracuseStep 953871 = 1430807) B1430807
theorem B2035243 : Blo 952587 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B953915 : Blo 952587 953915 := bstep (se 1 (by rfl) ⟨715436, by rfl⟩ : syracuseStep 953915 = 1430873) B1430873
theorem B953991 : Blo 952587 953991 := bstep (se 1 (by rfl) ⟨715493, by rfl⟩ : syracuseStep 953991 = 1430987) B1430987
theorem B953999 : Blo 952587 953999 := bstep (se 1 (by rfl) ⟨715499, by rfl⟩ : syracuseStep 953999 = 1430999) B1430999
theorem B954043 : Blo 952587 954043 := bstep (se 1 (by rfl) ⟨715532, by rfl⟩ : syracuseStep 954043 = 1431065) B1431065
theorem B3215105 : Blo 952587 3215105 := bstep (se 2 (by rfl) ⟨1205664, by rfl⟩ : syracuseStep 3215105 = 2411329) B2411329
theorem B954119 : Blo 952587 954119 := bstep (se 1 (by rfl) ⟨715589, by rfl⟩ : syracuseStep 954119 = 1431179) B1431179
theorem B954127 : Blo 952587 954127 := bstep (se 1 (by rfl) ⟨715595, by rfl⟩ : syracuseStep 954127 = 1431191) B1431191
theorem B954171 : Blo 952587 954171 := bstep (se 1 (by rfl) ⟨715628, by rfl⟩ : syracuseStep 954171 = 1431257) B1431257
theorem B1609591 : Blo 952587 1609591 := bstep (se 1 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 1609591 = 2414387) B2414387
theorem B954247 : Blo 952587 954247 := bstep (se 1 (by rfl) ⟨715685, by rfl⟩ : syracuseStep 954247 = 1431371) B1431371
theorem B954255 : Blo 952587 954255 := bstep (se 1 (by rfl) ⟨715691, by rfl⟩ : syracuseStep 954255 = 1431383) B1431383
theorem B4591505 : Blo 952587 4591505 := bstep (se 2 (by rfl) ⟨1721814, by rfl⟩ : syracuseStep 4591505 = 3443629) B3443629
theorem B954299 : Blo 952587 954299 := bstep (se 1 (by rfl) ⟨715724, by rfl⟩ : syracuseStep 954299 = 1431449) B1431449
theorem B954375 : Blo 952587 954375 := bstep (se 1 (by rfl) ⟨715781, by rfl⟩ : syracuseStep 954375 = 1431563) B1431563
theorem B954383 : Blo 952587 954383 := bstep (se 1 (by rfl) ⟨715787, by rfl⟩ : syracuseStep 954383 = 1431575) B1431575
theorem B1609787 : Blo 952587 1609787 := bstep (se 1 (by rfl) ⟨1207340, by rfl⟩ : syracuseStep 1609787 = 2414681) B2414681
theorem B954427 : Blo 952587 954427 := bstep (se 1 (by rfl) ⟨715820, by rfl⟩ : syracuseStep 954427 = 1431641) B1431641
theorem B2297915 : Blo 952587 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B954503 : Blo 952587 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B954511 : Blo 952587 954511 := bstep (se 1 (by rfl) ⟨715883, by rfl⟩ : syracuseStep 954511 = 1431767) B1431767
theorem B954555 : Blo 952587 954555 := bstep (se 1 (by rfl) ⟨715916, by rfl⟩ : syracuseStep 954555 = 1431833) B1431833
theorem B954631 : Blo 952587 954631 := bstep (se 1 (by rfl) ⟨715973, by rfl⟩ : syracuseStep 954631 = 1431947) B1431947
theorem B954639 : Blo 952587 954639 := bstep (se 1 (by rfl) ⟨715979, by rfl⟩ : syracuseStep 954639 = 1431959) B1431959
theorem B2298145 : Blo 952587 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B954683 : Blo 952587 954683 := bstep (se 1 (by rfl) ⟨716012, by rfl⟩ : syracuseStep 954683 = 1432025) B1432025
theorem B9802043 : Blo 952587 9802043 := bstep (se 1 (by rfl) ⟨7351532, by rfl⟩ : syracuseStep 9802043 = 14703065) B14703065
theorem B954759 : Blo 952587 954759 := bstep (se 1 (by rfl) ⟨716069, by rfl⟩ : syracuseStep 954759 = 1432139) B1432139
theorem B954767 : Blo 952587 954767 := bstep (se 1 (by rfl) ⟨716075, by rfl⟩ : syracuseStep 954767 = 1432151) B1432151
theorem B954811 : Blo 952587 954811 := bstep (se 1 (by rfl) ⟨716108, by rfl⟩ : syracuseStep 954811 = 1432217) B1432217
theorem B1610185 : Blo 952587 1610185 := bstep (se 2 (by rfl) ⟨603819, by rfl⟩ : syracuseStep 1610185 = 1207639) B1207639
theorem B954887 : Blo 952587 954887 := bstep (se 1 (by rfl) ⟨716165, by rfl⟩ : syracuseStep 954887 = 1432331) B1432331
theorem B3871243 : Blo 952587 3871243 := bstep (se 1 (by rfl) ⟨2903432, by rfl⟩ : syracuseStep 3871243 = 5806865) B5806865
theorem B954895 : Blo 952587 954895 := bstep (se 1 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 954895 = 1432343) B1432343
theorem B3215915 : Blo 952587 3215915 := bstep (se 1 (by rfl) ⟨2411936, by rfl⟩ : syracuseStep 3215915 = 4823873) B4823873
theorem B954939 : Blo 952587 954939 := bstep (se 1 (by rfl) ⟨716204, by rfl⟩ : syracuseStep 954939 = 1432409) B1432409
theorem B1020475 : Blo 952587 1020475 := bstep (se 1 (by rfl) ⟨765356, by rfl⟩ : syracuseStep 1020475 = 1530713) B1530713
theorem B955015 : Blo 952587 955015 := bstep (se 1 (by rfl) ⟨716261, by rfl⟩ : syracuseStep 955015 = 1432523) B1432523
theorem B955023 : Blo 952587 955023 := bstep (se 1 (by rfl) ⟨716267, by rfl⟩ : syracuseStep 955023 = 1432535) B1432535
theorem B955067 : Blo 952587 955067 := bstep (se 1 (by rfl) ⟨716300, by rfl⟩ : syracuseStep 955067 = 1432601) B1432601
theorem B5444333 : Blo 952587 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B955143 : Blo 952587 955143 := bstep (se 1 (by rfl) ⟨716357, by rfl⟩ : syracuseStep 955143 = 1432715) B1432715
theorem B955151 : Blo 952587 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B955195 : Blo 952587 955195 := bstep (se 1 (by rfl) ⟨716396, by rfl⟩ : syracuseStep 955195 = 1432793) B1432793
theorem B955271 : Blo 952587 955271 := bstep (se 1 (by rfl) ⟨716453, by rfl⟩ : syracuseStep 955271 = 1432907) B1432907
theorem B955279 : Blo 952587 955279 := bstep (se 1 (by rfl) ⟨716459, by rfl⟩ : syracuseStep 955279 = 1432919) B1432919
theorem B7246745 : Blo 952587 7246745 := bstep (se 2 (by rfl) ⟨2717529, by rfl⟩ : syracuseStep 7246745 = 5435059) B5435059
theorem B955323 : Blo 952587 955323 := bstep (se 1 (by rfl) ⟨716492, by rfl⟩ : syracuseStep 955323 = 1432985) B1432985
theorem B955399 : Blo 952587 955399 := bstep (se 1 (by rfl) ⟨716549, by rfl⟩ : syracuseStep 955399 = 1433099) B1433099
theorem B955407 : Blo 952587 955407 := bstep (se 1 (by rfl) ⟨716555, by rfl⟩ : syracuseStep 955407 = 1433111) B1433111
theorem B955451 : Blo 952587 955451 := bstep (se 1 (by rfl) ⟨716588, by rfl⟩ : syracuseStep 955451 = 1433177) B1433177
theorem B1610887 : Blo 952587 1610887 := bstep (se 1 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 1610887 = 2416331) B2416331
theorem B955527 : Blo 952587 955527 := bstep (se 1 (by rfl) ⟨716645, by rfl⟩ : syracuseStep 955527 = 1433291) B1433291
theorem B955535 : Blo 952587 955535 := bstep (se 1 (by rfl) ⟨716651, by rfl⟩ : syracuseStep 955535 = 1433303) B1433303
theorem B955579 : Blo 952587 955579 := bstep (se 1 (by rfl) ⟨716684, by rfl⟩ : syracuseStep 955579 = 1433369) B1433369
theorem B955655 : Blo 952587 955655 := bstep (se 1 (by rfl) ⟨716741, by rfl⟩ : syracuseStep 955655 = 1433483) B1433483
theorem B955663 : Blo 952587 955663 := bstep (se 1 (by rfl) ⟨716747, by rfl⟩ : syracuseStep 955663 = 1433495) B1433495
theorem B955707 : Blo 952587 955707 := bstep (se 1 (by rfl) ⟨716780, by rfl⟩ : syracuseStep 955707 = 1433561) B1433561
theorem B955783 : Blo 952587 955783 := bstep (se 1 (by rfl) ⟨716837, by rfl⟩ : syracuseStep 955783 = 1433675) B1433675
theorem B955791 : Blo 952587 955791 := bstep (se 1 (by rfl) ⟨716843, by rfl⟩ : syracuseStep 955791 = 1433687) B1433687
theorem B955835 : Blo 952587 955835 := bstep (se 1 (by rfl) ⟨716876, by rfl⟩ : syracuseStep 955835 = 1433753) B1433753
theorem B955911 : Blo 952587 955911 := bstep (se 1 (by rfl) ⟨716933, by rfl⟩ : syracuseStep 955911 = 1433867) B1433867
theorem B955919 : Blo 952587 955919 := bstep (se 1 (by rfl) ⟨716939, by rfl⟩ : syracuseStep 955919 = 1433879) B1433879
theorem B955963 : Blo 952587 955963 := bstep (se 1 (by rfl) ⟨716972, by rfl⟩ : syracuseStep 955963 = 1433945) B1433945
theorem B956039 : Blo 952587 956039 := bstep (se 1 (by rfl) ⟨717029, by rfl⟩ : syracuseStep 956039 = 1434059) B1434059
theorem B956047 : Blo 952587 956047 := bstep (se 1 (by rfl) ⟨717035, by rfl⟩ : syracuseStep 956047 = 1434071) B1434071
theorem B956091 : Blo 952587 956091 := bstep (se 1 (by rfl) ⟨717068, by rfl⟩ : syracuseStep 956091 = 1434137) B1434137
theorem B956167 : Blo 952587 956167 := bstep (se 1 (by rfl) ⟨717125, by rfl⟩ : syracuseStep 956167 = 1434251) B1434251
theorem B1611535 : Blo 952587 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B956175 : Blo 952587 956175 := bstep (se 1 (by rfl) ⟨717131, by rfl⟩ : syracuseStep 956175 = 1434263) B1434263
theorem B3217211 : Blo 952587 3217211 := bstep (se 1 (by rfl) ⟨2412908, by rfl⟩ : syracuseStep 3217211 = 4825817) B4825817
theorem B1087291 : Blo 952587 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B956219 : Blo 952587 956219 := bstep (se 1 (by rfl) ⟨717164, by rfl⟩ : syracuseStep 956219 = 1434329) B1434329
theorem B956295 : Blo 952587 956295 := bstep (se 1 (by rfl) ⟨717221, by rfl⟩ : syracuseStep 956295 = 1434443) B1434443
theorem B956303 : Blo 952587 956303 := bstep (se 1 (by rfl) ⟨717227, by rfl⟩ : syracuseStep 956303 = 1434455) B1434455
theorem B956347 : Blo 952587 956347 := bstep (se 1 (by rfl) ⟨717260, by rfl⟩ : syracuseStep 956347 = 1434521) B1434521
theorem B956423 : Blo 952587 956423 := bstep (se 1 (by rfl) ⟨717317, by rfl⟩ : syracuseStep 956423 = 1434635) B1434635
theorem B956431 : Blo 952587 956431 := bstep (se 1 (by rfl) ⟨717323, by rfl⟩ : syracuseStep 956431 = 1434647) B1434647
theorem B4823063 : Blo 952587 4823063 := bstep (se 1 (by rfl) ⟨3617297, by rfl⟩ : syracuseStep 4823063 = 7234595) B7234595
theorem B956475 : Blo 952587 956475 := bstep (se 1 (by rfl) ⟨717356, by rfl⟩ : syracuseStep 956475 = 1434713) B1434713
theorem B956551 : Blo 952587 956551 := bstep (se 1 (by rfl) ⟨717413, by rfl⟩ : syracuseStep 956551 = 1434827) B1434827
theorem B956559 : Blo 952587 956559 := bstep (se 1 (by rfl) ⟨717419, by rfl⟩ : syracuseStep 956559 = 1434839) B1434839
theorem B3217697 : Blo 952587 3217697 := bstep (se 2 (by rfl) ⟨1206636, by rfl⟩ : syracuseStep 3217697 = 2413273) B2413273
theorem B1612075 : Blo 952587 1612075 := bstep (se 1 (by rfl) ⟨1209056, by rfl⟩ : syracuseStep 1612075 = 2418113) B2418113
theorem B1612217 : Blo 952587 1612217 := bstep (se 2 (by rfl) ⟨604581, by rfl⟩ : syracuseStep 1612217 = 1209163) B1209163
theorem B10459601 : Blo 952587 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B17439275 : Blo 952587 17439275 := bstep (se 1 (by rfl) ⟨13079456, by rfl⟩ : syracuseStep 17439275 = 26158913) B26158913
theorem B38214341 : Blo 952587 38214341 := bstep (se 4 (by rfl) ⟨3582594, by rfl⟩ : syracuseStep 38214341 = 7165189) B7165189
theorem B11606819 : Blo 952587 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B7248689 : Blo 952587 7248689 := bstep (se 2 (by rfl) ⟨2718258, by rfl⟩ : syracuseStep 7248689 = 5436517) B5436517
theorem B1809211 : Blo 952587 1809211 := bstep (se 1 (by rfl) ⟨1356908, by rfl⟩ : syracuseStep 1809211 = 2713817) B2713817
theorem B3218291 : Blo 952587 3218291 := bstep (se 1 (by rfl) ⟨2413718, by rfl⟩ : syracuseStep 3218291 = 4827437) B4827437
theorem B1809287 : Blo 952587 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B2038729 : Blo 952587 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B5446723 : Blo 952587 5446723 := bstep (se 1 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 5446723 = 8170085) B8170085
theorem B7445591 : Blo 952587 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B1612919 : Blo 952587 1612919 := bstep (se 1 (by rfl) ⟨1209689, by rfl⟩ : syracuseStep 1612919 = 2419379) B2419379
theorem B37264535 : Blo 952587 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B5807305 : Blo 952587 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B1809697 : Blo 952587 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B1613371 : Blo 952587 1613371 := bstep (se 1 (by rfl) ⟨1210028, by rfl⟩ : syracuseStep 1613371 = 2420057) B2420057
theorem B4070999 : Blo 952587 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B1810039 : Blo 952587 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B1613513 : Blo 952587 1613513 := bstep (se 2 (by rfl) ⟨605067, by rfl⟩ : syracuseStep 1613513 = 1210135) B1210135
theorem B10886885 : Blo 952587 10886885 := bstep (se 4 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 10886885 = 2041291) B2041291
theorem B2039737 : Blo 952587 2039737 := bstep (se 2 (by rfl) ⟨764901, by rfl⟩ : syracuseStep 2039737 = 1529803) B1529803
theorem B1679305 : Blo 952587 1679305 := bstep (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) B1259479
theorem B5152835 : Blo 952587 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B3055735 : Blo 952587 3055735 := bstep (se 1 (by rfl) ⟨2291801, by rfl⟩ : syracuseStep 3055735 = 4583603) B4583603
theorem B2039993 : Blo 952587 2039993 := bstep (se 2 (by rfl) ⟨764997, by rfl⟩ : syracuseStep 2039993 = 1529995) B1529995
theorem B8167625 : Blo 952587 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B2040079 : Blo 952587 2040079 := bstep (se 1 (by rfl) ⟨1530059, by rfl⟩ : syracuseStep 2040079 = 3060119) B3060119
theorem B1614215 : Blo 952587 1614215 := bstep (se 1 (by rfl) ⟨1210661, by rfl⟩ : syracuseStep 1614215 = 2421323) B2421323
theorem B14885441 : Blo 952587 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B6103781 : Blo 952587 6103781 := bstep (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) B1144459
theorem B4826141 : Blo 952587 4826141 := bstep (se 3 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 4826141 = 1809803) B1809803
theorem B6890629 : Blo 952587 6890629 := bstep (se 4 (by rfl) ⟨645996, by rfl⟩ : syracuseStep 6890629 = 1291993) B1291993
theorem B2040967 : Blo 952587 2040967 := bstep (se 1 (by rfl) ⟨1530725, by rfl⟩ : syracuseStep 2040967 = 3061451) B3061451
theorem B1811641 : Blo 952587 1811641 := bstep (se 2 (by rfl) ⟨679365, by rfl⟩ : syracuseStep 1811641 = 1358731) B1358731
theorem B2041121 : Blo 952587 2041121 := bstep (se 2 (by rfl) ⟨765420, by rfl⟩ : syracuseStep 2041121 = 1530841) B1530841
theorem B3220883 : Blo 952587 3220883 := bstep (se 1 (by rfl) ⟨2415662, by rfl⟩ : syracuseStep 3220883 = 4831325) B4831325
theorem B1451449 : Blo 952587 1451449 := bstep (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) B1088587
theorem B16328141 : Blo 952587 16328141 := bstep (se 3 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 16328141 = 6123053) B6123053
theorem B4072913 : Blo 952587 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B4826627 : Blo 952587 4826627 := bstep (se 1 (by rfl) ⟨3619970, by rfl⟩ : syracuseStep 4826627 = 7239941) B7239941
theorem B1811983 : Blo 952587 1811983 := bstep (se 1 (by rfl) ⟨1358987, by rfl⟩ : syracuseStep 1811983 = 2717975) B2717975
theorem B2041463 : Blo 952587 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B2041633 : Blo 952587 2041633 := bstep (se 2 (by rfl) ⟨765612, by rfl⟩ : syracuseStep 2041633 = 1531225) B1531225
theorem B10856267 : Blo 952587 10856267 := bstep (se 1 (by rfl) ⟨8142200, by rfl⟩ : syracuseStep 10856267 = 16284401) B16284401
theorem B1747003 : Blo 952587 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1812871 : Blo 952587 1812871 := bstep (se 1 (by rfl) ⟨1359653, by rfl⟩ : syracuseStep 1812871 = 2719307) B2719307
theorem B4893385 : Blo 952587 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B6204161 : Blo 952587 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B3222287 : Blo 952587 3222287 := bstep (se 1 (by rfl) ⟨2416715, by rfl⟩ : syracuseStep 3222287 = 4833431) B4833431
theorem B5975005 : Blo 952587 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B3222557 : Blo 952587 3222557 := bstep (se 3 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 3222557 = 1208459) B1208459
theorem B4828247 : Blo 952587 4828247 := bstep (se 1 (by rfl) ⟨3621185, by rfl⟩ : syracuseStep 4828247 = 7242371) B7242371
theorem B4828733 : Blo 952587 4828733 := bstep (se 3 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 4828733 = 1810775) B1810775
theorem B1453967 : Blo 952587 1453967 := bstep (se 1 (by rfl) ⟨1090475, by rfl⟩ : syracuseStep 1453967 = 2180951) B2180951
theorem B2174867 : Blo 952587 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B1814663 : Blo 952587 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B3223961 : Blo 952587 3223961 := bstep (se 2 (by rfl) ⟨1208985, by rfl⟩ : syracuseStep 3223961 = 2417971) B2417971
theorem B1356601 : Blo 952587 1356601 := bstep (se 2 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 1356601 = 1017451) B1017451
theorem B3224663 : Blo 952587 3224663 := bstep (se 1 (by rfl) ⟨2418497, by rfl⟩ : syracuseStep 3224663 = 4836995) B4836995
theorem B2143367 : Blo 952587 2143367 := bstep (se 1 (by rfl) ⟨1607525, by rfl⟩ : syracuseStep 2143367 = 3215051) B3215051
theorem B4830515 : Blo 952587 4830515 := bstep (se 1 (by rfl) ⟨3622886, by rfl⟩ : syracuseStep 4830515 = 7245773) B7245773
theorem B2143547 : Blo 952587 2143547 := bstep (se 1 (by rfl) ⟨1607660, by rfl⟩ : syracuseStep 2143547 = 3215321) B3215321
theorem B2143673 : Blo 952587 2143673 := bstep (se 2 (by rfl) ⟨803877, by rfl⟩ : syracuseStep 2143673 = 1607755) B1607755
theorem B3225149 : Blo 952587 3225149 := bstep (se 3 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 3225149 = 1209431) B1209431
theorem B3618391 : Blo 952587 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B4830839 : Blo 952587 4830839 := bstep (se 1 (by rfl) ⟨3623129, by rfl⟩ : syracuseStep 4830839 = 7246259) B7246259
theorem B2144015 : Blo 952587 2144015 := bstep (se 1 (by rfl) ⟨1608011, by rfl⟩ : syracuseStep 2144015 = 3216023) B3216023
theorem B2144033 : Blo 952587 2144033 := bstep (se 2 (by rfl) ⟨804012, by rfl⟩ : syracuseStep 2144033 = 1608025) B1608025
theorem B4896571 : Blo 952587 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B3618695 : Blo 952587 3618695 := bstep (se 1 (by rfl) ⟨2714021, by rfl⟩ : syracuseStep 3618695 = 5428043) B5428043
theorem B1357831 : Blo 952587 1357831 := bstep (se 1 (by rfl) ⟨1018373, by rfl⟩ : syracuseStep 1357831 = 2036747) B2036747
theorem B1226795 : Blo 952587 1226795 := bstep (se 1 (by rfl) ⟨920096, by rfl⟩ : syracuseStep 1226795 = 1840193) B1840193
theorem B3618877 : Blo 952587 3618877 := bstep (se 3 (by rfl) ⟨678539, by rfl⟩ : syracuseStep 3618877 = 1357079) B1357079
theorem B7747645 : Blo 952587 7747645 := bstep (se 3 (by rfl) ⟨1452683, by rfl⟩ : syracuseStep 7747645 = 2905367) B2905367
theorem B2144375 : Blo 952587 2144375 := bstep (se 1 (by rfl) ⟨1608281, by rfl⟩ : syracuseStep 2144375 = 3216563) B3216563
theorem B2144555 : Blo 952587 2144555 := bstep (se 1 (by rfl) ⟨1608416, by rfl⟩ : syracuseStep 2144555 = 3216833) B3216833
theorem B7256465 : Blo 952587 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B4077971 : Blo 952587 4077971 := bstep (se 1 (by rfl) ⟨3058478, by rfl⟩ : syracuseStep 4077971 = 6116957) B6116957
theorem B4831811 : Blo 952587 4831811 := bstep (se 1 (by rfl) ⟨3623858, by rfl⟩ : syracuseStep 4831811 = 7247717) B7247717
theorem B2144915 : Blo 952587 2144915 := bstep (se 1 (by rfl) ⟨1608686, by rfl⟩ : syracuseStep 2144915 = 3217373) B3217373
theorem B2144969 : Blo 952587 2144969 := bstep (se 2 (by rfl) ⟨804363, by rfl⟩ : syracuseStep 2144969 = 1608727) B1608727
theorem B1358537 : Blo 952587 1358537 := bstep (se 2 (by rfl) ⟨509451, by rfl⟩ : syracuseStep 1358537 = 1018903) B1018903
theorem B1719083 : Blo 952587 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B1358651 : Blo 952587 1358651 := bstep (se 1 (by rfl) ⟨1018988, by rfl⟩ : syracuseStep 1358651 = 2037977) B2037977
theorem B4832135 : Blo 952587 4832135 := bstep (se 1 (by rfl) ⟨3624101, by rfl⟩ : syracuseStep 4832135 = 7248203) B7248203
theorem B3062681 : Blo 952587 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B3226553 : Blo 952587 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B2145671 : Blo 952587 2145671 := bstep (se 1 (by rfl) ⟨1609253, by rfl⟩ : syracuseStep 2145671 = 3218507) B3218507
theorem B6110599 : Blo 952587 6110599 := bstep (se 1 (by rfl) ⟨4582949, by rfl⟩ : syracuseStep 6110599 = 9165899) B9165899
theorem B1359289 : Blo 952587 1359289 := bstep (se 2 (by rfl) ⟨509733, by rfl⟩ : syracuseStep 1359289 = 1019467) B1019467
theorem B3227147 : Blo 952587 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B2145851 : Blo 952587 2145851 := bstep (se 1 (by rfl) ⟨1609388, by rfl⟩ : syracuseStep 2145851 = 3218777) B3218777
theorem B3227255 : Blo 952587 3227255 := bstep (se 1 (by rfl) ⟨2420441, by rfl⟩ : syracuseStep 3227255 = 4840883) B4840883
theorem B2145977 : Blo 952587 2145977 := bstep (se 2 (by rfl) ⟨804741, by rfl⟩ : syracuseStep 2145977 = 1609483) B1609483
theorem B10305281 : Blo 952587 10305281 := bstep (se 2 (by rfl) ⟨3864480, by rfl⟩ : syracuseStep 10305281 = 7728961) B7728961
theorem B3620609 : Blo 952587 3620609 := bstep (se 2 (by rfl) ⟨1357728, by rfl⟩ : syracuseStep 3620609 = 2715457) B2715457
theorem B18333485 : Blo 952587 18333485 := bstep (se 3 (by rfl) ⟨3437528, by rfl⟩ : syracuseStep 18333485 = 6875057) B6875057
theorem B31768523 : Blo 952587 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B2146319 : Blo 952587 2146319 := bstep (se 1 (by rfl) ⟨1609739, by rfl⟩ : syracuseStep 2146319 = 3219479) B3219479
theorem B4079645 : Blo 952587 4079645 := bstep (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) B1529867
theorem B2146337 : Blo 952587 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B3227849 : Blo 952587 3227849 := bstep (se 2 (by rfl) ⟨1210443, by rfl⟩ : syracuseStep 3227849 = 2420887) B2420887
theorem B10895633 : Blo 952587 10895633 := bstep (se 2 (by rfl) ⟨4085862, by rfl⟩ : syracuseStep 10895633 = 8171725) B8171725
theorem B2146679 : Blo 952587 2146679 := bstep (se 1 (by rfl) ⟨1610009, by rfl⟩ : syracuseStep 2146679 = 3220019) B3220019
theorem B66896273 : Blo 952587 66896273 := bstep (se 2 (by rfl) ⟨25086102, by rfl⟩ : syracuseStep 66896273 = 50172205) B50172205
theorem B1720777 : Blo 952587 1720777 := bstep (se 2 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 1720777 = 1290583) B1290583
theorem B11616797 : Blo 952587 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B2146859 : Blo 952587 2146859 := bstep (se 1 (by rfl) ⟨1610144, by rfl⟩ : syracuseStep 2146859 = 3220289) B3220289
theorem B8274703 : Blo 952587 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B7258895 : Blo 952587 7258895 := bstep (se 1 (by rfl) ⟨5444171, by rfl⟩ : syracuseStep 7258895 = 10888343) B10888343
theorem B3621779 : Blo 952587 3621779 := bstep (se 1 (by rfl) ⟨2716334, by rfl⟩ : syracuseStep 3621779 = 5432669) B5432669
theorem B2147219 : Blo 952587 2147219 := bstep (se 1 (by rfl) ⟨1610414, by rfl⟩ : syracuseStep 2147219 = 3220829) B3220829
theorem B5522329 : Blo 952587 5522329 := bstep (se 2 (by rfl) ⟨2070873, by rfl⟩ : syracuseStep 5522329 = 4141747) B4141747
theorem B2147273 : Blo 952587 2147273 := bstep (se 2 (by rfl) ⟨805227, by rfl⟩ : syracuseStep 2147273 = 1610455) B1610455
theorem B3622279 : Blo 952587 3622279 := bstep (se 1 (by rfl) ⟨2716709, by rfl⟩ : syracuseStep 3622279 = 5433419) B5433419
theorem B7751047 : Blo 952587 7751047 := bstep (se 1 (by rfl) ⟨5813285, by rfl⟩ : syracuseStep 7751047 = 11626571) B11626571
theorem B9192851 : Blo 952587 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B2147975 : Blo 952587 2147975 := bstep (se 1 (by rfl) ⟨1610981, by rfl⟩ : syracuseStep 2147975 = 3221963) B3221963
theorem B2148155 : Blo 952587 2148155 := bstep (se 1 (by rfl) ⟨1611116, by rfl⟩ : syracuseStep 2148155 = 3222233) B3222233
theorem B5162867 : Blo 952587 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B2148281 : Blo 952587 2148281 := bstep (se 2 (by rfl) ⟨805605, by rfl⟩ : syracuseStep 2148281 = 1611211) B1611211
theorem B13224181 : Blo 952587 13224181 := bstep (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) B1239767
theorem B2148623 : Blo 952587 2148623 := bstep (se 1 (by rfl) ⟨1611467, by rfl⟩ : syracuseStep 2148623 = 3222935) B3222935
theorem B2148641 : Blo 952587 2148641 := bstep (se 2 (by rfl) ⟨805740, by rfl⟩ : syracuseStep 2148641 = 1611481) B1611481
theorem B4835699 : Blo 952587 4835699 := bstep (se 1 (by rfl) ⟨3626774, by rfl⟩ : syracuseStep 4835699 = 7253549) B7253549
theorem B5163473 : Blo 952587 5163473 := bstep (se 2 (by rfl) ⟨1936302, by rfl⟩ : syracuseStep 5163473 = 3872605) B3872605
theorem B2148983 : Blo 952587 2148983 := bstep (se 1 (by rfl) ⟨1611737, by rfl⟩ : syracuseStep 2148983 = 3223475) B3223475
theorem B5163713 : Blo 952587 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B2411279 : Blo 952587 2411279 := bstep (se 1 (by rfl) ⟨1808459, by rfl⟩ : syracuseStep 2411279 = 3616919) B3616919
theorem B2149163 : Blo 952587 2149163 := bstep (se 1 (by rfl) ⟨1611872, by rfl⟩ : syracuseStep 2149163 = 3223745) B3223745
theorem B4836185 : Blo 952587 4836185 := bstep (se 2 (by rfl) ⟨1813569, by rfl⟩ : syracuseStep 4836185 = 3627139) B3627139
theorem B5426129 : Blo 952587 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B1526843 : Blo 952587 1526843 := bstep (se 1 (by rfl) ⟨1145132, by rfl⟩ : syracuseStep 1526843 = 2290265) B2290265
theorem B2149523 : Blo 952587 2149523 := bstep (se 1 (by rfl) ⟨1612142, by rfl⟩ : syracuseStep 2149523 = 3224285) B3224285
theorem B2149577 : Blo 952587 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B1723681 : Blo 952587 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B5426585 : Blo 952587 5426585 := bstep (se 2 (by rfl) ⟨2034969, by rfl⟩ : syracuseStep 5426585 = 4069939) B4069939
theorem B1428923 : Blo 952587 1428923 := bstep (se 1 (by rfl) ⟨1071692, by rfl⟩ : syracuseStep 1428923 = 2143385) B2143385
theorem B2411977 : Blo 952587 2411977 := bstep (se 2 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 2411977 = 1808983) B1808983
theorem B1428983 : Blo 952587 1428983 := bstep (se 1 (by rfl) ⟨1071737, by rfl⟩ : syracuseStep 1428983 = 2143475) B2143475
theorem B1429007 : Blo 952587 1429007 := bstep (se 1 (by rfl) ⟨1071755, by rfl⟩ : syracuseStep 1429007 = 2143511) B2143511
theorem B1429049 : Blo 952587 1429049 := bstep (se 2 (by rfl) ⟨535893, by rfl⟩ : syracuseStep 1429049 = 1071787) B1071787
theorem B2412119 : Blo 952587 2412119 := bstep (se 1 (by rfl) ⟨1809089, by rfl⟩ : syracuseStep 2412119 = 3618179) B3618179
theorem B1429127 : Blo 952587 1429127 := bstep (se 1 (by rfl) ⟨1071845, by rfl⟩ : syracuseStep 1429127 = 2143691) B2143691
theorem B1429163 : Blo 952587 1429163 := bstep (se 1 (by rfl) ⟨1071872, by rfl⟩ : syracuseStep 1429163 = 2143745) B2143745
theorem B1429193 : Blo 952587 1429193 := bstep (se 2 (by rfl) ⟨535947, by rfl⟩ : syracuseStep 1429193 = 1071895) B1071895
theorem B1429307 : Blo 952587 1429307 := bstep (se 1 (by rfl) ⟨1071980, by rfl⟩ : syracuseStep 1429307 = 2143961) B2143961
theorem B1429367 : Blo 952587 1429367 := bstep (se 1 (by rfl) ⟨1072025, by rfl⟩ : syracuseStep 1429367 = 2144051) B2144051
theorem B2150279 : Blo 952587 2150279 := bstep (se 1 (by rfl) ⟨1612709, by rfl⟩ : syracuseStep 2150279 = 3225419) B3225419
theorem B1429391 : Blo 952587 1429391 := bstep (se 1 (by rfl) ⟨1072043, by rfl⟩ : syracuseStep 1429391 = 2144087) B2144087
theorem B1429433 : Blo 952587 1429433 := bstep (se 2 (by rfl) ⟨536037, by rfl⟩ : syracuseStep 1429433 = 1072075) B1072075
theorem B1429511 : Blo 952587 1429511 := bstep (se 1 (by rfl) ⟨1072133, by rfl⟩ : syracuseStep 1429511 = 2144267) B2144267
theorem B1429547 : Blo 952587 1429547 := bstep (se 1 (by rfl) ⟨1072160, by rfl⟩ : syracuseStep 1429547 = 2144321) B2144321
theorem B2150459 : Blo 952587 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B5165117 : Blo 952587 5165117 := bstep (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) B1936919
theorem B1429577 : Blo 952587 1429577 := bstep (se 2 (by rfl) ⟨536091, by rfl⟩ : syracuseStep 1429577 = 1072183) B1072183
theorem B2904211 : Blo 952587 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B2150585 : Blo 952587 2150585 := bstep (se 2 (by rfl) ⟨806469, by rfl⟩ : syracuseStep 2150585 = 1612939) B1612939
theorem B1429691 : Blo 952587 1429691 := bstep (se 1 (by rfl) ⟨1072268, by rfl⟩ : syracuseStep 1429691 = 2144537) B2144537
theorem B4083949 : Blo 952587 4083949 := bstep (se 3 (by rfl) ⟨765740, by rfl⟩ : syracuseStep 4083949 = 1531481) B1531481
theorem B1429751 : Blo 952587 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B1429775 : Blo 952587 1429775 := bstep (se 1 (by rfl) ⟨1072331, by rfl⟩ : syracuseStep 1429775 = 2144663) B2144663
theorem B1429817 : Blo 952587 1429817 := bstep (se 2 (by rfl) ⟨536181, by rfl⟩ : syracuseStep 1429817 = 1072363) B1072363
theorem B1429895 : Blo 952587 1429895 := bstep (se 1 (by rfl) ⟨1072421, by rfl⟩ : syracuseStep 1429895 = 2144843) B2144843
theorem B29348243 : Blo 952587 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B4084121 : Blo 952587 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B1429931 : Blo 952587 1429931 := bstep (se 1 (by rfl) ⟨1072448, by rfl⟩ : syracuseStep 1429931 = 2144897) B2144897
theorem B1429961 : Blo 952587 1429961 := bstep (se 2 (by rfl) ⟨536235, by rfl⟩ : syracuseStep 1429961 = 1072471) B1072471
theorem B1528265 : Blo 952587 1528265 := bstep (se 2 (by rfl) ⟨573099, by rfl⟩ : syracuseStep 1528265 = 1146199) B1146199
theorem B2150927 : Blo 952587 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B2150945 : Blo 952587 2150945 := bstep (se 2 (by rfl) ⟨806604, by rfl⟩ : syracuseStep 2150945 = 1613209) B1613209
theorem B1430075 : Blo 952587 1430075 := bstep (se 1 (by rfl) ⟨1072556, by rfl⟩ : syracuseStep 1430075 = 2145113) B2145113
theorem B5165635 : Blo 952587 5165635 := bstep (se 1 (by rfl) ⟨3874226, by rfl⟩ : syracuseStep 5165635 = 7748453) B7748453
theorem B1430135 : Blo 952587 1430135 := bstep (se 1 (by rfl) ⟨1072601, by rfl⟩ : syracuseStep 1430135 = 2145203) B2145203
theorem B1430159 : Blo 952587 1430159 := bstep (se 1 (by rfl) ⟨1072619, by rfl⟩ : syracuseStep 1430159 = 2145239) B2145239
theorem B1430201 : Blo 952587 1430201 := bstep (se 2 (by rfl) ⟨536325, by rfl⟩ : syracuseStep 1430201 = 1072651) B1072651
theorem B1430279 : Blo 952587 1430279 := bstep (se 1 (by rfl) ⟨1072709, by rfl⟩ : syracuseStep 1430279 = 2145419) B2145419
theorem B1430315 : Blo 952587 1430315 := bstep (se 1 (by rfl) ⟨1072736, by rfl⟩ : syracuseStep 1430315 = 2145473) B2145473
theorem B2904893 : Blo 952587 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B1430345 : Blo 952587 1430345 := bstep (se 2 (by rfl) ⟨536379, by rfl⟩ : syracuseStep 1430345 = 1072759) B1072759
theorem B2151287 : Blo 952587 2151287 := bstep (se 1 (by rfl) ⟨1613465, by rfl⟩ : syracuseStep 2151287 = 3226931) B3226931
theorem B4838291 : Blo 952587 4838291 := bstep (se 1 (by rfl) ⟨3628718, by rfl⟩ : syracuseStep 4838291 = 7257437) B7257437
theorem B1430459 : Blo 952587 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B1430519 : Blo 952587 1430519 := bstep (se 1 (by rfl) ⟨1072889, by rfl⟩ : syracuseStep 1430519 = 2145779) B2145779
theorem B1430543 : Blo 952587 1430543 := bstep (se 1 (by rfl) ⟨1072907, by rfl⟩ : syracuseStep 1430543 = 2145815) B2145815
theorem B2151467 : Blo 952587 2151467 := bstep (se 1 (by rfl) ⟨1613600, by rfl⟩ : syracuseStep 2151467 = 3227201) B3227201
theorem B1430585 : Blo 952587 1430585 := bstep (se 2 (by rfl) ⟨536469, by rfl⟩ : syracuseStep 1430585 = 1072939) B1072939
theorem B1430663 : Blo 952587 1430663 := bstep (se 1 (by rfl) ⟨1072997, by rfl⟩ : syracuseStep 1430663 = 2145995) B2145995
theorem B1430699 : Blo 952587 1430699 := bstep (se 1 (by rfl) ⟨1073024, by rfl⟩ : syracuseStep 1430699 = 2146049) B2146049
theorem B1430729 : Blo 952587 1430729 := bstep (se 2 (by rfl) ⟨536523, by rfl⟩ : syracuseStep 1430729 = 1073047) B1073047
theorem B1430843 : Blo 952587 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B1430903 : Blo 952587 1430903 := bstep (se 1 (by rfl) ⟨1073177, by rfl⟩ : syracuseStep 1430903 = 2146355) B2146355
theorem B1430927 : Blo 952587 1430927 := bstep (se 1 (by rfl) ⟨1073195, by rfl⟩ : syracuseStep 1430927 = 2146391) B2146391
theorem B2151827 : Blo 952587 2151827 := bstep (se 1 (by rfl) ⟨1613870, by rfl⟩ : syracuseStep 2151827 = 3227741) B3227741
theorem B1430969 : Blo 952587 1430969 := bstep (se 2 (by rfl) ⟨536613, by rfl⟩ : syracuseStep 1430969 = 1073227) B1073227
theorem B2151881 : Blo 952587 2151881 := bstep (se 2 (by rfl) ⟨806955, by rfl⟩ : syracuseStep 2151881 = 1613911) B1613911
theorem B12211661 : Blo 952587 12211661 := bstep (se 3 (by rfl) ⟨2289686, by rfl⟩ : syracuseStep 12211661 = 4579373) B4579373
theorem B1431047 : Blo 952587 1431047 := bstep (se 1 (by rfl) ⟨1073285, by rfl⟩ : syracuseStep 1431047 = 2146571) B2146571
theorem B1431083 : Blo 952587 1431083 := bstep (se 1 (by rfl) ⟨1073312, by rfl⟩ : syracuseStep 1431083 = 2146625) B2146625
theorem B1431113 : Blo 952587 1431113 := bstep (se 2 (by rfl) ⟨536667, by rfl⟩ : syracuseStep 1431113 = 1073335) B1073335
theorem B2414195 : Blo 952587 2414195 := bstep (se 1 (by rfl) ⟨1810646, by rfl⟩ : syracuseStep 2414195 = 3621293) B3621293
theorem B1431227 : Blo 952587 1431227 := bstep (se 1 (by rfl) ⟨1073420, by rfl⟩ : syracuseStep 1431227 = 2146841) B2146841
theorem B1431287 : Blo 952587 1431287 := bstep (se 1 (by rfl) ⟨1073465, by rfl⟩ : syracuseStep 1431287 = 2146931) B2146931
theorem B1431311 : Blo 952587 1431311 := bstep (se 1 (by rfl) ⟨1073483, by rfl⟩ : syracuseStep 1431311 = 2146967) B2146967
theorem B18339635 : Blo 952587 18339635 := bstep (se 1 (by rfl) ⟨13754726, by rfl⟩ : syracuseStep 18339635 = 27509453) B27509453
theorem B1431353 : Blo 952587 1431353 := bstep (se 2 (by rfl) ⟨536757, by rfl⟩ : syracuseStep 1431353 = 1073515) B1073515
theorem B1431431 : Blo 952587 1431431 := bstep (se 1 (by rfl) ⟨1073573, by rfl⟩ : syracuseStep 1431431 = 2147147) B2147147
theorem B1431467 : Blo 952587 1431467 := bstep (se 1 (by rfl) ⟨1073600, by rfl⟩ : syracuseStep 1431467 = 2147201) B2147201
theorem B1431497 : Blo 952587 1431497 := bstep (se 2 (by rfl) ⟨536811, by rfl⟩ : syracuseStep 1431497 = 1073623) B1073623
theorem B1431611 : Blo 952587 1431611 := bstep (se 1 (by rfl) ⟨1073708, by rfl⟩ : syracuseStep 1431611 = 2147417) B2147417
theorem B2414711 : Blo 952587 2414711 := bstep (se 1 (by rfl) ⟨1811033, by rfl⟩ : syracuseStep 2414711 = 3622067) B3622067
theorem B1431671 : Blo 952587 1431671 := bstep (se 1 (by rfl) ⟨1073753, by rfl⟩ : syracuseStep 1431671 = 2147507) B2147507
theorem B1431695 : Blo 952587 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B1431737 : Blo 952587 1431737 := bstep (se 2 (by rfl) ⟨536901, by rfl⟩ : syracuseStep 1431737 = 1073803) B1073803
theorem B1431815 : Blo 952587 1431815 := bstep (se 1 (by rfl) ⟨1073861, by rfl⟩ : syracuseStep 1431815 = 2147723) B2147723
theorem B1431851 : Blo 952587 1431851 := bstep (se 1 (by rfl) ⟨1073888, by rfl⟩ : syracuseStep 1431851 = 2147777) B2147777
theorem B1431881 : Blo 952587 1431881 := bstep (se 2 (by rfl) ⟨536955, by rfl⟩ : syracuseStep 1431881 = 1073911) B1073911
theorem B1431995 : Blo 952587 1431995 := bstep (se 1 (by rfl) ⟨1073996, by rfl⟩ : syracuseStep 1431995 = 2147993) B2147993
theorem B1432055 : Blo 952587 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B1432079 : Blo 952587 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B1432121 : Blo 952587 1432121 := bstep (se 2 (by rfl) ⟨537045, by rfl⟩ : syracuseStep 1432121 = 1074091) B1074091
theorem B1071751 : Blo 952587 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B1432199 : Blo 952587 1432199 := bstep (se 1 (by rfl) ⟨1074149, by rfl⟩ : syracuseStep 1432199 = 2148299) B2148299
theorem B1432235 : Blo 952587 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B1432265 : Blo 952587 1432265 := bstep (se 2 (by rfl) ⟨537099, by rfl⟩ : syracuseStep 1432265 = 1074199) B1074199
theorem B4578029 : Blo 952587 4578029 := bstep (se 3 (by rfl) ⟨858380, by rfl⟩ : syracuseStep 4578029 = 1716761) B1716761
theorem B1071931 : Blo 952587 1071931 := bstep (se 1 (by rfl) ⟨803948, by rfl⟩ : syracuseStep 1071931 = 1607897) B1607897
theorem B1432379 : Blo 952587 1432379 := bstep (se 1 (by rfl) ⟨1074284, by rfl⟩ : syracuseStep 1432379 = 2148569) B2148569
theorem B1432439 : Blo 952587 1432439 := bstep (se 1 (by rfl) ⟨1074329, by rfl⟩ : syracuseStep 1432439 = 2148659) B2148659
theorem B1432463 : Blo 952587 1432463 := bstep (se 1 (by rfl) ⟨1074347, by rfl⟩ : syracuseStep 1432463 = 2148695) B2148695
theorem B3627929 : Blo 952587 3627929 := bstep (se 2 (by rfl) ⟨1360473, by rfl⟩ : syracuseStep 3627929 = 2720947) B2720947
theorem B1432505 : Blo 952587 1432505 := bstep (se 2 (by rfl) ⟨537189, by rfl⟩ : syracuseStep 1432505 = 1074379) B1074379
theorem B12409861 : Blo 952587 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B1432583 : Blo 952587 1432583 := bstep (se 1 (by rfl) ⟨1074437, by rfl⟩ : syracuseStep 1432583 = 2148875) B2148875
theorem B1432619 : Blo 952587 1432619 := bstep (se 1 (by rfl) ⟨1074464, by rfl⟩ : syracuseStep 1432619 = 2148929) B2148929
theorem B1432649 : Blo 952587 1432649 := bstep (se 2 (by rfl) ⟨537243, by rfl⟩ : syracuseStep 1432649 = 1074487) B1074487
theorem B2415703 : Blo 952587 2415703 := bstep (se 1 (by rfl) ⟨1811777, by rfl⟩ : syracuseStep 2415703 = 3623555) B3623555
theorem B1432763 : Blo 952587 1432763 := bstep (se 1 (by rfl) ⟨1074572, by rfl⟩ : syracuseStep 1432763 = 2149145) B2149145
theorem B1432823 : Blo 952587 1432823 := bstep (se 1 (by rfl) ⟨1074617, by rfl⟩ : syracuseStep 1432823 = 2149235) B2149235
theorem B1072399 : Blo 952587 1072399 := bstep (se 1 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 1072399 = 1608599) B1608599
theorem B1432847 : Blo 952587 1432847 := bstep (se 1 (by rfl) ⟨1074635, by rfl⟩ : syracuseStep 1432847 = 2149271) B2149271
theorem B1432889 : Blo 952587 1432889 := bstep (se 2 (by rfl) ⟨537333, by rfl⟩ : syracuseStep 1432889 = 1074667) B1074667
theorem B2416007 : Blo 952587 2416007 := bstep (se 1 (by rfl) ⟨1812005, by rfl⟩ : syracuseStep 2416007 = 3624011) B3624011
theorem B1432967 : Blo 952587 1432967 := bstep (se 1 (by rfl) ⟨1074725, by rfl⟩ : syracuseStep 1432967 = 2149451) B2149451
theorem B2448787 : Blo 952587 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B1433003 : Blo 952587 1433003 := bstep (se 1 (by rfl) ⟨1074752, by rfl⟩ : syracuseStep 1433003 = 2149505) B2149505
theorem B1433033 : Blo 952587 1433033 := bstep (se 2 (by rfl) ⟨537387, by rfl⟩ : syracuseStep 1433033 = 1074775) B1074775
theorem B2416139 : Blo 952587 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B1433147 : Blo 952587 1433147 := bstep (se 1 (by rfl) ⟨1074860, by rfl⟩ : syracuseStep 1433147 = 2149721) B2149721
theorem B1433207 : Blo 952587 1433207 := bstep (se 1 (by rfl) ⟨1074905, by rfl⟩ : syracuseStep 1433207 = 2149811) B2149811
theorem B1433231 : Blo 952587 1433231 := bstep (se 1 (by rfl) ⟨1074923, by rfl⟩ : syracuseStep 1433231 = 2149847) B2149847
theorem B1433273 : Blo 952587 1433273 := bstep (se 2 (by rfl) ⟨537477, by rfl⟩ : syracuseStep 1433273 = 1074955) B1074955
theorem B1072903 : Blo 952587 1072903 := bstep (se 1 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 1072903 = 1609355) B1609355
theorem B1433351 : Blo 952587 1433351 := bstep (se 1 (by rfl) ⟨1075013, by rfl⟩ : syracuseStep 1433351 = 2150027) B2150027
theorem B1433387 : Blo 952587 1433387 := bstep (se 1 (by rfl) ⟨1075040, by rfl⟩ : syracuseStep 1433387 = 2150081) B2150081
theorem B1433417 : Blo 952587 1433417 := bstep (se 2 (by rfl) ⟨537531, by rfl⟩ : syracuseStep 1433417 = 1075063) B1075063
theorem B2580311 : Blo 952587 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B157015907 : Blo 952587 157015907 := bstep (se 1 (by rfl) ⟨117761930, by rfl⟩ : syracuseStep 157015907 = 235523861) B235523861
theorem B4841369 : Blo 952587 4841369 := bstep (se 2 (by rfl) ⟨1815513, by rfl⟩ : syracuseStep 4841369 = 3631027) B3631027
theorem B1073083 : Blo 952587 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1433531 : Blo 952587 1433531 := bstep (se 1 (by rfl) ⟨1075148, by rfl⟩ : syracuseStep 1433531 = 2150297) B2150297
theorem B1433591 : Blo 952587 1433591 := bstep (se 1 (by rfl) ⟨1075193, by rfl⟩ : syracuseStep 1433591 = 2150387) B2150387
theorem B2416655 : Blo 952587 2416655 := bstep (se 1 (by rfl) ⟨1812491, by rfl⟩ : syracuseStep 2416655 = 3624983) B3624983
theorem B1433615 : Blo 952587 1433615 := bstep (se 1 (by rfl) ⟨1075211, by rfl⟩ : syracuseStep 1433615 = 2150423) B2150423
theorem B1433657 : Blo 952587 1433657 := bstep (se 2 (by rfl) ⟨537621, by rfl⟩ : syracuseStep 1433657 = 1075243) B1075243
theorem B1433735 : Blo 952587 1433735 := bstep (se 1 (by rfl) ⟨1075301, by rfl⟩ : syracuseStep 1433735 = 2150603) B2150603
theorem B1532039 : Blo 952587 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B2416787 : Blo 952587 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1433771 : Blo 952587 1433771 := bstep (se 1 (by rfl) ⟨1075328, by rfl⟩ : syracuseStep 1433771 = 2150657) B2150657
theorem B1433801 : Blo 952587 1433801 := bstep (se 2 (by rfl) ⟨537675, by rfl⟩ : syracuseStep 1433801 = 1075351) B1075351
theorem B1433915 : Blo 952587 1433915 := bstep (se 1 (by rfl) ⟨1075436, by rfl⟩ : syracuseStep 1433915 = 2150873) B2150873
theorem B1433975 : Blo 952587 1433975 := bstep (se 1 (by rfl) ⟨1075481, by rfl⟩ : syracuseStep 1433975 = 2150963) B2150963
theorem B1073551 : Blo 952587 1073551 := bstep (se 1 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 1073551 = 1610327) B1610327
theorem B1433999 : Blo 952587 1433999 := bstep (se 1 (by rfl) ⟨1075499, by rfl⟩ : syracuseStep 1433999 = 2150999) B2150999
theorem B1434041 : Blo 952587 1434041 := bstep (se 2 (by rfl) ⟨537765, by rfl⟩ : syracuseStep 1434041 = 1075531) B1075531
theorem B1434119 : Blo 952587 1434119 := bstep (se 1 (by rfl) ⟨1075589, by rfl⟩ : syracuseStep 1434119 = 2151179) B2151179
theorem B1434155 : Blo 952587 1434155 := bstep (se 1 (by rfl) ⟨1075616, by rfl⟩ : syracuseStep 1434155 = 2151233) B2151233
theorem B1434185 : Blo 952587 1434185 := bstep (se 2 (by rfl) ⟨537819, by rfl⟩ : syracuseStep 1434185 = 1075639) B1075639
theorem B1434299 : Blo 952587 1434299 := bstep (se 1 (by rfl) ⟨1075724, by rfl⟩ : syracuseStep 1434299 = 2151449) B2151449
theorem B1434359 : Blo 952587 1434359 := bstep (se 1 (by rfl) ⟨1075769, by rfl⟩ : syracuseStep 1434359 = 2151539) B2151539
theorem B1630991 : Blo 952587 1630991 := bstep (se 1 (by rfl) ⟨1223243, by rfl⟩ : syracuseStep 1630991 = 2446487) B2446487
theorem B1434383 : Blo 952587 1434383 := bstep (se 1 (by rfl) ⟨1075787, by rfl⟩ : syracuseStep 1434383 = 2151575) B2151575
theorem B1434425 : Blo 952587 1434425 := bstep (se 2 (by rfl) ⟨537909, by rfl⟩ : syracuseStep 1434425 = 1075819) B1075819
theorem B1074055 : Blo 952587 1074055 := bstep (se 1 (by rfl) ⟨805541, by rfl⟩ : syracuseStep 1074055 = 1611083) B1611083
theorem B1434503 : Blo 952587 1434503 := bstep (se 1 (by rfl) ⟨1075877, by rfl⟩ : syracuseStep 1434503 = 2151755) B2151755
theorem B1434539 : Blo 952587 1434539 := bstep (se 1 (by rfl) ⟨1075904, by rfl⟩ : syracuseStep 1434539 = 2151809) B2151809
theorem B1434569 : Blo 952587 1434569 := bstep (se 2 (by rfl) ⟨537963, by rfl⟩ : syracuseStep 1434569 = 1075927) B1075927
theorem B1074235 : Blo 952587 1074235 := bstep (se 1 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 1074235 = 1611353) B1611353
theorem B1434683 : Blo 952587 1434683 := bstep (se 1 (by rfl) ⟨1076012, by rfl⟩ : syracuseStep 1434683 = 2152025) B2152025
theorem B1434743 : Blo 952587 1434743 := bstep (se 1 (by rfl) ⟨1076057, by rfl⟩ : syracuseStep 1434743 = 2152115) B2152115
theorem B1434767 : Blo 952587 1434767 := bstep (se 1 (by rfl) ⟨1076075, by rfl⟩ : syracuseStep 1434767 = 2152151) B2152151
theorem B1434809 : Blo 952587 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B2417921 : Blo 952587 2417921 := bstep (se 2 (by rfl) ⟨906720, by rfl⟩ : syracuseStep 2417921 = 1813441) B1813441
theorem B26076593 : Blo 952587 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B6284729 : Blo 952587 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B4351499 : Blo 952587 4351499 := bstep (se 1 (by rfl) ⟨3263624, by rfl⟩ : syracuseStep 4351499 = 6527249) B6527249
theorem B1074703 : Blo 952587 1074703 := bstep (se 1 (by rfl) ⟨806027, by rfl⟩ : syracuseStep 1074703 = 1612055) B1612055
theorem B6121003 : Blo 952587 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B13395557 : Blo 952587 13395557 := bstep (se 4 (by rfl) ⟨1255833, by rfl⟩ : syracuseStep 13395557 = 2511667) B2511667
theorem B2418295 : Blo 952587 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B8251073 : Blo 952587 8251073 := bstep (se 2 (by rfl) ⟨3094152, by rfl⟩ : syracuseStep 8251073 = 6188305) B6188305
theorem B2582387 : Blo 952587 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B2713601 : Blo 952587 2713601 := bstep (se 2 (by rfl) ⟨1017600, by rfl⟩ : syracuseStep 2713601 = 2035201) B2035201
theorem B1075207 : Blo 952587 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B2418731 : Blo 952587 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B1075387 : Blo 952587 1075387 := bstep (se 1 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 1075387 = 1613081) B1613081
theorem B5433601 : Blo 952587 5433601 := bstep (se 2 (by rfl) ⟨2037600, by rfl⟩ : syracuseStep 5433601 = 4075201) B4075201
theorem B1206571 : Blo 952587 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B3631513 : Blo 952587 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B2714057 : Blo 952587 2714057 := bstep (se 2 (by rfl) ⟨1017771, by rfl⟩ : syracuseStep 2714057 = 2035543) B2035543
theorem B9169361 : Blo 952587 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B1075855 : Blo 952587 1075855 := bstep (se 1 (by rfl) ⟨806891, by rfl⟩ : syracuseStep 1075855 = 1613783) B1613783
theorem B3631817 : Blo 952587 3631817 := bstep (se 2 (by rfl) ⟨1361931, by rfl⟩ : syracuseStep 3631817 = 2723863) B2723863
theorem B5434127 : Blo 952587 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B8711027 : Blo 952587 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B2419571 : Blo 952587 2419571 := bstep (se 1 (by rfl) ⟨1814678, by rfl⟩ : syracuseStep 2419571 = 3629357) B3629357
theorem B2419591 : Blo 952587 2419591 := bstep (se 1 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 2419591 = 3629387) B3629387
theorem B10873763 : Blo 952587 10873763 := bstep (se 1 (by rfl) ⟨8155322, by rfl⟩ : syracuseStep 10873763 = 16310645) B16310645
theorem B2419865 : Blo 952587 2419865 := bstep (se 2 (by rfl) ⟨907449, by rfl⟩ : syracuseStep 2419865 = 1814899) B1814899
theorem B1207543 : Blo 952587 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B2420027 : Blo 952587 2420027 := bstep (se 1 (by rfl) ⟨1815020, by rfl⟩ : syracuseStep 2420027 = 3630041) B3630041
theorem B8154503 : Blo 952587 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B1306027 : Blo 952587 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B27553283 : Blo 952587 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B2420239 : Blo 952587 2420239 := bstep (se 1 (by rfl) ⟨1815179, by rfl⟩ : syracuseStep 2420239 = 3630359) B3630359
theorem B1207867 : Blo 952587 1207867 := bstep (se 1 (by rfl) ⟨905900, by rfl⟩ : syracuseStep 1207867 = 1811801) B1811801
theorem B9072307 : Blo 952587 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B2420513 : Blo 952587 2420513 := bstep (se 2 (by rfl) ⟨907692, by rfl⟩ : syracuseStep 2420513 = 1815385) B1815385
theorem B2715707 : Blo 952587 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1241275 : Blo 952587 1241275 := bstep (se 1 (by rfl) ⟨930956, by rfl⟩ : syracuseStep 1241275 = 1861913) B1861913
theorem B5435585 : Blo 952587 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B6123721 : Blo 952587 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B1208839 : Blo 952587 1208839 := bstep (se 1 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 1208839 = 1813259) B1813259
theorem B3863069 : Blo 952587 3863069 := bstep (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) B1448651
theorem B3437099 : Blo 952587 3437099 := bstep (se 1 (by rfl) ⟨2577824, by rfl⟩ : syracuseStep 3437099 = 5155649) B5155649
theorem B2716345 : Blo 952587 2716345 := bstep (se 2 (by rfl) ⟨1018629, by rfl⟩ : syracuseStep 2716345 = 2037259) B2037259
theorem B2454391 : Blo 952587 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B1209259 : Blo 952587 1209259 := bstep (se 1 (by rfl) ⟨906944, by rfl⟩ : syracuseStep 1209259 = 1813889) B1813889
theorem B2716733 : Blo 952587 2716733 := bstep (se 3 (by rfl) ⟨509387, by rfl⟩ : syracuseStep 2716733 = 1018775) B1018775
theorem B1209487 : Blo 952587 1209487 := bstep (se 1 (by rfl) ⟨907115, by rfl⟩ : syracuseStep 1209487 = 1814231) B1814231
theorem B3864107 : Blo 952587 3864107 := bstep (se 1 (by rfl) ⟨2898080, by rfl⟩ : syracuseStep 3864107 = 5796161) B5796161
theorem B1210231 : Blo 952587 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B2291609 : Blo 952587 2291609 := bstep (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) B1718707
theorem B2717849 : Blo 952587 2717849 := bstep (se 2 (by rfl) ⟨1019193, by rfl⟩ : syracuseStep 2717849 = 2038387) B2038387
theorem B1210555 : Blo 952587 1210555 := bstep (se 1 (by rfl) ⟨907916, by rfl⟩ : syracuseStep 1210555 = 1815833) B1815833
theorem B5798279 : Blo 952587 5798279 := bstep (se 1 (by rfl) ⟨4348709, by rfl⟩ : syracuseStep 5798279 = 8697419) B8697419
theorem B5437975 : Blo 952587 5437975 := bstep (se 1 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 5437975 = 8156963) B8156963
theorem B1309303 : Blo 952587 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B3865403 : Blo 952587 3865403 := bstep (se 1 (by rfl) ⟨2899052, by rfl⟩ : syracuseStep 3865403 = 5798105) B5798105
theorem B1375147 : Blo 952587 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B1145863 : Blo 952587 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B7339031 : Blo 952587 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B1932331 : Blo 952587 1932331 := bstep (se 1 (by rfl) ⟨1449248, by rfl⟩ : syracuseStep 1932331 = 2898497) B2898497
theorem B12418181 : Blo 952587 12418181 := bstep (se 4 (by rfl) ⟨1164204, by rfl⟩ : syracuseStep 12418181 = 2328409) B2328409
theorem B1310137 : Blo 952587 1310137 := bstep (se 2 (by rfl) ⟨491301, by rfl⟩ : syracuseStep 1310137 = 982603) B982603
theorem B5799377 : Blo 952587 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B11599325 : Blo 952587 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B2719261 : Blo 952587 2719261 := bstep (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) B1019723
theorem B3669547 : Blo 952587 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B6520439 : Blo 952587 6520439 := bstep (se 1 (by rfl) ⟨4890329, by rfl⟩ : syracuseStep 6520439 = 9780659) B9780659
theorem B9174707 : Blo 952587 9174707 := bstep (se 1 (by rfl) ⟨6881030, by rfl⟩ : syracuseStep 9174707 = 13762061) B13762061
theorem B2719433 : Blo 952587 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B2719489 : Blo 952587 2719489 := bstep (se 2 (by rfl) ⟨1019808, by rfl⟩ : syracuseStep 2719489 = 2039617) B2039617
theorem B2752289 : Blo 952587 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B2752391 : Blo 952587 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B2719763 : Blo 952587 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B7241885 : Blo 952587 7241885 := bstep (se 3 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 7241885 = 2715707) B2715707
theorem B3670211 : Blo 952587 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B44597515 : Blo 952587 44597515 := bstep (se 1 (by rfl) ⟨33448136, by rfl⟩ : syracuseStep 44597515 = 66896273) B66896273
theorem B2720105 : Blo 952587 2720105 := bstep (se 2 (by rfl) ⟨1020039, by rfl⟩ : syracuseStep 2720105 = 2040079) B2040079
theorem B2294369 : Blo 952587 2294369 := bstep (se 2 (by rfl) ⟨860388, by rfl⟩ : syracuseStep 2294369 = 1720777) B1720777
theorem B6128567 : Blo 952587 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B3441911 : Blo 952587 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B2721289 : Blo 952587 2721289 := bstep (se 2 (by rfl) ⟨1020483, by rfl⟩ : syracuseStep 2721289 = 2040967) B2040967
theorem B3671687 : Blo 952587 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B3442475 : Blo 952587 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B1607519 : Blo 952587 1607519 := bstep (se 1 (by rfl) ⟨1205639, by rfl⟩ : syracuseStep 1607519 = 2411279) B2411279
theorem B2295647 : Blo 952587 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B1935265 : Blo 952587 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B1017895 : Blo 952587 1017895 := bstep (se 1 (by rfl) ⟨763421, by rfl⟩ : syracuseStep 1017895 = 1526843) B1526843
theorem B8161337 : Blo 952587 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B7342169 : Blo 952587 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B36767843 : Blo 952587 36767843 := bstep (se 1 (by rfl) ⟨27575882, by rfl⟩ : syracuseStep 36767843 = 55151765) B55151765
theorem B952615 : Blo 952587 952615 := bstep (se 1 (by rfl) ⟨714461, by rfl⟩ : syracuseStep 952615 = 1428923) B1428923
theorem B952655 : Blo 952587 952655 := bstep (se 1 (by rfl) ⟨714491, by rfl⟩ : syracuseStep 952655 = 1428983) B1428983
theorem B952671 : Blo 952587 952671 := bstep (se 1 (by rfl) ⟨714503, by rfl⟩ : syracuseStep 952671 = 1429007) B1429007
theorem B952699 : Blo 952587 952699 := bstep (se 1 (by rfl) ⟨714524, by rfl⟩ : syracuseStep 952699 = 1429049) B1429049
theorem B2722177 : Blo 952587 2722177 := bstep (se 2 (by rfl) ⟨1020816, by rfl⟩ : syracuseStep 2722177 = 2041633) B2041633
theorem B1608079 : Blo 952587 1608079 := bstep (se 1 (by rfl) ⟨1206059, by rfl⟩ : syracuseStep 1608079 = 2412119) B2412119
theorem B952751 : Blo 952587 952751 := bstep (se 1 (by rfl) ⟨714563, by rfl⟩ : syracuseStep 952751 = 1429127) B1429127
theorem B952775 : Blo 952587 952775 := bstep (se 1 (by rfl) ⟨714581, by rfl⟩ : syracuseStep 952775 = 1429163) B1429163
theorem B952795 : Blo 952587 952795 := bstep (se 1 (by rfl) ⟨714596, by rfl⟩ : syracuseStep 952795 = 1429193) B1429193
theorem B952871 : Blo 952587 952871 := bstep (se 1 (by rfl) ⟨714653, by rfl⟩ : syracuseStep 952871 = 1429307) B1429307
theorem B952911 : Blo 952587 952911 := bstep (se 1 (by rfl) ⟨714683, by rfl⟩ : syracuseStep 952911 = 1429367) B1429367
theorem B952927 : Blo 952587 952927 := bstep (se 1 (by rfl) ⟨714695, by rfl⟩ : syracuseStep 952927 = 1429391) B1429391
theorem B952955 : Blo 952587 952955 := bstep (se 1 (by rfl) ⟨714716, by rfl⟩ : syracuseStep 952955 = 1429433) B1429433
theorem B953007 : Blo 952587 953007 := bstep (se 1 (by rfl) ⟨714755, by rfl⟩ : syracuseStep 953007 = 1429511) B1429511
theorem B953031 : Blo 952587 953031 := bstep (se 1 (by rfl) ⟨714773, by rfl⟩ : syracuseStep 953031 = 1429547) B1429547
theorem B3443411 : Blo 952587 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B953051 : Blo 952587 953051 := bstep (se 1 (by rfl) ⟨714788, by rfl⟩ : syracuseStep 953051 = 1429577) B1429577
theorem B2329337 : Blo 952587 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B953127 : Blo 952587 953127 := bstep (se 1 (by rfl) ⟨714845, by rfl⟩ : syracuseStep 953127 = 1429691) B1429691
theorem B953167 : Blo 952587 953167 := bstep (se 1 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 953167 = 1429751) B1429751
theorem B953183 : Blo 952587 953183 := bstep (se 1 (by rfl) ⟨714887, by rfl⟩ : syracuseStep 953183 = 1429775) B1429775
theorem B953211 : Blo 952587 953211 := bstep (se 1 (by rfl) ⟨714908, by rfl⟩ : syracuseStep 953211 = 1429817) B1429817
theorem B953263 : Blo 952587 953263 := bstep (se 1 (by rfl) ⟨714947, by rfl⟩ : syracuseStep 953263 = 1429895) B1429895
theorem B19565495 : Blo 952587 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B2722747 : Blo 952587 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B953287 : Blo 952587 953287 := bstep (se 1 (by rfl) ⟨714965, by rfl⟩ : syracuseStep 953287 = 1429931) B1429931
theorem B953307 : Blo 952587 953307 := bstep (se 1 (by rfl) ⟨714980, by rfl⟩ : syracuseStep 953307 = 1429961) B1429961
theorem B17632241 : Blo 952587 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B7244801 : Blo 952587 7244801 := bstep (se 2 (by rfl) ⟨2716800, by rfl⟩ : syracuseStep 7244801 = 5433601) B5433601
theorem B953383 : Blo 952587 953383 := bstep (se 1 (by rfl) ⟨715037, by rfl⟩ : syracuseStep 953383 = 1430075) B1430075
theorem B1608761 : Blo 952587 1608761 := bstep (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) B1206571
theorem B953423 : Blo 952587 953423 := bstep (se 1 (by rfl) ⟨715067, by rfl⟩ : syracuseStep 953423 = 1430135) B1430135
theorem B953439 : Blo 952587 953439 := bstep (se 1 (by rfl) ⟨715079, by rfl⟩ : syracuseStep 953439 = 1430159) B1430159
theorem B953467 : Blo 952587 953467 := bstep (se 1 (by rfl) ⟨715100, by rfl⟩ : syracuseStep 953467 = 1430201) B1430201
theorem B953519 : Blo 952587 953519 := bstep (se 1 (by rfl) ⟨715139, by rfl⟩ : syracuseStep 953519 = 1430279) B1430279
theorem B953543 : Blo 952587 953543 := bstep (se 1 (by rfl) ⟨715157, by rfl⟩ : syracuseStep 953543 = 1430315) B1430315
theorem B1936595 : Blo 952587 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B953563 : Blo 952587 953563 := bstep (se 1 (by rfl) ⟨715172, by rfl⟩ : syracuseStep 953563 = 1430345) B1430345
theorem B953639 : Blo 952587 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B953679 : Blo 952587 953679 := bstep (se 1 (by rfl) ⟨715259, by rfl⟩ : syracuseStep 953679 = 1430519) B1430519
theorem B953695 : Blo 952587 953695 := bstep (se 1 (by rfl) ⟨715271, by rfl⟩ : syracuseStep 953695 = 1430543) B1430543
theorem B953723 : Blo 952587 953723 := bstep (se 1 (by rfl) ⟨715292, by rfl⟩ : syracuseStep 953723 = 1430585) B1430585
theorem B953775 : Blo 952587 953775 := bstep (se 1 (by rfl) ⟨715331, by rfl⟩ : syracuseStep 953775 = 1430663) B1430663
theorem B953799 : Blo 952587 953799 := bstep (se 1 (by rfl) ⟨715349, by rfl⟩ : syracuseStep 953799 = 1430699) B1430699
theorem B953819 : Blo 952587 953819 := bstep (se 1 (by rfl) ⟨715364, by rfl⟩ : syracuseStep 953819 = 1430729) B1430729
theorem B953895 : Blo 952587 953895 := bstep (se 1 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 953895 = 1430843) B1430843
theorem B953935 : Blo 952587 953935 := bstep (se 1 (by rfl) ⟨715451, by rfl⟩ : syracuseStep 953935 = 1430903) B1430903
theorem B953951 : Blo 952587 953951 := bstep (se 1 (by rfl) ⟨715463, by rfl⟩ : syracuseStep 953951 = 1430927) B1430927
theorem B6524513 : Blo 952587 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B953979 : Blo 952587 953979 := bstep (se 1 (by rfl) ⟨715484, by rfl⟩ : syracuseStep 953979 = 1430969) B1430969
theorem B954031 : Blo 952587 954031 := bstep (se 1 (by rfl) ⟨715523, by rfl⟩ : syracuseStep 954031 = 1431047) B1431047
theorem B954055 : Blo 952587 954055 := bstep (se 1 (by rfl) ⟨715541, by rfl⟩ : syracuseStep 954055 = 1431083) B1431083
theorem B954075 : Blo 952587 954075 := bstep (se 1 (by rfl) ⟨715556, by rfl⟩ : syracuseStep 954075 = 1431113) B1431113
theorem B1609463 : Blo 952587 1609463 := bstep (se 1 (by rfl) ⟨1207097, by rfl⟩ : syracuseStep 1609463 = 2414195) B2414195
theorem B954151 : Blo 952587 954151 := bstep (se 1 (by rfl) ⟨715613, by rfl⟩ : syracuseStep 954151 = 1431227) B1431227
theorem B954191 : Blo 952587 954191 := bstep (se 1 (by rfl) ⟨715643, by rfl⟩ : syracuseStep 954191 = 1431287) B1431287
theorem B954207 : Blo 952587 954207 := bstep (se 1 (by rfl) ⟨715655, by rfl⟩ : syracuseStep 954207 = 1431311) B1431311
theorem B12226423 : Blo 952587 12226423 := bstep (se 1 (by rfl) ⟨9169817, by rfl⟩ : syracuseStep 12226423 = 18339635) B18339635
theorem B954235 : Blo 952587 954235 := bstep (se 1 (by rfl) ⟨715676, by rfl⟩ : syracuseStep 954235 = 1431353) B1431353
theorem B26480533 : Blo 952587 26480533 := bstep (se 6 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 26480533 = 1241275) B1241275
theorem B954287 : Blo 952587 954287 := bstep (se 1 (by rfl) ⟨715715, by rfl⟩ : syracuseStep 954287 = 1431431) B1431431
theorem B954311 : Blo 952587 954311 := bstep (se 1 (by rfl) ⟨715733, by rfl⟩ : syracuseStep 954311 = 1431467) B1431467
theorem B7966673 : Blo 952587 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B954331 : Blo 952587 954331 := bstep (se 1 (by rfl) ⟨715748, by rfl⟩ : syracuseStep 954331 = 1431497) B1431497
theorem B3215375 : Blo 952587 3215375 := bstep (se 1 (by rfl) ⟨2411531, by rfl⟩ : syracuseStep 3215375 = 4823063) B4823063
theorem B954407 : Blo 952587 954407 := bstep (se 1 (by rfl) ⟨715805, by rfl⟩ : syracuseStep 954407 = 1431611) B1431611
theorem B1609807 : Blo 952587 1609807 := bstep (se 1 (by rfl) ⟨1207355, by rfl⟩ : syracuseStep 1609807 = 2414711) B2414711
theorem B954447 : Blo 952587 954447 := bstep (se 1 (by rfl) ⟨715835, by rfl⟩ : syracuseStep 954447 = 1431671) B1431671
theorem B954463 : Blo 952587 954463 := bstep (se 1 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 954463 = 1431695) B1431695
theorem B954491 : Blo 952587 954491 := bstep (se 1 (by rfl) ⟨715868, by rfl⟩ : syracuseStep 954491 = 1431737) B1431737
theorem B954543 : Blo 952587 954543 := bstep (se 1 (by rfl) ⟨715907, by rfl⟩ : syracuseStep 954543 = 1431815) B1431815
theorem B954567 : Blo 952587 954567 := bstep (se 1 (by rfl) ⟨715925, by rfl⟩ : syracuseStep 954567 = 1431851) B1431851
theorem B954587 : Blo 952587 954587 := bstep (se 1 (by rfl) ⟨715940, by rfl⟩ : syracuseStep 954587 = 1431881) B1431881
theorem B954663 : Blo 952587 954663 := bstep (se 1 (by rfl) ⟨715997, by rfl⟩ : syracuseStep 954663 = 1431995) B1431995
theorem B1610057 : Blo 952587 1610057 := bstep (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) B1207543
theorem B954703 : Blo 952587 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B954719 : Blo 952587 954719 := bstep (se 1 (by rfl) ⟨716039, by rfl⟩ : syracuseStep 954719 = 1432079) B1432079
theorem B954747 : Blo 952587 954747 := bstep (se 1 (by rfl) ⟨716060, by rfl⟩ : syracuseStep 954747 = 1432121) B1432121
theorem B2298241 : Blo 952587 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B954799 : Blo 952587 954799 := bstep (se 1 (by rfl) ⟨716099, by rfl⟩ : syracuseStep 954799 = 1432199) B1432199
theorem B954823 : Blo 952587 954823 := bstep (se 1 (by rfl) ⟨716117, by rfl⟩ : syracuseStep 954823 = 1432235) B1432235
theorem B954843 : Blo 952587 954843 := bstep (se 1 (by rfl) ⟨716132, by rfl⟩ : syracuseStep 954843 = 1432265) B1432265
theorem B3052019 : Blo 952587 3052019 := bstep (se 1 (by rfl) ⟨2289014, by rfl⟩ : syracuseStep 3052019 = 4578029) B4578029
theorem B954919 : Blo 952587 954919 := bstep (se 1 (by rfl) ⟨716189, by rfl⟩ : syracuseStep 954919 = 1432379) B1432379
theorem B954959 : Blo 952587 954959 := bstep (se 1 (by rfl) ⟨716219, by rfl⟩ : syracuseStep 954959 = 1432439) B1432439
theorem B954975 : Blo 952587 954975 := bstep (se 1 (by rfl) ⟨716231, by rfl⟩ : syracuseStep 954975 = 1432463) B1432463
theorem B3215969 : Blo 952587 3215969 := bstep (se 2 (by rfl) ⟨1205988, by rfl⟩ : syracuseStep 3215969 = 2411977) B2411977
theorem B955003 : Blo 952587 955003 := bstep (se 1 (by rfl) ⟨716252, by rfl⟩ : syracuseStep 955003 = 1432505) B1432505
theorem B955055 : Blo 952587 955055 := bstep (se 1 (by rfl) ⟨716291, by rfl⟩ : syracuseStep 955055 = 1432583) B1432583
theorem B955079 : Blo 952587 955079 := bstep (se 1 (by rfl) ⟨716309, by rfl⟩ : syracuseStep 955079 = 1432619) B1432619
theorem B955099 : Blo 952587 955099 := bstep (se 1 (by rfl) ⟨716324, by rfl⟩ : syracuseStep 955099 = 1432649) B1432649
theorem B1610489 : Blo 952587 1610489 := bstep (se 2 (by rfl) ⟨603933, by rfl⟩ : syracuseStep 1610489 = 1207867) B1207867
theorem B24843023 : Blo 952587 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B955175 : Blo 952587 955175 := bstep (se 1 (by rfl) ⟨716381, by rfl⟩ : syracuseStep 955175 = 1432763) B1432763
theorem B955215 : Blo 952587 955215 := bstep (se 1 (by rfl) ⟨716411, by rfl⟩ : syracuseStep 955215 = 1432823) B1432823
theorem B955231 : Blo 952587 955231 := bstep (se 1 (by rfl) ⟨716423, by rfl⟩ : syracuseStep 955231 = 1432847) B1432847
theorem B955259 : Blo 952587 955259 := bstep (se 1 (by rfl) ⟨716444, by rfl⟩ : syracuseStep 955259 = 1432889) B1432889
theorem B1610671 : Blo 952587 1610671 := bstep (se 1 (by rfl) ⟨1208003, by rfl⟩ : syracuseStep 1610671 = 2416007) B2416007
theorem B955311 : Blo 952587 955311 := bstep (se 1 (by rfl) ⟨716483, by rfl⟩ : syracuseStep 955311 = 1432967) B1432967
theorem B955335 : Blo 952587 955335 := bstep (se 1 (by rfl) ⟨716501, by rfl⟩ : syracuseStep 955335 = 1433003) B1433003
theorem B955355 : Blo 952587 955355 := bstep (se 1 (by rfl) ⟨716516, by rfl⟩ : syracuseStep 955355 = 1433033) B1433033
theorem B1610759 : Blo 952587 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B955431 : Blo 952587 955431 := bstep (se 1 (by rfl) ⟨716573, by rfl⟩ : syracuseStep 955431 = 1433147) B1433147
theorem B955471 : Blo 952587 955471 := bstep (se 1 (by rfl) ⟨716603, by rfl⟩ : syracuseStep 955471 = 1433207) B1433207
theorem B955487 : Blo 952587 955487 := bstep (se 1 (by rfl) ⟨716615, by rfl⟩ : syracuseStep 955487 = 1433231) B1433231
theorem B955515 : Blo 952587 955515 := bstep (se 1 (by rfl) ⟨716636, by rfl⟩ : syracuseStep 955515 = 1433273) B1433273
theorem B955567 : Blo 952587 955567 := bstep (se 1 (by rfl) ⟨716675, by rfl⟩ : syracuseStep 955567 = 1433351) B1433351
theorem B955591 : Blo 952587 955591 := bstep (se 1 (by rfl) ⟨716693, by rfl⟩ : syracuseStep 955591 = 1433387) B1433387
theorem B955611 : Blo 952587 955611 := bstep (se 1 (by rfl) ⟨716708, by rfl⟩ : syracuseStep 955611 = 1433417) B1433417
theorem B955687 : Blo 952587 955687 := bstep (se 1 (by rfl) ⟨716765, by rfl⟩ : syracuseStep 955687 = 1433531) B1433531
theorem B955727 : Blo 952587 955727 := bstep (se 1 (by rfl) ⟨716795, by rfl⟩ : syracuseStep 955727 = 1433591) B1433591
theorem B1611103 : Blo 952587 1611103 := bstep (se 1 (by rfl) ⟨1208327, by rfl⟩ : syracuseStep 1611103 = 2416655) B2416655
theorem B955743 : Blo 952587 955743 := bstep (se 1 (by rfl) ⟨716807, by rfl⟩ : syracuseStep 955743 = 1433615) B1433615
theorem B955771 : Blo 952587 955771 := bstep (se 1 (by rfl) ⟨716828, by rfl⟩ : syracuseStep 955771 = 1433657) B1433657
theorem B955823 : Blo 952587 955823 := bstep (se 1 (by rfl) ⟨716867, by rfl⟩ : syracuseStep 955823 = 1433735) B1433735
theorem B1611191 : Blo 952587 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B955847 : Blo 952587 955847 := bstep (se 1 (by rfl) ⟨716885, by rfl⟩ : syracuseStep 955847 = 1433771) B1433771
theorem B955867 : Blo 952587 955867 := bstep (se 1 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 955867 = 1433801) B1433801
theorem B5445083 : Blo 952587 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B3872281 : Blo 952587 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B955943 : Blo 952587 955943 := bstep (se 1 (by rfl) ⟨716957, by rfl⟩ : syracuseStep 955943 = 1433915) B1433915
theorem B955983 : Blo 952587 955983 := bstep (se 1 (by rfl) ⟨716987, by rfl⟩ : syracuseStep 955983 = 1433975) B1433975
theorem B955999 : Blo 952587 955999 := bstep (se 1 (by rfl) ⟨716999, by rfl⟩ : syracuseStep 955999 = 1433999) B1433999
theorem B8164961 : Blo 952587 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B956027 : Blo 952587 956027 := bstep (se 1 (by rfl) ⟨717020, by rfl⟩ : syracuseStep 956027 = 1434041) B1434041
theorem B5445265 : Blo 952587 5445265 := bstep (se 2 (by rfl) ⟨2041974, by rfl⟩ : syracuseStep 5445265 = 4083949) B4083949
theorem B956079 : Blo 952587 956079 := bstep (se 1 (by rfl) ⟨717059, by rfl⟩ : syracuseStep 956079 = 1434119) B1434119
theorem B956103 : Blo 952587 956103 := bstep (se 1 (by rfl) ⟨717077, by rfl⟩ : syracuseStep 956103 = 1434155) B1434155
theorem B956123 : Blo 952587 956123 := bstep (se 1 (by rfl) ⟨717092, by rfl⟩ : syracuseStep 956123 = 1434185) B1434185
theorem B956199 : Blo 952587 956199 := bstep (se 1 (by rfl) ⟨717149, by rfl⟩ : syracuseStep 956199 = 1434299) B1434299
theorem B4069187 : Blo 952587 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B956239 : Blo 952587 956239 := bstep (se 1 (by rfl) ⟨717179, by rfl⟩ : syracuseStep 956239 = 1434359) B1434359
theorem B956255 : Blo 952587 956255 := bstep (se 1 (by rfl) ⟨717191, by rfl⟩ : syracuseStep 956255 = 1434383) B1434383
theorem B3676013 : Blo 952587 3676013 := bstep (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) B1378505
theorem B956283 : Blo 952587 956283 := bstep (se 1 (by rfl) ⟨717212, by rfl⟩ : syracuseStep 956283 = 1434425) B1434425
theorem B956335 : Blo 952587 956335 := bstep (se 1 (by rfl) ⟨717251, by rfl⟩ : syracuseStep 956335 = 1434503) B1434503
theorem B956359 : Blo 952587 956359 := bstep (se 1 (by rfl) ⟨717269, by rfl⟩ : syracuseStep 956359 = 1434539) B1434539
theorem B956379 : Blo 952587 956379 := bstep (se 1 (by rfl) ⟨717284, by rfl⟩ : syracuseStep 956379 = 1434569) B1434569
theorem B1611785 : Blo 952587 1611785 := bstep (se 2 (by rfl) ⟨604419, by rfl⟩ : syracuseStep 1611785 = 1208839) B1208839
theorem B3217427 : Blo 952587 3217427 := bstep (se 1 (by rfl) ⟨2413070, by rfl⟩ : syracuseStep 3217427 = 4826141) B4826141
theorem B956455 : Blo 952587 956455 := bstep (se 1 (by rfl) ⟨717341, by rfl⟩ : syracuseStep 956455 = 1434683) B1434683
theorem B956495 : Blo 952587 956495 := bstep (se 1 (by rfl) ⟨717371, by rfl⟩ : syracuseStep 956495 = 1434743) B1434743
theorem B6887513 : Blo 952587 6887513 := bstep (se 2 (by rfl) ⟨2582817, by rfl⟩ : syracuseStep 6887513 = 5165635) B5165635
theorem B956511 : Blo 952587 956511 := bstep (se 1 (by rfl) ⟨717383, by rfl⟩ : syracuseStep 956511 = 1434767) B1434767
theorem B956539 : Blo 952587 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B1611947 : Blo 952587 1611947 := bstep (se 1 (by rfl) ⟨1208960, by rfl⟩ : syracuseStep 1611947 = 2417921) B2417921
theorem B10885427 : Blo 952587 10885427 := bstep (se 1 (by rfl) ⟨8164070, by rfl⟩ : syracuseStep 10885427 = 16328141) B16328141
theorem B3217751 : Blo 952587 3217751 := bstep (se 1 (by rfl) ⟨2413313, by rfl⟩ : syracuseStep 3217751 = 4826627) B4826627
theorem B1808801 : Blo 952587 1808801 := bstep (se 2 (by rfl) ⟨678300, by rfl⟩ : syracuseStep 1808801 = 1356601) B1356601
theorem B13769261 : Blo 952587 13769261 := bstep (se 3 (by rfl) ⟨2581736, by rfl⟩ : syracuseStep 13769261 = 5163473) B5163473
theorem B1612345 : Blo 952587 1612345 := bstep (se 2 (by rfl) ⟨604629, by rfl⟩ : syracuseStep 1612345 = 1209259) B1209259
theorem B1809067 : Blo 952587 1809067 := bstep (se 1 (by rfl) ⟨1356800, by rfl⟩ : syracuseStep 1809067 = 2713601) B2713601
theorem B1612487 : Blo 952587 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B1612649 : Blo 952587 1612649 := bstep (se 2 (by rfl) ⟨604743, by rfl⟩ : syracuseStep 1612649 = 1209487) B1209487
theorem B1809371 : Blo 952587 1809371 := bstep (se 1 (by rfl) ⟨1357028, by rfl⟩ : syracuseStep 1809371 = 2714057) B2714057
theorem B4136107 : Blo 952587 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B5807351 : Blo 952587 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B1613047 : Blo 952587 1613047 := bstep (se 1 (by rfl) ⟨1209785, by rfl⟩ : syracuseStep 1613047 = 2419571) B2419571
theorem B7249175 : Blo 952587 7249175 := bstep (se 1 (by rfl) ⟨5436881, by rfl⟩ : syracuseStep 7249175 = 10873763) B10873763
theorem B3218831 : Blo 952587 3218831 := bstep (se 1 (by rfl) ⟨2414123, by rfl⟩ : syracuseStep 3218831 = 4828247) B4828247
theorem B1613243 : Blo 952587 1613243 := bstep (se 1 (by rfl) ⟨1209932, by rfl⟩ : syracuseStep 1613243 = 2419865) B2419865
theorem B4824521 : Blo 952587 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B1613351 : Blo 952587 1613351 := bstep (se 1 (by rfl) ⟨1210013, by rfl⟩ : syracuseStep 1613351 = 2420027) B2420027
theorem B6987397 : Blo 952587 6987397 := bstep (se 4 (by rfl) ⟨655068, by rfl⟩ : syracuseStep 6987397 = 1310137) B1310137
theorem B3219155 : Blo 952587 3219155 := bstep (se 1 (by rfl) ⟨2414366, by rfl⟩ : syracuseStep 3219155 = 4828733) B4828733
theorem B1449721 : Blo 952587 1449721 := bstep (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) B1087291
theorem B6528761 : Blo 952587 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B1613641 : Blo 952587 1613641 := bstep (se 2 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 1613641 = 1210231) B1210231
theorem B1613675 : Blo 952587 1613675 := bstep (se 1 (by rfl) ⟨1210256, by rfl⟩ : syracuseStep 1613675 = 2420513) B2420513
theorem B1449911 : Blo 952587 1449911 := bstep (se 1 (by rfl) ⟨1087433, by rfl⟩ : syracuseStep 1449911 = 2174867) B2174867
theorem B1810441 : Blo 952587 1810441 := bstep (se 2 (by rfl) ⟨678915, by rfl⟩ : syracuseStep 1810441 = 1357831) B1357831
theorem B4825169 : Blo 952587 4825169 := bstep (se 2 (by rfl) ⟨1809438, by rfl⟩ : syracuseStep 4825169 = 3618877) B3618877
theorem B10330193 : Blo 952587 10330193 := bstep (se 2 (by rfl) ⟨3873822, by rfl⟩ : syracuseStep 10330193 = 7747645) B7747645
theorem B1614073 : Blo 952587 1614073 := bstep (se 2 (by rfl) ⟨605277, by rfl⟩ : syracuseStep 1614073 = 1210555) B1210555
theorem B7250633 : Blo 952587 7250633 := bstep (se 2 (by rfl) ⟨2718987, by rfl⟩ : syracuseStep 7250633 = 5437975) B5437975
theorem B1811155 : Blo 952587 1811155 := bstep (se 1 (by rfl) ⟨1358366, by rfl⟩ : syracuseStep 1811155 = 2716733) B2716733
theorem B1745737 : Blo 952587 1745737 := bstep (se 2 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 1745737 = 1309303) B1309303
theorem B3220343 : Blo 952587 3220343 := bstep (se 1 (by rfl) ⟨2415257, by rfl⟩ : syracuseStep 3220343 = 4830515) B4830515
theorem B3220559 : Blo 952587 3220559 := bstep (se 1 (by rfl) ⟨2415419, by rfl⟩ : syracuseStep 3220559 = 4830839) B4830839
theorem B1811899 : Blo 952587 1811899 := bstep (se 1 (by rfl) ⟨1358924, by rfl⟩ : syracuseStep 1811899 = 2717849) B2717849
theorem B3220937 : Blo 952587 3220937 := bstep (se 2 (by rfl) ⟨1207851, by rfl⟩ : syracuseStep 3220937 = 2415703) B2415703
theorem B7743073 : Blo 952587 7743073 := bstep (se 2 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 7743073 = 5807305) B5807305
theorem B3221207 : Blo 952587 3221207 := bstep (se 1 (by rfl) ⟨2415905, by rfl⟩ : syracuseStep 3221207 = 4831811) B4831811
theorem B1812385 : Blo 952587 1812385 := bstep (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) B1359289
theorem B3221423 : Blo 952587 3221423 := bstep (se 1 (by rfl) ⟨2416067, by rfl⟩ : syracuseStep 3221423 = 4832135) B4832135
theorem B2041787 : Blo 952587 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B4892687 : Blo 952587 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B4892729 : Blo 952587 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B1812955 : Blo 952587 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B2239073 : Blo 952587 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B21179015 : Blo 952587 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B4074313 : Blo 952587 4074313 := bstep (se 2 (by rfl) ⟨1527867, by rfl⟩ : syracuseStep 4074313 = 3055735) B3055735
theorem B13085813 : Blo 952587 13085813 := bstep (se 5 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 13085813 = 1226795) B1226795
theorem B4075373 : Blo 952587 4075373 := bstep (se 3 (by rfl) ⟨764132, by rfl⟩ : syracuseStep 4075373 = 1528265) B1528265
theorem B30978125 : Blo 952587 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B9187505 : Blo 952587 9187505 := bstep (se 2 (by rfl) ⟨3445314, by rfl⟩ : syracuseStep 9187505 = 6890629) B6890629
theorem B3223799 : Blo 952587 3223799 := bstep (se 1 (by rfl) ⟨2417849, by rfl⟩ : syracuseStep 3223799 = 4835699) B4835699
theorem B10334729 : Blo 952587 10334729 := bstep (se 2 (by rfl) ⟨3875523, by rfl⟩ : syracuseStep 10334729 = 7751047) B7751047
theorem B4829705 : Blo 952587 4829705 := bstep (se 2 (by rfl) ⟨1811139, by rfl⟩ : syracuseStep 4829705 = 3622279) B3622279
theorem B3224123 : Blo 952587 3224123 := bstep (se 1 (by rfl) ⟨2418092, by rfl⟩ : syracuseStep 3224123 = 4836185) B4836185
theorem B1815119 : Blo 952587 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B1552975 : Blo 952587 1552975 := bstep (se 1 (by rfl) ⟨1164731, by rfl⟩ : syracuseStep 1552975 = 2329463) B2329463
theorem B3617419 : Blo 952587 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B3224393 : Blo 952587 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B3617723 : Blo 952587 3617723 := bstep (se 1 (by rfl) ⟨2713292, by rfl⟩ : syracuseStep 3617723 = 5426585) B5426585
theorem B2143403 : Blo 952587 2143403 := bstep (se 1 (by rfl) ⟨1607552, by rfl⟩ : syracuseStep 2143403 = 3215105) B3215105
theorem B3061003 : Blo 952587 3061003 := bstep (se 1 (by rfl) ⟨2295752, by rfl⟩ : syracuseStep 3061003 = 4591505) B4591505
theorem B6534695 : Blo 952587 6534695 := bstep (se 1 (by rfl) ⟨4901021, by rfl⟩ : syracuseStep 6534695 = 9802043) B9802043
theorem B2143943 : Blo 952587 2143943 := bstep (se 1 (by rfl) ⟨1607957, by rfl⟩ : syracuseStep 2143943 = 3215915) B3215915
theorem B3225527 : Blo 952587 3225527 := bstep (se 1 (by rfl) ⟨2419145, by rfl⟩ : syracuseStep 3225527 = 4838291) B4838291
theorem B4831163 : Blo 952587 4831163 := bstep (se 1 (by rfl) ⟨3623372, by rfl⟩ : syracuseStep 4831163 = 7246745) B7246745
theorem B8141107 : Blo 952587 8141107 := bstep (se 1 (by rfl) ⟨6105830, by rfl⟩ : syracuseStep 8141107 = 12211661) B12211661
theorem B3226121 : Blo 952587 3226121 := bstep (se 2 (by rfl) ⟨1209795, by rfl⟩ : syracuseStep 3226121 = 2419591) B2419591
theorem B2144807 : Blo 952587 2144807 := bstep (se 1 (by rfl) ⟨1608605, by rfl⟩ : syracuseStep 2144807 = 3217211) B3217211
theorem B2145131 : Blo 952587 2145131 := bstep (se 1 (by rfl) ⟨1608848, by rfl⟩ : syracuseStep 2145131 = 3217697) B3217697
theorem B2145185 : Blo 952587 2145185 := bstep (se 2 (by rfl) ⟨804444, by rfl⟩ : syracuseStep 2145185 = 1608889) B1608889
theorem B25476227 : Blo 952587 25476227 := bstep (se 1 (by rfl) ⟨19107170, by rfl⟩ : syracuseStep 25476227 = 38214341) B38214341
theorem B4832459 : Blo 952587 4832459 := bstep (se 1 (by rfl) ⟨3624344, by rfl⟩ : syracuseStep 4832459 = 7248689) B7248689
theorem B2145527 : Blo 952587 2145527 := bstep (se 1 (by rfl) ⟨1609145, by rfl⟩ : syracuseStep 2145527 = 3218291) B3218291
theorem B13090085 : Blo 952587 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B3226985 : Blo 952587 3226985 := bstep (se 2 (by rfl) ⟨1210119, by rfl⟩ : syracuseStep 3226985 = 2420239) B2420239
theorem B4963727 : Blo 952587 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B6110957 : Blo 952587 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B7257923 : Blo 952587 7257923 := bstep (se 1 (by rfl) ⟨5443442, by rfl⟩ : syracuseStep 7257923 = 10886885) B10886885
theorem B2146121 : Blo 952587 2146121 := bstep (se 2 (by rfl) ⟨804795, by rfl⟩ : syracuseStep 2146121 = 1609591) B1609591
theorem B1720207 : Blo 952587 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B104677271 : Blo 952587 104677271 := bstep (se 1 (by rfl) ⟨78507953, by rfl⟩ : syracuseStep 104677271 = 157015907) B157015907
theorem B3227579 : Blo 952587 3227579 := bstep (se 1 (by rfl) ⟨2420684, by rfl⟩ : syracuseStep 3227579 = 4841369) B4841369
theorem B1359995 : Blo 952587 1359995 := bstep (se 1 (by rfl) ⟨1019996, by rfl⟩ : syracuseStep 1359995 = 2039993) B2039993
theorem B3064193 : Blo 952587 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B2146913 : Blo 952587 2146913 := bstep (se 2 (by rfl) ⟨805092, by rfl⟩ : syracuseStep 2146913 = 1610185) B1610185
theorem B5161657 : Blo 952587 5161657 := bstep (se 2 (by rfl) ⟨1935621, by rfl⟩ : syracuseStep 5161657 = 3871243) B3871243
theorem B1360633 : Blo 952587 1360633 := bstep (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) B1020475
theorem B1360747 : Blo 952587 1360747 := bstep (se 1 (by rfl) ⟨1020560, by rfl⟩ : syracuseStep 1360747 = 2041121) B2041121
theorem B3621793 : Blo 952587 3621793 := bstep (se 2 (by rfl) ⟨1358172, by rfl⟩ : syracuseStep 3621793 = 2716345) B2716345
theorem B2147255 : Blo 952587 2147255 := bstep (se 1 (by rfl) ⟨1610441, by rfl⟩ : syracuseStep 2147255 = 3220883) B3220883
theorem B17384395 : Blo 952587 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B2900999 : Blo 952587 2900999 := bstep (se 1 (by rfl) ⟨2175749, by rfl⟩ : syracuseStep 2900999 = 4351499) B4351499
theorem B8930371 : Blo 952587 8930371 := bstep (se 1 (by rfl) ⟨6697778, by rfl⟩ : syracuseStep 8930371 = 13395557) B13395557
theorem B1360975 : Blo 952587 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B1721591 : Blo 952587 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B2147849 : Blo 952587 2147849 := bstep (se 2 (by rfl) ⟨805443, by rfl⟩ : syracuseStep 2147849 = 1610887) B1610887
theorem B6112907 : Blo 952587 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B3622751 : Blo 952587 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B2148191 : Blo 952587 2148191 := bstep (se 1 (by rfl) ⟨1611143, by rfl⟩ : syracuseStep 2148191 = 3222287) B3222287
theorem B3622765 : Blo 952587 3622765 := bstep (se 3 (by rfl) ⟨679268, by rfl⟩ : syracuseStep 3622765 = 1358537) B1358537
theorem B2148371 : Blo 952587 2148371 := bstep (se 1 (by rfl) ⟨1611278, by rfl⟩ : syracuseStep 2148371 = 3222557) B3222557
theorem B30951517 : Blo 952587 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B10307741 : Blo 952587 10307741 := bstep (se 3 (by rfl) ⟨1932701, by rfl⟩ : syracuseStep 10307741 = 3865403) B3865403
theorem B3623069 : Blo 952587 3623069 := bstep (se 3 (by rfl) ⟨679325, by rfl⟩ : syracuseStep 3623069 = 1358651) B1358651
theorem B6965477 : Blo 952587 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B18368855 : Blo 952587 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B2148713 : Blo 952587 2148713 := bstep (se 2 (by rfl) ⟨805767, by rfl⟩ : syracuseStep 2148713 = 1611535) B1611535
theorem B969311 : Blo 952587 969311 := bstep (se 1 (by rfl) ⟨726983, by rfl⟩ : syracuseStep 969311 = 1453967) B1453967
theorem B3623723 : Blo 952587 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B2149307 : Blo 952587 2149307 := bstep (se 1 (by rfl) ⟨1611980, by rfl⟩ : syracuseStep 2149307 = 3223961) B3223961
theorem B2575379 : Blo 952587 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B2149433 : Blo 952587 2149433 := bstep (se 2 (by rfl) ⟨806037, by rfl⟩ : syracuseStep 2149433 = 1612075) B1612075
theorem B2149775 : Blo 952587 2149775 := bstep (se 1 (by rfl) ⟨1612331, by rfl⟩ : syracuseStep 2149775 = 3224663) B3224663
theorem B1428911 : Blo 952587 1428911 := bstep (se 1 (by rfl) ⟨1071683, by rfl⟩ : syracuseStep 1428911 = 2143367) B2143367
theorem B1429001 : Blo 952587 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B1429031 : Blo 952587 1429031 := bstep (se 1 (by rfl) ⟨1071773, by rfl⟩ : syracuseStep 1429031 = 2143547) B2143547
theorem B48385637 : Blo 952587 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B1429115 : Blo 952587 1429115 := bstep (se 1 (by rfl) ⟨1071836, by rfl⟩ : syracuseStep 1429115 = 2143673) B2143673
theorem B2576071 : Blo 952587 2576071 := bstep (se 1 (by rfl) ⟨1932053, by rfl⟩ : syracuseStep 2576071 = 3864107) B3864107
theorem B2150099 : Blo 952587 2150099 := bstep (se 1 (by rfl) ⟨1612574, by rfl⟩ : syracuseStep 2150099 = 3225149) B3225149
theorem B1429241 : Blo 952587 1429241 := bstep (se 2 (by rfl) ⟨535965, by rfl⟩ : syracuseStep 1429241 = 1071931) B1071931
theorem B2412281 : Blo 952587 2412281 := bstep (se 2 (by rfl) ⟨904605, by rfl⟩ : syracuseStep 2412281 = 1809211) B1809211
theorem B1429343 : Blo 952587 1429343 := bstep (se 1 (by rfl) ⟨1072007, by rfl⟩ : syracuseStep 1429343 = 2144015) B2144015
theorem B1429355 : Blo 952587 1429355 := bstep (se 1 (by rfl) ⟨1072016, by rfl⟩ : syracuseStep 1429355 = 2144033) B2144033
theorem B2412463 : Blo 952587 2412463 := bstep (se 1 (by rfl) ⟨1809347, by rfl⟩ : syracuseStep 2412463 = 3618695) B3618695
theorem B1527817 : Blo 952587 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B2576441 : Blo 952587 2576441 := bstep (se 2 (by rfl) ⟨966165, by rfl⟩ : syracuseStep 2576441 = 1932331) B1932331
theorem B1429583 : Blo 952587 1429583 := bstep (se 1 (by rfl) ⟨1072187, by rfl⟩ : syracuseStep 1429583 = 2144375) B2144375
theorem B7262297 : Blo 952587 7262297 := bstep (se 2 (by rfl) ⟨2723361, by rfl⟩ : syracuseStep 7262297 = 5446723) B5446723
theorem B1429703 : Blo 952587 1429703 := bstep (se 1 (by rfl) ⟨1072277, by rfl⟩ : syracuseStep 1429703 = 2144555) B2144555
theorem B4837643 : Blo 952587 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B1429865 : Blo 952587 1429865 := bstep (se 2 (by rfl) ⟨536199, by rfl⟩ : syracuseStep 1429865 = 1072399) B1072399
theorem B2412929 : Blo 952587 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B1429943 : Blo 952587 1429943 := bstep (se 1 (by rfl) ⟨1072457, by rfl⟩ : syracuseStep 1429943 = 2144915) B2144915
theorem B1429979 : Blo 952587 1429979 := bstep (se 1 (by rfl) ⟨1072484, by rfl⟩ : syracuseStep 1429979 = 2144969) B2144969
theorem B8147465 : Blo 952587 8147465 := bstep (se 2 (by rfl) ⟨3055299, by rfl⟩ : syracuseStep 8147465 = 6110599) B6110599
theorem B3265049 : Blo 952587 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B2151035 : Blo 952587 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B3625681 : Blo 952587 3625681 := bstep (se 2 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 3625681 = 2719261) B2719261
theorem B2151161 : Blo 952587 2151161 := bstep (se 2 (by rfl) ⟨806685, by rfl⟩ : syracuseStep 2151161 = 1613371) B1613371
theorem B8278787 : Blo 952587 8278787 := bstep (se 1 (by rfl) ⟨6209090, by rfl⟩ : syracuseStep 8278787 = 12418181) B12418181
theorem B2413385 : Blo 952587 2413385 := bstep (se 2 (by rfl) ⟨905019, by rfl⟩ : syracuseStep 2413385 = 1810039) B1810039
theorem B1430447 : Blo 952587 1430447 := bstep (se 1 (by rfl) ⟨1072835, by rfl⟩ : syracuseStep 1430447 = 2145671) B2145671
theorem B3625985 : Blo 952587 3625985 := bstep (se 2 (by rfl) ⟨1359744, by rfl⟩ : syracuseStep 3625985 = 2719489) B2719489
theorem B2151431 : Blo 952587 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B1430537 : Blo 952587 1430537 := bstep (se 2 (by rfl) ⟨536451, by rfl⟩ : syracuseStep 1430537 = 1072903) B1072903
theorem B1430567 : Blo 952587 1430567 := bstep (se 1 (by rfl) ⟨1072925, by rfl⟩ : syracuseStep 1430567 = 2145851) B2145851
theorem B4346959 : Blo 952587 4346959 := bstep (se 1 (by rfl) ⟨3260219, by rfl⟩ : syracuseStep 4346959 = 6520439) B6520439
theorem B2151503 : Blo 952587 2151503 := bstep (se 1 (by rfl) ⟨1613627, by rfl⟩ : syracuseStep 2151503 = 3227255) B3227255
theorem B6116471 : Blo 952587 6116471 := bstep (se 1 (by rfl) ⟨4587353, by rfl⟩ : syracuseStep 6116471 = 9174707) B9174707
theorem B1430651 : Blo 952587 1430651 := bstep (se 1 (by rfl) ⟨1072988, by rfl⟩ : syracuseStep 1430651 = 2145977) B2145977
theorem B6870187 : Blo 952587 6870187 := bstep (se 1 (by rfl) ⟨5152640, by rfl⟩ : syracuseStep 6870187 = 10305281) B10305281
theorem B2413739 : Blo 952587 2413739 := bstep (se 1 (by rfl) ⟨1810304, by rfl⟩ : syracuseStep 2413739 = 3620609) B3620609
theorem B1430777 : Blo 952587 1430777 := bstep (se 2 (by rfl) ⟨536541, by rfl⟩ : syracuseStep 1430777 = 1073083) B1073083
theorem B1430879 : Blo 952587 1430879 := bstep (se 1 (by rfl) ⟨1073159, by rfl⟩ : syracuseStep 1430879 = 2146319) B2146319
theorem B1430891 : Blo 952587 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B3626441 : Blo 952587 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B2151899 : Blo 952587 2151899 := bstep (se 1 (by rfl) ⟨1613924, by rfl⟩ : syracuseStep 2151899 = 3227849) B3227849
theorem B7263755 : Blo 952587 7263755 := bstep (se 1 (by rfl) ⟨5447816, by rfl⟩ : syracuseStep 7263755 = 10895633) B10895633
theorem B6116903 : Blo 952587 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B1431119 : Blo 952587 1431119 := bstep (se 1 (by rfl) ⟨1073339, by rfl⟩ : syracuseStep 1431119 = 2146679) B2146679
theorem B4839101 : Blo 952587 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B4085437 : Blo 952587 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B1431239 : Blo 952587 1431239 := bstep (se 1 (by rfl) ⟨1073429, by rfl⟩ : syracuseStep 1431239 = 2146859) B2146859
theorem B4839263 : Blo 952587 4839263 := bstep (se 1 (by rfl) ⟨3629447, by rfl⟩ : syracuseStep 4839263 = 7258895) B7258895
theorem B1431401 : Blo 952587 1431401 := bstep (se 2 (by rfl) ⟨536775, by rfl⟩ : syracuseStep 1431401 = 1073551) B1073551
theorem B3626927 : Blo 952587 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B2414519 : Blo 952587 2414519 := bstep (se 1 (by rfl) ⟨1810889, by rfl⟩ : syracuseStep 2414519 = 3621779) B3621779
theorem B1431479 : Blo 952587 1431479 := bstep (se 1 (by rfl) ⟨1073609, by rfl⟩ : syracuseStep 1431479 = 2147219) B2147219
theorem B1431515 : Blo 952587 1431515 := bstep (se 1 (by rfl) ⟨1073636, by rfl⟩ : syracuseStep 1431515 = 2147273) B2147273
theorem B11032937 : Blo 952587 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B1431983 : Blo 952587 1431983 := bstep (se 1 (by rfl) ⟨1073987, by rfl⟩ : syracuseStep 1431983 = 2147975) B2147975
theorem B1432073 : Blo 952587 1432073 := bstep (se 2 (by rfl) ⟨537027, by rfl⟩ : syracuseStep 1432073 = 1074055) B1074055
theorem B2578969 : Blo 952587 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B7363105 : Blo 952587 7363105 := bstep (se 2 (by rfl) ⟨2761164, by rfl⟩ : syracuseStep 7363105 = 5522329) B5522329
theorem B1432103 : Blo 952587 1432103 := bstep (se 1 (by rfl) ⟨1074077, by rfl⟩ : syracuseStep 1432103 = 2148155) B2148155
theorem B1432187 : Blo 952587 1432187 := bstep (se 1 (by rfl) ⟨1074140, by rfl⟩ : syracuseStep 1432187 = 2148281) B2148281
theorem B1432313 : Blo 952587 1432313 := bstep (se 2 (by rfl) ⟨537117, by rfl⟩ : syracuseStep 1432313 = 1074235) B1074235
theorem B1071967 : Blo 952587 1071967 := bstep (se 1 (by rfl) ⟨803975, by rfl⟩ : syracuseStep 1071967 = 1607951) B1607951
theorem B1432415 : Blo 952587 1432415 := bstep (se 1 (by rfl) ⟨1074311, by rfl⟩ : syracuseStep 1432415 = 2148623) B2148623
theorem B1432427 : Blo 952587 1432427 := bstep (se 1 (by rfl) ⟨1074320, by rfl⟩ : syracuseStep 1432427 = 2148641) B2148641
theorem B2415521 : Blo 952587 2415521 := bstep (se 2 (by rfl) ⟨905820, by rfl⟩ : syracuseStep 2415521 = 1811641) B1811641
theorem B1432655 : Blo 952587 1432655 := bstep (se 1 (by rfl) ⟨1074491, by rfl⟩ : syracuseStep 1432655 = 2148983) B2148983
theorem B3628111 : Blo 952587 3628111 := bstep (se 1 (by rfl) ⟨2721083, by rfl⟩ : syracuseStep 3628111 = 5442167) B5442167
theorem B1072327 : Blo 952587 1072327 := bstep (se 1 (by rfl) ⟨804245, by rfl⟩ : syracuseStep 1072327 = 1608491) B1608491
theorem B1432775 : Blo 952587 1432775 := bstep (se 1 (by rfl) ⟨1074581, by rfl⟩ : syracuseStep 1432775 = 2149163) B2149163
theorem B2415977 : Blo 952587 2415977 := bstep (se 2 (by rfl) ⟨905991, by rfl⟩ : syracuseStep 2415977 = 1811983) B1811983
theorem B1432937 : Blo 952587 1432937 := bstep (se 2 (by rfl) ⟨537351, by rfl⟩ : syracuseStep 1432937 = 1074703) B1074703
theorem B4349309 : Blo 952587 4349309 := bstep (se 3 (by rfl) ⟨815495, by rfl⟩ : syracuseStep 4349309 = 1630991) B1630991
theorem B1433015 : Blo 952587 1433015 := bstep (se 1 (by rfl) ⟨1074761, by rfl⟩ : syracuseStep 1433015 = 2149523) B2149523
theorem B1433051 : Blo 952587 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B2580007 : Blo 952587 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B3628583 : Blo 952587 3628583 := bstep (se 1 (by rfl) ⟨2721437, by rfl⟩ : syracuseStep 3628583 = 5442875) B5442875
theorem B1433519 : Blo 952587 1433519 := bstep (se 1 (by rfl) ⟨1075139, by rfl⟩ : syracuseStep 1433519 = 2150279) B2150279
theorem B1433609 : Blo 952587 1433609 := bstep (se 2 (by rfl) ⟨537603, by rfl⟩ : syracuseStep 1433609 = 1075207) B1075207
theorem B1073191 : Blo 952587 1073191 := bstep (se 1 (by rfl) ⟨804893, by rfl⟩ : syracuseStep 1073191 = 1609787) B1609787
theorem B1433639 : Blo 952587 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B1531943 : Blo 952587 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B1433723 : Blo 952587 1433723 := bstep (se 1 (by rfl) ⟨1075292, by rfl⟩ : syracuseStep 1433723 = 2150585) B2150585
theorem B1433849 : Blo 952587 1433849 := bstep (se 2 (by rfl) ⟨537693, by rfl⟩ : syracuseStep 1433849 = 1075387) B1075387
theorem B1433951 : Blo 952587 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B1433963 : Blo 952587 1433963 := bstep (se 1 (by rfl) ⟨1075472, by rfl⟩ : syracuseStep 1433963 = 2150945) B2150945
theorem B3629555 : Blo 952587 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B2417161 : Blo 952587 2417161 := bstep (se 2 (by rfl) ⟨906435, by rfl⟩ : syracuseStep 2417161 = 1812871) B1812871
theorem B4842017 : Blo 952587 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B1434191 : Blo 952587 1434191 := bstep (se 1 (by rfl) ⟨1075643, by rfl⟩ : syracuseStep 1434191 = 2151287) B2151287
theorem B2450017 : Blo 952587 2450017 := bstep (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) B1837513
theorem B1434311 : Blo 952587 1434311 := bstep (se 1 (by rfl) ⟨1075733, by rfl⟩ : syracuseStep 1434311 = 2151467) B2151467
theorem B1434473 : Blo 952587 1434473 := bstep (se 2 (by rfl) ⟨537927, by rfl⟩ : syracuseStep 1434473 = 1075855) B1075855
theorem B1434551 : Blo 952587 1434551 := bstep (se 1 (by rfl) ⟨1075913, by rfl⟩ : syracuseStep 1434551 = 2151827) B2151827
theorem B1434587 : Blo 952587 1434587 := bstep (se 1 (by rfl) ⟨1075940, by rfl⟩ : syracuseStep 1434587 = 2151881) B2151881
theorem B1074811 : Blo 952587 1074811 := bstep (se 1 (by rfl) ⟨806108, by rfl⟩ : syracuseStep 1074811 = 1612217) B1612217
theorem B6973067 : Blo 952587 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B11626183 : Blo 952587 11626183 := bstep (se 1 (by rfl) ⟨8719637, by rfl⟩ : syracuseStep 11626183 = 17439275) B17439275
theorem B1206191 : Blo 952587 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B2418619 : Blo 952587 2418619 := bstep (se 1 (by rfl) ⟨1813964, by rfl⟩ : syracuseStep 2418619 = 3627929) B3627929
theorem B2713657 : Blo 952587 2713657 := bstep (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) B2035243
theorem B1075279 : Blo 952587 1075279 := bstep (se 1 (by rfl) ⟨806459, by rfl⟩ : syracuseStep 1075279 = 1612919) B1612919
theorem B2713999 : Blo 952587 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B1075675 : Blo 952587 1075675 := bstep (se 1 (by rfl) ⟨806756, by rfl⟩ : syracuseStep 1075675 = 1613513) B1613513
theorem B3435223 : Blo 952587 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B1076143 : Blo 952587 1076143 := bstep (se 1 (by rfl) ⟨807107, by rfl⟩ : syracuseStep 1076143 = 1614215) B1614215
theorem B9923627 : Blo 952587 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B4189819 : Blo 952587 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B2715275 : Blo 952587 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B5500715 : Blo 952587 5500715 := bstep (se 1 (by rfl) ⟨4125536, by rfl⟩ : syracuseStep 5500715 = 8251073) B8251073
theorem B7237511 : Blo 952587 7237511 := bstep (se 1 (by rfl) ⟨5428133, by rfl⟩ : syracuseStep 7237511 = 10856267) B10856267
theorem B2421211 : Blo 952587 2421211 := bstep (se 1 (by rfl) ⟨1815908, by rfl⟩ : syracuseStep 2421211 = 3631817) B3631817
theorem B5436335 : Blo 952587 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B2291399 : Blo 952587 2291399 := bstep (se 1 (by rfl) ⟨1718549, by rfl⟩ : syracuseStep 2291399 = 3437099) B3437099
theorem B1833529 : Blo 952587 1833529 := bstep (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) B1375147
theorem B2718305 : Blo 952587 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B16546481 : Blo 952587 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B3865519 : Blo 952587 3865519 := bstep (se 1 (by rfl) ⟨2899139, by rfl⟩ : syracuseStep 3865519 = 5798279) B5798279
theorem B2718647 : Blo 952587 2718647 := bstep (se 1 (by rfl) ⟨2038985, by rfl⟩ : syracuseStep 2718647 = 4077971) B4077971
theorem B1146055 : Blo 952587 1146055 := bstep (se 1 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 1146055 = 1719083) B1719083
theorem B3866251 : Blo 952587 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B7732883 : Blo 952587 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B7339709 : Blo 952587 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B1834859 : Blo 952587 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B12222323 : Blo 952587 12222323 := bstep (se 1 (by rfl) ⟨9166742, by rfl⟩ : syracuseStep 12222323 = 18333485) B18333485
theorem B2719649 : Blo 952587 2719649 := bstep (se 2 (by rfl) ⟨1019868, by rfl⟩ : syracuseStep 2719649 = 2039737) B2039737
theorem B1933999 : Blo 952587 1933999 := bstep (se 1 (by rfl) ⟨1450499, by rfl⟩ : syracuseStep 1933999 = 2900999) B2900999
theorem B1147727 : Blo 952587 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B6882209 : Blo 952587 6882209 := bstep (se 2 (by rfl) ⟨2580828, by rfl⟩ : syracuseStep 6882209 = 5161657) B5161657
theorem B2294983 : Blo 952587 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B27559277 : Blo 952587 27559277 := bstep (se 3 (by rfl) ⟨5167364, by rfl⟩ : syracuseStep 27559277 = 10334729) B10334729
theorem B5440891 : Blo 952587 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B24511895 : Blo 952587 24511895 := bstep (se 1 (by rfl) ⟨18383921, by rfl⟩ : syracuseStep 24511895 = 36767843) B36767843
theorem B33130133 : Blo 952587 33130133 := bstep (se 6 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 33130133 = 1552975) B1552975
theorem B13043663 : Blo 952587 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B10324097 : Blo 952587 10324097 := bstep (se 2 (by rfl) ⟨3871536, by rfl⟩ : syracuseStep 10324097 = 7743073) B7743073
theorem B15501577 : Blo 952587 15501577 := bstep (se 2 (by rfl) ⟨5813091, by rfl⟩ : syracuseStep 15501577 = 11626183) B11626183
theorem B952607 : Blo 952587 952607 := bstep (se 1 (by rfl) ⟨714455, by rfl⟩ : syracuseStep 952607 = 1428911) B1428911
theorem B952667 : Blo 952587 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B952687 : Blo 952587 952687 := bstep (se 1 (by rfl) ⟨714515, by rfl⟩ : syracuseStep 952687 = 1429031) B1429031
theorem B952743 : Blo 952587 952743 := bstep (se 1 (by rfl) ⟨714557, by rfl⟩ : syracuseStep 952743 = 1429115) B1429115
theorem B952827 : Blo 952587 952827 := bstep (se 1 (by rfl) ⟨714620, by rfl⟩ : syracuseStep 952827 = 1429241) B1429241
theorem B1608187 : Blo 952587 1608187 := bstep (se 1 (by rfl) ⟨1206140, by rfl⟩ : syracuseStep 1608187 = 2412281) B2412281
theorem B952895 : Blo 952587 952895 := bstep (se 1 (by rfl) ⟨714671, by rfl⟩ : syracuseStep 952895 = 1429343) B1429343
theorem B952903 : Blo 952587 952903 := bstep (se 1 (by rfl) ⟨714677, by rfl⟩ : syracuseStep 952903 = 1429355) B1429355
theorem B5311115 : Blo 952587 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B953055 : Blo 952587 953055 := bstep (se 1 (by rfl) ⟨714791, by rfl⟩ : syracuseStep 953055 = 1429583) B1429583
theorem B953135 : Blo 952587 953135 := bstep (se 1 (by rfl) ⟨714851, by rfl⟩ : syracuseStep 953135 = 1429703) B1429703
theorem B953243 : Blo 952587 953243 := bstep (se 1 (by rfl) ⟨714932, by rfl⟩ : syracuseStep 953243 = 1429865) B1429865
theorem B1608619 : Blo 952587 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B953295 : Blo 952587 953295 := bstep (se 1 (by rfl) ⟨714971, by rfl⟩ : syracuseStep 953295 = 1429943) B1429943
theorem B953319 : Blo 952587 953319 := bstep (se 1 (by rfl) ⟨714989, by rfl⟩ : syracuseStep 953319 = 1429979) B1429979
theorem B1608923 : Blo 952587 1608923 := bstep (se 1 (by rfl) ⟨1206692, by rfl⟩ : syracuseStep 1608923 = 2413385) B2413385
theorem B953631 : Blo 952587 953631 := bstep (se 1 (by rfl) ⟨715223, by rfl⟩ : syracuseStep 953631 = 1430447) B1430447
theorem B9178429 : Blo 952587 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B953691 : Blo 952587 953691 := bstep (se 1 (by rfl) ⟨715268, by rfl⟩ : syracuseStep 953691 = 1430537) B1430537
theorem B953711 : Blo 952587 953711 := bstep (se 1 (by rfl) ⟨715283, by rfl⟩ : syracuseStep 953711 = 1430567) B1430567
theorem B953767 : Blo 952587 953767 := bstep (se 1 (by rfl) ⟨715325, by rfl⟩ : syracuseStep 953767 = 1430651) B1430651
theorem B1609159 : Blo 952587 1609159 := bstep (se 1 (by rfl) ⟨1206869, by rfl⟩ : syracuseStep 1609159 = 2413739) B2413739
theorem B953851 : Blo 952587 953851 := bstep (se 1 (by rfl) ⟨715388, by rfl⟩ : syracuseStep 953851 = 1430777) B1430777
theorem B953919 : Blo 952587 953919 := bstep (se 1 (by rfl) ⟨715439, by rfl⟩ : syracuseStep 953919 = 1430879) B1430879
theorem B953927 : Blo 952587 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B954079 : Blo 952587 954079 := bstep (se 1 (by rfl) ⟨715559, by rfl⟩ : syracuseStep 954079 = 1431119) B1431119
theorem B5443307 : Blo 952587 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B954159 : Blo 952587 954159 := bstep (se 1 (by rfl) ⟨715619, by rfl⟩ : syracuseStep 954159 = 1431239) B1431239
theorem B954267 : Blo 952587 954267 := bstep (se 1 (by rfl) ⟨715700, by rfl⟩ : syracuseStep 954267 = 1431401) B1431401
theorem B1609679 : Blo 952587 1609679 := bstep (se 1 (by rfl) ⟨1207259, by rfl⟩ : syracuseStep 1609679 = 2414519) B2414519
theorem B954319 : Blo 952587 954319 := bstep (se 1 (by rfl) ⟨715739, by rfl⟩ : syracuseStep 954319 = 1431479) B1431479
theorem B954343 : Blo 952587 954343 := bstep (se 1 (by rfl) ⟨715757, by rfl⟩ : syracuseStep 954343 = 1431515) B1431515
theorem B4591675 : Blo 952587 4591675 := bstep (se 1 (by rfl) ⟨3443756, by rfl⟩ : syracuseStep 4591675 = 6887513) B6887513
theorem B954655 : Blo 952587 954655 := bstep (se 1 (by rfl) ⟨715991, by rfl⟩ : syracuseStep 954655 = 1431983) B1431983
theorem B954715 : Blo 952587 954715 := bstep (se 1 (by rfl) ⟨716036, by rfl⟩ : syracuseStep 954715 = 1432073) B1432073
theorem B954735 : Blo 952587 954735 := bstep (se 1 (by rfl) ⟨716051, by rfl⟩ : syracuseStep 954735 = 1432103) B1432103
theorem B9179507 : Blo 952587 9179507 := bstep (se 1 (by rfl) ⟨6884630, by rfl⟩ : syracuseStep 9179507 = 13769261) B13769261
theorem B954791 : Blo 952587 954791 := bstep (se 1 (by rfl) ⟨716093, by rfl⟩ : syracuseStep 954791 = 1432187) B1432187
theorem B954875 : Blo 952587 954875 := bstep (se 1 (by rfl) ⟨716156, by rfl⟩ : syracuseStep 954875 = 1432313) B1432313
theorem B954943 : Blo 952587 954943 := bstep (se 1 (by rfl) ⟨716207, by rfl⟩ : syracuseStep 954943 = 1432415) B1432415
theorem B954951 : Blo 952587 954951 := bstep (se 1 (by rfl) ⟨716213, by rfl⟩ : syracuseStep 954951 = 1432427) B1432427
theorem B1610347 : Blo 952587 1610347 := bstep (se 1 (by rfl) ⟨1207760, by rfl⟩ : syracuseStep 1610347 = 2415521) B2415521
theorem B955103 : Blo 952587 955103 := bstep (se 1 (by rfl) ⟨716327, by rfl⟩ : syracuseStep 955103 = 1432655) B1432655
theorem B955183 : Blo 952587 955183 := bstep (se 1 (by rfl) ⟨716387, by rfl⟩ : syracuseStep 955183 = 1432775) B1432775
theorem B3871567 : Blo 952587 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B1610651 : Blo 952587 1610651 := bstep (se 1 (by rfl) ⟨1207988, by rfl⟩ : syracuseStep 1610651 = 2415977) B2415977
theorem B955291 : Blo 952587 955291 := bstep (se 1 (by rfl) ⟨716468, by rfl⟩ : syracuseStep 955291 = 1432937) B1432937
theorem B955343 : Blo 952587 955343 := bstep (se 1 (by rfl) ⟨716507, by rfl⟩ : syracuseStep 955343 = 1433015) B1433015
theorem B3216347 : Blo 952587 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B955367 : Blo 952587 955367 := bstep (se 1 (by rfl) ⟨716525, by rfl⟩ : syracuseStep 955367 = 1433051) B1433051
theorem B3216509 : Blo 952587 3216509 := bstep (se 3 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 3216509 = 1206191) B1206191
theorem B5444765 : Blo 952587 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B3216617 : Blo 952587 3216617 := bstep (se 2 (by rfl) ⟨1206231, by rfl⟩ : syracuseStep 3216617 = 2412463) B2412463
theorem B955679 : Blo 952587 955679 := bstep (se 1 (by rfl) ⟨716759, by rfl⟩ : syracuseStep 955679 = 1433519) B1433519
theorem B955739 : Blo 952587 955739 := bstep (se 1 (by rfl) ⟨716804, by rfl⟩ : syracuseStep 955739 = 1433609) B1433609
theorem B2037089 : Blo 952587 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B955759 : Blo 952587 955759 := bstep (se 1 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 955759 = 1433639) B1433639
theorem B1021295 : Blo 952587 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B3216779 : Blo 952587 3216779 := bstep (se 1 (by rfl) ⟨2412584, by rfl⟩ : syracuseStep 3216779 = 4825169) B4825169
theorem B6886795 : Blo 952587 6886795 := bstep (se 1 (by rfl) ⟨5165096, by rfl⟩ : syracuseStep 6886795 = 10330193) B10330193
theorem B955815 : Blo 952587 955815 := bstep (se 1 (by rfl) ⟨716861, by rfl⟩ : syracuseStep 955815 = 1433723) B1433723
theorem B13047277 : Blo 952587 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B955899 : Blo 952587 955899 := bstep (se 1 (by rfl) ⟨716924, by rfl⟩ : syracuseStep 955899 = 1433849) B1433849
theorem B955967 : Blo 952587 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B955975 : Blo 952587 955975 := bstep (se 1 (by rfl) ⟨716981, by rfl⟩ : syracuseStep 955975 = 1433963) B1433963
theorem B956127 : Blo 952587 956127 := bstep (se 1 (by rfl) ⟨717095, by rfl⟩ : syracuseStep 956127 = 1434191) B1434191
theorem B956207 : Blo 952587 956207 := bstep (se 1 (by rfl) ⟨717155, by rfl⟩ : syracuseStep 956207 = 1434311) B1434311
theorem B956315 : Blo 952587 956315 := bstep (se 1 (by rfl) ⟨717236, by rfl⟩ : syracuseStep 956315 = 1434473) B1434473
theorem B956367 : Blo 952587 956367 := bstep (se 1 (by rfl) ⟨717275, by rfl⟩ : syracuseStep 956367 = 1434551) B1434551
theorem B956391 : Blo 952587 956391 := bstep (se 1 (by rfl) ⟨717293, by rfl⟩ : syracuseStep 956391 = 1434587) B1434587
theorem B4823225 : Blo 952587 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B9182429 : Blo 952587 9182429 := bstep (se 3 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 9182429 = 3443411) B3443411
theorem B8723875 : Blo 952587 8723875 := bstep (se 1 (by rfl) ⟨6542906, by rfl⟩ : syracuseStep 8723875 = 13085813) B13085813
theorem B5447249 : Blo 952587 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B1810183 : Blo 952587 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B4825007 : Blo 952587 4825007 := bstep (se 1 (by rfl) ⟨3618755, by rfl⟩ : syracuseStep 4825007 = 7237511) B7237511
theorem B20652083 : Blo 952587 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B3219803 : Blo 952587 3219803 := bstep (se 1 (by rfl) ⟨2414852, by rfl⟩ : syracuseStep 3219803 = 4829705) B4829705
theorem B10854809 : Blo 952587 10854809 := bstep (se 2 (by rfl) ⟨4070553, by rfl⟩ : syracuseStep 10854809 = 8141107) B8141107
theorem B5154025 : Blo 952587 5154025 := bstep (se 2 (by rfl) ⟨1932759, by rfl⟩ : syracuseStep 5154025 = 3865519) B3865519
theorem B3220775 : Blo 952587 3220775 := bstep (se 1 (by rfl) ⟨2415581, by rfl⟩ : syracuseStep 3220775 = 4831163) B4831163
theorem B5514809 : Blo 952587 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B1812203 : Blo 952587 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B1812431 : Blo 952587 1812431 := bstep (se 1 (by rfl) ⟨1359323, by rfl⟩ : syracuseStep 1812431 = 2718647) B2718647
theorem B16984151 : Blo 952587 16984151 := bstep (se 1 (by rfl) ⟨12738113, by rfl⟩ : syracuseStep 16984151 = 25476227) B25476227
theorem B3221639 : Blo 952587 3221639 := bstep (se 1 (by rfl) ⟨2416229, by rfl⟩ : syracuseStep 3221639 = 4832459) B4832459
theorem B9316529 : Blo 952587 9316529 := bstep (se 2 (by rfl) ⟨3493698, by rfl⟩ : syracuseStep 9316529 = 6987397) B6987397
theorem B5155001 : Blo 952587 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B8726723 : Blo 952587 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B4892957 : Blo 952587 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B5155255 : Blo 952587 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B4893139 : Blo 952587 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B4073971 : Blo 952587 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B1813099 : Blo 952587 1813099 := bstep (se 1 (by rfl) ⟨1359824, by rfl⟩ : syracuseStep 1813099 = 2719649) B2719649
theorem B1813175 : Blo 952587 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B4827923 : Blo 952587 4827923 := bstep (se 1 (by rfl) ⟨3620942, by rfl⟩ : syracuseStep 4827923 = 7241885) B7241885
theorem B1813403 : Blo 952587 1813403 := bstep (se 1 (by rfl) ⟨1360052, by rfl⟩ : syracuseStep 1813403 = 2720105) B2720105
theorem B2042795 : Blo 952587 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B3222881 : Blo 952587 3222881 := bstep (se 2 (by rfl) ⟨1208580, by rfl⟩ : syracuseStep 3222881 = 2417161) B2417161
theorem B1814177 : Blo 952587 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B4075271 : Blo 952587 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B1814329 : Blo 952587 1814329 := bstep (se 2 (by rfl) ⟨680373, by rfl⟩ : syracuseStep 1814329 = 1360747) B1360747
theorem B4829057 : Blo 952587 4829057 := bstep (se 2 (by rfl) ⟨1810896, by rfl⟩ : syracuseStep 4829057 = 3621793) B3621793
theorem B23179193 : Blo 952587 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B8138717 : Blo 952587 8138717 := bstep (se 3 (by rfl) ⟨1526009, by rfl⟩ : syracuseStep 8138717 = 3052019) B3052019
theorem B11907161 : Blo 952587 11907161 := bstep (se 2 (by rfl) ⟨4465185, by rfl⟩ : syracuseStep 11907161 = 8930371) B8930371
theorem B1814633 : Blo 952587 1814633 := bstep (se 2 (by rfl) ⟨680487, by rfl⟩ : syracuseStep 1814633 = 1360975) B1360975
theorem B4829867 : Blo 952587 4829867 := bstep (se 1 (by rfl) ⟨3622400, by rfl⟩ : syracuseStep 4829867 = 7244801) B7244801
theorem B1716919 : Blo 952587 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B1291063 : Blo 952587 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B32257091 : Blo 952587 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B4830353 : Blo 952587 4830353 := bstep (se 2 (by rfl) ⟨1811382, by rfl⟩ : syracuseStep 4830353 = 3622765) B3622765
theorem B3224825 : Blo 952587 3224825 := bstep (se 2 (by rfl) ⟨1209309, by rfl⟩ : syracuseStep 3224825 = 2418619) B2418619
theorem B2143583 : Blo 952587 2143583 := bstep (se 1 (by rfl) ⟨1607687, by rfl⟩ : syracuseStep 2143583 = 3215375) B3215375
theorem B1717627 : Blo 952587 1717627 := bstep (se 1 (by rfl) ⟨1288220, by rfl⟩ : syracuseStep 1717627 = 2576441) B2576441
theorem B1357193 : Blo 952587 1357193 := bstep (se 2 (by rfl) ⟨508947, by rfl⟩ : syracuseStep 1357193 = 1017895) B1017895
theorem B3618209 : Blo 952587 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B41268689 : Blo 952587 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B39269893 : Blo 952587 39269893 := bstep (se 4 (by rfl) ⟨3681552, by rfl⟩ : syracuseStep 39269893 = 7363105) B7363105
theorem B3225095 : Blo 952587 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B2143979 : Blo 952587 2143979 := bstep (se 1 (by rfl) ⟨1607984, by rfl⟩ : syracuseStep 2143979 = 3215969) B3215969
theorem B5519191 : Blo 952587 5519191 := bstep (se 1 (by rfl) ⟨4139393, by rfl⟩ : syracuseStep 5519191 = 8278787) B8278787
theorem B16562015 : Blo 952587 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B2144105 : Blo 952587 2144105 := bstep (se 2 (by rfl) ⟨804039, by rfl⟩ : syracuseStep 2144105 = 1608079) B1608079
theorem B3618665 : Blo 952587 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B4077647 : Blo 952587 4077647 := bstep (se 1 (by rfl) ⟨3058235, by rfl⟩ : syracuseStep 4077647 = 6116471) B6116471
theorem B4077935 : Blo 952587 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B3226067 : Blo 952587 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B3226175 : Blo 952587 3226175 := bstep (se 1 (by rfl) ⟨2419631, by rfl⟩ : syracuseStep 3226175 = 4839263) B4839263
theorem B2144951 : Blo 952587 2144951 := bstep (se 1 (by rfl) ⟨1608713, by rfl⟩ : syracuseStep 2144951 = 3217427) B3217427
theorem B7256951 : Blo 952587 7256951 := bstep (se 1 (by rfl) ⟨5442713, by rfl⟩ : syracuseStep 7256951 = 10885427) B10885427
theorem B2145167 : Blo 952587 2145167 := bstep (se 1 (by rfl) ⟨1608875, by rfl⟩ : syracuseStep 2145167 = 3217751) B3217751
theorem B7355291 : Blo 952587 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B18594845 : Blo 952587 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B5586425 : Blo 952587 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B4832783 : Blo 952587 4832783 := bstep (se 1 (by rfl) ⟨3624587, by rfl⟩ : syracuseStep 4832783 = 7249175) B7249175
theorem B2145887 : Blo 952587 2145887 := bstep (se 1 (by rfl) ⟨1609415, by rfl⟩ : syracuseStep 2145887 = 3218831) B3218831
theorem B2146103 : Blo 952587 2146103 := bstep (se 1 (by rfl) ⟨1609577, by rfl⟩ : syracuseStep 2146103 = 3219155) B3219155
theorem B16301897 : Blo 952587 16301897 := bstep (se 2 (by rfl) ⟨6113211, by rfl⟩ : syracuseStep 16301897 = 12226423) B12226423
theorem B35307377 : Blo 952587 35307377 := bstep (se 2 (by rfl) ⟨13240266, by rfl⟩ : syracuseStep 35307377 = 26480533) B26480533
theorem B2146409 : Blo 952587 2146409 := bstep (se 2 (by rfl) ⟨804903, by rfl⟩ : syracuseStep 2146409 = 1609807) B1609807
theorem B19579117 : Blo 952587 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B3228011 : Blo 952587 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B4833755 : Blo 952587 4833755 := bstep (se 1 (by rfl) ⟨3625316, by rfl⟩ : syracuseStep 4833755 = 7250633) B7250633
theorem B3064321 : Blo 952587 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B2146895 : Blo 952587 2146895 := bstep (se 1 (by rfl) ⟨1610171, by rfl⟩ : syracuseStep 2146895 = 3220343) B3220343
theorem B3228281 : Blo 952587 3228281 := bstep (se 2 (by rfl) ⟨1210605, by rfl⟩ : syracuseStep 3228281 = 2421211) B2421211
theorem B2147039 : Blo 952587 2147039 := bstep (se 1 (by rfl) ⟨1610279, by rfl⟩ : syracuseStep 2147039 = 3220559) B3220559
theorem B4834241 : Blo 952587 4834241 := bstep (se 2 (by rfl) ⟨1812840, by rfl⟩ : syracuseStep 4834241 = 3625681) B3625681
theorem B2147291 : Blo 952587 2147291 := bstep (se 1 (by rfl) ⟨1610468, by rfl⟩ : syracuseStep 2147291 = 3220937) B3220937
theorem B2147471 : Blo 952587 2147471 := bstep (se 1 (by rfl) ⟨1610603, by rfl⟩ : syracuseStep 2147471 = 3221207) B3221207
theorem B2147561 : Blo 952587 2147561 := bstep (se 2 (by rfl) ⟨805335, by rfl⟩ : syracuseStep 2147561 = 1610671) B1610671
theorem B2147615 : Blo 952587 2147615 := bstep (se 1 (by rfl) ⟨1610711, by rfl⟩ : syracuseStep 2147615 = 3221423) B3221423
theorem B3261791 : Blo 952587 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B37242389 : Blo 952587 37242389 := bstep (se 6 (by rfl) ⟨872868, by rfl⟩ : syracuseStep 37242389 = 1745737) B1745737
theorem B9160249 : Blo 952587 9160249 := bstep (se 2 (by rfl) ⟨3435093, by rfl⟩ : syracuseStep 9160249 = 6870187) B6870187
theorem B4081337 : Blo 952587 4081337 := bstep (se 2 (by rfl) ⟨1530501, by rfl⟩ : syracuseStep 4081337 = 3061003) B3061003
theorem B1492715 : Blo 952587 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B2148137 : Blo 952587 2148137 := bstep (se 2 (by rfl) ⟨805551, by rfl⟩ : syracuseStep 2148137 = 1611103) B1611103
theorem B6211565 : Blo 952587 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B5163041 : Blo 952587 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B7260353 : Blo 952587 7260353 := bstep (se 2 (by rfl) ⟨2722632, by rfl⟩ : syracuseStep 7260353 = 5445265) B5445265
theorem B2149199 : Blo 952587 2149199 := bstep (se 1 (by rfl) ⟨1611899, by rfl⟩ : syracuseStep 2149199 = 3223799) B3223799
theorem B2149415 : Blo 952587 2149415 := bstep (se 1 (by rfl) ⟨1612061, by rfl⟩ : syracuseStep 2149415 = 3224123) B3224123
theorem B2149595 : Blo 952587 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B3624223 : Blo 952587 3624223 := bstep (se 1 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 3624223 = 5436335) B5436335
theorem B2411815 : Blo 952587 2411815 := bstep (se 1 (by rfl) ⟨1808861, by rfl⟩ : syracuseStep 2411815 = 3617723) B3617723
theorem B2444705 : Blo 952587 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B2149793 : Blo 952587 2149793 := bstep (se 2 (by rfl) ⟨806172, by rfl⟩ : syracuseStep 2149793 = 1612345) B1612345
theorem B1428935 : Blo 952587 1428935 := bstep (se 1 (by rfl) ⟨1071701, by rfl⟩ : syracuseStep 1428935 = 2143403) B2143403
theorem B2412089 : Blo 952587 2412089 := bstep (se 2 (by rfl) ⟨904533, by rfl⟩ : syracuseStep 2412089 = 1809067) B1809067
theorem B1429289 : Blo 952587 1429289 := bstep (se 2 (by rfl) ⟨535983, by rfl⟩ : syracuseStep 1429289 = 1071967) B1071967
theorem B1429295 : Blo 952587 1429295 := bstep (se 1 (by rfl) ⟨1071971, by rfl⟩ : syracuseStep 1429295 = 2143943) B2143943
theorem B1527599 : Blo 952587 1527599 := bstep (se 1 (by rfl) ⟨1145699, by rfl⟩ : syracuseStep 1527599 = 2291399) B2291399
theorem B2150351 : Blo 952587 2150351 := bstep (se 1 (by rfl) ⟨1612763, by rfl⟩ : syracuseStep 2150351 = 3225527) B3225527
theorem B4837481 : Blo 952587 4837481 := bstep (se 2 (by rfl) ⟨1814055, by rfl⟩ : syracuseStep 4837481 = 3628111) B3628111
theorem B1429769 : Blo 952587 1429769 := bstep (se 2 (by rfl) ⟨536163, by rfl⟩ : syracuseStep 1429769 = 1072327) B1072327
theorem B1528073 : Blo 952587 1528073 := bstep (se 2 (by rfl) ⟨573027, by rfl⟩ : syracuseStep 1528073 = 1146055) B1146055
theorem B2150729 : Blo 952587 2150729 := bstep (se 2 (by rfl) ⟨806523, by rfl⟩ : syracuseStep 2150729 = 1613047) B1613047
theorem B2150747 : Blo 952587 2150747 := bstep (se 1 (by rfl) ⟨1613060, by rfl⟩ : syracuseStep 2150747 = 3226121) B3226121
theorem B1429871 : Blo 952587 1429871 := bstep (se 1 (by rfl) ⟨1072403, by rfl⟩ : syracuseStep 1429871 = 2144807) B2144807
theorem B11030987 : Blo 952587 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B1430087 : Blo 952587 1430087 := bstep (se 1 (by rfl) ⟨1072565, by rfl⟩ : syracuseStep 1430087 = 2145131) B2145131
theorem B1430123 : Blo 952587 1430123 := bstep (se 1 (by rfl) ⟨1072592, by rfl⟩ : syracuseStep 1430123 = 2145185) B2145185
theorem B14668573 : Blo 952587 14668573 := bstep (se 3 (by rfl) ⟨2750357, by rfl⟩ : syracuseStep 14668573 = 5500715) B5500715
theorem B1430351 : Blo 952587 1430351 := bstep (se 1 (by rfl) ⟨1072763, by rfl⟩ : syracuseStep 1430351 = 2145527) B2145527
theorem B2151323 : Blo 952587 2151323 := bstep (se 1 (by rfl) ⟨1613492, by rfl⟩ : syracuseStep 2151323 = 3226985) B3226985
theorem B2151521 : Blo 952587 2151521 := bstep (se 2 (by rfl) ⟨806820, by rfl⟩ : syracuseStep 2151521 = 1613641) B1613641
theorem B4838615 : Blo 952587 4838615 := bstep (se 1 (by rfl) ⟨3628961, by rfl⟩ : syracuseStep 4838615 = 7257923) B7257923
theorem B1430747 : Blo 952587 1430747 := bstep (se 1 (by rfl) ⟨1073060, by rfl⟩ : syracuseStep 1430747 = 2146121) B2146121
theorem B8148215 : Blo 952587 8148215 := bstep (se 1 (by rfl) ⟨6111161, by rfl⟩ : syracuseStep 8148215 = 12222323) B12222323
theorem B69784847 : Blo 952587 69784847 := bstep (se 1 (by rfl) ⟨52338635, by rfl⟩ : syracuseStep 69784847 = 104677271) B104677271
theorem B2151719 : Blo 952587 2151719 := bstep (se 1 (by rfl) ⟨1613789, by rfl⟩ : syracuseStep 2151719 = 3227579) B3227579
theorem B2413921 : Blo 952587 2413921 := bstep (se 2 (by rfl) ⟨905220, by rfl⟩ : syracuseStep 2413921 = 1810441) B1810441
theorem B1430921 : Blo 952587 1430921 := bstep (se 2 (by rfl) ⟨536595, by rfl⟩ : syracuseStep 1430921 = 1073191) B1073191
theorem B2446807 : Blo 952587 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B3626653 : Blo 952587 3626653 := bstep (se 3 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 3626653 = 1359995) B1359995
theorem B2152097 : Blo 952587 2152097 := bstep (se 2 (by rfl) ⟨807036, by rfl⟩ : syracuseStep 2152097 = 1614073) B1614073
theorem B59463353 : Blo 952587 59463353 := bstep (se 2 (by rfl) ⟨22298757, by rfl⟩ : syracuseStep 59463353 = 44597515) B44597515
theorem B1431275 : Blo 952587 1431275 := bstep (se 1 (by rfl) ⟨1073456, by rfl⟩ : syracuseStep 1431275 = 2146913) B2146913
theorem B1529579 : Blo 952587 1529579 := bstep (se 1 (by rfl) ⟨1147184, by rfl⟩ : syracuseStep 1529579 = 2294369) B2294369
theorem B1431503 : Blo 952587 1431503 := bstep (se 1 (by rfl) ⟨1073627, by rfl⟩ : syracuseStep 1431503 = 2147255) B2147255
theorem B4085711 : Blo 952587 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B2414873 : Blo 952587 2414873 := bstep (se 2 (by rfl) ⟨905577, by rfl⟩ : syracuseStep 2414873 = 1811155) B1811155
theorem B1431899 : Blo 952587 1431899 := bstep (se 1 (by rfl) ⟨1073924, by rfl⟩ : syracuseStep 1431899 = 2147849) B2147849
theorem B1071679 : Blo 952587 1071679 := bstep (se 1 (by rfl) ⟨803759, by rfl⟩ : syracuseStep 1071679 = 1607519) B1607519
theorem B2415167 : Blo 952587 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B1432127 : Blo 952587 1432127 := bstep (se 1 (by rfl) ⟨1074095, by rfl⟩ : syracuseStep 1432127 = 2148191) B2148191
theorem B1530431 : Blo 952587 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B1432247 : Blo 952587 1432247 := bstep (se 1 (by rfl) ⟨1074185, by rfl⟩ : syracuseStep 1432247 = 2148371) B2148371
theorem B8706797 : Blo 952587 8706797 := bstep (se 3 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 8706797 = 3265049) B3265049
theorem B2415379 : Blo 952587 2415379 := bstep (se 1 (by rfl) ⟨1811534, by rfl⟩ : syracuseStep 2415379 = 3623069) B3623069
theorem B4643651 : Blo 952587 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B12245903 : Blo 952587 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B1432475 : Blo 952587 1432475 := bstep (se 1 (by rfl) ⟨1074356, by rfl⟩ : syracuseStep 1432475 = 2148713) B2148713
theorem B2415815 : Blo 952587 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B2415865 : Blo 952587 2415865 := bstep (se 2 (by rfl) ⟨905949, by rfl⟩ : syracuseStep 2415865 = 1811899) B1811899
theorem B1432871 : Blo 952587 1432871 := bstep (se 1 (by rfl) ⟨1074653, by rfl⟩ : syracuseStep 1432871 = 2149307) B2149307
theorem B11754827 : Blo 952587 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B3628385 : Blo 952587 3628385 := bstep (se 2 (by rfl) ⟨1360644, by rfl⟩ : syracuseStep 3628385 = 2721289) B2721289
theorem B1072507 : Blo 952587 1072507 := bstep (se 1 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 1072507 = 1608761) B1608761
theorem B1432955 : Blo 952587 1432955 := bstep (se 1 (by rfl) ⟨1074716, by rfl⟩ : syracuseStep 1432955 = 2149433) B2149433
theorem B1433081 : Blo 952587 1433081 := bstep (se 2 (by rfl) ⟨537405, by rfl⟩ : syracuseStep 1433081 = 1074811) B1074811
theorem B1433183 : Blo 952587 1433183 := bstep (se 1 (by rfl) ⟨1074887, by rfl⟩ : syracuseStep 1433183 = 2149775) B2149775
theorem B4349675 : Blo 952587 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B1433399 : Blo 952587 1433399 := bstep (se 1 (by rfl) ⟨1075049, by rfl⟩ : syracuseStep 1433399 = 2150099) B2150099
theorem B1072975 : Blo 952587 1072975 := bstep (se 1 (by rfl) ⟨804731, by rfl⟩ : syracuseStep 1072975 = 1609463) B1609463
theorem B2580353 : Blo 952587 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B2416513 : Blo 952587 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B4841531 : Blo 952587 4841531 := bstep (se 1 (by rfl) ⟨3631148, by rfl⟩ : syracuseStep 4841531 = 7262297) B7262297
theorem B1433705 : Blo 952587 1433705 := bstep (se 2 (by rfl) ⟨537639, by rfl⟩ : syracuseStep 1433705 = 1075279) B1075279
theorem B1073371 : Blo 952587 1073371 := bstep (se 1 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 1073371 = 1610057) B1610057
theorem B5431643 : Blo 952587 5431643 := bstep (se 1 (by rfl) ⟨4073732, by rfl⟩ : syracuseStep 5431643 = 8147465) B8147465
theorem B1434023 : Blo 952587 1434023 := bstep (se 1 (by rfl) ⟨1075517, by rfl⟩ : syracuseStep 1434023 = 2151035) B2151035
theorem B1073659 : Blo 952587 1073659 := bstep (se 1 (by rfl) ⟨805244, by rfl⟩ : syracuseStep 1073659 = 1610489) B1610489
theorem B1434107 : Blo 952587 1434107 := bstep (se 1 (by rfl) ⟨1075580, by rfl⟩ : syracuseStep 1434107 = 2151161) B2151161
theorem B3629569 : Blo 952587 3629569 := bstep (se 2 (by rfl) ⟨1361088, by rfl⟩ : syracuseStep 3629569 = 2722177) B2722177
theorem B13066757 : Blo 952587 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B2417273 : Blo 952587 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B1434233 : Blo 952587 1434233 := bstep (se 2 (by rfl) ⟨537837, by rfl⟩ : syracuseStep 1434233 = 1075675) B1075675
theorem B2417323 : Blo 952587 2417323 := bstep (se 1 (by rfl) ⟨1812992, by rfl⟩ : syracuseStep 2417323 = 3625985) B3625985
theorem B1073839 : Blo 952587 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B1434287 : Blo 952587 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B1434335 : Blo 952587 1434335 := bstep (se 1 (by rfl) ⟨1075751, by rfl⟩ : syracuseStep 1434335 = 2151503) B2151503
theorem B4580297 : Blo 952587 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B1074127 : Blo 952587 1074127 := bstep (se 1 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 1074127 = 1611191) B1611191
theorem B2417627 : Blo 952587 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B3630055 : Blo 952587 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B1434599 : Blo 952587 1434599 := bstep (se 1 (by rfl) ⟨1075949, by rfl⟩ : syracuseStep 1434599 = 2151899) B2151899
theorem B4842503 : Blo 952587 4842503 := bstep (se 1 (by rfl) ⟨3631877, by rfl⟩ : syracuseStep 4842503 = 7263755) B7263755
theorem B5432417 : Blo 952587 5432417 := bstep (se 2 (by rfl) ⟨2037156, by rfl⟩ : syracuseStep 5432417 = 4074313) B4074313
theorem B2712791 : Blo 952587 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B1434857 : Blo 952587 1434857 := bstep (se 2 (by rfl) ⟨538071, by rfl⟩ : syracuseStep 1434857 = 1076143) B1076143
theorem B2450675 : Blo 952587 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B3630329 : Blo 952587 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B2417951 : Blo 952587 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B1074523 : Blo 952587 1074523 := bstep (se 1 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 1074523 = 1611785) B1611785
theorem B1074631 : Blo 952587 1074631 := bstep (se 1 (by rfl) ⟨805973, by rfl⟩ : syracuseStep 1074631 = 1611947) B1611947
theorem B1205867 : Blo 952587 1205867 := bstep (se 1 (by rfl) ⟨904400, by rfl⟩ : syracuseStep 1205867 = 1808801) B1808801
theorem B9791165 : Blo 952587 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1074991 : Blo 952587 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B1075099 : Blo 952587 1075099 := bstep (se 1 (by rfl) ⟨806324, by rfl⟩ : syracuseStep 1075099 = 1612649) B1612649
theorem B1206247 : Blo 952587 1206247 := bstep (se 1 (by rfl) ⟨904685, by rfl⟩ : syracuseStep 1206247 = 1809371) B1809371
theorem B3434761 : Blo 952587 3434761 := bstep (se 2 (by rfl) ⟨1288035, by rfl⟩ : syracuseStep 3434761 = 2576071) B2576071
theorem B1075495 : Blo 952587 1075495 := bstep (se 1 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 1075495 = 1613243) B1613243
theorem B2419055 : Blo 952587 2419055 := bstep (se 1 (by rfl) ⟨1814291, by rfl⟩ : syracuseStep 2419055 = 3628583) B3628583
theorem B1075567 : Blo 952587 1075567 := bstep (se 1 (by rfl) ⟨806675, by rfl⟩ : syracuseStep 1075567 = 1613351) B1613351
theorem B4352507 : Blo 952587 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B1075783 : Blo 952587 1075783 := bstep (se 1 (by rfl) ⟨806837, by rfl⟩ : syracuseStep 1075783 = 1613675) B1613675
theorem B2419703 : Blo 952587 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B27487309 : Blo 952587 27487309 := bstep (se 3 (by rfl) ⟨5153870, by rfl⟩ : syracuseStep 27487309 = 10307741) B10307741
theorem B5795945 : Blo 952587 5795945 := bstep (se 2 (by rfl) ⟨2173479, by rfl⟩ : syracuseStep 5795945 = 4346959) B4346959
theorem B2584829 : Blo 952587 2584829 := bstep (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) B969311
theorem B14119343 : Blo 952587 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B6615751 : Blo 952587 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B2716915 : Blo 952587 2716915 := bstep (se 1 (by rfl) ⟨2037686, by rfl⟩ : syracuseStep 2716915 = 4075373) B4075373
theorem B6125003 : Blo 952587 6125003 := bstep (se 1 (by rfl) ⟨4593752, by rfl⟩ : syracuseStep 6125003 = 9187505) B9187505
theorem B1210079 : Blo 952587 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B3438625 : Blo 952587 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B11598157 : Blo 952587 11598157 := bstep (se 3 (by rfl) ⟨2174654, by rfl⟩ : syracuseStep 11598157 = 4349309) B4349309
theorem B4356463 : Blo 952587 4356463 := bstep (se 1 (by rfl) ⟨3267347, by rfl⟩ : syracuseStep 4356463 = 6534695) B6534695
theorem B13236605 : Blo 952587 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B7731845 : Blo 952587 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B3440009 : Blo 952587 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B3866429 : Blo 952587 3866429 := bstep (se 3 (by rfl) ⟨724955, by rfl⟩ : syracuseStep 3866429 = 1449911) B1449911
theorem B2293609 : Blo 952587 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B4588139 : Blo 952587 4588139 := bstep (se 1 (by rfl) ⟨3441104, by rfl⟩ : syracuseStep 4588139 = 6882209) B6882209
theorem B22086755 : Blo 952587 22086755 := bstep (se 1 (by rfl) ⟨16565066, by rfl⟩ : syracuseStep 22086755 = 33130133) B33130133
theorem B2720891 : Blo 952587 2720891 := bstep (se 1 (by rfl) ⟨2040668, by rfl⟩ : syracuseStep 2720891 = 4081337) B4081337
theorem B3442027 : Blo 952587 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B6882731 : Blo 952587 6882731 := bstep (se 1 (by rfl) ⟨5162048, by rfl⟩ : syracuseStep 6882731 = 10324097) B10324097
theorem B3540743 : Blo 952587 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B952623 : Blo 952587 952623 := bstep (se 1 (by rfl) ⟨714467, by rfl⟩ : syracuseStep 952623 = 1428935) B1428935
theorem B1608059 : Blo 952587 1608059 := bstep (se 1 (by rfl) ⟨1206044, by rfl⟩ : syracuseStep 1608059 = 2412089) B2412089
theorem B952859 : Blo 952587 952859 := bstep (se 1 (by rfl) ⟨714644, by rfl⟩ : syracuseStep 952859 = 1429289) B1429289
theorem B952863 : Blo 952587 952863 := bstep (se 1 (by rfl) ⟨714647, by rfl⟩ : syracuseStep 952863 = 1429295) B1429295
theorem B1608329 : Blo 952587 1608329 := bstep (se 2 (by rfl) ⟨603123, by rfl⟩ : syracuseStep 1608329 = 1206247) B1206247
theorem B953179 : Blo 952587 953179 := bstep (se 1 (by rfl) ⟨714884, by rfl⟩ : syracuseStep 953179 = 1429769) B1429769
theorem B1018715 : Blo 952587 1018715 := bstep (se 1 (by rfl) ⟨764036, by rfl⟩ : syracuseStep 1018715 = 1528073) B1528073
theorem B953247 : Blo 952587 953247 := bstep (se 1 (by rfl) ⟨714935, by rfl⟩ : syracuseStep 953247 = 1429871) B1429871
theorem B953391 : Blo 952587 953391 := bstep (se 1 (by rfl) ⟨715043, by rfl⟩ : syracuseStep 953391 = 1430087) B1430087
theorem B953415 : Blo 952587 953415 := bstep (se 1 (by rfl) ⟨715061, by rfl⟩ : syracuseStep 953415 = 1430123) B1430123
theorem B953567 : Blo 952587 953567 := bstep (se 1 (by rfl) ⟨715175, by rfl⟩ : syracuseStep 953567 = 1430351) B1430351
theorem B953831 : Blo 952587 953831 := bstep (se 1 (by rfl) ⟨715373, by rfl⟩ : syracuseStep 953831 = 1430747) B1430747
theorem B953947 : Blo 952587 953947 := bstep (se 1 (by rfl) ⟨715460, by rfl⟩ : syracuseStep 953947 = 1430921) B1430921
theorem B2723453 : Blo 952587 2723453 := bstep (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) B1021295
theorem B41258645 : Blo 952587 41258645 := bstep (se 6 (by rfl) ⟨966999, by rfl⟩ : syracuseStep 41258645 = 1933999) B1933999
theorem B954183 : Blo 952587 954183 := bstep (se 1 (by rfl) ⟨715637, by rfl⟩ : syracuseStep 954183 = 1431275) B1431275
theorem B1019719 : Blo 952587 1019719 := bstep (se 1 (by rfl) ⟨764789, by rfl⟩ : syracuseStep 1019719 = 1529579) B1529579
theorem B954335 : Blo 952587 954335 := bstep (se 1 (by rfl) ⟨715751, by rfl⟩ : syracuseStep 954335 = 1431503) B1431503
theorem B2723807 : Blo 952587 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B3215483 : Blo 952587 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B1609915 : Blo 952587 1609915 := bstep (se 1 (by rfl) ⟨1207436, by rfl⟩ : syracuseStep 1609915 = 2414873) B2414873
theorem B954599 : Blo 952587 954599 := bstep (se 1 (by rfl) ⟨715949, by rfl⟩ : syracuseStep 954599 = 1431899) B1431899
theorem B3215645 : Blo 952587 3215645 := bstep (se 3 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 3215645 = 1205867) B1205867
theorem B1610111 : Blo 952587 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B954751 : Blo 952587 954751 := bstep (se 1 (by rfl) ⟨716063, by rfl⟩ : syracuseStep 954751 = 1432127) B1432127
theorem B1020287 : Blo 952587 1020287 := bstep (se 1 (by rfl) ⟨765215, by rfl⟩ : syracuseStep 1020287 = 1530431) B1530431
theorem B3215753 : Blo 952587 3215753 := bstep (se 2 (by rfl) ⟨1205907, by rfl⟩ : syracuseStep 3215753 = 2411815) B2411815
theorem B20648357 : Blo 952587 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B954831 : Blo 952587 954831 := bstep (se 1 (by rfl) ⟨716123, by rfl⟩ : syracuseStep 954831 = 1432247) B1432247
theorem B158568941 : Blo 952587 158568941 := bstep (se 3 (by rfl) ⟨29731676, by rfl⟩ : syracuseStep 158568941 = 59463353) B59463353
theorem B5804531 : Blo 952587 5804531 := bstep (se 1 (by rfl) ⟨4353398, by rfl⟩ : syracuseStep 5804531 = 8706797) B8706797
theorem B8163935 : Blo 952587 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B954983 : Blo 952587 954983 := bstep (se 1 (by rfl) ⟨716237, by rfl⟩ : syracuseStep 954983 = 1432475) B1432475
theorem B1610543 : Blo 952587 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B955247 : Blo 952587 955247 := bstep (se 1 (by rfl) ⟨716435, by rfl⟩ : syracuseStep 955247 = 1432871) B1432871
theorem B7836551 : Blo 952587 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B955303 : Blo 952587 955303 := bstep (se 1 (by rfl) ⟨716477, by rfl⟩ : syracuseStep 955303 = 1432955) B1432955
theorem B955387 : Blo 952587 955387 := bstep (se 1 (by rfl) ⟨716540, by rfl⟩ : syracuseStep 955387 = 1433081) B1433081
theorem B955455 : Blo 952587 955455 := bstep (se 1 (by rfl) ⟨716591, by rfl⟩ : syracuseStep 955455 = 1433183) B1433183
theorem B955599 : Blo 952587 955599 := bstep (se 1 (by rfl) ⟨716699, by rfl⟩ : syracuseStep 955599 = 1433399) B1433399
theorem B3216671 : Blo 952587 3216671 := bstep (se 1 (by rfl) ⟨2412503, by rfl⟩ : syracuseStep 3216671 = 4825007) B4825007
theorem B13768055 : Blo 952587 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B955803 : Blo 952587 955803 := bstep (se 1 (by rfl) ⟨716852, by rfl⟩ : syracuseStep 955803 = 1433705) B1433705
theorem B956015 : Blo 952587 956015 := bstep (se 1 (by rfl) ⟨717011, by rfl⟩ : syracuseStep 956015 = 1434023) B1434023
theorem B956071 : Blo 952587 956071 := bstep (se 1 (by rfl) ⟨717053, by rfl⟩ : syracuseStep 956071 = 1434107) B1434107
theorem B1611515 : Blo 952587 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B956155 : Blo 952587 956155 := bstep (se 1 (by rfl) ⟨717116, by rfl⟩ : syracuseStep 956155 = 1434233) B1434233
theorem B956191 : Blo 952587 956191 := bstep (se 1 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 956191 = 1434287) B1434287
theorem B956223 : Blo 952587 956223 := bstep (se 1 (by rfl) ⟨717167, by rfl⟩ : syracuseStep 956223 = 1434335) B1434335
theorem B58824629 : Blo 952587 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B3053531 : Blo 952587 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B1611751 : Blo 952587 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B956399 : Blo 952587 956399 := bstep (se 1 (by rfl) ⟨717299, by rfl⟩ : syracuseStep 956399 = 1434599) B1434599
theorem B956571 : Blo 952587 956571 := bstep (se 1 (by rfl) ⟨717428, by rfl⟩ : syracuseStep 956571 = 1434857) B1434857
theorem B1611967 : Blo 952587 1611967 := bstep (se 1 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 1611967 = 2417951) B2417951
theorem B8821001 : Blo 952587 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B1612703 : Blo 952587 1612703 := bstep (se 1 (by rfl) ⟨1209527, by rfl⟩ : syracuseStep 1612703 = 2419055) B2419055
theorem B3218561 : Blo 952587 3218561 := bstep (se 2 (by rfl) ⟨1206960, by rfl⟩ : syracuseStep 3218561 = 2413921) B2413921
theorem B3218615 : Blo 952587 3218615 := bstep (se 1 (by rfl) ⟨2413961, by rfl⟩ : syracuseStep 3218615 = 4827923) B4827923
theorem B9182393 : Blo 952587 9182393 := bstep (se 2 (by rfl) ⟨3443397, by rfl⟩ : syracuseStep 9182393 = 6886795) B6886795
theorem B1613135 : Blo 952587 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B3219371 : Blo 952587 3219371 := bstep (se 1 (by rfl) ⟨2414528, by rfl⟩ : syracuseStep 3219371 = 4829057) B4829057
theorem B7938107 : Blo 952587 7938107 := bstep (se 1 (by rfl) ⟨5953580, by rfl⟩ : syracuseStep 7938107 = 11907161) B11907161
theorem B9412895 : Blo 952587 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B3219911 : Blo 952587 3219911 := bstep (se 1 (by rfl) ⟨2414933, by rfl⟩ : syracuseStep 3219911 = 4829867) B4829867
theorem B5808617 : Blo 952587 5808617 := bstep (se 2 (by rfl) ⟨2178231, by rfl⟩ : syracuseStep 5808617 = 4356463) B4356463
theorem B21504727 : Blo 952587 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B3220235 : Blo 952587 3220235 := bstep (se 1 (by rfl) ⟨2415176, by rfl⟩ : syracuseStep 3220235 = 4830353) B4830353
theorem B3220505 : Blo 952587 3220505 := bstep (se 2 (by rfl) ⟨1207689, by rfl⟩ : syracuseStep 3220505 = 2415379) B2415379
theorem B8824403 : Blo 952587 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B3221153 : Blo 952587 3221153 := bstep (se 2 (by rfl) ⟨1207932, by rfl⟩ : syracuseStep 3221153 = 2415865) B2415865
theorem B5154563 : Blo 952587 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B12396563 : Blo 952587 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B4073597 : Blo 952587 4073597 := bstep (se 3 (by rfl) ⟨763799, by rfl⟩ : syracuseStep 4073597 = 1527599) B1527599
theorem B3221855 : Blo 952587 3221855 := bstep (se 1 (by rfl) ⟨2416391, by rfl⟩ : syracuseStep 3221855 = 4832783) B4832783
theorem B3058145 : Blo 952587 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B3222017 : Blo 952587 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B23538251 : Blo 952587 23538251 := bstep (se 1 (by rfl) ⟨17653688, by rfl⟩ : syracuseStep 23538251 = 35307377) B35307377
theorem B3222503 : Blo 952587 3222503 := bstep (se 1 (by rfl) ⟨2416877, by rfl⟩ : syracuseStep 3222503 = 4833755) B4833755
theorem B3222827 : Blo 952587 3222827 := bstep (se 1 (by rfl) ⟨2417120, by rfl⟩ : syracuseStep 3222827 = 4834241) B4834241
theorem B6892877 : Blo 952587 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B3223097 : Blo 952587 3223097 := bstep (se 2 (by rfl) ⟨1208661, by rfl⟩ : syracuseStep 3223097 = 2417323) B2417323
theorem B8695775 : Blo 952587 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B4141043 : Blo 952587 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B7254521 : Blo 952587 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B3060605 : Blo 952587 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B26096741 : Blo 952587 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B3224987 : Blo 952587 3224987 := bstep (se 1 (by rfl) ⟨2418740, by rfl⟩ : syracuseStep 3224987 = 4837481) B4837481
theorem B7353991 : Blo 952587 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B2144231 : Blo 952587 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B2144249 : Blo 952587 2144249 := bstep (se 2 (by rfl) ⟨804093, by rfl⟩ : syracuseStep 2144249 = 1608187) B1608187
theorem B2144339 : Blo 952587 2144339 := bstep (se 1 (by rfl) ⟨1608254, by rfl⟩ : syracuseStep 2144339 = 3216509) B3216509
theorem B3225743 : Blo 952587 3225743 := bstep (se 1 (by rfl) ⟨2419307, by rfl⟩ : syracuseStep 3225743 = 4838615) B4838615
theorem B2144411 : Blo 952587 2144411 := bstep (se 1 (by rfl) ⟨1608308, by rfl⟩ : syracuseStep 2144411 = 3216617) B3216617
theorem B1358059 : Blo 952587 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B8698109 : Blo 952587 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B2144519 : Blo 952587 2144519 := bstep (se 1 (by rfl) ⟨1608389, by rfl⟩ : syracuseStep 2144519 = 3216779) B3216779
theorem B9156901 : Blo 952587 9156901 := bstep (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) B1716919
theorem B3619181 : Blo 952587 3619181 := bstep (se 3 (by rfl) ⟨678596, by rfl⟩ : syracuseStep 3619181 = 1357193) B1357193
theorem B2144825 : Blo 952587 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B36649745 : Blo 952587 36649745 := bstep (se 2 (by rfl) ⟨13743654, by rfl⟩ : syracuseStep 36649745 = 27487309) B27487309
theorem B4832297 : Blo 952587 4832297 := bstep (se 2 (by rfl) ⟨1812111, by rfl⟩ : syracuseStep 4832297 = 3624223) B3624223
theorem B12237905 : Blo 952587 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B3095767 : Blo 952587 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B3226877 : Blo 952587 3226877 := bstep (se 3 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 3226877 = 1210079) B1210079
theorem B2145545 : Blo 952587 2145545 := bstep (se 2 (by rfl) ⟨804579, by rfl⟩ : syracuseStep 2145545 = 1609159) B1609159
theorem B3980573 : Blo 952587 3980573 := bstep (se 3 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 3980573 = 1492715) B1492715
theorem B2899783 : Blo 952587 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B1720235 : Blo 952587 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B3227687 : Blo 952587 3227687 := bstep (se 1 (by rfl) ⟨2420765, by rfl⟩ : syracuseStep 3227687 = 4841531) B4841531
theorem B3621095 : Blo 952587 3621095 := bstep (se 1 (by rfl) ⟨2715821, by rfl⟩ : syracuseStep 3621095 = 5431643) B5431643
theorem B2146535 : Blo 952587 2146535 := bstep (se 1 (by rfl) ⟨1609901, by rfl⟩ : syracuseStep 2146535 = 3219803) B3219803
theorem B3228335 : Blo 952587 3228335 := bstep (se 1 (by rfl) ⟨2421251, by rfl⟩ : syracuseStep 3228335 = 4842503) B4842503
theorem B3621611 : Blo 952587 3621611 := bstep (se 1 (by rfl) ⟨2716208, by rfl⟩ : syracuseStep 3621611 = 5432417) B5432417
theorem B2147129 : Blo 952587 2147129 := bstep (se 2 (by rfl) ⟨805173, by rfl⟩ : syracuseStep 2147129 = 1610347) B1610347
theorem B2147183 : Blo 952587 2147183 := bstep (se 1 (by rfl) ⟨1610387, by rfl⟩ : syracuseStep 2147183 = 3220775) B3220775
theorem B12239909 : Blo 952587 12239909 := bstep (se 4 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 12239909 = 2294983) B2294983
theorem B1721417 : Blo 952587 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B11322767 : Blo 952587 11322767 := bstep (se 1 (by rfl) ⟨8492075, by rfl⟩ : syracuseStep 11322767 = 16984151) B16984151
theorem B2147759 : Blo 952587 2147759 := bstep (se 1 (by rfl) ⟨1610819, by rfl⟩ : syracuseStep 2147759 = 3221639) B3221639
theorem B6211019 : Blo 952587 6211019 := bstep (se 1 (by rfl) ⟨4658264, by rfl⟩ : syracuseStep 6211019 = 9316529) B9316529
theorem B5817815 : Blo 952587 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B3261971 : Blo 952587 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B3622553 : Blo 952587 3622553 := bstep (se 2 (by rfl) ⟨1358457, by rfl⟩ : syracuseStep 3622553 = 2716915) B2716915
theorem B2901671 : Blo 952587 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B1361863 : Blo 952587 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B3262409 : Blo 952587 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B4835537 : Blo 952587 4835537 := bstep (se 2 (by rfl) ⟨1813326, by rfl⟩ : syracuseStep 4835537 = 3626653) B3626653
theorem B2148587 : Blo 952587 2148587 := bstep (se 1 (by rfl) ⟨1611440, by rfl⟩ : syracuseStep 2148587 = 3222881) B3222881
theorem B19614109 : Blo 952587 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B7358921 : Blo 952587 7358921 := bstep (se 2 (by rfl) ⟨2759595, by rfl⟩ : syracuseStep 7358921 = 5519191) B5519191
theorem B15452795 : Blo 952587 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B5425811 : Blo 952587 5425811 := bstep (se 1 (by rfl) ⟨4069358, by rfl⟩ : syracuseStep 5425811 = 8138717) B8138717
theorem B1428905 : Blo 952587 1428905 := bstep (se 2 (by rfl) ⟨535839, by rfl⟩ : syracuseStep 1428905 = 1071679) B1071679
theorem B2149883 : Blo 952587 2149883 := bstep (se 1 (by rfl) ⟨1612412, by rfl⟩ : syracuseStep 2149883 = 3224825) B3224825
theorem B1429055 : Blo 952587 1429055 := bstep (se 1 (by rfl) ⟨1071791, by rfl⟩ : syracuseStep 1429055 = 2143583) B2143583
theorem B2412139 : Blo 952587 2412139 := bstep (se 1 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 2412139 = 3618209) B3618209
theorem B4083335 : Blo 952587 4083335 := bstep (se 1 (by rfl) ⟨3062501, by rfl⟩ : syracuseStep 4083335 = 6125003) B6125003
theorem B27512459 : Blo 952587 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B2150063 : Blo 952587 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B1429319 : Blo 952587 1429319 := bstep (se 1 (by rfl) ⟨1071989, by rfl⟩ : syracuseStep 1429319 = 2143979) B2143979
theorem B1429403 : Blo 952587 1429403 := bstep (se 1 (by rfl) ⟨1072052, by rfl⟩ : syracuseStep 1429403 = 2144105) B2144105
theorem B2412443 : Blo 952587 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B2150711 : Blo 952587 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B2150783 : Blo 952587 2150783 := bstep (se 1 (by rfl) ⟨1613087, by rfl⟩ : syracuseStep 2150783 = 3226175) B3226175
theorem B4837805 : Blo 952587 4837805 := bstep (se 3 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 4837805 = 1814177) B1814177
theorem B1429967 : Blo 952587 1429967 := bstep (se 1 (by rfl) ⟨1072475, by rfl⟩ : syracuseStep 1429967 = 2144951) B2144951
theorem B1430009 : Blo 952587 1430009 := bstep (se 2 (by rfl) ⟨536253, by rfl⟩ : syracuseStep 1430009 = 1072507) B1072507
theorem B4837967 : Blo 952587 4837967 := bstep (se 1 (by rfl) ⟨3628475, by rfl⟩ : syracuseStep 4837967 = 7256951) B7256951
theorem B1430111 : Blo 952587 1430111 := bstep (se 1 (by rfl) ⟨1072583, by rfl⟩ : syracuseStep 1430111 = 2145167) B2145167
theorem B3724283 : Blo 952587 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B2413577 : Blo 952587 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1430591 : Blo 952587 1430591 := bstep (se 1 (by rfl) ⟨1072943, by rfl⟩ : syracuseStep 1430591 = 2145887) B2145887
theorem B1430633 : Blo 952587 1430633 := bstep (se 2 (by rfl) ⟨536487, by rfl⟩ : syracuseStep 1430633 = 1072975) B1072975
theorem B1430735 : Blo 952587 1430735 := bstep (se 1 (by rfl) ⟨1073051, by rfl⟩ : syracuseStep 1430735 = 2146103) B2146103
theorem B2577619 : Blo 952587 2577619 := bstep (se 1 (by rfl) ⟨1933214, by rfl⟩ : syracuseStep 2577619 = 3866429) B3866429
theorem B10867931 : Blo 952587 10867931 := bstep (se 1 (by rfl) ⟨8150948, by rfl⟩ : syracuseStep 10867931 = 16301897) B16301897
theorem B1430939 : Blo 952587 1430939 := bstep (se 1 (by rfl) ⟨1073204, by rfl⟩ : syracuseStep 1430939 = 2146409) B2146409
theorem B2152007 : Blo 952587 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B1431161 : Blo 952587 1431161 := bstep (se 2 (by rfl) ⟨536685, by rfl⟩ : syracuseStep 1431161 = 1073371) B1073371
theorem B26105489 : Blo 952587 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B1431263 : Blo 952587 1431263 := bstep (se 1 (by rfl) ⟨1073447, by rfl⟩ : syracuseStep 1431263 = 2146895) B2146895
theorem B2152187 : Blo 952587 2152187 := bstep (se 1 (by rfl) ⟨1614140, by rfl⟩ : syracuseStep 2152187 = 3228281) B3228281
theorem B1431359 : Blo 952587 1431359 := bstep (se 1 (by rfl) ⟨1073519, by rfl⟩ : syracuseStep 1431359 = 2147039) B2147039
theorem B1431527 : Blo 952587 1431527 := bstep (se 1 (by rfl) ⟨1073645, by rfl⟩ : syracuseStep 1431527 = 2147291) B2147291
theorem B1431545 : Blo 952587 1431545 := bstep (se 2 (by rfl) ⟨536829, by rfl⟩ : syracuseStep 1431545 = 1073659) B1073659
theorem B4839425 : Blo 952587 4839425 := bstep (se 2 (by rfl) ⟨1814784, by rfl⟩ : syracuseStep 4839425 = 3629569) B3629569
theorem B4085761 : Blo 952587 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B1431647 : Blo 952587 1431647 := bstep (se 1 (by rfl) ⟨1073735, by rfl⟩ : syracuseStep 1431647 = 2147471) B2147471
theorem B1431707 : Blo 952587 1431707 := bstep (se 1 (by rfl) ⟨1073780, by rfl⟩ : syracuseStep 1431707 = 2147561) B2147561
theorem B1431743 : Blo 952587 1431743 := bstep (se 1 (by rfl) ⟨1073807, by rfl⟩ : syracuseStep 1431743 = 2147615) B2147615
theorem B1431785 : Blo 952587 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B18372851 : Blo 952587 18372851 := bstep (se 1 (by rfl) ⟨13779638, by rfl⟩ : syracuseStep 18372851 = 27559277) B27559277
theorem B16341263 : Blo 952587 16341263 := bstep (se 1 (by rfl) ⟨12255947, by rfl⟩ : syracuseStep 16341263 = 24511895) B24511895
theorem B1432091 : Blo 952587 1432091 := bstep (se 1 (by rfl) ⟨1074068, by rfl⟩ : syracuseStep 1432091 = 2148137) B2148137
theorem B1432169 : Blo 952587 1432169 := bstep (se 2 (by rfl) ⟨537063, by rfl⟩ : syracuseStep 1432169 = 1074127) B1074127
theorem B4840073 : Blo 952587 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B4840235 : Blo 952587 4840235 := bstep (se 1 (by rfl) ⟨3630176, by rfl⟩ : syracuseStep 4840235 = 7260353) B7260353
theorem B6872033 : Blo 952587 6872033 := bstep (se 2 (by rfl) ⟨2577012, by rfl⟩ : syracuseStep 6872033 = 5154025) B5154025
theorem B1432697 : Blo 952587 1432697 := bstep (se 2 (by rfl) ⟨537261, by rfl⟩ : syracuseStep 1432697 = 1074523) B1074523
theorem B1432799 : Blo 952587 1432799 := bstep (se 1 (by rfl) ⟨1074599, by rfl⟩ : syracuseStep 1432799 = 2149199) B2149199
theorem B1432841 : Blo 952587 1432841 := bstep (se 2 (by rfl) ⟨537315, by rfl⟩ : syracuseStep 1432841 = 1074631) B1074631
theorem B1432943 : Blo 952587 1432943 := bstep (se 1 (by rfl) ⟨1074707, by rfl⟩ : syracuseStep 1432943 = 2149415) B2149415
theorem B12213665 : Blo 952587 12213665 := bstep (se 2 (by rfl) ⟨4580124, by rfl⟩ : syracuseStep 12213665 = 9160249) B9160249
theorem B1072615 : Blo 952587 1072615 := bstep (se 1 (by rfl) ⟨804461, by rfl⟩ : syracuseStep 1072615 = 1608923) B1608923
theorem B1433063 : Blo 952587 1433063 := bstep (se 1 (by rfl) ⟨1074797, by rfl⟩ : syracuseStep 1433063 = 2149595) B2149595
theorem B1629803 : Blo 952587 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B1433195 : Blo 952587 1433195 := bstep (se 1 (by rfl) ⟨1074896, by rfl⟩ : syracuseStep 1433195 = 2149793) B2149793
theorem B1433321 : Blo 952587 1433321 := bstep (se 2 (by rfl) ⟨537495, by rfl⟩ : syracuseStep 1433321 = 1074991) B1074991
theorem B3628871 : Blo 952587 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B1433465 : Blo 952587 1433465 := bstep (se 2 (by rfl) ⟨537549, by rfl⟩ : syracuseStep 1433465 = 1075099) B1075099
theorem B1073119 : Blo 952587 1073119 := bstep (se 1 (by rfl) ⟨804839, by rfl⟩ : syracuseStep 1073119 = 1609679) B1609679
theorem B1433567 : Blo 952587 1433567 := bstep (se 1 (by rfl) ⟨1075175, by rfl⟩ : syracuseStep 1433567 = 2150351) B2150351
theorem B1433819 : Blo 952587 1433819 := bstep (se 1 (by rfl) ⟨1075364, by rfl⟩ : syracuseStep 1433819 = 2150729) B2150729
theorem B1433831 : Blo 952587 1433831 := bstep (se 1 (by rfl) ⟨1075373, by rfl⟩ : syracuseStep 1433831 = 2150747) B2150747
theorem B6119671 : Blo 952587 6119671 := bstep (se 1 (by rfl) ⟨4589753, by rfl⟩ : syracuseStep 6119671 = 9179507) B9179507
theorem B4579681 : Blo 952587 4579681 := bstep (se 2 (by rfl) ⟨1717380, by rfl⟩ : syracuseStep 4579681 = 3434761) B3434761
theorem B20668769 : Blo 952587 20668769 := bstep (se 2 (by rfl) ⟨7750788, by rfl⟩ : syracuseStep 20668769 = 15501577) B15501577
theorem B1433993 : Blo 952587 1433993 := bstep (se 2 (by rfl) ⟨537747, by rfl⟩ : syracuseStep 1433993 = 1075495) B1075495
theorem B1434089 : Blo 952587 1434089 := bstep (se 2 (by rfl) ⟨537783, by rfl⟩ : syracuseStep 1434089 = 1075567) B1075567
theorem B7234109 : Blo 952587 7234109 := bstep (se 3 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 7234109 = 2712791) B2712791
theorem B6873673 : Blo 952587 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B1073767 : Blo 952587 1073767 := bstep (se 1 (by rfl) ⟨805325, by rfl⟩ : syracuseStep 1073767 = 1610651) B1610651
theorem B1434215 : Blo 952587 1434215 := bstep (se 1 (by rfl) ⟨1075661, by rfl⟩ : syracuseStep 1434215 = 2151323) B2151323
theorem B5431961 : Blo 952587 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B1434347 : Blo 952587 1434347 := bstep (se 1 (by rfl) ⟨1075760, by rfl⟩ : syracuseStep 1434347 = 2151521) B2151521
theorem B1434377 : Blo 952587 1434377 := bstep (se 2 (by rfl) ⟨537891, by rfl⟩ : syracuseStep 1434377 = 1075783) B1075783
theorem B3629843 : Blo 952587 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B2417465 : Blo 952587 2417465 := bstep (se 2 (by rfl) ⟨906549, by rfl⟩ : syracuseStep 2417465 = 1813099) B1813099
theorem B5432143 : Blo 952587 5432143 := bstep (se 1 (by rfl) ⟨4074107, by rfl⟩ : syracuseStep 5432143 = 8148215) B8148215
theorem B46523231 : Blo 952587 46523231 := bstep (se 1 (by rfl) ⟨34892423, by rfl⟩ : syracuseStep 46523231 = 69784847) B69784847
theorem B1434479 : Blo 952587 1434479 := bstep (se 1 (by rfl) ⟨1075859, by rfl⟩ : syracuseStep 1434479 = 2151719) B2151719
theorem B1434731 : Blo 952587 1434731 := bstep (se 1 (by rfl) ⟨1076048, by rfl⟩ : syracuseStep 1434731 = 2152097) B2152097
theorem B99313037 : Blo 952587 99313037 := bstep (se 3 (by rfl) ⟨18621194, by rfl⟩ : syracuseStep 99313037 = 37242389) B37242389
theorem B26109773 : Blo 952587 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B6121619 : Blo 952587 6121619 := bstep (se 1 (by rfl) ⟨4591214, by rfl⟩ : syracuseStep 6121619 = 9182429) B9182429
theorem B2418923 : Blo 952587 2418923 := bstep (se 1 (by rfl) ⟨1814192, by rfl⟩ : syracuseStep 2418923 = 3628385) B3628385
theorem B3631499 : Blo 952587 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B2419105 : Blo 952587 2419105 := bstep (se 2 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 2419105 = 1814329) B1814329
theorem B6122233 : Blo 952587 6122233 := bstep (se 2 (by rfl) ⟨2295837, by rfl⟩ : syracuseStep 6122233 = 4591675) B4591675
theorem B7236539 : Blo 952587 7236539 := bstep (se 1 (by rfl) ⟨5427404, by rfl⟩ : syracuseStep 7236539 = 10854809) B10854809
theorem B8711171 : Blo 952587 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B1633783 : Blo 952587 1633783 := bstep (se 1 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 1633783 = 2450675) B2450675
theorem B2420219 : Blo 952587 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B19558097 : Blo 952587 19558097 := bstep (se 2 (by rfl) ⟨7334286, by rfl⟩ : syracuseStep 19558097 = 14668573) B14668573
theorem B1208135 : Blo 952587 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B1208287 : Blo 952587 1208287 := bstep (se 1 (by rfl) ⟨906215, by rfl⟩ : syracuseStep 1208287 = 1812431) B1812431
theorem B3436667 : Blo 952587 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B1208783 : Blo 952587 1208783 := bstep (se 1 (by rfl) ⟨906587, by rfl⟩ : syracuseStep 1208783 = 1813175) B1813175
theorem B2290169 : Blo 952587 2290169 := bstep (se 2 (by rfl) ⟨858813, by rfl⟩ : syracuseStep 2290169 = 1717627) B1717627
theorem B1208935 : Blo 952587 1208935 := bstep (se 1 (by rfl) ⟨906701, by rfl⟩ : syracuseStep 1208935 = 1813403) B1813403
theorem B17396369 : Blo 952587 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B52359857 : Blo 952587 52359857 := bstep (se 2 (by rfl) ⟨19634946, by rfl⟩ : syracuseStep 52359857 = 39269893) B39269893
theorem B2716847 : Blo 952587 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B4584833 : Blo 952587 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B3863963 : Blo 952587 3863963 := bstep (se 1 (by rfl) ⟨2897972, by rfl⟩ : syracuseStep 3863963 = 5795945) B5795945
theorem B1209755 : Blo 952587 1209755 := bstep (se 1 (by rfl) ⟨907316, by rfl⟩ : syracuseStep 1209755 = 1814633) B1814633
theorem B15464209 : Blo 952587 15464209 := bstep (se 2 (by rfl) ⟨5799078, by rfl⟩ : syracuseStep 15464209 = 11598157) B11598157
theorem B9173357 : Blo 952587 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B11041343 : Blo 952587 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B2718431 : Blo 952587 2718431 := bstep (se 1 (by rfl) ⟨2038823, by rfl⟩ : syracuseStep 2718431 = 4077647) B4077647
theorem B2718623 : Blo 952587 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B11631833 : Blo 952587 11631833 := bstep (se 2 (by rfl) ⟨4361937, by rfl⟩ : syracuseStep 11631833 = 8723875) B8723875
theorem B8159561 : Blo 952587 8159561 := bstep (se 2 (by rfl) ⟨3059835, by rfl⟩ : syracuseStep 8159561 = 6119671) B6119671
theorem B8159939 : Blo 952587 8159939 := bstep (se 1 (by rfl) ⟨6119954, by rfl⟩ : syracuseStep 8159939 = 12239909) B12239909
theorem B25101053 : Blo 952587 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B4588487 : Blo 952587 4588487 := bstep (se 1 (by rfl) ⟨3441365, by rfl⟩ : syracuseStep 4588487 = 6882731) B6882731
theorem B28672969 : Blo 952587 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B2720765 : Blo 952587 2720765 := bstep (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) B1020287
theorem B7242857 : Blo 952587 7242857 := bstep (se 2 (by rfl) ⟨2716071, by rfl⟩ : syracuseStep 7242857 = 5432143) B5432143
theorem B1934447 : Blo 952587 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B2360495 : Blo 952587 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B4589369 : Blo 952587 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B952603 : Blo 952587 952603 := bstep (se 1 (by rfl) ⟨714452, by rfl⟩ : syracuseStep 952603 = 1428905) B1428905
theorem B952703 : Blo 952587 952703 := bstep (se 1 (by rfl) ⟨714527, by rfl⟩ : syracuseStep 952703 = 1429055) B1429055
theorem B2722223 : Blo 952587 2722223 := bstep (se 1 (by rfl) ⟨2041667, by rfl⟩ : syracuseStep 2722223 = 4083335) B4083335
theorem B952879 : Blo 952587 952879 := bstep (se 1 (by rfl) ⟨714659, by rfl⟩ : syracuseStep 952879 = 1429319) B1429319
theorem B952935 : Blo 952587 952935 := bstep (se 1 (by rfl) ⟨714701, by rfl⟩ : syracuseStep 952935 = 1429403) B1429403
theorem B1608295 : Blo 952587 1608295 := bstep (se 1 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 1608295 = 2412443) B2412443
theorem B4590445 : Blo 952587 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B13765571 : Blo 952587 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B953311 : Blo 952587 953311 := bstep (se 1 (by rfl) ⟨714983, by rfl⟩ : syracuseStep 953311 = 1429967) B1429967
theorem B105712627 : Blo 952587 105712627 := bstep (se 1 (by rfl) ⟨79284470, by rfl⟩ : syracuseStep 105712627 = 158568941) B158568941
theorem B3869687 : Blo 952587 3869687 := bstep (se 1 (by rfl) ⟨2902265, by rfl⟩ : syracuseStep 3869687 = 5804531) B5804531
theorem B953339 : Blo 952587 953339 := bstep (se 1 (by rfl) ⟨715004, by rfl⟩ : syracuseStep 953339 = 1430009) B1430009
theorem B953407 : Blo 952587 953407 := bstep (se 1 (by rfl) ⟨715055, by rfl⟩ : syracuseStep 953407 = 1430111) B1430111
theorem B5442623 : Blo 952587 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B26152145 : Blo 952587 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B1609051 : Blo 952587 1609051 := bstep (se 1 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 1609051 = 2413577) B2413577
theorem B953727 : Blo 952587 953727 := bstep (se 1 (by rfl) ⟨715295, by rfl⟩ : syracuseStep 953727 = 1430591) B1430591
theorem B953755 : Blo 952587 953755 := bstep (se 1 (by rfl) ⟨715316, by rfl⟩ : syracuseStep 953755 = 1430633) B1430633
theorem B953823 : Blo 952587 953823 := bstep (se 1 (by rfl) ⟨715367, by rfl⟩ : syracuseStep 953823 = 1430735) B1430735
theorem B7245287 : Blo 952587 7245287 := bstep (se 1 (by rfl) ⟨5433965, by rfl⟩ : syracuseStep 7245287 = 10867931) B10867931
theorem B9178703 : Blo 952587 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B953959 : Blo 952587 953959 := bstep (se 1 (by rfl) ⟨715469, by rfl⟩ : syracuseStep 953959 = 1430939) B1430939
theorem B8162977 : Blo 952587 8162977 := bstep (se 2 (by rfl) ⟨3061116, by rfl⟩ : syracuseStep 8162977 = 6122233) B6122233
theorem B954107 : Blo 952587 954107 := bstep (se 1 (by rfl) ⟨715580, by rfl⟩ : syracuseStep 954107 = 1431161) B1431161
theorem B17403659 : Blo 952587 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B954175 : Blo 952587 954175 := bstep (se 1 (by rfl) ⟨715631, by rfl⟩ : syracuseStep 954175 = 1431263) B1431263
theorem B954239 : Blo 952587 954239 := bstep (se 1 (by rfl) ⟨715679, by rfl⟩ : syracuseStep 954239 = 1431359) B1431359
theorem B2035687 : Blo 952587 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B954351 : Blo 952587 954351 := bstep (se 1 (by rfl) ⟨715763, by rfl⟩ : syracuseStep 954351 = 1431527) B1431527
theorem B954363 : Blo 952587 954363 := bstep (se 1 (by rfl) ⟨715772, by rfl⟩ : syracuseStep 954363 = 1431545) B1431545
theorem B954431 : Blo 952587 954431 := bstep (se 1 (by rfl) ⟨715823, by rfl⟩ : syracuseStep 954431 = 1431647) B1431647
theorem B954471 : Blo 952587 954471 := bstep (se 1 (by rfl) ⟨715853, by rfl⟩ : syracuseStep 954471 = 1431707) B1431707
theorem B954495 : Blo 952587 954495 := bstep (se 1 (by rfl) ⟨715871, by rfl⟩ : syracuseStep 954495 = 1431743) B1431743
theorem B954523 : Blo 952587 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B23531741 : Blo 952587 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B954727 : Blo 952587 954727 := bstep (se 1 (by rfl) ⟨716045, by rfl⟩ : syracuseStep 954727 = 1432091) B1432091
theorem B954779 : Blo 952587 954779 := bstep (se 1 (by rfl) ⟨716084, by rfl⟩ : syracuseStep 954779 = 1432169) B1432169
theorem B955131 : Blo 952587 955131 := bstep (se 1 (by rfl) ⟨716348, by rfl⟩ : syracuseStep 955131 = 1432697) B1432697
theorem B3216185 : Blo 952587 3216185 := bstep (se 2 (by rfl) ⟨1206069, by rfl⟩ : syracuseStep 3216185 = 2412139) B2412139
theorem B955199 : Blo 952587 955199 := bstep (se 1 (by rfl) ⟨716399, by rfl⟩ : syracuseStep 955199 = 1432799) B1432799
theorem B955227 : Blo 952587 955227 := bstep (se 1 (by rfl) ⟨716420, by rfl⟩ : syracuseStep 955227 = 1432841) B1432841
theorem B955295 : Blo 952587 955295 := bstep (se 1 (by rfl) ⟨716471, by rfl⟩ : syracuseStep 955295 = 1432943) B1432943
theorem B955375 : Blo 952587 955375 := bstep (se 1 (by rfl) ⟨716531, by rfl⟩ : syracuseStep 955375 = 1433063) B1433063
theorem B1086535 : Blo 952587 1086535 := bstep (se 1 (by rfl) ⟨814901, by rfl⟩ : syracuseStep 1086535 = 1629803) B1629803
theorem B955463 : Blo 952587 955463 := bstep (se 1 (by rfl) ⟨716597, by rfl⟩ : syracuseStep 955463 = 1433195) B1433195
theorem B955547 : Blo 952587 955547 := bstep (se 1 (by rfl) ⟨716660, by rfl⟩ : syracuseStep 955547 = 1433321) B1433321
theorem B955643 : Blo 952587 955643 := bstep (se 1 (by rfl) ⟨716732, by rfl⟩ : syracuseStep 955643 = 1433465) B1433465
theorem B1611049 : Blo 952587 1611049 := bstep (se 2 (by rfl) ⟨604143, by rfl⟩ : syracuseStep 1611049 = 1208287) B1208287
theorem B955711 : Blo 952587 955711 := bstep (se 1 (by rfl) ⟨716783, by rfl⟩ : syracuseStep 955711 = 1433567) B1433567
theorem B955879 : Blo 952587 955879 := bstep (se 1 (by rfl) ⟨716909, by rfl⟩ : syracuseStep 955879 = 1433819) B1433819
theorem B955887 : Blo 952587 955887 := bstep (se 1 (by rfl) ⟨716915, by rfl⟩ : syracuseStep 955887 = 1433831) B1433831
theorem B955995 : Blo 952587 955995 := bstep (se 1 (by rfl) ⟨716996, by rfl⟩ : syracuseStep 955995 = 1433993) B1433993
theorem B3872411 : Blo 952587 3872411 := bstep (se 1 (by rfl) ⟨2904308, by rfl⟩ : syracuseStep 3872411 = 5808617) B5808617
theorem B956059 : Blo 952587 956059 := bstep (se 1 (by rfl) ⟨717044, by rfl⟩ : syracuseStep 956059 = 1434089) B1434089
theorem B4822739 : Blo 952587 4822739 := bstep (se 1 (by rfl) ⟨3617054, by rfl⟩ : syracuseStep 4822739 = 7234109) B7234109
theorem B956143 : Blo 952587 956143 := bstep (se 1 (by rfl) ⟨717107, by rfl⟩ : syracuseStep 956143 = 1434215) B1434215
theorem B956231 : Blo 952587 956231 := bstep (se 1 (by rfl) ⟨717173, by rfl⟩ : syracuseStep 956231 = 1434347) B1434347
theorem B956251 : Blo 952587 956251 := bstep (se 1 (by rfl) ⟨717188, by rfl⟩ : syracuseStep 956251 = 1434377) B1434377
theorem B1611643 : Blo 952587 1611643 := bstep (se 1 (by rfl) ⟨1208732, by rfl⟩ : syracuseStep 1611643 = 2417465) B2417465
theorem B956319 : Blo 952587 956319 := bstep (se 1 (by rfl) ⟨717239, by rfl⟩ : syracuseStep 956319 = 1434479) B1434479
theorem B956487 : Blo 952587 956487 := bstep (se 1 (by rfl) ⟨717365, by rfl⟩ : syracuseStep 956487 = 1434731) B1434731
theorem B1611913 : Blo 952587 1611913 := bstep (se 2 (by rfl) ⟨604467, by rfl⟩ : syracuseStep 1611913 = 1208935) B1208935
theorem B17406515 : Blo 952587 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B8264375 : Blo 952587 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B1612615 : Blo 952587 1612615 := bstep (se 1 (by rfl) ⟨1209461, by rfl⟩ : syracuseStep 1612615 = 2418923) B2418923
theorem B2038763 : Blo 952587 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B4824359 : Blo 952587 4824359 := bstep (se 1 (by rfl) ⟨3618269, by rfl⟩ : syracuseStep 4824359 = 7236539) B7236539
theorem B5807447 : Blo 952587 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B9805321 : Blo 952587 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B1613479 : Blo 952587 1613479 := bstep (se 1 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 1613479 = 2420219) B2420219
theorem B20618945 : Blo 952587 20618945 := bstep (se 2 (by rfl) ⟨7732104, by rfl⟩ : syracuseStep 20618945 = 15464209) B15464209
theorem B7249661 : Blo 952587 7249661 := bstep (se 3 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 7249661 = 2718623) B2718623
theorem B2760695 : Blo 952587 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B5447681 : Blo 952587 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B1810745 : Blo 952587 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B34906571 : Blo 952587 34906571 := bstep (se 1 (by rfl) ⟨26179928, by rfl⟩ : syracuseStep 34906571 = 52359857) B52359857
theorem B2040403 : Blo 952587 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B1811231 : Blo 952587 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B3056555 : Blo 952587 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B1812287 : Blo 952587 1812287 := bstep (se 1 (by rfl) ⟨1359215, by rfl⟩ : syracuseStep 1812287 = 2718431) B2718431
theorem B3221531 : Blo 952587 3221531 := bstep (se 1 (by rfl) ⟨2416148, by rfl⟩ : syracuseStep 3221531 = 4832297) B4832297
theorem B3221693 : Blo 952587 3221693 := bstep (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) B1208135
theorem B3058759 : Blo 952587 3058759 := bstep (se 1 (by rfl) ⟨2294069, by rfl⟩ : syracuseStep 3058759 = 4588139) B4588139
theorem B6106241 : Blo 952587 6106241 := bstep (se 2 (by rfl) ⟨2289840, by rfl⟩ : syracuseStep 6106241 = 4579681) B4579681
theorem B14724503 : Blo 952587 14724503 := bstep (se 1 (by rfl) ⟨11043377, by rfl⟩ : syracuseStep 14724503 = 22086755) B22086755
theorem B1813927 : Blo 952587 1813927 := bstep (se 1 (by rfl) ⟨1360445, by rfl⟩ : syracuseStep 1813927 = 2720891) B2720891
theorem B7548511 : Blo 952587 7548511 := bstep (se 1 (by rfl) ⟨5661383, by rfl⟩ : syracuseStep 7548511 = 11322767) B11322767
theorem B4140679 : Blo 952587 4140679 := bstep (se 1 (by rfl) ⟨3105509, by rfl⟩ : syracuseStep 4140679 = 6211019) B6211019
theorem B3878543 : Blo 952587 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B3223421 : Blo 952587 3223421 := bstep (se 3 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 3223421 = 1208783) B1208783
theorem B2174939 : Blo 952587 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B3223691 : Blo 952587 3223691 := bstep (se 1 (by rfl) ⟨2417768, by rfl⟩ : syracuseStep 3223691 = 4835537) B4835537
theorem B10301863 : Blo 952587 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B3617207 : Blo 952587 3617207 := bstep (se 1 (by rfl) ⟨2712905, by rfl⟩ : syracuseStep 3617207 = 5425811) B5425811
theorem B1815635 : Blo 952587 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B27505763 : Blo 952587 27505763 := bstep (se 1 (by rfl) ⟨20629322, by rfl⟩ : syracuseStep 27505763 = 41258645) B41258645
theorem B1815871 : Blo 952587 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B2143655 : Blo 952587 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B2143763 : Blo 952587 2143763 := bstep (se 1 (by rfl) ⟨1607822, by rfl⟩ : syracuseStep 2143763 = 3215645) B3215645
theorem B2143835 : Blo 952587 2143835 := bstep (se 1 (by rfl) ⟨1607876, by rfl⟩ : syracuseStep 2143835 = 3215753) B3215753
theorem B3225203 : Blo 952587 3225203 := bstep (se 1 (by rfl) ⟨2418902, by rfl⟩ : syracuseStep 3225203 = 4837805) B4837805
theorem B3225311 : Blo 952587 3225311 := bstep (se 1 (by rfl) ⟨2418983, by rfl⟩ : syracuseStep 3225311 = 4837967) B4837967
theorem B3225473 : Blo 952587 3225473 := bstep (se 2 (by rfl) ⟨1209552, by rfl⟩ : syracuseStep 3225473 = 2419105) B2419105
theorem B5224367 : Blo 952587 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B2144447 : Blo 952587 2144447 := bstep (se 1 (by rfl) ⟨1608335, by rfl⟩ : syracuseStep 2144447 = 3216671) B3216671
theorem B3226013 : Blo 952587 3226013 := bstep (se 3 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 3226013 = 1209755) B1209755
theorem B3226283 : Blo 952587 3226283 := bstep (se 1 (by rfl) ⟨2419712, by rfl⟩ : syracuseStep 3226283 = 4839425) B4839425
theorem B8698589 : Blo 952587 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B5880667 : Blo 952587 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B10894175 : Blo 952587 10894175 := bstep (se 1 (by rfl) ⟨8170631, by rfl⟩ : syracuseStep 10894175 = 16341263) B16341263
theorem B3226715 : Blo 952587 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B3226823 : Blo 952587 3226823 := bstep (se 1 (by rfl) ⟨2420117, by rfl⟩ : syracuseStep 3226823 = 4840235) B4840235
theorem B2178377 : Blo 952587 2178377 := bstep (se 2 (by rfl) ⟨816891, by rfl⟩ : syracuseStep 2178377 = 1633783) B1633783
theorem B13745501 : Blo 952587 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B2145707 : Blo 952587 2145707 := bstep (se 1 (by rfl) ⟨1609280, by rfl⟩ : syracuseStep 2145707 = 3218561) B3218561
theorem B2145743 : Blo 952587 2145743 := bstep (se 1 (by rfl) ⟨1609307, by rfl⟩ : syracuseStep 2145743 = 3218615) B3218615
theorem B8142443 : Blo 952587 8142443 := bstep (se 1 (by rfl) ⟨6106832, by rfl⟩ : syracuseStep 8142443 = 12213665) B12213665
theorem B2146247 : Blo 952587 2146247 := bstep (se 1 (by rfl) ⟨1609685, by rfl⟩ : syracuseStep 2146247 = 3219371) B3219371
theorem B5292071 : Blo 952587 5292071 := bstep (se 1 (by rfl) ⟨3969053, by rfl⟩ : syracuseStep 5292071 = 7938107) B7938107
theorem B13779179 : Blo 952587 13779179 := bstep (se 1 (by rfl) ⟨10334384, by rfl⟩ : syracuseStep 13779179 = 20668769) B20668769
theorem B2146553 : Blo 952587 2146553 := bstep (se 2 (by rfl) ⟨804957, by rfl⟩ : syracuseStep 2146553 = 1609915) B1609915
theorem B2146607 : Blo 952587 2146607 := bstep (se 1 (by rfl) ⟨1609955, by rfl⟩ : syracuseStep 2146607 = 3219911) B3219911
theorem B3621307 : Blo 952587 3621307 := bstep (se 1 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 3621307 = 5431961) B5431961
theorem B2146823 : Blo 952587 2146823 := bstep (se 1 (by rfl) ⟨1610117, by rfl⟩ : syracuseStep 2146823 = 3220235) B3220235
theorem B31015487 : Blo 952587 31015487 := bstep (se 1 (by rfl) ⟨23261615, by rfl⟩ : syracuseStep 31015487 = 46523231) B46523231
theorem B2147003 : Blo 952587 2147003 := bstep (se 1 (by rfl) ⟨1610252, by rfl⟩ : syracuseStep 2147003 = 3220505) B3220505
theorem B66208691 : Blo 952587 66208691 := bstep (se 1 (by rfl) ⟨49656518, by rfl⟩ : syracuseStep 66208691 = 99313037) B99313037
theorem B2147435 : Blo 952587 2147435 := bstep (se 1 (by rfl) ⟨1610576, by rfl⟩ : syracuseStep 2147435 = 3221153) B3221153
theorem B4081079 : Blo 952587 4081079 := bstep (se 1 (by rfl) ⟨3060809, by rfl⟩ : syracuseStep 4081079 = 6121619) B6121619
theorem B2147903 : Blo 952587 2147903 := bstep (se 1 (by rfl) ⟨1610927, by rfl⟩ : syracuseStep 2147903 = 3221855) B3221855
theorem B2148011 : Blo 952587 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B2148335 : Blo 952587 2148335 := bstep (se 1 (by rfl) ⟨1611251, by rfl⟩ : syracuseStep 2148335 = 3222503) B3222503
theorem B2148551 : Blo 952587 2148551 := bstep (se 1 (by rfl) ⟨1611413, by rfl⟩ : syracuseStep 2148551 = 3222827) B3222827
theorem B2148731 : Blo 952587 2148731 := bstep (se 1 (by rfl) ⟨1611548, by rfl⟩ : syracuseStep 2148731 = 3223097) B3223097
theorem B2149001 : Blo 952587 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B2149289 : Blo 952587 2149289 := bstep (se 2 (by rfl) ⟨805983, by rfl⟩ : syracuseStep 2149289 = 1611967) B1611967
theorem B1526779 : Blo 952587 1526779 := bstep (se 1 (by rfl) ⟨1145084, by rfl⟩ : syracuseStep 1526779 = 2290169) B2290169
theorem B4836347 : Blo 952587 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B12209201 : Blo 952587 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B2575975 : Blo 952587 2575975 := bstep (se 1 (by rfl) ⟨1931981, by rfl⟩ : syracuseStep 2575975 = 3863963) B3863963
theorem B2149991 : Blo 952587 2149991 := bstep (se 1 (by rfl) ⟨1612493, by rfl⟩ : syracuseStep 2149991 = 3224987) B3224987
theorem B1429487 : Blo 952587 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B1429499 : Blo 952587 1429499 := bstep (se 1 (by rfl) ⟨1072124, by rfl⟩ : syracuseStep 1429499 = 2144249) B2144249
theorem B1429559 : Blo 952587 1429559 := bstep (se 1 (by rfl) ⟨1072169, by rfl⟩ : syracuseStep 1429559 = 2144339) B2144339
theorem B2150495 : Blo 952587 2150495 := bstep (se 1 (by rfl) ⟨1612871, by rfl⟩ : syracuseStep 2150495 = 3225743) B3225743
theorem B1429607 : Blo 952587 1429607 := bstep (se 1 (by rfl) ⟨1072205, by rfl⟩ : syracuseStep 1429607 = 2144411) B2144411
theorem B1429679 : Blo 952587 1429679 := bstep (se 1 (by rfl) ⟨1072259, by rfl⟩ : syracuseStep 1429679 = 2144519) B2144519
theorem B2412787 : Blo 952587 2412787 := bstep (se 1 (by rfl) ⟨1809590, by rfl⟩ : syracuseStep 2412787 = 3619181) B3619181
theorem B6115571 : Blo 952587 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B1429883 : Blo 952587 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B7360895 : Blo 952587 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B24433163 : Blo 952587 24433163 := bstep (se 1 (by rfl) ⟨18324872, by rfl⟩ : syracuseStep 24433163 = 36649745) B36649745
theorem B1430153 : Blo 952587 1430153 := bstep (se 2 (by rfl) ⟨536307, by rfl⟩ : syracuseStep 1430153 = 1072615) B1072615
theorem B7754555 : Blo 952587 7754555 := bstep (se 1 (by rfl) ⟨5815916, by rfl⟩ : syracuseStep 7754555 = 11631833) B11631833
theorem B2151251 : Blo 952587 2151251 := bstep (se 1 (by rfl) ⟨1613438, by rfl⟩ : syracuseStep 2151251 = 3226877) B3226877
theorem B1430363 : Blo 952587 1430363 := bstep (se 1 (by rfl) ⟨1072772, by rfl⟩ : syracuseStep 1430363 = 2145545) B2145545
theorem B7263269 : Blo 952587 7263269 := bstep (se 4 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 7263269 = 1361863) B1361863
theorem B1430825 : Blo 952587 1430825 := bstep (se 2 (by rfl) ⟨536559, by rfl⟩ : syracuseStep 1430825 = 1073119) B1073119
theorem B2151791 : Blo 952587 2151791 := bstep (se 1 (by rfl) ⟨1613843, by rfl⟩ : syracuseStep 2151791 = 3227687) B3227687
theorem B2414063 : Blo 952587 2414063 := bstep (se 1 (by rfl) ⟨1810547, by rfl⟩ : syracuseStep 2414063 = 3621095) B3621095
theorem B1431023 : Blo 952587 1431023 := bstep (se 1 (by rfl) ⟨1073267, by rfl⟩ : syracuseStep 1431023 = 2146535) B2146535
theorem B2152223 : Blo 952587 2152223 := bstep (se 1 (by rfl) ⟨1614167, by rfl⟩ : syracuseStep 2152223 = 3228335) B3228335
theorem B2414407 : Blo 952587 2414407 := bstep (se 1 (by rfl) ⟨1810805, by rfl⟩ : syracuseStep 2414407 = 3621611) B3621611
theorem B1431419 : Blo 952587 1431419 := bstep (se 1 (by rfl) ⟨1073564, by rfl⟩ : syracuseStep 1431419 = 2147129) B2147129
theorem B1431455 : Blo 952587 1431455 := bstep (se 1 (by rfl) ⟨1073591, by rfl⟩ : syracuseStep 1431455 = 2147183) B2147183
theorem B9164897 : Blo 952587 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B1431689 : Blo 952587 1431689 := bstep (se 2 (by rfl) ⟨536883, by rfl⟩ : syracuseStep 1431689 = 1073767) B1073767
theorem B1431839 : Blo 952587 1431839 := bstep (se 1 (by rfl) ⟨1073879, by rfl⟩ : syracuseStep 1431839 = 2147759) B2147759
theorem B2415035 : Blo 952587 2415035 := bstep (se 1 (by rfl) ⟨1811276, by rfl⟩ : syracuseStep 2415035 = 3622553) B3622553
theorem B1432391 : Blo 952587 1432391 := bstep (se 1 (by rfl) ⟨1074293, by rfl⟩ : syracuseStep 1432391 = 2148587) B2148587
theorem B1072039 : Blo 952587 1072039 := bstep (se 1 (by rfl) ⟨804029, by rfl⟩ : syracuseStep 1072039 = 1608059) B1608059
theorem B4905947 : Blo 952587 4905947 := bstep (se 1 (by rfl) ⟨3679460, by rfl⟩ : syracuseStep 4905947 = 7358921) B7358921
theorem B1072219 : Blo 952587 1072219 := bstep (se 1 (by rfl) ⟨804164, by rfl⟩ : syracuseStep 1072219 = 1608329) B1608329
theorem B1433255 : Blo 952587 1433255 := bstep (se 1 (by rfl) ⟨1074941, by rfl⟩ : syracuseStep 1433255 = 2149883) B2149883
theorem B18341639 : Blo 952587 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B1433375 : Blo 952587 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B1433807 : Blo 952587 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B1073407 : Blo 952587 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B1433855 : Blo 952587 1433855 := bstep (se 1 (by rfl) ⟨1075391, by rfl⟩ : syracuseStep 1433855 = 2150783) B2150783
theorem B1073695 : Blo 952587 1073695 := bstep (se 1 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 1073695 = 1610543) B1610543
theorem B2482855 : Blo 952587 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B1434671 : Blo 952587 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B1074343 : Blo 952587 1074343 := bstep (se 1 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 1074343 = 1611515) B1611515
theorem B1434791 : Blo 952587 1434791 := bstep (se 1 (by rfl) ⟨1076093, by rfl⟩ : syracuseStep 1434791 = 2152187) B2152187
theorem B39216419 : Blo 952587 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B12248567 : Blo 952587 12248567 := bstep (se 1 (by rfl) ⟨9186425, by rfl⟩ : syracuseStep 12248567 = 18372851) B18372851
theorem B1075135 : Blo 952587 1075135 := bstep (se 1 (by rfl) ⟨806351, by rfl⟩ : syracuseStep 1075135 = 1612703) B1612703
theorem B4581355 : Blo 952587 4581355 := bstep (se 1 (by rfl) ⟨3436016, by rfl⟩ : syracuseStep 4581355 = 6872033) B6872033
theorem B6121595 : Blo 952587 6121595 := bstep (se 1 (by rfl) ⟨4591196, by rfl⟩ : syracuseStep 6121595 = 9182393) B9182393
theorem B1075423 : Blo 952587 1075423 := bstep (se 1 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 1075423 = 1613135) B1613135
theorem B2419247 : Blo 952587 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B2419895 : Blo 952587 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B23194957 : Blo 952587 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B2715731 : Blo 952587 2715731 := bstep (se 1 (by rfl) ⟨2036798, by rfl⟩ : syracuseStep 2715731 = 4073597) B4073597
theorem B2420999 : Blo 952587 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B3436825 : Blo 952587 3436825 := bstep (se 2 (by rfl) ⟨1288809, by rfl⟩ : syracuseStep 3436825 = 2577619) B2577619
theorem B15692167 : Blo 952587 15692167 := bstep (se 1 (by rfl) ⟨11769125, by rfl⟩ : syracuseStep 15692167 = 23538251) B23538251
theorem B2716573 : Blo 952587 2716573 := bstep (se 3 (by rfl) ⟨509357, by rfl⟩ : syracuseStep 2716573 = 1018715) B1018715
theorem B13038731 : Blo 952587 13038731 := bstep (se 1 (by rfl) ⟨9779048, by rfl⟩ : syracuseStep 13038731 = 19558097) B19558097
theorem B5797183 : Blo 952587 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B2291111 : Blo 952587 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B11597579 : Blo 952587 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B17397827 : Blo 952587 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B18381005 : Blo 952587 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B4127689 : Blo 952587 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B5438501 : Blo 952587 5438501 := bstep (se 4 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 5438501 = 1019719) B1019719
theorem B8158603 : Blo 952587 8158603 := bstep (se 1 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 8158603 = 12237905) B12237905
theorem B2653715 : Blo 952587 2653715 := bstep (se 1 (by rfl) ⟨1990286, by rfl⟩ : syracuseStep 2653715 = 3980573) B3980573
theorem B3866377 : Blo 952587 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B4587293 : Blo 952587 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B5439707 : Blo 952587 5439707 := bstep (se 1 (by rfl) ⟨4079780, by rfl⟩ : syracuseStep 5439707 = 8159561) B8159561
theorem B20676991 : Blo 952587 20676991 := bstep (se 1 (by rfl) ⟨15507743, by rfl⟩ : syracuseStep 20676991 = 31015487) B31015487
theorem B5439959 : Blo 952587 5439959 := bstep (se 1 (by rfl) ⟨4079969, by rfl⟩ : syracuseStep 5439959 = 8159939) B8159939
theorem B2720537 : Blo 952587 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B1573663 : Blo 952587 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B2720719 : Blo 952587 2720719 := bstep (se 1 (by rfl) ⟨2040539, by rfl⟩ : syracuseStep 2720719 = 4081079) B4081079
theorem B9177047 : Blo 952587 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B17434763 : Blo 952587 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B176556509 : Blo 952587 176556509 := bstep (se 3 (by rfl) ⟨33104345, by rfl⟩ : syracuseStep 176556509 = 66208691) B66208691
theorem B11602439 : Blo 952587 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B952991 : Blo 952587 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B952999 : Blo 952587 952999 := bstep (se 1 (by rfl) ⟨714749, by rfl⟩ : syracuseStep 952999 = 1429499) B1429499
theorem B953039 : Blo 952587 953039 := bstep (se 1 (by rfl) ⟨714779, by rfl⟩ : syracuseStep 953039 = 1429559) B1429559
theorem B953071 : Blo 952587 953071 := bstep (se 1 (by rfl) ⟨714803, by rfl⟩ : syracuseStep 953071 = 1429607) B1429607
theorem B953119 : Blo 952587 953119 := bstep (se 1 (by rfl) ⟨714839, by rfl⟩ : syracuseStep 953119 = 1429679) B1429679
theorem B953255 : Blo 952587 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B16288775 : Blo 952587 16288775 := bstep (se 1 (by rfl) ⟨12216581, by rfl⟩ : syracuseStep 16288775 = 24433163) B24433163
theorem B953435 : Blo 952587 953435 := bstep (se 1 (by rfl) ⟨715076, by rfl⟩ : syracuseStep 953435 = 1430153) B1430153
theorem B953575 : Blo 952587 953575 := bstep (se 1 (by rfl) ⟨715181, by rfl⟩ : syracuseStep 953575 = 1430363) B1430363
theorem B953883 : Blo 952587 953883 := bstep (se 1 (by rfl) ⟨715412, by rfl⟩ : syracuseStep 953883 = 1430825) B1430825
theorem B13241893 : Blo 952587 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B1609375 : Blo 952587 1609375 := bstep (se 1 (by rfl) ⟨1207031, by rfl⟩ : syracuseStep 1609375 = 2414063) B2414063
theorem B954015 : Blo 952587 954015 := bstep (se 1 (by rfl) ⟨715511, by rfl⟩ : syracuseStep 954015 = 1431023) B1431023
theorem B3215159 : Blo 952587 3215159 := bstep (se 1 (by rfl) ⟨2411369, by rfl⟩ : syracuseStep 3215159 = 4822739) B4822739
theorem B954279 : Blo 952587 954279 := bstep (se 1 (by rfl) ⟨715709, by rfl⟩ : syracuseStep 954279 = 1431419) B1431419
theorem B954303 : Blo 952587 954303 := bstep (se 1 (by rfl) ⟨715727, by rfl⟩ : syracuseStep 954303 = 1431455) B1431455
theorem B2035705 : Blo 952587 2035705 := bstep (se 2 (by rfl) ⟨763389, by rfl⟩ : syracuseStep 2035705 = 1526779) B1526779
theorem B954459 : Blo 952587 954459 := bstep (se 1 (by rfl) ⟨715844, by rfl⟩ : syracuseStep 954459 = 1431689) B1431689
theorem B954559 : Blo 952587 954559 := bstep (se 1 (by rfl) ⟨715919, by rfl⟩ : syracuseStep 954559 = 1431839) B1431839
theorem B1610023 : Blo 952587 1610023 := bstep (se 1 (by rfl) ⟨1207517, by rfl⟩ : syracuseStep 1610023 = 2415035) B2415035
theorem B11604343 : Blo 952587 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B5509583 : Blo 952587 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B954927 : Blo 952587 954927 := bstep (se 1 (by rfl) ⟨716195, by rfl⟩ : syracuseStep 954927 = 1432391) B1432391
theorem B10064681 : Blo 952587 10064681 := bstep (se 2 (by rfl) ⟨3774255, by rfl⟩ : syracuseStep 10064681 = 7548511) B7548511
theorem B3216239 : Blo 952587 3216239 := bstep (se 1 (by rfl) ⟨2412179, by rfl⟩ : syracuseStep 3216239 = 4824359) B4824359
theorem B10883969 : Blo 952587 10883969 := bstep (se 2 (by rfl) ⟨4081488, by rfl⟩ : syracuseStep 10883969 = 8162977) B8162977
theorem B3871631 : Blo 952587 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B955503 : Blo 952587 955503 := bstep (se 1 (by rfl) ⟨716627, by rfl⟩ : syracuseStep 955503 = 1433255) B1433255
theorem B12227759 : Blo 952587 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B955583 : Blo 952587 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B1840463 : Blo 952587 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B955871 : Blo 952587 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B955903 : Blo 952587 955903 := bstep (se 1 (by rfl) ⟨716927, by rfl⟩ : syracuseStep 955903 = 1433855) B1433855
theorem B23271047 : Blo 952587 23271047 := bstep (se 1 (by rfl) ⟨17453285, by rfl⟩ : syracuseStep 23271047 = 34906571) B34906571
theorem B3217049 : Blo 952587 3217049 := bstep (se 2 (by rfl) ⟨1206393, by rfl⟩ : syracuseStep 3217049 = 2412787) B2412787
theorem B13735817 : Blo 952587 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B956447 : Blo 952587 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B956527 : Blo 952587 956527 := bstep (se 1 (by rfl) ⟨717395, by rfl⟩ : syracuseStep 956527 = 1434791) B1434791
theorem B8165711 : Blo 952587 8165711 := bstep (se 1 (by rfl) ⟨6124283, by rfl⟩ : syracuseStep 8165711 = 12248567) B12248567
theorem B1448713 : Blo 952587 1448713 := bstep (se 2 (by rfl) ⟨543267, by rfl⟩ : syracuseStep 1448713 = 1086535) B1086535
theorem B1612831 : Blo 952587 1612831 := bstep (se 1 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 1612831 = 2419247) B2419247
theorem B4070827 : Blo 952587 4070827 := bstep (se 1 (by rfl) ⟨3053120, by rfl⟩ : syracuseStep 4070827 = 6106241) B6106241
theorem B1613263 : Blo 952587 1613263 := bstep (se 1 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 1613263 = 2419895) B2419895
theorem B3219209 : Blo 952587 3219209 := bstep (se 2 (by rfl) ⟨1207203, by rfl⟩ : syracuseStep 3219209 = 2414407) B2414407
theorem B1449959 : Blo 952587 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B1810487 : Blo 952587 1810487 := bstep (se 1 (by rfl) ⟨1357865, by rfl⟩ : syracuseStep 1810487 = 2715731) B2715731
theorem B1613999 : Blo 952587 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B8692487 : Blo 952587 8692487 := bstep (se 1 (by rfl) ⟨6519365, by rfl⟩ : syracuseStep 8692487 = 13038731) B13038731
theorem B7840889 : Blo 952587 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B3482911 : Blo 952587 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B12232781 : Blo 952587 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B1452251 : Blo 952587 1452251 := bstep (se 1 (by rfl) ⟨1089188, by rfl⟩ : syracuseStep 1452251 = 2178377) B2178377
theorem B5155169 : Blo 952587 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B9186119 : Blo 952587 9186119 := bstep (se 1 (by rfl) ⟨6889589, by rfl⟩ : syracuseStep 9186119 = 13779179) B13779179
theorem B4828409 : Blo 952587 4828409 := bstep (se 2 (by rfl) ⟨1810653, by rfl⟩ : syracuseStep 4828409 = 3621307) B3621307
theorem B3058991 : Blo 952587 3058991 := bstep (se 1 (by rfl) ⟨2294243, by rfl⟩ : syracuseStep 3058991 = 4588487) B4588487
theorem B1813843 : Blo 952587 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B4828571 : Blo 952587 4828571 := bstep (se 1 (by rfl) ⟨3621428, by rfl⟩ : syracuseStep 4828571 = 7242857) B7242857
theorem B3059579 : Blo 952587 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B1814815 : Blo 952587 1814815 := bstep (se 1 (by rfl) ⟨1361111, by rfl⟩ : syracuseStep 1814815 = 2722223) B2722223
theorem B3224231 : Blo 952587 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B8139467 : Blo 952587 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B4830191 : Blo 952587 4830191 := bstep (se 1 (by rfl) ⟨3622643, by rfl⟩ : syracuseStep 4830191 = 7245287) B7245287
theorem B6108473 : Blo 952587 6108473 := bstep (se 2 (by rfl) ⟨2290677, by rfl⟩ : syracuseStep 6108473 = 4581355) B4581355
theorem B4077047 : Blo 952587 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B5158525 : Blo 952587 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B2144123 : Blo 952587 2144123 := bstep (se 1 (by rfl) ⟨1608092, by rfl⟩ : syracuseStep 2144123 = 3216185) B3216185
theorem B2144393 : Blo 952587 2144393 := bstep (se 2 (by rfl) ⟨804147, by rfl⟩ : syracuseStep 2144393 = 1608295) B1608295
theorem B140950169 : Blo 952587 140950169 := bstep (se 2 (by rfl) ⟨52856313, by rfl⟩ : syracuseStep 140950169 = 105712627) B105712627
theorem B6109931 : Blo 952587 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B4078345 : Blo 952587 4078345 := bstep (se 2 (by rfl) ⟨1529379, by rfl⟩ : syracuseStep 4078345 = 3058759) B3058759
theorem B2145401 : Blo 952587 2145401 := bstep (se 2 (by rfl) ⟨804525, by rfl⟩ : syracuseStep 2145401 = 1609051) B1609051
theorem B1359175 : Blo 952587 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B5520905 : Blo 952587 5520905 := bstep (se 2 (by rfl) ⟨2070339, by rfl⟩ : syracuseStep 5520905 = 4140679) B4140679
theorem B13745963 : Blo 952587 13745963 := bstep (se 1 (by rfl) ⟨10309472, by rfl⟩ : syracuseStep 13745963 = 20618945) B20618945
theorem B4833107 : Blo 952587 4833107 := bstep (se 1 (by rfl) ⟨3624830, by rfl⟩ : syracuseStep 4833107 = 7249661) B7249661
theorem B20922889 : Blo 952587 20922889 := bstep (se 2 (by rfl) ⟨7846083, by rfl⟩ : syracuseStep 20922889 = 15692167) B15692167
theorem B3622097 : Blo 952587 3622097 := bstep (se 2 (by rfl) ⟨1358286, by rfl⟩ : syracuseStep 3622097 = 2716573) B2716573
theorem B2147687 : Blo 952587 2147687 := bstep (se 1 (by rfl) ⟨1610765, by rfl⟩ : syracuseStep 2147687 = 3221531) B3221531
theorem B4081063 : Blo 952587 4081063 := bstep (se 1 (by rfl) ⟨3060797, by rfl⟩ : syracuseStep 4081063 = 6121595) B6121595
theorem B2147795 : Blo 952587 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B2148065 : Blo 952587 2148065 := bstep (se 2 (by rfl) ⟨805524, by rfl⟩ : syracuseStep 2148065 = 1611049) B1611049
theorem B9816335 : Blo 952587 9816335 := bstep (se 1 (by rfl) ⟨7362251, by rfl⟩ : syracuseStep 9816335 = 14724503) B14724503
theorem B2148857 : Blo 952587 2148857 := bstep (se 2 (by rfl) ⟨805821, by rfl⟩ : syracuseStep 2148857 = 1611643) B1611643
theorem B2148947 : Blo 952587 2148947 := bstep (se 1 (by rfl) ⟨1611710, by rfl⟩ : syracuseStep 2148947 = 3223421) B3223421
theorem B2149127 : Blo 952587 2149127 := bstep (se 1 (by rfl) ⟨1611845, by rfl⟩ : syracuseStep 2149127 = 3223691) B3223691
theorem B2149217 : Blo 952587 2149217 := bstep (se 2 (by rfl) ⟨805956, by rfl⟩ : syracuseStep 2149217 = 1611913) B1611913
theorem B2411471 : Blo 952587 2411471 := bstep (se 1 (by rfl) ⟨1808603, by rfl⟩ : syracuseStep 2411471 = 3617207) B3617207
theorem B18337175 : Blo 952587 18337175 := bstep (se 1 (by rfl) ⟨13752881, by rfl⟩ : syracuseStep 18337175 = 27505763) B27505763
theorem B1429103 : Blo 952587 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B1527407 : Blo 952587 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B1429175 : Blo 952587 1429175 := bstep (se 1 (by rfl) ⟨1071881, by rfl⟩ : syracuseStep 1429175 = 2143763) B2143763
theorem B1429223 : Blo 952587 1429223 := bstep (se 1 (by rfl) ⟨1071917, by rfl⟩ : syracuseStep 1429223 = 2143835) B2143835
theorem B2150135 : Blo 952587 2150135 := bstep (se 1 (by rfl) ⟨1612601, by rfl⟩ : syracuseStep 2150135 = 3225203) B3225203
theorem B2150153 : Blo 952587 2150153 := bstep (se 2 (by rfl) ⟨806307, by rfl⟩ : syracuseStep 2150153 = 1612615) B1612615
theorem B2150207 : Blo 952587 2150207 := bstep (se 1 (by rfl) ⟨1612655, by rfl⟩ : syracuseStep 2150207 = 3225311) B3225311
theorem B1429385 : Blo 952587 1429385 := bstep (se 2 (by rfl) ⟨536019, by rfl⟩ : syracuseStep 1429385 = 1072039) B1072039
theorem B2150315 : Blo 952587 2150315 := bstep (se 1 (by rfl) ⟨1612736, by rfl⟩ : syracuseStep 2150315 = 3225473) B3225473
theorem B1429625 : Blo 952587 1429625 := bstep (se 2 (by rfl) ⟨536109, by rfl⟩ : syracuseStep 1429625 = 1072219) B1072219
theorem B1429631 : Blo 952587 1429631 := bstep (se 1 (by rfl) ⟨1072223, by rfl⟩ : syracuseStep 1429631 = 2144447) B2144447
theorem B2150675 : Blo 952587 2150675 := bstep (se 1 (by rfl) ⟨1613006, by rfl⟩ : syracuseStep 2150675 = 3226013) B3226013
theorem B2150855 : Blo 952587 2150855 := bstep (se 1 (by rfl) ⟨1613141, by rfl⟩ : syracuseStep 2150855 = 3226283) B3226283
theorem B7262783 : Blo 952587 7262783 := bstep (se 1 (by rfl) ⟨5447087, by rfl⟩ : syracuseStep 7262783 = 10894175) B10894175
theorem B3625667 : Blo 952587 3625667 := bstep (se 1 (by rfl) ⟨2719250, by rfl⟩ : syracuseStep 3625667 = 5438501) B5438501
theorem B2151143 : Blo 952587 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B2151215 : Blo 952587 2151215 := bstep (se 1 (by rfl) ⟨1613411, by rfl⟩ : syracuseStep 2151215 = 3226823) B3226823
theorem B2151305 : Blo 952587 2151305 := bstep (se 2 (by rfl) ⟨806739, by rfl⟩ : syracuseStep 2151305 = 1613479) B1613479
theorem B9163667 : Blo 952587 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B1430471 : Blo 952587 1430471 := bstep (se 1 (by rfl) ⟨1072853, by rfl⟩ : syracuseStep 1430471 = 2145707) B2145707
theorem B1430495 : Blo 952587 1430495 := bstep (se 1 (by rfl) ⟨1072871, by rfl⟩ : syracuseStep 1430495 = 2145743) B2145743
theorem B5428295 : Blo 952587 5428295 := bstep (se 1 (by rfl) ⟨4071221, by rfl⟩ : syracuseStep 5428295 = 8142443) B8142443
theorem B1430831 : Blo 952587 1430831 := bstep (se 1 (by rfl) ⟨1073123, by rfl⟩ : syracuseStep 1430831 = 2146247) B2146247
theorem B3528047 : Blo 952587 3528047 := bstep (se 1 (by rfl) ⟨2646035, by rfl⟩ : syracuseStep 3528047 = 5292071) B5292071
theorem B1431035 : Blo 952587 1431035 := bstep (se 1 (by rfl) ⟨1073276, by rfl⟩ : syracuseStep 1431035 = 2146553) B2146553
theorem B1431071 : Blo 952587 1431071 := bstep (se 1 (by rfl) ⟨1073303, by rfl⟩ : syracuseStep 1431071 = 2146607) B2146607
theorem B1431209 : Blo 952587 1431209 := bstep (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) B1073407
theorem B1431215 : Blo 952587 1431215 := bstep (se 1 (by rfl) ⟨1073411, by rfl⟩ : syracuseStep 1431215 = 2146823) B2146823
theorem B1431335 : Blo 952587 1431335 := bstep (se 1 (by rfl) ⟨1073501, by rfl⟩ : syracuseStep 1431335 = 2147003) B2147003
theorem B16734035 : Blo 952587 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B1431593 : Blo 952587 1431593 := bstep (se 2 (by rfl) ⟨536847, by rfl⟩ : syracuseStep 1431593 = 1073695) B1073695
theorem B1431623 : Blo 952587 1431623 := bstep (se 1 (by rfl) ⟨1073717, by rfl⟩ : syracuseStep 1431623 = 2147435) B2147435
theorem B1431935 : Blo 952587 1431935 := bstep (se 1 (by rfl) ⟨1073951, by rfl⟩ : syracuseStep 1431935 = 2147903) B2147903
theorem B1432007 : Blo 952587 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B38230625 : Blo 952587 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B1432223 : Blo 952587 1432223 := bstep (se 1 (by rfl) ⟨1074167, by rfl⟩ : syracuseStep 1432223 = 2148335) B2148335
theorem B1432367 : Blo 952587 1432367 := bstep (se 1 (by rfl) ⟨1074275, by rfl⟩ : syracuseStep 1432367 = 2148551) B2148551
theorem B1432457 : Blo 952587 1432457 := bstep (se 2 (by rfl) ⟨537171, by rfl⟩ : syracuseStep 1432457 = 1074343) B1074343
theorem B1432487 : Blo 952587 1432487 := bstep (se 1 (by rfl) ⟨1074365, by rfl⟩ : syracuseStep 1432487 = 2148731) B2148731
theorem B1432667 : Blo 952587 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B1432859 : Blo 952587 1432859 := bstep (se 1 (by rfl) ⟨1074644, by rfl⟩ : syracuseStep 1432859 = 2149289) B2149289
theorem B2579791 : Blo 952587 2579791 := bstep (se 1 (by rfl) ⟨1934843, by rfl⟩ : syracuseStep 2579791 = 3869687) B3869687
theorem B3628415 : Blo 952587 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B6119135 : Blo 952587 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B1433327 : Blo 952587 1433327 := bstep (se 1 (by rfl) ⟨1074995, by rfl⟩ : syracuseStep 1433327 = 2149991) B2149991
theorem B8150813 : Blo 952587 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B1433513 : Blo 952587 1433513 := bstep (se 2 (by rfl) ⟨537567, by rfl⟩ : syracuseStep 1433513 = 1075135) B1075135
theorem B1433663 : Blo 952587 1433663 := bstep (se 1 (by rfl) ⟨1075247, by rfl⟩ : syracuseStep 1433663 = 2150495) B2150495
theorem B15687827 : Blo 952587 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B4841693 : Blo 952587 4841693 := bstep (se 3 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 4841693 = 1815635) B1815635
theorem B4907263 : Blo 952587 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B1433897 : Blo 952587 1433897 := bstep (se 2 (by rfl) ⟨537711, by rfl⟩ : syracuseStep 1433897 = 1075423) B1075423
theorem B5169703 : Blo 952587 5169703 := bstep (se 1 (by rfl) ⟨3877277, by rfl⟩ : syracuseStep 5169703 = 7754555) B7754555
theorem B1434167 : Blo 952587 1434167 := bstep (se 1 (by rfl) ⟨1075625, by rfl⟩ : syracuseStep 1434167 = 2151251) B2151251
theorem B4842179 : Blo 952587 4842179 := bstep (se 1 (by rfl) ⟨3631634, by rfl⟩ : syracuseStep 4842179 = 7263269) B7263269
theorem B1434527 : Blo 952587 1434527 := bstep (se 1 (by rfl) ⟨1075895, by rfl⟩ : syracuseStep 1434527 = 2151791) B2151791
theorem B2581607 : Blo 952587 2581607 := bstep (se 1 (by rfl) ⟨1936205, by rfl⟩ : syracuseStep 2581607 = 3872411) B3872411
theorem B6120593 : Blo 952587 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B1434815 : Blo 952587 1434815 := bstep (se 1 (by rfl) ⟨1076111, by rfl⟩ : syracuseStep 1434815 = 2152223) B2152223
theorem B30926609 : Blo 952587 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B2418569 : Blo 952587 2418569 := bstep (se 2 (by rfl) ⟨906963, by rfl⟩ : syracuseStep 2418569 = 1813927) B1813927
theorem B3270631 : Blo 952587 3270631 := bstep (se 1 (by rfl) ⟨2452973, by rfl⟩ : syracuseStep 3270631 = 4905947) B4905947
theorem B3434633 : Blo 952587 3434633 := bstep (se 2 (by rfl) ⟨1287987, by rfl⟩ : syracuseStep 3434633 = 2575975) B2575975
theorem B2714249 : Blo 952587 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B3631787 : Blo 952587 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B1207163 : Blo 952587 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B4582433 : Blo 952587 4582433 := bstep (se 2 (by rfl) ⟨1718412, by rfl⟩ : syracuseStep 4582433 = 3436825) B3436825
theorem B1207487 : Blo 952587 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B26144279 : Blo 952587 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B1208191 : Blo 952587 1208191 := bstep (se 1 (by rfl) ⟨906143, by rfl⟩ : syracuseStep 1208191 = 1812287) B1812287
theorem B7729577 : Blo 952587 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B2421161 : Blo 952587 2421161 := bstep (se 2 (by rfl) ⟨907935, by rfl⟩ : syracuseStep 2421161 = 1815871) B1815871
theorem B2585695 : Blo 952587 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B7731719 : Blo 952587 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B5503585 : Blo 952587 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B11598551 : Blo 952587 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B12254003 : Blo 952587 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B5799059 : Blo 952587 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B10878137 : Blo 952587 10878137 := bstep (se 2 (by rfl) ⟨4079301, by rfl⟩ : syracuseStep 10878137 = 8158603) B8158603
theorem B13073761 : Blo 952587 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B1769143 : Blo 952587 1769143 := bstep (se 1 (by rfl) ⟨1326857, by rfl⟩ : syracuseStep 1769143 = 2653715) B2653715
theorem B2098217 : Blo 952587 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B117704339 : Blo 952587 117704339 := bstep (se 1 (by rfl) ⟨88278254, by rfl⟩ : syracuseStep 117704339 = 176556509) B176556509
theorem B7734959 : Blo 952587 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B5441417 : Blo 952587 5441417 := bstep (se 2 (by rfl) ⟨2040531, by rfl⟩ : syracuseStep 5441417 = 4081063) B4081063
theorem B1607647 : Blo 952587 1607647 := bstep (se 1 (by rfl) ⟨1205735, by rfl⟩ : syracuseStep 1607647 = 2411471) B2411471
theorem B12224783 : Blo 952587 12224783 := bstep (se 1 (by rfl) ⟨9168587, by rfl⟩ : syracuseStep 12224783 = 18337175) B18337175
theorem B10324349 : Blo 952587 10324349 := bstep (se 3 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 10324349 = 3871631) B3871631
theorem B952735 : Blo 952587 952735 := bstep (se 1 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 952735 = 1429103) B1429103
theorem B1018271 : Blo 952587 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B952783 : Blo 952587 952783 := bstep (se 1 (by rfl) ⟨714587, by rfl⟩ : syracuseStep 952783 = 1429175) B1429175
theorem B952815 : Blo 952587 952815 := bstep (se 1 (by rfl) ⟨714611, by rfl⟩ : syracuseStep 952815 = 1429223) B1429223
theorem B952923 : Blo 952587 952923 := bstep (se 1 (by rfl) ⟨714692, by rfl⟩ : syracuseStep 952923 = 1429385) B1429385
theorem B4360841 : Blo 952587 4360841 := bstep (se 2 (by rfl) ⟨1635315, by rfl⟩ : syracuseStep 4360841 = 3270631) B3270631
theorem B953083 : Blo 952587 953083 := bstep (se 1 (by rfl) ⟨714812, by rfl⟩ : syracuseStep 953083 = 1429625) B1429625
theorem B953087 : Blo 952587 953087 := bstep (se 1 (by rfl) ⟨714815, by rfl⟩ : syracuseStep 953087 = 1429631) B1429631
theorem B3673055 : Blo 952587 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B953647 : Blo 952587 953647 := bstep (se 1 (by rfl) ⟨715235, by rfl⟩ : syracuseStep 953647 = 1430471) B1430471
theorem B953663 : Blo 952587 953663 := bstep (se 1 (by rfl) ⟨715247, by rfl⟩ : syracuseStep 953663 = 1430495) B1430495
theorem B19631605 : Blo 952587 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B953887 : Blo 952587 953887 := bstep (se 1 (by rfl) ⟨715415, by rfl⟩ : syracuseStep 953887 = 1430831) B1430831
theorem B9408125 : Blo 952587 9408125 := bstep (se 3 (by rfl) ⟨1764023, by rfl⟩ : syracuseStep 9408125 = 3528047) B3528047
theorem B954023 : Blo 952587 954023 := bstep (se 1 (by rfl) ⟨715517, by rfl⟩ : syracuseStep 954023 = 1431035) B1431035
theorem B954047 : Blo 952587 954047 := bstep (se 1 (by rfl) ⟨715535, by rfl⟩ : syracuseStep 954047 = 1431071) B1431071
theorem B954139 : Blo 952587 954139 := bstep (se 1 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 954139 = 1431209) B1431209
theorem B954143 : Blo 952587 954143 := bstep (se 1 (by rfl) ⟨715607, by rfl⟩ : syracuseStep 954143 = 1431215) B1431215
theorem B954223 : Blo 952587 954223 := bstep (se 1 (by rfl) ⟨715667, by rfl⟩ : syracuseStep 954223 = 1431335) B1431335
theorem B954395 : Blo 952587 954395 := bstep (se 1 (by rfl) ⟨715796, by rfl⟩ : syracuseStep 954395 = 1431593) B1431593
theorem B954415 : Blo 952587 954415 := bstep (se 1 (by rfl) ⟨715811, by rfl⟩ : syracuseStep 954415 = 1431623) B1431623
theorem B5443807 : Blo 952587 5443807 := bstep (se 1 (by rfl) ⟨4082855, by rfl⟩ : syracuseStep 5443807 = 8165711) B8165711
theorem B954623 : Blo 952587 954623 := bstep (se 1 (by rfl) ⟨715967, by rfl⟩ : syracuseStep 954623 = 1431935) B1431935
theorem B954671 : Blo 952587 954671 := bstep (se 1 (by rfl) ⟨716003, by rfl⟩ : syracuseStep 954671 = 1432007) B1432007
theorem B954815 : Blo 952587 954815 := bstep (se 1 (by rfl) ⟨716111, by rfl⟩ : syracuseStep 954815 = 1432223) B1432223
theorem B954911 : Blo 952587 954911 := bstep (se 1 (by rfl) ⟨716183, by rfl⟩ : syracuseStep 954911 = 1432367) B1432367
theorem B954971 : Blo 952587 954971 := bstep (se 1 (by rfl) ⟨716228, by rfl⟩ : syracuseStep 954971 = 1432457) B1432457
theorem B954991 : Blo 952587 954991 := bstep (se 1 (by rfl) ⟨716243, by rfl⟩ : syracuseStep 954991 = 1432487) B1432487
theorem B955111 : Blo 952587 955111 := bstep (se 1 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 955111 = 1432667) B1432667
theorem B955239 : Blo 952587 955239 := bstep (se 1 (by rfl) ⟨716429, by rfl⟩ : syracuseStep 955239 = 1432859) B1432859
theorem B955551 : Blo 952587 955551 := bstep (se 1 (by rfl) ⟨716663, by rfl⟩ : syracuseStep 955551 = 1433327) B1433327
theorem B1610921 : Blo 952587 1610921 := bstep (se 2 (by rfl) ⟨604095, by rfl⟩ : syracuseStep 1610921 = 1208191) B1208191
theorem B955675 : Blo 952587 955675 := bstep (se 1 (by rfl) ⟨716756, by rfl⟩ : syracuseStep 955675 = 1433513) B1433513
theorem B955775 : Blo 952587 955775 := bstep (se 1 (by rfl) ⟨716831, by rfl⟩ : syracuseStep 955775 = 1433663) B1433663
theorem B10458551 : Blo 952587 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B955931 : Blo 952587 955931 := bstep (se 1 (by rfl) ⟨716948, by rfl⟩ : syracuseStep 955931 = 1433897) B1433897
theorem B956111 : Blo 952587 956111 := bstep (se 1 (by rfl) ⟨717083, by rfl⟩ : syracuseStep 956111 = 1434167) B1434167
theorem B15472457 : Blo 952587 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B3872669 : Blo 952587 3872669 := bstep (se 3 (by rfl) ⟨726125, by rfl⟩ : syracuseStep 3872669 = 1452251) B1452251
theorem B956351 : Blo 952587 956351 := bstep (se 1 (by rfl) ⟨717263, by rfl⟩ : syracuseStep 956351 = 1434527) B1434527
theorem B956543 : Blo 952587 956543 := bstep (se 1 (by rfl) ⟨717407, by rfl⟩ : syracuseStep 956543 = 1434815) B1434815
theorem B20617739 : Blo 952587 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B1612379 : Blo 952587 1612379 := bstep (se 1 (by rfl) ⟨1209284, by rfl⟩ : syracuseStep 1612379 = 2418569) B2418569
theorem B3447593 : Blo 952587 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B16293149 : Blo 952587 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B3054955 : Blo 952587 3054955 := bstep (se 1 (by rfl) ⟨2291216, by rfl⟩ : syracuseStep 3054955 = 4582433) B4582433
theorem B3218939 : Blo 952587 3218939 := bstep (se 1 (by rfl) ⟨2414204, by rfl⟩ : syracuseStep 3218939 = 4828409) B4828409
theorem B2039327 : Blo 952587 2039327 := bstep (se 1 (by rfl) ⟨1529495, by rfl⟩ : syracuseStep 2039327 = 3058991) B3058991
theorem B3219047 : Blo 952587 3219047 := bstep (se 1 (by rfl) ⟨2414285, by rfl⟩ : syracuseStep 3219047 = 4828571) B4828571
theorem B3219101 : Blo 952587 3219101 := bstep (se 3 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 3219101 = 1207163) B1207163
theorem B5153051 : Blo 952587 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B1614107 : Blo 952587 1614107 := bstep (se 1 (by rfl) ⟨1210580, by rfl⟩ : syracuseStep 1614107 = 2421161) B2421161
theorem B3219965 : Blo 952587 3219965 := bstep (se 3 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 3219965 = 1207487) B1207487
theorem B3220127 : Blo 952587 3220127 := bstep (se 1 (by rfl) ⟨2415095, by rfl⟩ : syracuseStep 3220127 = 4830191) B4830191
theorem B4072315 : Blo 952587 4072315 := bstep (se 1 (by rfl) ⟨3054236, by rfl⟩ : syracuseStep 4072315 = 6108473) B6108473
theorem B5154479 : Blo 952587 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B1812233 : Blo 952587 1812233 := bstep (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) B1359175
theorem B8169335 : Blo 952587 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B7252091 : Blo 952587 7252091 := bstep (se 1 (by rfl) ⟨5439068, by rfl⟩ : syracuseStep 7252091 = 10878137) B10878137
theorem B3680603 : Blo 952587 3680603 := bstep (se 1 (by rfl) ⟨2760452, by rfl⟩ : syracuseStep 3680603 = 5520905) B5520905
theorem B3222071 : Blo 952587 3222071 := bstep (se 1 (by rfl) ⟨2416553, by rfl⟩ : syracuseStep 3222071 = 4833107) B4833107
theorem B27569321 : Blo 952587 27569321 := bstep (se 2 (by rfl) ⟨10338495, by rfl⟩ : syracuseStep 27569321 = 20676991) B20676991
theorem B1813691 : Blo 952587 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B27897185 : Blo 952587 27897185 := bstep (se 2 (by rfl) ⟨10461444, by rfl⟩ : syracuseStep 27897185 = 20922889) B20922889
theorem B6892937 : Blo 952587 6892937 := bstep (se 2 (by rfl) ⟨2584851, by rfl⟩ : syracuseStep 6892937 = 5169703) B5169703
theorem B10859183 : Blo 952587 10859183 := bstep (se 1 (by rfl) ⟨8144387, by rfl⟩ : syracuseStep 10859183 = 16288775) B16288775
theorem B2143439 : Blo 952587 2143439 := bstep (se 1 (by rfl) ⟨1607579, by rfl⟩ : syracuseStep 2143439 = 3215159) B3215159
theorem B2144159 : Blo 952587 2144159 := bstep (se 1 (by rfl) ⟨1608119, by rfl⟩ : syracuseStep 2144159 = 3216239) B3216239
theorem B7255979 : Blo 952587 7255979 := bstep (se 1 (by rfl) ⟨5441984, by rfl⟩ : syracuseStep 7255979 = 10883969) B10883969
theorem B6109111 : Blo 952587 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B3618863 : Blo 952587 3618863 := bstep (se 1 (by rfl) ⟨2714147, by rfl⟩ : syracuseStep 3618863 = 5428295) B5428295
theorem B15514031 : Blo 952587 15514031 := bstep (se 1 (by rfl) ⟨11635523, by rfl⟩ : syracuseStep 15514031 = 23271047) B23271047
theorem B2144699 : Blo 952587 2144699 := bstep (se 1 (by rfl) ⟨1608524, by rfl⟩ : syracuseStep 2144699 = 3217049) B3217049
theorem B11156023 : Blo 952587 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B9157211 : Blo 952587 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B2145833 : Blo 952587 2145833 := bstep (se 2 (by rfl) ⟨804687, by rfl⟩ : syracuseStep 2145833 = 1609375) B1609375
theorem B4079423 : Blo 952587 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B2146139 : Blo 952587 2146139 := bstep (se 1 (by rfl) ⟨1609604, by rfl⟩ : syracuseStep 2146139 = 3219209) B3219209
theorem B3227795 : Blo 952587 3227795 := bstep (se 1 (by rfl) ⟨2420846, by rfl⟩ : syracuseStep 3227795 = 4841693) B4841693
theorem B2146697 : Blo 952587 2146697 := bstep (se 2 (by rfl) ⟨805011, by rfl⟩ : syracuseStep 2146697 = 1610023) B1610023
theorem B3228119 : Blo 952587 3228119 := bstep (se 1 (by rfl) ⟨2421089, by rfl⟩ : syracuseStep 3228119 = 4842179) B4842179
theorem B1721071 : Blo 952587 1721071 := bstep (se 1 (by rfl) ⟨1290803, by rfl⟩ : syracuseStep 1721071 = 2581607) B2581607
theorem B5227259 : Blo 952587 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B4080395 : Blo 952587 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B13747117 : Blo 952587 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B2149487 : Blo 952587 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B5426311 : Blo 952587 5426311 := bstep (se 1 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 5426311 = 8139467) B8139467
theorem B1429415 : Blo 952587 1429415 := bstep (se 1 (by rfl) ⟨1072061, by rfl⟩ : syracuseStep 1429415 = 2144123) B2144123
theorem B2150441 : Blo 952587 2150441 := bstep (se 2 (by rfl) ⟨806415, by rfl⟩ : syracuseStep 2150441 = 1612831) B1612831
theorem B1429595 : Blo 952587 1429595 := bstep (se 1 (by rfl) ⟨1072196, by rfl⟩ : syracuseStep 1429595 = 2144393) B2144393
theorem B93966779 : Blo 952587 93966779 := bstep (se 1 (by rfl) ⟨70475084, by rfl⟩ : syracuseStep 93966779 = 140950169) B140950169
theorem B5427769 : Blo 952587 5427769 := bstep (se 2 (by rfl) ⟨2035413, by rfl⟩ : syracuseStep 5427769 = 4070827) B4070827
theorem B2151017 : Blo 952587 2151017 := bstep (se 2 (by rfl) ⟨806631, by rfl⟩ : syracuseStep 2151017 = 1613263) B1613263
theorem B1430267 : Blo 952587 1430267 := bstep (se 1 (by rfl) ⟨1072700, by rfl⟩ : syracuseStep 1430267 = 2145401) B2145401
theorem B9163975 : Blo 952587 9163975 := bstep (se 1 (by rfl) ⟨6872981, by rfl⟩ : syracuseStep 9163975 = 13745963) B13745963
theorem B3626471 : Blo 952587 3626471 := bstep (se 1 (by rfl) ⟨2719853, by rfl⟩ : syracuseStep 3626471 = 5439707) B5439707
theorem B3626639 : Blo 952587 3626639 := bstep (se 1 (by rfl) ⟨2719979, by rfl⟩ : syracuseStep 3626639 = 5439959) B5439959
theorem B6543017 : Blo 952587 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B2414731 : Blo 952587 2414731 := bstep (se 1 (by rfl) ⟨1811048, by rfl⟩ : syracuseStep 2414731 = 3622097) B3622097
theorem B1431791 : Blo 952587 1431791 := bstep (se 1 (by rfl) ⟨1073843, by rfl⟩ : syracuseStep 1431791 = 2147687) B2147687
theorem B1431863 : Blo 952587 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B1432043 : Blo 952587 1432043 := bstep (se 1 (by rfl) ⟨1074032, by rfl⟩ : syracuseStep 1432043 = 2148065) B2148065
theorem B3627625 : Blo 952587 3627625 := bstep (se 2 (by rfl) ⟨1360359, by rfl⟩ : syracuseStep 3627625 = 2720719) B2720719
theorem B6118031 : Blo 952587 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B11623175 : Blo 952587 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B6544223 : Blo 952587 6544223 := bstep (se 1 (by rfl) ⟨4908167, by rfl⟩ : syracuseStep 6544223 = 9816335) B9816335
theorem B1432571 : Blo 952587 1432571 := bstep (se 1 (by rfl) ⟨1074428, by rfl⟩ : syracuseStep 1432571 = 2148857) B2148857
theorem B4643881 : Blo 952587 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B1432631 : Blo 952587 1432631 := bstep (se 1 (by rfl) ⟨1074473, by rfl⟩ : syracuseStep 1432631 = 2148947) B2148947
theorem B1432751 : Blo 952587 1432751 := bstep (se 1 (by rfl) ⟨1074563, by rfl⟩ : syracuseStep 1432751 = 2149127) B2149127
theorem B1432811 : Blo 952587 1432811 := bstep (se 1 (by rfl) ⟨1074608, by rfl⟩ : syracuseStep 1432811 = 2149217) B2149217
theorem B1433423 : Blo 952587 1433423 := bstep (se 1 (by rfl) ⟨1075067, by rfl⟩ : syracuseStep 1433423 = 2150135) B2150135
theorem B1433435 : Blo 952587 1433435 := bstep (se 1 (by rfl) ⟨1075076, by rfl⟩ : syracuseStep 1433435 = 2150153) B2150153
theorem B1433471 : Blo 952587 1433471 := bstep (se 1 (by rfl) ⟨1075103, by rfl⟩ : syracuseStep 1433471 = 2150207) B2150207
theorem B1433543 : Blo 952587 1433543 := bstep (se 1 (by rfl) ⟨1075157, by rfl⟩ : syracuseStep 1433543 = 2150315) B2150315
theorem B1433783 : Blo 952587 1433783 := bstep (se 1 (by rfl) ⟨1075337, by rfl⟩ : syracuseStep 1433783 = 2150675) B2150675
theorem B1433903 : Blo 952587 1433903 := bstep (se 1 (by rfl) ⟨1075427, by rfl⟩ : syracuseStep 1433903 = 2150855) B2150855
theorem B4841855 : Blo 952587 4841855 := bstep (se 1 (by rfl) ⟨3631391, by rfl⟩ : syracuseStep 4841855 = 7262783) B7262783
theorem B2417111 : Blo 952587 2417111 := bstep (se 1 (by rfl) ⟨1812833, by rfl⟩ : syracuseStep 2417111 = 3625667) B3625667
theorem B1434095 : Blo 952587 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B6709787 : Blo 952587 6709787 := bstep (se 1 (by rfl) ⟨5032340, by rfl⟩ : syracuseStep 6709787 = 10064681) B10064681
theorem B1434143 : Blo 952587 1434143 := bstep (se 1 (by rfl) ⟨1075607, by rfl⟩ : syracuseStep 1434143 = 2151215) B2151215
theorem B1434203 : Blo 952587 1434203 := bstep (se 1 (by rfl) ⟨1075652, by rfl⟩ : syracuseStep 1434203 = 2151305) B2151305
theorem B8151839 : Blo 952587 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B25487083 : Blo 952587 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B2418457 : Blo 952587 2418457 := bstep (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) B1813843
theorem B17655857 : Blo 952587 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B2418943 : Blo 952587 2418943 := bstep (se 1 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 2418943 = 3628415) B3628415
theorem B5433875 : Blo 952587 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B2714273 : Blo 952587 2714273 := bstep (se 2 (by rfl) ⟨1017852, by rfl⟩ : syracuseStep 2714273 = 2035705) B2035705
theorem B1206991 : Blo 952587 1206991 := bstep (se 1 (by rfl) ⟨905243, by rfl⟩ : syracuseStep 1206991 = 1810487) B1810487
theorem B1075999 : Blo 952587 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B2419753 : Blo 952587 2419753 := bstep (se 2 (by rfl) ⟨907407, by rfl⟩ : syracuseStep 2419753 = 1814815) B1814815
theorem B5794991 : Blo 952587 5794991 := bstep (se 1 (by rfl) ⟨4346243, by rfl⟩ : syracuseStep 5794991 = 8692487) B8692487
theorem B8155187 : Blo 952587 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B2289755 : Blo 952587 2289755 := bstep (se 1 (by rfl) ⟨1717316, by rfl⟩ : syracuseStep 2289755 = 3434633) B3434633
theorem B7237997 : Blo 952587 7237997 := bstep (se 3 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 7237997 = 2714249) B2714249
theorem B2421191 : Blo 952587 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B6124079 : Blo 952587 6124079 := bstep (se 1 (by rfl) ⟨4593059, by rfl⟩ : syracuseStep 6124079 = 9186119) B9186119
theorem B6878033 : Blo 952587 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B17429519 : Blo 952587 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B7338113 : Blo 952587 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B2718031 : Blo 952587 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B1931617 : Blo 952587 1931617 := bstep (se 2 (by rfl) ⟨724356, by rfl⟩ : syracuseStep 1931617 = 1448713) B1448713
theorem B5437793 : Blo 952587 5437793 := bstep (se 2 (by rfl) ⟨2039172, by rfl⟩ : syracuseStep 5437793 = 4078345) B4078345
theorem B3439721 : Blo 952587 3439721 := bstep (se 2 (by rfl) ⟨1289895, by rfl⟩ : syracuseStep 3439721 = 2579791) B2579791
theorem B17431681 : Blo 952587 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B7732367 : Blo 952587 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B3866039 : Blo 952587 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B2358857 : Blo 952587 2358857 := bstep (se 2 (by rfl) ⟨884571, by rfl⟩ : syracuseStep 2358857 = 1769143) B1769143
theorem B8158877 : Blo 952587 8158877 := bstep (se 3 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 8158877 = 3059579) B3059579
theorem B3866557 : Blo 952587 3866557 := bstep (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) B1449959
theorem B6882899 : Blo 952587 6882899 := bstep (se 1 (by rfl) ⟨5162174, by rfl⟩ : syracuseStep 6882899 = 10324349) B10324349
theorem B10881053 : Blo 952587 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B33982777 : Blo 952587 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B952943 : Blo 952587 952943 := bstep (se 1 (by rfl) ⟨714707, by rfl⟩ : syracuseStep 952943 = 1429415) B1429415
theorem B953063 : Blo 952587 953063 := bstep (se 1 (by rfl) ⟨714797, by rfl⟩ : syracuseStep 953063 = 1429595) B1429595
theorem B953511 : Blo 952587 953511 := bstep (se 1 (by rfl) ⟨715133, by rfl⟩ : syracuseStep 953511 = 1430267) B1430267
theorem B1609321 : Blo 952587 1609321 := bstep (se 2 (by rfl) ⟨603495, by rfl⟩ : syracuseStep 1609321 = 1206991) B1206991
theorem B4362011 : Blo 952587 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B9179045 : Blo 952587 9179045 := bstep (se 4 (by rfl) ⟨860535, by rfl⟩ : syracuseStep 9179045 = 1721071) B1721071
theorem B954527 : Blo 952587 954527 := bstep (se 1 (by rfl) ⟨715895, by rfl⟩ : syracuseStep 954527 = 1431791) B1431791
theorem B954575 : Blo 952587 954575 := bstep (se 1 (by rfl) ⟨715931, by rfl⟩ : syracuseStep 954575 = 1431863) B1431863
theorem B954695 : Blo 952587 954695 := bstep (se 1 (by rfl) ⟨716021, by rfl⟩ : syracuseStep 954695 = 1432043) B1432043
theorem B2298395 : Blo 952587 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B4362815 : Blo 952587 4362815 := bstep (se 1 (by rfl) ⟨3272111, by rfl⟩ : syracuseStep 4362815 = 6544223) B6544223
theorem B955047 : Blo 952587 955047 := bstep (se 1 (by rfl) ⟨716285, by rfl⟩ : syracuseStep 955047 = 1432571) B1432571
theorem B955087 : Blo 952587 955087 := bstep (se 1 (by rfl) ⟨716315, by rfl⟩ : syracuseStep 955087 = 1432631) B1432631
theorem B955167 : Blo 952587 955167 := bstep (se 1 (by rfl) ⟨716375, by rfl⟩ : syracuseStep 955167 = 1432751) B1432751
theorem B955207 : Blo 952587 955207 := bstep (se 1 (by rfl) ⟨716405, by rfl⟩ : syracuseStep 955207 = 1432811) B1432811
theorem B10327117 : Blo 952587 10327117 := bstep (se 3 (by rfl) ⟨1936334, by rfl⟩ : syracuseStep 10327117 = 3872669) B3872669
theorem B955615 : Blo 952587 955615 := bstep (se 1 (by rfl) ⟨716711, by rfl⟩ : syracuseStep 955615 = 1433423) B1433423
theorem B955623 : Blo 952587 955623 := bstep (se 1 (by rfl) ⟨716717, by rfl⟩ : syracuseStep 955623 = 1433435) B1433435
theorem B955647 : Blo 952587 955647 := bstep (se 1 (by rfl) ⟨716735, by rfl⟩ : syracuseStep 955647 = 1433471) B1433471
theorem B955695 : Blo 952587 955695 := bstep (se 1 (by rfl) ⟨716771, by rfl⟩ : syracuseStep 955695 = 1433543) B1433543
theorem B955855 : Blo 952587 955855 := bstep (se 1 (by rfl) ⟨716891, by rfl⟩ : syracuseStep 955855 = 1433783) B1433783
theorem B955935 : Blo 952587 955935 := bstep (se 1 (by rfl) ⟨716951, by rfl⟩ : syracuseStep 955935 = 1433903) B1433903
theorem B1611407 : Blo 952587 1611407 := bstep (se 1 (by rfl) ⟨1208555, by rfl⟩ : syracuseStep 1611407 = 2417111) B2417111
theorem B956063 : Blo 952587 956063 := bstep (se 1 (by rfl) ⟨717047, by rfl⟩ : syracuseStep 956063 = 1434095) B1434095
theorem B956095 : Blo 952587 956095 := bstep (se 1 (by rfl) ⟨717071, by rfl⟩ : syracuseStep 956095 = 1434143) B1434143
theorem B956135 : Blo 952587 956135 := bstep (se 1 (by rfl) ⟨717101, by rfl⟩ : syracuseStep 956135 = 1434203) B1434203
theorem B5446223 : Blo 952587 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B11770571 : Blo 952587 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B1809515 : Blo 952587 1809515 := bstep (se 1 (by rfl) ⟨1357136, by rfl⟩ : syracuseStep 1809515 = 2714273) B2714273
theorem B4595291 : Blo 952587 4595291 := bstep (se 1 (by rfl) ⟨3446468, by rfl⟩ : syracuseStep 4595291 = 6892937) B6892937
theorem B3219641 : Blo 952587 3219641 := bstep (se 2 (by rfl) ⟨1207365, by rfl⟩ : syracuseStep 3219641 = 2414731) B2414731
theorem B4825331 : Blo 952587 4825331 := bstep (se 1 (by rfl) ⟨3618998, by rfl⟩ : syracuseStep 4825331 = 7237997) B7237997
theorem B1614127 : Blo 952587 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B4892075 : Blo 952587 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B23242241 : Blo 952587 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B6104807 : Blo 952587 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B4073273 : Blo 952587 4073273 := bstep (se 2 (by rfl) ⟨1527477, by rfl⟩ : syracuseStep 4073273 = 3054955) B3054955
theorem B5154911 : Blo 952587 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B5155409 : Blo 952587 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B6106013 : Blo 952587 6106013 := bstep (se 3 (by rfl) ⟨1144877, by rfl⟩ : syracuseStep 6106013 = 2289755) B2289755
theorem B5156639 : Blo 952587 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B18329489 : Blo 952587 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B3224609 : Blo 952587 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B6272083 : Blo 952587 6272083 := bstep (se 1 (by rfl) ⟨4704062, by rfl⟩ : syracuseStep 6272083 = 9408125) B9408125
theorem B2143529 : Blo 952587 2143529 := bstep (se 2 (by rfl) ⟨803823, by rfl⟩ : syracuseStep 2143529 = 1607647) B1607647
theorem B46478717 : Blo 952587 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B3225257 : Blo 952587 3225257 := bstep (se 2 (by rfl) ⟨1209471, by rfl⟩ : syracuseStep 3225257 = 2418943) B2418943
theorem B3226337 : Blo 952587 3226337 := bstep (se 2 (by rfl) ⟨1209876, by rfl⟩ : syracuseStep 3226337 = 2419753) B2419753
theorem B13745159 : Blo 952587 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B4078687 : Blo 952587 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B7748783 : Blo 952587 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B4832621 : Blo 952587 4832621 := bstep (se 3 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 4832621 = 1812233) B1812233
theorem B10862099 : Blo 952587 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B2145959 : Blo 952587 2145959 := bstep (se 1 (by rfl) ⟨1609469, by rfl⟩ : syracuseStep 2145959 = 3218939) B3218939
theorem B1359551 : Blo 952587 1359551 := bstep (se 1 (by rfl) ⟨1019663, by rfl⟩ : syracuseStep 1359551 = 2039327) B2039327
theorem B2146031 : Blo 952587 2146031 := bstep (se 1 (by rfl) ⟨1609523, by rfl⟩ : syracuseStep 2146031 = 3219047) B3219047
theorem B2146067 : Blo 952587 2146067 := bstep (se 1 (by rfl) ⟨1609550, by rfl⟩ : syracuseStep 2146067 = 3219101) B3219101
theorem B3227903 : Blo 952587 3227903 := bstep (se 1 (by rfl) ⟨2420927, by rfl⟩ : syracuseStep 3227903 = 4841855) B4841855
theorem B7258409 : Blo 952587 7258409 := bstep (se 2 (by rfl) ⟨2721903, by rfl⟩ : syracuseStep 7258409 = 5443807) B5443807
theorem B2146643 : Blo 952587 2146643 := bstep (se 1 (by rfl) ⟨1609982, by rfl⟩ : syracuseStep 2146643 = 3219965) B3219965
theorem B4473191 : Blo 952587 4473191 := bstep (se 1 (by rfl) ⟨3354893, by rfl⟩ : syracuseStep 4473191 = 6709787) B6709787
theorem B2146751 : Blo 952587 2146751 := bstep (se 1 (by rfl) ⟨1610063, by rfl⟩ : syracuseStep 2146751 = 3220127) B3220127
theorem B41370749 : Blo 952587 41370749 := bstep (se 3 (by rfl) ⟨7757015, by rfl⟩ : syracuseStep 41370749 = 15514031) B15514031
theorem B4834727 : Blo 952587 4834727 := bstep (se 1 (by rfl) ⟨3626045, by rfl⟩ : syracuseStep 4834727 = 7252091) B7252091
theorem B3622583 : Blo 952587 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B2148047 : Blo 952587 2148047 := bstep (se 1 (by rfl) ⟨1611035, by rfl⟩ : syracuseStep 2148047 = 3222071) B3222071
theorem B18598123 : Blo 952587 18598123 := bstep (se 1 (by rfl) ⟨13948592, by rfl⟩ : syracuseStep 18598123 = 27897185) B27897185
theorem B8145481 : Blo 952587 8145481 := bstep (se 2 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 8145481 = 6109111) B6109111
theorem B55757429 : Blo 952587 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B4082719 : Blo 952587 4082719 := bstep (se 1 (by rfl) ⟨3062039, by rfl⟩ : syracuseStep 4082719 = 6124079) B6124079
theorem B3624041 : Blo 952587 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B2575489 : Blo 952587 2575489 := bstep (se 2 (by rfl) ⟨965808, by rfl⟩ : syracuseStep 2575489 = 1931617) B1931617
theorem B4836509 : Blo 952587 4836509 := bstep (se 3 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 4836509 = 1813691) B1813691
theorem B1428959 : Blo 952587 1428959 := bstep (se 1 (by rfl) ⟨1071719, by rfl⟩ : syracuseStep 1428959 = 2143439) B2143439
theorem B4836833 : Blo 952587 4836833 := bstep (se 2 (by rfl) ⟨1813812, by rfl⟩ : syracuseStep 4836833 = 3627625) B3627625
theorem B1429439 : Blo 952587 1429439 := bstep (se 1 (by rfl) ⟨1072079, by rfl⟩ : syracuseStep 1429439 = 2144159) B2144159
theorem B4837319 : Blo 952587 4837319 := bstep (se 1 (by rfl) ⟨3627989, by rfl⟩ : syracuseStep 4837319 = 7255979) B7255979
theorem B2412575 : Blo 952587 2412575 := bstep (se 1 (by rfl) ⟨1809431, by rfl⟩ : syracuseStep 2412575 = 3618863) B3618863
theorem B3625195 : Blo 952587 3625195 := bstep (se 1 (by rfl) ⟨2718896, by rfl⟩ : syracuseStep 3625195 = 5437793) B5437793
theorem B1429799 : Blo 952587 1429799 := bstep (se 1 (by rfl) ⟨1072349, by rfl⟩ : syracuseStep 1429799 = 2144699) B2144699
theorem B2577359 : Blo 952587 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B1430555 : Blo 952587 1430555 := bstep (se 1 (by rfl) ⟨1072916, by rfl⟩ : syracuseStep 1430555 = 2145833) B2145833
theorem B1430759 : Blo 952587 1430759 := bstep (se 1 (by rfl) ⟨1073069, by rfl⟩ : syracuseStep 1430759 = 2146139) B2146139
theorem B2151863 : Blo 952587 2151863 := bstep (se 1 (by rfl) ⟨1613897, by rfl⟩ : syracuseStep 2151863 = 3227795) B3227795
theorem B1431131 : Blo 952587 1431131 := bstep (se 1 (by rfl) ⟨1073348, by rfl⟩ : syracuseStep 1431131 = 2146697) B2146697
theorem B2152079 : Blo 952587 2152079 := bstep (se 1 (by rfl) ⟨1614059, by rfl⟩ : syracuseStep 2152079 = 3228119) B3228119
theorem B1398811 : Blo 952587 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B78469559 : Blo 952587 78469559 := bstep (se 1 (by rfl) ⟨58852169, by rfl⟩ : syracuseStep 78469559 = 117704339) B117704339
theorem B5429753 : Blo 952587 5429753 := bstep (se 2 (by rfl) ⟨2036157, by rfl⟩ : syracuseStep 5429753 = 4072315) B4072315
theorem B3627611 : Blo 952587 3627611 := bstep (se 1 (by rfl) ⟨2720708, by rfl⟩ : syracuseStep 3627611 = 5441417) B5441417
theorem B8149855 : Blo 952587 8149855 := bstep (se 1 (by rfl) ⟨6112391, by rfl⟩ : syracuseStep 8149855 = 12224783) B12224783
theorem B2907227 : Blo 952587 2907227 := bstep (se 1 (by rfl) ⟨2180420, by rfl⟩ : syracuseStep 2907227 = 4360841) B4360841
theorem B2448703 : Blo 952587 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B1432991 : Blo 952587 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B1433627 : Blo 952587 1433627 := bstep (se 1 (by rfl) ⟨1075220, by rfl⟩ : syracuseStep 1433627 = 2150441) B2150441
theorem B62644519 : Blo 952587 62644519 := bstep (se 1 (by rfl) ⟨46983389, by rfl⟩ : syracuseStep 62644519 = 93966779) B93966779
theorem B1434011 : Blo 952587 1434011 := bstep (se 1 (by rfl) ⟨1075508, by rfl⟩ : syracuseStep 1434011 = 2151017) B2151017
theorem B1073947 : Blo 952587 1073947 := bstep (se 1 (by rfl) ⟨805460, by rfl⟩ : syracuseStep 1073947 = 1610921) B1610921
theorem B6972367 : Blo 952587 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B2417647 : Blo 952587 2417647 := bstep (se 1 (by rfl) ⟨1813235, by rfl⟩ : syracuseStep 2417647 = 3626471) B3626471
theorem B1434665 : Blo 952587 1434665 := bstep (se 2 (by rfl) ⟨537999, by rfl⟩ : syracuseStep 1434665 = 1075999) B1075999
theorem B2417759 : Blo 952587 2417759 := bstep (se 1 (by rfl) ⟨1813319, by rfl⟩ : syracuseStep 2417759 = 3626639) B3626639
theorem B10314971 : Blo 952587 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B7235081 : Blo 952587 7235081 := bstep (se 2 (by rfl) ⟨2713155, by rfl⟩ : syracuseStep 7235081 = 5426311) B5426311
theorem B1074919 : Blo 952587 1074919 := bstep (se 1 (by rfl) ⟨806189, by rfl⟩ : syracuseStep 1074919 = 1612379) B1612379
theorem B26175473 : Blo 952587 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B3435367 : Blo 952587 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B1076071 : Blo 952587 1076071 := bstep (se 1 (by rfl) ⟨807053, by rfl⟩ : syracuseStep 1076071 = 1614107) B1614107
theorem B24767365 : Blo 952587 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B5434559 : Blo 952587 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B7237025 : Blo 952587 7237025 := bstep (se 2 (by rfl) ⟨2713884, by rfl⟩ : syracuseStep 7237025 = 5427769) B5427769
theorem B2715389 : Blo 952587 2715389 := bstep (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) B1018271
theorem B3436319 : Blo 952587 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B2453735 : Blo 952587 2453735 := bstep (se 1 (by rfl) ⟨1840301, by rfl⟩ : syracuseStep 2453735 = 3680603) B3680603
theorem B12218633 : Blo 952587 12218633 := bstep (se 2 (by rfl) ⟨4581987, by rfl⟩ : syracuseStep 12218633 = 9163975) B9163975
theorem B18379547 : Blo 952587 18379547 := bstep (se 1 (by rfl) ⟨13784660, by rfl⟩ : syracuseStep 18379547 = 27569321) B27569321
theorem B3863327 : Blo 952587 3863327 := bstep (se 1 (by rfl) ⟨2897495, by rfl⟩ : syracuseStep 3863327 = 5794991) B5794991
theorem B5436791 : Blo 952587 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B7239455 : Blo 952587 7239455 := bstep (se 1 (by rfl) ⟨5429591, by rfl⟩ : syracuseStep 7239455 = 10859183) B10859183
theorem B4585355 : Blo 952587 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B14874697 : Blo 952587 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B2293147 : Blo 952587 2293147 := bstep (se 1 (by rfl) ⟨1719860, by rfl⟩ : syracuseStep 2293147 = 3439721) B3439721
theorem B1572571 : Blo 952587 1572571 := bstep (se 1 (by rfl) ⟨1179428, by rfl⟩ : syracuseStep 1572571 = 2358857) B2358857
theorem B5439251 : Blo 952587 5439251 := bstep (se 1 (by rfl) ⟨4079438, by rfl⟩ : syracuseStep 5439251 = 8158877) B8158877
theorem B2719615 : Blo 952587 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B79331717 : Blo 952587 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B83526025 : Blo 952587 83526025 := bstep (se 2 (by rfl) ⟨31322259, by rfl⟩ : syracuseStep 83526025 = 62644519) B62644519
theorem B11928509 : Blo 952587 11928509 := bstep (se 3 (by rfl) ⟨2236595, by rfl⟩ : syracuseStep 11928509 = 4473191) B4473191
theorem B6129053 : Blo 952587 6129053 := bstep (se 3 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 6129053 = 2298395) B2298395
theorem B952639 : Blo 952587 952639 := bstep (se 1 (by rfl) ⟨714479, by rfl⟩ : syracuseStep 952639 = 1428959) B1428959
theorem B952959 : Blo 952587 952959 := bstep (se 1 (by rfl) ⟨714719, by rfl⟩ : syracuseStep 952959 = 1429439) B1429439
theorem B1608383 : Blo 952587 1608383 := bstep (se 1 (by rfl) ⟨1206287, by rfl⟩ : syracuseStep 1608383 = 2412575) B2412575
theorem B953199 : Blo 952587 953199 := bstep (se 1 (by rfl) ⟨714899, by rfl⟩ : syracuseStep 953199 = 1429799) B1429799
theorem B953703 : Blo 952587 953703 := bstep (se 1 (by rfl) ⟨715277, by rfl⟩ : syracuseStep 953703 = 1430555) B1430555
theorem B953839 : Blo 952587 953839 := bstep (se 1 (by rfl) ⟨715379, by rfl⟩ : syracuseStep 953839 = 1430759) B1430759
theorem B954087 : Blo 952587 954087 := bstep (se 1 (by rfl) ⟨715565, by rfl⟩ : syracuseStep 954087 = 1431131) B1431131
theorem B5443625 : Blo 952587 5443625 := bstep (se 2 (by rfl) ⟨2041359, by rfl⟩ : syracuseStep 5443625 = 4082719) B4082719
theorem B18354397 : Blo 952587 18354397 := bstep (se 3 (by rfl) ⟨3441449, by rfl⟩ : syracuseStep 18354397 = 6882899) B6882899
theorem B1938151 : Blo 952587 1938151 := bstep (se 1 (by rfl) ⟨1453613, by rfl⟩ : syracuseStep 1938151 = 2907227) B2907227
theorem B955327 : Blo 952587 955327 := bstep (se 1 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 955327 = 1432991) B1432991
theorem B955751 : Blo 952587 955751 := bstep (se 1 (by rfl) ⟨716813, by rfl⟩ : syracuseStep 955751 = 1433627) B1433627
theorem B3216887 : Blo 952587 3216887 := bstep (se 1 (by rfl) ⟨2412665, by rfl⟩ : syracuseStep 3216887 = 4825331) B4825331
theorem B956007 : Blo 952587 956007 := bstep (se 1 (by rfl) ⟨717005, by rfl⟩ : syracuseStep 956007 = 1434011) B1434011
theorem B956443 : Blo 952587 956443 := bstep (se 1 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 956443 = 1434665) B1434665
theorem B1611839 : Blo 952587 1611839 := bstep (se 1 (by rfl) ⟨1208879, by rfl⟩ : syracuseStep 1611839 = 2417759) B2417759
theorem B4823387 : Blo 952587 4823387 := bstep (se 1 (by rfl) ⟨3617540, by rfl⟩ : syracuseStep 4823387 = 7235081) B7235081
theorem B4069871 : Blo 952587 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B13769489 : Blo 952587 13769489 := bstep (se 2 (by rfl) ⟨5163558, by rfl⟩ : syracuseStep 13769489 = 10327117) B10327117
theorem B8362777 : Blo 952587 8362777 := bstep (se 2 (by rfl) ⟨3136041, by rfl⟩ : syracuseStep 8362777 = 6272083) B6272083
theorem B4070675 : Blo 952587 4070675 := bstep (se 1 (by rfl) ⟨3053006, by rfl⟩ : syracuseStep 4070675 = 6106013) B6106013
theorem B4824683 : Blo 952587 4824683 := bstep (se 1 (by rfl) ⟨3618512, by rfl⟩ : syracuseStep 4824683 = 7237025) B7237025
theorem B1810259 : Blo 952587 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B4826303 : Blo 952587 4826303 := bstep (se 1 (by rfl) ⟨3619727, by rfl⟩ : syracuseStep 4826303 = 7239455) B7239455
theorem B3056903 : Blo 952587 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B3057529 : Blo 952587 3057529 := bstep (se 2 (by rfl) ⟨1146573, by rfl⟩ : syracuseStep 3057529 = 2293147) B2293147
theorem B3221747 : Blo 952587 3221747 := bstep (se 1 (by rfl) ⟨2416310, by rfl⟩ : syracuseStep 3221747 = 4832621) B4832621
theorem B3223151 : Blo 952587 3223151 := bstep (se 1 (by rfl) ⟨2417363, by rfl⟩ : syracuseStep 3223151 = 4834727) B4834727
theorem B3223529 : Blo 952587 3223529 := bstep (se 2 (by rfl) ⟨1208823, by rfl⟩ : syracuseStep 3223529 = 2417647) B2417647
theorem B7254035 : Blo 952587 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B37171619 : Blo 952587 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B3224339 : Blo 952587 3224339 := bstep (se 1 (by rfl) ⟨2418254, by rfl⟩ : syracuseStep 3224339 = 4836509) B4836509
theorem B3224555 : Blo 952587 3224555 := bstep (se 1 (by rfl) ⟨2418416, by rfl⟩ : syracuseStep 3224555 = 4836833) B4836833
theorem B3224879 : Blo 952587 3224879 := bstep (se 1 (by rfl) ⟨2418659, by rfl⟩ : syracuseStep 3224879 = 4837319) B4837319
theorem B10860641 : Blo 952587 10860641 := bstep (se 2 (by rfl) ⟨4072740, by rfl⟩ : syracuseStep 10860641 = 8145481) B8145481
theorem B52313039 : Blo 952587 52313039 := bstep (se 1 (by rfl) ⟨39234779, by rfl⟩ : syracuseStep 52313039 = 78469559) B78469559
theorem B3619835 : Blo 952587 3619835 := bstep (se 1 (by rfl) ⟨2714876, by rfl⟩ : syracuseStep 3619835 = 5429753) B5429753
theorem B7847047 : Blo 952587 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B2145761 : Blo 952587 2145761 := bstep (se 2 (by rfl) ⟨804660, by rfl⟩ : syracuseStep 2145761 = 1609321) B1609321
theorem B3063527 : Blo 952587 3063527 := bstep (se 1 (by rfl) ⟨2297645, by rfl⟩ : syracuseStep 3063527 = 4595291) B4595291
theorem B2146427 : Blo 952587 2146427 := bstep (se 1 (by rfl) ⟨1609820, by rfl⟩ : syracuseStep 2146427 = 3219641) B3219641
theorem B4833593 : Blo 952587 4833593 := bstep (se 2 (by rfl) ⟨1812597, by rfl⟩ : syracuseStep 4833593 = 3625195) B3625195
theorem B3261383 : Blo 952587 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B17450315 : Blo 952587 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B3623039 : Blo 952587 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B8145755 : Blo 952587 8145755 := bstep (se 1 (by rfl) ⟨6109316, by rfl⟩ : syracuseStep 8145755 = 12218633) B12218633
theorem B41208821 : Blo 952587 41208821 := bstep (se 5 (by rfl) ⟨1931663, by rfl⟩ : syracuseStep 41208821 = 3863327) B3863327
theorem B2149739 : Blo 952587 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B1429019 : Blo 952587 1429019 := bstep (se 1 (by rfl) ⟨1071764, by rfl⟩ : syracuseStep 1429019 = 2143529) B2143529
theorem B3624527 : Blo 952587 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B30985811 : Blo 952587 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B2150171 : Blo 952587 2150171 := bstep (se 1 (by rfl) ⟨1612628, by rfl⟩ : syracuseStep 2150171 = 3225257) B3225257
theorem B10866473 : Blo 952587 10866473 := bstep (se 2 (by rfl) ⟨4074927, by rfl⟩ : syracuseStep 10866473 = 8149855) B8149855
theorem B3264937 : Blo 952587 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B2150891 : Blo 952587 2150891 := bstep (se 1 (by rfl) ⟨1613168, by rfl⟩ : syracuseStep 2150891 = 3226337) B3226337
theorem B3625469 : Blo 952587 3625469 := bstep (se 3 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 3625469 = 1359551) B1359551
theorem B9163439 : Blo 952587 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B5165855 : Blo 952587 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B1430639 : Blo 952587 1430639 := bstep (se 1 (by rfl) ⟨1072979, by rfl⟩ : syracuseStep 1430639 = 2145959) B2145959
theorem B1430687 : Blo 952587 1430687 := bstep (se 1 (by rfl) ⟨1073015, by rfl⟩ : syracuseStep 1430687 = 2146031) B2146031
theorem B3626153 : Blo 952587 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B1430711 : Blo 952587 1430711 := bstep (se 1 (by rfl) ⟨1073033, by rfl⟩ : syracuseStep 1430711 = 2146067) B2146067
theorem B3626167 : Blo 952587 3626167 := bstep (se 1 (by rfl) ⟨2719625, by rfl⟩ : syracuseStep 3626167 = 5439251) B5439251
theorem B2151935 : Blo 952587 2151935 := bstep (se 1 (by rfl) ⟨1613951, by rfl⟩ : syracuseStep 2151935 = 3227903) B3227903
theorem B4838939 : Blo 952587 4838939 := bstep (se 1 (by rfl) ⟨3629204, by rfl⟩ : syracuseStep 4838939 = 7258409) B7258409
theorem B1431095 : Blo 952587 1431095 := bstep (se 1 (by rfl) ⟨1073321, by rfl⟩ : syracuseStep 1431095 = 2146643) B2146643
theorem B1431167 : Blo 952587 1431167 := bstep (se 1 (by rfl) ⟨1073375, by rfl⟩ : syracuseStep 1431167 = 2146751) B2146751
theorem B2152169 : Blo 952587 2152169 := bstep (se 2 (by rfl) ⟨807063, by rfl⟩ : syracuseStep 2152169 = 1614127) B1614127
theorem B27580499 : Blo 952587 27580499 := bstep (se 1 (by rfl) ⟨20685374, by rfl⟩ : syracuseStep 27580499 = 41370749) B41370749
theorem B1431929 : Blo 952587 1431929 := bstep (se 2 (by rfl) ⟨536973, by rfl⟩ : syracuseStep 1431929 = 1073947) B1073947
theorem B2415055 : Blo 952587 2415055 := bstep (se 1 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 2415055 = 3622583) B3622583
theorem B1432031 : Blo 952587 1432031 := bstep (se 1 (by rfl) ⟨1074023, by rfl⟩ : syracuseStep 1432031 = 2148047) B2148047
theorem B9296489 : Blo 952587 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B2416027 : Blo 952587 2416027 := bstep (se 1 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 2416027 = 3624041) B3624041
theorem B1433225 : Blo 952587 1433225 := bstep (se 2 (by rfl) ⟨537459, by rfl⟩ : syracuseStep 1433225 = 1074919) B1074919
theorem B2908007 : Blo 952587 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B6872957 : Blo 952587 6872957 := bstep (se 3 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 6872957 = 2577359) B2577359
theorem B6119363 : Blo 952587 6119363 := bstep (se 1 (by rfl) ⟨4589522, by rfl⟩ : syracuseStep 6119363 = 9179045) B9179045
theorem B24797497 : Blo 952587 24797497 := bstep (se 2 (by rfl) ⟨9299061, by rfl⟩ : syracuseStep 24797497 = 18598123) B18598123
theorem B2908543 : Blo 952587 2908543 := bstep (se 1 (by rfl) ⟨2181407, by rfl⟩ : syracuseStep 2908543 = 4362815) B4362815
theorem B45310369 : Blo 952587 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B1434575 : Blo 952587 1434575 := bstep (se 1 (by rfl) ⟨1075931, by rfl⟩ : syracuseStep 1434575 = 2151863) B2151863
theorem B1074271 : Blo 952587 1074271 := bstep (se 1 (by rfl) ⟨805703, by rfl⟩ : syracuseStep 1074271 = 1611407) B1611407
theorem B1434719 : Blo 952587 1434719 := bstep (se 1 (by rfl) ⟨1076039, by rfl⟩ : syracuseStep 1434719 = 2152079) B2152079
theorem B4580489 : Blo 952587 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B1434761 : Blo 952587 1434761 := bstep (se 2 (by rfl) ⟨538035, by rfl⟩ : syracuseStep 1434761 = 1076071) B1076071
theorem B33023153 : Blo 952587 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B3433985 : Blo 952587 3433985 := bstep (se 2 (by rfl) ⟨1287744, by rfl⟩ : syracuseStep 3433985 = 2575489) B2575489
theorem B3630815 : Blo 952587 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B2418407 : Blo 952587 2418407 := bstep (se 1 (by rfl) ⟨1813805, by rfl⟩ : syracuseStep 2418407 = 3627611) B3627611
theorem B1206343 : Blo 952587 1206343 := bstep (se 1 (by rfl) ⟨904757, by rfl⟩ : syracuseStep 1206343 = 1809515) B1809515
theorem B6876647 : Blo 952587 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B15494827 : Blo 952587 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B2715515 : Blo 952587 2715515 := bstep (se 1 (by rfl) ⟨2036636, by rfl⟩ : syracuseStep 2715515 = 4073273) B4073273
theorem B3436607 : Blo 952587 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B3436939 : Blo 952587 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B2290879 : Blo 952587 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B3437759 : Blo 952587 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B12219659 : Blo 952587 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B1865081 : Blo 952587 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1635823 : Blo 952587 1635823 := bstep (se 1 (by rfl) ⟨1226867, by rfl⟩ : syracuseStep 1635823 = 2453735) B2453735
theorem B12253031 : Blo 952587 12253031 := bstep (se 1 (by rfl) ⟨9189773, by rfl⟩ : syracuseStep 12253031 = 18379547) B18379547
theorem B5438249 : Blo 952587 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B2096761 : Blo 952587 2096761 := bstep (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) B1572571
theorem B7241399 : Blo 952587 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B52887811 : Blo 952587 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B33063329 : Blo 952587 33063329 := bstep (se 2 (by rfl) ⟨12398748, by rfl⟩ : syracuseStep 33063329 = 24797497) B24797497
theorem B11633543 : Blo 952587 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B952679 : Blo 952587 952679 := bstep (se 1 (by rfl) ⟨714509, by rfl⟩ : syracuseStep 952679 = 1429019) B1429019
theorem B7244315 : Blo 952587 7244315 := bstep (se 1 (by rfl) ⟨5433236, by rfl⟩ : syracuseStep 7244315 = 10866473) B10866473
theorem B1608457 : Blo 952587 1608457 := bstep (se 2 (by rfl) ⟨603171, by rfl⟩ : syracuseStep 1608457 = 1206343) B1206343
theorem B3443903 : Blo 952587 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B953759 : Blo 952587 953759 := bstep (se 1 (by rfl) ⟨715319, by rfl⟩ : syracuseStep 953759 = 1430639) B1430639
theorem B953791 : Blo 952587 953791 := bstep (se 1 (by rfl) ⟨715343, by rfl⟩ : syracuseStep 953791 = 1430687) B1430687
theorem B953807 : Blo 952587 953807 := bstep (se 1 (by rfl) ⟨715355, by rfl⟩ : syracuseStep 953807 = 1430711) B1430711
theorem B954063 : Blo 952587 954063 := bstep (se 1 (by rfl) ⟨715547, by rfl⟩ : syracuseStep 954063 = 1431095) B1431095
theorem B954111 : Blo 952587 954111 := bstep (se 1 (by rfl) ⟨715583, by rfl⟩ : syracuseStep 954111 = 1431167) B1431167
theorem B18386999 : Blo 952587 18386999 := bstep (se 1 (by rfl) ⟨13790249, by rfl⟩ : syracuseStep 18386999 = 27580499) B27580499
theorem B3215591 : Blo 952587 3215591 := bstep (se 1 (by rfl) ⟨2411693, by rfl⟩ : syracuseStep 3215591 = 4823387) B4823387
theorem B954619 : Blo 952587 954619 := bstep (se 1 (by rfl) ⟨715964, by rfl⟩ : syracuseStep 954619 = 1431929) B1431929
theorem B954687 : Blo 952587 954687 := bstep (se 1 (by rfl) ⟨716015, by rfl⟩ : syracuseStep 954687 = 1432031) B1432031
theorem B9179659 : Blo 952587 9179659 := bstep (se 1 (by rfl) ⟨6884744, by rfl⟩ : syracuseStep 9179659 = 13769489) B13769489
theorem B3216455 : Blo 952587 3216455 := bstep (se 1 (by rfl) ⟨2412341, by rfl⟩ : syracuseStep 3216455 = 4824683) B4824683
theorem B955483 : Blo 952587 955483 := bstep (se 1 (by rfl) ⟨716612, by rfl⟩ : syracuseStep 955483 = 1433225) B1433225
theorem B1938671 : Blo 952587 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B956383 : Blo 952587 956383 := bstep (se 1 (by rfl) ⟨717287, by rfl⟩ : syracuseStep 956383 = 1434575) B1434575
theorem B956479 : Blo 952587 956479 := bstep (se 1 (by rfl) ⟨717359, by rfl⟩ : syracuseStep 956479 = 1434719) B1434719
theorem B956507 : Blo 952587 956507 := bstep (se 1 (by rfl) ⟨717380, by rfl⟩ : syracuseStep 956507 = 1434761) B1434761
theorem B3217535 : Blo 952587 3217535 := bstep (se 1 (by rfl) ⟨2413151, by rfl⟩ : syracuseStep 3217535 = 4826303) B4826303
theorem B2037935 : Blo 952587 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B1612271 : Blo 952587 1612271 := bstep (se 1 (by rfl) ⟨1209203, by rfl⟩ : syracuseStep 1612271 = 2418407) B2418407
theorem B3054505 : Blo 952587 3054505 := bstep (se 2 (by rfl) ⟨1145439, by rfl⟩ : syracuseStep 3054505 = 2290879) B2290879
theorem B1810343 : Blo 952587 1810343 := bstep (se 1 (by rfl) ⟨1357757, by rfl⟩ : syracuseStep 1810343 = 2715515) B2715515
theorem B24781079 : Blo 952587 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B3220073 : Blo 952587 3220073 := bstep (se 2 (by rfl) ⟨1207527, by rfl⟩ : syracuseStep 3220073 = 2415055) B2415055
theorem B11150369 : Blo 952587 11150369 := bstep (se 2 (by rfl) ⟨4181388, by rfl⟩ : syracuseStep 11150369 = 8362777) B8362777
theorem B8168687 : Blo 952587 8168687 := bstep (se 1 (by rfl) ⟨6126515, by rfl⟩ : syracuseStep 8168687 = 12253031) B12253031
theorem B10462729 : Blo 952587 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B3221369 : Blo 952587 3221369 := bstep (se 2 (by rfl) ⟨1208013, by rfl⟩ : syracuseStep 3221369 = 2416027) B2416027
theorem B34875359 : Blo 952587 34875359 := bstep (se 1 (by rfl) ⟨26156519, by rfl⟩ : syracuseStep 34875359 = 52313039) B52313039
theorem B2795681 : Blo 952587 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B4827599 : Blo 952587 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B2042351 : Blo 952587 2042351 := bstep (se 1 (by rfl) ⟨1531763, by rfl⟩ : syracuseStep 2042351 = 3063527) B3063527
theorem B3222395 : Blo 952587 3222395 := bstep (se 1 (by rfl) ⟨2416796, by rfl⟩ : syracuseStep 3222395 = 4833593) B4833593
theorem B3878057 : Blo 952587 3878057 := bstep (se 2 (by rfl) ⟨1454271, by rfl⟩ : syracuseStep 3878057 = 2908543) B2908543
theorem B2174255 : Blo 952587 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B27472547 : Blo 952587 27472547 := bstep (se 1 (by rfl) ⟨20604410, by rfl⟩ : syracuseStep 27472547 = 41208821) B41208821
theorem B17412997 : Blo 952587 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B20657207 : Blo 952587 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B4076705 : Blo 952587 4076705 := bstep (se 2 (by rfl) ⟨1528764, by rfl⟩ : syracuseStep 4076705 = 3057529) B3057529
theorem B6108959 : Blo 952587 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B2144591 : Blo 952587 2144591 := bstep (se 1 (by rfl) ⟨1608443, by rfl⟩ : syracuseStep 2144591 = 3216887) B3216887
theorem B3225959 : Blo 952587 3225959 := bstep (se 1 (by rfl) ⟨2419469, by rfl⟩ : syracuseStep 3225959 = 4838939) B4838939
theorem B10336805 : Blo 952587 10336805 := bstep (se 4 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 10336805 = 1938151) B1938151
theorem B20659769 : Blo 952587 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B4079575 : Blo 952587 4079575 := bstep (se 1 (by rfl) ⟨3059681, by rfl⟩ : syracuseStep 4079575 = 6119363) B6119363
theorem B2147831 : Blo 952587 2147831 := bstep (se 1 (by rfl) ⟨1610873, by rfl⟩ : syracuseStep 2147831 = 3221747) B3221747
theorem B4834889 : Blo 952587 4834889 := bstep (se 2 (by rfl) ⟨1813083, by rfl⟩ : syracuseStep 4834889 = 3626167) B3626167
theorem B24790637 : Blo 952587 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B2181097 : Blo 952587 2181097 := bstep (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) B1635823
theorem B2148767 : Blo 952587 2148767 := bstep (se 1 (by rfl) ⟨1611575, by rfl⟩ : syracuseStep 2148767 = 3223151) B3223151
theorem B2149019 : Blo 952587 2149019 := bstep (se 1 (by rfl) ⟨1611764, by rfl⟩ : syracuseStep 2149019 = 3223529) B3223529
theorem B4836023 : Blo 952587 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B2149559 : Blo 952587 2149559 := bstep (se 1 (by rfl) ⟨1612169, by rfl⟩ : syracuseStep 2149559 = 3224339) B3224339
theorem B2149703 : Blo 952587 2149703 := bstep (se 1 (by rfl) ⟨1612277, by rfl⟩ : syracuseStep 2149703 = 3224555) B3224555
theorem B8146439 : Blo 952587 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B2149919 : Blo 952587 2149919 := bstep (se 1 (by rfl) ⟨1612439, by rfl⟩ : syracuseStep 2149919 = 3224879) B3224879
theorem B3625499 : Blo 952587 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B2413223 : Blo 952587 2413223 := bstep (se 1 (by rfl) ⟨1809917, by rfl⟩ : syracuseStep 2413223 = 3619835) B3619835
theorem B1430507 : Blo 952587 1430507 := bstep (se 1 (by rfl) ⟨1072880, by rfl⟩ : syracuseStep 1430507 = 2145761) B2145761
theorem B1430951 : Blo 952587 1430951 := bstep (se 1 (by rfl) ⟨1073213, by rfl⟩ : syracuseStep 1430951 = 2146427) B2146427
theorem B111368033 : Blo 952587 111368033 := bstep (se 2 (by rfl) ⟨41763012, by rfl⟩ : syracuseStep 111368033 = 83526025) B83526025
theorem B60413825 : Blo 952587 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B7952339 : Blo 952587 7952339 := bstep (se 1 (by rfl) ⟨5964254, by rfl⟩ : syracuseStep 7952339 = 11928509) B11928509
theorem B4086035 : Blo 952587 4086035 := bstep (se 1 (by rfl) ⟨3064526, by rfl⟩ : syracuseStep 4086035 = 6129053) B6129053
theorem B2415359 : Blo 952587 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B1432361 : Blo 952587 1432361 := bstep (se 2 (by rfl) ⟨537135, by rfl⟩ : syracuseStep 1432361 = 1074271) B1074271
theorem B1072255 : Blo 952587 1072255 := bstep (se 1 (by rfl) ⟨804191, by rfl⟩ : syracuseStep 1072255 = 1608383) B1608383
theorem B5430503 : Blo 952587 5430503 := bstep (se 1 (by rfl) ⟨4072877, by rfl⟩ : syracuseStep 5430503 = 8145755) B8145755
theorem B1433159 : Blo 952587 1433159 := bstep (se 1 (by rfl) ⟨1074869, by rfl⟩ : syracuseStep 1433159 = 2149739) B2149739
theorem B2416351 : Blo 952587 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B1433447 : Blo 952587 1433447 := bstep (se 1 (by rfl) ⟨1075085, by rfl⟩ : syracuseStep 1433447 = 2150171) B2150171
theorem B3629083 : Blo 952587 3629083 := bstep (se 1 (by rfl) ⟨2721812, by rfl⟩ : syracuseStep 3629083 = 5443625) B5443625
theorem B1433927 : Blo 952587 1433927 := bstep (se 1 (by rfl) ⟨1075445, by rfl⟩ : syracuseStep 1433927 = 2150891) B2150891
theorem B2416979 : Blo 952587 2416979 := bstep (se 1 (by rfl) ⟨1812734, by rfl⟩ : syracuseStep 2416979 = 3625469) B3625469
theorem B12214637 : Blo 952587 12214637 := bstep (se 3 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 12214637 = 4580489) B4580489
theorem B9167357 : Blo 952587 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B2417435 : Blo 952587 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B1434623 : Blo 952587 1434623 := bstep (se 1 (by rfl) ⟨1075967, by rfl⟩ : syracuseStep 1434623 = 2151935) B2151935
theorem B1434779 : Blo 952587 1434779 := bstep (se 1 (by rfl) ⟨1076084, by rfl⟩ : syracuseStep 1434779 = 2152169) B2152169
theorem B1074559 : Blo 952587 1074559 := bstep (se 1 (by rfl) ⟨805919, by rfl⟩ : syracuseStep 1074559 = 1611839) B1611839
theorem B2713247 : Blo 952587 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B2713783 : Blo 952587 2713783 := bstep (se 1 (by rfl) ⟨2035337, by rfl⟩ : syracuseStep 2713783 = 4070675) B4070675
theorem B1206839 : Blo 952587 1206839 := bstep (se 1 (by rfl) ⟨905129, by rfl⟩ : syracuseStep 1206839 = 1810259) B1810259
theorem B4581971 : Blo 952587 4581971 := bstep (se 1 (by rfl) ⟨3436478, by rfl⟩ : syracuseStep 4581971 = 6872957) B6872957
theorem B24472529 : Blo 952587 24472529 := bstep (se 2 (by rfl) ⟨9177198, by rfl⟩ : syracuseStep 24472529 = 18354397) B18354397
theorem B4582585 : Blo 952587 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B22015435 : Blo 952587 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B2289323 : Blo 952587 2289323 := bstep (se 1 (by rfl) ⟨1716992, by rfl⟩ : syracuseStep 2289323 = 3433985) B3433985
theorem B2420543 : Blo 952587 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B4584431 : Blo 952587 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B2291071 : Blo 952587 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B1243387 : Blo 952587 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B7240427 : Blo 952587 7240427 := bstep (se 1 (by rfl) ⟨5430320, by rfl⟩ : syracuseStep 7240427 = 10860641) B10860641
theorem B70517081 : Blo 952587 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B24446285 : Blo 952587 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B2295935 : Blo 952587 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B12257999 : Blo 952587 12257999 := bstep (se 1 (by rfl) ⟨9193499, by rfl⟩ : syracuseStep 12257999 = 18386999) B18386999
theorem B1608815 : Blo 952587 1608815 := bstep (se 1 (by rfl) ⟨1206611, by rfl⟩ : syracuseStep 1608815 = 2413223) B2413223
theorem B953671 : Blo 952587 953671 := bstep (se 1 (by rfl) ⟨715253, by rfl⟩ : syracuseStep 953671 = 1430507) B1430507
theorem B953967 : Blo 952587 953967 := bstep (se 1 (by rfl) ⟨715475, by rfl⟩ : syracuseStep 953967 = 1430951) B1430951
theorem B40275883 : Blo 952587 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B2724023 : Blo 952587 2724023 := bstep (se 1 (by rfl) ⟨2043017, by rfl⟩ : syracuseStep 2724023 = 4086035) B4086035
theorem B1610239 : Blo 952587 1610239 := bstep (se 1 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 1610239 = 2415359) B2415359
theorem B954907 : Blo 952587 954907 := bstep (se 1 (by rfl) ⟨716180, by rfl⟩ : syracuseStep 954907 = 1432361) B1432361
theorem B955439 : Blo 952587 955439 := bstep (se 1 (by rfl) ⟨716579, by rfl⟩ : syracuseStep 955439 = 1433159) B1433159
theorem B955631 : Blo 952587 955631 := bstep (se 1 (by rfl) ⟨716723, by rfl⟩ : syracuseStep 955631 = 1433447) B1433447
theorem B16520719 : Blo 952587 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B955951 : Blo 952587 955951 := bstep (se 1 (by rfl) ⟨716963, by rfl⟩ : syracuseStep 955951 = 1433927) B1433927
theorem B1611319 : Blo 952587 1611319 := bstep (se 1 (by rfl) ⟨1208489, by rfl⟩ : syracuseStep 1611319 = 2416979) B2416979
theorem B1611623 : Blo 952587 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B956415 : Blo 952587 956415 := bstep (se 1 (by rfl) ⟨717311, by rfl⟩ : syracuseStep 956415 = 1434623) B1434623
theorem B956519 : Blo 952587 956519 := bstep (se 1 (by rfl) ⟨717389, by rfl⟩ : syracuseStep 956519 = 1434779) B1434779
theorem B5445791 : Blo 952587 5445791 := bstep (se 1 (by rfl) ⟨4084343, by rfl⟩ : syracuseStep 5445791 = 8168687) B8168687
theorem B1808831 : Blo 952587 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B3218237 : Blo 952587 3218237 := bstep (se 3 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 3218237 = 1206839) B1206839
theorem B3218399 : Blo 952587 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B3054647 : Blo 952587 3054647 := bstep (se 1 (by rfl) ⟨2290985, by rfl⟩ : syracuseStep 3054647 = 4581971) B4581971
theorem B3054761 : Blo 952587 3054761 := bstep (se 2 (by rfl) ⟨1145535, by rfl⟩ : syracuseStep 3054761 = 2291071) B2291071
theorem B1449503 : Blo 952587 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B1613695 : Blo 952587 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B3056287 : Blo 952587 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B13771471 : Blo 952587 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B4072639 : Blo 952587 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B4072673 : Blo 952587 4072673 := bstep (se 2 (by rfl) ⟨1527252, by rfl⟩ : syracuseStep 4072673 = 3054505) B3054505
theorem B6891203 : Blo 952587 6891203 := bstep (se 1 (by rfl) ⟨5168402, by rfl⟩ : syracuseStep 6891203 = 10336805) B10336805
theorem B4826951 : Blo 952587 4826951 := bstep (se 1 (by rfl) ⟨3620213, by rfl⟩ : syracuseStep 4826951 = 7240427) B7240427
theorem B3221801 : Blo 952587 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B13773179 : Blo 952587 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B3223259 : Blo 952587 3223259 := bstep (se 1 (by rfl) ⟨2417444, by rfl⟩ : syracuseStep 3223259 = 4834889) B4834889
theorem B16527091 : Blo 952587 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B4829543 : Blo 952587 4829543 := bstep (se 1 (by rfl) ⟨3622157, by rfl⟩ : syracuseStep 4829543 = 7244315) B7244315
theorem B3224015 : Blo 952587 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B2143727 : Blo 952587 2143727 := bstep (se 1 (by rfl) ⟨1607795, by rfl⟩ : syracuseStep 2143727 = 3215591) B3215591
theorem B3618377 : Blo 952587 3618377 := bstep (se 2 (by rfl) ⟨1356891, by rfl⟩ : syracuseStep 3618377 = 2713783) B2713783
theorem B2144303 : Blo 952587 2144303 := bstep (se 1 (by rfl) ⟨1608227, by rfl⟩ : syracuseStep 2144303 = 3216455) B3216455
theorem B1292447 : Blo 952587 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B2144609 : Blo 952587 2144609 := bstep (se 2 (by rfl) ⟨804228, by rfl⟩ : syracuseStep 2144609 = 1608457) B1608457
theorem B2145023 : Blo 952587 2145023 := bstep (se 1 (by rfl) ⟨1608767, by rfl⟩ : syracuseStep 2145023 = 3217535) B3217535
theorem B1358623 : Blo 952587 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B6110113 : Blo 952587 6110113 := bstep (se 2 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 6110113 = 4582585) B4582585
theorem B3620335 : Blo 952587 3620335 := bstep (se 1 (by rfl) ⟨2715251, by rfl⟩ : syracuseStep 3620335 = 5430503) B5430503
theorem B8143091 : Blo 952587 8143091 := bstep (se 1 (by rfl) ⟨6107318, by rfl⟩ : syracuseStep 8143091 = 12214637) B12214637
theorem B2146715 : Blo 952587 2146715 := bstep (se 1 (by rfl) ⟨1610036, by rfl⟩ : syracuseStep 2146715 = 3220073) B3220073
theorem B7455149 : Blo 952587 7455149 := bstep (se 3 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 7455149 = 2795681) B2795681
theorem B12239545 : Blo 952587 12239545 := bstep (se 2 (by rfl) ⟨4589829, by rfl⟩ : syracuseStep 12239545 = 9179659) B9179659
theorem B23217329 : Blo 952587 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B2147579 : Blo 952587 2147579 := bstep (se 1 (by rfl) ⟨1610684, by rfl⟩ : syracuseStep 2147579 = 3221369) B3221369
theorem B23250239 : Blo 952587 23250239 := bstep (se 1 (by rfl) ⟨17437679, by rfl⟩ : syracuseStep 23250239 = 34875359) B34875359
theorem B1361567 : Blo 952587 1361567 := bstep (se 1 (by rfl) ⟨1021175, by rfl⟩ : syracuseStep 1361567 = 2042351) B2042351
theorem B2148263 : Blo 952587 2148263 := bstep (se 1 (by rfl) ⟨1611197, by rfl⟩ : syracuseStep 2148263 = 3222395) B3222395
theorem B1526215 : Blo 952587 1526215 := bstep (se 1 (by rfl) ⟨1144661, by rfl⟩ : syracuseStep 1526215 = 2289323) B2289323
theorem B1657849 : Blo 952587 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B1429673 : Blo 952587 1429673 := bstep (se 2 (by rfl) ⟨536127, by rfl⟩ : syracuseStep 1429673 = 1072255) B1072255
theorem B1429727 : Blo 952587 1429727 := bstep (se 1 (by rfl) ⟨1072295, by rfl⟩ : syracuseStep 1429727 = 2144591) B2144591
theorem B2150639 : Blo 952587 2150639 := bstep (se 1 (by rfl) ⟨1612979, by rfl⟩ : syracuseStep 2150639 = 3225959) B3225959
theorem B4838777 : Blo 952587 4838777 := bstep (se 2 (by rfl) ⟨1814541, by rfl⟩ : syracuseStep 4838777 = 3629083) B3629083
theorem B22042219 : Blo 952587 22042219 := bstep (se 1 (by rfl) ⟨16531664, by rfl⟩ : syracuseStep 22042219 = 33063329) B33063329
theorem B7755695 : Blo 952587 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B1431887 : Blo 952587 1431887 := bstep (se 1 (by rfl) ⟨1073915, by rfl⟩ : syracuseStep 1431887 = 2147831) B2147831
theorem B1432511 : Blo 952587 1432511 := bstep (se 1 (by rfl) ⟨1074383, by rfl⟩ : syracuseStep 1432511 = 2148767) B2148767
theorem B1432679 : Blo 952587 1432679 := bstep (se 1 (by rfl) ⟨1074509, by rfl⟩ : syracuseStep 1432679 = 2149019) B2149019
theorem B1432745 : Blo 952587 1432745 := bstep (se 2 (by rfl) ⟨537279, by rfl⟩ : syracuseStep 1432745 = 1074559) B1074559
theorem B13950305 : Blo 952587 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B1433039 : Blo 952587 1433039 := bstep (se 1 (by rfl) ⟨1074779, by rfl⟩ : syracuseStep 1433039 = 2149559) B2149559
theorem B1433135 : Blo 952587 1433135 := bstep (se 1 (by rfl) ⟨1074851, by rfl⟩ : syracuseStep 1433135 = 2149703) B2149703
theorem B5430959 : Blo 952587 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B1433279 : Blo 952587 1433279 := bstep (se 1 (by rfl) ⟨1074959, by rfl⟩ : syracuseStep 1433279 = 2149919) B2149919
theorem B2416999 : Blo 952587 2416999 := bstep (se 1 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 2416999 = 3625499) B3625499
theorem B74245355 : Blo 952587 74245355 := bstep (se 1 (by rfl) ⟨55684016, by rfl⟩ : syracuseStep 74245355 = 111368033) B111368033
theorem B5301559 : Blo 952587 5301559 := bstep (se 1 (by rfl) ⟨3976169, by rfl⟩ : syracuseStep 5301559 = 7952339) B7952339
theorem B1074847 : Blo 952587 1074847 := bstep (se 1 (by rfl) ⟨806135, by rfl⟩ : syracuseStep 1074847 = 1612271) B1612271
theorem B29353913 : Blo 952587 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B1206895 : Blo 952587 1206895 := bstep (se 1 (by rfl) ⟨905171, by rfl⟩ : syracuseStep 1206895 = 1810343) B1810343
theorem B7433579 : Blo 952587 7433579 := bstep (se 1 (by rfl) ⟨5575184, by rfl⟩ : syracuseStep 7433579 = 11150369) B11150369
theorem B16315019 : Blo 952587 16315019 := bstep (se 1 (by rfl) ⟨12236264, by rfl⟩ : syracuseStep 16315019 = 24472529) B24472529
theorem B2585371 : Blo 952587 2585371 := bstep (se 1 (by rfl) ⟨1939028, by rfl⟩ : syracuseStep 2585371 = 3878057) B3878057
theorem B18315031 : Blo 952587 18315031 := bstep (se 1 (by rfl) ⟨13736273, by rfl⟩ : syracuseStep 18315031 = 27472547) B27472547
theorem B2717803 : Blo 952587 2717803 := bstep (se 1 (by rfl) ⟨2038352, by rfl⟩ : syracuseStep 2717803 = 4076705) B4076705
theorem B11632517 : Blo 952587 11632517 := bstep (se 4 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 11632517 = 2181097) B2181097
theorem B5439433 : Blo 952587 5439433 := bstep (se 2 (by rfl) ⟨2039787, by rfl⟩ : syracuseStep 5439433 = 4079575) B4079575
theorem B15500159 : Blo 952587 15500159 := bstep (se 1 (by rfl) ⟨11625119, by rfl⟩ : syracuseStep 15500159 = 23250239) B23250239
theorem B16319393 : Blo 952587 16319393 := bstep (se 2 (by rfl) ⟨6119772, by rfl⟩ : syracuseStep 16319393 = 12239545) B12239545
theorem B953115 : Blo 952587 953115 := bstep (se 1 (by rfl) ⟨714836, by rfl⟩ : syracuseStep 953115 = 1429673) B1429673
theorem B953151 : Blo 952587 953151 := bstep (se 1 (by rfl) ⟨714863, by rfl⟩ : syracuseStep 953151 = 1429727) B1429727
theorem B2034953 : Blo 952587 2034953 := bstep (se 2 (by rfl) ⟨763107, by rfl⟩ : syracuseStep 2034953 = 1526215) B1526215
theorem B1609193 : Blo 952587 1609193 := bstep (se 2 (by rfl) ⟨603447, by rfl⟩ : syracuseStep 1609193 = 1206895) B1206895
theorem B954591 : Blo 952587 954591 := bstep (se 1 (by rfl) ⟨715943, by rfl⟩ : syracuseStep 954591 = 1431887) B1431887
theorem B955007 : Blo 952587 955007 := bstep (se 1 (by rfl) ⟨716255, by rfl⟩ : syracuseStep 955007 = 1432511) B1432511
theorem B2036431 : Blo 952587 2036431 := bstep (se 1 (by rfl) ⟨1527323, by rfl⟩ : syracuseStep 2036431 = 3054647) B3054647
theorem B955119 : Blo 952587 955119 := bstep (se 1 (by rfl) ⟨716339, by rfl⟩ : syracuseStep 955119 = 1432679) B1432679
theorem B2036507 : Blo 952587 2036507 := bstep (se 1 (by rfl) ⟨1527380, by rfl⟩ : syracuseStep 2036507 = 3054761) B3054761
theorem B955163 : Blo 952587 955163 := bstep (se 1 (by rfl) ⟨716372, by rfl⟩ : syracuseStep 955163 = 1432745) B1432745
theorem B955359 : Blo 952587 955359 := bstep (se 1 (by rfl) ⟨716519, by rfl⟩ : syracuseStep 955359 = 1433039) B1433039
theorem B955423 : Blo 952587 955423 := bstep (se 1 (by rfl) ⟨716567, by rfl⟩ : syracuseStep 955423 = 1433135) B1433135
theorem B955519 : Blo 952587 955519 := bstep (se 1 (by rfl) ⟨716639, by rfl⟩ : syracuseStep 955519 = 1433279) B1433279
theorem B3446525 : Blo 952587 3446525 := bstep (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) B1292447
theorem B3447161 : Blo 952587 3447161 := bstep (se 2 (by rfl) ⟨1292685, by rfl⟩ : syracuseStep 3447161 = 2585371) B2585371
theorem B4823549 : Blo 952587 4823549 := bstep (se 3 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 4823549 = 1808831) B1808831
theorem B3217967 : Blo 952587 3217967 := bstep (se 1 (by rfl) ⟨2413475, by rfl⟩ : syracuseStep 3217967 = 4826951) B4826951
theorem B19569275 : Blo 952587 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B22027625 : Blo 952587 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B24420041 : Blo 952587 24420041 := bstep (se 2 (by rfl) ⟨9157515, by rfl⟩ : syracuseStep 24420041 = 18315031) B18315031
theorem B3219695 : Blo 952587 3219695 := bstep (se 1 (by rfl) ⟨2414771, by rfl⟩ : syracuseStep 3219695 = 4829543) B4829543
theorem B1811497 : Blo 952587 1811497 := bstep (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) B1358623
theorem B4827113 : Blo 952587 4827113 := bstep (se 2 (by rfl) ⟨1810167, by rfl⟩ : syracuseStep 4827113 = 3620335) B3620335
theorem B7252577 : Blo 952587 7252577 := bstep (se 2 (by rfl) ⟨2719716, by rfl⟩ : syracuseStep 7252577 = 5439433) B5439433
theorem B3222665 : Blo 952587 3222665 := bstep (se 2 (by rfl) ⟨1208499, by rfl⟩ : syracuseStep 3222665 = 2416999) B2416999
theorem B15478219 : Blo 952587 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B4075049 : Blo 952587 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B16297523 : Blo 952587 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B18361961 : Blo 952587 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B8171999 : Blo 952587 8171999 := bstep (se 1 (by rfl) ⟨6128999, by rfl⟩ : syracuseStep 8171999 = 12257999) B12257999
theorem B1816015 : Blo 952587 1816015 := bstep (se 1 (by rfl) ⟨1362011, by rfl⟩ : syracuseStep 1816015 = 2724023) B2724023
theorem B3225851 : Blo 952587 3225851 := bstep (se 1 (by rfl) ⟨2419388, by rfl⟩ : syracuseStep 3225851 = 4838777) B4838777
theorem B2210465 : Blo 952587 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B2145491 : Blo 952587 2145491 := bstep (se 1 (by rfl) ⟨1609118, by rfl⟩ : syracuseStep 2145491 = 3218237) B3218237
theorem B2145599 : Blo 952587 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B22036121 : Blo 952587 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B966335 : Blo 952587 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B3620639 : Blo 952587 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B2146985 : Blo 952587 2146985 := bstep (se 2 (by rfl) ⟨805119, by rfl⟩ : syracuseStep 2146985 = 1610239) B1610239
theorem B49496903 : Blo 952587 49496903 := bstep (se 1 (by rfl) ⟨37122677, by rfl⟩ : syracuseStep 49496903 = 74245355) B74245355
theorem B2147867 : Blo 952587 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B2148425 : Blo 952587 2148425 := bstep (se 2 (by rfl) ⟨805659, by rfl⟩ : syracuseStep 2148425 = 1611319) B1611319
theorem B2148839 : Blo 952587 2148839 := bstep (se 1 (by rfl) ⟨1611629, by rfl⟩ : syracuseStep 2148839 = 3223259) B3223259
theorem B3623737 : Blo 952587 3623737 := bstep (se 2 (by rfl) ⟨1358901, by rfl⟩ : syracuseStep 3623737 = 2717803) B2717803
theorem B2149343 : Blo 952587 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B1429151 : Blo 952587 1429151 := bstep (se 1 (by rfl) ⟨1071863, by rfl⟩ : syracuseStep 1429151 = 2143727) B2143727
theorem B2412251 : Blo 952587 2412251 := bstep (se 1 (by rfl) ⟨1809188, by rfl⟩ : syracuseStep 2412251 = 3618377) B3618377
theorem B8146817 : Blo 952587 8146817 := bstep (se 2 (by rfl) ⟨3055056, by rfl⟩ : syracuseStep 8146817 = 6110113) B6110113
theorem B1429535 : Blo 952587 1429535 := bstep (se 1 (by rfl) ⟨1072151, by rfl⟩ : syracuseStep 1429535 = 2144303) B2144303
theorem B1429739 : Blo 952587 1429739 := bstep (se 1 (by rfl) ⟨1072304, by rfl⟩ : syracuseStep 1429739 = 2144609) B2144609
theorem B1430015 : Blo 952587 1430015 := bstep (se 1 (by rfl) ⟨1072511, by rfl⟩ : syracuseStep 1430015 = 2145023) B2145023
theorem B2151593 : Blo 952587 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B7755011 : Blo 952587 7755011 := bstep (se 1 (by rfl) ⟨5816258, by rfl⟩ : syracuseStep 7755011 = 11632517) B11632517
theorem B5428727 : Blo 952587 5428727 := bstep (se 1 (by rfl) ⟨4071545, by rfl⟩ : syracuseStep 5428727 = 8143091) B8143091
theorem B47011387 : Blo 952587 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B1431143 : Blo 952587 1431143 := bstep (se 1 (by rfl) ⟨1073357, by rfl⟩ : syracuseStep 1431143 = 2146715) B2146715
theorem B4970099 : Blo 952587 4970099 := bstep (se 1 (by rfl) ⟨3727574, by rfl⟩ : syracuseStep 4970099 = 7455149) B7455149
theorem B1431719 : Blo 952587 1431719 := bstep (se 1 (by rfl) ⟨1073789, by rfl⟩ : syracuseStep 1431719 = 2147579) B2147579
theorem B1432175 : Blo 952587 1432175 := bstep (se 1 (by rfl) ⟨1074131, by rfl⟩ : syracuseStep 1432175 = 2148263) B2148263
theorem B1530623 : Blo 952587 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B5430185 : Blo 952587 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B7068745 : Blo 952587 7068745 := bstep (se 2 (by rfl) ⟨2650779, by rfl⟩ : syracuseStep 7068745 = 5301559) B5301559
theorem B1072543 : Blo 952587 1072543 := bstep (se 1 (by rfl) ⟨804407, by rfl⟩ : syracuseStep 1072543 = 1608815) B1608815
theorem B1433129 : Blo 952587 1433129 := bstep (se 2 (by rfl) ⟨537423, by rfl⟩ : syracuseStep 1433129 = 1074847) B1074847
theorem B1433759 : Blo 952587 1433759 := bstep (se 1 (by rfl) ⟨1075319, by rfl⟩ : syracuseStep 1433759 = 2150639) B2150639
theorem B1074415 : Blo 952587 1074415 := bstep (se 1 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 1074415 = 1611623) B1611623
theorem B5170463 : Blo 952587 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B3630527 : Blo 952587 3630527 := bstep (se 1 (by rfl) ⟨2722895, by rfl⟩ : syracuseStep 3630527 = 5445791) B5445791
theorem B3630845 : Blo 952587 3630845 := bstep (se 3 (by rfl) ⟨680783, by rfl⟩ : syracuseStep 3630845 = 1361567) B1361567
theorem B18376541 : Blo 952587 18376541 := bstep (se 3 (by rfl) ⟨3445601, by rfl⟩ : syracuseStep 18376541 = 6891203) B6891203
theorem B9300203 : Blo 952587 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B53701177 : Blo 952587 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B2715115 : Blo 952587 2715115 := bstep (se 1 (by rfl) ⟨2036336, by rfl⟩ : syracuseStep 2715115 = 4072673) B4072673
theorem B36728477 : Blo 952587 36728477 := bstep (se 3 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 36728477 = 13773179) B13773179
theorem B29389625 : Blo 952587 29389625 := bstep (se 2 (by rfl) ⟨11021109, by rfl⟩ : syracuseStep 29389625 = 22042219) B22042219
theorem B10876679 : Blo 952587 10876679 := bstep (se 1 (by rfl) ⟨8157509, by rfl⟩ : syracuseStep 10876679 = 16315019) B16315019
theorem B19822877 : Blo 952587 19822877 := bstep (se 3 (by rfl) ⟨3716789, by rfl⟩ : syracuseStep 19822877 = 7433579) B7433579
theorem B32997935 : Blo 952587 32997935 := bstep (se 1 (by rfl) ⟨24748451, by rfl⟩ : syracuseStep 32997935 = 49496903) B49496903
theorem B10879595 : Blo 952587 10879595 := bstep (se 1 (by rfl) ⟨8159696, by rfl⟩ : syracuseStep 10879595 = 16319393) B16319393
theorem B952767 : Blo 952587 952767 := bstep (se 1 (by rfl) ⟨714575, by rfl⟩ : syracuseStep 952767 = 1429151) B1429151
theorem B1608167 : Blo 952587 1608167 := bstep (se 1 (by rfl) ⟨1206125, by rfl⟩ : syracuseStep 1608167 = 2412251) B2412251
theorem B953023 : Blo 952587 953023 := bstep (se 1 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 953023 = 1429535) B1429535
theorem B953159 : Blo 952587 953159 := bstep (se 1 (by rfl) ⟨714869, by rfl⟩ : syracuseStep 953159 = 1429739) B1429739
theorem B953343 : Blo 952587 953343 := bstep (se 1 (by rfl) ⟨715007, by rfl⟩ : syracuseStep 953343 = 1430015) B1430015
theorem B71601569 : Blo 952587 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B954095 : Blo 952587 954095 := bstep (se 1 (by rfl) ⟨715571, by rfl⟩ : syracuseStep 954095 = 1431143) B1431143
theorem B3313399 : Blo 952587 3313399 := bstep (se 1 (by rfl) ⟨2485049, by rfl⟩ : syracuseStep 3313399 = 4970099) B4970099
theorem B2297683 : Blo 952587 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B954479 : Blo 952587 954479 := bstep (se 1 (by rfl) ⟨715859, by rfl⟩ : syracuseStep 954479 = 1431719) B1431719
theorem B2298107 : Blo 952587 2298107 := bstep (se 1 (by rfl) ⟨1723580, by rfl⟩ : syracuseStep 2298107 = 3447161) B3447161
theorem B3215699 : Blo 952587 3215699 := bstep (se 1 (by rfl) ⟨2411774, by rfl⟩ : syracuseStep 3215699 = 4823549) B4823549
theorem B954783 : Blo 952587 954783 := bstep (se 1 (by rfl) ⟨716087, by rfl⟩ : syracuseStep 954783 = 1432175) B1432175
theorem B13046183 : Blo 952587 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B14685083 : Blo 952587 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B955419 : Blo 952587 955419 := bstep (se 1 (by rfl) ⟨716564, by rfl⟩ : syracuseStep 955419 = 1433129) B1433129
theorem B955839 : Blo 952587 955839 := bstep (se 1 (by rfl) ⟨716879, by rfl⟩ : syracuseStep 955839 = 1433759) B1433759
theorem B3446975 : Blo 952587 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B3218075 : Blo 952587 3218075 := bstep (se 1 (by rfl) ⟨2413556, by rfl⟩ : syracuseStep 3218075 = 4827113) B4827113
theorem B6200135 : Blo 952587 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B82550501 : Blo 952587 82550501 := bstep (se 4 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 82550501 = 15478219) B15478219
theorem B24485651 : Blo 952587 24485651 := bstep (se 1 (by rfl) ⟨18364238, by rfl⟩ : syracuseStep 24485651 = 36728477) B36728477
theorem B5447999 : Blo 952587 5447999 := bstep (se 1 (by rfl) ⟨4085999, by rfl⟩ : syracuseStep 5447999 = 8171999) B8171999
theorem B7251119 : Blo 952587 7251119 := bstep (se 1 (by rfl) ⟨5438339, by rfl⟩ : syracuseStep 7251119 = 10876679) B10876679
theorem B13215251 : Blo 952587 13215251 := bstep (se 1 (by rfl) ⟨9911438, by rfl⟩ : syracuseStep 13215251 = 19822877) B19822877
theorem B14690747 : Blo 952587 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B10333439 : Blo 952587 10333439 := bstep (se 1 (by rfl) ⟨7750079, by rfl⟩ : syracuseStep 10333439 = 15500159) B15500159
theorem B1356635 : Blo 952587 1356635 := bstep (se 1 (by rfl) ⟨1017476, by rfl⟩ : syracuseStep 1356635 = 2034953) B2034953
theorem B3619151 : Blo 952587 3619151 := bstep (se 1 (by rfl) ⟨2714363, by rfl⟩ : syracuseStep 3619151 = 5428727) B5428727
theorem B4831649 : Blo 952587 4831649 := bstep (se 2 (by rfl) ⟨1811868, by rfl⟩ : syracuseStep 4831649 = 3623737) B3623737
theorem B2145311 : Blo 952587 2145311 := bstep (se 1 (by rfl) ⟨1608983, by rfl⟩ : syracuseStep 2145311 = 3217967) B3217967
theorem B3620123 : Blo 952587 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B3620153 : Blo 952587 3620153 := bstep (se 2 (by rfl) ⟨1357557, by rfl⟩ : syracuseStep 3620153 = 2715115) B2715115
theorem B2146463 : Blo 952587 2146463 := bstep (se 1 (by rfl) ⟨1609847, by rfl⟩ : syracuseStep 2146463 = 3219695) B3219695
theorem B4835051 : Blo 952587 4835051 := bstep (se 1 (by rfl) ⟨3626288, by rfl⟩ : syracuseStep 4835051 = 7252577) B7252577
theorem B10307573 : Blo 952587 10307573 := bstep (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) B966335
theorem B4081661 : Blo 952587 4081661 := bstep (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) B1530623
theorem B2148443 : Blo 952587 2148443 := bstep (se 1 (by rfl) ⟨1611332, by rfl⟩ : syracuseStep 2148443 = 3222665) B3222665
theorem B10865015 : Blo 952587 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B12241307 : Blo 952587 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B9424993 : Blo 952587 9424993 := bstep (se 2 (by rfl) ⟨3534372, by rfl⟩ : syracuseStep 9424993 = 7068745) B7068745
theorem B2150567 : Blo 952587 2150567 := bstep (se 1 (by rfl) ⟨1612925, by rfl⟩ : syracuseStep 2150567 = 3225851) B3225851
theorem B1430057 : Blo 952587 1430057 := bstep (se 2 (by rfl) ⟨536271, by rfl⟩ : syracuseStep 1430057 = 1072543) B1072543
theorem B1430327 : Blo 952587 1430327 := bstep (se 1 (by rfl) ⟨1072745, by rfl⟩ : syracuseStep 1430327 = 2145491) B2145491
theorem B1430399 : Blo 952587 1430399 := bstep (se 1 (by rfl) ⟨1072799, by rfl⟩ : syracuseStep 1430399 = 2145599) B2145599
theorem B2413759 : Blo 952587 2413759 := bstep (se 1 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 2413759 = 3620639) B3620639
theorem B1431323 : Blo 952587 1431323 := bstep (se 1 (by rfl) ⟨1073492, by rfl⟩ : syracuseStep 1431323 = 2146985) B2146985
theorem B1431911 : Blo 952587 1431911 := bstep (se 1 (by rfl) ⟨1073933, by rfl⟩ : syracuseStep 1431911 = 2147867) B2147867
theorem B1432283 : Blo 952587 1432283 := bstep (se 1 (by rfl) ⟨1074212, by rfl⟩ : syracuseStep 1432283 = 2148425) B2148425
theorem B2415329 : Blo 952587 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B1432553 : Blo 952587 1432553 := bstep (se 2 (by rfl) ⟨537207, by rfl⟩ : syracuseStep 1432553 = 1074415) B1074415
theorem B1432559 : Blo 952587 1432559 := bstep (se 1 (by rfl) ⟨1074419, by rfl⟩ : syracuseStep 1432559 = 2148839) B2148839
theorem B1432895 : Blo 952587 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B5430685 : Blo 952587 5430685 := bstep (se 3 (by rfl) ⟨1018253, by rfl⟩ : syracuseStep 5430685 = 2036507) B2036507
theorem B1072795 : Blo 952587 1072795 := bstep (se 1 (by rfl) ⟨804596, by rfl⟩ : syracuseStep 1072795 = 1609193) B1609193
theorem B5431211 : Blo 952587 5431211 := bstep (se 1 (by rfl) ⟨4073408, by rfl⟩ : syracuseStep 5431211 = 8146817) B8146817
theorem B1434395 : Blo 952587 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B5170007 : Blo 952587 5170007 := bstep (se 1 (by rfl) ⟨3877505, by rfl⟩ : syracuseStep 5170007 = 7755011) B7755011
theorem B16280027 : Blo 952587 16280027 := bstep (se 1 (by rfl) ⟨12210020, by rfl⟩ : syracuseStep 16280027 = 24420041) B24420041
theorem B2715241 : Blo 952587 2715241 := bstep (se 2 (by rfl) ⟨1018215, by rfl⟩ : syracuseStep 2715241 = 2036431) B2036431
theorem B2420351 : Blo 952587 2420351 := bstep (se 1 (by rfl) ⟨1815263, by rfl⟩ : syracuseStep 2420351 = 3630527) B3630527
theorem B2420563 : Blo 952587 2420563 := bstep (se 1 (by rfl) ⟨1815422, by rfl⟩ : syracuseStep 2420563 = 3630845) B3630845
theorem B12251027 : Blo 952587 12251027 := bstep (se 1 (by rfl) ⟨9188270, by rfl⟩ : syracuseStep 12251027 = 18376541) B18376541
theorem B2421353 : Blo 952587 2421353 := bstep (se 2 (by rfl) ⟨908007, by rfl⟩ : syracuseStep 2421353 = 1816015) B1816015
theorem B62681849 : Blo 952587 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B2716699 : Blo 952587 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B19593083 : Blo 952587 19593083 := bstep (se 1 (by rfl) ⟨14694812, by rfl⟩ : syracuseStep 19593083 = 29389625) B29389625
theorem B1473643 : Blo 952587 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B2721107 : Blo 952587 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B7243343 : Blo 952587 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B8160871 : Blo 952587 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B953371 : Blo 952587 953371 := bstep (se 1 (by rfl) ⟨715028, by rfl⟩ : syracuseStep 953371 = 1430057) B1430057
theorem B953551 : Blo 952587 953551 := bstep (se 1 (by rfl) ⟨715163, by rfl⟩ : syracuseStep 953551 = 1430327) B1430327
theorem B953599 : Blo 952587 953599 := bstep (se 1 (by rfl) ⟨715199, by rfl⟩ : syracuseStep 953599 = 1430399) B1430399
theorem B954215 : Blo 952587 954215 := bstep (se 1 (by rfl) ⟨715661, by rfl⟩ : syracuseStep 954215 = 1431323) B1431323
theorem B2297983 : Blo 952587 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B954607 : Blo 952587 954607 := bstep (se 1 (by rfl) ⟨715955, by rfl⟩ : syracuseStep 954607 = 1431911) B1431911
theorem B954855 : Blo 952587 954855 := bstep (se 1 (by rfl) ⟨716141, by rfl⟩ : syracuseStep 954855 = 1432283) B1432283
theorem B1610219 : Blo 952587 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B4133423 : Blo 952587 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B955035 : Blo 952587 955035 := bstep (se 1 (by rfl) ⟨716276, by rfl⟩ : syracuseStep 955035 = 1432553) B1432553
theorem B955039 : Blo 952587 955039 := bstep (se 1 (by rfl) ⟨716279, by rfl⟩ : syracuseStep 955039 = 1432559) B1432559
theorem B955263 : Blo 952587 955263 := bstep (se 1 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 955263 = 1432895) B1432895
theorem B16323767 : Blo 952587 16323767 := bstep (se 1 (by rfl) ⟨12242825, by rfl⟩ : syracuseStep 16323767 = 24485651) B24485651
theorem B956263 : Blo 952587 956263 := bstep (se 1 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 956263 = 1434395) B1434395
theorem B3446671 : Blo 952587 3446671 := bstep (se 1 (by rfl) ⟨2585003, by rfl⟩ : syracuseStep 3446671 = 5170007) B5170007
theorem B3218345 : Blo 952587 3218345 := bstep (se 2 (by rfl) ⟨1206879, by rfl⟩ : syracuseStep 3218345 = 2413759) B2413759
theorem B10853351 : Blo 952587 10853351 := bstep (se 1 (by rfl) ⟨8140013, by rfl⟩ : syracuseStep 10853351 = 16280027) B16280027
theorem B6888959 : Blo 952587 6888959 := bstep (se 1 (by rfl) ⟨5166719, by rfl⟩ : syracuseStep 6888959 = 10333439) B10333439
theorem B1613567 : Blo 952587 1613567 := bstep (se 1 (by rfl) ⟨1210175, by rfl⟩ : syracuseStep 1613567 = 2420351) B2420351
theorem B8167351 : Blo 952587 8167351 := bstep (se 1 (by rfl) ⟨6125513, by rfl⟩ : syracuseStep 8167351 = 12251027) B12251027
theorem B1614235 : Blo 952587 1614235 := bstep (se 1 (by rfl) ⟨1210676, by rfl⟩ : syracuseStep 1614235 = 2421353) B2421353
theorem B41787899 : Blo 952587 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B3221099 : Blo 952587 3221099 := bstep (se 1 (by rfl) ⟨2415824, by rfl⟩ : syracuseStep 3221099 = 4831649) B4831649
theorem B21998623 : Blo 952587 21998623 := bstep (se 1 (by rfl) ⟨16498967, by rfl⟩ : syracuseStep 21998623 = 32997935) B32997935
theorem B7253063 : Blo 952587 7253063 := bstep (se 1 (by rfl) ⟨5439797, by rfl⟩ : syracuseStep 7253063 = 10879595) B10879595
theorem B3223367 : Blo 952587 3223367 := bstep (se 1 (by rfl) ⟨2417525, by rfl⟩ : syracuseStep 3223367 = 4835051) B4835051
theorem B3617693 : Blo 952587 3617693 := bstep (se 3 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 3617693 = 1356635) B1356635
theorem B2143799 : Blo 952587 2143799 := bstep (se 1 (by rfl) ⟨1607849, by rfl⟩ : syracuseStep 2143799 = 3215699) B3215699
theorem B8697455 : Blo 952587 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B2145383 : Blo 952587 2145383 := bstep (se 1 (by rfl) ⟨1609037, by rfl⟩ : syracuseStep 2145383 = 3218075) B3218075
theorem B3620321 : Blo 952587 3620321 := bstep (se 2 (by rfl) ⟨1357620, by rfl⟩ : syracuseStep 3620321 = 2715241) B2715241
theorem B3227417 : Blo 952587 3227417 := bstep (se 2 (by rfl) ⟨1210281, by rfl⟩ : syracuseStep 3227417 = 2420563) B2420563
theorem B3063577 : Blo 952587 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B55033667 : Blo 952587 55033667 := bstep (se 1 (by rfl) ⟨41275250, by rfl⟩ : syracuseStep 55033667 = 82550501) B82550501
theorem B3620807 : Blo 952587 3620807 := bstep (se 1 (by rfl) ⟨2715605, by rfl⟩ : syracuseStep 3620807 = 5431211) B5431211
theorem B12566657 : Blo 952587 12566657 := bstep (se 2 (by rfl) ⟨4712496, by rfl⟩ : syracuseStep 12566657 = 9424993) B9424993
theorem B4834079 : Blo 952587 4834079 := bstep (se 1 (by rfl) ⟨3625559, by rfl⟩ : syracuseStep 4834079 = 7251119) B7251119
theorem B3622265 : Blo 952587 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B13062055 : Blo 952587 13062055 := bstep (se 1 (by rfl) ⟨9796541, by rfl⟩ : syracuseStep 13062055 = 19593083) B19593083
theorem B2412767 : Blo 952587 2412767 := bstep (se 1 (by rfl) ⟨1809575, by rfl⟩ : syracuseStep 2412767 = 3619151) B3619151
theorem B1430207 : Blo 952587 1430207 := bstep (se 1 (by rfl) ⟨1072655, by rfl⟩ : syracuseStep 1430207 = 2145311) B2145311
theorem B2413415 : Blo 952587 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B1430393 : Blo 952587 1430393 := bstep (se 2 (by rfl) ⟨536397, by rfl⟩ : syracuseStep 1430393 = 1072795) B1072795
theorem B2413435 : Blo 952587 2413435 := bstep (se 1 (by rfl) ⟨1810076, by rfl⟩ : syracuseStep 2413435 = 3620153) B3620153
theorem B1430975 : Blo 952587 1430975 := bstep (se 1 (by rfl) ⟨1073231, by rfl⟩ : syracuseStep 1430975 = 2146463) B2146463
theorem B6871715 : Blo 952587 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B1432295 : Blo 952587 1432295 := bstep (se 1 (by rfl) ⟨1074221, by rfl⟩ : syracuseStep 1432295 = 2148443) B2148443
theorem B1072111 : Blo 952587 1072111 := bstep (se 1 (by rfl) ⟨804083, by rfl⟩ : syracuseStep 1072111 = 1608167) B1608167
theorem B47734379 : Blo 952587 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B1433711 : Blo 952587 1433711 := bstep (se 1 (by rfl) ⟨1075283, by rfl⟩ : syracuseStep 1433711 = 2150567) B2150567
theorem B1532071 : Blo 952587 1532071 := bstep (se 1 (by rfl) ⟨1149053, by rfl⟩ : syracuseStep 1532071 = 2298107) B2298107
theorem B9790055 : Blo 952587 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B4417865 : Blo 952587 4417865 := bstep (se 2 (by rfl) ⟨1656699, by rfl⟩ : syracuseStep 4417865 = 3313399) B3313399
theorem B3631999 : Blo 952587 3631999 := bstep (se 1 (by rfl) ⟨2723999, by rfl⟩ : syracuseStep 3631999 = 5447999) B5447999
theorem B7859429 : Blo 952587 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B8810167 : Blo 952587 8810167 := bstep (se 1 (by rfl) ⟨6607625, by rfl⟩ : syracuseStep 8810167 = 13215251) B13215251
theorem B9793831 : Blo 952587 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B7240913 : Blo 952587 7240913 := bstep (se 2 (by rfl) ⟨2715342, by rfl⟩ : syracuseStep 7240913 = 5430685) B5430685
theorem B10881161 : Blo 952587 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B1608511 : Blo 952587 1608511 := bstep (se 1 (by rfl) ⟨1206383, by rfl⟩ : syracuseStep 1608511 = 2412767) B2412767
theorem B2755615 : Blo 952587 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B953471 : Blo 952587 953471 := bstep (se 1 (by rfl) ⟨715103, by rfl⟩ : syracuseStep 953471 = 1430207) B1430207
theorem B1608943 : Blo 952587 1608943 := bstep (se 1 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 1608943 = 2413415) B2413415
theorem B953595 : Blo 952587 953595 := bstep (se 1 (by rfl) ⟨715196, by rfl⟩ : syracuseStep 953595 = 1430393) B1430393
theorem B10882511 : Blo 952587 10882511 := bstep (se 1 (by rfl) ⟨8161883, by rfl⟩ : syracuseStep 10882511 = 16323767) B16323767
theorem B953983 : Blo 952587 953983 := bstep (se 1 (by rfl) ⟨715487, by rfl⟩ : syracuseStep 953983 = 1430975) B1430975
theorem B29331497 : Blo 952587 29331497 := bstep (se 2 (by rfl) ⟨10999311, by rfl⟩ : syracuseStep 29331497 = 21998623) B21998623
theorem B954863 : Blo 952587 954863 := bstep (se 1 (by rfl) ⟨716147, by rfl⟩ : syracuseStep 954863 = 1432295) B1432295
theorem B4592639 : Blo 952587 4592639 := bstep (se 1 (by rfl) ⟨3444479, by rfl⟩ : syracuseStep 4592639 = 6888959) B6888959
theorem B31822919 : Blo 952587 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B955807 : Blo 952587 955807 := bstep (se 1 (by rfl) ⟨716855, by rfl⟩ : syracuseStep 955807 = 1433711) B1433711
theorem B27858599 : Blo 952587 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B6526703 : Blo 952587 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B3217913 : Blo 952587 3217913 := bstep (se 2 (by rfl) ⟨1206717, by rfl⟩ : syracuseStep 3217913 = 2413435) B2413435
theorem B4595561 : Blo 952587 4595561 := bstep (se 2 (by rfl) ⟨1723335, by rfl⟩ : syracuseStep 4595561 = 3446671) B3446671
theorem B4827275 : Blo 952587 4827275 := bstep (se 1 (by rfl) ⟨3620456, by rfl⟩ : syracuseStep 4827275 = 7240913) B7240913
theorem B10889801 : Blo 952587 10889801 := bstep (se 2 (by rfl) ⟨4083675, by rfl⟩ : syracuseStep 10889801 = 8167351) B8167351
theorem B2042761 : Blo 952587 2042761 := bstep (se 2 (by rfl) ⟨766035, by rfl⟩ : syracuseStep 2042761 = 1532071) B1532071
theorem B3222719 : Blo 952587 3222719 := bstep (se 1 (by rfl) ⟨2417039, by rfl⟩ : syracuseStep 3222719 = 4834079) B4834079
theorem B1814071 : Blo 952587 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B4828895 : Blo 952587 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B2145563 : Blo 952587 2145563 := bstep (se 1 (by rfl) ⟨1609172, by rfl⟩ : syracuseStep 2145563 = 3218345) B3218345
theorem B11746889 : Blo 952587 11746889 := bstep (se 2 (by rfl) ⟨4405083, by rfl⟩ : syracuseStep 11746889 = 8810167) B8810167
theorem B17416073 : Blo 952587 17416073 := bstep (se 2 (by rfl) ⟨6531027, by rfl⟩ : syracuseStep 17416073 = 13062055) B13062055
theorem B3063977 : Blo 952587 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B13058441 : Blo 952587 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B2147399 : Blo 952587 2147399 := bstep (se 1 (by rfl) ⟨1610549, by rfl⟩ : syracuseStep 2147399 = 3221099) B3221099
theorem B4835375 : Blo 952587 4835375 := bstep (se 1 (by rfl) ⟨3626531, by rfl⟩ : syracuseStep 4835375 = 7253063) B7253063
theorem B2148911 : Blo 952587 2148911 := bstep (se 1 (by rfl) ⟨1611683, by rfl⟩ : syracuseStep 2148911 = 3223367) B3223367
theorem B2411795 : Blo 952587 2411795 := bstep (se 1 (by rfl) ⟨1808846, by rfl⟩ : syracuseStep 2411795 = 3617693) B3617693
theorem B1429199 : Blo 952587 1429199 := bstep (se 1 (by rfl) ⟨1071899, by rfl⟩ : syracuseStep 1429199 = 2143799) B2143799
theorem B1429481 : Blo 952587 1429481 := bstep (se 2 (by rfl) ⟨536055, by rfl⟩ : syracuseStep 1429481 = 1072111) B1072111
theorem B1430255 : Blo 952587 1430255 := bstep (se 1 (by rfl) ⟨1072691, by rfl⟩ : syracuseStep 1430255 = 2145383) B2145383
theorem B2413547 : Blo 952587 2413547 := bstep (se 1 (by rfl) ⟨1810160, by rfl⟩ : syracuseStep 2413547 = 3620321) B3620321
theorem B4084769 : Blo 952587 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B2151611 : Blo 952587 2151611 := bstep (se 1 (by rfl) ⟨1613708, by rfl⟩ : syracuseStep 2151611 = 3227417) B3227417
theorem B36689111 : Blo 952587 36689111 := bstep (se 1 (by rfl) ⟨27516833, by rfl⟩ : syracuseStep 36689111 = 55033667) B55033667
theorem B2413871 : Blo 952587 2413871 := bstep (se 1 (by rfl) ⟨1810403, by rfl⟩ : syracuseStep 2413871 = 3620807) B3620807
theorem B8377771 : Blo 952587 8377771 := bstep (se 1 (by rfl) ⟨6283328, by rfl⟩ : syracuseStep 8377771 = 12566657) B12566657
theorem B2152313 : Blo 952587 2152313 := bstep (se 2 (by rfl) ⟨807117, by rfl⟩ : syracuseStep 2152313 = 1614235) B1614235
theorem B2414843 : Blo 952587 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1073479 : Blo 952587 1073479 := bstep (se 1 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 1073479 = 1610219) B1610219
theorem B4842665 : Blo 952587 4842665 := bstep (se 2 (by rfl) ⟨1815999, by rfl⟩ : syracuseStep 4842665 = 3631999) B3631999
theorem B4581143 : Blo 952587 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B7235567 : Blo 952587 7235567 := bstep (se 1 (by rfl) ⟨5426675, by rfl⟩ : syracuseStep 7235567 = 10853351) B10853351
theorem B1075711 : Blo 952587 1075711 := bstep (se 1 (by rfl) ⟨806783, by rfl⟩ : syracuseStep 1075711 = 1613567) B1613567
theorem B2945243 : Blo 952587 2945243 := bstep (se 1 (by rfl) ⟨2208932, by rfl⟩ : syracuseStep 2945243 = 4417865) B4417865
theorem B5239619 : Blo 952587 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B5798303 : Blo 952587 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B78217325 : Blo 952587 78217325 := bstep (se 3 (by rfl) ⟨14665748, by rfl⟩ : syracuseStep 78217325 = 29331497) B29331497
theorem B1607863 : Blo 952587 1607863 := bstep (se 1 (by rfl) ⟨1205897, by rfl⟩ : syracuseStep 1607863 = 2411795) B2411795
theorem B952799 : Blo 952587 952799 := bstep (se 1 (by rfl) ⟨714599, by rfl⟩ : syracuseStep 952799 = 1429199) B1429199
theorem B952987 : Blo 952587 952987 := bstep (se 1 (by rfl) ⟨714740, by rfl⟩ : syracuseStep 952987 = 1429481) B1429481
theorem B953503 : Blo 952587 953503 := bstep (se 1 (by rfl) ⟨715127, by rfl⟩ : syracuseStep 953503 = 1430255) B1430255
theorem B1609031 : Blo 952587 1609031 := bstep (se 1 (by rfl) ⟨1206773, by rfl⟩ : syracuseStep 1609031 = 2413547) B2413547
theorem B1609247 : Blo 952587 1609247 := bstep (se 1 (by rfl) ⟨1206935, by rfl⟩ : syracuseStep 1609247 = 2413871) B2413871
theorem B2723681 : Blo 952587 2723681 := bstep (se 2 (by rfl) ⟨1021380, by rfl⟩ : syracuseStep 2723681 = 2042761) B2042761
theorem B3674153 : Blo 952587 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B1609895 : Blo 952587 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B17404541 : Blo 952587 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B3054095 : Blo 952587 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B4823711 : Blo 952587 4823711 := bstep (se 1 (by rfl) ⟨3617783, by rfl⟩ : syracuseStep 4823711 = 7235567) B7235567
theorem B3218183 : Blo 952587 3218183 := bstep (se 1 (by rfl) ⟨2413637, by rfl⟩ : syracuseStep 3218183 = 4827275) B4827275
theorem B3219263 : Blo 952587 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B11610715 : Blo 952587 11610715 := bstep (se 1 (by rfl) ⟨8708036, by rfl⟩ : syracuseStep 11610715 = 17416073) B17416073
theorem B2042651 : Blo 952587 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B3223583 : Blo 952587 3223583 := bstep (se 1 (by rfl) ⟨2417687, by rfl⟩ : syracuseStep 3223583 = 4835375) B4835375
theorem B7254107 : Blo 952587 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B7255007 : Blo 952587 7255007 := bstep (se 1 (by rfl) ⟨5441255, by rfl⟩ : syracuseStep 7255007 = 10882511) B10882511
theorem B10892717 : Blo 952587 10892717 := bstep (se 3 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 10892717 = 4084769) B4084769
theorem B3061759 : Blo 952587 3061759 := bstep (se 1 (by rfl) ⟨2296319, by rfl⟩ : syracuseStep 3061759 = 4592639) B4592639
theorem B21215279 : Blo 952587 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B24459407 : Blo 952587 24459407 := bstep (se 1 (by rfl) ⟨18344555, by rfl⟩ : syracuseStep 24459407 = 36689111) B36689111
theorem B2144681 : Blo 952587 2144681 := bstep (se 2 (by rfl) ⟨804255, by rfl⟩ : syracuseStep 2144681 = 1608511) B1608511
theorem B2145257 : Blo 952587 2145257 := bstep (se 2 (by rfl) ⟨804471, by rfl⟩ : syracuseStep 2145257 = 1608943) B1608943
theorem B2145275 : Blo 952587 2145275 := bstep (se 1 (by rfl) ⟨1608956, by rfl⟩ : syracuseStep 2145275 = 3217913) B3217913
theorem B3063707 : Blo 952587 3063707 := bstep (se 1 (by rfl) ⟨2297780, by rfl⟩ : syracuseStep 3063707 = 4595561) B4595561
theorem B3228443 : Blo 952587 3228443 := bstep (se 1 (by rfl) ⟨2421332, by rfl⟩ : syracuseStep 3228443 = 4842665) B4842665
theorem B7259867 : Blo 952587 7259867 := bstep (se 1 (by rfl) ⟨5444900, by rfl⟩ : syracuseStep 7259867 = 10889801) B10889801
theorem B2148479 : Blo 952587 2148479 := bstep (se 1 (by rfl) ⟨1611359, by rfl⟩ : syracuseStep 2148479 = 3222719) B3222719
theorem B3493079 : Blo 952587 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B1430375 : Blo 952587 1430375 := bstep (se 1 (by rfl) ⟨1072781, by rfl⟩ : syracuseStep 1430375 = 2145563) B2145563
theorem B8705627 : Blo 952587 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B1431305 : Blo 952587 1431305 := bstep (se 2 (by rfl) ⟨536739, by rfl⟩ : syracuseStep 1431305 = 1073479) B1073479
theorem B1431599 : Blo 952587 1431599 := bstep (se 1 (by rfl) ⟨1073699, by rfl⟩ : syracuseStep 1431599 = 2147399) B2147399
theorem B1432607 : Blo 952587 1432607 := bstep (se 1 (by rfl) ⟨1074455, by rfl⟩ : syracuseStep 1432607 = 2148911) B2148911
theorem B1434281 : Blo 952587 1434281 := bstep (se 2 (by rfl) ⟨537855, by rfl⟩ : syracuseStep 1434281 = 1075711) B1075711
theorem B1434407 : Blo 952587 1434407 := bstep (se 1 (by rfl) ⟨1075805, by rfl⟩ : syracuseStep 1434407 = 2151611) B2151611
theorem B18572399 : Blo 952587 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B1434875 : Blo 952587 1434875 := bstep (se 1 (by rfl) ⟨1076156, by rfl⟩ : syracuseStep 1434875 = 2152313) B2152313
theorem B2418761 : Blo 952587 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B11170361 : Blo 952587 11170361 := bstep (se 2 (by rfl) ⟨4188885, by rfl⟩ : syracuseStep 11170361 = 8377771) B8377771
theorem B1963495 : Blo 952587 1963495 := bstep (se 1 (by rfl) ⟨1472621, by rfl⟩ : syracuseStep 1963495 = 2945243) B2945243
theorem B3865535 : Blo 952587 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B7831259 : Blo 952587 7831259 := bstep (se 1 (by rfl) ⟨5873444, by rfl⟩ : syracuseStep 7831259 = 11746889) B11746889
theorem B37259509 : Blo 952587 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B11603027 : Blo 952587 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B953583 : Blo 952587 953583 := bstep (se 1 (by rfl) ⟨715187, by rfl⟩ : syracuseStep 953583 = 1430375) B1430375
theorem B5803751 : Blo 952587 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B954203 : Blo 952587 954203 := bstep (se 1 (by rfl) ⟨715652, by rfl⟩ : syracuseStep 954203 = 1431305) B1431305
theorem B954399 : Blo 952587 954399 := bstep (se 1 (by rfl) ⟨715799, by rfl⟩ : syracuseStep 954399 = 1431599) B1431599
theorem B2036063 : Blo 952587 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B3215807 : Blo 952587 3215807 := bstep (se 1 (by rfl) ⟨2411855, by rfl⟩ : syracuseStep 3215807 = 4823711) B4823711
theorem B955071 : Blo 952587 955071 := bstep (se 1 (by rfl) ⟨716303, by rfl⟩ : syracuseStep 955071 = 1432607) B1432607
theorem B956187 : Blo 952587 956187 := bstep (se 1 (by rfl) ⟨717140, by rfl⟩ : syracuseStep 956187 = 1434281) B1434281
theorem B956271 : Blo 952587 956271 := bstep (se 1 (by rfl) ⟨717203, by rfl⟩ : syracuseStep 956271 = 1434407) B1434407
theorem B956583 : Blo 952587 956583 := bstep (se 1 (by rfl) ⟨717437, by rfl⟩ : syracuseStep 956583 = 1434875) B1434875
theorem B1612507 : Blo 952587 1612507 := bstep (se 1 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 1612507 = 2418761) B2418761
theorem B7446907 : Blo 952587 7446907 := bstep (se 1 (by rfl) ⟨5585180, by rfl⟩ : syracuseStep 7446907 = 11170361) B11170361
theorem B5220839 : Blo 952587 5220839 := bstep (se 1 (by rfl) ⟨3915629, by rfl⟩ : syracuseStep 5220839 = 7831259) B7831259
theorem B2042471 : Blo 952587 2042471 := bstep (se 1 (by rfl) ⟨1531853, by rfl⟩ : syracuseStep 2042471 = 3063707) B3063707
theorem B52144883 : Blo 952587 52144883 := bstep (se 1 (by rfl) ⟨39108662, by rfl⟩ : syracuseStep 52144883 = 78217325) B78217325
theorem B1815787 : Blo 952587 1815787 := bstep (se 1 (by rfl) ⟨1361840, by rfl⟩ : syracuseStep 1815787 = 2723681) B2723681
theorem B2143817 : Blo 952587 2143817 := bstep (se 2 (by rfl) ⟨803931, by rfl⟩ : syracuseStep 2143817 = 1607863) B1607863
theorem B15480953 : Blo 952587 15480953 := bstep (se 2 (by rfl) ⟨5805357, by rfl⟩ : syracuseStep 15480953 = 11610715) B11610715
theorem B2145455 : Blo 952587 2145455 := bstep (se 1 (by rfl) ⟨1609091, by rfl⟩ : syracuseStep 2145455 = 3218183) B3218183
theorem B2146175 : Blo 952587 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B1361767 : Blo 952587 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B4082345 : Blo 952587 4082345 := bstep (se 2 (by rfl) ⟨1530879, by rfl⟩ : syracuseStep 4082345 = 3061759) B3061759
theorem B2149055 : Blo 952587 2149055 := bstep (se 1 (by rfl) ⟨1611791, by rfl⟩ : syracuseStep 2149055 = 3223583) B3223583
theorem B4836071 : Blo 952587 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B4836671 : Blo 952587 4836671 := bstep (se 1 (by rfl) ⟨3627503, by rfl⟩ : syracuseStep 4836671 = 7255007) B7255007
theorem B7261811 : Blo 952587 7261811 := bstep (se 1 (by rfl) ⟨5446358, by rfl⟩ : syracuseStep 7261811 = 10892717) B10892717
theorem B14143519 : Blo 952587 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B16306271 : Blo 952587 16306271 := bstep (se 1 (by rfl) ⟨12229703, by rfl⟩ : syracuseStep 16306271 = 24459407) B24459407
theorem B1429787 : Blo 952587 1429787 := bstep (se 1 (by rfl) ⟨1072340, by rfl⟩ : syracuseStep 1429787 = 2144681) B2144681
theorem B2577023 : Blo 952587 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B1430171 : Blo 952587 1430171 := bstep (se 1 (by rfl) ⟨1072628, by rfl⟩ : syracuseStep 1430171 = 2145257) B2145257
theorem B1430183 : Blo 952587 1430183 := bstep (se 1 (by rfl) ⟨1072637, by rfl⟩ : syracuseStep 1430183 = 2145275) B2145275
theorem B2152295 : Blo 952587 2152295 := bstep (se 1 (by rfl) ⟨1614221, by rfl⟩ : syracuseStep 2152295 = 3228443) B3228443
theorem B4839911 : Blo 952587 4839911 := bstep (se 1 (by rfl) ⟨3629933, by rfl⟩ : syracuseStep 4839911 = 7259867) B7259867
theorem B1432319 : Blo 952587 1432319 := bstep (se 1 (by rfl) ⟨1074239, by rfl⟩ : syracuseStep 1432319 = 2148479) B2148479
theorem B1072687 : Blo 952587 1072687 := bstep (se 1 (by rfl) ⟨804515, by rfl⟩ : syracuseStep 1072687 = 1609031) B1609031
theorem B1072831 : Blo 952587 1072831 := bstep (se 1 (by rfl) ⟨804623, by rfl⟩ : syracuseStep 1072831 = 1609247) B1609247
theorem B2449435 : Blo 952587 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B1073263 : Blo 952587 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B12381599 : Blo 952587 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B2617993 : Blo 952587 2617993 := bstep (se 2 (by rfl) ⟨981747, by rfl⟩ : syracuseStep 2617993 = 1963495) B1963495
theorem B2721563 : Blo 952587 2721563 := bstep (se 1 (by rfl) ⟨2041172, by rfl⟩ : syracuseStep 2721563 = 4082345) B4082345
theorem B39716837 : Blo 952587 39716837 := bstep (se 4 (by rfl) ⟨3723453, by rfl⟩ : syracuseStep 39716837 = 7446907) B7446907
theorem B7735351 : Blo 952587 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B953191 : Blo 952587 953191 := bstep (se 1 (by rfl) ⟨714893, by rfl⟩ : syracuseStep 953191 = 1429787) B1429787
theorem B49679345 : Blo 952587 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B953447 : Blo 952587 953447 := bstep (se 1 (by rfl) ⟨715085, by rfl⟩ : syracuseStep 953447 = 1430171) B1430171
theorem B953455 : Blo 952587 953455 := bstep (se 1 (by rfl) ⟨715091, by rfl⟩ : syracuseStep 953455 = 1430183) B1430183
theorem B954879 : Blo 952587 954879 := bstep (se 1 (by rfl) ⟨716159, by rfl⟩ : syracuseStep 954879 = 1432319) B1432319
theorem B15476669 : Blo 952587 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B3224447 : Blo 952587 3224447 := bstep (se 1 (by rfl) ⟨2418335, by rfl⟩ : syracuseStep 3224447 = 4836671) B4836671
theorem B1815689 : Blo 952587 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B2143871 : Blo 952587 2143871 := bstep (se 1 (by rfl) ⟨1607903, by rfl⟩ : syracuseStep 2143871 = 3215807) B3215807
theorem B1718015 : Blo 952587 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B3226607 : Blo 952587 3226607 := bstep (se 1 (by rfl) ⟨2419955, by rfl⟩ : syracuseStep 3226607 = 4839911) B4839911
theorem B18858025 : Blo 952587 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B3490657 : Blo 952587 3490657 := bstep (se 2 (by rfl) ⟨1308996, by rfl⟩ : syracuseStep 3490657 = 2617993) B2617993
theorem B1361647 : Blo 952587 1361647 := bstep (se 1 (by rfl) ⟨1021235, by rfl⟩ : syracuseStep 1361647 = 2042471) B2042471
theorem B12896189 : Blo 952587 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B2150009 : Blo 952587 2150009 := bstep (se 2 (by rfl) ⟨806253, by rfl⟩ : syracuseStep 2150009 = 1612507) B1612507
theorem B1429211 : Blo 952587 1429211 := bstep (se 1 (by rfl) ⟨1071908, by rfl⟩ : syracuseStep 1429211 = 2143817) B2143817
theorem B1430249 : Blo 952587 1430249 := bstep (se 2 (by rfl) ⟨536343, by rfl⟩ : syracuseStep 1430249 = 1072687) B1072687
theorem B1430303 : Blo 952587 1430303 := bstep (se 1 (by rfl) ⟨1072727, by rfl⟩ : syracuseStep 1430303 = 2145455) B2145455
theorem B1430441 : Blo 952587 1430441 := bstep (se 2 (by rfl) ⟨536415, by rfl⟩ : syracuseStep 1430441 = 1072831) B1072831
theorem B1430783 : Blo 952587 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B3265913 : Blo 952587 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B1431017 : Blo 952587 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B5429501 : Blo 952587 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B1432703 : Blo 952587 1432703 := bstep (se 1 (by rfl) ⟨1074527, by rfl⟩ : syracuseStep 1432703 = 2149055) B2149055
theorem B4841207 : Blo 952587 4841207 := bstep (se 1 (by rfl) ⟨3630905, by rfl⟩ : syracuseStep 4841207 = 7261811) B7261811
theorem B10870847 : Blo 952587 10870847 := bstep (se 1 (by rfl) ⟨8153135, by rfl⟩ : syracuseStep 10870847 = 16306271) B16306271
theorem B1434863 : Blo 952587 1434863 := bstep (se 1 (by rfl) ⟨1076147, by rfl⟩ : syracuseStep 1434863 = 2152295) B2152295
theorem B13922237 : Blo 952587 13922237 := bstep (se 3 (by rfl) ⟨2610419, by rfl⟩ : syracuseStep 13922237 = 5220839) B5220839
theorem B2421049 : Blo 952587 2421049 := bstep (se 2 (by rfl) ⟨907893, by rfl⟩ : syracuseStep 2421049 = 1815787) B1815787
theorem B34763255 : Blo 952587 34763255 := bstep (se 1 (by rfl) ⟨26072441, by rfl⟩ : syracuseStep 34763255 = 52144883) B52144883
theorem B8254399 : Blo 952587 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B10320635 : Blo 952587 10320635 := bstep (se 1 (by rfl) ⟨7740476, by rfl⟩ : syracuseStep 10320635 = 15480953) B15480953
theorem B26477891 : Blo 952587 26477891 := bstep (se 1 (by rfl) ⟨19858418, by rfl⟩ : syracuseStep 26477891 = 39716837) B39716837
theorem B952807 : Blo 952587 952807 := bstep (se 1 (by rfl) ⟨714605, by rfl⟩ : syracuseStep 952807 = 1429211) B1429211
theorem B953499 : Blo 952587 953499 := bstep (se 1 (by rfl) ⟨715124, by rfl⟩ : syracuseStep 953499 = 1430249) B1430249
theorem B953535 : Blo 952587 953535 := bstep (se 1 (by rfl) ⟨715151, by rfl⟩ : syracuseStep 953535 = 1430303) B1430303
theorem B953627 : Blo 952587 953627 := bstep (se 1 (by rfl) ⟨715220, by rfl⟩ : syracuseStep 953627 = 1430441) B1430441
theorem B953855 : Blo 952587 953855 := bstep (se 1 (by rfl) ⟨715391, by rfl⟩ : syracuseStep 953855 = 1430783) B1430783
theorem B954011 : Blo 952587 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B18616837 : Blo 952587 18616837 := bstep (se 4 (by rfl) ⟨1745328, by rfl⟩ : syracuseStep 18616837 = 3490657) B3490657
theorem B955135 : Blo 952587 955135 := bstep (se 1 (by rfl) ⟨716351, by rfl⟩ : syracuseStep 955135 = 1432703) B1432703
theorem B7247231 : Blo 952587 7247231 := bstep (se 1 (by rfl) ⟨5435423, by rfl⟩ : syracuseStep 7247231 = 10870847) B10870847
theorem B956575 : Blo 952587 956575 := bstep (se 1 (by rfl) ⟨717431, by rfl⟩ : syracuseStep 956575 = 1434863) B1434863
theorem B23175503 : Blo 952587 23175503 := bstep (se 1 (by rfl) ⟨17381627, by rfl⟩ : syracuseStep 23175503 = 34763255) B34763255
theorem B100576133 : Blo 952587 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B1814375 : Blo 952587 1814375 := bstep (se 1 (by rfl) ⟨1360781, by rfl⟩ : syracuseStep 1814375 = 2721563) B2721563
theorem B8597459 : Blo 952587 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B1815529 : Blo 952587 1815529 := bstep (se 2 (by rfl) ⟨680823, by rfl⟩ : syracuseStep 1815529 = 1361647) B1361647
theorem B2177275 : Blo 952587 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B3619667 : Blo 952587 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B3227471 : Blo 952587 3227471 := bstep (se 1 (by rfl) ⟨2420603, by rfl⟩ : syracuseStep 3227471 = 4841207) B4841207
theorem B3228065 : Blo 952587 3228065 := bstep (se 2 (by rfl) ⟨1210524, by rfl⟩ : syracuseStep 3228065 = 2421049) B2421049
theorem B2149631 : Blo 952587 2149631 := bstep (se 1 (by rfl) ⟨1612223, by rfl⟩ : syracuseStep 2149631 = 3224447) B3224447
theorem B1429247 : Blo 952587 1429247 := bstep (se 1 (by rfl) ⟨1071935, by rfl⟩ : syracuseStep 1429247 = 2143871) B2143871
theorem B2151071 : Blo 952587 2151071 := bstep (se 1 (by rfl) ⟨1613303, by rfl⟩ : syracuseStep 2151071 = 3226607) B3226607
theorem B33119563 : Blo 952587 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B1433339 : Blo 952587 1433339 := bstep (se 1 (by rfl) ⟨1075004, by rfl⟩ : syracuseStep 1433339 = 2150009) B2150009
theorem B10313801 : Blo 952587 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B4581373 : Blo 952587 4581373 := bstep (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) B1718015
theorem B11005865 : Blo 952587 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B10317779 : Blo 952587 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B1210459 : Blo 952587 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B6880423 : Blo 952587 6880423 := bstep (se 1 (by rfl) ⟨5160317, by rfl⟩ : syracuseStep 6880423 = 10320635) B10320635
theorem B37125965 : Blo 952587 37125965 := bstep (se 3 (by rfl) ⟨6961118, by rfl⟩ : syracuseStep 37125965 = 13922237) B13922237
theorem B952831 : Blo 952587 952831 := bstep (se 1 (by rfl) ⟨714623, by rfl⟩ : syracuseStep 952831 = 1429247) B1429247
theorem B955559 : Blo 952587 955559 := bstep (se 1 (by rfl) ⟨716669, by rfl⟩ : syracuseStep 955559 = 1433339) B1433339
theorem B67050755 : Blo 952587 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B1613945 : Blo 952587 1613945 := bstep (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) B1210459
theorem B99002573 : Blo 952587 99002573 := bstep (se 3 (by rfl) ⟨18562982, by rfl⟩ : syracuseStep 99002573 = 37125965) B37125965
theorem B6108497 : Blo 952587 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B4831487 : Blo 952587 4831487 := bstep (se 1 (by rfl) ⟨3623615, by rfl⟩ : syracuseStep 4831487 = 7247231) B7247231
theorem B15450335 : Blo 952587 15450335 := bstep (se 1 (by rfl) ⟨11587751, by rfl⟩ : syracuseStep 15450335 = 23175503) B23175503
theorem B24822449 : Blo 952587 24822449 := bstep (se 2 (by rfl) ⟨9308418, by rfl⟩ : syracuseStep 24822449 = 18616837) B18616837
theorem B2903033 : Blo 952587 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B44159417 : Blo 952587 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B2413111 : Blo 952587 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B22926557 : Blo 952587 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B2151647 : Blo 952587 2151647 := bstep (se 1 (by rfl) ⟨1613735, by rfl⟩ : syracuseStep 2151647 = 3227471) B3227471
theorem B2152043 : Blo 952587 2152043 := bstep (se 1 (by rfl) ⟨1614032, by rfl⟩ : syracuseStep 2152043 = 3228065) B3228065
theorem B17651927 : Blo 952587 17651927 := bstep (se 1 (by rfl) ⟨13238945, by rfl⟩ : syracuseStep 17651927 = 26477891) B26477891
theorem B1433087 : Blo 952587 1433087 := bstep (se 1 (by rfl) ⟨1074815, by rfl⟩ : syracuseStep 1433087 = 2149631) B2149631
theorem B1434047 : Blo 952587 1434047 := bstep (se 1 (by rfl) ⟨1075535, by rfl⟩ : syracuseStep 1434047 = 2151071) B2151071
theorem B6875867 : Blo 952587 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B2420705 : Blo 952587 2420705 := bstep (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) B1815529
theorem B1209583 : Blo 952587 1209583 := bstep (se 1 (by rfl) ⟨907187, by rfl⟩ : syracuseStep 1209583 = 1814375) B1814375
theorem B7337243 : Blo 952587 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B6878519 : Blo 952587 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B9173897 : Blo 952587 9173897 := bstep (se 2 (by rfl) ⟨3440211, by rfl⟩ : syracuseStep 9173897 = 6880423) B6880423
theorem B16548299 : Blo 952587 16548299 := bstep (se 1 (by rfl) ⟨12411224, by rfl⟩ : syracuseStep 16548299 = 24822449) B24822449
theorem B1935355 : Blo 952587 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B19565981 : Blo 952587 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B11767951 : Blo 952587 11767951 := bstep (se 1 (by rfl) ⟨8825963, by rfl⟩ : syracuseStep 11767951 = 17651927) B17651927
theorem B44700503 : Blo 952587 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B955391 : Blo 952587 955391 := bstep (se 1 (by rfl) ⟨716543, by rfl⟩ : syracuseStep 955391 = 1433087) B1433087
theorem B956031 : Blo 952587 956031 := bstep (se 1 (by rfl) ⟨717023, by rfl⟩ : syracuseStep 956031 = 1434047) B1434047
theorem B3217481 : Blo 952587 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B66001715 : Blo 952587 66001715 := bstep (se 1 (by rfl) ⟨49501286, by rfl⟩ : syracuseStep 66001715 = 99002573) B99002573
theorem B1612777 : Blo 952587 1612777 := bstep (se 2 (by rfl) ⟨604791, by rfl⟩ : syracuseStep 1612777 = 1209583) B1209583
theorem B1613803 : Blo 952587 1613803 := bstep (se 1 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 1613803 = 2420705) B2420705
theorem B4072331 : Blo 952587 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B3220991 : Blo 952587 3220991 := bstep (se 1 (by rfl) ⟨2415743, by rfl⟩ : syracuseStep 3220991 = 4831487) B4831487
theorem B10300223 : Blo 952587 10300223 := bstep (se 1 (by rfl) ⟨7725167, by rfl⟩ : syracuseStep 10300223 = 15450335) B15450335
theorem B29439611 : Blo 952587 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B15284371 : Blo 952587 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B6115931 : Blo 952587 6115931 := bstep (se 1 (by rfl) ⟨4586948, by rfl⟩ : syracuseStep 6115931 = 9173897) B9173897
theorem B1434431 : Blo 952587 1434431 := bstep (se 1 (by rfl) ⟨1075823, by rfl⟩ : syracuseStep 1434431 = 2151647) B2151647
theorem B1434695 : Blo 952587 1434695 := bstep (se 1 (by rfl) ⟨1076021, by rfl⟩ : syracuseStep 1434695 = 2152043) B2152043
theorem B1075963 : Blo 952587 1075963 := bstep (se 1 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 1075963 = 1613945) B1613945
theorem B4583911 : Blo 952587 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B4585679 : Blo 952587 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B13043987 : Blo 952587 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B956287 : Blo 952587 956287 := bstep (se 1 (by rfl) ⟨717215, by rfl⟩ : syracuseStep 956287 = 1434431) B1434431
theorem B956463 : Blo 952587 956463 := bstep (se 1 (by rfl) ⟨717347, by rfl⟩ : syracuseStep 956463 = 1434695) B1434695
theorem B3057119 : Blo 952587 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B4077287 : Blo 952587 4077287 := bstep (se 1 (by rfl) ⟨3057965, by rfl⟩ : syracuseStep 4077287 = 6115931) B6115931
theorem B2144987 : Blo 952587 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B6111881 : Blo 952587 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B2147327 : Blo 952587 2147327 := bstep (se 1 (by rfl) ⟨1610495, by rfl⟩ : syracuseStep 2147327 = 3220991) B3220991
theorem B6866815 : Blo 952587 6866815 := bstep (se 1 (by rfl) ⟨5150111, by rfl⟩ : syracuseStep 6866815 = 10300223) B10300223
theorem B2150369 : Blo 952587 2150369 := bstep (se 2 (by rfl) ⟨806388, by rfl⟩ : syracuseStep 2150369 = 1612777) B1612777
theorem B2151737 : Blo 952587 2151737 := bstep (se 2 (by rfl) ⟨806901, by rfl⟩ : syracuseStep 2151737 = 1613803) B1613803
theorem B11032199 : Blo 952587 11032199 := bstep (se 1 (by rfl) ⟨8274149, by rfl⟩ : syracuseStep 11032199 = 16548299) B16548299
theorem B119201341 : Blo 952587 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B2580473 : Blo 952587 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B1434617 : Blo 952587 1434617 := bstep (se 2 (by rfl) ⟨537981, by rfl⟩ : syracuseStep 1434617 = 1075963) B1075963
theorem B44001143 : Blo 952587 44001143 := bstep (se 1 (by rfl) ⟨33000857, by rfl⟩ : syracuseStep 44001143 = 66001715) B66001715
theorem B15690601 : Blo 952587 15690601 := bstep (se 2 (by rfl) ⟨5883975, by rfl⟩ : syracuseStep 15690601 = 11767951) B11767951
theorem B2714887 : Blo 952587 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B20379161 : Blo 952587 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B19626407 : Blo 952587 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B956411 : Blo 952587 956411 := bstep (se 1 (by rfl) ⟨717308, by rfl⟩ : syracuseStep 956411 = 1434617) B1434617
theorem B2038079 : Blo 952587 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B29334095 : Blo 952587 29334095 := bstep (se 1 (by rfl) ⟨22000571, by rfl⟩ : syracuseStep 29334095 = 44001143) B44001143
theorem B13084271 : Blo 952587 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B158935121 : Blo 952587 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B4074587 : Blo 952587 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B8695991 : Blo 952587 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B9155753 : Blo 952587 9155753 := bstep (se 2 (by rfl) ⟨3433407, by rfl⟩ : syracuseStep 9155753 = 6866815) B6866815
theorem B7354799 : Blo 952587 7354799 := bstep (se 1 (by rfl) ⟨5516099, by rfl⟩ : syracuseStep 7354799 = 11032199) B11032199
theorem B20920801 : Blo 952587 20920801 := bstep (se 2 (by rfl) ⟨7845300, by rfl⟩ : syracuseStep 20920801 = 15690601) B15690601
theorem B54344429 : Blo 952587 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B3619849 : Blo 952587 3619849 := bstep (se 2 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 3619849 = 2714887) B2714887
theorem B1720315 : Blo 952587 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B1429991 : Blo 952587 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B1431551 : Blo 952587 1431551 := bstep (se 1 (by rfl) ⟨1073663, by rfl⟩ : syracuseStep 1431551 = 2147327) B2147327
theorem B1433579 : Blo 952587 1433579 := bstep (se 1 (by rfl) ⟨1075184, by rfl⟩ : syracuseStep 1433579 = 2150369) B2150369
theorem B1434491 : Blo 952587 1434491 := bstep (se 1 (by rfl) ⟨1075868, by rfl⟩ : syracuseStep 1434491 = 2151737) B2151737
theorem B2718191 : Blo 952587 2718191 := bstep (se 1 (by rfl) ⟨2038643, by rfl⟩ : syracuseStep 2718191 = 4077287) B4077287
theorem B953327 : Blo 952587 953327 := bstep (se 1 (by rfl) ⟨714995, by rfl⟩ : syracuseStep 953327 = 1429991) B1429991
theorem B954367 : Blo 952587 954367 := bstep (se 1 (by rfl) ⟨715775, by rfl⟩ : syracuseStep 954367 = 1431551) B1431551
theorem B955719 : Blo 952587 955719 := bstep (se 1 (by rfl) ⟨716789, by rfl⟩ : syracuseStep 955719 = 1433579) B1433579
theorem B956327 : Blo 952587 956327 := bstep (se 1 (by rfl) ⟨717245, by rfl⟩ : syracuseStep 956327 = 1434491) B1434491
theorem B8722847 : Blo 952587 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B27894401 : Blo 952587 27894401 := bstep (se 2 (by rfl) ⟨10460400, by rfl⟩ : syracuseStep 27894401 = 20920801) B20920801
theorem B6103835 : Blo 952587 6103835 := bstep (se 1 (by rfl) ⟨4577876, by rfl⟩ : syracuseStep 6103835 = 9155753) B9155753
theorem B4826465 : Blo 952587 4826465 := bstep (se 2 (by rfl) ⟨1809924, by rfl⟩ : syracuseStep 4826465 = 3619849) B3619849
theorem B1812127 : Blo 952587 1812127 := bstep (se 1 (by rfl) ⟨1359095, by rfl⟩ : syracuseStep 1812127 = 2718191) B2718191
theorem B105956747 : Blo 952587 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B4903199 : Blo 952587 4903199 := bstep (se 1 (by rfl) ⟨3677399, by rfl⟩ : syracuseStep 4903199 = 7354799) B7354799
theorem B36229619 : Blo 952587 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B19556063 : Blo 952587 19556063 := bstep (se 1 (by rfl) ⟨14667047, by rfl⟩ : syracuseStep 19556063 = 29334095) B29334095
theorem B5434877 : Blo 952587 5434877 := bstep (se 3 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 5434877 = 2038079) B2038079
theorem B2716391 : Blo 952587 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B5797327 : Blo 952587 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B2293753 : Blo 952587 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B24153079 : Blo 952587 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B4069223 : Blo 952587 4069223 := bstep (se 1 (by rfl) ⟨3051917, by rfl⟩ : syracuseStep 4069223 = 6103835) B6103835
theorem B3217643 : Blo 952587 3217643 := bstep (se 1 (by rfl) ⟨2413232, by rfl⟩ : syracuseStep 3217643 = 4826465) B4826465
theorem B1810927 : Blo 952587 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B3058337 : Blo 952587 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B18596267 : Blo 952587 18596267 := bstep (se 1 (by rfl) ⟨13947200, by rfl⟩ : syracuseStep 18596267 = 27894401) B27894401
theorem B3623251 : Blo 952587 3623251 := bstep (se 1 (by rfl) ⟨2717438, by rfl⟩ : syracuseStep 3623251 = 5434877) B5434877
theorem B70637831 : Blo 952587 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B2416169 : Blo 952587 2416169 := bstep (se 2 (by rfl) ⟨906063, by rfl⟩ : syracuseStep 2416169 = 1812127) B1812127
theorem B3268799 : Blo 952587 3268799 := bstep (se 1 (by rfl) ⟨2451599, by rfl⟩ : syracuseStep 3268799 = 4903199) B4903199
theorem B23260925 : Blo 952587 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B13037375 : Blo 952587 13037375 := bstep (se 1 (by rfl) ⟨9778031, by rfl⟩ : syracuseStep 13037375 = 19556063) B19556063
theorem B7729769 : Blo 952587 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B20612717 : Blo 952587 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B47091887 : Blo 952587 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B1610779 : Blo 952587 1610779 := bstep (se 1 (by rfl) ⟨1208084, by rfl⟩ : syracuseStep 1610779 = 2416169) B2416169
theorem B15507283 : Blo 952587 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B8691583 : Blo 952587 8691583 := bstep (se 1 (by rfl) ⟨6518687, by rfl⟩ : syracuseStep 8691583 = 13037375) B13037375
theorem B12397511 : Blo 952587 12397511 := bstep (se 1 (by rfl) ⟨9298133, by rfl⟩ : syracuseStep 12397511 = 18596267) B18596267
theorem B4831001 : Blo 952587 4831001 := bstep (se 2 (by rfl) ⟨1811625, by rfl⟩ : syracuseStep 4831001 = 3623251) B3623251
theorem B2145095 : Blo 952587 2145095 := bstep (se 1 (by rfl) ⟨1608821, by rfl⟩ : syracuseStep 2145095 = 3217643) B3217643
theorem B2179199 : Blo 952587 2179199 := bstep (se 1 (by rfl) ⟨1634399, by rfl⟩ : syracuseStep 2179199 = 3268799) B3268799
theorem B2414569 : Blo 952587 2414569 := bstep (se 2 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 2414569 = 1810927) B1810927
theorem B2712815 : Blo 952587 2712815 := bstep (se 1 (by rfl) ⟨2034611, by rfl⟩ : syracuseStep 2712815 = 4069223) B4069223
theorem B32204105 : Blo 952587 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B8155565 : Blo 952587 8155565 := bstep (se 3 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 8155565 = 3058337) B3058337
theorem B31394591 : Blo 952587 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B1808543 : Blo 952587 1808543 := bstep (se 1 (by rfl) ⟨1356407, by rfl⟩ : syracuseStep 1808543 = 2712815) B2712815
theorem B21469403 : Blo 952587 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B8265007 : Blo 952587 8265007 := bstep (se 1 (by rfl) ⟨6198755, by rfl⟩ : syracuseStep 8265007 = 12397511) B12397511
theorem B3219425 : Blo 952587 3219425 := bstep (se 2 (by rfl) ⟨1207284, by rfl⟩ : syracuseStep 3219425 = 2414569) B2414569
theorem B3220667 : Blo 952587 3220667 := bstep (se 1 (by rfl) ⟨2415500, by rfl⟩ : syracuseStep 3220667 = 4831001) B4831001
theorem B1452799 : Blo 952587 1452799 := bstep (se 1 (by rfl) ⟨1089599, by rfl⟩ : syracuseStep 1452799 = 2179199) B2179199
theorem B13741811 : Blo 952587 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B2147705 : Blo 952587 2147705 := bstep (se 2 (by rfl) ⟨805389, by rfl⟩ : syracuseStep 2147705 = 1610779) B1610779
theorem B1430063 : Blo 952587 1430063 := bstep (se 1 (by rfl) ⟨1072547, by rfl⟩ : syracuseStep 1430063 = 2145095) B2145095
theorem B11588777 : Blo 952587 11588777 := bstep (se 2 (by rfl) ⟨4345791, by rfl⟩ : syracuseStep 11588777 = 8691583) B8691583
theorem B5437043 : Blo 952587 5437043 := bstep (se 1 (by rfl) ⟨4077782, by rfl⟩ : syracuseStep 5437043 = 8155565) B8155565
theorem B20676377 : Blo 952587 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B953375 : Blo 952587 953375 := bstep (se 1 (by rfl) ⟨715031, by rfl⟩ : syracuseStep 953375 = 1430063) B1430063
theorem B11020009 : Blo 952587 11020009 := bstep (se 2 (by rfl) ⟨4132503, by rfl⟩ : syracuseStep 11020009 = 8265007) B8265007
theorem B7748261 : Blo 952587 7748261 := bstep (se 4 (by rfl) ⟨726399, by rfl⟩ : syracuseStep 7748261 = 1452799) B1452799
theorem B2146283 : Blo 952587 2146283 := bstep (se 1 (by rfl) ⟨1609712, by rfl⟩ : syracuseStep 2146283 = 3219425) B3219425
theorem B2147111 : Blo 952587 2147111 := bstep (se 1 (by rfl) ⟨1610333, by rfl⟩ : syracuseStep 2147111 = 3220667) B3220667
theorem B9161207 : Blo 952587 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B3624695 : Blo 952587 3624695 := bstep (se 1 (by rfl) ⟨2718521, by rfl⟩ : syracuseStep 3624695 = 5437043) B5437043
theorem B13784251 : Blo 952587 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B1431803 : Blo 952587 1431803 := bstep (se 1 (by rfl) ⟨1073852, by rfl⟩ : syracuseStep 1431803 = 2147705) B2147705
theorem B20929727 : Blo 952587 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B7725851 : Blo 952587 7725851 := bstep (se 1 (by rfl) ⟨5794388, by rfl⟩ : syracuseStep 7725851 = 11588777) B11588777
theorem B1205695 : Blo 952587 1205695 := bstep (se 1 (by rfl) ⟨904271, by rfl⟩ : syracuseStep 1205695 = 1808543) B1808543
theorem B14312935 : Blo 952587 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B1607593 : Blo 952587 1607593 := bstep (se 2 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 1607593 = 1205695) B1205695
theorem B954535 : Blo 952587 954535 := bstep (se 1 (by rfl) ⟨715901, by rfl⟩ : syracuseStep 954535 = 1431803) B1431803
theorem B5150567 : Blo 952587 5150567 := bstep (se 1 (by rfl) ⟨3862925, by rfl⟩ : syracuseStep 5150567 = 7725851) B7725851
theorem B6107471 : Blo 952587 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B14693345 : Blo 952587 14693345 := bstep (se 2 (by rfl) ⟨5510004, by rfl⟩ : syracuseStep 14693345 = 11020009) B11020009
theorem B76335653 : Blo 952587 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B5165507 : Blo 952587 5165507 := bstep (se 1 (by rfl) ⟨3874130, by rfl⟩ : syracuseStep 5165507 = 7748261) B7748261
theorem B1430855 : Blo 952587 1430855 := bstep (se 1 (by rfl) ⟨1073141, by rfl⟩ : syracuseStep 1430855 = 2146283) B2146283
theorem B1431407 : Blo 952587 1431407 := bstep (se 1 (by rfl) ⟨1073555, by rfl⟩ : syracuseStep 1431407 = 2147111) B2147111
theorem B2416463 : Blo 952587 2416463 := bstep (se 1 (by rfl) ⟨1812347, by rfl⟩ : syracuseStep 2416463 = 3624695) B3624695
theorem B13953151 : Blo 952587 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B18379001 : Blo 952587 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B3443671 : Blo 952587 3443671 := bstep (se 1 (by rfl) ⟨2582753, by rfl⟩ : syracuseStep 3443671 = 5165507) B5165507
theorem B953903 : Blo 952587 953903 := bstep (se 1 (by rfl) ⟨715427, by rfl⟩ : syracuseStep 953903 = 1430855) B1430855
theorem B954271 : Blo 952587 954271 := bstep (se 1 (by rfl) ⟨715703, by rfl⟩ : syracuseStep 954271 = 1431407) B1431407
theorem B1610975 : Blo 952587 1610975 := bstep (se 1 (by rfl) ⟨1208231, by rfl⟩ : syracuseStep 1610975 = 2416463) B2416463
theorem B203561741 : Blo 952587 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B4071647 : Blo 952587 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B2143457 : Blo 952587 2143457 := bstep (se 2 (by rfl) ⟨803796, by rfl⟩ : syracuseStep 2143457 = 1607593) B1607593
theorem B18604201 : Blo 952587 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B3433711 : Blo 952587 3433711 := bstep (se 1 (by rfl) ⟨2575283, by rfl⟩ : syracuseStep 3433711 = 5150567) B5150567
theorem B12252667 : Blo 952587 12252667 := bstep (se 1 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 12252667 = 18379001) B18379001
theorem B9795563 : Blo 952587 9795563 := bstep (se 1 (by rfl) ⟨7346672, by rfl⟩ : syracuseStep 9795563 = 14693345) B14693345
theorem B24805601 : Blo 952587 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B4591561 : Blo 952587 4591561 := bstep (se 2 (by rfl) ⟨1721835, by rfl⟩ : syracuseStep 4591561 = 3443671) B3443671
theorem B6530375 : Blo 952587 6530375 := bstep (se 1 (by rfl) ⟨4897781, by rfl⟩ : syracuseStep 6530375 = 9795563) B9795563
theorem B10857725 : Blo 952587 10857725 := bstep (se 3 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 10857725 = 4071647) B4071647
theorem B135707827 : Blo 952587 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B16336889 : Blo 952587 16336889 := bstep (se 2 (by rfl) ⟨6126333, by rfl⟩ : syracuseStep 16336889 = 12252667) B12252667
theorem B1428971 : Blo 952587 1428971 := bstep (se 1 (by rfl) ⟨1071728, by rfl⟩ : syracuseStep 1428971 = 2143457) B2143457
theorem B4578281 : Blo 952587 4578281 := bstep (se 2 (by rfl) ⟨1716855, by rfl⟩ : syracuseStep 4578281 = 3433711) B3433711
theorem B1073983 : Blo 952587 1073983 := bstep (se 1 (by rfl) ⟨805487, by rfl⟩ : syracuseStep 1073983 = 1610975) B1610975
theorem B952647 : Blo 952587 952647 := bstep (se 1 (by rfl) ⟨714485, by rfl⟩ : syracuseStep 952647 = 1428971) B1428971
theorem B3052187 : Blo 952587 3052187 := bstep (se 1 (by rfl) ⟨2289140, by rfl⟩ : syracuseStep 3052187 = 4578281) B4578281
theorem B10891259 : Blo 952587 10891259 := bstep (se 1 (by rfl) ⟨8168444, by rfl⟩ : syracuseStep 10891259 = 16336889) B16336889
theorem B16537067 : Blo 952587 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B1431977 : Blo 952587 1431977 := bstep (se 2 (by rfl) ⟨536991, by rfl⟩ : syracuseStep 1431977 = 1073983) B1073983
theorem B6122081 : Blo 952587 6122081 := bstep (se 2 (by rfl) ⟨2295780, by rfl⟩ : syracuseStep 6122081 = 4591561) B4591561
theorem B4353583 : Blo 952587 4353583 := bstep (se 1 (by rfl) ⟨3265187, by rfl⟩ : syracuseStep 4353583 = 6530375) B6530375
theorem B7238483 : Blo 952587 7238483 := bstep (se 1 (by rfl) ⟨5428862, by rfl⟩ : syracuseStep 7238483 = 10857725) B10857725
theorem B180943769 : Blo 952587 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B2034791 : Blo 952587 2034791 := bstep (se 1 (by rfl) ⟨1526093, by rfl⟩ : syracuseStep 2034791 = 3052187) B3052187
theorem B954651 : Blo 952587 954651 := bstep (se 1 (by rfl) ⟨715988, by rfl⟩ : syracuseStep 954651 = 1431977) B1431977
theorem B5804777 : Blo 952587 5804777 := bstep (se 2 (by rfl) ⟨2176791, by rfl⟩ : syracuseStep 5804777 = 4353583) B4353583
theorem B4825655 : Blo 952587 4825655 := bstep (se 1 (by rfl) ⟨3619241, by rfl⟩ : syracuseStep 4825655 = 7238483) B7238483
theorem B120629179 : Blo 952587 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B11024711 : Blo 952587 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B4081387 : Blo 952587 4081387 := bstep (se 1 (by rfl) ⟨3061040, by rfl⟩ : syracuseStep 4081387 = 6122081) B6122081
theorem B7260839 : Blo 952587 7260839 := bstep (se 1 (by rfl) ⟨5445629, by rfl⟩ : syracuseStep 7260839 = 10891259) B10891259
theorem B5441849 : Blo 952587 5441849 := bstep (se 2 (by rfl) ⟨2040693, by rfl⟩ : syracuseStep 5441849 = 4081387) B4081387
theorem B3869851 : Blo 952587 3869851 := bstep (se 1 (by rfl) ⟨2902388, by rfl⟩ : syracuseStep 3869851 = 5804777) B5804777
theorem B3217103 : Blo 952587 3217103 := bstep (se 1 (by rfl) ⟨2412827, by rfl⟩ : syracuseStep 3217103 = 4825655) B4825655
theorem B7349807 : Blo 952587 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B1356527 : Blo 952587 1356527 := bstep (se 1 (by rfl) ⟨1017395, by rfl⟩ : syracuseStep 1356527 = 2034791) B2034791
theorem B643355621 : Blo 952587 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B4840559 : Blo 952587 4840559 := bstep (se 1 (by rfl) ⟨3630419, by rfl⟩ : syracuseStep 4840559 = 7260839) B7260839
theorem B428903747 : Blo 952587 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B3617405 : Blo 952587 3617405 := bstep (se 3 (by rfl) ⟨678263, by rfl⟩ : syracuseStep 3617405 = 1356527) B1356527
theorem B2144735 : Blo 952587 2144735 := bstep (se 1 (by rfl) ⟨1608551, by rfl⟩ : syracuseStep 2144735 = 3217103) B3217103
theorem B5159801 : Blo 952587 5159801 := bstep (se 2 (by rfl) ⟨1934925, by rfl⟩ : syracuseStep 5159801 = 3869851) B3869851
theorem B3227039 : Blo 952587 3227039 := bstep (se 1 (by rfl) ⟨2420279, by rfl⟩ : syracuseStep 3227039 = 4840559) B4840559
theorem B4899871 : Blo 952587 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B3627899 : Blo 952587 3627899 := bstep (se 1 (by rfl) ⟨2720924, by rfl⟩ : syracuseStep 3627899 = 5441849) B5441849
theorem B285935831 : Blo 952587 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B26132645 : Blo 952587 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B2411603 : Blo 952587 2411603 := bstep (se 1 (by rfl) ⟨1808702, by rfl⟩ : syracuseStep 2411603 = 3617405) B3617405
theorem B1429823 : Blo 952587 1429823 := bstep (se 1 (by rfl) ⟨1072367, by rfl⟩ : syracuseStep 1429823 = 2144735) B2144735
theorem B2151359 : Blo 952587 2151359 := bstep (se 1 (by rfl) ⟨1613519, by rfl⟩ : syracuseStep 2151359 = 3227039) B3227039
theorem B2418599 : Blo 952587 2418599 := bstep (se 1 (by rfl) ⟨1813949, by rfl⟩ : syracuseStep 2418599 = 3627899) B3627899
theorem B3439867 : Blo 952587 3439867 := bstep (se 1 (by rfl) ⟨2579900, by rfl⟩ : syracuseStep 3439867 = 5159801) B5159801
theorem B1607735 : Blo 952587 1607735 := bstep (se 1 (by rfl) ⟨1205801, by rfl⟩ : syracuseStep 1607735 = 2411603) B2411603
theorem B953215 : Blo 952587 953215 := bstep (se 1 (by rfl) ⟨714911, by rfl⟩ : syracuseStep 953215 = 1429823) B1429823
theorem B1612399 : Blo 952587 1612399 := bstep (se 1 (by rfl) ⟨1209299, by rfl⟩ : syracuseStep 1612399 = 2418599) B2418599
theorem B190623887 : Blo 952587 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B17421763 : Blo 952587 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B1434239 : Blo 952587 1434239 := bstep (se 1 (by rfl) ⟨1075679, by rfl⟩ : syracuseStep 1434239 = 2151359) B2151359
theorem B4586489 : Blo 952587 4586489 := bstep (se 2 (by rfl) ⟨1719933, by rfl⟩ : syracuseStep 4586489 = 3439867) B3439867
theorem B956159 : Blo 952587 956159 := bstep (se 1 (by rfl) ⟨717119, by rfl⟩ : syracuseStep 956159 = 1434239) B1434239
theorem B127082591 : Blo 952587 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B3057659 : Blo 952587 3057659 := bstep (se 1 (by rfl) ⟨2293244, by rfl⟩ : syracuseStep 3057659 = 4586489) B4586489
theorem B2149865 : Blo 952587 2149865 := bstep (se 2 (by rfl) ⟨806199, by rfl⟩ : syracuseStep 2149865 = 1612399) B1612399
theorem B1071823 : Blo 952587 1071823 := bstep (se 1 (by rfl) ⟨803867, by rfl⟩ : syracuseStep 1071823 = 1607735) B1607735
theorem B23229017 : Blo 952587 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B2038439 : Blo 952587 2038439 := bstep (se 1 (by rfl) ⟨1528829, by rfl⟩ : syracuseStep 2038439 = 3057659) B3057659
theorem B84721727 : Blo 952587 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B15486011 : Blo 952587 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B1429097 : Blo 952587 1429097 := bstep (se 2 (by rfl) ⟨535911, by rfl⟩ : syracuseStep 1429097 = 1071823) B1071823
theorem B1433243 : Blo 952587 1433243 := bstep (se 1 (by rfl) ⟨1074932, by rfl⟩ : syracuseStep 1433243 = 2149865) B2149865
theorem B10324007 : Blo 952587 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B952731 : Blo 952587 952731 := bstep (se 1 (by rfl) ⟨714548, by rfl⟩ : syracuseStep 952731 = 1429097) B1429097
theorem B955495 : Blo 952587 955495 := bstep (se 1 (by rfl) ⟨716621, by rfl⟩ : syracuseStep 955495 = 1433243) B1433243
theorem B1358959 : Blo 952587 1358959 := bstep (se 1 (by rfl) ⟨1019219, by rfl⟩ : syracuseStep 1358959 = 2038439) B2038439
theorem B56481151 : Blo 952587 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B6882671 : Blo 952587 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B75308201 : Blo 952587 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B1811945 : Blo 952587 1811945 := bstep (se 2 (by rfl) ⟨679479, by rfl⟩ : syracuseStep 1811945 = 1358959) B1358959
theorem B4588447 : Blo 952587 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B50205467 : Blo 952587 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B1207963 : Blo 952587 1207963 := bstep (se 1 (by rfl) ⟨905972, by rfl⟩ : syracuseStep 1207963 = 1811945) B1811945
theorem B1610617 : Blo 952587 1610617 := bstep (se 2 (by rfl) ⟨603981, by rfl⟩ : syracuseStep 1610617 = 1207963) B1207963
theorem B6117929 : Blo 952587 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B133881245 : Blo 952587 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B4078619 : Blo 952587 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B2147489 : Blo 952587 2147489 := bstep (se 2 (by rfl) ⟨805308, by rfl⟩ : syracuseStep 2147489 = 1610617) B1610617
theorem B89254163 : Blo 952587 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B1431659 : Blo 952587 1431659 := bstep (se 1 (by rfl) ⟨1073744, by rfl⟩ : syracuseStep 1431659 = 2147489) B2147489
theorem B59502775 : Blo 952587 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B2719079 : Blo 952587 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B954439 : Blo 952587 954439 := bstep (se 1 (by rfl) ⟨715829, by rfl⟩ : syracuseStep 954439 = 1431659) B1431659
theorem B79337033 : Blo 952587 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B1812719 : Blo 952587 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B52891355 : Blo 952587 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B4833917 : Blo 952587 4833917 := bstep (se 3 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 4833917 = 1812719) B1812719
theorem B35260903 : Blo 952587 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B3222611 : Blo 952587 3222611 := bstep (se 1 (by rfl) ⟨2416958, by rfl⟩ : syracuseStep 3222611 = 4833917) B4833917
theorem B188058149 : Blo 952587 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B2148407 : Blo 952587 2148407 := bstep (se 1 (by rfl) ⟨1611305, by rfl⟩ : syracuseStep 2148407 = 3222611) B3222611
theorem B125372099 : Blo 952587 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B1432271 : Blo 952587 1432271 := bstep (se 1 (by rfl) ⟨1074203, by rfl⟩ : syracuseStep 1432271 = 2148407) B2148407
theorem B954847 : Blo 952587 954847 := bstep (se 1 (by rfl) ⟨716135, by rfl⟩ : syracuseStep 954847 = 1432271) B1432271
theorem B83581399 : Blo 952587 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B111441865 : Blo 952587 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 952587 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B99059435 : Blo 952587 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B66039623 : Blo 952587 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 952587 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 952587 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 952587 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 952587 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 952587 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 952587 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 952587 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 952587 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 952587 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 952587 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 952587 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 952587 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B5429227 : Blo 952587 5429227 := bstep (se 1 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 5429227 = 8143841) B8143841
theorem B7238969 : Blo 952587 7238969 := bstep (se 2 (by rfl) ⟨2714613, by rfl⟩ : syracuseStep 7238969 = 5429227) B5429227
theorem B4825979 : Blo 952587 4825979 := bstep (se 1 (by rfl) ⟨3619484, by rfl⟩ : syracuseStep 4825979 = 7238969) B7238969
theorem B3217319 : Blo 952587 3217319 := bstep (se 1 (by rfl) ⟨2412989, by rfl⟩ : syracuseStep 3217319 = 4825979) B4825979
theorem B2144879 : Blo 952587 2144879 := bstep (se 1 (by rfl) ⟨1608659, by rfl⟩ : syracuseStep 2144879 = 3217319) B3217319
theorem B1429919 : Blo 952587 1429919 := bstep (se 1 (by rfl) ⟨1072439, by rfl⟩ : syracuseStep 1429919 = 2144879) B2144879
theorem B953279 : Blo 952587 953279 := bstep (se 1 (by rfl) ⟨714959, by rfl⟩ : syracuseStep 953279 = 1429919) B1429919

theorem C0 (j : ℕ) (h1 : 238146 ≤ j) (h2 : j ≤ 238845) : Blo 952587 (4 * j + 3) := by
  interval_cases j
  · exact B952587
  · exact B952591
  · exact B952595
  · exact B952599
  · exact B952603
  · exact B952607
  · exact B952611
  · exact B952615
  · exact B952619
  · exact B952623
  · exact B952627
  · exact B952631
  · exact B952635
  · exact B952639
  · exact B952643
  · exact B952647
  · exact B952651
  · exact B952655
  · exact B952659
  · exact B952663
  · exact B952667
  · exact B952671
  · exact B952675
  · exact B952679
  · exact B952683
  · exact B952687
  · exact B952691
  · exact B952695
  · exact B952699
  · exact B952703
  · exact B952707
  · exact B952711
  · exact B952715
  · exact B952719
  · exact B952723
  · exact B952727
  · exact B952731
  · exact B952735
  · exact B952739
  · exact B952743
  · exact B952747
  · exact B952751
  · exact B952755
  · exact B952759
  · exact B952763
  · exact B952767
  · exact B952771
  · exact B952775
  · exact B952779
  · exact B952783
  · exact B952787
  · exact B952791
  · exact B952795
  · exact B952799
  · exact B952803
  · exact B952807
  · exact B952811
  · exact B952815
  · exact B952819
  · exact B952823
  · exact B952827
  · exact B952831
  · exact B952835
  · exact B952839
  · exact B952843
  · exact B952847
  · exact B952851
  · exact B952855
  · exact B952859
  · exact B952863
  · exact B952867
  · exact B952871
  · exact B952875
  · exact B952879
  · exact B952883
  · exact B952887
  · exact B952891
  · exact B952895
  · exact B952899
  · exact B952903
  · exact B952907
  · exact B952911
  · exact B952915
  · exact B952919
  · exact B952923
  · exact B952927
  · exact B952931
  · exact B952935
  · exact B952939
  · exact B952943
  · exact B952947
  · exact B952951
  · exact B952955
  · exact B952959
  · exact B952963
  · exact B952967
  · exact B952971
  · exact B952975
  · exact B952979
  · exact B952983
  · exact B952987
  · exact B952991
  · exact B952995
  · exact B952999
  · exact B953003
  · exact B953007
  · exact B953011
  · exact B953015
  · exact B953019
  · exact B953023
  · exact B953027
  · exact B953031
  · exact B953035
  · exact B953039
  · exact B953043
  · exact B953047
  · exact B953051
  · exact B953055
  · exact B953059
  · exact B953063
  · exact B953067
  · exact B953071
  · exact B953075
  · exact B953079
  · exact B953083
  · exact B953087
  · exact B953091
  · exact B953095
  · exact B953099
  · exact B953103
  · exact B953107
  · exact B953111
  · exact B953115
  · exact B953119
  · exact B953123
  · exact B953127
  · exact B953131
  · exact B953135
  · exact B953139
  · exact B953143
  · exact B953147
  · exact B953151
  · exact B953155
  · exact B953159
  · exact B953163
  · exact B953167
  · exact B953171
  · exact B953175
  · exact B953179
  · exact B953183
  · exact B953187
  · exact B953191
  · exact B953195
  · exact B953199
  · exact B953203
  · exact B953207
  · exact B953211
  · exact B953215
  · exact B953219
  · exact B953223
  · exact B953227
  · exact B953231
  · exact B953235
  · exact B953239
  · exact B953243
  · exact B953247
  · exact B953251
  · exact B953255
  · exact B953259
  · exact B953263
  · exact B953267
  · exact B953271
  · exact B953275
  · exact B953279
  · exact B953283
  · exact B953287
  · exact B953291
  · exact B953295
  · exact B953299
  · exact B953303
  · exact B953307
  · exact B953311
  · exact B953315
  · exact B953319
  · exact B953323
  · exact B953327
  · exact B953331
  · exact B953335
  · exact B953339
  · exact B953343
  · exact B953347
  · exact B953351
  · exact B953355
  · exact B953359
  · exact B953363
  · exact B953367
  · exact B953371
  · exact B953375
  · exact B953379
  · exact B953383
  · exact B953387
  · exact B953391
  · exact B953395
  · exact B953399
  · exact B953403
  · exact B953407
  · exact B953411
  · exact B953415
  · exact B953419
  · exact B953423
  · exact B953427
  · exact B953431
  · exact B953435
  · exact B953439
  · exact B953443
  · exact B953447
  · exact B953451
  · exact B953455
  · exact B953459
  · exact B953463
  · exact B953467
  · exact B953471
  · exact B953475
  · exact B953479
  · exact B953483
  · exact B953487
  · exact B953491
  · exact B953495
  · exact B953499
  · exact B953503
  · exact B953507
  · exact B953511
  · exact B953515
  · exact B953519
  · exact B953523
  · exact B953527
  · exact B953531
  · exact B953535
  · exact B953539
  · exact B953543
  · exact B953547
  · exact B953551
  · exact B953555
  · exact B953559
  · exact B953563
  · exact B953567
  · exact B953571
  · exact B953575
  · exact B953579
  · exact B953583
  · exact B953587
  · exact B953591
  · exact B953595
  · exact B953599
  · exact B953603
  · exact B953607
  · exact B953611
  · exact B953615
  · exact B953619
  · exact B953623
  · exact B953627
  · exact B953631
  · exact B953635
  · exact B953639
  · exact B953643
  · exact B953647
  · exact B953651
  · exact B953655
  · exact B953659
  · exact B953663
  · exact B953667
  · exact B953671
  · exact B953675
  · exact B953679
  · exact B953683
  · exact B953687
  · exact B953691
  · exact B953695
  · exact B953699
  · exact B953703
  · exact B953707
  · exact B953711
  · exact B953715
  · exact B953719
  · exact B953723
  · exact B953727
  · exact B953731
  · exact B953735
  · exact B953739
  · exact B953743
  · exact B953747
  · exact B953751
  · exact B953755
  · exact B953759
  · exact B953763
  · exact B953767
  · exact B953771
  · exact B953775
  · exact B953779
  · exact B953783
  · exact B953787
  · exact B953791
  · exact B953795
  · exact B953799
  · exact B953803
  · exact B953807
  · exact B953811
  · exact B953815
  · exact B953819
  · exact B953823
  · exact B953827
  · exact B953831
  · exact B953835
  · exact B953839
  · exact B953843
  · exact B953847
  · exact B953851
  · exact B953855
  · exact B953859
  · exact B953863
  · exact B953867
  · exact B953871
  · exact B953875
  · exact B953879
  · exact B953883
  · exact B953887
  · exact B953891
  · exact B953895
  · exact B953899
  · exact B953903
  · exact B953907
  · exact B953911
  · exact B953915
  · exact B953919
  · exact B953923
  · exact B953927
  · exact B953931
  · exact B953935
  · exact B953939
  · exact B953943
  · exact B953947
  · exact B953951
  · exact B953955
  · exact B953959
  · exact B953963
  · exact B953967
  · exact B953971
  · exact B953975
  · exact B953979
  · exact B953983
  · exact B953987
  · exact B953991
  · exact B953995
  · exact B953999
  · exact B954003
  · exact B954007
  · exact B954011
  · exact B954015
  · exact B954019
  · exact B954023
  · exact B954027
  · exact B954031
  · exact B954035
  · exact B954039
  · exact B954043
  · exact B954047
  · exact B954051
  · exact B954055
  · exact B954059
  · exact B954063
  · exact B954067
  · exact B954071
  · exact B954075
  · exact B954079
  · exact B954083
  · exact B954087
  · exact B954091
  · exact B954095
  · exact B954099
  · exact B954103
  · exact B954107
  · exact B954111
  · exact B954115
  · exact B954119
  · exact B954123
  · exact B954127
  · exact B954131
  · exact B954135
  · exact B954139
  · exact B954143
  · exact B954147
  · exact B954151
  · exact B954155
  · exact B954159
  · exact B954163
  · exact B954167
  · exact B954171
  · exact B954175
  · exact B954179
  · exact B954183
  · exact B954187
  · exact B954191
  · exact B954195
  · exact B954199
  · exact B954203
  · exact B954207
  · exact B954211
  · exact B954215
  · exact B954219
  · exact B954223
  · exact B954227
  · exact B954231
  · exact B954235
  · exact B954239
  · exact B954243
  · exact B954247
  · exact B954251
  · exact B954255
  · exact B954259
  · exact B954263
  · exact B954267
  · exact B954271
  · exact B954275
  · exact B954279
  · exact B954283
  · exact B954287
  · exact B954291
  · exact B954295
  · exact B954299
  · exact B954303
  · exact B954307
  · exact B954311
  · exact B954315
  · exact B954319
  · exact B954323
  · exact B954327
  · exact B954331
  · exact B954335
  · exact B954339
  · exact B954343
  · exact B954347
  · exact B954351
  · exact B954355
  · exact B954359
  · exact B954363
  · exact B954367
  · exact B954371
  · exact B954375
  · exact B954379
  · exact B954383
  · exact B954387
  · exact B954391
  · exact B954395
  · exact B954399
  · exact B954403
  · exact B954407
  · exact B954411
  · exact B954415
  · exact B954419
  · exact B954423
  · exact B954427
  · exact B954431
  · exact B954435
  · exact B954439
  · exact B954443
  · exact B954447
  · exact B954451
  · exact B954455
  · exact B954459
  · exact B954463
  · exact B954467
  · exact B954471
  · exact B954475
  · exact B954479
  · exact B954483
  · exact B954487
  · exact B954491
  · exact B954495
  · exact B954499
  · exact B954503
  · exact B954507
  · exact B954511
  · exact B954515
  · exact B954519
  · exact B954523
  · exact B954527
  · exact B954531
  · exact B954535
  · exact B954539
  · exact B954543
  · exact B954547
  · exact B954551
  · exact B954555
  · exact B954559
  · exact B954563
  · exact B954567
  · exact B954571
  · exact B954575
  · exact B954579
  · exact B954583
  · exact B954587
  · exact B954591
  · exact B954595
  · exact B954599
  · exact B954603
  · exact B954607
  · exact B954611
  · exact B954615
  · exact B954619
  · exact B954623
  · exact B954627
  · exact B954631
  · exact B954635
  · exact B954639
  · exact B954643
  · exact B954647
  · exact B954651
  · exact B954655
  · exact B954659
  · exact B954663
  · exact B954667
  · exact B954671
  · exact B954675
  · exact B954679
  · exact B954683
  · exact B954687
  · exact B954691
  · exact B954695
  · exact B954699
  · exact B954703
  · exact B954707
  · exact B954711
  · exact B954715
  · exact B954719
  · exact B954723
  · exact B954727
  · exact B954731
  · exact B954735
  · exact B954739
  · exact B954743
  · exact B954747
  · exact B954751
  · exact B954755
  · exact B954759
  · exact B954763
  · exact B954767
  · exact B954771
  · exact B954775
  · exact B954779
  · exact B954783
  · exact B954787
  · exact B954791
  · exact B954795
  · exact B954799
  · exact B954803
  · exact B954807
  · exact B954811
  · exact B954815
  · exact B954819
  · exact B954823
  · exact B954827
  · exact B954831
  · exact B954835
  · exact B954839
  · exact B954843
  · exact B954847
  · exact B954851
  · exact B954855
  · exact B954859
  · exact B954863
  · exact B954867
  · exact B954871
  · exact B954875
  · exact B954879
  · exact B954883
  · exact B954887
  · exact B954891
  · exact B954895
  · exact B954899
  · exact B954903
  · exact B954907
  · exact B954911
  · exact B954915
  · exact B954919
  · exact B954923
  · exact B954927
  · exact B954931
  · exact B954935
  · exact B954939
  · exact B954943
  · exact B954947
  · exact B954951
  · exact B954955
  · exact B954959
  · exact B954963
  · exact B954967
  · exact B954971
  · exact B954975
  · exact B954979
  · exact B954983
  · exact B954987
  · exact B954991
  · exact B954995
  · exact B954999
  · exact B955003
  · exact B955007
  · exact B955011
  · exact B955015
  · exact B955019
  · exact B955023
  · exact B955027
  · exact B955031
  · exact B955035
  · exact B955039
  · exact B955043
  · exact B955047
  · exact B955051
  · exact B955055
  · exact B955059
  · exact B955063
  · exact B955067
  · exact B955071
  · exact B955075
  · exact B955079
  · exact B955083
  · exact B955087
  · exact B955091
  · exact B955095
  · exact B955099
  · exact B955103
  · exact B955107
  · exact B955111
  · exact B955115
  · exact B955119
  · exact B955123
  · exact B955127
  · exact B955131
  · exact B955135
  · exact B955139
  · exact B955143
  · exact B955147
  · exact B955151
  · exact B955155
  · exact B955159
  · exact B955163
  · exact B955167
  · exact B955171
  · exact B955175
  · exact B955179
  · exact B955183
  · exact B955187
  · exact B955191
  · exact B955195
  · exact B955199
  · exact B955203
  · exact B955207
  · exact B955211
  · exact B955215
  · exact B955219
  · exact B955223
  · exact B955227
  · exact B955231
  · exact B955235
  · exact B955239
  · exact B955243
  · exact B955247
  · exact B955251
  · exact B955255
  · exact B955259
  · exact B955263
  · exact B955267
  · exact B955271
  · exact B955275
  · exact B955279
  · exact B955283
  · exact B955287
  · exact B955291
  · exact B955295
  · exact B955299
  · exact B955303
  · exact B955307
  · exact B955311
  · exact B955315
  · exact B955319
  · exact B955323
  · exact B955327
  · exact B955331
  · exact B955335
  · exact B955339
  · exact B955343
  · exact B955347
  · exact B955351
  · exact B955355
  · exact B955359
  · exact B955363
  · exact B955367
  · exact B955371
  · exact B955375
  · exact B955379
  · exact B955383

theorem C1 (j : ℕ) (h1 : 238846 ≤ j) (h2 : j ≤ 239146) : Blo 952587 (4 * j + 3) := by
  interval_cases j
  · exact B955387
  · exact B955391
  · exact B955395
  · exact B955399
  · exact B955403
  · exact B955407
  · exact B955411
  · exact B955415
  · exact B955419
  · exact B955423
  · exact B955427
  · exact B955431
  · exact B955435
  · exact B955439
  · exact B955443
  · exact B955447
  · exact B955451
  · exact B955455
  · exact B955459
  · exact B955463
  · exact B955467
  · exact B955471
  · exact B955475
  · exact B955479
  · exact B955483
  · exact B955487
  · exact B955491
  · exact B955495
  · exact B955499
  · exact B955503
  · exact B955507
  · exact B955511
  · exact B955515
  · exact B955519
  · exact B955523
  · exact B955527
  · exact B955531
  · exact B955535
  · exact B955539
  · exact B955543
  · exact B955547
  · exact B955551
  · exact B955555
  · exact B955559
  · exact B955563
  · exact B955567
  · exact B955571
  · exact B955575
  · exact B955579
  · exact B955583
  · exact B955587
  · exact B955591
  · exact B955595
  · exact B955599
  · exact B955603
  · exact B955607
  · exact B955611
  · exact B955615
  · exact B955619
  · exact B955623
  · exact B955627
  · exact B955631
  · exact B955635
  · exact B955639
  · exact B955643
  · exact B955647
  · exact B955651
  · exact B955655
  · exact B955659
  · exact B955663
  · exact B955667
  · exact B955671
  · exact B955675
  · exact B955679
  · exact B955683
  · exact B955687
  · exact B955691
  · exact B955695
  · exact B955699
  · exact B955703
  · exact B955707
  · exact B955711
  · exact B955715
  · exact B955719
  · exact B955723
  · exact B955727
  · exact B955731
  · exact B955735
  · exact B955739
  · exact B955743
  · exact B955747
  · exact B955751
  · exact B955755
  · exact B955759
  · exact B955763
  · exact B955767
  · exact B955771
  · exact B955775
  · exact B955779
  · exact B955783
  · exact B955787
  · exact B955791
  · exact B955795
  · exact B955799
  · exact B955803
  · exact B955807
  · exact B955811
  · exact B955815
  · exact B955819
  · exact B955823
  · exact B955827
  · exact B955831
  · exact B955835
  · exact B955839
  · exact B955843
  · exact B955847
  · exact B955851
  · exact B955855
  · exact B955859
  · exact B955863
  · exact B955867
  · exact B955871
  · exact B955875
  · exact B955879
  · exact B955883
  · exact B955887
  · exact B955891
  · exact B955895
  · exact B955899
  · exact B955903
  · exact B955907
  · exact B955911
  · exact B955915
  · exact B955919
  · exact B955923
  · exact B955927
  · exact B955931
  · exact B955935
  · exact B955939
  · exact B955943
  · exact B955947
  · exact B955951
  · exact B955955
  · exact B955959
  · exact B955963
  · exact B955967
  · exact B955971
  · exact B955975
  · exact B955979
  · exact B955983
  · exact B955987
  · exact B955991
  · exact B955995
  · exact B955999
  · exact B956003
  · exact B956007
  · exact B956011
  · exact B956015
  · exact B956019
  · exact B956023
  · exact B956027
  · exact B956031
  · exact B956035
  · exact B956039
  · exact B956043
  · exact B956047
  · exact B956051
  · exact B956055
  · exact B956059
  · exact B956063
  · exact B956067
  · exact B956071
  · exact B956075
  · exact B956079
  · exact B956083
  · exact B956087
  · exact B956091
  · exact B956095
  · exact B956099
  · exact B956103
  · exact B956107
  · exact B956111
  · exact B956115
  · exact B956119
  · exact B956123
  · exact B956127
  · exact B956131
  · exact B956135
  · exact B956139
  · exact B956143
  · exact B956147
  · exact B956151
  · exact B956155
  · exact B956159
  · exact B956163
  · exact B956167
  · exact B956171
  · exact B956175
  · exact B956179
  · exact B956183
  · exact B956187
  · exact B956191
  · exact B956195
  · exact B956199
  · exact B956203
  · exact B956207
  · exact B956211
  · exact B956215
  · exact B956219
  · exact B956223
  · exact B956227
  · exact B956231
  · exact B956235
  · exact B956239
  · exact B956243
  · exact B956247
  · exact B956251
  · exact B956255
  · exact B956259
  · exact B956263
  · exact B956267
  · exact B956271
  · exact B956275
  · exact B956279
  · exact B956283
  · exact B956287
  · exact B956291
  · exact B956295
  · exact B956299
  · exact B956303
  · exact B956307
  · exact B956311
  · exact B956315
  · exact B956319
  · exact B956323
  · exact B956327
  · exact B956331
  · exact B956335
  · exact B956339
  · exact B956343
  · exact B956347
  · exact B956351
  · exact B956355
  · exact B956359
  · exact B956363
  · exact B956367
  · exact B956371
  · exact B956375
  · exact B956379
  · exact B956383
  · exact B956387
  · exact B956391
  · exact B956395
  · exact B956399
  · exact B956403
  · exact B956407
  · exact B956411
  · exact B956415
  · exact B956419
  · exact B956423
  · exact B956427
  · exact B956431
  · exact B956435
  · exact B956439
  · exact B956443
  · exact B956447
  · exact B956451
  · exact B956455
  · exact B956459
  · exact B956463
  · exact B956467
  · exact B956471
  · exact B956475
  · exact B956479
  · exact B956483
  · exact B956487
  · exact B956491
  · exact B956495
  · exact B956499
  · exact B956503
  · exact B956507
  · exact B956511
  · exact B956515
  · exact B956519
  · exact B956523
  · exact B956527
  · exact B956531
  · exact B956535
  · exact B956539
  · exact B956543
  · exact B956547
  · exact B956551
  · exact B956555
  · exact B956559
  · exact B956563
  · exact B956567
  · exact B956571
  · exact B956575
  · exact B956579
  · exact B956583
  · exact B956587

theorem solution (m : ℕ) (hlo : 952587 ≤ m) (hhi : m ≤ 956587) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 238146 ≤ j := by omega
    have hj2 : j ≤ 239146 := by omega
    have hb : Blo 952587 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 238846 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
