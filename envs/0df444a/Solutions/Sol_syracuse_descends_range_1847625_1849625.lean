-- Prove2me | solution 1 for syracuse_descends_range_1847625_1849625
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:05:58.971209+00:00
-- url     : https://prove2.me/submissions/55eca2c6-d2f1-4b32-8c68-613b137fc6bf

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


theorem B2080777 : Blo 1847625 2080777 := bbase (se 2 (by rfl) ⟨780291, by rfl⟩ : syracuseStep 2080777 = 1560583) (by norm_num)
theorem B1974289 : Blo 1847625 1974289 := bbase (se 2 (by rfl) ⟨740358, by rfl⟩ : syracuseStep 1974289 = 1480717) (by norm_num)
theorem B3375125 : Blo 1847625 3375125 := bbase (se 6 (by rfl) ⟨79104, by rfl⟩ : syracuseStep 3375125 = 158209) (by norm_num)
theorem B4161581 : Blo 1847625 4161581 := bbase (se 3 (by rfl) ⟨780296, by rfl⟩ : syracuseStep 4161581 = 1560593) (by norm_num)
theorem B2080813 : Blo 1847625 2080813 := bbase (se 3 (by rfl) ⟨390152, by rfl⟩ : syracuseStep 2080813 = 780305) (by norm_num)
theorem B3121213 : Blo 1847625 3121213 := bbase (se 3 (by rfl) ⟨585227, by rfl⟩ : syracuseStep 3121213 = 1170455) (by norm_num)
theorem B4677709 : Blo 1847625 4677709 := bbase (se 3 (by rfl) ⟨877070, by rfl⟩ : syracuseStep 4677709 = 1754141) (by norm_num)
theorem B7897189 : Blo 1847625 7897189 := bbase (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) (by norm_num)
theorem B4161653 : Blo 1847625 4161653 := bbase (se 5 (by rfl) ⟨195077, by rfl⟩ : syracuseStep 4161653 = 390155) (by norm_num)
theorem B1974413 : Blo 1847625 1974413 := bbase (se 3 (by rfl) ⟨370202, by rfl⟩ : syracuseStep 1974413 = 740405) (by norm_num)
theorem B6242453 : Blo 1847625 6242453 := bbase (se 6 (by rfl) ⟨146307, by rfl⟩ : syracuseStep 6242453 = 292615) (by norm_num)
theorem B4677821 : Blo 1847625 4677821 := bbase (se 3 (by rfl) ⟨877091, by rfl⟩ : syracuseStep 4677821 = 1754183) (by norm_num)
theorem B6004949 : Blo 1847625 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B4678013 : Blo 1847625 4678013 := bbase (se 3 (by rfl) ⟨877127, by rfl⟩ : syracuseStep 4678013 = 1754255) (by norm_num)
theorem B1974665 : Blo 1847625 1974665 := bbase (se 2 (by rfl) ⟨740499, by rfl⟩ : syracuseStep 1974665 = 1480999) (by norm_num)
theorem B6660805 : Blo 1847625 6660805 := bbase (se 4 (by rfl) ⟨624450, by rfl⟩ : syracuseStep 6660805 = 1248901) (by norm_num)
theorem B4678357 : Blo 1847625 4678357 := bbase (se 7 (by rfl) ⟨54824, by rfl⟩ : syracuseStep 4678357 = 109649) (by norm_num)
theorem B24011477 : Blo 1847625 24011477 := bbase (se 7 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 24011477 = 562769) (by norm_num)
theorem B7021349 : Blo 1847625 7021349 := bbase (se 4 (by rfl) ⟨658251, by rfl⟩ : syracuseStep 7021349 = 1316503) (by norm_num)
theorem B3949373 : Blo 1847625 3949373 := bbase (se 3 (by rfl) ⟨740507, by rfl⟩ : syracuseStep 3949373 = 1481015) (by norm_num)
theorem B4678469 : Blo 1847625 4678469 := bbase (se 4 (by rfl) ⟨438606, by rfl⟩ : syracuseStep 4678469 = 877213) (by norm_num)
theorem B4440901 : Blo 1847625 4440901 := bbase (se 4 (by rfl) ⟨416334, by rfl⟩ : syracuseStep 4440901 = 832669) (by norm_num)
theorem B7897925 : Blo 1847625 7897925 := bbase (se 4 (by rfl) ⟨740430, by rfl⟩ : syracuseStep 7897925 = 1480861) (by norm_num)
theorem B1975109 : Blo 1847625 1975109 := bbase (se 4 (by rfl) ⟨185166, by rfl⟩ : syracuseStep 1975109 = 370333) (by norm_num)
theorem B3949517 : Blo 1847625 3949517 := bbase (se 3 (by rfl) ⟨740534, by rfl⟩ : syracuseStep 3949517 = 1481069) (by norm_num)
theorem B21046229 : Blo 1847625 21046229 := bbase (se 7 (by rfl) ⟨246635, by rfl⟩ : syracuseStep 21046229 = 493271) (by norm_num)
theorem B4678661 : Blo 1847625 4678661 := bbase (se 4 (by rfl) ⟨438624, by rfl⟩ : syracuseStep 4678661 = 877249) (by norm_num)
theorem B9356309 : Blo 1847625 9356309 := bbase (se 6 (by rfl) ⟨219288, by rfl⟩ : syracuseStep 9356309 = 438577) (by norm_num)
theorem B7021637 : Blo 1847625 7021637 := bbase (se 4 (by rfl) ⟨658278, by rfl⟩ : syracuseStep 7021637 = 1316557) (by norm_num)
theorem B2811037 : Blo 1847625 2811037 := bbase (se 3 (by rfl) ⟨527069, by rfl⟩ : syracuseStep 2811037 = 1054139) (by norm_num)
theorem B2221229 : Blo 1847625 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B2630893 : Blo 1847625 2630893 := bbase (se 3 (by rfl) ⟨493292, by rfl⟩ : syracuseStep 2630893 = 986585) (by norm_num)
theorem B3949877 : Blo 1847625 3949877 := bbase (se 5 (by rfl) ⟨185150, by rfl⟩ : syracuseStep 3949877 = 370301) (by norm_num)
theorem B4679005 : Blo 1847625 4679005 := bbase (se 3 (by rfl) ⟨877313, by rfl⟩ : syracuseStep 4679005 = 1754627) (by norm_num)
theorem B13002133 : Blo 1847625 13002133 := bbase (se 6 (by rfl) ⟨304737, by rfl⟩ : syracuseStep 13002133 = 609475) (by norm_num)
theorem B4441517 : Blo 1847625 4441517 := bbase (se 3 (by rfl) ⟨832784, by rfl⟩ : syracuseStep 4441517 = 1665569) (by norm_num)
theorem B3507637 : Blo 1847625 3507637 := bbase (se 5 (by rfl) ⟨164420, by rfl⟩ : syracuseStep 3507637 = 328841) (by norm_num)
theorem B4679117 : Blo 1847625 4679117 := bbase (se 3 (by rfl) ⟨877334, by rfl⟩ : syracuseStep 4679117 = 1754669) (by norm_num)
theorem B2221565 : Blo 1847625 2221565 := bbase (se 3 (by rfl) ⟨416543, by rfl⟩ : syracuseStep 2221565 = 833087) (by norm_num)
theorem B11847221 : Blo 1847625 11847221 := bbase (se 5 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 11847221 = 1110677) (by norm_num)
theorem B3507781 : Blo 1847625 3507781 := bbase (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) (by norm_num)
theorem B4441709 : Blo 1847625 4441709 := bbase (se 3 (by rfl) ⟨832820, by rfl⟩ : syracuseStep 4441709 = 1665641) (by norm_num)
theorem B2221681 : Blo 1847625 2221681 := bbase (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) (by norm_num)
theorem B4679309 : Blo 1847625 4679309 := bbase (se 3 (by rfl) ⟨877370, by rfl⟩ : syracuseStep 4679309 = 1754741) (by norm_num)
theorem B2000533 : Blo 1847625 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B2221753 : Blo 1847625 2221753 := bbase (se 2 (by rfl) ⟨833157, by rfl⟩ : syracuseStep 2221753 = 1666315) (by norm_num)
theorem B2221777 : Blo 1847625 2221777 := bbase (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) (by norm_num)
theorem B3507941 : Blo 1847625 3507941 := bbase (se 4 (by rfl) ⟨328869, by rfl⟩ : syracuseStep 3507941 = 657739) (by norm_num)
theorem B2631485 : Blo 1847625 2631485 := bbase (se 3 (by rfl) ⟨493403, by rfl⟩ : syracuseStep 2631485 = 986807) (by norm_num)
theorem B6235973 : Blo 1847625 6235973 := bbase (se 4 (by rfl) ⟨584622, by rfl⟩ : syracuseStep 6235973 = 1169245) (by norm_num)
theorem B2221921 : Blo 1847625 2221921 := bbase (se 2 (by rfl) ⟨833220, by rfl⟩ : syracuseStep 2221921 = 1666441) (by norm_num)
theorem B3508085 : Blo 1847625 3508085 := bbase (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) (by norm_num)
theorem B2631565 : Blo 1847625 2631565 := bbase (se 3 (by rfl) ⟨493418, by rfl⟩ : syracuseStep 2631565 = 986837) (by norm_num)
theorem B5924789 : Blo 1847625 5924789 := bbase (se 5 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 5924789 = 555449) (by norm_num)
theorem B4679653 : Blo 1847625 4679653 := bbase (se 4 (by rfl) ⟨438717, by rfl⟩ : syracuseStep 4679653 = 877435) (by norm_num)
theorem B2631685 : Blo 1847625 2631685 := bbase (se 4 (by rfl) ⟨246720, by rfl⟩ : syracuseStep 2631685 = 493441) (by norm_num)
theorem B5924917 : Blo 1847625 5924917 := bbase (se 5 (by rfl) ⟨277730, by rfl⟩ : syracuseStep 5924917 = 555461) (by norm_num)
theorem B4679765 : Blo 1847625 4679765 := bbase (se 8 (by rfl) ⟨27420, by rfl⟩ : syracuseStep 4679765 = 54841) (by norm_num)
theorem B2631781 : Blo 1847625 2631781 := bbase (se 4 (by rfl) ⟨246729, by rfl⟩ : syracuseStep 2631781 = 493459) (by norm_num)
theorem B3508373 : Blo 1847625 3508373 := bbase (se 6 (by rfl) ⟨82227, by rfl⟩ : syracuseStep 3508373 = 164455) (by norm_num)
theorem B4442285 : Blo 1847625 4442285 := bbase (se 3 (by rfl) ⟨832928, by rfl⟩ : syracuseStep 4442285 = 1665857) (by norm_num)
theorem B3745973 : Blo 1847625 3745973 := bbase (se 5 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 3745973 = 351185) (by norm_num)
theorem B6236405 : Blo 1847625 6236405 := bbase (se 5 (by rfl) ⟨292331, by rfl⟩ : syracuseStep 6236405 = 584663) (by norm_num)
theorem B2107657 : Blo 1847625 2107657 := bbase (se 2 (by rfl) ⟨790371, by rfl⟩ : syracuseStep 2107657 = 1580743) (by norm_num)
theorem B4679957 : Blo 1847625 4679957 := bbase (se 6 (by rfl) ⟨109686, by rfl⟩ : syracuseStep 4679957 = 219373) (by norm_num)
theorem B9357605 : Blo 1847625 9357605 := bbase (se 4 (by rfl) ⟨877275, by rfl⟩ : syracuseStep 9357605 = 1754551) (by norm_num)
theorem B3508525 : Blo 1847625 3508525 := bbase (se 3 (by rfl) ⟨657848, by rfl⟩ : syracuseStep 3508525 = 1315697) (by norm_num)
theorem B2812205 : Blo 1847625 2812205 := bbase (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) (by norm_num)
theorem B3000629 : Blo 1847625 3000629 := bbase (se 5 (by rfl) ⟨140654, by rfl⟩ : syracuseStep 3000629 = 281309) (by norm_num)
theorem B15796565 : Blo 1847625 15796565 := bbase (se 10 (by rfl) ⟨23139, by rfl⟩ : syracuseStep 15796565 = 46279) (by norm_num)
theorem B2107849 : Blo 1847625 2107849 := bbase (se 2 (by rfl) ⟨790443, by rfl⟩ : syracuseStep 2107849 = 1580887) (by norm_num)
theorem B9488869 : Blo 1847625 9488869 := bbase (se 4 (by rfl) ⟨889581, by rfl⟩ : syracuseStep 9488869 = 1779163) (by norm_num)
theorem B2771453 : Blo 1847625 2771453 := bbase (se 3 (by rfl) ⟨519647, by rfl⟩ : syracuseStep 2771453 = 1039295) (by norm_num)
theorem B2959877 : Blo 1847625 2959877 := bbase (se 4 (by rfl) ⟨277488, by rfl⟩ : syracuseStep 2959877 = 554977) (by norm_num)
theorem B2771477 : Blo 1847625 2771477 := bbase (se 6 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 2771477 = 129913) (by norm_num)
theorem B2771501 : Blo 1847625 2771501 := bbase (se 3 (by rfl) ⟨519656, by rfl⟩ : syracuseStep 2771501 = 1039313) (by norm_num)
theorem B2402861 : Blo 1847625 2402861 := bbase (se 3 (by rfl) ⟨450536, by rfl⟩ : syracuseStep 2402861 = 901073) (by norm_num)
theorem B2107949 : Blo 1847625 2107949 := bbase (se 3 (by rfl) ⟨395240, by rfl⟩ : syracuseStep 2107949 = 790481) (by norm_num)
theorem B4442669 : Blo 1847625 4442669 := bbase (se 3 (by rfl) ⟨833000, by rfl⟩ : syracuseStep 4442669 = 1666001) (by norm_num)
theorem B6752821 : Blo 1847625 6752821 := bbase (se 5 (by rfl) ⟨316538, by rfl⟩ : syracuseStep 6752821 = 633077) (by norm_num)
theorem B2771525 : Blo 1847625 2771525 := bbase (se 4 (by rfl) ⟨259830, by rfl⟩ : syracuseStep 2771525 = 519661) (by norm_num)
theorem B2632277 : Blo 1847625 2632277 := bbase (se 8 (by rfl) ⟨15423, by rfl⟩ : syracuseStep 2632277 = 30847) (by norm_num)
theorem B2771549 : Blo 1847625 2771549 := bbase (se 3 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 2771549 = 1039331) (by norm_num)
theorem B3508829 : Blo 1847625 3508829 := bbase (se 3 (by rfl) ⟨657905, by rfl⟩ : syracuseStep 3508829 = 1315811) (by norm_num)
theorem B4680301 : Blo 1847625 4680301 := bbase (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) (by norm_num)
theorem B2771573 : Blo 1847625 2771573 := bbase (se 5 (by rfl) ⟨129917, by rfl⟩ : syracuseStep 2771573 = 259835) (by norm_num)
theorem B2771597 : Blo 1847625 2771597 := bbase (se 3 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 2771597 = 1039349) (by norm_num)
theorem B2771621 : Blo 1847625 2771621 := bbase (se 4 (by rfl) ⟨259839, by rfl⟩ : syracuseStep 2771621 = 519679) (by norm_num)
theorem B6236837 : Blo 1847625 6236837 := bbase (se 4 (by rfl) ⟨584703, by rfl⟩ : syracuseStep 6236837 = 1169407) (by norm_num)
theorem B2771645 : Blo 1847625 2771645 := bbase (se 3 (by rfl) ⟨519683, by rfl⟩ : syracuseStep 2771645 = 1039367) (by norm_num)
theorem B2771669 : Blo 1847625 2771669 := bbase (se 7 (by rfl) ⟨32480, by rfl⟩ : syracuseStep 2771669 = 64961) (by norm_num)
theorem B4680413 : Blo 1847625 4680413 := bbase (se 3 (by rfl) ⟨877577, by rfl⟩ : syracuseStep 4680413 = 1755155) (by norm_num)
theorem B2960101 : Blo 1847625 2960101 := bbase (se 4 (by rfl) ⟨277509, by rfl⟩ : syracuseStep 2960101 = 555019) (by norm_num)
theorem B2771693 : Blo 1847625 2771693 := bbase (se 3 (by rfl) ⟨519692, by rfl⟩ : syracuseStep 2771693 = 1039385) (by norm_num)
theorem B2771717 : Blo 1847625 2771717 := bbase (se 4 (by rfl) ⟨259848, by rfl⟩ : syracuseStep 2771717 = 519697) (by norm_num)
theorem B2771741 : Blo 1847625 2771741 := bbase (se 3 (by rfl) ⟨519701, by rfl⟩ : syracuseStep 2771741 = 1039403) (by norm_num)
theorem B2960165 : Blo 1847625 2960165 := bbase (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) (by norm_num)
theorem B2771765 : Blo 1847625 2771765 := bbase (se 5 (by rfl) ⟨129926, by rfl⟩ : syracuseStep 2771765 = 259853) (by norm_num)
theorem B2771789 : Blo 1847625 2771789 := bbase (se 3 (by rfl) ⟨519710, by rfl⟩ : syracuseStep 2771789 = 1039421) (by norm_num)
theorem B2771813 : Blo 1847625 2771813 := bbase (se 4 (by rfl) ⟨259857, by rfl⟩ : syracuseStep 2771813 = 519715) (by norm_num)
theorem B2771837 : Blo 1847625 2771837 := bbase (se 3 (by rfl) ⟨519719, by rfl⟩ : syracuseStep 2771837 = 1039439) (by norm_num)
theorem B2771861 : Blo 1847625 2771861 := bbase (se 6 (by rfl) ⟨64965, by rfl⟩ : syracuseStep 2771861 = 129931) (by norm_num)
theorem B37522325 : Blo 1847625 37522325 := bbase (se 6 (by rfl) ⟨879429, by rfl⟩ : syracuseStep 37522325 = 1758859) (by norm_num)
theorem B4680605 : Blo 1847625 4680605 := bbase (se 3 (by rfl) ⟨877613, by rfl⟩ : syracuseStep 4680605 = 1755227) (by norm_num)
theorem B2960293 : Blo 1847625 2960293 := bbase (se 4 (by rfl) ⟨277527, by rfl⟩ : syracuseStep 2960293 = 555055) (by norm_num)
theorem B2771885 : Blo 1847625 2771885 := bbase (se 3 (by rfl) ⟨519728, by rfl⟩ : syracuseStep 2771885 = 1039457) (by norm_num)
theorem B7015349 : Blo 1847625 7015349 := bbase (se 5 (by rfl) ⟨328844, by rfl⟩ : syracuseStep 7015349 = 657689) (by norm_num)
theorem B2771909 : Blo 1847625 2771909 := bbase (se 4 (by rfl) ⟨259866, by rfl⟩ : syracuseStep 2771909 = 519733) (by norm_num)
theorem B2108369 : Blo 1847625 2108369 := bbase (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) (by norm_num)
theorem B2771933 : Blo 1847625 2771933 := bbase (se 3 (by rfl) ⟨519737, by rfl⟩ : syracuseStep 2771933 = 1039475) (by norm_num)
theorem B2001905 : Blo 1847625 2001905 := bbase (se 2 (by rfl) ⟨750714, by rfl⟩ : syracuseStep 2001905 = 1501429) (by norm_num)
theorem B2771957 : Blo 1847625 2771957 := bbase (se 5 (by rfl) ⟨129935, by rfl⟩ : syracuseStep 2771957 = 259871) (by norm_num)
theorem B7498757 : Blo 1847625 7498757 := bbase (se 4 (by rfl) ⟨703008, by rfl⟩ : syracuseStep 7498757 = 1406017) (by norm_num)
theorem B2771981 : Blo 1847625 2771981 := bbase (se 3 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 2771981 = 1039493) (by norm_num)
theorem B2772005 : Blo 1847625 2772005 := bbase (se 4 (by rfl) ⟨259875, by rfl⟩ : syracuseStep 2772005 = 519751) (by norm_num)
theorem B9612341 : Blo 1847625 9612341 := bbase (se 5 (by rfl) ⟨450578, by rfl⟩ : syracuseStep 9612341 = 901157) (by norm_num)
theorem B2772029 : Blo 1847625 2772029 := bbase (se 3 (by rfl) ⟨519755, by rfl⟩ : syracuseStep 2772029 = 1039511) (by norm_num)
theorem B2772053 : Blo 1847625 2772053 := bbase (se 8 (by rfl) ⟨16242, by rfl⟩ : syracuseStep 2772053 = 32485) (by norm_num)
theorem B6237269 : Blo 1847625 6237269 := bbase (se 8 (by rfl) ⟨36546, by rfl⟩ : syracuseStep 6237269 = 73093) (by norm_num)
theorem B3206245 : Blo 1847625 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B2772077 : Blo 1847625 2772077 := bbase (se 3 (by rfl) ⟨519764, by rfl⟩ : syracuseStep 2772077 = 1039529) (by norm_num)
theorem B2632829 : Blo 1847625 2632829 := bbase (se 3 (by rfl) ⟨493655, by rfl⟩ : syracuseStep 2632829 = 987311) (by norm_num)
theorem B2772101 : Blo 1847625 2772101 := bbase (se 4 (by rfl) ⟨259884, by rfl⟩ : syracuseStep 2772101 = 519769) (by norm_num)
theorem B35540117 : Blo 1847625 35540117 := bbase (se 6 (by rfl) ⟨832971, by rfl⟩ : syracuseStep 35540117 = 1665943) (by norm_num)
theorem B2772125 : Blo 1847625 2772125 := bbase (se 3 (by rfl) ⟨519773, by rfl⟩ : syracuseStep 2772125 = 1039547) (by norm_num)
theorem B2772149 : Blo 1847625 2772149 := bbase (se 5 (by rfl) ⟨129944, by rfl⟩ : syracuseStep 2772149 = 259889) (by norm_num)
theorem B2370745 : Blo 1847625 2370745 := bbase (se 2 (by rfl) ⟨889029, by rfl⟩ : syracuseStep 2370745 = 1778059) (by norm_num)
theorem B2772173 : Blo 1847625 2772173 := bbase (se 3 (by rfl) ⟨519782, by rfl⟩ : syracuseStep 2772173 = 1039565) (by norm_num)
theorem B26651861 : Blo 1847625 26651861 := bbase (se 7 (by rfl) ⟨312326, by rfl⟩ : syracuseStep 26651861 = 624653) (by norm_num)
theorem B2772197 : Blo 1847625 2772197 := bbase (se 4 (by rfl) ⟨259893, by rfl⟩ : syracuseStep 2772197 = 519787) (by norm_num)
theorem B4680949 : Blo 1847625 4680949 := bbase (se 5 (by rfl) ⟨219419, by rfl⟩ : syracuseStep 4680949 = 438839) (by norm_num)
theorem B2772221 : Blo 1847625 2772221 := bbase (se 3 (by rfl) ⟨519791, by rfl⟩ : syracuseStep 2772221 = 1039583) (by norm_num)
theorem B2772245 : Blo 1847625 2772245 := bbase (se 6 (by rfl) ⟨64974, by rfl⟩ : syracuseStep 2772245 = 129949) (by norm_num)
theorem B2772269 : Blo 1847625 2772269 := bbase (se 3 (by rfl) ⟨519800, by rfl⟩ : syracuseStep 2772269 = 1039601) (by norm_num)
theorem B2772293 : Blo 1847625 2772293 := bbase (se 4 (by rfl) ⟨259902, by rfl⟩ : syracuseStep 2772293 = 519805) (by norm_num)
theorem B3509581 : Blo 1847625 3509581 := bbase (se 3 (by rfl) ⟨658046, by rfl⟩ : syracuseStep 3509581 = 1316093) (by norm_num)
theorem B2772317 : Blo 1847625 2772317 := bbase (se 3 (by rfl) ⟨519809, by rfl⟩ : syracuseStep 2772317 = 1039619) (by norm_num)
theorem B4681061 : Blo 1847625 4681061 := bbase (se 4 (by rfl) ⟨438849, by rfl⟩ : syracuseStep 4681061 = 877699) (by norm_num)
theorem B2772341 : Blo 1847625 2772341 := bbase (se 5 (by rfl) ⟨129953, by rfl⟩ : syracuseStep 2772341 = 259907) (by norm_num)
theorem B2772365 : Blo 1847625 2772365 := bbase (se 3 (by rfl) ⟨519818, by rfl⟩ : syracuseStep 2772365 = 1039637) (by norm_num)
theorem B2772389 : Blo 1847625 2772389 := bbase (se 4 (by rfl) ⟨259911, by rfl⟩ : syracuseStep 2772389 = 519823) (by norm_num)
theorem B2772413 : Blo 1847625 2772413 := bbase (se 3 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 2772413 = 1039655) (by norm_num)
theorem B2772437 : Blo 1847625 2772437 := bbase (se 7 (by rfl) ⟨32489, by rfl⟩ : syracuseStep 2772437 = 64979) (by norm_num)
theorem B5336533 : Blo 1847625 5336533 := bbase (se 7 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 5336533 = 125075) (by norm_num)
theorem B3509725 : Blo 1847625 3509725 := bbase (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) (by norm_num)
theorem B2108897 : Blo 1847625 2108897 := bbase (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) (by norm_num)
theorem B8883685 : Blo 1847625 8883685 := bbase (se 4 (by rfl) ⟨832845, by rfl⟩ : syracuseStep 8883685 = 1665691) (by norm_num)
theorem B2772461 : Blo 1847625 2772461 := bbase (se 3 (by rfl) ⟨519836, by rfl⟩ : syracuseStep 2772461 = 1039673) (by norm_num)
theorem B6237701 : Blo 1847625 6237701 := bbase (se 4 (by rfl) ⟨584784, by rfl⟩ : syracuseStep 6237701 = 1169569) (by norm_num)
theorem B2772485 : Blo 1847625 2772485 := bbase (se 4 (by rfl) ⟨259920, by rfl⟩ : syracuseStep 2772485 = 519841) (by norm_num)
theorem B2772509 : Blo 1847625 2772509 := bbase (se 3 (by rfl) ⟨519845, by rfl⟩ : syracuseStep 2772509 = 1039691) (by norm_num)
theorem B4681253 : Blo 1847625 4681253 := bbase (se 4 (by rfl) ⟨438867, by rfl⟩ : syracuseStep 4681253 = 877735) (by norm_num)
theorem B2772533 : Blo 1847625 2772533 := bbase (se 5 (by rfl) ⟨129962, by rfl⟩ : syracuseStep 2772533 = 259925) (by norm_num)
theorem B9358901 : Blo 1847625 9358901 := bbase (se 5 (by rfl) ⟨438698, by rfl⟩ : syracuseStep 9358901 = 877397) (by norm_num)
theorem B2772557 : Blo 1847625 2772557 := bbase (se 3 (by rfl) ⟨519854, by rfl⟩ : syracuseStep 2772557 = 1039709) (by norm_num)
theorem B2772581 : Blo 1847625 2772581 := bbase (se 4 (by rfl) ⟨259929, by rfl⟩ : syracuseStep 2772581 = 519859) (by norm_num)
theorem B2338409 : Blo 1847625 2338409 := bbase (se 2 (by rfl) ⟨876903, by rfl⟩ : syracuseStep 2338409 = 1753807) (by norm_num)
theorem B2772605 : Blo 1847625 2772605 := bbase (se 3 (by rfl) ⟨519863, by rfl⟩ : syracuseStep 2772605 = 1039727) (by norm_num)
theorem B3509885 : Blo 1847625 3509885 := bbase (se 3 (by rfl) ⟨658103, by rfl⟩ : syracuseStep 3509885 = 1316207) (by norm_num)
theorem B2772629 : Blo 1847625 2772629 := bbase (se 6 (by rfl) ⟨64983, by rfl⟩ : syracuseStep 2772629 = 129967) (by norm_num)
theorem B2338465 : Blo 1847625 2338465 := bbase (se 2 (by rfl) ⟨876924, by rfl⟩ : syracuseStep 2338465 = 1753849) (by norm_num)
theorem B2371237 : Blo 1847625 2371237 := bbase (se 4 (by rfl) ⟨222303, by rfl⟩ : syracuseStep 2371237 = 444607) (by norm_num)
theorem B2772653 : Blo 1847625 2772653 := bbase (se 3 (by rfl) ⟨519872, by rfl⟩ : syracuseStep 2772653 = 1039745) (by norm_num)
theorem B2772677 : Blo 1847625 2772677 := bbase (se 4 (by rfl) ⟨259938, by rfl⟩ : syracuseStep 2772677 = 519877) (by norm_num)
theorem B2772701 : Blo 1847625 2772701 := bbase (se 3 (by rfl) ⟨519881, by rfl⟩ : syracuseStep 2772701 = 1039763) (by norm_num)
theorem B2772725 : Blo 1847625 2772725 := bbase (se 5 (by rfl) ⟨129971, by rfl⟩ : syracuseStep 2772725 = 259943) (by norm_num)
theorem B2338561 : Blo 1847625 2338561 := bbase (se 2 (by rfl) ⟨876960, by rfl⟩ : syracuseStep 2338561 = 1753921) (by norm_num)
theorem B4157189 : Blo 1847625 4157189 := bbase (se 4 (by rfl) ⟨389736, by rfl⟩ : syracuseStep 4157189 = 779473) (by norm_num)
theorem B2772749 : Blo 1847625 2772749 := bbase (se 3 (by rfl) ⟨519890, by rfl⟩ : syracuseStep 2772749 = 1039781) (by norm_num)
theorem B3510029 : Blo 1847625 3510029 := bbase (se 3 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 3510029 = 1316261) (by norm_num)
theorem B2772773 : Blo 1847625 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B13324085 : Blo 1847625 13324085 := bbase (se 5 (by rfl) ⟨624566, by rfl⟩ : syracuseStep 13324085 = 1249133) (by norm_num)
theorem B2772797 : Blo 1847625 2772797 := bbase (se 3 (by rfl) ⟨519899, by rfl⟩ : syracuseStep 2772797 = 1039799) (by norm_num)
theorem B4157261 : Blo 1847625 4157261 := bbase (se 3 (by rfl) ⟨779486, by rfl⟩ : syracuseStep 4157261 = 1558973) (by norm_num)
theorem B3329869 : Blo 1847625 3329869 := bbase (se 3 (by rfl) ⟨624350, by rfl⟩ : syracuseStep 3329869 = 1248701) (by norm_num)
theorem B17764181 : Blo 1847625 17764181 := bbase (se 9 (by rfl) ⟨52043, by rfl⟩ : syracuseStep 17764181 = 104087) (by norm_num)
theorem B2772821 : Blo 1847625 2772821 := bbase (se 9 (by rfl) ⟨8123, by rfl⟩ : syracuseStep 2772821 = 16247) (by norm_num)
theorem B2772845 : Blo 1847625 2772845 := bbase (se 3 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 2772845 = 1039817) (by norm_num)
theorem B4681597 : Blo 1847625 4681597 := bbase (se 3 (by rfl) ⟨877799, by rfl⟩ : syracuseStep 4681597 = 1755599) (by norm_num)
theorem B2772869 : Blo 1847625 2772869 := bbase (se 4 (by rfl) ⟨259956, by rfl⟩ : syracuseStep 2772869 = 519913) (by norm_num)
theorem B4157333 : Blo 1847625 4157333 := bbase (se 6 (by rfl) ⟨97437, by rfl⟩ : syracuseStep 4157333 = 194875) (by norm_num)
theorem B2772893 : Blo 1847625 2772893 := bbase (se 3 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 2772893 = 1039835) (by norm_num)
theorem B2338733 : Blo 1847625 2338733 := bbase (se 3 (by rfl) ⟨438512, by rfl⟩ : syracuseStep 2338733 = 877025) (by norm_num)
theorem B6238133 : Blo 1847625 6238133 := bbase (se 5 (by rfl) ⟨292412, by rfl⟩ : syracuseStep 6238133 = 584825) (by norm_num)
theorem B2772917 : Blo 1847625 2772917 := bbase (se 5 (by rfl) ⟨129980, by rfl⟩ : syracuseStep 2772917 = 259961) (by norm_num)
theorem B2772941 : Blo 1847625 2772941 := bbase (se 3 (by rfl) ⟨519926, by rfl⟩ : syracuseStep 2772941 = 1039853) (by norm_num)
theorem B4157405 : Blo 1847625 4157405 := bbase (se 3 (by rfl) ⟨779513, by rfl⟩ : syracuseStep 4157405 = 1559027) (by norm_num)
theorem B3330013 : Blo 1847625 3330013 := bbase (se 3 (by rfl) ⟨624377, by rfl⟩ : syracuseStep 3330013 = 1248755) (by norm_num)
theorem B2338789 : Blo 1847625 2338789 := bbase (se 4 (by rfl) ⟨219261, by rfl⟩ : syracuseStep 2338789 = 438523) (by norm_num)
theorem B2772965 : Blo 1847625 2772965 := bbase (se 4 (by rfl) ⟨259965, by rfl⟩ : syracuseStep 2772965 = 519931) (by norm_num)
theorem B4681709 : Blo 1847625 4681709 := bbase (se 3 (by rfl) ⟨877820, by rfl⟩ : syracuseStep 4681709 = 1755641) (by norm_num)
theorem B2772989 : Blo 1847625 2772989 := bbase (se 3 (by rfl) ⟨519935, by rfl⟩ : syracuseStep 2772989 = 1039871) (by norm_num)
theorem B2773013 : Blo 1847625 2773013 := bbase (se 6 (by rfl) ⟨64992, by rfl⟩ : syracuseStep 2773013 = 129985) (by norm_num)
theorem B4157477 : Blo 1847625 4157477 := bbase (se 4 (by rfl) ⟨389763, by rfl⟩ : syracuseStep 4157477 = 779527) (by norm_num)
theorem B2773037 : Blo 1847625 2773037 := bbase (se 3 (by rfl) ⟨519944, by rfl⟩ : syracuseStep 2773037 = 1039889) (by norm_num)
theorem B3510317 : Blo 1847625 3510317 := bbase (se 3 (by rfl) ⟨658184, by rfl⟩ : syracuseStep 3510317 = 1316369) (by norm_num)
theorem B2338885 : Blo 1847625 2338885 := bbase (se 4 (by rfl) ⟨219270, by rfl⟩ : syracuseStep 2338885 = 438541) (by norm_num)
theorem B2773061 : Blo 1847625 2773061 := bbase (se 4 (by rfl) ⟨259974, by rfl⟩ : syracuseStep 2773061 = 519949) (by norm_num)
theorem B33747029 : Blo 1847625 33747029 := bbase (se 8 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 33747029 = 395473) (by norm_num)
theorem B2773085 : Blo 1847625 2773085 := bbase (se 3 (by rfl) ⟨519953, by rfl⟩ : syracuseStep 2773085 = 1039907) (by norm_num)
theorem B7491685 : Blo 1847625 7491685 := bbase (se 4 (by rfl) ⟨702345, by rfl⟩ : syracuseStep 7491685 = 1404691) (by norm_num)
theorem B2437225 : Blo 1847625 2437225 := bbase (se 2 (by rfl) ⟨913959, by rfl⟩ : syracuseStep 2437225 = 1827919) (by norm_num)
theorem B4157549 : Blo 1847625 4157549 := bbase (se 3 (by rfl) ⟨779540, by rfl⟩ : syracuseStep 4157549 = 1559081) (by norm_num)
theorem B2961517 : Blo 1847625 2961517 := bbase (se 3 (by rfl) ⟨555284, by rfl⟩ : syracuseStep 2961517 = 1110569) (by norm_num)
theorem B2773109 : Blo 1847625 2773109 := bbase (se 5 (by rfl) ⟨129989, by rfl⟩ : syracuseStep 2773109 = 259979) (by norm_num)
theorem B2773133 : Blo 1847625 2773133 := bbase (se 3 (by rfl) ⟨519962, by rfl⟩ : syracuseStep 2773133 = 1039925) (by norm_num)
theorem B2773157 : Blo 1847625 2773157 := bbase (se 4 (by rfl) ⟨259983, by rfl⟩ : syracuseStep 2773157 = 519967) (by norm_num)
theorem B4157621 : Blo 1847625 4157621 := bbase (se 5 (by rfl) ⟨194888, by rfl⟩ : syracuseStep 4157621 = 389777) (by norm_num)
theorem B3330229 : Blo 1847625 3330229 := bbase (se 5 (by rfl) ⟨156104, by rfl⟩ : syracuseStep 3330229 = 312209) (by norm_num)
theorem B2773181 : Blo 1847625 2773181 := bbase (se 3 (by rfl) ⟨519971, by rfl⟩ : syracuseStep 2773181 = 1039943) (by norm_num)
theorem B2887877 : Blo 1847625 2887877 := bbase (se 4 (by rfl) ⟨270738, by rfl⟩ : syracuseStep 2887877 = 541477) (by norm_num)
theorem B3510469 : Blo 1847625 3510469 := bbase (se 4 (by rfl) ⟨329106, by rfl⟩ : syracuseStep 3510469 = 658213) (by norm_num)
theorem B2773205 : Blo 1847625 2773205 := bbase (se 7 (by rfl) ⟨32498, by rfl⟩ : syracuseStep 2773205 = 64997) (by norm_num)
theorem B2773229 : Blo 1847625 2773229 := bbase (se 3 (by rfl) ⟨519980, by rfl⟩ : syracuseStep 2773229 = 1039961) (by norm_num)
theorem B2339057 : Blo 1847625 2339057 := bbase (se 2 (by rfl) ⟨877146, by rfl⟩ : syracuseStep 2339057 = 1754293) (by norm_num)
theorem B4157693 : Blo 1847625 4157693 := bbase (se 3 (by rfl) ⟨779567, by rfl⟩ : syracuseStep 4157693 = 1559135) (by norm_num)
theorem B2773253 : Blo 1847625 2773253 := bbase (se 4 (by rfl) ⟨259992, by rfl⟩ : syracuseStep 2773253 = 519985) (by norm_num)
theorem B2371853 : Blo 1847625 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B2773277 : Blo 1847625 2773277 := bbase (se 3 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 2773277 = 1039979) (by norm_num)
theorem B2339113 : Blo 1847625 2339113 := bbase (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) (by norm_num)
theorem B2773301 : Blo 1847625 2773301 := bbase (se 5 (by rfl) ⟨129998, by rfl⟩ : syracuseStep 2773301 = 259997) (by norm_num)
theorem B5624117 : Blo 1847625 5624117 := bbase (se 5 (by rfl) ⟨263630, by rfl⟩ : syracuseStep 5624117 = 527261) (by norm_num)
theorem B4157765 : Blo 1847625 4157765 := bbase (se 4 (by rfl) ⟨389790, by rfl⟩ : syracuseStep 4157765 = 779581) (by norm_num)
theorem B2773325 : Blo 1847625 2773325 := bbase (se 3 (by rfl) ⟨519998, by rfl⟩ : syracuseStep 2773325 = 1039997) (by norm_num)
theorem B2167133 : Blo 1847625 2167133 := bbase (se 3 (by rfl) ⟨406337, by rfl⟩ : syracuseStep 2167133 = 812675) (by norm_num)
theorem B6238565 : Blo 1847625 6238565 := bbase (se 4 (by rfl) ⟨584865, by rfl⟩ : syracuseStep 6238565 = 1169731) (by norm_num)
theorem B2773349 : Blo 1847625 2773349 := bbase (se 4 (by rfl) ⟨260001, by rfl⟩ : syracuseStep 2773349 = 520003) (by norm_num)
theorem B2773373 : Blo 1847625 2773373 := bbase (se 3 (by rfl) ⟨520007, by rfl⟩ : syracuseStep 2773373 = 1040015) (by norm_num)
theorem B2339209 : Blo 1847625 2339209 := bbase (se 2 (by rfl) ⟨877203, by rfl⟩ : syracuseStep 2339209 = 1754407) (by norm_num)
theorem B4157837 : Blo 1847625 4157837 := bbase (se 3 (by rfl) ⟨779594, by rfl⟩ : syracuseStep 4157837 = 1559189) (by norm_num)
theorem B2773397 : Blo 1847625 2773397 := bbase (se 6 (by rfl) ⟨65001, by rfl⟩ : syracuseStep 2773397 = 130003) (by norm_num)
theorem B2773421 : Blo 1847625 2773421 := bbase (se 3 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 2773421 = 1040033) (by norm_num)
theorem B2773445 : Blo 1847625 2773445 := bbase (se 4 (by rfl) ⟨260010, by rfl⟩ : syracuseStep 2773445 = 520021) (by norm_num)
theorem B4157909 : Blo 1847625 4157909 := bbase (se 7 (by rfl) ⟨48725, by rfl⟩ : syracuseStep 4157909 = 97451) (by norm_num)
theorem B2773469 : Blo 1847625 2773469 := bbase (se 3 (by rfl) ⟨520025, by rfl⟩ : syracuseStep 2773469 = 1040051) (by norm_num)
theorem B2773493 : Blo 1847625 2773493 := bbase (se 5 (by rfl) ⟨130007, by rfl⟩ : syracuseStep 2773493 = 260015) (by norm_num)
theorem B3510773 : Blo 1847625 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B2773517 : Blo 1847625 2773517 := bbase (se 3 (by rfl) ⟨520034, by rfl⟩ : syracuseStep 2773517 = 1040069) (by norm_num)
theorem B4157981 : Blo 1847625 4157981 := bbase (se 3 (by rfl) ⟨779621, by rfl⟩ : syracuseStep 4157981 = 1559243) (by norm_num)
theorem B2773541 : Blo 1847625 2773541 := bbase (se 4 (by rfl) ⟨260019, by rfl⟩ : syracuseStep 2773541 = 520039) (by norm_num)
theorem B2339381 : Blo 1847625 2339381 := bbase (se 5 (by rfl) ⟨109658, by rfl⟩ : syracuseStep 2339381 = 219317) (by norm_num)
theorem B4002365 : Blo 1847625 4002365 := bbase (se 3 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 4002365 = 1500887) (by norm_num)
theorem B2773565 : Blo 1847625 2773565 := bbase (se 3 (by rfl) ⟨520043, by rfl⟩ : syracuseStep 2773565 = 1040087) (by norm_num)
theorem B2773589 : Blo 1847625 2773589 := bbase (se 8 (by rfl) ⟨16251, by rfl⟩ : syracuseStep 2773589 = 32503) (by norm_num)
theorem B4158053 : Blo 1847625 4158053 := bbase (se 4 (by rfl) ⟨389817, by rfl⟩ : syracuseStep 4158053 = 779635) (by norm_num)
theorem B5263973 : Blo 1847625 5263973 := bbase (se 4 (by rfl) ⟨493497, by rfl⟩ : syracuseStep 5263973 = 986995) (by norm_num)
theorem B2339437 : Blo 1847625 2339437 := bbase (se 3 (by rfl) ⟨438644, by rfl⟩ : syracuseStep 2339437 = 877289) (by norm_num)
theorem B2773613 : Blo 1847625 2773613 := bbase (se 3 (by rfl) ⟨520052, by rfl⟩ : syracuseStep 2773613 = 1040105) (by norm_num)
theorem B2773637 : Blo 1847625 2773637 := bbase (se 4 (by rfl) ⟨260028, by rfl⟩ : syracuseStep 2773637 = 520057) (by norm_num)
theorem B2773661 : Blo 1847625 2773661 := bbase (se 3 (by rfl) ⟨520061, by rfl⟩ : syracuseStep 2773661 = 1040123) (by norm_num)
theorem B4158125 : Blo 1847625 4158125 := bbase (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) (by norm_num)
theorem B13324981 : Blo 1847625 13324981 := bbase (se 5 (by rfl) ⟨624608, by rfl⟩ : syracuseStep 13324981 = 1249217) (by norm_num)
theorem B2773685 : Blo 1847625 2773685 := bbase (se 5 (by rfl) ⟨130016, by rfl⟩ : syracuseStep 2773685 = 260033) (by norm_num)
theorem B2339533 : Blo 1847625 2339533 := bbase (se 3 (by rfl) ⟨438662, by rfl⟩ : syracuseStep 2339533 = 877325) (by norm_num)
theorem B2773709 : Blo 1847625 2773709 := bbase (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) (by norm_num)
theorem B2773733 : Blo 1847625 2773733 := bbase (se 4 (by rfl) ⟨260037, by rfl⟩ : syracuseStep 2773733 = 520075) (by norm_num)
theorem B4158197 : Blo 1847625 4158197 := bbase (se 5 (by rfl) ⟨194915, by rfl⟩ : syracuseStep 4158197 = 389831) (by norm_num)
theorem B2773757 : Blo 1847625 2773757 := bbase (se 3 (by rfl) ⟨520079, by rfl⟩ : syracuseStep 2773757 = 1040159) (by norm_num)
theorem B2667269 : Blo 1847625 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B3330821 : Blo 1847625 3330821 := bbase (se 4 (by rfl) ⟨312264, by rfl⟩ : syracuseStep 3330821 = 624529) (by norm_num)
theorem B2962189 : Blo 1847625 2962189 := bbase (se 3 (by rfl) ⟨555410, by rfl⟩ : syracuseStep 2962189 = 1110821) (by norm_num)
theorem B6238997 : Blo 1847625 6238997 := bbase (se 6 (by rfl) ⟨146226, by rfl⟩ : syracuseStep 6238997 = 292453) (by norm_num)
theorem B2773781 : Blo 1847625 2773781 := bbase (se 6 (by rfl) ⟨65010, by rfl⟩ : syracuseStep 2773781 = 130021) (by norm_num)
theorem B2773805 : Blo 1847625 2773805 := bbase (se 3 (by rfl) ⟨520088, by rfl⟩ : syracuseStep 2773805 = 1040177) (by norm_num)
theorem B4158269 : Blo 1847625 4158269 := bbase (se 3 (by rfl) ⟨779675, by rfl⟩ : syracuseStep 4158269 = 1559351) (by norm_num)
theorem B9360197 : Blo 1847625 9360197 := bbase (se 4 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 9360197 = 1755037) (by norm_num)
theorem B2773829 : Blo 1847625 2773829 := bbase (se 4 (by rfl) ⟨260046, by rfl⟩ : syracuseStep 2773829 = 520093) (by norm_num)
theorem B2773853 : Blo 1847625 2773853 := bbase (se 3 (by rfl) ⟨520097, by rfl⟩ : syracuseStep 2773853 = 1040195) (by norm_num)
theorem B2773877 : Blo 1847625 2773877 := bbase (se 5 (by rfl) ⟨130025, by rfl⟩ : syracuseStep 2773877 = 260051) (by norm_num)
theorem B2339705 : Blo 1847625 2339705 := bbase (se 2 (by rfl) ⟨877389, by rfl⟩ : syracuseStep 2339705 = 1754779) (by norm_num)
theorem B4158341 : Blo 1847625 4158341 := bbase (se 4 (by rfl) ⟨389844, by rfl⟩ : syracuseStep 4158341 = 779689) (by norm_num)
theorem B2773901 : Blo 1847625 2773901 := bbase (se 3 (by rfl) ⟨520106, by rfl⟩ : syracuseStep 2773901 = 1040213) (by norm_num)
theorem B3117973 : Blo 1847625 3117973 := bbase (se 6 (by rfl) ⟨73077, by rfl⟩ : syracuseStep 3117973 = 146155) (by norm_num)
theorem B2773925 : Blo 1847625 2773925 := bbase (se 4 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 2773925 = 520111) (by norm_num)
theorem B2339761 : Blo 1847625 2339761 := bbase (se 2 (by rfl) ⟨877410, by rfl⟩ : syracuseStep 2339761 = 1754821) (by norm_num)
theorem B2773949 : Blo 1847625 2773949 := bbase (se 3 (by rfl) ⟨520115, by rfl⟩ : syracuseStep 2773949 = 1040231) (by norm_num)
theorem B4158413 : Blo 1847625 4158413 := bbase (se 3 (by rfl) ⟨779702, by rfl⟩ : syracuseStep 4158413 = 1559405) (by norm_num)
theorem B2773973 : Blo 1847625 2773973 := bbase (se 7 (by rfl) ⟨32507, by rfl⟩ : syracuseStep 2773973 = 65015) (by norm_num)
theorem B3331037 : Blo 1847625 3331037 := bbase (se 3 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 3331037 = 1249139) (by norm_num)
theorem B2888677 : Blo 1847625 2888677 := bbase (se 4 (by rfl) ⟨270813, by rfl⟩ : syracuseStep 2888677 = 541627) (by norm_num)
theorem B3118061 : Blo 1847625 3118061 := bbase (se 3 (by rfl) ⟨584636, by rfl⟩ : syracuseStep 3118061 = 1169273) (by norm_num)
theorem B7017461 : Blo 1847625 7017461 := bbase (se 5 (by rfl) ⟨328943, by rfl⟩ : syracuseStep 7017461 = 657887) (by norm_num)
theorem B13505525 : Blo 1847625 13505525 := bbase (se 5 (by rfl) ⟨633071, by rfl⟩ : syracuseStep 13505525 = 1266143) (by norm_num)
theorem B2774021 : Blo 1847625 2774021 := bbase (se 4 (by rfl) ⟨260064, by rfl⟩ : syracuseStep 2774021 = 520129) (by norm_num)
theorem B2339857 : Blo 1847625 2339857 := bbase (se 2 (by rfl) ⟨877446, by rfl⟩ : syracuseStep 2339857 = 1754893) (by norm_num)
theorem B4158485 : Blo 1847625 4158485 := bbase (se 6 (by rfl) ⟨97464, by rfl⟩ : syracuseStep 4158485 = 194929) (by norm_num)
theorem B2774045 : Blo 1847625 2774045 := bbase (se 3 (by rfl) ⟨520133, by rfl⟩ : syracuseStep 2774045 = 1040267) (by norm_num)
theorem B2774069 : Blo 1847625 2774069 := bbase (se 5 (by rfl) ⟨130034, by rfl⟩ : syracuseStep 2774069 = 260069) (by norm_num)
theorem B2774093 : Blo 1847625 2774093 := bbase (se 3 (by rfl) ⟨520142, by rfl⟩ : syracuseStep 2774093 = 1040285) (by norm_num)
theorem B4158557 : Blo 1847625 4158557 := bbase (se 3 (by rfl) ⟨779729, by rfl⟩ : syracuseStep 4158557 = 1559459) (by norm_num)
theorem B2774117 : Blo 1847625 2774117 := bbase (se 4 (by rfl) ⟨260073, by rfl⟩ : syracuseStep 2774117 = 520147) (by norm_num)
theorem B3118189 : Blo 1847625 3118189 := bbase (se 3 (by rfl) ⟨584660, by rfl⟩ : syracuseStep 3118189 = 1169321) (by norm_num)
theorem B2774141 : Blo 1847625 2774141 := bbase (se 3 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 2774141 = 1040303) (by norm_num)
theorem B2774165 : Blo 1847625 2774165 := bbase (se 6 (by rfl) ⟨65019, by rfl⟩ : syracuseStep 2774165 = 130039) (by norm_num)
theorem B4158629 : Blo 1847625 4158629 := bbase (se 4 (by rfl) ⟨389871, by rfl⟩ : syracuseStep 4158629 = 779743) (by norm_num)
theorem B2774189 : Blo 1847625 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B2340029 : Blo 1847625 2340029 := bbase (se 3 (by rfl) ⟨438755, by rfl⟩ : syracuseStep 2340029 = 877511) (by norm_num)
theorem B3118277 : Blo 1847625 3118277 := bbase (se 4 (by rfl) ⟨292338, by rfl⟩ : syracuseStep 3118277 = 584677) (by norm_num)
theorem B6239429 : Blo 1847625 6239429 := bbase (se 4 (by rfl) ⟨584946, by rfl⟩ : syracuseStep 6239429 = 1169893) (by norm_num)
theorem B2774213 : Blo 1847625 2774213 := bbase (se 4 (by rfl) ⟨260082, by rfl⟩ : syracuseStep 2774213 = 520165) (by norm_num)
theorem B2774237 : Blo 1847625 2774237 := bbase (se 3 (by rfl) ⟨520169, by rfl⟩ : syracuseStep 2774237 = 1040339) (by norm_num)
theorem B4158701 : Blo 1847625 4158701 := bbase (se 3 (by rfl) ⟨779756, by rfl⟩ : syracuseStep 4158701 = 1559513) (by norm_num)
theorem B2340085 : Blo 1847625 2340085 := bbase (se 5 (by rfl) ⟨109691, by rfl⟩ : syracuseStep 2340085 = 219383) (by norm_num)
theorem B2774261 : Blo 1847625 2774261 := bbase (se 5 (by rfl) ⟨130043, by rfl⟩ : syracuseStep 2774261 = 260087) (by norm_num)
theorem B3331325 : Blo 1847625 3331325 := bbase (se 3 (by rfl) ⟨624623, by rfl⟩ : syracuseStep 3331325 = 1249247) (by norm_num)
theorem B2774285 : Blo 1847625 2774285 := bbase (se 3 (by rfl) ⟨520178, by rfl⟩ : syracuseStep 2774285 = 1040357) (by norm_num)
theorem B7017749 : Blo 1847625 7017749 := bbase (se 6 (by rfl) ⟨164478, by rfl⟩ : syracuseStep 7017749 = 328957) (by norm_num)
theorem B2774309 : Blo 1847625 2774309 := bbase (se 4 (by rfl) ⟨260091, by rfl⟩ : syracuseStep 2774309 = 520183) (by norm_num)
theorem B4158773 : Blo 1847625 4158773 := bbase (se 5 (by rfl) ⟨194942, by rfl⟩ : syracuseStep 4158773 = 389885) (by norm_num)
theorem B1873213 : Blo 1847625 1873213 := bbase (se 3 (by rfl) ⟨351227, by rfl⟩ : syracuseStep 1873213 = 702455) (by norm_num)
theorem B2774333 : Blo 1847625 2774333 := bbase (se 3 (by rfl) ⟨520187, by rfl⟩ : syracuseStep 2774333 = 1040375) (by norm_num)
theorem B3118405 : Blo 1847625 3118405 := bbase (se 4 (by rfl) ⟨292350, by rfl⟩ : syracuseStep 3118405 = 584701) (by norm_num)
theorem B2340181 : Blo 1847625 2340181 := bbase (se 13 (by rfl) ⟨428, by rfl⟩ : syracuseStep 2340181 = 857) (by norm_num)
theorem B2774357 : Blo 1847625 2774357 := bbase (se 16 (by rfl) ⟨63, by rfl⟩ : syracuseStep 2774357 = 127) (by norm_num)
theorem B2774381 : Blo 1847625 2774381 := bbase (se 3 (by rfl) ⟨520196, by rfl⟩ : syracuseStep 2774381 = 1040393) (by norm_num)
theorem B4158845 : Blo 1847625 4158845 := bbase (se 3 (by rfl) ⟨779783, by rfl⟩ : syracuseStep 4158845 = 1559567) (by norm_num)
theorem B2774405 : Blo 1847625 2774405 := bbase (se 4 (by rfl) ⟨260100, by rfl⟩ : syracuseStep 2774405 = 520201) (by norm_num)
theorem B3118493 : Blo 1847625 3118493 := bbase (se 3 (by rfl) ⟨584717, by rfl⟩ : syracuseStep 3118493 = 1169435) (by norm_num)
theorem B2774429 : Blo 1847625 2774429 := bbase (se 3 (by rfl) ⟨520205, by rfl⟩ : syracuseStep 2774429 = 1040411) (by norm_num)
theorem B4158917 : Blo 1847625 4158917 := bbase (se 4 (by rfl) ⟨389898, by rfl⟩ : syracuseStep 4158917 = 779797) (by norm_num)
theorem B2340353 : Blo 1847625 2340353 := bbase (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) (by norm_num)
theorem B4158989 : Blo 1847625 4158989 := bbase (se 3 (by rfl) ⟨779810, by rfl⟩ : syracuseStep 4158989 = 1559621) (by norm_num)
theorem B35517973 : Blo 1847625 35517973 := bbase (se 6 (by rfl) ⟨832452, by rfl⟩ : syracuseStep 35517973 = 1664905) (by norm_num)
theorem B3118621 : Blo 1847625 3118621 := bbase (se 3 (by rfl) ⟨584741, by rfl⟩ : syracuseStep 3118621 = 1169483) (by norm_num)
theorem B2340409 : Blo 1847625 2340409 := bbase (se 2 (by rfl) ⟨877653, by rfl⟩ : syracuseStep 2340409 = 1755307) (by norm_num)
theorem B2773997 : Blo 1847625 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B4159061 : Blo 1847625 4159061 := bbase (se 8 (by rfl) ⟨24369, by rfl⟩ : syracuseStep 4159061 = 48739) (by norm_num)
theorem B3118709 : Blo 1847625 3118709 := bbase (se 5 (by rfl) ⟨146189, by rfl⟩ : syracuseStep 3118709 = 292379) (by norm_num)
theorem B6239861 : Blo 1847625 6239861 := bbase (se 5 (by rfl) ⟨292493, by rfl⟩ : syracuseStep 6239861 = 584987) (by norm_num)
theorem B10532501 : Blo 1847625 10532501 := bbase (se 6 (by rfl) ⟨246855, by rfl⟩ : syracuseStep 10532501 = 493711) (by norm_num)
theorem B2340505 : Blo 1847625 2340505 := bbase (se 2 (by rfl) ⟨877689, by rfl⟩ : syracuseStep 2340505 = 1755379) (by norm_num)
theorem B4159133 : Blo 1847625 4159133 := bbase (se 3 (by rfl) ⟨779837, by rfl⟩ : syracuseStep 4159133 = 1559675) (by norm_num)
theorem B4159205 : Blo 1847625 4159205 := bbase (se 4 (by rfl) ⟨389925, by rfl⟩ : syracuseStep 4159205 = 779851) (by norm_num)
theorem B3946229 : Blo 1847625 3946229 := bbase (se 5 (by rfl) ⟨184979, by rfl⟩ : syracuseStep 3946229 = 369959) (by norm_num)
theorem B3118837 : Blo 1847625 3118837 := bbase (se 5 (by rfl) ⟨146195, by rfl⟩ : syracuseStep 3118837 = 292391) (by norm_num)
theorem B5265157 : Blo 1847625 5265157 := bbase (se 4 (by rfl) ⟨493608, by rfl⟩ : syracuseStep 5265157 = 987217) (by norm_num)
theorem B10524437 : Blo 1847625 10524437 := bbase (se 6 (by rfl) ⟨246666, by rfl⟩ : syracuseStep 10524437 = 493333) (by norm_num)
theorem B4159277 : Blo 1847625 4159277 := bbase (se 3 (by rfl) ⟨779864, by rfl⟩ : syracuseStep 4159277 = 1559729) (by norm_num)
theorem B2340677 : Blo 1847625 2340677 := bbase (se 4 (by rfl) ⟨219438, by rfl⟩ : syracuseStep 2340677 = 438877) (by norm_num)
theorem B3118925 : Blo 1847625 3118925 := bbase (se 3 (by rfl) ⟨584798, by rfl⟩ : syracuseStep 3118925 = 1169597) (by norm_num)
theorem B2078581 : Blo 1847625 2078581 := bbase (se 5 (by rfl) ⟨97433, by rfl⟩ : syracuseStep 2078581 = 194867) (by norm_num)
theorem B4159349 : Blo 1847625 4159349 := bbase (se 5 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 4159349 = 389939) (by norm_num)
theorem B2340733 : Blo 1847625 2340733 := bbase (se 3 (by rfl) ⟨438887, by rfl⟩ : syracuseStep 2340733 = 877775) (by norm_num)
theorem B18970517 : Blo 1847625 18970517 := bbase (se 6 (by rfl) ⟨444621, by rfl⟩ : syracuseStep 18970517 = 889243) (by norm_num)
theorem B2078617 : Blo 1847625 2078617 := bbase (se 2 (by rfl) ⟨779481, by rfl⟩ : syracuseStep 2078617 = 1558963) (by norm_num)
theorem B5265317 : Blo 1847625 5265317 := bbase (se 4 (by rfl) ⟨493623, by rfl⟩ : syracuseStep 5265317 = 987247) (by norm_num)
theorem B2078653 : Blo 1847625 2078653 := bbase (se 3 (by rfl) ⟨389747, by rfl⟩ : syracuseStep 2078653 = 779495) (by norm_num)
theorem B4159421 : Blo 1847625 4159421 := bbase (se 3 (by rfl) ⟨779891, by rfl⟩ : syracuseStep 4159421 = 1559783) (by norm_num)
theorem B3119053 : Blo 1847625 3119053 := bbase (se 3 (by rfl) ⟨584822, by rfl⟩ : syracuseStep 3119053 = 1169645) (by norm_num)
theorem B2340829 : Blo 1847625 2340829 := bbase (se 3 (by rfl) ⟨438905, by rfl⟩ : syracuseStep 2340829 = 877811) (by norm_num)
theorem B2078689 : Blo 1847625 2078689 := bbase (se 2 (by rfl) ⟨779508, by rfl⟩ : syracuseStep 2078689 = 1559017) (by norm_num)
theorem B2078725 : Blo 1847625 2078725 := bbase (se 4 (by rfl) ⟨194880, by rfl⟩ : syracuseStep 2078725 = 389761) (by norm_num)
theorem B4159493 : Blo 1847625 4159493 := bbase (se 4 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 4159493 = 779905) (by norm_num)
theorem B3119141 : Blo 1847625 3119141 := bbase (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) (by norm_num)
theorem B6240293 : Blo 1847625 6240293 := bbase (se 4 (by rfl) ⟨585027, by rfl⟩ : syracuseStep 6240293 = 1170055) (by norm_num)
theorem B2078761 : Blo 1847625 2078761 := bbase (se 2 (by rfl) ⟨779535, by rfl⟩ : syracuseStep 2078761 = 1559071) (by norm_num)
theorem B2078797 : Blo 1847625 2078797 := bbase (se 3 (by rfl) ⟨389774, by rfl⟩ : syracuseStep 2078797 = 779549) (by norm_num)
theorem B4159565 : Blo 1847625 4159565 := bbase (se 3 (by rfl) ⟨779918, by rfl⟩ : syracuseStep 4159565 = 1559837) (by norm_num)
theorem B9361493 : Blo 1847625 9361493 := bbase (se 8 (by rfl) ⟨54852, by rfl⟩ : syracuseStep 9361493 = 109705) (by norm_num)
theorem B2078833 : Blo 1847625 2078833 := bbase (se 2 (by rfl) ⟨779562, by rfl⟩ : syracuseStep 2078833 = 1559125) (by norm_num)
theorem B2078869 : Blo 1847625 2078869 := bbase (se 6 (by rfl) ⟨48723, by rfl⟩ : syracuseStep 2078869 = 97447) (by norm_num)
theorem B4159637 : Blo 1847625 4159637 := bbase (se 6 (by rfl) ⟨97491, by rfl⟩ : syracuseStep 4159637 = 194983) (by norm_num)
theorem B5265557 : Blo 1847625 5265557 := bbase (se 6 (by rfl) ⟨123411, by rfl⟩ : syracuseStep 5265557 = 246823) (by norm_num)
theorem B3119269 : Blo 1847625 3119269 := bbase (se 4 (by rfl) ⟨292431, by rfl⟩ : syracuseStep 3119269 = 584863) (by norm_num)
theorem B2078905 : Blo 1847625 2078905 := bbase (se 2 (by rfl) ⟨779589, by rfl⟩ : syracuseStep 2078905 = 1559179) (by norm_num)
theorem B2078941 : Blo 1847625 2078941 := bbase (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) (by norm_num)
theorem B4159709 : Blo 1847625 4159709 := bbase (se 3 (by rfl) ⟨779945, by rfl⟩ : syracuseStep 4159709 = 1559891) (by norm_num)
theorem B3119357 : Blo 1847625 3119357 := bbase (se 3 (by rfl) ⟨584879, by rfl⟩ : syracuseStep 3119357 = 1169759) (by norm_num)
theorem B2078977 : Blo 1847625 2078977 := bbase (se 2 (by rfl) ⟨779616, by rfl⟩ : syracuseStep 2078977 = 1559233) (by norm_num)
theorem B2079013 : Blo 1847625 2079013 := bbase (se 4 (by rfl) ⟨194907, by rfl⟩ : syracuseStep 2079013 = 389815) (by norm_num)
theorem B4159781 : Blo 1847625 4159781 := bbase (se 4 (by rfl) ⟨389979, by rfl⟩ : syracuseStep 4159781 = 779959) (by norm_num)
theorem B2079049 : Blo 1847625 2079049 := bbase (se 2 (by rfl) ⟨779643, by rfl⟩ : syracuseStep 2079049 = 1559287) (by norm_num)
theorem B5265749 : Blo 1847625 5265749 := bbase (se 10 (by rfl) ⟨7713, by rfl⟩ : syracuseStep 5265749 = 15427) (by norm_num)
theorem B2079085 : Blo 1847625 2079085 := bbase (se 3 (by rfl) ⟨389828, by rfl⟩ : syracuseStep 2079085 = 779657) (by norm_num)
theorem B4159853 : Blo 1847625 4159853 := bbase (se 3 (by rfl) ⟨779972, by rfl⟩ : syracuseStep 4159853 = 1559945) (by norm_num)
theorem B3119485 : Blo 1847625 3119485 := bbase (se 3 (by rfl) ⟨584903, by rfl⟩ : syracuseStep 3119485 = 1169807) (by norm_num)
theorem B2079121 : Blo 1847625 2079121 := bbase (se 2 (by rfl) ⟨779670, by rfl⟩ : syracuseStep 2079121 = 1559341) (by norm_num)
theorem B6412709 : Blo 1847625 6412709 := bbase (se 4 (by rfl) ⟨601191, by rfl⟩ : syracuseStep 6412709 = 1202383) (by norm_num)
theorem B2079157 : Blo 1847625 2079157 := bbase (se 5 (by rfl) ⟨97460, by rfl⟩ : syracuseStep 2079157 = 194921) (by norm_num)
theorem B7018933 : Blo 1847625 7018933 := bbase (se 5 (by rfl) ⟨329012, by rfl⟩ : syracuseStep 7018933 = 658025) (by norm_num)
theorem B4159925 : Blo 1847625 4159925 := bbase (se 5 (by rfl) ⟨194996, by rfl⟩ : syracuseStep 4159925 = 389993) (by norm_num)
theorem B3119573 : Blo 1847625 3119573 := bbase (se 7 (by rfl) ⟨36557, by rfl⟩ : syracuseStep 3119573 = 73115) (by norm_num)
theorem B6240725 : Blo 1847625 6240725 := bbase (se 7 (by rfl) ⟨73133, by rfl⟩ : syracuseStep 6240725 = 146267) (by norm_num)
theorem B2079193 : Blo 1847625 2079193 := bbase (se 2 (by rfl) ⟨779697, by rfl⟩ : syracuseStep 2079193 = 1559395) (by norm_num)
theorem B3332573 : Blo 1847625 3332573 := bbase (se 3 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 3332573 = 1249715) (by norm_num)
theorem B3946981 : Blo 1847625 3946981 := bbase (se 4 (by rfl) ⟨370029, by rfl⟩ : syracuseStep 3946981 = 740059) (by norm_num)
theorem B9353717 : Blo 1847625 9353717 := bbase (se 5 (by rfl) ⟨438455, by rfl⟩ : syracuseStep 9353717 = 876911) (by norm_num)
theorem B2079229 : Blo 1847625 2079229 := bbase (se 3 (by rfl) ⟨389855, by rfl⟩ : syracuseStep 2079229 = 779711) (by norm_num)
theorem B4159997 : Blo 1847625 4159997 := bbase (se 3 (by rfl) ⟨779999, by rfl⟩ : syracuseStep 4159997 = 1559999) (by norm_num)
theorem B7494149 : Blo 1847625 7494149 := bbase (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) (by norm_num)
theorem B15784469 : Blo 1847625 15784469 := bbase (se 6 (by rfl) ⟨369948, by rfl⟩ : syracuseStep 15784469 = 739897) (by norm_num)
theorem B2079265 : Blo 1847625 2079265 := bbase (se 2 (by rfl) ⟨779724, by rfl⟩ : syracuseStep 2079265 = 1559449) (by norm_num)
theorem B2079301 : Blo 1847625 2079301 := bbase (se 4 (by rfl) ⟨194934, by rfl⟩ : syracuseStep 2079301 = 389869) (by norm_num)
theorem B4160069 : Blo 1847625 4160069 := bbase (se 4 (by rfl) ⟨390006, by rfl⟩ : syracuseStep 4160069 = 780013) (by norm_num)
theorem B3119701 : Blo 1847625 3119701 := bbase (se 8 (by rfl) ⟨18279, by rfl⟩ : syracuseStep 3119701 = 36559) (by norm_num)
theorem B2079337 : Blo 1847625 2079337 := bbase (se 2 (by rfl) ⟨779751, by rfl⟩ : syracuseStep 2079337 = 1559503) (by norm_num)
theorem B3947125 : Blo 1847625 3947125 := bbase (se 5 (by rfl) ⟨185021, by rfl⟩ : syracuseStep 3947125 = 370043) (by norm_num)
theorem B2079373 : Blo 1847625 2079373 := bbase (se 3 (by rfl) ⟨389882, by rfl⟩ : syracuseStep 2079373 = 779765) (by norm_num)
theorem B4160141 : Blo 1847625 4160141 := bbase (se 3 (by rfl) ⟨780026, by rfl⟩ : syracuseStep 4160141 = 1560053) (by norm_num)
theorem B11844245 : Blo 1847625 11844245 := bbase (se 6 (by rfl) ⟨277599, by rfl⟩ : syracuseStep 11844245 = 555199) (by norm_num)
theorem B3119789 : Blo 1847625 3119789 := bbase (se 3 (by rfl) ⟨584960, by rfl⟩ : syracuseStep 3119789 = 1169921) (by norm_num)
theorem B2079409 : Blo 1847625 2079409 := bbase (se 2 (by rfl) ⟨779778, by rfl⟩ : syracuseStep 2079409 = 1559557) (by norm_num)
theorem B2079445 : Blo 1847625 2079445 := bbase (se 7 (by rfl) ⟨24368, by rfl⟩ : syracuseStep 2079445 = 48737) (by norm_num)
theorem B4160213 : Blo 1847625 4160213 := bbase (se 7 (by rfl) ⟨48752, by rfl⟩ : syracuseStep 4160213 = 97505) (by norm_num)
theorem B7019237 : Blo 1847625 7019237 := bbase (se 4 (by rfl) ⟨658053, by rfl⟩ : syracuseStep 7019237 = 1316107) (by norm_num)
theorem B2079481 : Blo 1847625 2079481 := bbase (se 2 (by rfl) ⟨779805, by rfl⟩ : syracuseStep 2079481 = 1559611) (by norm_num)
theorem B2079517 : Blo 1847625 2079517 := bbase (se 3 (by rfl) ⟨389909, by rfl⟩ : syracuseStep 2079517 = 779819) (by norm_num)
theorem B4160285 : Blo 1847625 4160285 := bbase (se 3 (by rfl) ⟨780053, by rfl⟩ : syracuseStep 4160285 = 1560107) (by norm_num)
theorem B3119917 : Blo 1847625 3119917 := bbase (se 3 (by rfl) ⟨584984, by rfl⟩ : syracuseStep 3119917 = 1169969) (by norm_num)
theorem B10533685 : Blo 1847625 10533685 := bbase (se 5 (by rfl) ⟨493766, by rfl⟩ : syracuseStep 10533685 = 987533) (by norm_num)
theorem B2079553 : Blo 1847625 2079553 := bbase (se 2 (by rfl) ⟨779832, by rfl⟩ : syracuseStep 2079553 = 1559665) (by norm_num)
theorem B9001813 : Blo 1847625 9001813 := bbase (se 9 (by rfl) ⟨26372, by rfl⟩ : syracuseStep 9001813 = 52745) (by norm_num)
theorem B2079589 : Blo 1847625 2079589 := bbase (se 4 (by rfl) ⟨194961, by rfl⟩ : syracuseStep 2079589 = 389923) (by norm_num)
theorem B4160357 : Blo 1847625 4160357 := bbase (se 4 (by rfl) ⟨390033, by rfl⟩ : syracuseStep 4160357 = 780067) (by norm_num)
theorem B3120005 : Blo 1847625 3120005 := bbase (se 4 (by rfl) ⟨292500, by rfl⟩ : syracuseStep 3120005 = 585001) (by norm_num)
theorem B6241157 : Blo 1847625 6241157 := bbase (se 4 (by rfl) ⟨585108, by rfl⟩ : syracuseStep 6241157 = 1170217) (by norm_num)
theorem B2079625 : Blo 1847625 2079625 := bbase (se 2 (by rfl) ⟨779859, by rfl⟩ : syracuseStep 2079625 = 1559719) (by norm_num)
theorem B2079661 : Blo 1847625 2079661 := bbase (se 3 (by rfl) ⟨389936, by rfl⟩ : syracuseStep 2079661 = 779873) (by norm_num)
theorem B4160429 : Blo 1847625 4160429 := bbase (se 3 (by rfl) ⟨780080, by rfl⟩ : syracuseStep 4160429 = 1560161) (by norm_num)
theorem B2079697 : Blo 1847625 2079697 := bbase (se 2 (by rfl) ⟨779886, by rfl⟩ : syracuseStep 2079697 = 1559773) (by norm_num)
theorem B3947501 : Blo 1847625 3947501 := bbase (se 3 (by rfl) ⟨740156, by rfl⟩ : syracuseStep 3947501 = 1480313) (by norm_num)
theorem B2079733 : Blo 1847625 2079733 := bbase (se 5 (by rfl) ⟨97487, by rfl⟩ : syracuseStep 2079733 = 194975) (by norm_num)
theorem B14040053 : Blo 1847625 14040053 := bbase (se 5 (by rfl) ⟨658127, by rfl⟩ : syracuseStep 14040053 = 1316255) (by norm_num)
theorem B4160501 : Blo 1847625 4160501 := bbase (se 5 (by rfl) ⟨195023, by rfl⟩ : syracuseStep 4160501 = 390047) (by norm_num)
theorem B3120133 : Blo 1847625 3120133 := bbase (se 4 (by rfl) ⟨292512, by rfl⟩ : syracuseStep 3120133 = 585025) (by norm_num)
theorem B4217869 : Blo 1847625 4217869 := bbase (se 3 (by rfl) ⟨790850, by rfl⟩ : syracuseStep 4217869 = 1581701) (by norm_num)
theorem B14998549 : Blo 1847625 14998549 := bbase (se 6 (by rfl) ⟨351528, by rfl⟩ : syracuseStep 14998549 = 703057) (by norm_num)
theorem B2079769 : Blo 1847625 2079769 := bbase (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) (by norm_num)
theorem B2079805 : Blo 1847625 2079805 := bbase (se 3 (by rfl) ⟨389963, by rfl⟩ : syracuseStep 2079805 = 779927) (by norm_num)
theorem B4160573 : Blo 1847625 4160573 := bbase (se 3 (by rfl) ⟨780107, by rfl⟩ : syracuseStep 4160573 = 1560215) (by norm_num)
theorem B7896149 : Blo 1847625 7896149 := bbase (se 8 (by rfl) ⟨46266, by rfl⟩ : syracuseStep 7896149 = 92533) (by norm_num)
theorem B3120221 : Blo 1847625 3120221 := bbase (se 3 (by rfl) ⟨585041, by rfl⟩ : syracuseStep 3120221 = 1170083) (by norm_num)
theorem B2079841 : Blo 1847625 2079841 := bbase (se 2 (by rfl) ⟨779940, by rfl⟩ : syracuseStep 2079841 = 1559881) (by norm_num)
theorem B2079877 : Blo 1847625 2079877 := bbase (se 4 (by rfl) ⟨194988, by rfl⟩ : syracuseStep 2079877 = 389977) (by norm_num)
theorem B4160645 : Blo 1847625 4160645 := bbase (se 4 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 4160645 = 780121) (by norm_num)
theorem B2079913 : Blo 1847625 2079913 := bbase (se 2 (by rfl) ⟨779967, by rfl⟩ : syracuseStep 2079913 = 1559935) (by norm_num)
theorem B2079949 : Blo 1847625 2079949 := bbase (se 3 (by rfl) ⟨389990, by rfl⟩ : syracuseStep 2079949 = 779981) (by norm_num)
theorem B4160717 : Blo 1847625 4160717 := bbase (se 3 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 4160717 = 1560269) (by norm_num)
theorem B3120349 : Blo 1847625 3120349 := bbase (se 3 (by rfl) ⟨585065, by rfl⟩ : syracuseStep 3120349 = 1170131) (by norm_num)
theorem B2079985 : Blo 1847625 2079985 := bbase (se 2 (by rfl) ⟨779994, by rfl⟩ : syracuseStep 2079985 = 1559989) (by norm_num)
theorem B8428805 : Blo 1847625 8428805 := bbase (se 4 (by rfl) ⟨790200, by rfl⟩ : syracuseStep 8428805 = 1580401) (by norm_num)
theorem B8879381 : Blo 1847625 8879381 := bbase (se 6 (by rfl) ⟨208110, by rfl⟩ : syracuseStep 8879381 = 416221) (by norm_num)
theorem B2080021 : Blo 1847625 2080021 := bbase (se 6 (by rfl) ⟨48750, by rfl⟩ : syracuseStep 2080021 = 97501) (by norm_num)
theorem B4160789 : Blo 1847625 4160789 := bbase (se 6 (by rfl) ⟨97518, by rfl⟩ : syracuseStep 4160789 = 195037) (by norm_num)
theorem B3120437 : Blo 1847625 3120437 := bbase (se 5 (by rfl) ⟨146270, by rfl⟩ : syracuseStep 3120437 = 292541) (by norm_num)
theorem B6241589 : Blo 1847625 6241589 := bbase (se 5 (by rfl) ⟨292574, by rfl⟩ : syracuseStep 6241589 = 585149) (by norm_num)
theorem B5266741 : Blo 1847625 5266741 := bbase (se 5 (by rfl) ⟨246878, by rfl⟩ : syracuseStep 5266741 = 493757) (by norm_num)
theorem B2080057 : Blo 1847625 2080057 := bbase (se 2 (by rfl) ⟨780021, by rfl⟩ : syracuseStep 2080057 = 1560043) (by norm_num)
theorem B1973593 : Blo 1847625 1973593 := bbase (se 2 (by rfl) ⟨740097, by rfl⟩ : syracuseStep 1973593 = 1480195) (by norm_num)
theorem B3947869 : Blo 1847625 3947869 := bbase (se 3 (by rfl) ⟨740225, by rfl⟩ : syracuseStep 3947869 = 1480451) (by norm_num)
theorem B2080093 : Blo 1847625 2080093 := bbase (se 3 (by rfl) ⟨390017, by rfl⟩ : syracuseStep 2080093 = 780035) (by norm_num)
theorem B4160861 : Blo 1847625 4160861 := bbase (se 3 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 4160861 = 1560323) (by norm_num)
theorem B9362789 : Blo 1847625 9362789 := bbase (se 4 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 9362789 = 1755523) (by norm_num)
theorem B7896437 : Blo 1847625 7896437 := bbase (se 5 (by rfl) ⟨370145, by rfl⟩ : syracuseStep 7896437 = 740291) (by norm_num)
theorem B2080129 : Blo 1847625 2080129 := bbase (se 2 (by rfl) ⟨780048, by rfl⟩ : syracuseStep 2080129 = 1560097) (by norm_num)
theorem B14032277 : Blo 1847625 14032277 := bbase (se 6 (by rfl) ⟨328881, by rfl⟩ : syracuseStep 14032277 = 657763) (by norm_num)
theorem B1973665 : Blo 1847625 1973665 := bbase (se 2 (by rfl) ⟨740124, by rfl⟩ : syracuseStep 1973665 = 1480249) (by norm_num)
theorem B2080165 : Blo 1847625 2080165 := bbase (se 4 (by rfl) ⟨195015, by rfl⟩ : syracuseStep 2080165 = 390031) (by norm_num)
theorem B4160933 : Blo 1847625 4160933 := bbase (se 4 (by rfl) ⟨390087, by rfl⟩ : syracuseStep 4160933 = 780175) (by norm_num)
theorem B3120565 : Blo 1847625 3120565 := bbase (se 5 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 3120565 = 292553) (by norm_num)
theorem B4677061 : Blo 1847625 4677061 := bbase (se 4 (by rfl) ⟨438474, by rfl⟩ : syracuseStep 4677061 = 876949) (by norm_num)
theorem B2080201 : Blo 1847625 2080201 := bbase (se 2 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 2080201 = 1560151) (by norm_num)
theorem B2080237 : Blo 1847625 2080237 := bbase (se 3 (by rfl) ⟨390044, by rfl⟩ : syracuseStep 2080237 = 780089) (by norm_num)
theorem B4161005 : Blo 1847625 4161005 := bbase (se 3 (by rfl) ⟨780188, by rfl⟩ : syracuseStep 4161005 = 1560377) (by norm_num)
theorem B3120653 : Blo 1847625 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B2080273 : Blo 1847625 2080273 := bbase (se 2 (by rfl) ⟨780102, by rfl⟩ : syracuseStep 2080273 = 1560205) (by norm_num)
theorem B4677173 : Blo 1847625 4677173 := bbase (se 5 (by rfl) ⟨219242, by rfl⟩ : syracuseStep 4677173 = 438485) (by norm_num)
theorem B2080309 : Blo 1847625 2080309 := bbase (se 5 (by rfl) ⟨97514, by rfl⟩ : syracuseStep 2080309 = 195029) (by norm_num)
theorem B4161077 : Blo 1847625 4161077 := bbase (se 5 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 4161077 = 390101) (by norm_num)
theorem B8887877 : Blo 1847625 8887877 := bbase (se 4 (by rfl) ⟨833238, by rfl⟩ : syracuseStep 8887877 = 1666477) (by norm_num)
theorem B1973845 : Blo 1847625 1973845 := bbase (se 8 (by rfl) ⟨11565, by rfl⟩ : syracuseStep 1973845 = 23131) (by norm_num)
theorem B2080345 : Blo 1847625 2080345 := bbase (se 2 (by rfl) ⟨780129, by rfl⟩ : syracuseStep 2080345 = 1560259) (by norm_num)
theorem B2080381 : Blo 1847625 2080381 := bbase (se 3 (by rfl) ⟨390071, by rfl⟩ : syracuseStep 2080381 = 780143) (by norm_num)
theorem B4161149 : Blo 1847625 4161149 := bbase (se 3 (by rfl) ⟨780215, by rfl⟩ : syracuseStep 4161149 = 1560431) (by norm_num)
theorem B3120781 : Blo 1847625 3120781 := bbase (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) (by norm_num)
theorem B2080417 : Blo 1847625 2080417 := bbase (se 2 (by rfl) ⟨780156, by rfl⟩ : syracuseStep 2080417 = 1560313) (by norm_num)
theorem B2080453 : Blo 1847625 2080453 := bbase (se 4 (by rfl) ⟨195042, by rfl⟩ : syracuseStep 2080453 = 390085) (by norm_num)
theorem B4161221 : Blo 1847625 4161221 := bbase (se 4 (by rfl) ⟨390114, by rfl⟩ : syracuseStep 4161221 = 780229) (by norm_num)
theorem B5922533 : Blo 1847625 5922533 := bbase (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) (by norm_num)
theorem B3120869 : Blo 1847625 3120869 := bbase (se 4 (by rfl) ⟨292581, by rfl⟩ : syracuseStep 3120869 = 585163) (by norm_num)
theorem B6242021 : Blo 1847625 6242021 := bbase (se 4 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 6242021 = 1170379) (by norm_num)
theorem B2080489 : Blo 1847625 2080489 := bbase (se 2 (by rfl) ⟨780183, by rfl⟩ : syracuseStep 2080489 = 1560367) (by norm_num)
theorem B4562669 : Blo 1847625 4562669 := bbase (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) (by norm_num)
theorem B4677365 : Blo 1847625 4677365 := bbase (se 5 (by rfl) ⟨219251, by rfl⟩ : syracuseStep 4677365 = 438503) (by norm_num)
theorem B9355013 : Blo 1847625 9355013 := bbase (se 4 (by rfl) ⟨877032, by rfl⟩ : syracuseStep 9355013 = 1754065) (by norm_num)
theorem B2080525 : Blo 1847625 2080525 := bbase (se 3 (by rfl) ⟨390098, by rfl⟩ : syracuseStep 2080525 = 780197) (by norm_num)
theorem B4161293 : Blo 1847625 4161293 := bbase (se 3 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 4161293 = 1560485) (by norm_num)
theorem B2080561 : Blo 1847625 2080561 := bbase (se 2 (by rfl) ⟨780210, by rfl⟩ : syracuseStep 2080561 = 1560421) (by norm_num)
theorem B2809669 : Blo 1847625 2809669 := bbase (se 4 (by rfl) ⟨263406, by rfl⟩ : syracuseStep 2809669 = 526813) (by norm_num)
theorem B2080597 : Blo 1847625 2080597 := bbase (se 9 (by rfl) ⟨6095, by rfl⟩ : syracuseStep 2080597 = 12191) (by norm_num)
theorem B4161365 : Blo 1847625 4161365 := bbase (se 9 (by rfl) ⟨12191, by rfl⟩ : syracuseStep 4161365 = 24383) (by norm_num)
theorem B3120997 : Blo 1847625 3120997 := bbase (se 4 (by rfl) ⟨292593, by rfl⟩ : syracuseStep 3120997 = 585187) (by norm_num)
theorem B2080633 : Blo 1847625 2080633 := bbase (se 2 (by rfl) ⟨780237, by rfl⟩ : syracuseStep 2080633 = 1560475) (by norm_num)
theorem B2080669 : Blo 1847625 2080669 := bbase (se 3 (by rfl) ⟨390125, by rfl⟩ : syracuseStep 2080669 = 780251) (by norm_num)
theorem B4161437 : Blo 1847625 4161437 := bbase (se 3 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 4161437 = 1560539) (by norm_num)
theorem B3121085 : Blo 1847625 3121085 := bbase (se 3 (by rfl) ⟨585203, by rfl⟩ : syracuseStep 3121085 = 1170407) (by norm_num)
theorem B2080705 : Blo 1847625 2080705 := bbase (se 2 (by rfl) ⟨780264, by rfl⟩ : syracuseStep 2080705 = 1560529) (by norm_num)
theorem B19980245 : Blo 1847625 19980245 := bbase (se 7 (by rfl) ⟨234143, by rfl⟩ : syracuseStep 19980245 = 468287) (by norm_num)
theorem B2080741 : Blo 1847625 2080741 := bbase (se 4 (by rfl) ⟨195069, by rfl⟩ : syracuseStep 2080741 = 390139) (by norm_num)
theorem B4161509 : Blo 1847625 4161509 := bbase (se 4 (by rfl) ⟨390141, by rfl⟩ : syracuseStep 4161509 = 780283) (by norm_num)
theorem B4161617 : Blo 1847625 4161617 := bstep (se 2 (by rfl) ⟨1560606, by rfl⟩ : syracuseStep 4161617 = 3121213) B3121213
theorem B4161635 : Blo 1847625 4161635 := bstep (se 1 (by rfl) ⟨3121226, by rfl⟩ : syracuseStep 4161635 = 6242453) B6242453
theorem B1925251 : Blo 1847625 1925251 := bstep (se 1 (by rfl) ⟨1443938, by rfl⟩ : syracuseStep 1925251 = 2887877) B2887877
theorem B3948689 : Blo 1847625 3948689 := bstep (se 2 (by rfl) ⟨1480758, by rfl⟩ : syracuseStep 3948689 = 2961517) B2961517
theorem B4440305 : Blo 1847625 4440305 := bstep (se 2 (by rfl) ⟨1665114, by rfl⟩ : syracuseStep 4440305 = 3330229) B3330229
theorem B7020877 : Blo 1847625 7020877 := bstep (se 3 (by rfl) ⟨1316414, by rfl⟩ : syracuseStep 7020877 = 2632829) B2632829
theorem B2810209 : Blo 1847625 2810209 := bstep (se 2 (by rfl) ⟨1053828, by rfl⟩ : syracuseStep 2810209 = 2107657) B2107657
theorem B9355661 : Blo 1847625 9355661 := bstep (se 3 (by rfl) ⟨1754186, by rfl⟩ : syracuseStep 9355661 = 3508373) B3508373
theorem B4678033 : Blo 1847625 4678033 := bstep (se 2 (by rfl) ⟨1754262, by rfl⟩ : syracuseStep 4678033 = 3508525) B3508525
theorem B5923277 : Blo 1847625 5923277 := bstep (se 3 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 5923277 = 2221229) B2221229
theorem B16007651 : Blo 1847625 16007651 := bstep (se 1 (by rfl) ⟨12005738, by rfl⟩ : syracuseStep 16007651 = 24011477) B24011477
theorem B2220547 : Blo 1847625 2220547 := bstep (se 1 (by rfl) ⟨1665410, by rfl⟩ : syracuseStep 2220547 = 3330821) B3330821
theorem B2810465 : Blo 1847625 2810465 := bstep (se 2 (by rfl) ⟨1053924, by rfl⟩ : syracuseStep 2810465 = 2107849) B2107849
theorem B2220691 : Blo 1847625 2220691 := bstep (se 1 (by rfl) ⟨1665518, by rfl⟩ : syracuseStep 2220691 = 3331037) B3331037
theorem B4678307 : Blo 1847625 4678307 := bstep (se 1 (by rfl) ⟨3508730, by rfl⟩ : syracuseStep 4678307 = 7017461) B7017461
theorem B9003683 : Blo 1847625 9003683 := bstep (se 1 (by rfl) ⟨6752762, by rfl⟩ : syracuseStep 9003683 = 13505525) B13505525
theorem B6324941 : Blo 1847625 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B9003761 : Blo 1847625 9003761 := bstep (se 2 (by rfl) ⟨3376410, by rfl⟩ : syracuseStep 9003761 = 6752821) B6752821
theorem B50586389 : Blo 1847625 50586389 := bstep (se 6 (by rfl) ⟨1185618, by rfl⟩ : syracuseStep 50586389 = 2371237) B2371237
theorem B4678499 : Blo 1847625 4678499 := bstep (se 1 (by rfl) ⟨3508874, by rfl⟩ : syracuseStep 4678499 = 7017749) B7017749
theorem B14041997 : Blo 1847625 14041997 := bstep (se 3 (by rfl) ⟨2632874, by rfl⟩ : syracuseStep 14041997 = 5265749) B5265749
theorem B8881073 : Blo 1847625 8881073 := bstep (se 2 (by rfl) ⟨3330402, by rfl⟩ : syracuseStep 8881073 = 6660805) B6660805
theorem B7898147 : Blo 1847625 7898147 := bstep (se 1 (by rfl) ⟨5923610, by rfl⟩ : syracuseStep 7898147 = 11847221) B11847221
theorem B7021667 : Blo 1847625 7021667 := bstep (se 1 (by rfl) ⟨5266250, by rfl⟩ : syracuseStep 7021667 = 10532501) B10532501
theorem B12002417 : Blo 1847625 12002417 := bstep (se 2 (by rfl) ⟨4500906, by rfl⟩ : syracuseStep 12002417 = 9001813) B9001813
theorem B2630819 : Blo 1847625 2630819 := bstep (se 1 (by rfl) ⟨1973114, by rfl⟩ : syracuseStep 2630819 = 3946229) B3946229
theorem B3949859 : Blo 1847625 3949859 := bstep (se 1 (by rfl) ⟨2962394, by rfl⟩ : syracuseStep 3949859 = 5924789) B5924789
theorem B3851569 : Blo 1847625 3851569 := bstep (se 2 (by rfl) ⟨1444338, by rfl⟩ : syracuseStep 3851569 = 2888677) B2888677
theorem B5924173 : Blo 1847625 5924173 := bstep (se 3 (by rfl) ⟨1110782, by rfl⟩ : syracuseStep 5924173 = 2221565) B2221565
theorem B19998065 : Blo 1847625 19998065 := bstep (se 2 (by rfl) ⟨7499274, by rfl⟩ : syracuseStep 19998065 = 14998549) B14998549
theorem B6407629 : Blo 1847625 6407629 := bstep (se 3 (by rfl) ⟨1201430, by rfl⟩ : syracuseStep 6407629 = 2402861) B2402861
theorem B6235757 : Blo 1847625 6235757 := bstep (se 3 (by rfl) ⟨1169204, by rfl⟩ : syracuseStep 6235757 = 2338409) B2338409
theorem B3507857 : Blo 1847625 3507857 := bstep (se 2 (by rfl) ⟨1315446, by rfl⟩ : syracuseStep 3507857 = 2630893) B2630893
theorem B2221715 : Blo 1847625 2221715 := bstep (se 1 (by rfl) ⟨1666286, by rfl⟩ : syracuseStep 2221715 = 3332573) B3332573
theorem B6235811 : Blo 1847625 6235811 := bstep (se 1 (by rfl) ⟨4676858, by rfl⟩ : syracuseStep 6235811 = 9353717) B9353717
theorem B7022321 : Blo 1847625 7022321 := bstep (se 2 (by rfl) ⟨2633370, by rfl⟩ : syracuseStep 7022321 = 5266741) B5266741
theorem B4679441 : Blo 1847625 4679441 := bstep (se 2 (by rfl) ⟨1754790, by rfl⟩ : syracuseStep 4679441 = 3509581) B3509581
theorem B2631457 : Blo 1847625 2631457 := bstep (se 2 (by rfl) ⟨986796, by rfl⟩ : syracuseStep 2631457 = 1973593) B1973593
theorem B4679491 : Blo 1847625 4679491 := bstep (se 1 (by rfl) ⟨3509618, by rfl⟩ : syracuseStep 4679491 = 7019237) B7019237
theorem B17336177 : Blo 1847625 17336177 := bstep (se 2 (by rfl) ⟨6501066, by rfl⟩ : syracuseStep 17336177 = 13002133) B13002133
theorem B6236081 : Blo 1847625 6236081 := bstep (se 2 (by rfl) ⟨2338530, by rfl⟩ : syracuseStep 6236081 = 4677061) B4677061
theorem B12167117 : Blo 1847625 12167117 := bstep (se 3 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 12167117 = 4562669) B4562669
theorem B4679633 : Blo 1847625 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B4999171 : Blo 1847625 4999171 := bstep (se 1 (by rfl) ⟨3749378, by rfl⟩ : syracuseStep 4999171 = 7498757) B7498757
theorem B7112717 : Blo 1847625 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B6408227 : Blo 1847625 6408227 := bstep (se 1 (by rfl) ⟨4806170, by rfl⟩ : syracuseStep 6408227 = 9612341) B9612341
theorem B23693411 : Blo 1847625 23693411 := bstep (se 1 (by rfl) ⟨17770058, by rfl⟩ : syracuseStep 23693411 = 35540117) B35540117
theorem B2631793 : Blo 1847625 2631793 := bstep (se 2 (by rfl) ⟨986922, by rfl⟩ : syracuseStep 2631793 = 1973845) B1973845
theorem B5925251 : Blo 1847625 5925251 := bstep (se 1 (by rfl) ⟨4443938, by rfl⟩ : syracuseStep 5925251 = 8887877) B8887877
theorem B100059533 : Blo 1847625 100059533 := bstep (se 3 (by rfl) ⟨18761162, by rfl⟩ : syracuseStep 100059533 = 37522325) B37522325
theorem B3746225 : Blo 1847625 3746225 := bstep (se 2 (by rfl) ⟨1404834, by rfl⟩ : syracuseStep 3746225 = 2809669) B2809669
theorem B6236621 : Blo 1847625 6236621 := bstep (se 3 (by rfl) ⟨1169366, by rfl⟩ : syracuseStep 6236621 = 2338733) B2338733
theorem B2771441 : Blo 1847625 2771441 := bstep (se 2 (by rfl) ⟨1039290, by rfl⟩ : syracuseStep 2771441 = 2078581) B2078581
theorem B2771459 : Blo 1847625 2771459 := bstep (se 1 (by rfl) ⟨2078594, by rfl⟩ : syracuseStep 2771459 = 4157189) B4157189
theorem B6236675 : Blo 1847625 6236675 := bstep (se 1 (by rfl) ⟨4677506, by rfl⟩ : syracuseStep 6236675 = 9355013) B9355013
theorem B3508753 : Blo 1847625 3508753 := bstep (se 2 (by rfl) ⟨1315782, by rfl⟩ : syracuseStep 3508753 = 2631565) B2631565
theorem B2771489 : Blo 1847625 2771489 := bstep (se 2 (by rfl) ⟨1039308, by rfl⟩ : syracuseStep 2771489 = 2078617) B2078617
theorem B8882723 : Blo 1847625 8882723 := bstep (se 1 (by rfl) ⟨6662042, by rfl⟩ : syracuseStep 8882723 = 13324085) B13324085
theorem B5622317 : Blo 1847625 5622317 := bstep (se 3 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 5622317 = 2108369) B2108369
theorem B2771507 : Blo 1847625 2771507 := bstep (se 1 (by rfl) ⟨2078630, by rfl⟩ : syracuseStep 2771507 = 4157261) B4157261
theorem B2771537 : Blo 1847625 2771537 := bstep (se 2 (by rfl) ⟨1039326, by rfl⟩ : syracuseStep 2771537 = 2078653) B2078653
theorem B2771555 : Blo 1847625 2771555 := bstep (se 1 (by rfl) ⟨2078666, by rfl⟩ : syracuseStep 2771555 = 4157333) B4157333
theorem B2771585 : Blo 1847625 2771585 := bstep (se 2 (by rfl) ⟨1039344, by rfl⟩ : syracuseStep 2771585 = 2078689) B2078689
theorem B2771603 : Blo 1847625 2771603 := bstep (se 1 (by rfl) ⟨2078702, by rfl⟩ : syracuseStep 2771603 = 4157405) B4157405
theorem B2771633 : Blo 1847625 2771633 := bstep (se 2 (by rfl) ⟨1039362, by rfl⟩ : syracuseStep 2771633 = 2078725) B2078725
theorem B3508913 : Blo 1847625 3508913 := bstep (se 2 (by rfl) ⟨1315842, by rfl⟩ : syracuseStep 3508913 = 2631685) B2631685
theorem B2632385 : Blo 1847625 2632385 := bstep (se 2 (by rfl) ⟨987144, by rfl⟩ : syracuseStep 2632385 = 1974289) B1974289
theorem B2771651 : Blo 1847625 2771651 := bstep (se 1 (by rfl) ⟨2078738, by rfl⟩ : syracuseStep 2771651 = 4157477) B4157477
theorem B2771681 : Blo 1847625 2771681 := bstep (se 2 (by rfl) ⟨1039380, by rfl⟩ : syracuseStep 2771681 = 2078761) B2078761
theorem B22498019 : Blo 1847625 22498019 := bstep (se 1 (by rfl) ⟨16873514, by rfl⟩ : syracuseStep 22498019 = 33747029) B33747029
theorem B7899889 : Blo 1847625 7899889 := bstep (se 2 (by rfl) ⟨2962458, by rfl⟩ : syracuseStep 7899889 = 5924917) B5924917
theorem B2771699 : Blo 1847625 2771699 := bstep (se 1 (by rfl) ⟨2078774, by rfl⟩ : syracuseStep 2771699 = 4157549) B4157549
theorem B2771729 : Blo 1847625 2771729 := bstep (se 2 (by rfl) ⟨1039398, by rfl⟩ : syracuseStep 2771729 = 2078797) B2078797
theorem B6236945 : Blo 1847625 6236945 := bstep (se 2 (by rfl) ⟨2338854, by rfl⟩ : syracuseStep 6236945 = 4677709) B4677709
theorem B2771747 : Blo 1847625 2771747 := bstep (se 1 (by rfl) ⟨2078810, by rfl⟩ : syracuseStep 2771747 = 4157621) B4157621
theorem B9988913 : Blo 1847625 9988913 := bstep (se 2 (by rfl) ⟨3745842, by rfl⟩ : syracuseStep 9988913 = 7491685) B7491685
theorem B10529585 : Blo 1847625 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B2771777 : Blo 1847625 2771777 := bstep (se 2 (by rfl) ⟨1039416, by rfl⟩ : syracuseStep 2771777 = 2078833) B2078833
theorem B2771795 : Blo 1847625 2771795 := bstep (se 1 (by rfl) ⟨2078846, by rfl⟩ : syracuseStep 2771795 = 4157693) B4157693
theorem B2771825 : Blo 1847625 2771825 := bstep (se 2 (by rfl) ⟨1039434, by rfl⟩ : syracuseStep 2771825 = 2078869) B2078869
theorem B2771843 : Blo 1847625 2771843 := bstep (se 1 (by rfl) ⟨2078882, by rfl⟩ : syracuseStep 2771843 = 4157765) B4157765
theorem B2771873 : Blo 1847625 2771873 := bstep (se 2 (by rfl) ⟨1039452, by rfl⟩ : syracuseStep 2771873 = 2078905) B2078905
theorem B4680625 : Blo 1847625 4680625 := bstep (se 2 (by rfl) ⟨1755234, by rfl⟩ : syracuseStep 4680625 = 3510469) B3510469
theorem B2771891 : Blo 1847625 2771891 := bstep (se 1 (by rfl) ⟨2078918, by rfl⟩ : syracuseStep 2771891 = 4157837) B4157837
theorem B2771921 : Blo 1847625 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B2771939 : Blo 1847625 2771939 := bstep (se 1 (by rfl) ⟨2078954, by rfl⟩ : syracuseStep 2771939 = 4157909) B4157909
theorem B2771969 : Blo 1847625 2771969 := bstep (se 2 (by rfl) ⟨1039488, by rfl⟩ : syracuseStep 2771969 = 2078977) B2078977
theorem B2771987 : Blo 1847625 2771987 := bstep (se 1 (by rfl) ⟨2078990, by rfl⟩ : syracuseStep 2771987 = 4157981) B4157981
theorem B2772017 : Blo 1847625 2772017 := bstep (se 2 (by rfl) ⟨1039506, by rfl⟩ : syracuseStep 2772017 = 2079013) B2079013
theorem B2772035 : Blo 1847625 2772035 := bstep (se 1 (by rfl) ⟨2079026, by rfl⟩ : syracuseStep 2772035 = 4158053) B4158053
theorem B3509315 : Blo 1847625 3509315 := bstep (se 1 (by rfl) ⟨2631986, by rfl⟩ : syracuseStep 3509315 = 5263973) B5263973
theorem B2772065 : Blo 1847625 2772065 := bstep (se 2 (by rfl) ⟨1039524, by rfl⟩ : syracuseStep 2772065 = 2079049) B2079049
theorem B2772083 : Blo 1847625 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B2772113 : Blo 1847625 2772113 := bstep (se 2 (by rfl) ⟨1039542, by rfl⟩ : syracuseStep 2772113 = 2079085) B2079085
theorem B2772131 : Blo 1847625 2772131 := bstep (se 1 (by rfl) ⟨2079098, by rfl⟩ : syracuseStep 2772131 = 4158197) B4158197
theorem B2772161 : Blo 1847625 2772161 := bstep (se 2 (by rfl) ⟨1039560, by rfl⟩ : syracuseStep 2772161 = 2079121) B2079121
theorem B4680899 : Blo 1847625 4680899 := bstep (se 1 (by rfl) ⟨3510674, by rfl⟩ : syracuseStep 4680899 = 7021349) B7021349
theorem B14036165 : Blo 1847625 14036165 := bstep (se 4 (by rfl) ⟨1315890, by rfl⟩ : syracuseStep 14036165 = 2631781) B2631781
theorem B2772179 : Blo 1847625 2772179 := bstep (se 1 (by rfl) ⟨2079134, by rfl⟩ : syracuseStep 2772179 = 4158269) B4158269
theorem B2632915 : Blo 1847625 2632915 := bstep (se 1 (by rfl) ⟨1974686, by rfl⟩ : syracuseStep 2632915 = 3949373) B3949373
theorem B2772209 : Blo 1847625 2772209 := bstep (se 2 (by rfl) ⟨1039578, by rfl⟩ : syracuseStep 2772209 = 2079157) B2079157
theorem B9358577 : Blo 1847625 9358577 := bstep (se 2 (by rfl) ⟨3509466, by rfl⟩ : syracuseStep 9358577 = 7018933) B7018933
theorem B2772227 : Blo 1847625 2772227 := bstep (se 1 (by rfl) ⟨2079170, by rfl⟩ : syracuseStep 2772227 = 4158341) B4158341
theorem B2772257 : Blo 1847625 2772257 := bstep (se 2 (by rfl) ⟨1039596, by rfl⟩ : syracuseStep 2772257 = 2079193) B2079193
theorem B6237485 : Blo 1847625 6237485 := bstep (se 3 (by rfl) ⟨1169528, by rfl⟩ : syracuseStep 6237485 = 2339057) B2339057
theorem B5262641 : Blo 1847625 5262641 := bstep (se 2 (by rfl) ⟨1973490, by rfl⟩ : syracuseStep 5262641 = 3946981) B3946981
theorem B2772275 : Blo 1847625 2772275 := bstep (se 1 (by rfl) ⟨2079206, by rfl⟩ : syracuseStep 2772275 = 4158413) B4158413
theorem B8883533 : Blo 1847625 8883533 := bstep (se 3 (by rfl) ⟨1665662, by rfl⟩ : syracuseStep 8883533 = 3331325) B3331325
theorem B2772305 : Blo 1847625 2772305 := bstep (se 2 (by rfl) ⟨1039614, by rfl⟩ : syracuseStep 2772305 = 2079229) B2079229
theorem B6237539 : Blo 1847625 6237539 := bstep (se 1 (by rfl) ⟨4678154, by rfl⟩ : syracuseStep 6237539 = 9356309) B9356309
theorem B2772323 : Blo 1847625 2772323 := bstep (se 1 (by rfl) ⟨2079242, by rfl⟩ : syracuseStep 2772323 = 4158485) B4158485
theorem B2772353 : Blo 1847625 2772353 := bstep (se 2 (by rfl) ⟨1039632, by rfl⟩ : syracuseStep 2772353 = 2079265) B2079265
theorem B4681091 : Blo 1847625 4681091 := bstep (se 1 (by rfl) ⟨3510818, by rfl⟩ : syracuseStep 4681091 = 7021637) B7021637
theorem B2772371 : Blo 1847625 2772371 := bstep (se 1 (by rfl) ⟨2079278, by rfl⟩ : syracuseStep 2772371 = 4158557) B4158557
theorem B2772401 : Blo 1847625 2772401 := bstep (se 2 (by rfl) ⟨1039650, by rfl⟩ : syracuseStep 2772401 = 2079301) B2079301
theorem B2772419 : Blo 1847625 2772419 := bstep (se 1 (by rfl) ⟨2079314, by rfl⟩ : syracuseStep 2772419 = 4158629) B4158629
theorem B7499213 : Blo 1847625 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B2772449 : Blo 1847625 2772449 := bstep (se 2 (by rfl) ⟨1039668, by rfl⟩ : syracuseStep 2772449 = 2079337) B2079337
theorem B5262833 : Blo 1847625 5262833 := bstep (se 2 (by rfl) ⟨1973562, by rfl⟩ : syracuseStep 5262833 = 3947125) B3947125
theorem B2772467 : Blo 1847625 2772467 := bstep (se 1 (by rfl) ⟨2079350, by rfl⟩ : syracuseStep 2772467 = 4158701) B4158701
theorem B2772497 : Blo 1847625 2772497 := bstep (se 2 (by rfl) ⟨1039686, by rfl⟩ : syracuseStep 2772497 = 2079373) B2079373
theorem B2772515 : Blo 1847625 2772515 := bstep (se 1 (by rfl) ⟨2079386, by rfl⟩ : syracuseStep 2772515 = 4158773) B4158773
theorem B2633251 : Blo 1847625 2633251 := bstep (se 1 (by rfl) ⟨1974938, by rfl⟩ : syracuseStep 2633251 = 3949877) B3949877
theorem B2772545 : Blo 1847625 2772545 := bstep (se 2 (by rfl) ⟨1039704, by rfl⟩ : syracuseStep 2772545 = 2079409) B2079409
theorem B5779021 : Blo 1847625 5779021 := bstep (se 3 (by rfl) ⟨1083566, by rfl⟩ : syracuseStep 5779021 = 2167133) B2167133
theorem B2772563 : Blo 1847625 2772563 := bstep (se 1 (by rfl) ⟨2079422, by rfl⟩ : syracuseStep 2772563 = 4158845) B4158845
theorem B6237809 : Blo 1847625 6237809 := bstep (se 2 (by rfl) ⟨2339178, by rfl⟩ : syracuseStep 6237809 = 4678357) B4678357
theorem B2772593 : Blo 1847625 2772593 := bstep (se 2 (by rfl) ⟨1039722, by rfl⟩ : syracuseStep 2772593 = 2079445) B2079445
theorem B2961011 : Blo 1847625 2961011 := bstep (se 1 (by rfl) ⟨2220758, by rfl⟩ : syracuseStep 2961011 = 4441517) B4441517
theorem B2772611 : Blo 1847625 2772611 := bstep (se 1 (by rfl) ⟨2079458, by rfl⟩ : syracuseStep 2772611 = 4158917) B4158917
theorem B2772641 : Blo 1847625 2772641 := bstep (se 2 (by rfl) ⟨1039740, by rfl⟩ : syracuseStep 2772641 = 2079481) B2079481
theorem B2772659 : Blo 1847625 2772659 := bstep (se 1 (by rfl) ⟨2079494, by rfl⟩ : syracuseStep 2772659 = 4158989) B4158989
theorem B2772689 : Blo 1847625 2772689 := bstep (se 2 (by rfl) ⟨1039758, by rfl⟩ : syracuseStep 2772689 = 2079517) B2079517
theorem B2772707 : Blo 1847625 2772707 := bstep (se 1 (by rfl) ⟨2079530, by rfl⟩ : syracuseStep 2772707 = 4159061) B4159061
theorem B14044913 : Blo 1847625 14044913 := bstep (se 2 (by rfl) ⟨5266842, by rfl⟩ : syracuseStep 14044913 = 10533685) B10533685
theorem B2961139 : Blo 1847625 2961139 := bstep (se 1 (by rfl) ⟨2220854, by rfl⟩ : syracuseStep 2961139 = 4441709) B4441709
theorem B2772737 : Blo 1847625 2772737 := bstep (se 2 (by rfl) ⟨1039776, by rfl⟩ : syracuseStep 2772737 = 2079553) B2079553
theorem B17100557 : Blo 1847625 17100557 := bstep (se 3 (by rfl) ⟨3206354, by rfl⟩ : syracuseStep 17100557 = 6412709) B6412709
theorem B2772755 : Blo 1847625 2772755 := bstep (se 1 (by rfl) ⟨2079566, by rfl⟩ : syracuseStep 2772755 = 4159133) B4159133
theorem B2772785 : Blo 1847625 2772785 := bstep (se 2 (by rfl) ⟨1039794, by rfl⟩ : syracuseStep 2772785 = 2079589) B2079589
theorem B2338627 : Blo 1847625 2338627 := bstep (se 1 (by rfl) ⟨1753970, by rfl⟩ : syracuseStep 2338627 = 3507941) B3507941
theorem B2772803 : Blo 1847625 2772803 := bstep (se 1 (by rfl) ⟨2079602, by rfl⟩ : syracuseStep 2772803 = 4159205) B4159205
theorem B2772833 : Blo 1847625 2772833 := bstep (se 2 (by rfl) ⟨1039812, by rfl⟩ : syracuseStep 2772833 = 2079625) B2079625
theorem B7016291 : Blo 1847625 7016291 := bstep (se 1 (by rfl) ⟨5262218, by rfl⟩ : syracuseStep 7016291 = 10524437) B10524437
theorem B4157297 : Blo 1847625 4157297 := bstep (se 2 (by rfl) ⟨1558986, by rfl⟩ : syracuseStep 4157297 = 3117973) B3117973
theorem B2772851 : Blo 1847625 2772851 := bstep (se 1 (by rfl) ⟨2079638, by rfl⟩ : syracuseStep 2772851 = 4159277) B4159277
theorem B4157315 : Blo 1847625 4157315 := bstep (se 1 (by rfl) ⟨3117986, by rfl⟩ : syracuseStep 4157315 = 6235973) B6235973
theorem B2772881 : Blo 1847625 2772881 := bstep (se 2 (by rfl) ⟨1039830, by rfl⟩ : syracuseStep 2772881 = 2079661) B2079661
theorem B2338723 : Blo 1847625 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B2772899 : Blo 1847625 2772899 := bstep (se 1 (by rfl) ⟨2079674, by rfl⟩ : syracuseStep 2772899 = 4159349) B4159349
theorem B2772929 : Blo 1847625 2772929 := bstep (se 2 (by rfl) ⟨1039848, by rfl⟩ : syracuseStep 2772929 = 2079697) B2079697
theorem B3510211 : Blo 1847625 3510211 := bstep (se 1 (by rfl) ⟨2632658, by rfl⟩ : syracuseStep 3510211 = 5265317) B5265317
theorem B2772947 : Blo 1847625 2772947 := bstep (se 1 (by rfl) ⟨2079710, by rfl⟩ : syracuseStep 2772947 = 4159421) B4159421
theorem B2772977 : Blo 1847625 2772977 := bstep (se 2 (by rfl) ⟨1039866, by rfl⟩ : syracuseStep 2772977 = 2079733) B2079733
theorem B2772995 : Blo 1847625 2772995 := bstep (se 1 (by rfl) ⟨2079746, by rfl⟩ : syracuseStep 2772995 = 4159493) B4159493
theorem B5623825 : Blo 1847625 5623825 := bstep (se 2 (by rfl) ⟨2108934, by rfl⟩ : syracuseStep 5623825 = 4217869) B4217869
theorem B2773025 : Blo 1847625 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B2773043 : Blo 1847625 2773043 := bstep (se 1 (by rfl) ⟨2079782, by rfl⟩ : syracuseStep 2773043 = 4159565) B4159565
theorem B15798341 : Blo 1847625 15798341 := bstep (se 4 (by rfl) ⟨1481094, by rfl⟩ : syracuseStep 15798341 = 2962189) B2962189
theorem B2773073 : Blo 1847625 2773073 := bstep (se 2 (by rfl) ⟨1039902, by rfl⟩ : syracuseStep 2773073 = 2079805) B2079805
theorem B2773091 : Blo 1847625 2773091 := bstep (se 1 (by rfl) ⟨2079818, by rfl⟩ : syracuseStep 2773091 = 4159637) B4159637
theorem B3510371 : Blo 1847625 3510371 := bstep (se 1 (by rfl) ⟨2632778, by rfl⟩ : syracuseStep 3510371 = 5265557) B5265557
theorem B2961523 : Blo 1847625 2961523 := bstep (se 1 (by rfl) ⟨2221142, by rfl⟩ : syracuseStep 2961523 = 4442285) B4442285
theorem B2773121 : Blo 1847625 2773121 := bstep (se 2 (by rfl) ⟨1039920, by rfl⟩ : syracuseStep 2773121 = 2079841) B2079841
theorem B6238349 : Blo 1847625 6238349 := bstep (se 3 (by rfl) ⟨1169690, by rfl⟩ : syracuseStep 6238349 = 2339381) B2339381
theorem B4157585 : Blo 1847625 4157585 := bstep (se 2 (by rfl) ⟨1559094, by rfl⟩ : syracuseStep 4157585 = 3118189) B3118189
theorem B2773139 : Blo 1847625 2773139 := bstep (se 1 (by rfl) ⟨2079854, by rfl⟩ : syracuseStep 2773139 = 4159709) B4159709
theorem B4157603 : Blo 1847625 4157603 := bstep (se 1 (by rfl) ⟨3118202, by rfl⟩ : syracuseStep 4157603 = 6236405) B6236405
theorem B2773169 : Blo 1847625 2773169 := bstep (se 2 (by rfl) ⟨1039938, by rfl⟩ : syracuseStep 2773169 = 2079877) B2079877
theorem B6238403 : Blo 1847625 6238403 := bstep (se 1 (by rfl) ⟨4678802, by rfl⟩ : syracuseStep 6238403 = 9357605) B9357605
theorem B2773187 : Blo 1847625 2773187 := bstep (se 1 (by rfl) ⟨2079890, by rfl⟩ : syracuseStep 2773187 = 4159781) B4159781
theorem B3748049 : Blo 1847625 3748049 := bstep (se 2 (by rfl) ⟨1405518, by rfl⟩ : syracuseStep 3748049 = 2811037) B2811037
theorem B2773217 : Blo 1847625 2773217 := bstep (se 2 (by rfl) ⟨1039956, by rfl⟩ : syracuseStep 2773217 = 2079913) B2079913
theorem B10531043 : Blo 1847625 10531043 := bstep (se 1 (by rfl) ⟨7898282, by rfl⟩ : syracuseStep 10531043 = 15796565) B15796565
theorem B2773235 : Blo 1847625 2773235 := bstep (se 1 (by rfl) ⟨2079926, by rfl⟩ : syracuseStep 2773235 = 4159853) B4159853
theorem B2773265 : Blo 1847625 2773265 := bstep (se 2 (by rfl) ⟨1039974, by rfl⟩ : syracuseStep 2773265 = 2079949) B2079949
theorem B2773283 : Blo 1847625 2773283 := bstep (se 1 (by rfl) ⟨2079962, by rfl⟩ : syracuseStep 2773283 = 4159925) B4159925
theorem B2773313 : Blo 1847625 2773313 := bstep (se 2 (by rfl) ⟨1039992, by rfl⟩ : syracuseStep 2773313 = 2079985) B2079985
theorem B9990469 : Blo 1847625 9990469 := bstep (se 4 (by rfl) ⟨936606, by rfl⟩ : syracuseStep 9990469 = 1873213) B1873213
theorem B1847635 : Blo 1847625 1847635 := bstep (se 1 (by rfl) ⟨1385726, by rfl⟩ : syracuseStep 1847635 = 2771453) B2771453
theorem B2773331 : Blo 1847625 2773331 := bstep (se 1 (by rfl) ⟨2079998, by rfl⟩ : syracuseStep 2773331 = 4159997) B4159997
theorem B1847651 : Blo 1847625 1847651 := bstep (se 1 (by rfl) ⟨1385738, by rfl⟩ : syracuseStep 1847651 = 2771477) B2771477
theorem B10522979 : Blo 1847625 10522979 := bstep (se 1 (by rfl) ⟨7892234, by rfl⟩ : syracuseStep 10522979 = 15784469) B15784469
theorem B2773361 : Blo 1847625 2773361 := bstep (se 2 (by rfl) ⟨1040010, by rfl⟩ : syracuseStep 2773361 = 2080021) B2080021
theorem B1847667 : Blo 1847625 1847667 := bstep (se 1 (by rfl) ⟨1385750, by rfl⟩ : syracuseStep 1847667 = 2771501) B2771501
theorem B2961779 : Blo 1847625 2961779 := bstep (se 1 (by rfl) ⟨2221334, by rfl⟩ : syracuseStep 2961779 = 4442669) B4442669
theorem B1847683 : Blo 1847625 1847683 := bstep (se 1 (by rfl) ⟨1385762, by rfl⟩ : syracuseStep 1847683 = 2771525) B2771525
theorem B2773379 : Blo 1847625 2773379 := bstep (se 1 (by rfl) ⟨2080034, by rfl⟩ : syracuseStep 2773379 = 4160069) B4160069
theorem B31584653 : Blo 1847625 31584653 := bstep (se 3 (by rfl) ⟨5922122, by rfl⟩ : syracuseStep 31584653 = 11844245) B11844245
theorem B1847699 : Blo 1847625 1847699 := bstep (se 1 (by rfl) ⟨1385774, by rfl⟩ : syracuseStep 1847699 = 2771549) B2771549
theorem B2339219 : Blo 1847625 2339219 := bstep (se 1 (by rfl) ⟨1754414, by rfl⟩ : syracuseStep 2339219 = 3508829) B3508829
theorem B2773409 : Blo 1847625 2773409 := bstep (se 2 (by rfl) ⟨1040028, by rfl⟩ : syracuseStep 2773409 = 2080057) B2080057
theorem B1847715 : Blo 1847625 1847715 := bstep (se 1 (by rfl) ⟨1385786, by rfl⟩ : syracuseStep 1847715 = 2771573) B2771573
theorem B4157873 : Blo 1847625 4157873 := bstep (se 2 (by rfl) ⟨1559202, by rfl⟩ : syracuseStep 4157873 = 3118405) B3118405
theorem B1847731 : Blo 1847625 1847731 := bstep (se 1 (by rfl) ⟨1385798, by rfl⟩ : syracuseStep 1847731 = 2771597) B2771597
theorem B2773427 : Blo 1847625 2773427 := bstep (se 1 (by rfl) ⟨2080070, by rfl⟩ : syracuseStep 2773427 = 4160141) B4160141
theorem B1847747 : Blo 1847625 1847747 := bstep (se 1 (by rfl) ⟨1385810, by rfl⟩ : syracuseStep 1847747 = 2771621) B2771621
theorem B4157891 : Blo 1847625 4157891 := bstep (se 1 (by rfl) ⟨3118418, by rfl⟩ : syracuseStep 4157891 = 6236837) B6236837
theorem B5263825 : Blo 1847625 5263825 := bstep (se 2 (by rfl) ⟨1973934, by rfl⟩ : syracuseStep 5263825 = 3947869) B3947869
theorem B6238673 : Blo 1847625 6238673 := bstep (se 2 (by rfl) ⟨2339502, by rfl⟩ : syracuseStep 6238673 = 4679005) B4679005
theorem B1847763 : Blo 1847625 1847763 := bstep (se 1 (by rfl) ⟨1385822, by rfl⟩ : syracuseStep 1847763 = 2771645) B2771645
theorem B2773457 : Blo 1847625 2773457 := bstep (se 2 (by rfl) ⟨1040046, by rfl⟩ : syracuseStep 2773457 = 2080093) B2080093
theorem B1847779 : Blo 1847625 1847779 := bstep (se 1 (by rfl) ⟨1385834, by rfl⟩ : syracuseStep 1847779 = 2771669) B2771669
theorem B2773475 : Blo 1847625 2773475 := bstep (se 1 (by rfl) ⟨2080106, by rfl⟩ : syracuseStep 2773475 = 4160213) B4160213
theorem B1847795 : Blo 1847625 1847795 := bstep (se 1 (by rfl) ⟨1385846, by rfl⟩ : syracuseStep 1847795 = 2771693) B2771693
theorem B2773505 : Blo 1847625 2773505 := bstep (se 2 (by rfl) ⟨1040064, by rfl⟩ : syracuseStep 2773505 = 2080129) B2080129
theorem B1847811 : Blo 1847625 1847811 := bstep (se 1 (by rfl) ⟨1385858, by rfl⟩ : syracuseStep 1847811 = 2771717) B2771717
theorem B11850245 : Blo 1847625 11850245 := bstep (se 4 (by rfl) ⟨1110960, by rfl⟩ : syracuseStep 11850245 = 2221921) B2221921
theorem B1847827 : Blo 1847625 1847827 := bstep (se 1 (by rfl) ⟨1385870, by rfl⟩ : syracuseStep 1847827 = 2771741) B2771741
theorem B2773523 : Blo 1847625 2773523 := bstep (se 1 (by rfl) ⟨2080142, by rfl⟩ : syracuseStep 2773523 = 4160285) B4160285
theorem B1847843 : Blo 1847625 1847843 := bstep (se 1 (by rfl) ⟨1385882, by rfl⟩ : syracuseStep 1847843 = 2771765) B2771765
theorem B2773553 : Blo 1847625 2773553 := bstep (se 2 (by rfl) ⟨1040082, by rfl⟩ : syracuseStep 2773553 = 2080165) B2080165
theorem B1847859 : Blo 1847625 1847859 := bstep (se 1 (by rfl) ⟨1385894, by rfl⟩ : syracuseStep 1847859 = 2771789) B2771789
theorem B1847875 : Blo 1847625 1847875 := bstep (se 1 (by rfl) ⟨1385906, by rfl⟩ : syracuseStep 1847875 = 2771813) B2771813
theorem B2773571 : Blo 1847625 2773571 := bstep (se 1 (by rfl) ⟨2080178, by rfl⟩ : syracuseStep 2773571 = 4160357) B4160357
theorem B1847891 : Blo 1847625 1847891 := bstep (se 1 (by rfl) ⟨1385918, by rfl⟩ : syracuseStep 1847891 = 2771837) B2771837
theorem B2773601 : Blo 1847625 2773601 := bstep (se 2 (by rfl) ⟨1040100, by rfl⟩ : syracuseStep 2773601 = 2080201) B2080201
theorem B1847907 : Blo 1847625 1847907 := bstep (se 1 (by rfl) ⟨1385930, by rfl⟩ : syracuseStep 1847907 = 2771861) B2771861
theorem B7115377 : Blo 1847625 7115377 := bstep (se 2 (by rfl) ⟨2668266, by rfl⟩ : syracuseStep 7115377 = 5336533) B5336533
theorem B1847923 : Blo 1847625 1847923 := bstep (se 1 (by rfl) ⟨1385942, by rfl⟩ : syracuseStep 1847923 = 2771885) B2771885
theorem B2773619 : Blo 1847625 2773619 := bstep (se 1 (by rfl) ⟨2080214, by rfl⟩ : syracuseStep 2773619 = 4160429) B4160429
theorem B1847939 : Blo 1847625 1847939 := bstep (se 1 (by rfl) ⟨1385954, by rfl⟩ : syracuseStep 1847939 = 2771909) B2771909
theorem B2773649 : Blo 1847625 2773649 := bstep (se 2 (by rfl) ⟨1040118, by rfl⟩ : syracuseStep 2773649 = 2080237) B2080237
theorem B1847955 : Blo 1847625 1847955 := bstep (se 1 (by rfl) ⟨1385966, by rfl⟩ : syracuseStep 1847955 = 2771933) B2771933
theorem B1847971 : Blo 1847625 1847971 := bstep (se 1 (by rfl) ⟨1385978, by rfl⟩ : syracuseStep 1847971 = 2771957) B2771957
theorem B9360035 : Blo 1847625 9360035 := bstep (se 1 (by rfl) ⟨7020026, by rfl⟩ : syracuseStep 9360035 = 14040053) B14040053
theorem B2773667 : Blo 1847625 2773667 := bstep (se 1 (by rfl) ⟨2080250, by rfl⟩ : syracuseStep 2773667 = 4160501) B4160501
theorem B1847987 : Blo 1847625 1847987 := bstep (se 1 (by rfl) ⟨1385990, by rfl⟩ : syracuseStep 1847987 = 2771981) B2771981
theorem B2773697 : Blo 1847625 2773697 := bstep (se 2 (by rfl) ⟨1040136, by rfl⟩ : syracuseStep 2773697 = 2080273) B2080273
theorem B1848003 : Blo 1847625 1848003 := bstep (se 1 (by rfl) ⟨1386002, by rfl⟩ : syracuseStep 1848003 = 2772005) B2772005
theorem B4158161 : Blo 1847625 4158161 := bstep (se 2 (by rfl) ⟨1559310, by rfl⟩ : syracuseStep 4158161 = 3118621) B3118621
theorem B1848019 : Blo 1847625 1848019 := bstep (se 1 (by rfl) ⟨1386014, by rfl⟩ : syracuseStep 1848019 = 2772029) B2772029
theorem B2773715 : Blo 1847625 2773715 := bstep (se 1 (by rfl) ⟨2080286, by rfl⟩ : syracuseStep 2773715 = 4160573) B4160573
theorem B1848035 : Blo 1847625 1848035 := bstep (se 1 (by rfl) ⟨1386026, by rfl⟩ : syracuseStep 1848035 = 2772053) B2772053
theorem B4158179 : Blo 1847625 4158179 := bstep (se 1 (by rfl) ⟨3118634, by rfl⟩ : syracuseStep 4158179 = 6237269) B6237269
theorem B5264099 : Blo 1847625 5264099 := bstep (se 1 (by rfl) ⟨3948074, by rfl⟩ : syracuseStep 5264099 = 7896149) B7896149
theorem B2773745 : Blo 1847625 2773745 := bstep (se 2 (by rfl) ⟨1040154, by rfl⟩ : syracuseStep 2773745 = 2080309) B2080309
theorem B1848051 : Blo 1847625 1848051 := bstep (se 1 (by rfl) ⟨1386038, by rfl⟩ : syracuseStep 1848051 = 2772077) B2772077
theorem B1848067 : Blo 1847625 1848067 := bstep (se 1 (by rfl) ⟨1386050, by rfl⟩ : syracuseStep 1848067 = 2772101) B2772101
theorem B2773763 : Blo 1847625 2773763 := bstep (se 1 (by rfl) ⟨2080322, by rfl⟩ : syracuseStep 2773763 = 4160645) B4160645
theorem B7893773 : Blo 1847625 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B1848083 : Blo 1847625 1848083 := bstep (se 1 (by rfl) ⟨1386062, by rfl⟩ : syracuseStep 1848083 = 2772125) B2772125
theorem B2773793 : Blo 1847625 2773793 := bstep (se 2 (by rfl) ⟨1040172, by rfl⟩ : syracuseStep 2773793 = 2080345) B2080345
theorem B1848099 : Blo 1847625 1848099 := bstep (se 1 (by rfl) ⟨1386074, by rfl⟩ : syracuseStep 1848099 = 2772149) B2772149
theorem B1848115 : Blo 1847625 1848115 := bstep (se 1 (by rfl) ⟨1386086, by rfl⟩ : syracuseStep 1848115 = 2772173) B2772173
theorem B2773811 : Blo 1847625 2773811 := bstep (se 1 (by rfl) ⟨2080358, by rfl⟩ : syracuseStep 2773811 = 4160717) B4160717
theorem B2962241 : Blo 1847625 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B1848131 : Blo 1847625 1848131 := bstep (se 1 (by rfl) ⟨1386098, by rfl⟩ : syracuseStep 1848131 = 2772197) B2772197
theorem B7017293 : Blo 1847625 7017293 := bstep (se 3 (by rfl) ⟨1315742, by rfl⟩ : syracuseStep 7017293 = 2631485) B2631485
theorem B2773841 : Blo 1847625 2773841 := bstep (se 2 (by rfl) ⟨1040190, by rfl⟩ : syracuseStep 2773841 = 2080381) B2080381
theorem B1848147 : Blo 1847625 1848147 := bstep (se 1 (by rfl) ⟨1386110, by rfl⟩ : syracuseStep 1848147 = 2772221) B2772221
theorem B5919587 : Blo 1847625 5919587 := bstep (se 1 (by rfl) ⟨4439690, by rfl⟩ : syracuseStep 5919587 = 8879381) B8879381
theorem B1848163 : Blo 1847625 1848163 := bstep (se 1 (by rfl) ⟨1386122, by rfl⟩ : syracuseStep 1848163 = 2772245) B2772245
theorem B2773859 : Blo 1847625 2773859 := bstep (se 1 (by rfl) ⟨2080394, by rfl⟩ : syracuseStep 2773859 = 4160789) B4160789
theorem B2667377 : Blo 1847625 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B1848179 : Blo 1847625 1848179 := bstep (se 1 (by rfl) ⟨1386134, by rfl⟩ : syracuseStep 1848179 = 2772269) B2772269
theorem B3117953 : Blo 1847625 3117953 := bstep (se 2 (by rfl) ⟨1169232, by rfl⟩ : syracuseStep 3117953 = 2338465) B2338465
theorem B1848195 : Blo 1847625 1848195 := bstep (se 1 (by rfl) ⟨1386146, by rfl⟩ : syracuseStep 1848195 = 2772293) B2772293
theorem B2773889 : Blo 1847625 2773889 := bstep (se 2 (by rfl) ⟨1040208, by rfl⟩ : syracuseStep 2773889 = 2080417) B2080417
theorem B1848211 : Blo 1847625 1848211 := bstep (se 1 (by rfl) ⟨1386158, by rfl⟩ : syracuseStep 1848211 = 2772317) B2772317
theorem B2773907 : Blo 1847625 2773907 := bstep (se 1 (by rfl) ⟨2080430, by rfl⟩ : syracuseStep 2773907 = 4160861) B4160861
theorem B2962337 : Blo 1847625 2962337 := bstep (se 2 (by rfl) ⟨1110876, by rfl⟩ : syracuseStep 2962337 = 2221753) B2221753
theorem B1848227 : Blo 1847625 1848227 := bstep (se 1 (by rfl) ⟨1386170, by rfl⟩ : syracuseStep 1848227 = 2772341) B2772341
theorem B5264291 : Blo 1847625 5264291 := bstep (se 1 (by rfl) ⟨3948218, by rfl⟩ : syracuseStep 5264291 = 7896437) B7896437
theorem B2773937 : Blo 1847625 2773937 := bstep (se 2 (by rfl) ⟨1040226, by rfl⟩ : syracuseStep 2773937 = 2080453) B2080453
theorem B1848243 : Blo 1847625 1848243 := bstep (se 1 (by rfl) ⟨1386182, by rfl⟩ : syracuseStep 1848243 = 2772365) B2772365
theorem B2962369 : Blo 1847625 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B1848259 : Blo 1847625 1848259 := bstep (se 1 (by rfl) ⟨1386194, by rfl⟩ : syracuseStep 1848259 = 2772389) B2772389
theorem B2773955 : Blo 1847625 2773955 := bstep (se 1 (by rfl) ⟨2080466, by rfl⟩ : syracuseStep 2773955 = 4160933) B4160933
theorem B1848275 : Blo 1847625 1848275 := bstep (se 1 (by rfl) ⟨1386206, by rfl⟩ : syracuseStep 1848275 = 2772413) B2772413
theorem B2773985 : Blo 1847625 2773985 := bstep (se 2 (by rfl) ⟨1040244, by rfl⟩ : syracuseStep 2773985 = 2080489) B2080489
theorem B1848291 : Blo 1847625 1848291 := bstep (se 1 (by rfl) ⟨1386218, by rfl⟩ : syracuseStep 1848291 = 2772437) B2772437
theorem B6239213 : Blo 1847625 6239213 := bstep (se 3 (by rfl) ⟨1169852, by rfl⟩ : syracuseStep 6239213 = 2339705) B2339705
theorem B4158449 : Blo 1847625 4158449 := bstep (se 2 (by rfl) ⟨1559418, by rfl⟩ : syracuseStep 4158449 = 3118837) B3118837
theorem B1848307 : Blo 1847625 1848307 := bstep (se 1 (by rfl) ⟨1386230, by rfl⟩ : syracuseStep 1848307 = 2772461) B2772461
theorem B2774003 : Blo 1847625 2774003 := bstep (se 1 (by rfl) ⟨2080502, by rfl⟩ : syracuseStep 2774003 = 4161005) B4161005
theorem B3118081 : Blo 1847625 3118081 := bstep (se 2 (by rfl) ⟨1169280, by rfl⟩ : syracuseStep 3118081 = 2338561) B2338561
theorem B4158467 : Blo 1847625 4158467 := bstep (se 1 (by rfl) ⟨3118850, by rfl⟩ : syracuseStep 4158467 = 6237701) B6237701
theorem B1848323 : Blo 1847625 1848323 := bstep (se 1 (by rfl) ⟨1386242, by rfl⟩ : syracuseStep 1848323 = 2772485) B2772485
theorem B2774033 : Blo 1847625 2774033 := bstep (se 2 (by rfl) ⟨1040262, by rfl⟩ : syracuseStep 2774033 = 2080525) B2080525
theorem B1848339 : Blo 1847625 1848339 := bstep (se 1 (by rfl) ⟨1386254, by rfl⟩ : syracuseStep 1848339 = 2772509) B2772509
theorem B3118115 : Blo 1847625 3118115 := bstep (se 1 (by rfl) ⟨2338586, by rfl⟩ : syracuseStep 3118115 = 4677173) B4677173
theorem B1848355 : Blo 1847625 1848355 := bstep (se 1 (by rfl) ⟨1386266, by rfl⟩ : syracuseStep 1848355 = 2772533) B2772533
theorem B6239267 : Blo 1847625 6239267 := bstep (se 1 (by rfl) ⟨4679450, by rfl⟩ : syracuseStep 6239267 = 9358901) B9358901
theorem B2774051 : Blo 1847625 2774051 := bstep (se 1 (by rfl) ⟨2080538, by rfl⟩ : syracuseStep 2774051 = 4161077) B4161077
theorem B1848371 : Blo 1847625 1848371 := bstep (se 1 (by rfl) ⟨1386278, by rfl⟩ : syracuseStep 1848371 = 2772557) B2772557
theorem B2774081 : Blo 1847625 2774081 := bstep (se 2 (by rfl) ⟨1040280, by rfl⟩ : syracuseStep 2774081 = 2080561) B2080561
theorem B1848387 : Blo 1847625 1848387 := bstep (se 1 (by rfl) ⟨1386290, by rfl⟩ : syracuseStep 1848387 = 2772581) B2772581
theorem B1848403 : Blo 1847625 1848403 := bstep (se 1 (by rfl) ⟨1386302, by rfl⟩ : syracuseStep 1848403 = 2772605) B2772605
theorem B2339923 : Blo 1847625 2339923 := bstep (se 1 (by rfl) ⟨1754942, by rfl⟩ : syracuseStep 2339923 = 3509885) B3509885
theorem B2774099 : Blo 1847625 2774099 := bstep (se 1 (by rfl) ⟨2080574, by rfl⟩ : syracuseStep 2774099 = 4161149) B4161149
theorem B1848419 : Blo 1847625 1848419 := bstep (se 1 (by rfl) ⟨1386314, by rfl⟩ : syracuseStep 1848419 = 2772629) B2772629
theorem B2774129 : Blo 1847625 2774129 := bstep (se 2 (by rfl) ⟨1040298, by rfl⟩ : syracuseStep 2774129 = 2080597) B2080597
theorem B1848435 : Blo 1847625 1848435 := bstep (se 1 (by rfl) ⟨1386326, by rfl⟩ : syracuseStep 1848435 = 2772653) B2772653
theorem B1848451 : Blo 1847625 1848451 := bstep (se 1 (by rfl) ⟨1386338, by rfl⟩ : syracuseStep 1848451 = 2772677) B2772677
theorem B2774147 : Blo 1847625 2774147 := bstep (se 1 (by rfl) ⟨2080610, by rfl⟩ : syracuseStep 2774147 = 4161221) B4161221
theorem B1848467 : Blo 1847625 1848467 := bstep (se 1 (by rfl) ⟨1386350, by rfl⟩ : syracuseStep 1848467 = 2772701) B2772701
theorem B2774177 : Blo 1847625 2774177 := bstep (se 2 (by rfl) ⟨1040316, by rfl⟩ : syracuseStep 2774177 = 2080633) B2080633
theorem B3118243 : Blo 1847625 3118243 := bstep (se 1 (by rfl) ⟨2338682, by rfl⟩ : syracuseStep 3118243 = 4677365) B4677365
theorem B1848483 : Blo 1847625 1848483 := bstep (se 1 (by rfl) ⟨1386362, by rfl⟩ : syracuseStep 1848483 = 2772725) B2772725
theorem B1848499 : Blo 1847625 1848499 := bstep (se 1 (by rfl) ⟨1386374, by rfl⟩ : syracuseStep 1848499 = 2772749) B2772749
theorem B2340019 : Blo 1847625 2340019 := bstep (se 1 (by rfl) ⟨1755014, by rfl⟩ : syracuseStep 2340019 = 3510029) B3510029
theorem B21353653 : Blo 1847625 21353653 := bstep (se 5 (by rfl) ⟨1000952, by rfl⟩ : syracuseStep 21353653 = 2001905) B2001905
theorem B2774195 : Blo 1847625 2774195 := bstep (se 1 (by rfl) ⟨2080646, by rfl⟩ : syracuseStep 2774195 = 4161293) B4161293
theorem B1848515 : Blo 1847625 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B50607301 : Blo 1847625 50607301 := bstep (se 4 (by rfl) ⟨4744434, by rfl⟩ : syracuseStep 50607301 = 9488869) B9488869
theorem B10532045 : Blo 1847625 10532045 := bstep (se 3 (by rfl) ⟨1974758, by rfl⟩ : syracuseStep 10532045 = 3949517) B3949517
theorem B2774225 : Blo 1847625 2774225 := bstep (se 2 (by rfl) ⟨1040334, by rfl⟩ : syracuseStep 2774225 = 2080669) B2080669
theorem B1848531 : Blo 1847625 1848531 := bstep (se 1 (by rfl) ⟨1386398, by rfl⟩ : syracuseStep 1848531 = 2772797) B2772797
theorem B11842787 : Blo 1847625 11842787 := bstep (se 1 (by rfl) ⟨8882090, by rfl⟩ : syracuseStep 11842787 = 17764181) B17764181
theorem B1848547 : Blo 1847625 1848547 := bstep (se 1 (by rfl) ⟨1386410, by rfl⟩ : syracuseStep 1848547 = 2772821) B2772821
theorem B2774243 : Blo 1847625 2774243 := bstep (se 1 (by rfl) ⟨2080682, by rfl⟩ : syracuseStep 2774243 = 4161365) B4161365
theorem B1848563 : Blo 1847625 1848563 := bstep (se 1 (by rfl) ⟨1386422, by rfl⟩ : syracuseStep 1848563 = 2772845) B2772845
theorem B1848579 : Blo 1847625 1848579 := bstep (se 1 (by rfl) ⟨1386434, by rfl⟩ : syracuseStep 1848579 = 2772869) B2772869
theorem B2774273 : Blo 1847625 2774273 := bstep (se 2 (by rfl) ⟨1040352, by rfl⟩ : syracuseStep 2774273 = 2080705) B2080705
theorem B4158737 : Blo 1847625 4158737 := bstep (se 2 (by rfl) ⟨1559526, by rfl⟩ : syracuseStep 4158737 = 3119053) B3119053
theorem B1848595 : Blo 1847625 1848595 := bstep (se 1 (by rfl) ⟨1386446, by rfl⟩ : syracuseStep 1848595 = 2772893) B2772893
theorem B2774291 : Blo 1847625 2774291 := bstep (se 1 (by rfl) ⟨2080718, by rfl⟩ : syracuseStep 2774291 = 4161437) B4161437
theorem B4158755 : Blo 1847625 4158755 := bstep (se 1 (by rfl) ⟨3119066, by rfl⟩ : syracuseStep 4158755 = 6238133) B6238133
theorem B1848611 : Blo 1847625 1848611 := bstep (se 1 (by rfl) ⟨1386458, by rfl⟩ : syracuseStep 1848611 = 2772917) B2772917
theorem B3118385 : Blo 1847625 3118385 := bstep (se 2 (by rfl) ⟨1169394, by rfl⟩ : syracuseStep 3118385 = 2338789) B2338789
theorem B6239537 : Blo 1847625 6239537 := bstep (se 2 (by rfl) ⟨2339826, by rfl⟩ : syracuseStep 6239537 = 4679653) B4679653
theorem B1848627 : Blo 1847625 1848627 := bstep (se 1 (by rfl) ⟨1386470, by rfl⟩ : syracuseStep 1848627 = 2772941) B2772941
theorem B2774321 : Blo 1847625 2774321 := bstep (se 2 (by rfl) ⟨1040370, by rfl⟩ : syracuseStep 2774321 = 2080741) B2080741
theorem B1848643 : Blo 1847625 1848643 := bstep (se 1 (by rfl) ⟨1386482, by rfl⟩ : syracuseStep 1848643 = 2772965) B2772965
theorem B2774339 : Blo 1847625 2774339 := bstep (se 1 (by rfl) ⟨2080754, by rfl⟩ : syracuseStep 2774339 = 4161509) B4161509
theorem B1848659 : Blo 1847625 1848659 := bstep (se 1 (by rfl) ⟨1386494, by rfl⟩ : syracuseStep 1848659 = 2772989) B2772989
theorem B2774369 : Blo 1847625 2774369 := bstep (se 2 (by rfl) ⟨1040388, by rfl⟩ : syracuseStep 2774369 = 2080777) B2080777
theorem B2250083 : Blo 1847625 2250083 := bstep (se 1 (by rfl) ⟨1687562, by rfl⟩ : syracuseStep 2250083 = 3375125) B3375125
theorem B1848675 : Blo 1847625 1848675 := bstep (se 1 (by rfl) ⟨1386506, by rfl⟩ : syracuseStep 1848675 = 2773013) B2773013
theorem B1848691 : Blo 1847625 1848691 := bstep (se 1 (by rfl) ⟨1386518, by rfl⟩ : syracuseStep 1848691 = 2773037) B2773037
theorem B2774387 : Blo 1847625 2774387 := bstep (se 1 (by rfl) ⟨2080790, by rfl⟩ : syracuseStep 2774387 = 4161581) B4161581
theorem B1848707 : Blo 1847625 1848707 := bstep (se 1 (by rfl) ⟨1386530, by rfl⟩ : syracuseStep 1848707 = 2773061) B2773061
theorem B2774417 : Blo 1847625 2774417 := bstep (se 2 (by rfl) ⟨1040406, by rfl⟩ : syracuseStep 2774417 = 2080813) B2080813
theorem B1848723 : Blo 1847625 1848723 := bstep (se 1 (by rfl) ⟨1386542, by rfl⟩ : syracuseStep 1848723 = 2773085) B2773085
theorem B1848739 : Blo 1847625 1848739 := bstep (se 1 (by rfl) ⟨1386554, by rfl⟩ : syracuseStep 1848739 = 2773109) B2773109
theorem B2774435 : Blo 1847625 2774435 := bstep (se 1 (by rfl) ⟨2080826, by rfl⟩ : syracuseStep 2774435 = 4161653) B4161653
theorem B3118513 : Blo 1847625 3118513 := bstep (se 2 (by rfl) ⟨1169442, by rfl⟩ : syracuseStep 3118513 = 2338885) B2338885
theorem B1848755 : Blo 1847625 1848755 := bstep (se 1 (by rfl) ⟨1386566, by rfl⟩ : syracuseStep 1848755 = 2773133) B2773133
theorem B1848771 : Blo 1847625 1848771 := bstep (se 1 (by rfl) ⟨1386578, by rfl⟩ : syracuseStep 1848771 = 2773157) B2773157
theorem B9360845 : Blo 1847625 9360845 := bstep (se 3 (by rfl) ⟨1755158, by rfl⟩ : syracuseStep 9360845 = 3510317) B3510317
theorem B3118547 : Blo 1847625 3118547 := bstep (se 1 (by rfl) ⟨2338910, by rfl⟩ : syracuseStep 3118547 = 4677821) B4677821
theorem B1848787 : Blo 1847625 1848787 := bstep (se 1 (by rfl) ⟨1386590, by rfl⟩ : syracuseStep 1848787 = 2773181) B2773181
theorem B1848803 : Blo 1847625 1848803 := bstep (se 1 (by rfl) ⟨1386602, by rfl⟩ : syracuseStep 1848803 = 2773205) B2773205
theorem B1848819 : Blo 1847625 1848819 := bstep (se 1 (by rfl) ⟨1386614, by rfl⟩ : syracuseStep 1848819 = 2773229) B2773229
theorem B1848835 : Blo 1847625 1848835 := bstep (se 1 (by rfl) ⟨1386626, by rfl⟩ : syracuseStep 1848835 = 2773253) B2773253
theorem B1848851 : Blo 1847625 1848851 := bstep (se 1 (by rfl) ⟨1386638, by rfl⟩ : syracuseStep 1848851 = 2773277) B2773277
theorem B1848867 : Blo 1847625 1848867 := bstep (se 1 (by rfl) ⟨1386650, by rfl⟩ : syracuseStep 1848867 = 2773301) B2773301
theorem B3749411 : Blo 1847625 3749411 := bstep (se 1 (by rfl) ⟨2812058, by rfl⟩ : syracuseStep 3749411 = 5624117) B5624117
theorem B4159025 : Blo 1847625 4159025 := bstep (se 2 (by rfl) ⟨1559634, by rfl⟩ : syracuseStep 4159025 = 3119269) B3119269
theorem B1848883 : Blo 1847625 1848883 := bstep (se 1 (by rfl) ⟨1386662, by rfl⟩ : syracuseStep 1848883 = 2773325) B2773325
theorem B4159043 : Blo 1847625 4159043 := bstep (se 1 (by rfl) ⟨3119282, by rfl⟩ : syracuseStep 4159043 = 6238565) B6238565
theorem B1848899 : Blo 1847625 1848899 := bstep (se 1 (by rfl) ⟨1386674, by rfl⟩ : syracuseStep 1848899 = 2773349) B2773349
theorem B3118675 : Blo 1847625 3118675 := bstep (se 1 (by rfl) ⟨2339006, by rfl⟩ : syracuseStep 3118675 = 4678013) B4678013
theorem B1848915 : Blo 1847625 1848915 := bstep (se 1 (by rfl) ⟨1386686, by rfl⟩ : syracuseStep 1848915 = 2773373) B2773373
theorem B1848931 : Blo 1847625 1848931 := bstep (se 1 (by rfl) ⟨1386698, by rfl⟩ : syracuseStep 1848931 = 2773397) B2773397
theorem B1848947 : Blo 1847625 1848947 := bstep (se 1 (by rfl) ⟨1386710, by rfl⟩ : syracuseStep 1848947 = 2773421) B2773421
theorem B1848963 : Blo 1847625 1848963 := bstep (se 1 (by rfl) ⟨1386722, by rfl⟩ : syracuseStep 1848963 = 2773445) B2773445
theorem B1848979 : Blo 1847625 1848979 := bstep (se 1 (by rfl) ⟨1386734, by rfl⟩ : syracuseStep 1848979 = 2773469) B2773469
theorem B1848995 : Blo 1847625 1848995 := bstep (se 1 (by rfl) ⟨1386746, by rfl⟩ : syracuseStep 1848995 = 2773493) B2773493
theorem B2340515 : Blo 1847625 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B1849011 : Blo 1847625 1849011 := bstep (se 1 (by rfl) ⟨1386758, by rfl⟩ : syracuseStep 1849011 = 2773517) B2773517
theorem B1849027 : Blo 1847625 1849027 := bstep (se 1 (by rfl) ⟨1386770, by rfl⟩ : syracuseStep 1849027 = 2773541) B2773541
theorem B5265101 : Blo 1847625 5265101 := bstep (se 3 (by rfl) ⟨987206, by rfl⟩ : syracuseStep 5265101 = 1974413) B1974413
theorem B2668243 : Blo 1847625 2668243 := bstep (se 1 (by rfl) ⟨2001182, by rfl⟩ : syracuseStep 2668243 = 4002365) B4002365
theorem B1849043 : Blo 1847625 1849043 := bstep (se 1 (by rfl) ⟨1386782, by rfl⟩ : syracuseStep 1849043 = 2773565) B2773565
theorem B3118817 : Blo 1847625 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B1849059 : Blo 1847625 1849059 := bstep (se 1 (by rfl) ⟨1386794, by rfl⟩ : syracuseStep 1849059 = 2773589) B2773589
theorem B1849075 : Blo 1847625 1849075 := bstep (se 1 (by rfl) ⟨1386806, by rfl⟩ : syracuseStep 1849075 = 2773613) B2773613
theorem B1849091 : Blo 1847625 1849091 := bstep (se 1 (by rfl) ⟨1386818, by rfl⟩ : syracuseStep 1849091 = 2773637) B2773637
theorem B1849107 : Blo 1847625 1849107 := bstep (se 1 (by rfl) ⟨1386830, by rfl⟩ : syracuseStep 1849107 = 2773661) B2773661
theorem B1849123 : Blo 1847625 1849123 := bstep (se 1 (by rfl) ⟨1386842, by rfl⟩ : syracuseStep 1849123 = 2773685) B2773685
theorem B1849139 : Blo 1847625 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B22484789 : Blo 1847625 22484789 := bstep (se 5 (by rfl) ⟨1053974, by rfl⟩ : syracuseStep 22484789 = 2107949) B2107949
theorem B1849155 : Blo 1847625 1849155 := bstep (se 1 (by rfl) ⟨1386866, by rfl⟩ : syracuseStep 1849155 = 2773733) B2773733
theorem B6240077 : Blo 1847625 6240077 := bstep (se 3 (by rfl) ⟨1170014, by rfl⟩ : syracuseStep 6240077 = 2340029) B2340029
theorem B4159313 : Blo 1847625 4159313 := bstep (se 2 (by rfl) ⟨1559742, by rfl⟩ : syracuseStep 4159313 = 3119485) B3119485
theorem B1849171 : Blo 1847625 1849171 := bstep (se 1 (by rfl) ⟨1386878, by rfl⟩ : syracuseStep 1849171 = 2773757) B2773757
theorem B3118945 : Blo 1847625 3118945 := bstep (se 2 (by rfl) ⟨1169604, by rfl⟩ : syracuseStep 3118945 = 2339209) B2339209
theorem B4159331 : Blo 1847625 4159331 := bstep (se 1 (by rfl) ⟨3119498, by rfl⟩ : syracuseStep 4159331 = 6238997) B6238997
theorem B1849187 : Blo 1847625 1849187 := bstep (se 1 (by rfl) ⟨1386890, by rfl⟩ : syracuseStep 1849187 = 2773781) B2773781
theorem B1849203 : Blo 1847625 1849203 := bstep (se 1 (by rfl) ⟨1386902, by rfl⟩ : syracuseStep 1849203 = 2773805) B2773805
theorem B3118979 : Blo 1847625 3118979 := bstep (se 1 (by rfl) ⟨2339234, by rfl⟩ : syracuseStep 3118979 = 4678469) B4678469
theorem B6240131 : Blo 1847625 6240131 := bstep (se 1 (by rfl) ⟨4680098, by rfl⟩ : syracuseStep 6240131 = 9360197) B9360197
theorem B5265283 : Blo 1847625 5265283 := bstep (se 1 (by rfl) ⟨3948962, by rfl⟩ : syracuseStep 5265283 = 7897925) B7897925
theorem B1849219 : Blo 1847625 1849219 := bstep (se 1 (by rfl) ⟨1386914, by rfl⟩ : syracuseStep 1849219 = 2773829) B2773829
theorem B16013197 : Blo 1847625 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1849235 : Blo 1847625 1849235 := bstep (se 1 (by rfl) ⟨1386926, by rfl⟩ : syracuseStep 1849235 = 2773853) B2773853
theorem B1849251 : Blo 1847625 1849251 := bstep (se 1 (by rfl) ⟨1386938, by rfl⟩ : syracuseStep 1849251 = 2773877) B2773877
theorem B1849267 : Blo 1847625 1849267 := bstep (se 1 (by rfl) ⟨1386950, by rfl⟩ : syracuseStep 1849267 = 2773901) B2773901
theorem B1849283 : Blo 1847625 1849283 := bstep (se 1 (by rfl) ⟨1386962, by rfl⟩ : syracuseStep 1849283 = 2773925) B2773925
theorem B1849299 : Blo 1847625 1849299 := bstep (se 1 (by rfl) ⟨1386974, by rfl⟩ : syracuseStep 1849299 = 2773949) B2773949
theorem B14030819 : Blo 1847625 14030819 := bstep (se 1 (by rfl) ⟨10523114, by rfl⟩ : syracuseStep 14030819 = 21046229) B21046229
theorem B1849315 : Blo 1847625 1849315 := bstep (se 1 (by rfl) ⟨1386986, by rfl⟩ : syracuseStep 1849315 = 2773973) B2773973
theorem B2078707 : Blo 1847625 2078707 := bstep (se 1 (by rfl) ⟨1559030, by rfl⟩ : syracuseStep 2078707 = 3118061) B3118061
theorem B1849331 : Blo 1847625 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B3119107 : Blo 1847625 3119107 := bstep (se 1 (by rfl) ⟨2339330, by rfl⟩ : syracuseStep 3119107 = 4678661) B4678661
theorem B1849347 : Blo 1847625 1849347 := bstep (se 1 (by rfl) ⟨1387010, by rfl⟩ : syracuseStep 1849347 = 2774021) B2774021
theorem B1849363 : Blo 1847625 1849363 := bstep (se 1 (by rfl) ⟨1387022, by rfl⟩ : syracuseStep 1849363 = 2774045) B2774045
theorem B1849379 : Blo 1847625 1849379 := bstep (se 1 (by rfl) ⟨1387034, by rfl⟩ : syracuseStep 1849379 = 2774069) B2774069
theorem B1849395 : Blo 1847625 1849395 := bstep (se 1 (by rfl) ⟨1387046, by rfl⟩ : syracuseStep 1849395 = 2774093) B2774093
theorem B1849411 : Blo 1847625 1849411 := bstep (se 1 (by rfl) ⟨1387058, by rfl⟩ : syracuseStep 1849411 = 2774117) B2774117
theorem B1849427 : Blo 1847625 1849427 := bstep (se 1 (by rfl) ⟨1387070, by rfl⟩ : syracuseStep 1849427 = 2774141) B2774141
theorem B1849443 : Blo 1847625 1849443 := bstep (se 1 (by rfl) ⟨1387082, by rfl⟩ : syracuseStep 1849443 = 2774165) B2774165
theorem B4159601 : Blo 1847625 4159601 := bstep (se 2 (by rfl) ⟨1559850, by rfl⟩ : syracuseStep 4159601 = 3119701) B3119701
theorem B1849459 : Blo 1847625 1849459 := bstep (se 1 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 1849459 = 2774189) B2774189
theorem B2078851 : Blo 1847625 2078851 := bstep (se 1 (by rfl) ⟨1559138, by rfl⟩ : syracuseStep 2078851 = 3118277) B3118277
theorem B4159619 : Blo 1847625 4159619 := bstep (se 1 (by rfl) ⟨3119714, by rfl⟩ : syracuseStep 4159619 = 6239429) B6239429
theorem B1849475 : Blo 1847625 1849475 := bstep (se 1 (by rfl) ⟨1387106, by rfl⟩ : syracuseStep 1849475 = 2774213) B2774213
theorem B8001677 : Blo 1847625 8001677 := bstep (se 3 (by rfl) ⟨1500314, by rfl⟩ : syracuseStep 8001677 = 3000629) B3000629
theorem B3119249 : Blo 1847625 3119249 := bstep (se 2 (by rfl) ⟨1169718, by rfl⟩ : syracuseStep 3119249 = 2339437) B2339437
theorem B6240401 : Blo 1847625 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B1849491 : Blo 1847625 1849491 := bstep (se 1 (by rfl) ⟨1387118, by rfl⟩ : syracuseStep 1849491 = 2774237) B2774237
theorem B1849507 : Blo 1847625 1849507 := bstep (se 1 (by rfl) ⟨1387130, by rfl⟩ : syracuseStep 1849507 = 2774261) B2774261
theorem B1849523 : Blo 1847625 1849523 := bstep (se 1 (by rfl) ⟨1387142, by rfl⟩ : syracuseStep 1849523 = 2774285) B2774285
theorem B1849539 : Blo 1847625 1849539 := bstep (se 1 (by rfl) ⟨1387154, by rfl⟩ : syracuseStep 1849539 = 2774309) B2774309
theorem B1849555 : Blo 1847625 1849555 := bstep (se 1 (by rfl) ⟨1387166, by rfl⟩ : syracuseStep 1849555 = 2774333) B2774333
theorem B1849571 : Blo 1847625 1849571 := bstep (se 1 (by rfl) ⟨1387178, by rfl⟩ : syracuseStep 1849571 = 2774357) B2774357
theorem B17766641 : Blo 1847625 17766641 := bstep (se 2 (by rfl) ⟨6662490, by rfl⟩ : syracuseStep 17766641 = 13324981) B13324981
theorem B1849587 : Blo 1847625 1849587 := bstep (se 1 (by rfl) ⟨1387190, by rfl⟩ : syracuseStep 1849587 = 2774381) B2774381
theorem B1849603 : Blo 1847625 1849603 := bstep (se 1 (by rfl) ⟨1387202, by rfl⟩ : syracuseStep 1849603 = 2774405) B2774405
theorem B3119377 : Blo 1847625 3119377 := bstep (se 2 (by rfl) ⟨1169766, by rfl⟩ : syracuseStep 3119377 = 2339533) B2339533
theorem B2078995 : Blo 1847625 2078995 := bstep (se 1 (by rfl) ⟨1559246, by rfl⟩ : syracuseStep 2078995 = 3118493) B3118493
theorem B1849619 : Blo 1847625 1849619 := bstep (se 1 (by rfl) ⟨1387214, by rfl⟩ : syracuseStep 1849619 = 2774429) B2774429
theorem B3946801 : Blo 1847625 3946801 := bstep (se 2 (by rfl) ⟨1480050, by rfl⟩ : syracuseStep 3946801 = 2960101) B2960101
theorem B3119411 : Blo 1847625 3119411 := bstep (se 1 (by rfl) ⟨2339558, by rfl⟩ : syracuseStep 3119411 = 4679117) B4679117
theorem B5265773 : Blo 1847625 5265773 := bstep (se 3 (by rfl) ⟨987332, by rfl⟩ : syracuseStep 5265773 = 1974665) B1974665
theorem B4159889 : Blo 1847625 4159889 := bstep (se 2 (by rfl) ⟨1559958, by rfl⟩ : syracuseStep 4159889 = 3119917) B3119917
theorem B2079139 : Blo 1847625 2079139 := bstep (se 1 (by rfl) ⟨1559354, by rfl⟩ : syracuseStep 2079139 = 3118709) B3118709
theorem B4159907 : Blo 1847625 4159907 := bstep (se 1 (by rfl) ⟨3119930, by rfl⟩ : syracuseStep 4159907 = 6239861) B6239861
theorem B5921201 : Blo 1847625 5921201 := bstep (se 2 (by rfl) ⟨2220450, by rfl⟩ : syracuseStep 5921201 = 4440901) B4440901
theorem B3119539 : Blo 1847625 3119539 := bstep (se 1 (by rfl) ⟨2339654, by rfl⟩ : syracuseStep 3119539 = 4679309) B4679309
theorem B3947057 : Blo 1847625 3947057 := bstep (se 2 (by rfl) ⟨1480146, by rfl⟩ : syracuseStep 3947057 = 2960293) B2960293
theorem B2079283 : Blo 1847625 2079283 := bstep (se 1 (by rfl) ⟨1559462, by rfl⟩ : syracuseStep 2079283 = 3118925) B3118925
theorem B3119681 : Blo 1847625 3119681 := bstep (se 2 (by rfl) ⟨1169880, by rfl⟩ : syracuseStep 3119681 = 2339761) B2339761
theorem B12647011 : Blo 1847625 12647011 := bstep (se 1 (by rfl) ⟨9485258, by rfl⟩ : syracuseStep 12647011 = 18970517) B18970517
theorem B6240941 : Blo 1847625 6240941 := bstep (se 3 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 6240941 = 2340353) B2340353
theorem B4160177 : Blo 1847625 4160177 := bstep (se 2 (by rfl) ⟨1560066, by rfl⟩ : syracuseStep 4160177 = 3120133) B3120133
theorem B3119809 : Blo 1847625 3119809 := bstep (se 2 (by rfl) ⟨1169928, by rfl⟩ : syracuseStep 3119809 = 2339857) B2339857
theorem B2079427 : Blo 1847625 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B4160195 : Blo 1847625 4160195 := bstep (se 1 (by rfl) ⟨3120146, by rfl⟩ : syracuseStep 4160195 = 6240293) B6240293
theorem B89979605 : Blo 1847625 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B3119843 : Blo 1847625 3119843 := bstep (se 1 (by rfl) ⟨2339882, by rfl⟩ : syracuseStep 3119843 = 4679765) B4679765
theorem B6240995 : Blo 1847625 6240995 := bstep (se 1 (by rfl) ⟨4680746, by rfl⟩ : syracuseStep 6240995 = 9361493) B9361493
theorem B2497315 : Blo 1847625 2497315 := bstep (se 1 (by rfl) ⟨1872986, by rfl⟩ : syracuseStep 2497315 = 3745973) B3745973
theorem B4274993 : Blo 1847625 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B2079571 : Blo 1847625 2079571 := bstep (se 1 (by rfl) ⟨1559678, by rfl⟩ : syracuseStep 2079571 = 3119357) B3119357
theorem B3119971 : Blo 1847625 3119971 := bstep (se 1 (by rfl) ⟨2339978, by rfl⟩ : syracuseStep 3119971 = 4679957) B4679957
theorem B7019405 : Blo 1847625 7019405 := bstep (se 3 (by rfl) ⟨1316138, by rfl⟩ : syracuseStep 7019405 = 2632277) B2632277
theorem B3160993 : Blo 1847625 3160993 := bstep (se 2 (by rfl) ⟨1185372, by rfl⟩ : syracuseStep 3160993 = 2370745) B2370745
theorem B4160465 : Blo 1847625 4160465 := bstep (se 2 (by rfl) ⟨1560174, by rfl⟩ : syracuseStep 4160465 = 3120349) B3120349
theorem B2079715 : Blo 1847625 2079715 := bstep (se 1 (by rfl) ⟨1559786, by rfl⟩ : syracuseStep 2079715 = 3119573) B3119573
theorem B4160483 : Blo 1847625 4160483 := bstep (se 1 (by rfl) ⟨3120362, by rfl⟩ : syracuseStep 4160483 = 6240725) B6240725
theorem B3120113 : Blo 1847625 3120113 := bstep (se 2 (by rfl) ⟨1170042, by rfl⟩ : syracuseStep 3120113 = 2340085) B2340085
theorem B6241265 : Blo 1847625 6241265 := bstep (se 2 (by rfl) ⟨2340474, by rfl⟩ : syracuseStep 6241265 = 4680949) B4680949
theorem B1973251 : Blo 1847625 1973251 := bstep (se 1 (by rfl) ⟨1479938, by rfl⟩ : syracuseStep 1973251 = 2959877) B2959877
theorem B4996099 : Blo 1847625 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B3120241 : Blo 1847625 3120241 := bstep (se 2 (by rfl) ⟨1170090, by rfl⟩ : syracuseStep 3120241 = 2340181) B2340181
theorem B2079859 : Blo 1847625 2079859 := bstep (se 1 (by rfl) ⟨1559894, by rfl⟩ : syracuseStep 2079859 = 3119789) B3119789
theorem B3120275 : Blo 1847625 3120275 := bstep (se 1 (by rfl) ⟨2340206, by rfl⟩ : syracuseStep 3120275 = 4680413) B4680413
theorem B4676849 : Blo 1847625 4676849 := bstep (se 2 (by rfl) ⟨1753818, by rfl⟩ : syracuseStep 4676849 = 3507637) B3507637
theorem B4160753 : Blo 1847625 4160753 := bstep (se 2 (by rfl) ⟨1560282, by rfl⟩ : syracuseStep 4160753 = 3120565) B3120565
theorem B2080003 : Blo 1847625 2080003 := bstep (se 1 (by rfl) ⟨1560002, by rfl⟩ : syracuseStep 2080003 = 3120005) B3120005
theorem B4160771 : Blo 1847625 4160771 := bstep (se 1 (by rfl) ⟨3120578, by rfl⟩ : syracuseStep 4160771 = 6241157) B6241157
theorem B3120403 : Blo 1847625 3120403 := bstep (se 1 (by rfl) ⟨2340302, by rfl⟩ : syracuseStep 3120403 = 4680605) B4680605
theorem B4676899 : Blo 1847625 4676899 := bstep (se 1 (by rfl) ⟨3507674, by rfl⟩ : syracuseStep 4676899 = 7015349) B7015349
theorem B11844913 : Blo 1847625 11844913 := bstep (se 2 (by rfl) ⟨4441842, by rfl⟩ : syracuseStep 11844913 = 8883685) B8883685
theorem B47357297 : Blo 1847625 47357297 := bstep (se 2 (by rfl) ⟨17758986, by rfl⟩ : syracuseStep 47357297 = 35517973) B35517973
theorem B2080147 : Blo 1847625 2080147 := bstep (se 1 (by rfl) ⟨1560110, by rfl⟩ : syracuseStep 2080147 = 3120221) B3120221
theorem B3120545 : Blo 1847625 3120545 := bstep (se 2 (by rfl) ⟨1170204, by rfl⟩ : syracuseStep 3120545 = 2340409) B2340409
theorem B4677041 : Blo 1847625 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B17767907 : Blo 1847625 17767907 := bstep (se 1 (by rfl) ⟨13325930, by rfl⟩ : syracuseStep 17767907 = 26651861) B26651861
theorem B5619203 : Blo 1847625 5619203 := bstep (se 1 (by rfl) ⟨4214402, by rfl⟩ : syracuseStep 5619203 = 8428805) B8428805
theorem B10526213 : Blo 1847625 10526213 := bstep (se 4 (by rfl) ⟨986832, by rfl⟩ : syracuseStep 10526213 = 1973665) B1973665
theorem B6241805 : Blo 1847625 6241805 := bstep (se 3 (by rfl) ⟨1170338, by rfl⟩ : syracuseStep 6241805 = 2340677) B2340677
theorem B5266957 : Blo 1847625 5266957 := bstep (se 3 (by rfl) ⟨987554, by rfl⟩ : syracuseStep 5266957 = 1975109) B1975109
theorem B4161041 : Blo 1847625 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B51994133 : Blo 1847625 51994133 := bstep (se 6 (by rfl) ⟨1218612, by rfl⟩ : syracuseStep 51994133 = 2437225) B2437225
theorem B3120673 : Blo 1847625 3120673 := bstep (se 2 (by rfl) ⟨1170252, by rfl⟩ : syracuseStep 3120673 = 2340505) B2340505
theorem B2080291 : Blo 1847625 2080291 := bstep (se 1 (by rfl) ⟨1560218, by rfl⟩ : syracuseStep 2080291 = 3120437) B3120437
theorem B4161059 : Blo 1847625 4161059 := bstep (se 1 (by rfl) ⟨3120794, by rfl⟩ : syracuseStep 4161059 = 6241589) B6241589
theorem B3120707 : Blo 1847625 3120707 := bstep (se 1 (by rfl) ⟨2340530, by rfl⟩ : syracuseStep 3120707 = 4681061) B4681061
theorem B6241859 : Blo 1847625 6241859 := bstep (se 1 (by rfl) ⟨4681394, by rfl⟩ : syracuseStep 6241859 = 9362789) B9362789
theorem B9354851 : Blo 1847625 9354851 := bstep (se 1 (by rfl) ⟨7016138, by rfl⟩ : syracuseStep 9354851 = 14032277) B14032277
theorem B7020209 : Blo 1847625 7020209 := bstep (se 2 (by rfl) ⟨2632578, by rfl⟩ : syracuseStep 7020209 = 5265157) B5265157
theorem B2080435 : Blo 1847625 2080435 := bstep (se 1 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 2080435 = 3120653) B3120653
theorem B3120835 : Blo 1847625 3120835 := bstep (se 1 (by rfl) ⟨2340626, by rfl⟩ : syracuseStep 3120835 = 4681253) B4681253
theorem B4439825 : Blo 1847625 4439825 := bstep (se 2 (by rfl) ⟨1664934, by rfl⟩ : syracuseStep 4439825 = 3329869) B3329869
theorem B4161329 : Blo 1847625 4161329 := bstep (se 2 (by rfl) ⟨1560498, by rfl⟩ : syracuseStep 4161329 = 3120997) B3120997
theorem B3948355 : Blo 1847625 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B2080579 : Blo 1847625 2080579 := bstep (se 1 (by rfl) ⟨1560434, by rfl⟩ : syracuseStep 2080579 = 3120869) B3120869
theorem B4161347 : Blo 1847625 4161347 := bstep (se 1 (by rfl) ⟨3121010, by rfl⟩ : syracuseStep 4161347 = 6242021) B6242021
theorem B3120977 : Blo 1847625 3120977 := bstep (se 2 (by rfl) ⟨1170366, by rfl⟩ : syracuseStep 3120977 = 2340733) B2340733
theorem B6242129 : Blo 1847625 6242129 := bstep (se 2 (by rfl) ⟨2340798, by rfl⟩ : syracuseStep 6242129 = 4681597) B4681597
theorem B10526669 : Blo 1847625 10526669 := bstep (se 3 (by rfl) ⟨1973750, by rfl⟩ : syracuseStep 10526669 = 3947501) B3947501
theorem B4440017 : Blo 1847625 4440017 := bstep (se 2 (by rfl) ⟨1665006, by rfl⟩ : syracuseStep 4440017 = 3330013) B3330013
theorem B3121105 : Blo 1847625 3121105 := bstep (se 2 (by rfl) ⟨1170414, by rfl⟩ : syracuseStep 3121105 = 2340829) B2340829
theorem B2080723 : Blo 1847625 2080723 := bstep (se 1 (by rfl) ⟨1560542, by rfl⟩ : syracuseStep 2080723 = 3121085) B3121085
theorem B13320163 : Blo 1847625 13320163 := bstep (se 1 (by rfl) ⟨9990122, by rfl⟩ : syracuseStep 13320163 = 19980245) B19980245
theorem B3121139 : Blo 1847625 3121139 := bstep (se 1 (by rfl) ⟨2340854, by rfl⟩ : syracuseStep 3121139 = 4681709) B4681709
theorem B2498699 : Blo 1847625 2498699 := bstep (se 1 (by rfl) ⟨1874024, by rfl⟩ : syracuseStep 2498699 = 3748049) B3748049
theorem B7020695 : Blo 1847625 7020695 := bstep (se 1 (by rfl) ⟨5265521, by rfl⟩ : syracuseStep 7020695 = 10531043) B10531043
theorem B3948697 : Blo 1847625 3948697 := bstep (se 2 (by rfl) ⟨1480761, by rfl⟩ : syracuseStep 3948697 = 2961523) B2961523
theorem B3948851 : Blo 1847625 3948851 := bstep (se 1 (by rfl) ⟨2961638, by rfl⟩ : syracuseStep 3948851 = 5923277) B5923277
theorem B13320625 : Blo 1847625 13320625 := bstep (se 2 (by rfl) ⟨4995234, by rfl⟩ : syracuseStep 13320625 = 9990469) B9990469
theorem B1974827 : Blo 1847625 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B4678195 : Blo 1847625 4678195 := bstep (se 1 (by rfl) ⟨3508646, by rfl⟩ : syracuseStep 4678195 = 7017293) B7017293
theorem B4678337 : Blo 1847625 4678337 := bstep (se 2 (by rfl) ⟨1754376, by rfl⟩ : syracuseStep 4678337 = 3508753) B3508753
theorem B7021363 : Blo 1847625 7021363 := bstep (se 1 (by rfl) ⟨5266022, by rfl⟩ : syracuseStep 7021363 = 10532045) B10532045
theorem B9487169 : Blo 1847625 9487169 := bstep (se 2 (by rfl) ⟨3557688, by rfl⟩ : syracuseStep 9487169 = 7115377) B7115377
theorem B7898077 : Blo 1847625 7898077 := bstep (se 3 (by rfl) ⟨1480889, by rfl⟩ : syracuseStep 7898077 = 2961779) B2961779
theorem B2499607 : Blo 1847625 2499607 := bstep (se 1 (by rfl) ⟨1874705, by rfl⟩ : syracuseStep 2499607 = 3749411) B3749411
theorem B3949825 : Blo 1847625 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B14034221 : Blo 1847625 14034221 := bstep (se 3 (by rfl) ⟨2631416, by rfl⟩ : syracuseStep 14034221 = 5262833) B5262833
theorem B8111411 : Blo 1847625 8111411 := bstep (se 1 (by rfl) ⟨6083558, by rfl⟩ : syracuseStep 8111411 = 12167117) B12167117
theorem B15795607 : Blo 1847625 15795607 := bstep (se 1 (by rfl) ⟨11846705, by rfl⟩ : syracuseStep 15795607 = 23693411) B23693411
theorem B3950167 : Blo 1847625 3950167 := bstep (se 1 (by rfl) ⟨2962625, by rfl⟩ : syracuseStep 3950167 = 5925251) B5925251
theorem B2631371 : Blo 1847625 2631371 := bstep (se 1 (by rfl) ⟨1973528, by rfl⟩ : syracuseStep 2631371 = 3947057) B3947057
theorem B6235865 : Blo 1847625 6235865 := bstep (se 2 (by rfl) ⟨2338449, by rfl⟩ : syracuseStep 6235865 = 4676899) B4676899
theorem B5924573 : Blo 1847625 5924573 := bstep (se 3 (by rfl) ⟨1110857, by rfl⟩ : syracuseStep 5924573 = 2221715) B2221715
theorem B7898897 : Blo 1847625 7898897 := bstep (se 2 (by rfl) ⟨2962086, by rfl⟩ : syracuseStep 7898897 = 5924173) B5924173
theorem B4679603 : Blo 1847625 4679603 := bstep (se 1 (by rfl) ⟨3509702, by rfl⟩ : syracuseStep 4679603 = 7019405) B7019405
theorem B7022609 : Blo 1847625 7022609 := bstep (se 2 (by rfl) ⟨2633478, by rfl⟩ : syracuseStep 7022609 = 5266957) B5266957
theorem B85403717 : Blo 1847625 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B9357443 : Blo 1847625 9357443 := bstep (se 1 (by rfl) ⟨7018082, by rfl⟩ : syracuseStep 9357443 = 14036165) B14036165
theorem B3508427 : Blo 1847625 3508427 := bstep (se 1 (by rfl) ⟨2631320, by rfl⟩ : syracuseStep 3508427 = 5262641) B5262641
theorem B3557657 : Blo 1847625 3557657 := bstep (se 2 (by rfl) ⟨1334121, by rfl⟩ : syracuseStep 3557657 = 2668243) B2668243
theorem B7113005 : Blo 1847625 7113005 := bstep (se 3 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 7113005 = 2667377) B2667377
theorem B4999475 : Blo 1847625 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B3746135 : Blo 1847625 3746135 := bstep (se 1 (by rfl) ⟨2809601, by rfl⟩ : syracuseStep 3746135 = 5619203) B5619203
theorem B34662755 : Blo 1847625 34662755 := bstep (se 1 (by rfl) ⟨25997066, by rfl⟩ : syracuseStep 34662755 = 51994133) B51994133
theorem B3508609 : Blo 1847625 3508609 := bstep (se 2 (by rfl) ⟨1315728, by rfl⟩ : syracuseStep 3508609 = 2631457) B2631457
theorem B6236567 : Blo 1847625 6236567 := bstep (se 1 (by rfl) ⟨4677425, by rfl⟩ : syracuseStep 6236567 = 9354851) B9354851
theorem B7899565 : Blo 1847625 7899565 := bstep (se 3 (by rfl) ⟨1481168, by rfl⟩ : syracuseStep 7899565 = 2962337) B2962337
theorem B4680139 : Blo 1847625 4680139 := bstep (se 1 (by rfl) ⟨3510104, by rfl⟩ : syracuseStep 4680139 = 7020209) B7020209
theorem B2959883 : Blo 1847625 2959883 := bstep (se 1 (by rfl) ⟨2219912, by rfl⟩ : syracuseStep 2959883 = 4439825) B4439825
theorem B2771531 : Blo 1847625 2771531 := bstep (se 1 (by rfl) ⟨2078648, by rfl⟩ : syracuseStep 2771531 = 4157297) B4157297
theorem B2771543 : Blo 1847625 2771543 := bstep (se 1 (by rfl) ⟨2078657, by rfl⟩ : syracuseStep 2771543 = 4157315) B4157315
theorem B4680281 : Blo 1847625 4680281 := bstep (se 2 (by rfl) ⟨1755105, by rfl⟩ : syracuseStep 4680281 = 3510211) B3510211
theorem B2960011 : Blo 1847625 2960011 := bstep (se 1 (by rfl) ⟨2220008, by rfl⟩ : syracuseStep 2960011 = 4440017) B4440017
theorem B2771609 : Blo 1847625 2771609 := bstep (se 2 (by rfl) ⟨1039353, by rfl⟩ : syracuseStep 2771609 = 2078707) B2078707
theorem B7498433 : Blo 1847625 7498433 := bstep (se 2 (by rfl) ⟨2811912, by rfl⟩ : syracuseStep 7498433 = 5623825) B5623825
theorem B2771723 : Blo 1847625 2771723 := bstep (se 1 (by rfl) ⟨2078792, by rfl⟩ : syracuseStep 2771723 = 4157585) B4157585
theorem B2771735 : Blo 1847625 2771735 := bstep (se 1 (by rfl) ⟨2078801, by rfl⟩ : syracuseStep 2771735 = 4157603) B4157603
theorem B3509057 : Blo 1847625 3509057 := bstep (se 2 (by rfl) ⟨1315896, by rfl⟩ : syracuseStep 3509057 = 2631793) B2631793
theorem B2771801 : Blo 1847625 2771801 := bstep (se 2 (by rfl) ⟨1039425, by rfl⟩ : syracuseStep 2771801 = 2078851) B2078851
theorem B7015319 : Blo 1847625 7015319 := bstep (se 1 (by rfl) ⟨5261489, by rfl⟩ : syracuseStep 7015319 = 10522979) B10522979
theorem B6237107 : Blo 1847625 6237107 := bstep (se 1 (by rfl) ⟨4677830, by rfl⟩ : syracuseStep 6237107 = 9355661) B9355661
theorem B21056435 : Blo 1847625 21056435 := bstep (se 1 (by rfl) ⟨15792326, by rfl⟩ : syracuseStep 21056435 = 31584653) B31584653
theorem B2771915 : Blo 1847625 2771915 := bstep (se 1 (by rfl) ⟨2078936, by rfl⟩ : syracuseStep 2771915 = 4157873) B4157873
theorem B2771927 : Blo 1847625 2771927 := bstep (se 1 (by rfl) ⟨2078945, by rfl⟩ : syracuseStep 2771927 = 4157891) B4157891
theorem B7900163 : Blo 1847625 7900163 := bstep (se 1 (by rfl) ⟨5925122, by rfl⟩ : syracuseStep 7900163 = 11850245) B11850245
theorem B2771993 : Blo 1847625 2771993 := bstep (se 2 (by rfl) ⟨1039497, by rfl⟩ : syracuseStep 2771993 = 2078995) B2078995
theorem B10529837 : Blo 1847625 10529837 := bstep (se 3 (by rfl) ⟨1974344, by rfl⟩ : syracuseStep 10529837 = 3948689) B3948689
theorem B5262401 : Blo 1847625 5262401 := bstep (se 2 (by rfl) ⟨1973400, by rfl⟩ : syracuseStep 5262401 = 3946801) B3946801
theorem B7015517 : Blo 1847625 7015517 := bstep (se 3 (by rfl) ⟨1315409, by rfl⟩ : syracuseStep 7015517 = 2630819) B2630819
theorem B3746945 : Blo 1847625 3746945 := bstep (se 2 (by rfl) ⟨1405104, by rfl⟩ : syracuseStep 3746945 = 2810209) B2810209
theorem B2772107 : Blo 1847625 2772107 := bstep (se 1 (by rfl) ⟨2079080, by rfl⟩ : syracuseStep 2772107 = 4158161) B4158161
theorem B2772119 : Blo 1847625 2772119 := bstep (se 1 (by rfl) ⟨2079089, by rfl⟩ : syracuseStep 2772119 = 4158179) B4158179
theorem B3509399 : Blo 1847625 3509399 := bstep (se 1 (by rfl) ⟨2632049, by rfl⟩ : syracuseStep 3509399 = 5264099) B5264099
theorem B5262515 : Blo 1847625 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B6237377 : Blo 1847625 6237377 := bstep (se 2 (by rfl) ⟨2339016, by rfl⟩ : syracuseStep 6237377 = 4678033) B4678033
theorem B2772185 : Blo 1847625 2772185 := bstep (se 2 (by rfl) ⟨1039569, by rfl⟩ : syracuseStep 2772185 = 2079139) B2079139
theorem B11840813 : Blo 1847625 11840813 := bstep (se 3 (by rfl) ⟨2220152, by rfl⟩ : syracuseStep 11840813 = 4440305) B4440305
theorem B2772299 : Blo 1847625 2772299 := bstep (se 1 (by rfl) ⟨2079224, by rfl⟩ : syracuseStep 2772299 = 4158449) B4158449
theorem B2772311 : Blo 1847625 2772311 := bstep (se 1 (by rfl) ⟨2079233, by rfl⟩ : syracuseStep 2772311 = 4158467) B4158467
theorem B2960729 : Blo 1847625 2960729 := bstep (se 2 (by rfl) ⟨1110273, by rfl⟩ : syracuseStep 2960729 = 2220547) B2220547
theorem B10268005 : Blo 1847625 10268005 := bstep (se 4 (by rfl) ⟨962625, by rfl⟩ : syracuseStep 10268005 = 1925251) B1925251
theorem B4681111 : Blo 1847625 4681111 := bstep (se 1 (by rfl) ⟨3510833, by rfl⟩ : syracuseStep 4681111 = 7021667) B7021667
theorem B2772377 : Blo 1847625 2772377 := bstep (se 2 (by rfl) ⟨1039641, by rfl⟩ : syracuseStep 2772377 = 2079283) B2079283
theorem B16862681 : Blo 1847625 16862681 := bstep (se 2 (by rfl) ⟨6323505, by rfl⟩ : syracuseStep 16862681 = 12647011) B12647011
theorem B2772491 : Blo 1847625 2772491 := bstep (se 1 (by rfl) ⟨2079368, by rfl⟩ : syracuseStep 2772491 = 4158737) B4158737
theorem B2772503 : Blo 1847625 2772503 := bstep (se 1 (by rfl) ⟨2079377, by rfl⟩ : syracuseStep 2772503 = 4158755) B4158755
theorem B2633239 : Blo 1847625 2633239 := bstep (se 1 (by rfl) ⟨1974929, by rfl⟩ : syracuseStep 2633239 = 3949859) B3949859
theorem B2960921 : Blo 1847625 2960921 := bstep (se 2 (by rfl) ⟨1110345, by rfl⟩ : syracuseStep 2960921 = 2220691) B2220691
theorem B13332043 : Blo 1847625 13332043 := bstep (se 1 (by rfl) ⟨9999032, by rfl⟩ : syracuseStep 13332043 = 19998065) B19998065
theorem B2772569 : Blo 1847625 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B6000221 : Blo 1847625 6000221 := bstep (se 3 (by rfl) ⟨1125041, by rfl⟩ : syracuseStep 6000221 = 2250083) B2250083
theorem B2772683 : Blo 1847625 2772683 := bstep (se 1 (by rfl) ⟨2079512, by rfl⟩ : syracuseStep 2772683 = 4159025) B4159025
theorem B2772695 : Blo 1847625 2772695 := bstep (se 1 (by rfl) ⟨2079521, by rfl⟩ : syracuseStep 2772695 = 4159043) B4159043
theorem B3329753 : Blo 1847625 3329753 := bstep (se 2 (by rfl) ⟨1248657, by rfl⟩ : syracuseStep 3329753 = 2497315) B2497315
theorem B6237917 : Blo 1847625 6237917 := bstep (se 3 (by rfl) ⟨1169609, by rfl⟩ : syracuseStep 6237917 = 2339219) B2339219
theorem B4157171 : Blo 1847625 4157171 := bstep (se 1 (by rfl) ⟨3117878, by rfl⟩ : syracuseStep 4157171 = 6235757) B6235757
theorem B2338571 : Blo 1847625 2338571 := bstep (se 1 (by rfl) ⟨1753928, by rfl⟩ : syracuseStep 2338571 = 3507857) B3507857
theorem B4157207 : Blo 1847625 4157207 := bstep (se 1 (by rfl) ⟨3117905, by rfl⟩ : syracuseStep 4157207 = 6235811) B6235811
theorem B2772761 : Blo 1847625 2772761 := bstep (se 2 (by rfl) ⟨1039785, by rfl⟩ : syracuseStep 2772761 = 2079571) B2079571
theorem B3510067 : Blo 1847625 3510067 := bstep (se 1 (by rfl) ⟨2632550, by rfl⟩ : syracuseStep 3510067 = 5265101) B5265101
theorem B4681547 : Blo 1847625 4681547 := bstep (se 1 (by rfl) ⟨3511160, by rfl⟩ : syracuseStep 4681547 = 7022321) B7022321
theorem B4214657 : Blo 1847625 4214657 := bstep (se 2 (by rfl) ⟨1580496, by rfl⟩ : syracuseStep 4214657 = 3160993) B3160993
theorem B2772875 : Blo 1847625 2772875 := bstep (se 1 (by rfl) ⟨2079656, by rfl⟩ : syracuseStep 2772875 = 4159313) B4159313
theorem B2772887 : Blo 1847625 2772887 := bstep (se 1 (by rfl) ⟨2079665, by rfl⟩ : syracuseStep 2772887 = 4159331) B4159331
theorem B4157387 : Blo 1847625 4157387 := bstep (se 1 (by rfl) ⟨3118040, by rfl⟩ : syracuseStep 4157387 = 6236081) B6236081
theorem B2772953 : Blo 1847625 2772953 := bstep (se 2 (by rfl) ⟨1039857, by rfl⟩ : syracuseStep 2772953 = 2079715) B2079715
theorem B4157441 : Blo 1847625 4157441 := bstep (se 2 (by rfl) ⟨1559040, by rfl⟩ : syracuseStep 4157441 = 3118081) B3118081
theorem B4272151 : Blo 1847625 4272151 := bstep (se 1 (by rfl) ⟨3204113, by rfl⟩ : syracuseStep 4272151 = 6408227) B6408227
theorem B2773067 : Blo 1847625 2773067 := bstep (se 1 (by rfl) ⟨2079800, by rfl⟩ : syracuseStep 2773067 = 4159601) B4159601
theorem B2773079 : Blo 1847625 2773079 := bstep (se 1 (by rfl) ⟨2079809, by rfl⟩ : syracuseStep 2773079 = 4159619) B4159619
theorem B23687261 : Blo 1847625 23687261 := bstep (se 3 (by rfl) ⟨4441361, by rfl⟩ : syracuseStep 23687261 = 8882723) B8882723
theorem B2773145 : Blo 1847625 2773145 := bstep (se 2 (by rfl) ⟨1039929, by rfl⟩ : syracuseStep 2773145 = 2079859) B2079859
theorem B4157657 : Blo 1847625 4157657 := bstep (se 2 (by rfl) ⟨1559121, by rfl⟩ : syracuseStep 4157657 = 3118243) B3118243
theorem B28471537 : Blo 1847625 28471537 := bstep (se 2 (by rfl) ⟨10676826, by rfl⟩ : syracuseStep 28471537 = 21353653) B21353653
theorem B3510515 : Blo 1847625 3510515 := bstep (se 1 (by rfl) ⟨2632886, by rfl⟩ : syracuseStep 3510515 = 5265773) B5265773
theorem B2773259 : Blo 1847625 2773259 := bstep (se 1 (by rfl) ⟨2079944, by rfl⟩ : syracuseStep 2773259 = 4159889) B4159889
theorem B2773271 : Blo 1847625 2773271 := bstep (se 1 (by rfl) ⟨2079953, by rfl⟩ : syracuseStep 2773271 = 4159907) B4159907
theorem B3510553 : Blo 1847625 3510553 := bstep (se 2 (by rfl) ⟨1316457, by rfl⟩ : syracuseStep 3510553 = 2632915) B2632915
theorem B4157747 : Blo 1847625 4157747 := bstep (se 1 (by rfl) ⟨3118310, by rfl⟩ : syracuseStep 4157747 = 6236621) B6236621
theorem B1847627 : Blo 1847625 1847627 := bstep (se 1 (by rfl) ⟨1385720, by rfl⟩ : syracuseStep 1847627 = 2771441) B2771441
theorem B1847639 : Blo 1847625 1847639 := bstep (se 1 (by rfl) ⟨1385729, by rfl⟩ : syracuseStep 1847639 = 2771459) B2771459
theorem B4157783 : Blo 1847625 4157783 := bstep (se 1 (by rfl) ⟨3118337, by rfl⟩ : syracuseStep 4157783 = 6236675) B6236675
theorem B2773337 : Blo 1847625 2773337 := bstep (se 2 (by rfl) ⟨1040001, by rfl⟩ : syracuseStep 2773337 = 2080003) B2080003
theorem B21057893 : Blo 1847625 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B1847659 : Blo 1847625 1847659 := bstep (se 1 (by rfl) ⟨1385744, by rfl⟩ : syracuseStep 1847659 = 2771489) B2771489
theorem B3748211 : Blo 1847625 3748211 := bstep (se 1 (by rfl) ⟨2811158, by rfl⟩ : syracuseStep 3748211 = 5622317) B5622317
theorem B1847671 : Blo 1847625 1847671 := bstep (se 1 (by rfl) ⟨1385753, by rfl⟩ : syracuseStep 1847671 = 2771507) B2771507
theorem B1847691 : Blo 1847625 1847691 := bstep (se 1 (by rfl) ⟨1385768, by rfl⟩ : syracuseStep 1847691 = 2771537) B2771537
theorem B1847703 : Blo 1847625 1847703 := bstep (se 1 (by rfl) ⟨1385777, by rfl⟩ : syracuseStep 1847703 = 2771555) B2771555
theorem B1847723 : Blo 1847625 1847723 := bstep (se 1 (by rfl) ⟨1385792, by rfl⟩ : syracuseStep 1847723 = 2771585) B2771585
theorem B1847735 : Blo 1847625 1847735 := bstep (se 1 (by rfl) ⟨1385801, by rfl⟩ : syracuseStep 1847735 = 2771603) B2771603
theorem B1847755 : Blo 1847625 1847755 := bstep (se 1 (by rfl) ⟨1385816, by rfl⟩ : syracuseStep 1847755 = 2771633) B2771633
theorem B2339275 : Blo 1847625 2339275 := bstep (se 1 (by rfl) ⟨1754456, by rfl⟩ : syracuseStep 2339275 = 3508913) B3508913
theorem B2773451 : Blo 1847625 2773451 := bstep (se 1 (by rfl) ⟨2080088, by rfl⟩ : syracuseStep 2773451 = 4160177) B4160177
theorem B1847767 : Blo 1847625 1847767 := bstep (se 1 (by rfl) ⟨1385825, by rfl⟩ : syracuseStep 1847767 = 2771651) B2771651
theorem B2773463 : Blo 1847625 2773463 := bstep (se 1 (by rfl) ⟨2080097, by rfl⟩ : syracuseStep 2773463 = 4160195) B4160195
theorem B59986403 : Blo 1847625 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B1847787 : Blo 1847625 1847787 := bstep (se 1 (by rfl) ⟨1385840, by rfl⟩ : syracuseStep 1847787 = 2771681) B2771681
theorem B1847799 : Blo 1847625 1847799 := bstep (se 1 (by rfl) ⟨1385849, by rfl⟩ : syracuseStep 1847799 = 2771699) B2771699
theorem B1847819 : Blo 1847625 1847819 := bstep (se 1 (by rfl) ⟨1385864, by rfl⟩ : syracuseStep 1847819 = 2771729) B2771729
theorem B4157963 : Blo 1847625 4157963 := bstep (se 1 (by rfl) ⟨3118472, by rfl⟩ : syracuseStep 4157963 = 6236945) B6236945
theorem B1847831 : Blo 1847625 1847831 := bstep (se 1 (by rfl) ⟨1385873, by rfl⟩ : syracuseStep 1847831 = 2771747) B2771747
theorem B2773529 : Blo 1847625 2773529 := bstep (se 2 (by rfl) ⟨1040073, by rfl⟩ : syracuseStep 2773529 = 2080147) B2080147
theorem B1847851 : Blo 1847625 1847851 := bstep (se 1 (by rfl) ⟨1385888, by rfl⟩ : syracuseStep 1847851 = 2771777) B2771777
theorem B1847863 : Blo 1847625 1847863 := bstep (se 1 (by rfl) ⟨1385897, by rfl⟩ : syracuseStep 1847863 = 2771795) B2771795
theorem B4158017 : Blo 1847625 4158017 := bstep (se 2 (by rfl) ⟨1559256, by rfl⟩ : syracuseStep 4158017 = 3118513) B3118513
theorem B1847883 : Blo 1847625 1847883 := bstep (se 1 (by rfl) ⟨1385912, by rfl⟩ : syracuseStep 1847883 = 2771825) B2771825
theorem B1847895 : Blo 1847625 1847895 := bstep (se 1 (by rfl) ⟨1385921, by rfl⟩ : syracuseStep 1847895 = 2771843) B2771843
theorem B1847915 : Blo 1847625 1847915 := bstep (se 1 (by rfl) ⟨1385936, by rfl⟩ : syracuseStep 1847915 = 2771873) B2771873
theorem B1847927 : Blo 1847625 1847927 := bstep (se 1 (by rfl) ⟨1385945, by rfl⟩ : syracuseStep 1847927 = 2771891) B2771891
theorem B1847947 : Blo 1847625 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B2773643 : Blo 1847625 2773643 := bstep (se 1 (by rfl) ⟨2080232, by rfl⟩ : syracuseStep 2773643 = 4160465) B4160465
theorem B1847959 : Blo 1847625 1847959 := bstep (se 1 (by rfl) ⟨1385969, by rfl⟩ : syracuseStep 1847959 = 2771939) B2771939
theorem B2773655 : Blo 1847625 2773655 := bstep (se 1 (by rfl) ⟨2080241, by rfl⟩ : syracuseStep 2773655 = 4160483) B4160483
theorem B1847979 : Blo 1847625 1847979 := bstep (se 1 (by rfl) ⟨1385984, by rfl⟩ : syracuseStep 1847979 = 2771969) B2771969
theorem B1847991 : Blo 1847625 1847991 := bstep (se 1 (by rfl) ⟨1385993, by rfl⟩ : syracuseStep 1847991 = 2771987) B2771987
theorem B1848011 : Blo 1847625 1848011 := bstep (se 1 (by rfl) ⟨1386008, by rfl⟩ : syracuseStep 1848011 = 2772017) B2772017
theorem B1848023 : Blo 1847625 1848023 := bstep (se 1 (by rfl) ⟨1386017, by rfl⟩ : syracuseStep 1848023 = 2772035) B2772035
theorem B2339543 : Blo 1847625 2339543 := bstep (se 1 (by rfl) ⟨1754657, by rfl⟩ : syracuseStep 2339543 = 3509315) B3509315
theorem B2773721 : Blo 1847625 2773721 := bstep (se 2 (by rfl) ⟨1040145, by rfl⟩ : syracuseStep 2773721 = 2080291) B2080291
theorem B3511001 : Blo 1847625 3511001 := bstep (se 2 (by rfl) ⟨1316625, by rfl⟩ : syracuseStep 3511001 = 2633251) B2633251
theorem B1848043 : Blo 1847625 1848043 := bstep (se 1 (by rfl) ⟨1386032, by rfl⟩ : syracuseStep 1848043 = 2772065) B2772065
theorem B1848055 : Blo 1847625 1848055 := bstep (se 1 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 1848055 = 2772083) B2772083
theorem B1848075 : Blo 1847625 1848075 := bstep (se 1 (by rfl) ⟨1386056, by rfl⟩ : syracuseStep 1848075 = 2772113) B2772113
theorem B7705361 : Blo 1847625 7705361 := bstep (se 2 (by rfl) ⟨2889510, by rfl⟩ : syracuseStep 7705361 = 5779021) B5779021
theorem B1848087 : Blo 1847625 1848087 := bstep (se 1 (by rfl) ⟨1386065, by rfl⟩ : syracuseStep 1848087 = 2772131) B2772131
theorem B4158233 : Blo 1847625 4158233 := bstep (se 2 (by rfl) ⟨1559337, by rfl⟩ : syracuseStep 4158233 = 3118675) B3118675
theorem B1848107 : Blo 1847625 1848107 := bstep (se 1 (by rfl) ⟨1386080, by rfl⟩ : syracuseStep 1848107 = 2772161) B2772161
theorem B1848119 : Blo 1847625 1848119 := bstep (se 1 (by rfl) ⟨1386089, by rfl⟩ : syracuseStep 1848119 = 2772179) B2772179
theorem B3117899 : Blo 1847625 3117899 := bstep (se 1 (by rfl) ⟨2338424, by rfl⟩ : syracuseStep 3117899 = 4676849) B4676849
theorem B1848139 : Blo 1847625 1848139 := bstep (se 1 (by rfl) ⟨1386104, by rfl⟩ : syracuseStep 1848139 = 2772209) B2772209
theorem B6239051 : Blo 1847625 6239051 := bstep (se 1 (by rfl) ⟨4679288, by rfl⟩ : syracuseStep 6239051 = 9358577) B9358577
theorem B2773835 : Blo 1847625 2773835 := bstep (se 1 (by rfl) ⟨2080376, by rfl⟩ : syracuseStep 2773835 = 4160753) B4160753
theorem B1848151 : Blo 1847625 1848151 := bstep (se 1 (by rfl) ⟨1386113, by rfl⟩ : syracuseStep 1848151 = 2772227) B2772227
theorem B2773847 : Blo 1847625 2773847 := bstep (se 1 (by rfl) ⟨2080385, by rfl⟩ : syracuseStep 2773847 = 4160771) B4160771
theorem B1848171 : Blo 1847625 1848171 := bstep (se 1 (by rfl) ⟨1386128, by rfl⟩ : syracuseStep 1848171 = 2772257) B2772257
theorem B4158323 : Blo 1847625 4158323 := bstep (se 1 (by rfl) ⟨3118742, by rfl⟩ : syracuseStep 4158323 = 6237485) B6237485
theorem B1848183 : Blo 1847625 1848183 := bstep (se 1 (by rfl) ⟨1386137, by rfl⟩ : syracuseStep 1848183 = 2772275) B2772275
theorem B1848203 : Blo 1847625 1848203 := bstep (se 1 (by rfl) ⟨1386152, by rfl⟩ : syracuseStep 1848203 = 2772305) B2772305
theorem B4158359 : Blo 1847625 4158359 := bstep (se 1 (by rfl) ⟨3118769, by rfl⟩ : syracuseStep 4158359 = 6237539) B6237539
theorem B1848215 : Blo 1847625 1848215 := bstep (se 1 (by rfl) ⟨1386161, by rfl⟩ : syracuseStep 1848215 = 2772323) B2772323
theorem B2773913 : Blo 1847625 2773913 := bstep (se 2 (by rfl) ⟨1040217, by rfl⟩ : syracuseStep 2773913 = 2080435) B2080435
theorem B1848235 : Blo 1847625 1848235 := bstep (se 1 (by rfl) ⟨1386176, by rfl⟩ : syracuseStep 1848235 = 2772353) B2772353
theorem B1848247 : Blo 1847625 1848247 := bstep (se 1 (by rfl) ⟨1386185, by rfl⟩ : syracuseStep 1848247 = 2772371) B2772371
theorem B3118027 : Blo 1847625 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B1848267 : Blo 1847625 1848267 := bstep (se 1 (by rfl) ⟨1386200, by rfl⟩ : syracuseStep 1848267 = 2772401) B2772401
theorem B1848279 : Blo 1847625 1848279 := bstep (se 1 (by rfl) ⟨1386209, by rfl⟩ : syracuseStep 1848279 = 2772419) B2772419
theorem B1848299 : Blo 1847625 1848299 := bstep (se 1 (by rfl) ⟨1386224, by rfl⟩ : syracuseStep 1848299 = 2772449) B2772449
theorem B1848311 : Blo 1847625 1848311 := bstep (se 1 (by rfl) ⟨1386233, by rfl⟩ : syracuseStep 1848311 = 2772467) B2772467
theorem B7017475 : Blo 1847625 7017475 := bstep (se 1 (by rfl) ⟨5263106, by rfl⟩ : syracuseStep 7017475 = 10526213) B10526213
theorem B1848331 : Blo 1847625 1848331 := bstep (se 1 (by rfl) ⟨1386248, by rfl⟩ : syracuseStep 1848331 = 2772497) B2772497
theorem B2774027 : Blo 1847625 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B1848343 : Blo 1847625 1848343 := bstep (se 1 (by rfl) ⟨1386257, by rfl⟩ : syracuseStep 1848343 = 2772515) B2772515
theorem B2774039 : Blo 1847625 2774039 := bstep (se 1 (by rfl) ⟨2080529, by rfl⟩ : syracuseStep 2774039 = 4161059) B4161059
theorem B1848363 : Blo 1847625 1848363 := bstep (se 1 (by rfl) ⟨1386272, by rfl⟩ : syracuseStep 1848363 = 2772545) B2772545
theorem B1848375 : Blo 1847625 1848375 := bstep (se 1 (by rfl) ⟨1386281, by rfl⟩ : syracuseStep 1848375 = 2772563) B2772563
theorem B34174021 : Blo 1847625 34174021 := bstep (se 4 (by rfl) ⟨3203814, by rfl⟩ : syracuseStep 34174021 = 6407629) B6407629
theorem B4158539 : Blo 1847625 4158539 := bstep (se 1 (by rfl) ⟨3118904, by rfl⟩ : syracuseStep 4158539 = 6237809) B6237809
theorem B1848395 : Blo 1847625 1848395 := bstep (se 1 (by rfl) ⟨1386296, by rfl⟩ : syracuseStep 1848395 = 2772593) B2772593
theorem B1848407 : Blo 1847625 1848407 := bstep (se 1 (by rfl) ⟨1386305, by rfl⟩ : syracuseStep 1848407 = 2772611) B2772611
theorem B3118169 : Blo 1847625 3118169 := bstep (se 2 (by rfl) ⟨1169313, by rfl⟩ : syracuseStep 3118169 = 2338627) B2338627
theorem B6239321 : Blo 1847625 6239321 := bstep (se 2 (by rfl) ⟨2339745, by rfl⟩ : syracuseStep 6239321 = 4679491) B4679491
theorem B2774105 : Blo 1847625 2774105 := bstep (se 2 (by rfl) ⟨1040289, by rfl⟩ : syracuseStep 2774105 = 2080579) B2080579
theorem B14038109 : Blo 1847625 14038109 := bstep (se 3 (by rfl) ⟨2632145, by rfl⟩ : syracuseStep 14038109 = 5264291) B5264291
theorem B1848427 : Blo 1847625 1848427 := bstep (se 1 (by rfl) ⟨1386320, by rfl⟩ : syracuseStep 1848427 = 2772641) B2772641
theorem B1848439 : Blo 1847625 1848439 := bstep (se 1 (by rfl) ⟨1386329, by rfl⟩ : syracuseStep 1848439 = 2772659) B2772659
theorem B4158593 : Blo 1847625 4158593 := bstep (se 2 (by rfl) ⟨1559472, by rfl⟩ : syracuseStep 4158593 = 3118945) B3118945
theorem B1848459 : Blo 1847625 1848459 := bstep (se 1 (by rfl) ⟨1386344, by rfl⟩ : syracuseStep 1848459 = 2772689) B2772689
theorem B1848471 : Blo 1847625 1848471 := bstep (se 1 (by rfl) ⟨1386353, by rfl⟩ : syracuseStep 1848471 = 2772707) B2772707
theorem B1848491 : Blo 1847625 1848491 := bstep (se 1 (by rfl) ⟨1386368, by rfl⟩ : syracuseStep 1848491 = 2772737) B2772737
theorem B11400371 : Blo 1847625 11400371 := bstep (se 1 (by rfl) ⟨8550278, by rfl⟩ : syracuseStep 11400371 = 17100557) B17100557
theorem B1848503 : Blo 1847625 1848503 := bstep (se 1 (by rfl) ⟨1386377, by rfl⟩ : syracuseStep 1848503 = 2772755) B2772755
theorem B1848523 : Blo 1847625 1848523 := bstep (se 1 (by rfl) ⟨1386392, by rfl⟩ : syracuseStep 1848523 = 2772785) B2772785
theorem B2774219 : Blo 1847625 2774219 := bstep (se 1 (by rfl) ⟨2080664, by rfl⟩ : syracuseStep 2774219 = 4161329) B4161329
theorem B1848535 : Blo 1847625 1848535 := bstep (se 1 (by rfl) ⟨1386401, by rfl⟩ : syracuseStep 1848535 = 2772803) B2772803
theorem B3118297 : Blo 1847625 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B2774231 : Blo 1847625 2774231 := bstep (se 1 (by rfl) ⟨2080673, by rfl⟩ : syracuseStep 2774231 = 4161347) B4161347
theorem B1848555 : Blo 1847625 1848555 := bstep (se 1 (by rfl) ⟨1386416, by rfl⟩ : syracuseStep 1848555 = 2772833) B2772833
theorem B1848567 : Blo 1847625 1848567 := bstep (se 1 (by rfl) ⟨1386425, by rfl⟩ : syracuseStep 1848567 = 2772851) B2772851
theorem B1848587 : Blo 1847625 1848587 := bstep (se 1 (by rfl) ⟨1386440, by rfl⟩ : syracuseStep 1848587 = 2772881) B2772881
theorem B1848599 : Blo 1847625 1848599 := bstep (se 1 (by rfl) ⟨1386449, by rfl⟩ : syracuseStep 1848599 = 2772899) B2772899
theorem B2774297 : Blo 1847625 2774297 := bstep (se 2 (by rfl) ⟨1040361, by rfl⟩ : syracuseStep 2774297 = 2080723) B2080723
theorem B1848619 : Blo 1847625 1848619 := bstep (se 1 (by rfl) ⟨1386464, by rfl⟩ : syracuseStep 1848619 = 2772929) B2772929
theorem B7017779 : Blo 1847625 7017779 := bstep (se 1 (by rfl) ⟨5263334, by rfl⟩ : syracuseStep 7017779 = 10526669) B10526669
theorem B1848631 : Blo 1847625 1848631 := bstep (se 1 (by rfl) ⟨1386473, by rfl⟩ : syracuseStep 1848631 = 2772947) B2772947
theorem B1848651 : Blo 1847625 1848651 := bstep (se 1 (by rfl) ⟨1386488, by rfl⟩ : syracuseStep 1848651 = 2772977) B2772977
theorem B1848663 : Blo 1847625 1848663 := bstep (se 1 (by rfl) ⟨1386497, by rfl⟩ : syracuseStep 1848663 = 2772995) B2772995
theorem B4158809 : Blo 1847625 4158809 := bstep (se 2 (by rfl) ⟨1559553, by rfl⟩ : syracuseStep 4158809 = 3119107) B3119107
theorem B6665561 : Blo 1847625 6665561 := bstep (se 2 (by rfl) ⟨2499585, by rfl⟩ : syracuseStep 6665561 = 4999171) B4999171
theorem B10524005 : Blo 1847625 10524005 := bstep (se 4 (by rfl) ⟨986625, by rfl⟩ : syracuseStep 10524005 = 1973251) B1973251
theorem B26645861 : Blo 1847625 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B1848683 : Blo 1847625 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B1848695 : Blo 1847625 1848695 := bstep (se 1 (by rfl) ⟨1386521, by rfl⟩ : syracuseStep 1848695 = 2773043) B2773043
theorem B10532227 : Blo 1847625 10532227 := bstep (se 1 (by rfl) ⟨7899170, by rfl⟩ : syracuseStep 10532227 = 15798341) B15798341
theorem B1848715 : Blo 1847625 1848715 := bstep (se 1 (by rfl) ⟨1386536, by rfl⟩ : syracuseStep 1848715 = 2773073) B2773073
theorem B2774411 : Blo 1847625 2774411 := bstep (se 1 (by rfl) ⟨2080808, by rfl⟩ : syracuseStep 2774411 = 4161617) B4161617
theorem B1848727 : Blo 1847625 1848727 := bstep (se 1 (by rfl) ⟨1386545, by rfl⟩ : syracuseStep 1848727 = 2773091) B2773091
theorem B2340247 : Blo 1847625 2340247 := bstep (se 1 (by rfl) ⟨1755185, by rfl⟩ : syracuseStep 2340247 = 3510371) B3510371
theorem B2774423 : Blo 1847625 2774423 := bstep (se 1 (by rfl) ⟨2080817, by rfl⟩ : syracuseStep 2774423 = 4161635) B4161635
theorem B1848747 : Blo 1847625 1848747 := bstep (se 1 (by rfl) ⟨1386560, by rfl⟩ : syracuseStep 1848747 = 2773121) B2773121
theorem B4158899 : Blo 1847625 4158899 := bstep (se 1 (by rfl) ⟨3119174, by rfl⟩ : syracuseStep 4158899 = 6238349) B6238349
theorem B1848759 : Blo 1847625 1848759 := bstep (se 1 (by rfl) ⟨1386569, by rfl⟩ : syracuseStep 1848759 = 2773139) B2773139
theorem B1848779 : Blo 1847625 1848779 := bstep (se 1 (by rfl) ⟨1386584, by rfl⟩ : syracuseStep 1848779 = 2773169) B2773169
theorem B4158935 : Blo 1847625 4158935 := bstep (se 1 (by rfl) ⟨3119201, by rfl⟩ : syracuseStep 4158935 = 6238403) B6238403
theorem B1848791 : Blo 1847625 1848791 := bstep (se 1 (by rfl) ⟨1386593, by rfl⟩ : syracuseStep 1848791 = 2773187) B2773187
theorem B1848811 : Blo 1847625 1848811 := bstep (se 1 (by rfl) ⟨1386608, by rfl⟩ : syracuseStep 1848811 = 2773217) B2773217
theorem B1848823 : Blo 1847625 1848823 := bstep (se 1 (by rfl) ⟨1386617, by rfl⟩ : syracuseStep 1848823 = 2773235) B2773235
theorem B1848843 : Blo 1847625 1848843 := bstep (se 1 (by rfl) ⟨1386632, by rfl⟩ : syracuseStep 1848843 = 2773265) B2773265
theorem B1848855 : Blo 1847625 1848855 := bstep (se 1 (by rfl) ⟨1386641, by rfl⟩ : syracuseStep 1848855 = 2773283) B2773283
theorem B1848875 : Blo 1847625 1848875 := bstep (se 1 (by rfl) ⟨1386656, by rfl⟩ : syracuseStep 1848875 = 2773313) B2773313
theorem B1848887 : Blo 1847625 1848887 := bstep (se 1 (by rfl) ⟨1386665, by rfl⟩ : syracuseStep 1848887 = 2773331) B2773331
theorem B1848907 : Blo 1847625 1848907 := bstep (se 1 (by rfl) ⟨1386680, by rfl⟩ : syracuseStep 1848907 = 2773361) B2773361
theorem B1848919 : Blo 1847625 1848919 := bstep (se 1 (by rfl) ⟨1386689, by rfl⟩ : syracuseStep 1848919 = 2773379) B2773379
theorem B1848939 : Blo 1847625 1848939 := bstep (se 1 (by rfl) ⟨1386704, by rfl⟩ : syracuseStep 1848939 = 2773409) B2773409
theorem B1848951 : Blo 1847625 1848951 := bstep (se 1 (by rfl) ⟨1386713, by rfl⟩ : syracuseStep 1848951 = 2773427) B2773427
theorem B4159115 : Blo 1847625 4159115 := bstep (se 1 (by rfl) ⟨3119336, by rfl⟩ : syracuseStep 4159115 = 6238673) B6238673
theorem B1848971 : Blo 1847625 1848971 := bstep (se 1 (by rfl) ⟨1386728, by rfl⟩ : syracuseStep 1848971 = 2773457) B2773457
theorem B10671767 : Blo 1847625 10671767 := bstep (se 1 (by rfl) ⟨8003825, by rfl⟩ : syracuseStep 10671767 = 16007651) B16007651
theorem B1848983 : Blo 1847625 1848983 := bstep (se 1 (by rfl) ⟨1386737, by rfl⟩ : syracuseStep 1848983 = 2773475) B2773475
theorem B1849003 : Blo 1847625 1849003 := bstep (se 1 (by rfl) ⟨1386752, by rfl⟩ : syracuseStep 1849003 = 2773505) B2773505
theorem B1849015 : Blo 1847625 1849015 := bstep (se 1 (by rfl) ⟨1386761, by rfl⟩ : syracuseStep 1849015 = 2773523) B2773523
theorem B4159169 : Blo 1847625 4159169 := bstep (se 2 (by rfl) ⟨1559688, by rfl⟩ : syracuseStep 4159169 = 3119377) B3119377
theorem B1849035 : Blo 1847625 1849035 := bstep (se 1 (by rfl) ⟨1386776, by rfl⟩ : syracuseStep 1849035 = 2773553) B2773553
theorem B21337805 : Blo 1847625 21337805 := bstep (se 3 (by rfl) ⟨4000838, by rfl⟩ : syracuseStep 21337805 = 8001677) B8001677
theorem B1849047 : Blo 1847625 1849047 := bstep (se 1 (by rfl) ⟨1386785, by rfl⟩ : syracuseStep 1849047 = 2773571) B2773571
theorem B1873643 : Blo 1847625 1873643 := bstep (se 1 (by rfl) ⟨1405232, by rfl⟩ : syracuseStep 1873643 = 2810465) B2810465
theorem B1849067 : Blo 1847625 1849067 := bstep (se 1 (by rfl) ⟨1386800, by rfl⟩ : syracuseStep 1849067 = 2773601) B2773601
theorem B1849079 : Blo 1847625 1849079 := bstep (se 1 (by rfl) ⟨1386809, by rfl⟩ : syracuseStep 1849079 = 2773619) B2773619
theorem B1849099 : Blo 1847625 1849099 := bstep (se 1 (by rfl) ⟨1386824, by rfl⟩ : syracuseStep 1849099 = 2773649) B2773649
theorem B9361169 : Blo 1847625 9361169 := bstep (se 2 (by rfl) ⟨3510438, by rfl⟩ : syracuseStep 9361169 = 7020877) B7020877
theorem B3118871 : Blo 1847625 3118871 := bstep (se 1 (by rfl) ⟨2339153, by rfl⟩ : syracuseStep 3118871 = 4678307) B4678307
theorem B6240023 : Blo 1847625 6240023 := bstep (se 1 (by rfl) ⟨4680017, by rfl⟩ : syracuseStep 6240023 = 9360035) B9360035
theorem B1849111 : Blo 1847625 1849111 := bstep (se 1 (by rfl) ⟨1386833, by rfl⟩ : syracuseStep 1849111 = 2773667) B2773667
theorem B1849131 : Blo 1847625 1849131 := bstep (se 1 (by rfl) ⟨1386848, by rfl⟩ : syracuseStep 1849131 = 2773697) B2773697
theorem B4216627 : Blo 1847625 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B1849143 : Blo 1847625 1849143 := bstep (se 1 (by rfl) ⟨1386857, by rfl⟩ : syracuseStep 1849143 = 2773715) B2773715
theorem B6002507 : Blo 1847625 6002507 := bstep (se 1 (by rfl) ⟨4501880, by rfl⟩ : syracuseStep 6002507 = 9003761) B9003761
theorem B1849163 : Blo 1847625 1849163 := bstep (se 1 (by rfl) ⟨1386872, by rfl⟩ : syracuseStep 1849163 = 2773745) B2773745
theorem B1849175 : Blo 1847625 1849175 := bstep (se 1 (by rfl) ⟨1386881, by rfl⟩ : syracuseStep 1849175 = 2773763) B2773763
theorem B33724259 : Blo 1847625 33724259 := bstep (se 1 (by rfl) ⟨25293194, by rfl⟩ : syracuseStep 33724259 = 50586389) B50586389
theorem B1849195 : Blo 1847625 1849195 := bstep (se 1 (by rfl) ⟨1386896, by rfl⟩ : syracuseStep 1849195 = 2773793) B2773793
theorem B1849207 : Blo 1847625 1849207 := bstep (se 1 (by rfl) ⟨1386905, by rfl⟩ : syracuseStep 1849207 = 2773811) B2773811
theorem B1849227 : Blo 1847625 1849227 := bstep (se 1 (by rfl) ⟨1386920, by rfl⟩ : syracuseStep 1849227 = 2773841) B2773841
theorem B3946391 : Blo 1847625 3946391 := bstep (se 1 (by rfl) ⟨2959793, by rfl⟩ : syracuseStep 3946391 = 5919587) B5919587
theorem B3118999 : Blo 1847625 3118999 := bstep (se 1 (by rfl) ⟨2339249, by rfl⟩ : syracuseStep 3118999 = 4678499) B4678499
theorem B4159385 : Blo 1847625 4159385 := bstep (se 2 (by rfl) ⟨1559769, by rfl⟩ : syracuseStep 4159385 = 3119539) B3119539
theorem B1849239 : Blo 1847625 1849239 := bstep (se 1 (by rfl) ⟨1386929, by rfl⟩ : syracuseStep 1849239 = 2773859) B2773859
theorem B2078635 : Blo 1847625 2078635 := bstep (se 1 (by rfl) ⟨1558976, by rfl⟩ : syracuseStep 2078635 = 3117953) B3117953
theorem B1849259 : Blo 1847625 1849259 := bstep (se 1 (by rfl) ⟨1386944, by rfl⟩ : syracuseStep 1849259 = 2773889) B2773889
theorem B9361331 : Blo 1847625 9361331 := bstep (se 1 (by rfl) ⟨7020998, by rfl⟩ : syracuseStep 9361331 = 14041997) B14041997
theorem B1849271 : Blo 1847625 1849271 := bstep (se 1 (by rfl) ⟨1386953, by rfl⟩ : syracuseStep 1849271 = 2773907) B2773907
theorem B7018433 : Blo 1847625 7018433 := bstep (se 2 (by rfl) ⟨2631912, by rfl⟩ : syracuseStep 7018433 = 5263825) B5263825
theorem B5920715 : Blo 1847625 5920715 := bstep (se 1 (by rfl) ⟨4440536, by rfl⟩ : syracuseStep 5920715 = 8881073) B8881073
theorem B1849291 : Blo 1847625 1849291 := bstep (se 1 (by rfl) ⟨1386968, by rfl⟩ : syracuseStep 1849291 = 2773937) B2773937
theorem B1849303 : Blo 1847625 1849303 := bstep (se 1 (by rfl) ⟨1386977, by rfl⟩ : syracuseStep 1849303 = 2773955) B2773955
theorem B1849323 : Blo 1847625 1849323 := bstep (se 1 (by rfl) ⟨1386992, by rfl⟩ : syracuseStep 1849323 = 2773985) B2773985
theorem B4159475 : Blo 1847625 4159475 := bstep (se 1 (by rfl) ⟨3119606, by rfl⟩ : syracuseStep 4159475 = 6239213) B6239213
theorem B1849335 : Blo 1847625 1849335 := bstep (se 1 (by rfl) ⟨1387001, by rfl⟩ : syracuseStep 1849335 = 2774003) B2774003
theorem B1849355 : Blo 1847625 1849355 := bstep (se 1 (by rfl) ⟨1387016, by rfl⟩ : syracuseStep 1849355 = 2774033) B2774033
theorem B2078743 : Blo 1847625 2078743 := bstep (se 1 (by rfl) ⟨1559057, by rfl⟩ : syracuseStep 2078743 = 3118115) B3118115
theorem B4159511 : Blo 1847625 4159511 := bstep (se 1 (by rfl) ⟨3119633, by rfl⟩ : syracuseStep 4159511 = 6239267) B6239267
theorem B5265431 : Blo 1847625 5265431 := bstep (se 1 (by rfl) ⟨3949073, by rfl⟩ : syracuseStep 5265431 = 7898147) B7898147
theorem B1849367 : Blo 1847625 1849367 := bstep (se 1 (by rfl) ⟨1387025, by rfl⟩ : syracuseStep 1849367 = 2774051) B2774051
theorem B1849387 : Blo 1847625 1849387 := bstep (se 1 (by rfl) ⟨1387040, by rfl⟩ : syracuseStep 1849387 = 2774081) B2774081
theorem B1849399 : Blo 1847625 1849399 := bstep (se 1 (by rfl) ⟨1387049, by rfl⟩ : syracuseStep 1849399 = 2774099) B2774099
theorem B8001611 : Blo 1847625 8001611 := bstep (se 1 (by rfl) ⟨6001208, by rfl⟩ : syracuseStep 8001611 = 12002417) B12002417
theorem B1849419 : Blo 1847625 1849419 := bstep (se 1 (by rfl) ⟨1387064, by rfl⟩ : syracuseStep 1849419 = 2774129) B2774129
theorem B1849431 : Blo 1847625 1849431 := bstep (se 1 (by rfl) ⟨1387073, by rfl⟩ : syracuseStep 1849431 = 2774147) B2774147
theorem B1849451 : Blo 1847625 1849451 := bstep (se 1 (by rfl) ⟨1387088, by rfl⟩ : syracuseStep 1849451 = 2774177) B2774177
theorem B1849463 : Blo 1847625 1849463 := bstep (se 1 (by rfl) ⟨1387097, by rfl⟩ : syracuseStep 1849463 = 2774195) B2774195
theorem B1849483 : Blo 1847625 1849483 := bstep (se 1 (by rfl) ⟨1387112, by rfl⟩ : syracuseStep 1849483 = 2774225) B2774225
theorem B7895191 : Blo 1847625 7895191 := bstep (se 1 (by rfl) ⟨5921393, by rfl⟩ : syracuseStep 7895191 = 11842787) B11842787
theorem B1849495 : Blo 1847625 1849495 := bstep (se 1 (by rfl) ⟨1387121, by rfl⟩ : syracuseStep 1849495 = 2774243) B2774243
theorem B1849515 : Blo 1847625 1849515 := bstep (se 1 (by rfl) ⟨1387136, by rfl⟩ : syracuseStep 1849515 = 2774273) B2774273
theorem B1849527 : Blo 1847625 1849527 := bstep (se 1 (by rfl) ⟨1387145, by rfl⟩ : syracuseStep 1849527 = 2774291) B2774291
theorem B2078923 : Blo 1847625 2078923 := bstep (se 1 (by rfl) ⟨1559192, by rfl⟩ : syracuseStep 2078923 = 3118385) B3118385
theorem B4159691 : Blo 1847625 4159691 := bstep (se 1 (by rfl) ⟨3119768, by rfl⟩ : syracuseStep 4159691 = 6239537) B6239537
theorem B1849547 : Blo 1847625 1849547 := bstep (se 1 (by rfl) ⟨1387160, by rfl⟩ : syracuseStep 1849547 = 2774321) B2774321
theorem B1849559 : Blo 1847625 1849559 := bstep (se 1 (by rfl) ⟨1387169, by rfl⟩ : syracuseStep 1849559 = 2774339) B2774339
theorem B1849579 : Blo 1847625 1849579 := bstep (se 1 (by rfl) ⟨1387184, by rfl⟩ : syracuseStep 1849579 = 2774369) B2774369
theorem B1849591 : Blo 1847625 1849591 := bstep (se 1 (by rfl) ⟨1387193, by rfl⟩ : syracuseStep 1849591 = 2774387) B2774387
theorem B4159745 : Blo 1847625 4159745 := bstep (se 2 (by rfl) ⟨1559904, by rfl⟩ : syracuseStep 4159745 = 3119809) B3119809
theorem B1849611 : Blo 1847625 1849611 := bstep (se 1 (by rfl) ⟨1387208, by rfl⟩ : syracuseStep 1849611 = 2774417) B2774417
theorem B1849623 : Blo 1847625 1849623 := bstep (se 1 (by rfl) ⟨1387217, by rfl⟩ : syracuseStep 1849623 = 2774435) B2774435
theorem B6240563 : Blo 1847625 6240563 := bstep (se 1 (by rfl) ⟨4680422, by rfl⟩ : syracuseStep 6240563 = 9360845) B9360845
theorem B2079031 : Blo 1847625 2079031 := bstep (se 1 (by rfl) ⟨1559273, by rfl⟩ : syracuseStep 2079031 = 3118547) B3118547
theorem B10533185 : Blo 1847625 10533185 := bstep (se 2 (by rfl) ⟨3949944, by rfl⟩ : syracuseStep 10533185 = 7899889) B7899889
theorem B4159961 : Blo 1847625 4159961 := bstep (se 2 (by rfl) ⟨1559985, by rfl⟩ : syracuseStep 4159961 = 3119971) B3119971
theorem B2079211 : Blo 1847625 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B3119627 : Blo 1847625 3119627 := bstep (se 1 (by rfl) ⟨2339720, by rfl⟩ : syracuseStep 3119627 = 4679441) B4679441
theorem B14989859 : Blo 1847625 14989859 := bstep (se 1 (by rfl) ⟨11242394, by rfl⟩ : syracuseStep 14989859 = 22484789) B22484789
theorem B4160051 : Blo 1847625 4160051 := bstep (se 1 (by rfl) ⟨3120038, by rfl⟩ : syracuseStep 4160051 = 6240077) B6240077
theorem B6240833 : Blo 1847625 6240833 := bstep (se 2 (by rfl) ⟨2340312, by rfl⟩ : syracuseStep 6240833 = 4680625) B4680625
theorem B11557451 : Blo 1847625 11557451 := bstep (se 1 (by rfl) ⟨8668088, by rfl⟩ : syracuseStep 11557451 = 17336177) B17336177
theorem B2079319 : Blo 1847625 2079319 := bstep (se 1 (by rfl) ⟨1559489, by rfl⟩ : syracuseStep 2079319 = 3118979) B3118979
theorem B4160087 : Blo 1847625 4160087 := bstep (se 1 (by rfl) ⟨3120065, by rfl⟩ : syracuseStep 4160087 = 6240131) B6240131
theorem B3119755 : Blo 1847625 3119755 := bstep (se 1 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 3119755 = 4679633) B4679633
theorem B9353879 : Blo 1847625 9353879 := bstep (se 1 (by rfl) ⟨7015409, by rfl⟩ : syracuseStep 9353879 = 14030819) B14030819
theorem B4741811 : Blo 1847625 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B2079499 : Blo 1847625 2079499 := bstep (se 1 (by rfl) ⟨1559624, by rfl⟩ : syracuseStep 2079499 = 3119249) B3119249
theorem B4160267 : Blo 1847625 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B3119897 : Blo 1847625 3119897 := bstep (se 2 (by rfl) ⟨1169961, by rfl⟩ : syracuseStep 3119897 = 2339923) B2339923
theorem B4160321 : Blo 1847625 4160321 := bstep (se 2 (by rfl) ⟨1560120, by rfl⟩ : syracuseStep 4160321 = 3120241) B3120241
theorem B11844427 : Blo 1847625 11844427 := bstep (se 1 (by rfl) ⟨8883320, by rfl⟩ : syracuseStep 11844427 = 17766641) B17766641
theorem B2079607 : Blo 1847625 2079607 := bstep (se 1 (by rfl) ⟨1559705, by rfl⟩ : syracuseStep 2079607 = 3119411) B3119411
theorem B3120025 : Blo 1847625 3120025 := bstep (se 2 (by rfl) ⟨1170009, by rfl⟩ : syracuseStep 3120025 = 2340019) B2340019
theorem B67476401 : Blo 1847625 67476401 := bstep (se 2 (by rfl) ⟨25303650, by rfl⟩ : syracuseStep 67476401 = 50607301) B50607301
theorem B66706355 : Blo 1847625 66706355 := bstep (se 1 (by rfl) ⟨50029766, by rfl⟩ : syracuseStep 66706355 = 100059533) B100059533
theorem B2497483 : Blo 1847625 2497483 := bstep (se 1 (by rfl) ⟨1873112, by rfl⟩ : syracuseStep 2497483 = 3746225) B3746225
theorem B3947467 : Blo 1847625 3947467 := bstep (se 1 (by rfl) ⟨2960600, by rfl⟩ : syracuseStep 3947467 = 5921201) B5921201
theorem B4160537 : Blo 1847625 4160537 := bstep (se 2 (by rfl) ⟨1560201, by rfl⟩ : syracuseStep 4160537 = 3120403) B3120403
theorem B2079787 : Blo 1847625 2079787 := bstep (se 1 (by rfl) ⟨1559840, by rfl⟩ : syracuseStep 2079787 = 3119681) B3119681
theorem B15793217 : Blo 1847625 15793217 := bstep (se 2 (by rfl) ⟨5922456, by rfl⟩ : syracuseStep 15793217 = 11844913) B11844913
theorem B5135425 : Blo 1847625 5135425 := bstep (se 2 (by rfl) ⟨1925784, by rfl⟩ : syracuseStep 5135425 = 3851569) B3851569
theorem B24009821 : Blo 1847625 24009821 := bstep (se 3 (by rfl) ⟨4501841, by rfl⟩ : syracuseStep 24009821 = 9003683) B9003683
theorem B6241373 : Blo 1847625 6241373 := bstep (se 3 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 6241373 = 2340515) B2340515
theorem B4160627 : Blo 1847625 4160627 := bstep (se 1 (by rfl) ⟨3120470, by rfl⟩ : syracuseStep 4160627 = 6240941) B6240941
theorem B2079895 : Blo 1847625 2079895 := bstep (se 1 (by rfl) ⟨1559921, by rfl⟩ : syracuseStep 2079895 = 3119843) B3119843
theorem B4160663 : Blo 1847625 4160663 := bstep (se 1 (by rfl) ⟨3120497, by rfl⟩ : syracuseStep 4160663 = 6240995) B6240995
theorem B14998679 : Blo 1847625 14998679 := bstep (se 1 (by rfl) ⟨11249009, by rfl⟩ : syracuseStep 14998679 = 22498019) B22498019
theorem B7019693 : Blo 1847625 7019693 := bstep (se 3 (by rfl) ⟨1316192, by rfl⟩ : syracuseStep 7019693 = 2632385) B2632385
theorem B6659275 : Blo 1847625 6659275 := bstep (se 1 (by rfl) ⟨4994456, by rfl⟩ : syracuseStep 6659275 = 9988913) B9988913
theorem B7019723 : Blo 1847625 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B2849995 : Blo 1847625 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B2080075 : Blo 1847625 2080075 := bstep (se 1 (by rfl) ⟨1560056, by rfl⟩ : syracuseStep 2080075 = 3120113) B3120113
theorem B4160843 : Blo 1847625 4160843 := bstep (se 1 (by rfl) ⟨3120632, by rfl⟩ : syracuseStep 4160843 = 6241265) B6241265
theorem B4160897 : Blo 1847625 4160897 := bstep (se 2 (by rfl) ⟨1560336, by rfl⟩ : syracuseStep 4160897 = 3120673) B3120673
theorem B2080183 : Blo 1847625 2080183 := bstep (se 1 (by rfl) ⟨1560137, by rfl⟩ : syracuseStep 2080183 = 3120275) B3120275
theorem B3120599 : Blo 1847625 3120599 := bstep (se 1 (by rfl) ⟨2340449, by rfl⟩ : syracuseStep 3120599 = 4680899) B4680899
theorem B5922355 : Blo 1847625 5922355 := bstep (se 1 (by rfl) ⟨4441766, by rfl⟩ : syracuseStep 5922355 = 8883533) B8883533
theorem B31571531 : Blo 1847625 31571531 := bstep (se 1 (by rfl) ⟨23678648, by rfl⟩ : syracuseStep 31571531 = 47357297) B47357297
theorem B3120727 : Blo 1847625 3120727 := bstep (se 1 (by rfl) ⟨2340545, by rfl⟩ : syracuseStep 3120727 = 4681091) B4681091
theorem B4161113 : Blo 1847625 4161113 := bstep (se 2 (by rfl) ⟨1560417, by rfl⟩ : syracuseStep 4161113 = 3120835) B3120835
theorem B2080363 : Blo 1847625 2080363 := bstep (se 1 (by rfl) ⟨1560272, by rfl⟩ : syracuseStep 2080363 = 3120545) B3120545
theorem B11845271 : Blo 1847625 11845271 := bstep (se 1 (by rfl) ⟨8883953, by rfl⟩ : syracuseStep 11845271 = 17767907) B17767907
theorem B3948185 : Blo 1847625 3948185 := bstep (se 2 (by rfl) ⟨1480569, by rfl⟩ : syracuseStep 3948185 = 2961139) B2961139
theorem B4161203 : Blo 1847625 4161203 := bstep (se 1 (by rfl) ⟨3120902, by rfl⟩ : syracuseStep 4161203 = 6241805) B6241805
theorem B2080471 : Blo 1847625 2080471 := bstep (se 1 (by rfl) ⟨1560353, by rfl⟩ : syracuseStep 2080471 = 3120707) B3120707
theorem B4161239 : Blo 1847625 4161239 := bstep (se 1 (by rfl) ⟨3120929, by rfl⟩ : syracuseStep 4161239 = 6241859) B6241859
theorem B1974007 : Blo 1847625 1974007 := bstep (se 1 (by rfl) ⟨1480505, by rfl⟩ : syracuseStep 1974007 = 2961011) B2961011
theorem B9363275 : Blo 1847625 9363275 := bstep (se 1 (by rfl) ⟨7022456, by rfl⟩ : syracuseStep 9363275 = 14044913) B14044913
theorem B7020377 : Blo 1847625 7020377 := bstep (se 2 (by rfl) ⟨2632641, by rfl⟩ : syracuseStep 7020377 = 5265283) B5265283
theorem B2080651 : Blo 1847625 2080651 := bstep (se 1 (by rfl) ⟨1560488, by rfl⟩ : syracuseStep 2080651 = 3120977) B3120977
theorem B4161419 : Blo 1847625 4161419 := bstep (se 1 (by rfl) ⟨3121064, by rfl⟩ : syracuseStep 4161419 = 6242129) B6242129
theorem B4677527 : Blo 1847625 4677527 := bstep (se 1 (by rfl) ⟨3508145, by rfl⟩ : syracuseStep 4677527 = 7016291) B7016291
theorem B4161473 : Blo 1847625 4161473 := bstep (se 2 (by rfl) ⟨1560552, by rfl⟩ : syracuseStep 4161473 = 3121105) B3121105
theorem B17760217 : Blo 1847625 17760217 := bstep (se 2 (by rfl) ⟨6660081, by rfl⟩ : syracuseStep 17760217 = 13320163) B13320163
theorem B2080759 : Blo 1847625 2080759 := bstep (se 1 (by rfl) ⟨1560569, by rfl⟩ : syracuseStep 2080759 = 3121139) B3121139
theorem B10526921 : Blo 1847625 10526921 := bstep (se 2 (by rfl) ⟨3947595, by rfl⟩ : syracuseStep 10526921 = 7895191) B7895191
theorem B2498807 : Blo 1847625 2498807 := bstep (se 1 (by rfl) ⟨1874105, by rfl⟩ : syracuseStep 2498807 = 3748211) B3748211
theorem B37962049 : Blo 1847625 37962049 := bstep (se 2 (by rfl) ⟨14235768, by rfl⟩ : syracuseStep 37962049 = 28471537) B28471537
theorem B4678145 : Blo 1847625 4678145 := bstep (se 2 (by rfl) ⟨1754304, by rfl⟩ : syracuseStep 4678145 = 3508609) B3508609
theorem B5136907 : Blo 1847625 5136907 := bstep (se 1 (by rfl) ⟨3852680, by rfl⟩ : syracuseStep 5136907 = 7705361) B7705361
theorem B6324779 : Blo 1847625 6324779 := bstep (se 1 (by rfl) ⟨4743584, by rfl⟩ : syracuseStep 6324779 = 9487169) B9487169
theorem B17760833 : Blo 1847625 17760833 := bstep (se 2 (by rfl) ⟨6660312, by rfl⟩ : syracuseStep 17760833 = 13320625) B13320625
theorem B9356147 : Blo 1847625 9356147 := bstep (se 1 (by rfl) ⟨7017110, by rfl⟩ : syracuseStep 9356147 = 14034221) B14034221
theorem B5407607 : Blo 1847625 5407607 := bstep (se 1 (by rfl) ⟨4055705, by rfl⟩ : syracuseStep 5407607 = 8111411) B8111411
theorem B4678519 : Blo 1847625 4678519 := bstep (se 1 (by rfl) ⟨3508889, by rfl⟩ : syracuseStep 4678519 = 7017779) B7017779
theorem B3949715 : Blo 1847625 3949715 := bstep (se 1 (by rfl) ⟨2962286, by rfl⟩ : syracuseStep 3949715 = 5924573) B5924573
theorem B44967149 : Blo 1847625 44967149 := bstep (se 3 (by rfl) ⟨8431340, by rfl⟩ : syracuseStep 44967149 = 16862681) B16862681
theorem B2630927 : Blo 1847625 2630927 := bstep (se 1 (by rfl) ⟨1973195, by rfl⟩ : syracuseStep 2630927 = 3946391) B3946391
theorem B4678955 : Blo 1847625 4678955 := bstep (se 1 (by rfl) ⟨3509216, by rfl⟩ : syracuseStep 4678955 = 7018433) B7018433
theorem B9356633 : Blo 1847625 9356633 := bstep (se 2 (by rfl) ⟨3508737, by rfl⟩ : syracuseStep 9356633 = 7017475) B7017475
theorem B56935811 : Blo 1847625 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B5334407 : Blo 1847625 5334407 := bstep (se 1 (by rfl) ⟨4000805, by rfl⟩ : syracuseStep 5334407 = 8001611) B8001611
theorem B45565361 : Blo 1847625 45565361 := bstep (se 2 (by rfl) ⟨17087010, by rfl⟩ : syracuseStep 45565361 = 34174021) B34174021
theorem B7022123 : Blo 1847625 7022123 := bstep (se 1 (by rfl) ⟨5266592, by rfl⟩ : syracuseStep 7022123 = 10533185) B10533185
theorem B22488677 : Blo 1847625 22488677 := bstep (se 4 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 22488677 = 4216627) B4216627
theorem B6235919 : Blo 1847625 6235919 := bstep (se 1 (by rfl) ⟨4676939, by rfl⟩ : syracuseStep 6235919 = 9353879) B9353879
theorem B4998955 : Blo 1847625 4998955 := bstep (se 1 (by rfl) ⟨3749216, by rfl⟩ : syracuseStep 4998955 = 7498433) B7498433
theorem B13690673 : Blo 1847625 13690673 := bstep (se 2 (by rfl) ⟨5134002, by rfl⟩ : syracuseStep 13690673 = 10268005) B10268005
theorem B14042969 : Blo 1847625 14042969 := bstep (se 2 (by rfl) ⟨5266113, by rfl⟩ : syracuseStep 14042969 = 10532227) B10532227
theorem B44984267 : Blo 1847625 44984267 := bstep (se 1 (by rfl) ⟨33738200, by rfl⟩ : syracuseStep 44984267 = 67476401) B67476401
theorem B6236189 : Blo 1847625 6236189 := bstep (se 3 (by rfl) ⟨1169285, by rfl⟩ : syracuseStep 6236189 = 2338571) B2338571
theorem B3508267 : Blo 1847625 3508267 := bstep (se 1 (by rfl) ⟨2631200, by rfl⟩ : syracuseStep 3508267 = 5262401) B5262401
theorem B10528811 : Blo 1847625 10528811 := bstep (se 1 (by rfl) ⟨7896608, by rfl⟩ : syracuseStep 10528811 = 15793217) B15793217
theorem B21063725 : Blo 1847625 21063725 := bstep (se 3 (by rfl) ⟨3949448, by rfl⟩ : syracuseStep 21063725 = 7898897) B7898897
theorem B4679795 : Blo 1847625 4679795 := bstep (se 1 (by rfl) ⟨3509846, by rfl⟩ : syracuseStep 4679795 = 7019693) B7019693
theorem B3508343 : Blo 1847625 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B4679815 : Blo 1847625 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B2632009 : Blo 1847625 2632009 := bstep (se 2 (by rfl) ⟨987003, by rfl⟩ : syracuseStep 2632009 = 1974007) B1974007
theorem B21047687 : Blo 1847625 21047687 := bstep (se 1 (by rfl) ⟨15785765, by rfl⟩ : syracuseStep 21047687 = 31571531) B31571531
theorem B4000147 : Blo 1847625 4000147 := bstep (se 1 (by rfl) ⟨3000110, by rfl⟩ : syracuseStep 4000147 = 6000221) B6000221
theorem B4680089 : Blo 1847625 4680089 := bstep (se 2 (by rfl) ⟨1755033, by rfl⟩ : syracuseStep 4680089 = 3510067) B3510067
theorem B2632123 : Blo 1847625 2632123 := bstep (se 1 (by rfl) ⟨1974092, by rfl⟩ : syracuseStep 2632123 = 3948185) B3948185
theorem B2771447 : Blo 1847625 2771447 := bstep (se 1 (by rfl) ⟨2078585, by rfl⟩ : syracuseStep 2771447 = 4157171) B4157171
theorem B2771471 : Blo 1847625 2771471 := bstep (se 1 (by rfl) ⟨2078603, by rfl⟩ : syracuseStep 2771471 = 4157207) B4157207
theorem B2771513 : Blo 1847625 2771513 := bstep (se 2 (by rfl) ⟨1039317, by rfl⟩ : syracuseStep 2771513 = 2078635) B2078635
theorem B4680251 : Blo 1847625 4680251 := bstep (se 1 (by rfl) ⟨3510188, by rfl⟩ : syracuseStep 4680251 = 7020377) B7020377
theorem B2771591 : Blo 1847625 2771591 := bstep (se 1 (by rfl) ⟨2078693, by rfl⟩ : syracuseStep 2771591 = 4157387) B4157387
theorem B2771627 : Blo 1847625 2771627 := bstep (se 1 (by rfl) ⟨2078720, by rfl⟩ : syracuseStep 2771627 = 4157441) B4157441
theorem B2771657 : Blo 1847625 2771657 := bstep (se 2 (by rfl) ⟨1039371, by rfl⟩ : syracuseStep 2771657 = 2078743) B2078743
theorem B5696201 : Blo 1847625 5696201 := bstep (se 2 (by rfl) ⟨2136075, by rfl⟩ : syracuseStep 5696201 = 4272151) B4272151
theorem B4680463 : Blo 1847625 4680463 := bstep (se 1 (by rfl) ⟨3510347, by rfl⟩ : syracuseStep 4680463 = 7020695) B7020695
theorem B14043941 : Blo 1847625 14043941 := bstep (se 4 (by rfl) ⟨1316619, by rfl⟩ : syracuseStep 14043941 = 2633239) B2633239
theorem B2771771 : Blo 1847625 2771771 := bstep (se 1 (by rfl) ⟨2078828, by rfl⟩ : syracuseStep 2771771 = 4157657) B4157657
theorem B2771831 : Blo 1847625 2771831 := bstep (se 1 (by rfl) ⟨2078873, by rfl⟩ : syracuseStep 2771831 = 4157747) B4157747
theorem B2771855 : Blo 1847625 2771855 := bstep (se 1 (by rfl) ⟨2078891, by rfl⟩ : syracuseStep 2771855 = 4157783) B4157783
theorem B2771897 : Blo 1847625 2771897 := bstep (se 2 (by rfl) ⟨1039461, by rfl⟩ : syracuseStep 2771897 = 2078923) B2078923
theorem B2771975 : Blo 1847625 2771975 := bstep (se 1 (by rfl) ⟨2078981, by rfl⟩ : syracuseStep 2771975 = 4157963) B4157963
theorem B6663197 : Blo 1847625 6663197 := bstep (se 3 (by rfl) ⟨1249349, by rfl⟩ : syracuseStep 6663197 = 2498699) B2498699
theorem B4680737 : Blo 1847625 4680737 := bstep (se 2 (by rfl) ⟨1755276, by rfl⟩ : syracuseStep 4680737 = 3510553) B3510553
theorem B2772011 : Blo 1847625 2772011 := bstep (se 1 (by rfl) ⟨2079008, by rfl⟩ : syracuseStep 2772011 = 4158017) B4158017
theorem B2772041 : Blo 1847625 2772041 := bstep (se 2 (by rfl) ⟨1039515, by rfl⟩ : syracuseStep 2772041 = 2079031) B2079031
theorem B2772155 : Blo 1847625 2772155 := bstep (se 1 (by rfl) ⟨2079116, by rfl⟩ : syracuseStep 2772155 = 4158233) B4158233
theorem B2772215 : Blo 1847625 2772215 := bstep (se 1 (by rfl) ⟨2079161, by rfl⟩ : syracuseStep 2772215 = 4158323) B4158323
theorem B2772239 : Blo 1847625 2772239 := bstep (se 1 (by rfl) ⟨2079179, by rfl⟩ : syracuseStep 2772239 = 4158359) B4158359
theorem B2772281 : Blo 1847625 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B2772359 : Blo 1847625 2772359 := bstep (se 1 (by rfl) ⟨2079269, by rfl⟩ : syracuseStep 2772359 = 4158539) B4158539
theorem B9358739 : Blo 1847625 9358739 := bstep (se 1 (by rfl) ⟨7019054, by rfl⟩ : syracuseStep 9358739 = 14038109) B14038109
theorem B6237593 : Blo 1847625 6237593 := bstep (se 2 (by rfl) ⟨2339097, by rfl⟩ : syracuseStep 6237593 = 4678195) B4678195
theorem B2772395 : Blo 1847625 2772395 := bstep (se 1 (by rfl) ⟨2079296, by rfl⟩ : syracuseStep 2772395 = 4158593) B4158593
theorem B2772425 : Blo 1847625 2772425 := bstep (se 2 (by rfl) ⟨1039659, by rfl⟩ : syracuseStep 2772425 = 2079319) B2079319
theorem B10530269 : Blo 1847625 10530269 := bstep (se 3 (by rfl) ⟨1974425, by rfl⟩ : syracuseStep 10530269 = 3948851) B3948851
theorem B2772539 : Blo 1847625 2772539 := bstep (se 1 (by rfl) ⟨2079404, by rfl⟩ : syracuseStep 2772539 = 4158809) B4158809
theorem B9989693 : Blo 1847625 9989693 := bstep (se 3 (by rfl) ⟨1873067, by rfl⟩ : syracuseStep 9989693 = 3746135) B3746135
theorem B4443707 : Blo 1847625 4443707 := bstep (se 1 (by rfl) ⟨3332780, by rfl⟩ : syracuseStep 4443707 = 6665561) B6665561
theorem B7016003 : Blo 1847625 7016003 := bstep (se 1 (by rfl) ⟨5262002, by rfl⟩ : syracuseStep 7016003 = 10524005) B10524005
theorem B2772599 : Blo 1847625 2772599 := bstep (se 1 (by rfl) ⟨2079449, by rfl⟩ : syracuseStep 2772599 = 4158899) B4158899
theorem B2772623 : Blo 1847625 2772623 := bstep (se 1 (by rfl) ⟨2079467, by rfl⟩ : syracuseStep 2772623 = 4158935) B4158935
theorem B2772665 : Blo 1847625 2772665 := bstep (se 2 (by rfl) ⟨1039749, by rfl⟩ : syracuseStep 2772665 = 2079499) B2079499
theorem B2772743 : Blo 1847625 2772743 := bstep (se 1 (by rfl) ⟨2079557, by rfl⟩ : syracuseStep 2772743 = 4159115) B4159115
theorem B7114511 : Blo 1847625 7114511 := bstep (se 1 (by rfl) ⟨5335883, by rfl⟩ : syracuseStep 7114511 = 10671767) B10671767
theorem B2772779 : Blo 1847625 2772779 := bstep (se 1 (by rfl) ⟨2079584, by rfl⟩ : syracuseStep 2772779 = 4159169) B4159169
theorem B14225203 : Blo 1847625 14225203 := bstep (se 1 (by rfl) ⟨10668902, by rfl⟩ : syracuseStep 14225203 = 21337805) B21337805
theorem B4157243 : Blo 1847625 4157243 := bstep (se 1 (by rfl) ⟨3117932, by rfl⟩ : syracuseStep 4157243 = 6235865) B6235865
theorem B2772809 : Blo 1847625 2772809 := bstep (se 2 (by rfl) ⟨1039803, by rfl⟩ : syracuseStep 2772809 = 2079607) B2079607
theorem B4001671 : Blo 1847625 4001671 := bstep (se 1 (by rfl) ⟨3001253, by rfl⟩ : syracuseStep 4001671 = 6002507) B6002507
theorem B22482839 : Blo 1847625 22482839 := bstep (se 1 (by rfl) ⟨16862129, by rfl⟩ : syracuseStep 22482839 = 33724259) B33724259
theorem B4157369 : Blo 1847625 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B5263289 : Blo 1847625 5263289 := bstep (se 2 (by rfl) ⟨1973733, by rfl⟩ : syracuseStep 5263289 = 3947467) B3947467
theorem B2772923 : Blo 1847625 2772923 := bstep (se 1 (by rfl) ⟨2079692, by rfl⟩ : syracuseStep 2772923 = 4159385) B4159385
theorem B10530769 : Blo 1847625 10530769 := bstep (se 2 (by rfl) ⟨3949038, by rfl⟩ : syracuseStep 10530769 = 7898077) B7898077
theorem B2772983 : Blo 1847625 2772983 := bstep (se 1 (by rfl) ⟨2079737, by rfl⟩ : syracuseStep 2772983 = 4159475) B4159475
theorem B4681739 : Blo 1847625 4681739 := bstep (se 1 (by rfl) ⟨3511304, by rfl⟩ : syracuseStep 4681739 = 7022609) B7022609
theorem B2773007 : Blo 1847625 2773007 := bstep (se 1 (by rfl) ⟨2079755, by rfl⟩ : syracuseStep 2773007 = 4159511) B4159511
theorem B3510287 : Blo 1847625 3510287 := bstep (se 1 (by rfl) ⟨2632715, by rfl⟩ : syracuseStep 3510287 = 5265431) B5265431
theorem B109555733 : Blo 1847625 109555733 := bstep (se 6 (by rfl) ⟨2567712, by rfl⟩ : syracuseStep 109555733 = 5135425) B5135425
theorem B2773049 : Blo 1847625 2773049 := bstep (se 2 (by rfl) ⟨1039893, by rfl⟩ : syracuseStep 2773049 = 2079787) B2079787
theorem B6238295 : Blo 1847625 6238295 := bstep (se 1 (by rfl) ⟨4678721, by rfl⟩ : syracuseStep 6238295 = 9357443) B9357443
theorem B2338951 : Blo 1847625 2338951 := bstep (se 1 (by rfl) ⟨1754213, by rfl⟩ : syracuseStep 2338951 = 3508427) B3508427
theorem B2773127 : Blo 1847625 2773127 := bstep (se 1 (by rfl) ⟨2079845, by rfl⟩ : syracuseStep 2773127 = 4159691) B4159691
theorem B2773163 : Blo 1847625 2773163 := bstep (se 1 (by rfl) ⟨2079872, by rfl⟩ : syracuseStep 2773163 = 4159745) B4159745
theorem B2371771 : Blo 1847625 2371771 := bstep (se 1 (by rfl) ⟨1778828, by rfl⟩ : syracuseStep 2371771 = 3557657) B3557657
theorem B2773193 : Blo 1847625 2773193 := bstep (se 2 (by rfl) ⟨1039947, by rfl⟩ : syracuseStep 2773193 = 2079895) B2079895
theorem B4157711 : Blo 1847625 4157711 := bstep (se 1 (by rfl) ⟨3118283, by rfl⟩ : syracuseStep 4157711 = 6236567) B6236567
theorem B4157729 : Blo 1847625 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B2773307 : Blo 1847625 2773307 := bstep (se 1 (by rfl) ⟨2079980, by rfl⟩ : syracuseStep 2773307 = 4159961) B4159961
theorem B2773367 : Blo 1847625 2773367 := bstep (se 1 (by rfl) ⟨2080025, by rfl⟩ : syracuseStep 2773367 = 4160051) B4160051
theorem B1847687 : Blo 1847625 1847687 := bstep (se 1 (by rfl) ⟨1385765, by rfl⟩ : syracuseStep 1847687 = 2771531) B2771531
theorem B7704967 : Blo 1847625 7704967 := bstep (se 1 (by rfl) ⟨5778725, by rfl⟩ : syracuseStep 7704967 = 11557451) B11557451
theorem B1847695 : Blo 1847625 1847695 := bstep (se 1 (by rfl) ⟨1385771, by rfl⟩ : syracuseStep 1847695 = 2771543) B2771543
theorem B2773391 : Blo 1847625 2773391 := bstep (se 1 (by rfl) ⟨2080043, by rfl⟩ : syracuseStep 2773391 = 4160087) B4160087
theorem B2773433 : Blo 1847625 2773433 := bstep (se 2 (by rfl) ⟨1040037, by rfl⟩ : syracuseStep 2773433 = 2080075) B2080075
theorem B1847739 : Blo 1847625 1847739 := bstep (se 1 (by rfl) ⟨1385804, by rfl⟩ : syracuseStep 1847739 = 2771609) B2771609
theorem B1847815 : Blo 1847625 1847815 := bstep (se 1 (by rfl) ⟨1385861, by rfl⟩ : syracuseStep 1847815 = 2771723) B2771723
theorem B2773511 : Blo 1847625 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B1847823 : Blo 1847625 1847823 := bstep (se 1 (by rfl) ⟨1385867, by rfl⟩ : syracuseStep 1847823 = 2771735) B2771735
theorem B7016989 : Blo 1847625 7016989 := bstep (se 3 (by rfl) ⟨1315685, by rfl⟩ : syracuseStep 7016989 = 2631371) B2631371
theorem B2339371 : Blo 1847625 2339371 := bstep (se 1 (by rfl) ⟨1754528, by rfl⟩ : syracuseStep 2339371 = 3509057) B3509057
theorem B2773547 : Blo 1847625 2773547 := bstep (se 1 (by rfl) ⟨2080160, by rfl⟩ : syracuseStep 2773547 = 4160321) B4160321
theorem B1847867 : Blo 1847625 1847867 := bstep (se 1 (by rfl) ⟨1385900, by rfl⟩ : syracuseStep 1847867 = 2771801) B2771801
theorem B6238781 : Blo 1847625 6238781 := bstep (se 3 (by rfl) ⟨1169771, by rfl⟩ : syracuseStep 6238781 = 2339543) B2339543
theorem B2773577 : Blo 1847625 2773577 := bstep (se 2 (by rfl) ⟨1040091, by rfl⟩ : syracuseStep 2773577 = 2080183) B2080183
theorem B4158071 : Blo 1847625 4158071 := bstep (se 1 (by rfl) ⟨3118553, by rfl⟩ : syracuseStep 4158071 = 6237107) B6237107
theorem B14037623 : Blo 1847625 14037623 := bstep (se 1 (by rfl) ⟨10528217, by rfl⟩ : syracuseStep 14037623 = 21056435) B21056435
theorem B44470903 : Blo 1847625 44470903 := bstep (se 1 (by rfl) ⟨33353177, by rfl⟩ : syracuseStep 44470903 = 66706355) B66706355
theorem B1847943 : Blo 1847625 1847943 := bstep (se 1 (by rfl) ⟨1385957, by rfl⟩ : syracuseStep 1847943 = 2771915) B2771915
theorem B1847951 : Blo 1847625 1847951 := bstep (se 1 (by rfl) ⟨1385963, by rfl⟩ : syracuseStep 1847951 = 2771927) B2771927
theorem B1847995 : Blo 1847625 1847995 := bstep (se 1 (by rfl) ⟨1385996, by rfl⟩ : syracuseStep 1847995 = 2771993) B2771993
theorem B2773691 : Blo 1847625 2773691 := bstep (se 1 (by rfl) ⟨2080268, by rfl⟩ : syracuseStep 2773691 = 4160537) B4160537
theorem B2773751 : Blo 1847625 2773751 := bstep (se 1 (by rfl) ⟨2080313, by rfl⟩ : syracuseStep 2773751 = 4160627) B4160627
theorem B1848071 : Blo 1847625 1848071 := bstep (se 1 (by rfl) ⟨1386053, by rfl⟩ : syracuseStep 1848071 = 2772107) B2772107
theorem B1848079 : Blo 1847625 1848079 := bstep (se 1 (by rfl) ⟨1386059, by rfl⟩ : syracuseStep 1848079 = 2772119) B2772119
theorem B2339599 : Blo 1847625 2339599 := bstep (se 1 (by rfl) ⟨1754699, by rfl⟩ : syracuseStep 2339599 = 3509399) B3509399
theorem B2773775 : Blo 1847625 2773775 := bstep (se 1 (by rfl) ⟨2080331, by rfl⟩ : syracuseStep 2773775 = 4160663) B4160663
theorem B9999119 : Blo 1847625 9999119 := bstep (se 1 (by rfl) ⟨7499339, by rfl⟩ : syracuseStep 9999119 = 14998679) B14998679
theorem B4158251 : Blo 1847625 4158251 := bstep (se 1 (by rfl) ⟨3118688, by rfl⟩ : syracuseStep 4158251 = 6237377) B6237377
theorem B2773817 : Blo 1847625 2773817 := bstep (se 2 (by rfl) ⟨1040181, by rfl⟩ : syracuseStep 2773817 = 2080363) B2080363
theorem B1848123 : Blo 1847625 1848123 := bstep (se 1 (by rfl) ⟨1386092, by rfl⟩ : syracuseStep 1848123 = 2772185) B2772185
theorem B7893875 : Blo 1847625 7893875 := bstep (se 1 (by rfl) ⟨5920406, by rfl⟩ : syracuseStep 7893875 = 11840813) B11840813
theorem B1848199 : Blo 1847625 1848199 := bstep (se 1 (by rfl) ⟨1386149, by rfl⟩ : syracuseStep 1848199 = 2772299) B2772299
theorem B2773895 : Blo 1847625 2773895 := bstep (se 1 (by rfl) ⟨2080421, by rfl⟩ : syracuseStep 2773895 = 4160843) B4160843
theorem B1848207 : Blo 1847625 1848207 := bstep (se 1 (by rfl) ⟨1386155, by rfl⟩ : syracuseStep 1848207 = 2772311) B2772311
theorem B2773931 : Blo 1847625 2773931 := bstep (se 1 (by rfl) ⟨2080448, by rfl⟩ : syracuseStep 2773931 = 4160897) B4160897
theorem B1848251 : Blo 1847625 1848251 := bstep (se 1 (by rfl) ⟨1386188, by rfl⟩ : syracuseStep 1848251 = 2772377) B2772377
theorem B2773961 : Blo 1847625 2773961 := bstep (se 2 (by rfl) ⟨1040235, by rfl⟩ : syracuseStep 2773961 = 2080471) B2080471
theorem B1848327 : Blo 1847625 1848327 := bstep (se 1 (by rfl) ⟨1386245, by rfl⟩ : syracuseStep 1848327 = 2772491) B2772491
theorem B1848335 : Blo 1847625 1848335 := bstep (se 1 (by rfl) ⟨1386251, by rfl⟩ : syracuseStep 1848335 = 2772503) B2772503
theorem B1848379 : Blo 1847625 1848379 := bstep (se 1 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 1848379 = 2772569) B2772569
theorem B2774075 : Blo 1847625 2774075 := bstep (se 1 (by rfl) ⟨2080556, by rfl⟩ : syracuseStep 2774075 = 4161113) B4161113
theorem B19985525 : Blo 1847625 19985525 := bstep (se 5 (by rfl) ⟨936821, by rfl⟩ : syracuseStep 19985525 = 1873643) B1873643
theorem B2774135 : Blo 1847625 2774135 := bstep (se 1 (by rfl) ⟨2080601, by rfl⟩ : syracuseStep 2774135 = 4161203) B4161203
theorem B1848455 : Blo 1847625 1848455 := bstep (se 1 (by rfl) ⟨1386341, by rfl⟩ : syracuseStep 1848455 = 2772683) B2772683
theorem B1848463 : Blo 1847625 1848463 := bstep (se 1 (by rfl) ⟨1386347, by rfl⟩ : syracuseStep 1848463 = 2772695) B2772695
theorem B2774159 : Blo 1847625 2774159 := bstep (se 1 (by rfl) ⟨2080619, by rfl⟩ : syracuseStep 2774159 = 4161239) B4161239
theorem B4158611 : Blo 1847625 4158611 := bstep (se 1 (by rfl) ⟨3118958, by rfl⟩ : syracuseStep 4158611 = 6237917) B6237917
theorem B2774201 : Blo 1847625 2774201 := bstep (se 2 (by rfl) ⟨1040325, by rfl⟩ : syracuseStep 2774201 = 2080651) B2080651
theorem B1848507 : Blo 1847625 1848507 := bstep (se 1 (by rfl) ⟨1386380, by rfl⟩ : syracuseStep 1848507 = 2772761) B2772761
theorem B4158665 : Blo 1847625 4158665 := bstep (se 2 (by rfl) ⟨1559499, by rfl⟩ : syracuseStep 4158665 = 3118999) B3118999
theorem B1848583 : Blo 1847625 1848583 := bstep (se 1 (by rfl) ⟨1386437, by rfl⟩ : syracuseStep 1848583 = 2772875) B2772875
theorem B2774279 : Blo 1847625 2774279 := bstep (se 1 (by rfl) ⟨2080709, by rfl⟩ : syracuseStep 2774279 = 4161419) B4161419
theorem B3118351 : Blo 1847625 3118351 := bstep (se 1 (by rfl) ⟨2338763, by rfl⟩ : syracuseStep 3118351 = 4677527) B4677527
theorem B1848591 : Blo 1847625 1848591 := bstep (se 1 (by rfl) ⟨1386443, by rfl⟩ : syracuseStep 1848591 = 2772887) B2772887
theorem B23680289 : Blo 1847625 23680289 := bstep (se 2 (by rfl) ⟨8880108, by rfl⟩ : syracuseStep 23680289 = 17760217) B17760217
theorem B2774315 : Blo 1847625 2774315 := bstep (se 1 (by rfl) ⟨2080736, by rfl⟩ : syracuseStep 2774315 = 4161473) B4161473
theorem B1848635 : Blo 1847625 1848635 := bstep (se 1 (by rfl) ⟨1386476, by rfl⟩ : syracuseStep 1848635 = 2772953) B2772953
theorem B2774345 : Blo 1847625 2774345 := bstep (se 2 (by rfl) ⟨1040379, by rfl⟩ : syracuseStep 2774345 = 2080759) B2080759
theorem B1848711 : Blo 1847625 1848711 := bstep (se 1 (by rfl) ⟨1386533, by rfl⟩ : syracuseStep 1848711 = 2773067) B2773067
theorem B1848719 : Blo 1847625 1848719 := bstep (se 1 (by rfl) ⟨1386539, by rfl⟩ : syracuseStep 1848719 = 2773079) B2773079
theorem B15791507 : Blo 1847625 15791507 := bstep (se 1 (by rfl) ⟨11843630, by rfl⟩ : syracuseStep 15791507 = 23687261) B23687261
theorem B1848763 : Blo 1847625 1848763 := bstep (se 1 (by rfl) ⟨1386572, by rfl⟩ : syracuseStep 1848763 = 2773145) B2773145
theorem B2340343 : Blo 1847625 2340343 := bstep (se 1 (by rfl) ⟨1755257, by rfl⟩ : syracuseStep 2340343 = 3510515) B3510515
theorem B1848839 : Blo 1847625 1848839 := bstep (se 1 (by rfl) ⟨1386629, by rfl⟩ : syracuseStep 1848839 = 2773259) B2773259
theorem B1848847 : Blo 1847625 1848847 := bstep (se 1 (by rfl) ⟨1386635, by rfl⟩ : syracuseStep 1848847 = 2773271) B2773271
theorem B5264929 : Blo 1847625 5264929 := bstep (se 2 (by rfl) ⟨1974348, by rfl⟩ : syracuseStep 5264929 = 3948697) B3948697
theorem B1848891 : Blo 1847625 1848891 := bstep (se 1 (by rfl) ⟨1386668, by rfl⟩ : syracuseStep 1848891 = 2773337) B2773337
theorem B14038595 : Blo 1847625 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B1848967 : Blo 1847625 1848967 := bstep (se 1 (by rfl) ⟨1386725, by rfl⟩ : syracuseStep 1848967 = 2773451) B2773451
theorem B1848975 : Blo 1847625 1848975 := bstep (se 1 (by rfl) ⟨1386731, by rfl⟩ : syracuseStep 1848975 = 2773463) B2773463
theorem B39990935 : Blo 1847625 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B9991853 : Blo 1847625 9991853 := bstep (se 3 (by rfl) ⟨1873472, by rfl⟩ : syracuseStep 9991853 = 3746945) B3746945
theorem B1849019 : Blo 1847625 1849019 := bstep (se 1 (by rfl) ⟨1386764, by rfl⟩ : syracuseStep 1849019 = 2773529) B2773529
theorem B1849095 : Blo 1847625 1849095 := bstep (se 1 (by rfl) ⟨1386821, by rfl⟩ : syracuseStep 1849095 = 2773643) B2773643
theorem B1849103 : Blo 1847625 1849103 := bstep (se 1 (by rfl) ⟨1386827, by rfl⟩ : syracuseStep 1849103 = 2773655) B2773655
theorem B3118891 : Blo 1847625 3118891 := bstep (se 1 (by rfl) ⟨2339168, by rfl⟩ : syracuseStep 3118891 = 4678337) B4678337
theorem B1849147 : Blo 1847625 1849147 := bstep (se 1 (by rfl) ⟨1386860, by rfl⟩ : syracuseStep 1849147 = 2773721) B2773721
theorem B2340667 : Blo 1847625 2340667 := bstep (se 1 (by rfl) ⟨1755500, by rfl⟩ : syracuseStep 2340667 = 3511001) B3511001
theorem B2078599 : Blo 1847625 2078599 := bstep (se 1 (by rfl) ⟨1558949, by rfl⟩ : syracuseStep 2078599 = 3117899) B3117899
theorem B4159367 : Blo 1847625 4159367 := bstep (se 1 (by rfl) ⟨3119525, by rfl⟩ : syracuseStep 4159367 = 6239051) B6239051
theorem B1849223 : Blo 1847625 1849223 := bstep (se 1 (by rfl) ⟨1386917, by rfl⟩ : syracuseStep 1849223 = 2773835) B2773835
theorem B1849231 : Blo 1847625 1849231 := bstep (se 1 (by rfl) ⟨1386923, by rfl⟩ : syracuseStep 1849231 = 2773847) B2773847
theorem B10532753 : Blo 1847625 10532753 := bstep (se 2 (by rfl) ⟨3949782, by rfl⟩ : syracuseStep 10532753 = 7899565) B7899565
theorem B3119033 : Blo 1847625 3119033 := bstep (se 2 (by rfl) ⟨1169637, by rfl⟩ : syracuseStep 3119033 = 2339275) B2339275
theorem B6240185 : Blo 1847625 6240185 := bstep (se 2 (by rfl) ⟨2340069, by rfl⟩ : syracuseStep 6240185 = 4680139) B4680139
theorem B1849275 : Blo 1847625 1849275 := bstep (se 1 (by rfl) ⟨1386956, by rfl⟩ : syracuseStep 1849275 = 2773913) B2773913
theorem B1849351 : Blo 1847625 1849351 := bstep (se 1 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 1849351 = 2774027) B2774027
theorem B1849359 : Blo 1847625 1849359 := bstep (se 1 (by rfl) ⟨1387019, by rfl⟩ : syracuseStep 1849359 = 2774039) B2774039
theorem B2078779 : Blo 1847625 2078779 := bstep (se 1 (by rfl) ⟨1559084, by rfl⟩ : syracuseStep 2078779 = 3118169) B3118169
theorem B4159547 : Blo 1847625 4159547 := bstep (se 1 (by rfl) ⟨3119660, by rfl⟩ : syracuseStep 4159547 = 6239321) B6239321
theorem B1849403 : Blo 1847625 1849403 := bstep (se 1 (by rfl) ⟨1387052, by rfl⟩ : syracuseStep 1849403 = 2774105) B2774105
theorem B7600247 : Blo 1847625 7600247 := bstep (se 1 (by rfl) ⟨5700185, by rfl⟩ : syracuseStep 7600247 = 11400371) B11400371
theorem B1849479 : Blo 1847625 1849479 := bstep (se 1 (by rfl) ⟨1387109, by rfl⟩ : syracuseStep 1849479 = 2774219) B2774219
theorem B1849487 : Blo 1847625 1849487 := bstep (se 1 (by rfl) ⟨1387115, by rfl⟩ : syracuseStep 1849487 = 2774231) B2774231
theorem B3946681 : Blo 1847625 3946681 := bstep (se 2 (by rfl) ⟨1480005, by rfl⟩ : syracuseStep 3946681 = 2960011) B2960011
theorem B4159673 : Blo 1847625 4159673 := bstep (se 2 (by rfl) ⟨1559877, by rfl⟩ : syracuseStep 4159673 = 3119755) B3119755
theorem B1849531 : Blo 1847625 1849531 := bstep (se 1 (by rfl) ⟨1387148, by rfl⟩ : syracuseStep 1849531 = 2774297) B2774297
theorem B1849607 : Blo 1847625 1849607 := bstep (se 1 (by rfl) ⟨1387205, by rfl⟩ : syracuseStep 1849607 = 2774411) B2774411
theorem B71055629 : Blo 1847625 71055629 := bstep (se 3 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 71055629 = 26645861) B26645861
theorem B1849615 : Blo 1847625 1849615 := bstep (se 1 (by rfl) ⟨1387211, by rfl⟩ : syracuseStep 1849615 = 2774423) B2774423
theorem B9361817 : Blo 1847625 9361817 := bstep (se 2 (by rfl) ⟨3510681, by rfl⟩ : syracuseStep 9361817 = 7021363) B7021363
theorem B15792569 : Blo 1847625 15792569 := bstep (se 2 (by rfl) ⟨5922213, by rfl⟩ : syracuseStep 15792569 = 11844427) B11844427
theorem B6240779 : Blo 1847625 6240779 := bstep (se 1 (by rfl) ⟨4680584, by rfl⟩ : syracuseStep 6240779 = 9361169) B9361169
theorem B2079247 : Blo 1847625 2079247 := bstep (se 1 (by rfl) ⟨1559435, by rfl⟩ : syracuseStep 2079247 = 3118871) B3118871
theorem B4160015 : Blo 1847625 4160015 := bstep (se 1 (by rfl) ⟨3120011, by rfl⟩ : syracuseStep 4160015 = 6240023) B6240023
theorem B4160033 : Blo 1847625 4160033 := bstep (se 2 (by rfl) ⟨1560012, by rfl⟩ : syracuseStep 4160033 = 3120025) B3120025
theorem B3119735 : Blo 1847625 3119735 := bstep (se 1 (by rfl) ⟨2339801, by rfl⟩ : syracuseStep 3119735 = 4679603) B4679603
theorem B6240887 : Blo 1847625 6240887 := bstep (se 1 (by rfl) ⟨4680665, by rfl⟩ : syracuseStep 6240887 = 9361331) B9361331
theorem B3947143 : Blo 1847625 3947143 := bstep (se 1 (by rfl) ⟨2960357, by rfl⟩ : syracuseStep 3947143 = 5920715) B5920715
theorem B3332809 : Blo 1847625 3332809 := bstep (se 2 (by rfl) ⟨1249803, by rfl⟩ : syracuseStep 3332809 = 2499607) B2499607
theorem B7895789 : Blo 1847625 7895789 := bstep (se 3 (by rfl) ⟨1480460, by rfl⟩ : syracuseStep 7895789 = 2960921) B2960921
theorem B5266205 : Blo 1847625 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B4742003 : Blo 1847625 4742003 := bstep (se 1 (by rfl) ⟨3556502, by rfl⟩ : syracuseStep 4742003 = 7113005) B7113005
theorem B4160375 : Blo 1847625 4160375 := bstep (se 1 (by rfl) ⟨3120281, by rfl⟩ : syracuseStep 4160375 = 6240563) B6240563
theorem B3332983 : Blo 1847625 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B23108503 : Blo 1847625 23108503 := bstep (se 1 (by rfl) ⟨17331377, by rfl⟩ : syracuseStep 23108503 = 34662755) B34662755
theorem B8879033 : Blo 1847625 8879033 := bstep (se 2 (by rfl) ⟨3329637, by rfl⟩ : syracuseStep 8879033 = 6659275) B6659275
theorem B3799993 : Blo 1847625 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B5266433 : Blo 1847625 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B1973255 : Blo 1847625 1973255 := bstep (se 1 (by rfl) ⟨1479941, by rfl⟩ : syracuseStep 1973255 = 2959883) B2959883
theorem B2079751 : Blo 1847625 2079751 := bstep (se 1 (by rfl) ⟨1559813, by rfl⟩ : syracuseStep 2079751 = 3119627) B3119627
theorem B9993239 : Blo 1847625 9993239 := bstep (se 1 (by rfl) ⟨7494929, by rfl⟩ : syracuseStep 9993239 = 14989859) B14989859
theorem B4160555 : Blo 1847625 4160555 := bstep (se 1 (by rfl) ⟨3120416, by rfl⟩ : syracuseStep 4160555 = 6240833) B6240833
theorem B3120187 : Blo 1847625 3120187 := bstep (se 1 (by rfl) ⟨2340140, by rfl⟩ : syracuseStep 3120187 = 4680281) B4680281
theorem B3161207 : Blo 1847625 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2079931 : Blo 1847625 2079931 := bstep (se 1 (by rfl) ⟨1559948, by rfl⟩ : syracuseStep 2079931 = 3119897) B3119897
theorem B21060809 : Blo 1847625 21060809 := bstep (se 2 (by rfl) ⟨7897803, by rfl⟩ : syracuseStep 21060809 = 15795607) B15795607
theorem B3120329 : Blo 1847625 3120329 := bstep (se 2 (by rfl) ⟨1170123, by rfl⟩ : syracuseStep 3120329 = 2340247) B2340247
theorem B6241481 : Blo 1847625 6241481 := bstep (se 2 (by rfl) ⟨2340555, by rfl⟩ : syracuseStep 6241481 = 4681111) B4681111
theorem B8879341 : Blo 1847625 8879341 := bstep (se 3 (by rfl) ⟨1664876, by rfl⟩ : syracuseStep 8879341 = 3329753) B3329753
theorem B4676879 : Blo 1847625 4676879 := bstep (se 1 (by rfl) ⟨3507659, by rfl⟩ : syracuseStep 4676879 = 7015319) B7015319
theorem B5266775 : Blo 1847625 5266775 := bstep (se 1 (by rfl) ⟨3950081, by rfl⟩ : syracuseStep 5266775 = 7900163) B7900163
theorem B7019891 : Blo 1847625 7019891 := bstep (se 1 (by rfl) ⟨5264918, by rfl⟩ : syracuseStep 7019891 = 10529837) B10529837
theorem B4677011 : Blo 1847625 4677011 := bstep (se 1 (by rfl) ⟨3507758, by rfl⟩ : syracuseStep 4677011 = 7015517) B7015517
theorem B16006547 : Blo 1847625 16006547 := bstep (se 1 (by rfl) ⟨12004910, by rfl⟩ : syracuseStep 16006547 = 24009821) B24009821
theorem B4160915 : Blo 1847625 4160915 := bstep (se 1 (by rfl) ⟨3120686, by rfl⟩ : syracuseStep 4160915 = 6241373) B6241373
theorem B7896473 : Blo 1847625 7896473 := bstep (se 2 (by rfl) ⟨2961177, by rfl⟩ : syracuseStep 7896473 = 5922355) B5922355
theorem B17776057 : Blo 1847625 17776057 := bstep (se 2 (by rfl) ⟨6666021, by rfl⟩ : syracuseStep 17776057 = 13332043) B13332043
theorem B4160969 : Blo 1847625 4160969 := bstep (se 2 (by rfl) ⟨1560363, by rfl⟩ : syracuseStep 4160969 = 3120727) B3120727
theorem B5266889 : Blo 1847625 5266889 := bstep (se 2 (by rfl) ⟨1975083, by rfl⟩ : syracuseStep 5266889 = 3950167) B3950167
theorem B1973819 : Blo 1847625 1973819 := bstep (se 1 (by rfl) ⟨1480364, by rfl⟩ : syracuseStep 1973819 = 2960729) B2960729
theorem B2080399 : Blo 1847625 2080399 := bstep (se 1 (by rfl) ⟨1560299, by rfl⟩ : syracuseStep 2080399 = 3120599) B3120599
theorem B13319909 : Blo 1847625 13319909 := bstep (se 4 (by rfl) ⟨1248741, by rfl⟩ : syracuseStep 13319909 = 2497483) B2497483
theorem B7896847 : Blo 1847625 7896847 := bstep (se 1 (by rfl) ⟨5922635, by rfl⟩ : syracuseStep 7896847 = 11845271) B11845271
theorem B3121031 : Blo 1847625 3121031 := bstep (se 1 (by rfl) ⟨2340773, by rfl⟩ : syracuseStep 3121031 = 4681547) B4681547
theorem B6242183 : Blo 1847625 6242183 := bstep (se 1 (by rfl) ⟨4681637, by rfl⟩ : syracuseStep 6242183 = 9363275) B9363275
theorem B2809771 : Blo 1847625 2809771 := bstep (se 1 (by rfl) ⟨2107328, by rfl⟩ : syracuseStep 2809771 = 4214657) B4214657
theorem B3121159 : Blo 1847625 3121159 := bstep (se 1 (by rfl) ⟨2340869, by rfl⟩ : syracuseStep 3121159 = 4681739) B4681739
theorem B4677689 : Blo 1847625 4677689 := bstep (se 2 (by rfl) ⟨1754133, by rfl⟩ : syracuseStep 4677689 = 3508267) B3508267
theorem B3162361 : Blo 1847625 3162361 := bstep (se 2 (by rfl) ⟨1185885, by rfl⟩ : syracuseStep 3162361 = 2371771) B2371771
theorem B10273289 : Blo 1847625 10273289 := bstep (se 2 (by rfl) ⟨3852483, by rfl⟩ : syracuseStep 10273289 = 7704967) B7704967
theorem B6849209 : Blo 1847625 6849209 := bstep (se 2 (by rfl) ⟨2568453, by rfl⟩ : syracuseStep 6849209 = 5136907) B5136907
theorem B9355985 : Blo 1847625 9355985 := bstep (se 2 (by rfl) ⟨3508494, by rfl⟩ : syracuseStep 9355985 = 7016989) B7016989
theorem B59294537 : Blo 1847625 59294537 := bstep (se 2 (by rfl) ⟨22235451, by rfl⟩ : syracuseStep 59294537 = 44470903) B44470903
theorem B15786859 : Blo 1847625 15786859 := bstep (se 1 (by rfl) ⟨11840144, by rfl⟩ : syracuseStep 15786859 = 23680289) B23680289
theorem B3556271 : Blo 1847625 3556271 := bstep (se 1 (by rfl) ⟨2667203, by rfl⟩ : syracuseStep 3556271 = 5334407) B5334407
theorem B10527671 : Blo 1847625 10527671 := bstep (se 1 (by rfl) ⟨7895753, by rfl⟩ : syracuseStep 10527671 = 15791507) B15791507
theorem B30376907 : Blo 1847625 30376907 := bstep (se 1 (by rfl) ⟨22782680, by rfl⟩ : syracuseStep 30376907 = 45565361) B45565361
theorem B14992451 : Blo 1847625 14992451 := bstep (se 1 (by rfl) ⟨11244338, by rfl⟩ : syracuseStep 14992451 = 22488677) B22488677
theorem B6661235 : Blo 1847625 6661235 := bstep (se 1 (by rfl) ⟨4995926, by rfl⟩ : syracuseStep 6661235 = 9991853) B9991853
theorem B30811337 : Blo 1847625 30811337 := bstep (se 2 (by rfl) ⟨11554251, by rfl⟩ : syracuseStep 30811337 = 23108503) B23108503
theorem B9127115 : Blo 1847625 9127115 := bstep (se 1 (by rfl) ⟨6845336, by rfl⟩ : syracuseStep 9127115 = 13690673) B13690673
theorem B7021835 : Blo 1847625 7021835 := bstep (se 1 (by rfl) ⟨5266376, by rfl⟩ : syracuseStep 7021835 = 10532753) B10532753
theorem B14042483 : Blo 1847625 14042483 := bstep (se 1 (by rfl) ⟨10531862, by rfl⟩ : syracuseStep 14042483 = 21063725) B21063725
theorem B75867749 : Blo 1847625 75867749 := bstep (se 4 (by rfl) ⟨7112601, by rfl⟩ : syracuseStep 75867749 = 14225203) B14225203
theorem B10528379 : Blo 1847625 10528379 := bstep (se 1 (by rfl) ⟨7896284, by rfl⟩ : syracuseStep 10528379 = 15792569) B15792569
theorem B11839121 : Blo 1847625 11839121 := bstep (se 2 (by rfl) ⟨4439670, by rfl⟩ : syracuseStep 11839121 = 8879341) B8879341
theorem B15189869 : Blo 1847625 15189869 := bstep (se 3 (by rfl) ⟨2848100, by rfl⟩ : syracuseStep 15189869 = 5696201) B5696201
theorem B23701409 : Blo 1847625 23701409 := bstep (se 2 (by rfl) ⟨8888028, by rfl⟩ : syracuseStep 23701409 = 17776057) B17776057
theorem B6662159 : Blo 1847625 6662159 := bstep (se 1 (by rfl) ⟨4996619, by rfl⟩ : syracuseStep 6662159 = 9993239) B9993239
theorem B4442131 : Blo 1847625 4442131 := bstep (se 1 (by rfl) ⟨3331598, by rfl⟩ : syracuseStep 4442131 = 6663197) B6663197
theorem B2107471 : Blo 1847625 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B21334117 : Blo 1847625 21334117 := bstep (se 4 (by rfl) ⟨2000073, by rfl⟩ : syracuseStep 21334117 = 4000147) B4000147
theorem B14985445 : Blo 1847625 14985445 := bstep (se 4 (by rfl) ⟨1404885, by rfl⟩ : syracuseStep 14985445 = 2809771) B2809771
theorem B4679927 : Blo 1847625 4679927 := bstep (se 1 (by rfl) ⟨3509945, by rfl⟩ : syracuseStep 4679927 = 7019891) B7019891
theorem B14420285 : Blo 1847625 14420285 := bstep (se 3 (by rfl) ⟨2703803, by rfl⟩ : syracuseStep 14420285 = 5407607) B5407607
theorem B10529129 : Blo 1847625 10529129 := bstep (se 2 (by rfl) ⟨3948423, by rfl⟩ : syracuseStep 10529129 = 7896847) B7896847
theorem B2771465 : Blo 1847625 2771465 := bstep (se 2 (by rfl) ⟨1039299, by rfl⟩ : syracuseStep 2771465 = 2078599) B2078599
theorem B5335561 : Blo 1847625 5335561 := bstep (se 2 (by rfl) ⟨2000835, by rfl⟩ : syracuseStep 5335561 = 4001671) B4001671
theorem B2771495 : Blo 1847625 2771495 := bstep (se 1 (by rfl) ⟨2078621, by rfl⟩ : syracuseStep 2771495 = 4157243) B4157243
theorem B2771579 : Blo 1847625 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B3508859 : Blo 1847625 3508859 := bstep (se 1 (by rfl) ⟨2631644, by rfl⟩ : syracuseStep 3508859 = 5263289) B5263289
theorem B5262013 : Blo 1847625 5262013 := bstep (se 3 (by rfl) ⟨986627, by rfl⟩ : syracuseStep 5262013 = 1973255) B1973255
theorem B2771705 : Blo 1847625 2771705 := bstep (se 2 (by rfl) ⟨1039389, by rfl⟩ : syracuseStep 2771705 = 2078779) B2078779
theorem B2771807 : Blo 1847625 2771807 := bstep (se 1 (by rfl) ⟨2078855, by rfl⟩ : syracuseStep 2771807 = 4157711) B4157711
theorem B2771819 : Blo 1847625 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B5262241 : Blo 1847625 5262241 := bstep (se 2 (by rfl) ⟨1973340, by rfl⟩ : syracuseStep 5262241 = 3946681) B3946681
theorem B11840555 : Blo 1847625 11840555 := bstep (se 1 (by rfl) ⟨8880416, by rfl⟩ : syracuseStep 11840555 = 17760833) B17760833
theorem B2772047 : Blo 1847625 2772047 := bstep (se 1 (by rfl) ⟨2079035, by rfl⟩ : syracuseStep 2772047 = 4158071) B4158071
theorem B9358415 : Blo 1847625 9358415 := bstep (se 1 (by rfl) ⟨7018811, by rfl⟩ : syracuseStep 9358415 = 14037623) B14037623
theorem B3509345 : Blo 1847625 3509345 := bstep (se 2 (by rfl) ⟨1316004, by rfl⟩ : syracuseStep 3509345 = 2632009) B2632009
theorem B2772167 : Blo 1847625 2772167 := bstep (se 1 (by rfl) ⟨2079125, by rfl⟩ : syracuseStep 2772167 = 4158251) B4158251
theorem B5262583 : Blo 1847625 5262583 := bstep (se 1 (by rfl) ⟨3946937, by rfl⟩ : syracuseStep 5262583 = 7893875) B7893875
theorem B6237431 : Blo 1847625 6237431 := bstep (se 1 (by rfl) ⟨4678073, by rfl⟩ : syracuseStep 6237431 = 9356147) B9356147
theorem B3509497 : Blo 1847625 3509497 := bstep (se 2 (by rfl) ⟨1316061, by rfl⟩ : syracuseStep 3509497 = 2632123) B2632123
theorem B6663485 : Blo 1847625 6663485 := bstep (se 3 (by rfl) ⟨1249403, by rfl⟩ : syracuseStep 6663485 = 2498807) B2498807
theorem B2772329 : Blo 1847625 2772329 := bstep (se 2 (by rfl) ⟨1039623, by rfl⟩ : syracuseStep 2772329 = 2079247) B2079247
theorem B7015805 : Blo 1847625 7015805 := bstep (se 3 (by rfl) ⟨1315463, by rfl⟩ : syracuseStep 7015805 = 2630927) B2630927
theorem B13323683 : Blo 1847625 13323683 := bstep (se 1 (by rfl) ⟨9992762, by rfl⟩ : syracuseStep 13323683 = 19985525) B19985525
theorem B2772407 : Blo 1847625 2772407 := bstep (se 1 (by rfl) ⟨2079305, by rfl⟩ : syracuseStep 2772407 = 4158611) B4158611
theorem B2633143 : Blo 1847625 2633143 := bstep (se 1 (by rfl) ⟨1974857, by rfl⟩ : syracuseStep 2633143 = 3949715) B3949715
theorem B2772443 : Blo 1847625 2772443 := bstep (se 1 (by rfl) ⟨2079332, by rfl⟩ : syracuseStep 2772443 = 4158665) B4158665
theorem B29978099 : Blo 1847625 29978099 := bstep (se 1 (by rfl) ⟨22483574, by rfl⟩ : syracuseStep 29978099 = 44967149) B44967149
theorem B5262857 : Blo 1847625 5262857 := bstep (se 2 (by rfl) ⟨1973571, by rfl⟩ : syracuseStep 5262857 = 3947143) B3947143
theorem B6237755 : Blo 1847625 6237755 := bstep (se 1 (by rfl) ⟨4678316, by rfl⟩ : syracuseStep 6237755 = 9356633) B9356633
theorem B37957207 : Blo 1847625 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B4443745 : Blo 1847625 4443745 := bstep (se 2 (by rfl) ⟨1666404, by rfl⟩ : syracuseStep 4443745 = 3332809) B3332809
theorem B4681415 : Blo 1847625 4681415 := bstep (se 1 (by rfl) ⟨3511061, by rfl⟩ : syracuseStep 4681415 = 7022123) B7022123
theorem B9359063 : Blo 1847625 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B6238025 : Blo 1847625 6238025 := bstep (se 2 (by rfl) ⟨2339259, by rfl⟩ : syracuseStep 6238025 = 4678519) B4678519
theorem B4443977 : Blo 1847625 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B4157279 : Blo 1847625 4157279 := bstep (se 1 (by rfl) ⟨3117959, by rfl⟩ : syracuseStep 4157279 = 6235919) B6235919
theorem B5066657 : Blo 1847625 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B2772911 : Blo 1847625 2772911 := bstep (se 1 (by rfl) ⟨2079683, by rfl⟩ : syracuseStep 2772911 = 4159367) B4159367
theorem B2773001 : Blo 1847625 2773001 := bstep (se 2 (by rfl) ⟨1039875, by rfl⟩ : syracuseStep 2773001 = 2079751) B2079751
theorem B4157459 : Blo 1847625 4157459 := bstep (se 1 (by rfl) ⟨3118094, by rfl⟩ : syracuseStep 4157459 = 6236189) B6236189
theorem B2773031 : Blo 1847625 2773031 := bstep (se 1 (by rfl) ⟨2079773, by rfl⟩ : syracuseStep 2773031 = 4159547) B4159547
theorem B2338895 : Blo 1847625 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B5066831 : Blo 1847625 5066831 := bstep (se 1 (by rfl) ⟨3800123, by rfl⟩ : syracuseStep 5066831 = 7600247) B7600247
theorem B2773115 : Blo 1847625 2773115 := bstep (se 1 (by rfl) ⟨2079836, by rfl⟩ : syracuseStep 2773115 = 4159673) B4159673
theorem B5263517 : Blo 1847625 5263517 := bstep (se 3 (by rfl) ⟨986909, by rfl⟩ : syracuseStep 5263517 = 1973819) B1973819
theorem B11849885 : Blo 1847625 11849885 := bstep (se 3 (by rfl) ⟨2221853, by rfl⟩ : syracuseStep 11849885 = 4443707) B4443707
theorem B47370419 : Blo 1847625 47370419 := bstep (se 1 (by rfl) ⟨35527814, by rfl⟩ : syracuseStep 47370419 = 71055629) B71055629
theorem B2773241 : Blo 1847625 2773241 := bstep (se 2 (by rfl) ⟨1039965, by rfl⟩ : syracuseStep 2773241 = 2079931) B2079931
theorem B1847631 : Blo 1847625 1847631 := bstep (se 1 (by rfl) ⟨1385723, by rfl⟩ : syracuseStep 1847631 = 2771447) B2771447
theorem B1847647 : Blo 1847625 1847647 := bstep (se 1 (by rfl) ⟨1385735, by rfl⟩ : syracuseStep 1847647 = 2771471) B2771471
theorem B2773343 : Blo 1847625 2773343 := bstep (se 1 (by rfl) ⟨2080007, by rfl⟩ : syracuseStep 2773343 = 4160015) B4160015
theorem B4157801 : Blo 1847625 4157801 := bstep (se 2 (by rfl) ⟨1559175, by rfl⟩ : syracuseStep 4157801 = 3118351) B3118351
theorem B2773355 : Blo 1847625 2773355 := bstep (se 1 (by rfl) ⟨2080016, by rfl⟩ : syracuseStep 2773355 = 4160033) B4160033
theorem B1847675 : Blo 1847625 1847675 := bstep (se 1 (by rfl) ⟨1385756, by rfl⟩ : syracuseStep 1847675 = 2771513) B2771513
theorem B1847727 : Blo 1847625 1847727 := bstep (se 1 (by rfl) ⟨1385795, by rfl⟩ : syracuseStep 1847727 = 2771591) B2771591
theorem B1847751 : Blo 1847625 1847751 := bstep (se 1 (by rfl) ⟨1385813, by rfl⟩ : syracuseStep 1847751 = 2771627) B2771627
theorem B1847771 : Blo 1847625 1847771 := bstep (se 1 (by rfl) ⟨1385828, by rfl⟩ : syracuseStep 1847771 = 2771657) B2771657
theorem B5263859 : Blo 1847625 5263859 := bstep (se 1 (by rfl) ⟨3947894, by rfl⟩ : syracuseStep 5263859 = 7895789) B7895789
theorem B3510803 : Blo 1847625 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B1847847 : Blo 1847625 1847847 := bstep (se 1 (by rfl) ⟨1385885, by rfl⟩ : syracuseStep 1847847 = 2771771) B2771771
theorem B1847887 : Blo 1847625 1847887 := bstep (se 1 (by rfl) ⟨1385915, by rfl⟩ : syracuseStep 1847887 = 2771831) B2771831
theorem B2773583 : Blo 1847625 2773583 := bstep (se 1 (by rfl) ⟨2080187, by rfl⟩ : syracuseStep 2773583 = 4160375) B4160375
theorem B1847903 : Blo 1847625 1847903 := bstep (se 1 (by rfl) ⟨1385927, by rfl⟩ : syracuseStep 1847903 = 2771855) B2771855
theorem B5919355 : Blo 1847625 5919355 := bstep (se 1 (by rfl) ⟨4439516, by rfl⟩ : syracuseStep 5919355 = 8879033) B8879033
theorem B1847931 : Blo 1847625 1847931 := bstep (se 1 (by rfl) ⟨1385948, by rfl⟩ : syracuseStep 1847931 = 2771897) B2771897
theorem B1847983 : Blo 1847625 1847983 := bstep (se 1 (by rfl) ⟨1385987, by rfl⟩ : syracuseStep 1847983 = 2771975) B2771975
theorem B3510955 : Blo 1847625 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B1848007 : Blo 1847625 1848007 := bstep (se 1 (by rfl) ⟨1386005, by rfl⟩ : syracuseStep 1848007 = 2772011) B2772011
theorem B2773703 : Blo 1847625 2773703 := bstep (se 1 (by rfl) ⟨2080277, by rfl⟩ : syracuseStep 2773703 = 4160555) B4160555
theorem B1848027 : Blo 1847625 1848027 := bstep (se 1 (by rfl) ⟨1386020, by rfl⟩ : syracuseStep 1848027 = 2772041) B2772041
theorem B1848103 : Blo 1847625 1848103 := bstep (se 1 (by rfl) ⟨1386077, by rfl⟩ : syracuseStep 1848103 = 2772155) B2772155
theorem B1848143 : Blo 1847625 1848143 := bstep (se 1 (by rfl) ⟨1386107, by rfl⟩ : syracuseStep 1848143 = 2772215) B2772215
theorem B3117919 : Blo 1847625 3117919 := bstep (se 1 (by rfl) ⟨2338439, by rfl⟩ : syracuseStep 3117919 = 4676879) B4676879
theorem B1848159 : Blo 1847625 1848159 := bstep (se 1 (by rfl) ⟨1386119, by rfl⟩ : syracuseStep 1848159 = 2772239) B2772239
theorem B2773865 : Blo 1847625 2773865 := bstep (se 2 (by rfl) ⟨1040199, by rfl⟩ : syracuseStep 2773865 = 2080399) B2080399
theorem B1848187 : Blo 1847625 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B3511183 : Blo 1847625 3511183 := bstep (se 1 (by rfl) ⟨2633387, by rfl⟩ : syracuseStep 3511183 = 5266775) B5266775
theorem B1848239 : Blo 1847625 1848239 := bstep (se 1 (by rfl) ⟨1386179, by rfl⟩ : syracuseStep 1848239 = 2772359) B2772359
theorem B3118007 : Blo 1847625 3118007 := bstep (se 1 (by rfl) ⟨2338505, by rfl⟩ : syracuseStep 3118007 = 4677011) B4677011
theorem B10671031 : Blo 1847625 10671031 := bstep (se 1 (by rfl) ⟨8003273, by rfl⟩ : syracuseStep 10671031 = 16006547) B16006547
theorem B6239159 : Blo 1847625 6239159 := bstep (se 1 (by rfl) ⟨4679369, by rfl⟩ : syracuseStep 6239159 = 9358739) B9358739
theorem B4158395 : Blo 1847625 4158395 := bstep (se 1 (by rfl) ⟨3118796, by rfl⟩ : syracuseStep 4158395 = 6237593) B6237593
theorem B5264315 : Blo 1847625 5264315 := bstep (se 1 (by rfl) ⟨3948236, by rfl⟩ : syracuseStep 5264315 = 7896473) B7896473
theorem B2773943 : Blo 1847625 2773943 := bstep (se 1 (by rfl) ⟨2080457, by rfl⟩ : syracuseStep 2773943 = 4160915) B4160915
theorem B1848263 : Blo 1847625 1848263 := bstep (se 1 (by rfl) ⟨1386197, by rfl⟩ : syracuseStep 1848263 = 2772395) B2772395
theorem B1848283 : Blo 1847625 1848283 := bstep (se 1 (by rfl) ⟨1386212, by rfl⟩ : syracuseStep 1848283 = 2772425) B2772425
theorem B12645341 : Blo 1847625 12645341 := bstep (se 3 (by rfl) ⟨2371001, by rfl⟩ : syracuseStep 12645341 = 4742003) B4742003
theorem B2773979 : Blo 1847625 2773979 := bstep (se 1 (by rfl) ⟨2080484, by rfl⟩ : syracuseStep 2773979 = 4160969) B4160969
theorem B3511259 : Blo 1847625 3511259 := bstep (se 1 (by rfl) ⟨2633444, by rfl⟩ : syracuseStep 3511259 = 5266889) B5266889
theorem B1848359 : Blo 1847625 1848359 := bstep (se 1 (by rfl) ⟨1386269, by rfl⟩ : syracuseStep 1848359 = 2772539) B2772539
theorem B4158521 : Blo 1847625 4158521 := bstep (se 2 (by rfl) ⟨1559445, by rfl⟩ : syracuseStep 4158521 = 3118891) B3118891
theorem B6665273 : Blo 1847625 6665273 := bstep (se 2 (by rfl) ⟨2499477, by rfl⟩ : syracuseStep 6665273 = 4998955) B4998955
theorem B1848399 : Blo 1847625 1848399 := bstep (se 1 (by rfl) ⟨1386299, by rfl⟩ : syracuseStep 1848399 = 2772599) B2772599
theorem B1848415 : Blo 1847625 1848415 := bstep (se 1 (by rfl) ⟨1386311, by rfl⟩ : syracuseStep 1848415 = 2772623) B2772623
theorem B1848443 : Blo 1847625 1848443 := bstep (se 1 (by rfl) ⟨1386332, by rfl⟩ : syracuseStep 1848443 = 2772665) B2772665
theorem B1848495 : Blo 1847625 1848495 := bstep (se 1 (by rfl) ⟨1386371, by rfl⟩ : syracuseStep 1848495 = 2772743) B2772743
theorem B1848519 : Blo 1847625 1848519 := bstep (se 1 (by rfl) ⟨1386389, by rfl⟩ : syracuseStep 1848519 = 2772779) B2772779
theorem B1848539 : Blo 1847625 1848539 := bstep (se 1 (by rfl) ⟨1386404, by rfl⟩ : syracuseStep 1848539 = 2772809) B2772809
theorem B14988559 : Blo 1847625 14988559 := bstep (se 1 (by rfl) ⟨11241419, by rfl⟩ : syracuseStep 14988559 = 22482839) B22482839
theorem B1848615 : Blo 1847625 1848615 := bstep (se 1 (by rfl) ⟨1386461, by rfl⟩ : syracuseStep 1848615 = 2772923) B2772923
theorem B1848655 : Blo 1847625 1848655 := bstep (se 1 (by rfl) ⟨1386491, by rfl⟩ : syracuseStep 1848655 = 2772983) B2772983
theorem B1848671 : Blo 1847625 1848671 := bstep (se 1 (by rfl) ⟨1386503, by rfl⟩ : syracuseStep 1848671 = 2773007) B2773007
theorem B2340191 : Blo 1847625 2340191 := bstep (se 1 (by rfl) ⟨1755143, by rfl⟩ : syracuseStep 2340191 = 3510287) B3510287
theorem B73037155 : Blo 1847625 73037155 := bstep (se 1 (by rfl) ⟨54777866, by rfl⟩ : syracuseStep 73037155 = 109555733) B109555733
theorem B1848699 : Blo 1847625 1848699 := bstep (se 1 (by rfl) ⟨1386524, by rfl⟩ : syracuseStep 1848699 = 2773049) B2773049
theorem B4158863 : Blo 1847625 4158863 := bstep (se 1 (by rfl) ⟨3119147, by rfl⟩ : syracuseStep 4158863 = 6238295) B6238295
theorem B1848751 : Blo 1847625 1848751 := bstep (se 1 (by rfl) ⟨1386563, by rfl⟩ : syracuseStep 1848751 = 2773127) B2773127
theorem B1848775 : Blo 1847625 1848775 := bstep (se 1 (by rfl) ⟨1386581, by rfl⟩ : syracuseStep 1848775 = 2773163) B2773163
theorem B7017947 : Blo 1847625 7017947 := bstep (se 1 (by rfl) ⟨5263460, by rfl⟩ : syracuseStep 7017947 = 10526921) B10526921
theorem B1848795 : Blo 1847625 1848795 := bstep (se 1 (by rfl) ⟨1386596, by rfl⟩ : syracuseStep 1848795 = 2773193) B2773193
theorem B3118601 : Blo 1847625 3118601 := bstep (se 2 (by rfl) ⟨1169475, by rfl⟩ : syracuseStep 3118601 = 2338951) B2338951
theorem B6239753 : Blo 1847625 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B1848871 : Blo 1847625 1848871 := bstep (se 1 (by rfl) ⟨1386653, by rfl⟩ : syracuseStep 1848871 = 2773307) B2773307
theorem B1848911 : Blo 1847625 1848911 := bstep (se 1 (by rfl) ⟨1386683, by rfl⟩ : syracuseStep 1848911 = 2773367) B2773367
theorem B1848927 : Blo 1847625 1848927 := bstep (se 1 (by rfl) ⟨1386695, by rfl⟩ : syracuseStep 1848927 = 2773391) B2773391
theorem B1848955 : Blo 1847625 1848955 := bstep (se 1 (by rfl) ⟨1386716, by rfl⟩ : syracuseStep 1848955 = 2773433) B2773433
theorem B3118763 : Blo 1847625 3118763 := bstep (se 1 (by rfl) ⟨2339072, by rfl⟩ : syracuseStep 3118763 = 4678145) B4678145
theorem B1849007 : Blo 1847625 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B4216519 : Blo 1847625 4216519 := bstep (se 1 (by rfl) ⟨3162389, by rfl⟩ : syracuseStep 4216519 = 6324779) B6324779
theorem B1849031 : Blo 1847625 1849031 := bstep (se 1 (by rfl) ⟨1386773, by rfl⟩ : syracuseStep 1849031 = 2773547) B2773547
theorem B4159187 : Blo 1847625 4159187 := bstep (se 1 (by rfl) ⟨3119390, by rfl⟩ : syracuseStep 4159187 = 6238781) B6238781
theorem B1849051 : Blo 1847625 1849051 := bstep (se 1 (by rfl) ⟨1386788, by rfl⟩ : syracuseStep 1849051 = 2773577) B2773577
theorem B50616065 : Blo 1847625 50616065 := bstep (se 2 (by rfl) ⟨18981024, by rfl⟩ : syracuseStep 50616065 = 37962049) B37962049
theorem B1849127 : Blo 1847625 1849127 := bstep (se 1 (by rfl) ⟨1386845, by rfl⟩ : syracuseStep 1849127 = 2773691) B2773691
theorem B1849167 : Blo 1847625 1849167 := bstep (se 1 (by rfl) ⟨1386875, by rfl⟩ : syracuseStep 1849167 = 2773751) B2773751
theorem B1849183 : Blo 1847625 1849183 := bstep (se 1 (by rfl) ⟨1386887, by rfl⟩ : syracuseStep 1849183 = 2773775) B2773775
theorem B6666079 : Blo 1847625 6666079 := bstep (se 1 (by rfl) ⟨4999559, by rfl⟩ : syracuseStep 6666079 = 9999119) B9999119
theorem B1849211 : Blo 1847625 1849211 := bstep (se 1 (by rfl) ⟨1386908, by rfl⟩ : syracuseStep 1849211 = 2773817) B2773817
theorem B1849263 : Blo 1847625 1849263 := bstep (se 1 (by rfl) ⟨1386947, by rfl⟩ : syracuseStep 1849263 = 2773895) B2773895
theorem B1849287 : Blo 1847625 1849287 := bstep (se 1 (by rfl) ⟨1386965, by rfl⟩ : syracuseStep 1849287 = 2773931) B2773931
theorem B1849307 : Blo 1847625 1849307 := bstep (se 1 (by rfl) ⟨1386980, by rfl⟩ : syracuseStep 1849307 = 2773961) B2773961
theorem B1849383 : Blo 1847625 1849383 := bstep (se 1 (by rfl) ⟨1387037, by rfl⟩ : syracuseStep 1849383 = 2774075) B2774075
theorem B3119161 : Blo 1847625 3119161 := bstep (se 2 (by rfl) ⟨1169685, by rfl⟩ : syracuseStep 3119161 = 2339371) B2339371
theorem B1849423 : Blo 1847625 1849423 := bstep (se 1 (by rfl) ⟨1387067, by rfl⟩ : syracuseStep 1849423 = 2774135) B2774135
theorem B1849439 : Blo 1847625 1849439 := bstep (se 1 (by rfl) ⟨1387079, by rfl⟩ : syracuseStep 1849439 = 2774159) B2774159
theorem B1849467 : Blo 1847625 1849467 := bstep (se 1 (by rfl) ⟨1387100, by rfl⟩ : syracuseStep 1849467 = 2774201) B2774201
theorem B1849519 : Blo 1847625 1849519 := bstep (se 1 (by rfl) ⟨1387139, by rfl⟩ : syracuseStep 1849519 = 2774279) B2774279
theorem B3119303 : Blo 1847625 3119303 := bstep (se 1 (by rfl) ⟨2339477, by rfl⟩ : syracuseStep 3119303 = 4678955) B4678955
theorem B1849543 : Blo 1847625 1849543 := bstep (se 1 (by rfl) ⟨1387157, by rfl⟩ : syracuseStep 1849543 = 2774315) B2774315
theorem B1849563 : Blo 1847625 1849563 := bstep (se 1 (by rfl) ⟨1387172, by rfl⟩ : syracuseStep 1849563 = 2774345) B2774345
theorem B3119465 : Blo 1847625 3119465 := bstep (se 2 (by rfl) ⟨1169799, by rfl⟩ : syracuseStep 3119465 = 2339599) B2339599
theorem B6240617 : Blo 1847625 6240617 := bstep (se 2 (by rfl) ⟨2340231, by rfl⟩ : syracuseStep 6240617 = 4680463) B4680463
theorem B9361979 : Blo 1847625 9361979 := bstep (se 1 (by rfl) ⟨7021484, by rfl⟩ : syracuseStep 9361979 = 14042969) B14042969
theorem B2079355 : Blo 1847625 2079355 := bstep (se 1 (by rfl) ⟨1559516, by rfl⟩ : syracuseStep 2079355 = 3119033) B3119033
theorem B4160123 : Blo 1847625 4160123 := bstep (se 1 (by rfl) ⟨3120092, by rfl⟩ : syracuseStep 4160123 = 6240185) B6240185
theorem B29989511 : Blo 1847625 29989511 := bstep (se 1 (by rfl) ⟨22492133, by rfl⟩ : syracuseStep 29989511 = 44984267) B44984267
theorem B7019207 : Blo 1847625 7019207 := bstep (se 1 (by rfl) ⟨5264405, by rfl⟩ : syracuseStep 7019207 = 10528811) B10528811
theorem B3119863 : Blo 1847625 3119863 := bstep (se 1 (by rfl) ⟨2339897, by rfl⟩ : syracuseStep 3119863 = 4679795) B4679795
theorem B4160249 : Blo 1847625 4160249 := bstep (se 2 (by rfl) ⟨1560093, by rfl⟩ : syracuseStep 4160249 = 3120187) B3120187
theorem B14031791 : Blo 1847625 14031791 := bstep (se 1 (by rfl) ⟨10523843, by rfl⟩ : syracuseStep 14031791 = 21047687) B21047687
theorem B3120059 : Blo 1847625 3120059 := bstep (se 1 (by rfl) ⟨2340044, by rfl⟩ : syracuseStep 3120059 = 4680089) B4680089
theorem B6241211 : Blo 1847625 6241211 := bstep (se 1 (by rfl) ⟨4680908, by rfl⟩ : syracuseStep 6241211 = 9361817) B9361817
theorem B4160519 : Blo 1847625 4160519 := bstep (se 1 (by rfl) ⟨3120389, by rfl⟩ : syracuseStep 4160519 = 6240779) B6240779
theorem B3120167 : Blo 1847625 3120167 := bstep (se 1 (by rfl) ⟨2340125, by rfl⟩ : syracuseStep 3120167 = 4680251) B4680251
theorem B106642493 : Blo 1847625 106642493 := bstep (se 3 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 106642493 = 39990935) B39990935
theorem B2079823 : Blo 1847625 2079823 := bstep (se 1 (by rfl) ⟨1559867, by rfl⟩ : syracuseStep 2079823 = 3119735) B3119735
theorem B4160591 : Blo 1847625 4160591 := bstep (se 1 (by rfl) ⟨3120443, by rfl⟩ : syracuseStep 4160591 = 6240887) B6240887
theorem B9362627 : Blo 1847625 9362627 := bstep (se 1 (by rfl) ⟨7021970, by rfl⟩ : syracuseStep 9362627 = 14043941) B14043941
theorem B3120457 : Blo 1847625 3120457 := bstep (se 2 (by rfl) ⟨1170171, by rfl⟩ : syracuseStep 3120457 = 2340343) B2340343
theorem B3120491 : Blo 1847625 3120491 := bstep (se 1 (by rfl) ⟨2340368, by rfl⟩ : syracuseStep 3120491 = 4680737) B4680737
theorem B18972029 : Blo 1847625 18972029 := bstep (se 3 (by rfl) ⟨3557255, by rfl⟩ : syracuseStep 18972029 = 7114511) B7114511
theorem B7019905 : Blo 1847625 7019905 := bstep (se 2 (by rfl) ⟨2632464, by rfl⟩ : syracuseStep 7019905 = 5264929) B5264929
theorem B14040539 : Blo 1847625 14040539 := bstep (se 1 (by rfl) ⟨10530404, by rfl⟩ : syracuseStep 14040539 = 21060809) B21060809
theorem B2080219 : Blo 1847625 2080219 := bstep (se 1 (by rfl) ⟨1560164, by rfl⟩ : syracuseStep 2080219 = 3120329) B3120329
theorem B4160987 : Blo 1847625 4160987 := bstep (se 1 (by rfl) ⟨3120740, by rfl⟩ : syracuseStep 4160987 = 6241481) B6241481
theorem B7020179 : Blo 1847625 7020179 := bstep (se 1 (by rfl) ⟨5265134, by rfl⟩ : syracuseStep 7020179 = 10530269) B10530269
theorem B6659795 : Blo 1847625 6659795 := bstep (se 1 (by rfl) ⟨4994846, by rfl⟩ : syracuseStep 6659795 = 9989693) B9989693
theorem B4677335 : Blo 1847625 4677335 := bstep (se 1 (by rfl) ⟨3508001, by rfl⟩ : syracuseStep 4677335 = 7016003) B7016003
theorem B3120889 : Blo 1847625 3120889 := bstep (se 2 (by rfl) ⟨1170333, by rfl⟩ : syracuseStep 3120889 = 2340667) B2340667
theorem B8879939 : Blo 1847625 8879939 := bstep (se 1 (by rfl) ⟨6659954, by rfl⟩ : syracuseStep 8879939 = 13319909) B13319909
theorem B2080687 : Blo 1847625 2080687 := bstep (se 1 (by rfl) ⟨1560515, by rfl⟩ : syracuseStep 2080687 = 3121031) B3121031
theorem B4161455 : Blo 1847625 4161455 := bstep (se 1 (by rfl) ⟨3121091, by rfl⟩ : syracuseStep 4161455 = 6242183) B6242183
theorem B14041025 : Blo 1847625 14041025 := bstep (se 2 (by rfl) ⟨5265384, by rfl⟩ : syracuseStep 14041025 = 10530769) B10530769
theorem B4161545 : Blo 1847625 4161545 := bstep (se 2 (by rfl) ⟨1560579, by rfl⟩ : syracuseStep 4161545 = 3121159) B3121159
theorem B5922841 : Blo 1847625 5922841 := bstep (se 2 (by rfl) ⟨2221065, by rfl⟩ : syracuseStep 5922841 = 4442131) B4442131
theorem B2809961 : Blo 1847625 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B31580279 : Blo 1847625 31580279 := bstep (se 1 (by rfl) ⟨23685209, by rfl⟩ : syracuseStep 31580279 = 47370419) B47370419
theorem B19980593 : Blo 1847625 19980593 := bstep (se 2 (by rfl) ⟨7492722, by rfl⟩ : syracuseStep 19980593 = 14985445) B14985445
theorem B20251271 : Blo 1847625 20251271 := bstep (se 1 (by rfl) ⟨15188453, by rfl⟩ : syracuseStep 20251271 = 30376907) B30376907
theorem B8430227 : Blo 1847625 8430227 := bstep (se 1 (by rfl) ⟨6322670, by rfl⟩ : syracuseStep 8430227 = 12645341) B12645341
theorem B9994967 : Blo 1847625 9994967 := bstep (se 1 (by rfl) ⟨7496225, by rfl⟩ : syracuseStep 9994967 = 14992451) B14992451
theorem B17769293 : Blo 1847625 17769293 := bstep (se 3 (by rfl) ⟨3331742, by rfl⟩ : syracuseStep 17769293 = 6663485) B6663485
theorem B4678631 : Blo 1847625 4678631 := bstep (se 1 (by rfl) ⟨3508973, by rfl⟩ : syracuseStep 4678631 = 7017947) B7017947
theorem B22488101 : Blo 1847625 22488101 := bstep (se 4 (by rfl) ⟨2108259, by rfl⟩ : syracuseStep 22488101 = 4216519) B4216519
theorem B50578499 : Blo 1847625 50578499 := bstep (se 1 (by rfl) ⟨37933874, by rfl⟩ : syracuseStep 50578499 = 75867749) B75867749
theorem B33744043 : Blo 1847625 33744043 := bstep (se 1 (by rfl) ⟨25308032, by rfl⟩ : syracuseStep 33744043 = 50616065) B50616065
theorem B4441439 : Blo 1847625 4441439 := bstep (se 1 (by rfl) ⟨3331079, by rfl⟩ : syracuseStep 4441439 = 6662159) B6662159
theorem B27395437 : Blo 1847625 27395437 := bstep (se 3 (by rfl) ⟨5136644, by rfl⟩ : syracuseStep 27395437 = 10273289) B10273289
theorem B9356957 : Blo 1847625 9356957 := bstep (se 3 (by rfl) ⟨1754429, by rfl⟩ : syracuseStep 9356957 = 3508859) B3508859
theorem B4679329 : Blo 1847625 4679329 := bstep (se 2 (by rfl) ⟨1754748, by rfl⟩ : syracuseStep 4679329 = 3509497) B3509497
theorem B4679471 : Blo 1847625 4679471 := bstep (se 1 (by rfl) ⟨3509603, by rfl⟩ : syracuseStep 4679471 = 7019207) B7019207
theorem B5924993 : Blo 1847625 5924993 := bstep (se 2 (by rfl) ⟨2221872, by rfl⟩ : syracuseStep 5924993 = 4443745) B4443745
theorem B8882455 : Blo 1847625 8882455 := bstep (se 1 (by rfl) ⟨6661841, by rfl⟩ : syracuseStep 8882455 = 13323683) B13323683
theorem B56912165 : Blo 1847625 56912165 := bstep (se 4 (by rfl) ⟨5335515, by rfl⟩ : syracuseStep 56912165 = 10671031) B10671031
theorem B3508571 : Blo 1847625 3508571 := bstep (se 1 (by rfl) ⟨2631428, by rfl⟩ : syracuseStep 3508571 = 5262857) B5262857
theorem B4680119 : Blo 1847625 4680119 := bstep (se 1 (by rfl) ⟨3510089, by rfl⟩ : syracuseStep 4680119 = 7020179) B7020179
theorem B2771519 : Blo 1847625 2771519 := bstep (se 1 (by rfl) ⟨2078639, by rfl⟩ : syracuseStep 2771519 = 4157279) B4157279
theorem B3377771 : Blo 1847625 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B2771639 : Blo 1847625 2771639 := bstep (se 1 (by rfl) ⟨2078729, by rfl⟩ : syracuseStep 2771639 = 4157459) B4157459
theorem B3509011 : Blo 1847625 3509011 := bstep (se 1 (by rfl) ⟨2631758, by rfl⟩ : syracuseStep 3509011 = 5263517) B5263517
theorem B7899923 : Blo 1847625 7899923 := bstep (se 1 (by rfl) ⟨5924942, by rfl⟩ : syracuseStep 7899923 = 11849885) B11849885
theorem B28445489 : Blo 1847625 28445489 := bstep (se 2 (by rfl) ⟨10667058, by rfl⟩ : syracuseStep 28445489 = 21334117) B21334117
theorem B6237053 : Blo 1847625 6237053 := bstep (se 3 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 6237053 = 2338895) B2338895
theorem B13511549 : Blo 1847625 13511549 := bstep (se 3 (by rfl) ⟨2533415, by rfl⟩ : syracuseStep 13511549 = 5066831) B5066831
theorem B2771867 : Blo 1847625 2771867 := bstep (se 1 (by rfl) ⟨2078900, by rfl⟩ : syracuseStep 2771867 = 4157801) B4157801
theorem B9358253 : Blo 1847625 9358253 := bstep (se 3 (by rfl) ⟨1754672, by rfl⟩ : syracuseStep 9358253 = 3509345) B3509345
theorem B17763293 : Blo 1847625 17763293 := bstep (se 3 (by rfl) ⟨3330617, by rfl⟩ : syracuseStep 17763293 = 6661235) B6661235
theorem B3509239 : Blo 1847625 3509239 := bstep (se 1 (by rfl) ⟨2631929, by rfl⟩ : syracuseStep 3509239 = 5263859) B5263859
theorem B4566139 : Blo 1847625 4566139 := bstep (se 1 (by rfl) ⟨3424604, by rfl⟩ : syracuseStep 4566139 = 6849209) B6849209
theorem B6237323 : Blo 1847625 6237323 := bstep (se 1 (by rfl) ⟨4677992, by rfl⟩ : syracuseStep 6237323 = 9355985) B9355985
theorem B39529691 : Blo 1847625 39529691 := bstep (se 1 (by rfl) ⟨29647268, by rfl⟩ : syracuseStep 39529691 = 59294537) B59294537
theorem B2772263 : Blo 1847625 2772263 := bstep (se 1 (by rfl) ⟨2079197, by rfl⟩ : syracuseStep 2772263 = 4158395) B4158395
theorem B3509543 : Blo 1847625 3509543 := bstep (se 1 (by rfl) ⟨2632157, by rfl⟩ : syracuseStep 3509543 = 5264315) B5264315
theorem B7114081 : Blo 1847625 7114081 := bstep (se 2 (by rfl) ⟨2667780, by rfl⟩ : syracuseStep 7114081 = 5335561) B5335561
theorem B2772347 : Blo 1847625 2772347 := bstep (se 1 (by rfl) ⟨2079260, by rfl⟩ : syracuseStep 2772347 = 4158521) B4158521
theorem B4443515 : Blo 1847625 4443515 := bstep (se 1 (by rfl) ⟨3332636, by rfl⟩ : syracuseStep 4443515 = 6665273) B6665273
theorem B20540891 : Blo 1847625 20540891 := bstep (se 1 (by rfl) ⟨15405668, by rfl⟩ : syracuseStep 20540891 = 30811337) B30811337
theorem B7892473 : Blo 1847625 7892473 := bstep (se 2 (by rfl) ⟨2959677, by rfl⟩ : syracuseStep 7892473 = 5919355) B5919355
theorem B2772473 : Blo 1847625 2772473 := bstep (se 2 (by rfl) ⟨1039677, by rfl⟩ : syracuseStep 2772473 = 2079355) B2079355
theorem B4681223 : Blo 1847625 4681223 := bstep (se 1 (by rfl) ⟨3510917, by rfl⟩ : syracuseStep 4681223 = 7021835) B7021835
theorem B4681273 : Blo 1847625 4681273 := bstep (se 2 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 4681273 = 3510955) B3510955
theorem B7016017 : Blo 1847625 7016017 := bstep (se 2 (by rfl) ⟨2631006, by rfl⟩ : syracuseStep 7016017 = 5262013) B5262013
theorem B2772575 : Blo 1847625 2772575 := bstep (se 1 (by rfl) ⟨2079431, by rfl⟩ : syracuseStep 2772575 = 4158863) B4158863
theorem B7892747 : Blo 1847625 7892747 := bstep (se 1 (by rfl) ⟨5919560, by rfl⟩ : syracuseStep 7892747 = 11839121) B11839121
theorem B4157225 : Blo 1847625 4157225 := bstep (se 2 (by rfl) ⟨1558959, by rfl⟩ : syracuseStep 4157225 = 3117919) B3117919
theorem B2772791 : Blo 1847625 2772791 := bstep (se 1 (by rfl) ⟨2079593, by rfl⟩ : syracuseStep 2772791 = 4159187) B4159187
theorem B21049145 : Blo 1847625 21049145 := bstep (se 2 (by rfl) ⟨7893429, by rfl⟩ : syracuseStep 21049145 = 15786859) B15786859
theorem B4681577 : Blo 1847625 4681577 := bstep (se 2 (by rfl) ⟨1755591, by rfl⟩ : syracuseStep 4681577 = 3511183) B3511183
theorem B7016321 : Blo 1847625 7016321 := bstep (se 2 (by rfl) ⟨2631120, by rfl⟩ : syracuseStep 7016321 = 5262241) B5262241
theorem B2773097 : Blo 1847625 2773097 := bstep (se 2 (by rfl) ⟨1039911, by rfl⟩ : syracuseStep 2773097 = 2079823) B2079823
theorem B9613523 : Blo 1847625 9613523 := bstep (se 1 (by rfl) ⟨7210142, by rfl⟩ : syracuseStep 9613523 = 14420285) B14420285
theorem B7016777 : Blo 1847625 7016777 := bstep (se 2 (by rfl) ⟨2631291, by rfl⟩ : syracuseStep 7016777 = 5262583) B5262583
theorem B1847643 : Blo 1847625 1847643 := bstep (se 1 (by rfl) ⟨1385732, by rfl⟩ : syracuseStep 1847643 = 2771465) B2771465
theorem B19984745 : Blo 1847625 19984745 := bstep (se 2 (by rfl) ⟨7494279, by rfl⟩ : syracuseStep 19984745 = 14988559) B14988559
theorem B1847663 : Blo 1847625 1847663 := bstep (se 1 (by rfl) ⟨1385747, by rfl⟩ : syracuseStep 1847663 = 2771495) B2771495
theorem B1847719 : Blo 1847625 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B2773415 : Blo 1847625 2773415 := bstep (se 1 (by rfl) ⟨2080061, by rfl⟩ : syracuseStep 2773415 = 4160123) B4160123
theorem B19993007 : Blo 1847625 19993007 := bstep (se 1 (by rfl) ⟨14994755, by rfl⟩ : syracuseStep 19993007 = 29989511) B29989511
theorem B97382873 : Blo 1847625 97382873 := bstep (se 2 (by rfl) ⟨36518577, by rfl⟩ : syracuseStep 97382873 = 73037155) B73037155
theorem B1847803 : Blo 1847625 1847803 := bstep (se 1 (by rfl) ⟨1385852, by rfl⟩ : syracuseStep 1847803 = 2771705) B2771705
theorem B2773499 : Blo 1847625 2773499 := bstep (se 1 (by rfl) ⟨2080124, by rfl⟩ : syracuseStep 2773499 = 4160249) B4160249
theorem B9359873 : Blo 1847625 9359873 := bstep (se 2 (by rfl) ⟨3509952, by rfl⟩ : syracuseStep 9359873 = 7019905) B7019905
theorem B1847871 : Blo 1847625 1847871 := bstep (se 1 (by rfl) ⟨1385903, by rfl⟩ : syracuseStep 1847871 = 2771807) B2771807
theorem B1847879 : Blo 1847625 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B3510857 : Blo 1847625 3510857 := bstep (se 2 (by rfl) ⟨1316571, by rfl⟩ : syracuseStep 3510857 = 2633143) B2633143
theorem B2773625 : Blo 1847625 2773625 := bstep (se 2 (by rfl) ⟨1040109, by rfl⟩ : syracuseStep 2773625 = 2080219) B2080219
theorem B2773679 : Blo 1847625 2773679 := bstep (se 1 (by rfl) ⟨2080259, by rfl⟩ : syracuseStep 2773679 = 4160519) B4160519
theorem B7893703 : Blo 1847625 7893703 := bstep (se 1 (by rfl) ⟨5920277, by rfl⟩ : syracuseStep 7893703 = 11840555) B11840555
theorem B71094995 : Blo 1847625 71094995 := bstep (se 1 (by rfl) ⟨53321246, by rfl⟩ : syracuseStep 71094995 = 106642493) B106642493
theorem B1848031 : Blo 1847625 1848031 := bstep (se 1 (by rfl) ⟨1386023, by rfl⟩ : syracuseStep 1848031 = 2772047) B2772047
theorem B6238943 : Blo 1847625 6238943 := bstep (se 1 (by rfl) ⟨4679207, by rfl⟩ : syracuseStep 6238943 = 9358415) B9358415
theorem B2773727 : Blo 1847625 2773727 := bstep (se 1 (by rfl) ⟨2080295, by rfl⟩ : syracuseStep 2773727 = 4160591) B4160591
theorem B1848111 : Blo 1847625 1848111 := bstep (se 1 (by rfl) ⟨1386083, by rfl⟩ : syracuseStep 1848111 = 2772167) B2772167
theorem B4158287 : Blo 1847625 4158287 := bstep (se 1 (by rfl) ⟨3118715, by rfl⟩ : syracuseStep 4158287 = 6237431) B6237431
theorem B1848219 : Blo 1847625 1848219 := bstep (se 1 (by rfl) ⟨1386164, by rfl⟩ : syracuseStep 1848219 = 2772329) B2772329
theorem B40506317 : Blo 1847625 40506317 := bstep (se 3 (by rfl) ⟨7594934, by rfl⟩ : syracuseStep 40506317 = 15189869) B15189869
theorem B1848271 : Blo 1847625 1848271 := bstep (se 1 (by rfl) ⟨1386203, by rfl⟩ : syracuseStep 1848271 = 2772407) B2772407
theorem B1848295 : Blo 1847625 1848295 := bstep (se 1 (by rfl) ⟨1386221, by rfl⟩ : syracuseStep 1848295 = 2772443) B2772443
theorem B9360359 : Blo 1847625 9360359 := bstep (se 1 (by rfl) ⟨7020269, by rfl⟩ : syracuseStep 9360359 = 14040539) B14040539
theorem B2773991 : Blo 1847625 2773991 := bstep (se 1 (by rfl) ⟨2080493, by rfl⟩ : syracuseStep 2773991 = 4160987) B4160987
theorem B19985399 : Blo 1847625 19985399 := bstep (se 1 (by rfl) ⟨14989049, by rfl⟩ : syracuseStep 19985399 = 29978099) B29978099
theorem B4158503 : Blo 1847625 4158503 := bstep (se 1 (by rfl) ⟨3118877, by rfl⟩ : syracuseStep 4158503 = 6237755) B6237755
theorem B9483389 : Blo 1847625 9483389 := bstep (se 3 (by rfl) ⟨1778135, by rfl⟩ : syracuseStep 9483389 = 3556271) B3556271
theorem B3118223 : Blo 1847625 3118223 := bstep (se 1 (by rfl) ⟨2338667, by rfl⟩ : syracuseStep 3118223 = 4677335) B4677335
theorem B6239375 : Blo 1847625 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B5919959 : Blo 1847625 5919959 := bstep (se 1 (by rfl) ⟨4439969, by rfl⟩ : syracuseStep 5919959 = 8879939) B8879939
theorem B4158683 : Blo 1847625 4158683 := bstep (se 1 (by rfl) ⟨3119012, by rfl⟩ : syracuseStep 4158683 = 6238025) B6238025
theorem B2962651 : Blo 1847625 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B2774249 : Blo 1847625 2774249 := bstep (se 2 (by rfl) ⟨1040343, by rfl⟩ : syracuseStep 2774249 = 2080687) B2080687
theorem B1848607 : Blo 1847625 1848607 := bstep (se 1 (by rfl) ⟨1386455, by rfl⟩ : syracuseStep 1848607 = 2772911) B2772911
theorem B2774303 : Blo 1847625 2774303 := bstep (se 1 (by rfl) ⟨2080727, by rfl⟩ : syracuseStep 2774303 = 4161455) B4161455
theorem B9360683 : Blo 1847625 9360683 := bstep (se 1 (by rfl) ⟨7020512, by rfl⟩ : syracuseStep 9360683 = 14041025) B14041025
theorem B1848667 : Blo 1847625 1848667 := bstep (se 1 (by rfl) ⟨1386500, by rfl⟩ : syracuseStep 1848667 = 2773001) B2773001
theorem B1848687 : Blo 1847625 1848687 := bstep (se 1 (by rfl) ⟨1386515, by rfl⟩ : syracuseStep 1848687 = 2773031) B2773031
theorem B3118459 : Blo 1847625 3118459 := bstep (se 1 (by rfl) ⟨2338844, by rfl⟩ : syracuseStep 3118459 = 4677689) B4677689
theorem B4158881 : Blo 1847625 4158881 := bstep (se 2 (by rfl) ⟨1559580, by rfl⟩ : syracuseStep 4158881 = 3119161) B3119161
theorem B1848743 : Blo 1847625 1848743 := bstep (se 1 (by rfl) ⟨1386557, by rfl⟩ : syracuseStep 1848743 = 2773115) B2773115
theorem B1848827 : Blo 1847625 1848827 := bstep (se 1 (by rfl) ⟨1386620, by rfl⟩ : syracuseStep 1848827 = 2773241) B2773241
theorem B1848895 : Blo 1847625 1848895 := bstep (se 1 (by rfl) ⟨1386671, by rfl⟩ : syracuseStep 1848895 = 2773343) B2773343
theorem B1848903 : Blo 1847625 1848903 := bstep (se 1 (by rfl) ⟨1386677, by rfl⟩ : syracuseStep 1848903 = 2773355) B2773355
theorem B4216481 : Blo 1847625 4216481 := bstep (se 2 (by rfl) ⟨1581180, by rfl⟩ : syracuseStep 4216481 = 3162361) B3162361
theorem B1849055 : Blo 1847625 1849055 := bstep (se 1 (by rfl) ⟨1386791, by rfl⟩ : syracuseStep 1849055 = 2773583) B2773583
theorem B1849135 : Blo 1847625 1849135 := bstep (se 1 (by rfl) ⟨1386851, by rfl⟩ : syracuseStep 1849135 = 2773703) B2773703
theorem B1849243 : Blo 1847625 1849243 := bstep (se 1 (by rfl) ⟨1386932, by rfl⟩ : syracuseStep 1849243 = 2773865) B2773865
theorem B2078671 : Blo 1847625 2078671 := bstep (se 1 (by rfl) ⟨1559003, by rfl⟩ : syracuseStep 2078671 = 3118007) B3118007
theorem B7018447 : Blo 1847625 7018447 := bstep (se 1 (by rfl) ⟨5263835, by rfl⟩ : syracuseStep 7018447 = 10527671) B10527671
theorem B4159439 : Blo 1847625 4159439 := bstep (se 1 (by rfl) ⟨3119579, by rfl⟩ : syracuseStep 4159439 = 6239159) B6239159
theorem B1849295 : Blo 1847625 1849295 := bstep (se 1 (by rfl) ⟨1386971, by rfl⟩ : syracuseStep 1849295 = 2773943) B2773943
theorem B1849319 : Blo 1847625 1849319 := bstep (se 1 (by rfl) ⟨1386989, by rfl⟩ : syracuseStep 1849319 = 2773979) B2773979
theorem B2340839 : Blo 1847625 2340839 := bstep (se 1 (by rfl) ⟨1755629, by rfl⟩ : syracuseStep 2340839 = 3511259) B3511259
theorem B6084743 : Blo 1847625 6084743 := bstep (se 1 (by rfl) ⟨4563557, by rfl⟩ : syracuseStep 6084743 = 9127115) B9127115
theorem B9361655 : Blo 1847625 9361655 := bstep (se 1 (by rfl) ⟨7021241, by rfl⟩ : syracuseStep 9361655 = 14042483) B14042483
theorem B6240509 : Blo 1847625 6240509 := bstep (se 3 (by rfl) ⟨1170095, by rfl⟩ : syracuseStep 6240509 = 2340191) B2340191
theorem B4159817 : Blo 1847625 4159817 := bstep (se 2 (by rfl) ⟨1559931, by rfl⟩ : syracuseStep 4159817 = 3119863) B3119863
theorem B50592077 : Blo 1847625 50592077 := bstep (se 3 (by rfl) ⟨9486014, by rfl⟩ : syracuseStep 50592077 = 18972029) B18972029
theorem B2079067 : Blo 1847625 2079067 := bstep (se 1 (by rfl) ⟨1559300, by rfl⟩ : syracuseStep 2079067 = 3118601) B3118601
theorem B4159835 : Blo 1847625 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B7018919 : Blo 1847625 7018919 := bstep (se 1 (by rfl) ⟨5264189, by rfl⟩ : syracuseStep 7018919 = 10528379) B10528379
theorem B2079175 : Blo 1847625 2079175 := bstep (se 1 (by rfl) ⟨1559381, by rfl⟩ : syracuseStep 2079175 = 3118763) B3118763
theorem B15800939 : Blo 1847625 15800939 := bstep (se 1 (by rfl) ⟨11850704, by rfl⟩ : syracuseStep 15800939 = 23701409) B23701409
theorem B9362141 : Blo 1847625 9362141 := bstep (se 3 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 9362141 = 3510803) B3510803
theorem B2079535 : Blo 1847625 2079535 := bstep (se 1 (by rfl) ⟨1559651, by rfl⟩ : syracuseStep 2079535 = 3119303) B3119303
theorem B3119951 : Blo 1847625 3119951 := bstep (se 1 (by rfl) ⟨2339963, by rfl⟩ : syracuseStep 3119951 = 4679927) B4679927
theorem B2079643 : Blo 1847625 2079643 := bstep (se 1 (by rfl) ⟨1559732, by rfl⟩ : syracuseStep 2079643 = 3119465) B3119465
theorem B7019419 : Blo 1847625 7019419 := bstep (se 1 (by rfl) ⟨5264564, by rfl⟩ : syracuseStep 7019419 = 10529129) B10529129
theorem B4160411 : Blo 1847625 4160411 := bstep (se 1 (by rfl) ⟨3120308, by rfl⟩ : syracuseStep 4160411 = 6240617) B6240617
theorem B6241319 : Blo 1847625 6241319 := bstep (se 1 (by rfl) ⟨4680989, by rfl⟩ : syracuseStep 6241319 = 9361979) B9361979
theorem B4160609 : Blo 1847625 4160609 := bstep (se 2 (by rfl) ⟨1560228, by rfl⟩ : syracuseStep 4160609 = 3120457) B3120457
theorem B9354527 : Blo 1847625 9354527 := bstep (se 1 (by rfl) ⟨7015895, by rfl⟩ : syracuseStep 9354527 = 14031791) B14031791
theorem B2080039 : Blo 1847625 2080039 := bstep (se 1 (by rfl) ⟨1560029, by rfl⟩ : syracuseStep 2080039 = 3120059) B3120059
theorem B4160807 : Blo 1847625 4160807 := bstep (se 1 (by rfl) ⟨3120605, by rfl⟩ : syracuseStep 4160807 = 6241211) B6241211
theorem B2080111 : Blo 1847625 2080111 := bstep (se 1 (by rfl) ⟨1560083, by rfl⟩ : syracuseStep 2080111 = 3120167) B3120167
theorem B50609609 : Blo 1847625 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B6241751 : Blo 1847625 6241751 := bstep (se 1 (by rfl) ⟨4681313, by rfl⟩ : syracuseStep 6241751 = 9362627) B9362627
theorem B2080327 : Blo 1847625 2080327 := bstep (se 1 (by rfl) ⟨1560245, by rfl⟩ : syracuseStep 2080327 = 3120491) B3120491
theorem B4677203 : Blo 1847625 4677203 := bstep (se 1 (by rfl) ⟨3507902, by rfl⟩ : syracuseStep 4677203 = 7015805) B7015805
theorem B4161185 : Blo 1847625 4161185 := bstep (se 2 (by rfl) ⟨1560444, by rfl⟩ : syracuseStep 4161185 = 3120889) B3120889
theorem B8888105 : Blo 1847625 8888105 := bstep (se 2 (by rfl) ⟨3333039, by rfl⟩ : syracuseStep 8888105 = 6666079) B6666079
theorem B3120943 : Blo 1847625 3120943 := bstep (se 1 (by rfl) ⟨2340707, by rfl⟩ : syracuseStep 3120943 = 4681415) B4681415
theorem B4439863 : Blo 1847625 4439863 := bstep (se 1 (by rfl) ⟨3329897, by rfl⟩ : syracuseStep 4439863 = 6659795) B6659795
theorem B7897121 : Blo 1847625 7897121 := bstep (se 2 (by rfl) ⟨2961420, by rfl⟩ : syracuseStep 7897121 = 5922841) B5922841
theorem B21053519 : Blo 1847625 21053519 := bstep (se 1 (by rfl) ⟨15790139, by rfl⟩ : syracuseStep 21053519 = 31580279) B31580279
theorem B13320395 : Blo 1847625 13320395 := bstep (se 1 (by rfl) ⟨9990296, by rfl⟩ : syracuseStep 13320395 = 19980593) B19980593
theorem B4677851 : Blo 1847625 4677851 := bstep (se 1 (by rfl) ⟨3508388, by rfl⟩ : syracuseStep 4677851 = 7016777) B7016777
theorem B64921915 : Blo 1847625 64921915 := bstep (se 1 (by rfl) ⟨48691436, by rfl⟩ : syracuseStep 64921915 = 97382873) B97382873
theorem B13500847 : Blo 1847625 13500847 := bstep (se 1 (by rfl) ⟨10125635, by rfl⟩ : syracuseStep 13500847 = 20251271) B20251271
theorem B5620151 : Blo 1847625 5620151 := bstep (se 1 (by rfl) ⟨4215113, by rfl⟩ : syracuseStep 5620151 = 8430227) B8430227
theorem B11846195 : Blo 1847625 11846195 := bstep (se 1 (by rfl) ⟨8884646, by rfl⟩ : syracuseStep 11846195 = 17769293) B17769293
theorem B14992067 : Blo 1847625 14992067 := bstep (se 1 (by rfl) ⟨11244050, by rfl⟩ : syracuseStep 14992067 = 22488101) B22488101
theorem B33718999 : Blo 1847625 33718999 := bstep (se 1 (by rfl) ⟨25289249, by rfl⟩ : syracuseStep 33718999 = 50578499) B50578499
theorem B4678681 : Blo 1847625 4678681 := bstep (se 2 (by rfl) ⟨1754505, by rfl⟩ : syracuseStep 4678681 = 3509011) B3509011
theorem B2810987 : Blo 1847625 2810987 := bstep (se 1 (by rfl) ⟨2108240, by rfl⟩ : syracuseStep 2810987 = 4216481) B4216481
theorem B53314685 : Blo 1847625 53314685 := bstep (se 3 (by rfl) ⟨9996503, by rfl⟩ : syracuseStep 53314685 = 19993007) B19993007
theorem B4678985 : Blo 1847625 4678985 := bstep (se 2 (by rfl) ⟨1754619, by rfl⟩ : syracuseStep 4678985 = 3509239) B3509239
theorem B33728051 : Blo 1847625 33728051 := bstep (se 1 (by rfl) ⟨25296038, by rfl⟩ : syracuseStep 33728051 = 50592077) B50592077
theorem B44992057 : Blo 1847625 44992057 := bstep (se 2 (by rfl) ⟨16872021, by rfl⟩ : syracuseStep 44992057 = 33744043) B33744043
theorem B4679279 : Blo 1847625 4679279 := bstep (se 1 (by rfl) ⟨3509459, by rfl⟩ : syracuseStep 4679279 = 7018919) B7018919
theorem B3950201 : Blo 1847625 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B6236351 : Blo 1847625 6236351 := bstep (se 1 (by rfl) ⟨4677263, by rfl⟩ : syracuseStep 6236351 = 9354527) B9354527
theorem B5261831 : Blo 1847625 5261831 := bstep (se 1 (by rfl) ⟨3946373, by rfl⟩ : syracuseStep 5261831 = 7892747) B7892747
theorem B2771483 : Blo 1847625 2771483 := bstep (se 1 (by rfl) ⟨2078612, by rfl⟩ : syracuseStep 2771483 = 4157225) B4157225
theorem B5925403 : Blo 1847625 5925403 := bstep (se 1 (by rfl) ⟨4444052, by rfl⟩ : syracuseStep 5925403 = 8888105) B8888105
theorem B2771561 : Blo 1847625 2771561 := bstep (se 2 (by rfl) ⟨1039335, by rfl⟩ : syracuseStep 2771561 = 2078671) B2078671
theorem B9357929 : Blo 1847625 9357929 := bstep (se 2 (by rfl) ⟨3509223, by rfl⟩ : syracuseStep 9357929 = 7018447) B7018447
theorem B13323163 : Blo 1847625 13323163 := bstep (se 1 (by rfl) ⟨9992372, by rfl⟩ : syracuseStep 13323163 = 19984745) B19984745
theorem B2772089 : Blo 1847625 2772089 := bstep (se 2 (by rfl) ⟨1039533, by rfl⟩ : syracuseStep 2772089 = 2079067) B2079067
theorem B6663311 : Blo 1847625 6663311 := bstep (se 1 (by rfl) ⟨4997483, by rfl⟩ : syracuseStep 6663311 = 9994967) B9994967
theorem B25636061 : Blo 1847625 25636061 := bstep (se 3 (by rfl) ⟨4806761, by rfl⟩ : syracuseStep 25636061 = 9613523) B9613523
theorem B2772191 : Blo 1847625 2772191 := bstep (se 1 (by rfl) ⟨2079143, by rfl⟩ : syracuseStep 2772191 = 4158287) B4158287
theorem B2772233 : Blo 1847625 2772233 := bstep (se 2 (by rfl) ⟨1039587, by rfl⟩ : syracuseStep 2772233 = 2079175) B2079175
theorem B27004211 : Blo 1847625 27004211 := bstep (se 1 (by rfl) ⟨20253158, by rfl⟩ : syracuseStep 27004211 = 40506317) B40506317
theorem B13323599 : Blo 1847625 13323599 := bstep (se 1 (by rfl) ⟨9992699, by rfl⟩ : syracuseStep 13323599 = 19985399) B19985399
theorem B2772335 : Blo 1847625 2772335 := bstep (se 1 (by rfl) ⟨2079251, by rfl⟩ : syracuseStep 2772335 = 4158503) B4158503
theorem B2772455 : Blo 1847625 2772455 := bstep (se 1 (by rfl) ⟨2079341, by rfl⟩ : syracuseStep 2772455 = 4158683) B4158683
theorem B2960959 : Blo 1847625 2960959 := bstep (se 1 (by rfl) ⟨2220719, by rfl⟩ : syracuseStep 2960959 = 4441439) B4441439
theorem B2772587 : Blo 1847625 2772587 := bstep (se 1 (by rfl) ⟨2079440, by rfl⟩ : syracuseStep 2772587 = 4158881) B4158881
theorem B2772713 : Blo 1847625 2772713 := bstep (se 2 (by rfl) ⟨1039767, by rfl⟩ : syracuseStep 2772713 = 2079535) B2079535
theorem B6237971 : Blo 1847625 6237971 := bstep (se 1 (by rfl) ⟨4678478, by rfl⟩ : syracuseStep 6237971 = 9356957) B9356957
theorem B2772857 : Blo 1847625 2772857 := bstep (se 2 (by rfl) ⟨1039821, by rfl⟩ : syracuseStep 2772857 = 2079643) B2079643
theorem B9359225 : Blo 1847625 9359225 := bstep (se 2 (by rfl) ⟨3509709, by rfl⟩ : syracuseStep 9359225 = 7019419) B7019419
theorem B54775709 : Blo 1847625 54775709 := bstep (se 3 (by rfl) ⟨10270445, by rfl⟩ : syracuseStep 54775709 = 20540891) B20540891
theorem B2772959 : Blo 1847625 2772959 := bstep (se 1 (by rfl) ⟨2079719, by rfl⟩ : syracuseStep 2772959 = 4159439) B4159439
theorem B37941443 : Blo 1847625 37941443 := bstep (se 1 (by rfl) ⟨28456082, by rfl⟩ : syracuseStep 37941443 = 56912165) B56912165
theorem B2773211 : Blo 1847625 2773211 := bstep (se 1 (by rfl) ⟨2079908, by rfl⟩ : syracuseStep 2773211 = 4159817) B4159817
theorem B2339047 : Blo 1847625 2339047 := bstep (se 1 (by rfl) ⟨1754285, by rfl⟩ : syracuseStep 2339047 = 3508571) B3508571
theorem B2773223 : Blo 1847625 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B1847679 : Blo 1847625 1847679 := bstep (se 1 (by rfl) ⟨1385759, by rfl⟩ : syracuseStep 1847679 = 2771519) B2771519
theorem B2773385 : Blo 1847625 2773385 := bstep (se 2 (by rfl) ⟨1040019, by rfl⟩ : syracuseStep 2773385 = 2080039) B2080039
theorem B1847759 : Blo 1847625 1847759 := bstep (se 1 (by rfl) ⟨1385819, by rfl⟩ : syracuseStep 1847759 = 2771639) B2771639
theorem B2773481 : Blo 1847625 2773481 := bstep (se 2 (by rfl) ⟨1040055, by rfl⟩ : syracuseStep 2773481 = 2080111) B2080111
theorem B4157945 : Blo 1847625 4157945 := bstep (se 2 (by rfl) ⟨1559229, by rfl⟩ : syracuseStep 4157945 = 3118459) B3118459
theorem B4158035 : Blo 1847625 4158035 := bstep (se 1 (by rfl) ⟨3118526, by rfl⟩ : syracuseStep 4158035 = 6237053) B6237053
theorem B9007699 : Blo 1847625 9007699 := bstep (se 1 (by rfl) ⟨6755774, by rfl⟩ : syracuseStep 9007699 = 13511549) B13511549
theorem B1847911 : Blo 1847625 1847911 := bstep (se 1 (by rfl) ⟨1385933, by rfl⟩ : syracuseStep 1847911 = 2771867) B2771867
theorem B2773607 : Blo 1847625 2773607 := bstep (se 1 (by rfl) ⟨2080205, by rfl⟩ : syracuseStep 2773607 = 4160411) B4160411
theorem B6238835 : Blo 1847625 6238835 := bstep (se 1 (by rfl) ⟨4679126, by rfl⟩ : syracuseStep 6238835 = 9358253) B9358253
theorem B11842195 : Blo 1847625 11842195 := bstep (se 1 (by rfl) ⟨8881646, by rfl⟩ : syracuseStep 11842195 = 17763293) B17763293
theorem B10523297 : Blo 1847625 10523297 := bstep (se 2 (by rfl) ⟨3946236, by rfl⟩ : syracuseStep 10523297 = 7892473) B7892473
theorem B2773739 : Blo 1847625 2773739 := bstep (se 1 (by rfl) ⟨2080304, by rfl⟩ : syracuseStep 2773739 = 4160609) B4160609
theorem B4158215 : Blo 1847625 4158215 := bstep (se 1 (by rfl) ⟨3118661, by rfl⟩ : syracuseStep 4158215 = 6237323) B6237323
theorem B2773769 : Blo 1847625 2773769 := bstep (se 2 (by rfl) ⟨1040163, by rfl⟩ : syracuseStep 2773769 = 2080327) B2080327
theorem B1848175 : Blo 1847625 1848175 := bstep (se 1 (by rfl) ⟨1386131, by rfl⟩ : syracuseStep 1848175 = 2772263) B2772263
theorem B2339695 : Blo 1847625 2339695 := bstep (se 1 (by rfl) ⟨1754771, by rfl⟩ : syracuseStep 2339695 = 3509543) B3509543
theorem B2773871 : Blo 1847625 2773871 := bstep (se 1 (by rfl) ⟨2080403, by rfl⟩ : syracuseStep 2773871 = 4160807) B4160807
theorem B6239105 : Blo 1847625 6239105 := bstep (se 2 (by rfl) ⟨2339664, by rfl⟩ : syracuseStep 6239105 = 4679329) B4679329
theorem B1848231 : Blo 1847625 1848231 := bstep (se 1 (by rfl) ⟨1386173, by rfl⟩ : syracuseStep 1848231 = 2772347) B2772347
theorem B2962343 : Blo 1847625 2962343 := bstep (se 1 (by rfl) ⟨2221757, by rfl⟩ : syracuseStep 2962343 = 4443515) B4443515
theorem B33739739 : Blo 1847625 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B1848315 : Blo 1847625 1848315 := bstep (se 1 (by rfl) ⟨1386236, by rfl⟩ : syracuseStep 1848315 = 2772473) B2772473
theorem B3118135 : Blo 1847625 3118135 := bstep (se 1 (by rfl) ⟨2338601, by rfl⟩ : syracuseStep 3118135 = 4677203) B4677203
theorem B1848383 : Blo 1847625 1848383 := bstep (se 1 (by rfl) ⟨1386287, by rfl⟩ : syracuseStep 1848383 = 2772575) B2772575
theorem B5919817 : Blo 1847625 5919817 := bstep (se 2 (by rfl) ⟨2219931, by rfl⟩ : syracuseStep 5919817 = 4439863) B4439863
theorem B2774123 : Blo 1847625 2774123 := bstep (se 1 (by rfl) ⟨2080592, by rfl⟩ : syracuseStep 2774123 = 4161185) B4161185
theorem B1848527 : Blo 1847625 1848527 := bstep (se 1 (by rfl) ⟨1386395, by rfl⟩ : syracuseStep 1848527 = 2772791) B2772791
theorem B2774363 : Blo 1847625 2774363 := bstep (se 1 (by rfl) ⟨2080772, by rfl⟩ : syracuseStep 2774363 = 4161545) B4161545
theorem B1873307 : Blo 1847625 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B1848731 : Blo 1847625 1848731 := bstep (se 1 (by rfl) ⟨1386548, by rfl⟩ : syracuseStep 1848731 = 2773097) B2773097
theorem B1848943 : Blo 1847625 1848943 := bstep (se 1 (by rfl) ⟨1386707, by rfl⟩ : syracuseStep 1848943 = 2773415) B2773415
theorem B1848999 : Blo 1847625 1848999 := bstep (se 1 (by rfl) ⟨1386749, by rfl⟩ : syracuseStep 1848999 = 2773499) B2773499
theorem B6239915 : Blo 1847625 6239915 := bstep (se 1 (by rfl) ⟨4679936, by rfl⟩ : syracuseStep 6239915 = 9359873) B9359873
theorem B15799981 : Blo 1847625 15799981 := bstep (se 3 (by rfl) ⟨2962496, by rfl⟩ : syracuseStep 15799981 = 5924993) B5924993
theorem B16225981 : Blo 1847625 16225981 := bstep (se 3 (by rfl) ⟨3042371, by rfl⟩ : syracuseStep 16225981 = 6084743) B6084743
theorem B11843273 : Blo 1847625 11843273 := bstep (se 2 (by rfl) ⟨4441227, by rfl⟩ : syracuseStep 11843273 = 8882455) B8882455
theorem B2340571 : Blo 1847625 2340571 := bstep (se 1 (by rfl) ⟨1755428, by rfl⟩ : syracuseStep 2340571 = 3510857) B3510857
theorem B1849083 : Blo 1847625 1849083 := bstep (se 1 (by rfl) ⟨1386812, by rfl⟩ : syracuseStep 1849083 = 2773625) B2773625
theorem B1849119 : Blo 1847625 1849119 := bstep (se 1 (by rfl) ⟨1386839, by rfl⟩ : syracuseStep 1849119 = 2773679) B2773679
theorem B47396663 : Blo 1847625 47396663 := bstep (se 1 (by rfl) ⟨35547497, by rfl⟩ : syracuseStep 47396663 = 71094995) B71094995
theorem B4159295 : Blo 1847625 4159295 := bstep (se 1 (by rfl) ⟨3119471, by rfl⟩ : syracuseStep 4159295 = 6238943) B6238943
theorem B1849151 : Blo 1847625 1849151 := bstep (se 1 (by rfl) ⟨1386863, by rfl⟩ : syracuseStep 1849151 = 2773727) B2773727
theorem B24352741 : Blo 1847625 24352741 := bstep (se 4 (by rfl) ⟨2283069, by rfl⟩ : syracuseStep 24352741 = 4566139) B4566139
theorem B3119087 : Blo 1847625 3119087 := bstep (se 1 (by rfl) ⟨2339315, by rfl⟩ : syracuseStep 3119087 = 4678631) B4678631
theorem B6240239 : Blo 1847625 6240239 := bstep (se 1 (by rfl) ⟨4680179, by rfl⟩ : syracuseStep 6240239 = 9360359) B9360359
theorem B1849327 : Blo 1847625 1849327 := bstep (se 1 (by rfl) ⟨1386995, by rfl⟩ : syracuseStep 1849327 = 2773991) B2773991
theorem B6322259 : Blo 1847625 6322259 := bstep (se 1 (by rfl) ⟨4741694, by rfl⟩ : syracuseStep 6322259 = 9483389) B9483389
theorem B2078815 : Blo 1847625 2078815 := bstep (se 1 (by rfl) ⟨1559111, by rfl⟩ : syracuseStep 2078815 = 3118223) B3118223
theorem B4159583 : Blo 1847625 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B3946639 : Blo 1847625 3946639 := bstep (se 1 (by rfl) ⟨2959979, by rfl⟩ : syracuseStep 3946639 = 5919959) B5919959
theorem B1849499 : Blo 1847625 1849499 := bstep (se 1 (by rfl) ⟨1387124, by rfl⟩ : syracuseStep 1849499 = 2774249) B2774249
theorem B1849535 : Blo 1847625 1849535 := bstep (se 1 (by rfl) ⟨1387151, by rfl⟩ : syracuseStep 1849535 = 2774303) B2774303
theorem B6240455 : Blo 1847625 6240455 := bstep (se 1 (by rfl) ⟨4680341, by rfl⟩ : syracuseStep 6240455 = 9360683) B9360683
theorem B10524937 : Blo 1847625 10524937 := bstep (se 2 (by rfl) ⟨3946851, by rfl⟩ : syracuseStep 10524937 = 7893703) B7893703
theorem B3119647 : Blo 1847625 3119647 := bstep (se 1 (by rfl) ⟨2339735, by rfl⟩ : syracuseStep 3119647 = 4679471) B4679471
theorem B6241103 : Blo 1847625 6241103 := bstep (se 1 (by rfl) ⟨4680827, by rfl⟩ : syracuseStep 6241103 = 9361655) B9361655
theorem B4160339 : Blo 1847625 4160339 := bstep (se 1 (by rfl) ⟨3120254, by rfl⟩ : syracuseStep 4160339 = 6240509) B6240509
theorem B3120079 : Blo 1847625 3120079 := bstep (se 1 (by rfl) ⟨2340059, by rfl⟩ : syracuseStep 3120079 = 4680119) B4680119
theorem B2251847 : Blo 1847625 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B10533959 : Blo 1847625 10533959 := bstep (se 1 (by rfl) ⟨7900469, by rfl⟩ : syracuseStep 10533959 = 15800939) B15800939
theorem B9485441 : Blo 1847625 9485441 := bstep (se 2 (by rfl) ⟨3557040, by rfl⟩ : syracuseStep 9485441 = 7114081) B7114081
theorem B36527249 : Blo 1847625 36527249 := bstep (se 2 (by rfl) ⟨13697718, by rfl⟩ : syracuseStep 36527249 = 27395437) B27395437
theorem B6241427 : Blo 1847625 6241427 := bstep (se 1 (by rfl) ⟨4681070, by rfl⟩ : syracuseStep 6241427 = 9362141) B9362141
theorem B5266615 : Blo 1847625 5266615 := bstep (se 1 (by rfl) ⟨3949961, by rfl⟩ : syracuseStep 5266615 = 7899923) B7899923
theorem B18963659 : Blo 1847625 18963659 := bstep (se 1 (by rfl) ⟨14222744, by rfl⟩ : syracuseStep 18963659 = 28445489) B28445489
theorem B2079967 : Blo 1847625 2079967 := bstep (se 1 (by rfl) ⟨1559975, by rfl⟩ : syracuseStep 2079967 = 3119951) B3119951
theorem B4160879 : Blo 1847625 4160879 := bstep (se 1 (by rfl) ⟨3120659, by rfl⟩ : syracuseStep 4160879 = 6241319) B6241319
theorem B6241697 : Blo 1847625 6241697 := bstep (se 2 (by rfl) ⟨2340636, by rfl⟩ : syracuseStep 6241697 = 4681273) B4681273
theorem B9354689 : Blo 1847625 9354689 := bstep (se 2 (by rfl) ⟨3508008, by rfl⟩ : syracuseStep 9354689 = 7016017) B7016017
theorem B26353127 : Blo 1847625 26353127 := bstep (se 1 (by rfl) ⟨19764845, by rfl⟩ : syracuseStep 26353127 = 39529691) B39529691
theorem B4161167 : Blo 1847625 4161167 := bstep (se 1 (by rfl) ⟨3120875, by rfl⟩ : syracuseStep 4161167 = 6241751) B6241751
theorem B3120815 : Blo 1847625 3120815 := bstep (se 1 (by rfl) ⟨2340611, by rfl⟩ : syracuseStep 3120815 = 4681223) B4681223
theorem B4161257 : Blo 1847625 4161257 := bstep (se 2 (by rfl) ⟨1560471, by rfl⟩ : syracuseStep 4161257 = 3120943) B3120943
theorem B14032763 : Blo 1847625 14032763 := bstep (se 1 (by rfl) ⟨10524572, by rfl⟩ : syracuseStep 14032763 = 21049145) B21049145
theorem B3121051 : Blo 1847625 3121051 := bstep (se 1 (by rfl) ⟨2340788, by rfl⟩ : syracuseStep 3121051 = 4681577) B4681577
theorem B4677547 : Blo 1847625 4677547 := bstep (se 1 (by rfl) ⟨3508160, by rfl⟩ : syracuseStep 4677547 = 7016321) B7016321
theorem B6242237 : Blo 1847625 6242237 := bstep (se 3 (by rfl) ⟨1170419, by rfl⟩ : syracuseStep 6242237 = 2340839) B2340839
theorem B8880263 : Blo 1847625 8880263 := bstep (se 1 (by rfl) ⟨6660197, by rfl⟩ : syracuseStep 8880263 = 13320395) B13320395
theorem B6004925 : Blo 1847625 6004925 := bstep (se 3 (by rfl) ⟨1125923, by rfl⟩ : syracuseStep 6004925 = 2251847) B2251847
theorem B14033249 : Blo 1847625 14033249 := bstep (se 2 (by rfl) ⟨5262468, by rfl⟩ : syracuseStep 14033249 = 10524937) B10524937
theorem B7897463 : Blo 1847625 7897463 := bstep (se 1 (by rfl) ⟨5923097, by rfl⟩ : syracuseStep 7897463 = 11846195) B11846195
theorem B9994711 : Blo 1847625 9994711 := bstep (se 1 (by rfl) ⟨7496033, by rfl⟩ : syracuseStep 9994711 = 14992067) B14992067
theorem B12010265 : Blo 1847625 12010265 := bstep (se 2 (by rfl) ⟨4503849, by rfl⟩ : syracuseStep 12010265 = 9007699) B9007699
theorem B44958665 : Blo 1847625 44958665 := bstep (se 2 (by rfl) ⟨16859499, by rfl⟩ : syracuseStep 44958665 = 33718999) B33718999
theorem B29983861 : Blo 1847625 29983861 := bstep (se 5 (by rfl) ⟨1405493, by rfl⟩ : syracuseStep 29983861 = 2810987) B2810987
theorem B31597775 : Blo 1847625 31597775 := bstep (se 1 (by rfl) ⟨23698331, by rfl⟩ : syracuseStep 31597775 = 47396663) B47396663
theorem B7022153 : Blo 1847625 7022153 := bstep (se 2 (by rfl) ⟨2633307, by rfl⟩ : syracuseStep 7022153 = 5266615) B5266615
theorem B3507887 : Blo 1847625 3507887 := bstep (se 1 (by rfl) ⟨2630915, by rfl⟩ : syracuseStep 3507887 = 5261831) B5261831
theorem B7022639 : Blo 1847625 7022639 := bstep (se 1 (by rfl) ⟨5266979, by rfl⟩ : syracuseStep 7022639 = 10533959) B10533959
theorem B4442207 : Blo 1847625 4442207 := bstep (se 1 (by rfl) ⟨3331655, by rfl⟩ : syracuseStep 4442207 = 6663311) B6663311
theorem B12642439 : Blo 1847625 12642439 := bstep (se 1 (by rfl) ⟨9481829, by rfl⟩ : syracuseStep 12642439 = 18963659) B18963659
theorem B17090707 : Blo 1847625 17090707 := bstep (se 1 (by rfl) ⟨12818030, by rfl⟩ : syracuseStep 17090707 = 25636061) B25636061
theorem B8882399 : Blo 1847625 8882399 := bstep (se 1 (by rfl) ⟨6661799, by rfl⟩ : syracuseStep 8882399 = 13323599) B13323599
theorem B6236459 : Blo 1847625 6236459 := bstep (se 1 (by rfl) ⟨4677344, by rfl⟩ : syracuseStep 6236459 = 9354689) B9354689
theorem B7899581 : Blo 1847625 7899581 := bstep (se 3 (by rfl) ⟨1481171, by rfl⟩ : syracuseStep 7899581 = 2962343) B2962343
theorem B6236729 : Blo 1847625 6236729 := bstep (se 2 (by rfl) ⟨2338773, by rfl⟩ : syracuseStep 6236729 = 4677547) B4677547
theorem B14035679 : Blo 1847625 14035679 := bstep (se 1 (by rfl) ⟨10526759, by rfl⟩ : syracuseStep 14035679 = 21053519) B21053519
theorem B2771753 : Blo 1847625 2771753 := bstep (se 2 (by rfl) ⟨1039407, by rfl⟩ : syracuseStep 2771753 = 2078815) B2078815
theorem B5262185 : Blo 1847625 5262185 := bstep (se 2 (by rfl) ⟨1973319, by rfl⟩ : syracuseStep 5262185 = 3946639) B3946639
theorem B3746767 : Blo 1847625 3746767 := bstep (se 1 (by rfl) ⟨2810075, by rfl⟩ : syracuseStep 3746767 = 5620151) B5620151
theorem B2771963 : Blo 1847625 2771963 := bstep (se 1 (by rfl) ⟨2078972, by rfl⟩ : syracuseStep 2771963 = 4157945) B4157945
theorem B2772023 : Blo 1847625 2772023 := bstep (se 1 (by rfl) ⟨2079017, by rfl⟩ : syracuseStep 2772023 = 4158035) B4158035
theorem B7015531 : Blo 1847625 7015531 := bstep (se 1 (by rfl) ⟨5261648, by rfl⟩ : syracuseStep 7015531 = 10523297) B10523297
theorem B2772143 : Blo 1847625 2772143 := bstep (se 1 (by rfl) ⟨2079107, by rfl⟩ : syracuseStep 2772143 = 4158215) B4158215
theorem B18001129 : Blo 1847625 18001129 := bstep (se 2 (by rfl) ⟨6750423, by rfl⟩ : syracuseStep 18001129 = 13500847) B13500847
theorem B15789593 : Blo 1847625 15789593 := bstep (se 2 (by rfl) ⟨5921097, by rfl⟩ : syracuseStep 15789593 = 11842195) B11842195
theorem B2633467 : Blo 1847625 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B17764217 : Blo 1847625 17764217 := bstep (se 2 (by rfl) ⟨6661581, by rfl⟩ : syracuseStep 17764217 = 13323163) B13323163
theorem B2772863 : Blo 1847625 2772863 := bstep (se 1 (by rfl) ⟨2079647, by rfl⟩ : syracuseStep 2772863 = 4159295) B4159295
theorem B6238241 : Blo 1847625 6238241 := bstep (se 2 (by rfl) ⟨2339340, by rfl⟩ : syracuseStep 6238241 = 4678681) B4678681
theorem B4214839 : Blo 1847625 4214839 := bstep (se 1 (by rfl) ⟨3161129, by rfl⟩ : syracuseStep 4214839 = 6322259) B6322259
theorem B2773055 : Blo 1847625 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B4157513 : Blo 1847625 4157513 := bstep (se 2 (by rfl) ⟨1559067, by rfl⟩ : syracuseStep 4157513 = 3118135) B3118135
theorem B7893089 : Blo 1847625 7893089 := bstep (se 2 (by rfl) ⟨2959908, by rfl⟩ : syracuseStep 7893089 = 5919817) B5919817
theorem B4157567 : Blo 1847625 4157567 := bstep (se 1 (by rfl) ⟨3118175, by rfl⟩ : syracuseStep 4157567 = 6236351) B6236351
theorem B2773289 : Blo 1847625 2773289 := bstep (se 2 (by rfl) ⟨1039983, by rfl⟩ : syracuseStep 2773289 = 2079967) B2079967
theorem B1847655 : Blo 1847625 1847655 := bstep (se 1 (by rfl) ⟨1385741, by rfl⟩ : syracuseStep 1847655 = 2771483) B2771483
theorem B1847707 : Blo 1847625 1847707 := bstep (se 1 (by rfl) ⟨1385780, by rfl⟩ : syracuseStep 1847707 = 2771561) B2771561
theorem B6238619 : Blo 1847625 6238619 := bstep (se 1 (by rfl) ⟨4678964, by rfl⟩ : syracuseStep 6238619 = 9357929) B9357929
theorem B2773559 : Blo 1847625 2773559 := bstep (se 1 (by rfl) ⟨2080169, by rfl⟩ : syracuseStep 2773559 = 4160339) B4160339
theorem B1848059 : Blo 1847625 1848059 := bstep (se 1 (by rfl) ⟨1386044, by rfl⟩ : syracuseStep 1848059 = 2772089) B2772089
theorem B24351499 : Blo 1847625 24351499 := bstep (se 1 (by rfl) ⟨18263624, by rfl⟩ : syracuseStep 24351499 = 36527249) B36527249
theorem B1848127 : Blo 1847625 1848127 := bstep (se 1 (by rfl) ⟨1386095, by rfl⟩ : syracuseStep 1848127 = 2772191) B2772191
theorem B1848155 : Blo 1847625 1848155 := bstep (se 1 (by rfl) ⟨1386116, by rfl⟩ : syracuseStep 1848155 = 2772233) B2772233
theorem B18002807 : Blo 1847625 18002807 := bstep (se 1 (by rfl) ⟨13502105, by rfl⟩ : syracuseStep 18002807 = 27004211) B27004211
theorem B21066641 : Blo 1847625 21066641 := bstep (se 2 (by rfl) ⟨7899990, by rfl⟩ : syracuseStep 21066641 = 15799981) B15799981
theorem B1848223 : Blo 1847625 1848223 := bstep (se 1 (by rfl) ⟨1386167, by rfl⟩ : syracuseStep 1848223 = 2772335) B2772335
theorem B2773919 : Blo 1847625 2773919 := bstep (se 1 (by rfl) ⟨2080439, by rfl⟩ : syracuseStep 2773919 = 4160879) B4160879
theorem B1848303 : Blo 1847625 1848303 := bstep (se 1 (by rfl) ⟨1386227, by rfl⟩ : syracuseStep 1848303 = 2772455) B2772455
theorem B17568751 : Blo 1847625 17568751 := bstep (se 1 (by rfl) ⟨13176563, by rfl⟩ : syracuseStep 17568751 = 26353127) B26353127
theorem B1848391 : Blo 1847625 1848391 := bstep (se 1 (by rfl) ⟨1386293, by rfl⟩ : syracuseStep 1848391 = 2772587) B2772587
theorem B2774111 : Blo 1847625 2774111 := bstep (se 1 (by rfl) ⟨2080583, by rfl⟩ : syracuseStep 2774111 = 4161167) B4161167
theorem B1848475 : Blo 1847625 1848475 := bstep (se 1 (by rfl) ⟨1386356, by rfl⟩ : syracuseStep 1848475 = 2772713) B2772713
theorem B2774171 : Blo 1847625 2774171 := bstep (se 1 (by rfl) ⟨2080628, by rfl⟩ : syracuseStep 2774171 = 4161257) B4161257
theorem B4158647 : Blo 1847625 4158647 := bstep (se 1 (by rfl) ⟨3118985, by rfl⟩ : syracuseStep 4158647 = 6237971) B6237971
theorem B1848571 : Blo 1847625 1848571 := bstep (se 1 (by rfl) ⟨1386428, by rfl⟩ : syracuseStep 1848571 = 2772857) B2772857
theorem B6239483 : Blo 1847625 6239483 := bstep (se 1 (by rfl) ⟨4679612, by rfl⟩ : syracuseStep 6239483 = 9359225) B9359225
theorem B36517139 : Blo 1847625 36517139 := bstep (se 1 (by rfl) ⟨27387854, by rfl⟩ : syracuseStep 36517139 = 54775709) B54775709
theorem B32470321 : Blo 1847625 32470321 := bstep (se 2 (by rfl) ⟨12176370, by rfl⟩ : syracuseStep 32470321 = 24352741) B24352741
theorem B1848639 : Blo 1847625 1848639 := bstep (se 1 (by rfl) ⟨1386479, by rfl⟩ : syracuseStep 1848639 = 2772959) B2772959
theorem B5264747 : Blo 1847625 5264747 := bstep (se 1 (by rfl) ⟨3948560, by rfl⟩ : syracuseStep 5264747 = 7897121) B7897121
theorem B25294295 : Blo 1847625 25294295 := bstep (se 1 (by rfl) ⟨18970721, by rfl⟩ : syracuseStep 25294295 = 37941443) B37941443
theorem B31602149 : Blo 1847625 31602149 := bstep (se 4 (by rfl) ⟨2962701, by rfl⟩ : syracuseStep 31602149 = 5925403) B5925403
theorem B3118567 : Blo 1847625 3118567 := bstep (se 1 (by rfl) ⟨2338925, by rfl⟩ : syracuseStep 3118567 = 4677851) B4677851
theorem B1848807 : Blo 1847625 1848807 := bstep (se 1 (by rfl) ⟨1386605, by rfl⟩ : syracuseStep 1848807 = 2773211) B2773211
theorem B1848815 : Blo 1847625 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B1848923 : Blo 1847625 1848923 := bstep (se 1 (by rfl) ⟨1386692, by rfl⟩ : syracuseStep 1848923 = 2773385) B2773385
theorem B3118729 : Blo 1847625 3118729 := bstep (se 2 (by rfl) ⟨1169523, by rfl⟩ : syracuseStep 3118729 = 2339047) B2339047
theorem B1848987 : Blo 1847625 1848987 := bstep (se 1 (by rfl) ⟨1386740, by rfl⟩ : syracuseStep 1848987 = 2773481) B2773481
theorem B1849071 : Blo 1847625 1849071 := bstep (se 1 (by rfl) ⟨1386803, by rfl⟩ : syracuseStep 1849071 = 2773607) B2773607
theorem B4159223 : Blo 1847625 4159223 := bstep (se 1 (by rfl) ⟨3119417, by rfl⟩ : syracuseStep 4159223 = 6238835) B6238835
theorem B86562553 : Blo 1847625 86562553 := bstep (se 2 (by rfl) ⟨32460957, by rfl⟩ : syracuseStep 86562553 = 64921915) B64921915
theorem B1849159 : Blo 1847625 1849159 := bstep (se 1 (by rfl) ⟨1386869, by rfl⟩ : syracuseStep 1849159 = 2773739) B2773739
theorem B1849179 : Blo 1847625 1849179 := bstep (se 1 (by rfl) ⟨1386884, by rfl⟩ : syracuseStep 1849179 = 2773769) B2773769
theorem B1849247 : Blo 1847625 1849247 := bstep (se 1 (by rfl) ⟨1386935, by rfl⟩ : syracuseStep 1849247 = 2773871) B2773871
theorem B4159403 : Blo 1847625 4159403 := bstep (se 1 (by rfl) ⟨3119552, by rfl⟩ : syracuseStep 4159403 = 6239105) B6239105
theorem B22493159 : Blo 1847625 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B4159529 : Blo 1847625 4159529 := bstep (se 2 (by rfl) ⟨1559823, by rfl⟩ : syracuseStep 4159529 = 3119647) B3119647
theorem B1849415 : Blo 1847625 1849415 := bstep (se 1 (by rfl) ⟨1387061, by rfl⟩ : syracuseStep 1849415 = 2774123) B2774123
theorem B35543123 : Blo 1847625 35543123 := bstep (se 1 (by rfl) ⟨26657342, by rfl⟩ : syracuseStep 35543123 = 53314685) B53314685
theorem B3119323 : Blo 1847625 3119323 := bstep (se 1 (by rfl) ⟨2339492, by rfl⟩ : syracuseStep 3119323 = 4678985) B4678985
theorem B1849575 : Blo 1847625 1849575 := bstep (se 1 (by rfl) ⟨1387181, by rfl⟩ : syracuseStep 1849575 = 2774363) B2774363
theorem B86538565 : Blo 1847625 86538565 := bstep (se 4 (by rfl) ⟨8112990, by rfl⟩ : syracuseStep 86538565 = 16225981) B16225981
theorem B22485367 : Blo 1847625 22485367 := bstep (se 1 (by rfl) ⟨16864025, by rfl⟩ : syracuseStep 22485367 = 33728051) B33728051
theorem B4995485 : Blo 1847625 4995485 := bstep (se 3 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 4995485 = 1873307) B1873307
theorem B3119519 : Blo 1847625 3119519 := bstep (se 1 (by rfl) ⟨2339639, by rfl⟩ : syracuseStep 3119519 = 4679279) B4679279
theorem B4159943 : Blo 1847625 4159943 := bstep (se 1 (by rfl) ⟨3119957, by rfl⟩ : syracuseStep 4159943 = 6239915) B6239915
theorem B7895515 : Blo 1847625 7895515 := bstep (se 1 (by rfl) ⟨5921636, by rfl⟩ : syracuseStep 7895515 = 11843273) B11843273
theorem B3119593 : Blo 1847625 3119593 := bstep (se 2 (by rfl) ⟨1169847, by rfl⟩ : syracuseStep 3119593 = 2339695) B2339695
theorem B4160105 : Blo 1847625 4160105 := bstep (se 2 (by rfl) ⟨1560039, by rfl⟩ : syracuseStep 4160105 = 3120079) B3120079
theorem B2079391 : Blo 1847625 2079391 := bstep (se 1 (by rfl) ⟨1559543, by rfl⟩ : syracuseStep 2079391 = 3119087) B3119087
theorem B4160159 : Blo 1847625 4160159 := bstep (se 1 (by rfl) ⟨3120119, by rfl⟩ : syracuseStep 4160159 = 6240239) B6240239
theorem B4160303 : Blo 1847625 4160303 := bstep (se 1 (by rfl) ⟨3120227, by rfl⟩ : syracuseStep 4160303 = 6240455) B6240455
theorem B4160735 : Blo 1847625 4160735 := bstep (se 1 (by rfl) ⟨3120551, by rfl⟩ : syracuseStep 4160735 = 6241103) B6241103
theorem B59989409 : Blo 1847625 59989409 := bstep (se 2 (by rfl) ⟨22496028, by rfl⟩ : syracuseStep 59989409 = 44992057) B44992057
theorem B3947945 : Blo 1847625 3947945 := bstep (se 2 (by rfl) ⟨1480479, by rfl⟩ : syracuseStep 3947945 = 2960959) B2960959
theorem B6323627 : Blo 1847625 6323627 := bstep (se 1 (by rfl) ⟨4742720, by rfl⟩ : syracuseStep 6323627 = 9485441) B9485441
theorem B4160951 : Blo 1847625 4160951 := bstep (se 1 (by rfl) ⟨3120713, by rfl⟩ : syracuseStep 4160951 = 6241427) B6241427
theorem B4161131 : Blo 1847625 4161131 := bstep (se 1 (by rfl) ⟨3120848, by rfl⟩ : syracuseStep 4161131 = 6241697) B6241697
theorem B3120761 : Blo 1847625 3120761 := bstep (se 2 (by rfl) ⟨1170285, by rfl⟩ : syracuseStep 3120761 = 2340571) B2340571
theorem B2080543 : Blo 1847625 2080543 := bstep (se 1 (by rfl) ⟨1560407, by rfl⟩ : syracuseStep 2080543 = 3120815) B3120815
theorem B4161401 : Blo 1847625 4161401 := bstep (se 2 (by rfl) ⟨1560525, by rfl⟩ : syracuseStep 4161401 = 3121051) B3121051
theorem B9355175 : Blo 1847625 9355175 := bstep (se 1 (by rfl) ⟨7016381, by rfl⟩ : syracuseStep 9355175 = 14032763) B14032763
theorem B4161491 : Blo 1847625 4161491 := bstep (se 1 (by rfl) ⟨3121118, by rfl⟩ : syracuseStep 4161491 = 6242237) B6242237
theorem B5619785 : Blo 1847625 5619785 := bstep (se 2 (by rfl) ⟨2107419, by rfl⟩ : syracuseStep 5619785 = 4214839) B4214839
theorem B9355499 : Blo 1847625 9355499 := bstep (se 1 (by rfl) ⟨7016624, by rfl⟩ : syracuseStep 9355499 = 14033249) B14033249
theorem B115384753 : Blo 1847625 115384753 := bstep (se 2 (by rfl) ⟨43269282, by rfl⟩ : syracuseStep 115384753 = 86538565) B86538565
theorem B12001871 : Blo 1847625 12001871 := bstep (se 1 (by rfl) ⟨9001403, by rfl⟩ : syracuseStep 12001871 = 18002807) B18002807
theorem B10527353 : Blo 1847625 10527353 := bstep (se 2 (by rfl) ⟨3947757, by rfl⟩ : syracuseStep 10527353 = 7895515) B7895515
theorem B47383541 : Blo 1847625 47383541 := bstep (se 5 (by rfl) ⟨2221103, by rfl⟩ : syracuseStep 47383541 = 4442207) B4442207
theorem B10527853 : Blo 1847625 10527853 := bstep (se 3 (by rfl) ⟨1973972, by rfl⟩ : syracuseStep 10527853 = 3947945) B3947945
theorem B39978481 : Blo 1847625 39978481 := bstep (se 2 (by rfl) ⟨14991930, by rfl⟩ : syracuseStep 39978481 = 29983861) B29983861
theorem B9357119 : Blo 1847625 9357119 := bstep (se 1 (by rfl) ⟨7017839, by rfl⟩ : syracuseStep 9357119 = 14035679) B14035679
theorem B3508123 : Blo 1847625 3508123 := bstep (se 1 (by rfl) ⟨2631092, by rfl⟩ : syracuseStep 3508123 = 5262185) B5262185
theorem B6236783 : Blo 1847625 6236783 := bstep (se 1 (by rfl) ⟨4677587, by rfl⟩ : syracuseStep 6236783 = 9355175) B9355175
theorem B2771675 : Blo 1847625 2771675 := bstep (se 1 (by rfl) ⟨2078756, by rfl⟩ : syracuseStep 2771675 = 4157513) B4157513
theorem B5262059 : Blo 1847625 5262059 := bstep (se 1 (by rfl) ⟨3946544, by rfl⟩ : syracuseStep 5262059 = 7893089) B7893089
theorem B2771711 : Blo 1847625 2771711 := bstep (se 1 (by rfl) ⟨2078783, by rfl⟩ : syracuseStep 2771711 = 4157567) B4157567
theorem B8006843 : Blo 1847625 8006843 := bstep (se 1 (by rfl) ⟨6005132, by rfl⟩ : syracuseStep 8006843 = 12010265) B12010265
theorem B14044427 : Blo 1847625 14044427 := bstep (se 1 (by rfl) ⟨10533320, by rfl⟩ : syracuseStep 14044427 = 21066641) B21066641
theorem B2772431 : Blo 1847625 2772431 := bstep (se 1 (by rfl) ⟨2079323, by rfl⟩ : syracuseStep 2772431 = 4158647) B4158647
theorem B21065183 : Blo 1847625 21065183 := bstep (se 1 (by rfl) ⟨15798887, by rfl⟩ : syracuseStep 21065183 = 31597775) B31597775
theorem B2772521 : Blo 1847625 2772521 := bstep (se 2 (by rfl) ⟨1039695, by rfl⟩ : syracuseStep 2772521 = 2079391) B2079391
theorem B3509831 : Blo 1847625 3509831 := bstep (se 1 (by rfl) ⟨2632373, by rfl⟩ : syracuseStep 3509831 = 5264747) B5264747
theorem B16862863 : Blo 1847625 16862863 := bstep (se 1 (by rfl) ⟨12647147, by rfl⟩ : syracuseStep 16862863 = 25294295) B25294295
theorem B4681435 : Blo 1847625 4681435 := bstep (se 1 (by rfl) ⟨3511076, by rfl⟩ : syracuseStep 4681435 = 7022153) B7022153
theorem B16863005 : Blo 1847625 16863005 := bstep (se 3 (by rfl) ⟨3161813, by rfl⟩ : syracuseStep 16863005 = 6323627) B6323627
theorem B2772815 : Blo 1847625 2772815 := bstep (se 1 (by rfl) ⟨2079611, by rfl⟩ : syracuseStep 2772815 = 4159223) B4159223
theorem B2772935 : Blo 1847625 2772935 := bstep (se 1 (by rfl) ⟨2079701, by rfl⟩ : syracuseStep 2772935 = 4159403) B4159403
theorem B23425001 : Blo 1847625 23425001 := bstep (se 2 (by rfl) ⟨8784375, by rfl⟩ : syracuseStep 23425001 = 17568751) B17568751
theorem B14995439 : Blo 1847625 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B2773019 : Blo 1847625 2773019 := bstep (se 1 (by rfl) ⟨2079764, by rfl⟩ : syracuseStep 2773019 = 4159529) B4159529
theorem B4681759 : Blo 1847625 4681759 := bstep (se 1 (by rfl) ⟨3511319, by rfl⟩ : syracuseStep 4681759 = 7022639) B7022639
theorem B23695415 : Blo 1847625 23695415 := bstep (se 1 (by rfl) ⟨17771561, by rfl⟩ : syracuseStep 23695415 = 35543123) B35543123
theorem B4157639 : Blo 1847625 4157639 := bstep (se 1 (by rfl) ⟨3118229, by rfl⟩ : syracuseStep 4157639 = 6236459) B6236459
theorem B3330323 : Blo 1847625 3330323 := bstep (se 1 (by rfl) ⟨2497742, by rfl⟩ : syracuseStep 3330323 = 4995485) B4995485
theorem B2773295 : Blo 1847625 2773295 := bstep (se 1 (by rfl) ⟨2079971, by rfl⟩ : syracuseStep 2773295 = 4159943) B4159943
theorem B4157819 : Blo 1847625 4157819 := bstep (se 1 (by rfl) ⟨3118364, by rfl⟩ : syracuseStep 4157819 = 6236729) B6236729
theorem B2773403 : Blo 1847625 2773403 := bstep (se 1 (by rfl) ⟨2080052, by rfl⟩ : syracuseStep 2773403 = 4160105) B4160105
theorem B2773439 : Blo 1847625 2773439 := bstep (se 1 (by rfl) ⟨2080079, by rfl⟩ : syracuseStep 2773439 = 4160159) B4160159
theorem B1847835 : Blo 1847625 1847835 := bstep (se 1 (by rfl) ⟨1385876, by rfl⟩ : syracuseStep 1847835 = 2771753) B2771753
theorem B2773535 : Blo 1847625 2773535 := bstep (se 1 (by rfl) ⟨2080151, by rfl⟩ : syracuseStep 2773535 = 4160303) B4160303
theorem B4158089 : Blo 1847625 4158089 := bstep (se 2 (by rfl) ⟨1559283, by rfl⟩ : syracuseStep 4158089 = 3118567) B3118567
theorem B1847975 : Blo 1847625 1847975 := bstep (se 1 (by rfl) ⟨1385981, by rfl⟩ : syracuseStep 1847975 = 2771963) B2771963
theorem B1848015 : Blo 1847625 1848015 := bstep (se 1 (by rfl) ⟨1386011, by rfl⟩ : syracuseStep 1848015 = 2772023) B2772023
theorem B1848095 : Blo 1847625 1848095 := bstep (se 1 (by rfl) ⟨1386071, by rfl⟩ : syracuseStep 1848095 = 2772143) B2772143
theorem B2773823 : Blo 1847625 2773823 := bstep (se 1 (by rfl) ⟨2080367, by rfl⟩ : syracuseStep 2773823 = 4160735) B4160735
theorem B4158305 : Blo 1847625 4158305 := bstep (se 2 (by rfl) ⟨1559364, by rfl⟩ : syracuseStep 4158305 = 3118729) B3118729
theorem B2773967 : Blo 1847625 2773967 := bstep (se 1 (by rfl) ⟨2080475, by rfl⟩ : syracuseStep 2773967 = 4160951) B4160951
theorem B3511289 : Blo 1847625 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B2774057 : Blo 1847625 2774057 := bstep (se 2 (by rfl) ⟨1040271, by rfl⟩ : syracuseStep 2774057 = 2080543) B2080543
theorem B2774087 : Blo 1847625 2774087 := bstep (se 1 (by rfl) ⟨2080565, by rfl⟩ : syracuseStep 2774087 = 4161131) B4161131
theorem B11842811 : Blo 1847625 11842811 := bstep (se 1 (by rfl) ⟨8882108, by rfl⟩ : syracuseStep 11842811 = 17764217) B17764217
theorem B1848575 : Blo 1847625 1848575 := bstep (se 1 (by rfl) ⟨1386431, by rfl⟩ : syracuseStep 1848575 = 2772863) B2772863
theorem B2774267 : Blo 1847625 2774267 := bstep (se 1 (by rfl) ⟨2080700, by rfl⟩ : syracuseStep 2774267 = 4161401) B4161401
theorem B2774327 : Blo 1847625 2774327 := bstep (se 1 (by rfl) ⟨2080745, by rfl⟩ : syracuseStep 2774327 = 4161491) B4161491
theorem B4158827 : Blo 1847625 4158827 := bstep (se 1 (by rfl) ⟨3119120, by rfl⟩ : syracuseStep 4158827 = 6238241) B6238241
theorem B1848703 : Blo 1847625 1848703 := bstep (se 1 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 1848703 = 2773055) B2773055
theorem B5920175 : Blo 1847625 5920175 := bstep (se 1 (by rfl) ⟨4440131, by rfl⟩ : syracuseStep 5920175 = 8880263) B8880263
theorem B4003283 : Blo 1847625 4003283 := bstep (se 1 (by rfl) ⟨3002462, by rfl⟩ : syracuseStep 4003283 = 6004925) B6004925
theorem B16856585 : Blo 1847625 16856585 := bstep (se 2 (by rfl) ⟨6321219, by rfl⟩ : syracuseStep 16856585 = 12642439) B12642439
theorem B22787609 : Blo 1847625 22787609 := bstep (se 2 (by rfl) ⟨8545353, by rfl⟩ : syracuseStep 22787609 = 17090707) B17090707
theorem B1848859 : Blo 1847625 1848859 := bstep (se 1 (by rfl) ⟨1386644, by rfl⟩ : syracuseStep 1848859 = 2773289) B2773289
theorem B5264975 : Blo 1847625 5264975 := bstep (se 1 (by rfl) ⟨3948731, by rfl⟩ : syracuseStep 5264975 = 7897463) B7897463
theorem B4159079 : Blo 1847625 4159079 := bstep (se 1 (by rfl) ⟨3119309, by rfl⟩ : syracuseStep 4159079 = 6238619) B6238619
theorem B4159097 : Blo 1847625 4159097 := bstep (se 2 (by rfl) ⟨1559661, by rfl⟩ : syracuseStep 4159097 = 3119323) B3119323
theorem B1849039 : Blo 1847625 1849039 := bstep (se 1 (by rfl) ⟨1386779, by rfl⟩ : syracuseStep 1849039 = 2773559) B2773559
theorem B1849279 : Blo 1847625 1849279 := bstep (se 1 (by rfl) ⟨1386959, by rfl⟩ : syracuseStep 1849279 = 2773919) B2773919
theorem B13326281 : Blo 1847625 13326281 := bstep (se 2 (by rfl) ⟨4997355, by rfl⟩ : syracuseStep 13326281 = 9994711) B9994711
theorem B29972443 : Blo 1847625 29972443 := bstep (se 1 (by rfl) ⟨22479332, by rfl⟩ : syracuseStep 29972443 = 44958665) B44958665
theorem B4159457 : Blo 1847625 4159457 := bstep (se 2 (by rfl) ⟨1559796, by rfl⟩ : syracuseStep 4159457 = 3119593) B3119593
theorem B1849407 : Blo 1847625 1849407 := bstep (se 1 (by rfl) ⟨1387055, by rfl⟩ : syracuseStep 1849407 = 2774111) B2774111
theorem B1849447 : Blo 1847625 1849447 := bstep (se 1 (by rfl) ⟨1387085, by rfl⟩ : syracuseStep 1849447 = 2774171) B2774171
theorem B4159655 : Blo 1847625 4159655 := bstep (se 1 (by rfl) ⟨3119741, by rfl⟩ : syracuseStep 4159655 = 6239483) B6239483
theorem B24344759 : Blo 1847625 24344759 := bstep (se 1 (by rfl) ⟨18258569, by rfl⟩ : syracuseStep 24344759 = 36517139) B36517139
theorem B21068099 : Blo 1847625 21068099 := bstep (se 1 (by rfl) ⟨15801074, by rfl⟩ : syracuseStep 21068099 = 31602149) B31602149
theorem B4995689 : Blo 1847625 4995689 := bstep (se 2 (by rfl) ⟨1873383, by rfl⟩ : syracuseStep 4995689 = 3746767) B3746767
theorem B129874661 : Blo 1847625 129874661 := bstep (se 4 (by rfl) ⟨12175749, by rfl⟩ : syracuseStep 129874661 = 24351499) B24351499
theorem B9354041 : Blo 1847625 9354041 := bstep (se 2 (by rfl) ⟨3507765, by rfl⟩ : syracuseStep 9354041 = 7015531) B7015531
theorem B5921599 : Blo 1847625 5921599 := bstep (se 1 (by rfl) ⟨4441199, by rfl⟩ : syracuseStep 5921599 = 8882399) B8882399
theorem B2079679 : Blo 1847625 2079679 := bstep (se 1 (by rfl) ⟨1559759, by rfl⟩ : syracuseStep 2079679 = 3119519) B3119519
theorem B5266387 : Blo 1847625 5266387 := bstep (se 1 (by rfl) ⟨3949790, by rfl⟩ : syracuseStep 5266387 = 7899581) B7899581
theorem B24001505 : Blo 1847625 24001505 := bstep (se 2 (by rfl) ⟨9000564, by rfl⟩ : syracuseStep 24001505 = 18001129) B18001129
theorem B43293761 : Blo 1847625 43293761 := bstep (se 2 (by rfl) ⟨16235160, by rfl⟩ : syracuseStep 43293761 = 32470321) B32470321
theorem B9354365 : Blo 1847625 9354365 := bstep (se 3 (by rfl) ⟨1753943, by rfl⟩ : syracuseStep 9354365 = 3507887) B3507887
theorem B119921957 : Blo 1847625 119921957 := bstep (se 4 (by rfl) ⟨11242683, by rfl⟩ : syracuseStep 119921957 = 22485367) B22485367
theorem B39992939 : Blo 1847625 39992939 := bstep (se 1 (by rfl) ⟨29994704, by rfl⟩ : syracuseStep 39992939 = 59989409) B59989409
theorem B115416737 : Blo 1847625 115416737 := bstep (se 2 (by rfl) ⟨43281276, by rfl⟩ : syracuseStep 115416737 = 86562553) B86562553
theorem B10526395 : Blo 1847625 10526395 := bstep (se 1 (by rfl) ⟨7894796, by rfl⟩ : syracuseStep 10526395 = 15789593) B15789593
theorem B2080507 : Blo 1847625 2080507 := bstep (se 1 (by rfl) ⟨1560380, by rfl⟩ : syracuseStep 2080507 = 3120761) B3120761
theorem B6242345 : Blo 1847625 6242345 := bstep (se 2 (by rfl) ⟨2340879, by rfl⟩ : syracuseStep 6242345 = 4681759) B4681759
theorem B2220215 : Blo 1847625 2220215 := bstep (se 1 (by rfl) ⟨1665161, by rfl⟩ : syracuseStep 2220215 = 3330323) B3330323
theorem B153846337 : Blo 1847625 153846337 := bstep (se 2 (by rfl) ⟨57692376, by rfl⟩ : syracuseStep 153846337 = 115384753) B115384753
theorem B31589027 : Blo 1847625 31589027 := bstep (se 1 (by rfl) ⟨23691770, by rfl⟩ : syracuseStep 31589027 = 47383541) B47383541
theorem B15787133 : Blo 1847625 15787133 := bstep (se 3 (by rfl) ⟨2960087, by rfl⟩ : syracuseStep 15787133 = 5920175) B5920175
theorem B10675421 : Blo 1847625 10675421 := bstep (se 3 (by rfl) ⟨2001641, by rfl⟩ : syracuseStep 10675421 = 4003283) B4003283
theorem B7021849 : Blo 1847625 7021849 := bstep (se 2 (by rfl) ⟨2633193, by rfl⟩ : syracuseStep 7021849 = 5266387) B5266387
theorem B13321837 : Blo 1847625 13321837 := bstep (se 3 (by rfl) ⟨2497844, by rfl⟩ : syracuseStep 13321837 = 4995689) B4995689
theorem B86583107 : Blo 1847625 86583107 := bstep (se 1 (by rfl) ⟨64937330, by rfl⟩ : syracuseStep 86583107 = 129874661) B129874661
theorem B3508039 : Blo 1847625 3508039 := bstep (se 1 (by rfl) ⟨2631029, by rfl⟩ : syracuseStep 3508039 = 5262059) B5262059
theorem B6236027 : Blo 1847625 6236027 := bstep (se 1 (by rfl) ⟨4677020, by rfl⟩ : syracuseStep 6236027 = 9354041) B9354041
theorem B16001003 : Blo 1847625 16001003 := bstep (se 1 (by rfl) ⟨12000752, by rfl⟩ : syracuseStep 16001003 = 24001505) B24001505
theorem B28862507 : Blo 1847625 28862507 := bstep (se 1 (by rfl) ⟨21646880, by rfl⟩ : syracuseStep 28862507 = 43293761) B43293761
theorem B6236243 : Blo 1847625 6236243 := bstep (se 1 (by rfl) ⟨4677182, by rfl⟩ : syracuseStep 6236243 = 9354365) B9354365
theorem B79947971 : Blo 1847625 79947971 := bstep (se 1 (by rfl) ⟨59960978, by rfl⟩ : syracuseStep 79947971 = 119921957) B119921957
theorem B14035193 : Blo 1847625 14035193 := bstep (se 2 (by rfl) ⟨5263197, by rfl⟩ : syracuseStep 14035193 = 10526395) B10526395
theorem B14043455 : Blo 1847625 14043455 := bstep (se 1 (by rfl) ⟨10532591, by rfl⟩ : syracuseStep 14043455 = 21065183) B21065183
theorem B11242003 : Blo 1847625 11242003 := bstep (se 1 (by rfl) ⟨8431502, by rfl⟩ : syracuseStep 11242003 = 16863005) B16863005
theorem B39963257 : Blo 1847625 39963257 := bstep (se 2 (by rfl) ⟨14986221, by rfl⟩ : syracuseStep 39963257 = 29972443) B29972443
theorem B15616667 : Blo 1847625 15616667 := bstep (se 1 (by rfl) ⟨11712500, by rfl⟩ : syracuseStep 15616667 = 23425001) B23425001
theorem B9996959 : Blo 1847625 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B15796943 : Blo 1847625 15796943 := bstep (se 1 (by rfl) ⟨11847707, by rfl⟩ : syracuseStep 15796943 = 23695415) B23695415
theorem B2771759 : Blo 1847625 2771759 := bstep (se 1 (by rfl) ⟨2078819, by rfl⟩ : syracuseStep 2771759 = 4157639) B4157639
theorem B6236999 : Blo 1847625 6236999 := bstep (se 1 (by rfl) ⟨4677749, by rfl⟩ : syracuseStep 6236999 = 9355499) B9355499
theorem B2771879 : Blo 1847625 2771879 := bstep (se 1 (by rfl) ⟨2078909, by rfl⟩ : syracuseStep 2771879 = 4157819) B4157819
theorem B2772059 : Blo 1847625 2772059 := bstep (se 1 (by rfl) ⟨2079044, by rfl⟩ : syracuseStep 2772059 = 4158089) B4158089
theorem B2772203 : Blo 1847625 2772203 := bstep (se 1 (by rfl) ⟨2079152, by rfl⟩ : syracuseStep 2772203 = 4158305) B4158305
theorem B59944373 : Blo 1847625 59944373 := bstep (se 5 (by rfl) ⟨2809892, by rfl⟩ : syracuseStep 59944373 = 5619785) B5619785
theorem B2772551 : Blo 1847625 2772551 := bstep (se 1 (by rfl) ⟨2079413, by rfl⟩ : syracuseStep 2772551 = 4158827) B4158827
theorem B3509983 : Blo 1847625 3509983 := bstep (se 1 (by rfl) ⟨2632487, by rfl⟩ : syracuseStep 3509983 = 5264975) B5264975
theorem B2772719 : Blo 1847625 2772719 := bstep (se 1 (by rfl) ⟨2079539, by rfl⟩ : syracuseStep 2772719 = 4159079) B4159079
theorem B2772731 : Blo 1847625 2772731 := bstep (se 1 (by rfl) ⟨2079548, by rfl⟩ : syracuseStep 2772731 = 4159097) B4159097
theorem B6238079 : Blo 1847625 6238079 := bstep (se 1 (by rfl) ⟨4678559, by rfl⟩ : syracuseStep 6238079 = 9357119) B9357119
theorem B2772905 : Blo 1847625 2772905 := bstep (se 2 (by rfl) ⟨1039839, by rfl⟩ : syracuseStep 2772905 = 2079679) B2079679
theorem B8884187 : Blo 1847625 8884187 := bstep (se 1 (by rfl) ⟨6663140, by rfl⟩ : syracuseStep 8884187 = 13326281) B13326281
theorem B2772971 : Blo 1847625 2772971 := bstep (se 1 (by rfl) ⟨2079728, by rfl⟩ : syracuseStep 2772971 = 4159457) B4159457
theorem B2773103 : Blo 1847625 2773103 := bstep (se 1 (by rfl) ⟨2079827, by rfl⟩ : syracuseStep 2773103 = 4159655) B4159655
theorem B14037137 : Blo 1847625 14037137 := bstep (se 2 (by rfl) ⟨5263926, by rfl⟩ : syracuseStep 14037137 = 10527853) B10527853
theorem B9359549 : Blo 1847625 9359549 := bstep (se 3 (by rfl) ⟨1754915, by rfl⟩ : syracuseStep 9359549 = 3509831) B3509831
theorem B14045399 : Blo 1847625 14045399 := bstep (se 1 (by rfl) ⟨10534049, by rfl⟩ : syracuseStep 14045399 = 21068099) B21068099
theorem B4157855 : Blo 1847625 4157855 := bstep (se 1 (by rfl) ⟨3118391, by rfl⟩ : syracuseStep 4157855 = 6236783) B6236783
theorem B1847783 : Blo 1847625 1847783 := bstep (se 1 (by rfl) ⟨1385837, by rfl⟩ : syracuseStep 1847783 = 2771675) B2771675
theorem B1847807 : Blo 1847625 1847807 := bstep (se 1 (by rfl) ⟨1385855, by rfl⟩ : syracuseStep 1847807 = 2771711) B2771711
theorem B5337895 : Blo 1847625 5337895 := bstep (se 1 (by rfl) ⟨4003421, by rfl⟩ : syracuseStep 5337895 = 8006843) B8006843
theorem B22483817 : Blo 1847625 22483817 := bstep (se 2 (by rfl) ⟨8431431, by rfl⟩ : syracuseStep 22483817 = 16862863) B16862863
theorem B1848287 : Blo 1847625 1848287 := bstep (se 1 (by rfl) ⟨1386215, by rfl⟩ : syracuseStep 1848287 = 2772431) B2772431
theorem B2774009 : Blo 1847625 2774009 := bstep (se 2 (by rfl) ⟨1040253, by rfl⟩ : syracuseStep 2774009 = 2080507) B2080507
theorem B1848347 : Blo 1847625 1848347 := bstep (se 1 (by rfl) ⟨1386260, by rfl⟩ : syracuseStep 1848347 = 2772521) B2772521
theorem B26661959 : Blo 1847625 26661959 := bstep (se 1 (by rfl) ⟨19996469, by rfl⟩ : syracuseStep 26661959 = 39992939) B39992939
theorem B76944491 : Blo 1847625 76944491 := bstep (se 1 (by rfl) ⟨57708368, by rfl⟩ : syracuseStep 76944491 = 115416737) B115416737
theorem B1848543 : Blo 1847625 1848543 := bstep (se 1 (by rfl) ⟨1386407, by rfl⟩ : syracuseStep 1848543 = 2772815) B2772815
theorem B1848623 : Blo 1847625 1848623 := bstep (se 1 (by rfl) ⟨1386467, by rfl⟩ : syracuseStep 1848623 = 2772935) B2772935
theorem B1848679 : Blo 1847625 1848679 := bstep (se 1 (by rfl) ⟨1386509, by rfl⟩ : syracuseStep 1848679 = 2773019) B2773019
theorem B1848863 : Blo 1847625 1848863 := bstep (se 1 (by rfl) ⟨1386647, by rfl⟩ : syracuseStep 1848863 = 2773295) B2773295
theorem B1848935 : Blo 1847625 1848935 := bstep (se 1 (by rfl) ⟨1386701, by rfl⟩ : syracuseStep 1848935 = 2773403) B2773403
theorem B1848959 : Blo 1847625 1848959 := bstep (se 1 (by rfl) ⟨1386719, by rfl⟩ : syracuseStep 1848959 = 2773439) B2773439
theorem B1849023 : Blo 1847625 1849023 := bstep (se 1 (by rfl) ⟨1386767, by rfl⟩ : syracuseStep 1849023 = 2773535) B2773535
theorem B8001247 : Blo 1847625 8001247 := bstep (se 1 (by rfl) ⟨6000935, by rfl⟩ : syracuseStep 8001247 = 12001871) B12001871
theorem B7018235 : Blo 1847625 7018235 := bstep (se 1 (by rfl) ⟨5263676, by rfl⟩ : syracuseStep 7018235 = 10527353) B10527353
theorem B64919357 : Blo 1847625 64919357 := bstep (se 3 (by rfl) ⟨12172379, by rfl⟩ : syracuseStep 64919357 = 24344759) B24344759
theorem B1849215 : Blo 1847625 1849215 := bstep (se 1 (by rfl) ⟨1386911, by rfl⟩ : syracuseStep 1849215 = 2773823) B2773823
theorem B1849311 : Blo 1847625 1849311 := bstep (se 1 (by rfl) ⟨1386983, by rfl⟩ : syracuseStep 1849311 = 2773967) B2773967
theorem B1849371 : Blo 1847625 1849371 := bstep (se 1 (by rfl) ⟨1387028, by rfl⟩ : syracuseStep 1849371 = 2774057) B2774057
theorem B1849391 : Blo 1847625 1849391 := bstep (se 1 (by rfl) ⟨1387043, by rfl⟩ : syracuseStep 1849391 = 2774087) B2774087
theorem B7895207 : Blo 1847625 7895207 := bstep (se 1 (by rfl) ⟨5921405, by rfl⟩ : syracuseStep 7895207 = 11842811) B11842811
theorem B1849511 : Blo 1847625 1849511 := bstep (se 1 (by rfl) ⟨1387133, by rfl⟩ : syracuseStep 1849511 = 2774267) B2774267
theorem B1849551 : Blo 1847625 1849551 := bstep (se 1 (by rfl) ⟨1387163, by rfl⟩ : syracuseStep 1849551 = 2774327) B2774327
theorem B11237723 : Blo 1847625 11237723 := bstep (se 1 (by rfl) ⟨8428292, by rfl⟩ : syracuseStep 11237723 = 16856585) B16856585
theorem B7895465 : Blo 1847625 7895465 := bstep (se 2 (by rfl) ⟨2960799, by rfl⟩ : syracuseStep 7895465 = 5921599) B5921599
theorem B60766957 : Blo 1847625 60766957 := bstep (se 3 (by rfl) ⟨11393804, by rfl⟩ : syracuseStep 60766957 = 22787609) B22787609
theorem B53304641 : Blo 1847625 53304641 := bstep (se 2 (by rfl) ⟨19989240, by rfl⟩ : syracuseStep 53304641 = 39978481) B39978481
theorem B9362951 : Blo 1847625 9362951 := bstep (se 1 (by rfl) ⟨7022213, by rfl⟩ : syracuseStep 9362951 = 14044427) B14044427
theorem B6241913 : Blo 1847625 6241913 := bstep (se 2 (by rfl) ⟨2340717, by rfl⟩ : syracuseStep 6241913 = 4681435) B4681435
theorem B4677497 : Blo 1847625 4677497 := bstep (se 2 (by rfl) ⟨1754061, by rfl⟩ : syracuseStep 4677497 = 3508123) B3508123
theorem B9363437 : Blo 1847625 9363437 := bstep (se 3 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 9363437 = 3511289) B3511289
theorem B4161563 : Blo 1847625 4161563 := bstep (se 1 (by rfl) ⟨3121172, by rfl⟩ : syracuseStep 4161563 = 6242345) B6242345
theorem B9363599 : Blo 1847625 9363599 := bstep (se 1 (by rfl) ⟨7022699, by rfl⟩ : syracuseStep 9363599 = 14045399) B14045399
theorem B205128449 : Blo 1847625 205128449 := bstep (se 2 (by rfl) ⟨76923168, by rfl⟩ : syracuseStep 205128449 = 153846337) B153846337
theorem B4678823 : Blo 1847625 4678823 := bstep (se 1 (by rfl) ⟨3509117, by rfl⟩ : syracuseStep 4678823 = 7018235) B7018235
theorem B43279571 : Blo 1847625 43279571 := bstep (se 1 (by rfl) ⟨32459678, by rfl⟩ : syracuseStep 43279571 = 64919357) B64919357
theorem B57722071 : Blo 1847625 57722071 := bstep (se 1 (by rfl) ⟨43291553, by rfl⟩ : syracuseStep 57722071 = 86583107) B86583107
theorem B53298647 : Blo 1847625 53298647 := bstep (se 1 (by rfl) ⟨39973985, by rfl⟩ : syracuseStep 53298647 = 79947971) B79947971
theorem B9356795 : Blo 1847625 9356795 := bstep (se 1 (by rfl) ⟨7017596, by rfl⟩ : syracuseStep 9356795 = 14035193) B14035193
theorem B26642171 : Blo 1847625 26642171 := bstep (se 1 (by rfl) ⟨19981628, by rfl⟩ : syracuseStep 26642171 = 39963257) B39963257
theorem B17762449 : Blo 1847625 17762449 := bstep (se 2 (by rfl) ⟨6660918, by rfl⟩ : syracuseStep 17762449 = 13321837) B13321837
theorem B39962915 : Blo 1847625 39962915 := bstep (se 1 (by rfl) ⟨29972186, by rfl⟩ : syracuseStep 39962915 = 59944373) B59944373
theorem B10668329 : Blo 1847625 10668329 := bstep (se 2 (by rfl) ⟨4000623, by rfl⟩ : syracuseStep 10668329 = 8001247) B8001247
theorem B4679977 : Blo 1847625 4679977 := bstep (se 2 (by rfl) ⟨1754991, by rfl⟩ : syracuseStep 4679977 = 3509983) B3509983
theorem B9358091 : Blo 1847625 9358091 := bstep (se 1 (by rfl) ⟨7018568, by rfl⟩ : syracuseStep 9358091 = 14037137) B14037137
theorem B2771903 : Blo 1847625 2771903 := bstep (se 1 (by rfl) ⟨2078927, by rfl⟩ : syracuseStep 2771903 = 4157855) B4157855
theorem B81022609 : Blo 1847625 81022609 := bstep (se 2 (by rfl) ⟨30383478, by rfl⟩ : syracuseStep 81022609 = 60766957) B60766957
theorem B4157351 : Blo 1847625 4157351 := bstep (se 1 (by rfl) ⟨3118013, by rfl⟩ : syracuseStep 4157351 = 6236027) B6236027
theorem B4157495 : Blo 1847625 4157495 := bstep (se 1 (by rfl) ⟨3118121, by rfl⟩ : syracuseStep 4157495 = 6236243) B6236243
theorem B5263471 : Blo 1847625 5263471 := bstep (se 1 (by rfl) ⟨3947603, by rfl⟩ : syracuseStep 5263471 = 7895207) B7895207
theorem B7491815 : Blo 1847625 7491815 := bstep (se 1 (by rfl) ⟨5618861, by rfl⟩ : syracuseStep 7491815 = 11237723) B11237723
theorem B5263643 : Blo 1847625 5263643 := bstep (se 1 (by rfl) ⟨3947732, by rfl⟩ : syracuseStep 5263643 = 7895465) B7895465
theorem B6664639 : Blo 1847625 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B10531295 : Blo 1847625 10531295 := bstep (se 1 (by rfl) ⟨7898471, by rfl⟩ : syracuseStep 10531295 = 15796943) B15796943
theorem B1847839 : Blo 1847625 1847839 := bstep (se 1 (by rfl) ⟨1385879, by rfl⟩ : syracuseStep 1847839 = 2771759) B2771759
theorem B4157999 : Blo 1847625 4157999 := bstep (se 1 (by rfl) ⟨3118499, by rfl⟩ : syracuseStep 4157999 = 6236999) B6236999
theorem B1847919 : Blo 1847625 1847919 := bstep (se 1 (by rfl) ⟨1385939, by rfl⟩ : syracuseStep 1847919 = 2771879) B2771879
theorem B1848039 : Blo 1847625 1848039 := bstep (se 1 (by rfl) ⟨1386029, by rfl⟩ : syracuseStep 1848039 = 2772059) B2772059
theorem B1848135 : Blo 1847625 1848135 := bstep (se 1 (by rfl) ⟨1386101, by rfl⟩ : syracuseStep 1848135 = 2772203) B2772203
theorem B1848367 : Blo 1847625 1848367 := bstep (se 1 (by rfl) ⟨1386275, by rfl⟩ : syracuseStep 1848367 = 2772551) B2772551
theorem B1848479 : Blo 1847625 1848479 := bstep (se 1 (by rfl) ⟨1386359, by rfl⟩ : syracuseStep 1848479 = 2772719) B2772719
theorem B1848487 : Blo 1847625 1848487 := bstep (se 1 (by rfl) ⟨1386365, by rfl⟩ : syracuseStep 1848487 = 2772731) B2772731
theorem B3118331 : Blo 1847625 3118331 := bstep (se 1 (by rfl) ⟨2338748, by rfl⟩ : syracuseStep 3118331 = 4677497) B4677497
theorem B4158719 : Blo 1847625 4158719 := bstep (se 1 (by rfl) ⟨3119039, by rfl⟩ : syracuseStep 4158719 = 6238079) B6238079
theorem B1848603 : Blo 1847625 1848603 := bstep (se 1 (by rfl) ⟨1386452, by rfl⟩ : syracuseStep 1848603 = 2772905) B2772905
theorem B42669341 : Blo 1847625 42669341 := bstep (se 3 (by rfl) ⟨8000501, by rfl⟩ : syracuseStep 42669341 = 16001003) B16001003
theorem B1848647 : Blo 1847625 1848647 := bstep (se 1 (by rfl) ⟨1386485, by rfl⟩ : syracuseStep 1848647 = 2772971) B2772971
theorem B1848735 : Blo 1847625 1848735 := bstep (se 1 (by rfl) ⟨1386551, by rfl⟩ : syracuseStep 1848735 = 2773103) B2773103
theorem B6239699 : Blo 1847625 6239699 := bstep (se 1 (by rfl) ⟨4679774, by rfl⟩ : syracuseStep 6239699 = 9359549) B9359549
theorem B21059351 : Blo 1847625 21059351 := bstep (se 1 (by rfl) ⟨15794513, by rfl⟩ : syracuseStep 21059351 = 31589027) B31589027
theorem B14989211 : Blo 1847625 14989211 := bstep (se 1 (by rfl) ⟨11241908, by rfl⟩ : syracuseStep 14989211 = 22483817) B22483817
theorem B1849339 : Blo 1847625 1849339 := bstep (se 1 (by rfl) ⟨1387004, by rfl⟩ : syracuseStep 1849339 = 2774009) B2774009
theorem B14989337 : Blo 1847625 14989337 := bstep (se 2 (by rfl) ⟨5621001, by rfl⟩ : syracuseStep 14989337 = 11242003) B11242003
theorem B17774639 : Blo 1847625 17774639 := bstep (se 1 (by rfl) ⟨13330979, by rfl⟩ : syracuseStep 17774639 = 26661959) B26661959
theorem B51296327 : Blo 1847625 51296327 := bstep (se 1 (by rfl) ⟨38472245, by rfl⟩ : syracuseStep 51296327 = 76944491) B76944491
theorem B10524755 : Blo 1847625 10524755 := bstep (se 1 (by rfl) ⟨7893566, by rfl⟩ : syracuseStep 10524755 = 15787133) B15787133
theorem B7116947 : Blo 1847625 7116947 := bstep (se 1 (by rfl) ⟨5337710, by rfl⟩ : syracuseStep 7116947 = 10675421) B10675421
theorem B7117193 : Blo 1847625 7117193 := bstep (se 2 (by rfl) ⟨2668947, by rfl⟩ : syracuseStep 7117193 = 5337895) B5337895
theorem B19241671 : Blo 1847625 19241671 := bstep (se 1 (by rfl) ⟨14431253, by rfl⟩ : syracuseStep 19241671 = 28862507) B28862507
theorem B9362303 : Blo 1847625 9362303 := bstep (se 1 (by rfl) ⟨7021727, by rfl⟩ : syracuseStep 9362303 = 14043455) B14043455
theorem B9362465 : Blo 1847625 9362465 := bstep (se 2 (by rfl) ⟨3510924, by rfl⟩ : syracuseStep 9362465 = 7021849) B7021849
theorem B10411111 : Blo 1847625 10411111 := bstep (se 1 (by rfl) ⟨7808333, by rfl⟩ : syracuseStep 10411111 = 15616667) B15616667
theorem B23682293 : Blo 1847625 23682293 := bstep (se 5 (by rfl) ⟨1110107, by rfl⟩ : syracuseStep 23682293 = 2220215) B2220215
theorem B35536427 : Blo 1847625 35536427 := bstep (se 1 (by rfl) ⟨26652320, by rfl⟩ : syracuseStep 35536427 = 53304641) B53304641
theorem B6241967 : Blo 1847625 6241967 := bstep (se 1 (by rfl) ⟨4681475, by rfl⟩ : syracuseStep 6241967 = 9362951) B9362951
theorem B4161275 : Blo 1847625 4161275 := bstep (se 1 (by rfl) ⟨3120956, by rfl⟩ : syracuseStep 4161275 = 6241913) B6241913
theorem B4677385 : Blo 1847625 4677385 := bstep (se 2 (by rfl) ⟨1754019, by rfl⟩ : syracuseStep 4677385 = 3508039) B3508039
theorem B5922791 : Blo 1847625 5922791 := bstep (se 1 (by rfl) ⟨4442093, by rfl⟩ : syracuseStep 5922791 = 8884187) B8884187
theorem B6242291 : Blo 1847625 6242291 := bstep (se 1 (by rfl) ⟨4681718, by rfl⟩ : syracuseStep 6242291 = 9363437) B9363437
theorem B6242399 : Blo 1847625 6242399 := bstep (se 1 (by rfl) ⟨4681799, by rfl⟩ : syracuseStep 6242399 = 9363599) B9363599
theorem B23683265 : Blo 1847625 23683265 := bstep (se 2 (by rfl) ⟨8881224, by rfl⟩ : syracuseStep 23683265 = 17762449) B17762449
theorem B7020863 : Blo 1847625 7020863 := bstep (se 1 (by rfl) ⟨5265647, by rfl⟩ : syracuseStep 7020863 = 10531295) B10531295
theorem B55525925 : Blo 1847625 55525925 := bstep (se 4 (by rfl) ⟨5205555, by rfl⟩ : syracuseStep 55525925 = 10411111) B10411111
theorem B28853047 : Blo 1847625 28853047 := bstep (se 1 (by rfl) ⟨21639785, by rfl⟩ : syracuseStep 28853047 = 43279571) B43279571
theorem B17761447 : Blo 1847625 17761447 := bstep (se 1 (by rfl) ⟨13321085, by rfl⟩ : syracuseStep 17761447 = 26642171) B26642171
theorem B4744631 : Blo 1847625 4744631 := bstep (se 1 (by rfl) ⟨3558473, by rfl⟩ : syracuseStep 4744631 = 7116947) B7116947
theorem B26641943 : Blo 1847625 26641943 := bstep (se 1 (by rfl) ⟨19981457, by rfl⟩ : syracuseStep 26641943 = 39962915) B39962915
theorem B7112219 : Blo 1847625 7112219 := bstep (se 1 (by rfl) ⟨5334164, by rfl⟩ : syracuseStep 7112219 = 10668329) B10668329
theorem B15788195 : Blo 1847625 15788195 := bstep (se 1 (by rfl) ⟨11841146, by rfl⟩ : syracuseStep 15788195 = 23682293) B23682293
theorem B108030145 : Blo 1847625 108030145 := bstep (se 2 (by rfl) ⟨40511304, by rfl⟩ : syracuseStep 108030145 = 81022609) B81022609
theorem B6236513 : Blo 1847625 6236513 := bstep (se 2 (by rfl) ⟨2338692, by rfl⟩ : syracuseStep 6236513 = 4677385) B4677385
theorem B2771567 : Blo 1847625 2771567 := bstep (se 1 (by rfl) ⟨2078675, by rfl⟩ : syracuseStep 2771567 = 4157351) B4157351
theorem B2771663 : Blo 1847625 2771663 := bstep (se 1 (by rfl) ⟨2078747, by rfl⟩ : syracuseStep 2771663 = 4157495) B4157495
theorem B3509095 : Blo 1847625 3509095 := bstep (se 1 (by rfl) ⟨2631821, by rfl⟩ : syracuseStep 3509095 = 5263643) B5263643
theorem B2771999 : Blo 1847625 2771999 := bstep (se 1 (by rfl) ⟨2078999, by rfl⟩ : syracuseStep 2771999 = 4157999) B4157999
theorem B136752299 : Blo 1847625 136752299 := bstep (se 1 (by rfl) ⟨102564224, by rfl⟩ : syracuseStep 136752299 = 205128449) B205128449
theorem B2772479 : Blo 1847625 2772479 := bstep (se 1 (by rfl) ⟨2079359, by rfl⟩ : syracuseStep 2772479 = 4158719) B4158719
theorem B28446227 : Blo 1847625 28446227 := bstep (se 1 (by rfl) ⟨21334670, by rfl⟩ : syracuseStep 28446227 = 42669341) B42669341
theorem B35532431 : Blo 1847625 35532431 := bstep (se 1 (by rfl) ⟨26649323, by rfl⟩ : syracuseStep 35532431 = 53298647) B53298647
theorem B6237863 : Blo 1847625 6237863 := bstep (se 1 (by rfl) ⟨4678397, by rfl⟩ : syracuseStep 6237863 = 9356795) B9356795
theorem B11849759 : Blo 1847625 11849759 := bstep (se 1 (by rfl) ⟨8887319, by rfl⟩ : syracuseStep 11849759 = 17774639) B17774639
theorem B34197551 : Blo 1847625 34197551 := bstep (se 1 (by rfl) ⟨25648163, by rfl⟩ : syracuseStep 34197551 = 51296327) B51296327
theorem B7016503 : Blo 1847625 7016503 := bstep (se 1 (by rfl) ⟨5262377, by rfl⟩ : syracuseStep 7016503 = 10524755) B10524755
theorem B6238727 : Blo 1847625 6238727 := bstep (se 1 (by rfl) ⟨4679045, by rfl⟩ : syracuseStep 6238727 = 9358091) B9358091
theorem B1847935 : Blo 1847625 1847935 := bstep (se 1 (by rfl) ⟨1385951, by rfl⟩ : syracuseStep 1847935 = 2771903) B2771903
theorem B2774183 : Blo 1847625 2774183 := bstep (se 1 (by rfl) ⟨2080637, by rfl⟩ : syracuseStep 2774183 = 4161275) B4161275
theorem B2774375 : Blo 1847625 2774375 := bstep (se 1 (by rfl) ⟨2080781, by rfl⟩ : syracuseStep 2774375 = 4161563) B4161563
theorem B7017961 : Blo 1847625 7017961 := bstep (se 2 (by rfl) ⟨2631735, by rfl⟩ : syracuseStep 7017961 = 5263471) B5263471
theorem B4994543 : Blo 1847625 4994543 := bstep (se 1 (by rfl) ⟨3745907, by rfl⟩ : syracuseStep 4994543 = 7491815) B7491815
theorem B6239969 : Blo 1847625 6239969 := bstep (se 2 (by rfl) ⟨2339988, by rfl⟩ : syracuseStep 6239969 = 4679977) B4679977
theorem B8886185 : Blo 1847625 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B3119215 : Blo 1847625 3119215 := bstep (se 1 (by rfl) ⟨2339411, by rfl⟩ : syracuseStep 3119215 = 4678823) B4678823
theorem B2078887 : Blo 1847625 2078887 := bstep (se 1 (by rfl) ⟨1559165, by rfl⟩ : syracuseStep 2078887 = 3118331) B3118331
theorem B25655561 : Blo 1847625 25655561 := bstep (se 2 (by rfl) ⟨9620835, by rfl⟩ : syracuseStep 25655561 = 19241671) B19241671
theorem B4159799 : Blo 1847625 4159799 := bstep (se 1 (by rfl) ⟨3119849, by rfl⟩ : syracuseStep 4159799 = 6239699) B6239699
theorem B18979181 : Blo 1847625 18979181 := bstep (se 3 (by rfl) ⟨3558596, by rfl⟩ : syracuseStep 18979181 = 7117193) B7117193
theorem B14039567 : Blo 1847625 14039567 := bstep (se 1 (by rfl) ⟨10529675, by rfl⟩ : syracuseStep 14039567 = 21059351) B21059351
theorem B9992807 : Blo 1847625 9992807 := bstep (se 1 (by rfl) ⟨7494605, by rfl⟩ : syracuseStep 9992807 = 14989211) B14989211
theorem B9992891 : Blo 1847625 9992891 := bstep (se 1 (by rfl) ⟨7494668, by rfl⟩ : syracuseStep 9992891 = 14989337) B14989337
theorem B76962761 : Blo 1847625 76962761 := bstep (se 2 (by rfl) ⟨28861035, by rfl⟩ : syracuseStep 76962761 = 57722071) B57722071
theorem B4161527 : Blo 1847625 4161527 := bstep (se 1 (by rfl) ⟨3121145, by rfl⟩ : syracuseStep 4161527 = 6242291) B6242291
theorem B6241535 : Blo 1847625 6241535 := bstep (se 1 (by rfl) ⟨4681151, by rfl⟩ : syracuseStep 6241535 = 9362303) B9362303
theorem B6241643 : Blo 1847625 6241643 := bstep (se 1 (by rfl) ⟨4681232, by rfl⟩ : syracuseStep 6241643 = 9362465) B9362465
theorem B23690951 : Blo 1847625 23690951 := bstep (se 1 (by rfl) ⟨17768213, by rfl⟩ : syracuseStep 23690951 = 35536427) B35536427
theorem B4161311 : Blo 1847625 4161311 := bstep (se 1 (by rfl) ⟨3120983, by rfl⟩ : syracuseStep 4161311 = 6241967) B6241967
theorem B3948527 : Blo 1847625 3948527 := bstep (se 1 (by rfl) ⟨2961395, by rfl⟩ : syracuseStep 3948527 = 5922791) B5922791
theorem B22798367 : Blo 1847625 22798367 := bstep (se 1 (by rfl) ⟨17098775, by rfl⟩ : syracuseStep 22798367 = 34197551) B34197551
theorem B4161599 : Blo 1847625 4161599 := bstep (se 1 (by rfl) ⟨3121199, by rfl⟩ : syracuseStep 4161599 = 6242399) B6242399
theorem B9355337 : Blo 1847625 9355337 := bstep (se 2 (by rfl) ⟨3508251, by rfl⟩ : syracuseStep 9355337 = 7016503) B7016503
theorem B144040193 : Blo 1847625 144040193 := bstep (se 2 (by rfl) ⟨54015072, by rfl⟩ : syracuseStep 144040193 = 108030145) B108030145
theorem B3163087 : Blo 1847625 3163087 := bstep (se 1 (by rfl) ⟨2372315, by rfl⟩ : syracuseStep 3163087 = 4744631) B4744631
theorem B17761295 : Blo 1847625 17761295 := bstep (se 1 (by rfl) ⟨13320971, by rfl⟩ : syracuseStep 17761295 = 26641943) B26641943
theorem B38470729 : Blo 1847625 38470729 := bstep (se 2 (by rfl) ⟨14426523, by rfl⟩ : syracuseStep 38470729 = 28853047) B28853047
theorem B4678793 : Blo 1847625 4678793 := bstep (se 2 (by rfl) ⟨1754547, by rfl⟩ : syracuseStep 4678793 = 3509095) B3509095
theorem B5924123 : Blo 1847625 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B18965917 : Blo 1847625 18965917 := bstep (se 3 (by rfl) ⟨3556109, by rfl⟩ : syracuseStep 18965917 = 7112219) B7112219
theorem B6661871 : Blo 1847625 6661871 := bstep (se 1 (by rfl) ⟨4996403, by rfl⟩ : syracuseStep 6661871 = 9992807) B9992807
theorem B6661927 : Blo 1847625 6661927 := bstep (se 1 (by rfl) ⟨4996445, by rfl⟩ : syracuseStep 6661927 = 9992891) B9992891
theorem B51308507 : Blo 1847625 51308507 := bstep (se 1 (by rfl) ⟨38481380, by rfl⟩ : syracuseStep 51308507 = 76962761) B76962761
theorem B9357281 : Blo 1847625 9357281 := bstep (se 2 (by rfl) ⟨3508980, by rfl⟩ : syracuseStep 9357281 = 7017961) B7017961
theorem B2632351 : Blo 1847625 2632351 := bstep (se 1 (by rfl) ⟨1974263, by rfl⟩ : syracuseStep 2632351 = 3948527) B3948527
theorem B7899839 : Blo 1847625 7899839 := bstep (se 1 (by rfl) ⟨5924879, by rfl⟩ : syracuseStep 7899839 = 11849759) B11849759
theorem B15788843 : Blo 1847625 15788843 := bstep (se 1 (by rfl) ⟨11841632, by rfl⟩ : syracuseStep 15788843 = 23683265) B23683265
theorem B4680575 : Blo 1847625 4680575 := bstep (se 1 (by rfl) ⟨3510431, by rfl⟩ : syracuseStep 4680575 = 7020863) B7020863
theorem B2771849 : Blo 1847625 2771849 := bstep (se 2 (by rfl) ⟨1039443, by rfl⟩ : syracuseStep 2771849 = 2078887) B2078887
theorem B3329695 : Blo 1847625 3329695 := bstep (se 1 (by rfl) ⟨2497271, by rfl⟩ : syracuseStep 3329695 = 4994543) B4994543
theorem B2773199 : Blo 1847625 2773199 := bstep (se 1 (by rfl) ⟨2079899, by rfl⟩ : syracuseStep 2773199 = 4159799) B4159799
theorem B4157675 : Blo 1847625 4157675 := bstep (se 1 (by rfl) ⟨3118256, by rfl⟩ : syracuseStep 4157675 = 6236513) B6236513
theorem B12652787 : Blo 1847625 12652787 := bstep (se 1 (by rfl) ⟨9489590, by rfl⟩ : syracuseStep 12652787 = 18979181) B18979181
theorem B9359711 : Blo 1847625 9359711 := bstep (se 1 (by rfl) ⟨7019783, by rfl⟩ : syracuseStep 9359711 = 14039567) B14039567
theorem B1847711 : Blo 1847625 1847711 := bstep (se 1 (by rfl) ⟨1385783, by rfl⟩ : syracuseStep 1847711 = 2771567) B2771567
theorem B1847775 : Blo 1847625 1847775 := bstep (se 1 (by rfl) ⟨1385831, by rfl⟩ : syracuseStep 1847775 = 2771663) B2771663
theorem B1847999 : Blo 1847625 1847999 := bstep (se 1 (by rfl) ⟨1385999, by rfl⟩ : syracuseStep 1847999 = 2771999) B2771999
theorem B1848319 : Blo 1847625 1848319 := bstep (se 1 (by rfl) ⟨1386239, by rfl⟩ : syracuseStep 1848319 = 2772479) B2772479
theorem B23688287 : Blo 1847625 23688287 := bstep (se 1 (by rfl) ⟨17766215, by rfl⟩ : syracuseStep 23688287 = 35532431) B35532431
theorem B4158575 : Blo 1847625 4158575 := bstep (se 1 (by rfl) ⟨3118931, by rfl⟩ : syracuseStep 4158575 = 6237863) B6237863
theorem B2774207 : Blo 1847625 2774207 := bstep (se 1 (by rfl) ⟨2080655, by rfl⟩ : syracuseStep 2774207 = 4161311) B4161311
theorem B2774351 : Blo 1847625 2774351 := bstep (se 1 (by rfl) ⟨2080763, by rfl⟩ : syracuseStep 2774351 = 4161527) B4161527
theorem B4158953 : Blo 1847625 4158953 := bstep (se 2 (by rfl) ⟨1559607, by rfl⟩ : syracuseStep 4158953 = 3119215) B3119215
theorem B4159151 : Blo 1847625 4159151 := bstep (se 1 (by rfl) ⟨3119363, by rfl⟩ : syracuseStep 4159151 = 6238727) B6238727
theorem B37017283 : Blo 1847625 37017283 := bstep (se 1 (by rfl) ⟨27762962, by rfl⟩ : syracuseStep 37017283 = 55525925) B55525925
theorem B1849455 : Blo 1847625 1849455 := bstep (se 1 (by rfl) ⟨1387091, by rfl⟩ : syracuseStep 1849455 = 2774183) B2774183
theorem B1849583 : Blo 1847625 1849583 := bstep (se 1 (by rfl) ⟨1387187, by rfl⟩ : syracuseStep 1849583 = 2774375) B2774375
theorem B4159979 : Blo 1847625 4159979 := bstep (se 1 (by rfl) ⟨3119984, by rfl⟩ : syracuseStep 4159979 = 6239969) B6239969
theorem B10525463 : Blo 1847625 10525463 := bstep (se 1 (by rfl) ⟨7894097, by rfl⟩ : syracuseStep 10525463 = 15788195) B15788195
theorem B17103707 : Blo 1847625 17103707 := bstep (se 1 (by rfl) ⟨12827780, by rfl⟩ : syracuseStep 17103707 = 25655561) B25655561
theorem B23681929 : Blo 1847625 23681929 := bstep (se 2 (by rfl) ⟨8880723, by rfl⟩ : syracuseStep 23681929 = 17761447) B17761447
theorem B91168199 : Blo 1847625 91168199 := bstep (se 1 (by rfl) ⟨68376149, by rfl⟩ : syracuseStep 91168199 = 136752299) B136752299
theorem B4161023 : Blo 1847625 4161023 := bstep (se 1 (by rfl) ⟨3120767, by rfl⟩ : syracuseStep 4161023 = 6241535) B6241535
theorem B4161095 : Blo 1847625 4161095 := bstep (se 1 (by rfl) ⟨3120821, by rfl⟩ : syracuseStep 4161095 = 6241643) B6241643
theorem B18964151 : Blo 1847625 18964151 := bstep (se 1 (by rfl) ⟨14223113, by rfl⟩ : syracuseStep 18964151 = 28446227) B28446227
theorem B15793967 : Blo 1847625 15793967 := bstep (se 1 (by rfl) ⟨11845475, by rfl⟩ : syracuseStep 15793967 = 23690951) B23690951
theorem B96026795 : Blo 1847625 96026795 := bstep (se 1 (by rfl) ⟨72020096, by rfl⟩ : syracuseStep 96026795 = 144040193) B144040193
theorem B3949415 : Blo 1847625 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B4441247 : Blo 1847625 4441247 := bstep (se 1 (by rfl) ⟨3330935, by rfl⟩ : syracuseStep 4441247 = 6661871) B6661871
theorem B60778799 : Blo 1847625 60778799 := bstep (se 1 (by rfl) ⟨45584099, by rfl⟩ : syracuseStep 60778799 = 91168199) B91168199
theorem B8882569 : Blo 1847625 8882569 := bstep (se 2 (by rfl) ⟨3330963, by rfl⟩ : syracuseStep 8882569 = 6661927) B6661927
theorem B12642767 : Blo 1847625 12642767 := bstep (se 1 (by rfl) ⟨9482075, by rfl⟩ : syracuseStep 12642767 = 18964151) B18964151
theorem B10529311 : Blo 1847625 10529311 := bstep (se 1 (by rfl) ⟨7896983, by rfl⟩ : syracuseStep 10529311 = 15793967) B15793967
theorem B15198911 : Blo 1847625 15198911 := bstep (se 1 (by rfl) ⟨11399183, by rfl⟩ : syracuseStep 15198911 = 22798367) B22798367
theorem B6236891 : Blo 1847625 6236891 := bstep (se 1 (by rfl) ⟨4677668, by rfl⟩ : syracuseStep 6236891 = 9355337) B9355337
theorem B2771783 : Blo 1847625 2771783 := bstep (se 1 (by rfl) ⟨2078837, by rfl⟩ : syracuseStep 2771783 = 4157675) B4157675
theorem B11840863 : Blo 1847625 11840863 := bstep (se 1 (by rfl) ⟨8880647, by rfl⟩ : syracuseStep 11840863 = 17761295) B17761295
theorem B2772383 : Blo 1847625 2772383 := bstep (se 1 (by rfl) ⟨2079287, by rfl⟩ : syracuseStep 2772383 = 4158575) B4158575
theorem B3509801 : Blo 1847625 3509801 := bstep (se 2 (by rfl) ⟨1316175, by rfl⟩ : syracuseStep 3509801 = 2632351) B2632351
theorem B2772635 : Blo 1847625 2772635 := bstep (se 1 (by rfl) ⟨2079476, by rfl⟩ : syracuseStep 2772635 = 4158953) B4158953
theorem B2772767 : Blo 1847625 2772767 := bstep (se 1 (by rfl) ⟨2079575, by rfl⟩ : syracuseStep 2772767 = 4159151) B4159151
theorem B31575905 : Blo 1847625 31575905 := bstep (se 2 (by rfl) ⟨11840964, by rfl⟩ : syracuseStep 31575905 = 23681929) B23681929
theorem B34205671 : Blo 1847625 34205671 := bstep (se 1 (by rfl) ⟨25654253, by rfl⟩ : syracuseStep 34205671 = 51308507) B51308507
theorem B6238187 : Blo 1847625 6238187 := bstep (se 1 (by rfl) ⟨4678640, by rfl⟩ : syracuseStep 6238187 = 9357281) B9357281
theorem B51294305 : Blo 1847625 51294305 := bstep (se 2 (by rfl) ⟨19235364, by rfl⟩ : syracuseStep 51294305 = 38470729) B38470729
theorem B2773319 : Blo 1847625 2773319 := bstep (se 1 (by rfl) ⟨2079989, by rfl⟩ : syracuseStep 2773319 = 4159979) B4159979
theorem B7016975 : Blo 1847625 7016975 := bstep (se 1 (by rfl) ⟨5262731, by rfl⟩ : syracuseStep 7016975 = 10525463) B10525463
theorem B1847899 : Blo 1847625 1847899 := bstep (se 1 (by rfl) ⟨1385924, by rfl⟩ : syracuseStep 1847899 = 2771849) B2771849
theorem B2774015 : Blo 1847625 2774015 := bstep (se 1 (by rfl) ⟨2080511, by rfl⟩ : syracuseStep 2774015 = 4161023) B4161023
theorem B2774063 : Blo 1847625 2774063 := bstep (se 1 (by rfl) ⟨2080547, by rfl⟩ : syracuseStep 2774063 = 4161095) B4161095
theorem B2774399 : Blo 1847625 2774399 := bstep (se 1 (by rfl) ⟨2080799, by rfl⟩ : syracuseStep 2774399 = 4161599) B4161599
theorem B1848799 : Blo 1847625 1848799 := bstep (se 1 (by rfl) ⟨1386599, by rfl⟩ : syracuseStep 1848799 = 2773199) B2773199
theorem B8435191 : Blo 1847625 8435191 := bstep (se 1 (by rfl) ⟨6326393, by rfl⟩ : syracuseStep 8435191 = 12652787) B12652787
theorem B6239807 : Blo 1847625 6239807 := bstep (se 1 (by rfl) ⟨4679855, by rfl⟩ : syracuseStep 6239807 = 9359711) B9359711
theorem B15792191 : Blo 1847625 15792191 := bstep (se 1 (by rfl) ⟨11844143, by rfl⟩ : syracuseStep 15792191 = 23688287) B23688287
theorem B3119195 : Blo 1847625 3119195 := bstep (se 1 (by rfl) ⟨2339396, by rfl⟩ : syracuseStep 3119195 = 4678793) B4678793
theorem B1849471 : Blo 1847625 1849471 := bstep (se 1 (by rfl) ⟨1387103, by rfl⟩ : syracuseStep 1849471 = 2774207) B2774207
theorem B1849567 : Blo 1847625 1849567 := bstep (se 1 (by rfl) ⟨1387175, by rfl⟩ : syracuseStep 1849567 = 2774351) B2774351
theorem B4217449 : Blo 1847625 4217449 := bstep (se 2 (by rfl) ⟨1581543, by rfl⟩ : syracuseStep 4217449 = 3163087) B3163087
theorem B5266559 : Blo 1847625 5266559 := bstep (se 1 (by rfl) ⟨3949919, by rfl⟩ : syracuseStep 5266559 = 7899839) B7899839
theorem B10525895 : Blo 1847625 10525895 := bstep (se 1 (by rfl) ⟨7894421, by rfl⟩ : syracuseStep 10525895 = 15788843) B15788843
theorem B25287889 : Blo 1847625 25287889 := bstep (se 2 (by rfl) ⟨9482958, by rfl⟩ : syracuseStep 25287889 = 18965917) B18965917
theorem B11402471 : Blo 1847625 11402471 := bstep (se 1 (by rfl) ⟨8551853, by rfl⟩ : syracuseStep 11402471 = 17103707) B17103707
theorem B3120383 : Blo 1847625 3120383 := bstep (se 1 (by rfl) ⟨2340287, by rfl⟩ : syracuseStep 3120383 = 4680575) B4680575
theorem B4439593 : Blo 1847625 4439593 := bstep (se 2 (by rfl) ⟨1664847, by rfl⟩ : syracuseStep 4439593 = 3329695) B3329695
theorem B49356377 : Blo 1847625 49356377 := bstep (se 2 (by rfl) ⟨18508641, by rfl⟩ : syracuseStep 49356377 = 37017283) B37017283
theorem B4677983 : Blo 1847625 4677983 := bstep (se 1 (by rfl) ⟨3508487, by rfl⟩ : syracuseStep 4677983 = 7016975) B7016975
theorem B10528127 : Blo 1847625 10528127 := bstep (se 1 (by rfl) ⟨7896095, by rfl⟩ : syracuseStep 10528127 = 15792191) B15792191
theorem B40519199 : Blo 1847625 40519199 := bstep (se 1 (by rfl) ⟨30389399, by rfl⟩ : syracuseStep 40519199 = 60778799) B60778799
theorem B15787817 : Blo 1847625 15787817 := bstep (se 2 (by rfl) ⟨5920431, by rfl⟩ : syracuseStep 15787817 = 11840863) B11840863
theorem B182430245 : Blo 1847625 182430245 := bstep (se 4 (by rfl) ⟨17102835, by rfl⟩ : syracuseStep 182430245 = 34205671) B34205671
theorem B34196203 : Blo 1847625 34196203 := bstep (se 1 (by rfl) ⟨25647152, by rfl⟩ : syracuseStep 34196203 = 51294305) B51294305
theorem B23677829 : Blo 1847625 23677829 := bstep (se 4 (by rfl) ⟨2219796, by rfl⟩ : syracuseStep 23677829 = 4439593) B4439593
theorem B2632943 : Blo 1847625 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B2960831 : Blo 1847625 2960831 := bstep (se 1 (by rfl) ⟨2220623, by rfl⟩ : syracuseStep 2960831 = 4441247) B4441247
theorem B5623265 : Blo 1847625 5623265 := bstep (se 2 (by rfl) ⟨2108724, by rfl⟩ : syracuseStep 5623265 = 4217449) B4217449
theorem B4157927 : Blo 1847625 4157927 := bstep (se 1 (by rfl) ⟨3118445, by rfl⟩ : syracuseStep 4157927 = 6236891) B6236891
theorem B1847855 : Blo 1847625 1847855 := bstep (se 1 (by rfl) ⟨1385891, by rfl⟩ : syracuseStep 1847855 = 2771783) B2771783
theorem B3511039 : Blo 1847625 3511039 := bstep (se 1 (by rfl) ⟨2633279, by rfl⟩ : syracuseStep 3511039 = 5266559) B5266559
theorem B7017263 : Blo 1847625 7017263 := bstep (se 1 (by rfl) ⟨5262947, by rfl⟩ : syracuseStep 7017263 = 10525895) B10525895
theorem B1848255 : Blo 1847625 1848255 := bstep (se 1 (by rfl) ⟨1386191, by rfl⟩ : syracuseStep 1848255 = 2772383) B2772383
theorem B2339867 : Blo 1847625 2339867 := bstep (se 1 (by rfl) ⟨1754900, by rfl⟩ : syracuseStep 2339867 = 3509801) B3509801
theorem B32904251 : Blo 1847625 32904251 := bstep (se 1 (by rfl) ⟨24678188, by rfl⟩ : syracuseStep 32904251 = 49356377) B49356377
theorem B1848423 : Blo 1847625 1848423 := bstep (se 1 (by rfl) ⟨1386317, by rfl⟩ : syracuseStep 1848423 = 2772635) B2772635
theorem B1848511 : Blo 1847625 1848511 := bstep (se 1 (by rfl) ⟨1386383, by rfl⟩ : syracuseStep 1848511 = 2772767) B2772767
theorem B21050603 : Blo 1847625 21050603 := bstep (se 1 (by rfl) ⟨15787952, by rfl⟩ : syracuseStep 21050603 = 31575905) B31575905
theorem B4158791 : Blo 1847625 4158791 := bstep (se 1 (by rfl) ⟨3119093, by rfl⟩ : syracuseStep 4158791 = 6238187) B6238187
theorem B64017863 : Blo 1847625 64017863 := bstep (se 1 (by rfl) ⟨48013397, by rfl⟩ : syracuseStep 64017863 = 96026795) B96026795
theorem B1848879 : Blo 1847625 1848879 := bstep (se 1 (by rfl) ⟨1386659, by rfl⟩ : syracuseStep 1848879 = 2773319) B2773319
theorem B11843425 : Blo 1847625 11843425 := bstep (se 2 (by rfl) ⟨4441284, by rfl⟩ : syracuseStep 11843425 = 8882569) B8882569
theorem B1849343 : Blo 1847625 1849343 := bstep (se 1 (by rfl) ⟨1387007, by rfl⟩ : syracuseStep 1849343 = 2774015) B2774015
theorem B1849375 : Blo 1847625 1849375 := bstep (se 1 (by rfl) ⟨1387031, by rfl⟩ : syracuseStep 1849375 = 2774063) B2774063
theorem B14039081 : Blo 1847625 14039081 := bstep (se 2 (by rfl) ⟨5264655, by rfl⟩ : syracuseStep 14039081 = 10529311) B10529311
theorem B1849599 : Blo 1847625 1849599 := bstep (se 1 (by rfl) ⟨1387199, by rfl⟩ : syracuseStep 1849599 = 2774399) B2774399
theorem B4159871 : Blo 1847625 4159871 := bstep (se 1 (by rfl) ⟨3119903, by rfl⟩ : syracuseStep 4159871 = 6239807) B6239807
theorem B2079463 : Blo 1847625 2079463 := bstep (se 1 (by rfl) ⟨1559597, by rfl⟩ : syracuseStep 2079463 = 3119195) B3119195
theorem B33717185 : Blo 1847625 33717185 := bstep (se 2 (by rfl) ⟨12643944, by rfl⟩ : syracuseStep 33717185 = 25287889) B25287889
theorem B8428511 : Blo 1847625 8428511 := bstep (se 1 (by rfl) ⟨6321383, by rfl⟩ : syracuseStep 8428511 = 12642767) B12642767
theorem B10132607 : Blo 1847625 10132607 := bstep (se 1 (by rfl) ⟨7599455, by rfl⟩ : syracuseStep 10132607 = 15198911) B15198911
theorem B11246921 : Blo 1847625 11246921 := bstep (se 2 (by rfl) ⟨4217595, by rfl⟩ : syracuseStep 11246921 = 8435191) B8435191
theorem B7601647 : Blo 1847625 7601647 := bstep (se 1 (by rfl) ⟨5701235, by rfl⟩ : syracuseStep 7601647 = 11402471) B11402471
theorem B2080255 : Blo 1847625 2080255 := bstep (se 1 (by rfl) ⟨1560191, by rfl⟩ : syracuseStep 2080255 = 3120383) B3120383
theorem B4678175 : Blo 1847625 4678175 := bstep (se 1 (by rfl) ⟨3508631, by rfl⟩ : syracuseStep 4678175 = 7017263) B7017263
theorem B7021181 : Blo 1847625 7021181 := bstep (se 3 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 7021181 = 2632943) B2632943
theorem B14033735 : Blo 1847625 14033735 := bstep (se 1 (by rfl) ⟨10525301, by rfl⟩ : syracuseStep 14033735 = 21050603) B21050603
theorem B10135529 : Blo 1847625 10135529 := bstep (se 2 (by rfl) ⟨3800823, by rfl⟩ : syracuseStep 10135529 = 7601647) B7601647
theorem B7497947 : Blo 1847625 7497947 := bstep (se 1 (by rfl) ⟨5623460, by rfl⟩ : syracuseStep 7497947 = 11246921) B11246921
theorem B2771951 : Blo 1847625 2771951 := bstep (se 1 (by rfl) ⟨2078963, by rfl⟩ : syracuseStep 2771951 = 4157927) B4157927
theorem B2772527 : Blo 1847625 2772527 := bstep (se 1 (by rfl) ⟨2079395, by rfl⟩ : syracuseStep 2772527 = 4158791) B4158791
theorem B2772617 : Blo 1847625 2772617 := bstep (se 2 (by rfl) ⟨1039731, by rfl⟩ : syracuseStep 2772617 = 2079463) B2079463
theorem B4681385 : Blo 1847625 4681385 := bstep (se 2 (by rfl) ⟨1755519, by rfl⟩ : syracuseStep 4681385 = 3511039) B3511039
theorem B27012799 : Blo 1847625 27012799 := bstep (se 1 (by rfl) ⟨20259599, by rfl⟩ : syracuseStep 27012799 = 40519199) B40519199
theorem B9359387 : Blo 1847625 9359387 := bstep (se 1 (by rfl) ⟨7019540, by rfl⟩ : syracuseStep 9359387 = 14039081) B14039081
theorem B2773247 : Blo 1847625 2773247 := bstep (se 1 (by rfl) ⟨2079935, by rfl⟩ : syracuseStep 2773247 = 4159871) B4159871
theorem B2773673 : Blo 1847625 2773673 := bstep (se 2 (by rfl) ⟨1040127, by rfl⟩ : syracuseStep 2773673 = 2080255) B2080255
theorem B6755071 : Blo 1847625 6755071 := bstep (se 1 (by rfl) ⟨5066303, by rfl⟩ : syracuseStep 6755071 = 10132607) B10132607
theorem B3748843 : Blo 1847625 3748843 := bstep (se 1 (by rfl) ⟨2811632, by rfl⟩ : syracuseStep 3748843 = 5623265) B5623265
theorem B15791233 : Blo 1847625 15791233 := bstep (se 2 (by rfl) ⟨5921712, by rfl⟩ : syracuseStep 15791233 = 11843425) B11843425
theorem B6239645 : Blo 1847625 6239645 := bstep (se 3 (by rfl) ⟨1169933, by rfl⟩ : syracuseStep 6239645 = 2339867) B2339867
theorem B3118655 : Blo 1847625 3118655 := bstep (se 1 (by rfl) ⟨2338991, by rfl⟩ : syracuseStep 3118655 = 4677983) B4677983
theorem B21936167 : Blo 1847625 21936167 := bstep (se 1 (by rfl) ⟨16452125, by rfl⟩ : syracuseStep 21936167 = 32904251) B32904251
theorem B7018751 : Blo 1847625 7018751 := bstep (se 1 (by rfl) ⟨5264063, by rfl⟩ : syracuseStep 7018751 = 10528127) B10528127
theorem B42678575 : Blo 1847625 42678575 := bstep (se 1 (by rfl) ⟨32008931, by rfl⟩ : syracuseStep 42678575 = 64017863) B64017863
theorem B45594937 : Blo 1847625 45594937 := bstep (se 2 (by rfl) ⟨17098101, by rfl⟩ : syracuseStep 45594937 = 34196203) B34196203
theorem B7895549 : Blo 1847625 7895549 := bstep (se 3 (by rfl) ⟨1480415, by rfl⟩ : syracuseStep 7895549 = 2960831) B2960831
theorem B10525211 : Blo 1847625 10525211 := bstep (se 1 (by rfl) ⟨7893908, by rfl⟩ : syracuseStep 10525211 = 15787817) B15787817
theorem B486480653 : Blo 1847625 486480653 := bstep (se 3 (by rfl) ⟨91215122, by rfl⟩ : syracuseStep 486480653 = 182430245) B182430245
theorem B15785219 : Blo 1847625 15785219 := bstep (se 1 (by rfl) ⟨11838914, by rfl⟩ : syracuseStep 15785219 = 23677829) B23677829
theorem B22478123 : Blo 1847625 22478123 := bstep (se 1 (by rfl) ⟨16858592, by rfl⟩ : syracuseStep 22478123 = 33717185) B33717185
theorem B5619007 : Blo 1847625 5619007 := bstep (se 1 (by rfl) ⟨4214255, by rfl⟩ : syracuseStep 5619007 = 8428511) B8428511
theorem B60793249 : Blo 1847625 60793249 := bstep (se 2 (by rfl) ⟨22797468, by rfl⟩ : syracuseStep 60793249 = 45594937) B45594937
theorem B9355823 : Blo 1847625 9355823 := bstep (se 1 (by rfl) ⟨7016867, by rfl⟩ : syracuseStep 9355823 = 14033735) B14033735
theorem B4998457 : Blo 1847625 4998457 := bstep (se 2 (by rfl) ⟨1874421, by rfl⟩ : syracuseStep 4998457 = 3748843) B3748843
theorem B14624111 : Blo 1847625 14624111 := bstep (se 1 (by rfl) ⟨10968083, by rfl⟩ : syracuseStep 14624111 = 21936167) B21936167
theorem B4679167 : Blo 1847625 4679167 := bstep (se 1 (by rfl) ⟨3509375, by rfl⟩ : syracuseStep 4679167 = 7018751) B7018751
theorem B21054977 : Blo 1847625 21054977 := bstep (se 2 (by rfl) ⟨7895616, by rfl⟩ : syracuseStep 21054977 = 15791233) B15791233
theorem B28452383 : Blo 1847625 28452383 := bstep (se 1 (by rfl) ⟨21339287, by rfl⟩ : syracuseStep 28452383 = 42678575) B42678575
theorem B14985415 : Blo 1847625 14985415 := bstep (se 1 (by rfl) ⟨11239061, by rfl⟩ : syracuseStep 14985415 = 22478123) B22478123
theorem B4680787 : Blo 1847625 4680787 := bstep (se 1 (by rfl) ⟨3510590, by rfl⟩ : syracuseStep 4680787 = 7021181) B7021181
theorem B9006761 : Blo 1847625 9006761 := bstep (se 2 (by rfl) ⟨3377535, by rfl⟩ : syracuseStep 9006761 = 6755071) B6755071
theorem B5263699 : Blo 1847625 5263699 := bstep (se 1 (by rfl) ⟨3947774, by rfl⟩ : syracuseStep 5263699 = 7895549) B7895549
theorem B7016807 : Blo 1847625 7016807 := bstep (se 1 (by rfl) ⟨5262605, by rfl⟩ : syracuseStep 7016807 = 10525211) B10525211
theorem B7492009 : Blo 1847625 7492009 := bstep (se 2 (by rfl) ⟨2809503, by rfl⟩ : syracuseStep 7492009 = 5619007) B5619007
theorem B1847967 : Blo 1847625 1847967 := bstep (se 1 (by rfl) ⟨1385975, by rfl⟩ : syracuseStep 1847967 = 2771951) B2771951
theorem B10523479 : Blo 1847625 10523479 := bstep (se 1 (by rfl) ⟨7892609, by rfl⟩ : syracuseStep 10523479 = 15785219) B15785219
theorem B36017065 : Blo 1847625 36017065 := bstep (se 2 (by rfl) ⟨13506399, by rfl⟩ : syracuseStep 36017065 = 27012799) B27012799
theorem B1848351 : Blo 1847625 1848351 := bstep (se 1 (by rfl) ⟨1386263, by rfl⟩ : syracuseStep 1848351 = 2772527) B2772527
theorem B1848411 : Blo 1847625 1848411 := bstep (se 1 (by rfl) ⟨1386308, by rfl⟩ : syracuseStep 1848411 = 2772617) B2772617
theorem B6239591 : Blo 1847625 6239591 := bstep (se 1 (by rfl) ⟨4679693, by rfl⟩ : syracuseStep 6239591 = 9359387) B9359387
theorem B1848831 : Blo 1847625 1848831 := bstep (se 1 (by rfl) ⟨1386623, by rfl⟩ : syracuseStep 1848831 = 2773247) B2773247
theorem B3118783 : Blo 1847625 3118783 := bstep (se 1 (by rfl) ⟨2339087, by rfl⟩ : syracuseStep 3118783 = 4678175) B4678175
theorem B1849115 : Blo 1847625 1849115 := bstep (se 1 (by rfl) ⟨1386836, by rfl⟩ : syracuseStep 1849115 = 2773673) B2773673
theorem B19994525 : Blo 1847625 19994525 := bstep (se 3 (by rfl) ⟨3748973, by rfl⟩ : syracuseStep 19994525 = 7497947) B7497947
theorem B4159763 : Blo 1847625 4159763 := bstep (se 1 (by rfl) ⟨3119822, by rfl⟩ : syracuseStep 4159763 = 6239645) B6239645
theorem B2079103 : Blo 1847625 2079103 := bstep (se 1 (by rfl) ⟨1559327, by rfl⟩ : syracuseStep 2079103 = 3118655) B3118655
theorem B6757019 : Blo 1847625 6757019 := bstep (se 1 (by rfl) ⟨5067764, by rfl⟩ : syracuseStep 6757019 = 10135529) B10135529
theorem B324320435 : Blo 1847625 324320435 := bstep (se 1 (by rfl) ⟨243240326, by rfl⟩ : syracuseStep 324320435 = 486480653) B486480653
theorem B3120923 : Blo 1847625 3120923 := bstep (se 1 (by rfl) ⟨2340692, by rfl⟩ : syracuseStep 3120923 = 4681385) B4681385
theorem B4677871 : Blo 1847625 4677871 := bstep (se 1 (by rfl) ⟨3508403, by rfl⟩ : syracuseStep 4677871 = 7016807) B7016807
theorem B19980553 : Blo 1847625 19980553 := bstep (se 2 (by rfl) ⟨7492707, by rfl⟩ : syracuseStep 19980553 = 14985415) B14985415
theorem B9749407 : Blo 1847625 9749407 := bstep (se 1 (by rfl) ⟨7312055, by rfl⟩ : syracuseStep 9749407 = 14624111) B14624111
theorem B13329683 : Blo 1847625 13329683 := bstep (se 1 (by rfl) ⟨9997262, by rfl⟩ : syracuseStep 13329683 = 19994525) B19994525
theorem B216213623 : Blo 1847625 216213623 := bstep (se 1 (by rfl) ⟨162160217, by rfl⟩ : syracuseStep 216213623 = 324320435) B324320435
theorem B6237215 : Blo 1847625 6237215 := bstep (se 1 (by rfl) ⟨4677911, by rfl⟩ : syracuseStep 6237215 = 9355823) B9355823
theorem B2772137 : Blo 1847625 2772137 := bstep (se 2 (by rfl) ⟨1039551, by rfl⟩ : syracuseStep 2772137 = 2079103) B2079103
theorem B9989345 : Blo 1847625 9989345 := bstep (se 2 (by rfl) ⟨3746004, by rfl⟩ : syracuseStep 9989345 = 7492009) B7492009
theorem B14036651 : Blo 1847625 14036651 := bstep (se 1 (by rfl) ⟨10527488, by rfl⟩ : syracuseStep 14036651 = 21054977) B21054977
theorem B18968255 : Blo 1847625 18968255 := bstep (se 1 (by rfl) ⟨14226191, by rfl⟩ : syracuseStep 18968255 = 28452383) B28452383
theorem B2773175 : Blo 1847625 2773175 := bstep (se 1 (by rfl) ⟨2079881, by rfl⟩ : syracuseStep 2773175 = 4159763) B4159763
theorem B6664609 : Blo 1847625 6664609 := bstep (se 2 (by rfl) ⟨2499228, by rfl⟩ : syracuseStep 6664609 = 4998457) B4998457
theorem B6238889 : Blo 1847625 6238889 := bstep (se 2 (by rfl) ⟨2339583, by rfl⟩ : syracuseStep 6238889 = 4679167) B4679167
theorem B192091013 : Blo 1847625 192091013 := bstep (se 4 (by rfl) ⟨18008532, by rfl⟩ : syracuseStep 192091013 = 36017065) B36017065
theorem B4158377 : Blo 1847625 4158377 := bstep (se 2 (by rfl) ⟨1559391, by rfl⟩ : syracuseStep 4158377 = 3118783) B3118783
theorem B7018265 : Blo 1847625 7018265 := bstep (se 2 (by rfl) ⟨2631849, by rfl⟩ : syracuseStep 7018265 = 5263699) B5263699
theorem B81057665 : Blo 1847625 81057665 := bstep (se 2 (by rfl) ⟨30396624, by rfl⟩ : syracuseStep 81057665 = 60793249) B60793249
theorem B4159727 : Blo 1847625 4159727 := bstep (se 1 (by rfl) ⟨3119795, by rfl⟩ : syracuseStep 4159727 = 6239591) B6239591
theorem B14031305 : Blo 1847625 14031305 := bstep (se 2 (by rfl) ⟨5261739, by rfl⟩ : syracuseStep 14031305 = 10523479) B10523479
theorem B6241049 : Blo 1847625 6241049 := bstep (se 2 (by rfl) ⟨2340393, by rfl⟩ : syracuseStep 6241049 = 4680787) B4680787
theorem B4504679 : Blo 1847625 4504679 := bstep (se 1 (by rfl) ⟨3378509, by rfl⟩ : syracuseStep 4504679 = 6757019) B6757019
theorem B6004507 : Blo 1847625 6004507 := bstep (se 1 (by rfl) ⟨4503380, by rfl⟩ : syracuseStep 6004507 = 9006761) B9006761
theorem B2080615 : Blo 1847625 2080615 := bstep (se 1 (by rfl) ⟨1560461, by rfl⟩ : syracuseStep 2080615 = 3120923) B3120923
theorem B26640737 : Blo 1847625 26640737 := bstep (se 2 (by rfl) ⟨9990276, by rfl⟩ : syracuseStep 26640737 = 19980553) B19980553
theorem B4678843 : Blo 1847625 4678843 := bstep (se 1 (by rfl) ⟨3509132, by rfl⟩ : syracuseStep 4678843 = 7018265) B7018265
theorem B8006009 : Blo 1847625 8006009 := bstep (se 2 (by rfl) ⟨3002253, by rfl⟩ : syracuseStep 8006009 = 6004507) B6004507
theorem B9357767 : Blo 1847625 9357767 := bstep (se 1 (by rfl) ⟨7018325, by rfl⟩ : syracuseStep 9357767 = 14036651) B14036651
theorem B6237161 : Blo 1847625 6237161 := bstep (se 2 (by rfl) ⟨2338935, by rfl⟩ : syracuseStep 6237161 = 4677871) B4677871
theorem B128060675 : Blo 1847625 128060675 := bstep (se 1 (by rfl) ⟨96045506, by rfl⟩ : syracuseStep 128060675 = 192091013) B192091013
theorem B2772251 : Blo 1847625 2772251 := bstep (se 1 (by rfl) ⟨2079188, by rfl⟩ : syracuseStep 2772251 = 4158377) B4158377
theorem B54038443 : Blo 1847625 54038443 := bstep (se 1 (by rfl) ⟨40528832, by rfl⟩ : syracuseStep 54038443 = 81057665) B81057665
theorem B144142415 : Blo 1847625 144142415 := bstep (se 1 (by rfl) ⟨108106811, by rfl⟩ : syracuseStep 144142415 = 216213623) B216213623
theorem B2773151 : Blo 1847625 2773151 := bstep (se 1 (by rfl) ⟨2079863, by rfl⟩ : syracuseStep 2773151 = 4159727) B4159727
theorem B4158143 : Blo 1847625 4158143 := bstep (se 1 (by rfl) ⟨3118607, by rfl⟩ : syracuseStep 4158143 = 6237215) B6237215
theorem B3003119 : Blo 1847625 3003119 := bstep (se 1 (by rfl) ⟨2252339, by rfl⟩ : syracuseStep 3003119 = 4504679) B4504679
theorem B1848091 : Blo 1847625 1848091 := bstep (se 1 (by rfl) ⟨1386068, by rfl⟩ : syracuseStep 1848091 = 2772137) B2772137
theorem B12645503 : Blo 1847625 12645503 := bstep (se 1 (by rfl) ⟨9484127, by rfl⟩ : syracuseStep 12645503 = 18968255) B18968255
theorem B2774153 : Blo 1847625 2774153 := bstep (se 2 (by rfl) ⟨1040307, by rfl⟩ : syracuseStep 2774153 = 2080615) B2080615
theorem B1848783 : Blo 1847625 1848783 := bstep (se 1 (by rfl) ⟨1386587, by rfl⟩ : syracuseStep 1848783 = 2773175) B2773175
theorem B4159259 : Blo 1847625 4159259 := bstep (se 1 (by rfl) ⟨3119444, by rfl⟩ : syracuseStep 4159259 = 6238889) B6238889
theorem B26638253 : Blo 1847625 26638253 := bstep (se 3 (by rfl) ⟨4994672, by rfl⟩ : syracuseStep 26638253 = 9989345) B9989345
theorem B8886455 : Blo 1847625 8886455 := bstep (se 1 (by rfl) ⟨6664841, by rfl⟩ : syracuseStep 8886455 = 13329683) B13329683
theorem B12999209 : Blo 1847625 12999209 := bstep (se 2 (by rfl) ⟨4874703, by rfl⟩ : syracuseStep 12999209 = 9749407) B9749407
theorem B9354203 : Blo 1847625 9354203 := bstep (se 1 (by rfl) ⟨7015652, by rfl⟩ : syracuseStep 9354203 = 14031305) B14031305
theorem B4160699 : Blo 1847625 4160699 := bstep (se 1 (by rfl) ⟨3120524, by rfl⟩ : syracuseStep 4160699 = 6241049) B6241049
theorem B35544581 : Blo 1847625 35544581 := bstep (se 4 (by rfl) ⟨3332304, by rfl⟩ : syracuseStep 35544581 = 6664609) B6664609
theorem B17760491 : Blo 1847625 17760491 := bstep (se 1 (by rfl) ⟨13320368, by rfl⟩ : syracuseStep 17760491 = 26640737) B26640737
theorem B8430335 : Blo 1847625 8430335 := bstep (se 1 (by rfl) ⟨6322751, by rfl⟩ : syracuseStep 8430335 = 12645503) B12645503
theorem B5924303 : Blo 1847625 5924303 := bstep (se 1 (by rfl) ⟨4443227, by rfl⟩ : syracuseStep 5924303 = 8886455) B8886455
theorem B6236135 : Blo 1847625 6236135 := bstep (se 1 (by rfl) ⟨4677101, by rfl⟩ : syracuseStep 6236135 = 9354203) B9354203
theorem B72051257 : Blo 1847625 72051257 := bstep (se 2 (by rfl) ⟨27019221, by rfl⟩ : syracuseStep 72051257 = 54038443) B54038443
theorem B96094943 : Blo 1847625 96094943 := bstep (se 1 (by rfl) ⟨72071207, by rfl⟩ : syracuseStep 96094943 = 144142415) B144142415
theorem B2772095 : Blo 1847625 2772095 := bstep (se 1 (by rfl) ⟨2079071, by rfl⟩ : syracuseStep 2772095 = 4158143) B4158143
theorem B2002079 : Blo 1847625 2002079 := bstep (se 1 (by rfl) ⟨1501559, by rfl⟩ : syracuseStep 2002079 = 3003119) B3003119
theorem B2772839 : Blo 1847625 2772839 := bstep (se 1 (by rfl) ⟨2079629, by rfl⟩ : syracuseStep 2772839 = 4159259) B4159259
theorem B85397429 : Blo 1847625 85397429 := bstep (se 5 (by rfl) ⟨4003004, by rfl⟩ : syracuseStep 85397429 = 8006009) B8006009
theorem B34664557 : Blo 1847625 34664557 := bstep (se 3 (by rfl) ⟨6499604, by rfl⟩ : syracuseStep 34664557 = 12999209) B12999209
theorem B6238457 : Blo 1847625 6238457 := bstep (se 2 (by rfl) ⟨2339421, by rfl⟩ : syracuseStep 6238457 = 4678843) B4678843
theorem B6238511 : Blo 1847625 6238511 := bstep (se 1 (by rfl) ⟨4678883, by rfl⟩ : syracuseStep 6238511 = 9357767) B9357767
theorem B4158107 : Blo 1847625 4158107 := bstep (se 1 (by rfl) ⟨3118580, by rfl⟩ : syracuseStep 4158107 = 6237161) B6237161
theorem B2773799 : Blo 1847625 2773799 := bstep (se 1 (by rfl) ⟨2080349, by rfl⟩ : syracuseStep 2773799 = 4160699) B4160699
theorem B85373783 : Blo 1847625 85373783 := bstep (se 1 (by rfl) ⟨64030337, by rfl⟩ : syracuseStep 85373783 = 128060675) B128060675
theorem B1848167 : Blo 1847625 1848167 := bstep (se 1 (by rfl) ⟨1386125, by rfl⟩ : syracuseStep 1848167 = 2772251) B2772251
theorem B23696387 : Blo 1847625 23696387 := bstep (se 1 (by rfl) ⟨17772290, by rfl⟩ : syracuseStep 23696387 = 35544581) B35544581
theorem B1848767 : Blo 1847625 1848767 := bstep (se 1 (by rfl) ⟨1386575, by rfl⟩ : syracuseStep 1848767 = 2773151) B2773151
theorem B1849435 : Blo 1847625 1849435 := bstep (se 1 (by rfl) ⟨1387076, by rfl⟩ : syracuseStep 1849435 = 2774153) B2774153
theorem B17758835 : Blo 1847625 17758835 := bstep (se 1 (by rfl) ⟨13319126, by rfl⟩ : syracuseStep 17758835 = 26638253) B26638253
theorem B46219409 : Blo 1847625 46219409 := bstep (se 2 (by rfl) ⟨17332278, by rfl⟩ : syracuseStep 46219409 = 34664557) B34664557
theorem B5620223 : Blo 1847625 5620223 := bstep (se 1 (by rfl) ⟨4215167, by rfl⟩ : syracuseStep 5620223 = 8430335) B8430335
theorem B3949535 : Blo 1847625 3949535 := bstep (se 1 (by rfl) ⟨2962151, by rfl⟩ : syracuseStep 3949535 = 5924303) B5924303
theorem B11839223 : Blo 1847625 11839223 := bstep (se 1 (by rfl) ⟨8879417, by rfl⟩ : syracuseStep 11839223 = 17758835) B17758835
theorem B64063295 : Blo 1847625 64063295 := bstep (se 1 (by rfl) ⟨48047471, by rfl⟩ : syracuseStep 64063295 = 96094943) B96094943
theorem B11840327 : Blo 1847625 11840327 := bstep (se 1 (by rfl) ⟨8880245, by rfl⟩ : syracuseStep 11840327 = 17760491) B17760491
theorem B2772071 : Blo 1847625 2772071 := bstep (se 1 (by rfl) ⟨2079053, by rfl⟩ : syracuseStep 2772071 = 4158107) B4158107
theorem B15797591 : Blo 1847625 15797591 := bstep (se 1 (by rfl) ⟨11848193, by rfl⟩ : syracuseStep 15797591 = 23696387) B23696387
theorem B4157423 : Blo 1847625 4157423 := bstep (se 1 (by rfl) ⟨3118067, by rfl⟩ : syracuseStep 4157423 = 6236135) B6236135
theorem B48034171 : Blo 1847625 48034171 := bstep (se 1 (by rfl) ⟨36025628, by rfl⟩ : syracuseStep 48034171 = 72051257) B72051257
theorem B1848063 : Blo 1847625 1848063 := bstep (se 1 (by rfl) ⟨1386047, by rfl⟩ : syracuseStep 1848063 = 2772095) B2772095
theorem B1848559 : Blo 1847625 1848559 := bstep (se 1 (by rfl) ⟨1386419, by rfl⟩ : syracuseStep 1848559 = 2772839) B2772839
theorem B56931619 : Blo 1847625 56931619 := bstep (se 1 (by rfl) ⟨42698714, by rfl⟩ : syracuseStep 56931619 = 85397429) B85397429
theorem B4158971 : Blo 1847625 4158971 := bstep (se 1 (by rfl) ⟨3119228, by rfl⟩ : syracuseStep 4158971 = 6238457) B6238457
theorem B4159007 : Blo 1847625 4159007 := bstep (se 1 (by rfl) ⟨3119255, by rfl⟩ : syracuseStep 4159007 = 6238511) B6238511
theorem B5338877 : Blo 1847625 5338877 := bstep (se 3 (by rfl) ⟨1001039, by rfl⟩ : syracuseStep 5338877 = 2002079) B2002079
theorem B1849199 : Blo 1847625 1849199 := bstep (se 1 (by rfl) ⟨1386899, by rfl⟩ : syracuseStep 1849199 = 2773799) B2773799
theorem B56915855 : Blo 1847625 56915855 := bstep (se 1 (by rfl) ⟨42686891, by rfl⟩ : syracuseStep 56915855 = 85373783) B85373783
theorem B64045561 : Blo 1847625 64045561 := bstep (se 2 (by rfl) ⟨24017085, by rfl⟩ : syracuseStep 64045561 = 48034171) B48034171
theorem B75908825 : Blo 1847625 75908825 := bstep (se 2 (by rfl) ⟨28465809, by rfl⟩ : syracuseStep 75908825 = 56931619) B56931619
theorem B2771615 : Blo 1847625 2771615 := bstep (se 1 (by rfl) ⟨2078711, by rfl⟩ : syracuseStep 2771615 = 4157423) B4157423
theorem B30812939 : Blo 1847625 30812939 := bstep (se 1 (by rfl) ⟨23109704, by rfl⟩ : syracuseStep 30812939 = 46219409) B46219409
theorem B2633023 : Blo 1847625 2633023 := bstep (se 1 (by rfl) ⟨1974767, by rfl⟩ : syracuseStep 2633023 = 3949535) B3949535
theorem B2772647 : Blo 1847625 2772647 := bstep (se 1 (by rfl) ⟨2079485, by rfl⟩ : syracuseStep 2772647 = 4158971) B4158971
theorem B2772671 : Blo 1847625 2772671 := bstep (se 1 (by rfl) ⟨2079503, by rfl⟩ : syracuseStep 2772671 = 4159007) B4159007
theorem B7892815 : Blo 1847625 7892815 := bstep (se 1 (by rfl) ⟨5919611, by rfl⟩ : syracuseStep 7892815 = 11839223) B11839223
theorem B42708863 : Blo 1847625 42708863 := bstep (se 1 (by rfl) ⟨32031647, by rfl⟩ : syracuseStep 42708863 = 64063295) B64063295
theorem B14987261 : Blo 1847625 14987261 := bstep (se 3 (by rfl) ⟨2810111, by rfl⟩ : syracuseStep 14987261 = 5620223) B5620223
theorem B7893551 : Blo 1847625 7893551 := bstep (se 1 (by rfl) ⟨5920163, by rfl⟩ : syracuseStep 7893551 = 11840327) B11840327
theorem B1848047 : Blo 1847625 1848047 := bstep (se 1 (by rfl) ⟨1386035, by rfl⟩ : syracuseStep 1848047 = 2772071) B2772071
theorem B10531727 : Blo 1847625 10531727 := bstep (se 1 (by rfl) ⟨7898795, by rfl⟩ : syracuseStep 10531727 = 15797591) B15797591
theorem B37943903 : Blo 1847625 37943903 := bstep (se 1 (by rfl) ⟨28457927, by rfl⟩ : syracuseStep 37943903 = 56915855) B56915855
theorem B14237005 : Blo 1847625 14237005 := bstep (se 3 (by rfl) ⟨2669438, by rfl⟩ : syracuseStep 14237005 = 5338877) B5338877
theorem B7021151 : Blo 1847625 7021151 := bstep (se 1 (by rfl) ⟨5265863, by rfl⟩ : syracuseStep 7021151 = 10531727) B10531727
theorem B85394081 : Blo 1847625 85394081 := bstep (se 2 (by rfl) ⟨32022780, by rfl⟩ : syracuseStep 85394081 = 64045561) B64045561
theorem B18982673 : Blo 1847625 18982673 := bstep (se 2 (by rfl) ⟨7118502, by rfl⟩ : syracuseStep 18982673 = 14237005) B14237005
theorem B5262367 : Blo 1847625 5262367 := bstep (se 1 (by rfl) ⟨3946775, by rfl⟩ : syracuseStep 5262367 = 7893551) B7893551
theorem B50605883 : Blo 1847625 50605883 := bstep (se 1 (by rfl) ⟨37954412, by rfl⟩ : syracuseStep 50605883 = 75908825) B75908825
theorem B101183741 : Blo 1847625 101183741 := bstep (se 3 (by rfl) ⟨18971951, by rfl⟩ : syracuseStep 101183741 = 37943903) B37943903
theorem B3510697 : Blo 1847625 3510697 := bstep (se 2 (by rfl) ⟨1316511, by rfl⟩ : syracuseStep 3510697 = 2633023) B2633023
theorem B1847743 : Blo 1847625 1847743 := bstep (se 1 (by rfl) ⟨1385807, by rfl⟩ : syracuseStep 1847743 = 2771615) B2771615
theorem B20541959 : Blo 1847625 20541959 := bstep (se 1 (by rfl) ⟨15406469, by rfl⟩ : syracuseStep 20541959 = 30812939) B30812939
theorem B10523753 : Blo 1847625 10523753 := bstep (se 2 (by rfl) ⟨3946407, by rfl⟩ : syracuseStep 10523753 = 7892815) B7892815
theorem B1848431 : Blo 1847625 1848431 := bstep (se 1 (by rfl) ⟨1386323, by rfl⟩ : syracuseStep 1848431 = 2772647) B2772647
theorem B1848447 : Blo 1847625 1848447 := bstep (se 1 (by rfl) ⟨1386335, by rfl⟩ : syracuseStep 1848447 = 2772671) B2772671
theorem B28472575 : Blo 1847625 28472575 := bstep (se 1 (by rfl) ⟨21354431, by rfl⟩ : syracuseStep 28472575 = 42708863) B42708863
theorem B9991507 : Blo 1847625 9991507 := bstep (se 1 (by rfl) ⟨7493630, by rfl⟩ : syracuseStep 9991507 = 14987261) B14987261
theorem B37963433 : Blo 1847625 37963433 := bstep (se 2 (by rfl) ⟨14236287, by rfl⟩ : syracuseStep 37963433 = 28472575) B28472575
theorem B13322009 : Blo 1847625 13322009 := bstep (se 2 (by rfl) ⟨4995753, by rfl⟩ : syracuseStep 13322009 = 9991507) B9991507
theorem B33737255 : Blo 1847625 33737255 := bstep (se 1 (by rfl) ⟨25302941, by rfl⟩ : syracuseStep 33737255 = 50605883) B50605883
theorem B67455827 : Blo 1847625 67455827 := bstep (se 1 (by rfl) ⟨50591870, by rfl⟩ : syracuseStep 67455827 = 101183741) B101183741
theorem B4680767 : Blo 1847625 4680767 := bstep (se 1 (by rfl) ⟨3510575, by rfl⟩ : syracuseStep 4680767 = 7021151) B7021151
theorem B56929387 : Blo 1847625 56929387 := bstep (se 1 (by rfl) ⟨42697040, by rfl⟩ : syracuseStep 56929387 = 85394081) B85394081
theorem B4680929 : Blo 1847625 4680929 := bstep (se 2 (by rfl) ⟨1755348, by rfl⟩ : syracuseStep 4680929 = 3510697) B3510697
theorem B7015835 : Blo 1847625 7015835 := bstep (se 1 (by rfl) ⟨5261876, by rfl⟩ : syracuseStep 7015835 = 10523753) B10523753
theorem B7016489 : Blo 1847625 7016489 := bstep (se 2 (by rfl) ⟨2631183, by rfl⟩ : syracuseStep 7016489 = 5262367) B5262367
theorem B13694639 : Blo 1847625 13694639 := bstep (se 1 (by rfl) ⟨10270979, by rfl⟩ : syracuseStep 13694639 = 20541959) B20541959
theorem B12655115 : Blo 1847625 12655115 := bstep (se 1 (by rfl) ⟨9491336, by rfl⟩ : syracuseStep 12655115 = 18982673) B18982673
theorem B4677659 : Blo 1847625 4677659 := bstep (se 1 (by rfl) ⟨3508244, by rfl⟩ : syracuseStep 4677659 = 7016489) B7016489
theorem B8881339 : Blo 1847625 8881339 := bstep (se 1 (by rfl) ⟨6661004, by rfl⟩ : syracuseStep 8881339 = 13322009) B13322009
theorem B25308955 : Blo 1847625 25308955 := bstep (se 1 (by rfl) ⟨18981716, by rfl⟩ : syracuseStep 25308955 = 37963433) B37963433
theorem B22491503 : Blo 1847625 22491503 := bstep (se 1 (by rfl) ⟨16868627, by rfl⟩ : syracuseStep 22491503 = 33737255) B33737255
theorem B146076149 : Blo 1847625 146076149 := bstep (se 5 (by rfl) ⟨6847319, by rfl⟩ : syracuseStep 146076149 = 13694639) B13694639
theorem B44970551 : Blo 1847625 44970551 := bstep (se 1 (by rfl) ⟨33727913, by rfl⟩ : syracuseStep 44970551 = 67455827) B67455827
theorem B75905849 : Blo 1847625 75905849 := bstep (se 2 (by rfl) ⟨28464693, by rfl⟩ : syracuseStep 75905849 = 56929387) B56929387
theorem B8436743 : Blo 1847625 8436743 := bstep (se 1 (by rfl) ⟨6327557, by rfl⟩ : syracuseStep 8436743 = 12655115) B12655115
theorem B3120511 : Blo 1847625 3120511 := bstep (se 1 (by rfl) ⟨2340383, by rfl⟩ : syracuseStep 3120511 = 4680767) B4680767
theorem B3120619 : Blo 1847625 3120619 := bstep (se 1 (by rfl) ⟨2340464, by rfl⟩ : syracuseStep 3120619 = 4680929) B4680929
theorem B4677223 : Blo 1847625 4677223 := bstep (se 1 (by rfl) ⟨3507917, by rfl⟩ : syracuseStep 4677223 = 7015835) B7015835
theorem B134981093 : Blo 1847625 134981093 := bstep (se 4 (by rfl) ⟨12654477, by rfl⟩ : syracuseStep 134981093 = 25308955) B25308955
theorem B6236297 : Blo 1847625 6236297 := bstep (se 2 (by rfl) ⟨2338611, by rfl⟩ : syracuseStep 6236297 = 4677223) B4677223
theorem B14994335 : Blo 1847625 14994335 := bstep (se 1 (by rfl) ⟨11245751, by rfl⟩ : syracuseStep 14994335 = 22491503) B22491503
theorem B11841785 : Blo 1847625 11841785 := bstep (se 2 (by rfl) ⟨4440669, by rfl⟩ : syracuseStep 11841785 = 8881339) B8881339
theorem B5624495 : Blo 1847625 5624495 := bstep (se 1 (by rfl) ⟨4218371, by rfl⟩ : syracuseStep 5624495 = 8436743) B8436743
theorem B3118439 : Blo 1847625 3118439 := bstep (se 1 (by rfl) ⟨2338829, by rfl⟩ : syracuseStep 3118439 = 4677659) B4677659
theorem B29980367 : Blo 1847625 29980367 := bstep (se 1 (by rfl) ⟨22485275, by rfl⟩ : syracuseStep 29980367 = 44970551) B44970551
theorem B389536397 : Blo 1847625 389536397 := bstep (se 3 (by rfl) ⟨73038074, by rfl⟩ : syracuseStep 389536397 = 146076149) B146076149
theorem B4160681 : Blo 1847625 4160681 := bstep (se 2 (by rfl) ⟨1560255, by rfl⟩ : syracuseStep 4160681 = 3120511) B3120511
theorem B4160825 : Blo 1847625 4160825 := bstep (se 2 (by rfl) ⟨1560309, by rfl⟩ : syracuseStep 4160825 = 3120619) B3120619
theorem B202415597 : Blo 1847625 202415597 := bstep (se 3 (by rfl) ⟨37952924, by rfl⟩ : syracuseStep 202415597 = 75905849) B75905849
theorem B9996223 : Blo 1847625 9996223 := bstep (se 1 (by rfl) ⟨7497167, by rfl⟩ : syracuseStep 9996223 = 14994335) B14994335
theorem B4157531 : Blo 1847625 4157531 := bstep (se 1 (by rfl) ⟨3118148, by rfl⟩ : syracuseStep 4157531 = 6236297) B6236297
theorem B259690931 : Blo 1847625 259690931 := bstep (se 1 (by rfl) ⟨194768198, by rfl⟩ : syracuseStep 259690931 = 389536397) B389536397
theorem B2773787 : Blo 1847625 2773787 := bstep (se 1 (by rfl) ⟨2080340, by rfl⟩ : syracuseStep 2773787 = 4160681) B4160681
theorem B2773883 : Blo 1847625 2773883 := bstep (se 1 (by rfl) ⟨2080412, by rfl⟩ : syracuseStep 2773883 = 4160825) B4160825
theorem B134943731 : Blo 1847625 134943731 := bstep (se 1 (by rfl) ⟨101207798, by rfl⟩ : syracuseStep 134943731 = 202415597) B202415597
theorem B7894523 : Blo 1847625 7894523 := bstep (se 1 (by rfl) ⟨5920892, by rfl⟩ : syracuseStep 7894523 = 11841785) B11841785
theorem B3749663 : Blo 1847625 3749663 := bstep (se 1 (by rfl) ⟨2812247, by rfl⟩ : syracuseStep 3749663 = 5624495) B5624495
theorem B2078959 : Blo 1847625 2078959 := bstep (se 1 (by rfl) ⟨1559219, by rfl⟩ : syracuseStep 2078959 = 3118439) B3118439
theorem B89987395 : Blo 1847625 89987395 := bstep (se 1 (by rfl) ⟨67490546, by rfl⟩ : syracuseStep 89987395 = 134981093) B134981093
theorem B19986911 : Blo 1847625 19986911 := bstep (se 1 (by rfl) ⟨14990183, by rfl⟩ : syracuseStep 19986911 = 29980367) B29980367
theorem B2771687 : Blo 1847625 2771687 := bstep (se 1 (by rfl) ⟨2078765, by rfl⟩ : syracuseStep 2771687 = 4157531) B4157531
theorem B2771945 : Blo 1847625 2771945 := bstep (se 2 (by rfl) ⟨1039479, by rfl⟩ : syracuseStep 2771945 = 2078959) B2078959
theorem B119983193 : Blo 1847625 119983193 := bstep (se 2 (by rfl) ⟨44993697, by rfl⟩ : syracuseStep 119983193 = 89987395) B89987395
theorem B13324607 : Blo 1847625 13324607 := bstep (se 1 (by rfl) ⟨9993455, by rfl⟩ : syracuseStep 13324607 = 19986911) B19986911
theorem B9999101 : Blo 1847625 9999101 := bstep (se 3 (by rfl) ⟨1874831, by rfl⟩ : syracuseStep 9999101 = 3749663) B3749663
theorem B173127287 : Blo 1847625 173127287 := bstep (se 1 (by rfl) ⟨129845465, by rfl⟩ : syracuseStep 173127287 = 259690931) B259690931
theorem B1849191 : Blo 1847625 1849191 := bstep (se 1 (by rfl) ⟨1386893, by rfl⟩ : syracuseStep 1849191 = 2773787) B2773787
theorem B1849255 : Blo 1847625 1849255 := bstep (se 1 (by rfl) ⟨1386941, by rfl⟩ : syracuseStep 1849255 = 2773883) B2773883
theorem B89962487 : Blo 1847625 89962487 := bstep (se 1 (by rfl) ⟨67471865, by rfl⟩ : syracuseStep 89962487 = 134943731) B134943731
theorem B21052061 : Blo 1847625 21052061 := bstep (se 3 (by rfl) ⟨3947261, by rfl⟩ : syracuseStep 21052061 = 7894523) B7894523
theorem B13328297 : Blo 1847625 13328297 := bstep (se 2 (by rfl) ⟨4998111, by rfl⟩ : syracuseStep 13328297 = 9996223) B9996223
theorem B115418191 : Blo 1847625 115418191 := bstep (se 1 (by rfl) ⟨86563643, by rfl⟩ : syracuseStep 115418191 = 173127287) B173127287
theorem B59974991 : Blo 1847625 59974991 := bstep (se 1 (by rfl) ⟨44981243, by rfl⟩ : syracuseStep 59974991 = 89962487) B89962487
theorem B14034707 : Blo 1847625 14034707 := bstep (se 1 (by rfl) ⟨10526030, by rfl⟩ : syracuseStep 14034707 = 21052061) B21052061
theorem B79988795 : Blo 1847625 79988795 := bstep (se 1 (by rfl) ⟨59991596, by rfl⟩ : syracuseStep 79988795 = 119983193) B119983193
theorem B8883071 : Blo 1847625 8883071 := bstep (se 1 (by rfl) ⟨6662303, by rfl⟩ : syracuseStep 8883071 = 13324607) B13324607
theorem B1847791 : Blo 1847625 1847791 := bstep (se 1 (by rfl) ⟨1385843, by rfl⟩ : syracuseStep 1847791 = 2771687) B2771687
theorem B1847963 : Blo 1847625 1847963 := bstep (se 1 (by rfl) ⟨1385972, by rfl⟩ : syracuseStep 1847963 = 2771945) B2771945
theorem B8885531 : Blo 1847625 8885531 := bstep (se 1 (by rfl) ⟨6664148, by rfl⟩ : syracuseStep 8885531 = 13328297) B13328297
theorem B6666067 : Blo 1847625 6666067 := bstep (se 1 (by rfl) ⟨4999550, by rfl⟩ : syracuseStep 6666067 = 9999101) B9999101
theorem B5923687 : Blo 1847625 5923687 := bstep (se 1 (by rfl) ⟨4442765, by rfl⟩ : syracuseStep 5923687 = 8885531) B8885531
theorem B9356471 : Blo 1847625 9356471 := bstep (se 1 (by rfl) ⟨7017353, by rfl⟩ : syracuseStep 9356471 = 14034707) B14034707
theorem B53325863 : Blo 1847625 53325863 := bstep (se 1 (by rfl) ⟨39994397, by rfl⟩ : syracuseStep 53325863 = 79988795) B79988795
theorem B153890921 : Blo 1847625 153890921 := bstep (se 2 (by rfl) ⟨57709095, by rfl⟩ : syracuseStep 153890921 = 115418191) B115418191
theorem B39983327 : Blo 1847625 39983327 := bstep (se 1 (by rfl) ⟨29987495, by rfl⟩ : syracuseStep 39983327 = 59974991) B59974991
theorem B5922047 : Blo 1847625 5922047 := bstep (se 1 (by rfl) ⟨4441535, by rfl⟩ : syracuseStep 5922047 = 8883071) B8883071
theorem B8888089 : Blo 1847625 8888089 := bstep (se 2 (by rfl) ⟨3333033, by rfl⟩ : syracuseStep 8888089 = 6666067) B6666067
theorem B7898249 : Blo 1847625 7898249 := bstep (se 2 (by rfl) ⟨2961843, by rfl⟩ : syracuseStep 7898249 = 5923687) B5923687
theorem B6237647 : Blo 1847625 6237647 := bstep (se 1 (by rfl) ⟨4678235, by rfl⟩ : syracuseStep 6237647 = 9356471) B9356471
theorem B11850785 : Blo 1847625 11850785 := bstep (se 2 (by rfl) ⟨4444044, by rfl⟩ : syracuseStep 11850785 = 8888089) B8888089
theorem B35550575 : Blo 1847625 35550575 := bstep (se 1 (by rfl) ⟨26662931, by rfl⟩ : syracuseStep 35550575 = 53325863) B53325863
theorem B102593947 : Blo 1847625 102593947 := bstep (se 1 (by rfl) ⟨76945460, by rfl⟩ : syracuseStep 102593947 = 153890921) B153890921
theorem B26655551 : Blo 1847625 26655551 := bstep (se 1 (by rfl) ⟨19991663, by rfl⟩ : syracuseStep 26655551 = 39983327) B39983327
theorem B3948031 : Blo 1847625 3948031 := bstep (se 1 (by rfl) ⟨2961023, by rfl⟩ : syracuseStep 3948031 = 5922047) B5922047
theorem B23700383 : Blo 1847625 23700383 := bstep (se 1 (by rfl) ⟨17775287, by rfl⟩ : syracuseStep 23700383 = 35550575) B35550575
theorem B136791929 : Blo 1847625 136791929 := bstep (se 2 (by rfl) ⟨51296973, by rfl⟩ : syracuseStep 136791929 = 102593947) B102593947
theorem B17770367 : Blo 1847625 17770367 := bstep (se 1 (by rfl) ⟨13327775, by rfl⟩ : syracuseStep 17770367 = 26655551) B26655551
theorem B7900523 : Blo 1847625 7900523 := bstep (se 1 (by rfl) ⟨5925392, by rfl⟩ : syracuseStep 7900523 = 11850785) B11850785
theorem B5264041 : Blo 1847625 5264041 := bstep (se 2 (by rfl) ⟨1974015, by rfl⟩ : syracuseStep 5264041 = 3948031) B3948031
theorem B4158431 : Blo 1847625 4158431 := bstep (se 1 (by rfl) ⟨3118823, by rfl⟩ : syracuseStep 4158431 = 6237647) B6237647
theorem B5265499 : Blo 1847625 5265499 := bstep (se 1 (by rfl) ⟨3949124, by rfl⟩ : syracuseStep 5265499 = 7898249) B7898249
theorem B7020665 : Blo 1847625 7020665 := bstep (se 2 (by rfl) ⟨2632749, by rfl⟩ : syracuseStep 7020665 = 5265499) B5265499
theorem B11846911 : Blo 1847625 11846911 := bstep (se 1 (by rfl) ⟨8885183, by rfl⟩ : syracuseStep 11846911 = 17770367) B17770367
theorem B2772287 : Blo 1847625 2772287 := bstep (se 1 (by rfl) ⟨2079215, by rfl⟩ : syracuseStep 2772287 = 4158431) B4158431
theorem B364778477 : Blo 1847625 364778477 := bstep (se 3 (by rfl) ⟨68395964, by rfl⟩ : syracuseStep 364778477 = 136791929) B136791929
theorem B15800255 : Blo 1847625 15800255 := bstep (se 1 (by rfl) ⟨11850191, by rfl⟩ : syracuseStep 15800255 = 23700383) B23700383
theorem B7018721 : Blo 1847625 7018721 := bstep (se 2 (by rfl) ⟨2632020, by rfl⟩ : syracuseStep 7018721 = 5264041) B5264041
theorem B5267015 : Blo 1847625 5267015 := bstep (se 1 (by rfl) ⟨3950261, by rfl⟩ : syracuseStep 5267015 = 7900523) B7900523
theorem B4679147 : Blo 1847625 4679147 := bstep (se 1 (by rfl) ⟨3509360, by rfl⟩ : syracuseStep 4679147 = 7018721) B7018721
theorem B15795881 : Blo 1847625 15795881 := bstep (se 2 (by rfl) ⟨5923455, by rfl⟩ : syracuseStep 15795881 = 11846911) B11846911
theorem B4680443 : Blo 1847625 4680443 := bstep (se 1 (by rfl) ⟨3510332, by rfl⟩ : syracuseStep 4680443 = 7020665) B7020665
theorem B1848191 : Blo 1847625 1848191 := bstep (se 1 (by rfl) ⟨1386143, by rfl⟩ : syracuseStep 1848191 = 2772287) B2772287
theorem B3511343 : Blo 1847625 3511343 := bstep (se 1 (by rfl) ⟨2633507, by rfl⟩ : syracuseStep 3511343 = 5267015) B5267015
theorem B243185651 : Blo 1847625 243185651 := bstep (se 1 (by rfl) ⟨182389238, by rfl⟩ : syracuseStep 243185651 = 364778477) B364778477
theorem B10533503 : Blo 1847625 10533503 := bstep (se 1 (by rfl) ⟨7900127, by rfl⟩ : syracuseStep 10533503 = 15800255) B15800255
theorem B7022335 : Blo 1847625 7022335 := bstep (se 1 (by rfl) ⟨5266751, by rfl⟩ : syracuseStep 7022335 = 10533503) B10533503
theorem B10530587 : Blo 1847625 10530587 := bstep (se 1 (by rfl) ⟨7897940, by rfl⟩ : syracuseStep 10530587 = 15795881) B15795881
theorem B162123767 : Blo 1847625 162123767 := bstep (se 1 (by rfl) ⟨121592825, by rfl⟩ : syracuseStep 162123767 = 243185651) B243185651
theorem B2340895 : Blo 1847625 2340895 := bstep (se 1 (by rfl) ⟨1755671, by rfl⟩ : syracuseStep 2340895 = 3511343) B3511343
theorem B3119431 : Blo 1847625 3119431 := bstep (se 1 (by rfl) ⟨2339573, by rfl⟩ : syracuseStep 3119431 = 4679147) B4679147
theorem B3120295 : Blo 1847625 3120295 := bstep (se 1 (by rfl) ⟨2340221, by rfl⟩ : syracuseStep 3120295 = 4680443) B4680443
theorem B3121193 : Blo 1847625 3121193 := bstep (se 2 (by rfl) ⟨1170447, by rfl⟩ : syracuseStep 3121193 = 2340895) B2340895
theorem B108082511 : Blo 1847625 108082511 := bstep (se 1 (by rfl) ⟨81061883, by rfl⟩ : syracuseStep 108082511 = 162123767) B162123767
theorem B4159241 : Blo 1847625 4159241 := bstep (se 2 (by rfl) ⟨1559715, by rfl⟩ : syracuseStep 4159241 = 3119431) B3119431
theorem B4160393 : Blo 1847625 4160393 := bstep (se 2 (by rfl) ⟨1560147, by rfl⟩ : syracuseStep 4160393 = 3120295) B3120295
theorem B9363113 : Blo 1847625 9363113 := bstep (se 2 (by rfl) ⟨3511167, by rfl⟩ : syracuseStep 9363113 = 7022335) B7022335
theorem B7020391 : Blo 1847625 7020391 := bstep (se 1 (by rfl) ⟨5265293, by rfl⟩ : syracuseStep 7020391 = 10530587) B10530587
theorem B2080795 : Blo 1847625 2080795 := bstep (se 1 (by rfl) ⟨1560596, by rfl⟩ : syracuseStep 2080795 = 3121193) B3121193
theorem B2772827 : Blo 1847625 2772827 := bstep (se 1 (by rfl) ⟨2079620, by rfl⟩ : syracuseStep 2772827 = 4159241) B4159241
theorem B2773595 : Blo 1847625 2773595 := bstep (se 1 (by rfl) ⟨2080196, by rfl⟩ : syracuseStep 2773595 = 4160393) B4160393
theorem B9360521 : Blo 1847625 9360521 := bstep (se 2 (by rfl) ⟨3510195, by rfl⟩ : syracuseStep 9360521 = 7020391) B7020391
theorem B72055007 : Blo 1847625 72055007 := bstep (se 1 (by rfl) ⟨54041255, by rfl⟩ : syracuseStep 72055007 = 108082511) B108082511
theorem B6242075 : Blo 1847625 6242075 := bstep (se 1 (by rfl) ⟨4681556, by rfl⟩ : syracuseStep 6242075 = 9363113) B9363113
theorem B1848551 : Blo 1847625 1848551 := bstep (se 1 (by rfl) ⟨1386413, by rfl⟩ : syracuseStep 1848551 = 2772827) B2772827
theorem B2774393 : Blo 1847625 2774393 := bstep (se 2 (by rfl) ⟨1040397, by rfl⟩ : syracuseStep 2774393 = 2080795) B2080795
theorem B1849063 : Blo 1847625 1849063 := bstep (se 1 (by rfl) ⟨1386797, by rfl⟩ : syracuseStep 1849063 = 2773595) B2773595
theorem B6240347 : Blo 1847625 6240347 := bstep (se 1 (by rfl) ⟨4680260, by rfl⟩ : syracuseStep 6240347 = 9360521) B9360521
theorem B48036671 : Blo 1847625 48036671 := bstep (se 1 (by rfl) ⟨36027503, by rfl⟩ : syracuseStep 48036671 = 72055007) B72055007
theorem B4161383 : Blo 1847625 4161383 := bstep (se 1 (by rfl) ⟨3121037, by rfl⟩ : syracuseStep 4161383 = 6242075) B6242075
theorem B32024447 : Blo 1847625 32024447 := bstep (se 1 (by rfl) ⟨24018335, by rfl⟩ : syracuseStep 32024447 = 48036671) B48036671
theorem B2774255 : Blo 1847625 2774255 := bstep (se 1 (by rfl) ⟨2080691, by rfl⟩ : syracuseStep 2774255 = 4161383) B4161383
theorem B1849595 : Blo 1847625 1849595 := bstep (se 1 (by rfl) ⟨1387196, by rfl⟩ : syracuseStep 1849595 = 2774393) B2774393
theorem B4160231 : Blo 1847625 4160231 := bstep (se 1 (by rfl) ⟨3120173, by rfl⟩ : syracuseStep 4160231 = 6240347) B6240347
theorem B21349631 : Blo 1847625 21349631 := bstep (se 1 (by rfl) ⟨16012223, by rfl⟩ : syracuseStep 21349631 = 32024447) B32024447
theorem B2773487 : Blo 1847625 2773487 := bstep (se 1 (by rfl) ⟨2080115, by rfl⟩ : syracuseStep 2773487 = 4160231) B4160231
theorem B1849503 : Blo 1847625 1849503 := bstep (se 1 (by rfl) ⟨1387127, by rfl⟩ : syracuseStep 1849503 = 2774255) B2774255
theorem B14233087 : Blo 1847625 14233087 := bstep (se 1 (by rfl) ⟨10674815, by rfl⟩ : syracuseStep 14233087 = 21349631) B21349631
theorem B1848991 : Blo 1847625 1848991 := bstep (se 1 (by rfl) ⟨1386743, by rfl⟩ : syracuseStep 1848991 = 2773487) B2773487
theorem B18977449 : Blo 1847625 18977449 := bstep (se 2 (by rfl) ⟨7116543, by rfl⟩ : syracuseStep 18977449 = 14233087) B14233087
theorem B25303265 : Blo 1847625 25303265 := bstep (se 2 (by rfl) ⟨9488724, by rfl⟩ : syracuseStep 25303265 = 18977449) B18977449
theorem B16868843 : Blo 1847625 16868843 := bstep (se 1 (by rfl) ⟨12651632, by rfl⟩ : syracuseStep 16868843 = 25303265) B25303265
theorem B11245895 : Blo 1847625 11245895 := bstep (se 1 (by rfl) ⟨8434421, by rfl⟩ : syracuseStep 11245895 = 16868843) B16868843
theorem B7497263 : Blo 1847625 7497263 := bstep (se 1 (by rfl) ⟨5622947, by rfl⟩ : syracuseStep 7497263 = 11245895) B11245895
theorem B4998175 : Blo 1847625 4998175 := bstep (se 1 (by rfl) ⟨3748631, by rfl⟩ : syracuseStep 4998175 = 7497263) B7497263
theorem B26656933 : Blo 1847625 26656933 := bstep (se 4 (by rfl) ⟨2499087, by rfl⟩ : syracuseStep 26656933 = 4998175) B4998175
theorem B35542577 : Blo 1847625 35542577 := bstep (se 2 (by rfl) ⟨13328466, by rfl⟩ : syracuseStep 35542577 = 26656933) B26656933
theorem B23695051 : Blo 1847625 23695051 := bstep (se 1 (by rfl) ⟨17771288, by rfl⟩ : syracuseStep 23695051 = 35542577) B35542577
theorem B31593401 : Blo 1847625 31593401 := bstep (se 2 (by rfl) ⟨11847525, by rfl⟩ : syracuseStep 31593401 = 23695051) B23695051
theorem B21062267 : Blo 1847625 21062267 := bstep (se 1 (by rfl) ⟨15796700, by rfl⟩ : syracuseStep 21062267 = 31593401) B31593401
theorem B14041511 : Blo 1847625 14041511 := bstep (se 1 (by rfl) ⟨10531133, by rfl⟩ : syracuseStep 14041511 = 21062267) B21062267
theorem B9361007 : Blo 1847625 9361007 := bstep (se 1 (by rfl) ⟨7020755, by rfl⟩ : syracuseStep 9361007 = 14041511) B14041511
theorem B6240671 : Blo 1847625 6240671 := bstep (se 1 (by rfl) ⟨4680503, by rfl⟩ : syracuseStep 6240671 = 9361007) B9361007
theorem B4160447 : Blo 1847625 4160447 := bstep (se 1 (by rfl) ⟨3120335, by rfl⟩ : syracuseStep 4160447 = 6240671) B6240671
theorem B2773631 : Blo 1847625 2773631 := bstep (se 1 (by rfl) ⟨2080223, by rfl⟩ : syracuseStep 2773631 = 4160447) B4160447
theorem B1849087 : Blo 1847625 1849087 := bstep (se 1 (by rfl) ⟨1386815, by rfl⟩ : syracuseStep 1849087 = 2773631) B2773631

theorem C0 (j : ℕ) (h1 : 461906 ≤ j) (h2 : j ≤ 462405) : Blo 1847625 (4 * j + 3) := by
  interval_cases j
  · exact B1847627
  · exact B1847631
  · exact B1847635
  · exact B1847639
  · exact B1847643
  · exact B1847647
  · exact B1847651
  · exact B1847655
  · exact B1847659
  · exact B1847663
  · exact B1847667
  · exact B1847671
  · exact B1847675
  · exact B1847679
  · exact B1847683
  · exact B1847687
  · exact B1847691
  · exact B1847695
  · exact B1847699
  · exact B1847703
  · exact B1847707
  · exact B1847711
  · exact B1847715
  · exact B1847719
  · exact B1847723
  · exact B1847727
  · exact B1847731
  · exact B1847735
  · exact B1847739
  · exact B1847743
  · exact B1847747
  · exact B1847751
  · exact B1847755
  · exact B1847759
  · exact B1847763
  · exact B1847767
  · exact B1847771
  · exact B1847775
  · exact B1847779
  · exact B1847783
  · exact B1847787
  · exact B1847791
  · exact B1847795
  · exact B1847799
  · exact B1847803
  · exact B1847807
  · exact B1847811
  · exact B1847815
  · exact B1847819
  · exact B1847823
  · exact B1847827
  · exact B1847831
  · exact B1847835
  · exact B1847839
  · exact B1847843
  · exact B1847847
  · exact B1847851
  · exact B1847855
  · exact B1847859
  · exact B1847863
  · exact B1847867
  · exact B1847871
  · exact B1847875
  · exact B1847879
  · exact B1847883
  · exact B1847887
  · exact B1847891
  · exact B1847895
  · exact B1847899
  · exact B1847903
  · exact B1847907
  · exact B1847911
  · exact B1847915
  · exact B1847919
  · exact B1847923
  · exact B1847927
  · exact B1847931
  · exact B1847935
  · exact B1847939
  · exact B1847943
  · exact B1847947
  · exact B1847951
  · exact B1847955
  · exact B1847959
  · exact B1847963
  · exact B1847967
  · exact B1847971
  · exact B1847975
  · exact B1847979
  · exact B1847983
  · exact B1847987
  · exact B1847991
  · exact B1847995
  · exact B1847999
  · exact B1848003
  · exact B1848007
  · exact B1848011
  · exact B1848015
  · exact B1848019
  · exact B1848023
  · exact B1848027
  · exact B1848031
  · exact B1848035
  · exact B1848039
  · exact B1848043
  · exact B1848047
  · exact B1848051
  · exact B1848055
  · exact B1848059
  · exact B1848063
  · exact B1848067
  · exact B1848071
  · exact B1848075
  · exact B1848079
  · exact B1848083
  · exact B1848087
  · exact B1848091
  · exact B1848095
  · exact B1848099
  · exact B1848103
  · exact B1848107
  · exact B1848111
  · exact B1848115
  · exact B1848119
  · exact B1848123
  · exact B1848127
  · exact B1848131
  · exact B1848135
  · exact B1848139
  · exact B1848143
  · exact B1848147
  · exact B1848151
  · exact B1848155
  · exact B1848159
  · exact B1848163
  · exact B1848167
  · exact B1848171
  · exact B1848175
  · exact B1848179
  · exact B1848183
  · exact B1848187
  · exact B1848191
  · exact B1848195
  · exact B1848199
  · exact B1848203
  · exact B1848207
  · exact B1848211
  · exact B1848215
  · exact B1848219
  · exact B1848223
  · exact B1848227
  · exact B1848231
  · exact B1848235
  · exact B1848239
  · exact B1848243
  · exact B1848247
  · exact B1848251
  · exact B1848255
  · exact B1848259
  · exact B1848263
  · exact B1848267
  · exact B1848271
  · exact B1848275
  · exact B1848279
  · exact B1848283
  · exact B1848287
  · exact B1848291
  · exact B1848295
  · exact B1848299
  · exact B1848303
  · exact B1848307
  · exact B1848311
  · exact B1848315
  · exact B1848319
  · exact B1848323
  · exact B1848327
  · exact B1848331
  · exact B1848335
  · exact B1848339
  · exact B1848343
  · exact B1848347
  · exact B1848351
  · exact B1848355
  · exact B1848359
  · exact B1848363
  · exact B1848367
  · exact B1848371
  · exact B1848375
  · exact B1848379
  · exact B1848383
  · exact B1848387
  · exact B1848391
  · exact B1848395
  · exact B1848399
  · exact B1848403
  · exact B1848407
  · exact B1848411
  · exact B1848415
  · exact B1848419
  · exact B1848423
  · exact B1848427
  · exact B1848431
  · exact B1848435
  · exact B1848439
  · exact B1848443
  · exact B1848447
  · exact B1848451
  · exact B1848455
  · exact B1848459
  · exact B1848463
  · exact B1848467
  · exact B1848471
  · exact B1848475
  · exact B1848479
  · exact B1848483
  · exact B1848487
  · exact B1848491
  · exact B1848495
  · exact B1848499
  · exact B1848503
  · exact B1848507
  · exact B1848511
  · exact B1848515
  · exact B1848519
  · exact B1848523
  · exact B1848527
  · exact B1848531
  · exact B1848535
  · exact B1848539
  · exact B1848543
  · exact B1848547
  · exact B1848551
  · exact B1848555
  · exact B1848559
  · exact B1848563
  · exact B1848567
  · exact B1848571
  · exact B1848575
  · exact B1848579
  · exact B1848583
  · exact B1848587
  · exact B1848591
  · exact B1848595
  · exact B1848599
  · exact B1848603
  · exact B1848607
  · exact B1848611
  · exact B1848615
  · exact B1848619
  · exact B1848623
  · exact B1848627
  · exact B1848631
  · exact B1848635
  · exact B1848639
  · exact B1848643
  · exact B1848647
  · exact B1848651
  · exact B1848655
  · exact B1848659
  · exact B1848663
  · exact B1848667
  · exact B1848671
  · exact B1848675
  · exact B1848679
  · exact B1848683
  · exact B1848687
  · exact B1848691
  · exact B1848695
  · exact B1848699
  · exact B1848703
  · exact B1848707
  · exact B1848711
  · exact B1848715
  · exact B1848719
  · exact B1848723
  · exact B1848727
  · exact B1848731
  · exact B1848735
  · exact B1848739
  · exact B1848743
  · exact B1848747
  · exact B1848751
  · exact B1848755
  · exact B1848759
  · exact B1848763
  · exact B1848767
  · exact B1848771
  · exact B1848775
  · exact B1848779
  · exact B1848783
  · exact B1848787
  · exact B1848791
  · exact B1848795
  · exact B1848799
  · exact B1848803
  · exact B1848807
  · exact B1848811
  · exact B1848815
  · exact B1848819
  · exact B1848823
  · exact B1848827
  · exact B1848831
  · exact B1848835
  · exact B1848839
  · exact B1848843
  · exact B1848847
  · exact B1848851
  · exact B1848855
  · exact B1848859
  · exact B1848863
  · exact B1848867
  · exact B1848871
  · exact B1848875
  · exact B1848879
  · exact B1848883
  · exact B1848887
  · exact B1848891
  · exact B1848895
  · exact B1848899
  · exact B1848903
  · exact B1848907
  · exact B1848911
  · exact B1848915
  · exact B1848919
  · exact B1848923
  · exact B1848927
  · exact B1848931
  · exact B1848935
  · exact B1848939
  · exact B1848943
  · exact B1848947
  · exact B1848951
  · exact B1848955
  · exact B1848959
  · exact B1848963
  · exact B1848967
  · exact B1848971
  · exact B1848975
  · exact B1848979
  · exact B1848983
  · exact B1848987
  · exact B1848991
  · exact B1848995
  · exact B1848999
  · exact B1849003
  · exact B1849007
  · exact B1849011
  · exact B1849015
  · exact B1849019
  · exact B1849023
  · exact B1849027
  · exact B1849031
  · exact B1849035
  · exact B1849039
  · exact B1849043
  · exact B1849047
  · exact B1849051
  · exact B1849055
  · exact B1849059
  · exact B1849063
  · exact B1849067
  · exact B1849071
  · exact B1849075
  · exact B1849079
  · exact B1849083
  · exact B1849087
  · exact B1849091
  · exact B1849095
  · exact B1849099
  · exact B1849103
  · exact B1849107
  · exact B1849111
  · exact B1849115
  · exact B1849119
  · exact B1849123
  · exact B1849127
  · exact B1849131
  · exact B1849135
  · exact B1849139
  · exact B1849143
  · exact B1849147
  · exact B1849151
  · exact B1849155
  · exact B1849159
  · exact B1849163
  · exact B1849167
  · exact B1849171
  · exact B1849175
  · exact B1849179
  · exact B1849183
  · exact B1849187
  · exact B1849191
  · exact B1849195
  · exact B1849199
  · exact B1849203
  · exact B1849207
  · exact B1849211
  · exact B1849215
  · exact B1849219
  · exact B1849223
  · exact B1849227
  · exact B1849231
  · exact B1849235
  · exact B1849239
  · exact B1849243
  · exact B1849247
  · exact B1849251
  · exact B1849255
  · exact B1849259
  · exact B1849263
  · exact B1849267
  · exact B1849271
  · exact B1849275
  · exact B1849279
  · exact B1849283
  · exact B1849287
  · exact B1849291
  · exact B1849295
  · exact B1849299
  · exact B1849303
  · exact B1849307
  · exact B1849311
  · exact B1849315
  · exact B1849319
  · exact B1849323
  · exact B1849327
  · exact B1849331
  · exact B1849335
  · exact B1849339
  · exact B1849343
  · exact B1849347
  · exact B1849351
  · exact B1849355
  · exact B1849359
  · exact B1849363
  · exact B1849367
  · exact B1849371
  · exact B1849375
  · exact B1849379
  · exact B1849383
  · exact B1849387
  · exact B1849391
  · exact B1849395
  · exact B1849399
  · exact B1849403
  · exact B1849407
  · exact B1849411
  · exact B1849415
  · exact B1849419
  · exact B1849423
  · exact B1849427
  · exact B1849431
  · exact B1849435
  · exact B1849439
  · exact B1849443
  · exact B1849447
  · exact B1849451
  · exact B1849455
  · exact B1849459
  · exact B1849463
  · exact B1849467
  · exact B1849471
  · exact B1849475
  · exact B1849479
  · exact B1849483
  · exact B1849487
  · exact B1849491
  · exact B1849495
  · exact B1849499
  · exact B1849503
  · exact B1849507
  · exact B1849511
  · exact B1849515
  · exact B1849519
  · exact B1849523
  · exact B1849527
  · exact B1849531
  · exact B1849535
  · exact B1849539
  · exact B1849543
  · exact B1849547
  · exact B1849551
  · exact B1849555
  · exact B1849559
  · exact B1849563
  · exact B1849567
  · exact B1849571
  · exact B1849575
  · exact B1849579
  · exact B1849583
  · exact B1849587
  · exact B1849591
  · exact B1849595
  · exact B1849599
  · exact B1849603
  · exact B1849607
  · exact B1849611
  · exact B1849615
  · exact B1849619
  · exact B1849623

theorem solution (m : ℕ) (hlo : 1847625 ≤ m) (hhi : m ≤ 1849625) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 461906 ≤ j := by omega
    have hj2 : j ≤ 462405 := by omega
    have hb : Blo 1847625 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
