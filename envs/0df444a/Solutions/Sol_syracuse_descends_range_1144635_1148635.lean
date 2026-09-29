-- Prove2me | solution 1 for syracuse_descends_range_1144635_1148635
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:46.662997+00:00
-- url     : https://prove2.me/submissions/daf4c6c8-6711-4b9f-9605-65cc3842ffdf

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


theorem B1933429 : Blo 1144635 1933429 := bbase (se 5 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 1933429 = 181259) (by norm_num)
theorem B5800085 : Blo 1144635 5800085 := bbase (se 6 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 5800085 = 271879) (by norm_num)
theorem B1933517 : Blo 1144635 1933517 := bbase (se 3 (by rfl) ⟨362534, by rfl⟩ : syracuseStep 1933517 = 725069) (by norm_num)
theorem B4358357 : Blo 1144635 4358357 := bbase (se 7 (by rfl) ⟨51074, by rfl⟩ : syracuseStep 4358357 = 102149) (by norm_num)
theorem B3866885 : Blo 1144635 3866885 := bbase (se 4 (by rfl) ⟨362520, by rfl⟩ : syracuseStep 3866885 = 725041) (by norm_num)
theorem B1376561 : Blo 1144635 1376561 := bbase (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) (by norm_num)
theorem B1933645 : Blo 1144635 1933645 := bbase (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) (by norm_num)
theorem B1835389 : Blo 1144635 1835389 := bbase (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) (by norm_num)
theorem B1933733 : Blo 1144635 1933733 := bbase (se 4 (by rfl) ⟨181287, by rfl⟩ : syracuseStep 1933733 = 362575) (by norm_num)
theorem B6521269 : Blo 1144635 6521269 := bbase (se 5 (by rfl) ⟨305684, by rfl⟩ : syracuseStep 6521269 = 611369) (by norm_num)
theorem B1933861 : Blo 1144635 1933861 := bbase (se 4 (by rfl) ⟨181299, by rfl⟩ : syracuseStep 1933861 = 362599) (by norm_num)
theorem B9306677 : Blo 1144635 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B1933949 : Blo 1144635 1933949 := bbase (se 3 (by rfl) ⟨362615, by rfl⟩ : syracuseStep 1933949 = 725231) (by norm_num)
theorem B2654893 : Blo 1144635 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B3867317 : Blo 1144635 3867317 := bbase (se 5 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 3867317 = 362561) (by norm_num)
theorem B2753237 : Blo 1144635 2753237 := bbase (se 7 (by rfl) ⟨32264, by rfl⟩ : syracuseStep 2753237 = 64529) (by norm_num)
theorem B1934077 : Blo 1144635 1934077 := bbase (se 3 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 1934077 = 725279) (by norm_num)
theorem B1934165 : Blo 1144635 1934165 := bbase (se 9 (by rfl) ⟨5666, by rfl⟩ : syracuseStep 1934165 = 11333) (by norm_num)
theorem B2982757 : Blo 1144635 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B1377157 : Blo 1144635 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1934293 : Blo 1144635 1934293 := bbase (se 7 (by rfl) ⟨22667, by rfl⟩ : syracuseStep 1934293 = 45335) (by norm_num)
theorem B1377253 : Blo 1144635 1377253 := bbase (se 4 (by rfl) ⟨129117, by rfl⟩ : syracuseStep 1377253 = 258235) (by norm_num)
theorem B1934381 : Blo 1144635 1934381 := bbase (se 3 (by rfl) ⟨362696, by rfl⟩ : syracuseStep 1934381 = 725393) (by norm_num)
theorem B1836101 : Blo 1144635 1836101 := bbase (se 4 (by rfl) ⟨172134, by rfl⟩ : syracuseStep 1836101 = 344269) (by norm_num)
theorem B3867749 : Blo 1144635 3867749 := bbase (se 4 (by rfl) ⟨362601, by rfl⟩ : syracuseStep 3867749 = 725203) (by norm_num)
theorem B1934509 : Blo 1144635 1934509 := bbase (se 3 (by rfl) ⟨362720, by rfl⟩ : syracuseStep 1934509 = 725441) (by norm_num)
theorem B4129973 : Blo 1144635 4129973 := bbase (se 5 (by rfl) ⟨193592, by rfl⟩ : syracuseStep 4129973 = 387185) (by norm_num)
theorem B4654261 : Blo 1144635 4654261 := bbase (se 5 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 4654261 = 436337) (by norm_num)
theorem B1934597 : Blo 1144635 1934597 := bbase (se 4 (by rfl) ⟨181368, by rfl⟩ : syracuseStep 1934597 = 362737) (by norm_num)
theorem B3671381 : Blo 1144635 3671381 := bbase (se 12 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3671381 = 2689) (by norm_num)
theorem B4359541 : Blo 1144635 4359541 := bbase (se 5 (by rfl) ⟨204353, by rfl⟩ : syracuseStep 4359541 = 408707) (by norm_num)
theorem B1934725 : Blo 1144635 1934725 := bbase (se 4 (by rfl) ⟨181380, by rfl⟩ : syracuseStep 1934725 = 362761) (by norm_num)
theorem B5801381 : Blo 1144635 5801381 := bbase (se 4 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 5801381 = 1087759) (by norm_num)
theorem B1934813 : Blo 1144635 1934813 := bbase (se 3 (by rfl) ⟨362777, by rfl⟩ : syracuseStep 1934813 = 725555) (by norm_num)
theorem B3868181 : Blo 1144635 3868181 := bbase (se 6 (by rfl) ⟨90660, by rfl⟩ : syracuseStep 3868181 = 181321) (by norm_num)
theorem B2065981 : Blo 1144635 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B1934941 : Blo 1144635 1934941 := bbase (se 3 (by rfl) ⟨362801, by rfl⟩ : syracuseStep 1934941 = 725603) (by norm_num)
theorem B4359845 : Blo 1144635 4359845 := bbase (se 4 (by rfl) ⟨408735, by rfl⟩ : syracuseStep 4359845 = 817471) (by norm_num)
theorem B1935029 : Blo 1144635 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B11175637 : Blo 1144635 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B1836773 : Blo 1144635 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B1935157 : Blo 1144635 1935157 := bbase (se 5 (by rfl) ⟨90710, by rfl⟩ : syracuseStep 1935157 = 181421) (by norm_num)
theorem B7341941 : Blo 1144635 7341941 := bbase (se 5 (by rfl) ⟨344153, by rfl⟩ : syracuseStep 7341941 = 688307) (by norm_num)
theorem B9930613 : Blo 1144635 9930613 := bbase (se 5 (by rfl) ⟨465497, by rfl⟩ : syracuseStep 9930613 = 930995) (by norm_num)
theorem B1935245 : Blo 1144635 1935245 := bbase (se 3 (by rfl) ⟨362858, by rfl⟩ : syracuseStep 1935245 = 725717) (by norm_num)
theorem B3868613 : Blo 1144635 3868613 := bbase (se 4 (by rfl) ⟨362682, by rfl⟩ : syracuseStep 3868613 = 725365) (by norm_num)
theorem B1935373 : Blo 1144635 1935373 := bbase (se 3 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 1935373 = 725765) (by norm_num)
theorem B2066485 : Blo 1144635 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1378397 : Blo 1144635 1378397 := bbase (se 3 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 1378397 = 516899) (by norm_num)
theorem B1935461 : Blo 1144635 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B5376149 : Blo 1144635 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1837285 : Blo 1144635 1837285 := bbase (se 4 (by rfl) ⟨172245, by rfl⟩ : syracuseStep 1837285 = 344491) (by norm_num)
theorem B1935589 : Blo 1144635 1935589 := bbase (se 4 (by rfl) ⟨181461, by rfl⟩ : syracuseStep 1935589 = 362923) (by norm_num)
theorem B4131125 : Blo 1144635 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B1935677 : Blo 1144635 1935677 := bbase (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) (by norm_num)
theorem B6523253 : Blo 1144635 6523253 := bbase (se 5 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 6523253 = 611555) (by norm_num)
theorem B3869045 : Blo 1144635 3869045 := bbase (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) (by norm_num)
theorem B3672469 : Blo 1144635 3672469 := bbase (se 6 (by rfl) ⟨86073, by rfl⟩ : syracuseStep 3672469 = 172147) (by norm_num)
theorem B1378729 : Blo 1144635 1378729 := bbase (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) (by norm_num)
theorem B1935805 : Blo 1144635 1935805 := bbase (se 3 (by rfl) ⟨362963, by rfl⟩ : syracuseStep 1935805 = 725927) (by norm_num)
theorem B1935893 : Blo 1144635 1935893 := bbase (se 6 (by rfl) ⟨45372, by rfl⟩ : syracuseStep 1935893 = 90745) (by norm_num)
theorem B1936021 : Blo 1144635 1936021 := bbase (se 6 (by rfl) ⟨45375, by rfl⟩ : syracuseStep 1936021 = 90751) (by norm_num)
theorem B1837741 : Blo 1144635 1837741 := bbase (se 3 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 1837741 = 689153) (by norm_num)
theorem B5802677 : Blo 1144635 5802677 := bbase (se 5 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 5802677 = 544001) (by norm_num)
theorem B1936109 : Blo 1144635 1936109 := bbase (se 3 (by rfl) ⟨363020, by rfl⟩ : syracuseStep 1936109 = 726041) (by norm_num)
theorem B3869477 : Blo 1144635 3869477 := bbase (se 4 (by rfl) ⟨362763, by rfl⟩ : syracuseStep 3869477 = 725527) (by norm_num)
theorem B1936237 : Blo 1144635 1936237 := bbase (se 3 (by rfl) ⟨363044, by rfl⟩ : syracuseStep 1936237 = 726089) (by norm_num)
theorem B2067365 : Blo 1144635 2067365 := bbase (se 4 (by rfl) ⟨193815, by rfl⟩ : syracuseStep 2067365 = 387631) (by norm_num)
theorem B1936325 : Blo 1144635 1936325 := bbase (se 4 (by rfl) ⟨181530, by rfl⟩ : syracuseStep 1936325 = 363061) (by norm_num)
theorem B2755613 : Blo 1144635 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B1936453 : Blo 1144635 1936453 := bbase (se 4 (by rfl) ⟨181542, by rfl⟩ : syracuseStep 1936453 = 363085) (by norm_num)
theorem B1379425 : Blo 1144635 1379425 := bbase (se 2 (by rfl) ⟨517284, by rfl⟩ : syracuseStep 1379425 = 1034569) (by norm_num)
theorem B2067581 : Blo 1144635 2067581 := bbase (se 3 (by rfl) ⟨387671, by rfl⟩ : syracuseStep 2067581 = 775343) (by norm_num)
theorem B1379473 : Blo 1144635 1379473 := bbase (se 2 (by rfl) ⟨517302, by rfl⟩ : syracuseStep 1379473 = 1034605) (by norm_num)
theorem B1936541 : Blo 1144635 1936541 := bbase (se 3 (by rfl) ⟨363101, by rfl⟩ : syracuseStep 1936541 = 726203) (by norm_num)
theorem B3869909 : Blo 1144635 3869909 := bbase (se 7 (by rfl) ⟨45350, by rfl⟩ : syracuseStep 3869909 = 90701) (by norm_num)
theorem B2067725 : Blo 1144635 2067725 := bbase (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) (by norm_num)
theorem B1936669 : Blo 1144635 1936669 := bbase (se 3 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 1936669 = 726251) (by norm_num)
theorem B1838413 : Blo 1144635 1838413 := bbase (se 3 (by rfl) ⟨344702, by rfl⟩ : syracuseStep 1838413 = 689405) (by norm_num)
theorem B2067805 : Blo 1144635 2067805 := bbase (se 3 (by rfl) ⟨387713, by rfl⟩ : syracuseStep 2067805 = 775427) (by norm_num)
theorem B1936757 : Blo 1144635 1936757 := bbase (se 5 (by rfl) ⟨90785, by rfl⟩ : syracuseStep 1936757 = 181571) (by norm_num)
theorem B4656533 : Blo 1144635 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B2755997 : Blo 1144635 2755997 := bbase (se 3 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 2755997 = 1033499) (by norm_num)
theorem B1936885 : Blo 1144635 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B3673637 : Blo 1144635 3673637 := bbase (se 4 (by rfl) ⟨344403, by rfl⟩ : syracuseStep 3673637 = 688807) (by norm_num)
theorem B1936973 : Blo 1144635 1936973 := bbase (se 3 (by rfl) ⟨363182, by rfl⟩ : syracuseStep 1936973 = 726365) (by norm_num)
theorem B2756197 : Blo 1144635 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B3870341 : Blo 1144635 3870341 := bbase (se 4 (by rfl) ⟨362844, by rfl⟩ : syracuseStep 3870341 = 725689) (by norm_num)
theorem B1937101 : Blo 1144635 1937101 := bbase (se 3 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 1937101 = 726413) (by norm_num)
theorem B1838837 : Blo 1144635 1838837 := bbase (se 5 (by rfl) ⟨86195, by rfl⟩ : syracuseStep 1838837 = 172391) (by norm_num)
theorem B1937189 : Blo 1144635 1937189 := bbase (se 4 (by rfl) ⟨181611, by rfl⟩ : syracuseStep 1937189 = 363223) (by norm_num)
theorem B5508917 : Blo 1144635 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B1740677 : Blo 1144635 1740677 := bbase (se 4 (by rfl) ⟨163188, by rfl⟩ : syracuseStep 1740677 = 326377) (by norm_num)
theorem B1937317 : Blo 1144635 1937317 := bbase (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) (by norm_num)
theorem B5803973 : Blo 1144635 5803973 := bbase (se 4 (by rfl) ⟨544122, by rfl⟩ : syracuseStep 5803973 = 1088245) (by norm_num)
theorem B1937405 : Blo 1144635 1937405 := bbase (se 3 (by rfl) ⟨363263, by rfl⟩ : syracuseStep 1937405 = 726527) (by norm_num)
theorem B1839125 : Blo 1144635 1839125 := bbase (se 6 (by rfl) ⟨43104, by rfl⟩ : syracuseStep 1839125 = 86209) (by norm_num)
theorem B3870773 : Blo 1144635 3870773 := bbase (se 5 (by rfl) ⟨181442, by rfl⟩ : syracuseStep 3870773 = 362885) (by norm_num)
theorem B2789477 : Blo 1144635 2789477 := bbase (se 4 (by rfl) ⟨261513, by rfl⟩ : syracuseStep 2789477 = 523027) (by norm_num)
theorem B1937533 : Blo 1144635 1937533 := bbase (se 3 (by rfl) ⟨363287, by rfl⟩ : syracuseStep 1937533 = 726575) (by norm_num)
theorem B1937621 : Blo 1144635 1937621 := bbase (se 7 (by rfl) ⟨22706, by rfl⟩ : syracuseStep 1937621 = 45413) (by norm_num)
theorem B1937749 : Blo 1144635 1937749 := bbase (se 10 (by rfl) ⟨2838, by rfl⟩ : syracuseStep 1937749 = 5677) (by norm_num)
theorem B1937837 : Blo 1144635 1937837 := bbase (se 3 (by rfl) ⟨363344, by rfl⟩ : syracuseStep 1937837 = 726689) (by norm_num)
theorem B3871205 : Blo 1144635 3871205 := bbase (se 4 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 3871205 = 725851) (by norm_num)
theorem B6525461 : Blo 1144635 6525461 := bbase (se 6 (by rfl) ⟨152940, by rfl⟩ : syracuseStep 6525461 = 305881) (by norm_num)
theorem B19599893 : Blo 1144635 19599893 := bbase (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) (by norm_num)
theorem B1937965 : Blo 1144635 1937965 := bbase (se 3 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 1937965 = 726737) (by norm_num)
theorem B1938053 : Blo 1144635 1938053 := bbase (se 4 (by rfl) ⟨181692, by rfl⟩ : syracuseStep 1938053 = 363385) (by norm_num)
theorem B4133605 : Blo 1144635 4133605 := bbase (se 4 (by rfl) ⟨387525, by rfl⟩ : syracuseStep 4133605 = 775051) (by norm_num)
theorem B1938181 : Blo 1144635 1938181 := bbase (se 4 (by rfl) ⟨181704, by rfl⟩ : syracuseStep 1938181 = 363409) (by norm_num)
theorem B1938269 : Blo 1144635 1938269 := bbase (se 3 (by rfl) ⟨363425, by rfl⟩ : syracuseStep 1938269 = 726851) (by norm_num)
theorem B8721269 : Blo 1144635 8721269 := bbase (se 5 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 8721269 = 817619) (by norm_num)
theorem B3871637 : Blo 1144635 3871637 := bbase (se 6 (by rfl) ⟨90741, by rfl⟩ : syracuseStep 3871637 = 181483) (by norm_num)
theorem B2790413 : Blo 1144635 2790413 := bbase (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) (by norm_num)
theorem B2757773 : Blo 1144635 2757773 := bbase (se 3 (by rfl) ⟨517082, by rfl⟩ : syracuseStep 2757773 = 1034165) (by norm_num)
theorem B5805269 : Blo 1144635 5805269 := bbase (se 7 (by rfl) ⟨68030, by rfl⟩ : syracuseStep 5805269 = 136061) (by norm_num)
theorem B3872069 : Blo 1144635 3872069 := bbase (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) (by norm_num)
theorem B3675493 : Blo 1144635 3675493 := bbase (se 4 (by rfl) ⟨344577, by rfl⟩ : syracuseStep 3675493 = 689155) (by norm_num)
theorem B6198677 : Blo 1144635 6198677 := bbase (se 6 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 6198677 = 290563) (by norm_num)
theorem B1414597 : Blo 1144635 1414597 := bbase (se 4 (by rfl) ⟨132618, by rfl⟩ : syracuseStep 1414597 = 265237) (by norm_num)
theorem B4134341 : Blo 1144635 4134341 := bbase (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) (by norm_num)
theorem B1742405 : Blo 1144635 1742405 := bbase (se 4 (by rfl) ⟨163350, by rfl⟩ : syracuseStep 1742405 = 326701) (by norm_num)
theorem B1742429 : Blo 1144635 1742429 := bbase (se 3 (by rfl) ⟨326705, by rfl⟩ : syracuseStep 1742429 = 653411) (by norm_num)
theorem B3872501 : Blo 1144635 3872501 := bbase (se 5 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 3872501 = 363047) (by norm_num)
theorem B5510933 : Blo 1144635 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B4135045 : Blo 1144635 4135045 := bbase (se 4 (by rfl) ⟨387660, by rfl⟩ : syracuseStep 4135045 = 775321) (by norm_num)
theorem B3872933 : Blo 1144635 3872933 := bbase (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) (by norm_num)
theorem B5806565 : Blo 1144635 5806565 := bbase (se 4 (by rfl) ⟨544365, by rfl⟩ : syracuseStep 5806565 = 1088731) (by norm_num)
theorem B5511685 : Blo 1144635 5511685 := bbase (se 4 (by rfl) ⟨516720, by rfl⟩ : syracuseStep 5511685 = 1033441) (by norm_num)
theorem B2759197 : Blo 1144635 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B3873365 : Blo 1144635 3873365 := bbase (se 8 (by rfl) ⟨22695, by rfl⟩ : syracuseStep 3873365 = 45391) (by norm_num)
theorem B10459829 : Blo 1144635 10459829 := bbase (se 5 (by rfl) ⟨490304, by rfl⟩ : syracuseStep 10459829 = 980609) (by norm_num)
theorem B3676853 : Blo 1144635 3676853 := bbase (se 5 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 3676853 = 344705) (by norm_num)
theorem B1448705 : Blo 1144635 1448705 := bbase (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) (by norm_num)
theorem B1448761 : Blo 1144635 1448761 := bbase (se 2 (by rfl) ⟨543285, by rfl⟩ : syracuseStep 1448761 = 1086571) (by norm_num)
theorem B1448857 : Blo 1144635 1448857 := bbase (se 2 (by rfl) ⟨543321, by rfl⟩ : syracuseStep 1448857 = 1086643) (by norm_num)
theorem B3873797 : Blo 1144635 3873797 := bbase (se 4 (by rfl) ⟨363168, by rfl⟩ : syracuseStep 3873797 = 726337) (by norm_num)
theorem B1449029 : Blo 1144635 1449029 := bbase (se 4 (by rfl) ⟨135846, by rfl⟩ : syracuseStep 1449029 = 271693) (by norm_num)
theorem B1449085 : Blo 1144635 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B1449181 : Blo 1144635 1449181 := bbase (se 3 (by rfl) ⟨271721, by rfl⟩ : syracuseStep 1449181 = 543443) (by norm_num)
theorem B1449353 : Blo 1144635 1449353 := bbase (se 2 (by rfl) ⟨543507, by rfl⟩ : syracuseStep 1449353 = 1087015) (by norm_num)
theorem B3874229 : Blo 1144635 3874229 := bbase (se 5 (by rfl) ⟨181604, by rfl⟩ : syracuseStep 3874229 = 363209) (by norm_num)
theorem B1449409 : Blo 1144635 1449409 := bbase (se 2 (by rfl) ⟨543528, by rfl⟩ : syracuseStep 1449409 = 1087057) (by norm_num)
theorem B2203109 : Blo 1144635 2203109 := bbase (se 4 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 2203109 = 413083) (by norm_num)
theorem B1449505 : Blo 1144635 1449505 := bbase (se 2 (by rfl) ⟨543564, by rfl⟩ : syracuseStep 1449505 = 1087129) (by norm_num)
theorem B2301509 : Blo 1144635 2301509 := bbase (se 4 (by rfl) ⟨215766, by rfl⟩ : syracuseStep 2301509 = 431533) (by norm_num)
theorem B9313973 : Blo 1144635 9313973 := bbase (se 5 (by rfl) ⟨436592, by rfl⟩ : syracuseStep 9313973 = 873185) (by norm_num)
theorem B1449677 : Blo 1144635 1449677 := bbase (se 3 (by rfl) ⟨271814, by rfl⟩ : syracuseStep 1449677 = 543629) (by norm_num)
theorem B5807861 : Blo 1144635 5807861 := bbase (se 5 (by rfl) ⟨272243, by rfl⟩ : syracuseStep 5807861 = 544487) (by norm_num)
theorem B1449733 : Blo 1144635 1449733 := bbase (se 4 (by rfl) ⟨135912, by rfl⟩ : syracuseStep 1449733 = 271825) (by norm_num)
theorem B1449829 : Blo 1144635 1449829 := bbase (se 4 (by rfl) ⟨135921, by rfl⟩ : syracuseStep 1449829 = 271843) (by norm_num)
theorem B3874661 : Blo 1144635 3874661 := bbase (se 4 (by rfl) ⟨363249, by rfl⟩ : syracuseStep 3874661 = 726499) (by norm_num)
theorem B1450001 : Blo 1144635 1450001 := bbase (se 2 (by rfl) ⟨543750, by rfl⟩ : syracuseStep 1450001 = 1087501) (by norm_num)
theorem B8822837 : Blo 1144635 8822837 := bbase (se 5 (by rfl) ⟨413570, by rfl⟩ : syracuseStep 8822837 = 827141) (by norm_num)
theorem B1450057 : Blo 1144635 1450057 := bbase (se 2 (by rfl) ⟨543771, by rfl⟩ : syracuseStep 1450057 = 1087543) (by norm_num)
theorem B1450153 : Blo 1144635 1450153 := bbase (se 2 (by rfl) ⟨543807, by rfl⟩ : syracuseStep 1450153 = 1087615) (by norm_num)
theorem B1745101 : Blo 1144635 1745101 := bbase (se 3 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 1745101 = 654413) (by norm_num)
theorem B3875093 : Blo 1144635 3875093 := bbase (se 6 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 3875093 = 181645) (by norm_num)
theorem B1450325 : Blo 1144635 1450325 := bbase (se 10 (by rfl) ⟨2124, by rfl⟩ : syracuseStep 1450325 = 4249) (by norm_num)
theorem B1450381 : Blo 1144635 1450381 := bbase (se 3 (by rfl) ⟨271946, by rfl⟩ : syracuseStep 1450381 = 543893) (by norm_num)
theorem B3350965 : Blo 1144635 3350965 := bbase (se 5 (by rfl) ⟨157076, by rfl⟩ : syracuseStep 3350965 = 314153) (by norm_num)
theorem B1450477 : Blo 1144635 1450477 := bbase (se 3 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 1450477 = 543929) (by norm_num)
theorem B1450649 : Blo 1144635 1450649 := bbase (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) (by norm_num)
theorem B3875525 : Blo 1144635 3875525 := bbase (se 4 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 3875525 = 726661) (by norm_num)
theorem B1450705 : Blo 1144635 1450705 := bbase (se 2 (by rfl) ⟨544014, by rfl⟩ : syracuseStep 1450705 = 1088029) (by norm_num)
theorem B8823509 : Blo 1144635 8823509 := bbase (se 7 (by rfl) ⟨103400, by rfl⟩ : syracuseStep 8823509 = 206801) (by norm_num)
theorem B1549037 : Blo 1144635 1549037 := bbase (se 3 (by rfl) ⟨290444, by rfl⟩ : syracuseStep 1549037 = 580889) (by norm_num)
theorem B1450801 : Blo 1144635 1450801 := bbase (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) (by norm_num)
theorem B24814421 : Blo 1144635 24814421 := bbase (se 9 (by rfl) ⟨72698, by rfl⟩ : syracuseStep 24814421 = 145397) (by norm_num)
theorem B1450973 : Blo 1144635 1450973 := bbase (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) (by norm_num)
theorem B5809157 : Blo 1144635 5809157 := bbase (se 4 (by rfl) ⟨544608, by rfl⟩ : syracuseStep 5809157 = 1089217) (by norm_num)
theorem B1451029 : Blo 1144635 1451029 := bbase (se 6 (by rfl) ⟨34008, by rfl⟩ : syracuseStep 1451029 = 68017) (by norm_num)
theorem B1451125 : Blo 1144635 1451125 := bbase (se 5 (by rfl) ⟨68021, by rfl⟩ : syracuseStep 1451125 = 136043) (by norm_num)
theorem B3875957 : Blo 1144635 3875957 := bbase (se 5 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 3875957 = 363371) (by norm_num)
theorem B4891909 : Blo 1144635 4891909 := bbase (se 4 (by rfl) ⟨458616, by rfl⟩ : syracuseStep 4891909 = 917233) (by norm_num)
theorem B1451297 : Blo 1144635 1451297 := bbase (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) (by norm_num)
theorem B8267093 : Blo 1144635 8267093 := bbase (se 12 (by rfl) ⟨3027, by rfl⟩ : syracuseStep 8267093 = 6055) (by norm_num)
theorem B1451353 : Blo 1144635 1451353 := bbase (se 2 (by rfl) ⟨544257, by rfl⟩ : syracuseStep 1451353 = 1088515) (by norm_num)
theorem B1746269 : Blo 1144635 1746269 := bbase (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) (by norm_num)
theorem B1451449 : Blo 1144635 1451449 := bbase (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) (by norm_num)
theorem B1746365 : Blo 1144635 1746365 := bbase (se 3 (by rfl) ⟨327443, by rfl⟩ : syracuseStep 1746365 = 654887) (by norm_num)
theorem B3876389 : Blo 1144635 3876389 := bbase (se 4 (by rfl) ⟨363411, by rfl⟩ : syracuseStep 3876389 = 726823) (by norm_num)
theorem B1287733 : Blo 1144635 1287733 := bbase (se 5 (by rfl) ⟨60362, by rfl⟩ : syracuseStep 1287733 = 120725) (by norm_num)
theorem B1287769 : Blo 1144635 1287769 := bbase (se 2 (by rfl) ⟨482913, by rfl⟩ : syracuseStep 1287769 = 965827) (by norm_num)
theorem B1451621 : Blo 1144635 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B3483253 : Blo 1144635 3483253 := bbase (se 5 (by rfl) ⟨163277, by rfl⟩ : syracuseStep 3483253 = 326555) (by norm_num)
theorem B1287805 : Blo 1144635 1287805 := bbase (se 3 (by rfl) ⟨241463, by rfl⟩ : syracuseStep 1287805 = 482927) (by norm_num)
theorem B1451677 : Blo 1144635 1451677 := bbase (se 3 (by rfl) ⟨272189, by rfl⟩ : syracuseStep 1451677 = 544379) (by norm_num)
theorem B1287841 : Blo 1144635 1287841 := bbase (se 2 (by rfl) ⟨482940, by rfl⟩ : syracuseStep 1287841 = 965881) (by norm_num)
theorem B1222337 : Blo 1144635 1222337 := bbase (se 2 (by rfl) ⟨458376, by rfl⟩ : syracuseStep 1222337 = 916753) (by norm_num)
theorem B1287877 : Blo 1144635 1287877 := bbase (se 4 (by rfl) ⟨120738, by rfl⟩ : syracuseStep 1287877 = 241477) (by norm_num)
theorem B1287913 : Blo 1144635 1287913 := bbase (se 2 (by rfl) ⟨482967, by rfl⟩ : syracuseStep 1287913 = 965935) (by norm_num)
theorem B1451773 : Blo 1144635 1451773 := bbase (se 3 (by rfl) ⟨272207, by rfl⟩ : syracuseStep 1451773 = 544415) (by norm_num)
theorem B1287949 : Blo 1144635 1287949 := bbase (se 3 (by rfl) ⟨241490, by rfl⟩ : syracuseStep 1287949 = 482981) (by norm_num)
theorem B1287985 : Blo 1144635 1287985 := bbase (se 2 (by rfl) ⟨482994, by rfl⟩ : syracuseStep 1287985 = 965989) (by norm_num)
theorem B1288021 : Blo 1144635 1288021 := bbase (se 9 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 1288021 = 7547) (by norm_num)
theorem B1288057 : Blo 1144635 1288057 := bbase (se 2 (by rfl) ⟨483021, by rfl⟩ : syracuseStep 1288057 = 966043) (by norm_num)
theorem B1288093 : Blo 1144635 1288093 := bbase (se 3 (by rfl) ⟨241517, by rfl⟩ : syracuseStep 1288093 = 483035) (by norm_num)
theorem B1451945 : Blo 1144635 1451945 := bbase (se 2 (by rfl) ⟨544479, by rfl⟩ : syracuseStep 1451945 = 1088959) (by norm_num)
theorem B1288129 : Blo 1144635 1288129 := bbase (se 2 (by rfl) ⟨483048, by rfl⟩ : syracuseStep 1288129 = 966097) (by norm_num)
theorem B1452001 : Blo 1144635 1452001 := bbase (se 2 (by rfl) ⟨544500, by rfl⟩ : syracuseStep 1452001 = 1089001) (by norm_num)
theorem B1288165 : Blo 1144635 1288165 := bbase (se 4 (by rfl) ⟨120765, by rfl⟩ : syracuseStep 1288165 = 241531) (by norm_num)
theorem B1288201 : Blo 1144635 1288201 := bbase (se 2 (by rfl) ⟨483075, by rfl⟩ : syracuseStep 1288201 = 966151) (by norm_num)
theorem B1288237 : Blo 1144635 1288237 := bbase (se 3 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 1288237 = 483089) (by norm_num)
theorem B1452097 : Blo 1144635 1452097 := bbase (se 2 (by rfl) ⟨544536, by rfl⟩ : syracuseStep 1452097 = 1089073) (by norm_num)
theorem B1288273 : Blo 1144635 1288273 := bbase (se 2 (by rfl) ⟨483102, by rfl⟩ : syracuseStep 1288273 = 966205) (by norm_num)
theorem B1288309 : Blo 1144635 1288309 := bbase (se 5 (by rfl) ⟨60389, by rfl⟩ : syracuseStep 1288309 = 120779) (by norm_num)
theorem B1222781 : Blo 1144635 1222781 := bbase (se 3 (by rfl) ⟨229271, by rfl⟩ : syracuseStep 1222781 = 458543) (by norm_num)
theorem B1288345 : Blo 1144635 1288345 := bbase (se 2 (by rfl) ⟨483129, by rfl⟩ : syracuseStep 1288345 = 966259) (by norm_num)
theorem B1288381 : Blo 1144635 1288381 := bbase (se 3 (by rfl) ⟨241571, by rfl⟩ : syracuseStep 1288381 = 483143) (by norm_num)
theorem B1288417 : Blo 1144635 1288417 := bbase (se 2 (by rfl) ⟨483156, by rfl⟩ : syracuseStep 1288417 = 966313) (by norm_num)
theorem B1452269 : Blo 1144635 1452269 := bbase (se 3 (by rfl) ⟨272300, by rfl⟩ : syracuseStep 1452269 = 544601) (by norm_num)
theorem B1288453 : Blo 1144635 1288453 := bbase (se 4 (by rfl) ⟨120792, by rfl⟩ : syracuseStep 1288453 = 241585) (by norm_num)
theorem B5810453 : Blo 1144635 5810453 := bbase (se 6 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 5810453 = 272365) (by norm_num)
theorem B1452325 : Blo 1144635 1452325 := bbase (se 4 (by rfl) ⟨136155, by rfl⟩ : syracuseStep 1452325 = 272311) (by norm_num)
theorem B1288489 : Blo 1144635 1288489 := bbase (se 2 (by rfl) ⟨483183, by rfl⟩ : syracuseStep 1288489 = 966367) (by norm_num)
theorem B1288525 : Blo 1144635 1288525 := bbase (se 3 (by rfl) ⟨241598, by rfl⟩ : syracuseStep 1288525 = 483197) (by norm_num)
theorem B1288561 : Blo 1144635 1288561 := bbase (se 2 (by rfl) ⟨483210, by rfl⟩ : syracuseStep 1288561 = 966421) (by norm_num)
theorem B2173301 : Blo 1144635 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B1223029 : Blo 1144635 1223029 := bbase (se 5 (by rfl) ⟨57329, by rfl⟩ : syracuseStep 1223029 = 114659) (by norm_num)
theorem B1452421 : Blo 1144635 1452421 := bbase (se 4 (by rfl) ⟨136164, by rfl⟩ : syracuseStep 1452421 = 272329) (by norm_num)
theorem B1288597 : Blo 1144635 1288597 := bbase (se 6 (by rfl) ⟨30201, by rfl⟩ : syracuseStep 1288597 = 60403) (by norm_num)
theorem B1288633 : Blo 1144635 1288633 := bbase (se 2 (by rfl) ⟨483237, by rfl⟩ : syracuseStep 1288633 = 966475) (by norm_num)
theorem B10463701 : Blo 1144635 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B1288669 : Blo 1144635 1288669 := bbase (se 3 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 1288669 = 483251) (by norm_num)
theorem B1288705 : Blo 1144635 1288705 := bbase (se 2 (by rfl) ⟨483264, by rfl⟩ : syracuseStep 1288705 = 966529) (by norm_num)
theorem B1288741 : Blo 1144635 1288741 := bbase (se 4 (by rfl) ⟨120819, by rfl⟩ : syracuseStep 1288741 = 241639) (by norm_num)
theorem B1452593 : Blo 1144635 1452593 := bbase (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) (by norm_num)
theorem B1288777 : Blo 1144635 1288777 := bbase (se 2 (by rfl) ⟨483291, by rfl⟩ : syracuseStep 1288777 = 966583) (by norm_num)
theorem B1452649 : Blo 1144635 1452649 := bbase (se 2 (by rfl) ⟨544743, by rfl⟩ : syracuseStep 1452649 = 1089487) (by norm_num)
theorem B1288813 : Blo 1144635 1288813 := bbase (se 3 (by rfl) ⟨241652, by rfl⟩ : syracuseStep 1288813 = 483305) (by norm_num)
theorem B1288849 : Blo 1144635 1288849 := bbase (se 2 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 1288849 = 966637) (by norm_num)
theorem B1288885 : Blo 1144635 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B1452745 : Blo 1144635 1452745 := bbase (se 2 (by rfl) ⟨544779, by rfl⟩ : syracuseStep 1452745 = 1089559) (by norm_num)
theorem B1551053 : Blo 1144635 1551053 := bbase (se 3 (by rfl) ⟨290822, by rfl⟩ : syracuseStep 1551053 = 581645) (by norm_num)
theorem B1288921 : Blo 1144635 1288921 := bbase (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) (by norm_num)
theorem B1288957 : Blo 1144635 1288957 := bbase (se 3 (by rfl) ⟨241679, by rfl⟩ : syracuseStep 1288957 = 483359) (by norm_num)
theorem B1288993 : Blo 1144635 1288993 := bbase (se 2 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 1288993 = 966745) (by norm_num)
theorem B1223473 : Blo 1144635 1223473 := bbase (se 2 (by rfl) ⟨458802, by rfl⟩ : syracuseStep 1223473 = 917605) (by norm_num)
theorem B1289029 : Blo 1144635 1289029 := bbase (se 4 (by rfl) ⟨120846, by rfl⟩ : syracuseStep 1289029 = 241693) (by norm_num)
theorem B1289065 : Blo 1144635 1289065 := bbase (se 2 (by rfl) ⟨483399, by rfl⟩ : syracuseStep 1289065 = 966799) (by norm_num)
theorem B1223533 : Blo 1144635 1223533 := bbase (se 3 (by rfl) ⟨229412, by rfl⟩ : syracuseStep 1223533 = 458825) (by norm_num)
theorem B1452917 : Blo 1144635 1452917 := bbase (se 5 (by rfl) ⟨68105, by rfl⟩ : syracuseStep 1452917 = 136211) (by norm_num)
theorem B1289101 : Blo 1144635 1289101 := bbase (se 3 (by rfl) ⟨241706, by rfl⟩ : syracuseStep 1289101 = 483413) (by norm_num)
theorem B1452973 : Blo 1144635 1452973 := bbase (se 3 (by rfl) ⟨272432, by rfl⟩ : syracuseStep 1452973 = 544865) (by norm_num)
theorem B1289137 : Blo 1144635 1289137 := bbase (se 2 (by rfl) ⟨483426, by rfl⟩ : syracuseStep 1289137 = 966853) (by norm_num)
theorem B1289173 : Blo 1144635 1289173 := bbase (se 7 (by rfl) ⟨15107, by rfl⟩ : syracuseStep 1289173 = 30215) (by norm_num)
theorem B1289209 : Blo 1144635 1289209 := bbase (se 2 (by rfl) ⟨483453, by rfl⟩ : syracuseStep 1289209 = 966907) (by norm_num)
theorem B1453069 : Blo 1144635 1453069 := bbase (se 3 (by rfl) ⟨272450, by rfl⟩ : syracuseStep 1453069 = 544901) (by norm_num)
theorem B1289245 : Blo 1144635 1289245 := bbase (se 3 (by rfl) ⟨241733, by rfl⟩ : syracuseStep 1289245 = 483467) (by norm_num)
theorem B1289281 : Blo 1144635 1289281 := bbase (se 2 (by rfl) ⟨483480, by rfl⟩ : syracuseStep 1289281 = 966961) (by norm_num)
theorem B7842901 : Blo 1144635 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B2174053 : Blo 1144635 2174053 := bbase (se 4 (by rfl) ⟨203817, by rfl⟩ : syracuseStep 2174053 = 407635) (by norm_num)
theorem B1289317 : Blo 1144635 1289317 := bbase (se 4 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 1289317 = 241747) (by norm_num)
theorem B1289353 : Blo 1144635 1289353 := bbase (se 2 (by rfl) ⟨483507, by rfl⟩ : syracuseStep 1289353 = 967015) (by norm_num)
theorem B1223849 : Blo 1144635 1223849 := bbase (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) (by norm_num)
theorem B1289389 : Blo 1144635 1289389 := bbase (se 3 (by rfl) ⟨241760, by rfl⟩ : syracuseStep 1289389 = 483521) (by norm_num)
theorem B2796725 : Blo 1144635 2796725 := bbase (se 5 (by rfl) ⟨131096, by rfl⟩ : syracuseStep 2796725 = 262193) (by norm_num)
theorem B1453241 : Blo 1144635 1453241 := bbase (se 2 (by rfl) ⟨544965, by rfl⟩ : syracuseStep 1453241 = 1089931) (by norm_num)
theorem B1289425 : Blo 1144635 1289425 := bbase (se 2 (by rfl) ⟨483534, by rfl⟩ : syracuseStep 1289425 = 967069) (by norm_num)
theorem B1453297 : Blo 1144635 1453297 := bbase (se 2 (by rfl) ⟨544986, by rfl⟩ : syracuseStep 1453297 = 1089973) (by norm_num)
theorem B2174197 : Blo 1144635 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B1289461 : Blo 1144635 1289461 := bbase (se 5 (by rfl) ⟨60443, by rfl⟩ : syracuseStep 1289461 = 120887) (by norm_num)
theorem B1551637 : Blo 1144635 1551637 := bbase (se 6 (by rfl) ⟨36366, by rfl⟩ : syracuseStep 1551637 = 72733) (by norm_num)
theorem B1289497 : Blo 1144635 1289497 := bbase (se 2 (by rfl) ⟨483561, by rfl⟩ : syracuseStep 1289497 = 967123) (by norm_num)
theorem B3484981 : Blo 1144635 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B1289533 : Blo 1144635 1289533 := bbase (se 3 (by rfl) ⟨241787, by rfl⟩ : syracuseStep 1289533 = 483575) (by norm_num)
theorem B1453393 : Blo 1144635 1453393 := bbase (se 2 (by rfl) ⟨545022, by rfl⟩ : syracuseStep 1453393 = 1090045) (by norm_num)
theorem B1289569 : Blo 1144635 1289569 := bbase (se 2 (by rfl) ⟨483588, by rfl⟩ : syracuseStep 1289569 = 967177) (by norm_num)
theorem B1289605 : Blo 1144635 1289605 := bbase (se 4 (by rfl) ⟨120900, by rfl⟩ : syracuseStep 1289605 = 241801) (by norm_num)
theorem B2174357 : Blo 1144635 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B1289641 : Blo 1144635 1289641 := bbase (se 2 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 1289641 = 967231) (by norm_num)
theorem B1289677 : Blo 1144635 1289677 := bbase (se 3 (by rfl) ⟨241814, by rfl⟩ : syracuseStep 1289677 = 483629) (by norm_num)
theorem B1289713 : Blo 1144635 1289713 := bbase (se 2 (by rfl) ⟨483642, by rfl⟩ : syracuseStep 1289713 = 967285) (by norm_num)
theorem B1453565 : Blo 1144635 1453565 := bbase (se 3 (by rfl) ⟨272543, by rfl⟩ : syracuseStep 1453565 = 545087) (by norm_num)
theorem B1289749 : Blo 1144635 1289749 := bbase (se 6 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 1289749 = 60457) (by norm_num)
theorem B2174501 : Blo 1144635 2174501 := bbase (se 4 (by rfl) ⟨203859, by rfl⟩ : syracuseStep 2174501 = 407719) (by norm_num)
theorem B5811749 : Blo 1144635 5811749 := bbase (se 4 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 5811749 = 1089703) (by norm_num)
theorem B1453621 : Blo 1144635 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B1289785 : Blo 1144635 1289785 := bbase (se 2 (by rfl) ⟨483669, by rfl⟩ : syracuseStep 1289785 = 967339) (by norm_num)
theorem B1289821 : Blo 1144635 1289821 := bbase (se 3 (by rfl) ⟨241841, by rfl⟩ : syracuseStep 1289821 = 483683) (by norm_num)
theorem B1224293 : Blo 1144635 1224293 := bbase (se 4 (by rfl) ⟨114777, by rfl⟩ : syracuseStep 1224293 = 229555) (by norm_num)
theorem B1289857 : Blo 1144635 1289857 := bbase (se 2 (by rfl) ⟨483696, by rfl⟩ : syracuseStep 1289857 = 967393) (by norm_num)
theorem B1453717 : Blo 1144635 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B1224353 : Blo 1144635 1224353 := bbase (se 2 (by rfl) ⟨459132, by rfl⟩ : syracuseStep 1224353 = 918265) (by norm_num)
theorem B1289893 : Blo 1144635 1289893 := bbase (se 4 (by rfl) ⟨120927, by rfl⟩ : syracuseStep 1289893 = 241855) (by norm_num)
theorem B1289929 : Blo 1144635 1289929 := bbase (se 2 (by rfl) ⟨483723, by rfl⟩ : syracuseStep 1289929 = 967447) (by norm_num)
theorem B1289965 : Blo 1144635 1289965 := bbase (se 3 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 1289965 = 483737) (by norm_num)
theorem B1290001 : Blo 1144635 1290001 := bbase (se 2 (by rfl) ⟨483750, by rfl⟩ : syracuseStep 1290001 = 967501) (by norm_num)
theorem B1224481 : Blo 1144635 1224481 := bbase (se 2 (by rfl) ⟨459180, by rfl⟩ : syracuseStep 1224481 = 918361) (by norm_num)
theorem B1290037 : Blo 1144635 1290037 := bbase (se 5 (by rfl) ⟨60470, by rfl⟩ : syracuseStep 1290037 = 120941) (by norm_num)
theorem B2174789 : Blo 1144635 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B1290073 : Blo 1144635 1290073 := bbase (se 2 (by rfl) ⟨483777, by rfl⟩ : syracuseStep 1290073 = 967555) (by norm_num)
theorem B1290109 : Blo 1144635 1290109 := bbase (se 3 (by rfl) ⟨241895, by rfl⟩ : syracuseStep 1290109 = 483791) (by norm_num)
theorem B1290145 : Blo 1144635 1290145 := bbase (se 2 (by rfl) ⟨483804, by rfl⟩ : syracuseStep 1290145 = 967609) (by norm_num)
theorem B1290181 : Blo 1144635 1290181 := bbase (se 4 (by rfl) ⟨120954, by rfl⟩ : syracuseStep 1290181 = 241909) (by norm_num)
theorem B2174941 : Blo 1144635 2174941 := bbase (se 3 (by rfl) ⟨407801, by rfl⟩ : syracuseStep 2174941 = 815603) (by norm_num)
theorem B1290217 : Blo 1144635 1290217 := bbase (se 2 (by rfl) ⟨483831, by rfl⟩ : syracuseStep 1290217 = 967663) (by norm_num)
theorem B5451781 : Blo 1144635 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B1290253 : Blo 1144635 1290253 := bbase (se 3 (by rfl) ⟨241922, by rfl⟩ : syracuseStep 1290253 = 483845) (by norm_num)
theorem B1290289 : Blo 1144635 1290289 := bbase (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) (by norm_num)
theorem B1290325 : Blo 1144635 1290325 := bbase (se 8 (by rfl) ⟨7560, by rfl⟩ : syracuseStep 1290325 = 15121) (by norm_num)
theorem B1290361 : Blo 1144635 1290361 := bbase (se 2 (by rfl) ⟨483885, by rfl⟩ : syracuseStep 1290361 = 967771) (by norm_num)
theorem B1290397 : Blo 1144635 1290397 := bbase (se 3 (by rfl) ⟨241949, by rfl⟩ : syracuseStep 1290397 = 483899) (by norm_num)
theorem B4894901 : Blo 1144635 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B1290433 : Blo 1144635 1290433 := bbase (se 2 (by rfl) ⟨483912, by rfl⟩ : syracuseStep 1290433 = 967825) (by norm_num)
theorem B1224925 : Blo 1144635 1224925 := bbase (se 3 (by rfl) ⟨229673, by rfl⟩ : syracuseStep 1224925 = 459347) (by norm_num)
theorem B1290469 : Blo 1144635 1290469 := bbase (se 4 (by rfl) ⟨120981, by rfl⟩ : syracuseStep 1290469 = 241963) (by norm_num)
theorem B1290505 : Blo 1144635 1290505 := bbase (se 2 (by rfl) ⟨483939, by rfl⟩ : syracuseStep 1290505 = 967879) (by norm_num)
theorem B2175245 : Blo 1144635 2175245 := bbase (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) (by norm_num)
theorem B1290541 : Blo 1144635 1290541 := bbase (se 3 (by rfl) ⟨241976, by rfl⟩ : syracuseStep 1290541 = 483953) (by norm_num)
theorem B1290577 : Blo 1144635 1290577 := bbase (se 2 (by rfl) ⟨483966, by rfl⟩ : syracuseStep 1290577 = 967933) (by norm_num)
theorem B1225045 : Blo 1144635 1225045 := bbase (se 10 (by rfl) ⟨1794, by rfl⟩ : syracuseStep 1225045 = 3589) (by norm_num)
theorem B1290613 : Blo 1144635 1290613 := bbase (se 5 (by rfl) ⟨60497, by rfl⟩ : syracuseStep 1290613 = 120995) (by norm_num)
theorem B1290649 : Blo 1144635 1290649 := bbase (se 2 (by rfl) ⟨483993, by rfl⟩ : syracuseStep 1290649 = 967987) (by norm_num)
theorem B1290685 : Blo 1144635 1290685 := bbase (se 3 (by rfl) ⟨242003, by rfl⟩ : syracuseStep 1290685 = 484007) (by norm_num)
theorem B1290721 : Blo 1144635 1290721 := bbase (se 2 (by rfl) ⟨484020, by rfl⟩ : syracuseStep 1290721 = 968041) (by norm_num)
theorem B1290757 : Blo 1144635 1290757 := bbase (se 4 (by rfl) ⟨121008, by rfl⟩ : syracuseStep 1290757 = 242017) (by norm_num)
theorem B1290793 : Blo 1144635 1290793 := bbase (se 2 (by rfl) ⟨484047, by rfl⟩ : syracuseStep 1290793 = 968095) (by norm_num)
theorem B1290829 : Blo 1144635 1290829 := bbase (se 3 (by rfl) ⟨242030, by rfl⟩ : syracuseStep 1290829 = 484061) (by norm_num)
theorem B1225297 : Blo 1144635 1225297 := bbase (se 2 (by rfl) ⟨459486, by rfl⟩ : syracuseStep 1225297 = 918973) (by norm_num)
theorem B1225301 : Blo 1144635 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1290865 : Blo 1144635 1290865 := bbase (se 2 (by rfl) ⟨484074, by rfl⟩ : syracuseStep 1290865 = 968149) (by norm_num)
theorem B1290901 : Blo 1144635 1290901 := bbase (se 6 (by rfl) ⟨30255, by rfl⟩ : syracuseStep 1290901 = 60511) (by norm_num)
theorem B1290937 : Blo 1144635 1290937 := bbase (se 2 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 1290937 = 968203) (by norm_num)
theorem B1290973 : Blo 1144635 1290973 := bbase (se 3 (by rfl) ⟨242057, by rfl⟩ : syracuseStep 1290973 = 484115) (by norm_num)
theorem B1716965 : Blo 1144635 1716965 := bbase (se 4 (by rfl) ⟨160965, by rfl⟩ : syracuseStep 1716965 = 321931) (by norm_num)
theorem B1716989 : Blo 1144635 1716989 := bbase (se 3 (by rfl) ⟨321935, by rfl⟩ : syracuseStep 1716989 = 643871) (by norm_num)
theorem B1291009 : Blo 1144635 1291009 := bbase (se 2 (by rfl) ⟨484128, by rfl⟩ : syracuseStep 1291009 = 968257) (by norm_num)
theorem B1717013 : Blo 1144635 1717013 := bbase (se 6 (by rfl) ⟨40242, by rfl⟩ : syracuseStep 1717013 = 80485) (by norm_num)
theorem B1291045 : Blo 1144635 1291045 := bbase (se 4 (by rfl) ⟨121035, by rfl⟩ : syracuseStep 1291045 = 242071) (by norm_num)
theorem B1717037 : Blo 1144635 1717037 := bbase (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) (by norm_num)
theorem B5813045 : Blo 1144635 5813045 := bbase (se 5 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 5813045 = 544973) (by norm_num)
theorem B1717061 : Blo 1144635 1717061 := bbase (se 4 (by rfl) ⟨160974, by rfl⟩ : syracuseStep 1717061 = 321949) (by norm_num)
theorem B1291081 : Blo 1144635 1291081 := bbase (se 2 (by rfl) ⟨484155, by rfl⟩ : syracuseStep 1291081 = 968311) (by norm_num)
theorem B1717085 : Blo 1144635 1717085 := bbase (se 3 (by rfl) ⟨321953, by rfl⟩ : syracuseStep 1717085 = 643907) (by norm_num)
theorem B1291117 : Blo 1144635 1291117 := bbase (se 3 (by rfl) ⟨242084, by rfl⟩ : syracuseStep 1291117 = 484169) (by norm_num)
theorem B1717109 : Blo 1144635 1717109 := bbase (se 5 (by rfl) ⟨80489, by rfl⟩ : syracuseStep 1717109 = 160979) (by norm_num)
theorem B1717133 : Blo 1144635 1717133 := bbase (se 3 (by rfl) ⟨321962, by rfl⟩ : syracuseStep 1717133 = 643925) (by norm_num)
theorem B1291153 : Blo 1144635 1291153 := bbase (se 2 (by rfl) ⟨484182, by rfl⟩ : syracuseStep 1291153 = 968365) (by norm_num)
theorem B1717157 : Blo 1144635 1717157 := bbase (se 4 (by rfl) ⟨160983, by rfl⟩ : syracuseStep 1717157 = 321967) (by norm_num)
theorem B1291189 : Blo 1144635 1291189 := bbase (se 5 (by rfl) ⟨60524, by rfl⟩ : syracuseStep 1291189 = 121049) (by norm_num)
theorem B1717181 : Blo 1144635 1717181 := bbase (se 3 (by rfl) ⟨321971, by rfl⟩ : syracuseStep 1717181 = 643943) (by norm_num)
theorem B1717205 : Blo 1144635 1717205 := bbase (se 7 (by rfl) ⟨20123, by rfl⟩ : syracuseStep 1717205 = 40247) (by norm_num)
theorem B1291225 : Blo 1144635 1291225 := bbase (se 2 (by rfl) ⟨484209, by rfl⟩ : syracuseStep 1291225 = 968419) (by norm_num)
theorem B1717229 : Blo 1144635 1717229 := bbase (se 3 (by rfl) ⟨321980, by rfl⟩ : syracuseStep 1717229 = 643961) (by norm_num)
theorem B2175997 : Blo 1144635 2175997 := bbase (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) (by norm_num)
theorem B1291261 : Blo 1144635 1291261 := bbase (se 3 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 1291261 = 484223) (by norm_num)
theorem B1717253 : Blo 1144635 1717253 := bbase (se 4 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 1717253 = 321985) (by norm_num)
theorem B1717277 : Blo 1144635 1717277 := bbase (se 3 (by rfl) ⟨321989, by rfl⟩ : syracuseStep 1717277 = 643979) (by norm_num)
theorem B1291297 : Blo 1144635 1291297 := bbase (se 2 (by rfl) ⟨484236, by rfl⟩ : syracuseStep 1291297 = 968473) (by norm_num)
theorem B1717301 : Blo 1144635 1717301 := bbase (se 5 (by rfl) ⟨80498, by rfl⟩ : syracuseStep 1717301 = 160997) (by norm_num)
theorem B1291333 : Blo 1144635 1291333 := bbase (se 4 (by rfl) ⟨121062, by rfl⟩ : syracuseStep 1291333 = 242125) (by norm_num)
theorem B1717325 : Blo 1144635 1717325 := bbase (se 3 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 1717325 = 643997) (by norm_num)
theorem B1717349 : Blo 1144635 1717349 := bbase (se 4 (by rfl) ⟨161001, by rfl⟩ : syracuseStep 1717349 = 322003) (by norm_num)
theorem B1291369 : Blo 1144635 1291369 := bbase (se 2 (by rfl) ⟨484263, by rfl⟩ : syracuseStep 1291369 = 968527) (by norm_num)
theorem B1717373 : Blo 1144635 1717373 := bbase (se 3 (by rfl) ⟨322007, by rfl⟩ : syracuseStep 1717373 = 644015) (by norm_num)
theorem B5518469 : Blo 1144635 5518469 := bbase (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) (by norm_num)
theorem B1225865 : Blo 1144635 1225865 := bbase (se 2 (by rfl) ⟨459699, by rfl⟩ : syracuseStep 1225865 = 919399) (by norm_num)
theorem B2176141 : Blo 1144635 2176141 := bbase (se 3 (by rfl) ⟨408026, by rfl⟩ : syracuseStep 2176141 = 816053) (by norm_num)
theorem B1291405 : Blo 1144635 1291405 := bbase (se 3 (by rfl) ⟨242138, by rfl⟩ : syracuseStep 1291405 = 484277) (by norm_num)
theorem B1717397 : Blo 1144635 1717397 := bbase (se 6 (by rfl) ⟨40251, by rfl⟩ : syracuseStep 1717397 = 80503) (by norm_num)
theorem B4895909 : Blo 1144635 4895909 := bbase (se 4 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 4895909 = 917983) (by norm_num)
theorem B1717421 : Blo 1144635 1717421 := bbase (se 3 (by rfl) ⟨322016, by rfl⟩ : syracuseStep 1717421 = 644033) (by norm_num)
theorem B1291441 : Blo 1144635 1291441 := bbase (se 2 (by rfl) ⟨484290, by rfl⟩ : syracuseStep 1291441 = 968581) (by norm_num)
theorem B1717445 : Blo 1144635 1717445 := bbase (se 4 (by rfl) ⟨161010, by rfl⟩ : syracuseStep 1717445 = 322021) (by norm_num)
theorem B1291477 : Blo 1144635 1291477 := bbase (se 7 (by rfl) ⟨15134, by rfl⟩ : syracuseStep 1291477 = 30269) (by norm_num)
theorem B1717469 : Blo 1144635 1717469 := bbase (se 3 (by rfl) ⟨322025, by rfl⟩ : syracuseStep 1717469 = 644051) (by norm_num)
theorem B1717493 : Blo 1144635 1717493 := bbase (se 5 (by rfl) ⟨80507, by rfl⟩ : syracuseStep 1717493 = 161015) (by norm_num)
theorem B1291513 : Blo 1144635 1291513 := bbase (se 2 (by rfl) ⟨484317, by rfl⟩ : syracuseStep 1291513 = 968635) (by norm_num)
theorem B1717517 : Blo 1144635 1717517 := bbase (se 3 (by rfl) ⟨322034, by rfl⟩ : syracuseStep 1717517 = 644069) (by norm_num)
theorem B1291549 : Blo 1144635 1291549 := bbase (se 3 (by rfl) ⟨242165, by rfl⟩ : syracuseStep 1291549 = 484331) (by norm_num)
theorem B1717541 : Blo 1144635 1717541 := bbase (se 4 (by rfl) ⟨161019, by rfl⟩ : syracuseStep 1717541 = 322039) (by norm_num)
theorem B2176301 : Blo 1144635 2176301 := bbase (se 3 (by rfl) ⟨408056, by rfl⟩ : syracuseStep 2176301 = 816113) (by norm_num)
theorem B1717565 : Blo 1144635 1717565 := bbase (se 3 (by rfl) ⟨322043, by rfl⟩ : syracuseStep 1717565 = 644087) (by norm_num)
theorem B1291585 : Blo 1144635 1291585 := bbase (se 2 (by rfl) ⟨484344, by rfl⟩ : syracuseStep 1291585 = 968689) (by norm_num)
theorem B1226053 : Blo 1144635 1226053 := bbase (se 4 (by rfl) ⟨114942, by rfl⟩ : syracuseStep 1226053 = 229885) (by norm_num)
theorem B1717589 : Blo 1144635 1717589 := bbase (se 13 (by rfl) ⟨314, by rfl⟩ : syracuseStep 1717589 = 629) (by norm_num)
theorem B1291621 : Blo 1144635 1291621 := bbase (se 4 (by rfl) ⟨121089, by rfl⟩ : syracuseStep 1291621 = 242179) (by norm_num)
theorem B1717613 : Blo 1144635 1717613 := bbase (se 3 (by rfl) ⟨322052, by rfl⟩ : syracuseStep 1717613 = 644105) (by norm_num)
theorem B1717637 : Blo 1144635 1717637 := bbase (se 4 (by rfl) ⟨161028, by rfl⟩ : syracuseStep 1717637 = 322057) (by norm_num)
theorem B1291657 : Blo 1144635 1291657 := bbase (se 2 (by rfl) ⟨484371, by rfl⟩ : syracuseStep 1291657 = 968743) (by norm_num)
theorem B1717661 : Blo 1144635 1717661 := bbase (se 3 (by rfl) ⟨322061, by rfl⟩ : syracuseStep 1717661 = 644123) (by norm_num)
theorem B1291693 : Blo 1144635 1291693 := bbase (se 3 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 1291693 = 484385) (by norm_num)
theorem B1717685 : Blo 1144635 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B2176445 : Blo 1144635 2176445 := bbase (se 3 (by rfl) ⟨408083, by rfl⟩ : syracuseStep 2176445 = 816167) (by norm_num)
theorem B1717709 : Blo 1144635 1717709 := bbase (se 3 (by rfl) ⟨322070, by rfl⟩ : syracuseStep 1717709 = 644141) (by norm_num)
theorem B1291729 : Blo 1144635 1291729 := bbase (se 2 (by rfl) ⟨484398, by rfl⟩ : syracuseStep 1291729 = 968797) (by norm_num)
theorem B1717733 : Blo 1144635 1717733 := bbase (se 4 (by rfl) ⟨161037, by rfl⟩ : syracuseStep 1717733 = 322075) (by norm_num)
theorem B1291765 : Blo 1144635 1291765 := bbase (se 5 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 1291765 = 121103) (by norm_num)
theorem B1717757 : Blo 1144635 1717757 := bbase (se 3 (by rfl) ⟨322079, by rfl⟩ : syracuseStep 1717757 = 644159) (by norm_num)
theorem B1717781 : Blo 1144635 1717781 := bbase (se 6 (by rfl) ⟨40260, by rfl⟩ : syracuseStep 1717781 = 80521) (by norm_num)
theorem B1291801 : Blo 1144635 1291801 := bbase (se 2 (by rfl) ⟨484425, by rfl⟩ : syracuseStep 1291801 = 968851) (by norm_num)
theorem B1717805 : Blo 1144635 1717805 := bbase (se 3 (by rfl) ⟨322088, by rfl⟩ : syracuseStep 1717805 = 644177) (by norm_num)
theorem B1291837 : Blo 1144635 1291837 := bbase (se 3 (by rfl) ⟨242219, by rfl⟩ : syracuseStep 1291837 = 484439) (by norm_num)
theorem B1717829 : Blo 1144635 1717829 := bbase (se 4 (by rfl) ⟨161046, by rfl⟩ : syracuseStep 1717829 = 322093) (by norm_num)
theorem B1717853 : Blo 1144635 1717853 := bbase (se 3 (by rfl) ⟨322097, by rfl⟩ : syracuseStep 1717853 = 644195) (by norm_num)
theorem B1291873 : Blo 1144635 1291873 := bbase (se 2 (by rfl) ⟨484452, by rfl⟩ : syracuseStep 1291873 = 968905) (by norm_num)
theorem B1717877 : Blo 1144635 1717877 := bbase (se 5 (by rfl) ⟨80525, by rfl⟩ : syracuseStep 1717877 = 161051) (by norm_num)
theorem B1291909 : Blo 1144635 1291909 := bbase (se 4 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 1291909 = 242233) (by norm_num)
theorem B1717901 : Blo 1144635 1717901 := bbase (se 3 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 1717901 = 644213) (by norm_num)
theorem B1717925 : Blo 1144635 1717925 := bbase (se 4 (by rfl) ⟨161055, by rfl⟩ : syracuseStep 1717925 = 322111) (by norm_num)
theorem B1291945 : Blo 1144635 1291945 := bbase (se 2 (by rfl) ⟨484479, by rfl⟩ : syracuseStep 1291945 = 968959) (by norm_num)
theorem B1717949 : Blo 1144635 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B1291981 : Blo 1144635 1291981 := bbase (se 3 (by rfl) ⟨242246, by rfl⟩ : syracuseStep 1291981 = 484493) (by norm_num)
theorem B1717973 : Blo 1144635 1717973 := bbase (se 7 (by rfl) ⟨20132, by rfl⟩ : syracuseStep 1717973 = 40265) (by norm_num)
theorem B2176733 : Blo 1144635 2176733 := bbase (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) (by norm_num)
theorem B1717997 : Blo 1144635 1717997 := bbase (se 3 (by rfl) ⟨322124, by rfl⟩ : syracuseStep 1717997 = 644249) (by norm_num)
theorem B1292017 : Blo 1144635 1292017 := bbase (se 2 (by rfl) ⟨484506, by rfl⟩ : syracuseStep 1292017 = 969013) (by norm_num)
theorem B2897653 : Blo 1144635 2897653 := bbase (se 5 (by rfl) ⟨135827, by rfl⟩ : syracuseStep 2897653 = 271655) (by norm_num)
theorem B1718021 : Blo 1144635 1718021 := bbase (se 4 (by rfl) ⟨161064, by rfl⟩ : syracuseStep 1718021 = 322129) (by norm_num)
theorem B1292053 : Blo 1144635 1292053 := bbase (se 6 (by rfl) ⟨30282, by rfl⟩ : syracuseStep 1292053 = 60565) (by norm_num)
theorem B1718045 : Blo 1144635 1718045 := bbase (se 3 (by rfl) ⟨322133, by rfl⟩ : syracuseStep 1718045 = 644267) (by norm_num)
theorem B1718069 : Blo 1144635 1718069 := bbase (se 5 (by rfl) ⟨80534, by rfl⟩ : syracuseStep 1718069 = 161069) (by norm_num)
theorem B1292089 : Blo 1144635 1292089 := bbase (se 2 (by rfl) ⟨484533, by rfl⟩ : syracuseStep 1292089 = 969067) (by norm_num)
theorem B1718093 : Blo 1144635 1718093 := bbase (se 3 (by rfl) ⟨322142, by rfl⟩ : syracuseStep 1718093 = 644285) (by norm_num)
theorem B1292125 : Blo 1144635 1292125 := bbase (se 3 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 1292125 = 484547) (by norm_num)
theorem B2897765 : Blo 1144635 2897765 := bbase (se 4 (by rfl) ⟨271665, by rfl⟩ : syracuseStep 2897765 = 543331) (by norm_num)
theorem B1718117 : Blo 1144635 1718117 := bbase (se 4 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 1718117 = 322147) (by norm_num)
theorem B2176885 : Blo 1144635 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B1718141 : Blo 1144635 1718141 := bbase (se 3 (by rfl) ⟨322151, by rfl⟩ : syracuseStep 1718141 = 644303) (by norm_num)
theorem B1292161 : Blo 1144635 1292161 := bbase (se 2 (by rfl) ⟨484560, by rfl⟩ : syracuseStep 1292161 = 969121) (by norm_num)
theorem B1718165 : Blo 1144635 1718165 := bbase (se 6 (by rfl) ⟨40269, by rfl⟩ : syracuseStep 1718165 = 80539) (by norm_num)
theorem B1292197 : Blo 1144635 1292197 := bbase (se 4 (by rfl) ⟨121143, by rfl⟩ : syracuseStep 1292197 = 242287) (by norm_num)
theorem B1718189 : Blo 1144635 1718189 := bbase (se 3 (by rfl) ⟨322160, by rfl⟩ : syracuseStep 1718189 = 644321) (by norm_num)
theorem B1718213 : Blo 1144635 1718213 := bbase (se 4 (by rfl) ⟨161082, by rfl⟩ : syracuseStep 1718213 = 322165) (by norm_num)
theorem B1718237 : Blo 1144635 1718237 := bbase (se 3 (by rfl) ⟨322169, by rfl⟩ : syracuseStep 1718237 = 644339) (by norm_num)
theorem B1718261 : Blo 1144635 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B1718285 : Blo 1144635 1718285 := bbase (se 3 (by rfl) ⟨322178, by rfl⟩ : syracuseStep 1718285 = 644357) (by norm_num)
theorem B2897957 : Blo 1144635 2897957 := bbase (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) (by norm_num)
theorem B1718309 : Blo 1144635 1718309 := bbase (se 4 (by rfl) ⟨161091, by rfl⟩ : syracuseStep 1718309 = 322183) (by norm_num)
theorem B1718333 : Blo 1144635 1718333 := bbase (se 3 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 1718333 = 644375) (by norm_num)
theorem B5814341 : Blo 1144635 5814341 := bbase (se 4 (by rfl) ⟨545094, by rfl⟩ : syracuseStep 5814341 = 1090189) (by norm_num)
theorem B8697941 : Blo 1144635 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B1718357 : Blo 1144635 1718357 := bbase (se 8 (by rfl) ⟨10068, by rfl⟩ : syracuseStep 1718357 = 20137) (by norm_num)
theorem B1718381 : Blo 1144635 1718381 := bbase (se 3 (by rfl) ⟨322196, by rfl⟩ : syracuseStep 1718381 = 644393) (by norm_num)
theorem B1718405 : Blo 1144635 1718405 := bbase (se 4 (by rfl) ⟨161100, by rfl⟩ : syracuseStep 1718405 = 322201) (by norm_num)
theorem B1718429 : Blo 1144635 1718429 := bbase (se 3 (by rfl) ⟨322205, by rfl⟩ : syracuseStep 1718429 = 644411) (by norm_num)
theorem B2177189 : Blo 1144635 2177189 := bbase (se 4 (by rfl) ⟨204111, by rfl⟩ : syracuseStep 2177189 = 408223) (by norm_num)
theorem B1718453 : Blo 1144635 1718453 := bbase (se 5 (by rfl) ⟨80552, by rfl⟩ : syracuseStep 1718453 = 161105) (by norm_num)
theorem B6535349 : Blo 1144635 6535349 := bbase (se 5 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 6535349 = 612689) (by norm_num)
theorem B1718477 : Blo 1144635 1718477 := bbase (se 3 (by rfl) ⟨322214, by rfl⟩ : syracuseStep 1718477 = 644429) (by norm_num)
theorem B1161425 : Blo 1144635 1161425 := bbase (se 2 (by rfl) ⟨435534, by rfl⟩ : syracuseStep 1161425 = 871069) (by norm_num)
theorem B1718501 : Blo 1144635 1718501 := bbase (se 4 (by rfl) ⟨161109, by rfl⟩ : syracuseStep 1718501 = 322219) (by norm_num)
theorem B1718525 : Blo 1144635 1718525 := bbase (se 3 (by rfl) ⟨322223, by rfl⟩ : syracuseStep 1718525 = 644447) (by norm_num)
theorem B13220117 : Blo 1144635 13220117 := bbase (se 6 (by rfl) ⟨309846, by rfl⟩ : syracuseStep 13220117 = 619693) (by norm_num)
theorem B1718549 : Blo 1144635 1718549 := bbase (se 6 (by rfl) ⟨40278, by rfl⟩ : syracuseStep 1718549 = 80557) (by norm_num)
theorem B1718573 : Blo 1144635 1718573 := bbase (se 3 (by rfl) ⟨322232, by rfl⟩ : syracuseStep 1718573 = 644465) (by norm_num)
theorem B1718597 : Blo 1144635 1718597 := bbase (se 4 (by rfl) ⟨161118, by rfl⟩ : syracuseStep 1718597 = 322237) (by norm_num)
theorem B3488069 : Blo 1144635 3488069 := bbase (se 4 (by rfl) ⟨327006, by rfl⟩ : syracuseStep 3488069 = 654013) (by norm_num)
theorem B1718621 : Blo 1144635 1718621 := bbase (se 3 (by rfl) ⟨322241, by rfl⟩ : syracuseStep 1718621 = 644483) (by norm_num)
theorem B1718645 : Blo 1144635 1718645 := bbase (se 5 (by rfl) ⟨80561, by rfl⟩ : syracuseStep 1718645 = 161123) (by norm_num)
theorem B2898301 : Blo 1144635 2898301 := bbase (se 3 (by rfl) ⟨543431, by rfl⟩ : syracuseStep 2898301 = 1086863) (by norm_num)
theorem B1718669 : Blo 1144635 1718669 := bbase (se 3 (by rfl) ⟨322250, by rfl⟩ : syracuseStep 1718669 = 644501) (by norm_num)
theorem B1718693 : Blo 1144635 1718693 := bbase (se 4 (by rfl) ⟨161127, by rfl⟩ : syracuseStep 1718693 = 322255) (by norm_num)
theorem B1718717 : Blo 1144635 1718717 := bbase (se 3 (by rfl) ⟨322259, by rfl⟩ : syracuseStep 1718717 = 644519) (by norm_num)
theorem B1718741 : Blo 1144635 1718741 := bbase (se 7 (by rfl) ⟨20141, by rfl⟩ : syracuseStep 1718741 = 40283) (by norm_num)
theorem B2898413 : Blo 1144635 2898413 := bbase (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) (by norm_num)
theorem B1718765 : Blo 1144635 1718765 := bbase (se 3 (by rfl) ⟨322268, by rfl⟩ : syracuseStep 1718765 = 644537) (by norm_num)
theorem B1718789 : Blo 1144635 1718789 := bbase (se 4 (by rfl) ⟨161136, by rfl⟩ : syracuseStep 1718789 = 322273) (by norm_num)
theorem B1161733 : Blo 1144635 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B1718813 : Blo 1144635 1718813 := bbase (se 3 (by rfl) ⟨322277, by rfl⟩ : syracuseStep 1718813 = 644555) (by norm_num)
theorem B1718837 : Blo 1144635 1718837 := bbase (se 5 (by rfl) ⟨80570, by rfl⟩ : syracuseStep 1718837 = 161141) (by norm_num)
theorem B1718861 : Blo 1144635 1718861 := bbase (se 3 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 1718861 = 644573) (by norm_num)
theorem B1718885 : Blo 1144635 1718885 := bbase (se 4 (by rfl) ⟨161145, by rfl⟩ : syracuseStep 1718885 = 322291) (by norm_num)
theorem B11188853 : Blo 1144635 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B1718909 : Blo 1144635 1718909 := bbase (se 3 (by rfl) ⟨322295, by rfl⟩ : syracuseStep 1718909 = 644591) (by norm_num)
theorem B1718933 : Blo 1144635 1718933 := bbase (se 6 (by rfl) ⟨40287, by rfl⟩ : syracuseStep 1718933 = 80575) (by norm_num)
theorem B2898605 : Blo 1144635 2898605 := bbase (se 3 (by rfl) ⟨543488, by rfl⟩ : syracuseStep 2898605 = 1086977) (by norm_num)
theorem B1718957 : Blo 1144635 1718957 := bbase (se 3 (by rfl) ⟨322304, by rfl⟩ : syracuseStep 1718957 = 644609) (by norm_num)
theorem B1718981 : Blo 1144635 1718981 := bbase (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) (by norm_num)
theorem B1719005 : Blo 1144635 1719005 := bbase (se 3 (by rfl) ⟨322313, by rfl⟩ : syracuseStep 1719005 = 644627) (by norm_num)
theorem B1719029 : Blo 1144635 1719029 := bbase (se 5 (by rfl) ⟨80579, by rfl⟩ : syracuseStep 1719029 = 161159) (by norm_num)
theorem B1719053 : Blo 1144635 1719053 := bbase (se 3 (by rfl) ⟨322322, by rfl⟩ : syracuseStep 1719053 = 644645) (by norm_num)
theorem B1719077 : Blo 1144635 1719077 := bbase (se 4 (by rfl) ⟨161163, by rfl⟩ : syracuseStep 1719077 = 322327) (by norm_num)
theorem B1719101 : Blo 1144635 1719101 := bbase (se 3 (by rfl) ⟨322331, by rfl⟩ : syracuseStep 1719101 = 644663) (by norm_num)
theorem B1719125 : Blo 1144635 1719125 := bbase (se 9 (by rfl) ⟨5036, by rfl⟩ : syracuseStep 1719125 = 10073) (by norm_num)
theorem B1719149 : Blo 1144635 1719149 := bbase (se 3 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 1719149 = 644681) (by norm_num)
theorem B1719173 : Blo 1144635 1719173 := bbase (se 4 (by rfl) ⟨161172, by rfl⟩ : syracuseStep 1719173 = 322345) (by norm_num)
theorem B2177941 : Blo 1144635 2177941 := bbase (se 6 (by rfl) ⟨51045, by rfl⟩ : syracuseStep 2177941 = 102091) (by norm_num)
theorem B4897685 : Blo 1144635 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B1719197 : Blo 1144635 1719197 := bbase (se 3 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 1719197 = 644699) (by norm_num)
theorem B1719221 : Blo 1144635 1719221 := bbase (se 5 (by rfl) ⟨80588, by rfl⟩ : syracuseStep 1719221 = 161177) (by norm_num)
theorem B1719245 : Blo 1144635 1719245 := bbase (se 3 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 1719245 = 644717) (by norm_num)
theorem B1719269 : Blo 1144635 1719269 := bbase (se 4 (by rfl) ⟨161181, by rfl⟩ : syracuseStep 1719269 = 322363) (by norm_num)
theorem B1719293 : Blo 1144635 1719293 := bbase (se 3 (by rfl) ⟨322367, by rfl⟩ : syracuseStep 1719293 = 644735) (by norm_num)
theorem B2898949 : Blo 1144635 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B1719317 : Blo 1144635 1719317 := bbase (se 6 (by rfl) ⟨40296, by rfl⟩ : syracuseStep 1719317 = 80593) (by norm_num)
theorem B2178085 : Blo 1144635 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B1719341 : Blo 1144635 1719341 := bbase (se 3 (by rfl) ⟨322376, by rfl⟩ : syracuseStep 1719341 = 644753) (by norm_num)
theorem B1719365 : Blo 1144635 1719365 := bbase (se 4 (by rfl) ⟨161190, by rfl⟩ : syracuseStep 1719365 = 322381) (by norm_num)
theorem B15711317 : Blo 1144635 15711317 := bbase (se 8 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 15711317 = 184117) (by norm_num)
theorem B1719389 : Blo 1144635 1719389 := bbase (se 3 (by rfl) ⟨322385, by rfl⟩ : syracuseStep 1719389 = 644771) (by norm_num)
theorem B3095653 : Blo 1144635 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B2899061 : Blo 1144635 2899061 := bbase (se 5 (by rfl) ⟨135893, by rfl⟩ : syracuseStep 2899061 = 271787) (by norm_num)
theorem B1719413 : Blo 1144635 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B1719437 : Blo 1144635 1719437 := bbase (se 3 (by rfl) ⟨322394, by rfl⟩ : syracuseStep 1719437 = 644789) (by norm_num)
theorem B3259541 : Blo 1144635 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B11025557 : Blo 1144635 11025557 := bbase (se 6 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 11025557 = 516823) (by norm_num)
theorem B1719461 : Blo 1144635 1719461 := bbase (se 4 (by rfl) ⟨161199, by rfl⟩ : syracuseStep 1719461 = 322399) (by norm_num)
theorem B1719485 : Blo 1144635 1719485 := bbase (se 3 (by rfl) ⟨322403, by rfl⟩ : syracuseStep 1719485 = 644807) (by norm_num)
theorem B2178245 : Blo 1144635 2178245 := bbase (se 4 (by rfl) ⟨204210, by rfl⟩ : syracuseStep 2178245 = 408421) (by norm_num)
theorem B1719509 : Blo 1144635 1719509 := bbase (se 7 (by rfl) ⟨20150, by rfl⟩ : syracuseStep 1719509 = 40301) (by norm_num)
theorem B1719533 : Blo 1144635 1719533 := bbase (se 3 (by rfl) ⟨322412, by rfl⟩ : syracuseStep 1719533 = 644825) (by norm_num)
theorem B1719557 : Blo 1144635 1719557 := bbase (se 4 (by rfl) ⟨161208, by rfl⟩ : syracuseStep 1719557 = 322417) (by norm_num)
theorem B1719581 : Blo 1144635 1719581 := bbase (se 3 (by rfl) ⟨322421, by rfl⟩ : syracuseStep 1719581 = 644843) (by norm_num)
theorem B2899253 : Blo 1144635 2899253 := bbase (se 5 (by rfl) ⟨135902, by rfl⟩ : syracuseStep 2899253 = 271805) (by norm_num)
theorem B1719605 : Blo 1144635 1719605 := bbase (se 5 (by rfl) ⟨80606, by rfl⟩ : syracuseStep 1719605 = 161213) (by norm_num)
theorem B7355701 : Blo 1144635 7355701 := bbase (se 5 (by rfl) ⟨344798, by rfl⟩ : syracuseStep 7355701 = 689597) (by norm_num)
theorem B1719629 : Blo 1144635 1719629 := bbase (se 3 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 1719629 = 644861) (by norm_num)
theorem B2178389 : Blo 1144635 2178389 := bbase (se 11 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 2178389 = 3191) (by norm_num)
theorem B1719653 : Blo 1144635 1719653 := bbase (se 4 (by rfl) ⟨161217, by rfl⟩ : syracuseStep 1719653 = 322435) (by norm_num)
theorem B1719677 : Blo 1144635 1719677 := bbase (se 3 (by rfl) ⟨322439, by rfl⟩ : syracuseStep 1719677 = 644879) (by norm_num)
theorem B1719701 : Blo 1144635 1719701 := bbase (se 6 (by rfl) ⟨40305, by rfl⟩ : syracuseStep 1719701 = 80611) (by norm_num)
theorem B1719725 : Blo 1144635 1719725 := bbase (se 3 (by rfl) ⟨322448, by rfl⟩ : syracuseStep 1719725 = 644897) (by norm_num)
theorem B1719749 : Blo 1144635 1719749 := bbase (se 4 (by rfl) ⟨161226, by rfl⟩ : syracuseStep 1719749 = 322453) (by norm_num)
theorem B1719773 : Blo 1144635 1719773 := bbase (se 3 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 1719773 = 644915) (by norm_num)
theorem B3096053 : Blo 1144635 3096053 := bbase (se 5 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 3096053 = 290255) (by norm_num)
theorem B1719797 : Blo 1144635 1719797 := bbase (se 5 (by rfl) ⟨80615, by rfl⟩ : syracuseStep 1719797 = 161231) (by norm_num)
theorem B1719821 : Blo 1144635 1719821 := bbase (se 3 (by rfl) ⟨322466, by rfl⟩ : syracuseStep 1719821 = 644933) (by norm_num)
theorem B1719845 : Blo 1144635 1719845 := bbase (se 4 (by rfl) ⟨161235, by rfl⟩ : syracuseStep 1719845 = 322471) (by norm_num)
theorem B1719869 : Blo 1144635 1719869 := bbase (se 3 (by rfl) ⟨322475, by rfl⟩ : syracuseStep 1719869 = 644951) (by norm_num)
theorem B1719893 : Blo 1144635 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B1719917 : Blo 1144635 1719917 := bbase (se 3 (by rfl) ⟨322484, by rfl⟩ : syracuseStep 1719917 = 644969) (by norm_num)
theorem B2178677 : Blo 1144635 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B6209141 : Blo 1144635 6209141 := bbase (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) (by norm_num)
theorem B1719941 : Blo 1144635 1719941 := bbase (se 4 (by rfl) ⟨161244, by rfl⟩ : syracuseStep 1719941 = 322489) (by norm_num)
theorem B2899597 : Blo 1144635 2899597 := bbase (se 3 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 2899597 = 1087349) (by norm_num)
theorem B1719965 : Blo 1144635 1719965 := bbase (se 3 (by rfl) ⟨322493, by rfl⟩ : syracuseStep 1719965 = 644987) (by norm_num)
theorem B1719989 : Blo 1144635 1719989 := bbase (se 5 (by rfl) ⟨80624, by rfl⟩ : syracuseStep 1719989 = 161249) (by norm_num)
theorem B1720013 : Blo 1144635 1720013 := bbase (se 3 (by rfl) ⟨322502, by rfl⟩ : syracuseStep 1720013 = 645005) (by norm_num)
theorem B1654501 : Blo 1144635 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B1720037 : Blo 1144635 1720037 := bbase (se 4 (by rfl) ⟨161253, by rfl⟩ : syracuseStep 1720037 = 322507) (by norm_num)
theorem B2899709 : Blo 1144635 2899709 := bbase (se 3 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 2899709 = 1087391) (by norm_num)
theorem B1720061 : Blo 1144635 1720061 := bbase (se 3 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 1720061 = 645023) (by norm_num)
theorem B2178829 : Blo 1144635 2178829 := bbase (se 3 (by rfl) ⟨408530, by rfl⟩ : syracuseStep 2178829 = 817061) (by norm_num)
theorem B1720085 : Blo 1144635 1720085 := bbase (se 6 (by rfl) ⟨40314, by rfl⟩ : syracuseStep 1720085 = 80629) (by norm_num)
theorem B1720109 : Blo 1144635 1720109 := bbase (se 3 (by rfl) ⟨322520, by rfl⟩ : syracuseStep 1720109 = 645041) (by norm_num)
theorem B1720133 : Blo 1144635 1720133 := bbase (se 4 (by rfl) ⟨161262, by rfl⟩ : syracuseStep 1720133 = 322525) (by norm_num)
theorem B3358549 : Blo 1144635 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B1720157 : Blo 1144635 1720157 := bbase (se 3 (by rfl) ⟨322529, by rfl⟩ : syracuseStep 1720157 = 645059) (by norm_num)
theorem B1720181 : Blo 1144635 1720181 := bbase (se 5 (by rfl) ⟨80633, by rfl⟩ : syracuseStep 1720181 = 161267) (by norm_num)
theorem B1720205 : Blo 1144635 1720205 := bbase (se 3 (by rfl) ⟨322538, by rfl⟩ : syracuseStep 1720205 = 645077) (by norm_num)
theorem B3096485 : Blo 1144635 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B1720229 : Blo 1144635 1720229 := bbase (se 4 (by rfl) ⟨161271, by rfl⟩ : syracuseStep 1720229 = 322543) (by norm_num)
theorem B2899901 : Blo 1144635 2899901 := bbase (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) (by norm_num)
theorem B1720253 : Blo 1144635 1720253 := bbase (se 3 (by rfl) ⟨322547, by rfl⟩ : syracuseStep 1720253 = 645095) (by norm_num)
theorem B1163209 : Blo 1144635 1163209 := bbase (se 2 (by rfl) ⟨436203, by rfl⟩ : syracuseStep 1163209 = 872407) (by norm_num)
theorem B1720277 : Blo 1144635 1720277 := bbase (se 7 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 1720277 = 40319) (by norm_num)
theorem B1720301 : Blo 1144635 1720301 := bbase (se 3 (by rfl) ⟨322556, by rfl⟩ : syracuseStep 1720301 = 645113) (by norm_num)
theorem B1720325 : Blo 1144635 1720325 := bbase (se 4 (by rfl) ⟨161280, by rfl⟩ : syracuseStep 1720325 = 322561) (by norm_num)
theorem B1720349 : Blo 1144635 1720349 := bbase (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) (by norm_num)
theorem B3096613 : Blo 1144635 3096613 := bbase (se 4 (by rfl) ⟨290307, by rfl⟩ : syracuseStep 3096613 = 580615) (by norm_num)
theorem B1720373 : Blo 1144635 1720373 := bbase (se 5 (by rfl) ⟨80642, by rfl⟩ : syracuseStep 1720373 = 161285) (by norm_num)
theorem B2179133 : Blo 1144635 2179133 := bbase (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) (by norm_num)
theorem B1720397 : Blo 1144635 1720397 := bbase (se 3 (by rfl) ⟨322574, by rfl⟩ : syracuseStep 1720397 = 645149) (by norm_num)
theorem B1720421 : Blo 1144635 1720421 := bbase (se 4 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 1720421 = 322579) (by norm_num)
theorem B3260533 : Blo 1144635 3260533 := bbase (se 5 (by rfl) ⟨152837, by rfl⟩ : syracuseStep 3260533 = 305675) (by norm_num)
theorem B1720445 : Blo 1144635 1720445 := bbase (se 3 (by rfl) ⟨322583, by rfl⟩ : syracuseStep 1720445 = 645167) (by norm_num)
theorem B1720469 : Blo 1144635 1720469 := bbase (se 6 (by rfl) ⟨40323, by rfl⟩ : syracuseStep 1720469 = 80647) (by norm_num)
theorem B1720493 : Blo 1144635 1720493 := bbase (se 3 (by rfl) ⟨322592, by rfl⟩ : syracuseStep 1720493 = 645185) (by norm_num)
theorem B1720517 : Blo 1144635 1720517 := bbase (se 4 (by rfl) ⟨161298, by rfl⟩ : syracuseStep 1720517 = 322597) (by norm_num)
theorem B1720541 : Blo 1144635 1720541 := bbase (se 3 (by rfl) ⟨322601, by rfl⟩ : syracuseStep 1720541 = 645203) (by norm_num)
theorem B1720565 : Blo 1144635 1720565 := bbase (se 5 (by rfl) ⟨80651, by rfl⟩ : syracuseStep 1720565 = 161303) (by norm_num)
theorem B1720589 : Blo 1144635 1720589 := bbase (se 3 (by rfl) ⟨322610, by rfl⟩ : syracuseStep 1720589 = 645221) (by norm_num)
theorem B2900245 : Blo 1144635 2900245 := bbase (se 6 (by rfl) ⟨67974, by rfl⟩ : syracuseStep 2900245 = 135949) (by norm_num)
theorem B1720613 : Blo 1144635 1720613 := bbase (se 4 (by rfl) ⟨161307, by rfl⟩ : syracuseStep 1720613 = 322615) (by norm_num)
theorem B1720637 : Blo 1144635 1720637 := bbase (se 3 (by rfl) ⟨322619, by rfl⟩ : syracuseStep 1720637 = 645239) (by norm_num)
theorem B4538693 : Blo 1144635 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B9290069 : Blo 1144635 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B1720661 : Blo 1144635 1720661 := bbase (se 10 (by rfl) ⟨2520, by rfl⟩ : syracuseStep 1720661 = 5041) (by norm_num)
theorem B1720685 : Blo 1144635 1720685 := bbase (se 3 (by rfl) ⟨322628, by rfl⟩ : syracuseStep 1720685 = 645257) (by norm_num)
theorem B2900357 : Blo 1144635 2900357 := bbase (se 4 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 2900357 = 543817) (by norm_num)
theorem B1720709 : Blo 1144635 1720709 := bbase (se 4 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 1720709 = 322633) (by norm_num)
theorem B1720733 : Blo 1144635 1720733 := bbase (se 3 (by rfl) ⟨322637, by rfl⟩ : syracuseStep 1720733 = 645275) (by norm_num)
theorem B1720757 : Blo 1144635 1720757 := bbase (se 5 (by rfl) ⟨80660, by rfl⟩ : syracuseStep 1720757 = 161321) (by norm_num)
theorem B1720781 : Blo 1144635 1720781 := bbase (se 3 (by rfl) ⟨322646, by rfl⟩ : syracuseStep 1720781 = 645293) (by norm_num)
theorem B1720805 : Blo 1144635 1720805 := bbase (se 4 (by rfl) ⟨161325, by rfl⟩ : syracuseStep 1720805 = 322651) (by norm_num)
theorem B1720829 : Blo 1144635 1720829 := bbase (se 3 (by rfl) ⟨322655, by rfl⟩ : syracuseStep 1720829 = 645311) (by norm_num)
theorem B1720853 : Blo 1144635 1720853 := bbase (se 6 (by rfl) ⟨40332, by rfl⟩ : syracuseStep 1720853 = 80665) (by norm_num)
theorem B1720877 : Blo 1144635 1720877 := bbase (se 3 (by rfl) ⟨322664, by rfl⟩ : syracuseStep 1720877 = 645329) (by norm_num)
theorem B2900549 : Blo 1144635 2900549 := bbase (se 4 (by rfl) ⟨271926, by rfl⟩ : syracuseStep 2900549 = 543853) (by norm_num)
theorem B1720901 : Blo 1144635 1720901 := bbase (se 4 (by rfl) ⟨161334, by rfl⟩ : syracuseStep 1720901 = 322669) (by norm_num)
theorem B1720925 : Blo 1144635 1720925 := bbase (se 3 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 1720925 = 645347) (by norm_num)
theorem B1720949 : Blo 1144635 1720949 := bbase (se 5 (by rfl) ⟨80669, by rfl⟩ : syracuseStep 1720949 = 161339) (by norm_num)
theorem B1720973 : Blo 1144635 1720973 := bbase (se 3 (by rfl) ⟨322682, by rfl⟩ : syracuseStep 1720973 = 645365) (by norm_num)
theorem B1720997 : Blo 1144635 1720997 := bbase (se 4 (by rfl) ⟨161343, by rfl⟩ : syracuseStep 1720997 = 322687) (by norm_num)
theorem B1721021 : Blo 1144635 1721021 := bbase (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) (by norm_num)
theorem B1721045 : Blo 1144635 1721045 := bbase (se 7 (by rfl) ⟨20168, by rfl⟩ : syracuseStep 1721045 = 40337) (by norm_num)
theorem B1721069 : Blo 1144635 1721069 := bbase (se 3 (by rfl) ⟨322700, by rfl⟩ : syracuseStep 1721069 = 645401) (by norm_num)
theorem B1721093 : Blo 1144635 1721093 := bbase (se 4 (by rfl) ⟨161352, by rfl⟩ : syracuseStep 1721093 = 322705) (by norm_num)
theorem B1721117 : Blo 1144635 1721117 := bbase (se 3 (by rfl) ⟨322709, by rfl⟩ : syracuseStep 1721117 = 645419) (by norm_num)
theorem B1164061 : Blo 1144635 1164061 := bbase (se 3 (by rfl) ⟨218261, by rfl⟩ : syracuseStep 1164061 = 436523) (by norm_num)
theorem B2179885 : Blo 1144635 2179885 := bbase (se 3 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 2179885 = 817457) (by norm_num)
theorem B1721141 : Blo 1144635 1721141 := bbase (se 5 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 1721141 = 161357) (by norm_num)
theorem B1721165 : Blo 1144635 1721165 := bbase (se 3 (by rfl) ⟨322718, by rfl⟩ : syracuseStep 1721165 = 645437) (by norm_num)
theorem B1721189 : Blo 1144635 1721189 := bbase (se 4 (by rfl) ⟨161361, by rfl⟩ : syracuseStep 1721189 = 322723) (by norm_num)
theorem B1721213 : Blo 1144635 1721213 := bbase (se 3 (by rfl) ⟨322727, by rfl⟩ : syracuseStep 1721213 = 645455) (by norm_num)
theorem B1721237 : Blo 1144635 1721237 := bbase (se 6 (by rfl) ⟨40341, by rfl⟩ : syracuseStep 1721237 = 80683) (by norm_num)
theorem B2900893 : Blo 1144635 2900893 := bbase (se 3 (by rfl) ⟨543917, by rfl⟩ : syracuseStep 2900893 = 1087835) (by norm_num)
theorem B1721261 : Blo 1144635 1721261 := bbase (se 3 (by rfl) ⟨322736, by rfl⟩ : syracuseStep 1721261 = 645473) (by norm_num)
theorem B2180029 : Blo 1144635 2180029 := bbase (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) (by norm_num)
theorem B1721285 : Blo 1144635 1721285 := bbase (se 4 (by rfl) ⟨161370, by rfl⟩ : syracuseStep 1721285 = 322741) (by norm_num)
theorem B1721309 : Blo 1144635 1721309 := bbase (se 3 (by rfl) ⟨322745, by rfl⟩ : syracuseStep 1721309 = 645491) (by norm_num)
theorem B1721333 : Blo 1144635 1721333 := bbase (se 5 (by rfl) ⟨80687, by rfl⟩ : syracuseStep 1721333 = 161375) (by norm_num)
theorem B2901005 : Blo 1144635 2901005 := bbase (se 3 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 2901005 = 1087877) (by norm_num)
theorem B1721357 : Blo 1144635 1721357 := bbase (se 3 (by rfl) ⟨322754, by rfl⟩ : syracuseStep 1721357 = 645509) (by norm_num)
theorem B1721381 : Blo 1144635 1721381 := bbase (se 4 (by rfl) ⟨161379, by rfl⟩ : syracuseStep 1721381 = 322759) (by norm_num)
theorem B1721405 : Blo 1144635 1721405 := bbase (se 3 (by rfl) ⟨322763, by rfl⟩ : syracuseStep 1721405 = 645527) (by norm_num)
theorem B1721429 : Blo 1144635 1721429 := bbase (se 8 (by rfl) ⟨10086, by rfl⟩ : syracuseStep 1721429 = 20173) (by norm_num)
theorem B2180189 : Blo 1144635 2180189 := bbase (se 3 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 2180189 = 817571) (by norm_num)
theorem B1721453 : Blo 1144635 1721453 := bbase (se 3 (by rfl) ⟨322772, by rfl⟩ : syracuseStep 1721453 = 645545) (by norm_num)
theorem B1721477 : Blo 1144635 1721477 := bbase (se 4 (by rfl) ⟨161388, by rfl⟩ : syracuseStep 1721477 = 322777) (by norm_num)
theorem B1721501 : Blo 1144635 1721501 := bbase (se 3 (by rfl) ⟨322781, by rfl⟩ : syracuseStep 1721501 = 645563) (by norm_num)
theorem B1721525 : Blo 1144635 1721525 := bbase (se 5 (by rfl) ⟨80696, by rfl⟩ : syracuseStep 1721525 = 161393) (by norm_num)
theorem B3261637 : Blo 1144635 3261637 := bbase (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) (by norm_num)
theorem B2901197 : Blo 1144635 2901197 := bbase (se 3 (by rfl) ⟨543974, by rfl⟩ : syracuseStep 2901197 = 1087949) (by norm_num)
theorem B1721549 : Blo 1144635 1721549 := bbase (se 3 (by rfl) ⟨322790, by rfl⟩ : syracuseStep 1721549 = 645581) (by norm_num)
theorem B1721573 : Blo 1144635 1721573 := bbase (se 4 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 1721573 = 322795) (by norm_num)
theorem B2180333 : Blo 1144635 2180333 := bbase (se 3 (by rfl) ⟨408812, by rfl⟩ : syracuseStep 2180333 = 817625) (by norm_num)
theorem B1721597 : Blo 1144635 1721597 := bbase (se 3 (by rfl) ⟨322799, by rfl⟩ : syracuseStep 1721597 = 645599) (by norm_num)
theorem B1721621 : Blo 1144635 1721621 := bbase (se 6 (by rfl) ⟨40350, by rfl⟩ : syracuseStep 1721621 = 80701) (by norm_num)
theorem B1721645 : Blo 1144635 1721645 := bbase (se 3 (by rfl) ⟨322808, by rfl⟩ : syracuseStep 1721645 = 645617) (by norm_num)
theorem B1721669 : Blo 1144635 1721669 := bbase (se 4 (by rfl) ⟨161406, by rfl⟩ : syracuseStep 1721669 = 322813) (by norm_num)
theorem B1721693 : Blo 1144635 1721693 := bbase (se 3 (by rfl) ⟨322817, by rfl⟩ : syracuseStep 1721693 = 645635) (by norm_num)
theorem B1721717 : Blo 1144635 1721717 := bbase (se 5 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 1721717 = 161411) (by norm_num)
theorem B1721741 : Blo 1144635 1721741 := bbase (se 3 (by rfl) ⟨322826, by rfl⟩ : syracuseStep 1721741 = 645653) (by norm_num)
theorem B1721765 : Blo 1144635 1721765 := bbase (se 4 (by rfl) ⟨161415, by rfl⟩ : syracuseStep 1721765 = 322831) (by norm_num)
theorem B1721789 : Blo 1144635 1721789 := bbase (se 3 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 1721789 = 645671) (by norm_num)
theorem B1721813 : Blo 1144635 1721813 := bbase (se 7 (by rfl) ⟨20177, by rfl⟩ : syracuseStep 1721813 = 40355) (by norm_num)
theorem B1721837 : Blo 1144635 1721837 := bbase (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) (by norm_num)
theorem B1721861 : Blo 1144635 1721861 := bbase (se 4 (by rfl) ⟨161424, by rfl⟩ : syracuseStep 1721861 = 322849) (by norm_num)
theorem B1721885 : Blo 1144635 1721885 := bbase (se 3 (by rfl) ⟨322853, by rfl⟩ : syracuseStep 1721885 = 645707) (by norm_num)
theorem B2901541 : Blo 1144635 2901541 := bbase (se 4 (by rfl) ⟨272019, by rfl⟩ : syracuseStep 2901541 = 544039) (by norm_num)
theorem B1721909 : Blo 1144635 1721909 := bbase (se 5 (by rfl) ⟨80714, by rfl⟩ : syracuseStep 1721909 = 161429) (by norm_num)
theorem B1721933 : Blo 1144635 1721933 := bbase (se 3 (by rfl) ⟨322862, by rfl⟩ : syracuseStep 1721933 = 645725) (by norm_num)
theorem B1721957 : Blo 1144635 1721957 := bbase (se 4 (by rfl) ⟨161433, by rfl⟩ : syracuseStep 1721957 = 322867) (by norm_num)
theorem B1721981 : Blo 1144635 1721981 := bbase (se 3 (by rfl) ⟨322871, by rfl⟩ : syracuseStep 1721981 = 645743) (by norm_num)
theorem B5228165 : Blo 1144635 5228165 := bbase (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) (by norm_num)
theorem B2901653 : Blo 1144635 2901653 := bbase (se 6 (by rfl) ⟨68007, by rfl⟩ : syracuseStep 2901653 = 136015) (by norm_num)
theorem B1722005 : Blo 1144635 1722005 := bbase (se 6 (by rfl) ⟨40359, by rfl⟩ : syracuseStep 1722005 = 80719) (by norm_num)
theorem B1722029 : Blo 1144635 1722029 := bbase (se 3 (by rfl) ⟨322880, by rfl⟩ : syracuseStep 1722029 = 645761) (by norm_num)
theorem B1722053 : Blo 1144635 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B1722077 : Blo 1144635 1722077 := bbase (se 3 (by rfl) ⟨322889, by rfl⟩ : syracuseStep 1722077 = 645779) (by norm_num)
theorem B1722101 : Blo 1144635 1722101 := bbase (se 5 (by rfl) ⟨80723, by rfl⟩ : syracuseStep 1722101 = 161447) (by norm_num)
theorem B1722125 : Blo 1144635 1722125 := bbase (se 3 (by rfl) ⟨322898, by rfl⟩ : syracuseStep 1722125 = 645797) (by norm_num)
theorem B1722149 : Blo 1144635 1722149 := bbase (se 4 (by rfl) ⟨161451, by rfl⟩ : syracuseStep 1722149 = 322903) (by norm_num)
theorem B1722173 : Blo 1144635 1722173 := bbase (se 3 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 1722173 = 645815) (by norm_num)
theorem B2901845 : Blo 1144635 2901845 := bbase (se 9 (by rfl) ⟨8501, by rfl⟩ : syracuseStep 2901845 = 17003) (by norm_num)
theorem B1722197 : Blo 1144635 1722197 := bbase (se 9 (by rfl) ⟨5045, by rfl⟩ : syracuseStep 1722197 = 10091) (by norm_num)
theorem B1722221 : Blo 1144635 1722221 := bbase (se 3 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 1722221 = 645833) (by norm_num)
theorem B1722245 : Blo 1144635 1722245 := bbase (se 4 (by rfl) ⟨161460, by rfl⟩ : syracuseStep 1722245 = 322921) (by norm_num)
theorem B1722269 : Blo 1144635 1722269 := bbase (se 3 (by rfl) ⟨322925, by rfl⟩ : syracuseStep 1722269 = 645851) (by norm_num)
theorem B1722293 : Blo 1144635 1722293 := bbase (se 5 (by rfl) ⟨80732, by rfl⟩ : syracuseStep 1722293 = 161465) (by norm_num)
theorem B1722317 : Blo 1144635 1722317 := bbase (se 3 (by rfl) ⟨322934, by rfl⟩ : syracuseStep 1722317 = 645869) (by norm_num)
theorem B1722341 : Blo 1144635 1722341 := bbase (se 4 (by rfl) ⟨161469, by rfl⟩ : syracuseStep 1722341 = 322939) (by norm_num)
theorem B1722365 : Blo 1144635 1722365 := bbase (se 3 (by rfl) ⟨322943, by rfl⟩ : syracuseStep 1722365 = 645887) (by norm_num)
theorem B1722389 : Blo 1144635 1722389 := bbase (se 6 (by rfl) ⟨40368, by rfl⟩ : syracuseStep 1722389 = 80737) (by norm_num)
theorem B1722413 : Blo 1144635 1722413 := bbase (se 3 (by rfl) ⟨322952, by rfl⟩ : syracuseStep 1722413 = 645905) (by norm_num)
theorem B1722437 : Blo 1144635 1722437 := bbase (se 4 (by rfl) ⟨161478, by rfl⟩ : syracuseStep 1722437 = 322957) (by norm_num)
theorem B1722461 : Blo 1144635 1722461 := bbase (se 3 (by rfl) ⟨322961, by rfl⟩ : syracuseStep 1722461 = 645923) (by norm_num)
theorem B1722485 : Blo 1144635 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B1722509 : Blo 1144635 1722509 := bbase (se 3 (by rfl) ⟨322970, by rfl⟩ : syracuseStep 1722509 = 645941) (by norm_num)
theorem B1722533 : Blo 1144635 1722533 := bbase (se 4 (by rfl) ⟨161487, by rfl⟩ : syracuseStep 1722533 = 322975) (by norm_num)
theorem B2902189 : Blo 1144635 2902189 := bbase (se 3 (by rfl) ⟨544160, by rfl⟩ : syracuseStep 2902189 = 1088321) (by norm_num)
theorem B1722557 : Blo 1144635 1722557 := bbase (se 3 (by rfl) ⟨322979, by rfl⟩ : syracuseStep 1722557 = 645959) (by norm_num)
theorem B1722581 : Blo 1144635 1722581 := bbase (se 7 (by rfl) ⟨20186, by rfl⟩ : syracuseStep 1722581 = 40373) (by norm_num)
theorem B1722605 : Blo 1144635 1722605 := bbase (se 3 (by rfl) ⟨322988, by rfl⟩ : syracuseStep 1722605 = 645977) (by norm_num)
theorem B1722629 : Blo 1144635 1722629 := bbase (se 4 (by rfl) ⟨161496, by rfl⟩ : syracuseStep 1722629 = 322993) (by norm_num)
theorem B2902301 : Blo 1144635 2902301 := bbase (se 3 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 2902301 = 1088363) (by norm_num)
theorem B1722653 : Blo 1144635 1722653 := bbase (se 3 (by rfl) ⟨322997, by rfl⟩ : syracuseStep 1722653 = 645995) (by norm_num)
theorem B1722677 : Blo 1144635 1722677 := bbase (se 5 (by rfl) ⟨80750, by rfl⟩ : syracuseStep 1722677 = 161501) (by norm_num)
theorem B1722701 : Blo 1144635 1722701 := bbase (se 3 (by rfl) ⟨323006, by rfl⟩ : syracuseStep 1722701 = 646013) (by norm_num)
theorem B1722725 : Blo 1144635 1722725 := bbase (se 4 (by rfl) ⟨161505, by rfl⟩ : syracuseStep 1722725 = 323011) (by norm_num)
theorem B1722749 : Blo 1144635 1722749 := bbase (se 3 (by rfl) ⟨323015, by rfl⟩ : syracuseStep 1722749 = 646031) (by norm_num)
theorem B1722773 : Blo 1144635 1722773 := bbase (se 6 (by rfl) ⟨40377, by rfl⟩ : syracuseStep 1722773 = 80755) (by norm_num)
theorem B1722797 : Blo 1144635 1722797 := bbase (se 3 (by rfl) ⟨323024, by rfl⟩ : syracuseStep 1722797 = 646049) (by norm_num)
theorem B1722821 : Blo 1144635 1722821 := bbase (se 4 (by rfl) ⟨161514, by rfl⟩ : syracuseStep 1722821 = 323029) (by norm_num)
theorem B2902493 : Blo 1144635 2902493 := bbase (se 3 (by rfl) ⟨544217, by rfl⟩ : syracuseStep 2902493 = 1088435) (by norm_num)
theorem B1722845 : Blo 1144635 1722845 := bbase (se 3 (by rfl) ⟨323033, by rfl⟩ : syracuseStep 1722845 = 646067) (by norm_num)
theorem B1722869 : Blo 1144635 1722869 := bbase (se 5 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 1722869 = 161519) (by norm_num)
theorem B1722893 : Blo 1144635 1722893 := bbase (se 3 (by rfl) ⟨323042, by rfl⟩ : syracuseStep 1722893 = 646085) (by norm_num)
theorem B1722917 : Blo 1144635 1722917 := bbase (se 4 (by rfl) ⟨161523, by rfl⟩ : syracuseStep 1722917 = 323047) (by norm_num)
theorem B1722941 : Blo 1144635 1722941 := bbase (se 3 (by rfl) ⟨323051, by rfl⟩ : syracuseStep 1722941 = 646103) (by norm_num)
theorem B1985141 : Blo 1144635 1985141 := bbase (se 5 (by rfl) ⟨93053, by rfl⟩ : syracuseStep 1985141 = 186107) (by norm_num)
theorem B3263141 : Blo 1144635 3263141 := bbase (se 4 (by rfl) ⟨305919, by rfl⟩ : syracuseStep 3263141 = 611839) (by norm_num)
theorem B2902837 : Blo 1144635 2902837 := bbase (se 5 (by rfl) ⟨136070, by rfl⟩ : syracuseStep 2902837 = 272141) (by norm_num)
theorem B2902949 : Blo 1144635 2902949 := bbase (se 4 (by rfl) ⟨272151, by rfl⟩ : syracuseStep 2902949 = 544303) (by norm_num)
theorem B4901957 : Blo 1144635 4901957 := bbase (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) (by norm_num)
theorem B2903141 : Blo 1144635 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B2575493 : Blo 1144635 2575493 := bbase (se 4 (by rfl) ⟨241452, by rfl⟩ : syracuseStep 2575493 = 482905) (by norm_num)
theorem B2575565 : Blo 1144635 2575565 := bbase (se 3 (by rfl) ⟨482918, by rfl⟩ : syracuseStep 2575565 = 965837) (by norm_num)
theorem B24792277 : Blo 1144635 24792277 := bbase (se 7 (by rfl) ⟨290534, by rfl⟩ : syracuseStep 24792277 = 581069) (by norm_num)
theorem B2575637 : Blo 1144635 2575637 := bbase (se 6 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 2575637 = 120733) (by norm_num)
theorem B2575709 : Blo 1144635 2575709 := bbase (se 3 (by rfl) ⟨482945, by rfl⟩ : syracuseStep 2575709 = 965891) (by norm_num)
theorem B4410773 : Blo 1144635 4410773 := bbase (se 6 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 4410773 = 206755) (by norm_num)
theorem B2575781 : Blo 1144635 2575781 := bbase (se 4 (by rfl) ⟨241479, by rfl⟩ : syracuseStep 2575781 = 482959) (by norm_num)
theorem B5229989 : Blo 1144635 5229989 := bbase (se 4 (by rfl) ⟨490311, by rfl⟩ : syracuseStep 5229989 = 980623) (by norm_num)
theorem B2444717 : Blo 1144635 2444717 := bbase (se 3 (by rfl) ⟨458384, by rfl⟩ : syracuseStep 2444717 = 916769) (by norm_num)
theorem B2903485 : Blo 1144635 2903485 := bbase (se 3 (by rfl) ⟨544403, by rfl⟩ : syracuseStep 2903485 = 1088807) (by norm_num)
theorem B2575853 : Blo 1144635 2575853 := bbase (se 3 (by rfl) ⟨482972, by rfl⟩ : syracuseStep 2575853 = 965945) (by norm_num)
theorem B2903597 : Blo 1144635 2903597 := bbase (se 3 (by rfl) ⟨544424, by rfl⟩ : syracuseStep 2903597 = 1088849) (by norm_num)
theorem B2575925 : Blo 1144635 2575925 := bbase (se 5 (by rfl) ⟨120746, by rfl⟩ : syracuseStep 2575925 = 241493) (by norm_num)
theorem B2444861 : Blo 1144635 2444861 := bbase (se 3 (by rfl) ⟨458411, by rfl⟩ : syracuseStep 2444861 = 916823) (by norm_num)
theorem B2575997 : Blo 1144635 2575997 := bbase (se 3 (by rfl) ⟨482999, by rfl⟩ : syracuseStep 2575997 = 965999) (by norm_num)
theorem B2576069 : Blo 1144635 2576069 := bbase (se 4 (by rfl) ⟨241506, by rfl⟩ : syracuseStep 2576069 = 483013) (by norm_num)
theorem B2903789 : Blo 1144635 2903789 := bbase (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) (by norm_num)
theorem B2576141 : Blo 1144635 2576141 := bbase (se 3 (by rfl) ⟨483026, by rfl⟩ : syracuseStep 2576141 = 966053) (by norm_num)
theorem B4411205 : Blo 1144635 4411205 := bbase (se 4 (by rfl) ⟨413550, by rfl⟩ : syracuseStep 4411205 = 827101) (by norm_num)
theorem B2576213 : Blo 1144635 2576213 := bbase (se 9 (by rfl) ⟨7547, by rfl⟩ : syracuseStep 2576213 = 15095) (by norm_num)
theorem B8376149 : Blo 1144635 8376149 := bbase (se 9 (by rfl) ⟨24539, by rfl⟩ : syracuseStep 8376149 = 49079) (by norm_num)
theorem B2576285 : Blo 1144635 2576285 := bbase (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) (by norm_num)
theorem B2445221 : Blo 1144635 2445221 := bbase (se 4 (by rfl) ⟨229239, by rfl⟩ : syracuseStep 2445221 = 458479) (by norm_num)
theorem B6279125 : Blo 1144635 6279125 := bbase (se 7 (by rfl) ⟨73583, by rfl⟩ : syracuseStep 6279125 = 147167) (by norm_num)
theorem B2576357 : Blo 1144635 2576357 := bbase (se 4 (by rfl) ⟨241533, by rfl⟩ : syracuseStep 2576357 = 483067) (by norm_num)
theorem B2576429 : Blo 1144635 2576429 := bbase (se 3 (by rfl) ⟨483080, by rfl⟩ : syracuseStep 2576429 = 966161) (by norm_num)
theorem B2904133 : Blo 1144635 2904133 := bbase (se 4 (by rfl) ⟨272262, by rfl⟩ : syracuseStep 2904133 = 544525) (by norm_num)
theorem B2576501 : Blo 1144635 2576501 := bbase (se 5 (by rfl) ⟨120773, by rfl⟩ : syracuseStep 2576501 = 241547) (by norm_num)
theorem B3920021 : Blo 1144635 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B2904245 : Blo 1144635 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B2576573 : Blo 1144635 2576573 := bbase (se 3 (by rfl) ⟨483107, by rfl⟩ : syracuseStep 2576573 = 966215) (by norm_num)
theorem B3264725 : Blo 1144635 3264725 := bbase (se 7 (by rfl) ⟨38258, by rfl⟩ : syracuseStep 3264725 = 76517) (by norm_num)
theorem B2576645 : Blo 1144635 2576645 := bbase (se 4 (by rfl) ⟨241560, by rfl⟩ : syracuseStep 2576645 = 483121) (by norm_num)
theorem B2576717 : Blo 1144635 2576717 := bbase (se 3 (by rfl) ⟨483134, by rfl⟩ : syracuseStep 2576717 = 966269) (by norm_num)
theorem B2904437 : Blo 1144635 2904437 := bbase (se 5 (by rfl) ⟨136145, by rfl⟩ : syracuseStep 2904437 = 272291) (by norm_num)
theorem B2576789 : Blo 1144635 2576789 := bbase (se 6 (by rfl) ⟨60393, by rfl⟩ : syracuseStep 2576789 = 120787) (by norm_num)
theorem B2576861 : Blo 1144635 2576861 := bbase (se 3 (by rfl) ⟨483161, by rfl⟩ : syracuseStep 2576861 = 966323) (by norm_num)
theorem B4346405 : Blo 1144635 4346405 := bbase (se 4 (by rfl) ⟨407475, by rfl⟩ : syracuseStep 4346405 = 814951) (by norm_num)
theorem B2576933 : Blo 1144635 2576933 := bbase (se 4 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 2576933 = 483175) (by norm_num)
theorem B16536149 : Blo 1144635 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B2577005 : Blo 1144635 2577005 := bbase (se 3 (by rfl) ⟨483188, by rfl⟩ : syracuseStep 2577005 = 966377) (by norm_num)
theorem B9786005 : Blo 1144635 9786005 := bbase (se 6 (by rfl) ⟨229359, by rfl⟩ : syracuseStep 9786005 = 458719) (by norm_num)
theorem B2577077 : Blo 1144635 2577077 := bbase (se 5 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 2577077 = 241601) (by norm_num)
theorem B2904781 : Blo 1144635 2904781 := bbase (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) (by norm_num)
theorem B2577149 : Blo 1144635 2577149 := bbase (se 3 (by rfl) ⟨483215, by rfl⟩ : syracuseStep 2577149 = 966431) (by norm_num)
theorem B2446109 : Blo 1144635 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B4903733 : Blo 1144635 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B2904893 : Blo 1144635 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B4346693 : Blo 1144635 4346693 := bbase (se 4 (by rfl) ⟨407502, by rfl⟩ : syracuseStep 4346693 = 815005) (by norm_num)
theorem B2577221 : Blo 1144635 2577221 := bbase (se 4 (by rfl) ⟨241614, by rfl⟩ : syracuseStep 2577221 = 483229) (by norm_num)
theorem B3265397 : Blo 1144635 3265397 := bbase (se 5 (by rfl) ⟨153065, by rfl⟩ : syracuseStep 3265397 = 306131) (by norm_num)
theorem B2577293 : Blo 1144635 2577293 := bbase (se 3 (by rfl) ⟨483242, by rfl⟩ : syracuseStep 2577293 = 966485) (by norm_num)
theorem B2577365 : Blo 1144635 2577365 := bbase (se 7 (by rfl) ⟨30203, by rfl⟩ : syracuseStep 2577365 = 60407) (by norm_num)
theorem B2905085 : Blo 1144635 2905085 := bbase (se 3 (by rfl) ⟨544703, by rfl⟩ : syracuseStep 2905085 = 1089407) (by norm_num)
theorem B2446357 : Blo 1144635 2446357 := bbase (se 6 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 2446357 = 114673) (by norm_num)
theorem B2577437 : Blo 1144635 2577437 := bbase (se 3 (by rfl) ⟨483269, by rfl⟩ : syracuseStep 2577437 = 966539) (by norm_num)
theorem B4903973 : Blo 1144635 4903973 := bbase (se 4 (by rfl) ⟨459747, by rfl⟩ : syracuseStep 4903973 = 919495) (by norm_num)
theorem B2577509 : Blo 1144635 2577509 := bbase (se 4 (by rfl) ⟨241641, by rfl⟩ : syracuseStep 2577509 = 483283) (by norm_num)
theorem B2577581 : Blo 1144635 2577581 := bbase (se 3 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 2577581 = 966593) (by norm_num)
theorem B2577653 : Blo 1144635 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B3265829 : Blo 1144635 3265829 := bbase (se 4 (by rfl) ⟨306171, by rfl⟩ : syracuseStep 3265829 = 612343) (by norm_num)
theorem B2577725 : Blo 1144635 2577725 := bbase (se 3 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 2577725 = 966647) (by norm_num)
theorem B2905429 : Blo 1144635 2905429 := bbase (se 16 (by rfl) ⟨66, by rfl⟩ : syracuseStep 2905429 = 133) (by norm_num)
theorem B2577797 : Blo 1144635 2577797 := bbase (se 4 (by rfl) ⟨241668, by rfl⟩ : syracuseStep 2577797 = 483337) (by norm_num)
theorem B3102085 : Blo 1144635 3102085 := bbase (se 4 (by rfl) ⟨290820, by rfl⟩ : syracuseStep 3102085 = 581641) (by norm_num)
theorem B3102149 : Blo 1144635 3102149 := bbase (se 4 (by rfl) ⟨290826, by rfl⟩ : syracuseStep 3102149 = 581653) (by norm_num)
theorem B2905541 : Blo 1144635 2905541 := bbase (se 4 (by rfl) ⟨272394, by rfl⟩ : syracuseStep 2905541 = 544789) (by norm_num)
theorem B2577869 : Blo 1144635 2577869 := bbase (se 3 (by rfl) ⟨483350, by rfl⟩ : syracuseStep 2577869 = 966701) (by norm_num)
theorem B2446861 : Blo 1144635 2446861 := bbase (se 3 (by rfl) ⟨458786, by rfl⟩ : syracuseStep 2446861 = 917573) (by norm_num)
theorem B2577941 : Blo 1144635 2577941 := bbase (se 6 (by rfl) ⟨60420, by rfl⟩ : syracuseStep 2577941 = 120841) (by norm_num)
theorem B2578013 : Blo 1144635 2578013 := bbase (se 3 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 2578013 = 966755) (by norm_num)
theorem B2905733 : Blo 1144635 2905733 := bbase (se 4 (by rfl) ⟨272412, by rfl⟩ : syracuseStep 2905733 = 544825) (by norm_num)
theorem B2578085 : Blo 1144635 2578085 := bbase (se 4 (by rfl) ⟨241695, by rfl⟩ : syracuseStep 2578085 = 483391) (by norm_num)
theorem B8705717 : Blo 1144635 8705717 := bbase (se 5 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 8705717 = 816161) (by norm_num)
theorem B2578157 : Blo 1144635 2578157 := bbase (se 3 (by rfl) ⟨483404, by rfl⟩ : syracuseStep 2578157 = 966809) (by norm_num)
theorem B2578229 : Blo 1144635 2578229 := bbase (se 5 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 2578229 = 241709) (by norm_num)
theorem B2578301 : Blo 1144635 2578301 := bbase (se 3 (by rfl) ⟨483431, by rfl⟩ : syracuseStep 2578301 = 966863) (by norm_num)
theorem B2578373 : Blo 1144635 2578373 := bbase (se 4 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 2578373 = 483445) (by norm_num)
theorem B2906077 : Blo 1144635 2906077 := bbase (se 3 (by rfl) ⟨544889, by rfl⟩ : syracuseStep 2906077 = 1089779) (by norm_num)
theorem B4347877 : Blo 1144635 4347877 := bbase (se 4 (by rfl) ⟨407613, by rfl⟩ : syracuseStep 4347877 = 815227) (by norm_num)
theorem B2578445 : Blo 1144635 2578445 := bbase (se 3 (by rfl) ⟨483458, by rfl⟩ : syracuseStep 2578445 = 966917) (by norm_num)
theorem B3266581 : Blo 1144635 3266581 := bbase (se 6 (by rfl) ⟨76560, by rfl⟩ : syracuseStep 3266581 = 153121) (by norm_num)
theorem B2906189 : Blo 1144635 2906189 := bbase (se 3 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 2906189 = 1089821) (by norm_num)
theorem B2578517 : Blo 1144635 2578517 := bbase (se 8 (by rfl) ⟨15108, by rfl⟩ : syracuseStep 2578517 = 30217) (by norm_num)
theorem B2578589 : Blo 1144635 2578589 := bbase (se 3 (by rfl) ⟨483485, by rfl⟩ : syracuseStep 2578589 = 966971) (by norm_num)
theorem B2578661 : Blo 1144635 2578661 := bbase (se 4 (by rfl) ⟨241749, by rfl⟩ : syracuseStep 2578661 = 483499) (by norm_num)
theorem B2939141 : Blo 1144635 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B2906381 : Blo 1144635 2906381 := bbase (se 3 (by rfl) ⟨544946, by rfl⟩ : syracuseStep 2906381 = 1089893) (by norm_num)
theorem B4348181 : Blo 1144635 4348181 := bbase (se 6 (by rfl) ⟨101910, by rfl⟩ : syracuseStep 4348181 = 203821) (by norm_num)
theorem B2611493 : Blo 1144635 2611493 := bbase (se 4 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 2611493 = 489655) (by norm_num)
theorem B2578733 : Blo 1144635 2578733 := bbase (se 3 (by rfl) ⟨483512, by rfl⟩ : syracuseStep 2578733 = 967025) (by norm_num)
theorem B2611565 : Blo 1144635 2611565 := bbase (se 3 (by rfl) ⟨489668, by rfl⟩ : syracuseStep 2611565 = 979337) (by norm_num)
theorem B2578805 : Blo 1144635 2578805 := bbase (se 5 (by rfl) ⟨120881, by rfl⟩ : syracuseStep 2578805 = 241763) (by norm_num)
theorem B2447749 : Blo 1144635 2447749 := bbase (se 4 (by rfl) ⟨229476, by rfl⟩ : syracuseStep 2447749 = 458953) (by norm_num)
theorem B2578877 : Blo 1144635 2578877 := bbase (se 3 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 2578877 = 967079) (by norm_num)
theorem B2578949 : Blo 1144635 2578949 := bbase (se 4 (by rfl) ⟨241776, by rfl⟩ : syracuseStep 2578949 = 483553) (by norm_num)
theorem B4643365 : Blo 1144635 4643365 := bbase (se 4 (by rfl) ⟨435315, by rfl⟩ : syracuseStep 4643365 = 870631) (by norm_num)
theorem B2579021 : Blo 1144635 2579021 := bbase (se 3 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 2579021 = 967133) (by norm_num)
theorem B2906725 : Blo 1144635 2906725 := bbase (se 4 (by rfl) ⟨272505, by rfl⟩ : syracuseStep 2906725 = 545011) (by norm_num)
theorem B4414085 : Blo 1144635 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B2579093 : Blo 1144635 2579093 := bbase (se 6 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 2579093 = 120895) (by norm_num)
theorem B2906837 : Blo 1144635 2906837 := bbase (se 7 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 2906837 = 68129) (by norm_num)
theorem B2579165 : Blo 1144635 2579165 := bbase (se 3 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 2579165 = 967187) (by norm_num)
theorem B2579237 : Blo 1144635 2579237 := bbase (se 4 (by rfl) ⟨241803, by rfl⟩ : syracuseStep 2579237 = 483607) (by norm_num)
theorem B2579309 : Blo 1144635 2579309 := bbase (se 3 (by rfl) ⟨483620, by rfl⟩ : syracuseStep 2579309 = 967241) (by norm_num)
theorem B2448245 : Blo 1144635 2448245 := bbase (se 5 (by rfl) ⟨114761, by rfl⟩ : syracuseStep 2448245 = 229523) (by norm_num)
theorem B2907029 : Blo 1144635 2907029 := bbase (se 6 (by rfl) ⟨68133, by rfl⟩ : syracuseStep 2907029 = 136267) (by norm_num)
theorem B2579381 : Blo 1144635 2579381 := bbase (se 5 (by rfl) ⟨120908, by rfl⟩ : syracuseStep 2579381 = 241817) (by norm_num)
theorem B2579453 : Blo 1144635 2579453 := bbase (se 3 (by rfl) ⟨483647, by rfl⟩ : syracuseStep 2579453 = 967295) (by norm_num)
theorem B2481197 : Blo 1144635 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B2579525 : Blo 1144635 2579525 := bbase (se 4 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 2579525 = 483661) (by norm_num)
theorem B2579597 : Blo 1144635 2579597 := bbase (se 3 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 2579597 = 967349) (by norm_num)
theorem B2579669 : Blo 1144635 2579669 := bbase (se 7 (by rfl) ⟨30230, by rfl⟩ : syracuseStep 2579669 = 60461) (by norm_num)
theorem B2907373 : Blo 1144635 2907373 := bbase (se 3 (by rfl) ⟨545132, by rfl⟩ : syracuseStep 2907373 = 1090265) (by norm_num)
theorem B4906261 : Blo 1144635 4906261 := bbase (se 6 (by rfl) ⟨114990, by rfl⟩ : syracuseStep 4906261 = 229981) (by norm_num)
theorem B2579741 : Blo 1144635 2579741 := bbase (se 3 (by rfl) ⟨483701, by rfl⟩ : syracuseStep 2579741 = 967403) (by norm_num)
theorem B2907485 : Blo 1144635 2907485 := bbase (se 3 (by rfl) ⟨545153, by rfl⟩ : syracuseStep 2907485 = 1090307) (by norm_num)
theorem B2579813 : Blo 1144635 2579813 := bbase (se 4 (by rfl) ⟨241857, by rfl⟩ : syracuseStep 2579813 = 483715) (by norm_num)
theorem B2579885 : Blo 1144635 2579885 := bbase (se 3 (by rfl) ⟨483728, by rfl⟩ : syracuseStep 2579885 = 967457) (by norm_num)
theorem B2579957 : Blo 1144635 2579957 := bbase (se 5 (by rfl) ⟨120935, by rfl⟩ : syracuseStep 2579957 = 241871) (by norm_num)
theorem B2580029 : Blo 1144635 2580029 := bbase (se 3 (by rfl) ⟨483755, by rfl⟩ : syracuseStep 2580029 = 967511) (by norm_num)
theorem B2580101 : Blo 1144635 2580101 := bbase (se 4 (by rfl) ⟨241884, by rfl⟩ : syracuseStep 2580101 = 483769) (by norm_num)
theorem B2580173 : Blo 1144635 2580173 := bbase (se 3 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 2580173 = 967565) (by norm_num)
theorem B2449133 : Blo 1144635 2449133 := bbase (se 3 (by rfl) ⟨459212, by rfl⟩ : syracuseStep 2449133 = 918425) (by norm_num)
theorem B2580245 : Blo 1144635 2580245 := bbase (se 6 (by rfl) ⟨60474, by rfl⟩ : syracuseStep 2580245 = 120949) (by norm_num)
theorem B4644661 : Blo 1144635 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B4972373 : Blo 1144635 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B2580317 : Blo 1144635 2580317 := bbase (se 3 (by rfl) ⟨483809, by rfl⟩ : syracuseStep 2580317 = 967619) (by norm_num)
theorem B2449253 : Blo 1144635 2449253 := bbase (se 4 (by rfl) ⟨229617, by rfl⟩ : syracuseStep 2449253 = 459235) (by norm_num)
theorem B2580389 : Blo 1144635 2580389 := bbase (se 4 (by rfl) ⟨241911, by rfl⟩ : syracuseStep 2580389 = 483823) (by norm_num)
theorem B2580461 : Blo 1144635 2580461 := bbase (se 3 (by rfl) ⟨483836, by rfl⟩ : syracuseStep 2580461 = 967673) (by norm_num)
theorem B2580533 : Blo 1144635 2580533 := bbase (se 5 (by rfl) ⟨120962, by rfl⟩ : syracuseStep 2580533 = 241925) (by norm_num)
theorem B2515045 : Blo 1144635 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B2580605 : Blo 1144635 2580605 := bbase (se 3 (by rfl) ⟨483863, by rfl⟩ : syracuseStep 2580605 = 967727) (by norm_num)
theorem B2580677 : Blo 1144635 2580677 := bbase (se 4 (by rfl) ⟨241938, by rfl⟩ : syracuseStep 2580677 = 483877) (by norm_num)
theorem B1630477 : Blo 1144635 1630477 := bbase (se 3 (by rfl) ⟨305714, by rfl⟩ : syracuseStep 1630477 = 611429) (by norm_num)
theorem B2580749 : Blo 1144635 2580749 := bbase (se 3 (by rfl) ⟨483890, by rfl⟩ : syracuseStep 2580749 = 967781) (by norm_num)
theorem B4350293 : Blo 1144635 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B2613589 : Blo 1144635 2613589 := bbase (se 10 (by rfl) ⟨3828, by rfl⟩ : syracuseStep 2613589 = 7657) (by norm_num)
theorem B2580821 : Blo 1144635 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B2580893 : Blo 1144635 2580893 := bbase (se 3 (by rfl) ⟨483917, by rfl⟩ : syracuseStep 2580893 = 967835) (by norm_num)
theorem B2449885 : Blo 1144635 2449885 := bbase (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) (by norm_num)
theorem B2580965 : Blo 1144635 2580965 := bbase (se 4 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 2580965 = 483931) (by norm_num)
theorem B2581037 : Blo 1144635 2581037 := bbase (se 3 (by rfl) ⟨483944, by rfl⟩ : syracuseStep 2581037 = 967889) (by norm_num)
theorem B4350581 : Blo 1144635 4350581 := bbase (se 5 (by rfl) ⟨203933, by rfl⟩ : syracuseStep 4350581 = 407867) (by norm_num)
theorem B2581109 : Blo 1144635 2581109 := bbase (se 5 (by rfl) ⟨120989, by rfl⟩ : syracuseStep 2581109 = 241979) (by norm_num)
theorem B2581181 : Blo 1144635 2581181 := bbase (se 3 (by rfl) ⟨483971, by rfl⟩ : syracuseStep 2581181 = 967943) (by norm_num)
theorem B2581253 : Blo 1144635 2581253 := bbase (se 4 (by rfl) ⟨241992, by rfl⟩ : syracuseStep 2581253 = 483985) (by norm_num)
theorem B3269429 : Blo 1144635 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B2581325 : Blo 1144635 2581325 := bbase (se 3 (by rfl) ⟨483998, by rfl⟩ : syracuseStep 2581325 = 967997) (by norm_num)
theorem B2581397 : Blo 1144635 2581397 := bbase (se 6 (by rfl) ⟨60501, by rfl⟩ : syracuseStep 2581397 = 121003) (by norm_num)
theorem B2581469 : Blo 1144635 2581469 := bbase (se 3 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 2581469 = 968051) (by norm_num)
theorem B1631269 : Blo 1144635 1631269 := bbase (se 4 (by rfl) ⟨152931, by rfl⟩ : syracuseStep 1631269 = 305863) (by norm_num)
theorem B2581541 : Blo 1144635 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B2581613 : Blo 1144635 2581613 := bbase (se 3 (by rfl) ⟨484052, by rfl⟩ : syracuseStep 2581613 = 968105) (by norm_num)
theorem B2581685 : Blo 1144635 2581685 := bbase (se 5 (by rfl) ⟨121016, by rfl⟩ : syracuseStep 2581685 = 242033) (by norm_num)
theorem B2581757 : Blo 1144635 2581757 := bbase (se 3 (by rfl) ⟨484079, by rfl⟩ : syracuseStep 2581757 = 968159) (by norm_num)
theorem B2581829 : Blo 1144635 2581829 := bbase (se 4 (by rfl) ⟨242046, by rfl⟩ : syracuseStep 2581829 = 484093) (by norm_num)
theorem B2450773 : Blo 1144635 2450773 := bbase (se 12 (by rfl) ⟨897, by rfl⟩ : syracuseStep 2450773 = 1795) (by norm_num)
theorem B1631605 : Blo 1144635 1631605 := bbase (se 5 (by rfl) ⟨76481, by rfl⟩ : syracuseStep 1631605 = 152963) (by norm_num)
theorem B2581901 : Blo 1144635 2581901 := bbase (se 3 (by rfl) ⟨484106, by rfl⟩ : syracuseStep 2581901 = 968213) (by norm_num)
theorem B2450893 : Blo 1144635 2450893 := bbase (se 3 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 2450893 = 919085) (by norm_num)
theorem B2581973 : Blo 1144635 2581973 := bbase (se 7 (by rfl) ⟨30257, by rfl⟩ : syracuseStep 2581973 = 60515) (by norm_num)
theorem B2582045 : Blo 1144635 2582045 := bbase (se 3 (by rfl) ⟨484133, by rfl⟩ : syracuseStep 2582045 = 968267) (by norm_num)
theorem B1631821 : Blo 1144635 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B2582117 : Blo 1144635 2582117 := bbase (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) (by norm_num)
theorem B2582189 : Blo 1144635 2582189 := bbase (se 3 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 2582189 = 968321) (by norm_num)
theorem B2451149 : Blo 1144635 2451149 := bbase (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) (by norm_num)
theorem B2582261 : Blo 1144635 2582261 := bbase (se 5 (by rfl) ⟨121043, by rfl⟩ : syracuseStep 2582261 = 242087) (by norm_num)
theorem B4351765 : Blo 1144635 4351765 := bbase (se 6 (by rfl) ⟨101994, by rfl⟩ : syracuseStep 4351765 = 203989) (by norm_num)
theorem B13068053 : Blo 1144635 13068053 := bbase (se 6 (by rfl) ⟨306282, by rfl⟩ : syracuseStep 13068053 = 612565) (by norm_num)
theorem B2582333 : Blo 1144635 2582333 := bbase (se 3 (by rfl) ⟨484187, by rfl⟩ : syracuseStep 2582333 = 968375) (by norm_num)
theorem B2942837 : Blo 1144635 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B2582405 : Blo 1144635 2582405 := bbase (se 4 (by rfl) ⟨242100, by rfl⟩ : syracuseStep 2582405 = 484201) (by norm_num)
theorem B1632197 : Blo 1144635 1632197 := bbase (se 4 (by rfl) ⟨153018, by rfl⟩ : syracuseStep 1632197 = 306037) (by norm_num)
theorem B2582477 : Blo 1144635 2582477 := bbase (se 3 (by rfl) ⟨484214, by rfl⟩ : syracuseStep 2582477 = 968429) (by norm_num)
theorem B3270613 : Blo 1144635 3270613 := bbase (se 7 (by rfl) ⟨38327, by rfl⟩ : syracuseStep 3270613 = 76655) (by norm_num)
theorem B1239049 : Blo 1144635 1239049 := bbase (se 2 (by rfl) ⟨464643, by rfl⟩ : syracuseStep 1239049 = 929287) (by norm_num)
theorem B2582549 : Blo 1144635 2582549 := bbase (se 6 (by rfl) ⟨60528, by rfl⟩ : syracuseStep 2582549 = 121057) (by norm_num)
theorem B4352069 : Blo 1144635 4352069 := bbase (se 4 (by rfl) ⟨408006, by rfl⟩ : syracuseStep 4352069 = 816013) (by norm_num)
theorem B2582621 : Blo 1144635 2582621 := bbase (se 3 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 2582621 = 968483) (by norm_num)
theorem B3270773 : Blo 1144635 3270773 := bbase (se 5 (by rfl) ⟨153317, by rfl⟩ : syracuseStep 3270773 = 306635) (by norm_num)
theorem B2582693 : Blo 1144635 2582693 := bbase (se 4 (by rfl) ⟨242127, by rfl⟩ : syracuseStep 2582693 = 484255) (by norm_num)
theorem B2582765 : Blo 1144635 2582765 := bbase (se 3 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 2582765 = 968537) (by norm_num)
theorem B2582837 : Blo 1144635 2582837 := bbase (se 5 (by rfl) ⟨121070, by rfl⟩ : syracuseStep 2582837 = 242141) (by norm_num)
theorem B2582909 : Blo 1144635 2582909 := bbase (se 3 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 2582909 = 968591) (by norm_num)
theorem B1239457 : Blo 1144635 1239457 := bbase (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) (by norm_num)
theorem B1468861 : Blo 1144635 1468861 := bbase (se 3 (by rfl) ⟨275411, by rfl⟩ : syracuseStep 1468861 = 550823) (by norm_num)
theorem B2582981 : Blo 1144635 2582981 := bbase (se 4 (by rfl) ⟨242154, by rfl⟩ : syracuseStep 2582981 = 484309) (by norm_num)
theorem B2583053 : Blo 1144635 2583053 := bbase (se 3 (by rfl) ⟨484322, by rfl⟩ : syracuseStep 2583053 = 968645) (by norm_num)
theorem B2452037 : Blo 1144635 2452037 := bbase (se 4 (by rfl) ⟨229878, by rfl⟩ : syracuseStep 2452037 = 459757) (by norm_num)
theorem B2583125 : Blo 1144635 2583125 := bbase (se 8 (by rfl) ⟨15135, by rfl⟩ : syracuseStep 2583125 = 30271) (by norm_num)
theorem B2583197 : Blo 1144635 2583197 := bbase (se 3 (by rfl) ⟨484349, by rfl⟩ : syracuseStep 2583197 = 968699) (by norm_num)
theorem B2583269 : Blo 1144635 2583269 := bbase (se 4 (by rfl) ⟨242181, by rfl⟩ : syracuseStep 2583269 = 484363) (by norm_num)
theorem B2583341 : Blo 1144635 2583341 := bbase (se 3 (by rfl) ⟨484376, by rfl⟩ : syracuseStep 2583341 = 968753) (by norm_num)
theorem B2452277 : Blo 1144635 2452277 := bbase (se 5 (by rfl) ⟨114950, by rfl⟩ : syracuseStep 2452277 = 229901) (by norm_num)
theorem B7858997 : Blo 1144635 7858997 := bbase (se 5 (by rfl) ⟨368390, by rfl⟩ : syracuseStep 7858997 = 736781) (by norm_num)
theorem B1305409 : Blo 1144635 1305409 := bbase (se 2 (by rfl) ⟨489528, by rfl⟩ : syracuseStep 1305409 = 979057) (by norm_num)
theorem B23554901 : Blo 1144635 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B2583413 : Blo 1144635 2583413 := bbase (se 5 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 2583413 = 242195) (by norm_num)
theorem B2583485 : Blo 1144635 2583485 := bbase (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) (by norm_num)
theorem B4025285 : Blo 1144635 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B3926981 : Blo 1144635 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B2583557 : Blo 1144635 2583557 := bbase (se 4 (by rfl) ⟨242208, by rfl⟩ : syracuseStep 2583557 = 484417) (by norm_num)
theorem B5237797 : Blo 1144635 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B2583629 : Blo 1144635 2583629 := bbase (se 3 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 2583629 = 968861) (by norm_num)
theorem B5794901 : Blo 1144635 5794901 := bbase (se 8 (by rfl) ⟨33954, by rfl⟩ : syracuseStep 5794901 = 67909) (by norm_num)
theorem B2616437 : Blo 1144635 2616437 := bbase (se 5 (by rfl) ⟨122645, by rfl⟩ : syracuseStep 2616437 = 245291) (by norm_num)
theorem B2583701 : Blo 1144635 2583701 := bbase (se 6 (by rfl) ⟨60555, by rfl⟩ : syracuseStep 2583701 = 121111) (by norm_num)
theorem B1961165 : Blo 1144635 1961165 := bbase (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) (by norm_num)
theorem B2583773 : Blo 1144635 2583773 := bbase (se 3 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 2583773 = 968915) (by norm_num)
theorem B2583845 : Blo 1144635 2583845 := bbase (se 4 (by rfl) ⟨242235, by rfl⟩ : syracuseStep 2583845 = 484471) (by norm_num)
theorem B2452781 : Blo 1144635 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B2452789 : Blo 1144635 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B1469765 : Blo 1144635 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1633621 : Blo 1144635 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B2583917 : Blo 1144635 2583917 := bbase (se 3 (by rfl) ⟨484484, by rfl⟩ : syracuseStep 2583917 = 968969) (by norm_num)
theorem B2583989 : Blo 1144635 2583989 := bbase (se 5 (by rfl) ⟨121124, by rfl⟩ : syracuseStep 2583989 = 242249) (by norm_num)
theorem B2584061 : Blo 1144635 2584061 := bbase (se 3 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 2584061 = 969023) (by norm_num)
theorem B2584133 : Blo 1144635 2584133 := bbase (se 4 (by rfl) ⟨242262, by rfl⟩ : syracuseStep 2584133 = 484525) (by norm_num)
theorem B2092637 : Blo 1144635 2092637 := bbase (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) (by norm_num)
theorem B2584205 : Blo 1144635 2584205 := bbase (se 3 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 2584205 = 969077) (by norm_num)
theorem B2584277 : Blo 1144635 2584277 := bbase (se 7 (by rfl) ⟨30284, by rfl⟩ : syracuseStep 2584277 = 60569) (by norm_num)
theorem B1306381 : Blo 1144635 1306381 := bbase (se 3 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 1306381 = 489893) (by norm_num)
theorem B2584349 : Blo 1144635 2584349 := bbase (se 3 (by rfl) ⟨484565, by rfl⟩ : syracuseStep 2584349 = 969131) (by norm_num)
theorem B5500709 : Blo 1144635 5500709 := bbase (se 4 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 5500709 = 1031383) (by norm_num)
theorem B5959477 : Blo 1144635 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B2584421 : Blo 1144635 2584421 := bbase (se 4 (by rfl) ⟨242289, by rfl⟩ : syracuseStep 2584421 = 484579) (by norm_num)
theorem B1634213 : Blo 1144635 1634213 := bbase (se 4 (by rfl) ⟨153207, by rfl⟩ : syracuseStep 1634213 = 306415) (by norm_num)
theorem B1961957 : Blo 1144635 1961957 := bbase (se 4 (by rfl) ⟨183933, by rfl⟩ : syracuseStep 1961957 = 367867) (by norm_num)
theorem B1634293 : Blo 1144635 1634293 := bbase (se 5 (by rfl) ⟨76607, by rfl⟩ : syracuseStep 1634293 = 153215) (by norm_num)
theorem B32206933 : Blo 1144635 32206933 := bbase (se 8 (by rfl) ⟨188712, by rfl⟩ : syracuseStep 32206933 = 377425) (by norm_num)
theorem B1634413 : Blo 1144635 1634413 := bbase (se 3 (by rfl) ⟨306452, by rfl⟩ : syracuseStep 1634413 = 612905) (by norm_num)
theorem B4354181 : Blo 1144635 4354181 := bbase (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) (by norm_num)
theorem B1634509 : Blo 1144635 1634509 := bbase (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) (by norm_num)
theorem B7336277 : Blo 1144635 7336277 := bbase (se 10 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 7336277 = 21493) (by norm_num)
theorem B5796197 : Blo 1144635 5796197 := bbase (se 4 (by rfl) ⟨543393, by rfl⟩ : syracuseStep 5796197 = 1086787) (by norm_num)
theorem B4354469 : Blo 1144635 4354469 := bbase (se 4 (by rfl) ⟨408231, by rfl⟩ : syracuseStep 4354469 = 816463) (by norm_num)
theorem B2617805 : Blo 1144635 2617805 := bbase (se 3 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 2617805 = 981677) (by norm_num)
theorem B1471129 : Blo 1144635 1471129 := bbase (se 2 (by rfl) ⟨551673, by rfl⟩ : syracuseStep 1471129 = 1103347) (by norm_num)
theorem B1635005 : Blo 1144635 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B1176401 : Blo 1144635 1176401 := bbase (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) (by norm_num)
theorem B3863429 : Blo 1144635 3863429 := bbase (se 4 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 3863429 = 724393) (by norm_num)
theorem B2945933 : Blo 1144635 2945933 := bbase (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) (by norm_num)
theorem B2618261 : Blo 1144635 2618261 := bbase (se 6 (by rfl) ⟨61365, by rfl⟩ : syracuseStep 2618261 = 122731) (by norm_num)
theorem B1307549 : Blo 1144635 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B2946005 : Blo 1144635 2946005 := bbase (se 7 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 2946005 = 69047) (by norm_num)
theorem B2618381 : Blo 1144635 2618381 := bbase (se 3 (by rfl) ⟨490946, by rfl⟩ : syracuseStep 2618381 = 981893) (by norm_num)
theorem B2356309 : Blo 1144635 2356309 := bbase (se 8 (by rfl) ⟨13806, by rfl⟩ : syracuseStep 2356309 = 27613) (by norm_num)
theorem B3667189 : Blo 1144635 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B8713493 : Blo 1144635 8713493 := bbase (se 6 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 8713493 = 408445) (by norm_num)
theorem B3863861 : Blo 1144635 3863861 := bbase (se 5 (by rfl) ⟨181118, by rfl⟩ : syracuseStep 3863861 = 362237) (by norm_num)
theorem B1242469 : Blo 1144635 1242469 := bbase (se 4 (by rfl) ⟨116481, by rfl⟩ : syracuseStep 1242469 = 232963) (by norm_num)
theorem B2094445 : Blo 1144635 2094445 := bbase (se 3 (by rfl) ⟨392708, by rfl⟩ : syracuseStep 2094445 = 785417) (by norm_num)
theorem B2651525 : Blo 1144635 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B11007413 : Blo 1144635 11007413 := bbase (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) (by norm_num)
theorem B1177049 : Blo 1144635 1177049 := bbase (se 2 (by rfl) ⟨441393, by rfl⟩ : syracuseStep 1177049 = 882787) (by norm_num)
theorem B1471981 : Blo 1144635 1471981 := bbase (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) (by norm_num)
theorem B6190613 : Blo 1144635 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B4355653 : Blo 1144635 4355653 := bbase (se 4 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 4355653 = 816685) (by norm_num)
theorem B5797493 : Blo 1144635 5797493 := bbase (se 5 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 5797493 = 543515) (by norm_num)
theorem B1767037 : Blo 1144635 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B3667589 : Blo 1144635 3667589 := bbase (se 4 (by rfl) ⟨343836, by rfl⟩ : syracuseStep 3667589 = 687673) (by norm_num)
theorem B5502613 : Blo 1144635 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B5502629 : Blo 1144635 5502629 := bbase (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) (by norm_num)
theorem B6190805 : Blo 1144635 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B3864293 : Blo 1144635 3864293 := bbase (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) (by norm_num)
theorem B4355957 : Blo 1144635 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B3864725 : Blo 1144635 3864725 := bbase (se 6 (by rfl) ⟨90579, by rfl⟩ : syracuseStep 3864725 = 181159) (by norm_num)
theorem B1931573 : Blo 1144635 1931573 := bbase (se 5 (by rfl) ⟨90542, by rfl⟩ : syracuseStep 1931573 = 181085) (by norm_num)
theorem B1931701 : Blo 1144635 1931701 := bbase (se 5 (by rfl) ⟨90548, by rfl⟩ : syracuseStep 1931701 = 181097) (by norm_num)
theorem B1931789 : Blo 1144635 1931789 := bbase (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) (by norm_num)
theorem B1473061 : Blo 1144635 1473061 := bbase (se 4 (by rfl) ⟨138099, by rfl⟩ : syracuseStep 1473061 = 276199) (by norm_num)
theorem B3865157 : Blo 1144635 3865157 := bbase (se 4 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 3865157 = 724717) (by norm_num)
theorem B1309285 : Blo 1144635 1309285 := bbase (se 4 (by rfl) ⟨122745, by rfl⟩ : syracuseStep 1309285 = 245491) (by norm_num)
theorem B1931917 : Blo 1144635 1931917 := bbase (se 3 (by rfl) ⟨362234, by rfl⟩ : syracuseStep 1931917 = 724469) (by norm_num)
theorem B1932005 : Blo 1144635 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B1833749 : Blo 1144635 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 1144635 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B2063141 : Blo 1144635 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B1932133 : Blo 1144635 1932133 := bbase (se 4 (by rfl) ⟨181137, by rfl⟩ : syracuseStep 1932133 = 362275) (by norm_num)
theorem B2063213 : Blo 1144635 2063213 := bbase (se 3 (by rfl) ⟨386852, by rfl⟩ : syracuseStep 2063213 = 773705) (by norm_num)
theorem B1833845 : Blo 1144635 1833845 := bbase (se 5 (by rfl) ⟨85961, by rfl⟩ : syracuseStep 1833845 = 171923) (by norm_num)
theorem B5798789 : Blo 1144635 5798789 := bbase (se 4 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 5798789 = 1087273) (by norm_num)
theorem B1833877 : Blo 1144635 1833877 := bbase (se 6 (by rfl) ⟨42981, by rfl⟩ : syracuseStep 1833877 = 85963) (by norm_num)
theorem B1932221 : Blo 1144635 1932221 := bbase (se 3 (by rfl) ⟨362291, by rfl⟩ : syracuseStep 1932221 = 724583) (by norm_num)
theorem B7076821 : Blo 1144635 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B3865589 : Blo 1144635 3865589 := bbase (se 5 (by rfl) ⟨181199, by rfl⟩ : syracuseStep 3865589 = 362399) (by norm_num)
theorem B1375273 : Blo 1144635 1375273 := bbase (se 2 (by rfl) ⟨515727, by rfl⟩ : syracuseStep 1375273 = 1031455) (by norm_num)
theorem B1932349 : Blo 1144635 1932349 := bbase (se 3 (by rfl) ⟨362315, by rfl⟩ : syracuseStep 1932349 = 724631) (by norm_num)
theorem B2751565 : Blo 1144635 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B1932437 : Blo 1144635 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B6520085 : Blo 1144635 6520085 := bbase (se 6 (by rfl) ⟨152814, by rfl⟩ : syracuseStep 6520085 = 305629) (by norm_num)
theorem B1932565 : Blo 1144635 1932565 := bbase (se 6 (by rfl) ⟨45294, by rfl⟩ : syracuseStep 1932565 = 90589) (by norm_num)
theorem B1932653 : Blo 1144635 1932653 := bbase (se 3 (by rfl) ⟨362372, by rfl⟩ : syracuseStep 1932653 = 724745) (by norm_num)
theorem B8256917 : Blo 1144635 8256917 := bbase (se 6 (by rfl) ⟨193521, by rfl⟩ : syracuseStep 8256917 = 387043) (by norm_num)
theorem B3866021 : Blo 1144635 3866021 := bbase (se 4 (by rfl) ⟨362439, by rfl⟩ : syracuseStep 3866021 = 724879) (by norm_num)
theorem B1932781 : Blo 1144635 1932781 := bbase (se 3 (by rfl) ⟨362396, by rfl⟩ : syracuseStep 1932781 = 724793) (by norm_num)
theorem B3538421 : Blo 1144635 3538421 := bbase (se 5 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 3538421 = 331727) (by norm_num)
theorem B2326061 : Blo 1144635 2326061 := bbase (se 3 (by rfl) ⟨436136, by rfl⟩ : syracuseStep 2326061 = 872273) (by norm_num)
theorem B1932869 : Blo 1144635 1932869 := bbase (se 4 (by rfl) ⟨181206, by rfl⟩ : syracuseStep 1932869 = 362413) (by norm_num)
theorem B2752181 : Blo 1144635 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B1932997 : Blo 1144635 1932997 := bbase (se 4 (by rfl) ⟨181218, by rfl⟩ : syracuseStep 1932997 = 362437) (by norm_num)
theorem B3145429 : Blo 1144635 3145429 := bbase (se 7 (by rfl) ⟨36860, by rfl⟩ : syracuseStep 3145429 = 73721) (by norm_num)
theorem B2752237 : Blo 1144635 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B1933085 : Blo 1144635 1933085 := bbase (se 3 (by rfl) ⟨362453, by rfl⟩ : syracuseStep 1933085 = 724907) (by norm_num)
theorem B3866453 : Blo 1144635 3866453 := bbase (se 9 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 3866453 = 22655) (by norm_num)
theorem B1933213 : Blo 1144635 1933213 := bbase (se 3 (by rfl) ⟨362477, by rfl⟩ : syracuseStep 1933213 = 724955) (by norm_num)
theorem B4358069 : Blo 1144635 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B5505013 : Blo 1144635 5505013 := bbase (se 5 (by rfl) ⟨258047, by rfl⟩ : syracuseStep 5505013 = 516095) (by norm_num)
theorem B1933301 : Blo 1144635 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B1146883 : Blo 1144635 1146883 := bstep (se 1 (by rfl) ⟨860162, by rfl⟩ : syracuseStep 1146883 = 1720325) B1720325
theorem B1146899 : Blo 1144635 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B1146915 : Blo 1144635 1146915 := bstep (se 1 (by rfl) ⟨860186, by rfl⟩ : syracuseStep 1146915 = 1720373) B1720373
theorem B3866669 : Blo 1144635 3866669 := bstep (se 3 (by rfl) ⟨725000, by rfl⟩ : syracuseStep 3866669 = 1450001) B1450001
theorem B4128817 : Blo 1144635 4128817 := bstep (se 2 (by rfl) ⟨1548306, by rfl⟩ : syracuseStep 4128817 = 3096613) B3096613
theorem B1146931 : Blo 1144635 1146931 := bstep (se 1 (by rfl) ⟨860198, by rfl⟩ : syracuseStep 1146931 = 1720397) B1720397
theorem B1146947 : Blo 1144635 1146947 := bstep (se 1 (by rfl) ⟨860210, by rfl⟩ : syracuseStep 1146947 = 1720421) B1720421
theorem B1146963 : Blo 1144635 1146963 := bstep (se 1 (by rfl) ⟨860222, by rfl⟩ : syracuseStep 1146963 = 1720445) B1720445
theorem B1933409 : Blo 1144635 1933409 := bstep (se 2 (by rfl) ⟨725028, by rfl⟩ : syracuseStep 1933409 = 1450057) B1450057
theorem B3866723 : Blo 1144635 3866723 := bstep (se 1 (by rfl) ⟨2900042, by rfl⟩ : syracuseStep 3866723 = 5800085) B5800085
theorem B1146979 : Blo 1144635 1146979 := bstep (se 1 (by rfl) ⟨860234, by rfl⟩ : syracuseStep 1146979 = 1720469) B1720469
theorem B1146995 : Blo 1144635 1146995 := bstep (se 1 (by rfl) ⟨860246, by rfl⟩ : syracuseStep 1146995 = 1720493) B1720493
theorem B1147011 : Blo 1144635 1147011 := bstep (se 1 (by rfl) ⟨860258, by rfl⟩ : syracuseStep 1147011 = 1720517) B1720517
theorem B1147027 : Blo 1144635 1147027 := bstep (se 1 (by rfl) ⟨860270, by rfl⟩ : syracuseStep 1147027 = 1720541) B1720541
theorem B1147043 : Blo 1144635 1147043 := bstep (se 1 (by rfl) ⟨860282, by rfl⟩ : syracuseStep 1147043 = 1720565) B1720565
theorem B1147059 : Blo 1144635 1147059 := bstep (se 1 (by rfl) ⟨860294, by rfl⟩ : syracuseStep 1147059 = 1720589) B1720589
theorem B1147075 : Blo 1144635 1147075 := bstep (se 1 (by rfl) ⟨860306, by rfl⟩ : syracuseStep 1147075 = 1720613) B1720613
theorem B1147091 : Blo 1144635 1147091 := bstep (se 1 (by rfl) ⟨860318, by rfl⟩ : syracuseStep 1147091 = 1720637) B1720637
theorem B1933537 : Blo 1144635 1933537 := bstep (se 2 (by rfl) ⟨725076, by rfl⟩ : syracuseStep 1933537 = 1450153) B1450153
theorem B6193379 : Blo 1144635 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B1147107 : Blo 1144635 1147107 := bstep (se 1 (by rfl) ⟨860330, by rfl⟩ : syracuseStep 1147107 = 1720661) B1720661
theorem B1147123 : Blo 1144635 1147123 := bstep (se 1 (by rfl) ⟨860342, by rfl⟩ : syracuseStep 1147123 = 1720685) B1720685
theorem B1933571 : Blo 1144635 1933571 := bstep (se 1 (by rfl) ⟨1450178, by rfl⟩ : syracuseStep 1933571 = 2900357) B2900357
theorem B1147139 : Blo 1144635 1147139 := bstep (se 1 (by rfl) ⟨860354, by rfl⟩ : syracuseStep 1147139 = 1720709) B1720709
theorem B2326801 : Blo 1144635 2326801 := bstep (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) B1745101
theorem B1147155 : Blo 1144635 1147155 := bstep (se 1 (by rfl) ⟨860366, by rfl⟩ : syracuseStep 1147155 = 1720733) B1720733
theorem B1147171 : Blo 1144635 1147171 := bstep (se 1 (by rfl) ⟨860378, by rfl⟩ : syracuseStep 1147171 = 1720757) B1720757
theorem B1147187 : Blo 1144635 1147187 := bstep (se 1 (by rfl) ⟨860390, by rfl⟩ : syracuseStep 1147187 = 1720781) B1720781
theorem B1147203 : Blo 1144635 1147203 := bstep (se 1 (by rfl) ⟨860402, by rfl⟩ : syracuseStep 1147203 = 1720805) B1720805
theorem B1147219 : Blo 1144635 1147219 := bstep (se 1 (by rfl) ⟨860414, by rfl⟩ : syracuseStep 1147219 = 1720829) B1720829
theorem B1147235 : Blo 1144635 1147235 := bstep (se 1 (by rfl) ⟨860426, by rfl⟩ : syracuseStep 1147235 = 1720853) B1720853
theorem B3866993 : Blo 1144635 3866993 := bstep (se 2 (by rfl) ⟨1450122, by rfl⟩ : syracuseStep 3866993 = 2900245) B2900245
theorem B1147251 : Blo 1144635 1147251 := bstep (se 1 (by rfl) ⟨860438, by rfl⟩ : syracuseStep 1147251 = 1720877) B1720877
theorem B1933699 : Blo 1144635 1933699 := bstep (se 1 (by rfl) ⟨1450274, by rfl⟩ : syracuseStep 1933699 = 2900549) B2900549
theorem B1147267 : Blo 1144635 1147267 := bstep (se 1 (by rfl) ⟨860450, by rfl⟩ : syracuseStep 1147267 = 1720901) B1720901
theorem B1147283 : Blo 1144635 1147283 := bstep (se 1 (by rfl) ⟨860462, by rfl⟩ : syracuseStep 1147283 = 1720925) B1720925
theorem B1147299 : Blo 1144635 1147299 := bstep (se 1 (by rfl) ⟨860474, by rfl⟩ : syracuseStep 1147299 = 1720949) B1720949
theorem B1147315 : Blo 1144635 1147315 := bstep (se 1 (by rfl) ⟨860486, by rfl⟩ : syracuseStep 1147315 = 1720973) B1720973
theorem B1147331 : Blo 1144635 1147331 := bstep (se 1 (by rfl) ⟨860498, by rfl⟩ : syracuseStep 1147331 = 1720997) B1720997
theorem B1147347 : Blo 1144635 1147347 := bstep (se 1 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 1147347 = 1721021) B1721021
theorem B1147363 : Blo 1144635 1147363 := bstep (se 1 (by rfl) ⟨860522, by rfl⟩ : syracuseStep 1147363 = 1721045) B1721045
theorem B1147379 : Blo 1144635 1147379 := bstep (se 1 (by rfl) ⟨860534, by rfl⟩ : syracuseStep 1147379 = 1721069) B1721069
theorem B1147395 : Blo 1144635 1147395 := bstep (se 1 (by rfl) ⟨860546, by rfl⟩ : syracuseStep 1147395 = 1721093) B1721093
theorem B1933841 : Blo 1144635 1933841 := bstep (se 2 (by rfl) ⟨725190, by rfl⟩ : syracuseStep 1933841 = 1450381) B1450381
theorem B1147411 : Blo 1144635 1147411 := bstep (se 1 (by rfl) ⟨860558, by rfl⟩ : syracuseStep 1147411 = 1721117) B1721117
theorem B1147427 : Blo 1144635 1147427 := bstep (se 1 (by rfl) ⟨860570, by rfl⟩ : syracuseStep 1147427 = 1721141) B1721141
theorem B1147443 : Blo 1144635 1147443 := bstep (se 1 (by rfl) ⟨860582, by rfl⟩ : syracuseStep 1147443 = 1721165) B1721165
theorem B1147459 : Blo 1144635 1147459 := bstep (se 1 (by rfl) ⟨860594, by rfl⟩ : syracuseStep 1147459 = 1721189) B1721189
theorem B1147475 : Blo 1144635 1147475 := bstep (se 1 (by rfl) ⟨860606, by rfl⟩ : syracuseStep 1147475 = 1721213) B1721213
theorem B1147491 : Blo 1144635 1147491 := bstep (se 1 (by rfl) ⟨860618, by rfl⟩ : syracuseStep 1147491 = 1721237) B1721237
theorem B1147507 : Blo 1144635 1147507 := bstep (se 1 (by rfl) ⟨860630, by rfl⟩ : syracuseStep 1147507 = 1721261) B1721261
theorem B1147523 : Blo 1144635 1147523 := bstep (se 1 (by rfl) ⟨860642, by rfl⟩ : syracuseStep 1147523 = 1721285) B1721285
theorem B1933969 : Blo 1144635 1933969 := bstep (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) B1450477
theorem B1147539 : Blo 1144635 1147539 := bstep (se 1 (by rfl) ⟨860654, by rfl⟩ : syracuseStep 1147539 = 1721309) B1721309
theorem B1147555 : Blo 1144635 1147555 := bstep (se 1 (by rfl) ⟨860666, by rfl⟩ : syracuseStep 1147555 = 1721333) B1721333
theorem B1934003 : Blo 1144635 1934003 := bstep (se 1 (by rfl) ⟨1450502, by rfl⟩ : syracuseStep 1934003 = 2901005) B2901005
theorem B1147571 : Blo 1144635 1147571 := bstep (se 1 (by rfl) ⟨860678, by rfl⟩ : syracuseStep 1147571 = 1721357) B1721357
theorem B1147587 : Blo 1144635 1147587 := bstep (se 1 (by rfl) ⟨860690, by rfl⟩ : syracuseStep 1147587 = 1721381) B1721381
theorem B1147603 : Blo 1144635 1147603 := bstep (se 1 (by rfl) ⟨860702, by rfl⟩ : syracuseStep 1147603 = 1721405) B1721405
theorem B1147619 : Blo 1144635 1147619 := bstep (se 1 (by rfl) ⟨860714, by rfl⟩ : syracuseStep 1147619 = 1721429) B1721429
theorem B1147635 : Blo 1144635 1147635 := bstep (se 1 (by rfl) ⟨860726, by rfl⟩ : syracuseStep 1147635 = 1721453) B1721453
theorem B1147651 : Blo 1144635 1147651 := bstep (se 1 (by rfl) ⟨860738, by rfl⟩ : syracuseStep 1147651 = 1721477) B1721477
theorem B1147667 : Blo 1144635 1147667 := bstep (se 1 (by rfl) ⟨860750, by rfl⟩ : syracuseStep 1147667 = 1721501) B1721501
theorem B2753315 : Blo 1144635 2753315 := bstep (se 1 (by rfl) ⟨2064986, by rfl⟩ : syracuseStep 2753315 = 4129973) B4129973
theorem B1147683 : Blo 1144635 1147683 := bstep (se 1 (by rfl) ⟨860762, by rfl⟩ : syracuseStep 1147683 = 1721525) B1721525
theorem B3670829 : Blo 1144635 3670829 := bstep (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) B1376561
theorem B1934131 : Blo 1144635 1934131 := bstep (se 1 (by rfl) ⟨1450598, by rfl⟩ : syracuseStep 1934131 = 2901197) B2901197
theorem B1147699 : Blo 1144635 1147699 := bstep (se 1 (by rfl) ⟨860774, by rfl⟩ : syracuseStep 1147699 = 1721549) B1721549
theorem B1147715 : Blo 1144635 1147715 := bstep (se 1 (by rfl) ⟨860786, by rfl⟩ : syracuseStep 1147715 = 1721573) B1721573
theorem B1147731 : Blo 1144635 1147731 := bstep (se 1 (by rfl) ⟨860798, by rfl⟩ : syracuseStep 1147731 = 1721597) B1721597
theorem B1147747 : Blo 1144635 1147747 := bstep (se 1 (by rfl) ⟨860810, by rfl⟩ : syracuseStep 1147747 = 1721621) B1721621
theorem B1147763 : Blo 1144635 1147763 := bstep (se 1 (by rfl) ⟨860822, by rfl⟩ : syracuseStep 1147763 = 1721645) B1721645
theorem B1147779 : Blo 1144635 1147779 := bstep (se 1 (by rfl) ⟨860834, by rfl⟩ : syracuseStep 1147779 = 1721669) B1721669
theorem B3867533 : Blo 1144635 3867533 := bstep (se 3 (by rfl) ⟨725162, by rfl⟩ : syracuseStep 3867533 = 1450325) B1450325
theorem B3539857 : Blo 1144635 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B1147795 : Blo 1144635 1147795 := bstep (se 1 (by rfl) ⟨860846, by rfl⟩ : syracuseStep 1147795 = 1721693) B1721693
theorem B1147811 : Blo 1144635 1147811 := bstep (se 1 (by rfl) ⟨860858, by rfl⟩ : syracuseStep 1147811 = 1721717) B1721717
theorem B1147827 : Blo 1144635 1147827 := bstep (se 1 (by rfl) ⟨860870, by rfl⟩ : syracuseStep 1147827 = 1721741) B1721741
theorem B1934273 : Blo 1144635 1934273 := bstep (se 2 (by rfl) ⟨725352, by rfl⟩ : syracuseStep 1934273 = 1450705) B1450705
theorem B3867587 : Blo 1144635 3867587 := bstep (se 1 (by rfl) ⟨2900690, by rfl⟩ : syracuseStep 3867587 = 5801381) B5801381
theorem B1147843 : Blo 1144635 1147843 := bstep (se 1 (by rfl) ⟨860882, by rfl⟩ : syracuseStep 1147843 = 1721765) B1721765
theorem B1147859 : Blo 1144635 1147859 := bstep (se 1 (by rfl) ⟨860894, by rfl⟩ : syracuseStep 1147859 = 1721789) B1721789
theorem B1147875 : Blo 1144635 1147875 := bstep (se 1 (by rfl) ⟨860906, by rfl⟩ : syracuseStep 1147875 = 1721813) B1721813
theorem B1147891 : Blo 1144635 1147891 := bstep (se 1 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 1147891 = 1721837) B1721837
theorem B1147907 : Blo 1144635 1147907 := bstep (se 1 (by rfl) ⟨860930, by rfl⟩ : syracuseStep 1147907 = 1721861) B1721861
theorem B1147923 : Blo 1144635 1147923 := bstep (se 1 (by rfl) ⟨860942, by rfl⟩ : syracuseStep 1147923 = 1721885) B1721885
theorem B1147939 : Blo 1144635 1147939 := bstep (se 1 (by rfl) ⟨860954, by rfl⟩ : syracuseStep 1147939 = 1721909) B1721909
theorem B1147955 : Blo 1144635 1147955 := bstep (se 1 (by rfl) ⟨860966, by rfl⟩ : syracuseStep 1147955 = 1721933) B1721933
theorem B1934401 : Blo 1144635 1934401 := bstep (se 2 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 1934401 = 1450801) B1450801
theorem B1147971 : Blo 1144635 1147971 := bstep (se 1 (by rfl) ⟨860978, by rfl⟩ : syracuseStep 1147971 = 1721957) B1721957
theorem B8717381 : Blo 1144635 8717381 := bstep (se 4 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 8717381 = 1634509) B1634509
theorem B1147987 : Blo 1144635 1147987 := bstep (se 1 (by rfl) ⟨860990, by rfl⟩ : syracuseStep 1147987 = 1721981) B1721981
theorem B1934435 : Blo 1144635 1934435 := bstep (se 1 (by rfl) ⟨1450826, by rfl⟩ : syracuseStep 1934435 = 2901653) B2901653
theorem B1148003 : Blo 1144635 1148003 := bstep (se 1 (by rfl) ⟨861002, by rfl⟩ : syracuseStep 1148003 = 1722005) B1722005
theorem B1148019 : Blo 1144635 1148019 := bstep (se 1 (by rfl) ⟨861014, by rfl⟩ : syracuseStep 1148019 = 1722029) B1722029
theorem B1148035 : Blo 1144635 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B1148051 : Blo 1144635 1148051 := bstep (se 1 (by rfl) ⟨861038, by rfl⟩ : syracuseStep 1148051 = 1722077) B1722077
theorem B1148067 : Blo 1144635 1148067 := bstep (se 1 (by rfl) ⟨861050, by rfl⟩ : syracuseStep 1148067 = 1722101) B1722101
theorem B1836209 : Blo 1144635 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B1148083 : Blo 1144635 1148083 := bstep (se 1 (by rfl) ⟨861062, by rfl⟩ : syracuseStep 1148083 = 1722125) B1722125
theorem B1148099 : Blo 1144635 1148099 := bstep (se 1 (by rfl) ⟨861074, by rfl⟩ : syracuseStep 1148099 = 1722149) B1722149
theorem B9798853 : Blo 1144635 9798853 := bstep (se 4 (by rfl) ⟨918642, by rfl⟩ : syracuseStep 9798853 = 1837285) B1837285
theorem B6980813 : Blo 1144635 6980813 := bstep (se 3 (by rfl) ⟨1308902, by rfl⟩ : syracuseStep 6980813 = 2617805) B2617805
theorem B3867857 : Blo 1144635 3867857 := bstep (se 2 (by rfl) ⟨1450446, by rfl⟩ : syracuseStep 3867857 = 2900893) B2900893
theorem B1148115 : Blo 1144635 1148115 := bstep (se 1 (by rfl) ⟨861086, by rfl⟩ : syracuseStep 1148115 = 1722173) B1722173
theorem B1934563 : Blo 1144635 1934563 := bstep (se 1 (by rfl) ⟨1450922, by rfl⟩ : syracuseStep 1934563 = 2901845) B2901845
theorem B1148131 : Blo 1144635 1148131 := bstep (se 1 (by rfl) ⟨861098, by rfl⟩ : syracuseStep 1148131 = 1722197) B1722197
theorem B1148147 : Blo 1144635 1148147 := bstep (se 1 (by rfl) ⟨861110, by rfl⟩ : syracuseStep 1148147 = 1722221) B1722221
theorem B1148163 : Blo 1144635 1148163 := bstep (se 1 (by rfl) ⟨861122, by rfl⟩ : syracuseStep 1148163 = 1722245) B1722245
theorem B1148179 : Blo 1144635 1148179 := bstep (se 1 (by rfl) ⟨861134, by rfl⟩ : syracuseStep 1148179 = 1722269) B1722269
theorem B1148195 : Blo 1144635 1148195 := bstep (se 1 (by rfl) ⟨861146, by rfl⟩ : syracuseStep 1148195 = 1722293) B1722293
theorem B1148211 : Blo 1144635 1148211 := bstep (se 1 (by rfl) ⟨861158, by rfl⟩ : syracuseStep 1148211 = 1722317) B1722317
theorem B1148227 : Blo 1144635 1148227 := bstep (se 1 (by rfl) ⟨861170, by rfl⟩ : syracuseStep 1148227 = 1722341) B1722341
theorem B1148243 : Blo 1144635 1148243 := bstep (se 1 (by rfl) ⟨861182, by rfl⟩ : syracuseStep 1148243 = 1722365) B1722365
theorem B1148259 : Blo 1144635 1148259 := bstep (se 1 (by rfl) ⟨861194, by rfl⟩ : syracuseStep 1148259 = 1722389) B1722389
theorem B1934705 : Blo 1144635 1934705 := bstep (se 2 (by rfl) ⟨725514, by rfl⟩ : syracuseStep 1934705 = 1451029) B1451029
theorem B1148275 : Blo 1144635 1148275 := bstep (se 1 (by rfl) ⟨861206, by rfl⟩ : syracuseStep 1148275 = 1722413) B1722413
theorem B1148291 : Blo 1144635 1148291 := bstep (se 1 (by rfl) ⟨861218, by rfl⟩ : syracuseStep 1148291 = 1722437) B1722437
theorem B1148307 : Blo 1144635 1148307 := bstep (se 1 (by rfl) ⟨861230, by rfl⟩ : syracuseStep 1148307 = 1722461) B1722461
theorem B1148323 : Blo 1144635 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B1148339 : Blo 1144635 1148339 := bstep (se 1 (by rfl) ⟨861254, by rfl⟩ : syracuseStep 1148339 = 1722509) B1722509
theorem B1148355 : Blo 1144635 1148355 := bstep (se 1 (by rfl) ⟨861266, by rfl⟩ : syracuseStep 1148355 = 1722533) B1722533
theorem B1148371 : Blo 1144635 1148371 := bstep (se 1 (by rfl) ⟨861278, by rfl⟩ : syracuseStep 1148371 = 1722557) B1722557
theorem B1148387 : Blo 1144635 1148387 := bstep (se 1 (by rfl) ⟨861290, by rfl⟩ : syracuseStep 1148387 = 1722581) B1722581
theorem B1934833 : Blo 1144635 1934833 := bstep (se 2 (by rfl) ⟨725562, by rfl⟩ : syracuseStep 1934833 = 1451125) B1451125
theorem B1148403 : Blo 1144635 1148403 := bstep (se 1 (by rfl) ⟨861302, by rfl⟩ : syracuseStep 1148403 = 1722605) B1722605
theorem B1148419 : Blo 1144635 1148419 := bstep (se 1 (by rfl) ⟨861314, by rfl⟩ : syracuseStep 1148419 = 1722629) B1722629
theorem B1934867 : Blo 1144635 1934867 := bstep (se 1 (by rfl) ⟨1451150, by rfl⟩ : syracuseStep 1934867 = 2902301) B2902301
theorem B1148435 : Blo 1144635 1148435 := bstep (se 1 (by rfl) ⟨861326, by rfl⟩ : syracuseStep 1148435 = 1722653) B1722653
theorem B2754083 : Blo 1144635 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B1148451 : Blo 1144635 1148451 := bstep (se 1 (by rfl) ⟨861338, by rfl⟩ : syracuseStep 1148451 = 1722677) B1722677
theorem B1148467 : Blo 1144635 1148467 := bstep (se 1 (by rfl) ⟨861350, by rfl⟩ : syracuseStep 1148467 = 1722701) B1722701
theorem B1148483 : Blo 1144635 1148483 := bstep (se 1 (by rfl) ⟨861362, by rfl⟩ : syracuseStep 1148483 = 1722725) B1722725
theorem B1148499 : Blo 1144635 1148499 := bstep (se 1 (by rfl) ⟨861374, by rfl⟩ : syracuseStep 1148499 = 1722749) B1722749
theorem B1148515 : Blo 1144635 1148515 := bstep (se 1 (by rfl) ⟨861386, by rfl⟩ : syracuseStep 1148515 = 1722773) B1722773
theorem B1148531 : Blo 1144635 1148531 := bstep (se 1 (by rfl) ⟨861398, by rfl⟩ : syracuseStep 1148531 = 1722797) B1722797
theorem B1148547 : Blo 1144635 1148547 := bstep (se 1 (by rfl) ⟨861410, by rfl⟩ : syracuseStep 1148547 = 1722821) B1722821
theorem B1934995 : Blo 1144635 1934995 := bstep (se 1 (by rfl) ⟨1451246, by rfl⟩ : syracuseStep 1934995 = 2902493) B2902493
theorem B1148563 : Blo 1144635 1148563 := bstep (se 1 (by rfl) ⟨861422, by rfl⟩ : syracuseStep 1148563 = 1722845) B1722845
theorem B1148579 : Blo 1144635 1148579 := bstep (se 1 (by rfl) ⟨861434, by rfl⟩ : syracuseStep 1148579 = 1722869) B1722869
theorem B6522545 : Blo 1144635 6522545 := bstep (se 2 (by rfl) ⟨2445954, by rfl⟩ : syracuseStep 6522545 = 4891909) B4891909
theorem B1148595 : Blo 1144635 1148595 := bstep (se 1 (by rfl) ⟨861446, by rfl⟩ : syracuseStep 1148595 = 1722893) B1722893
theorem B1148611 : Blo 1144635 1148611 := bstep (se 1 (by rfl) ⟨861458, by rfl⟩ : syracuseStep 1148611 = 1722917) B1722917
theorem B1148627 : Blo 1144635 1148627 := bstep (se 1 (by rfl) ⟨861470, by rfl⟩ : syracuseStep 1148627 = 1722941) B1722941
theorem B3868397 : Blo 1144635 3868397 := bstep (se 3 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 3868397 = 1450649) B1450649
theorem B1935137 : Blo 1144635 1935137 := bstep (se 2 (by rfl) ⟨725676, by rfl⟩ : syracuseStep 1935137 = 1451353) B1451353
theorem B3868451 : Blo 1144635 3868451 := bstep (se 1 (by rfl) ⟨2901338, by rfl⟩ : syracuseStep 3868451 = 5802677) B5802677
theorem B4360013 : Blo 1144635 4360013 := bstep (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) B1635005
theorem B7341965 : Blo 1144635 7341965 := bstep (se 3 (by rfl) ⟨1376618, by rfl⟩ : syracuseStep 7341965 = 2753237) B2753237
theorem B1935265 : Blo 1144635 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B1935299 : Blo 1144635 1935299 := bstep (se 1 (by rfl) ⟨1451474, by rfl⟩ : syracuseStep 1935299 = 2902949) B2902949
theorem B1378243 : Blo 1144635 1378243 := bstep (se 1 (by rfl) ⟨1033682, by rfl⟩ : syracuseStep 1378243 = 2067365) B2067365
theorem B4130765 : Blo 1144635 4130765 := bstep (se 3 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 4130765 = 1549037) B1549037
theorem B1837075 : Blo 1144635 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B3868721 : Blo 1144635 3868721 := bstep (se 2 (by rfl) ⟨1450770, by rfl⟩ : syracuseStep 3868721 = 2901541) B2901541
theorem B1935427 : Blo 1144635 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B2754641 : Blo 1144635 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B1378387 : Blo 1144635 1378387 := bstep (se 1 (by rfl) ⟨1033790, by rfl⟩ : syracuseStep 1378387 = 2067581) B2067581
theorem B1935569 : Blo 1144635 1935569 := bstep (se 2 (by rfl) ⟨725838, by rfl⟩ : syracuseStep 1935569 = 1451677) B1451677
theorem B1837331 : Blo 1144635 1837331 := bstep (se 1 (by rfl) ⟨1377998, by rfl⟩ : syracuseStep 1837331 = 2755997) B2755997
theorem B7833925 : Blo 1144635 7833925 := bstep (se 4 (by rfl) ⟨734430, by rfl⟩ : syracuseStep 7833925 = 1468861) B1468861
theorem B1935697 : Blo 1144635 1935697 := bstep (se 2 (by rfl) ⟨725886, by rfl⟩ : syracuseStep 1935697 = 1451773) B1451773
theorem B5802353 : Blo 1144635 5802353 := bstep (se 2 (by rfl) ⟨2175882, by rfl⟩ : syracuseStep 5802353 = 4351765) B4351765
theorem B1935731 : Blo 1144635 1935731 := bstep (se 1 (by rfl) ⟨1451798, by rfl⟩ : syracuseStep 1935731 = 2903597) B2903597
theorem B13240817 : Blo 1144635 13240817 := bstep (se 2 (by rfl) ⟨4965306, by rfl⟩ : syracuseStep 13240817 = 9930613) B9930613
theorem B1935859 : Blo 1144635 1935859 := bstep (se 1 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 1935859 = 2903789) B2903789
theorem B3672611 : Blo 1144635 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B3869261 : Blo 1144635 3869261 := bstep (se 3 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 3869261 = 1450973) B1450973
theorem B4360817 : Blo 1144635 4360817 := bstep (se 2 (by rfl) ⟨1635306, by rfl⟩ : syracuseStep 4360817 = 3270613) B3270613
theorem B1936001 : Blo 1144635 1936001 := bstep (se 2 (by rfl) ⟨726000, by rfl⟩ : syracuseStep 1936001 = 1452001) B1452001
theorem B3869315 : Blo 1144635 3869315 := bstep (se 1 (by rfl) ⟨2901986, by rfl⟩ : syracuseStep 3869315 = 5803973) B5803973
theorem B2755313 : Blo 1144635 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B1936129 : Blo 1144635 1936129 := bstep (se 2 (by rfl) ⟨726048, by rfl⟩ : syracuseStep 1936129 = 1452097) B1452097
theorem B1936163 : Blo 1144635 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B3869585 : Blo 1144635 3869585 := bstep (se 2 (by rfl) ⟨1451094, by rfl⟩ : syracuseStep 3869585 = 2902189) B2902189
theorem B1936291 : Blo 1144635 1936291 := bstep (se 1 (by rfl) ⟨1452218, by rfl⟩ : syracuseStep 1936291 = 2904437) B2904437
theorem B1936433 : Blo 1144635 1936433 := bstep (se 2 (by rfl) ⟨726162, by rfl⟩ : syracuseStep 1936433 = 1452325) B1452325
theorem B6524003 : Blo 1144635 6524003 := bstep (se 1 (by rfl) ⟨4893002, by rfl⟩ : syracuseStep 6524003 = 9786005) B9786005
theorem B1936561 : Blo 1144635 1936561 := bstep (se 2 (by rfl) ⟨726210, by rfl⟩ : syracuseStep 1936561 = 1452421) B1452421
theorem B1936595 : Blo 1144635 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1838305 : Blo 1144635 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B1936723 : Blo 1144635 1936723 := bstep (se 1 (by rfl) ⟨1452542, by rfl⟩ : syracuseStep 1936723 = 2905085) B2905085
theorem B3870125 : Blo 1144635 3870125 := bstep (se 3 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 3870125 = 1451297) B1451297
theorem B1936865 : Blo 1144635 1936865 := bstep (se 2 (by rfl) ⟨726324, by rfl⟩ : syracuseStep 1936865 = 1452649) B1452649
theorem B3870179 : Blo 1144635 3870179 := bstep (se 1 (by rfl) ⟨2902634, by rfl⟩ : syracuseStep 3870179 = 5805269) B5805269
theorem B1936993 : Blo 1144635 1936993 := bstep (se 2 (by rfl) ⟨726372, by rfl⟩ : syracuseStep 1936993 = 1452745) B1452745
theorem B4132451 : Blo 1144635 4132451 := bstep (se 1 (by rfl) ⟨3099338, by rfl⟩ : syracuseStep 4132451 = 6198677) B6198677
theorem B2068099 : Blo 1144635 2068099 := bstep (se 1 (by rfl) ⟨1551074, by rfl⟩ : syracuseStep 2068099 = 3102149) B3102149
theorem B1937027 : Blo 1144635 1937027 := bstep (se 1 (by rfl) ⟨1452770, by rfl⟩ : syracuseStep 1937027 = 2905541) B2905541
theorem B3870449 : Blo 1144635 3870449 := bstep (se 2 (by rfl) ⟨1451418, by rfl⟩ : syracuseStep 3870449 = 2902837) B2902837
theorem B1740545 : Blo 1144635 1740545 := bstep (se 2 (by rfl) ⟨652704, by rfl⟩ : syracuseStep 1740545 = 1305409) B1305409
theorem B1937155 : Blo 1144635 1937155 := bstep (se 1 (by rfl) ⟨1452866, by rfl⟩ : syracuseStep 1937155 = 2905733) B2905733
theorem B5803811 : Blo 1144635 5803811 := bstep (se 1 (by rfl) ⟨4352858, by rfl⟩ : syracuseStep 5803811 = 8705717) B8705717
theorem B4656973 : Blo 1144635 4656973 := bstep (se 3 (by rfl) ⟨873182, by rfl⟩ : syracuseStep 4656973 = 1746365) B1746365
theorem B3673955 : Blo 1144635 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B1937297 : Blo 1144635 1937297 := bstep (se 2 (by rfl) ⟨726486, by rfl⟩ : syracuseStep 1937297 = 1452973) B1452973
theorem B1937425 : Blo 1144635 1937425 := bstep (se 2 (by rfl) ⟨726534, by rfl⟩ : syracuseStep 1937425 = 1453069) B1453069
theorem B6983729 : Blo 1144635 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1937459 : Blo 1144635 1937459 := bstep (se 1 (by rfl) ⟨1453094, by rfl⟩ : syracuseStep 1937459 = 2906189) B2906189
theorem B10457201 : Blo 1144635 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B1839233 : Blo 1144635 1839233 := bstep (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) B1379425
theorem B1937587 : Blo 1144635 1937587 := bstep (se 1 (by rfl) ⟨1453190, by rfl⟩ : syracuseStep 1937587 = 2906381) B2906381
theorem B1740995 : Blo 1144635 1740995 := bstep (se 1 (by rfl) ⟨1305746, by rfl⟩ : syracuseStep 1740995 = 2611493) B2611493
theorem B1741043 : Blo 1144635 1741043 := bstep (se 1 (by rfl) ⟨1305782, by rfl⟩ : syracuseStep 1741043 = 2611565) B2611565
theorem B3870989 : Blo 1144635 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B1937729 : Blo 1144635 1937729 := bstep (se 2 (by rfl) ⟨726648, by rfl⟩ : syracuseStep 1937729 = 1453297) B1453297
theorem B3871043 : Blo 1144635 3871043 := bstep (se 1 (by rfl) ⟨2903282, by rfl⟩ : syracuseStep 3871043 = 5806565) B5806565
theorem B2068849 : Blo 1144635 2068849 := bstep (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) B1551637
theorem B1937857 : Blo 1144635 1937857 := bstep (se 2 (by rfl) ⟨726696, by rfl⟩ : syracuseStep 1937857 = 1453393) B1453393
theorem B2757073 : Blo 1144635 2757073 := bstep (se 2 (by rfl) ⟨1033902, by rfl⟩ : syracuseStep 2757073 = 2067805) B2067805
theorem B1937891 : Blo 1144635 1937891 := bstep (se 1 (by rfl) ⟨1453418, by rfl⟩ : syracuseStep 1937891 = 2906837) B2906837
theorem B5804621 : Blo 1144635 5804621 := bstep (se 3 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 5804621 = 2176733) B2176733
theorem B3871313 : Blo 1144635 3871313 := bstep (se 2 (by rfl) ⟨1451742, by rfl⟩ : syracuseStep 3871313 = 2903485) B2903485
theorem B1938019 : Blo 1144635 1938019 := bstep (se 1 (by rfl) ⟨1453514, by rfl⟩ : syracuseStep 1938019 = 2907029) B2907029
theorem B1938161 : Blo 1144635 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1938289 : Blo 1144635 1938289 := bstep (se 2 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 1938289 = 1453717) B1453717
theorem B1938323 : Blo 1144635 1938323 := bstep (se 1 (by rfl) ⟨1453742, by rfl⟩ : syracuseStep 1938323 = 2907485) B2907485
theorem B1741841 : Blo 1144635 1741841 := bstep (se 2 (by rfl) ⟨653190, by rfl⟩ : syracuseStep 1741841 = 1306381) B1306381
theorem B3871853 : Blo 1144635 3871853 := bstep (se 3 (by rfl) ⟨725972, by rfl⟩ : syracuseStep 3871853 = 1451945) B1451945
theorem B3871907 : Blo 1144635 3871907 := bstep (se 1 (by rfl) ⟨2903930, by rfl⟩ : syracuseStep 3871907 = 5807861) B5807861
theorem B7345349 : Blo 1144635 7345349 := bstep (se 4 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 7345349 = 1377253) B1377253
theorem B3314915 : Blo 1144635 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B3872177 : Blo 1144635 3872177 := bstep (se 2 (by rfl) ⟨1452066, by rfl⟩ : syracuseStep 3872177 = 2904133) B2904133
theorem B3675725 : Blo 1144635 3675725 := bstep (se 3 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 3675725 = 1378397) B1378397
theorem B3872717 : Blo 1144635 3872717 := bstep (se 3 (by rfl) ⟨726134, by rfl⟩ : syracuseStep 3872717 = 1452269) B1452269
theorem B3872771 : Blo 1144635 3872771 := bstep (se 1 (by rfl) ⟨2904578, by rfl⟩ : syracuseStep 3872771 = 5809157) B5809157
theorem B5511395 : Blo 1144635 5511395 := bstep (se 1 (by rfl) ⟨4133546, by rfl⟩ : syracuseStep 5511395 = 8267093) B8267093
theorem B3873041 : Blo 1144635 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B5511473 : Blo 1144635 5511473 := bstep (se 2 (by rfl) ⟨2066802, by rfl⟩ : syracuseStep 5511473 = 4133605) B4133605
theorem B3873581 : Blo 1144635 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B3873635 : Blo 1144635 3873635 := bstep (se 1 (by rfl) ⟨2905226, by rfl⟩ : syracuseStep 3873635 = 5810453) B5810453
theorem B1448867 : Blo 1144635 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B4889585 : Blo 1144635 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B3873905 : Blo 1144635 3873905 := bstep (se 2 (by rfl) ⟨1452714, by rfl⟩ : syracuseStep 3873905 = 2905429) B2905429
theorem B2792593 : Blo 1144635 2792593 := bstep (se 2 (by rfl) ⟨1047222, by rfl⟩ : syracuseStep 2792593 = 2094445) B2094445
theorem B4136113 : Blo 1144635 4136113 := bstep (se 2 (by rfl) ⟨1551042, by rfl⟩ : syracuseStep 4136113 = 3102085) B3102085
theorem B4136141 : Blo 1144635 4136141 := bstep (se 3 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 4136141 = 1551053) B1551053
theorem B1744291 : Blo 1144635 1744291 := bstep (se 1 (by rfl) ⟨1308218, by rfl⟩ : syracuseStep 1744291 = 2616437) B2616437
theorem B5807537 : Blo 1144635 5807537 := bstep (se 2 (by rfl) ⟨2177826, by rfl⟩ : syracuseStep 5807537 = 4355653) B4355653
theorem B1449571 : Blo 1144635 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B4890253 : Blo 1144635 4890253 := bstep (se 3 (by rfl) ⟨916922, by rfl⟩ : syracuseStep 4890253 = 1833845) B1833845
theorem B3874445 : Blo 1144635 3874445 := bstep (se 3 (by rfl) ⟨726458, by rfl⟩ : syracuseStep 3874445 = 1452917) B1452917
theorem B1449667 : Blo 1144635 1449667 := bstep (se 1 (by rfl) ⟨1087250, by rfl⟩ : syracuseStep 1449667 = 2174501) B2174501
theorem B3874499 : Blo 1144635 3874499 := bstep (se 1 (by rfl) ⟨2905874, by rfl⟩ : syracuseStep 3874499 = 5811749) B5811749
theorem B3874769 : Blo 1144635 3874769 := bstep (se 2 (by rfl) ⟨1453038, by rfl⟩ : syracuseStep 3874769 = 2906077) B2906077
theorem B5513393 : Blo 1144635 5513393 := bstep (se 2 (by rfl) ⟨2067522, by rfl⟩ : syracuseStep 5513393 = 4135045) B4135045
theorem B1450163 : Blo 1144635 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B4890851 : Blo 1144635 4890851 := bstep (se 1 (by rfl) ⟨3668138, by rfl⟩ : syracuseStep 4890851 = 7336277) B7336277
theorem B8692109 : Blo 1144635 8692109 := bstep (se 3 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 8692109 = 3259541) B3259541
theorem B3875309 : Blo 1144635 3875309 := bstep (se 3 (by rfl) ⟨726620, by rfl⟩ : syracuseStep 3875309 = 1453241) B1453241
theorem B3875363 : Blo 1144635 3875363 := bstep (se 1 (by rfl) ⟨2906522, by rfl⟩ : syracuseStep 3875363 = 5813045) B5813045
theorem B1745507 : Blo 1144635 1745507 := bstep (se 1 (by rfl) ⟨1309130, by rfl⟩ : syracuseStep 1745507 = 2618261) B2618261
theorem B1548977 : Blo 1144635 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B7348913 : Blo 1144635 7348913 := bstep (se 2 (by rfl) ⟨2755842, by rfl⟩ : syracuseStep 7348913 = 5511685) B5511685
theorem B1745587 : Blo 1144635 1745587 := bstep (se 1 (by rfl) ⟨1309190, by rfl⟩ : syracuseStep 1745587 = 2618381) B2618381
theorem B5513933 : Blo 1144635 5513933 := bstep (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) B2067725
theorem B3678929 : Blo 1144635 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B3678979 : Blo 1144635 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B1745713 : Blo 1144635 1745713 := bstep (se 2 (by rfl) ⟨654642, by rfl⟩ : syracuseStep 1745713 = 1309285) B1309285
theorem B3875633 : Blo 1144635 3875633 := bstep (se 2 (by rfl) ⟨1453362, by rfl⟩ : syracuseStep 3875633 = 2906725) B2906725
theorem B5808995 : Blo 1144635 5808995 := bstep (se 1 (by rfl) ⟨4356746, by rfl⟩ : syracuseStep 5808995 = 8713493) B8713493
theorem B1450867 : Blo 1144635 1450867 := bstep (se 1 (by rfl) ⟨1088150, by rfl⟩ : syracuseStep 1450867 = 2176301) B2176301
theorem B1450963 : Blo 1144635 1450963 := bstep (se 1 (by rfl) ⟨1088222, by rfl⟩ : syracuseStep 1450963 = 2176445) B2176445
theorem B3876173 : Blo 1144635 3876173 := bstep (se 3 (by rfl) ⟨726782, by rfl⟩ : syracuseStep 3876173 = 1453565) B1453565
theorem B3876227 : Blo 1144635 3876227 := bstep (se 1 (by rfl) ⟨2907170, by rfl⟩ : syracuseStep 3876227 = 5814341) B5814341
theorem B1451459 : Blo 1144635 1451459 := bstep (se 1 (by rfl) ⟨1088594, by rfl⟩ : syracuseStep 1451459 = 2177189) B2177189
theorem B1287715 : Blo 1144635 1287715 := bstep (se 1 (by rfl) ⟨965786, by rfl⟩ : syracuseStep 1287715 = 1931573) B1931573
theorem B5809805 : Blo 1144635 5809805 := bstep (se 3 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 5809805 = 2178677) B2178677
theorem B16557709 : Blo 1144635 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B3876497 : Blo 1144635 3876497 := bstep (se 2 (by rfl) ⟨1453686, by rfl⟩ : syracuseStep 3876497 = 2907373) B2907373
theorem B1287859 : Blo 1144635 1287859 := bstep (se 1 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 1287859 = 1931789) B1931789
theorem B9807601 : Blo 1144635 9807601 := bstep (se 2 (by rfl) ⟨3677850, by rfl⟩ : syracuseStep 9807601 = 7355701) B7355701
theorem B1288003 : Blo 1144635 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B1222499 : Blo 1144635 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B1288147 : Blo 1144635 1288147 := bstep (se 1 (by rfl) ⟨966110, by rfl⟩ : syracuseStep 1288147 = 1932221) B1932221
theorem B1288291 : Blo 1144635 1288291 := bstep (se 1 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 1288291 = 1932437) B1932437
theorem B7350371 : Blo 1144635 7350371 := bstep (se 1 (by rfl) ⟨5512778, by rfl⟩ : syracuseStep 7350371 = 11025557) B11025557
theorem B1452163 : Blo 1144635 1452163 := bstep (se 1 (by rfl) ⟨1089122, by rfl⟩ : syracuseStep 1452163 = 2178245) B2178245
theorem B1452259 : Blo 1144635 1452259 := bstep (se 1 (by rfl) ⟨1089194, by rfl⟩ : syracuseStep 1452259 = 2178389) B2178389
theorem B1288435 : Blo 1144635 1288435 := bstep (se 1 (by rfl) ⟨966326, by rfl⟩ : syracuseStep 1288435 = 1932653) B1932653
theorem B2206001 : Blo 1144635 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B1550707 : Blo 1144635 1550707 := bstep (se 1 (by rfl) ⟨1163030, by rfl⟩ : syracuseStep 1550707 = 2326061) B2326061
theorem B1288579 : Blo 1144635 1288579 := bstep (se 1 (by rfl) ⟨966434, by rfl⟩ : syracuseStep 1288579 = 1932869) B1932869
theorem B1288723 : Blo 1144635 1288723 := bstep (se 1 (by rfl) ⟨966542, by rfl⟩ : syracuseStep 1288723 = 1933085) B1933085
theorem B1550945 : Blo 1144635 1550945 := bstep (se 2 (by rfl) ⟨581604, by rfl⟩ : syracuseStep 1550945 = 1163209) B1163209
theorem B1288867 : Blo 1144635 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B1452755 : Blo 1144635 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B3353393 : Blo 1144635 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B1289011 : Blo 1144635 1289011 := bstep (se 1 (by rfl) ⟨966758, by rfl⟩ : syracuseStep 1289011 = 1933517) B1933517
theorem B3025795 : Blo 1144635 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B1289155 : Blo 1144635 1289155 := bstep (se 1 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 1289155 = 1933733) B1933733
theorem B2173969 : Blo 1144635 2173969 := bstep (se 2 (by rfl) ⟨815238, by rfl⟩ : syracuseStep 2173969 = 1630477) B1630477
theorem B6204451 : Blo 1144635 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B1289299 : Blo 1144635 1289299 := bstep (se 1 (by rfl) ⟨966974, by rfl⟩ : syracuseStep 1289299 = 1933949) B1933949
theorem B1289443 : Blo 1144635 1289443 := bstep (se 1 (by rfl) ⟨967082, by rfl⟩ : syracuseStep 1289443 = 1934165) B1934165
theorem B8695025 : Blo 1144635 8695025 := bstep (se 2 (by rfl) ⟨3260634, by rfl⟩ : syracuseStep 8695025 = 6521269) B6521269
theorem B4467953 : Blo 1144635 4467953 := bstep (se 2 (by rfl) ⟨1675482, by rfl⟩ : syracuseStep 4467953 = 3350965) B3350965
theorem B1289587 : Blo 1144635 1289587 := bstep (se 1 (by rfl) ⟨967190, by rfl⟩ : syracuseStep 1289587 = 1934381) B1934381
theorem B1224067 : Blo 1144635 1224067 := bstep (se 1 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 1224067 = 1836101) B1836101
theorem B1453459 : Blo 1144635 1453459 := bstep (se 1 (by rfl) ⟨1090094, by rfl⟩ : syracuseStep 1453459 = 2180189) B2180189
theorem B1453555 : Blo 1144635 1453555 := bstep (se 1 (by rfl) ⟨1090166, by rfl⟩ : syracuseStep 1453555 = 2180333) B2180333
theorem B1289731 : Blo 1144635 1289731 := bstep (se 1 (by rfl) ⟨967298, by rfl⟩ : syracuseStep 1289731 = 1934597) B1934597
theorem B1289875 : Blo 1144635 1289875 := bstep (se 1 (by rfl) ⟨967406, by rfl⟩ : syracuseStep 1289875 = 1934813) B1934813
theorem B3485443 : Blo 1144635 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B1290019 : Blo 1144635 1290019 := bstep (se 1 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 1290019 = 1935029) B1935029
theorem B3977009 : Blo 1144635 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B1224515 : Blo 1144635 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B6532933 : Blo 1144635 6532933 := bstep (se 4 (by rfl) ⟨612462, by rfl⟩ : syracuseStep 6532933 = 1224925) B1224925
theorem B4894627 : Blo 1144635 4894627 := bstep (se 1 (by rfl) ⟨3670970, by rfl⟩ : syracuseStep 4894627 = 7341941) B7341941
theorem B1290163 : Blo 1144635 1290163 := bstep (se 1 (by rfl) ⟨967622, by rfl⟩ : syracuseStep 1290163 = 1935245) B1935245
theorem B2175025 : Blo 1144635 2175025 := bstep (se 2 (by rfl) ⟨815634, by rfl⟩ : syracuseStep 2175025 = 1631269) B1631269
theorem B1290307 : Blo 1144635 1290307 := bstep (se 1 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 1290307 = 1935461) B1935461
theorem B3584099 : Blo 1144635 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B1290451 : Blo 1144635 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B6205681 : Blo 1144635 6205681 := bstep (se 2 (by rfl) ⟨2327130, by rfl⟩ : syracuseStep 6205681 = 4654261) B4654261
theorem B1290595 : Blo 1144635 1290595 := bstep (se 1 (by rfl) ⟨967946, by rfl⟩ : syracuseStep 1290595 = 1935893) B1935893
theorem B1323427 : Blo 1144635 1323427 := bstep (se 1 (by rfl) ⟨992570, by rfl⟩ : syracuseStep 1323427 = 1985141) B1985141
theorem B2175427 : Blo 1144635 2175427 := bstep (se 1 (by rfl) ⟨1631570, by rfl⟩ : syracuseStep 2175427 = 3263141) B3263141
theorem B13939141 : Blo 1144635 13939141 := bstep (se 4 (by rfl) ⟨1306794, by rfl⟩ : syracuseStep 13939141 = 2613589) B2613589
theorem B2175473 : Blo 1144635 2175473 := bstep (se 2 (by rfl) ⟨815802, by rfl⟩ : syracuseStep 2175473 = 1631605) B1631605
theorem B5812721 : Blo 1144635 5812721 := bstep (se 2 (by rfl) ⟨2179770, by rfl⟩ : syracuseStep 5812721 = 4359541) B4359541
theorem B1290739 : Blo 1144635 1290739 := bstep (se 1 (by rfl) ⟨968054, by rfl⟩ : syracuseStep 1290739 = 1936109) B1936109
theorem B1290883 : Blo 1144635 1290883 := bstep (se 1 (by rfl) ⟨968162, by rfl⟩ : syracuseStep 1290883 = 1936325) B1936325
theorem B1716977 : Blo 1144635 1716977 := bstep (se 2 (by rfl) ⟨643866, by rfl⟩ : syracuseStep 1716977 = 1287733) B1287733
theorem B1716995 : Blo 1144635 1716995 := bstep (se 1 (by rfl) ⟨1287746, by rfl⟩ : syracuseStep 1716995 = 2575493) B2575493
theorem B2175761 : Blo 1144635 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B1291027 : Blo 1144635 1291027 := bstep (se 1 (by rfl) ⟨968270, by rfl⟩ : syracuseStep 1291027 = 1936541) B1936541
theorem B1717025 : Blo 1144635 1717025 := bstep (se 2 (by rfl) ⟨643884, by rfl⟩ : syracuseStep 1717025 = 1287769) B1287769
theorem B1717043 : Blo 1144635 1717043 := bstep (se 1 (by rfl) ⟨1287782, by rfl⟩ : syracuseStep 1717043 = 2575565) B2575565
theorem B1717073 : Blo 1144635 1717073 := bstep (se 2 (by rfl) ⟨643902, by rfl⟩ : syracuseStep 1717073 = 1287805) B1287805
theorem B1717091 : Blo 1144635 1717091 := bstep (se 1 (by rfl) ⟨1287818, by rfl⟩ : syracuseStep 1717091 = 2575637) B2575637
theorem B1717121 : Blo 1144635 1717121 := bstep (se 2 (by rfl) ⟨643920, by rfl⟩ : syracuseStep 1717121 = 1287841) B1287841
theorem B1717139 : Blo 1144635 1717139 := bstep (se 1 (by rfl) ⟨1287854, by rfl⟩ : syracuseStep 1717139 = 2575709) B2575709
theorem B1291171 : Blo 1144635 1291171 := bstep (se 1 (by rfl) ⟨968378, by rfl⟩ : syracuseStep 1291171 = 1936757) B1936757
theorem B1717169 : Blo 1144635 1717169 := bstep (se 2 (by rfl) ⟨643938, by rfl⟩ : syracuseStep 1717169 = 1287877) B1287877
theorem B1717187 : Blo 1144635 1717187 := bstep (se 1 (by rfl) ⟨1287890, by rfl⟩ : syracuseStep 1717187 = 2575781) B2575781
theorem B3486659 : Blo 1144635 3486659 := bstep (se 1 (by rfl) ⟨2614994, by rfl⟩ : syracuseStep 3486659 = 5229989) B5229989
theorem B1717217 : Blo 1144635 1717217 := bstep (se 2 (by rfl) ⟨643956, by rfl⟩ : syracuseStep 1717217 = 1287913) B1287913
theorem B1717235 : Blo 1144635 1717235 := bstep (se 1 (by rfl) ⟨1287926, by rfl⟩ : syracuseStep 1717235 = 2575853) B2575853
theorem B1717265 : Blo 1144635 1717265 := bstep (se 2 (by rfl) ⟨643974, by rfl⟩ : syracuseStep 1717265 = 1287949) B1287949
theorem B1717283 : Blo 1144635 1717283 := bstep (se 1 (by rfl) ⟨1287962, by rfl⟩ : syracuseStep 1717283 = 2575925) B2575925
theorem B1291315 : Blo 1144635 1291315 := bstep (se 1 (by rfl) ⟨968486, by rfl⟩ : syracuseStep 1291315 = 1936973) B1936973
theorem B1717313 : Blo 1144635 1717313 := bstep (se 2 (by rfl) ⟨643992, by rfl⟩ : syracuseStep 1717313 = 1287985) B1287985
theorem B3486797 : Blo 1144635 3486797 := bstep (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) B1307549
theorem B1717331 : Blo 1144635 1717331 := bstep (se 1 (by rfl) ⟨1287998, by rfl⟩ : syracuseStep 1717331 = 2575997) B2575997
theorem B1717361 : Blo 1144635 1717361 := bstep (se 2 (by rfl) ⟨644010, by rfl⟩ : syracuseStep 1717361 = 1288021) B1288021
theorem B1717379 : Blo 1144635 1717379 := bstep (se 1 (by rfl) ⟨1288034, by rfl⟩ : syracuseStep 1717379 = 2576069) B2576069
theorem B1717409 : Blo 1144635 1717409 := bstep (se 2 (by rfl) ⟨644028, by rfl⟩ : syracuseStep 1717409 = 1288057) B1288057
theorem B1225891 : Blo 1144635 1225891 := bstep (se 1 (by rfl) ⟨919418, by rfl⟩ : syracuseStep 1225891 = 1838837) B1838837
theorem B1717427 : Blo 1144635 1717427 := bstep (se 1 (by rfl) ⟨1288070, by rfl⟩ : syracuseStep 1717427 = 2576141) B2576141
theorem B1291459 : Blo 1144635 1291459 := bstep (se 1 (by rfl) ⟨968594, by rfl⟩ : syracuseStep 1291459 = 1937189) B1937189
theorem B1717457 : Blo 1144635 1717457 := bstep (se 2 (by rfl) ⟨644046, by rfl⟩ : syracuseStep 1717457 = 1288093) B1288093
theorem B1717475 : Blo 1144635 1717475 := bstep (se 1 (by rfl) ⟨1288106, by rfl⟩ : syracuseStep 1717475 = 2576213) B2576213
theorem B5584099 : Blo 1144635 5584099 := bstep (se 1 (by rfl) ⟨4188074, by rfl⟩ : syracuseStep 5584099 = 8376149) B8376149
theorem B1717505 : Blo 1144635 1717505 := bstep (se 2 (by rfl) ⟨644064, by rfl⟩ : syracuseStep 1717505 = 1288129) B1288129
theorem B1717523 : Blo 1144635 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B1717553 : Blo 1144635 1717553 := bstep (se 2 (by rfl) ⟨644082, by rfl⟩ : syracuseStep 1717553 = 1288165) B1288165
theorem B1717571 : Blo 1144635 1717571 := bstep (se 1 (by rfl) ⟨1288178, by rfl⟩ : syracuseStep 1717571 = 2576357) B2576357
theorem B1291603 : Blo 1144635 1291603 := bstep (se 1 (by rfl) ⟨968702, by rfl⟩ : syracuseStep 1291603 = 1937405) B1937405
theorem B1652065 : Blo 1144635 1652065 := bstep (se 2 (by rfl) ⟨619524, by rfl⟩ : syracuseStep 1652065 = 1239049) B1239049
theorem B1717601 : Blo 1144635 1717601 := bstep (se 2 (by rfl) ⟨644100, by rfl⟩ : syracuseStep 1717601 = 1288201) B1288201
theorem B1717619 : Blo 1144635 1717619 := bstep (se 1 (by rfl) ⟨1288214, by rfl⟩ : syracuseStep 1717619 = 2576429) B2576429
theorem B1717649 : Blo 1144635 1717649 := bstep (se 2 (by rfl) ⟨644118, by rfl⟩ : syracuseStep 1717649 = 1288237) B1288237
theorem B1717667 : Blo 1144635 1717667 := bstep (se 1 (by rfl) ⟨1288250, by rfl⟩ : syracuseStep 1717667 = 2576501) B2576501
theorem B1717697 : Blo 1144635 1717697 := bstep (se 2 (by rfl) ⟨644136, by rfl⟩ : syracuseStep 1717697 = 1288273) B1288273
theorem B1717715 : Blo 1144635 1717715 := bstep (se 1 (by rfl) ⟨1288286, by rfl⟩ : syracuseStep 1717715 = 2576573) B2576573
theorem B2176483 : Blo 1144635 2176483 := bstep (se 1 (by rfl) ⟨1632362, by rfl⟩ : syracuseStep 2176483 = 3264725) B3264725
theorem B1291747 : Blo 1144635 1291747 := bstep (se 1 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 1291747 = 1937621) B1937621
theorem B1717745 : Blo 1144635 1717745 := bstep (se 2 (by rfl) ⟨644154, by rfl⟩ : syracuseStep 1717745 = 1288309) B1288309
theorem B1717763 : Blo 1144635 1717763 := bstep (se 1 (by rfl) ⟨1288322, by rfl⟩ : syracuseStep 1717763 = 2576645) B2576645
theorem B1717793 : Blo 1144635 1717793 := bstep (se 2 (by rfl) ⟨644172, by rfl⟩ : syracuseStep 1717793 = 1288345) B1288345
theorem B1717811 : Blo 1144635 1717811 := bstep (se 1 (by rfl) ⟨1288358, by rfl⟩ : syracuseStep 1717811 = 2576717) B2576717
theorem B1717841 : Blo 1144635 1717841 := bstep (se 2 (by rfl) ⟨644190, by rfl⟩ : syracuseStep 1717841 = 1288381) B1288381
theorem B1717859 : Blo 1144635 1717859 := bstep (se 1 (by rfl) ⟨1288394, by rfl⟩ : syracuseStep 1717859 = 2576789) B2576789
theorem B1291891 : Blo 1144635 1291891 := bstep (se 1 (by rfl) ⟨968918, by rfl⟩ : syracuseStep 1291891 = 1937837) B1937837
theorem B1717889 : Blo 1144635 1717889 := bstep (se 2 (by rfl) ⟨644208, by rfl⟩ : syracuseStep 1717889 = 1288417) B1288417
theorem B1717907 : Blo 1144635 1717907 := bstep (se 1 (by rfl) ⟨1288430, by rfl⟩ : syracuseStep 1717907 = 2576861) B2576861
theorem B1717937 : Blo 1144635 1717937 := bstep (se 2 (by rfl) ⟨644226, by rfl⟩ : syracuseStep 1717937 = 1288453) B1288453
theorem B2897603 : Blo 1144635 2897603 := bstep (se 1 (by rfl) ⟨2173202, by rfl⟩ : syracuseStep 2897603 = 4346405) B4346405
theorem B1717955 : Blo 1144635 1717955 := bstep (se 1 (by rfl) ⟨1288466, by rfl⟩ : syracuseStep 1717955 = 2576933) B2576933
theorem B7354061 : Blo 1144635 7354061 := bstep (se 3 (by rfl) ⟨1378886, by rfl⟩ : syracuseStep 7354061 = 2757773) B2757773
theorem B1717985 : Blo 1144635 1717985 := bstep (se 2 (by rfl) ⟨644244, by rfl⟩ : syracuseStep 1717985 = 1288489) B1288489
theorem B11024099 : Blo 1144635 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B1718003 : Blo 1144635 1718003 := bstep (se 1 (by rfl) ⟨1288502, by rfl⟩ : syracuseStep 1718003 = 2577005) B2577005
theorem B1292035 : Blo 1144635 1292035 := bstep (se 1 (by rfl) ⟨969026, by rfl⟩ : syracuseStep 1292035 = 1938053) B1938053
theorem B6534917 : Blo 1144635 6534917 := bstep (se 4 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 6534917 = 1225297) B1225297
theorem B1718033 : Blo 1144635 1718033 := bstep (se 2 (by rfl) ⟨644262, by rfl⟩ : syracuseStep 1718033 = 1288525) B1288525
theorem B1718051 : Blo 1144635 1718051 := bstep (se 1 (by rfl) ⟨1288538, by rfl⟩ : syracuseStep 1718051 = 2577077) B2577077
theorem B1718081 : Blo 1144635 1718081 := bstep (se 2 (by rfl) ⟨644280, by rfl⟩ : syracuseStep 1718081 = 1288561) B1288561
theorem B1718099 : Blo 1144635 1718099 := bstep (se 1 (by rfl) ⟨1288574, by rfl⟩ : syracuseStep 1718099 = 2577149) B2577149
theorem B1718129 : Blo 1144635 1718129 := bstep (se 2 (by rfl) ⟨644298, by rfl⟩ : syracuseStep 1718129 = 1288597) B1288597
theorem B4896625 : Blo 1144635 4896625 := bstep (se 2 (by rfl) ⟨1836234, by rfl⟩ : syracuseStep 4896625 = 3672469) B3672469
theorem B1652609 : Blo 1144635 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B2897795 : Blo 1144635 2897795 := bstep (se 1 (by rfl) ⟨2173346, by rfl⟩ : syracuseStep 2897795 = 4346693) B4346693
theorem B1718147 : Blo 1144635 1718147 := bstep (se 1 (by rfl) ⟨1288610, by rfl⟩ : syracuseStep 1718147 = 2577221) B2577221
theorem B1292179 : Blo 1144635 1292179 := bstep (se 1 (by rfl) ⟨969134, by rfl⟩ : syracuseStep 1292179 = 1938269) B1938269
theorem B1718177 : Blo 1144635 1718177 := bstep (se 2 (by rfl) ⟨644316, by rfl⟩ : syracuseStep 1718177 = 1288633) B1288633
theorem B2176931 : Blo 1144635 2176931 := bstep (se 1 (by rfl) ⟨1632698, by rfl⟩ : syracuseStep 2176931 = 3265397) B3265397
theorem B5814179 : Blo 1144635 5814179 := bstep (se 1 (by rfl) ⟨4360634, by rfl⟩ : syracuseStep 5814179 = 8721269) B8721269
theorem B1718195 : Blo 1144635 1718195 := bstep (se 1 (by rfl) ⟨1288646, by rfl⟩ : syracuseStep 1718195 = 2577293) B2577293
theorem B1718225 : Blo 1144635 1718225 := bstep (se 2 (by rfl) ⟨644334, by rfl⟩ : syracuseStep 1718225 = 1288669) B1288669
theorem B1718243 : Blo 1144635 1718243 := bstep (se 1 (by rfl) ⟨1288682, by rfl⟩ : syracuseStep 1718243 = 2577365) B2577365
theorem B1718273 : Blo 1144635 1718273 := bstep (se 2 (by rfl) ⟨644352, by rfl⟩ : syracuseStep 1718273 = 1288705) B1288705
theorem B1718291 : Blo 1144635 1718291 := bstep (se 1 (by rfl) ⟨1288718, by rfl⟩ : syracuseStep 1718291 = 2577437) B2577437
theorem B1718321 : Blo 1144635 1718321 := bstep (se 2 (by rfl) ⟨644370, by rfl⟩ : syracuseStep 1718321 = 1288741) B1288741
theorem B1718339 : Blo 1144635 1718339 := bstep (se 1 (by rfl) ⟨1288754, by rfl⟩ : syracuseStep 1718339 = 2577509) B2577509
theorem B1718369 : Blo 1144635 1718369 := bstep (se 2 (by rfl) ⟨644388, by rfl⟩ : syracuseStep 1718369 = 1288777) B1288777
theorem B1718387 : Blo 1144635 1718387 := bstep (se 1 (by rfl) ⟨1288790, by rfl⟩ : syracuseStep 1718387 = 2577581) B2577581
theorem B7846021 : Blo 1144635 7846021 := bstep (se 4 (by rfl) ⟨735564, by rfl⟩ : syracuseStep 7846021 = 1471129) B1471129
theorem B1718417 : Blo 1144635 1718417 := bstep (se 2 (by rfl) ⟨644406, by rfl⟩ : syracuseStep 1718417 = 1288813) B1288813
theorem B1718435 : Blo 1144635 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B1718465 : Blo 1144635 1718465 := bstep (se 2 (by rfl) ⟨644424, by rfl⟩ : syracuseStep 1718465 = 1288849) B1288849
theorem B2177219 : Blo 1144635 2177219 := bstep (se 1 (by rfl) ⟨1632914, by rfl⟩ : syracuseStep 2177219 = 3265829) B3265829
theorem B1718483 : Blo 1144635 1718483 := bstep (se 1 (by rfl) ⟨1288862, by rfl⟩ : syracuseStep 1718483 = 2577725) B2577725
theorem B1718513 : Blo 1144635 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B1718531 : Blo 1144635 1718531 := bstep (se 1 (by rfl) ⟨1288898, by rfl⟩ : syracuseStep 1718531 = 2577797) B2577797
theorem B1718561 : Blo 1144635 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1718579 : Blo 1144635 1718579 := bstep (se 1 (by rfl) ⟨1288934, by rfl⟩ : syracuseStep 1718579 = 2577869) B2577869
theorem B1718609 : Blo 1144635 1718609 := bstep (se 2 (by rfl) ⟨644478, by rfl⟩ : syracuseStep 1718609 = 1288957) B1288957
theorem B1718627 : Blo 1144635 1718627 := bstep (se 1 (by rfl) ⟨1288970, by rfl⟩ : syracuseStep 1718627 = 2577941) B2577941
theorem B1718657 : Blo 1144635 1718657 := bstep (se 2 (by rfl) ⟨644496, by rfl⟩ : syracuseStep 1718657 = 1288993) B1288993
theorem B1718675 : Blo 1144635 1718675 := bstep (se 1 (by rfl) ⟨1289006, by rfl⟩ : syracuseStep 1718675 = 2578013) B2578013
theorem B1718705 : Blo 1144635 1718705 := bstep (se 2 (by rfl) ⟨644514, by rfl⟩ : syracuseStep 1718705 = 1289029) B1289029
theorem B1718723 : Blo 1144635 1718723 := bstep (se 1 (by rfl) ⟨1289042, by rfl⟩ : syracuseStep 1718723 = 2578085) B2578085
theorem B1718753 : Blo 1144635 1718753 := bstep (se 2 (by rfl) ⟨644532, by rfl⟩ : syracuseStep 1718753 = 1289065) B1289065
theorem B1718771 : Blo 1144635 1718771 := bstep (se 1 (by rfl) ⟨1289078, by rfl⟩ : syracuseStep 1718771 = 2578157) B2578157
theorem B11024909 : Blo 1144635 11024909 := bstep (se 3 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 11024909 = 4134341) B4134341
theorem B1718801 : Blo 1144635 1718801 := bstep (se 2 (by rfl) ⟨644550, by rfl⟩ : syracuseStep 1718801 = 1289101) B1289101
theorem B1718819 : Blo 1144635 1718819 := bstep (se 1 (by rfl) ⟨1289114, by rfl⟩ : syracuseStep 1718819 = 2578229) B2578229
theorem B1718849 : Blo 1144635 1718849 := bstep (se 2 (by rfl) ⟨644568, by rfl⟩ : syracuseStep 1718849 = 1289137) B1289137
theorem B1718867 : Blo 1144635 1718867 := bstep (se 1 (by rfl) ⟨1289150, by rfl⟩ : syracuseStep 1718867 = 2578301) B2578301
theorem B1718897 : Blo 1144635 1718897 := bstep (se 2 (by rfl) ⟨644586, by rfl⟩ : syracuseStep 1718897 = 1289173) B1289173
theorem B1718915 : Blo 1144635 1718915 := bstep (se 1 (by rfl) ⟨1289186, by rfl⟩ : syracuseStep 1718915 = 2578373) B2578373
theorem B1718945 : Blo 1144635 1718945 := bstep (se 2 (by rfl) ⟨644604, by rfl⟩ : syracuseStep 1718945 = 1289209) B1289209
theorem B1718963 : Blo 1144635 1718963 := bstep (se 1 (by rfl) ⟨1289222, by rfl⟩ : syracuseStep 1718963 = 2578445) B2578445
theorem B1718993 : Blo 1144635 1718993 := bstep (se 2 (by rfl) ⟨644622, by rfl⟩ : syracuseStep 1718993 = 1289245) B1289245
theorem B1719011 : Blo 1144635 1719011 := bstep (se 1 (by rfl) ⟨1289258, by rfl⟩ : syracuseStep 1719011 = 2578517) B2578517
theorem B1719041 : Blo 1144635 1719041 := bstep (se 2 (by rfl) ⟨644640, by rfl⟩ : syracuseStep 1719041 = 1289281) B1289281
theorem B1719059 : Blo 1144635 1719059 := bstep (se 1 (by rfl) ⟨1289294, by rfl⟩ : syracuseStep 1719059 = 2578589) B2578589
theorem B2898737 : Blo 1144635 2898737 := bstep (se 2 (by rfl) ⟨1087026, by rfl⟩ : syracuseStep 2898737 = 2174053) B2174053
theorem B1719089 : Blo 1144635 1719089 := bstep (se 2 (by rfl) ⟨644658, by rfl⟩ : syracuseStep 1719089 = 1289317) B1289317
theorem B1719107 : Blo 1144635 1719107 := bstep (se 1 (by rfl) ⟨1289330, by rfl⟩ : syracuseStep 1719107 = 2578661) B2578661
theorem B6208325 : Blo 1144635 6208325 := bstep (se 4 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 6208325 = 1164061) B1164061
theorem B1719137 : Blo 1144635 1719137 := bstep (se 2 (by rfl) ⟨644676, by rfl⟩ : syracuseStep 1719137 = 1289353) B1289353
theorem B2898787 : Blo 1144635 2898787 := bstep (se 1 (by rfl) ⟨2174090, by rfl⟩ : syracuseStep 2898787 = 4348181) B4348181
theorem B1719155 : Blo 1144635 1719155 := bstep (se 1 (by rfl) ⟨1289366, by rfl⟩ : syracuseStep 1719155 = 2578733) B2578733
theorem B1719185 : Blo 1144635 1719185 := bstep (se 2 (by rfl) ⟨644694, by rfl⟩ : syracuseStep 1719185 = 1289389) B1289389
theorem B1719203 : Blo 1144635 1719203 := bstep (se 1 (by rfl) ⟨1289402, by rfl⟩ : syracuseStep 1719203 = 2578805) B2578805
theorem B1719233 : Blo 1144635 1719233 := bstep (se 2 (by rfl) ⟨644712, by rfl⟩ : syracuseStep 1719233 = 1289425) B1289425
theorem B1719251 : Blo 1144635 1719251 := bstep (se 1 (by rfl) ⟨1289438, by rfl⟩ : syracuseStep 1719251 = 2578877) B2578877
theorem B2898929 : Blo 1144635 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B1719281 : Blo 1144635 1719281 := bstep (se 2 (by rfl) ⟨644730, by rfl⟩ : syracuseStep 1719281 = 1289461) B1289461
theorem B1719299 : Blo 1144635 1719299 := bstep (se 1 (by rfl) ⟨1289474, by rfl⟩ : syracuseStep 1719299 = 2578949) B2578949
theorem B1719329 : Blo 1144635 1719329 := bstep (se 2 (by rfl) ⟨644748, by rfl⟩ : syracuseStep 1719329 = 1289497) B1289497
theorem B1719347 : Blo 1144635 1719347 := bstep (se 1 (by rfl) ⟨1289510, by rfl⟩ : syracuseStep 1719347 = 2579021) B2579021
theorem B1719377 : Blo 1144635 1719377 := bstep (se 2 (by rfl) ⟨644766, by rfl⟩ : syracuseStep 1719377 = 1289533) B1289533
theorem B1719395 : Blo 1144635 1719395 := bstep (se 1 (by rfl) ⟨1289546, by rfl⟩ : syracuseStep 1719395 = 2579093) B2579093
theorem B2178161 : Blo 1144635 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B1719425 : Blo 1144635 1719425 := bstep (se 2 (by rfl) ⟨644784, by rfl⟩ : syracuseStep 1719425 = 1289569) B1289569
theorem B1719443 : Blo 1144635 1719443 := bstep (se 1 (by rfl) ⟨1289582, by rfl⟩ : syracuseStep 1719443 = 2579165) B2579165
theorem B3259565 : Blo 1144635 3259565 := bstep (se 3 (by rfl) ⟨611168, by rfl⟩ : syracuseStep 3259565 = 1222337) B1222337
theorem B1719473 : Blo 1144635 1719473 := bstep (se 2 (by rfl) ⟨644802, by rfl⟩ : syracuseStep 1719473 = 1289605) B1289605
theorem B1719491 : Blo 1144635 1719491 := bstep (se 1 (by rfl) ⟨1289618, by rfl⟩ : syracuseStep 1719491 = 2579237) B2579237
theorem B1719521 : Blo 1144635 1719521 := bstep (se 2 (by rfl) ⟨644820, by rfl⟩ : syracuseStep 1719521 = 1289641) B1289641
theorem B1719539 : Blo 1144635 1719539 := bstep (se 1 (by rfl) ⟨1289654, by rfl⟩ : syracuseStep 1719539 = 2579309) B2579309
theorem B1719569 : Blo 1144635 1719569 := bstep (se 2 (by rfl) ⟨644838, by rfl⟩ : syracuseStep 1719569 = 1289677) B1289677
theorem B1719587 : Blo 1144635 1719587 := bstep (se 1 (by rfl) ⟨1289690, by rfl⟩ : syracuseStep 1719587 = 2579381) B2579381
theorem B1719617 : Blo 1144635 1719617 := bstep (se 2 (by rfl) ⟨644856, by rfl⟩ : syracuseStep 1719617 = 1289713) B1289713
theorem B1719635 : Blo 1144635 1719635 := bstep (se 1 (by rfl) ⟨1289726, by rfl⟩ : syracuseStep 1719635 = 2579453) B2579453
theorem B1719665 : Blo 1144635 1719665 := bstep (se 2 (by rfl) ⟨644874, by rfl⟩ : syracuseStep 1719665 = 1289749) B1289749
theorem B1719683 : Blo 1144635 1719683 := bstep (se 1 (by rfl) ⟨1289762, by rfl⟩ : syracuseStep 1719683 = 2579525) B2579525
theorem B1719713 : Blo 1144635 1719713 := bstep (se 2 (by rfl) ⟨644892, by rfl⟩ : syracuseStep 1719713 = 1289785) B1289785
theorem B1719731 : Blo 1144635 1719731 := bstep (se 1 (by rfl) ⟨1289798, by rfl⟩ : syracuseStep 1719731 = 2579597) B2579597
theorem B1719761 : Blo 1144635 1719761 := bstep (se 2 (by rfl) ⟨644910, by rfl⟩ : syracuseStep 1719761 = 1289821) B1289821
theorem B1719779 : Blo 1144635 1719779 := bstep (se 1 (by rfl) ⟨1289834, by rfl⟩ : syracuseStep 1719779 = 2579669) B2579669
theorem B1719809 : Blo 1144635 1719809 := bstep (se 2 (by rfl) ⟨644928, by rfl⟩ : syracuseStep 1719809 = 1289857) B1289857
theorem B1719827 : Blo 1144635 1719827 := bstep (se 1 (by rfl) ⟨1289870, by rfl⟩ : syracuseStep 1719827 = 2579741) B2579741
theorem B1719857 : Blo 1144635 1719857 := bstep (se 2 (by rfl) ⟨644946, by rfl⟩ : syracuseStep 1719857 = 1289893) B1289893
theorem B1719875 : Blo 1144635 1719875 := bstep (se 1 (by rfl) ⟨1289906, by rfl⟩ : syracuseStep 1719875 = 2579813) B2579813
theorem B1719905 : Blo 1144635 1719905 := bstep (se 2 (by rfl) ⟨644964, by rfl⟩ : syracuseStep 1719905 = 1289929) B1289929
theorem B1719923 : Blo 1144635 1719923 := bstep (se 1 (by rfl) ⟨1289942, by rfl⟩ : syracuseStep 1719923 = 2579885) B2579885
theorem B1719953 : Blo 1144635 1719953 := bstep (se 2 (by rfl) ⟨644982, by rfl⟩ : syracuseStep 1719953 = 1289965) B1289965
theorem B1719971 : Blo 1144635 1719971 := bstep (se 1 (by rfl) ⟨1289978, by rfl⟩ : syracuseStep 1719971 = 2579957) B2579957
theorem B1720001 : Blo 1144635 1720001 := bstep (se 2 (by rfl) ⟨645000, by rfl⟩ : syracuseStep 1720001 = 1290001) B1290001
theorem B1720019 : Blo 1144635 1720019 := bstep (se 1 (by rfl) ⟨1290014, by rfl⟩ : syracuseStep 1720019 = 2580029) B2580029
theorem B1720049 : Blo 1144635 1720049 := bstep (se 2 (by rfl) ⟨645018, by rfl⟩ : syracuseStep 1720049 = 1290037) B1290037
theorem B1720067 : Blo 1144635 1720067 := bstep (se 1 (by rfl) ⟨1290050, by rfl⟩ : syracuseStep 1720067 = 2580101) B2580101
theorem B1720097 : Blo 1144635 1720097 := bstep (se 2 (by rfl) ⟨645036, by rfl⟩ : syracuseStep 1720097 = 1290073) B1290073
theorem B6209315 : Blo 1144635 6209315 := bstep (se 1 (by rfl) ⟨4656986, by rfl⟩ : syracuseStep 6209315 = 9313973) B9313973
theorem B1720115 : Blo 1144635 1720115 := bstep (se 1 (by rfl) ⟨1290086, by rfl⟩ : syracuseStep 1720115 = 2580173) B2580173
theorem B1720145 : Blo 1144635 1720145 := bstep (se 2 (by rfl) ⟨645054, by rfl⟩ : syracuseStep 1720145 = 1290109) B1290109
theorem B1720163 : Blo 1144635 1720163 := bstep (se 1 (by rfl) ⟨1290122, by rfl⟩ : syracuseStep 1720163 = 2580245) B2580245
theorem B1720193 : Blo 1144635 1720193 := bstep (se 2 (by rfl) ⟨645072, by rfl⟩ : syracuseStep 1720193 = 1290145) B1290145
theorem B1720211 : Blo 1144635 1720211 := bstep (se 1 (by rfl) ⟨1290158, by rfl⟩ : syracuseStep 1720211 = 2580317) B2580317
theorem B1720241 : Blo 1144635 1720241 := bstep (se 2 (by rfl) ⟨645090, by rfl⟩ : syracuseStep 1720241 = 1290181) B1290181
theorem B1720259 : Blo 1144635 1720259 := bstep (se 1 (by rfl) ⟨1290194, by rfl⟩ : syracuseStep 1720259 = 2580389) B2580389
theorem B2899921 : Blo 1144635 2899921 := bstep (se 2 (by rfl) ⟨1087470, by rfl⟩ : syracuseStep 2899921 = 2174941) B2174941
theorem B1720289 : Blo 1144635 1720289 := bstep (se 2 (by rfl) ⟨645108, by rfl⟩ : syracuseStep 1720289 = 1290217) B1290217
theorem B2179057 : Blo 1144635 2179057 := bstep (se 2 (by rfl) ⟨817146, by rfl⟩ : syracuseStep 2179057 = 1634293) B1634293
theorem B1720307 : Blo 1144635 1720307 := bstep (se 1 (by rfl) ⟨1290230, by rfl⟩ : syracuseStep 1720307 = 2580461) B2580461
theorem B1720337 : Blo 1144635 1720337 := bstep (se 2 (by rfl) ⟨645126, by rfl⟩ : syracuseStep 1720337 = 1290253) B1290253
theorem B5881891 : Blo 1144635 5881891 := bstep (se 1 (by rfl) ⟨4411418, by rfl⟩ : syracuseStep 5881891 = 8822837) B8822837
theorem B1720355 : Blo 1144635 1720355 := bstep (se 1 (by rfl) ⟨1290266, by rfl⟩ : syracuseStep 1720355 = 2580533) B2580533
theorem B1720385 : Blo 1144635 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B1720403 : Blo 1144635 1720403 := bstep (se 1 (by rfl) ⟨1290302, by rfl⟩ : syracuseStep 1720403 = 2580605) B2580605
theorem B42942577 : Blo 1144635 42942577 := bstep (se 2 (by rfl) ⟨16103466, by rfl⟩ : syracuseStep 42942577 = 32206933) B32206933
theorem B1720433 : Blo 1144635 1720433 := bstep (se 2 (by rfl) ⟨645162, by rfl⟩ : syracuseStep 1720433 = 1290325) B1290325
theorem B1720451 : Blo 1144635 1720451 := bstep (se 1 (by rfl) ⟨1290338, by rfl⟩ : syracuseStep 1720451 = 2580677) B2580677
theorem B2179217 : Blo 1144635 2179217 := bstep (se 2 (by rfl) ⟨817206, by rfl⟩ : syracuseStep 2179217 = 1634413) B1634413
theorem B1720481 : Blo 1144635 1720481 := bstep (se 2 (by rfl) ⟨645180, by rfl⟩ : syracuseStep 1720481 = 1290361) B1290361
theorem B1720499 : Blo 1144635 1720499 := bstep (se 1 (by rfl) ⟨1290374, by rfl⟩ : syracuseStep 1720499 = 2580749) B2580749
theorem B1720529 : Blo 1144635 1720529 := bstep (se 2 (by rfl) ⟨645198, by rfl⟩ : syracuseStep 1720529 = 1290397) B1290397
theorem B2900195 : Blo 1144635 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B1720547 : Blo 1144635 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B1720577 : Blo 1144635 1720577 := bstep (se 2 (by rfl) ⟨645216, by rfl⟩ : syracuseStep 1720577 = 1290433) B1290433
theorem B1720595 : Blo 1144635 1720595 := bstep (se 1 (by rfl) ⟨1290446, by rfl⟩ : syracuseStep 1720595 = 2580893) B2580893
theorem B1720625 : Blo 1144635 1720625 := bstep (se 2 (by rfl) ⟨645234, by rfl⟩ : syracuseStep 1720625 = 1290469) B1290469
theorem B1720643 : Blo 1144635 1720643 := bstep (se 1 (by rfl) ⟨1290482, by rfl⟩ : syracuseStep 1720643 = 2580965) B2580965
theorem B3260749 : Blo 1144635 3260749 := bstep (se 3 (by rfl) ⟨611390, by rfl⟩ : syracuseStep 3260749 = 1222781) B1222781
theorem B1720673 : Blo 1144635 1720673 := bstep (se 2 (by rfl) ⟨645252, by rfl⟩ : syracuseStep 1720673 = 1290505) B1290505
theorem B1720691 : Blo 1144635 1720691 := bstep (se 1 (by rfl) ⟨1290518, by rfl⟩ : syracuseStep 1720691 = 2581037) B2581037
theorem B1720721 : Blo 1144635 1720721 := bstep (se 2 (by rfl) ⟨645270, by rfl⟩ : syracuseStep 1720721 = 1290541) B1290541
theorem B2900387 : Blo 1144635 2900387 := bstep (se 1 (by rfl) ⟨2175290, by rfl⟩ : syracuseStep 2900387 = 4350581) B4350581
theorem B1720739 : Blo 1144635 1720739 := bstep (se 1 (by rfl) ⟨1290554, by rfl⟩ : syracuseStep 1720739 = 2581109) B2581109
theorem B1720769 : Blo 1144635 1720769 := bstep (se 2 (by rfl) ⟨645288, by rfl⟩ : syracuseStep 1720769 = 1290577) B1290577
theorem B12566981 : Blo 1144635 12566981 := bstep (se 4 (by rfl) ⟨1178154, by rfl⟩ : syracuseStep 12566981 = 2356309) B2356309
theorem B1720787 : Blo 1144635 1720787 := bstep (se 1 (by rfl) ⟨1290590, by rfl⟩ : syracuseStep 1720787 = 2581181) B2581181
theorem B5882339 : Blo 1144635 5882339 := bstep (se 1 (by rfl) ⟨4411754, by rfl⟩ : syracuseStep 5882339 = 8823509) B8823509
theorem B1720817 : Blo 1144635 1720817 := bstep (se 2 (by rfl) ⟨645306, by rfl⟩ : syracuseStep 1720817 = 1290613) B1290613
theorem B1720835 : Blo 1144635 1720835 := bstep (se 1 (by rfl) ⟨1290626, by rfl⟩ : syracuseStep 1720835 = 2581253) B2581253
theorem B1720865 : Blo 1144635 1720865 := bstep (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) B1290649
theorem B2179619 : Blo 1144635 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B3097133 : Blo 1144635 3097133 := bstep (se 3 (by rfl) ⟨580712, by rfl⟩ : syracuseStep 3097133 = 1161425) B1161425
theorem B1720883 : Blo 1144635 1720883 := bstep (se 1 (by rfl) ⟨1290662, by rfl⟩ : syracuseStep 1720883 = 2581325) B2581325
theorem B1720913 : Blo 1144635 1720913 := bstep (se 2 (by rfl) ⟨645342, by rfl⟩ : syracuseStep 1720913 = 1290685) B1290685
theorem B1720931 : Blo 1144635 1720931 := bstep (se 1 (by rfl) ⟨1290698, by rfl⟩ : syracuseStep 1720931 = 2581397) B2581397
theorem B1720961 : Blo 1144635 1720961 := bstep (se 2 (by rfl) ⟨645360, by rfl⟩ : syracuseStep 1720961 = 1290721) B1290721
theorem B1720979 : Blo 1144635 1720979 := bstep (se 1 (by rfl) ⟨1290734, by rfl⟩ : syracuseStep 1720979 = 2581469) B2581469
theorem B1721009 : Blo 1144635 1721009 := bstep (se 2 (by rfl) ⟨645378, by rfl⟩ : syracuseStep 1721009 = 1290757) B1290757
theorem B1721027 : Blo 1144635 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B1721057 : Blo 1144635 1721057 := bstep (se 2 (by rfl) ⟨645396, by rfl⟩ : syracuseStep 1721057 = 1290793) B1290793
theorem B1721075 : Blo 1144635 1721075 := bstep (se 1 (by rfl) ⟨1290806, by rfl⟩ : syracuseStep 1721075 = 2581613) B2581613
theorem B7357189 : Blo 1144635 7357189 := bstep (se 4 (by rfl) ⟨689736, by rfl⟩ : syracuseStep 7357189 = 1379473) B1379473
theorem B1721105 : Blo 1144635 1721105 := bstep (se 2 (by rfl) ⟨645414, by rfl⟩ : syracuseStep 1721105 = 1290829) B1290829
theorem B1721123 : Blo 1144635 1721123 := bstep (se 1 (by rfl) ⟨1290842, by rfl⟩ : syracuseStep 1721123 = 2581685) B2581685
theorem B1721153 : Blo 1144635 1721153 := bstep (se 2 (by rfl) ⟨645432, by rfl⟩ : syracuseStep 1721153 = 1290865) B1290865
theorem B1721171 : Blo 1144635 1721171 := bstep (se 1 (by rfl) ⟨1290878, by rfl⟩ : syracuseStep 1721171 = 2581757) B2581757
theorem B1721201 : Blo 1144635 1721201 := bstep (se 2 (by rfl) ⟨645450, by rfl⟩ : syracuseStep 1721201 = 1290901) B1290901
theorem B1721219 : Blo 1144635 1721219 := bstep (se 1 (by rfl) ⟨1290914, by rfl⟩ : syracuseStep 1721219 = 2581829) B2581829
theorem B1164179 : Blo 1144635 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B1721249 : Blo 1144635 1721249 := bstep (se 2 (by rfl) ⟨645468, by rfl⟩ : syracuseStep 1721249 = 1290937) B1290937
theorem B1721267 : Blo 1144635 1721267 := bstep (se 1 (by rfl) ⟨1290950, by rfl⟩ : syracuseStep 1721267 = 2581901) B2581901
theorem B1721297 : Blo 1144635 1721297 := bstep (se 2 (by rfl) ⟨645486, by rfl⟩ : syracuseStep 1721297 = 1290973) B1290973
theorem B1721315 : Blo 1144635 1721315 := bstep (se 1 (by rfl) ⟨1290986, by rfl⟩ : syracuseStep 1721315 = 2581973) B2581973
theorem B1721345 : Blo 1144635 1721345 := bstep (se 2 (by rfl) ⟨645504, by rfl⟩ : syracuseStep 1721345 = 1291009) B1291009
theorem B1721363 : Blo 1144635 1721363 := bstep (se 1 (by rfl) ⟨1291022, by rfl⟩ : syracuseStep 1721363 = 2582045) B2582045
theorem B1721393 : Blo 1144635 1721393 := bstep (se 2 (by rfl) ⟨645522, by rfl⟩ : syracuseStep 1721393 = 1291045) B1291045
theorem B1721411 : Blo 1144635 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B1721441 : Blo 1144635 1721441 := bstep (se 2 (by rfl) ⟨645540, by rfl⟩ : syracuseStep 1721441 = 1291081) B1291081
theorem B1721459 : Blo 1144635 1721459 := bstep (se 1 (by rfl) ⟨1291094, by rfl⟩ : syracuseStep 1721459 = 2582189) B2582189
theorem B1721489 : Blo 1144635 1721489 := bstep (se 2 (by rfl) ⟨645558, by rfl⟩ : syracuseStep 1721489 = 1291117) B1291117
theorem B1721507 : Blo 1144635 1721507 := bstep (se 1 (by rfl) ⟨1291130, by rfl⟩ : syracuseStep 1721507 = 2582261) B2582261
theorem B1721537 : Blo 1144635 1721537 := bstep (se 2 (by rfl) ⟨645576, by rfl⟩ : syracuseStep 1721537 = 1291153) B1291153
theorem B1721555 : Blo 1144635 1721555 := bstep (se 1 (by rfl) ⟨1291166, by rfl⟩ : syracuseStep 1721555 = 2582333) B2582333
theorem B1721585 : Blo 1144635 1721585 := bstep (se 2 (by rfl) ⟨645594, by rfl⟩ : syracuseStep 1721585 = 1291189) B1291189
theorem B1721603 : Blo 1144635 1721603 := bstep (se 1 (by rfl) ⟨1291202, by rfl⟩ : syracuseStep 1721603 = 2582405) B2582405
theorem B1721633 : Blo 1144635 1721633 := bstep (se 2 (by rfl) ⟨645612, by rfl⟩ : syracuseStep 1721633 = 1291225) B1291225
theorem B1721651 : Blo 1144635 1721651 := bstep (se 1 (by rfl) ⟨1291238, by rfl⟩ : syracuseStep 1721651 = 2582477) B2582477
theorem B2901329 : Blo 1144635 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1721681 : Blo 1144635 1721681 := bstep (se 2 (by rfl) ⟨645630, by rfl⟩ : syracuseStep 1721681 = 1291261) B1291261
theorem B1721699 : Blo 1144635 1721699 := bstep (se 1 (by rfl) ⟨1291274, by rfl⟩ : syracuseStep 1721699 = 2582549) B2582549
theorem B3261809 : Blo 1144635 3261809 := bstep (se 2 (by rfl) ⟨1223178, by rfl⟩ : syracuseStep 3261809 = 2446357) B2446357
theorem B1721729 : Blo 1144635 1721729 := bstep (se 2 (by rfl) ⟨645648, by rfl⟩ : syracuseStep 1721729 = 1291297) B1291297
theorem B2901379 : Blo 1144635 2901379 := bstep (se 1 (by rfl) ⟨2176034, by rfl⟩ : syracuseStep 2901379 = 4352069) B4352069
theorem B1721747 : Blo 1144635 1721747 := bstep (se 1 (by rfl) ⟨1291310, by rfl⟩ : syracuseStep 1721747 = 2582621) B2582621
theorem B2180515 : Blo 1144635 2180515 := bstep (se 1 (by rfl) ⟨1635386, by rfl⟩ : syracuseStep 2180515 = 3270773) B3270773
theorem B1721777 : Blo 1144635 1721777 := bstep (se 2 (by rfl) ⟨645666, by rfl⟩ : syracuseStep 1721777 = 1291333) B1291333
theorem B1721795 : Blo 1144635 1721795 := bstep (se 1 (by rfl) ⟨1291346, by rfl⟩ : syracuseStep 1721795 = 2582693) B2582693
theorem B1721825 : Blo 1144635 1721825 := bstep (se 2 (by rfl) ⟨645684, by rfl⟩ : syracuseStep 1721825 = 1291369) B1291369
theorem B1721843 : Blo 1144635 1721843 := bstep (se 1 (by rfl) ⟨1291382, by rfl⟩ : syracuseStep 1721843 = 2582765) B2582765
theorem B6538765 : Blo 1144635 6538765 := bstep (se 3 (by rfl) ⟨1226018, by rfl⟩ : syracuseStep 6538765 = 2452037) B2452037
theorem B2901521 : Blo 1144635 2901521 := bstep (se 2 (by rfl) ⟨1088070, by rfl⟩ : syracuseStep 2901521 = 2176141) B2176141
theorem B1721873 : Blo 1144635 1721873 := bstep (se 2 (by rfl) ⟨645702, by rfl⟩ : syracuseStep 1721873 = 1291405) B1291405
theorem B1721891 : Blo 1144635 1721891 := bstep (se 1 (by rfl) ⟨1291418, by rfl⟩ : syracuseStep 1721891 = 2582837) B2582837
theorem B1721921 : Blo 1144635 1721921 := bstep (se 2 (by rfl) ⟨645720, by rfl⟩ : syracuseStep 1721921 = 1291441) B1291441
theorem B1721939 : Blo 1144635 1721939 := bstep (se 1 (by rfl) ⟨1291454, by rfl⟩ : syracuseStep 1721939 = 2582909) B2582909
theorem B1721969 : Blo 1144635 1721969 := bstep (se 2 (by rfl) ⟨645738, by rfl⟩ : syracuseStep 1721969 = 1291477) B1291477
theorem B1721987 : Blo 1144635 1721987 := bstep (se 1 (by rfl) ⟨1291490, by rfl⟩ : syracuseStep 1721987 = 2582981) B2582981
theorem B1722017 : Blo 1144635 1722017 := bstep (se 2 (by rfl) ⟨645756, by rfl⟩ : syracuseStep 1722017 = 1291513) B1291513
theorem B1722035 : Blo 1144635 1722035 := bstep (se 1 (by rfl) ⟨1291526, by rfl⟩ : syracuseStep 1722035 = 2583053) B2583053
theorem B1722065 : Blo 1144635 1722065 := bstep (se 2 (by rfl) ⟨645774, by rfl⟩ : syracuseStep 1722065 = 1291549) B1291549
theorem B1722083 : Blo 1144635 1722083 := bstep (se 1 (by rfl) ⟨1291562, by rfl⟩ : syracuseStep 1722083 = 2583125) B2583125
theorem B1722113 : Blo 1144635 1722113 := bstep (se 2 (by rfl) ⟨645792, by rfl⟩ : syracuseStep 1722113 = 1291585) B1291585
theorem B1722131 : Blo 1144635 1722131 := bstep (se 1 (by rfl) ⟨1291598, by rfl⟩ : syracuseStep 1722131 = 2583197) B2583197
theorem B4900657 : Blo 1144635 4900657 := bstep (se 2 (by rfl) ⟨1837746, by rfl⟩ : syracuseStep 4900657 = 3675493) B3675493
theorem B1656625 : Blo 1144635 1656625 := bstep (se 2 (by rfl) ⟨621234, by rfl⟩ : syracuseStep 1656625 = 1242469) B1242469
theorem B1722161 : Blo 1144635 1722161 := bstep (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) B1291621
theorem B1722179 : Blo 1144635 1722179 := bstep (se 1 (by rfl) ⟨1291634, by rfl⟩ : syracuseStep 1722179 = 2583269) B2583269
theorem B1722209 : Blo 1144635 1722209 := bstep (se 2 (by rfl) ⟨645828, by rfl⟩ : syracuseStep 1722209 = 1291657) B1291657
theorem B1722227 : Blo 1144635 1722227 := bstep (se 1 (by rfl) ⟨1291670, by rfl⟩ : syracuseStep 1722227 = 2583341) B2583341
theorem B1722257 : Blo 1144635 1722257 := bstep (se 2 (by rfl) ⟨645846, by rfl⟩ : syracuseStep 1722257 = 1291693) B1291693
theorem B1722275 : Blo 1144635 1722275 := bstep (se 1 (by rfl) ⟨1291706, by rfl⟩ : syracuseStep 1722275 = 2583413) B2583413
theorem B1886129 : Blo 1144635 1886129 := bstep (se 2 (by rfl) ⟨707298, by rfl⟩ : syracuseStep 1886129 = 1414597) B1414597
theorem B1722305 : Blo 1144635 1722305 := bstep (se 2 (by rfl) ⟨645864, by rfl⟩ : syracuseStep 1722305 = 1291729) B1291729
theorem B1722323 : Blo 1144635 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B1722353 : Blo 1144635 1722353 := bstep (se 2 (by rfl) ⟨645882, by rfl⟩ : syracuseStep 1722353 = 1291765) B1291765
theorem B1722371 : Blo 1144635 1722371 := bstep (se 1 (by rfl) ⟨1291778, by rfl⟩ : syracuseStep 1722371 = 2583557) B2583557
theorem B3262481 : Blo 1144635 3262481 := bstep (se 2 (by rfl) ⟨1223430, by rfl⟩ : syracuseStep 3262481 = 2446861) B2446861
theorem B1722401 : Blo 1144635 1722401 := bstep (se 2 (by rfl) ⟨645900, by rfl⟩ : syracuseStep 1722401 = 1291801) B1291801
theorem B1722419 : Blo 1144635 1722419 := bstep (se 1 (by rfl) ⟨1291814, by rfl⟩ : syracuseStep 1722419 = 2583629) B2583629
theorem B1722449 : Blo 1144635 1722449 := bstep (se 2 (by rfl) ⟨645918, by rfl⟩ : syracuseStep 1722449 = 1291837) B1291837
theorem B1722467 : Blo 1144635 1722467 := bstep (se 1 (by rfl) ⟨1291850, by rfl⟩ : syracuseStep 1722467 = 2583701) B2583701
theorem B1722497 : Blo 1144635 1722497 := bstep (se 2 (by rfl) ⟨645936, by rfl⟩ : syracuseStep 1722497 = 1291873) B1291873
theorem B1722515 : Blo 1144635 1722515 := bstep (se 1 (by rfl) ⟨1291886, by rfl⟩ : syracuseStep 1722515 = 2583773) B2583773
theorem B1722545 : Blo 1144635 1722545 := bstep (se 2 (by rfl) ⟨645954, by rfl⟩ : syracuseStep 1722545 = 1291909) B1291909
theorem B1722563 : Blo 1144635 1722563 := bstep (se 1 (by rfl) ⟨1291922, by rfl⟩ : syracuseStep 1722563 = 2583845) B2583845
theorem B1722593 : Blo 1144635 1722593 := bstep (se 2 (by rfl) ⟨645972, by rfl⟩ : syracuseStep 1722593 = 1291945) B1291945
theorem B1722611 : Blo 1144635 1722611 := bstep (se 1 (by rfl) ⟨1291958, by rfl⟩ : syracuseStep 1722611 = 2583917) B2583917
theorem B1722641 : Blo 1144635 1722641 := bstep (se 2 (by rfl) ⟨645990, by rfl⟩ : syracuseStep 1722641 = 1291981) B1291981
theorem B1722659 : Blo 1144635 1722659 := bstep (se 1 (by rfl) ⟨1291994, by rfl⟩ : syracuseStep 1722659 = 2583989) B2583989
theorem B1722689 : Blo 1144635 1722689 := bstep (se 2 (by rfl) ⟨646008, by rfl⟩ : syracuseStep 1722689 = 1292017) B1292017
theorem B1722707 : Blo 1144635 1722707 := bstep (se 1 (by rfl) ⟨1292030, by rfl⟩ : syracuseStep 1722707 = 2584061) B2584061
theorem B1722737 : Blo 1144635 1722737 := bstep (se 2 (by rfl) ⟨646026, by rfl⟩ : syracuseStep 1722737 = 1292053) B1292053
theorem B1722755 : Blo 1144635 1722755 := bstep (se 1 (by rfl) ⟨1292066, by rfl⟩ : syracuseStep 1722755 = 2584133) B2584133
theorem B1395091 : Blo 1144635 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B1722785 : Blo 1144635 1722785 := bstep (se 2 (by rfl) ⟨646044, by rfl⟩ : syracuseStep 1722785 = 1292089) B1292089
theorem B1722803 : Blo 1144635 1722803 := bstep (se 1 (by rfl) ⟨1292102, by rfl⟩ : syracuseStep 1722803 = 2584205) B2584205
theorem B1722833 : Blo 1144635 1722833 := bstep (se 2 (by rfl) ⟨646062, by rfl⟩ : syracuseStep 1722833 = 1292125) B1292125
theorem B1722851 : Blo 1144635 1722851 := bstep (se 1 (by rfl) ⟨1292138, by rfl⟩ : syracuseStep 1722851 = 2584277) B2584277
theorem B2902513 : Blo 1144635 2902513 := bstep (se 2 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 2902513 = 2176885) B2176885
theorem B1722881 : Blo 1144635 1722881 := bstep (se 2 (by rfl) ⟨646080, by rfl⟩ : syracuseStep 1722881 = 1292161) B1292161
theorem B10471949 : Blo 1144635 10471949 := bstep (se 3 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 10471949 = 3926981) B3926981
theorem B1722899 : Blo 1144635 1722899 := bstep (se 1 (by rfl) ⟨1292174, by rfl⟩ : syracuseStep 1722899 = 2584349) B2584349
theorem B1722929 : Blo 1144635 1722929 := bstep (se 2 (by rfl) ⟨646098, by rfl⟩ : syracuseStep 1722929 = 1292197) B1292197
theorem B1722947 : Blo 1144635 1722947 := bstep (se 1 (by rfl) ⟨1292210, by rfl⟩ : syracuseStep 1722947 = 2584421) B2584421
theorem B2902787 : Blo 1144635 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B3263267 : Blo 1144635 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B2902979 : Blo 1144635 2902979 := bstep (se 1 (by rfl) ⟨2177234, by rfl⟩ : syracuseStep 2902979 = 4354469) B4354469
theorem B3263597 : Blo 1144635 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B7457933 : Blo 1144635 7457933 := bstep (se 3 (by rfl) ⟨1398362, by rfl⟩ : syracuseStep 7457933 = 2796725) B2796725
theorem B3263665 : Blo 1144635 3263665 := bstep (se 2 (by rfl) ⟨1223874, by rfl⟩ : syracuseStep 3263665 = 2447749) B2447749
theorem B14699717 : Blo 1144635 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B2575601 : Blo 1144635 2575601 := bstep (se 2 (by rfl) ⟨965850, by rfl⟩ : syracuseStep 2575601 = 1931701) B1931701
theorem B2575619 : Blo 1144635 2575619 := bstep (se 1 (by rfl) ⟨1931714, by rfl⟩ : syracuseStep 2575619 = 3863429) B3863429
theorem B3263939 : Blo 1144635 3263939 := bstep (se 1 (by rfl) ⟨2447954, by rfl⟩ : syracuseStep 3263939 = 4895909) B4895909
theorem B6540749 : Blo 1144635 6540749 := bstep (se 3 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 6540749 = 2452781) B2452781
theorem B3919373 : Blo 1144635 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B2575889 : Blo 1144635 2575889 := bstep (se 2 (by rfl) ⟨965958, by rfl⟩ : syracuseStep 2575889 = 1931917) B1931917
theorem B2575907 : Blo 1144635 2575907 := bstep (se 1 (by rfl) ⟨1931930, by rfl⟩ : syracuseStep 2575907 = 3863861) B3863861
theorem B2445059 : Blo 1144635 2445059 := bstep (se 1 (by rfl) ⟨1833794, by rfl⟩ : syracuseStep 2445059 = 3667589) B3667589
theorem B2576177 : Blo 1144635 2576177 := bstep (se 2 (by rfl) ⟨966066, by rfl⟩ : syracuseStep 2576177 = 1932133) B1932133
theorem B2576195 : Blo 1144635 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B2445169 : Blo 1144635 2445169 := bstep (se 2 (by rfl) ⟨916938, by rfl⟩ : syracuseStep 2445169 = 1833877) B1833877
theorem B2903921 : Blo 1144635 2903921 := bstep (se 2 (by rfl) ⟨1088970, by rfl⟩ : syracuseStep 2903921 = 2177941) B2177941
theorem B2903971 : Blo 1144635 2903971 := bstep (se 1 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 2903971 = 4355957) B4355957
theorem B2904113 : Blo 1144635 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B2576465 : Blo 1144635 2576465 := bstep (se 2 (by rfl) ⟨966174, by rfl⟩ : syracuseStep 2576465 = 1932349) B1932349
theorem B2576483 : Blo 1144635 2576483 := bstep (se 1 (by rfl) ⟨1932362, by rfl⟩ : syracuseStep 2576483 = 3864725) B3864725
theorem B3264781 : Blo 1144635 3264781 := bstep (se 3 (by rfl) ⟨612146, by rfl⟩ : syracuseStep 3264781 = 1224293) B1224293
theorem B2576753 : Blo 1144635 2576753 := bstep (se 2 (by rfl) ⟨966282, by rfl⟩ : syracuseStep 2576753 = 1932565) B1932565
theorem B6541681 : Blo 1144635 6541681 := bstep (se 2 (by rfl) ⟨2453130, by rfl⟩ : syracuseStep 6541681 = 4906261) B4906261
theorem B2576771 : Blo 1144635 2576771 := bstep (se 1 (by rfl) ⟨1932578, by rfl⟩ : syracuseStep 2576771 = 3865157) B3865157
theorem B7459235 : Blo 1144635 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B3264941 : Blo 1144635 3264941 := bstep (se 3 (by rfl) ⟨612176, by rfl⟩ : syracuseStep 3264941 = 1224353) B1224353
theorem B17912261 : Blo 1144635 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B3265123 : Blo 1144635 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B2577041 : Blo 1144635 2577041 := bstep (se 2 (by rfl) ⟨966390, by rfl⟩ : syracuseStep 2577041 = 1932781) B1932781
theorem B2577059 : Blo 1144635 2577059 := bstep (se 1 (by rfl) ⟨1932794, by rfl⟩ : syracuseStep 2577059 = 3865589) B3865589
theorem B10474211 : Blo 1144635 10474211 := bstep (se 1 (by rfl) ⟨7855658, by rfl⟩ : syracuseStep 10474211 = 15711317) B15711317
theorem B4346723 : Blo 1144635 4346723 := bstep (se 1 (by rfl) ⟨3260042, by rfl⟩ : syracuseStep 4346723 = 6520085) B6520085
theorem B2577329 : Blo 1144635 2577329 := bstep (se 2 (by rfl) ⟨966498, by rfl⟩ : syracuseStep 2577329 = 1932997) B1932997
theorem B2577347 : Blo 1144635 2577347 := bstep (se 1 (by rfl) ⟨1933010, by rfl⟩ : syracuseStep 2577347 = 3866021) B3866021
theorem B4641805 : Blo 1144635 4641805 := bstep (se 3 (by rfl) ⟨870338, by rfl⟩ : syracuseStep 4641805 = 1740677) B1740677
theorem B2905105 : Blo 1144635 2905105 := bstep (se 2 (by rfl) ⟨1089414, by rfl⟩ : syracuseStep 2905105 = 2178829) B2178829
theorem B2577617 : Blo 1144635 2577617 := bstep (se 2 (by rfl) ⟨966606, by rfl⟩ : syracuseStep 2577617 = 1933213) B1933213
theorem B2577635 : Blo 1144635 2577635 := bstep (se 1 (by rfl) ⟨1933226, by rfl⟩ : syracuseStep 2577635 = 3866453) B3866453
theorem B5231885 : Blo 1144635 5231885 := bstep (se 3 (by rfl) ⟨980978, by rfl⟩ : syracuseStep 5231885 = 1961957) B1961957
theorem B2905379 : Blo 1144635 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B4904333 : Blo 1144635 4904333 := bstep (se 3 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 4904333 = 1839125) B1839125
theorem B2905571 : Blo 1144635 2905571 := bstep (se 1 (by rfl) ⟨2179178, by rfl⟩ : syracuseStep 2905571 = 4358357) B4358357
theorem B4347377 : Blo 1144635 4347377 := bstep (se 2 (by rfl) ⟨1630266, by rfl⟩ : syracuseStep 4347377 = 3260533) B3260533
theorem B2577905 : Blo 1144635 2577905 := bstep (se 2 (by rfl) ⟨966714, by rfl⟩ : syracuseStep 2577905 = 1933429) B1933429
theorem B2577923 : Blo 1144635 2577923 := bstep (se 1 (by rfl) ⟨1933442, by rfl⟩ : syracuseStep 2577923 = 3866885) B3866885
theorem B2578193 : Blo 1144635 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B2578211 : Blo 1144635 2578211 := bstep (se 1 (by rfl) ⟨1933658, by rfl⟩ : syracuseStep 2578211 = 3867317) B3867317
theorem B2447185 : Blo 1144635 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B3266513 : Blo 1144635 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B2578481 : Blo 1144635 2578481 := bstep (se 2 (by rfl) ⟨966930, by rfl⟩ : syracuseStep 2578481 = 1933861) B1933861
theorem B2578499 : Blo 1144635 2578499 := bstep (se 1 (by rfl) ⟨1933874, by rfl⟩ : syracuseStep 2578499 = 3867749) B3867749
theorem B2447587 : Blo 1144635 2447587 := bstep (se 1 (by rfl) ⟨1835690, by rfl⟩ : syracuseStep 2447587 = 3671381) B3671381
theorem B2578769 : Blo 1144635 2578769 := bstep (se 2 (by rfl) ⟨967038, by rfl⟩ : syracuseStep 2578769 = 1934077) B1934077
theorem B2578787 : Blo 1144635 2578787 := bstep (se 1 (by rfl) ⟨1934090, by rfl⟩ : syracuseStep 2578787 = 3868181) B3868181
theorem B2906513 : Blo 1144635 2906513 := bstep (se 2 (by rfl) ⟨1089942, by rfl⟩ : syracuseStep 2906513 = 2179885) B2179885
theorem B2906563 : Blo 1144635 2906563 := bstep (se 1 (by rfl) ⟨2179922, by rfl⟩ : syracuseStep 2906563 = 4359845) B4359845
theorem B2906705 : Blo 1144635 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B2579057 : Blo 1144635 2579057 := bstep (se 2 (by rfl) ⟨967146, by rfl⟩ : syracuseStep 2579057 = 1934293) B1934293
theorem B2579075 : Blo 1144635 2579075 := bstep (se 1 (by rfl) ⟨1934306, by rfl⟩ : syracuseStep 2579075 = 3868613) B3868613
theorem B3267469 : Blo 1144635 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B2579345 : Blo 1144635 2579345 := bstep (se 2 (by rfl) ⟨967254, by rfl⟩ : syracuseStep 2579345 = 1934509) B1934509
theorem B4348835 : Blo 1144635 4348835 := bstep (se 1 (by rfl) ⟨3261626, by rfl⟩ : syracuseStep 4348835 = 6523253) B6523253
theorem B2579363 : Blo 1144635 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B4348849 : Blo 1144635 4348849 := bstep (se 2 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 4348849 = 3261637) B3261637
theorem B3267697 : Blo 1144635 3267697 := bstep (se 2 (by rfl) ⟨1225386, by rfl⟩ : syracuseStep 3267697 = 2450773) B2450773
theorem B2579633 : Blo 1144635 2579633 := bstep (se 2 (by rfl) ⟨967362, by rfl⟩ : syracuseStep 2579633 = 1934725) B1934725
theorem B2579651 : Blo 1144635 2579651 := bstep (se 1 (by rfl) ⟨1934738, by rfl⟩ : syracuseStep 2579651 = 3869477) B3869477
theorem B3267857 : Blo 1144635 3267857 := bstep (se 2 (by rfl) ⟨1225446, by rfl⟩ : syracuseStep 3267857 = 2450893) B2450893
theorem B3267971 : Blo 1144635 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B2579921 : Blo 1144635 2579921 := bstep (se 2 (by rfl) ⟨967470, by rfl⟩ : syracuseStep 2579921 = 1934941) B1934941
theorem B2579939 : Blo 1144635 2579939 := bstep (se 1 (by rfl) ⟨1934954, by rfl⟩ : syracuseStep 2579939 = 3869909) B3869909
theorem B3137069 : Blo 1144635 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B2940515 : Blo 1144635 2940515 := bstep (se 1 (by rfl) ⟨2205386, by rfl⟩ : syracuseStep 2940515 = 4410773) B4410773
theorem B14900849 : Blo 1144635 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B1629811 : Blo 1144635 1629811 := bstep (se 1 (by rfl) ⟨1222358, by rfl⟩ : syracuseStep 1629811 = 2444717) B2444717
theorem B2449091 : Blo 1144635 2449091 := bstep (se 1 (by rfl) ⟨1836818, by rfl⟩ : syracuseStep 2449091 = 3673637) B3673637
theorem B2580209 : Blo 1144635 2580209 := bstep (se 2 (by rfl) ⟨967578, by rfl⟩ : syracuseStep 2580209 = 1935157) B1935157
theorem B2580227 : Blo 1144635 2580227 := bstep (se 1 (by rfl) ⟨1935170, by rfl⟩ : syracuseStep 2580227 = 3870341) B3870341
theorem B2940803 : Blo 1144635 2940803 := bstep (se 1 (by rfl) ⟨2205602, by rfl⟩ : syracuseStep 2940803 = 4411205) B4411205
theorem B1630147 : Blo 1144635 1630147 := bstep (se 1 (by rfl) ⟨1222610, by rfl⟩ : syracuseStep 1630147 = 2445221) B2445221
theorem B2580497 : Blo 1144635 2580497 := bstep (se 2 (by rfl) ⟨967686, by rfl⟩ : syracuseStep 2580497 = 1935373) B1935373
theorem B2580515 : Blo 1144635 2580515 := bstep (se 1 (by rfl) ⟨1935386, by rfl⟩ : syracuseStep 2580515 = 3870773) B3870773
theorem B1859651 : Blo 1144635 1859651 := bstep (se 1 (by rfl) ⟨1394738, by rfl⟩ : syracuseStep 1859651 = 2789477) B2789477
theorem B2613347 : Blo 1144635 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B2580785 : Blo 1144635 2580785 := bstep (se 2 (by rfl) ⟨967794, by rfl⟩ : syracuseStep 2580785 = 1935589) B1935589
theorem B2580803 : Blo 1144635 2580803 := bstep (se 1 (by rfl) ⟨1935602, by rfl⟩ : syracuseStep 2580803 = 3871205) B3871205
theorem B4350307 : Blo 1144635 4350307 := bstep (se 1 (by rfl) ⟨3262730, by rfl⟩ : syracuseStep 4350307 = 6525461) B6525461
theorem B13066595 : Blo 1144635 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B3268973 : Blo 1144635 3268973 := bstep (se 3 (by rfl) ⟨612932, by rfl⟩ : syracuseStep 3268973 = 1225865) B1225865
theorem B1630705 : Blo 1144635 1630705 := bstep (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) B1223029
theorem B1630739 : Blo 1144635 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B3269155 : Blo 1144635 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B2581073 : Blo 1144635 2581073 := bstep (se 2 (by rfl) ⟨967902, by rfl⟩ : syracuseStep 2581073 = 1935805) B1935805
theorem B2581091 : Blo 1144635 2581091 := bstep (se 1 (by rfl) ⟨1935818, by rfl⟩ : syracuseStep 2581091 = 3871637) B3871637
theorem B13951601 : Blo 1144635 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B1860275 : Blo 1144635 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B3269315 : Blo 1144635 3269315 := bstep (se 1 (by rfl) ⟨2451986, by rfl⟩ : syracuseStep 3269315 = 4903973) B4903973
theorem B2581361 : Blo 1144635 2581361 := bstep (se 2 (by rfl) ⟨968010, by rfl⟩ : syracuseStep 2581361 = 1936021) B1936021
theorem B2581379 : Blo 1144635 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B2450321 : Blo 1144635 2450321 := bstep (se 2 (by rfl) ⟨918870, by rfl⟩ : syracuseStep 2450321 = 1837741) B1837741
theorem B1631297 : Blo 1144635 1631297 := bstep (se 2 (by rfl) ⟨611736, by rfl⟩ : syracuseStep 1631297 = 1223473) B1223473
theorem B1631377 : Blo 1144635 1631377 := bstep (se 2 (by rfl) ⟨611766, by rfl⟩ : syracuseStep 1631377 = 1223533) B1223533
theorem B2581649 : Blo 1144635 2581649 := bstep (se 2 (by rfl) ⟨968118, by rfl⟩ : syracuseStep 2581649 = 1936237) B1936237
theorem B2581667 : Blo 1144635 2581667 := bstep (se 1 (by rfl) ⟨1936250, by rfl⟩ : syracuseStep 2581667 = 3872501) B3872501
theorem B3138797 : Blo 1144635 3138797 := bstep (se 3 (by rfl) ⟨588524, by rfl⟩ : syracuseStep 3138797 = 1177049) B1177049
theorem B2581937 : Blo 1144635 2581937 := bstep (se 2 (by rfl) ⟨968226, by rfl⟩ : syracuseStep 2581937 = 1936453) B1936453
theorem B2581955 : Blo 1144635 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B1959427 : Blo 1144635 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B4646413 : Blo 1144635 4646413 := bstep (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) B1742405
theorem B4646477 : Blo 1144635 4646477 := bstep (se 3 (by rfl) ⟨871214, by rfl⟩ : syracuseStep 4646477 = 1742429) B1742429
theorem B33056369 : Blo 1144635 33056369 := bstep (se 2 (by rfl) ⟨12396138, by rfl⟩ : syracuseStep 33056369 = 24792277) B24792277
theorem B2582225 : Blo 1144635 2582225 := bstep (se 2 (by rfl) ⟨968334, by rfl⟩ : syracuseStep 2582225 = 1936669) B1936669
theorem B2582243 : Blo 1144635 2582243 := bstep (se 1 (by rfl) ⟨1936682, by rfl⟩ : syracuseStep 2582243 = 3873365) B3873365
theorem B4646641 : Blo 1144635 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B3270385 : Blo 1144635 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B2942723 : Blo 1144635 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B2451217 : Blo 1144635 2451217 := bstep (se 2 (by rfl) ⟨919206, by rfl⟩ : syracuseStep 2451217 = 1838413) B1838413
theorem B6973219 : Blo 1144635 6973219 := bstep (se 1 (by rfl) ⟨5229914, by rfl⟩ : syracuseStep 6973219 = 10459829) B10459829
theorem B2451235 : Blo 1144635 2451235 := bstep (se 1 (by rfl) ⟨1838426, by rfl⟩ : syracuseStep 2451235 = 3676853) B3676853
theorem B1632163 : Blo 1144635 1632163 := bstep (se 1 (by rfl) ⟨1224122, by rfl⟩ : syracuseStep 1632163 = 2448245) B2448245
theorem B2582513 : Blo 1144635 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B2582531 : Blo 1144635 2582531 := bstep (se 1 (by rfl) ⟨1936898, by rfl⟩ : syracuseStep 2582531 = 3873797) B3873797
theorem B2582801 : Blo 1144635 2582801 := bstep (se 2 (by rfl) ⟨968550, by rfl⟩ : syracuseStep 2582801 = 1937101) B1937101
theorem B2582819 : Blo 1144635 2582819 := bstep (se 1 (by rfl) ⟨1937114, by rfl⟩ : syracuseStep 2582819 = 3874229) B3874229
theorem B1468739 : Blo 1144635 1468739 := bstep (se 1 (by rfl) ⟨1101554, by rfl⟩ : syracuseStep 1468739 = 2203109) B2203109
theorem B1632641 : Blo 1144635 1632641 := bstep (se 2 (by rfl) ⟨612240, by rfl⟩ : syracuseStep 1632641 = 1224481) B1224481
theorem B1534339 : Blo 1144635 1534339 := bstep (se 1 (by rfl) ⟨1150754, by rfl⟩ : syracuseStep 1534339 = 2301509) B2301509
theorem B1632755 : Blo 1144635 1632755 := bstep (se 1 (by rfl) ⟨1224566, by rfl⟩ : syracuseStep 1632755 = 2449133) B2449133
theorem B4352525 : Blo 1144635 4352525 := bstep (se 3 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 4352525 = 1632197) B1632197
theorem B2583089 : Blo 1144635 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B1632835 : Blo 1144635 1632835 := bstep (se 1 (by rfl) ⟨1224626, by rfl⟩ : syracuseStep 1632835 = 2449253) B2449253
theorem B2583107 : Blo 1144635 2583107 := bstep (se 1 (by rfl) ⟨1937330, by rfl⟩ : syracuseStep 2583107 = 3874661) B3874661
theorem B7269041 : Blo 1144635 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B2583377 : Blo 1144635 2583377 := bstep (se 2 (by rfl) ⟨968766, by rfl⟩ : syracuseStep 2583377 = 1937533) B1937533
theorem B2583395 : Blo 1144635 2583395 := bstep (se 1 (by rfl) ⟨1937546, by rfl⟩ : syracuseStep 2583395 = 3875093) B3875093
theorem B1633393 : Blo 1144635 1633393 := bstep (se 2 (by rfl) ⟨612522, by rfl⟩ : syracuseStep 1633393 = 1225045) B1225045
theorem B2583665 : Blo 1144635 2583665 := bstep (se 2 (by rfl) ⟨968874, by rfl⟩ : syracuseStep 2583665 = 1937749) B1937749
theorem B2583683 : Blo 1144635 2583683 := bstep (se 1 (by rfl) ⟨1937762, by rfl⟩ : syracuseStep 2583683 = 3875525) B3875525
theorem B16542947 : Blo 1144635 16542947 := bstep (se 1 (by rfl) ⟨12407210, by rfl⟩ : syracuseStep 16542947 = 24814421) B24814421
theorem B2583953 : Blo 1144635 2583953 := bstep (se 2 (by rfl) ⟨968982, by rfl⟩ : syracuseStep 2583953 = 1937965) B1937965
theorem B2583971 : Blo 1144635 2583971 := bstep (se 1 (by rfl) ⟨1937978, by rfl⟩ : syracuseStep 2583971 = 3875957) B3875957
theorem B9301517 : Blo 1144635 9301517 := bstep (se 3 (by rfl) ⟨1744034, by rfl⟩ : syracuseStep 9301517 = 3488069) B3488069
theorem B2584241 : Blo 1144635 2584241 := bstep (se 2 (by rfl) ⟨969090, by rfl⟩ : syracuseStep 2584241 = 1938181) B1938181
theorem B2584259 : Blo 1144635 2584259 := bstep (se 1 (by rfl) ⟨1938194, by rfl⟩ : syracuseStep 2584259 = 3876389) B3876389
theorem B1634099 : Blo 1144635 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B8712035 : Blo 1144635 8712035 := bstep (se 1 (by rfl) ⟨6534026, by rfl⟩ : syracuseStep 8712035 = 13068053) B13068053
theorem B1961891 : Blo 1144635 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B1634737 : Blo 1144635 1634737 := bstep (se 2 (by rfl) ⟨613026, by rfl⟩ : syracuseStep 1634737 = 1226053) B1226053
theorem B1634851 : Blo 1144635 1634851 := bstep (se 1 (by rfl) ⟨1226138, by rfl⟩ : syracuseStep 1634851 = 2452277) B2452277
theorem B5239331 : Blo 1144635 5239331 := bstep (se 1 (by rfl) ⟨3929498, by rfl⟩ : syracuseStep 5239331 = 7858997) B7858997
theorem B2683523 : Blo 1144635 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B1962641 : Blo 1144635 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B3863213 : Blo 1144635 3863213 := bstep (se 3 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 3863213 = 1448705) B1448705
theorem B3863267 : Blo 1144635 3863267 := bstep (se 1 (by rfl) ⟨2897450, by rfl⟩ : syracuseStep 3863267 = 5794901) B5794901
theorem B1307443 : Blo 1144635 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B2356049 : Blo 1144635 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B7336817 : Blo 1144635 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B62813069 : Blo 1144635 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B3863537 : Blo 1144635 3863537 := bstep (se 2 (by rfl) ⟨1448826, by rfl⟩ : syracuseStep 3863537 = 2897653) B2897653
theorem B3667139 : Blo 1144635 3667139 := bstep (se 1 (by rfl) ⟨2750354, by rfl⟩ : syracuseStep 3667139 = 5500709) B5500709
theorem B5797169 : Blo 1144635 5797169 := bstep (se 2 (by rfl) ⟨2173938, by rfl⟩ : syracuseStep 5797169 = 4347877) B4347877
theorem B4355441 : Blo 1144635 4355441 := bstep (se 2 (by rfl) ⟨1633290, by rfl⟩ : syracuseStep 4355441 = 3266581) B3266581
theorem B6616525 : Blo 1144635 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B3864077 : Blo 1144635 3864077 := bstep (se 3 (by rfl) ⟨724514, by rfl⟩ : syracuseStep 3864077 = 1449029) B1449029
theorem B3864131 : Blo 1144635 3864131 := bstep (se 1 (by rfl) ⟨2898098, by rfl⟩ : syracuseStep 3864131 = 5796197) B5796197
theorem B1144643 : Blo 1144635 1144643 := bstep (se 1 (by rfl) ⟨858482, by rfl⟩ : syracuseStep 1144643 = 1716965) B1716965
theorem B3864401 : Blo 1144635 3864401 := bstep (se 2 (by rfl) ⟨1449150, by rfl⟩ : syracuseStep 3864401 = 2898301) B2898301
theorem B1144659 : Blo 1144635 1144659 := bstep (se 1 (by rfl) ⟨858494, by rfl⟩ : syracuseStep 1144659 = 1716989) B1716989
theorem B1144675 : Blo 1144635 1144675 := bstep (se 1 (by rfl) ⟨858506, by rfl⟩ : syracuseStep 1144675 = 1717013) B1717013
theorem B1144691 : Blo 1144635 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B1144707 : Blo 1144635 1144707 := bstep (se 1 (by rfl) ⟨858530, by rfl⟩ : syracuseStep 1144707 = 1717061) B1717061
theorem B1144723 : Blo 1144635 1144723 := bstep (se 1 (by rfl) ⟨858542, by rfl⟩ : syracuseStep 1144723 = 1717085) B1717085
theorem B1144739 : Blo 1144635 1144739 := bstep (se 1 (by rfl) ⟨858554, by rfl⟩ : syracuseStep 1144739 = 1717109) B1717109
theorem B1144755 : Blo 1144635 1144755 := bstep (se 1 (by rfl) ⟨858566, by rfl⟩ : syracuseStep 1144755 = 1717133) B1717133
theorem B1963955 : Blo 1144635 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B1144771 : Blo 1144635 1144771 := bstep (se 1 (by rfl) ⟨858578, by rfl⟩ : syracuseStep 1144771 = 1717157) B1717157
theorem B18577349 : Blo 1144635 18577349 := bstep (se 4 (by rfl) ⟨1741626, by rfl⟩ : syracuseStep 18577349 = 3483253) B3483253
theorem B1144787 : Blo 1144635 1144787 := bstep (se 1 (by rfl) ⟨858590, by rfl⟩ : syracuseStep 1144787 = 1717181) B1717181
theorem B1144803 : Blo 1144635 1144803 := bstep (se 1 (by rfl) ⟨858602, by rfl⟩ : syracuseStep 1144803 = 1717205) B1717205
theorem B1964003 : Blo 1144635 1964003 := bstep (se 1 (by rfl) ⟨1473002, by rfl⟩ : syracuseStep 1964003 = 2946005) B2946005
theorem B1144819 : Blo 1144635 1144819 := bstep (se 1 (by rfl) ⟨858614, by rfl⟩ : syracuseStep 1144819 = 1717229) B1717229
theorem B1144835 : Blo 1144635 1144835 := bstep (se 1 (by rfl) ⟨858626, by rfl⟩ : syracuseStep 1144835 = 1717253) B1717253
theorem B1144851 : Blo 1144635 1144851 := bstep (se 1 (by rfl) ⟨858638, by rfl⟩ : syracuseStep 1144851 = 1717277) B1717277
theorem B1144867 : Blo 1144635 1144867 := bstep (se 1 (by rfl) ⟨858650, by rfl⟩ : syracuseStep 1144867 = 1717301) B1717301
theorem B6191153 : Blo 1144635 6191153 := bstep (se 2 (by rfl) ⟨2321682, by rfl⟩ : syracuseStep 6191153 = 4643365) B4643365
theorem B1964081 : Blo 1144635 1964081 := bstep (se 2 (by rfl) ⟨736530, by rfl⟩ : syracuseStep 1964081 = 1473061) B1473061
theorem B1144883 : Blo 1144635 1144883 := bstep (se 1 (by rfl) ⟨858662, by rfl⟩ : syracuseStep 1144883 = 1717325) B1717325
theorem B1144899 : Blo 1144635 1144899 := bstep (se 1 (by rfl) ⟨858674, by rfl⟩ : syracuseStep 1144899 = 1717349) B1717349
theorem B1144915 : Blo 1144635 1144915 := bstep (se 1 (by rfl) ⟨858686, by rfl⟩ : syracuseStep 1144915 = 1717373) B1717373
theorem B1144931 : Blo 1144635 1144931 := bstep (se 1 (by rfl) ⟨858698, by rfl⟩ : syracuseStep 1144931 = 1717397) B1717397
theorem B1144947 : Blo 1144635 1144947 := bstep (se 1 (by rfl) ⟨858710, by rfl⟩ : syracuseStep 1144947 = 1717421) B1717421
theorem B1144963 : Blo 1144635 1144963 := bstep (se 1 (by rfl) ⟨858722, by rfl⟩ : syracuseStep 1144963 = 1717445) B1717445
theorem B1144979 : Blo 1144635 1144979 := bstep (se 1 (by rfl) ⟨858734, by rfl⟩ : syracuseStep 1144979 = 1717469) B1717469
theorem B1144995 : Blo 1144635 1144995 := bstep (se 1 (by rfl) ⟨858746, by rfl⟩ : syracuseStep 1144995 = 1717493) B1717493
theorem B1145011 : Blo 1144635 1145011 := bstep (se 1 (by rfl) ⟨858758, by rfl⟩ : syracuseStep 1145011 = 1717517) B1717517
theorem B1145027 : Blo 1144635 1145027 := bstep (se 1 (by rfl) ⟨858770, by rfl⟩ : syracuseStep 1145027 = 1717541) B1717541
theorem B1145043 : Blo 1144635 1145043 := bstep (se 1 (by rfl) ⟨858782, by rfl⟩ : syracuseStep 1145043 = 1717565) B1717565
theorem B1145059 : Blo 1144635 1145059 := bstep (se 1 (by rfl) ⟨858794, by rfl⟩ : syracuseStep 1145059 = 1717589) B1717589
theorem B1145075 : Blo 1144635 1145075 := bstep (se 1 (by rfl) ⟨858806, by rfl⟩ : syracuseStep 1145075 = 1717613) B1717613
theorem B1145091 : Blo 1144635 1145091 := bstep (se 1 (by rfl) ⟨858818, by rfl⟩ : syracuseStep 1145091 = 1717637) B1717637
theorem B1767683 : Blo 1144635 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B1145107 : Blo 1144635 1145107 := bstep (se 1 (by rfl) ⟨858830, by rfl⟩ : syracuseStep 1145107 = 1717661) B1717661
theorem B1145123 : Blo 1144635 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B7338275 : Blo 1144635 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B1145139 : Blo 1144635 1145139 := bstep (se 1 (by rfl) ⟨858854, by rfl⟩ : syracuseStep 1145139 = 1717709) B1717709
theorem B1145155 : Blo 1144635 1145155 := bstep (se 1 (by rfl) ⟨858866, by rfl⟩ : syracuseStep 1145155 = 1717733) B1717733
theorem B1145171 : Blo 1144635 1145171 := bstep (se 1 (by rfl) ⟨858878, by rfl⟩ : syracuseStep 1145171 = 1717757) B1717757
theorem B4127075 : Blo 1144635 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B1145187 : Blo 1144635 1145187 := bstep (se 1 (by rfl) ⟨858890, by rfl⟩ : syracuseStep 1145187 = 1717781) B1717781
theorem B3864941 : Blo 1144635 3864941 := bstep (se 3 (by rfl) ⟨724676, by rfl⟩ : syracuseStep 3864941 = 1449353) B1449353
theorem B1571185 : Blo 1144635 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B1145203 : Blo 1144635 1145203 := bstep (se 1 (by rfl) ⟨858902, by rfl⟩ : syracuseStep 1145203 = 1717805) B1717805
theorem B1145219 : Blo 1144635 1145219 := bstep (se 1 (by rfl) ⟨858914, by rfl⟩ : syracuseStep 1145219 = 1717829) B1717829
theorem B12417421 : Blo 1144635 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B1145235 : Blo 1144635 1145235 := bstep (se 1 (by rfl) ⟨858926, by rfl⟩ : syracuseStep 1145235 = 1717853) B1717853
theorem B1931681 : Blo 1144635 1931681 := bstep (se 2 (by rfl) ⟨724380, by rfl⟩ : syracuseStep 1931681 = 1448761) B1448761
theorem B3864995 : Blo 1144635 3864995 := bstep (se 1 (by rfl) ⟨2898746, by rfl⟩ : syracuseStep 3864995 = 5797493) B5797493
theorem B1145251 : Blo 1144635 1145251 := bstep (se 1 (by rfl) ⟨858938, by rfl⟩ : syracuseStep 1145251 = 1717877) B1717877
theorem B1145267 : Blo 1144635 1145267 := bstep (se 1 (by rfl) ⟨858950, by rfl⟩ : syracuseStep 1145267 = 1717901) B1717901
theorem B3668419 : Blo 1144635 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B1145283 : Blo 1144635 1145283 := bstep (se 1 (by rfl) ⟨858962, by rfl⟩ : syracuseStep 1145283 = 1717925) B1717925
theorem B1145299 : Blo 1144635 1145299 := bstep (se 1 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 1145299 = 1717949) B1717949
theorem B4127203 : Blo 1144635 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B1145315 : Blo 1144635 1145315 := bstep (se 1 (by rfl) ⟨858986, by rfl⟩ : syracuseStep 1145315 = 1717973) B1717973
theorem B1145331 : Blo 1144635 1145331 := bstep (se 1 (by rfl) ⟨858998, by rfl⟩ : syracuseStep 1145331 = 1717997) B1717997
theorem B1145347 : Blo 1144635 1145347 := bstep (se 1 (by rfl) ⟨859010, by rfl⟩ : syracuseStep 1145347 = 1718021) B1718021
theorem B1145363 : Blo 1144635 1145363 := bstep (se 1 (by rfl) ⟨859022, by rfl⟩ : syracuseStep 1145363 = 1718045) B1718045
theorem B1931809 : Blo 1144635 1931809 := bstep (se 2 (by rfl) ⟨724428, by rfl⟩ : syracuseStep 1931809 = 1448857) B1448857
theorem B1145379 : Blo 1144635 1145379 := bstep (se 1 (by rfl) ⟨859034, by rfl⟩ : syracuseStep 1145379 = 1718069) B1718069
theorem B1145395 : Blo 1144635 1145395 := bstep (se 1 (by rfl) ⟨859046, by rfl⟩ : syracuseStep 1145395 = 1718093) B1718093
theorem B1931843 : Blo 1144635 1931843 := bstep (se 1 (by rfl) ⟨1448882, by rfl⟩ : syracuseStep 1931843 = 2897765) B2897765
theorem B1145411 : Blo 1144635 1145411 := bstep (se 1 (by rfl) ⟨859058, by rfl⟩ : syracuseStep 1145411 = 1718117) B1718117
theorem B14678597 : Blo 1144635 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1145427 : Blo 1144635 1145427 := bstep (se 1 (by rfl) ⟨859070, by rfl⟩ : syracuseStep 1145427 = 1718141) B1718141
theorem B1145443 : Blo 1144635 1145443 := bstep (se 1 (by rfl) ⟨859082, by rfl⟩ : syracuseStep 1145443 = 1718165) B1718165
theorem B9435761 : Blo 1144635 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1145459 : Blo 1144635 1145459 := bstep (se 1 (by rfl) ⟨859094, by rfl⟩ : syracuseStep 1145459 = 1718189) B1718189
theorem B1145475 : Blo 1144635 1145475 := bstep (se 1 (by rfl) ⟨859106, by rfl⟩ : syracuseStep 1145475 = 1718213) B1718213
theorem B1145491 : Blo 1144635 1145491 := bstep (se 1 (by rfl) ⟨859118, by rfl⟩ : syracuseStep 1145491 = 1718237) B1718237
theorem B1145507 : Blo 1144635 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B3865265 : Blo 1144635 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B1145523 : Blo 1144635 1145523 := bstep (se 1 (by rfl) ⟨859142, by rfl⟩ : syracuseStep 1145523 = 1718285) B1718285
theorem B1931971 : Blo 1144635 1931971 := bstep (se 1 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 1931971 = 2897957) B2897957
theorem B1145539 : Blo 1144635 1145539 := bstep (se 1 (by rfl) ⟨859154, by rfl⟩ : syracuseStep 1145539 = 1718309) B1718309
theorem B1145555 : Blo 1144635 1145555 := bstep (se 1 (by rfl) ⟨859166, by rfl⟩ : syracuseStep 1145555 = 1718333) B1718333
theorem B1833697 : Blo 1144635 1833697 := bstep (se 2 (by rfl) ⟨687636, by rfl⟩ : syracuseStep 1833697 = 1375273) B1375273
theorem B5798627 : Blo 1144635 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1145571 : Blo 1144635 1145571 := bstep (se 1 (by rfl) ⟨859178, by rfl⟩ : syracuseStep 1145571 = 1718357) B1718357
theorem B1145587 : Blo 1144635 1145587 := bstep (se 1 (by rfl) ⟨859190, by rfl⟩ : syracuseStep 1145587 = 1718381) B1718381
theorem B1145603 : Blo 1144635 1145603 := bstep (se 1 (by rfl) ⟨859202, by rfl⟩ : syracuseStep 1145603 = 1718405) B1718405
theorem B3668753 : Blo 1144635 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1145619 : Blo 1144635 1145619 := bstep (se 1 (by rfl) ⟨859214, by rfl⟩ : syracuseStep 1145619 = 1718429) B1718429
theorem B1145635 : Blo 1144635 1145635 := bstep (se 1 (by rfl) ⟨859226, by rfl⟩ : syracuseStep 1145635 = 1718453) B1718453
theorem B4356899 : Blo 1144635 4356899 := bstep (se 1 (by rfl) ⟨3267674, by rfl⟩ : syracuseStep 4356899 = 6535349) B6535349
theorem B4127537 : Blo 1144635 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B1145651 : Blo 1144635 1145651 := bstep (se 1 (by rfl) ⟨859238, by rfl⟩ : syracuseStep 1145651 = 1718477) B1718477
theorem B1145667 : Blo 1144635 1145667 := bstep (se 1 (by rfl) ⟨859250, by rfl⟩ : syracuseStep 1145667 = 1718501) B1718501
theorem B6519629 : Blo 1144635 6519629 := bstep (se 3 (by rfl) ⟨1222430, by rfl⟩ : syracuseStep 6519629 = 2444861) B2444861
theorem B1932113 : Blo 1144635 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1145683 : Blo 1144635 1145683 := bstep (se 1 (by rfl) ⟨859262, by rfl⟩ : syracuseStep 1145683 = 1718525) B1718525
theorem B8813411 : Blo 1144635 8813411 := bstep (se 1 (by rfl) ⟨6610058, by rfl⟩ : syracuseStep 8813411 = 13220117) B13220117
theorem B1145699 : Blo 1144635 1145699 := bstep (se 1 (by rfl) ⟨859274, by rfl⟩ : syracuseStep 1145699 = 1718549) B1718549
theorem B1145715 : Blo 1144635 1145715 := bstep (se 1 (by rfl) ⟨859286, by rfl⟩ : syracuseStep 1145715 = 1718573) B1718573
theorem B1145731 : Blo 1144635 1145731 := bstep (se 1 (by rfl) ⟨859298, by rfl⟩ : syracuseStep 1145731 = 1718597) B1718597
theorem B1145747 : Blo 1144635 1145747 := bstep (se 1 (by rfl) ⟨859310, by rfl⟩ : syracuseStep 1145747 = 1718621) B1718621
theorem B1145763 : Blo 1144635 1145763 := bstep (se 1 (by rfl) ⟨859322, by rfl⟩ : syracuseStep 1145763 = 1718645) B1718645
theorem B1145779 : Blo 1144635 1145779 := bstep (se 1 (by rfl) ⟨859334, by rfl⟩ : syracuseStep 1145779 = 1718669) B1718669
theorem B1145795 : Blo 1144635 1145795 := bstep (se 1 (by rfl) ⟨859346, by rfl⟩ : syracuseStep 1145795 = 1718693) B1718693
theorem B31783877 : Blo 1144635 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B1932241 : Blo 1144635 1932241 := bstep (se 2 (by rfl) ⟨724590, by rfl⟩ : syracuseStep 1932241 = 1449181) B1449181
theorem B1145811 : Blo 1144635 1145811 := bstep (se 1 (by rfl) ⟨859358, by rfl⟩ : syracuseStep 1145811 = 1718717) B1718717
theorem B1145827 : Blo 1144635 1145827 := bstep (se 1 (by rfl) ⟨859370, by rfl⟩ : syracuseStep 1145827 = 1718741) B1718741
theorem B1932275 : Blo 1144635 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B1145843 : Blo 1144635 1145843 := bstep (se 1 (by rfl) ⟨859382, by rfl⟩ : syracuseStep 1145843 = 1718765) B1718765
theorem B1145859 : Blo 1144635 1145859 := bstep (se 1 (by rfl) ⟨859394, by rfl⟩ : syracuseStep 1145859 = 1718789) B1718789
theorem B1145875 : Blo 1144635 1145875 := bstep (se 1 (by rfl) ⟨859406, by rfl⟩ : syracuseStep 1145875 = 1718813) B1718813
theorem B1145891 : Blo 1144635 1145891 := bstep (se 1 (by rfl) ⟨859418, by rfl⟩ : syracuseStep 1145891 = 1718837) B1718837
theorem B1145907 : Blo 1144635 1145907 := bstep (se 1 (by rfl) ⟨859430, by rfl⟩ : syracuseStep 1145907 = 1718861) B1718861
theorem B1145923 : Blo 1144635 1145923 := bstep (se 1 (by rfl) ⟨859442, by rfl⟩ : syracuseStep 1145923 = 1718885) B1718885
theorem B1145939 : Blo 1144635 1145939 := bstep (se 1 (by rfl) ⟨859454, by rfl⟩ : syracuseStep 1145939 = 1718909) B1718909
theorem B1145955 : Blo 1144635 1145955 := bstep (se 1 (by rfl) ⟨859466, by rfl⟩ : syracuseStep 1145955 = 1718933) B1718933
theorem B1932403 : Blo 1144635 1932403 := bstep (se 1 (by rfl) ⟨1449302, by rfl⟩ : syracuseStep 1932403 = 2898605) B2898605
theorem B1145971 : Blo 1144635 1145971 := bstep (se 1 (by rfl) ⟨859478, by rfl⟩ : syracuseStep 1145971 = 1718957) B1718957
theorem B1145987 : Blo 1144635 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B1146003 : Blo 1144635 1146003 := bstep (se 1 (by rfl) ⟨859502, by rfl⟩ : syracuseStep 1146003 = 1719005) B1719005
theorem B1146019 : Blo 1144635 1146019 := bstep (se 1 (by rfl) ⟨859514, by rfl⟩ : syracuseStep 1146019 = 1719029) B1719029
theorem B1146035 : Blo 1144635 1146035 := bstep (se 1 (by rfl) ⟨859526, by rfl⟩ : syracuseStep 1146035 = 1719053) B1719053
theorem B1375427 : Blo 1144635 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B1146051 : Blo 1144635 1146051 := bstep (se 1 (by rfl) ⟨859538, by rfl⟩ : syracuseStep 1146051 = 1719077) B1719077
theorem B3865805 : Blo 1144635 3865805 := bstep (se 3 (by rfl) ⟨724838, by rfl⟩ : syracuseStep 3865805 = 1449677) B1449677
theorem B1146067 : Blo 1144635 1146067 := bstep (se 1 (by rfl) ⟨859550, by rfl⟩ : syracuseStep 1146067 = 1719101) B1719101
theorem B1146083 : Blo 1144635 1146083 := bstep (se 1 (by rfl) ⟨859562, by rfl⟩ : syracuseStep 1146083 = 1719125) B1719125
theorem B1375475 : Blo 1144635 1375475 := bstep (se 1 (by rfl) ⟨1031606, by rfl⟩ : syracuseStep 1375475 = 2063213) B2063213
theorem B1146099 : Blo 1144635 1146099 := bstep (se 1 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 1146099 = 1719149) B1719149
theorem B1932545 : Blo 1144635 1932545 := bstep (se 2 (by rfl) ⟨724704, by rfl⟩ : syracuseStep 1932545 = 1449409) B1449409
theorem B3865859 : Blo 1144635 3865859 := bstep (se 1 (by rfl) ⟨2899394, by rfl⟩ : syracuseStep 3865859 = 5798789) B5798789
theorem B1146115 : Blo 1144635 1146115 := bstep (se 1 (by rfl) ⟨859586, by rfl⟩ : syracuseStep 1146115 = 1719173) B1719173
theorem B1146131 : Blo 1144635 1146131 := bstep (se 1 (by rfl) ⟨859598, by rfl⟩ : syracuseStep 1146131 = 1719197) B1719197
theorem B1146147 : Blo 1144635 1146147 := bstep (se 1 (by rfl) ⟨859610, by rfl⟩ : syracuseStep 1146147 = 1719221) B1719221
theorem B1146163 : Blo 1144635 1146163 := bstep (se 1 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 1146163 = 1719245) B1719245
theorem B1146179 : Blo 1144635 1146179 := bstep (se 1 (by rfl) ⟨859634, by rfl⟩ : syracuseStep 1146179 = 1719269) B1719269
theorem B1146195 : Blo 1144635 1146195 := bstep (se 1 (by rfl) ⟨859646, by rfl⟩ : syracuseStep 1146195 = 1719293) B1719293
theorem B1146211 : Blo 1144635 1146211 := bstep (se 1 (by rfl) ⟨859658, by rfl⟩ : syracuseStep 1146211 = 1719317) B1719317
theorem B1146227 : Blo 1144635 1146227 := bstep (se 1 (by rfl) ⟨859670, by rfl⟩ : syracuseStep 1146227 = 1719341) B1719341
theorem B1932673 : Blo 1144635 1932673 := bstep (se 2 (by rfl) ⟨724752, by rfl⟩ : syracuseStep 1932673 = 1449505) B1449505
theorem B1146243 : Blo 1144635 1146243 := bstep (se 1 (by rfl) ⟨859682, by rfl⟩ : syracuseStep 1146243 = 1719365) B1719365
theorem B1146259 : Blo 1144635 1146259 := bstep (se 1 (by rfl) ⟨859694, by rfl⟩ : syracuseStep 1146259 = 1719389) B1719389
theorem B1932707 : Blo 1144635 1932707 := bstep (se 1 (by rfl) ⟨1449530, by rfl⟩ : syracuseStep 1932707 = 2899061) B2899061
theorem B1146275 : Blo 1144635 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B1146291 : Blo 1144635 1146291 := bstep (se 1 (by rfl) ⟨859718, by rfl⟩ : syracuseStep 1146291 = 1719437) B1719437
theorem B1146307 : Blo 1144635 1146307 := bstep (se 1 (by rfl) ⟨859730, by rfl⟩ : syracuseStep 1146307 = 1719461) B1719461
theorem B1146323 : Blo 1144635 1146323 := bstep (se 1 (by rfl) ⟨859742, by rfl⟩ : syracuseStep 1146323 = 1719485) B1719485
theorem B1146339 : Blo 1144635 1146339 := bstep (se 1 (by rfl) ⟨859754, by rfl⟩ : syracuseStep 1146339 = 1719509) B1719509
theorem B1146355 : Blo 1144635 1146355 := bstep (se 1 (by rfl) ⟨859766, by rfl⟩ : syracuseStep 1146355 = 1719533) B1719533
theorem B1146371 : Blo 1144635 1146371 := bstep (se 1 (by rfl) ⟨859778, by rfl⟩ : syracuseStep 1146371 = 1719557) B1719557
theorem B5799437 : Blo 1144635 5799437 := bstep (se 3 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 5799437 = 2174789) B2174789
theorem B3866129 : Blo 1144635 3866129 := bstep (se 2 (by rfl) ⟨1449798, by rfl⟩ : syracuseStep 3866129 = 2899597) B2899597
theorem B1146387 : Blo 1144635 1146387 := bstep (se 1 (by rfl) ⟨859790, by rfl⟩ : syracuseStep 1146387 = 1719581) B1719581
theorem B1932835 : Blo 1144635 1932835 := bstep (se 1 (by rfl) ⟨1449626, by rfl⟩ : syracuseStep 1932835 = 2899253) B2899253
theorem B1146403 : Blo 1144635 1146403 := bstep (se 1 (by rfl) ⟨859802, by rfl⟩ : syracuseStep 1146403 = 1719605) B1719605
theorem B1146419 : Blo 1144635 1146419 := bstep (se 1 (by rfl) ⟨859814, by rfl⟩ : syracuseStep 1146419 = 1719629) B1719629
theorem B1146435 : Blo 1144635 1146435 := bstep (se 1 (by rfl) ⟨859826, by rfl⟩ : syracuseStep 1146435 = 1719653) B1719653
theorem B1146451 : Blo 1144635 1146451 := bstep (se 1 (by rfl) ⟨859838, by rfl⟩ : syracuseStep 1146451 = 1719677) B1719677
theorem B5504611 : Blo 1144635 5504611 := bstep (se 1 (by rfl) ⟨4128458, by rfl⟩ : syracuseStep 5504611 = 8256917) B8256917
theorem B1146467 : Blo 1144635 1146467 := bstep (se 1 (by rfl) ⟨859850, by rfl⟩ : syracuseStep 1146467 = 1719701) B1719701
theorem B4193905 : Blo 1144635 4193905 := bstep (se 2 (by rfl) ⟨1572714, by rfl⟩ : syracuseStep 4193905 = 3145429) B3145429
theorem B1146483 : Blo 1144635 1146483 := bstep (se 1 (by rfl) ⟨859862, by rfl⟩ : syracuseStep 1146483 = 1719725) B1719725
theorem B1146499 : Blo 1144635 1146499 := bstep (se 1 (by rfl) ⟨859874, by rfl⟩ : syracuseStep 1146499 = 1719749) B1719749
theorem B1146515 : Blo 1144635 1146515 := bstep (se 1 (by rfl) ⟨859886, by rfl⟩ : syracuseStep 1146515 = 1719773) B1719773
theorem B2064035 : Blo 1144635 2064035 := bstep (se 1 (by rfl) ⟨1548026, by rfl⟩ : syracuseStep 2064035 = 3096053) B3096053
theorem B1146531 : Blo 1144635 1146531 := bstep (se 1 (by rfl) ⟨859898, by rfl⟩ : syracuseStep 1146531 = 1719797) B1719797
theorem B2358947 : Blo 1144635 2358947 := bstep (se 1 (by rfl) ⟨1769210, by rfl⟩ : syracuseStep 2358947 = 3538421) B3538421
theorem B1932977 : Blo 1144635 1932977 := bstep (se 2 (by rfl) ⟨724866, by rfl⟩ : syracuseStep 1932977 = 1449733) B1449733
theorem B1146547 : Blo 1144635 1146547 := bstep (se 1 (by rfl) ⟨859910, by rfl⟩ : syracuseStep 1146547 = 1719821) B1719821
theorem B1146563 : Blo 1144635 1146563 := bstep (se 1 (by rfl) ⟨859922, by rfl⟩ : syracuseStep 1146563 = 1719845) B1719845
theorem B1146579 : Blo 1144635 1146579 := bstep (se 1 (by rfl) ⟨859934, by rfl⟩ : syracuseStep 1146579 = 1719869) B1719869
theorem B1146595 : Blo 1144635 1146595 := bstep (se 1 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 1146595 = 1719893) B1719893
theorem B6192881 : Blo 1144635 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B1146611 : Blo 1144635 1146611 := bstep (se 1 (by rfl) ⟨859958, by rfl⟩ : syracuseStep 1146611 = 1719917) B1719917
theorem B1146627 : Blo 1144635 1146627 := bstep (se 1 (by rfl) ⟨859970, by rfl⟩ : syracuseStep 1146627 = 1719941) B1719941
theorem B4357901 : Blo 1144635 4357901 := bstep (se 3 (by rfl) ⟨817106, by rfl⟩ : syracuseStep 4357901 = 1634213) B1634213
theorem B1146643 : Blo 1144635 1146643 := bstep (se 1 (by rfl) ⟨859982, by rfl⟩ : syracuseStep 1146643 = 1719965) B1719965
theorem B1834787 : Blo 1144635 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B1146659 : Blo 1144635 1146659 := bstep (se 1 (by rfl) ⟨859994, by rfl⟩ : syracuseStep 1146659 = 1719989) B1719989
theorem B1933105 : Blo 1144635 1933105 := bstep (se 2 (by rfl) ⟨724914, by rfl⟩ : syracuseStep 1933105 = 1449829) B1449829
theorem B1146675 : Blo 1144635 1146675 := bstep (se 1 (by rfl) ⟨860006, by rfl⟩ : syracuseStep 1146675 = 1720013) B1720013
theorem B1146691 : Blo 1144635 1146691 := bstep (se 1 (by rfl) ⟨860018, by rfl⟩ : syracuseStep 1146691 = 1720037) B1720037
theorem B1933139 : Blo 1144635 1933139 := bstep (se 1 (by rfl) ⟨1449854, by rfl⟩ : syracuseStep 1933139 = 2899709) B2899709
theorem B1146707 : Blo 1144635 1146707 := bstep (se 1 (by rfl) ⟨860030, by rfl⟩ : syracuseStep 1146707 = 1720061) B1720061
theorem B1146723 : Blo 1144635 1146723 := bstep (se 1 (by rfl) ⟨860042, by rfl⟩ : syracuseStep 1146723 = 1720085) B1720085
theorem B1146739 : Blo 1144635 1146739 := bstep (se 1 (by rfl) ⟨860054, by rfl⟩ : syracuseStep 1146739 = 1720109) B1720109
theorem B1146755 : Blo 1144635 1146755 := bstep (se 1 (by rfl) ⟨860066, by rfl⟩ : syracuseStep 1146755 = 1720133) B1720133
theorem B16744333 : Blo 1144635 16744333 := bstep (se 3 (by rfl) ⟨3139562, by rfl⟩ : syracuseStep 16744333 = 6279125) B6279125
theorem B1146771 : Blo 1144635 1146771 := bstep (se 1 (by rfl) ⟨860078, by rfl⟩ : syracuseStep 1146771 = 1720157) B1720157
theorem B1146787 : Blo 1144635 1146787 := bstep (se 1 (by rfl) ⟨860090, by rfl⟩ : syracuseStep 1146787 = 1720181) B1720181
theorem B1146803 : Blo 1144635 1146803 := bstep (se 1 (by rfl) ⟨860102, by rfl⟩ : syracuseStep 1146803 = 1720205) B1720205
theorem B2064323 : Blo 1144635 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B1146819 : Blo 1144635 1146819 := bstep (se 1 (by rfl) ⟨860114, by rfl⟩ : syracuseStep 1146819 = 1720229) B1720229
theorem B1933267 : Blo 1144635 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B1146835 : Blo 1144635 1146835 := bstep (se 1 (by rfl) ⟨860126, by rfl⟩ : syracuseStep 1146835 = 1720253) B1720253
theorem B1146851 : Blo 1144635 1146851 := bstep (se 1 (by rfl) ⟨860138, by rfl⟩ : syracuseStep 1146851 = 1720277) B1720277
theorem B7340017 : Blo 1144635 7340017 := bstep (se 2 (by rfl) ⟨2752506, by rfl⟩ : syracuseStep 7340017 = 5505013) B5505013
theorem B1146867 : Blo 1144635 1146867 := bstep (se 1 (by rfl) ⟨860150, by rfl⟩ : syracuseStep 1146867 = 1720301) B1720301
theorem B1146891 : Blo 1144635 1146891 := bstep (se 1 (by rfl) ⟨860168, by rfl⟩ : syracuseStep 1146891 = 1720337) B1720337
theorem B1146903 : Blo 1144635 1146903 := bstep (se 1 (by rfl) ⟨860177, by rfl⟩ : syracuseStep 1146903 = 1720355) B1720355
theorem B1146923 : Blo 1144635 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B1146935 : Blo 1144635 1146935 := bstep (se 1 (by rfl) ⟨860201, by rfl⟩ : syracuseStep 1146935 = 1720403) B1720403
theorem B5505089 : Blo 1144635 5505089 := bstep (se 2 (by rfl) ⟨2064408, by rfl⟩ : syracuseStep 5505089 = 4128817) B4128817
theorem B1146955 : Blo 1144635 1146955 := bstep (se 1 (by rfl) ⟨860216, by rfl⟩ : syracuseStep 1146955 = 1720433) B1720433
theorem B1146967 : Blo 1144635 1146967 := bstep (se 1 (by rfl) ⟨860225, by rfl⟩ : syracuseStep 1146967 = 1720451) B1720451
theorem B1146987 : Blo 1144635 1146987 := bstep (se 1 (by rfl) ⟨860240, by rfl⟩ : syracuseStep 1146987 = 1720481) B1720481
theorem B1146999 : Blo 1144635 1146999 := bstep (se 1 (by rfl) ⟨860249, by rfl⟩ : syracuseStep 1146999 = 1720499) B1720499
theorem B1147019 : Blo 1144635 1147019 := bstep (se 1 (by rfl) ⟨860264, by rfl⟩ : syracuseStep 1147019 = 1720529) B1720529
theorem B1933463 : Blo 1144635 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B1147031 : Blo 1144635 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B1147051 : Blo 1144635 1147051 := bstep (se 1 (by rfl) ⟨860288, by rfl⟩ : syracuseStep 1147051 = 1720577) B1720577
theorem B1147063 : Blo 1144635 1147063 := bstep (se 1 (by rfl) ⟨860297, by rfl⟩ : syracuseStep 1147063 = 1720595) B1720595
theorem B1147083 : Blo 1144635 1147083 := bstep (se 1 (by rfl) ⟨860312, by rfl⟩ : syracuseStep 1147083 = 1720625) B1720625
theorem B1147095 : Blo 1144635 1147095 := bstep (se 1 (by rfl) ⟨860321, by rfl⟩ : syracuseStep 1147095 = 1720643) B1720643
theorem B1147115 : Blo 1144635 1147115 := bstep (se 1 (by rfl) ⟨860336, by rfl⟩ : syracuseStep 1147115 = 1720673) B1720673
theorem B1147127 : Blo 1144635 1147127 := bstep (se 1 (by rfl) ⟨860345, by rfl⟩ : syracuseStep 1147127 = 1720691) B1720691
theorem B1147147 : Blo 1144635 1147147 := bstep (se 1 (by rfl) ⟨860360, by rfl⟩ : syracuseStep 1147147 = 1720721) B1720721
theorem B1933591 : Blo 1144635 1933591 := bstep (se 1 (by rfl) ⟨1450193, by rfl⟩ : syracuseStep 1933591 = 2900387) B2900387
theorem B1147159 : Blo 1144635 1147159 := bstep (se 1 (by rfl) ⟨860369, by rfl⟩ : syracuseStep 1147159 = 1720739) B1720739
theorem B1147179 : Blo 1144635 1147179 := bstep (se 1 (by rfl) ⟨860384, by rfl⟩ : syracuseStep 1147179 = 1720769) B1720769
theorem B27885869 : Blo 1144635 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B1147191 : Blo 1144635 1147191 := bstep (se 1 (by rfl) ⟨860393, by rfl⟩ : syracuseStep 1147191 = 1720787) B1720787
theorem B1147211 : Blo 1144635 1147211 := bstep (se 1 (by rfl) ⟨860408, by rfl⟩ : syracuseStep 1147211 = 1720817) B1720817
theorem B1147223 : Blo 1144635 1147223 := bstep (se 1 (by rfl) ⟨860417, by rfl⟩ : syracuseStep 1147223 = 1720835) B1720835
theorem B1147243 : Blo 1144635 1147243 := bstep (se 1 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 1147243 = 1720865) B1720865
theorem B2064755 : Blo 1144635 2064755 := bstep (se 1 (by rfl) ⟨1548566, by rfl⟩ : syracuseStep 2064755 = 3097133) B3097133
theorem B1147255 : Blo 1144635 1147255 := bstep (se 1 (by rfl) ⟨860441, by rfl⟩ : syracuseStep 1147255 = 1720883) B1720883
theorem B1147275 : Blo 1144635 1147275 := bstep (se 1 (by rfl) ⟨860456, by rfl⟩ : syracuseStep 1147275 = 1720913) B1720913
theorem B1147287 : Blo 1144635 1147287 := bstep (se 1 (by rfl) ⟨860465, by rfl⟩ : syracuseStep 1147287 = 1720931) B1720931
theorem B1147307 : Blo 1144635 1147307 := bstep (se 1 (by rfl) ⟨860480, by rfl⟩ : syracuseStep 1147307 = 1720961) B1720961
theorem B1147319 : Blo 1144635 1147319 := bstep (se 1 (by rfl) ⟨860489, by rfl⟩ : syracuseStep 1147319 = 1720979) B1720979
theorem B1147339 : Blo 1144635 1147339 := bstep (se 1 (by rfl) ⟨860504, by rfl⟩ : syracuseStep 1147339 = 1721009) B1721009
theorem B1147351 : Blo 1144635 1147351 := bstep (se 1 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 1147351 = 1721027) B1721027
theorem B5800409 : Blo 1144635 5800409 := bstep (se 2 (by rfl) ⟨2175153, by rfl⟩ : syracuseStep 5800409 = 4350307) B4350307
theorem B3867101 : Blo 1144635 3867101 := bstep (se 3 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 3867101 = 1450163) B1450163
theorem B1147371 : Blo 1144635 1147371 := bstep (se 1 (by rfl) ⟨860528, by rfl⟩ : syracuseStep 1147371 = 1721057) B1721057
theorem B1147383 : Blo 1144635 1147383 := bstep (se 1 (by rfl) ⟨860537, by rfl⟩ : syracuseStep 1147383 = 1721075) B1721075
theorem B1147403 : Blo 1144635 1147403 := bstep (se 1 (by rfl) ⟨860552, by rfl⟩ : syracuseStep 1147403 = 1721105) B1721105
theorem B1835543 : Blo 1144635 1835543 := bstep (se 1 (by rfl) ⟨1376657, by rfl⟩ : syracuseStep 1835543 = 2753315) B2753315
theorem B1147415 : Blo 1144635 1147415 := bstep (se 1 (by rfl) ⟨860561, by rfl⟩ : syracuseStep 1147415 = 1721123) B1721123
theorem B1147435 : Blo 1144635 1147435 := bstep (se 1 (by rfl) ⟨860576, by rfl⟩ : syracuseStep 1147435 = 1721153) B1721153
theorem B1147447 : Blo 1144635 1147447 := bstep (se 1 (by rfl) ⟨860585, by rfl⟩ : syracuseStep 1147447 = 1721171) B1721171
theorem B1147467 : Blo 1144635 1147467 := bstep (se 1 (by rfl) ⟨860600, by rfl⟩ : syracuseStep 1147467 = 1721201) B1721201
theorem B1147479 : Blo 1144635 1147479 := bstep (se 1 (by rfl) ⟨860609, by rfl⟩ : syracuseStep 1147479 = 1721219) B1721219
theorem B16515677 : Blo 1144635 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B1147499 : Blo 1144635 1147499 := bstep (se 1 (by rfl) ⟨860624, by rfl⟩ : syracuseStep 1147499 = 1721249) B1721249
theorem B1147511 : Blo 1144635 1147511 := bstep (se 1 (by rfl) ⟨860633, by rfl⟩ : syracuseStep 1147511 = 1721267) B1721267
theorem B1147531 : Blo 1144635 1147531 := bstep (se 1 (by rfl) ⟨860648, by rfl⟩ : syracuseStep 1147531 = 1721297) B1721297
theorem B1147543 : Blo 1144635 1147543 := bstep (se 1 (by rfl) ⟨860657, by rfl⟩ : syracuseStep 1147543 = 1721315) B1721315
theorem B1147563 : Blo 1144635 1147563 := bstep (se 1 (by rfl) ⟨860672, by rfl⟩ : syracuseStep 1147563 = 1721345) B1721345
theorem B1147575 : Blo 1144635 1147575 := bstep (se 1 (by rfl) ⟨860681, by rfl⟩ : syracuseStep 1147575 = 1721363) B1721363
theorem B1147595 : Blo 1144635 1147595 := bstep (se 1 (by rfl) ⟨860696, by rfl⟩ : syracuseStep 1147595 = 1721393) B1721393
theorem B1147607 : Blo 1144635 1147607 := bstep (se 1 (by rfl) ⟨860705, by rfl⟩ : syracuseStep 1147607 = 1721411) B1721411
theorem B4358873 : Blo 1144635 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B1147627 : Blo 1144635 1147627 := bstep (se 1 (by rfl) ⟨860720, by rfl⟩ : syracuseStep 1147627 = 1721441) B1721441
theorem B1147639 : Blo 1144635 1147639 := bstep (se 1 (by rfl) ⟨860729, by rfl⟩ : syracuseStep 1147639 = 1721459) B1721459
theorem B1147659 : Blo 1144635 1147659 := bstep (se 1 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 1147659 = 1721489) B1721489
theorem B1147671 : Blo 1144635 1147671 := bstep (se 1 (by rfl) ⟨860753, by rfl⟩ : syracuseStep 1147671 = 1721507) B1721507
theorem B1147691 : Blo 1144635 1147691 := bstep (se 1 (by rfl) ⟨860768, by rfl⟩ : syracuseStep 1147691 = 1721537) B1721537
theorem B4653875 : Blo 1144635 4653875 := bstep (se 1 (by rfl) ⟨3490406, by rfl⟩ : syracuseStep 4653875 = 6980813) B6980813
theorem B1147703 : Blo 1144635 1147703 := bstep (se 1 (by rfl) ⟨860777, by rfl⟩ : syracuseStep 1147703 = 1721555) B1721555
theorem B1147723 : Blo 1144635 1147723 := bstep (se 1 (by rfl) ⟨860792, by rfl⟩ : syracuseStep 1147723 = 1721585) B1721585
theorem B1147735 : Blo 1144635 1147735 := bstep (se 1 (by rfl) ⟨860801, by rfl⟩ : syracuseStep 1147735 = 1721603) B1721603
theorem B1147755 : Blo 1144635 1147755 := bstep (se 1 (by rfl) ⟨860816, by rfl⟩ : syracuseStep 1147755 = 1721633) B1721633
theorem B1147767 : Blo 1144635 1147767 := bstep (se 1 (by rfl) ⟨860825, by rfl⟩ : syracuseStep 1147767 = 1721651) B1721651
theorem B1934219 : Blo 1144635 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1147787 : Blo 1144635 1147787 := bstep (se 1 (by rfl) ⟨860840, by rfl⟩ : syracuseStep 1147787 = 1721681) B1721681
theorem B1147799 : Blo 1144635 1147799 := bstep (se 1 (by rfl) ⟨860849, by rfl⟩ : syracuseStep 1147799 = 1721699) B1721699
theorem B2327449 : Blo 1144635 2327449 := bstep (se 2 (by rfl) ⟨872793, by rfl⟩ : syracuseStep 2327449 = 1745587) B1745587
theorem B1147819 : Blo 1144635 1147819 := bstep (se 1 (by rfl) ⟨860864, by rfl⟩ : syracuseStep 1147819 = 1721729) B1721729
theorem B1147831 : Blo 1144635 1147831 := bstep (se 1 (by rfl) ⟨860873, by rfl⟩ : syracuseStep 1147831 = 1721747) B1721747
theorem B1147851 : Blo 1144635 1147851 := bstep (se 1 (by rfl) ⟨860888, by rfl⟩ : syracuseStep 1147851 = 1721777) B1721777
theorem B1147863 : Blo 1144635 1147863 := bstep (se 1 (by rfl) ⟨860897, by rfl⟩ : syracuseStep 1147863 = 1721795) B1721795
theorem B1147883 : Blo 1144635 1147883 := bstep (se 1 (by rfl) ⟨860912, by rfl⟩ : syracuseStep 1147883 = 1721825) B1721825
theorem B1147895 : Blo 1144635 1147895 := bstep (se 1 (by rfl) ⟨860921, by rfl⟩ : syracuseStep 1147895 = 1721843) B1721843
theorem B1934347 : Blo 1144635 1934347 := bstep (se 1 (by rfl) ⟨1450760, by rfl⟩ : syracuseStep 1934347 = 2901521) B2901521
theorem B1147915 : Blo 1144635 1147915 := bstep (se 1 (by rfl) ⟨860936, by rfl⟩ : syracuseStep 1147915 = 1721873) B1721873
theorem B1836055 : Blo 1144635 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B1147927 : Blo 1144635 1147927 := bstep (se 1 (by rfl) ⟨860945, by rfl⟩ : syracuseStep 1147927 = 1721891) B1721891
theorem B1147947 : Blo 1144635 1147947 := bstep (se 1 (by rfl) ⟨860960, by rfl⟩ : syracuseStep 1147947 = 1721921) B1721921
theorem B1147959 : Blo 1144635 1147959 := bstep (se 1 (by rfl) ⟨860969, by rfl⟩ : syracuseStep 1147959 = 1721939) B1721939
theorem B1147979 : Blo 1144635 1147979 := bstep (se 1 (by rfl) ⟨860984, by rfl⟩ : syracuseStep 1147979 = 1721969) B1721969
theorem B1147991 : Blo 1144635 1147991 := bstep (se 1 (by rfl) ⟨860993, by rfl⟩ : syracuseStep 1147991 = 1721987) B1721987
theorem B1148011 : Blo 1144635 1148011 := bstep (se 1 (by rfl) ⟨861008, by rfl⟩ : syracuseStep 1148011 = 1722017) B1722017
theorem B1148023 : Blo 1144635 1148023 := bstep (se 1 (by rfl) ⟨861017, by rfl⟩ : syracuseStep 1148023 = 1722035) B1722035
theorem B1148043 : Blo 1144635 1148043 := bstep (se 1 (by rfl) ⟨861032, by rfl⟩ : syracuseStep 1148043 = 1722065) B1722065
theorem B1148055 : Blo 1144635 1148055 := bstep (se 1 (by rfl) ⟨861041, by rfl⟩ : syracuseStep 1148055 = 1722083) B1722083
theorem B1934489 : Blo 1144635 1934489 := bstep (se 2 (by rfl) ⟨725433, by rfl⟩ : syracuseStep 1934489 = 1450867) B1450867
theorem B1148075 : Blo 1144635 1148075 := bstep (se 1 (by rfl) ⟨861056, by rfl⟩ : syracuseStep 1148075 = 1722113) B1722113
theorem B1148087 : Blo 1144635 1148087 := bstep (se 1 (by rfl) ⟨861065, by rfl⟩ : syracuseStep 1148087 = 1722131) B1722131
theorem B4719809 : Blo 1144635 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1148107 : Blo 1144635 1148107 := bstep (se 1 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 1148107 = 1722161) B1722161
theorem B1148119 : Blo 1144635 1148119 := bstep (se 1 (by rfl) ⟨861089, by rfl⟩ : syracuseStep 1148119 = 1722179) B1722179
theorem B1148139 : Blo 1144635 1148139 := bstep (se 1 (by rfl) ⟨861104, by rfl⟩ : syracuseStep 1148139 = 1722209) B1722209
theorem B1148151 : Blo 1144635 1148151 := bstep (se 1 (by rfl) ⟨861113, by rfl⟩ : syracuseStep 1148151 = 1722227) B1722227
theorem B1148171 : Blo 1144635 1148171 := bstep (se 1 (by rfl) ⟨861128, by rfl⟩ : syracuseStep 1148171 = 1722257) B1722257
theorem B1148183 : Blo 1144635 1148183 := bstep (se 1 (by rfl) ⟨861137, by rfl⟩ : syracuseStep 1148183 = 1722275) B1722275
theorem B1934617 : Blo 1144635 1934617 := bstep (se 2 (by rfl) ⟨725481, by rfl⟩ : syracuseStep 1934617 = 1450963) B1450963
theorem B1148203 : Blo 1144635 1148203 := bstep (se 1 (by rfl) ⟨861152, by rfl⟩ : syracuseStep 1148203 = 1722305) B1722305
theorem B2753843 : Blo 1144635 2753843 := bstep (se 1 (by rfl) ⟨2065382, by rfl⟩ : syracuseStep 2753843 = 4130765) B4130765
theorem B1148215 : Blo 1144635 1148215 := bstep (se 1 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 1148215 = 1722323) B1722323
theorem B1148235 : Blo 1144635 1148235 := bstep (se 1 (by rfl) ⟨861176, by rfl⟩ : syracuseStep 1148235 = 1722353) B1722353
theorem B1148247 : Blo 1144635 1148247 := bstep (se 1 (by rfl) ⟨861185, by rfl⟩ : syracuseStep 1148247 = 1722371) B1722371
theorem B1148267 : Blo 1144635 1148267 := bstep (se 1 (by rfl) ⟨861200, by rfl⟩ : syracuseStep 1148267 = 1722401) B1722401
theorem B1148279 : Blo 1144635 1148279 := bstep (se 1 (by rfl) ⟨861209, by rfl⟩ : syracuseStep 1148279 = 1722419) B1722419
theorem B1836427 : Blo 1144635 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B1148299 : Blo 1144635 1148299 := bstep (se 1 (by rfl) ⟨861224, by rfl⟩ : syracuseStep 1148299 = 1722449) B1722449
theorem B1148311 : Blo 1144635 1148311 := bstep (se 1 (by rfl) ⟨861233, by rfl⟩ : syracuseStep 1148311 = 1722467) B1722467
theorem B1148331 : Blo 1144635 1148331 := bstep (se 1 (by rfl) ⟨861248, by rfl⟩ : syracuseStep 1148331 = 1722497) B1722497
theorem B1148343 : Blo 1144635 1148343 := bstep (se 1 (by rfl) ⟨861257, by rfl⟩ : syracuseStep 1148343 = 1722515) B1722515
theorem B1148363 : Blo 1144635 1148363 := bstep (se 1 (by rfl) ⟨861272, by rfl⟩ : syracuseStep 1148363 = 1722545) B1722545
theorem B1148375 : Blo 1144635 1148375 := bstep (se 1 (by rfl) ⟨861281, by rfl⟩ : syracuseStep 1148375 = 1722563) B1722563
theorem B1148395 : Blo 1144635 1148395 := bstep (se 1 (by rfl) ⟨861296, by rfl⟩ : syracuseStep 1148395 = 1722593) B1722593
theorem B1148407 : Blo 1144635 1148407 := bstep (se 1 (by rfl) ⟨861305, by rfl⟩ : syracuseStep 1148407 = 1722611) B1722611
theorem B1148427 : Blo 1144635 1148427 := bstep (se 1 (by rfl) ⟨861320, by rfl⟩ : syracuseStep 1148427 = 1722641) B1722641
theorem B1148439 : Blo 1144635 1148439 := bstep (se 1 (by rfl) ⟨861329, by rfl⟩ : syracuseStep 1148439 = 1722659) B1722659
theorem B1148459 : Blo 1144635 1148459 := bstep (se 1 (by rfl) ⟨861344, by rfl⟩ : syracuseStep 1148459 = 1722689) B1722689
theorem B1148471 : Blo 1144635 1148471 := bstep (se 1 (by rfl) ⟨861353, by rfl⟩ : syracuseStep 1148471 = 1722707) B1722707
theorem B3868235 : Blo 1144635 3868235 := bstep (se 1 (by rfl) ⟨2901176, by rfl⟩ : syracuseStep 3868235 = 5802353) B5802353
theorem B1148491 : Blo 1144635 1148491 := bstep (se 1 (by rfl) ⟨861368, by rfl⟩ : syracuseStep 1148491 = 1722737) B1722737
theorem B1148503 : Blo 1144635 1148503 := bstep (se 1 (by rfl) ⟨861377, by rfl⟩ : syracuseStep 1148503 = 1722755) B1722755
theorem B4654685 : Blo 1144635 4654685 := bstep (se 3 (by rfl) ⟨872753, by rfl⟩ : syracuseStep 4654685 = 1745507) B1745507
theorem B1148523 : Blo 1144635 1148523 := bstep (se 1 (by rfl) ⟨861392, by rfl⟩ : syracuseStep 1148523 = 1722785) B1722785
theorem B1148535 : Blo 1144635 1148535 := bstep (se 1 (by rfl) ⟨861401, by rfl⟩ : syracuseStep 1148535 = 1722803) B1722803
theorem B1148555 : Blo 1144635 1148555 := bstep (se 1 (by rfl) ⟨861416, by rfl⟩ : syracuseStep 1148555 = 1722833) B1722833
theorem B1148567 : Blo 1144635 1148567 := bstep (se 1 (by rfl) ⟨861425, by rfl⟩ : syracuseStep 1148567 = 1722851) B1722851
theorem B1148587 : Blo 1144635 1148587 := bstep (se 1 (by rfl) ⟨861440, by rfl⟩ : syracuseStep 1148587 = 1722881) B1722881
theorem B6981299 : Blo 1144635 6981299 := bstep (se 1 (by rfl) ⟨5235974, by rfl⟩ : syracuseStep 6981299 = 10471949) B10471949
theorem B1148599 : Blo 1144635 1148599 := bstep (se 1 (by rfl) ⟨861449, by rfl⟩ : syracuseStep 1148599 = 1722899) B1722899
theorem B1148619 : Blo 1144635 1148619 := bstep (se 1 (by rfl) ⟨861464, by rfl⟩ : syracuseStep 1148619 = 1722929) B1722929
theorem B1148631 : Blo 1144635 1148631 := bstep (se 1 (by rfl) ⟨861473, by rfl⟩ : syracuseStep 1148631 = 1722947) B1722947
theorem B4130605 : Blo 1144635 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B1836875 : Blo 1144635 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B1935191 : Blo 1144635 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B3868505 : Blo 1144635 3868505 := bstep (se 2 (by rfl) ⟨1450689, by rfl⟩ : syracuseStep 3868505 = 2901379) B2901379
theorem B1935319 : Blo 1144635 1935319 := bstep (se 1 (by rfl) ⟨1451489, by rfl⟩ : syracuseStep 1935319 = 2902979) B2902979
theorem B6195217 : Blo 1144635 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B8718353 : Blo 1144635 8718353 := bstep (se 2 (by rfl) ⟨3269382, by rfl⟩ : syracuseStep 8718353 = 6538765) B6538765
theorem B5802029 : Blo 1144635 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B9799811 : Blo 1144635 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B4360499 : Blo 1144635 4360499 := bstep (se 1 (by rfl) ⟨3270374, by rfl⟩ : syracuseStep 4360499 = 6540749) B6540749
theorem B6195521 : Blo 1144635 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B13076801 : Blo 1144635 13076801 := bstep (se 2 (by rfl) ⟨4903800, by rfl⟩ : syracuseStep 13076801 = 9807601) B9807601
theorem B4360513 : Blo 1144635 4360513 := bstep (se 2 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 4360513 = 3270385) B3270385
theorem B19564901 : Blo 1144635 19564901 := bstep (se 4 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 19564901 = 3668419) B3668419
theorem B2754967 : Blo 1144635 2754967 := bstep (se 1 (by rfl) ⟨2066225, by rfl⟩ : syracuseStep 2754967 = 4132451) B4132451
theorem B3869207 : Blo 1144635 3869207 := bstep (se 1 (by rfl) ⟨2901905, by rfl⟩ : syracuseStep 3869207 = 5803811) B5803811
theorem B1935947 : Blo 1144635 1935947 := bstep (se 1 (by rfl) ⟨1451960, by rfl⟩ : syracuseStep 1935947 = 2903921) B2903921
theorem B1837657 : Blo 1144635 1837657 := bstep (se 2 (by rfl) ⟨689121, by rfl⟩ : syracuseStep 1837657 = 1378243) B1378243
theorem B1936075 : Blo 1144635 1936075 := bstep (se 1 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 1936075 = 2904113) B2904113
theorem B4655819 : Blo 1144635 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1936217 : Blo 1144635 1936217 := bstep (se 2 (by rfl) ⟨726081, by rfl⟩ : syracuseStep 1936217 = 1452163) B1452163
theorem B1936345 : Blo 1144635 1936345 := bstep (se 2 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 1936345 = 1452259) B1452259
theorem B3869747 : Blo 1144635 3869747 := bstep (se 1 (by rfl) ⟨2902310, by rfl⟩ : syracuseStep 3869747 = 5804621) B5804621
theorem B6982807 : Blo 1144635 6982807 := bstep (se 1 (by rfl) ⟨5237105, by rfl⟩ : syracuseStep 6982807 = 10474211) B10474211
theorem B3870017 : Blo 1144635 3870017 := bstep (se 2 (by rfl) ⟨1451256, by rfl⟩ : syracuseStep 3870017 = 2902513) B2902513
theorem B1936919 : Blo 1144635 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B1937047 : Blo 1144635 1937047 := bstep (se 1 (by rfl) ⟨1452785, by rfl⟩ : syracuseStep 1937047 = 2905571) B2905571
theorem B4034393 : Blo 1144635 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B3870557 : Blo 1144635 3870557 := bstep (se 3 (by rfl) ⟨725729, by rfl⟩ : syracuseStep 3870557 = 1451459) B1451459
theorem B3674263 : Blo 1144635 3674263 := bstep (se 1 (by rfl) ⟨2755697, by rfl⟩ : syracuseStep 3674263 = 5511395) B5511395
theorem B3674315 : Blo 1144635 3674315 := bstep (se 1 (by rfl) ⟨2755736, by rfl⟩ : syracuseStep 3674315 = 5511473) B5511473
theorem B9310469 : Blo 1144635 9310469 := bstep (se 4 (by rfl) ⟨872856, by rfl⟩ : syracuseStep 9310469 = 1745713) B1745713
theorem B1937675 : Blo 1144635 1937675 := bstep (se 1 (by rfl) ⟨1453256, by rfl⟩ : syracuseStep 1937675 = 2906513) B2906513
theorem B1937803 : Blo 1144635 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B1937945 : Blo 1144635 1937945 := bstep (se 2 (by rfl) ⟨726729, by rfl⟩ : syracuseStep 1937945 = 1453459) B1453459
theorem B1938073 : Blo 1144635 1938073 := bstep (se 2 (by rfl) ⟨726777, by rfl⟩ : syracuseStep 1938073 = 1453555) B1453555
theorem B3871691 : Blo 1144635 3871691 := bstep (se 1 (by rfl) ⟨2903768, by rfl⟩ : syracuseStep 3871691 = 5807537) B5807537
theorem B9933899 : Blo 1144635 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B6526169 : Blo 1144635 6526169 := bstep (se 2 (by rfl) ⟨2447313, by rfl⟩ : syracuseStep 6526169 = 4894627) B4894627
theorem B3871961 : Blo 1144635 3871961 := bstep (se 2 (by rfl) ⟨1451985, by rfl⟩ : syracuseStep 3871961 = 2903971) B2903971
theorem B1742231 : Blo 1144635 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B3675955 : Blo 1144635 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B2758465 : Blo 1144635 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B8722241 : Blo 1144635 8722241 := bstep (se 2 (by rfl) ⟨3270840, by rfl⟩ : syracuseStep 8722241 = 6541681) B6541681
theorem B5805917 : Blo 1144635 5805917 := bstep (se 3 (by rfl) ⟨1088609, by rfl⟩ : syracuseStep 5805917 = 2177219) B2177219
theorem B3872663 : Blo 1144635 3872663 := bstep (se 1 (by rfl) ⟨2904497, by rfl⟩ : syracuseStep 3872663 = 5808995) B5808995
theorem B18585521 : Blo 1144635 18585521 := bstep (se 2 (by rfl) ⟨6969570, by rfl⟩ : syracuseStep 18585521 = 13939141) B13939141
theorem B3676097 : Blo 1144635 3676097 := bstep (se 2 (by rfl) ⟨1378536, by rfl⟩ : syracuseStep 3676097 = 2757073) B2757073
theorem B1743257 : Blo 1144635 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B3873203 : Blo 1144635 3873203 := bstep (se 1 (by rfl) ⟨2904902, by rfl⟩ : syracuseStep 3873203 = 5809805) B5809805
theorem B3873473 : Blo 1144635 3873473 := bstep (se 2 (by rfl) ⟨1452552, by rfl⟩ : syracuseStep 3873473 = 2905105) B2905105
theorem B4135853 : Blo 1144635 4135853 := bstep (se 3 (by rfl) ⟨775472, by rfl⟩ : syracuseStep 4135853 = 1550945) B1550945
theorem B7445465 : Blo 1144635 7445465 := bstep (se 2 (by rfl) ⟨2792049, by rfl⟩ : syracuseStep 7445465 = 5584099) B5584099
theorem B2235595 : Blo 1144635 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B3874013 : Blo 1144635 3874013 := bstep (se 3 (by rfl) ⟨726377, by rfl⟩ : syracuseStep 3874013 = 1452755) B1452755
theorem B8822033 : Blo 1144635 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B6201011 : Blo 1144635 6201011 := bstep (se 1 (by rfl) ⟨4650758, by rfl⟩ : syracuseStep 6201011 = 9301517) B9301517
theorem B6528833 : Blo 1144635 6528833 := bstep (se 2 (by rfl) ⟨2448312, by rfl⟩ : syracuseStep 6528833 = 4896625) B4896625
theorem B5808023 : Blo 1144635 5808023 := bstep (se 1 (by rfl) ⟨4356017, by rfl⟩ : syracuseStep 5808023 = 8712035) B8712035
theorem B10461361 : Blo 1144635 10461361 := bstep (se 2 (by rfl) ⟨3923010, by rfl⟩ : syracuseStep 10461361 = 7846021) B7846021
theorem B1450315 : Blo 1144635 1450315 := bstep (se 1 (by rfl) ⟨1087736, by rfl⟩ : syracuseStep 1450315 = 2175473) B2175473
theorem B3875147 : Blo 1144635 3875147 := bstep (se 1 (by rfl) ⟨2906360, by rfl⟩ : syracuseStep 3875147 = 5812721) B5812721
theorem B16556561 : Blo 1144635 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B4891211 : Blo 1144635 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B3875417 : Blo 1144635 3875417 := bstep (se 2 (by rfl) ⟨1453281, by rfl⟩ : syracuseStep 3875417 = 2906563) B2906563
theorem B7349399 : Blo 1144635 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B1451287 : Blo 1144635 1451287 := bstep (se 1 (by rfl) ⟨1088465, by rfl⟩ : syracuseStep 1451287 = 2176931) B2176931
theorem B3876119 : Blo 1144635 3876119 := bstep (se 1 (by rfl) ⟨2907089, by rfl⟩ : syracuseStep 3876119 = 5814179) B5814179
theorem B8365517 : Blo 1144635 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B4892183 : Blo 1144635 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B5514817 : Blo 1144635 5514817 := bstep (se 2 (by rfl) ⟨2068056, by rfl⟩ : syracuseStep 5514817 = 4136113) B4136113
theorem B1287787 : Blo 1144635 1287787 := bstep (se 1 (by rfl) ⟨965840, by rfl⟩ : syracuseStep 1287787 = 1931681) B1931681
theorem B7349939 : Blo 1144635 7349939 := bstep (se 1 (by rfl) ⟨5512454, by rfl⟩ : syracuseStep 7349939 = 11024909) B11024909
theorem B1287895 : Blo 1144635 1287895 := bstep (se 1 (by rfl) ⟨965921, by rfl⟩ : syracuseStep 1287895 = 1931843) B1931843
theorem B4138883 : Blo 1144635 4138883 := bstep (se 1 (by rfl) ⟨3104162, by rfl⟩ : syracuseStep 4138883 = 6208325) B6208325
theorem B1288075 : Blo 1144635 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B5875607 : Blo 1144635 5875607 := bstep (se 1 (by rfl) ⟨4406705, by rfl⟩ : syracuseStep 5875607 = 8813411) B8813411
theorem B1288183 : Blo 1144635 1288183 := bstep (se 1 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 1288183 = 1932275) B1932275
theorem B1452107 : Blo 1144635 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B2173043 : Blo 1144635 2173043 := bstep (se 1 (by rfl) ⟨1629782, by rfl⟩ : syracuseStep 2173043 = 3259565) B3259565
theorem B2173081 : Blo 1144635 2173081 := bstep (se 2 (by rfl) ⟨814905, by rfl⟩ : syracuseStep 2173081 = 1629811) B1629811
theorem B1288363 : Blo 1144635 1288363 := bstep (se 1 (by rfl) ⟨966272, by rfl⟩ : syracuseStep 1288363 = 1932545) B1932545
theorem B1288471 : Blo 1144635 1288471 := bstep (se 1 (by rfl) ⟨966353, by rfl⟩ : syracuseStep 1288471 = 1932707) B1932707
theorem B1288651 : Blo 1144635 1288651 := bstep (se 1 (by rfl) ⟨966488, by rfl⟩ : syracuseStep 1288651 = 1932977) B1932977
theorem B22325777 : Blo 1144635 22325777 := bstep (se 2 (by rfl) ⟨8372166, by rfl⟩ : syracuseStep 22325777 = 16744333) B16744333
theorem B1223191 : Blo 1144635 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B4139543 : Blo 1144635 4139543 := bstep (se 1 (by rfl) ⟨3104657, by rfl⟩ : syracuseStep 4139543 = 6209315) B6209315
theorem B1288759 : Blo 1144635 1288759 := bstep (se 1 (by rfl) ⟨966569, by rfl⟩ : syracuseStep 1288759 = 1933139) B1933139
theorem B2173529 : Blo 1144635 2173529 := bstep (se 2 (by rfl) ⟨815073, by rfl⟩ : syracuseStep 2173529 = 1630147) B1630147
theorem B7842521 : Blo 1144635 7842521 := bstep (se 2 (by rfl) ⟨2940945, by rfl⟩ : syracuseStep 7842521 = 5881891) B5881891
theorem B1288939 : Blo 1144635 1288939 := bstep (se 1 (by rfl) ⟨966704, by rfl⟩ : syracuseStep 1288939 = 1933409) B1933409
theorem B1452811 : Blo 1144635 1452811 := bstep (se 1 (by rfl) ⟨1089608, by rfl⟩ : syracuseStep 1452811 = 2179217) B2179217
theorem B57256769 : Blo 1144635 57256769 := bstep (se 2 (by rfl) ⟨21471288, by rfl⟩ : syracuseStep 57256769 = 42942577) B42942577
theorem B1289047 : Blo 1144635 1289047 := bstep (se 1 (by rfl) ⟨966785, by rfl⟩ : syracuseStep 1289047 = 1933571) B1933571
theorem B1289227 : Blo 1144635 1289227 := bstep (se 1 (by rfl) ⟨966920, by rfl⟩ : syracuseStep 1289227 = 1933841) B1933841
theorem B1453079 : Blo 1144635 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B7351397 : Blo 1144635 7351397 := bstep (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) B1378387
theorem B1289335 : Blo 1144635 1289335 := bstep (se 1 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 1289335 = 1934003) B1934003
theorem B1289515 : Blo 1144635 1289515 := bstep (se 1 (by rfl) ⟨967136, by rfl⟩ : syracuseStep 1289515 = 1934273) B1934273
theorem B2174273 : Blo 1144635 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B5811587 : Blo 1144635 5811587 := bstep (se 1 (by rfl) ⟨4358690, by rfl⟩ : syracuseStep 5811587 = 8717381) B8717381
theorem B1289623 : Blo 1144635 1289623 := bstep (se 1 (by rfl) ⟨967217, by rfl⟩ : syracuseStep 1289623 = 1934435) B1934435
theorem B2174539 : Blo 1144635 2174539 := bstep (se 1 (by rfl) ⟨1630904, by rfl⟩ : syracuseStep 2174539 = 3261809) B3261809
theorem B1289803 : Blo 1144635 1289803 := bstep (se 1 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 1289803 = 1934705) B1934705
theorem B9809585 : Blo 1144635 9809585 := bstep (se 2 (by rfl) ⟨3678594, by rfl⟩ : syracuseStep 9809585 = 7357189) B7357189
theorem B1289911 : Blo 1144635 1289911 := bstep (se 1 (by rfl) ⟨967433, by rfl⟩ : syracuseStep 1289911 = 1934867) B1934867
theorem B1290091 : Blo 1144635 1290091 := bstep (se 1 (by rfl) ⟨967568, by rfl⟩ : syracuseStep 1290091 = 1935137) B1935137
theorem B4894643 : Blo 1144635 4894643 := bstep (se 1 (by rfl) ⟨3670982, by rfl⟩ : syracuseStep 4894643 = 7341965) B7341965
theorem B1290199 : Blo 1144635 1290199 := bstep (se 1 (by rfl) ⟨967649, by rfl⟩ : syracuseStep 1290199 = 1935299) B1935299
theorem B2174987 : Blo 1144635 2174987 := bstep (se 1 (by rfl) ⟨1631240, by rfl⟩ : syracuseStep 2174987 = 3262481) B3262481
theorem B1290379 : Blo 1144635 1290379 := bstep (se 1 (by rfl) ⟨967784, by rfl⟩ : syracuseStep 1290379 = 1935569) B1935569
theorem B1224887 : Blo 1144635 1224887 := bstep (se 1 (by rfl) ⟨918665, by rfl⟩ : syracuseStep 1224887 = 1837331) B1837331
theorem B2175169 : Blo 1144635 2175169 := bstep (se 2 (by rfl) ⟨815688, by rfl⟩ : syracuseStep 2175169 = 1631377) B1631377
theorem B1290487 : Blo 1144635 1290487 := bstep (se 1 (by rfl) ⟨967865, by rfl⟩ : syracuseStep 1290487 = 1935731) B1935731
theorem B8827211 : Blo 1144635 8827211 := bstep (se 1 (by rfl) ⟨6620408, by rfl⟩ : syracuseStep 8827211 = 13240817) B13240817
theorem B1290667 : Blo 1144635 1290667 := bstep (se 1 (by rfl) ⟨968000, by rfl⟩ : syracuseStep 1290667 = 1936001) B1936001
theorem B2175511 : Blo 1144635 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B1290775 : Blo 1144635 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B8270437 : Blo 1144635 8270437 := bstep (se 4 (by rfl) ⟨775353, by rfl⟩ : syracuseStep 8270437 = 1550707) B1550707
theorem B1290955 : Blo 1144635 1290955 := bstep (se 1 (by rfl) ⟨968216, by rfl⟩ : syracuseStep 1290955 = 1936433) B1936433
theorem B1716953 : Blo 1144635 1716953 := bstep (se 2 (by rfl) ⟨643857, by rfl⟩ : syracuseStep 1716953 = 1287715) B1287715
theorem B2175731 : Blo 1144635 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B1291063 : Blo 1144635 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1717067 : Blo 1144635 1717067 := bstep (se 1 (by rfl) ⟨1287800, by rfl⟩ : syracuseStep 1717067 = 2575601) B2575601
theorem B1717079 : Blo 1144635 1717079 := bstep (se 1 (by rfl) ⟨1287809, by rfl⟩ : syracuseStep 1717079 = 2575619) B2575619
theorem B1717145 : Blo 1144635 1717145 := bstep (se 2 (by rfl) ⟨643929, by rfl⟩ : syracuseStep 1717145 = 1287859) B1287859
theorem B2175959 : Blo 1144635 2175959 := bstep (se 1 (by rfl) ⟨1631969, by rfl⟩ : syracuseStep 2175959 = 3263939) B3263939
theorem B1291243 : Blo 1144635 1291243 := bstep (se 1 (by rfl) ⟨968432, by rfl⟩ : syracuseStep 1291243 = 1936865) B1936865
theorem B1717259 : Blo 1144635 1717259 := bstep (se 1 (by rfl) ⟨1287944, by rfl⟩ : syracuseStep 1717259 = 2575889) B2575889
theorem B1717271 : Blo 1144635 1717271 := bstep (se 1 (by rfl) ⟨1287953, by rfl⟩ : syracuseStep 1717271 = 2575907) B2575907
theorem B6534209 : Blo 1144635 6534209 := bstep (se 2 (by rfl) ⟨2450328, by rfl⟩ : syracuseStep 6534209 = 4900657) B4900657
theorem B2208833 : Blo 1144635 2208833 := bstep (se 2 (by rfl) ⟨828312, by rfl⟩ : syracuseStep 2208833 = 1656625) B1656625
theorem B1291351 : Blo 1144635 1291351 := bstep (se 1 (by rfl) ⟨968513, by rfl⟩ : syracuseStep 1291351 = 1937027) B1937027
theorem B1717337 : Blo 1144635 1717337 := bstep (se 2 (by rfl) ⟨644001, by rfl⟩ : syracuseStep 1717337 = 1288003) B1288003
theorem B1160363 : Blo 1144635 1160363 := bstep (se 1 (by rfl) ⟨870272, by rfl⟩ : syracuseStep 1160363 = 1740545) B1740545
theorem B1717451 : Blo 1144635 1717451 := bstep (se 1 (by rfl) ⟨1288088, by rfl⟩ : syracuseStep 1717451 = 2576177) B2576177
theorem B1717463 : Blo 1144635 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B2176217 : Blo 1144635 2176217 := bstep (se 2 (by rfl) ⟨816081, by rfl⟩ : syracuseStep 2176217 = 1632163) B1632163
theorem B1291531 : Blo 1144635 1291531 := bstep (se 1 (by rfl) ⟨968648, by rfl⟩ : syracuseStep 1291531 = 1937297) B1937297
theorem B1717529 : Blo 1144635 1717529 := bstep (se 2 (by rfl) ⟨644073, by rfl⟩ : syracuseStep 1717529 = 1288147) B1288147
theorem B1291639 : Blo 1144635 1291639 := bstep (se 1 (by rfl) ⟨968729, by rfl⟩ : syracuseStep 1291639 = 1937459) B1937459
theorem B1717643 : Blo 1144635 1717643 := bstep (se 1 (by rfl) ⟨1288232, by rfl⟩ : syracuseStep 1717643 = 2576465) B2576465
theorem B1717655 : Blo 1144635 1717655 := bstep (se 1 (by rfl) ⟨1288241, by rfl⟩ : syracuseStep 1717655 = 2576483) B2576483
theorem B1160663 : Blo 1144635 1160663 := bstep (se 1 (by rfl) ⟨870497, by rfl⟩ : syracuseStep 1160663 = 1740995) B1740995
theorem B1717721 : Blo 1144635 1717721 := bstep (se 2 (by rfl) ⟨644145, by rfl⟩ : syracuseStep 1717721 = 1288291) B1288291
theorem B1160695 : Blo 1144635 1160695 := bstep (se 1 (by rfl) ⟨870521, by rfl⟩ : syracuseStep 1160695 = 1741043) B1741043
theorem B1291819 : Blo 1144635 1291819 := bstep (se 1 (by rfl) ⟨968864, by rfl⟩ : syracuseStep 1291819 = 1937729) B1937729
theorem B1717835 : Blo 1144635 1717835 := bstep (se 1 (by rfl) ⟨1288376, by rfl⟩ : syracuseStep 1717835 = 2576753) B2576753
theorem B1717847 : Blo 1144635 1717847 := bstep (se 1 (by rfl) ⟨1288385, by rfl⟩ : syracuseStep 1717847 = 2576771) B2576771
theorem B2176627 : Blo 1144635 2176627 := bstep (se 1 (by rfl) ⟨1632470, by rfl⟩ : syracuseStep 2176627 = 3264941) B3264941
theorem B11941507 : Blo 1144635 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B1291927 : Blo 1144635 1291927 := bstep (se 1 (by rfl) ⟨968945, by rfl⟩ : syracuseStep 1291927 = 1937891) B1937891
theorem B1717913 : Blo 1144635 1717913 := bstep (se 2 (by rfl) ⟨644217, by rfl⟩ : syracuseStep 1717913 = 1288435) B1288435
theorem B1718027 : Blo 1144635 1718027 := bstep (se 1 (by rfl) ⟨1288520, by rfl⟩ : syracuseStep 1718027 = 2577041) B2577041
theorem B1718039 : Blo 1144635 1718039 := bstep (se 1 (by rfl) ⟨1288529, by rfl⟩ : syracuseStep 1718039 = 2577059) B2577059
theorem B4896557 : Blo 1144635 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B1292107 : Blo 1144635 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B1718105 : Blo 1144635 1718105 := bstep (se 2 (by rfl) ⟨644289, by rfl⟩ : syracuseStep 1718105 = 1288579) B1288579
theorem B2045785 : Blo 1144635 2045785 := bstep (se 2 (by rfl) ⟨767169, by rfl⟩ : syracuseStep 2045785 = 1534339) B1534339
theorem B2897815 : Blo 1144635 2897815 := bstep (se 1 (by rfl) ⟨2173361, by rfl⟩ : syracuseStep 2897815 = 4346723) B4346723
theorem B1292215 : Blo 1144635 1292215 := bstep (se 1 (by rfl) ⟨969161, by rfl⟩ : syracuseStep 1292215 = 1938323) B1938323
theorem B1718219 : Blo 1144635 1718219 := bstep (se 1 (by rfl) ⟨1288664, by rfl⟩ : syracuseStep 1718219 = 2577329) B2577329
theorem B8370125 : Blo 1144635 8370125 := bstep (se 3 (by rfl) ⟨1569398, by rfl⟩ : syracuseStep 8370125 = 3138797) B3138797
theorem B1718231 : Blo 1144635 1718231 := bstep (se 1 (by rfl) ⟨1288673, by rfl⟩ : syracuseStep 1718231 = 2577347) B2577347
theorem B1161227 : Blo 1144635 1161227 := bstep (se 1 (by rfl) ⟨870920, by rfl⟩ : syracuseStep 1161227 = 1741841) B1741841
theorem B1718297 : Blo 1144635 1718297 := bstep (se 2 (by rfl) ⟨644361, by rfl⟩ : syracuseStep 1718297 = 1288723) B1288723
theorem B2177113 : Blo 1144635 2177113 := bstep (se 2 (by rfl) ⟨816417, by rfl⟩ : syracuseStep 2177113 = 1632835) B1632835
theorem B4896899 : Blo 1144635 4896899 := bstep (se 1 (by rfl) ⟨3672674, by rfl⟩ : syracuseStep 4896899 = 7345349) B7345349
theorem B1718411 : Blo 1144635 1718411 := bstep (se 1 (by rfl) ⟨1288808, by rfl⟩ : syracuseStep 1718411 = 2577617) B2577617
theorem B1718423 : Blo 1144635 1718423 := bstep (se 1 (by rfl) ⟨1288817, by rfl⟩ : syracuseStep 1718423 = 2577635) B2577635
theorem B2209943 : Blo 1144635 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1718489 : Blo 1144635 1718489 := bstep (se 2 (by rfl) ⟨644433, by rfl⟩ : syracuseStep 1718489 = 1288867) B1288867
theorem B2898251 : Blo 1144635 2898251 := bstep (se 1 (by rfl) ⟨2173688, by rfl⟩ : syracuseStep 2898251 = 4347377) B4347377
theorem B1718603 : Blo 1144635 1718603 := bstep (se 1 (by rfl) ⟨1288952, by rfl⟩ : syracuseStep 1718603 = 2577905) B2577905
theorem B1718615 : Blo 1144635 1718615 := bstep (se 1 (by rfl) ⟨1288961, by rfl⟩ : syracuseStep 1718615 = 2577923) B2577923
theorem B1718681 : Blo 1144635 1718681 := bstep (se 2 (by rfl) ⟨644505, by rfl⟩ : syracuseStep 1718681 = 1289011) B1289011
theorem B9779717 : Blo 1144635 9779717 := bstep (se 4 (by rfl) ⟨916848, by rfl⟩ : syracuseStep 9779717 = 1833697) B1833697
theorem B1718795 : Blo 1144635 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B1718807 : Blo 1144635 1718807 := bstep (se 1 (by rfl) ⟨1289105, by rfl⟩ : syracuseStep 1718807 = 2578211) B2578211
theorem B1718873 : Blo 1144635 1718873 := bstep (se 2 (by rfl) ⟨644577, by rfl⟩ : syracuseStep 1718873 = 1289155) B1289155
theorem B2177675 : Blo 1144635 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B2898625 : Blo 1144635 2898625 := bstep (se 2 (by rfl) ⟨1086984, by rfl⟩ : syracuseStep 2898625 = 2173969) B2173969
theorem B1718987 : Blo 1144635 1718987 := bstep (se 1 (by rfl) ⟨1289240, by rfl⟩ : syracuseStep 1718987 = 2578481) B2578481
theorem B1718999 : Blo 1144635 1718999 := bstep (se 1 (by rfl) ⟨1289249, by rfl⟩ : syracuseStep 1718999 = 2578499) B2578499
theorem B8272601 : Blo 1144635 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B1719065 : Blo 1144635 1719065 := bstep (se 2 (by rfl) ⟨644649, by rfl⟩ : syracuseStep 1719065 = 1289299) B1289299
theorem B2177857 : Blo 1144635 2177857 := bstep (se 2 (by rfl) ⟨816696, by rfl⟩ : syracuseStep 2177857 = 1633393) B1633393
theorem B1719179 : Blo 1144635 1719179 := bstep (se 1 (by rfl) ⟨1289384, by rfl⟩ : syracuseStep 1719179 = 2578769) B2578769
theorem B1719191 : Blo 1144635 1719191 := bstep (se 1 (by rfl) ⟨1289393, by rfl⟩ : syracuseStep 1719191 = 2578787) B2578787
theorem B1719257 : Blo 1144635 1719257 := bstep (se 2 (by rfl) ⟨644721, by rfl⟩ : syracuseStep 1719257 = 1289443) B1289443
theorem B1719371 : Blo 1144635 1719371 := bstep (se 1 (by rfl) ⟨1289528, by rfl⟩ : syracuseStep 1719371 = 2579057) B2579057
theorem B1719383 : Blo 1144635 1719383 := bstep (se 1 (by rfl) ⟨1289537, by rfl⟩ : syracuseStep 1719383 = 2579075) B2579075
theorem B1719449 : Blo 1144635 1719449 := bstep (se 2 (by rfl) ⟨644793, by rfl⟩ : syracuseStep 1719449 = 1289587) B1289587
theorem B1719563 : Blo 1144635 1719563 := bstep (se 1 (by rfl) ⟨1289672, by rfl⟩ : syracuseStep 1719563 = 2579345) B2579345
theorem B2899223 : Blo 1144635 2899223 := bstep (se 1 (by rfl) ⟨2174417, by rfl⟩ : syracuseStep 2899223 = 4348835) B4348835
theorem B1719575 : Blo 1144635 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B1719641 : Blo 1144635 1719641 := bstep (se 2 (by rfl) ⟨644865, by rfl⟩ : syracuseStep 1719641 = 1289731) B1289731
theorem B1719755 : Blo 1144635 1719755 := bstep (se 1 (by rfl) ⟨1289816, by rfl⟩ : syracuseStep 1719755 = 2579633) B2579633
theorem B1719767 : Blo 1144635 1719767 := bstep (se 1 (by rfl) ⟨1289825, by rfl⟩ : syracuseStep 1719767 = 2579651) B2579651
theorem B2178571 : Blo 1144635 2178571 := bstep (se 1 (by rfl) ⟨1633928, by rfl⟩ : syracuseStep 2178571 = 3267857) B3267857
theorem B1719833 : Blo 1144635 1719833 := bstep (se 2 (by rfl) ⟨644937, by rfl⟩ : syracuseStep 1719833 = 1289875) B1289875
theorem B2178647 : Blo 1144635 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B3259997 : Blo 1144635 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B1719947 : Blo 1144635 1719947 := bstep (se 1 (by rfl) ⟨1289960, by rfl⟩ : syracuseStep 1719947 = 2579921) B2579921
theorem B1719959 : Blo 1144635 1719959 := bstep (se 1 (by rfl) ⟨1289969, by rfl⟩ : syracuseStep 1719959 = 2579939) B2579939
theorem B4406957 : Blo 1144635 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B1720025 : Blo 1144635 1720025 := bstep (se 2 (by rfl) ⟨645009, by rfl⟩ : syracuseStep 1720025 = 1290019) B1290019
theorem B6209297 : Blo 1144635 6209297 := bstep (se 2 (by rfl) ⟨2328486, by rfl⟩ : syracuseStep 6209297 = 4656973) B4656973
theorem B3260225 : Blo 1144635 3260225 := bstep (se 2 (by rfl) ⟨1222584, by rfl⟩ : syracuseStep 3260225 = 2445169) B2445169
theorem B1720139 : Blo 1144635 1720139 := bstep (se 1 (by rfl) ⟨1290104, by rfl⟩ : syracuseStep 1720139 = 2580209) B2580209
theorem B1720151 : Blo 1144635 1720151 := bstep (se 1 (by rfl) ⟨1290113, by rfl⟩ : syracuseStep 1720151 = 2580227) B2580227
theorem B1720217 : Blo 1144635 1720217 := bstep (se 2 (by rfl) ⟨645081, by rfl⟩ : syracuseStep 1720217 = 1290163) B1290163
theorem B1720331 : Blo 1144635 1720331 := bstep (se 1 (by rfl) ⟨1290248, by rfl⟩ : syracuseStep 1720331 = 2580497) B2580497
theorem B1720343 : Blo 1144635 1720343 := bstep (se 1 (by rfl) ⟨1290257, by rfl⟩ : syracuseStep 1720343 = 2580515) B2580515
theorem B2900033 : Blo 1144635 2900033 := bstep (se 2 (by rfl) ⟨1087512, by rfl⟩ : syracuseStep 2900033 = 2175025) B2175025
theorem B24756293 : Blo 1144635 24756293 := bstep (se 4 (by rfl) ⟨2320902, by rfl⟩ : syracuseStep 24756293 = 4641805) B4641805
theorem B1720409 : Blo 1144635 1720409 := bstep (se 2 (by rfl) ⟨645153, by rfl⟩ : syracuseStep 1720409 = 1290307) B1290307
theorem B3260567 : Blo 1144635 3260567 := bstep (se 1 (by rfl) ⟨2445425, by rfl⟩ : syracuseStep 3260567 = 4890851) B4890851
theorem B1720523 : Blo 1144635 1720523 := bstep (se 1 (by rfl) ⟨1290392, by rfl⟩ : syracuseStep 1720523 = 2580785) B2580785
theorem B1720535 : Blo 1144635 1720535 := bstep (se 1 (by rfl) ⟨1290401, by rfl⟩ : syracuseStep 1720535 = 2580803) B2580803
theorem B2179315 : Blo 1144635 2179315 := bstep (se 1 (by rfl) ⟨1634486, by rfl⟩ : syracuseStep 2179315 = 3268973) B3268973
theorem B1720601 : Blo 1144635 1720601 := bstep (se 2 (by rfl) ⟨645225, by rfl⟩ : syracuseStep 1720601 = 1290451) B1290451
theorem B8274241 : Blo 1144635 8274241 := bstep (se 2 (by rfl) ⟨3102840, by rfl⟩ : syracuseStep 8274241 = 6205681) B6205681
theorem B1720715 : Blo 1144635 1720715 := bstep (se 1 (by rfl) ⟨1290536, by rfl⟩ : syracuseStep 1720715 = 2581073) B2581073
theorem B1720727 : Blo 1144635 1720727 := bstep (se 1 (by rfl) ⟨1290545, by rfl⟩ : syracuseStep 1720727 = 2581091) B2581091
theorem B4899275 : Blo 1144635 4899275 := bstep (se 1 (by rfl) ⟨3674456, by rfl⟩ : syracuseStep 4899275 = 7348913) B7348913
theorem B2179543 : Blo 1144635 2179543 := bstep (se 1 (by rfl) ⟨1634657, by rfl⟩ : syracuseStep 2179543 = 3269315) B3269315
theorem B1720793 : Blo 1144635 1720793 := bstep (se 2 (by rfl) ⟨645297, by rfl⟩ : syracuseStep 1720793 = 1290595) B1290595
theorem B2179649 : Blo 1144635 2179649 := bstep (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) B1634737
theorem B1720907 : Blo 1144635 1720907 := bstep (se 1 (by rfl) ⟨1290680, by rfl⟩ : syracuseStep 1720907 = 2581361) B2581361
theorem B1720919 : Blo 1144635 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B2900569 : Blo 1144635 2900569 := bstep (se 2 (by rfl) ⟨1087713, by rfl⟩ : syracuseStep 2900569 = 2175427) B2175427
theorem B1720985 : Blo 1144635 1720985 := bstep (se 2 (by rfl) ⟨645369, by rfl⟩ : syracuseStep 1720985 = 1290739) B1290739
theorem B2179801 : Blo 1144635 2179801 := bstep (se 2 (by rfl) ⟨817425, by rfl⟩ : syracuseStep 2179801 = 1634851) B1634851
theorem B1721099 : Blo 1144635 1721099 := bstep (se 1 (by rfl) ⟨1290824, by rfl⟩ : syracuseStep 1721099 = 2581649) B2581649
theorem B1721111 : Blo 1144635 1721111 := bstep (se 1 (by rfl) ⟨1290833, by rfl⟩ : syracuseStep 1721111 = 2581667) B2581667
theorem B5882669 : Blo 1144635 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B1721177 : Blo 1144635 1721177 := bstep (se 2 (by rfl) ⟨645441, by rfl⟩ : syracuseStep 1721177 = 1290883) B1290883
theorem B3916637 : Blo 1144635 3916637 := bstep (se 3 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 3916637 = 1468739) B1468739
theorem B1721291 : Blo 1144635 1721291 := bstep (se 1 (by rfl) ⟨1290968, by rfl⟩ : syracuseStep 1721291 = 2581937) B2581937
theorem B1721303 : Blo 1144635 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B1721369 : Blo 1144635 1721369 := bstep (se 2 (by rfl) ⟨645513, by rfl⟩ : syracuseStep 1721369 = 1291027) B1291027
theorem B3097651 : Blo 1144635 3097651 := bstep (se 1 (by rfl) ⟨2323238, by rfl⟩ : syracuseStep 3097651 = 4646477) B4646477
theorem B22037579 : Blo 1144635 22037579 := bstep (se 1 (by rfl) ⟨16528184, by rfl⟩ : syracuseStep 22037579 = 33056369) B33056369
theorem B1721483 : Blo 1144635 1721483 := bstep (se 1 (by rfl) ⟨1291112, by rfl⟩ : syracuseStep 1721483 = 2582225) B2582225
theorem B1721495 : Blo 1144635 1721495 := bstep (se 1 (by rfl) ⟨1291121, by rfl⟩ : syracuseStep 1721495 = 2582243) B2582243
theorem B1721561 : Blo 1144635 1721561 := bstep (se 2 (by rfl) ⟨645585, by rfl⟩ : syracuseStep 1721561 = 1291171) B1291171
theorem B1721675 : Blo 1144635 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B1721687 : Blo 1144635 1721687 := bstep (se 1 (by rfl) ⟨1291265, by rfl⟩ : syracuseStep 1721687 = 2582531) B2582531
theorem B4900247 : Blo 1144635 4900247 := bstep (se 1 (by rfl) ⟨3675185, by rfl⟩ : syracuseStep 4900247 = 7350371) B7350371
theorem B1721753 : Blo 1144635 1721753 := bstep (se 2 (by rfl) ⟨645657, by rfl⟩ : syracuseStep 1721753 = 1291315) B1291315
theorem B1721867 : Blo 1144635 1721867 := bstep (se 1 (by rfl) ⟨1291400, by rfl⟩ : syracuseStep 1721867 = 2582801) B2582801
theorem B1721879 : Blo 1144635 1721879 := bstep (se 1 (by rfl) ⟨1291409, by rfl⟩ : syracuseStep 1721879 = 2582819) B2582819
theorem B1721945 : Blo 1144635 1721945 := bstep (se 2 (by rfl) ⟨645729, by rfl⟩ : syracuseStep 1721945 = 1291459) B1291459
theorem B2901683 : Blo 1144635 2901683 := bstep (se 1 (by rfl) ⟨2176262, by rfl⟩ : syracuseStep 2901683 = 4352525) B4352525
theorem B1722059 : Blo 1144635 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B1722071 : Blo 1144635 1722071 := bstep (se 1 (by rfl) ⟨1291553, by rfl⟩ : syracuseStep 1722071 = 2583107) B2583107
theorem B1722137 : Blo 1144635 1722137 := bstep (se 2 (by rfl) ⟨645801, by rfl⟩ : syracuseStep 1722137 = 1291603) B1291603
theorem B19384109 : Blo 1144635 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B1722251 : Blo 1144635 1722251 := bstep (se 1 (by rfl) ⟨1291688, by rfl⟩ : syracuseStep 1722251 = 2583377) B2583377
theorem B1722263 : Blo 1144635 1722263 := bstep (se 1 (by rfl) ⟨1291697, by rfl⟩ : syracuseStep 1722263 = 2583395) B2583395
theorem B2901977 : Blo 1144635 2901977 := bstep (se 2 (by rfl) ⟨1088241, by rfl⟩ : syracuseStep 2901977 = 2176483) B2176483
theorem B1722329 : Blo 1144635 1722329 := bstep (se 2 (by rfl) ⟨645873, by rfl⟩ : syracuseStep 1722329 = 1291747) B1291747
theorem B9783341 : Blo 1144635 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B1722443 : Blo 1144635 1722443 := bstep (se 1 (by rfl) ⟨1291832, by rfl⟩ : syracuseStep 1722443 = 2583665) B2583665
theorem B1722455 : Blo 1144635 1722455 := bstep (se 1 (by rfl) ⟨1291841, by rfl⟩ : syracuseStep 1722455 = 2583683) B2583683
theorem B11028631 : Blo 1144635 11028631 := bstep (se 1 (by rfl) ⟨8271473, by rfl⟩ : syracuseStep 11028631 = 16542947) B16542947
theorem B1722521 : Blo 1144635 1722521 := bstep (se 2 (by rfl) ⟨645945, by rfl⟩ : syracuseStep 1722521 = 1291891) B1291891
theorem B1722635 : Blo 1144635 1722635 := bstep (se 1 (by rfl) ⟨1291976, by rfl⟩ : syracuseStep 1722635 = 2583953) B2583953
theorem B1722647 : Blo 1144635 1722647 := bstep (se 1 (by rfl) ⟨1291985, by rfl⟩ : syracuseStep 1722647 = 2583971) B2583971
theorem B1722713 : Blo 1144635 1722713 := bstep (se 2 (by rfl) ⟨646017, by rfl⟩ : syracuseStep 1722713 = 1292035) B1292035
theorem B3262913 : Blo 1144635 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B1722827 : Blo 1144635 1722827 := bstep (se 1 (by rfl) ⟨1292120, by rfl⟩ : syracuseStep 1722827 = 2584241) B2584241
theorem B1722839 : Blo 1144635 1722839 := bstep (se 1 (by rfl) ⟨1292129, by rfl⟩ : syracuseStep 1722839 = 2584259) B2584259
theorem B1722905 : Blo 1144635 1722905 := bstep (se 2 (by rfl) ⟨646089, by rfl⟩ : syracuseStep 1722905 = 1292179) B1292179
theorem B3263449 : Blo 1144635 3263449 := bstep (se 2 (by rfl) ⟨1223793, by rfl⟩ : syracuseStep 3263449 = 2447587) B2447587
theorem B3492887 : Blo 1144635 3492887 := bstep (se 1 (by rfl) ⟨2619665, by rfl⟩ : syracuseStep 3492887 = 5239331) B5239331
theorem B1789015 : Blo 1144635 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B2575475 : Blo 1144635 2575475 := bstep (se 1 (by rfl) ⟨1931606, by rfl⟩ : syracuseStep 2575475 = 3863213) B3863213
theorem B2575511 : Blo 1144635 2575511 := bstep (se 1 (by rfl) ⟨1931633, by rfl⟩ : syracuseStep 2575511 = 3863267) B3863267
theorem B11029709 : Blo 1144635 11029709 := bstep (se 3 (by rfl) ⟨2068070, by rfl⟩ : syracuseStep 11029709 = 4136141) B4136141
theorem B2575691 : Blo 1144635 2575691 := bstep (se 1 (by rfl) ⟨1931768, by rfl⟩ : syracuseStep 2575691 = 3863537) B3863537
theorem B11029861 : Blo 1144635 11029861 := bstep (se 4 (by rfl) ⟨1034049, by rfl⟩ : syracuseStep 11029861 = 2068099) B2068099
theorem B2575745 : Blo 1144635 2575745 := bstep (se 2 (by rfl) ⟨965904, by rfl⟩ : syracuseStep 2575745 = 1931809) B1931809
theorem B2444759 : Blo 1144635 2444759 := bstep (se 1 (by rfl) ⟨1833569, by rfl⟩ : syracuseStep 2444759 = 3667139) B3667139
theorem B2903627 : Blo 1144635 2903627 := bstep (se 1 (by rfl) ⟨2177720, by rfl⟩ : syracuseStep 2903627 = 4355441) B4355441
theorem B2575961 : Blo 1144635 2575961 := bstep (se 2 (by rfl) ⟨965985, by rfl⟩ : syracuseStep 2575961 = 1931971) B1931971
theorem B2576051 : Blo 1144635 2576051 := bstep (se 1 (by rfl) ⟨1932038, by rfl⟩ : syracuseStep 2576051 = 3864077) B3864077
theorem B2576087 : Blo 1144635 2576087 := bstep (se 1 (by rfl) ⟨1932065, by rfl⟩ : syracuseStep 2576087 = 3864131) B3864131
theorem B4902707 : Blo 1144635 4902707 := bstep (se 1 (by rfl) ⟨3677030, by rfl⟩ : syracuseStep 4902707 = 7354061) B7354061
theorem B2576267 : Blo 1144635 2576267 := bstep (se 1 (by rfl) ⟨1932200, by rfl⟩ : syracuseStep 2576267 = 3864401) B3864401
theorem B2576321 : Blo 1144635 2576321 := bstep (se 2 (by rfl) ⟨966120, by rfl⟩ : syracuseStep 2576321 = 1932241) B1932241
theorem B2576537 : Blo 1144635 2576537 := bstep (se 2 (by rfl) ⟨966201, by rfl⟩ : syracuseStep 2576537 = 1932403) B1932403
theorem B3723457 : Blo 1144635 3723457 := bstep (se 2 (by rfl) ⟨1396296, by rfl⟩ : syracuseStep 3723457 = 2792593) B2792593
theorem B2576627 : Blo 1144635 2576627 := bstep (se 1 (by rfl) ⟨1932470, by rfl⟩ : syracuseStep 2576627 = 3864941) B3864941
theorem B2576663 : Blo 1144635 2576663 := bstep (se 1 (by rfl) ⟨1932497, by rfl⟩ : syracuseStep 2576663 = 3864995) B3864995
theorem B9785731 : Blo 1144635 9785731 := bstep (se 1 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 9785731 = 14678597) B14678597
theorem B2576843 : Blo 1144635 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B2576897 : Blo 1144635 2576897 := bstep (se 2 (by rfl) ⟨966336, by rfl⟩ : syracuseStep 2576897 = 1932673) B1932673
theorem B2904599 : Blo 1144635 2904599 := bstep (se 1 (by rfl) ⟨2178449, by rfl⟩ : syracuseStep 2904599 = 4356899) B4356899
theorem B4346419 : Blo 1144635 4346419 := bstep (se 1 (by rfl) ⟨3259814, by rfl⟩ : syracuseStep 4346419 = 6519629) B6519629
theorem B21189251 : Blo 1144635 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B2577113 : Blo 1144635 2577113 := bstep (se 2 (by rfl) ⟨966417, by rfl⟩ : syracuseStep 2577113 = 1932835) B1932835
theorem B2577203 : Blo 1144635 2577203 := bstep (se 1 (by rfl) ⟨1932902, by rfl⟩ : syracuseStep 2577203 = 3865805) B3865805
theorem B5591873 : Blo 1144635 5591873 := bstep (se 2 (by rfl) ⟨2096952, by rfl⟩ : syracuseStep 5591873 = 4193905) B4193905
theorem B2577239 : Blo 1144635 2577239 := bstep (se 1 (by rfl) ⟨1932929, by rfl⟩ : syracuseStep 2577239 = 3865859) B3865859
theorem B3265373 : Blo 1144635 3265373 := bstep (se 3 (by rfl) ⟨612257, by rfl⟩ : syracuseStep 3265373 = 1224515) B1224515
theorem B2577419 : Blo 1144635 2577419 := bstep (se 1 (by rfl) ⟨1933064, by rfl⟩ : syracuseStep 2577419 = 3866129) B3866129
theorem B2577473 : Blo 1144635 2577473 := bstep (se 2 (by rfl) ⟨966552, by rfl⟩ : syracuseStep 2577473 = 1933105) B1933105
theorem B2905267 : Blo 1144635 2905267 := bstep (se 1 (by rfl) ⟨2178950, by rfl⟩ : syracuseStep 2905267 = 4357901) B4357901
theorem B2577689 : Blo 1144635 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B9786689 : Blo 1144635 9786689 := bstep (se 2 (by rfl) ⟨3670008, by rfl⟩ : syracuseStep 9786689 = 7340017) B7340017
theorem B2905409 : Blo 1144635 2905409 := bstep (se 2 (by rfl) ⟨1089528, by rfl⟩ : syracuseStep 2905409 = 2179057) B2179057
theorem B2577779 : Blo 1144635 2577779 := bstep (se 1 (by rfl) ⟨1933334, by rfl⟩ : syracuseStep 2577779 = 3866669) B3866669
theorem B2577815 : Blo 1144635 2577815 := bstep (se 1 (by rfl) ⟨1933361, by rfl⟩ : syracuseStep 2577815 = 3866723) B3866723
theorem B2577995 : Blo 1144635 2577995 := bstep (se 1 (by rfl) ⟨1933496, by rfl⟩ : syracuseStep 2577995 = 3866993) B3866993
theorem B9557597 : Blo 1144635 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B2578049 : Blo 1144635 2578049 := bstep (se 2 (by rfl) ⟨966768, by rfl⟩ : syracuseStep 2578049 = 1933537) B1933537
theorem B8377987 : Blo 1144635 8377987 := bstep (se 1 (by rfl) ⟨6283490, by rfl⟩ : syracuseStep 8377987 = 12566981) B12566981
theorem B4904621 : Blo 1144635 4904621 := bstep (se 3 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 4904621 = 1839233) B1839233
theorem B3102401 : Blo 1144635 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B4347665 : Blo 1144635 4347665 := bstep (se 2 (by rfl) ⟨1630374, by rfl⟩ : syracuseStep 4347665 = 3260749) B3260749
theorem B14702381 : Blo 1144635 14702381 := bstep (se 3 (by rfl) ⟨2756696, by rfl⟩ : syracuseStep 14702381 = 5513393) B5513393
theorem B2578265 : Blo 1144635 2578265 := bstep (se 2 (by rfl) ⟨966849, by rfl⟩ : syracuseStep 2578265 = 1933699) B1933699
theorem B2447219 : Blo 1144635 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B2578355 : Blo 1144635 2578355 := bstep (se 1 (by rfl) ⟨1933766, by rfl⟩ : syracuseStep 2578355 = 3867533) B3867533
theorem B2578391 : Blo 1144635 2578391 := bstep (se 1 (by rfl) ⟨1933793, by rfl⟩ : syracuseStep 2578391 = 3867587) B3867587
theorem B2578571 : Blo 1144635 2578571 := bstep (se 1 (by rfl) ⟨1933928, by rfl⟩ : syracuseStep 2578571 = 3867857) B3867857
theorem B2578625 : Blo 1144635 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B4905305 : Blo 1144635 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B2578841 : Blo 1144635 2578841 := bstep (se 2 (by rfl) ⟨967065, by rfl⟩ : syracuseStep 2578841 = 1934131) B1934131
theorem B4348363 : Blo 1144635 4348363 := bstep (se 1 (by rfl) ⟨3261272, by rfl⟩ : syracuseStep 4348363 = 6522545) B6522545
theorem B2578931 : Blo 1144635 2578931 := bstep (se 1 (by rfl) ⟨1934198, by rfl⟩ : syracuseStep 2578931 = 3868397) B3868397
theorem B2578967 : Blo 1144635 2578967 := bstep (se 1 (by rfl) ⟨1934225, by rfl⟩ : syracuseStep 2578967 = 3868451) B3868451
theorem B2906675 : Blo 1144635 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B15686237 : Blo 1144635 15686237 := bstep (se 3 (by rfl) ⟨2941169, by rfl⟩ : syracuseStep 15686237 = 5882339) B5882339
theorem B2579147 : Blo 1144635 2579147 := bstep (se 1 (by rfl) ⟨1934360, by rfl⟩ : syracuseStep 2579147 = 3868721) B3868721
theorem B4348637 : Blo 1144635 4348637 := bstep (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) B1630739
theorem B2579201 : Blo 1144635 2579201 := bstep (se 2 (by rfl) ⟨967200, by rfl⟩ : syracuseStep 2579201 = 1934401) B1934401
theorem B13065137 : Blo 1144635 13065137 := bstep (se 2 (by rfl) ⟨4899426, by rfl⟩ : syracuseStep 13065137 = 9798853) B9798853
theorem B2579417 : Blo 1144635 2579417 := bstep (se 2 (by rfl) ⟨967281, by rfl⟩ : syracuseStep 2579417 = 1934563) B1934563
theorem B2448407 : Blo 1144635 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B5233709 : Blo 1144635 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B2579507 : Blo 1144635 2579507 := bstep (se 1 (by rfl) ⟨1934630, by rfl⟩ : syracuseStep 2579507 = 3869261) B3869261
theorem B2907211 : Blo 1144635 2907211 := bstep (se 1 (by rfl) ⟨2180408, by rfl⟩ : syracuseStep 2907211 = 4360817) B4360817
theorem B2579543 : Blo 1144635 2579543 := bstep (se 1 (by rfl) ⟨1934657, by rfl⟩ : syracuseStep 2579543 = 3869315) B3869315
theorem B2907353 : Blo 1144635 2907353 := bstep (se 2 (by rfl) ⟨1090257, by rfl⟩ : syracuseStep 2907353 = 2180515) B2180515
theorem B2579723 : Blo 1144635 2579723 := bstep (se 1 (by rfl) ⟨1934792, by rfl⟩ : syracuseStep 2579723 = 3869585) B3869585
theorem B2579777 : Blo 1144635 2579777 := bstep (se 2 (by rfl) ⟨967416, by rfl⟩ : syracuseStep 2579777 = 1934833) B1934833
theorem B2612569 : Blo 1144635 2612569 := bstep (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) B1959427
theorem B4349335 : Blo 1144635 4349335 := bstep (se 1 (by rfl) ⟨3262001, by rfl⟩ : syracuseStep 4349335 = 6524003) B6524003
theorem B4971955 : Blo 1144635 4971955 := bstep (se 1 (by rfl) ⟨3728966, by rfl⟩ : syracuseStep 4971955 = 7457933) B7457933
theorem B22076945 : Blo 1144635 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B2579993 : Blo 1144635 2579993 := bstep (se 2 (by rfl) ⟨967497, by rfl⟩ : syracuseStep 2579993 = 1934995) B1934995
theorem B2580083 : Blo 1144635 2580083 := bstep (se 1 (by rfl) ⟨1935062, by rfl⟩ : syracuseStep 2580083 = 3870125) B3870125
theorem B2580119 : Blo 1144635 2580119 := bstep (se 1 (by rfl) ⟨1935089, by rfl⟩ : syracuseStep 2580119 = 3870179) B3870179
theorem B2612915 : Blo 1144635 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B3268289 : Blo 1144635 3268289 := bstep (se 2 (by rfl) ⟨1225608, by rfl⟩ : syracuseStep 3268289 = 2451217) B2451217
theorem B9297625 : Blo 1144635 9297625 := bstep (se 2 (by rfl) ⟨3486609, by rfl⟩ : syracuseStep 9297625 = 6973219) B6973219
theorem B3268313 : Blo 1144635 3268313 := bstep (se 2 (by rfl) ⟨1225617, by rfl⟩ : syracuseStep 3268313 = 2451235) B2451235
theorem B3104477 : Blo 1144635 3104477 := bstep (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) B1164179
theorem B2580299 : Blo 1144635 2580299 := bstep (se 1 (by rfl) ⟨1935224, by rfl⟩ : syracuseStep 2580299 = 3870449) B3870449
theorem B1630039 : Blo 1144635 1630039 := bstep (se 1 (by rfl) ⟨1222529, by rfl⟩ : syracuseStep 1630039 = 2445059) B2445059
theorem B9297757 : Blo 1144635 9297757 := bstep (se 3 (by rfl) ⟨1743329, by rfl⟩ : syracuseStep 9297757 = 3486659) B3486659
theorem B2580353 : Blo 1144635 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B2449433 : Blo 1144635 2449433 := bstep (se 2 (by rfl) ⟨918537, by rfl⟩ : syracuseStep 2449433 = 1837075) B1837075
theorem B2580569 : Blo 1144635 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B4350125 : Blo 1144635 4350125 := bstep (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) B1631297
theorem B2580659 : Blo 1144635 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B2580695 : Blo 1144635 2580695 := bstep (se 1 (by rfl) ⟨1935521, by rfl⟩ : syracuseStep 2580695 = 3871043) B3871043
theorem B4972823 : Blo 1144635 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B2580875 : Blo 1144635 2580875 := bstep (se 1 (by rfl) ⟨1935656, by rfl⟩ : syracuseStep 2580875 = 3871313) B3871313
theorem B10445233 : Blo 1144635 10445233 := bstep (se 2 (by rfl) ⟨3916962, by rfl⟩ : syracuseStep 10445233 = 7833925) B7833925
theorem B2580929 : Blo 1144635 2580929 := bstep (se 2 (by rfl) ⟨967848, by rfl⟩ : syracuseStep 2580929 = 1935697) B1935697
theorem B1860121 : Blo 1144635 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B2581145 : Blo 1144635 2581145 := bstep (se 2 (by rfl) ⟨967929, by rfl⟩ : syracuseStep 2581145 = 1935859) B1935859
theorem B13951693 : Blo 1144635 13951693 := bstep (se 3 (by rfl) ⟨2615942, by rfl⟩ : syracuseStep 13951693 = 5231885) B5231885
theorem B2581235 : Blo 1144635 2581235 := bstep (se 1 (by rfl) ⟨1935926, by rfl⟩ : syracuseStep 2581235 = 3871853) B3871853
theorem B2581271 : Blo 1144635 2581271 := bstep (se 1 (by rfl) ⟨1935953, by rfl⟩ : syracuseStep 2581271 = 3871907) B3871907
theorem B3269555 : Blo 1144635 3269555 := bstep (se 1 (by rfl) ⟨2452166, by rfl⟩ : syracuseStep 3269555 = 4904333) B4904333
theorem B2581451 : Blo 1144635 2581451 := bstep (se 1 (by rfl) ⟨1936088, by rfl⟩ : syracuseStep 2581451 = 3872177) B3872177
theorem B2581505 : Blo 1144635 2581505 := bstep (se 2 (by rfl) ⟨968064, by rfl⟩ : syracuseStep 2581505 = 1936129) B1936129
theorem B2450483 : Blo 1144635 2450483 := bstep (se 1 (by rfl) ⟨1837862, by rfl⟩ : syracuseStep 2450483 = 3675725) B3675725
theorem B2581721 : Blo 1144635 2581721 := bstep (se 2 (by rfl) ⟨968145, by rfl⟩ : syracuseStep 2581721 = 1936291) B1936291
theorem B2581811 : Blo 1144635 2581811 := bstep (se 1 (by rfl) ⟨1936358, by rfl⟩ : syracuseStep 2581811 = 3872717) B3872717
theorem B2581847 : Blo 1144635 2581847 := bstep (se 1 (by rfl) ⟨1936385, by rfl⟩ : syracuseStep 2581847 = 3872771) B3872771
theorem B2582027 : Blo 1144635 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B4351553 : Blo 1144635 4351553 := bstep (se 2 (by rfl) ⟨1631832, by rfl⟩ : syracuseStep 4351553 = 3263665) B3263665
theorem B2582081 : Blo 1144635 2582081 := bstep (se 2 (by rfl) ⟨968280, by rfl⟩ : syracuseStep 2582081 = 1936561) B1936561
theorem B2451073 : Blo 1144635 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B2582297 : Blo 1144635 2582297 := bstep (se 2 (by rfl) ⟨968361, by rfl⟩ : syracuseStep 2582297 = 1936723) B1936723
theorem B1632089 : Blo 1144635 1632089 := bstep (se 2 (by rfl) ⟨612033, by rfl⟩ : syracuseStep 1632089 = 1224067) B1224067
theorem B2582387 : Blo 1144635 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B2582423 : Blo 1144635 2582423 := bstep (se 1 (by rfl) ⟨1936817, by rfl⟩ : syracuseStep 2582423 = 3873635) B3873635
theorem B2582603 : Blo 1144635 2582603 := bstep (se 1 (by rfl) ⟨1936952, by rfl⟩ : syracuseStep 2582603 = 3873905) B3873905
theorem B2582657 : Blo 1144635 2582657 := bstep (se 2 (by rfl) ⟨968496, by rfl⟩ : syracuseStep 2582657 = 1936993) B1936993
theorem B4647257 : Blo 1144635 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B2582873 : Blo 1144635 2582873 := bstep (se 2 (by rfl) ⟨968577, by rfl⟩ : syracuseStep 2582873 = 1937155) B1937155
theorem B1960343 : Blo 1144635 1960343 := bstep (se 1 (by rfl) ⟨1470257, by rfl⟩ : syracuseStep 1960343 = 2940515) B2940515
theorem B8710577 : Blo 1144635 8710577 := bstep (se 2 (by rfl) ⟨3266466, by rfl⟩ : syracuseStep 8710577 = 6532933) B6532933
theorem B2582963 : Blo 1144635 2582963 := bstep (se 1 (by rfl) ⟨1937222, by rfl⟩ : syracuseStep 2582963 = 3874445) B3874445
theorem B1632727 : Blo 1144635 1632727 := bstep (se 1 (by rfl) ⟨1224545, by rfl⟩ : syracuseStep 1632727 = 2449091) B2449091
theorem B2582999 : Blo 1144635 2582999 := bstep (se 1 (by rfl) ⟨1937249, by rfl⟩ : syracuseStep 2582999 = 3874499) B3874499
theorem B1960535 : Blo 1144635 1960535 := bstep (se 1 (by rfl) ⟨1470401, by rfl⟩ : syracuseStep 1960535 = 2940803) B2940803
theorem B5237341 : Blo 1144635 5237341 := bstep (se 3 (by rfl) ⟨982001, by rfl⟩ : syracuseStep 5237341 = 1964003) B1964003
theorem B2583179 : Blo 1144635 2583179 := bstep (se 1 (by rfl) ⟨1937384, by rfl⟩ : syracuseStep 2583179 = 3874769) B3874769
theorem B2583233 : Blo 1144635 2583233 := bstep (se 2 (by rfl) ⟨968712, by rfl⟩ : syracuseStep 2583233 = 1937425) B1937425
theorem B1239767 : Blo 1144635 1239767 := bstep (se 1 (by rfl) ⟨929825, by rfl⟩ : syracuseStep 1239767 = 1859651) B1859651
theorem B8711063 : Blo 1144635 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B2583449 : Blo 1144635 2583449 := bstep (se 2 (by rfl) ⟨968793, by rfl⟩ : syracuseStep 2583449 = 1937587) B1937587
theorem B5794739 : Blo 1144635 5794739 := bstep (se 1 (by rfl) ⟨4346054, by rfl⟩ : syracuseStep 5794739 = 8692109) B8692109
theorem B2583539 : Blo 1144635 2583539 := bstep (se 1 (by rfl) ⟨1937654, by rfl⟩ : syracuseStep 2583539 = 3875309) B3875309
theorem B4353041 : Blo 1144635 4353041 := bstep (se 2 (by rfl) ⟨1632390, by rfl⟩ : syracuseStep 4353041 = 3264781) B3264781
theorem B2583575 : Blo 1144635 2583575 := bstep (se 1 (by rfl) ⟨1937681, by rfl⟩ : syracuseStep 2583575 = 3875363) B3875363
theorem B9301067 : Blo 1144635 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B1240183 : Blo 1144635 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B2452619 : Blo 1144635 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B2583755 : Blo 1144635 2583755 := bstep (se 1 (by rfl) ⟨1937816, by rfl⟩ : syracuseStep 2583755 = 3875633) B3875633
theorem B1764569 : Blo 1144635 1764569 := bstep (se 2 (by rfl) ⟨661713, by rfl⟩ : syracuseStep 1764569 = 1323427) B1323427
theorem B2583809 : Blo 1144635 2583809 := bstep (se 2 (by rfl) ⟨968928, by rfl⟩ : syracuseStep 2583809 = 1937857) B1937857
theorem B1633547 : Blo 1144635 1633547 := bstep (se 1 (by rfl) ⟨1225160, by rfl⟩ : syracuseStep 1633547 = 2450321) B2450321
theorem B4713821 : Blo 1144635 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B4353497 : Blo 1144635 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B2584025 : Blo 1144635 2584025 := bstep (se 2 (by rfl) ⟨969009, by rfl⟩ : syracuseStep 2584025 = 1938019) B1938019
theorem B2584115 : Blo 1144635 2584115 := bstep (se 1 (by rfl) ⟨1938086, by rfl⟩ : syracuseStep 2584115 = 3876173) B3876173
theorem B2584151 : Blo 1144635 2584151 := bstep (se 1 (by rfl) ⟨1938113, by rfl⟩ : syracuseStep 2584151 = 3876227) B3876227
theorem B4353709 : Blo 1144635 4353709 := bstep (se 3 (by rfl) ⟨816320, by rfl⟩ : syracuseStep 4353709 = 1632641) B1632641
theorem B2584331 : Blo 1144635 2584331 := bstep (se 1 (by rfl) ⟨1938248, by rfl⟩ : syracuseStep 2584331 = 3876497) B3876497
theorem B2584385 : Blo 1144635 2584385 := bstep (se 2 (by rfl) ⟨969144, by rfl⟩ : syracuseStep 2584385 = 1938289) B1938289
theorem B1961815 : Blo 1144635 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B4354013 : Blo 1144635 4354013 := bstep (se 3 (by rfl) ⟨816377, by rfl⟩ : syracuseStep 4354013 = 1632755) B1632755
theorem B1634521 : Blo 1144635 1634521 := bstep (se 2 (by rfl) ⟨612945, by rfl⟩ : syracuseStep 1634521 = 1225891) B1225891
theorem B8811013 : Blo 1144635 8811013 := bstep (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) B1652065
theorem B5796683 : Blo 1144635 5796683 := bstep (se 1 (by rfl) ⟨4347512, by rfl⟩ : syracuseStep 5796683 = 8695025) B8695025
theorem B2978635 : Blo 1144635 2978635 := bstep (se 1 (by rfl) ⟨2233976, by rfl⟩ : syracuseStep 2978635 = 4467953) B4467953
theorem B3863645 : Blo 1144635 3863645 := bstep (se 3 (by rfl) ⟨724433, by rfl⟩ : syracuseStep 3863645 = 1448867) B1448867
theorem B2651339 : Blo 1144635 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B1307927 : Blo 1144635 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B13038893 : Blo 1144635 13038893 := bstep (se 3 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 13038893 = 4889585) B4889585
theorem B2094913 : Blo 1144635 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1144651 : Blo 1144635 1144651 := bstep (se 1 (by rfl) ⟨858488, by rfl⟩ : syracuseStep 1144651 = 1716977) B1716977
theorem B1144663 : Blo 1144635 1144663 := bstep (se 1 (by rfl) ⟨858497, by rfl⟩ : syracuseStep 1144663 = 1716995) B1716995
theorem B3667805 : Blo 1144635 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B1144683 : Blo 1144635 1144683 := bstep (se 1 (by rfl) ⟨858512, by rfl⟩ : syracuseStep 1144683 = 1717025) B1717025
theorem B1144695 : Blo 1144635 1144695 := bstep (se 1 (by rfl) ⟨858521, by rfl⟩ : syracuseStep 1144695 = 1717043) B1717043
theorem B1144715 : Blo 1144635 1144715 := bstep (se 1 (by rfl) ⟨858536, by rfl⟩ : syracuseStep 1144715 = 1717073) B1717073
theorem B1570699 : Blo 1144635 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B1144727 : Blo 1144635 1144727 := bstep (se 1 (by rfl) ⟨858545, by rfl⟩ : syracuseStep 1144727 = 1717091) B1717091
theorem B1144747 : Blo 1144635 1144747 := bstep (se 1 (by rfl) ⟨858560, by rfl⟩ : syracuseStep 1144747 = 1717121) B1717121
theorem B41875379 : Blo 1144635 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B1144759 : Blo 1144635 1144759 := bstep (se 1 (by rfl) ⟨858569, by rfl⟩ : syracuseStep 1144759 = 1717139) B1717139
theorem B1144779 : Blo 1144635 1144779 := bstep (se 1 (by rfl) ⟨858584, by rfl⟩ : syracuseStep 1144779 = 1717169) B1717169
theorem B1144791 : Blo 1144635 1144791 := bstep (se 1 (by rfl) ⟨858593, by rfl⟩ : syracuseStep 1144791 = 1717187) B1717187
theorem B5502937 : Blo 1144635 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B3667933 : Blo 1144635 3667933 := bstep (se 3 (by rfl) ⟨687737, by rfl⟩ : syracuseStep 3667933 = 1375475) B1375475
theorem B1144811 : Blo 1144635 1144811 := bstep (se 1 (by rfl) ⟨858608, by rfl⟩ : syracuseStep 1144811 = 1717217) B1717217
theorem B1144823 : Blo 1144635 1144823 := bstep (se 1 (by rfl) ⟨858617, by rfl⟩ : syracuseStep 1144823 = 1717235) B1717235
theorem B1144843 : Blo 1144635 1144843 := bstep (se 1 (by rfl) ⟨858632, by rfl⟩ : syracuseStep 1144843 = 1717265) B1717265
theorem B1144855 : Blo 1144635 1144855 := bstep (se 1 (by rfl) ⟨858641, by rfl⟩ : syracuseStep 1144855 = 1717283) B1717283
theorem B1144875 : Blo 1144635 1144875 := bstep (se 1 (by rfl) ⟨858656, by rfl⟩ : syracuseStep 1144875 = 1717313) B1717313
theorem B2324531 : Blo 1144635 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B1144887 : Blo 1144635 1144887 := bstep (se 1 (by rfl) ⟨858665, by rfl⟩ : syracuseStep 1144887 = 1717331) B1717331
theorem B1144907 : Blo 1144635 1144907 := bstep (se 1 (by rfl) ⟨858680, by rfl⟩ : syracuseStep 1144907 = 1717361) B1717361
theorem B1144919 : Blo 1144635 1144919 := bstep (se 1 (by rfl) ⟨858689, by rfl⟩ : syracuseStep 1144919 = 1717379) B1717379
theorem B1144939 : Blo 1144635 1144939 := bstep (se 1 (by rfl) ⟨858704, by rfl⟩ : syracuseStep 1144939 = 1717409) B1717409
theorem B1144951 : Blo 1144635 1144951 := bstep (se 1 (by rfl) ⟨858713, by rfl⟩ : syracuseStep 1144951 = 1717427) B1717427
theorem B1144971 : Blo 1144635 1144971 := bstep (se 1 (by rfl) ⟨858728, by rfl⟩ : syracuseStep 1144971 = 1717457) B1717457
theorem B1144983 : Blo 1144635 1144983 := bstep (se 1 (by rfl) ⟨858737, by rfl⟩ : syracuseStep 1144983 = 1717475) B1717475
theorem B1145003 : Blo 1144635 1145003 := bstep (se 1 (by rfl) ⟨858752, by rfl⟩ : syracuseStep 1145003 = 1717505) B1717505
theorem B1145015 : Blo 1144635 1145015 := bstep (se 1 (by rfl) ⟨858761, by rfl⟩ : syracuseStep 1145015 = 1717523) B1717523
theorem B1145035 : Blo 1144635 1145035 := bstep (se 1 (by rfl) ⟨858776, by rfl⟩ : syracuseStep 1145035 = 1717553) B1717553
theorem B3864779 : Blo 1144635 3864779 := bstep (se 1 (by rfl) ⟨2898584, by rfl⟩ : syracuseStep 3864779 = 5797169) B5797169
theorem B1145047 : Blo 1144635 1145047 := bstep (se 1 (by rfl) ⟨858785, by rfl⟩ : syracuseStep 1145047 = 1717571) B1717571
theorem B1145067 : Blo 1144635 1145067 := bstep (se 1 (by rfl) ⟨858800, by rfl⟩ : syracuseStep 1145067 = 1717601) B1717601
theorem B1145079 : Blo 1144635 1145079 := bstep (se 1 (by rfl) ⟨858809, by rfl⟩ : syracuseStep 1145079 = 1717619) B1717619
theorem B1145099 : Blo 1144635 1145099 := bstep (se 1 (by rfl) ⟨858824, by rfl⟩ : syracuseStep 1145099 = 1717649) B1717649
theorem B1145111 : Blo 1144635 1145111 := bstep (se 1 (by rfl) ⟨858833, by rfl⟩ : syracuseStep 1145111 = 1717667) B1717667
theorem B1145131 : Blo 1144635 1145131 := bstep (se 1 (by rfl) ⟨858848, by rfl⟩ : syracuseStep 1145131 = 1717697) B1717697
theorem B1145143 : Blo 1144635 1145143 := bstep (se 1 (by rfl) ⟨858857, by rfl⟩ : syracuseStep 1145143 = 1717715) B1717715
theorem B1145163 : Blo 1144635 1145163 := bstep (se 1 (by rfl) ⟨858872, by rfl⟩ : syracuseStep 1145163 = 1717745) B1717745
theorem B1145175 : Blo 1144635 1145175 := bstep (se 1 (by rfl) ⟨858881, by rfl⟩ : syracuseStep 1145175 = 1717763) B1717763
theorem B1145195 : Blo 1144635 1145195 := bstep (se 1 (by rfl) ⟨858896, by rfl⟩ : syracuseStep 1145195 = 1717793) B1717793
theorem B1145207 : Blo 1144635 1145207 := bstep (se 1 (by rfl) ⟨858905, by rfl⟩ : syracuseStep 1145207 = 1717811) B1717811
theorem B1145227 : Blo 1144635 1145227 := bstep (se 1 (by rfl) ⟨858920, by rfl⟩ : syracuseStep 1145227 = 1717841) B1717841
theorem B1145239 : Blo 1144635 1145239 := bstep (se 1 (by rfl) ⟨858929, by rfl⟩ : syracuseStep 1145239 = 1717859) B1717859
theorem B1145259 : Blo 1144635 1145259 := bstep (se 1 (by rfl) ⟨858944, by rfl⟩ : syracuseStep 1145259 = 1717889) B1717889
theorem B1145271 : Blo 1144635 1145271 := bstep (se 1 (by rfl) ⟨858953, by rfl⟩ : syracuseStep 1145271 = 1717907) B1717907
theorem B1145291 : Blo 1144635 1145291 := bstep (se 1 (by rfl) ⟨858968, by rfl⟩ : syracuseStep 1145291 = 1717937) B1717937
theorem B1931735 : Blo 1144635 1931735 := bstep (se 1 (by rfl) ⟨1448801, by rfl⟩ : syracuseStep 1931735 = 2897603) B2897603
theorem B1145303 : Blo 1144635 1145303 := bstep (se 1 (by rfl) ⟨858977, by rfl⟩ : syracuseStep 1145303 = 1717955) B1717955
theorem B3865049 : Blo 1144635 3865049 := bstep (se 2 (by rfl) ⟨1449393, by rfl⟩ : syracuseStep 3865049 = 2898787) B2898787
theorem B1145323 : Blo 1144635 1145323 := bstep (se 1 (by rfl) ⟨858992, by rfl⟩ : syracuseStep 1145323 = 1717985) B1717985
theorem B1145335 : Blo 1144635 1145335 := bstep (se 1 (by rfl) ⟨859001, by rfl⟩ : syracuseStep 1145335 = 1718003) B1718003
theorem B4356611 : Blo 1144635 4356611 := bstep (se 1 (by rfl) ⟨3267458, by rfl⟩ : syracuseStep 4356611 = 6534917) B6534917
theorem B1145355 : Blo 1144635 1145355 := bstep (se 1 (by rfl) ⟨859016, by rfl⟩ : syracuseStep 1145355 = 1718033) B1718033
theorem B4356625 : Blo 1144635 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B1145367 : Blo 1144635 1145367 := bstep (se 1 (by rfl) ⟨859025, by rfl⟩ : syracuseStep 1145367 = 1718051) B1718051
theorem B1145387 : Blo 1144635 1145387 := bstep (se 1 (by rfl) ⟨859040, by rfl⟩ : syracuseStep 1145387 = 1718081) B1718081
theorem B1145399 : Blo 1144635 1145399 := bstep (se 1 (by rfl) ⟨859049, by rfl⟩ : syracuseStep 1145399 = 1718099) B1718099
theorem B5798465 : Blo 1144635 5798465 := bstep (se 2 (by rfl) ⟨2174424, by rfl⟩ : syracuseStep 5798465 = 4348849) B4348849
theorem B1145419 : Blo 1144635 1145419 := bstep (se 1 (by rfl) ⟨859064, by rfl⟩ : syracuseStep 1145419 = 1718129) B1718129
theorem B1931863 : Blo 1144635 1931863 := bstep (se 1 (by rfl) ⟨1448897, by rfl⟩ : syracuseStep 1931863 = 2897795) B2897795
theorem B1145431 : Blo 1144635 1145431 := bstep (se 1 (by rfl) ⟨859073, by rfl⟩ : syracuseStep 1145431 = 1718147) B1718147
theorem B1145451 : Blo 1144635 1145451 := bstep (se 1 (by rfl) ⟨859088, by rfl⟩ : syracuseStep 1145451 = 1718177) B1718177
theorem B1145463 : Blo 1144635 1145463 := bstep (se 1 (by rfl) ⟨859097, by rfl⟩ : syracuseStep 1145463 = 1718195) B1718195
theorem B1309303 : Blo 1144635 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B12384899 : Blo 1144635 12384899 := bstep (se 1 (by rfl) ⟨9288674, by rfl⟩ : syracuseStep 12384899 = 18577349) B18577349
theorem B1145483 : Blo 1144635 1145483 := bstep (se 1 (by rfl) ⟨859112, by rfl⟩ : syracuseStep 1145483 = 1718225) B1718225
theorem B1145495 : Blo 1144635 1145495 := bstep (se 1 (by rfl) ⟨859121, by rfl⟩ : syracuseStep 1145495 = 1718243) B1718243
theorem B1145515 : Blo 1144635 1145515 := bstep (se 1 (by rfl) ⟨859136, by rfl⟩ : syracuseStep 1145515 = 1718273) B1718273
theorem B1145527 : Blo 1144635 1145527 := bstep (se 1 (by rfl) ⟨859145, by rfl⟩ : syracuseStep 1145527 = 1718291) B1718291
theorem B4127435 : Blo 1144635 4127435 := bstep (se 1 (by rfl) ⟨3095576, by rfl⟩ : syracuseStep 4127435 = 6191153) B6191153
theorem B1145547 : Blo 1144635 1145547 := bstep (se 1 (by rfl) ⟨859160, by rfl⟩ : syracuseStep 1145547 = 1718321) B1718321
theorem B1309387 : Blo 1144635 1309387 := bstep (se 1 (by rfl) ⟨982040, by rfl⟩ : syracuseStep 1309387 = 1964081) B1964081
theorem B1145559 : Blo 1144635 1145559 := bstep (se 1 (by rfl) ⟨859169, by rfl⟩ : syracuseStep 1145559 = 1718339) B1718339
theorem B1145579 : Blo 1144635 1145579 := bstep (se 1 (by rfl) ⟨859184, by rfl⟩ : syracuseStep 1145579 = 1718369) B1718369
theorem B1145591 : Blo 1144635 1145591 := bstep (se 1 (by rfl) ⟨859193, by rfl⟩ : syracuseStep 1145591 = 1718387) B1718387
theorem B1145611 : Blo 1144635 1145611 := bstep (se 1 (by rfl) ⟨859208, by rfl⟩ : syracuseStep 1145611 = 1718417) B1718417
theorem B1145623 : Blo 1144635 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B1145643 : Blo 1144635 1145643 := bstep (se 1 (by rfl) ⟨859232, by rfl⟩ : syracuseStep 1145643 = 1718465) B1718465
theorem B1145655 : Blo 1144635 1145655 := bstep (se 1 (by rfl) ⟨859241, by rfl⟩ : syracuseStep 1145655 = 1718483) B1718483
theorem B4356929 : Blo 1144635 4356929 := bstep (se 2 (by rfl) ⟨1633848, by rfl⟩ : syracuseStep 4356929 = 3267697) B3267697
theorem B1145675 : Blo 1144635 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B1145687 : Blo 1144635 1145687 := bstep (se 1 (by rfl) ⟨859265, by rfl⟩ : syracuseStep 1145687 = 1718531) B1718531
theorem B1145707 : Blo 1144635 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B1145719 : Blo 1144635 1145719 := bstep (se 1 (by rfl) ⟨859289, by rfl⟩ : syracuseStep 1145719 = 1718579) B1718579
theorem B1145739 : Blo 1144635 1145739 := bstep (se 1 (by rfl) ⟨859304, by rfl⟩ : syracuseStep 1145739 = 1718609) B1718609
theorem B2751383 : Blo 1144635 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B1145751 : Blo 1144635 1145751 := bstep (se 1 (by rfl) ⟨859313, by rfl⟩ : syracuseStep 1145751 = 1718627) B1718627
theorem B1145771 : Blo 1144635 1145771 := bstep (se 1 (by rfl) ⟨859328, by rfl⟩ : syracuseStep 1145771 = 1718657) B1718657
theorem B1145783 : Blo 1144635 1145783 := bstep (se 1 (by rfl) ⟨859337, by rfl⟩ : syracuseStep 1145783 = 1718675) B1718675
theorem B1145803 : Blo 1144635 1145803 := bstep (se 1 (by rfl) ⟨859352, by rfl⟩ : syracuseStep 1145803 = 1718705) B1718705
theorem B1145815 : Blo 1144635 1145815 := bstep (se 1 (by rfl) ⟨859361, by rfl⟩ : syracuseStep 1145815 = 1718723) B1718723
theorem B1145835 : Blo 1144635 1145835 := bstep (se 1 (by rfl) ⟨859376, by rfl⟩ : syracuseStep 1145835 = 1718753) B1718753
theorem B1145847 : Blo 1144635 1145847 := bstep (se 1 (by rfl) ⟨859385, by rfl⟩ : syracuseStep 1145847 = 1718771) B1718771
theorem B1145867 : Blo 1144635 1145867 := bstep (se 1 (by rfl) ⟨859400, by rfl⟩ : syracuseStep 1145867 = 1718801) B1718801
theorem B1145879 : Blo 1144635 1145879 := bstep (se 1 (by rfl) ⟨859409, by rfl⟩ : syracuseStep 1145879 = 1718819) B1718819
theorem B1145899 : Blo 1144635 1145899 := bstep (se 1 (by rfl) ⟨859424, by rfl⟩ : syracuseStep 1145899 = 1718849) B1718849
theorem B1145911 : Blo 1144635 1145911 := bstep (se 1 (by rfl) ⟨859433, by rfl⟩ : syracuseStep 1145911 = 1718867) B1718867
theorem B1145931 : Blo 1144635 1145931 := bstep (se 1 (by rfl) ⟨859448, by rfl⟩ : syracuseStep 1145931 = 1718897) B1718897
theorem B6290507 : Blo 1144635 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B1145943 : Blo 1144635 1145943 := bstep (se 1 (by rfl) ⟨859457, by rfl⟩ : syracuseStep 1145943 = 1718915) B1718915
theorem B6290525 : Blo 1144635 6290525 := bstep (se 3 (by rfl) ⟨1179473, by rfl⟩ : syracuseStep 6290525 = 2358947) B2358947
theorem B1145963 : Blo 1144635 1145963 := bstep (se 1 (by rfl) ⟨859472, by rfl⟩ : syracuseStep 1145963 = 1718945) B1718945
theorem B1145975 : Blo 1144635 1145975 := bstep (se 1 (by rfl) ⟨859481, by rfl⟩ : syracuseStep 1145975 = 1718963) B1718963
theorem B1145995 : Blo 1144635 1145995 := bstep (se 1 (by rfl) ⟨859496, by rfl⟩ : syracuseStep 1145995 = 1718993) B1718993
theorem B3865751 : Blo 1144635 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B1146007 : Blo 1144635 1146007 := bstep (se 1 (by rfl) ⟨859505, by rfl⟩ : syracuseStep 1146007 = 1719011) B1719011
theorem B1146027 : Blo 1144635 1146027 := bstep (se 1 (by rfl) ⟨859520, by rfl⟩ : syracuseStep 1146027 = 1719041) B1719041
theorem B20118709 : Blo 1144635 20118709 := bstep (se 5 (by rfl) ⟨943064, by rfl⟩ : syracuseStep 20118709 = 1886129) B1886129
theorem B1146039 : Blo 1144635 1146039 := bstep (se 1 (by rfl) ⟨859529, by rfl⟩ : syracuseStep 1146039 = 1719059) B1719059
theorem B1932491 : Blo 1144635 1932491 := bstep (se 1 (by rfl) ⟨1449368, by rfl⟩ : syracuseStep 1932491 = 2898737) B2898737
theorem B2751691 : Blo 1144635 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B1146059 : Blo 1144635 1146059 := bstep (se 1 (by rfl) ⟨859544, by rfl⟩ : syracuseStep 1146059 = 1719089) B1719089
theorem B1146071 : Blo 1144635 1146071 := bstep (se 1 (by rfl) ⟨859553, by rfl⟩ : syracuseStep 1146071 = 1719107) B1719107
theorem B2325721 : Blo 1144635 2325721 := bstep (se 2 (by rfl) ⟨872145, by rfl⟩ : syracuseStep 2325721 = 1744291) B1744291
theorem B1146091 : Blo 1144635 1146091 := bstep (se 1 (by rfl) ⟨859568, by rfl⟩ : syracuseStep 1146091 = 1719137) B1719137
theorem B1146103 : Blo 1144635 1146103 := bstep (se 1 (by rfl) ⟨859577, by rfl⟩ : syracuseStep 1146103 = 1719155) B1719155
theorem B1146123 : Blo 1144635 1146123 := bstep (se 1 (by rfl) ⟨859592, by rfl⟩ : syracuseStep 1146123 = 1719185) B1719185
theorem B1146135 : Blo 1144635 1146135 := bstep (se 1 (by rfl) ⟨859601, by rfl⟩ : syracuseStep 1146135 = 1719203) B1719203
theorem B1146155 : Blo 1144635 1146155 := bstep (se 1 (by rfl) ⟨859616, by rfl⟩ : syracuseStep 1146155 = 1719233) B1719233
theorem B1146167 : Blo 1144635 1146167 := bstep (se 1 (by rfl) ⟨859625, by rfl⟩ : syracuseStep 1146167 = 1719251) B1719251
theorem B1932619 : Blo 1144635 1932619 := bstep (se 1 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 1932619 = 2898929) B2898929
theorem B1146187 : Blo 1144635 1146187 := bstep (se 1 (by rfl) ⟨859640, by rfl⟩ : syracuseStep 1146187 = 1719281) B1719281
theorem B1146199 : Blo 1144635 1146199 := bstep (se 1 (by rfl) ⟨859649, by rfl⟩ : syracuseStep 1146199 = 1719299) B1719299
theorem B1146219 : Blo 1144635 1146219 := bstep (se 1 (by rfl) ⟨859664, by rfl⟩ : syracuseStep 1146219 = 1719329) B1719329
theorem B1146231 : Blo 1144635 1146231 := bstep (se 1 (by rfl) ⟨859673, by rfl⟩ : syracuseStep 1146231 = 1719347) B1719347
theorem B1146251 : Blo 1144635 1146251 := bstep (se 1 (by rfl) ⟨859688, by rfl⟩ : syracuseStep 1146251 = 1719377) B1719377
theorem B1146263 : Blo 1144635 1146263 := bstep (se 1 (by rfl) ⟨859697, by rfl⟩ : syracuseStep 1146263 = 1719395) B1719395
theorem B1146283 : Blo 1144635 1146283 := bstep (se 1 (by rfl) ⟨859712, by rfl⟩ : syracuseStep 1146283 = 1719425) B1719425
theorem B1146295 : Blo 1144635 1146295 := bstep (se 1 (by rfl) ⟨859721, by rfl⟩ : syracuseStep 1146295 = 1719443) B1719443
theorem B1146315 : Blo 1144635 1146315 := bstep (se 1 (by rfl) ⟨859736, by rfl⟩ : syracuseStep 1146315 = 1719473) B1719473
theorem B1146327 : Blo 1144635 1146327 := bstep (se 1 (by rfl) ⟨859745, by rfl⟩ : syracuseStep 1146327 = 1719491) B1719491
theorem B1932761 : Blo 1144635 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B7339481 : Blo 1144635 7339481 := bstep (se 2 (by rfl) ⟨2752305, by rfl⟩ : syracuseStep 7339481 = 5504611) B5504611
theorem B4357597 : Blo 1144635 4357597 := bstep (se 3 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 4357597 = 1634099) B1634099
theorem B1146347 : Blo 1144635 1146347 := bstep (se 1 (by rfl) ⟨859760, by rfl⟩ : syracuseStep 1146347 = 1719521) B1719521
theorem B1146359 : Blo 1144635 1146359 := bstep (se 1 (by rfl) ⟨859769, by rfl⟩ : syracuseStep 1146359 = 1719539) B1719539
theorem B1146379 : Blo 1144635 1146379 := bstep (se 1 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 1146379 = 1719569) B1719569
theorem B6520337 : Blo 1144635 6520337 := bstep (se 2 (by rfl) ⟨2445126, by rfl⟩ : syracuseStep 6520337 = 4890253) B4890253
theorem B1146391 : Blo 1144635 1146391 := bstep (se 1 (by rfl) ⟨859793, by rfl⟩ : syracuseStep 1146391 = 1719587) B1719587
theorem B1146411 : Blo 1144635 1146411 := bstep (se 1 (by rfl) ⟨859808, by rfl⟩ : syracuseStep 1146411 = 1719617) B1719617
theorem B1146423 : Blo 1144635 1146423 := bstep (se 1 (by rfl) ⟨859817, by rfl⟩ : syracuseStep 1146423 = 1719635) B1719635
theorem B1146443 : Blo 1144635 1146443 := bstep (se 1 (by rfl) ⟨859832, by rfl⟩ : syracuseStep 1146443 = 1719665) B1719665
theorem B1146455 : Blo 1144635 1146455 := bstep (se 1 (by rfl) ⟨859841, by rfl⟩ : syracuseStep 1146455 = 1719683) B1719683
theorem B1932889 : Blo 1144635 1932889 := bstep (se 2 (by rfl) ⟨724833, by rfl⟩ : syracuseStep 1932889 = 1449667) B1449667
theorem B9797213 : Blo 1144635 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B1146475 : Blo 1144635 1146475 := bstep (se 1 (by rfl) ⟨859856, by rfl⟩ : syracuseStep 1146475 = 1719713) B1719713
theorem B1146487 : Blo 1144635 1146487 := bstep (se 1 (by rfl) ⟨859865, by rfl⟩ : syracuseStep 1146487 = 1719731) B1719731
theorem B1146507 : Blo 1144635 1146507 := bstep (se 1 (by rfl) ⟨859880, by rfl⟩ : syracuseStep 1146507 = 1719761) B1719761
theorem B1146519 : Blo 1144635 1146519 := bstep (se 1 (by rfl) ⟨859889, by rfl⟩ : syracuseStep 1146519 = 1719779) B1719779
theorem B1146539 : Blo 1144635 1146539 := bstep (se 1 (by rfl) ⟨859904, by rfl⟩ : syracuseStep 1146539 = 1719809) B1719809
theorem B3866291 : Blo 1144635 3866291 := bstep (se 1 (by rfl) ⟨2899718, by rfl⟩ : syracuseStep 3866291 = 5799437) B5799437
theorem B1146551 : Blo 1144635 1146551 := bstep (se 1 (by rfl) ⟨859913, by rfl⟩ : syracuseStep 1146551 = 1719827) B1719827
theorem B1146571 : Blo 1144635 1146571 := bstep (se 1 (by rfl) ⟨859928, by rfl⟩ : syracuseStep 1146571 = 1719857) B1719857
theorem B1146583 : Blo 1144635 1146583 := bstep (se 1 (by rfl) ⟨859937, by rfl⟩ : syracuseStep 1146583 = 1719875) B1719875
theorem B1146603 : Blo 1144635 1146603 := bstep (se 1 (by rfl) ⟨859952, by rfl⟩ : syracuseStep 1146603 = 1719905) B1719905
theorem B1146615 : Blo 1144635 1146615 := bstep (se 1 (by rfl) ⟨859961, by rfl⟩ : syracuseStep 1146615 = 1719923) B1719923
theorem B1146635 : Blo 1144635 1146635 := bstep (se 1 (by rfl) ⟨859976, by rfl⟩ : syracuseStep 1146635 = 1719953) B1719953
theorem B1376023 : Blo 1144635 1376023 := bstep (se 1 (by rfl) ⟨1032017, by rfl⟩ : syracuseStep 1376023 = 2064035) B2064035
theorem B1146647 : Blo 1144635 1146647 := bstep (se 1 (by rfl) ⟨859985, by rfl⟩ : syracuseStep 1146647 = 1719971) B1719971
theorem B1146667 : Blo 1144635 1146667 := bstep (se 1 (by rfl) ⟨860000, by rfl⟩ : syracuseStep 1146667 = 1720001) B1720001
theorem B1146679 : Blo 1144635 1146679 := bstep (se 1 (by rfl) ⟨860009, by rfl⟩ : syracuseStep 1146679 = 1720019) B1720019
theorem B4128587 : Blo 1144635 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B1146699 : Blo 1144635 1146699 := bstep (se 1 (by rfl) ⟨860024, by rfl⟩ : syracuseStep 1146699 = 1720049) B1720049
theorem B1146711 : Blo 1144635 1146711 := bstep (se 1 (by rfl) ⟨860033, by rfl⟩ : syracuseStep 1146711 = 1720067) B1720067
theorem B5504861 : Blo 1144635 5504861 := bstep (se 3 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 5504861 = 2064323) B2064323
theorem B1146731 : Blo 1144635 1146731 := bstep (se 1 (by rfl) ⟨860048, by rfl⟩ : syracuseStep 1146731 = 1720097) B1720097
theorem B1146743 : Blo 1144635 1146743 := bstep (se 1 (by rfl) ⟨860057, by rfl⟩ : syracuseStep 1146743 = 1720115) B1720115
theorem B1146763 : Blo 1144635 1146763 := bstep (se 1 (by rfl) ⟨860072, by rfl⟩ : syracuseStep 1146763 = 1720145) B1720145
theorem B1146775 : Blo 1144635 1146775 := bstep (se 1 (by rfl) ⟨860081, by rfl⟩ : syracuseStep 1146775 = 1720163) B1720163
theorem B1146795 : Blo 1144635 1146795 := bstep (se 1 (by rfl) ⟨860096, by rfl⟩ : syracuseStep 1146795 = 1720193) B1720193
theorem B1146807 : Blo 1144635 1146807 := bstep (se 1 (by rfl) ⟨860105, by rfl⟩ : syracuseStep 1146807 = 1720211) B1720211
theorem B3866561 : Blo 1144635 3866561 := bstep (se 2 (by rfl) ⟨1449960, by rfl⟩ : syracuseStep 3866561 = 2899921) B2899921
theorem B1146827 : Blo 1144635 1146827 := bstep (se 1 (by rfl) ⟨860120, by rfl⟩ : syracuseStep 1146827 = 1720241) B1720241
theorem B1146839 : Blo 1144635 1146839 := bstep (se 1 (by rfl) ⟨860129, by rfl⟩ : syracuseStep 1146839 = 1720259) B1720259
theorem B1146859 : Blo 1144635 1146859 := bstep (se 1 (by rfl) ⟨860144, by rfl⟩ : syracuseStep 1146859 = 1720289) B1720289
theorem B1146871 : Blo 1144635 1146871 := bstep (se 1 (by rfl) ⟨860153, by rfl⟩ : syracuseStep 1146871 = 1720307) B1720307
theorem B1146887 : Blo 1144635 1146887 := bstep (se 1 (by rfl) ⟨860165, by rfl⟩ : syracuseStep 1146887 = 1720331) B1720331
theorem B1146895 : Blo 1144635 1146895 := bstep (se 1 (by rfl) ⟨860171, by rfl⟩ : syracuseStep 1146895 = 1720343) B1720343
theorem B1933355 : Blo 1144635 1933355 := bstep (se 1 (by rfl) ⟨1450016, by rfl⟩ : syracuseStep 1933355 = 2900033) B2900033
theorem B1146939 : Blo 1144635 1146939 := bstep (se 1 (by rfl) ⟨860204, by rfl⟩ : syracuseStep 1146939 = 1720409) B1720409
theorem B1147015 : Blo 1144635 1147015 := bstep (se 1 (by rfl) ⟨860261, by rfl⟩ : syracuseStep 1147015 = 1720523) B1720523
theorem B1147023 : Blo 1144635 1147023 := bstep (se 1 (by rfl) ⟨860267, by rfl⟩ : syracuseStep 1147023 = 1720535) B1720535
theorem B14680237 : Blo 1144635 14680237 := bstep (se 3 (by rfl) ⟨2752544, by rfl⟩ : syracuseStep 14680237 = 5505089) B5505089
theorem B1147067 : Blo 1144635 1147067 := bstep (se 1 (by rfl) ⟨860300, by rfl⟩ : syracuseStep 1147067 = 1720601) B1720601
theorem B1376503 : Blo 1144635 1376503 := bstep (se 1 (by rfl) ⟨1032377, by rfl⟩ : syracuseStep 1376503 = 2064755) B2064755
theorem B1147143 : Blo 1144635 1147143 := bstep (se 1 (by rfl) ⟨860357, by rfl⟩ : syracuseStep 1147143 = 1720715) B1720715
theorem B1147151 : Blo 1144635 1147151 := bstep (se 1 (by rfl) ⟨860363, by rfl⟩ : syracuseStep 1147151 = 1720727) B1720727
theorem B3866939 : Blo 1144635 3866939 := bstep (se 1 (by rfl) ⟨2900204, by rfl⟩ : syracuseStep 3866939 = 5800409) B5800409
theorem B1147195 : Blo 1144635 1147195 := bstep (se 1 (by rfl) ⟨860396, by rfl⟩ : syracuseStep 1147195 = 1720793) B1720793
theorem B1147271 : Blo 1144635 1147271 := bstep (se 1 (by rfl) ⟨860453, by rfl⟩ : syracuseStep 1147271 = 1720907) B1720907
theorem B1147279 : Blo 1144635 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B11010451 : Blo 1144635 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B1933753 : Blo 1144635 1933753 := bstep (se 2 (by rfl) ⟨725157, by rfl⟩ : syracuseStep 1933753 = 1450315) B1450315
theorem B1147323 : Blo 1144635 1147323 := bstep (se 1 (by rfl) ⟨860492, by rfl⟩ : syracuseStep 1147323 = 1720985) B1720985
theorem B1147399 : Blo 1144635 1147399 := bstep (se 1 (by rfl) ⟨860549, by rfl⟩ : syracuseStep 1147399 = 1721099) B1721099
theorem B1147407 : Blo 1144635 1147407 := bstep (se 1 (by rfl) ⟨860555, by rfl⟩ : syracuseStep 1147407 = 1721111) B1721111
theorem B1147451 : Blo 1144635 1147451 := bstep (se 1 (by rfl) ⟨860588, by rfl⟩ : syracuseStep 1147451 = 1721177) B1721177
theorem B13926977 : Blo 1144635 13926977 := bstep (se 2 (by rfl) ⟨5222616, by rfl⟩ : syracuseStep 13926977 = 10445233) B10445233
theorem B1147527 : Blo 1144635 1147527 := bstep (se 1 (by rfl) ⟨860645, by rfl⟩ : syracuseStep 1147527 = 1721291) B1721291
theorem B1147535 : Blo 1144635 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B23560885 : Blo 1144635 23560885 := bstep (se 5 (by rfl) ⟨1104416, by rfl⟩ : syracuseStep 23560885 = 2208833) B2208833
theorem B1147579 : Blo 1144635 1147579 := bstep (se 1 (by rfl) ⟨860684, by rfl⟩ : syracuseStep 1147579 = 1721369) B1721369
theorem B1147655 : Blo 1144635 1147655 := bstep (se 1 (by rfl) ⟨860741, by rfl⟩ : syracuseStep 1147655 = 1721483) B1721483
theorem B1147663 : Blo 1144635 1147663 := bstep (se 1 (by rfl) ⟨860747, by rfl⟩ : syracuseStep 1147663 = 1721495) B1721495
theorem B3867425 : Blo 1144635 3867425 := bstep (se 2 (by rfl) ⟨1450284, by rfl⟩ : syracuseStep 3867425 = 2900569) B2900569
theorem B3146539 : Blo 1144635 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B1147707 : Blo 1144635 1147707 := bstep (se 1 (by rfl) ⟨860780, by rfl⟩ : syracuseStep 1147707 = 1721561) B1721561
theorem B1147783 : Blo 1144635 1147783 := bstep (se 1 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 1147783 = 1721675) B1721675
theorem B1147791 : Blo 1144635 1147791 := bstep (se 1 (by rfl) ⟨860843, by rfl⟩ : syracuseStep 1147791 = 1721687) B1721687
theorem B1147835 : Blo 1144635 1147835 := bstep (se 1 (by rfl) ⟨860876, by rfl⟩ : syracuseStep 1147835 = 1721753) B1721753
theorem B1147911 : Blo 1144635 1147911 := bstep (se 1 (by rfl) ⟨860933, by rfl⟩ : syracuseStep 1147911 = 1721867) B1721867
theorem B1147919 : Blo 1144635 1147919 := bstep (se 1 (by rfl) ⟨860939, by rfl⟩ : syracuseStep 1147919 = 1721879) B1721879
theorem B1147963 : Blo 1144635 1147963 := bstep (se 1 (by rfl) ⟨860972, by rfl⟩ : syracuseStep 1147963 = 1721945) B1721945
theorem B1934455 : Blo 1144635 1934455 := bstep (se 1 (by rfl) ⟨1450841, by rfl⟩ : syracuseStep 1934455 = 2901683) B2901683
theorem B4654199 : Blo 1144635 4654199 := bstep (se 1 (by rfl) ⟨3490649, by rfl⟩ : syracuseStep 4654199 = 6981299) B6981299
theorem B1148039 : Blo 1144635 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B1148047 : Blo 1144635 1148047 := bstep (se 1 (by rfl) ⟨861035, by rfl⟩ : syracuseStep 1148047 = 1722071) B1722071
theorem B1148091 : Blo 1144635 1148091 := bstep (se 1 (by rfl) ⟨861068, by rfl⟩ : syracuseStep 1148091 = 1722137) B1722137
theorem B1148167 : Blo 1144635 1148167 := bstep (se 1 (by rfl) ⟨861125, by rfl⟩ : syracuseStep 1148167 = 1722251) B1722251
theorem B1148175 : Blo 1144635 1148175 := bstep (se 1 (by rfl) ⟨861131, by rfl⟩ : syracuseStep 1148175 = 1722263) B1722263
theorem B1934651 : Blo 1144635 1934651 := bstep (se 1 (by rfl) ⟨1450988, by rfl⟩ : syracuseStep 1934651 = 2901977) B2901977
theorem B1148219 : Blo 1144635 1148219 := bstep (se 1 (by rfl) ⟨861164, by rfl⟩ : syracuseStep 1148219 = 1722329) B1722329
theorem B6522227 : Blo 1144635 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B3868019 : Blo 1144635 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B1148295 : Blo 1144635 1148295 := bstep (se 1 (by rfl) ⟨861221, by rfl⟩ : syracuseStep 1148295 = 1722443) B1722443
theorem B1148303 : Blo 1144635 1148303 := bstep (se 1 (by rfl) ⟨861227, by rfl⟩ : syracuseStep 1148303 = 1722455) B1722455
theorem B4130201 : Blo 1144635 4130201 := bstep (se 2 (by rfl) ⟨1548825, by rfl⟩ : syracuseStep 4130201 = 3097651) B3097651
theorem B1148347 : Blo 1144635 1148347 := bstep (se 1 (by rfl) ⟨861260, by rfl⟩ : syracuseStep 1148347 = 1722521) B1722521
theorem B1148423 : Blo 1144635 1148423 := bstep (se 1 (by rfl) ⟨861317, by rfl⟩ : syracuseStep 1148423 = 1722635) B1722635
theorem B1148431 : Blo 1144635 1148431 := bstep (se 1 (by rfl) ⟨861323, by rfl⟩ : syracuseStep 1148431 = 1722647) B1722647
theorem B4130347 : Blo 1144635 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B8717867 : Blo 1144635 8717867 := bstep (se 1 (by rfl) ⟨6538400, by rfl⟩ : syracuseStep 8717867 = 13076801) B13076801
theorem B1148475 : Blo 1144635 1148475 := bstep (se 1 (by rfl) ⟨861356, by rfl⟩ : syracuseStep 1148475 = 1722713) B1722713
theorem B13043267 : Blo 1144635 13043267 := bstep (se 1 (by rfl) ⟨9782450, by rfl⟩ : syracuseStep 13043267 = 19564901) B19564901
theorem B1148551 : Blo 1144635 1148551 := bstep (se 1 (by rfl) ⟨861413, by rfl⟩ : syracuseStep 1148551 = 1722827) B1722827
theorem B1148559 : Blo 1144635 1148559 := bstep (se 1 (by rfl) ⟨861419, by rfl⟩ : syracuseStep 1148559 = 1722839) B1722839
theorem B1148603 : Blo 1144635 1148603 := bstep (se 1 (by rfl) ⟨861452, by rfl⟩ : syracuseStep 1148603 = 1722905) B1722905
theorem B1935049 : Blo 1144635 1935049 := bstep (se 2 (by rfl) ⟨725643, by rfl⟩ : syracuseStep 1935049 = 1451287) B1451287
theorem B14911661 : Blo 1144635 14911661 := bstep (se 3 (by rfl) ⟨2795936, by rfl⟩ : syracuseStep 14911661 = 5591873) B5591873
theorem B1935751 : Blo 1144635 1935751 := bstep (se 1 (by rfl) ⟨1451813, by rfl⟩ : syracuseStep 1935751 = 2903627) B2903627
theorem B2689595 : Blo 1144635 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B8260289 : Blo 1144635 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B6523685 : Blo 1144635 6523685 := bstep (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) B1223191
theorem B1936399 : Blo 1144635 1936399 := bstep (se 1 (by rfl) ⟨1452299, by rfl⟩ : syracuseStep 1936399 = 2904599) B2904599
theorem B14126167 : Blo 1144635 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B9800837 : Blo 1144635 9800837 := bstep (se 4 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 9800837 = 1837657) B1837657
theorem B3673289 : Blo 1144635 3673289 := bstep (se 2 (by rfl) ⟨1377483, by rfl⟩ : syracuseStep 3673289 = 2754967) B2754967
theorem B6982949 : Blo 1144635 6982949 := bstep (se 4 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 6982949 = 1309303) B1309303
theorem B7343581 : Blo 1144635 7343581 := bstep (se 3 (by rfl) ⟨1376921, by rfl⟩ : syracuseStep 7343581 = 2753843) B2753843
theorem B6524459 : Blo 1144635 6524459 := bstep (se 1 (by rfl) ⟨4893344, by rfl⟩ : syracuseStep 6524459 = 9786689) B9786689
theorem B1936939 : Blo 1144635 1936939 := bstep (se 1 (by rfl) ⟨1452704, by rfl⟩ : syracuseStep 1936939 = 2905409) B2905409
theorem B1937081 : Blo 1144635 1937081 := bstep (se 2 (by rfl) ⟨726405, by rfl⟩ : syracuseStep 1937081 = 1452811) B1452811
theorem B2068267 : Blo 1144635 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B9801587 : Blo 1144635 9801587 := bstep (se 1 (by rfl) ⟨7351190, by rfl⟩ : syracuseStep 9801587 = 14702381) B14702381
theorem B3870611 : Blo 1144635 3870611 := bstep (se 1 (by rfl) ⟨2902958, by rfl⟩ : syracuseStep 3870611 = 5805917) B5805917
theorem B12390347 : Blo 1144635 12390347 := bstep (se 1 (by rfl) ⟨9292760, by rfl⟩ : syracuseStep 12390347 = 18585521) B18585521
theorem B9310409 : Blo 1144635 9310409 := bstep (se 2 (by rfl) ⟨3491403, by rfl⟩ : syracuseStep 9310409 = 6982807) B6982807
theorem B1937783 : Blo 1144635 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B2757235 : Blo 1144635 2757235 := bstep (se 1 (by rfl) ⟨2067926, by rfl⟩ : syracuseStep 2757235 = 4135853) B4135853
theorem B1938235 : Blo 1144635 1938235 := bstep (se 1 (by rfl) ⟨1453676, by rfl⟩ : syracuseStep 1938235 = 2907353) B2907353
theorem B5804945 : Blo 1144635 5804945 := bstep (se 2 (by rfl) ⟨2176854, by rfl⟩ : syracuseStep 5804945 = 4353709) B4353709
theorem B6525917 : Blo 1144635 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B14717963 : Blo 1144635 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B1741943 : Blo 1144635 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B4134007 : Blo 1144635 4134007 := bstep (se 1 (by rfl) ⟨3100505, by rfl⟩ : syracuseStep 4134007 = 6201011) B6201011
theorem B2069651 : Blo 1144635 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B3872015 : Blo 1144635 3872015 := bstep (se 1 (by rfl) ⟨2904011, by rfl⟩ : syracuseStep 3872015 = 5808023) B5808023
theorem B3315215 : Blo 1144635 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B3872285 : Blo 1144635 3872285 := bstep (se 3 (by rfl) ⟨726053, by rfl⟩ : syracuseStep 3872285 = 1452107) B1452107
theorem B13047641 : Blo 1144635 13047641 := bstep (se 2 (by rfl) ⟨4892865, by rfl⟩ : syracuseStep 13047641 = 9785731) B9785731
theorem B5577011 : Blo 1144635 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B3971513 : Blo 1144635 3971513 := bstep (se 2 (by rfl) ⟨1489317, by rfl⟩ : syracuseStep 3971513 = 2978635) B2978635
theorem B2759255 : Blo 1144635 2759255 := bstep (se 1 (by rfl) ⟨2069441, by rfl⟩ : syracuseStep 2759255 = 4138883) B4138883
theorem B1448695 : Blo 1144635 1448695 := bstep (se 1 (by rfl) ⟨1086521, by rfl⟩ : syracuseStep 1448695 = 2173043) B2173043
theorem B3873689 : Blo 1144635 3873689 := bstep (se 2 (by rfl) ⟨1452633, by rfl⟩ : syracuseStep 3873689 = 2905267) B2905267
theorem B5807051 : Blo 1144635 5807051 := bstep (se 1 (by rfl) ⟨4355288, by rfl⟩ : syracuseStep 5807051 = 8710577) B8710577
theorem B14883851 : Blo 1144635 14883851 := bstep (se 1 (by rfl) ⟨11162888, by rfl⟩ : syracuseStep 14883851 = 22325777) B22325777
theorem B1449019 : Blo 1144635 1449019 := bstep (se 1 (by rfl) ⟨1086764, by rfl⟩ : syracuseStep 1449019 = 2173529) B2173529
theorem B5807375 : Blo 1144635 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B1547593 : Blo 1144635 1547593 := bstep (se 2 (by rfl) ⟨580347, by rfl⟩ : syracuseStep 1547593 = 1160695) B1160695
theorem B6200711 : Blo 1144635 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B1449515 : Blo 1144635 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B3874391 : Blo 1144635 3874391 := bstep (se 1 (by rfl) ⟨2905793, by rfl⟩ : syracuseStep 3874391 = 5811587) B5811587
theorem B2793217 : Blo 1144635 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B2727713 : Blo 1144635 2727713 := bstep (se 2 (by rfl) ⟨1022892, by rfl⟩ : syracuseStep 2727713 = 2045785) B2045785
theorem B4890577 : Blo 1144635 4890577 := bstep (se 2 (by rfl) ⟨1833966, by rfl⟩ : syracuseStep 4890577 = 3667933) B3667933
theorem B1449991 : Blo 1144635 1449991 := bstep (se 1 (by rfl) ⟨1087493, by rfl⟩ : syracuseStep 1449991 = 2174987) B2174987
theorem B6529085 : Blo 1144635 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B3874877 : Blo 1144635 3874877 := bstep (se 3 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 3874877 = 1453079) B1453079
theorem B9314365 : Blo 1144635 9314365 := bstep (se 3 (by rfl) ⟨1746443, by rfl⟩ : syracuseStep 9314365 = 3492887) B3492887
theorem B1450487 : Blo 1144635 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B1450639 : Blo 1144635 1450639 := bstep (se 1 (by rfl) ⟨1087979, by rfl⟩ : syracuseStep 1450639 = 2175959) B2175959
theorem B5808833 : Blo 1144635 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B1450811 : Blo 1144635 1450811 := bstep (se 1 (by rfl) ⟨1088108, by rfl⟩ : syracuseStep 1450811 = 2176217) B2176217
theorem B8692595 : Blo 1144635 8692595 := bstep (se 1 (by rfl) ⟨6519446, by rfl⟩ : syracuseStep 8692595 = 13038893) B13038893
theorem B1745849 : Blo 1144635 1745849 := bstep (se 2 (by rfl) ⟨654693, by rfl⟩ : syracuseStep 1745849 = 1309387) B1309387
theorem B5580083 : Blo 1144635 5580083 := bstep (se 1 (by rfl) ⟨4185062, by rfl⟩ : syracuseStep 5580083 = 8370125) B8370125
theorem B1549687 : Blo 1144635 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B3876281 : Blo 1144635 3876281 := bstep (se 2 (by rfl) ⟨1453605, by rfl⟩ : syracuseStep 3876281 = 2907211) B2907211
theorem B22029893 : Blo 1144635 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B1287823 : Blo 1144635 1287823 := bstep (se 1 (by rfl) ⟨965867, by rfl⟩ : syracuseStep 1287823 = 1931735) B1931735
theorem B1451783 : Blo 1144635 1451783 := bstep (se 1 (by rfl) ⟨1088837, by rfl⟩ : syracuseStep 1451783 = 2177675) B2177675
theorem B3483425 : Blo 1144635 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B5515067 : Blo 1144635 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B6629273 : Blo 1144635 6629273 := bstep (se 2 (by rfl) ⟨2485977, by rfl⟩ : syracuseStep 6629273 = 4971955) B4971955
theorem B5810129 : Blo 1144635 5810129 := bstep (se 2 (by rfl) ⟨2178798, by rfl⟩ : syracuseStep 5810129 = 4357597) B4357597
theorem B1288327 : Blo 1144635 1288327 := bstep (se 1 (by rfl) ⟨966245, by rfl⟩ : syracuseStep 1288327 = 1932491) B1932491
theorem B12396833 : Blo 1144635 12396833 := bstep (se 2 (by rfl) ⟨4648812, by rfl⟩ : syracuseStep 12396833 = 9297625) B9297625
theorem B1288507 : Blo 1144635 1288507 := bstep (se 1 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 1288507 = 1932761) B1932761
theorem B4892987 : Blo 1144635 4892987 := bstep (se 1 (by rfl) ⟨3669740, by rfl⟩ : syracuseStep 4892987 = 7339481) B7339481
theorem B1452431 : Blo 1144635 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B2173331 : Blo 1144635 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B6531475 : Blo 1144635 6531475 := bstep (se 1 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 6531475 = 9797213) B9797213
theorem B2173385 : Blo 1144635 2173385 := bstep (se 2 (by rfl) ⟨815019, by rfl⟩ : syracuseStep 2173385 = 1630039) B1630039
theorem B12397009 : Blo 1144635 12397009 := bstep (se 2 (by rfl) ⟨4648878, by rfl⟩ : syracuseStep 12397009 = 9297757) B9297757
theorem B4139531 : Blo 1144635 4139531 := bstep (se 1 (by rfl) ⟨3104648, by rfl⟩ : syracuseStep 4139531 = 6209297) B6209297
theorem B2173483 : Blo 1144635 2173483 := bstep (se 1 (by rfl) ⟨1630112, by rfl⟩ : syracuseStep 2173483 = 3260225) B3260225
theorem B2173711 : Blo 1144635 2173711 := bstep (se 1 (by rfl) ⟨1630283, by rfl⟩ : syracuseStep 2173711 = 3260567) B3260567
theorem B1288975 : Blo 1144635 1288975 := bstep (se 1 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 1288975 = 1933463) B1933463
theorem B18590579 : Blo 1144635 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B1223695 : Blo 1144635 1223695 := bstep (se 1 (by rfl) ⟨917771, by rfl⟩ : syracuseStep 1223695 = 1835543) B1835543
theorem B1289479 : Blo 1144635 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B14691719 : Blo 1144635 14691719 := bstep (se 1 (by rfl) ⟨11018789, by rfl⟩ : syracuseStep 14691719 = 22037579) B22037579
theorem B1289659 : Blo 1144635 1289659 := bstep (se 1 (by rfl) ⟨967244, by rfl⟩ : syracuseStep 1289659 = 1934489) B1934489
theorem B12922739 : Blo 1144635 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1290127 : Blo 1144635 1290127 := bstep (se 1 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 1290127 = 1935191) B1935191
theorem B5812235 : Blo 1144635 5812235 := bstep (se 1 (by rfl) ⟨4359176, by rfl⟩ : syracuseStep 5812235 = 8718353) B8718353
theorem B6533207 : Blo 1144635 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B5812397 : Blo 1144635 5812397 := bstep (se 3 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 5812397 = 2179649) B2179649
theorem B2175275 : Blo 1144635 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B1290631 : Blo 1144635 1290631 := bstep (se 1 (by rfl) ⟨967973, by rfl⟩ : syracuseStep 1290631 = 1935947) B1935947
theorem B1290811 : Blo 1144635 1290811 := bstep (se 1 (by rfl) ⟨968108, by rfl⟩ : syracuseStep 1290811 = 1936217) B1936217
theorem B1716983 : Blo 1144635 1716983 := bstep (se 1 (by rfl) ⟨1287737, by rfl⟩ : syracuseStep 1716983 = 2575475) B2575475
theorem B7353089 : Blo 1144635 7353089 := bstep (se 2 (by rfl) ⟨2757408, by rfl⟩ : syracuseStep 7353089 = 5514817) B5514817
theorem B1717007 : Blo 1144635 1717007 := bstep (se 1 (by rfl) ⟨1287755, by rfl⟩ : syracuseStep 1717007 = 2575511) B2575511
theorem B7353139 : Blo 1144635 7353139 := bstep (se 1 (by rfl) ⟨5514854, by rfl⟩ : syracuseStep 7353139 = 11029709) B11029709
theorem B1717049 : Blo 1144635 1717049 := bstep (se 2 (by rfl) ⟨643893, by rfl⟩ : syracuseStep 1717049 = 1287787) B1287787
theorem B1717127 : Blo 1144635 1717127 := bstep (se 1 (by rfl) ⟨1287845, by rfl⟩ : syracuseStep 1717127 = 2575691) B2575691
theorem B1717163 : Blo 1144635 1717163 := bstep (se 1 (by rfl) ⟨1287872, by rfl⟩ : syracuseStep 1717163 = 2575745) B2575745
theorem B1717193 : Blo 1144635 1717193 := bstep (se 2 (by rfl) ⟨643947, by rfl⟩ : syracuseStep 1717193 = 1287895) B1287895
theorem B1291279 : Blo 1144635 1291279 := bstep (se 1 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 1291279 = 1936919) B1936919
theorem B1717307 : Blo 1144635 1717307 := bstep (se 1 (by rfl) ⟨1287980, by rfl⟩ : syracuseStep 1717307 = 2575961) B2575961
theorem B1717367 : Blo 1144635 1717367 := bstep (se 1 (by rfl) ⟨1288025, by rfl⟩ : syracuseStep 1717367 = 2576051) B2576051
theorem B1717391 : Blo 1144635 1717391 := bstep (se 1 (by rfl) ⟨1288043, by rfl⟩ : syracuseStep 1717391 = 2576087) B2576087
theorem B1717433 : Blo 1144635 1717433 := bstep (se 2 (by rfl) ⟨644037, by rfl⟩ : syracuseStep 1717433 = 1288075) B1288075
theorem B1717511 : Blo 1144635 1717511 := bstep (se 1 (by rfl) ⟨1288133, by rfl⟩ : syracuseStep 1717511 = 2576267) B2576267
theorem B1717547 : Blo 1144635 1717547 := bstep (se 1 (by rfl) ⟨1288160, by rfl⟩ : syracuseStep 1717547 = 2576321) B2576321
theorem B1717577 : Blo 1144635 1717577 := bstep (se 2 (by rfl) ⟨644091, by rfl⟩ : syracuseStep 1717577 = 1288183) B1288183
theorem B1717691 : Blo 1144635 1717691 := bstep (se 1 (by rfl) ⟨1288268, by rfl⟩ : syracuseStep 1717691 = 2576537) B2576537
theorem B1717751 : Blo 1144635 1717751 := bstep (se 1 (by rfl) ⟨1288313, by rfl⟩ : syracuseStep 1717751 = 2576627) B2576627
theorem B1291783 : Blo 1144635 1291783 := bstep (se 1 (by rfl) ⟨968837, by rfl⟩ : syracuseStep 1291783 = 1937675) B1937675
theorem B1717775 : Blo 1144635 1717775 := bstep (se 1 (by rfl) ⟨1288331, by rfl⟩ : syracuseStep 1717775 = 2576663) B2576663
theorem B26490397 : Blo 1144635 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B2897441 : Blo 1144635 2897441 := bstep (se 2 (by rfl) ⟨1086540, by rfl⟩ : syracuseStep 2897441 = 2173081) B2173081
theorem B1717817 : Blo 1144635 1717817 := bstep (se 2 (by rfl) ⟨644181, by rfl⟩ : syracuseStep 1717817 = 1288363) B1288363
theorem B1717895 : Blo 1144635 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B1717931 : Blo 1144635 1717931 := bstep (se 1 (by rfl) ⟨1288448, by rfl⟩ : syracuseStep 1717931 = 2576897) B2576897
theorem B1291963 : Blo 1144635 1291963 := bstep (se 1 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 1291963 = 1937945) B1937945
theorem B1717961 : Blo 1144635 1717961 := bstep (se 2 (by rfl) ⟨644235, by rfl⟩ : syracuseStep 1717961 = 1288471) B1288471
theorem B5814017 : Blo 1144635 5814017 := bstep (se 2 (by rfl) ⟨2180256, by rfl⟩ : syracuseStep 5814017 = 4360513) B4360513
theorem B3094301 : Blo 1144635 3094301 := bstep (se 3 (by rfl) ⟨580181, by rfl⟩ : syracuseStep 3094301 = 1160363) B1160363
theorem B1718075 : Blo 1144635 1718075 := bstep (se 1 (by rfl) ⟨1288556, by rfl⟩ : syracuseStep 1718075 = 2577113) B2577113
theorem B27932485 : Blo 1144635 27932485 := bstep (se 4 (by rfl) ⟨2618670, by rfl⟩ : syracuseStep 27932485 = 5237341) B5237341
theorem B1718135 : Blo 1144635 1718135 := bstep (se 1 (by rfl) ⟨1288601, by rfl⟩ : syracuseStep 1718135 = 2577203) B2577203
theorem B1718159 : Blo 1144635 1718159 := bstep (se 1 (by rfl) ⟨1288619, by rfl⟩ : syracuseStep 1718159 = 2577239) B2577239
theorem B1718201 : Blo 1144635 1718201 := bstep (se 2 (by rfl) ⟨644325, by rfl⟩ : syracuseStep 1718201 = 1288651) B1288651
theorem B2176969 : Blo 1144635 2176969 := bstep (se 2 (by rfl) ⟨816363, by rfl⟩ : syracuseStep 2176969 = 1632727) B1632727
theorem B1718279 : Blo 1144635 1718279 := bstep (se 1 (by rfl) ⟨1288709, by rfl⟩ : syracuseStep 1718279 = 2577419) B2577419
theorem B1718315 : Blo 1144635 1718315 := bstep (se 1 (by rfl) ⟨1288736, by rfl⟩ : syracuseStep 1718315 = 2577473) B2577473
theorem B3487805 : Blo 1144635 3487805 := bstep (se 3 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 3487805 = 1307927) B1307927
theorem B1718345 : Blo 1144635 1718345 := bstep (se 2 (by rfl) ⟨644379, by rfl⟩ : syracuseStep 1718345 = 1288759) B1288759
theorem B1718459 : Blo 1144635 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B1718519 : Blo 1144635 1718519 := bstep (se 1 (by rfl) ⟨1288889, by rfl⟩ : syracuseStep 1718519 = 2577779) B2577779
theorem B1718543 : Blo 1144635 1718543 := bstep (se 1 (by rfl) ⟨1288907, by rfl⟩ : syracuseStep 1718543 = 2577815) B2577815
theorem B1161487 : Blo 1144635 1161487 := bstep (se 1 (by rfl) ⟨871115, by rfl⟩ : syracuseStep 1161487 = 1742231) B1742231
theorem B1718585 : Blo 1144635 1718585 := bstep (se 2 (by rfl) ⟨644469, by rfl⟩ : syracuseStep 1718585 = 1288939) B1288939
theorem B1718663 : Blo 1144635 1718663 := bstep (se 1 (by rfl) ⟨1288997, by rfl⟩ : syracuseStep 1718663 = 2577995) B2577995
theorem B6371731 : Blo 1144635 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B1718699 : Blo 1144635 1718699 := bstep (se 1 (by rfl) ⟨1289024, by rfl⟩ : syracuseStep 1718699 = 2578049) B2578049
theorem B1718729 : Blo 1144635 1718729 := bstep (se 2 (by rfl) ⟨644523, by rfl⟩ : syracuseStep 1718729 = 1289047) B1289047
theorem B2898443 : Blo 1144635 2898443 := bstep (se 1 (by rfl) ⟨2173832, by rfl⟩ : syracuseStep 2898443 = 4347665) B4347665
theorem B5814827 : Blo 1144635 5814827 := bstep (se 1 (by rfl) ⟨4361120, by rfl⟩ : syracuseStep 5814827 = 8722241) B8722241
theorem B1718843 : Blo 1144635 1718843 := bstep (se 1 (by rfl) ⟨1289132, by rfl⟩ : syracuseStep 1718843 = 2578265) B2578265
theorem B3095101 : Blo 1144635 3095101 := bstep (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) B1160663
theorem B1718903 : Blo 1144635 1718903 := bstep (se 1 (by rfl) ⟨1289177, by rfl⟩ : syracuseStep 1718903 = 2578355) B2578355
theorem B1718927 : Blo 1144635 1718927 := bstep (se 1 (by rfl) ⟨1289195, by rfl⟩ : syracuseStep 1718927 = 2578391) B2578391
theorem B1718969 : Blo 1144635 1718969 := bstep (se 2 (by rfl) ⟨644613, by rfl⟩ : syracuseStep 1718969 = 1289227) B1289227
theorem B1719047 : Blo 1144635 1719047 := bstep (se 1 (by rfl) ⟨1289285, by rfl⟩ : syracuseStep 1719047 = 2578571) B2578571
theorem B1719083 : Blo 1144635 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B1653577 : Blo 1144635 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B1719113 : Blo 1144635 1719113 := bstep (se 2 (by rfl) ⟨644667, by rfl⟩ : syracuseStep 1719113 = 1289335) B1289335
theorem B1719227 : Blo 1144635 1719227 := bstep (se 1 (by rfl) ⟨1289420, by rfl⟩ : syracuseStep 1719227 = 2578841) B2578841
theorem B1162171 : Blo 1144635 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B1719287 : Blo 1144635 1719287 := bstep (se 1 (by rfl) ⟨1289465, by rfl⟩ : syracuseStep 1719287 = 2578931) B2578931
theorem B1719311 : Blo 1144635 1719311 := bstep (se 1 (by rfl) ⟨1289483, by rfl⟩ : syracuseStep 1719311 = 2578967) B2578967
theorem B1719353 : Blo 1144635 1719353 := bstep (se 2 (by rfl) ⟨644757, by rfl⟩ : syracuseStep 1719353 = 1289515) B1289515
theorem B1719431 : Blo 1144635 1719431 := bstep (se 1 (by rfl) ⟨1289573, by rfl⟩ : syracuseStep 1719431 = 2579147) B2579147
theorem B2899091 : Blo 1144635 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B1719467 : Blo 1144635 1719467 := bstep (se 1 (by rfl) ⟨1289600, by rfl⟩ : syracuseStep 1719467 = 2579201) B2579201
theorem B1719497 : Blo 1144635 1719497 := bstep (se 2 (by rfl) ⟨644811, by rfl⟩ : syracuseStep 1719497 = 1289623) B1289623
theorem B4963643 : Blo 1144635 4963643 := bstep (se 1 (by rfl) ⟨3722732, by rfl⟩ : syracuseStep 4963643 = 7445465) B7445465
theorem B1719611 : Blo 1144635 1719611 := bstep (se 1 (by rfl) ⟨1289708, by rfl⟩ : syracuseStep 1719611 = 2579417) B2579417
theorem B3489139 : Blo 1144635 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B1719671 : Blo 1144635 1719671 := bstep (se 1 (by rfl) ⟨1289753, by rfl⟩ : syracuseStep 1719671 = 2579507) B2579507
theorem B1719695 : Blo 1144635 1719695 := bstep (se 1 (by rfl) ⟨1289771, by rfl⟩ : syracuseStep 1719695 = 2579543) B2579543
theorem B2899385 : Blo 1144635 2899385 := bstep (se 2 (by rfl) ⟨1087269, by rfl⟩ : syracuseStep 2899385 = 2174539) B2174539
theorem B1719737 : Blo 1144635 1719737 := bstep (se 2 (by rfl) ⟨644901, by rfl⟩ : syracuseStep 1719737 = 1289803) B1289803
theorem B1719815 : Blo 1144635 1719815 := bstep (se 1 (by rfl) ⟨1289861, by rfl⟩ : syracuseStep 1719815 = 2579723) B2579723
theorem B5881355 : Blo 1144635 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B4898333 : Blo 1144635 4898333 := bstep (se 3 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 4898333 = 1836875) B1836875
theorem B1719851 : Blo 1144635 1719851 := bstep (se 1 (by rfl) ⟨1289888, by rfl⟩ : syracuseStep 1719851 = 2579777) B2579777
theorem B1719881 : Blo 1144635 1719881 := bstep (se 2 (by rfl) ⟨644955, by rfl⟩ : syracuseStep 1719881 = 1289911) B1289911
theorem B1719995 : Blo 1144635 1719995 := bstep (se 1 (by rfl) ⟨1289996, by rfl⟩ : syracuseStep 1719995 = 2579993) B2579993
theorem B1720055 : Blo 1144635 1720055 := bstep (se 1 (by rfl) ⟨1290041, by rfl⟩ : syracuseStep 1720055 = 2580083) B2580083
theorem B1720079 : Blo 1144635 1720079 := bstep (se 1 (by rfl) ⟨1290059, by rfl⟩ : syracuseStep 1720079 = 2580119) B2580119
theorem B1720121 : Blo 1144635 1720121 := bstep (se 2 (by rfl) ⟨645045, by rfl⟩ : syracuseStep 1720121 = 1290091) B1290091
theorem B2178875 : Blo 1144635 2178875 := bstep (se 1 (by rfl) ⟨1634156, by rfl⟩ : syracuseStep 2178875 = 3268313) B3268313
theorem B1720199 : Blo 1144635 1720199 := bstep (se 1 (by rfl) ⟨1290149, by rfl⟩ : syracuseStep 1720199 = 2580299) B2580299
theorem B1720235 : Blo 1144635 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B1720265 : Blo 1144635 1720265 := bstep (se 2 (by rfl) ⟨645099, by rfl⟩ : syracuseStep 1720265 = 1290199) B1290199
theorem B3096605 : Blo 1144635 3096605 := bstep (se 3 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 3096605 = 1161227) B1161227
theorem B1720379 : Blo 1144635 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B2900083 : Blo 1144635 2900083 := bstep (se 1 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 2900083 = 4350125) B4350125
theorem B1720439 : Blo 1144635 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B1720463 : Blo 1144635 1720463 := bstep (se 1 (by rfl) ⟨1290347, by rfl⟩ : syracuseStep 1720463 = 2580695) B2580695
theorem B1720505 : Blo 1144635 1720505 := bstep (se 2 (by rfl) ⟨645189, by rfl⟩ : syracuseStep 1720505 = 1290379) B1290379
theorem B4899017 : Blo 1144635 4899017 := bstep (se 2 (by rfl) ⟨1837131, by rfl⟩ : syracuseStep 4899017 = 3674263) B3674263
theorem B2900225 : Blo 1144635 2900225 := bstep (se 2 (by rfl) ⟨1087584, by rfl⟩ : syracuseStep 2900225 = 2175169) B2175169
theorem B4964609 : Blo 1144635 4964609 := bstep (se 2 (by rfl) ⟨1861728, by rfl⟩ : syracuseStep 4964609 = 3723457) B3723457
theorem B1720583 : Blo 1144635 1720583 := bstep (se 1 (by rfl) ⟨1290437, by rfl⟩ : syracuseStep 1720583 = 2580875) B2580875
theorem B2179361 : Blo 1144635 2179361 := bstep (se 2 (by rfl) ⟨817260, by rfl⟩ : syracuseStep 2179361 = 1634521) B1634521
theorem B1720619 : Blo 1144635 1720619 := bstep (se 1 (by rfl) ⟨1290464, by rfl⟩ : syracuseStep 1720619 = 2580929) B2580929
theorem B1720649 : Blo 1144635 1720649 := bstep (se 2 (by rfl) ⟨645243, by rfl⟩ : syracuseStep 1720649 = 1290487) B1290487
theorem B3260807 : Blo 1144635 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B1720763 : Blo 1144635 1720763 := bstep (se 1 (by rfl) ⟨1290572, by rfl⟩ : syracuseStep 1720763 = 2581145) B2581145
theorem B1720823 : Blo 1144635 1720823 := bstep (se 1 (by rfl) ⟨1290617, by rfl⟩ : syracuseStep 1720823 = 2581235) B2581235
theorem B1720847 : Blo 1144635 1720847 := bstep (se 1 (by rfl) ⟨1290635, by rfl⟩ : syracuseStep 1720847 = 2581271) B2581271
theorem B1720889 : Blo 1144635 1720889 := bstep (se 2 (by rfl) ⟨645333, by rfl⟩ : syracuseStep 1720889 = 1290667) B1290667
theorem B2179703 : Blo 1144635 2179703 := bstep (se 1 (by rfl) ⟨1634777, by rfl⟩ : syracuseStep 2179703 = 3269555) B3269555
theorem B1720967 : Blo 1144635 1720967 := bstep (se 1 (by rfl) ⟨1290725, by rfl⟩ : syracuseStep 1720967 = 2581451) B2581451
theorem B1721003 : Blo 1144635 1721003 := bstep (se 1 (by rfl) ⟨1290752, by rfl⟩ : syracuseStep 1721003 = 2581505) B2581505
theorem B11748017 : Blo 1144635 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B2900681 : Blo 1144635 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B1721033 : Blo 1144635 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B4899599 : Blo 1144635 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B11027249 : Blo 1144635 11027249 := bstep (se 2 (by rfl) ⟨4135218, by rfl⟩ : syracuseStep 11027249 = 8270437) B8270437
theorem B1721147 : Blo 1144635 1721147 := bstep (se 1 (by rfl) ⟨1290860, by rfl⟩ : syracuseStep 1721147 = 2581721) B2581721
theorem B1721207 : Blo 1144635 1721207 := bstep (se 1 (by rfl) ⟨1290905, by rfl⟩ : syracuseStep 1721207 = 2581811) B2581811
theorem B1721231 : Blo 1144635 1721231 := bstep (se 1 (by rfl) ⟨1290923, by rfl⟩ : syracuseStep 1721231 = 2581847) B2581847
theorem B1721273 : Blo 1144635 1721273 := bstep (se 2 (by rfl) ⟨645477, by rfl⟩ : syracuseStep 1721273 = 1290955) B1290955
theorem B1721351 : Blo 1144635 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B3261455 : Blo 1144635 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B2901035 : Blo 1144635 2901035 := bstep (se 1 (by rfl) ⟨2175776, by rfl⟩ : syracuseStep 2901035 = 4351553) B4351553
theorem B1721387 : Blo 1144635 1721387 := bstep (se 1 (by rfl) ⟨1291040, by rfl⟩ : syracuseStep 1721387 = 2582081) B2582081
theorem B1721417 : Blo 1144635 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B4899959 : Blo 1144635 4899959 := bstep (se 1 (by rfl) ⟨3674969, by rfl⟩ : syracuseStep 4899959 = 7349939) B7349939
theorem B1721531 : Blo 1144635 1721531 := bstep (se 1 (by rfl) ⟨1291148, by rfl⟩ : syracuseStep 1721531 = 2582297) B2582297
theorem B1721591 : Blo 1144635 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B3917071 : Blo 1144635 3917071 := bstep (se 1 (by rfl) ⟨2937803, by rfl⟩ : syracuseStep 3917071 = 5875607) B5875607
theorem B1721615 : Blo 1144635 1721615 := bstep (se 1 (by rfl) ⟨1291211, by rfl⟩ : syracuseStep 1721615 = 2582423) B2582423
theorem B1721657 : Blo 1144635 1721657 := bstep (se 2 (by rfl) ⟨645621, by rfl⟩ : syracuseStep 1721657 = 1291243) B1291243
theorem B1721735 : Blo 1144635 1721735 := bstep (se 1 (by rfl) ⟨1291301, by rfl⟩ : syracuseStep 1721735 = 2582603) B2582603
theorem B1721771 : Blo 1144635 1721771 := bstep (se 1 (by rfl) ⟨1291328, by rfl⟩ : syracuseStep 1721771 = 2582657) B2582657
theorem B1721801 : Blo 1144635 1721801 := bstep (se 2 (by rfl) ⟨645675, by rfl⟩ : syracuseStep 1721801 = 1291351) B1291351
theorem B3098171 : Blo 1144635 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B1721915 : Blo 1144635 1721915 := bstep (se 1 (by rfl) ⟨1291436, by rfl⟩ : syracuseStep 1721915 = 2582873) B2582873
theorem B41829965 : Blo 1144635 41829965 := bstep (se 3 (by rfl) ⟨7843118, by rfl⟩ : syracuseStep 41829965 = 15686237) B15686237
theorem B1721975 : Blo 1144635 1721975 := bstep (se 1 (by rfl) ⟨1291481, by rfl⟩ : syracuseStep 1721975 = 2582963) B2582963
theorem B1721999 : Blo 1144635 1721999 := bstep (se 1 (by rfl) ⟨1291499, by rfl⟩ : syracuseStep 1721999 = 2582999) B2582999
theorem B1722041 : Blo 1144635 1722041 := bstep (se 2 (by rfl) ⟨645765, by rfl⟩ : syracuseStep 1722041 = 1291531) B1291531
theorem B1722119 : Blo 1144635 1722119 := bstep (se 1 (by rfl) ⟨1291589, by rfl⟩ : syracuseStep 1722119 = 2583179) B2583179
theorem B1722155 : Blo 1144635 1722155 := bstep (se 1 (by rfl) ⟨1291616, by rfl⟩ : syracuseStep 1722155 = 2583233) B2583233
theorem B5228347 : Blo 1144635 5228347 := bstep (se 1 (by rfl) ⟨3921260, by rfl⟩ : syracuseStep 5228347 = 7842521) B7842521
theorem B1722185 : Blo 1144635 1722185 := bstep (se 2 (by rfl) ⟨645819, by rfl⟩ : syracuseStep 1722185 = 1291639) B1291639
theorem B1722299 : Blo 1144635 1722299 := bstep (se 1 (by rfl) ⟨1291724, by rfl⟩ : syracuseStep 1722299 = 2583449) B2583449
theorem B1722359 : Blo 1144635 1722359 := bstep (se 1 (by rfl) ⟨1291769, by rfl⟩ : syracuseStep 1722359 = 2583539) B2583539
theorem B2902027 : Blo 1144635 2902027 := bstep (se 1 (by rfl) ⟨2176520, by rfl⟩ : syracuseStep 2902027 = 4353041) B4353041
theorem B1722383 : Blo 1144635 1722383 := bstep (se 1 (by rfl) ⟨1291787, by rfl⟩ : syracuseStep 1722383 = 2583575) B2583575
theorem B1722425 : Blo 1144635 1722425 := bstep (se 2 (by rfl) ⟨645909, by rfl⟩ : syracuseStep 1722425 = 1291819) B1291819
theorem B4900931 : Blo 1144635 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B1722503 : Blo 1144635 1722503 := bstep (se 1 (by rfl) ⟨1291877, by rfl⟩ : syracuseStep 1722503 = 2583755) B2583755
theorem B2902169 : Blo 1144635 2902169 := bstep (se 2 (by rfl) ⟨1088313, by rfl⟩ : syracuseStep 2902169 = 2176627) B2176627
theorem B1722539 : Blo 1144635 1722539 := bstep (se 1 (by rfl) ⟨1291904, by rfl⟩ : syracuseStep 1722539 = 2583809) B2583809
theorem B1722569 : Blo 1144635 1722569 := bstep (se 2 (by rfl) ⟨645963, by rfl⟩ : syracuseStep 1722569 = 1291927) B1291927
theorem B13224181 : Blo 1144635 13224181 := bstep (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) B1239767
theorem B2902331 : Blo 1144635 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B1722683 : Blo 1144635 1722683 := bstep (se 1 (by rfl) ⟨1292012, by rfl⟩ : syracuseStep 1722683 = 2584025) B2584025
theorem B1722743 : Blo 1144635 1722743 := bstep (se 1 (by rfl) ⟨1292057, by rfl⟩ : syracuseStep 1722743 = 2584115) B2584115
theorem B1722767 : Blo 1144635 1722767 := bstep (se 1 (by rfl) ⟨1292075, by rfl⟩ : syracuseStep 1722767 = 2584151) B2584151
theorem B4901273 : Blo 1144635 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B1722809 : Blo 1144635 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B6539723 : Blo 1144635 6539723 := bstep (se 1 (by rfl) ⟨4904792, by rfl⟩ : syracuseStep 6539723 = 9809585) B9809585
theorem B1722887 : Blo 1144635 1722887 := bstep (se 1 (by rfl) ⟨1292165, by rfl⟩ : syracuseStep 1722887 = 2584331) B2584331
theorem B1722923 : Blo 1144635 1722923 := bstep (se 1 (by rfl) ⟨1292192, by rfl⟩ : syracuseStep 1722923 = 2584385) B2584385
theorem B1722953 : Blo 1144635 1722953 := bstep (se 2 (by rfl) ⟨646107, by rfl⟩ : syracuseStep 1722953 = 1292215) B1292215
theorem B3263095 : Blo 1144635 3263095 := bstep (se 1 (by rfl) ⟨2447321, by rfl⟩ : syracuseStep 3263095 = 4894643) B4894643
theorem B2902675 : Blo 1144635 2902675 := bstep (se 1 (by rfl) ⟨2177006, by rfl⟩ : syracuseStep 2902675 = 4354013) B4354013
theorem B2902817 : Blo 1144635 2902817 := bstep (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) B2177113
theorem B5884807 : Blo 1144635 5884807 := bstep (se 1 (by rfl) ⟨4413605, by rfl⟩ : syracuseStep 5884807 = 8827211) B8827211
theorem B4705517 : Blo 1144635 4705517 := bstep (se 3 (by rfl) ⟨882284, by rfl⟩ : syracuseStep 4705517 = 1764569) B1764569
theorem B63688037 : Blo 1144635 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B2575763 : Blo 1144635 2575763 := bstep (se 1 (by rfl) ⟨1931822, by rfl⟩ : syracuseStep 2575763 = 3863645) B3863645
theorem B2575817 : Blo 1144635 2575817 := bstep (se 2 (by rfl) ⟨965931, by rfl⟩ : syracuseStep 2575817 = 1931863) B1931863
theorem B2903809 : Blo 1144635 2903809 := bstep (se 2 (by rfl) ⟨1088928, by rfl⟩ : syracuseStep 2903809 = 2177857) B2177857
theorem B3264371 : Blo 1144635 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B2445203 : Blo 1144635 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B3264599 : Blo 1144635 3264599 := bstep (se 1 (by rfl) ⟨2448449, by rfl⟩ : syracuseStep 3264599 = 4896899) B4896899
theorem B2576519 : Blo 1144635 2576519 := bstep (se 1 (by rfl) ⟨1932389, by rfl⟩ : syracuseStep 2576519 = 3864779) B3864779
theorem B26824945 : Blo 1144635 26824945 := bstep (se 2 (by rfl) ⟨10059354, by rfl⟩ : syracuseStep 26824945 = 20118709) B20118709
theorem B3100961 : Blo 1144635 3100961 := bstep (se 2 (by rfl) ⟨1162860, by rfl⟩ : syracuseStep 3100961 = 2325721) B2325721
theorem B2576699 : Blo 1144635 2576699 := bstep (se 1 (by rfl) ⟨1932524, by rfl⟩ : syracuseStep 2576699 = 3865049) B3865049
theorem B2904407 : Blo 1144635 2904407 := bstep (se 1 (by rfl) ⟨2178305, by rfl⟩ : syracuseStep 2904407 = 4356611) B4356611
theorem B2576825 : Blo 1144635 2576825 := bstep (se 2 (by rfl) ⟨966309, by rfl⟩ : syracuseStep 2576825 = 1932619) B1932619
theorem B2904619 : Blo 1144635 2904619 := bstep (se 1 (by rfl) ⟨2178464, by rfl⟩ : syracuseStep 2904619 = 4356929) B4356929
theorem B2904761 : Blo 1144635 2904761 := bstep (se 2 (by rfl) ⟨1089285, by rfl⟩ : syracuseStep 2904761 = 2178571) B2178571
theorem B2577167 : Blo 1144635 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2577185 : Blo 1144635 2577185 := bstep (se 2 (by rfl) ⟨966444, by rfl⟩ : syracuseStep 2577185 = 1932889) B1932889
theorem B4346891 : Blo 1144635 4346891 := bstep (se 1 (by rfl) ⟨3260168, by rfl⟩ : syracuseStep 4346891 = 6520337) B6520337
theorem B2937971 : Blo 1144635 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B2577527 : Blo 1144635 2577527 := bstep (se 1 (by rfl) ⟨1933145, by rfl⟩ : syracuseStep 2577527 = 3866291) B3866291
theorem B2577707 : Blo 1144635 2577707 := bstep (se 1 (by rfl) ⟨1933280, by rfl⟩ : syracuseStep 2577707 = 3866561) B3866561
theorem B66016781 : Blo 1144635 66016781 := bstep (se 3 (by rfl) ⟨12378146, by rfl⟩ : syracuseStep 66016781 = 24756293) B24756293
theorem B13948481 : Blo 1144635 13948481 := bstep (se 2 (by rfl) ⟨5230680, by rfl⟩ : syracuseStep 13948481 = 10461361) B10461361
theorem B3266183 : Blo 1144635 3266183 := bstep (se 1 (by rfl) ⟨2449637, by rfl⟩ : syracuseStep 3266183 = 4899275) B4899275
theorem B2578067 : Blo 1144635 2578067 := bstep (se 1 (by rfl) ⟨1933550, by rfl⟩ : syracuseStep 2578067 = 3867101) B3867101
theorem B2905753 : Blo 1144635 2905753 := bstep (se 2 (by rfl) ⟨1089657, by rfl⟩ : syracuseStep 2905753 = 2179315) B2179315
theorem B2578121 : Blo 1144635 2578121 := bstep (se 2 (by rfl) ⟨966795, by rfl⟩ : syracuseStep 2578121 = 1933591) B1933591
theorem B2905915 : Blo 1144635 2905915 := bstep (se 1 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 2905915 = 4358873) B4358873
theorem B3266365 : Blo 1144635 3266365 := bstep (se 3 (by rfl) ⟨612443, by rfl⟩ : syracuseStep 3266365 = 1224887) B1224887
theorem B3921779 : Blo 1144635 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B3102583 : Blo 1144635 3102583 := bstep (se 1 (by rfl) ⟨2326937, by rfl⟩ : syracuseStep 3102583 = 4653875) B4653875
theorem B2611091 : Blo 1144635 2611091 := bstep (se 1 (by rfl) ⟨1958318, by rfl⟩ : syracuseStep 2611091 = 3916637) B3916637
theorem B2906057 : Blo 1144635 2906057 := bstep (se 2 (by rfl) ⟨1089771, by rfl⟩ : syracuseStep 2906057 = 2179543) B2179543
theorem B24827917 : Blo 1144635 24827917 := bstep (se 3 (by rfl) ⟨4655234, by rfl⟩ : syracuseStep 24827917 = 9310469) B9310469
theorem B2480161 : Blo 1144635 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B3266831 : Blo 1144635 3266831 := bstep (se 1 (by rfl) ⟨2450123, by rfl⟩ : syracuseStep 3266831 = 4900247) B4900247
theorem B18602257 : Blo 1144635 18602257 := bstep (se 2 (by rfl) ⟨6975846, by rfl⟩ : syracuseStep 18602257 = 13951693) B13951693
theorem B2906401 : Blo 1144635 2906401 := bstep (se 2 (by rfl) ⟨1089900, by rfl⟩ : syracuseStep 2906401 = 2179801) B2179801
theorem B2578823 : Blo 1144635 2578823 := bstep (se 1 (by rfl) ⟨1934117, by rfl⟩ : syracuseStep 2578823 = 3868235) B3868235
theorem B3103123 : Blo 1144635 3103123 := bstep (se 1 (by rfl) ⟨2327342, by rfl⟩ : syracuseStep 3103123 = 4654685) B4654685
theorem B3103265 : Blo 1144635 3103265 := bstep (se 2 (by rfl) ⟨1163724, by rfl⟩ : syracuseStep 3103265 = 2327449) B2327449
theorem B2579003 : Blo 1144635 2579003 := bstep (se 1 (by rfl) ⟨1934252, by rfl⟩ : syracuseStep 2579003 = 3868505) B3868505
theorem B2579129 : Blo 1144635 2579129 := bstep (se 2 (by rfl) ⟨967173, by rfl⟩ : syracuseStep 2579129 = 1934347) B1934347
theorem B2448073 : Blo 1144635 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B2906999 : Blo 1144635 2906999 := bstep (se 1 (by rfl) ⟨2180249, by rfl⟩ : syracuseStep 2906999 = 4360499) B4360499
theorem B44129285 : Blo 1144635 44129285 := bstep (se 4 (by rfl) ⟨4137120, by rfl⟩ : syracuseStep 44129285 = 8274241) B8274241
theorem B2579471 : Blo 1144635 2579471 := bstep (se 1 (by rfl) ⟨1934603, by rfl⟩ : syracuseStep 2579471 = 3869207) B3869207
theorem B2579489 : Blo 1144635 2579489 := bstep (se 2 (by rfl) ⟨967308, by rfl⟩ : syracuseStep 2579489 = 1934617) B1934617
theorem B2448569 : Blo 1144635 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B2579831 : Blo 1144635 2579831 := bstep (se 1 (by rfl) ⟨1934873, by rfl⟩ : syracuseStep 2579831 = 3869747) B3869747
theorem B3268097 : Blo 1144635 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B2580011 : Blo 1144635 2580011 := bstep (se 1 (by rfl) ⟨1935008, by rfl⟩ : syracuseStep 2580011 = 3870017) B3870017
theorem B8707661 : Blo 1144635 8707661 := bstep (se 3 (by rfl) ⟨1632686, by rfl⟩ : syracuseStep 8707661 = 3265373) B3265373
theorem B1629839 : Blo 1144635 1629839 := bstep (se 1 (by rfl) ⟨1222379, by rfl⟩ : syracuseStep 1629839 = 2444759) B2444759
theorem B2580371 : Blo 1144635 2580371 := bstep (se 1 (by rfl) ⟨1935278, by rfl⟩ : syracuseStep 2580371 = 3870557) B3870557
theorem B2580425 : Blo 1144635 2580425 := bstep (se 2 (by rfl) ⟨967659, by rfl⟩ : syracuseStep 2580425 = 1935319) B1935319
theorem B2449543 : Blo 1144635 2449543 := bstep (se 1 (by rfl) ⟨1837157, by rfl⟩ : syracuseStep 2449543 = 3674315) B3674315
theorem B14704841 : Blo 1144635 14704841 := bstep (se 2 (by rfl) ⟨5514315, by rfl⟩ : syracuseStep 14704841 = 11028631) B11028631
theorem B2581127 : Blo 1144635 2581127 := bstep (se 1 (by rfl) ⟨1935845, by rfl⟩ : syracuseStep 2581127 = 3871691) B3871691
theorem B4350779 : Blo 1144635 4350779 := bstep (se 1 (by rfl) ⟨3263084, by rfl⟩ : syracuseStep 4350779 = 6526169) B6526169
theorem B2581307 : Blo 1144635 2581307 := bstep (se 1 (by rfl) ⟨1935980, by rfl⟩ : syracuseStep 2581307 = 3871961) B3871961
theorem B2581433 : Blo 1144635 2581433 := bstep (se 2 (by rfl) ⟨968037, by rfl⟩ : syracuseStep 2581433 = 1936075) B1936075
theorem B3269747 : Blo 1144635 3269747 := bstep (se 1 (by rfl) ⟨2452310, by rfl⟩ : syracuseStep 3269747 = 4904621) B4904621
theorem B2581775 : Blo 1144635 2581775 := bstep (se 1 (by rfl) ⟨1936331, by rfl⟩ : syracuseStep 2581775 = 3872663) B3872663
theorem B4351265 : Blo 1144635 4351265 := bstep (se 2 (by rfl) ⟨1631724, by rfl⟩ : syracuseStep 4351265 = 3263449) B3263449
theorem B2581793 : Blo 1144635 2581793 := bstep (se 2 (by rfl) ⟨968172, by rfl⟩ : syracuseStep 2581793 = 1936345) B1936345
theorem B2450731 : Blo 1144635 2450731 := bstep (se 1 (by rfl) ⟨1838048, by rfl⟩ : syracuseStep 2450731 = 3676097) B3676097
theorem B2385353 : Blo 1144635 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B3270203 : Blo 1144635 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B2582135 : Blo 1144635 2582135 := bstep (se 1 (by rfl) ⟨1936601, by rfl⟩ : syracuseStep 2582135 = 3873203) B3873203
theorem B2582315 : Blo 1144635 2582315 := bstep (se 1 (by rfl) ⟨1936736, by rfl⟩ : syracuseStep 2582315 = 3873473) B3873473
theorem B14706481 : Blo 1144635 14706481 := bstep (se 2 (by rfl) ⟨5514930, by rfl⟩ : syracuseStep 14706481 = 11029861) B11029861
theorem B8710091 : Blo 1144635 8710091 := bstep (se 1 (by rfl) ⟨6532568, by rfl⟩ : syracuseStep 8710091 = 13065137) B13065137
theorem B2582675 : Blo 1144635 2582675 := bstep (se 1 (by rfl) ⟨1937006, by rfl⟩ : syracuseStep 2582675 = 3874013) B3874013
theorem B2582729 : Blo 1144635 2582729 := bstep (se 2 (by rfl) ⟨968523, by rfl⟩ : syracuseStep 2582729 = 1937047) B1937047
theorem B4352237 : Blo 1144635 4352237 := bstep (se 3 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 4352237 = 1632089) B1632089
theorem B2615753 : Blo 1144635 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B4352555 : Blo 1144635 4352555 := bstep (se 1 (by rfl) ⟨3264416, by rfl⟩ : syracuseStep 4352555 = 6528833) B6528833
theorem B1632955 : Blo 1144635 1632955 := bstep (se 1 (by rfl) ⟨1224716, by rfl⟩ : syracuseStep 1632955 = 2449433) B2449433
theorem B2583431 : Blo 1144635 2583431 := bstep (se 1 (by rfl) ⟨1937573, by rfl⟩ : syracuseStep 2583431 = 3875147) B3875147
theorem B11037707 : Blo 1144635 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B2583611 : Blo 1144635 2583611 := bstep (se 1 (by rfl) ⟨1937708, by rfl⟩ : syracuseStep 2583611 = 3875417) B3875417
theorem B5893181 : Blo 1144635 5893181 := bstep (se 3 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 5893181 = 2209943) B2209943
theorem B2583737 : Blo 1144635 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B1633655 : Blo 1144635 1633655 := bstep (se 1 (by rfl) ⟨1225241, by rfl⟩ : syracuseStep 1633655 = 2450483) B2450483
theorem B5795225 : Blo 1144635 5795225 := bstep (se 2 (by rfl) ⟨2173209, by rfl⟩ : syracuseStep 5795225 = 4346419) B4346419
theorem B2584079 : Blo 1144635 2584079 := bstep (se 1 (by rfl) ⟨1938059, by rfl⟩ : syracuseStep 2584079 = 3876119) B3876119
theorem B2584097 : Blo 1144635 2584097 := bstep (se 2 (by rfl) ⟨969036, by rfl⟩ : syracuseStep 2584097 = 1938073) B1938073
theorem B11038781 : Blo 1144635 11038781 := bstep (se 3 (by rfl) ⟨2069771, by rfl⟩ : syracuseStep 11038781 = 4139543) B4139543
theorem B1306895 : Blo 1144635 1306895 := bstep (se 1 (by rfl) ⟨980171, by rfl⟩ : syracuseStep 1306895 = 1960343) B1960343
theorem B1307023 : Blo 1144635 1307023 := bstep (se 1 (by rfl) ⟨980267, by rfl⟩ : syracuseStep 1307023 = 1960535) B1960535
theorem B12415517 : Blo 1144635 12415517 := bstep (se 3 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 12415517 = 4655819) B4655819
theorem B38171179 : Blo 1144635 38171179 := bstep (se 1 (by rfl) ⟨28628384, by rfl⟩ : syracuseStep 38171179 = 57256769) B57256769
theorem B3863159 : Blo 1144635 3863159 := bstep (se 1 (by rfl) ⟨2897369, by rfl⟩ : syracuseStep 3863159 = 5794739) B5794739
theorem B1635079 : Blo 1144635 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B11170649 : Blo 1144635 11170649 := bstep (se 2 (by rfl) ⟨4188993, by rfl⟩ : syracuseStep 11170649 = 8377987) B8377987
theorem B3142547 : Blo 1144635 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B2094265 : Blo 1144635 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B3863753 : Blo 1144635 3863753 := bstep (se 2 (by rfl) ⟨1448907, by rfl⟩ : syracuseStep 3863753 = 2897815) B2897815
theorem B7337249 : Blo 1144635 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B16774685 : Blo 1144635 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1144635 : Blo 1144635 1144635 := bstep (se 1 (by rfl) ⟨858476, by rfl⟩ : syracuseStep 1144635 = 1716953) B1716953
theorem B1144711 : Blo 1144635 1144711 := bstep (se 1 (by rfl) ⟨858533, by rfl⟩ : syracuseStep 1144711 = 1717067) B1717067
theorem B3864455 : Blo 1144635 3864455 := bstep (se 1 (by rfl) ⟨2898341, by rfl⟩ : syracuseStep 3864455 = 5796683) B5796683
theorem B1144719 : Blo 1144635 1144719 := bstep (se 1 (by rfl) ⟨858539, by rfl⟩ : syracuseStep 1144719 = 1717079) B1717079
theorem B5797817 : Blo 1144635 5797817 := bstep (se 2 (by rfl) ⟨2174181, by rfl⟩ : syracuseStep 5797817 = 4348363) B4348363
theorem B1144763 : Blo 1144635 1144763 := bstep (se 1 (by rfl) ⟨858572, by rfl⟩ : syracuseStep 1144763 = 1717145) B1717145
theorem B1144839 : Blo 1144635 1144839 := bstep (se 1 (by rfl) ⟨858629, by rfl⟩ : syracuseStep 1144839 = 1717259) B1717259
theorem B1144847 : Blo 1144635 1144847 := bstep (se 1 (by rfl) ⟨858635, by rfl⟩ : syracuseStep 1144847 = 1717271) B1717271
theorem B4356125 : Blo 1144635 4356125 := bstep (se 3 (by rfl) ⟨816773, by rfl⟩ : syracuseStep 4356125 = 1633547) B1633547
theorem B4356139 : Blo 1144635 4356139 := bstep (se 1 (by rfl) ⟨3267104, by rfl⟩ : syracuseStep 4356139 = 6534209) B6534209
theorem B1144891 : Blo 1144635 1144891 := bstep (se 1 (by rfl) ⟨858668, by rfl⟩ : syracuseStep 1144891 = 1717337) B1717337
theorem B1144967 : Blo 1144635 1144967 := bstep (se 1 (by rfl) ⟨858725, by rfl⟩ : syracuseStep 1144967 = 1717451) B1717451
theorem B1767559 : Blo 1144635 1767559 := bstep (se 1 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 1767559 = 2651339) B2651339
theorem B1144975 : Blo 1144635 1144975 := bstep (se 1 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 1144975 = 1717463) B1717463
theorem B1145019 : Blo 1144635 1145019 := bstep (se 1 (by rfl) ⟨858764, by rfl⟩ : syracuseStep 1145019 = 1717529) B1717529
theorem B3864833 : Blo 1144635 3864833 := bstep (se 2 (by rfl) ⟨1449312, by rfl⟩ : syracuseStep 3864833 = 2898625) B2898625
theorem B1145095 : Blo 1144635 1145095 := bstep (se 1 (by rfl) ⟨858821, by rfl⟩ : syracuseStep 1145095 = 1717643) B1717643
theorem B1145103 : Blo 1144635 1145103 := bstep (se 1 (by rfl) ⟨858827, by rfl⟩ : syracuseStep 1145103 = 1717655) B1717655
theorem B1145147 : Blo 1144635 1145147 := bstep (se 1 (by rfl) ⟨858860, by rfl⟩ : syracuseStep 1145147 = 1717721) B1717721
theorem B1145223 : Blo 1144635 1145223 := bstep (se 1 (by rfl) ⟨858917, by rfl⟩ : syracuseStep 1145223 = 1717835) B1717835
theorem B1145231 : Blo 1144635 1145231 := bstep (se 1 (by rfl) ⟨858923, by rfl⟩ : syracuseStep 1145231 = 1717847) B1717847
theorem B1145275 : Blo 1144635 1145275 := bstep (se 1 (by rfl) ⟨858956, by rfl⟩ : syracuseStep 1145275 = 1717913) B1717913
theorem B1145351 : Blo 1144635 1145351 := bstep (se 1 (by rfl) ⟨859013, by rfl⟩ : syracuseStep 1145351 = 1718027) B1718027
theorem B1145359 : Blo 1144635 1145359 := bstep (se 1 (by rfl) ⟨859019, by rfl⟩ : syracuseStep 1145359 = 1718039) B1718039
theorem B1145403 : Blo 1144635 1145403 := bstep (se 1 (by rfl) ⟨859052, by rfl⟩ : syracuseStep 1145403 = 1718105) B1718105
theorem B27916919 : Blo 1144635 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B1145479 : Blo 1144635 1145479 := bstep (se 1 (by rfl) ⟨859109, by rfl⟩ : syracuseStep 1145479 = 1718219) B1718219
theorem B1145487 : Blo 1144635 1145487 := bstep (se 1 (by rfl) ⟨859115, by rfl⟩ : syracuseStep 1145487 = 1718231) B1718231
theorem B1145531 : Blo 1144635 1145531 := bstep (se 1 (by rfl) ⟨859148, by rfl⟩ : syracuseStep 1145531 = 1718297) B1718297
theorem B1145607 : Blo 1144635 1145607 := bstep (se 1 (by rfl) ⟨859205, by rfl⟩ : syracuseStep 1145607 = 1718411) B1718411
theorem B1145615 : Blo 1144635 1145615 := bstep (se 1 (by rfl) ⟨859211, by rfl⟩ : syracuseStep 1145615 = 1718423) B1718423
theorem B1145659 : Blo 1144635 1145659 := bstep (se 1 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 1145659 = 1718489) B1718489
theorem B1932167 : Blo 1144635 1932167 := bstep (se 1 (by rfl) ⟨1449125, by rfl⟩ : syracuseStep 1932167 = 2898251) B2898251
theorem B1145735 : Blo 1144635 1145735 := bstep (se 1 (by rfl) ⟨859301, by rfl⟩ : syracuseStep 1145735 = 1718603) B1718603
theorem B1145743 : Blo 1144635 1145743 := bstep (se 1 (by rfl) ⟨859307, by rfl⟩ : syracuseStep 1145743 = 1718615) B1718615
theorem B3668921 : Blo 1144635 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B2980793 : Blo 1144635 2980793 := bstep (se 2 (by rfl) ⟨1117797, by rfl⟩ : syracuseStep 2980793 = 2235595) B2235595
theorem B1145787 : Blo 1144635 1145787 := bstep (se 1 (by rfl) ⟨859340, by rfl⟩ : syracuseStep 1145787 = 1718681) B1718681
theorem B6519811 : Blo 1144635 6519811 := bstep (se 1 (by rfl) ⟨4889858, by rfl⟩ : syracuseStep 6519811 = 9779717) B9779717
theorem B14711813 : Blo 1144635 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B1145863 : Blo 1144635 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B1145871 : Blo 1144635 1145871 := bstep (se 1 (by rfl) ⟨859403, by rfl⟩ : syracuseStep 1145871 = 1718807) B1718807
theorem B3865643 : Blo 1144635 3865643 := bstep (se 1 (by rfl) ⟨2899232, by rfl⟩ : syracuseStep 3865643 = 5798465) B5798465
theorem B1145915 : Blo 1144635 1145915 := bstep (se 1 (by rfl) ⟨859436, by rfl⟩ : syracuseStep 1145915 = 1718873) B1718873
theorem B8256599 : Blo 1144635 8256599 := bstep (se 1 (by rfl) ⟨6192449, by rfl⟩ : syracuseStep 8256599 = 12384899) B12384899
theorem B2751623 : Blo 1144635 2751623 := bstep (se 1 (by rfl) ⟨2063717, by rfl⟩ : syracuseStep 2751623 = 4127435) B4127435
theorem B1145991 : Blo 1144635 1145991 := bstep (se 1 (by rfl) ⟨859493, by rfl⟩ : syracuseStep 1145991 = 1718987) B1718987
theorem B1145999 : Blo 1144635 1145999 := bstep (se 1 (by rfl) ⟨859499, by rfl⟩ : syracuseStep 1145999 = 1718999) B1718999
theorem B8715437 : Blo 1144635 8715437 := bstep (se 3 (by rfl) ⟨1634144, by rfl⟩ : syracuseStep 8715437 = 3268289) B3268289
theorem B1146043 : Blo 1144635 1146043 := bstep (se 1 (by rfl) ⟨859532, by rfl⟩ : syracuseStep 1146043 = 1719065) B1719065
theorem B5799113 : Blo 1144635 5799113 := bstep (se 2 (by rfl) ⟨2174667, by rfl⟩ : syracuseStep 5799113 = 4349335) B4349335
theorem B1146119 : Blo 1144635 1146119 := bstep (se 1 (by rfl) ⟨859589, by rfl⟩ : syracuseStep 1146119 = 1719179) B1719179
theorem B1834255 : Blo 1144635 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B1146127 : Blo 1144635 1146127 := bstep (se 1 (by rfl) ⟨859595, by rfl⟩ : syracuseStep 1146127 = 1719191) B1719191
theorem B1146171 : Blo 1144635 1146171 := bstep (se 1 (by rfl) ⟨859628, by rfl⟩ : syracuseStep 1146171 = 1719257) B1719257
theorem B1146247 : Blo 1144635 1146247 := bstep (se 1 (by rfl) ⟨859685, by rfl⟩ : syracuseStep 1146247 = 1719371) B1719371
theorem B1146255 : Blo 1144635 1146255 := bstep (se 1 (by rfl) ⟨859691, by rfl⟩ : syracuseStep 1146255 = 1719383) B1719383
theorem B4193683 : Blo 1144635 4193683 := bstep (se 1 (by rfl) ⟨3145262, by rfl⟩ : syracuseStep 4193683 = 6290525) B6290525
theorem B1146299 : Blo 1144635 1146299 := bstep (se 1 (by rfl) ⟨859724, by rfl⟩ : syracuseStep 1146299 = 1719449) B1719449
theorem B13073885 : Blo 1144635 13073885 := bstep (se 3 (by rfl) ⟨2451353, by rfl⟩ : syracuseStep 13073885 = 4902707) B4902707
theorem B1146375 : Blo 1144635 1146375 := bstep (se 1 (by rfl) ⟨859781, by rfl⟩ : syracuseStep 1146375 = 1719563) B1719563
theorem B1932815 : Blo 1144635 1932815 := bstep (se 1 (by rfl) ⟨1449611, by rfl⟩ : syracuseStep 1932815 = 2899223) B2899223
theorem B1146383 : Blo 1144635 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B1146427 : Blo 1144635 1146427 := bstep (se 1 (by rfl) ⟨859820, by rfl⟩ : syracuseStep 1146427 = 1719641) B1719641
theorem B1146503 : Blo 1144635 1146503 := bstep (se 1 (by rfl) ⟨859877, by rfl⟩ : syracuseStep 1146503 = 1719755) B1719755
theorem B1146511 : Blo 1144635 1146511 := bstep (se 1 (by rfl) ⟨859883, by rfl⟩ : syracuseStep 1146511 = 1719767) B1719767
theorem B1146555 : Blo 1144635 1146555 := bstep (se 1 (by rfl) ⟨859916, by rfl⟩ : syracuseStep 1146555 = 1719833) B1719833
theorem B1834697 : Blo 1144635 1834697 := bstep (se 2 (by rfl) ⟨688011, by rfl⟩ : syracuseStep 1834697 = 1376023) B1376023
theorem B1146631 : Blo 1144635 1146631 := bstep (se 1 (by rfl) ⟨859973, by rfl⟩ : syracuseStep 1146631 = 1719947) B1719947
theorem B1146639 : Blo 1144635 1146639 := bstep (se 1 (by rfl) ⟨859979, by rfl⟩ : syracuseStep 1146639 = 1719959) B1719959
theorem B1146683 : Blo 1144635 1146683 := bstep (se 1 (by rfl) ⟨860012, by rfl⟩ : syracuseStep 1146683 = 1720025) B1720025
theorem B2752391 : Blo 1144635 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B1146759 : Blo 1144635 1146759 := bstep (se 1 (by rfl) ⟨860069, by rfl⟩ : syracuseStep 1146759 = 1720139) B1720139
theorem B1146767 : Blo 1144635 1146767 := bstep (se 1 (by rfl) ⟨860075, by rfl⟩ : syracuseStep 1146767 = 1720151) B1720151
theorem B3669907 : Blo 1144635 3669907 := bstep (se 1 (by rfl) ⟨2752430, by rfl⟩ : syracuseStep 3669907 = 5504861) B5504861
theorem B1146811 : Blo 1144635 1146811 := bstep (se 1 (by rfl) ⟨860108, by rfl⟩ : syracuseStep 1146811 = 1720217) B1720217
theorem B1933321 : Blo 1144635 1933321 := bstep (se 2 (by rfl) ⟨724995, by rfl⟩ : syracuseStep 1933321 = 1449991) B1449991
theorem B2064403 : Blo 1144635 2064403 := bstep (se 1 (by rfl) ⟨1548302, by rfl⟩ : syracuseStep 2064403 = 3096605) B3096605
theorem B1146919 : Blo 1144635 1146919 := bstep (se 1 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 1146919 = 1720379) B1720379
theorem B1146959 : Blo 1144635 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B12419153 : Blo 1144635 12419153 := bstep (se 2 (by rfl) ⟨4657182, by rfl⟩ : syracuseStep 12419153 = 9314365) B9314365
theorem B1146975 : Blo 1144635 1146975 := bstep (se 1 (by rfl) ⟨860231, by rfl⟩ : syracuseStep 1146975 = 1720463) B1720463
theorem B1147003 : Blo 1144635 1147003 := bstep (se 1 (by rfl) ⟨860252, by rfl⟩ : syracuseStep 1147003 = 1720505) B1720505
theorem B3866777 : Blo 1144635 3866777 := bstep (se 2 (by rfl) ⟨1450041, by rfl⟩ : syracuseStep 3866777 = 2900083) B2900083
theorem B1933483 : Blo 1144635 1933483 := bstep (se 1 (by rfl) ⟨1450112, by rfl⟩ : syracuseStep 1933483 = 2900225) B2900225
theorem B1147055 : Blo 1144635 1147055 := bstep (se 1 (by rfl) ⟨860291, by rfl⟩ : syracuseStep 1147055 = 1720583) B1720583
theorem B1147079 : Blo 1144635 1147079 := bstep (se 1 (by rfl) ⟨860309, by rfl⟩ : syracuseStep 1147079 = 1720619) B1720619
theorem B1147099 : Blo 1144635 1147099 := bstep (se 1 (by rfl) ⟨860324, by rfl⟩ : syracuseStep 1147099 = 1720649) B1720649
theorem B1147175 : Blo 1144635 1147175 := bstep (se 1 (by rfl) ⟨860381, by rfl⟩ : syracuseStep 1147175 = 1720763) B1720763
theorem B1147215 : Blo 1144635 1147215 := bstep (se 1 (by rfl) ⟨860411, by rfl⟩ : syracuseStep 1147215 = 1720823) B1720823
theorem B1147231 : Blo 1144635 1147231 := bstep (se 1 (by rfl) ⟨860423, by rfl⟩ : syracuseStep 1147231 = 1720847) B1720847
theorem B1147259 : Blo 1144635 1147259 := bstep (se 1 (by rfl) ⟨860444, by rfl⟩ : syracuseStep 1147259 = 1720889) B1720889
theorem B1147311 : Blo 1144635 1147311 := bstep (se 1 (by rfl) ⟨860483, by rfl⟩ : syracuseStep 1147311 = 1720967) B1720967
theorem B1147335 : Blo 1144635 1147335 := bstep (se 1 (by rfl) ⟨860501, by rfl⟩ : syracuseStep 1147335 = 1721003) B1721003
theorem B7832011 : Blo 1144635 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B1933787 : Blo 1144635 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B1147355 : Blo 1144635 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B14680601 : Blo 1144635 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B1147431 : Blo 1144635 1147431 := bstep (se 1 (by rfl) ⟨860573, by rfl⟩ : syracuseStep 1147431 = 1721147) B1721147
theorem B1147471 : Blo 1144635 1147471 := bstep (se 1 (by rfl) ⟨860603, by rfl⟩ : syracuseStep 1147471 = 1721207) B1721207
theorem B1147487 : Blo 1144635 1147487 := bstep (se 1 (by rfl) ⟨860615, by rfl⟩ : syracuseStep 1147487 = 1721231) B1721231
theorem B1147515 : Blo 1144635 1147515 := bstep (se 1 (by rfl) ⟨860636, by rfl⟩ : syracuseStep 1147515 = 1721273) B1721273
theorem B13238957 : Blo 1144635 13238957 := bstep (se 3 (by rfl) ⟨2482304, by rfl⟩ : syracuseStep 13238957 = 4964609) B4964609
theorem B1147567 : Blo 1144635 1147567 := bstep (se 1 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 1147567 = 1721351) B1721351
theorem B1934023 : Blo 1144635 1934023 := bstep (se 1 (by rfl) ⟨1450517, by rfl⟩ : syracuseStep 1934023 = 2901035) B2901035
theorem B1147591 : Blo 1144635 1147591 := bstep (se 1 (by rfl) ⟨860693, by rfl⟩ : syracuseStep 1147591 = 1721387) B1721387
theorem B1147611 : Blo 1144635 1147611 := bstep (se 1 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 1147611 = 1721417) B1721417
theorem B5800733 : Blo 1144635 5800733 := bstep (se 3 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 5800733 = 2175275) B2175275
theorem B1147687 : Blo 1144635 1147687 := bstep (se 1 (by rfl) ⟨860765, by rfl⟩ : syracuseStep 1147687 = 1721531) B1721531
theorem B1147727 : Blo 1144635 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B1147743 : Blo 1144635 1147743 := bstep (se 1 (by rfl) ⟨860807, by rfl⟩ : syracuseStep 1147743 = 1721615) B1721615
theorem B1934185 : Blo 1144635 1934185 := bstep (se 2 (by rfl) ⟨725319, by rfl⟩ : syracuseStep 1934185 = 1450639) B1450639
theorem B1147771 : Blo 1144635 1147771 := bstep (se 1 (by rfl) ⟨860828, by rfl⟩ : syracuseStep 1147771 = 1721657) B1721657
theorem B1147823 : Blo 1144635 1147823 := bstep (se 1 (by rfl) ⟨860867, by rfl⟩ : syracuseStep 1147823 = 1721735) B1721735
theorem B1147847 : Blo 1144635 1147847 := bstep (se 1 (by rfl) ⟨860885, by rfl⟩ : syracuseStep 1147847 = 1721771) B1721771
theorem B1147867 : Blo 1144635 1147867 := bstep (se 1 (by rfl) ⟨860900, by rfl⟩ : syracuseStep 1147867 = 1721801) B1721801
theorem B2065447 : Blo 1144635 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B1147943 : Blo 1144635 1147943 := bstep (se 1 (by rfl) ⟨860957, by rfl⟩ : syracuseStep 1147943 = 1721915) B1721915
theorem B27886643 : Blo 1144635 27886643 := bstep (se 1 (by rfl) ⟨20914982, by rfl⟩ : syracuseStep 27886643 = 41829965) B41829965
theorem B4195385 : Blo 1144635 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B1147983 : Blo 1144635 1147983 := bstep (se 1 (by rfl) ⟨860987, by rfl⟩ : syracuseStep 1147983 = 1721975) B1721975
theorem B1147999 : Blo 1144635 1147999 := bstep (se 1 (by rfl) ⟨860999, by rfl⟩ : syracuseStep 1147999 = 1721999) B1721999
theorem B1148027 : Blo 1144635 1148027 := bstep (se 1 (by rfl) ⟨861020, by rfl⟩ : syracuseStep 1148027 = 1722041) B1722041
theorem B1148079 : Blo 1144635 1148079 := bstep (se 1 (by rfl) ⟨861059, by rfl⟩ : syracuseStep 1148079 = 1722119) B1722119
theorem B1148103 : Blo 1144635 1148103 := bstep (se 1 (by rfl) ⟨861077, by rfl⟩ : syracuseStep 1148103 = 1722155) B1722155
theorem B1148123 : Blo 1144635 1148123 := bstep (se 1 (by rfl) ⟨861092, by rfl⟩ : syracuseStep 1148123 = 1722185) B1722185
theorem B7341349 : Blo 1144635 7341349 := bstep (se 4 (by rfl) ⟨688251, by rfl⟩ : syracuseStep 7341349 = 1376503) B1376503
theorem B1148199 : Blo 1144635 1148199 := bstep (se 1 (by rfl) ⟨861149, by rfl⟩ : syracuseStep 1148199 = 1722299) B1722299
theorem B3867965 : Blo 1144635 3867965 := bstep (se 3 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 3867965 = 1450487) B1450487
theorem B1148239 : Blo 1144635 1148239 := bstep (se 1 (by rfl) ⟨861179, by rfl⟩ : syracuseStep 1148239 = 1722359) B1722359
theorem B1148255 : Blo 1144635 1148255 := bstep (se 1 (by rfl) ⟨861191, by rfl⟩ : syracuseStep 1148255 = 1722383) B1722383
theorem B1148283 : Blo 1144635 1148283 := bstep (se 1 (by rfl) ⟨861212, by rfl⟩ : syracuseStep 1148283 = 1722425) B1722425
theorem B1148335 : Blo 1144635 1148335 := bstep (se 1 (by rfl) ⟨861251, by rfl⟩ : syracuseStep 1148335 = 1722503) B1722503
theorem B1934779 : Blo 1144635 1934779 := bstep (se 1 (by rfl) ⟨1451084, by rfl⟩ : syracuseStep 1934779 = 2902169) B2902169
theorem B1148359 : Blo 1144635 1148359 := bstep (se 1 (by rfl) ⟨861269, by rfl⟩ : syracuseStep 1148359 = 1722539) B1722539
theorem B1148379 : Blo 1144635 1148379 := bstep (se 1 (by rfl) ⟨861284, by rfl⟩ : syracuseStep 1148379 = 1722569) B1722569
theorem B1934887 : Blo 1144635 1934887 := bstep (se 1 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 1934887 = 2902331) B2902331
theorem B1148455 : Blo 1144635 1148455 := bstep (se 1 (by rfl) ⟨861341, by rfl⟩ : syracuseStep 1148455 = 1722683) B1722683
theorem B1148495 : Blo 1144635 1148495 := bstep (se 1 (by rfl) ⟨861371, by rfl⟩ : syracuseStep 1148495 = 1722743) B1722743
theorem B1148511 : Blo 1144635 1148511 := bstep (se 1 (by rfl) ⟨861383, by rfl⟩ : syracuseStep 1148511 = 1722767) B1722767
theorem B1148539 : Blo 1144635 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B4359815 : Blo 1144635 4359815 := bstep (se 1 (by rfl) ⟨3269861, by rfl⟩ : syracuseStep 4359815 = 6539723) B6539723
theorem B1148591 : Blo 1144635 1148591 := bstep (se 1 (by rfl) ⟨861443, by rfl⟩ : syracuseStep 1148591 = 1722887) B1722887
theorem B1148615 : Blo 1144635 1148615 := bstep (se 1 (by rfl) ⟨861461, by rfl⟩ : syracuseStep 1148615 = 1722923) B1722923
theorem B1148635 : Blo 1144635 1148635 := bstep (se 1 (by rfl) ⟨861476, by rfl⟩ : syracuseStep 1148635 = 1722953) B1722953
theorem B5506859 : Blo 1144635 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B2066249 : Blo 1144635 2066249 := bstep (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) B1549687
theorem B1935211 : Blo 1144635 1935211 := bstep (se 1 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 1935211 = 2902817) B2902817
theorem B5507129 : Blo 1144635 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B3868829 : Blo 1144635 3868829 := bstep (se 3 (by rfl) ⟨725405, by rfl⟩ : syracuseStep 3868829 = 1450811) B1450811
theorem B29788397 : Blo 1144635 29788397 := bstep (se 3 (by rfl) ⟨5585324, by rfl⟩ : syracuseStep 29788397 = 11170649) B11170649
theorem B8260231 : Blo 1144635 8260231 := bstep (se 1 (by rfl) ⟨6195173, by rfl⟩ : syracuseStep 8260231 = 12390347) B12390347
theorem B3869369 : Blo 1144635 3869369 := bstep (se 2 (by rfl) ⟨1451013, by rfl⟩ : syracuseStep 3869369 = 2902027) B2902027
theorem B1936271 : Blo 1144635 1936271 := bstep (se 1 (by rfl) ⟨1452203, by rfl⟩ : syracuseStep 1936271 = 2904407) B2904407
theorem B8719325 : Blo 1144635 8719325 := bstep (se 3 (by rfl) ⟨1634873, by rfl⟩ : syracuseStep 8719325 = 3269747) B3269747
theorem B17632241 : Blo 1144635 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B1936507 : Blo 1144635 1936507 := bstep (se 1 (by rfl) ⟨1452380, by rfl⟩ : syracuseStep 1936507 = 2904761) B2904761
theorem B3869963 : Blo 1144635 3869963 := bstep (se 1 (by rfl) ⟨2902472, by rfl⟩ : syracuseStep 3869963 = 5804945) B5804945
theorem B1379767 : Blo 1144635 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B3870233 : Blo 1144635 3870233 := bstep (se 2 (by rfl) ⟨1451337, by rfl⟩ : syracuseStep 3870233 = 2902675) B2902675
theorem B44011187 : Blo 1144635 44011187 := bstep (se 1 (by rfl) ⟨33008390, by rfl⟩ : syracuseStep 44011187 = 66016781) B66016781
theorem B11013869 : Blo 1144635 11013869 := bstep (se 3 (by rfl) ⟨2065100, by rfl⟩ : syracuseStep 11013869 = 4130201) B4130201
theorem B6360941 : Blo 1144635 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B1740727 : Blo 1144635 1740727 := bstep (se 1 (by rfl) ⟨1305545, by rfl⟩ : syracuseStep 1740727 = 2611091) B2611091
theorem B1937371 : Blo 1144635 1937371 := bstep (se 1 (by rfl) ⟨1453028, by rfl⟩ : syracuseStep 1937371 = 2906057) B2906057
theorem B37195949 : Blo 1144635 37195949 := bstep (se 3 (by rfl) ⟨6974240, by rfl⟩ : syracuseStep 37195949 = 13948481) B13948481
theorem B2068843 : Blo 1144635 2068843 := bstep (se 1 (by rfl) ⟨1551632, by rfl⟩ : syracuseStep 2068843 = 3103265) B3103265
theorem B1839503 : Blo 1144635 1839503 := bstep (se 1 (by rfl) ⟨1379627, by rfl⟩ : syracuseStep 1839503 = 2759255) B2759255
theorem B1937999 : Blo 1144635 1937999 := bstep (se 1 (by rfl) ⟨1453499, by rfl⟩ : syracuseStep 1937999 = 2906999) B2906999
theorem B3871367 : Blo 1144635 3871367 := bstep (se 1 (by rfl) ⟨2903525, by rfl⟩ : syracuseStep 3871367 = 5807051) B5807051
theorem B3871421 : Blo 1144635 3871421 := bstep (se 3 (by rfl) ⟨725891, by rfl⟩ : syracuseStep 3871421 = 1451783) B1451783
theorem B3871583 : Blo 1144635 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B4133807 : Blo 1144635 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B3871745 : Blo 1144635 3871745 := bstep (se 2 (by rfl) ⟨1451904, by rfl⟩ : syracuseStep 3871745 = 2903809) B2903809
theorem B5805107 : Blo 1144635 5805107 := bstep (se 1 (by rfl) ⟨4353830, by rfl⟩ : syracuseStep 5805107 = 8707661) B8707661
theorem B2757689 : Blo 1144635 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B9803227 : Blo 1144635 9803227 := bstep (se 1 (by rfl) ⟨7352420, by rfl⟩ : syracuseStep 9803227 = 14704841) B14704841
theorem B3872555 : Blo 1144635 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B50894905 : Blo 1144635 50894905 := bstep (se 2 (by rfl) ⟨19085589, by rfl⟩ : syracuseStep 50894905 = 38171179) B38171179
theorem B3872825 : Blo 1144635 3872825 := bstep (se 2 (by rfl) ⟨1452309, by rfl⟩ : syracuseStep 3872825 = 2904619) B2904619
theorem B3676313 : Blo 1144635 3676313 := bstep (se 2 (by rfl) ⟨1378617, by rfl⟩ : syracuseStep 3676313 = 2757235) B2757235
theorem B3873149 : Blo 1144635 3873149 := bstep (se 3 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 3873149 = 1452431) B1452431
theorem B14686595 : Blo 1144635 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B9804185 : Blo 1144635 9804185 := bstep (se 2 (by rfl) ⟨3676569, by rfl⟩ : syracuseStep 9804185 = 7353139) B7353139
theorem B5806727 : Blo 1144635 5806727 := bstep (se 1 (by rfl) ⟨4355045, by rfl⟩ : syracuseStep 5806727 = 8710091) B8710091
theorem B3873419 : Blo 1144635 3873419 := bstep (se 1 (by rfl) ⟨2905064, by rfl⟩ : syracuseStep 3873419 = 5810129) B5810129
theorem B8264555 : Blo 1144635 8264555 := bstep (se 1 (by rfl) ⟨6198416, by rfl⟩ : syracuseStep 8264555 = 12396833) B12396833
theorem B1448923 : Blo 1144635 1448923 := bstep (se 1 (by rfl) ⟨1086692, by rfl⟩ : syracuseStep 1448923 = 2173385) B2173385
theorem B1743835 : Blo 1144635 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B2759687 : Blo 1144635 2759687 := bstep (se 1 (by rfl) ⟨2069765, by rfl⟩ : syracuseStep 2759687 = 4139531) B4139531
theorem B12393719 : Blo 1144635 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B3874337 : Blo 1144635 3874337 := bstep (se 2 (by rfl) ⟨1452876, by rfl⟩ : syracuseStep 3874337 = 2905753) B2905753
theorem B3874553 : Blo 1144635 3874553 := bstep (se 2 (by rfl) ⟨1452957, by rfl⟩ : syracuseStep 3874553 = 2905915) B2905915
theorem B4136777 : Blo 1144635 4136777 := bstep (se 2 (by rfl) ⟨1551291, by rfl⟩ : syracuseStep 4136777 = 3102583) B3102583
theorem B3874823 : Blo 1144635 3874823 := bstep (se 1 (by rfl) ⟨2906117, by rfl⟩ : syracuseStep 3874823 = 5812235) B5812235
theorem B33103889 : Blo 1144635 33103889 := bstep (se 2 (by rfl) ⟨12413958, by rfl⟩ : syracuseStep 33103889 = 24827917) B24827917
theorem B5808185 : Blo 1144635 5808185 := bstep (se 2 (by rfl) ⟨2178069, by rfl⟩ : syracuseStep 5808185 = 4356139) B4356139
theorem B3874931 : Blo 1144635 3874931 := bstep (se 1 (by rfl) ⟨2906198, by rfl⟩ : syracuseStep 3874931 = 5812397) B5812397
theorem B1548649 : Blo 1144635 1548649 := bstep (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) B1161487
theorem B3875201 : Blo 1144635 3875201 := bstep (se 2 (by rfl) ⟨1453200, by rfl⟩ : syracuseStep 3875201 = 2906401) B2906401
theorem B6529517 : Blo 1144635 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B4137497 : Blo 1144635 4137497 := bstep (se 2 (by rfl) ⟨1551561, by rfl⟩ : syracuseStep 4137497 = 3103123) B3103123
theorem B8495641 : Blo 1144635 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B18621197 : Blo 1144635 18621197 := bstep (se 3 (by rfl) ⟨3491474, by rfl⟩ : syracuseStep 18621197 = 6982949) B6982949
theorem B4891499 : Blo 1144635 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B11183123 : Blo 1144635 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B3876011 : Blo 1144635 3876011 := bstep (se 1 (by rfl) ⟨2907008, by rfl⟩ : syracuseStep 3876011 = 5814017) B5814017
theorem B1549561 : Blo 1144635 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B8693081 : Blo 1144635 8693081 := bstep (se 2 (by rfl) ⟨3259905, by rfl⟩ : syracuseStep 8693081 = 6519811) B6519811
theorem B3876551 : Blo 1144635 3876551 := bstep (se 1 (by rfl) ⟨2907413, by rfl⟩ : syracuseStep 3876551 = 5814827) B5814827
theorem B4892525 : Blo 1144635 4892525 := bstep (se 3 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 4892525 = 1834697) B1834697
theorem B1288111 : Blo 1144635 1288111 := bstep (se 1 (by rfl) ⟨966083, by rfl⟩ : syracuseStep 1288111 = 1932167) B1932167
theorem B9807875 : Blo 1144635 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B5810291 : Blo 1144635 5810291 := bstep (se 1 (by rfl) ⟨4357718, by rfl⟩ : syracuseStep 5810291 = 8715437) B8715437
theorem B1288543 : Blo 1144635 1288543 := bstep (se 1 (by rfl) ⟨966407, by rfl⟩ : syracuseStep 1288543 = 1932815) B1932815
theorem B4893209 : Blo 1144635 4893209 := bstep (se 2 (by rfl) ⟨1834953, by rfl⟩ : syracuseStep 4893209 = 3669907) B3669907
theorem B1452583 : Blo 1144635 1452583 := bstep (se 1 (by rfl) ⟨1089437, by rfl⟩ : syracuseStep 1452583 = 2178875) B2178875
theorem B1288903 : Blo 1144635 1288903 := bstep (se 1 (by rfl) ⟨966677, by rfl⟩ : syracuseStep 1288903 = 1933355) B1933355
theorem B1452907 : Blo 1144635 1452907 := bstep (se 1 (by rfl) ⟨1089680, by rfl⟩ : syracuseStep 1452907 = 2179361) B2179361
theorem B19573649 : Blo 1144635 19573649 := bstep (se 2 (by rfl) ⟨7340118, by rfl⟩ : syracuseStep 19573649 = 14680237) B14680237
theorem B2173871 : Blo 1144635 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B9284651 : Blo 1144635 9284651 := bstep (se 1 (by rfl) ⟨6963488, by rfl⟩ : syracuseStep 9284651 = 13926977) B13926977
theorem B1453135 : Blo 1144635 1453135 := bstep (se 1 (by rfl) ⟨1089851, by rfl⟩ : syracuseStep 1453135 = 2179703) B2179703
theorem B7351499 : Blo 1144635 7351499 := bstep (se 1 (by rfl) ⟨5513624, by rfl⟩ : syracuseStep 7351499 = 11027249) B11027249
theorem B2174303 : Blo 1144635 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B3485053 : Blo 1144635 3485053 := bstep (se 3 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 3485053 = 1306895) B1306895
theorem B8269229 : Blo 1144635 8269229 := bstep (se 3 (by rfl) ⟨1550480, by rfl⟩ : syracuseStep 8269229 = 3100961) B3100961
theorem B1289767 : Blo 1144635 1289767 := bstep (se 1 (by rfl) ⟨967325, by rfl⟩ : syracuseStep 1289767 = 1934651) B1934651
theorem B5811911 : Blo 1144635 5811911 := bstep (se 1 (by rfl) ⟨4358933, by rfl⟩ : syracuseStep 5811911 = 8717867) B8717867
theorem B8695511 : Blo 1144635 8695511 := bstep (se 1 (by rfl) ⟨6521633, by rfl⟩ : syracuseStep 8695511 = 13043267) B13043267
theorem B5222761 : Blo 1144635 5222761 := bstep (se 2 (by rfl) ⟨1958535, by rfl⟩ : syracuseStep 5222761 = 3917071) B3917071
theorem B6533891 : Blo 1144635 6533891 := bstep (se 1 (by rfl) ⟨4900418, by rfl⟩ : syracuseStep 6533891 = 9800837) B9800837
theorem B1717097 : Blo 1144635 1717097 := bstep (se 2 (by rfl) ⟨643911, by rfl⟩ : syracuseStep 1717097 = 1287823) B1287823
theorem B1717175 : Blo 1144635 1717175 := bstep (se 1 (by rfl) ⟨1287881, by rfl⟩ : syracuseStep 1717175 = 2575763) B2575763
theorem B1717211 : Blo 1144635 1717211 := bstep (se 1 (by rfl) ⟨1287908, by rfl⟩ : syracuseStep 1717211 = 2575817) B2575817
theorem B19608641 : Blo 1144635 19608641 := bstep (se 2 (by rfl) ⟨7353240, by rfl⟩ : syracuseStep 19608641 = 14706481) B14706481
theorem B1291387 : Blo 1144635 1291387 := bstep (se 1 (by rfl) ⟨968540, by rfl⟩ : syracuseStep 1291387 = 1937081) B1937081
theorem B2176247 : Blo 1144635 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B6534391 : Blo 1144635 6534391 := bstep (se 1 (by rfl) ⟨4900793, by rfl⟩ : syracuseStep 6534391 = 9801587) B9801587
theorem B2176399 : Blo 1144635 2176399 := bstep (se 1 (by rfl) ⟨1632299, by rfl⟩ : syracuseStep 2176399 = 3264599) B3264599
theorem B1717679 : Blo 1144635 1717679 := bstep (se 1 (by rfl) ⟨1288259, by rfl⟩ : syracuseStep 1717679 = 2576519) B2576519
theorem B6206939 : Blo 1144635 6206939 := bstep (se 1 (by rfl) ⟨4655204, by rfl⟩ : syracuseStep 6206939 = 9310409) B9310409
theorem B1717769 : Blo 1144635 1717769 := bstep (se 2 (by rfl) ⟨644163, by rfl⟩ : syracuseStep 1717769 = 1288327) B1288327
theorem B1717799 : Blo 1144635 1717799 := bstep (se 1 (by rfl) ⟨1288349, by rfl⟩ : syracuseStep 1717799 = 2576699) B2576699
theorem B1291855 : Blo 1144635 1291855 := bstep (se 1 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 1291855 = 1937783) B1937783
theorem B1717883 : Blo 1144635 1717883 := bstep (se 1 (by rfl) ⟨1288412, by rfl⟩ : syracuseStep 1717883 = 2576825) B2576825
theorem B1718009 : Blo 1144635 1718009 := bstep (se 2 (by rfl) ⟨644253, by rfl⟩ : syracuseStep 1718009 = 1288507) B1288507
theorem B1718111 : Blo 1144635 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B1718123 : Blo 1144635 1718123 := bstep (se 1 (by rfl) ⟨1288592, by rfl⟩ : syracuseStep 1718123 = 2577185) B2577185
theorem B16529345 : Blo 1144635 16529345 := bstep (se 2 (by rfl) ⟨6198504, by rfl⟩ : syracuseStep 16529345 = 12397009) B12397009
theorem B2897927 : Blo 1144635 2897927 := bstep (se 1 (by rfl) ⟨2173445, by rfl⟩ : syracuseStep 2897927 = 4346891) B4346891
theorem B9811975 : Blo 1144635 9811975 := bstep (se 1 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 9811975 = 14717963) B14717963
theorem B2897977 : Blo 1144635 2897977 := bstep (se 2 (by rfl) ⟨1086741, by rfl⟩ : syracuseStep 2897977 = 2173483) B2173483
theorem B1718351 : Blo 1144635 1718351 := bstep (se 1 (by rfl) ⟨1288763, by rfl⟩ : syracuseStep 1718351 = 2577527) B2577527
theorem B1718471 : Blo 1144635 1718471 := bstep (se 1 (by rfl) ⟨1288853, by rfl⟩ : syracuseStep 1718471 = 2577707) B2577707
theorem B2177273 : Blo 1144635 2177273 := bstep (se 2 (by rfl) ⟨816477, by rfl⟩ : syracuseStep 2177273 = 1632955) B1632955
theorem B2898281 : Blo 1144635 2898281 := bstep (se 2 (by rfl) ⟨1086855, by rfl⟩ : syracuseStep 2898281 = 2173711) B2173711
theorem B1718633 : Blo 1144635 1718633 := bstep (se 2 (by rfl) ⟨644487, by rfl⟩ : syracuseStep 1718633 = 1288975) B1288975
theorem B13056389 : Blo 1144635 13056389 := bstep (se 4 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 13056389 = 2448073) B2448073
theorem B2177455 : Blo 1144635 2177455 := bstep (se 1 (by rfl) ⟨1633091, by rfl⟩ : syracuseStep 2177455 = 3266183) B3266183
theorem B1718711 : Blo 1144635 1718711 := bstep (se 1 (by rfl) ⟨1289033, by rfl⟩ : syracuseStep 1718711 = 2578067) B2578067
theorem B1718747 : Blo 1144635 1718747 := bstep (se 1 (by rfl) ⟨1289060, by rfl⟩ : syracuseStep 1718747 = 2578121) B2578121
theorem B7846409 : Blo 1144635 7846409 := bstep (se 2 (by rfl) ⟨2942403, by rfl⟩ : syracuseStep 7846409 = 5884807) B5884807
theorem B8698427 : Blo 1144635 8698427 := bstep (se 1 (by rfl) ⟨6523820, by rfl⟩ : syracuseStep 8698427 = 13047641) B13047641
theorem B3718007 : Blo 1144635 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B1719215 : Blo 1144635 1719215 := bstep (se 1 (by rfl) ⟨1289411, by rfl⟩ : syracuseStep 1719215 = 2578823) B2578823
theorem B1719305 : Blo 1144635 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B1719335 : Blo 1144635 1719335 := bstep (se 1 (by rfl) ⟨1289501, by rfl⟩ : syracuseStep 1719335 = 2579003) B2579003
theorem B1719419 : Blo 1144635 1719419 := bstep (se 1 (by rfl) ⟨1289564, by rfl⟩ : syracuseStep 1719419 = 2579129) B2579129
theorem B1719545 : Blo 1144635 1719545 := bstep (se 2 (by rfl) ⟨644829, by rfl⟩ : syracuseStep 1719545 = 1289659) B1289659
theorem B1719647 : Blo 1144635 1719647 := bstep (se 1 (by rfl) ⟨1289735, by rfl⟩ : syracuseStep 1719647 = 2579471) B2579471
theorem B1719659 : Blo 1144635 1719659 := bstep (se 1 (by rfl) ⟨1289744, by rfl⟩ : syracuseStep 1719659 = 2579489) B2579489
theorem B1719887 : Blo 1144635 1719887 := bstep (se 1 (by rfl) ⟨1289915, by rfl⟩ : syracuseStep 1719887 = 2579831) B2579831
theorem B2178731 : Blo 1144635 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B1720007 : Blo 1144635 1720007 := bstep (se 1 (by rfl) ⟨1290005, by rfl⟩ : syracuseStep 1720007 = 2580011) B2580011
theorem B1720169 : Blo 1144635 1720169 := bstep (se 2 (by rfl) ⟨645063, by rfl⟩ : syracuseStep 1720169 = 1290127) B1290127
theorem B1720247 : Blo 1144635 1720247 := bstep (se 1 (by rfl) ⟨1290185, by rfl⟩ : syracuseStep 1720247 = 2580371) B2580371
theorem B1720283 : Blo 1144635 1720283 := bstep (se 1 (by rfl) ⟨1290212, by rfl⟩ : syracuseStep 1720283 = 2580425) B2580425
theorem B35766593 : Blo 1144635 35766593 := bstep (se 2 (by rfl) ⟨13412472, by rfl⟩ : syracuseStep 35766593 = 26824945) B26824945
theorem B1720751 : Blo 1144635 1720751 := bstep (se 1 (by rfl) ⟨1290563, by rfl⟩ : syracuseStep 1720751 = 2581127) B2581127
theorem B39764429 : Blo 1144635 39764429 := bstep (se 3 (by rfl) ⟨7455830, by rfl⟩ : syracuseStep 39764429 = 14911661) B14911661
theorem B1720841 : Blo 1144635 1720841 := bstep (se 2 (by rfl) ⟨645315, by rfl⟩ : syracuseStep 1720841 = 1290631) B1290631
theorem B2900519 : Blo 1144635 2900519 := bstep (se 1 (by rfl) ⟨2175389, by rfl⟩ : syracuseStep 2900519 = 4350779) B4350779
theorem B1720871 : Blo 1144635 1720871 := bstep (se 1 (by rfl) ⟨1290653, by rfl⟩ : syracuseStep 1720871 = 2581307) B2581307
theorem B1720955 : Blo 1144635 1720955 := bstep (se 1 (by rfl) ⟨1290716, by rfl⟩ : syracuseStep 1720955 = 2581433) B2581433
theorem B1163899 : Blo 1144635 1163899 := bstep (se 1 (by rfl) ⟨872924, by rfl⟩ : syracuseStep 1163899 = 1745849) B1745849
theorem B1721081 : Blo 1144635 1721081 := bstep (se 2 (by rfl) ⟨645405, by rfl⟩ : syracuseStep 1721081 = 1290811) B1290811
theorem B1721183 : Blo 1144635 1721183 := bstep (se 1 (by rfl) ⟨1290887, by rfl⟩ : syracuseStep 1721183 = 2581775) B2581775
theorem B2900843 : Blo 1144635 2900843 := bstep (se 1 (by rfl) ⟨2175632, by rfl⟩ : syracuseStep 2900843 = 4351265) B4351265
theorem B1721195 : Blo 1144635 1721195 := bstep (se 1 (by rfl) ⟨1290896, by rfl⟩ : syracuseStep 1721195 = 2581793) B2581793
theorem B3720055 : Blo 1144635 3720055 := bstep (se 1 (by rfl) ⟨2790041, by rfl⟩ : syracuseStep 3720055 = 5580083) B5580083
theorem B2180105 : Blo 1144635 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B2180135 : Blo 1144635 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B1721423 : Blo 1144635 1721423 := bstep (se 1 (by rfl) ⟨1291067, by rfl⟩ : syracuseStep 1721423 = 2582135) B2582135
theorem B1721543 : Blo 1144635 1721543 := bstep (se 1 (by rfl) ⟨1291157, by rfl⟩ : syracuseStep 1721543 = 2582315) B2582315
theorem B1721705 : Blo 1144635 1721705 := bstep (se 2 (by rfl) ⟨645639, by rfl⟩ : syracuseStep 1721705 = 1291279) B1291279
theorem B9782693 : Blo 1144635 9782693 := bstep (se 4 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 9782693 = 1834255) B1834255
theorem B1721783 : Blo 1144635 1721783 := bstep (se 1 (by rfl) ⟨1291337, by rfl⟩ : syracuseStep 1721783 = 2582675) B2582675
theorem B1721819 : Blo 1144635 1721819 := bstep (se 1 (by rfl) ⟨1291364, by rfl⟩ : syracuseStep 1721819 = 2582729) B2582729
theorem B2901491 : Blo 1144635 2901491 := bstep (se 1 (by rfl) ⟨2176118, by rfl⟩ : syracuseStep 2901491 = 4352237) B4352237
theorem B35276309 : Blo 1144635 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B3261991 : Blo 1144635 3261991 := bstep (se 1 (by rfl) ⟨2446493, by rfl⟩ : syracuseStep 3261991 = 4892987) B4892987
theorem B2901703 : Blo 1144635 2901703 := bstep (se 1 (by rfl) ⟨2176277, by rfl⟩ : syracuseStep 2901703 = 4352555) B4352555
theorem B1722287 : Blo 1144635 1722287 := bstep (se 1 (by rfl) ⟨1291715, by rfl⟩ : syracuseStep 1722287 = 2583431) B2583431
theorem B7358471 : Blo 1144635 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B1722377 : Blo 1144635 1722377 := bstep (se 2 (by rfl) ⟨645891, by rfl⟩ : syracuseStep 1722377 = 1291783) B1291783
theorem B1722407 : Blo 1144635 1722407 := bstep (se 1 (by rfl) ⟨1291805, by rfl⟩ : syracuseStep 1722407 = 2583611) B2583611
theorem B22366309 : Blo 1144635 22366309 := bstep (se 4 (by rfl) ⟨2096841, by rfl⟩ : syracuseStep 22366309 = 4193683) B4193683
theorem B1722491 : Blo 1144635 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B1722617 : Blo 1144635 1722617 := bstep (se 2 (by rfl) ⟨645981, by rfl⟩ : syracuseStep 1722617 = 1291963) B1291963
theorem B1722719 : Blo 1144635 1722719 := bstep (se 1 (by rfl) ⟨1292039, by rfl⟩ : syracuseStep 1722719 = 2584079) B2584079
theorem B1722731 : Blo 1144635 1722731 := bstep (se 1 (by rfl) ⟨1292048, by rfl⟩ : syracuseStep 1722731 = 2584097) B2584097
theorem B37243313 : Blo 1144635 37243313 := bstep (se 2 (by rfl) ⟨13966242, by rfl⟩ : syracuseStep 37243313 = 27932485) B27932485
theorem B2902625 : Blo 1144635 2902625 := bstep (se 2 (by rfl) ⟨1088484, by rfl⟩ : syracuseStep 2902625 = 2176969) B2176969
theorem B7359187 : Blo 1144635 7359187 := bstep (se 1 (by rfl) ⟨5519390, by rfl⟩ : syracuseStep 7359187 = 11038781) B11038781
theorem B8277011 : Blo 1144635 8277011 := bstep (se 1 (by rfl) ⟨6207758, by rfl⟩ : syracuseStep 8277011 = 12415517) B12415517
theorem B2575439 : Blo 1144635 2575439 := bstep (se 1 (by rfl) ⟨1931579, by rfl⟩ : syracuseStep 2575439 = 3863159) B3863159
theorem B4902059 : Blo 1144635 4902059 := bstep (se 1 (by rfl) ⟨3676544, by rfl⟩ : syracuseStep 4902059 = 7353089) B7353089
theorem B2575835 : Blo 1144635 2575835 := bstep (se 1 (by rfl) ⟨1931876, by rfl⟩ : syracuseStep 2575835 = 3863753) B3863753
theorem B2576303 : Blo 1144635 2576303 := bstep (se 1 (by rfl) ⟨1932227, by rfl⟩ : syracuseStep 2576303 = 3864455) B3864455
theorem B2904083 : Blo 1144635 2904083 := bstep (se 1 (by rfl) ⟨2178062, by rfl⟩ : syracuseStep 2904083 = 4356125) B4356125
theorem B13062221 : Blo 1144635 13062221 := bstep (se 3 (by rfl) ⟨2449166, by rfl⟩ : syracuseStep 13062221 = 4898333) B4898333
theorem B2576555 : Blo 1144635 2576555 := bstep (se 1 (by rfl) ⟨1932416, by rfl⟩ : syracuseStep 2576555 = 3864833) B3864833
theorem B4346237 : Blo 1144635 4346237 := bstep (se 3 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 4346237 = 1629839) B1629839
theorem B2445947 : Blo 1144635 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B1987195 : Blo 1144635 1987195 := bstep (se 1 (by rfl) ⟨1490396, by rfl⟩ : syracuseStep 1987195 = 2980793) B2980793
theorem B2577095 : Blo 1144635 2577095 := bstep (se 1 (by rfl) ⟨1932821, by rfl⟩ : syracuseStep 2577095 = 3865643) B3865643
theorem B3724289 : Blo 1144635 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B3920903 : Blo 1144635 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B3266011 : Blo 1144635 3266011 := bstep (se 1 (by rfl) ⟨2449508, by rfl⟩ : syracuseStep 3266011 = 4899017) B4899017
theorem B3266057 : Blo 1144635 3266057 := bstep (se 2 (by rfl) ⟨1224771, by rfl⟩ : syracuseStep 3266057 = 2449543) B2449543
theorem B2577959 : Blo 1144635 2577959 := bstep (se 1 (by rfl) ⟨1933469, by rfl⟩ : syracuseStep 2577959 = 3866939) B3866939
theorem B3266399 : Blo 1144635 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B2578283 : Blo 1144635 2578283 := bstep (se 1 (by rfl) ⟨1933712, by rfl⟩ : syracuseStep 2578283 = 3867425) B3867425
theorem B2578337 : Blo 1144635 2578337 := bstep (se 2 (by rfl) ⟨966876, by rfl⟩ : syracuseStep 2578337 = 1933753) B1933753
theorem B3102799 : Blo 1144635 3102799 := bstep (se 1 (by rfl) ⟨2327099, by rfl⟩ : syracuseStep 3102799 = 4654199) B4654199
theorem B3266639 : Blo 1144635 3266639 := bstep (se 1 (by rfl) ⟨2449979, by rfl⟩ : syracuseStep 3266639 = 4899959) B4899959
theorem B31414513 : Blo 1144635 31414513 := bstep (se 2 (by rfl) ⟨11780442, by rfl⟩ : syracuseStep 31414513 = 23560885) B23560885
theorem B4348151 : Blo 1144635 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B2578679 : Blo 1144635 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B3267287 : Blo 1144635 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B2579273 : Blo 1144635 2579273 := bstep (se 2 (by rfl) ⟨967227, by rfl⟩ : syracuseStep 2579273 = 1934455) B1934455
theorem B3267515 : Blo 1144635 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B1793063 : Blo 1144635 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B3267641 : Blo 1144635 3267641 := bstep (se 2 (by rfl) ⟨1225365, by rfl⟩ : syracuseStep 3267641 = 2450731) B2450731
theorem B4349123 : Blo 1144635 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B6970789 : Blo 1144635 6970789 := bstep (se 4 (by rfl) ⟨653511, by rfl⟩ : syracuseStep 6970789 = 1307023) B1307023
theorem B3137011 : Blo 1144635 3137011 := bstep (se 1 (by rfl) ⟨2352758, by rfl⟩ : syracuseStep 3137011 = 4705517) B4705517
theorem B2580065 : Blo 1144635 2580065 := bstep (se 2 (by rfl) ⟨967524, by rfl⟩ : syracuseStep 2580065 = 1935049) B1935049
theorem B4349639 : Blo 1144635 4349639 := bstep (se 1 (by rfl) ⟨3262229, by rfl⟩ : syracuseStep 4349639 = 6524459) B6524459
theorem B6971129 : Blo 1144635 6971129 := bstep (se 2 (by rfl) ⟨2614173, by rfl⟩ : syracuseStep 6971129 = 5228347) B5228347
theorem B1630135 : Blo 1144635 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B2580407 : Blo 1144635 2580407 := bstep (se 1 (by rfl) ⟨1935305, by rfl⟩ : syracuseStep 2580407 = 3870611) B3870611
theorem B4645181 : Blo 1144635 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B2581001 : Blo 1144635 2581001 := bstep (se 2 (by rfl) ⟨967875, by rfl⟩ : syracuseStep 2581001 = 1935751) B1935751
theorem B8708633 : Blo 1144635 8708633 := bstep (se 2 (by rfl) ⟨3265737, by rfl⟩ : syracuseStep 8708633 = 6531475) B6531475
theorem B4350611 : Blo 1144635 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B1958647 : Blo 1144635 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B4350793 : Blo 1144635 4350793 := bstep (se 2 (by rfl) ⟨1631547, by rfl⟩ : syracuseStep 4350793 = 3263095) B3263095
theorem B2581343 : Blo 1144635 2581343 := bstep (se 1 (by rfl) ⟨1936007, by rfl⟩ : syracuseStep 2581343 = 3872015) B3872015
theorem B2581523 : Blo 1144635 2581523 := bstep (se 1 (by rfl) ⟨1936142, by rfl⟩ : syracuseStep 2581523 = 3872285) B3872285
theorem B2614519 : Blo 1144635 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B1631593 : Blo 1144635 1631593 := bstep (se 2 (by rfl) ⟨611847, by rfl⟩ : syracuseStep 1631593 = 1223695) B1223695
theorem B2581865 : Blo 1144635 2581865 := bstep (se 2 (by rfl) ⟨968199, by rfl⟩ : syracuseStep 2581865 = 1936399) B1936399
theorem B8840573 : Blo 1144635 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B18834889 : Blo 1144635 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B2647675 : Blo 1144635 2647675 := bstep (se 1 (by rfl) ⟨1985756, by rfl⟩ : syracuseStep 2647675 = 3971513) B3971513
theorem B2582459 : Blo 1144635 2582459 := bstep (se 1 (by rfl) ⟨1936844, by rfl⟩ : syracuseStep 2582459 = 3873689) B3873689
theorem B9791441 : Blo 1144635 9791441 := bstep (se 2 (by rfl) ⟨3671790, by rfl⟩ : syracuseStep 9791441 = 7343581) B7343581
theorem B29419523 : Blo 1144635 29419523 := bstep (se 1 (by rfl) ⟨22064642, by rfl⟩ : syracuseStep 29419523 = 44129285) B44129285
theorem B9922567 : Blo 1144635 9922567 := bstep (se 1 (by rfl) ⟨7441925, by rfl⟩ : syracuseStep 9922567 = 14883851) B14883851
theorem B2582585 : Blo 1144635 2582585 := bstep (se 2 (by rfl) ⟨968469, by rfl⟩ : syracuseStep 2582585 = 1936939) B1936939
theorem B8251469 : Blo 1144635 8251469 := bstep (se 3 (by rfl) ⟨1547150, by rfl⟩ : syracuseStep 8251469 = 3094301) B3094301
theorem B14706845 : Blo 1144635 14706845 := bstep (se 3 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 14706845 = 5515067) B5515067
theorem B2582927 : Blo 1144635 2582927 := bstep (se 1 (by rfl) ⟨1937195, by rfl⟩ : syracuseStep 2582927 = 3874391) B3874391
theorem B4352723 : Blo 1144635 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B2583251 : Blo 1144635 2583251 := bstep (se 1 (by rfl) ⟨1937438, by rfl⟩ : syracuseStep 2583251 = 3874877) B3874877
theorem B5795063 : Blo 1144635 5795063 := bstep (se 1 (by rfl) ⟨4346297, by rfl⟩ : syracuseStep 5795063 = 8692595) B8692595
theorem B22048037 : Blo 1144635 22048037 := bstep (se 4 (by rfl) ⟨2067003, by rfl⟩ : syracuseStep 22048037 = 4134007) B4134007
theorem B8711549 : Blo 1144635 8711549 := bstep (se 3 (by rfl) ⟨1633415, by rfl⟩ : syracuseStep 8711549 = 3266831) B3266831
theorem B2584187 : Blo 1144635 2584187 := bstep (se 1 (by rfl) ⟨1938140, by rfl⟩ : syracuseStep 2584187 = 3876281) B3876281
theorem B11169413 : Blo 1144635 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B5795549 : Blo 1144635 5795549 := bstep (se 3 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 5795549 = 2173331) B2173331
theorem B2584313 : Blo 1144635 2584313 := bstep (se 2 (by rfl) ⟨969117, by rfl⟩ : syracuseStep 2584313 = 1938235) B1938235
theorem B2322283 : Blo 1144635 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B4419515 : Blo 1144635 4419515 := bstep (se 1 (by rfl) ⟨3314636, by rfl⟩ : syracuseStep 4419515 = 6629273) B6629273
theorem B8253829 : Blo 1144635 8253829 := bstep (se 4 (by rfl) ⟨773796, by rfl⟩ : syracuseStep 8253829 = 1547593) B1547593
theorem B35320529 : Blo 1144635 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B3928787 : Blo 1144635 3928787 := bstep (se 1 (by rfl) ⟨2946590, by rfl⟩ : syracuseStep 3928787 = 5893181) B5893181
theorem B9794479 : Blo 1144635 9794479 := bstep (se 1 (by rfl) ⟨7345859, by rfl⟩ : syracuseStep 9794479 = 14691719) B14691719
theorem B3863483 : Blo 1144635 3863483 := bstep (se 1 (by rfl) ⟨2897612, by rfl⟩ : syracuseStep 3863483 = 5795225) B5795225
theorem B4355153 : Blo 1144635 4355153 := bstep (se 2 (by rfl) ⟨1633182, by rfl⟩ : syracuseStep 4355153 = 3266365) B3266365
theorem B8615159 : Blo 1144635 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B3306881 : Blo 1144635 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B4355471 : Blo 1144635 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B2356745 : Blo 1144635 2356745 := bstep (se 2 (by rfl) ⟨883779, by rfl⟩ : syracuseStep 2356745 = 1767559) B1767559
theorem B24803009 : Blo 1144635 24803009 := bstep (se 2 (by rfl) ⟨9301128, by rfl⟩ : syracuseStep 24803009 = 18602257) B18602257
theorem B1144655 : Blo 1144635 1144655 := bstep (se 1 (by rfl) ⟨858491, by rfl⟩ : syracuseStep 1144655 = 1716983) B1716983
theorem B1144671 : Blo 1144635 1144671 := bstep (se 1 (by rfl) ⟨858503, by rfl⟩ : syracuseStep 1144671 = 1717007) B1717007
theorem B9795437 : Blo 1144635 9795437 := bstep (se 3 (by rfl) ⟨1836644, by rfl⟩ : syracuseStep 9795437 = 3673289) B3673289
theorem B1144699 : Blo 1144635 1144699 := bstep (se 1 (by rfl) ⟨858524, by rfl⟩ : syracuseStep 1144699 = 1717049) B1717049
theorem B1144751 : Blo 1144635 1144751 := bstep (se 1 (by rfl) ⟨858563, by rfl⟩ : syracuseStep 1144751 = 1717127) B1717127
theorem B2095031 : Blo 1144635 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B1144775 : Blo 1144635 1144775 := bstep (se 1 (by rfl) ⟨858581, by rfl⟩ : syracuseStep 1144775 = 1717163) B1717163
theorem B1144795 : Blo 1144635 1144795 := bstep (se 1 (by rfl) ⟨858596, by rfl⟩ : syracuseStep 1144795 = 1717193) B1717193
theorem B1144871 : Blo 1144635 1144871 := bstep (se 1 (by rfl) ⟨858653, by rfl⟩ : syracuseStep 1144871 = 1717307) B1717307
theorem B1144911 : Blo 1144635 1144911 := bstep (se 1 (by rfl) ⟨858683, by rfl⟩ : syracuseStep 1144911 = 1717367) B1717367
theorem B4126801 : Blo 1144635 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B1144927 : Blo 1144635 1144927 := bstep (se 1 (by rfl) ⟨858695, by rfl⟩ : syracuseStep 1144927 = 1717391) B1717391
theorem B1144955 : Blo 1144635 1144955 := bstep (se 1 (by rfl) ⟨858716, by rfl⟩ : syracuseStep 1144955 = 1717433) B1717433
theorem B1145007 : Blo 1144635 1145007 := bstep (se 1 (by rfl) ⟨858755, by rfl⟩ : syracuseStep 1145007 = 1717511) B1717511
theorem B1145031 : Blo 1144635 1145031 := bstep (se 1 (by rfl) ⟨858773, by rfl⟩ : syracuseStep 1145031 = 1717547) B1717547
theorem B1145051 : Blo 1144635 1145051 := bstep (se 1 (by rfl) ⟨858788, by rfl⟩ : syracuseStep 1145051 = 1717577) B1717577
theorem B169834765 : Blo 1144635 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B1145127 : Blo 1144635 1145127 := bstep (se 1 (by rfl) ⟨858845, by rfl⟩ : syracuseStep 1145127 = 1717691) B1717691
theorem B4356413 : Blo 1144635 4356413 := bstep (se 3 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 4356413 = 1633655) B1633655
theorem B1931593 : Blo 1144635 1931593 := bstep (se 2 (by rfl) ⟨724347, by rfl⟩ : syracuseStep 1931593 = 1448695) B1448695
theorem B1145167 : Blo 1144635 1145167 := bstep (se 1 (by rfl) ⟨858875, by rfl⟩ : syracuseStep 1145167 = 1717751) B1717751
theorem B1145183 : Blo 1144635 1145183 := bstep (se 1 (by rfl) ⟨858887, by rfl⟩ : syracuseStep 1145183 = 1717775) B1717775
theorem B1931627 : Blo 1144635 1931627 := bstep (se 1 (by rfl) ⟨1448720, by rfl⟩ : syracuseStep 1931627 = 2897441) B2897441
theorem B1145211 : Blo 1144635 1145211 := bstep (se 1 (by rfl) ⟨858908, by rfl⟩ : syracuseStep 1145211 = 1717817) B1717817
theorem B1145263 : Blo 1144635 1145263 := bstep (se 1 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 1145263 = 1717895) B1717895
theorem B1145287 : Blo 1144635 1145287 := bstep (se 1 (by rfl) ⟨858965, by rfl⟩ : syracuseStep 1145287 = 1717931) B1717931
theorem B1145307 : Blo 1144635 1145307 := bstep (se 1 (by rfl) ⟨858980, by rfl⟩ : syracuseStep 1145307 = 1717961) B1717961
theorem B1145383 : Blo 1144635 1145383 := bstep (se 1 (by rfl) ⟨859037, by rfl⟩ : syracuseStep 1145383 = 1718075) B1718075
theorem B1145423 : Blo 1144635 1145423 := bstep (se 1 (by rfl) ⟨859067, by rfl⟩ : syracuseStep 1145423 = 1718135) B1718135
theorem B1145439 : Blo 1144635 1145439 := bstep (se 1 (by rfl) ⟨859079, by rfl⟩ : syracuseStep 1145439 = 1718159) B1718159
theorem B3865211 : Blo 1144635 3865211 := bstep (se 1 (by rfl) ⟨2898908, by rfl⟩ : syracuseStep 3865211 = 5797817) B5797817
theorem B1145467 : Blo 1144635 1145467 := bstep (se 1 (by rfl) ⟨859100, by rfl⟩ : syracuseStep 1145467 = 1718201) B1718201
theorem B1145519 : Blo 1144635 1145519 := bstep (se 1 (by rfl) ⟨859139, by rfl⟩ : syracuseStep 1145519 = 1718279) B1718279
theorem B1145543 : Blo 1144635 1145543 := bstep (se 1 (by rfl) ⟨859157, by rfl⟩ : syracuseStep 1145543 = 1718315) B1718315
theorem B2325203 : Blo 1144635 2325203 := bstep (se 1 (by rfl) ⟨1743902, by rfl⟩ : syracuseStep 2325203 = 3487805) B3487805
theorem B1145563 : Blo 1144635 1145563 := bstep (se 1 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 1145563 = 1718345) B1718345
theorem B1932025 : Blo 1144635 1932025 := bstep (se 2 (by rfl) ⟨724509, by rfl⟩ : syracuseStep 1932025 = 1449019) B1449019
theorem B3865373 : Blo 1144635 3865373 := bstep (se 3 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 3865373 = 1449515) B1449515
theorem B1145639 : Blo 1144635 1145639 := bstep (se 1 (by rfl) ⟨859229, by rfl⟩ : syracuseStep 1145639 = 1718459) B1718459
theorem B1145679 : Blo 1144635 1145679 := bstep (se 1 (by rfl) ⟨859259, by rfl⟩ : syracuseStep 1145679 = 1718519) B1718519
theorem B1145695 : Blo 1144635 1145695 := bstep (se 1 (by rfl) ⟨859271, by rfl⟩ : syracuseStep 1145695 = 1718543) B1718543
theorem B1145723 : Blo 1144635 1145723 := bstep (se 1 (by rfl) ⟨859292, by rfl⟩ : syracuseStep 1145723 = 1718585) B1718585
theorem B1145775 : Blo 1144635 1145775 := bstep (se 1 (by rfl) ⟨859331, by rfl⟩ : syracuseStep 1145775 = 1718663) B1718663
theorem B1145799 : Blo 1144635 1145799 := bstep (se 1 (by rfl) ⟨859349, by rfl⟩ : syracuseStep 1145799 = 1718699) B1718699
theorem B1145819 : Blo 1144635 1145819 := bstep (se 1 (by rfl) ⟨859364, by rfl⟩ : syracuseStep 1145819 = 1718729) B1718729
theorem B1932295 : Blo 1144635 1932295 := bstep (se 1 (by rfl) ⟨1449221, by rfl⟩ : syracuseStep 1932295 = 2898443) B2898443
theorem B1145895 : Blo 1144635 1145895 := bstep (se 1 (by rfl) ⟨859421, by rfl⟩ : syracuseStep 1145895 = 1718843) B1718843
theorem B1145935 : Blo 1144635 1145935 := bstep (se 1 (by rfl) ⟨859451, by rfl⟩ : syracuseStep 1145935 = 1718903) B1718903
theorem B18611279 : Blo 1144635 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B1145951 : Blo 1144635 1145951 := bstep (se 1 (by rfl) ⟨859463, by rfl⟩ : syracuseStep 1145951 = 1718927) B1718927
theorem B1145979 : Blo 1144635 1145979 := bstep (se 1 (by rfl) ⟨859484, by rfl⟩ : syracuseStep 1145979 = 1718969) B1718969
theorem B4652185 : Blo 1144635 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B1146031 : Blo 1144635 1146031 := bstep (se 1 (by rfl) ⟨859523, by rfl⟩ : syracuseStep 1146031 = 1719047) B1719047
theorem B1146055 : Blo 1144635 1146055 := bstep (se 1 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 1146055 = 1719083) B1719083
theorem B1146075 : Blo 1144635 1146075 := bstep (se 1 (by rfl) ⟨859556, by rfl⟩ : syracuseStep 1146075 = 1719113) B1719113
theorem B1146151 : Blo 1144635 1146151 := bstep (se 1 (by rfl) ⟨859613, by rfl⟩ : syracuseStep 1146151 = 1719227) B1719227
theorem B1146191 : Blo 1144635 1146191 := bstep (se 1 (by rfl) ⟨859643, by rfl⟩ : syracuseStep 1146191 = 1719287) B1719287
theorem B1146207 : Blo 1144635 1146207 := bstep (se 1 (by rfl) ⟨859655, by rfl⟩ : syracuseStep 1146207 = 1719311) B1719311
theorem B1146235 : Blo 1144635 1146235 := bstep (se 1 (by rfl) ⟨859676, by rfl⟩ : syracuseStep 1146235 = 1719353) B1719353
theorem B5504399 : Blo 1144635 5504399 := bstep (se 1 (by rfl) ⟨4128299, by rfl⟩ : syracuseStep 5504399 = 8256599) B8256599
theorem B7273901 : Blo 1144635 7273901 := bstep (se 3 (by rfl) ⟨1363856, by rfl⟩ : syracuseStep 7273901 = 2727713) B2727713
theorem B1834415 : Blo 1144635 1834415 := bstep (se 1 (by rfl) ⟨1375811, by rfl⟩ : syracuseStep 1834415 = 2751623) B2751623
theorem B1146287 : Blo 1144635 1146287 := bstep (se 1 (by rfl) ⟨859715, by rfl⟩ : syracuseStep 1146287 = 1719431) B1719431
theorem B1932727 : Blo 1144635 1932727 := bstep (se 1 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 1932727 = 2899091) B2899091
theorem B1146311 : Blo 1144635 1146311 := bstep (se 1 (by rfl) ⟨859733, by rfl⟩ : syracuseStep 1146311 = 1719467) B1719467
theorem B3866075 : Blo 1144635 3866075 := bstep (se 1 (by rfl) ⟨2899556, by rfl⟩ : syracuseStep 3866075 = 5799113) B5799113
theorem B1146331 : Blo 1144635 1146331 := bstep (se 1 (by rfl) ⟨859748, by rfl⟩ : syracuseStep 1146331 = 1719497) B1719497
theorem B3309095 : Blo 1144635 3309095 := bstep (se 1 (by rfl) ⟨2481821, by rfl⟩ : syracuseStep 3309095 = 4963643) B4963643
theorem B1146407 : Blo 1144635 1146407 := bstep (se 1 (by rfl) ⟨859805, by rfl⟩ : syracuseStep 1146407 = 1719611) B1719611
theorem B1146447 : Blo 1144635 1146447 := bstep (se 1 (by rfl) ⟨859835, by rfl⟩ : syracuseStep 1146447 = 1719671) B1719671
theorem B1146463 : Blo 1144635 1146463 := bstep (se 1 (by rfl) ⟨859847, by rfl⟩ : syracuseStep 1146463 = 1719695) B1719695
theorem B1932923 : Blo 1144635 1932923 := bstep (se 1 (by rfl) ⟨1449692, by rfl⟩ : syracuseStep 1932923 = 2899385) B2899385
theorem B1146491 : Blo 1144635 1146491 := bstep (se 1 (by rfl) ⟨859868, by rfl⟩ : syracuseStep 1146491 = 1719737) B1719737
theorem B8715923 : Blo 1144635 8715923 := bstep (se 1 (by rfl) ⟨6536942, by rfl⟩ : syracuseStep 8715923 = 13073885) B13073885
theorem B1146543 : Blo 1144635 1146543 := bstep (se 1 (by rfl) ⟨859907, by rfl⟩ : syracuseStep 1146543 = 1719815) B1719815
theorem B7339709 : Blo 1144635 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B1146567 : Blo 1144635 1146567 := bstep (se 1 (by rfl) ⟨859925, by rfl⟩ : syracuseStep 1146567 = 1719851) B1719851
theorem B1146587 : Blo 1144635 1146587 := bstep (se 1 (by rfl) ⟨859940, by rfl⟩ : syracuseStep 1146587 = 1719881) B1719881
theorem B1146663 : Blo 1144635 1146663 := bstep (se 1 (by rfl) ⟨859997, by rfl⟩ : syracuseStep 1146663 = 1719995) B1719995
theorem B1146703 : Blo 1144635 1146703 := bstep (se 1 (by rfl) ⟨860027, by rfl⟩ : syracuseStep 1146703 = 1720055) B1720055
theorem B1146719 : Blo 1144635 1146719 := bstep (se 1 (by rfl) ⟨860039, by rfl⟩ : syracuseStep 1146719 = 1720079) B1720079
theorem B1146747 : Blo 1144635 1146747 := bstep (se 1 (by rfl) ⟨860060, by rfl⟩ : syracuseStep 1146747 = 1720121) B1720121
theorem B1146799 : Blo 1144635 1146799 := bstep (se 1 (by rfl) ⟨860099, by rfl⟩ : syracuseStep 1146799 = 1720199) B1720199
theorem B6520769 : Blo 1144635 6520769 := bstep (se 2 (by rfl) ⟨2445288, by rfl⟩ : syracuseStep 6520769 = 4890577) B4890577
theorem B1146823 : Blo 1144635 1146823 := bstep (se 1 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 1146823 = 1720235) B1720235
theorem B1146843 : Blo 1144635 1146843 := bstep (se 1 (by rfl) ⟨860132, by rfl⟩ : syracuseStep 1146843 = 1720265) B1720265
theorem B2752537 : Blo 1144635 2752537 := bstep (se 2 (by rfl) ⟨1032201, by rfl⟩ : syracuseStep 2752537 = 2064403) B2064403
theorem B1147167 : Blo 1144635 1147167 := bstep (se 1 (by rfl) ⟨860375, by rfl⟩ : syracuseStep 1147167 = 1720751) B1720751
theorem B26509619 : Blo 1144635 26509619 := bstep (se 1 (by rfl) ⟨19882214, by rfl⟩ : syracuseStep 26509619 = 39764429) B39764429
theorem B1147227 : Blo 1144635 1147227 := bstep (se 1 (by rfl) ⟨860420, by rfl⟩ : syracuseStep 1147227 = 1720841) B1720841
theorem B1933679 : Blo 1144635 1933679 := bstep (se 1 (by rfl) ⟨1450259, by rfl⟩ : syracuseStep 1933679 = 2900519) B2900519
theorem B1147247 : Blo 1144635 1147247 := bstep (se 1 (by rfl) ⟨860435, by rfl⟩ : syracuseStep 1147247 = 1720871) B1720871
theorem B1147303 : Blo 1144635 1147303 := bstep (se 1 (by rfl) ⟨860477, by rfl⟩ : syracuseStep 1147303 = 1720955) B1720955
theorem B2064865 : Blo 1144635 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B1147387 : Blo 1144635 1147387 := bstep (se 1 (by rfl) ⟨860540, by rfl⟩ : syracuseStep 1147387 = 1721081) B1721081
theorem B3867155 : Blo 1144635 3867155 := bstep (se 1 (by rfl) ⟨2900366, by rfl⟩ : syracuseStep 3867155 = 5800733) B5800733
theorem B1147455 : Blo 1144635 1147455 := bstep (se 1 (by rfl) ⟨860591, by rfl⟩ : syracuseStep 1147455 = 1721183) B1721183
theorem B1933895 : Blo 1144635 1933895 := bstep (se 1 (by rfl) ⟨1450421, by rfl⟩ : syracuseStep 1933895 = 2900843) B2900843
theorem B1147463 : Blo 1144635 1147463 := bstep (se 1 (by rfl) ⟨860597, by rfl⟩ : syracuseStep 1147463 = 1721195) B1721195
theorem B1147615 : Blo 1144635 1147615 := bstep (se 1 (by rfl) ⟨860711, by rfl⟩ : syracuseStep 1147615 = 1721423) B1721423
theorem B1147695 : Blo 1144635 1147695 := bstep (se 1 (by rfl) ⟨860771, by rfl⟩ : syracuseStep 1147695 = 1721543) B1721543
theorem B1147803 : Blo 1144635 1147803 := bstep (se 1 (by rfl) ⟨860852, by rfl⟩ : syracuseStep 1147803 = 1721705) B1721705
theorem B6521795 : Blo 1144635 6521795 := bstep (se 1 (by rfl) ⟨4891346, by rfl⟩ : syracuseStep 6521795 = 9782693) B9782693
theorem B1147855 : Blo 1144635 1147855 := bstep (se 1 (by rfl) ⟨860891, by rfl⟩ : syracuseStep 1147855 = 1721783) B1721783
theorem B1147879 : Blo 1144635 1147879 := bstep (se 1 (by rfl) ⟨860909, by rfl⟩ : syracuseStep 1147879 = 1721819) B1721819
theorem B1934327 : Blo 1144635 1934327 := bstep (se 1 (by rfl) ⟨1450745, by rfl⟩ : syracuseStep 1934327 = 2901491) B2901491
theorem B5801057 : Blo 1144635 5801057 := bstep (se 2 (by rfl) ⟨2175396, by rfl⟩ : syracuseStep 5801057 = 4350793) B4350793
theorem B3671239 : Blo 1144635 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B1377499 : Blo 1144635 1377499 := bstep (se 1 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 1377499 = 2066249) B2066249
theorem B1148191 : Blo 1144635 1148191 := bstep (se 1 (by rfl) ⟨861143, by rfl⟩ : syracuseStep 1148191 = 1722287) B1722287
theorem B1148251 : Blo 1144635 1148251 := bstep (se 1 (by rfl) ⟨861188, by rfl⟩ : syracuseStep 1148251 = 1722377) B1722377
theorem B1148271 : Blo 1144635 1148271 := bstep (se 1 (by rfl) ⟨861203, by rfl⟩ : syracuseStep 1148271 = 1722407) B1722407
theorem B3671419 : Blo 1144635 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B2753929 : Blo 1144635 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B1148327 : Blo 1144635 1148327 := bstep (se 1 (by rfl) ⟨861245, by rfl⟩ : syracuseStep 1148327 = 1722491) B1722491
theorem B19858931 : Blo 1144635 19858931 := bstep (se 1 (by rfl) ⟨14894198, by rfl⟩ : syracuseStep 19858931 = 29788397) B29788397
theorem B1148411 : Blo 1144635 1148411 := bstep (se 1 (by rfl) ⟨861308, by rfl⟩ : syracuseStep 1148411 = 1722617) B1722617
theorem B1148479 : Blo 1144635 1148479 := bstep (se 1 (by rfl) ⟨861359, by rfl⟩ : syracuseStep 1148479 = 1722719) B1722719
theorem B1148487 : Blo 1144635 1148487 := bstep (se 1 (by rfl) ⟨861365, by rfl⟩ : syracuseStep 1148487 = 1722731) B1722731
theorem B2066081 : Blo 1144635 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1935083 : Blo 1144635 1935083 := bstep (se 1 (by rfl) ⟨1451312, by rfl⟩ : syracuseStep 1935083 = 2902625) B2902625
theorem B3868937 : Blo 1144635 3868937 := bstep (se 2 (by rfl) ⟨1450851, by rfl⟩ : syracuseStep 3868937 = 2901703) B2901703
theorem B7342579 : Blo 1144635 7342579 := bstep (se 1 (by rfl) ⟨5506934, by rfl⟩ : syracuseStep 7342579 = 11013869) B11013869
theorem B1936055 : Blo 1144635 1936055 := bstep (se 1 (by rfl) ⟨1452041, by rfl⟩ : syracuseStep 1936055 = 2904083) B2904083
theorem B29821745 : Blo 1144635 29821745 := bstep (se 2 (by rfl) ⟨11183154, by rfl⟩ : syracuseStep 29821745 = 22366309) B22366309
theorem B2755871 : Blo 1144635 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B5803325 : Blo 1144635 5803325 := bstep (se 3 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 5803325 = 2176247) B2176247
theorem B3870071 : Blo 1144635 3870071 := bstep (se 1 (by rfl) ⟨2902553, by rfl⟩ : syracuseStep 3870071 = 5805107) B5805107
theorem B1838459 : Blo 1144635 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B1936777 : Blo 1144635 1936777 := bstep (se 2 (by rfl) ⟨726291, by rfl⟩ : syracuseStep 1936777 = 1452583) B1452583
theorem B11013641 : Blo 1144635 11013641 := bstep (se 2 (by rfl) ⟨4130115, by rfl⟩ : syracuseStep 11013641 = 8260231) B8260231
theorem B1937209 : Blo 1144635 1937209 := bstep (se 2 (by rfl) ⟨726453, by rfl⟩ : syracuseStep 1937209 = 1452907) B1452907
theorem B1937513 : Blo 1144635 1937513 := bstep (se 2 (by rfl) ⟨726567, by rfl⟩ : syracuseStep 1937513 = 1453135) B1453135
theorem B3871151 : Blo 1144635 3871151 := bstep (se 1 (by rfl) ⟨2903363, by rfl⟩ : syracuseStep 3871151 = 5806727) B5806727
theorem B5509703 : Blo 1144635 5509703 := bstep (se 1 (by rfl) ⟨4132277, by rfl⟩ : syracuseStep 5509703 = 8264555) B8264555
theorem B1839689 : Blo 1144635 1839689 := bstep (se 2 (by rfl) ⟨689883, by rfl⟩ : syracuseStep 1839689 = 1379767) B1379767
theorem B1839791 : Blo 1144635 1839791 := bstep (se 1 (by rfl) ⟨1379843, by rfl⟩ : syracuseStep 1839791 = 2759687) B2759687
theorem B8262479 : Blo 1144635 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B2757851 : Blo 1144635 2757851 := bstep (se 1 (by rfl) ⟨2068388, by rfl⟩ : syracuseStep 2757851 = 4136777) B4136777
theorem B3872123 : Blo 1144635 3872123 := bstep (se 1 (by rfl) ⟨2904092, by rfl⟩ : syracuseStep 3872123 = 5808185) B5808185
theorem B25138613 : Blo 1144635 25138613 := bstep (se 5 (by rfl) ⟨1178372, by rfl⟩ : syracuseStep 25138613 = 2356745) B2356745
theorem B5805755 : Blo 1144635 5805755 := bstep (se 1 (by rfl) ⟨4354316, by rfl⟩ : syracuseStep 5805755 = 8708633) B8708633
theorem B2758331 : Blo 1144635 2758331 := bstep (se 1 (by rfl) ⟨2068748, by rfl⟩ : syracuseStep 2758331 = 4137497) B4137497
theorem B9803501 : Blo 1144635 9803501 := bstep (se 3 (by rfl) ⟨1838156, by rfl⟩ : syracuseStep 9803501 = 3676313) B3676313
theorem B2758457 : Blo 1144635 2758457 := bstep (se 2 (by rfl) ⟨1034421, by rfl⟩ : syracuseStep 2758457 = 2068843) B2068843
theorem B6527627 : Blo 1144635 6527627 := bstep (se 1 (by rfl) ⟨4895720, by rfl⟩ : syracuseStep 6527627 = 9791441) B9791441
theorem B3873527 : Blo 1144635 3873527 := bstep (se 1 (by rfl) ⟨2905145, by rfl⟩ : syracuseStep 3873527 = 5810291) B5810291
theorem B9804563 : Blo 1144635 9804563 := bstep (se 1 (by rfl) ⟨7353422, by rfl⟩ : syracuseStep 9804563 = 14706845) B14706845
theorem B13049099 : Blo 1144635 13049099 := bstep (se 1 (by rfl) ⟨9786824, by rfl⟩ : syracuseStep 13049099 = 19573649) B19573649
theorem B1449247 : Blo 1144635 1449247 := bstep (se 1 (by rfl) ⟨1086935, by rfl⟩ : syracuseStep 1449247 = 2173871) B2173871
theorem B111418901 : Blo 1144635 111418901 := bstep (se 6 (by rfl) ⟨2611380, by rfl⟩ : syracuseStep 111418901 = 5222761) B5222761
theorem B5807699 : Blo 1144635 5807699 := bstep (se 1 (by rfl) ⟨4355774, by rfl⟩ : syracuseStep 5807699 = 8711549) B8711549
theorem B5512819 : Blo 1144635 5512819 := bstep (se 1 (by rfl) ⟨4134614, by rfl⟩ : syracuseStep 5512819 = 8269229) B8269229
theorem B7446275 : Blo 1144635 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B3874607 : Blo 1144635 3874607 := bstep (se 1 (by rfl) ⟨2905955, by rfl⟩ : syracuseStep 3874607 = 5811911) B5811911
theorem B13082633 : Blo 1144635 13082633 := bstep (se 2 (by rfl) ⟨4905987, by rfl⟩ : syracuseStep 13082633 = 9811975) B9811975
theorem B4137065 : Blo 1144635 4137065 := bstep (se 2 (by rfl) ⟨1551399, by rfl⟩ : syracuseStep 4137065 = 3102799) B3102799
theorem B41886017 : Blo 1144635 41886017 := bstep (se 2 (by rfl) ⟨15707256, by rfl⟩ : syracuseStep 41886017 = 31414513) B31414513
theorem B5743439 : Blo 1144635 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B2204587 : Blo 1144635 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B4137959 : Blo 1144635 4137959 := bstep (se 1 (by rfl) ⟨3103469, by rfl⟩ : syracuseStep 4137959 = 6206939) B6206939
theorem B6530291 : Blo 1144635 6530291 := bstep (se 1 (by rfl) ⟨4897718, by rfl⟩ : syracuseStep 6530291 = 9795437) B9795437
theorem B11019563 : Blo 1144635 11019563 := bstep (se 1 (by rfl) ⟨8264672, by rfl⟩ : syracuseStep 11019563 = 16529345) B16529345
theorem B1451515 : Blo 1144635 1451515 := bstep (se 1 (by rfl) ⟨1088636, by rfl⟩ : syracuseStep 1451515 = 2177273) B2177273
theorem B6202913 : Blo 1144635 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B1287751 : Blo 1144635 1287751 := bstep (se 1 (by rfl) ⟨965813, by rfl⟩ : syracuseStep 1287751 = 1931627) B1931627
theorem B1550135 : Blo 1144635 1550135 := bstep (se 1 (by rfl) ⟨1162601, by rfl⟩ : syracuseStep 1550135 = 2325203) B2325203
theorem B1222943 : Blo 1144635 1222943 := bstep (se 1 (by rfl) ⟨917207, by rfl⟩ : syracuseStep 1222943 = 1834415) B1834415
theorem B8694053 : Blo 1144635 8694053 := bstep (se 4 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 8694053 = 1630135) B1630135
theorem B2206063 : Blo 1144635 2206063 := bstep (se 1 (by rfl) ⟨1654547, by rfl⟩ : syracuseStep 2206063 = 3309095) B3309095
theorem B1288615 : Blo 1144635 1288615 := bstep (se 1 (by rfl) ⟨966461, by rfl⟩ : syracuseStep 1288615 = 1932923) B1932923
theorem B5810615 : Blo 1144635 5810615 := bstep (se 1 (by rfl) ⟨4357961, by rfl⟩ : syracuseStep 5810615 = 8715923) B8715923
theorem B1452487 : Blo 1144635 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B4893139 : Blo 1144635 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B1289191 : Blo 1144635 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B8825971 : Blo 1144635 8825971 := bstep (se 1 (by rfl) ⟨6619478, by rfl⟩ : syracuseStep 8825971 = 13238957) B13238957
theorem B1453403 : Blo 1144635 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B18591095 : Blo 1144635 18591095 := bstep (se 1 (by rfl) ⟨13943321, by rfl⟩ : syracuseStep 18591095 = 27886643) B27886643
theorem B2796923 : Blo 1144635 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B1551865 : Blo 1144635 1551865 := bstep (se 2 (by rfl) ⟨581949, by rfl⟩ : syracuseStep 1551865 = 1163899) B1163899
theorem B4960073 : Blo 1144635 4960073 := bstep (se 2 (by rfl) ⟨1860027, by rfl⟩ : syracuseStep 4960073 = 3720055) B3720055
theorem B3486025 : Blo 1144635 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B1290847 : Blo 1144635 1290847 := bstep (se 1 (by rfl) ⟨968135, by rfl⟩ : syracuseStep 1290847 = 1936271) B1936271
theorem B25113185 : Blo 1144635 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B5812883 : Blo 1144635 5812883 := bstep (se 1 (by rfl) ⟨4359662, by rfl⟩ : syracuseStep 5812883 = 8719325) B8719325
theorem B5518007 : Blo 1144635 5518007 := bstep (se 1 (by rfl) ⟨4138505, by rfl⟩ : syracuseStep 5518007 = 8277011) B8277011
theorem B1716959 : Blo 1144635 1716959 := bstep (se 1 (by rfl) ⟨1287719, by rfl⟩ : syracuseStep 1716959 = 2575439) B2575439
theorem B1717223 : Blo 1144635 1717223 := bstep (se 1 (by rfl) ⟨1287917, by rfl⟩ : syracuseStep 1717223 = 2575835) B2575835
theorem B29340791 : Blo 1144635 29340791 := bstep (se 1 (by rfl) ⟨22005593, by rfl⟩ : syracuseStep 29340791 = 44011187) B44011187
theorem B1717481 : Blo 1144635 1717481 := bstep (se 2 (by rfl) ⟨644055, by rfl⟩ : syracuseStep 1717481 = 1288111) B1288111
theorem B1717535 : Blo 1144635 1717535 := bstep (se 1 (by rfl) ⟨1288151, by rfl⟩ : syracuseStep 1717535 = 2576303) B2576303
theorem B5813693 : Blo 1144635 5813693 := bstep (se 3 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 5813693 = 2180135) B2180135
theorem B1717703 : Blo 1144635 1717703 := bstep (se 1 (by rfl) ⟨1288277, by rfl⟩ : syracuseStep 1717703 = 2576555) B2576555
theorem B2897491 : Blo 1144635 2897491 := bstep (se 1 (by rfl) ⟨2173118, by rfl⟩ : syracuseStep 2897491 = 4346237) B4346237
theorem B1226335 : Blo 1144635 1226335 := bstep (se 1 (by rfl) ⟨919751, by rfl⟩ : syracuseStep 1226335 = 1839503) B1839503
theorem B1291999 : Blo 1144635 1291999 := bstep (se 1 (by rfl) ⟨968999, by rfl⟩ : syracuseStep 1291999 = 1937999) B1937999
theorem B1718057 : Blo 1144635 1718057 := bstep (se 2 (by rfl) ⟨644271, by rfl⟩ : syracuseStep 1718057 = 1288543) B1288543
theorem B1718063 : Blo 1144635 1718063 := bstep (se 1 (by rfl) ⟨1288547, by rfl⟩ : syracuseStep 1718063 = 2577095) B2577095
theorem B1718537 : Blo 1144635 1718537 := bstep (se 2 (by rfl) ⟨644451, by rfl⟩ : syracuseStep 1718537 = 1288903) B1288903
theorem B9812249 : Blo 1144635 9812249 := bstep (se 2 (by rfl) ⟨3679593, by rfl⟩ : syracuseStep 9812249 = 7359187) B7359187
theorem B2177371 : Blo 1144635 2177371 := bstep (se 1 (by rfl) ⟨1633028, by rfl⟩ : syracuseStep 2177371 = 3266057) B3266057
theorem B1718639 : Blo 1144635 1718639 := bstep (se 1 (by rfl) ⟨1288979, by rfl⟩ : syracuseStep 1718639 = 2577959) B2577959
theorem B2177599 : Blo 1144635 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B1718855 : Blo 1144635 1718855 := bstep (se 1 (by rfl) ⟨1289141, by rfl⟩ : syracuseStep 1718855 = 2578283) B2578283
theorem B1718891 : Blo 1144635 1718891 := bstep (se 1 (by rfl) ⟨1289168, by rfl⟩ : syracuseStep 1718891 = 2578337) B2578337
theorem B2177759 : Blo 1144635 2177759 := bstep (se 1 (by rfl) ⟨1633319, by rfl⟩ : syracuseStep 2177759 = 3266639) B3266639
theorem B2898767 : Blo 1144635 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B1719119 : Blo 1144635 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B6536123 : Blo 1144635 6536123 := bstep (se 1 (by rfl) ⟨4902092, by rfl⟩ : syracuseStep 6536123 = 9804185) B9804185
theorem B2178191 : Blo 1144635 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B1719515 : Blo 1144635 1719515 := bstep (se 1 (by rfl) ⟨1289636, by rfl⟩ : syracuseStep 1719515 = 2579273) B2579273
theorem B2178343 : Blo 1144635 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B2178427 : Blo 1144635 2178427 := bstep (se 1 (by rfl) ⟨1633820, by rfl⟩ : syracuseStep 2178427 = 3267641) B3267641
theorem B1719689 : Blo 1144635 1719689 := bstep (se 2 (by rfl) ⟨644883, by rfl⟩ : syracuseStep 1719689 = 1289767) B1289767
theorem B2899415 : Blo 1144635 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B1720043 : Blo 1144635 1720043 := bstep (se 1 (by rfl) ⟨1290032, by rfl⟩ : syracuseStep 1720043 = 2580065) B2580065
theorem B2899759 : Blo 1144635 2899759 := bstep (se 1 (by rfl) ⟨2174819, by rfl⟩ : syracuseStep 2899759 = 4349639) B4349639
theorem B3096377 : Blo 1144635 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B5586749 : Blo 1144635 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B1720271 : Blo 1144635 1720271 := bstep (se 1 (by rfl) ⟨1290203, by rfl⟩ : syracuseStep 1720271 = 2580407) B2580407
theorem B22069259 : Blo 1144635 22069259 := bstep (se 1 (by rfl) ⟨16551944, by rfl⟩ : syracuseStep 22069259 = 33103889) B33103889
theorem B3096787 : Blo 1144635 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B1720667 : Blo 1144635 1720667 := bstep (se 1 (by rfl) ⟨1290500, by rfl⟩ : syracuseStep 1720667 = 2581001) B2581001
theorem B2900407 : Blo 1144635 2900407 := bstep (se 1 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 2900407 = 4350611) B4350611
theorem B1720895 : Blo 1144635 1720895 := bstep (se 1 (by rfl) ⟨1290671, by rfl⟩ : syracuseStep 1720895 = 2581343) B2581343
theorem B3260999 : Blo 1144635 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B1721015 : Blo 1144635 1721015 := bstep (se 1 (by rfl) ⟨1290761, by rfl⟩ : syracuseStep 1721015 = 2581523) B2581523
theorem B7455415 : Blo 1144635 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B1721243 : Blo 1144635 1721243 := bstep (se 1 (by rfl) ⟨1290932, by rfl⟩ : syracuseStep 1721243 = 2581865) B2581865
theorem B13059305 : Blo 1144635 13059305 := bstep (se 2 (by rfl) ⟨4897239, by rfl⟩ : syracuseStep 13059305 = 9794479) B9794479
theorem B3261683 : Blo 1144635 3261683 := bstep (se 1 (by rfl) ⟨2446262, by rfl⟩ : syracuseStep 3261683 = 4892525) B4892525
theorem B1721639 : Blo 1144635 1721639 := bstep (se 1 (by rfl) ⟨1291229, by rfl⟩ : syracuseStep 1721639 = 2582459) B2582459
theorem B19613015 : Blo 1144635 19613015 := bstep (se 1 (by rfl) ⟨14709761, by rfl⟩ : syracuseStep 19613015 = 29419523) B29419523
theorem B6538583 : Blo 1144635 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B1721723 : Blo 1144635 1721723 := bstep (se 1 (by rfl) ⟨1291292, by rfl⟩ : syracuseStep 1721723 = 2582585) B2582585
theorem B1721849 : Blo 1144635 1721849 := bstep (se 2 (by rfl) ⟨645693, by rfl⟩ : syracuseStep 1721849 = 1291387) B1291387
theorem B1721951 : Blo 1144635 1721951 := bstep (se 1 (by rfl) ⟨1291463, by rfl⟩ : syracuseStep 1721951 = 2582927) B2582927
theorem B3262139 : Blo 1144635 3262139 := bstep (se 1 (by rfl) ⟨2446604, by rfl⟩ : syracuseStep 3262139 = 4893209) B4893209
theorem B2901815 : Blo 1144635 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B1722167 : Blo 1144635 1722167 := bstep (se 1 (by rfl) ⟨1291625, by rfl⟩ : syracuseStep 1722167 = 2583251) B2583251
theorem B2901865 : Blo 1144635 2901865 := bstep (se 2 (by rfl) ⟨1088199, by rfl⟩ : syracuseStep 2901865 = 2176399) B2176399
theorem B8701829 : Blo 1144635 8701829 := bstep (se 4 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 8701829 = 1631593) B1631593
theorem B1722473 : Blo 1144635 1722473 := bstep (se 2 (by rfl) ⟨645927, by rfl⟩ : syracuseStep 1722473 = 1291855) B1291855
theorem B4900999 : Blo 1144635 4900999 := bstep (se 1 (by rfl) ⟨3675749, by rfl⟩ : syracuseStep 4900999 = 7351499) B7351499
theorem B14698691 : Blo 1144635 14698691 := bstep (se 1 (by rfl) ⟨11024018, by rfl⟩ : syracuseStep 14698691 = 22048037) B22048037
theorem B1722791 : Blo 1144635 1722791 := bstep (se 1 (by rfl) ⟨1292093, by rfl⟩ : syracuseStep 1722791 = 2584187) B2584187
theorem B1722875 : Blo 1144635 1722875 := bstep (se 1 (by rfl) ⟨1292156, by rfl⟩ : syracuseStep 1722875 = 2584313) B2584313
theorem B16730725 : Blo 1144635 16730725 := bstep (se 4 (by rfl) ⟨1568505, by rfl⟩ : syracuseStep 16730725 = 3137011) B3137011
theorem B226446353 : Blo 1144635 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B2575457 : Blo 1144635 2575457 := bstep (se 2 (by rfl) ⟨965796, by rfl⟩ : syracuseStep 2575457 = 1931593) B1931593
theorem B23547019 : Blo 1144635 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B2903273 : Blo 1144635 2903273 := bstep (se 2 (by rfl) ⟨1088727, by rfl⟩ : syracuseStep 2903273 = 2177455) B2177455
theorem B2575655 : Blo 1144635 2575655 := bstep (se 1 (by rfl) ⟨1931741, by rfl⟩ : syracuseStep 2575655 = 3863483) B3863483
theorem B2903435 : Blo 1144635 2903435 := bstep (se 1 (by rfl) ⟨2177576, by rfl⟩ : syracuseStep 2903435 = 4355153) B4355153
theorem B2903647 : Blo 1144635 2903647 := bstep (se 1 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 2903647 = 4355471) B4355471
theorem B2576033 : Blo 1144635 2576033 := bstep (se 2 (by rfl) ⟨966012, by rfl⟩ : syracuseStep 2576033 = 1932025) B1932025
theorem B16535339 : Blo 1144635 16535339 := bstep (se 1 (by rfl) ⟨12401504, by rfl⟩ : syracuseStep 16535339 = 24803009) B24803009
theorem B2576393 : Blo 1144635 2576393 := bstep (se 2 (by rfl) ⟨966147, by rfl⟩ : syracuseStep 2576393 = 1932295) B1932295
theorem B2904275 : Blo 1144635 2904275 := bstep (se 1 (by rfl) ⟨2178206, by rfl⟩ : syracuseStep 2904275 = 4356413) B4356413
theorem B8704259 : Blo 1144635 8704259 := bstep (se 1 (by rfl) ⟨6528194, by rfl⟩ : syracuseStep 8704259 = 13056389) B13056389
theorem B5230939 : Blo 1144635 5230939 := bstep (se 1 (by rfl) ⟨3923204, by rfl⟩ : syracuseStep 5230939 = 7846409) B7846409
theorem B2576807 : Blo 1144635 2576807 := bstep (se 1 (by rfl) ⟨1932605, by rfl⟩ : syracuseStep 2576807 = 3865211) B3865211
theorem B2576915 : Blo 1144635 2576915 := bstep (se 1 (by rfl) ⟨1932686, by rfl⟩ : syracuseStep 2576915 = 3865373) B3865373
theorem B9294385 : Blo 1144635 9294385 := bstep (se 2 (by rfl) ⟨3485394, by rfl⟩ : syracuseStep 9294385 = 6970789) B6970789
theorem B2576969 : Blo 1144635 2576969 := bstep (se 2 (by rfl) ⟨966363, by rfl⟩ : syracuseStep 2576969 = 1932727) B1932727
theorem B2478671 : Blo 1144635 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B12407519 : Blo 1144635 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B16962509 : Blo 1144635 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B2577383 : Blo 1144635 2577383 := bstep (se 1 (by rfl) ⟨1933037, by rfl⟩ : syracuseStep 2577383 = 3866075) B3866075
theorem B4347179 : Blo 1144635 4347179 := bstep (se 1 (by rfl) ⟨3260384, by rfl⟩ : syracuseStep 4347179 = 6520769) B6520769
theorem B2577761 : Blo 1144635 2577761 := bstep (se 2 (by rfl) ⟨966660, by rfl⟩ : syracuseStep 2577761 = 1933321) B1933321
theorem B8279435 : Blo 1144635 8279435 := bstep (se 1 (by rfl) ⟨6209576, by rfl⟩ : syracuseStep 8279435 = 12419153) B12419153
theorem B2577851 : Blo 1144635 2577851 := bstep (se 1 (by rfl) ⟨1933388, by rfl⟩ : syracuseStep 2577851 = 3866777) B3866777
theorem B23844395 : Blo 1144635 23844395 := bstep (se 1 (by rfl) ⟨17883296, by rfl⟩ : syracuseStep 23844395 = 35766593) B35766593
theorem B2577977 : Blo 1144635 2577977 := bstep (se 2 (by rfl) ⟨966741, by rfl⟩ : syracuseStep 2577977 = 1933483) B1933483
theorem B9787067 : Blo 1144635 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B10442681 : Blo 1144635 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B11327521 : Blo 1144635 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B2578643 : Blo 1144635 2578643 := bstep (se 1 (by rfl) ⟨1933982, by rfl⟩ : syracuseStep 2578643 = 3867965) B3867965
theorem B2578697 : Blo 1144635 2578697 := bstep (se 2 (by rfl) ⟨967011, by rfl⟩ : syracuseStep 2578697 = 1934023) B1934023
theorem B2611529 : Blo 1144635 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B23517539 : Blo 1144635 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B2906543 : Blo 1144635 2906543 := bstep (se 1 (by rfl) ⟨2179907, by rfl⟩ : syracuseStep 2906543 = 4359815) B4359815
theorem B2578913 : Blo 1144635 2578913 := bstep (se 2 (by rfl) ⟨967092, by rfl⟩ : syracuseStep 2578913 = 1934185) B1934185
theorem B4905647 : Blo 1144635 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B2579219 : Blo 1144635 2579219 := bstep (se 1 (by rfl) ⟨1934414, by rfl⟩ : syracuseStep 2579219 = 3868829) B3868829
theorem B24828875 : Blo 1144635 24828875 := bstep (se 1 (by rfl) ⟨18621656, by rfl⟩ : syracuseStep 24828875 = 37243313) B37243313
theorem B9788465 : Blo 1144635 9788465 := bstep (se 2 (by rfl) ⟨3670674, by rfl⟩ : syracuseStep 9788465 = 7341349) B7341349
theorem B2579579 : Blo 1144635 2579579 := bstep (se 1 (by rfl) ⟨1934684, by rfl⟩ : syracuseStep 2579579 = 3869369) B3869369
theorem B2579705 : Blo 1144635 2579705 := bstep (se 2 (by rfl) ⟨967389, by rfl⟩ : syracuseStep 2579705 = 1934779) B1934779
theorem B11754827 : Blo 1144635 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B4349321 : Blo 1144635 4349321 := bstep (se 2 (by rfl) ⟨1630995, by rfl⟩ : syracuseStep 4349321 = 3261991) B3261991
theorem B2579849 : Blo 1144635 2579849 := bstep (se 2 (by rfl) ⟨967443, by rfl⟩ : syracuseStep 2579849 = 1934887) B1934887
theorem B3268039 : Blo 1144635 3268039 := bstep (se 1 (by rfl) ⟨2451029, by rfl⟩ : syracuseStep 3268039 = 4902059) B4902059
theorem B3530233 : Blo 1144635 3530233 := bstep (se 2 (by rfl) ⟨1323837, by rfl⟩ : syracuseStep 3530233 = 2647675) B2647675
theorem B2579975 : Blo 1144635 2579975 := bstep (se 1 (by rfl) ⟨1934981, by rfl⟩ : syracuseStep 2579975 = 3869963) B3869963
theorem B2580155 : Blo 1144635 2580155 := bstep (se 1 (by rfl) ⟨1935116, by rfl⟩ : syracuseStep 2580155 = 3870233) B3870233
theorem B2580281 : Blo 1144635 2580281 := bstep (se 2 (by rfl) ⟨967605, by rfl⟩ : syracuseStep 2580281 = 1935211) B1935211
theorem B13230089 : Blo 1144635 13230089 := bstep (se 2 (by rfl) ⟨4961283, by rfl⟩ : syracuseStep 13230089 = 9922567) B9922567
theorem B8708147 : Blo 1144635 8708147 := bstep (se 1 (by rfl) ⟨6531110, by rfl⟩ : syracuseStep 8708147 = 13062221) B13062221
theorem B24797299 : Blo 1144635 24797299 := bstep (se 1 (by rfl) ⟨18597974, by rfl⟩ : syracuseStep 24797299 = 37195949) B37195949
theorem B1630631 : Blo 1144635 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B2580911 : Blo 1144635 2580911 := bstep (se 1 (by rfl) ⟨1935683, by rfl⟩ : syracuseStep 2580911 = 3871367) B3871367
theorem B2580947 : Blo 1144635 2580947 := bstep (se 1 (by rfl) ⟨1935710, by rfl⟩ : syracuseStep 2580947 = 3871421) B3871421
theorem B2581055 : Blo 1144635 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B2482859 : Blo 1144635 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2581163 : Blo 1144635 2581163 := bstep (se 1 (by rfl) ⟨1935872, by rfl⟩ : syracuseStep 2581163 = 3871745) B3871745
theorem B2613935 : Blo 1144635 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B2581703 : Blo 1144635 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B2581883 : Blo 1144635 2581883 := bstep (se 1 (by rfl) ⟨1936412, by rfl⟩ : syracuseStep 2581883 = 3872825) B3872825
theorem B2582009 : Blo 1144635 2582009 := bstep (se 2 (by rfl) ⟨968253, by rfl⟩ : syracuseStep 2582009 = 1936507) B1936507
theorem B2582099 : Blo 1144635 2582099 := bstep (se 1 (by rfl) ⟨1936574, by rfl⟩ : syracuseStep 2582099 = 3873149) B3873149
theorem B9791063 : Blo 1144635 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B2582279 : Blo 1144635 2582279 := bstep (se 1 (by rfl) ⟨1936709, by rfl⟩ : syracuseStep 2582279 = 3873419) B3873419
theorem B4646737 : Blo 1144635 4646737 := bstep (se 2 (by rfl) ⟨1742526, by rfl⟩ : syracuseStep 4646737 = 3485053) B3485053
theorem B2582891 : Blo 1144635 2582891 := bstep (se 1 (by rfl) ⟨1937168, by rfl⟩ : syracuseStep 2582891 = 3874337) B3874337
theorem B4647419 : Blo 1144635 4647419 := bstep (se 1 (by rfl) ⟨3485564, by rfl⟩ : syracuseStep 4647419 = 6971129) B6971129
theorem B2583035 : Blo 1144635 2583035 := bstep (se 1 (by rfl) ⟨1937276, by rfl⟩ : syracuseStep 2583035 = 3874553) B3874553
theorem B2320969 : Blo 1144635 2320969 := bstep (se 2 (by rfl) ⟨870363, by rfl⟩ : syracuseStep 2320969 = 1740727) B1740727
theorem B2583161 : Blo 1144635 2583161 := bstep (se 2 (by rfl) ⟨968685, by rfl⟩ : syracuseStep 2583161 = 1937371) B1937371
theorem B2583215 : Blo 1144635 2583215 := bstep (se 1 (by rfl) ⟨1937411, by rfl⟩ : syracuseStep 2583215 = 3874823) B3874823
theorem B2583287 : Blo 1144635 2583287 := bstep (se 1 (by rfl) ⟨1937465, by rfl⟩ : syracuseStep 2583287 = 3874931) B3874931
theorem B2583467 : Blo 1144635 2583467 := bstep (se 1 (by rfl) ⟨1937600, by rfl⟩ : syracuseStep 2583467 = 3875201) B3875201
theorem B4353011 : Blo 1144635 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B11005105 : Blo 1144635 11005105 := bstep (se 2 (by rfl) ⟨4126914, by rfl⟩ : syracuseStep 11005105 = 8253829) B8253829
theorem B12414131 : Blo 1144635 12414131 := bstep (se 1 (by rfl) ⟨9310598, by rfl⟩ : syracuseStep 12414131 = 18621197) B18621197
theorem B2584007 : Blo 1144635 2584007 := bstep (se 1 (by rfl) ⟨1938005, by rfl⟩ : syracuseStep 2584007 = 3876011) B3876011
theorem B2649593 : Blo 1144635 2649593 := bstep (se 2 (by rfl) ⟨993597, by rfl⟩ : syracuseStep 2649593 = 1987195) B1987195
theorem B5795387 : Blo 1144635 5795387 := bstep (se 1 (by rfl) ⟨4346540, by rfl⟩ : syracuseStep 5795387 = 8693081) B8693081
theorem B5893715 : Blo 1144635 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B2584367 : Blo 1144635 2584367 := bstep (se 1 (by rfl) ⟨1938275, by rfl⟩ : syracuseStep 2584367 = 3876551) B3876551
theorem B5500979 : Blo 1144635 5500979 := bstep (se 1 (by rfl) ⟨4125734, by rfl⟩ : syracuseStep 5500979 = 8251469) B8251469
theorem B8712521 : Blo 1144635 8712521 := bstep (se 2 (by rfl) ⟨3267195, by rfl⟩ : syracuseStep 8712521 = 6534391) B6534391
theorem B4354681 : Blo 1144635 4354681 := bstep (se 2 (by rfl) ⟨1633005, by rfl⟩ : syracuseStep 4354681 = 3266011) B3266011
theorem B13070969 : Blo 1144635 13070969 := bstep (se 2 (by rfl) ⟨4901613, by rfl⟩ : syracuseStep 13070969 = 9803227) B9803227
theorem B6189767 : Blo 1144635 6189767 := bstep (se 1 (by rfl) ⟨4642325, by rfl⟩ : syracuseStep 6189767 = 9284651) B9284651
theorem B3863375 : Blo 1144635 3863375 := bstep (se 1 (by rfl) ⟨2897531, by rfl⟩ : syracuseStep 3863375 = 5795063) B5795063
theorem B5797007 : Blo 1144635 5797007 := bstep (se 1 (by rfl) ⟨4347755, by rfl⟩ : syracuseStep 5797007 = 8695511) B8695511
theorem B3863699 : Blo 1144635 3863699 := bstep (se 1 (by rfl) ⟨2897774, by rfl⟩ : syracuseStep 3863699 = 5795549) B5795549
theorem B2946343 : Blo 1144635 2946343 := bstep (se 1 (by rfl) ⟨2209757, by rfl⟩ : syracuseStep 2946343 = 4419515) B4419515
theorem B3863969 : Blo 1144635 3863969 := bstep (se 2 (by rfl) ⟨1448988, by rfl⟩ : syracuseStep 3863969 = 2897977) B2897977
theorem B67859873 : Blo 1144635 67859873 := bstep (se 2 (by rfl) ⟨25447452, by rfl⟩ : syracuseStep 67859873 = 50894905) B50894905
theorem B4781501 : Blo 1144635 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B5502401 : Blo 1144635 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B2619191 : Blo 1144635 2619191 := bstep (se 1 (by rfl) ⟨1964393, by rfl⟩ : syracuseStep 2619191 = 3928787) B3928787
theorem B4355927 : Blo 1144635 4355927 := bstep (se 1 (by rfl) ⟨3266945, by rfl⟩ : syracuseStep 4355927 = 6533891) B6533891
theorem B1144731 : Blo 1144635 1144731 := bstep (se 1 (by rfl) ⟨858548, by rfl⟩ : syracuseStep 1144731 = 1717097) B1717097
theorem B1144783 : Blo 1144635 1144783 := bstep (se 1 (by rfl) ⟨858587, by rfl⟩ : syracuseStep 1144783 = 1717175) B1717175
theorem B1144807 : Blo 1144635 1144807 := bstep (se 1 (by rfl) ⟨858605, by rfl⟩ : syracuseStep 1144807 = 1717211) B1717211
theorem B13072427 : Blo 1144635 13072427 := bstep (se 1 (by rfl) ⟨9804320, by rfl⟩ : syracuseStep 13072427 = 19608641) B19608641
theorem B5798141 : Blo 1144635 5798141 := bstep (se 3 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 5798141 = 2174303) B2174303
theorem B1145119 : Blo 1144635 1145119 := bstep (se 1 (by rfl) ⟨858839, by rfl⟩ : syracuseStep 1145119 = 1717679) B1717679
theorem B1145179 : Blo 1144635 1145179 := bstep (se 1 (by rfl) ⟨858884, by rfl⟩ : syracuseStep 1145179 = 1717769) B1717769
theorem B1145199 : Blo 1144635 1145199 := bstep (se 1 (by rfl) ⟨858899, by rfl⟩ : syracuseStep 1145199 = 1717799) B1717799
theorem B1145255 : Blo 1144635 1145255 := bstep (se 1 (by rfl) ⟨858941, by rfl⟩ : syracuseStep 1145255 = 1717883) B1717883
theorem B1145339 : Blo 1144635 1145339 := bstep (se 1 (by rfl) ⟨859004, by rfl⟩ : syracuseStep 1145339 = 1718009) B1718009
theorem B1145407 : Blo 1144635 1145407 := bstep (se 1 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 1145407 = 1718111) B1718111
theorem B1145415 : Blo 1144635 1145415 := bstep (se 1 (by rfl) ⟨859061, by rfl⟩ : syracuseStep 1145415 = 1718123) B1718123
theorem B1931897 : Blo 1144635 1931897 := bstep (se 2 (by rfl) ⟨724461, by rfl⟩ : syracuseStep 1931897 = 1448923) B1448923
theorem B2325113 : Blo 1144635 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B1931951 : Blo 1144635 1931951 := bstep (se 1 (by rfl) ⟨1448963, by rfl⟩ : syracuseStep 1931951 = 2897927) B2897927
theorem B1145567 : Blo 1144635 1145567 := bstep (se 1 (by rfl) ⟨859175, by rfl⟩ : syracuseStep 1145567 = 1718351) B1718351
theorem B1145647 : Blo 1144635 1145647 := bstep (se 1 (by rfl) ⟨859235, by rfl⟩ : syracuseStep 1145647 = 1718471) B1718471
theorem B1932187 : Blo 1144635 1932187 := bstep (se 1 (by rfl) ⟨1449140, by rfl⟩ : syracuseStep 1932187 = 2898281) B2898281
theorem B1145755 : Blo 1144635 1145755 := bstep (se 1 (by rfl) ⟨859316, by rfl⟩ : syracuseStep 1145755 = 1718633) B1718633
theorem B1145807 : Blo 1144635 1145807 := bstep (se 1 (by rfl) ⟨859355, by rfl⟩ : syracuseStep 1145807 = 1718711) B1718711
theorem B1145831 : Blo 1144635 1145831 := bstep (se 1 (by rfl) ⟨859373, by rfl⟩ : syracuseStep 1145831 = 1718747) B1718747
theorem B5798951 : Blo 1144635 5798951 := bstep (se 1 (by rfl) ⟨4349213, by rfl⟩ : syracuseStep 5798951 = 8698427) B8698427
theorem B1146143 : Blo 1144635 1146143 := bstep (se 1 (by rfl) ⟨859607, by rfl⟩ : syracuseStep 1146143 = 1719215) B1719215
theorem B1146203 : Blo 1144635 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B1146223 : Blo 1144635 1146223 := bstep (se 1 (by rfl) ⟨859667, by rfl⟩ : syracuseStep 1146223 = 1719335) B1719335
theorem B1146279 : Blo 1144635 1146279 := bstep (se 1 (by rfl) ⟨859709, by rfl⟩ : syracuseStep 1146279 = 1719419) B1719419
theorem B1146363 : Blo 1144635 1146363 := bstep (se 1 (by rfl) ⟨859772, by rfl⟩ : syracuseStep 1146363 = 1719545) B1719545
theorem B1146431 : Blo 1144635 1146431 := bstep (se 1 (by rfl) ⟨859823, by rfl⟩ : syracuseStep 1146431 = 1719647) B1719647
theorem B1146439 : Blo 1144635 1146439 := bstep (se 1 (by rfl) ⟨859829, by rfl⟩ : syracuseStep 1146439 = 1719659) B1719659
theorem B3669599 : Blo 1144635 3669599 := bstep (se 1 (by rfl) ⟨2752199, by rfl⟩ : syracuseStep 3669599 = 5504399) B5504399
theorem B4849267 : Blo 1144635 4849267 := bstep (se 1 (by rfl) ⟨3636950, by rfl⟩ : syracuseStep 4849267 = 7273901) B7273901
theorem B1146591 : Blo 1144635 1146591 := bstep (se 1 (by rfl) ⟨859943, by rfl⟩ : syracuseStep 1146591 = 1719887) B1719887
theorem B1146671 : Blo 1144635 1146671 := bstep (se 1 (by rfl) ⟨860003, by rfl⟩ : syracuseStep 1146671 = 1720007) B1720007
theorem B1146779 : Blo 1144635 1146779 := bstep (se 1 (by rfl) ⟨860084, by rfl⟩ : syracuseStep 1146779 = 1720169) B1720169
theorem B1146831 : Blo 1144635 1146831 := bstep (se 1 (by rfl) ⟨860123, by rfl⟩ : syracuseStep 1146831 = 1720247) B1720247
theorem B1146855 : Blo 1144635 1146855 := bstep (se 1 (by rfl) ⟨860141, by rfl⟩ : syracuseStep 1146855 = 1720283) B1720283
theorem B14712839 : Blo 1144635 14712839 := bstep (se 1 (by rfl) ⟨11034629, by rfl⟩ : syracuseStep 14712839 = 22069259) B22069259
theorem B3670049 : Blo 1144635 3670049 := bstep (se 2 (by rfl) ⟨1376268, by rfl⟩ : syracuseStep 3670049 = 2752537) B2752537
theorem B33063065 : Blo 1144635 33063065 := bstep (se 2 (by rfl) ⟨12398649, by rfl⟩ : syracuseStep 33063065 = 24797299) B24797299
theorem B1147111 : Blo 1144635 1147111 := bstep (se 1 (by rfl) ⟨860333, by rfl⟩ : syracuseStep 1147111 = 1720667) B1720667
theorem B4129049 : Blo 1144635 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B1147263 : Blo 1144635 1147263 := bstep (se 1 (by rfl) ⟨860447, by rfl⟩ : syracuseStep 1147263 = 1720895) B1720895
theorem B1147343 : Blo 1144635 1147343 := bstep (se 1 (by rfl) ⟨860507, by rfl⟩ : syracuseStep 1147343 = 1721015) B1721015
theorem B3867209 : Blo 1144635 3867209 := bstep (se 2 (by rfl) ⟨1450203, by rfl⟩ : syracuseStep 3867209 = 2900407) B2900407
theorem B1147495 : Blo 1144635 1147495 := bstep (se 1 (by rfl) ⟨860621, by rfl⟩ : syracuseStep 1147495 = 1721243) B1721243
theorem B2753153 : Blo 1144635 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B3867371 : Blo 1144635 3867371 := bstep (se 1 (by rfl) ⟨2900528, by rfl⟩ : syracuseStep 3867371 = 5801057) B5801057
theorem B1147759 : Blo 1144635 1147759 := bstep (se 1 (by rfl) ⟨860819, by rfl⟩ : syracuseStep 1147759 = 1721639) B1721639
theorem B13075343 : Blo 1144635 13075343 := bstep (se 1 (by rfl) ⟨9806507, by rfl⟩ : syracuseStep 13075343 = 19613015) B19613015
theorem B4359055 : Blo 1144635 4359055 := bstep (se 1 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 4359055 = 6538583) B6538583
theorem B1147815 : Blo 1144635 1147815 := bstep (se 1 (by rfl) ⟨860861, by rfl⟩ : syracuseStep 1147815 = 1721723) B1721723
theorem B13239287 : Blo 1144635 13239287 := bstep (se 1 (by rfl) ⟨9929465, by rfl⟩ : syracuseStep 13239287 = 19858931) B19858931
theorem B1147899 : Blo 1144635 1147899 := bstep (se 1 (by rfl) ⟨860924, by rfl⟩ : syracuseStep 1147899 = 1721849) B1721849
theorem B1147967 : Blo 1144635 1147967 := bstep (se 1 (by rfl) ⟨860975, by rfl⟩ : syracuseStep 1147967 = 1721951) B1721951
theorem B1934543 : Blo 1144635 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B1148111 : Blo 1144635 1148111 := bstep (se 1 (by rfl) ⟨861083, by rfl⟩ : syracuseStep 1148111 = 1722167) B1722167
theorem B5801219 : Blo 1144635 5801219 := bstep (se 1 (by rfl) ⟨4350914, by rfl⟩ : syracuseStep 5801219 = 8701829) B8701829
theorem B1148315 : Blo 1144635 1148315 := bstep (se 1 (by rfl) ⟨861236, by rfl⟩ : syracuseStep 1148315 = 1722473) B1722473
theorem B9799127 : Blo 1144635 9799127 := bstep (se 1 (by rfl) ⟨7349345, by rfl⟩ : syracuseStep 9799127 = 14698691) B14698691
theorem B1148527 : Blo 1144635 1148527 := bstep (se 1 (by rfl) ⟨861395, by rfl⟩ : syracuseStep 1148527 = 1722791) B1722791
theorem B1836665 : Blo 1144635 1836665 := bstep (se 2 (by rfl) ⟨688749, by rfl⟩ : syracuseStep 1836665 = 1377499) B1377499
theorem B1148583 : Blo 1144635 1148583 := bstep (se 1 (by rfl) ⟨861437, by rfl⟩ : syracuseStep 1148583 = 1722875) B1722875
theorem B6620957 : Blo 1144635 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B3671905 : Blo 1144635 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B1935353 : Blo 1144635 1935353 := bstep (se 2 (by rfl) ⟨725757, by rfl⟩ : syracuseStep 1935353 = 1451515) B1451515
theorem B150964235 : Blo 1144635 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B1935515 : Blo 1144635 1935515 := bstep (se 1 (by rfl) ⟨1451636, by rfl⟩ : syracuseStep 1935515 = 2903273) B2903273
theorem B1837247 : Blo 1144635 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B3868883 : Blo 1144635 3868883 := bstep (se 1 (by rfl) ⟨2901662, by rfl⟩ : syracuseStep 3868883 = 5803325) B5803325
theorem B1935623 : Blo 1144635 1935623 := bstep (se 1 (by rfl) ⟨1451717, by rfl⟩ : syracuseStep 1935623 = 2903435) B2903435
theorem B7342427 : Blo 1144635 7342427 := bstep (se 1 (by rfl) ⟨5506820, by rfl⟩ : syracuseStep 7342427 = 11013641) B11013641
theorem B6195649 : Blo 1144635 6195649 := bstep (se 2 (by rfl) ⟨2323368, by rfl⟩ : syracuseStep 6195649 = 4646737) B4646737
theorem B3869153 : Blo 1144635 3869153 := bstep (se 2 (by rfl) ⟨1450932, by rfl⟩ : syracuseStep 3869153 = 2901865) B2901865
theorem B1936183 : Blo 1144635 1936183 := bstep (se 1 (by rfl) ⟨1452137, by rfl⟩ : syracuseStep 1936183 = 2904275) B2904275
theorem B5802839 : Blo 1144635 5802839 := bstep (se 1 (by rfl) ⟨4352129, by rfl⟩ : syracuseStep 5802839 = 8704259) B8704259
theorem B13044725 : Blo 1144635 13044725 := bstep (se 5 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 13044725 = 1222943) B1222943
theorem B3673135 : Blo 1144635 3673135 := bstep (se 1 (by rfl) ⟨2754851, by rfl⟩ : syracuseStep 3673135 = 5509703) B5509703
theorem B5508319 : Blo 1144635 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B1936649 : Blo 1144635 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B6524185 : Blo 1144635 6524185 := bstep (se 2 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 6524185 = 4893139) B4893139
theorem B11308339 : Blo 1144635 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B1838567 : Blo 1144635 1838567 := bstep (se 1 (by rfl) ⟨1378925, by rfl⟩ : syracuseStep 1838567 = 2757851) B2757851
theorem B15896263 : Blo 1144635 15896263 := bstep (se 1 (by rfl) ⟨11922197, by rfl⟩ : syracuseStep 15896263 = 23844395) B23844395
theorem B6524711 : Blo 1144635 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B3870503 : Blo 1144635 3870503 := bstep (se 1 (by rfl) ⟨2902877, by rfl⟩ : syracuseStep 3870503 = 5805755) B5805755
theorem B1838971 : Blo 1144635 1838971 := bstep (se 1 (by rfl) ⟨1379228, by rfl⟩ : syracuseStep 1838971 = 2758457) B2758457
theorem B11767961 : Blo 1144635 11767961 := bstep (se 2 (by rfl) ⟨4412985, by rfl⟩ : syracuseStep 11767961 = 8825971) B8825971
theorem B31396025 : Blo 1144635 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B1741019 : Blo 1144635 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B1937695 : Blo 1144635 1937695 := bstep (se 1 (by rfl) ⟨1453271, by rfl⟩ : syracuseStep 1937695 = 2906543) B2906543
theorem B5509549 : Blo 1144635 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B16552583 : Blo 1144635 16552583 := bstep (se 1 (by rfl) ⟨12414437, by rfl⟩ : syracuseStep 16552583 = 24828875) B24828875
theorem B2069153 : Blo 1144635 2069153 := bstep (se 2 (by rfl) ⟨775932, by rfl⟩ : syracuseStep 2069153 = 1551865) B1551865
theorem B6525643 : Blo 1144635 6525643 := bstep (se 1 (by rfl) ⟨4894232, by rfl⟩ : syracuseStep 6525643 = 9788465) B9788465
theorem B3871529 : Blo 1144635 3871529 := bstep (se 2 (by rfl) ⟨1451823, by rfl⟩ : syracuseStep 3871529 = 2903647) B2903647
theorem B4133693 : Blo 1144635 4133693 := bstep (se 3 (by rfl) ⟨775067, by rfl⟩ : syracuseStep 4133693 = 1550135) B1550135
theorem B7836551 : Blo 1144635 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B3871799 : Blo 1144635 3871799 := bstep (se 1 (by rfl) ⟨2903849, by rfl⟩ : syracuseStep 3871799 = 5807699) B5807699
theorem B8820059 : Blo 1144635 8820059 := bstep (se 1 (by rfl) ⟨6615044, by rfl⟩ : syracuseStep 8820059 = 13230089) B13230089
theorem B8721755 : Blo 1144635 8721755 := bstep (se 1 (by rfl) ⟨6541316, by rfl⟩ : syracuseStep 8721755 = 13082633) B13082633
theorem B5805431 : Blo 1144635 5805431 := bstep (se 1 (by rfl) ⟨4354073, by rfl⟩ : syracuseStep 5805431 = 8708147) B8708147
theorem B2758043 : Blo 1144635 2758043 := bstep (se 1 (by rfl) ⟨2068532, by rfl⟩ : syracuseStep 2758043 = 4137065) B4137065
theorem B27924011 : Blo 1144635 27924011 := bstep (se 1 (by rfl) ⟨20943008, by rfl⟩ : syracuseStep 27924011 = 41886017) B41886017
theorem B2758639 : Blo 1144635 2758639 := bstep (se 1 (by rfl) ⟨2068979, by rfl⟩ : syracuseStep 2758639 = 4137959) B4137959
theorem B12392513 : Blo 1144635 12392513 := bstep (se 2 (by rfl) ⟨4647192, by rfl⟩ : syracuseStep 12392513 = 9294385) B9294385
theorem B5806241 : Blo 1144635 5806241 := bstep (se 2 (by rfl) ⟨2177340, by rfl⟩ : syracuseStep 5806241 = 4354681) B4354681
theorem B7346375 : Blo 1144635 7346375 := bstep (se 1 (by rfl) ⟨5509781, by rfl⟩ : syracuseStep 7346375 = 11019563) B11019563
theorem B6527375 : Blo 1144635 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B3873743 : Blo 1144635 3873743 := bstep (se 1 (by rfl) ⟨2905307, by rfl⟩ : syracuseStep 3873743 = 5810615) B5810615
theorem B12394063 : Blo 1144635 12394063 := bstep (se 1 (by rfl) ⟨9295547, by rfl⟩ : syracuseStep 12394063 = 18591095) B18591095
theorem B5808347 : Blo 1144635 5808347 := bstep (se 1 (by rfl) ⟨4356260, by rfl⟩ : syracuseStep 5808347 = 8712521) B8712521
theorem B5808509 : Blo 1144635 5808509 := bstep (se 3 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 5808509 = 2178191) B2178191
theorem B3875255 : Blo 1144635 3875255 := bstep (se 1 (by rfl) ⟨2906441, by rfl⟩ : syracuseStep 3875255 = 5812883) B5812883
theorem B3678671 : Blo 1144635 3678671 := bstep (se 1 (by rfl) ⟨2759003, by rfl⟩ : syracuseStep 3678671 = 5518007) B5518007
theorem B3875741 : Blo 1144635 3875741 := bstep (se 3 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 3875741 = 1453403) B1453403
theorem B3187667 : Blo 1144635 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B3875795 : Blo 1144635 3875795 := bstep (se 1 (by rfl) ⟨2906846, by rfl⟩ : syracuseStep 3875795 = 5813693) B5813693
theorem B1746127 : Blo 1144635 1746127 := bstep (se 1 (by rfl) ⟨1309595, by rfl⟩ : syracuseStep 1746127 = 2619191) B2619191
theorem B1287931 : Blo 1144635 1287931 := bstep (se 1 (by rfl) ⟨965948, by rfl⟩ : syracuseStep 1287931 = 1931897) B1931897
theorem B1550075 : Blo 1144635 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B1287967 : Blo 1144635 1287967 := bstep (se 1 (by rfl) ⟨965975, by rfl⟩ : syracuseStep 1287967 = 1931951) B1931951
theorem B1451839 : Blo 1144635 1451839 := bstep (se 1 (by rfl) ⟨1088879, by rfl⟩ : syracuseStep 1451839 = 2177759) B2177759
theorem B7350425 : Blo 1144635 7350425 := bstep (se 2 (by rfl) ⟨2756409, by rfl⟩ : syracuseStep 7350425 = 5512819) B5512819
theorem B6465689 : Blo 1144635 6465689 := bstep (se 2 (by rfl) ⟨2424633, by rfl⟩ : syracuseStep 6465689 = 4849267) B4849267
theorem B17673079 : Blo 1144635 17673079 := bstep (se 1 (by rfl) ⟨13254809, by rfl⟩ : syracuseStep 17673079 = 26509619) B26509619
theorem B1289119 : Blo 1144635 1289119 := bstep (se 1 (by rfl) ⟨966839, by rfl⟩ : syracuseStep 1289119 = 1933679) B1933679
theorem B1289263 : Blo 1144635 1289263 := bstep (se 1 (by rfl) ⟨966947, by rfl⟩ : syracuseStep 1289263 = 1933895) B1933895
theorem B1289551 : Blo 1144635 1289551 := bstep (se 1 (by rfl) ⟨967163, by rfl⟩ : syracuseStep 1289551 = 1934327) B1934327
theorem B2174455 : Blo 1144635 2174455 := bstep (se 1 (by rfl) ⟨1630841, by rfl⟩ : syracuseStep 2174455 = 3261683) B3261683
theorem B9940553 : Blo 1144635 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B2174759 : Blo 1144635 2174759 := bstep (se 1 (by rfl) ⟨1631069, by rfl⟩ : syracuseStep 2174759 = 3262139) B3262139
theorem B1290055 : Blo 1144635 1290055 := bstep (se 1 (by rfl) ⟨967541, by rfl⟩ : syracuseStep 1290055 = 1935083) B1935083
theorem B8695997 : Blo 1144635 8695997 := bstep (se 3 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 8695997 = 3260999) B3260999
theorem B4894985 : Blo 1144635 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B1290703 : Blo 1144635 1290703 := bstep (se 1 (by rfl) ⟨968027, by rfl⟩ : syracuseStep 1290703 = 1936055) B1936055
theorem B4895225 : Blo 1144635 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B1716971 : Blo 1144635 1716971 := bstep (se 1 (by rfl) ⟨1287728, by rfl⟩ : syracuseStep 1716971 = 2575457) B2575457
theorem B1717001 : Blo 1144635 1717001 := bstep (se 2 (by rfl) ⟨643875, by rfl⟩ : syracuseStep 1717001 = 1287751) B1287751
theorem B1717103 : Blo 1144635 1717103 := bstep (se 1 (by rfl) ⟨1287827, by rfl⟩ : syracuseStep 1717103 = 2575655) B2575655
theorem B1225639 : Blo 1144635 1225639 := bstep (se 1 (by rfl) ⟨919229, by rfl⟩ : syracuseStep 1225639 = 1838459) B1838459
theorem B1717355 : Blo 1144635 1717355 := bstep (se 1 (by rfl) ⟨1288016, by rfl⟩ : syracuseStep 1717355 = 2576033) B2576033
theorem B11023559 : Blo 1144635 11023559 := bstep (se 1 (by rfl) ⟨8267669, by rfl⟩ : syracuseStep 11023559 = 16535339) B16535339
theorem B1717595 : Blo 1144635 1717595 := bstep (se 1 (by rfl) ⟨1288196, by rfl⟩ : syracuseStep 1717595 = 2576393) B2576393
theorem B1291675 : Blo 1144635 1291675 := bstep (se 1 (by rfl) ⟨968756, by rfl⟩ : syracuseStep 1291675 = 1937513) B1937513
theorem B6534665 : Blo 1144635 6534665 := bstep (se 2 (by rfl) ⟨2450499, by rfl⟩ : syracuseStep 6534665 = 4900999) B4900999
theorem B1717871 : Blo 1144635 1717871 := bstep (se 1 (by rfl) ⟨1288403, by rfl⟩ : syracuseStep 1717871 = 2576807) B2576807
theorem B1717943 : Blo 1144635 1717943 := bstep (se 1 (by rfl) ⟨1288457, by rfl⟩ : syracuseStep 1717943 = 2576915) B2576915
theorem B1717979 : Blo 1144635 1717979 := bstep (se 1 (by rfl) ⟨1288484, by rfl⟩ : syracuseStep 1717979 = 2576969) B2576969
theorem B1226459 : Blo 1144635 1226459 := bstep (se 1 (by rfl) ⟨919844, by rfl⟩ : syracuseStep 1226459 = 1839689) B1839689
theorem B1652447 : Blo 1144635 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B8271679 : Blo 1144635 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B1718153 : Blo 1144635 1718153 := bstep (se 2 (by rfl) ⟨644307, by rfl⟩ : syracuseStep 1718153 = 1288615) B1288615
theorem B1718255 : Blo 1144635 1718255 := bstep (se 1 (by rfl) ⟨1288691, by rfl⟩ : syracuseStep 1718255 = 2577383) B2577383
theorem B3094625 : Blo 1144635 3094625 := bstep (se 2 (by rfl) ⟨1160484, by rfl⟩ : syracuseStep 3094625 = 2320969) B2320969
theorem B2898119 : Blo 1144635 2898119 := bstep (se 1 (by rfl) ⟨2173589, by rfl⟩ : syracuseStep 2898119 = 4347179) B4347179
theorem B1718507 : Blo 1144635 1718507 := bstep (se 1 (by rfl) ⟨1288880, by rfl⟩ : syracuseStep 1718507 = 2577761) B2577761
theorem B5519623 : Blo 1144635 5519623 := bstep (se 1 (by rfl) ⟨4139717, by rfl⟩ : syracuseStep 5519623 = 8279435) B8279435
theorem B1718567 : Blo 1144635 1718567 := bstep (se 1 (by rfl) ⟨1288925, by rfl⟩ : syracuseStep 1718567 = 2577851) B2577851
theorem B1718651 : Blo 1144635 1718651 := bstep (se 1 (by rfl) ⟨1288988, by rfl⟩ : syracuseStep 1718651 = 2577977) B2577977
theorem B6535667 : Blo 1144635 6535667 := bstep (se 1 (by rfl) ⟨4901750, by rfl⟩ : syracuseStep 6535667 = 9803501) B9803501
theorem B6961787 : Blo 1144635 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B1718921 : Blo 1144635 1718921 := bstep (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) B1289191
theorem B1719095 : Blo 1144635 1719095 := bstep (se 1 (by rfl) ⟨1289321, by rfl⟩ : syracuseStep 1719095 = 2578643) B2578643
theorem B1719131 : Blo 1144635 1719131 := bstep (se 1 (by rfl) ⟨1289348, by rfl⟩ : syracuseStep 1719131 = 2578697) B2578697
theorem B15678359 : Blo 1144635 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B1719275 : Blo 1144635 1719275 := bstep (se 1 (by rfl) ⟨1289456, by rfl⟩ : syracuseStep 1719275 = 2578913) B2578913
theorem B7355549 : Blo 1144635 7355549 := bstep (se 3 (by rfl) ⟨1379165, by rfl⟩ : syracuseStep 7355549 = 2758331) B2758331
theorem B1719479 : Blo 1144635 1719479 := bstep (se 1 (by rfl) ⟨1289609, by rfl⟩ : syracuseStep 1719479 = 2579219) B2579219
theorem B6536375 : Blo 1144635 6536375 := bstep (se 1 (by rfl) ⟨4902281, by rfl⟩ : syracuseStep 6536375 = 9804563) B9804563
theorem B1719719 : Blo 1144635 1719719 := bstep (se 1 (by rfl) ⟨1289789, by rfl⟩ : syracuseStep 1719719 = 2579579) B2579579
theorem B1719803 : Blo 1144635 1719803 := bstep (se 1 (by rfl) ⟨1289852, by rfl⟩ : syracuseStep 1719803 = 2579705) B2579705
theorem B8699399 : Blo 1144635 8699399 := bstep (se 1 (by rfl) ⟨6524549, by rfl⟩ : syracuseStep 8699399 = 13049099) B13049099
theorem B2899547 : Blo 1144635 2899547 := bstep (se 1 (by rfl) ⟨2174660, by rfl⟩ : syracuseStep 2899547 = 4349321) B4349321
theorem B1719899 : Blo 1144635 1719899 := bstep (se 1 (by rfl) ⟨1289924, by rfl⟩ : syracuseStep 1719899 = 2579849) B2579849
theorem B1719983 : Blo 1144635 1719983 := bstep (se 1 (by rfl) ⟨1289987, by rfl⟩ : syracuseStep 1719983 = 2579975) B2579975
theorem B1720103 : Blo 1144635 1720103 := bstep (se 1 (by rfl) ⟨1290077, by rfl⟩ : syracuseStep 1720103 = 2580155) B2580155
theorem B4964183 : Blo 1144635 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B1720187 : Blo 1144635 1720187 := bstep (se 1 (by rfl) ⟨1290140, by rfl⟩ : syracuseStep 1720187 = 2580281) B2580281
theorem B1720607 : Blo 1144635 1720607 := bstep (se 1 (by rfl) ⟨1290455, by rfl⟩ : syracuseStep 1720607 = 2580911) B2580911
theorem B1720631 : Blo 1144635 1720631 := bstep (se 1 (by rfl) ⟨1290473, by rfl⟩ : syracuseStep 1720631 = 2580947) B2580947
theorem B1720703 : Blo 1144635 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B1720775 : Blo 1144635 1720775 := bstep (se 1 (by rfl) ⟨1290581, by rfl⟩ : syracuseStep 1720775 = 2581163) B2581163
theorem B1721129 : Blo 1144635 1721129 := bstep (se 2 (by rfl) ⟨645423, by rfl⟩ : syracuseStep 1721129 = 1290847) B1290847
theorem B1721135 : Blo 1144635 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B1721255 : Blo 1144635 1721255 := bstep (se 1 (by rfl) ⟨1290941, by rfl⟩ : syracuseStep 1721255 = 2581883) B2581883
theorem B1721339 : Blo 1144635 1721339 := bstep (se 1 (by rfl) ⟨1291004, by rfl⟩ : syracuseStep 1721339 = 2582009) B2582009
theorem B1721399 : Blo 1144635 1721399 := bstep (se 1 (by rfl) ⟨1291049, by rfl⟩ : syracuseStep 1721399 = 2582099) B2582099
theorem B1721519 : Blo 1144635 1721519 := bstep (se 1 (by rfl) ⟨1291139, by rfl⟩ : syracuseStep 1721519 = 2582279) B2582279
theorem B1721927 : Blo 1144635 1721927 := bstep (se 1 (by rfl) ⟨1291445, by rfl⟩ : syracuseStep 1721927 = 2582891) B2582891
theorem B3098279 : Blo 1144635 3098279 := bstep (se 1 (by rfl) ⟨2323709, by rfl⟩ : syracuseStep 3098279 = 4647419) B4647419
theorem B1722023 : Blo 1144635 1722023 := bstep (se 1 (by rfl) ⟨1291517, by rfl⟩ : syracuseStep 1722023 = 2583035) B2583035
theorem B1722107 : Blo 1144635 1722107 := bstep (se 1 (by rfl) ⟨1291580, by rfl⟩ : syracuseStep 1722107 = 2583161) B2583161
theorem B1722143 : Blo 1144635 1722143 := bstep (se 1 (by rfl) ⟨1291607, by rfl⟩ : syracuseStep 1722143 = 2583215) B2583215
theorem B1722191 : Blo 1144635 1722191 := bstep (se 1 (by rfl) ⟨1291643, by rfl⟩ : syracuseStep 1722191 = 2583287) B2583287
theorem B1722311 : Blo 1144635 1722311 := bstep (se 1 (by rfl) ⟨1291733, by rfl⟩ : syracuseStep 1722311 = 2583467) B2583467
theorem B2902007 : Blo 1144635 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B8276087 : Blo 1144635 8276087 := bstep (se 1 (by rfl) ⟨6207065, by rfl⟩ : syracuseStep 8276087 = 12414131) B12414131
theorem B1722665 : Blo 1144635 1722665 := bstep (se 2 (by rfl) ⟨645999, by rfl⟩ : syracuseStep 1722665 = 1291999) B1291999
theorem B1722671 : Blo 1144635 1722671 := bstep (se 1 (by rfl) ⟨1292003, by rfl⟩ : syracuseStep 1722671 = 2584007) B2584007
theorem B1722911 : Blo 1144635 1722911 := bstep (se 1 (by rfl) ⟨1292183, by rfl⟩ : syracuseStep 1722911 = 2584367) B2584367
theorem B2903161 : Blo 1144635 2903161 := bstep (se 2 (by rfl) ⟨1088685, by rfl⟩ : syracuseStep 2903161 = 2177371) B2177371
theorem B2575583 : Blo 1144635 2575583 := bstep (se 1 (by rfl) ⟨1931687, by rfl⟩ : syracuseStep 2575583 = 3863375) B3863375
theorem B2903465 : Blo 1144635 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B2575799 : Blo 1144635 2575799 := bstep (se 1 (by rfl) ⟨1931849, by rfl⟩ : syracuseStep 2575799 = 3863699) B3863699
theorem B2575979 : Blo 1144635 2575979 := bstep (se 1 (by rfl) ⟨1931984, by rfl⟩ : syracuseStep 2575979 = 3863969) B3863969
theorem B45239915 : Blo 1144635 45239915 := bstep (se 1 (by rfl) ⟨33929936, by rfl⟩ : syracuseStep 45239915 = 67859873) B67859873
theorem B2576249 : Blo 1144635 2576249 := bstep (se 2 (by rfl) ⟨966093, by rfl⟩ : syracuseStep 2576249 = 1932187) B1932187
theorem B2903951 : Blo 1144635 2903951 := bstep (se 1 (by rfl) ⟨2177963, by rfl⟩ : syracuseStep 2903951 = 4355927) B4355927
theorem B6541499 : Blo 1144635 6541499 := bstep (se 1 (by rfl) ⟨4906124, by rfl⟩ : syracuseStep 6541499 = 9812249) B9812249
theorem B2904457 : Blo 1144635 2904457 := bstep (se 2 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 2904457 = 2178343) B2178343
theorem B2904569 : Blo 1144635 2904569 := bstep (se 2 (by rfl) ⟨1089213, by rfl⟩ : syracuseStep 2904569 = 2178427) B2178427
theorem B4706977 : Blo 1144635 4706977 := bstep (se 2 (by rfl) ⟨1765116, by rfl⟩ : syracuseStep 4706977 = 3530233) B3530233
theorem B13226861 : Blo 1144635 13226861 := bstep (se 3 (by rfl) ⟨2480036, by rfl⟩ : syracuseStep 13226861 = 4960073) B4960073
theorem B2446399 : Blo 1144635 2446399 := bstep (se 1 (by rfl) ⟨1834799, by rfl⟩ : syracuseStep 2446399 = 3669599) B3669599
theorem B3724499 : Blo 1144635 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B2578103 : Blo 1144635 2578103 := bstep (se 1 (by rfl) ⟨1933577, by rfl⟩ : syracuseStep 2578103 = 3867155) B3867155
theorem B4347863 : Blo 1144635 4347863 := bstep (se 1 (by rfl) ⟨3260897, by rfl⟩ : syracuseStep 4347863 = 6521795) B6521795
theorem B8706203 : Blo 1144635 8706203 := bstep (se 1 (by rfl) ⟨6529652, by rfl⟩ : syracuseStep 8706203 = 13059305) B13059305
theorem B4348349 : Blo 1144635 4348349 := bstep (se 3 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 4348349 = 1630631) B1630631
theorem B2939449 : Blo 1144635 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B2579291 : Blo 1144635 2579291 := bstep (se 1 (by rfl) ⟨1934468, by rfl⟩ : syracuseStep 2579291 = 3868937) B3868937
theorem B6970493 : Blo 1144635 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B4906109 : Blo 1144635 4906109 := bstep (se 3 (by rfl) ⟨919895, by rfl⟩ : syracuseStep 4906109 = 1839791) B1839791
theorem B19881163 : Blo 1144635 19881163 := bstep (se 1 (by rfl) ⟨14910872, by rfl⟩ : syracuseStep 19881163 = 29821745) B29821745
theorem B2580047 : Blo 1144635 2580047 := bstep (se 1 (by rfl) ⟨1935035, by rfl⟩ : syracuseStep 2580047 = 3870071) B3870071
theorem B2580767 : Blo 1144635 2580767 := bstep (se 1 (by rfl) ⟨1935575, by rfl⟩ : syracuseStep 2580767 = 3871151) B3871151
theorem B2941417 : Blo 1144635 2941417 := bstep (se 2 (by rfl) ⟨1103031, by rfl⟩ : syracuseStep 2941417 = 2206063) B2206063
theorem B9790105 : Blo 1144635 9790105 := bstep (se 2 (by rfl) ⟨3671289, by rfl⟩ : syracuseStep 9790105 = 7342579) B7342579
theorem B22307633 : Blo 1144635 22307633 := bstep (se 2 (by rfl) ⟨8365362, by rfl⟩ : syracuseStep 22307633 = 16730725) B16730725
theorem B2581415 : Blo 1144635 2581415 := bstep (se 1 (by rfl) ⟨1936061, by rfl⟩ : syracuseStep 2581415 = 3872123) B3872123
theorem B67036301 : Blo 1144635 67036301 := bstep (se 3 (by rfl) ⟨12569306, by rfl⟩ : syracuseStep 67036301 = 25138613) B25138613
theorem B16541101 : Blo 1144635 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B14673473 : Blo 1144635 14673473 := bstep (se 2 (by rfl) ⟨5502552, by rfl⟩ : syracuseStep 14673473 = 11005105) B11005105
theorem B4351751 : Blo 1144635 4351751 := bstep (se 1 (by rfl) ⟨3263813, by rfl⟩ : syracuseStep 4351751 = 6527627) B6527627
theorem B3270431 : Blo 1144635 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B2582351 : Blo 1144635 2582351 := bstep (se 1 (by rfl) ⟨1936763, by rfl⟩ : syracuseStep 2582351 = 3873527) B3873527
theorem B2582369 : Blo 1144635 2582369 := bstep (se 2 (by rfl) ⟨968388, by rfl⟩ : syracuseStep 2582369 = 1936777) B1936777
theorem B74279267 : Blo 1144635 74279267 := bstep (se 1 (by rfl) ⟨55709450, by rfl⟩ : syracuseStep 74279267 = 111418901) B111418901
theorem B2582945 : Blo 1144635 2582945 := bstep (se 2 (by rfl) ⟨968604, by rfl⟩ : syracuseStep 2582945 = 1937209) B1937209
theorem B2583071 : Blo 1144635 2583071 := bstep (se 1 (by rfl) ⟨1937303, by rfl⟩ : syracuseStep 2583071 = 3874607) B3874607
theorem B4648033 : Blo 1144635 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B6974585 : Blo 1144635 6974585 := bstep (se 2 (by rfl) ⟨2615469, by rfl⟩ : syracuseStep 6974585 = 5230939) B5230939
theorem B3828959 : Blo 1144635 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B4353527 : Blo 1144635 4353527 := bstep (se 1 (by rfl) ⟨3265145, by rfl⟩ : syracuseStep 4353527 = 6530291) B6530291
theorem B5796035 : Blo 1144635 5796035 := bstep (se 1 (by rfl) ⟨4347026, by rfl⟩ : syracuseStep 5796035 = 8694053) B8694053
theorem B3928457 : Blo 1144635 3928457 := bstep (se 2 (by rfl) ⟨1473171, by rfl⟩ : syracuseStep 3928457 = 2946343) B2946343
theorem B3863321 : Blo 1144635 3863321 := bstep (se 2 (by rfl) ⟨1448745, by rfl⟩ : syracuseStep 3863321 = 2897491) B2897491
theorem B1635113 : Blo 1144635 1635113 := bstep (se 2 (by rfl) ⟨613167, by rfl⟩ : syracuseStep 1635113 = 1226335) B1226335
theorem B1864615 : Blo 1144635 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B1766395 : Blo 1144635 1766395 := bstep (se 1 (by rfl) ⟨1324796, by rfl⟩ : syracuseStep 1766395 = 2649593) B2649593
theorem B3863591 : Blo 1144635 3863591 := bstep (se 1 (by rfl) ⟨2897693, by rfl⟩ : syracuseStep 3863591 = 5795387) B5795387
theorem B3929143 : Blo 1144635 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B3667319 : Blo 1144635 3667319 := bstep (se 1 (by rfl) ⟨2750489, by rfl⟩ : syracuseStep 3667319 = 5500979) B5500979
theorem B15103361 : Blo 1144635 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B16742123 : Blo 1144635 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B8713979 : Blo 1144635 8713979 := bstep (se 1 (by rfl) ⟨6535484, by rfl⟩ : syracuseStep 8713979 = 13070969) B13070969
theorem B4126511 : Blo 1144635 4126511 := bstep (se 1 (by rfl) ⟨3094883, by rfl⟩ : syracuseStep 4126511 = 6189767) B6189767
theorem B1144639 : Blo 1144635 1144639 := bstep (se 1 (by rfl) ⟨858479, by rfl⟩ : syracuseStep 1144639 = 1716959) B1716959
theorem B1144815 : Blo 1144635 1144815 := bstep (se 1 (by rfl) ⟨858611, by rfl⟩ : syracuseStep 1144815 = 1717223) B1717223
theorem B19560527 : Blo 1144635 19560527 := bstep (se 1 (by rfl) ⟨14670395, by rfl⟩ : syracuseStep 19560527 = 29340791) B29340791
theorem B3864671 : Blo 1144635 3864671 := bstep (se 1 (by rfl) ⟨2898503, by rfl⟩ : syracuseStep 3864671 = 5797007) B5797007
theorem B1144987 : Blo 1144635 1144987 := bstep (se 1 (by rfl) ⟨858740, by rfl⟩ : syracuseStep 1144987 = 1717481) B1717481
theorem B1145023 : Blo 1144635 1145023 := bstep (se 1 (by rfl) ⟨858767, by rfl⟩ : syracuseStep 1145023 = 1717535) B1717535
theorem B3668267 : Blo 1144635 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B1145135 : Blo 1144635 1145135 := bstep (se 1 (by rfl) ⟨858851, by rfl⟩ : syracuseStep 1145135 = 1717703) B1717703
theorem B1145371 : Blo 1144635 1145371 := bstep (se 1 (by rfl) ⟨859028, by rfl⟩ : syracuseStep 1145371 = 1718057) B1718057
theorem B1145375 : Blo 1144635 1145375 := bstep (se 1 (by rfl) ⟨859031, by rfl⟩ : syracuseStep 1145375 = 1718063) B1718063
theorem B8714951 : Blo 1144635 8714951 := bstep (se 1 (by rfl) ⟨6536213, by rfl⟩ : syracuseStep 8714951 = 13072427) B13072427
theorem B3865427 : Blo 1144635 3865427 := bstep (se 1 (by rfl) ⟨2899070, by rfl⟩ : syracuseStep 3865427 = 5798141) B5798141
theorem B1145691 : Blo 1144635 1145691 := bstep (se 1 (by rfl) ⟨859268, by rfl⟩ : syracuseStep 1145691 = 1718537) B1718537
theorem B1145759 : Blo 1144635 1145759 := bstep (se 1 (by rfl) ⟨859319, by rfl⟩ : syracuseStep 1145759 = 1718639) B1718639
theorem B1932329 : Blo 1144635 1932329 := bstep (se 2 (by rfl) ⟨724623, by rfl⟩ : syracuseStep 1932329 = 1449247) B1449247
theorem B1145903 : Blo 1144635 1145903 := bstep (se 1 (by rfl) ⟨859427, by rfl⟩ : syracuseStep 1145903 = 1718855) B1718855
theorem B1145927 : Blo 1144635 1145927 := bstep (se 1 (by rfl) ⟨859445, by rfl⟩ : syracuseStep 1145927 = 1718891) B1718891
theorem B1932511 : Blo 1144635 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B1146079 : Blo 1144635 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B4357385 : Blo 1144635 4357385 := bstep (se 2 (by rfl) ⟨1634019, by rfl⟩ : syracuseStep 4357385 = 3268039) B3268039
theorem B4357415 : Blo 1144635 4357415 := bstep (se 1 (by rfl) ⟨3268061, by rfl⟩ : syracuseStep 4357415 = 6536123) B6536123
theorem B3865967 : Blo 1144635 3865967 := bstep (se 1 (by rfl) ⟨2899475, by rfl⟩ : syracuseStep 3865967 = 5798951) B5798951
theorem B1146343 : Blo 1144635 1146343 := bstep (se 1 (by rfl) ⟨859757, by rfl⟩ : syracuseStep 1146343 = 1719515) B1719515
theorem B1146459 : Blo 1144635 1146459 := bstep (se 1 (by rfl) ⟨859844, by rfl⟩ : syracuseStep 1146459 = 1719689) B1719689
theorem B1932943 : Blo 1144635 1932943 := bstep (se 1 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 1932943 = 2899415) B2899415
theorem B3866345 : Blo 1144635 3866345 := bstep (se 2 (by rfl) ⟨1449879, by rfl⟩ : syracuseStep 3866345 = 2899759) B2899759
theorem B1146695 : Blo 1144635 1146695 := bstep (se 1 (by rfl) ⟨860021, by rfl⟩ : syracuseStep 1146695 = 1720043) B1720043
theorem B2064251 : Blo 1144635 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B1146847 : Blo 1144635 1146847 := bstep (se 1 (by rfl) ⟨860135, by rfl⟩ : syracuseStep 1146847 = 1720271) B1720271
theorem B2752699 : Blo 1144635 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B1147071 : Blo 1144635 1147071 := bstep (se 1 (by rfl) ⟨860303, by rfl⟩ : syracuseStep 1147071 = 1720607) B1720607
theorem B1147087 : Blo 1144635 1147087 := bstep (se 1 (by rfl) ⟨860315, by rfl⟩ : syracuseStep 1147087 = 1720631) B1720631
theorem B1147135 : Blo 1144635 1147135 := bstep (se 1 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 1147135 = 1720703) B1720703
theorem B1147183 : Blo 1144635 1147183 := bstep (se 1 (by rfl) ⟨860387, by rfl⟩ : syracuseStep 1147183 = 1720775) B1720775
theorem B1835435 : Blo 1144635 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B1147419 : Blo 1144635 1147419 := bstep (se 1 (by rfl) ⟨860564, by rfl⟩ : syracuseStep 1147419 = 1721129) B1721129
theorem B1147423 : Blo 1144635 1147423 := bstep (se 1 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 1147423 = 1721135) B1721135
theorem B8716895 : Blo 1144635 8716895 := bstep (se 1 (by rfl) ⟨6537671, by rfl⟩ : syracuseStep 8716895 = 13075343) B13075343
theorem B1147503 : Blo 1144635 1147503 := bstep (se 1 (by rfl) ⟨860627, by rfl⟩ : syracuseStep 1147503 = 1721255) B1721255
theorem B1147559 : Blo 1144635 1147559 := bstep (se 1 (by rfl) ⟨860669, by rfl⟩ : syracuseStep 1147559 = 1721339) B1721339
theorem B1147599 : Blo 1144635 1147599 := bstep (se 1 (by rfl) ⟨860699, by rfl⟩ : syracuseStep 1147599 = 1721399) B1721399
theorem B1147679 : Blo 1144635 1147679 := bstep (se 1 (by rfl) ⟨860759, by rfl⟩ : syracuseStep 1147679 = 1721519) B1721519
theorem B3867479 : Blo 1144635 3867479 := bstep (se 1 (by rfl) ⟨2900609, by rfl⟩ : syracuseStep 3867479 = 5801219) B5801219
theorem B1147951 : Blo 1144635 1147951 := bstep (se 1 (by rfl) ⟨860963, by rfl⟩ : syracuseStep 1147951 = 1721927) B1721927
theorem B2065519 : Blo 1144635 2065519 := bstep (se 1 (by rfl) ⟨1549139, by rfl⟩ : syracuseStep 2065519 = 3098279) B3098279
theorem B1148015 : Blo 1144635 1148015 := bstep (se 1 (by rfl) ⟨861011, by rfl⟩ : syracuseStep 1148015 = 1722023) B1722023
theorem B1148071 : Blo 1144635 1148071 := bstep (se 1 (by rfl) ⟨861053, by rfl⟩ : syracuseStep 1148071 = 1722107) B1722107
theorem B1148095 : Blo 1144635 1148095 := bstep (se 1 (by rfl) ⟨861071, by rfl⟩ : syracuseStep 1148095 = 1722143) B1722143
theorem B1148127 : Blo 1144635 1148127 := bstep (se 1 (by rfl) ⟨861095, by rfl⟩ : syracuseStep 1148127 = 1722191) B1722191
theorem B1148207 : Blo 1144635 1148207 := bstep (se 1 (by rfl) ⟨861155, by rfl⟩ : syracuseStep 1148207 = 1722311) B1722311
theorem B1934671 : Blo 1144635 1934671 := bstep (se 1 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 1934671 = 2902007) B2902007
theorem B1148443 : Blo 1144635 1148443 := bstep (se 1 (by rfl) ⟨861332, by rfl⟩ : syracuseStep 1148443 = 1722665) B1722665
theorem B1148447 : Blo 1144635 1148447 := bstep (se 1 (by rfl) ⟨861335, by rfl⟩ : syracuseStep 1148447 = 1722671) B1722671
theorem B2328169 : Blo 1144635 2328169 := bstep (se 2 (by rfl) ⟨873063, by rfl⟩ : syracuseStep 2328169 = 1746127) B1746127
theorem B1148607 : Blo 1144635 1148607 := bstep (se 1 (by rfl) ⟨861455, by rfl⟩ : syracuseStep 1148607 = 1722911) B1722911
theorem B3868559 : Blo 1144635 3868559 := bstep (se 1 (by rfl) ⟨2901419, by rfl⟩ : syracuseStep 3868559 = 5802839) B5802839
theorem B22054801 : Blo 1144635 22054801 := bstep (se 2 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 22054801 = 16541101) B16541101
theorem B4360301 : Blo 1144635 4360301 := bstep (se 3 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 4360301 = 1635113) B1635113
theorem B1935643 : Blo 1144635 1935643 := bstep (se 1 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 1935643 = 2903465) B2903465
theorem B1935785 : Blo 1144635 1935785 := bstep (se 2 (by rfl) ⟨725919, by rfl⟩ : syracuseStep 1935785 = 1451839) B1451839
theorem B1935967 : Blo 1144635 1935967 := bstep (se 1 (by rfl) ⟨1451975, by rfl⟩ : syracuseStep 1935967 = 2903951) B2903951
theorem B4360999 : Blo 1144635 4360999 := bstep (se 1 (by rfl) ⟨3270749, by rfl⟩ : syracuseStep 4360999 = 6541499) B6541499
theorem B1936379 : Blo 1144635 1936379 := bstep (se 1 (by rfl) ⟨1452284, by rfl⟩ : syracuseStep 1936379 = 2904569) B2904569
theorem B1379435 : Blo 1144635 1379435 := bstep (se 1 (by rfl) ⟨1034576, by rfl⟩ : syracuseStep 1379435 = 2069153) B2069153
theorem B2755795 : Blo 1144635 2755795 := bstep (se 1 (by rfl) ⟨2066846, by rfl⟩ : syracuseStep 2755795 = 4133693) B4133693
theorem B9931997 : Blo 1144635 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B8260865 : Blo 1144635 8260865 := bstep (se 2 (by rfl) ⟨3097824, by rfl⟩ : syracuseStep 8260865 = 6195649) B6195649
theorem B3870287 : Blo 1144635 3870287 := bstep (se 1 (by rfl) ⟨2902715, by rfl⟩ : syracuseStep 3870287 = 5805431) B5805431
theorem B1838695 : Blo 1144635 1838695 := bstep (se 1 (by rfl) ⟨1379021, by rfl⟩ : syracuseStep 1838695 = 2758043) B2758043
theorem B94080629 : Blo 1144635 94080629 := bstep (se 5 (by rfl) ⟨4410029, by rfl⟩ : syracuseStep 94080629 = 8820059) B8820059
theorem B18616007 : Blo 1144635 18616007 := bstep (se 1 (by rfl) ⟨13962005, by rfl⟩ : syracuseStep 18616007 = 27924011) B27924011
theorem B23564105 : Blo 1144635 23564105 := bstep (se 2 (by rfl) ⟨8836539, by rfl⟩ : syracuseStep 23564105 = 17673079) B17673079
theorem B8261675 : Blo 1144635 8261675 := bstep (se 1 (by rfl) ⟨6196256, by rfl⟩ : syracuseStep 8261675 = 12392513) B12392513
theorem B5804135 : Blo 1144635 5804135 := bstep (se 1 (by rfl) ⟨4353101, by rfl⟩ : syracuseStep 5804135 = 8706203) B8706203
theorem B3870827 : Blo 1144635 3870827 := bstep (se 1 (by rfl) ⟨2903120, by rfl⟩ : syracuseStep 3870827 = 5806241) B5806241
theorem B3870881 : Blo 1144635 3870881 := bstep (se 2 (by rfl) ⟨1451580, by rfl⟩ : syracuseStep 3870881 = 2903161) B2903161
theorem B7344425 : Blo 1144635 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B4133533 : Blo 1144635 4133533 := bstep (se 3 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 4133533 = 1550075) B1550075
theorem B3872231 : Blo 1144635 3872231 := bstep (se 1 (by rfl) ⟨2904173, by rfl⟩ : syracuseStep 3872231 = 5808347) B5808347
theorem B3872339 : Blo 1144635 3872339 := bstep (se 1 (by rfl) ⟨2904254, by rfl⟩ : syracuseStep 3872339 = 5808509) B5808509
theorem B3872609 : Blo 1144635 3872609 := bstep (se 2 (by rfl) ⟨1452228, by rfl⟩ : syracuseStep 3872609 = 2904457) B2904457
theorem B7346065 : Blo 1144635 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B49519511 : Blo 1144635 49519511 := bstep (se 1 (by rfl) ⟨37139633, by rfl⟩ : syracuseStep 49519511 = 74279267) B74279267
theorem B6627035 : Blo 1144635 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B1449839 : Blo 1144635 1449839 := bstep (se 1 (by rfl) ⟨1087379, by rfl⟩ : syracuseStep 1449839 = 2174759) B2174759
theorem B3678185 : Blo 1144635 3678185 := bstep (se 2 (by rfl) ⟨1379319, by rfl⟩ : syracuseStep 3678185 = 2758639) B2758639
theorem B18587981 : Blo 1144635 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B7349039 : Blo 1144635 7349039 := bstep (se 1 (by rfl) ⟨5511779, by rfl⟩ : syracuseStep 7349039 = 11023559) B11023559
theorem B10068907 : Blo 1144635 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B5809319 : Blo 1144635 5809319 := bstep (se 1 (by rfl) ⟨4356989, by rfl⟩ : syracuseStep 5809319 = 8713979) B8713979
theorem B5809967 : Blo 1144635 5809967 := bstep (se 1 (by rfl) ⟨4357475, by rfl⟩ : syracuseStep 5809967 = 8714951) B8714951
theorem B1288219 : Blo 1144635 1288219 := bstep (se 1 (by rfl) ⟨966164, by rfl⟩ : syracuseStep 1288219 = 1932329) B1932329
theorem B16525417 : Blo 1144635 16525417 := bstep (se 2 (by rfl) ⟨6197031, by rfl⟩ : syracuseStep 16525417 = 12394063) B12394063
theorem B9808559 : Blo 1144635 9808559 := bstep (se 1 (by rfl) ⟨7356419, by rfl⟩ : syracuseStep 9808559 = 14712839) B14712839
theorem B8826191 : Blo 1144635 8826191 := bstep (se 1 (by rfl) ⟨6619643, by rfl⟩ : syracuseStep 8826191 = 13239287) B13239287
theorem B1289695 : Blo 1144635 1289695 := bstep (se 1 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 1289695 = 1934543) B1934543
theorem B13053473 : Blo 1144635 13053473 := bstep (se 2 (by rfl) ⟨4895052, by rfl⟩ : syracuseStep 13053473 = 9790105) B9790105
theorem B6532751 : Blo 1144635 6532751 := bstep (se 1 (by rfl) ⟨4899563, by rfl⟩ : syracuseStep 6532751 = 9799127) B9799127
theorem B1224443 : Blo 1144635 1224443 := bstep (se 1 (by rfl) ⟨918332, by rfl⟩ : syracuseStep 1224443 = 1836665) B1836665
theorem B5812073 : Blo 1144635 5812073 := bstep (se 2 (by rfl) ⟨2179527, by rfl⟩ : syracuseStep 5812073 = 4359055) B4359055
theorem B1290235 : Blo 1144635 1290235 := bstep (se 1 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 1290235 = 1935353) B1935353
theorem B100642823 : Blo 1144635 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B5517391 : Blo 1144635 5517391 := bstep (se 1 (by rfl) ⟨4138043, by rfl⟩ : syracuseStep 5517391 = 8276087) B8276087
theorem B1290343 : Blo 1144635 1290343 := bstep (se 1 (by rfl) ⟨967757, by rfl⟩ : syracuseStep 1290343 = 1935515) B1935515
theorem B1290415 : Blo 1144635 1290415 := bstep (se 1 (by rfl) ⟨967811, by rfl⟩ : syracuseStep 1290415 = 1935623) B1935623
theorem B4894951 : Blo 1144635 4894951 := bstep (se 1 (by rfl) ⟨3671213, by rfl⟩ : syracuseStep 4894951 = 7342427) B7342427
theorem B8696483 : Blo 1144635 8696483 := bstep (se 1 (by rfl) ⟨6522362, by rfl⟩ : syracuseStep 8696483 = 13044725) B13044725
theorem B1717055 : Blo 1144635 1717055 := bstep (se 1 (by rfl) ⟨1287791, by rfl⟩ : syracuseStep 1717055 = 2575583) B2575583
theorem B1291099 : Blo 1144635 1291099 := bstep (se 1 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 1291099 = 1936649) B1936649
theorem B35271629 : Blo 1144635 35271629 := bstep (se 3 (by rfl) ⟨6613430, by rfl⟩ : syracuseStep 35271629 = 13226861) B13226861
theorem B1717199 : Blo 1144635 1717199 := bstep (se 1 (by rfl) ⟨1287899, by rfl⟩ : syracuseStep 1717199 = 2575799) B2575799
theorem B1225711 : Blo 1144635 1225711 := bstep (se 1 (by rfl) ⟨919283, by rfl⟩ : syracuseStep 1225711 = 1838567) B1838567
theorem B1717241 : Blo 1144635 1717241 := bstep (se 2 (by rfl) ⟨643965, by rfl⟩ : syracuseStep 1717241 = 1287931) B1287931
theorem B1717289 : Blo 1144635 1717289 := bstep (se 2 (by rfl) ⟨643983, by rfl⟩ : syracuseStep 1717289 = 1287967) B1287967
theorem B1717319 : Blo 1144635 1717319 := bstep (se 1 (by rfl) ⟨1287989, by rfl⟩ : syracuseStep 1717319 = 2575979) B2575979
theorem B4895873 : Blo 1144635 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B1717499 : Blo 1144635 1717499 := bstep (se 1 (by rfl) ⟨1288124, by rfl⟩ : syracuseStep 1717499 = 2576249) B2576249
theorem B5224367 : Blo 1144635 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B5814503 : Blo 1144635 5814503 := bstep (se 1 (by rfl) ⟨4360877, by rfl⟩ : syracuseStep 5814503 = 8721755) B8721755
theorem B1718735 : Blo 1144635 1718735 := bstep (se 1 (by rfl) ⟨1289051, by rfl⟩ : syracuseStep 1718735 = 2578103) B2578103
theorem B1718825 : Blo 1144635 1718825 := bstep (se 2 (by rfl) ⟨644559, by rfl⟩ : syracuseStep 1718825 = 1289119) B1289119
theorem B2898575 : Blo 1144635 2898575 := bstep (se 1 (by rfl) ⟨2173931, by rfl⟩ : syracuseStep 2898575 = 4347863) B4347863
theorem B1719017 : Blo 1144635 1719017 := bstep (se 2 (by rfl) ⟨644631, by rfl⟩ : syracuseStep 1719017 = 1289263) B1289263
theorem B4897513 : Blo 1144635 4897513 := bstep (se 2 (by rfl) ⟨1836567, by rfl⟩ : syracuseStep 4897513 = 3673135) B3673135
theorem B4897583 : Blo 1144635 4897583 := bstep (se 1 (by rfl) ⟨3673187, by rfl⟩ : syracuseStep 4897583 = 7346375) B7346375
theorem B2898899 : Blo 1144635 2898899 := bstep (se 1 (by rfl) ⟨2174174, by rfl⟩ : syracuseStep 2898899 = 4348349) B4348349
theorem B8698913 : Blo 1144635 8698913 := bstep (se 2 (by rfl) ⟨3262092, by rfl⟩ : syracuseStep 8698913 = 6524185) B6524185
theorem B1719401 : Blo 1144635 1719401 := bstep (se 2 (by rfl) ⟨644775, by rfl⟩ : syracuseStep 1719401 = 1289551) B1289551
theorem B1719527 : Blo 1144635 1719527 := bstep (se 1 (by rfl) ⟨1289645, by rfl⟩ : syracuseStep 1719527 = 2579291) B2579291
theorem B4406525 : Blo 1144635 4406525 := bstep (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) B1652447
theorem B2899273 : Blo 1144635 2899273 := bstep (se 2 (by rfl) ⟨1087227, by rfl⟩ : syracuseStep 2899273 = 2174455) B2174455
theorem B1720031 : Blo 1144635 1720031 := bstep (se 1 (by rfl) ⟨1290023, by rfl⟩ : syracuseStep 1720031 = 2580047) B2580047
theorem B1720073 : Blo 1144635 1720073 := bstep (se 2 (by rfl) ⟨645027, by rfl⟩ : syracuseStep 1720073 = 1290055) B1290055
theorem B1720511 : Blo 1144635 1720511 := bstep (se 1 (by rfl) ⟨1290383, by rfl⟩ : syracuseStep 1720511 = 2580767) B2580767
theorem B4899325 : Blo 1144635 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B24789509 : Blo 1144635 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B1720937 : Blo 1144635 1720937 := bstep (se 2 (by rfl) ⟨645351, by rfl⟩ : syracuseStep 1720937 = 1290703) B1290703
theorem B1720943 : Blo 1144635 1720943 := bstep (se 1 (by rfl) ⟨1290707, by rfl⟩ : syracuseStep 1720943 = 2581415) B2581415
theorem B6275969 : Blo 1144635 6275969 := bstep (se 2 (by rfl) ⟨2353488, by rfl⟩ : syracuseStep 6275969 = 4706977) B4706977
theorem B8700857 : Blo 1144635 8700857 := bstep (se 2 (by rfl) ⟨3262821, by rfl⟩ : syracuseStep 8700857 = 6525643) B6525643
theorem B9782315 : Blo 1144635 9782315 := bstep (se 1 (by rfl) ⟨7336736, by rfl⟩ : syracuseStep 9782315 = 14673473) B14673473
theorem B2901167 : Blo 1144635 2901167 := bstep (se 1 (by rfl) ⟨2175875, by rfl⟩ : syracuseStep 2901167 = 4351751) B4351751
theorem B2180287 : Blo 1144635 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B1721567 : Blo 1144635 1721567 := bstep (se 1 (by rfl) ⟨1291175, by rfl⟩ : syracuseStep 1721567 = 2582351) B2582351
theorem B1721579 : Blo 1144635 1721579 := bstep (se 1 (by rfl) ⟨1291184, by rfl⟩ : syracuseStep 1721579 = 2582369) B2582369
theorem B3261865 : Blo 1144635 3261865 := bstep (se 2 (by rfl) ⟨1223199, by rfl⟩ : syracuseStep 3261865 = 2446399) B2446399
theorem B4900283 : Blo 1144635 4900283 := bstep (se 1 (by rfl) ⟨3675212, by rfl⟩ : syracuseStep 4900283 = 7350425) B7350425
theorem B4310459 : Blo 1144635 4310459 := bstep (se 1 (by rfl) ⟨3232844, by rfl⟩ : syracuseStep 4310459 = 6465689) B6465689
theorem B60311141 : Blo 1144635 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B1721963 : Blo 1144635 1721963 := bstep (se 1 (by rfl) ⟨1291472, by rfl⟩ : syracuseStep 1721963 = 2582945) B2582945
theorem B1722047 : Blo 1144635 1722047 := bstep (se 1 (by rfl) ⟨1291535, by rfl⟩ : syracuseStep 1722047 = 2583071) B2583071
theorem B1722233 : Blo 1144635 1722233 := bstep (se 2 (by rfl) ⟨645837, by rfl⟩ : syracuseStep 1722233 = 1291675) B1291675
theorem B2902351 : Blo 1144635 2902351 := bstep (se 1 (by rfl) ⟨2176763, by rfl⟩ : syracuseStep 2902351 = 4353527) B4353527
theorem B11028905 : Blo 1144635 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B3263323 : Blo 1144635 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B3263483 : Blo 1144635 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B7359497 : Blo 1144635 7359497 := bstep (se 2 (by rfl) ⟨2759811, by rfl⟩ : syracuseStep 7359497 = 5519623) B5519623
theorem B2575547 : Blo 1144635 2575547 := bstep (se 1 (by rfl) ⟨1931660, by rfl⟩ : syracuseStep 2575547 = 3863321) B3863321
theorem B2575727 : Blo 1144635 2575727 := bstep (se 1 (by rfl) ⟨1931795, by rfl⟩ : syracuseStep 2575727 = 3863591) B3863591
theorem B3919265 : Blo 1144635 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B2444879 : Blo 1144635 2444879 := bstep (se 1 (by rfl) ⟨1833659, by rfl⟩ : syracuseStep 2444879 = 3667319) B3667319
theorem B11161415 : Blo 1144635 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B2576447 : Blo 1144635 2576447 := bstep (se 1 (by rfl) ⟨1932335, by rfl⟩ : syracuseStep 2576447 = 3864671) B3864671
theorem B2445511 : Blo 1144635 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B120639773 : Blo 1144635 120639773 := bstep (se 3 (by rfl) ⟨22619957, by rfl⟩ : syracuseStep 120639773 = 45239915) B45239915
theorem B2576681 : Blo 1144635 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B4641191 : Blo 1144635 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B2576951 : Blo 1144635 2576951 := bstep (se 1 (by rfl) ⟨1932713, by rfl⟩ : syracuseStep 2576951 = 3865427) B3865427
theorem B4903699 : Blo 1144635 4903699 := bstep (se 1 (by rfl) ⟨3677774, by rfl⟩ : syracuseStep 4903699 = 7355549) B7355549
theorem B2904923 : Blo 1144635 2904923 := bstep (se 1 (by rfl) ⟨2178692, by rfl⟩ : syracuseStep 2904923 = 4357385) B4357385
theorem B2577257 : Blo 1144635 2577257 := bstep (se 2 (by rfl) ⟨966471, by rfl⟩ : syracuseStep 2577257 = 1932943) B1932943
theorem B2904943 : Blo 1144635 2904943 := bstep (se 1 (by rfl) ⟨2178707, by rfl⟩ : syracuseStep 2904943 = 4357415) B4357415
theorem B2577311 : Blo 1144635 2577311 := bstep (se 1 (by rfl) ⟨1932983, by rfl⟩ : syracuseStep 2577311 = 3865967) B3865967
theorem B2577563 : Blo 1144635 2577563 := bstep (se 1 (by rfl) ⟨1933172, by rfl⟩ : syracuseStep 2577563 = 3866345) B3866345
theorem B2446699 : Blo 1144635 2446699 := bstep (se 1 (by rfl) ⟨1835024, by rfl⟩ : syracuseStep 2446699 = 3670049) B3670049
theorem B22042043 : Blo 1144635 22042043 := bstep (se 1 (by rfl) ⟨16531532, by rfl⟩ : syracuseStep 22042043 = 33063065) B33063065
theorem B2578139 : Blo 1144635 2578139 := bstep (se 1 (by rfl) ⟨1933604, by rfl⟩ : syracuseStep 2578139 = 3867209) B3867209
theorem B31381229 : Blo 1144635 31381229 := bstep (se 3 (by rfl) ⟨5883980, by rfl⟩ : syracuseStep 31381229 = 11767961) B11767961
theorem B2578247 : Blo 1144635 2578247 := bstep (se 1 (by rfl) ⟨1933685, by rfl⟩ : syracuseStep 2578247 = 3867371) B3867371
theorem B4642717 : Blo 1144635 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B10475885 : Blo 1144635 10475885 := bstep (se 3 (by rfl) ⟨1964228, by rfl⟩ : syracuseStep 10475885 = 3928457) B3928457
theorem B4413971 : Blo 1144635 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B2579255 : Blo 1144635 2579255 := bstep (se 1 (by rfl) ⟨1934441, by rfl⟩ : syracuseStep 2579255 = 3868883) B3868883
theorem B2579435 : Blo 1144635 2579435 := bstep (se 1 (by rfl) ⟨1934576, by rfl⟩ : syracuseStep 2579435 = 3869153) B3869153
theorem B4349807 : Blo 1144635 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B2580335 : Blo 1144635 2580335 := bstep (se 1 (by rfl) ⟨1935251, by rfl⟩ : syracuseStep 2580335 = 3870503) B3870503
theorem B15687557 : Blo 1144635 15687557 := bstep (se 4 (by rfl) ⟨1470708, by rfl⟩ : syracuseStep 15687557 = 2941417) B2941417
theorem B20930683 : Blo 1144635 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B11035055 : Blo 1144635 11035055 := bstep (se 1 (by rfl) ⟨8276291, by rfl⟩ : syracuseStep 11035055 = 16552583) B16552583
theorem B2581019 : Blo 1144635 2581019 := bstep (se 1 (by rfl) ⟨1935764, by rfl⟩ : syracuseStep 2581019 = 3871529) B3871529
theorem B2581199 : Blo 1144635 2581199 := bstep (se 1 (by rfl) ⟨1935899, by rfl⟩ : syracuseStep 2581199 = 3871799) B3871799
theorem B2581577 : Blo 1144635 2581577 := bstep (se 2 (by rfl) ⟨968091, by rfl⟩ : syracuseStep 2581577 = 1936183) B1936183
theorem B4351583 : Blo 1144635 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B3270557 : Blo 1144635 3270557 := bstep (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) B1226459
theorem B2582495 : Blo 1144635 2582495 := bstep (se 1 (by rfl) ⟨1936871, by rfl⟩ : syracuseStep 2582495 = 3873743) B3873743
theorem B3270739 : Blo 1144635 3270739 := bstep (se 1 (by rfl) ⟨2453054, by rfl⟩ : syracuseStep 3270739 = 4906109) B4906109
theorem B21195017 : Blo 1144635 21195017 := bstep (se 2 (by rfl) ⟨7948131, by rfl⟩ : syracuseStep 21195017 = 15896263) B15896263
theorem B2451961 : Blo 1144635 2451961 := bstep (se 2 (by rfl) ⟨919485, by rfl⟩ : syracuseStep 2451961 = 1838971) B1838971
theorem B2583503 : Blo 1144635 2583503 := bstep (se 1 (by rfl) ⟨1937627, by rfl⟩ : syracuseStep 2583503 = 3875255) B3875255
theorem B2452447 : Blo 1144635 2452447 := bstep (se 1 (by rfl) ⟨1839335, by rfl⟩ : syracuseStep 2452447 = 3678671) B3678671
theorem B2583593 : Blo 1144635 2583593 := bstep (se 2 (by rfl) ⟨968847, by rfl⟩ : syracuseStep 2583593 = 1937695) B1937695
theorem B14871755 : Blo 1144635 14871755 := bstep (se 1 (by rfl) ⟨11153816, by rfl⟩ : syracuseStep 14871755 = 22307633) B22307633
theorem B2583827 : Blo 1144635 2583827 := bstep (se 1 (by rfl) ⟨1937870, by rfl⟩ : syracuseStep 2583827 = 3875741) B3875741
theorem B2125111 : Blo 1144635 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2583863 : Blo 1144635 2583863 := bstep (se 1 (by rfl) ⟨1937897, by rfl⟩ : syracuseStep 2583863 = 3875795) B3875795
theorem B44690867 : Blo 1144635 44690867 := bstep (se 1 (by rfl) ⟨33518150, by rfl⟩ : syracuseStep 44690867 = 67036301) B67036301
theorem B1634185 : Blo 1144635 1634185 := bstep (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) B1225639
theorem B2486153 : Blo 1144635 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B2355193 : Blo 1144635 2355193 := bstep (se 2 (by rfl) ⟨883197, by rfl⟩ : syracuseStep 2355193 = 1766395) B1766395
theorem B5238857 : Blo 1144635 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B4649723 : Blo 1144635 4649723 := bstep (se 1 (by rfl) ⟨3487292, by rfl⟩ : syracuseStep 4649723 = 6974585) B6974585
theorem B2552639 : Blo 1144635 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B5797331 : Blo 1144635 5797331 := bstep (se 1 (by rfl) ⟨4347998, by rfl⟩ : syracuseStep 5797331 = 8695997) B8695997
theorem B3864023 : Blo 1144635 3864023 := bstep (se 1 (by rfl) ⟨2898017, by rfl⟩ : syracuseStep 3864023 = 5796035) B5796035
theorem B1144647 : Blo 1144635 1144647 := bstep (se 1 (by rfl) ⟨858485, by rfl⟩ : syracuseStep 1144647 = 1716971) B1716971
theorem B1144667 : Blo 1144635 1144667 := bstep (se 1 (by rfl) ⟨858500, by rfl⟩ : syracuseStep 1144667 = 1717001) B1717001
theorem B1144735 : Blo 1144635 1144735 := bstep (se 1 (by rfl) ⟨858551, by rfl⟩ : syracuseStep 1144735 = 1717103) B1717103
theorem B1144903 : Blo 1144635 1144903 := bstep (se 1 (by rfl) ⟨858677, by rfl⟩ : syracuseStep 1144903 = 1717355) B1717355
theorem B1145063 : Blo 1144635 1145063 := bstep (se 1 (by rfl) ⟨858797, by rfl⟩ : syracuseStep 1145063 = 1717595) B1717595
theorem B4356443 : Blo 1144635 4356443 := bstep (se 1 (by rfl) ⟨3267332, by rfl⟩ : syracuseStep 4356443 = 6534665) B6534665
theorem B1145247 : Blo 1144635 1145247 := bstep (se 1 (by rfl) ⟨858935, by rfl⟩ : syracuseStep 1145247 = 1717871) B1717871
theorem B1145295 : Blo 1144635 1145295 := bstep (se 1 (by rfl) ⟨858971, by rfl⟩ : syracuseStep 1145295 = 1717943) B1717943
theorem B1145319 : Blo 1144635 1145319 := bstep (se 1 (by rfl) ⟨858989, by rfl⟩ : syracuseStep 1145319 = 1717979) B1717979
theorem B2751007 : Blo 1144635 2751007 := bstep (se 1 (by rfl) ⟨2063255, by rfl⟩ : syracuseStep 2751007 = 4126511) B4126511
theorem B1145435 : Blo 1144635 1145435 := bstep (se 1 (by rfl) ⟨859076, by rfl⟩ : syracuseStep 1145435 = 1718153) B1718153
theorem B1145503 : Blo 1144635 1145503 := bstep (se 1 (by rfl) ⟨859127, by rfl⟩ : syracuseStep 1145503 = 1718255) B1718255
theorem B13040351 : Blo 1144635 13040351 := bstep (se 1 (by rfl) ⟨9780263, by rfl⟩ : syracuseStep 13040351 = 19560527) B19560527
theorem B2063083 : Blo 1144635 2063083 := bstep (se 1 (by rfl) ⟨1547312, by rfl⟩ : syracuseStep 2063083 = 3094625) B3094625
theorem B1932079 : Blo 1144635 1932079 := bstep (se 1 (by rfl) ⟨1449059, by rfl⟩ : syracuseStep 1932079 = 2898119) B2898119
theorem B1145671 : Blo 1144635 1145671 := bstep (se 1 (by rfl) ⟨859253, by rfl⟩ : syracuseStep 1145671 = 1718507) B1718507
theorem B1145711 : Blo 1144635 1145711 := bstep (se 1 (by rfl) ⟨859283, by rfl⟩ : syracuseStep 1145711 = 1718567) B1718567
theorem B1145767 : Blo 1144635 1145767 := bstep (se 1 (by rfl) ⟨859325, by rfl⟩ : syracuseStep 1145767 = 1718651) B1718651
theorem B26508217 : Blo 1144635 26508217 := bstep (se 2 (by rfl) ⟨9940581, by rfl⟩ : syracuseStep 26508217 = 19881163) B19881163
theorem B4357111 : Blo 1144635 4357111 := bstep (se 1 (by rfl) ⟨3267833, by rfl⟩ : syracuseStep 4357111 = 6535667) B6535667
theorem B1145947 : Blo 1144635 1145947 := bstep (se 1 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 1145947 = 1718921) B1718921
theorem B1146063 : Blo 1144635 1146063 := bstep (se 1 (by rfl) ⟨859547, by rfl⟩ : syracuseStep 1146063 = 1719095) B1719095
theorem B1146087 : Blo 1144635 1146087 := bstep (se 1 (by rfl) ⟨859565, by rfl⟩ : syracuseStep 1146087 = 1719131) B1719131
theorem B10452239 : Blo 1144635 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B1146183 : Blo 1144635 1146183 := bstep (se 1 (by rfl) ⟨859637, by rfl⟩ : syracuseStep 1146183 = 1719275) B1719275
theorem B1146319 : Blo 1144635 1146319 := bstep (se 1 (by rfl) ⟨859739, by rfl⟩ : syracuseStep 1146319 = 1719479) B1719479
theorem B4357583 : Blo 1144635 4357583 := bstep (se 1 (by rfl) ⟨3268187, by rfl⟩ : syracuseStep 4357583 = 6536375) B6536375
theorem B1146479 : Blo 1144635 1146479 := bstep (se 1 (by rfl) ⟨859859, by rfl⟩ : syracuseStep 1146479 = 1719719) B1719719
theorem B5504669 : Blo 1144635 5504669 := bstep (se 3 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 5504669 = 2064251) B2064251
theorem B1146535 : Blo 1144635 1146535 := bstep (se 1 (by rfl) ⟨859901, by rfl⟩ : syracuseStep 1146535 = 1719803) B1719803
theorem B5799599 : Blo 1144635 5799599 := bstep (se 1 (by rfl) ⟨4349699, by rfl⟩ : syracuseStep 5799599 = 8699399) B8699399
theorem B1933031 : Blo 1144635 1933031 := bstep (se 1 (by rfl) ⟨1449773, by rfl⟩ : syracuseStep 1933031 = 2899547) B2899547
theorem B1146599 : Blo 1144635 1146599 := bstep (se 1 (by rfl) ⟨859949, by rfl⟩ : syracuseStep 1146599 = 1719899) B1719899
theorem B1146655 : Blo 1144635 1146655 := bstep (se 1 (by rfl) ⟨859991, by rfl⟩ : syracuseStep 1146655 = 1719983) B1719983
theorem B1146735 : Blo 1144635 1146735 := bstep (se 1 (by rfl) ⟨860051, by rfl⟩ : syracuseStep 1146735 = 1720103) B1720103
theorem B3309455 : Blo 1144635 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B1146791 : Blo 1144635 1146791 := bstep (se 1 (by rfl) ⟨860093, by rfl⟩ : syracuseStep 1146791 = 1720187) B1720187
theorem B1147007 : Blo 1144635 1147007 := bstep (se 1 (by rfl) ⟨860255, by rfl⟩ : syracuseStep 1147007 = 1720511) B1720511
theorem B3670265 : Blo 1144635 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B1147291 : Blo 1144635 1147291 := bstep (se 1 (by rfl) ⟨860468, by rfl⟩ : syracuseStep 1147291 = 1720937) B1720937
theorem B1147295 : Blo 1144635 1147295 := bstep (se 1 (by rfl) ⟨860471, by rfl⟩ : syracuseStep 1147295 = 1720943) B1720943
theorem B5800571 : Blo 1144635 5800571 := bstep (se 1 (by rfl) ⟨4350428, by rfl⟩ : syracuseStep 5800571 = 8700857) B8700857
theorem B6521543 : Blo 1144635 6521543 := bstep (se 1 (by rfl) ⟨4891157, by rfl⟩ : syracuseStep 6521543 = 9782315) B9782315
theorem B1934111 : Blo 1144635 1934111 := bstep (se 1 (by rfl) ⟨1450583, by rfl⟩ : syracuseStep 1934111 = 2901167) B2901167
theorem B1147711 : Blo 1144635 1147711 := bstep (se 1 (by rfl) ⟨860783, by rfl⟩ : syracuseStep 1147711 = 1721567) B1721567
theorem B1147719 : Blo 1144635 1147719 := bstep (se 1 (by rfl) ⟨860789, by rfl⟩ : syracuseStep 1147719 = 1721579) B1721579
theorem B40207427 : Blo 1144635 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B1147975 : Blo 1144635 1147975 := bstep (se 1 (by rfl) ⟨860981, by rfl⟩ : syracuseStep 1147975 = 1721963) B1721963
theorem B1148031 : Blo 1144635 1148031 := bstep (se 1 (by rfl) ⟨861023, by rfl⟩ : syracuseStep 1148031 = 1722047) B1722047
theorem B1148155 : Blo 1144635 1148155 := bstep (se 1 (by rfl) ⟨861116, by rfl⟩ : syracuseStep 1148155 = 1722233) B1722233
theorem B6621331 : Blo 1144635 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B5507243 : Blo 1144635 5507243 := bstep (se 1 (by rfl) ⟨4130432, by rfl⟩ : syracuseStep 5507243 = 8260865) B8260865
theorem B62720419 : Blo 1144635 62720419 := bstep (se 1 (by rfl) ⟨47040314, by rfl⟩ : syracuseStep 62720419 = 94080629) B94080629
theorem B5507783 : Blo 1144635 5507783 := bstep (se 1 (by rfl) ⟨4130837, by rfl⟩ : syracuseStep 5507783 = 8261675) B8261675
theorem B3869423 : Blo 1144635 3869423 := bstep (se 1 (by rfl) ⟨2902067, by rfl⟩ : syracuseStep 3869423 = 5804135) B5804135
theorem B4360985 : Blo 1144635 4360985 := bstep (se 2 (by rfl) ⟨1635369, by rfl⟩ : syracuseStep 4360985 = 3270739) B3270739
theorem B3869801 : Blo 1144635 3869801 := bstep (se 2 (by rfl) ⟨1451175, by rfl⟩ : syracuseStep 3869801 = 2902351) B2902351
theorem B1936615 : Blo 1144635 1936615 := bstep (se 1 (by rfl) ⟨1452461, by rfl⟩ : syracuseStep 1936615 = 2904923) B2904923
theorem B6983923 : Blo 1144635 6983923 := bstep (se 1 (by rfl) ⟨5237942, by rfl⟩ : syracuseStep 6983923 = 10475885) B10475885
theorem B3674393 : Blo 1144635 3674393 := bstep (se 2 (by rfl) ⟨1377897, by rfl⟩ : syracuseStep 3674393 = 2755795) B2755795
theorem B13079717 : Blo 1144635 13079717 := bstep (se 4 (by rfl) ⟨1226223, by rfl⟩ : syracuseStep 13079717 = 2452447) B2452447
theorem B10458371 : Blo 1144635 10458371 := bstep (se 1 (by rfl) ⟨7843778, by rfl⟩ : syracuseStep 10458371 = 15687557) B15687557
theorem B12391987 : Blo 1144635 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B6526601 : Blo 1144635 6526601 := bstep (se 2 (by rfl) ⟨2447475, by rfl⟩ : syracuseStep 6526601 = 4894951) B4894951
theorem B11016101 : Blo 1144635 11016101 := bstep (se 4 (by rfl) ⟨1032759, by rfl⟩ : syracuseStep 11016101 = 2065519) B2065519
theorem B3872879 : Blo 1144635 3872879 := bstep (se 1 (by rfl) ⟨2904659, by rfl⟩ : syracuseStep 3872879 = 5809319) B5809319
theorem B5511377 : Blo 1144635 5511377 := bstep (se 2 (by rfl) ⟨2066766, by rfl⟩ : syracuseStep 5511377 = 4133533) B4133533
theorem B3873257 : Blo 1144635 3873257 := bstep (se 2 (by rfl) ⟨1452471, by rfl⟩ : syracuseStep 3873257 = 2904943) B2904943
theorem B3873311 : Blo 1144635 3873311 := bstep (se 1 (by rfl) ⟨2904983, by rfl⟩ : syracuseStep 3873311 = 5809967) B5809967
theorem B14130011 : Blo 1144635 14130011 := bstep (se 1 (by rfl) ⟨10597508, by rfl⟩ : syracuseStep 14130011 = 21195017) B21195017
theorem B29793911 : Blo 1144635 29793911 := bstep (se 1 (by rfl) ⟨22345433, by rfl⟩ : syracuseStep 29793911 = 44690867) B44690867
theorem B3874715 : Blo 1144635 3874715 := bstep (se 1 (by rfl) ⟨2906036, by rfl⟩ : syracuseStep 3874715 = 5812073) B5812073
theorem B3678493 : Blo 1144635 3678493 := bstep (se 3 (by rfl) ⟨689717, by rfl⟩ : syracuseStep 3678493 = 1379435) B1379435
theorem B6530017 : Blo 1144635 6530017 := bstep (se 2 (by rfl) ⟨2448756, by rfl⟩ : syracuseStep 6530017 = 4897513) B4897513
theorem B3482911 : Blo 1144635 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B5809481 : Blo 1144635 5809481 := bstep (se 2 (by rfl) ⟨2178555, by rfl⟩ : syracuseStep 5809481 = 4357111) B4357111
theorem B3876335 : Blo 1144635 3876335 := bstep (se 1 (by rfl) ⟨2907251, by rfl⟩ : syracuseStep 3876335 = 5814503) B5814503
theorem B8693567 : Blo 1144635 8693567 := bstep (se 1 (by rfl) ⟨6520175, by rfl⟩ : syracuseStep 8693567 = 13040351) B13040351
theorem B29763773 : Blo 1144635 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B8825213 : Blo 1144635 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B1288687 : Blo 1144635 1288687 := bstep (se 1 (by rfl) ⟨966515, by rfl⟩ : syracuseStep 1288687 = 1933031) B1933031
theorem B1223623 : Blo 1144635 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B16526339 : Blo 1144635 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B5811263 : Blo 1144635 5811263 := bstep (se 1 (by rfl) ⟨4358447, by rfl⟩ : syracuseStep 5811263 = 8716895) B8716895
theorem B6532433 : Blo 1144635 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B1290523 : Blo 1144635 1290523 := bstep (se 1 (by rfl) ⟨967892, by rfl⟩ : syracuseStep 1290523 = 1935785) B1935785
theorem B7352603 : Blo 1144635 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B2175655 : Blo 1144635 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B1290919 : Blo 1144635 1290919 := bstep (se 1 (by rfl) ⟨968189, by rfl⟩ : syracuseStep 1290919 = 1936379) B1936379
theorem B1717031 : Blo 1144635 1717031 := bstep (se 1 (by rfl) ⟨1287773, by rfl⟩ : syracuseStep 1717031 = 2575547) B2575547
theorem B1717151 : Blo 1144635 1717151 := bstep (se 1 (by rfl) ⟨1287863, by rfl⟩ : syracuseStep 1717151 = 2575727) B2575727
theorem B29406401 : Blo 1144635 29406401 := bstep (se 2 (by rfl) ⟨11027400, by rfl⟩ : syracuseStep 29406401 = 22054801) B22054801
theorem B15709403 : Blo 1144635 15709403 := bstep (se 1 (by rfl) ⟨11782052, by rfl⟩ : syracuseStep 15709403 = 23564105) B23564105
theorem B1717625 : Blo 1144635 1717625 := bstep (se 2 (by rfl) ⟨644109, by rfl⟩ : syracuseStep 1717625 = 1288219) B1288219
theorem B1717631 : Blo 1144635 1717631 := bstep (se 1 (by rfl) ⟨1288223, by rfl⟩ : syracuseStep 1717631 = 2576447) B2576447
theorem B22033889 : Blo 1144635 22033889 := bstep (se 2 (by rfl) ⟨8262708, by rfl⟩ : syracuseStep 22033889 = 16525417) B16525417
theorem B80426515 : Blo 1144635 80426515 := bstep (se 1 (by rfl) ⟨60319886, by rfl⟩ : syracuseStep 80426515 = 120639773) B120639773
theorem B1717787 : Blo 1144635 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B4896283 : Blo 1144635 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B3094127 : Blo 1144635 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B1717967 : Blo 1144635 1717967 := bstep (se 1 (by rfl) ⟨1288475, by rfl⟩ : syracuseStep 1717967 = 2576951) B2576951
theorem B1718171 : Blo 1144635 1718171 := bstep (se 1 (by rfl) ⟨1288628, by rfl⟩ : syracuseStep 1718171 = 2577257) B2577257
theorem B1718207 : Blo 1144635 1718207 := bstep (se 1 (by rfl) ⟨1288655, by rfl⟩ : syracuseStep 1718207 = 2577311) B2577311
theorem B1718375 : Blo 1144635 1718375 := bstep (se 1 (by rfl) ⟨1288781, by rfl⟩ : syracuseStep 1718375 = 2577563) B2577563
theorem B14694695 : Blo 1144635 14694695 := bstep (se 1 (by rfl) ⟨11021021, by rfl⟩ : syracuseStep 14694695 = 22042043) B22042043
theorem B5814665 : Blo 1144635 5814665 := bstep (se 2 (by rfl) ⟨2180499, by rfl⟩ : syracuseStep 5814665 = 4360999) B4360999
theorem B1718759 : Blo 1144635 1718759 := bstep (se 1 (by rfl) ⟨1289069, by rfl⟩ : syracuseStep 1718759 = 2578139) B2578139
theorem B1718831 : Blo 1144635 1718831 := bstep (se 1 (by rfl) ⟨1289123, by rfl⟩ : syracuseStep 1718831 = 2578247) B2578247
theorem B2833481 : Blo 1144635 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1719503 : Blo 1144635 1719503 := bstep (se 1 (by rfl) ⟨1289627, by rfl⟩ : syracuseStep 1719503 = 2579255) B2579255
theorem B33013007 : Blo 1144635 33013007 := bstep (se 1 (by rfl) ⟨24759755, by rfl⟩ : syracuseStep 33013007 = 49519511) B49519511
theorem B1719593 : Blo 1144635 1719593 := bstep (se 2 (by rfl) ⟨644847, by rfl⟩ : syracuseStep 1719593 = 1289695) B1289695
theorem B1719623 : Blo 1144635 1719623 := bstep (se 1 (by rfl) ⟨1289717, by rfl⟩ : syracuseStep 1719623 = 2579435) B2579435
theorem B2178913 : Blo 1144635 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B2899871 : Blo 1144635 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B1720223 : Blo 1144635 1720223 := bstep (se 1 (by rfl) ⟨1290167, by rfl⟩ : syracuseStep 1720223 = 2580335) B2580335
theorem B6537125 : Blo 1144635 6537125 := bstep (se 4 (by rfl) ⟨612855, by rfl⟩ : syracuseStep 6537125 = 1225711) B1225711
theorem B1720313 : Blo 1144635 1720313 := bstep (se 2 (by rfl) ⟨645117, by rfl⟩ : syracuseStep 1720313 = 1290235) B1290235
theorem B7356521 : Blo 1144635 7356521 := bstep (se 2 (by rfl) ⟨2758695, by rfl⟩ : syracuseStep 7356521 = 5517391) B5517391
theorem B1720457 : Blo 1144635 1720457 := bstep (se 2 (by rfl) ⟨645171, by rfl⟩ : syracuseStep 1720457 = 1290343) B1290343
theorem B1720553 : Blo 1144635 1720553 := bstep (se 2 (by rfl) ⟨645207, by rfl⟩ : syracuseStep 1720553 = 1290415) B1290415
theorem B3260681 : Blo 1144635 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B7356703 : Blo 1144635 7356703 := bstep (se 1 (by rfl) ⟨5517527, by rfl⟩ : syracuseStep 7356703 = 11035055) B11035055
theorem B1720679 : Blo 1144635 1720679 := bstep (se 1 (by rfl) ⟨1290509, by rfl⟩ : syracuseStep 1720679 = 2581019) B2581019
theorem B1720799 : Blo 1144635 1720799 := bstep (se 1 (by rfl) ⟨1290599, by rfl⟩ : syracuseStep 1720799 = 2581199) B2581199
theorem B4899359 : Blo 1144635 4899359 := bstep (se 1 (by rfl) ⟨3674519, by rfl⟩ : syracuseStep 4899359 = 7349039) B7349039
theorem B1721051 : Blo 1144635 1721051 := bstep (se 1 (by rfl) ⟨1290788, by rfl⟩ : syracuseStep 1721051 = 2581577) B2581577
theorem B6538265 : Blo 1144635 6538265 := bstep (se 2 (by rfl) ⟨2451849, by rfl⟩ : syracuseStep 6538265 = 4903699) B4903699
theorem B2901055 : Blo 1144635 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B1721465 : Blo 1144635 1721465 := bstep (se 2 (by rfl) ⟨645549, by rfl⟩ : syracuseStep 1721465 = 1291099) B1291099
theorem B2180371 : Blo 1144635 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B1721663 : Blo 1144635 1721663 := bstep (se 1 (by rfl) ⟨1291247, by rfl⟩ : syracuseStep 1721663 = 2582495) B2582495
theorem B6539039 : Blo 1144635 6539039 := bstep (se 1 (by rfl) ⟨4904279, by rfl⟩ : syracuseStep 6539039 = 9808559) B9808559
theorem B3262265 : Blo 1144635 3262265 := bstep (se 2 (by rfl) ⟨1223349, by rfl⟩ : syracuseStep 3262265 = 2446699) B2446699
theorem B1722335 : Blo 1144635 1722335 := bstep (se 1 (by rfl) ⟨1291751, by rfl⟩ : syracuseStep 1722335 = 2583503) B2583503
theorem B1722395 : Blo 1144635 1722395 := bstep (se 1 (by rfl) ⟨1291796, by rfl⟩ : syracuseStep 1722395 = 2583593) B2583593
theorem B9914503 : Blo 1144635 9914503 := bstep (se 1 (by rfl) ⟨7435877, by rfl⟩ : syracuseStep 9914503 = 14871755) B14871755
theorem B1722551 : Blo 1144635 1722551 := bstep (se 1 (by rfl) ⟨1291913, by rfl⟩ : syracuseStep 1722551 = 2583827) B2583827
theorem B1722575 : Blo 1144635 1722575 := bstep (se 1 (by rfl) ⟨1291931, by rfl⟩ : syracuseStep 1722575 = 2583863) B2583863
theorem B5884127 : Blo 1144635 5884127 := bstep (se 1 (by rfl) ⟨4413095, by rfl⟩ : syracuseStep 5884127 = 8826191) B8826191
theorem B8702315 : Blo 1144635 8702315 := bstep (se 1 (by rfl) ⟨6526736, by rfl⟩ : syracuseStep 8702315 = 13053473) B13053473
theorem B1657435 : Blo 1144635 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B67095215 : Blo 1144635 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B3492571 : Blo 1144635 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B3099815 : Blo 1144635 3099815 := bstep (se 1 (by rfl) ⟨2324861, by rfl⟩ : syracuseStep 3099815 = 4649723) B4649723
theorem B23514419 : Blo 1144635 23514419 := bstep (se 1 (by rfl) ⟨17635814, by rfl⟩ : syracuseStep 23514419 = 35271629) B35271629
theorem B3263915 : Blo 1144635 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B2576015 : Blo 1144635 2576015 := bstep (se 1 (by rfl) ⟨1932011, by rfl⟩ : syracuseStep 2576015 = 3864023) B3864023
theorem B2576105 : Blo 1144635 2576105 := bstep (se 2 (by rfl) ⟨966039, by rfl⟩ : syracuseStep 2576105 = 1932079) B1932079
theorem B35344289 : Blo 1144635 35344289 := bstep (se 2 (by rfl) ⟨13254108, by rfl⟩ : syracuseStep 35344289 = 26508217) B26508217
theorem B2904295 : Blo 1144635 2904295 := bstep (se 1 (by rfl) ⟨2178221, by rfl⟩ : syracuseStep 2904295 = 4356443) B4356443
theorem B3265055 : Blo 1144635 3265055 := bstep (se 1 (by rfl) ⟨2448791, by rfl⟩ : syracuseStep 3265055 = 4897583) B4897583
theorem B3265181 : Blo 1144635 3265181 := bstep (se 3 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 3265181 = 1224443) B1224443
theorem B2937683 : Blo 1144635 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B6968159 : Blo 1144635 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B2905055 : Blo 1144635 2905055 := bstep (se 1 (by rfl) ⟨2178791, by rfl⟩ : syracuseStep 2905055 = 4357583) B4357583
theorem B27907577 : Blo 1144635 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B2578319 : Blo 1144635 2578319 := bstep (se 1 (by rfl) ⟨1933739, by rfl⟩ : syracuseStep 2578319 = 3867479) B3867479
theorem B4183979 : Blo 1144635 4183979 := bstep (se 1 (by rfl) ⟨3137984, by rfl⟩ : syracuseStep 4183979 = 6275969) B6275969
theorem B3266855 : Blo 1144635 3266855 := bstep (se 1 (by rfl) ⟨2450141, by rfl⟩ : syracuseStep 3266855 = 4900283) B4900283
theorem B2873639 : Blo 1144635 2873639 := bstep (se 1 (by rfl) ⟨2155229, by rfl⟩ : syracuseStep 2873639 = 4310459) B4310459
theorem B13425209 : Blo 1144635 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B2579039 : Blo 1144635 2579039 := bstep (se 1 (by rfl) ⟨1934279, by rfl⟩ : syracuseStep 2579039 = 3868559) B3868559
theorem B2906867 : Blo 1144635 2906867 := bstep (se 1 (by rfl) ⟨2180150, by rfl⟩ : syracuseStep 2906867 = 4360301) B4360301
theorem B2907049 : Blo 1144635 2907049 := bstep (se 2 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 2907049 = 2180287) B2180287
theorem B2579561 : Blo 1144635 2579561 := bstep (se 2 (by rfl) ⟨967335, by rfl⟩ : syracuseStep 2579561 = 1934671) B1934671
theorem B4349153 : Blo 1144635 4349153 := bstep (se 2 (by rfl) ⟨1630932, by rfl⟩ : syracuseStep 4349153 = 3261865) B3261865
theorem B4906331 : Blo 1144635 4906331 := bstep (se 1 (by rfl) ⟨3679748, by rfl⟩ : syracuseStep 4906331 = 7359497) B7359497
theorem B3104225 : Blo 1144635 3104225 := bstep (se 2 (by rfl) ⟨1164084, by rfl⟩ : syracuseStep 3104225 = 2328169) B2328169
theorem B2612843 : Blo 1144635 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B1629919 : Blo 1144635 1629919 := bstep (se 1 (by rfl) ⟨1222439, by rfl⟩ : syracuseStep 1629919 = 2444879) B2444879
theorem B2580191 : Blo 1144635 2580191 := bstep (se 1 (by rfl) ⟨1935143, by rfl⟩ : syracuseStep 2580191 = 3870287) B3870287
theorem B12410671 : Blo 1144635 12410671 := bstep (se 1 (by rfl) ⟨9308003, by rfl⟩ : syracuseStep 12410671 = 18616007) B18616007
theorem B2580551 : Blo 1144635 2580551 := bstep (se 1 (by rfl) ⟨1935413, by rfl⟩ : syracuseStep 2580551 = 3870827) B3870827
theorem B2580587 : Blo 1144635 2580587 := bstep (se 1 (by rfl) ⟨1935440, by rfl⟩ : syracuseStep 2580587 = 3870881) B3870881
theorem B2580857 : Blo 1144635 2580857 := bstep (se 2 (by rfl) ⟨967821, by rfl⟩ : syracuseStep 2580857 = 1935643) B1935643
theorem B3269281 : Blo 1144635 3269281 := bstep (se 2 (by rfl) ⟨1225980, by rfl⟩ : syracuseStep 3269281 = 2451961) B2451961
theorem B2581289 : Blo 1144635 2581289 := bstep (se 2 (by rfl) ⟨967983, by rfl⟩ : syracuseStep 2581289 = 1935967) B1935967
theorem B2581487 : Blo 1144635 2581487 := bstep (se 1 (by rfl) ⟨1936115, by rfl⟩ : syracuseStep 2581487 = 3872231) B3872231
theorem B2581559 : Blo 1144635 2581559 := bstep (se 1 (by rfl) ⟨1936169, by rfl⟩ : syracuseStep 2581559 = 3872339) B3872339
theorem B4351097 : Blo 1144635 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B2581739 : Blo 1144635 2581739 := bstep (se 1 (by rfl) ⟨1936304, by rfl⟩ : syracuseStep 2581739 = 3872609) B3872609
theorem B2942647 : Blo 1144635 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B83683277 : Blo 1144635 83683277 := bstep (se 3 (by rfl) ⟨15690614, by rfl⟩ : syracuseStep 83683277 = 31381229) B31381229
theorem B2451593 : Blo 1144635 2451593 := bstep (se 2 (by rfl) ⟨919347, by rfl⟩ : syracuseStep 2451593 = 1838695) B1838695
theorem B4418023 : Blo 1144635 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B2452123 : Blo 1144635 2452123 := bstep (se 1 (by rfl) ⟨1839092, by rfl⟩ : syracuseStep 2452123 = 3678185) B3678185
theorem B3140257 : Blo 1144635 3140257 := bstep (se 2 (by rfl) ⟨1177596, by rfl⟩ : syracuseStep 3140257 = 2355193) B2355193
theorem B4355167 : Blo 1144635 4355167 := bstep (se 1 (by rfl) ⟨3266375, by rfl⟩ : syracuseStep 4355167 = 6532751) B6532751
theorem B9794753 : Blo 1144635 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B6190289 : Blo 1144635 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B5797655 : Blo 1144635 5797655 := bstep (se 1 (by rfl) ⟨4348241, by rfl⟩ : syracuseStep 5797655 = 8696483) B8696483
theorem B1144703 : Blo 1144635 1144703 := bstep (se 1 (by rfl) ⟨858527, by rfl⟩ : syracuseStep 1144703 = 1717055) B1717055
theorem B1144799 : Blo 1144635 1144799 := bstep (se 1 (by rfl) ⟨858599, by rfl⟩ : syracuseStep 1144799 = 1717199) B1717199
theorem B27228149 : Blo 1144635 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1144827 : Blo 1144635 1144827 := bstep (se 1 (by rfl) ⟨858620, by rfl⟩ : syracuseStep 1144827 = 1717241) B1717241
theorem B1144859 : Blo 1144635 1144859 := bstep (se 1 (by rfl) ⟨858644, by rfl⟩ : syracuseStep 1144859 = 1717289) B1717289
theorem B3668009 : Blo 1144635 3668009 := bstep (se 2 (by rfl) ⟨1375503, by rfl⟩ : syracuseStep 3668009 = 2751007) B2751007
theorem B1144879 : Blo 1144635 1144879 := bstep (se 1 (by rfl) ⟨858659, by rfl⟩ : syracuseStep 1144879 = 1717319) B1717319
theorem B1144999 : Blo 1144635 1144999 := bstep (se 1 (by rfl) ⟨858749, by rfl⟩ : syracuseStep 1144999 = 1717499) B1717499
theorem B3864887 : Blo 1144635 3864887 := bstep (se 1 (by rfl) ⟨2898665, by rfl⟩ : syracuseStep 3864887 = 5797331) B5797331
theorem B2750777 : Blo 1144635 2750777 := bstep (se 2 (by rfl) ⟨1031541, by rfl⟩ : syracuseStep 2750777 = 2063083) B2063083
theorem B1145823 : Blo 1144635 1145823 := bstep (se 1 (by rfl) ⟨859367, by rfl⟩ : syracuseStep 1145823 = 1718735) B1718735
theorem B1145883 : Blo 1144635 1145883 := bstep (se 1 (by rfl) ⟨859412, by rfl⟩ : syracuseStep 1145883 = 1718825) B1718825
theorem B1932383 : Blo 1144635 1932383 := bstep (se 1 (by rfl) ⟨1449287, by rfl⟩ : syracuseStep 1932383 = 2898575) B2898575
theorem B3865697 : Blo 1144635 3865697 := bstep (se 2 (by rfl) ⟨1449636, by rfl⟩ : syracuseStep 3865697 = 2899273) B2899273
theorem B1146011 : Blo 1144635 1146011 := bstep (se 1 (by rfl) ⟨859508, by rfl⟩ : syracuseStep 1146011 = 1719017) B1719017
theorem B1932599 : Blo 1144635 1932599 := bstep (se 1 (by rfl) ⟨1449449, by rfl⟩ : syracuseStep 1932599 = 2898899) B2898899
theorem B5799275 : Blo 1144635 5799275 := bstep (se 1 (by rfl) ⟨4349456, by rfl⟩ : syracuseStep 5799275 = 8698913) B8698913
theorem B1146267 : Blo 1144635 1146267 := bstep (se 1 (by rfl) ⟨859700, by rfl⟩ : syracuseStep 1146267 = 1719401) B1719401
theorem B1146351 : Blo 1144635 1146351 := bstep (se 1 (by rfl) ⟨859763, by rfl⟩ : syracuseStep 1146351 = 1719527) B1719527
theorem B3866237 : Blo 1144635 3866237 := bstep (se 3 (by rfl) ⟨724919, by rfl⟩ : syracuseStep 3866237 = 1449839) B1449839
theorem B3669779 : Blo 1144635 3669779 := bstep (se 1 (by rfl) ⟨2752334, by rfl⟩ : syracuseStep 3669779 = 5504669) B5504669
theorem B3866399 : Blo 1144635 3866399 := bstep (se 1 (by rfl) ⟨2899799, by rfl⟩ : syracuseStep 3866399 = 5799599) B5799599
theorem B1146687 : Blo 1144635 1146687 := bstep (se 1 (by rfl) ⟨860015, by rfl⟩ : syracuseStep 1146687 = 1720031) B1720031
theorem B1146715 : Blo 1144635 1146715 := bstep (se 1 (by rfl) ⟨860036, by rfl⟩ : syracuseStep 1146715 = 1720073) B1720073
theorem B1146971 : Blo 1144635 1146971 := bstep (se 1 (by rfl) ⟨860228, by rfl⟩ : syracuseStep 1146971 = 1720457) B1720457
theorem B1147035 : Blo 1144635 1147035 := bstep (se 1 (by rfl) ⟨860276, by rfl⟩ : syracuseStep 1147035 = 1720553) B1720553
theorem B1147119 : Blo 1144635 1147119 := bstep (se 1 (by rfl) ⟨860339, by rfl⟩ : syracuseStep 1147119 = 1720679) B1720679
theorem B1147199 : Blo 1144635 1147199 := bstep (se 1 (by rfl) ⟨860399, by rfl⟩ : syracuseStep 1147199 = 1720799) B1720799
theorem B3867047 : Blo 1144635 3867047 := bstep (se 1 (by rfl) ⟨2900285, by rfl⟩ : syracuseStep 3867047 = 5800571) B5800571
theorem B1147367 : Blo 1144635 1147367 := bstep (se 1 (by rfl) ⟨860525, by rfl⟩ : syracuseStep 1147367 = 1721051) B1721051
theorem B4358843 : Blo 1144635 4358843 := bstep (se 1 (by rfl) ⟨3269132, by rfl⟩ : syracuseStep 4358843 = 6538265) B6538265
theorem B26804951 : Blo 1144635 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B1147643 : Blo 1144635 1147643 := bstep (se 1 (by rfl) ⟨860732, by rfl⟩ : syracuseStep 1147643 = 1721465) B1721465
theorem B1147775 : Blo 1144635 1147775 := bstep (se 1 (by rfl) ⟨860831, by rfl⟩ : syracuseStep 1147775 = 1721663) B1721663
theorem B4359041 : Blo 1144635 4359041 := bstep (se 2 (by rfl) ⟨1634640, by rfl⟩ : syracuseStep 4359041 = 3269281) B3269281
theorem B4359359 : Blo 1144635 4359359 := bstep (se 1 (by rfl) ⟨3269519, by rfl⟩ : syracuseStep 4359359 = 6539039) B6539039
theorem B1148223 : Blo 1144635 1148223 := bstep (se 1 (by rfl) ⟨861167, by rfl⟩ : syracuseStep 1148223 = 1722335) B1722335
theorem B1148263 : Blo 1144635 1148263 := bstep (se 1 (by rfl) ⟨861197, by rfl⟩ : syracuseStep 1148263 = 1722395) B1722395
theorem B3868073 : Blo 1144635 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B3671495 : Blo 1144635 3671495 := bstep (se 1 (by rfl) ⟨2753621, by rfl⟩ : syracuseStep 3671495 = 5507243) B5507243
theorem B1148367 : Blo 1144635 1148367 := bstep (se 1 (by rfl) ⟨861275, by rfl⟩ : syracuseStep 1148367 = 1722551) B1722551
theorem B1148383 : Blo 1144635 1148383 := bstep (se 1 (by rfl) ⟨861287, by rfl⟩ : syracuseStep 1148383 = 1722575) B1722575
theorem B5801543 : Blo 1144635 5801543 := bstep (se 1 (by rfl) ⟨4351157, by rfl⟩ : syracuseStep 5801543 = 8702315) B8702315
theorem B44730143 : Blo 1144635 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B3671855 : Blo 1144635 3671855 := bstep (se 1 (by rfl) ⟨2753891, by rfl⟩ : syracuseStep 3671855 = 5507783) B5507783
theorem B2066543 : Blo 1144635 2066543 := bstep (se 1 (by rfl) ⟨1549907, by rfl⟩ : syracuseStep 2066543 = 3099815) B3099815
theorem B23562859 : Blo 1144635 23562859 := bstep (se 1 (by rfl) ⟨17672144, by rfl⟩ : syracuseStep 23562859 = 35344289) B35344289
theorem B83627225 : Blo 1144635 83627225 := bstep (se 2 (by rfl) ⟨31360209, by rfl⟩ : syracuseStep 83627225 = 62720419) B62720419
theorem B1936703 : Blo 1144635 1936703 := bstep (se 1 (by rfl) ⟨1452527, by rfl⟩ : syracuseStep 1936703 = 2905055) B2905055
theorem B8719811 : Blo 1144635 8719811 := bstep (se 1 (by rfl) ⟨6539858, by rfl⟩ : syracuseStep 8719811 = 13079717) B13079717
theorem B4656761 : Blo 1144635 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B7344067 : Blo 1144635 7344067 := bstep (se 1 (by rfl) ⟨5508050, by rfl⟩ : syracuseStep 7344067 = 11016101) B11016101
theorem B3674251 : Blo 1144635 3674251 := bstep (se 1 (by rfl) ⟨2755688, by rfl⟩ : syracuseStep 3674251 = 5511377) B5511377
theorem B8950139 : Blo 1144635 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B1937911 : Blo 1144635 1937911 := bstep (se 1 (by rfl) ⟨1453433, by rfl⟩ : syracuseStep 1937911 = 2906867) B2906867
theorem B2069483 : Blo 1144635 2069483 := bstep (se 1 (by rfl) ⟨1552112, by rfl⟩ : syracuseStep 2069483 = 3104225) B3104225
theorem B1741895 : Blo 1144635 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B3872393 : Blo 1144635 3872393 := bstep (se 2 (by rfl) ⟨1452147, by rfl⟩ : syracuseStep 3872393 = 2904295) B2904295
theorem B9311897 : Blo 1144635 9311897 := bstep (se 2 (by rfl) ⟨3491961, by rfl⟩ : syracuseStep 9311897 = 6983923) B6983923
theorem B3872987 : Blo 1144635 3872987 := bstep (se 1 (by rfl) ⟨2904740, by rfl⟩ : syracuseStep 3872987 = 5809481) B5809481
theorem B5806889 : Blo 1144635 5806889 := bstep (se 2 (by rfl) ⟨2177583, by rfl⟩ : syracuseStep 5806889 = 4355167) B4355167
theorem B11017559 : Blo 1144635 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B6528377 : Blo 1144635 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B3874175 : Blo 1144635 3874175 := bstep (se 1 (by rfl) ⟨2905631, by rfl⟩ : syracuseStep 3874175 = 5811263) B5811263
theorem B16522649 : Blo 1144635 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B6529835 : Blo 1144635 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B19604267 : Blo 1144635 19604267 := bstep (se 1 (by rfl) ⟨14703200, by rfl⟩ : syracuseStep 19604267 = 29406401) B29406401
theorem B14689259 : Blo 1144635 14689259 := bstep (se 1 (by rfl) ⟨11016944, by rfl⟩ : syracuseStep 14689259 = 22033889) B22033889
theorem B3876065 : Blo 1144635 3876065 := bstep (se 2 (by rfl) ⟨1453524, by rfl⟩ : syracuseStep 3876065 = 2907049) B2907049
theorem B3876443 : Blo 1144635 3876443 := bstep (se 1 (by rfl) ⟨2907332, by rfl⟩ : syracuseStep 3876443 = 5814665) B5814665
theorem B1288255 : Blo 1144635 1288255 := bstep (se 1 (by rfl) ⟨966191, by rfl⟩ : syracuseStep 1288255 = 1932383) B1932383
theorem B1288399 : Blo 1144635 1288399 := bstep (se 1 (by rfl) ⟨966299, by rfl⟩ : syracuseStep 1288399 = 1932599) B1932599
theorem B2173225 : Blo 1144635 2173225 := bstep (se 2 (by rfl) ⟨814959, by rfl⟩ : syracuseStep 2173225 = 1629919) B1629919
theorem B2173787 : Blo 1144635 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B9808937 : Blo 1144635 9808937 := bstep (se 2 (by rfl) ⟨3678351, by rfl⟩ : syracuseStep 9808937 = 7356703) B7356703
theorem B1289407 : Blo 1144635 1289407 := bstep (se 1 (by rfl) ⟨967055, by rfl⟩ : syracuseStep 1289407 = 1934111) B1934111
theorem B2174843 : Blo 1144635 2174843 := bstep (se 1 (by rfl) ⟨1631132, by rfl⟩ : syracuseStep 2174843 = 3262265) B3262265
theorem B1717343 : Blo 1144635 1717343 := bstep (se 1 (by rfl) ⟨1288007, by rfl⟩ : syracuseStep 1717343 = 2576015) B2576015
theorem B1717403 : Blo 1144635 1717403 := bstep (se 1 (by rfl) ⟨1288052, by rfl⟩ : syracuseStep 1717403 = 2576105) B2576105
theorem B13219337 : Blo 1144635 13219337 := bstep (se 2 (by rfl) ⟨4957251, by rfl⟩ : syracuseStep 13219337 = 9914503) B9914503
theorem B8828441 : Blo 1144635 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B2176703 : Blo 1144635 2176703 := bstep (se 1 (by rfl) ⟨1632527, by rfl⟩ : syracuseStep 2176703 = 3265055) B3265055
theorem B2176787 : Blo 1144635 2176787 := bstep (se 1 (by rfl) ⟨1632590, by rfl⟩ : syracuseStep 2176787 = 3265181) B3265181
theorem B1718249 : Blo 1144635 1718249 := bstep (se 2 (by rfl) ⟨644343, by rfl⟩ : syracuseStep 1718249 = 1288687) B1288687
theorem B2209913 : Blo 1144635 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B1718879 : Blo 1144635 1718879 := bstep (se 1 (by rfl) ⟨1289159, by rfl⟩ : syracuseStep 1718879 = 2578319) B2578319
theorem B2177903 : Blo 1144635 2177903 := bstep (se 1 (by rfl) ⟨1633427, by rfl⟩ : syracuseStep 2177903 = 3266855) B3266855
theorem B1915759 : Blo 1144635 1915759 := bstep (se 1 (by rfl) ⟨1436819, by rfl⟩ : syracuseStep 1915759 = 2873639) B2873639
theorem B1719359 : Blo 1144635 1719359 := bstep (se 1 (by rfl) ⟨1289519, by rfl⟩ : syracuseStep 1719359 = 2579039) B2579039
theorem B1719707 : Blo 1144635 1719707 := bstep (se 1 (by rfl) ⟨1289780, by rfl⟩ : syracuseStep 1719707 = 2579561) B2579561
theorem B2899435 : Blo 1144635 2899435 := bstep (se 1 (by rfl) ⟨2174576, by rfl⟩ : syracuseStep 2899435 = 4349153) B4349153
theorem B1720127 : Blo 1144635 1720127 := bstep (se 1 (by rfl) ⟨1290095, by rfl⟩ : syracuseStep 1720127 = 2580191) B2580191
theorem B1720367 : Blo 1144635 1720367 := bstep (se 1 (by rfl) ⟨1290275, by rfl⟩ : syracuseStep 1720367 = 2580551) B2580551
theorem B1720391 : Blo 1144635 1720391 := bstep (se 1 (by rfl) ⟨1290293, by rfl⟩ : syracuseStep 1720391 = 2580587) B2580587
theorem B9781357 : Blo 1144635 9781357 := bstep (se 3 (by rfl) ⟨1834004, by rfl⟩ : syracuseStep 9781357 = 3668009) B3668009
theorem B1720571 : Blo 1144635 1720571 := bstep (se 1 (by rfl) ⟨1290428, by rfl⟩ : syracuseStep 1720571 = 2580857) B2580857
theorem B6537581 : Blo 1144635 6537581 := bstep (se 3 (by rfl) ⟨1225796, by rfl⟩ : syracuseStep 6537581 = 2451593) B2451593
theorem B1720697 : Blo 1144635 1720697 := bstep (se 2 (by rfl) ⟨645261, by rfl⟩ : syracuseStep 1720697 = 1290523) B1290523
theorem B1720859 : Blo 1144635 1720859 := bstep (se 1 (by rfl) ⟨1290644, by rfl⟩ : syracuseStep 1720859 = 2581289) B2581289
theorem B1720991 : Blo 1144635 1720991 := bstep (se 1 (by rfl) ⟨1290743, by rfl⟩ : syracuseStep 1720991 = 2581487) B2581487
theorem B1721039 : Blo 1144635 1721039 := bstep (se 1 (by rfl) ⟨1290779, by rfl⟩ : syracuseStep 1721039 = 2581559) B2581559
theorem B2900731 : Blo 1144635 2900731 := bstep (se 1 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 2900731 = 4351097) B4351097
theorem B1721159 : Blo 1144635 1721159 := bstep (se 1 (by rfl) ⟨1290869, by rfl⟩ : syracuseStep 1721159 = 2581739) B2581739
theorem B2900873 : Blo 1144635 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B1721225 : Blo 1144635 1721225 := bstep (se 2 (by rfl) ⟨645459, by rfl⟩ : syracuseStep 1721225 = 1290919) B1290919
theorem B55788851 : Blo 1144635 55788851 := bstep (se 1 (by rfl) ⟨41841638, by rfl⟩ : syracuseStep 55788851 = 83683277) B83683277
theorem B19842515 : Blo 1144635 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B5883475 : Blo 1144635 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B107235353 : Blo 1144635 107235353 := bstep (se 2 (by rfl) ⟨40213257, by rfl⟩ : syracuseStep 107235353 = 80426515) B80426515
theorem B4901735 : Blo 1144635 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B7555949 : Blo 1144635 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B62705117 : Blo 1144635 62705117 := bstep (se 3 (by rfl) ⟨11757209, by rfl⟩ : syracuseStep 62705117 = 23514419) B23514419
theorem B10472935 : Blo 1144635 10472935 := bstep (se 1 (by rfl) ⟨7854701, by rfl⟩ : syracuseStep 10472935 = 15709403) B15709403
theorem B8703773 : Blo 1144635 8703773 := bstep (se 3 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 8703773 = 3263915) B3263915
theorem B2576591 : Blo 1144635 2576591 := bstep (se 1 (by rfl) ⟨1932443, by rfl⟩ : syracuseStep 2576591 = 3864887) B3864887
theorem B79450429 : Blo 1144635 79450429 := bstep (se 3 (by rfl) ⟨14896955, by rfl⟩ : syracuseStep 79450429 = 29793911) B29793911
theorem B2577131 : Blo 1144635 2577131 := bstep (se 1 (by rfl) ⟨1932848, by rfl⟩ : syracuseStep 2577131 = 3865697) B3865697
theorem B22008671 : Blo 1144635 22008671 := bstep (se 1 (by rfl) ⟨16506503, by rfl⟩ : syracuseStep 22008671 = 33013007) B33013007
theorem B2577491 : Blo 1144635 2577491 := bstep (se 1 (by rfl) ⟨1933118, by rfl⟩ : syracuseStep 2577491 = 3866237) B3866237
theorem B2905217 : Blo 1144635 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B2446519 : Blo 1144635 2446519 := bstep (se 1 (by rfl) ⟨1834889, by rfl⟩ : syracuseStep 2446519 = 3669779) B3669779
theorem B2577599 : Blo 1144635 2577599 := bstep (se 1 (by rfl) ⟨1933199, by rfl⟩ : syracuseStep 2577599 = 3866399) B3866399
theorem B2446843 : Blo 1144635 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B19617389 : Blo 1144635 19617389 := bstep (se 3 (by rfl) ⟨3678260, by rfl⟩ : syracuseStep 19617389 = 7356521) B7356521
theorem B3266239 : Blo 1144635 3266239 := bstep (se 1 (by rfl) ⟨2449679, by rfl⟩ : syracuseStep 3266239 = 4899359) B4899359
theorem B4904657 : Blo 1144635 4904657 := bstep (se 2 (by rfl) ⟨1839246, by rfl⟩ : syracuseStep 4904657 = 3678493) B3678493
theorem B4347695 : Blo 1144635 4347695 := bstep (se 1 (by rfl) ⟨3260771, by rfl⟩ : syracuseStep 4347695 = 6521543) B6521543
theorem B8706689 : Blo 1144635 8706689 := bstep (se 2 (by rfl) ⟨3265008, by rfl⟩ : syracuseStep 8706689 = 6530017) B6530017
theorem B3922751 : Blo 1144635 3922751 := bstep (se 1 (by rfl) ⟨2942063, by rfl⟩ : syracuseStep 3922751 = 5884127) B5884127
theorem B2907161 : Blo 1144635 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B4643881 : Blo 1144635 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B2579615 : Blo 1144635 2579615 := bstep (se 1 (by rfl) ⟨1934711, by rfl⟩ : syracuseStep 2579615 = 3869423) B3869423
theorem B2907323 : Blo 1144635 2907323 := bstep (se 1 (by rfl) ⟨2180492, by rfl⟩ : syracuseStep 2907323 = 4360985) B4360985
theorem B2579867 : Blo 1144635 2579867 := bstep (se 1 (by rfl) ⟨1934900, by rfl⟩ : syracuseStep 2579867 = 3869801) B3869801
theorem B2449595 : Blo 1144635 2449595 := bstep (se 1 (by rfl) ⟨1837196, by rfl⟩ : syracuseStep 2449595 = 3674393) B3674393
theorem B1958455 : Blo 1144635 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B4645439 : Blo 1144635 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B5890697 : Blo 1144635 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B6972247 : Blo 1144635 6972247 := bstep (se 1 (by rfl) ⟨5229185, by rfl⟩ : syracuseStep 6972247 = 10458371) B10458371
theorem B3269497 : Blo 1144635 3269497 := bstep (se 2 (by rfl) ⟨1226061, by rfl⟩ : syracuseStep 3269497 = 2452123) B2452123
theorem B4187009 : Blo 1144635 4187009 := bstep (se 2 (by rfl) ⟨1570128, by rfl⟩ : syracuseStep 4187009 = 3140257) B3140257
theorem B18605051 : Blo 1144635 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B4351067 : Blo 1144635 4351067 := bstep (se 1 (by rfl) ⟨3263300, by rfl⟩ : syracuseStep 4351067 = 6526601) B6526601
theorem B1631497 : Blo 1144635 1631497 := bstep (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) B1223623
theorem B2581919 : Blo 1144635 2581919 := bstep (se 1 (by rfl) ⟨1936439, by rfl⟩ : syracuseStep 2581919 = 3872879) B3872879
theorem B2582153 : Blo 1144635 2582153 := bstep (se 2 (by rfl) ⟨968307, by rfl⟩ : syracuseStep 2582153 = 1936615) B1936615
theorem B2582171 : Blo 1144635 2582171 := bstep (se 1 (by rfl) ⟨1936628, by rfl⟩ : syracuseStep 2582171 = 3873257) B3873257
theorem B2582207 : Blo 1144635 2582207 := bstep (se 1 (by rfl) ⟨1936655, by rfl⟩ : syracuseStep 2582207 = 3873311) B3873311
theorem B3270887 : Blo 1144635 3270887 := bstep (se 1 (by rfl) ⟨2453165, by rfl⟩ : syracuseStep 3270887 = 4906331) B4906331
theorem B2583143 : Blo 1144635 2583143 := bstep (se 1 (by rfl) ⟨1937357, by rfl⟩ : syracuseStep 2583143 = 3874715) B3874715
theorem B2584223 : Blo 1144635 2584223 := bstep (se 1 (by rfl) ⟨1938167, by rfl⟩ : syracuseStep 2584223 = 3876335) B3876335
theorem B5795711 : Blo 1144635 5795711 := bstep (se 1 (by rfl) ⟨4346783, by rfl⟩ : syracuseStep 5795711 = 8693567) B8693567
theorem B4354955 : Blo 1144635 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B37680029 : Blo 1144635 37680029 := bstep (se 3 (by rfl) ⟨7065005, by rfl⟩ : syracuseStep 37680029 = 14130011) B14130011
theorem B1144687 : Blo 1144635 1144687 := bstep (se 1 (by rfl) ⟨858515, by rfl⟩ : syracuseStep 1144687 = 1717031) B1717031
theorem B1144767 : Blo 1144635 1144767 := bstep (se 1 (by rfl) ⟨858575, by rfl⟩ : syracuseStep 1144767 = 1717151) B1717151
theorem B4126859 : Blo 1144635 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B1145083 : Blo 1144635 1145083 := bstep (se 1 (by rfl) ⟨858812, by rfl⟩ : syracuseStep 1145083 = 1717625) B1717625
theorem B1145087 : Blo 1144635 1145087 := bstep (se 1 (by rfl) ⟨858815, by rfl⟩ : syracuseStep 1145087 = 1717631) B1717631
theorem B15694117 : Blo 1144635 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B1145191 : Blo 1144635 1145191 := bstep (se 1 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 1145191 = 1717787) B1717787
theorem B2062751 : Blo 1144635 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B1145311 : Blo 1144635 1145311 := bstep (se 1 (by rfl) ⟨858983, by rfl⟩ : syracuseStep 1145311 = 1717967) B1717967
theorem B3865103 : Blo 1144635 3865103 := bstep (se 1 (by rfl) ⟨2898827, by rfl⟩ : syracuseStep 3865103 = 5797655) B5797655
theorem B1145447 : Blo 1144635 1145447 := bstep (se 1 (by rfl) ⟨859085, by rfl⟩ : syracuseStep 1145447 = 1718171) B1718171
theorem B1145471 : Blo 1144635 1145471 := bstep (se 1 (by rfl) ⟨859103, by rfl⟩ : syracuseStep 1145471 = 1718207) B1718207
theorem B18152099 : Blo 1144635 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B1145583 : Blo 1144635 1145583 := bstep (se 1 (by rfl) ⟨859187, by rfl⟩ : syracuseStep 1145583 = 1718375) B1718375
theorem B9796463 : Blo 1144635 9796463 := bstep (se 1 (by rfl) ⟨7347347, by rfl⟩ : syracuseStep 9796463 = 14694695) B14694695
theorem B1833851 : Blo 1144635 1833851 := bstep (se 1 (by rfl) ⟨1375388, by rfl⟩ : syracuseStep 1833851 = 2750777) B2750777
theorem B1145839 : Blo 1144635 1145839 := bstep (se 1 (by rfl) ⟨859379, by rfl⟩ : syracuseStep 1145839 = 1718759) B1718759
theorem B1145887 : Blo 1144635 1145887 := bstep (se 1 (by rfl) ⟨859415, by rfl⟩ : syracuseStep 1145887 = 1718831) B1718831
theorem B44629109 : Blo 1144635 44629109 := bstep (se 5 (by rfl) ⟨2091989, by rfl⟩ : syracuseStep 44629109 = 4183979) B4183979
theorem B1146335 : Blo 1144635 1146335 := bstep (se 1 (by rfl) ⟨859751, by rfl⟩ : syracuseStep 1146335 = 1719503) B1719503
theorem B1146395 : Blo 1144635 1146395 := bstep (se 1 (by rfl) ⟨859796, by rfl⟩ : syracuseStep 1146395 = 1719593) B1719593
theorem B1146415 : Blo 1144635 1146415 := bstep (se 1 (by rfl) ⟨859811, by rfl⟩ : syracuseStep 1146415 = 1719623) B1719623
theorem B3866183 : Blo 1144635 3866183 := bstep (se 1 (by rfl) ⟨2899637, by rfl⟩ : syracuseStep 3866183 = 5799275) B5799275
theorem B16547561 : Blo 1144635 16547561 := bstep (se 2 (by rfl) ⟨6205335, by rfl⟩ : syracuseStep 16547561 = 12410671) B12410671
theorem B1933247 : Blo 1144635 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B4358083 : Blo 1144635 4358083 := bstep (se 1 (by rfl) ⟨3268562, by rfl⟩ : syracuseStep 4358083 = 6537125) B6537125
theorem B1146815 : Blo 1144635 1146815 := bstep (se 1 (by rfl) ⟨860111, by rfl⟩ : syracuseStep 1146815 = 1720223) B1720223
theorem B1146875 : Blo 1144635 1146875 := bstep (se 1 (by rfl) ⟨860156, by rfl⟩ : syracuseStep 1146875 = 1720313) B1720313
theorem B1146911 : Blo 1144635 1146911 := bstep (se 1 (by rfl) ⟨860183, by rfl⟩ : syracuseStep 1146911 = 1720367) B1720367
theorem B1146927 : Blo 1144635 1146927 := bstep (se 1 (by rfl) ⟨860195, by rfl⟩ : syracuseStep 1146927 = 1720391) B1720391
theorem B13041809 : Blo 1144635 13041809 := bstep (se 2 (by rfl) ⟨4890678, by rfl⟩ : syracuseStep 13041809 = 9781357) B9781357
theorem B1147047 : Blo 1144635 1147047 := bstep (se 1 (by rfl) ⟨860285, by rfl⟩ : syracuseStep 1147047 = 1720571) B1720571
theorem B4358387 : Blo 1144635 4358387 := bstep (se 1 (by rfl) ⟨3268790, by rfl⟩ : syracuseStep 4358387 = 6537581) B6537581
theorem B1147131 : Blo 1144635 1147131 := bstep (se 1 (by rfl) ⟨860348, by rfl⟩ : syracuseStep 1147131 = 1720697) B1720697
theorem B1147239 : Blo 1144635 1147239 := bstep (se 1 (by rfl) ⟨860429, by rfl⟩ : syracuseStep 1147239 = 1720859) B1720859
theorem B1147327 : Blo 1144635 1147327 := bstep (se 1 (by rfl) ⟨860495, by rfl⟩ : syracuseStep 1147327 = 1720991) B1720991
theorem B1147359 : Blo 1144635 1147359 := bstep (se 1 (by rfl) ⟨860519, by rfl⟩ : syracuseStep 1147359 = 1721039) B1721039
theorem B1147439 : Blo 1144635 1147439 := bstep (se 1 (by rfl) ⟨860579, by rfl⟩ : syracuseStep 1147439 = 1721159) B1721159
theorem B1933915 : Blo 1144635 1933915 := bstep (se 1 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 1933915 = 2900873) B2900873
theorem B1147483 : Blo 1144635 1147483 := bstep (se 1 (by rfl) ⟨860612, by rfl⟩ : syracuseStep 1147483 = 1721225) B1721225
theorem B37192567 : Blo 1144635 37192567 := bstep (se 1 (by rfl) ⟨27894425, by rfl⟩ : syracuseStep 37192567 = 55788851) B55788851
theorem B3867641 : Blo 1144635 3867641 := bstep (se 2 (by rfl) ⟨1450365, by rfl⟩ : syracuseStep 3867641 = 2900731) B2900731
theorem B3867695 : Blo 1144635 3867695 := bstep (se 1 (by rfl) ⟨2900771, by rfl⟩ : syracuseStep 3867695 = 5801543) B5801543
theorem B4359329 : Blo 1144635 4359329 := bstep (se 2 (by rfl) ⟨1634748, by rfl⟩ : syracuseStep 4359329 = 3269497) B3269497
theorem B29820095 : Blo 1144635 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B1377695 : Blo 1144635 1377695 := bstep (se 1 (by rfl) ⟨1033271, by rfl⟩ : syracuseStep 1377695 = 2066543) B2066543
theorem B5802515 : Blo 1144635 5802515 := bstep (se 1 (by rfl) ⟨4351886, by rfl⟩ : syracuseStep 5802515 = 8703773) B8703773
theorem B5966759 : Blo 1144635 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B1936811 : Blo 1144635 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B13078259 : Blo 1144635 13078259 := bstep (se 1 (by rfl) ⟨9808694, by rfl⟩ : syracuseStep 13078259 = 19617389) B19617389
theorem B5804459 : Blo 1144635 5804459 := bstep (se 1 (by rfl) ⟨4353344, by rfl⟩ : syracuseStep 5804459 = 8706689) B8706689
theorem B3871259 : Blo 1144635 3871259 := bstep (se 1 (by rfl) ⟨2903444, by rfl⟩ : syracuseStep 3871259 = 5806889) B5806889
theorem B13963913 : Blo 1144635 13963913 := bstep (se 2 (by rfl) ⟨5236467, by rfl⟩ : syracuseStep 13963913 = 10472935) B10472935
theorem B1938107 : Blo 1144635 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B1938215 : Blo 1144635 1938215 := bstep (se 1 (by rfl) ⟨1453661, by rfl⟩ : syracuseStep 1938215 = 2907323) B2907323
theorem B11015099 : Blo 1144635 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B1449191 : Blo 1144635 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B10460669 : Blo 1144635 10460669 := bstep (se 3 (by rfl) ⟨1961375, by rfl⟩ : syracuseStep 10460669 = 3922751) B3922751
theorem B4890269 : Blo 1144635 4890269 := bstep (se 3 (by rfl) ⟨916925, by rfl⟩ : syracuseStep 4890269 = 1833851) B1833851
theorem B1449895 : Blo 1144635 1449895 := bstep (se 1 (by rfl) ⟨1087421, by rfl⟩ : syracuseStep 1449895 = 2174843) B2174843
theorem B1451135 : Blo 1144635 1451135 := bstep (se 1 (by rfl) ⟨1088351, by rfl⟩ : syracuseStep 1451135 = 2176703) B2176703
theorem B1451191 : Blo 1144635 1451191 := bstep (se 1 (by rfl) ⟨1088393, by rfl⟩ : syracuseStep 1451191 = 2176787) B2176787
theorem B12101399 : Blo 1144635 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B6530975 : Blo 1144635 6530975 := bstep (se 1 (by rfl) ⟨4898231, by rfl⟩ : syracuseStep 6530975 = 9796463) B9796463
theorem B1451935 : Blo 1144635 1451935 := bstep (se 1 (by rfl) ⟨1088951, by rfl⟩ : syracuseStep 1451935 = 2177903) B2177903
theorem B5810777 : Blo 1144635 5810777 := bstep (se 2 (by rfl) ⟨2179041, by rfl⟩ : syracuseStep 5810777 = 4358083) B4358083
theorem B1288831 : Blo 1144635 1288831 := bstep (se 1 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 1288831 = 1933247) B1933247
theorem B17869967 : Blo 1144635 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B2175329 : Blo 1144635 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B7844633 : Blo 1144635 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B55751483 : Blo 1144635 55751483 := bstep (se 1 (by rfl) ⟨41813612, by rfl⟩ : syracuseStep 55751483 = 83627225) B83627225
theorem B1291135 : Blo 1144635 1291135 := bstep (se 1 (by rfl) ⟨968351, by rfl⟩ : syracuseStep 1291135 = 1936703) B1936703
theorem B5813207 : Blo 1144635 5813207 := bstep (se 1 (by rfl) ⟨4359905, by rfl⟩ : syracuseStep 5813207 = 8719811) B8719811
theorem B5518621 : Blo 1144635 5518621 := bstep (se 3 (by rfl) ⟨1034741, by rfl⟩ : syracuseStep 5518621 = 2069483) B2069483
theorem B1717673 : Blo 1144635 1717673 := bstep (se 2 (by rfl) ⟨644127, by rfl⟩ : syracuseStep 1717673 = 1288255) B1288255
theorem B1717727 : Blo 1144635 1717727 := bstep (se 1 (by rfl) ⟨1288295, by rfl⟩ : syracuseStep 1717727 = 2576591) B2576591
theorem B1717865 : Blo 1144635 1717865 := bstep (se 2 (by rfl) ⟨644199, by rfl⟩ : syracuseStep 1717865 = 1288399) B1288399
theorem B2897633 : Blo 1144635 2897633 := bstep (se 2 (by rfl) ⟨1086612, by rfl⟩ : syracuseStep 2897633 = 2173225) B2173225
theorem B1718087 : Blo 1144635 1718087 := bstep (se 1 (by rfl) ⟨1288565, by rfl⟩ : syracuseStep 1718087 = 2577131) B2577131
theorem B1161263 : Blo 1144635 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B1718327 : Blo 1144635 1718327 := bstep (se 1 (by rfl) ⟨1288745, by rfl⟩ : syracuseStep 1718327 = 2577491) B2577491
theorem B1718399 : Blo 1144635 1718399 := bstep (se 1 (by rfl) ⟨1288799, by rfl⟩ : syracuseStep 1718399 = 2577599) B2577599
theorem B6207931 : Blo 1144635 6207931 := bstep (se 1 (by rfl) ⟨4655948, by rfl⟩ : syracuseStep 6207931 = 9311897) B9311897
theorem B2898463 : Blo 1144635 2898463 := bstep (se 1 (by rfl) ⟨2173847, by rfl⟩ : syracuseStep 2898463 = 4347695) B4347695
theorem B1719209 : Blo 1144635 1719209 := bstep (se 2 (by rfl) ⟨644703, by rfl⟩ : syracuseStep 1719209 = 1289407) B1289407
theorem B22002677 : Blo 1144635 22002677 := bstep (se 5 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 22002677 = 2062751) B2062751
theorem B1719743 : Blo 1144635 1719743 := bstep (se 1 (by rfl) ⟨1289807, by rfl⟩ : syracuseStep 1719743 = 2579615) B2579615
theorem B1719911 : Blo 1144635 1719911 := bstep (se 1 (by rfl) ⟨1289933, by rfl⟩ : syracuseStep 1719911 = 2579867) B2579867
theorem B4899001 : Blo 1144635 4899001 := bstep (se 2 (by rfl) ⟨1837125, by rfl⟩ : syracuseStep 4899001 = 3674251) B3674251
theorem B3096959 : Blo 1144635 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B12403367 : Blo 1144635 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B2900711 : Blo 1144635 2900711 := bstep (se 1 (by rfl) ⟨2175533, by rfl⟩ : syracuseStep 2900711 = 4351067) B4351067
theorem B334807829 : Blo 1144635 334807829 := bstep (se 6 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 334807829 = 15694117) B15694117
theorem B1721279 : Blo 1144635 1721279 := bstep (se 1 (by rfl) ⟨1290959, by rfl⟩ : syracuseStep 1721279 = 2581919) B2581919
theorem B1721435 : Blo 1144635 1721435 := bstep (se 1 (by rfl) ⟨1291076, by rfl⟩ : syracuseStep 1721435 = 2582153) B2582153
theorem B1721447 : Blo 1144635 1721447 := bstep (se 1 (by rfl) ⟨1291085, by rfl⟩ : syracuseStep 1721447 = 2582171) B2582171
theorem B1721471 : Blo 1144635 1721471 := bstep (se 1 (by rfl) ⟨1291103, by rfl⟩ : syracuseStep 1721471 = 2582207) B2582207
theorem B2180591 : Blo 1144635 2180591 := bstep (se 1 (by rfl) ⟨1635443, by rfl⟩ : syracuseStep 2180591 = 3270887) B3270887
theorem B3262025 : Blo 1144635 3262025 := bstep (se 2 (by rfl) ⟨1223259, by rfl⟩ : syracuseStep 3262025 = 2446519) B2446519
theorem B1722095 : Blo 1144635 1722095 := bstep (se 1 (by rfl) ⟨1291571, by rfl⟩ : syracuseStep 1722095 = 2583143) B2583143
theorem B3262457 : Blo 1144635 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B6539291 : Blo 1144635 6539291 := bstep (se 1 (by rfl) ⟨4904468, by rfl⟩ : syracuseStep 6539291 = 9808937) B9808937
theorem B1722815 : Blo 1144635 1722815 := bstep (se 1 (by rfl) ⟨1292111, by rfl⟩ : syracuseStep 1722815 = 2584223) B2584223
theorem B2903303 : Blo 1144635 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B25120019 : Blo 1144635 25120019 := bstep (se 1 (by rfl) ⟨18840014, by rfl⟩ : syracuseStep 25120019 = 37680029) B37680029
theorem B29380157 : Blo 1144635 29380157 := bstep (se 3 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 29380157 = 11017559) B11017559
theorem B5885627 : Blo 1144635 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B2576735 : Blo 1144635 2576735 := bstep (se 1 (by rfl) ⟨1932551, by rfl⟩ : syracuseStep 2576735 = 3865103) B3865103
theorem B2577455 : Blo 1144635 2577455 := bstep (se 1 (by rfl) ⟨1933091, by rfl⟩ : syracuseStep 2577455 = 3866183) B3866183
theorem B11031707 : Blo 1144635 11031707 := bstep (se 1 (by rfl) ⟨8273780, by rfl⟩ : syracuseStep 11031707 = 16547561) B16547561
theorem B2578031 : Blo 1144635 2578031 := bstep (se 1 (by rfl) ⟨1933523, by rfl⟩ : syracuseStep 2578031 = 3867047) B3867047
theorem B2905895 : Blo 1144635 2905895 := bstep (se 1 (by rfl) ⟨2179421, by rfl⟩ : syracuseStep 2905895 = 4358843) B4358843
theorem B2906027 : Blo 1144635 2906027 := bstep (se 1 (by rfl) ⟨2179520, by rfl⟩ : syracuseStep 2906027 = 4359041) B4359041
theorem B2611273 : Blo 1144635 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B2906239 : Blo 1144635 2906239 := bstep (se 1 (by rfl) ⟨2179679, by rfl⟩ : syracuseStep 2906239 = 4359359) B4359359
theorem B2578715 : Blo 1144635 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B2447663 : Blo 1144635 2447663 := bstep (se 1 (by rfl) ⟨1835747, by rfl⟩ : syracuseStep 2447663 = 3671495) B3671495
theorem B13228343 : Blo 1144635 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B9296329 : Blo 1144635 9296329 := bstep (se 2 (by rfl) ⟨3486123, by rfl⟩ : syracuseStep 9296329 = 6972247) B6972247
theorem B2447903 : Blo 1144635 2447903 := bstep (se 1 (by rfl) ⟨1835927, by rfl⟩ : syracuseStep 2447903 = 3671855) B3671855
theorem B71490235 : Blo 1144635 71490235 := bstep (se 1 (by rfl) ⟨53617676, by rfl⟩ : syracuseStep 71490235 = 107235353) B107235353
theorem B3267823 : Blo 1144635 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B5037299 : Blo 1144635 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B41803411 : Blo 1144635 41803411 := bstep (se 1 (by rfl) ⟨31352558, by rfl⟩ : syracuseStep 41803411 = 62705117) B62705117
theorem B11165357 : Blo 1144635 11165357 := bstep (se 3 (by rfl) ⟨2093504, by rfl⟩ : syracuseStep 11165357 = 4187009) B4187009
theorem B3104507 : Blo 1144635 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B14672447 : Blo 1144635 14672447 := bstep (se 1 (by rfl) ⟨11004335, by rfl⟩ : syracuseStep 14672447 = 22008671) B22008671
theorem B31417145 : Blo 1144635 31417145 := bstep (se 2 (by rfl) ⟨11781429, by rfl⟩ : syracuseStep 31417145 = 23562859) B23562859
theorem B2581595 : Blo 1144635 2581595 := bstep (se 1 (by rfl) ⟨1936196, by rfl⟩ : syracuseStep 2581595 = 3872393) B3872393
theorem B3269771 : Blo 1144635 3269771 := bstep (se 1 (by rfl) ⟨2452328, by rfl⟩ : syracuseStep 3269771 = 4904657) B4904657
theorem B2581991 : Blo 1144635 2581991 := bstep (se 1 (by rfl) ⟨1936493, by rfl⟩ : syracuseStep 2581991 = 3872987) B3872987
theorem B4352251 : Blo 1144635 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B2582783 : Blo 1144635 2582783 := bstep (se 1 (by rfl) ⟨1937087, by rfl⟩ : syracuseStep 2582783 = 3874175) B3874175
theorem B9792089 : Blo 1144635 9792089 := bstep (se 2 (by rfl) ⟨3672033, by rfl⟩ : syracuseStep 9792089 = 7344067) B7344067
theorem B1633063 : Blo 1144635 1633063 := bstep (se 1 (by rfl) ⟨1224797, by rfl⟩ : syracuseStep 1633063 = 2449595) B2449595
theorem B24767365 : Blo 1144635 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B105933905 : Blo 1144635 105933905 := bstep (se 2 (by rfl) ⟨39725214, by rfl⟩ : syracuseStep 105933905 = 79450429) B79450429
theorem B3927131 : Blo 1144635 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B4353223 : Blo 1144635 4353223 := bstep (se 1 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 4353223 = 6529835) B6529835
theorem B13069511 : Blo 1144635 13069511 := bstep (se 1 (by rfl) ⟨9802133, by rfl⟩ : syracuseStep 13069511 = 19604267) B19604267
theorem B9792839 : Blo 1144635 9792839 := bstep (se 1 (by rfl) ⟨7344629, by rfl⟩ : syracuseStep 9792839 = 14689259) B14689259
theorem B2583881 : Blo 1144635 2583881 := bstep (se 2 (by rfl) ⟨968955, by rfl⟩ : syracuseStep 2583881 = 1937911) B1937911
theorem B2584043 : Blo 1144635 2584043 := bstep (se 1 (by rfl) ⟨1938032, by rfl⟩ : syracuseStep 2584043 = 3876065) B3876065
theorem B2584295 : Blo 1144635 2584295 := bstep (se 1 (by rfl) ⟨1938221, by rfl⟩ : syracuseStep 2584295 = 3876443) B3876443
theorem B4354985 : Blo 1144635 4354985 := bstep (se 2 (by rfl) ⟨1633119, by rfl⟩ : syracuseStep 4354985 = 3266239) B3266239
theorem B3863807 : Blo 1144635 3863807 := bstep (se 1 (by rfl) ⟨2897855, by rfl⟩ : syracuseStep 3863807 = 5795711) B5795711
theorem B1144895 : Blo 1144635 1144895 := bstep (se 1 (by rfl) ⟨858671, by rfl⟩ : syracuseStep 1144895 = 1717343) B1717343
theorem B1144935 : Blo 1144635 1144935 := bstep (se 1 (by rfl) ⟨858701, by rfl⟩ : syracuseStep 1144935 = 1717403) B1717403
theorem B8812891 : Blo 1144635 8812891 := bstep (se 1 (by rfl) ⟨6609668, by rfl⟩ : syracuseStep 8812891 = 13219337) B13219337
theorem B2554345 : Blo 1144635 2554345 := bstep (se 2 (by rfl) ⟨957879, by rfl⟩ : syracuseStep 2554345 = 1915759) B1915759
theorem B1145499 : Blo 1144635 1145499 := bstep (se 1 (by rfl) ⟨859124, by rfl⟩ : syracuseStep 1145499 = 1718249) B1718249
theorem B1473275 : Blo 1144635 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B2751239 : Blo 1144635 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B1145919 : Blo 1144635 1145919 := bstep (se 1 (by rfl) ⟨859439, by rfl⟩ : syracuseStep 1145919 = 1718879) B1718879
theorem B3865913 : Blo 1144635 3865913 := bstep (se 2 (by rfl) ⟨1449717, by rfl⟩ : syracuseStep 3865913 = 2899435) B2899435
theorem B1146239 : Blo 1144635 1146239 := bstep (se 1 (by rfl) ⟨859679, by rfl⟩ : syracuseStep 1146239 = 1719359) B1719359
theorem B29752739 : Blo 1144635 29752739 := bstep (se 1 (by rfl) ⟨22314554, by rfl⟩ : syracuseStep 29752739 = 44629109) B44629109
theorem B1146471 : Blo 1144635 1146471 := bstep (se 1 (by rfl) ⟨859853, by rfl⟩ : syracuseStep 1146471 = 1719707) B1719707
theorem B1146751 : Blo 1144635 1146751 := bstep (se 1 (by rfl) ⟨860063, by rfl⟩ : syracuseStep 1146751 = 1720127) B1720127
theorem B1933807 : Blo 1144635 1933807 := bstep (se 1 (by rfl) ⟨1450355, by rfl⟩ : syracuseStep 1933807 = 2900711) B2900711
theorem B1147519 : Blo 1144635 1147519 := bstep (se 1 (by rfl) ⟨860639, by rfl⟩ : syracuseStep 1147519 = 1721279) B1721279
theorem B1147623 : Blo 1144635 1147623 := bstep (se 1 (by rfl) ⟨860717, by rfl⟩ : syracuseStep 1147623 = 1721435) B1721435
theorem B1147631 : Blo 1144635 1147631 := bstep (se 1 (by rfl) ⟨860723, by rfl⟩ : syracuseStep 1147631 = 1721447) B1721447
theorem B1147647 : Blo 1144635 1147647 := bstep (se 1 (by rfl) ⟨860735, by rfl⟩ : syracuseStep 1147647 = 1721471) B1721471
theorem B8258557 : Blo 1144635 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B1148063 : Blo 1144635 1148063 := bstep (se 1 (by rfl) ⟨861047, by rfl⟩ : syracuseStep 1148063 = 1722095) B1722095
theorem B4359527 : Blo 1144635 4359527 := bstep (se 1 (by rfl) ⟨3269645, by rfl⟩ : syracuseStep 4359527 = 6539291) B6539291
theorem B1934921 : Blo 1144635 1934921 := bstep (se 2 (by rfl) ⟨725595, by rfl⟩ : syracuseStep 1934921 = 1451191) B1451191
theorem B1148543 : Blo 1144635 1148543 := bstep (se 1 (by rfl) ⟨861407, by rfl⟩ : syracuseStep 1148543 = 1722815) B1722815
theorem B3868343 : Blo 1144635 3868343 := bstep (se 1 (by rfl) ⟨2901257, by rfl⟩ : syracuseStep 3868343 = 5802515) B5802515
theorem B1935535 : Blo 1144635 1935535 := bstep (se 1 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 1935535 = 2903303) B2903303
theorem B16746679 : Blo 1144635 16746679 := bstep (se 1 (by rfl) ⟨12560009, by rfl⟩ : syracuseStep 16746679 = 25120019) B25120019
theorem B8718839 : Blo 1144635 8718839 := bstep (se 1 (by rfl) ⟨6539129, by rfl⟩ : syracuseStep 8718839 = 13078259) B13078259
theorem B1935913 : Blo 1144635 1935913 := bstep (se 2 (by rfl) ⟨725967, by rfl⟩ : syracuseStep 1935913 = 1451935) B1451935
theorem B3869639 : Blo 1144635 3869639 := bstep (se 1 (by rfl) ⟨2902229, by rfl⟩ : syracuseStep 3869639 = 5804459) B5804459
theorem B5803001 : Blo 1144635 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B3869693 : Blo 1144635 3869693 := bstep (se 3 (by rfl) ⟨725567, by rfl⟩ : syracuseStep 3869693 = 1451135) B1451135
theorem B9309275 : Blo 1144635 9309275 := bstep (se 1 (by rfl) ⟨6981956, by rfl⟩ : syracuseStep 9309275 = 13963913) B13963913
theorem B7343399 : Blo 1144635 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B3673853 : Blo 1144635 3673853 := bstep (se 3 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 3673853 = 1377695) B1377695
theorem B1937263 : Blo 1144635 1937263 := bstep (se 1 (by rfl) ⟨1452947, by rfl⟩ : syracuseStep 1937263 = 2905895) B2905895
theorem B1937351 : Blo 1144635 1937351 := bstep (se 1 (by rfl) ⟨1453013, by rfl⟩ : syracuseStep 1937351 = 2906027) B2906027
theorem B8818895 : Blo 1144635 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B5804297 : Blo 1144635 5804297 := bstep (se 2 (by rfl) ⟨2176611, by rfl⟩ : syracuseStep 5804297 = 4353223) B4353223
theorem B7443571 : Blo 1144635 7443571 := bstep (se 1 (by rfl) ⟨5582678, by rfl⟩ : syracuseStep 7443571 = 11165357) B11165357
theorem B20944763 : Blo 1144635 20944763 := bstep (se 1 (by rfl) ⟨15708572, by rfl⟩ : syracuseStep 20944763 = 31417145) B31417145
theorem B6527101 : Blo 1144635 6527101 := bstep (se 3 (by rfl) ⟨1223831, by rfl⟩ : syracuseStep 6527101 = 2447663) B2447663
theorem B8067599 : Blo 1144635 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B29432645 : Blo 1144635 29432645 := bstep (se 4 (by rfl) ⟨2759310, by rfl⟩ : syracuseStep 29432645 = 5518621) B5518621
theorem B6528059 : Blo 1144635 6528059 := bstep (se 1 (by rfl) ⟨4896044, by rfl⟩ : syracuseStep 6528059 = 9792089) B9792089
theorem B3873851 : Blo 1144635 3873851 := bstep (se 1 (by rfl) ⟨2905388, by rfl⟩ : syracuseStep 3873851 = 5810777) B5810777
theorem B70622603 : Blo 1144635 70622603 := bstep (se 1 (by rfl) ⟨52966952, by rfl⟩ : syracuseStep 70622603 = 105933905) B105933905
theorem B6528559 : Blo 1144635 6528559 := bstep (se 1 (by rfl) ⟨4896419, by rfl⟩ : syracuseStep 6528559 = 9792839) B9792839
theorem B3481697 : Blo 1144635 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B3874985 : Blo 1144635 3874985 := bstep (se 2 (by rfl) ⟨1453119, by rfl⟩ : syracuseStep 3874985 = 2906239) B2906239
theorem B1450219 : Blo 1144635 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B37167655 : Blo 1144635 37167655 := bstep (se 1 (by rfl) ⟨27875741, by rfl⟩ : syracuseStep 37167655 = 55751483) B55751483
theorem B12395105 : Blo 1144635 12395105 := bstep (se 2 (by rfl) ⟨4648164, by rfl⟩ : syracuseStep 12395105 = 9296329) B9296329
theorem B3875471 : Blo 1144635 3875471 := bstep (se 1 (by rfl) ⟨2906603, by rfl⟩ : syracuseStep 3875471 = 5813207) B5813207
theorem B27895117 : Blo 1144635 27895117 := bstep (se 3 (by rfl) ⟨5230334, by rfl⟩ : syracuseStep 27895117 = 10460669) B10460669
theorem B19835159 : Blo 1144635 19835159 := bstep (se 1 (by rfl) ⟨14876369, by rfl⟩ : syracuseStep 19835159 = 29752739) B29752739
theorem B8694539 : Blo 1144635 8694539 := bstep (se 1 (by rfl) ⟨6520904, by rfl⟩ : syracuseStep 8694539 = 13041809) B13041809
theorem B6532001 : Blo 1144635 6532001 := bstep (se 2 (by rfl) ⟨2449500, by rfl⟩ : syracuseStep 6532001 = 4899001) B4899001
theorem B8268911 : Blo 1144635 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B1453727 : Blo 1144635 1453727 := bstep (se 1 (by rfl) ⟨1090295, by rfl⟩ : syracuseStep 1453727 = 2180591) B2180591
theorem B2174683 : Blo 1144635 2174683 := bstep (se 1 (by rfl) ⟨1631012, by rfl⟩ : syracuseStep 2174683 = 3262025) B3262025
theorem B49590089 : Blo 1144635 49590089 := bstep (se 2 (by rfl) ⟨18596283, by rfl⟩ : syracuseStep 49590089 = 37192567) B37192567
theorem B3977839 : Blo 1144635 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B1291207 : Blo 1144635 1291207 := bstep (se 1 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 1291207 = 1936811) B1936811
theorem B1717823 : Blo 1144635 1717823 := bstep (se 1 (by rfl) ⟨1288367, by rfl⟩ : syracuseStep 1717823 = 2576735) B2576735
theorem B1292071 : Blo 1144635 1292071 := bstep (se 1 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 1292071 = 1938107) B1938107
theorem B1292143 : Blo 1144635 1292143 := bstep (se 1 (by rfl) ⟨969107, by rfl⟩ : syracuseStep 1292143 = 1938215) B1938215
theorem B1718303 : Blo 1144635 1718303 := bstep (se 1 (by rfl) ⟨1288727, by rfl⟩ : syracuseStep 1718303 = 2577455) B2577455
theorem B7354471 : Blo 1144635 7354471 := bstep (se 1 (by rfl) ⟨5515853, by rfl⟩ : syracuseStep 7354471 = 11031707) B11031707
theorem B1718441 : Blo 1144635 1718441 := bstep (se 2 (by rfl) ⟨644415, by rfl⟩ : syracuseStep 1718441 = 1288831) B1288831
theorem B2177417 : Blo 1144635 2177417 := bstep (se 2 (by rfl) ⟨816531, by rfl⟩ : syracuseStep 2177417 = 1633063) B1633063
theorem B1718687 : Blo 1144635 1718687 := bstep (se 1 (by rfl) ⟨1289015, by rfl⟩ : syracuseStep 1718687 = 2578031) B2578031
theorem B1719143 : Blo 1144635 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B3358199 : Blo 1144635 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B3260179 : Blo 1144635 3260179 := bstep (se 1 (by rfl) ⟨2445134, by rfl⟩ : syracuseStep 3260179 = 4890269) B4890269
theorem B8699885 : Blo 1144635 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B3096701 : Blo 1144635 3096701 := bstep (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) B1161263
theorem B9781631 : Blo 1144635 9781631 := bstep (se 1 (by rfl) ⟨7336223, by rfl⟩ : syracuseStep 9781631 = 14672447) B14672447
theorem B1721063 : Blo 1144635 1721063 := bstep (se 1 (by rfl) ⟨1290797, by rfl⟩ : syracuseStep 1721063 = 2581595) B2581595
theorem B2179847 : Blo 1144635 2179847 := bstep (se 1 (by rfl) ⟨1634885, by rfl⟩ : syracuseStep 2179847 = 3269771) B3269771
theorem B1721327 : Blo 1144635 1721327 := bstep (se 1 (by rfl) ⟨1290995, by rfl⟩ : syracuseStep 1721327 = 2581991) B2581991
theorem B1721513 : Blo 1144635 1721513 := bstep (se 2 (by rfl) ⟨645567, by rfl⟩ : syracuseStep 1721513 = 1291135) B1291135
theorem B1721855 : Blo 1144635 1721855 := bstep (se 1 (by rfl) ⟨1291391, by rfl⟩ : syracuseStep 1721855 = 2582783) B2582783
theorem B11913311 : Blo 1144635 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B1722587 : Blo 1144635 1722587 := bstep (se 1 (by rfl) ⟨1291940, by rfl⟩ : syracuseStep 1722587 = 2583881) B2583881
theorem B1722695 : Blo 1144635 1722695 := bstep (se 1 (by rfl) ⟨1292021, by rfl⟩ : syracuseStep 1722695 = 2584043) B2584043
theorem B1722863 : Blo 1144635 1722863 := bstep (se 1 (by rfl) ⟨1292147, by rfl⟩ : syracuseStep 1722863 = 2584295) B2584295
theorem B11750521 : Blo 1144635 11750521 := bstep (se 2 (by rfl) ⟨4406445, by rfl⟩ : syracuseStep 11750521 = 8812891) B8812891
theorem B5229755 : Blo 1144635 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B8277241 : Blo 1144635 8277241 := bstep (se 2 (by rfl) ⟨3103965, by rfl⟩ : syracuseStep 8277241 = 6207931) B6207931
theorem B2903323 : Blo 1144635 2903323 := bstep (se 1 (by rfl) ⟨2177492, by rfl⟩ : syracuseStep 2903323 = 4354985) B4354985
theorem B2575871 : Blo 1144635 2575871 := bstep (se 1 (by rfl) ⟨1931903, by rfl⟩ : syracuseStep 2575871 = 3863807) B3863807
theorem B8278685 : Blo 1144635 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B14668451 : Blo 1144635 14668451 := bstep (se 1 (by rfl) ⟨11001338, by rfl⟩ : syracuseStep 14668451 = 22002677) B22002677
theorem B2577275 : Blo 1144635 2577275 := bstep (se 1 (by rfl) ⟨1932956, by rfl⟩ : syracuseStep 2577275 = 3865913) B3865913
theorem B2905591 : Blo 1144635 2905591 := bstep (se 1 (by rfl) ⟨2179193, by rfl⟩ : syracuseStep 2905591 = 4358387) B4358387
theorem B223205219 : Blo 1144635 223205219 := bstep (se 1 (by rfl) ⟨167403914, by rfl⟩ : syracuseStep 223205219 = 334807829) B334807829
theorem B2578427 : Blo 1144635 2578427 := bstep (se 1 (by rfl) ⟨1933820, by rfl⟩ : syracuseStep 2578427 = 3867641) B3867641
theorem B2578463 : Blo 1144635 2578463 := bstep (se 1 (by rfl) ⟨1933847, by rfl⟩ : syracuseStep 2578463 = 3867695) B3867695
theorem B2906219 : Blo 1144635 2906219 := bstep (se 1 (by rfl) ⟨2179664, by rfl⟩ : syracuseStep 2906219 = 4359329) B4359329
theorem B2578553 : Blo 1144635 2578553 := bstep (se 2 (by rfl) ⟨966957, by rfl⟩ : syracuseStep 2578553 = 1933915) B1933915
theorem B19880063 : Blo 1144635 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B19586771 : Blo 1144635 19586771 := bstep (se 1 (by rfl) ⟨14690078, by rfl⟩ : syracuseStep 19586771 = 29380157) B29380157
theorem B13623173 : Blo 1144635 13623173 := bstep (se 4 (by rfl) ⟨1277172, by rfl⟩ : syracuseStep 13623173 = 2554345) B2554345
theorem B2580839 : Blo 1144635 2580839 := bstep (se 1 (by rfl) ⟨1935629, by rfl⟩ : syracuseStep 2580839 = 3871259) B3871259
theorem B33023153 : Blo 1144635 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B1631935 : Blo 1144635 1631935 := bstep (se 1 (by rfl) ⟨1223951, by rfl⟩ : syracuseStep 1631935 = 2447903) B2447903
theorem B4353983 : Blo 1144635 4353983 := bstep (se 1 (by rfl) ⟨3265487, by rfl⟩ : syracuseStep 4353983 = 6530975) B6530975
theorem B3928733 : Blo 1144635 3928733 := bstep (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) B1473275
theorem B2618087 : Blo 1144635 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B8713007 : Blo 1144635 8713007 := bstep (se 1 (by rfl) ⟨6534755, by rfl⟩ : syracuseStep 8713007 = 13069511) B13069511
theorem B3864509 : Blo 1144635 3864509 := bstep (se 3 (by rfl) ⟨724595, by rfl⟩ : syracuseStep 3864509 = 1449191) B1449191
theorem B3864617 : Blo 1144635 3864617 := bstep (se 2 (by rfl) ⟨1449231, by rfl⟩ : syracuseStep 3864617 = 2898463) B2898463
theorem B95320313 : Blo 1144635 95320313 := bstep (se 2 (by rfl) ⟨35745117, by rfl⟩ : syracuseStep 95320313 = 71490235) B71490235
theorem B1145115 : Blo 1144635 1145115 := bstep (se 1 (by rfl) ⟨858836, by rfl⟩ : syracuseStep 1145115 = 1717673) B1717673
theorem B1145151 : Blo 1144635 1145151 := bstep (se 1 (by rfl) ⟨858863, by rfl⟩ : syracuseStep 1145151 = 1717727) B1717727
theorem B1145243 : Blo 1144635 1145243 := bstep (se 1 (by rfl) ⟨858932, by rfl⟩ : syracuseStep 1145243 = 1717865) B1717865
theorem B1931755 : Blo 1144635 1931755 := bstep (se 1 (by rfl) ⟨1448816, by rfl⟩ : syracuseStep 1931755 = 2897633) B2897633
theorem B1145391 : Blo 1144635 1145391 := bstep (se 1 (by rfl) ⟨859043, by rfl⟩ : syracuseStep 1145391 = 1718087) B1718087
theorem B1145551 : Blo 1144635 1145551 := bstep (se 1 (by rfl) ⟨859163, by rfl⟩ : syracuseStep 1145551 = 1718327) B1718327
theorem B1145599 : Blo 1144635 1145599 := bstep (se 1 (by rfl) ⟨859199, by rfl⟩ : syracuseStep 1145599 = 1718399) B1718399
theorem B4357097 : Blo 1144635 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B15695005 : Blo 1144635 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B1834159 : Blo 1144635 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B1146139 : Blo 1144635 1146139 := bstep (se 1 (by rfl) ⟨859604, by rfl⟩ : syracuseStep 1146139 = 1719209) B1719209
theorem B55737881 : Blo 1144635 55737881 := bstep (se 2 (by rfl) ⟨20901705, by rfl⟩ : syracuseStep 55737881 = 41803411) B41803411
theorem B1146495 : Blo 1144635 1146495 := bstep (se 1 (by rfl) ⟨859871, by rfl⟩ : syracuseStep 1146495 = 1719743) B1719743
theorem B1146607 : Blo 1144635 1146607 := bstep (se 1 (by rfl) ⟨859955, by rfl⟩ : syracuseStep 1146607 = 1719911) B1719911
theorem B1933193 : Blo 1144635 1933193 := bstep (se 2 (by rfl) ⟨724947, by rfl⟩ : syracuseStep 1933193 = 1449895) B1449895
theorem B2064467 : Blo 1144635 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B6521087 : Blo 1144635 6521087 := bstep (se 1 (by rfl) ⟨4890815, by rfl⟩ : syracuseStep 6521087 = 9781631) B9781631
theorem B1933625 : Blo 1144635 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B1147375 : Blo 1144635 1147375 := bstep (se 1 (by rfl) ⟨860531, by rfl⟩ : syracuseStep 1147375 = 1721063) B1721063
theorem B1147551 : Blo 1144635 1147551 := bstep (se 1 (by rfl) ⟨860663, by rfl⟩ : syracuseStep 1147551 = 1721327) B1721327
theorem B1147675 : Blo 1144635 1147675 := bstep (se 1 (by rfl) ⟨860756, by rfl⟩ : syracuseStep 1147675 = 1721513) B1721513
theorem B1147903 : Blo 1144635 1147903 := bstep (se 1 (by rfl) ⟨860927, by rfl⟩ : syracuseStep 1147903 = 1721855) B1721855
theorem B11011409 : Blo 1144635 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B1148391 : Blo 1144635 1148391 := bstep (se 1 (by rfl) ⟨861293, by rfl⟩ : syracuseStep 1148391 = 1722587) B1722587
theorem B1148463 : Blo 1144635 1148463 := bstep (se 1 (by rfl) ⟨861347, by rfl⟩ : syracuseStep 1148463 = 1722695) B1722695
theorem B1148575 : Blo 1144635 1148575 := bstep (se 1 (by rfl) ⟨861431, by rfl⟩ : syracuseStep 1148575 = 1722863) B1722863
theorem B37193489 : Blo 1144635 37193489 := bstep (se 2 (by rfl) ⟨13947558, by rfl⟩ : syracuseStep 37193489 = 27895117) B27895117
theorem B6981565 : Blo 1144635 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B3868667 : Blo 1144635 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B3869531 : Blo 1144635 3869531 := bstep (se 1 (by rfl) ⟨2902148, by rfl⟩ : syracuseStep 3869531 = 5804297) B5804297
theorem B148803479 : Blo 1144635 148803479 := bstep (se 1 (by rfl) ⟨111602609, by rfl⟩ : syracuseStep 148803479 = 223205219) B223205219
theorem B13963175 : Blo 1144635 13963175 := bstep (se 1 (by rfl) ⟨10472381, by rfl⟩ : syracuseStep 13963175 = 20944763) B20944763
theorem B1937479 : Blo 1144635 1937479 := bstep (se 1 (by rfl) ⟨1453109, by rfl⟩ : syracuseStep 1937479 = 2906219) B2906219
theorem B15667361 : Blo 1144635 15667361 := bstep (se 2 (by rfl) ⟨5875260, by rfl⟩ : syracuseStep 15667361 = 11750521) B11750521
theorem B5378399 : Blo 1144635 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B3871097 : Blo 1144635 3871097 := bstep (se 2 (by rfl) ⟨1451661, by rfl⟩ : syracuseStep 3871097 = 2903323) B2903323
theorem B9082115 : Blo 1144635 9082115 := bstep (se 1 (by rfl) ⟨6811586, by rfl⟩ : syracuseStep 9082115 = 13623173) B13623173
theorem B8263403 : Blo 1144635 8263403 := bstep (se 1 (by rfl) ⟨6197552, by rfl⟩ : syracuseStep 8263403 = 12395105) B12395105
theorem B52893757 : Blo 1144635 52893757 := bstep (se 3 (by rfl) ⟨9917579, by rfl⟩ : syracuseStep 52893757 = 19835159) B19835159
theorem B3874121 : Blo 1144635 3874121 := bstep (se 2 (by rfl) ⟨1452795, by rfl⟩ : syracuseStep 3874121 = 2905591) B2905591
theorem B5512607 : Blo 1144635 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B9805961 : Blo 1144635 9805961 := bstep (se 2 (by rfl) ⟨3677235, by rfl⟩ : syracuseStep 9805961 = 7354471) B7354471
theorem B5808671 : Blo 1144635 5808671 := bstep (se 1 (by rfl) ⟨4356503, by rfl⟩ : syracuseStep 5808671 = 8713007) B8713007
theorem B8955197 : Blo 1144635 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B63546875 : Blo 1144635 63546875 := bstep (se 1 (by rfl) ⟨47660156, by rfl⟩ : syracuseStep 63546875 = 95320313) B95320313
theorem B1451611 : Blo 1144635 1451611 := bstep (se 1 (by rfl) ⟨1088708, by rfl⟩ : syracuseStep 1451611 = 2177417) B2177417
theorem B3876605 : Blo 1144635 3876605 := bstep (se 3 (by rfl) ⟨726863, by rfl⟩ : syracuseStep 3876605 = 1453727) B1453727
theorem B1288795 : Blo 1144635 1288795 := bstep (se 1 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 1288795 = 1933193) B1933193
theorem B1453231 : Blo 1144635 1453231 := bstep (se 1 (by rfl) ⟨1089923, by rfl⟩ : syracuseStep 1453231 = 2179847) B2179847
theorem B49556873 : Blo 1144635 49556873 := bstep (se 2 (by rfl) ⟨18583827, by rfl⟩ : syracuseStep 49556873 = 37167655) B37167655
theorem B1289947 : Blo 1144635 1289947 := bstep (se 1 (by rfl) ⟨967460, by rfl⟩ : syracuseStep 1289947 = 1934921) B1934921
theorem B7942207 : Blo 1144635 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B5812559 : Blo 1144635 5812559 := bstep (se 1 (by rfl) ⟨4359419, by rfl⟩ : syracuseStep 5812559 = 8718839) B8718839
theorem B6206183 : Blo 1144635 6206183 := bstep (se 1 (by rfl) ⟨4654637, by rfl⟩ : syracuseStep 6206183 = 9309275) B9309275
theorem B3486503 : Blo 1144635 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B2175913 : Blo 1144635 2175913 := bstep (se 2 (by rfl) ⟨815967, by rfl⟩ : syracuseStep 2175913 = 1631935) B1631935
theorem B1717247 : Blo 1144635 1717247 := bstep (se 1 (by rfl) ⟨1287935, by rfl⟩ : syracuseStep 1717247 = 2575871) B2575871
theorem B1291567 : Blo 1144635 1291567 := bstep (se 1 (by rfl) ⟨968675, by rfl⟩ : syracuseStep 1291567 = 1937351) B1937351
theorem B22328905 : Blo 1144635 22328905 := bstep (se 2 (by rfl) ⟨8373339, by rfl⟩ : syracuseStep 22328905 = 16746679) B16746679
theorem B5519123 : Blo 1144635 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B9778967 : Blo 1144635 9778967 := bstep (se 1 (by rfl) ⟨7334225, by rfl⟩ : syracuseStep 9778967 = 14668451) B14668451
theorem B21215141 : Blo 1144635 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B1718183 : Blo 1144635 1718183 := bstep (se 1 (by rfl) ⟨1288637, by rfl⟩ : syracuseStep 1718183 = 2577275) B2577275
theorem B1718951 : Blo 1144635 1718951 := bstep (se 1 (by rfl) ⟨1289213, by rfl⟩ : syracuseStep 1718951 = 2578427) B2578427
theorem B1718975 : Blo 1144635 1718975 := bstep (se 1 (by rfl) ⟨1289231, by rfl⟩ : syracuseStep 1718975 = 2578463) B2578463
theorem B1719035 : Blo 1144635 1719035 := bstep (se 1 (by rfl) ⟨1289276, by rfl⟩ : syracuseStep 1719035 = 2578553) B2578553
theorem B13253375 : Blo 1144635 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B2899577 : Blo 1144635 2899577 := bstep (se 2 (by rfl) ⟨1087341, by rfl⟩ : syracuseStep 2899577 = 2174683) B2174683
theorem B13057847 : Blo 1144635 13057847 := bstep (se 1 (by rfl) ⟨9793385, by rfl⟩ : syracuseStep 13057847 = 19586771) B19586771
theorem B1720559 : Blo 1144635 1720559 := bstep (se 1 (by rfl) ⟨1290419, by rfl⟩ : syracuseStep 1720559 = 2580839) B2580839
theorem B1721609 : Blo 1144635 1721609 := bstep (se 2 (by rfl) ⟨645603, by rfl⟩ : syracuseStep 1721609 = 1291207) B1291207
theorem B1722761 : Blo 1144635 1722761 := bstep (se 2 (by rfl) ⟨646035, by rfl⟩ : syracuseStep 1722761 = 1292071) B1292071
theorem B1722857 : Blo 1144635 1722857 := bstep (se 2 (by rfl) ⟨646071, by rfl⟩ : syracuseStep 1722857 = 1292143) B1292143
theorem B2902655 : Blo 1144635 2902655 := bstep (se 1 (by rfl) ⟨2176991, by rfl⟩ : syracuseStep 2902655 = 4353983) B4353983
theorem B8702801 : Blo 1144635 8702801 := bstep (se 2 (by rfl) ⟨3263550, by rfl⟩ : syracuseStep 8702801 = 6527101) B6527101
theorem B2575673 : Blo 1144635 2575673 := bstep (se 2 (by rfl) ⟨965877, by rfl⟩ : syracuseStep 2575673 = 1931755) B1931755
theorem B19582397 : Blo 1144635 19582397 := bstep (se 3 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 19582397 = 7343399) B7343399
theorem B2576339 : Blo 1144635 2576339 := bstep (se 1 (by rfl) ⟨1932254, by rfl⟩ : syracuseStep 2576339 = 3864509) B3864509
theorem B2576411 : Blo 1144635 2576411 := bstep (se 1 (by rfl) ⟨1932308, by rfl⟩ : syracuseStep 2576411 = 3864617) B3864617
theorem B20926673 : Blo 1144635 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B2445545 : Blo 1144635 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B2904731 : Blo 1144635 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B8704745 : Blo 1144635 8704745 := bstep (se 2 (by rfl) ⟨3264279, by rfl⟩ : syracuseStep 8704745 = 6528559) B6528559
theorem B4346905 : Blo 1144635 4346905 := bstep (se 2 (by rfl) ⟨1630089, by rfl⟩ : syracuseStep 4346905 = 3260179) B3260179
theorem B23517053 : Blo 1144635 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B2578409 : Blo 1144635 2578409 := bstep (se 2 (by rfl) ⟨966903, by rfl⟩ : syracuseStep 2578409 = 1933807) B1933807
theorem B2906351 : Blo 1144635 2906351 := bstep (se 1 (by rfl) ⟨2179763, by rfl⟩ : syracuseStep 2906351 = 4359527) B4359527
theorem B2578895 : Blo 1144635 2578895 := bstep (se 1 (by rfl) ⟨1934171, by rfl⟩ : syracuseStep 2578895 = 3868343) B3868343
theorem B2579759 : Blo 1144635 2579759 := bstep (se 1 (by rfl) ⟨1934819, by rfl⟩ : syracuseStep 2579759 = 3869639) B3869639
theorem B2579795 : Blo 1144635 2579795 := bstep (se 1 (by rfl) ⟨1934846, by rfl⟩ : syracuseStep 2579795 = 3869693) B3869693
theorem B2449235 : Blo 1144635 2449235 := bstep (se 1 (by rfl) ⟨1836926, by rfl⟩ : syracuseStep 2449235 = 3673853) B3673853
theorem B2580713 : Blo 1144635 2580713 := bstep (se 2 (by rfl) ⟨967767, by rfl⟩ : syracuseStep 2580713 = 1935535) B1935535
theorem B2581217 : Blo 1144635 2581217 := bstep (se 2 (by rfl) ⟨967956, by rfl⟩ : syracuseStep 2581217 = 1935913) B1935913
theorem B11036321 : Blo 1144635 11036321 := bstep (se 2 (by rfl) ⟨4138620, by rfl⟩ : syracuseStep 11036321 = 8277241) B8277241
theorem B19621763 : Blo 1144635 19621763 := bstep (se 1 (by rfl) ⟨14716322, by rfl⟩ : syracuseStep 19621763 = 29432645) B29432645
theorem B4352039 : Blo 1144635 4352039 := bstep (se 1 (by rfl) ⟨3264029, by rfl⟩ : syracuseStep 4352039 = 6528059) B6528059
theorem B2582567 : Blo 1144635 2582567 := bstep (se 1 (by rfl) ⟨1936925, by rfl⟩ : syracuseStep 2582567 = 3873851) B3873851
theorem B47081735 : Blo 1144635 47081735 := bstep (se 1 (by rfl) ⟨35311301, by rfl⟩ : syracuseStep 47081735 = 70622603) B70622603
theorem B2583017 : Blo 1144635 2583017 := bstep (se 2 (by rfl) ⟨968631, by rfl⟩ : syracuseStep 2583017 = 1937263) B1937263
theorem B2321131 : Blo 1144635 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B2583323 : Blo 1144635 2583323 := bstep (se 1 (by rfl) ⟨1937492, by rfl⟩ : syracuseStep 2583323 = 3874985) B3874985
theorem B2583647 : Blo 1144635 2583647 := bstep (se 1 (by rfl) ⟨1937735, by rfl⟩ : syracuseStep 2583647 = 3875471) B3875471
theorem B22015435 : Blo 1144635 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B9924761 : Blo 1144635 9924761 := bstep (se 2 (by rfl) ⟨3721785, by rfl⟩ : syracuseStep 9924761 = 7443571) B7443571
theorem B5796359 : Blo 1144635 5796359 := bstep (se 1 (by rfl) ⟨4347269, by rfl⟩ : syracuseStep 5796359 = 8694539) B8694539
theorem B4354667 : Blo 1144635 4354667 := bstep (se 1 (by rfl) ⟨3266000, by rfl⟩ : syracuseStep 4354667 = 6532001) B6532001
theorem B33060059 : Blo 1144635 33060059 := bstep (se 1 (by rfl) ⟨24795044, by rfl⟩ : syracuseStep 33060059 = 49590089) B49590089
theorem B2619155 : Blo 1144635 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B1145215 : Blo 1144635 1145215 := bstep (se 1 (by rfl) ⟨858911, by rfl⟩ : syracuseStep 1145215 = 1717823) B1717823
theorem B1145535 : Blo 1144635 1145535 := bstep (se 1 (by rfl) ⟨859151, by rfl⟩ : syracuseStep 1145535 = 1718303) B1718303
theorem B1145627 : Blo 1144635 1145627 := bstep (se 1 (by rfl) ⟨859220, by rfl⟩ : syracuseStep 1145627 = 1718441) B1718441
theorem B1145791 : Blo 1144635 1145791 := bstep (se 1 (by rfl) ⟨859343, by rfl⟩ : syracuseStep 1145791 = 1718687) B1718687
theorem B1146095 : Blo 1144635 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B37158587 : Blo 1144635 37158587 := bstep (se 1 (by rfl) ⟨27868940, by rfl⟩ : syracuseStep 37158587 = 55737881) B55737881
theorem B5799923 : Blo 1144635 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B1147039 : Blo 1144635 1147039 := bstep (se 1 (by rfl) ⟨860279, by rfl⟩ : syracuseStep 1147039 = 1720559) B1720559
theorem B5505245 : Blo 1144635 5505245 := bstep (se 3 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 5505245 = 2064467) B2064467
theorem B1147739 : Blo 1144635 1147739 := bstep (se 1 (by rfl) ⟨860804, by rfl⟩ : syracuseStep 1147739 = 1721609) B1721609
theorem B7340939 : Blo 1144635 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B1148507 : Blo 1144635 1148507 := bstep (se 1 (by rfl) ⟨861380, by rfl⟩ : syracuseStep 1148507 = 1722761) B1722761
theorem B1148571 : Blo 1144635 1148571 := bstep (se 1 (by rfl) ⟨861428, by rfl⟩ : syracuseStep 1148571 = 1722857) B1722857
theorem B1935103 : Blo 1144635 1935103 := bstep (se 1 (by rfl) ⟨1451327, by rfl⟩ : syracuseStep 1935103 = 2902655) B2902655
theorem B5801867 : Blo 1144635 5801867 := bstep (se 1 (by rfl) ⟨4351400, by rfl⟩ : syracuseStep 5801867 = 8702801) B8702801
theorem B1935481 : Blo 1144635 1935481 := bstep (se 2 (by rfl) ⟨725805, by rfl⟩ : syracuseStep 1935481 = 1451611) B1451611
theorem B9308753 : Blo 1144635 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B9308783 : Blo 1144635 9308783 := bstep (se 1 (by rfl) ⟨6981587, by rfl⟩ : syracuseStep 9308783 = 13963175) B13963175
theorem B1936487 : Blo 1144635 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B5803163 : Blo 1144635 5803163 := bstep (se 1 (by rfl) ⟨4352372, by rfl⟩ : syracuseStep 5803163 = 8704745) B8704745
theorem B5508935 : Blo 1144635 5508935 := bstep (se 1 (by rfl) ⟨4131701, by rfl⟩ : syracuseStep 5508935 = 8263403) B8263403
theorem B1937567 : Blo 1144635 1937567 := bstep (se 1 (by rfl) ⟨1453175, by rfl⟩ : syracuseStep 1937567 = 2906351) B2906351
theorem B1937641 : Blo 1144635 1937641 := bstep (se 2 (by rfl) ⟨726615, by rfl⟩ : syracuseStep 1937641 = 1453231) B1453231
theorem B6984413 : Blo 1144635 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B3675071 : Blo 1144635 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B10589609 : Blo 1144635 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B3872447 : Blo 1144635 3872447 := bstep (se 1 (by rfl) ⟨2904335, by rfl⟩ : syracuseStep 3872447 = 5808671) B5808671
theorem B5970131 : Blo 1144635 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B13081175 : Blo 1144635 13081175 := bstep (se 1 (by rfl) ⟨9810881, by rfl⟩ : syracuseStep 13081175 = 19621763) B19621763
theorem B33037915 : Blo 1144635 33037915 := bstep (se 1 (by rfl) ⟨24778436, by rfl⟩ : syracuseStep 33037915 = 49556873) B49556873
theorem B70525009 : Blo 1144635 70525009 := bstep (se 2 (by rfl) ⟨26446878, by rfl⟩ : syracuseStep 70525009 = 52893757) B52893757
theorem B3875039 : Blo 1144635 3875039 := bstep (se 1 (by rfl) ⟨2906279, by rfl⟩ : syracuseStep 3875039 = 5812559) B5812559
theorem B4137455 : Blo 1144635 4137455 := bstep (se 1 (by rfl) ⟨3103091, by rfl⟩ : syracuseStep 4137455 = 6206183) B6206183
theorem B3679415 : Blo 1144635 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B6531293 : Blo 1144635 6531293 := bstep (se 3 (by rfl) ⟨1224617, by rfl⟩ : syracuseStep 6531293 = 2449235) B2449235
theorem B1289083 : Blo 1144635 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B1717115 : Blo 1144635 1717115 := bstep (se 1 (by rfl) ⟨1287836, by rfl⟩ : syracuseStep 1717115 = 2575673) B2575673
theorem B13054931 : Blo 1144635 13054931 := bstep (se 1 (by rfl) ⟨9791198, by rfl⟩ : syracuseStep 13054931 = 19582397) B19582397
theorem B99202319 : Blo 1144635 99202319 := bstep (se 1 (by rfl) ⟨74401739, by rfl⟩ : syracuseStep 99202319 = 148803479) B148803479
theorem B1717559 : Blo 1144635 1717559 := bstep (se 1 (by rfl) ⟨1288169, by rfl⟩ : syracuseStep 1717559 = 2576339) B2576339
theorem B1717607 : Blo 1144635 1717607 := bstep (se 1 (by rfl) ⟨1288205, by rfl⟩ : syracuseStep 1717607 = 2576411) B2576411
theorem B3585599 : Blo 1144635 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B1718393 : Blo 1144635 1718393 := bstep (se 2 (by rfl) ⟨644397, by rfl⟩ : syracuseStep 1718393 = 1288795) B1288795
theorem B3094841 : Blo 1144635 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B15678035 : Blo 1144635 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B1718939 : Blo 1144635 1718939 := bstep (se 1 (by rfl) ⟨1289204, by rfl⟩ : syracuseStep 1718939 = 2578409) B2578409
theorem B1719263 : Blo 1144635 1719263 := bstep (se 1 (by rfl) ⟨1289447, by rfl⟩ : syracuseStep 1719263 = 2578895) B2578895
theorem B1719839 : Blo 1144635 1719839 := bstep (se 1 (by rfl) ⟨1289879, by rfl⟩ : syracuseStep 1719839 = 2579759) B2579759
theorem B1719863 : Blo 1144635 1719863 := bstep (se 1 (by rfl) ⟨1289897, by rfl⟩ : syracuseStep 1719863 = 2579795) B2579795
theorem B1719929 : Blo 1144635 1719929 := bstep (se 2 (by rfl) ⟨644973, by rfl⟩ : syracuseStep 1719929 = 1289947) B1289947
theorem B6537307 : Blo 1144635 6537307 := bstep (se 1 (by rfl) ⟨4902980, by rfl⟩ : syracuseStep 6537307 = 9805961) B9805961
theorem B1720475 : Blo 1144635 1720475 := bstep (se 1 (by rfl) ⟨1290356, by rfl⟩ : syracuseStep 1720475 = 2580713) B2580713
theorem B1720811 : Blo 1144635 1720811 := bstep (se 1 (by rfl) ⟨1290608, by rfl⟩ : syracuseStep 1720811 = 2581217) B2581217
theorem B7357547 : Blo 1144635 7357547 := bstep (se 1 (by rfl) ⟨5518160, by rfl⟩ : syracuseStep 7357547 = 11036321) B11036321
theorem B2901217 : Blo 1144635 2901217 := bstep (se 2 (by rfl) ⟨1087956, by rfl⟩ : syracuseStep 2901217 = 2175913) B2175913
theorem B2901359 : Blo 1144635 2901359 := bstep (se 1 (by rfl) ⟨2176019, by rfl⟩ : syracuseStep 2901359 = 4352039) B4352039
theorem B1721711 : Blo 1144635 1721711 := bstep (se 1 (by rfl) ⟨1291283, by rfl⟩ : syracuseStep 1721711 = 2582567) B2582567
theorem B1722011 : Blo 1144635 1722011 := bstep (se 1 (by rfl) ⟨1291508, by rfl⟩ : syracuseStep 1722011 = 2583017) B2583017
theorem B1722089 : Blo 1144635 1722089 := bstep (se 2 (by rfl) ⟨645783, by rfl⟩ : syracuseStep 1722089 = 1291567) B1291567
theorem B1722215 : Blo 1144635 1722215 := bstep (se 1 (by rfl) ⟨1291661, by rfl⟩ : syracuseStep 1722215 = 2583323) B2583323
theorem B1722431 : Blo 1144635 1722431 := bstep (se 1 (by rfl) ⟨1291823, by rfl⟩ : syracuseStep 1722431 = 2583647) B2583647
theorem B29771873 : Blo 1144635 29771873 := bstep (se 2 (by rfl) ⟨11164452, by rfl⟩ : syracuseStep 29771873 = 22328905) B22328905
theorem B2903111 : Blo 1144635 2903111 := bstep (se 1 (by rfl) ⟨2177333, by rfl⟩ : syracuseStep 2903111 = 4354667) B4354667
theorem B22040039 : Blo 1144635 22040039 := bstep (se 1 (by rfl) ⟨16530029, by rfl⟩ : syracuseStep 22040039 = 33060059) B33060059
theorem B14143427 : Blo 1144635 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B8835583 : Blo 1144635 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B8705231 : Blo 1144635 8705231 := bstep (se 1 (by rfl) ⟨6528923, by rfl⟩ : syracuseStep 8705231 = 13057847) B13057847
theorem B4347391 : Blo 1144635 4347391 := bstep (se 1 (by rfl) ⟨3260543, by rfl⟩ : syracuseStep 4347391 = 6521087) B6521087
theorem B3866615 : Blo 1144635 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B24795659 : Blo 1144635 24795659 := bstep (se 1 (by rfl) ⟨18596744, by rfl⟩ : syracuseStep 24795659 = 37193489) B37193489
theorem B2579111 : Blo 1144635 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B2579687 : Blo 1144635 2579687 := bstep (se 1 (by rfl) ⟨1934765, by rfl⟩ : syracuseStep 2579687 = 3869531) B3869531
theorem B10444907 : Blo 1144635 10444907 := bstep (se 1 (by rfl) ⟨7833680, by rfl⟩ : syracuseStep 10444907 = 15667361) B15667361
theorem B13951115 : Blo 1144635 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B1630363 : Blo 1144635 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B2580731 : Blo 1144635 2580731 := bstep (se 1 (by rfl) ⟨1935548, by rfl⟩ : syracuseStep 2580731 = 3871097) B3871097
theorem B6054743 : Blo 1144635 6054743 := bstep (se 1 (by rfl) ⟨4541057, by rfl⟩ : syracuseStep 6054743 = 9082115) B9082115
theorem B29353913 : Blo 1144635 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B2582747 : Blo 1144635 2582747 := bstep (se 1 (by rfl) ⟨1937060, by rfl⟩ : syracuseStep 2582747 = 3874121) B3874121
theorem B2583305 : Blo 1144635 2583305 := bstep (se 2 (by rfl) ⟨968739, by rfl⟩ : syracuseStep 2583305 = 1937479) B1937479
theorem B42364583 : Blo 1144635 42364583 := bstep (se 1 (by rfl) ⟨31773437, by rfl⟩ : syracuseStep 42364583 = 63546875) B63546875
theorem B2584403 : Blo 1144635 2584403 := bstep (se 1 (by rfl) ⟨1938302, by rfl⟩ : syracuseStep 2584403 = 3876605) B3876605
theorem B5795873 : Blo 1144635 5795873 := bstep (se 2 (by rfl) ⟨2173452, by rfl⟩ : syracuseStep 5795873 = 4346905) B4346905
theorem B31387823 : Blo 1144635 31387823 := bstep (se 1 (by rfl) ⟨23540867, by rfl⟩ : syracuseStep 31387823 = 47081735) B47081735
theorem B6616507 : Blo 1144635 6616507 := bstep (se 1 (by rfl) ⟨4962380, by rfl⟩ : syracuseStep 6616507 = 9924761) B9924761
theorem B3864239 : Blo 1144635 3864239 := bstep (se 1 (by rfl) ⟨2898179, by rfl⟩ : syracuseStep 3864239 = 5796359) B5796359
theorem B2324335 : Blo 1144635 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B1144831 : Blo 1144635 1144831 := bstep (se 1 (by rfl) ⟨858623, by rfl⟩ : syracuseStep 1144831 = 1717247) B1717247
theorem B6519311 : Blo 1144635 6519311 := bstep (se 1 (by rfl) ⟨4889483, by rfl⟩ : syracuseStep 6519311 = 9778967) B9778967
theorem B1145455 : Blo 1144635 1145455 := bstep (se 1 (by rfl) ⟨859091, by rfl⟩ : syracuseStep 1145455 = 1718183) B1718183
theorem B1145967 : Blo 1144635 1145967 := bstep (se 1 (by rfl) ⟨859475, by rfl⟩ : syracuseStep 1145967 = 1718951) B1718951
theorem B1145983 : Blo 1144635 1145983 := bstep (se 1 (by rfl) ⟨859487, by rfl⟩ : syracuseStep 1145983 = 1718975) B1718975
theorem B1146023 : Blo 1144635 1146023 := bstep (se 1 (by rfl) ⟨859517, by rfl⟩ : syracuseStep 1146023 = 1719035) B1719035
theorem B1933051 : Blo 1144635 1933051 := bstep (se 1 (by rfl) ⟨1449788, by rfl⟩ : syracuseStep 1933051 = 2899577) B2899577
theorem B24772391 : Blo 1144635 24772391 := bstep (se 1 (by rfl) ⟨18579293, by rfl⟩ : syracuseStep 24772391 = 37158587) B37158587
theorem B1146983 : Blo 1144635 1146983 := bstep (se 1 (by rfl) ⟨860237, by rfl⟩ : syracuseStep 1146983 = 1720475) B1720475
theorem B8716409 : Blo 1144635 8716409 := bstep (se 2 (by rfl) ⟨3268653, by rfl⟩ : syracuseStep 8716409 = 6537307) B6537307
theorem B3670163 : Blo 1144635 3670163 := bstep (se 1 (by rfl) ⟨2752622, by rfl⟩ : syracuseStep 3670163 = 5505245) B5505245
theorem B27853085 : Blo 1144635 27853085 := bstep (se 3 (by rfl) ⟨5222453, by rfl⟩ : syracuseStep 27853085 = 10444907) B10444907
theorem B1147207 : Blo 1144635 1147207 := bstep (se 1 (by rfl) ⟨860405, by rfl⟩ : syracuseStep 1147207 = 1720811) B1720811
theorem B1934239 : Blo 1144635 1934239 := bstep (se 1 (by rfl) ⟨1450679, by rfl⟩ : syracuseStep 1934239 = 2901359) B2901359
theorem B1147807 : Blo 1144635 1147807 := bstep (se 1 (by rfl) ⟨860855, by rfl⟩ : syracuseStep 1147807 = 1721711) B1721711
theorem B1148007 : Blo 1144635 1148007 := bstep (se 1 (by rfl) ⟨861005, by rfl⟩ : syracuseStep 1148007 = 1722011) B1722011
theorem B1148059 : Blo 1144635 1148059 := bstep (se 1 (by rfl) ⟨861044, by rfl⟩ : syracuseStep 1148059 = 1722089) B1722089
theorem B1148143 : Blo 1144635 1148143 := bstep (se 1 (by rfl) ⟨861107, by rfl⟩ : syracuseStep 1148143 = 1722215) B1722215
theorem B3867911 : Blo 1144635 3867911 := bstep (se 1 (by rfl) ⟨2900933, by rfl⟩ : syracuseStep 3867911 = 5801867) B5801867
theorem B1148287 : Blo 1144635 1148287 := bstep (se 1 (by rfl) ⟨861215, by rfl⟩ : syracuseStep 1148287 = 1722431) B1722431
theorem B3868289 : Blo 1144635 3868289 := bstep (se 2 (by rfl) ⟨1450608, by rfl⟩ : syracuseStep 3868289 = 2901217) B2901217
theorem B1935407 : Blo 1144635 1935407 := bstep (se 1 (by rfl) ⟨1451555, by rfl⟩ : syracuseStep 1935407 = 2903111) B2903111
theorem B3868775 : Blo 1144635 3868775 := bstep (se 1 (by rfl) ⟨2901581, by rfl⟩ : syracuseStep 3868775 = 5803163) B5803163
theorem B9800189 : Blo 1144635 9800189 := bstep (se 3 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 9800189 = 3675071) B3675071
theorem B3672623 : Blo 1144635 3672623 := bstep (se 1 (by rfl) ⟨2754467, by rfl⟩ : syracuseStep 3672623 = 5508935) B5508935
theorem B4656275 : Blo 1144635 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B5803487 : Blo 1144635 5803487 := bstep (se 1 (by rfl) ⟨4352615, by rfl⟩ : syracuseStep 5803487 = 8705231) B8705231
theorem B8720783 : Blo 1144635 8720783 := bstep (se 1 (by rfl) ⟨6540587, by rfl⟩ : syracuseStep 8720783 = 13081175) B13081175
theorem B2758303 : Blo 1144635 2758303 := bstep (se 1 (by rfl) ⟨2068727, by rfl⟩ : syracuseStep 2758303 = 4137455) B4137455
theorem B19569275 : Blo 1144635 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B8822009 : Blo 1144635 8822009 := bstep (se 2 (by rfl) ⟨3308253, by rfl⟩ : syracuseStep 8822009 = 6616507) B6616507
theorem B66134879 : Blo 1144635 66134879 := bstep (se 1 (by rfl) ⟨49601159, by rfl⟩ : syracuseStep 66134879 = 99202319) B99202319
theorem B44050553 : Blo 1144635 44050553 := bstep (se 2 (by rfl) ⟨16518957, by rfl⟩ : syracuseStep 44050553 = 33037915) B33037915
theorem B2173817 : Blo 1144635 2173817 := bstep (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) B1630363
theorem B4893959 : Blo 1144635 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B6205835 : Blo 1144635 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B1290991 : Blo 1144635 1290991 := bstep (se 1 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 1290991 = 1936487) B1936487
theorem B14693359 : Blo 1144635 14693359 := bstep (se 1 (by rfl) ⟨11020019, by rfl⟩ : syracuseStep 14693359 = 22040039) B22040039
theorem B1291711 : Blo 1144635 1291711 := bstep (se 1 (by rfl) ⟨968783, by rfl⟩ : syracuseStep 1291711 = 1937567) B1937567
theorem B7059739 : Blo 1144635 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B1718777 : Blo 1144635 1718777 := bstep (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) B1289083
theorem B3980087 : Blo 1144635 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B16530439 : Blo 1144635 16530439 := bstep (se 1 (by rfl) ⟨12397829, by rfl⟩ : syracuseStep 16530439 = 24795659) B24795659
theorem B1719407 : Blo 1144635 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B1719791 : Blo 1144635 1719791 := bstep (se 1 (by rfl) ⟨1289843, by rfl⟩ : syracuseStep 1719791 = 2579687) B2579687
theorem B1720487 : Blo 1144635 1720487 := bstep (se 1 (by rfl) ⟨1290365, by rfl⟩ : syracuseStep 1720487 = 2580731) B2580731
theorem B11780777 : Blo 1144635 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B1721831 : Blo 1144635 1721831 := bstep (se 1 (by rfl) ⟨1291373, by rfl⟩ : syracuseStep 1721831 = 2582747) B2582747
theorem B24823421 : Blo 1144635 24823421 := bstep (se 3 (by rfl) ⟨4654391, by rfl⟩ : syracuseStep 24823421 = 9308783) B9308783
theorem B1722203 : Blo 1144635 1722203 := bstep (se 1 (by rfl) ⟨1291652, by rfl⟩ : syracuseStep 1722203 = 2583305) B2583305
theorem B3099113 : Blo 1144635 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B1722935 : Blo 1144635 1722935 := bstep (se 1 (by rfl) ⟨1292201, by rfl⟩ : syracuseStep 1722935 = 2584403) B2584403
theorem B20925215 : Blo 1144635 20925215 := bstep (se 1 (by rfl) ⟨15693911, by rfl⟩ : syracuseStep 20925215 = 31387823) B31387823
theorem B8703287 : Blo 1144635 8703287 := bstep (se 1 (by rfl) ⟨6527465, by rfl⟩ : syracuseStep 8703287 = 13054931) B13054931
theorem B2576159 : Blo 1144635 2576159 := bstep (se 1 (by rfl) ⟨1932119, by rfl⟩ : syracuseStep 2576159 = 3864239) B3864239
theorem B4346207 : Blo 1144635 4346207 := bstep (se 1 (by rfl) ⟨3259655, by rfl⟩ : syracuseStep 4346207 = 6519311) B6519311
theorem B2577401 : Blo 1144635 2577401 := bstep (se 2 (by rfl) ⟨966525, by rfl⟩ : syracuseStep 2577401 = 1933051) B1933051
theorem B2577743 : Blo 1144635 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B94033345 : Blo 1144635 94033345 := bstep (se 2 (by rfl) ⟨35262504, by rfl⟩ : syracuseStep 94033345 = 70525009) B70525009
theorem B4905031 : Blo 1144635 4905031 := bstep (se 1 (by rfl) ⟨3678773, by rfl⟩ : syracuseStep 4905031 = 7357547) B7357547
theorem B19847915 : Blo 1144635 19847915 := bstep (se 1 (by rfl) ⟨14885936, by rfl⟩ : syracuseStep 19847915 = 29771873) B29771873
theorem B16145981 : Blo 1144635 16145981 := bstep (se 3 (by rfl) ⟨3027371, by rfl⟩ : syracuseStep 16145981 = 6054743) B6054743
theorem B2580137 : Blo 1144635 2580137 := bstep (se 2 (by rfl) ⟨967551, by rfl⟩ : syracuseStep 2580137 = 1935103) B1935103
theorem B9428951 : Blo 1144635 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B2580641 : Blo 1144635 2580641 := bstep (se 2 (by rfl) ⟨967740, by rfl⟩ : syracuseStep 2580641 = 1935481) B1935481
theorem B2581631 : Blo 1144635 2581631 := bstep (se 1 (by rfl) ⟨1936223, by rfl⟩ : syracuseStep 2581631 = 3872447) B3872447
theorem B9300743 : Blo 1144635 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B2583359 : Blo 1144635 2583359 := bstep (se 1 (by rfl) ⟨1937519, by rfl⟩ : syracuseStep 2583359 = 3875039) B3875039
theorem B2583521 : Blo 1144635 2583521 := bstep (se 2 (by rfl) ⟨968820, by rfl⟩ : syracuseStep 2583521 = 1937641) B1937641
theorem B2452943 : Blo 1144635 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B4354195 : Blo 1144635 4354195 := bstep (se 1 (by rfl) ⟨3265646, by rfl⟩ : syracuseStep 4354195 = 6531293) B6531293
theorem B5796521 : Blo 1144635 5796521 := bstep (se 2 (by rfl) ⟨2173695, by rfl⟩ : syracuseStep 5796521 = 4347391) B4347391
theorem B28243055 : Blo 1144635 28243055 := bstep (se 1 (by rfl) ⟨21182291, by rfl⟩ : syracuseStep 28243055 = 42364583) B42364583
theorem B3863915 : Blo 1144635 3863915 := bstep (se 1 (by rfl) ⟨2897936, by rfl⟩ : syracuseStep 3863915 = 5795873) B5795873
theorem B1144743 : Blo 1144635 1144743 := bstep (se 1 (by rfl) ⟨858557, by rfl⟩ : syracuseStep 1144743 = 1717115) B1717115
theorem B1145039 : Blo 1144635 1145039 := bstep (se 1 (by rfl) ⟨858779, by rfl⟩ : syracuseStep 1145039 = 1717559) B1717559
theorem B1145071 : Blo 1144635 1145071 := bstep (se 1 (by rfl) ⟨858803, by rfl⟩ : syracuseStep 1145071 = 1717607) B1717607
theorem B2390399 : Blo 1144635 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B1145595 : Blo 1144635 1145595 := bstep (se 1 (by rfl) ⟨859196, by rfl⟩ : syracuseStep 1145595 = 1718393) B1718393
theorem B2063227 : Blo 1144635 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B10452023 : Blo 1144635 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B1145959 : Blo 1144635 1145959 := bstep (se 1 (by rfl) ⟨859469, by rfl⟩ : syracuseStep 1145959 = 1718939) B1718939
theorem B1146175 : Blo 1144635 1146175 := bstep (se 1 (by rfl) ⟨859631, by rfl⟩ : syracuseStep 1146175 = 1719263) B1719263
theorem B1146559 : Blo 1144635 1146559 := bstep (se 1 (by rfl) ⟨859919, by rfl⟩ : syracuseStep 1146559 = 1719839) B1719839
theorem B1146575 : Blo 1144635 1146575 := bstep (se 1 (by rfl) ⟨859931, by rfl⟩ : syracuseStep 1146575 = 1719863) B1719863
theorem B1146619 : Blo 1144635 1146619 := bstep (se 1 (by rfl) ⟨859964, by rfl⟩ : syracuseStep 1146619 = 1719929) B1719929
theorem B16514927 : Blo 1144635 16514927 := bstep (se 1 (by rfl) ⟨12386195, by rfl⟩ : syracuseStep 16514927 = 24772391) B24772391
theorem B1146991 : Blo 1144635 1146991 := bstep (se 1 (by rfl) ⟨860243, by rfl⟩ : syracuseStep 1146991 = 1720487) B1720487
theorem B1147887 : Blo 1144635 1147887 := bstep (se 1 (by rfl) ⟨860915, by rfl⟩ : syracuseStep 1147887 = 1721831) B1721831
theorem B16548893 : Blo 1144635 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B16548947 : Blo 1144635 16548947 := bstep (se 1 (by rfl) ⟨12411710, by rfl⟩ : syracuseStep 16548947 = 24823421) B24823421
theorem B1148135 : Blo 1144635 1148135 := bstep (se 1 (by rfl) ⟨861101, by rfl⟩ : syracuseStep 1148135 = 1722203) B1722203
theorem B2066075 : Blo 1144635 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B1148623 : Blo 1144635 1148623 := bstep (se 1 (by rfl) ⟨861467, by rfl⟩ : syracuseStep 1148623 = 1722935) B1722935
theorem B5802191 : Blo 1144635 5802191 := bstep (se 1 (by rfl) ⟨4351643, by rfl⟩ : syracuseStep 5802191 = 8703287) B8703287
theorem B3868991 : Blo 1144635 3868991 := bstep (se 1 (by rfl) ⟨2901743, by rfl⟩ : syracuseStep 3868991 = 5803487) B5803487
theorem B13046183 : Blo 1144635 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B5805593 : Blo 1144635 5805593 := bstep (se 2 (by rfl) ⟨2177097, by rfl⟩ : syracuseStep 5805593 = 4354195) B4354195
theorem B29367035 : Blo 1144635 29367035 := bstep (se 1 (by rfl) ⟨22025276, by rfl⟩ : syracuseStep 29367035 = 44050553) B44050553
theorem B6200495 : Blo 1144635 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B125377793 : Blo 1144635 125377793 := bstep (se 2 (by rfl) ⟨47016672, by rfl⟩ : syracuseStep 125377793 = 94033345) B94033345
theorem B3677737 : Blo 1144635 3677737 := bstep (se 2 (by rfl) ⟨1379151, by rfl⟩ : syracuseStep 3677737 = 2758303) B2758303
theorem B9412985 : Blo 1144635 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B13050557 : Blo 1144635 13050557 := bstep (se 3 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 13050557 = 4893959) B4893959
theorem B5810939 : Blo 1144635 5810939 := bstep (se 1 (by rfl) ⟨4358204, by rfl⟩ : syracuseStep 5810939 = 8716409) B8716409
theorem B1290271 : Blo 1144635 1290271 := bstep (se 1 (by rfl) ⟨967703, by rfl⟩ : syracuseStep 1290271 = 1935407) B1935407
theorem B6533459 : Blo 1144635 6533459 := bstep (se 1 (by rfl) ⟨4900094, by rfl⟩ : syracuseStep 6533459 = 9800189) B9800189
theorem B1717439 : Blo 1144635 1717439 := bstep (se 1 (by rfl) ⟨1288079, by rfl⟩ : syracuseStep 1717439 = 2576159) B2576159
theorem B2897471 : Blo 1144635 2897471 := bstep (se 1 (by rfl) ⟨2173103, by rfl⟩ : syracuseStep 2897471 = 4346207) B4346207
theorem B5813855 : Blo 1144635 5813855 := bstep (se 1 (by rfl) ⟨4360391, by rfl⟩ : syracuseStep 5813855 = 8720783) B8720783
theorem B1718267 : Blo 1144635 1718267 := bstep (se 1 (by rfl) ⟨1288700, by rfl⟩ : syracuseStep 1718267 = 2577401) B2577401
theorem B1718495 : Blo 1144635 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B5881339 : Blo 1144635 5881339 := bstep (se 1 (by rfl) ⟨4411004, by rfl⟩ : syracuseStep 5881339 = 8822009) B8822009
theorem B10763987 : Blo 1144635 10763987 := bstep (se 1 (by rfl) ⟨8072990, by rfl⟩ : syracuseStep 10763987 = 16145981) B16145981
theorem B1720091 : Blo 1144635 1720091 := bstep (se 1 (by rfl) ⟨1290068, by rfl⟩ : syracuseStep 1720091 = 2580137) B2580137
theorem B1720427 : Blo 1144635 1720427 := bstep (se 1 (by rfl) ⟨1290320, by rfl⟩ : syracuseStep 1720427 = 2580641) B2580641
theorem B44089919 : Blo 1144635 44089919 := bstep (se 1 (by rfl) ⟨33067439, by rfl⟩ : syracuseStep 44089919 = 66134879) B66134879
theorem B1721087 : Blo 1144635 1721087 := bstep (se 1 (by rfl) ⟨1290815, by rfl⟩ : syracuseStep 1721087 = 2581631) B2581631
theorem B1721321 : Blo 1144635 1721321 := bstep (se 2 (by rfl) ⟨645495, by rfl⟩ : syracuseStep 1721321 = 1290991) B1290991
theorem B1722239 : Blo 1144635 1722239 := bstep (se 1 (by rfl) ⟨1291679, by rfl⟩ : syracuseStep 1722239 = 2583359) B2583359
theorem B1722281 : Blo 1144635 1722281 := bstep (se 2 (by rfl) ⟨645855, by rfl⟩ : syracuseStep 1722281 = 1291711) B1291711
theorem B1722347 : Blo 1144635 1722347 := bstep (se 1 (by rfl) ⟨1291760, by rfl⟩ : syracuseStep 1722347 = 2583521) B2583521
theorem B6540041 : Blo 1144635 6540041 := bstep (se 2 (by rfl) ⟨2452515, by rfl⟩ : syracuseStep 6540041 = 4905031) B4905031
theorem B18828703 : Blo 1144635 18828703 := bstep (se 1 (by rfl) ⟨14121527, by rfl⟩ : syracuseStep 18828703 = 28243055) B28243055
theorem B2575943 : Blo 1144635 2575943 := bstep (se 1 (by rfl) ⟨1931957, by rfl⟩ : syracuseStep 2575943 = 3863915) B3863915
theorem B6541181 : Blo 1144635 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B22040585 : Blo 1144635 22040585 := bstep (se 2 (by rfl) ⟨8265219, by rfl⟩ : syracuseStep 22040585 = 16530439) B16530439
theorem B1593599 : Blo 1144635 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B6968015 : Blo 1144635 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B2446775 : Blo 1144635 2446775 := bstep (se 1 (by rfl) ⟨1835081, by rfl⟩ : syracuseStep 2446775 = 3670163) B3670163
theorem B18568723 : Blo 1144635 18568723 := bstep (se 1 (by rfl) ⟨13926542, by rfl⟩ : syracuseStep 18568723 = 27853085) B27853085
theorem B7853851 : Blo 1144635 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B2578607 : Blo 1144635 2578607 := bstep (se 1 (by rfl) ⟨1933955, by rfl⟩ : syracuseStep 2578607 = 3867911) B3867911
theorem B2578859 : Blo 1144635 2578859 := bstep (se 1 (by rfl) ⟨1934144, by rfl⟩ : syracuseStep 2578859 = 3868289) B3868289
theorem B2578985 : Blo 1144635 2578985 := bstep (se 2 (by rfl) ⟨967119, by rfl⟩ : syracuseStep 2578985 = 1934239) B1934239
theorem B2579183 : Blo 1144635 2579183 := bstep (se 1 (by rfl) ⟨1934387, by rfl⟩ : syracuseStep 2579183 = 3868775) B3868775
theorem B2448415 : Blo 1144635 2448415 := bstep (se 1 (by rfl) ⟨1836311, by rfl⟩ : syracuseStep 2448415 = 3672623) B3672623
theorem B13950143 : Blo 1144635 13950143 := bstep (se 1 (by rfl) ⟨10462607, by rfl⟩ : syracuseStep 13950143 = 20925215) B20925215
theorem B3104183 : Blo 1144635 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B13231943 : Blo 1144635 13231943 := bstep (se 1 (by rfl) ⟨9923957, by rfl⟩ : syracuseStep 13231943 = 19847915) B19847915
theorem B6285967 : Blo 1144635 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B19591145 : Blo 1144635 19591145 := bstep (se 2 (by rfl) ⟨7346679, by rfl⟩ : syracuseStep 19591145 = 14693359) B14693359
theorem B5796845 : Blo 1144635 5796845 := bstep (se 3 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 5796845 = 2173817) B2173817
theorem B3864347 : Blo 1144635 3864347 := bstep (se 1 (by rfl) ⟨2898260, by rfl⟩ : syracuseStep 3864347 = 5796521) B5796521
theorem B2750969 : Blo 1144635 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B1145851 : Blo 1144635 1145851 := bstep (se 1 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 1145851 = 1718777) B1718777
theorem B2653391 : Blo 1144635 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B1146271 : Blo 1144635 1146271 := bstep (se 1 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 1146271 = 1719407) B1719407
theorem B1146527 : Blo 1144635 1146527 := bstep (se 1 (by rfl) ⟨859895, by rfl⟩ : syracuseStep 1146527 = 1719791) B1719791
theorem B11009951 : Blo 1144635 11009951 := bstep (se 1 (by rfl) ⟨8257463, by rfl⟩ : syracuseStep 11009951 = 16514927) B16514927
theorem B1146951 : Blo 1144635 1146951 := bstep (se 1 (by rfl) ⟨860213, by rfl⟩ : syracuseStep 1146951 = 1720427) B1720427
theorem B29393279 : Blo 1144635 29393279 := bstep (se 1 (by rfl) ⟨22044959, by rfl⟩ : syracuseStep 29393279 = 44089919) B44089919
theorem B1147391 : Blo 1144635 1147391 := bstep (se 1 (by rfl) ⟨860543, by rfl⟩ : syracuseStep 1147391 = 1721087) B1721087
theorem B1147547 : Blo 1144635 1147547 := bstep (se 1 (by rfl) ⟨860660, by rfl⟩ : syracuseStep 1147547 = 1721321) B1721321
theorem B1377383 : Blo 1144635 1377383 := bstep (se 1 (by rfl) ⟨1033037, by rfl⟩ : syracuseStep 1377383 = 2066075) B2066075
theorem B1148159 : Blo 1144635 1148159 := bstep (se 1 (by rfl) ⟨861119, by rfl⟩ : syracuseStep 1148159 = 1722239) B1722239
theorem B1148187 : Blo 1144635 1148187 := bstep (se 1 (by rfl) ⟨861140, by rfl⟩ : syracuseStep 1148187 = 1722281) B1722281
theorem B1148231 : Blo 1144635 1148231 := bstep (se 1 (by rfl) ⟨861173, by rfl⟩ : syracuseStep 1148231 = 1722347) B1722347
theorem B3868127 : Blo 1144635 3868127 := bstep (se 1 (by rfl) ⟨2901095, by rfl⟩ : syracuseStep 3868127 = 5802191) B5802191
theorem B4360027 : Blo 1144635 4360027 := bstep (se 1 (by rfl) ⟨3270020, by rfl⟩ : syracuseStep 4360027 = 6540041) B6540041
theorem B4360787 : Blo 1144635 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B3870395 : Blo 1144635 3870395 := bstep (se 1 (by rfl) ⟨2902796, by rfl⟩ : syracuseStep 3870395 = 5805593) B5805593
theorem B4133663 : Blo 1144635 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B2069455 : Blo 1144635 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B8821295 : Blo 1144635 8821295 := bstep (se 1 (by rfl) ⟨6615971, by rfl⟩ : syracuseStep 8821295 = 13231943) B13231943
theorem B3873959 : Blo 1144635 3873959 := bstep (se 1 (by rfl) ⟨2905469, by rfl⟩ : syracuseStep 3873959 = 5810939) B5810939
theorem B3875903 : Blo 1144635 3875903 := bstep (se 1 (by rfl) ⟨2906927, by rfl⟩ : syracuseStep 3875903 = 5813855) B5813855
theorem B7841785 : Blo 1144635 7841785 := bstep (se 2 (by rfl) ⟨2940669, by rfl⟩ : syracuseStep 7841785 = 5881339) B5881339
theorem B1717295 : Blo 1144635 1717295 := bstep (se 1 (by rfl) ⟨1287971, by rfl⟩ : syracuseStep 1717295 = 2575943) B2575943
theorem B14693723 : Blo 1144635 14693723 := bstep (se 1 (by rfl) ⟨11020292, by rfl⟩ : syracuseStep 14693723 = 22040585) B22040585
theorem B8697455 : Blo 1144635 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B134100629 : Blo 1144635 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B1719071 : Blo 1144635 1719071 := bstep (se 1 (by rfl) ⟨1289303, by rfl⟩ : syracuseStep 1719071 = 2578607) B2578607
theorem B1719239 : Blo 1144635 1719239 := bstep (se 1 (by rfl) ⟨1289429, by rfl⟩ : syracuseStep 1719239 = 2578859) B2578859
theorem B1719323 : Blo 1144635 1719323 := bstep (se 1 (by rfl) ⟨1289492, by rfl⟩ : syracuseStep 1719323 = 2578985) B2578985
theorem B1719455 : Blo 1144635 1719455 := bstep (se 1 (by rfl) ⟨1289591, by rfl⟩ : syracuseStep 1719455 = 2579183) B2579183
theorem B19578023 : Blo 1144635 19578023 := bstep (se 1 (by rfl) ⟨14683517, by rfl⟩ : syracuseStep 19578023 = 29367035) B29367035
theorem B1720361 : Blo 1144635 1720361 := bstep (se 2 (by rfl) ⟨645135, by rfl⟩ : syracuseStep 1720361 = 1290271) B1290271
theorem B6275323 : Blo 1144635 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B8700371 : Blo 1144635 8700371 := bstep (se 1 (by rfl) ⟨6525278, by rfl⟩ : syracuseStep 8700371 = 13050557) B13050557
theorem B24758297 : Blo 1144635 24758297 := bstep (se 2 (by rfl) ⟨9284361, by rfl⟩ : syracuseStep 24758297 = 18568723) B18568723
theorem B100419749 : Blo 1144635 100419749 := bstep (se 4 (by rfl) ⟨9414351, by rfl⟩ : syracuseStep 100419749 = 18828703) B18828703
theorem B10471801 : Blo 1144635 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B13060763 : Blo 1144635 13060763 := bstep (se 1 (by rfl) ⟨9795572, by rfl⟩ : syracuseStep 13060763 = 19591145) B19591145
theorem B2576231 : Blo 1144635 2576231 := bstep (se 1 (by rfl) ⟨1932173, by rfl⟩ : syracuseStep 2576231 = 3864347) B3864347
theorem B3264553 : Blo 1144635 3264553 := bstep (se 2 (by rfl) ⟨1224207, by rfl⟩ : syracuseStep 3264553 = 2448415) B2448415
theorem B4903649 : Blo 1144635 4903649 := bstep (se 2 (by rfl) ⟨1838868, by rfl⟩ : syracuseStep 4903649 = 3677737) B3677737
theorem B4249597 : Blo 1144635 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B11032595 : Blo 1144635 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B11032631 : Blo 1144635 11032631 := bstep (se 1 (by rfl) ⟨8274473, by rfl⟩ : syracuseStep 11032631 = 16548947) B16548947
theorem B2579327 : Blo 1144635 2579327 := bstep (se 1 (by rfl) ⟨1934495, by rfl⟩ : syracuseStep 2579327 = 3868991) B3868991
theorem B4645343 : Blo 1144635 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B1631183 : Blo 1144635 1631183 := bstep (se 1 (by rfl) ⟨1223387, by rfl⟩ : syracuseStep 1631183 = 2446775) B2446775
theorem B9300095 : Blo 1144635 9300095 := bstep (se 1 (by rfl) ⟨6975071, by rfl⟩ : syracuseStep 9300095 = 13950143) B13950143
theorem B83585195 : Blo 1144635 83585195 := bstep (se 1 (by rfl) ⟨62688896, by rfl⟩ : syracuseStep 83585195 = 125377793) B125377793
theorem B7335917 : Blo 1144635 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B4355639 : Blo 1144635 4355639 := bstep (se 1 (by rfl) ⟨3266729, by rfl⟩ : syracuseStep 4355639 = 6533459) B6533459
theorem B3864563 : Blo 1144635 3864563 := bstep (se 1 (by rfl) ⟨2898422, by rfl⟩ : syracuseStep 3864563 = 5796845) B5796845
theorem B1144959 : Blo 1144635 1144959 := bstep (se 1 (by rfl) ⟨858719, by rfl⟩ : syracuseStep 1144959 = 1717439) B1717439
theorem B1931647 : Blo 1144635 1931647 := bstep (se 1 (by rfl) ⟨1448735, by rfl⟩ : syracuseStep 1931647 = 2897471) B2897471
theorem B1145511 : Blo 1144635 1145511 := bstep (se 1 (by rfl) ⟨859133, by rfl⟩ : syracuseStep 1145511 = 1718267) B1718267
theorem B1145663 : Blo 1144635 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B28703965 : Blo 1144635 28703965 := bstep (se 3 (by rfl) ⟨5381993, by rfl⟩ : syracuseStep 28703965 = 10763987) B10763987
theorem B1768927 : Blo 1144635 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B1146727 : Blo 1144635 1146727 := bstep (se 1 (by rfl) ⟨860045, by rfl⟩ : syracuseStep 1146727 = 1720091) B1720091
theorem B7339967 : Blo 1144635 7339967 := bstep (se 1 (by rfl) ⟨5504975, by rfl⟩ : syracuseStep 7339967 = 11009951) B11009951
theorem B1146907 : Blo 1144635 1146907 := bstep (se 1 (by rfl) ⟨860180, by rfl⟩ : syracuseStep 1146907 = 1720361) B1720361
theorem B19595519 : Blo 1144635 19595519 := bstep (se 1 (by rfl) ⟨14696639, by rfl⟩ : syracuseStep 19595519 = 29393279) B29393279
theorem B5800247 : Blo 1144635 5800247 := bstep (se 1 (by rfl) ⟨4350185, by rfl⟩ : syracuseStep 5800247 = 8700371) B8700371
theorem B66946499 : Blo 1144635 66946499 := bstep (se 1 (by rfl) ⟨50209874, by rfl⟩ : syracuseStep 66946499 = 100419749) B100419749
theorem B10455713 : Blo 1144635 10455713 := bstep (se 2 (by rfl) ⟨3920892, by rfl⟩ : syracuseStep 10455713 = 7841785) B7841785
theorem B3673021 : Blo 1144635 3673021 := bstep (se 3 (by rfl) ⟨688691, by rfl⟩ : syracuseStep 3673021 = 1377383) B1377383
theorem B13962401 : Blo 1144635 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B2755775 : Blo 1144635 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B2759273 : Blo 1144635 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B6200063 : Blo 1144635 6200063 := bstep (se 1 (by rfl) ⟨4650047, by rfl⟩ : syracuseStep 6200063 = 9300095) B9300095
theorem B4890611 : Blo 1144635 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B89400419 : Blo 1144635 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B13052015 : Blo 1144635 13052015 := bstep (se 1 (by rfl) ⟨9789011, by rfl⟩ : syracuseStep 13052015 = 19578023) B19578023
theorem B4893311 : Blo 1144635 4893311 := bstep (se 1 (by rfl) ⟨3669983, by rfl⟩ : syracuseStep 4893311 = 7339967) B7339967
theorem B8367097 : Blo 1144635 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B5813369 : Blo 1144635 5813369 := bstep (se 2 (by rfl) ⟨2180013, by rfl⟩ : syracuseStep 5813369 = 4360027) B4360027
theorem B1717487 : Blo 1144635 1717487 := bstep (se 1 (by rfl) ⟨1288115, by rfl⟩ : syracuseStep 1717487 = 2576231) B2576231
theorem B7355063 : Blo 1144635 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B7355087 : Blo 1144635 7355087 := bstep (se 1 (by rfl) ⟨5516315, by rfl⟩ : syracuseStep 7355087 = 11032631) B11032631
theorem B5880863 : Blo 1144635 5880863 := bstep (se 1 (by rfl) ⟨4410647, by rfl⟩ : syracuseStep 5880863 = 8821295) B8821295
theorem B1719551 : Blo 1144635 1719551 := bstep (se 1 (by rfl) ⟨1289663, by rfl⟩ : syracuseStep 1719551 = 2579327) B2579327
theorem B3096895 : Blo 1144635 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B55723463 : Blo 1144635 55723463 := bstep (se 1 (by rfl) ⟨41792597, by rfl⟩ : syracuseStep 55723463 = 83585195) B83585195
theorem B2575529 : Blo 1144635 2575529 := bstep (se 2 (by rfl) ⟨965823, by rfl⟩ : syracuseStep 2575529 = 1931647) B1931647
theorem B2903759 : Blo 1144635 2903759 := bstep (se 1 (by rfl) ⟨2177819, by rfl⟩ : syracuseStep 2903759 = 4355639) B4355639
theorem B2576375 : Blo 1144635 2576375 := bstep (se 1 (by rfl) ⟨1932281, by rfl⟩ : syracuseStep 2576375 = 3864563) B3864563
theorem B2578751 : Blo 1144635 2578751 := bstep (se 1 (by rfl) ⟨1934063, by rfl⟩ : syracuseStep 2578751 = 3868127) B3868127
theorem B16505531 : Blo 1144635 16505531 := bstep (se 1 (by rfl) ⟨12379148, by rfl⟩ : syracuseStep 16505531 = 24758297) B24758297
theorem B2907191 : Blo 1144635 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B8707175 : Blo 1144635 8707175 := bstep (se 1 (by rfl) ⟨6530381, by rfl⟩ : syracuseStep 8707175 = 13060763) B13060763
theorem B2580263 : Blo 1144635 2580263 := bstep (se 1 (by rfl) ⟨1935197, by rfl⟩ : syracuseStep 2580263 = 3870395) B3870395
theorem B4349821 : Blo 1144635 4349821 := bstep (se 3 (by rfl) ⟨815591, by rfl⟩ : syracuseStep 4349821 = 1631183) B1631183
theorem B3269099 : Blo 1144635 3269099 := bstep (se 1 (by rfl) ⟨2451824, by rfl⟩ : syracuseStep 3269099 = 4903649) B4903649
theorem B2582639 : Blo 1144635 2582639 := bstep (se 1 (by rfl) ⟨1936979, by rfl⟩ : syracuseStep 2582639 = 3873959) B3873959
theorem B4352737 : Blo 1144635 4352737 := bstep (se 2 (by rfl) ⟨1632276, by rfl⟩ : syracuseStep 4352737 = 3264553) B3264553
theorem B2583935 : Blo 1144635 2583935 := bstep (se 1 (by rfl) ⟨1937951, by rfl⟩ : syracuseStep 2583935 = 3875903) B3875903
theorem B5666129 : Blo 1144635 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B1144863 : Blo 1144635 1144863 := bstep (se 1 (by rfl) ⟨858647, by rfl⟩ : syracuseStep 1144863 = 1717295) B1717295
theorem B9795815 : Blo 1144635 9795815 := bstep (se 1 (by rfl) ⟨7346861, by rfl⟩ : syracuseStep 9795815 = 14693723) B14693723
theorem B5798303 : Blo 1144635 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B38271953 : Blo 1144635 38271953 := bstep (se 2 (by rfl) ⟨14351982, by rfl⟩ : syracuseStep 38271953 = 28703965) B28703965
theorem B1146047 : Blo 1144635 1146047 := bstep (se 1 (by rfl) ⟨859535, by rfl⟩ : syracuseStep 1146047 = 1719071) B1719071
theorem B2358569 : Blo 1144635 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B1146159 : Blo 1144635 1146159 := bstep (se 1 (by rfl) ⟨859619, by rfl⟩ : syracuseStep 1146159 = 1719239) B1719239
theorem B1146215 : Blo 1144635 1146215 := bstep (se 1 (by rfl) ⟨859661, by rfl⟩ : syracuseStep 1146215 = 1719323) B1719323
theorem B1146303 : Blo 1144635 1146303 := bstep (se 1 (by rfl) ⟨859727, by rfl⟩ : syracuseStep 1146303 = 1719455) B1719455
theorem B3866831 : Blo 1144635 3866831 := bstep (se 1 (by rfl) ⟨2900123, by rfl⟩ : syracuseStep 3866831 = 5800247) B5800247
theorem B4129193 : Blo 1144635 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B44630999 : Blo 1144635 44630999 := bstep (se 1 (by rfl) ⟨33473249, by rfl⟩ : syracuseStep 44630999 = 66946499) B66946499
theorem B9308267 : Blo 1144635 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B1837183 : Blo 1144635 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B1935839 : Blo 1144635 1935839 := bstep (se 1 (by rfl) ⟨1451879, by rfl⟩ : syracuseStep 1935839 = 2903759) B2903759
theorem B5803649 : Blo 1144635 5803649 := bstep (se 2 (by rfl) ⟨2176368, by rfl⟩ : syracuseStep 5803649 = 4352737) B4352737
theorem B1839515 : Blo 1144635 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B4133375 : Blo 1144635 4133375 := bstep (se 1 (by rfl) ⟨3100031, by rfl⟩ : syracuseStep 4133375 = 6200063) B6200063
theorem B1938127 : Blo 1144635 1938127 := bstep (se 1 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 1938127 = 2907191) B2907191
theorem B5804783 : Blo 1144635 5804783 := bstep (se 1 (by rfl) ⟨4353587, by rfl⟩ : syracuseStep 5804783 = 8707175) B8707175
theorem B3875579 : Blo 1144635 3875579 := bstep (se 1 (by rfl) ⟨2906684, by rfl⟩ : syracuseStep 3875579 = 5813369) B5813369
theorem B3777419 : Blo 1144635 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B6530543 : Blo 1144635 6530543 := bstep (se 1 (by rfl) ⟨4897907, by rfl⟩ : syracuseStep 6530543 = 9795815) B9795815
theorem B1717019 : Blo 1144635 1717019 := bstep (se 1 (by rfl) ⟨1287764, by rfl⟩ : syracuseStep 1717019 = 2575529) B2575529
theorem B1717583 : Blo 1144635 1717583 := bstep (se 1 (by rfl) ⟨1288187, by rfl⟩ : syracuseStep 1717583 = 2576375) B2576375
theorem B4897361 : Blo 1144635 4897361 := bstep (se 2 (by rfl) ⟨1836510, by rfl⟩ : syracuseStep 4897361 = 3673021) B3673021
theorem B11156129 : Blo 1144635 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B1719167 : Blo 1144635 1719167 := bstep (se 1 (by rfl) ⟨1289375, by rfl⟩ : syracuseStep 1719167 = 2578751) B2578751
theorem B1720175 : Blo 1144635 1720175 := bstep (se 1 (by rfl) ⟨1290131, by rfl⟩ : syracuseStep 1720175 = 2580263) B2580263
theorem B3260407 : Blo 1144635 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B2179399 : Blo 1144635 2179399 := bstep (se 1 (by rfl) ⟨1634549, by rfl⟩ : syracuseStep 2179399 = 3269099) B3269099
theorem B8701343 : Blo 1144635 8701343 := bstep (se 1 (by rfl) ⟨6526007, by rfl⟩ : syracuseStep 8701343 = 13052015) B13052015
theorem B1721759 : Blo 1144635 1721759 := bstep (se 1 (by rfl) ⟨1291319, by rfl⟩ : syracuseStep 1721759 = 2582639) B2582639
theorem B3262207 : Blo 1144635 3262207 := bstep (se 1 (by rfl) ⟨2446655, by rfl⟩ : syracuseStep 3262207 = 4893311) B4893311
theorem B1722623 : Blo 1144635 1722623 := bstep (se 1 (by rfl) ⟨1291967, by rfl⟩ : syracuseStep 1722623 = 2583935) B2583935
theorem B102058541 : Blo 1144635 102058541 := bstep (se 3 (by rfl) ⟨19135976, by rfl⟩ : syracuseStep 102058541 = 38271953) B38271953
theorem B4903375 : Blo 1144635 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B4903391 : Blo 1144635 4903391 := bstep (se 1 (by rfl) ⟨3677543, by rfl⟩ : syracuseStep 4903391 = 7355087) B7355087
theorem B3920575 : Blo 1144635 3920575 := bstep (se 1 (by rfl) ⟨2940431, by rfl⟩ : syracuseStep 3920575 = 5880863) B5880863
theorem B13063679 : Blo 1144635 13063679 := bstep (se 1 (by rfl) ⟨9797759, by rfl⟩ : syracuseStep 13063679 = 19595519) B19595519
theorem B37148975 : Blo 1144635 37148975 := bstep (se 1 (by rfl) ⟨27861731, by rfl⟩ : syracuseStep 37148975 = 55723463) B55723463
theorem B6970475 : Blo 1144635 6970475 := bstep (se 1 (by rfl) ⟨5227856, by rfl⟩ : syracuseStep 6970475 = 10455713) B10455713
theorem B11003687 : Blo 1144635 11003687 := bstep (se 1 (by rfl) ⟨8252765, by rfl⟩ : syracuseStep 11003687 = 16505531) B16505531
theorem B59600279 : Blo 1144635 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B6289517 : Blo 1144635 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B1144991 : Blo 1144635 1144991 := bstep (se 1 (by rfl) ⟨858743, by rfl⟩ : syracuseStep 1144991 = 1717487) B1717487
theorem B3865535 : Blo 1144635 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B1146367 : Blo 1144635 1146367 := bstep (se 1 (by rfl) ⟨859775, by rfl⟩ : syracuseStep 1146367 = 1719551) B1719551
theorem B5799761 : Blo 1144635 5799761 := bstep (se 2 (by rfl) ⟨2174910, by rfl⟩ : syracuseStep 5799761 = 4349821) B4349821
theorem B2752795 : Blo 1144635 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B29753999 : Blo 1144635 29753999 := bstep (se 1 (by rfl) ⟨22315499, by rfl⟩ : syracuseStep 29753999 = 44630999) B44630999
theorem B5800895 : Blo 1144635 5800895 := bstep (se 1 (by rfl) ⟨4350671, by rfl⟩ : syracuseStep 5800895 = 8701343) B8701343
theorem B1147839 : Blo 1144635 1147839 := bstep (se 1 (by rfl) ⟨860879, by rfl⟩ : syracuseStep 1147839 = 1721759) B1721759
theorem B1148415 : Blo 1144635 1148415 := bstep (se 1 (by rfl) ⟨861311, by rfl⟩ : syracuseStep 1148415 = 1722623) B1722623
theorem B3869099 : Blo 1144635 3869099 := bstep (se 1 (by rfl) ⟨2901824, by rfl⟩ : syracuseStep 3869099 = 5803649) B5803649
theorem B2755583 : Blo 1144635 2755583 := bstep (se 1 (by rfl) ⟨2066687, by rfl⟩ : syracuseStep 2755583 = 4133375) B4133375
theorem B3869855 : Blo 1144635 3869855 := bstep (se 1 (by rfl) ⟨2902391, by rfl⟩ : syracuseStep 3869855 = 5804783) B5804783
theorem B6205511 : Blo 1144635 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B1290559 : Blo 1144635 1290559 := bstep (se 1 (by rfl) ⟨967919, by rfl⟩ : syracuseStep 1290559 = 1935839) B1935839
theorem B68039027 : Blo 1144635 68039027 := bstep (se 1 (by rfl) ⟨51029270, by rfl⟩ : syracuseStep 68039027 = 102058541) B102058541
theorem B10073117 : Blo 1144635 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B6537833 : Blo 1144635 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B5227433 : Blo 1144635 5227433 := bstep (se 2 (by rfl) ⟨1960287, by rfl⟩ : syracuseStep 5227433 = 3920575) B3920575
theorem B39733519 : Blo 1144635 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B3264907 : Blo 1144635 3264907 := bstep (se 1 (by rfl) ⟨2448680, by rfl⟩ : syracuseStep 3264907 = 4897361) B4897361
theorem B2577023 : Blo 1144635 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B4347209 : Blo 1144635 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B2577887 : Blo 1144635 2577887 := bstep (se 1 (by rfl) ⟨1933415, by rfl⟩ : syracuseStep 2577887 = 3866831) B3866831
theorem B2905865 : Blo 1144635 2905865 := bstep (se 2 (by rfl) ⟨1089699, by rfl⟩ : syracuseStep 2905865 = 2179399) B2179399
theorem B4905373 : Blo 1144635 4905373 := bstep (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) B1839515
theorem B4349609 : Blo 1144635 4349609 := bstep (se 2 (by rfl) ⟨1631103, by rfl⟩ : syracuseStep 4349609 = 3262207) B3262207
theorem B2449577 : Blo 1144635 2449577 := bstep (se 2 (by rfl) ⟨918591, by rfl⟩ : syracuseStep 2449577 = 1837183) B1837183
theorem B3268927 : Blo 1144635 3268927 := bstep (se 1 (by rfl) ⟨2451695, by rfl⟩ : syracuseStep 3268927 = 4903391) B4903391
theorem B8709119 : Blo 1144635 8709119 := bstep (se 1 (by rfl) ⟨6531839, by rfl⟩ : syracuseStep 8709119 = 13063679) B13063679
theorem B24765983 : Blo 1144635 24765983 := bstep (se 1 (by rfl) ⟨18574487, by rfl⟩ : syracuseStep 24765983 = 37148975) B37148975
theorem B4646983 : Blo 1144635 4646983 := bstep (se 1 (by rfl) ⟨3485237, by rfl⟩ : syracuseStep 4646983 = 6970475) B6970475
theorem B2583719 : Blo 1144635 2583719 := bstep (se 1 (by rfl) ⟨1937789, by rfl⟩ : syracuseStep 2583719 = 3875579) B3875579
theorem B2584169 : Blo 1144635 2584169 := bstep (se 2 (by rfl) ⟨969063, by rfl⟩ : syracuseStep 2584169 = 1938127) B1938127
theorem B4353695 : Blo 1144635 4353695 := bstep (se 1 (by rfl) ⟨3265271, by rfl⟩ : syracuseStep 4353695 = 6530543) B6530543
theorem B7335791 : Blo 1144635 7335791 := bstep (se 1 (by rfl) ⟨5501843, by rfl⟩ : syracuseStep 7335791 = 11003687) B11003687
theorem B1144679 : Blo 1144635 1144679 := bstep (se 1 (by rfl) ⟨858509, by rfl⟩ : syracuseStep 1144679 = 1717019) B1717019
theorem B1145055 : Blo 1144635 1145055 := bstep (se 1 (by rfl) ⟨858791, by rfl⟩ : syracuseStep 1145055 = 1717583) B1717583
theorem B4193011 : Blo 1144635 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B7437419 : Blo 1144635 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B1146111 : Blo 1144635 1146111 := bstep (se 1 (by rfl) ⟨859583, by rfl⟩ : syracuseStep 1146111 = 1719167) B1719167
theorem B3866507 : Blo 1144635 3866507 := bstep (se 1 (by rfl) ⟨2899880, by rfl⟩ : syracuseStep 3866507 = 5799761) B5799761
theorem B1146783 : Blo 1144635 1146783 := bstep (se 1 (by rfl) ⟨860087, by rfl⟩ : syracuseStep 1146783 = 1720175) B1720175
theorem B4358555 : Blo 1144635 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B4358569 : Blo 1144635 4358569 := bstep (se 2 (by rfl) ⟨1634463, by rfl⟩ : syracuseStep 4358569 = 3268927) B3268927
theorem B3867263 : Blo 1144635 3867263 := bstep (se 1 (by rfl) ⟨2900447, by rfl⟩ : syracuseStep 3867263 = 5800895) B5800895
theorem B14681573 : Blo 1144635 14681573 := bstep (se 4 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 14681573 = 2752795) B2752795
theorem B1837055 : Blo 1144635 1837055 := bstep (se 1 (by rfl) ⟨1377791, by rfl⟩ : syracuseStep 1837055 = 2755583) B2755583
theorem B6195977 : Blo 1144635 6195977 := bstep (se 2 (by rfl) ⟨2323491, by rfl⟩ : syracuseStep 6195977 = 4646983) B4646983
theorem B1937243 : Blo 1144635 1937243 := bstep (se 1 (by rfl) ⟨1452932, by rfl⟩ : syracuseStep 1937243 = 2905865) B2905865
theorem B5806079 : Blo 1144635 5806079 := bstep (se 1 (by rfl) ⟨4354559, by rfl⟩ : syracuseStep 5806079 = 8709119) B8709119
theorem B4890527 : Blo 1144635 4890527 := bstep (se 1 (by rfl) ⟨3667895, by rfl⟩ : syracuseStep 4890527 = 7335791) B7335791
theorem B4137007 : Blo 1144635 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B45359351 : Blo 1144635 45359351 := bstep (se 1 (by rfl) ⟨34019513, by rfl⟩ : syracuseStep 45359351 = 68039027) B68039027
theorem B4958279 : Blo 1144635 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B19835999 : Blo 1144635 19835999 := bstep (se 1 (by rfl) ⟨14876999, by rfl⟩ : syracuseStep 19835999 = 29753999) B29753999
theorem B3484955 : Blo 1144635 3484955 := bstep (se 1 (by rfl) ⟨2613716, by rfl⟩ : syracuseStep 3484955 = 5227433) B5227433
theorem B1718015 : Blo 1144635 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B2898139 : Blo 1144635 2898139 := bstep (se 1 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 2898139 = 4347209) B4347209
theorem B1718591 : Blo 1144635 1718591 := bstep (se 1 (by rfl) ⟨1288943, by rfl⟩ : syracuseStep 1718591 = 2577887) B2577887
theorem B22362725 : Blo 1144635 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B2899739 : Blo 1144635 2899739 := bstep (se 1 (by rfl) ⟨2174804, by rfl⟩ : syracuseStep 2899739 = 4349609) B4349609
theorem B1720745 : Blo 1144635 1720745 := bstep (se 2 (by rfl) ⟨645279, by rfl⟩ : syracuseStep 1720745 = 1290559) B1290559
theorem B1722479 : Blo 1144635 1722479 := bstep (se 1 (by rfl) ⟨1291859, by rfl⟩ : syracuseStep 1722479 = 2583719) B2583719
theorem B1722779 : Blo 1144635 1722779 := bstep (se 1 (by rfl) ⟨1292084, by rfl⟩ : syracuseStep 1722779 = 2584169) B2584169
theorem B2902463 : Blo 1144635 2902463 := bstep (se 1 (by rfl) ⟨2176847, by rfl⟩ : syracuseStep 2902463 = 4353695) B4353695
theorem B6540497 : Blo 1144635 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B2577671 : Blo 1144635 2577671 := bstep (se 1 (by rfl) ⟨1933253, by rfl⟩ : syracuseStep 2577671 = 3866507) B3866507
theorem B2579399 : Blo 1144635 2579399 := bstep (se 1 (by rfl) ⟨1934549, by rfl⟩ : syracuseStep 2579399 = 3869099) B3869099
theorem B2579903 : Blo 1144635 2579903 := bstep (se 1 (by rfl) ⟨1934927, by rfl⟩ : syracuseStep 2579903 = 3869855) B3869855
theorem B26861645 : Blo 1144635 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B52978025 : Blo 1144635 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B1633051 : Blo 1144635 1633051 := bstep (se 1 (by rfl) ⟨1224788, by rfl⟩ : syracuseStep 1633051 = 2449577) B2449577
theorem B4353209 : Blo 1144635 4353209 := bstep (se 2 (by rfl) ⟨1632453, by rfl⟩ : syracuseStep 4353209 = 3264907) B3264907
theorem B16510655 : Blo 1144635 16510655 := bstep (se 1 (by rfl) ⟨12382991, by rfl⟩ : syracuseStep 16510655 = 24765983) B24765983
theorem B71631053 : Blo 1144635 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B1147163 : Blo 1144635 1147163 := bstep (se 1 (by rfl) ⟨860372, by rfl⟩ : syracuseStep 1147163 = 1720745) B1720745
theorem B1148319 : Blo 1144635 1148319 := bstep (se 1 (by rfl) ⟨861239, by rfl⟩ : syracuseStep 1148319 = 1722479) B1722479
theorem B1148519 : Blo 1144635 1148519 := bstep (se 1 (by rfl) ⟨861389, by rfl⟩ : syracuseStep 1148519 = 1722779) B1722779
theorem B1934975 : Blo 1144635 1934975 := bstep (se 1 (by rfl) ⟨1451231, by rfl⟩ : syracuseStep 1934975 = 2902463) B2902463
theorem B4130651 : Blo 1144635 4130651 := bstep (se 1 (by rfl) ⟨3097988, by rfl⟩ : syracuseStep 4130651 = 6195977) B6195977
theorem B4360331 : Blo 1144635 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B3870719 : Blo 1144635 3870719 := bstep (se 1 (by rfl) ⟨2903039, by rfl⟩ : syracuseStep 3870719 = 5806079) B5806079
theorem B5516009 : Blo 1144635 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B5811425 : Blo 1144635 5811425 := bstep (se 2 (by rfl) ⟨2179284, by rfl⟩ : syracuseStep 5811425 = 4358569) B4358569
theorem B1224703 : Blo 1144635 1224703 := bstep (se 1 (by rfl) ⟨918527, by rfl⟩ : syracuseStep 1224703 = 1837055) B1837055
theorem B1291495 : Blo 1144635 1291495 := bstep (se 1 (by rfl) ⟨968621, by rfl⟩ : syracuseStep 1291495 = 1937243) B1937243
theorem B1718447 : Blo 1144635 1718447 := bstep (se 1 (by rfl) ⟨1288835, by rfl⟩ : syracuseStep 1718447 = 2577671) B2577671
theorem B1719599 : Blo 1144635 1719599 := bstep (se 1 (by rfl) ⟨1289699, by rfl⟩ : syracuseStep 1719599 = 2579399) B2579399
theorem B1719935 : Blo 1144635 1719935 := bstep (se 1 (by rfl) ⟨1289951, by rfl⟩ : syracuseStep 1719935 = 2579903) B2579903
theorem B3260351 : Blo 1144635 3260351 := bstep (se 1 (by rfl) ⟨2445263, by rfl⟩ : syracuseStep 3260351 = 4890527) B4890527
theorem B13223999 : Blo 1144635 13223999 := bstep (se 1 (by rfl) ⟨9917999, by rfl⟩ : syracuseStep 13223999 = 19835999) B19835999
theorem B2902139 : Blo 1144635 2902139 := bstep (se 1 (by rfl) ⟨2176604, by rfl⟩ : syracuseStep 2902139 = 4353209) B4353209
theorem B9293213 : Blo 1144635 9293213 := bstep (se 3 (by rfl) ⟨1742477, by rfl⟩ : syracuseStep 9293213 = 3484955) B3484955
theorem B2905703 : Blo 1144635 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B2578175 : Blo 1144635 2578175 := bstep (se 1 (by rfl) ⟨1933631, by rfl⟩ : syracuseStep 2578175 = 3867263) B3867263
theorem B9787715 : Blo 1144635 9787715 := bstep (se 1 (by rfl) ⟨7340786, by rfl⟩ : syracuseStep 9787715 = 14681573) B14681573
theorem B8709605 : Blo 1144635 8709605 := bstep (se 4 (by rfl) ⟨816525, by rfl⟩ : syracuseStep 8709605 = 1633051) B1633051
theorem B30239567 : Blo 1144635 30239567 := bstep (se 1 (by rfl) ⟨22679675, by rfl⟩ : syracuseStep 30239567 = 45359351) B45359351
theorem B35318683 : Blo 1144635 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B3305519 : Blo 1144635 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B11007103 : Blo 1144635 11007103 := bstep (se 1 (by rfl) ⟨8255327, by rfl⟩ : syracuseStep 11007103 = 16510655) B16510655
theorem B3864185 : Blo 1144635 3864185 := bstep (se 2 (by rfl) ⟨1449069, by rfl⟩ : syracuseStep 3864185 = 2898139) B2898139
theorem B1145343 : Blo 1144635 1145343 := bstep (se 1 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 1145343 = 1718015) B1718015
theorem B1145727 : Blo 1144635 1145727 := bstep (se 1 (by rfl) ⟨859295, by rfl⟩ : syracuseStep 1145727 = 1718591) B1718591
theorem B14908483 : Blo 1144635 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B1933159 : Blo 1144635 1933159 := bstep (se 1 (by rfl) ⟨1449869, by rfl⟩ : syracuseStep 1933159 = 2899739) B2899739
theorem B2753767 : Blo 1144635 2753767 := bstep (se 1 (by rfl) ⟨2065325, by rfl⟩ : syracuseStep 2753767 = 4130651) B4130651
theorem B8815999 : Blo 1144635 8815999 := bstep (se 1 (by rfl) ⟨6611999, by rfl⟩ : syracuseStep 8815999 = 13223999) B13223999
theorem B1934759 : Blo 1144635 1934759 := bstep (se 1 (by rfl) ⟨1451069, by rfl⟩ : syracuseStep 1934759 = 2902139) B2902139
theorem B6195475 : Blo 1144635 6195475 := bstep (se 1 (by rfl) ⟨4646606, by rfl⟩ : syracuseStep 6195475 = 9293213) B9293213
theorem B1937135 : Blo 1144635 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B47091577 : Blo 1144635 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B6525143 : Blo 1144635 6525143 := bstep (se 1 (by rfl) ⟨4893857, by rfl⟩ : syracuseStep 6525143 = 9787715) B9787715
theorem B5806403 : Blo 1144635 5806403 := bstep (se 1 (by rfl) ⟨4354802, by rfl⟩ : syracuseStep 5806403 = 8709605) B8709605
theorem B3677339 : Blo 1144635 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B20159711 : Blo 1144635 20159711 := bstep (se 1 (by rfl) ⟨15119783, by rfl⟩ : syracuseStep 20159711 = 30239567) B30239567
theorem B3874283 : Blo 1144635 3874283 := bstep (se 1 (by rfl) ⟨2905712, by rfl⟩ : syracuseStep 3874283 = 5811425) B5811425
theorem B2203679 : Blo 1144635 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B2173567 : Blo 1144635 2173567 := bstep (se 1 (by rfl) ⟨1630175, by rfl⟩ : syracuseStep 2173567 = 3260351) B3260351
theorem B6531749 : Blo 1144635 6531749 := bstep (se 4 (by rfl) ⟨612351, by rfl⟩ : syracuseStep 6531749 = 1224703) B1224703
theorem B47754035 : Blo 1144635 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B1289983 : Blo 1144635 1289983 := bstep (se 1 (by rfl) ⟨967487, by rfl⟩ : syracuseStep 1289983 = 1934975) B1934975
theorem B1718783 : Blo 1144635 1718783 := bstep (se 1 (by rfl) ⟨1289087, by rfl⟩ : syracuseStep 1718783 = 2578175) B2578175
theorem B1721993 : Blo 1144635 1721993 := bstep (se 2 (by rfl) ⟨645747, by rfl⟩ : syracuseStep 1721993 = 1291495) B1291495
theorem B2576123 : Blo 1144635 2576123 := bstep (se 1 (by rfl) ⟨1932092, by rfl⟩ : syracuseStep 2576123 = 3864185) B3864185
theorem B19877977 : Blo 1144635 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B2577545 : Blo 1144635 2577545 := bstep (se 2 (by rfl) ⟨966579, by rfl⟩ : syracuseStep 2577545 = 1933159) B1933159
theorem B2906887 : Blo 1144635 2906887 := bstep (se 1 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 2906887 = 4360331) B4360331
theorem B2580479 : Blo 1144635 2580479 := bstep (se 1 (by rfl) ⟨1935359, by rfl⟩ : syracuseStep 2580479 = 3870719) B3870719
theorem B14676137 : Blo 1144635 14676137 := bstep (se 2 (by rfl) ⟨5503551, by rfl⟩ : syracuseStep 14676137 = 11007103) B11007103
theorem B1145631 : Blo 1144635 1145631 := bstep (se 1 (by rfl) ⟨859223, by rfl⟩ : syracuseStep 1145631 = 1718447) B1718447
theorem B1146399 : Blo 1144635 1146399 := bstep (se 1 (by rfl) ⟨859799, by rfl⟩ : syracuseStep 1146399 = 1719599) B1719599
theorem B1146623 : Blo 1144635 1146623 := bstep (se 1 (by rfl) ⟨859967, by rfl⟩ : syracuseStep 1146623 = 1719935) B1719935
theorem B1147995 : Blo 1144635 1147995 := bstep (se 1 (by rfl) ⟨860996, by rfl⟩ : syracuseStep 1147995 = 1721993) B1721993
theorem B3671689 : Blo 1144635 3671689 := bstep (se 2 (by rfl) ⟨1376883, by rfl⟩ : syracuseStep 3671689 = 2753767) B2753767
theorem B8260633 : Blo 1144635 8260633 := bstep (se 2 (by rfl) ⟨3097737, by rfl⟩ : syracuseStep 8260633 = 6195475) B6195475
theorem B3870935 : Blo 1144635 3870935 := bstep (se 1 (by rfl) ⟨2903201, by rfl⟩ : syracuseStep 3870935 = 5806403) B5806403
theorem B13439807 : Blo 1144635 13439807 := bstep (se 1 (by rfl) ⟨10079855, by rfl⟩ : syracuseStep 13439807 = 20159711) B20159711
theorem B62788769 : Blo 1144635 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B3875849 : Blo 1144635 3875849 := bstep (se 2 (by rfl) ⟨1453443, by rfl⟩ : syracuseStep 3875849 = 2906887) B2906887
theorem B1289839 : Blo 1144635 1289839 := bstep (se 1 (by rfl) ⟨967379, by rfl⟩ : syracuseStep 1289839 = 1934759) B1934759
theorem B1291423 : Blo 1144635 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B1717415 : Blo 1144635 1717415 := bstep (se 1 (by rfl) ⟨1288061, by rfl⟩ : syracuseStep 1717415 = 2576123) B2576123
theorem B1718363 : Blo 1144635 1718363 := bstep (se 1 (by rfl) ⟨1288772, by rfl⟩ : syracuseStep 1718363 = 2577545) B2577545
theorem B2898089 : Blo 1144635 2898089 := bstep (se 2 (by rfl) ⟨1086783, by rfl⟩ : syracuseStep 2898089 = 2173567) B2173567
theorem B1719977 : Blo 1144635 1719977 := bstep (se 2 (by rfl) ⟨644991, by rfl⟩ : syracuseStep 1719977 = 1289983) B1289983
theorem B1720319 : Blo 1144635 1720319 := bstep (se 1 (by rfl) ⟨1290239, by rfl⟩ : syracuseStep 1720319 = 2580479) B2580479
theorem B31836023 : Blo 1144635 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B9784091 : Blo 1144635 9784091 := bstep (se 1 (by rfl) ⟨7338068, by rfl⟩ : syracuseStep 9784091 = 14676137) B14676137
theorem B11754665 : Blo 1144635 11754665 := bstep (se 2 (by rfl) ⟨4407999, by rfl⟩ : syracuseStep 11754665 = 8815999) B8815999
theorem B4350095 : Blo 1144635 4350095 := bstep (se 1 (by rfl) ⟨3262571, by rfl⟩ : syracuseStep 4350095 = 6525143) B6525143
theorem B2451559 : Blo 1144635 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B2582855 : Blo 1144635 2582855 := bstep (se 1 (by rfl) ⟨1937141, by rfl⟩ : syracuseStep 2582855 = 3874283) B3874283
theorem B1469119 : Blo 1144635 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B26503969 : Blo 1144635 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B4354499 : Blo 1144635 4354499 := bstep (se 1 (by rfl) ⟨3265874, by rfl⟩ : syracuseStep 4354499 = 6531749) B6531749
theorem B1145855 : Blo 1144635 1145855 := bstep (se 1 (by rfl) ⟨859391, by rfl⟩ : syracuseStep 1145855 = 1718783) B1718783
theorem B6522727 : Blo 1144635 6522727 := bstep (se 1 (by rfl) ⟨4892045, by rfl⟩ : syracuseStep 6522727 = 9784091) B9784091
theorem B11014177 : Blo 1144635 11014177 := bstep (se 2 (by rfl) ⟨4130316, by rfl⟩ : syracuseStep 11014177 = 8260633) B8260633
theorem B7836443 : Blo 1144635 7836443 := bstep (se 1 (by rfl) ⟨5877332, by rfl⟩ : syracuseStep 7836443 = 11754665) B11754665
theorem B4895585 : Blo 1144635 4895585 := bstep (se 2 (by rfl) ⟨1835844, by rfl⟩ : syracuseStep 4895585 = 3671689) B3671689
theorem B8959871 : Blo 1144635 8959871 := bstep (se 1 (by rfl) ⟨6719903, by rfl⟩ : syracuseStep 8959871 = 13439807) B13439807
theorem B41859179 : Blo 1144635 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B35338625 : Blo 1144635 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B1719785 : Blo 1144635 1719785 := bstep (se 2 (by rfl) ⟨644919, by rfl⟩ : syracuseStep 1719785 = 1289839) B1289839
theorem B2900063 : Blo 1144635 2900063 := bstep (se 1 (by rfl) ⟨2175047, by rfl⟩ : syracuseStep 2900063 = 4350095) B4350095
theorem B1721897 : Blo 1144635 1721897 := bstep (se 2 (by rfl) ⟨645711, by rfl⟩ : syracuseStep 1721897 = 1291423) B1291423
theorem B1721903 : Blo 1144635 1721903 := bstep (se 1 (by rfl) ⟨1291427, by rfl⟩ : syracuseStep 1721903 = 2582855) B2582855
theorem B2902999 : Blo 1144635 2902999 := bstep (se 1 (by rfl) ⟨2177249, by rfl⟩ : syracuseStep 2902999 = 4354499) B4354499
theorem B21224015 : Blo 1144635 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B3268745 : Blo 1144635 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B2580623 : Blo 1144635 2580623 := bstep (se 1 (by rfl) ⟨1935467, by rfl⟩ : syracuseStep 2580623 = 3870935) B3870935
theorem B1958825 : Blo 1144635 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B2583899 : Blo 1144635 2583899 := bstep (se 1 (by rfl) ⟨1937924, by rfl⟩ : syracuseStep 2583899 = 3875849) B3875849
theorem B1144943 : Blo 1144635 1144943 := bstep (se 1 (by rfl) ⟨858707, by rfl⟩ : syracuseStep 1144943 = 1717415) B1717415
theorem B1145575 : Blo 1144635 1145575 := bstep (se 1 (by rfl) ⟨859181, by rfl⟩ : syracuseStep 1145575 = 1718363) B1718363
theorem B1932059 : Blo 1144635 1932059 := bstep (se 1 (by rfl) ⟨1449044, by rfl⟩ : syracuseStep 1932059 = 2898089) B2898089
theorem B1146651 : Blo 1144635 1146651 := bstep (se 1 (by rfl) ⟨859988, by rfl⟩ : syracuseStep 1146651 = 1719977) B1719977
theorem B1146879 : Blo 1144635 1146879 := bstep (se 1 (by rfl) ⟨860159, by rfl⟩ : syracuseStep 1146879 = 1720319) B1720319
theorem B1933375 : Blo 1144635 1933375 := bstep (se 1 (by rfl) ⟨1450031, by rfl⟩ : syracuseStep 1933375 = 2900063) B2900063
theorem B1147931 : Blo 1144635 1147931 := bstep (se 1 (by rfl) ⟨860948, by rfl⟩ : syracuseStep 1147931 = 1721897) B1721897
theorem B1147935 : Blo 1144635 1147935 := bstep (se 1 (by rfl) ⟨860951, by rfl⟩ : syracuseStep 1147935 = 1721903) B1721903
theorem B3870665 : Blo 1144635 3870665 := bstep (se 2 (by rfl) ⟨1451499, by rfl⟩ : syracuseStep 3870665 = 2902999) B2902999
theorem B14685569 : Blo 1144635 14685569 := bstep (se 2 (by rfl) ⟨5507088, by rfl⟩ : syracuseStep 14685569 = 11014177) B11014177
theorem B5973247 : Blo 1144635 5973247 := bstep (se 1 (by rfl) ⟨4479935, by rfl⟩ : syracuseStep 5973247 = 8959871) B8959871
theorem B1288039 : Blo 1144635 1288039 := bstep (se 1 (by rfl) ⟨966029, by rfl⟩ : syracuseStep 1288039 = 1932059) B1932059
theorem B8696969 : Blo 1144635 8696969 := bstep (se 2 (by rfl) ⟨3261363, by rfl⟩ : syracuseStep 8696969 = 6522727) B6522727
theorem B5224295 : Blo 1144635 5224295 := bstep (se 1 (by rfl) ⟨3918221, by rfl⟩ : syracuseStep 5224295 = 7836443) B7836443
theorem B2179163 : Blo 1144635 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B1720415 : Blo 1144635 1720415 := bstep (se 1 (by rfl) ⟨1290311, by rfl⟩ : syracuseStep 1720415 = 2580623) B2580623
theorem B1722599 : Blo 1144635 1722599 := bstep (se 1 (by rfl) ⟨1291949, by rfl⟩ : syracuseStep 1722599 = 2583899) B2583899
theorem B3263723 : Blo 1144635 3263723 := bstep (se 1 (by rfl) ⟨2447792, by rfl⟩ : syracuseStep 3263723 = 4895585) B4895585
theorem B27906119 : Blo 1144635 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B14149343 : Blo 1144635 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B1305883 : Blo 1144635 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B23559083 : Blo 1144635 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B1146523 : Blo 1144635 1146523 := bstep (se 1 (by rfl) ⟨859892, by rfl⟩ : syracuseStep 1146523 = 1719785) B1719785
theorem B1146943 : Blo 1144635 1146943 := bstep (se 1 (by rfl) ⟨860207, by rfl⟩ : syracuseStep 1146943 = 1720415) B1720415
theorem B1148399 : Blo 1144635 1148399 := bstep (se 1 (by rfl) ⟨861299, by rfl⟩ : syracuseStep 1148399 = 1722599) B1722599
theorem B7964329 : Blo 1144635 7964329 := bstep (se 2 (by rfl) ⟨2986623, by rfl⟩ : syracuseStep 7964329 = 5973247) B5973247
theorem B1741177 : Blo 1144635 1741177 := bstep (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) B1305883
theorem B13931453 : Blo 1144635 13931453 := bstep (se 3 (by rfl) ⟨2612147, by rfl⟩ : syracuseStep 13931453 = 5224295) B5224295
theorem B15706055 : Blo 1144635 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B5811101 : Blo 1144635 5811101 := bstep (se 3 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 5811101 = 2179163) B2179163
theorem B2175815 : Blo 1144635 2175815 := bstep (se 1 (by rfl) ⟨1631861, by rfl⟩ : syracuseStep 2175815 = 3263723) B3263723
theorem B1717385 : Blo 1144635 1717385 := bstep (se 2 (by rfl) ⟨644019, by rfl⟩ : syracuseStep 1717385 = 1288039) B1288039
theorem B2577833 : Blo 1144635 2577833 := bstep (se 2 (by rfl) ⟨966687, by rfl⟩ : syracuseStep 2577833 = 1933375) B1933375
theorem B2580443 : Blo 1144635 2580443 := bstep (se 1 (by rfl) ⟨1935332, by rfl⟩ : syracuseStep 2580443 = 3870665) B3870665
theorem B18604079 : Blo 1144635 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B9790379 : Blo 1144635 9790379 := bstep (se 1 (by rfl) ⟨7342784, by rfl⟩ : syracuseStep 9790379 = 14685569) B14685569
theorem B9432895 : Blo 1144635 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B5797979 : Blo 1144635 5797979 := bstep (se 1 (by rfl) ⟨4348484, by rfl⟩ : syracuseStep 5797979 = 8696969) B8696969
theorem B10619105 : Blo 1144635 10619105 := bstep (se 2 (by rfl) ⟨3982164, by rfl⟩ : syracuseStep 10619105 = 7964329) B7964329
theorem B6526919 : Blo 1144635 6526919 := bstep (se 1 (by rfl) ⟨4895189, by rfl⟩ : syracuseStep 6526919 = 9790379) B9790379
theorem B3874067 : Blo 1144635 3874067 := bstep (se 1 (by rfl) ⟨2905550, by rfl⟩ : syracuseStep 3874067 = 5811101) B5811101
theorem B1450543 : Blo 1144635 1450543 := bstep (se 1 (by rfl) ⟨1087907, by rfl⟩ : syracuseStep 1450543 = 2175815) B2175815
theorem B9287635 : Blo 1144635 9287635 := bstep (se 1 (by rfl) ⟨6965726, by rfl⟩ : syracuseStep 9287635 = 13931453) B13931453
theorem B1718555 : Blo 1144635 1718555 := bstep (se 1 (by rfl) ⟨1288916, by rfl⟩ : syracuseStep 1718555 = 2577833) B2577833
theorem B1720295 : Blo 1144635 1720295 := bstep (se 1 (by rfl) ⟨1290221, by rfl⟩ : syracuseStep 1720295 = 2580443) B2580443
theorem B12402719 : Blo 1144635 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B10470703 : Blo 1144635 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B12577193 : Blo 1144635 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B2321569 : Blo 1144635 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B1144923 : Blo 1144635 1144923 := bstep (se 1 (by rfl) ⟨858692, by rfl⟩ : syracuseStep 1144923 = 1717385) B1717385
theorem B3865319 : Blo 1144635 3865319 := bstep (se 1 (by rfl) ⟨2898989, by rfl⟩ : syracuseStep 3865319 = 5797979) B5797979
theorem B1934057 : Blo 1144635 1934057 := bstep (se 2 (by rfl) ⟨725271, by rfl⟩ : syracuseStep 1934057 = 1450543) B1450543
theorem B13960937 : Blo 1144635 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B28317613 : Blo 1144635 28317613 := bstep (se 3 (by rfl) ⟨5309552, by rfl⟩ : syracuseStep 28317613 = 10619105) B10619105
theorem B8268479 : Blo 1144635 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B3095425 : Blo 1144635 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B2576879 : Blo 1144635 2576879 := bstep (se 1 (by rfl) ⟨1932659, by rfl⟩ : syracuseStep 2576879 = 3865319) B3865319
theorem B4351279 : Blo 1144635 4351279 := bstep (se 1 (by rfl) ⟨3263459, by rfl⟩ : syracuseStep 4351279 = 6526919) B6526919
theorem B2582711 : Blo 1144635 2582711 := bstep (se 1 (by rfl) ⟨1937033, by rfl⟩ : syracuseStep 2582711 = 3874067) B3874067
theorem B8384795 : Blo 1144635 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B12383513 : Blo 1144635 12383513 := bstep (se 2 (by rfl) ⟨4643817, by rfl⟩ : syracuseStep 12383513 = 9287635) B9287635
theorem B1145703 : Blo 1144635 1145703 := bstep (se 1 (by rfl) ⟨859277, by rfl⟩ : syracuseStep 1145703 = 1718555) B1718555
theorem B1146863 : Blo 1144635 1146863 := bstep (se 1 (by rfl) ⟨860147, by rfl⟩ : syracuseStep 1146863 = 1720295) B1720295
theorem B5801705 : Blo 1144635 5801705 := bstep (se 2 (by rfl) ⟨2175639, by rfl⟩ : syracuseStep 5801705 = 4351279) B4351279
theorem B37229165 : Blo 1144635 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B5512319 : Blo 1144635 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B37756817 : Blo 1144635 37756817 := bstep (se 2 (by rfl) ⟨14158806, by rfl⟩ : syracuseStep 37756817 = 28317613) B28317613
theorem B1289371 : Blo 1144635 1289371 := bstep (se 1 (by rfl) ⟨967028, by rfl⟩ : syracuseStep 1289371 = 1934057) B1934057
theorem B1717919 : Blo 1144635 1717919 := bstep (se 1 (by rfl) ⟨1288439, by rfl⟩ : syracuseStep 1717919 = 2576879) B2576879
theorem B1721807 : Blo 1144635 1721807 := bstep (se 1 (by rfl) ⟨1291355, by rfl⟩ : syracuseStep 1721807 = 2582711) B2582711
theorem B5589863 : Blo 1144635 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B16508933 : Blo 1144635 16508933 := bstep (se 4 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 16508933 = 3095425) B3095425
theorem B8255675 : Blo 1144635 8255675 := bstep (se 1 (by rfl) ⟨6191756, by rfl⟩ : syracuseStep 8255675 = 12383513) B12383513
theorem B1147871 : Blo 1144635 1147871 := bstep (se 1 (by rfl) ⟨860903, by rfl⟩ : syracuseStep 1147871 = 1721807) B1721807
theorem B3867803 : Blo 1144635 3867803 := bstep (se 1 (by rfl) ⟨2900852, by rfl⟩ : syracuseStep 3867803 = 5801705) B5801705
theorem B3674879 : Blo 1144635 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B25171211 : Blo 1144635 25171211 := bstep (se 1 (by rfl) ⟨18878408, by rfl⟩ : syracuseStep 25171211 = 37756817) B37756817
theorem B24819443 : Blo 1144635 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B1719161 : Blo 1144635 1719161 := bstep (se 2 (by rfl) ⟨644685, by rfl⟩ : syracuseStep 1719161 = 1289371) B1289371
theorem B3726575 : Blo 1144635 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B11005955 : Blo 1144635 11005955 := bstep (se 1 (by rfl) ⟨8254466, by rfl⟩ : syracuseStep 11005955 = 16508933) B16508933
theorem B1145279 : Blo 1144635 1145279 := bstep (se 1 (by rfl) ⟨858959, by rfl⟩ : syracuseStep 1145279 = 1717919) B1717919
theorem B5503783 : Blo 1144635 5503783 := bstep (se 1 (by rfl) ⟨4127837, by rfl⟩ : syracuseStep 5503783 = 8255675) B8255675
theorem B16780807 : Blo 1144635 16780807 := bstep (se 1 (by rfl) ⟨12585605, by rfl⟩ : syracuseStep 16780807 = 25171211) B25171211
theorem B2578535 : Blo 1144635 2578535 := bstep (se 1 (by rfl) ⟨1933901, by rfl⟩ : syracuseStep 2578535 = 3867803) B3867803
theorem B2449919 : Blo 1144635 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B2484383 : Blo 1144635 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B7337303 : Blo 1144635 7337303 := bstep (se 1 (by rfl) ⟨5502977, by rfl⟩ : syracuseStep 7337303 = 11005955) B11005955
theorem B7338377 : Blo 1144635 7338377 := bstep (se 2 (by rfl) ⟨2751891, by rfl⟩ : syracuseStep 7338377 = 5503783) B5503783
theorem B16546295 : Blo 1144635 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B1146107 : Blo 1144635 1146107 := bstep (se 1 (by rfl) ⟨859580, by rfl⟩ : syracuseStep 1146107 = 1719161) B1719161
theorem B6625021 : Blo 1144635 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B4891535 : Blo 1144635 4891535 := bstep (se 1 (by rfl) ⟨3668651, by rfl⟩ : syracuseStep 4891535 = 7337303) B7337303
theorem B4892251 : Blo 1144635 4892251 := bstep (se 1 (by rfl) ⟨3669188, by rfl⟩ : syracuseStep 4892251 = 7338377) B7338377
theorem B1719023 : Blo 1144635 1719023 := bstep (se 1 (by rfl) ⟨1289267, by rfl⟩ : syracuseStep 1719023 = 2578535) B2578535
theorem B11030863 : Blo 1144635 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B22374409 : Blo 1144635 22374409 := bstep (se 2 (by rfl) ⟨8390403, by rfl⟩ : syracuseStep 22374409 = 16780807) B16780807
theorem B1633279 : Blo 1144635 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B6523001 : Blo 1144635 6523001 := bstep (se 2 (by rfl) ⟨2446125, by rfl⟩ : syracuseStep 6523001 = 4892251) B4892251
theorem B141333781 : Blo 1144635 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B29832545 : Blo 1144635 29832545 := bstep (se 2 (by rfl) ⟨11187204, by rfl⟩ : syracuseStep 29832545 = 22374409) B22374409
theorem B2177705 : Blo 1144635 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B3261023 : Blo 1144635 3261023 := bstep (se 1 (by rfl) ⟨2445767, by rfl⟩ : syracuseStep 3261023 = 4891535) B4891535
theorem B14707817 : Blo 1144635 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B1146015 : Blo 1144635 1146015 := bstep (se 1 (by rfl) ⟨859511, by rfl⟩ : syracuseStep 1146015 = 1719023) B1719023
theorem B5807213 : Blo 1144635 5807213 := bstep (se 3 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 5807213 = 2177705) B2177705
theorem B9805211 : Blo 1144635 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B2174015 : Blo 1144635 2174015 := bstep (se 1 (by rfl) ⟨1630511, by rfl⟩ : syracuseStep 2174015 = 3261023) B3261023
theorem B4348667 : Blo 1144635 4348667 := bstep (se 1 (by rfl) ⟨3261500, by rfl⟩ : syracuseStep 4348667 = 6523001) B6523001
theorem B188445041 : Blo 1144635 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B19888363 : Blo 1144635 19888363 := bstep (se 1 (by rfl) ⟨14916272, by rfl⟩ : syracuseStep 19888363 = 29832545) B29832545
theorem B3871475 : Blo 1144635 3871475 := bstep (se 1 (by rfl) ⟨2903606, by rfl⟩ : syracuseStep 3871475 = 5807213) B5807213
theorem B1449343 : Blo 1144635 1449343 := bstep (se 1 (by rfl) ⟨1087007, by rfl⟩ : syracuseStep 1449343 = 2174015) B2174015
theorem B26517817 : Blo 1144635 26517817 := bstep (se 2 (by rfl) ⟨9944181, by rfl⟩ : syracuseStep 26517817 = 19888363) B19888363
theorem B2899111 : Blo 1144635 2899111 := bstep (se 1 (by rfl) ⟨2174333, by rfl⟩ : syracuseStep 2899111 = 4348667) B4348667
theorem B6536807 : Blo 1144635 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B125630027 : Blo 1144635 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B35357089 : Blo 1144635 35357089 := bstep (se 2 (by rfl) ⟨13258908, by rfl⟩ : syracuseStep 35357089 = 26517817) B26517817
theorem B2580983 : Blo 1144635 2580983 := bstep (se 1 (by rfl) ⟨1935737, by rfl⟩ : syracuseStep 2580983 = 3871475) B3871475
theorem B83753351 : Blo 1144635 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B3865481 : Blo 1144635 3865481 := bstep (se 2 (by rfl) ⟨1449555, by rfl⟩ : syracuseStep 3865481 = 2899111) B2899111
theorem B1932457 : Blo 1144635 1932457 := bstep (se 2 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 1932457 = 1449343) B1449343
theorem B4357871 : Blo 1144635 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B1720655 : Blo 1144635 1720655 := bstep (se 1 (by rfl) ⟨1290491, by rfl⟩ : syracuseStep 1720655 = 2580983) B2580983
theorem B2576609 : Blo 1144635 2576609 := bstep (se 2 (by rfl) ⟨966228, by rfl⟩ : syracuseStep 2576609 = 1932457) B1932457
theorem B2576987 : Blo 1144635 2576987 := bstep (se 1 (by rfl) ⟨1932740, by rfl⟩ : syracuseStep 2576987 = 3865481) B3865481
theorem B2905247 : Blo 1144635 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B47142785 : Blo 1144635 47142785 := bstep (se 2 (by rfl) ⟨17678544, by rfl⟩ : syracuseStep 47142785 = 35357089) B35357089
theorem B55835567 : Blo 1144635 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B1147103 : Blo 1144635 1147103 := bstep (se 1 (by rfl) ⟨860327, by rfl⟩ : syracuseStep 1147103 = 1720655) B1720655
theorem B1936831 : Blo 1144635 1936831 := bstep (se 1 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 1936831 = 2905247) B2905247
theorem B31428523 : Blo 1144635 31428523 := bstep (se 1 (by rfl) ⟨23571392, by rfl⟩ : syracuseStep 31428523 = 47142785) B47142785
theorem B1717739 : Blo 1144635 1717739 := bstep (se 1 (by rfl) ⟨1288304, by rfl⟩ : syracuseStep 1717739 = 2576609) B2576609
theorem B1717991 : Blo 1144635 1717991 := bstep (se 1 (by rfl) ⟨1288493, by rfl⟩ : syracuseStep 1717991 = 2576987) B2576987
theorem B37223711 : Blo 1144635 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B24815807 : Blo 1144635 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B2582441 : Blo 1144635 2582441 := bstep (se 2 (by rfl) ⟨968415, by rfl⟩ : syracuseStep 2582441 = 1936831) B1936831
theorem B41904697 : Blo 1144635 41904697 := bstep (se 2 (by rfl) ⟨15714261, by rfl⟩ : syracuseStep 41904697 = 31428523) B31428523
theorem B1145159 : Blo 1144635 1145159 := bstep (se 1 (by rfl) ⟨858869, by rfl⟩ : syracuseStep 1145159 = 1717739) B1717739
theorem B1145327 : Blo 1144635 1145327 := bstep (se 1 (by rfl) ⟨858995, by rfl⟩ : syracuseStep 1145327 = 1717991) B1717991
theorem B55872929 : Blo 1144635 55872929 := bstep (se 2 (by rfl) ⟨20952348, by rfl⟩ : syracuseStep 55872929 = 41904697) B41904697
theorem B1721627 : Blo 1144635 1721627 := bstep (se 1 (by rfl) ⟨1291220, by rfl⟩ : syracuseStep 1721627 = 2582441) B2582441
theorem B16543871 : Blo 1144635 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B1147751 : Blo 1144635 1147751 := bstep (se 1 (by rfl) ⟨860813, by rfl⟩ : syracuseStep 1147751 = 1721627) B1721627
theorem B11029247 : Blo 1144635 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B37248619 : Blo 1144635 37248619 := bstep (se 1 (by rfl) ⟨27936464, by rfl⟩ : syracuseStep 37248619 = 55872929) B55872929
theorem B7352831 : Blo 1144635 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B49664825 : Blo 1144635 49664825 := bstep (se 2 (by rfl) ⟨18624309, by rfl⟩ : syracuseStep 49664825 = 37248619) B37248619
theorem B33109883 : Blo 1144635 33109883 := bstep (se 1 (by rfl) ⟨24832412, by rfl⟩ : syracuseStep 33109883 = 49664825) B49664825
theorem B4901887 : Blo 1144635 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B6535849 : Blo 1144635 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B22073255 : Blo 1144635 22073255 := bstep (se 1 (by rfl) ⟨16554941, by rfl⟩ : syracuseStep 22073255 = 33109883) B33109883
theorem B14715503 : Blo 1144635 14715503 := bstep (se 1 (by rfl) ⟨11036627, by rfl⟩ : syracuseStep 14715503 = 22073255) B22073255
theorem B8714465 : Blo 1144635 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 1144635 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B9810335 : Blo 1144635 9810335 := bstep (se 1 (by rfl) ⟨7357751, by rfl⟩ : syracuseStep 9810335 = 14715503) B14715503
theorem B3873095 : Blo 1144635 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B6540223 : Blo 1144635 6540223 := bstep (se 1 (by rfl) ⟨4905167, by rfl⟩ : syracuseStep 6540223 = 9810335) B9810335
theorem B8720297 : Blo 1144635 8720297 := bstep (se 2 (by rfl) ⟨3270111, by rfl⟩ : syracuseStep 8720297 = 6540223) B6540223
theorem B2582063 : Blo 1144635 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B5813531 : Blo 1144635 5813531 := bstep (se 1 (by rfl) ⟨4360148, by rfl⟩ : syracuseStep 5813531 = 8720297) B8720297
theorem B1721375 : Blo 1144635 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B1147583 : Blo 1144635 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B3875687 : Blo 1144635 3875687 := bstep (se 1 (by rfl) ⟨2906765, by rfl⟩ : syracuseStep 3875687 = 5813531) B5813531
theorem B2583791 : Blo 1144635 2583791 := bstep (se 1 (by rfl) ⟨1937843, by rfl⟩ : syracuseStep 2583791 = 3875687) B3875687
theorem B1722527 : Blo 1144635 1722527 := bstep (se 1 (by rfl) ⟨1291895, by rfl⟩ : syracuseStep 1722527 = 2583791) B2583791
theorem B1148351 : Blo 1144635 1148351 := bstep (se 1 (by rfl) ⟨861263, by rfl⟩ : syracuseStep 1148351 = 1722527) B1722527

theorem C0 (j : ℕ) (h1 : 286158 ≤ j) (h2 : j ≤ 286857) : Blo 1144635 (4 * j + 3) := by
  interval_cases j
  · exact B1144635
  · exact B1144639
  · exact B1144643
  · exact B1144647
  · exact B1144651
  · exact B1144655
  · exact B1144659
  · exact B1144663
  · exact B1144667
  · exact B1144671
  · exact B1144675
  · exact B1144679
  · exact B1144683
  · exact B1144687
  · exact B1144691
  · exact B1144695
  · exact B1144699
  · exact B1144703
  · exact B1144707
  · exact B1144711
  · exact B1144715
  · exact B1144719
  · exact B1144723
  · exact B1144727
  · exact B1144731
  · exact B1144735
  · exact B1144739
  · exact B1144743
  · exact B1144747
  · exact B1144751
  · exact B1144755
  · exact B1144759
  · exact B1144763
  · exact B1144767
  · exact B1144771
  · exact B1144775
  · exact B1144779
  · exact B1144783
  · exact B1144787
  · exact B1144791
  · exact B1144795
  · exact B1144799
  · exact B1144803
  · exact B1144807
  · exact B1144811
  · exact B1144815
  · exact B1144819
  · exact B1144823
  · exact B1144827
  · exact B1144831
  · exact B1144835
  · exact B1144839
  · exact B1144843
  · exact B1144847
  · exact B1144851
  · exact B1144855
  · exact B1144859
  · exact B1144863
  · exact B1144867
  · exact B1144871
  · exact B1144875
  · exact B1144879
  · exact B1144883
  · exact B1144887
  · exact B1144891
  · exact B1144895
  · exact B1144899
  · exact B1144903
  · exact B1144907
  · exact B1144911
  · exact B1144915
  · exact B1144919
  · exact B1144923
  · exact B1144927
  · exact B1144931
  · exact B1144935
  · exact B1144939
  · exact B1144943
  · exact B1144947
  · exact B1144951
  · exact B1144955
  · exact B1144959
  · exact B1144963
  · exact B1144967
  · exact B1144971
  · exact B1144975
  · exact B1144979
  · exact B1144983
  · exact B1144987
  · exact B1144991
  · exact B1144995
  · exact B1144999
  · exact B1145003
  · exact B1145007
  · exact B1145011
  · exact B1145015
  · exact B1145019
  · exact B1145023
  · exact B1145027
  · exact B1145031
  · exact B1145035
  · exact B1145039
  · exact B1145043
  · exact B1145047
  · exact B1145051
  · exact B1145055
  · exact B1145059
  · exact B1145063
  · exact B1145067
  · exact B1145071
  · exact B1145075
  · exact B1145079
  · exact B1145083
  · exact B1145087
  · exact B1145091
  · exact B1145095
  · exact B1145099
  · exact B1145103
  · exact B1145107
  · exact B1145111
  · exact B1145115
  · exact B1145119
  · exact B1145123
  · exact B1145127
  · exact B1145131
  · exact B1145135
  · exact B1145139
  · exact B1145143
  · exact B1145147
  · exact B1145151
  · exact B1145155
  · exact B1145159
  · exact B1145163
  · exact B1145167
  · exact B1145171
  · exact B1145175
  · exact B1145179
  · exact B1145183
  · exact B1145187
  · exact B1145191
  · exact B1145195
  · exact B1145199
  · exact B1145203
  · exact B1145207
  · exact B1145211
  · exact B1145215
  · exact B1145219
  · exact B1145223
  · exact B1145227
  · exact B1145231
  · exact B1145235
  · exact B1145239
  · exact B1145243
  · exact B1145247
  · exact B1145251
  · exact B1145255
  · exact B1145259
  · exact B1145263
  · exact B1145267
  · exact B1145271
  · exact B1145275
  · exact B1145279
  · exact B1145283
  · exact B1145287
  · exact B1145291
  · exact B1145295
  · exact B1145299
  · exact B1145303
  · exact B1145307
  · exact B1145311
  · exact B1145315
  · exact B1145319
  · exact B1145323
  · exact B1145327
  · exact B1145331
  · exact B1145335
  · exact B1145339
  · exact B1145343
  · exact B1145347
  · exact B1145351
  · exact B1145355
  · exact B1145359
  · exact B1145363
  · exact B1145367
  · exact B1145371
  · exact B1145375
  · exact B1145379
  · exact B1145383
  · exact B1145387
  · exact B1145391
  · exact B1145395
  · exact B1145399
  · exact B1145403
  · exact B1145407
  · exact B1145411
  · exact B1145415
  · exact B1145419
  · exact B1145423
  · exact B1145427
  · exact B1145431
  · exact B1145435
  · exact B1145439
  · exact B1145443
  · exact B1145447
  · exact B1145451
  · exact B1145455
  · exact B1145459
  · exact B1145463
  · exact B1145467
  · exact B1145471
  · exact B1145475
  · exact B1145479
  · exact B1145483
  · exact B1145487
  · exact B1145491
  · exact B1145495
  · exact B1145499
  · exact B1145503
  · exact B1145507
  · exact B1145511
  · exact B1145515
  · exact B1145519
  · exact B1145523
  · exact B1145527
  · exact B1145531
  · exact B1145535
  · exact B1145539
  · exact B1145543
  · exact B1145547
  · exact B1145551
  · exact B1145555
  · exact B1145559
  · exact B1145563
  · exact B1145567
  · exact B1145571
  · exact B1145575
  · exact B1145579
  · exact B1145583
  · exact B1145587
  · exact B1145591
  · exact B1145595
  · exact B1145599
  · exact B1145603
  · exact B1145607
  · exact B1145611
  · exact B1145615
  · exact B1145619
  · exact B1145623
  · exact B1145627
  · exact B1145631
  · exact B1145635
  · exact B1145639
  · exact B1145643
  · exact B1145647
  · exact B1145651
  · exact B1145655
  · exact B1145659
  · exact B1145663
  · exact B1145667
  · exact B1145671
  · exact B1145675
  · exact B1145679
  · exact B1145683
  · exact B1145687
  · exact B1145691
  · exact B1145695
  · exact B1145699
  · exact B1145703
  · exact B1145707
  · exact B1145711
  · exact B1145715
  · exact B1145719
  · exact B1145723
  · exact B1145727
  · exact B1145731
  · exact B1145735
  · exact B1145739
  · exact B1145743
  · exact B1145747
  · exact B1145751
  · exact B1145755
  · exact B1145759
  · exact B1145763
  · exact B1145767
  · exact B1145771
  · exact B1145775
  · exact B1145779
  · exact B1145783
  · exact B1145787
  · exact B1145791
  · exact B1145795
  · exact B1145799
  · exact B1145803
  · exact B1145807
  · exact B1145811
  · exact B1145815
  · exact B1145819
  · exact B1145823
  · exact B1145827
  · exact B1145831
  · exact B1145835
  · exact B1145839
  · exact B1145843
  · exact B1145847
  · exact B1145851
  · exact B1145855
  · exact B1145859
  · exact B1145863
  · exact B1145867
  · exact B1145871
  · exact B1145875
  · exact B1145879
  · exact B1145883
  · exact B1145887
  · exact B1145891
  · exact B1145895
  · exact B1145899
  · exact B1145903
  · exact B1145907
  · exact B1145911
  · exact B1145915
  · exact B1145919
  · exact B1145923
  · exact B1145927
  · exact B1145931
  · exact B1145935
  · exact B1145939
  · exact B1145943
  · exact B1145947
  · exact B1145951
  · exact B1145955
  · exact B1145959
  · exact B1145963
  · exact B1145967
  · exact B1145971
  · exact B1145975
  · exact B1145979
  · exact B1145983
  · exact B1145987
  · exact B1145991
  · exact B1145995
  · exact B1145999
  · exact B1146003
  · exact B1146007
  · exact B1146011
  · exact B1146015
  · exact B1146019
  · exact B1146023
  · exact B1146027
  · exact B1146031
  · exact B1146035
  · exact B1146039
  · exact B1146043
  · exact B1146047
  · exact B1146051
  · exact B1146055
  · exact B1146059
  · exact B1146063
  · exact B1146067
  · exact B1146071
  · exact B1146075
  · exact B1146079
  · exact B1146083
  · exact B1146087
  · exact B1146091
  · exact B1146095
  · exact B1146099
  · exact B1146103
  · exact B1146107
  · exact B1146111
  · exact B1146115
  · exact B1146119
  · exact B1146123
  · exact B1146127
  · exact B1146131
  · exact B1146135
  · exact B1146139
  · exact B1146143
  · exact B1146147
  · exact B1146151
  · exact B1146155
  · exact B1146159
  · exact B1146163
  · exact B1146167
  · exact B1146171
  · exact B1146175
  · exact B1146179
  · exact B1146183
  · exact B1146187
  · exact B1146191
  · exact B1146195
  · exact B1146199
  · exact B1146203
  · exact B1146207
  · exact B1146211
  · exact B1146215
  · exact B1146219
  · exact B1146223
  · exact B1146227
  · exact B1146231
  · exact B1146235
  · exact B1146239
  · exact B1146243
  · exact B1146247
  · exact B1146251
  · exact B1146255
  · exact B1146259
  · exact B1146263
  · exact B1146267
  · exact B1146271
  · exact B1146275
  · exact B1146279
  · exact B1146283
  · exact B1146287
  · exact B1146291
  · exact B1146295
  · exact B1146299
  · exact B1146303
  · exact B1146307
  · exact B1146311
  · exact B1146315
  · exact B1146319
  · exact B1146323
  · exact B1146327
  · exact B1146331
  · exact B1146335
  · exact B1146339
  · exact B1146343
  · exact B1146347
  · exact B1146351
  · exact B1146355
  · exact B1146359
  · exact B1146363
  · exact B1146367
  · exact B1146371
  · exact B1146375
  · exact B1146379
  · exact B1146383
  · exact B1146387
  · exact B1146391
  · exact B1146395
  · exact B1146399
  · exact B1146403
  · exact B1146407
  · exact B1146411
  · exact B1146415
  · exact B1146419
  · exact B1146423
  · exact B1146427
  · exact B1146431
  · exact B1146435
  · exact B1146439
  · exact B1146443
  · exact B1146447
  · exact B1146451
  · exact B1146455
  · exact B1146459
  · exact B1146463
  · exact B1146467
  · exact B1146471
  · exact B1146475
  · exact B1146479
  · exact B1146483
  · exact B1146487
  · exact B1146491
  · exact B1146495
  · exact B1146499
  · exact B1146503
  · exact B1146507
  · exact B1146511
  · exact B1146515
  · exact B1146519
  · exact B1146523
  · exact B1146527
  · exact B1146531
  · exact B1146535
  · exact B1146539
  · exact B1146543
  · exact B1146547
  · exact B1146551
  · exact B1146555
  · exact B1146559
  · exact B1146563
  · exact B1146567
  · exact B1146571
  · exact B1146575
  · exact B1146579
  · exact B1146583
  · exact B1146587
  · exact B1146591
  · exact B1146595
  · exact B1146599
  · exact B1146603
  · exact B1146607
  · exact B1146611
  · exact B1146615
  · exact B1146619
  · exact B1146623
  · exact B1146627
  · exact B1146631
  · exact B1146635
  · exact B1146639
  · exact B1146643
  · exact B1146647
  · exact B1146651
  · exact B1146655
  · exact B1146659
  · exact B1146663
  · exact B1146667
  · exact B1146671
  · exact B1146675
  · exact B1146679
  · exact B1146683
  · exact B1146687
  · exact B1146691
  · exact B1146695
  · exact B1146699
  · exact B1146703
  · exact B1146707
  · exact B1146711
  · exact B1146715
  · exact B1146719
  · exact B1146723
  · exact B1146727
  · exact B1146731
  · exact B1146735
  · exact B1146739
  · exact B1146743
  · exact B1146747
  · exact B1146751
  · exact B1146755
  · exact B1146759
  · exact B1146763
  · exact B1146767
  · exact B1146771
  · exact B1146775
  · exact B1146779
  · exact B1146783
  · exact B1146787
  · exact B1146791
  · exact B1146795
  · exact B1146799
  · exact B1146803
  · exact B1146807
  · exact B1146811
  · exact B1146815
  · exact B1146819
  · exact B1146823
  · exact B1146827
  · exact B1146831
  · exact B1146835
  · exact B1146839
  · exact B1146843
  · exact B1146847
  · exact B1146851
  · exact B1146855
  · exact B1146859
  · exact B1146863
  · exact B1146867
  · exact B1146871
  · exact B1146875
  · exact B1146879
  · exact B1146883
  · exact B1146887
  · exact B1146891
  · exact B1146895
  · exact B1146899
  · exact B1146903
  · exact B1146907
  · exact B1146911
  · exact B1146915
  · exact B1146919
  · exact B1146923
  · exact B1146927
  · exact B1146931
  · exact B1146935
  · exact B1146939
  · exact B1146943
  · exact B1146947
  · exact B1146951
  · exact B1146955
  · exact B1146959
  · exact B1146963
  · exact B1146967
  · exact B1146971
  · exact B1146975
  · exact B1146979
  · exact B1146983
  · exact B1146987
  · exact B1146991
  · exact B1146995
  · exact B1146999
  · exact B1147003
  · exact B1147007
  · exact B1147011
  · exact B1147015
  · exact B1147019
  · exact B1147023
  · exact B1147027
  · exact B1147031
  · exact B1147035
  · exact B1147039
  · exact B1147043
  · exact B1147047
  · exact B1147051
  · exact B1147055
  · exact B1147059
  · exact B1147063
  · exact B1147067
  · exact B1147071
  · exact B1147075
  · exact B1147079
  · exact B1147083
  · exact B1147087
  · exact B1147091
  · exact B1147095
  · exact B1147099
  · exact B1147103
  · exact B1147107
  · exact B1147111
  · exact B1147115
  · exact B1147119
  · exact B1147123
  · exact B1147127
  · exact B1147131
  · exact B1147135
  · exact B1147139
  · exact B1147143
  · exact B1147147
  · exact B1147151
  · exact B1147155
  · exact B1147159
  · exact B1147163
  · exact B1147167
  · exact B1147171
  · exact B1147175
  · exact B1147179
  · exact B1147183
  · exact B1147187
  · exact B1147191
  · exact B1147195
  · exact B1147199
  · exact B1147203
  · exact B1147207
  · exact B1147211
  · exact B1147215
  · exact B1147219
  · exact B1147223
  · exact B1147227
  · exact B1147231
  · exact B1147235
  · exact B1147239
  · exact B1147243
  · exact B1147247
  · exact B1147251
  · exact B1147255
  · exact B1147259
  · exact B1147263
  · exact B1147267
  · exact B1147271
  · exact B1147275
  · exact B1147279
  · exact B1147283
  · exact B1147287
  · exact B1147291
  · exact B1147295
  · exact B1147299
  · exact B1147303
  · exact B1147307
  · exact B1147311
  · exact B1147315
  · exact B1147319
  · exact B1147323
  · exact B1147327
  · exact B1147331
  · exact B1147335
  · exact B1147339
  · exact B1147343
  · exact B1147347
  · exact B1147351
  · exact B1147355
  · exact B1147359
  · exact B1147363
  · exact B1147367
  · exact B1147371
  · exact B1147375
  · exact B1147379
  · exact B1147383
  · exact B1147387
  · exact B1147391
  · exact B1147395
  · exact B1147399
  · exact B1147403
  · exact B1147407
  · exact B1147411
  · exact B1147415
  · exact B1147419
  · exact B1147423
  · exact B1147427
  · exact B1147431

theorem C1 (j : ℕ) (h1 : 286858 ≤ j) (h2 : j ≤ 287158) : Blo 1144635 (4 * j + 3) := by
  interval_cases j
  · exact B1147435
  · exact B1147439
  · exact B1147443
  · exact B1147447
  · exact B1147451
  · exact B1147455
  · exact B1147459
  · exact B1147463
  · exact B1147467
  · exact B1147471
  · exact B1147475
  · exact B1147479
  · exact B1147483
  · exact B1147487
  · exact B1147491
  · exact B1147495
  · exact B1147499
  · exact B1147503
  · exact B1147507
  · exact B1147511
  · exact B1147515
  · exact B1147519
  · exact B1147523
  · exact B1147527
  · exact B1147531
  · exact B1147535
  · exact B1147539
  · exact B1147543
  · exact B1147547
  · exact B1147551
  · exact B1147555
  · exact B1147559
  · exact B1147563
  · exact B1147567
  · exact B1147571
  · exact B1147575
  · exact B1147579
  · exact B1147583
  · exact B1147587
  · exact B1147591
  · exact B1147595
  · exact B1147599
  · exact B1147603
  · exact B1147607
  · exact B1147611
  · exact B1147615
  · exact B1147619
  · exact B1147623
  · exact B1147627
  · exact B1147631
  · exact B1147635
  · exact B1147639
  · exact B1147643
  · exact B1147647
  · exact B1147651
  · exact B1147655
  · exact B1147659
  · exact B1147663
  · exact B1147667
  · exact B1147671
  · exact B1147675
  · exact B1147679
  · exact B1147683
  · exact B1147687
  · exact B1147691
  · exact B1147695
  · exact B1147699
  · exact B1147703
  · exact B1147707
  · exact B1147711
  · exact B1147715
  · exact B1147719
  · exact B1147723
  · exact B1147727
  · exact B1147731
  · exact B1147735
  · exact B1147739
  · exact B1147743
  · exact B1147747
  · exact B1147751
  · exact B1147755
  · exact B1147759
  · exact B1147763
  · exact B1147767
  · exact B1147771
  · exact B1147775
  · exact B1147779
  · exact B1147783
  · exact B1147787
  · exact B1147791
  · exact B1147795
  · exact B1147799
  · exact B1147803
  · exact B1147807
  · exact B1147811
  · exact B1147815
  · exact B1147819
  · exact B1147823
  · exact B1147827
  · exact B1147831
  · exact B1147835
  · exact B1147839
  · exact B1147843
  · exact B1147847
  · exact B1147851
  · exact B1147855
  · exact B1147859
  · exact B1147863
  · exact B1147867
  · exact B1147871
  · exact B1147875
  · exact B1147879
  · exact B1147883
  · exact B1147887
  · exact B1147891
  · exact B1147895
  · exact B1147899
  · exact B1147903
  · exact B1147907
  · exact B1147911
  · exact B1147915
  · exact B1147919
  · exact B1147923
  · exact B1147927
  · exact B1147931
  · exact B1147935
  · exact B1147939
  · exact B1147943
  · exact B1147947
  · exact B1147951
  · exact B1147955
  · exact B1147959
  · exact B1147963
  · exact B1147967
  · exact B1147971
  · exact B1147975
  · exact B1147979
  · exact B1147983
  · exact B1147987
  · exact B1147991
  · exact B1147995
  · exact B1147999
  · exact B1148003
  · exact B1148007
  · exact B1148011
  · exact B1148015
  · exact B1148019
  · exact B1148023
  · exact B1148027
  · exact B1148031
  · exact B1148035
  · exact B1148039
  · exact B1148043
  · exact B1148047
  · exact B1148051
  · exact B1148055
  · exact B1148059
  · exact B1148063
  · exact B1148067
  · exact B1148071
  · exact B1148075
  · exact B1148079
  · exact B1148083
  · exact B1148087
  · exact B1148091
  · exact B1148095
  · exact B1148099
  · exact B1148103
  · exact B1148107
  · exact B1148111
  · exact B1148115
  · exact B1148119
  · exact B1148123
  · exact B1148127
  · exact B1148131
  · exact B1148135
  · exact B1148139
  · exact B1148143
  · exact B1148147
  · exact B1148151
  · exact B1148155
  · exact B1148159
  · exact B1148163
  · exact B1148167
  · exact B1148171
  · exact B1148175
  · exact B1148179
  · exact B1148183
  · exact B1148187
  · exact B1148191
  · exact B1148195
  · exact B1148199
  · exact B1148203
  · exact B1148207
  · exact B1148211
  · exact B1148215
  · exact B1148219
  · exact B1148223
  · exact B1148227
  · exact B1148231
  · exact B1148235
  · exact B1148239
  · exact B1148243
  · exact B1148247
  · exact B1148251
  · exact B1148255
  · exact B1148259
  · exact B1148263
  · exact B1148267
  · exact B1148271
  · exact B1148275
  · exact B1148279
  · exact B1148283
  · exact B1148287
  · exact B1148291
  · exact B1148295
  · exact B1148299
  · exact B1148303
  · exact B1148307
  · exact B1148311
  · exact B1148315
  · exact B1148319
  · exact B1148323
  · exact B1148327
  · exact B1148331
  · exact B1148335
  · exact B1148339
  · exact B1148343
  · exact B1148347
  · exact B1148351
  · exact B1148355
  · exact B1148359
  · exact B1148363
  · exact B1148367
  · exact B1148371
  · exact B1148375
  · exact B1148379
  · exact B1148383
  · exact B1148387
  · exact B1148391
  · exact B1148395
  · exact B1148399
  · exact B1148403
  · exact B1148407
  · exact B1148411
  · exact B1148415
  · exact B1148419
  · exact B1148423
  · exact B1148427
  · exact B1148431
  · exact B1148435
  · exact B1148439
  · exact B1148443
  · exact B1148447
  · exact B1148451
  · exact B1148455
  · exact B1148459
  · exact B1148463
  · exact B1148467
  · exact B1148471
  · exact B1148475
  · exact B1148479
  · exact B1148483
  · exact B1148487
  · exact B1148491
  · exact B1148495
  · exact B1148499
  · exact B1148503
  · exact B1148507
  · exact B1148511
  · exact B1148515
  · exact B1148519
  · exact B1148523
  · exact B1148527
  · exact B1148531
  · exact B1148535
  · exact B1148539
  · exact B1148543
  · exact B1148547
  · exact B1148551
  · exact B1148555
  · exact B1148559
  · exact B1148563
  · exact B1148567
  · exact B1148571
  · exact B1148575
  · exact B1148579
  · exact B1148583
  · exact B1148587
  · exact B1148591
  · exact B1148595
  · exact B1148599
  · exact B1148603
  · exact B1148607
  · exact B1148611
  · exact B1148615
  · exact B1148619
  · exact B1148623
  · exact B1148627
  · exact B1148631
  · exact B1148635

theorem solution (m : ℕ) (hlo : 1144635 ≤ m) (hhi : m ≤ 1148635) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 286158 ≤ j := by omega
    have hj2 : j ≤ 287158 := by omega
    have hb : Blo 1144635 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 286858 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
