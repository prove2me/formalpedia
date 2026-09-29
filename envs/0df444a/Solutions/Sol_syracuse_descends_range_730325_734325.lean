-- Prove2me | solution 1 for syracuse_descends_range_730325_734325
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:10.527191+00:00
-- url     : https://prove2.me/submissions/e8e1b1a7-e1b6-4943-9083-daa3067b0149

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


theorem B1409125 : Blo 730325 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B85524821 : Blo 730325 85524821 := bbase (se 10 (by rfl) ⟨125280, by rfl⟩ : syracuseStep 85524821 = 250561) (by norm_num)
theorem B3703157 : Blo 730325 3703157 := bbase (se 5 (by rfl) ⟨173585, by rfl⟩ : syracuseStep 3703157 = 347171) (by norm_num)
theorem B10584533 : Blo 730325 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B1671653 : Blo 730325 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B7144213 : Blo 730325 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1115245 : Blo 730325 1115245 := bbase (se 3 (by rfl) ⟨209108, by rfl⟩ : syracuseStep 1115245 = 418217) (by norm_num)
theorem B3802405 : Blo 730325 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B5571989 : Blo 730325 5571989 := bbase (se 6 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 5571989 = 261187) (by norm_num)
theorem B3704453 : Blo 730325 3704453 := bbase (se 4 (by rfl) ⟨347292, by rfl⟩ : syracuseStep 3704453 = 694585) (by norm_num)
theorem B952141 : Blo 730325 952141 := bbase (se 3 (by rfl) ⟨178526, by rfl⟩ : syracuseStep 952141 = 357053) (by norm_num)
theorem B4687733 : Blo 730325 4687733 := bbase (se 5 (by rfl) ⟨219737, by rfl⟩ : syracuseStep 4687733 = 439475) (by norm_num)
theorem B2787317 : Blo 730325 2787317 := bbase (se 5 (by rfl) ⟨130655, by rfl⟩ : syracuseStep 2787317 = 261311) (by norm_num)
theorem B1116413 : Blo 730325 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B2787605 : Blo 730325 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B1116509 : Blo 730325 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B4163957 : Blo 730325 4163957 := bbase (se 5 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 4163957 = 390371) (by norm_num)
theorem B1673597 : Blo 730325 1673597 := bbase (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) (by norm_num)
theorem B821641 : Blo 730325 821641 := bbase (se 2 (by rfl) ⟨308115, by rfl⟩ : syracuseStep 821641 = 616231) (by norm_num)
theorem B2034085 : Blo 730325 2034085 := bbase (se 4 (by rfl) ⟨190695, by rfl⟩ : syracuseStep 2034085 = 381391) (by norm_num)
theorem B821677 : Blo 730325 821677 := bbase (se 3 (by rfl) ⟨154064, by rfl⟩ : syracuseStep 821677 = 308129) (by norm_num)
theorem B821713 : Blo 730325 821713 := bbase (se 2 (by rfl) ⟨308142, by rfl⟩ : syracuseStep 821713 = 616285) (by norm_num)
theorem B821749 : Blo 730325 821749 := bbase (se 5 (by rfl) ⟨38519, by rfl⟩ : syracuseStep 821749 = 77039) (by norm_num)
theorem B3574277 : Blo 730325 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B821785 : Blo 730325 821785 := bbase (se 2 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 821785 = 616339) (by norm_num)
theorem B821821 : Blo 730325 821821 := bbase (se 3 (by rfl) ⟨154091, by rfl⟩ : syracuseStep 821821 = 308183) (by norm_num)
theorem B821857 : Blo 730325 821857 := bbase (se 2 (by rfl) ⟨308196, by rfl⟩ : syracuseStep 821857 = 616393) (by norm_num)
theorem B1608317 : Blo 730325 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B821893 : Blo 730325 821893 := bbase (se 4 (by rfl) ⟨77052, by rfl⟩ : syracuseStep 821893 = 154105) (by norm_num)
theorem B821929 : Blo 730325 821929 := bbase (se 2 (by rfl) ⟨308223, by rfl⟩ : syracuseStep 821929 = 616447) (by norm_num)
theorem B821965 : Blo 730325 821965 := bbase (se 3 (by rfl) ⟨154118, by rfl⟩ : syracuseStep 821965 = 308237) (by norm_num)
theorem B822001 : Blo 730325 822001 := bbase (se 2 (by rfl) ⟨308250, by rfl⟩ : syracuseStep 822001 = 616501) (by norm_num)
theorem B822037 : Blo 730325 822037 := bbase (se 6 (by rfl) ⟨19266, by rfl⟩ : syracuseStep 822037 = 38533) (by norm_num)
theorem B822073 : Blo 730325 822073 := bbase (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) (by norm_num)
theorem B822109 : Blo 730325 822109 := bbase (se 3 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 822109 = 308291) (by norm_num)
theorem B822145 : Blo 730325 822145 := bbase (se 2 (by rfl) ⟨308304, by rfl⟩ : syracuseStep 822145 = 616609) (by norm_num)
theorem B3705749 : Blo 730325 3705749 := bbase (se 6 (by rfl) ⟨86853, by rfl⟩ : syracuseStep 3705749 = 173707) (by norm_num)
theorem B822181 : Blo 730325 822181 := bbase (se 4 (by rfl) ⟨77079, by rfl⟩ : syracuseStep 822181 = 154159) (by norm_num)
theorem B822217 : Blo 730325 822217 := bbase (se 2 (by rfl) ⟨308331, by rfl⟩ : syracuseStep 822217 = 616663) (by norm_num)
theorem B3574757 : Blo 730325 3574757 := bbase (se 4 (by rfl) ⟨335133, by rfl⟩ : syracuseStep 3574757 = 670267) (by norm_num)
theorem B822253 : Blo 730325 822253 := bbase (se 3 (by rfl) ⟨154172, by rfl⟩ : syracuseStep 822253 = 308345) (by norm_num)
theorem B822289 : Blo 730325 822289 := bbase (se 2 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 822289 = 616717) (by norm_num)
theorem B822325 : Blo 730325 822325 := bbase (se 5 (by rfl) ⟨38546, by rfl⟩ : syracuseStep 822325 = 77093) (by norm_num)
theorem B822361 : Blo 730325 822361 := bbase (se 2 (by rfl) ⟨308385, by rfl⟩ : syracuseStep 822361 = 616771) (by norm_num)
theorem B822397 : Blo 730325 822397 := bbase (se 3 (by rfl) ⟨154199, by rfl⟩ : syracuseStep 822397 = 308399) (by norm_num)
theorem B822433 : Blo 730325 822433 := bbase (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) (by norm_num)
theorem B822469 : Blo 730325 822469 := bbase (se 4 (by rfl) ⟨77106, by rfl⟩ : syracuseStep 822469 = 154213) (by norm_num)
theorem B822505 : Blo 730325 822505 := bbase (se 2 (by rfl) ⟨308439, by rfl⟩ : syracuseStep 822505 = 616879) (by norm_num)
theorem B822541 : Blo 730325 822541 := bbase (se 3 (by rfl) ⟨154226, by rfl⟩ : syracuseStep 822541 = 308453) (by norm_num)
theorem B822577 : Blo 730325 822577 := bbase (se 2 (by rfl) ⟨308466, by rfl⟩ : syracuseStep 822577 = 616933) (by norm_num)
theorem B822613 : Blo 730325 822613 := bbase (se 11 (by rfl) ⟨602, by rfl⟩ : syracuseStep 822613 = 1205) (by norm_num)
theorem B822649 : Blo 730325 822649 := bbase (se 2 (by rfl) ⟨308493, by rfl⟩ : syracuseStep 822649 = 616987) (by norm_num)
theorem B822685 : Blo 730325 822685 := bbase (se 3 (by rfl) ⟨154253, by rfl⟩ : syracuseStep 822685 = 308507) (by norm_num)
theorem B822721 : Blo 730325 822721 := bbase (se 2 (by rfl) ⟨308520, by rfl⟩ : syracuseStep 822721 = 617041) (by norm_num)
theorem B822757 : Blo 730325 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B822793 : Blo 730325 822793 := bbase (se 2 (by rfl) ⟨308547, by rfl⟩ : syracuseStep 822793 = 617095) (by norm_num)
theorem B4165141 : Blo 730325 4165141 := bbase (se 6 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 4165141 = 195241) (by norm_num)
theorem B822829 : Blo 730325 822829 := bbase (se 3 (by rfl) ⟨154280, by rfl⟩ : syracuseStep 822829 = 308561) (by norm_num)
theorem B822865 : Blo 730325 822865 := bbase (se 2 (by rfl) ⟨308574, by rfl⟩ : syracuseStep 822865 = 617149) (by norm_num)
theorem B822901 : Blo 730325 822901 := bbase (se 5 (by rfl) ⟨38573, by rfl⟩ : syracuseStep 822901 = 77147) (by norm_num)
theorem B822937 : Blo 730325 822937 := bbase (se 2 (by rfl) ⟨308601, by rfl⟩ : syracuseStep 822937 = 617203) (by norm_num)
theorem B822973 : Blo 730325 822973 := bbase (se 3 (by rfl) ⟨154307, by rfl⟩ : syracuseStep 822973 = 308615) (by norm_num)
theorem B823009 : Blo 730325 823009 := bbase (se 2 (by rfl) ⟨308628, by rfl⟩ : syracuseStep 823009 = 617257) (by norm_num)
theorem B823045 : Blo 730325 823045 := bbase (se 4 (by rfl) ⟨77160, by rfl⟩ : syracuseStep 823045 = 154321) (by norm_num)
theorem B823081 : Blo 730325 823081 := bbase (se 2 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 823081 = 617311) (by norm_num)
theorem B823117 : Blo 730325 823117 := bbase (se 3 (by rfl) ⟨154334, by rfl⟩ : syracuseStep 823117 = 308669) (by norm_num)
theorem B823153 : Blo 730325 823153 := bbase (se 2 (by rfl) ⟨308682, by rfl⟩ : syracuseStep 823153 = 617365) (by norm_num)
theorem B823189 : Blo 730325 823189 := bbase (se 6 (by rfl) ⟨19293, by rfl⟩ : syracuseStep 823189 = 38587) (by norm_num)
theorem B823225 : Blo 730325 823225 := bbase (se 2 (by rfl) ⟨308709, by rfl⟩ : syracuseStep 823225 = 617419) (by norm_num)
theorem B823261 : Blo 730325 823261 := bbase (se 3 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 823261 = 308723) (by norm_num)
theorem B823297 : Blo 730325 823297 := bbase (se 2 (by rfl) ⟨308736, by rfl⟩ : syracuseStep 823297 = 617473) (by norm_num)
theorem B1249285 : Blo 730325 1249285 := bbase (se 4 (by rfl) ⟨117120, by rfl⟩ : syracuseStep 1249285 = 234241) (by norm_num)
theorem B823333 : Blo 730325 823333 := bbase (se 4 (by rfl) ⟨77187, by rfl⟩ : syracuseStep 823333 = 154375) (by norm_num)
theorem B3510341 : Blo 730325 3510341 := bbase (se 4 (by rfl) ⟨329094, by rfl⟩ : syracuseStep 3510341 = 658189) (by norm_num)
theorem B823369 : Blo 730325 823369 := bbase (se 2 (by rfl) ⟨308763, by rfl⟩ : syracuseStep 823369 = 617527) (by norm_num)
theorem B823405 : Blo 730325 823405 := bbase (se 3 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 823405 = 308777) (by norm_num)
theorem B823441 : Blo 730325 823441 := bbase (se 2 (by rfl) ⟨308790, by rfl⟩ : syracuseStep 823441 = 617581) (by norm_num)
theorem B3707045 : Blo 730325 3707045 := bbase (se 4 (by rfl) ⟨347535, by rfl⟩ : syracuseStep 3707045 = 695071) (by norm_num)
theorem B823477 : Blo 730325 823477 := bbase (se 5 (by rfl) ⟨38600, by rfl⟩ : syracuseStep 823477 = 77201) (by norm_num)
theorem B823513 : Blo 730325 823513 := bbase (se 2 (by rfl) ⟨308817, by rfl⟩ : syracuseStep 823513 = 617635) (by norm_num)
theorem B823549 : Blo 730325 823549 := bbase (se 3 (by rfl) ⟨154415, by rfl⟩ : syracuseStep 823549 = 308831) (by norm_num)
theorem B823585 : Blo 730325 823585 := bbase (se 2 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 823585 = 617689) (by norm_num)
theorem B823621 : Blo 730325 823621 := bbase (se 4 (by rfl) ⟨77214, by rfl⟩ : syracuseStep 823621 = 154429) (by norm_num)
theorem B823657 : Blo 730325 823657 := bbase (se 2 (by rfl) ⟨308871, by rfl⟩ : syracuseStep 823657 = 617743) (by norm_num)
theorem B823693 : Blo 730325 823693 := bbase (se 3 (by rfl) ⟨154442, by rfl⟩ : syracuseStep 823693 = 308885) (by norm_num)
theorem B823729 : Blo 730325 823729 := bbase (se 2 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 823729 = 617797) (by norm_num)
theorem B823765 : Blo 730325 823765 := bbase (se 7 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 823765 = 19307) (by norm_num)
theorem B823801 : Blo 730325 823801 := bbase (se 2 (by rfl) ⟨308925, by rfl⟩ : syracuseStep 823801 = 617851) (by norm_num)
theorem B823837 : Blo 730325 823837 := bbase (se 3 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 823837 = 308939) (by norm_num)
theorem B823873 : Blo 730325 823873 := bbase (se 2 (by rfl) ⟨308952, by rfl⟩ : syracuseStep 823873 = 617905) (by norm_num)
theorem B823909 : Blo 730325 823909 := bbase (se 4 (by rfl) ⟨77241, by rfl⟩ : syracuseStep 823909 = 154483) (by norm_num)
theorem B823945 : Blo 730325 823945 := bbase (se 2 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 823945 = 617959) (by norm_num)
theorem B823981 : Blo 730325 823981 := bbase (se 3 (by rfl) ⟨154496, by rfl⟩ : syracuseStep 823981 = 308993) (by norm_num)
theorem B5083829 : Blo 730325 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B824017 : Blo 730325 824017 := bbase (se 2 (by rfl) ⟨309006, by rfl⟩ : syracuseStep 824017 = 618013) (by norm_num)
theorem B1643237 : Blo 730325 1643237 := bbase (se 4 (by rfl) ⟨154053, by rfl⟩ : syracuseStep 1643237 = 308107) (by norm_num)
theorem B824053 : Blo 730325 824053 := bbase (se 5 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 824053 = 77255) (by norm_num)
theorem B824089 : Blo 730325 824089 := bbase (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) (by norm_num)
theorem B1643309 : Blo 730325 1643309 := bbase (se 3 (by rfl) ⟨308120, by rfl⟩ : syracuseStep 1643309 = 616241) (by norm_num)
theorem B824125 : Blo 730325 824125 := bbase (se 3 (by rfl) ⟨154523, by rfl⟩ : syracuseStep 824125 = 309047) (by norm_num)
theorem B824161 : Blo 730325 824161 := bbase (se 2 (by rfl) ⟨309060, by rfl⟩ : syracuseStep 824161 = 618121) (by norm_num)
theorem B1643381 : Blo 730325 1643381 := bbase (se 5 (by rfl) ⟨77033, by rfl⟩ : syracuseStep 1643381 = 154067) (by norm_num)
theorem B824197 : Blo 730325 824197 := bbase (se 4 (by rfl) ⟨77268, by rfl⟩ : syracuseStep 824197 = 154537) (by norm_num)
theorem B824233 : Blo 730325 824233 := bbase (se 2 (by rfl) ⟨309087, by rfl⟩ : syracuseStep 824233 = 618175) (by norm_num)
theorem B1643453 : Blo 730325 1643453 := bbase (se 3 (by rfl) ⟨308147, by rfl⟩ : syracuseStep 1643453 = 616295) (by norm_num)
theorem B824269 : Blo 730325 824269 := bbase (se 3 (by rfl) ⟨154550, by rfl⟩ : syracuseStep 824269 = 309101) (by norm_num)
theorem B824305 : Blo 730325 824305 := bbase (se 2 (by rfl) ⟨309114, by rfl⟩ : syracuseStep 824305 = 618229) (by norm_num)
theorem B1643525 : Blo 730325 1643525 := bbase (se 4 (by rfl) ⟨154080, by rfl⟩ : syracuseStep 1643525 = 308161) (by norm_num)
theorem B824341 : Blo 730325 824341 := bbase (se 6 (by rfl) ⟨19320, by rfl⟩ : syracuseStep 824341 = 38641) (by norm_num)
theorem B824377 : Blo 730325 824377 := bbase (se 2 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 824377 = 618283) (by norm_num)
theorem B1643597 : Blo 730325 1643597 := bbase (se 3 (by rfl) ⟨308174, by rfl⟩ : syracuseStep 1643597 = 616349) (by norm_num)
theorem B824413 : Blo 730325 824413 := bbase (se 3 (by rfl) ⟨154577, by rfl⟩ : syracuseStep 824413 = 309155) (by norm_num)
theorem B824449 : Blo 730325 824449 := bbase (se 2 (by rfl) ⟨309168, by rfl⟩ : syracuseStep 824449 = 618337) (by norm_num)
theorem B1643669 : Blo 730325 1643669 := bbase (se 6 (by rfl) ⟨38523, by rfl⟩ : syracuseStep 1643669 = 77047) (by norm_num)
theorem B824485 : Blo 730325 824485 := bbase (se 4 (by rfl) ⟨77295, by rfl⟩ : syracuseStep 824485 = 154591) (by norm_num)
theorem B824521 : Blo 730325 824521 := bbase (se 2 (by rfl) ⟨309195, by rfl⟩ : syracuseStep 824521 = 618391) (by norm_num)
theorem B1643741 : Blo 730325 1643741 := bbase (se 3 (by rfl) ⟨308201, by rfl⟩ : syracuseStep 1643741 = 616403) (by norm_num)
theorem B824557 : Blo 730325 824557 := bbase (se 3 (by rfl) ⟨154604, by rfl⟩ : syracuseStep 824557 = 309209) (by norm_num)
theorem B824593 : Blo 730325 824593 := bbase (se 2 (by rfl) ⟨309222, by rfl⟩ : syracuseStep 824593 = 618445) (by norm_num)
theorem B1643813 : Blo 730325 1643813 := bbase (se 4 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 1643813 = 308215) (by norm_num)
theorem B824629 : Blo 730325 824629 := bbase (se 5 (by rfl) ⟨38654, by rfl⟩ : syracuseStep 824629 = 77309) (by norm_num)
theorem B1250621 : Blo 730325 1250621 := bbase (se 3 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 1250621 = 468983) (by norm_num)
theorem B824665 : Blo 730325 824665 := bbase (se 2 (by rfl) ⟨309249, by rfl⟩ : syracuseStep 824665 = 618499) (by norm_num)
theorem B1643885 : Blo 730325 1643885 := bbase (se 3 (by rfl) ⟨308228, by rfl⟩ : syracuseStep 1643885 = 616457) (by norm_num)
theorem B824701 : Blo 730325 824701 := bbase (se 3 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 824701 = 309263) (by norm_num)
theorem B824737 : Blo 730325 824737 := bbase (se 2 (by rfl) ⟨309276, by rfl⟩ : syracuseStep 824737 = 618553) (by norm_num)
theorem B1643957 : Blo 730325 1643957 := bbase (se 5 (by rfl) ⟨77060, by rfl⟩ : syracuseStep 1643957 = 154121) (by norm_num)
theorem B3708341 : Blo 730325 3708341 := bbase (se 5 (by rfl) ⟨173828, by rfl⟩ : syracuseStep 3708341 = 347657) (by norm_num)
theorem B824773 : Blo 730325 824773 := bbase (se 4 (by rfl) ⟨77322, by rfl⟩ : syracuseStep 824773 = 154645) (by norm_num)
theorem B4167125 : Blo 730325 4167125 := bbase (se 7 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 4167125 = 97667) (by norm_num)
theorem B824809 : Blo 730325 824809 := bbase (se 2 (by rfl) ⟨309303, by rfl⟩ : syracuseStep 824809 = 618607) (by norm_num)
theorem B1644029 : Blo 730325 1644029 := bbase (se 3 (by rfl) ⟨308255, by rfl⟩ : syracuseStep 1644029 = 616511) (by norm_num)
theorem B824845 : Blo 730325 824845 := bbase (se 3 (by rfl) ⟨154658, by rfl⟩ : syracuseStep 824845 = 309317) (by norm_num)
theorem B824881 : Blo 730325 824881 := bbase (se 2 (by rfl) ⟨309330, by rfl⟩ : syracuseStep 824881 = 618661) (by norm_num)
theorem B1644101 : Blo 730325 1644101 := bbase (se 4 (by rfl) ⟨154134, by rfl⟩ : syracuseStep 1644101 = 308269) (by norm_num)
theorem B824917 : Blo 730325 824917 := bbase (se 8 (by rfl) ⟨4833, by rfl⟩ : syracuseStep 824917 = 9667) (by norm_num)
theorem B824953 : Blo 730325 824953 := bbase (se 2 (by rfl) ⟨309357, by rfl⟩ : syracuseStep 824953 = 618715) (by norm_num)
theorem B1644173 : Blo 730325 1644173 := bbase (se 3 (by rfl) ⟨308282, by rfl⟩ : syracuseStep 1644173 = 616565) (by norm_num)
theorem B3511957 : Blo 730325 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B824989 : Blo 730325 824989 := bbase (se 3 (by rfl) ⟨154685, by rfl⟩ : syracuseStep 824989 = 309371) (by norm_num)
theorem B825025 : Blo 730325 825025 := bbase (se 2 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 825025 = 618769) (by norm_num)
theorem B1644245 : Blo 730325 1644245 := bbase (se 7 (by rfl) ⟨19268, by rfl⟩ : syracuseStep 1644245 = 38537) (by norm_num)
theorem B825061 : Blo 730325 825061 := bbase (se 4 (by rfl) ⟨77349, by rfl⟩ : syracuseStep 825061 = 154699) (by norm_num)
theorem B825097 : Blo 730325 825097 := bbase (se 2 (by rfl) ⟨309411, by rfl⟩ : syracuseStep 825097 = 618823) (by norm_num)
theorem B1644317 : Blo 730325 1644317 := bbase (se 3 (by rfl) ⟨308309, by rfl⟩ : syracuseStep 1644317 = 616619) (by norm_num)
theorem B825133 : Blo 730325 825133 := bbase (se 3 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 825133 = 309425) (by norm_num)
theorem B825169 : Blo 730325 825169 := bbase (se 2 (by rfl) ⟨309438, by rfl⟩ : syracuseStep 825169 = 618877) (by norm_num)
theorem B6264661 : Blo 730325 6264661 := bbase (se 9 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 6264661 = 36707) (by norm_num)
theorem B1644389 : Blo 730325 1644389 := bbase (se 4 (by rfl) ⟨154161, by rfl⟩ : syracuseStep 1644389 = 308323) (by norm_num)
theorem B825205 : Blo 730325 825205 := bbase (se 5 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 825205 = 77363) (by norm_num)
theorem B825241 : Blo 730325 825241 := bbase (se 2 (by rfl) ⟨309465, by rfl⟩ : syracuseStep 825241 = 618931) (by norm_num)
theorem B1644461 : Blo 730325 1644461 := bbase (se 3 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 1644461 = 616673) (by norm_num)
theorem B825277 : Blo 730325 825277 := bbase (se 3 (by rfl) ⟨154739, by rfl⟩ : syracuseStep 825277 = 309479) (by norm_num)
theorem B1054661 : Blo 730325 1054661 := bbase (se 4 (by rfl) ⟨98874, by rfl⟩ : syracuseStep 1054661 = 197749) (by norm_num)
theorem B825313 : Blo 730325 825313 := bbase (se 2 (by rfl) ⟨309492, by rfl⟩ : syracuseStep 825313 = 618985) (by norm_num)
theorem B989165 : Blo 730325 989165 := bbase (se 3 (by rfl) ⟨185468, by rfl⟩ : syracuseStep 989165 = 370937) (by norm_num)
theorem B1644533 : Blo 730325 1644533 := bbase (se 5 (by rfl) ⟨77087, by rfl⟩ : syracuseStep 1644533 = 154175) (by norm_num)
theorem B825349 : Blo 730325 825349 := bbase (se 4 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 825349 = 154753) (by norm_num)
theorem B825385 : Blo 730325 825385 := bbase (se 2 (by rfl) ⟨309519, by rfl⟩ : syracuseStep 825385 = 619039) (by norm_num)
theorem B1644605 : Blo 730325 1644605 := bbase (se 3 (by rfl) ⟨308363, by rfl⟩ : syracuseStep 1644605 = 616727) (by norm_num)
theorem B825421 : Blo 730325 825421 := bbase (se 3 (by rfl) ⟨154766, by rfl⟩ : syracuseStep 825421 = 309533) (by norm_num)
theorem B825457 : Blo 730325 825457 := bbase (se 2 (by rfl) ⟨309546, by rfl⟩ : syracuseStep 825457 = 619093) (by norm_num)
theorem B1644677 : Blo 730325 1644677 := bbase (se 4 (by rfl) ⟨154188, by rfl⟩ : syracuseStep 1644677 = 308377) (by norm_num)
theorem B825493 : Blo 730325 825493 := bbase (se 6 (by rfl) ⟨19347, by rfl⟩ : syracuseStep 825493 = 38695) (by norm_num)
theorem B825529 : Blo 730325 825529 := bbase (se 2 (by rfl) ⟨309573, by rfl⟩ : syracuseStep 825529 = 619147) (by norm_num)
theorem B1644749 : Blo 730325 1644749 := bbase (se 3 (by rfl) ⟨308390, by rfl⟩ : syracuseStep 1644749 = 616781) (by norm_num)
theorem B1808605 : Blo 730325 1808605 := bbase (se 3 (by rfl) ⟨339113, by rfl⟩ : syracuseStep 1808605 = 678227) (by norm_num)
theorem B825565 : Blo 730325 825565 := bbase (se 3 (by rfl) ⟨154793, by rfl⟩ : syracuseStep 825565 = 309587) (by norm_num)
theorem B825601 : Blo 730325 825601 := bbase (se 2 (by rfl) ⟨309600, by rfl⟩ : syracuseStep 825601 = 619201) (by norm_num)
theorem B1644821 : Blo 730325 1644821 := bbase (se 6 (by rfl) ⟨38550, by rfl⟩ : syracuseStep 1644821 = 77101) (by norm_num)
theorem B825637 : Blo 730325 825637 := bbase (se 4 (by rfl) ⟨77403, by rfl⟩ : syracuseStep 825637 = 154807) (by norm_num)
theorem B2005301 : Blo 730325 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B825673 : Blo 730325 825673 := bbase (se 2 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 825673 = 619255) (by norm_num)
theorem B1644893 : Blo 730325 1644893 := bbase (se 3 (by rfl) ⟨308417, by rfl⟩ : syracuseStep 1644893 = 616835) (by norm_num)
theorem B825709 : Blo 730325 825709 := bbase (se 3 (by rfl) ⟨154820, by rfl⟩ : syracuseStep 825709 = 309641) (by norm_num)
theorem B825745 : Blo 730325 825745 := bbase (se 2 (by rfl) ⟨309654, by rfl⟩ : syracuseStep 825745 = 619309) (by norm_num)
theorem B1644965 : Blo 730325 1644965 := bbase (se 4 (by rfl) ⟨154215, by rfl⟩ : syracuseStep 1644965 = 308431) (by norm_num)
theorem B825781 : Blo 730325 825781 := bbase (se 5 (by rfl) ⟨38708, by rfl⟩ : syracuseStep 825781 = 77417) (by norm_num)
theorem B825817 : Blo 730325 825817 := bbase (se 2 (by rfl) ⟨309681, by rfl⟩ : syracuseStep 825817 = 619363) (by norm_num)
theorem B1645037 : Blo 730325 1645037 := bbase (se 3 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 1645037 = 616889) (by norm_num)
theorem B825853 : Blo 730325 825853 := bbase (se 3 (by rfl) ⟨154847, by rfl⟩ : syracuseStep 825853 = 309695) (by norm_num)
theorem B825889 : Blo 730325 825889 := bbase (se 2 (by rfl) ⟨309708, by rfl⟩ : syracuseStep 825889 = 619417) (by norm_num)
theorem B1645109 : Blo 730325 1645109 := bbase (se 5 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 1645109 = 154229) (by norm_num)
theorem B825925 : Blo 730325 825925 := bbase (se 4 (by rfl) ⟨77430, by rfl⟩ : syracuseStep 825925 = 154861) (by norm_num)
theorem B4463189 : Blo 730325 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B825961 : Blo 730325 825961 := bbase (se 2 (by rfl) ⟨309735, by rfl⟩ : syracuseStep 825961 = 619471) (by norm_num)
theorem B1645181 : Blo 730325 1645181 := bbase (se 3 (by rfl) ⟨308471, by rfl⟩ : syracuseStep 1645181 = 616943) (by norm_num)
theorem B825997 : Blo 730325 825997 := bbase (se 3 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 825997 = 309749) (by norm_num)
theorem B826033 : Blo 730325 826033 := bbase (se 2 (by rfl) ⟨309762, by rfl⟩ : syracuseStep 826033 = 619525) (by norm_num)
theorem B1645253 : Blo 730325 1645253 := bbase (se 4 (by rfl) ⟨154242, by rfl⟩ : syracuseStep 1645253 = 308485) (by norm_num)
theorem B3709637 : Blo 730325 3709637 := bbase (se 4 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 3709637 = 695557) (by norm_num)
theorem B826069 : Blo 730325 826069 := bbase (se 7 (by rfl) ⟨9680, by rfl⟩ : syracuseStep 826069 = 19361) (by norm_num)
theorem B826105 : Blo 730325 826105 := bbase (se 2 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 826105 = 619579) (by norm_num)
theorem B1645325 : Blo 730325 1645325 := bbase (se 3 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 1645325 = 616997) (by norm_num)
theorem B989965 : Blo 730325 989965 := bbase (se 3 (by rfl) ⟨185618, by rfl⟩ : syracuseStep 989965 = 371237) (by norm_num)
theorem B1481509 : Blo 730325 1481509 := bbase (se 4 (by rfl) ⟨138891, by rfl⟩ : syracuseStep 1481509 = 277783) (by norm_num)
theorem B924473 : Blo 730325 924473 := bbase (se 2 (by rfl) ⟨346677, by rfl⟩ : syracuseStep 924473 = 693355) (by norm_num)
theorem B1645397 : Blo 730325 1645397 := bbase (se 9 (by rfl) ⟨4820, by rfl⟩ : syracuseStep 1645397 = 9641) (by norm_num)
theorem B924529 : Blo 730325 924529 := bbase (se 2 (by rfl) ⟨346698, by rfl⟩ : syracuseStep 924529 = 693397) (by norm_num)
theorem B1645469 : Blo 730325 1645469 := bbase (se 3 (by rfl) ⟨308525, by rfl⟩ : syracuseStep 1645469 = 617051) (by norm_num)
theorem B924625 : Blo 730325 924625 := bbase (se 2 (by rfl) ⟨346734, by rfl⟩ : syracuseStep 924625 = 693469) (by norm_num)
theorem B1645541 : Blo 730325 1645541 := bbase (se 4 (by rfl) ⟨154269, by rfl⟩ : syracuseStep 1645541 = 308539) (by norm_num)
theorem B1645613 : Blo 730325 1645613 := bbase (se 3 (by rfl) ⟨308552, by rfl⟩ : syracuseStep 1645613 = 617105) (by norm_num)
theorem B1645685 : Blo 730325 1645685 := bbase (se 5 (by rfl) ⟨77141, by rfl⟩ : syracuseStep 1645685 = 154283) (by norm_num)
theorem B924797 : Blo 730325 924797 := bbase (se 3 (by rfl) ⟨173399, by rfl⟩ : syracuseStep 924797 = 346799) (by norm_num)
theorem B924853 : Blo 730325 924853 := bbase (se 5 (by rfl) ⟨43352, by rfl⟩ : syracuseStep 924853 = 86705) (by norm_num)
theorem B1645757 : Blo 730325 1645757 := bbase (se 3 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 1645757 = 617159) (by norm_num)
theorem B1645829 : Blo 730325 1645829 := bbase (se 4 (by rfl) ⟨154296, by rfl⟩ : syracuseStep 1645829 = 308593) (by norm_num)
theorem B2465045 : Blo 730325 2465045 := bbase (se 6 (by rfl) ⟨57774, by rfl⟩ : syracuseStep 2465045 = 115549) (by norm_num)
theorem B924949 : Blo 730325 924949 := bbase (se 6 (by rfl) ⟨21678, by rfl⟩ : syracuseStep 924949 = 43357) (by norm_num)
theorem B1645901 : Blo 730325 1645901 := bbase (se 3 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 1645901 = 617213) (by norm_num)
theorem B1645973 : Blo 730325 1645973 := bbase (se 6 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 1645973 = 77155) (by norm_num)
theorem B925121 : Blo 730325 925121 := bbase (se 2 (by rfl) ⟨346920, by rfl⟩ : syracuseStep 925121 = 693841) (by norm_num)
theorem B1646045 : Blo 730325 1646045 := bbase (se 3 (by rfl) ⟨308633, by rfl⟩ : syracuseStep 1646045 = 617267) (by norm_num)
theorem B925177 : Blo 730325 925177 := bbase (se 2 (by rfl) ⟨346941, by rfl⟩ : syracuseStep 925177 = 693883) (by norm_num)
theorem B1646117 : Blo 730325 1646117 := bbase (se 4 (by rfl) ⟨154323, by rfl⟩ : syracuseStep 1646117 = 308647) (by norm_num)
theorem B925273 : Blo 730325 925273 := bbase (se 2 (by rfl) ⟨346977, by rfl⟩ : syracuseStep 925273 = 693955) (by norm_num)
theorem B1646189 : Blo 730325 1646189 := bbase (se 3 (by rfl) ⟨308660, by rfl⟩ : syracuseStep 1646189 = 617321) (by norm_num)
theorem B4169333 : Blo 730325 4169333 := bbase (se 5 (by rfl) ⟨195437, by rfl⟩ : syracuseStep 4169333 = 390875) (by norm_num)
theorem B14294677 : Blo 730325 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B1646261 : Blo 730325 1646261 := bbase (se 5 (by rfl) ⟨77168, by rfl⟩ : syracuseStep 1646261 = 154337) (by norm_num)
theorem B2465477 : Blo 730325 2465477 := bbase (se 4 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 2465477 = 462277) (by norm_num)
theorem B794321 : Blo 730325 794321 := bbase (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) (by norm_num)
theorem B1318621 : Blo 730325 1318621 := bbase (se 3 (by rfl) ⟨247241, by rfl⟩ : syracuseStep 1318621 = 494483) (by norm_num)
theorem B1646333 : Blo 730325 1646333 := bbase (se 3 (by rfl) ⟨308687, by rfl⟩ : syracuseStep 1646333 = 617375) (by norm_num)
theorem B925445 : Blo 730325 925445 := bbase (se 4 (by rfl) ⟨86760, by rfl⟩ : syracuseStep 925445 = 173521) (by norm_num)
theorem B4693781 : Blo 730325 4693781 := bbase (se 6 (by rfl) ⟨110010, by rfl⟩ : syracuseStep 4693781 = 220021) (by norm_num)
theorem B6266645 : Blo 730325 6266645 := bbase (se 6 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 6266645 = 293749) (by norm_num)
theorem B925501 : Blo 730325 925501 := bbase (se 3 (by rfl) ⟨173531, by rfl⟩ : syracuseStep 925501 = 347063) (by norm_num)
theorem B1646405 : Blo 730325 1646405 := bbase (se 4 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 1646405 = 308701) (by norm_num)
theorem B1646477 : Blo 730325 1646477 := bbase (se 3 (by rfl) ⟨308714, by rfl⟩ : syracuseStep 1646477 = 617429) (by norm_num)
theorem B925597 : Blo 730325 925597 := bbase (se 3 (by rfl) ⟨173549, by rfl⟩ : syracuseStep 925597 = 347099) (by norm_num)
theorem B1646549 : Blo 730325 1646549 := bbase (se 7 (by rfl) ⟨19295, by rfl⟩ : syracuseStep 1646549 = 38591) (by norm_num)
theorem B3710933 : Blo 730325 3710933 := bbase (se 7 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 3710933 = 86975) (by norm_num)
theorem B1646621 : Blo 730325 1646621 := bbase (se 3 (by rfl) ⟨308741, by rfl⟩ : syracuseStep 1646621 = 617483) (by norm_num)
theorem B925769 : Blo 730325 925769 := bbase (se 2 (by rfl) ⟨347163, by rfl⟩ : syracuseStep 925769 = 694327) (by norm_num)
theorem B1646693 : Blo 730325 1646693 := bbase (se 4 (by rfl) ⟨154377, by rfl⟩ : syracuseStep 1646693 = 308755) (by norm_num)
theorem B2465909 : Blo 730325 2465909 := bbase (se 5 (by rfl) ⟨115589, by rfl⟩ : syracuseStep 2465909 = 231179) (by norm_num)
theorem B925825 : Blo 730325 925825 := bbase (se 2 (by rfl) ⟨347184, by rfl⟩ : syracuseStep 925825 = 694369) (by norm_num)
theorem B1056925 : Blo 730325 1056925 := bbase (se 3 (by rfl) ⟨198173, by rfl⟩ : syracuseStep 1056925 = 396347) (by norm_num)
theorem B1646765 : Blo 730325 1646765 := bbase (se 3 (by rfl) ⟨308768, by rfl⟩ : syracuseStep 1646765 = 617537) (by norm_num)
theorem B925921 : Blo 730325 925921 := bbase (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) (by norm_num)
theorem B1646837 : Blo 730325 1646837 := bbase (se 5 (by rfl) ⟨77195, by rfl⟩ : syracuseStep 1646837 = 154391) (by norm_num)
theorem B1646909 : Blo 730325 1646909 := bbase (se 3 (by rfl) ⟨308795, by rfl⟩ : syracuseStep 1646909 = 617591) (by norm_num)
theorem B1319261 : Blo 730325 1319261 := bbase (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) (by norm_num)
theorem B1646981 : Blo 730325 1646981 := bbase (se 4 (by rfl) ⟨154404, by rfl⟩ : syracuseStep 1646981 = 308809) (by norm_num)
theorem B926093 : Blo 730325 926093 := bbase (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) (by norm_num)
theorem B926149 : Blo 730325 926149 := bbase (se 4 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 926149 = 173653) (by norm_num)
theorem B1647053 : Blo 730325 1647053 := bbase (se 3 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 1647053 = 617645) (by norm_num)
theorem B3121669 : Blo 730325 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B1647125 : Blo 730325 1647125 := bbase (se 6 (by rfl) ⟨38604, by rfl⟩ : syracuseStep 1647125 = 77209) (by norm_num)
theorem B2466341 : Blo 730325 2466341 := bbase (se 4 (by rfl) ⟨231219, by rfl⟩ : syracuseStep 2466341 = 462439) (by norm_num)
theorem B926245 : Blo 730325 926245 := bbase (se 4 (by rfl) ⟨86835, by rfl⟩ : syracuseStep 926245 = 173671) (by norm_num)
theorem B1647197 : Blo 730325 1647197 := bbase (se 3 (by rfl) ⟨308849, by rfl⟩ : syracuseStep 1647197 = 617699) (by norm_num)
theorem B1253981 : Blo 730325 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B1647269 : Blo 730325 1647269 := bbase (se 4 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 1647269 = 308863) (by norm_num)
theorem B5415605 : Blo 730325 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B926417 : Blo 730325 926417 := bbase (se 2 (by rfl) ⟨347406, by rfl⟩ : syracuseStep 926417 = 694813) (by norm_num)
theorem B1647341 : Blo 730325 1647341 := bbase (se 3 (by rfl) ⟨308876, by rfl⟩ : syracuseStep 1647341 = 617753) (by norm_num)
theorem B926473 : Blo 730325 926473 := bbase (se 2 (by rfl) ⟨347427, by rfl⟩ : syracuseStep 926473 = 694855) (by norm_num)
theorem B5219093 : Blo 730325 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B5022485 : Blo 730325 5022485 := bbase (se 6 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 5022485 = 235429) (by norm_num)
theorem B1647413 : Blo 730325 1647413 := bbase (se 5 (by rfl) ⟨77222, by rfl⟩ : syracuseStep 1647413 = 154445) (by norm_num)
theorem B893749 : Blo 730325 893749 := bbase (se 5 (by rfl) ⟨41894, by rfl⟩ : syracuseStep 893749 = 83789) (by norm_num)
theorem B926569 : Blo 730325 926569 := bbase (se 2 (by rfl) ⟨347463, by rfl⟩ : syracuseStep 926569 = 694927) (by norm_num)
theorem B1647485 : Blo 730325 1647485 := bbase (se 3 (by rfl) ⟨308903, by rfl⟩ : syracuseStep 1647485 = 617807) (by norm_num)
theorem B893857 : Blo 730325 893857 := bbase (se 2 (by rfl) ⟨335196, by rfl⟩ : syracuseStep 893857 = 670393) (by norm_num)
theorem B1647557 : Blo 730325 1647557 := bbase (se 4 (by rfl) ⟨154458, by rfl⟩ : syracuseStep 1647557 = 308917) (by norm_num)
theorem B2466773 : Blo 730325 2466773 := bbase (se 7 (by rfl) ⟨28907, by rfl⟩ : syracuseStep 2466773 = 57815) (by norm_num)
theorem B1647629 : Blo 730325 1647629 := bbase (se 3 (by rfl) ⟨308930, by rfl⟩ : syracuseStep 1647629 = 617861) (by norm_num)
theorem B926741 : Blo 730325 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B926797 : Blo 730325 926797 := bbase (se 3 (by rfl) ⟨173774, by rfl⟩ : syracuseStep 926797 = 347549) (by norm_num)
theorem B1647701 : Blo 730325 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B1647773 : Blo 730325 1647773 := bbase (se 3 (by rfl) ⟨308957, by rfl⟩ : syracuseStep 1647773 = 617915) (by norm_num)
theorem B926893 : Blo 730325 926893 := bbase (se 3 (by rfl) ⟨173792, by rfl⟩ : syracuseStep 926893 = 347585) (by norm_num)
theorem B1647845 : Blo 730325 1647845 := bbase (se 4 (by rfl) ⟨154485, by rfl⟩ : syracuseStep 1647845 = 308971) (by norm_num)
theorem B3712229 : Blo 730325 3712229 := bbase (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) (by norm_num)
theorem B1647917 : Blo 730325 1647917 := bbase (se 3 (by rfl) ⟨308984, by rfl⟩ : syracuseStep 1647917 = 617969) (by norm_num)
theorem B927065 : Blo 730325 927065 := bbase (se 2 (by rfl) ⟨347649, by rfl⟩ : syracuseStep 927065 = 695299) (by norm_num)
theorem B1647989 : Blo 730325 1647989 := bbase (se 5 (by rfl) ⟨77249, by rfl⟩ : syracuseStep 1647989 = 154499) (by norm_num)
theorem B2467205 : Blo 730325 2467205 := bbase (se 4 (by rfl) ⟨231300, by rfl⟩ : syracuseStep 2467205 = 462601) (by norm_num)
theorem B927121 : Blo 730325 927121 := bbase (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) (by norm_num)
theorem B1648061 : Blo 730325 1648061 := bbase (se 3 (by rfl) ⟨309011, by rfl⟩ : syracuseStep 1648061 = 618023) (by norm_num)
theorem B927217 : Blo 730325 927217 := bbase (se 2 (by rfl) ⟨347706, by rfl⟩ : syracuseStep 927217 = 695413) (by norm_num)
theorem B1648133 : Blo 730325 1648133 := bbase (se 4 (by rfl) ⟨154512, by rfl⟩ : syracuseStep 1648133 = 309025) (by norm_num)
theorem B1058333 : Blo 730325 1058333 := bbase (se 3 (by rfl) ⟨198437, by rfl⟩ : syracuseStep 1058333 = 396875) (by norm_num)
theorem B1648205 : Blo 730325 1648205 := bbase (se 3 (by rfl) ⟨309038, by rfl⟩ : syracuseStep 1648205 = 618077) (by norm_num)
theorem B1975909 : Blo 730325 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B1320581 : Blo 730325 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B1648277 : Blo 730325 1648277 := bbase (se 6 (by rfl) ⟨38631, by rfl⟩ : syracuseStep 1648277 = 77263) (by norm_num)
theorem B1255061 : Blo 730325 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B927389 : Blo 730325 927389 := bbase (se 3 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 927389 = 347771) (by norm_num)
theorem B927445 : Blo 730325 927445 := bbase (se 7 (by rfl) ⟨10868, by rfl⟩ : syracuseStep 927445 = 21737) (by norm_num)
theorem B1648349 : Blo 730325 1648349 := bbase (se 3 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 1648349 = 618131) (by norm_num)
theorem B1648421 : Blo 730325 1648421 := bbase (se 4 (by rfl) ⟨154539, by rfl⟩ : syracuseStep 1648421 = 309079) (by norm_num)
theorem B2467637 : Blo 730325 2467637 := bbase (se 5 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 2467637 = 231341) (by norm_num)
theorem B927541 : Blo 730325 927541 := bbase (se 5 (by rfl) ⟨43478, by rfl⟩ : syracuseStep 927541 = 86957) (by norm_num)
theorem B1648493 : Blo 730325 1648493 := bbase (se 3 (by rfl) ⟨309092, by rfl⟩ : syracuseStep 1648493 = 618185) (by norm_num)
theorem B1648565 : Blo 730325 1648565 := bbase (se 5 (by rfl) ⟨77276, by rfl⟩ : syracuseStep 1648565 = 154553) (by norm_num)
theorem B3123157 : Blo 730325 3123157 := bbase (se 7 (by rfl) ⟨36599, by rfl⟩ : syracuseStep 3123157 = 73199) (by norm_num)
theorem B927713 : Blo 730325 927713 := bbase (se 2 (by rfl) ⟨347892, by rfl⟩ : syracuseStep 927713 = 695785) (by norm_num)
theorem B3123173 : Blo 730325 3123173 := bbase (se 4 (by rfl) ⟨292797, by rfl⟩ : syracuseStep 3123173 = 585595) (by norm_num)
theorem B1583101 : Blo 730325 1583101 := bbase (se 3 (by rfl) ⟨296831, by rfl⟩ : syracuseStep 1583101 = 593663) (by norm_num)
theorem B1648637 : Blo 730325 1648637 := bbase (se 3 (by rfl) ⟨309119, by rfl⟩ : syracuseStep 1648637 = 618239) (by norm_num)
theorem B927769 : Blo 730325 927769 := bbase (se 2 (by rfl) ⟨347913, by rfl⟩ : syracuseStep 927769 = 695827) (by norm_num)
theorem B1648709 : Blo 730325 1648709 := bbase (se 4 (by rfl) ⟨154566, by rfl⟩ : syracuseStep 1648709 = 309133) (by norm_num)
theorem B1255493 : Blo 730325 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B6006869 : Blo 730325 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B927865 : Blo 730325 927865 := bbase (se 2 (by rfl) ⟨347949, by rfl⟩ : syracuseStep 927865 = 695899) (by norm_num)
theorem B1648781 : Blo 730325 1648781 := bbase (se 3 (by rfl) ⟨309146, by rfl⟩ : syracuseStep 1648781 = 618293) (by norm_num)
theorem B7514261 : Blo 730325 7514261 := bbase (se 6 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 7514261 = 352231) (by norm_num)
theorem B1648853 : Blo 730325 1648853 := bbase (se 7 (by rfl) ⟨19322, by rfl⟩ : syracuseStep 1648853 = 38645) (by norm_num)
theorem B2468069 : Blo 730325 2468069 := bbase (se 4 (by rfl) ⟨231381, by rfl⟩ : syracuseStep 2468069 = 462763) (by norm_num)
theorem B1386733 : Blo 730325 1386733 := bbase (se 3 (by rfl) ⟨260012, by rfl⟩ : syracuseStep 1386733 = 520025) (by norm_num)
theorem B1583381 : Blo 730325 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B1648925 : Blo 730325 1648925 := bbase (se 3 (by rfl) ⟨309173, by rfl⟩ : syracuseStep 1648925 = 618347) (by norm_num)
theorem B928037 : Blo 730325 928037 := bbase (se 4 (by rfl) ⟨87003, by rfl⟩ : syracuseStep 928037 = 174007) (by norm_num)
theorem B1321309 : Blo 730325 1321309 := bbase (se 3 (by rfl) ⟨247745, by rfl⟩ : syracuseStep 1321309 = 495491) (by norm_num)
theorem B928093 : Blo 730325 928093 := bbase (se 3 (by rfl) ⟨174017, by rfl⟩ : syracuseStep 928093 = 348035) (by norm_num)
theorem B1648997 : Blo 730325 1648997 := bbase (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) (by norm_num)
theorem B1386877 : Blo 730325 1386877 := bbase (se 3 (by rfl) ⟨260039, by rfl⟩ : syracuseStep 1386877 = 520079) (by norm_num)
theorem B1649069 : Blo 730325 1649069 := bbase (se 3 (by rfl) ⟨309200, by rfl⟩ : syracuseStep 1649069 = 618401) (by norm_num)
theorem B928189 : Blo 730325 928189 := bbase (se 3 (by rfl) ⟨174035, by rfl⟩ : syracuseStep 928189 = 348071) (by norm_num)
theorem B1649141 : Blo 730325 1649141 := bbase (se 5 (by rfl) ⟨77303, by rfl⟩ : syracuseStep 1649141 = 154607) (by norm_num)
theorem B3713525 : Blo 730325 3713525 := bbase (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) (by norm_num)
theorem B1387037 : Blo 730325 1387037 := bbase (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) (by norm_num)
theorem B1321525 : Blo 730325 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1649213 : Blo 730325 1649213 := bbase (se 3 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 1649213 = 618455) (by norm_num)
theorem B928361 : Blo 730325 928361 := bbase (se 2 (by rfl) ⟨348135, by rfl⟩ : syracuseStep 928361 = 696271) (by norm_num)
theorem B5548661 : Blo 730325 5548661 := bbase (se 5 (by rfl) ⟨260093, by rfl⟩ : syracuseStep 5548661 = 520187) (by norm_num)
theorem B1649285 : Blo 730325 1649285 := bbase (se 4 (by rfl) ⟨154620, by rfl⟩ : syracuseStep 1649285 = 309241) (by norm_num)
theorem B2468501 : Blo 730325 2468501 := bbase (se 6 (by rfl) ⟨57855, by rfl⟩ : syracuseStep 2468501 = 115711) (by norm_num)
theorem B928417 : Blo 730325 928417 := bbase (se 2 (by rfl) ⟨348156, by rfl⟩ : syracuseStep 928417 = 696313) (by norm_num)
theorem B1387181 : Blo 730325 1387181 := bbase (se 3 (by rfl) ⟨260096, by rfl⟩ : syracuseStep 1387181 = 520193) (by norm_num)
theorem B1649357 : Blo 730325 1649357 := bbase (se 3 (by rfl) ⟨309254, by rfl⟩ : syracuseStep 1649357 = 618509) (by norm_num)
theorem B1780445 : Blo 730325 1780445 := bbase (se 3 (by rfl) ⟨333833, by rfl⟩ : syracuseStep 1780445 = 667667) (by norm_num)
theorem B928513 : Blo 730325 928513 := bbase (se 2 (by rfl) ⟨348192, by rfl⟩ : syracuseStep 928513 = 696385) (by norm_num)
theorem B1649429 : Blo 730325 1649429 := bbase (se 6 (by rfl) ⟨38658, by rfl⟩ : syracuseStep 1649429 = 77317) (by norm_num)
theorem B1649501 : Blo 730325 1649501 := bbase (se 3 (by rfl) ⟨309281, by rfl⟩ : syracuseStep 1649501 = 618563) (by norm_num)
theorem B1649573 : Blo 730325 1649573 := bbase (se 4 (by rfl) ⟨154647, by rfl⟩ : syracuseStep 1649573 = 309295) (by norm_num)
theorem B928685 : Blo 730325 928685 := bbase (se 3 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 928685 = 348257) (by norm_num)
theorem B1387469 : Blo 730325 1387469 := bbase (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) (by norm_num)
theorem B928741 : Blo 730325 928741 := bbase (se 4 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 928741 = 174139) (by norm_num)
theorem B1649645 : Blo 730325 1649645 := bbase (se 3 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 1649645 = 618617) (by norm_num)
theorem B1322029 : Blo 730325 1322029 := bbase (se 3 (by rfl) ⟨247880, by rfl⟩ : syracuseStep 1322029 = 495761) (by norm_num)
theorem B1649717 : Blo 730325 1649717 := bbase (se 5 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 1649717 = 154661) (by norm_num)
theorem B2468933 : Blo 730325 2468933 := bbase (se 4 (by rfl) ⟨231462, by rfl⟩ : syracuseStep 2468933 = 462925) (by norm_num)
theorem B928837 : Blo 730325 928837 := bbase (se 4 (by rfl) ⟨87078, by rfl⟩ : syracuseStep 928837 = 174157) (by norm_num)
theorem B1387621 : Blo 730325 1387621 := bbase (se 4 (by rfl) ⟨130089, by rfl⟩ : syracuseStep 1387621 = 260179) (by norm_num)
theorem B1649789 : Blo 730325 1649789 := bbase (se 3 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 1649789 = 618671) (by norm_num)
theorem B1649861 : Blo 730325 1649861 := bbase (se 4 (by rfl) ⟨154674, by rfl⟩ : syracuseStep 1649861 = 309349) (by norm_num)
theorem B929009 : Blo 730325 929009 := bbase (se 2 (by rfl) ⟨348378, by rfl⟩ : syracuseStep 929009 = 696757) (by norm_num)
theorem B7056629 : Blo 730325 7056629 := bbase (se 5 (by rfl) ⟨330779, by rfl⟩ : syracuseStep 7056629 = 661559) (by norm_num)
theorem B1649933 : Blo 730325 1649933 := bbase (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) (by norm_num)
theorem B929065 : Blo 730325 929065 := bbase (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) (by norm_num)
theorem B1650005 : Blo 730325 1650005 := bbase (se 11 (by rfl) ⟨1208, by rfl⟩ : syracuseStep 1650005 = 2417) (by norm_num)
theorem B1486181 : Blo 730325 1486181 := bbase (se 4 (by rfl) ⟨139329, by rfl⟩ : syracuseStep 1486181 = 278659) (by norm_num)
theorem B5942645 : Blo 730325 5942645 := bbase (se 5 (by rfl) ⟨278561, by rfl⟩ : syracuseStep 5942645 = 557123) (by norm_num)
theorem B929161 : Blo 730325 929161 := bbase (se 2 (by rfl) ⟨348435, by rfl⟩ : syracuseStep 929161 = 696871) (by norm_num)
theorem B1387925 : Blo 730325 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B1650077 : Blo 730325 1650077 := bbase (se 3 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 1650077 = 618779) (by norm_num)
theorem B1650149 : Blo 730325 1650149 := bbase (se 4 (by rfl) ⟨154701, by rfl⟩ : syracuseStep 1650149 = 309403) (by norm_num)
theorem B2469365 : Blo 730325 2469365 := bbase (se 5 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 2469365 = 231503) (by norm_num)
theorem B1650221 : Blo 730325 1650221 := bbase (se 3 (by rfl) ⟨309416, by rfl⟩ : syracuseStep 1650221 = 618833) (by norm_num)
theorem B929333 : Blo 730325 929333 := bbase (se 5 (by rfl) ⟨43562, by rfl⟩ : syracuseStep 929333 = 87125) (by norm_num)
theorem B1650293 : Blo 730325 1650293 := bbase (se 5 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 1650293 = 154715) (by norm_num)
theorem B1650365 : Blo 730325 1650365 := bbase (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) (by norm_num)
theorem B1650437 : Blo 730325 1650437 := bbase (se 4 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 1650437 = 309457) (by norm_num)
theorem B3714821 : Blo 730325 3714821 := bbase (se 4 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 3714821 = 696529) (by norm_num)
theorem B3518261 : Blo 730325 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B2862917 : Blo 730325 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1650509 : Blo 730325 1650509 := bbase (se 3 (by rfl) ⟨309470, by rfl⟩ : syracuseStep 1650509 = 618941) (by norm_num)
theorem B2502485 : Blo 730325 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B1650581 : Blo 730325 1650581 := bbase (se 6 (by rfl) ⟨38685, by rfl⟩ : syracuseStep 1650581 = 77371) (by norm_num)
theorem B2469797 : Blo 730325 2469797 := bbase (se 4 (by rfl) ⟨231543, by rfl⟩ : syracuseStep 2469797 = 463087) (by norm_num)
theorem B1486765 : Blo 730325 1486765 := bbase (se 3 (by rfl) ⟨278768, by rfl⟩ : syracuseStep 1486765 = 557537) (by norm_num)
theorem B1650653 : Blo 730325 1650653 := bbase (se 3 (by rfl) ⟨309497, by rfl⟩ : syracuseStep 1650653 = 618995) (by norm_num)
theorem B1978373 : Blo 730325 1978373 := bbase (se 4 (by rfl) ⟨185472, by rfl⟩ : syracuseStep 1978373 = 370945) (by norm_num)
theorem B1650725 : Blo 730325 1650725 := bbase (se 4 (by rfl) ⟨154755, by rfl⟩ : syracuseStep 1650725 = 309511) (by norm_num)
theorem B1781813 : Blo 730325 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B1650797 : Blo 730325 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B1388677 : Blo 730325 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B3125429 : Blo 730325 3125429 := bbase (se 5 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 3125429 = 293009) (by norm_num)
theorem B1650869 : Blo 730325 1650869 := bbase (se 5 (by rfl) ⟨77384, by rfl⟩ : syracuseStep 1650869 = 154769) (by norm_num)
theorem B1650941 : Blo 730325 1650941 := bbase (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) (by norm_num)
theorem B1388821 : Blo 730325 1388821 := bbase (se 6 (by rfl) ⟨32550, by rfl⟩ : syracuseStep 1388821 = 65101) (by norm_num)
theorem B1651013 : Blo 730325 1651013 := bbase (se 4 (by rfl) ⟨154782, by rfl⟩ : syracuseStep 1651013 = 309565) (by norm_num)
theorem B2470229 : Blo 730325 2470229 := bbase (se 10 (by rfl) ⟨3618, by rfl⟩ : syracuseStep 2470229 = 7237) (by norm_num)
theorem B14102869 : Blo 730325 14102869 := bbase (se 10 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 14102869 = 41317) (by norm_num)
theorem B1651085 : Blo 730325 1651085 := bbase (se 3 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 1651085 = 619157) (by norm_num)
theorem B1388981 : Blo 730325 1388981 := bbase (se 5 (by rfl) ⟨65108, by rfl⟩ : syracuseStep 1388981 = 130217) (by norm_num)
theorem B1651157 : Blo 730325 1651157 := bbase (se 7 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 1651157 = 38699) (by norm_num)
theorem B1651229 : Blo 730325 1651229 := bbase (se 3 (by rfl) ⟨309605, by rfl⟩ : syracuseStep 1651229 = 619211) (by norm_num)
theorem B1389125 : Blo 730325 1389125 := bbase (se 4 (by rfl) ⟨130230, by rfl⟩ : syracuseStep 1389125 = 260461) (by norm_num)
theorem B1651301 : Blo 730325 1651301 := bbase (se 4 (by rfl) ⟨154809, by rfl⟩ : syracuseStep 1651301 = 309619) (by norm_num)
theorem B2372261 : Blo 730325 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B1651373 : Blo 730325 1651373 := bbase (se 3 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 1651373 = 619265) (by norm_num)
theorem B1651445 : Blo 730325 1651445 := bbase (se 5 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 1651445 = 154823) (by norm_num)
theorem B2470661 : Blo 730325 2470661 := bbase (se 4 (by rfl) ⟨231624, by rfl⟩ : syracuseStep 2470661 = 463249) (by norm_num)
theorem B1651517 : Blo 730325 1651517 := bbase (se 3 (by rfl) ⟨309659, by rfl⟩ : syracuseStep 1651517 = 619319) (by norm_num)
theorem B2962277 : Blo 730325 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B1389413 : Blo 730325 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1651589 : Blo 730325 1651589 := bbase (se 4 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 1651589 = 309673) (by norm_num)
theorem B8893333 : Blo 730325 8893333 := bbase (se 6 (by rfl) ⟨208437, by rfl⟩ : syracuseStep 8893333 = 416875) (by norm_num)
theorem B1586117 : Blo 730325 1586117 := bbase (se 4 (by rfl) ⟨148698, by rfl⟩ : syracuseStep 1586117 = 297397) (by norm_num)
theorem B1651661 : Blo 730325 1651661 := bbase (se 3 (by rfl) ⟨309686, by rfl⟩ : syracuseStep 1651661 = 619373) (by norm_num)
theorem B12530645 : Blo 730325 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1389565 : Blo 730325 1389565 := bbase (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) (by norm_num)
theorem B3716117 : Blo 730325 3716117 := bbase (se 6 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 3716117 = 174193) (by norm_num)
theorem B1651733 : Blo 730325 1651733 := bbase (se 6 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 1651733 = 77425) (by norm_num)
theorem B1586213 : Blo 730325 1586213 := bbase (se 4 (by rfl) ⟨148707, by rfl⟩ : syracuseStep 1586213 = 297415) (by norm_num)
theorem B1651805 : Blo 730325 1651805 := bbase (se 3 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 1651805 = 619427) (by norm_num)
theorem B1651877 : Blo 730325 1651877 := bbase (se 4 (by rfl) ⟨154863, by rfl⟩ : syracuseStep 1651877 = 309727) (by norm_num)
theorem B2471093 : Blo 730325 2471093 := bbase (se 5 (by rfl) ⟨115832, by rfl⟩ : syracuseStep 2471093 = 231665) (by norm_num)
theorem B1881269 : Blo 730325 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B1651949 : Blo 730325 1651949 := bbase (se 3 (by rfl) ⟨309740, by rfl⟩ : syracuseStep 1651949 = 619481) (by norm_num)
theorem B1389869 : Blo 730325 1389869 := bbase (se 3 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 1389869 = 521201) (by norm_num)
theorem B1652021 : Blo 730325 1652021 := bbase (se 5 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 1652021 = 154877) (by norm_num)
theorem B1848653 : Blo 730325 1848653 := bbase (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) (by norm_num)
theorem B1652093 : Blo 730325 1652093 := bbase (se 3 (by rfl) ⟨309767, by rfl⟩ : syracuseStep 1652093 = 619535) (by norm_num)
theorem B1652165 : Blo 730325 1652165 := bbase (se 4 (by rfl) ⟨154890, by rfl⟩ : syracuseStep 1652165 = 309781) (by norm_num)
theorem B1848845 : Blo 730325 1848845 := bbase (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) (by norm_num)
theorem B2471525 : Blo 730325 2471525 := bbase (se 4 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 2471525 = 463411) (by norm_num)
theorem B2340485 : Blo 730325 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B1095509 : Blo 730325 1095509 := bbase (se 9 (by rfl) ⟨3209, by rfl⟩ : syracuseStep 1095509 = 6419) (by norm_num)
theorem B1849189 : Blo 730325 1849189 := bbase (se 4 (by rfl) ⟨173361, by rfl⟩ : syracuseStep 1849189 = 346723) (by norm_num)
theorem B1095533 : Blo 730325 1095533 := bbase (se 3 (by rfl) ⟨205412, by rfl⟩ : syracuseStep 1095533 = 410825) (by norm_num)
theorem B1095557 : Blo 730325 1095557 := bbase (se 4 (by rfl) ⟨102708, by rfl⟩ : syracuseStep 1095557 = 205417) (by norm_num)
theorem B2635669 : Blo 730325 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1095581 : Blo 730325 1095581 := bbase (se 3 (by rfl) ⟨205421, by rfl⟩ : syracuseStep 1095581 = 410843) (by norm_num)
theorem B1095605 : Blo 730325 1095605 := bbase (se 5 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 1095605 = 102713) (by norm_num)
theorem B1095629 : Blo 730325 1095629 := bbase (se 3 (by rfl) ⟨205430, by rfl⟩ : syracuseStep 1095629 = 410861) (by norm_num)
theorem B1849301 : Blo 730325 1849301 := bbase (se 7 (by rfl) ⟨21671, by rfl⟩ : syracuseStep 1849301 = 43343) (by norm_num)
theorem B1095653 : Blo 730325 1095653 := bbase (se 4 (by rfl) ⟨102717, by rfl⟩ : syracuseStep 1095653 = 205435) (by norm_num)
theorem B1095677 : Blo 730325 1095677 := bbase (se 3 (by rfl) ⟨205439, by rfl⟩ : syracuseStep 1095677 = 410879) (by norm_num)
theorem B1095701 : Blo 730325 1095701 := bbase (se 6 (by rfl) ⟨25680, by rfl⟩ : syracuseStep 1095701 = 51361) (by norm_num)
theorem B2471957 : Blo 730325 2471957 := bbase (se 6 (by rfl) ⟨57936, by rfl⟩ : syracuseStep 2471957 = 115873) (by norm_num)
theorem B1390621 : Blo 730325 1390621 := bbase (se 3 (by rfl) ⟨260741, by rfl⟩ : syracuseStep 1390621 = 521483) (by norm_num)
theorem B1095725 : Blo 730325 1095725 := bbase (se 3 (by rfl) ⟨205448, by rfl⟩ : syracuseStep 1095725 = 410897) (by norm_num)
theorem B1095749 : Blo 730325 1095749 := bbase (se 4 (by rfl) ⟨102726, by rfl⟩ : syracuseStep 1095749 = 205453) (by norm_num)
theorem B1095773 : Blo 730325 1095773 := bbase (se 3 (by rfl) ⟨205457, by rfl⟩ : syracuseStep 1095773 = 410915) (by norm_num)
theorem B1095797 : Blo 730325 1095797 := bbase (se 5 (by rfl) ⟨51365, by rfl⟩ : syracuseStep 1095797 = 102731) (by norm_num)
theorem B1095821 : Blo 730325 1095821 := bbase (se 3 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 1095821 = 410933) (by norm_num)
theorem B1849493 : Blo 730325 1849493 := bbase (se 6 (by rfl) ⟨43347, by rfl⟩ : syracuseStep 1849493 = 86695) (by norm_num)
theorem B1882261 : Blo 730325 1882261 := bbase (se 6 (by rfl) ⟨44115, by rfl⟩ : syracuseStep 1882261 = 88231) (by norm_num)
theorem B1095845 : Blo 730325 1095845 := bbase (se 4 (by rfl) ⟨102735, by rfl⟩ : syracuseStep 1095845 = 205471) (by norm_num)
theorem B1390765 : Blo 730325 1390765 := bbase (se 3 (by rfl) ⟨260768, by rfl⟩ : syracuseStep 1390765 = 521537) (by norm_num)
theorem B1095869 : Blo 730325 1095869 := bbase (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) (by norm_num)
theorem B2635973 : Blo 730325 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1095893 : Blo 730325 1095893 := bbase (se 7 (by rfl) ⟨12842, by rfl⟩ : syracuseStep 1095893 = 25685) (by norm_num)
theorem B1095917 : Blo 730325 1095917 := bbase (se 3 (by rfl) ⟨205484, by rfl⟩ : syracuseStep 1095917 = 410969) (by norm_num)
theorem B1095941 : Blo 730325 1095941 := bbase (se 4 (by rfl) ⟨102744, by rfl⟩ : syracuseStep 1095941 = 205489) (by norm_num)
theorem B1095965 : Blo 730325 1095965 := bbase (se 3 (by rfl) ⟨205493, by rfl⟩ : syracuseStep 1095965 = 410987) (by norm_num)
theorem B3717413 : Blo 730325 3717413 := bbase (se 4 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 3717413 = 697015) (by norm_num)
theorem B1095989 : Blo 730325 1095989 := bbase (se 5 (by rfl) ⟨51374, by rfl⟩ : syracuseStep 1095989 = 102749) (by norm_num)
theorem B1096013 : Blo 730325 1096013 := bbase (se 3 (by rfl) ⟨205502, by rfl⟩ : syracuseStep 1096013 = 411005) (by norm_num)
theorem B1390925 : Blo 730325 1390925 := bbase (se 3 (by rfl) ⟨260798, by rfl⟩ : syracuseStep 1390925 = 521597) (by norm_num)
theorem B1096037 : Blo 730325 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B1096061 : Blo 730325 1096061 := bbase (se 3 (by rfl) ⟨205511, by rfl⟩ : syracuseStep 1096061 = 411023) (by norm_num)
theorem B833933 : Blo 730325 833933 := bbase (se 3 (by rfl) ⟨156362, by rfl⟩ : syracuseStep 833933 = 312725) (by norm_num)
theorem B1096085 : Blo 730325 1096085 := bbase (se 6 (by rfl) ⟨25689, by rfl⟩ : syracuseStep 1096085 = 51379) (by norm_num)
theorem B1096109 : Blo 730325 1096109 := bbase (se 3 (by rfl) ⟨205520, by rfl⟩ : syracuseStep 1096109 = 411041) (by norm_num)
theorem B1096133 : Blo 730325 1096133 := bbase (se 4 (by rfl) ⟨102762, by rfl⟩ : syracuseStep 1096133 = 205525) (by norm_num)
theorem B833989 : Blo 730325 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B2472389 : Blo 730325 2472389 := bbase (se 4 (by rfl) ⟨231786, by rfl⟩ : syracuseStep 2472389 = 463573) (by norm_num)
theorem B1096157 : Blo 730325 1096157 := bbase (se 3 (by rfl) ⟨205529, by rfl⟩ : syracuseStep 1096157 = 411059) (by norm_num)
theorem B1391069 : Blo 730325 1391069 := bbase (se 3 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 1391069 = 521651) (by norm_num)
theorem B1849837 : Blo 730325 1849837 := bbase (se 3 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 1849837 = 693689) (by norm_num)
theorem B1096181 : Blo 730325 1096181 := bbase (se 5 (by rfl) ⟨51383, by rfl⟩ : syracuseStep 1096181 = 102767) (by norm_num)
theorem B2341381 : Blo 730325 2341381 := bbase (se 4 (by rfl) ⟨219504, by rfl⟩ : syracuseStep 2341381 = 439009) (by norm_num)
theorem B3521029 : Blo 730325 3521029 := bbase (se 4 (by rfl) ⟨330096, by rfl⟩ : syracuseStep 3521029 = 660193) (by norm_num)
theorem B1096205 : Blo 730325 1096205 := bbase (se 3 (by rfl) ⟨205538, by rfl⟩ : syracuseStep 1096205 = 411077) (by norm_num)
theorem B1096229 : Blo 730325 1096229 := bbase (se 4 (by rfl) ⟨102771, by rfl⟩ : syracuseStep 1096229 = 205543) (by norm_num)
theorem B1096253 : Blo 730325 1096253 := bbase (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) (by norm_num)
theorem B1096277 : Blo 730325 1096277 := bbase (se 8 (by rfl) ⟨6423, by rfl⟩ : syracuseStep 1096277 = 12847) (by norm_num)
theorem B1849949 : Blo 730325 1849949 := bbase (se 3 (by rfl) ⟨346865, by rfl⟩ : syracuseStep 1849949 = 693731) (by norm_num)
theorem B1096301 : Blo 730325 1096301 := bbase (se 3 (by rfl) ⟨205556, by rfl⟩ : syracuseStep 1096301 = 411113) (by norm_num)
theorem B1096325 : Blo 730325 1096325 := bbase (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) (by norm_num)
theorem B1096349 : Blo 730325 1096349 := bbase (se 3 (by rfl) ⟨205565, by rfl⟩ : syracuseStep 1096349 = 411131) (by norm_num)
theorem B834221 : Blo 730325 834221 := bbase (se 3 (by rfl) ⟨156416, by rfl⟩ : syracuseStep 834221 = 312833) (by norm_num)
theorem B1096373 : Blo 730325 1096373 := bbase (se 5 (by rfl) ⟨51392, by rfl⟩ : syracuseStep 1096373 = 102785) (by norm_num)
theorem B1096397 : Blo 730325 1096397 := bbase (se 3 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 1096397 = 411149) (by norm_num)
theorem B1096421 : Blo 730325 1096421 := bbase (se 4 (by rfl) ⟨102789, by rfl⟩ : syracuseStep 1096421 = 205579) (by norm_num)
theorem B1096445 : Blo 730325 1096445 := bbase (se 3 (by rfl) ⟨205583, by rfl⟩ : syracuseStep 1096445 = 411167) (by norm_num)
theorem B1391357 : Blo 730325 1391357 := bbase (se 3 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 1391357 = 521759) (by norm_num)
theorem B1096469 : Blo 730325 1096469 := bbase (se 6 (by rfl) ⟨25698, by rfl⟩ : syracuseStep 1096469 = 51397) (by norm_num)
theorem B1850141 : Blo 730325 1850141 := bbase (se 3 (by rfl) ⟨346901, by rfl⟩ : syracuseStep 1850141 = 693803) (by norm_num)
theorem B1096493 : Blo 730325 1096493 := bbase (se 3 (by rfl) ⟨205592, by rfl⟩ : syracuseStep 1096493 = 411185) (by norm_num)
theorem B1096517 : Blo 730325 1096517 := bbase (se 4 (by rfl) ⟨102798, by rfl⟩ : syracuseStep 1096517 = 205597) (by norm_num)
theorem B1096541 : Blo 730325 1096541 := bbase (se 3 (by rfl) ⟨205601, by rfl⟩ : syracuseStep 1096541 = 411203) (by norm_num)
theorem B1096565 : Blo 730325 1096565 := bbase (se 5 (by rfl) ⟨51401, by rfl⟩ : syracuseStep 1096565 = 102803) (by norm_num)
theorem B2472821 : Blo 730325 2472821 := bbase (se 5 (by rfl) ⟨115913, by rfl⟩ : syracuseStep 2472821 = 231827) (by norm_num)
theorem B1096589 : Blo 730325 1096589 := bbase (se 3 (by rfl) ⟨205610, by rfl⟩ : syracuseStep 1096589 = 411221) (by norm_num)
theorem B1391509 : Blo 730325 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B1096613 : Blo 730325 1096613 := bbase (se 4 (by rfl) ⟨102807, by rfl⟩ : syracuseStep 1096613 = 205615) (by norm_num)
theorem B1096637 : Blo 730325 1096637 := bbase (se 3 (by rfl) ⟨205619, by rfl⟩ : syracuseStep 1096637 = 411239) (by norm_num)
theorem B1096661 : Blo 730325 1096661 := bbase (se 7 (by rfl) ⟨12851, by rfl⟩ : syracuseStep 1096661 = 25703) (by norm_num)
theorem B1096685 : Blo 730325 1096685 := bbase (se 3 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 1096685 = 411257) (by norm_num)
theorem B1096709 : Blo 730325 1096709 := bbase (se 4 (by rfl) ⟨102816, by rfl⟩ : syracuseStep 1096709 = 205633) (by norm_num)
theorem B1096733 : Blo 730325 1096733 := bbase (se 3 (by rfl) ⟨205637, by rfl⟩ : syracuseStep 1096733 = 411275) (by norm_num)
theorem B1096757 : Blo 730325 1096757 := bbase (se 5 (by rfl) ⟨51410, by rfl⟩ : syracuseStep 1096757 = 102821) (by norm_num)
theorem B1096781 : Blo 730325 1096781 := bbase (se 3 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 1096781 = 411293) (by norm_num)
theorem B1096805 : Blo 730325 1096805 := bbase (se 4 (by rfl) ⟨102825, by rfl⟩ : syracuseStep 1096805 = 205651) (by norm_num)
theorem B1850485 : Blo 730325 1850485 := bbase (se 5 (by rfl) ⟨86741, by rfl⟩ : syracuseStep 1850485 = 173483) (by norm_num)
theorem B1096829 : Blo 730325 1096829 := bbase (se 3 (by rfl) ⟨205655, by rfl⟩ : syracuseStep 1096829 = 411311) (by norm_num)
theorem B1096853 : Blo 730325 1096853 := bbase (se 6 (by rfl) ⟨25707, by rfl⟩ : syracuseStep 1096853 = 51415) (by norm_num)
theorem B1096877 : Blo 730325 1096877 := bbase (se 3 (by rfl) ⟨205664, by rfl⟩ : syracuseStep 1096877 = 411329) (by norm_num)
theorem B1096901 : Blo 730325 1096901 := bbase (se 4 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 1096901 = 205669) (by norm_num)
theorem B1391813 : Blo 730325 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B1096925 : Blo 730325 1096925 := bbase (se 3 (by rfl) ⟨205673, by rfl⟩ : syracuseStep 1096925 = 411347) (by norm_num)
theorem B1850597 : Blo 730325 1850597 := bbase (se 4 (by rfl) ⟨173493, by rfl⟩ : syracuseStep 1850597 = 346987) (by norm_num)
theorem B1096949 : Blo 730325 1096949 := bbase (se 5 (by rfl) ⟨51419, by rfl⟩ : syracuseStep 1096949 = 102839) (by norm_num)
theorem B1096973 : Blo 730325 1096973 := bbase (se 3 (by rfl) ⟨205682, by rfl⟩ : syracuseStep 1096973 = 411365) (by norm_num)
theorem B1096997 : Blo 730325 1096997 := bbase (se 4 (by rfl) ⟨102843, by rfl⟩ : syracuseStep 1096997 = 205687) (by norm_num)
theorem B2473253 : Blo 730325 2473253 := bbase (se 4 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 2473253 = 463735) (by norm_num)
theorem B1097021 : Blo 730325 1097021 := bbase (se 3 (by rfl) ⟨205691, by rfl⟩ : syracuseStep 1097021 = 411383) (by norm_num)
theorem B1097045 : Blo 730325 1097045 := bbase (se 11 (by rfl) ⟨803, by rfl⟩ : syracuseStep 1097045 = 1607) (by norm_num)
theorem B1097069 : Blo 730325 1097069 := bbase (se 3 (by rfl) ⟨205700, by rfl⟩ : syracuseStep 1097069 = 411401) (by norm_num)
theorem B2964869 : Blo 730325 2964869 := bbase (se 4 (by rfl) ⟨277956, by rfl⟩ : syracuseStep 2964869 = 555913) (by norm_num)
theorem B1097093 : Blo 730325 1097093 := bbase (se 4 (by rfl) ⟨102852, by rfl⟩ : syracuseStep 1097093 = 205705) (by norm_num)
theorem B1097117 : Blo 730325 1097117 := bbase (se 3 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 1097117 = 411419) (by norm_num)
theorem B1850789 : Blo 730325 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B1097141 : Blo 730325 1097141 := bbase (se 5 (by rfl) ⟨51428, by rfl⟩ : syracuseStep 1097141 = 102857) (by norm_num)
theorem B1097165 : Blo 730325 1097165 := bbase (se 3 (by rfl) ⟨205718, by rfl⟩ : syracuseStep 1097165 = 411437) (by norm_num)
theorem B1097189 : Blo 730325 1097189 := bbase (se 4 (by rfl) ⟨102861, by rfl⟩ : syracuseStep 1097189 = 205723) (by norm_num)
theorem B1097213 : Blo 730325 1097213 := bbase (se 3 (by rfl) ⟨205727, by rfl⟩ : syracuseStep 1097213 = 411455) (by norm_num)
theorem B1097237 : Blo 730325 1097237 := bbase (se 6 (by rfl) ⟨25716, by rfl⟩ : syracuseStep 1097237 = 51433) (by norm_num)
theorem B1097261 : Blo 730325 1097261 := bbase (se 3 (by rfl) ⟨205736, by rfl⟩ : syracuseStep 1097261 = 411473) (by norm_num)
theorem B1097285 : Blo 730325 1097285 := bbase (se 4 (by rfl) ⟨102870, by rfl⟩ : syracuseStep 1097285 = 205741) (by norm_num)
theorem B835157 : Blo 730325 835157 := bbase (se 8 (by rfl) ⟨4893, by rfl⟩ : syracuseStep 835157 = 9787) (by norm_num)
theorem B1097309 : Blo 730325 1097309 := bbase (se 3 (by rfl) ⟨205745, by rfl⟩ : syracuseStep 1097309 = 411491) (by norm_num)
theorem B1097333 : Blo 730325 1097333 := bbase (se 5 (by rfl) ⟨51437, by rfl⟩ : syracuseStep 1097333 = 102875) (by norm_num)
theorem B1097357 : Blo 730325 1097357 := bbase (se 3 (by rfl) ⟨205754, by rfl⟩ : syracuseStep 1097357 = 411509) (by norm_num)
theorem B1097381 : Blo 730325 1097381 := bbase (se 4 (by rfl) ⟨102879, by rfl⟩ : syracuseStep 1097381 = 205759) (by norm_num)
theorem B3391141 : Blo 730325 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B1097405 : Blo 730325 1097405 := bbase (se 3 (by rfl) ⟨205763, by rfl⟩ : syracuseStep 1097405 = 411527) (by norm_num)
theorem B1097429 : Blo 730325 1097429 := bbase (se 7 (by rfl) ⟨12860, by rfl⟩ : syracuseStep 1097429 = 25721) (by norm_num)
theorem B2473685 : Blo 730325 2473685 := bbase (se 7 (by rfl) ⟨28988, by rfl⟩ : syracuseStep 2473685 = 57977) (by norm_num)
theorem B1097453 : Blo 730325 1097453 := bbase (se 3 (by rfl) ⟨205772, by rfl⟩ : syracuseStep 1097453 = 411545) (by norm_num)
theorem B1851133 : Blo 730325 1851133 := bbase (se 3 (by rfl) ⟨347087, by rfl⟩ : syracuseStep 1851133 = 694175) (by norm_num)
theorem B1097477 : Blo 730325 1097477 := bbase (se 4 (by rfl) ⟨102888, by rfl⟩ : syracuseStep 1097477 = 205777) (by norm_num)
theorem B1097501 : Blo 730325 1097501 := bbase (se 3 (by rfl) ⟨205781, by rfl⟩ : syracuseStep 1097501 = 411563) (by norm_num)
theorem B1097525 : Blo 730325 1097525 := bbase (se 5 (by rfl) ⟨51446, by rfl⟩ : syracuseStep 1097525 = 102893) (by norm_num)
theorem B1097549 : Blo 730325 1097549 := bbase (se 3 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 1097549 = 411581) (by norm_num)
theorem B1097573 : Blo 730325 1097573 := bbase (se 4 (by rfl) ⟨102897, by rfl⟩ : syracuseStep 1097573 = 205795) (by norm_num)
theorem B1851245 : Blo 730325 1851245 := bbase (se 3 (by rfl) ⟨347108, by rfl⟩ : syracuseStep 1851245 = 694217) (by norm_num)
theorem B1097597 : Blo 730325 1097597 := bbase (se 3 (by rfl) ⟨205799, by rfl⟩ : syracuseStep 1097597 = 411599) (by norm_num)
theorem B1097621 : Blo 730325 1097621 := bbase (se 6 (by rfl) ⟨25725, by rfl⟩ : syracuseStep 1097621 = 51451) (by norm_num)
theorem B1097645 : Blo 730325 1097645 := bbase (se 3 (by rfl) ⟨205808, by rfl⟩ : syracuseStep 1097645 = 411617) (by norm_num)
theorem B1392565 : Blo 730325 1392565 := bbase (se 5 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 1392565 = 130553) (by norm_num)
theorem B1097669 : Blo 730325 1097669 := bbase (se 4 (by rfl) ⟨102906, by rfl⟩ : syracuseStep 1097669 = 205813) (by norm_num)
theorem B1097693 : Blo 730325 1097693 := bbase (se 3 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 1097693 = 411635) (by norm_num)
theorem B1097717 : Blo 730325 1097717 := bbase (se 5 (by rfl) ⟨51455, by rfl⟩ : syracuseStep 1097717 = 102911) (by norm_num)
theorem B1097741 : Blo 730325 1097741 := bbase (se 3 (by rfl) ⟨205826, by rfl⟩ : syracuseStep 1097741 = 411653) (by norm_num)
theorem B1097765 : Blo 730325 1097765 := bbase (se 4 (by rfl) ⟨102915, by rfl⟩ : syracuseStep 1097765 = 205831) (by norm_num)
theorem B1851437 : Blo 730325 1851437 := bbase (se 3 (by rfl) ⟨347144, by rfl⟩ : syracuseStep 1851437 = 694289) (by norm_num)
theorem B5947445 : Blo 730325 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B1097789 : Blo 730325 1097789 := bbase (se 3 (by rfl) ⟨205835, by rfl⟩ : syracuseStep 1097789 = 411671) (by norm_num)
theorem B1392709 : Blo 730325 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B1097813 : Blo 730325 1097813 := bbase (se 8 (by rfl) ⟨6432, by rfl⟩ : syracuseStep 1097813 = 12865) (by norm_num)
theorem B1097837 : Blo 730325 1097837 := bbase (se 3 (by rfl) ⟨205844, by rfl⟩ : syracuseStep 1097837 = 411689) (by norm_num)
theorem B2080885 : Blo 730325 2080885 := bbase (se 5 (by rfl) ⟨97541, by rfl⟩ : syracuseStep 2080885 = 195083) (by norm_num)
theorem B3129461 : Blo 730325 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B1097861 : Blo 730325 1097861 := bbase (se 4 (by rfl) ⟨102924, by rfl⟩ : syracuseStep 1097861 = 205849) (by norm_num)
theorem B2474117 : Blo 730325 2474117 := bbase (se 4 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 2474117 = 463897) (by norm_num)
theorem B1097885 : Blo 730325 1097885 := bbase (se 3 (by rfl) ⟨205853, by rfl⟩ : syracuseStep 1097885 = 411707) (by norm_num)
theorem B1097909 : Blo 730325 1097909 := bbase (se 5 (by rfl) ⟨51464, by rfl⟩ : syracuseStep 1097909 = 102929) (by norm_num)
theorem B1097933 : Blo 730325 1097933 := bbase (se 3 (by rfl) ⟨205862, by rfl⟩ : syracuseStep 1097933 = 411725) (by norm_num)
theorem B1097957 : Blo 730325 1097957 := bbase (se 4 (by rfl) ⟨102933, by rfl⟩ : syracuseStep 1097957 = 205867) (by norm_num)
theorem B1392869 : Blo 730325 1392869 := bbase (se 4 (by rfl) ⟨130581, by rfl⟩ : syracuseStep 1392869 = 261163) (by norm_num)
theorem B1097981 : Blo 730325 1097981 := bbase (se 3 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 1097981 = 411743) (by norm_num)
theorem B2081045 : Blo 730325 2081045 := bbase (se 6 (by rfl) ⟨48774, by rfl⟩ : syracuseStep 2081045 = 97549) (by norm_num)
theorem B1098005 : Blo 730325 1098005 := bbase (se 6 (by rfl) ⟨25734, by rfl⟩ : syracuseStep 1098005 = 51469) (by norm_num)
theorem B1098029 : Blo 730325 1098029 := bbase (se 3 (by rfl) ⟨205880, by rfl⟩ : syracuseStep 1098029 = 411761) (by norm_num)
theorem B1098053 : Blo 730325 1098053 := bbase (se 4 (by rfl) ⟨102942, by rfl⟩ : syracuseStep 1098053 = 205885) (by norm_num)
theorem B1098077 : Blo 730325 1098077 := bbase (se 3 (by rfl) ⟨205889, by rfl⟩ : syracuseStep 1098077 = 411779) (by norm_num)
theorem B1098101 : Blo 730325 1098101 := bbase (se 5 (by rfl) ⟨51473, by rfl⟩ : syracuseStep 1098101 = 102947) (by norm_num)
theorem B1393013 : Blo 730325 1393013 := bbase (se 5 (by rfl) ⟨65297, by rfl⟩ : syracuseStep 1393013 = 130595) (by norm_num)
theorem B1851781 : Blo 730325 1851781 := bbase (se 4 (by rfl) ⟨173604, by rfl⟩ : syracuseStep 1851781 = 347209) (by norm_num)
theorem B1098125 : Blo 730325 1098125 := bbase (se 3 (by rfl) ⟨205898, by rfl⟩ : syracuseStep 1098125 = 411797) (by norm_num)
theorem B1098149 : Blo 730325 1098149 := bbase (se 4 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 1098149 = 205903) (by norm_num)
theorem B1130917 : Blo 730325 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B1098173 : Blo 730325 1098173 := bbase (se 3 (by rfl) ⟨205907, by rfl⟩ : syracuseStep 1098173 = 411815) (by norm_num)
theorem B1098197 : Blo 730325 1098197 := bbase (se 7 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 1098197 = 25739) (by norm_num)
theorem B1098221 : Blo 730325 1098221 := bbase (se 3 (by rfl) ⟨205916, by rfl⟩ : syracuseStep 1098221 = 411833) (by norm_num)
theorem B1851893 : Blo 730325 1851893 := bbase (se 5 (by rfl) ⟨86807, by rfl⟩ : syracuseStep 1851893 = 173615) (by norm_num)
theorem B2081285 : Blo 730325 2081285 := bbase (se 4 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 2081285 = 390241) (by norm_num)
theorem B1098245 : Blo 730325 1098245 := bbase (se 4 (by rfl) ⟨102960, by rfl⟩ : syracuseStep 1098245 = 205921) (by norm_num)
theorem B1098269 : Blo 730325 1098269 := bbase (se 3 (by rfl) ⟨205925, by rfl⟩ : syracuseStep 1098269 = 411851) (by norm_num)
theorem B1098293 : Blo 730325 1098293 := bbase (se 5 (by rfl) ⟨51482, by rfl⟩ : syracuseStep 1098293 = 102965) (by norm_num)
theorem B2474549 : Blo 730325 2474549 := bbase (se 5 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 2474549 = 231989) (by norm_num)
theorem B2114117 : Blo 730325 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B1098317 : Blo 730325 1098317 := bbase (se 3 (by rfl) ⟨205934, by rfl⟩ : syracuseStep 1098317 = 411869) (by norm_num)
theorem B1786445 : Blo 730325 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B1098341 : Blo 730325 1098341 := bbase (se 4 (by rfl) ⟨102969, by rfl⟩ : syracuseStep 1098341 = 205939) (by norm_num)
theorem B1098365 : Blo 730325 1098365 := bbase (se 3 (by rfl) ⟨205943, by rfl⟩ : syracuseStep 1098365 = 411887) (by norm_num)
theorem B1098389 : Blo 730325 1098389 := bbase (se 6 (by rfl) ⟨25743, by rfl⟩ : syracuseStep 1098389 = 51487) (by norm_num)
theorem B1393301 : Blo 730325 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B1098413 : Blo 730325 1098413 := bbase (se 3 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 1098413 = 411905) (by norm_num)
theorem B1852085 : Blo 730325 1852085 := bbase (se 5 (by rfl) ⟨86816, by rfl⟩ : syracuseStep 1852085 = 173633) (by norm_num)
theorem B2081477 : Blo 730325 2081477 := bbase (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) (by norm_num)
theorem B1098437 : Blo 730325 1098437 := bbase (se 4 (by rfl) ⟨102978, by rfl⟩ : syracuseStep 1098437 = 205957) (by norm_num)
theorem B1098461 : Blo 730325 1098461 := bbase (se 3 (by rfl) ⟨205961, by rfl⟩ : syracuseStep 1098461 = 411923) (by norm_num)
theorem B1098485 : Blo 730325 1098485 := bbase (se 5 (by rfl) ⟨51491, by rfl⟩ : syracuseStep 1098485 = 102983) (by norm_num)
theorem B1098509 : Blo 730325 1098509 := bbase (se 3 (by rfl) ⟨205970, by rfl⟩ : syracuseStep 1098509 = 411941) (by norm_num)
theorem B1098533 : Blo 730325 1098533 := bbase (se 4 (by rfl) ⟨102987, by rfl⟩ : syracuseStep 1098533 = 205975) (by norm_num)
theorem B1393453 : Blo 730325 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B1098557 : Blo 730325 1098557 := bbase (se 3 (by rfl) ⟨205979, by rfl⟩ : syracuseStep 1098557 = 411959) (by norm_num)
theorem B1098581 : Blo 730325 1098581 := bbase (se 9 (by rfl) ⟨3218, by rfl⟩ : syracuseStep 1098581 = 6437) (by norm_num)
theorem B1098605 : Blo 730325 1098605 := bbase (se 3 (by rfl) ⟨205988, by rfl⟩ : syracuseStep 1098605 = 411977) (by norm_num)
theorem B1098629 : Blo 730325 1098629 := bbase (se 4 (by rfl) ⟨102996, by rfl⟩ : syracuseStep 1098629 = 205993) (by norm_num)
theorem B1098653 : Blo 730325 1098653 := bbase (se 3 (by rfl) ⟨205997, by rfl⟩ : syracuseStep 1098653 = 411995) (by norm_num)
theorem B1098677 : Blo 730325 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B1098701 : Blo 730325 1098701 := bbase (se 3 (by rfl) ⟨206006, by rfl⟩ : syracuseStep 1098701 = 412013) (by norm_num)
theorem B1098725 : Blo 730325 1098725 := bbase (se 4 (by rfl) ⟨103005, by rfl⟩ : syracuseStep 1098725 = 206011) (by norm_num)
theorem B2474981 : Blo 730325 2474981 := bbase (se 4 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 2474981 = 464059) (by norm_num)
theorem B1098749 : Blo 730325 1098749 := bbase (se 3 (by rfl) ⟨206015, by rfl⟩ : syracuseStep 1098749 = 412031) (by norm_num)
theorem B1852429 : Blo 730325 1852429 := bbase (se 3 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 1852429 = 694661) (by norm_num)
theorem B1098773 : Blo 730325 1098773 := bbase (se 6 (by rfl) ⟨25752, by rfl⟩ : syracuseStep 1098773 = 51505) (by norm_num)
theorem B1098797 : Blo 730325 1098797 := bbase (se 3 (by rfl) ⟨206024, by rfl⟩ : syracuseStep 1098797 = 412049) (by norm_num)
theorem B1098821 : Blo 730325 1098821 := bbase (se 4 (by rfl) ⟨103014, by rfl⟩ : syracuseStep 1098821 = 206029) (by norm_num)
theorem B9520213 : Blo 730325 9520213 := bbase (se 8 (by rfl) ⟨55782, by rfl⟩ : syracuseStep 9520213 = 111565) (by norm_num)
theorem B1098845 : Blo 730325 1098845 := bbase (se 3 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 1098845 = 412067) (by norm_num)
theorem B1393757 : Blo 730325 1393757 := bbase (se 3 (by rfl) ⟨261329, by rfl⟩ : syracuseStep 1393757 = 522659) (by norm_num)
theorem B1000549 : Blo 730325 1000549 := bbase (se 4 (by rfl) ⟨93801, by rfl⟩ : syracuseStep 1000549 = 187603) (by norm_num)
theorem B1098869 : Blo 730325 1098869 := bbase (se 5 (by rfl) ⟨51509, by rfl⟩ : syracuseStep 1098869 = 103019) (by norm_num)
theorem B1852541 : Blo 730325 1852541 := bbase (se 3 (by rfl) ⟨347351, by rfl⟩ : syracuseStep 1852541 = 694703) (by norm_num)
theorem B1098893 : Blo 730325 1098893 := bbase (se 3 (by rfl) ⟨206042, by rfl⟩ : syracuseStep 1098893 = 412085) (by norm_num)
theorem B1787029 : Blo 730325 1787029 := bbase (se 6 (by rfl) ⟨41883, by rfl⟩ : syracuseStep 1787029 = 83767) (by norm_num)
theorem B1098917 : Blo 730325 1098917 := bbase (se 4 (by rfl) ⟨103023, by rfl⟩ : syracuseStep 1098917 = 206047) (by norm_num)
theorem B1098941 : Blo 730325 1098941 := bbase (se 3 (by rfl) ⟨206051, by rfl⟩ : syracuseStep 1098941 = 412103) (by norm_num)
theorem B1098965 : Blo 730325 1098965 := bbase (se 7 (by rfl) ⟨12878, by rfl⟩ : syracuseStep 1098965 = 25757) (by norm_num)
theorem B1000669 : Blo 730325 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B1098989 : Blo 730325 1098989 := bbase (se 3 (by rfl) ⟨206060, by rfl⟩ : syracuseStep 1098989 = 412121) (by norm_num)
theorem B1099013 : Blo 730325 1099013 := bbase (se 4 (by rfl) ⟨103032, by rfl⟩ : syracuseStep 1099013 = 206065) (by norm_num)
theorem B4179221 : Blo 730325 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B1099037 : Blo 730325 1099037 := bbase (se 3 (by rfl) ⟨206069, by rfl⟩ : syracuseStep 1099037 = 412139) (by norm_num)
theorem B1099061 : Blo 730325 1099061 := bbase (se 5 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 1099061 = 103037) (by norm_num)
theorem B1852733 : Blo 730325 1852733 := bbase (se 3 (by rfl) ⟨347387, by rfl⟩ : syracuseStep 1852733 = 694775) (by norm_num)
theorem B1099085 : Blo 730325 1099085 := bbase (se 3 (by rfl) ⟨206078, by rfl⟩ : syracuseStep 1099085 = 412157) (by norm_num)
theorem B2344277 : Blo 730325 2344277 := bbase (se 12 (by rfl) ⟨858, by rfl⟩ : syracuseStep 2344277 = 1717) (by norm_num)
theorem B1099109 : Blo 730325 1099109 := bbase (se 4 (by rfl) ⟨103041, by rfl⟩ : syracuseStep 1099109 = 206083) (by norm_num)
theorem B1983845 : Blo 730325 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B1099133 : Blo 730325 1099133 := bbase (se 3 (by rfl) ⟨206087, by rfl⟩ : syracuseStep 1099133 = 412175) (by norm_num)
theorem B1099157 : Blo 730325 1099157 := bbase (se 6 (by rfl) ⟨25761, by rfl⟩ : syracuseStep 1099157 = 51523) (by norm_num)
theorem B2475413 : Blo 730325 2475413 := bbase (se 6 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 2475413 = 116035) (by norm_num)
theorem B1099181 : Blo 730325 1099181 := bbase (se 3 (by rfl) ⟨206096, by rfl⟩ : syracuseStep 1099181 = 412193) (by norm_num)
theorem B1099205 : Blo 730325 1099205 := bbase (se 4 (by rfl) ⟨103050, by rfl⟩ : syracuseStep 1099205 = 206101) (by norm_num)
theorem B2639317 : Blo 730325 2639317 := bbase (se 7 (by rfl) ⟨30929, by rfl⟩ : syracuseStep 2639317 = 61859) (by norm_num)
theorem B1099229 : Blo 730325 1099229 := bbase (se 3 (by rfl) ⟨206105, by rfl⟩ : syracuseStep 1099229 = 412211) (by norm_num)
theorem B1099253 : Blo 730325 1099253 := bbase (se 5 (by rfl) ⟨51527, by rfl⟩ : syracuseStep 1099253 = 103055) (by norm_num)
theorem B1099277 : Blo 730325 1099277 := bbase (se 3 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 1099277 = 412229) (by norm_num)
theorem B1099301 : Blo 730325 1099301 := bbase (se 4 (by rfl) ⟨103059, by rfl⟩ : syracuseStep 1099301 = 206119) (by norm_num)
theorem B1099325 : Blo 730325 1099325 := bbase (se 3 (by rfl) ⟨206123, by rfl⟩ : syracuseStep 1099325 = 412247) (by norm_num)
theorem B1099349 : Blo 730325 1099349 := bbase (se 8 (by rfl) ⟨6441, by rfl⟩ : syracuseStep 1099349 = 12883) (by norm_num)
theorem B1099373 : Blo 730325 1099373 := bbase (se 3 (by rfl) ⟨206132, by rfl⟩ : syracuseStep 1099373 = 412265) (by norm_num)
theorem B1099397 : Blo 730325 1099397 := bbase (se 4 (by rfl) ⟨103068, by rfl⟩ : syracuseStep 1099397 = 206137) (by norm_num)
theorem B1853077 : Blo 730325 1853077 := bbase (se 6 (by rfl) ⟨43431, by rfl⟩ : syracuseStep 1853077 = 86863) (by norm_num)
theorem B1099421 : Blo 730325 1099421 := bbase (se 3 (by rfl) ⟨206141, by rfl⟩ : syracuseStep 1099421 = 412283) (by norm_num)
theorem B2082469 : Blo 730325 2082469 := bbase (se 4 (by rfl) ⟨195231, by rfl⟩ : syracuseStep 2082469 = 390463) (by norm_num)
theorem B2967205 : Blo 730325 2967205 := bbase (se 4 (by rfl) ⟨278175, by rfl⟩ : syracuseStep 2967205 = 556351) (by norm_num)
theorem B1099445 : Blo 730325 1099445 := bbase (se 5 (by rfl) ⟨51536, by rfl⟩ : syracuseStep 1099445 = 103073) (by norm_num)
theorem B1427149 : Blo 730325 1427149 := bbase (se 3 (by rfl) ⟨267590, by rfl⟩ : syracuseStep 1427149 = 535181) (by norm_num)
theorem B1099469 : Blo 730325 1099469 := bbase (se 3 (by rfl) ⟨206150, by rfl⟩ : syracuseStep 1099469 = 412301) (by norm_num)
theorem B1099493 : Blo 730325 1099493 := bbase (se 4 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 1099493 = 206155) (by norm_num)
theorem B1099517 : Blo 730325 1099517 := bbase (se 3 (by rfl) ⟨206159, by rfl⟩ : syracuseStep 1099517 = 412319) (by norm_num)
theorem B1853189 : Blo 730325 1853189 := bbase (se 4 (by rfl) ⟨173736, by rfl⟩ : syracuseStep 1853189 = 347473) (by norm_num)
theorem B1099541 : Blo 730325 1099541 := bbase (se 6 (by rfl) ⟨25770, by rfl⟩ : syracuseStep 1099541 = 51541) (by norm_num)
theorem B1099565 : Blo 730325 1099565 := bbase (se 3 (by rfl) ⟨206168, by rfl⟩ : syracuseStep 1099565 = 412337) (by norm_num)
theorem B1099589 : Blo 730325 1099589 := bbase (se 4 (by rfl) ⟨103086, by rfl⟩ : syracuseStep 1099589 = 206173) (by norm_num)
theorem B2475845 : Blo 730325 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B1099613 : Blo 730325 1099613 := bbase (se 3 (by rfl) ⟨206177, by rfl⟩ : syracuseStep 1099613 = 412355) (by norm_num)
theorem B3131237 : Blo 730325 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B1099637 : Blo 730325 1099637 := bbase (se 5 (by rfl) ⟨51545, by rfl⟩ : syracuseStep 1099637 = 103091) (by norm_num)
theorem B1099661 : Blo 730325 1099661 := bbase (se 3 (by rfl) ⟨206186, by rfl⟩ : syracuseStep 1099661 = 412373) (by norm_num)
theorem B1755037 : Blo 730325 1755037 := bbase (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) (by norm_num)
theorem B1099685 : Blo 730325 1099685 := bbase (se 4 (by rfl) ⟨103095, by rfl⟩ : syracuseStep 1099685 = 206191) (by norm_num)
theorem B1099709 : Blo 730325 1099709 := bbase (se 3 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 1099709 = 412391) (by norm_num)
theorem B1853381 : Blo 730325 1853381 := bbase (se 4 (by rfl) ⟨173754, by rfl⟩ : syracuseStep 1853381 = 347509) (by norm_num)
theorem B1099733 : Blo 730325 1099733 := bbase (se 7 (by rfl) ⟨12887, by rfl⟩ : syracuseStep 1099733 = 25775) (by norm_num)
theorem B1099757 : Blo 730325 1099757 := bbase (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) (by norm_num)
theorem B1099781 : Blo 730325 1099781 := bbase (se 4 (by rfl) ⟨103104, by rfl⟩ : syracuseStep 1099781 = 206209) (by norm_num)
theorem B1099805 : Blo 730325 1099805 := bbase (se 3 (by rfl) ⟨206213, by rfl⟩ : syracuseStep 1099805 = 412427) (by norm_num)
theorem B1099829 : Blo 730325 1099829 := bbase (se 5 (by rfl) ⟨51554, by rfl⟩ : syracuseStep 1099829 = 103109) (by norm_num)
theorem B1099853 : Blo 730325 1099853 := bbase (se 3 (by rfl) ⟨206222, by rfl⟩ : syracuseStep 1099853 = 412445) (by norm_num)
theorem B1099877 : Blo 730325 1099877 := bbase (se 4 (by rfl) ⟨103113, by rfl⟩ : syracuseStep 1099877 = 206227) (by norm_num)
theorem B1099901 : Blo 730325 1099901 := bbase (se 3 (by rfl) ⟨206231, by rfl⟩ : syracuseStep 1099901 = 412463) (by norm_num)
theorem B1099925 : Blo 730325 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B1099949 : Blo 730325 1099949 := bbase (se 3 (by rfl) ⟨206240, by rfl⟩ : syracuseStep 1099949 = 412481) (by norm_num)
theorem B1099973 : Blo 730325 1099973 := bbase (se 4 (by rfl) ⟨103122, by rfl⟩ : syracuseStep 1099973 = 206245) (by norm_num)
theorem B5556437 : Blo 730325 5556437 := bbase (se 7 (by rfl) ⟨65114, by rfl⟩ : syracuseStep 5556437 = 130229) (by norm_num)
theorem B1099997 : Blo 730325 1099997 := bbase (se 3 (by rfl) ⟨206249, by rfl⟩ : syracuseStep 1099997 = 412499) (by norm_num)
theorem B1100021 : Blo 730325 1100021 := bbase (se 5 (by rfl) ⟨51563, by rfl⟩ : syracuseStep 1100021 = 103127) (by norm_num)
theorem B2476277 : Blo 730325 2476277 := bbase (se 5 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 2476277 = 232151) (by norm_num)
theorem B1100045 : Blo 730325 1100045 := bbase (se 3 (by rfl) ⟨206258, by rfl⟩ : syracuseStep 1100045 = 412517) (by norm_num)
theorem B1853725 : Blo 730325 1853725 := bbase (se 3 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 1853725 = 695147) (by norm_num)
theorem B1100069 : Blo 730325 1100069 := bbase (se 4 (by rfl) ⟨103131, by rfl⟩ : syracuseStep 1100069 = 206263) (by norm_num)
theorem B1100093 : Blo 730325 1100093 := bbase (se 3 (by rfl) ⟨206267, by rfl⟩ : syracuseStep 1100093 = 412535) (by norm_num)
theorem B1100117 : Blo 730325 1100117 := bbase (se 10 (by rfl) ⟨1611, by rfl⟩ : syracuseStep 1100117 = 3223) (by norm_num)
theorem B1100141 : Blo 730325 1100141 := bbase (se 3 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 1100141 = 412553) (by norm_num)
theorem B1100165 : Blo 730325 1100165 := bbase (se 4 (by rfl) ⟨103140, by rfl⟩ : syracuseStep 1100165 = 206281) (by norm_num)
theorem B1853837 : Blo 730325 1853837 := bbase (se 3 (by rfl) ⟨347594, by rfl⟩ : syracuseStep 1853837 = 695189) (by norm_num)
theorem B1100189 : Blo 730325 1100189 := bbase (se 3 (by rfl) ⟨206285, by rfl⟩ : syracuseStep 1100189 = 412571) (by norm_num)
theorem B1100213 : Blo 730325 1100213 := bbase (se 5 (by rfl) ⟨51572, by rfl⟩ : syracuseStep 1100213 = 103145) (by norm_num)
theorem B1100237 : Blo 730325 1100237 := bbase (se 3 (by rfl) ⟨206294, by rfl⟩ : syracuseStep 1100237 = 412589) (by norm_num)
theorem B1100261 : Blo 730325 1100261 := bbase (se 4 (by rfl) ⟨103149, by rfl⟩ : syracuseStep 1100261 = 206299) (by norm_num)
theorem B1100285 : Blo 730325 1100285 := bbase (se 3 (by rfl) ⟨206303, by rfl⟩ : syracuseStep 1100285 = 412607) (by norm_num)
theorem B3951125 : Blo 730325 3951125 := bbase (se 6 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 3951125 = 185209) (by norm_num)
theorem B1100309 : Blo 730325 1100309 := bbase (se 6 (by rfl) ⟨25788, by rfl⟩ : syracuseStep 1100309 = 51577) (by norm_num)
theorem B1100333 : Blo 730325 1100333 := bbase (se 3 (by rfl) ⟨206312, by rfl⟩ : syracuseStep 1100333 = 412625) (by norm_num)
theorem B1755701 : Blo 730325 1755701 := bbase (se 5 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 1755701 = 164597) (by norm_num)
theorem B1100357 : Blo 730325 1100357 := bbase (se 4 (by rfl) ⟨103158, by rfl⟩ : syracuseStep 1100357 = 206317) (by norm_num)
theorem B1854029 : Blo 730325 1854029 := bbase (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) (by norm_num)
theorem B1100381 : Blo 730325 1100381 := bbase (se 3 (by rfl) ⟨206321, by rfl⟩ : syracuseStep 1100381 = 412643) (by norm_num)
theorem B1100405 : Blo 730325 1100405 := bbase (se 5 (by rfl) ⟨51581, by rfl⟩ : syracuseStep 1100405 = 103163) (by norm_num)
theorem B1100429 : Blo 730325 1100429 := bbase (se 3 (by rfl) ⟨206330, by rfl⟩ : syracuseStep 1100429 = 412661) (by norm_num)
theorem B1100453 : Blo 730325 1100453 := bbase (se 4 (by rfl) ⟨103167, by rfl⟩ : syracuseStep 1100453 = 206335) (by norm_num)
theorem B2476709 : Blo 730325 2476709 := bbase (se 4 (by rfl) ⟨232191, by rfl⟩ : syracuseStep 2476709 = 464383) (by norm_num)
theorem B1100477 : Blo 730325 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B1100501 : Blo 730325 1100501 := bbase (se 7 (by rfl) ⟨12896, by rfl⟩ : syracuseStep 1100501 = 25793) (by norm_num)
theorem B1100525 : Blo 730325 1100525 := bbase (se 3 (by rfl) ⟨206348, by rfl⟩ : syracuseStep 1100525 = 412697) (by norm_num)
theorem B2083573 : Blo 730325 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B1100549 : Blo 730325 1100549 := bbase (se 4 (by rfl) ⟨103176, by rfl⟩ : syracuseStep 1100549 = 206353) (by norm_num)
theorem B1100573 : Blo 730325 1100573 := bbase (se 3 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 1100573 = 412715) (by norm_num)
theorem B1100597 : Blo 730325 1100597 := bbase (se 5 (by rfl) ⟨51590, by rfl⟩ : syracuseStep 1100597 = 103181) (by norm_num)
theorem B3132229 : Blo 730325 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B1100621 : Blo 730325 1100621 := bbase (se 3 (by rfl) ⟨206366, by rfl⟩ : syracuseStep 1100621 = 412733) (by norm_num)
theorem B1100645 : Blo 730325 1100645 := bbase (se 4 (by rfl) ⟨103185, by rfl⟩ : syracuseStep 1100645 = 206371) (by norm_num)
theorem B1100669 : Blo 730325 1100669 := bbase (se 3 (by rfl) ⟨206375, by rfl⟩ : syracuseStep 1100669 = 412751) (by norm_num)
theorem B1100693 : Blo 730325 1100693 := bbase (se 6 (by rfl) ⟨25797, by rfl⟩ : syracuseStep 1100693 = 51595) (by norm_num)
theorem B1854373 : Blo 730325 1854373 := bbase (se 4 (by rfl) ⟨173847, by rfl⟩ : syracuseStep 1854373 = 347695) (by norm_num)
theorem B1100717 : Blo 730325 1100717 := bbase (se 3 (by rfl) ⟨206384, by rfl⟩ : syracuseStep 1100717 = 412769) (by norm_num)
theorem B5622709 : Blo 730325 5622709 := bbase (se 5 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 5622709 = 527129) (by norm_num)
theorem B1100741 : Blo 730325 1100741 := bbase (se 4 (by rfl) ⟨103194, by rfl⟩ : syracuseStep 1100741 = 206389) (by norm_num)
theorem B1100765 : Blo 730325 1100765 := bbase (se 3 (by rfl) ⟨206393, by rfl⟩ : syracuseStep 1100765 = 412787) (by norm_num)
theorem B3525605 : Blo 730325 3525605 := bbase (se 4 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 3525605 = 661051) (by norm_num)
theorem B740333 : Blo 730325 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B1100789 : Blo 730325 1100789 := bbase (se 5 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 1100789 = 103199) (by norm_num)
theorem B1100813 : Blo 730325 1100813 := bbase (se 3 (by rfl) ⟨206402, by rfl⟩ : syracuseStep 1100813 = 412805) (by norm_num)
theorem B1854485 : Blo 730325 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B1100837 : Blo 730325 1100837 := bbase (se 4 (by rfl) ⟨103203, by rfl⟩ : syracuseStep 1100837 = 206407) (by norm_num)
theorem B937021 : Blo 730325 937021 := bbase (se 3 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 937021 = 351383) (by norm_num)
theorem B1100861 : Blo 730325 1100861 := bbase (se 3 (by rfl) ⟨206411, by rfl⟩ : syracuseStep 1100861 = 412823) (by norm_num)
theorem B1100885 : Blo 730325 1100885 := bbase (se 8 (by rfl) ⟨6450, by rfl⟩ : syracuseStep 1100885 = 12901) (by norm_num)
theorem B2477141 : Blo 730325 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B1100909 : Blo 730325 1100909 := bbase (se 3 (by rfl) ⟨206420, by rfl⟩ : syracuseStep 1100909 = 412841) (by norm_num)
theorem B1100933 : Blo 730325 1100933 := bbase (se 4 (by rfl) ⟨103212, by rfl⟩ : syracuseStep 1100933 = 206425) (by norm_num)
theorem B6245525 : Blo 730325 6245525 := bbase (se 6 (by rfl) ⟨146379, by rfl⟩ : syracuseStep 6245525 = 292759) (by norm_num)
theorem B1100957 : Blo 730325 1100957 := bbase (se 3 (by rfl) ⟨206429, by rfl⟩ : syracuseStep 1100957 = 412859) (by norm_num)
theorem B1100981 : Blo 730325 1100981 := bbase (se 5 (by rfl) ⟨51608, by rfl⟩ : syracuseStep 1100981 = 103217) (by norm_num)
theorem B1101005 : Blo 730325 1101005 := bbase (se 3 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 1101005 = 412877) (by norm_num)
theorem B1854677 : Blo 730325 1854677 := bbase (se 7 (by rfl) ⟨21734, by rfl⟩ : syracuseStep 1854677 = 43469) (by norm_num)
theorem B1101029 : Blo 730325 1101029 := bbase (se 4 (by rfl) ⟨103221, by rfl⟩ : syracuseStep 1101029 = 206443) (by norm_num)
theorem B1101053 : Blo 730325 1101053 := bbase (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) (by norm_num)
theorem B1101077 : Blo 730325 1101077 := bbase (se 6 (by rfl) ⟨25806, by rfl⟩ : syracuseStep 1101077 = 51613) (by norm_num)
theorem B1101101 : Blo 730325 1101101 := bbase (se 3 (by rfl) ⟨206456, by rfl⟩ : syracuseStep 1101101 = 412913) (by norm_num)
theorem B1101125 : Blo 730325 1101125 := bbase (se 4 (by rfl) ⟨103230, by rfl⟩ : syracuseStep 1101125 = 206461) (by norm_num)
theorem B1101149 : Blo 730325 1101149 := bbase (se 3 (by rfl) ⟨206465, by rfl⟩ : syracuseStep 1101149 = 412931) (by norm_num)
theorem B1101173 : Blo 730325 1101173 := bbase (se 5 (by rfl) ⟨51617, by rfl⟩ : syracuseStep 1101173 = 103235) (by norm_num)
theorem B1101197 : Blo 730325 1101197 := bbase (se 3 (by rfl) ⟨206474, by rfl⟩ : syracuseStep 1101197 = 412949) (by norm_num)
theorem B10833301 : Blo 730325 10833301 := bbase (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) (by norm_num)
theorem B1101221 : Blo 730325 1101221 := bbase (se 4 (by rfl) ⟨103239, by rfl⟩ : syracuseStep 1101221 = 206479) (by norm_num)
theorem B1559981 : Blo 730325 1559981 := bbase (se 3 (by rfl) ⟨292496, by rfl⟩ : syracuseStep 1559981 = 584993) (by norm_num)
theorem B1101245 : Blo 730325 1101245 := bbase (se 3 (by rfl) ⟨206483, by rfl⟩ : syracuseStep 1101245 = 412967) (by norm_num)
theorem B1068485 : Blo 730325 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B2641349 : Blo 730325 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B1101269 : Blo 730325 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B1101293 : Blo 730325 1101293 := bbase (se 3 (by rfl) ⟨206492, by rfl⟩ : syracuseStep 1101293 = 412985) (by norm_num)
theorem B2477573 : Blo 730325 2477573 := bbase (se 4 (by rfl) ⟨232272, by rfl⟩ : syracuseStep 2477573 = 464545) (by norm_num)
theorem B1101317 : Blo 730325 1101317 := bbase (se 4 (by rfl) ⟨103248, by rfl⟩ : syracuseStep 1101317 = 206497) (by norm_num)
theorem B1101341 : Blo 730325 1101341 := bbase (se 3 (by rfl) ⟨206501, by rfl⟩ : syracuseStep 1101341 = 413003) (by norm_num)
theorem B2346533 : Blo 730325 2346533 := bbase (se 4 (by rfl) ⟨219987, by rfl⟩ : syracuseStep 2346533 = 439975) (by norm_num)
theorem B1855021 : Blo 730325 1855021 := bbase (se 3 (by rfl) ⟨347816, by rfl⟩ : syracuseStep 1855021 = 695633) (by norm_num)
theorem B4574773 : Blo 730325 4574773 := bbase (se 5 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 4574773 = 428885) (by norm_num)
theorem B1101365 : Blo 730325 1101365 := bbase (se 5 (by rfl) ⟨51626, by rfl⟩ : syracuseStep 1101365 = 103253) (by norm_num)
theorem B3395141 : Blo 730325 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B1101389 : Blo 730325 1101389 := bbase (se 3 (by rfl) ⟨206510, by rfl⟩ : syracuseStep 1101389 = 413021) (by norm_num)
theorem B1101413 : Blo 730325 1101413 := bbase (se 4 (by rfl) ⟨103257, by rfl⟩ : syracuseStep 1101413 = 206515) (by norm_num)
theorem B1232509 : Blo 730325 1232509 := bbase (se 3 (by rfl) ⟨231095, by rfl⟩ : syracuseStep 1232509 = 462191) (by norm_num)
theorem B1101437 : Blo 730325 1101437 := bbase (se 3 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 1101437 = 413039) (by norm_num)
theorem B1101461 : Blo 730325 1101461 := bbase (se 6 (by rfl) ⟨25815, by rfl⟩ : syracuseStep 1101461 = 51631) (by norm_num)
theorem B1855133 : Blo 730325 1855133 := bbase (se 3 (by rfl) ⟨347837, by rfl⟩ : syracuseStep 1855133 = 695675) (by norm_num)
theorem B1101485 : Blo 730325 1101485 := bbase (se 3 (by rfl) ⟨206528, by rfl⟩ : syracuseStep 1101485 = 413057) (by norm_num)
theorem B1232597 : Blo 730325 1232597 := bbase (se 7 (by rfl) ⟨14444, by rfl⟩ : syracuseStep 1232597 = 28889) (by norm_num)
theorem B1232725 : Blo 730325 1232725 := bbase (se 9 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 1232725 = 7223) (by norm_num)
theorem B1855325 : Blo 730325 1855325 := bbase (se 3 (by rfl) ⟨347873, by rfl⟩ : syracuseStep 1855325 = 695747) (by norm_num)
theorem B1560485 : Blo 730325 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B1232813 : Blo 730325 1232813 := bbase (se 3 (by rfl) ⟨231152, by rfl⟩ : syracuseStep 1232813 = 462305) (by norm_num)
theorem B1560493 : Blo 730325 1560493 := bbase (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) (by norm_num)
theorem B2478005 : Blo 730325 2478005 := bbase (se 5 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 2478005 = 232313) (by norm_num)
theorem B1232941 : Blo 730325 1232941 := bbase (se 3 (by rfl) ⟨231176, by rfl⟩ : syracuseStep 1232941 = 462353) (by norm_num)
theorem B1233029 : Blo 730325 1233029 := bbase (se 4 (by rfl) ⟨115596, by rfl⟩ : syracuseStep 1233029 = 231193) (by norm_num)
theorem B1855669 : Blo 730325 1855669 := bbase (se 5 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 1855669 = 173969) (by norm_num)
theorem B2085077 : Blo 730325 2085077 := bbase (se 7 (by rfl) ⟨24434, by rfl⟩ : syracuseStep 2085077 = 48869) (by norm_num)
theorem B2773237 : Blo 730325 2773237 := bbase (se 5 (by rfl) ⟨129995, by rfl⟩ : syracuseStep 2773237 = 259991) (by norm_num)
theorem B1233157 : Blo 730325 1233157 := bbase (se 4 (by rfl) ⟨115608, by rfl⟩ : syracuseStep 1233157 = 231217) (by norm_num)
theorem B1757477 : Blo 730325 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B2347301 : Blo 730325 2347301 := bbase (se 4 (by rfl) ⟨220059, by rfl⟩ : syracuseStep 2347301 = 440119) (by norm_num)
theorem B2642213 : Blo 730325 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B1855781 : Blo 730325 1855781 := bbase (se 4 (by rfl) ⟨173979, by rfl⟩ : syracuseStep 1855781 = 347959) (by norm_num)
theorem B1233245 : Blo 730325 1233245 := bbase (se 3 (by rfl) ⟨231233, by rfl⟩ : syracuseStep 1233245 = 462467) (by norm_num)
theorem B741793 : Blo 730325 741793 := bbase (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) (by norm_num)
theorem B5624245 : Blo 730325 5624245 := bbase (se 5 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 5624245 = 527273) (by norm_num)
theorem B1233373 : Blo 730325 1233373 := bbase (se 3 (by rfl) ⟨231257, by rfl⟩ : syracuseStep 1233373 = 462515) (by norm_num)
theorem B1855973 : Blo 730325 1855973 := bbase (se 4 (by rfl) ⟨173997, by rfl⟩ : syracuseStep 1855973 = 347995) (by norm_num)
theorem B2773541 : Blo 730325 2773541 := bbase (se 4 (by rfl) ⟨260019, by rfl⟩ : syracuseStep 2773541 = 520039) (by norm_num)
theorem B1233461 : Blo 730325 1233461 := bbase (se 5 (by rfl) ⟨57818, by rfl⟩ : syracuseStep 1233461 = 115637) (by norm_num)
theorem B1692269 : Blo 730325 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B1233589 : Blo 730325 1233589 := bbase (se 5 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 1233589 = 115649) (by norm_num)
theorem B1233677 : Blo 730325 1233677 := bbase (se 3 (by rfl) ⟨231314, by rfl⟩ : syracuseStep 1233677 = 462629) (by norm_num)
theorem B2347813 : Blo 730325 2347813 := bbase (se 4 (by rfl) ⟨220107, by rfl⟩ : syracuseStep 2347813 = 440215) (by norm_num)
theorem B1856317 : Blo 730325 1856317 := bbase (se 3 (by rfl) ⟨348059, by rfl⟩ : syracuseStep 1856317 = 696119) (by norm_num)
theorem B1233805 : Blo 730325 1233805 := bbase (se 3 (by rfl) ⟨231338, by rfl⟩ : syracuseStep 1233805 = 462677) (by norm_num)
theorem B1856429 : Blo 730325 1856429 := bbase (se 3 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 1856429 = 696161) (by norm_num)
theorem B1233893 : Blo 730325 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B1561621 : Blo 730325 1561621 := bbase (se 6 (by rfl) ⟨36600, by rfl⟩ : syracuseStep 1561621 = 73201) (by norm_num)
theorem B939037 : Blo 730325 939037 := bbase (se 3 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 939037 = 352139) (by norm_num)
theorem B1234021 : Blo 730325 1234021 := bbase (se 4 (by rfl) ⟨115689, by rfl⟩ : syracuseStep 1234021 = 231379) (by norm_num)
theorem B1856621 : Blo 730325 1856621 := bbase (se 3 (by rfl) ⟨348116, by rfl⟩ : syracuseStep 1856621 = 696233) (by norm_num)
theorem B1234109 : Blo 730325 1234109 := bbase (se 3 (by rfl) ⟨231395, by rfl⟩ : syracuseStep 1234109 = 462791) (by norm_num)
theorem B2512117 : Blo 730325 2512117 := bbase (se 5 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 2512117 = 235511) (by norm_num)
theorem B1234237 : Blo 730325 1234237 := bbase (se 3 (by rfl) ⟨231419, by rfl⟩ : syracuseStep 1234237 = 462839) (by norm_num)
theorem B1561997 : Blo 730325 1561997 := bbase (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) (by norm_num)
theorem B1234325 : Blo 730325 1234325 := bbase (se 6 (by rfl) ⟨28929, by rfl⟩ : syracuseStep 1234325 = 57859) (by norm_num)
theorem B1856965 : Blo 730325 1856965 := bbase (se 4 (by rfl) ⟨174090, by rfl⟩ : syracuseStep 1856965 = 348181) (by norm_num)
theorem B1234453 : Blo 730325 1234453 := bbase (se 6 (by rfl) ⟨28932, by rfl⟩ : syracuseStep 1234453 = 57865) (by norm_num)
theorem B13391381 : Blo 730325 13391381 := bbase (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) (by norm_num)
theorem B1857077 : Blo 730325 1857077 := bbase (se 5 (by rfl) ⟨87050, by rfl⟩ : syracuseStep 1857077 = 174101) (by norm_num)
theorem B1234541 : Blo 730325 1234541 := bbase (se 3 (by rfl) ⟨231476, by rfl⟩ : syracuseStep 1234541 = 462953) (by norm_num)
theorem B7034485 : Blo 730325 7034485 := bbase (se 5 (by rfl) ⟨329741, by rfl⟩ : syracuseStep 7034485 = 659483) (by norm_num)
theorem B939745 : Blo 730325 939745 := bbase (se 2 (by rfl) ⟨352404, by rfl⟩ : syracuseStep 939745 = 704809) (by norm_num)
theorem B1234669 : Blo 730325 1234669 := bbase (se 3 (by rfl) ⟨231500, by rfl⟩ : syracuseStep 1234669 = 463001) (by norm_num)
theorem B1857269 : Blo 730325 1857269 := bbase (se 5 (by rfl) ⟨87059, by rfl⟩ : syracuseStep 1857269 = 174119) (by norm_num)
theorem B2086661 : Blo 730325 2086661 := bbase (se 4 (by rfl) ⟨195624, by rfl⟩ : syracuseStep 2086661 = 391249) (by norm_num)
theorem B1234757 : Blo 730325 1234757 := bbase (se 4 (by rfl) ⟨115758, by rfl⟩ : syracuseStep 1234757 = 231517) (by norm_num)
theorem B743261 : Blo 730325 743261 := bbase (se 3 (by rfl) ⟨139361, by rfl⟩ : syracuseStep 743261 = 278723) (by norm_num)
theorem B1234885 : Blo 730325 1234885 := bbase (se 4 (by rfl) ⟨115770, by rfl⟩ : syracuseStep 1234885 = 231541) (by norm_num)
theorem B5625845 : Blo 730325 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B1234973 : Blo 730325 1234973 := bbase (se 3 (by rfl) ⟨231557, by rfl⟩ : syracuseStep 1234973 = 463115) (by norm_num)
theorem B6248501 : Blo 730325 6248501 := bbase (se 5 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 6248501 = 585797) (by norm_num)
theorem B1857613 : Blo 730325 1857613 := bbase (se 3 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 1857613 = 696605) (by norm_num)
theorem B1235101 : Blo 730325 1235101 := bbase (se 3 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 1235101 = 463163) (by norm_num)
theorem B1857725 : Blo 730325 1857725 := bbase (se 3 (by rfl) ⟨348323, by rfl⟩ : syracuseStep 1857725 = 696647) (by norm_num)
theorem B1235189 : Blo 730325 1235189 := bbase (se 5 (by rfl) ⟨57899, by rfl⟩ : syracuseStep 1235189 = 115799) (by norm_num)
theorem B1759573 : Blo 730325 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B2677093 : Blo 730325 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B1235317 : Blo 730325 1235317 := bbase (se 5 (by rfl) ⟨57905, by rfl⟩ : syracuseStep 1235317 = 115811) (by norm_num)
theorem B1857917 : Blo 730325 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B2087333 : Blo 730325 2087333 := bbase (se 4 (by rfl) ⟨195687, by rfl⟩ : syracuseStep 2087333 = 391375) (by norm_num)
theorem B1235405 : Blo 730325 1235405 := bbase (se 3 (by rfl) ⟨231638, by rfl⟩ : syracuseStep 1235405 = 463277) (by norm_num)
theorem B2349557 : Blo 730325 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B4512277 : Blo 730325 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B1235533 : Blo 730325 1235533 := bbase (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) (by norm_num)
theorem B2775653 : Blo 730325 2775653 := bbase (se 4 (by rfl) ⟨260217, by rfl⟩ : syracuseStep 2775653 = 520435) (by norm_num)
theorem B1432205 : Blo 730325 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B1235621 : Blo 730325 1235621 := bbase (se 4 (by rfl) ⟨115839, by rfl⟩ : syracuseStep 1235621 = 231679) (by norm_num)
theorem B2349749 : Blo 730325 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B1858261 : Blo 730325 1858261 := bbase (se 7 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 1858261 = 43553) (by norm_num)
theorem B1235749 : Blo 730325 1235749 := bbase (se 4 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 1235749 = 231703) (by norm_num)
theorem B1858373 : Blo 730325 1858373 := bbase (se 4 (by rfl) ⟨174222, by rfl⟩ : syracuseStep 1858373 = 348445) (by norm_num)
theorem B4447061 : Blo 730325 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B2087765 : Blo 730325 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1170293 : Blo 730325 1170293 := bbase (se 5 (by rfl) ⟨54857, by rfl⟩ : syracuseStep 1170293 = 109715) (by norm_num)
theorem B1235837 : Blo 730325 1235837 := bbase (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) (by norm_num)
theorem B2775941 : Blo 730325 2775941 := bbase (se 4 (by rfl) ⟨260244, by rfl⟩ : syracuseStep 2775941 = 520489) (by norm_num)
theorem B1563637 : Blo 730325 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B1235965 : Blo 730325 1235965 := bbase (se 3 (by rfl) ⟨231743, by rfl⟩ : syracuseStep 1235965 = 463487) (by norm_num)
theorem B1858565 : Blo 730325 1858565 := bbase (se 4 (by rfl) ⟨174240, by rfl⟩ : syracuseStep 1858565 = 348481) (by norm_num)
theorem B1760285 : Blo 730325 1760285 := bbase (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) (by norm_num)
theorem B1236053 : Blo 730325 1236053 := bbase (se 8 (by rfl) ⟨7242, by rfl⟩ : syracuseStep 1236053 = 14485) (by norm_num)
theorem B1236181 : Blo 730325 1236181 := bbase (se 7 (by rfl) ⟨14486, by rfl⟩ : syracuseStep 1236181 = 28973) (by norm_num)
theorem B1236269 : Blo 730325 1236269 := bbase (se 3 (by rfl) ⟨231800, by rfl⟩ : syracuseStep 1236269 = 463601) (by norm_num)
theorem B3956053 : Blo 730325 3956053 := bbase (se 11 (by rfl) ⟨2897, by rfl⟩ : syracuseStep 3956053 = 5795) (by norm_num)
theorem B13557077 : Blo 730325 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B1170845 : Blo 730325 1170845 := bbase (se 3 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 1170845 = 439067) (by norm_num)
theorem B1760669 : Blo 730325 1760669 := bbase (se 3 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 1760669 = 660251) (by norm_num)
theorem B1236397 : Blo 730325 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B1170877 : Blo 730325 1170877 := bbase (se 3 (by rfl) ⟨219539, by rfl⟩ : syracuseStep 1170877 = 439079) (by norm_num)
theorem B2973125 : Blo 730325 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1269245 : Blo 730325 1269245 := bbase (se 3 (by rfl) ⟨237983, by rfl⟩ : syracuseStep 1269245 = 475967) (by norm_num)
theorem B1236485 : Blo 730325 1236485 := bbase (se 4 (by rfl) ⟨115920, by rfl⟩ : syracuseStep 1236485 = 231841) (by norm_num)
theorem B2088517 : Blo 730325 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B1236613 : Blo 730325 1236613 := bbase (se 4 (by rfl) ⟨115932, by rfl⟩ : syracuseStep 1236613 = 231865) (by norm_num)
theorem B1760957 : Blo 730325 1760957 := bbase (se 3 (by rfl) ⟨330179, by rfl⟩ : syracuseStep 1760957 = 660359) (by norm_num)
theorem B1236701 : Blo 730325 1236701 := bbase (se 3 (by rfl) ⟨231881, by rfl⟩ : syracuseStep 1236701 = 463763) (by norm_num)
theorem B1040141 : Blo 730325 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B1236829 : Blo 730325 1236829 := bbase (se 3 (by rfl) ⟨231905, by rfl⟩ : syracuseStep 1236829 = 463811) (by norm_num)
theorem B1564525 : Blo 730325 1564525 := bbase (se 3 (by rfl) ⟨293348, by rfl⟩ : syracuseStep 1564525 = 586697) (by norm_num)
theorem B1269661 : Blo 730325 1269661 := bbase (se 3 (by rfl) ⟨238061, by rfl⟩ : syracuseStep 1269661 = 476123) (by norm_num)
theorem B1236917 : Blo 730325 1236917 := bbase (se 5 (by rfl) ⟨57980, by rfl⟩ : syracuseStep 1236917 = 115961) (by norm_num)
theorem B2777125 : Blo 730325 2777125 := bbase (se 4 (by rfl) ⟨260355, by rfl⟩ : syracuseStep 2777125 = 520711) (by norm_num)
theorem B1237045 : Blo 730325 1237045 := bbase (se 5 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 1237045 = 115973) (by norm_num)
theorem B2384005 : Blo 730325 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1237133 : Blo 730325 1237133 := bbase (se 3 (by rfl) ⟨231962, by rfl⟩ : syracuseStep 1237133 = 463925) (by norm_num)
theorem B1237261 : Blo 730325 1237261 := bbase (se 3 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 1237261 = 463973) (by norm_num)
theorem B1040693 : Blo 730325 1040693 := bbase (se 5 (by rfl) ⟨48782, by rfl⟩ : syracuseStep 1040693 = 97565) (by norm_num)
theorem B2777429 : Blo 730325 2777429 := bbase (se 10 (by rfl) ⟨4068, by rfl⟩ : syracuseStep 2777429 = 8137) (by norm_num)
theorem B1171805 : Blo 730325 1171805 := bbase (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) (by norm_num)
theorem B1565021 : Blo 730325 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1237349 : Blo 730325 1237349 := bbase (se 4 (by rfl) ⟨116001, by rfl⟩ : syracuseStep 1237349 = 232003) (by norm_num)
theorem B1237477 : Blo 730325 1237477 := bbase (se 4 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 1237477 = 232027) (by norm_num)
theorem B1237565 : Blo 730325 1237565 := bbase (se 3 (by rfl) ⟨232043, by rfl⟩ : syracuseStep 1237565 = 464087) (by norm_num)
theorem B1237693 : Blo 730325 1237693 := bbase (se 3 (by rfl) ⟨232067, by rfl⟩ : syracuseStep 1237693 = 464135) (by norm_num)
theorem B1237781 : Blo 730325 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B1336109 : Blo 730325 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B1237909 : Blo 730325 1237909 := bbase (se 6 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 1237909 = 58027) (by norm_num)
theorem B1237997 : Blo 730325 1237997 := bbase (se 3 (by rfl) ⟨232124, by rfl⟩ : syracuseStep 1237997 = 464249) (by norm_num)
theorem B1172485 : Blo 730325 1172485 := bbase (se 4 (by rfl) ⟨109920, by rfl⟩ : syracuseStep 1172485 = 219841) (by norm_num)
theorem B1041445 : Blo 730325 1041445 := bbase (se 4 (by rfl) ⟨97635, by rfl⟩ : syracuseStep 1041445 = 195271) (by norm_num)
theorem B1172549 : Blo 730325 1172549 := bbase (se 4 (by rfl) ⟨109926, by rfl⟩ : syracuseStep 1172549 = 219853) (by norm_num)
theorem B1238125 : Blo 730325 1238125 := bbase (se 3 (by rfl) ⟨232148, by rfl⟩ : syracuseStep 1238125 = 464297) (by norm_num)
theorem B1565885 : Blo 730325 1565885 := bbase (se 3 (by rfl) ⟨293603, by rfl⟩ : syracuseStep 1565885 = 587207) (by norm_num)
theorem B1238213 : Blo 730325 1238213 := bbase (se 4 (by rfl) ⟨116082, by rfl⟩ : syracuseStep 1238213 = 232165) (by norm_num)
theorem B1238341 : Blo 730325 1238341 := bbase (se 4 (by rfl) ⟨116094, by rfl⟩ : syracuseStep 1238341 = 232189) (by norm_num)
theorem B1566029 : Blo 730325 1566029 := bbase (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) (by norm_num)
theorem B1238429 : Blo 730325 1238429 := bbase (se 3 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 1238429 = 464411) (by norm_num)
theorem B11855317 : Blo 730325 11855317 := bbase (se 7 (by rfl) ⟨138929, by rfl⟩ : syracuseStep 11855317 = 277859) (by norm_num)
theorem B1238557 : Blo 730325 1238557 := bbase (se 3 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 1238557 = 464459) (by norm_num)
theorem B1238645 : Blo 730325 1238645 := bbase (se 5 (by rfl) ⟨58061, by rfl⟩ : syracuseStep 1238645 = 116123) (by norm_num)
theorem B779905 : Blo 730325 779905 := bbase (se 2 (by rfl) ⟨292464, by rfl⟩ : syracuseStep 779905 = 584929) (by norm_num)
theorem B878249 : Blo 730325 878249 := bbase (se 2 (by rfl) ⟨329343, by rfl⟩ : syracuseStep 878249 = 658687) (by norm_num)
theorem B1238773 : Blo 730325 1238773 := bbase (se 5 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 1238773 = 116135) (by norm_num)
theorem B5564213 : Blo 730325 5564213 := bbase (se 5 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 5564213 = 521645) (by norm_num)
theorem B1042237 : Blo 730325 1042237 := bbase (se 3 (by rfl) ⟨195419, by rfl⟩ : syracuseStep 1042237 = 390839) (by norm_num)
theorem B1238861 : Blo 730325 1238861 := bbase (se 3 (by rfl) ⟨232286, by rfl⟩ : syracuseStep 1238861 = 464573) (by norm_num)
theorem B1238989 : Blo 730325 1238989 := bbase (se 3 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 1238989 = 464621) (by norm_num)
theorem B15820757 : Blo 730325 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B1239077 : Blo 730325 1239077 := bbase (se 4 (by rfl) ⟨116163, by rfl⟩ : syracuseStep 1239077 = 232327) (by norm_num)
theorem B1566773 : Blo 730325 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1042573 : Blo 730325 1042573 := bbase (se 3 (by rfl) ⟨195482, by rfl⟩ : syracuseStep 1042573 = 390965) (by norm_num)
theorem B878941 : Blo 730325 878941 := bbase (se 3 (by rfl) ⟨164801, by rfl⟩ : syracuseStep 878941 = 329603) (by norm_num)
theorem B1042789 : Blo 730325 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B1173869 : Blo 730325 1173869 := bbase (se 3 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 1173869 = 440201) (by norm_num)
theorem B2779541 : Blo 730325 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B780725 : Blo 730325 780725 := bbase (se 5 (by rfl) ⟨36596, by rfl⟩ : syracuseStep 780725 = 73193) (by norm_num)
theorem B1174061 : Blo 730325 1174061 := bbase (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) (by norm_num)
theorem B879157 : Blo 730325 879157 := bbase (se 5 (by rfl) ⟨41210, by rfl⟩ : syracuseStep 879157 = 82421) (by norm_num)
theorem B1174189 : Blo 730325 1174189 := bbase (se 3 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 1174189 = 440321) (by norm_num)
theorem B1764013 : Blo 730325 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B2779829 : Blo 730325 2779829 := bbase (se 5 (by rfl) ⟨130304, by rfl⟩ : syracuseStep 2779829 = 260609) (by norm_num)
theorem B1043165 : Blo 730325 1043165 := bbase (se 3 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 1043165 = 391187) (by norm_num)
theorem B1567525 : Blo 730325 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B781169 : Blo 730325 781169 := bbase (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) (by norm_num)
theorem B1567669 : Blo 730325 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B781417 : Blo 730325 781417 := bbase (se 2 (by rfl) ⟨293031, by rfl⟩ : syracuseStep 781417 = 586063) (by norm_num)
theorem B1666261 : Blo 730325 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B1666333 : Blo 730325 1666333 := bbase (se 3 (by rfl) ⟨312437, by rfl⟩ : syracuseStep 1666333 = 624875) (by norm_num)
theorem B1174829 : Blo 730325 1174829 := bbase (se 3 (by rfl) ⟨220280, by rfl⟩ : syracuseStep 1174829 = 440561) (by norm_num)
theorem B1568045 : Blo 730325 1568045 := bbase (se 3 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 1568045 = 588017) (by norm_num)
theorem B3697973 : Blo 730325 3697973 := bbase (se 5 (by rfl) ⟨173342, by rfl⟩ : syracuseStep 3697973 = 346685) (by norm_num)
theorem B5270933 : Blo 730325 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B2223557 : Blo 730325 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B781849 : Blo 730325 781849 := bbase (se 2 (by rfl) ⟨293193, by rfl⟩ : syracuseStep 781849 = 586387) (by norm_num)
theorem B1306165 : Blo 730325 1306165 := bbase (se 5 (by rfl) ⟨61226, by rfl⟩ : syracuseStep 1306165 = 122453) (by norm_num)
theorem B781921 : Blo 730325 781921 := bbase (se 2 (by rfl) ⟨293220, by rfl⟩ : syracuseStep 781921 = 586441) (by norm_num)
theorem B1175285 : Blo 730325 1175285 := bbase (se 5 (by rfl) ⟨55091, by rfl⟩ : syracuseStep 1175285 = 110183) (by norm_num)
theorem B7499573 : Blo 730325 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B2781013 : Blo 730325 2781013 := bbase (se 9 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 2781013 = 16295) (by norm_num)
theorem B1666981 : Blo 730325 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B782293 : Blo 730325 782293 := bbase (se 7 (by rfl) ⟨9167, by rfl⟩ : syracuseStep 782293 = 18335) (by norm_num)
theorem B1175509 : Blo 730325 1175509 := bbase (se 7 (by rfl) ⟨13775, by rfl⟩ : syracuseStep 1175509 = 27551) (by norm_num)
theorem B1175573 : Blo 730325 1175573 := bbase (se 6 (by rfl) ⟨27552, by rfl⟩ : syracuseStep 1175573 = 55105) (by norm_num)
theorem B1044589 : Blo 730325 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B2781317 : Blo 730325 2781317 := bbase (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) (by norm_num)
theorem B1175701 : Blo 730325 1175701 := bbase (se 6 (by rfl) ⟨27555, by rfl⟩ : syracuseStep 1175701 = 55111) (by norm_num)
theorem B880853 : Blo 730325 880853 := bbase (se 7 (by rfl) ⟨10322, by rfl⟩ : syracuseStep 880853 = 20645) (by norm_num)
theorem B782669 : Blo 730325 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B782741 : Blo 730325 782741 := bbase (se 6 (by rfl) ⟨18345, by rfl⟩ : syracuseStep 782741 = 36691) (by norm_num)
theorem B881065 : Blo 730325 881065 := bbase (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) (by norm_num)
theorem B881209 : Blo 730325 881209 := bbase (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) (by norm_num)
theorem B3699269 : Blo 730325 3699269 := bbase (se 4 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 3699269 = 693613) (by norm_num)
theorem B782929 : Blo 730325 782929 := bbase (se 2 (by rfl) ⟨293598, by rfl⟩ : syracuseStep 782929 = 587197) (by norm_num)
theorem B1503893 : Blo 730325 1503893 := bbase (se 6 (by rfl) ⟨35247, by rfl⟩ : syracuseStep 1503893 = 70495) (by norm_num)
theorem B1045181 : Blo 730325 1045181 := bbase (se 3 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 1045181 = 391943) (by norm_num)
theorem B3764933 : Blo 730325 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B783113 : Blo 730325 783113 := bbase (se 2 (by rfl) ⟨293667, by rfl⟩ : syracuseStep 783113 = 587335) (by norm_num)
theorem B1045261 : Blo 730325 1045261 := bbase (se 3 (by rfl) ⟨195986, by rfl⟩ : syracuseStep 1045261 = 391973) (by norm_num)
theorem B1045381 : Blo 730325 1045381 := bbase (se 4 (by rfl) ⟨98004, by rfl⟩ : syracuseStep 1045381 = 196009) (by norm_num)
theorem B1045477 : Blo 730325 1045477 := bbase (se 4 (by rfl) ⟨98013, by rfl⟩ : syracuseStep 1045477 = 196027) (by norm_num)
theorem B2258405 : Blo 730325 2258405 := bbase (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) (by norm_num)
theorem B783865 : Blo 730325 783865 := bbase (se 2 (by rfl) ⟨293949, by rfl⟩ : syracuseStep 783865 = 587899) (by norm_num)
theorem B1504813 : Blo 730325 1504813 := bbase (se 3 (by rfl) ⟨282152, by rfl⟩ : syracuseStep 1504813 = 564305) (by norm_num)
theorem B783937 : Blo 730325 783937 := bbase (se 2 (by rfl) ⟨293976, by rfl⟩ : syracuseStep 783937 = 587953) (by norm_num)
theorem B784117 : Blo 730325 784117 := bbase (se 5 (by rfl) ⟨36755, by rfl⟩ : syracuseStep 784117 = 73511) (by norm_num)
theorem B3700565 : Blo 730325 3700565 := bbase (se 9 (by rfl) ⟨10841, by rfl⟩ : syracuseStep 3700565 = 21683) (by norm_num)
theorem B4454453 : Blo 730325 4454453 := bbase (se 5 (by rfl) ⟨208802, by rfl⟩ : syracuseStep 4454453 = 417605) (by norm_num)
theorem B2783429 : Blo 730325 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B2783717 : Blo 730325 2783717 := bbase (se 4 (by rfl) ⟨260973, by rfl⟩ : syracuseStep 2783717 = 521947) (by norm_num)
theorem B1669901 : Blo 730325 1669901 := bbase (se 3 (by rfl) ⟨313106, by rfl⟩ : syracuseStep 1669901 = 626213) (by norm_num)
theorem B3701861 : Blo 730325 3701861 := bbase (se 4 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 3701861 = 694099) (by norm_num)
theorem B1670485 : Blo 730325 1670485 := bbase (se 11 (by rfl) ⟨1223, by rfl⟩ : syracuseStep 1670485 = 2447) (by norm_num)
theorem B1113517 : Blo 730325 1113517 := bbase (se 3 (by rfl) ⟨208784, by rfl⟩ : syracuseStep 1113517 = 417569) (by norm_num)
theorem B1113725 : Blo 730325 1113725 := bbase (se 3 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 1113725 = 417647) (by norm_num)
theorem B2784901 : Blo 730325 2784901 := bbase (se 4 (by rfl) ⟨261084, by rfl⟩ : syracuseStep 2784901 = 522169) (by norm_num)
theorem B1408757 : Blo 730325 1408757 := bbase (se 5 (by rfl) ⟨66035, by rfl⟩ : syracuseStep 1408757 = 132071) (by norm_num)
theorem B6356789 : Blo 730325 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B5930837 : Blo 730325 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B2785205 : Blo 730325 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B8355797 : Blo 730325 8355797 := bbase (se 7 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 8355797 = 195839) (by norm_num)
theorem B5275637 : Blo 730325 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B3964963 : Blo 730325 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B3702833 : Blo 730325 3702833 := bstep (se 2 (by rfl) ⟨1388562, by rfl⟩ : syracuseStep 3702833 = 2777125) B2777125
theorem B3178673 : Blo 730325 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B1409233 : Blo 730325 1409233 := bstep (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) B1056925
theorem B57016547 : Blo 730325 57016547 := bstep (se 1 (by rfl) ⟨42762410, by rfl⟩ : syracuseStep 57016547 = 85524821) B85524821
theorem B1114435 : Blo 730325 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B1409411 : Blo 730325 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B1507889 : Blo 730325 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B4162225 : Blo 730325 4162225 := bstep (se 2 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 4162225 = 3121669) B3121669
theorem B4686605 : Blo 730325 4686605 := bstep (se 3 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 4686605 = 1757477) B1757477
theorem B2786147 : Blo 730325 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B3704291 : Blo 730325 3704291 := bstep (se 1 (by rfl) ⟨2778218, by rfl⟩ : syracuseStep 3704291 = 5556437) B5556437
theorem B1115731 : Blo 730325 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B6326029 : Blo 730325 6326029 := bstep (se 3 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 6326029 = 2372261) B2372261
theorem B2787149 : Blo 730325 2787149 := bstep (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) B1045181
theorem B4163683 : Blo 730325 4163683 := bstep (se 1 (by rfl) ⟨3122762, by rfl⟩ : syracuseStep 4163683 = 6245525) B6245525
theorem B3705101 : Blo 730325 3705101 := bstep (se 3 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 3705101 = 1389413) B1389413
theorem B1902865 : Blo 730325 1902865 := bstep (se 2 (by rfl) ⟨713574, by rfl⟩ : syracuseStep 1902865 = 1427149) B1427149
theorem B2263427 : Blo 730325 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B821731 : Blo 730325 821731 := bstep (se 1 (by rfl) ⟨616298, by rfl⟩ : syracuseStep 821731 = 1232597) B1232597
theorem B4164209 : Blo 730325 4164209 := bstep (se 2 (by rfl) ⟨1561578, by rfl⟩ : syracuseStep 4164209 = 3123157) B3123157
theorem B821875 : Blo 730325 821875 := bstep (se 1 (by rfl) ⟨616406, by rfl⟩ : syracuseStep 821875 = 1232813) B1232813
theorem B822019 : Blo 730325 822019 := bstep (se 1 (by rfl) ⟨616514, by rfl⟩ : syracuseStep 822019 = 1233029) B1233029
theorem B822163 : Blo 730325 822163 := bstep (se 1 (by rfl) ⟨616622, by rfl⟩ : syracuseStep 822163 = 1233245) B1233245
theorem B4688837 : Blo 730325 4688837 := bstep (se 4 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 4688837 = 879157) B879157
theorem B7048133 : Blo 730325 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B822307 : Blo 730325 822307 := bstep (se 1 (by rfl) ⟨616730, by rfl⟩ : syracuseStep 822307 = 1233461) B1233461
theorem B822451 : Blo 730325 822451 := bstep (se 1 (by rfl) ⟨616838, by rfl⟩ : syracuseStep 822451 = 1233677) B1233677
theorem B822595 : Blo 730325 822595 := bstep (se 1 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 822595 = 1233893) B1233893
theorem B822739 : Blo 730325 822739 := bstep (se 1 (by rfl) ⟨617054, by rfl⟩ : syracuseStep 822739 = 1234109) B1234109
theorem B822883 : Blo 730325 822883 := bstep (se 1 (by rfl) ⟨617162, by rfl⟩ : syracuseStep 822883 = 1234325) B1234325
theorem B823027 : Blo 730325 823027 := bstep (se 1 (by rfl) ⟨617270, by rfl⟩ : syracuseStep 823027 = 1234541) B1234541
theorem B823171 : Blo 730325 823171 := bstep (se 1 (by rfl) ⟨617378, by rfl⟩ : syracuseStep 823171 = 1234757) B1234757
theorem B823315 : Blo 730325 823315 := bstep (se 1 (by rfl) ⟨617486, by rfl⟩ : syracuseStep 823315 = 1234973) B1234973
theorem B4165667 : Blo 730325 4165667 := bstep (se 1 (by rfl) ⟨3124250, by rfl⟩ : syracuseStep 4165667 = 6248501) B6248501
theorem B5279813 : Blo 730325 5279813 := bstep (se 4 (by rfl) ⟨494982, by rfl⟩ : syracuseStep 5279813 = 989965) B989965
theorem B2822221 : Blo 730325 2822221 := bstep (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) B1058333
theorem B1249361 : Blo 730325 1249361 := bstep (se 2 (by rfl) ⟨468510, by rfl⟩ : syracuseStep 1249361 = 937021) B937021
theorem B823459 : Blo 730325 823459 := bstep (se 1 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 823459 = 1235189) B1235189
theorem B7901381 : Blo 730325 7901381 := bstep (se 4 (by rfl) ⟨740754, by rfl⟩ : syracuseStep 7901381 = 1481509) B1481509
theorem B823603 : Blo 730325 823603 := bstep (se 1 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 823603 = 1235405) B1235405
theorem B3346829 : Blo 730325 3346829 := bstep (se 3 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 3346829 = 1255061) B1255061
theorem B823747 : Blo 730325 823747 := bstep (se 1 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 823747 = 1235621) B1235621
theorem B823891 : Blo 730325 823891 := bstep (se 1 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 823891 = 1235837) B1235837
theorem B824035 : Blo 730325 824035 := bstep (se 1 (by rfl) ⟨618026, by rfl⟩ : syracuseStep 824035 = 1236053) B1236053
theorem B6099697 : Blo 730325 6099697 := bstep (se 2 (by rfl) ⟨2287386, by rfl⟩ : syracuseStep 6099697 = 4574773) B4574773
theorem B1741553 : Blo 730325 1741553 := bstep (se 2 (by rfl) ⟨653082, by rfl⟩ : syracuseStep 1741553 = 1306165) B1306165
theorem B1643345 : Blo 730325 1643345 := bstep (se 2 (by rfl) ⟨616254, by rfl⟩ : syracuseStep 1643345 = 1232509) B1232509
theorem B1643363 : Blo 730325 1643363 := bstep (se 1 (by rfl) ⟨1232522, by rfl⟩ : syracuseStep 1643363 = 2465045) B2465045
theorem B824179 : Blo 730325 824179 := bstep (se 1 (by rfl) ⟨618134, by rfl⟩ : syracuseStep 824179 = 1236269) B1236269
theorem B824323 : Blo 730325 824323 := bstep (se 1 (by rfl) ⟨618242, by rfl⟩ : syracuseStep 824323 = 1236485) B1236485
theorem B1643633 : Blo 730325 1643633 := bstep (se 2 (by rfl) ⟨616362, by rfl⟩ : syracuseStep 1643633 = 1232725) B1232725
theorem B3708017 : Blo 730325 3708017 := bstep (se 2 (by rfl) ⟨1390506, by rfl⟩ : syracuseStep 3708017 = 2781013) B2781013
theorem B1643651 : Blo 730325 1643651 := bstep (se 1 (by rfl) ⟨1232738, by rfl⟩ : syracuseStep 1643651 = 2465477) B2465477
theorem B824467 : Blo 730325 824467 := bstep (se 1 (by rfl) ⟨618350, by rfl⟩ : syracuseStep 824467 = 1236701) B1236701
theorem B5575877 : Blo 730325 5575877 := bstep (se 4 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 5575877 = 1045477) B1045477
theorem B824611 : Blo 730325 824611 := bstep (se 1 (by rfl) ⟨618458, by rfl⟩ : syracuseStep 824611 = 1236917) B1236917
theorem B1643921 : Blo 730325 1643921 := bstep (se 2 (by rfl) ⟨616470, by rfl⟩ : syracuseStep 1643921 = 1232941) B1232941
theorem B1643939 : Blo 730325 1643939 := bstep (se 1 (by rfl) ⟨1232954, by rfl⟩ : syracuseStep 1643939 = 2465909) B2465909
theorem B824755 : Blo 730325 824755 := bstep (se 1 (by rfl) ⟨618566, by rfl⟩ : syracuseStep 824755 = 1237133) B1237133
theorem B824899 : Blo 730325 824899 := bstep (se 1 (by rfl) ⟨618674, by rfl⟩ : syracuseStep 824899 = 1237349) B1237349
theorem B1644209 : Blo 730325 1644209 := bstep (se 2 (by rfl) ⟨616578, by rfl⟩ : syracuseStep 1644209 = 1233157) B1233157
theorem B1644227 : Blo 730325 1644227 := bstep (se 1 (by rfl) ⟨1233170, by rfl⟩ : syracuseStep 1644227 = 2466341) B2466341
theorem B825043 : Blo 730325 825043 := bstep (se 1 (by rfl) ⟨618782, by rfl⟩ : syracuseStep 825043 = 1237565) B1237565
theorem B3610403 : Blo 730325 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B3479395 : Blo 730325 3479395 := bstep (se 1 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 3479395 = 5219093) B5219093
theorem B825187 : Blo 730325 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B3348323 : Blo 730325 3348323 := bstep (se 1 (by rfl) ⟨2511242, by rfl⟩ : syracuseStep 3348323 = 5022485) B5022485
theorem B989057 : Blo 730325 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B4167557 : Blo 730325 4167557 := bstep (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) B781417
theorem B1644497 : Blo 730325 1644497 := bstep (se 2 (by rfl) ⟨616686, by rfl⟩ : syracuseStep 1644497 = 1233373) B1233373
theorem B1644515 : Blo 730325 1644515 := bstep (se 1 (by rfl) ⟨1233386, by rfl⟩ : syracuseStep 1644515 = 2466773) B2466773
theorem B825331 : Blo 730325 825331 := bstep (se 1 (by rfl) ⟨618998, by rfl⟩ : syracuseStep 825331 = 1237997) B1237997
theorem B825475 : Blo 730325 825475 := bstep (se 1 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 825475 = 1238213) B1238213
theorem B1644785 : Blo 730325 1644785 := bstep (se 2 (by rfl) ⟨616794, by rfl⟩ : syracuseStep 1644785 = 1233589) B1233589
theorem B1644803 : Blo 730325 1644803 := bstep (se 1 (by rfl) ⟨1233602, by rfl⟩ : syracuseStep 1644803 = 2467205) B2467205
theorem B825619 : Blo 730325 825619 := bstep (se 1 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 825619 = 1238429) B1238429
theorem B825763 : Blo 730325 825763 := bstep (se 1 (by rfl) ⟨619322, by rfl⟩ : syracuseStep 825763 = 1238645) B1238645
theorem B1645073 : Blo 730325 1645073 := bstep (se 2 (by rfl) ⟨616902, by rfl⟩ : syracuseStep 1645073 = 1233805) B1233805
theorem B1645091 : Blo 730325 1645091 := bstep (se 1 (by rfl) ⟨1233818, by rfl⟩ : syracuseStep 1645091 = 2467637) B2467637
theorem B3709475 : Blo 730325 3709475 := bstep (se 1 (by rfl) ⟨2782106, by rfl⟩ : syracuseStep 3709475 = 5564213) B5564213
theorem B825907 : Blo 730325 825907 := bstep (se 1 (by rfl) ⟨619430, by rfl⟩ : syracuseStep 825907 = 1238861) B1238861
theorem B826051 : Blo 730325 826051 := bstep (se 1 (by rfl) ⟨619538, by rfl⟩ : syracuseStep 826051 = 1239077) B1239077
theorem B1252049 : Blo 730325 1252049 := bstep (se 2 (by rfl) ⟨469518, by rfl⟩ : syracuseStep 1252049 = 939037) B939037
theorem B4004579 : Blo 730325 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1645361 : Blo 730325 1645361 := bstep (se 2 (by rfl) ⟨617010, by rfl⟩ : syracuseStep 1645361 = 1234021) B1234021
theorem B15276853 : Blo 730325 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B1645379 : Blo 730325 1645379 := bstep (se 1 (by rfl) ⟨1234034, by rfl⟩ : syracuseStep 1645379 = 2468069) B2468069
theorem B1055587 : Blo 730325 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B924691 : Blo 730325 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B1645649 : Blo 730325 1645649 := bstep (se 2 (by rfl) ⟨617118, by rfl⟩ : syracuseStep 1645649 = 1234237) B1234237
theorem B1645667 : Blo 730325 1645667 := bstep (se 1 (by rfl) ⟨1234250, by rfl⟩ : syracuseStep 1645667 = 2468501) B2468501
theorem B924787 : Blo 730325 924787 := bstep (se 1 (by rfl) ⟨693590, by rfl⟩ : syracuseStep 924787 = 1387181) B1387181
theorem B6265997 : Blo 730325 6265997 := bstep (se 3 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 6265997 = 2349749) B2349749
theorem B1186963 : Blo 730325 1186963 := bstep (se 1 (by rfl) ⟨890222, by rfl⟩ : syracuseStep 1186963 = 1780445) B1780445
theorem B3710285 : Blo 730325 3710285 := bstep (se 3 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 3710285 = 1391357) B1391357
theorem B1645937 : Blo 730325 1645937 := bstep (se 2 (by rfl) ⟨617226, by rfl⟩ : syracuseStep 1645937 = 1234453) B1234453
theorem B1645955 : Blo 730325 1645955 := bstep (se 1 (by rfl) ⟨1234466, by rfl⟩ : syracuseStep 1645955 = 2468933) B2468933
theorem B2006417 : Blo 730325 2006417 := bstep (se 2 (by rfl) ⟨752406, by rfl⟩ : syracuseStep 2006417 = 1504813) B1504813
theorem B2465261 : Blo 730325 2465261 := bstep (se 3 (by rfl) ⟨462236, by rfl⟩ : syracuseStep 2465261 = 924473) B924473
theorem B9379313 : Blo 730325 9379313 := bstep (se 2 (by rfl) ⟨3517242, by rfl⟩ : syracuseStep 9379313 = 7034485) B7034485
theorem B2465315 : Blo 730325 2465315 := bstep (se 1 (by rfl) ⟨1848986, by rfl⟩ : syracuseStep 2465315 = 3697973) B3697973
theorem B990787 : Blo 730325 990787 := bstep (se 1 (by rfl) ⟨743090, by rfl⟩ : syracuseStep 990787 = 1486181) B1486181
theorem B925283 : Blo 730325 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B3513955 : Blo 730325 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B1482371 : Blo 730325 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B3120781 : Blo 730325 3120781 := bstep (se 3 (by rfl) ⟨585146, by rfl⟩ : syracuseStep 3120781 = 1170293) B1170293
theorem B1646225 : Blo 730325 1646225 := bstep (se 2 (by rfl) ⟨617334, by rfl⟩ : syracuseStep 1646225 = 1234669) B1234669
theorem B1646243 : Blo 730325 1646243 := bstep (se 1 (by rfl) ⟨1234682, by rfl⟩ : syracuseStep 1646243 = 2469365) B2469365
theorem B2465585 : Blo 730325 2465585 := bstep (se 2 (by rfl) ⟨924594, by rfl⟩ : syracuseStep 2465585 = 1849189) B1849189
theorem B3514225 : Blo 730325 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B1908611 : Blo 730325 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B1646513 : Blo 730325 1646513 := bstep (se 2 (by rfl) ⟨617442, by rfl⟩ : syracuseStep 1646513 = 1234885) B1234885
theorem B1646531 : Blo 730325 1646531 := bstep (se 1 (by rfl) ⟨1234898, by rfl⟩ : syracuseStep 1646531 = 2469797) B2469797
theorem B1974221 : Blo 730325 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B1318915 : Blo 730325 1318915 := bstep (se 1 (by rfl) ⟨989186, by rfl⟩ : syracuseStep 1318915 = 1978373) B1978373
theorem B1187875 : Blo 730325 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B1646801 : Blo 730325 1646801 := bstep (se 2 (by rfl) ⟨617550, by rfl⟩ : syracuseStep 1646801 = 1235101) B1235101
theorem B1646819 : Blo 730325 1646819 := bstep (se 1 (by rfl) ⟨1235114, by rfl⟩ : syracuseStep 1646819 = 2470229) B2470229
theorem B925987 : Blo 730325 925987 := bstep (se 1 (by rfl) ⟨694490, by rfl⟩ : syracuseStep 925987 = 1388981) B1388981
theorem B2466125 : Blo 730325 2466125 := bstep (se 3 (by rfl) ⟨462398, by rfl⟩ : syracuseStep 2466125 = 924797) B924797
theorem B2466179 : Blo 730325 2466179 := bstep (se 1 (by rfl) ⟨1849634, by rfl⟩ : syracuseStep 2466179 = 3699269) B3699269
theorem B926083 : Blo 730325 926083 := bstep (se 1 (by rfl) ⟨694562, by rfl⟩ : syracuseStep 926083 = 1389125) B1389125
theorem B1647089 : Blo 730325 1647089 := bstep (se 2 (by rfl) ⟨617658, by rfl⟩ : syracuseStep 1647089 = 1235317) B1235317
theorem B1647107 : Blo 730325 1647107 := bstep (se 1 (by rfl) ⟨1235330, by rfl⟩ : syracuseStep 1647107 = 2470661) B2470661
theorem B1974851 : Blo 730325 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B1057411 : Blo 730325 1057411 := bstep (se 1 (by rfl) ⟨793058, by rfl⟩ : syracuseStep 1057411 = 1586117) B1586117
theorem B2466449 : Blo 730325 2466449 := bstep (se 2 (by rfl) ⟨924918, by rfl⟩ : syracuseStep 2466449 = 1849837) B1849837
theorem B3121841 : Blo 730325 3121841 := bstep (se 2 (by rfl) ⟨1170690, by rfl⟩ : syracuseStep 3121841 = 2341381) B2341381
theorem B4694705 : Blo 730325 4694705 := bstep (se 2 (by rfl) ⟨1760514, by rfl⟩ : syracuseStep 4694705 = 3521029) B3521029
theorem B1057475 : Blo 730325 1057475 := bstep (se 1 (by rfl) ⟨793106, by rfl⟩ : syracuseStep 1057475 = 1586213) B1586213
theorem B1647377 : Blo 730325 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B1647395 : Blo 730325 1647395 := bstep (se 1 (by rfl) ⟨1235546, by rfl⟩ : syracuseStep 1647395 = 2471093) B2471093
theorem B1254179 : Blo 730325 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B926579 : Blo 730325 926579 := bstep (se 1 (by rfl) ⟨694934, by rfl⟩ : syracuseStep 926579 = 1389869) B1389869
theorem B1647665 : Blo 730325 1647665 := bstep (se 2 (by rfl) ⟨617874, by rfl⟩ : syracuseStep 1647665 = 1235749) B1235749
theorem B1647683 : Blo 730325 1647683 := bstep (se 1 (by rfl) ⟨1235762, by rfl⟩ : syracuseStep 1647683 = 2471525) B2471525
theorem B2466989 : Blo 730325 2466989 := bstep (se 3 (by rfl) ⟨462560, by rfl⟩ : syracuseStep 2466989 = 925121) B925121
theorem B8332469 : Blo 730325 8332469 := bstep (se 5 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 8332469 = 781169) B781169
theorem B730339 : Blo 730325 730339 := bstep (se 1 (by rfl) ⟨547754, by rfl⟩ : syracuseStep 730339 = 1095509) B1095509
theorem B2467043 : Blo 730325 2467043 := bstep (se 1 (by rfl) ⟨1850282, by rfl⟩ : syracuseStep 2467043 = 3700565) B3700565
theorem B730355 : Blo 730325 730355 := bstep (se 1 (by rfl) ⟨547766, by rfl⟩ : syracuseStep 730355 = 1095533) B1095533
theorem B730371 : Blo 730325 730371 := bstep (se 1 (by rfl) ⟨547778, by rfl⟩ : syracuseStep 730371 = 1095557) B1095557
theorem B730387 : Blo 730325 730387 := bstep (se 1 (by rfl) ⟨547790, by rfl⟩ : syracuseStep 730387 = 1095581) B1095581
theorem B730403 : Blo 730325 730403 := bstep (se 1 (by rfl) ⟨547802, by rfl⟩ : syracuseStep 730403 = 1095605) B1095605
theorem B730419 : Blo 730325 730419 := bstep (se 1 (by rfl) ⟨547814, by rfl⟩ : syracuseStep 730419 = 1095629) B1095629
theorem B730435 : Blo 730325 730435 := bstep (se 1 (by rfl) ⟨547826, by rfl⟩ : syracuseStep 730435 = 1095653) B1095653
theorem B1647953 : Blo 730325 1647953 := bstep (se 2 (by rfl) ⟨617982, by rfl⟩ : syracuseStep 1647953 = 1235965) B1235965
theorem B730451 : Blo 730325 730451 := bstep (se 1 (by rfl) ⟨547838, by rfl⟩ : syracuseStep 730451 = 1095677) B1095677
theorem B730467 : Blo 730325 730467 := bstep (se 1 (by rfl) ⟨547850, by rfl⟩ : syracuseStep 730467 = 1095701) B1095701
theorem B1647971 : Blo 730325 1647971 := bstep (se 1 (by rfl) ⟨1235978, by rfl⟩ : syracuseStep 1647971 = 2471957) B2471957
theorem B730483 : Blo 730325 730483 := bstep (se 1 (by rfl) ⟨547862, by rfl⟩ : syracuseStep 730483 = 1095725) B1095725
theorem B730499 : Blo 730325 730499 := bstep (se 1 (by rfl) ⟨547874, by rfl⟩ : syracuseStep 730499 = 1095749) B1095749
theorem B730515 : Blo 730325 730515 := bstep (se 1 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 730515 = 1095773) B1095773
theorem B730531 : Blo 730325 730531 := bstep (se 1 (by rfl) ⟨547898, by rfl⟩ : syracuseStep 730531 = 1095797) B1095797
theorem B730547 : Blo 730325 730547 := bstep (se 1 (by rfl) ⟨547910, by rfl⟩ : syracuseStep 730547 = 1095821) B1095821
theorem B730563 : Blo 730325 730563 := bstep (se 1 (by rfl) ⟨547922, by rfl⟩ : syracuseStep 730563 = 1095845) B1095845
theorem B730579 : Blo 730325 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B730595 : Blo 730325 730595 := bstep (se 1 (by rfl) ⟨547946, by rfl⟩ : syracuseStep 730595 = 1095893) B1095893
theorem B2467313 : Blo 730325 2467313 := bstep (se 2 (by rfl) ⟨925242, by rfl⟩ : syracuseStep 2467313 = 1850485) B1850485
theorem B730611 : Blo 730325 730611 := bstep (se 1 (by rfl) ⟨547958, by rfl⟩ : syracuseStep 730611 = 1095917) B1095917
theorem B730627 : Blo 730325 730627 := bstep (se 1 (by rfl) ⟨547970, by rfl⟩ : syracuseStep 730627 = 1095941) B1095941
theorem B730643 : Blo 730325 730643 := bstep (se 1 (by rfl) ⟨547982, by rfl⟩ : syracuseStep 730643 = 1095965) B1095965
theorem B730659 : Blo 730325 730659 := bstep (se 1 (by rfl) ⟨547994, by rfl⟩ : syracuseStep 730659 = 1095989) B1095989
theorem B730675 : Blo 730325 730675 := bstep (se 1 (by rfl) ⟨548006, by rfl⟩ : syracuseStep 730675 = 1096013) B1096013
theorem B927283 : Blo 730325 927283 := bstep (se 1 (by rfl) ⟨695462, by rfl⟩ : syracuseStep 927283 = 1390925) B1390925
theorem B730691 : Blo 730325 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B730707 : Blo 730325 730707 := bstep (se 1 (by rfl) ⟨548030, by rfl⟩ : syracuseStep 730707 = 1096061) B1096061
theorem B730723 : Blo 730325 730723 := bstep (se 1 (by rfl) ⟨548042, by rfl⟩ : syracuseStep 730723 = 1096085) B1096085
theorem B1648241 : Blo 730325 1648241 := bstep (se 2 (by rfl) ⟨618090, by rfl⟩ : syracuseStep 1648241 = 1236181) B1236181
theorem B730739 : Blo 730325 730739 := bstep (se 1 (by rfl) ⟨548054, by rfl⟩ : syracuseStep 730739 = 1096109) B1096109
theorem B730755 : Blo 730325 730755 := bstep (se 1 (by rfl) ⟨548066, by rfl⟩ : syracuseStep 730755 = 1096133) B1096133
theorem B1648259 : Blo 730325 1648259 := bstep (se 1 (by rfl) ⟨1236194, by rfl⟩ : syracuseStep 1648259 = 2472389) B2472389
theorem B730771 : Blo 730325 730771 := bstep (se 1 (by rfl) ⟨548078, by rfl⟩ : syracuseStep 730771 = 1096157) B1096157
theorem B927379 : Blo 730325 927379 := bstep (se 1 (by rfl) ⟨695534, by rfl⟩ : syracuseStep 927379 = 1391069) B1391069
theorem B730787 : Blo 730325 730787 := bstep (se 1 (by rfl) ⟨548090, by rfl⟩ : syracuseStep 730787 = 1096181) B1096181
theorem B730803 : Blo 730325 730803 := bstep (se 1 (by rfl) ⟨548102, by rfl⟩ : syracuseStep 730803 = 1096205) B1096205
theorem B730819 : Blo 730325 730819 := bstep (se 1 (by rfl) ⟨548114, by rfl⟩ : syracuseStep 730819 = 1096229) B1096229
theorem B730835 : Blo 730325 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B730851 : Blo 730325 730851 := bstep (se 1 (by rfl) ⟨548138, by rfl⟩ : syracuseStep 730851 = 1096277) B1096277
theorem B730867 : Blo 730325 730867 := bstep (se 1 (by rfl) ⟨548150, by rfl⟩ : syracuseStep 730867 = 1096301) B1096301
theorem B730883 : Blo 730325 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B730899 : Blo 730325 730899 := bstep (se 1 (by rfl) ⟨548174, by rfl⟩ : syracuseStep 730899 = 1096349) B1096349
theorem B730915 : Blo 730325 730915 := bstep (se 1 (by rfl) ⟨548186, by rfl⟩ : syracuseStep 730915 = 1096373) B1096373
theorem B730931 : Blo 730325 730931 := bstep (se 1 (by rfl) ⟨548198, by rfl⟩ : syracuseStep 730931 = 1096397) B1096397
theorem B730947 : Blo 730325 730947 := bstep (se 1 (by rfl) ⟨548210, by rfl⟩ : syracuseStep 730947 = 1096421) B1096421
theorem B730963 : Blo 730325 730963 := bstep (se 1 (by rfl) ⟨548222, by rfl⟩ : syracuseStep 730963 = 1096445) B1096445
theorem B730979 : Blo 730325 730979 := bstep (se 1 (by rfl) ⟨548234, by rfl⟩ : syracuseStep 730979 = 1096469) B1096469
theorem B730995 : Blo 730325 730995 := bstep (se 1 (by rfl) ⟨548246, by rfl⟩ : syracuseStep 730995 = 1096493) B1096493
theorem B731011 : Blo 730325 731011 := bstep (se 1 (by rfl) ⟨548258, by rfl⟩ : syracuseStep 731011 = 1096517) B1096517
theorem B1484689 : Blo 730325 1484689 := bstep (se 2 (by rfl) ⟨556758, by rfl⟩ : syracuseStep 1484689 = 1113517) B1113517
theorem B1648529 : Blo 730325 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B731027 : Blo 730325 731027 := bstep (se 1 (by rfl) ⟨548270, by rfl⟩ : syracuseStep 731027 = 1096541) B1096541
theorem B731043 : Blo 730325 731043 := bstep (se 1 (by rfl) ⟨548282, by rfl⟩ : syracuseStep 731043 = 1096565) B1096565
theorem B1648547 : Blo 730325 1648547 := bstep (se 1 (by rfl) ⟨1236410, by rfl⟩ : syracuseStep 1648547 = 2472821) B2472821
theorem B731059 : Blo 730325 731059 := bstep (se 1 (by rfl) ⟨548294, by rfl⟩ : syracuseStep 731059 = 1096589) B1096589
theorem B731075 : Blo 730325 731075 := bstep (se 1 (by rfl) ⟨548306, by rfl⟩ : syracuseStep 731075 = 1096613) B1096613
theorem B731091 : Blo 730325 731091 := bstep (se 1 (by rfl) ⟨548318, by rfl⟩ : syracuseStep 731091 = 1096637) B1096637
theorem B731107 : Blo 730325 731107 := bstep (se 1 (by rfl) ⟨548330, by rfl⟩ : syracuseStep 731107 = 1096661) B1096661
theorem B731123 : Blo 730325 731123 := bstep (se 1 (by rfl) ⟨548342, by rfl⟩ : syracuseStep 731123 = 1096685) B1096685
theorem B731139 : Blo 730325 731139 := bstep (se 1 (by rfl) ⟨548354, by rfl⟩ : syracuseStep 731139 = 1096709) B1096709
theorem B2467853 : Blo 730325 2467853 := bstep (se 3 (by rfl) ⟨462722, by rfl⟩ : syracuseStep 2467853 = 925445) B925445
theorem B731155 : Blo 730325 731155 := bstep (se 1 (by rfl) ⟨548366, by rfl⟩ : syracuseStep 731155 = 1096733) B1096733
theorem B731171 : Blo 730325 731171 := bstep (se 1 (by rfl) ⟨548378, by rfl⟩ : syracuseStep 731171 = 1096757) B1096757
theorem B731187 : Blo 730325 731187 := bstep (se 1 (by rfl) ⟨548390, by rfl⟩ : syracuseStep 731187 = 1096781) B1096781
theorem B731203 : Blo 730325 731203 := bstep (se 1 (by rfl) ⟨548402, by rfl⟩ : syracuseStep 731203 = 1096805) B1096805
theorem B2467907 : Blo 730325 2467907 := bstep (se 1 (by rfl) ⟨1850930, by rfl⟩ : syracuseStep 2467907 = 3701861) B3701861
theorem B731219 : Blo 730325 731219 := bstep (se 1 (by rfl) ⟨548414, by rfl⟩ : syracuseStep 731219 = 1096829) B1096829
theorem B731235 : Blo 730325 731235 := bstep (se 1 (by rfl) ⟨548426, by rfl⟩ : syracuseStep 731235 = 1096853) B1096853
theorem B731251 : Blo 730325 731251 := bstep (se 1 (by rfl) ⟨548438, by rfl⟩ : syracuseStep 731251 = 1096877) B1096877
theorem B731267 : Blo 730325 731267 := bstep (se 1 (by rfl) ⟨548450, by rfl⟩ : syracuseStep 731267 = 1096901) B1096901
theorem B927875 : Blo 730325 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B731283 : Blo 730325 731283 := bstep (se 1 (by rfl) ⟨548462, by rfl⟩ : syracuseStep 731283 = 1096925) B1096925
theorem B731299 : Blo 730325 731299 := bstep (se 1 (by rfl) ⟨548474, by rfl⟩ : syracuseStep 731299 = 1096949) B1096949
theorem B1648817 : Blo 730325 1648817 := bstep (se 2 (by rfl) ⟨618306, by rfl⟩ : syracuseStep 1648817 = 1236613) B1236613
theorem B731315 : Blo 730325 731315 := bstep (se 1 (by rfl) ⟨548486, by rfl⟩ : syracuseStep 731315 = 1096973) B1096973
theorem B3713201 : Blo 730325 3713201 := bstep (se 2 (by rfl) ⟨1392450, by rfl⟩ : syracuseStep 3713201 = 2784901) B2784901
theorem B731331 : Blo 730325 731331 := bstep (se 1 (by rfl) ⟨548498, by rfl⟩ : syracuseStep 731331 = 1096997) B1096997
theorem B1648835 : Blo 730325 1648835 := bstep (se 1 (by rfl) ⟨1236626, by rfl⟩ : syracuseStep 1648835 = 2473253) B2473253
theorem B8890565 : Blo 730325 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B731347 : Blo 730325 731347 := bstep (se 1 (by rfl) ⟨548510, by rfl⟩ : syracuseStep 731347 = 1097021) B1097021
theorem B731363 : Blo 730325 731363 := bstep (se 1 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 731363 = 1097045) B1097045
theorem B731379 : Blo 730325 731379 := bstep (se 1 (by rfl) ⟨548534, by rfl⟩ : syracuseStep 731379 = 1097069) B1097069
theorem B1976579 : Blo 730325 1976579 := bstep (se 1 (by rfl) ⟨1482434, by rfl⟩ : syracuseStep 1976579 = 2964869) B2964869
theorem B731395 : Blo 730325 731395 := bstep (se 1 (by rfl) ⟨548546, by rfl⟩ : syracuseStep 731395 = 1097093) B1097093
theorem B731411 : Blo 730325 731411 := bstep (se 1 (by rfl) ⟨548558, by rfl⟩ : syracuseStep 731411 = 1097117) B1097117
theorem B731427 : Blo 730325 731427 := bstep (se 1 (by rfl) ⟨548570, by rfl⟩ : syracuseStep 731427 = 1097141) B1097141
theorem B731443 : Blo 730325 731443 := bstep (se 1 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 731443 = 1097165) B1097165
theorem B731459 : Blo 730325 731459 := bstep (se 1 (by rfl) ⟨548594, by rfl⟩ : syracuseStep 731459 = 1097189) B1097189
theorem B2468177 : Blo 730325 2468177 := bstep (se 2 (by rfl) ⟨925566, by rfl⟩ : syracuseStep 2468177 = 1851133) B1851133
theorem B731475 : Blo 730325 731475 := bstep (se 1 (by rfl) ⟨548606, by rfl⟩ : syracuseStep 731475 = 1097213) B1097213
theorem B731491 : Blo 730325 731491 := bstep (se 1 (by rfl) ⟨548618, by rfl⟩ : syracuseStep 731491 = 1097237) B1097237
theorem B731507 : Blo 730325 731507 := bstep (se 1 (by rfl) ⟨548630, by rfl⟩ : syracuseStep 731507 = 1097261) B1097261
theorem B731523 : Blo 730325 731523 := bstep (se 1 (by rfl) ⟨548642, by rfl⟩ : syracuseStep 731523 = 1097285) B1097285
theorem B731539 : Blo 730325 731539 := bstep (se 1 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 731539 = 1097309) B1097309
theorem B731555 : Blo 730325 731555 := bstep (se 1 (by rfl) ⟨548666, by rfl⟩ : syracuseStep 731555 = 1097333) B1097333
theorem B731571 : Blo 730325 731571 := bstep (se 1 (by rfl) ⟨548678, by rfl⟩ : syracuseStep 731571 = 1097357) B1097357
theorem B731587 : Blo 730325 731587 := bstep (se 1 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 731587 = 1097381) B1097381
theorem B1649105 : Blo 730325 1649105 := bstep (se 2 (by rfl) ⟨618414, by rfl⟩ : syracuseStep 1649105 = 1236829) B1236829
theorem B731603 : Blo 730325 731603 := bstep (se 1 (by rfl) ⟨548702, by rfl⟩ : syracuseStep 731603 = 1097405) B1097405
theorem B731619 : Blo 730325 731619 := bstep (se 1 (by rfl) ⟨548714, by rfl⟩ : syracuseStep 731619 = 1097429) B1097429
theorem B1649123 : Blo 730325 1649123 := bstep (se 1 (by rfl) ⟨1236842, by rfl⟩ : syracuseStep 1649123 = 2473685) B2473685
theorem B731635 : Blo 730325 731635 := bstep (se 1 (by rfl) ⟨548726, by rfl⟩ : syracuseStep 731635 = 1097453) B1097453
theorem B731651 : Blo 730325 731651 := bstep (se 1 (by rfl) ⟨548738, by rfl⟩ : syracuseStep 731651 = 1097477) B1097477
theorem B731667 : Blo 730325 731667 := bstep (se 1 (by rfl) ⟨548750, by rfl⟩ : syracuseStep 731667 = 1097501) B1097501
theorem B731683 : Blo 730325 731683 := bstep (se 1 (by rfl) ⟨548762, by rfl⟩ : syracuseStep 731683 = 1097525) B1097525
theorem B4237859 : Blo 730325 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B731699 : Blo 730325 731699 := bstep (se 1 (by rfl) ⟨548774, by rfl⟩ : syracuseStep 731699 = 1097549) B1097549
theorem B731715 : Blo 730325 731715 := bstep (se 1 (by rfl) ⟨548786, by rfl⟩ : syracuseStep 731715 = 1097573) B1097573
theorem B731731 : Blo 730325 731731 := bstep (se 1 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 731731 = 1097597) B1097597
theorem B731747 : Blo 730325 731747 := bstep (se 1 (by rfl) ⟨548810, by rfl⟩ : syracuseStep 731747 = 1097621) B1097621
theorem B731763 : Blo 730325 731763 := bstep (se 1 (by rfl) ⟨548822, by rfl⟩ : syracuseStep 731763 = 1097645) B1097645
theorem B731779 : Blo 730325 731779 := bstep (se 1 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 731779 = 1097669) B1097669
theorem B731795 : Blo 730325 731795 := bstep (se 1 (by rfl) ⟨548846, by rfl⟩ : syracuseStep 731795 = 1097693) B1097693
theorem B731811 : Blo 730325 731811 := bstep (se 1 (by rfl) ⟨548858, by rfl⟩ : syracuseStep 731811 = 1097717) B1097717
theorem B3517091 : Blo 730325 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B731827 : Blo 730325 731827 := bstep (se 1 (by rfl) ⟨548870, by rfl⟩ : syracuseStep 731827 = 1097741) B1097741
theorem B731843 : Blo 730325 731843 := bstep (se 1 (by rfl) ⟨548882, by rfl⟩ : syracuseStep 731843 = 1097765) B1097765
theorem B731859 : Blo 730325 731859 := bstep (se 1 (by rfl) ⟨548894, by rfl⟩ : syracuseStep 731859 = 1097789) B1097789
theorem B731875 : Blo 730325 731875 := bstep (se 1 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 731875 = 1097813) B1097813
theorem B1649393 : Blo 730325 1649393 := bstep (se 2 (by rfl) ⟨618522, by rfl⟩ : syracuseStep 1649393 = 1237045) B1237045
theorem B731891 : Blo 730325 731891 := bstep (se 1 (by rfl) ⟨548918, by rfl⟩ : syracuseStep 731891 = 1097837) B1097837
theorem B731907 : Blo 730325 731907 := bstep (se 1 (by rfl) ⟨548930, by rfl⟩ : syracuseStep 731907 = 1097861) B1097861
theorem B1649411 : Blo 730325 1649411 := bstep (se 1 (by rfl) ⟨1237058, by rfl⟩ : syracuseStep 1649411 = 2474117) B2474117
theorem B731923 : Blo 730325 731923 := bstep (se 1 (by rfl) ⟨548942, by rfl⟩ : syracuseStep 731923 = 1097885) B1097885
theorem B731939 : Blo 730325 731939 := bstep (se 1 (by rfl) ⟨548954, by rfl⟩ : syracuseStep 731939 = 1097909) B1097909
theorem B1878833 : Blo 730325 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B731955 : Blo 730325 731955 := bstep (se 1 (by rfl) ⟨548966, by rfl⟩ : syracuseStep 731955 = 1097933) B1097933
theorem B731971 : Blo 730325 731971 := bstep (se 1 (by rfl) ⟨548978, by rfl⟩ : syracuseStep 731971 = 1097957) B1097957
theorem B928579 : Blo 730325 928579 := bstep (se 1 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 928579 = 1392869) B1392869
theorem B731987 : Blo 730325 731987 := bstep (se 1 (by rfl) ⟨548990, by rfl⟩ : syracuseStep 731987 = 1097981) B1097981
theorem B1387363 : Blo 730325 1387363 := bstep (se 1 (by rfl) ⟨1040522, by rfl⟩ : syracuseStep 1387363 = 2081045) B2081045
theorem B732003 : Blo 730325 732003 := bstep (se 1 (by rfl) ⟨549002, by rfl⟩ : syracuseStep 732003 = 1098005) B1098005
theorem B2468717 : Blo 730325 2468717 := bstep (se 3 (by rfl) ⟨462884, by rfl⟩ : syracuseStep 2468717 = 925769) B925769
theorem B732019 : Blo 730325 732019 := bstep (se 1 (by rfl) ⟨549014, by rfl⟩ : syracuseStep 732019 = 1098029) B1098029
theorem B732035 : Blo 730325 732035 := bstep (se 1 (by rfl) ⟨549026, by rfl⟩ : syracuseStep 732035 = 1098053) B1098053
theorem B732051 : Blo 730325 732051 := bstep (se 1 (by rfl) ⟨549038, by rfl⟩ : syracuseStep 732051 = 1098077) B1098077
theorem B2468771 : Blo 730325 2468771 := bstep (se 1 (by rfl) ⟨1851578, by rfl⟩ : syracuseStep 2468771 = 3703157) B3703157
theorem B732067 : Blo 730325 732067 := bstep (se 1 (by rfl) ⟨549050, by rfl⟩ : syracuseStep 732067 = 1098101) B1098101
theorem B928675 : Blo 730325 928675 := bstep (se 1 (by rfl) ⟨696506, by rfl⟩ : syracuseStep 928675 = 1393013) B1393013
theorem B732083 : Blo 730325 732083 := bstep (se 1 (by rfl) ⟨549062, by rfl⟩ : syracuseStep 732083 = 1098125) B1098125
theorem B732099 : Blo 730325 732099 := bstep (se 1 (by rfl) ⟨549074, by rfl⟩ : syracuseStep 732099 = 1098149) B1098149
theorem B732115 : Blo 730325 732115 := bstep (se 1 (by rfl) ⟨549086, by rfl⟩ : syracuseStep 732115 = 1098173) B1098173
theorem B732131 : Blo 730325 732131 := bstep (se 1 (by rfl) ⟨549098, by rfl⟩ : syracuseStep 732131 = 1098197) B1098197
theorem B732147 : Blo 730325 732147 := bstep (se 1 (by rfl) ⟨549110, by rfl⟩ : syracuseStep 732147 = 1098221) B1098221
theorem B1387523 : Blo 730325 1387523 := bstep (se 1 (by rfl) ⟨1040642, by rfl⟩ : syracuseStep 1387523 = 2081285) B2081285
theorem B732163 : Blo 730325 732163 := bstep (se 1 (by rfl) ⟨549122, by rfl⟩ : syracuseStep 732163 = 1098245) B1098245
theorem B1649681 : Blo 730325 1649681 := bstep (se 2 (by rfl) ⟨618630, by rfl⟩ : syracuseStep 1649681 = 1237261) B1237261
theorem B732179 : Blo 730325 732179 := bstep (se 1 (by rfl) ⟨549134, by rfl⟩ : syracuseStep 732179 = 1098269) B1098269
theorem B732195 : Blo 730325 732195 := bstep (se 1 (by rfl) ⟨549146, by rfl⟩ : syracuseStep 732195 = 1098293) B1098293
theorem B1649699 : Blo 730325 1649699 := bstep (se 1 (by rfl) ⟨1237274, by rfl⟩ : syracuseStep 1649699 = 2474549) B2474549
theorem B732211 : Blo 730325 732211 := bstep (se 1 (by rfl) ⟨549158, by rfl⟩ : syracuseStep 732211 = 1098317) B1098317
theorem B1190963 : Blo 730325 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B732227 : Blo 730325 732227 := bstep (se 1 (by rfl) ⟨549170, by rfl⟩ : syracuseStep 732227 = 1098341) B1098341
theorem B732243 : Blo 730325 732243 := bstep (se 1 (by rfl) ⟨549182, by rfl⟩ : syracuseStep 732243 = 1098365) B1098365
theorem B732259 : Blo 730325 732259 := bstep (se 1 (by rfl) ⟨549194, by rfl⟩ : syracuseStep 732259 = 1098389) B1098389
theorem B732275 : Blo 730325 732275 := bstep (se 1 (by rfl) ⟨549206, by rfl⟩ : syracuseStep 732275 = 1098413) B1098413
theorem B732291 : Blo 730325 732291 := bstep (se 1 (by rfl) ⟨549218, by rfl⟩ : syracuseStep 732291 = 1098437) B1098437
theorem B732307 : Blo 730325 732307 := bstep (se 1 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 732307 = 1098461) B1098461
theorem B732323 : Blo 730325 732323 := bstep (se 1 (by rfl) ⟨549242, by rfl⟩ : syracuseStep 732323 = 1098485) B1098485
theorem B2469041 : Blo 730325 2469041 := bstep (se 2 (by rfl) ⟨925890, by rfl⟩ : syracuseStep 2469041 = 1851781) B1851781
theorem B732339 : Blo 730325 732339 := bstep (se 1 (by rfl) ⟨549254, by rfl⟩ : syracuseStep 732339 = 1098509) B1098509
theorem B732355 : Blo 730325 732355 := bstep (se 1 (by rfl) ⟨549266, by rfl⟩ : syracuseStep 732355 = 1098533) B1098533
theorem B732371 : Blo 730325 732371 := bstep (se 1 (by rfl) ⟨549278, by rfl⟩ : syracuseStep 732371 = 1098557) B1098557
theorem B732387 : Blo 730325 732387 := bstep (se 1 (by rfl) ⟨549290, by rfl⟩ : syracuseStep 732387 = 1098581) B1098581
theorem B732403 : Blo 730325 732403 := bstep (se 1 (by rfl) ⟨549302, by rfl⟩ : syracuseStep 732403 = 1098605) B1098605
theorem B732419 : Blo 730325 732419 := bstep (se 1 (by rfl) ⟨549314, by rfl⟩ : syracuseStep 732419 = 1098629) B1098629
theorem B732435 : Blo 730325 732435 := bstep (se 1 (by rfl) ⟨549326, by rfl⟩ : syracuseStep 732435 = 1098653) B1098653
theorem B732451 : Blo 730325 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B1649969 : Blo 730325 1649969 := bstep (se 2 (by rfl) ⟨618738, by rfl⟩ : syracuseStep 1649969 = 1237477) B1237477
theorem B732467 : Blo 730325 732467 := bstep (se 1 (by rfl) ⟨549350, by rfl⟩ : syracuseStep 732467 = 1098701) B1098701
theorem B732483 : Blo 730325 732483 := bstep (se 1 (by rfl) ⟨549362, by rfl⟩ : syracuseStep 732483 = 1098725) B1098725
theorem B1649987 : Blo 730325 1649987 := bstep (se 1 (by rfl) ⟨1237490, by rfl⟩ : syracuseStep 1649987 = 2474981) B2474981
theorem B732499 : Blo 730325 732499 := bstep (se 1 (by rfl) ⟨549374, by rfl⟩ : syracuseStep 732499 = 1098749) B1098749
theorem B732515 : Blo 730325 732515 := bstep (se 1 (by rfl) ⟨549386, by rfl⟩ : syracuseStep 732515 = 1098773) B1098773
theorem B732531 : Blo 730325 732531 := bstep (se 1 (by rfl) ⟨549398, by rfl⟩ : syracuseStep 732531 = 1098797) B1098797
theorem B732547 : Blo 730325 732547 := bstep (se 1 (by rfl) ⟨549410, by rfl⟩ : syracuseStep 732547 = 1098821) B1098821
theorem B732563 : Blo 730325 732563 := bstep (se 1 (by rfl) ⟨549422, by rfl⟩ : syracuseStep 732563 = 1098845) B1098845
theorem B929171 : Blo 730325 929171 := bstep (se 1 (by rfl) ⟨696878, by rfl⟩ : syracuseStep 929171 = 1393757) B1393757
theorem B732579 : Blo 730325 732579 := bstep (se 1 (by rfl) ⟨549434, by rfl⟩ : syracuseStep 732579 = 1098869) B1098869
theorem B732595 : Blo 730325 732595 := bstep (se 1 (by rfl) ⟨549446, by rfl⟩ : syracuseStep 732595 = 1098893) B1098893
theorem B732611 : Blo 730325 732611 := bstep (se 1 (by rfl) ⟨549458, by rfl⟩ : syracuseStep 732611 = 1098917) B1098917
theorem B10038725 : Blo 730325 10038725 := bstep (se 4 (by rfl) ⟨941130, by rfl⟩ : syracuseStep 10038725 = 1882261) B1882261
theorem B732627 : Blo 730325 732627 := bstep (se 1 (by rfl) ⟨549470, by rfl⟩ : syracuseStep 732627 = 1098941) B1098941
theorem B732643 : Blo 730325 732643 := bstep (se 1 (by rfl) ⟨549482, by rfl⟩ : syracuseStep 732643 = 1098965) B1098965
theorem B732659 : Blo 730325 732659 := bstep (se 1 (by rfl) ⟨549494, by rfl⟩ : syracuseStep 732659 = 1098989) B1098989
theorem B732675 : Blo 730325 732675 := bstep (se 1 (by rfl) ⟨549506, by rfl⟩ : syracuseStep 732675 = 1099013) B1099013
theorem B732691 : Blo 730325 732691 := bstep (se 1 (by rfl) ⟨549518, by rfl⟩ : syracuseStep 732691 = 1099037) B1099037
theorem B732707 : Blo 730325 732707 := bstep (se 1 (by rfl) ⟨549530, by rfl⟩ : syracuseStep 732707 = 1099061) B1099061
theorem B732723 : Blo 730325 732723 := bstep (se 1 (by rfl) ⟨549542, by rfl⟩ : syracuseStep 732723 = 1099085) B1099085
theorem B732739 : Blo 730325 732739 := bstep (se 1 (by rfl) ⟨549554, by rfl⟩ : syracuseStep 732739 = 1099109) B1099109
theorem B1322563 : Blo 730325 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B3124813 : Blo 730325 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B3518029 : Blo 730325 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B4173389 : Blo 730325 4173389 := bstep (se 3 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 4173389 = 1565021) B1565021
theorem B1650257 : Blo 730325 1650257 := bstep (se 2 (by rfl) ⟨618846, by rfl⟩ : syracuseStep 1650257 = 1237693) B1237693
theorem B732755 : Blo 730325 732755 := bstep (se 1 (by rfl) ⟨549566, by rfl⟩ : syracuseStep 732755 = 1099133) B1099133
theorem B732771 : Blo 730325 732771 := bstep (se 1 (by rfl) ⟨549578, by rfl⟩ : syracuseStep 732771 = 1099157) B1099157
theorem B1650275 : Blo 730325 1650275 := bstep (se 1 (by rfl) ⟨1237706, by rfl⟩ : syracuseStep 1650275 = 2475413) B2475413
theorem B3714659 : Blo 730325 3714659 := bstep (se 1 (by rfl) ⟨2785994, by rfl⟩ : syracuseStep 3714659 = 5571989) B5571989
theorem B732787 : Blo 730325 732787 := bstep (se 1 (by rfl) ⟨549590, by rfl⟩ : syracuseStep 732787 = 1099181) B1099181
theorem B732803 : Blo 730325 732803 := bstep (se 1 (by rfl) ⟨549602, by rfl⟩ : syracuseStep 732803 = 1099205) B1099205
theorem B732819 : Blo 730325 732819 := bstep (se 1 (by rfl) ⟨549614, by rfl⟩ : syracuseStep 732819 = 1099229) B1099229
theorem B732835 : Blo 730325 732835 := bstep (se 1 (by rfl) ⟨549626, by rfl⟩ : syracuseStep 732835 = 1099253) B1099253
theorem B732851 : Blo 730325 732851 := bstep (se 1 (by rfl) ⟨549638, by rfl⟩ : syracuseStep 732851 = 1099277) B1099277
theorem B732867 : Blo 730325 732867 := bstep (se 1 (by rfl) ⟨549650, by rfl⟩ : syracuseStep 732867 = 1099301) B1099301
theorem B2469581 : Blo 730325 2469581 := bstep (se 3 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 2469581 = 926093) B926093
theorem B732883 : Blo 730325 732883 := bstep (se 1 (by rfl) ⟨549662, by rfl⟩ : syracuseStep 732883 = 1099325) B1099325
theorem B732899 : Blo 730325 732899 := bstep (se 1 (by rfl) ⟨549674, by rfl⟩ : syracuseStep 732899 = 1099349) B1099349
theorem B1191665 : Blo 730325 1191665 := bstep (se 2 (by rfl) ⟨446874, by rfl⟩ : syracuseStep 1191665 = 893749) B893749
theorem B732915 : Blo 730325 732915 := bstep (se 1 (by rfl) ⟨549686, by rfl⟩ : syracuseStep 732915 = 1099373) B1099373
theorem B2469635 : Blo 730325 2469635 := bstep (se 1 (by rfl) ⟨1852226, by rfl⟩ : syracuseStep 2469635 = 3704453) B3704453
theorem B732931 : Blo 730325 732931 := bstep (se 1 (by rfl) ⟨549698, by rfl⟩ : syracuseStep 732931 = 1099397) B1099397
theorem B732947 : Blo 730325 732947 := bstep (se 1 (by rfl) ⟨549710, by rfl⟩ : syracuseStep 732947 = 1099421) B1099421
theorem B732963 : Blo 730325 732963 := bstep (se 1 (by rfl) ⟨549722, by rfl⟩ : syracuseStep 732963 = 1099445) B1099445
theorem B732979 : Blo 730325 732979 := bstep (se 1 (by rfl) ⟨549734, by rfl⟩ : syracuseStep 732979 = 1099469) B1099469
theorem B732995 : Blo 730325 732995 := bstep (se 1 (by rfl) ⟨549746, by rfl⟩ : syracuseStep 732995 = 1099493) B1099493
theorem B733011 : Blo 730325 733011 := bstep (se 1 (by rfl) ⟨549758, by rfl⟩ : syracuseStep 733011 = 1099517) B1099517
theorem B733027 : Blo 730325 733027 := bstep (se 1 (by rfl) ⟨549770, by rfl⟩ : syracuseStep 733027 = 1099541) B1099541
theorem B1650545 : Blo 730325 1650545 := bstep (se 2 (by rfl) ⟨618954, by rfl⟩ : syracuseStep 1650545 = 1237909) B1237909
theorem B733043 : Blo 730325 733043 := bstep (se 1 (by rfl) ⟨549782, by rfl⟩ : syracuseStep 733043 = 1099565) B1099565
theorem B1191809 : Blo 730325 1191809 := bstep (se 2 (by rfl) ⟨446928, by rfl⟩ : syracuseStep 1191809 = 893857) B893857
theorem B733059 : Blo 730325 733059 := bstep (se 1 (by rfl) ⟨549794, by rfl⟩ : syracuseStep 733059 = 1099589) B1099589
theorem B1650563 : Blo 730325 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B28225421 : Blo 730325 28225421 := bstep (se 3 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 28225421 = 10584533) B10584533
theorem B733075 : Blo 730325 733075 := bstep (se 1 (by rfl) ⟨549806, by rfl⟩ : syracuseStep 733075 = 1099613) B1099613
theorem B3125155 : Blo 730325 3125155 := bstep (se 1 (by rfl) ⟨2343866, by rfl⟩ : syracuseStep 3125155 = 4687733) B4687733
theorem B733091 : Blo 730325 733091 := bstep (se 1 (by rfl) ⟨549818, by rfl⟩ : syracuseStep 733091 = 1099637) B1099637
theorem B733107 : Blo 730325 733107 := bstep (se 1 (by rfl) ⟨549830, by rfl⟩ : syracuseStep 733107 = 1099661) B1099661
theorem B733123 : Blo 730325 733123 := bstep (se 1 (by rfl) ⟨549842, by rfl⟩ : syracuseStep 733123 = 1099685) B1099685
theorem B733139 : Blo 730325 733139 := bstep (se 1 (by rfl) ⟨549854, by rfl⟩ : syracuseStep 733139 = 1099709) B1099709
theorem B733155 : Blo 730325 733155 := bstep (se 1 (by rfl) ⟨549866, by rfl⟩ : syracuseStep 733155 = 1099733) B1099733
theorem B733171 : Blo 730325 733171 := bstep (se 1 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 733171 = 1099757) B1099757
theorem B733187 : Blo 730325 733187 := bstep (se 1 (by rfl) ⟨549890, by rfl⟩ : syracuseStep 733187 = 1099781) B1099781
theorem B2469905 : Blo 730325 2469905 := bstep (se 2 (by rfl) ⟨926214, by rfl⟩ : syracuseStep 2469905 = 1852429) B1852429
theorem B733203 : Blo 730325 733203 := bstep (se 1 (by rfl) ⟨549902, by rfl⟩ : syracuseStep 733203 = 1099805) B1099805
theorem B733219 : Blo 730325 733219 := bstep (se 1 (by rfl) ⟨549914, by rfl⟩ : syracuseStep 733219 = 1099829) B1099829
theorem B1388593 : Blo 730325 1388593 := bstep (se 2 (by rfl) ⟨520722, by rfl⟩ : syracuseStep 1388593 = 1041445) B1041445
theorem B733235 : Blo 730325 733235 := bstep (se 1 (by rfl) ⟨549926, by rfl⟩ : syracuseStep 733235 = 1099853) B1099853
theorem B733251 : Blo 730325 733251 := bstep (se 1 (by rfl) ⟨549938, by rfl⟩ : syracuseStep 733251 = 1099877) B1099877
theorem B733267 : Blo 730325 733267 := bstep (se 1 (by rfl) ⟨549950, by rfl⟩ : syracuseStep 733267 = 1099901) B1099901
theorem B733283 : Blo 730325 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B12693617 : Blo 730325 12693617 := bstep (se 2 (by rfl) ⟨4760106, by rfl⟩ : syracuseStep 12693617 = 9520213) B9520213
theorem B733299 : Blo 730325 733299 := bstep (se 1 (by rfl) ⟨549974, by rfl⟩ : syracuseStep 733299 = 1099949) B1099949
theorem B733315 : Blo 730325 733315 := bstep (se 1 (by rfl) ⟨549986, by rfl⟩ : syracuseStep 733315 = 1099973) B1099973
theorem B1486993 : Blo 730325 1486993 := bstep (se 2 (by rfl) ⟨557622, by rfl⟩ : syracuseStep 1486993 = 1115245) B1115245
theorem B1650833 : Blo 730325 1650833 := bstep (se 2 (by rfl) ⟨619062, by rfl⟩ : syracuseStep 1650833 = 1238125) B1238125
theorem B733331 : Blo 730325 733331 := bstep (se 1 (by rfl) ⟨549998, by rfl⟩ : syracuseStep 733331 = 1099997) B1099997
theorem B733347 : Blo 730325 733347 := bstep (se 1 (by rfl) ⟨550010, by rfl⟩ : syracuseStep 733347 = 1100021) B1100021
theorem B1650851 : Blo 730325 1650851 := bstep (se 1 (by rfl) ⟨1238138, by rfl⟩ : syracuseStep 1650851 = 2476277) B2476277
theorem B733363 : Blo 730325 733363 := bstep (se 1 (by rfl) ⟨550022, by rfl⟩ : syracuseStep 733363 = 1100045) B1100045
theorem B733379 : Blo 730325 733379 := bstep (se 1 (by rfl) ⟨550034, by rfl⟩ : syracuseStep 733379 = 1100069) B1100069
theorem B733395 : Blo 730325 733395 := bstep (se 1 (by rfl) ⟨550046, by rfl⟩ : syracuseStep 733395 = 1100093) B1100093
theorem B733411 : Blo 730325 733411 := bstep (se 1 (by rfl) ⟨550058, by rfl⟩ : syracuseStep 733411 = 1100117) B1100117
theorem B733427 : Blo 730325 733427 := bstep (se 1 (by rfl) ⟨550070, by rfl⟩ : syracuseStep 733427 = 1100141) B1100141
theorem B733443 : Blo 730325 733443 := bstep (se 1 (by rfl) ⟨550082, by rfl⟩ : syracuseStep 733443 = 1100165) B1100165
theorem B733459 : Blo 730325 733459 := bstep (se 1 (by rfl) ⟨550094, by rfl⟩ : syracuseStep 733459 = 1100189) B1100189
theorem B733475 : Blo 730325 733475 := bstep (se 1 (by rfl) ⟨550106, by rfl⟩ : syracuseStep 733475 = 1100213) B1100213
theorem B733491 : Blo 730325 733491 := bstep (se 1 (by rfl) ⟨550118, by rfl⟩ : syracuseStep 733491 = 1100237) B1100237
theorem B733507 : Blo 730325 733507 := bstep (se 1 (by rfl) ⟨550130, by rfl⟩ : syracuseStep 733507 = 1100261) B1100261
theorem B733523 : Blo 730325 733523 := bstep (se 1 (by rfl) ⟨550142, by rfl⟩ : syracuseStep 733523 = 1100285) B1100285
theorem B2634083 : Blo 730325 2634083 := bstep (se 1 (by rfl) ⟨1975562, by rfl⟩ : syracuseStep 2634083 = 3951125) B3951125
theorem B733539 : Blo 730325 733539 := bstep (se 1 (by rfl) ⟨550154, by rfl⟩ : syracuseStep 733539 = 1100309) B1100309
theorem B733555 : Blo 730325 733555 := bstep (se 1 (by rfl) ⟨550166, by rfl⟩ : syracuseStep 733555 = 1100333) B1100333
theorem B733571 : Blo 730325 733571 := bstep (se 1 (by rfl) ⟨550178, by rfl⟩ : syracuseStep 733571 = 1100357) B1100357
theorem B4010381 : Blo 730325 4010381 := bstep (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) B1503893
theorem B3715469 : Blo 730325 3715469 := bstep (se 3 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 3715469 = 1393301) B1393301
theorem B733587 : Blo 730325 733587 := bstep (se 1 (by rfl) ⟨550190, by rfl⟩ : syracuseStep 733587 = 1100381) B1100381
theorem B733603 : Blo 730325 733603 := bstep (se 1 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 733603 = 1100405) B1100405
theorem B1651121 : Blo 730325 1651121 := bstep (se 2 (by rfl) ⟨619170, by rfl⟩ : syracuseStep 1651121 = 1238341) B1238341
theorem B733619 : Blo 730325 733619 := bstep (se 1 (by rfl) ⟨550214, by rfl⟩ : syracuseStep 733619 = 1100429) B1100429
theorem B733635 : Blo 730325 733635 := bstep (se 1 (by rfl) ⟨550226, by rfl⟩ : syracuseStep 733635 = 1100453) B1100453
theorem B1651139 : Blo 730325 1651139 := bstep (se 1 (by rfl) ⟨1238354, by rfl⟩ : syracuseStep 1651139 = 2476709) B2476709
theorem B733651 : Blo 730325 733651 := bstep (se 1 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 733651 = 1100477) B1100477
theorem B733667 : Blo 730325 733667 := bstep (se 1 (by rfl) ⟨550250, by rfl⟩ : syracuseStep 733667 = 1100501) B1100501
theorem B733683 : Blo 730325 733683 := bstep (se 1 (by rfl) ⟨550262, by rfl⟩ : syracuseStep 733683 = 1100525) B1100525
theorem B733699 : Blo 730325 733699 := bstep (se 1 (by rfl) ⟨550274, by rfl⟩ : syracuseStep 733699 = 1100549) B1100549
theorem B5550605 : Blo 730325 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B733715 : Blo 730325 733715 := bstep (se 1 (by rfl) ⟨550286, by rfl⟩ : syracuseStep 733715 = 1100573) B1100573
theorem B733731 : Blo 730325 733731 := bstep (se 1 (by rfl) ⟨550298, by rfl⟩ : syracuseStep 733731 = 1100597) B1100597
theorem B2470445 : Blo 730325 2470445 := bstep (se 3 (by rfl) ⟨463208, by rfl⟩ : syracuseStep 2470445 = 926417) B926417
theorem B733747 : Blo 730325 733747 := bstep (se 1 (by rfl) ⟨550310, by rfl⟩ : syracuseStep 733747 = 1100621) B1100621
theorem B733763 : Blo 730325 733763 := bstep (se 1 (by rfl) ⟨550322, by rfl⟩ : syracuseStep 733763 = 1100645) B1100645
theorem B733779 : Blo 730325 733779 := bstep (se 1 (by rfl) ⟨550334, by rfl⟩ : syracuseStep 733779 = 1100669) B1100669
theorem B2470499 : Blo 730325 2470499 := bstep (se 1 (by rfl) ⟨1852874, by rfl⟩ : syracuseStep 2470499 = 3705749) B3705749
theorem B733795 : Blo 730325 733795 := bstep (se 1 (by rfl) ⟨550346, by rfl⟩ : syracuseStep 733795 = 1100693) B1100693
theorem B15807089 : Blo 730325 15807089 := bstep (se 2 (by rfl) ⟨5927658, by rfl⟩ : syracuseStep 15807089 = 11855317) B11855317
theorem B3519089 : Blo 730325 3519089 := bstep (se 2 (by rfl) ⟨1319658, by rfl⟩ : syracuseStep 3519089 = 2639317) B2639317
theorem B733811 : Blo 730325 733811 := bstep (se 1 (by rfl) ⟨550358, by rfl⟩ : syracuseStep 733811 = 1100717) B1100717
theorem B733827 : Blo 730325 733827 := bstep (se 1 (by rfl) ⟨550370, by rfl⟩ : syracuseStep 733827 = 1100741) B1100741
theorem B733843 : Blo 730325 733843 := bstep (se 1 (by rfl) ⟨550382, by rfl⟩ : syracuseStep 733843 = 1100765) B1100765
theorem B733859 : Blo 730325 733859 := bstep (se 1 (by rfl) ⟨550394, by rfl⟩ : syracuseStep 733859 = 1100789) B1100789
theorem B733875 : Blo 730325 733875 := bstep (se 1 (by rfl) ⟨550406, by rfl⟩ : syracuseStep 733875 = 1100813) B1100813
theorem B733891 : Blo 730325 733891 := bstep (se 1 (by rfl) ⟨550418, by rfl⟩ : syracuseStep 733891 = 1100837) B1100837
theorem B1651409 : Blo 730325 1651409 := bstep (se 2 (by rfl) ⟨619278, by rfl⟩ : syracuseStep 1651409 = 1238557) B1238557
theorem B733907 : Blo 730325 733907 := bstep (se 1 (by rfl) ⟨550430, by rfl⟩ : syracuseStep 733907 = 1100861) B1100861
theorem B733923 : Blo 730325 733923 := bstep (se 1 (by rfl) ⟨550442, by rfl⟩ : syracuseStep 733923 = 1100885) B1100885
theorem B1651427 : Blo 730325 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B733939 : Blo 730325 733939 := bstep (se 1 (by rfl) ⟨550454, by rfl⟩ : syracuseStep 733939 = 1100909) B1100909
theorem B733955 : Blo 730325 733955 := bstep (se 1 (by rfl) ⟨550466, by rfl⟩ : syracuseStep 733955 = 1100933) B1100933
theorem B733971 : Blo 730325 733971 := bstep (se 1 (by rfl) ⟨550478, by rfl⟩ : syracuseStep 733971 = 1100957) B1100957
theorem B733987 : Blo 730325 733987 := bstep (se 1 (by rfl) ⟨550490, by rfl⟩ : syracuseStep 733987 = 1100981) B1100981
theorem B2634545 : Blo 730325 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B734003 : Blo 730325 734003 := bstep (se 1 (by rfl) ⟨550502, by rfl⟩ : syracuseStep 734003 = 1101005) B1101005
theorem B734019 : Blo 730325 734019 := bstep (se 1 (by rfl) ⟨550514, by rfl⟩ : syracuseStep 734019 = 1101029) B1101029
theorem B734035 : Blo 730325 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B734051 : Blo 730325 734051 := bstep (se 1 (by rfl) ⟨550538, by rfl⟩ : syracuseStep 734051 = 1101077) B1101077
theorem B2470769 : Blo 730325 2470769 := bstep (se 2 (by rfl) ⟨926538, by rfl⟩ : syracuseStep 2470769 = 1853077) B1853077
theorem B734067 : Blo 730325 734067 := bstep (se 1 (by rfl) ⟨550550, by rfl⟩ : syracuseStep 734067 = 1101101) B1101101
theorem B734083 : Blo 730325 734083 := bstep (se 1 (by rfl) ⟨550562, by rfl⟩ : syracuseStep 734083 = 1101125) B1101125
theorem B734099 : Blo 730325 734099 := bstep (se 1 (by rfl) ⟨550574, by rfl⟩ : syracuseStep 734099 = 1101149) B1101149
theorem B734115 : Blo 730325 734115 := bstep (se 1 (by rfl) ⟨550586, by rfl⟩ : syracuseStep 734115 = 1101173) B1101173
theorem B734131 : Blo 730325 734131 := bstep (se 1 (by rfl) ⟨550598, by rfl⟩ : syracuseStep 734131 = 1101197) B1101197
theorem B734147 : Blo 730325 734147 := bstep (se 1 (by rfl) ⟨550610, by rfl⟩ : syracuseStep 734147 = 1101221) B1101221
theorem B734163 : Blo 730325 734163 := bstep (se 1 (by rfl) ⟨550622, by rfl⟩ : syracuseStep 734163 = 1101245) B1101245
theorem B734179 : Blo 730325 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B1651697 : Blo 730325 1651697 := bstep (se 2 (by rfl) ⟨619386, by rfl⟩ : syracuseStep 1651697 = 1238773) B1238773
theorem B734195 : Blo 730325 734195 := bstep (se 1 (by rfl) ⟨550646, by rfl⟩ : syracuseStep 734195 = 1101293) B1101293
theorem B1651715 : Blo 730325 1651715 := bstep (se 1 (by rfl) ⟨1238786, by rfl⟩ : syracuseStep 1651715 = 2477573) B2477573
theorem B734211 : Blo 730325 734211 := bstep (se 1 (by rfl) ⟨550658, by rfl⟩ : syracuseStep 734211 = 1101317) B1101317
theorem B734227 : Blo 730325 734227 := bstep (se 1 (by rfl) ⟨550670, by rfl⟩ : syracuseStep 734227 = 1101341) B1101341
theorem B734243 : Blo 730325 734243 := bstep (se 1 (by rfl) ⟨550682, by rfl⟩ : syracuseStep 734243 = 1101365) B1101365
theorem B734259 : Blo 730325 734259 := bstep (se 1 (by rfl) ⟨550694, by rfl⟩ : syracuseStep 734259 = 1101389) B1101389
theorem B734275 : Blo 730325 734275 := bstep (se 1 (by rfl) ⟨550706, by rfl⟩ : syracuseStep 734275 = 1101413) B1101413
theorem B1389649 : Blo 730325 1389649 := bstep (se 2 (by rfl) ⟨521118, by rfl⟩ : syracuseStep 1389649 = 1042237) B1042237
theorem B734291 : Blo 730325 734291 := bstep (se 1 (by rfl) ⟨550718, by rfl⟩ : syracuseStep 734291 = 1101437) B1101437
theorem B734307 : Blo 730325 734307 := bstep (se 1 (by rfl) ⟨550730, by rfl⟩ : syracuseStep 734307 = 1101461) B1101461
theorem B734323 : Blo 730325 734323 := bstep (se 1 (by rfl) ⟨550742, by rfl⟩ : syracuseStep 734323 = 1101485) B1101485
theorem B2340049 : Blo 730325 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B1651985 : Blo 730325 1651985 := bstep (se 2 (by rfl) ⟨619494, by rfl⟩ : syracuseStep 1651985 = 1238989) B1238989
theorem B1652003 : Blo 730325 1652003 := bstep (se 1 (by rfl) ⟨1239002, by rfl⟩ : syracuseStep 1652003 = 2478005) B2478005
theorem B2110801 : Blo 730325 2110801 := bstep (se 2 (by rfl) ⟨791550, by rfl⟩ : syracuseStep 2110801 = 1583101) B1583101
theorem B2340227 : Blo 730325 2340227 := bstep (se 1 (by rfl) ⟨1755170, by rfl⟩ : syracuseStep 2340227 = 3510341) B3510341
theorem B2471309 : Blo 730325 2471309 := bstep (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) B926741
theorem B2471363 : Blo 730325 2471363 := bstep (se 1 (by rfl) ⟨1853522, by rfl⟩ : syracuseStep 2471363 = 3707045) B3707045
theorem B1390051 : Blo 730325 1390051 := bstep (se 1 (by rfl) ⟨1042538, by rfl⟩ : syracuseStep 1390051 = 2085077) B2085077
theorem B1390097 : Blo 730325 1390097 := bstep (se 2 (by rfl) ⟨521286, by rfl⟩ : syracuseStep 1390097 = 1042573) B1042573
theorem B4699781 : Blo 730325 4699781 := bstep (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) B881209
theorem B1848977 : Blo 730325 1848977 := bstep (se 2 (by rfl) ⟨693366, by rfl⟩ : syracuseStep 1848977 = 1386733) B1386733
theorem B1849027 : Blo 730325 1849027 := bstep (se 1 (by rfl) ⟨1386770, by rfl⟩ : syracuseStep 1849027 = 2773541) B2773541
theorem B2471633 : Blo 730325 2471633 := bstep (se 2 (by rfl) ⟨926862, by rfl⟩ : syracuseStep 2471633 = 1853725) B1853725
theorem B1128179 : Blo 730325 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B4175621 : Blo 730325 4175621 := bstep (se 4 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 4175621 = 782929) B782929
theorem B3389219 : Blo 730325 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B1390385 : Blo 730325 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B12531509 : Blo 730325 12531509 := bstep (se 5 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 12531509 = 1174829) B1174829
theorem B1095491 : Blo 730325 1095491 := bstep (se 1 (by rfl) ⟨821618, by rfl⟩ : syracuseStep 1095491 = 1643237) B1643237
theorem B1849169 : Blo 730325 1849169 := bstep (se 2 (by rfl) ⟨693438, by rfl⟩ : syracuseStep 1849169 = 1386877) B1386877
theorem B1095521 : Blo 730325 1095521 := bstep (se 2 (by rfl) ⟨410820, by rfl⟩ : syracuseStep 1095521 = 821641) B821641
theorem B1095539 : Blo 730325 1095539 := bstep (se 1 (by rfl) ⟨821654, by rfl⟩ : syracuseStep 1095539 = 1643309) B1643309
theorem B1095569 : Blo 730325 1095569 := bstep (se 2 (by rfl) ⟨410838, by rfl⟩ : syracuseStep 1095569 = 821677) B821677
theorem B1095587 : Blo 730325 1095587 := bstep (se 1 (by rfl) ⟨821690, by rfl⟩ : syracuseStep 1095587 = 1643381) B1643381
theorem B1095617 : Blo 730325 1095617 := bstep (se 2 (by rfl) ⟨410856, by rfl⟩ : syracuseStep 1095617 = 821713) B821713
theorem B1095635 : Blo 730325 1095635 := bstep (se 1 (by rfl) ⟨821726, by rfl⟩ : syracuseStep 1095635 = 1643453) B1643453
theorem B1095665 : Blo 730325 1095665 := bstep (se 2 (by rfl) ⟨410874, by rfl⟩ : syracuseStep 1095665 = 821749) B821749
theorem B1095683 : Blo 730325 1095683 := bstep (se 1 (by rfl) ⟨821762, by rfl⟩ : syracuseStep 1095683 = 1643525) B1643525
theorem B1095713 : Blo 730325 1095713 := bstep (se 2 (by rfl) ⟨410892, by rfl⟩ : syracuseStep 1095713 = 821785) B821785
theorem B1095731 : Blo 730325 1095731 := bstep (se 1 (by rfl) ⟨821798, by rfl⟩ : syracuseStep 1095731 = 1643597) B1643597
theorem B1095761 : Blo 730325 1095761 := bstep (se 2 (by rfl) ⟨410910, by rfl⟩ : syracuseStep 1095761 = 821821) B821821
theorem B1095779 : Blo 730325 1095779 := bstep (se 1 (by rfl) ⟨821834, by rfl⟩ : syracuseStep 1095779 = 1643669) B1643669
theorem B1095809 : Blo 730325 1095809 := bstep (se 2 (by rfl) ⟨410928, by rfl⟩ : syracuseStep 1095809 = 821857) B821857
theorem B1095827 : Blo 730325 1095827 := bstep (se 1 (by rfl) ⟨821870, by rfl⟩ : syracuseStep 1095827 = 1643741) B1643741
theorem B1095857 : Blo 730325 1095857 := bstep (se 2 (by rfl) ⟨410946, by rfl⟩ : syracuseStep 1095857 = 821893) B821893
theorem B1095875 : Blo 730325 1095875 := bstep (se 1 (by rfl) ⟨821906, by rfl⟩ : syracuseStep 1095875 = 1643813) B1643813
theorem B833747 : Blo 730325 833747 := bstep (se 1 (by rfl) ⟨625310, by rfl⟩ : syracuseStep 833747 = 1250621) B1250621
theorem B1095905 : Blo 730325 1095905 := bstep (se 2 (by rfl) ⟨410964, by rfl⟩ : syracuseStep 1095905 = 821929) B821929
theorem B2472173 : Blo 730325 2472173 := bstep (se 3 (by rfl) ⟨463532, by rfl⟩ : syracuseStep 2472173 = 927065) B927065
theorem B1095923 : Blo 730325 1095923 := bstep (se 1 (by rfl) ⟨821942, by rfl⟩ : syracuseStep 1095923 = 1643885) B1643885
theorem B1095953 : Blo 730325 1095953 := bstep (se 2 (by rfl) ⟨410982, by rfl⟩ : syracuseStep 1095953 = 821965) B821965
theorem B1095971 : Blo 730325 1095971 := bstep (se 1 (by rfl) ⟨821978, by rfl⟩ : syracuseStep 1095971 = 1643957) B1643957
theorem B2472227 : Blo 730325 2472227 := bstep (se 1 (by rfl) ⟨1854170, by rfl⟩ : syracuseStep 2472227 = 3708341) B3708341
theorem B1096001 : Blo 730325 1096001 := bstep (se 2 (by rfl) ⟨411000, by rfl⟩ : syracuseStep 1096001 = 822001) B822001
theorem B1096019 : Blo 730325 1096019 := bstep (se 1 (by rfl) ⟨822014, by rfl⟩ : syracuseStep 1096019 = 1644029) B1644029
theorem B8927587 : Blo 730325 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B1096049 : Blo 730325 1096049 := bstep (se 2 (by rfl) ⟨411018, by rfl⟩ : syracuseStep 1096049 = 822037) B822037
theorem B1096067 : Blo 730325 1096067 := bstep (se 1 (by rfl) ⟨822050, by rfl⟩ : syracuseStep 1096067 = 1644101) B1644101
theorem B1096097 : Blo 730325 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B4176305 : Blo 730325 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B1096115 : Blo 730325 1096115 := bstep (se 1 (by rfl) ⟨822086, by rfl⟩ : syracuseStep 1096115 = 1644173) B1644173
theorem B1096145 : Blo 730325 1096145 := bstep (se 2 (by rfl) ⟨411054, by rfl⟩ : syracuseStep 1096145 = 822109) B822109
theorem B1096163 : Blo 730325 1096163 := bstep (se 1 (by rfl) ⟨822122, by rfl⟩ : syracuseStep 1096163 = 1644245) B1644245
theorem B1096193 : Blo 730325 1096193 := bstep (se 2 (by rfl) ⟨411072, by rfl⟩ : syracuseStep 1096193 = 822145) B822145
theorem B1391107 : Blo 730325 1391107 := bstep (se 1 (by rfl) ⟨1043330, by rfl⟩ : syracuseStep 1391107 = 2086661) B2086661
theorem B1096211 : Blo 730325 1096211 := bstep (se 1 (by rfl) ⟨822158, by rfl⟩ : syracuseStep 1096211 = 1644317) B1644317
theorem B1096241 : Blo 730325 1096241 := bstep (se 2 (by rfl) ⟨411090, by rfl⟩ : syracuseStep 1096241 = 822181) B822181
theorem B2472497 : Blo 730325 2472497 := bstep (se 2 (by rfl) ⟨927186, by rfl⟩ : syracuseStep 2472497 = 1854373) B1854373
theorem B1096259 : Blo 730325 1096259 := bstep (se 1 (by rfl) ⟨822194, by rfl⟩ : syracuseStep 1096259 = 1644389) B1644389
theorem B1096289 : Blo 730325 1096289 := bstep (se 2 (by rfl) ⟨411108, by rfl⟩ : syracuseStep 1096289 = 822217) B822217
theorem B1096307 : Blo 730325 1096307 := bstep (se 1 (by rfl) ⟨822230, by rfl⟩ : syracuseStep 1096307 = 1644461) B1644461
theorem B1096337 : Blo 730325 1096337 := bstep (se 2 (by rfl) ⟨411126, by rfl⟩ : syracuseStep 1096337 = 822253) B822253
theorem B3750563 : Blo 730325 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B1096355 : Blo 730325 1096355 := bstep (se 1 (by rfl) ⟨822266, by rfl⟩ : syracuseStep 1096355 = 1644533) B1644533
theorem B1096385 : Blo 730325 1096385 := bstep (se 2 (by rfl) ⟨411144, by rfl⟩ : syracuseStep 1096385 = 822289) B822289
theorem B1096403 : Blo 730325 1096403 := bstep (se 1 (by rfl) ⟨822302, by rfl⟩ : syracuseStep 1096403 = 1644605) B1644605
theorem B1096433 : Blo 730325 1096433 := bstep (se 2 (by rfl) ⟨411162, by rfl⟩ : syracuseStep 1096433 = 822325) B822325
theorem B1096451 : Blo 730325 1096451 := bstep (se 1 (by rfl) ⟨822338, by rfl⟩ : syracuseStep 1096451 = 1644677) B1644677
theorem B1096481 : Blo 730325 1096481 := bstep (se 2 (by rfl) ⟨411180, by rfl⟩ : syracuseStep 1096481 = 822361) B822361
theorem B1850161 : Blo 730325 1850161 := bstep (se 2 (by rfl) ⟨693810, by rfl⟩ : syracuseStep 1850161 = 1387621) B1387621
theorem B1096499 : Blo 730325 1096499 := bstep (se 1 (by rfl) ⟨822374, by rfl⟩ : syracuseStep 1096499 = 1644749) B1644749
theorem B1096529 : Blo 730325 1096529 := bstep (se 2 (by rfl) ⟨411198, by rfl⟩ : syracuseStep 1096529 = 822397) B822397
theorem B1096547 : Blo 730325 1096547 := bstep (se 1 (by rfl) ⟨822410, by rfl⟩ : syracuseStep 1096547 = 1644821) B1644821
theorem B1096577 : Blo 730325 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B1096595 : Blo 730325 1096595 := bstep (se 1 (by rfl) ⟨822446, by rfl⟩ : syracuseStep 1096595 = 1644893) B1644893
theorem B1096625 : Blo 730325 1096625 := bstep (se 2 (by rfl) ⟨411234, by rfl⟩ : syracuseStep 1096625 = 822469) B822469
theorem B1096643 : Blo 730325 1096643 := bstep (se 1 (by rfl) ⟨822482, by rfl⟩ : syracuseStep 1096643 = 1644965) B1644965
theorem B1391555 : Blo 730325 1391555 := bstep (se 1 (by rfl) ⟨1043666, by rfl⟩ : syracuseStep 1391555 = 2087333) B2087333
theorem B1096673 : Blo 730325 1096673 := bstep (se 2 (by rfl) ⟨411252, by rfl⟩ : syracuseStep 1096673 = 822505) B822505
theorem B1096691 : Blo 730325 1096691 := bstep (se 1 (by rfl) ⟨822518, by rfl⟩ : syracuseStep 1096691 = 1645037) B1645037
theorem B3521549 : Blo 730325 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B1096721 : Blo 730325 1096721 := bstep (se 2 (by rfl) ⟨411270, by rfl⟩ : syracuseStep 1096721 = 822541) B822541
theorem B1096739 : Blo 730325 1096739 := bstep (se 1 (by rfl) ⟨822554, by rfl⟩ : syracuseStep 1096739 = 1645109) B1645109
theorem B1096769 : Blo 730325 1096769 := bstep (se 2 (by rfl) ⟨411288, by rfl⟩ : syracuseStep 1096769 = 822577) B822577
theorem B1850435 : Blo 730325 1850435 := bstep (se 1 (by rfl) ⟨1387826, by rfl⟩ : syracuseStep 1850435 = 2775653) B2775653
theorem B2473037 : Blo 730325 2473037 := bstep (se 3 (by rfl) ⟨463694, by rfl⟩ : syracuseStep 2473037 = 927389) B927389
theorem B1096787 : Blo 730325 1096787 := bstep (se 1 (by rfl) ⟨822590, by rfl⟩ : syracuseStep 1096787 = 1645181) B1645181
theorem B2341997 : Blo 730325 2341997 := bstep (se 3 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 2341997 = 878249) B878249
theorem B1096817 : Blo 730325 1096817 := bstep (se 2 (by rfl) ⟨411306, by rfl⟩ : syracuseStep 1096817 = 822613) B822613
theorem B1096835 : Blo 730325 1096835 := bstep (se 1 (by rfl) ⟨822626, by rfl⟩ : syracuseStep 1096835 = 1645253) B1645253
theorem B2473091 : Blo 730325 2473091 := bstep (se 1 (by rfl) ⟨1854818, by rfl⟩ : syracuseStep 2473091 = 3709637) B3709637
theorem B1096865 : Blo 730325 1096865 := bstep (se 2 (by rfl) ⟨411324, by rfl⟩ : syracuseStep 1096865 = 822649) B822649
theorem B1096883 : Blo 730325 1096883 := bstep (se 1 (by rfl) ⟨822662, by rfl⟩ : syracuseStep 1096883 = 1645325) B1645325
theorem B1096913 : Blo 730325 1096913 := bstep (se 2 (by rfl) ⟨411342, by rfl⟩ : syracuseStep 1096913 = 822685) B822685
theorem B2964707 : Blo 730325 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B1096931 : Blo 730325 1096931 := bstep (se 1 (by rfl) ⟨822698, by rfl⟩ : syracuseStep 1096931 = 1645397) B1645397
theorem B1391843 : Blo 730325 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1096961 : Blo 730325 1096961 := bstep (se 2 (by rfl) ⟨411360, by rfl⟩ : syracuseStep 1096961 = 822721) B822721
theorem B1850627 : Blo 730325 1850627 := bstep (se 1 (by rfl) ⟨1387970, by rfl⟩ : syracuseStep 1850627 = 2775941) B2775941
theorem B1096979 : Blo 730325 1096979 := bstep (se 1 (by rfl) ⟨822734, by rfl⟩ : syracuseStep 1096979 = 1645469) B1645469
theorem B1097009 : Blo 730325 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B1097027 : Blo 730325 1097027 := bstep (se 1 (by rfl) ⟨822770, by rfl⟩ : syracuseStep 1097027 = 1645541) B1645541
theorem B1097057 : Blo 730325 1097057 := bstep (se 2 (by rfl) ⟨411396, by rfl⟩ : syracuseStep 1097057 = 822793) B822793
theorem B5553521 : Blo 730325 5553521 := bstep (se 2 (by rfl) ⟨2082570, by rfl⟩ : syracuseStep 5553521 = 4165141) B4165141
theorem B1097075 : Blo 730325 1097075 := bstep (se 1 (by rfl) ⟨822806, by rfl⟩ : syracuseStep 1097075 = 1645613) B1645613
theorem B1097105 : Blo 730325 1097105 := bstep (se 2 (by rfl) ⟨411414, by rfl⟩ : syracuseStep 1097105 = 822829) B822829
theorem B2473361 : Blo 730325 2473361 := bstep (se 2 (by rfl) ⟨927510, by rfl⟩ : syracuseStep 2473361 = 1855021) B1855021
theorem B1097123 : Blo 730325 1097123 := bstep (se 1 (by rfl) ⟨822842, by rfl⟩ : syracuseStep 1097123 = 1645685) B1645685
theorem B1097153 : Blo 730325 1097153 := bstep (se 2 (by rfl) ⟨411432, by rfl⟩ : syracuseStep 1097153 = 822865) B822865
theorem B47431109 : Blo 730325 47431109 := bstep (se 4 (by rfl) ⟨4446666, by rfl⟩ : syracuseStep 47431109 = 8893333) B8893333
theorem B1097171 : Blo 730325 1097171 := bstep (se 1 (by rfl) ⟨822878, by rfl⟩ : syracuseStep 1097171 = 1645757) B1645757
theorem B1097201 : Blo 730325 1097201 := bstep (se 2 (by rfl) ⟨411450, by rfl⟩ : syracuseStep 1097201 = 822901) B822901
theorem B1097219 : Blo 730325 1097219 := bstep (se 1 (by rfl) ⟨822914, by rfl⟩ : syracuseStep 1097219 = 1645829) B1645829
theorem B1097249 : Blo 730325 1097249 := bstep (se 2 (by rfl) ⟨411468, by rfl⟩ : syracuseStep 1097249 = 822937) B822937
theorem B1097267 : Blo 730325 1097267 := bstep (se 1 (by rfl) ⟨822950, by rfl⟩ : syracuseStep 1097267 = 1645901) B1645901
theorem B1097297 : Blo 730325 1097297 := bstep (se 2 (by rfl) ⟨411486, by rfl⟩ : syracuseStep 1097297 = 822973) B822973
theorem B1097315 : Blo 730325 1097315 := bstep (se 1 (by rfl) ⟨822986, by rfl⟩ : syracuseStep 1097315 = 1645973) B1645973
theorem B1097345 : Blo 730325 1097345 := bstep (se 2 (by rfl) ⟨411504, by rfl⟩ : syracuseStep 1097345 = 823009) B823009
theorem B1982083 : Blo 730325 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B1097363 : Blo 730325 1097363 := bstep (se 1 (by rfl) ⟨823022, by rfl⟩ : syracuseStep 1097363 = 1646045) B1646045
theorem B1097393 : Blo 730325 1097393 := bstep (se 2 (by rfl) ⟨411522, by rfl⟩ : syracuseStep 1097393 = 823045) B823045
theorem B1097411 : Blo 730325 1097411 := bstep (se 1 (by rfl) ⟨823058, by rfl⟩ : syracuseStep 1097411 = 1646117) B1646117
theorem B1097441 : Blo 730325 1097441 := bstep (se 2 (by rfl) ⟨411540, by rfl⟩ : syracuseStep 1097441 = 823081) B823081
theorem B1097459 : Blo 730325 1097459 := bstep (se 1 (by rfl) ⟨823094, by rfl⟩ : syracuseStep 1097459 = 1646189) B1646189
theorem B1097489 : Blo 730325 1097489 := bstep (se 2 (by rfl) ⟨411558, by rfl⟩ : syracuseStep 1097489 = 823117) B823117
theorem B1097507 : Blo 730325 1097507 := bstep (se 1 (by rfl) ⟨823130, by rfl⟩ : syracuseStep 1097507 = 1646261) B1646261
theorem B1097537 : Blo 730325 1097537 := bstep (se 2 (by rfl) ⟨411576, by rfl⟩ : syracuseStep 1097537 = 823153) B823153
theorem B1097555 : Blo 730325 1097555 := bstep (se 1 (by rfl) ⟨823166, by rfl⟩ : syracuseStep 1097555 = 1646333) B1646333
theorem B3129187 : Blo 730325 3129187 := bstep (se 1 (by rfl) ⟨2346890, by rfl⟩ : syracuseStep 3129187 = 4693781) B4693781
theorem B4177763 : Blo 730325 4177763 := bstep (se 1 (by rfl) ⟨3133322, by rfl⟩ : syracuseStep 4177763 = 6266645) B6266645
theorem B1097585 : Blo 730325 1097585 := bstep (se 2 (by rfl) ⟨411594, by rfl⟩ : syracuseStep 1097585 = 823189) B823189
theorem B1097603 : Blo 730325 1097603 := bstep (se 1 (by rfl) ⟨823202, by rfl⟩ : syracuseStep 1097603 = 1646405) B1646405
theorem B2080657 : Blo 730325 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1982353 : Blo 730325 1982353 := bstep (se 2 (by rfl) ⟨743382, by rfl⟩ : syracuseStep 1982353 = 1486765) B1486765
theorem B1097633 : Blo 730325 1097633 := bstep (se 2 (by rfl) ⟨411612, by rfl⟩ : syracuseStep 1097633 = 823225) B823225
theorem B2473901 : Blo 730325 2473901 := bstep (se 3 (by rfl) ⟨463856, by rfl⟩ : syracuseStep 2473901 = 927713) B927713
theorem B1097651 : Blo 730325 1097651 := bstep (se 1 (by rfl) ⟨823238, by rfl⟩ : syracuseStep 1097651 = 1646477) B1646477
theorem B2637773 : Blo 730325 2637773 := bstep (se 3 (by rfl) ⟨494582, by rfl⟩ : syracuseStep 2637773 = 989165) B989165
theorem B1097681 : Blo 730325 1097681 := bstep (se 2 (by rfl) ⟨411630, by rfl⟩ : syracuseStep 1097681 = 823261) B823261
theorem B1097699 : Blo 730325 1097699 := bstep (se 1 (by rfl) ⟨823274, by rfl⟩ : syracuseStep 1097699 = 1646549) B1646549
theorem B2473955 : Blo 730325 2473955 := bstep (se 1 (by rfl) ⟨1855466, by rfl⟩ : syracuseStep 2473955 = 3710933) B3710933
theorem B1097729 : Blo 730325 1097729 := bstep (se 2 (by rfl) ⟨411648, by rfl⟩ : syracuseStep 1097729 = 823297) B823297
theorem B1097747 : Blo 730325 1097747 := bstep (se 1 (by rfl) ⟨823310, by rfl⟩ : syracuseStep 1097747 = 1646621) B1646621
theorem B1097777 : Blo 730325 1097777 := bstep (se 2 (by rfl) ⟨411666, by rfl⟩ : syracuseStep 1097777 = 823333) B823333
theorem B1097795 : Blo 730325 1097795 := bstep (se 1 (by rfl) ⟨823346, by rfl⟩ : syracuseStep 1097795 = 1646693) B1646693
theorem B1097825 : Blo 730325 1097825 := bstep (se 2 (by rfl) ⟨411684, by rfl⟩ : syracuseStep 1097825 = 823369) B823369
theorem B1097843 : Blo 730325 1097843 := bstep (se 1 (by rfl) ⟨823382, by rfl⟩ : syracuseStep 1097843 = 1646765) B1646765
theorem B1097873 : Blo 730325 1097873 := bstep (se 2 (by rfl) ⟨411702, by rfl⟩ : syracuseStep 1097873 = 823405) B823405
theorem B1392785 : Blo 730325 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B1097891 : Blo 730325 1097891 := bstep (se 1 (by rfl) ⟨823418, by rfl⟩ : syracuseStep 1097891 = 1646837) B1646837
theorem B1851569 : Blo 730325 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B1097921 : Blo 730325 1097921 := bstep (se 2 (by rfl) ⟨411720, by rfl⟩ : syracuseStep 1097921 = 823441) B823441
theorem B1097939 : Blo 730325 1097939 := bstep (se 1 (by rfl) ⟨823454, by rfl⟩ : syracuseStep 1097939 = 1646909) B1646909
theorem B1851619 : Blo 730325 1851619 := bstep (se 1 (by rfl) ⟨1388714, by rfl⟩ : syracuseStep 1851619 = 2777429) B2777429
theorem B1097969 : Blo 730325 1097969 := bstep (se 2 (by rfl) ⟨411738, by rfl⟩ : syracuseStep 1097969 = 823477) B823477
theorem B2474225 : Blo 730325 2474225 := bstep (se 2 (by rfl) ⟨927834, by rfl⟩ : syracuseStep 2474225 = 1855669) B1855669
theorem B1097987 : Blo 730325 1097987 := bstep (se 1 (by rfl) ⟨823490, by rfl⟩ : syracuseStep 1097987 = 1646981) B1646981
theorem B1098017 : Blo 730325 1098017 := bstep (se 2 (by rfl) ⟨411756, by rfl⟩ : syracuseStep 1098017 = 823513) B823513
theorem B1098035 : Blo 730325 1098035 := bstep (se 1 (by rfl) ⟨823526, by rfl⟩ : syracuseStep 1098035 = 1647053) B1647053
theorem B1098065 : Blo 730325 1098065 := bstep (se 2 (by rfl) ⟨411774, by rfl⟩ : syracuseStep 1098065 = 823549) B823549
theorem B1098083 : Blo 730325 1098083 := bstep (se 1 (by rfl) ⟨823562, by rfl⟩ : syracuseStep 1098083 = 1647125) B1647125
theorem B1851761 : Blo 730325 1851761 := bstep (se 2 (by rfl) ⟨694410, by rfl⟩ : syracuseStep 1851761 = 1388821) B1388821
theorem B1098113 : Blo 730325 1098113 := bstep (se 2 (by rfl) ⟨411792, by rfl⟩ : syracuseStep 1098113 = 823585) B823585
theorem B1098131 : Blo 730325 1098131 := bstep (se 1 (by rfl) ⟨823598, by rfl⟩ : syracuseStep 1098131 = 1647197) B1647197
theorem B835987 : Blo 730325 835987 := bstep (se 1 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 835987 = 1253981) B1253981
theorem B1098161 : Blo 730325 1098161 := bstep (se 2 (by rfl) ⟨411810, by rfl⟩ : syracuseStep 1098161 = 823621) B823621
theorem B1098179 : Blo 730325 1098179 := bstep (se 1 (by rfl) ⟨823634, by rfl⟩ : syracuseStep 1098179 = 1647269) B1647269
theorem B1098209 : Blo 730325 1098209 := bstep (se 2 (by rfl) ⟨411828, by rfl⟩ : syracuseStep 1098209 = 823657) B823657
theorem B1098227 : Blo 730325 1098227 := bstep (se 1 (by rfl) ⟨823670, by rfl⟩ : syracuseStep 1098227 = 1647341) B1647341
theorem B1098257 : Blo 730325 1098257 := bstep (se 2 (by rfl) ⟨411846, by rfl⟩ : syracuseStep 1098257 = 823693) B823693
theorem B1098275 : Blo 730325 1098275 := bstep (se 1 (by rfl) ⟨823706, by rfl⟩ : syracuseStep 1098275 = 1647413) B1647413
theorem B1098305 : Blo 730325 1098305 := bstep (se 2 (by rfl) ⟨411864, by rfl⟩ : syracuseStep 1098305 = 823729) B823729
theorem B1098323 : Blo 730325 1098323 := bstep (se 1 (by rfl) ⟨823742, by rfl⟩ : syracuseStep 1098323 = 1647485) B1647485
theorem B1098353 : Blo 730325 1098353 := bstep (se 2 (by rfl) ⟨411882, by rfl⟩ : syracuseStep 1098353 = 823765) B823765
theorem B1098371 : Blo 730325 1098371 := bstep (se 1 (by rfl) ⟨823778, by rfl⟩ : syracuseStep 1098371 = 1647557) B1647557
theorem B1098401 : Blo 730325 1098401 := bstep (se 2 (by rfl) ⟨411900, by rfl⟩ : syracuseStep 1098401 = 823801) B823801
theorem B1098419 : Blo 730325 1098419 := bstep (se 1 (by rfl) ⟨823814, by rfl⟩ : syracuseStep 1098419 = 1647629) B1647629
theorem B1098449 : Blo 730325 1098449 := bstep (se 2 (by rfl) ⟨411918, by rfl⟩ : syracuseStep 1098449 = 823837) B823837
theorem B1098467 : Blo 730325 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1098497 : Blo 730325 1098497 := bstep (se 2 (by rfl) ⟨411936, by rfl⟩ : syracuseStep 1098497 = 823873) B823873
theorem B2474765 : Blo 730325 2474765 := bstep (se 3 (by rfl) ⟨464018, by rfl⟩ : syracuseStep 2474765 = 928037) B928037
theorem B1098515 : Blo 730325 1098515 := bstep (se 1 (by rfl) ⟨823886, by rfl⟩ : syracuseStep 1098515 = 1647773) B1647773
theorem B1098545 : Blo 730325 1098545 := bstep (se 2 (by rfl) ⟨411954, by rfl⟩ : syracuseStep 1098545 = 823909) B823909
theorem B1098563 : Blo 730325 1098563 := bstep (se 1 (by rfl) ⟨823922, by rfl⟩ : syracuseStep 1098563 = 1647845) B1647845
theorem B2474819 : Blo 730325 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B1098593 : Blo 730325 1098593 := bstep (se 2 (by rfl) ⟨411972, by rfl⟩ : syracuseStep 1098593 = 823945) B823945
theorem B1098611 : Blo 730325 1098611 := bstep (se 1 (by rfl) ⟨823958, by rfl⟩ : syracuseStep 1098611 = 1647917) B1647917
theorem B1098641 : Blo 730325 1098641 := bstep (se 2 (by rfl) ⟨411990, by rfl⟩ : syracuseStep 1098641 = 823981) B823981
theorem B1098659 : Blo 730325 1098659 := bstep (se 1 (by rfl) ⟨823994, by rfl⟩ : syracuseStep 1098659 = 1647989) B1647989
theorem B1098689 : Blo 730325 1098689 := bstep (se 2 (by rfl) ⟨412008, by rfl⟩ : syracuseStep 1098689 = 824017) B824017
theorem B1098707 : Blo 730325 1098707 := bstep (se 1 (by rfl) ⟨824030, by rfl⟩ : syracuseStep 1098707 = 1648061) B1648061
theorem B1098737 : Blo 730325 1098737 := bstep (se 2 (by rfl) ⟨412026, by rfl⟩ : syracuseStep 1098737 = 824053) B824053
theorem B1098755 : Blo 730325 1098755 := bstep (se 1 (by rfl) ⟨824066, by rfl⟩ : syracuseStep 1098755 = 1648133) B1648133
theorem B1393681 : Blo 730325 1393681 := bstep (se 2 (by rfl) ⟨522630, by rfl⟩ : syracuseStep 1393681 = 1045261) B1045261
theorem B1098785 : Blo 730325 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B3130417 : Blo 730325 3130417 := bstep (se 2 (by rfl) ⟨1173906, by rfl⟩ : syracuseStep 3130417 = 2347813) B2347813
theorem B1098803 : Blo 730325 1098803 := bstep (se 1 (by rfl) ⟨824102, by rfl⟩ : syracuseStep 1098803 = 1648205) B1648205
theorem B1098833 : Blo 730325 1098833 := bstep (se 2 (by rfl) ⟨412062, by rfl⟩ : syracuseStep 1098833 = 824125) B824125
theorem B2475089 : Blo 730325 2475089 := bstep (se 2 (by rfl) ⟨928158, by rfl⟩ : syracuseStep 2475089 = 1856317) B1856317
theorem B1098851 : Blo 730325 1098851 := bstep (se 1 (by rfl) ⟨824138, by rfl⟩ : syracuseStep 1098851 = 1648277) B1648277
theorem B1098881 : Blo 730325 1098881 := bstep (se 2 (by rfl) ⟨412080, by rfl⟩ : syracuseStep 1098881 = 824161) B824161
theorem B2081933 : Blo 730325 2081933 := bstep (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) B780725
theorem B1098899 : Blo 730325 1098899 := bstep (se 1 (by rfl) ⟨824174, by rfl⟩ : syracuseStep 1098899 = 1648349) B1648349
theorem B1098929 : Blo 730325 1098929 := bstep (se 2 (by rfl) ⟨412098, by rfl⟩ : syracuseStep 1098929 = 824197) B824197
theorem B1393841 : Blo 730325 1393841 := bstep (se 2 (by rfl) ⟨522690, by rfl⟩ : syracuseStep 1393841 = 1045381) B1045381
theorem B1098947 : Blo 730325 1098947 := bstep (se 1 (by rfl) ⟨824210, by rfl⟩ : syracuseStep 1098947 = 1648421) B1648421
theorem B1098977 : Blo 730325 1098977 := bstep (se 2 (by rfl) ⟨412116, by rfl⟩ : syracuseStep 1098977 = 824233) B824233
theorem B1098995 : Blo 730325 1098995 := bstep (se 1 (by rfl) ⟨824246, by rfl⟩ : syracuseStep 1098995 = 1648493) B1648493
theorem B1099025 : Blo 730325 1099025 := bstep (se 2 (by rfl) ⟨412134, by rfl⟩ : syracuseStep 1099025 = 824269) B824269
theorem B1099043 : Blo 730325 1099043 := bstep (se 1 (by rfl) ⟨824282, by rfl⟩ : syracuseStep 1099043 = 1648565) B1648565
theorem B1099073 : Blo 730325 1099073 := bstep (se 2 (by rfl) ⟨412152, by rfl⟩ : syracuseStep 1099073 = 824305) B824305
theorem B2082115 : Blo 730325 2082115 := bstep (se 1 (by rfl) ⟨1561586, by rfl⟩ : syracuseStep 2082115 = 3123173) B3123173
theorem B1852753 : Blo 730325 1852753 := bstep (se 2 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 1852753 = 1389565) B1389565
theorem B1099091 : Blo 730325 1099091 := bstep (se 1 (by rfl) ⟨824318, by rfl⟩ : syracuseStep 1099091 = 1648637) B1648637
theorem B2082161 : Blo 730325 2082161 := bstep (se 2 (by rfl) ⟨780810, by rfl⟩ : syracuseStep 2082161 = 1561621) B1561621
theorem B1099121 : Blo 730325 1099121 := bstep (se 2 (by rfl) ⟨412170, by rfl⟩ : syracuseStep 1099121 = 824341) B824341
theorem B1099139 : Blo 730325 1099139 := bstep (se 1 (by rfl) ⟨824354, by rfl⟩ : syracuseStep 1099139 = 1648709) B1648709
theorem B836995 : Blo 730325 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B1099169 : Blo 730325 1099169 := bstep (se 2 (by rfl) ⟨412188, by rfl⟩ : syracuseStep 1099169 = 824377) B824377
theorem B1099187 : Blo 730325 1099187 := bstep (se 1 (by rfl) ⟨824390, by rfl⟩ : syracuseStep 1099187 = 1648781) B1648781
theorem B1099217 : Blo 730325 1099217 := bstep (se 2 (by rfl) ⟨412206, by rfl⟩ : syracuseStep 1099217 = 824413) B824413
theorem B1099235 : Blo 730325 1099235 := bstep (se 1 (by rfl) ⟨824426, by rfl⟩ : syracuseStep 1099235 = 1648853) B1648853
theorem B1099265 : Blo 730325 1099265 := bstep (se 2 (by rfl) ⟨412224, by rfl⟩ : syracuseStep 1099265 = 824449) B824449
theorem B1099283 : Blo 730325 1099283 := bstep (se 1 (by rfl) ⟨824462, by rfl⟩ : syracuseStep 1099283 = 1648925) B1648925
theorem B1099313 : Blo 730325 1099313 := bstep (se 2 (by rfl) ⟨412242, by rfl⟩ : syracuseStep 1099313 = 824485) B824485
theorem B1099331 : Blo 730325 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B1099361 : Blo 730325 1099361 := bstep (se 2 (by rfl) ⟨412260, by rfl⟩ : syracuseStep 1099361 = 824521) B824521
theorem B1853027 : Blo 730325 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B2475629 : Blo 730325 2475629 := bstep (se 3 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 2475629 = 928361) B928361
theorem B1099379 : Blo 730325 1099379 := bstep (se 1 (by rfl) ⟨824534, by rfl⟩ : syracuseStep 1099379 = 1649069) B1649069
theorem B1099409 : Blo 730325 1099409 := bstep (se 2 (by rfl) ⟨412278, by rfl⟩ : syracuseStep 1099409 = 824557) B824557
theorem B1099427 : Blo 730325 1099427 := bstep (se 1 (by rfl) ⟨824570, by rfl⟩ : syracuseStep 1099427 = 1649141) B1649141
theorem B2475683 : Blo 730325 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B1099457 : Blo 730325 1099457 := bstep (se 2 (by rfl) ⟨412296, by rfl⟩ : syracuseStep 1099457 = 824593) B824593
theorem B1099475 : Blo 730325 1099475 := bstep (se 1 (by rfl) ⟨824606, by rfl⟩ : syracuseStep 1099475 = 1649213) B1649213
theorem B1099505 : Blo 730325 1099505 := bstep (se 2 (by rfl) ⟨412314, by rfl⟩ : syracuseStep 1099505 = 824629) B824629
theorem B1099523 : Blo 730325 1099523 := bstep (se 1 (by rfl) ⟨824642, by rfl⟩ : syracuseStep 1099523 = 1649285) B1649285
theorem B1099553 : Blo 730325 1099553 := bstep (se 2 (by rfl) ⟨412332, by rfl⟩ : syracuseStep 1099553 = 824665) B824665
theorem B1853219 : Blo 730325 1853219 := bstep (se 1 (by rfl) ⟨1389914, by rfl⟩ : syracuseStep 1853219 = 2779829) B2779829
theorem B1099571 : Blo 730325 1099571 := bstep (se 1 (by rfl) ⟨824678, by rfl⟩ : syracuseStep 1099571 = 1649357) B1649357
theorem B1099601 : Blo 730325 1099601 := bstep (se 2 (by rfl) ⟨412350, by rfl⟩ : syracuseStep 1099601 = 824701) B824701
theorem B1099619 : Blo 730325 1099619 := bstep (se 1 (by rfl) ⟨824714, by rfl⟩ : syracuseStep 1099619 = 1649429) B1649429
theorem B1099649 : Blo 730325 1099649 := bstep (se 2 (by rfl) ⟨412368, by rfl⟩ : syracuseStep 1099649 = 824737) B824737
theorem B1099667 : Blo 730325 1099667 := bstep (se 1 (by rfl) ⟨824750, by rfl⟩ : syracuseStep 1099667 = 1649501) B1649501
theorem B1099697 : Blo 730325 1099697 := bstep (se 2 (by rfl) ⟨412386, by rfl⟩ : syracuseStep 1099697 = 824773) B824773
theorem B2475953 : Blo 730325 2475953 := bstep (se 2 (by rfl) ⟨928482, by rfl⟩ : syracuseStep 2475953 = 1856965) B1856965
theorem B1099715 : Blo 730325 1099715 := bstep (se 1 (by rfl) ⟨824786, by rfl⟩ : syracuseStep 1099715 = 1649573) B1649573
theorem B1099745 : Blo 730325 1099745 := bstep (se 2 (by rfl) ⟨412404, by rfl⟩ : syracuseStep 1099745 = 824809) B824809
theorem B1099763 : Blo 730325 1099763 := bstep (se 1 (by rfl) ⟨824822, by rfl⟩ : syracuseStep 1099763 = 1649645) B1649645
theorem B1099793 : Blo 730325 1099793 := bstep (se 2 (by rfl) ⟨412422, by rfl⟩ : syracuseStep 1099793 = 824845) B824845
theorem B1099811 : Blo 730325 1099811 := bstep (se 1 (by rfl) ⟨824858, by rfl⟩ : syracuseStep 1099811 = 1649717) B1649717
theorem B1099841 : Blo 730325 1099841 := bstep (se 2 (by rfl) ⟨412440, by rfl⟩ : syracuseStep 1099841 = 824881) B824881
theorem B1099859 : Blo 730325 1099859 := bstep (se 1 (by rfl) ⟨824894, by rfl⟩ : syracuseStep 1099859 = 1649789) B1649789
theorem B1099889 : Blo 730325 1099889 := bstep (se 2 (by rfl) ⟨412458, by rfl⟩ : syracuseStep 1099889 = 824917) B824917
theorem B1099907 : Blo 730325 1099907 := bstep (se 1 (by rfl) ⟨824930, by rfl⟩ : syracuseStep 1099907 = 1649861) B1649861
theorem B1099937 : Blo 730325 1099937 := bstep (se 2 (by rfl) ⟨412476, by rfl⟩ : syracuseStep 1099937 = 824953) B824953
theorem B4704419 : Blo 730325 4704419 := bstep (se 1 (by rfl) ⟨3528314, by rfl⟩ : syracuseStep 4704419 = 7056629) B7056629
theorem B1099955 : Blo 730325 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B8472757 : Blo 730325 8472757 := bstep (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) B794321
theorem B1099985 : Blo 730325 1099985 := bstep (se 2 (by rfl) ⟨412494, by rfl⟩ : syracuseStep 1099985 = 824989) B824989
theorem B1100003 : Blo 730325 1100003 := bstep (se 1 (by rfl) ⟨825002, by rfl⟩ : syracuseStep 1100003 = 1650005) B1650005
theorem B1100033 : Blo 730325 1100033 := bstep (se 2 (by rfl) ⟨412512, by rfl⟩ : syracuseStep 1100033 = 825025) B825025
theorem B1100051 : Blo 730325 1100051 := bstep (se 1 (by rfl) ⟨825038, by rfl⟩ : syracuseStep 1100051 = 1650077) B1650077
theorem B1100081 : Blo 730325 1100081 := bstep (se 2 (by rfl) ⟨412530, by rfl⟩ : syracuseStep 1100081 = 825061) B825061
theorem B1100099 : Blo 730325 1100099 := bstep (se 1 (by rfl) ⟨825074, by rfl⟩ : syracuseStep 1100099 = 1650149) B1650149
theorem B1100129 : Blo 730325 1100129 := bstep (se 2 (by rfl) ⟨412548, by rfl⟩ : syracuseStep 1100129 = 825097) B825097
theorem B1100147 : Blo 730325 1100147 := bstep (se 1 (by rfl) ⟨825110, by rfl⟩ : syracuseStep 1100147 = 1650221) B1650221
theorem B1100177 : Blo 730325 1100177 := bstep (se 2 (by rfl) ⟨412566, by rfl⟩ : syracuseStep 1100177 = 825133) B825133
theorem B1100195 : Blo 730325 1100195 := bstep (se 1 (by rfl) ⟨825146, by rfl⟩ : syracuseStep 1100195 = 1650293) B1650293
theorem B1100225 : Blo 730325 1100225 := bstep (se 2 (by rfl) ⟨412584, by rfl⟩ : syracuseStep 1100225 = 825169) B825169
theorem B2476493 : Blo 730325 2476493 := bstep (se 3 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 2476493 = 928685) B928685
theorem B1100243 : Blo 730325 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B1100273 : Blo 730325 1100273 := bstep (se 2 (by rfl) ⟨412602, by rfl⟩ : syracuseStep 1100273 = 825205) B825205
theorem B1100291 : Blo 730325 1100291 := bstep (se 1 (by rfl) ⟨825218, by rfl⟩ : syracuseStep 1100291 = 1650437) B1650437
theorem B2476547 : Blo 730325 2476547 := bstep (se 1 (by rfl) ⟨1857410, by rfl⟩ : syracuseStep 2476547 = 3714821) B3714821
theorem B1100321 : Blo 730325 1100321 := bstep (se 2 (by rfl) ⟨412620, by rfl⟩ : syracuseStep 1100321 = 825241) B825241
theorem B4999715 : Blo 730325 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B2345507 : Blo 730325 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B1100339 : Blo 730325 1100339 := bstep (se 1 (by rfl) ⟨825254, by rfl⟩ : syracuseStep 1100339 = 1650509) B1650509
theorem B15026741 : Blo 730325 15026741 := bstep (se 5 (by rfl) ⟨704378, by rfl⟩ : syracuseStep 15026741 = 1408757) B1408757
theorem B1100369 : Blo 730325 1100369 := bstep (se 2 (by rfl) ⟨412638, by rfl⟩ : syracuseStep 1100369 = 825277) B825277
theorem B1100387 : Blo 730325 1100387 := bstep (se 1 (by rfl) ⟨825290, by rfl⟩ : syracuseStep 1100387 = 1650581) B1650581
theorem B1100417 : Blo 730325 1100417 := bstep (se 2 (by rfl) ⟨412656, by rfl⟩ : syracuseStep 1100417 = 825313) B825313
theorem B1100435 : Blo 730325 1100435 := bstep (se 1 (by rfl) ⟨825326, by rfl⟩ : syracuseStep 1100435 = 1650653) B1650653
theorem B1100465 : Blo 730325 1100465 := bstep (se 2 (by rfl) ⟨412674, by rfl⟩ : syracuseStep 1100465 = 825349) B825349
theorem B1100483 : Blo 730325 1100483 := bstep (se 1 (by rfl) ⟨825362, by rfl⟩ : syracuseStep 1100483 = 1650725) B1650725
theorem B1854161 : Blo 730325 1854161 := bstep (se 2 (by rfl) ⟨695310, by rfl⟩ : syracuseStep 1854161 = 1390621) B1390621
theorem B1100513 : Blo 730325 1100513 := bstep (se 2 (by rfl) ⟨412692, by rfl⟩ : syracuseStep 1100513 = 825385) B825385
theorem B1100531 : Blo 730325 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1854211 : Blo 730325 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B1100561 : Blo 730325 1100561 := bstep (se 2 (by rfl) ⟨412710, by rfl⟩ : syracuseStep 1100561 = 825421) B825421
theorem B2476817 : Blo 730325 2476817 := bstep (se 2 (by rfl) ⟨928806, by rfl⟩ : syracuseStep 2476817 = 1857613) B1857613
theorem B2083619 : Blo 730325 2083619 := bstep (se 1 (by rfl) ⟨1562714, by rfl⟩ : syracuseStep 2083619 = 3125429) B3125429
theorem B1100579 : Blo 730325 1100579 := bstep (se 1 (by rfl) ⟨825434, by rfl⟩ : syracuseStep 1100579 = 1650869) B1650869
theorem B1100609 : Blo 730325 1100609 := bstep (se 2 (by rfl) ⟨412728, by rfl⟩ : syracuseStep 1100609 = 825457) B825457
theorem B1100627 : Blo 730325 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B1100657 : Blo 730325 1100657 := bstep (se 2 (by rfl) ⟨412746, by rfl⟩ : syracuseStep 1100657 = 825493) B825493
theorem B1100675 : Blo 730325 1100675 := bstep (se 1 (by rfl) ⟨825506, by rfl⟩ : syracuseStep 1100675 = 1651013) B1651013
theorem B1854353 : Blo 730325 1854353 := bstep (se 2 (by rfl) ⟨695382, by rfl⟩ : syracuseStep 1854353 = 1390765) B1390765
theorem B1100705 : Blo 730325 1100705 := bstep (se 2 (by rfl) ⟨412764, by rfl⟩ : syracuseStep 1100705 = 825529) B825529
theorem B1100723 : Blo 730325 1100723 := bstep (se 1 (by rfl) ⟨825542, by rfl⟩ : syracuseStep 1100723 = 1651085) B1651085
theorem B2411473 : Blo 730325 2411473 := bstep (se 2 (by rfl) ⟨904302, by rfl⟩ : syracuseStep 2411473 = 1808605) B1808605
theorem B1100753 : Blo 730325 1100753 := bstep (se 2 (by rfl) ⟨412782, by rfl⟩ : syracuseStep 1100753 = 825565) B825565
theorem B1100771 : Blo 730325 1100771 := bstep (se 1 (by rfl) ⟨825578, by rfl⟩ : syracuseStep 1100771 = 1651157) B1651157
theorem B1100801 : Blo 730325 1100801 := bstep (se 2 (by rfl) ⟨412800, by rfl⟩ : syracuseStep 1100801 = 825601) B825601
theorem B4180997 : Blo 730325 4180997 := bstep (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) B783937
theorem B1100819 : Blo 730325 1100819 := bstep (se 1 (by rfl) ⟨825614, by rfl⟩ : syracuseStep 1100819 = 1651229) B1651229
theorem B1100849 : Blo 730325 1100849 := bstep (se 2 (by rfl) ⟨412818, by rfl⟩ : syracuseStep 1100849 = 825637) B825637
theorem B1100867 : Blo 730325 1100867 := bstep (se 1 (by rfl) ⟨825650, by rfl⟩ : syracuseStep 1100867 = 1651301) B1651301
theorem B1100897 : Blo 730325 1100897 := bstep (se 2 (by rfl) ⟨412836, by rfl⟩ : syracuseStep 1100897 = 825673) B825673
theorem B2346097 : Blo 730325 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B1100915 : Blo 730325 1100915 := bstep (se 1 (by rfl) ⟨825686, by rfl⟩ : syracuseStep 1100915 = 1651373) B1651373
theorem B2509955 : Blo 730325 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B1100945 : Blo 730325 1100945 := bstep (se 2 (by rfl) ⟨412854, by rfl⟩ : syracuseStep 1100945 = 825709) B825709
theorem B1100963 : Blo 730325 1100963 := bstep (se 1 (by rfl) ⟨825722, by rfl⟩ : syracuseStep 1100963 = 1651445) B1651445
theorem B1100993 : Blo 730325 1100993 := bstep (se 2 (by rfl) ⟨412872, by rfl⟩ : syracuseStep 1100993 = 825745) B825745
theorem B1101011 : Blo 730325 1101011 := bstep (se 1 (by rfl) ⟨825758, by rfl⟩ : syracuseStep 1101011 = 1651517) B1651517
theorem B1101041 : Blo 730325 1101041 := bstep (se 2 (by rfl) ⟨412890, by rfl⟩ : syracuseStep 1101041 = 825781) B825781
theorem B1101059 : Blo 730325 1101059 := bstep (se 1 (by rfl) ⟨825794, by rfl⟩ : syracuseStep 1101059 = 1651589) B1651589
theorem B1101089 : Blo 730325 1101089 := bstep (se 2 (by rfl) ⟨412908, by rfl⟩ : syracuseStep 1101089 = 825817) B825817
theorem B2477357 : Blo 730325 2477357 := bstep (se 3 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 2477357 = 929009) B929009
theorem B1101107 : Blo 730325 1101107 := bstep (se 1 (by rfl) ⟨825830, by rfl⟩ : syracuseStep 1101107 = 1651661) B1651661
theorem B1101137 : Blo 730325 1101137 := bstep (se 2 (by rfl) ⟨412926, by rfl⟩ : syracuseStep 1101137 = 825853) B825853
theorem B2477411 : Blo 730325 2477411 := bstep (se 1 (by rfl) ⟨1858058, by rfl⟩ : syracuseStep 2477411 = 3716117) B3716117
theorem B1101155 : Blo 730325 1101155 := bstep (se 1 (by rfl) ⟨825866, by rfl⟩ : syracuseStep 1101155 = 1651733) B1651733
theorem B6016369 : Blo 730325 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B1101185 : Blo 730325 1101185 := bstep (se 2 (by rfl) ⟨412944, by rfl⟩ : syracuseStep 1101185 = 825889) B825889
theorem B1101203 : Blo 730325 1101203 := bstep (se 1 (by rfl) ⟨825902, by rfl⟩ : syracuseStep 1101203 = 1651805) B1651805
theorem B1101233 : Blo 730325 1101233 := bstep (se 2 (by rfl) ⟨412962, by rfl⟩ : syracuseStep 1101233 = 825925) B825925
theorem B1101251 : Blo 730325 1101251 := bstep (se 1 (by rfl) ⟨825938, by rfl⟩ : syracuseStep 1101251 = 1651877) B1651877
theorem B4181453 : Blo 730325 4181453 := bstep (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) B1568045
theorem B1101281 : Blo 730325 1101281 := bstep (se 2 (by rfl) ⟨412980, by rfl⟩ : syracuseStep 1101281 = 825961) B825961
theorem B1101299 : Blo 730325 1101299 := bstep (se 1 (by rfl) ⟨825974, by rfl⟩ : syracuseStep 1101299 = 1651949) B1651949
theorem B1101329 : Blo 730325 1101329 := bstep (se 2 (by rfl) ⟨412998, by rfl⟩ : syracuseStep 1101329 = 825997) B825997
theorem B1101347 : Blo 730325 1101347 := bstep (se 1 (by rfl) ⟨826010, by rfl⟩ : syracuseStep 1101347 = 1652021) B1652021
theorem B1232435 : Blo 730325 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B1101377 : Blo 730325 1101377 := bstep (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) B826033
theorem B1101395 : Blo 730325 1101395 := bstep (se 1 (by rfl) ⟨826046, by rfl⟩ : syracuseStep 1101395 = 1652093) B1652093
theorem B2477681 : Blo 730325 2477681 := bstep (se 2 (by rfl) ⟨929130, by rfl⟩ : syracuseStep 2477681 = 1858261) B1858261
theorem B1101425 : Blo 730325 1101425 := bstep (se 2 (by rfl) ⟨413034, by rfl⟩ : syracuseStep 1101425 = 826069) B826069
theorem B1101443 : Blo 730325 1101443 := bstep (se 1 (by rfl) ⟨826082, by rfl⟩ : syracuseStep 1101443 = 1652165) B1652165
theorem B1101473 : Blo 730325 1101473 := bstep (se 2 (by rfl) ⟨413052, by rfl⟩ : syracuseStep 1101473 = 826105) B826105
theorem B1232563 : Blo 730325 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B1560323 : Blo 730325 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1232705 : Blo 730325 1232705 := bstep (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) B924529
theorem B1855345 : Blo 730325 1855345 := bstep (se 2 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 1855345 = 1391509) B1391509
theorem B1232833 : Blo 730325 1232833 := bstep (se 2 (by rfl) ⟨462312, by rfl⟩ : syracuseStep 1232833 = 924625) B924625
theorem B1232867 : Blo 730325 1232867 := bstep (se 1 (by rfl) ⟨924650, by rfl⟩ : syracuseStep 1232867 = 1849301) B1849301
theorem B2084849 : Blo 730325 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B2969635 : Blo 730325 2969635 := bstep (se 1 (by rfl) ⟨2227226, by rfl⟩ : syracuseStep 2969635 = 4454453) B4454453
theorem B1232995 : Blo 730325 1232995 := bstep (se 1 (by rfl) ⟨924746, by rfl⟩ : syracuseStep 1232995 = 1849493) B1849493
theorem B1757315 : Blo 730325 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1855619 : Blo 730325 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B2478221 : Blo 730325 2478221 := bstep (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) B929333
theorem B2478275 : Blo 730325 2478275 := bstep (se 1 (by rfl) ⟨1858706, by rfl⟩ : syracuseStep 2478275 = 3717413) B3717413
theorem B1233137 : Blo 730325 1233137 := bstep (se 2 (by rfl) ⟨462426, by rfl⟩ : syracuseStep 1233137 = 924853) B924853
theorem B1855811 : Blo 730325 1855811 := bstep (se 1 (by rfl) ⟨1391858, by rfl⟩ : syracuseStep 1855811 = 2783717) B2783717
theorem B1233265 : Blo 730325 1233265 := bstep (se 2 (by rfl) ⟨462474, by rfl⟩ : syracuseStep 1233265 = 924949) B924949
theorem B1233299 : Blo 730325 1233299 := bstep (se 1 (by rfl) ⟨924974, by rfl⟩ : syracuseStep 1233299 = 1849949) B1849949
theorem B1233427 : Blo 730325 1233427 := bstep (se 1 (by rfl) ⟨925070, by rfl⟩ : syracuseStep 1233427 = 1850141) B1850141
theorem B8344133 : Blo 730325 8344133 := bstep (se 4 (by rfl) ⟨782262, by rfl⟩ : syracuseStep 8344133 = 1564525) B1564525
theorem B1561169 : Blo 730325 1561169 := bstep (se 2 (by rfl) ⟨585438, by rfl⟩ : syracuseStep 1561169 = 1170877) B1170877
theorem B1233569 : Blo 730325 1233569 := bstep (se 2 (by rfl) ⟨462588, by rfl⟩ : syracuseStep 1233569 = 925177) B925177
theorem B2773709 : Blo 730325 2773709 := bstep (se 3 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 2773709 = 1040141) B1040141
theorem B1233697 : Blo 730325 1233697 := bstep (se 2 (by rfl) ⟨462636, by rfl⟩ : syracuseStep 1233697 = 925273) B925273
theorem B1233731 : Blo 730325 1233731 := bstep (se 1 (by rfl) ⟨925298, by rfl⟩ : syracuseStep 1233731 = 1850597) B1850597
theorem B19059569 : Blo 730325 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B1233859 : Blo 730325 1233859 := bstep (se 1 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 1233859 = 1850789) B1850789
theorem B1758161 : Blo 730325 1758161 := bstep (se 2 (by rfl) ⟨659310, by rfl⟩ : syracuseStep 1758161 = 1318621) B1318621
theorem B1234001 : Blo 730325 1234001 := bstep (se 2 (by rfl) ⟨462750, by rfl⟩ : syracuseStep 1234001 = 925501) B925501
theorem B742483 : Blo 730325 742483 := bstep (se 1 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 742483 = 1113725) B1113725
theorem B1234129 : Blo 730325 1234129 := bstep (se 2 (by rfl) ⟨462798, by rfl⟩ : syracuseStep 1234129 = 925597) B925597
theorem B1692881 : Blo 730325 1692881 := bstep (se 2 (by rfl) ⟨634830, by rfl⟩ : syracuseStep 1692881 = 1269661) B1269661
theorem B3953891 : Blo 730325 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B1856753 : Blo 730325 1856753 := bstep (se 2 (by rfl) ⟨696282, by rfl⟩ : syracuseStep 1856753 = 1392565) B1392565
theorem B1234163 : Blo 730325 1234163 := bstep (se 1 (by rfl) ⟨925622, by rfl⟩ : syracuseStep 1234163 = 1851245) B1851245
theorem B1856803 : Blo 730325 1856803 := bstep (se 1 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 1856803 = 2785205) B2785205
theorem B1234291 : Blo 730325 1234291 := bstep (se 1 (by rfl) ⟨925718, by rfl⟩ : syracuseStep 1234291 = 1851437) B1851437
theorem B3134861 : Blo 730325 3134861 := bstep (se 3 (by rfl) ⟨587786, by rfl⟩ : syracuseStep 3134861 = 1175573) B1175573
theorem B2086307 : Blo 730325 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B1856945 : Blo 730325 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B2774513 : Blo 730325 2774513 := bstep (se 2 (by rfl) ⟨1040442, by rfl⟩ : syracuseStep 2774513 = 2080885) B2080885
theorem B1234433 : Blo 730325 1234433 := bstep (se 2 (by rfl) ⟨462912, by rfl⟩ : syracuseStep 1234433 = 925825) B925825
theorem B1234561 : Blo 730325 1234561 := bstep (se 2 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 1234561 = 925921) B925921
theorem B1234595 : Blo 730325 1234595 := bstep (se 1 (by rfl) ⟨925946, by rfl⟩ : syracuseStep 1234595 = 1851893) B1851893
theorem B1234723 : Blo 730325 1234723 := bstep (se 1 (by rfl) ⟨926042, by rfl⟩ : syracuseStep 1234723 = 1852085) B1852085
theorem B2348941 : Blo 730325 2348941 := bstep (se 3 (by rfl) ⟨440426, by rfl⟩ : syracuseStep 2348941 = 880853) B880853
theorem B1234865 : Blo 730325 1234865 := bstep (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) B926149
theorem B1234993 : Blo 730325 1234993 := bstep (se 2 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 1234993 = 926245) B926245
theorem B1235027 : Blo 730325 1235027 := bstep (se 1 (by rfl) ⟨926270, by rfl⟩ : syracuseStep 1235027 = 1852541) B1852541
theorem B2775181 : Blo 730325 2775181 := bstep (se 3 (by rfl) ⟨520346, by rfl⟩ : syracuseStep 2775181 = 1040693) B1040693
theorem B2087117 : Blo 730325 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B1235155 : Blo 730325 1235155 := bstep (se 1 (by rfl) ⟨926366, by rfl⟩ : syracuseStep 1235155 = 1852733) B1852733
theorem B1562851 : Blo 730325 1562851 := bstep (se 1 (by rfl) ⟨1172138, by rfl⟩ : syracuseStep 1562851 = 2344277) B2344277
theorem B1235297 : Blo 730325 1235297 := bstep (se 2 (by rfl) ⟨463236, by rfl⟩ : syracuseStep 1235297 = 926473) B926473
theorem B9525617 : Blo 730325 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B2087309 : Blo 730325 2087309 := bstep (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) B782741
theorem B1857937 : Blo 730325 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B1235425 : Blo 730325 1235425 := bstep (se 2 (by rfl) ⟨463284, by rfl⟩ : syracuseStep 1235425 = 926569) B926569
theorem B1235459 : Blo 730325 1235459 := bstep (se 1 (by rfl) ⟨926594, by rfl⟩ : syracuseStep 1235459 = 1853189) B1853189
theorem B1235587 : Blo 730325 1235587 := bstep (se 1 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 1235587 = 1853381) B1853381
theorem B1858211 : Blo 730325 1858211 := bstep (se 1 (by rfl) ⟨1393658, by rfl⟩ : syracuseStep 1858211 = 2787317) B2787317
theorem B1563313 : Blo 730325 1563313 := bstep (se 2 (by rfl) ⟨586242, by rfl⟩ : syracuseStep 1563313 = 1172485) B1172485
theorem B1235729 : Blo 730325 1235729 := bstep (se 2 (by rfl) ⟨463398, by rfl⟩ : syracuseStep 1235729 = 926797) B926797
theorem B1334065 : Blo 730325 1334065 := bstep (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) B1000549
theorem B744275 : Blo 730325 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B1858403 : Blo 730325 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B1235857 : Blo 730325 1235857 := bstep (se 2 (by rfl) ⟨463446, by rfl⟩ : syracuseStep 1235857 = 926893) B926893
theorem B2775971 : Blo 730325 2775971 := bstep (se 1 (by rfl) ⟨2081978, by rfl⟩ : syracuseStep 2775971 = 4163957) B4163957
theorem B1235891 : Blo 730325 1235891 := bstep (se 1 (by rfl) ⟨926918, by rfl⟩ : syracuseStep 1235891 = 1853837) B1853837
theorem B1334225 : Blo 730325 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B2382851 : Blo 730325 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B1170467 : Blo 730325 1170467 := bstep (se 1 (by rfl) ⟨877850, by rfl⟩ : syracuseStep 1170467 = 1755701) B1755701
theorem B5069873 : Blo 730325 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1236019 : Blo 730325 1236019 := bstep (se 1 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 1236019 = 1854029) B1854029
theorem B1072211 : Blo 730325 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1236161 : Blo 730325 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B14277829 : Blo 730325 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B1236289 : Blo 730325 1236289 := bstep (se 2 (by rfl) ⟨463608, by rfl⟩ : syracuseStep 1236289 = 927217) B927217
theorem B2350403 : Blo 730325 2350403 := bstep (se 1 (by rfl) ⟨1762802, by rfl⟩ : syracuseStep 2350403 = 3525605) B3525605
theorem B1236323 : Blo 730325 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B2088301 : Blo 730325 2088301 := bstep (se 3 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 2088301 = 783113) B783113
theorem B3562957 : Blo 730325 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1236451 : Blo 730325 1236451 := bstep (se 1 (by rfl) ⟨927338, by rfl⟩ : syracuseStep 1236451 = 1854677) B1854677
theorem B1039873 : Blo 730325 1039873 := bstep (se 2 (by rfl) ⟨389952, by rfl⟩ : syracuseStep 1039873 = 779905) B779905
theorem B2776625 : Blo 730325 2776625 := bstep (se 2 (by rfl) ⟨1041234, by rfl⟩ : syracuseStep 2776625 = 2082469) B2082469
theorem B3956273 : Blo 730325 3956273 := bstep (se 2 (by rfl) ⟨1483602, by rfl⟩ : syracuseStep 3956273 = 2967205) B2967205
theorem B1236593 : Blo 730325 1236593 := bstep (se 2 (by rfl) ⟨463722, by rfl⟩ : syracuseStep 1236593 = 927445) B927445
theorem B1039987 : Blo 730325 1039987 := bstep (se 1 (by rfl) ⟨779990, by rfl⟩ : syracuseStep 1039987 = 1559981) B1559981
theorem B1564355 : Blo 730325 1564355 := bstep (se 1 (by rfl) ⟨1173266, by rfl⟩ : syracuseStep 1564355 = 2346533) B2346533
theorem B1236721 : Blo 730325 1236721 := bstep (se 2 (by rfl) ⟨463770, by rfl⟩ : syracuseStep 1236721 = 927541) B927541
theorem B1269521 : Blo 730325 1269521 := bstep (se 2 (by rfl) ⟨476070, by rfl⟩ : syracuseStep 1269521 = 952141) B952141
theorem B1236755 : Blo 730325 1236755 := bstep (se 1 (by rfl) ⟨927566, by rfl⟩ : syracuseStep 1236755 = 1855133) B1855133
theorem B1236883 : Blo 730325 1236883 := bstep (se 1 (by rfl) ⟨927662, by rfl⟩ : syracuseStep 1236883 = 1855325) B1855325
theorem B1237025 : Blo 730325 1237025 := bstep (se 2 (by rfl) ⟨463884, by rfl⟩ : syracuseStep 1237025 = 927769) B927769
theorem B1237153 : Blo 730325 1237153 := bstep (se 2 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 1237153 = 927865) B927865
theorem B1564867 : Blo 730325 1564867 := bstep (se 1 (by rfl) ⟨1173650, by rfl⟩ : syracuseStep 1564867 = 2347301) B2347301
theorem B1761475 : Blo 730325 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B1237187 : Blo 730325 1237187 := bstep (se 1 (by rfl) ⟨927890, by rfl⟩ : syracuseStep 1237187 = 1855781) B1855781
theorem B1237315 : Blo 730325 1237315 := bstep (se 1 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 1237315 = 1855973) B1855973
theorem B1171921 : Blo 730325 1171921 := bstep (se 2 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 1171921 = 878941) B878941
theorem B1761745 : Blo 730325 1761745 := bstep (se 2 (by rfl) ⟨660654, by rfl⟩ : syracuseStep 1761745 = 1321309) B1321309
theorem B1237457 : Blo 730325 1237457 := bstep (se 2 (by rfl) ⟨464046, by rfl⟩ : syracuseStep 1237457 = 928093) B928093
theorem B2712113 : Blo 730325 2712113 := bstep (se 2 (by rfl) ⟨1017042, by rfl⟩ : syracuseStep 2712113 = 2034085) B2034085
theorem B1237585 : Blo 730325 1237585 := bstep (se 2 (by rfl) ⟨464094, by rfl⟩ : syracuseStep 1237585 = 928189) B928189
theorem B1237619 : Blo 730325 1237619 := bstep (se 1 (by rfl) ⟨928214, by rfl⟩ : syracuseStep 1237619 = 1856429) B1856429
theorem B1237747 : Blo 730325 1237747 := bstep (se 1 (by rfl) ⟨928310, by rfl⟩ : syracuseStep 1237747 = 1856621) B1856621
theorem B1237889 : Blo 730325 1237889 := bstep (se 2 (by rfl) ⟨464208, by rfl⟩ : syracuseStep 1237889 = 928417) B928417
theorem B1565585 : Blo 730325 1565585 := bstep (se 2 (by rfl) ⟨587094, by rfl⟩ : syracuseStep 1565585 = 1174189) B1174189
theorem B2352017 : Blo 730325 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B1041331 : Blo 730325 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B2778083 : Blo 730325 2778083 := bstep (se 1 (by rfl) ⟨2083562, by rfl⟩ : syracuseStep 2778083 = 4167125) B4167125
theorem B2778097 : Blo 730325 2778097 := bstep (se 2 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 2778097 = 2083573) B2083573
theorem B1238017 : Blo 730325 1238017 := bstep (se 2 (by rfl) ⟨464256, by rfl⟩ : syracuseStep 1238017 = 928513) B928513
theorem B1238051 : Blo 730325 1238051 := bstep (se 1 (by rfl) ⟨928538, by rfl⟩ : syracuseStep 1238051 = 1857077) B1857077
theorem B2090033 : Blo 730325 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1238179 : Blo 730325 1238179 := bstep (se 1 (by rfl) ⟨928634, by rfl⟩ : syracuseStep 1238179 = 1857269) B1857269
theorem B7496945 : Blo 730325 7496945 := bstep (se 2 (by rfl) ⟨2811354, by rfl⟩ : syracuseStep 7496945 = 5622709) B5622709
theorem B2090225 : Blo 730325 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B1238321 : Blo 730325 1238321 := bstep (se 2 (by rfl) ⟨464370, by rfl⟩ : syracuseStep 1238321 = 928741) B928741
theorem B1762705 : Blo 730325 1762705 := bstep (se 2 (by rfl) ⟨661014, by rfl⟩ : syracuseStep 1762705 = 1322029) B1322029
theorem B1238449 : Blo 730325 1238449 := bstep (se 2 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 1238449 = 928837) B928837
theorem B1238483 : Blo 730325 1238483 := bstep (se 1 (by rfl) ⟨928862, by rfl⟩ : syracuseStep 1238483 = 1857725) B1857725
theorem B1336867 : Blo 730325 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B1238611 : Blo 730325 1238611 := bstep (se 1 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 1238611 = 1857917) B1857917
theorem B2221681 : Blo 730325 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B1566371 : Blo 730325 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B2221777 : Blo 730325 2221777 := bstep (se 2 (by rfl) ⟨833166, by rfl⟩ : syracuseStep 2221777 = 1666333) B1666333
theorem B1238753 : Blo 730325 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B2975459 : Blo 730325 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B1238881 : Blo 730325 1238881 := bstep (se 2 (by rfl) ⟨464580, by rfl⟩ : syracuseStep 1238881 = 929161) B929161
theorem B14444401 : Blo 730325 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B1238915 : Blo 730325 1238915 := bstep (se 1 (by rfl) ⟨929186, by rfl⟩ : syracuseStep 1238915 = 1858373) B1858373
theorem B1239043 : Blo 730325 1239043 := bstep (se 1 (by rfl) ⟨929282, by rfl⟩ : syracuseStep 1239043 = 1858565) B1858565
theorem B1173523 : Blo 730325 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1042465 : Blo 730325 1042465 := bstep (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) B781849
theorem B1042561 : Blo 730325 1042561 := bstep (se 2 (by rfl) ⟨390960, by rfl⟩ : syracuseStep 1042561 = 781921) B781921
theorem B9038051 : Blo 730325 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B8349965 : Blo 730325 8349965 := bstep (se 3 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 8349965 = 3131237) B3131237
theorem B780563 : Blo 730325 780563 := bstep (se 1 (by rfl) ⟨585422, by rfl⟩ : syracuseStep 780563 = 1170845) B1170845
theorem B1173779 : Blo 730325 1173779 := bstep (se 1 (by rfl) ⟨880334, by rfl⟩ : syracuseStep 1173779 = 1760669) B1760669
theorem B846163 : Blo 730325 846163 := bstep (se 1 (by rfl) ⟨634622, by rfl⟩ : syracuseStep 846163 = 1269245) B1269245
theorem B2779555 : Blo 730325 2779555 := bstep (se 1 (by rfl) ⟨2084666, by rfl⟩ : syracuseStep 2779555 = 4169333) B4169333
theorem B1173971 : Blo 730325 1173971 := bstep (se 1 (by rfl) ⟨880478, by rfl⟩ : syracuseStep 1173971 = 1760957) B1760957
theorem B2812429 : Blo 730325 2812429 := bstep (se 3 (by rfl) ⟨527330, by rfl⟩ : syracuseStep 2812429 = 1054661) B1054661
theorem B1043057 : Blo 730325 1043057 := bstep (se 2 (by rfl) ⟨391146, by rfl⟩ : syracuseStep 1043057 = 782293) B782293
theorem B1567345 : Blo 730325 1567345 := bstep (se 2 (by rfl) ⟨587754, by rfl⟩ : syracuseStep 1567345 = 1175509) B1175509
theorem B1665713 : Blo 730325 1665713 := bstep (se 2 (by rfl) ⟨624642, by rfl⟩ : syracuseStep 1665713 = 1249285) B1249285
theorem B1567601 : Blo 730325 1567601 := bstep (se 2 (by rfl) ⟨587850, by rfl⟩ : syracuseStep 1567601 = 1175701) B1175701
theorem B3697649 : Blo 730325 3697649 := bstep (se 2 (by rfl) ⟨1386618, by rfl⟩ : syracuseStep 3697649 = 2773237) B2773237
theorem B18803825 : Blo 730325 18803825 := bstep (se 2 (by rfl) ⟨7051434, by rfl⟩ : syracuseStep 18803825 = 14102869) B14102869
theorem B1174753 : Blo 730325 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B7498993 : Blo 730325 7498993 := bstep (se 2 (by rfl) ⟨2812122, by rfl⟩ : syracuseStep 7498993 = 5624245) B5624245
theorem B781699 : Blo 730325 781699 := bstep (se 1 (by rfl) ⟨586274, by rfl⟩ : syracuseStep 781699 = 1172549) B1172549
theorem B9530821 : Blo 730325 9530821 := bstep (se 4 (by rfl) ⟨893514, by rfl⟩ : syracuseStep 9530821 = 1787029) B1787029
theorem B1043923 : Blo 730325 1043923 := bstep (se 1 (by rfl) ⟨782942, by rfl⟩ : syracuseStep 1043923 = 1565885) B1565885
theorem B1044019 : Blo 730325 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B2977357 : Blo 730325 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B2223821 : Blo 730325 2223821 := bstep (se 3 (by rfl) ⟨416966, by rfl⟩ : syracuseStep 2223821 = 833933) B833933
theorem B13397957 : Blo 730325 13397957 := bstep (se 4 (by rfl) ⟨1256058, by rfl⟩ : syracuseStep 13397957 = 2512117) B2512117
theorem B10547171 : Blo 730325 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B1044515 : Blo 730325 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B5009507 : Blo 730325 5009507 := bstep (se 1 (by rfl) ⟨3757130, by rfl⟩ : syracuseStep 5009507 = 7514261) B7514261
theorem B782579 : Blo 730325 782579 := bstep (se 1 (by rfl) ⟨586934, by rfl⟩ : syracuseStep 782579 = 1173869) B1173869
theorem B782707 : Blo 730325 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B3699107 : Blo 730325 3699107 := bstep (se 1 (by rfl) ⟨2774330, by rfl⟩ : syracuseStep 3699107 = 5548661) B5548661
theorem B2224589 : Blo 730325 2224589 := bstep (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) B834221
theorem B2781773 : Blo 730325 2781773 := bstep (se 3 (by rfl) ⟨521582, by rfl⟩ : syracuseStep 2781773 = 1043165) B1043165
theorem B1045153 : Blo 730325 1045153 := bstep (se 2 (by rfl) ⟨391932, by rfl⟩ : syracuseStep 1045153 = 783865) B783865
theorem B4453069 : Blo 730325 4453069 := bstep (se 3 (by rfl) ⟨834950, by rfl⟩ : syracuseStep 4453069 = 1669901) B1669901
theorem B4682609 : Blo 730325 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B3961763 : Blo 730325 3961763 := bstep (se 1 (by rfl) ⟨2971322, by rfl⟩ : syracuseStep 3961763 = 5942645) B5942645
theorem B1045489 : Blo 730325 1045489 := bstep (se 2 (by rfl) ⟨392058, by rfl⟩ : syracuseStep 1045489 = 784117) B784117
theorem B8352881 : Blo 730325 8352881 := bstep (se 2 (by rfl) ⟨3132330, by rfl⟩ : syracuseStep 8352881 = 6264661) B6264661
theorem B783523 : Blo 730325 783523 := bstep (se 1 (by rfl) ⟨587642, by rfl⟩ : syracuseStep 783523 = 1175285) B1175285
theorem B3699917 : Blo 730325 3699917 := bstep (se 3 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 3699917 = 1387469) B1387469
theorem B1668323 : Blo 730325 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B9532685 : Blo 730325 9532685 := bstep (se 3 (by rfl) ⟨1787378, by rfl⟩ : syracuseStep 9532685 = 3574757) B3574757
theorem B1111985 : Blo 730325 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B8353763 : Blo 730325 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B7928117 : Blo 730325 7928117 := bstep (se 5 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 7928117 = 743261) B743261
theorem B1505603 : Blo 730325 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B5011973 : Blo 730325 5011973 := bstep (se 4 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 5011973 = 939745) B939745
theorem B2849293 : Blo 730325 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B7043597 : Blo 730325 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B2227085 : Blo 730325 2227085 := bstep (se 3 (by rfl) ⟨417578, by rfl⟩ : syracuseStep 2227085 = 835157) B835157
theorem B5274737 : Blo 730325 5274737 := bstep (se 2 (by rfl) ⟨1978026, by rfl⟩ : syracuseStep 5274737 = 3956053) B3956053
theorem B2227313 : Blo 730325 2227313 := bstep (se 2 (by rfl) ⟨835242, by rfl⟩ : syracuseStep 2227313 = 1670485) B1670485
theorem B2784689 : Blo 730325 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B4521521 : Blo 730325 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B4161293 : Blo 730325 4161293 := bstep (se 3 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 4161293 = 1560485) B1560485
theorem B5570531 : Blo 730325 5570531 := bstep (se 1 (by rfl) ⟨4177898, by rfl⟩ : syracuseStep 5570531 = 8355797) B8355797
theorem B2785373 : Blo 730325 2785373 := bstep (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) B1044515
theorem B38011031 : Blo 730325 38011031 := bstep (se 1 (by rfl) ⟨28508273, by rfl⟩ : syracuseStep 38011031 = 57016547) B57016547
theorem B4686173 : Blo 730325 4686173 := bstep (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) B1757315
theorem B1114649 : Blo 730325 1114649 := bstep (se 2 (by rfl) ⟨417993, by rfl⟩ : syracuseStep 1114649 = 835987) B835987
theorem B1409881 : Blo 730325 1409881 := bstep (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) B1057411
theorem B5932237 : Blo 730325 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B3704129 : Blo 730325 3704129 := bstep (se 2 (by rfl) ⟨1389048, by rfl⟩ : syracuseStep 3704129 = 2778097) B2778097
theorem B1508951 : Blo 730325 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B1115993 : Blo 730325 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B2819933 : Blo 730325 2819933 := bstep (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) B1057475
theorem B2787331 : Blo 730325 2787331 := bstep (se 1 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 2787331 = 4180997) B4180997
theorem B1673303 : Blo 730325 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B2787635 : Blo 730325 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B821623 : Blo 730325 821623 := bstep (se 1 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 821623 = 1232435) B1232435
theorem B821803 : Blo 730325 821803 := bstep (se 1 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 821803 = 1232705) B1232705
theorem B821911 : Blo 730325 821911 := bstep (se 1 (by rfl) ⟨616433, by rfl⟩ : syracuseStep 821911 = 1232867) B1232867
theorem B822091 : Blo 730325 822091 := bstep (se 1 (by rfl) ⟨616568, by rfl⟩ : syracuseStep 822091 = 1233137) B1233137
theorem B2231219 : Blo 730325 2231219 := bstep (se 1 (by rfl) ⟨1673414, by rfl⟩ : syracuseStep 2231219 = 3346829) B3346829
theorem B822199 : Blo 730325 822199 := bstep (se 1 (by rfl) ⟨616649, by rfl⟩ : syracuseStep 822199 = 1233299) B1233299
theorem B822379 : Blo 730325 822379 := bstep (se 1 (by rfl) ⟨616784, by rfl⟩ : syracuseStep 822379 = 1233569) B1233569
theorem B822487 : Blo 730325 822487 := bstep (se 1 (by rfl) ⟨616865, by rfl⟩ : syracuseStep 822487 = 1233731) B1233731
theorem B3706073 : Blo 730325 3706073 := bstep (se 2 (by rfl) ⟨1389777, by rfl⟩ : syracuseStep 3706073 = 2779555) B2779555
theorem B5573933 : Blo 730325 5573933 := bstep (se 3 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 5573933 = 2090225) B2090225
theorem B822667 : Blo 730325 822667 := bstep (se 1 (by rfl) ⟨617000, by rfl⟩ : syracuseStep 822667 = 1234001) B1234001
theorem B822775 : Blo 730325 822775 := bstep (se 1 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 822775 = 1234163) B1234163
theorem B822955 : Blo 730325 822955 := bstep (se 1 (by rfl) ⟨617216, by rfl⟩ : syracuseStep 822955 = 1234433) B1234433
theorem B823063 : Blo 730325 823063 := bstep (se 1 (by rfl) ⟨617297, by rfl⟩ : syracuseStep 823063 = 1234595) B1234595
theorem B2232215 : Blo 730325 2232215 := bstep (se 1 (by rfl) ⟨1674161, by rfl⟩ : syracuseStep 2232215 = 3348323) B3348323
theorem B3215297 : Blo 730325 3215297 := bstep (se 2 (by rfl) ⟨1205736, by rfl⟩ : syracuseStep 3215297 = 2411473) B2411473
theorem B823243 : Blo 730325 823243 := bstep (se 1 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 823243 = 1234865) B1234865
theorem B823351 : Blo 730325 823351 := bstep (se 1 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 823351 = 1235027) B1235027
theorem B823531 : Blo 730325 823531 := bstep (se 1 (by rfl) ⟨617648, by rfl⟩ : syracuseStep 823531 = 1235297) B1235297
theorem B9998657 : Blo 730325 9998657 := bstep (se 2 (by rfl) ⟨3749496, by rfl⟩ : syracuseStep 9998657 = 7498993) B7498993
theorem B823639 : Blo 730325 823639 := bstep (se 1 (by rfl) ⟨617729, by rfl⟩ : syracuseStep 823639 = 1235459) B1235459
theorem B823819 : Blo 730325 823819 := bstep (se 1 (by rfl) ⟨617864, by rfl⟩ : syracuseStep 823819 = 1235729) B1235729
theorem B7934557 : Blo 730325 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B823927 : Blo 730325 823927 := bstep (se 1 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 823927 = 1235891) B1235891
theorem B889483 : Blo 730325 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B3379915 : Blo 730325 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B4166417 : Blo 730325 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B4690705 : Blo 730325 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B3969809 : Blo 730325 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B824107 : Blo 730325 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B3707693 : Blo 730325 3707693 := bstep (se 3 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 3707693 = 1390385) B1390385
theorem B824215 : Blo 730325 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B1643417 : Blo 730325 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B1643507 : Blo 730325 1643507 := bstep (se 1 (by rfl) ⟨1232630, by rfl⟩ : syracuseStep 1643507 = 2465261) B2465261
theorem B1643543 : Blo 730325 1643543 := bstep (se 1 (by rfl) ⟨1232657, by rfl⟩ : syracuseStep 1643543 = 2465315) B2465315
theorem B824395 : Blo 730325 824395 := bstep (se 1 (by rfl) ⟨618296, by rfl⟩ : syracuseStep 824395 = 1236593) B1236593
theorem B988247 : Blo 730325 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B824503 : Blo 730325 824503 := bstep (se 1 (by rfl) ⟨618377, by rfl⟩ : syracuseStep 824503 = 1236755) B1236755
theorem B1643723 : Blo 730325 1643723 := bstep (se 1 (by rfl) ⟨1232792, by rfl⟩ : syracuseStep 1643723 = 2465585) B2465585
theorem B4166873 : Blo 730325 4166873 := bstep (se 2 (by rfl) ⟨1562577, by rfl⟩ : syracuseStep 4166873 = 3125155) B3125155
theorem B1643777 : Blo 730325 1643777 := bstep (se 2 (by rfl) ⟨616416, by rfl⟩ : syracuseStep 1643777 = 1232833) B1232833
theorem B1316147 : Blo 730325 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B824683 : Blo 730325 824683 := bstep (se 1 (by rfl) ⟨618512, by rfl⟩ : syracuseStep 824683 = 1237025) B1237025
theorem B824791 : Blo 730325 824791 := bstep (se 1 (by rfl) ⟨618593, by rfl⟩ : syracuseStep 824791 = 1237187) B1237187
theorem B1643993 : Blo 730325 1643993 := bstep (se 2 (by rfl) ⟨616497, by rfl⟩ : syracuseStep 1643993 = 1232995) B1232995
theorem B1644083 : Blo 730325 1644083 := bstep (se 1 (by rfl) ⟨1233062, by rfl⟩ : syracuseStep 1644083 = 2466125) B2466125
theorem B1644119 : Blo 730325 1644119 := bstep (se 1 (by rfl) ⟨1233089, by rfl⟩ : syracuseStep 1644119 = 2466179) B2466179
theorem B824971 : Blo 730325 824971 := bstep (se 1 (by rfl) ⟨618728, by rfl⟩ : syracuseStep 824971 = 1237457) B1237457
theorem B1808075 : Blo 730325 1808075 := bstep (se 1 (by rfl) ⟨1356056, by rfl⟩ : syracuseStep 1808075 = 2712113) B2712113
theorem B1316567 : Blo 730325 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B825079 : Blo 730325 825079 := bstep (se 1 (by rfl) ⟨618809, by rfl⟩ : syracuseStep 825079 = 1237619) B1237619
theorem B1644299 : Blo 730325 1644299 := bstep (se 1 (by rfl) ⟨1233224, by rfl⟩ : syracuseStep 1644299 = 2466449) B2466449
theorem B1644353 : Blo 730325 1644353 := bstep (se 2 (by rfl) ⟨616632, by rfl⟩ : syracuseStep 1644353 = 1233265) B1233265
theorem B825259 : Blo 730325 825259 := bstep (se 1 (by rfl) ⟨618944, by rfl⟩ : syracuseStep 825259 = 1237889) B1237889
theorem B825367 : Blo 730325 825367 := bstep (se 1 (by rfl) ⟨619025, by rfl⟩ : syracuseStep 825367 = 1238051) B1238051
theorem B1644569 : Blo 730325 1644569 := bstep (se 2 (by rfl) ⟨616713, by rfl⟩ : syracuseStep 1644569 = 1233427) B1233427
theorem B6330469 : Blo 730325 6330469 := bstep (se 4 (by rfl) ⟨593481, by rfl⟩ : syracuseStep 6330469 = 1186963) B1186963
theorem B1644659 : Blo 730325 1644659 := bstep (se 1 (by rfl) ⟨1233494, by rfl⟩ : syracuseStep 1644659 = 2466989) B2466989
theorem B1644695 : Blo 730325 1644695 := bstep (se 1 (by rfl) ⟨1233521, by rfl⟩ : syracuseStep 1644695 = 2467043) B2467043
theorem B825547 : Blo 730325 825547 := bstep (se 1 (by rfl) ⟨619160, by rfl⟩ : syracuseStep 825547 = 1238321) B1238321
theorem B5937425 : Blo 730325 5937425 := bstep (se 2 (by rfl) ⟨2226534, by rfl⟩ : syracuseStep 5937425 = 4453069) B4453069
theorem B825655 : Blo 730325 825655 := bstep (se 1 (by rfl) ⟨619241, by rfl⟩ : syracuseStep 825655 = 1238483) B1238483
theorem B1644875 : Blo 730325 1644875 := bstep (se 1 (by rfl) ⟨1233656, by rfl⟩ : syracuseStep 1644875 = 2467313) B2467313
theorem B1644929 : Blo 730325 1644929 := bstep (se 2 (by rfl) ⟨616848, by rfl⟩ : syracuseStep 1644929 = 1233697) B1233697
theorem B825835 : Blo 730325 825835 := bstep (se 1 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 825835 = 1238753) B1238753
theorem B825943 : Blo 730325 825943 := bstep (se 1 (by rfl) ⟨619457, by rfl⟩ : syracuseStep 825943 = 1238915) B1238915
theorem B1645145 : Blo 730325 1645145 := bstep (se 2 (by rfl) ⟨616929, by rfl⟩ : syracuseStep 1645145 = 1233859) B1233859
theorem B1645235 : Blo 730325 1645235 := bstep (se 1 (by rfl) ⟨1233926, by rfl⟩ : syracuseStep 1645235 = 2467853) B2467853
theorem B1645271 : Blo 730325 1645271 := bstep (se 1 (by rfl) ⟨1233953, by rfl⟩ : syracuseStep 1645271 = 2467907) B2467907
theorem B989977 : Blo 730325 989977 := bstep (se 2 (by rfl) ⟨371241, by rfl⟩ : syracuseStep 989977 = 742483) B742483
theorem B1317719 : Blo 730325 1317719 := bstep (se 1 (by rfl) ⟨988289, by rfl⟩ : syracuseStep 1317719 = 1976579) B1976579
theorem B1645451 : Blo 730325 1645451 := bstep (se 1 (by rfl) ⟨1234088, by rfl⟩ : syracuseStep 1645451 = 2468177) B2468177
theorem B3120065 : Blo 730325 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B1645505 : Blo 730325 1645505 := bstep (se 2 (by rfl) ⟨617064, by rfl⟩ : syracuseStep 1645505 = 1234129) B1234129
theorem B10001501 : Blo 730325 10001501 := bstep (se 3 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 10001501 = 3750563) B3750563
theorem B1645721 : Blo 730325 1645721 := bstep (se 2 (by rfl) ⟨617145, by rfl⟩ : syracuseStep 1645721 = 1234291) B1234291
theorem B1645811 : Blo 730325 1645811 := bstep (se 1 (by rfl) ⟨1234358, by rfl⟩ : syracuseStep 1645811 = 2468717) B2468717
theorem B1645847 : Blo 730325 1645847 := bstep (se 1 (by rfl) ⟨1234385, by rfl⟩ : syracuseStep 1645847 = 2468771) B2468771
theorem B2465099 : Blo 730325 2465099 := bstep (se 1 (by rfl) ⟨1848824, by rfl⟩ : syracuseStep 2465099 = 3697649) B3697649
theorem B925015 : Blo 730325 925015 := bstep (se 1 (by rfl) ⟨693761, by rfl⟩ : syracuseStep 925015 = 1387523) B1387523
theorem B1646027 : Blo 730325 1646027 := bstep (se 1 (by rfl) ⟨1234520, by rfl⟩ : syracuseStep 1646027 = 2469041) B2469041
theorem B1646081 : Blo 730325 1646081 := bstep (se 2 (by rfl) ⟨617280, by rfl⟩ : syracuseStep 1646081 = 1234561) B1234561
theorem B2465369 : Blo 730325 2465369 := bstep (se 2 (by rfl) ⟨924513, by rfl⟩ : syracuseStep 2465369 = 1849027) B1849027
theorem B6692483 : Blo 730325 6692483 := bstep (se 1 (by rfl) ⟨5019362, by rfl⟩ : syracuseStep 6692483 = 10038725) B10038725
theorem B1646297 : Blo 730325 1646297 := bstep (se 2 (by rfl) ⟨617361, by rfl⟩ : syracuseStep 1646297 = 1234723) B1234723
theorem B1482547 : Blo 730325 1482547 := bstep (se 1 (by rfl) ⟨1111910, by rfl⟩ : syracuseStep 1482547 = 2223821) B2223821
theorem B1646387 : Blo 730325 1646387 := bstep (se 1 (by rfl) ⟨1234790, by rfl⟩ : syracuseStep 1646387 = 2469581) B2469581
theorem B794443 : Blo 730325 794443 := bstep (se 1 (by rfl) ⟨595832, by rfl⟩ : syracuseStep 794443 = 1191665) B1191665
theorem B1646423 : Blo 730325 1646423 := bstep (se 1 (by rfl) ⟨1234817, by rfl⟩ : syracuseStep 1646423 = 2469635) B2469635
theorem B794539 : Blo 730325 794539 := bstep (se 1 (by rfl) ⟨595904, by rfl⟩ : syracuseStep 794539 = 1191809) B1191809
theorem B18816947 : Blo 730325 18816947 := bstep (se 1 (by rfl) ⟨14112710, by rfl⟩ : syracuseStep 18816947 = 28225421) B28225421
theorem B1646603 : Blo 730325 1646603 := bstep (se 1 (by rfl) ⟨1234952, by rfl⟩ : syracuseStep 1646603 = 2469905) B2469905
theorem B1646657 : Blo 730325 1646657 := bstep (se 2 (by rfl) ⟨617496, by rfl⟩ : syracuseStep 1646657 = 1234993) B1234993
theorem B8462411 : Blo 730325 8462411 := bstep (se 1 (by rfl) ⟨6346808, by rfl⟩ : syracuseStep 8462411 = 12693617) B12693617
theorem B2859229 : Blo 730325 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B2466071 : Blo 730325 2466071 := bstep (se 1 (by rfl) ⟨1849553, by rfl⟩ : syracuseStep 2466071 = 3699107) B3699107
theorem B1646873 : Blo 730325 1646873 := bstep (se 2 (by rfl) ⟨617577, by rfl⟩ : syracuseStep 1646873 = 1235155) B1235155
theorem B1646963 : Blo 730325 1646963 := bstep (se 1 (by rfl) ⟨1235222, by rfl⟩ : syracuseStep 1646963 = 2470445) B2470445
theorem B1646999 : Blo 730325 1646999 := bstep (se 1 (by rfl) ⟨1235249, by rfl⟩ : syracuseStep 1646999 = 2470499) B2470499
theorem B11903449 : Blo 730325 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B3121739 : Blo 730325 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B1647179 : Blo 730325 1647179 := bstep (se 1 (by rfl) ⟨1235384, by rfl⟩ : syracuseStep 1647179 = 2470769) B2470769
theorem B3711581 : Blo 730325 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B1647233 : Blo 730325 1647233 := bstep (se 2 (by rfl) ⟨617712, by rfl⟩ : syracuseStep 1647233 = 1235425) B1235425
theorem B2466611 : Blo 730325 2466611 := bstep (se 1 (by rfl) ⟨1849958, by rfl⟩ : syracuseStep 2466611 = 3699917) B3699917
theorem B1647449 : Blo 730325 1647449 := bstep (se 2 (by rfl) ⟨617793, by rfl⟩ : syracuseStep 1647449 = 1235587) B1235587
theorem B1647539 : Blo 730325 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B1647575 : Blo 730325 1647575 := bstep (se 1 (by rfl) ⟨1235681, by rfl⟩ : syracuseStep 1647575 = 2471363) B2471363
theorem B926731 : Blo 730325 926731 := bstep (se 1 (by rfl) ⟨695048, by rfl⟩ : syracuseStep 926731 = 1390097) B1390097
theorem B5350445 : Blo 730325 5350445 := bstep (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) B2006417
theorem B1778753 : Blo 730325 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B2466881 : Blo 730325 2466881 := bstep (se 2 (by rfl) ⟨925080, by rfl⟩ : syracuseStep 2466881 = 1850161) B1850161
theorem B1647755 : Blo 730325 1647755 := bstep (se 1 (by rfl) ⟨1235816, by rfl⟩ : syracuseStep 1647755 = 2471633) B2471633
theorem B1647809 : Blo 730325 1647809 := bstep (se 2 (by rfl) ⟨617928, by rfl⟩ : syracuseStep 1647809 = 1235857) B1235857
theorem B730327 : Blo 730325 730327 := bstep (se 1 (by rfl) ⟨547745, by rfl⟩ : syracuseStep 730327 = 1095491) B1095491
theorem B730347 : Blo 730325 730347 := bstep (se 1 (by rfl) ⟨547760, by rfl⟩ : syracuseStep 730347 = 1095521) B1095521
theorem B730359 : Blo 730325 730359 := bstep (se 1 (by rfl) ⟨547769, by rfl⟩ : syracuseStep 730359 = 1095539) B1095539
theorem B730379 : Blo 730325 730379 := bstep (se 1 (by rfl) ⟨547784, by rfl⟩ : syracuseStep 730379 = 1095569) B1095569
theorem B730391 : Blo 730325 730391 := bstep (se 1 (by rfl) ⟨547793, by rfl⟩ : syracuseStep 730391 = 1095587) B1095587
theorem B730411 : Blo 730325 730411 := bstep (se 1 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 730411 = 1095617) B1095617
theorem B730423 : Blo 730325 730423 := bstep (se 1 (by rfl) ⟨547817, by rfl⟩ : syracuseStep 730423 = 1095635) B1095635
theorem B730443 : Blo 730325 730443 := bstep (se 1 (by rfl) ⟨547832, by rfl⟩ : syracuseStep 730443 = 1095665) B1095665
theorem B730455 : Blo 730325 730455 := bstep (se 1 (by rfl) ⟨547841, by rfl⟩ : syracuseStep 730455 = 1095683) B1095683
theorem B730475 : Blo 730325 730475 := bstep (se 1 (by rfl) ⟨547856, by rfl⟩ : syracuseStep 730475 = 1095713) B1095713
theorem B730487 : Blo 730325 730487 := bstep (se 1 (by rfl) ⟨547865, by rfl⟩ : syracuseStep 730487 = 1095731) B1095731
theorem B730507 : Blo 730325 730507 := bstep (se 1 (by rfl) ⟨547880, by rfl⟩ : syracuseStep 730507 = 1095761) B1095761
theorem B730519 : Blo 730325 730519 := bstep (se 1 (by rfl) ⟨547889, by rfl⟩ : syracuseStep 730519 = 1095779) B1095779
theorem B1648025 : Blo 730325 1648025 := bstep (se 2 (by rfl) ⟨618009, by rfl⟩ : syracuseStep 1648025 = 1236019) B1236019
theorem B730539 : Blo 730325 730539 := bstep (se 1 (by rfl) ⟨547904, by rfl⟩ : syracuseStep 730539 = 1095809) B1095809
theorem B730551 : Blo 730325 730551 := bstep (se 1 (by rfl) ⟨547913, by rfl⟩ : syracuseStep 730551 = 1095827) B1095827
theorem B730571 : Blo 730325 730571 := bstep (se 1 (by rfl) ⟨547928, by rfl⟩ : syracuseStep 730571 = 1095857) B1095857
theorem B730583 : Blo 730325 730583 := bstep (se 1 (by rfl) ⟨547937, by rfl⟩ : syracuseStep 730583 = 1095875) B1095875
theorem B730603 : Blo 730325 730603 := bstep (se 1 (by rfl) ⟨547952, by rfl⟩ : syracuseStep 730603 = 1095905) B1095905
theorem B1648115 : Blo 730325 1648115 := bstep (se 1 (by rfl) ⟨1236086, by rfl⟩ : syracuseStep 1648115 = 2472173) B2472173
theorem B730615 : Blo 730325 730615 := bstep (se 1 (by rfl) ⟨547961, by rfl⟩ : syracuseStep 730615 = 1095923) B1095923
theorem B730635 : Blo 730325 730635 := bstep (se 1 (by rfl) ⟨547976, by rfl⟩ : syracuseStep 730635 = 1095953) B1095953
theorem B730647 : Blo 730325 730647 := bstep (se 1 (by rfl) ⟨547985, by rfl⟩ : syracuseStep 730647 = 1095971) B1095971
theorem B1648151 : Blo 730325 1648151 := bstep (se 1 (by rfl) ⟨1236113, by rfl⟩ : syracuseStep 1648151 = 2472227) B2472227
theorem B5285411 : Blo 730325 5285411 := bstep (se 1 (by rfl) ⟨3964058, by rfl⟩ : syracuseStep 5285411 = 7928117) B7928117
theorem B730667 : Blo 730325 730667 := bstep (se 1 (by rfl) ⟨548000, by rfl⟩ : syracuseStep 730667 = 1096001) B1096001
theorem B730679 : Blo 730325 730679 := bstep (se 1 (by rfl) ⟨548009, by rfl⟩ : syracuseStep 730679 = 1096019) B1096019
theorem B730699 : Blo 730325 730699 := bstep (se 1 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 730699 = 1096049) B1096049
theorem B730711 : Blo 730325 730711 := bstep (se 1 (by rfl) ⟨548033, by rfl⟩ : syracuseStep 730711 = 1096067) B1096067
theorem B2467421 : Blo 730325 2467421 := bstep (se 3 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 2467421 = 925283) B925283
theorem B730731 : Blo 730325 730731 := bstep (se 1 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 730731 = 1096097) B1096097
theorem B730743 : Blo 730325 730743 := bstep (se 1 (by rfl) ⟨548057, by rfl⟩ : syracuseStep 730743 = 1096115) B1096115
theorem B730763 : Blo 730325 730763 := bstep (se 1 (by rfl) ⟨548072, by rfl⟩ : syracuseStep 730763 = 1096145) B1096145
theorem B730775 : Blo 730325 730775 := bstep (se 1 (by rfl) ⟨548081, by rfl⟩ : syracuseStep 730775 = 1096163) B1096163
theorem B730795 : Blo 730325 730795 := bstep (se 1 (by rfl) ⟨548096, by rfl⟩ : syracuseStep 730795 = 1096193) B1096193
theorem B4695731 : Blo 730325 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B730807 : Blo 730325 730807 := bstep (se 1 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 730807 = 1096211) B1096211
theorem B730827 : Blo 730325 730827 := bstep (se 1 (by rfl) ⟨548120, by rfl⟩ : syracuseStep 730827 = 1096241) B1096241
theorem B1648331 : Blo 730325 1648331 := bstep (se 1 (by rfl) ⟨1236248, by rfl⟩ : syracuseStep 1648331 = 2472497) B2472497
theorem B730839 : Blo 730325 730839 := bstep (se 1 (by rfl) ⟨548129, by rfl⟩ : syracuseStep 730839 = 1096259) B1096259
theorem B730859 : Blo 730325 730859 := bstep (se 1 (by rfl) ⟨548144, by rfl⟩ : syracuseStep 730859 = 1096289) B1096289
theorem B730871 : Blo 730325 730871 := bstep (se 1 (by rfl) ⟨548153, by rfl⟩ : syracuseStep 730871 = 1096307) B1096307
theorem B1648385 : Blo 730325 1648385 := bstep (se 2 (by rfl) ⟨618144, by rfl⟩ : syracuseStep 1648385 = 1236289) B1236289
theorem B730891 : Blo 730325 730891 := bstep (se 1 (by rfl) ⟨548168, by rfl⟩ : syracuseStep 730891 = 1096337) B1096337
theorem B730903 : Blo 730325 730903 := bstep (se 1 (by rfl) ⟨548177, by rfl⟩ : syracuseStep 730903 = 1096355) B1096355
theorem B730923 : Blo 730325 730923 := bstep (se 1 (by rfl) ⟨548192, by rfl⟩ : syracuseStep 730923 = 1096385) B1096385
theorem B730935 : Blo 730325 730935 := bstep (se 1 (by rfl) ⟨548201, by rfl⟩ : syracuseStep 730935 = 1096403) B1096403
theorem B730955 : Blo 730325 730955 := bstep (se 1 (by rfl) ⟨548216, by rfl⟩ : syracuseStep 730955 = 1096433) B1096433
theorem B730967 : Blo 730325 730967 := bstep (se 1 (by rfl) ⟨548225, by rfl⟩ : syracuseStep 730967 = 1096451) B1096451
theorem B730987 : Blo 730325 730987 := bstep (se 1 (by rfl) ⟨548240, by rfl⟩ : syracuseStep 730987 = 1096481) B1096481
theorem B730999 : Blo 730325 730999 := bstep (se 1 (by rfl) ⟨548249, by rfl⟩ : syracuseStep 730999 = 1096499) B1096499
theorem B731019 : Blo 730325 731019 := bstep (se 1 (by rfl) ⟨548264, by rfl⟩ : syracuseStep 731019 = 1096529) B1096529
theorem B731031 : Blo 730325 731031 := bstep (se 1 (by rfl) ⟨548273, by rfl⟩ : syracuseStep 731031 = 1096547) B1096547
theorem B731051 : Blo 730325 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B1484723 : Blo 730325 1484723 := bstep (se 1 (by rfl) ⟨1113542, by rfl⟩ : syracuseStep 1484723 = 2227085) B2227085
theorem B731063 : Blo 730325 731063 := bstep (se 1 (by rfl) ⟨548297, by rfl⟩ : syracuseStep 731063 = 1096595) B1096595
theorem B731083 : Blo 730325 731083 := bstep (se 1 (by rfl) ⟨548312, by rfl⟩ : syracuseStep 731083 = 1096625) B1096625
theorem B731095 : Blo 730325 731095 := bstep (se 1 (by rfl) ⟨548321, by rfl⟩ : syracuseStep 731095 = 1096643) B1096643
theorem B1648601 : Blo 730325 1648601 := bstep (se 2 (by rfl) ⟨618225, by rfl⟩ : syracuseStep 1648601 = 1236451) B1236451
theorem B927703 : Blo 730325 927703 := bstep (se 1 (by rfl) ⟨695777, by rfl⟩ : syracuseStep 927703 = 1391555) B1391555
theorem B731115 : Blo 730325 731115 := bstep (se 1 (by rfl) ⟨548336, by rfl⟩ : syracuseStep 731115 = 1096673) B1096673
theorem B731127 : Blo 730325 731127 := bstep (se 1 (by rfl) ⟨548345, by rfl⟩ : syracuseStep 731127 = 1096691) B1096691
theorem B1386497 : Blo 730325 1386497 := bstep (se 2 (by rfl) ⟨519936, by rfl⟩ : syracuseStep 1386497 = 1039873) B1039873
theorem B731147 : Blo 730325 731147 := bstep (se 1 (by rfl) ⟨548360, by rfl⟩ : syracuseStep 731147 = 1096721) B1096721
theorem B731159 : Blo 730325 731159 := bstep (se 1 (by rfl) ⟨548369, by rfl⟩ : syracuseStep 731159 = 1096739) B1096739
theorem B731179 : Blo 730325 731179 := bstep (se 1 (by rfl) ⟨548384, by rfl⟩ : syracuseStep 731179 = 1096769) B1096769
theorem B1648691 : Blo 730325 1648691 := bstep (se 1 (by rfl) ⟨1236518, by rfl⟩ : syracuseStep 1648691 = 2473037) B2473037
theorem B731191 : Blo 730325 731191 := bstep (se 1 (by rfl) ⟨548393, by rfl⟩ : syracuseStep 731191 = 1096787) B1096787
theorem B731211 : Blo 730325 731211 := bstep (se 1 (by rfl) ⟨548408, by rfl⟩ : syracuseStep 731211 = 1096817) B1096817
theorem B3516491 : Blo 730325 3516491 := bstep (se 1 (by rfl) ⟨2637368, by rfl⟩ : syracuseStep 3516491 = 5274737) B5274737
theorem B1484875 : Blo 730325 1484875 := bstep (se 1 (by rfl) ⟨1113656, by rfl⟩ : syracuseStep 1484875 = 2227313) B2227313
theorem B731223 : Blo 730325 731223 := bstep (se 1 (by rfl) ⟨548417, by rfl⟩ : syracuseStep 731223 = 1096835) B1096835
theorem B1648727 : Blo 730325 1648727 := bstep (se 1 (by rfl) ⟨1236545, by rfl⟩ : syracuseStep 1648727 = 2473091) B2473091
theorem B1321049 : Blo 730325 1321049 := bstep (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) B990787
theorem B731243 : Blo 730325 731243 := bstep (se 1 (by rfl) ⟨548432, by rfl⟩ : syracuseStep 731243 = 1096865) B1096865
theorem B731255 : Blo 730325 731255 := bstep (se 1 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 731255 = 1096883) B1096883
theorem B731275 : Blo 730325 731275 := bstep (se 1 (by rfl) ⟨548456, by rfl⟩ : syracuseStep 731275 = 1096913) B1096913
theorem B1976471 : Blo 730325 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B731287 : Blo 730325 731287 := bstep (se 1 (by rfl) ⟨548465, by rfl⟩ : syracuseStep 731287 = 1096931) B1096931
theorem B1386649 : Blo 730325 1386649 := bstep (se 2 (by rfl) ⟨519993, by rfl⟩ : syracuseStep 1386649 = 1039987) B1039987
theorem B731307 : Blo 730325 731307 := bstep (se 1 (by rfl) ⟨548480, by rfl⟩ : syracuseStep 731307 = 1096961) B1096961
theorem B731319 : Blo 730325 731319 := bstep (se 1 (by rfl) ⟨548489, by rfl⟩ : syracuseStep 731319 = 1096979) B1096979
theorem B731339 : Blo 730325 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B731351 : Blo 730325 731351 := bstep (se 1 (by rfl) ⟨548513, by rfl⟩ : syracuseStep 731351 = 1097027) B1097027
theorem B731371 : Blo 730325 731371 := bstep (se 1 (by rfl) ⟨548528, by rfl⟩ : syracuseStep 731371 = 1097057) B1097057
theorem B731383 : Blo 730325 731383 := bstep (se 1 (by rfl) ⟨548537, by rfl⟩ : syracuseStep 731383 = 1097075) B1097075
theorem B731403 : Blo 730325 731403 := bstep (se 1 (by rfl) ⟨548552, by rfl⟩ : syracuseStep 731403 = 1097105) B1097105
theorem B1648907 : Blo 730325 1648907 := bstep (se 1 (by rfl) ⟨1236680, by rfl⟩ : syracuseStep 1648907 = 2473361) B2473361
theorem B731415 : Blo 730325 731415 := bstep (se 1 (by rfl) ⟨548561, by rfl⟩ : syracuseStep 731415 = 1097123) B1097123
theorem B731435 : Blo 730325 731435 := bstep (se 1 (by rfl) ⟨548576, by rfl⟩ : syracuseStep 731435 = 1097153) B1097153
theorem B731447 : Blo 730325 731447 := bstep (se 1 (by rfl) ⟨548585, by rfl⟩ : syracuseStep 731447 = 1097171) B1097171
theorem B1648961 : Blo 730325 1648961 := bstep (se 2 (by rfl) ⟨618360, by rfl⟩ : syracuseStep 1648961 = 1236721) B1236721
theorem B731467 : Blo 730325 731467 := bstep (se 1 (by rfl) ⟨548600, by rfl⟩ : syracuseStep 731467 = 1097201) B1097201
theorem B731479 : Blo 730325 731479 := bstep (se 1 (by rfl) ⟨548609, by rfl⟩ : syracuseStep 731479 = 1097219) B1097219
theorem B731499 : Blo 730325 731499 := bstep (se 1 (by rfl) ⟨548624, by rfl⟩ : syracuseStep 731499 = 1097249) B1097249
theorem B731511 : Blo 730325 731511 := bstep (se 1 (by rfl) ⟨548633, by rfl⟩ : syracuseStep 731511 = 1097267) B1097267
theorem B731531 : Blo 730325 731531 := bstep (se 1 (by rfl) ⟨548648, by rfl⟩ : syracuseStep 731531 = 1097297) B1097297
theorem B731543 : Blo 730325 731543 := bstep (se 1 (by rfl) ⟨548657, by rfl⟩ : syracuseStep 731543 = 1097315) B1097315
theorem B731563 : Blo 730325 731563 := bstep (se 1 (by rfl) ⟨548672, by rfl⟩ : syracuseStep 731563 = 1097345) B1097345
theorem B731575 : Blo 730325 731575 := bstep (se 1 (by rfl) ⟨548681, by rfl⟩ : syracuseStep 731575 = 1097363) B1097363
theorem B731595 : Blo 730325 731595 := bstep (se 1 (by rfl) ⟨548696, by rfl⟩ : syracuseStep 731595 = 1097393) B1097393
theorem B731607 : Blo 730325 731607 := bstep (se 1 (by rfl) ⟨548705, by rfl⟩ : syracuseStep 731607 = 1097411) B1097411
theorem B4172249 : Blo 730325 4172249 := bstep (se 2 (by rfl) ⟨1564593, by rfl⟩ : syracuseStep 4172249 = 3129187) B3129187
theorem B731627 : Blo 730325 731627 := bstep (se 1 (by rfl) ⟨548720, by rfl⟩ : syracuseStep 731627 = 1097441) B1097441
theorem B731639 : Blo 730325 731639 := bstep (se 1 (by rfl) ⟨548729, by rfl⟩ : syracuseStep 731639 = 1097459) B1097459
theorem B731659 : Blo 730325 731659 := bstep (se 1 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 731659 = 1097489) B1097489
theorem B731671 : Blo 730325 731671 := bstep (se 1 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 731671 = 1097507) B1097507
theorem B1649177 : Blo 730325 1649177 := bstep (se 2 (by rfl) ⟨618441, by rfl⟩ : syracuseStep 1649177 = 1236883) B1236883
theorem B731691 : Blo 730325 731691 := bstep (se 1 (by rfl) ⟨548768, by rfl⟩ : syracuseStep 731691 = 1097537) B1097537
theorem B731703 : Blo 730325 731703 := bstep (se 1 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 731703 = 1097555) B1097555
theorem B731723 : Blo 730325 731723 := bstep (se 1 (by rfl) ⟨548792, by rfl⟩ : syracuseStep 731723 = 1097585) B1097585
theorem B731735 : Blo 730325 731735 := bstep (se 1 (by rfl) ⟨548801, by rfl⟩ : syracuseStep 731735 = 1097603) B1097603
theorem B731755 : Blo 730325 731755 := bstep (se 1 (by rfl) ⟨548816, by rfl⟩ : syracuseStep 731755 = 1097633) B1097633
theorem B1649267 : Blo 730325 1649267 := bstep (se 1 (by rfl) ⟨1236950, by rfl⟩ : syracuseStep 1649267 = 2473901) B2473901
theorem B731767 : Blo 730325 731767 := bstep (se 1 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 731767 = 1097651) B1097651
theorem B731787 : Blo 730325 731787 := bstep (se 1 (by rfl) ⟨548840, by rfl⟩ : syracuseStep 731787 = 1097681) B1097681
theorem B731799 : Blo 730325 731799 := bstep (se 1 (by rfl) ⟨548849, by rfl⟩ : syracuseStep 731799 = 1097699) B1097699
theorem B1649303 : Blo 730325 1649303 := bstep (se 1 (by rfl) ⟨1236977, by rfl⟩ : syracuseStep 1649303 = 2473955) B2473955
theorem B3713687 : Blo 730325 3713687 := bstep (se 1 (by rfl) ⟨2785265, by rfl⟩ : syracuseStep 3713687 = 5570531) B5570531
theorem B731819 : Blo 730325 731819 := bstep (se 1 (by rfl) ⟨548864, by rfl⟩ : syracuseStep 731819 = 1097729) B1097729
theorem B731831 : Blo 730325 731831 := bstep (se 1 (by rfl) ⟨548873, by rfl⟩ : syracuseStep 731831 = 1097747) B1097747
theorem B2468555 : Blo 730325 2468555 := bstep (se 1 (by rfl) ⟨1851416, by rfl⟩ : syracuseStep 2468555 = 3702833) B3702833
theorem B731851 : Blo 730325 731851 := bstep (se 1 (by rfl) ⟨548888, by rfl⟩ : syracuseStep 731851 = 1097777) B1097777
theorem B731863 : Blo 730325 731863 := bstep (se 1 (by rfl) ⟨548897, by rfl⟩ : syracuseStep 731863 = 1097795) B1097795
theorem B1583833 : Blo 730325 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B5286617 : Blo 730325 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B731883 : Blo 730325 731883 := bstep (se 1 (by rfl) ⟨548912, by rfl⟩ : syracuseStep 731883 = 1097825) B1097825
theorem B731895 : Blo 730325 731895 := bstep (se 1 (by rfl) ⟨548921, by rfl⟩ : syracuseStep 731895 = 1097843) B1097843
theorem B731915 : Blo 730325 731915 := bstep (se 1 (by rfl) ⟨548936, by rfl⟩ : syracuseStep 731915 = 1097873) B1097873
theorem B928523 : Blo 730325 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B731927 : Blo 730325 731927 := bstep (se 1 (by rfl) ⟨548945, by rfl⟩ : syracuseStep 731927 = 1097891) B1097891
theorem B731947 : Blo 730325 731947 := bstep (se 1 (by rfl) ⟨548960, by rfl⟩ : syracuseStep 731947 = 1097921) B1097921
theorem B731959 : Blo 730325 731959 := bstep (se 1 (by rfl) ⟨548969, by rfl⟩ : syracuseStep 731959 = 1097939) B1097939
theorem B731979 : Blo 730325 731979 := bstep (se 1 (by rfl) ⟨548984, by rfl⟩ : syracuseStep 731979 = 1097969) B1097969
theorem B1649483 : Blo 730325 1649483 := bstep (se 1 (by rfl) ⟨1237112, by rfl⟩ : syracuseStep 1649483 = 2474225) B2474225
theorem B731991 : Blo 730325 731991 := bstep (se 1 (by rfl) ⟨548993, by rfl⟩ : syracuseStep 731991 = 1097987) B1097987
theorem B732011 : Blo 730325 732011 := bstep (se 1 (by rfl) ⟨549008, by rfl⟩ : syracuseStep 732011 = 1098017) B1098017
theorem B732023 : Blo 730325 732023 := bstep (se 1 (by rfl) ⟨549017, by rfl⟩ : syracuseStep 732023 = 1098035) B1098035
theorem B1649537 : Blo 730325 1649537 := bstep (se 2 (by rfl) ⟨618576, by rfl⟩ : syracuseStep 1649537 = 1237153) B1237153
theorem B732043 : Blo 730325 732043 := bstep (se 1 (by rfl) ⟨549032, by rfl⟩ : syracuseStep 732043 = 1098065) B1098065
theorem B732055 : Blo 730325 732055 := bstep (se 1 (by rfl) ⟨549041, by rfl⟩ : syracuseStep 732055 = 1098083) B1098083
theorem B732075 : Blo 730325 732075 := bstep (se 1 (by rfl) ⟨549056, by rfl⟩ : syracuseStep 732075 = 1098113) B1098113
theorem B732087 : Blo 730325 732087 := bstep (se 1 (by rfl) ⟨549065, by rfl⟩ : syracuseStep 732087 = 1098131) B1098131
theorem B1878977 : Blo 730325 1878977 := bstep (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) B1409233
theorem B732107 : Blo 730325 732107 := bstep (se 1 (by rfl) ⟨549080, by rfl⟩ : syracuseStep 732107 = 1098161) B1098161
theorem B732119 : Blo 730325 732119 := bstep (se 1 (by rfl) ⟨549089, by rfl⟩ : syracuseStep 732119 = 1098179) B1098179
theorem B2468825 : Blo 730325 2468825 := bstep (se 2 (by rfl) ⟨925809, by rfl⟩ : syracuseStep 2468825 = 1851619) B1851619
theorem B732139 : Blo 730325 732139 := bstep (se 1 (by rfl) ⟨549104, by rfl⟩ : syracuseStep 732139 = 1098209) B1098209
theorem B732151 : Blo 730325 732151 := bstep (se 1 (by rfl) ⟨549113, by rfl⟩ : syracuseStep 732151 = 1098227) B1098227
theorem B732171 : Blo 730325 732171 := bstep (se 1 (by rfl) ⟨549128, by rfl⟩ : syracuseStep 732171 = 1098257) B1098257
theorem B732183 : Blo 730325 732183 := bstep (se 1 (by rfl) ⟨549137, by rfl⟩ : syracuseStep 732183 = 1098275) B1098275
theorem B732203 : Blo 730325 732203 := bstep (se 1 (by rfl) ⟨549152, by rfl⟩ : syracuseStep 732203 = 1098305) B1098305
theorem B732215 : Blo 730325 732215 := bstep (se 1 (by rfl) ⟨549161, by rfl⟩ : syracuseStep 732215 = 1098323) B1098323
theorem B15051845 : Blo 730325 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B732235 : Blo 730325 732235 := bstep (se 1 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 732235 = 1098353) B1098353
theorem B732247 : Blo 730325 732247 := bstep (se 1 (by rfl) ⟨549185, by rfl⟩ : syracuseStep 732247 = 1098371) B1098371
theorem B1485913 : Blo 730325 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B1649753 : Blo 730325 1649753 := bstep (se 2 (by rfl) ⟨618657, by rfl⟩ : syracuseStep 1649753 = 1237315) B1237315
theorem B732267 : Blo 730325 732267 := bstep (se 1 (by rfl) ⟨549200, by rfl⟩ : syracuseStep 732267 = 1098401) B1098401
theorem B732279 : Blo 730325 732279 := bstep (se 1 (by rfl) ⟨549209, by rfl⟩ : syracuseStep 732279 = 1098419) B1098419
theorem B732299 : Blo 730325 732299 := bstep (se 1 (by rfl) ⟨549224, by rfl⟩ : syracuseStep 732299 = 1098449) B1098449
theorem B732311 : Blo 730325 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B732331 : Blo 730325 732331 := bstep (se 1 (by rfl) ⟨549248, by rfl⟩ : syracuseStep 732331 = 1098497) B1098497
theorem B3124403 : Blo 730325 3124403 := bstep (se 1 (by rfl) ⟨2343302, by rfl⟩ : syracuseStep 3124403 = 4686605) B4686605
theorem B1649843 : Blo 730325 1649843 := bstep (se 1 (by rfl) ⟨1237382, by rfl⟩ : syracuseStep 1649843 = 2474765) B2474765
theorem B732343 : Blo 730325 732343 := bstep (se 1 (by rfl) ⟨549257, by rfl⟩ : syracuseStep 732343 = 1098515) B1098515
theorem B732363 : Blo 730325 732363 := bstep (se 1 (by rfl) ⟨549272, by rfl⟩ : syracuseStep 732363 = 1098545) B1098545
theorem B732375 : Blo 730325 732375 := bstep (se 1 (by rfl) ⟨549281, by rfl⟩ : syracuseStep 732375 = 1098563) B1098563
theorem B1649879 : Blo 730325 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B732395 : Blo 730325 732395 := bstep (se 1 (by rfl) ⟨549296, by rfl⟩ : syracuseStep 732395 = 1098593) B1098593
theorem B732407 : Blo 730325 732407 := bstep (se 1 (by rfl) ⟨549305, by rfl⟩ : syracuseStep 732407 = 1098611) B1098611
theorem B732427 : Blo 730325 732427 := bstep (se 1 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 732427 = 1098641) B1098641
theorem B732439 : Blo 730325 732439 := bstep (se 1 (by rfl) ⟨549329, by rfl⟩ : syracuseStep 732439 = 1098659) B1098659
theorem B732459 : Blo 730325 732459 := bstep (se 1 (by rfl) ⟨549344, by rfl⟩ : syracuseStep 732459 = 1098689) B1098689
theorem B732471 : Blo 730325 732471 := bstep (se 1 (by rfl) ⟨549353, by rfl⟩ : syracuseStep 732471 = 1098707) B1098707
theorem B732491 : Blo 730325 732491 := bstep (se 1 (by rfl) ⟨549368, by rfl⟩ : syracuseStep 732491 = 1098737) B1098737
theorem B732503 : Blo 730325 732503 := bstep (se 1 (by rfl) ⟨549377, by rfl⟩ : syracuseStep 732503 = 1098755) B1098755
theorem B732523 : Blo 730325 732523 := bstep (se 1 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 732523 = 1098785) B1098785
theorem B732535 : Blo 730325 732535 := bstep (se 1 (by rfl) ⟨549401, by rfl⟩ : syracuseStep 732535 = 1098803) B1098803
theorem B732555 : Blo 730325 732555 := bstep (se 1 (by rfl) ⟨549416, by rfl⟩ : syracuseStep 732555 = 1098833) B1098833
theorem B1650059 : Blo 730325 1650059 := bstep (se 1 (by rfl) ⟨1237544, by rfl⟩ : syracuseStep 1650059 = 2475089) B2475089
theorem B732567 : Blo 730325 732567 := bstep (se 1 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 732567 = 1098851) B1098851
theorem B732587 : Blo 730325 732587 := bstep (se 1 (by rfl) ⟨549440, by rfl⟩ : syracuseStep 732587 = 1098881) B1098881
theorem B1387955 : Blo 730325 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B732599 : Blo 730325 732599 := bstep (se 1 (by rfl) ⟨549449, by rfl⟩ : syracuseStep 732599 = 1098899) B1098899
theorem B1650113 : Blo 730325 1650113 := bstep (se 2 (by rfl) ⟨618792, by rfl⟩ : syracuseStep 1650113 = 1237585) B1237585
theorem B732619 : Blo 730325 732619 := bstep (se 1 (by rfl) ⟨549464, by rfl⟩ : syracuseStep 732619 = 1098929) B1098929
theorem B929227 : Blo 730325 929227 := bstep (se 1 (by rfl) ⟨696920, by rfl⟩ : syracuseStep 929227 = 1393841) B1393841
theorem B732631 : Blo 730325 732631 := bstep (se 1 (by rfl) ⟨549473, by rfl⟩ : syracuseStep 732631 = 1098947) B1098947
theorem B732651 : Blo 730325 732651 := bstep (se 1 (by rfl) ⟨549488, by rfl⟩ : syracuseStep 732651 = 1098977) B1098977
theorem B732663 : Blo 730325 732663 := bstep (se 1 (by rfl) ⟨549497, by rfl⟩ : syracuseStep 732663 = 1098995) B1098995
theorem B732683 : Blo 730325 732683 := bstep (se 1 (by rfl) ⟨549512, by rfl⟩ : syracuseStep 732683 = 1099025) B1099025
theorem B732695 : Blo 730325 732695 := bstep (se 1 (by rfl) ⟨549521, by rfl⟩ : syracuseStep 732695 = 1099043) B1099043
theorem B732715 : Blo 730325 732715 := bstep (se 1 (by rfl) ⟨549536, by rfl⟩ : syracuseStep 732715 = 1099073) B1099073
theorem B732727 : Blo 730325 732727 := bstep (se 1 (by rfl) ⟨549545, by rfl⟩ : syracuseStep 732727 = 1099091) B1099091
theorem B5549633 : Blo 730325 5549633 := bstep (se 2 (by rfl) ⟨2081112, by rfl⟩ : syracuseStep 5549633 = 4162225) B4162225
theorem B1388107 : Blo 730325 1388107 := bstep (se 1 (by rfl) ⟨1041080, by rfl⟩ : syracuseStep 1388107 = 2082161) B2082161
theorem B732747 : Blo 730325 732747 := bstep (se 1 (by rfl) ⟨549560, by rfl⟩ : syracuseStep 732747 = 1099121) B1099121
theorem B732759 : Blo 730325 732759 := bstep (se 1 (by rfl) ⟨549569, by rfl⟩ : syracuseStep 732759 = 1099139) B1099139
theorem B732779 : Blo 730325 732779 := bstep (se 1 (by rfl) ⟨549584, by rfl⟩ : syracuseStep 732779 = 1099169) B1099169
theorem B732791 : Blo 730325 732791 := bstep (se 1 (by rfl) ⟨549593, by rfl⟩ : syracuseStep 732791 = 1099187) B1099187
theorem B732811 : Blo 730325 732811 := bstep (se 1 (by rfl) ⟨549608, by rfl⟩ : syracuseStep 732811 = 1099217) B1099217
theorem B2469527 : Blo 730325 2469527 := bstep (se 1 (by rfl) ⟨1852145, by rfl⟩ : syracuseStep 2469527 = 3704291) B3704291
theorem B732823 : Blo 730325 732823 := bstep (se 1 (by rfl) ⟨549617, by rfl⟩ : syracuseStep 732823 = 1099235) B1099235
theorem B1650329 : Blo 730325 1650329 := bstep (se 2 (by rfl) ⟨618873, by rfl⟩ : syracuseStep 1650329 = 1237747) B1237747
theorem B732843 : Blo 730325 732843 := bstep (se 1 (by rfl) ⟨549632, by rfl⟩ : syracuseStep 732843 = 1099265) B1099265
theorem B732855 : Blo 730325 732855 := bstep (se 1 (by rfl) ⟨549641, by rfl⟩ : syracuseStep 732855 = 1099283) B1099283
theorem B732875 : Blo 730325 732875 := bstep (se 1 (by rfl) ⟨549656, by rfl⟩ : syracuseStep 732875 = 1099313) B1099313
theorem B732887 : Blo 730325 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B732907 : Blo 730325 732907 := bstep (se 1 (by rfl) ⟨549680, by rfl⟩ : syracuseStep 732907 = 1099361) B1099361
theorem B1650419 : Blo 730325 1650419 := bstep (se 1 (by rfl) ⟨1237814, by rfl⟩ : syracuseStep 1650419 = 2475629) B2475629
theorem B732919 : Blo 730325 732919 := bstep (se 1 (by rfl) ⟨549689, by rfl⟩ : syracuseStep 732919 = 1099379) B1099379
theorem B732939 : Blo 730325 732939 := bstep (se 1 (by rfl) ⟨549704, by rfl⟩ : syracuseStep 732939 = 1099409) B1099409
theorem B732951 : Blo 730325 732951 := bstep (se 1 (by rfl) ⟨549713, by rfl⟩ : syracuseStep 732951 = 1099427) B1099427
theorem B1650455 : Blo 730325 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B732971 : Blo 730325 732971 := bstep (se 1 (by rfl) ⟨549728, by rfl⟩ : syracuseStep 732971 = 1099457) B1099457
theorem B732983 : Blo 730325 732983 := bstep (se 1 (by rfl) ⟨549737, by rfl⟩ : syracuseStep 732983 = 1099475) B1099475
theorem B733003 : Blo 730325 733003 := bstep (se 1 (by rfl) ⟨549752, by rfl⟩ : syracuseStep 733003 = 1099505) B1099505
theorem B733015 : Blo 730325 733015 := bstep (se 1 (by rfl) ⟨549761, by rfl⟩ : syracuseStep 733015 = 1099523) B1099523
theorem B733035 : Blo 730325 733035 := bstep (se 1 (by rfl) ⟨549776, by rfl⟩ : syracuseStep 733035 = 1099553) B1099553
theorem B733047 : Blo 730325 733047 := bstep (se 1 (by rfl) ⟨549785, by rfl⟩ : syracuseStep 733047 = 1099571) B1099571
theorem B733067 : Blo 730325 733067 := bstep (se 1 (by rfl) ⟨549800, by rfl⟩ : syracuseStep 733067 = 1099601) B1099601
theorem B733079 : Blo 730325 733079 := bstep (se 1 (by rfl) ⟨549809, by rfl⟩ : syracuseStep 733079 = 1099619) B1099619
theorem B1388441 : Blo 730325 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B733099 : Blo 730325 733099 := bstep (se 1 (by rfl) ⟨549824, by rfl⟩ : syracuseStep 733099 = 1099649) B1099649
theorem B733111 : Blo 730325 733111 := bstep (se 1 (by rfl) ⟨549833, by rfl⟩ : syracuseStep 733111 = 1099667) B1099667
theorem B733131 : Blo 730325 733131 := bstep (se 1 (by rfl) ⟨549848, by rfl⟩ : syracuseStep 733131 = 1099697) B1099697
theorem B1650635 : Blo 730325 1650635 := bstep (se 1 (by rfl) ⟨1237976, by rfl⟩ : syracuseStep 1650635 = 2475953) B2475953
theorem B733143 : Blo 730325 733143 := bstep (se 1 (by rfl) ⟨549857, by rfl⟩ : syracuseStep 733143 = 1099715) B1099715
theorem B733163 : Blo 730325 733163 := bstep (se 1 (by rfl) ⟨549872, by rfl⟩ : syracuseStep 733163 = 1099745) B1099745
theorem B733175 : Blo 730325 733175 := bstep (se 1 (by rfl) ⟨549881, by rfl⟩ : syracuseStep 733175 = 1099763) B1099763
theorem B1650689 : Blo 730325 1650689 := bstep (se 2 (by rfl) ⟨619008, by rfl⟩ : syracuseStep 1650689 = 1238017) B1238017
theorem B733195 : Blo 730325 733195 := bstep (se 1 (by rfl) ⟨549896, by rfl⟩ : syracuseStep 733195 = 1099793) B1099793
theorem B733207 : Blo 730325 733207 := bstep (se 1 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 733207 = 1099811) B1099811
theorem B733227 : Blo 730325 733227 := bstep (se 1 (by rfl) ⟨549920, by rfl⟩ : syracuseStep 733227 = 1099841) B1099841
theorem B733239 : Blo 730325 733239 := bstep (se 1 (by rfl) ⟨549929, by rfl⟩ : syracuseStep 733239 = 1099859) B1099859
theorem B4173889 : Blo 730325 4173889 := bstep (se 2 (by rfl) ⟨1565208, by rfl⟩ : syracuseStep 4173889 = 3130417) B3130417
theorem B733259 : Blo 730325 733259 := bstep (se 1 (by rfl) ⟨549944, by rfl⟩ : syracuseStep 733259 = 1099889) B1099889
theorem B733271 : Blo 730325 733271 := bstep (se 1 (by rfl) ⟨549953, by rfl⟩ : syracuseStep 733271 = 1099907) B1099907
theorem B733291 : Blo 730325 733291 := bstep (se 1 (by rfl) ⟨549968, by rfl⟩ : syracuseStep 733291 = 1099937) B1099937
theorem B733303 : Blo 730325 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B733323 : Blo 730325 733323 := bstep (se 1 (by rfl) ⟨549992, by rfl⟩ : syracuseStep 733323 = 1099985) B1099985
theorem B733335 : Blo 730325 733335 := bstep (se 1 (by rfl) ⟨550001, by rfl⟩ : syracuseStep 733335 = 1100003) B1100003
theorem B733355 : Blo 730325 733355 := bstep (se 1 (by rfl) ⟨550016, by rfl⟩ : syracuseStep 733355 = 1100033) B1100033
theorem B2470067 : Blo 730325 2470067 := bstep (se 1 (by rfl) ⟨1852550, by rfl⟩ : syracuseStep 2470067 = 3705101) B3705101
theorem B733367 : Blo 730325 733367 := bstep (se 1 (by rfl) ⟨550025, by rfl⟩ : syracuseStep 733367 = 1100051) B1100051
theorem B733387 : Blo 730325 733387 := bstep (se 1 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 733387 = 1100081) B1100081
theorem B733399 : Blo 730325 733399 := bstep (se 1 (by rfl) ⟨550049, by rfl⟩ : syracuseStep 733399 = 1100099) B1100099
theorem B1650905 : Blo 730325 1650905 := bstep (se 2 (by rfl) ⟨619089, by rfl⟩ : syracuseStep 1650905 = 1238179) B1238179
theorem B733419 : Blo 730325 733419 := bstep (se 1 (by rfl) ⟨550064, by rfl⟩ : syracuseStep 733419 = 1100129) B1100129
theorem B733431 : Blo 730325 733431 := bstep (se 1 (by rfl) ⟨550073, by rfl⟩ : syracuseStep 733431 = 1100147) B1100147
theorem B733451 : Blo 730325 733451 := bstep (se 1 (by rfl) ⟨550088, by rfl⟩ : syracuseStep 733451 = 1100177) B1100177
theorem B733463 : Blo 730325 733463 := bstep (se 1 (by rfl) ⟨550097, by rfl⟩ : syracuseStep 733463 = 1100195) B1100195
theorem B733483 : Blo 730325 733483 := bstep (se 1 (by rfl) ⟨550112, by rfl⟩ : syracuseStep 733483 = 1100225) B1100225
theorem B1650995 : Blo 730325 1650995 := bstep (se 1 (by rfl) ⟨1238246, by rfl⟩ : syracuseStep 1650995 = 2476493) B2476493
theorem B733495 : Blo 730325 733495 := bstep (se 1 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 733495 = 1100243) B1100243
theorem B733515 : Blo 730325 733515 := bstep (se 1 (by rfl) ⟨550136, by rfl⟩ : syracuseStep 733515 = 1100273) B1100273
theorem B733527 : Blo 730325 733527 := bstep (se 1 (by rfl) ⟨550145, by rfl⟩ : syracuseStep 733527 = 1100291) B1100291
theorem B1651031 : Blo 730325 1651031 := bstep (se 1 (by rfl) ⟨1238273, by rfl⟩ : syracuseStep 1651031 = 2476547) B2476547
theorem B733547 : Blo 730325 733547 := bstep (se 1 (by rfl) ⟨550160, by rfl⟩ : syracuseStep 733547 = 1100321) B1100321
theorem B733559 : Blo 730325 733559 := bstep (se 1 (by rfl) ⟨550169, by rfl⟩ : syracuseStep 733559 = 1100339) B1100339
theorem B733579 : Blo 730325 733579 := bstep (se 1 (by rfl) ⟨550184, by rfl⟩ : syracuseStep 733579 = 1100369) B1100369
theorem B733591 : Blo 730325 733591 := bstep (se 1 (by rfl) ⟨550193, by rfl⟩ : syracuseStep 733591 = 1100387) B1100387
theorem B733611 : Blo 730325 733611 := bstep (se 1 (by rfl) ⟨550208, by rfl⟩ : syracuseStep 733611 = 1100417) B1100417
theorem B733623 : Blo 730325 733623 := bstep (se 1 (by rfl) ⟨550217, by rfl⟩ : syracuseStep 733623 = 1100435) B1100435
theorem B2470337 : Blo 730325 2470337 := bstep (se 2 (by rfl) ⟨926376, by rfl⟩ : syracuseStep 2470337 = 1852753) B1852753
theorem B733643 : Blo 730325 733643 := bstep (se 1 (by rfl) ⟨550232, by rfl⟩ : syracuseStep 733643 = 1100465) B1100465
theorem B733655 : Blo 730325 733655 := bstep (se 1 (by rfl) ⟨550241, by rfl⟩ : syracuseStep 733655 = 1100483) B1100483
theorem B733675 : Blo 730325 733675 := bstep (se 1 (by rfl) ⟨550256, by rfl⟩ : syracuseStep 733675 = 1100513) B1100513
theorem B733687 : Blo 730325 733687 := bstep (se 1 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 733687 = 1100531) B1100531
theorem B733707 : Blo 730325 733707 := bstep (se 1 (by rfl) ⟨550280, by rfl⟩ : syracuseStep 733707 = 1100561) B1100561
theorem B1651211 : Blo 730325 1651211 := bstep (se 1 (by rfl) ⟨1238408, by rfl⟩ : syracuseStep 1651211 = 2476817) B2476817
theorem B1389079 : Blo 730325 1389079 := bstep (se 1 (by rfl) ⟨1041809, by rfl⟩ : syracuseStep 1389079 = 2083619) B2083619
theorem B733719 : Blo 730325 733719 := bstep (se 1 (by rfl) ⟨550289, by rfl⟩ : syracuseStep 733719 = 1100579) B1100579
theorem B733739 : Blo 730325 733739 := bstep (se 1 (by rfl) ⟨550304, by rfl⟩ : syracuseStep 733739 = 1100609) B1100609
theorem B733751 : Blo 730325 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B1651265 : Blo 730325 1651265 := bstep (se 2 (by rfl) ⟨619224, by rfl⟩ : syracuseStep 1651265 = 1238449) B1238449
theorem B733771 : Blo 730325 733771 := bstep (se 1 (by rfl) ⟨550328, by rfl⟩ : syracuseStep 733771 = 1100657) B1100657
theorem B733783 : Blo 730325 733783 := bstep (se 1 (by rfl) ⟨550337, by rfl⟩ : syracuseStep 733783 = 1100675) B1100675
theorem B733803 : Blo 730325 733803 := bstep (se 1 (by rfl) ⟨550352, by rfl⟩ : syracuseStep 733803 = 1100705) B1100705
theorem B733815 : Blo 730325 733815 := bstep (se 1 (by rfl) ⟨550361, by rfl⟩ : syracuseStep 733815 = 1100723) B1100723
theorem B3125891 : Blo 730325 3125891 := bstep (se 1 (by rfl) ⟨2344418, by rfl⟩ : syracuseStep 3125891 = 4688837) B4688837
theorem B4698755 : Blo 730325 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B733835 : Blo 730325 733835 := bstep (se 1 (by rfl) ⟨550376, by rfl⟩ : syracuseStep 733835 = 1100753) B1100753
theorem B733847 : Blo 730325 733847 := bstep (se 1 (by rfl) ⟨550385, by rfl⟩ : syracuseStep 733847 = 1100771) B1100771
theorem B733867 : Blo 730325 733867 := bstep (se 1 (by rfl) ⟨550400, by rfl⟩ : syracuseStep 733867 = 1100801) B1100801
theorem B733879 : Blo 730325 733879 := bstep (se 1 (by rfl) ⟨550409, by rfl⟩ : syracuseStep 733879 = 1100819) B1100819
theorem B733899 : Blo 730325 733899 := bstep (se 1 (by rfl) ⟨550424, by rfl⟩ : syracuseStep 733899 = 1100849) B1100849
theorem B733911 : Blo 730325 733911 := bstep (se 1 (by rfl) ⟨550433, by rfl⟩ : syracuseStep 733911 = 1100867) B1100867
theorem B733931 : Blo 730325 733931 := bstep (se 1 (by rfl) ⟨550448, by rfl⟩ : syracuseStep 733931 = 1100897) B1100897
theorem B733943 : Blo 730325 733943 := bstep (se 1 (by rfl) ⟨550457, by rfl⟩ : syracuseStep 733943 = 1100915) B1100915
theorem B733963 : Blo 730325 733963 := bstep (se 1 (by rfl) ⟨550472, by rfl⟩ : syracuseStep 733963 = 1100945) B1100945
theorem B733975 : Blo 730325 733975 := bstep (se 1 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 733975 = 1100963) B1100963
theorem B1487641 : Blo 730325 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B1651481 : Blo 730325 1651481 := bstep (se 2 (by rfl) ⟨619305, by rfl⟩ : syracuseStep 1651481 = 1238611) B1238611
theorem B733995 : Blo 730325 733995 := bstep (se 1 (by rfl) ⟨550496, by rfl⟩ : syracuseStep 733995 = 1100993) B1100993
theorem B734007 : Blo 730325 734007 := bstep (se 1 (by rfl) ⟨550505, by rfl⟩ : syracuseStep 734007 = 1101011) B1101011
theorem B2962241 : Blo 730325 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B734027 : Blo 730325 734027 := bstep (se 1 (by rfl) ⟨550520, by rfl⟩ : syracuseStep 734027 = 1101041) B1101041
theorem B734039 : Blo 730325 734039 := bstep (se 1 (by rfl) ⟨550529, by rfl⟩ : syracuseStep 734039 = 1101059) B1101059
theorem B734059 : Blo 730325 734059 := bstep (se 1 (by rfl) ⟨550544, by rfl⟩ : syracuseStep 734059 = 1101089) B1101089
theorem B1651571 : Blo 730325 1651571 := bstep (se 1 (by rfl) ⟨1238678, by rfl⟩ : syracuseStep 1651571 = 2477357) B2477357
theorem B734071 : Blo 730325 734071 := bstep (se 1 (by rfl) ⟨550553, by rfl⟩ : syracuseStep 734071 = 1101107) B1101107
theorem B734091 : Blo 730325 734091 := bstep (se 1 (by rfl) ⟨550568, by rfl⟩ : syracuseStep 734091 = 1101137) B1101137
theorem B1651607 : Blo 730325 1651607 := bstep (se 1 (by rfl) ⟨1238705, by rfl⟩ : syracuseStep 1651607 = 2477411) B2477411
theorem B734103 : Blo 730325 734103 := bstep (se 1 (by rfl) ⟨550577, by rfl⟩ : syracuseStep 734103 = 1101155) B1101155
theorem B734123 : Blo 730325 734123 := bstep (se 1 (by rfl) ⟨550592, by rfl⟩ : syracuseStep 734123 = 1101185) B1101185
theorem B734135 : Blo 730325 734135 := bstep (se 1 (by rfl) ⟨550601, by rfl⟩ : syracuseStep 734135 = 1101203) B1101203
theorem B2962369 : Blo 730325 2962369 := bstep (se 2 (by rfl) ⟨1110888, by rfl⟩ : syracuseStep 2962369 = 2221777) B2221777
theorem B734155 : Blo 730325 734155 := bstep (se 1 (by rfl) ⟨550616, by rfl⟩ : syracuseStep 734155 = 1101233) B1101233
theorem B734167 : Blo 730325 734167 := bstep (se 1 (by rfl) ⟨550625, by rfl⟩ : syracuseStep 734167 = 1101251) B1101251
theorem B2470877 : Blo 730325 2470877 := bstep (se 3 (by rfl) ⟨463289, by rfl⟩ : syracuseStep 2470877 = 926579) B926579
theorem B734187 : Blo 730325 734187 := bstep (se 1 (by rfl) ⟨550640, by rfl⟩ : syracuseStep 734187 = 1101281) B1101281
theorem B734199 : Blo 730325 734199 := bstep (se 1 (by rfl) ⟨550649, by rfl⟩ : syracuseStep 734199 = 1101299) B1101299
theorem B734219 : Blo 730325 734219 := bstep (se 1 (by rfl) ⟨550664, by rfl⟩ : syracuseStep 734219 = 1101329) B1101329
theorem B8434705 : Blo 730325 8434705 := bstep (se 2 (by rfl) ⟨3163014, by rfl⟩ : syracuseStep 8434705 = 6326029) B6326029
theorem B734231 : Blo 730325 734231 := bstep (se 1 (by rfl) ⟨550673, by rfl⟩ : syracuseStep 734231 = 1101347) B1101347
theorem B734251 : Blo 730325 734251 := bstep (se 1 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 734251 = 1101377) B1101377
theorem B734263 : Blo 730325 734263 := bstep (se 1 (by rfl) ⟨550697, by rfl⟩ : syracuseStep 734263 = 1101395) B1101395
theorem B1651787 : Blo 730325 1651787 := bstep (se 1 (by rfl) ⟨1238840, by rfl⟩ : syracuseStep 1651787 = 2477681) B2477681
theorem B734283 : Blo 730325 734283 := bstep (se 1 (by rfl) ⟨550712, by rfl⟩ : syracuseStep 734283 = 1101425) B1101425
theorem B734295 : Blo 730325 734295 := bstep (se 1 (by rfl) ⟨550721, by rfl⟩ : syracuseStep 734295 = 1101443) B1101443
theorem B734315 : Blo 730325 734315 := bstep (se 1 (by rfl) ⟨550736, by rfl⟩ : syracuseStep 734315 = 1101473) B1101473
theorem B1651841 : Blo 730325 1651841 := bstep (se 2 (by rfl) ⟨619440, by rfl⟩ : syracuseStep 1651841 = 1238881) B1238881
theorem B1979585 : Blo 730325 1979585 := bstep (se 2 (by rfl) ⟨742344, by rfl⟩ : syracuseStep 1979585 = 1484689) B1484689
theorem B1389899 : Blo 730325 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B1652057 : Blo 730325 1652057 := bstep (se 2 (by rfl) ⟨619521, by rfl⟩ : syracuseStep 1652057 = 1239043) B1239043
theorem B1389953 : Blo 730325 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B3519875 : Blo 730325 3519875 := bstep (se 1 (by rfl) ⟨2639906, by rfl⟩ : syracuseStep 3519875 = 5279813) B5279813
theorem B832907 : Blo 730325 832907 := bstep (se 1 (by rfl) ⟨624680, by rfl⟩ : syracuseStep 832907 = 1249361) B1249361
theorem B1652147 : Blo 730325 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B1652183 : Blo 730325 1652183 := bstep (se 1 (by rfl) ⟨1239137, by rfl⟩ : syracuseStep 1652183 = 2478275) B2478275
theorem B5551577 : Blo 730325 5551577 := bstep (se 2 (by rfl) ⟨2081841, by rfl⟩ : syracuseStep 5551577 = 4163683) B4163683
theorem B2537153 : Blo 730325 2537153 := bstep (se 2 (by rfl) ⟨951432, by rfl⟩ : syracuseStep 2537153 = 1902865) B1902865
theorem B1128217 : Blo 730325 1128217 := bstep (se 2 (by rfl) ⟨423081, by rfl⟩ : syracuseStep 1128217 = 846163) B846163
theorem B1849139 : Blo 730325 1849139 := bstep (se 1 (by rfl) ⟨1386854, by rfl⟩ : syracuseStep 1849139 = 2773709) B2773709
theorem B1161035 : Blo 730325 1161035 := bstep (se 1 (by rfl) ⟨870776, by rfl⟩ : syracuseStep 1161035 = 1741553) B1741553
theorem B1095563 : Blo 730325 1095563 := bstep (se 1 (by rfl) ⟨821672, by rfl⟩ : syracuseStep 1095563 = 1643345) B1643345
theorem B1095575 : Blo 730325 1095575 := bstep (se 1 (by rfl) ⟨821681, by rfl⟩ : syracuseStep 1095575 = 1643363) B1643363
theorem B1095641 : Blo 730325 1095641 := bstep (se 2 (by rfl) ⟨410865, by rfl⟩ : syracuseStep 1095641 = 821731) B821731
theorem B3749905 : Blo 730325 3749905 := bstep (se 2 (by rfl) ⟨1406214, by rfl⟩ : syracuseStep 3749905 = 2812429) B2812429
theorem B1095755 : Blo 730325 1095755 := bstep (se 1 (by rfl) ⟨821816, by rfl⟩ : syracuseStep 1095755 = 1643633) B1643633
theorem B2472011 : Blo 730325 2472011 := bstep (se 1 (by rfl) ⟨1854008, by rfl⟩ : syracuseStep 2472011 = 3708017) B3708017
theorem B1095767 : Blo 730325 1095767 := bstep (se 1 (by rfl) ⟨821825, by rfl⟩ : syracuseStep 1095767 = 1643651) B1643651
theorem B3717251 : Blo 730325 3717251 := bstep (se 1 (by rfl) ⟨2787938, by rfl⟩ : syracuseStep 3717251 = 5575877) B5575877
theorem B1128587 : Blo 730325 1128587 := bstep (se 1 (by rfl) ⟨846440, by rfl⟩ : syracuseStep 1128587 = 1692881) B1692881
theorem B1095833 : Blo 730325 1095833 := bstep (se 2 (by rfl) ⟨410937, by rfl⟩ : syracuseStep 1095833 = 821875) B821875
theorem B1095947 : Blo 730325 1095947 := bstep (se 1 (by rfl) ⟨821960, by rfl⟩ : syracuseStep 1095947 = 1643921) B1643921
theorem B1095959 : Blo 730325 1095959 := bstep (se 1 (by rfl) ⟨821969, by rfl⟩ : syracuseStep 1095959 = 1643939) B1643939
theorem B1390871 : Blo 730325 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B1849675 : Blo 730325 1849675 := bstep (se 1 (by rfl) ⟨1387256, by rfl⟩ : syracuseStep 1849675 = 2774513) B2774513
theorem B1096025 : Blo 730325 1096025 := bstep (se 2 (by rfl) ⟨411009, by rfl⟩ : syracuseStep 1096025 = 822019) B822019
theorem B2472281 : Blo 730325 2472281 := bstep (se 2 (by rfl) ⟨927105, by rfl⟩ : syracuseStep 2472281 = 1854211) B1854211
theorem B1096139 : Blo 730325 1096139 := bstep (se 1 (by rfl) ⟨822104, by rfl⟩ : syracuseStep 1096139 = 1644209) B1644209
theorem B1096151 : Blo 730325 1096151 := bstep (se 1 (by rfl) ⟨822113, by rfl⟩ : syracuseStep 1096151 = 1644227) B1644227
theorem B1849817 : Blo 730325 1849817 := bstep (se 2 (by rfl) ⟨693681, by rfl⟩ : syracuseStep 1849817 = 1387363) B1387363
theorem B2406935 : Blo 730325 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B1096217 : Blo 730325 1096217 := bstep (se 2 (by rfl) ⟨411081, by rfl⟩ : syracuseStep 1096217 = 822163) B822163
theorem B1096331 : Blo 730325 1096331 := bstep (se 1 (by rfl) ⟨822248, by rfl⟩ : syracuseStep 1096331 = 1644497) B1644497
theorem B1096343 : Blo 730325 1096343 := bstep (se 1 (by rfl) ⟨822257, by rfl⟩ : syracuseStep 1096343 = 1644515) B1644515
theorem B1096409 : Blo 730325 1096409 := bstep (se 2 (by rfl) ⟨411153, by rfl⟩ : syracuseStep 1096409 = 822307) B822307
theorem B1391411 : Blo 730325 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B3128129 : Blo 730325 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B1096523 : Blo 730325 1096523 := bstep (se 1 (by rfl) ⟨822392, by rfl⟩ : syracuseStep 1096523 = 1644785) B1644785
theorem B1096535 : Blo 730325 1096535 := bstep (se 1 (by rfl) ⟨822401, by rfl⟩ : syracuseStep 1096535 = 1644803) B1644803
theorem B1096601 : Blo 730325 1096601 := bstep (se 2 (by rfl) ⟨411225, by rfl⟩ : syracuseStep 1096601 = 822451) B822451
theorem B81476549 : Blo 730325 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1096715 : Blo 730325 1096715 := bstep (se 1 (by rfl) ⟨822536, by rfl⟩ : syracuseStep 1096715 = 1645073) B1645073
theorem B1096727 : Blo 730325 1096727 := bstep (se 1 (by rfl) ⟨822545, by rfl⟩ : syracuseStep 1096727 = 1645091) B1645091
theorem B2472983 : Blo 730325 2472983 := bstep (se 1 (by rfl) ⟨1854737, by rfl⟩ : syracuseStep 2472983 = 3709475) B3709475
theorem B1096793 : Blo 730325 1096793 := bstep (se 2 (by rfl) ⟨411297, by rfl⟩ : syracuseStep 1096793 = 822595) B822595
theorem B1096907 : Blo 730325 1096907 := bstep (se 1 (by rfl) ⟨822680, by rfl⟩ : syracuseStep 1096907 = 1645361) B1645361
theorem B1096919 : Blo 730325 1096919 := bstep (se 1 (by rfl) ⟨822689, by rfl⟩ : syracuseStep 1096919 = 1645379) B1645379
theorem B1850647 : Blo 730325 1850647 := bstep (se 1 (by rfl) ⟨1387985, by rfl⟩ : syracuseStep 1850647 = 2775971) B2775971
theorem B1096985 : Blo 730325 1096985 := bstep (se 2 (by rfl) ⟨411369, by rfl⟩ : syracuseStep 1096985 = 822739) B822739
theorem B1391897 : Blo 730325 1391897 := bstep (se 2 (by rfl) ⟨521961, by rfl⟩ : syracuseStep 1391897 = 1043923) B1043923
theorem B1588567 : Blo 730325 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B1097099 : Blo 730325 1097099 := bstep (se 1 (by rfl) ⟨822824, by rfl⟩ : syracuseStep 1097099 = 1645649) B1645649
theorem B1097111 : Blo 730325 1097111 := bstep (se 1 (by rfl) ⟨822833, by rfl⟩ : syracuseStep 1097111 = 1645667) B1645667
theorem B4177331 : Blo 730325 4177331 := bstep (se 1 (by rfl) ⟨3132998, by rfl⟩ : syracuseStep 4177331 = 6265997) B6265997
theorem B1097177 : Blo 730325 1097177 := bstep (se 2 (by rfl) ⟨411441, by rfl⟩ : syracuseStep 1097177 = 822883) B822883
theorem B2473523 : Blo 730325 2473523 := bstep (se 1 (by rfl) ⟨1855142, by rfl⟩ : syracuseStep 2473523 = 3710285) B3710285
theorem B1097291 : Blo 730325 1097291 := bstep (se 1 (by rfl) ⟨822968, by rfl⟩ : syracuseStep 1097291 = 1645937) B1645937
theorem B1097303 : Blo 730325 1097303 := bstep (se 1 (by rfl) ⟨822977, by rfl⟩ : syracuseStep 1097303 = 1645955) B1645955
theorem B1097369 : Blo 730325 1097369 := bstep (se 2 (by rfl) ⟨411513, by rfl⟩ : syracuseStep 1097369 = 823027) B823027
theorem B2637485 : Blo 730325 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B1851083 : Blo 730325 1851083 := bstep (se 1 (by rfl) ⟨1388312, by rfl⟩ : syracuseStep 1851083 = 2776625) B2776625
theorem B2637515 : Blo 730325 2637515 := bstep (se 1 (by rfl) ⟨1978136, by rfl⟩ : syracuseStep 2637515 = 3956273) B3956273
theorem B1097483 : Blo 730325 1097483 := bstep (se 1 (by rfl) ⟨823112, by rfl⟩ : syracuseStep 1097483 = 1646225) B1646225
theorem B1097495 : Blo 730325 1097495 := bstep (se 1 (by rfl) ⟨823121, by rfl⟩ : syracuseStep 1097495 = 1646243) B1646243
theorem B2473793 : Blo 730325 2473793 := bstep (se 2 (by rfl) ⟨927672, by rfl⟩ : syracuseStep 2473793 = 1855345) B1855345
theorem B1097561 : Blo 730325 1097561 := bstep (se 2 (by rfl) ⟨411585, by rfl⟩ : syracuseStep 1097561 = 823171) B823171
theorem B1097675 : Blo 730325 1097675 := bstep (se 1 (by rfl) ⟨823256, by rfl⟩ : syracuseStep 1097675 = 1646513) B1646513
theorem B1097687 : Blo 730325 1097687 := bstep (se 1 (by rfl) ⟨823265, by rfl⟩ : syracuseStep 1097687 = 1646531) B1646531
theorem B1097753 : Blo 730325 1097753 := bstep (se 2 (by rfl) ⟨411657, by rfl⟩ : syracuseStep 1097753 = 823315) B823315
theorem B1851457 : Blo 730325 1851457 := bstep (se 2 (by rfl) ⟨694296, by rfl⟩ : syracuseStep 1851457 = 1388593) B1388593
theorem B1097867 : Blo 730325 1097867 := bstep (se 1 (by rfl) ⟨823400, by rfl⟩ : syracuseStep 1097867 = 1646801) B1646801
theorem B1097879 : Blo 730325 1097879 := bstep (se 1 (by rfl) ⟨823409, by rfl⟩ : syracuseStep 1097879 = 1646819) B1646819
theorem B1982657 : Blo 730325 1982657 := bstep (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) B1486993
theorem B1097945 : Blo 730325 1097945 := bstep (se 2 (by rfl) ⟨411729, by rfl⟩ : syracuseStep 1097945 = 823459) B823459
theorem B1098059 : Blo 730325 1098059 := bstep (se 1 (by rfl) ⟨823544, by rfl⟩ : syracuseStep 1098059 = 1647089) B1647089
theorem B1098071 : Blo 730325 1098071 := bstep (se 1 (by rfl) ⟨823553, by rfl⟩ : syracuseStep 1098071 = 1647107) B1647107
theorem B2474333 : Blo 730325 2474333 := bstep (se 3 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 2474333 = 927875) B927875
theorem B1098137 : Blo 730325 1098137 := bstep (se 2 (by rfl) ⟨411801, by rfl⟩ : syracuseStep 1098137 = 823603) B823603
theorem B2081227 : Blo 730325 2081227 := bstep (se 1 (by rfl) ⟨1560920, by rfl⟩ : syracuseStep 2081227 = 3121841) B3121841
theorem B3129803 : Blo 730325 3129803 := bstep (se 1 (by rfl) ⟨2347352, by rfl⟩ : syracuseStep 3129803 = 4694705) B4694705
theorem B1098251 : Blo 730325 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B23708173 : Blo 730325 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1098263 : Blo 730325 1098263 := bstep (se 1 (by rfl) ⟨823697, by rfl⟩ : syracuseStep 1098263 = 1647395) B1647395
theorem B836119 : Blo 730325 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1098329 : Blo 730325 1098329 := bstep (se 2 (by rfl) ⟨411873, by rfl⟩ : syracuseStep 1098329 = 823747) B823747
theorem B1852055 : Blo 730325 1852055 := bstep (se 1 (by rfl) ⟨1389041, by rfl⟩ : syracuseStep 1852055 = 2778083) B2778083
theorem B1098443 : Blo 730325 1098443 := bstep (se 1 (by rfl) ⟨823832, by rfl⟩ : syracuseStep 1098443 = 1647665) B1647665
theorem B1393355 : Blo 730325 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B1098455 : Blo 730325 1098455 := bstep (se 1 (by rfl) ⟨823841, by rfl⟩ : syracuseStep 1098455 = 1647683) B1647683
theorem B2081501 : Blo 730325 2081501 := bstep (se 3 (by rfl) ⟨390281, by rfl⟩ : syracuseStep 2081501 = 780563) B780563
theorem B1098521 : Blo 730325 1098521 := bstep (se 2 (by rfl) ⟨411945, by rfl⟩ : syracuseStep 1098521 = 823891) B823891
theorem B5554979 : Blo 730325 5554979 := bstep (se 1 (by rfl) ⟨4166234, by rfl⟩ : syracuseStep 5554979 = 8332469) B8332469
theorem B4997963 : Blo 730325 4997963 := bstep (se 1 (by rfl) ⟨3748472, by rfl⟩ : syracuseStep 4997963 = 7496945) B7496945
theorem B4178789 : Blo 730325 4178789 := bstep (se 4 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 4178789 = 783523) B783523
theorem B1393537 : Blo 730325 1393537 := bstep (se 2 (by rfl) ⟨522576, by rfl⟩ : syracuseStep 1393537 = 1045153) B1045153
theorem B1098635 : Blo 730325 1098635 := bstep (se 1 (by rfl) ⟨823976, by rfl⟩ : syracuseStep 1098635 = 1647953) B1647953
theorem B1098647 : Blo 730325 1098647 := bstep (se 1 (by rfl) ⟨823985, by rfl⟩ : syracuseStep 1098647 = 1647971) B1647971
theorem B1098713 : Blo 730325 1098713 := bstep (se 2 (by rfl) ⟨412017, by rfl⟩ : syracuseStep 1098713 = 824035) B824035
theorem B1098827 : Blo 730325 1098827 := bstep (se 1 (by rfl) ⟨824120, by rfl⟩ : syracuseStep 1098827 = 1648241) B1648241
theorem B1098839 : Blo 730325 1098839 := bstep (se 1 (by rfl) ⟨824129, by rfl⟩ : syracuseStep 1098839 = 1648259) B1648259
theorem B1098905 : Blo 730325 1098905 := bstep (se 2 (by rfl) ⟨412089, by rfl⟩ : syracuseStep 1098905 = 824179) B824179
theorem B3130589 : Blo 730325 3130589 := bstep (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) B1173971
theorem B1099019 : Blo 730325 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B1099031 : Blo 730325 1099031 := bstep (se 1 (by rfl) ⟨824273, by rfl⟩ : syracuseStep 1099031 = 1648547) B1648547
theorem B1393985 : Blo 730325 1393985 := bstep (se 2 (by rfl) ⟨522744, by rfl⟩ : syracuseStep 1393985 = 1045489) B1045489
theorem B1099097 : Blo 730325 1099097 := bstep (se 2 (by rfl) ⟨412161, by rfl⟩ : syracuseStep 1099097 = 824323) B824323
theorem B1852865 : Blo 730325 1852865 := bstep (se 2 (by rfl) ⟨694824, by rfl⟩ : syracuseStep 1852865 = 1389649) B1389649
theorem B1099211 : Blo 730325 1099211 := bstep (se 1 (by rfl) ⟨824408, by rfl⟩ : syracuseStep 1099211 = 1648817) B1648817
theorem B2475467 : Blo 730325 2475467 := bstep (se 1 (by rfl) ⟨1856600, by rfl⟩ : syracuseStep 2475467 = 3713201) B3713201
theorem B1099223 : Blo 730325 1099223 := bstep (se 1 (by rfl) ⟨824417, by rfl⟩ : syracuseStep 1099223 = 1648835) B1648835
theorem B1099289 : Blo 730325 1099289 := bstep (se 2 (by rfl) ⟨412233, by rfl⟩ : syracuseStep 1099289 = 824467) B824467
theorem B1099403 : Blo 730325 1099403 := bstep (se 1 (by rfl) ⟨824552, by rfl⟩ : syracuseStep 1099403 = 1649105) B1649105
theorem B1099415 : Blo 730325 1099415 := bstep (se 1 (by rfl) ⟨824561, by rfl⟩ : syracuseStep 1099415 = 1649123) B1649123
theorem B1099481 : Blo 730325 1099481 := bstep (se 2 (by rfl) ⟨412305, by rfl⟩ : syracuseStep 1099481 = 824611) B824611
theorem B2475737 : Blo 730325 2475737 := bstep (se 2 (by rfl) ⟨928401, by rfl⟩ : syracuseStep 2475737 = 1856803) B1856803
theorem B2344727 : Blo 730325 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B1099595 : Blo 730325 1099595 := bstep (se 1 (by rfl) ⟨824696, by rfl⟩ : syracuseStep 1099595 = 1649393) B1649393
theorem B1099607 : Blo 730325 1099607 := bstep (se 1 (by rfl) ⟨824705, by rfl⟩ : syracuseStep 1099607 = 1649411) B1649411
theorem B1099673 : Blo 730325 1099673 := bstep (se 2 (by rfl) ⟨412377, by rfl⟩ : syracuseStep 1099673 = 824755) B824755
theorem B1853401 : Blo 730325 1853401 := bstep (se 2 (by rfl) ⟨695025, by rfl⟩ : syracuseStep 1853401 = 1390051) B1390051
theorem B1099787 : Blo 730325 1099787 := bstep (se 1 (by rfl) ⟨824840, by rfl⟩ : syracuseStep 1099787 = 1649681) B1649681
theorem B1099799 : Blo 730325 1099799 := bstep (se 1 (by rfl) ⟨824849, by rfl⟩ : syracuseStep 1099799 = 1649699) B1649699
theorem B12535883 : Blo 730325 12535883 := bstep (se 1 (by rfl) ⟨9401912, by rfl⟩ : syracuseStep 12535883 = 18803825) B18803825
theorem B1099865 : Blo 730325 1099865 := bstep (se 2 (by rfl) ⟨412449, by rfl⟩ : syracuseStep 1099865 = 824899) B824899
theorem B13355189 : Blo 730325 13355189 := bstep (se 5 (by rfl) ⟨626024, by rfl⟩ : syracuseStep 13355189 = 1252049) B1252049
theorem B1099979 : Blo 730325 1099979 := bstep (se 1 (by rfl) ⟨824984, by rfl⟩ : syracuseStep 1099979 = 1649969) B1649969
theorem B1099991 : Blo 730325 1099991 := bstep (se 1 (by rfl) ⟨824993, by rfl⟩ : syracuseStep 1099991 = 1649987) B1649987
theorem B1984733 : Blo 730325 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B1100057 : Blo 730325 1100057 := bstep (se 2 (by rfl) ⟨412521, by rfl⟩ : syracuseStep 1100057 = 825043) B825043
theorem B1100171 : Blo 730325 1100171 := bstep (se 1 (by rfl) ⟨825128, by rfl⟩ : syracuseStep 1100171 = 1650257) B1650257
theorem B1100183 : Blo 730325 1100183 := bstep (se 1 (by rfl) ⟨825137, by rfl⟩ : syracuseStep 1100183 = 1650275) B1650275
theorem B2476439 : Blo 730325 2476439 := bstep (se 1 (by rfl) ⟨1857329, by rfl⟩ : syracuseStep 2476439 = 3714659) B3714659
theorem B4639193 : Blo 730325 4639193 := bstep (se 2 (by rfl) ⟨1739697, by rfl⟩ : syracuseStep 4639193 = 3479395) B3479395
theorem B1100249 : Blo 730325 1100249 := bstep (se 2 (by rfl) ⟨412593, by rfl⟩ : syracuseStep 1100249 = 825187) B825187
theorem B3131921 : Blo 730325 3131921 := bstep (se 2 (by rfl) ⟨1174470, by rfl⟩ : syracuseStep 3131921 = 2348941) B2348941
theorem B1100363 : Blo 730325 1100363 := bstep (se 1 (by rfl) ⟨825272, by rfl⟩ : syracuseStep 1100363 = 1650545) B1650545
theorem B1100375 : Blo 730325 1100375 := bstep (se 1 (by rfl) ⟨825281, by rfl⟩ : syracuseStep 1100375 = 1650563) B1650563
theorem B8931971 : Blo 730325 8931971 := bstep (se 1 (by rfl) ⟨6698978, by rfl⟩ : syracuseStep 8931971 = 13397957) B13397957
theorem B7031447 : Blo 730325 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B1100441 : Blo 730325 1100441 := bstep (se 2 (by rfl) ⟨412665, by rfl⟩ : syracuseStep 1100441 = 825331) B825331
theorem B1100555 : Blo 730325 1100555 := bstep (se 1 (by rfl) ⟨825416, by rfl⟩ : syracuseStep 1100555 = 1650833) B1650833
theorem B1100567 : Blo 730325 1100567 := bstep (se 1 (by rfl) ⟨825425, by rfl⟩ : syracuseStep 1100567 = 1650851) B1650851
theorem B1100633 : Blo 730325 1100633 := bstep (se 2 (by rfl) ⟨412737, by rfl⟩ : syracuseStep 1100633 = 825475) B825475
theorem B7129957 : Blo 730325 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B1756055 : Blo 730325 1756055 := bstep (se 1 (by rfl) ⟨1317041, by rfl⟩ : syracuseStep 1756055 = 2634083) B2634083
theorem B2673587 : Blo 730325 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B2476979 : Blo 730325 2476979 := bstep (se 1 (by rfl) ⟨1857734, by rfl⟩ : syracuseStep 2476979 = 3715469) B3715469
theorem B1100747 : Blo 730325 1100747 := bstep (se 1 (by rfl) ⟨825560, by rfl⟩ : syracuseStep 1100747 = 1651121) B1651121
theorem B1100759 : Blo 730325 1100759 := bstep (se 1 (by rfl) ⟨825569, by rfl⟩ : syracuseStep 1100759 = 1651139) B1651139
theorem B2083801 : Blo 730325 2083801 := bstep (se 2 (by rfl) ⟨781425, by rfl⟩ : syracuseStep 2083801 = 1562851) B1562851
theorem B1100825 : Blo 730325 1100825 := bstep (se 2 (by rfl) ⟨412809, by rfl⟩ : syracuseStep 1100825 = 825619) B825619
theorem B1854515 : Blo 730325 1854515 := bstep (se 1 (by rfl) ⟨1390886, by rfl⟩ : syracuseStep 1854515 = 2781773) B2781773
theorem B10538059 : Blo 730325 10538059 := bstep (se 1 (by rfl) ⟨7903544, by rfl⟩ : syracuseStep 10538059 = 15807089) B15807089
theorem B2346059 : Blo 730325 2346059 := bstep (se 1 (by rfl) ⟨1759544, by rfl⟩ : syracuseStep 2346059 = 3519089) B3519089
theorem B1100939 : Blo 730325 1100939 := bstep (se 1 (by rfl) ⟨825704, by rfl⟩ : syracuseStep 1100939 = 1651409) B1651409
theorem B1100951 : Blo 730325 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B2477249 : Blo 730325 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1756363 : Blo 730325 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B1101017 : Blo 730325 1101017 := bstep (se 2 (by rfl) ⟨412881, by rfl⟩ : syracuseStep 1101017 = 825763) B825763
theorem B2641175 : Blo 730325 2641175 := bstep (se 1 (by rfl) ⟨1980881, by rfl⟩ : syracuseStep 2641175 = 3961763) B3961763
theorem B1101131 : Blo 730325 1101131 := bstep (se 1 (by rfl) ⟨825848, by rfl⟩ : syracuseStep 1101131 = 1651697) B1651697
theorem B1101143 : Blo 730325 1101143 := bstep (se 1 (by rfl) ⟨825857, by rfl⟩ : syracuseStep 1101143 = 1651715) B1651715
theorem B1854809 : Blo 730325 1854809 := bstep (se 2 (by rfl) ⟨695553, by rfl⟩ : syracuseStep 1854809 = 1391107) B1391107
theorem B1101209 : Blo 730325 1101209 := bstep (se 2 (by rfl) ⟨412953, by rfl⟩ : syracuseStep 1101209 = 825907) B825907
theorem B1101323 : Blo 730325 1101323 := bstep (se 1 (by rfl) ⟨825992, by rfl⟩ : syracuseStep 1101323 = 1651985) B1651985
theorem B1101335 : Blo 730325 1101335 := bstep (se 1 (by rfl) ⟨826001, by rfl⟩ : syracuseStep 1101335 = 1652003) B1652003
theorem B2084417 : Blo 730325 2084417 := bstep (se 2 (by rfl) ⟨781656, by rfl⟩ : syracuseStep 2084417 = 1563313) B1563313
theorem B1560151 : Blo 730325 1560151 := bstep (se 1 (by rfl) ⟨1170113, by rfl⟩ : syracuseStep 1560151 = 2340227) B2340227
theorem B1101401 : Blo 730325 1101401 := bstep (se 2 (by rfl) ⟨413025, by rfl⟩ : syracuseStep 1101401 = 826051) B826051
theorem B2477789 : Blo 730325 2477789 := bstep (se 3 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 2477789 = 929171) B929171
theorem B3133187 : Blo 730325 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B1232651 : Blo 730325 1232651 := bstep (se 1 (by rfl) ⟨924488, by rfl⟩ : syracuseStep 1232651 = 1848977) B1848977
theorem B1232779 : Blo 730325 1232779 := bstep (se 1 (by rfl) ⟨924584, by rfl⟩ : syracuseStep 1232779 = 1849169) B1849169
theorem B741323 : Blo 730325 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B1232921 : Blo 730325 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B1233049 : Blo 730325 1233049 := bstep (se 2 (by rfl) ⟨462393, by rfl⟩ : syracuseStep 1233049 = 924787) B924787
theorem B1003735 : Blo 730325 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B2347699 : Blo 730325 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1233623 : Blo 730325 1233623 := bstep (se 1 (by rfl) ⟨925217, by rfl⟩ : syracuseStep 1233623 = 1850435) B1850435
theorem B1561331 : Blo 730325 1561331 := bstep (se 1 (by rfl) ⟨1170998, by rfl⟩ : syracuseStep 1561331 = 2341997) B2341997
theorem B1233751 : Blo 730325 1233751 := bstep (se 1 (by rfl) ⟨925313, by rfl⟩ : syracuseStep 1233751 = 1850627) B1850627
theorem B2642777 : Blo 730325 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B1856459 : Blo 730325 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B2774195 : Blo 730325 2774195 := bstep (se 1 (by rfl) ⟨2080646, by rfl⟩ : syracuseStep 2774195 = 4161293) B4161293
theorem B2774209 : Blo 730325 2774209 := bstep (se 2 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 2774209 = 2080657) B2080657
theorem B2643137 : Blo 730325 2643137 := bstep (se 2 (by rfl) ⟨991176, by rfl⟩ : syracuseStep 2643137 = 1982353) B1982353
theorem B1758515 : Blo 730325 1758515 := bstep (se 1 (by rfl) ⟨1318886, by rfl⟩ : syracuseStep 1758515 = 2637773) B2637773
theorem B1758553 : Blo 730325 1758553 := bstep (se 2 (by rfl) ⟨659457, by rfl⟩ : syracuseStep 1758553 = 1318915) B1318915
theorem B1234379 : Blo 730325 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B2119115 : Blo 730325 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1234507 : Blo 730325 1234507 := bstep (se 1 (by rfl) ⟨925880, by rfl⟩ : syracuseStep 1234507 = 1851761) B1851761
theorem B939607 : Blo 730325 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B2086489 : Blo 730325 2086489 := bstep (se 2 (by rfl) ⟨782433, by rfl⟩ : syracuseStep 2086489 = 1564867) B1564867
theorem B2348633 : Blo 730325 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B1005259 : Blo 730325 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B1234649 : Blo 730325 1234649 := bstep (se 2 (by rfl) ⟨462993, by rfl⟩ : syracuseStep 1234649 = 925987) B925987
theorem B1234777 : Blo 730325 1234777 := bstep (se 2 (by rfl) ⟨463041, by rfl⟩ : syracuseStep 1234777 = 926083) B926083
theorem B1857431 : Blo 730325 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1562561 : Blo 730325 1562561 := bstep (se 2 (by rfl) ⟨585960, by rfl⟩ : syracuseStep 1562561 = 1171921) B1171921
theorem B2348993 : Blo 730325 2348993 := bstep (se 2 (by rfl) ⟨880872, by rfl⟩ : syracuseStep 2348993 = 1761745) B1761745
theorem B2086877 : Blo 730325 2086877 := bstep (se 3 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 2086877 = 782579) B782579
theorem B5560325 : Blo 730325 5560325 := bstep (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) B1042561
theorem B1235351 : Blo 730325 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1235479 : Blo 730325 1235479 := bstep (se 1 (by rfl) ⟨926609, by rfl⟩ : syracuseStep 1235479 = 1853219) B1853219
theorem B1858099 : Blo 730325 1858099 := bstep (se 1 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 1858099 = 2787149) B2787149
theorem B1858241 : Blo 730325 1858241 := bstep (se 2 (by rfl) ⟨696840, by rfl⟩ : syracuseStep 1858241 = 1393681) B1393681
theorem B3136279 : Blo 730325 3136279 := bstep (se 1 (by rfl) ⟨2352209, by rfl⟩ : syracuseStep 3136279 = 4704419) B4704419
theorem B3333143 : Blo 730325 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1563671 : Blo 730325 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B10017827 : Blo 730325 10017827 := bstep (se 1 (by rfl) ⟨7513370, by rfl⟩ : syracuseStep 10017827 = 15026741) B15026741
theorem B2776139 : Blo 730325 2776139 := bstep (se 1 (by rfl) ⟨2082104, by rfl⟩ : syracuseStep 2776139 = 4164209) B4164209
theorem B2776153 : Blo 730325 2776153 := bstep (se 2 (by rfl) ⟨1041057, by rfl⟩ : syracuseStep 2776153 = 2082115) B2082115
theorem B1236107 : Blo 730325 1236107 := bstep (se 1 (by rfl) ⟨927080, by rfl⟩ : syracuseStep 1236107 = 1854161) B1854161
theorem B1236235 : Blo 730325 1236235 := bstep (se 1 (by rfl) ⟨927176, by rfl⟩ : syracuseStep 1236235 = 1854353) B1854353
theorem B1236377 : Blo 730325 1236377 := bstep (se 2 (by rfl) ⟨463641, by rfl⟩ : syracuseStep 1236377 = 927283) B927283
theorem B1236505 : Blo 730325 1236505 := bstep (se 2 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 1236505 = 927379) B927379
theorem B19259201 : Blo 730325 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B1040215 : Blo 730325 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B2777111 : Blo 730325 2777111 := bstep (se 1 (by rfl) ⟨2082833, by rfl⟩ : syracuseStep 2777111 = 4165667) B4165667
theorem B1564697 : Blo 730325 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B1237079 : Blo 730325 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B5267587 : Blo 730325 5267587 := bstep (se 1 (by rfl) ⟨3950690, by rfl⟩ : syracuseStep 5267587 = 7901381) B7901381
theorem B1237207 : Blo 730325 1237207 := bstep (se 1 (by rfl) ⟨927905, by rfl⟩ : syracuseStep 1237207 = 1855811) B1855811
theorem B11297009 : Blo 730325 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B5562755 : Blo 730325 5562755 := bstep (se 1 (by rfl) ⟨4172066, by rfl⟩ : syracuseStep 5562755 = 8344133) B8344133
theorem B1040779 : Blo 730325 1040779 := bstep (se 1 (by rfl) ⟨780584, by rfl⟩ : syracuseStep 1040779 = 1561169) B1561169
theorem B12706379 : Blo 730325 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B10543709 : Blo 730325 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B1172107 : Blo 730325 1172107 := bstep (se 1 (by rfl) ⟨879080, by rfl⟩ : syracuseStep 1172107 = 1758161) B1758161
theorem B25420493 : Blo 730325 25420493 := bstep (se 3 (by rfl) ⟨4766342, by rfl⟩ : syracuseStep 25420493 = 9532685) B9532685
theorem B2089793 : Blo 730325 2089793 := bstep (se 2 (by rfl) ⟨783672, by rfl⟩ : syracuseStep 2089793 = 1567345) B1567345
theorem B1237835 : Blo 730325 1237835 := bstep (se 1 (by rfl) ⟨928376, by rfl⟩ : syracuseStep 1237835 = 1856753) B1856753
theorem B2089907 : Blo 730325 2089907 := bstep (se 1 (by rfl) ⟨1567430, by rfl⟩ : syracuseStep 2089907 = 3134861) B3134861
theorem B1237963 : Blo 730325 1237963 := bstep (se 1 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 1237963 = 1856945) B1856945
theorem B1238105 : Blo 730325 1238105 := bstep (se 2 (by rfl) ⟨464289, by rfl⟩ : syracuseStep 1238105 = 928579) B928579
theorem B1238233 : Blo 730325 1238233 := bstep (se 2 (by rfl) ⟨464337, by rfl⟩ : syracuseStep 1238233 = 928675) B928675
theorem B2778371 : Blo 730325 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B32531717 : Blo 730325 32531717 := bstep (se 4 (by rfl) ⟨3049848, by rfl⟩ : syracuseStep 32531717 = 6099697) B6099697
theorem B6350411 : Blo 730325 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B1566337 : Blo 730325 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B1238807 : Blo 730325 1238807 := bstep (se 1 (by rfl) ⟨929105, by rfl⟩ : syracuseStep 1238807 = 1858211) B1858211
theorem B8021825 : Blo 730325 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B1042265 : Blo 730325 1042265 := bstep (se 2 (by rfl) ⟨390849, by rfl⟩ : syracuseStep 1042265 = 781699) B781699
theorem B1238935 : Blo 730325 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B12707761 : Blo 730325 12707761 := bstep (se 2 (by rfl) ⟨4765410, by rfl⟩ : syracuseStep 12707761 = 9530821) B9530821
theorem B3008477 : Blo 730325 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B780311 : Blo 730325 780311 := bstep (se 1 (by rfl) ⟨585233, by rfl⟩ : syracuseStep 780311 = 1170467) B1170467
theorem B1763417 : Blo 730325 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B1566935 : Blo 730325 1566935 := bstep (se 1 (by rfl) ⟨1175201, by rfl⟩ : syracuseStep 1566935 = 2350403) B2350403
theorem B6252875 : Blo 730325 6252875 := bstep (se 1 (by rfl) ⟨4689656, by rfl⟩ : syracuseStep 6252875 = 9379313) B9379313
theorem B1042903 : Blo 730325 1042903 := bstep (se 1 (by rfl) ⟨782177, by rfl⟩ : syracuseStep 1042903 = 1564355) B1564355
theorem B846347 : Blo 730325 846347 := bstep (se 1 (by rfl) ⟨634760, by rfl⟩ : syracuseStep 846347 = 1269521) B1269521
theorem B1272407 : Blo 730325 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B3959513 : Blo 730325 3959513 := bstep (se 2 (by rfl) ⟨1484817, by rfl⟩ : syracuseStep 3959513 = 2969635) B2969635
theorem B1043609 : Blo 730325 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B2223325 : Blo 730325 2223325 := bstep (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) B833747
theorem B1043723 : Blo 730325 1043723 := bstep (se 1 (by rfl) ⟨782792, by rfl⟩ : syracuseStep 1043723 = 1565585) B1565585
theorem B1568011 : Blo 730325 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B5566157 : Blo 730325 5566157 := bstep (se 3 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 5566157 = 2087309) B2087309
theorem B1044247 : Blo 730325 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B11300957 : Blo 730325 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B6025367 : Blo 730325 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B5566643 : Blo 730325 5566643 := bstep (se 1 (by rfl) ⟨4174982, by rfl⟩ : syracuseStep 5566643 = 8349965) B8349965
theorem B782519 : Blo 730325 782519 := bstep (se 1 (by rfl) ⟨586889, by rfl⟩ : syracuseStep 782519 = 1173779) B1173779
theorem B2781485 : Blo 730325 2781485 := bstep (se 3 (by rfl) ⟨521528, by rfl⟩ : syracuseStep 2781485 = 1043057) B1043057
theorem B2814401 : Blo 730325 2814401 := bstep (se 2 (by rfl) ⟨1055400, by rfl⟩ : syracuseStep 2814401 = 2110801) B2110801
theorem B1110475 : Blo 730325 1110475 := bstep (se 1 (by rfl) ⟨832856, by rfl⟩ : syracuseStep 1110475 = 1665713) B1665713
theorem B1045067 : Blo 730325 1045067 := bstep (se 1 (by rfl) ⟨783800, by rfl⟩ : syracuseStep 1045067 = 1567601) B1567601
theorem B10678877 : Blo 730325 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B9401093 : Blo 730325 9401093 := bstep (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) B1762705
theorem B5010221 : Blo 730325 5010221 := bstep (se 3 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 5010221 = 1878833) B1878833
theorem B2782259 : Blo 730325 2782259 := bstep (se 1 (by rfl) ⟨2086694, by rfl⟩ : syracuseStep 2782259 = 4173389) B4173389
theorem B3339671 : Blo 730325 3339671 := bstep (se 1 (by rfl) ⟨2504753, by rfl⟩ : syracuseStep 3339671 = 5009507) B5009507
theorem B3175901 : Blo 730325 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B3700241 : Blo 730325 3700241 := bstep (se 2 (by rfl) ⟨1387590, by rfl⟩ : syracuseStep 3700241 = 2775181) B2775181
theorem B5568101 : Blo 730325 5568101 := bstep (se 4 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 5568101 = 1044019) B1044019
theorem B3700403 : Blo 730325 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B3799057 : Blo 730325 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B5568587 : Blo 730325 5568587 := bstep (se 1 (by rfl) ⟨4176440, by rfl⟩ : syracuseStep 5568587 = 8352881) B8352881
theorem B1112215 : Blo 730325 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B1407449 : Blo 730325 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B2783747 : Blo 730325 2783747 := bstep (se 1 (by rfl) ⟨2087810, by rfl⟩ : syracuseStep 2783747 = 4175621) B4175621
theorem B2259479 : Blo 730325 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B8354339 : Blo 730325 8354339 := bstep (se 1 (by rfl) ⟨6265754, by rfl⟩ : syracuseStep 8354339 = 12531509) B12531509
theorem B5569175 : Blo 730325 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B19037105 : Blo 730325 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B2784203 : Blo 730325 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B3341315 : Blo 730325 3341315 := bstep (se 1 (by rfl) ⟨2505986, by rfl⟩ : syracuseStep 3341315 = 5011973) B5011973
theorem B2784401 : Blo 730325 2784401 := bstep (se 2 (by rfl) ⟨1044150, by rfl⟩ : syracuseStep 2784401 = 2088301) B2088301
theorem B4750609 : Blo 730325 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B4685273 : Blo 730325 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B4161041 : Blo 730325 4161041 := bstep (se 2 (by rfl) ⟨1560390, by rfl⟩ : syracuseStep 4161041 = 3120781) B3120781
theorem B3702347 : Blo 730325 3702347 := bstep (se 1 (by rfl) ⟨2776760, by rfl⟩ : syracuseStep 3702347 = 5553521) B5553521
theorem B31620739 : Blo 730325 31620739 := bstep (se 1 (by rfl) ⟨23715554, by rfl⟩ : syracuseStep 31620739 = 47431109) B47431109
theorem B3014347 : Blo 730325 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B4685633 : Blo 730325 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B2785175 : Blo 730325 2785175 := bstep (se 1 (by rfl) ⟨2088881, by rfl⟩ : syracuseStep 2785175 = 4177763) B4177763
theorem B3703319 : Blo 730325 3703319 := bstep (se 1 (by rfl) ⟨2777489, by rfl⟩ : syracuseStep 3703319 = 5554979) B5554979
theorem B2785859 : Blo 730325 2785859 := bstep (se 1 (by rfl) ⟨2089394, by rfl⟩ : syracuseStep 2785859 = 4178789) B4178789
theorem B1114825 : Blo 730325 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B8357255 : Blo 730325 8357255 := bstep (se 1 (by rfl) ⟨6267941, by rfl⟩ : syracuseStep 8357255 = 12535883) B12535883
theorem B2786845 : Blo 730325 2786845 := bstep (se 3 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 2786845 = 1045067) B1045067
theorem B4687631 : Blo 730325 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B821767 : Blo 730325 821767 := bstep (se 1 (by rfl) ⟨616325, by rfl⟩ : syracuseStep 821767 = 1232651) B1232651
theorem B16943681 : Blo 730325 16943681 := bstep (se 2 (by rfl) ⟨6353880, by rfl⟩ : syracuseStep 16943681 = 12707761) B12707761
theorem B821947 : Blo 730325 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B822415 : Blo 730325 822415 := bstep (se 1 (by rfl) ⟨616811, by rfl⟩ : syracuseStep 822415 = 1233623) B1233623
theorem B3509725 : Blo 730325 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B4689373 : Blo 730325 4689373 := bstep (se 3 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 4689373 = 1758515) B1758515
theorem B3706397 : Blo 730325 3706397 := bstep (se 3 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 3706397 = 1389899) B1389899
theorem B822919 : Blo 730325 822919 := bstep (se 1 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 822919 = 1234379) B1234379
theorem B1412743 : Blo 730325 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B9506609 : Blo 730325 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B823099 : Blo 730325 823099 := bstep (se 1 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 823099 = 1234649) B1234649
theorem B3706883 : Blo 730325 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B6263021 : Blo 730325 6263021 := bstep (se 3 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 6263021 = 2348633) B2348633
theorem B823567 : Blo 730325 823567 := bstep (se 1 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 823567 = 1235351) B1235351
theorem B824071 : Blo 730325 824071 := bstep (se 1 (by rfl) ⟨618053, by rfl⟩ : syracuseStep 824071 = 1236107) B1236107
theorem B1643399 : Blo 730325 1643399 := bstep (se 1 (by rfl) ⟨1232549, by rfl⟩ : syracuseStep 1643399 = 2465099) B2465099
theorem B824251 : Blo 730325 824251 := bstep (se 1 (by rfl) ⟨618188, by rfl⟩ : syracuseStep 824251 = 1236377) B1236377
theorem B1643579 : Blo 730325 1643579 := bstep (se 1 (by rfl) ⟨1232684, by rfl⟩ : syracuseStep 1643579 = 2465369) B2465369
theorem B4461655 : Blo 730325 4461655 := bstep (se 1 (by rfl) ⟨3346241, by rfl⟩ : syracuseStep 4461655 = 6692483) B6692483
theorem B1643705 : Blo 730325 1643705 := bstep (se 2 (by rfl) ⟨616389, by rfl⟩ : syracuseStep 1643705 = 1232779) B1232779
theorem B5641607 : Blo 730325 5641607 := bstep (se 1 (by rfl) ⟨4231205, by rfl⟩ : syracuseStep 5641607 = 8462411) B8462411
theorem B824719 : Blo 730325 824719 := bstep (se 1 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 824719 = 1237079) B1237079
theorem B1644047 : Blo 730325 1644047 := bstep (se 1 (by rfl) ⟨1233035, by rfl⟩ : syracuseStep 1644047 = 2466071) B2466071
theorem B9377309 : Blo 730325 9377309 := bstep (se 3 (by rfl) ⟨1758245, by rfl⟩ : syracuseStep 9377309 = 3516491) B3516491
theorem B1644065 : Blo 730325 1644065 := bstep (se 2 (by rfl) ⟨616524, by rfl⟩ : syracuseStep 1644065 = 1233049) B1233049
theorem B4462141 : Blo 730325 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B3708503 : Blo 730325 3708503 := bstep (se 1 (by rfl) ⟨2781377, by rfl⟩ : syracuseStep 3708503 = 5562755) B5562755
theorem B16946995 : Blo 730325 16946995 := bstep (se 1 (by rfl) ⟨12710246, by rfl⟩ : syracuseStep 16946995 = 25420493) B25420493
theorem B1644407 : Blo 730325 1644407 := bstep (se 1 (by rfl) ⟨1233305, by rfl⟩ : syracuseStep 1644407 = 2466611) B2466611
theorem B825223 : Blo 730325 825223 := bstep (se 1 (by rfl) ⟨618917, by rfl⟩ : syracuseStep 825223 = 1237835) B1237835
theorem B1185835 : Blo 730325 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B1644587 : Blo 730325 1644587 := bstep (se 1 (by rfl) ⟨1233440, by rfl⟩ : syracuseStep 1644587 = 2466881) B2466881
theorem B825403 : Blo 730325 825403 := bstep (se 1 (by rfl) ⟨619052, by rfl⟩ : syracuseStep 825403 = 1238105) B1238105
theorem B3708989 : Blo 730325 3708989 := bstep (se 3 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 3708989 = 1390871) B1390871
theorem B1185977 : Blo 730325 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B1644947 : Blo 730325 1644947 := bstep (se 1 (by rfl) ⟨1233710, by rfl⟩ : syracuseStep 1644947 = 2467421) B2467421
theorem B1645001 : Blo 730325 1645001 := bstep (se 2 (by rfl) ⟨616875, by rfl⟩ : syracuseStep 1645001 = 1233751) B1233751
theorem B825871 : Blo 730325 825871 := bstep (se 1 (by rfl) ⟨619403, by rfl⟩ : syracuseStep 825871 = 1238807) B1238807
theorem B5347883 : Blo 730325 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B989815 : Blo 730325 989815 := bstep (se 1 (by rfl) ⟨742361, by rfl⟩ : syracuseStep 989815 = 1484723) B1484723
theorem B2005651 : Blo 730325 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B11246273 : Blo 730325 11246273 := bstep (se 2 (by rfl) ⟨4217352, by rfl⟩ : syracuseStep 11246273 = 8434705) B8434705
theorem B1317647 : Blo 730325 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B4168583 : Blo 730325 4168583 := bstep (se 1 (by rfl) ⟨3126437, by rfl⟩ : syracuseStep 4168583 = 6252875) B6252875
theorem B14851133 : Blo 730325 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B9378949 : Blo 730325 9378949 := bstep (se 4 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 9378949 = 1758553) B1758553
theorem B1645703 : Blo 730325 1645703 := bstep (se 1 (by rfl) ⟨1234277, by rfl⟩ : syracuseStep 1645703 = 2468555) B2468555
theorem B1645883 : Blo 730325 1645883 := bstep (se 1 (by rfl) ⟨1234412, by rfl⟩ : syracuseStep 1645883 = 2468825) B2468825
theorem B1646009 : Blo 730325 1646009 := bstep (se 2 (by rfl) ⟨617253, by rfl⟩ : syracuseStep 1646009 = 1234507) B1234507
theorem B3513917 : Blo 730325 3513917 := bstep (se 3 (by rfl) ⟨658859, by rfl⟩ : syracuseStep 3513917 = 1317719) B1317719
theorem B1646351 : Blo 730325 1646351 := bstep (se 1 (by rfl) ⟨1234763, by rfl⟩ : syracuseStep 1646351 = 2469527) B2469527
theorem B1646369 : Blo 730325 1646369 := bstep (se 2 (by rfl) ⟨617388, by rfl⟩ : syracuseStep 1646369 = 1234777) B1234777
theorem B3710771 : Blo 730325 3710771 := bstep (se 1 (by rfl) ⟨2783078, by rfl⟩ : syracuseStep 3710771 = 5566157) B5566157
theorem B4169789 : Blo 730325 4169789 := bstep (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) B1563671
theorem B1646711 : Blo 730325 1646711 := bstep (se 1 (by rfl) ⟨1235033, by rfl⟩ : syracuseStep 1646711 = 2470067) B2470067
theorem B3711095 : Blo 730325 3711095 := bstep (se 1 (by rfl) ⟨2783321, by rfl⟩ : syracuseStep 3711095 = 5566643) B5566643
theorem B1482953 : Blo 730325 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B1876267 : Blo 730325 1876267 := bstep (se 1 (by rfl) ⟨1407200, by rfl⟩ : syracuseStep 1876267 = 2814401) B2814401
theorem B1646891 : Blo 730325 1646891 := bstep (se 1 (by rfl) ⟨1235168, by rfl⟩ : syracuseStep 1646891 = 2470337) B2470337
theorem B7119251 : Blo 730325 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B2466233 : Blo 730325 2466233 := bstep (se 2 (by rfl) ⟨924837, by rfl⟩ : syracuseStep 2466233 = 1849675) B1849675
theorem B6267395 : Blo 730325 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B1974827 : Blo 730325 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B1647251 : Blo 730325 1647251 := bstep (se 1 (by rfl) ⟨1235438, by rfl⟩ : syracuseStep 1647251 = 2470877) B2470877
theorem B1647305 : Blo 730325 1647305 := bstep (se 2 (by rfl) ⟨617739, by rfl⟩ : syracuseStep 1647305 = 1235479) B1235479
theorem B1319723 : Blo 730325 1319723 := bstep (se 1 (by rfl) ⟨989792, by rfl⟩ : syracuseStep 1319723 = 1979585) B1979585
theorem B926635 : Blo 730325 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B2466827 : Blo 730325 2466827 := bstep (se 1 (by rfl) ⟨1850120, by rfl⟩ : syracuseStep 2466827 = 3700241) B3700241
theorem B1319969 : Blo 730325 1319969 := bstep (se 2 (by rfl) ⟨494988, by rfl⟩ : syracuseStep 1319969 = 989977) B989977
theorem B3712067 : Blo 730325 3712067 := bstep (se 1 (by rfl) ⟨2784050, by rfl⟩ : syracuseStep 3712067 = 5568101) B5568101
theorem B2466935 : Blo 730325 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B730375 : Blo 730325 730375 := bstep (se 1 (by rfl) ⟨547781, by rfl⟩ : syracuseStep 730375 = 1095563) B1095563
theorem B730383 : Blo 730325 730383 := bstep (se 1 (by rfl) ⟨547787, by rfl⟩ : syracuseStep 730383 = 1095575) B1095575
theorem B730427 : Blo 730325 730427 := bstep (se 1 (by rfl) ⟨547820, by rfl⟩ : syracuseStep 730427 = 1095641) B1095641
theorem B730503 : Blo 730325 730503 := bstep (se 1 (by rfl) ⟨547877, by rfl⟩ : syracuseStep 730503 = 1095755) B1095755
theorem B1648007 : Blo 730325 1648007 := bstep (se 1 (by rfl) ⟨1236005, by rfl⟩ : syracuseStep 1648007 = 2472011) B2472011
theorem B3712391 : Blo 730325 3712391 := bstep (se 1 (by rfl) ⟨2784293, by rfl⟩ : syracuseStep 3712391 = 5568587) B5568587
theorem B730511 : Blo 730325 730511 := bstep (se 1 (by rfl) ⟨547883, by rfl⟩ : syracuseStep 730511 = 1095767) B1095767
theorem B730555 : Blo 730325 730555 := bstep (se 1 (by rfl) ⟨547916, by rfl⟩ : syracuseStep 730555 = 1095833) B1095833
theorem B730631 : Blo 730325 730631 := bstep (se 1 (by rfl) ⟨547973, by rfl⟩ : syracuseStep 730631 = 1095947) B1095947
theorem B730639 : Blo 730325 730639 := bstep (se 1 (by rfl) ⟨547979, by rfl⟩ : syracuseStep 730639 = 1095959) B1095959
theorem B730683 : Blo 730325 730683 := bstep (se 1 (by rfl) ⟨548012, by rfl⟩ : syracuseStep 730683 = 1096025) B1096025
theorem B1648187 : Blo 730325 1648187 := bstep (se 1 (by rfl) ⟨1236140, by rfl⟩ : syracuseStep 1648187 = 2472281) B2472281
theorem B730759 : Blo 730325 730759 := bstep (se 1 (by rfl) ⟨548069, by rfl⟩ : syracuseStep 730759 = 1096139) B1096139
theorem B730767 : Blo 730325 730767 := bstep (se 1 (by rfl) ⟨548075, by rfl⟩ : syracuseStep 730767 = 1096151) B1096151
theorem B1648313 : Blo 730325 1648313 := bstep (se 2 (by rfl) ⟨618117, by rfl⟩ : syracuseStep 1648313 = 1236235) B1236235
theorem B730811 : Blo 730325 730811 := bstep (se 1 (by rfl) ⟨548108, by rfl⟩ : syracuseStep 730811 = 1096217) B1096217
theorem B6334145 : Blo 730325 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B2467529 : Blo 730325 2467529 := bstep (se 2 (by rfl) ⟨925323, by rfl⟩ : syracuseStep 2467529 = 1850647) B1850647
theorem B730887 : Blo 730325 730887 := bstep (se 1 (by rfl) ⟨548165, by rfl⟩ : syracuseStep 730887 = 1096331) B1096331
theorem B730895 : Blo 730325 730895 := bstep (se 1 (by rfl) ⟨548171, by rfl⟩ : syracuseStep 730895 = 1096343) B1096343
theorem B730939 : Blo 730325 730939 := bstep (se 1 (by rfl) ⟨548204, by rfl⟩ : syracuseStep 730939 = 1096409) B1096409
theorem B927607 : Blo 730325 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B731015 : Blo 730325 731015 := bstep (se 1 (by rfl) ⟨548261, by rfl⟩ : syracuseStep 731015 = 1096523) B1096523
theorem B731023 : Blo 730325 731023 := bstep (se 1 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 731023 = 1096535) B1096535
theorem B731067 : Blo 730325 731067 := bstep (se 1 (by rfl) ⟨548300, by rfl⟩ : syracuseStep 731067 = 1096601) B1096601
theorem B12691403 : Blo 730325 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B731143 : Blo 730325 731143 := bstep (se 1 (by rfl) ⟨548357, by rfl⟩ : syracuseStep 731143 = 1096715) B1096715
theorem B731151 : Blo 730325 731151 := bstep (se 1 (by rfl) ⟨548363, by rfl⟩ : syracuseStep 731151 = 1096727) B1096727
theorem B1648655 : Blo 730325 1648655 := bstep (se 1 (by rfl) ⟨1236491, by rfl⟩ : syracuseStep 1648655 = 2472983) B2472983
theorem B1648673 : Blo 730325 1648673 := bstep (se 2 (by rfl) ⟨618252, by rfl⟩ : syracuseStep 1648673 = 1236505) B1236505
theorem B731195 : Blo 730325 731195 := bstep (se 1 (by rfl) ⟨548396, by rfl⟩ : syracuseStep 731195 = 1096793) B1096793
theorem B731271 : Blo 730325 731271 := bstep (se 1 (by rfl) ⟨548453, by rfl⟩ : syracuseStep 731271 = 1096907) B1096907
theorem B731279 : Blo 730325 731279 := bstep (se 1 (by rfl) ⟨548459, by rfl⟩ : syracuseStep 731279 = 1096919) B1096919
theorem B731323 : Blo 730325 731323 := bstep (se 1 (by rfl) ⟨548492, by rfl⟩ : syracuseStep 731323 = 1096985) B1096985
theorem B927931 : Blo 730325 927931 := bstep (se 1 (by rfl) ⟨695948, by rfl⟩ : syracuseStep 927931 = 1391897) B1391897
theorem B4237541 : Blo 730325 4237541 := bstep (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) B794539
theorem B731399 : Blo 730325 731399 := bstep (se 1 (by rfl) ⟨548549, by rfl⟩ : syracuseStep 731399 = 1097099) B1097099
theorem B731407 : Blo 730325 731407 := bstep (se 1 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 731407 = 1097111) B1097111
theorem B3123515 : Blo 730325 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B731451 : Blo 730325 731451 := bstep (se 1 (by rfl) ⟨548588, by rfl⟩ : syracuseStep 731451 = 1097177) B1097177
theorem B1649015 : Blo 730325 1649015 := bstep (se 1 (by rfl) ⟨1236761, by rfl⟩ : syracuseStep 1649015 = 2473523) B2473523
theorem B2468231 : Blo 730325 2468231 := bstep (se 1 (by rfl) ⟨1851173, by rfl⟩ : syracuseStep 2468231 = 3702347) B3702347
theorem B731527 : Blo 730325 731527 := bstep (se 1 (by rfl) ⟨548645, by rfl⟩ : syracuseStep 731527 = 1097291) B1097291
theorem B731535 : Blo 730325 731535 := bstep (se 1 (by rfl) ⟨548651, by rfl⟩ : syracuseStep 731535 = 1097303) B1097303
theorem B1976729 : Blo 730325 1976729 := bstep (se 2 (by rfl) ⟨741273, by rfl⟩ : syracuseStep 1976729 = 1482547) B1482547
theorem B1059257 : Blo 730325 1059257 := bstep (se 2 (by rfl) ⟨397221, by rfl⟩ : syracuseStep 1059257 = 794443) B794443
theorem B731579 : Blo 730325 731579 := bstep (se 1 (by rfl) ⟨548684, by rfl⟩ : syracuseStep 731579 = 1097369) B1097369
theorem B1386953 : Blo 730325 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B731655 : Blo 730325 731655 := bstep (se 1 (by rfl) ⟨548741, by rfl⟩ : syracuseStep 731655 = 1097483) B1097483
theorem B731663 : Blo 730325 731663 := bstep (se 1 (by rfl) ⟨548747, by rfl⟩ : syracuseStep 731663 = 1097495) B1097495
theorem B1976861 : Blo 730325 1976861 := bstep (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) B741323
theorem B3123755 : Blo 730325 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B1649195 : Blo 730325 1649195 := bstep (se 1 (by rfl) ⟨1236896, by rfl⟩ : syracuseStep 1649195 = 2473793) B2473793
theorem B731707 : Blo 730325 731707 := bstep (se 1 (by rfl) ⟨548780, by rfl⟩ : syracuseStep 731707 = 1097561) B1097561
theorem B731783 : Blo 730325 731783 := bstep (se 1 (by rfl) ⟨548837, by rfl⟩ : syracuseStep 731783 = 1097675) B1097675
theorem B731791 : Blo 730325 731791 := bstep (se 1 (by rfl) ⟨548843, by rfl⟩ : syracuseStep 731791 = 1097687) B1097687
theorem B731835 : Blo 730325 731835 := bstep (se 1 (by rfl) ⟨548876, by rfl⟩ : syracuseStep 731835 = 1097753) B1097753
theorem B2468609 : Blo 730325 2468609 := bstep (se 2 (by rfl) ⟨925728, by rfl⟩ : syracuseStep 2468609 = 1851457) B1851457
theorem B19999493 : Blo 730325 19999493 := bstep (se 4 (by rfl) ⟨1874952, by rfl⟩ : syracuseStep 19999493 = 3749905) B3749905
theorem B731911 : Blo 730325 731911 := bstep (se 1 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 731911 = 1097867) B1097867
theorem B25340687 : Blo 730325 25340687 := bstep (se 1 (by rfl) ⟨19005515, by rfl⟩ : syracuseStep 25340687 = 38011031) B38011031
theorem B731919 : Blo 730325 731919 := bstep (se 1 (by rfl) ⟨548939, by rfl⟩ : syracuseStep 731919 = 1097879) B1097879
theorem B1321771 : Blo 730325 1321771 := bstep (se 1 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 1321771 = 1982657) B1982657
theorem B731963 : Blo 730325 731963 := bstep (se 1 (by rfl) ⟨548972, by rfl⟩ : syracuseStep 731963 = 1097945) B1097945
theorem B7023449 : Blo 730325 7023449 := bstep (se 2 (by rfl) ⟨2633793, by rfl⟩ : syracuseStep 7023449 = 5267587) B5267587
theorem B732039 : Blo 730325 732039 := bstep (se 1 (by rfl) ⟨549029, by rfl⟩ : syracuseStep 732039 = 1098059) B1098059
theorem B732047 : Blo 730325 732047 := bstep (se 1 (by rfl) ⟨549035, by rfl⟩ : syracuseStep 732047 = 1098071) B1098071
theorem B3124115 : Blo 730325 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B1649555 : Blo 730325 1649555 := bstep (se 1 (by rfl) ⟨1237166, by rfl⟩ : syracuseStep 1649555 = 2474333) B2474333
theorem B732091 : Blo 730325 732091 := bstep (se 1 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 732091 = 1098137) B1098137
theorem B1649609 : Blo 730325 1649609 := bstep (se 2 (by rfl) ⟨618603, by rfl⟩ : syracuseStep 1649609 = 1237207) B1237207
theorem B732167 : Blo 730325 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B732175 : Blo 730325 732175 := bstep (se 1 (by rfl) ⟨549131, by rfl⟩ : syracuseStep 732175 = 1098263) B1098263
theorem B732219 : Blo 730325 732219 := bstep (se 1 (by rfl) ⟨549164, by rfl⟩ : syracuseStep 732219 = 1098329) B1098329
theorem B16067645 : Blo 730325 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B732295 : Blo 730325 732295 := bstep (se 1 (by rfl) ⟨549221, by rfl⟩ : syracuseStep 732295 = 1098443) B1098443
theorem B928903 : Blo 730325 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B732303 : Blo 730325 732303 := bstep (se 1 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 732303 = 1098455) B1098455
theorem B1387667 : Blo 730325 1387667 := bstep (se 1 (by rfl) ⟨1040750, by rfl⟩ : syracuseStep 1387667 = 2081501) B2081501
theorem B1387705 : Blo 730325 1387705 := bstep (se 2 (by rfl) ⟨520389, by rfl⟩ : syracuseStep 1387705 = 1040779) B1040779
theorem B732347 : Blo 730325 732347 := bstep (se 1 (by rfl) ⟨549260, by rfl⟩ : syracuseStep 732347 = 1098521) B1098521
theorem B732423 : Blo 730325 732423 := bstep (se 1 (by rfl) ⟨549317, by rfl⟩ : syracuseStep 732423 = 1098635) B1098635
theorem B732431 : Blo 730325 732431 := bstep (se 1 (by rfl) ⟨549323, by rfl⟩ : syracuseStep 732431 = 1098647) B1098647
theorem B15871265 : Blo 730325 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B30125357 : Blo 730325 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B732475 : Blo 730325 732475 := bstep (se 1 (by rfl) ⟨549356, by rfl⟩ : syracuseStep 732475 = 1098713) B1098713
theorem B732551 : Blo 730325 732551 := bstep (se 1 (by rfl) ⟨549413, by rfl⟩ : syracuseStep 732551 = 1098827) B1098827
theorem B732559 : Blo 730325 732559 := bstep (se 1 (by rfl) ⟨549419, by rfl⟩ : syracuseStep 732559 = 1098839) B1098839
theorem B732603 : Blo 730325 732603 := bstep (se 1 (by rfl) ⟨549452, by rfl⟩ : syracuseStep 732603 = 1098905) B1098905
theorem B732679 : Blo 730325 732679 := bstep (se 1 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 732679 = 1099019) B1099019
theorem B732687 : Blo 730325 732687 := bstep (se 1 (by rfl) ⟨549515, by rfl⟩ : syracuseStep 732687 = 1099031) B1099031
theorem B2469419 : Blo 730325 2469419 := bstep (se 1 (by rfl) ⟨1852064, by rfl⟩ : syracuseStep 2469419 = 3704129) B3704129
theorem B929323 : Blo 730325 929323 := bstep (se 1 (by rfl) ⟨696992, by rfl⟩ : syracuseStep 929323 = 1393985) B1393985
theorem B732731 : Blo 730325 732731 := bstep (se 1 (by rfl) ⟨549548, by rfl⟩ : syracuseStep 732731 = 1099097) B1099097
theorem B732807 : Blo 730325 732807 := bstep (se 1 (by rfl) ⟨549605, by rfl⟩ : syracuseStep 732807 = 1099211) B1099211
theorem B1650311 : Blo 730325 1650311 := bstep (se 1 (by rfl) ⟨1237733, by rfl⟩ : syracuseStep 1650311 = 2475467) B2475467
theorem B732815 : Blo 730325 732815 := bstep (se 1 (by rfl) ⟨549611, by rfl⟩ : syracuseStep 732815 = 1099223) B1099223
theorem B732859 : Blo 730325 732859 := bstep (se 1 (by rfl) ⟨549644, by rfl⟩ : syracuseStep 732859 = 1099289) B1099289
theorem B732935 : Blo 730325 732935 := bstep (se 1 (by rfl) ⟨549701, by rfl⟩ : syracuseStep 732935 = 1099403) B1099403
theorem B732943 : Blo 730325 732943 := bstep (se 1 (by rfl) ⟨549707, by rfl⟩ : syracuseStep 732943 = 1099415) B1099415
theorem B1879841 : Blo 730325 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B5353253 : Blo 730325 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B732987 : Blo 730325 732987 := bstep (se 1 (by rfl) ⟨549740, by rfl⟩ : syracuseStep 732987 = 1099481) B1099481
theorem B1650491 : Blo 730325 1650491 := bstep (se 1 (by rfl) ⟨1237868, by rfl⟩ : syracuseStep 1650491 = 2475737) B2475737
theorem B15249221 : Blo 730325 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B733063 : Blo 730325 733063 := bstep (se 1 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 733063 = 1099595) B1099595
theorem B733071 : Blo 730325 733071 := bstep (se 1 (by rfl) ⟨549803, by rfl⟩ : syracuseStep 733071 = 1099607) B1099607
theorem B1879955 : Blo 730325 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B1650617 : Blo 730325 1650617 := bstep (se 2 (by rfl) ⟨618981, by rfl⟩ : syracuseStep 1650617 = 1237963) B1237963
theorem B733115 : Blo 730325 733115 := bstep (se 1 (by rfl) ⟨549836, by rfl⟩ : syracuseStep 733115 = 1099673) B1099673
theorem B733191 : Blo 730325 733191 := bstep (se 1 (by rfl) ⟨549893, by rfl⟩ : syracuseStep 733191 = 1099787) B1099787
theorem B733199 : Blo 730325 733199 := bstep (se 1 (by rfl) ⟨549899, by rfl⟩ : syracuseStep 733199 = 1099799) B1099799
theorem B733243 : Blo 730325 733243 := bstep (se 1 (by rfl) ⟨549932, by rfl⟩ : syracuseStep 733243 = 1099865) B1099865
theorem B733319 : Blo 730325 733319 := bstep (se 1 (by rfl) ⟨549989, by rfl⟩ : syracuseStep 733319 = 1099979) B1099979
theorem B733327 : Blo 730325 733327 := bstep (se 1 (by rfl) ⟨549995, by rfl⟩ : syracuseStep 733327 = 1099991) B1099991
theorem B1323155 : Blo 730325 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B733371 : Blo 730325 733371 := bstep (se 1 (by rfl) ⟨550028, by rfl⟩ : syracuseStep 733371 = 1100057) B1100057
theorem B733447 : Blo 730325 733447 := bstep (se 1 (by rfl) ⟨550085, by rfl⟩ : syracuseStep 733447 = 1100171) B1100171
theorem B733455 : Blo 730325 733455 := bstep (se 1 (by rfl) ⟨550091, by rfl⟩ : syracuseStep 733455 = 1100183) B1100183
theorem B1650959 : Blo 730325 1650959 := bstep (se 1 (by rfl) ⟨1238219, by rfl⟩ : syracuseStep 1650959 = 2476439) B2476439
theorem B7909649 : Blo 730325 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B1650977 : Blo 730325 1650977 := bstep (se 2 (by rfl) ⟨619116, by rfl⟩ : syracuseStep 1650977 = 1238233) B1238233
theorem B3092795 : Blo 730325 3092795 := bstep (se 1 (by rfl) ⟨2319596, by rfl⟩ : syracuseStep 3092795 = 4639193) B4639193
theorem B733499 : Blo 730325 733499 := bstep (se 1 (by rfl) ⟨550124, by rfl⟩ : syracuseStep 733499 = 1100249) B1100249
theorem B733575 : Blo 730325 733575 := bstep (se 1 (by rfl) ⟨550181, by rfl⟩ : syracuseStep 733575 = 1100363) B1100363
theorem B733583 : Blo 730325 733583 := bstep (se 1 (by rfl) ⟨550187, by rfl⟩ : syracuseStep 733583 = 1100375) B1100375
theorem B733627 : Blo 730325 733627 := bstep (se 1 (by rfl) ⟨550220, by rfl⟩ : syracuseStep 733627 = 1100441) B1100441
theorem B733703 : Blo 730325 733703 := bstep (se 1 (by rfl) ⟨550277, by rfl⟩ : syracuseStep 733703 = 1100555) B1100555
theorem B733711 : Blo 730325 733711 := bstep (se 1 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 733711 = 1100567) B1100567
theorem B733755 : Blo 730325 733755 := bstep (se 1 (by rfl) ⟨550316, by rfl⟩ : syracuseStep 733755 = 1100633) B1100633
theorem B1487479 : Blo 730325 1487479 := bstep (se 1 (by rfl) ⟨1115609, by rfl⟩ : syracuseStep 1487479 = 2231219) B2231219
theorem B1651319 : Blo 730325 1651319 := bstep (se 1 (by rfl) ⟨1238489, by rfl⟩ : syracuseStep 1651319 = 2476979) B2476979
theorem B733831 : Blo 730325 733831 := bstep (se 1 (by rfl) ⟨550373, by rfl⟩ : syracuseStep 733831 = 1100747) B1100747
theorem B733839 : Blo 730325 733839 := bstep (se 1 (by rfl) ⟨550379, by rfl⟩ : syracuseStep 733839 = 1100759) B1100759
theorem B733883 : Blo 730325 733883 := bstep (se 1 (by rfl) ⟨550412, by rfl⟩ : syracuseStep 733883 = 1100825) B1100825
theorem B733959 : Blo 730325 733959 := bstep (se 1 (by rfl) ⟨550469, by rfl⟩ : syracuseStep 733959 = 1100939) B1100939
theorem B733967 : Blo 730325 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B1651499 : Blo 730325 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B2470715 : Blo 730325 2470715 := bstep (se 1 (by rfl) ⟨1853036, by rfl⟩ : syracuseStep 2470715 = 3706073) B3706073
theorem B734011 : Blo 730325 734011 := bstep (se 1 (by rfl) ⟨550508, by rfl⟩ : syracuseStep 734011 = 1101017) B1101017
theorem B3715955 : Blo 730325 3715955 := bstep (se 1 (by rfl) ⟨2786966, by rfl⟩ : syracuseStep 3715955 = 5573933) B5573933
theorem B734087 : Blo 730325 734087 := bstep (se 1 (by rfl) ⟨550565, by rfl⟩ : syracuseStep 734087 = 1101131) B1101131
theorem B734095 : Blo 730325 734095 := bstep (se 1 (by rfl) ⟨550571, by rfl⟩ : syracuseStep 734095 = 1101143) B1101143
theorem B734139 : Blo 730325 734139 := bstep (se 1 (by rfl) ⟨550604, by rfl⟩ : syracuseStep 734139 = 1101209) B1101209
theorem B734215 : Blo 730325 734215 := bstep (se 1 (by rfl) ⟨550661, by rfl⟩ : syracuseStep 734215 = 1101323) B1101323
theorem B734223 : Blo 730325 734223 := bstep (se 1 (by rfl) ⟨550667, by rfl⟩ : syracuseStep 734223 = 1101335) B1101335
theorem B1389611 : Blo 730325 1389611 := bstep (se 1 (by rfl) ⟨1042208, by rfl⟩ : syracuseStep 1389611 = 2084417) B2084417
theorem B734267 : Blo 730325 734267 := bstep (se 1 (by rfl) ⟨550700, by rfl⟩ : syracuseStep 734267 = 1101401) B1101401
theorem B1651859 : Blo 730325 1651859 := bstep (se 1 (by rfl) ⟨1238894, by rfl⟩ : syracuseStep 1651859 = 2477789) B2477789
theorem B1651913 : Blo 730325 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B1488143 : Blo 730325 1488143 := bstep (se 1 (by rfl) ⟨1116107, by rfl⟩ : syracuseStep 1488143 = 2232215) B2232215
theorem B2471201 : Blo 730325 2471201 := bstep (se 2 (by rfl) ⟨926700, by rfl⟩ : syracuseStep 2471201 = 1853401) B1853401
theorem B3716441 : Blo 730325 3716441 := bstep (se 2 (by rfl) ⟨1393665, by rfl⟩ : syracuseStep 3716441 = 2787331) B2787331
theorem B1848865 : Blo 730325 1848865 := bstep (se 2 (by rfl) ⟨693324, by rfl⟩ : syracuseStep 1848865 = 1386649) B1386649
theorem B6665771 : Blo 730325 6665771 := bstep (se 1 (by rfl) ⟨4999328, by rfl⟩ : syracuseStep 6665771 = 9998657) B9998657
theorem B2635325 : Blo 730325 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B1095497 : Blo 730325 1095497 := bstep (se 2 (by rfl) ⟨410811, by rfl⟩ : syracuseStep 1095497 = 821623) B821623
theorem B2471795 : Blo 730325 2471795 := bstep (se 1 (by rfl) ⟨1853846, by rfl⟩ : syracuseStep 2471795 = 3707693) B3707693
theorem B1095611 : Blo 730325 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B1390537 : Blo 730325 1390537 := bstep (se 2 (by rfl) ⟨521451, by rfl⟩ : syracuseStep 1390537 = 1042903) B1042903
theorem B1095671 : Blo 730325 1095671 := bstep (se 1 (by rfl) ⟨821753, by rfl⟩ : syracuseStep 1095671 = 1643507) B1643507
theorem B86751245 : Blo 730325 86751245 := bstep (se 3 (by rfl) ⟨16265858, by rfl⟩ : syracuseStep 86751245 = 32531717) B32531717
theorem B1095695 : Blo 730325 1095695 := bstep (se 1 (by rfl) ⟨821771, by rfl⟩ : syracuseStep 1095695 = 1643543) B1643543
theorem B1095737 : Blo 730325 1095737 := bstep (se 2 (by rfl) ⟨410901, by rfl⟩ : syracuseStep 1095737 = 821803) B821803
theorem B1849463 : Blo 730325 1849463 := bstep (se 1 (by rfl) ⟨1387097, by rfl⟩ : syracuseStep 1849463 = 2774195) B2774195
theorem B1095815 : Blo 730325 1095815 := bstep (se 1 (by rfl) ⟨821861, by rfl⟩ : syracuseStep 1095815 = 1643723) B1643723
theorem B1095851 : Blo 730325 1095851 := bstep (se 1 (by rfl) ⟨821888, by rfl⟩ : syracuseStep 1095851 = 1643777) B1643777
theorem B1095881 : Blo 730325 1095881 := bstep (se 2 (by rfl) ⟨410955, by rfl⟩ : syracuseStep 1095881 = 821911) B821911
theorem B2111777 : Blo 730325 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B1095995 : Blo 730325 1095995 := bstep (se 1 (by rfl) ⟨821996, by rfl⟩ : syracuseStep 1095995 = 1643993) B1643993
theorem B1096055 : Blo 730325 1096055 := bstep (se 1 (by rfl) ⟨822041, by rfl⟩ : syracuseStep 1096055 = 1644083) B1644083
theorem B1096079 : Blo 730325 1096079 := bstep (se 1 (by rfl) ⟨822059, by rfl⟩ : syracuseStep 1096079 = 1644119) B1644119
theorem B1096121 : Blo 730325 1096121 := bstep (se 2 (by rfl) ⟨411045, by rfl⟩ : syracuseStep 1096121 = 822091) B822091
theorem B1096199 : Blo 730325 1096199 := bstep (se 1 (by rfl) ⟨822149, by rfl⟩ : syracuseStep 1096199 = 1644299) B1644299
theorem B1096235 : Blo 730325 1096235 := bstep (se 1 (by rfl) ⟨822176, by rfl⟩ : syracuseStep 1096235 = 1644353) B1644353
theorem B1096265 : Blo 730325 1096265 := bstep (se 2 (by rfl) ⟨411099, by rfl⟩ : syracuseStep 1096265 = 822199) B822199
theorem B1391251 : Blo 730325 1391251 := bstep (se 1 (by rfl) ⟨1043438, by rfl⟩ : syracuseStep 1391251 = 2086877) B2086877
theorem B1096379 : Blo 730325 1096379 := bstep (se 1 (by rfl) ⟨822284, by rfl⟩ : syracuseStep 1096379 = 1644569) B1644569
theorem B1096439 : Blo 730325 1096439 := bstep (se 1 (by rfl) ⟨822329, by rfl⟩ : syracuseStep 1096439 = 1644659) B1644659
theorem B1096463 : Blo 730325 1096463 := bstep (se 1 (by rfl) ⟨822347, by rfl⟩ : syracuseStep 1096463 = 1644695) B1644695
theorem B1981217 : Blo 730325 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B1096505 : Blo 730325 1096505 := bstep (se 2 (by rfl) ⟨411189, by rfl⟩ : syracuseStep 1096505 = 822379) B822379
theorem B1096583 : Blo 730325 1096583 := bstep (se 1 (by rfl) ⟨822437, by rfl⟩ : syracuseStep 1096583 = 1644875) B1644875
theorem B1096619 : Blo 730325 1096619 := bstep (se 1 (by rfl) ⟨822464, by rfl⟩ : syracuseStep 1096619 = 1644929) B1644929
theorem B2341817 : Blo 730325 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B1096649 : Blo 730325 1096649 := bstep (se 2 (by rfl) ⟨411243, by rfl⟩ : syracuseStep 1096649 = 822487) B822487
theorem B2964433 : Blo 730325 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B1096763 : Blo 730325 1096763 := bstep (se 1 (by rfl) ⟨822572, by rfl⟩ : syracuseStep 1096763 = 1645145) B1645145
theorem B1096823 : Blo 730325 1096823 := bstep (se 1 (by rfl) ⟨822617, by rfl⟩ : syracuseStep 1096823 = 1645235) B1645235
theorem B1096847 : Blo 730325 1096847 := bstep (se 1 (by rfl) ⟨822635, by rfl⟩ : syracuseStep 1096847 = 1645271) B1645271
theorem B1096889 : Blo 730325 1096889 := bstep (se 2 (by rfl) ⟨411333, by rfl⟩ : syracuseStep 1096889 = 822667) B822667
theorem B1096967 : Blo 730325 1096967 := bstep (se 1 (by rfl) ⟨822725, by rfl⟩ : syracuseStep 1096967 = 1645451) B1645451
theorem B2080043 : Blo 730325 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B1097003 : Blo 730325 1097003 := bstep (se 1 (by rfl) ⟨822752, by rfl⟩ : syracuseStep 1097003 = 1645505) B1645505
theorem B1097033 : Blo 730325 1097033 := bstep (se 2 (by rfl) ⟨411387, by rfl⟩ : syracuseStep 1097033 = 822775) B822775
theorem B1850759 : Blo 730325 1850759 := bstep (se 1 (by rfl) ⟨1388069, by rfl⟩ : syracuseStep 1850759 = 2776139) B2776139
theorem B6667667 : Blo 730325 6667667 := bstep (se 1 (by rfl) ⟨5000750, by rfl⟩ : syracuseStep 6667667 = 10001501) B10001501
theorem B1850809 : Blo 730325 1850809 := bstep (se 2 (by rfl) ⟨694053, by rfl⟩ : syracuseStep 1850809 = 1388107) B1388107
theorem B1097147 : Blo 730325 1097147 := bstep (se 1 (by rfl) ⟨822860, by rfl⟩ : syracuseStep 1097147 = 1645721) B1645721
theorem B1097207 : Blo 730325 1097207 := bstep (se 1 (by rfl) ⟨822905, by rfl⟩ : syracuseStep 1097207 = 1645811) B1645811
theorem B1097231 : Blo 730325 1097231 := bstep (se 1 (by rfl) ⟨822923, by rfl⟩ : syracuseStep 1097231 = 1645847) B1645847
theorem B1097273 : Blo 730325 1097273 := bstep (se 2 (by rfl) ⟨411477, by rfl⟩ : syracuseStep 1097273 = 822955) B822955
theorem B1097351 : Blo 730325 1097351 := bstep (se 1 (by rfl) ⟨823013, by rfl⟩ : syracuseStep 1097351 = 1646027) B1646027
theorem B1097387 : Blo 730325 1097387 := bstep (se 1 (by rfl) ⟨823040, by rfl⟩ : syracuseStep 1097387 = 1646081) B1646081
theorem B1097417 : Blo 730325 1097417 := bstep (se 2 (by rfl) ⟨411531, by rfl⟩ : syracuseStep 1097417 = 823063) B823063
theorem B1392329 : Blo 730325 1392329 := bstep (se 2 (by rfl) ⟨522123, by rfl⟩ : syracuseStep 1392329 = 1044247) B1044247
theorem B1097531 : Blo 730325 1097531 := bstep (se 1 (by rfl) ⟨823148, by rfl⟩ : syracuseStep 1097531 = 1646297) B1646297
theorem B1097591 : Blo 730325 1097591 := bstep (se 1 (by rfl) ⟨823193, by rfl⟩ : syracuseStep 1097591 = 1646387) B1646387
theorem B1097615 : Blo 730325 1097615 := bstep (se 1 (by rfl) ⟨823211, by rfl⟩ : syracuseStep 1097615 = 1646423) B1646423
theorem B1097657 : Blo 730325 1097657 := bstep (se 2 (by rfl) ⟨411621, by rfl⟩ : syracuseStep 1097657 = 823243) B823243
theorem B1097735 : Blo 730325 1097735 := bstep (se 1 (by rfl) ⟨823301, by rfl⟩ : syracuseStep 1097735 = 1646603) B1646603
theorem B1851407 : Blo 730325 1851407 := bstep (se 1 (by rfl) ⟨1388555, by rfl⟩ : syracuseStep 1851407 = 2777111) B2777111
theorem B1097771 : Blo 730325 1097771 := bstep (se 1 (by rfl) ⟨823328, by rfl⟩ : syracuseStep 1097771 = 1646657) B1646657
theorem B2080829 : Blo 730325 2080829 := bstep (se 3 (by rfl) ⟨390155, by rfl⟩ : syracuseStep 2080829 = 780311) B780311
theorem B1097801 : Blo 730325 1097801 := bstep (se 2 (by rfl) ⟨411675, by rfl⟩ : syracuseStep 1097801 = 823351) B823351
theorem B1097915 : Blo 730325 1097915 := bstep (se 1 (by rfl) ⟨823436, by rfl⟩ : syracuseStep 1097915 = 1646873) B1646873
theorem B3522797 : Blo 730325 3522797 := bstep (se 3 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 3522797 = 1321049) B1321049
theorem B4702445 : Blo 730325 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B1097975 : Blo 730325 1097975 := bstep (se 1 (by rfl) ⟨823481, by rfl⟩ : syracuseStep 1097975 = 1646963) B1646963
theorem B1097999 : Blo 730325 1097999 := bstep (se 1 (by rfl) ⟨823499, by rfl⟩ : syracuseStep 1097999 = 1646999) B1646999
theorem B1098041 : Blo 730325 1098041 := bstep (se 2 (by rfl) ⟨411765, by rfl⟩ : syracuseStep 1098041 = 823531) B823531
theorem B2081159 : Blo 730325 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B1098119 : Blo 730325 1098119 := bstep (se 1 (by rfl) ⟨823589, by rfl⟩ : syracuseStep 1098119 = 1647179) B1647179
theorem B8470919 : Blo 730325 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B7029139 : Blo 730325 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B2474387 : Blo 730325 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1098155 : Blo 730325 1098155 := bstep (se 1 (by rfl) ⟨823616, by rfl⟩ : syracuseStep 1098155 = 1647233) B1647233
theorem B1098185 : Blo 730325 1098185 := bstep (se 2 (by rfl) ⟨411819, by rfl⟩ : syracuseStep 1098185 = 823639) B823639
theorem B1393195 : Blo 730325 1393195 := bstep (se 1 (by rfl) ⟨1044896, by rfl⟩ : syracuseStep 1393195 = 2089793) B2089793
theorem B1098299 : Blo 730325 1098299 := bstep (se 1 (by rfl) ⟨823724, by rfl⟩ : syracuseStep 1098299 = 1647449) B1647449
theorem B1098359 : Blo 730325 1098359 := bstep (se 1 (by rfl) ⟨823769, by rfl⟩ : syracuseStep 1098359 = 1647539) B1647539
theorem B1393271 : Blo 730325 1393271 := bstep (se 1 (by rfl) ⟨1044953, by rfl⟩ : syracuseStep 1393271 = 2089907) B2089907
theorem B1098383 : Blo 730325 1098383 := bstep (se 1 (by rfl) ⟨823787, by rfl⟩ : syracuseStep 1098383 = 1647575) B1647575
theorem B1098425 : Blo 730325 1098425 := bstep (se 2 (by rfl) ⟨411909, by rfl⟩ : syracuseStep 1098425 = 823819) B823819
theorem B1852105 : Blo 730325 1852105 := bstep (se 2 (by rfl) ⟨694539, by rfl⟩ : syracuseStep 1852105 = 1389079) B1389079
theorem B1098503 : Blo 730325 1098503 := bstep (se 1 (by rfl) ⟨823877, by rfl⟩ : syracuseStep 1098503 = 1647755) B1647755
theorem B1098539 : Blo 730325 1098539 := bstep (se 1 (by rfl) ⟨823904, by rfl⟩ : syracuseStep 1098539 = 1647809) B1647809
theorem B1098569 : Blo 730325 1098569 := bstep (se 2 (by rfl) ⟨411963, by rfl⟩ : syracuseStep 1098569 = 823927) B823927
theorem B1852247 : Blo 730325 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B3130265 : Blo 730325 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B4506553 : Blo 730325 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B1098683 : Blo 730325 1098683 := bstep (se 1 (by rfl) ⟨824012, by rfl⟩ : syracuseStep 1098683 = 1648025) B1648025
theorem B1098743 : Blo 730325 1098743 := bstep (se 1 (by rfl) ⟨824057, by rfl⟩ : syracuseStep 1098743 = 1648115) B1648115
theorem B1098767 : Blo 730325 1098767 := bstep (se 1 (by rfl) ⟨824075, by rfl⟩ : syracuseStep 1098767 = 1648151) B1648151
theorem B3523607 : Blo 730325 3523607 := bstep (se 1 (by rfl) ⟨2642705, by rfl⟩ : syracuseStep 3523607 = 5285411) B5285411
theorem B1983521 : Blo 730325 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B1098809 : Blo 730325 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B3130487 : Blo 730325 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B1098887 : Blo 730325 1098887 := bstep (se 1 (by rfl) ⟨824165, by rfl⟩ : syracuseStep 1098887 = 1648331) B1648331
theorem B1098923 : Blo 730325 1098923 := bstep (se 1 (by rfl) ⟨824192, by rfl⟩ : syracuseStep 1098923 = 1648385) B1648385
theorem B1098953 : Blo 730325 1098953 := bstep (se 2 (by rfl) ⟨412107, by rfl⟩ : syracuseStep 1098953 = 824215) B824215
theorem B3949825 : Blo 730325 3949825 := bstep (se 2 (by rfl) ⟨1481184, by rfl⟩ : syracuseStep 3949825 = 2962369) B2962369
theorem B1099067 : Blo 730325 1099067 := bstep (se 1 (by rfl) ⟨824300, by rfl⟩ : syracuseStep 1099067 = 1648601) B1648601
theorem B1099127 : Blo 730325 1099127 := bstep (se 1 (by rfl) ⟨824345, by rfl⟩ : syracuseStep 1099127 = 1648691) B1648691
theorem B1099151 : Blo 730325 1099151 := bstep (se 1 (by rfl) ⟨824363, by rfl⟩ : syracuseStep 1099151 = 1648727) B1648727
theorem B1099193 : Blo 730325 1099193 := bstep (se 2 (by rfl) ⟨412197, by rfl⟩ : syracuseStep 1099193 = 824395) B824395
theorem B1099271 : Blo 730325 1099271 := bstep (se 1 (by rfl) ⟨824453, by rfl⟩ : syracuseStep 1099271 = 1648907) B1648907
theorem B1099307 : Blo 730325 1099307 := bstep (se 1 (by rfl) ⟨824480, by rfl⟩ : syracuseStep 1099307 = 1648961) B1648961
theorem B3393085 : Blo 730325 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1099337 : Blo 730325 1099337 := bstep (se 2 (by rfl) ⟨412251, by rfl⟩ : syracuseStep 1099337 = 824503) B824503
theorem B1099451 : Blo 730325 1099451 := bstep (se 1 (by rfl) ⟨824588, by rfl⟩ : syracuseStep 1099451 = 1649177) B1649177
theorem B1099511 : Blo 730325 1099511 := bstep (se 1 (by rfl) ⟨824633, by rfl⟩ : syracuseStep 1099511 = 1649267) B1649267
theorem B1099535 : Blo 730325 1099535 := bstep (se 1 (by rfl) ⟨824651, by rfl⟩ : syracuseStep 1099535 = 1649303) B1649303
theorem B2475791 : Blo 730325 2475791 := bstep (se 1 (by rfl) ⟨1856843, by rfl⟩ : syracuseStep 2475791 = 3713687) B3713687
theorem B1099577 : Blo 730325 1099577 := bstep (se 2 (by rfl) ⟨412341, by rfl⟩ : syracuseStep 1099577 = 824683) B824683
theorem B2639675 : Blo 730325 2639675 := bstep (se 1 (by rfl) ⟨1979756, by rfl⟩ : syracuseStep 2639675 = 3959513) B3959513
theorem B3524411 : Blo 730325 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B1099655 : Blo 730325 1099655 := bstep (se 1 (by rfl) ⟨824741, by rfl⟩ : syracuseStep 1099655 = 1649483) B1649483
theorem B1099691 : Blo 730325 1099691 := bstep (se 1 (by rfl) ⟨824768, by rfl⟩ : syracuseStep 1099691 = 1649537) B1649537
theorem B1099721 : Blo 730325 1099721 := bstep (se 2 (by rfl) ⟨412395, by rfl⟩ : syracuseStep 1099721 = 824791) B824791
theorem B2476061 : Blo 730325 2476061 := bstep (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) B928523
theorem B1099835 : Blo 730325 1099835 := bstep (se 1 (by rfl) ⟨824876, by rfl⟩ : syracuseStep 1099835 = 1649753) B1649753
theorem B2082935 : Blo 730325 2082935 := bstep (se 1 (by rfl) ⟨1562201, by rfl⟩ : syracuseStep 2082935 = 3124403) B3124403
theorem B1099895 : Blo 730325 1099895 := bstep (se 1 (by rfl) ⟨824921, by rfl⟩ : syracuseStep 1099895 = 1649843) B1649843
theorem B1099919 : Blo 730325 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B1099961 : Blo 730325 1099961 := bstep (se 2 (by rfl) ⟨412485, by rfl⟩ : syracuseStep 1099961 = 824971) B824971
theorem B1100039 : Blo 730325 1100039 := bstep (se 1 (by rfl) ⟨825029, by rfl⟩ : syracuseStep 1100039 = 1650059) B1650059
theorem B1100075 : Blo 730325 1100075 := bstep (se 1 (by rfl) ⟨825056, by rfl⟩ : syracuseStep 1100075 = 1650113) B1650113
theorem B1100105 : Blo 730325 1100105 := bstep (se 2 (by rfl) ⟨412539, by rfl⟩ : syracuseStep 1100105 = 825079) B825079
theorem B1100219 : Blo 730325 1100219 := bstep (se 1 (by rfl) ⟨825164, by rfl⟩ : syracuseStep 1100219 = 1650329) B1650329
theorem B7129565 : Blo 730325 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B1100279 : Blo 730325 1100279 := bstep (se 1 (by rfl) ⟨825209, by rfl⟩ : syracuseStep 1100279 = 1650419) B1650419
theorem B1100303 : Blo 730325 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B1100345 : Blo 730325 1100345 := bstep (se 2 (by rfl) ⟨412629, by rfl⟩ : syracuseStep 1100345 = 825259) B825259
theorem B1100423 : Blo 730325 1100423 := bstep (se 1 (by rfl) ⟨825317, by rfl⟩ : syracuseStep 1100423 = 1650635) B1650635
theorem B1100459 : Blo 730325 1100459 := bstep (se 1 (by rfl) ⟨825344, by rfl⟩ : syracuseStep 1100459 = 1650689) B1650689
theorem B5065409 : Blo 730325 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B1100489 : Blo 730325 1100489 := bstep (se 2 (by rfl) ⟨412683, by rfl⟩ : syracuseStep 1100489 = 825367) B825367
theorem B8440625 : Blo 730325 8440625 := bstep (se 2 (by rfl) ⟨3165234, by rfl⟩ : syracuseStep 8440625 = 6330469) B6330469
theorem B1100603 : Blo 730325 1100603 := bstep (se 1 (by rfl) ⟨825452, by rfl⟩ : syracuseStep 1100603 = 1650905) B1650905
theorem B1854323 : Blo 730325 1854323 := bstep (se 1 (by rfl) ⟨1390742, by rfl⟩ : syracuseStep 1854323 = 2781485) B2781485
theorem B1100663 : Blo 730325 1100663 := bstep (se 1 (by rfl) ⟨825497, by rfl⟩ : syracuseStep 1100663 = 1650995) B1650995
theorem B1100687 : Blo 730325 1100687 := bstep (se 1 (by rfl) ⟨825515, by rfl⟩ : syracuseStep 1100687 = 1651031) B1651031
theorem B1100729 : Blo 730325 1100729 := bstep (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) B825547
theorem B1100807 : Blo 730325 1100807 := bstep (se 1 (by rfl) ⟨825605, by rfl⟩ : syracuseStep 1100807 = 1651211) B1651211
theorem B1100843 : Blo 730325 1100843 := bstep (se 1 (by rfl) ⟨825632, by rfl⟩ : syracuseStep 1100843 = 1651265) B1651265
theorem B1100873 : Blo 730325 1100873 := bstep (se 2 (by rfl) ⟨412827, by rfl⟩ : syracuseStep 1100873 = 825655) B825655
theorem B2083927 : Blo 730325 2083927 := bstep (se 1 (by rfl) ⟨1562945, by rfl⟩ : syracuseStep 2083927 = 3125891) B3125891
theorem B3132503 : Blo 730325 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B1100987 : Blo 730325 1100987 := bstep (se 1 (by rfl) ⟨825740, by rfl⟩ : syracuseStep 1100987 = 1651481) B1651481
theorem B1101047 : Blo 730325 1101047 := bstep (se 1 (by rfl) ⟨825785, by rfl⟩ : syracuseStep 1101047 = 1651571) B1651571
theorem B1101071 : Blo 730325 1101071 := bstep (se 1 (by rfl) ⟨825803, by rfl⟩ : syracuseStep 1101071 = 1651607) B1651607
theorem B1101113 : Blo 730325 1101113 := bstep (se 2 (by rfl) ⟨412917, by rfl⟩ : syracuseStep 1101113 = 825835) B825835
theorem B1854839 : Blo 730325 1854839 := bstep (se 1 (by rfl) ⟨1391129, by rfl⟩ : syracuseStep 1854839 = 2782259) B2782259
theorem B1101191 : Blo 730325 1101191 := bstep (se 1 (by rfl) ⟨825893, by rfl⟩ : syracuseStep 1101191 = 1651787) B1651787
theorem B2477465 : Blo 730325 2477465 := bstep (se 2 (by rfl) ⟨929049, by rfl⟩ : syracuseStep 2477465 = 1858099) B1858099
theorem B1101227 : Blo 730325 1101227 := bstep (se 1 (by rfl) ⟨825920, by rfl⟩ : syracuseStep 1101227 = 1651841) B1651841
theorem B1101257 : Blo 730325 1101257 := bstep (se 2 (by rfl) ⟨412971, by rfl⟩ : syracuseStep 1101257 = 825943) B825943
theorem B1101371 : Blo 730325 1101371 := bstep (se 1 (by rfl) ⟨826028, by rfl⟩ : syracuseStep 1101371 = 1652057) B1652057
theorem B2346583 : Blo 730325 2346583 := bstep (se 1 (by rfl) ⟨1759937, by rfl⟩ : syracuseStep 2346583 = 3519875) B3519875
theorem B1101431 : Blo 730325 1101431 := bstep (se 1 (by rfl) ⟨826073, by rfl⟩ : syracuseStep 1101431 = 1652147) B1652147
theorem B1101455 : Blo 730325 1101455 := bstep (se 1 (by rfl) ⟨826091, by rfl⟩ : syracuseStep 1101455 = 1652183) B1652183
theorem B2117267 : Blo 730325 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B4181705 : Blo 730325 4181705 := bstep (se 2 (by rfl) ⟨1568139, by rfl⟩ : syracuseStep 4181705 = 3136279) B3136279
theorem B1691435 : Blo 730325 1691435 := bstep (se 1 (by rfl) ⟨1268576, by rfl⟩ : syracuseStep 1691435 = 2537153) B2537153
theorem B1232759 : Blo 730325 1232759 := bstep (se 1 (by rfl) ⟨924569, by rfl⟩ : syracuseStep 1232759 = 1849139) B1849139
theorem B2478167 : Blo 730325 2478167 := bstep (se 1 (by rfl) ⟨1858625, by rfl⟩ : syracuseStep 2478167 = 3717251) B3717251
theorem B1233211 : Blo 730325 1233211 := bstep (se 1 (by rfl) ⟨924908, by rfl⟩ : syracuseStep 1233211 = 1849817) B1849817
theorem B938299 : Blo 730325 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B1855831 : Blo 730325 1855831 := bstep (se 1 (by rfl) ⟨1391873, by rfl⟩ : syracuseStep 1855831 = 2783747) B2783747
theorem B1233353 : Blo 730325 1233353 := bstep (se 2 (by rfl) ⟨462507, by rfl⟩ : syracuseStep 1233353 = 925015) B925015
theorem B2118089 : Blo 730325 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B2085419 : Blo 730325 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B54317699 : Blo 730325 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B1856135 : Blo 730325 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B1856267 : Blo 730325 1856267 := bstep (se 1 (by rfl) ⟨1392200, by rfl⟩ : syracuseStep 1856267 = 2784401) B2784401
theorem B42160985 : Blo 730325 42160985 := bstep (se 2 (by rfl) ⟨15810369, by rfl⟩ : syracuseStep 42160985 = 31620739) B31620739
theorem B4019129 : Blo 730325 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B2774027 : Blo 730325 2774027 := bstep (se 1 (by rfl) ⟨2080520, by rfl⟩ : syracuseStep 2774027 = 4161041) B4161041
theorem B1758323 : Blo 730325 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B1234055 : Blo 730325 1234055 := bstep (se 1 (by rfl) ⟨925541, by rfl⟩ : syracuseStep 1234055 = 1851083) B1851083
theorem B1758343 : Blo 730325 1758343 := bstep (se 1 (by rfl) ⟨1318757, by rfl⟩ : syracuseStep 1758343 = 2637515) B2637515
theorem B8574125 : Blo 730325 8574125 := bstep (se 3 (by rfl) ⟨1607648, by rfl⟩ : syracuseStep 8574125 = 3215297) B3215297
theorem B1856783 : Blo 730325 1856783 := bstep (se 1 (by rfl) ⟨1392587, by rfl⟩ : syracuseStep 1856783 = 2785175) B2785175
theorem B1856915 : Blo 730325 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B2086535 : Blo 730325 2086535 := bstep (se 1 (by rfl) ⟨1564901, by rfl⟩ : syracuseStep 2086535 = 3129803) B3129803
theorem B743099 : Blo 730325 743099 := bstep (se 1 (by rfl) ⟨557324, by rfl⟩ : syracuseStep 743099 = 1114649) B1114649
theorem B7919333 : Blo 730325 7919333 := bstep (se 4 (by rfl) ⟨742437, by rfl⟩ : syracuseStep 7919333 = 1484875) B1484875
theorem B1234703 : Blo 730325 1234703 := bstep (se 1 (by rfl) ⟨926027, by rfl⟩ : syracuseStep 1234703 = 1852055) B1852055
theorem B2086717 : Blo 730325 2086717 := bstep (se 3 (by rfl) ⟨391259, by rfl⟩ : syracuseStep 2086717 = 782519) B782519
theorem B3331975 : Blo 730325 3331975 := bstep (se 1 (by rfl) ⟨2498981, by rfl⟩ : syracuseStep 3331975 = 4997963) B4997963
theorem B2774969 : Blo 730325 2774969 := bstep (se 2 (by rfl) ⟨1040613, by rfl⟩ : syracuseStep 2774969 = 2081227) B2081227
theorem B31610897 : Blo 730325 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B2087059 : Blo 730325 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B1562809 : Blo 730325 1562809 := bstep (se 2 (by rfl) ⟨586053, by rfl⟩ : syracuseStep 1562809 = 1172107) B1172107
theorem B1235243 : Blo 730325 1235243 := bstep (se 1 (by rfl) ⟨926432, by rfl⟩ : syracuseStep 1235243 = 1852865) B1852865
theorem B1005967 : Blo 730325 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B1858049 : Blo 730325 1858049 := bstep (se 2 (by rfl) ⟨696768, by rfl⟩ : syracuseStep 1858049 = 1393537) B1393537
theorem B1563151 : Blo 730325 1563151 := bstep (se 1 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 1563151 = 2344727) B2344727
theorem B743995 : Blo 730325 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B1235641 : Blo 730325 1235641 := bstep (se 2 (by rfl) ⟨463365, by rfl⟩ : syracuseStep 1235641 = 926731) B926731
theorem B8903459 : Blo 730325 8903459 := bstep (se 1 (by rfl) ⟨6677594, by rfl⟩ : syracuseStep 8903459 = 13355189) B13355189
theorem B1858423 : Blo 730325 1858423 := bstep (se 1 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 1858423 = 2787635) B2787635
theorem B2087947 : Blo 730325 2087947 := bstep (se 1 (by rfl) ⟨1565960, by rfl⟩ : syracuseStep 2087947 = 3131921) B3131921
theorem B5954647 : Blo 730325 5954647 := bstep (se 1 (by rfl) ⟨4465985, by rfl⟩ : syracuseStep 5954647 = 8931971) B8931971
theorem B1170703 : Blo 730325 1170703 := bstep (se 1 (by rfl) ⟨878027, by rfl⟩ : syracuseStep 1170703 = 1756055) B1756055
theorem B1236343 : Blo 730325 1236343 := bstep (se 1 (by rfl) ⟨927257, by rfl⟩ : syracuseStep 1236343 = 1854515) B1854515
theorem B1564039 : Blo 730325 1564039 := bstep (se 1 (by rfl) ⟨1173029, by rfl⟩ : syracuseStep 1564039 = 2346059) B2346059
theorem B13360589 : Blo 730325 13360589 := bstep (se 3 (by rfl) ⟨2505110, by rfl⟩ : syracuseStep 13360589 = 5010221) B5010221
theorem B2088449 : Blo 730325 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B1760783 : Blo 730325 1760783 := bstep (se 1 (by rfl) ⟨1320587, by rfl⟩ : syracuseStep 1760783 = 2641175) B2641175
theorem B1236539 : Blo 730325 1236539 := bstep (se 1 (by rfl) ⟨927404, by rfl⟩ : syracuseStep 1236539 = 1854809) B1854809
theorem B5922533 : Blo 730325 5922533 := bstep (se 4 (by rfl) ⟨555237, by rfl⟩ : syracuseStep 5922533 = 1110475) B1110475
theorem B2088791 : Blo 730325 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B1236937 : Blo 730325 1236937 := bstep (se 2 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 1236937 = 927703) B927703
theorem B1040887 : Blo 730325 1040887 := bstep (se 1 (by rfl) ⟨780665, by rfl⟩ : syracuseStep 1040887 = 1561331) B1561331
theorem B2777611 : Blo 730325 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B2646539 : Blo 730325 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B1761851 : Blo 730325 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1237639 : Blo 730325 1237639 := bstep (se 1 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 1237639 = 1856459) B1856459
theorem B1762091 : Blo 730325 1762091 := bstep (se 1 (by rfl) ⟨1321568, by rfl⟩ : syracuseStep 1762091 = 2643137) B2643137
theorem B2777915 : Blo 730325 2777915 := bstep (se 1 (by rfl) ⟨2083436, by rfl⟩ : syracuseStep 2777915 = 4166873) B4166873
theorem B2221085 : Blo 730325 2221085 := bstep (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) B832907
theorem B8905789 : Blo 730325 8905789 := bstep (se 3 (by rfl) ⟨1669835, by rfl⟩ : syracuseStep 8905789 = 3339671) B3339671
theorem B1205383 : Blo 730325 1205383 := bstep (se 1 (by rfl) ⟨904037, by rfl⟩ : syracuseStep 1205383 = 1808075) B1808075
theorem B877711 : Blo 730325 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B1238287 : Blo 730325 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B2778401 : Blo 730325 2778401 := bstep (se 2 (by rfl) ⟨1041900, by rfl⟩ : syracuseStep 2778401 = 2083801) B2083801
theorem B1041707 : Blo 730325 1041707 := bstep (se 1 (by rfl) ⟨781280, by rfl⟩ : syracuseStep 1041707 = 1562561) B1562561
theorem B1565995 : Blo 730325 1565995 := bstep (se 1 (by rfl) ⟨1174496, by rfl⟩ : syracuseStep 1565995 = 2348993) B2348993
theorem B14050745 : Blo 730325 14050745 := bstep (se 2 (by rfl) ⟨5269029, by rfl⟩ : syracuseStep 14050745 = 10538059) B10538059
theorem B3958283 : Blo 730325 3958283 := bstep (se 1 (by rfl) ⟨2968712, by rfl⟩ : syracuseStep 3958283 = 5937425) B5937425
theorem B16934429 : Blo 730325 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B2090681 : Blo 730325 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B1238827 : Blo 730325 1238827 := bstep (se 1 (by rfl) ⟨929120, by rfl⟩ : syracuseStep 1238827 = 1858241) B1858241
theorem B1238969 : Blo 730325 1238969 := bstep (se 2 (by rfl) ⟨464613, by rfl⟩ : syracuseStep 1238969 = 929227) B929227
theorem B2222095 : Blo 730325 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B6678551 : Blo 730325 6678551 := bstep (se 1 (by rfl) ⟨5008913, by rfl⟩ : syracuseStep 6678551 = 10017827) B10017827
theorem B2779373 : Blo 730325 2779373 := bstep (se 3 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 2779373 = 1042265) B1042265
theorem B12839467 : Blo 730325 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B12544631 : Blo 730325 12544631 := bstep (se 1 (by rfl) ⟨9408473, by rfl⟩ : syracuseStep 12544631 = 18816947) B18816947
theorem B3697325 : Blo 730325 3697325 := bstep (se 3 (by rfl) ⟨693248, by rfl⟩ : syracuseStep 3697325 = 1386497) B1386497
theorem B1043131 : Blo 730325 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B5565185 : Blo 730325 5565185 := bstep (se 2 (by rfl) ⟨2086944, by rfl⟩ : syracuseStep 5565185 = 4173889) B4173889
theorem B3009565 : Blo 730325 3009565 := bstep (se 3 (by rfl) ⟨564293, by rfl⟩ : syracuseStep 3009565 = 1128587) B1128587
theorem B3566963 : Blo 730325 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B10579409 : Blo 730325 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B6254273 : Blo 730325 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B2256925 : Blo 730325 2256925 := bstep (se 3 (by rfl) ⟨423173, by rfl⟩ : syracuseStep 2256925 = 846347) B846347
theorem B1044623 : Blo 730325 1044623 := bstep (se 1 (by rfl) ⟨783467, by rfl⟩ : syracuseStep 1044623 = 1566935) B1566935
theorem B3698945 : Blo 730325 3698945 := bstep (se 2 (by rfl) ⟨1387104, by rfl⟩ : syracuseStep 3698945 = 2774209) B2774209
theorem B2781499 : Blo 730325 2781499 := bstep (se 1 (by rfl) ⟨2086124, by rfl⟩ : syracuseStep 2781499 = 4172249) B4172249
theorem B2781985 : Blo 730325 2781985 := bstep (se 2 (by rfl) ⟨1043244, by rfl⟩ : syracuseStep 2781985 = 2086489) B2086489
theorem B1340345 : Blo 730325 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B1504289 : Blo 730325 1504289 := bstep (se 2 (by rfl) ⟨564108, by rfl⟩ : syracuseStep 1504289 = 1128217) B1128217
theorem B3699755 : Blo 730325 3699755 := bstep (se 1 (by rfl) ⟨2774816, by rfl⟩ : syracuseStep 3699755 = 5549633) B5549633
theorem B5010605 : Blo 730325 5010605 := bstep (se 3 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 5010605 = 1878977) B1878977
theorem B7533971 : Blo 730325 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B40138253 : Blo 730325 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B2782957 : Blo 730325 2782957 := bstep (se 3 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 2782957 = 1043609) B1043609
theorem B8320805 : Blo 730325 8320805 := bstep (se 4 (by rfl) ⟨780075, by rfl⟩ : syracuseStep 8320805 = 1560151) B1560151
theorem B5011237 : Blo 730325 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B2783261 : Blo 730325 2783261 := bstep (se 3 (by rfl) ⟨521861, by rfl⟩ : syracuseStep 2783261 = 1043723) B1043723
theorem B12384373 : Blo 730325 12384373 := bstep (se 5 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 12384373 = 1161035) B1161035
theorem B3701051 : Blo 730325 3701051 := bstep (se 1 (by rfl) ⟨2775788, by rfl⟩ : syracuseStep 3701051 = 5551577) B5551577
theorem B3701213 : Blo 730325 3701213 := bstep (se 3 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 3701213 = 1387955) B1387955
theorem B3701537 : Blo 730325 3701537 := bstep (se 2 (by rfl) ⟨1388076, by rfl⟩ : syracuseStep 3701537 = 2776153) B2776153
theorem B1604623 : Blo 730325 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B1506319 : Blo 730325 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B5569559 : Blo 730325 5569559 := bstep (se 1 (by rfl) ⟨4177169, by rfl⟩ : syracuseStep 5569559 = 8354339) B8354339
theorem B2227543 : Blo 730325 2227543 := bstep (se 1 (by rfl) ⟨1670657, by rfl⟩ : syracuseStep 2227543 = 3341315) B3341315
theorem B2784887 : Blo 730325 2784887 := bstep (se 1 (by rfl) ⟨2088665, by rfl⟩ : syracuseStep 2784887 = 4177331) B4177331
theorem B3702509 : Blo 730325 3702509 := bstep (se 3 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 3702509 = 1388441) B1388441
theorem B2785661 : Blo 730325 2785661 := bstep (se 3 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 2785661 = 1044623) B1044623
theorem B9372185 : Blo 730325 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B3703481 : Blo 730325 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B5571503 : Blo 730325 5571503 := bstep (se 1 (by rfl) ⟨4178627, by rfl⟩ : syracuseStep 5571503 = 8357255) B8357255
theorem B1607177 : Blo 730325 1607177 := bstep (se 2 (by rfl) ⟨602691, by rfl⟩ : syracuseStep 1607177 = 1205383) B1205383
theorem B4753043 : Blo 730325 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B3376939 : Blo 730325 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B91457333 : Blo 730325 91457333 := bstep (se 5 (by rfl) ⟨4287062, by rfl⟩ : syracuseStep 91457333 = 8574125) B8574125
theorem B4524113 : Blo 730325 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B1411511 : Blo 730325 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B2787803 : Blo 730325 2787803 := bstep (se 1 (by rfl) ⟨2090852, by rfl⟩ : syracuseStep 2787803 = 4181705) B4181705
theorem B3574253 : Blo 730325 3574253 := bstep (se 3 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 3574253 = 1340345) B1340345
theorem B821839 : Blo 730325 821839 := bstep (se 1 (by rfl) ⟨616379, by rfl⟩ : syracuseStep 821839 = 1232759) B1232759
theorem B822235 : Blo 730325 822235 := bstep (se 1 (by rfl) ⟨616676, by rfl⟩ : syracuseStep 822235 = 1233353) B1233353
theorem B36211799 : Blo 730325 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B822703 : Blo 730325 822703 := bstep (se 1 (by rfl) ⟨617027, by rfl⟩ : syracuseStep 822703 = 1234055) B1234055
theorem B15044285 : Blo 730325 15044285 := bstep (se 3 (by rfl) ⟨2820803, by rfl⟩ : syracuseStep 15044285 = 5641607) B5641607
theorem B5279555 : Blo 730325 5279555 := bstep (se 1 (by rfl) ⟨3959666, by rfl⟩ : syracuseStep 5279555 = 7919333) B7919333
theorem B823135 : Blo 730325 823135 := bstep (se 1 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 823135 = 1234703) B1234703
theorem B21073931 : Blo 730325 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B790651 : Blo 730325 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B823495 : Blo 730325 823495 := bstep (se 1 (by rfl) ⟨617621, by rfl⟩ : syracuseStep 823495 = 1235243) B1235243
theorem B5935639 : Blo 730325 5935639 := bstep (se 1 (by rfl) ⟨4451729, by rfl⟩ : syracuseStep 5935639 = 8903459) B8903459
theorem B9900755 : Blo 730325 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B824359 : Blo 730325 824359 := bstep (se 1 (by rfl) ⟨618269, by rfl⟩ : syracuseStep 824359 = 1236539) B1236539
theorem B8033701 : Blo 730325 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B1644155 : Blo 730325 1644155 := bstep (se 1 (by rfl) ⟨1233116, by rfl⟩ : syracuseStep 1644155 = 2466233) B2466233
theorem B1644281 : Blo 730325 1644281 := bstep (se 2 (by rfl) ⟨616605, by rfl⟩ : syracuseStep 1644281 = 1233211) B1233211
theorem B1251065 : Blo 730325 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B3708665 : Blo 730325 3708665 := bstep (se 2 (by rfl) ⟨1390749, by rfl⟩ : syracuseStep 3708665 = 2781499) B2781499
theorem B1644551 : Blo 730325 1644551 := bstep (se 1 (by rfl) ⟨1233413, by rfl⟩ : syracuseStep 1644551 = 2466827) B2466827
theorem B1480723 : Blo 730325 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1644623 : Blo 730325 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B3709313 : Blo 730325 3709313 := bstep (se 2 (by rfl) ⟨1390992, by rfl⟩ : syracuseStep 3709313 = 2781985) B2781985
theorem B1645019 : Blo 730325 1645019 := bstep (se 1 (by rfl) ⟨1233764, by rfl⟩ : syracuseStep 1645019 = 2467529) B2467529
theorem B2824685 : Blo 730325 2824685 := bstep (se 3 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 2824685 = 1059257) B1059257
theorem B825979 : Blo 730325 825979 := bstep (se 1 (by rfl) ⟨619484, by rfl⟩ : syracuseStep 825979 = 1238969) B1238969
theorem B8460935 : Blo 730325 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B2825027 : Blo 730325 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B1645487 : Blo 730325 1645487 := bstep (se 1 (by rfl) ⟨1234115, by rfl⟩ : syracuseStep 1645487 = 2468231) B2468231
theorem B924635 : Blo 730325 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B1317907 : Blo 730325 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B8363087 : Blo 730325 8363087 := bstep (se 1 (by rfl) ⟨6272315, by rfl⟩ : syracuseStep 8363087 = 12544631) B12544631
theorem B2464883 : Blo 730325 2464883 := bstep (se 1 (by rfl) ⟨1848662, by rfl⟩ : syracuseStep 2464883 = 3697325) B3697325
theorem B1645739 : Blo 730325 1645739 := bstep (se 1 (by rfl) ⟨1234304, by rfl⟩ : syracuseStep 1645739 = 2468609) B2468609
theorem B3710123 : Blo 730325 3710123 := bstep (se 1 (by rfl) ⟨2782592, by rfl⟩ : syracuseStep 3710123 = 5565185) B5565185
theorem B3513725 : Blo 730325 3513725 := bstep (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) B1317647
theorem B2465153 : Blo 730325 2465153 := bstep (se 2 (by rfl) ⟨924432, by rfl⟩ : syracuseStep 2465153 = 1848865) B1848865
theorem B5283245 : Blo 730325 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B925111 : Blo 730325 925111 := bstep (se 1 (by rfl) ⟨693833, by rfl⟩ : syracuseStep 925111 = 1387667) B1387667
theorem B7052939 : Blo 730325 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B3710609 : Blo 730325 3710609 := bstep (se 2 (by rfl) ⟨1391478, by rfl⟩ : syracuseStep 3710609 = 2782957) B2782957
theorem B1646279 : Blo 730325 1646279 := bstep (se 1 (by rfl) ⟨1234709, by rfl⟩ : syracuseStep 1646279 = 2469419) B2469419
theorem B4169515 : Blo 730325 4169515 := bstep (se 1 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 4169515 = 6254273) B6254273
theorem B1253227 : Blo 730325 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B10166147 : Blo 730325 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B1253303 : Blo 730325 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B1581113 : Blo 730325 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B2465963 : Blo 730325 2465963 := bstep (se 1 (by rfl) ⟨1849472, by rfl⟩ : syracuseStep 2465963 = 3698945) B3698945
theorem B1647143 : Blo 730325 1647143 := bstep (se 1 (by rfl) ⟨1235357, by rfl⟩ : syracuseStep 1647143 = 2470715) B2470715
theorem B2466503 : Blo 730325 2466503 := bstep (se 1 (by rfl) ⟨1849877, by rfl⟩ : syracuseStep 2466503 = 3699755) B3699755
theorem B926407 : Blo 730325 926407 := bstep (se 1 (by rfl) ⟨694805, by rfl⟩ : syracuseStep 926407 = 1389611) B1389611
theorem B991993 : Blo 730325 991993 := bstep (se 2 (by rfl) ⟨371997, by rfl⟩ : syracuseStep 991993 = 743995) B743995
theorem B1319753 : Blo 730325 1319753 := bstep (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) B989815
theorem B992095 : Blo 730325 992095 := bstep (se 1 (by rfl) ⟨744071, by rfl⟩ : syracuseStep 992095 = 1488143) B1488143
theorem B1647467 : Blo 730325 1647467 := bstep (se 1 (by rfl) ⟨1235600, by rfl⟩ : syracuseStep 1647467 = 2471201) B2471201
theorem B1647521 : Blo 730325 1647521 := bstep (se 2 (by rfl) ⟨617820, by rfl⟩ : syracuseStep 1647521 = 1235641) B1235641
theorem B5022647 : Blo 730325 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B9511901 : Blo 730325 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B5547203 : Blo 730325 5547203 := bstep (se 1 (by rfl) ⟨4160402, by rfl⟩ : syracuseStep 5547203 = 8320805) B8320805
theorem B730331 : Blo 730325 730331 := bstep (se 1 (by rfl) ⟨547748, by rfl⟩ : syracuseStep 730331 = 1095497) B1095497
theorem B1647863 : Blo 730325 1647863 := bstep (se 1 (by rfl) ⟨1235897, by rfl⟩ : syracuseStep 1647863 = 2471795) B2471795
theorem B730407 : Blo 730325 730407 := bstep (se 1 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 730407 = 1095611) B1095611
theorem B730447 : Blo 730325 730447 := bstep (se 1 (by rfl) ⟨547835, by rfl⟩ : syracuseStep 730447 = 1095671) B1095671
theorem B730463 : Blo 730325 730463 := bstep (se 1 (by rfl) ⟨547847, by rfl⟩ : syracuseStep 730463 = 1095695) B1095695
theorem B2139497 : Blo 730325 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B730491 : Blo 730325 730491 := bstep (se 1 (by rfl) ⟨547868, by rfl⟩ : syracuseStep 730491 = 1095737) B1095737
theorem B4695421 : Blo 730325 4695421 := bstep (se 3 (by rfl) ⟨880391, by rfl⟩ : syracuseStep 4695421 = 1760783) B1760783
theorem B730543 : Blo 730325 730543 := bstep (se 1 (by rfl) ⟨547907, by rfl⟩ : syracuseStep 730543 = 1095815) B1095815
theorem B730567 : Blo 730325 730567 := bstep (se 1 (by rfl) ⟨547925, by rfl⟩ : syracuseStep 730567 = 1095851) B1095851
theorem B7939529 : Blo 730325 7939529 := bstep (se 2 (by rfl) ⟨2977323, by rfl⟩ : syracuseStep 7939529 = 5954647) B5954647
theorem B730587 : Blo 730325 730587 := bstep (se 1 (by rfl) ⟨547940, by rfl⟩ : syracuseStep 730587 = 1095881) B1095881
theorem B730663 : Blo 730325 730663 := bstep (se 1 (by rfl) ⟨547997, by rfl⟩ : syracuseStep 730663 = 1095995) B1095995
theorem B2467367 : Blo 730325 2467367 := bstep (se 1 (by rfl) ⟨1850525, by rfl⟩ : syracuseStep 2467367 = 3701051) B3701051
theorem B730703 : Blo 730325 730703 := bstep (se 1 (by rfl) ⟨548027, by rfl⟩ : syracuseStep 730703 = 1096055) B1096055
theorem B730719 : Blo 730325 730719 := bstep (se 1 (by rfl) ⟨548039, by rfl⟩ : syracuseStep 730719 = 1096079) B1096079
theorem B730747 : Blo 730325 730747 := bstep (se 1 (by rfl) ⟨548060, by rfl⟩ : syracuseStep 730747 = 1096121) B1096121
theorem B2467475 : Blo 730325 2467475 := bstep (se 1 (by rfl) ⟨1850606, by rfl⟩ : syracuseStep 2467475 = 3701213) B3701213
theorem B730799 : Blo 730325 730799 := bstep (se 1 (by rfl) ⟨548099, by rfl⟩ : syracuseStep 730799 = 1096199) B1096199
theorem B730823 : Blo 730325 730823 := bstep (se 1 (by rfl) ⟨548117, by rfl⟩ : syracuseStep 730823 = 1096235) B1096235
theorem B730843 : Blo 730325 730843 := bstep (se 1 (by rfl) ⟨548132, by rfl⟩ : syracuseStep 730843 = 1096265) B1096265
theorem B730919 : Blo 730325 730919 := bstep (se 1 (by rfl) ⟨548189, by rfl⟩ : syracuseStep 730919 = 1096379) B1096379
theorem B1648457 : Blo 730325 1648457 := bstep (se 2 (by rfl) ⟨618171, by rfl⟩ : syracuseStep 1648457 = 1236343) B1236343
theorem B730959 : Blo 730325 730959 := bstep (se 1 (by rfl) ⟨548219, by rfl⟩ : syracuseStep 730959 = 1096439) B1096439
theorem B730975 : Blo 730325 730975 := bstep (se 1 (by rfl) ⟨548231, by rfl⟩ : syracuseStep 730975 = 1096463) B1096463
theorem B2467691 : Blo 730325 2467691 := bstep (se 1 (by rfl) ⟨1850768, by rfl⟩ : syracuseStep 2467691 = 3701537) B3701537
theorem B3712877 : Blo 730325 3712877 := bstep (se 3 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 3712877 = 1392329) B1392329
theorem B731003 : Blo 730325 731003 := bstep (se 1 (by rfl) ⟨548252, by rfl⟩ : syracuseStep 731003 = 1096505) B1096505
theorem B2467745 : Blo 730325 2467745 := bstep (se 2 (by rfl) ⟨925404, by rfl⟩ : syracuseStep 2467745 = 1850809) B1850809
theorem B731055 : Blo 730325 731055 := bstep (se 1 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 731055 = 1096583) B1096583
theorem B731079 : Blo 730325 731079 := bstep (se 1 (by rfl) ⟨548309, by rfl⟩ : syracuseStep 731079 = 1096619) B1096619
theorem B731099 : Blo 730325 731099 := bstep (se 1 (by rfl) ⟨548324, by rfl⟩ : syracuseStep 731099 = 1096649) B1096649
theorem B3713039 : Blo 730325 3713039 := bstep (se 1 (by rfl) ⟨2784779, by rfl⟩ : syracuseStep 3713039 = 5569559) B5569559
theorem B731175 : Blo 730325 731175 := bstep (se 1 (by rfl) ⟨548381, by rfl⟩ : syracuseStep 731175 = 1096763) B1096763
theorem B731215 : Blo 730325 731215 := bstep (se 1 (by rfl) ⟨548411, by rfl⟩ : syracuseStep 731215 = 1096823) B1096823
theorem B731231 : Blo 730325 731231 := bstep (se 1 (by rfl) ⟨548423, by rfl⟩ : syracuseStep 731231 = 1096847) B1096847
theorem B731259 : Blo 730325 731259 := bstep (se 1 (by rfl) ⟨548444, by rfl⟩ : syracuseStep 731259 = 1096889) B1096889
theorem B731311 : Blo 730325 731311 := bstep (se 1 (by rfl) ⟨548483, by rfl⟩ : syracuseStep 731311 = 1096967) B1096967
theorem B1386695 : Blo 730325 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B731335 : Blo 730325 731335 := bstep (se 1 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 731335 = 1097003) B1097003
theorem B731355 : Blo 730325 731355 := bstep (se 1 (by rfl) ⟨548516, by rfl⟩ : syracuseStep 731355 = 1097033) B1097033
theorem B731431 : Blo 730325 731431 := bstep (se 1 (by rfl) ⟨548573, by rfl⟩ : syracuseStep 731431 = 1097147) B1097147
theorem B731471 : Blo 730325 731471 := bstep (se 1 (by rfl) ⟨548603, by rfl⟩ : syracuseStep 731471 = 1097207) B1097207
theorem B731487 : Blo 730325 731487 := bstep (se 1 (by rfl) ⟨548615, by rfl⟩ : syracuseStep 731487 = 1097231) B1097231
theorem B731515 : Blo 730325 731515 := bstep (se 1 (by rfl) ⟨548636, by rfl⟩ : syracuseStep 731515 = 1097273) B1097273
theorem B731567 : Blo 730325 731567 := bstep (se 1 (by rfl) ⟨548675, by rfl⟩ : syracuseStep 731567 = 1097351) B1097351
theorem B731591 : Blo 730325 731591 := bstep (se 1 (by rfl) ⟨548693, by rfl⟩ : syracuseStep 731591 = 1097387) B1097387
theorem B731611 : Blo 730325 731611 := bstep (se 1 (by rfl) ⟨548708, by rfl⟩ : syracuseStep 731611 = 1097417) B1097417
theorem B2468339 : Blo 730325 2468339 := bstep (se 1 (by rfl) ⟨1851254, by rfl⟩ : syracuseStep 2468339 = 3702509) B3702509
theorem B731687 : Blo 730325 731687 := bstep (se 1 (by rfl) ⟨548765, by rfl⟩ : syracuseStep 731687 = 1097531) B1097531
theorem B731727 : Blo 730325 731727 := bstep (se 1 (by rfl) ⟨548795, by rfl⟩ : syracuseStep 731727 = 1097591) B1097591
theorem B731743 : Blo 730325 731743 := bstep (se 1 (by rfl) ⟨548807, by rfl⟩ : syracuseStep 731743 = 1097615) B1097615
theorem B1649249 : Blo 730325 1649249 := bstep (se 2 (by rfl) ⟨618468, by rfl⟩ : syracuseStep 1649249 = 1236937) B1236937
theorem B731771 : Blo 730325 731771 := bstep (se 1 (by rfl) ⟨548828, by rfl⟩ : syracuseStep 731771 = 1097657) B1097657
theorem B731823 : Blo 730325 731823 := bstep (se 1 (by rfl) ⟨548867, by rfl⟩ : syracuseStep 731823 = 1097735) B1097735
theorem B731847 : Blo 730325 731847 := bstep (se 1 (by rfl) ⟨548885, by rfl⟩ : syracuseStep 731847 = 1097771) B1097771
theorem B1387219 : Blo 730325 1387219 := bstep (se 1 (by rfl) ⟨1040414, by rfl⟩ : syracuseStep 1387219 = 2080829) B2080829
theorem B731867 : Blo 730325 731867 := bstep (se 1 (by rfl) ⟨548900, by rfl⟩ : syracuseStep 731867 = 1097801) B1097801
theorem B731943 : Blo 730325 731943 := bstep (se 1 (by rfl) ⟨548957, by rfl⟩ : syracuseStep 731943 = 1097915) B1097915
theorem B731983 : Blo 730325 731983 := bstep (se 1 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 731983 = 1097975) B1097975
theorem B731999 : Blo 730325 731999 := bstep (se 1 (by rfl) ⟨548999, by rfl⟩ : syracuseStep 731999 = 1097999) B1097999
theorem B732027 : Blo 730325 732027 := bstep (se 1 (by rfl) ⟨549020, by rfl⟩ : syracuseStep 732027 = 1098041) B1098041
theorem B1387439 : Blo 730325 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B732079 : Blo 730325 732079 := bstep (se 1 (by rfl) ⟨549059, by rfl⟩ : syracuseStep 732079 = 1098119) B1098119
theorem B5647279 : Blo 730325 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B1649591 : Blo 730325 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B732103 : Blo 730325 732103 := bstep (se 1 (by rfl) ⟨549077, by rfl⟩ : syracuseStep 732103 = 1098155) B1098155
theorem B732123 : Blo 730325 732123 := bstep (se 1 (by rfl) ⟨549092, by rfl⟩ : syracuseStep 732123 = 1098185) B1098185
theorem B2468879 : Blo 730325 2468879 := bstep (se 1 (by rfl) ⟨1851659, by rfl⟩ : syracuseStep 2468879 = 3703319) B3703319
theorem B732199 : Blo 730325 732199 := bstep (se 1 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 732199 = 1098299) B1098299
theorem B2501689 : Blo 730325 2501689 := bstep (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) B1876267
theorem B732239 : Blo 730325 732239 := bstep (se 1 (by rfl) ⟨549179, by rfl⟩ : syracuseStep 732239 = 1098359) B1098359
theorem B928847 : Blo 730325 928847 := bstep (se 1 (by rfl) ⟨696635, by rfl⟩ : syracuseStep 928847 = 1393271) B1393271
theorem B732255 : Blo 730325 732255 := bstep (se 1 (by rfl) ⟨549191, by rfl⟩ : syracuseStep 732255 = 1098383) B1098383
theorem B732283 : Blo 730325 732283 := bstep (se 1 (by rfl) ⟨549212, by rfl⟩ : syracuseStep 732283 = 1098425) B1098425
theorem B732335 : Blo 730325 732335 := bstep (se 1 (by rfl) ⟨549251, by rfl⟩ : syracuseStep 732335 = 1098503) B1098503
theorem B732359 : Blo 730325 732359 := bstep (se 1 (by rfl) ⟨549269, by rfl⟩ : syracuseStep 732359 = 1098539) B1098539
theorem B732379 : Blo 730325 732379 := bstep (se 1 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 732379 = 1098569) B1098569
theorem B732455 : Blo 730325 732455 := bstep (se 1 (by rfl) ⟨549341, by rfl⟩ : syracuseStep 732455 = 1098683) B1098683
theorem B1387849 : Blo 730325 1387849 := bstep (se 2 (by rfl) ⟨520443, by rfl⟩ : syracuseStep 1387849 = 1040887) B1040887
theorem B732495 : Blo 730325 732495 := bstep (se 1 (by rfl) ⟨549371, by rfl⟩ : syracuseStep 732495 = 1098743) B1098743
theorem B732511 : Blo 730325 732511 := bstep (se 1 (by rfl) ⟨549383, by rfl⟩ : syracuseStep 732511 = 1098767) B1098767
theorem B1322347 : Blo 730325 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B732539 : Blo 730325 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B732591 : Blo 730325 732591 := bstep (se 1 (by rfl) ⟨549443, by rfl⟩ : syracuseStep 732591 = 1098887) B1098887
theorem B732615 : Blo 730325 732615 := bstep (se 1 (by rfl) ⟨549461, by rfl⟩ : syracuseStep 732615 = 1098923) B1098923
theorem B732635 : Blo 730325 732635 := bstep (se 1 (by rfl) ⟨549476, by rfl⟩ : syracuseStep 732635 = 1098953) B1098953
theorem B1650185 : Blo 730325 1650185 := bstep (se 2 (by rfl) ⟨618819, by rfl⟩ : syracuseStep 1650185 = 1237639) B1237639
theorem B732711 : Blo 730325 732711 := bstep (se 1 (by rfl) ⟨549533, by rfl⟩ : syracuseStep 732711 = 1099067) B1099067
theorem B732751 : Blo 730325 732751 := bstep (se 1 (by rfl) ⟨549563, by rfl⟩ : syracuseStep 732751 = 1099127) B1099127
theorem B732767 : Blo 730325 732767 := bstep (se 1 (by rfl) ⟨549575, by rfl⟩ : syracuseStep 732767 = 1099151) B1099151
theorem B2469473 : Blo 730325 2469473 := bstep (se 2 (by rfl) ⟨926052, by rfl⟩ : syracuseStep 2469473 = 1852105) B1852105
theorem B1486433 : Blo 730325 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B732795 : Blo 730325 732795 := bstep (se 1 (by rfl) ⟨549596, by rfl⟩ : syracuseStep 732795 = 1099193) B1099193
theorem B732847 : Blo 730325 732847 := bstep (se 1 (by rfl) ⟨549635, by rfl⟩ : syracuseStep 732847 = 1099271) B1099271
theorem B732871 : Blo 730325 732871 := bstep (se 1 (by rfl) ⟨549653, by rfl⟩ : syracuseStep 732871 = 1099307) B1099307
theorem B732891 : Blo 730325 732891 := bstep (se 1 (by rfl) ⟨549668, by rfl⟩ : syracuseStep 732891 = 1099337) B1099337
theorem B732967 : Blo 730325 732967 := bstep (se 1 (by rfl) ⟨549725, by rfl⟩ : syracuseStep 732967 = 1099451) B1099451
theorem B733007 : Blo 730325 733007 := bstep (se 1 (by rfl) ⟨549755, by rfl⟩ : syracuseStep 733007 = 1099511) B1099511
theorem B3125087 : Blo 730325 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B733023 : Blo 730325 733023 := bstep (se 1 (by rfl) ⟨549767, by rfl⟩ : syracuseStep 733023 = 1099535) B1099535
theorem B1650527 : Blo 730325 1650527 := bstep (se 1 (by rfl) ⟨1237895, by rfl⟩ : syracuseStep 1650527 = 2475791) B2475791
theorem B5648237 : Blo 730325 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B733051 : Blo 730325 733051 := bstep (se 1 (by rfl) ⟨549788, by rfl⟩ : syracuseStep 733051 = 1099577) B1099577
theorem B6008737 : Blo 730325 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B733103 : Blo 730325 733103 := bstep (se 1 (by rfl) ⟨549827, by rfl⟩ : syracuseStep 733103 = 1099655) B1099655
theorem B733127 : Blo 730325 733127 := bstep (se 1 (by rfl) ⟨549845, by rfl⟩ : syracuseStep 733127 = 1099691) B1099691
theorem B733147 : Blo 730325 733147 := bstep (se 1 (by rfl) ⟨549860, by rfl⟩ : syracuseStep 733147 = 1099721) B1099721
theorem B1650707 : Blo 730325 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B733223 : Blo 730325 733223 := bstep (se 1 (by rfl) ⟨549917, by rfl⟩ : syracuseStep 733223 = 1099835) B1099835
theorem B733263 : Blo 730325 733263 := bstep (se 1 (by rfl) ⟨549947, by rfl⟩ : syracuseStep 733263 = 1099895) B1099895
theorem B11874385 : Blo 730325 11874385 := bstep (se 2 (by rfl) ⟨4452894, by rfl⟩ : syracuseStep 11874385 = 8905789) B8905789
theorem B733279 : Blo 730325 733279 := bstep (se 1 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 733279 = 1099919) B1099919
theorem B733307 : Blo 730325 733307 := bstep (se 1 (by rfl) ⟨549980, by rfl⟩ : syracuseStep 733307 = 1099961) B1099961
theorem B4698269 : Blo 730325 4698269 := bstep (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) B1761851
theorem B733359 : Blo 730325 733359 := bstep (se 1 (by rfl) ⟨550019, by rfl⟩ : syracuseStep 733359 = 1100039) B1100039
theorem B733383 : Blo 730325 733383 := bstep (se 1 (by rfl) ⟨550037, by rfl⟩ : syracuseStep 733383 = 1100075) B1100075
theorem B733403 : Blo 730325 733403 := bstep (se 1 (by rfl) ⟨550052, by rfl⟩ : syracuseStep 733403 = 1100105) B1100105
theorem B733479 : Blo 730325 733479 := bstep (se 1 (by rfl) ⟨550109, by rfl⟩ : syracuseStep 733479 = 1100219) B1100219
theorem B733519 : Blo 730325 733519 := bstep (se 1 (by rfl) ⟨550139, by rfl⟩ : syracuseStep 733519 = 1100279) B1100279
theorem B733535 : Blo 730325 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B1651049 : Blo 730325 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B733563 : Blo 730325 733563 := bstep (se 1 (by rfl) ⟨550172, by rfl⟩ : syracuseStep 733563 = 1100345) B1100345
theorem B733615 : Blo 730325 733615 := bstep (se 1 (by rfl) ⟨550211, by rfl⟩ : syracuseStep 733615 = 1100423) B1100423
theorem B733639 : Blo 730325 733639 := bstep (se 1 (by rfl) ⟨550229, by rfl⟩ : syracuseStep 733639 = 1100459) B1100459
theorem B733659 : Blo 730325 733659 := bstep (se 1 (by rfl) ⟨550244, by rfl⟩ : syracuseStep 733659 = 1100489) B1100489
theorem B733735 : Blo 730325 733735 := bstep (se 1 (by rfl) ⟨550301, by rfl⟩ : syracuseStep 733735 = 1100603) B1100603
theorem B733775 : Blo 730325 733775 := bstep (se 1 (by rfl) ⟨550331, by rfl⟩ : syracuseStep 733775 = 1100663) B1100663
theorem B733791 : Blo 730325 733791 := bstep (se 1 (by rfl) ⟨550343, by rfl⟩ : syracuseStep 733791 = 1100687) B1100687
theorem B733819 : Blo 730325 733819 := bstep (se 1 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 733819 = 1100729) B1100729
theorem B733871 : Blo 730325 733871 := bstep (se 1 (by rfl) ⟨550403, by rfl⟩ : syracuseStep 733871 = 1100807) B1100807
theorem B733895 : Blo 730325 733895 := bstep (se 1 (by rfl) ⟨550421, by rfl⟩ : syracuseStep 733895 = 1100843) B1100843
theorem B3715793 : Blo 730325 3715793 := bstep (se 2 (by rfl) ⟨1393422, by rfl⟩ : syracuseStep 3715793 = 2786845) B2786845
theorem B733915 : Blo 730325 733915 := bstep (se 1 (by rfl) ⟨550436, by rfl⟩ : syracuseStep 733915 = 1100873) B1100873
theorem B733991 : Blo 730325 733991 := bstep (se 1 (by rfl) ⟨550493, by rfl⟩ : syracuseStep 733991 = 1100987) B1100987
theorem B734031 : Blo 730325 734031 := bstep (se 1 (by rfl) ⟨550523, by rfl⟩ : syracuseStep 734031 = 1101047) B1101047
theorem B734047 : Blo 730325 734047 := bstep (se 1 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 734047 = 1101071) B1101071
theorem B734075 : Blo 730325 734075 := bstep (se 1 (by rfl) ⟨550556, by rfl⟩ : syracuseStep 734075 = 1101113) B1101113
theorem B734127 : Blo 730325 734127 := bstep (se 1 (by rfl) ⟨550595, by rfl⟩ : syracuseStep 734127 = 1101191) B1101191
theorem B1651643 : Blo 730325 1651643 := bstep (se 1 (by rfl) ⟨1238732, by rfl⟩ : syracuseStep 1651643 = 2477465) B2477465
theorem B734151 : Blo 730325 734151 := bstep (se 1 (by rfl) ⟨550613, by rfl⟩ : syracuseStep 734151 = 1101227) B1101227
theorem B734171 : Blo 730325 734171 := bstep (se 1 (by rfl) ⟨550628, by rfl⟩ : syracuseStep 734171 = 1101257) B1101257
theorem B2470931 : Blo 730325 2470931 := bstep (se 1 (by rfl) ⟨1853198, by rfl⟩ : syracuseStep 2470931 = 3706397) B3706397
theorem B734247 : Blo 730325 734247 := bstep (se 1 (by rfl) ⟨550685, by rfl⟩ : syracuseStep 734247 = 1101371) B1101371
theorem B1651769 : Blo 730325 1651769 := bstep (se 2 (by rfl) ⟨619413, by rfl⟩ : syracuseStep 1651769 = 1238827) B1238827
theorem B734287 : Blo 730325 734287 := bstep (se 1 (by rfl) ⟨550715, by rfl⟩ : syracuseStep 734287 = 1101431) B1101431
theorem B734303 : Blo 730325 734303 := bstep (se 1 (by rfl) ⟨550727, by rfl⟩ : syracuseStep 734303 = 1101455) B1101455
theorem B1127623 : Blo 730325 1127623 := bstep (se 1 (by rfl) ⟨845717, by rfl⟩ : syracuseStep 1127623 = 1691435) B1691435
theorem B6337739 : Blo 730325 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B2471255 : Blo 730325 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B2962793 : Blo 730325 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1652111 : Blo 730325 1652111 := bstep (se 1 (by rfl) ⟨1239083, by rfl⟩ : syracuseStep 1652111 = 2478167) B2478167
theorem B4011437 : Blo 730325 4011437 := bstep (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) B1504289
theorem B4175347 : Blo 730325 4175347 := bstep (se 1 (by rfl) ⟨3131510, by rfl⟩ : syracuseStep 4175347 = 6263021) B6263021
theorem B1390279 : Blo 730325 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B1095599 : Blo 730325 1095599 := bstep (se 1 (by rfl) ⟨821699, by rfl⟩ : syracuseStep 1095599 = 1643399) B1643399
theorem B1849351 : Blo 730325 1849351 := bstep (se 1 (by rfl) ⟨1387013, by rfl⟩ : syracuseStep 1849351 = 2774027) B2774027
theorem B1095689 : Blo 730325 1095689 := bstep (se 2 (by rfl) ⟨410883, by rfl⟩ : syracuseStep 1095689 = 821767) B821767
theorem B1095719 : Blo 730325 1095719 := bstep (se 1 (by rfl) ⟨821789, by rfl⟩ : syracuseStep 1095719 = 1643579) B1643579
theorem B17119289 : Blo 730325 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B1095803 : Blo 730325 1095803 := bstep (se 1 (by rfl) ⟨821852, by rfl⟩ : syracuseStep 1095803 = 1643705) B1643705
theorem B1095929 : Blo 730325 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B1390841 : Blo 730325 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B1096031 : Blo 730325 1096031 := bstep (se 1 (by rfl) ⟨822023, by rfl⟩ : syracuseStep 1096031 = 1644047) B1644047
theorem B1096043 : Blo 730325 1096043 := bstep (se 1 (by rfl) ⟨822032, by rfl⟩ : syracuseStep 1096043 = 1644065) B1644065
theorem B2472335 : Blo 730325 2472335 := bstep (se 1 (by rfl) ⟨1854251, by rfl⟩ : syracuseStep 2472335 = 3708503) B3708503
theorem B1391023 : Blo 730325 1391023 := bstep (se 1 (by rfl) ⟨1043267, by rfl⟩ : syracuseStep 1391023 = 2086535) B2086535
theorem B1096271 : Blo 730325 1096271 := bstep (se 1 (by rfl) ⟨822203, by rfl⟩ : syracuseStep 1096271 = 1644407) B1644407
theorem B1849979 : Blo 730325 1849979 := bstep (se 1 (by rfl) ⟨1387484, by rfl⟩ : syracuseStep 1849979 = 2774969) B2774969
theorem B1096391 : Blo 730325 1096391 := bstep (se 1 (by rfl) ⟨822293, by rfl⟩ : syracuseStep 1096391 = 1644587) B1644587
theorem B4012753 : Blo 730325 4012753 := bstep (se 2 (by rfl) ⟨1504782, by rfl⟩ : syracuseStep 4012753 = 3009565) B3009565
theorem B2472659 : Blo 730325 2472659 := bstep (se 1 (by rfl) ⟨1854494, by rfl⟩ : syracuseStep 2472659 = 3708989) B3708989
theorem B17775389 : Blo 730325 17775389 := bstep (se 3 (by rfl) ⟨3332885, by rfl⟩ : syracuseStep 17775389 = 6665771) B6665771
theorem B1096553 : Blo 730325 1096553 := bstep (se 2 (by rfl) ⟨411207, by rfl⟩ : syracuseStep 1096553 = 822415) B822415
theorem B1850273 : Blo 730325 1850273 := bstep (se 2 (by rfl) ⟨693852, by rfl⟩ : syracuseStep 1850273 = 1387705) B1387705
theorem B21085109 : Blo 730325 21085109 := bstep (se 5 (by rfl) ⟨988364, by rfl⟩ : syracuseStep 21085109 = 1976729) B1976729
theorem B1096631 : Blo 730325 1096631 := bstep (se 1 (by rfl) ⟨822473, by rfl⟩ : syracuseStep 1096631 = 1644947) B1644947
theorem B1096667 : Blo 730325 1096667 := bstep (se 1 (by rfl) ⟨822500, by rfl⟩ : syracuseStep 1096667 = 1645001) B1645001
theorem B1981597 : Blo 730325 1981597 := bstep (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) B743099
theorem B1097135 : Blo 730325 1097135 := bstep (se 1 (by rfl) ⟨822851, by rfl⟩ : syracuseStep 1097135 = 1645703) B1645703
theorem B3128777 : Blo 730325 3128777 := bstep (se 2 (by rfl) ⟨1173291, by rfl⟩ : syracuseStep 3128777 = 2346583) B2346583
theorem B1097225 : Blo 730325 1097225 := bstep (se 2 (by rfl) ⟨411459, by rfl⟩ : syracuseStep 1097225 = 822919) B822919
theorem B1883657 : Blo 730325 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1097255 : Blo 730325 1097255 := bstep (se 1 (by rfl) ⟨822941, by rfl⟩ : syracuseStep 1097255 = 1645883) B1645883
theorem B1097339 : Blo 730325 1097339 := bstep (se 1 (by rfl) ⟨823004, by rfl⟩ : syracuseStep 1097339 = 1646009) B1646009
theorem B1392299 : Blo 730325 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B2342611 : Blo 730325 2342611 := bstep (se 1 (by rfl) ⟨1756958, by rfl⟩ : syracuseStep 2342611 = 3513917) B3513917
theorem B1097465 : Blo 730325 1097465 := bstep (se 2 (by rfl) ⟨411549, by rfl⟩ : syracuseStep 1097465 = 823099) B823099
theorem B3948355 : Blo 730325 3948355 := bstep (se 1 (by rfl) ⟨2961266, by rfl⟩ : syracuseStep 3948355 = 5922533) B5922533
theorem B1097567 : Blo 730325 1097567 := bstep (se 1 (by rfl) ⟨823175, by rfl⟩ : syracuseStep 1097567 = 1646351) B1646351
theorem B1097579 : Blo 730325 1097579 := bstep (se 1 (by rfl) ⟨823184, by rfl⟩ : syracuseStep 1097579 = 1646369) B1646369
theorem B2473847 : Blo 730325 2473847 := bstep (se 1 (by rfl) ⟨1855385, by rfl⟩ : syracuseStep 2473847 = 3710771) B3710771
theorem B1392527 : Blo 730325 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B1097807 : Blo 730325 1097807 := bstep (se 1 (by rfl) ⟨823355, by rfl⟩ : syracuseStep 1097807 = 1646711) B1646711
theorem B2474063 : Blo 730325 2474063 := bstep (se 1 (by rfl) ⟨1855547, by rfl⟩ : syracuseStep 2474063 = 3711095) B3711095
theorem B1097927 : Blo 730325 1097927 := bstep (se 1 (by rfl) ⟨823445, by rfl⟩ : syracuseStep 1097927 = 1646891) B1646891
theorem B5554493 : Blo 730325 5554493 := bstep (se 3 (by rfl) ⟨1041467, by rfl⟩ : syracuseStep 5554493 = 2082935) B2082935
theorem B4178263 : Blo 730325 4178263 := bstep (se 1 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 4178263 = 6267395) B6267395
theorem B1098089 : Blo 730325 1098089 := bstep (se 2 (by rfl) ⟨411783, by rfl⟩ : syracuseStep 1098089 = 823567) B823567
theorem B1098167 : Blo 730325 1098167 := bstep (se 1 (by rfl) ⟨823625, by rfl⟩ : syracuseStep 1098167 = 1647251) B1647251
theorem B2474441 : Blo 730325 2474441 := bstep (se 2 (by rfl) ⟨927915, by rfl⟩ : syracuseStep 2474441 = 1855831) B1855831
theorem B1098203 : Blo 730325 1098203 := bstep (se 1 (by rfl) ⟨823652, by rfl⟩ : syracuseStep 1098203 = 1647305) B1647305
theorem B1851943 : Blo 730325 1851943 := bstep (se 1 (by rfl) ⟨1388957, by rfl⟩ : syracuseStep 1851943 = 2777915) B2777915
theorem B2474711 : Blo 730325 2474711 := bstep (se 1 (by rfl) ⟨1856033, by rfl⟩ : syracuseStep 2474711 = 3712067) B3712067
theorem B1983305 : Blo 730325 1983305 := bstep (se 2 (by rfl) ⟨743739, by rfl⟩ : syracuseStep 1983305 = 1487479) B1487479
theorem B1852267 : Blo 730325 1852267 := bstep (se 1 (by rfl) ⟨1389200, by rfl⟩ : syracuseStep 1852267 = 2778401) B2778401
theorem B1098671 : Blo 730325 1098671 := bstep (se 1 (by rfl) ⟨824003, by rfl⟩ : syracuseStep 1098671 = 1648007) B1648007
theorem B2474927 : Blo 730325 2474927 := bstep (se 1 (by rfl) ⟨1856195, by rfl⟩ : syracuseStep 2474927 = 3712391) B3712391
theorem B2638855 : Blo 730325 2638855 := bstep (se 1 (by rfl) ⟨1979141, by rfl⟩ : syracuseStep 2638855 = 3958283) B3958283
theorem B1098761 : Blo 730325 1098761 := bstep (se 2 (by rfl) ⟨412035, by rfl⟩ : syracuseStep 1098761 = 824071) B824071
theorem B11289619 : Blo 730325 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B1098791 : Blo 730325 1098791 := bstep (se 1 (by rfl) ⟨824093, by rfl⟩ : syracuseStep 1098791 = 1648187) B1648187
theorem B1098875 : Blo 730325 1098875 := bstep (se 1 (by rfl) ⟨824156, by rfl⟩ : syracuseStep 1098875 = 1648313) B1648313
theorem B1393787 : Blo 730325 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B1099001 : Blo 730325 1099001 := bstep (se 2 (by rfl) ⟨412125, by rfl⟩ : syracuseStep 1099001 = 824251) B824251
theorem B1099103 : Blo 730325 1099103 := bstep (se 1 (by rfl) ⟨824327, by rfl⟩ : syracuseStep 1099103 = 1648655) B1648655
theorem B1099115 : Blo 730325 1099115 := bstep (se 1 (by rfl) ⟨824336, by rfl⟩ : syracuseStep 1099115 = 1648673) B1648673
theorem B6243749 : Blo 730325 6243749 := bstep (se 4 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 6243749 = 1170703) B1170703
theorem B5948873 : Blo 730325 5948873 := bstep (se 2 (by rfl) ⟨2230827, by rfl⟩ : syracuseStep 5948873 = 4461655) B4461655
theorem B1852915 : Blo 730325 1852915 := bstep (se 1 (by rfl) ⟨1389686, by rfl⟩ : syracuseStep 1852915 = 2779373) B2779373
theorem B2344457 : Blo 730325 2344457 := bstep (se 2 (by rfl) ⟨879171, by rfl⟩ : syracuseStep 2344457 = 1758343) B1758343
theorem B2082343 : Blo 730325 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B1099343 : Blo 730325 1099343 := bstep (se 1 (by rfl) ⟨824507, by rfl⟩ : syracuseStep 1099343 = 1649015) B1649015
theorem B2082503 : Blo 730325 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1099463 : Blo 730325 1099463 := bstep (se 1 (by rfl) ⟨824597, by rfl⟩ : syracuseStep 1099463 = 1649195) B1649195
theorem B11880229 : Blo 730325 11880229 := bstep (se 4 (by rfl) ⟨1113771, by rfl⟩ : syracuseStep 11880229 = 2227543) B2227543
theorem B16893791 : Blo 730325 16893791 := bstep (se 1 (by rfl) ⟨12670343, by rfl⟩ : syracuseStep 16893791 = 25340687) B25340687
theorem B1099625 : Blo 730325 1099625 := bstep (se 2 (by rfl) ⟨412359, by rfl⟩ : syracuseStep 1099625 = 824719) B824719
theorem B2082743 : Blo 730325 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B1099703 : Blo 730325 1099703 := bstep (se 1 (by rfl) ⟨824777, by rfl⟩ : syracuseStep 1099703 = 1649555) B1649555
theorem B1099739 : Blo 730325 1099739 := bstep (se 1 (by rfl) ⟨824804, by rfl⟩ : syracuseStep 1099739 = 1649609) B1649609
theorem B5949521 : Blo 730325 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B22595993 : Blo 730325 22595993 := bstep (se 2 (by rfl) ⟨8473497, by rfl⟩ : syracuseStep 22595993 = 16946995) B16946995
theorem B1100207 : Blo 730325 1100207 := bstep (se 1 (by rfl) ⟨825155, by rfl⟩ : syracuseStep 1100207 = 1650311) B1650311
theorem B4442633 : Blo 730325 4442633 := bstep (se 2 (by rfl) ⟨1665987, by rfl⟩ : syracuseStep 4442633 = 3331975) B3331975
theorem B1100297 : Blo 730325 1100297 := bstep (se 2 (by rfl) ⟨412611, by rfl⟩ : syracuseStep 1100297 = 825223) B825223
theorem B1100327 : Blo 730325 1100327 := bstep (se 1 (by rfl) ⟨825245, by rfl⟩ : syracuseStep 1100327 = 1650491) B1650491
theorem B1854049 : Blo 730325 1854049 := bstep (se 2 (by rfl) ⟨695268, by rfl⟩ : syracuseStep 1854049 = 1390537) B1390537
theorem B1100411 : Blo 730325 1100411 := bstep (se 1 (by rfl) ⟨825308, by rfl⟩ : syracuseStep 1100411 = 1650617) B1650617
theorem B1100537 : Blo 730325 1100537 := bstep (se 2 (by rfl) ⟨412701, by rfl⟩ : syracuseStep 1100537 = 825403) B825403
theorem B1100639 : Blo 730325 1100639 := bstep (se 1 (by rfl) ⟨825479, by rfl⟩ : syracuseStep 1100639 = 1650959) B1650959
theorem B1100651 : Blo 730325 1100651 := bstep (se 1 (by rfl) ⟨825488, by rfl⟩ : syracuseStep 1100651 = 1650977) B1650977
theorem B2083745 : Blo 730325 2083745 := bstep (se 2 (by rfl) ⟨781404, by rfl⟩ : syracuseStep 2083745 = 1562809) B1562809
theorem B1100879 : Blo 730325 1100879 := bstep (se 1 (by rfl) ⟨825659, by rfl⟩ : syracuseStep 1100879 = 1651319) B1651319
theorem B1100999 : Blo 730325 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B2477303 : Blo 730325 2477303 := bstep (se 1 (by rfl) ⟨1857977, by rfl⟩ : syracuseStep 2477303 = 3715955) B3715955
theorem B2084201 : Blo 730325 2084201 := bstep (se 2 (by rfl) ⟨781575, by rfl⟩ : syracuseStep 2084201 = 1563151) B1563151
theorem B1101161 : Blo 730325 1101161 := bstep (se 2 (by rfl) ⟨412935, by rfl⟩ : syracuseStep 1101161 = 825871) B825871
theorem B1101239 : Blo 730325 1101239 := bstep (se 1 (by rfl) ⟨825929, by rfl⟩ : syracuseStep 1101239 = 1651859) B1651859
theorem B1101275 : Blo 730325 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B2674201 : Blo 730325 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B1855001 : Blo 730325 1855001 := bstep (se 2 (by rfl) ⟨695625, by rfl⟩ : syracuseStep 1855001 = 1391251) B1391251
theorem B2477627 : Blo 730325 2477627 := bstep (se 1 (by rfl) ⟨1858220, by rfl⟩ : syracuseStep 2477627 = 3716441) B3716441
theorem B26758835 : Blo 730325 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B1756883 : Blo 730325 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B2477897 : Blo 730325 2477897 := bstep (se 2 (by rfl) ⟨929211, by rfl⟩ : syracuseStep 2477897 = 1858423) B1858423
theorem B3952577 : Blo 730325 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B1855507 : Blo 730325 1855507 := bstep (se 1 (by rfl) ⟨1391630, by rfl⟩ : syracuseStep 1855507 = 2783261) B2783261
theorem B1232975 : Blo 730325 1232975 := bstep (se 1 (by rfl) ⟨924731, by rfl⟩ : syracuseStep 1232975 = 1849463) B1849463
theorem B12505265 : Blo 730325 12505265 := bstep (se 2 (by rfl) ⟨4689474, by rfl⟩ : syracuseStep 12505265 = 9378949) B9378949
theorem B26726597 : Blo 730325 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B2085385 : Blo 730325 2085385 := bstep (se 2 (by rfl) ⟨782019, by rfl⟩ : syracuseStep 2085385 = 1564039) B1564039
theorem B1561211 : Blo 730325 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B1233839 : Blo 730325 1233839 := bstep (se 1 (by rfl) ⟨925379, by rfl⟩ : syracuseStep 1233839 = 1850759) B1850759
theorem B4445111 : Blo 730325 4445111 := bstep (se 1 (by rfl) ⟨3333833, by rfl⟩ : syracuseStep 4445111 = 6667667) B6667667
theorem B1856591 : Blo 730325 1856591 := bstep (se 1 (by rfl) ⟨1392443, by rfl⟩ : syracuseStep 1856591 = 2784887) B2784887
theorem B1234271 : Blo 730325 1234271 := bstep (se 1 (by rfl) ⟨925703, by rfl⟩ : syracuseStep 1234271 = 1851407) B1851407
theorem B2348531 : Blo 730325 2348531 := bstep (se 1 (by rfl) ⟨1761398, by rfl⟩ : syracuseStep 2348531 = 3522797) B3522797
theorem B3134963 : Blo 730325 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B1857239 : Blo 730325 1857239 := bstep (se 1 (by rfl) ⟨1392929, by rfl⟩ : syracuseStep 1857239 = 2785859) B2785859
theorem B3954541 : Blo 730325 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B1234831 : Blo 730325 1234831 := bstep (se 1 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 1234831 = 1852247) B1852247
theorem B2086843 : Blo 730325 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B2349071 : Blo 730325 2349071 := bstep (se 1 (by rfl) ⟨1761803, by rfl⟩ : syracuseStep 2349071 = 3523607) B3523607
theorem B1857593 : Blo 730325 1857593 := bstep (se 2 (by rfl) ⟨696597, by rfl⟩ : syracuseStep 1857593 = 1393195) B1393195
theorem B2086991 : Blo 730325 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1235513 : Blo 730325 1235513 := bstep (se 2 (by rfl) ⟨463317, by rfl⟩ : syracuseStep 1235513 = 926635) B926635
theorem B5266205 : Blo 730325 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B1170281 : Blo 730325 1170281 := bstep (se 2 (by rfl) ⟨438855, by rfl⟩ : syracuseStep 1170281 = 877711) B877711
theorem B5266433 : Blo 730325 5266433 := bstep (se 2 (by rfl) ⟨1974912, by rfl⟩ : syracuseStep 5266433 = 3949825) B3949825
theorem B11295787 : Blo 730325 11295787 := bstep (se 1 (by rfl) ⟨8471840, by rfl⟩ : syracuseStep 11295787 = 16943681) B16943681
theorem B2087993 : Blo 730325 2087993 := bstep (se 2 (by rfl) ⟨782997, by rfl⟩ : syracuseStep 2087993 = 1565995) B1565995
theorem B5627083 : Blo 730325 5627083 := bstep (se 1 (by rfl) ⟨4220312, by rfl⟩ : syracuseStep 5627083 = 8440625) B8440625
theorem B1236215 : Blo 730325 1236215 := bstep (se 1 (by rfl) ⟨927161, by rfl⟩ : syracuseStep 1236215 = 1854323) B1854323
theorem B2088335 : Blo 730325 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B1236559 : Blo 730325 1236559 := bstep (se 1 (by rfl) ⟨927419, by rfl⟩ : syracuseStep 1236559 = 1854839) B1854839
theorem B1236809 : Blo 730325 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B1237241 : Blo 730325 1237241 := bstep (se 2 (by rfl) ⟨463965, by rfl⟩ : syracuseStep 1237241 = 927931) B927931
theorem B1237423 : Blo 730325 1237423 := bstep (se 1 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 1237423 = 1856135) B1856135
theorem B1237511 : Blo 730325 1237511 := bstep (se 1 (by rfl) ⟨928133, by rfl⟩ : syracuseStep 1237511 = 1856267) B1856267
theorem B28107323 : Blo 730325 28107323 := bstep (se 1 (by rfl) ⟨21080492, by rfl⟩ : syracuseStep 28107323 = 42160985) B42160985
theorem B2679419 : Blo 730325 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B1172215 : Blo 730325 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B2777885 : Blo 730325 2777885 := bstep (se 3 (by rfl) ⟨520853, by rfl⟩ : syracuseStep 2777885 = 1041707) B1041707
theorem B1237855 : Blo 730325 1237855 := bstep (se 1 (by rfl) ⟨928391, by rfl⟩ : syracuseStep 1237855 = 1856783) B1856783
theorem B1237943 : Blo 730325 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B6251539 : Blo 730325 6251539 := bstep (se 1 (by rfl) ⟨4688654, by rfl⟩ : syracuseStep 6251539 = 9377309) B9377309
theorem B1762361 : Blo 730325 1762361 := bstep (se 2 (by rfl) ⟨660885, by rfl⟩ : syracuseStep 1762361 = 1321771) B1321771
theorem B2778569 : Blo 730325 2778569 := bstep (se 2 (by rfl) ⟨1041963, by rfl⟩ : syracuseStep 2778569 = 2083927) B2083927
theorem B1238537 : Blo 730325 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B1238699 : Blo 730325 1238699 := bstep (se 1 (by rfl) ⟨929024, by rfl⟩ : syracuseStep 1238699 = 1858049) B1858049
theorem B3565255 : Blo 730325 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B7497515 : Blo 730325 7497515 := bstep (se 1 (by rfl) ⟨5623136, by rfl⟩ : syracuseStep 7497515 = 11246273) B11246273
theorem B2779055 : Blo 730325 2779055 := bstep (se 1 (by rfl) ⟨2084291, by rfl⟩ : syracuseStep 2779055 = 4168583) B4168583
theorem B4679633 : Blo 730325 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B6252497 : Blo 730325 6252497 := bstep (se 2 (by rfl) ⟨2344686, by rfl⟩ : syracuseStep 6252497 = 4689373) B4689373
theorem B1239097 : Blo 730325 1239097 := bstep (se 2 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 1239097 = 929323) B929323
theorem B7039133 : Blo 730325 7039133 := bstep (se 3 (by rfl) ⟨1319837, by rfl⟩ : syracuseStep 7039133 = 2639675) B2639675
theorem B9398429 : Blo 730325 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B8907059 : Blo 730325 8907059 := bstep (se 1 (by rfl) ⟨6680294, by rfl⟩ : syracuseStep 8907059 = 13360589) B13360589
theorem B3009233 : Blo 730325 3009233 := bstep (se 2 (by rfl) ⟨1128462, by rfl⟩ : syracuseStep 3009233 = 2256925) B2256925
theorem B2779859 : Blo 730325 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B4746167 : Blo 730325 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B1764359 : Blo 730325 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B879815 : Blo 730325 879815 := bstep (se 1 (by rfl) ⟨659861, by rfl⟩ : syracuseStep 879815 = 1319723) B1319723
theorem B1174727 : Blo 730325 1174727 := bstep (se 1 (by rfl) ⟨881045, by rfl⟩ : syracuseStep 1174727 = 1762091) B1762091
theorem B879979 : Blo 730325 879979 := bstep (se 1 (by rfl) ⟨659984, by rfl⟩ : syracuseStep 879979 = 1319969) B1319969
theorem B9367163 : Blo 730325 9367163 := bstep (se 1 (by rfl) ⟨7025372, by rfl⟩ : syracuseStep 9367163 = 14050745) B14050745
theorem B4222763 : Blo 730325 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B4452367 : Blo 730325 4452367 := bstep (se 1 (by rfl) ⟨3339275, by rfl⟩ : syracuseStep 4452367 = 6678551) B6678551
theorem B13332995 : Blo 730325 13332995 := bstep (se 1 (by rfl) ⟨9999746, by rfl⟩ : syracuseStep 13332995 = 19999493) B19999493
theorem B4682299 : Blo 730325 4682299 := bstep (se 1 (by rfl) ⟨3511724, by rfl⟩ : syracuseStep 4682299 = 7023449) B7023449
theorem B10711763 : Blo 730325 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B10580843 : Blo 730325 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B20083571 : Blo 730325 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B2782289 : Blo 730325 2782289 := bstep (se 2 (by rfl) ⟨1043358, by rfl⟩ : syracuseStep 2782289 = 2086717) B2086717
theorem B3568835 : Blo 730325 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B882103 : Blo 730325 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B16512497 : Blo 730325 16512497 := bstep (se 2 (by rfl) ⟨6192186, by rfl⟩ : syracuseStep 16512497 = 12384373) B12384373
theorem B5273099 : Blo 730325 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B2782745 : Blo 730325 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B2061863 : Blo 730325 2061863 := bstep (se 1 (by rfl) ⟨1546397, by rfl⟩ : syracuseStep 2061863 = 3092795) B3092795
theorem B1341289 : Blo 730325 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B3340403 : Blo 730325 3340403 := bstep (se 1 (by rfl) ⟨2505302, by rfl⟩ : syracuseStep 3340403 = 5010605) B5010605
theorem B57834163 : Blo 730325 57834163 := bstep (se 1 (by rfl) ⟨43375622, by rfl⟩ : syracuseStep 57834163 = 86751245) B86751245
theorem B2783929 : Blo 730325 2783929 := bstep (se 2 (by rfl) ⟨1043973, by rfl⟩ : syracuseStep 2783929 = 2087947) B2087947
theorem B1407851 : Blo 730325 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B7897189 : Blo 730325 7897189 := bstep (se 4 (by rfl) ⟨740361, by rfl⟩ : syracuseStep 7897189 = 1480723) B1480723
theorem B3702995 : Blo 730325 3702995 := bstep (se 1 (by rfl) ⟨2777246, by rfl⟩ : syracuseStep 3702995 = 5554493) B5554493
theorem B5571017 : Blo 730325 5571017 := bstep (se 2 (by rfl) ⟨2089131, by rfl⟩ : syracuseStep 5571017 = 4178263) B4178263
theorem B4162499 : Blo 730325 4162499 := bstep (se 1 (by rfl) ⟨3121874, by rfl⟩ : syracuseStep 4162499 = 6243749) B6243749
theorem B3965915 : Blo 730325 3965915 := bstep (se 1 (by rfl) ⟨2974436, by rfl⟩ : syracuseStep 3965915 = 5948873) B5948873
theorem B3966347 : Blo 730325 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B3016075 : Blo 730325 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B6260561 : Blo 730325 6260561 := bstep (se 2 (by rfl) ⟨2347710, by rfl⟩ : syracuseStep 6260561 = 4695421) B4695421
theorem B4753673 : Blo 730325 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B10029523 : Blo 730325 10029523 := bstep (se 1 (by rfl) ⟨7522142, by rfl⟩ : syracuseStep 10029523 = 15044285) B15044285
theorem B821983 : Blo 730325 821983 := bstep (se 1 (by rfl) ⟨616487, by rfl⟩ : syracuseStep 821983 = 1232975) B1232975
theorem B822559 : Blo 730325 822559 := bstep (se 1 (by rfl) ⟨616919, by rfl⟩ : syracuseStep 822559 = 1233839) B1233839
theorem B822847 : Blo 730325 822847 := bstep (se 1 (by rfl) ⟨617135, by rfl⟩ : syracuseStep 822847 = 1234271) B1234271
theorem B823675 : Blo 730325 823675 := bstep (se 1 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 823675 = 1235513) B1235513
theorem B5640623 : Blo 730325 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B3510803 : Blo 730325 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B3510955 : Blo 730325 3510955 := bstep (se 1 (by rfl) ⟨2633216, by rfl⟩ : syracuseStep 3510955 = 5266433) B5266433
theorem B5575391 : Blo 730325 5575391 := bstep (se 1 (by rfl) ⟨4181543, by rfl⟩ : syracuseStep 5575391 = 8363087) B8363087
theorem B1643255 : Blo 730325 1643255 := bstep (se 1 (by rfl) ⟨1232441, by rfl⟩ : syracuseStep 1643255 = 2464883) B2464883
theorem B824143 : Blo 730325 824143 := bstep (se 1 (by rfl) ⟨618107, by rfl⟩ : syracuseStep 824143 = 1236215) B1236215
theorem B1643435 : Blo 730325 1643435 := bstep (se 1 (by rfl) ⟨1232576, by rfl⟩ : syracuseStep 1643435 = 2465153) B2465153
theorem B824539 : Blo 730325 824539 := bstep (se 1 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 824539 = 1236809) B1236809
theorem B5936489 : Blo 730325 5936489 := bstep (se 2 (by rfl) ⟨2226183, by rfl⟩ : syracuseStep 5936489 = 4452367) B4452367
theorem B1054075 : Blo 730325 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B15832513 : Blo 730325 15832513 := bstep (se 2 (by rfl) ⟨5937192, by rfl⟩ : syracuseStep 15832513 = 11874385) B11874385
theorem B1643975 : Blo 730325 1643975 := bstep (se 1 (by rfl) ⟨1232981, by rfl⟩ : syracuseStep 1643975 = 2465963) B2465963
theorem B1054201 : Blo 730325 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B824827 : Blo 730325 824827 := bstep (se 1 (by rfl) ⟨618620, by rfl⟩ : syracuseStep 824827 = 1237241) B1237241
theorem B825007 : Blo 730325 825007 := bstep (se 1 (by rfl) ⟨618755, by rfl⟩ : syracuseStep 825007 = 1237511) B1237511
theorem B1644335 : Blo 730325 1644335 := bstep (se 1 (by rfl) ⟨1233251, by rfl⟩ : syracuseStep 1644335 = 2466503) B2466503
theorem B825295 : Blo 730325 825295 := bstep (se 1 (by rfl) ⟨618971, by rfl⟩ : syracuseStep 825295 = 1237943) B1237943
theorem B3348431 : Blo 730325 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B825691 : Blo 730325 825691 := bstep (se 1 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 825691 = 1238537) B1238537
theorem B1644911 : Blo 730325 1644911 := bstep (se 1 (by rfl) ⟨1233683, by rfl⟩ : syracuseStep 1644911 = 2467367) B2467367
theorem B1644983 : Blo 730325 1644983 := bstep (se 1 (by rfl) ⟨1233737, by rfl⟩ : syracuseStep 1644983 = 2467475) B2467475
theorem B825799 : Blo 730325 825799 := bstep (se 1 (by rfl) ⟨619349, by rfl⟩ : syracuseStep 825799 = 1238699) B1238699
theorem B1645127 : Blo 730325 1645127 := bstep (se 1 (by rfl) ⟨1233845, by rfl⟩ : syracuseStep 1645127 = 2467691) B2467691
theorem B1645163 : Blo 730325 1645163 := bstep (se 1 (by rfl) ⟨1233872, by rfl⟩ : syracuseStep 1645163 = 2467745) B2467745
theorem B4168331 : Blo 730325 4168331 := bstep (se 1 (by rfl) ⟨3126248, by rfl⟩ : syracuseStep 4168331 = 6252497) B6252497
theorem B4692755 : Blo 730325 4692755 := bstep (se 1 (by rfl) ⟨3519566, by rfl⟩ : syracuseStep 4692755 = 7039133) B7039133
theorem B6265619 : Blo 730325 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B924463 : Blo 730325 924463 := bstep (se 1 (by rfl) ⟨693347, by rfl⟩ : syracuseStep 924463 = 1386695) B1386695
theorem B5938039 : Blo 730325 5938039 := bstep (se 1 (by rfl) ⟨4453529, by rfl⟩ : syracuseStep 5938039 = 8907059) B8907059
theorem B1645559 : Blo 730325 1645559 := bstep (se 1 (by rfl) ⟨1234169, by rfl⟩ : syracuseStep 1645559 = 2468339) B2468339
theorem B2006155 : Blo 730325 2006155 := bstep (se 1 (by rfl) ⟨1504616, by rfl⟩ : syracuseStep 2006155 = 3009233) B3009233
theorem B924959 : Blo 730325 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B1645919 : Blo 730325 1645919 := bstep (se 1 (by rfl) ⟨1234439, by rfl⟩ : syracuseStep 1645919 = 2468879) B2468879
theorem B1646315 : Blo 730325 1646315 := bstep (se 1 (by rfl) ⟨1234736, by rfl⟩ : syracuseStep 1646315 = 2469473) B2469473
theorem B990955 : Blo 730325 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B1646441 : Blo 730325 1646441 := bstep (se 2 (by rfl) ⟨617415, by rfl⟩ : syracuseStep 1646441 = 1234831) B1234831
theorem B2465693 : Blo 730325 2465693 := bstep (se 3 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 2465693 = 924635) B924635
theorem B2465801 : Blo 730325 2465801 := bstep (se 2 (by rfl) ⟨924675, by rfl⟩ : syracuseStep 2465801 = 1849351) B1849351
theorem B8888663 : Blo 730325 8888663 := bstep (se 1 (by rfl) ⟨6666497, by rfl⟩ : syracuseStep 8888663 = 13332995) B13332995
theorem B7053895 : Blo 730325 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B1647287 : Blo 730325 1647287 := bstep (se 1 (by rfl) ⟨1235465, by rfl⟩ : syracuseStep 1647287 = 2470931) B2470931
theorem B1647503 : Blo 730325 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B77112217 : Blo 730325 77112217 := bstep (se 2 (by rfl) ⟨28917081, by rfl⟩ : syracuseStep 77112217 = 57834163) B57834163
theorem B1975195 : Blo 730325 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B3711905 : Blo 730325 3711905 := bstep (se 2 (by rfl) ⟨1391964, by rfl⟩ : syracuseStep 3711905 = 2783929) B2783929
theorem B5350337 : Blo 730325 5350337 := bstep (se 2 (by rfl) ⟨2006376, by rfl⟩ : syracuseStep 5350337 = 4012753) B4012753
theorem B3515399 : Blo 730325 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B730399 : Blo 730325 730399 := bstep (se 1 (by rfl) ⟨547799, by rfl⟩ : syracuseStep 730399 = 1095599) B1095599
theorem B730459 : Blo 730325 730459 := bstep (se 1 (by rfl) ⟨547844, by rfl⟩ : syracuseStep 730459 = 1095689) B1095689
theorem B730479 : Blo 730325 730479 := bstep (se 1 (by rfl) ⟨547859, by rfl⟩ : syracuseStep 730479 = 1095719) B1095719
theorem B11412859 : Blo 730325 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B730535 : Blo 730325 730535 := bstep (se 1 (by rfl) ⟨547901, by rfl⟩ : syracuseStep 730535 = 1095803) B1095803
theorem B730619 : Blo 730325 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B927227 : Blo 730325 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B730687 : Blo 730325 730687 := bstep (se 1 (by rfl) ⟨548015, by rfl⟩ : syracuseStep 730687 = 1096031) B1096031
theorem B730695 : Blo 730325 730695 := bstep (se 1 (by rfl) ⟨548021, by rfl⟩ : syracuseStep 730695 = 1096043) B1096043
theorem B1648223 : Blo 730325 1648223 := bstep (se 1 (by rfl) ⟨1236167, by rfl⟩ : syracuseStep 1648223 = 2472335) B2472335
theorem B730847 : Blo 730325 730847 := bstep (se 1 (by rfl) ⟨548135, by rfl⟩ : syracuseStep 730847 = 1096271) B1096271
theorem B730927 : Blo 730325 730927 := bstep (se 1 (by rfl) ⟨548195, by rfl⟩ : syracuseStep 730927 = 1096391) B1096391
theorem B1648439 : Blo 730325 1648439 := bstep (se 1 (by rfl) ⟨1236329, by rfl⟩ : syracuseStep 1648439 = 2472659) B2472659
theorem B7153541 : Blo 730325 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B731035 : Blo 730325 731035 := bstep (se 1 (by rfl) ⟨548276, by rfl⟩ : syracuseStep 731035 = 1096553) B1096553
theorem B731087 : Blo 730325 731087 := bstep (se 1 (by rfl) ⟨548315, by rfl⟩ : syracuseStep 731087 = 1096631) B1096631
theorem B731111 : Blo 730325 731111 := bstep (se 1 (by rfl) ⟨548333, by rfl⟩ : syracuseStep 731111 = 1096667) B1096667
theorem B1648745 : Blo 730325 1648745 := bstep (se 2 (by rfl) ⟨618279, by rfl⟩ : syracuseStep 1648745 = 1236559) B1236559
theorem B3123481 : Blo 730325 3123481 := bstep (se 2 (by rfl) ⟨1171305, by rfl⟩ : syracuseStep 3123481 = 2342611) B2342611
theorem B731423 : Blo 730325 731423 := bstep (se 1 (by rfl) ⟨548567, by rfl⟩ : syracuseStep 731423 = 1097135) B1097135
theorem B731483 : Blo 730325 731483 := bstep (se 1 (by rfl) ⟨548612, by rfl⟩ : syracuseStep 731483 = 1097225) B1097225
theorem B1255771 : Blo 730325 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B731503 : Blo 730325 731503 := bstep (se 1 (by rfl) ⟨548627, by rfl⟩ : syracuseStep 731503 = 1097255) B1097255
theorem B731559 : Blo 730325 731559 := bstep (se 1 (by rfl) ⟨548669, by rfl⟩ : syracuseStep 731559 = 1097339) B1097339
theorem B928199 : Blo 730325 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B731643 : Blo 730325 731643 := bstep (se 1 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 731643 = 1097465) B1097465
theorem B731711 : Blo 730325 731711 := bstep (se 1 (by rfl) ⟨548783, by rfl⟩ : syracuseStep 731711 = 1097567) B1097567
theorem B731719 : Blo 730325 731719 := bstep (se 1 (by rfl) ⟨548789, by rfl⟩ : syracuseStep 731719 = 1097579) B1097579
theorem B1649231 : Blo 730325 1649231 := bstep (se 1 (by rfl) ⟨1236923, by rfl⟩ : syracuseStep 1649231 = 2473847) B2473847
theorem B928351 : Blo 730325 928351 := bstep (se 1 (by rfl) ⟨696263, by rfl⟩ : syracuseStep 928351 = 1392527) B1392527
theorem B731871 : Blo 730325 731871 := bstep (se 1 (by rfl) ⟨548903, by rfl⟩ : syracuseStep 731871 = 1097807) B1097807
theorem B1649375 : Blo 730325 1649375 := bstep (se 1 (by rfl) ⟨1237031, by rfl⟩ : syracuseStep 1649375 = 2474063) B2474063
theorem B731951 : Blo 730325 731951 := bstep (se 1 (by rfl) ⟨548963, by rfl⟩ : syracuseStep 731951 = 1097927) B1097927
theorem B732059 : Blo 730325 732059 := bstep (se 1 (by rfl) ⟨549044, by rfl⟩ : syracuseStep 732059 = 1098089) B1098089
theorem B732111 : Blo 730325 732111 := bstep (se 1 (by rfl) ⟨549083, by rfl⟩ : syracuseStep 732111 = 1098167) B1098167
theorem B1649627 : Blo 730325 1649627 := bstep (se 1 (by rfl) ⟨1237220, by rfl⟩ : syracuseStep 1649627 = 2474441) B2474441
theorem B732135 : Blo 730325 732135 := bstep (se 1 (by rfl) ⟨549101, by rfl⟩ : syracuseStep 732135 = 1098203) B1098203
theorem B2468987 : Blo 730325 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B1649807 : Blo 730325 1649807 := bstep (se 1 (by rfl) ⟨1237355, by rfl⟩ : syracuseStep 1649807 = 2474711) B2474711
theorem B1322203 : Blo 730325 1322203 := bstep (se 1 (by rfl) ⟨991652, by rfl⟩ : syracuseStep 1322203 = 1983305) B1983305
theorem B1649897 : Blo 730325 1649897 := bstep (se 2 (by rfl) ⟨618711, by rfl⟩ : syracuseStep 1649897 = 1237423) B1237423
theorem B732447 : Blo 730325 732447 := bstep (se 1 (by rfl) ⟨549335, by rfl⟩ : syracuseStep 732447 = 1098671) B1098671
theorem B1649951 : Blo 730325 1649951 := bstep (se 1 (by rfl) ⟨1237463, by rfl⟩ : syracuseStep 1649951 = 2474927) B2474927
theorem B3714335 : Blo 730325 3714335 := bstep (se 1 (by rfl) ⟨2785751, by rfl⟩ : syracuseStep 3714335 = 5571503) B5571503
theorem B732507 : Blo 730325 732507 := bstep (se 1 (by rfl) ⟨549380, by rfl⟩ : syracuseStep 732507 = 1098761) B1098761
theorem B732527 : Blo 730325 732527 := bstep (se 1 (by rfl) ⟨549395, by rfl⟩ : syracuseStep 732527 = 1098791) B1098791
theorem B2469257 : Blo 730325 2469257 := bstep (se 2 (by rfl) ⟨925971, by rfl⟩ : syracuseStep 2469257 = 1851943) B1851943
theorem B732583 : Blo 730325 732583 := bstep (se 1 (by rfl) ⟨549437, by rfl⟩ : syracuseStep 732583 = 1098875) B1098875
theorem B732667 : Blo 730325 732667 := bstep (se 1 (by rfl) ⟨549500, by rfl⟩ : syracuseStep 732667 = 1099001) B1099001
theorem B732735 : Blo 730325 732735 := bstep (se 1 (by rfl) ⟨549551, by rfl⟩ : syracuseStep 732735 = 1099103) B1099103
theorem B732743 : Blo 730325 732743 := bstep (se 1 (by rfl) ⟨549557, by rfl⟩ : syracuseStep 732743 = 1099115) B1099115
theorem B1322657 : Blo 730325 1322657 := bstep (se 2 (by rfl) ⟨495996, by rfl⟩ : syracuseStep 1322657 = 991993) B991993
theorem B732895 : Blo 730325 732895 := bstep (se 1 (by rfl) ⟨549671, by rfl⟩ : syracuseStep 732895 = 1099343) B1099343
theorem B1650473 : Blo 730325 1650473 := bstep (se 2 (by rfl) ⟨618927, by rfl⟩ : syracuseStep 1650473 = 1237855) B1237855
theorem B1388335 : Blo 730325 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B732975 : Blo 730325 732975 := bstep (se 1 (by rfl) ⟨549731, by rfl⟩ : syracuseStep 732975 = 1099463) B1099463
theorem B2469689 : Blo 730325 2469689 := bstep (se 2 (by rfl) ⟨926133, by rfl⟩ : syracuseStep 2469689 = 1852267) B1852267
theorem B733083 : Blo 730325 733083 := bstep (se 1 (by rfl) ⟨549812, by rfl⟩ : syracuseStep 733083 = 1099625) B1099625
theorem B1388495 : Blo 730325 1388495 := bstep (se 1 (by rfl) ⟨1041371, by rfl⟩ : syracuseStep 1388495 = 2082743) B2082743
theorem B733135 : Blo 730325 733135 := bstep (se 1 (by rfl) ⟨549851, by rfl⟩ : syracuseStep 733135 = 1099703) B1099703
theorem B733159 : Blo 730325 733159 := bstep (se 1 (by rfl) ⟨549869, by rfl⟩ : syracuseStep 733159 = 1099739) B1099739
theorem B3518473 : Blo 730325 3518473 := bstep (se 2 (by rfl) ⟨1319427, by rfl⟩ : syracuseStep 3518473 = 2638855) B2638855
theorem B8335385 : Blo 730325 8335385 := bstep (se 2 (by rfl) ⟨3125769, by rfl⟩ : syracuseStep 8335385 = 6251539) B6251539
theorem B15052825 : Blo 730325 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B733471 : Blo 730325 733471 := bstep (se 1 (by rfl) ⟨550103, by rfl⟩ : syracuseStep 733471 = 1100207) B1100207
theorem B2961755 : Blo 730325 2961755 := bstep (se 1 (by rfl) ⟨2221316, by rfl⟩ : syracuseStep 2961755 = 4442633) B4442633
theorem B733531 : Blo 730325 733531 := bstep (se 1 (by rfl) ⟨550148, by rfl⟩ : syracuseStep 733531 = 1100297) B1100297
theorem B733551 : Blo 730325 733551 := bstep (se 1 (by rfl) ⟨550163, by rfl⟩ : syracuseStep 733551 = 1100327) B1100327
theorem B733607 : Blo 730325 733607 := bstep (se 1 (by rfl) ⟨550205, by rfl⟩ : syracuseStep 733607 = 1100411) B1100411
theorem B733691 : Blo 730325 733691 := bstep (se 1 (by rfl) ⟨550268, by rfl⟩ : syracuseStep 733691 = 1100537) B1100537
theorem B733759 : Blo 730325 733759 := bstep (se 1 (by rfl) ⟨550319, by rfl⟩ : syracuseStep 733759 = 1100639) B1100639
theorem B733767 : Blo 730325 733767 := bstep (se 1 (by rfl) ⟨550325, by rfl⟩ : syracuseStep 733767 = 1100651) B1100651
theorem B1389163 : Blo 730325 1389163 := bstep (se 1 (by rfl) ⟨1041872, by rfl⟩ : syracuseStep 1389163 = 2083745) B2083745
theorem B2470553 : Blo 730325 2470553 := bstep (se 2 (by rfl) ⟨926457, by rfl⟩ : syracuseStep 2470553 = 1852915) B1852915
theorem B733919 : Blo 730325 733919 := bstep (se 1 (by rfl) ⟨550439, by rfl⟩ : syracuseStep 733919 = 1100879) B1100879
theorem B733999 : Blo 730325 733999 := bstep (se 1 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 733999 = 1100999) B1100999
theorem B1651535 : Blo 730325 1651535 := bstep (se 1 (by rfl) ⟨1238651, by rfl⟩ : syracuseStep 1651535 = 2477303) B2477303
theorem B1389467 : Blo 730325 1389467 := bstep (se 1 (by rfl) ⟨1042100, by rfl⟩ : syracuseStep 1389467 = 2084201) B2084201
theorem B734107 : Blo 730325 734107 := bstep (se 1 (by rfl) ⟨550580, by rfl⟩ : syracuseStep 734107 = 1101161) B1101161
theorem B734159 : Blo 730325 734159 := bstep (se 1 (by rfl) ⟨550619, by rfl⟩ : syracuseStep 734159 = 1101239) B1101239
theorem B734183 : Blo 730325 734183 := bstep (se 1 (by rfl) ⟨550637, by rfl⟩ : syracuseStep 734183 = 1101275) B1101275
theorem B1651751 : Blo 730325 1651751 := bstep (se 1 (by rfl) ⟨1238813, by rfl⟩ : syracuseStep 1651751 = 2477627) B2477627
theorem B15840305 : Blo 730325 15840305 := bstep (se 2 (by rfl) ⟨5940114, by rfl⟩ : syracuseStep 15840305 = 11880229) B11880229
theorem B4502585 : Blo 730325 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B17839223 : Blo 730325 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B3519703 : Blo 730325 3519703 := bstep (se 1 (by rfl) ⟨2639777, by rfl⟩ : syracuseStep 3519703 = 5279555) B5279555
theorem B1651931 : Blo 730325 1651931 := bstep (se 1 (by rfl) ⟨1238948, by rfl⟩ : syracuseStep 1651931 = 2477897) B2477897
theorem B2635051 : Blo 730325 2635051 := bstep (se 1 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 2635051 = 3952577) B3952577
theorem B1652129 : Blo 730325 1652129 := bstep (se 2 (by rfl) ⟨619548, by rfl⟩ : syracuseStep 1652129 = 1239097) B1239097
theorem B8336843 : Blo 730325 8336843 := bstep (se 1 (by rfl) ⟨6252632, by rfl⟩ : syracuseStep 8336843 = 12505265) B12505265
theorem B3716765 : Blo 730325 3716765 := bstep (se 3 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 3716765 = 1393787) B1393787
theorem B6600503 : Blo 730325 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B2963407 : Blo 730325 2963407 := bstep (se 1 (by rfl) ⟨2222555, by rfl⟩ : syracuseStep 2963407 = 4445111) B4445111
theorem B1095785 : Blo 730325 1095785 := bstep (se 2 (by rfl) ⟨410919, by rfl⟩ : syracuseStep 1095785 = 821839) B821839
theorem B2472065 : Blo 730325 2472065 := bstep (se 2 (by rfl) ⟨927024, by rfl⟩ : syracuseStep 2472065 = 1854049) B1854049
theorem B1849625 : Blo 730325 1849625 := bstep (se 2 (by rfl) ⟨693609, by rfl⟩ : syracuseStep 1849625 = 1387219) B1387219
theorem B1096103 : Blo 730325 1096103 := bstep (se 1 (by rfl) ⟨822077, by rfl⟩ : syracuseStep 1096103 = 1644155) B1644155
theorem B1096187 : Blo 730325 1096187 := bstep (se 1 (by rfl) ⟨822140, by rfl⟩ : syracuseStep 1096187 = 1644281) B1644281
theorem B834043 : Blo 730325 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B2472443 : Blo 730325 2472443 := bstep (se 1 (by rfl) ⟨1854332, by rfl⟩ : syracuseStep 2472443 = 3708665) B3708665
theorem B1096313 : Blo 730325 1096313 := bstep (se 2 (by rfl) ⟨411117, by rfl⟩ : syracuseStep 1096313 = 822235) B822235
theorem B1096367 : Blo 730325 1096367 := bstep (se 1 (by rfl) ⟨822275, by rfl⟩ : syracuseStep 1096367 = 1644551) B1644551
theorem B1096415 : Blo 730325 1096415 := bstep (se 1 (by rfl) ⟨822311, by rfl⟩ : syracuseStep 1096415 = 1644623) B1644623
theorem B1391327 : Blo 730325 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B2472875 : Blo 730325 2472875 := bstep (se 1 (by rfl) ⟨1854656, by rfl⟩ : syracuseStep 2472875 = 3709313) B3709313
theorem B1096679 : Blo 730325 1096679 := bstep (se 1 (by rfl) ⟨822509, by rfl⟩ : syracuseStep 1096679 = 1645019) B1645019
theorem B1883123 : Blo 730325 1883123 := bstep (se 1 (by rfl) ⟨1412342, by rfl⟩ : syracuseStep 1883123 = 2824685) B2824685
theorem B1850465 : Blo 730325 1850465 := bstep (se 2 (by rfl) ⟨693924, by rfl⟩ : syracuseStep 1850465 = 1387849) B1387849
theorem B5291173 : Blo 730325 5291173 := bstep (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) B992095
theorem B1883351 : Blo 730325 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B1096937 : Blo 730325 1096937 := bstep (se 2 (by rfl) ⟨411351, by rfl⟩ : syracuseStep 1096937 = 822703) B822703
theorem B1096991 : Blo 730325 1096991 := bstep (se 1 (by rfl) ⟨822743, by rfl⟩ : syracuseStep 1096991 = 1645487) B1645487
theorem B1391995 : Blo 730325 1391995 := bstep (se 1 (by rfl) ⟨1043996, by rfl⟩ : syracuseStep 1391995 = 2087993) B2087993
theorem B1097159 : Blo 730325 1097159 := bstep (se 1 (by rfl) ⟨822869, by rfl⟩ : syracuseStep 1097159 = 1645739) B1645739
theorem B2473415 : Blo 730325 2473415 := bstep (se 1 (by rfl) ⟨1855061, by rfl⟩ : syracuseStep 2473415 = 3710123) B3710123
theorem B2342483 : Blo 730325 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B1392223 : Blo 730325 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B4701959 : Blo 730325 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B2473739 : Blo 730325 2473739 := bstep (se 1 (by rfl) ⟨1855304, by rfl⟩ : syracuseStep 2473739 = 3710609) B3710609
theorem B1097513 : Blo 730325 1097513 := bstep (se 2 (by rfl) ⟨411567, by rfl⟩ : syracuseStep 1097513 = 823135) B823135
theorem B1097519 : Blo 730325 1097519 := bstep (se 1 (by rfl) ⟨823139, by rfl⟩ : syracuseStep 1097519 = 1646279) B1646279
theorem B8011649 : Blo 730325 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B835535 : Blo 730325 835535 := bstep (se 1 (by rfl) ⟨626651, by rfl⟩ : syracuseStep 835535 = 1253303) B1253303
theorem B2474009 : Blo 730325 2474009 := bstep (se 2 (by rfl) ⟨927753, by rfl⟩ : syracuseStep 2474009 = 1855507) B1855507
theorem B1097993 : Blo 730325 1097993 := bstep (se 2 (by rfl) ⟨411747, by rfl⟩ : syracuseStep 1097993 = 823495) B823495
theorem B1098095 : Blo 730325 1098095 := bstep (se 1 (by rfl) ⟨823571, by rfl⟩ : syracuseStep 1098095 = 1647143) B1647143
theorem B1786279 : Blo 730325 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B1851923 : Blo 730325 1851923 := bstep (se 1 (by rfl) ⟨1388942, by rfl⟩ : syracuseStep 1851923 = 2777885) B2777885
theorem B1098311 : Blo 730325 1098311 := bstep (se 1 (by rfl) ⟨823733, by rfl⟩ : syracuseStep 1098311 = 1647467) B1647467
theorem B1098347 : Blo 730325 1098347 := bstep (se 1 (by rfl) ⟨823760, by rfl⟩ : syracuseStep 1098347 = 1647521) B1647521
theorem B6341267 : Blo 730325 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B7914185 : Blo 730325 7914185 := bstep (se 2 (by rfl) ⟨2967819, by rfl⟩ : syracuseStep 7914185 = 5935639) B5935639
theorem B6243065 : Blo 730325 6243065 := bstep (se 2 (by rfl) ⟨2341149, by rfl⟩ : syracuseStep 6243065 = 4682299) B4682299
theorem B1098575 : Blo 730325 1098575 := bstep (se 1 (by rfl) ⟨823931, by rfl⟩ : syracuseStep 1098575 = 1647863) B1647863
theorem B1426331 : Blo 730325 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B1852379 : Blo 730325 1852379 := bstep (se 1 (by rfl) ⟨1389284, by rfl⟩ : syracuseStep 1852379 = 2778569) B2778569
theorem B5293019 : Blo 730325 5293019 := bstep (se 1 (by rfl) ⟨3969764, by rfl⟩ : syracuseStep 5293019 = 7939529) B7939529
theorem B4998343 : Blo 730325 4998343 := bstep (se 1 (by rfl) ⟨3748757, by rfl⟩ : syracuseStep 4998343 = 7497515) B7497515
theorem B1098971 : Blo 730325 1098971 := bstep (se 1 (by rfl) ⟨824228, by rfl⟩ : syracuseStep 1098971 = 1648457) B1648457
theorem B2475251 : Blo 730325 2475251 := bstep (se 1 (by rfl) ⟨1856438, by rfl⟩ : syracuseStep 2475251 = 3712877) B3712877
theorem B1852703 : Blo 730325 1852703 := bstep (se 1 (by rfl) ⟨1389527, by rfl⟩ : syracuseStep 1852703 = 2779055) B2779055
theorem B2475359 : Blo 730325 2475359 := bstep (se 1 (by rfl) ⟨1856519, by rfl⟩ : syracuseStep 2475359 = 3713039) B3713039
theorem B1099145 : Blo 730325 1099145 := bstep (se 2 (by rfl) ⟨412179, by rfl⟩ : syracuseStep 1099145 = 824359) B824359
theorem B1099499 : Blo 730325 1099499 := bstep (se 1 (by rfl) ⟨824624, by rfl⟩ : syracuseStep 1099499 = 1649249) B1649249
theorem B1853239 : Blo 730325 1853239 := bstep (se 1 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 1853239 = 2779859) B2779859
theorem B3164111 : Blo 730325 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B1099727 : Blo 730325 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B1853705 : Blo 730325 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B1100123 : Blo 730325 1100123 := bstep (se 1 (by rfl) ⟨825092, by rfl⟩ : syracuseStep 1100123 = 1650185) B1650185
theorem B6244775 : Blo 730325 6244775 := bstep (se 1 (by rfl) ⟨4683581, by rfl⟩ : syracuseStep 6244775 = 9367163) B9367163
theorem B2083391 : Blo 730325 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B1100351 : Blo 730325 1100351 := bstep (se 1 (by rfl) ⟨825263, by rfl⟩ : syracuseStep 1100351 = 1650527) B1650527
theorem B1100471 : Blo 730325 1100471 := bstep (se 1 (by rfl) ⟨825353, by rfl⟩ : syracuseStep 1100471 = 1650707) B1650707
theorem B3132179 : Blo 730325 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B2476925 : Blo 730325 2476925 := bstep (se 3 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 2476925 = 928847) B928847
theorem B1100699 : Blo 730325 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B2477195 : Blo 730325 2477195 := bstep (se 1 (by rfl) ⟨1857896, by rfl⟩ : syracuseStep 2477195 = 3715793) B3715793
theorem B2346173 : Blo 730325 2346173 := bstep (se 3 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 2346173 = 879815) B879815
theorem B1854697 : Blo 730325 1854697 := bstep (se 2 (by rfl) ⟨695511, by rfl⟩ : syracuseStep 1854697 = 1391023) B1391023
theorem B13389047 : Blo 730325 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B1101095 : Blo 730325 1101095 := bstep (se 1 (by rfl) ⟨825821, by rfl⟩ : syracuseStep 1101095 = 1651643) B1651643
theorem B1101179 : Blo 730325 1101179 := bstep (se 1 (by rfl) ⟨825884, by rfl⟩ : syracuseStep 1101179 = 1651769) B1651769
theorem B1854859 : Blo 730325 1854859 := bstep (se 1 (by rfl) ⟨1391144, by rfl⟩ : syracuseStep 1854859 = 2782289) B2782289
theorem B2379223 : Blo 730325 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B1101305 : Blo 730325 1101305 := bstep (se 2 (by rfl) ⟨412989, by rfl⟩ : syracuseStep 1101305 = 825979) B825979
theorem B1101407 : Blo 730325 1101407 := bstep (se 1 (by rfl) ⟨826055, by rfl⟩ : syracuseStep 1101407 = 1652111) B1652111
theorem B2674291 : Blo 730325 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B1855163 : Blo 730325 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B1757209 : Blo 730325 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B15061049 : Blo 730325 15061049 := bstep (se 2 (by rfl) ⟨5647893, by rfl⟩ : syracuseStep 15061049 = 11295787) B11295787
theorem B2642129 : Blo 730325 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B21057893 : Blo 730325 21057893 := bstep (se 4 (by rfl) ⟨1974177, by rfl⟩ : syracuseStep 21057893 = 3948355) B3948355
theorem B1233319 : Blo 730325 1233319 := bstep (se 1 (by rfl) ⟨924989, by rfl⟩ : syracuseStep 1233319 = 1849979) B1849979
theorem B11850259 : Blo 730325 11850259 := bstep (se 1 (by rfl) ⟨8887694, by rfl⟩ : syracuseStep 11850259 = 17775389) B17775389
theorem B938567 : Blo 730325 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B1233481 : Blo 730325 1233481 := bstep (se 2 (by rfl) ⟨462555, by rfl⟩ : syracuseStep 1233481 = 925111) B925111
theorem B1233515 : Blo 730325 1233515 := bstep (se 1 (by rfl) ⟨925136, by rfl⟩ : syracuseStep 1233515 = 1850273) B1850273
theorem B2085851 : Blo 730325 2085851 := bstep (se 1 (by rfl) ⟨1564388, by rfl⟩ : syracuseStep 2085851 = 3128777) B3128777
theorem B5559353 : Blo 730325 5559353 := bstep (se 2 (by rfl) ⟨2084757, by rfl⟩ : syracuseStep 5559353 = 4169515) B4169515
theorem B1857107 : Blo 730325 1857107 := bstep (se 1 (by rfl) ⟨1392830, by rfl⟩ : syracuseStep 1857107 = 2785661) B2785661
theorem B6248123 : Blo 730325 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B1235209 : Blo 730325 1235209 := bstep (se 2 (by rfl) ⟨463203, by rfl⟩ : syracuseStep 1235209 = 926407) B926407
theorem B1562971 : Blo 730325 1562971 := bstep (se 1 (by rfl) ⟨1172228, by rfl⟩ : syracuseStep 1562971 = 2344457) B2344457
theorem B1071451 : Blo 730325 1071451 := bstep (se 1 (by rfl) ⟨803588, by rfl⟩ : syracuseStep 1071451 = 1607177) B1607177
theorem B3168695 : Blo 730325 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B60971555 : Blo 730325 60971555 := bstep (se 1 (by rfl) ⟨45728666, by rfl⟩ : syracuseStep 60971555 = 91457333) B91457333
theorem B11262527 : Blo 730325 11262527 := bstep (se 1 (by rfl) ⟨8446895, by rfl⟩ : syracuseStep 11262527 = 16893791) B16893791
theorem B15063995 : Blo 730325 15063995 := bstep (se 1 (by rfl) ⟨11297996, by rfl⟩ : syracuseStep 15063995 = 22595993) B22595993
theorem B1858535 : Blo 730325 1858535 := bstep (se 1 (by rfl) ⟨1393901, by rfl⟩ : syracuseStep 1858535 = 2787803) B2787803
theorem B2776457 : Blo 730325 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B24141199 : Blo 730325 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B1236667 : Blo 730325 1236667 := bstep (se 1 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 1236667 = 1855001) B1855001
theorem B1171255 : Blo 730325 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B14049287 : Blo 730325 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B17817731 : Blo 730325 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B1040807 : Blo 730325 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B1237727 : Blo 730325 1237727 := bstep (se 1 (by rfl) ⟨928295, by rfl⟩ : syracuseStep 1237727 = 1856591) B1856591
theorem B1565687 : Blo 730325 1565687 := bstep (se 1 (by rfl) ⟨1174265, by rfl⟩ : syracuseStep 1565687 = 2348531) B2348531
theorem B2089975 : Blo 730325 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B1238159 : Blo 730325 1238159 := bstep (se 1 (by rfl) ⟨928619, by rfl⟩ : syracuseStep 1238159 = 1857239) B1857239
theorem B7529705 : Blo 730325 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B6251813 : Blo 730325 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B1566047 : Blo 730325 1566047 := bstep (se 1 (by rfl) ⟨1174535, by rfl⟩ : syracuseStep 1566047 = 2349071) B2349071
theorem B1238395 : Blo 730325 1238395 := bstep (se 1 (by rfl) ⟨928796, by rfl⟩ : syracuseStep 1238395 = 1857593) B1857593
theorem B3335585 : Blo 730325 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B1173305 : Blo 730325 1173305 := bstep (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) B879979
theorem B1763129 : Blo 730325 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B780187 : Blo 730325 780187 := bstep (se 1 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 780187 = 1170281) B1170281
theorem B3565601 : Blo 730325 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B12479021 : Blo 730325 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B6777431 : Blo 730325 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B18738215 : Blo 730325 18738215 := bstep (se 1 (by rfl) ⟨14053661, by rfl⟩ : syracuseStep 18738215 = 28107323) B28107323
theorem B879835 : Blo 730325 879835 := bstep (se 1 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 879835 = 1319753) B1319753
theorem B2780513 : Blo 730325 2780513 := bstep (se 2 (by rfl) ⟨1042692, by rfl⟩ : syracuseStep 2780513 = 2085385) B2085385
theorem B1174907 : Blo 730325 1174907 := bstep (se 1 (by rfl) ⟨881180, by rfl⟩ : syracuseStep 1174907 = 1762361) B1762361
theorem B3698135 : Blo 730325 3698135 := bstep (se 1 (by rfl) ⟨2773601, by rfl⟩ : syracuseStep 3698135 = 5547203) B5547203
theorem B3764029 : Blo 730325 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B9531341 : Blo 730325 9531341 := bstep (se 3 (by rfl) ⟨1787126, by rfl⟩ : syracuseStep 9531341 = 3574253) B3574253
theorem B1503497 : Blo 730325 1503497 := bstep (se 2 (by rfl) ⟨563811, by rfl⟩ : syracuseStep 1503497 = 1127623) B1127623
theorem B10711601 : Blo 730325 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B1176137 : Blo 730325 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B5567129 : Blo 730325 5567129 := bstep (se 2 (by rfl) ⟨2087673, by rfl⟩ : syracuseStep 5567129 = 4175347) B4175347
theorem B1176239 : Blo 730325 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B783151 : Blo 730325 783151 := bstep (se 1 (by rfl) ⟨587363, by rfl⟩ : syracuseStep 783151 = 1174727) B1174727
theorem B5272721 : Blo 730325 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B2815175 : Blo 730325 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B3765491 : Blo 730325 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B2782457 : Blo 730325 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B7141175 : Blo 730325 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B4225159 : Blo 730325 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B11008331 : Blo 730325 11008331 := bstep (se 1 (by rfl) ⟨8256248, by rfl⟩ : syracuseStep 11008331 = 16512497) B16512497
theorem B1374575 : Blo 730325 1374575 := bstep (se 1 (by rfl) ⟨1030931, by rfl⟩ : syracuseStep 1374575 = 2061863) B2061863
theorem B14088653 : Blo 730325 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B2226935 : Blo 730325 2226935 := bstep (se 1 (by rfl) ⟨1670201, by rfl⟩ : syracuseStep 2226935 = 3340403) B3340403
theorem B7502777 : Blo 730325 7502777 := bstep (se 2 (by rfl) ⟨2813541, by rfl⟩ : syracuseStep 7502777 = 5627083) B5627083
theorem B14056739 : Blo 730325 14056739 := bstep (se 1 (by rfl) ⟨10542554, by rfl⟩ : syracuseStep 14056739 = 21085109) B21085109
theorem B1670969 : Blo 730325 1670969 := bstep (se 2 (by rfl) ⟨626613, by rfl⟩ : syracuseStep 1670969 = 1253227) B1253227
theorem B5276123 : Blo 730325 5276123 := bstep (se 1 (by rfl) ⟨3957092, by rfl⟩ : syracuseStep 5276123 = 7914185) B7914185
theorem B4162043 : Blo 730325 4162043 := bstep (se 1 (by rfl) ⟨3121532, by rfl⟩ : syracuseStep 4162043 = 6243065) B6243065
theorem B950887 : Blo 730325 950887 := bstep (se 1 (by rfl) ⟨713165, by rfl⟩ : syracuseStep 950887 = 1426331) B1426331
theorem B9405193 : Blo 730325 9405193 := bstep (se 2 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 9405193 = 7053895) B7053895
theorem B2786633 : Blo 730325 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B4163183 : Blo 730325 4163183 := bstep (se 1 (by rfl) ⟨3122387, by rfl⟩ : syracuseStep 4163183 = 6244775) B6244775
theorem B16910045 : Blo 730325 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B4164641 : Blo 730325 4164641 := bstep (se 2 (by rfl) ⟨1561740, by rfl⟩ : syracuseStep 4164641 = 3123481) B3123481
theorem B822343 : Blo 730325 822343 := bstep (se 1 (by rfl) ⟨616757, by rfl⟩ : syracuseStep 822343 = 1233515) B1233515
theorem B1674361 : Blo 730325 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B13372697 : Blo 730325 13372697 := bstep (se 2 (by rfl) ⟨5014761, by rfl⟩ : syracuseStep 13372697 = 10029523) B10029523
theorem B3706235 : Blo 730325 3706235 := bstep (se 1 (by rfl) ⟨2779676, by rfl⟩ : syracuseStep 3706235 = 5559353) B5559353
theorem B4165415 : Blo 730325 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B2232287 : Blo 730325 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B7508351 : Blo 730325 7508351 := bstep (se 1 (by rfl) ⟨5631263, by rfl⟩ : syracuseStep 7508351 = 11262527) B11262527
theorem B5018705 : Blo 730325 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B1643795 : Blo 730325 1643795 := bstep (se 1 (by rfl) ⟨1232846, by rfl⟩ : syracuseStep 1643795 = 2465693) B2465693
theorem B1643867 : Blo 730325 1643867 := bstep (se 1 (by rfl) ⟨1232900, by rfl⟩ : syracuseStep 1643867 = 2465801) B2465801
theorem B4691297 : Blo 730325 4691297 := bstep (se 2 (by rfl) ⟨1759236, by rfl⟩ : syracuseStep 4691297 = 3518473) B3518473
theorem B825151 : Blo 730325 825151 := bstep (se 1 (by rfl) ⟨618863, by rfl⟩ : syracuseStep 825151 = 1237727) B1237727
theorem B1644425 : Blo 730325 1644425 := bstep (se 2 (by rfl) ⟨616659, by rfl⟩ : syracuseStep 1644425 = 1233319) B1233319
theorem B15800345 : Blo 730325 15800345 := bstep (se 2 (by rfl) ⟨5925129, by rfl⟩ : syracuseStep 15800345 = 11850259) B11850259
theorem B825439 : Blo 730325 825439 := bstep (se 1 (by rfl) ⟨619079, by rfl⟩ : syracuseStep 825439 = 1238159) B1238159
theorem B1644641 : Blo 730325 1644641 := bstep (se 2 (by rfl) ⟨616740, by rfl⟩ : syracuseStep 1644641 = 1233481) B1233481
theorem B5019803 : Blo 730325 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B4167875 : Blo 730325 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B4692937 : Blo 730325 4692937 := bstep (se 2 (by rfl) ⟨1759851, by rfl⟩ : syracuseStep 4692937 = 3519703) B3519703
theorem B3513401 : Blo 730325 3513401 := bstep (se 2 (by rfl) ⟨1317525, by rfl⟩ : syracuseStep 3513401 = 2635051) B2635051
theorem B21110017 : Blo 730325 21110017 := bstep (se 2 (by rfl) ⟨7916256, by rfl⟩ : syracuseStep 21110017 = 15832513) B15832513
theorem B12492143 : Blo 730325 12492143 := bstep (se 1 (by rfl) ⟨9369107, by rfl⟩ : syracuseStep 12492143 = 18738215) B18738215
theorem B1645991 : Blo 730325 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1646171 : Blo 730325 1646171 := bstep (se 1 (by rfl) ⟨1234628, by rfl⟩ : syracuseStep 1646171 = 2469257) B2469257
theorem B2465423 : Blo 730325 2465423 := bstep (se 1 (by rfl) ⟨1849067, by rfl⟩ : syracuseStep 2465423 = 3698135) B3698135
theorem B1646459 : Blo 730325 1646459 := bstep (se 1 (by rfl) ⟨1234844, by rfl⟩ : syracuseStep 1646459 = 2469689) B2469689
theorem B925663 : Blo 730325 925663 := bstep (se 1 (by rfl) ⟨694247, by rfl⟩ : syracuseStep 925663 = 1388495) B1388495
theorem B1974503 : Blo 730325 1974503 := bstep (se 1 (by rfl) ⟨1480877, by rfl⟩ : syracuseStep 1974503 = 2961755) B2961755
theorem B1646945 : Blo 730325 1646945 := bstep (se 2 (by rfl) ⟨617604, by rfl⟩ : syracuseStep 1646945 = 1235209) B1235209
theorem B1647035 : Blo 730325 1647035 := bstep (se 1 (by rfl) ⟨1235276, by rfl⟩ : syracuseStep 1647035 = 2470553) B2470553
theorem B3711419 : Blo 730325 3711419 := bstep (se 1 (by rfl) ⟨2783564, by rfl⟩ : syracuseStep 3711419 = 5567129) B5567129
theorem B5022269 : Blo 730325 5022269 := bstep (se 3 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 5022269 = 1883351) B1883351
theorem B926311 : Blo 730325 926311 := bstep (se 1 (by rfl) ⟨694733, by rfl⟩ : syracuseStep 926311 = 1389467) B1389467
theorem B10560203 : Blo 730325 10560203 := bstep (se 1 (by rfl) ⟨7920152, by rfl⟩ : syracuseStep 10560203 = 15840305) B15840305
theorem B2466557 : Blo 730325 2466557 := bstep (se 3 (by rfl) ⟨462479, by rfl⟩ : syracuseStep 2466557 = 924959) B924959
theorem B3515147 : Blo 730325 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B1876783 : Blo 730325 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B4400335 : Blo 730325 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B4760783 : Blo 730325 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B730523 : Blo 730325 730523 := bstep (se 1 (by rfl) ⟨547892, by rfl⟩ : syracuseStep 730523 = 1095785) B1095785
theorem B1648043 : Blo 730325 1648043 := bstep (se 1 (by rfl) ⟨1236032, by rfl⟩ : syracuseStep 1648043 = 2472065) B2472065
theorem B7054897 : Blo 730325 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B730735 : Blo 730325 730735 := bstep (se 1 (by rfl) ⟨548051, by rfl⟩ : syracuseStep 730735 = 1096103) B1096103
theorem B730791 : Blo 730325 730791 := bstep (se 1 (by rfl) ⟨548093, by rfl⟩ : syracuseStep 730791 = 1096187) B1096187
theorem B1648295 : Blo 730325 1648295 := bstep (se 1 (by rfl) ⟨1236221, by rfl⟩ : syracuseStep 1648295 = 2472443) B2472443
theorem B730875 : Blo 730325 730875 := bstep (se 1 (by rfl) ⟨548156, by rfl⟩ : syracuseStep 730875 = 1096313) B1096313
theorem B730911 : Blo 730325 730911 := bstep (se 1 (by rfl) ⟨548183, by rfl⟩ : syracuseStep 730911 = 1096367) B1096367
theorem B730943 : Blo 730325 730943 := bstep (se 1 (by rfl) ⟨548207, by rfl⟩ : syracuseStep 730943 = 1096415) B1096415
theorem B927551 : Blo 730325 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B1484623 : Blo 730325 1484623 := bstep (se 1 (by rfl) ⟨1113467, by rfl⟩ : syracuseStep 1484623 = 2226935) B2226935
theorem B32188265 : Blo 730325 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B1648583 : Blo 730325 1648583 := bstep (se 1 (by rfl) ⟨1236437, by rfl⟩ : syracuseStep 1648583 = 2472875) B2472875
theorem B731119 : Blo 730325 731119 := bstep (se 1 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 731119 = 1096679) B1096679
theorem B1255415 : Blo 730325 1255415 := bstep (se 1 (by rfl) ⟨941561, by rfl⟩ : syracuseStep 1255415 = 1883123) B1883123
theorem B731291 : Blo 730325 731291 := bstep (se 1 (by rfl) ⟨548468, by rfl⟩ : syracuseStep 731291 = 1096937) B1096937
theorem B731327 : Blo 730325 731327 := bstep (se 1 (by rfl) ⟨548495, by rfl⟩ : syracuseStep 731327 = 1096991) B1096991
theorem B1648889 : Blo 730325 1648889 := bstep (se 2 (by rfl) ⟨618333, by rfl⟩ : syracuseStep 1648889 = 1236667) B1236667
theorem B731439 : Blo 730325 731439 := bstep (se 1 (by rfl) ⟨548579, by rfl⟩ : syracuseStep 731439 = 1097159) B1097159
theorem B1648943 : Blo 730325 1648943 := bstep (se 1 (by rfl) ⟨1236707, by rfl⟩ : syracuseStep 1648943 = 2473415) B2473415
theorem B1321273 : Blo 730325 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B1649159 : Blo 730325 1649159 := bstep (se 1 (by rfl) ⟨1236869, by rfl⟩ : syracuseStep 1649159 = 2473739) B2473739
theorem B731675 : Blo 730325 731675 := bstep (se 1 (by rfl) ⟨548756, by rfl⟩ : syracuseStep 731675 = 1097513) B1097513
theorem B731679 : Blo 730325 731679 := bstep (se 1 (by rfl) ⟨548759, by rfl⟩ : syracuseStep 731679 = 1097519) B1097519
theorem B1649339 : Blo 730325 1649339 := bstep (se 1 (by rfl) ⟨1237004, by rfl⟩ : syracuseStep 1649339 = 2474009) B2474009
theorem B10529585 : Blo 730325 10529585 := bstep (se 2 (by rfl) ⟨3948594, by rfl⟩ : syracuseStep 10529585 = 7897189) B7897189
theorem B2468663 : Blo 730325 2468663 := bstep (se 1 (by rfl) ⟨1851497, by rfl⟩ : syracuseStep 2468663 = 3702995) B3702995
theorem B731995 : Blo 730325 731995 := bstep (se 1 (by rfl) ⟨548996, by rfl⟩ : syracuseStep 731995 = 1097993) B1097993
theorem B732063 : Blo 730325 732063 := bstep (se 1 (by rfl) ⟨549047, by rfl⟩ : syracuseStep 732063 = 1098095) B1098095
theorem B3714011 : Blo 730325 3714011 := bstep (se 1 (by rfl) ⟨2785508, by rfl⟩ : syracuseStep 3714011 = 5571017) B5571017
theorem B732207 : Blo 730325 732207 := bstep (se 1 (by rfl) ⟨549155, by rfl⟩ : syracuseStep 732207 = 1098311) B1098311
theorem B732231 : Blo 730325 732231 := bstep (se 1 (by rfl) ⟨549173, by rfl⟩ : syracuseStep 732231 = 1098347) B1098347
theorem B732383 : Blo 730325 732383 := bstep (se 1 (by rfl) ⟨549287, by rfl⟩ : syracuseStep 732383 = 1098575) B1098575
theorem B732647 : Blo 730325 732647 := bstep (se 1 (by rfl) ⟨549485, by rfl⟩ : syracuseStep 732647 = 1098971) B1098971
theorem B1650167 : Blo 730325 1650167 := bstep (se 1 (by rfl) ⟨1237625, by rfl⟩ : syracuseStep 1650167 = 2475251) B2475251
theorem B23703101 : Blo 730325 23703101 := bstep (se 3 (by rfl) ⟨4444331, by rfl⟩ : syracuseStep 23703101 = 8888663) B8888663
theorem B1650239 : Blo 730325 1650239 := bstep (se 1 (by rfl) ⟨1237679, by rfl⟩ : syracuseStep 1650239 = 2475359) B2475359
theorem B732763 : Blo 730325 732763 := bstep (se 1 (by rfl) ⟨549572, by rfl⟩ : syracuseStep 732763 = 1099145) B1099145
theorem B732999 : Blo 730325 732999 := bstep (se 1 (by rfl) ⟨549749, by rfl⟩ : syracuseStep 732999 = 1099499) B1099499
theorem B2633593 : Blo 730325 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B4173707 : Blo 730325 4173707 := bstep (se 1 (by rfl) ⟨3130280, by rfl⟩ : syracuseStep 4173707 = 6260561) B6260561
theorem B2109407 : Blo 730325 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B733151 : Blo 730325 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B2502845 : Blo 730325 2502845 := bstep (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) B938567
theorem B733415 : Blo 730325 733415 := bstep (se 1 (by rfl) ⟨550061, by rfl⟩ : syracuseStep 733415 = 1100123) B1100123
theorem B6664457 : Blo 730325 6664457 := bstep (se 2 (by rfl) ⟨2499171, by rfl⟩ : syracuseStep 6664457 = 4998343) B4998343
theorem B1388927 : Blo 730325 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B733567 : Blo 730325 733567 := bstep (se 1 (by rfl) ⟨550175, by rfl⟩ : syracuseStep 733567 = 1100351) B1100351
theorem B733647 : Blo 730325 733647 := bstep (se 1 (by rfl) ⟨550235, by rfl⟩ : syracuseStep 733647 = 1100471) B1100471
theorem B5714405 : Blo 730325 5714405 := bstep (se 4 (by rfl) ⟨535725, by rfl⟩ : syracuseStep 5714405 = 1071451) B1071451
theorem B15217145 : Blo 730325 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B1651193 : Blo 730325 1651193 := bstep (se 2 (by rfl) ⟨619197, by rfl⟩ : syracuseStep 1651193 = 1238395) B1238395
theorem B1651283 : Blo 730325 1651283 := bstep (se 1 (by rfl) ⟨1238462, by rfl⟩ : syracuseStep 1651283 = 2476925) B2476925
theorem B733799 : Blo 730325 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B1651463 : Blo 730325 1651463 := bstep (se 1 (by rfl) ⟨1238597, by rfl⟩ : syracuseStep 1651463 = 2477195) B2477195
theorem B8926031 : Blo 730325 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B734063 : Blo 730325 734063 := bstep (se 1 (by rfl) ⟨550547, by rfl⟩ : syracuseStep 734063 = 1101095) B1101095
theorem B734119 : Blo 730325 734119 := bstep (se 1 (by rfl) ⟨550589, by rfl⟩ : syracuseStep 734119 = 1101179) B1101179
theorem B734203 : Blo 730325 734203 := bstep (se 1 (by rfl) ⟨550652, by rfl⟩ : syracuseStep 734203 = 1101305) B1101305
theorem B734271 : Blo 730325 734271 := bstep (se 1 (by rfl) ⟨550703, by rfl⟩ : syracuseStep 734271 = 1101407) B1101407
theorem B2470985 : Blo 730325 2470985 := bstep (se 2 (by rfl) ⟨926619, by rfl⟩ : syracuseStep 2470985 = 1853239) B1853239
theorem B4175165 : Blo 730325 4175165 := bstep (se 3 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 4175165 = 1565687) B1565687
theorem B10040699 : Blo 730325 10040699 := bstep (se 1 (by rfl) ⟨7530524, by rfl⟩ : syracuseStep 10040699 = 15061049) B15061049
theorem B12006893 : Blo 730325 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B14038595 : Blo 730325 14038595 := bstep (se 1 (by rfl) ⟨10528946, by rfl⟩ : syracuseStep 14038595 = 21057893) B21057893
theorem B2340535 : Blo 730325 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B3716927 : Blo 730325 3716927 := bstep (se 1 (by rfl) ⟨2787695, by rfl⟩ : syracuseStep 3716927 = 5575391) B5575391
theorem B1095503 : Blo 730325 1095503 := bstep (se 1 (by rfl) ⟨821627, by rfl⟩ : syracuseStep 1095503 = 1643255) B1643255
theorem B1095623 : Blo 730325 1095623 := bstep (se 1 (by rfl) ⟨821717, by rfl⟩ : syracuseStep 1095623 = 1643435) B1643435
theorem B18725093 : Blo 730325 18725093 := bstep (se 4 (by rfl) ⟨1755477, by rfl⟩ : syracuseStep 18725093 = 3510955) B3510955
theorem B1095977 : Blo 730325 1095977 := bstep (se 2 (by rfl) ⟨410991, by rfl⟩ : syracuseStep 1095977 = 821983) B821983
theorem B1095983 : Blo 730325 1095983 := bstep (se 1 (by rfl) ⟨821987, by rfl⟩ : syracuseStep 1095983 = 1643975) B1643975
theorem B8894893 : Blo 730325 8894893 := bstep (se 3 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 8894893 = 3335585) B3335585
theorem B1096223 : Blo 730325 1096223 := bstep (se 1 (by rfl) ⟨822167, by rfl⟩ : syracuseStep 1096223 = 1644335) B1644335
theorem B2472605 : Blo 730325 2472605 := bstep (se 3 (by rfl) ⟨463613, by rfl⟩ : syracuseStep 2472605 = 927227) B927227
theorem B1096607 : Blo 730325 1096607 := bstep (se 1 (by rfl) ⟨822455, by rfl⟩ : syracuseStep 1096607 = 1644911) B1644911
theorem B4176805 : Blo 730325 4176805 := bstep (se 4 (by rfl) ⟨391575, by rfl⟩ : syracuseStep 4176805 = 783151) B783151
theorem B1096655 : Blo 730325 1096655 := bstep (se 1 (by rfl) ⟨822491, by rfl⟩ : syracuseStep 1096655 = 1644983) B1644983
theorem B2112463 : Blo 730325 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B2472929 : Blo 730325 2472929 := bstep (se 2 (by rfl) ⟨927348, by rfl⟩ : syracuseStep 2472929 = 1854697) B1854697
theorem B40647703 : Blo 730325 40647703 := bstep (se 1 (by rfl) ⟨30485777, by rfl⟩ : syracuseStep 40647703 = 60971555) B60971555
theorem B1096745 : Blo 730325 1096745 := bstep (se 2 (by rfl) ⟨411279, by rfl⟩ : syracuseStep 1096745 = 822559) B822559
theorem B1096751 : Blo 730325 1096751 := bstep (se 1 (by rfl) ⟨822563, by rfl⟩ : syracuseStep 1096751 = 1645127) B1645127
theorem B1096775 : Blo 730325 1096775 := bstep (se 1 (by rfl) ⟨822581, by rfl⟩ : syracuseStep 1096775 = 1645163) B1645163
theorem B4177079 : Blo 730325 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B2473145 : Blo 730325 2473145 := bstep (se 2 (by rfl) ⟨927429, by rfl⟩ : syracuseStep 2473145 = 1854859) B1854859
theorem B10042663 : Blo 730325 10042663 := bstep (se 1 (by rfl) ⟨7531997, by rfl⟩ : syracuseStep 10042663 = 15063995) B15063995
theorem B1097039 : Blo 730325 1097039 := bstep (se 1 (by rfl) ⟨822779, by rfl⟩ : syracuseStep 1097039 = 1645559) B1645559
theorem B1097129 : Blo 730325 1097129 := bstep (se 2 (by rfl) ⟨411423, by rfl⟩ : syracuseStep 1097129 = 822847) B822847
theorem B3128813 : Blo 730325 3128813 := bstep (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) B1173305
theorem B1097279 : Blo 730325 1097279 := bstep (se 1 (by rfl) ⟨822959, by rfl⟩ : syracuseStep 1097279 = 1645919) B1645919
theorem B1850971 : Blo 730325 1850971 := bstep (se 1 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 1850971 = 2776457) B2776457
theorem B1851113 : Blo 730325 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B1097543 : Blo 730325 1097543 := bstep (se 1 (by rfl) ⟨823157, by rfl⟩ : syracuseStep 1097543 = 1646315) B1646315
theorem B1097627 : Blo 730325 1097627 := bstep (se 1 (by rfl) ⟨823220, by rfl⟩ : syracuseStep 1097627 = 1646441) B1646441
theorem B2342945 : Blo 730325 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B20070433 : Blo 730325 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B11878487 : Blo 730325 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B1098191 : Blo 730325 1098191 := bstep (se 1 (by rfl) ⟨823643, by rfl⟩ : syracuseStep 1098191 = 1647287) B1647287
theorem B1098233 : Blo 730325 1098233 := bstep (se 2 (by rfl) ⟨411837, by rfl⟩ : syracuseStep 1098233 = 823675) B823675
theorem B1098335 : Blo 730325 1098335 := bstep (se 1 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 1098335 = 1647503) B1647503
theorem B2474603 : Blo 730325 2474603 := bstep (se 1 (by rfl) ⟨1855952, by rfl⟩ : syracuseStep 2474603 = 3711905) B3711905
theorem B2343599 : Blo 730325 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B1852217 : Blo 730325 1852217 := bstep (se 2 (by rfl) ⟨694581, by rfl⟩ : syracuseStep 1852217 = 1389163) B1389163
theorem B1098815 : Blo 730325 1098815 := bstep (se 1 (by rfl) ⟨824111, by rfl⟩ : syracuseStep 1098815 = 1648223) B1648223
theorem B1098857 : Blo 730325 1098857 := bstep (se 2 (by rfl) ⟨412071, by rfl⟩ : syracuseStep 1098857 = 824143) B824143
theorem B2475197 : Blo 730325 2475197 := bstep (se 3 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 2475197 = 928199) B928199
theorem B1098959 : Blo 730325 1098959 := bstep (se 1 (by rfl) ⟨824219, by rfl⟩ : syracuseStep 1098959 = 1648439) B1648439
theorem B4769027 : Blo 730325 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B2377067 : Blo 730325 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B1099163 : Blo 730325 1099163 := bstep (se 1 (by rfl) ⟨824372, by rfl⟩ : syracuseStep 1099163 = 1648745) B1648745
theorem B1099385 : Blo 730325 1099385 := bstep (se 2 (by rfl) ⟨412269, by rfl⟩ : syracuseStep 1099385 = 824539) B824539
theorem B1099487 : Blo 730325 1099487 := bstep (se 1 (by rfl) ⟨824615, by rfl⟩ : syracuseStep 1099487 = 1649231) B1649231
theorem B1099583 : Blo 730325 1099583 := bstep (se 1 (by rfl) ⟨824687, by rfl⟩ : syracuseStep 1099583 = 1649375) B1649375
theorem B1099751 : Blo 730325 1099751 := bstep (se 1 (by rfl) ⟨824813, by rfl⟩ : syracuseStep 1099751 = 1649627) B1649627
theorem B1099769 : Blo 730325 1099769 := bstep (se 2 (by rfl) ⟨412413, by rfl⟩ : syracuseStep 1099769 = 824827) B824827
theorem B1099871 : Blo 730325 1099871 := bstep (se 1 (by rfl) ⟨824903, by rfl⟩ : syracuseStep 1099871 = 1649807) B1649807
theorem B1099931 : Blo 730325 1099931 := bstep (se 1 (by rfl) ⟨824948, by rfl⟩ : syracuseStep 1099931 = 1649897) B1649897
theorem B1099967 : Blo 730325 1099967 := bstep (se 1 (by rfl) ⟨824975, by rfl⟩ : syracuseStep 1099967 = 1649951) B1649951
theorem B2476223 : Blo 730325 2476223 := bstep (se 1 (by rfl) ⟨1857167, by rfl⟩ : syracuseStep 2476223 = 3714335) B3714335
theorem B1100009 : Blo 730325 1100009 := bstep (se 2 (by rfl) ⟨412503, by rfl⟩ : syracuseStep 1100009 = 825007) B825007
theorem B1853675 : Blo 730325 1853675 := bstep (se 1 (by rfl) ⟨1390256, by rfl⟩ : syracuseStep 1853675 = 2780513) B2780513
theorem B1100315 : Blo 730325 1100315 := bstep (se 1 (by rfl) ⟨825236, by rfl⟩ : syracuseStep 1100315 = 1650473) B1650473
theorem B3951209 : Blo 730325 3951209 := bstep (se 2 (by rfl) ⟨1481703, by rfl⟩ : syracuseStep 3951209 = 2963407) B2963407
theorem B1100393 : Blo 730325 1100393 := bstep (se 2 (by rfl) ⟨412647, by rfl⟩ : syracuseStep 1100393 = 825295) B825295
theorem B5556923 : Blo 730325 5556923 := bstep (se 1 (by rfl) ⟨4167692, by rfl⟩ : syracuseStep 5556923 = 8335385) B8335385
theorem B2083961 : Blo 730325 2083961 := bstep (se 2 (by rfl) ⟨781485, by rfl⟩ : syracuseStep 2083961 = 1562971) B1562971
theorem B1100921 : Blo 730325 1100921 := bstep (se 2 (by rfl) ⟨412845, by rfl⟩ : syracuseStep 1100921 = 825691) B825691
theorem B1101023 : Blo 730325 1101023 := bstep (se 1 (by rfl) ⟨825767, by rfl⟩ : syracuseStep 1101023 = 1651535) B1651535
theorem B1101065 : Blo 730325 1101065 := bstep (se 2 (by rfl) ⟨412899, by rfl⟩ : syracuseStep 1101065 = 825799) B825799
theorem B1101167 : Blo 730325 1101167 := bstep (se 1 (by rfl) ⟨825875, by rfl⟩ : syracuseStep 1101167 = 1651751) B1651751
theorem B1101287 : Blo 730325 1101287 := bstep (se 1 (by rfl) ⟨825965, by rfl⟩ : syracuseStep 1101287 = 1651931) B1651931
theorem B2510327 : Blo 730325 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B1854971 : Blo 730325 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B1101419 : Blo 730325 1101419 := bstep (se 1 (by rfl) ⟨826064, by rfl⟩ : syracuseStep 1101419 = 1652129) B1652129
theorem B5557895 : Blo 730325 5557895 := bstep (se 1 (by rfl) ⟨4168421, by rfl⟩ : syracuseStep 5557895 = 8336843) B8336843
theorem B1232617 : Blo 730325 1232617 := bstep (se 2 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 1232617 = 924463) B924463
theorem B2477843 : Blo 730325 2477843 := bstep (se 1 (by rfl) ⟨1858382, by rfl⟩ : syracuseStep 2477843 = 3716765) B3716765
theorem B7917385 : Blo 730325 7917385 := bstep (se 2 (by rfl) ⟨2969019, by rfl⟩ : syracuseStep 7917385 = 5938039) B5938039
theorem B2674873 : Blo 730325 2674873 := bstep (se 2 (by rfl) ⟨1003077, by rfl⟩ : syracuseStep 2674873 = 2006155) B2006155
theorem B1233083 : Blo 730325 1233083 := bstep (se 1 (by rfl) ⟨924812, by rfl⟩ : syracuseStep 1233083 = 1849625) B1849625
theorem B9392435 : Blo 730325 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B1855993 : Blo 730325 1855993 := bstep (se 2 (by rfl) ⟨695997, by rfl⟩ : syracuseStep 1855993 = 1391995) B1391995
theorem B5001851 : Blo 730325 5001851 := bstep (se 1 (by rfl) ⟨3751388, by rfl⟩ : syracuseStep 5001851 = 7502777) B7502777
theorem B1233643 : Blo 730325 1233643 := bstep (se 1 (by rfl) ⟨925232, by rfl⟩ : syracuseStep 1233643 = 1850465) B1850465
theorem B1856297 : Blo 730325 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B1561655 : Blo 730325 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B1561673 : Blo 730325 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B3134639 : Blo 730325 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B1234615 : Blo 730325 1234615 := bstep (se 1 (by rfl) ⟨925961, by rfl⟩ : syracuseStep 1234615 = 1851923) B1851923
theorem B64149205 : Blo 730325 64149205 := bstep (se 7 (by rfl) ⟨751748, by rfl⟩ : syracuseStep 64149205 = 1503497) B1503497
theorem B2381705 : Blo 730325 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B2774999 : Blo 730325 2774999 := bstep (se 1 (by rfl) ⟨2081249, by rfl⟩ : syracuseStep 2774999 = 4162499) B4162499
theorem B1234919 : Blo 730325 1234919 := bstep (se 1 (by rfl) ⟨926189, by rfl⟩ : syracuseStep 1234919 = 1852379) B1852379
theorem B2643943 : Blo 730325 2643943 := bstep (se 1 (by rfl) ⟨1982957, by rfl⟩ : syracuseStep 2643943 = 3965915) B3965915
theorem B3528679 : Blo 730325 3528679 := bstep (se 1 (by rfl) ⟨2646509, by rfl⟩ : syracuseStep 3528679 = 5293019) B5293019
theorem B1235135 : Blo 730325 1235135 := bstep (se 1 (by rfl) ⟨926351, by rfl⟩ : syracuseStep 1235135 = 1852703) B1852703
theorem B2775485 : Blo 730325 2775485 := bstep (se 3 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 2775485 = 1040807) B1040807
theorem B102816289 : Blo 730325 102816289 := bstep (se 2 (by rfl) ⟨38556108, by rfl⟩ : syracuseStep 102816289 = 77112217) B77112217
theorem B3169115 : Blo 730325 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B1235803 : Blo 730325 1235803 := bstep (se 1 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 1235803 = 1853705) B1853705
theorem B3136637 : Blo 730325 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B2088119 : Blo 730325 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B4021433 : Blo 730325 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B1564115 : Blo 730325 1564115 := bstep (se 1 (by rfl) ⟨1173086, by rfl⟩ : syracuseStep 1564115 = 2346173) B2346173
theorem B1236775 : Blo 730325 1236775 := bstep (se 1 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 1236775 = 1855163) B1855163
theorem B1040249 : Blo 730325 1040249 := bstep (se 2 (by rfl) ⟨390093, by rfl⟩ : syracuseStep 1040249 = 780187) B780187
theorem B5562269 : Blo 730325 5562269 := bstep (se 3 (by rfl) ⟨1042925, by rfl⟩ : syracuseStep 5562269 = 2085851) B2085851
theorem B1761419 : Blo 730325 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B3760415 : Blo 730325 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B1237801 : Blo 730325 1237801 := bstep (se 2 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 1237801 = 928351) B928351
theorem B3957659 : Blo 730325 3957659 := bstep (se 1 (by rfl) ⟨2968244, by rfl⟩ : syracuseStep 3957659 = 5936489) B5936489
theorem B10576925 : Blo 730325 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B1238071 : Blo 730325 1238071 := bstep (se 1 (by rfl) ⟨928553, by rfl⟩ : syracuseStep 1238071 = 1857107) B1857107
theorem B1173113 : Blo 730325 1173113 := bstep (se 2 (by rfl) ⟨439917, by rfl⟩ : syracuseStep 1173113 = 879835) B879835
theorem B1762937 : Blo 730325 1762937 := bstep (se 2 (by rfl) ⟨661101, by rfl⟩ : syracuseStep 1762937 = 1322203) B1322203
theorem B2778887 : Blo 730325 2778887 := bstep (se 1 (by rfl) ⟨2084165, by rfl⟩ : syracuseStep 2778887 = 4168331) B4168331
theorem B3172297 : Blo 730325 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B1239023 : Blo 730325 1239023 := bstep (se 1 (by rfl) ⟨929267, by rfl⟩ : syracuseStep 1239023 = 1858535) B1858535
theorem B3565721 : Blo 730325 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B9366191 : Blo 730325 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B3566891 : Blo 730325 3566891 := bstep (se 1 (by rfl) ⟨2675168, by rfl⟩ : syracuseStep 3566891 = 5350337) B5350337
theorem B1044031 : Blo 730325 1044031 := bstep (se 1 (by rfl) ⟨783023, by rfl⟩ : syracuseStep 1044031 = 1566047) B1566047
theorem B3665533 : Blo 730325 3665533 := bstep (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) B1374575
theorem B1175419 : Blo 730325 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B8319347 : Blo 730325 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B4518287 : Blo 730325 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B1405433 : Blo 730325 1405433 := bstep (se 2 (by rfl) ⟨527037, by rfl⟩ : syracuseStep 1405433 = 1054075) B1054075
theorem B1405601 : Blo 730325 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B12514013 : Blo 730325 12514013 := bstep (se 3 (by rfl) ⟨2346377, by rfl⟩ : syracuseStep 12514013 = 4692755) B4692755
theorem B783271 : Blo 730325 783271 := bstep (se 1 (by rfl) ⟨587453, by rfl⟩ : syracuseStep 783271 = 1174907) B1174907
theorem B881771 : Blo 730325 881771 := bstep (se 1 (by rfl) ⟨661328, by rfl⟩ : syracuseStep 881771 = 1322657) B1322657
theorem B6354227 : Blo 730325 6354227 := bstep (se 1 (by rfl) ⟨4765670, by rfl⟩ : syracuseStep 6354227 = 9531341) B9531341
theorem B5633545 : Blo 730325 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B7141067 : Blo 730325 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B784091 : Blo 730325 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B1112057 : Blo 730325 1112057 := bstep (se 2 (by rfl) ⟨417021, by rfl⟩ : syracuseStep 1112057 = 834043) B834043
theorem B11892815 : Blo 730325 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B7338887 : Blo 730325 7338887 := bstep (se 1 (by rfl) ⟨5504165, by rfl⟩ : syracuseStep 7338887 = 11008331) B11008331
theorem B9371159 : Blo 730325 9371159 := bstep (se 1 (by rfl) ⟨7028369, by rfl⟩ : syracuseStep 9371159 = 14056739) B14056739
theorem B1113979 : Blo 730325 1113979 := bstep (se 1 (by rfl) ⟨835484, by rfl⟩ : syracuseStep 1113979 = 1670969) B1670969
theorem B2228093 : Blo 730325 2228093 := bstep (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) B835535
theorem B5341099 : Blo 730325 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B3179351 : Blo 730325 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B3703805 : Blo 730325 3703805 := bstep (se 3 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 3703805 = 1388927) B1388927
theorem B9405557 : Blo 730325 9405557 := bstep (se 5 (by rfl) ⟨440885, by rfl⟩ : syracuseStep 9405557 = 881771) B881771
theorem B11273363 : Blo 730325 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B5867113 : Blo 730325 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B3704615 : Blo 730325 3704615 := bstep (se 1 (by rfl) ⟨2778461, by rfl⟩ : syracuseStep 3704615 = 5556923) B5556923
theorem B9406529 : Blo 730325 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B8915131 : Blo 730325 8915131 := bstep (se 1 (by rfl) ⟨6686348, by rfl⟩ : syracuseStep 8915131 = 13372697) B13372697
theorem B1673551 : Blo 730325 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B3705263 : Blo 730325 3705263 := bstep (se 1 (by rfl) ⟨2778947, by rfl⟩ : syracuseStep 3705263 = 5557895) B5557895
theorem B4229729 : Blo 730325 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B822055 : Blo 730325 822055 := bstep (se 1 (by rfl) ⟨616541, by rfl⟩ : syracuseStep 822055 = 1233083) B1233083
theorem B6261623 : Blo 730325 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B3345803 : Blo 730325 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B823279 : Blo 730325 823279 := bstep (se 1 (by rfl) ⟨617459, by rfl⟩ : syracuseStep 823279 = 1234919) B1234919
theorem B3346535 : Blo 730325 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B823423 : Blo 730325 823423 := bstep (se 1 (by rfl) ⟨617567, by rfl⟩ : syracuseStep 823423 = 1235135) B1235135
theorem B4887377 : Blo 730325 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B8328095 : Blo 730325 8328095 := bstep (se 1 (by rfl) ⟨6246071, by rfl⟩ : syracuseStep 8328095 = 12492143) B12492143
theorem B1643489 : Blo 730325 1643489 := bstep (se 2 (by rfl) ⟨616308, by rfl⟩ : syracuseStep 1643489 = 1232617) B1232617
theorem B1643615 : Blo 730325 1643615 := bstep (se 1 (by rfl) ⟨1232711, by rfl⟩ : syracuseStep 1643615 = 2465423) B2465423
theorem B10556513 : Blo 730325 10556513 := bstep (se 2 (by rfl) ⟨3958692, by rfl⟩ : syracuseStep 10556513 = 7917385) B7917385
theorem B3511457 : Blo 730325 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B3708179 : Blo 730325 3708179 := bstep (se 1 (by rfl) ⟨2781134, by rfl⟩ : syracuseStep 3708179 = 5562269) B5562269
theorem B3347773 : Blo 730325 3347773 := bstep (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) B1255415
theorem B1316335 : Blo 730325 1316335 := bstep (se 1 (by rfl) ⟨987251, by rfl⟩ : syracuseStep 1316335 = 1974503) B1974503
theorem B3348179 : Blo 730325 3348179 := bstep (se 1 (by rfl) ⟨2511134, by rfl⟩ : syracuseStep 3348179 = 5022269) B5022269
theorem B1644371 : Blo 730325 1644371 := bstep (se 1 (by rfl) ⟨1233278, by rfl⟩ : syracuseStep 1644371 = 2466557) B2466557
theorem B7051283 : Blo 730325 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B1644857 : Blo 730325 1644857 := bstep (se 2 (by rfl) ⟨616821, by rfl⟩ : syracuseStep 1644857 = 1233643) B1233643
theorem B826015 : Blo 730325 826015 := bstep (se 1 (by rfl) ⟨619511, by rfl⟩ : syracuseStep 826015 = 1239023) B1239023
theorem B7019723 : Blo 730325 7019723 := bstep (se 1 (by rfl) ⟨5264792, by rfl⟩ : syracuseStep 7019723 = 10529585) B10529585
theorem B1645775 : Blo 730325 1645775 := bstep (se 1 (by rfl) ⟨1234331, by rfl⟩ : syracuseStep 1645775 = 2468663) B2468663
theorem B7511393 : Blo 730325 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B3120713 : Blo 730325 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B1646153 : Blo 730325 1646153 := bstep (se 2 (by rfl) ⟨617307, by rfl⟩ : syracuseStep 1646153 = 1234615) B1234615
theorem B85532273 : Blo 730325 85532273 := bstep (se 2 (by rfl) ⟨32074602, by rfl⟩ : syracuseStep 85532273 = 64149205) B64149205
theorem B15802067 : Blo 730325 15802067 := bstep (se 1 (by rfl) ⟨11851550, by rfl⟩ : syracuseStep 15802067 = 23703101) B23703101
theorem B5546231 : Blo 730325 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B3809603 : Blo 730325 3809603 := bstep (se 1 (by rfl) ⟨2857202, by rfl⟩ : syracuseStep 3809603 = 5714405) B5714405
theorem B1647323 : Blo 730325 1647323 := bstep (se 1 (by rfl) ⟨1235492, by rfl⟩ : syracuseStep 1647323 = 2470985) B2470985
theorem B4236151 : Blo 730325 4236151 := bstep (se 1 (by rfl) ⟨3177113, by rfl⟩ : syracuseStep 4236151 = 6354227) B6354227
theorem B6693799 : Blo 730325 6693799 := bstep (se 1 (by rfl) ⟨5020349, by rfl⟩ : syracuseStep 6693799 = 10040699) B10040699
theorem B8004595 : Blo 730325 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B1647737 : Blo 730325 1647737 := bstep (se 2 (by rfl) ⟨617901, by rfl⟩ : syracuseStep 1647737 = 1235803) B1235803
theorem B4760711 : Blo 730325 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B4170973 : Blo 730325 4170973 := bstep (se 3 (by rfl) ⟨782057, by rfl⟩ : syracuseStep 4170973 = 1564115) B1564115
theorem B730335 : Blo 730325 730335 := bstep (se 1 (by rfl) ⟨547751, by rfl⟩ : syracuseStep 730335 = 1095503) B1095503
theorem B730415 : Blo 730325 730415 := bstep (se 1 (by rfl) ⟨547811, by rfl⟩ : syracuseStep 730415 = 1095623) B1095623
theorem B25404853 : Blo 730325 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B730651 : Blo 730325 730651 := bstep (se 1 (by rfl) ⟨547988, by rfl⟩ : syracuseStep 730651 = 1095977) B1095977
theorem B730655 : Blo 730325 730655 := bstep (se 1 (by rfl) ⟨547991, by rfl⟩ : syracuseStep 730655 = 1095983) B1095983
theorem B730815 : Blo 730325 730815 := bstep (se 1 (by rfl) ⟨548111, by rfl⟩ : syracuseStep 730815 = 1096223) B1096223
theorem B1648403 : Blo 730325 1648403 := bstep (se 1 (by rfl) ⟨1236302, by rfl⟩ : syracuseStep 1648403 = 2472605) B2472605
theorem B4892591 : Blo 730325 4892591 := bstep (se 1 (by rfl) ⟨3669443, by rfl⟩ : syracuseStep 4892591 = 7338887) B7338887
theorem B731071 : Blo 730325 731071 := bstep (se 1 (by rfl) ⟨548303, by rfl⟩ : syracuseStep 731071 = 1096607) B1096607
theorem B731103 : Blo 730325 731103 := bstep (se 1 (by rfl) ⟨548327, by rfl⟩ : syracuseStep 731103 = 1096655) B1096655
theorem B1648619 : Blo 730325 1648619 := bstep (se 1 (by rfl) ⟨1236464, by rfl⟩ : syracuseStep 1648619 = 2472929) B2472929
theorem B731163 : Blo 730325 731163 := bstep (se 1 (by rfl) ⟨548372, by rfl⟩ : syracuseStep 731163 = 1096745) B1096745
theorem B731167 : Blo 730325 731167 := bstep (se 1 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 731167 = 1096751) B1096751
theorem B731183 : Blo 730325 731183 := bstep (se 1 (by rfl) ⟨548387, by rfl⟩ : syracuseStep 731183 = 1096775) B1096775
theorem B2467961 : Blo 730325 2467961 := bstep (se 2 (by rfl) ⟨925485, by rfl⟩ : syracuseStep 2467961 = 1850971) B1850971
theorem B1648763 : Blo 730325 1648763 := bstep (se 1 (by rfl) ⟨1236572, by rfl⟩ : syracuseStep 1648763 = 2473145) B2473145
theorem B731359 : Blo 730325 731359 := bstep (se 1 (by rfl) ⟨548519, by rfl⟩ : syracuseStep 731359 = 1097039) B1097039
theorem B731419 : Blo 730325 731419 := bstep (se 1 (by rfl) ⟨548564, by rfl⟩ : syracuseStep 731419 = 1097129) B1097129
theorem B731519 : Blo 730325 731519 := bstep (se 1 (by rfl) ⟨548639, by rfl⟩ : syracuseStep 731519 = 1097279) B1097279
theorem B1649033 : Blo 730325 1649033 := bstep (se 2 (by rfl) ⟨618387, by rfl⟩ : syracuseStep 1649033 = 1236775) B1236775
theorem B1485305 : Blo 730325 1485305 := bstep (se 2 (by rfl) ⟨556989, by rfl⟩ : syracuseStep 1485305 = 1113979) B1113979
theorem B731695 : Blo 730325 731695 := bstep (se 1 (by rfl) ⟨548771, by rfl⟩ : syracuseStep 731695 = 1097543) B1097543
theorem B7121465 : Blo 730325 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B1485395 : Blo 730325 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B731751 : Blo 730325 731751 := bstep (se 1 (by rfl) ⟨548813, by rfl⟩ : syracuseStep 731751 = 1097627) B1097627
theorem B732127 : Blo 730325 732127 := bstep (se 1 (by rfl) ⟨549095, by rfl⟩ : syracuseStep 732127 = 1098191) B1098191
theorem B3517415 : Blo 730325 3517415 := bstep (se 1 (by rfl) ⟨2638061, by rfl⟩ : syracuseStep 3517415 = 5276123) B5276123
theorem B732155 : Blo 730325 732155 := bstep (se 1 (by rfl) ⟨549116, by rfl⟩ : syracuseStep 732155 = 1098233) B1098233
theorem B732223 : Blo 730325 732223 := bstep (se 1 (by rfl) ⟨549167, by rfl⟩ : syracuseStep 732223 = 1098335) B1098335
theorem B1649735 : Blo 730325 1649735 := bstep (se 1 (by rfl) ⟨1237301, by rfl⟩ : syracuseStep 1649735 = 2474603) B2474603
theorem B732543 : Blo 730325 732543 := bstep (se 1 (by rfl) ⟨549407, by rfl⟩ : syracuseStep 732543 = 1098815) B1098815
theorem B732571 : Blo 730325 732571 := bstep (se 1 (by rfl) ⟨549428, by rfl⟩ : syracuseStep 732571 = 1098857) B1098857
theorem B1650131 : Blo 730325 1650131 := bstep (se 1 (by rfl) ⟨1237598, by rfl⟩ : syracuseStep 1650131 = 2475197) B2475197
theorem B732639 : Blo 730325 732639 := bstep (se 1 (by rfl) ⟨549479, by rfl⟩ : syracuseStep 732639 = 1098959) B1098959
theorem B732775 : Blo 730325 732775 := bstep (se 1 (by rfl) ⟨549581, by rfl⟩ : syracuseStep 732775 = 1099163) B1099163
theorem B1650401 : Blo 730325 1650401 := bstep (se 2 (by rfl) ⟨618900, by rfl⟩ : syracuseStep 1650401 = 1237801) B1237801
theorem B2502377 : Blo 730325 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B732923 : Blo 730325 732923 := bstep (se 1 (by rfl) ⟨549692, by rfl⟩ : syracuseStep 732923 = 1099385) B1099385
theorem B732991 : Blo 730325 732991 := bstep (se 1 (by rfl) ⟨549743, by rfl⟩ : syracuseStep 732991 = 1099487) B1099487
theorem B733055 : Blo 730325 733055 := bstep (se 1 (by rfl) ⟨549791, by rfl⟩ : syracuseStep 733055 = 1099583) B1099583
theorem B733167 : Blo 730325 733167 := bstep (se 1 (by rfl) ⟨549875, by rfl⟩ : syracuseStep 733167 = 1099751) B1099751
theorem B733179 : Blo 730325 733179 := bstep (se 1 (by rfl) ⟨549884, by rfl⟩ : syracuseStep 733179 = 1099769) B1099769
theorem B733247 : Blo 730325 733247 := bstep (se 1 (by rfl) ⟨549935, by rfl⟩ : syracuseStep 733247 = 1099871) B1099871
theorem B1650761 : Blo 730325 1650761 := bstep (se 2 (by rfl) ⟨619035, by rfl⟩ : syracuseStep 1650761 = 1238071) B1238071
theorem B733287 : Blo 730325 733287 := bstep (se 1 (by rfl) ⟨549965, by rfl⟩ : syracuseStep 733287 = 1099931) B1099931
theorem B733311 : Blo 730325 733311 := bstep (se 1 (by rfl) ⟨549983, by rfl⟩ : syracuseStep 733311 = 1099967) B1099967
theorem B1650815 : Blo 730325 1650815 := bstep (se 1 (by rfl) ⟨1238111, by rfl⟩ : syracuseStep 1650815 = 2476223) B2476223
theorem B733339 : Blo 730325 733339 := bstep (se 1 (by rfl) ⟨550004, by rfl⟩ : syracuseStep 733339 = 1100009) B1100009
theorem B733543 : Blo 730325 733543 := bstep (se 1 (by rfl) ⟨550157, by rfl⟩ : syracuseStep 733543 = 1100315) B1100315
theorem B2634139 : Blo 730325 2634139 := bstep (se 1 (by rfl) ⟨1975604, by rfl⟩ : syracuseStep 2634139 = 3951209) B3951209
theorem B733595 : Blo 730325 733595 := bstep (se 1 (by rfl) ⟨550196, by rfl⟩ : syracuseStep 733595 = 1100393) B1100393
theorem B1389307 : Blo 730325 1389307 := bstep (se 1 (by rfl) ⟨1041980, by rfl⟩ : syracuseStep 1389307 = 2083961) B2083961
theorem B733947 : Blo 730325 733947 := bstep (se 1 (by rfl) ⟨550460, by rfl⟩ : syracuseStep 733947 = 1100921) B1100921
theorem B734015 : Blo 730325 734015 := bstep (se 1 (by rfl) ⟨550511, by rfl⟩ : syracuseStep 734015 = 1101023) B1101023
theorem B734043 : Blo 730325 734043 := bstep (se 1 (by rfl) ⟨550532, by rfl⟩ : syracuseStep 734043 = 1101065) B1101065
theorem B734111 : Blo 730325 734111 := bstep (se 1 (by rfl) ⟨550583, by rfl⟩ : syracuseStep 734111 = 1101167) B1101167
theorem B2470823 : Blo 730325 2470823 := bstep (se 1 (by rfl) ⟨1853117, by rfl⟩ : syracuseStep 2470823 = 3706235) B3706235
theorem B734191 : Blo 730325 734191 := bstep (se 1 (by rfl) ⟨550643, by rfl⟩ : syracuseStep 734191 = 1101287) B1101287
theorem B734279 : Blo 730325 734279 := bstep (se 1 (by rfl) ⟨550709, by rfl⟩ : syracuseStep 734279 = 1101419) B1101419
theorem B1979497 : Blo 730325 1979497 := bstep (se 2 (by rfl) ⟨742311, by rfl⟩ : syracuseStep 1979497 = 1484623) B1484623
theorem B1651895 : Blo 730325 1651895 := bstep (se 1 (by rfl) ⟨1238921, by rfl⟩ : syracuseStep 1651895 = 2477843) B2477843
theorem B1488191 : Blo 730325 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B1095863 : Blo 730325 1095863 := bstep (se 1 (by rfl) ⟨821897, by rfl⟩ : syracuseStep 1095863 = 1643795) B1643795
theorem B1095911 : Blo 730325 1095911 := bstep (se 1 (by rfl) ⟨821933, by rfl⟩ : syracuseStep 1095911 = 1643867) B1643867
theorem B3127531 : Blo 730325 3127531 := bstep (se 1 (by rfl) ⟨2345648, by rfl⟩ : syracuseStep 3127531 = 4691297) B4691297
theorem B6338845 : Blo 730325 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1096283 : Blo 730325 1096283 := bstep (se 1 (by rfl) ⟨822212, by rfl⟩ : syracuseStep 1096283 = 1644425) B1644425
theorem B1849999 : Blo 730325 1849999 := bstep (se 1 (by rfl) ⟨1387499, by rfl⟩ : syracuseStep 1849999 = 2774999) B2774999
theorem B10533563 : Blo 730325 10533563 := bstep (se 1 (by rfl) ⟨7900172, by rfl⟩ : syracuseStep 10533563 = 15800345) B15800345
theorem B1096427 : Blo 730325 1096427 := bstep (se 1 (by rfl) ⟨822320, by rfl⟩ : syracuseStep 1096427 = 1644641) B1644641
theorem B1096457 : Blo 730325 1096457 := bstep (se 2 (by rfl) ⟨411171, by rfl⟩ : syracuseStep 1096457 = 822343) B822343
theorem B1850323 : Blo 730325 1850323 := bstep (se 1 (by rfl) ⟨1387742, by rfl⟩ : syracuseStep 1850323 = 2775485) B2775485
theorem B2112743 : Blo 730325 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B2342267 : Blo 730325 2342267 := bstep (se 1 (by rfl) ⟨1756700, by rfl⟩ : syracuseStep 2342267 = 3513401) B3513401
theorem B1392041 : Blo 730325 1392041 := bstep (se 2 (by rfl) ⟨522015, by rfl⟩ : syracuseStep 1392041 = 1044031) B1044031
theorem B1392079 : Blo 730325 1392079 := bstep (se 1 (by rfl) ⟨1044059, by rfl⟩ : syracuseStep 1392079 = 2088119) B2088119
theorem B2473469 : Blo 730325 2473469 := bstep (se 3 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 2473469 = 927551) B927551
theorem B1097327 : Blo 730325 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B1097447 : Blo 730325 1097447 := bstep (se 1 (by rfl) ⟨823085, by rfl⟩ : syracuseStep 1097447 = 1646171) B1646171
theorem B1097639 : Blo 730325 1097639 := bstep (se 1 (by rfl) ⟨823229, by rfl⟩ : syracuseStep 1097639 = 1646459) B1646459
theorem B2506943 : Blo 730325 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1097963 : Blo 730325 1097963 := bstep (se 1 (by rfl) ⟨823472, by rfl⟩ : syracuseStep 1097963 = 1646945) B1646945
theorem B1098023 : Blo 730325 1098023 := bstep (se 1 (by rfl) ⟨823517, by rfl⟩ : syracuseStep 1098023 = 1647035) B1647035
theorem B2474279 : Blo 730325 2474279 := bstep (se 1 (by rfl) ⟨1855709, by rfl⟩ : syracuseStep 2474279 = 3711419) B3711419
theorem B2343431 : Blo 730325 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B2638439 : Blo 730325 2638439 := bstep (se 1 (by rfl) ⟨1978829, by rfl⟩ : syracuseStep 2638439 = 3957659) B3957659
theorem B8929925 : Blo 730325 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B2474657 : Blo 730325 2474657 := bstep (se 2 (by rfl) ⟨927996, by rfl⟩ : syracuseStep 2474657 = 1855993) B1855993
theorem B1098695 : Blo 730325 1098695 := bstep (se 1 (by rfl) ⟨824021, by rfl⟩ : syracuseStep 1098695 = 1648043) B1648043
theorem B1098863 : Blo 730325 1098863 := bstep (se 1 (by rfl) ⟨824147, by rfl⟩ : syracuseStep 1098863 = 1648295) B1648295
theorem B1852591 : Blo 730325 1852591 := bstep (se 1 (by rfl) ⟨1389443, by rfl⟩ : syracuseStep 1852591 = 2778887) B2778887
theorem B1099055 : Blo 730325 1099055 := bstep (se 1 (by rfl) ⟨824291, by rfl⟩ : syracuseStep 1099055 = 1648583) B1648583
theorem B2377147 : Blo 730325 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B1099259 : Blo 730325 1099259 := bstep (se 1 (by rfl) ⟨824444, by rfl⟩ : syracuseStep 1099259 = 1648889) B1648889
theorem B1099295 : Blo 730325 1099295 := bstep (se 1 (by rfl) ⟨824471, by rfl⟩ : syracuseStep 1099295 = 1648943) B1648943
theorem B1099439 : Blo 730325 1099439 := bstep (se 1 (by rfl) ⟨824579, by rfl⟩ : syracuseStep 1099439 = 1649159) B1649159
theorem B6244127 : Blo 730325 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B1099559 : Blo 730325 1099559 := bstep (se 1 (by rfl) ⟨824669, by rfl⟩ : syracuseStep 1099559 = 1649339) B1649339
theorem B2476007 : Blo 730325 2476007 := bstep (se 1 (by rfl) ⟨1857005, by rfl⟩ : syracuseStep 2476007 = 3714011) B3714011
theorem B2377927 : Blo 730325 2377927 := bstep (se 1 (by rfl) ⟨1783445, by rfl⟩ : syracuseStep 2377927 = 3566891) B3566891
theorem B1100111 : Blo 730325 1100111 := bstep (se 1 (by rfl) ⟨825083, by rfl⟩ : syracuseStep 1100111 = 1650167) B1650167
theorem B1100159 : Blo 730325 1100159 := bstep (se 1 (by rfl) ⟨825119, by rfl⟩ : syracuseStep 1100159 = 1650239) B1650239
theorem B1100201 : Blo 730325 1100201 := bstep (se 2 (by rfl) ⟨412575, by rfl⟩ : syracuseStep 1100201 = 825151) B825151
theorem B3525257 : Blo 730325 3525257 := bstep (se 2 (by rfl) ⟨1321971, by rfl⟩ : syracuseStep 3525257 = 2643943) B2643943
theorem B4704905 : Blo 730325 4704905 := bstep (se 2 (by rfl) ⟨1764339, by rfl⟩ : syracuseStep 4704905 = 3528679) B3528679
theorem B1100585 : Blo 730325 1100585 := bstep (se 2 (by rfl) ⟨412719, by rfl⟩ : syracuseStep 1100585 = 825439) B825439
theorem B4442971 : Blo 730325 4442971 := bstep (se 1 (by rfl) ⟨3332228, by rfl⟩ : syracuseStep 4442971 = 6664457) B6664457
theorem B936955 : Blo 730325 936955 := bstep (se 1 (by rfl) ⟨702716, by rfl⟩ : syracuseStep 936955 = 1405433) B1405433
theorem B10144763 : Blo 730325 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B1100795 : Blo 730325 1100795 := bstep (se 1 (by rfl) ⟨825596, by rfl⟩ : syracuseStep 1100795 = 1651193) B1651193
theorem B1100855 : Blo 730325 1100855 := bstep (se 1 (by rfl) ⟨825641, by rfl⟩ : syracuseStep 1100855 = 1651283) B1651283
theorem B937067 : Blo 730325 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B8342675 : Blo 730325 8342675 := bstep (se 1 (by rfl) ⟨6257006, by rfl⟩ : syracuseStep 8342675 = 12514013) B12514013
theorem B1100975 : Blo 730325 1100975 := bstep (se 1 (by rfl) ⟨825731, by rfl⟩ : syracuseStep 1100975 = 1651463) B1651463
theorem B5950687 : Blo 730325 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B137088385 : Blo 730325 137088385 := bstep (se 2 (by rfl) ⟨51408144, by rfl⟩ : syracuseStep 137088385 = 102816289) B102816289
theorem B9359063 : Blo 730325 9359063 := bstep (se 1 (by rfl) ⟨7019297, by rfl⟩ : syracuseStep 9359063 = 14038595) B14038595
theorem B2477951 : Blo 730325 2477951 := bstep (se 1 (by rfl) ⟨1858463, by rfl⟩ : syracuseStep 2477951 = 3716927) B3716927
theorem B741371 : Blo 730325 741371 := bstep (se 1 (by rfl) ⟨556028, by rfl⟩ : syracuseStep 741371 = 1112057) B1112057
theorem B13390217 : Blo 730325 13390217 := bstep (se 2 (by rfl) ⟨5021331, by rfl⟩ : syracuseStep 13390217 = 10042663) B10042663
theorem B2773997 : Blo 730325 2773997 := bstep (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) B1040249
theorem B2085875 : Blo 730325 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B6247439 : Blo 730325 6247439 := bstep (se 1 (by rfl) ⟨4685579, by rfl⟩ : syracuseStep 6247439 = 9371159) B9371159
theorem B1234075 : Blo 730325 1234075 := bstep (se 1 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 1234075 = 1851113) B1851113
theorem B5625085 : Blo 730325 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B1234217 : Blo 730325 1234217 := bstep (se 2 (by rfl) ⟨462831, by rfl⟩ : syracuseStep 1234217 = 925663) B925663
theorem B1561963 : Blo 730325 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B26760577 : Blo 730325 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B7918991 : Blo 730325 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B2774695 : Blo 730325 2774695 := bstep (se 1 (by rfl) ⟨2081021, by rfl⟩ : syracuseStep 2774695 = 4162043) B4162043
theorem B1562399 : Blo 730325 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B1234811 : Blo 730325 1234811 := bstep (se 1 (by rfl) ⟨926108, by rfl⟩ : syracuseStep 1234811 = 1852217) B1852217
theorem B1267849 : Blo 730325 1267849 := bstep (se 2 (by rfl) ⟨475443, by rfl⟩ : syracuseStep 1267849 = 950887) B950887
theorem B1235081 : Blo 730325 1235081 := bstep (se 2 (by rfl) ⟨463155, by rfl⟩ : syracuseStep 1235081 = 926311) B926311
theorem B1857755 : Blo 730325 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B12540257 : Blo 730325 12540257 := bstep (se 2 (by rfl) ⟨4702596, by rfl⟩ : syracuseStep 12540257 = 9405193) B9405193
theorem B2775455 : Blo 730325 2775455 := bstep (se 1 (by rfl) ⟨2081591, by rfl⟩ : syracuseStep 2775455 = 4163183) B4163183
theorem B1235783 : Blo 730325 1235783 := bstep (se 1 (by rfl) ⟨926837, by rfl⟩ : syracuseStep 1235783 = 1853675) B1853675
theorem B2776427 : Blo 730325 2776427 := bstep (se 1 (by rfl) ⟨2082320, by rfl⟩ : syracuseStep 2776427 = 4164641) B4164641
theorem B1236647 : Blo 730325 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B2776943 : Blo 730325 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B5005567 : Blo 730325 5005567 := bstep (se 1 (by rfl) ⟨3754175, by rfl⟩ : syracuseStep 5005567 = 7508351) B7508351
theorem B1761697 : Blo 730325 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B3334567 : Blo 730325 3334567 := bstep (se 1 (by rfl) ⟨2500925, by rfl⟩ : syracuseStep 3334567 = 5001851) B5001851
theorem B1237531 : Blo 730325 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B1041103 : Blo 730325 1041103 := bstep (se 1 (by rfl) ⟨780827, by rfl⟩ : syracuseStep 1041103 = 1561655) B1561655
theorem B1041115 : Blo 730325 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B2089759 : Blo 730325 2089759 := bstep (se 1 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 2089759 = 3134639) B3134639
theorem B2778583 : Blo 730325 2778583 := bstep (se 1 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 2778583 = 4167875) B4167875
theorem B2090909 : Blo 730325 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B2091091 : Blo 730325 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B2680955 : Blo 730325 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B1567225 : Blo 730325 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B1174279 : Blo 730325 1174279 := bstep (se 1 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 1174279 = 1761419) B1761419
theorem B3566497 : Blo 730325 3566497 := bstep (se 2 (by rfl) ⟨1337436, by rfl⟩ : syracuseStep 3566497 = 2674873) B2674873
theorem B7040135 : Blo 730325 7040135 := bstep (se 1 (by rfl) ⟨5280101, by rfl⟩ : syracuseStep 7040135 = 10560203) B10560203
theorem B3173855 : Blo 730325 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B782075 : Blo 730325 782075 := bstep (se 1 (by rfl) ⟨586556, by rfl⟩ : syracuseStep 782075 = 1173113) B1173113
theorem B1175291 : Blo 730325 1175291 := bstep (se 1 (by rfl) ⟨881468, by rfl⟩ : syracuseStep 1175291 = 1762937) B1762937
theorem B1044361 : Blo 730325 1044361 := bstep (se 2 (by rfl) ⟨391635, by rfl⟩ : syracuseStep 1044361 = 783271) B783271
theorem B21458843 : Blo 730325 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B2782471 : Blo 730325 2782471 := bstep (se 1 (by rfl) ⟨2086853, by rfl⟩ : syracuseStep 2782471 = 4173707) B4173707
theorem B1668563 : Blo 730325 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B3012191 : Blo 730325 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B11859857 : Blo 730325 11859857 := bstep (se 2 (by rfl) ⟨4447446, by rfl⟩ : syracuseStep 11859857 = 8894893) B8894893
theorem B2783443 : Blo 730325 2783443 := bstep (se 1 (by rfl) ⟨2087582, by rfl⟩ : syracuseStep 2783443 = 4175165) B4175165
theorem B5569073 : Blo 730325 5569073 := bstep (se 2 (by rfl) ⟨2088402, by rfl⟩ : syracuseStep 5569073 = 4176805) B4176805
theorem B6257249 : Blo 730325 6257249 := bstep (se 2 (by rfl) ⟨2346468, by rfl⟩ : syracuseStep 6257249 = 4692937) B4692937
theorem B2816617 : Blo 730325 2816617 := bstep (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) B2112463
theorem B54196937 : Blo 730325 54196937 := bstep (se 2 (by rfl) ⟨20323851, by rfl⟩ : syracuseStep 54196937 = 40647703) B40647703
theorem B7928543 : Blo 730325 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B12483395 : Blo 730325 12483395 := bstep (se 1 (by rfl) ⟨9362546, by rfl⟩ : syracuseStep 12483395 = 18725093) B18725093
theorem B28146689 : Blo 730325 28146689 := bstep (se 2 (by rfl) ⟨10555008, by rfl⟩ : syracuseStep 28146689 = 21110017) B21110017
theorem B2784719 : Blo 730325 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B6685181 : Blo 730325 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B12682277 : Blo 730325 12682277 := bstep (se 4 (by rfl) ⟨1188963, by rfl⟩ : syracuseStep 12682277 = 2377927) B2377927
theorem B2786345 : Blo 730325 2786345 := bstep (se 2 (by rfl) ⟨1044879, by rfl⟩ : syracuseStep 2786345 = 2089759) B2089759
theorem B4162751 : Blo 730325 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B2819819 : Blo 730325 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B3704777 : Blo 730325 3704777 := bstep (se 2 (by rfl) ⟨1389291, by rfl⟩ : syracuseStep 3704777 = 2778583) B2778583
theorem B2230535 : Blo 730325 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B2231023 : Blo 730325 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B2788121 : Blo 730325 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B2231401 : Blo 730325 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B4164959 : Blo 730325 4164959 := bstep (se 1 (by rfl) ⟨3123719, by rfl⟩ : syracuseStep 4164959 = 6247439) B6247439
theorem B3968509 : Blo 730325 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B822811 : Blo 730325 822811 := bstep (se 1 (by rfl) ⟨617108, by rfl⟩ : syracuseStep 822811 = 1234217) B1234217
theorem B5279327 : Blo 730325 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B2232119 : Blo 730325 2232119 := bstep (se 1 (by rfl) ⟨1674089, by rfl⟩ : syracuseStep 2232119 = 3348179) B3348179
theorem B4755329 : Blo 730325 4755329 := bstep (se 2 (by rfl) ⟨1783248, by rfl⟩ : syracuseStep 4755329 = 3566497) B3566497
theorem B823207 : Blo 730325 823207 := bstep (se 1 (by rfl) ⟨617405, by rfl⟩ : syracuseStep 823207 = 1234811) B1234811
theorem B1249273 : Blo 730325 1249273 := bstep (se 2 (by rfl) ⟨468477, by rfl⟩ : syracuseStep 1249273 = 936955) B936955
theorem B823387 : Blo 730325 823387 := bstep (se 1 (by rfl) ⟨617540, by rfl⟩ : syracuseStep 823387 = 1235081) B1235081
theorem B8360171 : Blo 730325 8360171 := bstep (se 1 (by rfl) ⟨6270128, by rfl⟩ : syracuseStep 8360171 = 12540257) B12540257
theorem B7934249 : Blo 730325 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B823855 : Blo 730325 823855 := bstep (se 1 (by rfl) ⟨617891, by rfl⟩ : syracuseStep 823855 = 1235783) B1235783
theorem B33854453 : Blo 730325 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B57021515 : Blo 730325 57021515 := bstep (se 1 (by rfl) ⟨42766136, by rfl⟩ : syracuseStep 57021515 = 85532273) B85532273
theorem B824431 : Blo 730325 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B10557317 : Blo 730325 10557317 := bstep (se 4 (by rfl) ⟨989748, by rfl⟩ : syracuseStep 10557317 = 1979497) B1979497
theorem B1645307 : Blo 730325 1645307 := bstep (se 1 (by rfl) ⟨1233980, by rfl⟩ : syracuseStep 1645307 = 2467961) B2467961
theorem B1645433 : Blo 730325 1645433 := bstep (se 2 (by rfl) ⟨617037, by rfl⟩ : syracuseStep 1645433 = 1234075) B1234075
theorem B990203 : Blo 730325 990203 := bstep (se 1 (by rfl) ⟨742652, by rfl⟩ : syracuseStep 990203 = 1485305) B1485305
theorem B3709961 : Blo 730325 3709961 := bstep (se 2 (by rfl) ⟨1391235, by rfl⟩ : syracuseStep 3709961 = 2782471) B2782471
theorem B990263 : Blo 730325 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B4693423 : Blo 730325 4693423 := bstep (se 1 (by rfl) ⟨3520067, by rfl⟩ : syracuseStep 4693423 = 7040135) B7040135
theorem B2924552213 : Blo 730325 2924552213 := bstep (se 6 (by rfl) ⟨68544192, by rfl⟩ : syracuseStep 2924552213 = 137088385) B137088385
theorem B3711257 : Blo 730325 3711257 := bstep (se 2 (by rfl) ⟨1391721, by rfl⟩ : syracuseStep 3711257 = 2783443) B2783443
theorem B2498845 : Blo 730325 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B4170041 : Blo 730325 4170041 := bstep (se 2 (by rfl) ⟨1563765, by rfl⟩ : syracuseStep 4170041 = 3127531) B3127531
theorem B1647215 : Blo 730325 1647215 := bstep (se 1 (by rfl) ⟨1235411, by rfl⟩ : syracuseStep 1647215 = 2470823) B2470823
theorem B2466665 : Blo 730325 2466665 := bstep (se 2 (by rfl) ⟨924999, by rfl⟩ : syracuseStep 2466665 = 1849999) B1849999
theorem B2008127 : Blo 730325 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B7906571 : Blo 730325 7906571 := bstep (se 1 (by rfl) ⟨5929928, by rfl⟩ : syracuseStep 7906571 = 11859857) B11859857
theorem B2467097 : Blo 730325 2467097 := bstep (se 2 (by rfl) ⟨925161, by rfl⟩ : syracuseStep 2467097 = 1850323) B1850323
theorem B730575 : Blo 730325 730575 := bstep (se 1 (by rfl) ⟨547931, by rfl⟩ : syracuseStep 730575 = 1095863) B1095863
theorem B730607 : Blo 730325 730607 := bstep (se 1 (by rfl) ⟨547955, by rfl⟩ : syracuseStep 730607 = 1095911) B1095911
theorem B3712715 : Blo 730325 3712715 := bstep (se 1 (by rfl) ⟨2784536, by rfl⟩ : syracuseStep 3712715 = 5569073) B5569073
theorem B730855 : Blo 730325 730855 := bstep (se 1 (by rfl) ⟨548141, by rfl⟩ : syracuseStep 730855 = 1096283) B1096283
theorem B4171499 : Blo 730325 4171499 := bstep (se 1 (by rfl) ⟨3128624, by rfl⟩ : syracuseStep 4171499 = 6257249) B6257249
theorem B7022375 : Blo 730325 7022375 := bstep (se 1 (by rfl) ⟨5266781, by rfl⟩ : syracuseStep 7022375 = 10533563) B10533563
theorem B5285695 : Blo 730325 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B730951 : Blo 730325 730951 := bstep (se 1 (by rfl) ⟨548213, by rfl⟩ : syracuseStep 730951 = 1096427) B1096427
theorem B730971 : Blo 730325 730971 := bstep (se 1 (by rfl) ⟨548228, by rfl⟩ : syracuseStep 730971 = 1096457) B1096457
theorem B928027 : Blo 730325 928027 := bstep (se 1 (by rfl) ⟨696020, by rfl⟩ : syracuseStep 928027 = 1392041) B1392041
theorem B1648979 : Blo 730325 1648979 := bstep (se 1 (by rfl) ⟨1236734, by rfl⟩ : syracuseStep 1648979 = 2473469) B2473469
theorem B731551 : Blo 730325 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B731631 : Blo 730325 731631 := bstep (se 1 (by rfl) ⟨548723, by rfl⟩ : syracuseStep 731631 = 1097447) B1097447
theorem B731759 : Blo 730325 731759 := bstep (se 1 (by rfl) ⟨548819, by rfl⟩ : syracuseStep 731759 = 1097639) B1097639
theorem B1976989 : Blo 730325 1976989 := bstep (se 3 (by rfl) ⟨370685, by rfl⟩ : syracuseStep 1976989 = 741371) B741371
theorem B731975 : Blo 730325 731975 := bstep (se 1 (by rfl) ⟨548981, by rfl⟩ : syracuseStep 731975 = 1097963) B1097963
theorem B732015 : Blo 730325 732015 := bstep (se 1 (by rfl) ⟨549011, by rfl⟩ : syracuseStep 732015 = 1098023) B1098023
theorem B1649519 : Blo 730325 1649519 := bstep (se 1 (by rfl) ⟨1237139, by rfl⟩ : syracuseStep 1649519 = 2474279) B2474279
theorem B1649771 : Blo 730325 1649771 := bstep (se 1 (by rfl) ⟨1237328, by rfl⟩ : syracuseStep 1649771 = 2474657) B2474657
theorem B732463 : Blo 730325 732463 := bstep (se 1 (by rfl) ⟨549347, by rfl⟩ : syracuseStep 732463 = 1098695) B1098695
theorem B2469203 : Blo 730325 2469203 := bstep (se 1 (by rfl) ⟨1851902, by rfl⟩ : syracuseStep 2469203 = 3703805) B3703805
theorem B1650041 : Blo 730325 1650041 := bstep (se 2 (by rfl) ⟨618765, by rfl⟩ : syracuseStep 1650041 = 1237531) B1237531
theorem B6761861 : Blo 730325 6761861 := bstep (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) B1267849
theorem B732575 : Blo 730325 732575 := bstep (se 1 (by rfl) ⟨549431, by rfl⟩ : syracuseStep 732575 = 1098863) B1098863
theorem B6270371 : Blo 730325 6270371 := bstep (se 1 (by rfl) ⟨4702778, by rfl⟩ : syracuseStep 6270371 = 9405557) B9405557
theorem B7515575 : Blo 730325 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B732703 : Blo 730325 732703 := bstep (se 1 (by rfl) ⟨549527, by rfl⟩ : syracuseStep 732703 = 1099055) B1099055
theorem B1388153 : Blo 730325 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B732839 : Blo 730325 732839 := bstep (se 1 (by rfl) ⟨549629, by rfl⟩ : syracuseStep 732839 = 1099259) B1099259
theorem B732863 : Blo 730325 732863 := bstep (se 1 (by rfl) ⟨549647, by rfl⟩ : syracuseStep 732863 = 1099295) B1099295
theorem B732959 : Blo 730325 732959 := bstep (se 1 (by rfl) ⟨549719, by rfl⟩ : syracuseStep 732959 = 1099439) B1099439
theorem B5648201 : Blo 730325 5648201 := bstep (se 2 (by rfl) ⟨2118075, by rfl⟩ : syracuseStep 5648201 = 4236151) B4236151
theorem B2469743 : Blo 730325 2469743 := bstep (se 1 (by rfl) ⟨1852307, by rfl⟩ : syracuseStep 2469743 = 3704615) B3704615
theorem B733039 : Blo 730325 733039 := bstep (se 1 (by rfl) ⟨549779, by rfl⟩ : syracuseStep 733039 = 1099559) B1099559
theorem B8925065 : Blo 730325 8925065 := bstep (se 2 (by rfl) ⟨3346899, by rfl⟩ : syracuseStep 8925065 = 6693799) B6693799
theorem B1650671 : Blo 730325 1650671 := bstep (se 1 (by rfl) ⟨1238003, by rfl⟩ : syracuseStep 1650671 = 2476007) B2476007
theorem B6271019 : Blo 730325 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B733407 : Blo 730325 733407 := bstep (se 1 (by rfl) ⟨550055, by rfl⟩ : syracuseStep 733407 = 1100111) B1100111
theorem B2470121 : Blo 730325 2470121 := bstep (se 2 (by rfl) ⟨926295, by rfl⟩ : syracuseStep 2470121 = 1852591) B1852591
theorem B733439 : Blo 730325 733439 := bstep (se 1 (by rfl) ⟨550079, by rfl⟩ : syracuseStep 733439 = 1100159) B1100159
theorem B733467 : Blo 730325 733467 := bstep (se 1 (by rfl) ⟨550100, by rfl⟩ : syracuseStep 733467 = 1100201) B1100201
theorem B2470175 : Blo 730325 2470175 := bstep (se 1 (by rfl) ⟨1852631, by rfl⟩ : syracuseStep 2470175 = 3705263) B3705263
theorem B733723 : Blo 730325 733723 := bstep (se 1 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 733723 = 1100585) B1100585
theorem B4174415 : Blo 730325 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B6763175 : Blo 730325 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B733863 : Blo 730325 733863 := bstep (se 1 (by rfl) ⟨550397, by rfl⟩ : syracuseStep 733863 = 1100795) B1100795
theorem B733903 : Blo 730325 733903 := bstep (se 1 (by rfl) ⟨550427, by rfl⟩ : syracuseStep 733903 = 1100855) B1100855
theorem B733983 : Blo 730325 733983 := bstep (se 1 (by rfl) ⟨550487, by rfl⟩ : syracuseStep 733983 = 1100975) B1100975
theorem B6239375 : Blo 730325 6239375 := bstep (se 1 (by rfl) ⟨4679531, by rfl⟩ : syracuseStep 6239375 = 9359063) B9359063
theorem B1651967 : Blo 730325 1651967 := bstep (se 1 (by rfl) ⟨1238975, by rfl⟩ : syracuseStep 1651967 = 2477951) B2477951
theorem B8926811 : Blo 730325 8926811 := bstep (se 1 (by rfl) ⟨6695108, by rfl⟩ : syracuseStep 8926811 = 13390217) B13390217
theorem B3258251 : Blo 730325 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B5552063 : Blo 730325 5552063 := bstep (se 1 (by rfl) ⟨4164047, by rfl⟩ : syracuseStep 5552063 = 8328095) B8328095
theorem B1095659 : Blo 730325 1095659 := bstep (se 1 (by rfl) ⟨821744, by rfl⟩ : syracuseStep 1095659 = 1643489) B1643489
theorem B1849331 : Blo 730325 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B1390583 : Blo 730325 1390583 := bstep (se 1 (by rfl) ⟨1042937, by rfl⟩ : syracuseStep 1390583 = 2085875) B2085875
theorem B1095743 : Blo 730325 1095743 := bstep (se 1 (by rfl) ⟨821807, by rfl⟩ : syracuseStep 1095743 = 1643615) B1643615
theorem B2340971 : Blo 730325 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2472119 : Blo 730325 2472119 := bstep (se 1 (by rfl) ⟨1854089, by rfl⟩ : syracuseStep 2472119 = 3708179) B3708179
theorem B1096073 : Blo 730325 1096073 := bstep (se 2 (by rfl) ⟨411027, by rfl⟩ : syracuseStep 1096073 = 822055) B822055
theorem B5552549 : Blo 730325 5552549 := bstep (se 4 (by rfl) ⟨520551, by rfl⟩ : syracuseStep 5552549 = 1041103) B1041103
theorem B1096247 : Blo 730325 1096247 := bstep (se 1 (by rfl) ⟨822185, by rfl⟩ : syracuseStep 1096247 = 1644371) B1644371
theorem B4700855 : Blo 730325 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B1096571 : Blo 730325 1096571 := bstep (se 1 (by rfl) ⟨822428, by rfl⟩ : syracuseStep 1096571 = 1644857) B1644857
theorem B1850303 : Blo 730325 1850303 := bstep (se 1 (by rfl) ⟨1387727, by rfl⟩ : syracuseStep 1850303 = 2775455) B2775455
theorem B1097183 : Blo 730325 1097183 := bstep (se 1 (by rfl) ⟨822887, by rfl⟩ : syracuseStep 1097183 = 1645775) B1645775
theorem B1850951 : Blo 730325 1850951 := bstep (se 1 (by rfl) ⟨1388213, by rfl⟩ : syracuseStep 1850951 = 2776427) B2776427
theorem B2080475 : Blo 730325 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B1097435 : Blo 730325 1097435 := bstep (se 1 (by rfl) ⟨823076, by rfl⟩ : syracuseStep 1097435 = 1646153) B1646153
theorem B10534711 : Blo 730325 10534711 := bstep (se 1 (by rfl) ⟨7901033, by rfl⟩ : syracuseStep 10534711 = 15802067) B15802067
theorem B1392481 : Blo 730325 1392481 := bstep (se 2 (by rfl) ⟨522180, by rfl⟩ : syracuseStep 1392481 = 1044361) B1044361
theorem B1851295 : Blo 730325 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B1097705 : Blo 730325 1097705 := bstep (se 2 (by rfl) ⟨411639, by rfl⟩ : syracuseStep 1097705 = 823279) B823279
theorem B1097897 : Blo 730325 1097897 := bstep (se 2 (by rfl) ⟨411711, by rfl⟩ : syracuseStep 1097897 = 823423) B823423
theorem B2539735 : Blo 730325 2539735 := bstep (se 1 (by rfl) ⟨1904801, by rfl⟩ : syracuseStep 2539735 = 3809603) B3809603
theorem B1098215 : Blo 730325 1098215 := bstep (se 1 (by rfl) ⟨823661, by rfl⟩ : syracuseStep 1098215 = 1647323) B1647323
theorem B1098491 : Blo 730325 1098491 := bstep (se 1 (by rfl) ⟨823868, by rfl⟩ : syracuseStep 1098491 = 1647737) B1647737
theorem B1852409 : Blo 730325 1852409 := bstep (se 2 (by rfl) ⟨694653, by rfl⟩ : syracuseStep 1852409 = 1389307) B1389307
theorem B1098935 : Blo 730325 1098935 := bstep (se 1 (by rfl) ⟨824201, by rfl⟩ : syracuseStep 1098935 = 1648403) B1648403
theorem B1393939 : Blo 730325 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B3261727 : Blo 730325 3261727 := bstep (se 1 (by rfl) ⟨2446295, by rfl⟩ : syracuseStep 3261727 = 4892591) B4892591
theorem B1099079 : Blo 730325 1099079 := bstep (se 1 (by rfl) ⟨824309, by rfl⟩ : syracuseStep 1099079 = 1648619) B1648619
theorem B1099175 : Blo 730325 1099175 := bstep (se 1 (by rfl) ⟨824381, by rfl⟩ : syracuseStep 1099175 = 1648763) B1648763
theorem B1787303 : Blo 730325 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B1099355 : Blo 730325 1099355 := bstep (se 1 (by rfl) ⟨824516, by rfl⟩ : syracuseStep 1099355 = 1649033) B1649033
theorem B2082617 : Blo 730325 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B1755113 : Blo 730325 1755113 := bstep (se 2 (by rfl) ⟨658167, by rfl⟩ : syracuseStep 1755113 = 1316335) B1316335
theorem B2344943 : Blo 730325 2344943 := bstep (se 1 (by rfl) ⟨1758707, by rfl⟩ : syracuseStep 2344943 = 3517415) B3517415
theorem B1099823 : Blo 730325 1099823 := bstep (se 1 (by rfl) ⟨824867, by rfl⟩ : syracuseStep 1099823 = 1649735) B1649735
theorem B1100087 : Blo 730325 1100087 := bstep (se 1 (by rfl) ⟨825065, by rfl⟩ : syracuseStep 1100087 = 1650131) B1650131
theorem B1100267 : Blo 730325 1100267 := bstep (se 1 (by rfl) ⟨825200, by rfl⟩ : syracuseStep 1100267 = 1650401) B1650401
theorem B14305895 : Blo 730325 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B1100507 : Blo 730325 1100507 := bstep (se 1 (by rfl) ⟨825380, by rfl⟩ : syracuseStep 1100507 = 1650761) B1650761
theorem B1100543 : Blo 730325 1100543 := bstep (se 1 (by rfl) ⟨825407, by rfl⟩ : syracuseStep 1100543 = 1650815) B1650815
theorem B1101263 : Blo 730325 1101263 := bstep (se 1 (by rfl) ⟨825947, by rfl⟩ : syracuseStep 1101263 = 1651895) B1651895
theorem B3755489 : Blo 730325 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B1101353 : Blo 730325 1101353 := bstep (se 2 (by rfl) ⟨413007, by rfl⟩ : syracuseStep 1101353 = 826015) B826015
theorem B36131291 : Blo 730325 36131291 := bstep (se 1 (by rfl) ⟨27098468, by rfl⟩ : syracuseStep 36131291 = 54196937) B54196937
theorem B1856105 : Blo 730325 1856105 := bstep (se 2 (by rfl) ⟨696039, by rfl⟩ : syracuseStep 1856105 = 1392079) B1392079
theorem B2085533 : Blo 730325 2085533 := bstep (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) B782075
theorem B18764459 : Blo 730325 18764459 := bstep (se 1 (by rfl) ⟨14073344, by rfl⟩ : syracuseStep 18764459 = 28146689) B28146689
theorem B1561511 : Blo 730325 1561511 := bstep (se 1 (by rfl) ⟨1171133, by rfl⟩ : syracuseStep 1561511 = 2342267) B2342267
theorem B1856479 : Blo 730325 1856479 := bstep (se 1 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 1856479 = 2784719) B2784719
theorem B6674089 : Blo 730325 6674089 := bstep (se 2 (by rfl) ⟨2502783, by rfl⟩ : syracuseStep 6674089 = 5005567) B5005567
theorem B1758959 : Blo 730325 1758959 := bstep (se 1 (by rfl) ⟨1319219, by rfl⟩ : syracuseStep 1758959 = 2638439) B2638439
theorem B5953283 : Blo 730325 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B2348929 : Blo 730325 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B4446089 : Blo 730325 4446089 := bstep (se 2 (by rfl) ⟨1667283, by rfl⟩ : syracuseStep 4446089 = 3334567) B3334567
theorem B2119567 : Blo 730325 2119567 := bstep (se 1 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 2119567 = 3179351) B3179351
theorem B10672793 : Blo 730325 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B6249149 : Blo 730325 6249149 := bstep (se 3 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 6249149 = 2343431) B2343431
theorem B5561297 : Blo 730325 5561297 := bstep (se 2 (by rfl) ⟨2085486, by rfl⟩ : syracuseStep 5561297 = 4170973) B4170973
theorem B2350171 : Blo 730325 2350171 := bstep (se 1 (by rfl) ⟨1762628, by rfl⟩ : syracuseStep 2350171 = 3525257) B3525257
theorem B3136603 : Blo 730325 3136603 := bstep (se 1 (by rfl) ⟨2352452, by rfl⟩ : syracuseStep 3136603 = 4704905) B4704905
theorem B33873137 : Blo 730325 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B3169529 : Blo 730325 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B5561783 : Blo 730325 5561783 := bstep (se 1 (by rfl) ⟨4171337, by rfl⟩ : syracuseStep 5561783 = 8342675) B8342675
theorem B7822817 : Blo 730325 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B14048741 : Blo 730325 14048741 := bstep (se 4 (by rfl) ⟨1317069, by rfl⟩ : syracuseStep 14048741 = 2634139) B2634139
theorem B11886841 : Blo 730325 11886841 := bstep (se 2 (by rfl) ⟨4457565, by rfl⟩ : syracuseStep 11886841 = 8915131) B8915131
theorem B2089633 : Blo 730325 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B7037675 : Blo 730325 7037675 := bstep (se 1 (by rfl) ⟨5278256, by rfl⟩ : syracuseStep 7037675 = 10556513) B10556513
theorem B1565705 : Blo 730325 1565705 := bstep (se 2 (by rfl) ⟨587139, by rfl⟩ : syracuseStep 1565705 = 1174279) B1174279
theorem B5923961 : Blo 730325 5923961 := bstep (se 2 (by rfl) ⟨2221485, by rfl⟩ : syracuseStep 5923961 = 4442971) B4442971
theorem B1041599 : Blo 730325 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B1238503 : Blo 730325 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B4679815 : Blo 730325 4679815 := bstep (se 1 (by rfl) ⟨3509861, by rfl⟩ : syracuseStep 4679815 = 7019723) B7019723
theorem B5007595 : Blo 730325 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B3697487 : Blo 730325 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B3173807 : Blo 730325 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B17854789 : Blo 730325 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B7500113 : Blo 730325 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B4747643 : Blo 730325 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B35680769 : Blo 730325 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B3699593 : Blo 730325 3699593 := bstep (se 2 (by rfl) ⟨1387347, by rfl⟩ : syracuseStep 3699593 = 2774695) B2774695
theorem B1668251 : Blo 730325 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B783527 : Blo 730325 783527 := bstep (se 1 (by rfl) ⟨587645, by rfl⟩ : syracuseStep 783527 = 1175291) B1175291
theorem B8451793 : Blo 730325 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B1112375 : Blo 730325 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B8322263 : Blo 730325 8322263 := bstep (se 1 (by rfl) ⟨6241697, by rfl⟩ : syracuseStep 8322263 = 12483395) B12483395
theorem B1408495 : Blo 730325 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B4456787 : Blo 730325 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B8454851 : Blo 730325 8454851 := bstep (se 1 (by rfl) ⟨6341138, by rfl⟩ : syracuseStep 8454851 = 12682277) B12682277
theorem B2786177 : Blo 730325 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B9537263 : Blo 730325 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B7047593 : Blo 730325 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B5573447 : Blo 730325 5573447 := bstep (se 1 (by rfl) ⟨4180085, by rfl⟩ : syracuseStep 5573447 = 8360171) B8360171
theorem B24087527 : Blo 730325 24087527 := bstep (se 1 (by rfl) ⟨18065645, by rfl⟩ : syracuseStep 24087527 = 36131291) B36131291
theorem B38014343 : Blo 730325 38014343 := bstep (se 1 (by rfl) ⟨28510757, by rfl⟩ : syracuseStep 38014343 = 57021515) B57021515
theorem B3968855 : Blo 730325 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B7115195 : Blo 730325 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B4166099 : Blo 730325 4166099 := bstep (se 1 (by rfl) ⟨3124574, by rfl⟩ : syracuseStep 4166099 = 6249149) B6249149
theorem B3707531 : Blo 730325 3707531 := bstep (se 1 (by rfl) ⟨2780648, by rfl⟩ : syracuseStep 3707531 = 5561297) B5561297
theorem B22582091 : Blo 730325 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B3707855 : Blo 730325 3707855 := bstep (se 1 (by rfl) ⟨2780891, by rfl⟩ : syracuseStep 3707855 = 5561783) B5561783
theorem B5215211 : Blo 730325 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B1949701475 : Blo 730325 1949701475 := bstep (se 1 (by rfl) ⟨1462276106, by rfl⟩ : syracuseStep 1949701475 = 2924552213) B2924552213
theorem B4691783 : Blo 730325 4691783 := bstep (se 1 (by rfl) ⟨3518837, by rfl⟩ : syracuseStep 4691783 = 7037675) B7037675
theorem B1644443 : Blo 730325 1644443 := bstep (se 1 (by rfl) ⟨1233332, by rfl⟩ : syracuseStep 1644443 = 2466665) B2466665
theorem B1644731 : Blo 730325 1644731 := bstep (se 1 (by rfl) ⟨1233548, by rfl⟩ : syracuseStep 1644731 = 2467097) B2467097
theorem B2464991 : Blo 730325 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B1646135 : Blo 730325 1646135 := bstep (se 1 (by rfl) ⟨1234601, by rfl⟩ : syracuseStep 1646135 = 2469203) B2469203
theorem B925435 : Blo 730325 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B2826089 : Blo 730325 2826089 := bstep (se 2 (by rfl) ⟨1059783, by rfl⟩ : syracuseStep 2826089 = 2119567) B2119567
theorem B1646495 : Blo 730325 1646495 := bstep (se 1 (by rfl) ⟨1234871, by rfl⟩ : syracuseStep 1646495 = 2469743) B2469743
theorem B1646747 : Blo 730325 1646747 := bstep (se 1 (by rfl) ⟨1235060, by rfl⟩ : syracuseStep 1646747 = 2470121) B2470121
theorem B1646783 : Blo 730325 1646783 := bstep (se 1 (by rfl) ⟨1235087, by rfl⟩ : syracuseStep 1646783 = 2470175) B2470175
theorem B2466395 : Blo 730325 2466395 := bstep (se 1 (by rfl) ⟨1849796, by rfl⟩ : syracuseStep 2466395 = 3699593) B3699593
theorem B8463485 : Blo 730325 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B2172167 : Blo 730325 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B730439 : Blo 730325 730439 := bstep (se 1 (by rfl) ⟨547829, by rfl⟩ : syracuseStep 730439 = 1095659) B1095659
theorem B927055 : Blo 730325 927055 := bstep (se 1 (by rfl) ⟨695291, by rfl⟩ : syracuseStep 927055 = 1390583) B1390583
theorem B730495 : Blo 730325 730495 := bstep (se 1 (by rfl) ⟨547871, by rfl⟩ : syracuseStep 730495 = 1095743) B1095743
theorem B1648079 : Blo 730325 1648079 := bstep (se 1 (by rfl) ⟨1236059, by rfl⟩ : syracuseStep 1648079 = 2472119) B2472119
theorem B730715 : Blo 730325 730715 := bstep (se 1 (by rfl) ⟨548036, by rfl⟩ : syracuseStep 730715 = 1096073) B1096073
theorem B730831 : Blo 730325 730831 := bstep (se 1 (by rfl) ⟨548123, by rfl⟩ : syracuseStep 730831 = 1096247) B1096247
theorem B731047 : Blo 730325 731047 := bstep (se 1 (by rfl) ⟨548285, by rfl⟩ : syracuseStep 731047 = 1096571) B1096571
theorem B1877993 : Blo 730325 1877993 := bstep (se 2 (by rfl) ⟨704247, by rfl⟩ : syracuseStep 1877993 = 1408495) B1408495
theorem B5548175 : Blo 730325 5548175 := bstep (se 1 (by rfl) ⟨4161131, by rfl⟩ : syracuseStep 5548175 = 8322263) B8322263
theorem B731455 : Blo 730325 731455 := bstep (se 1 (by rfl) ⟨548591, by rfl⟩ : syracuseStep 731455 = 1097183) B1097183
theorem B1386983 : Blo 730325 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B731623 : Blo 730325 731623 := bstep (se 1 (by rfl) ⟨548717, by rfl⟩ : syracuseStep 731623 = 1097435) B1097435
theorem B2468393 : Blo 730325 2468393 := bstep (se 2 (by rfl) ⟨925647, by rfl⟩ : syracuseStep 2468393 = 1851295) B1851295
theorem B731803 : Blo 730325 731803 := bstep (se 1 (by rfl) ⟨548852, by rfl⟩ : syracuseStep 731803 = 1097705) B1097705
theorem B731931 : Blo 730325 731931 := bstep (se 1 (by rfl) ⟨548948, by rfl⟩ : syracuseStep 731931 = 1097897) B1097897
theorem B732143 : Blo 730325 732143 := bstep (se 1 (by rfl) ⟨549107, by rfl⟩ : syracuseStep 732143 = 1098215) B1098215
theorem B732327 : Blo 730325 732327 := bstep (se 1 (by rfl) ⟨549245, by rfl⟩ : syracuseStep 732327 = 1098491) B1098491
theorem B732623 : Blo 730325 732623 := bstep (se 1 (by rfl) ⟨549467, by rfl⟩ : syracuseStep 732623 = 1098935) B1098935
theorem B732719 : Blo 730325 732719 := bstep (se 1 (by rfl) ⟨549539, by rfl⟩ : syracuseStep 732719 = 1099079) B1099079
theorem B732783 : Blo 730325 732783 := bstep (se 1 (by rfl) ⟨549587, by rfl⟩ : syracuseStep 732783 = 1099175) B1099175
theorem B732903 : Blo 730325 732903 := bstep (se 1 (by rfl) ⟨549677, by rfl⟩ : syracuseStep 732903 = 1099355) B1099355
theorem B13545253 : Blo 730325 13545253 := bstep (se 4 (by rfl) ⟨1269867, by rfl⟩ : syracuseStep 13545253 = 2539735) B2539735
theorem B1388411 : Blo 730325 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B2469851 : Blo 730325 2469851 := bstep (se 1 (by rfl) ⟨1852388, by rfl⟩ : syracuseStep 2469851 = 3704777) B3704777
theorem B733215 : Blo 730325 733215 := bstep (se 1 (by rfl) ⟨549911, by rfl⟩ : syracuseStep 733215 = 1099823) B1099823
theorem B733391 : Blo 730325 733391 := bstep (se 1 (by rfl) ⟨550043, by rfl⟩ : syracuseStep 733391 = 1100087) B1100087
theorem B733511 : Blo 730325 733511 := bstep (se 1 (by rfl) ⟨550133, by rfl⟩ : syracuseStep 733511 = 1100267) B1100267
theorem B733671 : Blo 730325 733671 := bstep (se 1 (by rfl) ⟨550253, by rfl⟩ : syracuseStep 733671 = 1100507) B1100507
theorem B733695 : Blo 730325 733695 := bstep (se 1 (by rfl) ⟨550271, by rfl⟩ : syracuseStep 733695 = 1100543) B1100543
theorem B1651337 : Blo 730325 1651337 := bstep (se 2 (by rfl) ⟨619251, by rfl⟩ : syracuseStep 1651337 = 1238503) B1238503
theorem B734175 : Blo 730325 734175 := bstep (se 1 (by rfl) ⟨550631, by rfl⟩ : syracuseStep 734175 = 1101263) B1101263
theorem B734235 : Blo 730325 734235 := bstep (se 1 (by rfl) ⟨550676, by rfl⟩ : syracuseStep 734235 = 1101353) B1101353
theorem B3519551 : Blo 730325 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B1488079 : Blo 730325 1488079 := bstep (se 1 (by rfl) ⟨1116059, by rfl⟩ : syracuseStep 1488079 = 2232119) B2232119
theorem B5355005 : Blo 730325 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B6239753 : Blo 730325 6239753 := bstep (se 2 (by rfl) ⟨2339907, by rfl⟩ : syracuseStep 6239753 = 4679815) B4679815
theorem B5289499 : Blo 730325 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B1390355 : Blo 730325 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B2635985 : Blo 730325 2635985 := bstep (se 2 (by rfl) ⟨988494, by rfl⟩ : syracuseStep 2635985 = 1976989) B1976989
theorem B4766141 : Blo 730325 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B2964059 : Blo 730325 2964059 := bstep (se 1 (by rfl) ⟨2223044, by rfl⟩ : syracuseStep 2964059 = 4446089) B4446089
theorem B1096871 : Blo 730325 1096871 := bstep (se 1 (by rfl) ⟨822653, by rfl⟩ : syracuseStep 1096871 = 1645307) B1645307
theorem B1096955 : Blo 730325 1096955 := bstep (se 1 (by rfl) ⟨822716, by rfl⟩ : syracuseStep 1096955 = 1645433) B1645433
theorem B7519517 : Blo 730325 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B5291345 : Blo 730325 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B2473307 : Blo 730325 2473307 := bstep (se 1 (by rfl) ⟨1854980, by rfl⟩ : syracuseStep 2473307 = 3709961) B3709961
theorem B1097081 : Blo 730325 1097081 := bstep (se 2 (by rfl) ⟨411405, by rfl⟩ : syracuseStep 1097081 = 822811) B822811
theorem B2113019 : Blo 730325 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B40058549 : Blo 730325 40058549 := bstep (se 5 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 40058549 = 3755489) B3755489
theorem B1097609 : Blo 730325 1097609 := bstep (se 2 (by rfl) ⟨411603, by rfl⟩ : syracuseStep 1097609 = 823207) B823207
theorem B1097849 : Blo 730325 1097849 := bstep (se 2 (by rfl) ⟨411693, by rfl⟩ : syracuseStep 1097849 = 823387) B823387
theorem B2474171 : Blo 730325 2474171 := bstep (se 1 (by rfl) ⟨1855628, by rfl⟩ : syracuseStep 2474171 = 3711257) B3711257
theorem B1098143 : Blo 730325 1098143 := bstep (se 1 (by rfl) ⟨823607, by rfl⟩ : syracuseStep 1098143 = 1647215) B1647215
theorem B23806385 : Blo 730325 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B5948093 : Blo 730325 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B1098473 : Blo 730325 1098473 := bstep (se 2 (by rfl) ⟨411927, by rfl⟩ : syracuseStep 1098473 = 823855) B823855
theorem B3949307 : Blo 730325 3949307 := bstep (se 1 (by rfl) ⟨2961980, by rfl⟩ : syracuseStep 3949307 = 5923961) B5923961
theorem B2475143 : Blo 730325 2475143 := bstep (se 1 (by rfl) ⟨1856357, by rfl⟩ : syracuseStep 2475143 = 3712715) B3712715
theorem B2475305 : Blo 730325 2475305 := bstep (se 2 (by rfl) ⟨928239, by rfl⟩ : syracuseStep 2475305 = 1856479) B1856479
theorem B1099241 : Blo 730325 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B1099319 : Blo 730325 1099319 := bstep (se 1 (by rfl) ⟨824489, by rfl⟩ : syracuseStep 1099319 = 1648979) B1648979
theorem B1099679 : Blo 730325 1099679 := bstep (se 1 (by rfl) ⟨824759, by rfl⟩ : syracuseStep 1099679 = 1649519) B1649519
theorem B1099847 : Blo 730325 1099847 := bstep (se 1 (by rfl) ⟨824885, by rfl⟩ : syracuseStep 1099847 = 1649771) B1649771
theorem B8898785 : Blo 730325 8898785 := bstep (se 2 (by rfl) ⟨3337044, by rfl⟩ : syracuseStep 8898785 = 6674089) B6674089
theorem B1100027 : Blo 730325 1100027 := bstep (se 1 (by rfl) ⟨825020, by rfl⟩ : syracuseStep 1100027 = 1650041) B1650041
theorem B4507907 : Blo 730325 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B4180247 : Blo 730325 4180247 := bstep (se 1 (by rfl) ⟨3135185, by rfl⟩ : syracuseStep 4180247 = 6270371) B6270371
theorem B3131905 : Blo 730325 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B5950043 : Blo 730325 5950043 := bstep (se 1 (by rfl) ⟨4462532, by rfl⟩ : syracuseStep 5950043 = 8925065) B8925065
theorem B2640541 : Blo 730325 2640541 := bstep (se 3 (by rfl) ⟨495101, by rfl⟩ : syracuseStep 2640541 = 990203) B990203
theorem B1100447 : Blo 730325 1100447 := bstep (se 1 (by rfl) ⟨825335, by rfl⟩ : syracuseStep 1100447 = 1650671) B1650671
theorem B4180679 : Blo 730325 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B2640701 : Blo 730325 2640701 := bstep (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) B990263
theorem B5000075 : Blo 730325 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B3165095 : Blo 730325 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B4508783 : Blo 730325 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B1101311 : Blo 730325 1101311 := bstep (se 1 (by rfl) ⟨825983, by rfl⟩ : syracuseStep 1101311 = 1651967) B1651967
theorem B5951207 : Blo 730325 5951207 := bstep (se 1 (by rfl) ⟨4463405, by rfl⟩ : syracuseStep 5951207 = 8926811) B8926811
theorem B1232887 : Blo 730325 1232887 := bstep (se 1 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 1232887 = 1849331) B1849331
theorem B1560647 : Blo 730325 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B3133561 : Blo 730325 3133561 := bstep (se 2 (by rfl) ⟨1175085, by rfl⟩ : syracuseStep 3133561 = 2350171) B2350171
theorem B4182137 : Blo 730325 4182137 := bstep (se 2 (by rfl) ⟨1568301, by rfl⟩ : syracuseStep 4182137 = 3136603) B3136603
theorem B741583 : Blo 730325 741583 := bstep (se 1 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 741583 = 1112375) B1112375
theorem B3133903 : Blo 730325 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B1233535 : Blo 730325 1233535 := bstep (se 1 (by rfl) ⟨925151, by rfl⟩ : syracuseStep 1233535 = 1850303) B1850303
theorem B1233967 : Blo 730325 1233967 := bstep (se 1 (by rfl) ⟨925475, by rfl⟩ : syracuseStep 1233967 = 1850951) B1850951
theorem B14046281 : Blo 730325 14046281 := bstep (se 2 (by rfl) ⟨5267355, by rfl⟩ : syracuseStep 14046281 = 10534711) B10534711
theorem B1856641 : Blo 730325 1856641 := bstep (se 2 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 1856641 = 1392481) B1392481
theorem B15849121 : Blo 730325 15849121 := bstep (se 2 (by rfl) ⟨5943420, by rfl⟩ : syracuseStep 15849121 = 11886841) B11886841
theorem B3331793 : Blo 730325 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1234939 : Blo 730325 1234939 := bstep (se 1 (by rfl) ⟨926204, by rfl⟩ : syracuseStep 1234939 = 1852409) B1852409
theorem B1857563 : Blo 730325 1857563 := bstep (se 1 (by rfl) ⟨1393172, by rfl⟩ : syracuseStep 1857563 = 2786345) B2786345
theorem B2775167 : Blo 730325 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B1563295 : Blo 730325 1563295 := bstep (se 1 (by rfl) ⟨1172471, by rfl⟩ : syracuseStep 1563295 = 2344943) B2344943
theorem B1858585 : Blo 730325 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B1858747 : Blo 730325 1858747 := bstep (se 1 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 1858747 = 2788121) B2788121
theorem B2776639 : Blo 730325 2776639 := bstep (se 1 (by rfl) ⟨2082479, by rfl⟩ : syracuseStep 2776639 = 4164959) B4164959
theorem B3170219 : Blo 730325 3170219 := bstep (se 1 (by rfl) ⟨2377664, by rfl⟩ : syracuseStep 3170219 = 4755329) B4755329
theorem B6676793 : Blo 730325 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B1237369 : Blo 730325 1237369 := bstep (se 2 (by rfl) ⟨464013, by rfl⟩ : syracuseStep 1237369 = 928027) B928027
theorem B1237403 : Blo 730325 1237403 := bstep (se 1 (by rfl) ⟨928052, by rfl⟩ : syracuseStep 1237403 = 1856105) B1856105
theorem B2089405 : Blo 730325 2089405 := bstep (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) B783527
theorem B12509639 : Blo 730325 12509639 := bstep (se 1 (by rfl) ⟨9382229, by rfl⟩ : syracuseStep 12509639 = 18764459) B18764459
theorem B2777597 : Blo 730325 2777597 := bstep (se 3 (by rfl) ⟨520799, by rfl⟩ : syracuseStep 2777597 = 1041599) B1041599
theorem B1041007 : Blo 730325 1041007 := bstep (se 1 (by rfl) ⟨780755, by rfl⟩ : syracuseStep 1041007 = 1561511) B1561511
theorem B22569635 : Blo 730325 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B2974697 : Blo 730325 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B1172639 : Blo 730325 1172639 := bstep (se 1 (by rfl) ⟨879479, by rfl⟩ : syracuseStep 1172639 = 1758959) B1758959
theorem B7038211 : Blo 730325 7038211 := bstep (se 1 (by rfl) ⟨5278658, by rfl⟩ : syracuseStep 7038211 = 10557317) B10557317
theorem B2975201 : Blo 730325 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B9365827 : Blo 730325 9365827 := bstep (se 1 (by rfl) ⟨7024370, by rfl⟩ : syracuseStep 9365827 = 14048741) B14048741
theorem B4680301 : Blo 730325 4680301 := bstep (se 3 (by rfl) ⟨877556, by rfl⟩ : syracuseStep 4680301 = 1755113) B1755113
theorem B1665697 : Blo 730325 1665697 := bstep (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) B1249273
theorem B2780027 : Blo 730325 2780027 := bstep (se 1 (by rfl) ⟨2085020, by rfl⟩ : syracuseStep 2780027 = 4170041) B4170041
theorem B1043803 : Blo 730325 1043803 := bstep (se 1 (by rfl) ⟨782852, by rfl⟩ : syracuseStep 1043803 = 1565705) B1565705
theorem B5271047 : Blo 730325 5271047 := bstep (se 1 (by rfl) ⟨3953285, by rfl⟩ : syracuseStep 5271047 = 7906571) B7906571
theorem B2780999 : Blo 730325 2780999 := bstep (se 1 (by rfl) ⟨2085749, by rfl⟩ : syracuseStep 2780999 = 4171499) B4171499
theorem B4681583 : Blo 730325 4681583 := bstep (se 1 (by rfl) ⟨3511187, by rfl⟩ : syracuseStep 4681583 = 7022375) B7022375
theorem B17395877 : Blo 730325 17395877 := bstep (se 4 (by rfl) ⟨1630863, by rfl⟩ : syracuseStep 17395877 = 3261727) B3261727
theorem B11269057 : Blo 730325 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B5010383 : Blo 730325 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B3765467 : Blo 730325 3765467 := bstep (se 1 (by rfl) ⟨2824100, by rfl⟩ : syracuseStep 3765467 = 5648201) B5648201
theorem B23787179 : Blo 730325 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B2782943 : Blo 730325 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B4159583 : Blo 730325 4159583 := bstep (se 1 (by rfl) ⟨3119687, by rfl⟩ : syracuseStep 4159583 = 6239375) B6239375
theorem B1112167 : Blo 730325 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B3701375 : Blo 730325 3701375 := bstep (se 1 (by rfl) ⟨2776031, by rfl⟩ : syracuseStep 3701375 = 5552063) B5552063
theorem B3701699 : Blo 730325 3701699 := bstep (se 1 (by rfl) ⟨2776274, by rfl⟩ : syracuseStep 3701699 = 5552549) B5552549
theorem B6257897 : Blo 730325 6257897 := bstep (se 2 (by rfl) ⟨2346711, by rfl⟩ : syracuseStep 6257897 = 4693423) B4693423
theorem B4161725 : Blo 730325 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B5636567 : Blo 730325 5636567 := bstep (se 1 (by rfl) ⟨4227425, by rfl⟩ : syracuseStep 5636567 = 8454851) B8454851
theorem B2785873 : Blo 730325 2785873 := bstep (se 2 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 2785873 = 2089405) B2089405
theorem B6358175 : Blo 730325 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B5932523 : Blo 730325 5932523 := bstep (se 1 (by rfl) ⟨4449392, by rfl⟩ : syracuseStep 5932523 = 8898785) B8898785
theorem B2786831 : Blo 730325 2786831 := bstep (se 1 (by rfl) ⟨2090123, by rfl⟩ : syracuseStep 2786831 = 4180247) B4180247
theorem B3966695 : Blo 730325 3966695 := bstep (se 1 (by rfl) ⟨2975021, by rfl⟩ : syracuseStep 3966695 = 5950043) B5950043
theorem B2787119 : Blo 730325 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B15861581 : Blo 730325 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B16058351 : Blo 730325 16058351 := bstep (se 1 (by rfl) ⟨12043763, by rfl⟩ : syracuseStep 16058351 = 24087527) B24087527
theorem B3967471 : Blo 730325 3967471 := bstep (se 1 (by rfl) ⟨2975603, by rfl⟩ : syracuseStep 3967471 = 5951207) B5951207
theorem B2788091 : Blo 730325 2788091 := bstep (se 1 (by rfl) ⟨2091068, by rfl⟩ : syracuseStep 2788091 = 4182137) B4182137
theorem B12487769 : Blo 730325 12487769 := bstep (se 2 (by rfl) ⟨4682913, by rfl⟩ : syracuseStep 12487769 = 9365827) B9365827
theorem B3476807 : Blo 730325 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B5199203933 : Blo 730325 5199203933 := bstep (se 3 (by rfl) ⟨974850737, by rfl⟩ : syracuseStep 5199203933 = 1949701475) B1949701475
theorem B1643327 : Blo 730325 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B18060337 : Blo 730325 18060337 := bstep (se 2 (by rfl) ⟨6772626, by rfl⟩ : syracuseStep 18060337 = 13545253) B13545253
theorem B1643849 : Blo 730325 1643849 := bstep (se 2 (by rfl) ⟨616443, by rfl⟩ : syracuseStep 1643849 = 1232887) B1232887
theorem B824935 : Blo 730325 824935 := bstep (se 1 (by rfl) ⟨618701, by rfl⟩ : syracuseStep 824935 = 1237403) B1237403
theorem B988777 : Blo 730325 988777 := bstep (se 2 (by rfl) ⟨370791, by rfl⟩ : syracuseStep 988777 = 741583) B741583
theorem B1644263 : Blo 730325 1644263 := bstep (se 1 (by rfl) ⟨1233197, by rfl⟩ : syracuseStep 1644263 = 2466395) B2466395
theorem B1644713 : Blo 730325 1644713 := bstep (se 2 (by rfl) ⟨616767, by rfl⟩ : syracuseStep 1644713 = 1233535) B1233535
theorem B1448111 : Blo 730325 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B1251995 : Blo 730325 1251995 := bstep (se 1 (by rfl) ⟨938996, by rfl⟩ : syracuseStep 1251995 = 1877993) B1877993
theorem B1645289 : Blo 730325 1645289 := bstep (se 2 (by rfl) ⟨616983, by rfl⟩ : syracuseStep 1645289 = 1233967) B1233967
theorem B1645595 : Blo 730325 1645595 := bstep (se 1 (by rfl) ⟨1234196, by rfl⟩ : syracuseStep 1645595 = 2468393) B2468393
theorem B7052665 : Blo 730325 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B3514031 : Blo 730325 3514031 := bstep (se 1 (by rfl) ⟨2635523, by rfl⟩ : syracuseStep 3514031 = 5271047) B5271047
theorem B3121055 : Blo 730325 3121055 := bstep (se 1 (by rfl) ⟨2340791, by rfl⟩ : syracuseStep 3121055 = 4681583) B4681583
theorem B925607 : Blo 730325 925607 := bstep (se 1 (by rfl) ⟨694205, by rfl⟩ : syracuseStep 925607 = 1388411) B1388411
theorem B1646567 : Blo 730325 1646567 := bstep (se 1 (by rfl) ⟨1234925, by rfl⟩ : syracuseStep 1646567 = 2469851) B2469851
theorem B1646585 : Blo 730325 1646585 := bstep (se 2 (by rfl) ⟨617469, by rfl⟩ : syracuseStep 1646585 = 1234939) B1234939
theorem B1482889 : Blo 730325 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B926903 : Blo 730325 926903 := bstep (se 1 (by rfl) ⟨695177, by rfl⟩ : syracuseStep 926903 = 1390355) B1390355
theorem B1976039 : Blo 730325 1976039 := bstep (se 1 (by rfl) ⟨1482029, by rfl⟩ : syracuseStep 1976039 = 2964059) B2964059
theorem B2467583 : Blo 730325 2467583 := bstep (se 1 (by rfl) ⟨1850687, by rfl⟩ : syracuseStep 2467583 = 3701375) B3701375
theorem B2467799 : Blo 730325 2467799 := bstep (se 1 (by rfl) ⟨1850849, by rfl⟩ : syracuseStep 2467799 = 3701699) B3701699
theorem B731247 : Blo 730325 731247 := bstep (se 1 (by rfl) ⟨548435, by rfl⟩ : syracuseStep 731247 = 1096871) B1096871
theorem B4171931 : Blo 730325 4171931 := bstep (se 1 (by rfl) ⟨3128948, by rfl⟩ : syracuseStep 4171931 = 6257897) B6257897
theorem B731303 : Blo 730325 731303 := bstep (se 1 (by rfl) ⟨548477, by rfl⟩ : syracuseStep 731303 = 1096955) B1096955
theorem B1648871 : Blo 730325 1648871 := bstep (se 1 (by rfl) ⟨1236653, by rfl⟩ : syracuseStep 1648871 = 2473307) B2473307
theorem B731387 : Blo 730325 731387 := bstep (se 1 (by rfl) ⟨548540, by rfl⟩ : syracuseStep 731387 = 1097081) B1097081
theorem B731739 : Blo 730325 731739 := bstep (se 1 (by rfl) ⟨548804, by rfl⟩ : syracuseStep 731739 = 1097609) B1097609
theorem B731899 : Blo 730325 731899 := bstep (se 1 (by rfl) ⟨548924, by rfl⟩ : syracuseStep 731899 = 1097849) B1097849
theorem B1649447 : Blo 730325 1649447 := bstep (se 1 (by rfl) ⟨1237085, by rfl⟩ : syracuseStep 1649447 = 2474171) B2474171
theorem B732095 : Blo 730325 732095 := bstep (se 1 (by rfl) ⟨549071, by rfl⟩ : syracuseStep 732095 = 1098143) B1098143
theorem B15870923 : Blo 730325 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B732315 : Blo 730325 732315 := bstep (se 1 (by rfl) ⟨549236, by rfl⟩ : syracuseStep 732315 = 1098473) B1098473
theorem B1649825 : Blo 730325 1649825 := bstep (se 2 (by rfl) ⟨618684, by rfl⟩ : syracuseStep 1649825 = 1237369) B1237369
theorem B2632871 : Blo 730325 2632871 := bstep (se 1 (by rfl) ⟨1974653, by rfl⟩ : syracuseStep 2632871 = 3949307) B3949307
theorem B1650095 : Blo 730325 1650095 := bstep (se 1 (by rfl) ⟨1237571, by rfl⟩ : syracuseStep 1650095 = 2475143) B2475143
theorem B1388009 : Blo 730325 1388009 := bstep (se 2 (by rfl) ⟨520503, by rfl⟩ : syracuseStep 1388009 = 1041007) B1041007
theorem B1650203 : Blo 730325 1650203 := bstep (se 1 (by rfl) ⟨1237652, by rfl⟩ : syracuseStep 1650203 = 2475305) B2475305
theorem B732827 : Blo 730325 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B732879 : Blo 730325 732879 := bstep (se 1 (by rfl) ⟨549659, by rfl⟩ : syracuseStep 732879 = 1099319) B1099319
theorem B733119 : Blo 730325 733119 := bstep (se 1 (by rfl) ⟨549839, by rfl⟩ : syracuseStep 733119 = 1099679) B1099679
theorem B733231 : Blo 730325 733231 := bstep (se 1 (by rfl) ⟨549923, by rfl⟩ : syracuseStep 733231 = 1099847) B1099847
theorem B733351 : Blo 730325 733351 := bstep (se 1 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 733351 = 1100027) B1100027
theorem B4698395 : Blo 730325 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B9384281 : Blo 730325 9384281 := bstep (se 2 (by rfl) ⟨3519105, by rfl⟩ : syracuseStep 9384281 = 7038211) B7038211
theorem B733631 : Blo 730325 733631 := bstep (se 1 (by rfl) ⟨550223, by rfl⟩ : syracuseStep 733631 = 1100447) B1100447
theorem B3715631 : Blo 730325 3715631 := bstep (se 1 (by rfl) ⟨2786723, by rfl⟩ : syracuseStep 3715631 = 5573447) B5573447
theorem B2110063 : Blo 730325 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B25342895 : Blo 730325 25342895 := bstep (se 1 (by rfl) ⟨19007171, by rfl⟩ : syracuseStep 25342895 = 38014343) B38014343
theorem B734207 : Blo 730325 734207 := bstep (se 1 (by rfl) ⟨550655, by rfl⟩ : syracuseStep 734207 = 1101311) B1101311
theorem B2471687 : Blo 730325 2471687 := bstep (se 1 (by rfl) ⟨1853765, by rfl⟩ : syracuseStep 2471687 = 3707531) B3707531
theorem B10041245 : Blo 730325 10041245 := bstep (se 3 (by rfl) ⟨1882733, by rfl⟩ : syracuseStep 10041245 = 3765467) B3765467
theorem B2471903 : Blo 730325 2471903 := bstep (se 1 (by rfl) ⟨1853927, by rfl⟩ : syracuseStep 2471903 = 3707855) B3707855
theorem B4175873 : Blo 730325 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B6240401 : Blo 730325 6240401 := bstep (se 2 (by rfl) ⟨2340150, by rfl⟩ : syracuseStep 6240401 = 4680301) B4680301
theorem B3520721 : Blo 730325 3520721 := bstep (se 2 (by rfl) ⟨1320270, by rfl⟩ : syracuseStep 3520721 = 2640541) B2640541
theorem B3127855 : Blo 730325 3127855 := bstep (se 1 (by rfl) ⟨2345891, by rfl⟩ : syracuseStep 3127855 = 4691783) B4691783
theorem B1096295 : Blo 730325 1096295 := bstep (se 1 (by rfl) ⟨822221, by rfl⟩ : syracuseStep 1096295 = 1644443) B1644443
theorem B1850111 : Blo 730325 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B1096487 : Blo 730325 1096487 := bstep (se 1 (by rfl) ⟨822365, by rfl⟩ : syracuseStep 1096487 = 1644731) B1644731
theorem B1391737 : Blo 730325 1391737 := bstep (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) B1043803
theorem B1097423 : Blo 730325 1097423 := bstep (se 1 (by rfl) ⟨823067, by rfl⟩ : syracuseStep 1097423 = 1646135) B1646135
theorem B1884059 : Blo 730325 1884059 := bstep (se 1 (by rfl) ⟨1413044, by rfl⟩ : syracuseStep 1884059 = 2826089) B2826089
theorem B1097663 : Blo 730325 1097663 := bstep (se 1 (by rfl) ⟨823247, by rfl⟩ : syracuseStep 1097663 = 1646495) B1646495
theorem B1097831 : Blo 730325 1097831 := bstep (se 1 (by rfl) ⟨823373, by rfl⟩ : syracuseStep 1097831 = 1646747) B1646747
theorem B1097855 : Blo 730325 1097855 := bstep (se 1 (by rfl) ⟨823391, by rfl⟩ : syracuseStep 1097855 = 1646783) B1646783
theorem B4178081 : Blo 730325 4178081 := bstep (se 2 (by rfl) ⟨1566780, by rfl⟩ : syracuseStep 4178081 = 3133561) B3133561
theorem B8339759 : Blo 730325 8339759 := bstep (se 1 (by rfl) ⟨6254819, by rfl⟩ : syracuseStep 8339759 = 12509639) B12509639
theorem B1851731 : Blo 730325 1851731 := bstep (se 1 (by rfl) ⟨1388798, by rfl⟩ : syracuseStep 1851731 = 2777597) B2777597
theorem B4178537 : Blo 730325 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B1983131 : Blo 730325 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B1098719 : Blo 730325 1098719 := bstep (se 1 (by rfl) ⟨824039, by rfl⟩ : syracuseStep 1098719 = 1648079) B1648079
theorem B1983467 : Blo 730325 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B15025409 : Blo 730325 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B2475521 : Blo 730325 2475521 := bstep (se 2 (by rfl) ⟨928320, by rfl⟩ : syracuseStep 2475521 = 1856641) B1856641
theorem B1984105 : Blo 730325 1984105 := bstep (se 2 (by rfl) ⟨744039, by rfl⟩ : syracuseStep 1984105 = 1488079) B1488079
theorem B1853351 : Blo 730325 1853351 := bstep (se 1 (by rfl) ⟨1390013, by rfl⟩ : syracuseStep 1853351 = 2780027) B2780027
theorem B1853999 : Blo 730325 1853999 := bstep (se 1 (by rfl) ⟨1390499, by rfl⟩ : syracuseStep 1853999 = 2780999) B2780999
theorem B1100891 : Blo 730325 1100891 := bstep (se 1 (by rfl) ⟨825668, by rfl⟩ : syracuseStep 1100891 = 1651337) B1651337
theorem B2346367 : Blo 730325 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B2084393 : Blo 730325 2084393 := bstep (se 2 (by rfl) ⟨781647, by rfl⟩ : syracuseStep 2084393 = 1563295) B1563295
theorem B1855295 : Blo 730325 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B2478113 : Blo 730325 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B2773055 : Blo 730325 2773055 := bstep (se 1 (by rfl) ⟨2079791, by rfl⟩ : syracuseStep 2773055 = 4159583) B4159583
theorem B1757323 : Blo 730325 1757323 := bstep (se 1 (by rfl) ⟨1317992, by rfl⟩ : syracuseStep 1757323 = 2635985) B2635985
theorem B2478329 : Blo 730325 2478329 := bstep (se 2 (by rfl) ⟨929373, by rfl⟩ : syracuseStep 2478329 = 1858747) B1858747
theorem B3527563 : Blo 730325 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B1233913 : Blo 730325 1233913 := bstep (se 2 (by rfl) ⟨462717, by rfl⟩ : syracuseStep 1233913 = 925435) B925435
theorem B1857451 : Blo 730325 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B60185693 : Blo 730325 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1236073 : Blo 730325 1236073 := bstep (se 2 (by rfl) ⟨463527, by rfl⟩ : syracuseStep 1236073 = 927055) B927055
theorem B1760467 : Blo 730325 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B3333383 : Blo 730325 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B3005855 : Blo 730325 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B60218909 : Blo 730325 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B13361021 : Blo 730325 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B2645903 : Blo 730325 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B4743463 : Blo 730325 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B2777399 : Blo 730325 2777399 := bstep (se 1 (by rfl) ⟨2083049, by rfl⟩ : syracuseStep 2777399 = 4166099) B4166099
theorem B22569293 : Blo 730325 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B9364187 : Blo 730325 9364187 := bstep (se 1 (by rfl) ⟨7023140, by rfl⟩ : syracuseStep 9364187 = 14046281) B14046281
theorem B47539061 : Blo 730325 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B2220929 : Blo 730325 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B2221195 : Blo 730325 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B14280013 : Blo 730325 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B1238375 : Blo 730325 1238375 := bstep (se 1 (by rfl) ⟨928781, by rfl⟩ : syracuseStep 1238375 = 1857563) B1857563
theorem B4451195 : Blo 730325 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B12021085 : Blo 730325 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B781759 : Blo 730325 781759 := bstep (se 1 (by rfl) ⟨586319, by rfl⟩ : syracuseStep 781759 = 1172639) B1172639
theorem B3698621 : Blo 730325 3698621 := bstep (se 3 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 3698621 = 1386983) B1386983
theorem B3698783 : Blo 730325 3698783 := bstep (se 1 (by rfl) ⟨2774087, by rfl⟩ : syracuseStep 3698783 = 5548175) B5548175
theorem B21132161 : Blo 730325 21132161 := bstep (se 2 (by rfl) ⟨7924560, by rfl⟩ : syracuseStep 21132161 = 15849121) B15849121
theorem B11597251 : Blo 730325 11597251 := bstep (se 1 (by rfl) ⟨8697938, by rfl⟩ : syracuseStep 11597251 = 17395877) B17395877
theorem B4159835 : Blo 730325 4159835 := bstep (se 1 (by rfl) ⟨3119876, by rfl⟩ : syracuseStep 4159835 = 6239753) B6239753
theorem B15858119 : Blo 730325 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B3177427 : Blo 730325 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B3702185 : Blo 730325 3702185 := bstep (se 2 (by rfl) ⟨1388319, by rfl⟩ : syracuseStep 3702185 = 2776639) B2776639
theorem B5013011 : Blo 730325 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B1408679 : Blo 730325 1408679 := bstep (se 1 (by rfl) ⟨1056509, by rfl⟩ : syracuseStep 1408679 = 2113019) B2113019
theorem B8453917 : Blo 730325 8453917 := bstep (se 3 (by rfl) ⟨1585109, by rfl⟩ : syracuseStep 8453917 = 3170219) B3170219
theorem B26705699 : Blo 730325 26705699 := bstep (se 1 (by rfl) ⟨20029274, by rfl⟩ : syracuseStep 26705699 = 40058549) B40058549
theorem B2785387 : Blo 730325 2785387 := bstep (se 1 (by rfl) ⟨2089040, by rfl⟩ : syracuseStep 2785387 = 4178081) B4178081
theorem B6324617 : Blo 730325 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B2785691 : Blo 730325 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B19040017 : Blo 730325 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B8325179 : Blo 730325 8325179 := bstep (se 1 (by rfl) ⟨6243884, by rfl⟩ : syracuseStep 8325179 = 12487769) B12487769
theorem B3466135955 : Blo 730325 3466135955 := bstep (se 1 (by rfl) ⟨2599601966, by rfl⟩ : syracuseStep 3466135955 = 5199203933) B5199203933
theorem B16028113 : Blo 730325 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B2003903 : Blo 730325 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B40145939 : Blo 730325 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B15046195 : Blo 730325 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B31692707 : Blo 730325 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B1480619 : Blo 730325 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B825583 : Blo 730325 825583 := bstep (se 1 (by rfl) ⟨619187, by rfl⟩ : syracuseStep 825583 = 1238375) B1238375
theorem B1317359 : Blo 730325 1317359 := bstep (se 1 (by rfl) ⟨988019, by rfl⟩ : syracuseStep 1317359 = 1976039) B1976039
theorem B1645055 : Blo 730325 1645055 := bstep (se 1 (by rfl) ⟨1233791, by rfl⟩ : syracuseStep 1645055 = 2467583) B2467583
theorem B1645199 : Blo 730325 1645199 := bstep (se 1 (by rfl) ⟨1233899, by rfl⟩ : syracuseStep 1645199 = 2467799) B2467799
theorem B1645217 : Blo 730325 1645217 := bstep (se 2 (by rfl) ⟨616956, by rfl⟩ : syracuseStep 1645217 = 1233913) B1233913
theorem B1318369 : Blo 730325 1318369 := bstep (se 2 (by rfl) ⟨494388, by rfl⟩ : syracuseStep 1318369 = 988777) B988777
theorem B925339 : Blo 730325 925339 := bstep (se 1 (by rfl) ⟨694004, by rfl⟩ : syracuseStep 925339 = 1388009) B1388009
theorem B2465747 : Blo 730325 2465747 := bstep (se 1 (by rfl) ⟨1849310, by rfl⟩ : syracuseStep 2465747 = 3698621) B3698621
theorem B2465855 : Blo 730325 2465855 := bstep (se 1 (by rfl) ⟨1849391, by rfl⟩ : syracuseStep 2465855 = 3698783) B3698783
theorem B7020989 : Blo 730325 7020989 := bstep (se 3 (by rfl) ⟨1316435, by rfl⟩ : syracuseStep 7020989 = 2632871) B2632871
theorem B4170473 : Blo 730325 4170473 := bstep (se 2 (by rfl) ⟨1563927, by rfl⟩ : syracuseStep 4170473 = 3127855) B3127855
theorem B1647791 : Blo 730325 1647791 := bstep (se 1 (by rfl) ⟨1235843, by rfl⟩ : syracuseStep 1647791 = 2471687) B2471687
theorem B6694163 : Blo 730325 6694163 := bstep (se 1 (by rfl) ⟨5020622, by rfl⟩ : syracuseStep 6694163 = 10041245) B10041245
theorem B4236569 : Blo 730325 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B1647935 : Blo 730325 1647935 := bstep (se 1 (by rfl) ⟨1235951, by rfl⟩ : syracuseStep 1647935 = 2471903) B2471903
theorem B1648097 : Blo 730325 1648097 := bstep (se 2 (by rfl) ⟨618036, by rfl⟩ : syracuseStep 1648097 = 1236073) B1236073
theorem B730863 : Blo 730325 730863 := bstep (se 1 (by rfl) ⟨548147, by rfl⟩ : syracuseStep 730863 = 1096295) B1096295
theorem B730991 : Blo 730325 730991 := bstep (se 1 (by rfl) ⟨548243, by rfl⟩ : syracuseStep 730991 = 1096487) B1096487
theorem B2468123 : Blo 730325 2468123 := bstep (se 1 (by rfl) ⟨1851092, by rfl⟩ : syracuseStep 2468123 = 3702185) B3702185
theorem B7055741 : Blo 730325 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B2468285 : Blo 730325 2468285 := bstep (se 3 (by rfl) ⟨462803, by rfl⟩ : syracuseStep 2468285 = 925607) B925607
theorem B731615 : Blo 730325 731615 := bstep (se 1 (by rfl) ⟨548711, by rfl⟩ : syracuseStep 731615 = 1097423) B1097423
theorem B17803799 : Blo 730325 17803799 := bstep (se 1 (by rfl) ⟨13352849, by rfl⟩ : syracuseStep 17803799 = 26705699) B26705699
theorem B1256039 : Blo 730325 1256039 := bstep (se 1 (by rfl) ⟨942029, by rfl⟩ : syracuseStep 1256039 = 1884059) B1884059
theorem B731775 : Blo 730325 731775 := bstep (se 1 (by rfl) ⟨548831, by rfl⟩ : syracuseStep 731775 = 1097663) B1097663
theorem B731887 : Blo 730325 731887 := bstep (se 1 (by rfl) ⟨548915, by rfl⟩ : syracuseStep 731887 = 1097831) B1097831
theorem B731903 : Blo 730325 731903 := bstep (se 1 (by rfl) ⟨548927, by rfl⟩ : syracuseStep 731903 = 1097855) B1097855
theorem B1977185 : Blo 730325 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B1322087 : Blo 730325 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B732479 : Blo 730325 732479 := bstep (se 1 (by rfl) ⟨549359, by rfl⟩ : syracuseStep 732479 = 1098719) B1098719
theorem B3714497 : Blo 730325 3714497 := bstep (se 2 (by rfl) ⟨1392936, by rfl⟩ : syracuseStep 3714497 = 2785873) B2785873
theorem B4238783 : Blo 730325 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B1650347 : Blo 730325 1650347 := bstep (se 1 (by rfl) ⟨1237760, by rfl⟩ : syracuseStep 1650347 = 2475521) B2475521
theorem B2961593 : Blo 730325 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B733927 : Blo 730325 733927 := bstep (se 1 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 733927 = 1100891) B1100891
theorem B5289245 : Blo 730325 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B1652075 : Blo 730325 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B1848703 : Blo 730325 1848703 := bstep (se 1 (by rfl) ⟨1386527, by rfl⟩ : syracuseStep 1848703 = 2773055) B2773055
theorem B1652219 : Blo 730325 1652219 := bstep (se 1 (by rfl) ⟨1239164, by rfl⟩ : syracuseStep 1652219 = 2478329) B2478329
theorem B2471741 : Blo 730325 2471741 := bstep (se 3 (by rfl) ⟨463451, by rfl⟩ : syracuseStep 2471741 = 926903) B926903
theorem B1095551 : Blo 730325 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B5289961 : Blo 730325 5289961 := bstep (se 2 (by rfl) ⟨1983735, by rfl⟩ : syracuseStep 5289961 = 3967471) B3967471
theorem B1095899 : Blo 730325 1095899 := bstep (se 1 (by rfl) ⟨821924, by rfl⟩ : syracuseStep 1095899 = 1643849) B1643849
theorem B1096175 : Blo 730325 1096175 := bstep (se 1 (by rfl) ⟨822131, by rfl⟩ : syracuseStep 1096175 = 1644263) B1644263
theorem B1096475 : Blo 730325 1096475 := bstep (se 1 (by rfl) ⟨822356, by rfl⟩ : syracuseStep 1096475 = 1644713) B1644713
theorem B965407 : Blo 730325 965407 := bstep (se 1 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 965407 = 1448111) B1448111
theorem B1096859 : Blo 730325 1096859 := bstep (se 1 (by rfl) ⟨822644, by rfl⟩ : syracuseStep 1096859 = 1645289) B1645289
theorem B3128489 : Blo 730325 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B1097063 : Blo 730325 1097063 := bstep (se 1 (by rfl) ⟨822797, by rfl⟩ : syracuseStep 1097063 = 1645595) B1645595
theorem B2342687 : Blo 730325 2342687 := bstep (se 1 (by rfl) ⟨1757015, by rfl⟩ : syracuseStep 2342687 = 3514031) B3514031
theorem B2080703 : Blo 730325 2080703 := bstep (se 1 (by rfl) ⟨1560527, by rfl⟩ : syracuseStep 2080703 = 3121055) B3121055
theorem B1097711 : Blo 730325 1097711 := bstep (se 1 (by rfl) ⟨823283, by rfl⟩ : syracuseStep 1097711 = 1646567) B1646567
theorem B1097723 : Blo 730325 1097723 := bstep (se 1 (by rfl) ⟨823292, by rfl⟩ : syracuseStep 1097723 = 1646585) B1646585
theorem B2343097 : Blo 730325 2343097 := bstep (se 2 (by rfl) ⟨878661, by rfl⟩ : syracuseStep 2343097 = 1757323) B1757323
theorem B1851599 : Blo 730325 1851599 := bstep (se 1 (by rfl) ⟨1388699, by rfl⟩ : syracuseStep 1851599 = 2777399) B2777399
theorem B6242791 : Blo 730325 6242791 := bstep (se 1 (by rfl) ⟨4682093, by rfl⟩ : syracuseStep 6242791 = 9364187) B9364187
theorem B4703417 : Blo 730325 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B1099247 : Blo 730325 1099247 := bstep (se 1 (by rfl) ⟨824435, by rfl⟩ : syracuseStep 1099247 = 1648871) B1648871
theorem B1099631 : Blo 730325 1099631 := bstep (se 1 (by rfl) ⟨824723, by rfl⟩ : syracuseStep 1099631 = 1649447) B1649447
theorem B2967463 : Blo 730325 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B1099883 : Blo 730325 1099883 := bstep (se 1 (by rfl) ⟨824912, by rfl⟩ : syracuseStep 1099883 = 1649825) B1649825
theorem B1099913 : Blo 730325 1099913 := bstep (se 2 (by rfl) ⟨412467, by rfl⟩ : syracuseStep 1099913 = 824935) B824935
theorem B1100063 : Blo 730325 1100063 := bstep (se 1 (by rfl) ⟨825047, by rfl⟩ : syracuseStep 1100063 = 1650095) B1650095
theorem B1100135 : Blo 730325 1100135 := bstep (se 1 (by rfl) ⟨825101, by rfl⟩ : syracuseStep 1100135 = 1650203) B1650203
theorem B2476601 : Blo 730325 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B3132263 : Blo 730325 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B2477087 : Blo 730325 2477087 := bstep (se 1 (by rfl) ⟨1857815, by rfl⟩ : syracuseStep 2477087 = 3715631) B3715631
theorem B16895263 : Blo 730325 16895263 := bstep (se 1 (by rfl) ⟨12671447, by rfl⟩ : syracuseStep 16895263 = 25342895) B25342895
theorem B5558381 : Blo 730325 5558381 := bstep (se 3 (by rfl) ⟨1042196, by rfl⟩ : syracuseStep 5558381 = 2084393) B2084393
theorem B2347147 : Blo 730325 2347147 := bstep (se 1 (by rfl) ⟨1760360, by rfl⟩ : syracuseStep 2347147 = 3520721) B3520721
theorem B1855649 : Blo 730325 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B2773223 : Blo 730325 2773223 := bstep (se 1 (by rfl) ⟨2079917, by rfl⟩ : syracuseStep 2773223 = 4159835) B4159835
theorem B2347289 : Blo 730325 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B10572079 : Blo 730325 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B1233407 : Blo 730325 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B939119 : Blo 730325 939119 := bstep (se 1 (by rfl) ⟨704339, by rfl⟩ : syracuseStep 939119 = 1408679) B1408679
theorem B2774483 : Blo 730325 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B5559839 : Blo 730325 5559839 := bstep (se 1 (by rfl) ⟨4169879, by rfl⟩ : syracuseStep 5559839 = 8339759) B8339759
theorem B1234487 : Blo 730325 1234487 := bstep (se 1 (by rfl) ⟨925865, by rfl⟩ : syracuseStep 1234487 = 1851731) B1851731
theorem B3757711 : Blo 730325 3757711 := bstep (se 1 (by rfl) ⟨2818283, by rfl⟩ : syracuseStep 3757711 = 5636567) B5636567
theorem B10016939 : Blo 730325 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B3955015 : Blo 730325 3955015 := bstep (se 1 (by rfl) ⟨2966261, by rfl⟩ : syracuseStep 3955015 = 5932523) B5932523
theorem B1857887 : Blo 730325 1857887 := bstep (se 1 (by rfl) ⟨1393415, by rfl⟩ : syracuseStep 1857887 = 2786831) B2786831
theorem B2644463 : Blo 730325 2644463 := bstep (se 1 (by rfl) ⟨1983347, by rfl⟩ : syracuseStep 2644463 = 3966695) B3966695
theorem B1858079 : Blo 730325 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B10574387 : Blo 730325 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B1235567 : Blo 730325 1235567 := bstep (se 1 (by rfl) ⟨926675, by rfl⟩ : syracuseStep 1235567 = 1853351) B1853351
theorem B10705567 : Blo 730325 10705567 := bstep (se 1 (by rfl) ⟨8029175, by rfl⟩ : syracuseStep 10705567 = 16058351) B16058351
theorem B1235999 : Blo 730325 1235999 := bstep (se 1 (by rfl) ⟨926999, by rfl⟩ : syracuseStep 1235999 = 1853999) B1853999
theorem B1858727 : Blo 730325 1858727 := bstep (se 1 (by rfl) ⟨1394045, by rfl⟩ : syracuseStep 1858727 = 2788091) B2788091
theorem B2645473 : Blo 730325 2645473 := bstep (se 2 (by rfl) ⟨992052, by rfl⟩ : syracuseStep 2645473 = 1984105) B1984105
theorem B2317871 : Blo 730325 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B1236863 : Blo 730325 1236863 := bstep (se 1 (by rfl) ⟨927647, by rfl⟩ : syracuseStep 1236863 = 1855295) B1855295
theorem B1042345 : Blo 730325 1042345 := bstep (se 2 (by rfl) ⟨390879, by rfl⟩ : syracuseStep 1042345 = 781759) B781759
theorem B2222255 : Blo 730325 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B8907347 : Blo 730325 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B2813417 : Blo 730325 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B24080449 : Blo 730325 24080449 := bstep (se 2 (by rfl) ⟨9030168, by rfl⟩ : syracuseStep 24080449 = 18060337) B18060337
theorem B2781287 : Blo 730325 2781287 := bstep (se 1 (by rfl) ⟨2085965, by rfl⟩ : syracuseStep 2781287 = 4171931) B4171931
theorem B3338653 : Blo 730325 3338653 := bstep (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) B1251995
theorem B15463001 : Blo 730325 15463001 := bstep (se 2 (by rfl) ⟨5798625, by rfl⟩ : syracuseStep 15463001 = 11597251) B11597251
theorem B10580615 : Blo 730325 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B6256187 : Blo 730325 6256187 := bstep (se 1 (by rfl) ⟨4692140, by rfl⟩ : syracuseStep 6256187 = 9384281) B9384281
theorem B160495181 : Blo 730325 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B14088107 : Blo 730325 14088107 := bstep (se 1 (by rfl) ⟨10566080, by rfl⟩ : syracuseStep 14088107 = 21132161) B21132161
theorem B2783915 : Blo 730325 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B4160267 : Blo 730325 4160267 := bstep (se 1 (by rfl) ⟨3120200, by rfl⟩ : syracuseStep 4160267 = 6240401) B6240401
theorem B9403553 : Blo 730325 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B3342007 : Blo 730325 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B11271889 : Blo 730325 11271889 := bstep (se 2 (by rfl) ⟨4226958, by rfl⟩ : syracuseStep 11271889 = 8453917) B8453917
theorem B8323721 : Blo 730325 8323721 := bstep (se 2 (by rfl) ⟨3121395, by rfl⟩ : syracuseStep 8323721 = 6242791) B6242791
theorem B3705587 : Blo 730325 3705587 := bstep (se 1 (by rfl) ⟨2779190, by rfl⟩ : syracuseStep 3705587 = 5558381) B5558381
theorem B822271 : Blo 730325 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B3706559 : Blo 730325 3706559 := bstep (se 1 (by rfl) ⟨2779919, by rfl⟩ : syracuseStep 3706559 = 5559839) B5559839
theorem B822991 : Blo 730325 822991 := bstep (se 1 (by rfl) ⟨617243, by rfl⟩ : syracuseStep 822991 = 1234487) B1234487
theorem B987079 : Blo 730325 987079 := bstep (se 1 (by rfl) ⟨740309, by rfl⟩ : syracuseStep 987079 = 1480619) B1480619
theorem B7049591 : Blo 730325 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B823711 : Blo 730325 823711 := bstep (se 1 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 823711 = 1235567) B1235567
theorem B823999 : Blo 730325 823999 := bstep (se 1 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 823999 = 1235999) B1235999
theorem B1545247 : Blo 730325 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B824575 : Blo 730325 824575 := bstep (se 1 (by rfl) ⟨618431, by rfl⟩ : syracuseStep 824575 = 1236863) B1236863
theorem B1643831 : Blo 730325 1643831 := bstep (se 1 (by rfl) ⟨1232873, by rfl⟩ : syracuseStep 1643831 = 2465747) B2465747
theorem B1643903 : Blo 730325 1643903 := bstep (se 1 (by rfl) ⟨1232927, by rfl⟩ : syracuseStep 1643903 = 2465855) B2465855
theorem B14096105 : Blo 730325 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B21370817 : Blo 730325 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B4462775 : Blo 730325 4462775 := bstep (se 1 (by rfl) ⟨3347081, by rfl⟩ : syracuseStep 4462775 = 6694163) B6694163
theorem B2824379 : Blo 730325 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B1481503 : Blo 730325 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B1645415 : Blo 730325 1645415 := bstep (se 1 (by rfl) ⟨1234061, by rfl⟩ : syracuseStep 1645415 = 2468123) B2468123
theorem B1645523 : Blo 730325 1645523 := bstep (se 1 (by rfl) ⟨1234142, by rfl⟩ : syracuseStep 1645523 = 2468285) B2468285
theorem B11869199 : Blo 730325 11869199 := bstep (se 1 (by rfl) ⟨8901899, by rfl⟩ : syracuseStep 11869199 = 17803799) B17803799
theorem B2464937 : Blo 730325 2464937 := bstep (se 2 (by rfl) ⟨924351, by rfl⟩ : syracuseStep 2464937 = 1848703) B1848703
theorem B1318123 : Blo 730325 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B20061593 : Blo 730325 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B2825855 : Blo 730325 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B1875611 : Blo 730325 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B7053281 : Blo 730325 7053281 := bstep (se 2 (by rfl) ⟨2644980, by rfl⟩ : syracuseStep 7053281 = 5289961) B5289961
theorem B1974395 : Blo 730325 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B7053743 : Blo 730325 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B4170791 : Blo 730325 4170791 := bstep (se 1 (by rfl) ⟨3128093, by rfl⟩ : syracuseStep 4170791 = 6256187) B6256187
theorem B1287209 : Blo 730325 1287209 := bstep (se 2 (by rfl) ⟨482703, by rfl⟩ : syracuseStep 1287209 = 965407) B965407
theorem B106996787 : Blo 730325 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B1647827 : Blo 730325 1647827 := bstep (se 1 (by rfl) ⟨1235870, by rfl⟩ : syracuseStep 1647827 = 2471741) B2471741
theorem B730367 : Blo 730325 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B730599 : Blo 730325 730599 := bstep (se 1 (by rfl) ⟨547949, by rfl⟩ : syracuseStep 730599 = 1095899) B1095899
theorem B730783 : Blo 730325 730783 := bstep (se 1 (by rfl) ⟨548087, by rfl⟩ : syracuseStep 730783 = 1096175) B1096175
theorem B730983 : Blo 730325 730983 := bstep (se 1 (by rfl) ⟨548237, by rfl⟩ : syracuseStep 730983 = 1096475) B1096475
theorem B731239 : Blo 730325 731239 := bstep (se 1 (by rfl) ⟨548429, by rfl⟩ : syracuseStep 731239 = 1096859) B1096859
theorem B6269035 : Blo 730325 6269035 := bstep (se 1 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 6269035 = 9403553) B9403553
theorem B731375 : Blo 730325 731375 := bstep (se 1 (by rfl) ⟨548531, by rfl⟩ : syracuseStep 731375 = 1097063) B1097063
theorem B1387135 : Blo 730325 1387135 := bstep (se 1 (by rfl) ⟨1040351, by rfl⟩ : syracuseStep 1387135 = 2080703) B2080703
theorem B731807 : Blo 730325 731807 := bstep (se 1 (by rfl) ⟨548855, by rfl⟩ : syracuseStep 731807 = 1097711) B1097711
theorem B731815 : Blo 730325 731815 := bstep (se 1 (by rfl) ⟨548861, by rfl⟩ : syracuseStep 731815 = 1097723) B1097723
theorem B3713849 : Blo 730325 3713849 := bstep (se 2 (by rfl) ⟨1392693, by rfl⟩ : syracuseStep 3713849 = 2785387) B2785387
theorem B12496517 : Blo 730325 12496517 := bstep (se 4 (by rfl) ⟨1171548, by rfl⟩ : syracuseStep 12496517 = 2343097) B2343097
theorem B732831 : Blo 730325 732831 := bstep (se 1 (by rfl) ⟨549623, by rfl⟩ : syracuseStep 732831 = 1099247) B1099247
theorem B733087 : Blo 730325 733087 := bstep (se 1 (by rfl) ⟨549815, by rfl⟩ : syracuseStep 733087 = 1099631) B1099631
theorem B5550119 : Blo 730325 5550119 := bstep (se 1 (by rfl) ⟨4162589, by rfl⟩ : syracuseStep 5550119 = 8325179) B8325179
theorem B733255 : Blo 730325 733255 := bstep (se 1 (by rfl) ⟨549941, by rfl⟩ : syracuseStep 733255 = 1099883) B1099883
theorem B733275 : Blo 730325 733275 := bstep (se 1 (by rfl) ⟨549956, by rfl⟩ : syracuseStep 733275 = 1099913) B1099913
theorem B733375 : Blo 730325 733375 := bstep (se 1 (by rfl) ⟨550031, by rfl⟩ : syracuseStep 733375 = 1100063) B1100063
theorem B41234669 : Blo 730325 41234669 := bstep (se 3 (by rfl) ⟨7731500, by rfl⟩ : syracuseStep 41234669 = 15463001) B15463001
theorem B733423 : Blo 730325 733423 := bstep (se 1 (by rfl) ⟨550067, by rfl⟩ : syracuseStep 733423 = 1100135) B1100135
theorem B1651067 : Blo 730325 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B1651391 : Blo 730325 1651391 := bstep (se 1 (by rfl) ⟨1238543, by rfl⟩ : syracuseStep 1651391 = 2477087) B2477087
theorem B1389793 : Blo 730325 1389793 := bstep (se 2 (by rfl) ⟨521172, by rfl⟩ : syracuseStep 1389793 = 1042345) B1042345
theorem B1848815 : Blo 730325 1848815 := bstep (se 1 (by rfl) ⟨1386611, by rfl⟩ : syracuseStep 1848815 = 2773223) B2773223
theorem B2504317 : Blo 730325 2504317 := bstep (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) B939119
theorem B1849655 : Blo 730325 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B1096703 : Blo 730325 1096703 := bstep (se 1 (by rfl) ⟨822527, by rfl⟩ : syracuseStep 1096703 = 1645055) B1645055
theorem B22527017 : Blo 730325 22527017 := bstep (se 2 (by rfl) ⟨8447631, by rfl⟩ : syracuseStep 22527017 = 16895263) B16895263
theorem B1096799 : Blo 730325 1096799 := bstep (se 1 (by rfl) ⟨822599, by rfl⟩ : syracuseStep 1096799 = 1645199) B1645199
theorem B1096811 : Blo 730325 1096811 := bstep (se 1 (by rfl) ⟨822608, by rfl⟩ : syracuseStep 1096811 = 1645217) B1645217
theorem B3129529 : Blo 730325 3129529 := bstep (se 2 (by rfl) ⟨1173573, by rfl⟩ : syracuseStep 3129529 = 2347147) B2347147
theorem B1098527 : Blo 730325 1098527 := bstep (se 1 (by rfl) ⟨823895, by rfl⟩ : syracuseStep 1098527 = 1647791) B1647791
theorem B1098623 : Blo 730325 1098623 := bstep (se 1 (by rfl) ⟨823967, by rfl⟩ : syracuseStep 1098623 = 1647935) B1647935
theorem B1098731 : Blo 730325 1098731 := bstep (se 1 (by rfl) ⟨824048, by rfl⟩ : syracuseStep 1098731 = 1648097) B1648097
theorem B4703827 : Blo 730325 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B837359 : Blo 730325 837359 := bstep (se 1 (by rfl) ⟨628019, by rfl⟩ : syracuseStep 837359 = 1256039) B1256039
theorem B2476331 : Blo 730325 2476331 := bstep (se 1 (by rfl) ⟨1857248, by rfl⟩ : syracuseStep 2476331 = 3714497) B3714497
theorem B1100231 : Blo 730325 1100231 := bstep (se 1 (by rfl) ⟨825173, by rfl⟩ : syracuseStep 1100231 = 1650347) B1650347
theorem B1854191 : Blo 730325 1854191 := bstep (se 1 (by rfl) ⟨1390643, by rfl⟩ : syracuseStep 1854191 = 2781287) B2781287
theorem B3525565 : Blo 730325 3525565 := bstep (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) B1322087
theorem B1100777 : Blo 730325 1100777 := bstep (se 2 (by rfl) ⟨412791, by rfl⟩ : syracuseStep 1100777 = 825583) B825583
theorem B3526163 : Blo 730325 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B14274089 : Blo 730325 14274089 := bstep (se 2 (by rfl) ⟨5352783, by rfl⟩ : syracuseStep 14274089 = 10705567) B10705567
theorem B1101383 : Blo 730325 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B1101479 : Blo 730325 1101479 := bstep (se 1 (by rfl) ⟨826109, by rfl⟩ : syracuseStep 1101479 = 1652219) B1652219
theorem B9392071 : Blo 730325 9392071 := bstep (se 1 (by rfl) ⟨7044053, by rfl⟩ : syracuseStep 9392071 = 14088107) B14088107
theorem B1855943 : Blo 730325 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B2773511 : Blo 730325 2773511 := bstep (se 1 (by rfl) ⟨2080133, by rfl⟩ : syracuseStep 2773511 = 4160267) B4160267
theorem B1757825 : Blo 730325 1757825 := bstep (se 2 (by rfl) ⟨659184, by rfl⟩ : syracuseStep 1757825 = 1318369) B1318369
theorem B3527297 : Blo 730325 3527297 := bstep (se 2 (by rfl) ⟨1322736, by rfl⟩ : syracuseStep 3527297 = 2645473) B2645473
theorem B6247165 : Blo 730325 6247165 := bstep (se 3 (by rfl) ⟨1171343, by rfl⟩ : syracuseStep 6247165 = 2342687) B2342687
theorem B2085659 : Blo 730325 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B1233785 : Blo 730325 1233785 := bstep (se 2 (by rfl) ⟨462669, by rfl⟩ : syracuseStep 1233785 = 925339) B925339
theorem B15029185 : Blo 730325 15029185 := bstep (se 2 (by rfl) ⟨5635944, by rfl⟩ : syracuseStep 15029185 = 11271889) B11271889
theorem B1234399 : Blo 730325 1234399 := bstep (se 1 (by rfl) ⟨925799, by rfl⟩ : syracuseStep 1234399 = 1851599) B1851599
theorem B4216411 : Blo 730325 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1857127 : Blo 730325 1857127 := bstep (se 1 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 1857127 = 2785691) B2785691
theorem B3135611 : Blo 730325 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B2310757303 : Blo 730325 2310757303 := bstep (se 1 (by rfl) ⟨1733067977, by rfl⟩ : syracuseStep 2310757303 = 3466135955) B3466135955
theorem B2088175 : Blo 730325 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B25386689 : Blo 730325 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B3956617 : Blo 730325 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B1237099 : Blo 730325 1237099 := bstep (se 1 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 1237099 = 1855649) B1855649
theorem B1564859 : Blo 730325 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B1335935 : Blo 730325 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B26763959 : Blo 730325 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B21128471 : Blo 730325 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B6677959 : Blo 730325 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B1238591 : Blo 730325 1238591 := bstep (se 1 (by rfl) ⟨928943, by rfl⟩ : syracuseStep 1238591 = 1857887) B1857887
theorem B878239 : Blo 730325 878239 := bstep (se 1 (by rfl) ⟨658679, by rfl⟩ : syracuseStep 878239 = 1317359) B1317359
theorem B1762975 : Blo 730325 1762975 := bstep (se 1 (by rfl) ⟨1322231, by rfl⟩ : syracuseStep 1762975 = 2644463) B2644463
theorem B1238719 : Blo 730325 1238719 := bstep (se 1 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 1238719 = 1858079) B1858079
theorem B1239151 : Blo 730325 1239151 := bstep (se 1 (by rfl) ⟨929363, by rfl⟩ : syracuseStep 1239151 = 1858727) B1858727
theorem B32107265 : Blo 730325 32107265 := bstep (se 2 (by rfl) ⟨12040224, by rfl⟩ : syracuseStep 32107265 = 24080449) B24080449
theorem B4680659 : Blo 730325 4680659 := bstep (se 1 (by rfl) ⟨3510494, by rfl⟩ : syracuseStep 4680659 = 7020989) B7020989
theorem B2780315 : Blo 730325 2780315 := bstep (se 1 (by rfl) ⟨2085236, by rfl⟩ : syracuseStep 2780315 = 4170473) B4170473
theorem B4451537 : Blo 730325 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B23752925 : Blo 730325 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B5010281 : Blo 730325 5010281 := bstep (se 2 (by rfl) ⟨1878855, by rfl⟩ : syracuseStep 5010281 = 3757711) B3757711
theorem B5273353 : Blo 730325 5273353 := bstep (se 2 (by rfl) ⟨1977507, by rfl⟩ : syracuseStep 5273353 = 3955015) B3955015
theorem B4456009 : Blo 730325 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B8358713 : Blo 730325 8358713 := bstep (se 2 (by rfl) ⟨3134517, by rfl⟩ : syracuseStep 8358713 = 6269035) B6269035
theorem B822523 : Blo 730325 822523 := bstep (se 1 (by rfl) ⟨616892, by rfl⟩ : syracuseStep 822523 = 1233785) B1233785
theorem B1643291 : Blo 730325 1643291 := bstep (se 1 (by rfl) ⟨1232468, by rfl⟩ : syracuseStep 1643291 = 2464937) B2464937
theorem B13374395 : Blo 730325 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B1250407 : Blo 730325 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B56988845 : Blo 730325 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B1316105 : Blo 730325 1316105 := bstep (se 2 (by rfl) ⟨493539, by rfl⟩ : syracuseStep 1316105 = 987079) B987079
theorem B12522761 : Blo 730325 12522761 := bstep (se 2 (by rfl) ⟨4696035, by rfl⟩ : syracuseStep 12522761 = 9392071) B9392071
theorem B1316263 : Blo 730325 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B8361629 : Blo 730325 8361629 := bstep (se 3 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 8361629 = 3135611) B3135611
theorem B890623 : Blo 730325 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B8329553 : Blo 730325 8329553 := bstep (se 2 (by rfl) ⟨3123582, by rfl⟩ : syracuseStep 8329553 = 6247165) B6247165
theorem B825727 : Blo 730325 825727 := bstep (se 1 (by rfl) ⟨619295, by rfl⟩ : syracuseStep 825727 = 1238591) B1238591
theorem B21404843 : Blo 730325 21404843 := bstep (se 1 (by rfl) ⟨16053632, by rfl⟩ : syracuseStep 21404843 = 32107265) B32107265
theorem B1645865 : Blo 730325 1645865 := bstep (se 2 (by rfl) ⟨617199, by rfl⟩ : syracuseStep 1645865 = 1234399) B1234399
theorem B3120439 : Blo 730325 3120439 := bstep (se 1 (by rfl) ⟨2340329, by rfl⟩ : syracuseStep 3120439 = 4680659) B4680659
theorem B8331011 : Blo 730325 8331011 := bstep (se 1 (by rfl) ⟨6248258, by rfl⟩ : syracuseStep 8331011 = 12496517) B12496517
theorem B15835283 : Blo 730325 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B1975337 : Blo 730325 1975337 := bstep (se 2 (by rfl) ⟨740751, by rfl⟩ : syracuseStep 1975337 = 1481503) B1481503
theorem B731135 : Blo 730325 731135 := bstep (se 1 (by rfl) ⟨548351, by rfl⟩ : syracuseStep 731135 = 1096703) B1096703
theorem B15018011 : Blo 730325 15018011 := bstep (se 1 (by rfl) ⟨11263508, by rfl⟩ : syracuseStep 15018011 = 22527017) B22527017
theorem B731199 : Blo 730325 731199 := bstep (se 1 (by rfl) ⟨548399, by rfl⟩ : syracuseStep 731199 = 1096799) B1096799
theorem B731207 : Blo 730325 731207 := bstep (se 1 (by rfl) ⟨548405, by rfl⟩ : syracuseStep 731207 = 1096811) B1096811
theorem B5941345 : Blo 730325 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B1649465 : Blo 730325 1649465 := bstep (se 2 (by rfl) ⟨618549, by rfl⟩ : syracuseStep 1649465 = 1237099) B1237099
theorem B4172705 : Blo 730325 4172705 := bstep (se 2 (by rfl) ⟨1564764, by rfl⟩ : syracuseStep 4172705 = 3129529) B3129529
theorem B5549147 : Blo 730325 5549147 := bstep (se 1 (by rfl) ⟨4161860, by rfl⟩ : syracuseStep 5549147 = 8323721) B8323721
theorem B4172957 : Blo 730325 4172957 := bstep (se 3 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 4172957 = 1564859) B1564859
theorem B732351 : Blo 730325 732351 := bstep (se 1 (by rfl) ⟨549263, by rfl⟩ : syracuseStep 732351 = 1098527) B1098527
theorem B732415 : Blo 730325 732415 := bstep (se 1 (by rfl) ⟨549311, by rfl⟩ : syracuseStep 732415 = 1098623) B1098623
theorem B732487 : Blo 730325 732487 := bstep (se 1 (by rfl) ⟨549365, by rfl⟩ : syracuseStep 732487 = 1098731) B1098731
theorem B1650887 : Blo 730325 1650887 := bstep (se 1 (by rfl) ⟨1238165, by rfl⟩ : syracuseStep 1650887 = 2476331) B2476331
theorem B733487 : Blo 730325 733487 := bstep (se 1 (by rfl) ⟨550115, by rfl⟩ : syracuseStep 733487 = 1100231) B1100231
theorem B2470391 : Blo 730325 2470391 := bstep (se 1 (by rfl) ⟨1852793, by rfl⟩ : syracuseStep 2470391 = 3705587) B3705587
theorem B733851 : Blo 730325 733851 := bstep (se 1 (by rfl) ⟨550388, by rfl⟩ : syracuseStep 733851 = 1100777) B1100777
theorem B6271769 : Blo 730325 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B1651625 : Blo 730325 1651625 := bstep (se 2 (by rfl) ⟨619359, by rfl⟩ : syracuseStep 1651625 = 1238719) B1238719
theorem B9516059 : Blo 730325 9516059 := bstep (se 1 (by rfl) ⟨7137044, by rfl⟩ : syracuseStep 9516059 = 14274089) B14274089
theorem B734255 : Blo 730325 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B734319 : Blo 730325 734319 := bstep (se 1 (by rfl) ⟨550739, by rfl⟩ : syracuseStep 734319 = 1101479) B1101479
theorem B2471039 : Blo 730325 2471039 := bstep (se 1 (by rfl) ⟨1853279, by rfl⟩ : syracuseStep 2471039 = 3706559) B3706559
theorem B1652201 : Blo 730325 1652201 := bstep (se 2 (by rfl) ⟨619575, by rfl⟩ : syracuseStep 1652201 = 1239151) B1239151
theorem B4699727 : Blo 730325 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B1849007 : Blo 730325 1849007 := bstep (se 1 (by rfl) ⟨1386755, by rfl⟩ : syracuseStep 1849007 = 2773511) B2773511
theorem B1390439 : Blo 730325 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B1849513 : Blo 730325 1849513 := bstep (se 2 (by rfl) ⟨693567, by rfl⟩ : syracuseStep 1849513 = 1387135) B1387135
theorem B1095887 : Blo 730325 1095887 := bstep (se 1 (by rfl) ⟨821915, by rfl⟩ : syracuseStep 1095887 = 1643831) B1643831
theorem B1095935 : Blo 730325 1095935 := bstep (se 1 (by rfl) ⟨821951, by rfl⟩ : syracuseStep 1095935 = 1643903) B1643903
theorem B4700753 : Blo 730325 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B1096361 : Blo 730325 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B1882919 : Blo 730325 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B1096943 : Blo 730325 1096943 := bstep (se 1 (by rfl) ⟨822707, by rfl⟩ : syracuseStep 1096943 = 1645415) B1645415
theorem B1097015 : Blo 730325 1097015 := bstep (se 1 (by rfl) ⟨822761, by rfl⟩ : syracuseStep 1097015 = 1645523) B1645523
theorem B7912799 : Blo 730325 7912799 := bstep (se 1 (by rfl) ⟨5934599, by rfl⟩ : syracuseStep 7912799 = 11869199) B11869199
theorem B1097321 : Blo 730325 1097321 := bstep (se 2 (by rfl) ⟨411495, by rfl⟩ : syracuseStep 1097321 = 822991) B822991
theorem B1883903 : Blo 730325 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B16924459 : Blo 730325 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B4702187 : Blo 730325 4702187 := bstep (se 1 (by rfl) ⟨3526640, by rfl⟩ : syracuseStep 4702187 = 7053281) B7053281
theorem B4702495 : Blo 730325 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B17842639 : Blo 730325 17842639 := bstep (se 1 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 17842639 = 26763959) B26763959
theorem B1098281 : Blo 730325 1098281 := bstep (se 2 (by rfl) ⟨411855, by rfl⟩ : syracuseStep 1098281 = 823711) B823711
theorem B1098551 : Blo 730325 1098551 := bstep (se 1 (by rfl) ⟨823913, by rfl⟩ : syracuseStep 1098551 = 1647827) B1647827
theorem B1098665 : Blo 730325 1098665 := bstep (se 2 (by rfl) ⟨411999, by rfl⟩ : syracuseStep 1098665 = 823999) B823999
theorem B7029989 : Blo 730325 7029989 := bstep (se 4 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 7029989 = 1318123) B1318123
theorem B20038913 : Blo 730325 20038913 := bstep (se 2 (by rfl) ⟨7514592, by rfl⟩ : syracuseStep 20038913 = 15029185) B15029185
theorem B1853057 : Blo 730325 1853057 := bstep (se 2 (by rfl) ⟨694896, by rfl⟩ : syracuseStep 1853057 = 1389793) B1389793
theorem B1099433 : Blo 730325 1099433 := bstep (se 2 (by rfl) ⟨412287, by rfl⟩ : syracuseStep 1099433 = 824575) B824575
theorem B2475899 : Blo 730325 2475899 := bstep (se 1 (by rfl) ⟨1856924, by rfl⟩ : syracuseStep 2475899 = 3713849) B3713849
theorem B1853543 : Blo 730325 1853543 := bstep (se 1 (by rfl) ⟨1390157, by rfl⟩ : syracuseStep 1853543 = 2780315) B2780315
theorem B5621881 : Blo 730325 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B2476169 : Blo 730325 2476169 := bstep (se 2 (by rfl) ⟨928563, by rfl⟩ : syracuseStep 2476169 = 1857127) B1857127
theorem B2967691 : Blo 730325 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B7031137 : Blo 730325 7031137 := bstep (se 2 (by rfl) ⟨2636676, by rfl⟩ : syracuseStep 7031137 = 5273353) B5273353
theorem B8931829 : Blo 730325 8931829 := bstep (se 5 (by rfl) ⟨418679, by rfl⟩ : syracuseStep 8931829 = 837359) B837359
theorem B1100711 : Blo 730325 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B1100927 : Blo 730325 1100927 := bstep (se 1 (by rfl) ⟨825695, by rfl⟩ : syracuseStep 1100927 = 1651391) B1651391
theorem B1232543 : Blo 730325 1232543 := bstep (se 1 (by rfl) ⟨924407, by rfl⟩ : syracuseStep 1232543 = 1848815) B1848815
theorem B1233103 : Blo 730325 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B1236127 : Blo 730325 1236127 := bstep (se 1 (by rfl) ⟨927095, by rfl⟩ : syracuseStep 1236127 = 1854191) B1854191
theorem B8903945 : Blo 730325 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B1170985 : Blo 730325 1170985 := bstep (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) B878239
theorem B2350633 : Blo 730325 2350633 := bstep (se 2 (by rfl) ⟨881487, by rfl⟩ : syracuseStep 2350633 = 1762975) B1762975
theorem B2350775 : Blo 730325 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B3432557 : Blo 730325 3432557 := bstep (se 3 (by rfl) ⟨643604, by rfl⟩ : syracuseStep 3432557 = 1287209) B1287209
theorem B1237295 : Blo 730325 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B1171883 : Blo 730325 1171883 := bstep (se 1 (by rfl) ⟨878912, by rfl⟩ : syracuseStep 1171883 = 1757825) B1757825
theorem B2351531 : Blo 730325 2351531 := bstep (se 1 (by rfl) ⟨1763648, by rfl⟩ : syracuseStep 2351531 = 3527297) B3527297
theorem B9397403 : Blo 730325 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B2975183 : Blo 730325 2975183 := bstep (se 1 (by rfl) ⟨2231387, by rfl⟩ : syracuseStep 2975183 = 4462775) B4462775
theorem B2780527 : Blo 730325 2780527 := bstep (se 1 (by rfl) ⟨2085395, by rfl⟩ : syracuseStep 2780527 = 4170791) B4170791
theorem B71331191 : Blo 730325 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B14085647 : Blo 730325 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B2060329 : Blo 730325 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B3339089 : Blo 730325 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B3700079 : Blo 730325 3700079 := bstep (se 1 (by rfl) ⟨2775059, by rfl⟩ : syracuseStep 3700079 = 5550119) B5550119
theorem B27489779 : Blo 730325 27489779 := bstep (se 1 (by rfl) ⟨20617334, by rfl⟩ : syracuseStep 27489779 = 41234669) B41234669
theorem B3340187 : Blo 730325 3340187 := bstep (se 1 (by rfl) ⟨2505140, by rfl⟩ : syracuseStep 3340187 = 5010281) B5010281
theorem B3081009737 : Blo 730325 3081009737 := bstep (se 2 (by rfl) ⟨1155378651, by rfl⟩ : syracuseStep 3081009737 = 2310757303) B2310757303
theorem B2784233 : Blo 730325 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B5275489 : Blo 730325 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B23790185 : Blo 730325 23790185 := bstep (se 2 (by rfl) ⟨8921319, by rfl⟩ : syracuseStep 23790185 = 17842639) B17842639
theorem B4686659 : Blo 730325 4686659 := bstep (se 1 (by rfl) ⟨3514994, by rfl⟩ : syracuseStep 4686659 = 7029989) B7029989
theorem B5572475 : Blo 730325 5572475 := bstep (se 1 (by rfl) ⟨4179356, by rfl⟩ : syracuseStep 5572475 = 8358713) B8358713
theorem B821695 : Blo 730325 821695 := bstep (se 1 (by rfl) ⟨616271, by rfl⟩ : syracuseStep 821695 = 1232543) B1232543
theorem B9374849 : Blo 730325 9374849 := bstep (se 2 (by rfl) ⟨3515568, by rfl⟩ : syracuseStep 9374849 = 7031137) B7031137
theorem B8916263 : Blo 730325 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B5574419 : Blo 730325 5574419 := bstep (se 1 (by rfl) ⟨4180814, by rfl⟩ : syracuseStep 5574419 = 8361629) B8361629
theorem B3707369 : Blo 730325 3707369 := bstep (se 2 (by rfl) ⟨1390263, by rfl⟩ : syracuseStep 3707369 = 2780527) B2780527
theorem B5935963 : Blo 730325 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B10556855 : Blo 730325 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B824863 : Blo 730325 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B1644137 : Blo 730325 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B1316891 : Blo 730325 1316891 := bstep (se 1 (by rfl) ⟨987668, by rfl⟩ : syracuseStep 1316891 = 1975337) B1975337
theorem B6264935 : Blo 730325 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B8216025965 : Blo 730325 8216025965 := bstep (se 3 (by rfl) ⟨1540504868, by rfl⟩ : syracuseStep 8216025965 = 3081009737) B3081009737
theorem B47554127 : Blo 730325 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B1187497 : Blo 730325 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B2466017 : Blo 730325 2466017 := bstep (se 2 (by rfl) ⟨924756, by rfl⟩ : syracuseStep 2466017 = 1849513) B1849513
theorem B1646927 : Blo 730325 1646927 := bstep (se 1 (by rfl) ⟨1235195, by rfl⟩ : syracuseStep 1646927 = 2470391) B2470391
theorem B1647359 : Blo 730325 1647359 := bstep (se 1 (by rfl) ⟨1235519, by rfl⟩ : syracuseStep 1647359 = 2471039) B2471039
theorem B2466719 : Blo 730325 2466719 := bstep (se 1 (by rfl) ⟨1850039, by rfl⟩ : syracuseStep 2466719 = 3700079) B3700079
theorem B18326519 : Blo 730325 18326519 := bstep (se 1 (by rfl) ⟨13744889, by rfl⟩ : syracuseStep 18326519 = 27489779) B27489779
theorem B926959 : Blo 730325 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B730591 : Blo 730325 730591 := bstep (se 1 (by rfl) ⟨547943, by rfl⟩ : syracuseStep 730591 = 1095887) B1095887
theorem B730623 : Blo 730325 730623 := bstep (se 1 (by rfl) ⟨547967, by rfl⟩ : syracuseStep 730623 = 1095935) B1095935
theorem B1648169 : Blo 730325 1648169 := bstep (se 2 (by rfl) ⟨618063, by rfl⟩ : syracuseStep 1648169 = 1236127) B1236127
theorem B730907 : Blo 730325 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B1255279 : Blo 730325 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B5023741 : Blo 730325 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B731295 : Blo 730325 731295 := bstep (se 1 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 731295 = 1096943) B1096943
theorem B731343 : Blo 730325 731343 := bstep (se 1 (by rfl) ⟨548507, by rfl⟩ : syracuseStep 731343 = 1097015) B1097015
theorem B731547 : Blo 730325 731547 := bstep (se 1 (by rfl) ⟨548660, by rfl⟩ : syracuseStep 731547 = 1097321) B1097321
theorem B9153485 : Blo 730325 9153485 := bstep (se 3 (by rfl) ⟨1716278, by rfl⟩ : syracuseStep 9153485 = 3432557) B3432557
theorem B732187 : Blo 730325 732187 := bstep (se 1 (by rfl) ⟨549140, by rfl⟩ : syracuseStep 732187 = 1098281) B1098281
theorem B6269993 : Blo 730325 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B732367 : Blo 730325 732367 := bstep (se 1 (by rfl) ⟨549275, by rfl⟩ : syracuseStep 732367 = 1098551) B1098551
theorem B732443 : Blo 730325 732443 := bstep (se 1 (by rfl) ⟨549332, by rfl⟩ : syracuseStep 732443 = 1098665) B1098665
theorem B732955 : Blo 730325 732955 := bstep (se 1 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 732955 = 1099433) B1099433
theorem B1650599 : Blo 730325 1650599 := bstep (se 1 (by rfl) ⟨1237949, by rfl⟩ : syracuseStep 1650599 = 2475899) B2475899
theorem B1650779 : Blo 730325 1650779 := bstep (se 1 (by rfl) ⟨1238084, by rfl⟩ : syracuseStep 1650779 = 2476169) B2476169
theorem B733807 : Blo 730325 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B733951 : Blo 730325 733951 := bstep (se 1 (by rfl) ⟨550463, by rfl⟩ : syracuseStep 733951 = 1100927) B1100927
theorem B1095527 : Blo 730325 1095527 := bstep (se 1 (by rfl) ⟨821645, by rfl⟩ : syracuseStep 1095527 = 1643291) B1643291
theorem B11909105 : Blo 730325 11909105 := bstep (se 2 (by rfl) ⟨4465914, by rfl⟩ : syracuseStep 11909105 = 8931829) B8931829
theorem B37992563 : Blo 730325 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B5553035 : Blo 730325 5553035 := bstep (se 1 (by rfl) ⟨4164776, by rfl⟩ : syracuseStep 5553035 = 8329553) B8329553
theorem B1096697 : Blo 730325 1096697 := bstep (se 2 (by rfl) ⟨411261, by rfl⟩ : syracuseStep 1096697 = 822523) B822523
theorem B14269895 : Blo 730325 14269895 := bstep (se 1 (by rfl) ⟨10702421, by rfl⟩ : syracuseStep 14269895 = 21404843) B21404843
theorem B1097243 : Blo 730325 1097243 := bstep (se 1 (by rfl) ⟨822932, by rfl⟩ : syracuseStep 1097243 = 1645865) B1645865
theorem B5554007 : Blo 730325 5554007 := bstep (se 1 (by rfl) ⟨4165505, by rfl⟩ : syracuseStep 5554007 = 8331011) B8331011
theorem B6668837 : Blo 730325 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B1983455 : Blo 730325 1983455 := bstep (se 1 (by rfl) ⟨1487591, by rfl⟩ : syracuseStep 1983455 = 2975183) B2975183
theorem B10012007 : Blo 730325 10012007 := bstep (se 1 (by rfl) ⟨7509005, by rfl⟩ : syracuseStep 10012007 = 15018011) B15018011
theorem B1099643 : Blo 730325 1099643 := bstep (se 1 (by rfl) ⟨824732, by rfl⟩ : syracuseStep 1099643 = 1649465) B1649465
theorem B1755017 : Blo 730325 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B9390431 : Blo 730325 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B1100591 : Blo 730325 1100591 := bstep (se 1 (by rfl) ⟨825443, by rfl⟩ : syracuseStep 1100591 = 1650887) B1650887
theorem B1100969 : Blo 730325 1100969 := bstep (se 2 (by rfl) ⟨412863, by rfl⟩ : syracuseStep 1100969 = 825727) B825727
theorem B4181179 : Blo 730325 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B1101083 : Blo 730325 1101083 := bstep (se 1 (by rfl) ⟨825812, by rfl⟩ : syracuseStep 1101083 = 1651625) B1651625
theorem B6344039 : Blo 730325 6344039 := bstep (se 1 (by rfl) ⟨4758029, by rfl⟩ : syracuseStep 6344039 = 9516059) B9516059
theorem B1101467 : Blo 730325 1101467 := bstep (se 1 (by rfl) ⟨826100, by rfl⟩ : syracuseStep 1101467 = 1652201) B1652201
theorem B3133151 : Blo 730325 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1232671 : Blo 730325 1232671 := bstep (se 1 (by rfl) ⟨924503, by rfl⟩ : syracuseStep 1232671 = 1849007) B1849007
theorem B3133835 : Blo 730325 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B1856155 : Blo 730325 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B1561313 : Blo 730325 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B3134177 : Blo 730325 3134177 := bstep (se 2 (by rfl) ⟨1175316, by rfl⟩ : syracuseStep 3134177 = 2350633) B2350633
theorem B22565945 : Blo 730325 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B7033985 : Blo 730325 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B3134791 : Blo 730325 3134791 := bstep (se 1 (by rfl) ⟨2351093, by rfl⟩ : syracuseStep 3134791 = 4702187) B4702187
theorem B13359275 : Blo 730325 13359275 := bstep (se 1 (by rfl) ⟨10019456, by rfl⟩ : syracuseStep 13359275 = 20038913) B20038913
theorem B1235371 : Blo 730325 1235371 := bstep (se 1 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 1235371 = 1853057) B1853057
theorem B1235695 : Blo 730325 1235695 := bstep (se 1 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 1235695 = 1853543) B1853543
theorem B7921793 : Blo 730325 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B7495841 : Blo 730325 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B3956921 : Blo 730325 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B877403 : Blo 730325 877403 := bstep (se 1 (by rfl) ⟨658052, by rfl⟩ : syracuseStep 877403 = 1316105) B1316105
theorem B8348507 : Blo 730325 8348507 := bstep (se 1 (by rfl) ⟨6261380, by rfl⟩ : syracuseStep 8348507 = 12522761) B12522761
theorem B1567183 : Blo 730325 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B2747105 : Blo 730325 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B781255 : Blo 730325 781255 := bstep (se 1 (by rfl) ⟨585941, by rfl⟩ : syracuseStep 781255 = 1171883) B1171883
theorem B1567687 : Blo 730325 1567687 := bstep (se 1 (by rfl) ⟨1175765, by rfl⟩ : syracuseStep 1567687 = 2351531) B2351531
theorem B2781803 : Blo 730325 2781803 := bstep (se 1 (by rfl) ⟨2086352, by rfl⟩ : syracuseStep 2781803 = 4172705) B4172705
theorem B3699431 : Blo 730325 3699431 := bstep (se 1 (by rfl) ⟨2774573, by rfl⟩ : syracuseStep 3699431 = 5549147) B5549147
theorem B2781971 : Blo 730325 2781971 := bstep (se 1 (by rfl) ⟨2086478, by rfl⟩ : syracuseStep 2781971 = 4172957) B4172957
theorem B2226059 : Blo 730325 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B2226791 : Blo 730325 2226791 := bstep (se 1 (by rfl) ⟨1670093, by rfl⟩ : syracuseStep 2226791 = 3340187) B3340187
theorem B4160585 : Blo 730325 4160585 := bstep (se 2 (by rfl) ⟨1560219, by rfl⟩ : syracuseStep 4160585 = 3120439) B3120439
theorem B5275199 : Blo 730325 5275199 := bstep (se 1 (by rfl) ⟨3956399, by rfl⟩ : syracuseStep 5275199 = 7912799) B7912799
theorem B15860123 : Blo 730325 15860123 := bstep (se 1 (by rfl) ⟨11895092, by rfl⟩ : syracuseStep 15860123 = 23790185) B23790185
theorem B6260287 : Blo 730325 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B4163501 : Blo 730325 4163501 := bstep (se 3 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 4163501 = 1561313) B1561313
theorem B1673705 : Blo 730325 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B15043963 : Blo 730325 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B4689323 : Blo 730325 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B5574905 : Blo 730325 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B1643561 : Blo 730325 1643561 := bstep (se 2 (by rfl) ⟨616335, by rfl⟩ : syracuseStep 1643561 = 1232671) B1232671
theorem B5281195 : Blo 730325 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B1644011 : Blo 730325 1644011 := bstep (se 1 (by rfl) ⟨1233008, by rfl⟩ : syracuseStep 1644011 = 2466017) B2466017
theorem B1644479 : Blo 730325 1644479 := bstep (se 1 (by rfl) ⟨1233359, by rfl⟩ : syracuseStep 1644479 = 2466719) B2466719
theorem B6102323 : Blo 730325 6102323 := bstep (se 1 (by rfl) ⟨4576742, by rfl⟩ : syracuseStep 6102323 = 9153485) B9153485
theorem B2466287 : Blo 730325 2466287 := bstep (se 1 (by rfl) ⟨1849715, by rfl⟩ : syracuseStep 2466287 = 3699431) B3699431
theorem B1647161 : Blo 730325 1647161 := bstep (se 2 (by rfl) ⟨617685, by rfl⟩ : syracuseStep 1647161 = 1235371) B1235371
theorem B16917437 : Blo 730325 16917437 := bstep (se 3 (by rfl) ⟨3172019, by rfl⟩ : syracuseStep 16917437 = 6344039) B6344039
theorem B1647593 : Blo 730325 1647593 := bstep (se 2 (by rfl) ⟨617847, by rfl⟩ : syracuseStep 1647593 = 1235695) B1235695
theorem B730351 : Blo 730325 730351 := bstep (se 1 (by rfl) ⟨547763, by rfl⟩ : syracuseStep 730351 = 1095527) B1095527
theorem B1484039 : Blo 730325 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B7939403 : Blo 730325 7939403 := bstep (se 1 (by rfl) ⟨5954552, by rfl⟩ : syracuseStep 7939403 = 11909105) B11909105
theorem B1484527 : Blo 730325 1484527 := bstep (se 1 (by rfl) ⟨1113395, by rfl⟩ : syracuseStep 1484527 = 2226791) B2226791
theorem B731131 : Blo 730325 731131 := bstep (se 1 (by rfl) ⟨548348, by rfl⟩ : syracuseStep 731131 = 1096697) B1096697
theorem B1583329 : Blo 730325 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B9513263 : Blo 730325 9513263 := bstep (se 1 (by rfl) ⟨7134947, by rfl⟩ : syracuseStep 9513263 = 14269895) B14269895
theorem B731495 : Blo 730325 731495 := bstep (se 1 (by rfl) ⟨548621, by rfl⟩ : syracuseStep 731495 = 1097243) B1097243
theorem B3516799 : Blo 730325 3516799 := bstep (se 1 (by rfl) ⟨2637599, by rfl⟩ : syracuseStep 3516799 = 5275199) B5275199
theorem B3124439 : Blo 730325 3124439 := bstep (se 1 (by rfl) ⟨2343329, by rfl⟩ : syracuseStep 3124439 = 4686659) B4686659
theorem B1322303 : Blo 730325 1322303 := bstep (se 1 (by rfl) ⟨991727, by rfl⟩ : syracuseStep 1322303 = 1983455) B1983455
theorem B733095 : Blo 730325 733095 := bstep (se 1 (by rfl) ⟨549821, by rfl⟩ : syracuseStep 733095 = 1099643) B1099643
theorem B3714983 : Blo 730325 3714983 := bstep (se 1 (by rfl) ⟨2786237, by rfl⟩ : syracuseStep 3714983 = 5572475) B5572475
theorem B733727 : Blo 730325 733727 := bstep (se 1 (by rfl) ⟨550295, by rfl⟩ : syracuseStep 733727 = 1100591) B1100591
theorem B733979 : Blo 730325 733979 := bstep (se 1 (by rfl) ⟨550484, by rfl⟩ : syracuseStep 733979 = 1100969) B1100969
theorem B734055 : Blo 730325 734055 := bstep (se 1 (by rfl) ⟨550541, by rfl⟩ : syracuseStep 734055 = 1101083) B1101083
theorem B5944175 : Blo 730325 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B2339741 : Blo 730325 2339741 := bstep (se 3 (by rfl) ⟨438701, by rfl⟩ : syracuseStep 2339741 = 877403) B877403
theorem B734311 : Blo 730325 734311 := bstep (se 1 (by rfl) ⟨550733, by rfl⟩ : syracuseStep 734311 = 1101467) B1101467
theorem B3716279 : Blo 730325 3716279 := bstep (se 1 (by rfl) ⟨2787209, by rfl⟩ : syracuseStep 3716279 = 5574419) B5574419
theorem B6698321 : Blo 730325 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B2471579 : Blo 730325 2471579 := bstep (se 1 (by rfl) ⟨1853684, by rfl⟩ : syracuseStep 2471579 = 3707369) B3707369
theorem B1095593 : Blo 730325 1095593 := bstep (se 2 (by rfl) ⟨410847, by rfl⟩ : syracuseStep 1095593 = 821695) B821695
theorem B1096091 : Blo 730325 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B4176623 : Blo 730325 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B5477350643 : Blo 730325 5477350643 := bstep (se 1 (by rfl) ⟨4108012982, by rfl⟩ : syracuseStep 5477350643 = 8216025965) B8216025965
theorem B31702751 : Blo 730325 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B4997227 : Blo 730325 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B2637947 : Blo 730325 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B1097951 : Blo 730325 1097951 := bstep (se 1 (by rfl) ⟨823463, by rfl⟩ : syracuseStep 1097951 = 1646927) B1646927
theorem B1098239 : Blo 730325 1098239 := bstep (se 1 (by rfl) ⟨823679, by rfl⟩ : syracuseStep 1098239 = 1647359) B1647359
theorem B2474873 : Blo 730325 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B1098779 : Blo 730325 1098779 := bstep (se 1 (by rfl) ⟨824084, by rfl⟩ : syracuseStep 1098779 = 1648169) B1648169
theorem B7914617 : Blo 730325 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B4179721 : Blo 730325 4179721 := bstep (se 2 (by rfl) ⟨1567395, by rfl⟩ : syracuseStep 4179721 = 3134791) B3134791
theorem B4179995 : Blo 730325 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B1099817 : Blo 730325 1099817 := bstep (se 2 (by rfl) ⟨412431, by rfl⟩ : syracuseStep 1099817 = 824863) B824863
theorem B1100399 : Blo 730325 1100399 := bstep (se 1 (by rfl) ⟨825299, by rfl⟩ : syracuseStep 1100399 = 1650599) B1650599
theorem B1100519 : Blo 730325 1100519 := bstep (se 1 (by rfl) ⟨825389, by rfl⟩ : syracuseStep 1100519 = 1650779) B1650779
theorem B1854535 : Blo 730325 1854535 := bstep (se 1 (by rfl) ⟨1390901, by rfl⟩ : syracuseStep 1854535 = 2781803) B2781803
theorem B1854647 : Blo 730325 1854647 := bstep (se 1 (by rfl) ⟨1390985, by rfl⟩ : syracuseStep 1854647 = 2781971) B2781971
theorem B2773723 : Blo 730325 2773723 := bstep (se 1 (by rfl) ⟨2080292, by rfl⟩ : syracuseStep 2773723 = 4160585) B4160585
theorem B4445891 : Blo 730325 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B6674671 : Blo 730325 6674671 := bstep (se 1 (by rfl) ⟨5006003, by rfl⟩ : syracuseStep 6674671 = 10012007) B10012007
theorem B1170011 : Blo 730325 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1235945 : Blo 730325 1235945 := bstep (se 2 (by rfl) ⟨463479, by rfl⟩ : syracuseStep 1235945 = 926959) B926959
theorem B6249899 : Blo 730325 6249899 := bstep (se 1 (by rfl) ⟨4687424, by rfl⟩ : syracuseStep 6249899 = 9374849) B9374849
theorem B2088767 : Blo 730325 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B2089223 : Blo 730325 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B2089451 : Blo 730325 2089451 := bstep (se 1 (by rfl) ⟨1567088, by rfl⟩ : syracuseStep 2089451 = 3134177) B3134177
theorem B2089577 : Blo 730325 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B7037903 : Blo 730325 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B1041673 : Blo 730325 1041673 := bstep (se 2 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 1041673 = 781255) B781255
theorem B2090249 : Blo 730325 2090249 := bstep (se 2 (by rfl) ⟨783843, by rfl⟩ : syracuseStep 2090249 = 1567687) B1567687
theorem B877927 : Blo 730325 877927 := bstep (se 1 (by rfl) ⟨658445, by rfl⟩ : syracuseStep 877927 = 1316891) B1316891
theorem B8906183 : Blo 730325 8906183 := bstep (se 1 (by rfl) ⟨6679637, by rfl⟩ : syracuseStep 8906183 = 13359275) B13359275
theorem B5565671 : Blo 730325 5565671 := bstep (se 1 (by rfl) ⟨4174253, by rfl⟩ : syracuseStep 5565671 = 8348507) B8348507
theorem B12217679 : Blo 730325 12217679 := bstep (se 1 (by rfl) ⟨9163259, by rfl⟩ : syracuseStep 12217679 = 18326519) B18326519
theorem B1831403 : Blo 730325 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B25328375 : Blo 730325 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B3702023 : Blo 730325 3702023 := bstep (se 1 (by rfl) ⟨2776517, by rfl⟩ : syracuseStep 3702023 = 5553035) B5553035
theorem B3702671 : Blo 730325 3702671 := bstep (se 1 (by rfl) ⟨2777003, by rfl⟩ : syracuseStep 3702671 = 5554007) B5554007
theorem B5276411 : Blo 730325 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B2786663 : Blo 730325 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B1115803 : Blo 730325 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B5572961 : Blo 730325 5572961 := bstep (se 2 (by rfl) ⟨2089860, by rfl⟩ : syracuseStep 5572961 = 4179721) B4179721
theorem B4689065 : Blo 730325 4689065 := bstep (se 2 (by rfl) ⟨1758399, by rfl⟩ : syracuseStep 4689065 = 3516799) B3516799
theorem B20058617 : Blo 730325 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B823963 : Blo 730325 823963 := bstep (se 1 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 823963 = 1235945) B1235945
theorem B4068215 : Blo 730325 4068215 := bstep (se 1 (by rfl) ⟨3051161, by rfl⟩ : syracuseStep 4068215 = 6102323) B6102323
theorem B4166599 : Blo 730325 4166599 := bstep (se 1 (by rfl) ⟨3124949, by rfl⟩ : syracuseStep 4166599 = 6249899) B6249899
theorem B1644191 : Blo 730325 1644191 := bstep (se 1 (by rfl) ⟨1233143, by rfl⟩ : syracuseStep 1644191 = 2466287) B2466287
theorem B11278291 : Blo 730325 11278291 := bstep (se 1 (by rfl) ⟨8458718, by rfl⟩ : syracuseStep 11278291 = 16917437) B16917437
theorem B4691935 : Blo 730325 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B5937455 : Blo 730325 5937455 := bstep (se 1 (by rfl) ⟨4453091, by rfl⟩ : syracuseStep 5937455 = 8906183) B8906183
theorem B3120029 : Blo 730325 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B3710447 : Blo 730325 3710447 := bstep (se 1 (by rfl) ⟨2782835, by rfl⟩ : syracuseStep 3710447 = 5565671) B5565671
theorem B1220935 : Blo 730325 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B4465547 : Blo 730325 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B1647719 : Blo 730325 1647719 := bstep (se 1 (by rfl) ⟨1235789, by rfl⟩ : syracuseStep 1647719 = 2471579) B2471579
theorem B730395 : Blo 730325 730395 := bstep (se 1 (by rfl) ⟨547796, by rfl⟩ : syracuseStep 730395 = 1095593) B1095593
theorem B730727 : Blo 730325 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B16885583 : Blo 730325 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B2468015 : Blo 730325 2468015 := bstep (se 1 (by rfl) ⟨1851011, by rfl⟩ : syracuseStep 2468015 = 3702023) B3702023
theorem B2468447 : Blo 730325 2468447 := bstep (se 1 (by rfl) ⟨1851335, by rfl⟩ : syracuseStep 2468447 = 3702671) B3702671
theorem B6662969 : Blo 730325 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B731967 : Blo 730325 731967 := bstep (se 1 (by rfl) ⟨548975, by rfl⟩ : syracuseStep 731967 = 1097951) B1097951
theorem B732159 : Blo 730325 732159 := bstep (se 1 (by rfl) ⟨549119, by rfl⟩ : syracuseStep 732159 = 1098239) B1098239
theorem B1649915 : Blo 730325 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B732519 : Blo 730325 732519 := bstep (se 1 (by rfl) ⟨549389, by rfl⟩ : syracuseStep 732519 = 1098779) B1098779
theorem B733211 : Blo 730325 733211 := bstep (se 1 (by rfl) ⟨549908, by rfl⟩ : syracuseStep 733211 = 1099817) B1099817
theorem B1388897 : Blo 730325 1388897 := bstep (se 2 (by rfl) ⟨520836, by rfl⟩ : syracuseStep 1388897 = 1041673) B1041673
theorem B733599 : Blo 730325 733599 := bstep (se 1 (by rfl) ⟨550199, by rfl⟩ : syracuseStep 733599 = 1100399) B1100399
theorem B733679 : Blo 730325 733679 := bstep (se 1 (by rfl) ⟨550259, by rfl⟩ : syracuseStep 733679 = 1100519) B1100519
theorem B3126215 : Blo 730325 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B1979369 : Blo 730325 1979369 := bstep (se 2 (by rfl) ⟨742263, by rfl⟩ : syracuseStep 1979369 = 1484527) B1484527
theorem B3716603 : Blo 730325 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B2111105 : Blo 730325 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B1095707 : Blo 730325 1095707 := bstep (se 1 (by rfl) ⟨821780, by rfl⟩ : syracuseStep 1095707 = 1643561) B1643561
theorem B1096007 : Blo 730325 1096007 := bstep (se 1 (by rfl) ⟨822005, by rfl⟩ : syracuseStep 1096007 = 1644011) B1644011
theorem B2963927 : Blo 730325 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B1096319 : Blo 730325 1096319 := bstep (se 1 (by rfl) ⟨822239, by rfl⟩ : syracuseStep 1096319 = 1644479) B1644479
theorem B2472713 : Blo 730325 2472713 := bstep (se 2 (by rfl) ⟨927267, by rfl⟩ : syracuseStep 2472713 = 1854535) B1854535
theorem B1392815 : Blo 730325 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B1392967 : Blo 730325 1392967 := bstep (se 1 (by rfl) ⟨1044725, by rfl⟩ : syracuseStep 1392967 = 2089451) B2089451
theorem B1098107 : Blo 730325 1098107 := bstep (se 1 (by rfl) ⟨823580, by rfl⟩ : syracuseStep 1098107 = 1647161) B1647161
theorem B1393051 : Blo 730325 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B1098395 : Blo 730325 1098395 := bstep (se 1 (by rfl) ⟨823796, by rfl⟩ : syracuseStep 1098395 = 1647593) B1647593
theorem B1393499 : Blo 730325 1393499 := bstep (se 1 (by rfl) ⟨1045124, by rfl⟩ : syracuseStep 1393499 = 2090249) B2090249
theorem B5292935 : Blo 730325 5292935 := bstep (se 1 (by rfl) ⟨3969701, by rfl⟩ : syracuseStep 5292935 = 7939403) B7939403
theorem B6342175 : Blo 730325 6342175 := bstep (se 1 (by rfl) ⟨4756631, by rfl⟩ : syracuseStep 6342175 = 9513263) B9513263
theorem B2082959 : Blo 730325 2082959 := bstep (se 1 (by rfl) ⟨1562219, by rfl⟩ : syracuseStep 2082959 = 3124439) B3124439
theorem B8145119 : Blo 730325 8145119 := bstep (se 1 (by rfl) ⟨6108839, by rfl⟩ : syracuseStep 8145119 = 12217679) B12217679
theorem B2476655 : Blo 730325 2476655 := bstep (se 1 (by rfl) ⟨1857491, by rfl⟩ : syracuseStep 2476655 = 3714983) B3714983
theorem B8899561 : Blo 730325 8899561 := bstep (se 2 (by rfl) ⟨3337335, by rfl⟩ : syracuseStep 8899561 = 6674671) B6674671
theorem B1559827 : Blo 730325 1559827 := bstep (se 1 (by rfl) ⟨1169870, by rfl⟩ : syracuseStep 1559827 = 2339741) B2339741
theorem B2477519 : Blo 730325 2477519 := bstep (se 1 (by rfl) ⟨1858139, by rfl⟩ : syracuseStep 2477519 = 3716279) B3716279
theorem B3526141 : Blo 730325 3526141 := bstep (se 3 (by rfl) ⟨661151, by rfl⟩ : syracuseStep 3526141 = 1322303) B1322303
theorem B1758631 : Blo 730325 1758631 := bstep (se 1 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 1758631 = 2637947) B2637947
theorem B10573415 : Blo 730325 10573415 := bstep (se 1 (by rfl) ⟨7930061, by rfl⟩ : syracuseStep 10573415 = 15860123) B15860123
theorem B2775667 : Blo 730325 2775667 := bstep (se 1 (by rfl) ⟨2081750, by rfl⟩ : syracuseStep 2775667 = 4163501) B4163501
theorem B1170569 : Blo 730325 1170569 := bstep (se 2 (by rfl) ⟨438963, by rfl⟩ : syracuseStep 1170569 = 877927) B877927
theorem B8347049 : Blo 730325 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B1236431 : Blo 730325 1236431 := bstep (se 1 (by rfl) ⟨927323, by rfl⟩ : syracuseStep 1236431 = 1854647) B1854647
theorem B3957437 : Blo 730325 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B3698297 : Blo 730325 3698297 := bstep (se 2 (by rfl) ⟨1386861, by rfl⟩ : syracuseStep 3698297 = 2773723) B2773723
theorem B7041593 : Blo 730325 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B3962783 : Blo 730325 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B2784415 : Blo 730325 2784415 := bstep (se 1 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 2784415 = 4176623) B4176623
theorem B3651567095 : Blo 730325 3651567095 := bstep (se 1 (by rfl) ⟨2738675321, by rfl⟩ : syracuseStep 3651567095 = 5477350643) B5477350643
theorem B5570045 : Blo 730325 5570045 := bstep (se 3 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 5570045 = 2088767) B2088767
theorem B21135167 : Blo 730325 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B18777581 : Blo 730325 18777581 := bstep (se 3 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 18777581 = 7041593) B7041593
theorem B10553165 : Blo 730325 10553165 := bstep (se 3 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 10553165 = 3957437) B3957437
theorem B8456233 : Blo 730325 8456233 := bstep (se 2 (by rfl) ⟨3171087, by rfl⟩ : syracuseStep 8456233 = 6342175) B6342175
theorem B13372411 : Blo 730325 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B7048943 : Blo 730325 7048943 := bstep (se 1 (by rfl) ⟨5286707, by rfl⟩ : syracuseStep 7048943 = 10573415) B10573415
theorem B824287 : Blo 730325 824287 := bstep (se 1 (by rfl) ⟨618215, by rfl⟩ : syracuseStep 824287 = 1236431) B1236431
theorem B1645343 : Blo 730325 1645343 := bstep (se 1 (by rfl) ⟨1234007, by rfl⟩ : syracuseStep 1645343 = 2468015) B2468015
theorem B1645631 : Blo 730325 1645631 := bstep (se 1 (by rfl) ⟨1234223, by rfl⟩ : syracuseStep 1645631 = 2468447) B2468447
theorem B2465531 : Blo 730325 2465531 := bstep (se 1 (by rfl) ⟨1849148, by rfl⟩ : syracuseStep 2465531 = 3698297) B3698297
theorem B925931 : Blo 730325 925931 := bstep (se 1 (by rfl) ⟨694448, by rfl⟩ : syracuseStep 925931 = 1388897) B1388897
theorem B3121517 : Blo 730325 3121517 := bstep (se 3 (by rfl) ⟨585284, by rfl⟩ : syracuseStep 3121517 = 1170569) B1170569
theorem B1319579 : Blo 730325 1319579 := bstep (se 1 (by rfl) ⟨989684, by rfl⟩ : syracuseStep 1319579 = 1979369) B1979369
theorem B730471 : Blo 730325 730471 := bstep (se 1 (by rfl) ⟨547853, by rfl⟩ : syracuseStep 730471 = 1095707) B1095707
theorem B3712553 : Blo 730325 3712553 := bstep (se 2 (by rfl) ⟨1392207, by rfl⟩ : syracuseStep 3712553 = 2784415) B2784415
theorem B730671 : Blo 730325 730671 := bstep (se 1 (by rfl) ⟨548003, by rfl⟩ : syracuseStep 730671 = 1096007) B1096007
theorem B1975951 : Blo 730325 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B730879 : Blo 730325 730879 := bstep (se 1 (by rfl) ⟨548159, by rfl⟩ : syracuseStep 730879 = 1096319) B1096319
theorem B1648475 : Blo 730325 1648475 := bstep (se 1 (by rfl) ⟨1236356, by rfl⟩ : syracuseStep 1648475 = 2472713) B2472713
theorem B2434378063 : Blo 730325 2434378063 := bstep (se 1 (by rfl) ⟨1825783547, by rfl⟩ : syracuseStep 2434378063 = 3651567095) B3651567095
theorem B3713363 : Blo 730325 3713363 := bstep (se 1 (by rfl) ⟨2785022, by rfl⟩ : syracuseStep 3713363 = 5570045) B5570045
theorem B732071 : Blo 730325 732071 := bstep (se 1 (by rfl) ⟨549053, by rfl⟩ : syracuseStep 732071 = 1098107) B1098107
theorem B732263 : Blo 730325 732263 := bstep (se 1 (by rfl) ⟨549197, by rfl⟩ : syracuseStep 732263 = 1098395) B1098395
theorem B3714173 : Blo 730325 3714173 := bstep (se 3 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 3714173 = 1392815) B1392815
theorem B3517607 : Blo 730325 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B928999 : Blo 730325 928999 := bstep (se 1 (by rfl) ⟨696749, by rfl⟩ : syracuseStep 928999 = 1393499) B1393499
theorem B1388639 : Blo 730325 1388639 := bstep (se 1 (by rfl) ⟨1041479, by rfl⟩ : syracuseStep 1388639 = 2082959) B2082959
theorem B3715307 : Blo 730325 3715307 := bstep (se 1 (by rfl) ⟨2786480, by rfl⟩ : syracuseStep 3715307 = 5572961) B5572961
theorem B1651103 : Blo 730325 1651103 := bstep (se 1 (by rfl) ⟨1238327, by rfl⟩ : syracuseStep 1651103 = 2476655) B2476655
theorem B3126043 : Blo 730325 3126043 := bstep (se 1 (by rfl) ⟨2344532, by rfl⟩ : syracuseStep 3126043 = 4689065) B4689065
theorem B1487737 : Blo 730325 1487737 := bstep (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) B1115803
theorem B1651679 : Blo 730325 1651679 := bstep (se 1 (by rfl) ⟨1238759, by rfl⟩ : syracuseStep 1651679 = 2477519) B2477519
theorem B1096127 : Blo 730325 1096127 := bstep (se 1 (by rfl) ⟨822095, by rfl⟩ : syracuseStep 1096127 = 1644191) B1644191
theorem B2079769 : Blo 730325 2079769 := bstep (se 2 (by rfl) ⟨779913, by rfl⟩ : syracuseStep 2079769 = 1559827) B1559827
theorem B2080019 : Blo 730325 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B4701521 : Blo 730325 4701521 := bstep (se 2 (by rfl) ⟨1763070, by rfl⟩ : syracuseStep 4701521 = 3526141) B3526141
theorem B2473631 : Blo 730325 2473631 := bstep (se 1 (by rfl) ⟨1855223, by rfl⟩ : syracuseStep 2473631 = 3710447) B3710447
theorem B47464325 : Blo 730325 47464325 := bstep (se 4 (by rfl) ⟨4449780, by rfl⟩ : syracuseStep 47464325 = 8899561) B8899561
theorem B1098479 : Blo 730325 1098479 := bstep (se 1 (by rfl) ⟨823859, by rfl⟩ : syracuseStep 1098479 = 1647719) B1647719
theorem B1098617 : Blo 730325 1098617 := bstep (se 2 (by rfl) ⟨411981, by rfl⟩ : syracuseStep 1098617 = 823963) B823963
theorem B11257055 : Blo 730325 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B5555465 : Blo 730325 5555465 := bstep (se 2 (by rfl) ⟨2083299, by rfl⟩ : syracuseStep 5555465 = 4166599) B4166599
theorem B4441979 : Blo 730325 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B2344841 : Blo 730325 2344841 := bstep (se 2 (by rfl) ⟨879315, by rfl⟩ : syracuseStep 2344841 = 1758631) B1758631
theorem B1099943 : Blo 730325 1099943 := bstep (se 1 (by rfl) ⟨824957, by rfl⟩ : syracuseStep 1099943 = 1649915) B1649915
theorem B2084143 : Blo 730325 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B2477735 : Blo 730325 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B2641855 : Blo 730325 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B1627913 : Blo 730325 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B1857289 : Blo 730325 1857289 := bstep (se 2 (by rfl) ⟨696483, by rfl⟩ : syracuseStep 1857289 = 1392967) B1392967
theorem B1857401 : Blo 730325 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B3528623 : Blo 730325 3528623 := bstep (se 1 (by rfl) ⟨2646467, by rfl⟩ : syracuseStep 3528623 = 5292935) B5292935
theorem B1857775 : Blo 730325 1857775 := bstep (se 1 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 1857775 = 2786663) B2786663
theorem B5430079 : Blo 730325 5430079 := bstep (se 1 (by rfl) ⟨4072559, by rfl⟩ : syracuseStep 5430079 = 8145119) B8145119
theorem B2712143 : Blo 730325 2712143 := bstep (se 1 (by rfl) ⟨2034107, by rfl⟩ : syracuseStep 2712143 = 4068215) B4068215
theorem B3958303 : Blo 730325 3958303 := bstep (se 1 (by rfl) ⟨2968727, by rfl⟩ : syracuseStep 3958303 = 5937455) B5937455
theorem B5564699 : Blo 730325 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B2977031 : Blo 730325 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B15037721 : Blo 730325 15037721 := bstep (se 2 (by rfl) ⟨5639145, by rfl⟩ : syracuseStep 15037721 = 11278291) B11278291
theorem B6255913 : Blo 730325 6255913 := bstep (se 2 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 6255913 = 4691935) B4691935
theorem B3700889 : Blo 730325 3700889 := bstep (se 2 (by rfl) ⟨1387833, by rfl⟩ : syracuseStep 3700889 = 2775667) B2775667
theorem B1407403 : Blo 730325 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B14090111 : Blo 730325 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B7504703 : Blo 730325 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B3703643 : Blo 730325 3703643 := bstep (se 1 (by rfl) ⟨2777732, by rfl⟩ : syracuseStep 3703643 = 5555465) B5555465
theorem B12518387 : Blo 730325 12518387 := bstep (se 1 (by rfl) ⟨9388790, by rfl⟩ : syracuseStep 12518387 = 18777581) B18777581
theorem B5277737 : Blo 730325 5277737 := bstep (se 2 (by rfl) ⟨1979151, by rfl⟩ : syracuseStep 5277737 = 3958303) B3958303
theorem B11274977 : Blo 730325 11274977 := bstep (se 2 (by rfl) ⟨4228116, by rfl⟩ : syracuseStep 11274977 = 8456233) B8456233
theorem B3245837417 : Blo 730325 3245837417 := bstep (se 2 (by rfl) ⟨1217189031, by rfl⟩ : syracuseStep 3245837417 = 2434378063) B2434378063
theorem B1085275 : Blo 730325 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B17829881 : Blo 730325 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B7934597 : Blo 730325 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B1643687 : Blo 730325 1643687 := bstep (se 1 (by rfl) ⟨1232765, by rfl⟩ : syracuseStep 1643687 = 2465531) B2465531
theorem B1808095 : Blo 730325 1808095 := bstep (se 1 (by rfl) ⟨1356071, by rfl⟩ : syracuseStep 1808095 = 2712143) B2712143
theorem B4168057 : Blo 730325 4168057 := bstep (se 2 (by rfl) ⟨1563021, by rfl⟩ : syracuseStep 4168057 = 3126043) B3126043
theorem B3709799 : Blo 730325 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B925759 : Blo 730325 925759 := bstep (se 1 (by rfl) ⟨694319, by rfl⟩ : syracuseStep 925759 = 1388639) B1388639
theorem B9380285 : Blo 730325 9380285 := bstep (se 3 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 9380285 = 3517607) B3517607
theorem B1876537 : Blo 730325 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B7938749 : Blo 730325 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B5546717 : Blo 730325 5546717 := bstep (se 3 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 5546717 = 2080019) B2080019
theorem B2467259 : Blo 730325 2467259 := bstep (se 1 (by rfl) ⟨1850444, by rfl⟩ : syracuseStep 2467259 = 3700889) B3700889
theorem B730751 : Blo 730325 730751 := bstep (se 1 (by rfl) ⟨548063, by rfl⟩ : syracuseStep 730751 = 1096127) B1096127
theorem B1649087 : Blo 730325 1649087 := bstep (se 1 (by rfl) ⟨1236815, by rfl⟩ : syracuseStep 1649087 = 2473631) B2473631
theorem B732319 : Blo 730325 732319 := bstep (se 1 (by rfl) ⟨549239, by rfl⟩ : syracuseStep 732319 = 1098479) B1098479
theorem B732411 : Blo 730325 732411 := bstep (se 1 (by rfl) ⟨549308, by rfl⟩ : syracuseStep 732411 = 1098617) B1098617
theorem B2469149 : Blo 730325 2469149 := bstep (se 3 (by rfl) ⟨462965, by rfl⟩ : syracuseStep 2469149 = 925931) B925931
theorem B2961319 : Blo 730325 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B733295 : Blo 730325 733295 := bstep (se 1 (by rfl) ⟨549971, by rfl⟩ : syracuseStep 733295 = 1099943) B1099943
theorem B2634601 : Blo 730325 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B1651823 : Blo 730325 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B4699295 : Blo 730325 4699295 := bstep (se 1 (by rfl) ⟨3524471, by rfl⟩ : syracuseStep 4699295 = 7048943) B7048943
theorem B1096895 : Blo 730325 1096895 := bstep (se 1 (by rfl) ⟨822671, by rfl⟩ : syracuseStep 1096895 = 1645343) B1645343
theorem B1097087 : Blo 730325 1097087 := bstep (se 1 (by rfl) ⟨822815, by rfl⟩ : syracuseStep 1097087 = 1645631) B1645631
theorem B3522473 : Blo 730325 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B2081011 : Blo 730325 2081011 := bstep (se 1 (by rfl) ⟨1560758, by rfl⟩ : syracuseStep 2081011 = 3121517) B3121517
theorem B2475035 : Blo 730325 2475035 := bstep (se 1 (by rfl) ⟨1856276, by rfl⟩ : syracuseStep 2475035 = 3712553) B3712553
theorem B1098983 : Blo 730325 1098983 := bstep (se 1 (by rfl) ⟨824237, by rfl⟩ : syracuseStep 1098983 = 1648475) B1648475
theorem B1099049 : Blo 730325 1099049 := bstep (se 2 (by rfl) ⟨412143, by rfl⟩ : syracuseStep 1099049 = 824287) B824287
theorem B2475575 : Blo 730325 2475575 := bstep (se 1 (by rfl) ⟨1856681, by rfl⟩ : syracuseStep 2475575 = 3713363) B3713363
theorem B8341217 : Blo 730325 8341217 := bstep (se 2 (by rfl) ⟨3127956, by rfl⟩ : syracuseStep 8341217 = 6255913) B6255913
theorem B2476115 : Blo 730325 2476115 := bstep (se 1 (by rfl) ⟨1857086, by rfl⟩ : syracuseStep 2476115 = 3714173) B3714173
theorem B2476385 : Blo 730325 2476385 := bstep (se 2 (by rfl) ⟨928644, by rfl⟩ : syracuseStep 2476385 = 1857289) B1857289
theorem B2476871 : Blo 730325 2476871 := bstep (se 1 (by rfl) ⟨1857653, by rfl⟩ : syracuseStep 2476871 = 3715307) B3715307
theorem B1100735 : Blo 730325 1100735 := bstep (se 1 (by rfl) ⟨825551, by rfl⟩ : syracuseStep 1100735 = 1651103) B1651103
theorem B2477033 : Blo 730325 2477033 := bstep (se 2 (by rfl) ⟨928887, by rfl⟩ : syracuseStep 2477033 = 1857775) B1857775
theorem B1101119 : Blo 730325 1101119 := bstep (se 1 (by rfl) ⟨825839, by rfl⟩ : syracuseStep 1101119 = 1651679) B1651679
theorem B12537389 : Blo 730325 12537389 := bstep (se 3 (by rfl) ⟨2350760, by rfl⟩ : syracuseStep 12537389 = 4701521) B4701521
theorem B2773025 : Blo 730325 2773025 := bstep (se 2 (by rfl) ⟨1039884, by rfl⟩ : syracuseStep 2773025 = 2079769) B2079769
theorem B9393407 : Blo 730325 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B31642883 : Blo 730325 31642883 := bstep (se 1 (by rfl) ⟨23732162, by rfl⟩ : syracuseStep 31642883 = 47464325) B47464325
theorem B7035443 : Blo 730325 7035443 := bstep (se 1 (by rfl) ⟨5276582, by rfl⟩ : syracuseStep 7035443 = 10553165) B10553165
theorem B1563227 : Blo 730325 1563227 := bstep (se 1 (by rfl) ⟨1172420, by rfl⟩ : syracuseStep 1563227 = 2344841) B2344841
theorem B1238267 : Blo 730325 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B2352415 : Blo 730325 2352415 := bstep (se 1 (by rfl) ⟨1764311, by rfl⟩ : syracuseStep 2352415 = 3528623) B3528623
theorem B1238665 : Blo 730325 1238665 := bstep (se 2 (by rfl) ⟨464499, by rfl⟩ : syracuseStep 1238665 = 928999) B928999
theorem B28960421 : Blo 730325 28960421 := bstep (se 4 (by rfl) ⟨2715039, by rfl⟩ : syracuseStep 28960421 = 5430079) B5430079
theorem B2778857 : Blo 730325 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B879719 : Blo 730325 879719 := bstep (se 1 (by rfl) ⟨659789, by rfl⟩ : syracuseStep 879719 = 1319579) B1319579
theorem B10025147 : Blo 730325 10025147 := bstep (se 1 (by rfl) ⟨7518860, by rfl⟩ : syracuseStep 10025147 = 15037721) B15037721
theorem B6262271 : Blo 730325 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B4690295 : Blo 730325 4690295 := bstep (se 1 (by rfl) ⟨3517721, by rfl⟩ : syracuseStep 4690295 = 7035443) B7035443
theorem B1447033 : Blo 730325 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B825511 : Blo 730325 825511 := bstep (se 1 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 825511 = 1238267) B1238267
theorem B1644839 : Blo 730325 1644839 := bstep (se 1 (by rfl) ⟨1233629, by rfl⟩ : syracuseStep 1644839 = 2467259) B2467259
theorem B3512801 : Blo 730325 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B1646099 : Blo 730325 1646099 := bstep (se 1 (by rfl) ⟨1234574, by rfl⟩ : syracuseStep 1646099 = 2469149) B2469149
theorem B33433037 : Blo 730325 33433037 := bstep (se 3 (by rfl) ⟨6268694, by rfl⟩ : syracuseStep 33433037 = 12537389) B12537389
theorem B731263 : Blo 730325 731263 := bstep (se 1 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 731263 = 1096895) B1096895
theorem B731391 : Blo 730325 731391 := bstep (se 1 (by rfl) ⟨548543, by rfl⟩ : syracuseStep 731391 = 1097087) B1097087
theorem B2469095 : Blo 730325 2469095 := bstep (se 1 (by rfl) ⟨1851821, by rfl⟩ : syracuseStep 2469095 = 3703643) B3703643
theorem B1650023 : Blo 730325 1650023 := bstep (se 1 (by rfl) ⟨1237517, by rfl⟩ : syracuseStep 1650023 = 2475035) B2475035
theorem B2502049 : Blo 730325 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B732655 : Blo 730325 732655 := bstep (se 1 (by rfl) ⟨549491, by rfl⟩ : syracuseStep 732655 = 1098983) B1098983
theorem B732699 : Blo 730325 732699 := bstep (se 1 (by rfl) ⟨549524, by rfl⟩ : syracuseStep 732699 = 1099049) B1099049
theorem B1650383 : Blo 730325 1650383 := bstep (se 1 (by rfl) ⟨1237787, by rfl⟩ : syracuseStep 1650383 = 2475575) B2475575
theorem B3518491 : Blo 730325 3518491 := bstep (se 1 (by rfl) ⟨2638868, by rfl⟩ : syracuseStep 3518491 = 5277737) B5277737
theorem B1650743 : Blo 730325 1650743 := bstep (se 1 (by rfl) ⟨1238057, by rfl⟩ : syracuseStep 1650743 = 2476115) B2476115
theorem B1650923 : Blo 730325 1650923 := bstep (se 1 (by rfl) ⟨1238192, by rfl⟩ : syracuseStep 1650923 = 2476385) B2476385
theorem B7516651 : Blo 730325 7516651 := bstep (se 1 (by rfl) ⟨5637488, by rfl⟩ : syracuseStep 7516651 = 11274977) B11274977
theorem B1651247 : Blo 730325 1651247 := bstep (se 1 (by rfl) ⟨1238435, by rfl⟩ : syracuseStep 1651247 = 2476871) B2476871
theorem B733823 : Blo 730325 733823 := bstep (se 1 (by rfl) ⟨550367, by rfl⟩ : syracuseStep 733823 = 1100735) B1100735
theorem B1651355 : Blo 730325 1651355 := bstep (se 1 (by rfl) ⟨1238516, by rfl⟩ : syracuseStep 1651355 = 2477033) B2477033
theorem B1651553 : Blo 730325 1651553 := bstep (se 2 (by rfl) ⟨619332, by rfl⟩ : syracuseStep 1651553 = 1238665) B1238665
theorem B734079 : Blo 730325 734079 := bstep (se 1 (by rfl) ⟨550559, by rfl⟩ : syracuseStep 734079 = 1101119) B1101119
theorem B1848683 : Blo 730325 1848683 := bstep (se 1 (by rfl) ⟨1386512, by rfl⟩ : syracuseStep 1848683 = 2773025) B2773025
theorem B5289731 : Blo 730325 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B1095791 : Blo 730325 1095791 := bstep (se 1 (by rfl) ⟨821843, by rfl⟩ : syracuseStep 1095791 = 1643687) B1643687
theorem B2473199 : Blo 730325 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B3948425 : Blo 730325 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B5292499 : Blo 730325 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B1852571 : Blo 730325 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B1099391 : Blo 730325 1099391 := bstep (se 1 (by rfl) ⟨824543, by rfl⟩ : syracuseStep 1099391 = 1649087) B1649087
theorem B2410793 : Blo 730325 2410793 := bstep (se 2 (by rfl) ⟨904047, by rfl⟩ : syracuseStep 2410793 = 1808095) B1808095
theorem B2345917 : Blo 730325 2345917 := bstep (se 3 (by rfl) ⟨439859, by rfl⟩ : syracuseStep 2345917 = 879719) B879719
theorem B5557409 : Blo 730325 5557409 := bstep (se 2 (by rfl) ⟨2084028, by rfl⟩ : syracuseStep 5557409 = 4168057) B4168057
theorem B1101215 : Blo 730325 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B3132863 : Blo 730325 3132863 := bstep (se 1 (by rfl) ⟨2349647, by rfl⟩ : syracuseStep 3132863 = 4699295) B4699295
theorem B2348315 : Blo 730325 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B1234345 : Blo 730325 1234345 := bstep (se 2 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 1234345 = 925759) B925759
theorem B2774681 : Blo 730325 2774681 := bstep (se 2 (by rfl) ⟨1040505, by rfl⟩ : syracuseStep 2774681 = 2081011) B2081011
theorem B5003135 : Blo 730325 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B8345591 : Blo 730325 8345591 := bstep (se 1 (by rfl) ⟨6259193, by rfl⟩ : syracuseStep 8345591 = 12518387) B12518387
theorem B5560811 : Blo 730325 5560811 := bstep (se 1 (by rfl) ⟨4170608, by rfl⟩ : syracuseStep 5560811 = 8341217) B8341217
theorem B3136553 : Blo 730325 3136553 := bstep (se 2 (by rfl) ⟨1176207, by rfl⟩ : syracuseStep 3136553 = 2352415) B2352415
theorem B2163891611 : Blo 730325 2163891611 := bstep (se 1 (by rfl) ⟨1622918708, by rfl⟩ : syracuseStep 2163891611 = 3245837417) B3245837417
theorem B11886587 : Blo 730325 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B21095255 : Blo 730325 21095255 := bstep (se 1 (by rfl) ⟨15821441, by rfl⟩ : syracuseStep 21095255 = 31642883) B31642883
theorem B1042151 : Blo 730325 1042151 := bstep (se 1 (by rfl) ⟨781613, by rfl⟩ : syracuseStep 1042151 = 1563227) B1563227
theorem B77227789 : Blo 730325 77227789 := bstep (se 3 (by rfl) ⟨14480210, by rfl⟩ : syracuseStep 77227789 = 28960421) B28960421
theorem B6253523 : Blo 730325 6253523 := bstep (se 1 (by rfl) ⟨4690142, by rfl⟩ : syracuseStep 6253523 = 9380285) B9380285
theorem B3697811 : Blo 730325 3697811 := bstep (se 1 (by rfl) ⟨2773358, by rfl⟩ : syracuseStep 3697811 = 5546717) B5546717
theorem B6683431 : Blo 730325 6683431 := bstep (se 1 (by rfl) ⟨5012573, by rfl⟩ : syracuseStep 6683431 = 10025147) B10025147
theorem B1607195 : Blo 730325 1607195 := bstep (se 1 (by rfl) ⟨1205396, by rfl⟩ : syracuseStep 1607195 = 2410793) B2410793
theorem B3704939 : Blo 730325 3704939 := bstep (se 1 (by rfl) ⟨2778704, by rfl⟩ : syracuseStep 3704939 = 5557409) B5557409
theorem B3707207 : Blo 730325 3707207 := bstep (se 1 (by rfl) ⟨2780405, by rfl⟩ : syracuseStep 3707207 = 5560811) B5560811
theorem B4691321 : Blo 730325 4691321 := bstep (se 2 (by rfl) ⟨1759245, by rfl⟩ : syracuseStep 4691321 = 3518491) B3518491
theorem B14063503 : Blo 730325 14063503 := bstep (se 1 (by rfl) ⟨10547627, by rfl⟩ : syracuseStep 14063503 = 21095255) B21095255
theorem B22288691 : Blo 730325 22288691 := bstep (se 1 (by rfl) ⟨16716518, by rfl⟩ : syracuseStep 22288691 = 33433037) B33433037
theorem B1645793 : Blo 730325 1645793 := bstep (se 2 (by rfl) ⟨617172, by rfl⟩ : syracuseStep 1645793 = 1234345) B1234345
theorem B4169015 : Blo 730325 4169015 := bstep (se 1 (by rfl) ⟨3126761, by rfl⟩ : syracuseStep 4169015 = 6253523) B6253523
theorem B2465207 : Blo 730325 2465207 := bstep (se 1 (by rfl) ⟨1848905, by rfl⟩ : syracuseStep 2465207 = 3697811) B3697811
theorem B1646063 : Blo 730325 1646063 := bstep (se 1 (by rfl) ⟨1234547, by rfl⟩ : syracuseStep 1646063 = 2469095) B2469095
theorem B730527 : Blo 730325 730527 := bstep (se 1 (by rfl) ⟨547895, by rfl⟩ : syracuseStep 730527 = 1095791) B1095791
theorem B1648799 : Blo 730325 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B2632283 : Blo 730325 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B7056665 : Blo 730325 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B732927 : Blo 730325 732927 := bstep (se 1 (by rfl) ⟨549695, by rfl⟩ : syracuseStep 732927 = 1099391) B1099391
theorem B734143 : Blo 730325 734143 := bstep (se 1 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 734143 = 1101215) B1101215
theorem B4174847 : Blo 730325 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B102970385 : Blo 730325 102970385 := bstep (se 2 (by rfl) ⟨38613894, by rfl⟩ : syracuseStep 102970385 = 77227789) B77227789
theorem B3126863 : Blo 730325 3126863 := bstep (se 1 (by rfl) ⟨2345147, by rfl⟩ : syracuseStep 3126863 = 4690295) B4690295
theorem B1849787 : Blo 730325 1849787 := bstep (se 1 (by rfl) ⟨1387340, by rfl⟩ : syracuseStep 1849787 = 2774681) B2774681
theorem B3127889 : Blo 730325 3127889 := bstep (se 2 (by rfl) ⟨1172958, by rfl⟩ : syracuseStep 3127889 = 2345917) B2345917
theorem B1096559 : Blo 730325 1096559 := bstep (se 1 (by rfl) ⟨822419, by rfl⟩ : syracuseStep 1096559 = 1644839) B1644839
theorem B2341867 : Blo 730325 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B1442594407 : Blo 730325 1442594407 := bstep (se 1 (by rfl) ⟨1081945805, by rfl⟩ : syracuseStep 1442594407 = 2163891611) B2163891611
theorem B1097399 : Blo 730325 1097399 := bstep (se 1 (by rfl) ⟨823049, by rfl⟩ : syracuseStep 1097399 = 1646099) B1646099
theorem B1100015 : Blo 730325 1100015 := bstep (se 1 (by rfl) ⟨825011, by rfl⟩ : syracuseStep 1100015 = 1650023) B1650023
theorem B1100255 : Blo 730325 1100255 := bstep (se 1 (by rfl) ⟨825191, by rfl⟩ : syracuseStep 1100255 = 1650383) B1650383
theorem B1100495 : Blo 730325 1100495 := bstep (se 1 (by rfl) ⟨825371, by rfl⟩ : syracuseStep 1100495 = 1650743) B1650743
theorem B1100615 : Blo 730325 1100615 := bstep (se 1 (by rfl) ⟨825461, by rfl⟩ : syracuseStep 1100615 = 1650923) B1650923
theorem B1100681 : Blo 730325 1100681 := bstep (se 2 (by rfl) ⟨412755, by rfl⟩ : syracuseStep 1100681 = 825511) B825511
theorem B1100831 : Blo 730325 1100831 := bstep (se 1 (by rfl) ⟨825623, by rfl⟩ : syracuseStep 1100831 = 1651247) B1651247
theorem B1100903 : Blo 730325 1100903 := bstep (se 1 (by rfl) ⟨825677, by rfl⟩ : syracuseStep 1100903 = 1651355) B1651355
theorem B1101035 : Blo 730325 1101035 := bstep (se 1 (by rfl) ⟨825776, by rfl⟩ : syracuseStep 1101035 = 1651553) B1651553
theorem B1232455 : Blo 730325 1232455 := bstep (se 1 (by rfl) ⟨924341, by rfl⟩ : syracuseStep 1232455 = 1848683) B1848683
theorem B3526487 : Blo 730325 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B1235047 : Blo 730325 1235047 := bstep (se 1 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 1235047 = 1852571) B1852571
theorem B2088575 : Blo 730325 2088575 := bstep (se 1 (by rfl) ⟨1566431, by rfl⟩ : syracuseStep 2088575 = 3132863) B3132863
theorem B1565543 : Blo 730325 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B3335423 : Blo 730325 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B5563727 : Blo 730325 5563727 := bstep (se 1 (by rfl) ⟨4172795, by rfl⟩ : syracuseStep 5563727 = 8345591) B8345591
theorem B3336065 : Blo 730325 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B2779069 : Blo 730325 2779069 := bstep (se 3 (by rfl) ⟨521075, by rfl⟩ : syracuseStep 2779069 = 1042151) B1042151
theorem B2091035 : Blo 730325 2091035 := bstep (se 1 (by rfl) ⟨1568276, by rfl⟩ : syracuseStep 2091035 = 3136553) B3136553
theorem B7924391 : Blo 730325 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B10022201 : Blo 730325 10022201 := bstep (se 2 (by rfl) ⟨3758325, by rfl⟩ : syracuseStep 10022201 = 7516651) B7516651
theorem B1929377 : Blo 730325 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B8911241 : Blo 730325 8911241 := bstep (se 2 (by rfl) ⟨3341715, by rfl⟩ : syracuseStep 8911241 = 6683431) B6683431
theorem B5145005 : Blo 730325 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B3705425 : Blo 730325 3705425 := bstep (se 2 (by rfl) ⟨1389534, by rfl⟩ : syracuseStep 3705425 = 2779069) B2779069
theorem B1643273 : Blo 730325 1643273 := bstep (se 2 (by rfl) ⟨616227, by rfl⟩ : syracuseStep 1643273 = 1232455) B1232455
theorem B1643471 : Blo 730325 1643471 := bstep (se 1 (by rfl) ⟨1232603, by rfl⟩ : syracuseStep 1643471 = 2465207) B2465207
theorem B3709151 : Blo 730325 3709151 := bstep (se 1 (by rfl) ⟨2781863, by rfl⟩ : syracuseStep 3709151 = 5563727) B5563727
theorem B5282927 : Blo 730325 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B18751337 : Blo 730325 18751337 := bstep (se 2 (by rfl) ⟨7031751, by rfl⟩ : syracuseStep 18751337 = 14063503) B14063503
theorem B1646729 : Blo 730325 1646729 := bstep (se 2 (by rfl) ⟨617523, by rfl⟩ : syracuseStep 1646729 = 1235047) B1235047
theorem B3122489 : Blo 730325 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B5940827 : Blo 730325 5940827 := bstep (se 1 (by rfl) ⟨4455620, by rfl⟩ : syracuseStep 5940827 = 8911241) B8911241
theorem B731039 : Blo 730325 731039 := bstep (se 1 (by rfl) ⟨548279, by rfl⟩ : syracuseStep 731039 = 1096559) B1096559
theorem B1923459209 : Blo 730325 1923459209 := bstep (se 2 (by rfl) ⟨721297203, by rfl⟩ : syracuseStep 1923459209 = 1442594407) B1442594407
theorem B731599 : Blo 730325 731599 := bstep (se 1 (by rfl) ⟨548699, by rfl⟩ : syracuseStep 731599 = 1097399) B1097399
theorem B2469959 : Blo 730325 2469959 := bstep (se 1 (by rfl) ⟨1852469, by rfl⟩ : syracuseStep 2469959 = 3704939) B3704939
theorem B733343 : Blo 730325 733343 := bstep (se 1 (by rfl) ⟨550007, by rfl⟩ : syracuseStep 733343 = 1100015) B1100015
theorem B733503 : Blo 730325 733503 := bstep (se 1 (by rfl) ⟨550127, by rfl⟩ : syracuseStep 733503 = 1100255) B1100255
theorem B733663 : Blo 730325 733663 := bstep (se 1 (by rfl) ⟨550247, by rfl⟩ : syracuseStep 733663 = 1100495) B1100495
theorem B733743 : Blo 730325 733743 := bstep (se 1 (by rfl) ⟨550307, by rfl⟩ : syracuseStep 733743 = 1100615) B1100615
theorem B733787 : Blo 730325 733787 := bstep (se 1 (by rfl) ⟨550340, by rfl⟩ : syracuseStep 733787 = 1100681) B1100681
theorem B733887 : Blo 730325 733887 := bstep (se 1 (by rfl) ⟨550415, by rfl⟩ : syracuseStep 733887 = 1100831) B1100831
theorem B733935 : Blo 730325 733935 := bstep (se 1 (by rfl) ⟨550451, by rfl⟩ : syracuseStep 733935 = 1100903) B1100903
theorem B734023 : Blo 730325 734023 := bstep (se 1 (by rfl) ⟨550517, by rfl⟩ : syracuseStep 734023 = 1101035) B1101035
theorem B2471471 : Blo 730325 2471471 := bstep (se 1 (by rfl) ⟨1853603, by rfl⟩ : syracuseStep 2471471 = 3707207) B3707207
theorem B8894461 : Blo 730325 8894461 := bstep (se 3 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 8894461 = 3335423) B3335423
theorem B3127547 : Blo 730325 3127547 := bstep (se 1 (by rfl) ⟨2345660, by rfl⟩ : syracuseStep 3127547 = 4691321) B4691321
theorem B8338301 : Blo 730325 8338301 := bstep (se 3 (by rfl) ⟨1563431, by rfl⟩ : syracuseStep 8338301 = 3126863) B3126863
theorem B1097195 : Blo 730325 1097195 := bstep (se 1 (by rfl) ⟨822896, by rfl⟩ : syracuseStep 1097195 = 1645793) B1645793
theorem B1097375 : Blo 730325 1097375 := bstep (se 1 (by rfl) ⟨823031, by rfl⟩ : syracuseStep 1097375 = 1646063) B1646063
theorem B1392383 : Blo 730325 1392383 := bstep (se 1 (by rfl) ⟨1044287, by rfl⟩ : syracuseStep 1392383 = 2088575) B2088575
theorem B1394023 : Blo 730325 1394023 := bstep (se 1 (by rfl) ⟨1045517, by rfl⟩ : syracuseStep 1394023 = 2091035) B2091035
theorem B1099199 : Blo 730325 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B1754855 : Blo 730325 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B4704443 : Blo 730325 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B1233191 : Blo 730325 1233191 := bstep (se 1 (by rfl) ⟨924893, by rfl⟩ : syracuseStep 1233191 = 1849787) B1849787
theorem B2085259 : Blo 730325 2085259 := bstep (se 1 (by rfl) ⟨1563944, by rfl⟩ : syracuseStep 2085259 = 3127889) B3127889
theorem B1071463 : Blo 730325 1071463 := bstep (se 1 (by rfl) ⟨803597, by rfl⟩ : syracuseStep 1071463 = 1607195) B1607195
theorem B2350991 : Blo 730325 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B2779343 : Blo 730325 2779343 := bstep (se 1 (by rfl) ⟨2084507, by rfl⟩ : syracuseStep 2779343 = 4169015) B4169015
theorem B1043695 : Blo 730325 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B59436509 : Blo 730325 59436509 := bstep (se 3 (by rfl) ⟨11144345, by rfl⟩ : syracuseStep 59436509 = 22288691) B22288691
theorem B2224043 : Blo 730325 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B6681467 : Blo 730325 6681467 := bstep (se 1 (by rfl) ⟨5011100, by rfl⟩ : syracuseStep 6681467 = 10022201) B10022201
theorem B2783231 : Blo 730325 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B68646923 : Blo 730325 68646923 := bstep (se 1 (by rfl) ⟨51485192, by rfl⟩ : syracuseStep 68646923 = 102970385) B102970385
theorem B822127 : Blo 730325 822127 := bstep (se 1 (by rfl) ⟨616595, by rfl⟩ : syracuseStep 822127 = 1233191) B1233191
theorem B8326637 : Blo 730325 8326637 := bstep (se 3 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 8326637 = 3122489) B3122489
theorem B1482695 : Blo 730325 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B1646639 : Blo 730325 1646639 := bstep (se 1 (by rfl) ⟨1234979, by rfl⟩ : syracuseStep 1646639 = 2469959) B2469959
theorem B1647647 : Blo 730325 1647647 := bstep (se 1 (by rfl) ⟨1235735, by rfl⟩ : syracuseStep 1647647 = 2471471) B2471471
theorem B731463 : Blo 730325 731463 := bstep (se 1 (by rfl) ⟨548597, by rfl⟩ : syracuseStep 731463 = 1097195) B1097195
theorem B6269309 : Blo 730325 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B731583 : Blo 730325 731583 := bstep (se 1 (by rfl) ⟨548687, by rfl⟩ : syracuseStep 731583 = 1097375) B1097375
theorem B928255 : Blo 730325 928255 := bstep (se 1 (by rfl) ⟨696191, by rfl⟩ : syracuseStep 928255 = 1392383) B1392383
theorem B732799 : Blo 730325 732799 := bstep (se 1 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 732799 = 1099199) B1099199
theorem B2470283 : Blo 730325 2470283 := bstep (se 1 (by rfl) ⟨1852712, by rfl⟩ : syracuseStep 2470283 = 3705425) B3705425
theorem B1095515 : Blo 730325 1095515 := bstep (se 1 (by rfl) ⟨821636, by rfl⟩ : syracuseStep 1095515 = 1643273) B1643273
theorem B1095647 : Blo 730325 1095647 := bstep (se 1 (by rfl) ⟨821735, by rfl⟩ : syracuseStep 1095647 = 1643471) B1643471
theorem B2472767 : Blo 730325 2472767 := bstep (se 1 (by rfl) ⟨1854575, by rfl⟩ : syracuseStep 2472767 = 3709151) B3709151
theorem B1391593 : Blo 730325 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B3521951 : Blo 730325 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B12500891 : Blo 730325 12500891 := bstep (se 1 (by rfl) ⟨9375668, by rfl⟩ : syracuseStep 12500891 = 18751337) B18751337
theorem B1097819 : Blo 730325 1097819 := bstep (se 1 (by rfl) ⟨823364, by rfl⟩ : syracuseStep 1097819 = 1646729) B1646729
theorem B1852895 : Blo 730325 1852895 := bstep (se 1 (by rfl) ⟨1389671, by rfl⟩ : syracuseStep 1852895 = 2779343) B2779343
theorem B1428617 : Blo 730325 1428617 := bstep (se 2 (by rfl) ⟨535731, by rfl⟩ : syracuseStep 1428617 = 1071463) B1071463
theorem B1855487 : Blo 730325 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B45764615 : Blo 730325 45764615 := bstep (se 1 (by rfl) ⟨34323461, by rfl⟩ : syracuseStep 45764615 = 68646923) B68646923
theorem B2085031 : Blo 730325 2085031 := bstep (se 1 (by rfl) ⟨1563773, by rfl⟩ : syracuseStep 2085031 = 3127547) B3127547
theorem B5558867 : Blo 730325 5558867 := bstep (se 1 (by rfl) ⟨4169150, by rfl⟩ : syracuseStep 5558867 = 8338301) B8338301
theorem B13720013 : Blo 730325 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B1169903 : Blo 730325 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B3136295 : Blo 730325 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B1858697 : Blo 730325 1858697 := bstep (se 2 (by rfl) ⟨697011, by rfl⟩ : syracuseStep 1858697 = 1394023) B1394023
theorem B2780345 : Blo 730325 2780345 := bstep (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) B2085259
theorem B3960551 : Blo 730325 3960551 := bstep (se 1 (by rfl) ⟨2970413, by rfl⟩ : syracuseStep 3960551 = 5940827) B5940827
theorem B1282306139 : Blo 730325 1282306139 := bstep (se 1 (by rfl) ⟨961729604, by rfl⟩ : syracuseStep 1282306139 = 1923459209) B1923459209
theorem B11859281 : Blo 730325 11859281 := bstep (se 2 (by rfl) ⟨4447230, by rfl⟩ : syracuseStep 11859281 = 8894461) B8894461
theorem B4454311 : Blo 730325 4454311 := bstep (se 1 (by rfl) ⟨3340733, by rfl⟩ : syracuseStep 4454311 = 6681467) B6681467
theorem B158497357 : Blo 730325 158497357 := bstep (se 3 (by rfl) ⟨29718254, by rfl⟩ : syracuseStep 158497357 = 59436509) B59436509
theorem B952411 : Blo 730325 952411 := bstep (se 1 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 952411 = 1428617) B1428617
theorem B30509743 : Blo 730325 30509743 := bstep (se 1 (by rfl) ⟨22882307, by rfl⟩ : syracuseStep 30509743 = 45764615) B45764615
theorem B3705911 : Blo 730325 3705911 := bstep (se 1 (by rfl) ⟨2779433, by rfl⟩ : syracuseStep 3705911 = 5558867) B5558867
theorem B9146675 : Blo 730325 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B988463 : Blo 730325 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B3119741 : Blo 730325 3119741 := bstep (se 3 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 3119741 = 1169903) B1169903
theorem B5939081 : Blo 730325 5939081 := bstep (se 2 (by rfl) ⟨2227155, by rfl⟩ : syracuseStep 5939081 = 4454311) B4454311
theorem B1646855 : Blo 730325 1646855 := bstep (se 1 (by rfl) ⟨1235141, by rfl⟩ : syracuseStep 1646855 = 2470283) B2470283
theorem B211329809 : Blo 730325 211329809 := bstep (se 2 (by rfl) ⟨79248678, by rfl⟩ : syracuseStep 211329809 = 158497357) B158497357
theorem B7906187 : Blo 730325 7906187 := bstep (se 1 (by rfl) ⟨5929640, by rfl⟩ : syracuseStep 7906187 = 11859281) B11859281
theorem B730343 : Blo 730325 730343 := bstep (se 1 (by rfl) ⟨547757, by rfl⟩ : syracuseStep 730343 = 1095515) B1095515
theorem B730431 : Blo 730325 730431 := bstep (se 1 (by rfl) ⟨547823, by rfl⟩ : syracuseStep 730431 = 1095647) B1095647
theorem B1648511 : Blo 730325 1648511 := bstep (se 1 (by rfl) ⟨1236383, by rfl⟩ : syracuseStep 1648511 = 2472767) B2472767
theorem B8333927 : Blo 730325 8333927 := bstep (se 1 (by rfl) ⟨6250445, by rfl⟩ : syracuseStep 8333927 = 12500891) B12500891
theorem B731879 : Blo 730325 731879 := bstep (se 1 (by rfl) ⟨548909, by rfl⟩ : syracuseStep 731879 = 1097819) B1097819
theorem B5551091 : Blo 730325 5551091 := bstep (se 1 (by rfl) ⟨4163318, by rfl⟩ : syracuseStep 5551091 = 8326637) B8326637
theorem B1096169 : Blo 730325 1096169 := bstep (se 2 (by rfl) ⟨411063, by rfl⟩ : syracuseStep 1096169 = 822127) B822127
theorem B1097759 : Blo 730325 1097759 := bstep (se 1 (by rfl) ⟨823319, by rfl⟩ : syracuseStep 1097759 = 1646639) B1646639
theorem B1098431 : Blo 730325 1098431 := bstep (se 1 (by rfl) ⟨823823, by rfl⟩ : syracuseStep 1098431 = 1647647) B1647647
theorem B4179539 : Blo 730325 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B1853563 : Blo 730325 1853563 := bstep (se 1 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 1853563 = 2780345) B2780345
theorem B2640367 : Blo 730325 2640367 := bstep (se 1 (by rfl) ⟨1980275, by rfl⟩ : syracuseStep 2640367 = 3960551) B3960551
theorem B854870759 : Blo 730325 854870759 := bstep (se 1 (by rfl) ⟨641153069, by rfl⟩ : syracuseStep 854870759 = 1282306139) B1282306139
theorem B1855457 : Blo 730325 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B2347967 : Blo 730325 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B1235263 : Blo 730325 1235263 := bstep (se 1 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 1235263 = 1852895) B1852895
theorem B1236991 : Blo 730325 1236991 := bstep (se 1 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 1236991 = 1855487) B1855487
theorem B1237673 : Blo 730325 1237673 := bstep (se 2 (by rfl) ⟨464127, by rfl⟩ : syracuseStep 1237673 = 928255) B928255
theorem B2090863 : Blo 730325 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B1239131 : Blo 730325 1239131 := bstep (se 1 (by rfl) ⟨929348, by rfl⟩ : syracuseStep 1239131 = 1858697) B1858697
theorem B2780041 : Blo 730325 2780041 := bstep (se 2 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 2780041 = 2085031) B2085031
theorem B2786359 : Blo 730325 2786359 := bstep (se 1 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 2786359 = 4179539) B4179539
theorem B2787817 : Blo 730325 2787817 := bstep (se 2 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 2787817 = 2090863) B2090863
theorem B6261245 : Blo 730325 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B6097783 : Blo 730325 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B3706721 : Blo 730325 3706721 := bstep (se 2 (by rfl) ⟨1390020, by rfl⟩ : syracuseStep 3706721 = 2780041) B2780041
theorem B825115 : Blo 730325 825115 := bstep (se 1 (by rfl) ⟨618836, by rfl⟩ : syracuseStep 825115 = 1237673) B1237673
theorem B826087 : Blo 730325 826087 := bstep (se 1 (by rfl) ⟨619565, by rfl⟩ : syracuseStep 826087 = 1239131) B1239131
theorem B1647017 : Blo 730325 1647017 := bstep (se 2 (by rfl) ⟨617631, by rfl⟩ : syracuseStep 1647017 = 1235263) B1235263
theorem B730779 : Blo 730325 730779 := bstep (se 1 (by rfl) ⟨548084, by rfl⟩ : syracuseStep 730779 = 1096169) B1096169
theorem B1649321 : Blo 730325 1649321 := bstep (se 2 (by rfl) ⟨618495, by rfl⟩ : syracuseStep 1649321 = 1236991) B1236991
theorem B731839 : Blo 730325 731839 := bstep (se 1 (by rfl) ⟨548879, by rfl⟩ : syracuseStep 731839 = 1097759) B1097759
theorem B732287 : Blo 730325 732287 := bstep (se 1 (by rfl) ⟨549215, by rfl⟩ : syracuseStep 732287 = 1098431) B1098431
theorem B569913839 : Blo 730325 569913839 := bstep (se 1 (by rfl) ⟨427435379, by rfl⟩ : syracuseStep 569913839 = 854870759) B854870759
theorem B2470607 : Blo 730325 2470607 := bstep (se 1 (by rfl) ⟨1852955, by rfl⟩ : syracuseStep 2470607 = 3705911) B3705911
theorem B2471417 : Blo 730325 2471417 := bstep (se 2 (by rfl) ⟨926781, by rfl⟩ : syracuseStep 2471417 = 1853563) B1853563
theorem B2635901 : Blo 730325 2635901 := bstep (se 3 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 2635901 = 988463) B988463
theorem B40679657 : Blo 730325 40679657 := bstep (se 2 (by rfl) ⟨15254871, by rfl⟩ : syracuseStep 40679657 = 30509743) B30509743
theorem B2079827 : Blo 730325 2079827 := bstep (se 1 (by rfl) ⟨1559870, by rfl⟩ : syracuseStep 2079827 = 3119741) B3119741
theorem B1097903 : Blo 730325 1097903 := bstep (se 1 (by rfl) ⟨823427, by rfl⟩ : syracuseStep 1097903 = 1646855) B1646855
theorem B140886539 : Blo 730325 140886539 := bstep (se 1 (by rfl) ⟨105664904, by rfl⟩ : syracuseStep 140886539 = 211329809) B211329809
theorem B1099007 : Blo 730325 1099007 := bstep (se 1 (by rfl) ⟨824255, by rfl⟩ : syracuseStep 1099007 = 1648511) B1648511
theorem B5555951 : Blo 730325 5555951 := bstep (se 1 (by rfl) ⟨4166963, by rfl⟩ : syracuseStep 5555951 = 8333927) B8333927
theorem B14081957 : Blo 730325 14081957 := bstep (se 4 (by rfl) ⟨1320183, by rfl⟩ : syracuseStep 14081957 = 2640367) B2640367
theorem B1236971 : Blo 730325 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B1269881 : Blo 730325 1269881 := bstep (se 2 (by rfl) ⟨476205, by rfl⟩ : syracuseStep 1269881 = 952411) B952411
theorem B3959387 : Blo 730325 3959387 := bstep (se 1 (by rfl) ⟨2969540, by rfl⟩ : syracuseStep 3959387 = 5939081) B5939081
theorem B5270791 : Blo 730325 5270791 := bstep (se 1 (by rfl) ⟨3953093, by rfl⟩ : syracuseStep 5270791 = 7906187) B7906187
theorem B3700727 : Blo 730325 3700727 := bstep (se 1 (by rfl) ⟨2775545, by rfl⟩ : syracuseStep 3700727 = 5551091) B5551091
theorem B3703967 : Blo 730325 3703967 := bstep (se 1 (by rfl) ⟨2777975, by rfl⟩ : syracuseStep 3703967 = 5555951) B5555951
theorem B8130377 : Blo 730325 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B824647 : Blo 730325 824647 := bstep (se 1 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 824647 = 1236971) B1236971
theorem B1647071 : Blo 730325 1647071 := bstep (se 1 (by rfl) ⟨1235303, by rfl⟩ : syracuseStep 1647071 = 2470607) B2470607
theorem B1647611 : Blo 730325 1647611 := bstep (se 1 (by rfl) ⟨1235708, by rfl⟩ : syracuseStep 1647611 = 2471417) B2471417
theorem B2467151 : Blo 730325 2467151 := bstep (se 1 (by rfl) ⟨1850363, by rfl⟩ : syracuseStep 2467151 = 3700727) B3700727
theorem B1386551 : Blo 730325 1386551 := bstep (se 1 (by rfl) ⟨1039913, by rfl⟩ : syracuseStep 1386551 = 2079827) B2079827
theorem B731935 : Blo 730325 731935 := bstep (se 1 (by rfl) ⟨548951, by rfl⟩ : syracuseStep 731935 = 1097903) B1097903
theorem B93924359 : Blo 730325 93924359 := bstep (se 1 (by rfl) ⟨70443269, by rfl⟩ : syracuseStep 93924359 = 140886539) B140886539
theorem B732671 : Blo 730325 732671 := bstep (se 1 (by rfl) ⟨549503, by rfl⟩ : syracuseStep 732671 = 1099007) B1099007
theorem B3715145 : Blo 730325 3715145 := bstep (se 2 (by rfl) ⟨1393179, by rfl⟩ : syracuseStep 3715145 = 2786359) B2786359
theorem B4174163 : Blo 730325 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B2471147 : Blo 730325 2471147 := bstep (se 1 (by rfl) ⟨1853360, by rfl⟩ : syracuseStep 2471147 = 3706721) B3706721
theorem B3717089 : Blo 730325 3717089 := bstep (se 2 (by rfl) ⟨1393908, by rfl⟩ : syracuseStep 3717089 = 2787817) B2787817
theorem B7027721 : Blo 730325 7027721 := bstep (se 2 (by rfl) ⟨2635395, by rfl⟩ : syracuseStep 7027721 = 5270791) B5270791
theorem B9387971 : Blo 730325 9387971 := bstep (se 1 (by rfl) ⟨7040978, by rfl⟩ : syracuseStep 9387971 = 14081957) B14081957
theorem B1098011 : Blo 730325 1098011 := bstep (se 1 (by rfl) ⟨823508, by rfl⟩ : syracuseStep 1098011 = 1647017) B1647017
theorem B2639591 : Blo 730325 2639591 := bstep (se 1 (by rfl) ⟨1979693, by rfl⟩ : syracuseStep 2639591 = 3959387) B3959387
theorem B1099547 : Blo 730325 1099547 := bstep (se 1 (by rfl) ⟨824660, by rfl⟩ : syracuseStep 1099547 = 1649321) B1649321
theorem B1100153 : Blo 730325 1100153 := bstep (se 2 (by rfl) ⟨412557, by rfl⟩ : syracuseStep 1100153 = 825115) B825115
theorem B1101449 : Blo 730325 1101449 := bstep (se 2 (by rfl) ⟨413043, by rfl⟩ : syracuseStep 1101449 = 826087) B826087
theorem B1757267 : Blo 730325 1757267 := bstep (se 1 (by rfl) ⟨1317950, by rfl⟩ : syracuseStep 1757267 = 2635901) B2635901
theorem B27119771 : Blo 730325 27119771 := bstep (se 1 (by rfl) ⟨20339828, by rfl⟩ : syracuseStep 27119771 = 40679657) B40679657
theorem B846587 : Blo 730325 846587 := bstep (se 1 (by rfl) ⟨634940, by rfl⟩ : syracuseStep 846587 = 1269881) B1269881
theorem B379942559 : Blo 730325 379942559 := bstep (se 1 (by rfl) ⟨284956919, by rfl⟩ : syracuseStep 379942559 = 569913839) B569913839
theorem B1644767 : Blo 730325 1644767 := bstep (se 1 (by rfl) ⟨1233575, by rfl⟩ : syracuseStep 1644767 = 2467151) B2467151
theorem B924367 : Blo 730325 924367 := bstep (se 1 (by rfl) ⟨693275, by rfl⟩ : syracuseStep 924367 = 1386551) B1386551
theorem B1647431 : Blo 730325 1647431 := bstep (se 1 (by rfl) ⟨1235573, by rfl⟩ : syracuseStep 1647431 = 2471147) B2471147
theorem B732007 : Blo 730325 732007 := bstep (se 1 (by rfl) ⟨549005, by rfl⟩ : syracuseStep 732007 = 1098011) B1098011
theorem B2469311 : Blo 730325 2469311 := bstep (se 1 (by rfl) ⟨1851983, by rfl⟩ : syracuseStep 2469311 = 3703967) B3703967
theorem B733031 : Blo 730325 733031 := bstep (se 1 (by rfl) ⟨549773, by rfl⟩ : syracuseStep 733031 = 1099547) B1099547
theorem B733435 : Blo 730325 733435 := bstep (se 1 (by rfl) ⟨550076, by rfl⟩ : syracuseStep 733435 = 1100153) B1100153
theorem B734299 : Blo 730325 734299 := bstep (se 1 (by rfl) ⟨550724, by rfl⟩ : syracuseStep 734299 = 1101449) B1101449
theorem B5420251 : Blo 730325 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1098047 : Blo 730325 1098047 := bstep (se 1 (by rfl) ⟨823535, by rfl⟩ : syracuseStep 1098047 = 1647071) B1647071
theorem B1098407 : Blo 730325 1098407 := bstep (se 1 (by rfl) ⟨823805, by rfl⟩ : syracuseStep 1098407 = 1647611) B1647611
theorem B1099529 : Blo 730325 1099529 := bstep (se 2 (by rfl) ⟨412323, by rfl⟩ : syracuseStep 1099529 = 824647) B824647
theorem B2476763 : Blo 730325 2476763 := bstep (se 1 (by rfl) ⟨1857572, by rfl⟩ : syracuseStep 2476763 = 3715145) B3715145
theorem B2478059 : Blo 730325 2478059 := bstep (se 1 (by rfl) ⟨1858544, by rfl⟩ : syracuseStep 2478059 = 3717089) B3717089
theorem B1759727 : Blo 730325 1759727 := bstep (se 1 (by rfl) ⟨1319795, by rfl⟩ : syracuseStep 1759727 = 2639591) B2639591
theorem B1171511 : Blo 730325 1171511 := bstep (se 1 (by rfl) ⟨878633, by rfl⟩ : syracuseStep 1171511 = 1757267) B1757267
theorem B18079847 : Blo 730325 18079847 := bstep (se 1 (by rfl) ⟨13559885, by rfl⟩ : syracuseStep 18079847 = 27119771) B27119771
theorem B2257565 : Blo 730325 2257565 := bstep (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) B846587
theorem B62616239 : Blo 730325 62616239 := bstep (se 1 (by rfl) ⟨46962179, by rfl⟩ : syracuseStep 62616239 = 93924359) B93924359
theorem B2782775 : Blo 730325 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B253295039 : Blo 730325 253295039 := bstep (se 1 (by rfl) ⟨189971279, by rfl⟩ : syracuseStep 253295039 = 379942559) B379942559
theorem B4685147 : Blo 730325 4685147 := bstep (se 1 (by rfl) ⟨3513860, by rfl⟩ : syracuseStep 4685147 = 7027721) B7027721
theorem B6258647 : Blo 730325 6258647 := bstep (se 1 (by rfl) ⟨4693985, by rfl⟩ : syracuseStep 6258647 = 9387971) B9387971
theorem B1646207 : Blo 730325 1646207 := bstep (se 1 (by rfl) ⟨1234655, by rfl⟩ : syracuseStep 1646207 = 2469311) B2469311
theorem B168863359 : Blo 730325 168863359 := bstep (se 1 (by rfl) ⟨126647519, by rfl⟩ : syracuseStep 168863359 = 253295039) B253295039
theorem B3123431 : Blo 730325 3123431 := bstep (se 1 (by rfl) ⟨2342573, by rfl⟩ : syracuseStep 3123431 = 4685147) B4685147
theorem B4172431 : Blo 730325 4172431 := bstep (se 1 (by rfl) ⟨3129323, by rfl⟩ : syracuseStep 4172431 = 6258647) B6258647
theorem B732031 : Blo 730325 732031 := bstep (se 1 (by rfl) ⟨549023, by rfl⟩ : syracuseStep 732031 = 1098047) B1098047
theorem B732271 : Blo 730325 732271 := bstep (se 1 (by rfl) ⟨549203, by rfl⟩ : syracuseStep 732271 = 1098407) B1098407
theorem B733019 : Blo 730325 733019 := bstep (se 1 (by rfl) ⟨549764, by rfl⟩ : syracuseStep 733019 = 1099529) B1099529
theorem B1651175 : Blo 730325 1651175 := bstep (se 1 (by rfl) ⟨1238381, by rfl⟩ : syracuseStep 1651175 = 2476763) B2476763
theorem B1652039 : Blo 730325 1652039 := bstep (se 1 (by rfl) ⟨1239029, by rfl⟩ : syracuseStep 1652039 = 2478059) B2478059
theorem B1096511 : Blo 730325 1096511 := bstep (se 1 (by rfl) ⟨822383, by rfl⟩ : syracuseStep 1096511 = 1644767) B1644767
theorem B1098287 : Blo 730325 1098287 := bstep (se 1 (by rfl) ⟨823715, by rfl⟩ : syracuseStep 1098287 = 1647431) B1647431
theorem B7227001 : Blo 730325 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B1232489 : Blo 730325 1232489 := bstep (se 2 (by rfl) ⟨462183, by rfl⟩ : syracuseStep 1232489 = 924367) B924367
theorem B1855183 : Blo 730325 1855183 := bstep (se 1 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 1855183 = 2782775) B2782775
theorem B6020173 : Blo 730325 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B1173151 : Blo 730325 1173151 := bstep (se 1 (by rfl) ⟨879863, by rfl⟩ : syracuseStep 1173151 = 1759727) B1759727
theorem B781007 : Blo 730325 781007 := bstep (se 1 (by rfl) ⟨585755, by rfl⟩ : syracuseStep 781007 = 1171511) B1171511
theorem B12053231 : Blo 730325 12053231 := bstep (se 1 (by rfl) ⟨9039923, by rfl⟩ : syracuseStep 12053231 = 18079847) B18079847
theorem B41744159 : Blo 730325 41744159 := bstep (se 1 (by rfl) ⟨31308119, by rfl⟩ : syracuseStep 41744159 = 62616239) B62616239
theorem B225151145 : Blo 730325 225151145 := bstep (se 2 (by rfl) ⟨84431679, by rfl⟩ : syracuseStep 225151145 = 168863359) B168863359
theorem B821659 : Blo 730325 821659 := bstep (se 1 (by rfl) ⟨616244, by rfl⟩ : syracuseStep 821659 = 1232489) B1232489
theorem B8035487 : Blo 730325 8035487 := bstep (se 1 (by rfl) ⟨6026615, by rfl⟩ : syracuseStep 8035487 = 12053231) B12053231
theorem B38544005 : Blo 730325 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B27829439 : Blo 730325 27829439 := bstep (se 1 (by rfl) ⟨20872079, by rfl⟩ : syracuseStep 27829439 = 41744159) B41744159
theorem B731007 : Blo 730325 731007 := bstep (se 1 (by rfl) ⟨548255, by rfl⟩ : syracuseStep 731007 = 1096511) B1096511
theorem B732191 : Blo 730325 732191 := bstep (se 1 (by rfl) ⟨549143, by rfl⟩ : syracuseStep 732191 = 1098287) B1098287
theorem B2473577 : Blo 730325 2473577 := bstep (se 2 (by rfl) ⟨927591, by rfl⟩ : syracuseStep 2473577 = 1855183) B1855183
theorem B1097471 : Blo 730325 1097471 := bstep (se 1 (by rfl) ⟨823103, by rfl⟩ : syracuseStep 1097471 = 1646207) B1646207
theorem B2082287 : Blo 730325 2082287 := bstep (se 1 (by rfl) ⟨1561715, by rfl⟩ : syracuseStep 2082287 = 3123431) B3123431
theorem B2082685 : Blo 730325 2082685 := bstep (se 3 (by rfl) ⟨390503, by rfl⟩ : syracuseStep 2082685 = 781007) B781007
theorem B1100783 : Blo 730325 1100783 := bstep (se 1 (by rfl) ⟨825587, by rfl⟩ : syracuseStep 1100783 = 1651175) B1651175
theorem B1101359 : Blo 730325 1101359 := bstep (se 1 (by rfl) ⟨826019, by rfl⟩ : syracuseStep 1101359 = 1652039) B1652039
theorem B1564201 : Blo 730325 1564201 := bstep (se 2 (by rfl) ⟨586575, by rfl⟩ : syracuseStep 1564201 = 1173151) B1173151
theorem B5563241 : Blo 730325 5563241 := bstep (se 2 (by rfl) ⟨2086215, by rfl⟩ : syracuseStep 5563241 = 4172431) B4172431
theorem B32107589 : Blo 730325 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B25696003 : Blo 730325 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B3708827 : Blo 730325 3708827 := bstep (se 1 (by rfl) ⟨2781620, by rfl⟩ : syracuseStep 3708827 = 5563241) B5563241
theorem B18552959 : Blo 730325 18552959 := bstep (se 1 (by rfl) ⟨13914719, by rfl⟩ : syracuseStep 18552959 = 27829439) B27829439
theorem B21405059 : Blo 730325 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B1649051 : Blo 730325 1649051 := bstep (se 1 (by rfl) ⟨1236788, by rfl⟩ : syracuseStep 1649051 = 2473577) B2473577
theorem B731647 : Blo 730325 731647 := bstep (se 1 (by rfl) ⟨548735, by rfl⟩ : syracuseStep 731647 = 1097471) B1097471
theorem B1388191 : Blo 730325 1388191 := bstep (se 1 (by rfl) ⟨1041143, by rfl⟩ : syracuseStep 1388191 = 2082287) B2082287
theorem B2401612213 : Blo 730325 2401612213 := bstep (se 5 (by rfl) ⟨112575572, by rfl⟩ : syracuseStep 2401612213 = 225151145) B225151145
theorem B733855 : Blo 730325 733855 := bstep (se 1 (by rfl) ⟨550391, by rfl⟩ : syracuseStep 733855 = 1100783) B1100783
theorem B734239 : Blo 730325 734239 := bstep (se 1 (by rfl) ⟨550679, by rfl⟩ : syracuseStep 734239 = 1101359) B1101359
theorem B1095545 : Blo 730325 1095545 := bstep (se 2 (by rfl) ⟨410829, by rfl⟩ : syracuseStep 1095545 = 821659) B821659
theorem B5356991 : Blo 730325 5356991 := bstep (se 1 (by rfl) ⟨4017743, by rfl⟩ : syracuseStep 5356991 = 8035487) B8035487
theorem B2085601 : Blo 730325 2085601 := bstep (se 2 (by rfl) ⟨782100, by rfl⟩ : syracuseStep 2085601 = 1564201) B1564201
theorem B2776913 : Blo 730325 2776913 := bstep (se 2 (by rfl) ⟨1041342, by rfl⟩ : syracuseStep 2776913 = 2082685) B2082685
theorem B730363 : Blo 730325 730363 := bstep (se 1 (by rfl) ⟨547772, by rfl⟩ : syracuseStep 730363 = 1095545) B1095545
theorem B2472551 : Blo 730325 2472551 := bstep (se 1 (by rfl) ⟨1854413, by rfl⟩ : syracuseStep 2472551 = 3708827) B3708827
theorem B12368639 : Blo 730325 12368639 := bstep (se 1 (by rfl) ⟨9276479, by rfl⟩ : syracuseStep 12368639 = 18552959) B18552959
theorem B1850921 : Blo 730325 1850921 := bstep (se 2 (by rfl) ⟨694095, by rfl⟩ : syracuseStep 1850921 = 1388191) B1388191
theorem B14270039 : Blo 730325 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B1851275 : Blo 730325 1851275 := bstep (se 1 (by rfl) ⟨1388456, by rfl⟩ : syracuseStep 1851275 = 2776913) B2776913
theorem B1099367 : Blo 730325 1099367 := bstep (se 1 (by rfl) ⟨824525, by rfl⟩ : syracuseStep 1099367 = 1649051) B1649051
theorem B34261337 : Blo 730325 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B3202149617 : Blo 730325 3202149617 := bstep (se 2 (by rfl) ⟨1200806106, by rfl⟩ : syracuseStep 3202149617 = 2401612213) B2401612213
theorem B2780801 : Blo 730325 2780801 := bstep (se 2 (by rfl) ⟨1042800, by rfl⟩ : syracuseStep 2780801 = 2085601) B2085601
theorem B3571327 : Blo 730325 3571327 := bstep (se 1 (by rfl) ⟨2678495, by rfl⟩ : syracuseStep 3571327 = 5356991) B5356991
theorem B91363565 : Blo 730325 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B1648367 : Blo 730325 1648367 := bstep (se 1 (by rfl) ⟨1236275, by rfl⟩ : syracuseStep 1648367 = 2472551) B2472551
theorem B4761769 : Blo 730325 4761769 := bstep (se 2 (by rfl) ⟨1785663, by rfl⟩ : syracuseStep 4761769 = 3571327) B3571327
theorem B9513359 : Blo 730325 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B732911 : Blo 730325 732911 := bstep (se 1 (by rfl) ⟨549683, by rfl⟩ : syracuseStep 732911 = 1099367) B1099367
theorem B32983037 : Blo 730325 32983037 := bstep (se 3 (by rfl) ⟨6184319, by rfl⟩ : syracuseStep 32983037 = 12368639) B12368639
theorem B1853867 : Blo 730325 1853867 := bstep (se 1 (by rfl) ⟨1390400, by rfl⟩ : syracuseStep 1853867 = 2780801) B2780801
theorem B1233947 : Blo 730325 1233947 := bstep (se 1 (by rfl) ⟨925460, by rfl⟩ : syracuseStep 1233947 = 1850921) B1850921
theorem B1234183 : Blo 730325 1234183 := bstep (se 1 (by rfl) ⟨925637, by rfl⟩ : syracuseStep 1234183 = 1851275) B1851275
theorem B2134766411 : Blo 730325 2134766411 := bstep (se 1 (by rfl) ⟨1601074808, by rfl⟩ : syracuseStep 2134766411 = 3202149617) B3202149617
theorem B21988691 : Blo 730325 21988691 := bstep (se 1 (by rfl) ⟨16491518, by rfl⟩ : syracuseStep 21988691 = 32983037) B32983037
theorem B822631 : Blo 730325 822631 := bstep (se 1 (by rfl) ⟨616973, by rfl⟩ : syracuseStep 822631 = 1233947) B1233947
theorem B1645577 : Blo 730325 1645577 := bstep (se 2 (by rfl) ⟨617091, by rfl⟩ : syracuseStep 1645577 = 1234183) B1234183
theorem B1098911 : Blo 730325 1098911 := bstep (se 1 (by rfl) ⟨824183, by rfl⟩ : syracuseStep 1098911 = 1648367) B1648367
theorem B6342239 : Blo 730325 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B1235911 : Blo 730325 1235911 := bstep (se 1 (by rfl) ⟨926933, by rfl⟩ : syracuseStep 1235911 = 1853867) B1853867
theorem B6349025 : Blo 730325 6349025 := bstep (se 2 (by rfl) ⟨2380884, by rfl⟩ : syracuseStep 6349025 = 4761769) B4761769
theorem B60909043 : Blo 730325 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B1423177607 : Blo 730325 1423177607 := bstep (se 1 (by rfl) ⟨1067383205, by rfl⟩ : syracuseStep 1423177607 = 2134766411) B2134766411
theorem B4228159 : Blo 730325 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B4232683 : Blo 730325 4232683 := bstep (se 1 (by rfl) ⟨3174512, by rfl⟩ : syracuseStep 4232683 = 6349025) B6349025
theorem B1647881 : Blo 730325 1647881 := bstep (se 2 (by rfl) ⟨617955, by rfl⟩ : syracuseStep 1647881 = 1235911) B1235911
theorem B732607 : Blo 730325 732607 := bstep (se 1 (by rfl) ⟨549455, by rfl⟩ : syracuseStep 732607 = 1098911) B1098911
theorem B14659127 : Blo 730325 14659127 := bstep (se 1 (by rfl) ⟨10994345, by rfl⟩ : syracuseStep 14659127 = 21988691) B21988691
theorem B81212057 : Blo 730325 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B1096841 : Blo 730325 1096841 := bstep (se 2 (by rfl) ⟨411315, by rfl⟩ : syracuseStep 1096841 = 822631) B822631
theorem B1097051 : Blo 730325 1097051 := bstep (se 1 (by rfl) ⟨822788, by rfl⟩ : syracuseStep 1097051 = 1645577) B1645577
theorem B948785071 : Blo 730325 948785071 := bstep (se 1 (by rfl) ⟨711588803, by rfl⟩ : syracuseStep 948785071 = 1423177607) B1423177607
theorem B5637545 : Blo 730325 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B1265046761 : Blo 730325 1265046761 := bstep (se 2 (by rfl) ⟨474392535, by rfl⟩ : syracuseStep 1265046761 = 948785071) B948785071
theorem B5643577 : Blo 730325 5643577 := bstep (se 2 (by rfl) ⟨2116341, by rfl⟩ : syracuseStep 5643577 = 4232683) B4232683
theorem B9772751 : Blo 730325 9772751 := bstep (se 1 (by rfl) ⟨7329563, by rfl⟩ : syracuseStep 9772751 = 14659127) B14659127
theorem B54141371 : Blo 730325 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B731227 : Blo 730325 731227 := bstep (se 1 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 731227 = 1096841) B1096841
theorem B731367 : Blo 730325 731367 := bstep (se 1 (by rfl) ⟨548525, by rfl⟩ : syracuseStep 731367 = 1097051) B1097051
theorem B1098587 : Blo 730325 1098587 := bstep (se 1 (by rfl) ⟨823940, by rfl⟩ : syracuseStep 1098587 = 1647881) B1647881
theorem B26060669 : Blo 730325 26060669 := bstep (se 3 (by rfl) ⟨4886375, by rfl⟩ : syracuseStep 26060669 = 9772751) B9772751
theorem B732391 : Blo 730325 732391 := bstep (se 1 (by rfl) ⟨549293, by rfl⟩ : syracuseStep 732391 = 1098587) B1098587
theorem B843364507 : Blo 730325 843364507 := bstep (se 1 (by rfl) ⟨632523380, by rfl⟩ : syracuseStep 843364507 = 1265046761) B1265046761
theorem B36094247 : Blo 730325 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B7524769 : Blo 730325 7524769 := bstep (se 2 (by rfl) ⟨2821788, by rfl⟩ : syracuseStep 7524769 = 5643577) B5643577
theorem B3758363 : Blo 730325 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B10033025 : Blo 730325 10033025 := bstep (se 2 (by rfl) ⟨3762384, by rfl⟩ : syracuseStep 10033025 = 7524769) B7524769
theorem B17373779 : Blo 730325 17373779 := bstep (se 1 (by rfl) ⟨13030334, by rfl⟩ : syracuseStep 17373779 = 26060669) B26060669
theorem B24062831 : Blo 730325 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B2505575 : Blo 730325 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B1124486009 : Blo 730325 1124486009 := bstep (se 2 (by rfl) ⟨421682253, by rfl⟩ : syracuseStep 1124486009 = 843364507) B843364507
theorem B11582519 : Blo 730325 11582519 := bstep (se 1 (by rfl) ⟨8686889, by rfl⟩ : syracuseStep 11582519 = 17373779) B17373779
theorem B26754733 : Blo 730325 26754733 := bstep (se 3 (by rfl) ⟨5016512, by rfl⟩ : syracuseStep 26754733 = 10033025) B10033025
theorem B16041887 : Blo 730325 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B749657339 : Blo 730325 749657339 := bstep (se 1 (by rfl) ⟨562243004, by rfl⟩ : syracuseStep 749657339 = 1124486009) B1124486009
theorem B6681533 : Blo 730325 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B123546869 : Blo 730325 123546869 := bstep (se 5 (by rfl) ⟨5791259, by rfl⟩ : syracuseStep 123546869 = 11582519) B11582519
theorem B10694591 : Blo 730325 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B35672977 : Blo 730325 35672977 := bstep (se 2 (by rfl) ⟨13377366, by rfl⟩ : syracuseStep 35672977 = 26754733) B26754733
theorem B17817421 : Blo 730325 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B499771559 : Blo 730325 499771559 := bstep (se 1 (by rfl) ⟨374828669, by rfl⟩ : syracuseStep 499771559 = 749657339) B749657339
theorem B47563969 : Blo 730325 47563969 := bstep (se 2 (by rfl) ⟨17836488, by rfl⟩ : syracuseStep 47563969 = 35672977) B35672977
theorem B82364579 : Blo 730325 82364579 := bstep (se 1 (by rfl) ⟨61773434, by rfl⟩ : syracuseStep 82364579 = 123546869) B123546869
theorem B7129727 : Blo 730325 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B333181039 : Blo 730325 333181039 := bstep (se 1 (by rfl) ⟨249885779, by rfl⟩ : syracuseStep 333181039 = 499771559) B499771559
theorem B23756561 : Blo 730325 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B4753151 : Blo 730325 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B444241385 : Blo 730325 444241385 := bstep (se 2 (by rfl) ⟨166590519, by rfl⟩ : syracuseStep 444241385 = 333181039) B333181039
theorem B15837707 : Blo 730325 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B63418625 : Blo 730325 63418625 := bstep (se 2 (by rfl) ⟨23781984, by rfl⟩ : syracuseStep 63418625 = 47563969) B47563969
theorem B54909719 : Blo 730325 54909719 := bstep (se 1 (by rfl) ⟨41182289, by rfl⟩ : syracuseStep 54909719 = 82364579) B82364579
theorem B296160923 : Blo 730325 296160923 := bstep (se 1 (by rfl) ⟨222120692, by rfl⟩ : syracuseStep 296160923 = 444241385) B444241385
theorem B36606479 : Blo 730325 36606479 := bstep (se 1 (by rfl) ⟨27454859, by rfl⟩ : syracuseStep 36606479 = 54909719) B54909719
theorem B10558471 : Blo 730325 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B42279083 : Blo 730325 42279083 := bstep (se 1 (by rfl) ⟨31709312, by rfl⟩ : syracuseStep 42279083 = 63418625) B63418625
theorem B3168767 : Blo 730325 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B97617277 : Blo 730325 97617277 := bstep (se 3 (by rfl) ⟨18303239, by rfl⟩ : syracuseStep 97617277 = 36606479) B36606479
theorem B28186055 : Blo 730325 28186055 := bstep (se 1 (by rfl) ⟨21139541, by rfl⟩ : syracuseStep 28186055 = 42279083) B42279083
theorem B197440615 : Blo 730325 197440615 := bstep (se 1 (by rfl) ⟨148080461, by rfl⟩ : syracuseStep 197440615 = 296160923) B296160923
theorem B14077961 : Blo 730325 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B8450045 : Blo 730325 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B520625477 : Blo 730325 520625477 := bstep (se 4 (by rfl) ⟨48808638, by rfl⟩ : syracuseStep 520625477 = 97617277) B97617277
theorem B9385307 : Blo 730325 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B18790703 : Blo 730325 18790703 := bstep (se 1 (by rfl) ⟨14093027, by rfl⟩ : syracuseStep 18790703 = 28186055) B28186055
theorem B263254153 : Blo 730325 263254153 := bstep (se 2 (by rfl) ⟨98720307, by rfl⟩ : syracuseStep 263254153 = 197440615) B197440615
theorem B5633363 : Blo 730325 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B347083651 : Blo 730325 347083651 := bstep (se 1 (by rfl) ⟨260312738, by rfl⟩ : syracuseStep 347083651 = 520625477) B520625477
theorem B12527135 : Blo 730325 12527135 := bstep (se 1 (by rfl) ⟨9395351, by rfl⟩ : syracuseStep 12527135 = 18790703) B18790703
theorem B3755575 : Blo 730325 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B351005537 : Blo 730325 351005537 := bstep (se 2 (by rfl) ⟨131627076, by rfl⟩ : syracuseStep 351005537 = 263254153) B263254153
theorem B6256871 : Blo 730325 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B234003691 : Blo 730325 234003691 := bstep (se 1 (by rfl) ⟨175502768, by rfl⟩ : syracuseStep 234003691 = 351005537) B351005537
theorem B4171247 : Blo 730325 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B5007433 : Blo 730325 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B8351423 : Blo 730325 8351423 := bstep (se 1 (by rfl) ⟨6263567, by rfl⟩ : syracuseStep 8351423 = 12527135) B12527135
theorem B462778201 : Blo 730325 462778201 := bstep (se 2 (by rfl) ⟨173541825, by rfl⟩ : syracuseStep 462778201 = 347083651) B347083651
theorem B617037601 : Blo 730325 617037601 := bstep (se 2 (by rfl) ⟨231389100, by rfl⟩ : syracuseStep 617037601 = 462778201) B462778201
theorem B312004921 : Blo 730325 312004921 := bstep (se 2 (by rfl) ⟨117001845, by rfl⟩ : syracuseStep 312004921 = 234003691) B234003691
theorem B6676577 : Blo 730325 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B2780831 : Blo 730325 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B5567615 : Blo 730325 5567615 := bstep (se 1 (by rfl) ⟨4175711, by rfl⟩ : syracuseStep 5567615 = 8351423) B8351423
theorem B3711743 : Blo 730325 3711743 := bstep (se 1 (by rfl) ⟨2783807, by rfl⟩ : syracuseStep 3711743 = 5567615) B5567615
theorem B822716801 : Blo 730325 822716801 := bstep (se 2 (by rfl) ⟨308518800, by rfl⟩ : syracuseStep 822716801 = 617037601) B617037601
theorem B416006561 : Blo 730325 416006561 := bstep (se 2 (by rfl) ⟨156002460, by rfl⟩ : syracuseStep 416006561 = 312004921) B312004921
theorem B1853887 : Blo 730325 1853887 := bstep (se 1 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 1853887 = 2780831) B2780831
theorem B4451051 : Blo 730325 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B548477867 : Blo 730325 548477867 := bstep (se 1 (by rfl) ⟨411358400, by rfl⟩ : syracuseStep 548477867 = 822716801) B822716801
theorem B2471849 : Blo 730325 2471849 := bstep (se 2 (by rfl) ⟨926943, by rfl⟩ : syracuseStep 2471849 = 1853887) B1853887
theorem B2474495 : Blo 730325 2474495 := bstep (se 1 (by rfl) ⟨1855871, by rfl⟩ : syracuseStep 2474495 = 3711743) B3711743
theorem B2967367 : Blo 730325 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B1109350829 : Blo 730325 1109350829 := bstep (se 3 (by rfl) ⟨208003280, by rfl⟩ : syracuseStep 1109350829 = 416006561) B416006561
theorem B1647899 : Blo 730325 1647899 := bstep (se 1 (by rfl) ⟨1235924, by rfl⟩ : syracuseStep 1647899 = 2471849) B2471849
theorem B1649663 : Blo 730325 1649663 := bstep (se 1 (by rfl) ⟨1237247, by rfl⟩ : syracuseStep 1649663 = 2474495) B2474495
theorem B3956489 : Blo 730325 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B739567219 : Blo 730325 739567219 := bstep (se 1 (by rfl) ⟨554675414, by rfl⟩ : syracuseStep 739567219 = 1109350829) B1109350829
theorem B365651911 : Blo 730325 365651911 := bstep (se 1 (by rfl) ⟨274238933, by rfl⟩ : syracuseStep 365651911 = 548477867) B548477867
theorem B986089625 : Blo 730325 986089625 := bstep (se 2 (by rfl) ⟨369783609, by rfl⟩ : syracuseStep 986089625 = 739567219) B739567219
theorem B487535881 : Blo 730325 487535881 := bstep (se 2 (by rfl) ⟨182825955, by rfl⟩ : syracuseStep 487535881 = 365651911) B365651911
theorem B2637659 : Blo 730325 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B1098599 : Blo 730325 1098599 := bstep (se 1 (by rfl) ⟨823949, by rfl⟩ : syracuseStep 1098599 = 1647899) B1647899
theorem B1099775 : Blo 730325 1099775 := bstep (se 1 (by rfl) ⟨824831, by rfl⟩ : syracuseStep 1099775 = 1649663) B1649663
theorem B657393083 : Blo 730325 657393083 := bstep (se 1 (by rfl) ⟨493044812, by rfl⟩ : syracuseStep 657393083 = 986089625) B986089625
theorem B732399 : Blo 730325 732399 := bstep (se 1 (by rfl) ⟨549299, by rfl⟩ : syracuseStep 732399 = 1098599) B1098599
theorem B733183 : Blo 730325 733183 := bstep (se 1 (by rfl) ⟨549887, by rfl⟩ : syracuseStep 733183 = 1099775) B1099775
theorem B1758439 : Blo 730325 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B650047841 : Blo 730325 650047841 := bstep (se 2 (by rfl) ⟨243767940, by rfl⟩ : syracuseStep 650047841 = 487535881) B487535881
theorem B433365227 : Blo 730325 433365227 := bstep (se 1 (by rfl) ⟨325023920, by rfl⟩ : syracuseStep 433365227 = 650047841) B650047841
theorem B2344585 : Blo 730325 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B438262055 : Blo 730325 438262055 := bstep (se 1 (by rfl) ⟨328696541, by rfl⟩ : syracuseStep 438262055 = 657393083) B657393083
theorem B3126113 : Blo 730325 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B292174703 : Blo 730325 292174703 := bstep (se 1 (by rfl) ⟨219131027, by rfl⟩ : syracuseStep 292174703 = 438262055) B438262055
theorem B288910151 : Blo 730325 288910151 := bstep (se 1 (by rfl) ⟨216682613, by rfl⟩ : syracuseStep 288910151 = 433365227) B433365227
theorem B194783135 : Blo 730325 194783135 := bstep (se 1 (by rfl) ⟨146087351, by rfl⟩ : syracuseStep 194783135 = 292174703) B292174703
theorem B2084075 : Blo 730325 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B192606767 : Blo 730325 192606767 := bstep (se 1 (by rfl) ⟨144455075, by rfl⟩ : syracuseStep 192606767 = 288910151) B288910151
theorem B1389383 : Blo 730325 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B519421693 : Blo 730325 519421693 := bstep (se 3 (by rfl) ⟨97391567, by rfl⟩ : syracuseStep 519421693 = 194783135) B194783135
theorem B128404511 : Blo 730325 128404511 := bstep (se 1 (by rfl) ⟨96303383, by rfl⟩ : syracuseStep 128404511 = 192606767) B192606767
theorem B926255 : Blo 730325 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B692562257 : Blo 730325 692562257 := bstep (se 2 (by rfl) ⟨259710846, by rfl⟩ : syracuseStep 692562257 = 519421693) B519421693
theorem B85603007 : Blo 730325 85603007 := bstep (se 1 (by rfl) ⟨64202255, by rfl⟩ : syracuseStep 85603007 = 128404511) B128404511
theorem B461708171 : Blo 730325 461708171 := bstep (se 1 (by rfl) ⟨346281128, by rfl⟩ : syracuseStep 461708171 = 692562257) B692562257
theorem B2470013 : Blo 730325 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B57068671 : Blo 730325 57068671 := bstep (se 1 (by rfl) ⟨42801503, by rfl⟩ : syracuseStep 57068671 = 85603007) B85603007
theorem B76091561 : Blo 730325 76091561 := bstep (se 2 (by rfl) ⟨28534335, by rfl⟩ : syracuseStep 76091561 = 57068671) B57068671
theorem B1646675 : Blo 730325 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B307805447 : Blo 730325 307805447 := bstep (se 1 (by rfl) ⟨230854085, by rfl⟩ : syracuseStep 307805447 = 461708171) B461708171
theorem B50727707 : Blo 730325 50727707 := bstep (se 1 (by rfl) ⟨38045780, by rfl⟩ : syracuseStep 50727707 = 76091561) B76091561
theorem B205203631 : Blo 730325 205203631 := bstep (se 1 (by rfl) ⟨153902723, by rfl⟩ : syracuseStep 205203631 = 307805447) B307805447
theorem B1097783 : Blo 730325 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B33818471 : Blo 730325 33818471 := bstep (se 1 (by rfl) ⟨25363853, by rfl⟩ : syracuseStep 33818471 = 50727707) B50727707
theorem B731855 : Blo 730325 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B273604841 : Blo 730325 273604841 := bstep (se 2 (by rfl) ⟨102601815, by rfl⟩ : syracuseStep 273604841 = 205203631) B205203631
theorem B22545647 : Blo 730325 22545647 := bstep (se 1 (by rfl) ⟨16909235, by rfl⟩ : syracuseStep 22545647 = 33818471) B33818471
theorem B182403227 : Blo 730325 182403227 := bstep (se 1 (by rfl) ⟨136802420, by rfl⟩ : syracuseStep 182403227 = 273604841) B273604841
theorem B121602151 : Blo 730325 121602151 := bstep (se 1 (by rfl) ⟨91201613, by rfl⟩ : syracuseStep 121602151 = 182403227) B182403227
theorem B15030431 : Blo 730325 15030431 := bstep (se 1 (by rfl) ⟨11272823, by rfl⟩ : syracuseStep 15030431 = 22545647) B22545647
theorem B648544805 : Blo 730325 648544805 := bstep (se 4 (by rfl) ⟨60801075, by rfl⟩ : syracuseStep 648544805 = 121602151) B121602151
theorem B10020287 : Blo 730325 10020287 := bstep (se 1 (by rfl) ⟨7515215, by rfl⟩ : syracuseStep 10020287 = 15030431) B15030431
theorem B432363203 : Blo 730325 432363203 := bstep (se 1 (by rfl) ⟨324272402, by rfl⟩ : syracuseStep 432363203 = 648544805) B648544805
theorem B6680191 : Blo 730325 6680191 := bstep (se 1 (by rfl) ⟨5010143, by rfl⟩ : syracuseStep 6680191 = 10020287) B10020287
theorem B288242135 : Blo 730325 288242135 := bstep (se 1 (by rfl) ⟨216181601, by rfl⟩ : syracuseStep 288242135 = 432363203) B432363203
theorem B8906921 : Blo 730325 8906921 := bstep (se 2 (by rfl) ⟨3340095, by rfl⟩ : syracuseStep 8906921 = 6680191) B6680191
theorem B5937947 : Blo 730325 5937947 := bstep (se 1 (by rfl) ⟨4453460, by rfl⟩ : syracuseStep 5937947 = 8906921) B8906921
theorem B192161423 : Blo 730325 192161423 := bstep (se 1 (by rfl) ⟨144121067, by rfl⟩ : syracuseStep 192161423 = 288242135) B288242135
theorem B128107615 : Blo 730325 128107615 := bstep (se 1 (by rfl) ⟨96080711, by rfl⟩ : syracuseStep 128107615 = 192161423) B192161423
theorem B3958631 : Blo 730325 3958631 := bstep (se 1 (by rfl) ⟨2968973, by rfl⟩ : syracuseStep 3958631 = 5937947) B5937947
theorem B2639087 : Blo 730325 2639087 := bstep (se 1 (by rfl) ⟨1979315, by rfl⟩ : syracuseStep 2639087 = 3958631) B3958631
theorem B170810153 : Blo 730325 170810153 := bstep (se 2 (by rfl) ⟨64053807, by rfl⟩ : syracuseStep 170810153 = 128107615) B128107615
theorem B113873435 : Blo 730325 113873435 := bstep (se 1 (by rfl) ⟨85405076, by rfl⟩ : syracuseStep 113873435 = 170810153) B170810153
theorem B1759391 : Blo 730325 1759391 := bstep (se 1 (by rfl) ⟨1319543, by rfl⟩ : syracuseStep 1759391 = 2639087) B2639087
theorem B75915623 : Blo 730325 75915623 := bstep (se 1 (by rfl) ⟨56936717, by rfl⟩ : syracuseStep 75915623 = 113873435) B113873435
theorem B1172927 : Blo 730325 1172927 := bstep (se 1 (by rfl) ⟨879695, by rfl⟩ : syracuseStep 1172927 = 1759391) B1759391
theorem B3127805 : Blo 730325 3127805 := bstep (se 3 (by rfl) ⟨586463, by rfl⟩ : syracuseStep 3127805 = 1172927) B1172927
theorem B50610415 : Blo 730325 50610415 := bstep (se 1 (by rfl) ⟨37957811, by rfl⟩ : syracuseStep 50610415 = 75915623) B75915623
theorem B67480553 : Blo 730325 67480553 := bstep (se 2 (by rfl) ⟨25305207, by rfl⟩ : syracuseStep 67480553 = 50610415) B50610415
theorem B2085203 : Blo 730325 2085203 := bstep (se 1 (by rfl) ⟨1563902, by rfl⟩ : syracuseStep 2085203 = 3127805) B3127805
theorem B1390135 : Blo 730325 1390135 := bstep (se 1 (by rfl) ⟨1042601, by rfl⟩ : syracuseStep 1390135 = 2085203) B2085203
theorem B44987035 : Blo 730325 44987035 := bstep (se 1 (by rfl) ⟨33740276, by rfl⟩ : syracuseStep 44987035 = 67480553) B67480553
theorem B59982713 : Blo 730325 59982713 := bstep (se 2 (by rfl) ⟨22493517, by rfl⟩ : syracuseStep 59982713 = 44987035) B44987035
theorem B1853513 : Blo 730325 1853513 := bstep (se 2 (by rfl) ⟨695067, by rfl⟩ : syracuseStep 1853513 = 1390135) B1390135
theorem B39988475 : Blo 730325 39988475 := bstep (se 1 (by rfl) ⟨29991356, by rfl⟩ : syracuseStep 39988475 = 59982713) B59982713
theorem B1235675 : Blo 730325 1235675 := bstep (se 1 (by rfl) ⟨926756, by rfl⟩ : syracuseStep 1235675 = 1853513) B1853513
theorem B823783 : Blo 730325 823783 := bstep (se 1 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 823783 = 1235675) B1235675
theorem B26658983 : Blo 730325 26658983 := bstep (se 1 (by rfl) ⟨19994237, by rfl⟩ : syracuseStep 26658983 = 39988475) B39988475
theorem B71090621 : Blo 730325 71090621 := bstep (se 3 (by rfl) ⟨13329491, by rfl⟩ : syracuseStep 71090621 = 26658983) B26658983
theorem B1098377 : Blo 730325 1098377 := bstep (se 2 (by rfl) ⟨411891, by rfl⟩ : syracuseStep 1098377 = 823783) B823783
theorem B47393747 : Blo 730325 47393747 := bstep (se 1 (by rfl) ⟨35545310, by rfl⟩ : syracuseStep 47393747 = 71090621) B71090621
theorem B732251 : Blo 730325 732251 := bstep (se 1 (by rfl) ⟨549188, by rfl⟩ : syracuseStep 732251 = 1098377) B1098377
theorem B31595831 : Blo 730325 31595831 := bstep (se 1 (by rfl) ⟨23696873, by rfl⟩ : syracuseStep 31595831 = 47393747) B47393747
theorem B21063887 : Blo 730325 21063887 := bstep (se 1 (by rfl) ⟨15797915, by rfl⟩ : syracuseStep 21063887 = 31595831) B31595831
theorem B14042591 : Blo 730325 14042591 := bstep (se 1 (by rfl) ⟨10531943, by rfl⟩ : syracuseStep 14042591 = 21063887) B21063887
theorem B9361727 : Blo 730325 9361727 := bstep (se 1 (by rfl) ⟨7021295, by rfl⟩ : syracuseStep 9361727 = 14042591) B14042591
theorem B6241151 : Blo 730325 6241151 := bstep (se 1 (by rfl) ⟨4680863, by rfl⟩ : syracuseStep 6241151 = 9361727) B9361727
theorem B4160767 : Blo 730325 4160767 := bstep (se 1 (by rfl) ⟨3120575, by rfl⟩ : syracuseStep 4160767 = 6241151) B6241151
theorem B5547689 : Blo 730325 5547689 := bstep (se 2 (by rfl) ⟨2080383, by rfl⟩ : syracuseStep 5547689 = 4160767) B4160767
theorem B3698459 : Blo 730325 3698459 := bstep (se 1 (by rfl) ⟨2773844, by rfl⟩ : syracuseStep 3698459 = 5547689) B5547689
theorem B2465639 : Blo 730325 2465639 := bstep (se 1 (by rfl) ⟨1849229, by rfl⟩ : syracuseStep 2465639 = 3698459) B3698459
theorem B1643759 : Blo 730325 1643759 := bstep (se 1 (by rfl) ⟨1232819, by rfl⟩ : syracuseStep 1643759 = 2465639) B2465639
theorem B1095839 : Blo 730325 1095839 := bstep (se 1 (by rfl) ⟨821879, by rfl⟩ : syracuseStep 1095839 = 1643759) B1643759
theorem B730559 : Blo 730325 730559 := bstep (se 1 (by rfl) ⟨547919, by rfl⟩ : syracuseStep 730559 = 1095839) B1095839

theorem C0 (j : ℕ) (h1 : 182581 ≤ j) (h2 : j ≤ 183280) : Blo 730325 (4 * j + 3) := by
  interval_cases j
  · exact B730327
  · exact B730331
  · exact B730335
  · exact B730339
  · exact B730343
  · exact B730347
  · exact B730351
  · exact B730355
  · exact B730359
  · exact B730363
  · exact B730367
  · exact B730371
  · exact B730375
  · exact B730379
  · exact B730383
  · exact B730387
  · exact B730391
  · exact B730395
  · exact B730399
  · exact B730403
  · exact B730407
  · exact B730411
  · exact B730415
  · exact B730419
  · exact B730423
  · exact B730427
  · exact B730431
  · exact B730435
  · exact B730439
  · exact B730443
  · exact B730447
  · exact B730451
  · exact B730455
  · exact B730459
  · exact B730463
  · exact B730467
  · exact B730471
  · exact B730475
  · exact B730479
  · exact B730483
  · exact B730487
  · exact B730491
  · exact B730495
  · exact B730499
  · exact B730503
  · exact B730507
  · exact B730511
  · exact B730515
  · exact B730519
  · exact B730523
  · exact B730527
  · exact B730531
  · exact B730535
  · exact B730539
  · exact B730543
  · exact B730547
  · exact B730551
  · exact B730555
  · exact B730559
  · exact B730563
  · exact B730567
  · exact B730571
  · exact B730575
  · exact B730579
  · exact B730583
  · exact B730587
  · exact B730591
  · exact B730595
  · exact B730599
  · exact B730603
  · exact B730607
  · exact B730611
  · exact B730615
  · exact B730619
  · exact B730623
  · exact B730627
  · exact B730631
  · exact B730635
  · exact B730639
  · exact B730643
  · exact B730647
  · exact B730651
  · exact B730655
  · exact B730659
  · exact B730663
  · exact B730667
  · exact B730671
  · exact B730675
  · exact B730679
  · exact B730683
  · exact B730687
  · exact B730691
  · exact B730695
  · exact B730699
  · exact B730703
  · exact B730707
  · exact B730711
  · exact B730715
  · exact B730719
  · exact B730723
  · exact B730727
  · exact B730731
  · exact B730735
  · exact B730739
  · exact B730743
  · exact B730747
  · exact B730751
  · exact B730755
  · exact B730759
  · exact B730763
  · exact B730767
  · exact B730771
  · exact B730775
  · exact B730779
  · exact B730783
  · exact B730787
  · exact B730791
  · exact B730795
  · exact B730799
  · exact B730803
  · exact B730807
  · exact B730811
  · exact B730815
  · exact B730819
  · exact B730823
  · exact B730827
  · exact B730831
  · exact B730835
  · exact B730839
  · exact B730843
  · exact B730847
  · exact B730851
  · exact B730855
  · exact B730859
  · exact B730863
  · exact B730867
  · exact B730871
  · exact B730875
  · exact B730879
  · exact B730883
  · exact B730887
  · exact B730891
  · exact B730895
  · exact B730899
  · exact B730903
  · exact B730907
  · exact B730911
  · exact B730915
  · exact B730919
  · exact B730923
  · exact B730927
  · exact B730931
  · exact B730935
  · exact B730939
  · exact B730943
  · exact B730947
  · exact B730951
  · exact B730955
  · exact B730959
  · exact B730963
  · exact B730967
  · exact B730971
  · exact B730975
  · exact B730979
  · exact B730983
  · exact B730987
  · exact B730991
  · exact B730995
  · exact B730999
  · exact B731003
  · exact B731007
  · exact B731011
  · exact B731015
  · exact B731019
  · exact B731023
  · exact B731027
  · exact B731031
  · exact B731035
  · exact B731039
  · exact B731043
  · exact B731047
  · exact B731051
  · exact B731055
  · exact B731059
  · exact B731063
  · exact B731067
  · exact B731071
  · exact B731075
  · exact B731079
  · exact B731083
  · exact B731087
  · exact B731091
  · exact B731095
  · exact B731099
  · exact B731103
  · exact B731107
  · exact B731111
  · exact B731115
  · exact B731119
  · exact B731123
  · exact B731127
  · exact B731131
  · exact B731135
  · exact B731139
  · exact B731143
  · exact B731147
  · exact B731151
  · exact B731155
  · exact B731159
  · exact B731163
  · exact B731167
  · exact B731171
  · exact B731175
  · exact B731179
  · exact B731183
  · exact B731187
  · exact B731191
  · exact B731195
  · exact B731199
  · exact B731203
  · exact B731207
  · exact B731211
  · exact B731215
  · exact B731219
  · exact B731223
  · exact B731227
  · exact B731231
  · exact B731235
  · exact B731239
  · exact B731243
  · exact B731247
  · exact B731251
  · exact B731255
  · exact B731259
  · exact B731263
  · exact B731267
  · exact B731271
  · exact B731275
  · exact B731279
  · exact B731283
  · exact B731287
  · exact B731291
  · exact B731295
  · exact B731299
  · exact B731303
  · exact B731307
  · exact B731311
  · exact B731315
  · exact B731319
  · exact B731323
  · exact B731327
  · exact B731331
  · exact B731335
  · exact B731339
  · exact B731343
  · exact B731347
  · exact B731351
  · exact B731355
  · exact B731359
  · exact B731363
  · exact B731367
  · exact B731371
  · exact B731375
  · exact B731379
  · exact B731383
  · exact B731387
  · exact B731391
  · exact B731395
  · exact B731399
  · exact B731403
  · exact B731407
  · exact B731411
  · exact B731415
  · exact B731419
  · exact B731423
  · exact B731427
  · exact B731431
  · exact B731435
  · exact B731439
  · exact B731443
  · exact B731447
  · exact B731451
  · exact B731455
  · exact B731459
  · exact B731463
  · exact B731467
  · exact B731471
  · exact B731475
  · exact B731479
  · exact B731483
  · exact B731487
  · exact B731491
  · exact B731495
  · exact B731499
  · exact B731503
  · exact B731507
  · exact B731511
  · exact B731515
  · exact B731519
  · exact B731523
  · exact B731527
  · exact B731531
  · exact B731535
  · exact B731539
  · exact B731543
  · exact B731547
  · exact B731551
  · exact B731555
  · exact B731559
  · exact B731563
  · exact B731567
  · exact B731571
  · exact B731575
  · exact B731579
  · exact B731583
  · exact B731587
  · exact B731591
  · exact B731595
  · exact B731599
  · exact B731603
  · exact B731607
  · exact B731611
  · exact B731615
  · exact B731619
  · exact B731623
  · exact B731627
  · exact B731631
  · exact B731635
  · exact B731639
  · exact B731643
  · exact B731647
  · exact B731651
  · exact B731655
  · exact B731659
  · exact B731663
  · exact B731667
  · exact B731671
  · exact B731675
  · exact B731679
  · exact B731683
  · exact B731687
  · exact B731691
  · exact B731695
  · exact B731699
  · exact B731703
  · exact B731707
  · exact B731711
  · exact B731715
  · exact B731719
  · exact B731723
  · exact B731727
  · exact B731731
  · exact B731735
  · exact B731739
  · exact B731743
  · exact B731747
  · exact B731751
  · exact B731755
  · exact B731759
  · exact B731763
  · exact B731767
  · exact B731771
  · exact B731775
  · exact B731779
  · exact B731783
  · exact B731787
  · exact B731791
  · exact B731795
  · exact B731799
  · exact B731803
  · exact B731807
  · exact B731811
  · exact B731815
  · exact B731819
  · exact B731823
  · exact B731827
  · exact B731831
  · exact B731835
  · exact B731839
  · exact B731843
  · exact B731847
  · exact B731851
  · exact B731855
  · exact B731859
  · exact B731863
  · exact B731867
  · exact B731871
  · exact B731875
  · exact B731879
  · exact B731883
  · exact B731887
  · exact B731891
  · exact B731895
  · exact B731899
  · exact B731903
  · exact B731907
  · exact B731911
  · exact B731915
  · exact B731919
  · exact B731923
  · exact B731927
  · exact B731931
  · exact B731935
  · exact B731939
  · exact B731943
  · exact B731947
  · exact B731951
  · exact B731955
  · exact B731959
  · exact B731963
  · exact B731967
  · exact B731971
  · exact B731975
  · exact B731979
  · exact B731983
  · exact B731987
  · exact B731991
  · exact B731995
  · exact B731999
  · exact B732003
  · exact B732007
  · exact B732011
  · exact B732015
  · exact B732019
  · exact B732023
  · exact B732027
  · exact B732031
  · exact B732035
  · exact B732039
  · exact B732043
  · exact B732047
  · exact B732051
  · exact B732055
  · exact B732059
  · exact B732063
  · exact B732067
  · exact B732071
  · exact B732075
  · exact B732079
  · exact B732083
  · exact B732087
  · exact B732091
  · exact B732095
  · exact B732099
  · exact B732103
  · exact B732107
  · exact B732111
  · exact B732115
  · exact B732119
  · exact B732123
  · exact B732127
  · exact B732131
  · exact B732135
  · exact B732139
  · exact B732143
  · exact B732147
  · exact B732151
  · exact B732155
  · exact B732159
  · exact B732163
  · exact B732167
  · exact B732171
  · exact B732175
  · exact B732179
  · exact B732183
  · exact B732187
  · exact B732191
  · exact B732195
  · exact B732199
  · exact B732203
  · exact B732207
  · exact B732211
  · exact B732215
  · exact B732219
  · exact B732223
  · exact B732227
  · exact B732231
  · exact B732235
  · exact B732239
  · exact B732243
  · exact B732247
  · exact B732251
  · exact B732255
  · exact B732259
  · exact B732263
  · exact B732267
  · exact B732271
  · exact B732275
  · exact B732279
  · exact B732283
  · exact B732287
  · exact B732291
  · exact B732295
  · exact B732299
  · exact B732303
  · exact B732307
  · exact B732311
  · exact B732315
  · exact B732319
  · exact B732323
  · exact B732327
  · exact B732331
  · exact B732335
  · exact B732339
  · exact B732343
  · exact B732347
  · exact B732351
  · exact B732355
  · exact B732359
  · exact B732363
  · exact B732367
  · exact B732371
  · exact B732375
  · exact B732379
  · exact B732383
  · exact B732387
  · exact B732391
  · exact B732395
  · exact B732399
  · exact B732403
  · exact B732407
  · exact B732411
  · exact B732415
  · exact B732419
  · exact B732423
  · exact B732427
  · exact B732431
  · exact B732435
  · exact B732439
  · exact B732443
  · exact B732447
  · exact B732451
  · exact B732455
  · exact B732459
  · exact B732463
  · exact B732467
  · exact B732471
  · exact B732475
  · exact B732479
  · exact B732483
  · exact B732487
  · exact B732491
  · exact B732495
  · exact B732499
  · exact B732503
  · exact B732507
  · exact B732511
  · exact B732515
  · exact B732519
  · exact B732523
  · exact B732527
  · exact B732531
  · exact B732535
  · exact B732539
  · exact B732543
  · exact B732547
  · exact B732551
  · exact B732555
  · exact B732559
  · exact B732563
  · exact B732567
  · exact B732571
  · exact B732575
  · exact B732579
  · exact B732583
  · exact B732587
  · exact B732591
  · exact B732595
  · exact B732599
  · exact B732603
  · exact B732607
  · exact B732611
  · exact B732615
  · exact B732619
  · exact B732623
  · exact B732627
  · exact B732631
  · exact B732635
  · exact B732639
  · exact B732643
  · exact B732647
  · exact B732651
  · exact B732655
  · exact B732659
  · exact B732663
  · exact B732667
  · exact B732671
  · exact B732675
  · exact B732679
  · exact B732683
  · exact B732687
  · exact B732691
  · exact B732695
  · exact B732699
  · exact B732703
  · exact B732707
  · exact B732711
  · exact B732715
  · exact B732719
  · exact B732723
  · exact B732727
  · exact B732731
  · exact B732735
  · exact B732739
  · exact B732743
  · exact B732747
  · exact B732751
  · exact B732755
  · exact B732759
  · exact B732763
  · exact B732767
  · exact B732771
  · exact B732775
  · exact B732779
  · exact B732783
  · exact B732787
  · exact B732791
  · exact B732795
  · exact B732799
  · exact B732803
  · exact B732807
  · exact B732811
  · exact B732815
  · exact B732819
  · exact B732823
  · exact B732827
  · exact B732831
  · exact B732835
  · exact B732839
  · exact B732843
  · exact B732847
  · exact B732851
  · exact B732855
  · exact B732859
  · exact B732863
  · exact B732867
  · exact B732871
  · exact B732875
  · exact B732879
  · exact B732883
  · exact B732887
  · exact B732891
  · exact B732895
  · exact B732899
  · exact B732903
  · exact B732907
  · exact B732911
  · exact B732915
  · exact B732919
  · exact B732923
  · exact B732927
  · exact B732931
  · exact B732935
  · exact B732939
  · exact B732943
  · exact B732947
  · exact B732951
  · exact B732955
  · exact B732959
  · exact B732963
  · exact B732967
  · exact B732971
  · exact B732975
  · exact B732979
  · exact B732983
  · exact B732987
  · exact B732991
  · exact B732995
  · exact B732999
  · exact B733003
  · exact B733007
  · exact B733011
  · exact B733015
  · exact B733019
  · exact B733023
  · exact B733027
  · exact B733031
  · exact B733035
  · exact B733039
  · exact B733043
  · exact B733047
  · exact B733051
  · exact B733055
  · exact B733059
  · exact B733063
  · exact B733067
  · exact B733071
  · exact B733075
  · exact B733079
  · exact B733083
  · exact B733087
  · exact B733091
  · exact B733095
  · exact B733099
  · exact B733103
  · exact B733107
  · exact B733111
  · exact B733115
  · exact B733119
  · exact B733123

theorem C1 (j : ℕ) (h1 : 183281 ≤ j) (h2 : j ≤ 183580) : Blo 730325 (4 * j + 3) := by
  interval_cases j
  · exact B733127
  · exact B733131
  · exact B733135
  · exact B733139
  · exact B733143
  · exact B733147
  · exact B733151
  · exact B733155
  · exact B733159
  · exact B733163
  · exact B733167
  · exact B733171
  · exact B733175
  · exact B733179
  · exact B733183
  · exact B733187
  · exact B733191
  · exact B733195
  · exact B733199
  · exact B733203
  · exact B733207
  · exact B733211
  · exact B733215
  · exact B733219
  · exact B733223
  · exact B733227
  · exact B733231
  · exact B733235
  · exact B733239
  · exact B733243
  · exact B733247
  · exact B733251
  · exact B733255
  · exact B733259
  · exact B733263
  · exact B733267
  · exact B733271
  · exact B733275
  · exact B733279
  · exact B733283
  · exact B733287
  · exact B733291
  · exact B733295
  · exact B733299
  · exact B733303
  · exact B733307
  · exact B733311
  · exact B733315
  · exact B733319
  · exact B733323
  · exact B733327
  · exact B733331
  · exact B733335
  · exact B733339
  · exact B733343
  · exact B733347
  · exact B733351
  · exact B733355
  · exact B733359
  · exact B733363
  · exact B733367
  · exact B733371
  · exact B733375
  · exact B733379
  · exact B733383
  · exact B733387
  · exact B733391
  · exact B733395
  · exact B733399
  · exact B733403
  · exact B733407
  · exact B733411
  · exact B733415
  · exact B733419
  · exact B733423
  · exact B733427
  · exact B733431
  · exact B733435
  · exact B733439
  · exact B733443
  · exact B733447
  · exact B733451
  · exact B733455
  · exact B733459
  · exact B733463
  · exact B733467
  · exact B733471
  · exact B733475
  · exact B733479
  · exact B733483
  · exact B733487
  · exact B733491
  · exact B733495
  · exact B733499
  · exact B733503
  · exact B733507
  · exact B733511
  · exact B733515
  · exact B733519
  · exact B733523
  · exact B733527
  · exact B733531
  · exact B733535
  · exact B733539
  · exact B733543
  · exact B733547
  · exact B733551
  · exact B733555
  · exact B733559
  · exact B733563
  · exact B733567
  · exact B733571
  · exact B733575
  · exact B733579
  · exact B733583
  · exact B733587
  · exact B733591
  · exact B733595
  · exact B733599
  · exact B733603
  · exact B733607
  · exact B733611
  · exact B733615
  · exact B733619
  · exact B733623
  · exact B733627
  · exact B733631
  · exact B733635
  · exact B733639
  · exact B733643
  · exact B733647
  · exact B733651
  · exact B733655
  · exact B733659
  · exact B733663
  · exact B733667
  · exact B733671
  · exact B733675
  · exact B733679
  · exact B733683
  · exact B733687
  · exact B733691
  · exact B733695
  · exact B733699
  · exact B733703
  · exact B733707
  · exact B733711
  · exact B733715
  · exact B733719
  · exact B733723
  · exact B733727
  · exact B733731
  · exact B733735
  · exact B733739
  · exact B733743
  · exact B733747
  · exact B733751
  · exact B733755
  · exact B733759
  · exact B733763
  · exact B733767
  · exact B733771
  · exact B733775
  · exact B733779
  · exact B733783
  · exact B733787
  · exact B733791
  · exact B733795
  · exact B733799
  · exact B733803
  · exact B733807
  · exact B733811
  · exact B733815
  · exact B733819
  · exact B733823
  · exact B733827
  · exact B733831
  · exact B733835
  · exact B733839
  · exact B733843
  · exact B733847
  · exact B733851
  · exact B733855
  · exact B733859
  · exact B733863
  · exact B733867
  · exact B733871
  · exact B733875
  · exact B733879
  · exact B733883
  · exact B733887
  · exact B733891
  · exact B733895
  · exact B733899
  · exact B733903
  · exact B733907
  · exact B733911
  · exact B733915
  · exact B733919
  · exact B733923
  · exact B733927
  · exact B733931
  · exact B733935
  · exact B733939
  · exact B733943
  · exact B733947
  · exact B733951
  · exact B733955
  · exact B733959
  · exact B733963
  · exact B733967
  · exact B733971
  · exact B733975
  · exact B733979
  · exact B733983
  · exact B733987
  · exact B733991
  · exact B733995
  · exact B733999
  · exact B734003
  · exact B734007
  · exact B734011
  · exact B734015
  · exact B734019
  · exact B734023
  · exact B734027
  · exact B734031
  · exact B734035
  · exact B734039
  · exact B734043
  · exact B734047
  · exact B734051
  · exact B734055
  · exact B734059
  · exact B734063
  · exact B734067
  · exact B734071
  · exact B734075
  · exact B734079
  · exact B734083
  · exact B734087
  · exact B734091
  · exact B734095
  · exact B734099
  · exact B734103
  · exact B734107
  · exact B734111
  · exact B734115
  · exact B734119
  · exact B734123
  · exact B734127
  · exact B734131
  · exact B734135
  · exact B734139
  · exact B734143
  · exact B734147
  · exact B734151
  · exact B734155
  · exact B734159
  · exact B734163
  · exact B734167
  · exact B734171
  · exact B734175
  · exact B734179
  · exact B734183
  · exact B734187
  · exact B734191
  · exact B734195
  · exact B734199
  · exact B734203
  · exact B734207
  · exact B734211
  · exact B734215
  · exact B734219
  · exact B734223
  · exact B734227
  · exact B734231
  · exact B734235
  · exact B734239
  · exact B734243
  · exact B734247
  · exact B734251
  · exact B734255
  · exact B734259
  · exact B734263
  · exact B734267
  · exact B734271
  · exact B734275
  · exact B734279
  · exact B734283
  · exact B734287
  · exact B734291
  · exact B734295
  · exact B734299
  · exact B734303
  · exact B734307
  · exact B734311
  · exact B734315
  · exact B734319
  · exact B734323

theorem solution (m : ℕ) (hlo : 730325 ≤ m) (hhi : m ≤ 734325) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 182581 ≤ j := by omega
    have hj2 : j ≤ 183580 := by omega
    have hb : Blo 730325 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 183281 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
