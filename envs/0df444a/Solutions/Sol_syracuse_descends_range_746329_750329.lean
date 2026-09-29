-- Prove2me | solution 1 for syracuse_descends_range_746329_750329
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:15.819234+00:00
-- url     : https://prove2.me/submissions/2f137acb-b7ea-4904-809b-bba3c08bccb1

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


theorem B1802341 : Blo 746329 1802341 := bbase (se 4 (by rfl) ⟨168969, by rfl⟩ : syracuseStep 1802341 = 337939) (by norm_num)
theorem B1441901 : Blo 746329 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B2392229 : Blo 746329 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B2523365 : Blo 746329 2523365 := bbase (se 4 (by rfl) ⟨236565, by rfl⟩ : syracuseStep 2523365 = 473131) (by norm_num)
theorem B2130229 : Blo 746329 2130229 := bbase (se 5 (by rfl) ⟨99854, by rfl⟩ : syracuseStep 2130229 = 199709) (by norm_num)
theorem B852553 : Blo 746329 852553 := bbase (se 2 (by rfl) ⟨319707, by rfl⟩ : syracuseStep 852553 = 639415) (by norm_num)
theorem B4260437 : Blo 746329 4260437 := bbase (se 8 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 4260437 = 49927) (by norm_num)
theorem B2523797 : Blo 746329 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B1540949 : Blo 746329 1540949 := bbase (se 9 (by rfl) ⟨4514, by rfl⟩ : syracuseStep 1540949 = 9029) (by norm_num)
theorem B2524229 : Blo 746329 2524229 := bbase (se 4 (by rfl) ⟨236646, by rfl⟩ : syracuseStep 2524229 = 473293) (by norm_num)
theorem B5407829 : Blo 746329 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B853201 : Blo 746329 853201 := bbase (se 2 (by rfl) ⟨319950, by rfl⟩ : syracuseStep 853201 = 639901) (by norm_num)
theorem B853237 : Blo 746329 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B1344917 : Blo 746329 1344917 := bbase (se 6 (by rfl) ⟨31521, by rfl⟩ : syracuseStep 1344917 = 63043) (by norm_num)
theorem B853429 : Blo 746329 853429 := bbase (se 5 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 853429 = 80009) (by norm_num)
theorem B1705445 : Blo 746329 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B2524661 : Blo 746329 2524661 := bbase (se 5 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 2524661 = 236687) (by norm_num)
theorem B2131733 : Blo 746329 2131733 := bbase (se 6 (by rfl) ⟨49962, by rfl⟩ : syracuseStep 2131733 = 99925) (by norm_num)
theorem B2525093 : Blo 746329 2525093 := bbase (se 4 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 2525093 = 473455) (by norm_num)
theorem B1345493 : Blo 746329 1345493 := bbase (se 7 (by rfl) ⟨15767, by rfl⟩ : syracuseStep 1345493 = 31535) (by norm_num)
theorem B854077 : Blo 746329 854077 := bbase (se 3 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 854077 = 320279) (by norm_num)
theorem B7178453 : Blo 746329 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B821485 : Blo 746329 821485 := bbase (se 3 (by rfl) ⟨154028, by rfl⟩ : syracuseStep 821485 = 308057) (by norm_num)
theorem B2525525 : Blo 746329 2525525 := bbase (se 10 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 2525525 = 7399) (by norm_num)
theorem B2394485 : Blo 746329 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B854477 : Blo 746329 854477 := bbase (se 3 (by rfl) ⟨160214, by rfl⟩ : syracuseStep 854477 = 320429) (by norm_num)
theorem B4262645 : Blo 746329 4262645 := bbase (se 5 (by rfl) ⟨199811, by rfl⟩ : syracuseStep 4262645 = 399623) (by norm_num)
theorem B2525957 : Blo 746329 2525957 := bbase (se 4 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 2525957 = 473617) (by norm_num)
theorem B756649 : Blo 746329 756649 := bbase (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) (by norm_num)
theorem B2526389 : Blo 746329 2526389 := bbase (se 5 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 2526389 = 236849) (by norm_num)
theorem B1346797 : Blo 746329 1346797 := bbase (se 3 (by rfl) ⟨252524, by rfl⟩ : syracuseStep 1346797 = 505049) (by norm_num)
theorem B855317 : Blo 746329 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B2133317 : Blo 746329 2133317 := bbase (se 4 (by rfl) ⟨199998, by rfl⟩ : syracuseStep 2133317 = 399997) (by norm_num)
theorem B2526821 : Blo 746329 2526821 := bbase (se 4 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 2526821 = 473779) (by norm_num)
theorem B1347517 : Blo 746329 1347517 := bbase (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) (by norm_num)
theorem B3411925 : Blo 746329 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B2133989 : Blo 746329 2133989 := bbase (se 4 (by rfl) ⟨200061, by rfl⟩ : syracuseStep 2133989 = 400123) (by norm_num)
theorem B2527253 : Blo 746329 2527253 := bbase (se 6 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 2527253 = 118465) (by norm_num)
theorem B757793 : Blo 746329 757793 := bbase (se 2 (by rfl) ⟨284172, by rfl⟩ : syracuseStep 757793 = 568345) (by norm_num)
theorem B5673077 : Blo 746329 5673077 := bbase (se 5 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 5673077 = 531851) (by norm_num)
theorem B2134421 : Blo 746329 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B2527685 : Blo 746329 2527685 := bbase (se 4 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 2527685 = 473941) (by norm_num)
theorem B1282565 : Blo 746329 1282565 := bbase (se 4 (by rfl) ⟨120240, by rfl⟩ : syracuseStep 1282565 = 240481) (by norm_num)
theorem B2691605 : Blo 746329 2691605 := bbase (se 6 (by rfl) ⟨63084, by rfl⟩ : syracuseStep 2691605 = 126169) (by norm_num)
theorem B1217045 : Blo 746329 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B1348181 : Blo 746329 1348181 := bbase (se 8 (by rfl) ⟨7899, by rfl⟩ : syracuseStep 1348181 = 15799) (by norm_num)
theorem B2528117 : Blo 746329 2528117 := bbase (se 5 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 2528117 = 237011) (by norm_num)
theorem B758741 : Blo 746329 758741 := bbase (se 7 (by rfl) ⟨8891, by rfl⟩ : syracuseStep 758741 = 17783) (by norm_num)
theorem B2135173 : Blo 746329 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B759013 : Blo 746329 759013 := bbase (se 4 (by rfl) ⟨71157, by rfl⟩ : syracuseStep 759013 = 142315) (by norm_num)
theorem B1119509 : Blo 746329 1119509 := bbase (se 6 (by rfl) ⟨26238, by rfl⟩ : syracuseStep 1119509 = 52477) (by norm_num)
theorem B2528549 : Blo 746329 2528549 := bbase (se 4 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 2528549 = 474103) (by norm_num)
theorem B1119533 : Blo 746329 1119533 := bbase (se 3 (by rfl) ⟨209912, by rfl⟩ : syracuseStep 1119533 = 419825) (by norm_num)
theorem B1119557 : Blo 746329 1119557 := bbase (se 4 (by rfl) ⟨104958, by rfl⟩ : syracuseStep 1119557 = 209917) (by norm_num)
theorem B1119581 : Blo 746329 1119581 := bbase (se 3 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 1119581 = 419843) (by norm_num)
theorem B1119605 : Blo 746329 1119605 := bbase (se 5 (by rfl) ⟨52481, by rfl⟩ : syracuseStep 1119605 = 104963) (by norm_num)
theorem B1119629 : Blo 746329 1119629 := bbase (se 3 (by rfl) ⟨209930, by rfl⟩ : syracuseStep 1119629 = 419861) (by norm_num)
theorem B1119653 : Blo 746329 1119653 := bbase (se 4 (by rfl) ⟨104967, by rfl⟩ : syracuseStep 1119653 = 209935) (by norm_num)
theorem B1119677 : Blo 746329 1119677 := bbase (se 3 (by rfl) ⟨209939, by rfl⟩ : syracuseStep 1119677 = 419879) (by norm_num)
theorem B1119701 : Blo 746329 1119701 := bbase (se 7 (by rfl) ⟨13121, by rfl⟩ : syracuseStep 1119701 = 26243) (by norm_num)
theorem B1119725 : Blo 746329 1119725 := bbase (se 3 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 1119725 = 419897) (by norm_num)
theorem B1119749 : Blo 746329 1119749 := bbase (se 4 (by rfl) ⟨104976, by rfl⟩ : syracuseStep 1119749 = 209953) (by norm_num)
theorem B759305 : Blo 746329 759305 := bbase (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) (by norm_num)
theorem B1119773 : Blo 746329 1119773 := bbase (se 3 (by rfl) ⟨209957, by rfl⟩ : syracuseStep 1119773 = 419915) (by norm_num)
theorem B759325 : Blo 746329 759325 := bbase (se 3 (by rfl) ⟨142373, by rfl⟩ : syracuseStep 759325 = 284747) (by norm_num)
theorem B1119797 : Blo 746329 1119797 := bbase (se 5 (by rfl) ⟨52490, by rfl⟩ : syracuseStep 1119797 = 104981) (by norm_num)
theorem B3413573 : Blo 746329 3413573 := bbase (se 4 (by rfl) ⟨320022, by rfl⟩ : syracuseStep 3413573 = 640045) (by norm_num)
theorem B1119821 : Blo 746329 1119821 := bbase (se 3 (by rfl) ⟨209966, by rfl⟩ : syracuseStep 1119821 = 419933) (by norm_num)
theorem B1119845 : Blo 746329 1119845 := bbase (se 4 (by rfl) ⟨104985, by rfl⟩ : syracuseStep 1119845 = 209971) (by norm_num)
theorem B1119869 : Blo 746329 1119869 := bbase (se 3 (by rfl) ⟨209975, by rfl⟩ : syracuseStep 1119869 = 419951) (by norm_num)
theorem B1119893 : Blo 746329 1119893 := bbase (se 6 (by rfl) ⟨26247, by rfl⟩ : syracuseStep 1119893 = 52495) (by norm_num)
theorem B1119917 : Blo 746329 1119917 := bbase (se 3 (by rfl) ⟨209984, by rfl⟩ : syracuseStep 1119917 = 419969) (by norm_num)
theorem B1119941 : Blo 746329 1119941 := bbase (se 4 (by rfl) ⟨104994, by rfl⟩ : syracuseStep 1119941 = 209989) (by norm_num)
theorem B2528981 : Blo 746329 2528981 := bbase (se 7 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 2528981 = 59273) (by norm_num)
theorem B1119965 : Blo 746329 1119965 := bbase (se 3 (by rfl) ⟨209993, by rfl⟩ : syracuseStep 1119965 = 419987) (by norm_num)
theorem B1119989 : Blo 746329 1119989 := bbase (se 5 (by rfl) ⟨52499, by rfl⟩ : syracuseStep 1119989 = 104999) (by norm_num)
theorem B1120013 : Blo 746329 1120013 := bbase (se 3 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 1120013 = 420005) (by norm_num)
theorem B1120037 : Blo 746329 1120037 := bbase (se 4 (by rfl) ⟨105003, by rfl⟩ : syracuseStep 1120037 = 210007) (by norm_num)
theorem B1120061 : Blo 746329 1120061 := bbase (se 3 (by rfl) ⟨210011, by rfl⟩ : syracuseStep 1120061 = 420023) (by norm_num)
theorem B1120085 : Blo 746329 1120085 := bbase (se 9 (by rfl) ⟨3281, by rfl⟩ : syracuseStep 1120085 = 6563) (by norm_num)
theorem B1120109 : Blo 746329 1120109 := bbase (se 3 (by rfl) ⟨210020, by rfl⟩ : syracuseStep 1120109 = 420041) (by norm_num)
theorem B1120133 : Blo 746329 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B1120157 : Blo 746329 1120157 := bbase (se 3 (by rfl) ⟨210029, by rfl⟩ : syracuseStep 1120157 = 420059) (by norm_num)
theorem B1120181 : Blo 746329 1120181 := bbase (se 5 (by rfl) ⟨52508, by rfl⟩ : syracuseStep 1120181 = 105017) (by norm_num)
theorem B1120205 : Blo 746329 1120205 := bbase (se 3 (by rfl) ⟨210038, by rfl⟩ : syracuseStep 1120205 = 420077) (by norm_num)
theorem B1120229 : Blo 746329 1120229 := bbase (se 4 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 1120229 = 210043) (by norm_num)
theorem B1120253 : Blo 746329 1120253 := bbase (se 3 (by rfl) ⟨210047, by rfl⟩ : syracuseStep 1120253 = 420095) (by norm_num)
theorem B1120277 : Blo 746329 1120277 := bbase (se 6 (by rfl) ⟨26256, by rfl⟩ : syracuseStep 1120277 = 52513) (by norm_num)
theorem B1120301 : Blo 746329 1120301 := bbase (se 3 (by rfl) ⟨210056, by rfl⟩ : syracuseStep 1120301 = 420113) (by norm_num)
theorem B1120325 : Blo 746329 1120325 := bbase (se 4 (by rfl) ⟨105030, by rfl⟩ : syracuseStep 1120325 = 210061) (by norm_num)
theorem B759889 : Blo 746329 759889 := bbase (se 2 (by rfl) ⟨284958, by rfl⟩ : syracuseStep 759889 = 569917) (by norm_num)
theorem B1120349 : Blo 746329 1120349 := bbase (se 3 (by rfl) ⟨210065, by rfl⟩ : syracuseStep 1120349 = 420131) (by norm_num)
theorem B1120373 : Blo 746329 1120373 := bbase (se 5 (by rfl) ⟨52517, by rfl⟩ : syracuseStep 1120373 = 105035) (by norm_num)
theorem B2529413 : Blo 746329 2529413 := bbase (se 4 (by rfl) ⟨237132, by rfl⟩ : syracuseStep 2529413 = 474265) (by norm_num)
theorem B1120397 : Blo 746329 1120397 := bbase (se 3 (by rfl) ⟨210074, by rfl⟩ : syracuseStep 1120397 = 420149) (by norm_num)
theorem B1120421 : Blo 746329 1120421 := bbase (se 4 (by rfl) ⟨105039, by rfl⟩ : syracuseStep 1120421 = 210079) (by norm_num)
theorem B1120445 : Blo 746329 1120445 := bbase (se 3 (by rfl) ⟨210083, by rfl⟩ : syracuseStep 1120445 = 420167) (by norm_num)
theorem B2398405 : Blo 746329 2398405 := bbase (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) (by norm_num)
theorem B1120469 : Blo 746329 1120469 := bbase (se 7 (by rfl) ⟨13130, by rfl⟩ : syracuseStep 1120469 = 26261) (by norm_num)
theorem B1120493 : Blo 746329 1120493 := bbase (se 3 (by rfl) ⟨210092, by rfl⟩ : syracuseStep 1120493 = 420185) (by norm_num)
theorem B1120517 : Blo 746329 1120517 := bbase (se 4 (by rfl) ⟨105048, by rfl⟩ : syracuseStep 1120517 = 210097) (by norm_num)
theorem B1120541 : Blo 746329 1120541 := bbase (se 3 (by rfl) ⟨210101, by rfl⟩ : syracuseStep 1120541 = 420203) (by norm_num)
theorem B1120565 : Blo 746329 1120565 := bbase (se 5 (by rfl) ⟨52526, by rfl⟩ : syracuseStep 1120565 = 105053) (by norm_num)
theorem B1120589 : Blo 746329 1120589 := bbase (se 3 (by rfl) ⟨210110, by rfl⟩ : syracuseStep 1120589 = 420221) (by norm_num)
theorem B1120613 : Blo 746329 1120613 := bbase (se 4 (by rfl) ⟨105057, by rfl⟩ : syracuseStep 1120613 = 210115) (by norm_num)
theorem B1120637 : Blo 746329 1120637 := bbase (se 3 (by rfl) ⟨210119, by rfl⟩ : syracuseStep 1120637 = 420239) (by norm_num)
theorem B9083285 : Blo 746329 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B1120661 : Blo 746329 1120661 := bbase (se 6 (by rfl) ⟨26265, by rfl⟩ : syracuseStep 1120661 = 52531) (by norm_num)
theorem B1120685 : Blo 746329 1120685 := bbase (se 3 (by rfl) ⟨210128, by rfl⟩ : syracuseStep 1120685 = 420257) (by norm_num)
theorem B760249 : Blo 746329 760249 := bbase (se 2 (by rfl) ⟨285093, by rfl⟩ : syracuseStep 760249 = 570187) (by norm_num)
theorem B1120709 : Blo 746329 1120709 := bbase (se 4 (by rfl) ⟨105066, by rfl⟩ : syracuseStep 1120709 = 210133) (by norm_num)
theorem B2398661 : Blo 746329 2398661 := bbase (se 4 (by rfl) ⟨224874, by rfl⟩ : syracuseStep 2398661 = 449749) (by norm_num)
theorem B1120733 : Blo 746329 1120733 := bbase (se 3 (by rfl) ⟨210137, by rfl⟩ : syracuseStep 1120733 = 420275) (by norm_num)
theorem B1120757 : Blo 746329 1120757 := bbase (se 5 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 1120757 = 105071) (by norm_num)
theorem B1120781 : Blo 746329 1120781 := bbase (se 3 (by rfl) ⟨210146, by rfl⟩ : syracuseStep 1120781 = 420293) (by norm_num)
theorem B1120805 : Blo 746329 1120805 := bbase (se 4 (by rfl) ⟨105075, by rfl⟩ : syracuseStep 1120805 = 210151) (by norm_num)
theorem B2529845 : Blo 746329 2529845 := bbase (se 5 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 2529845 = 237173) (by norm_num)
theorem B1120829 : Blo 746329 1120829 := bbase (se 3 (by rfl) ⟨210155, by rfl⟩ : syracuseStep 1120829 = 420311) (by norm_num)
theorem B1120853 : Blo 746329 1120853 := bbase (se 8 (by rfl) ⟨6567, by rfl⟩ : syracuseStep 1120853 = 13135) (by norm_num)
theorem B1120877 : Blo 746329 1120877 := bbase (se 3 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 1120877 = 420329) (by norm_num)
theorem B1120901 : Blo 746329 1120901 := bbase (se 4 (by rfl) ⟨105084, by rfl⟩ : syracuseStep 1120901 = 210169) (by norm_num)
theorem B1514141 : Blo 746329 1514141 := bbase (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) (by norm_num)
theorem B1120925 : Blo 746329 1120925 := bbase (se 3 (by rfl) ⟨210173, by rfl⟩ : syracuseStep 1120925 = 420347) (by norm_num)
theorem B1120949 : Blo 746329 1120949 := bbase (se 5 (by rfl) ⟨52544, by rfl⟩ : syracuseStep 1120949 = 105089) (by norm_num)
theorem B1120973 : Blo 746329 1120973 := bbase (se 3 (by rfl) ⟨210182, by rfl⟩ : syracuseStep 1120973 = 420365) (by norm_num)
theorem B1120997 : Blo 746329 1120997 := bbase (se 4 (by rfl) ⟨105093, by rfl⟩ : syracuseStep 1120997 = 210187) (by norm_num)
theorem B1121021 : Blo 746329 1121021 := bbase (se 3 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 1121021 = 420383) (by norm_num)
theorem B1121045 : Blo 746329 1121045 := bbase (se 6 (by rfl) ⟨26274, by rfl⟩ : syracuseStep 1121045 = 52549) (by norm_num)
theorem B1121069 : Blo 746329 1121069 := bbase (se 3 (by rfl) ⟨210200, by rfl⟩ : syracuseStep 1121069 = 420401) (by norm_num)
theorem B1121093 : Blo 746329 1121093 := bbase (se 4 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 1121093 = 210205) (by norm_num)
theorem B8624981 : Blo 746329 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B1121117 : Blo 746329 1121117 := bbase (se 3 (by rfl) ⟨210209, by rfl⟩ : syracuseStep 1121117 = 420419) (by norm_num)
theorem B1121141 : Blo 746329 1121141 := bbase (se 5 (by rfl) ⟨52553, by rfl⟩ : syracuseStep 1121141 = 105107) (by norm_num)
theorem B1121165 : Blo 746329 1121165 := bbase (se 3 (by rfl) ⟨210218, by rfl⟩ : syracuseStep 1121165 = 420437) (by norm_num)
theorem B1121189 : Blo 746329 1121189 := bbase (se 4 (by rfl) ⟨105111, by rfl⟩ : syracuseStep 1121189 = 210223) (by norm_num)
theorem B1121213 : Blo 746329 1121213 := bbase (se 3 (by rfl) ⟨210227, by rfl⟩ : syracuseStep 1121213 = 420455) (by norm_num)
theorem B1350589 : Blo 746329 1350589 := bbase (se 3 (by rfl) ⟨253235, by rfl⟩ : syracuseStep 1350589 = 506471) (by norm_num)
theorem B1121237 : Blo 746329 1121237 := bbase (se 7 (by rfl) ⟨13139, by rfl⟩ : syracuseStep 1121237 = 26279) (by norm_num)
theorem B2530277 : Blo 746329 2530277 := bbase (se 4 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 2530277 = 474427) (by norm_num)
theorem B1121261 : Blo 746329 1121261 := bbase (se 3 (by rfl) ⟨210236, by rfl⟩ : syracuseStep 1121261 = 420473) (by norm_num)
theorem B1121285 : Blo 746329 1121285 := bbase (se 4 (by rfl) ⟨105120, by rfl⟩ : syracuseStep 1121285 = 210241) (by norm_num)
theorem B1121309 : Blo 746329 1121309 := bbase (se 3 (by rfl) ⟨210245, by rfl⟩ : syracuseStep 1121309 = 420491) (by norm_num)
theorem B1121333 : Blo 746329 1121333 := bbase (se 5 (by rfl) ⟨52562, by rfl⟩ : syracuseStep 1121333 = 105125) (by norm_num)
theorem B1121357 : Blo 746329 1121357 := bbase (se 3 (by rfl) ⟨210254, by rfl⟩ : syracuseStep 1121357 = 420509) (by norm_num)
theorem B2104421 : Blo 746329 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B1121381 : Blo 746329 1121381 := bbase (se 4 (by rfl) ⟨105129, by rfl⟩ : syracuseStep 1121381 = 210259) (by norm_num)
theorem B1121405 : Blo 746329 1121405 := bbase (se 3 (by rfl) ⟨210263, by rfl⟩ : syracuseStep 1121405 = 420527) (by norm_num)
theorem B1121429 : Blo 746329 1121429 := bbase (se 6 (by rfl) ⟨26283, by rfl⟩ : syracuseStep 1121429 = 52567) (by norm_num)
theorem B1121453 : Blo 746329 1121453 := bbase (se 3 (by rfl) ⟨210272, by rfl⟩ : syracuseStep 1121453 = 420545) (by norm_num)
theorem B1121477 : Blo 746329 1121477 := bbase (se 4 (by rfl) ⟨105138, by rfl⟩ : syracuseStep 1121477 = 210277) (by norm_num)
theorem B1121501 : Blo 746329 1121501 := bbase (se 3 (by rfl) ⟨210281, by rfl⟩ : syracuseStep 1121501 = 420563) (by norm_num)
theorem B1121525 : Blo 746329 1121525 := bbase (se 5 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 1121525 = 105143) (by norm_num)
theorem B1121549 : Blo 746329 1121549 := bbase (se 3 (by rfl) ⟨210290, by rfl⟩ : syracuseStep 1121549 = 420581) (by norm_num)
theorem B1121573 : Blo 746329 1121573 := bbase (se 4 (by rfl) ⟨105147, by rfl⟩ : syracuseStep 1121573 = 210295) (by norm_num)
theorem B1121597 : Blo 746329 1121597 := bbase (se 3 (by rfl) ⟨210299, by rfl⟩ : syracuseStep 1121597 = 420599) (by norm_num)
theorem B1121621 : Blo 746329 1121621 := bbase (se 11 (by rfl) ⟨821, by rfl⟩ : syracuseStep 1121621 = 1643) (by norm_num)
theorem B1121645 : Blo 746329 1121645 := bbase (se 3 (by rfl) ⟨210308, by rfl⟩ : syracuseStep 1121645 = 420617) (by norm_num)
theorem B1121669 : Blo 746329 1121669 := bbase (se 4 (by rfl) ⟨105156, by rfl⟩ : syracuseStep 1121669 = 210313) (by norm_num)
theorem B2530709 : Blo 746329 2530709 := bbase (se 6 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 2530709 = 118627) (by norm_num)
theorem B1121693 : Blo 746329 1121693 := bbase (se 3 (by rfl) ⟨210317, by rfl⟩ : syracuseStep 1121693 = 420635) (by norm_num)
theorem B1121717 : Blo 746329 1121717 := bbase (se 5 (by rfl) ⟨52580, by rfl⟩ : syracuseStep 1121717 = 105161) (by norm_num)
theorem B1351093 : Blo 746329 1351093 := bbase (se 5 (by rfl) ⟨63332, by rfl⟩ : syracuseStep 1351093 = 126665) (by norm_num)
theorem B1121741 : Blo 746329 1121741 := bbase (se 3 (by rfl) ⟨210326, by rfl⟩ : syracuseStep 1121741 = 420653) (by norm_num)
theorem B1121765 : Blo 746329 1121765 := bbase (se 4 (by rfl) ⟨105165, by rfl⟩ : syracuseStep 1121765 = 210331) (by norm_num)
theorem B1121789 : Blo 746329 1121789 := bbase (se 3 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 1121789 = 420671) (by norm_num)
theorem B1121813 : Blo 746329 1121813 := bbase (se 6 (by rfl) ⟨26292, by rfl⟩ : syracuseStep 1121813 = 52585) (by norm_num)
theorem B1121837 : Blo 746329 1121837 := bbase (se 3 (by rfl) ⟨210344, by rfl⟩ : syracuseStep 1121837 = 420689) (by norm_num)
theorem B1121861 : Blo 746329 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B1121885 : Blo 746329 1121885 := bbase (se 3 (by rfl) ⟨210353, by rfl⟩ : syracuseStep 1121885 = 420707) (by norm_num)
theorem B1121909 : Blo 746329 1121909 := bbase (se 5 (by rfl) ⟨52589, by rfl⟩ : syracuseStep 1121909 = 105179) (by norm_num)
theorem B1121933 : Blo 746329 1121933 := bbase (se 3 (by rfl) ⟨210362, by rfl⟩ : syracuseStep 1121933 = 420725) (by norm_num)
theorem B1121957 : Blo 746329 1121957 := bbase (se 4 (by rfl) ⟨105183, by rfl⟩ : syracuseStep 1121957 = 210367) (by norm_num)
theorem B1121981 : Blo 746329 1121981 := bbase (se 3 (by rfl) ⟨210371, by rfl⟩ : syracuseStep 1121981 = 420743) (by norm_num)
theorem B1122005 : Blo 746329 1122005 := bbase (se 7 (by rfl) ⟨13148, by rfl⟩ : syracuseStep 1122005 = 26297) (by norm_num)
theorem B1122029 : Blo 746329 1122029 := bbase (se 3 (by rfl) ⟨210380, by rfl⟩ : syracuseStep 1122029 = 420761) (by norm_num)
theorem B1122053 : Blo 746329 1122053 := bbase (se 4 (by rfl) ⟨105192, by rfl⟩ : syracuseStep 1122053 = 210385) (by norm_num)
theorem B1122077 : Blo 746329 1122077 := bbase (se 3 (by rfl) ⟨210389, by rfl⟩ : syracuseStep 1122077 = 420779) (by norm_num)
theorem B958249 : Blo 746329 958249 := bbase (se 2 (by rfl) ⟨359343, by rfl⟩ : syracuseStep 958249 = 718687) (by norm_num)
theorem B1122101 : Blo 746329 1122101 := bbase (se 5 (by rfl) ⟨52598, by rfl⟩ : syracuseStep 1122101 = 105197) (by norm_num)
theorem B1941317 : Blo 746329 1941317 := bbase (se 4 (by rfl) ⟨181998, by rfl⟩ : syracuseStep 1941317 = 363997) (by norm_num)
theorem B2531141 : Blo 746329 2531141 := bbase (se 4 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 2531141 = 474589) (by norm_num)
theorem B1122125 : Blo 746329 1122125 := bbase (se 3 (by rfl) ⟨210398, by rfl⟩ : syracuseStep 1122125 = 420797) (by norm_num)
theorem B1122149 : Blo 746329 1122149 := bbase (se 4 (by rfl) ⟨105201, by rfl⟩ : syracuseStep 1122149 = 210403) (by norm_num)
theorem B1417085 : Blo 746329 1417085 := bbase (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) (by norm_num)
theorem B1122173 : Blo 746329 1122173 := bbase (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) (by norm_num)
theorem B1122197 : Blo 746329 1122197 := bbase (se 6 (by rfl) ⟨26301, by rfl⟩ : syracuseStep 1122197 = 52603) (by norm_num)
theorem B1122221 : Blo 746329 1122221 := bbase (se 3 (by rfl) ⟨210416, by rfl⟩ : syracuseStep 1122221 = 420833) (by norm_num)
theorem B958393 : Blo 746329 958393 := bbase (se 2 (by rfl) ⟨359397, by rfl⟩ : syracuseStep 958393 = 718795) (by norm_num)
theorem B1122245 : Blo 746329 1122245 := bbase (se 4 (by rfl) ⟨105210, by rfl⟩ : syracuseStep 1122245 = 210421) (by norm_num)
theorem B1679309 : Blo 746329 1679309 := bbase (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) (by norm_num)
theorem B1122269 : Blo 746329 1122269 := bbase (se 3 (by rfl) ⟨210425, by rfl⟩ : syracuseStep 1122269 = 420851) (by norm_num)
theorem B1122293 : Blo 746329 1122293 := bbase (se 5 (by rfl) ⟨52607, by rfl⟩ : syracuseStep 1122293 = 105215) (by norm_num)
theorem B1122317 : Blo 746329 1122317 := bbase (se 3 (by rfl) ⟨210434, by rfl⟩ : syracuseStep 1122317 = 420869) (by norm_num)
theorem B1679381 : Blo 746329 1679381 := bbase (se 6 (by rfl) ⟨39360, by rfl⟩ : syracuseStep 1679381 = 78721) (by norm_num)
theorem B1122341 : Blo 746329 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B1122365 : Blo 746329 1122365 := bbase (se 3 (by rfl) ⟨210443, by rfl⟩ : syracuseStep 1122365 = 420887) (by norm_num)
theorem B1122389 : Blo 746329 1122389 := bbase (se 8 (by rfl) ⟨6576, by rfl⟩ : syracuseStep 1122389 = 13153) (by norm_num)
theorem B1679453 : Blo 746329 1679453 := bbase (se 3 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 1679453 = 629795) (by norm_num)
theorem B1122413 : Blo 746329 1122413 := bbase (se 3 (by rfl) ⟨210452, by rfl⟩ : syracuseStep 1122413 = 420905) (by norm_num)
theorem B1122437 : Blo 746329 1122437 := bbase (se 4 (by rfl) ⟨105228, by rfl⟩ : syracuseStep 1122437 = 210457) (by norm_num)
theorem B1122461 : Blo 746329 1122461 := bbase (se 3 (by rfl) ⟨210461, by rfl⟩ : syracuseStep 1122461 = 420923) (by norm_num)
theorem B1679525 : Blo 746329 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B1122485 : Blo 746329 1122485 := bbase (se 5 (by rfl) ⟨52616, by rfl⟩ : syracuseStep 1122485 = 105233) (by norm_num)
theorem B1122509 : Blo 746329 1122509 := bbase (se 3 (by rfl) ⟨210470, by rfl⟩ : syracuseStep 1122509 = 420941) (by norm_num)
theorem B1122533 : Blo 746329 1122533 := bbase (se 4 (by rfl) ⟨105237, by rfl⟩ : syracuseStep 1122533 = 210475) (by norm_num)
theorem B1679597 : Blo 746329 1679597 := bbase (se 3 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 1679597 = 629849) (by norm_num)
theorem B2531573 : Blo 746329 2531573 := bbase (se 5 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 2531573 = 237335) (by norm_num)
theorem B1122557 : Blo 746329 1122557 := bbase (se 3 (by rfl) ⟨210479, by rfl⟩ : syracuseStep 1122557 = 420959) (by norm_num)
theorem B1122581 : Blo 746329 1122581 := bbase (se 6 (by rfl) ⟨26310, by rfl⟩ : syracuseStep 1122581 = 52621) (by norm_num)
theorem B1351973 : Blo 746329 1351973 := bbase (se 4 (by rfl) ⟨126747, by rfl⟩ : syracuseStep 1351973 = 253495) (by norm_num)
theorem B1122605 : Blo 746329 1122605 := bbase (se 3 (by rfl) ⟨210488, by rfl⟩ : syracuseStep 1122605 = 420977) (by norm_num)
theorem B1679669 : Blo 746329 1679669 := bbase (se 5 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 1679669 = 157469) (by norm_num)
theorem B1122629 : Blo 746329 1122629 := bbase (se 4 (by rfl) ⟨105246, by rfl⟩ : syracuseStep 1122629 = 210493) (by norm_num)
theorem B1122653 : Blo 746329 1122653 := bbase (se 3 (by rfl) ⟨210497, by rfl⟩ : syracuseStep 1122653 = 420995) (by norm_num)
theorem B958825 : Blo 746329 958825 := bbase (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) (by norm_num)
theorem B1352045 : Blo 746329 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B1122677 : Blo 746329 1122677 := bbase (se 5 (by rfl) ⟨52625, by rfl⟩ : syracuseStep 1122677 = 105251) (by norm_num)
theorem B1679741 : Blo 746329 1679741 := bbase (se 3 (by rfl) ⟨314951, by rfl⟩ : syracuseStep 1679741 = 629903) (by norm_num)
theorem B1122701 : Blo 746329 1122701 := bbase (se 3 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 1122701 = 421013) (by norm_num)
theorem B1122725 : Blo 746329 1122725 := bbase (se 4 (by rfl) ⟨105255, by rfl⟩ : syracuseStep 1122725 = 210511) (by norm_num)
theorem B1122749 : Blo 746329 1122749 := bbase (se 3 (by rfl) ⟨210515, by rfl⟩ : syracuseStep 1122749 = 421031) (by norm_num)
theorem B1679813 : Blo 746329 1679813 := bbase (se 4 (by rfl) ⟨157482, by rfl⟩ : syracuseStep 1679813 = 314965) (by norm_num)
theorem B1122773 : Blo 746329 1122773 := bbase (se 7 (by rfl) ⟨13157, by rfl⟩ : syracuseStep 1122773 = 26315) (by norm_num)
theorem B1122797 : Blo 746329 1122797 := bbase (se 3 (by rfl) ⟨210524, by rfl⟩ : syracuseStep 1122797 = 421049) (by norm_num)
theorem B1122821 : Blo 746329 1122821 := bbase (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) (by norm_num)
theorem B1155589 : Blo 746329 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B1679885 : Blo 746329 1679885 := bbase (se 3 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 1679885 = 629957) (by norm_num)
theorem B1122845 : Blo 746329 1122845 := bbase (se 3 (by rfl) ⟨210533, by rfl⟩ : syracuseStep 1122845 = 421067) (by norm_num)
theorem B1122869 : Blo 746329 1122869 := bbase (se 5 (by rfl) ⟨52634, by rfl⟩ : syracuseStep 1122869 = 105269) (by norm_num)
theorem B1122893 : Blo 746329 1122893 := bbase (se 3 (by rfl) ⟨210542, by rfl⟩ : syracuseStep 1122893 = 421085) (by norm_num)
theorem B1679957 : Blo 746329 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B2564693 : Blo 746329 2564693 := bbase (se 8 (by rfl) ⟨15027, by rfl⟩ : syracuseStep 2564693 = 30055) (by norm_num)
theorem B1122917 : Blo 746329 1122917 := bbase (se 4 (by rfl) ⟨105273, by rfl⟩ : syracuseStep 1122917 = 210547) (by norm_num)
theorem B1417837 : Blo 746329 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B1122941 : Blo 746329 1122941 := bbase (se 3 (by rfl) ⟨210551, by rfl⟩ : syracuseStep 1122941 = 421103) (by norm_num)
theorem B1122965 : Blo 746329 1122965 := bbase (se 6 (by rfl) ⟨26319, by rfl⟩ : syracuseStep 1122965 = 52639) (by norm_num)
theorem B1680029 : Blo 746329 1680029 := bbase (se 3 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 1680029 = 630011) (by norm_num)
theorem B2532005 : Blo 746329 2532005 := bbase (se 4 (by rfl) ⟨237375, by rfl⟩ : syracuseStep 2532005 = 474751) (by norm_num)
theorem B1122989 : Blo 746329 1122989 := bbase (se 3 (by rfl) ⟨210560, by rfl⟩ : syracuseStep 1122989 = 421121) (by norm_num)
theorem B1123013 : Blo 746329 1123013 := bbase (se 4 (by rfl) ⟨105282, by rfl⟩ : syracuseStep 1123013 = 210565) (by norm_num)
theorem B1123037 : Blo 746329 1123037 := bbase (se 3 (by rfl) ⟨210569, by rfl⟩ : syracuseStep 1123037 = 421139) (by norm_num)
theorem B1680101 : Blo 746329 1680101 := bbase (se 4 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 1680101 = 315019) (by norm_num)
theorem B1123061 : Blo 746329 1123061 := bbase (se 5 (by rfl) ⟨52643, by rfl⟩ : syracuseStep 1123061 = 105287) (by norm_num)
theorem B1417981 : Blo 746329 1417981 := bbase (se 3 (by rfl) ⟨265871, by rfl⟩ : syracuseStep 1417981 = 531743) (by norm_num)
theorem B1123085 : Blo 746329 1123085 := bbase (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) (by norm_num)
theorem B2564885 : Blo 746329 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B1123109 : Blo 746329 1123109 := bbase (se 4 (by rfl) ⟨105291, by rfl⟩ : syracuseStep 1123109 = 210583) (by norm_num)
theorem B1680173 : Blo 746329 1680173 := bbase (se 3 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 1680173 = 630065) (by norm_num)
theorem B5481269 : Blo 746329 5481269 := bbase (se 5 (by rfl) ⟨256934, by rfl⟩ : syracuseStep 5481269 = 513869) (by norm_num)
theorem B1123133 : Blo 746329 1123133 := bbase (se 3 (by rfl) ⟨210587, by rfl⟩ : syracuseStep 1123133 = 421175) (by norm_num)
theorem B1123157 : Blo 746329 1123157 := bbase (se 9 (by rfl) ⟨3290, by rfl⟩ : syracuseStep 1123157 = 6581) (by norm_num)
theorem B1123181 : Blo 746329 1123181 := bbase (se 3 (by rfl) ⟨210596, by rfl⟩ : syracuseStep 1123181 = 421193) (by norm_num)
theorem B1680245 : Blo 746329 1680245 := bbase (se 5 (by rfl) ⟨78761, by rfl⟩ : syracuseStep 1680245 = 157523) (by norm_num)
theorem B1123205 : Blo 746329 1123205 := bbase (se 4 (by rfl) ⟨105300, by rfl⟩ : syracuseStep 1123205 = 210601) (by norm_num)
theorem B1418141 : Blo 746329 1418141 := bbase (se 3 (by rfl) ⟨265901, by rfl⟩ : syracuseStep 1418141 = 531803) (by norm_num)
theorem B1123229 : Blo 746329 1123229 := bbase (se 3 (by rfl) ⟨210605, by rfl⟩ : syracuseStep 1123229 = 421211) (by norm_num)
theorem B1123253 : Blo 746329 1123253 := bbase (se 5 (by rfl) ⟨52652, by rfl⟩ : syracuseStep 1123253 = 105305) (by norm_num)
theorem B1680317 : Blo 746329 1680317 := bbase (se 3 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 1680317 = 630119) (by norm_num)
theorem B1123277 : Blo 746329 1123277 := bbase (se 3 (by rfl) ⟨210614, by rfl⟩ : syracuseStep 1123277 = 421229) (by norm_num)
theorem B1123301 : Blo 746329 1123301 := bbase (se 4 (by rfl) ⟨105309, by rfl⟩ : syracuseStep 1123301 = 210619) (by norm_num)
theorem B1123325 : Blo 746329 1123325 := bbase (se 3 (by rfl) ⟨210623, by rfl⟩ : syracuseStep 1123325 = 421247) (by norm_num)
theorem B1680389 : Blo 746329 1680389 := bbase (se 4 (by rfl) ⟨157536, by rfl⟩ : syracuseStep 1680389 = 315073) (by norm_num)
theorem B1123349 : Blo 746329 1123349 := bbase (se 6 (by rfl) ⟨26328, by rfl⟩ : syracuseStep 1123349 = 52657) (by norm_num)
theorem B1418285 : Blo 746329 1418285 := bbase (se 3 (by rfl) ⟨265928, by rfl⟩ : syracuseStep 1418285 = 531857) (by norm_num)
theorem B1123373 : Blo 746329 1123373 := bbase (se 3 (by rfl) ⟨210632, by rfl⟩ : syracuseStep 1123373 = 421265) (by norm_num)
theorem B1123397 : Blo 746329 1123397 := bbase (se 4 (by rfl) ⟨105318, by rfl⟩ : syracuseStep 1123397 = 210637) (by norm_num)
theorem B1680461 : Blo 746329 1680461 := bbase (se 3 (by rfl) ⟨315086, by rfl⟩ : syracuseStep 1680461 = 630173) (by norm_num)
theorem B1123421 : Blo 746329 1123421 := bbase (se 3 (by rfl) ⟨210641, by rfl⟩ : syracuseStep 1123421 = 421283) (by norm_num)
theorem B959585 : Blo 746329 959585 := bbase (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) (by norm_num)
theorem B1123445 : Blo 746329 1123445 := bbase (se 5 (by rfl) ⟨52661, by rfl⟩ : syracuseStep 1123445 = 105323) (by norm_num)
theorem B1123469 : Blo 746329 1123469 := bbase (se 3 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 1123469 = 421301) (by norm_num)
theorem B1680533 : Blo 746329 1680533 := bbase (se 6 (by rfl) ⟨39387, by rfl⟩ : syracuseStep 1680533 = 78775) (by norm_num)
theorem B2401429 : Blo 746329 2401429 := bbase (se 6 (by rfl) ⟨56283, by rfl⟩ : syracuseStep 2401429 = 112567) (by norm_num)
theorem B1123493 : Blo 746329 1123493 := bbase (se 4 (by rfl) ⟨105327, by rfl⟩ : syracuseStep 1123493 = 210655) (by norm_num)
theorem B3515557 : Blo 746329 3515557 := bbase (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) (by norm_num)
theorem B1123517 : Blo 746329 1123517 := bbase (se 3 (by rfl) ⟨210659, by rfl⟩ : syracuseStep 1123517 = 421319) (by norm_num)
theorem B1123541 : Blo 746329 1123541 := bbase (se 7 (by rfl) ⟨13166, by rfl⟩ : syracuseStep 1123541 = 26333) (by norm_num)
theorem B1680605 : Blo 746329 1680605 := bbase (se 3 (by rfl) ⟨315113, by rfl⟩ : syracuseStep 1680605 = 630227) (by norm_num)
theorem B1123565 : Blo 746329 1123565 := bbase (se 3 (by rfl) ⟨210668, by rfl⟩ : syracuseStep 1123565 = 421337) (by norm_num)
theorem B1123589 : Blo 746329 1123589 := bbase (se 4 (by rfl) ⟨105336, by rfl⟩ : syracuseStep 1123589 = 210673) (by norm_num)
theorem B1123613 : Blo 746329 1123613 := bbase (se 3 (by rfl) ⟨210677, by rfl⟩ : syracuseStep 1123613 = 421355) (by norm_num)
theorem B1680677 : Blo 746329 1680677 := bbase (se 4 (by rfl) ⟨157563, by rfl⟩ : syracuseStep 1680677 = 315127) (by norm_num)
theorem B1123637 : Blo 746329 1123637 := bbase (se 5 (by rfl) ⟨52670, by rfl⟩ : syracuseStep 1123637 = 105341) (by norm_num)
theorem B1418573 : Blo 746329 1418573 := bbase (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) (by norm_num)
theorem B1123661 : Blo 746329 1123661 := bbase (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) (by norm_num)
theorem B1123685 : Blo 746329 1123685 := bbase (se 4 (by rfl) ⟨105345, by rfl⟩ : syracuseStep 1123685 = 210691) (by norm_num)
theorem B1680749 : Blo 746329 1680749 := bbase (se 3 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 1680749 = 630281) (by norm_num)
theorem B1123709 : Blo 746329 1123709 := bbase (se 3 (by rfl) ⟨210695, by rfl⟩ : syracuseStep 1123709 = 421391) (by norm_num)
theorem B1123733 : Blo 746329 1123733 := bbase (se 6 (by rfl) ⟨26337, by rfl⟩ : syracuseStep 1123733 = 52675) (by norm_num)
theorem B1123757 : Blo 746329 1123757 := bbase (se 3 (by rfl) ⟨210704, by rfl⟩ : syracuseStep 1123757 = 421409) (by norm_num)
theorem B1680821 : Blo 746329 1680821 := bbase (se 5 (by rfl) ⟨78788, by rfl⟩ : syracuseStep 1680821 = 157577) (by norm_num)
theorem B1123781 : Blo 746329 1123781 := bbase (se 4 (by rfl) ⟨105354, by rfl⟩ : syracuseStep 1123781 = 210709) (by norm_num)
theorem B4793813 : Blo 746329 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B1123805 : Blo 746329 1123805 := bbase (se 3 (by rfl) ⟨210713, by rfl⟩ : syracuseStep 1123805 = 421427) (by norm_num)
theorem B1418725 : Blo 746329 1418725 := bbase (se 4 (by rfl) ⟨133005, by rfl⟩ : syracuseStep 1418725 = 266011) (by norm_num)
theorem B1123829 : Blo 746329 1123829 := bbase (se 5 (by rfl) ⟨52679, by rfl⟩ : syracuseStep 1123829 = 105359) (by norm_num)
theorem B1680893 : Blo 746329 1680893 := bbase (se 3 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 1680893 = 630335) (by norm_num)
theorem B2336261 : Blo 746329 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1123853 : Blo 746329 1123853 := bbase (se 3 (by rfl) ⟨210722, by rfl⟩ : syracuseStep 1123853 = 421445) (by norm_num)
theorem B1123877 : Blo 746329 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B1123901 : Blo 746329 1123901 := bbase (se 3 (by rfl) ⟨210731, by rfl⟩ : syracuseStep 1123901 = 421463) (by norm_num)
theorem B1680965 : Blo 746329 1680965 := bbase (se 4 (by rfl) ⟨157590, by rfl⟩ : syracuseStep 1680965 = 315181) (by norm_num)
theorem B1517125 : Blo 746329 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B1123925 : Blo 746329 1123925 := bbase (se 8 (by rfl) ⟨6585, by rfl⟩ : syracuseStep 1123925 = 13171) (by norm_num)
theorem B1123949 : Blo 746329 1123949 := bbase (se 3 (by rfl) ⟨210740, by rfl⟩ : syracuseStep 1123949 = 421481) (by norm_num)
theorem B1123973 : Blo 746329 1123973 := bbase (se 4 (by rfl) ⟨105372, by rfl⟩ : syracuseStep 1123973 = 210745) (by norm_num)
theorem B1681037 : Blo 746329 1681037 := bbase (se 3 (by rfl) ⟨315194, by rfl⟩ : syracuseStep 1681037 = 630389) (by norm_num)
theorem B1123997 : Blo 746329 1123997 := bbase (se 3 (by rfl) ⟨210749, by rfl⟩ : syracuseStep 1123997 = 421499) (by norm_num)
theorem B1124021 : Blo 746329 1124021 := bbase (se 5 (by rfl) ⟨52688, by rfl⟩ : syracuseStep 1124021 = 105377) (by norm_num)
theorem B1124045 : Blo 746329 1124045 := bbase (se 3 (by rfl) ⟨210758, by rfl⟩ : syracuseStep 1124045 = 421517) (by norm_num)
theorem B1681109 : Blo 746329 1681109 := bbase (se 7 (by rfl) ⟨19700, by rfl⟩ : syracuseStep 1681109 = 39401) (by norm_num)
theorem B3155669 : Blo 746329 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B1124069 : Blo 746329 1124069 := bbase (se 4 (by rfl) ⟨105381, by rfl⟩ : syracuseStep 1124069 = 210763) (by norm_num)
theorem B1124093 : Blo 746329 1124093 := bbase (se 3 (by rfl) ⟨210767, by rfl⟩ : syracuseStep 1124093 = 421535) (by norm_num)
theorem B3778325 : Blo 746329 3778325 := bbase (se 6 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 3778325 = 177109) (by norm_num)
theorem B1419029 : Blo 746329 1419029 := bbase (se 6 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 1419029 = 66517) (by norm_num)
theorem B2696981 : Blo 746329 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B1124117 : Blo 746329 1124117 := bbase (se 6 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 1124117 = 52693) (by norm_num)
theorem B1681181 : Blo 746329 1681181 := bbase (se 3 (by rfl) ⟨315221, by rfl⟩ : syracuseStep 1681181 = 630443) (by norm_num)
theorem B1124141 : Blo 746329 1124141 := bbase (se 3 (by rfl) ⟨210776, by rfl⟩ : syracuseStep 1124141 = 421553) (by norm_num)
theorem B1124165 : Blo 746329 1124165 := bbase (se 4 (by rfl) ⟨105390, by rfl⟩ : syracuseStep 1124165 = 210781) (by norm_num)
theorem B1124189 : Blo 746329 1124189 := bbase (se 3 (by rfl) ⟨210785, by rfl⟩ : syracuseStep 1124189 = 421571) (by norm_num)
theorem B1681253 : Blo 746329 1681253 := bbase (se 4 (by rfl) ⟨157617, by rfl⟩ : syracuseStep 1681253 = 315235) (by norm_num)
theorem B1124213 : Blo 746329 1124213 := bbase (se 5 (by rfl) ⟨52697, by rfl⟩ : syracuseStep 1124213 = 105395) (by norm_num)
theorem B1124237 : Blo 746329 1124237 := bbase (se 3 (by rfl) ⟨210794, by rfl⟩ : syracuseStep 1124237 = 421589) (by norm_num)
theorem B1124261 : Blo 746329 1124261 := bbase (se 4 (by rfl) ⟨105399, by rfl⟩ : syracuseStep 1124261 = 210799) (by norm_num)
theorem B1681325 : Blo 746329 1681325 := bbase (se 3 (by rfl) ⟨315248, by rfl⟩ : syracuseStep 1681325 = 630497) (by norm_num)
theorem B1124285 : Blo 746329 1124285 := bbase (se 3 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 1124285 = 421607) (by norm_num)
theorem B1124309 : Blo 746329 1124309 := bbase (se 7 (by rfl) ⟨13175, by rfl⟩ : syracuseStep 1124309 = 26351) (by norm_num)
theorem B1124333 : Blo 746329 1124333 := bbase (se 3 (by rfl) ⟨210812, by rfl⟩ : syracuseStep 1124333 = 421625) (by norm_num)
theorem B1681397 : Blo 746329 1681397 := bbase (se 5 (by rfl) ⟨78815, by rfl⟩ : syracuseStep 1681397 = 157631) (by norm_num)
theorem B1124357 : Blo 746329 1124357 := bbase (se 4 (by rfl) ⟨105408, by rfl⟩ : syracuseStep 1124357 = 210817) (by norm_num)
theorem B1124381 : Blo 746329 1124381 := bbase (se 3 (by rfl) ⟨210821, by rfl⟩ : syracuseStep 1124381 = 421643) (by norm_num)
theorem B1124405 : Blo 746329 1124405 := bbase (se 5 (by rfl) ⟨52706, by rfl⟩ : syracuseStep 1124405 = 105413) (by norm_num)
theorem B1681469 : Blo 746329 1681469 := bbase (se 3 (by rfl) ⟨315275, by rfl⟩ : syracuseStep 1681469 = 630551) (by norm_num)
theorem B1124429 : Blo 746329 1124429 := bbase (se 3 (by rfl) ⟨210830, by rfl⟩ : syracuseStep 1124429 = 421661) (by norm_num)
theorem B1124453 : Blo 746329 1124453 := bbase (se 4 (by rfl) ⟨105417, by rfl⟩ : syracuseStep 1124453 = 210835) (by norm_num)
theorem B1124477 : Blo 746329 1124477 := bbase (se 3 (by rfl) ⟨210839, by rfl⟩ : syracuseStep 1124477 = 421679) (by norm_num)
theorem B1681541 : Blo 746329 1681541 := bbase (se 4 (by rfl) ⟨157644, by rfl⟩ : syracuseStep 1681541 = 315289) (by norm_num)
theorem B1124501 : Blo 746329 1124501 := bbase (se 6 (by rfl) ⟨26355, by rfl⟩ : syracuseStep 1124501 = 52711) (by norm_num)
theorem B1517725 : Blo 746329 1517725 := bbase (se 3 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 1517725 = 569147) (by norm_num)
theorem B1124525 : Blo 746329 1124525 := bbase (se 3 (by rfl) ⟨210848, by rfl⟩ : syracuseStep 1124525 = 421697) (by norm_num)
theorem B1124549 : Blo 746329 1124549 := bbase (se 4 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 1124549 = 210853) (by norm_num)
theorem B1681613 : Blo 746329 1681613 := bbase (se 3 (by rfl) ⟨315302, by rfl⟩ : syracuseStep 1681613 = 630605) (by norm_num)
theorem B1124573 : Blo 746329 1124573 := bbase (se 3 (by rfl) ⟨210857, by rfl⟩ : syracuseStep 1124573 = 421715) (by norm_num)
theorem B1124597 : Blo 746329 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B1124621 : Blo 746329 1124621 := bbase (se 3 (by rfl) ⟨210866, by rfl⟩ : syracuseStep 1124621 = 421733) (by norm_num)
theorem B1681685 : Blo 746329 1681685 := bbase (se 6 (by rfl) ⟨39414, by rfl⟩ : syracuseStep 1681685 = 78829) (by norm_num)
theorem B1124645 : Blo 746329 1124645 := bbase (se 4 (by rfl) ⟨105435, by rfl⟩ : syracuseStep 1124645 = 210871) (by norm_num)
theorem B1124669 : Blo 746329 1124669 := bbase (se 3 (by rfl) ⟨210875, by rfl⟩ : syracuseStep 1124669 = 421751) (by norm_num)
theorem B1124693 : Blo 746329 1124693 := bbase (se 10 (by rfl) ⟨1647, by rfl⟩ : syracuseStep 1124693 = 3295) (by norm_num)
theorem B1681757 : Blo 746329 1681757 := bbase (se 3 (by rfl) ⟨315329, by rfl⟩ : syracuseStep 1681757 = 630659) (by norm_num)
theorem B1124717 : Blo 746329 1124717 := bbase (se 3 (by rfl) ⟨210884, by rfl⟩ : syracuseStep 1124717 = 421769) (by norm_num)
theorem B3189125 : Blo 746329 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B1124741 : Blo 746329 1124741 := bbase (se 4 (by rfl) ⟨105444, by rfl⟩ : syracuseStep 1124741 = 210889) (by norm_num)
theorem B1124765 : Blo 746329 1124765 := bbase (se 3 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 1124765 = 421787) (by norm_num)
theorem B1681829 : Blo 746329 1681829 := bbase (se 4 (by rfl) ⟨157671, by rfl⟩ : syracuseStep 1681829 = 315343) (by norm_num)
theorem B1124789 : Blo 746329 1124789 := bbase (se 5 (by rfl) ⟨52724, by rfl⟩ : syracuseStep 1124789 = 105449) (by norm_num)
theorem B1124813 : Blo 746329 1124813 := bbase (se 3 (by rfl) ⟨210902, by rfl⟩ : syracuseStep 1124813 = 421805) (by norm_num)
theorem B1124837 : Blo 746329 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B1681901 : Blo 746329 1681901 := bbase (se 3 (by rfl) ⟨315356, by rfl⟩ : syracuseStep 1681901 = 630713) (by norm_num)
theorem B1124861 : Blo 746329 1124861 := bbase (se 3 (by rfl) ⟨210911, by rfl⟩ : syracuseStep 1124861 = 421823) (by norm_num)
theorem B1419781 : Blo 746329 1419781 := bbase (se 4 (by rfl) ⟨133104, by rfl⟩ : syracuseStep 1419781 = 266209) (by norm_num)
theorem B1124885 : Blo 746329 1124885 := bbase (se 6 (by rfl) ⟨26364, by rfl⟩ : syracuseStep 1124885 = 52729) (by norm_num)
theorem B797213 : Blo 746329 797213 := bbase (se 3 (by rfl) ⟨149477, by rfl⟩ : syracuseStep 797213 = 298955) (by norm_num)
theorem B1124909 : Blo 746329 1124909 := bbase (se 3 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 1124909 = 421841) (by norm_num)
theorem B1681973 : Blo 746329 1681973 := bbase (se 5 (by rfl) ⟨78842, by rfl⟩ : syracuseStep 1681973 = 157685) (by norm_num)
theorem B1124933 : Blo 746329 1124933 := bbase (se 4 (by rfl) ⟨105462, by rfl⟩ : syracuseStep 1124933 = 210925) (by norm_num)
theorem B1124957 : Blo 746329 1124957 := bbase (se 3 (by rfl) ⟨210929, by rfl⟩ : syracuseStep 1124957 = 421859) (by norm_num)
theorem B3189365 : Blo 746329 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B1124981 : Blo 746329 1124981 := bbase (se 5 (by rfl) ⟨52733, by rfl⟩ : syracuseStep 1124981 = 105467) (by norm_num)
theorem B1682045 : Blo 746329 1682045 := bbase (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) (by norm_num)
theorem B1125005 : Blo 746329 1125005 := bbase (se 3 (by rfl) ⟨210938, by rfl⟩ : syracuseStep 1125005 = 421877) (by norm_num)
theorem B1419925 : Blo 746329 1419925 := bbase (se 6 (by rfl) ⟨33279, by rfl⟩ : syracuseStep 1419925 = 66559) (by norm_num)
theorem B1125029 : Blo 746329 1125029 := bbase (se 4 (by rfl) ⟨105471, by rfl⟩ : syracuseStep 1125029 = 210943) (by norm_num)
theorem B1125053 : Blo 746329 1125053 := bbase (se 3 (by rfl) ⟨210947, by rfl⟩ : syracuseStep 1125053 = 421895) (by norm_num)
theorem B1682117 : Blo 746329 1682117 := bbase (se 4 (by rfl) ⟨157698, by rfl⟩ : syracuseStep 1682117 = 315397) (by norm_num)
theorem B1125077 : Blo 746329 1125077 := bbase (se 7 (by rfl) ⟨13184, by rfl⟩ : syracuseStep 1125077 = 26369) (by norm_num)
theorem B797401 : Blo 746329 797401 := bbase (se 2 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 797401 = 598051) (by norm_num)
theorem B1125101 : Blo 746329 1125101 := bbase (se 3 (by rfl) ⟨210956, by rfl⟩ : syracuseStep 1125101 = 421913) (by norm_num)
theorem B1125125 : Blo 746329 1125125 := bbase (se 4 (by rfl) ⟨105480, by rfl⟩ : syracuseStep 1125125 = 210961) (by norm_num)
theorem B1682189 : Blo 746329 1682189 := bbase (se 3 (by rfl) ⟨315410, by rfl⟩ : syracuseStep 1682189 = 630821) (by norm_num)
theorem B1125149 : Blo 746329 1125149 := bbase (se 3 (by rfl) ⟨210965, by rfl⟩ : syracuseStep 1125149 = 421931) (by norm_num)
theorem B1420085 : Blo 746329 1420085 := bbase (se 5 (by rfl) ⟨66566, by rfl⟩ : syracuseStep 1420085 = 133133) (by norm_num)
theorem B1125173 : Blo 746329 1125173 := bbase (se 5 (by rfl) ⟨52742, by rfl⟩ : syracuseStep 1125173 = 105485) (by norm_num)
theorem B1125197 : Blo 746329 1125197 := bbase (se 3 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 1125197 = 421949) (by norm_num)
theorem B1682261 : Blo 746329 1682261 := bbase (se 9 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 1682261 = 9857) (by norm_num)
theorem B1125221 : Blo 746329 1125221 := bbase (se 4 (by rfl) ⟨105489, by rfl⟩ : syracuseStep 1125221 = 210979) (by norm_num)
theorem B1125245 : Blo 746329 1125245 := bbase (se 3 (by rfl) ⟨210983, by rfl⟩ : syracuseStep 1125245 = 421967) (by norm_num)
theorem B1125269 : Blo 746329 1125269 := bbase (se 6 (by rfl) ⟨26373, by rfl⟩ : syracuseStep 1125269 = 52747) (by norm_num)
theorem B1682333 : Blo 746329 1682333 := bbase (se 3 (by rfl) ⟨315437, by rfl⟩ : syracuseStep 1682333 = 630875) (by norm_num)
theorem B1125293 : Blo 746329 1125293 := bbase (se 3 (by rfl) ⟨210992, by rfl⟩ : syracuseStep 1125293 = 421985) (by norm_num)
theorem B1420229 : Blo 746329 1420229 := bbase (se 4 (by rfl) ⟨133146, by rfl⟩ : syracuseStep 1420229 = 266293) (by norm_num)
theorem B1125317 : Blo 746329 1125317 := bbase (se 4 (by rfl) ⟨105498, by rfl⟩ : syracuseStep 1125317 = 210997) (by norm_num)
theorem B1125341 : Blo 746329 1125341 := bbase (se 3 (by rfl) ⟨211001, by rfl⟩ : syracuseStep 1125341 = 422003) (by norm_num)
theorem B1682405 : Blo 746329 1682405 := bbase (se 4 (by rfl) ⟨157725, by rfl⟩ : syracuseStep 1682405 = 315451) (by norm_num)
theorem B1125365 : Blo 746329 1125365 := bbase (se 5 (by rfl) ⟨52751, by rfl⟩ : syracuseStep 1125365 = 105503) (by norm_num)
theorem B1125389 : Blo 746329 1125389 := bbase (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) (by norm_num)
theorem B14363669 : Blo 746329 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B3779621 : Blo 746329 3779621 := bbase (se 4 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 3779621 = 708679) (by norm_num)
theorem B1125413 : Blo 746329 1125413 := bbase (se 4 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 1125413 = 211015) (by norm_num)
theorem B1682477 : Blo 746329 1682477 := bbase (se 3 (by rfl) ⟨315464, by rfl⟩ : syracuseStep 1682477 = 630929) (by norm_num)
theorem B1125437 : Blo 746329 1125437 := bbase (se 3 (by rfl) ⟨211019, by rfl⟩ : syracuseStep 1125437 = 422039) (by norm_num)
theorem B1125461 : Blo 746329 1125461 := bbase (se 8 (by rfl) ⟨6594, by rfl⟩ : syracuseStep 1125461 = 13189) (by norm_num)
theorem B1125485 : Blo 746329 1125485 := bbase (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) (by norm_num)
theorem B1682549 : Blo 746329 1682549 := bbase (se 5 (by rfl) ⟨78869, by rfl⟩ : syracuseStep 1682549 = 157739) (by norm_num)
theorem B1682621 : Blo 746329 1682621 := bbase (se 3 (by rfl) ⟨315491, by rfl⟩ : syracuseStep 1682621 = 630983) (by norm_num)
theorem B1420517 : Blo 746329 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B1682693 : Blo 746329 1682693 := bbase (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) (by norm_num)
theorem B1518869 : Blo 746329 1518869 := bbase (se 6 (by rfl) ⟨35598, by rfl⟩ : syracuseStep 1518869 = 71197) (by norm_num)
theorem B1682765 : Blo 746329 1682765 := bbase (se 3 (by rfl) ⟨315518, by rfl⟩ : syracuseStep 1682765 = 631037) (by norm_num)
theorem B1420669 : Blo 746329 1420669 := bbase (se 3 (by rfl) ⟨266375, by rfl⟩ : syracuseStep 1420669 = 532751) (by norm_num)
theorem B1682837 : Blo 746329 1682837 := bbase (se 6 (by rfl) ⟨39441, by rfl⟩ : syracuseStep 1682837 = 78883) (by norm_num)
theorem B2436533 : Blo 746329 2436533 := bbase (se 5 (by rfl) ⟨114212, by rfl⟩ : syracuseStep 2436533 = 228425) (by norm_num)
theorem B5385685 : Blo 746329 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B14396885 : Blo 746329 14396885 := bbase (se 7 (by rfl) ⟨168713, by rfl⟩ : syracuseStep 14396885 = 337427) (by norm_num)
theorem B1682909 : Blo 746329 1682909 := bbase (se 3 (by rfl) ⟨315545, by rfl⟩ : syracuseStep 1682909 = 631091) (by norm_num)
theorem B798221 : Blo 746329 798221 := bbase (se 3 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 798221 = 299333) (by norm_num)
theorem B1682981 : Blo 746329 1682981 := bbase (se 4 (by rfl) ⟨157779, by rfl⟩ : syracuseStep 1682981 = 315559) (by norm_num)
theorem B1683053 : Blo 746329 1683053 := bbase (se 3 (by rfl) ⟨315572, by rfl⟩ : syracuseStep 1683053 = 631145) (by norm_num)
theorem B896653 : Blo 746329 896653 := bbase (se 3 (by rfl) ⟨168122, by rfl⟩ : syracuseStep 896653 = 336245) (by norm_num)
theorem B1420973 : Blo 746329 1420973 := bbase (se 3 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 1420973 = 532865) (by norm_num)
theorem B1683125 : Blo 746329 1683125 := bbase (se 5 (by rfl) ⟨78896, by rfl⟩ : syracuseStep 1683125 = 157793) (by norm_num)
theorem B5680853 : Blo 746329 5680853 := bbase (se 7 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 5680853 = 133145) (by norm_num)
theorem B1683197 : Blo 746329 1683197 := bbase (se 3 (by rfl) ⟨315599, by rfl⟩ : syracuseStep 1683197 = 631199) (by norm_num)
theorem B1683269 : Blo 746329 1683269 := bbase (se 4 (by rfl) ⟨157806, by rfl⟩ : syracuseStep 1683269 = 315613) (by norm_num)
theorem B962437 : Blo 746329 962437 := bbase (se 4 (by rfl) ⟨90228, by rfl⟩ : syracuseStep 962437 = 180457) (by norm_num)
theorem B1683341 : Blo 746329 1683341 := bbase (se 3 (by rfl) ⟨315626, by rfl⟩ : syracuseStep 1683341 = 631253) (by norm_num)
theorem B798665 : Blo 746329 798665 := bbase (se 2 (by rfl) ⟨299499, by rfl⟩ : syracuseStep 798665 = 598999) (by norm_num)
theorem B1683413 : Blo 746329 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B1683485 : Blo 746329 1683485 := bbase (se 3 (by rfl) ⟨315653, by rfl⟩ : syracuseStep 1683485 = 631307) (by norm_num)
theorem B3420229 : Blo 746329 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B1683557 : Blo 746329 1683557 := bbase (se 4 (by rfl) ⟨157833, by rfl⟩ : syracuseStep 1683557 = 315667) (by norm_num)
theorem B1683629 : Blo 746329 1683629 := bbase (se 3 (by rfl) ⟨315680, by rfl⟩ : syracuseStep 1683629 = 631361) (by norm_num)
theorem B798913 : Blo 746329 798913 := bbase (se 2 (by rfl) ⟨299592, by rfl⟩ : syracuseStep 798913 = 599185) (by norm_num)
theorem B2699477 : Blo 746329 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1683701 : Blo 746329 1683701 := bbase (se 5 (by rfl) ⟨78923, by rfl⟩ : syracuseStep 1683701 = 157847) (by norm_num)
theorem B3780917 : Blo 746329 3780917 := bbase (se 5 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 3780917 = 354461) (by norm_num)
theorem B1683773 : Blo 746329 1683773 := bbase (se 3 (by rfl) ⟨315707, by rfl⟩ : syracuseStep 1683773 = 631415) (by norm_num)
theorem B897365 : Blo 746329 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1683845 : Blo 746329 1683845 := bbase (se 4 (by rfl) ⟨157860, by rfl⟩ : syracuseStep 1683845 = 315721) (by norm_num)
theorem B4272533 : Blo 746329 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B1421725 : Blo 746329 1421725 := bbase (se 3 (by rfl) ⟨266573, by rfl⟩ : syracuseStep 1421725 = 533147) (by norm_num)
theorem B1683917 : Blo 746329 1683917 := bbase (se 3 (by rfl) ⟨315734, by rfl⟩ : syracuseStep 1683917 = 631469) (by norm_num)
theorem B1683989 : Blo 746329 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B864805 : Blo 746329 864805 := bbase (se 4 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 864805 = 162151) (by norm_num)
theorem B1421869 : Blo 746329 1421869 := bbase (se 3 (by rfl) ⟨266600, by rfl⟩ : syracuseStep 1421869 = 533201) (by norm_num)
theorem B1684061 : Blo 746329 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B799345 : Blo 746329 799345 := bbase (se 2 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 799345 = 599509) (by norm_num)
theorem B897701 : Blo 746329 897701 := bbase (se 4 (by rfl) ⟨84159, by rfl⟩ : syracuseStep 897701 = 168319) (by norm_num)
theorem B1684133 : Blo 746329 1684133 := bbase (se 4 (by rfl) ⟨157887, by rfl⟩ : syracuseStep 1684133 = 315775) (by norm_num)
theorem B799417 : Blo 746329 799417 := bbase (se 2 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 799417 = 599563) (by norm_num)
theorem B1422029 : Blo 746329 1422029 := bbase (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) (by norm_num)
theorem B1684205 : Blo 746329 1684205 := bbase (se 3 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 1684205 = 631577) (by norm_num)
theorem B2700053 : Blo 746329 2700053 := bbase (se 6 (by rfl) ⟨63282, by rfl⟩ : syracuseStep 2700053 = 126565) (by norm_num)
theorem B897817 : Blo 746329 897817 := bbase (se 2 (by rfl) ⟨336681, by rfl⟩ : syracuseStep 897817 = 673363) (by norm_num)
theorem B897841 : Blo 746329 897841 := bbase (se 2 (by rfl) ⟨336690, by rfl⟩ : syracuseStep 897841 = 673381) (by norm_num)
theorem B1684277 : Blo 746329 1684277 := bbase (se 5 (by rfl) ⟨78950, by rfl⟩ : syracuseStep 1684277 = 157901) (by norm_num)
theorem B1422173 : Blo 746329 1422173 := bbase (se 3 (by rfl) ⟨266657, by rfl⟩ : syracuseStep 1422173 = 533315) (by norm_num)
theorem B3191653 : Blo 746329 3191653 := bbase (se 4 (by rfl) ⟨299217, by rfl⟩ : syracuseStep 3191653 = 598435) (by norm_num)
theorem B1618813 : Blo 746329 1618813 := bbase (se 3 (by rfl) ⟨303527, by rfl⟩ : syracuseStep 1618813 = 607055) (by norm_num)
theorem B1684349 : Blo 746329 1684349 := bbase (se 3 (by rfl) ⟨315815, by rfl⟩ : syracuseStep 1684349 = 631631) (by norm_num)
theorem B1684421 : Blo 746329 1684421 := bbase (se 4 (by rfl) ⟨157914, by rfl⟩ : syracuseStep 1684421 = 315829) (by norm_num)
theorem B1684493 : Blo 746329 1684493 := bbase (se 3 (by rfl) ⟨315842, by rfl⟩ : syracuseStep 1684493 = 631685) (by norm_num)
theorem B799789 : Blo 746329 799789 := bbase (se 3 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 799789 = 299921) (by norm_num)
theorem B1684565 : Blo 746329 1684565 := bbase (se 8 (by rfl) ⟨9870, by rfl⟩ : syracuseStep 1684565 = 19741) (by norm_num)
theorem B1422461 : Blo 746329 1422461 := bbase (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) (by norm_num)
theorem B1684637 : Blo 746329 1684637 := bbase (se 3 (by rfl) ⟨315869, by rfl⟩ : syracuseStep 1684637 = 631739) (by norm_num)
theorem B2700485 : Blo 746329 2700485 := bbase (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) (by norm_num)
theorem B1684709 : Blo 746329 1684709 := bbase (se 4 (by rfl) ⟨157941, by rfl⟩ : syracuseStep 1684709 = 315883) (by norm_num)
theorem B1422613 : Blo 746329 1422613 := bbase (se 6 (by rfl) ⟨33342, by rfl⟩ : syracuseStep 1422613 = 66685) (by norm_num)
theorem B1684781 : Blo 746329 1684781 := bbase (se 3 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 1684781 = 631793) (by norm_num)
theorem B1684853 : Blo 746329 1684853 := bbase (se 5 (by rfl) ⟨78977, by rfl⟩ : syracuseStep 1684853 = 157955) (by norm_num)
theorem B800165 : Blo 746329 800165 := bbase (se 4 (by rfl) ⟨75015, by rfl⟩ : syracuseStep 800165 = 150031) (by norm_num)
theorem B1684925 : Blo 746329 1684925 := bbase (se 3 (by rfl) ⟨315923, by rfl⟩ : syracuseStep 1684925 = 631847) (by norm_num)
theorem B898537 : Blo 746329 898537 := bbase (se 2 (by rfl) ⟨336951, by rfl⟩ : syracuseStep 898537 = 673903) (by norm_num)
theorem B800237 : Blo 746329 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B1684997 : Blo 746329 1684997 := bbase (se 4 (by rfl) ⟨157968, by rfl⟩ : syracuseStep 1684997 = 315937) (by norm_num)
theorem B3782213 : Blo 746329 3782213 := bbase (se 4 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 3782213 = 709165) (by norm_num)
theorem B1422917 : Blo 746329 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B898633 : Blo 746329 898633 := bbase (se 2 (by rfl) ⟨336987, by rfl⟩ : syracuseStep 898633 = 673975) (by norm_num)
theorem B1685069 : Blo 746329 1685069 := bbase (se 3 (by rfl) ⟨315950, by rfl⟩ : syracuseStep 1685069 = 631901) (by norm_num)
theorem B4044437 : Blo 746329 4044437 := bbase (se 6 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 4044437 = 189583) (by norm_num)
theorem B1685141 : Blo 746329 1685141 := bbase (se 6 (by rfl) ⟨39495, by rfl⟩ : syracuseStep 1685141 = 78991) (by norm_num)
theorem B800425 : Blo 746329 800425 := bbase (se 2 (by rfl) ⟨300159, by rfl⟩ : syracuseStep 800425 = 600319) (by norm_num)
theorem B1685213 : Blo 746329 1685213 := bbase (se 3 (by rfl) ⟨315977, by rfl⟩ : syracuseStep 1685213 = 631955) (by norm_num)
theorem B3847925 : Blo 746329 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B1062677 : Blo 746329 1062677 := bbase (se 6 (by rfl) ⟨24906, by rfl⟩ : syracuseStep 1062677 = 49813) (by norm_num)
theorem B1685285 : Blo 746329 1685285 := bbase (se 4 (by rfl) ⟨157995, by rfl⟩ : syracuseStep 1685285 = 315991) (by norm_num)
theorem B800609 : Blo 746329 800609 := bbase (se 2 (by rfl) ⟨300228, by rfl⟩ : syracuseStep 800609 = 600457) (by norm_num)
theorem B1062757 : Blo 746329 1062757 := bbase (se 4 (by rfl) ⟨99633, by rfl⟩ : syracuseStep 1062757 = 199267) (by norm_num)
theorem B1685357 : Blo 746329 1685357 := bbase (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) (by norm_num)
theorem B1685429 : Blo 746329 1685429 := bbase (se 5 (by rfl) ⟨79004, by rfl⟩ : syracuseStep 1685429 = 158009) (by norm_num)
theorem B1062877 : Blo 746329 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B1259509 : Blo 746329 1259509 := bbase (se 5 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 1259509 = 118079) (by norm_num)
theorem B1685501 : Blo 746329 1685501 := bbase (se 3 (by rfl) ⟨316031, by rfl⟩ : syracuseStep 1685501 = 632063) (by norm_num)
theorem B11548693 : Blo 746329 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B1062973 : Blo 746329 1062973 := bbase (se 3 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 1062973 = 398615) (by norm_num)
theorem B1685573 : Blo 746329 1685573 := bbase (se 4 (by rfl) ⟨158022, by rfl⟩ : syracuseStep 1685573 = 316045) (by norm_num)
theorem B1259597 : Blo 746329 1259597 := bbase (se 3 (by rfl) ⟨236174, by rfl⟩ : syracuseStep 1259597 = 472349) (by norm_num)
theorem B2275445 : Blo 746329 2275445 := bbase (se 5 (by rfl) ⟨106661, by rfl⟩ : syracuseStep 2275445 = 213323) (by norm_num)
theorem B1685645 : Blo 746329 1685645 := bbase (se 3 (by rfl) ⟨316058, by rfl⟩ : syracuseStep 1685645 = 632117) (by norm_num)
theorem B1259725 : Blo 746329 1259725 := bbase (se 3 (by rfl) ⟨236198, by rfl⟩ : syracuseStep 1259725 = 472397) (by norm_num)
theorem B1685717 : Blo 746329 1685717 := bbase (se 7 (by rfl) ⟨19754, by rfl⟩ : syracuseStep 1685717 = 39509) (by norm_num)
theorem B1685789 : Blo 746329 1685789 := bbase (se 3 (by rfl) ⟨316085, by rfl⟩ : syracuseStep 1685789 = 632171) (by norm_num)
theorem B1259813 : Blo 746329 1259813 := bbase (se 4 (by rfl) ⟨118107, by rfl⟩ : syracuseStep 1259813 = 236215) (by norm_num)
theorem B3193141 : Blo 746329 3193141 := bbase (se 5 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 3193141 = 299357) (by norm_num)
theorem B1423669 : Blo 746329 1423669 := bbase (se 5 (by rfl) ⟨66734, by rfl⟩ : syracuseStep 1423669 = 133469) (by norm_num)
theorem B3193157 : Blo 746329 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B1685861 : Blo 746329 1685861 := bbase (se 4 (by rfl) ⟨158049, by rfl⟩ : syracuseStep 1685861 = 316099) (by norm_num)
theorem B1259941 : Blo 746329 1259941 := bbase (se 4 (by rfl) ⟨118119, by rfl⟩ : syracuseStep 1259941 = 236239) (by norm_num)
theorem B1685933 : Blo 746329 1685933 := bbase (se 3 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 1685933 = 632225) (by norm_num)
theorem B1423813 : Blo 746329 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B1686005 : Blo 746329 1686005 := bbase (se 5 (by rfl) ⟨79031, by rfl⟩ : syracuseStep 1686005 = 158063) (by norm_num)
theorem B1260029 : Blo 746329 1260029 := bbase (se 3 (by rfl) ⟨236255, by rfl⟩ : syracuseStep 1260029 = 472511) (by norm_num)
theorem B6404629 : Blo 746329 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1063469 : Blo 746329 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B899633 : Blo 746329 899633 := bbase (se 2 (by rfl) ⟨337362, by rfl⟩ : syracuseStep 899633 = 674725) (by norm_num)
theorem B1686077 : Blo 746329 1686077 := bbase (se 3 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 1686077 = 632279) (by norm_num)
theorem B1423973 : Blo 746329 1423973 := bbase (se 4 (by rfl) ⟨133497, by rfl⟩ : syracuseStep 1423973 = 266995) (by norm_num)
theorem B1260157 : Blo 746329 1260157 := bbase (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) (by norm_num)
theorem B1686149 : Blo 746329 1686149 := bbase (se 4 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 1686149 = 316153) (by norm_num)
theorem B1686221 : Blo 746329 1686221 := bbase (se 3 (by rfl) ⟨316166, by rfl⟩ : syracuseStep 1686221 = 632333) (by norm_num)
theorem B1260245 : Blo 746329 1260245 := bbase (se 7 (by rfl) ⟨14768, by rfl⟩ : syracuseStep 1260245 = 29537) (by norm_num)
theorem B1424117 : Blo 746329 1424117 := bbase (se 5 (by rfl) ⟨66755, by rfl⟩ : syracuseStep 1424117 = 133511) (by norm_num)
theorem B1686293 : Blo 746329 1686293 := bbase (se 6 (by rfl) ⟨39522, by rfl⟩ : syracuseStep 1686293 = 79045) (by norm_num)
theorem B899921 : Blo 746329 899921 := bbase (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) (by norm_num)
theorem B1260373 : Blo 746329 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B3783509 : Blo 746329 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B1686365 : Blo 746329 1686365 := bbase (se 3 (by rfl) ⟨316193, by rfl⟩ : syracuseStep 1686365 = 632387) (by norm_num)
theorem B1686437 : Blo 746329 1686437 := bbase (se 4 (by rfl) ⟨158103, by rfl⟩ : syracuseStep 1686437 = 316207) (by norm_num)
theorem B1260461 : Blo 746329 1260461 := bbase (se 3 (by rfl) ⟨236336, by rfl⟩ : syracuseStep 1260461 = 472673) (by norm_num)
theorem B1686509 : Blo 746329 1686509 := bbase (se 3 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 1686509 = 632441) (by norm_num)
theorem B900085 : Blo 746329 900085 := bbase (se 5 (by rfl) ⟨42191, by rfl⟩ : syracuseStep 900085 = 84383) (by norm_num)
theorem B900113 : Blo 746329 900113 := bbase (se 2 (by rfl) ⟨337542, by rfl⟩ : syracuseStep 900113 = 675085) (by norm_num)
theorem B1424405 : Blo 746329 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B1260589 : Blo 746329 1260589 := bbase (se 3 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 1260589 = 472721) (by norm_num)
theorem B1686581 : Blo 746329 1686581 := bbase (se 5 (by rfl) ⟨79058, by rfl⟩ : syracuseStep 1686581 = 158117) (by norm_num)
theorem B1064021 : Blo 746329 1064021 := bbase (se 8 (by rfl) ⟨6234, by rfl⟩ : syracuseStep 1064021 = 12469) (by norm_num)
theorem B769109 : Blo 746329 769109 := bbase (se 8 (by rfl) ⟨4506, by rfl⟩ : syracuseStep 769109 = 9013) (by norm_num)
theorem B1686653 : Blo 746329 1686653 := bbase (se 3 (by rfl) ⟨316247, by rfl⟩ : syracuseStep 1686653 = 632495) (by norm_num)
theorem B1260677 : Blo 746329 1260677 := bbase (se 4 (by rfl) ⟨118188, by rfl⟩ : syracuseStep 1260677 = 236377) (by norm_num)
theorem B900229 : Blo 746329 900229 := bbase (se 4 (by rfl) ⟨84396, by rfl⟩ : syracuseStep 900229 = 168793) (by norm_num)
theorem B1686725 : Blo 746329 1686725 := bbase (se 4 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 1686725 = 316261) (by norm_num)
theorem B900325 : Blo 746329 900325 := bbase (se 4 (by rfl) ⟨84405, by rfl⟩ : syracuseStep 900325 = 168811) (by norm_num)
theorem B1260805 : Blo 746329 1260805 := bbase (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) (by norm_num)
theorem B1686797 : Blo 746329 1686797 := bbase (se 3 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 1686797 = 632549) (by norm_num)
theorem B1686869 : Blo 746329 1686869 := bbase (se 11 (by rfl) ⟨1235, by rfl⟩ : syracuseStep 1686869 = 2471) (by norm_num)
theorem B1260893 : Blo 746329 1260893 := bbase (se 3 (by rfl) ⟨236417, by rfl⟩ : syracuseStep 1260893 = 472835) (by norm_num)
theorem B1686941 : Blo 746329 1686941 := bbase (se 3 (by rfl) ⟨316301, by rfl⟩ : syracuseStep 1686941 = 632603) (by norm_num)
theorem B1261021 : Blo 746329 1261021 := bbase (se 3 (by rfl) ⟨236441, by rfl⟩ : syracuseStep 1261021 = 472883) (by norm_num)
theorem B1687013 : Blo 746329 1687013 := bbase (se 4 (by rfl) ⟨158157, by rfl⟩ : syracuseStep 1687013 = 316315) (by norm_num)
theorem B4046357 : Blo 746329 4046357 := bbase (se 6 (by rfl) ⟨94836, by rfl⟩ : syracuseStep 4046357 = 189673) (by norm_num)
theorem B1687085 : Blo 746329 1687085 := bbase (se 3 (by rfl) ⟨316328, by rfl⟩ : syracuseStep 1687085 = 632657) (by norm_num)
theorem B2833973 : Blo 746329 2833973 := bbase (se 5 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 2833973 = 265685) (by norm_num)
theorem B1261109 : Blo 746329 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B1195589 : Blo 746329 1195589 := bbase (se 4 (by rfl) ⟨112086, by rfl⟩ : syracuseStep 1195589 = 224173) (by norm_num)
theorem B1687157 : Blo 746329 1687157 := bbase (se 5 (by rfl) ⟨79085, by rfl⟩ : syracuseStep 1687157 = 158171) (by norm_num)
theorem B1261237 : Blo 746329 1261237 := bbase (se 5 (by rfl) ⟨59120, by rfl⟩ : syracuseStep 1261237 = 118241) (by norm_num)
theorem B1687229 : Blo 746329 1687229 := bbase (se 3 (by rfl) ⟨316355, by rfl⟩ : syracuseStep 1687229 = 632711) (by norm_num)
theorem B1195717 : Blo 746329 1195717 := bbase (se 4 (by rfl) ⟨112098, by rfl⟩ : syracuseStep 1195717 = 224197) (by norm_num)
theorem B900805 : Blo 746329 900805 := bbase (se 4 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 900805 = 168901) (by norm_num)
theorem B1687301 : Blo 746329 1687301 := bbase (se 4 (by rfl) ⟨158184, by rfl⟩ : syracuseStep 1687301 = 316369) (by norm_num)
theorem B1261325 : Blo 746329 1261325 := bbase (se 3 (by rfl) ⟨236498, by rfl⟩ : syracuseStep 1261325 = 472997) (by norm_num)
theorem B1064773 : Blo 746329 1064773 := bbase (se 4 (by rfl) ⟨99822, by rfl⟩ : syracuseStep 1064773 = 199645) (by norm_num)
theorem B1687373 : Blo 746329 1687373 := bbase (se 3 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 1687373 = 632765) (by norm_num)
theorem B2834261 : Blo 746329 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B1261453 : Blo 746329 1261453 := bbase (se 3 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 1261453 = 473045) (by norm_num)
theorem B1687445 : Blo 746329 1687445 := bbase (se 6 (by rfl) ⟨39549, by rfl⟩ : syracuseStep 1687445 = 79099) (by norm_num)
theorem B2703253 : Blo 746329 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B770005 : Blo 746329 770005 := bbase (se 7 (by rfl) ⟨9023, by rfl⟩ : syracuseStep 770005 = 18047) (by norm_num)
theorem B1687517 : Blo 746329 1687517 := bbase (se 3 (by rfl) ⟨316409, by rfl⟩ : syracuseStep 1687517 = 632819) (by norm_num)
theorem B1261541 : Blo 746329 1261541 := bbase (se 4 (by rfl) ⟨118269, by rfl⟩ : syracuseStep 1261541 = 236539) (by norm_num)
theorem B5128181 : Blo 746329 5128181 := bbase (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) (by norm_num)
theorem B1687589 : Blo 746329 1687589 := bbase (se 4 (by rfl) ⟨158211, by rfl⟩ : syracuseStep 1687589 = 316423) (by norm_num)
theorem B3784805 : Blo 746329 3784805 := bbase (se 4 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 3784805 = 709651) (by norm_num)
theorem B1261669 : Blo 746329 1261669 := bbase (se 4 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 1261669 = 236563) (by norm_num)
theorem B1687661 : Blo 746329 1687661 := bbase (se 3 (by rfl) ⟨316436, by rfl⟩ : syracuseStep 1687661 = 632873) (by norm_num)
theorem B1687733 : Blo 746329 1687733 := bbase (se 5 (by rfl) ⟨79112, by rfl⟩ : syracuseStep 1687733 = 158225) (by norm_num)
theorem B1261757 : Blo 746329 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B8536277 : Blo 746329 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B9126101 : Blo 746329 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B1687805 : Blo 746329 1687805 := bbase (se 3 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 1687805 = 632927) (by norm_num)
theorem B1261885 : Blo 746329 1261885 := bbase (se 3 (by rfl) ⟨236603, by rfl⟩ : syracuseStep 1261885 = 473207) (by norm_num)
theorem B1687877 : Blo 746329 1687877 := bbase (se 4 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 1687877 = 316477) (by norm_num)
theorem B1687949 : Blo 746329 1687949 := bbase (se 3 (by rfl) ⟨316490, by rfl⟩ : syracuseStep 1687949 = 632981) (by norm_num)
theorem B1261973 : Blo 746329 1261973 := bbase (se 6 (by rfl) ⟨29577, by rfl⟩ : syracuseStep 1261973 = 59155) (by norm_num)
theorem B6406613 : Blo 746329 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B10961365 : Blo 746329 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1688021 : Blo 746329 1688021 := bbase (se 7 (by rfl) ⟨19781, by rfl⟩ : syracuseStep 1688021 = 39563) (by norm_num)
theorem B1196525 : Blo 746329 1196525 := bbase (se 3 (by rfl) ⟨224348, by rfl⟩ : syracuseStep 1196525 = 448697) (by norm_num)
theorem B1262101 : Blo 746329 1262101 := bbase (se 6 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 1262101 = 59161) (by norm_num)
theorem B3195413 : Blo 746329 3195413 := bbase (se 6 (by rfl) ⟨74892, by rfl⟩ : syracuseStep 3195413 = 149785) (by norm_num)
theorem B6242837 : Blo 746329 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1688093 : Blo 746329 1688093 := bbase (se 3 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 1688093 = 633035) (by norm_num)
theorem B1065565 : Blo 746329 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B1688165 : Blo 746329 1688165 := bbase (se 4 (by rfl) ⟨158265, by rfl⟩ : syracuseStep 1688165 = 316531) (by norm_num)
theorem B1262189 : Blo 746329 1262189 := bbase (se 3 (by rfl) ⟨236660, by rfl⟩ : syracuseStep 1262189 = 473321) (by norm_num)
theorem B1688237 : Blo 746329 1688237 := bbase (se 3 (by rfl) ⟨316544, by rfl⟩ : syracuseStep 1688237 = 633089) (by norm_num)
theorem B1262317 : Blo 746329 1262317 := bbase (se 3 (by rfl) ⟨236684, by rfl⟩ : syracuseStep 1262317 = 473369) (by norm_num)
theorem B1196813 : Blo 746329 1196813 := bbase (se 3 (by rfl) ⟨224402, by rfl⟩ : syracuseStep 1196813 = 448805) (by norm_num)
theorem B1262405 : Blo 746329 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B1065901 : Blo 746329 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B1262533 : Blo 746329 1262533 := bbase (se 4 (by rfl) ⟨118362, by rfl⟩ : syracuseStep 1262533 = 236725) (by norm_num)
theorem B2835445 : Blo 746329 2835445 := bbase (se 5 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 2835445 = 265823) (by norm_num)
theorem B1262621 : Blo 746329 1262621 := bbase (se 3 (by rfl) ⟨236741, by rfl⟩ : syracuseStep 1262621 = 473483) (by norm_num)
theorem B1066117 : Blo 746329 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B1262749 : Blo 746329 1262749 := bbase (se 3 (by rfl) ⟨236765, by rfl⟩ : syracuseStep 1262749 = 473531) (by norm_num)
theorem B1197229 : Blo 746329 1197229 := bbase (se 3 (by rfl) ⟨224480, by rfl⟩ : syracuseStep 1197229 = 448961) (by norm_num)
theorem B3884213 : Blo 746329 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1262837 : Blo 746329 1262837 := bbase (se 5 (by rfl) ⟨59195, by rfl⟩ : syracuseStep 1262837 = 118391) (by norm_num)
theorem B2835749 : Blo 746329 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B3786101 : Blo 746329 3786101 := bbase (se 5 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 3786101 = 354947) (by norm_num)
theorem B1262965 : Blo 746329 1262965 := bbase (se 5 (by rfl) ⟨59201, by rfl⟩ : syracuseStep 1262965 = 118403) (by norm_num)
theorem B1263053 : Blo 746329 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B10765781 : Blo 746329 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B3032549 : Blo 746329 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1066493 : Blo 746329 1066493 := bbase (se 3 (by rfl) ⟨199967, by rfl⟩ : syracuseStep 1066493 = 399935) (by norm_num)
theorem B1263181 : Blo 746329 1263181 := bbase (se 3 (by rfl) ⟨236846, by rfl⟩ : syracuseStep 1263181 = 473693) (by norm_num)
theorem B1263269 : Blo 746329 1263269 := bbase (se 4 (by rfl) ⟨118431, by rfl⟩ : syracuseStep 1263269 = 236863) (by norm_num)
theorem B1263397 : Blo 746329 1263397 := bbase (se 4 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 1263397 = 236887) (by norm_num)
theorem B8898389 : Blo 746329 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B1263485 : Blo 746329 1263485 := bbase (se 3 (by rfl) ⟨236903, by rfl⟩ : syracuseStep 1263485 = 473807) (by norm_num)
theorem B1263613 : Blo 746329 1263613 := bbase (se 3 (by rfl) ⟨236927, by rfl⟩ : syracuseStep 1263613 = 473855) (by norm_num)
theorem B1198165 : Blo 746329 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B7784533 : Blo 746329 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B1263701 : Blo 746329 1263701 := bbase (se 8 (by rfl) ⟨7404, by rfl⟩ : syracuseStep 1263701 = 14809) (by norm_num)
theorem B1263829 : Blo 746329 1263829 := bbase (se 7 (by rfl) ⟨14810, by rfl⟩ : syracuseStep 1263829 = 29621) (by norm_num)
theorem B1263917 : Blo 746329 1263917 := bbase (se 3 (by rfl) ⟨236984, by rfl⟩ : syracuseStep 1263917 = 473969) (by norm_num)
theorem B1264045 : Blo 746329 1264045 := bbase (se 3 (by rfl) ⟨237008, by rfl⟩ : syracuseStep 1264045 = 474017) (by norm_num)
theorem B1264133 : Blo 746329 1264133 := bbase (se 4 (by rfl) ⟨118512, by rfl⟩ : syracuseStep 1264133 = 237025) (by norm_num)
theorem B5130805 : Blo 746329 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B3787397 : Blo 746329 3787397 := bbase (se 4 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 3787397 = 710137) (by norm_num)
theorem B1264261 : Blo 746329 1264261 := bbase (se 4 (by rfl) ⟨118524, by rfl⟩ : syracuseStep 1264261 = 237049) (by norm_num)
theorem B1264349 : Blo 746329 1264349 := bbase (se 3 (by rfl) ⟨237065, by rfl⟩ : syracuseStep 1264349 = 474131) (by norm_num)
theorem B3033893 : Blo 746329 3033893 := bbase (se 4 (by rfl) ⟨284427, by rfl⟩ : syracuseStep 3033893 = 568855) (by norm_num)
theorem B1264477 : Blo 746329 1264477 := bbase (se 3 (by rfl) ⟨237089, by rfl⟩ : syracuseStep 1264477 = 474179) (by norm_num)
theorem B1067917 : Blo 746329 1067917 := bbase (se 3 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 1067917 = 400469) (by norm_num)
theorem B1264565 : Blo 746329 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B1264693 : Blo 746329 1264693 := bbase (se 5 (by rfl) ⟨59282, by rfl⟩ : syracuseStep 1264693 = 118565) (by norm_num)
theorem B1264781 : Blo 746329 1264781 := bbase (se 3 (by rfl) ⟨237146, by rfl⟩ : syracuseStep 1264781 = 474293) (by norm_num)
theorem B1199357 : Blo 746329 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B1264909 : Blo 746329 1264909 := bbase (se 3 (by rfl) ⟨237170, by rfl⟩ : syracuseStep 1264909 = 474341) (by norm_num)
theorem B5688629 : Blo 746329 5688629 := bbase (se 5 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 5688629 = 533309) (by norm_num)
theorem B2837861 : Blo 746329 2837861 := bbase (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) (by norm_num)
theorem B1264997 : Blo 746329 1264997 := bbase (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) (by norm_num)
theorem B1199549 : Blo 746329 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B1265125 : Blo 746329 1265125 := bbase (se 4 (by rfl) ⟨118605, by rfl⟩ : syracuseStep 1265125 = 237211) (by norm_num)
theorem B7687669 : Blo 746329 7687669 := bbase (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) (by norm_num)
theorem B1265213 : Blo 746329 1265213 := bbase (se 3 (by rfl) ⟨237227, by rfl⟩ : syracuseStep 1265213 = 474455) (by norm_num)
theorem B2838149 : Blo 746329 2838149 := bbase (se 4 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 2838149 = 532153) (by norm_num)
theorem B1265341 : Blo 746329 1265341 := bbase (se 3 (by rfl) ⟨237251, by rfl⟩ : syracuseStep 1265341 = 474503) (by norm_num)
theorem B1265429 : Blo 746329 1265429 := bbase (se 6 (by rfl) ⟨29658, by rfl⟩ : syracuseStep 1265429 = 59317) (by norm_num)
theorem B3788693 : Blo 746329 3788693 := bbase (se 6 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 3788693 = 177595) (by norm_num)
theorem B1265557 : Blo 746329 1265557 := bbase (se 6 (by rfl) ⟨29661, by rfl⟩ : syracuseStep 1265557 = 59323) (by norm_num)
theorem B7196597 : Blo 746329 7196597 := bbase (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) (by norm_num)
theorem B3592133 : Blo 746329 3592133 := bbase (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) (by norm_num)
theorem B839641 : Blo 746329 839641 := bbase (se 2 (by rfl) ⟨314865, by rfl⟩ : syracuseStep 839641 = 629731) (by norm_num)
theorem B1265645 : Blo 746329 1265645 := bbase (se 3 (by rfl) ⟨237308, by rfl⟩ : syracuseStep 1265645 = 474617) (by norm_num)
theorem B839677 : Blo 746329 839677 := bbase (se 3 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 839677 = 314879) (by norm_num)
theorem B839713 : Blo 746329 839713 := bbase (se 2 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 839713 = 629785) (by norm_num)
theorem B839749 : Blo 746329 839749 := bbase (se 4 (by rfl) ⟨78726, by rfl⟩ : syracuseStep 839749 = 157453) (by norm_num)
theorem B839785 : Blo 746329 839785 := bbase (se 2 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 839785 = 629839) (by norm_num)
theorem B1265773 : Blo 746329 1265773 := bbase (se 3 (by rfl) ⟨237332, by rfl⟩ : syracuseStep 1265773 = 474665) (by norm_num)
theorem B839821 : Blo 746329 839821 := bbase (se 3 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 839821 = 314933) (by norm_num)
theorem B4804757 : Blo 746329 4804757 := bbase (se 6 (by rfl) ⟨112611, by rfl⟩ : syracuseStep 4804757 = 225223) (by norm_num)
theorem B839857 : Blo 746329 839857 := bbase (se 2 (by rfl) ⟨314946, by rfl⟩ : syracuseStep 839857 = 629893) (by norm_num)
theorem B1265861 : Blo 746329 1265861 := bbase (se 4 (by rfl) ⟨118674, by rfl⟩ : syracuseStep 1265861 = 237349) (by norm_num)
theorem B839893 : Blo 746329 839893 := bbase (se 7 (by rfl) ⟨9842, by rfl⟩ : syracuseStep 839893 = 19685) (by norm_num)
theorem B839929 : Blo 746329 839929 := bbase (se 2 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 839929 = 629947) (by norm_num)
theorem B839965 : Blo 746329 839965 := bbase (se 3 (by rfl) ⟨157493, by rfl⟩ : syracuseStep 839965 = 314987) (by norm_num)
theorem B840001 : Blo 746329 840001 := bbase (se 2 (by rfl) ⟨315000, by rfl⟩ : syracuseStep 840001 = 630001) (by norm_num)
theorem B1265989 : Blo 746329 1265989 := bbase (se 4 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 1265989 = 237373) (by norm_num)
theorem B840037 : Blo 746329 840037 := bbase (se 4 (by rfl) ⟨78753, by rfl⟩ : syracuseStep 840037 = 157507) (by norm_num)
theorem B840073 : Blo 746329 840073 := bbase (se 2 (by rfl) ⟨315027, by rfl⟩ : syracuseStep 840073 = 630055) (by norm_num)
theorem B1266077 : Blo 746329 1266077 := bbase (se 3 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 1266077 = 474779) (by norm_num)
theorem B840109 : Blo 746329 840109 := bbase (se 3 (by rfl) ⟨157520, by rfl⟩ : syracuseStep 840109 = 315041) (by norm_num)
theorem B840145 : Blo 746329 840145 := bbase (se 2 (by rfl) ⟨315054, by rfl⟩ : syracuseStep 840145 = 630109) (by norm_num)
theorem B3199445 : Blo 746329 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B840181 : Blo 746329 840181 := bbase (se 5 (by rfl) ⟨39383, by rfl⟩ : syracuseStep 840181 = 78767) (by norm_num)
theorem B840217 : Blo 746329 840217 := bbase (se 2 (by rfl) ⟨315081, by rfl⟩ : syracuseStep 840217 = 630163) (by norm_num)
theorem B840253 : Blo 746329 840253 := bbase (se 3 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 840253 = 315095) (by norm_num)
theorem B3330629 : Blo 746329 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B840289 : Blo 746329 840289 := bbase (se 2 (by rfl) ⟨315108, by rfl⟩ : syracuseStep 840289 = 630217) (by norm_num)
theorem B840325 : Blo 746329 840325 := bbase (se 4 (by rfl) ⟨78780, by rfl⟩ : syracuseStep 840325 = 157561) (by norm_num)
theorem B12145301 : Blo 746329 12145301 := bbase (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) (by norm_num)
theorem B840361 : Blo 746329 840361 := bbase (se 2 (by rfl) ⟨315135, by rfl⟩ : syracuseStep 840361 = 630271) (by norm_num)
theorem B840397 : Blo 746329 840397 := bbase (se 3 (by rfl) ⟨157574, by rfl⟩ : syracuseStep 840397 = 315149) (by norm_num)
theorem B840433 : Blo 746329 840433 := bbase (se 2 (by rfl) ⟨315162, by rfl⟩ : syracuseStep 840433 = 630325) (by norm_num)
theorem B1823485 : Blo 746329 1823485 := bbase (se 3 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 1823485 = 683807) (by norm_num)
theorem B840469 : Blo 746329 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B2839333 : Blo 746329 2839333 := bbase (se 4 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 2839333 = 532375) (by norm_num)
theorem B1299253 : Blo 746329 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B840505 : Blo 746329 840505 := bbase (se 2 (by rfl) ⟨315189, by rfl⟩ : syracuseStep 840505 = 630379) (by norm_num)
theorem B840541 : Blo 746329 840541 := bbase (se 3 (by rfl) ⟨157601, by rfl⟩ : syracuseStep 840541 = 315203) (by norm_num)
theorem B1200997 : Blo 746329 1200997 := bbase (se 4 (by rfl) ⟨112593, by rfl⟩ : syracuseStep 1200997 = 225187) (by norm_num)
theorem B840577 : Blo 746329 840577 := bbase (se 2 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 840577 = 630433) (by norm_num)
theorem B840613 : Blo 746329 840613 := bbase (se 4 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 840613 = 157615) (by norm_num)
theorem B840649 : Blo 746329 840649 := bbase (se 2 (by rfl) ⟨315243, by rfl⟩ : syracuseStep 840649 = 630487) (by norm_num)
theorem B840685 : Blo 746329 840685 := bbase (se 3 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 840685 = 315257) (by norm_num)
theorem B840721 : Blo 746329 840721 := bbase (se 2 (by rfl) ⟨315270, by rfl⟩ : syracuseStep 840721 = 630541) (by norm_num)
theorem B840757 : Blo 746329 840757 := bbase (se 5 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 840757 = 78821) (by norm_num)
theorem B1889365 : Blo 746329 1889365 := bbase (se 8 (by rfl) ⟨11070, by rfl⟩ : syracuseStep 1889365 = 22141) (by norm_num)
theorem B2839637 : Blo 746329 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B840793 : Blo 746329 840793 := bbase (se 2 (by rfl) ⟨315297, by rfl⟩ : syracuseStep 840793 = 630595) (by norm_num)
theorem B840829 : Blo 746329 840829 := bbase (se 3 (by rfl) ⟨157655, by rfl⟩ : syracuseStep 840829 = 315311) (by norm_num)
theorem B840865 : Blo 746329 840865 := bbase (se 2 (by rfl) ⟨315324, by rfl⟩ : syracuseStep 840865 = 630649) (by norm_num)
theorem B1365157 : Blo 746329 1365157 := bbase (se 4 (by rfl) ⟨127983, by rfl⟩ : syracuseStep 1365157 = 255967) (by norm_num)
theorem B3789989 : Blo 746329 3789989 := bbase (se 4 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 3789989 = 710623) (by norm_num)
theorem B1889477 : Blo 746329 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B840901 : Blo 746329 840901 := bbase (se 4 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 840901 = 157669) (by norm_num)
theorem B840937 : Blo 746329 840937 := bbase (se 2 (by rfl) ⟨315351, by rfl⟩ : syracuseStep 840937 = 630703) (by norm_num)
theorem B840973 : Blo 746329 840973 := bbase (se 3 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 840973 = 315365) (by norm_num)
theorem B841009 : Blo 746329 841009 := bbase (se 2 (by rfl) ⟨315378, by rfl⟩ : syracuseStep 841009 = 630757) (by norm_num)
theorem B841045 : Blo 746329 841045 := bbase (se 15 (by rfl) ⟨38, by rfl⟩ : syracuseStep 841045 = 77) (by norm_num)
theorem B1594733 : Blo 746329 1594733 := bbase (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) (by norm_num)
theorem B841081 : Blo 746329 841081 := bbase (se 2 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 841081 = 630811) (by norm_num)
theorem B1889669 : Blo 746329 1889669 := bbase (se 4 (by rfl) ⟨177156, by rfl⟩ : syracuseStep 1889669 = 354313) (by norm_num)
theorem B841117 : Blo 746329 841117 := bbase (se 3 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 841117 = 315419) (by norm_num)
theorem B808385 : Blo 746329 808385 := bbase (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) (by norm_num)
theorem B841153 : Blo 746329 841153 := bbase (se 2 (by rfl) ⟨315432, by rfl⟩ : syracuseStep 841153 = 630865) (by norm_num)
theorem B1299925 : Blo 746329 1299925 := bbase (se 7 (by rfl) ⟨15233, by rfl⟩ : syracuseStep 1299925 = 30467) (by norm_num)
theorem B841189 : Blo 746329 841189 := bbase (se 4 (by rfl) ⟨78861, by rfl⟩ : syracuseStep 841189 = 157723) (by norm_num)
theorem B1136117 : Blo 746329 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B972281 : Blo 746329 972281 := bbase (se 2 (by rfl) ⟨364605, by rfl⟩ : syracuseStep 972281 = 729211) (by norm_num)
theorem B841225 : Blo 746329 841225 := bbase (se 2 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 841225 = 630919) (by norm_num)
theorem B4052501 : Blo 746329 4052501 := bbase (se 6 (by rfl) ⟨94980, by rfl⟩ : syracuseStep 4052501 = 189961) (by norm_num)
theorem B841261 : Blo 746329 841261 := bbase (se 3 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 841261 = 315473) (by norm_num)
theorem B841297 : Blo 746329 841297 := bbase (se 2 (by rfl) ⟨315486, by rfl⟩ : syracuseStep 841297 = 630973) (by norm_num)
theorem B1594973 : Blo 746329 1594973 := bbase (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) (by norm_num)
theorem B841333 : Blo 746329 841333 := bbase (se 5 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 841333 = 78875) (by norm_num)
theorem B841369 : Blo 746329 841369 := bbase (se 2 (by rfl) ⟨315513, by rfl⟩ : syracuseStep 841369 = 631027) (by norm_num)
theorem B841405 : Blo 746329 841405 := bbase (se 3 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 841405 = 315527) (by norm_num)
theorem B1890013 : Blo 746329 1890013 := bbase (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) (by norm_num)
theorem B841441 : Blo 746329 841441 := bbase (se 2 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 841441 = 631081) (by norm_num)
theorem B841477 : Blo 746329 841477 := bbase (se 4 (by rfl) ⟨78888, by rfl⟩ : syracuseStep 841477 = 157777) (by norm_num)
theorem B841513 : Blo 746329 841513 := bbase (se 2 (by rfl) ⟨315567, by rfl⟩ : syracuseStep 841513 = 631135) (by norm_num)
theorem B1890125 : Blo 746329 1890125 := bbase (se 3 (by rfl) ⟨354398, by rfl⟩ : syracuseStep 1890125 = 708797) (by norm_num)
theorem B841549 : Blo 746329 841549 := bbase (se 3 (by rfl) ⟨157790, by rfl⟩ : syracuseStep 841549 = 315581) (by norm_num)
theorem B841585 : Blo 746329 841585 := bbase (se 2 (by rfl) ⟨315594, by rfl⟩ : syracuseStep 841585 = 631189) (by norm_num)
theorem B841621 : Blo 746329 841621 := bbase (se 6 (by rfl) ⟨19725, by rfl⟩ : syracuseStep 841621 = 39451) (by norm_num)
theorem B841657 : Blo 746329 841657 := bbase (se 2 (by rfl) ⟨315621, by rfl⟩ : syracuseStep 841657 = 631243) (by norm_num)
theorem B841693 : Blo 746329 841693 := bbase (se 3 (by rfl) ⟨157817, by rfl⟩ : syracuseStep 841693 = 315635) (by norm_num)
theorem B841729 : Blo 746329 841729 := bbase (se 2 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 841729 = 631297) (by norm_num)
theorem B1366021 : Blo 746329 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B1890317 : Blo 746329 1890317 := bbase (se 3 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 1890317 = 708869) (by norm_num)
theorem B841765 : Blo 746329 841765 := bbase (se 4 (by rfl) ⟨78915, by rfl⟩ : syracuseStep 841765 = 157831) (by norm_num)
theorem B841801 : Blo 746329 841801 := bbase (se 2 (by rfl) ⟨315675, by rfl⟩ : syracuseStep 841801 = 631351) (by norm_num)
theorem B1595477 : Blo 746329 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B1595485 : Blo 746329 1595485 := bbase (se 3 (by rfl) ⟨299153, by rfl⟩ : syracuseStep 1595485 = 598307) (by norm_num)
theorem B841837 : Blo 746329 841837 := bbase (se 3 (by rfl) ⟨157844, by rfl⟩ : syracuseStep 841837 = 315689) (by norm_num)
theorem B1136773 : Blo 746329 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B841873 : Blo 746329 841873 := bbase (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) (by norm_num)
theorem B841909 : Blo 746329 841909 := bbase (se 5 (by rfl) ⟨39464, by rfl⟩ : syracuseStep 841909 = 78929) (by norm_num)
theorem B3201221 : Blo 746329 3201221 := bbase (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) (by norm_num)
theorem B8542421 : Blo 746329 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B841945 : Blo 746329 841945 := bbase (se 2 (by rfl) ⟨315729, by rfl⟩ : syracuseStep 841945 = 631459) (by norm_num)
theorem B1366253 : Blo 746329 1366253 := bbase (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) (by norm_num)
theorem B841981 : Blo 746329 841981 := bbase (se 3 (by rfl) ⟨157871, by rfl⟩ : syracuseStep 841981 = 315743) (by norm_num)
theorem B842017 : Blo 746329 842017 := bbase (se 2 (by rfl) ⟨315756, by rfl⟩ : syracuseStep 842017 = 631513) (by norm_num)
theorem B1136933 : Blo 746329 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B842053 : Blo 746329 842053 := bbase (se 4 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 842053 = 157885) (by norm_num)
theorem B1890661 : Blo 746329 1890661 := bbase (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) (by norm_num)
theorem B842089 : Blo 746329 842089 := bbase (se 2 (by rfl) ⟨315783, by rfl⟩ : syracuseStep 842089 = 631567) (by norm_num)
theorem B842125 : Blo 746329 842125 := bbase (se 3 (by rfl) ⟨157898, by rfl⟩ : syracuseStep 842125 = 315797) (by norm_num)
theorem B842161 : Blo 746329 842161 := bbase (se 2 (by rfl) ⟨315810, by rfl⟩ : syracuseStep 842161 = 631621) (by norm_num)
theorem B3791285 : Blo 746329 3791285 := bbase (se 5 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 3791285 = 355433) (by norm_num)
theorem B1890773 : Blo 746329 1890773 := bbase (se 7 (by rfl) ⟨22157, by rfl⟩ : syracuseStep 1890773 = 44315) (by norm_num)
theorem B842197 : Blo 746329 842197 := bbase (se 7 (by rfl) ⟨9869, by rfl⟩ : syracuseStep 842197 = 19739) (by norm_num)
theorem B842233 : Blo 746329 842233 := bbase (se 2 (by rfl) ⟨315837, by rfl⟩ : syracuseStep 842233 = 631675) (by norm_num)
theorem B842269 : Blo 746329 842269 := bbase (se 3 (by rfl) ⟨157925, by rfl⟩ : syracuseStep 842269 = 315851) (by norm_num)
theorem B842305 : Blo 746329 842305 := bbase (se 2 (by rfl) ⟨315864, by rfl⟩ : syracuseStep 842305 = 631729) (by norm_num)
theorem B842341 : Blo 746329 842341 := bbase (se 4 (by rfl) ⟨78969, by rfl⟩ : syracuseStep 842341 = 157939) (by norm_num)
theorem B842377 : Blo 746329 842377 := bbase (se 2 (by rfl) ⟨315891, by rfl⟩ : syracuseStep 842377 = 631783) (by norm_num)
theorem B1890965 : Blo 746329 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B842413 : Blo 746329 842413 := bbase (se 3 (by rfl) ⟨157952, by rfl⟩ : syracuseStep 842413 = 315905) (by norm_num)
theorem B842449 : Blo 746329 842449 := bbase (se 2 (by rfl) ⟨315918, by rfl⟩ : syracuseStep 842449 = 631837) (by norm_num)
theorem B842485 : Blo 746329 842485 := bbase (se 5 (by rfl) ⟨39491, by rfl⟩ : syracuseStep 842485 = 78983) (by norm_num)
theorem B842521 : Blo 746329 842521 := bbase (se 2 (by rfl) ⟨315945, by rfl⟩ : syracuseStep 842521 = 631891) (by norm_num)
theorem B842557 : Blo 746329 842557 := bbase (se 3 (by rfl) ⟨157979, by rfl⟩ : syracuseStep 842557 = 315959) (by norm_num)
theorem B842593 : Blo 746329 842593 := bbase (se 2 (by rfl) ⟨315972, by rfl⟩ : syracuseStep 842593 = 631945) (by norm_num)
theorem B1825637 : Blo 746329 1825637 := bbase (se 4 (by rfl) ⟨171153, by rfl⟩ : syracuseStep 1825637 = 342307) (by norm_num)
theorem B842629 : Blo 746329 842629 := bbase (se 4 (by rfl) ⟨78996, by rfl⟩ : syracuseStep 842629 = 157993) (by norm_num)
theorem B875405 : Blo 746329 875405 := bbase (se 3 (by rfl) ⟨164138, by rfl⟩ : syracuseStep 875405 = 328277) (by norm_num)
theorem B842665 : Blo 746329 842665 := bbase (se 2 (by rfl) ⟨315999, by rfl⟩ : syracuseStep 842665 = 631999) (by norm_num)
theorem B842701 : Blo 746329 842701 := bbase (se 3 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 842701 = 316013) (by norm_num)
theorem B1891309 : Blo 746329 1891309 := bbase (se 3 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 1891309 = 709241) (by norm_num)
theorem B842737 : Blo 746329 842737 := bbase (se 2 (by rfl) ⟨316026, by rfl⟩ : syracuseStep 842737 = 632053) (by norm_num)
theorem B842773 : Blo 746329 842773 := bbase (se 6 (by rfl) ⟨19752, by rfl⟩ : syracuseStep 842773 = 39505) (by norm_num)
theorem B973873 : Blo 746329 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B842809 : Blo 746329 842809 := bbase (se 2 (by rfl) ⟨316053, by rfl⟩ : syracuseStep 842809 = 632107) (by norm_num)
theorem B1891421 : Blo 746329 1891421 := bbase (se 3 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 1891421 = 709283) (by norm_num)
theorem B842845 : Blo 746329 842845 := bbase (se 3 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 842845 = 316067) (by norm_num)
theorem B842881 : Blo 746329 842881 := bbase (se 2 (by rfl) ⟨316080, by rfl⟩ : syracuseStep 842881 = 632161) (by norm_num)
theorem B2841749 : Blo 746329 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B5397653 : Blo 746329 5397653 := bbase (se 6 (by rfl) ⟨126507, by rfl⟩ : syracuseStep 5397653 = 253015) (by norm_num)
theorem B842917 : Blo 746329 842917 := bbase (se 4 (by rfl) ⟨79023, by rfl⟩ : syracuseStep 842917 = 158047) (by norm_num)
theorem B3202213 : Blo 746329 3202213 := bbase (se 4 (by rfl) ⟨300207, by rfl⟩ : syracuseStep 3202213 = 600415) (by norm_num)
theorem B1596613 : Blo 746329 1596613 := bbase (se 4 (by rfl) ⟨149682, by rfl⟩ : syracuseStep 1596613 = 299365) (by norm_num)
theorem B842953 : Blo 746329 842953 := bbase (se 2 (by rfl) ⟨316107, by rfl⟩ : syracuseStep 842953 = 632215) (by norm_num)
theorem B842989 : Blo 746329 842989 := bbase (se 3 (by rfl) ⟨158060, by rfl⟩ : syracuseStep 842989 = 316121) (by norm_num)
theorem B843025 : Blo 746329 843025 := bbase (se 2 (by rfl) ⟨316134, by rfl⟩ : syracuseStep 843025 = 632269) (by norm_num)
theorem B1137941 : Blo 746329 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B1891613 : Blo 746329 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B843061 : Blo 746329 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B843097 : Blo 746329 843097 := bbase (se 2 (by rfl) ⟨316161, by rfl⟩ : syracuseStep 843097 = 632323) (by norm_num)
theorem B843133 : Blo 746329 843133 := bbase (se 3 (by rfl) ⟨158087, by rfl⟩ : syracuseStep 843133 = 316175) (by norm_num)
theorem B843169 : Blo 746329 843169 := bbase (se 2 (by rfl) ⟨316188, by rfl⟩ : syracuseStep 843169 = 632377) (by norm_num)
theorem B2842037 : Blo 746329 2842037 := bbase (se 5 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 2842037 = 266441) (by norm_num)
theorem B810425 : Blo 746329 810425 := bbase (se 2 (by rfl) ⟨303909, by rfl⟩ : syracuseStep 810425 = 607819) (by norm_num)
theorem B843205 : Blo 746329 843205 := bbase (se 4 (by rfl) ⟨79050, by rfl⟩ : syracuseStep 843205 = 158101) (by norm_num)
theorem B843241 : Blo 746329 843241 := bbase (se 2 (by rfl) ⟨316215, by rfl⟩ : syracuseStep 843241 = 632431) (by norm_num)
theorem B843277 : Blo 746329 843277 := bbase (se 3 (by rfl) ⟨158114, by rfl⟩ : syracuseStep 843277 = 316229) (by norm_num)
theorem B843313 : Blo 746329 843313 := bbase (se 2 (by rfl) ⟨316242, by rfl⟩ : syracuseStep 843313 = 632485) (by norm_num)
theorem B2022965 : Blo 746329 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B1596989 : Blo 746329 1596989 := bbase (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) (by norm_num)
theorem B843349 : Blo 746329 843349 := bbase (se 8 (by rfl) ⟨4941, by rfl⟩ : syracuseStep 843349 = 9883) (by norm_num)
theorem B1891957 : Blo 746329 1891957 := bbase (se 5 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 1891957 = 177371) (by norm_num)
theorem B843385 : Blo 746329 843385 := bbase (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) (by norm_num)
theorem B843421 : Blo 746329 843421 := bbase (se 3 (by rfl) ⟨158141, by rfl⟩ : syracuseStep 843421 = 316283) (by norm_num)
theorem B843457 : Blo 746329 843457 := bbase (se 2 (by rfl) ⟨316296, by rfl⟩ : syracuseStep 843457 = 632593) (by norm_num)
theorem B3792581 : Blo 746329 3792581 := bbase (se 4 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 3792581 = 711109) (by norm_num)
theorem B1892069 : Blo 746329 1892069 := bbase (se 4 (by rfl) ⟨177381, by rfl⟩ : syracuseStep 1892069 = 354763) (by norm_num)
theorem B843493 : Blo 746329 843493 := bbase (se 4 (by rfl) ⟨79077, by rfl⟩ : syracuseStep 843493 = 158155) (by norm_num)
theorem B1793789 : Blo 746329 1793789 := bbase (se 3 (by rfl) ⟨336335, by rfl⟩ : syracuseStep 1793789 = 672671) (by norm_num)
theorem B843529 : Blo 746329 843529 := bbase (se 2 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 843529 = 632647) (by norm_num)
theorem B843565 : Blo 746329 843565 := bbase (se 3 (by rfl) ⟨158168, by rfl⟩ : syracuseStep 843565 = 316337) (by norm_num)
theorem B843601 : Blo 746329 843601 := bbase (se 2 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 843601 = 632701) (by norm_num)
theorem B843637 : Blo 746329 843637 := bbase (se 5 (by rfl) ⟨39545, by rfl⟩ : syracuseStep 843637 = 79091) (by norm_num)
theorem B843673 : Blo 746329 843673 := bbase (se 2 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 843673 = 632755) (by norm_num)
theorem B1892261 : Blo 746329 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B843709 : Blo 746329 843709 := bbase (se 3 (by rfl) ⟨158195, by rfl⟩ : syracuseStep 843709 = 316391) (by norm_num)
theorem B843745 : Blo 746329 843745 := bbase (se 2 (by rfl) ⟨316404, by rfl⟩ : syracuseStep 843745 = 632809) (by norm_num)
theorem B843781 : Blo 746329 843781 := bbase (se 4 (by rfl) ⟨79104, by rfl⟩ : syracuseStep 843781 = 158209) (by norm_num)
theorem B1925141 : Blo 746329 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B843817 : Blo 746329 843817 := bbase (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) (by norm_num)
theorem B843853 : Blo 746329 843853 := bbase (se 3 (by rfl) ⟨158222, by rfl⟩ : syracuseStep 843853 = 316445) (by norm_num)
theorem B843889 : Blo 746329 843889 := bbase (se 2 (by rfl) ⟨316458, by rfl⟩ : syracuseStep 843889 = 632917) (by norm_num)
theorem B843925 : Blo 746329 843925 := bbase (se 6 (by rfl) ⟨19779, by rfl⟩ : syracuseStep 843925 = 39559) (by norm_num)
theorem B1794221 : Blo 746329 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B843961 : Blo 746329 843961 := bbase (se 2 (by rfl) ⟨316485, by rfl⟩ : syracuseStep 843961 = 632971) (by norm_num)
theorem B843997 : Blo 746329 843997 := bbase (se 3 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 843997 = 316499) (by norm_num)
theorem B1892605 : Blo 746329 1892605 := bbase (se 3 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 1892605 = 709727) (by norm_num)
theorem B844033 : Blo 746329 844033 := bbase (se 2 (by rfl) ⟨316512, by rfl⟩ : syracuseStep 844033 = 633025) (by norm_num)
theorem B844069 : Blo 746329 844069 := bbase (se 4 (by rfl) ⟨79131, by rfl⟩ : syracuseStep 844069 = 158263) (by norm_num)
theorem B844105 : Blo 746329 844105 := bbase (se 2 (by rfl) ⟨316539, by rfl⟩ : syracuseStep 844105 = 633079) (by norm_num)
theorem B1892717 : Blo 746329 1892717 := bbase (se 3 (by rfl) ⟨354884, by rfl⟩ : syracuseStep 1892717 = 709769) (by norm_num)
theorem B1892909 : Blo 746329 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B2843221 : Blo 746329 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B8086229 : Blo 746329 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B811901 : Blo 746329 811901 := bbase (se 3 (by rfl) ⟨152231, by rfl⟩ : syracuseStep 811901 = 304463) (by norm_num)
theorem B1893253 : Blo 746329 1893253 := bbase (se 4 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 1893253 = 354985) (by norm_num)
theorem B2843525 : Blo 746329 2843525 := bbase (se 4 (by rfl) ⟨266580, by rfl⟩ : syracuseStep 2843525 = 533161) (by norm_num)
theorem B3597205 : Blo 746329 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B3793877 : Blo 746329 3793877 := bbase (se 7 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 3793877 = 88919) (by norm_num)
theorem B1893365 : Blo 746329 1893365 := bbase (se 5 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 1893365 = 177503) (by norm_num)
theorem B910369 : Blo 746329 910369 := bbase (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) (by norm_num)
theorem B1598629 : Blo 746329 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B1893557 : Blo 746329 1893557 := bbase (se 5 (by rfl) ⟨88760, by rfl⟩ : syracuseStep 1893557 = 177521) (by norm_num)
theorem B28697813 : Blo 746329 28697813 := bbase (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) (by norm_num)
theorem B2024693 : Blo 746329 2024693 := bbase (se 5 (by rfl) ⟨94907, by rfl⟩ : syracuseStep 2024693 = 189815) (by norm_num)
theorem B1795421 : Blo 746329 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B3237317 : Blo 746329 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B1893901 : Blo 746329 1893901 := bbase (se 3 (by rfl) ⟨355106, by rfl⟩ : syracuseStep 1893901 = 710213) (by norm_num)
theorem B1894013 : Blo 746329 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B1894205 : Blo 746329 1894205 := bbase (se 3 (by rfl) ⟨355163, by rfl⟩ : syracuseStep 1894205 = 710327) (by norm_num)
theorem B1140709 : Blo 746329 1140709 := bbase (se 4 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 1140709 = 213883) (by norm_num)
theorem B1599517 : Blo 746329 1599517 := bbase (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) (by norm_num)
theorem B1009741 : Blo 746329 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B1534069 : Blo 746329 1534069 := bbase (se 5 (by rfl) ⟨71909, by rfl⟩ : syracuseStep 1534069 = 143819) (by norm_num)
theorem B1894549 : Blo 746329 1894549 := bbase (se 6 (by rfl) ⟨44403, by rfl⟩ : syracuseStep 1894549 = 88807) (by norm_num)
theorem B3795173 : Blo 746329 3795173 := bbase (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) (by norm_num)
theorem B1894661 : Blo 746329 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1894853 : Blo 746329 1894853 := bbase (se 4 (by rfl) ⟨177642, by rfl⟩ : syracuseStep 1894853 = 355285) (by norm_num)
theorem B944617 : Blo 746329 944617 := bbase (se 2 (by rfl) ⟨354231, by rfl⟩ : syracuseStep 944617 = 708463) (by norm_num)
theorem B1600013 : Blo 746329 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1436221 : Blo 746329 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B944713 : Blo 746329 944713 := bbase (se 2 (by rfl) ⟨354267, by rfl⟩ : syracuseStep 944713 = 708535) (by norm_num)
theorem B1108669 : Blo 746329 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B944885 : Blo 746329 944885 := bbase (se 5 (by rfl) ⟨44291, by rfl⟩ : syracuseStep 944885 = 88583) (by norm_num)
theorem B1895197 : Blo 746329 1895197 := bbase (se 3 (by rfl) ⟨355349, by rfl⟩ : syracuseStep 1895197 = 710699) (by norm_num)
theorem B944941 : Blo 746329 944941 := bbase (se 3 (by rfl) ⟨177176, by rfl⟩ : syracuseStep 944941 = 354353) (by norm_num)
theorem B6810421 : Blo 746329 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B945037 : Blo 746329 945037 := bbase (se 3 (by rfl) ⟨177194, by rfl⟩ : syracuseStep 945037 = 354389) (by norm_num)
theorem B1895309 : Blo 746329 1895309 := bbase (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) (by norm_num)
theorem B5696405 : Blo 746329 5696405 := bbase (se 6 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 5696405 = 267019) (by norm_num)
theorem B2845637 : Blo 746329 2845637 := bbase (se 4 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 2845637 = 533557) (by norm_num)
theorem B1534997 : Blo 746329 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B945209 : Blo 746329 945209 := bbase (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) (by norm_num)
theorem B1895501 : Blo 746329 1895501 := bbase (se 3 (by rfl) ⟨355406, by rfl⟩ : syracuseStep 1895501 = 710813) (by norm_num)
theorem B945265 : Blo 746329 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B1141933 : Blo 746329 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B945361 : Blo 746329 945361 := bbase (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) (by norm_num)
theorem B2845925 : Blo 746329 2845925 := bbase (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) (by norm_num)
theorem B1600877 : Blo 746329 1600877 := bbase (se 3 (by rfl) ⟨300164, by rfl⟩ : syracuseStep 1600877 = 600329) (by norm_num)
theorem B945533 : Blo 746329 945533 := bbase (se 3 (by rfl) ⟨177287, by rfl⟩ : syracuseStep 945533 = 354575) (by norm_num)
theorem B1895845 : Blo 746329 1895845 := bbase (se 4 (by rfl) ⟨177735, by rfl⟩ : syracuseStep 1895845 = 355471) (by norm_num)
theorem B945589 : Blo 746329 945589 := bbase (se 5 (by rfl) ⟨44324, by rfl⟩ : syracuseStep 945589 = 88649) (by norm_num)
theorem B3796469 : Blo 746329 3796469 := bbase (se 5 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 3796469 = 355919) (by norm_num)
theorem B1601021 : Blo 746329 1601021 := bbase (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) (by norm_num)
theorem B945685 : Blo 746329 945685 := bbase (se 6 (by rfl) ⟨22164, by rfl⟩ : syracuseStep 945685 = 44329) (by norm_num)
theorem B1895957 : Blo 746329 1895957 := bbase (se 6 (by rfl) ⟨44436, by rfl⟩ : syracuseStep 1895957 = 88873) (by norm_num)
theorem B1797709 : Blo 746329 1797709 := bbase (se 3 (by rfl) ⟨337070, by rfl⟩ : syracuseStep 1797709 = 674141) (by norm_num)
theorem B1797805 : Blo 746329 1797805 := bbase (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) (by norm_num)
theorem B945857 : Blo 746329 945857 := bbase (se 2 (by rfl) ⟨354696, by rfl⟩ : syracuseStep 945857 = 709393) (by norm_num)
theorem B1896149 : Blo 746329 1896149 := bbase (se 7 (by rfl) ⟨22220, by rfl⟩ : syracuseStep 1896149 = 44441) (by norm_num)
theorem B945913 : Blo 746329 945913 := bbase (se 2 (by rfl) ⟨354717, by rfl⟩ : syracuseStep 945913 = 709435) (by norm_num)
theorem B6385493 : Blo 746329 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B946009 : Blo 746329 946009 := bbase (se 2 (by rfl) ⟨354753, by rfl⟩ : syracuseStep 946009 = 709507) (by norm_num)
theorem B1797997 : Blo 746329 1797997 := bbase (se 3 (by rfl) ⟨337124, by rfl⟩ : syracuseStep 1797997 = 674249) (by norm_num)
theorem B1437677 : Blo 746329 1437677 := bbase (se 3 (by rfl) ⟨269564, by rfl⟩ : syracuseStep 1437677 = 539129) (by norm_num)
theorem B2519045 : Blo 746329 2519045 := bbase (se 4 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 2519045 = 472321) (by norm_num)
theorem B946181 : Blo 746329 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B1896493 : Blo 746329 1896493 := bbase (se 3 (by rfl) ⟨355592, by rfl⟩ : syracuseStep 1896493 = 711185) (by norm_num)
theorem B946237 : Blo 746329 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B946333 : Blo 746329 946333 := bbase (se 3 (by rfl) ⟨177437, by rfl⟩ : syracuseStep 946333 = 354875) (by norm_num)
theorem B1896605 : Blo 746329 1896605 := bbase (se 3 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 1896605 = 711227) (by norm_num)
theorem B1798325 : Blo 746329 1798325 := bbase (se 5 (by rfl) ⟨84296, by rfl⟩ : syracuseStep 1798325 = 168593) (by norm_num)
theorem B1601765 : Blo 746329 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B946505 : Blo 746329 946505 := bbase (se 2 (by rfl) ⟨354939, by rfl⟩ : syracuseStep 946505 = 709879) (by norm_num)
theorem B1896797 : Blo 746329 1896797 := bbase (se 3 (by rfl) ⟨355649, by rfl⟩ : syracuseStep 1896797 = 711299) (by norm_num)
theorem B946561 : Blo 746329 946561 := bbase (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) (by norm_num)
theorem B2847109 : Blo 746329 2847109 := bbase (se 4 (by rfl) ⟨266916, by rfl⟩ : syracuseStep 2847109 = 533833) (by norm_num)
theorem B2519477 : Blo 746329 2519477 := bbase (se 5 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 2519477 = 236201) (by norm_num)
theorem B946657 : Blo 746329 946657 := bbase (se 2 (by rfl) ⟨354996, by rfl⟩ : syracuseStep 946657 = 709993) (by norm_num)
theorem B2126357 : Blo 746329 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B1798757 : Blo 746329 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B946829 : Blo 746329 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B1897141 : Blo 746329 1897141 := bbase (se 5 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 1897141 = 177857) (by norm_num)
theorem B2847413 : Blo 746329 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B946885 : Blo 746329 946885 := bbase (se 4 (by rfl) ⟨88770, by rfl⟩ : syracuseStep 946885 = 177541) (by norm_num)
theorem B3797765 : Blo 746329 3797765 := bbase (se 4 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 3797765 = 712081) (by norm_num)
theorem B946981 : Blo 746329 946981 := bbase (se 4 (by rfl) ⟨88779, by rfl⟩ : syracuseStep 946981 = 177559) (by norm_num)
theorem B1897253 : Blo 746329 1897253 := bbase (se 4 (by rfl) ⟨177867, by rfl⟩ : syracuseStep 1897253 = 355735) (by norm_num)
theorem B3601205 : Blo 746329 3601205 := bbase (se 5 (by rfl) ⟨168806, by rfl⟩ : syracuseStep 3601205 = 337613) (by norm_num)
theorem B2519909 : Blo 746329 2519909 := bbase (se 4 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 2519909 = 472483) (by norm_num)
theorem B5403509 : Blo 746329 5403509 := bbase (se 5 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 5403509 = 506579) (by norm_num)
theorem B1799093 : Blo 746329 1799093 := bbase (se 5 (by rfl) ⟨84332, by rfl⟩ : syracuseStep 1799093 = 168665) (by norm_num)
theorem B1438661 : Blo 746329 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B947153 : Blo 746329 947153 := bbase (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) (by norm_num)
theorem B1897445 : Blo 746329 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B947209 : Blo 746329 947209 := bbase (se 2 (by rfl) ⟨355203, by rfl⟩ : syracuseStep 947209 = 710407) (by norm_num)
theorem B947305 : Blo 746329 947305 := bbase (se 2 (by rfl) ⟨355239, by rfl⟩ : syracuseStep 947305 = 710479) (by norm_num)
theorem B1537165 : Blo 746329 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B2520341 : Blo 746329 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B947477 : Blo 746329 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B1897789 : Blo 746329 1897789 := bbase (se 3 (by rfl) ⟨355835, by rfl⟩ : syracuseStep 1897789 = 711671) (by norm_num)
theorem B2159941 : Blo 746329 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B947533 : Blo 746329 947533 := bbase (se 3 (by rfl) ⟨177662, by rfl⟩ : syracuseStep 947533 = 355325) (by norm_num)
theorem B947629 : Blo 746329 947629 := bbase (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) (by norm_num)
theorem B1897901 : Blo 746329 1897901 := bbase (se 3 (by rfl) ⟨355856, by rfl⟩ : syracuseStep 1897901 = 711713) (by norm_num)
theorem B4257269 : Blo 746329 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B947801 : Blo 746329 947801 := bbase (se 2 (by rfl) ⟨355425, by rfl⟩ : syracuseStep 947801 = 710851) (by norm_num)
theorem B1898093 : Blo 746329 1898093 := bbase (se 3 (by rfl) ⟨355892, by rfl⟩ : syracuseStep 1898093 = 711785) (by norm_num)
theorem B947857 : Blo 746329 947857 := bbase (se 2 (by rfl) ⟨355446, by rfl⟩ : syracuseStep 947857 = 710893) (by norm_num)
theorem B2127541 : Blo 746329 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B2520773 : Blo 746329 2520773 := bbase (se 4 (by rfl) ⟨236322, by rfl⟩ : syracuseStep 2520773 = 472645) (by norm_num)
theorem B947953 : Blo 746329 947953 := bbase (se 2 (by rfl) ⟨355482, by rfl⟩ : syracuseStep 947953 = 710965) (by norm_num)
theorem B2127701 : Blo 746329 2127701 := bbase (se 9 (by rfl) ⟨6233, by rfl⟩ : syracuseStep 2127701 = 12467) (by norm_num)
theorem B948125 : Blo 746329 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B1898437 : Blo 746329 1898437 := bbase (se 4 (by rfl) ⟨177978, by rfl⟩ : syracuseStep 1898437 = 355957) (by norm_num)
theorem B948181 : Blo 746329 948181 := bbase (se 7 (by rfl) ⟨11111, by rfl⟩ : syracuseStep 948181 = 22223) (by norm_num)
theorem B1800149 : Blo 746329 1800149 := bbase (se 7 (by rfl) ⟨21095, by rfl⟩ : syracuseStep 1800149 = 42191) (by norm_num)
theorem B3405797 : Blo 746329 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B948277 : Blo 746329 948277 := bbase (se 5 (by rfl) ⟨44450, by rfl⟩ : syracuseStep 948277 = 88901) (by norm_num)
theorem B1898549 : Blo 746329 1898549 := bbase (se 5 (by rfl) ⟨88994, by rfl⟩ : syracuseStep 1898549 = 177989) (by norm_num)
theorem B2127941 : Blo 746329 2127941 := bbase (se 4 (by rfl) ⟨199494, by rfl⟩ : syracuseStep 2127941 = 398989) (by norm_num)
theorem B2521205 : Blo 746329 2521205 := bbase (se 5 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 2521205 = 236363) (by norm_num)
theorem B2160773 : Blo 746329 2160773 := bbase (se 4 (by rfl) ⟨202572, by rfl⟩ : syracuseStep 2160773 = 405145) (by norm_num)
theorem B948449 : Blo 746329 948449 := bbase (se 2 (by rfl) ⟨355668, by rfl⟩ : syracuseStep 948449 = 711337) (by norm_num)
theorem B1898741 : Blo 746329 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B2128133 : Blo 746329 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B948505 : Blo 746329 948505 := bbase (se 2 (by rfl) ⟨355689, by rfl⟩ : syracuseStep 948505 = 711379) (by norm_num)
theorem B2881829 : Blo 746329 2881829 := bbase (se 4 (by rfl) ⟨270171, by rfl⟩ : syracuseStep 2881829 = 540343) (by norm_num)
theorem B948601 : Blo 746329 948601 := bbase (se 2 (by rfl) ⟨355725, by rfl⟩ : syracuseStep 948601 = 711451) (by norm_num)
theorem B2521637 : Blo 746329 2521637 := bbase (se 4 (by rfl) ⟨236403, by rfl⟩ : syracuseStep 2521637 = 472807) (by norm_num)
theorem B948773 : Blo 746329 948773 := bbase (se 4 (by rfl) ⟨88947, by rfl⟩ : syracuseStep 948773 = 177895) (by norm_num)
theorem B1899085 : Blo 746329 1899085 := bbase (se 3 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 1899085 = 712157) (by norm_num)
theorem B948829 : Blo 746329 948829 := bbase (se 3 (by rfl) ⟨177905, by rfl⟩ : syracuseStep 948829 = 355811) (by norm_num)
theorem B4258453 : Blo 746329 4258453 := bbase (se 6 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 4258453 = 199615) (by norm_num)
theorem B948925 : Blo 746329 948925 := bbase (se 3 (by rfl) ⟨177923, by rfl⟩ : syracuseStep 948925 = 355847) (by norm_num)
theorem B1899197 : Blo 746329 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B6388469 : Blo 746329 6388469 := bbase (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) (by norm_num)
theorem B949097 : Blo 746329 949097 := bbase (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) (by norm_num)
theorem B949153 : Blo 746329 949153 := bbase (se 2 (by rfl) ⟨355932, by rfl⟩ : syracuseStep 949153 = 711865) (by norm_num)
theorem B2522069 : Blo 746329 2522069 := bbase (se 7 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 2522069 = 59111) (by norm_num)
theorem B949249 : Blo 746329 949249 := bbase (se 2 (by rfl) ⟨355968, by rfl⟩ : syracuseStep 949249 = 711937) (by norm_num)
theorem B949421 : Blo 746329 949421 := bbase (se 3 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 949421 = 356033) (by norm_num)
theorem B2129125 : Blo 746329 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B949477 : Blo 746329 949477 := bbase (se 4 (by rfl) ⟨89013, by rfl⟩ : syracuseStep 949477 = 178027) (by norm_num)
theorem B949573 : Blo 746329 949573 := bbase (se 4 (by rfl) ⟨89022, by rfl⟩ : syracuseStep 949573 = 178045) (by norm_num)
theorem B2522501 : Blo 746329 2522501 := bbase (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) (by norm_num)
theorem B1539533 : Blo 746329 1539533 := bbase (se 3 (by rfl) ⟨288662, by rfl⟩ : syracuseStep 1539533 = 577325) (by norm_num)
theorem B851413 : Blo 746329 851413 := bbase (se 7 (by rfl) ⟨9977, by rfl⟩ : syracuseStep 851413 = 19955) (by norm_num)
theorem B4783637 : Blo 746329 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B3603989 : Blo 746329 3603989 := bbase (se 6 (by rfl) ⟨84468, by rfl⟩ : syracuseStep 3603989 = 168937) (by norm_num)
theorem B851677 : Blo 746329 851677 := bbase (se 3 (by rfl) ⟨159689, by rfl⟩ : syracuseStep 851677 = 319379) (by norm_num)
theorem B2391781 : Blo 746329 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B2522933 : Blo 746329 2522933 := bbase (se 5 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 2522933 = 236525) (by norm_num)
theorem B851833 : Blo 746329 851833 := bbase (se 2 (by rfl) ⟨319437, by rfl⟩ : syracuseStep 851833 = 638875) (by norm_num)
theorem B2523149 : Blo 746329 2523149 := bstep (se 3 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 2523149 = 946181) B946181
theorem B2523203 : Blo 746329 2523203 := bstep (se 1 (by rfl) ⟨1892402, by rfl⟩ : syracuseStep 2523203 = 3784805) B3784805
theorem B5669189 : Blo 746329 5669189 := bstep (se 4 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 5669189 = 1062973) B1062973
theorem B2523473 : Blo 746329 2523473 := bstep (se 2 (by rfl) ⟨946302, by rfl⟩ : syracuseStep 2523473 = 1892605) B1892605
theorem B2130275 : Blo 746329 2130275 := bstep (se 1 (by rfl) ⟨1597706, by rfl⟩ : syracuseStep 2130275 = 3195413) B3195413
theorem B1278433 : Blo 746329 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B14615153 : Blo 746329 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B6062789 : Blo 746329 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B3605219 : Blo 746329 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B2589475 : Blo 746329 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B2524013 : Blo 746329 2524013 := bstep (se 3 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 2524013 = 946505) B946505
theorem B2392973 : Blo 746329 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B2524067 : Blo 746329 2524067 := bstep (se 1 (by rfl) ⟨1893050, by rfl⟩ : syracuseStep 2524067 = 3786101) B3786101
theorem B7177187 : Blo 746329 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B4260869 : Blo 746329 4260869 := bstep (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) B798913
theorem B2524337 : Blo 746329 2524337 := bstep (se 2 (by rfl) ⟨946626, by rfl⟩ : syracuseStep 2524337 = 1893253) B1893253
theorem B5932259 : Blo 746329 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B16647565 : Blo 746329 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B4785635 : Blo 746329 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B2131505 : Blo 746329 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B4687409 : Blo 746329 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B2524877 : Blo 746329 2524877 := bstep (se 3 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 2524877 = 946829) B946829
theorem B2524931 : Blo 746329 2524931 := bstep (se 1 (by rfl) ⟨1893698, by rfl⟩ : syracuseStep 2524931 = 3787397) B3787397
theorem B2393869 : Blo 746329 2393869 := bstep (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) B897701
theorem B2525201 : Blo 746329 2525201 := bstep (se 2 (by rfl) ⟨946950, by rfl⟩ : syracuseStep 2525201 = 1893901) B1893901
theorem B2165069 : Blo 746329 2165069 := bstep (se 3 (by rfl) ⟨405950, by rfl⟩ : syracuseStep 2165069 = 811901) B811901
theorem B3836429 : Blo 746329 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B2525741 : Blo 746329 2525741 := bstep (se 3 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 2525741 = 947153) B947153
theorem B2525795 : Blo 746329 2525795 := bstep (se 1 (by rfl) ⟨1894346, by rfl⟩ : syracuseStep 2525795 = 3788693) B3788693
theorem B2394755 : Blo 746329 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B6163141 : Blo 746329 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B1346321 : Blo 746329 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B2526065 : Blo 746329 2526065 := bstep (se 2 (by rfl) ⟨947274, by rfl⟩ : syracuseStep 2526065 = 1894549) B1894549
theorem B2558893 : Blo 746329 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B2132963 : Blo 746329 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B855043 : Blo 746329 855043 := bstep (se 1 (by rfl) ⟨641282, by rfl⟩ : syracuseStep 855043 = 1282565) B1282565
theorem B8096867 : Blo 746329 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B2526605 : Blo 746329 2526605 := bstep (se 3 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 2526605 = 947477) B947477
theorem B2526659 : Blo 746329 2526659 := bstep (se 1 (by rfl) ⟨1894994, by rfl⟩ : syracuseStep 2526659 = 3789989) B3789989
theorem B1478225 : Blo 746329 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B2526929 : Blo 746329 2526929 := bstep (se 2 (by rfl) ⟨947598, by rfl⟩ : syracuseStep 2526929 = 1895197) B1895197
theorem B9080561 : Blo 746329 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B2133773 : Blo 746329 2133773 := bstep (se 3 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 2133773 = 800165) B800165
theorem B2133965 : Blo 746329 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B2592749 : Blo 746329 2592749 := bstep (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) B972281
theorem B6230029 : Blo 746329 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B757955 : Blo 746329 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B2527469 : Blo 746329 2527469 := bstep (se 3 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 2527469 = 947801) B947801
theorem B2527523 : Blo 746329 2527523 := bstep (se 1 (by rfl) ⟨1895642, by rfl⟩ : syracuseStep 2527523 = 3791285) B3791285
theorem B2527793 : Blo 746329 2527793 := bstep (se 2 (by rfl) ⟨947922, by rfl⟩ : syracuseStep 2527793 = 1895845) B1895845
theorem B7180913 : Blo 746329 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B8622773 : Blo 746329 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B2396945 : Blo 746329 2396945 := bstep (se 2 (by rfl) ⟨898854, by rfl⟩ : syracuseStep 2396945 = 1797709) B1797709
theorem B758627 : Blo 746329 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B2397073 : Blo 746329 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B2134957 : Blo 746329 2134957 := bstep (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) B800609
theorem B1348643 : Blo 746329 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B2528333 : Blo 746329 2528333 := bstep (se 3 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 2528333 = 948125) B948125
theorem B2528387 : Blo 746329 2528387 := bstep (se 1 (by rfl) ⟨1896290, by rfl⟩ : syracuseStep 2528387 = 3792581) B3792581
theorem B2397329 : Blo 746329 2397329 := bstep (se 2 (by rfl) ⟨898998, by rfl⟩ : syracuseStep 2397329 = 1797997) B1797997
theorem B1283249 : Blo 746329 1283249 := bstep (se 2 (by rfl) ⟨481218, by rfl⟩ : syracuseStep 1283249 = 962437) B962437
theorem B1119521 : Blo 746329 1119521 := bstep (se 2 (by rfl) ⟨419820, by rfl⟩ : syracuseStep 1119521 = 839641) B839641
theorem B1119539 : Blo 746329 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B1119569 : Blo 746329 1119569 := bstep (se 2 (by rfl) ⟨419838, by rfl⟩ : syracuseStep 1119569 = 839677) B839677
theorem B1119587 : Blo 746329 1119587 := bstep (se 1 (by rfl) ⟨839690, by rfl⟩ : syracuseStep 1119587 = 1679381) B1679381
theorem B1119617 : Blo 746329 1119617 := bstep (se 2 (by rfl) ⟨419856, by rfl⟩ : syracuseStep 1119617 = 839713) B839713
theorem B2528657 : Blo 746329 2528657 := bstep (se 2 (by rfl) ⟨948246, by rfl⟩ : syracuseStep 2528657 = 1896493) B1896493
theorem B1119635 : Blo 746329 1119635 := bstep (se 1 (by rfl) ⟨839726, by rfl⟩ : syracuseStep 1119635 = 1679453) B1679453
theorem B1119665 : Blo 746329 1119665 := bstep (se 2 (by rfl) ⟨419874, by rfl⟩ : syracuseStep 1119665 = 839749) B839749
theorem B4560305 : Blo 746329 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B1119683 : Blo 746329 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B1119713 : Blo 746329 1119713 := bstep (se 2 (by rfl) ⟨419892, by rfl⟩ : syracuseStep 1119713 = 839785) B839785
theorem B1119731 : Blo 746329 1119731 := bstep (se 1 (by rfl) ⟨839798, by rfl⟩ : syracuseStep 1119731 = 1679597) B1679597
theorem B4855301 : Blo 746329 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B1119761 : Blo 746329 1119761 := bstep (se 2 (by rfl) ⟨419910, by rfl⟩ : syracuseStep 1119761 = 839821) B839821
theorem B1119779 : Blo 746329 1119779 := bstep (se 1 (by rfl) ⟨839834, by rfl⟩ : syracuseStep 1119779 = 1679669) B1679669
theorem B1119809 : Blo 746329 1119809 := bstep (se 2 (by rfl) ⟨419928, by rfl⟩ : syracuseStep 1119809 = 839857) B839857
theorem B1119827 : Blo 746329 1119827 := bstep (se 1 (by rfl) ⟨839870, by rfl⟩ : syracuseStep 1119827 = 1679741) B1679741
theorem B1119857 : Blo 746329 1119857 := bstep (se 2 (by rfl) ⟨419946, by rfl⟩ : syracuseStep 1119857 = 839893) B839893
theorem B1119875 : Blo 746329 1119875 := bstep (se 1 (by rfl) ⟨839906, by rfl⟩ : syracuseStep 1119875 = 1679813) B1679813
theorem B1119905 : Blo 746329 1119905 := bstep (se 2 (by rfl) ⟨419964, by rfl⟩ : syracuseStep 1119905 = 839929) B839929
theorem B1119923 : Blo 746329 1119923 := bstep (se 1 (by rfl) ⟨839942, by rfl⟩ : syracuseStep 1119923 = 1679885) B1679885
theorem B1119953 : Blo 746329 1119953 := bstep (se 2 (by rfl) ⟨419982, by rfl⟩ : syracuseStep 1119953 = 839965) B839965
theorem B1119971 : Blo 746329 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B1709795 : Blo 746329 1709795 := bstep (se 1 (by rfl) ⟨1282346, by rfl⟩ : syracuseStep 1709795 = 2564693) B2564693
theorem B1120001 : Blo 746329 1120001 := bstep (se 2 (by rfl) ⟨420000, by rfl⟩ : syracuseStep 1120001 = 840001) B840001
theorem B1120019 : Blo 746329 1120019 := bstep (se 1 (by rfl) ⟨840014, by rfl⟩ : syracuseStep 1120019 = 1680029) B1680029
theorem B1120049 : Blo 746329 1120049 := bstep (se 2 (by rfl) ⟨420018, by rfl⟩ : syracuseStep 1120049 = 840037) B840037
theorem B1120067 : Blo 746329 1120067 := bstep (se 1 (by rfl) ⟨840050, by rfl⟩ : syracuseStep 1120067 = 1680101) B1680101
theorem B1120097 : Blo 746329 1120097 := bstep (se 2 (by rfl) ⟨420036, by rfl⟩ : syracuseStep 1120097 = 840073) B840073
theorem B1709923 : Blo 746329 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B1120115 : Blo 746329 1120115 := bstep (se 1 (by rfl) ⟨840086, by rfl⟩ : syracuseStep 1120115 = 1680173) B1680173
theorem B1120145 : Blo 746329 1120145 := bstep (se 2 (by rfl) ⟨420054, by rfl⟩ : syracuseStep 1120145 = 840109) B840109
theorem B1120163 : Blo 746329 1120163 := bstep (se 1 (by rfl) ⟨840122, by rfl⟩ : syracuseStep 1120163 = 1680245) B1680245
theorem B2529197 : Blo 746329 2529197 := bstep (se 3 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 2529197 = 948449) B948449
theorem B1120193 : Blo 746329 1120193 := bstep (se 2 (by rfl) ⟨420072, by rfl⟩ : syracuseStep 1120193 = 840145) B840145
theorem B1120211 : Blo 746329 1120211 := bstep (se 1 (by rfl) ⟨840158, by rfl⟩ : syracuseStep 1120211 = 1680317) B1680317
theorem B2529251 : Blo 746329 2529251 := bstep (se 1 (by rfl) ⟨1896938, by rfl⟩ : syracuseStep 2529251 = 3793877) B3793877
theorem B1120241 : Blo 746329 1120241 := bstep (se 2 (by rfl) ⟨420090, by rfl⟩ : syracuseStep 1120241 = 840181) B840181
theorem B1120259 : Blo 746329 1120259 := bstep (se 1 (by rfl) ⟨840194, by rfl⟩ : syracuseStep 1120259 = 1680389) B1680389
theorem B5675021 : Blo 746329 5675021 := bstep (se 3 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 5675021 = 2128133) B2128133
theorem B1120289 : Blo 746329 1120289 := bstep (se 2 (by rfl) ⟨420108, by rfl⟩ : syracuseStep 1120289 = 840217) B840217
theorem B1153073 : Blo 746329 1153073 := bstep (se 2 (by rfl) ⟨432402, by rfl⟩ : syracuseStep 1153073 = 864805) B864805
theorem B1120307 : Blo 746329 1120307 := bstep (se 1 (by rfl) ⟨840230, by rfl⟩ : syracuseStep 1120307 = 1680461) B1680461
theorem B8198213 : Blo 746329 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B1120337 : Blo 746329 1120337 := bstep (se 2 (by rfl) ⟨420126, by rfl⟩ : syracuseStep 1120337 = 840253) B840253
theorem B1120355 : Blo 746329 1120355 := bstep (se 1 (by rfl) ⟨840266, by rfl⟩ : syracuseStep 1120355 = 1680533) B1680533
theorem B1120385 : Blo 746329 1120385 := bstep (se 2 (by rfl) ⟨420144, by rfl⟩ : syracuseStep 1120385 = 840289) B840289
theorem B1120403 : Blo 746329 1120403 := bstep (se 1 (by rfl) ⟨840302, by rfl⟩ : syracuseStep 1120403 = 1680605) B1680605
theorem B1349795 : Blo 746329 1349795 := bstep (se 1 (by rfl) ⟨1012346, by rfl⟩ : syracuseStep 1349795 = 2024693) B2024693
theorem B1120433 : Blo 746329 1120433 := bstep (se 2 (by rfl) ⟨420162, by rfl⟩ : syracuseStep 1120433 = 840325) B840325
theorem B1120451 : Blo 746329 1120451 := bstep (se 1 (by rfl) ⟨840338, by rfl⟩ : syracuseStep 1120451 = 1680677) B1680677
theorem B1120481 : Blo 746329 1120481 := bstep (se 2 (by rfl) ⟨420180, by rfl⟩ : syracuseStep 1120481 = 840361) B840361
theorem B2529521 : Blo 746329 2529521 := bstep (se 2 (by rfl) ⟨948570, by rfl⟩ : syracuseStep 2529521 = 1897141) B1897141
theorem B1120499 : Blo 746329 1120499 := bstep (se 1 (by rfl) ⟨840374, by rfl⟩ : syracuseStep 1120499 = 1680749) B1680749
theorem B1120529 : Blo 746329 1120529 := bstep (se 2 (by rfl) ⟨420198, by rfl⟩ : syracuseStep 1120529 = 840397) B840397
theorem B1120547 : Blo 746329 1120547 := bstep (se 1 (by rfl) ⟨840410, by rfl⟩ : syracuseStep 1120547 = 1680821) B1680821
theorem B1120577 : Blo 746329 1120577 := bstep (se 2 (by rfl) ⟨420216, by rfl⟩ : syracuseStep 1120577 = 840433) B840433
theorem B2431313 : Blo 746329 2431313 := bstep (se 2 (by rfl) ⟨911742, by rfl⟩ : syracuseStep 2431313 = 1823485) B1823485
theorem B1120595 : Blo 746329 1120595 := bstep (se 1 (by rfl) ⟨840446, by rfl⟩ : syracuseStep 1120595 = 1680893) B1680893
theorem B1120625 : Blo 746329 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B1120643 : Blo 746329 1120643 := bstep (se 1 (by rfl) ⟨840482, by rfl⟩ : syracuseStep 1120643 = 1680965) B1680965
theorem B1120673 : Blo 746329 1120673 := bstep (se 2 (by rfl) ⟨420252, by rfl⟩ : syracuseStep 1120673 = 840505) B840505
theorem B1120691 : Blo 746329 1120691 := bstep (se 1 (by rfl) ⟨840518, by rfl⟩ : syracuseStep 1120691 = 1681037) B1681037
theorem B1120721 : Blo 746329 1120721 := bstep (se 2 (by rfl) ⟨420270, by rfl⟩ : syracuseStep 1120721 = 840541) B840541
theorem B1120739 : Blo 746329 1120739 := bstep (se 1 (by rfl) ⟨840554, by rfl⟩ : syracuseStep 1120739 = 1681109) B1681109
theorem B2103779 : Blo 746329 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B1120769 : Blo 746329 1120769 := bstep (se 2 (by rfl) ⟨420288, by rfl⟩ : syracuseStep 1120769 = 840577) B840577
theorem B1120787 : Blo 746329 1120787 := bstep (se 1 (by rfl) ⟨840590, by rfl⟩ : syracuseStep 1120787 = 1681181) B1681181
theorem B1120817 : Blo 746329 1120817 := bstep (se 2 (by rfl) ⟨420306, by rfl⟩ : syracuseStep 1120817 = 840613) B840613
theorem B1120835 : Blo 746329 1120835 := bstep (se 1 (by rfl) ⟨840626, by rfl⟩ : syracuseStep 1120835 = 1681253) B1681253
theorem B1120865 : Blo 746329 1120865 := bstep (se 2 (by rfl) ⟨420324, by rfl⟩ : syracuseStep 1120865 = 840649) B840649
theorem B1120883 : Blo 746329 1120883 := bstep (se 1 (by rfl) ⟨840662, by rfl⟩ : syracuseStep 1120883 = 1681325) B1681325
theorem B1120913 : Blo 746329 1120913 := bstep (se 2 (by rfl) ⟨420342, by rfl⟩ : syracuseStep 1120913 = 840685) B840685
theorem B1120931 : Blo 746329 1120931 := bstep (se 1 (by rfl) ⟨840698, by rfl⟩ : syracuseStep 1120931 = 1681397) B1681397
theorem B1120961 : Blo 746329 1120961 := bstep (se 2 (by rfl) ⟨420360, by rfl⟩ : syracuseStep 1120961 = 840721) B840721
theorem B4266701 : Blo 746329 4266701 := bstep (se 3 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 4266701 = 1600013) B1600013
theorem B1120979 : Blo 746329 1120979 := bstep (se 1 (by rfl) ⟨840734, by rfl⟩ : syracuseStep 1120979 = 1681469) B1681469
theorem B1121009 : Blo 746329 1121009 := bstep (se 2 (by rfl) ⟨420378, by rfl⟩ : syracuseStep 1121009 = 840757) B840757
theorem B1121027 : Blo 746329 1121027 := bstep (se 1 (by rfl) ⟨840770, by rfl⟩ : syracuseStep 1121027 = 1681541) B1681541
theorem B2530061 : Blo 746329 2530061 := bstep (se 3 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 2530061 = 948773) B948773
theorem B1121057 : Blo 746329 1121057 := bstep (se 2 (by rfl) ⟨420396, by rfl⟩ : syracuseStep 1121057 = 840793) B840793
theorem B2399021 : Blo 746329 2399021 := bstep (se 3 (by rfl) ⟨449816, by rfl⟩ : syracuseStep 2399021 = 899633) B899633
theorem B1121075 : Blo 746329 1121075 := bstep (se 1 (by rfl) ⟨840806, by rfl⟩ : syracuseStep 1121075 = 1681613) B1681613
theorem B2530115 : Blo 746329 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B1121105 : Blo 746329 1121105 := bstep (se 2 (by rfl) ⟨420414, by rfl⟩ : syracuseStep 1121105 = 840829) B840829
theorem B1121123 : Blo 746329 1121123 := bstep (se 1 (by rfl) ⟨840842, by rfl⟩ : syracuseStep 1121123 = 1681685) B1681685
theorem B1121153 : Blo 746329 1121153 := bstep (se 2 (by rfl) ⟨420432, by rfl⟩ : syracuseStep 1121153 = 840865) B840865
theorem B1121171 : Blo 746329 1121171 := bstep (se 1 (by rfl) ⟨840878, by rfl⟩ : syracuseStep 1121171 = 1681757) B1681757
theorem B1121201 : Blo 746329 1121201 := bstep (se 2 (by rfl) ⟨420450, by rfl⟩ : syracuseStep 1121201 = 840901) B840901
theorem B1121219 : Blo 746329 1121219 := bstep (se 1 (by rfl) ⟨840914, by rfl⟩ : syracuseStep 1121219 = 1681829) B1681829
theorem B1121249 : Blo 746329 1121249 := bstep (se 2 (by rfl) ⟨420468, by rfl⟩ : syracuseStep 1121249 = 840937) B840937
theorem B1121267 : Blo 746329 1121267 := bstep (se 1 (by rfl) ⟨840950, by rfl⟩ : syracuseStep 1121267 = 1681901) B1681901
theorem B1121297 : Blo 746329 1121297 := bstep (se 2 (by rfl) ⟨420486, by rfl⟩ : syracuseStep 1121297 = 840973) B840973
theorem B1121315 : Blo 746329 1121315 := bstep (se 1 (by rfl) ⟨840986, by rfl⟩ : syracuseStep 1121315 = 1681973) B1681973
theorem B1121345 : Blo 746329 1121345 := bstep (se 2 (by rfl) ⟨420504, by rfl⟩ : syracuseStep 1121345 = 841009) B841009
theorem B2530385 : Blo 746329 2530385 := bstep (se 2 (by rfl) ⟨948894, by rfl⟩ : syracuseStep 2530385 = 1897789) B1897789
theorem B1121363 : Blo 746329 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B1121393 : Blo 746329 1121393 := bstep (se 2 (by rfl) ⟨420522, by rfl⟩ : syracuseStep 1121393 = 841045) B841045
theorem B1121411 : Blo 746329 1121411 := bstep (se 1 (by rfl) ⟨841058, by rfl⟩ : syracuseStep 1121411 = 1682117) B1682117
theorem B1121441 : Blo 746329 1121441 := bstep (se 2 (by rfl) ⟨420540, by rfl⟩ : syracuseStep 1121441 = 841081) B841081
theorem B1121459 : Blo 746329 1121459 := bstep (se 1 (by rfl) ⟨841094, by rfl⟩ : syracuseStep 1121459 = 1682189) B1682189
theorem B1121489 : Blo 746329 1121489 := bstep (se 2 (by rfl) ⟨420558, by rfl⟩ : syracuseStep 1121489 = 841117) B841117
theorem B1121507 : Blo 746329 1121507 := bstep (se 1 (by rfl) ⟨841130, by rfl⟩ : syracuseStep 1121507 = 1682261) B1682261
theorem B1121537 : Blo 746329 1121537 := bstep (se 2 (by rfl) ⟨420576, by rfl⟩ : syracuseStep 1121537 = 841153) B841153
theorem B1121555 : Blo 746329 1121555 := bstep (se 1 (by rfl) ⟨841166, by rfl⟩ : syracuseStep 1121555 = 1682333) B1682333
theorem B1121585 : Blo 746329 1121585 := bstep (se 2 (by rfl) ⟨420594, by rfl⟩ : syracuseStep 1121585 = 841189) B841189
theorem B1121603 : Blo 746329 1121603 := bstep (se 1 (by rfl) ⟨841202, by rfl⟩ : syracuseStep 1121603 = 1682405) B1682405
theorem B1121633 : Blo 746329 1121633 := bstep (se 2 (by rfl) ⟨420612, by rfl⟩ : syracuseStep 1121633 = 841225) B841225
theorem B1023331 : Blo 746329 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B9575779 : Blo 746329 9575779 := bstep (se 1 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 9575779 = 14363669) B14363669
theorem B1121651 : Blo 746329 1121651 := bstep (se 1 (by rfl) ⟨841238, by rfl⟩ : syracuseStep 1121651 = 1682477) B1682477
theorem B1121681 : Blo 746329 1121681 := bstep (se 2 (by rfl) ⟨420630, by rfl⟩ : syracuseStep 1121681 = 841261) B841261
theorem B1121699 : Blo 746329 1121699 := bstep (se 1 (by rfl) ⟨841274, by rfl⟩ : syracuseStep 1121699 = 1682549) B1682549
theorem B1121729 : Blo 746329 1121729 := bstep (se 2 (by rfl) ⟨420648, by rfl⟩ : syracuseStep 1121729 = 841297) B841297
theorem B1121747 : Blo 746329 1121747 := bstep (se 1 (by rfl) ⟨841310, by rfl⟩ : syracuseStep 1121747 = 1682621) B1682621
theorem B1121777 : Blo 746329 1121777 := bstep (se 2 (by rfl) ⟨420666, by rfl⟩ : syracuseStep 1121777 = 841333) B841333
theorem B1121795 : Blo 746329 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B1121825 : Blo 746329 1121825 := bstep (se 2 (by rfl) ⟨420684, by rfl⟩ : syracuseStep 1121825 = 841369) B841369
theorem B2399789 : Blo 746329 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B1121843 : Blo 746329 1121843 := bstep (se 1 (by rfl) ⟨841382, by rfl⟩ : syracuseStep 1121843 = 1682765) B1682765
theorem B1121873 : Blo 746329 1121873 := bstep (se 2 (by rfl) ⟨420702, by rfl⟩ : syracuseStep 1121873 = 841405) B841405
theorem B1121891 : Blo 746329 1121891 := bstep (se 1 (by rfl) ⟨841418, by rfl⟩ : syracuseStep 1121891 = 1682837) B1682837
theorem B2530925 : Blo 746329 2530925 := bstep (se 3 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 2530925 = 949097) B949097
theorem B1121921 : Blo 746329 1121921 := bstep (se 2 (by rfl) ⟨420720, by rfl⟩ : syracuseStep 1121921 = 841441) B841441
theorem B1121939 : Blo 746329 1121939 := bstep (se 1 (by rfl) ⟨841454, by rfl⟩ : syracuseStep 1121939 = 1682909) B1682909
theorem B2530979 : Blo 746329 2530979 := bstep (se 1 (by rfl) ⟨1898234, by rfl⟩ : syracuseStep 2530979 = 3796469) B3796469
theorem B1121969 : Blo 746329 1121969 := bstep (se 2 (by rfl) ⟨420738, by rfl⟩ : syracuseStep 1121969 = 841477) B841477
theorem B1121987 : Blo 746329 1121987 := bstep (se 1 (by rfl) ⟨841490, by rfl⟩ : syracuseStep 1121987 = 1682981) B1682981
theorem B2334413 : Blo 746329 2334413 := bstep (se 3 (by rfl) ⟨437702, by rfl⟩ : syracuseStep 2334413 = 875405) B875405
theorem B1122017 : Blo 746329 1122017 := bstep (se 2 (by rfl) ⟨420756, by rfl⟩ : syracuseStep 1122017 = 841513) B841513
theorem B1122035 : Blo 746329 1122035 := bstep (se 1 (by rfl) ⟨841526, by rfl⟩ : syracuseStep 1122035 = 1683053) B1683053
theorem B1122065 : Blo 746329 1122065 := bstep (se 2 (by rfl) ⟨420774, by rfl⟩ : syracuseStep 1122065 = 841549) B841549
theorem B1122083 : Blo 746329 1122083 := bstep (se 1 (by rfl) ⟨841562, by rfl⟩ : syracuseStep 1122083 = 1683125) B1683125
theorem B1417009 : Blo 746329 1417009 := bstep (se 2 (by rfl) ⟨531378, by rfl⟩ : syracuseStep 1417009 = 1062757) B1062757
theorem B1122113 : Blo 746329 1122113 := bstep (se 2 (by rfl) ⟨420792, by rfl⟩ : syracuseStep 1122113 = 841585) B841585
theorem B1122131 : Blo 746329 1122131 := bstep (se 1 (by rfl) ⟨841598, by rfl⟩ : syracuseStep 1122131 = 1683197) B1683197
theorem B1122161 : Blo 746329 1122161 := bstep (se 2 (by rfl) ⟨420810, by rfl⟩ : syracuseStep 1122161 = 841621) B841621
theorem B1122179 : Blo 746329 1122179 := bstep (se 1 (by rfl) ⟨841634, by rfl⟩ : syracuseStep 1122179 = 1683269) B1683269
theorem B1122209 : Blo 746329 1122209 := bstep (se 2 (by rfl) ⟨420828, by rfl⟩ : syracuseStep 1122209 = 841657) B841657
theorem B2531249 : Blo 746329 2531249 := bstep (se 2 (by rfl) ⟨949218, by rfl⟩ : syracuseStep 2531249 = 1898437) B1898437
theorem B1122227 : Blo 746329 1122227 := bstep (se 1 (by rfl) ⟨841670, by rfl⟩ : syracuseStep 1122227 = 1683341) B1683341
theorem B1417169 : Blo 746329 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B1122257 : Blo 746329 1122257 := bstep (se 2 (by rfl) ⟨420846, by rfl⟩ : syracuseStep 1122257 = 841693) B841693
theorem B1122275 : Blo 746329 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B1679345 : Blo 746329 1679345 := bstep (se 2 (by rfl) ⟨629754, by rfl⟩ : syracuseStep 1679345 = 1259509) B1259509
theorem B958451 : Blo 746329 958451 := bstep (se 1 (by rfl) ⟨718838, by rfl⟩ : syracuseStep 958451 = 1437677) B1437677
theorem B1122305 : Blo 746329 1122305 := bstep (se 2 (by rfl) ⟨420864, by rfl⟩ : syracuseStep 1122305 = 841729) B841729
theorem B1679363 : Blo 746329 1679363 := bstep (se 1 (by rfl) ⟨1259522, by rfl⟩ : syracuseStep 1679363 = 2519045) B2519045
theorem B1122323 : Blo 746329 1122323 := bstep (se 1 (by rfl) ⟨841742, by rfl⟩ : syracuseStep 1122323 = 1683485) B1683485
theorem B2400301 : Blo 746329 2400301 := bstep (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) B900113
theorem B1122353 : Blo 746329 1122353 := bstep (se 2 (by rfl) ⟨420882, by rfl⟩ : syracuseStep 1122353 = 841765) B841765
theorem B1122371 : Blo 746329 1122371 := bstep (se 1 (by rfl) ⟨841778, by rfl⟩ : syracuseStep 1122371 = 1683557) B1683557
theorem B1122401 : Blo 746329 1122401 := bstep (se 2 (by rfl) ⟨420900, by rfl⟩ : syracuseStep 1122401 = 841801) B841801
theorem B1122419 : Blo 746329 1122419 := bstep (se 1 (by rfl) ⟨841814, by rfl⟩ : syracuseStep 1122419 = 1683629) B1683629
theorem B1122449 : Blo 746329 1122449 := bstep (se 2 (by rfl) ⟨420918, by rfl⟩ : syracuseStep 1122449 = 841837) B841837
theorem B1122467 : Blo 746329 1122467 := bstep (se 1 (by rfl) ⟨841850, by rfl⟩ : syracuseStep 1122467 = 1683701) B1683701
theorem B1122497 : Blo 746329 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B1122515 : Blo 746329 1122515 := bstep (se 1 (by rfl) ⟨841886, by rfl⟩ : syracuseStep 1122515 = 1683773) B1683773
theorem B1122545 : Blo 746329 1122545 := bstep (se 2 (by rfl) ⟨420954, by rfl⟩ : syracuseStep 1122545 = 841909) B841909
theorem B1122563 : Blo 746329 1122563 := bstep (se 1 (by rfl) ⟨841922, by rfl⟩ : syracuseStep 1122563 = 1683845) B1683845
theorem B5611789 : Blo 746329 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B1679633 : Blo 746329 1679633 := bstep (se 2 (by rfl) ⟨629862, by rfl⟩ : syracuseStep 1679633 = 1259725) B1259725
theorem B1122593 : Blo 746329 1122593 := bstep (se 2 (by rfl) ⟨420972, by rfl⟩ : syracuseStep 1122593 = 841945) B841945
theorem B1679651 : Blo 746329 1679651 := bstep (se 1 (by rfl) ⟨1259738, by rfl⟩ : syracuseStep 1679651 = 2519477) B2519477
theorem B1122611 : Blo 746329 1122611 := bstep (se 1 (by rfl) ⟨841958, by rfl⟩ : syracuseStep 1122611 = 1683917) B1683917
theorem B1122641 : Blo 746329 1122641 := bstep (se 2 (by rfl) ⟨420990, by rfl⟩ : syracuseStep 1122641 = 841981) B841981
theorem B1417571 : Blo 746329 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B1122659 : Blo 746329 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B1122689 : Blo 746329 1122689 := bstep (se 2 (by rfl) ⟨421008, by rfl⟩ : syracuseStep 1122689 = 842017) B842017
theorem B4792709 : Blo 746329 4792709 := bstep (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) B898633
theorem B1122707 : Blo 746329 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B1122737 : Blo 746329 1122737 := bstep (se 2 (by rfl) ⟨421026, by rfl⟩ : syracuseStep 1122737 = 842053) B842053
theorem B1122755 : Blo 746329 1122755 := bstep (se 1 (by rfl) ⟨842066, by rfl⟩ : syracuseStep 1122755 = 1684133) B1684133
theorem B2531789 : Blo 746329 2531789 := bstep (se 3 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 2531789 = 949421) B949421
theorem B1122785 : Blo 746329 1122785 := bstep (se 2 (by rfl) ⟨421044, by rfl⟩ : syracuseStep 1122785 = 842089) B842089
theorem B1122803 : Blo 746329 1122803 := bstep (se 1 (by rfl) ⟨842102, by rfl⟩ : syracuseStep 1122803 = 1684205) B1684205
theorem B2531843 : Blo 746329 2531843 := bstep (se 1 (by rfl) ⟨1898882, by rfl⟩ : syracuseStep 2531843 = 3797765) B3797765
theorem B1122833 : Blo 746329 1122833 := bstep (se 2 (by rfl) ⟨421062, by rfl⟩ : syracuseStep 1122833 = 842125) B842125
theorem B1122851 : Blo 746329 1122851 := bstep (se 1 (by rfl) ⟨842138, by rfl⟩ : syracuseStep 1122851 = 1684277) B1684277
theorem B2400803 : Blo 746329 2400803 := bstep (se 1 (by rfl) ⟨1800602, by rfl⟩ : syracuseStep 2400803 = 3601205) B3601205
theorem B1679921 : Blo 746329 1679921 := bstep (se 2 (by rfl) ⟨629970, by rfl⟩ : syracuseStep 1679921 = 1259941) B1259941
theorem B1122881 : Blo 746329 1122881 := bstep (se 2 (by rfl) ⟨421080, by rfl⟩ : syracuseStep 1122881 = 842161) B842161
theorem B1679939 : Blo 746329 1679939 := bstep (se 1 (by rfl) ⟨1259954, by rfl⟩ : syracuseStep 1679939 = 2519909) B2519909
theorem B1122899 : Blo 746329 1122899 := bstep (se 1 (by rfl) ⟨842174, by rfl⟩ : syracuseStep 1122899 = 1684349) B1684349
theorem B1122929 : Blo 746329 1122929 := bstep (se 2 (by rfl) ⟨421098, by rfl⟩ : syracuseStep 1122929 = 842197) B842197
theorem B1122947 : Blo 746329 1122947 := bstep (se 1 (by rfl) ⟨842210, by rfl⟩ : syracuseStep 1122947 = 1684421) B1684421
theorem B1122977 : Blo 746329 1122977 := bstep (se 2 (by rfl) ⟨421116, by rfl⟩ : syracuseStep 1122977 = 842233) B842233
theorem B1122995 : Blo 746329 1122995 := bstep (se 1 (by rfl) ⟨842246, by rfl⟩ : syracuseStep 1122995 = 1684493) B1684493
theorem B1123025 : Blo 746329 1123025 := bstep (se 2 (by rfl) ⟨421134, by rfl⟩ : syracuseStep 1123025 = 842269) B842269
theorem B1123043 : Blo 746329 1123043 := bstep (se 1 (by rfl) ⟨842282, by rfl⟩ : syracuseStep 1123043 = 1684565) B1684565
theorem B1123073 : Blo 746329 1123073 := bstep (se 2 (by rfl) ⟨421152, by rfl⟩ : syracuseStep 1123073 = 842305) B842305
theorem B2532113 : Blo 746329 2532113 := bstep (se 2 (by rfl) ⟨949542, by rfl⟩ : syracuseStep 2532113 = 1899085) B1899085
theorem B1123091 : Blo 746329 1123091 := bstep (se 1 (by rfl) ⟨842318, by rfl⟩ : syracuseStep 1123091 = 1684637) B1684637
theorem B1123121 : Blo 746329 1123121 := bstep (se 2 (by rfl) ⟨421170, by rfl⟩ : syracuseStep 1123121 = 842341) B842341
theorem B1123139 : Blo 746329 1123139 := bstep (se 1 (by rfl) ⟨842354, by rfl⟩ : syracuseStep 1123139 = 1684709) B1684709
theorem B1680209 : Blo 746329 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B1123169 : Blo 746329 1123169 := bstep (se 2 (by rfl) ⟨421188, by rfl⟩ : syracuseStep 1123169 = 842377) B842377
theorem B1680227 : Blo 746329 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B5677937 : Blo 746329 5677937 := bstep (se 2 (by rfl) ⟨2129226, by rfl⟩ : syracuseStep 5677937 = 4258453) B4258453
theorem B1123187 : Blo 746329 1123187 := bstep (se 1 (by rfl) ⟨842390, by rfl⟩ : syracuseStep 1123187 = 1684781) B1684781
theorem B4268933 : Blo 746329 4268933 := bstep (se 4 (by rfl) ⟨400212, by rfl⟩ : syracuseStep 4268933 = 800425) B800425
theorem B1123217 : Blo 746329 1123217 := bstep (se 2 (by rfl) ⟨421206, by rfl⟩ : syracuseStep 1123217 = 842413) B842413
theorem B1123235 : Blo 746329 1123235 := bstep (se 1 (by rfl) ⟨842426, by rfl⟩ : syracuseStep 1123235 = 1684853) B1684853
theorem B1123265 : Blo 746329 1123265 := bstep (se 2 (by rfl) ⟨421224, by rfl⟩ : syracuseStep 1123265 = 842449) B842449
theorem B1123283 : Blo 746329 1123283 := bstep (se 1 (by rfl) ⟨842462, by rfl⟩ : syracuseStep 1123283 = 1684925) B1684925
theorem B1123313 : Blo 746329 1123313 := bstep (se 2 (by rfl) ⟨421242, by rfl⟩ : syracuseStep 1123313 = 842485) B842485
theorem B1123331 : Blo 746329 1123331 := bstep (se 1 (by rfl) ⟨842498, by rfl⟩ : syracuseStep 1123331 = 1684997) B1684997
theorem B1123361 : Blo 746329 1123361 := bstep (se 2 (by rfl) ⟨421260, by rfl⟩ : syracuseStep 1123361 = 842521) B842521
theorem B1123379 : Blo 746329 1123379 := bstep (se 1 (by rfl) ⟨842534, by rfl⟩ : syracuseStep 1123379 = 1685069) B1685069
theorem B1123409 : Blo 746329 1123409 := bstep (se 2 (by rfl) ⟨421278, by rfl⟩ : syracuseStep 1123409 = 842557) B842557
theorem B2696291 : Blo 746329 2696291 := bstep (se 1 (by rfl) ⟨2022218, by rfl⟩ : syracuseStep 2696291 = 4044437) B4044437
theorem B1123427 : Blo 746329 1123427 := bstep (se 1 (by rfl) ⟨842570, by rfl⟩ : syracuseStep 1123427 = 1685141) B1685141
theorem B1680497 : Blo 746329 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B1123457 : Blo 746329 1123457 := bstep (se 2 (by rfl) ⟨421296, by rfl⟩ : syracuseStep 1123457 = 842593) B842593
theorem B1680515 : Blo 746329 1680515 := bstep (se 1 (by rfl) ⟨1260386, by rfl⟩ : syracuseStep 1680515 = 2520773) B2520773
theorem B1123475 : Blo 746329 1123475 := bstep (se 1 (by rfl) ⟨842606, by rfl⟩ : syracuseStep 1123475 = 1685213) B1685213
theorem B2565283 : Blo 746329 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1123505 : Blo 746329 1123505 := bstep (se 2 (by rfl) ⟨421314, by rfl⟩ : syracuseStep 1123505 = 842629) B842629
theorem B1123523 : Blo 746329 1123523 := bstep (se 1 (by rfl) ⟨842642, by rfl⟩ : syracuseStep 1123523 = 1685285) B1685285
theorem B4105421 : Blo 746329 4105421 := bstep (se 3 (by rfl) ⟨769766, by rfl⟩ : syracuseStep 4105421 = 1539533) B1539533
theorem B1123553 : Blo 746329 1123553 := bstep (se 2 (by rfl) ⟨421332, by rfl⟩ : syracuseStep 1123553 = 842665) B842665
theorem B1418467 : Blo 746329 1418467 := bstep (se 1 (by rfl) ⟨1063850, by rfl⟩ : syracuseStep 1418467 = 2127701) B2127701
theorem B1123571 : Blo 746329 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B1123601 : Blo 746329 1123601 := bstep (se 2 (by rfl) ⟨421350, by rfl⟩ : syracuseStep 1123601 = 842701) B842701
theorem B1123619 : Blo 746329 1123619 := bstep (se 1 (by rfl) ⟨842714, by rfl⟩ : syracuseStep 1123619 = 1685429) B1685429
theorem B1123649 : Blo 746329 1123649 := bstep (se 2 (by rfl) ⟨421368, by rfl⟩ : syracuseStep 1123649 = 842737) B842737
theorem B2270531 : Blo 746329 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B1123667 : Blo 746329 1123667 := bstep (se 1 (by rfl) ⟨842750, by rfl⟩ : syracuseStep 1123667 = 1685501) B1685501
theorem B1123697 : Blo 746329 1123697 := bstep (se 2 (by rfl) ⟨421386, by rfl⟩ : syracuseStep 1123697 = 842773) B842773
theorem B1418627 : Blo 746329 1418627 := bstep (se 1 (by rfl) ⟨1063970, by rfl⟩ : syracuseStep 1418627 = 2127941) B2127941
theorem B1123715 : Blo 746329 1123715 := bstep (se 1 (by rfl) ⟨842786, by rfl⟩ : syracuseStep 1123715 = 1685573) B1685573
theorem B1680785 : Blo 746329 1680785 := bstep (se 2 (by rfl) ⟨630294, by rfl⟩ : syracuseStep 1680785 = 1260589) B1260589
theorem B1123745 : Blo 746329 1123745 := bstep (se 2 (by rfl) ⟨421404, by rfl⟩ : syracuseStep 1123745 = 842809) B842809
theorem B1680803 : Blo 746329 1680803 := bstep (se 1 (by rfl) ⟨1260602, by rfl⟩ : syracuseStep 1680803 = 2521205) B2521205
theorem B1516963 : Blo 746329 1516963 := bstep (se 1 (by rfl) ⟨1137722, by rfl⟩ : syracuseStep 1516963 = 2275445) B2275445
theorem B1123763 : Blo 746329 1123763 := bstep (se 1 (by rfl) ⟨842822, by rfl⟩ : syracuseStep 1123763 = 1685645) B1685645
theorem B1123793 : Blo 746329 1123793 := bstep (se 2 (by rfl) ⟨421422, by rfl⟩ : syracuseStep 1123793 = 842845) B842845
theorem B1123811 : Blo 746329 1123811 := bstep (se 1 (by rfl) ⟨842858, by rfl⟩ : syracuseStep 1123811 = 1685717) B1685717
theorem B1123841 : Blo 746329 1123841 := bstep (se 2 (by rfl) ⟨421440, by rfl⟩ : syracuseStep 1123841 = 842881) B842881
theorem B1123859 : Blo 746329 1123859 := bstep (se 1 (by rfl) ⟨842894, by rfl⟩ : syracuseStep 1123859 = 1685789) B1685789
theorem B1123889 : Blo 746329 1123889 := bstep (se 2 (by rfl) ⟨421458, by rfl⟩ : syracuseStep 1123889 = 842917) B842917
theorem B4269617 : Blo 746329 4269617 := bstep (se 2 (by rfl) ⟨1601106, by rfl⟩ : syracuseStep 4269617 = 3202213) B3202213
theorem B1123907 : Blo 746329 1123907 := bstep (se 1 (by rfl) ⟨842930, by rfl⟩ : syracuseStep 1123907 = 1685861) B1685861
theorem B1123937 : Blo 746329 1123937 := bstep (se 2 (by rfl) ⟨421476, by rfl⟩ : syracuseStep 1123937 = 842953) B842953
theorem B1123955 : Blo 746329 1123955 := bstep (se 1 (by rfl) ⟨842966, by rfl⟩ : syracuseStep 1123955 = 1685933) B1685933
theorem B1123985 : Blo 746329 1123985 := bstep (se 2 (by rfl) ⟨421494, by rfl⟩ : syracuseStep 1123985 = 842989) B842989
theorem B1124003 : Blo 746329 1124003 := bstep (se 1 (by rfl) ⟨843002, by rfl⟩ : syracuseStep 1124003 = 1686005) B1686005
theorem B1681073 : Blo 746329 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B1124033 : Blo 746329 1124033 := bstep (se 2 (by rfl) ⟨421512, by rfl⟩ : syracuseStep 1124033 = 843025) B843025
theorem B1681091 : Blo 746329 1681091 := bstep (se 1 (by rfl) ⟨1260818, by rfl⟩ : syracuseStep 1681091 = 2521637) B2521637
theorem B1124051 : Blo 746329 1124051 := bstep (se 1 (by rfl) ⟨843038, by rfl⟩ : syracuseStep 1124051 = 1686077) B1686077
theorem B1124081 : Blo 746329 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B1124099 : Blo 746329 1124099 := bstep (se 1 (by rfl) ⟨843074, by rfl⟩ : syracuseStep 1124099 = 1686149) B1686149
theorem B1124129 : Blo 746329 1124129 := bstep (se 2 (by rfl) ⟨421548, by rfl⟩ : syracuseStep 1124129 = 843097) B843097
theorem B1124147 : Blo 746329 1124147 := bstep (se 1 (by rfl) ⟨843110, by rfl⟩ : syracuseStep 1124147 = 1686221) B1686221
theorem B1124177 : Blo 746329 1124177 := bstep (se 2 (by rfl) ⟨421566, by rfl⟩ : syracuseStep 1124177 = 843133) B843133
theorem B1124195 : Blo 746329 1124195 := bstep (se 1 (by rfl) ⟨843146, by rfl⟩ : syracuseStep 1124195 = 1686293) B1686293
theorem B1124225 : Blo 746329 1124225 := bstep (se 2 (by rfl) ⟨421584, by rfl⟩ : syracuseStep 1124225 = 843169) B843169
theorem B1124243 : Blo 746329 1124243 := bstep (se 1 (by rfl) ⟨843182, by rfl⟩ : syracuseStep 1124243 = 1686365) B1686365
theorem B1124273 : Blo 746329 1124273 := bstep (se 2 (by rfl) ⟨421602, by rfl⟩ : syracuseStep 1124273 = 843205) B843205
theorem B1124291 : Blo 746329 1124291 := bstep (se 1 (by rfl) ⟨843218, by rfl⟩ : syracuseStep 1124291 = 1686437) B1686437
theorem B1681361 : Blo 746329 1681361 := bstep (se 2 (by rfl) ⟨630510, by rfl⟩ : syracuseStep 1681361 = 1261021) B1261021
theorem B1124321 : Blo 746329 1124321 := bstep (se 2 (by rfl) ⟨421620, by rfl⟩ : syracuseStep 1124321 = 843241) B843241
theorem B1681379 : Blo 746329 1681379 := bstep (se 1 (by rfl) ⟨1261034, by rfl⟩ : syracuseStep 1681379 = 2522069) B2522069
theorem B1124339 : Blo 746329 1124339 := bstep (se 1 (by rfl) ⟨843254, by rfl⟩ : syracuseStep 1124339 = 1686509) B1686509
theorem B1124369 : Blo 746329 1124369 := bstep (se 2 (by rfl) ⟨421638, by rfl⟩ : syracuseStep 1124369 = 843277) B843277
theorem B1124387 : Blo 746329 1124387 := bstep (se 1 (by rfl) ⟨843290, by rfl⟩ : syracuseStep 1124387 = 1686581) B1686581
theorem B1124417 : Blo 746329 1124417 := bstep (se 2 (by rfl) ⟨421656, by rfl⟩ : syracuseStep 1124417 = 843313) B843313
theorem B1124435 : Blo 746329 1124435 := bstep (se 1 (by rfl) ⟨843326, by rfl⟩ : syracuseStep 1124435 = 1686653) B1686653
theorem B1124465 : Blo 746329 1124465 := bstep (se 2 (by rfl) ⟨421674, by rfl⟩ : syracuseStep 1124465 = 843349) B843349
theorem B1124483 : Blo 746329 1124483 := bstep (se 1 (by rfl) ⟨843362, by rfl⟩ : syracuseStep 1124483 = 1686725) B1686725
theorem B1124513 : Blo 746329 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B1124531 : Blo 746329 1124531 := bstep (se 1 (by rfl) ⟨843398, by rfl⟩ : syracuseStep 1124531 = 1686797) B1686797
theorem B1124561 : Blo 746329 1124561 := bstep (se 2 (by rfl) ⟨421710, by rfl⟩ : syracuseStep 1124561 = 843421) B843421
theorem B1124579 : Blo 746329 1124579 := bstep (se 1 (by rfl) ⟨843434, by rfl⟩ : syracuseStep 1124579 = 1686869) B1686869
theorem B1681649 : Blo 746329 1681649 := bstep (se 2 (by rfl) ⟨630618, by rfl⟩ : syracuseStep 1681649 = 1261237) B1261237
theorem B1124609 : Blo 746329 1124609 := bstep (se 2 (by rfl) ⟨421728, by rfl⟩ : syracuseStep 1124609 = 843457) B843457
theorem B1681667 : Blo 746329 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1124627 : Blo 746329 1124627 := bstep (se 1 (by rfl) ⟨843470, by rfl⟩ : syracuseStep 1124627 = 1686941) B1686941
theorem B3189041 : Blo 746329 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B1124657 : Blo 746329 1124657 := bstep (se 2 (by rfl) ⟨421746, by rfl⟩ : syracuseStep 1124657 = 843493) B843493
theorem B1124675 : Blo 746329 1124675 := bstep (se 1 (by rfl) ⟨843506, by rfl⟩ : syracuseStep 1124675 = 1687013) B1687013
theorem B1124705 : Blo 746329 1124705 := bstep (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) B843529
theorem B3189091 : Blo 746329 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B2697571 : Blo 746329 2697571 := bstep (se 1 (by rfl) ⟨2023178, by rfl⟩ : syracuseStep 2697571 = 4046357) B4046357
theorem B2402659 : Blo 746329 2402659 := bstep (se 1 (by rfl) ⟨1801994, by rfl⟩ : syracuseStep 2402659 = 3603989) B3603989
theorem B1124723 : Blo 746329 1124723 := bstep (se 1 (by rfl) ⟨843542, by rfl⟩ : syracuseStep 1124723 = 1687085) B1687085
theorem B797059 : Blo 746329 797059 := bstep (se 1 (by rfl) ⟨597794, by rfl⟩ : syracuseStep 797059 = 1195589) B1195589
theorem B1124753 : Blo 746329 1124753 := bstep (se 2 (by rfl) ⟨421782, by rfl⟩ : syracuseStep 1124753 = 843565) B843565
theorem B1124771 : Blo 746329 1124771 := bstep (se 1 (by rfl) ⟨843578, by rfl⟩ : syracuseStep 1124771 = 1687157) B1687157
theorem B1419697 : Blo 746329 1419697 := bstep (se 2 (by rfl) ⟨532386, by rfl⟩ : syracuseStep 1419697 = 1064773) B1064773
theorem B1124801 : Blo 746329 1124801 := bstep (se 2 (by rfl) ⟨421800, by rfl⟩ : syracuseStep 1124801 = 843601) B843601
theorem B18196933 : Blo 746329 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B4106693 : Blo 746329 4106693 := bstep (se 4 (by rfl) ⟨385002, by rfl⟩ : syracuseStep 4106693 = 770005) B770005
theorem B1124819 : Blo 746329 1124819 := bstep (se 1 (by rfl) ⟨843614, by rfl⟩ : syracuseStep 1124819 = 1687229) B1687229
theorem B1124849 : Blo 746329 1124849 := bstep (se 2 (by rfl) ⟨421818, by rfl⟩ : syracuseStep 1124849 = 843637) B843637
theorem B1124867 : Blo 746329 1124867 := bstep (se 1 (by rfl) ⟨843650, by rfl⟩ : syracuseStep 1124867 = 1687301) B1687301
theorem B1681937 : Blo 746329 1681937 := bstep (se 2 (by rfl) ⟨630726, by rfl⟩ : syracuseStep 1681937 = 1261453) B1261453
theorem B1124897 : Blo 746329 1124897 := bstep (se 2 (by rfl) ⟨421836, by rfl⟩ : syracuseStep 1124897 = 843673) B843673
theorem B1681955 : Blo 746329 1681955 := bstep (se 1 (by rfl) ⟨1261466, by rfl⟩ : syracuseStep 1681955 = 2522933) B2522933
theorem B1124915 : Blo 746329 1124915 := bstep (se 1 (by rfl) ⟨843686, by rfl⟩ : syracuseStep 1124915 = 1687373) B1687373
theorem B1124945 : Blo 746329 1124945 := bstep (se 2 (by rfl) ⟨421854, by rfl⟩ : syracuseStep 1124945 = 843709) B843709
theorem B1124963 : Blo 746329 1124963 := bstep (se 1 (by rfl) ⟨843722, by rfl⟩ : syracuseStep 1124963 = 1687445) B1687445
theorem B1124993 : Blo 746329 1124993 := bstep (se 2 (by rfl) ⟨421872, by rfl⟩ : syracuseStep 1124993 = 843745) B843745
theorem B1125011 : Blo 746329 1125011 := bstep (se 1 (by rfl) ⟨843758, by rfl⟩ : syracuseStep 1125011 = 1687517) B1687517
theorem B3418787 : Blo 746329 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B1125041 : Blo 746329 1125041 := bstep (se 2 (by rfl) ⟨421890, by rfl⟩ : syracuseStep 1125041 = 843781) B843781
theorem B1125059 : Blo 746329 1125059 := bstep (se 1 (by rfl) ⟨843794, by rfl⟩ : syracuseStep 1125059 = 1687589) B1687589
theorem B1125089 : Blo 746329 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B1125107 : Blo 746329 1125107 := bstep (se 1 (by rfl) ⟨843830, by rfl⟩ : syracuseStep 1125107 = 1687661) B1687661
theorem B1125137 : Blo 746329 1125137 := bstep (se 2 (by rfl) ⟨421926, by rfl⟩ : syracuseStep 1125137 = 843853) B843853
theorem B1125155 : Blo 746329 1125155 := bstep (se 1 (by rfl) ⟨843866, by rfl⟩ : syracuseStep 1125155 = 1687733) B1687733
theorem B1682225 : Blo 746329 1682225 := bstep (se 2 (by rfl) ⟨630834, by rfl⟩ : syracuseStep 1682225 = 1261669) B1261669
theorem B2403121 : Blo 746329 2403121 := bstep (se 2 (by rfl) ⟨901170, by rfl⟩ : syracuseStep 2403121 = 1802341) B1802341
theorem B1125185 : Blo 746329 1125185 := bstep (se 2 (by rfl) ⟨421944, by rfl⟩ : syracuseStep 1125185 = 843889) B843889
theorem B1682243 : Blo 746329 1682243 := bstep (se 1 (by rfl) ⟨1261682, by rfl⟩ : syracuseStep 1682243 = 2523365) B2523365
theorem B8530757 : Blo 746329 8530757 := bstep (se 4 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 8530757 = 1599517) B1599517
theorem B1125203 : Blo 746329 1125203 := bstep (se 1 (by rfl) ⟨843902, by rfl⟩ : syracuseStep 1125203 = 1687805) B1687805
theorem B1125233 : Blo 746329 1125233 := bstep (se 2 (by rfl) ⟨421962, by rfl⟩ : syracuseStep 1125233 = 843925) B843925
theorem B1125251 : Blo 746329 1125251 := bstep (se 1 (by rfl) ⟨843938, by rfl⟩ : syracuseStep 1125251 = 1687877) B1687877
theorem B1125281 : Blo 746329 1125281 := bstep (se 2 (by rfl) ⟨421980, by rfl⟩ : syracuseStep 1125281 = 843961) B843961
theorem B1125299 : Blo 746329 1125299 := bstep (se 1 (by rfl) ⟨843974, by rfl⟩ : syracuseStep 1125299 = 1687949) B1687949
theorem B3845069 : Blo 746329 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B1125329 : Blo 746329 1125329 := bstep (se 2 (by rfl) ⟨421998, by rfl⟩ : syracuseStep 1125329 = 843997) B843997
theorem B4271075 : Blo 746329 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B1125347 : Blo 746329 1125347 := bstep (se 1 (by rfl) ⟨844010, by rfl⟩ : syracuseStep 1125347 = 1688021) B1688021
theorem B797683 : Blo 746329 797683 := bstep (se 1 (by rfl) ⟨598262, by rfl⟩ : syracuseStep 797683 = 1196525) B1196525
theorem B1125377 : Blo 746329 1125377 := bstep (se 2 (by rfl) ⟨422016, by rfl⟩ : syracuseStep 1125377 = 844033) B844033
theorem B1125395 : Blo 746329 1125395 := bstep (se 1 (by rfl) ⟨844046, by rfl⟩ : syracuseStep 1125395 = 1688093) B1688093
theorem B1125425 : Blo 746329 1125425 := bstep (se 2 (by rfl) ⟨422034, by rfl⟩ : syracuseStep 1125425 = 844069) B844069
theorem B1125443 : Blo 746329 1125443 := bstep (se 1 (by rfl) ⟨844082, by rfl⟩ : syracuseStep 1125443 = 1688165) B1688165
theorem B1682513 : Blo 746329 1682513 := bstep (se 2 (by rfl) ⟨630942, by rfl⟩ : syracuseStep 1682513 = 1261885) B1261885
theorem B1125473 : Blo 746329 1125473 := bstep (se 2 (by rfl) ⟨422052, by rfl⟩ : syracuseStep 1125473 = 844105) B844105
theorem B1682531 : Blo 746329 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B1125491 : Blo 746329 1125491 := bstep (se 1 (by rfl) ⟨844118, by rfl⟩ : syracuseStep 1125491 = 1688237) B1688237
theorem B1682801 : Blo 746329 1682801 := bstep (se 2 (by rfl) ⟨631050, by rfl⟩ : syracuseStep 1682801 = 1262101) B1262101
theorem B1682819 : Blo 746329 1682819 := bstep (se 1 (by rfl) ⟨1262114, by rfl⟩ : syracuseStep 1682819 = 2524229) B2524229
theorem B1420753 : Blo 746329 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B896611 : Blo 746329 896611 := bstep (se 1 (by rfl) ⟨672458, by rfl⟩ : syracuseStep 896611 = 1344917) B1344917
theorem B1683089 : Blo 746329 1683089 := bstep (se 2 (by rfl) ⟨631158, by rfl⟩ : syracuseStep 1683089 = 1262317) B1262317
theorem B1683107 : Blo 746329 1683107 := bstep (se 1 (by rfl) ⟨1262330, by rfl⟩ : syracuseStep 1683107 = 2524661) B2524661
theorem B1421155 : Blo 746329 1421155 := bstep (se 1 (by rfl) ⟨1065866, by rfl⟩ : syracuseStep 1421155 = 2131733) B2131733
theorem B4796273 : Blo 746329 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1421201 : Blo 746329 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B1683377 : Blo 746329 1683377 := bstep (se 2 (by rfl) ⟨631266, by rfl⟩ : syracuseStep 1683377 = 1262533) B1262533
theorem B1683395 : Blo 746329 1683395 := bstep (se 1 (by rfl) ⟨1262546, by rfl⟩ : syracuseStep 1683395 = 2525093) B2525093
theorem B896995 : Blo 746329 896995 := bstep (se 1 (by rfl) ⟨672746, by rfl⟩ : syracuseStep 896995 = 1345493) B1345493
theorem B3780593 : Blo 746329 3780593 := bstep (se 2 (by rfl) ⟨1417722, by rfl⟩ : syracuseStep 3780593 = 2835445) B2835445
theorem B1421489 : Blo 746329 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B1683665 : Blo 746329 1683665 := bstep (se 2 (by rfl) ⟨631374, by rfl⟩ : syracuseStep 1683665 = 1262749) B1262749
theorem B1683683 : Blo 746329 1683683 := bstep (se 1 (by rfl) ⟨1262762, by rfl⟩ : syracuseStep 1683683 = 2525525) B2525525
theorem B1683953 : Blo 746329 1683953 := bstep (se 2 (by rfl) ⟨631482, by rfl⟩ : syracuseStep 1683953 = 1262965) B1262965
theorem B1683971 : Blo 746329 1683971 := bstep (se 1 (by rfl) ⟨1262978, by rfl⟩ : syracuseStep 1683971 = 2525957) B2525957
theorem B3191501 : Blo 746329 3191501 := bstep (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) B1196813
theorem B1684241 : Blo 746329 1684241 := bstep (se 2 (by rfl) ⟨631590, by rfl⟩ : syracuseStep 1684241 = 1263181) B1263181
theorem B1684259 : Blo 746329 1684259 := bstep (se 1 (by rfl) ⟨1263194, by rfl⟩ : syracuseStep 1684259 = 2526389) B2526389
theorem B799571 : Blo 746329 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B1422211 : Blo 746329 1422211 := bstep (se 1 (by rfl) ⟨1066658, by rfl⟩ : syracuseStep 1422211 = 2133317) B2133317
theorem B4109197 : Blo 746329 4109197 := bstep (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) B1540949
theorem B1684529 : Blo 746329 1684529 := bstep (se 2 (by rfl) ⟨631698, by rfl⟩ : syracuseStep 1684529 = 1263397) B1263397
theorem B1684547 : Blo 746329 1684547 := bstep (se 1 (by rfl) ⟨1263410, by rfl⟩ : syracuseStep 1684547 = 2526821) B2526821
theorem B4797731 : Blo 746329 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1520945 : Blo 746329 1520945 := bstep (se 2 (by rfl) ⟨570354, by rfl⟩ : syracuseStep 1520945 = 1140709) B1140709
theorem B1422659 : Blo 746329 1422659 := bstep (se 1 (by rfl) ⟨1066994, by rfl⟩ : syracuseStep 1422659 = 2133989) B2133989
theorem B1684817 : Blo 746329 1684817 := bstep (se 2 (by rfl) ⟨631806, by rfl⟩ : syracuseStep 1684817 = 1263613) B1263613
theorem B1684835 : Blo 746329 1684835 := bstep (se 1 (by rfl) ⟨1263626, by rfl⟩ : syracuseStep 1684835 = 2527253) B2527253
theorem B3782051 : Blo 746329 3782051 := bstep (se 1 (by rfl) ⟨2836538, by rfl⟩ : syracuseStep 3782051 = 5673077) B5673077
theorem B2045425 : Blo 746329 2045425 := bstep (se 2 (by rfl) ⟨767034, by rfl⟩ : syracuseStep 2045425 = 1534069) B1534069
theorem B1422947 : Blo 746329 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B1685105 : Blo 746329 1685105 := bstep (se 2 (by rfl) ⟨631914, by rfl⟩ : syracuseStep 1685105 = 1263829) B1263829
theorem B1685123 : Blo 746329 1685123 := bstep (se 1 (by rfl) ⟨1263842, by rfl⟩ : syracuseStep 1685123 = 2527685) B2527685
theorem B898787 : Blo 746329 898787 := bstep (se 1 (by rfl) ⟨674090, by rfl⟩ : syracuseStep 898787 = 1348181) B1348181
theorem B1685393 : Blo 746329 1685393 := bstep (se 2 (by rfl) ⟨632022, by rfl⟩ : syracuseStep 1685393 = 1264045) B1264045
theorem B1685411 : Blo 746329 1685411 := bstep (se 1 (by rfl) ⟨1264058, by rfl⟩ : syracuseStep 1685411 = 2528117) B2528117
theorem B1259489 : Blo 746329 1259489 := bstep (se 2 (by rfl) ⟨472308, by rfl⟩ : syracuseStep 1259489 = 944617) B944617
theorem B1914961 : Blo 746329 1914961 := bstep (se 2 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 1914961 = 1436221) B1436221
theorem B1259617 : Blo 746329 1259617 := bstep (se 2 (by rfl) ⟨472356, by rfl⟩ : syracuseStep 1259617 = 944713) B944713
theorem B1259651 : Blo 746329 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B1685681 : Blo 746329 1685681 := bstep (se 2 (by rfl) ⟨632130, by rfl⟩ : syracuseStep 1685681 = 1264261) B1264261
theorem B1685699 : Blo 746329 1685699 := bstep (se 1 (by rfl) ⟨1264274, by rfl⟩ : syracuseStep 1685699 = 2528549) B2528549
theorem B3782861 : Blo 746329 3782861 := bstep (se 3 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 3782861 = 1418573) B1418573
theorem B1259779 : Blo 746329 1259779 := bstep (se 1 (by rfl) ⟨944834, by rfl⟩ : syracuseStep 1259779 = 1889669) B1889669
theorem B1063201 : Blo 746329 1063201 := bstep (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) B797401
theorem B2701667 : Blo 746329 2701667 := bstep (se 1 (by rfl) ⟨2026250, by rfl⟩ : syracuseStep 2701667 = 4052501) B4052501
theorem B2275715 : Blo 746329 2275715 := bstep (se 1 (by rfl) ⟨1706786, by rfl⟩ : syracuseStep 2275715 = 3413573) B3413573
theorem B1259921 : Blo 746329 1259921 := bstep (se 2 (by rfl) ⟨472470, by rfl⟩ : syracuseStep 1259921 = 944941) B944941
theorem B1063315 : Blo 746329 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B1685969 : Blo 746329 1685969 := bstep (se 2 (by rfl) ⟨632238, by rfl⟩ : syracuseStep 1685969 = 1264477) B1264477
theorem B1685987 : Blo 746329 1685987 := bstep (se 1 (by rfl) ⟨1264490, by rfl⟩ : syracuseStep 1685987 = 2528981) B2528981
theorem B1260049 : Blo 746329 1260049 := bstep (se 2 (by rfl) ⟨472518, by rfl⟩ : syracuseStep 1260049 = 945037) B945037
theorem B1423889 : Blo 746329 1423889 := bstep (se 2 (by rfl) ⟨533958, by rfl⟩ : syracuseStep 1423889 = 1067917) B1067917
theorem B1260083 : Blo 746329 1260083 := bstep (se 1 (by rfl) ⟨945062, by rfl⟩ : syracuseStep 1260083 = 1890125) B1890125
theorem B3029645 : Blo 746329 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B1260211 : Blo 746329 1260211 := bstep (se 1 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 1260211 = 1890317) B1890317
theorem B1686257 : Blo 746329 1686257 := bstep (se 2 (by rfl) ⟨632346, by rfl⟩ : syracuseStep 1686257 = 1264693) B1264693
theorem B1686275 : Blo 746329 1686275 := bstep (se 1 (by rfl) ⟨1264706, by rfl⟩ : syracuseStep 1686275 = 2529413) B2529413
theorem B1260353 : Blo 746329 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1522577 : Blo 746329 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B1260481 : Blo 746329 1260481 := bstep (se 2 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 1260481 = 945361) B945361
theorem B1260515 : Blo 746329 1260515 := bstep (se 1 (by rfl) ⟨945386, by rfl⟩ : syracuseStep 1260515 = 1890773) B1890773
theorem B1686545 : Blo 746329 1686545 := bstep (se 2 (by rfl) ⟨632454, by rfl⟩ : syracuseStep 1686545 = 1264909) B1264909
theorem B1686563 : Blo 746329 1686563 := bstep (se 1 (by rfl) ⟨1264922, by rfl⟩ : syracuseStep 1686563 = 2529845) B2529845
theorem B1260643 : Blo 746329 1260643 := bstep (se 1 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 1260643 = 1890965) B1890965
theorem B1260785 : Blo 746329 1260785 := bstep (se 2 (by rfl) ⟨472794, by rfl⟩ : syracuseStep 1260785 = 945589) B945589
theorem B1686833 : Blo 746329 1686833 := bstep (se 2 (by rfl) ⟨632562, by rfl⟩ : syracuseStep 1686833 = 1265125) B1265125
theorem B1686851 : Blo 746329 1686851 := bstep (se 1 (by rfl) ⟨1265138, by rfl⟩ : syracuseStep 1686851 = 2530277) B2530277
theorem B1260913 : Blo 746329 1260913 := bstep (se 2 (by rfl) ⟨472842, by rfl⟩ : syracuseStep 1260913 = 945685) B945685
theorem B2833805 : Blo 746329 2833805 := bstep (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) B1062677
theorem B7191949 : Blo 746329 7191949 := bstep (se 3 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 7191949 = 2696981) B2696981
theorem B1260947 : Blo 746329 1260947 := bstep (se 1 (by rfl) ⟨945710, by rfl⟩ : syracuseStep 1260947 = 1891421) B1891421
theorem B1261075 : Blo 746329 1261075 := bstep (se 1 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 1261075 = 1891613) B1891613
theorem B1687121 : Blo 746329 1687121 := bstep (se 2 (by rfl) ⟨632670, by rfl⟩ : syracuseStep 1687121 = 1265341) B1265341
theorem B1687139 : Blo 746329 1687139 := bstep (se 1 (by rfl) ⟨1265354, by rfl⟩ : syracuseStep 1687139 = 2530709) B2530709
theorem B1261217 : Blo 746329 1261217 := bstep (se 2 (by rfl) ⟨472956, by rfl⟩ : syracuseStep 1261217 = 945913) B945913
theorem B1064659 : Blo 746329 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B1261345 : Blo 746329 1261345 := bstep (se 2 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 1261345 = 946009) B946009
theorem B1261379 : Blo 746329 1261379 := bstep (se 1 (by rfl) ⟨946034, by rfl⟩ : syracuseStep 1261379 = 1892069) B1892069
theorem B1195859 : Blo 746329 1195859 := bstep (se 1 (by rfl) ⟨896894, by rfl⟩ : syracuseStep 1195859 = 1793789) B1793789
theorem B1687409 : Blo 746329 1687409 := bstep (se 2 (by rfl) ⟨632778, by rfl⟩ : syracuseStep 1687409 = 1265557) B1265557
theorem B1294211 : Blo 746329 1294211 := bstep (se 1 (by rfl) ⟨970658, by rfl⟩ : syracuseStep 1294211 = 1941317) B1941317
theorem B1687427 : Blo 746329 1687427 := bstep (se 1 (by rfl) ⟨1265570, by rfl⟩ : syracuseStep 1687427 = 2531141) B2531141
theorem B4800397 : Blo 746329 4800397 := bstep (se 3 (by rfl) ⟨900074, by rfl⟩ : syracuseStep 4800397 = 1800149) B1800149
theorem B1261507 : Blo 746329 1261507 := bstep (se 1 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 1261507 = 1892261) B1892261
theorem B1261649 : Blo 746329 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B1196147 : Blo 746329 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1687697 : Blo 746329 1687697 := bstep (se 2 (by rfl) ⟨632886, by rfl⟩ : syracuseStep 1687697 = 1265773) B1265773
theorem B1687715 : Blo 746329 1687715 := bstep (se 1 (by rfl) ⟨1265786, by rfl⟩ : syracuseStep 1687715 = 2531573) B2531573
theorem B901315 : Blo 746329 901315 := bstep (se 1 (by rfl) ⟨675986, by rfl⟩ : syracuseStep 901315 = 1351973) B1351973
theorem B1261777 : Blo 746329 1261777 := bstep (se 2 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 1261777 = 946333) B946333
theorem B1261811 : Blo 746329 1261811 := bstep (se 1 (by rfl) ⟨946358, by rfl⟩ : syracuseStep 1261811 = 1892717) B1892717
theorem B901363 : Blo 746329 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B5193989 : Blo 746329 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B1261939 : Blo 746329 1261939 := bstep (se 1 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 1261939 = 1892909) B1892909
theorem B1687985 : Blo 746329 1687985 := bstep (se 2 (by rfl) ⟨632994, by rfl⟩ : syracuseStep 1687985 = 1265989) B1265989
theorem B1688003 : Blo 746329 1688003 := bstep (se 1 (by rfl) ⟨1266002, by rfl⟩ : syracuseStep 1688003 = 2532005) B2532005
theorem B5390819 : Blo 746329 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1262081 : Blo 746329 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B8536589 : Blo 746329 8536589 := bstep (se 3 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 8536589 = 3201221) B3201221
theorem B3654179 : Blo 746329 3654179 := bstep (se 1 (by rfl) ⟨2740634, by rfl⟩ : syracuseStep 3654179 = 5481269) B5481269
theorem B1262209 : Blo 746329 1262209 := bstep (se 2 (by rfl) ⟨473328, by rfl⟩ : syracuseStep 1262209 = 946657) B946657
theorem B1262243 : Blo 746329 1262243 := bstep (se 1 (by rfl) ⟨946682, by rfl⟩ : syracuseStep 1262243 = 1893365) B1893365
theorem B7684877 : Blo 746329 7684877 := bstep (se 3 (by rfl) ⟨1440914, by rfl⟩ : syracuseStep 7684877 = 2881829) B2881829
theorem B1262371 : Blo 746329 1262371 := bstep (se 1 (by rfl) ⟨946778, by rfl⟩ : syracuseStep 1262371 = 1893557) B1893557
theorem B1065793 : Blo 746329 1065793 := bstep (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) B799345
theorem B1196947 : Blo 746329 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B1065889 : Blo 746329 1065889 := bstep (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) B799417
theorem B1262513 : Blo 746329 1262513 := bstep (se 2 (by rfl) ⟨473442, by rfl⟩ : syracuseStep 1262513 = 946885) B946885
theorem B3195875 : Blo 746329 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1197089 : Blo 746329 1197089 := bstep (se 2 (by rfl) ⟨448908, by rfl⟩ : syracuseStep 1197089 = 897817) B897817
theorem B3785777 : Blo 746329 3785777 := bstep (se 2 (by rfl) ⟨1419666, by rfl⟩ : syracuseStep 3785777 = 2839333) B2839333
theorem B1262641 : Blo 746329 1262641 := bstep (se 2 (by rfl) ⟨473490, by rfl⟩ : syracuseStep 1262641 = 946981) B946981
theorem B1197121 : Blo 746329 1197121 := bstep (se 2 (by rfl) ⟨448920, by rfl⟩ : syracuseStep 1197121 = 897841) B897841
theorem B1262675 : Blo 746329 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B4048069 : Blo 746329 4048069 := bstep (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) B759013
theorem B1262803 : Blo 746329 1262803 := bstep (se 1 (by rfl) ⟨947102, by rfl⟩ : syracuseStep 1262803 = 1894205) B1894205
theorem B1262945 : Blo 746329 1262945 := bstep (se 2 (by rfl) ⟨473604, by rfl⟩ : syracuseStep 1262945 = 947209) B947209
theorem B1066385 : Blo 746329 1066385 := bstep (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) B799789
theorem B2835917 : Blo 746329 2835917 := bstep (se 3 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 2835917 = 1063469) B1063469
theorem B1263073 : Blo 746329 1263073 := bstep (se 2 (by rfl) ⟨473652, by rfl⟩ : syracuseStep 1263073 = 947305) B947305
theorem B1263107 : Blo 746329 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B1820209 : Blo 746329 1820209 := bstep (se 2 (by rfl) ⟨682578, by rfl⟩ : syracuseStep 1820209 = 1365157) B1365157
theorem B1263235 : Blo 746329 1263235 := bstep (se 1 (by rfl) ⟨947426, by rfl⟩ : syracuseStep 1263235 = 1894853) B1894853
theorem B1263377 : Blo 746329 1263377 := bstep (se 2 (by rfl) ⟨473766, by rfl⟩ : syracuseStep 1263377 = 947533) B947533
theorem B1263505 : Blo 746329 1263505 := bstep (se 2 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 1263505 = 947629) B947629
theorem B1263539 : Blo 746329 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1198049 : Blo 746329 1198049 := bstep (se 2 (by rfl) ⟨449268, by rfl⟩ : syracuseStep 1198049 = 898537) B898537
theorem B1263667 : Blo 746329 1263667 := bstep (se 1 (by rfl) ⟨947750, by rfl⟩ : syracuseStep 1263667 = 1895501) B1895501
theorem B1263809 : Blo 746329 1263809 := bstep (se 2 (by rfl) ⟨473928, by rfl⟩ : syracuseStep 1263809 = 947857) B947857
theorem B2836721 : Blo 746329 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B1067251 : Blo 746329 1067251 := bstep (se 1 (by rfl) ⟨800438, by rfl⟩ : syracuseStep 1067251 = 1600877) B1600877
theorem B4868365 : Blo 746329 4868365 := bstep (se 3 (by rfl) ⟨912818, by rfl⟩ : syracuseStep 4868365 = 1825637) B1825637
theorem B1624355 : Blo 746329 1624355 := bstep (se 1 (by rfl) ⟨1218266, by rfl⟩ : syracuseStep 1624355 = 2436533) B2436533
theorem B1263937 : Blo 746329 1263937 := bstep (se 2 (by rfl) ⟨473976, by rfl⟩ : syracuseStep 1263937 = 947953) B947953
theorem B1067347 : Blo 746329 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B1263971 : Blo 746329 1263971 := bstep (se 1 (by rfl) ⟨947978, by rfl⟩ : syracuseStep 1263971 = 1895957) B1895957
theorem B3787235 : Blo 746329 3787235 := bstep (se 1 (by rfl) ⟨2840426, by rfl⟩ : syracuseStep 3787235 = 5680853) B5680853
theorem B1264099 : Blo 746329 1264099 := bstep (se 1 (by rfl) ⟨948074, by rfl⟩ : syracuseStep 1264099 = 1896149) B1896149
theorem B1264241 : Blo 746329 1264241 := bstep (se 2 (by rfl) ⟨474090, by rfl⟩ : syracuseStep 1264241 = 948181) B948181
theorem B1821361 : Blo 746329 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1264369 : Blo 746329 1264369 := bstep (se 2 (by rfl) ⟨474138, by rfl⟩ : syracuseStep 1264369 = 948277) B948277
theorem B1264403 : Blo 746329 1264403 := bstep (se 1 (by rfl) ⟨948302, by rfl⟩ : syracuseStep 1264403 = 1896605) B1896605
theorem B1198883 : Blo 746329 1198883 := bstep (se 1 (by rfl) ⟨899162, by rfl⟩ : syracuseStep 1198883 = 1798325) B1798325
theorem B1067843 : Blo 746329 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B2837389 : Blo 746329 2837389 := bstep (se 3 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 2837389 = 1064021) B1064021
theorem B2050957 : Blo 746329 2050957 := bstep (se 3 (by rfl) ⟨384554, by rfl⟩ : syracuseStep 2050957 = 769109) B769109
theorem B1264531 : Blo 746329 1264531 := bstep (se 1 (by rfl) ⟨948398, by rfl⟩ : syracuseStep 1264531 = 1896797) B1896797
theorem B3197873 : Blo 746329 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B1264673 : Blo 746329 1264673 := bstep (se 2 (by rfl) ⟨474252, by rfl⟩ : syracuseStep 1264673 = 948505) B948505
theorem B1199171 : Blo 746329 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B1264801 : Blo 746329 1264801 := bstep (se 2 (by rfl) ⟨474300, by rfl⟩ : syracuseStep 1264801 = 948601) B948601
theorem B1264835 : Blo 746329 1264835 := bstep (se 1 (by rfl) ⟨948626, by rfl⟩ : syracuseStep 1264835 = 1897253) B1897253
theorem B36457685 : Blo 746329 36457685 := bstep (se 7 (by rfl) ⟨427238, by rfl⟩ : syracuseStep 36457685 = 854477) B854477
theorem B3788045 : Blo 746329 3788045 := bstep (se 3 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 3788045 = 1420517) B1420517
theorem B1199395 : Blo 746329 1199395 := bstep (se 1 (by rfl) ⟨899546, by rfl⟩ : syracuseStep 1199395 = 1799093) B1799093
theorem B1264963 : Blo 746329 1264963 := bstep (se 1 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 1264963 = 1897445) B1897445
theorem B8539505 : Blo 746329 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B4050317 : Blo 746329 4050317 := bstep (se 3 (by rfl) ⟨759434, by rfl⟩ : syracuseStep 4050317 = 1518869) B1518869
theorem B2280845 : Blo 746329 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B1265105 : Blo 746329 1265105 := bstep (se 2 (by rfl) ⟨474414, by rfl⟩ : syracuseStep 1265105 = 948829) B948829
theorem B1265233 : Blo 746329 1265233 := bstep (se 2 (by rfl) ⟨474462, by rfl⟩ : syracuseStep 1265233 = 948925) B948925
theorem B1265267 : Blo 746329 1265267 := bstep (se 1 (by rfl) ⟨948950, by rfl⟩ : syracuseStep 1265267 = 1897901) B1897901
theorem B2838179 : Blo 746329 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B1265395 : Blo 746329 1265395 := bstep (se 1 (by rfl) ⟨949046, by rfl⟩ : syracuseStep 1265395 = 1898093) B1898093
theorem B4542277 : Blo 746329 4542277 := bstep (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) B851677
theorem B3198797 : Blo 746329 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B1265537 : Blo 746329 1265537 := bstep (se 2 (by rfl) ⟨474576, by rfl⟩ : syracuseStep 1265537 = 949153) B949153
theorem B1200113 : Blo 746329 1200113 := bstep (se 2 (by rfl) ⟨450042, by rfl⟩ : syracuseStep 1200113 = 900085) B900085
theorem B1265665 : Blo 746329 1265665 := bstep (se 2 (by rfl) ⟨474624, by rfl⟩ : syracuseStep 1265665 = 949249) B949249
theorem B1265699 : Blo 746329 1265699 := bstep (se 1 (by rfl) ⟨949274, by rfl⟩ : syracuseStep 1265699 = 1898549) B1898549
theorem B839731 : Blo 746329 839731 := bstep (se 1 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 839731 = 1259597) B1259597
theorem B1265827 : Blo 746329 1265827 := bstep (se 1 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 1265827 = 1898741) B1898741
theorem B1200305 : Blo 746329 1200305 := bstep (se 2 (by rfl) ⟨450114, by rfl⟩ : syracuseStep 1200305 = 900229) B900229
theorem B839875 : Blo 746329 839875 := bstep (se 1 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 839875 = 1259813) B1259813
theorem B2838833 : Blo 746329 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B1200433 : Blo 746329 1200433 := bstep (se 2 (by rfl) ⟨450162, by rfl⟩ : syracuseStep 1200433 = 900325) B900325
theorem B1265969 : Blo 746329 1265969 := bstep (se 2 (by rfl) ⟨474738, by rfl⟩ : syracuseStep 1265969 = 949477) B949477
theorem B840019 : Blo 746329 840019 := bstep (se 1 (by rfl) ⟨630014, by rfl⟩ : syracuseStep 840019 = 1260029) B1260029
theorem B1266097 : Blo 746329 1266097 := bstep (se 2 (by rfl) ⟨474786, by rfl⟩ : syracuseStep 1266097 = 949573) B949573
theorem B1266131 : Blo 746329 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B840163 : Blo 746329 840163 := bstep (se 1 (by rfl) ⟨630122, by rfl⟩ : syracuseStep 840163 = 1260245) B1260245
theorem B1135217 : Blo 746329 1135217 := bstep (se 2 (by rfl) ⟨425706, by rfl⟩ : syracuseStep 1135217 = 851413) B851413
theorem B840307 : Blo 746329 840307 := bstep (se 1 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 840307 = 1260461) B1260461
theorem B840451 : Blo 746329 840451 := bstep (se 1 (by rfl) ⟨630338, by rfl⟩ : syracuseStep 840451 = 1260677) B1260677
theorem B840595 : Blo 746329 840595 := bstep (se 1 (by rfl) ⟨630446, by rfl⟩ : syracuseStep 840595 = 1260893) B1260893
theorem B1594289 : Blo 746329 1594289 := bstep (se 2 (by rfl) ⟨597858, by rfl⟩ : syracuseStep 1594289 = 1195717) B1195717
theorem B1201073 : Blo 746329 1201073 := bstep (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) B900805
theorem B1889315 : Blo 746329 1889315 := bstep (se 1 (by rfl) ⟨1416986, by rfl⟩ : syracuseStep 1889315 = 2833973) B2833973
theorem B840739 : Blo 746329 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B1135777 : Blo 746329 1135777 := bstep (se 2 (by rfl) ⟨425916, by rfl⟩ : syracuseStep 1135777 = 851833) B851833
theorem B840883 : Blo 746329 840883 := bstep (se 1 (by rfl) ⟨630662, by rfl⟩ : syracuseStep 840883 = 1261325) B1261325
theorem B1889507 : Blo 746329 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B841027 : Blo 746329 841027 := bstep (se 1 (by rfl) ⟨630770, by rfl⟩ : syracuseStep 841027 = 1261541) B1261541
theorem B5133709 : Blo 746329 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B2020781 : Blo 746329 2020781 := bstep (se 3 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 2020781 = 757793) B757793
theorem B1594819 : Blo 746329 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B841171 : Blo 746329 841171 := bstep (se 1 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 841171 = 1261757) B1261757
theorem B6084067 : Blo 746329 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B841315 : Blo 746329 841315 := bstep (se 1 (by rfl) ⟨630986, by rfl⟩ : syracuseStep 841315 = 1261973) B1261973
theorem B2840291 : Blo 746329 2840291 := bstep (se 1 (by rfl) ⟨2130218, by rfl⟩ : syracuseStep 2840291 = 4260437) B4260437
theorem B2840305 : Blo 746329 2840305 := bstep (se 2 (by rfl) ⟨1065114, by rfl⟩ : syracuseStep 2840305 = 2130229) B2130229
theorem B841459 : Blo 746329 841459 := bstep (se 1 (by rfl) ⟨631094, by rfl⟩ : syracuseStep 841459 = 1262189) B1262189
theorem B841603 : Blo 746329 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B22763405 : Blo 746329 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B841747 : Blo 746329 841747 := bstep (se 1 (by rfl) ⟨631310, by rfl⟩ : syracuseStep 841747 = 1262621) B1262621
theorem B1136737 : Blo 746329 1136737 := bstep (se 2 (by rfl) ⟨426276, by rfl⟩ : syracuseStep 1136737 = 852553) B852553
theorem B3790961 : Blo 746329 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1890449 : Blo 746329 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B841891 : Blo 746329 841891 := bstep (se 1 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 841891 = 1262837) B1262837
theorem B1890499 : Blo 746329 1890499 := bstep (se 1 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 1890499 = 2835749) B2835749
theorem B842035 : Blo 746329 842035 := bstep (se 1 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 842035 = 1263053) B1263053
theorem B1136963 : Blo 746329 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2021699 : Blo 746329 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B1890641 : Blo 746329 1890641 := bstep (se 2 (by rfl) ⟨708990, by rfl⟩ : syracuseStep 1890641 = 1417981) B1417981
theorem B842179 : Blo 746329 842179 := bstep (se 1 (by rfl) ⟨631634, by rfl⟩ : syracuseStep 842179 = 1263269) B1263269
theorem B4381253 : Blo 746329 4381253 := bstep (se 4 (by rfl) ⟨410742, by rfl⟩ : syracuseStep 4381253 = 821485) B821485
theorem B842323 : Blo 746329 842323 := bstep (se 1 (by rfl) ⟨631742, by rfl⟩ : syracuseStep 842323 = 1263485) B1263485
theorem B842467 : Blo 746329 842467 := bstep (se 1 (by rfl) ⟨631850, by rfl⟩ : syracuseStep 842467 = 1263701) B1263701
theorem B3201905 : Blo 746329 3201905 := bstep (se 2 (by rfl) ⟨1200714, by rfl⟩ : syracuseStep 3201905 = 2401429) B2401429
theorem B842611 : Blo 746329 842611 := bstep (se 1 (by rfl) ⟨631958, by rfl⟩ : syracuseStep 842611 = 1263917) B1263917
theorem B1596305 : Blo 746329 1596305 := bstep (se 2 (by rfl) ⟨598614, by rfl⟩ : syracuseStep 1596305 = 1197229) B1197229
theorem B1596323 : Blo 746329 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1137601 : Blo 746329 1137601 := bstep (se 2 (by rfl) ⟨426600, by rfl⟩ : syracuseStep 1137601 = 853201) B853201
theorem B1137649 : Blo 746329 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B842755 : Blo 746329 842755 := bstep (se 1 (by rfl) ⟨632066, by rfl⟩ : syracuseStep 842755 = 1264133) B1264133
theorem B842899 : Blo 746329 842899 := bstep (se 1 (by rfl) ⟨632174, by rfl⟩ : syracuseStep 842899 = 1264349) B1264349
theorem B2841763 : Blo 746329 2841763 := bstep (se 1 (by rfl) ⟨2131322, by rfl⟩ : syracuseStep 2841763 = 4262645) B4262645
theorem B1137905 : Blo 746329 1137905 := bstep (se 2 (by rfl) ⟨426714, by rfl⟩ : syracuseStep 1137905 = 853429) B853429
theorem B843043 : Blo 746329 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B1891633 : Blo 746329 1891633 := bstep (se 2 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 1891633 = 1418725) B1418725
theorem B2022833 : Blo 746329 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B843187 : Blo 746329 843187 := bstep (se 1 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 843187 = 1264781) B1264781
theorem B3792419 : Blo 746329 3792419 := bstep (se 1 (by rfl) ⟨2844314, by rfl⟩ : syracuseStep 3792419 = 5688629) B5688629
theorem B1891907 : Blo 746329 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B843331 : Blo 746329 843331 := bstep (se 1 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 843331 = 1264997) B1264997
theorem B4054661 : Blo 746329 4054661 := bstep (se 4 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 4054661 = 760249) B760249
theorem B843475 : Blo 746329 843475 := bstep (se 1 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 843475 = 1265213) B1265213
theorem B1892099 : Blo 746329 1892099 := bstep (se 1 (by rfl) ⟨1419074, by rfl⟩ : syracuseStep 1892099 = 2838149) B2838149
theorem B843619 : Blo 746329 843619 := bstep (se 1 (by rfl) ⟨632714, by rfl⟩ : syracuseStep 843619 = 1265429) B1265429
theorem B2023309 : Blo 746329 2023309 := bstep (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) B758741
theorem B843763 : Blo 746329 843763 := bstep (se 1 (by rfl) ⟨632822, by rfl⟩ : syracuseStep 843763 = 1265645) B1265645
theorem B1138769 : Blo 746329 1138769 := bstep (se 2 (by rfl) ⟨427038, by rfl⟩ : syracuseStep 1138769 = 854077) B854077
theorem B3203171 : Blo 746329 3203171 := bstep (se 1 (by rfl) ⟨2402378, by rfl⟩ : syracuseStep 3203171 = 4804757) B4804757
theorem B1597553 : Blo 746329 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B10379377 : Blo 746329 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B843907 : Blo 746329 843907 := bstep (se 1 (by rfl) ⟨632930, by rfl⟩ : syracuseStep 843907 = 1265861) B1265861
theorem B2023633 : Blo 746329 2023633 := bstep (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) B1517725
theorem B844051 : Blo 746329 844051 := bstep (se 1 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 844051 = 1266077) B1266077
theorem B3793229 : Blo 746329 3793229 := bstep (se 3 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 3793229 = 1422461) B1422461
theorem B1794403 : Blo 746329 1794403 := bstep (se 1 (by rfl) ⟨1345802, by rfl⟩ : syracuseStep 1794403 = 2691605) B2691605
theorem B811363 : Blo 746329 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B2220419 : Blo 746329 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B1893041 : Blo 746329 1893041 := bstep (se 2 (by rfl) ⟨709890, by rfl⟩ : syracuseStep 1893041 = 1419781) B1419781
theorem B1893091 : Blo 746329 1893091 := bstep (se 1 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 1893091 = 2839637) B2839637
theorem B6841073 : Blo 746329 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B746339 : Blo 746329 746339 := bstep (se 1 (by rfl) ⟨559754, by rfl⟩ : syracuseStep 746339 = 1119509) B1119509
theorem B1893233 : Blo 746329 1893233 := bstep (se 2 (by rfl) ⟨709962, by rfl⟩ : syracuseStep 1893233 = 1419925) B1419925
theorem B746355 : Blo 746329 746355 := bstep (se 1 (by rfl) ⟨559766, by rfl⟩ : syracuseStep 746355 = 1119533) B1119533
theorem B746371 : Blo 746329 746371 := bstep (se 1 (by rfl) ⟨559778, by rfl⟩ : syracuseStep 746371 = 1119557) B1119557
theorem B746387 : Blo 746329 746387 := bstep (se 1 (by rfl) ⟨559790, by rfl⟩ : syracuseStep 746387 = 1119581) B1119581
theorem B746403 : Blo 746329 746403 := bstep (se 1 (by rfl) ⟨559802, by rfl⟩ : syracuseStep 746403 = 1119605) B1119605
theorem B746419 : Blo 746329 746419 := bstep (se 1 (by rfl) ⟨559814, by rfl⟩ : syracuseStep 746419 = 1119629) B1119629
theorem B746435 : Blo 746329 746435 := bstep (se 1 (by rfl) ⟨559826, by rfl⟩ : syracuseStep 746435 = 1119653) B1119653
theorem B4252621 : Blo 746329 4252621 := bstep (se 3 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 4252621 = 1594733) B1594733
theorem B746451 : Blo 746329 746451 := bstep (se 1 (by rfl) ⟨559838, by rfl⟩ : syracuseStep 746451 = 1119677) B1119677
theorem B746467 : Blo 746329 746467 := bstep (se 1 (by rfl) ⟨559850, by rfl⟩ : syracuseStep 746467 = 1119701) B1119701
theorem B746483 : Blo 746329 746483 := bstep (se 1 (by rfl) ⟨559862, by rfl⟩ : syracuseStep 746483 = 1119725) B1119725
theorem B746499 : Blo 746329 746499 := bstep (se 1 (by rfl) ⟨559874, by rfl⟩ : syracuseStep 746499 = 1119749) B1119749
theorem B746515 : Blo 746329 746515 := bstep (se 1 (by rfl) ⟨559886, by rfl⟩ : syracuseStep 746515 = 1119773) B1119773
theorem B746531 : Blo 746329 746531 := bstep (se 1 (by rfl) ⟨559898, by rfl⟩ : syracuseStep 746531 = 1119797) B1119797
theorem B746547 : Blo 746329 746547 := bstep (se 1 (by rfl) ⟨559910, by rfl⟩ : syracuseStep 746547 = 1119821) B1119821
theorem B746563 : Blo 746329 746563 := bstep (se 1 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 746563 = 1119845) B1119845
theorem B746579 : Blo 746329 746579 := bstep (se 1 (by rfl) ⟨559934, by rfl⟩ : syracuseStep 746579 = 1119869) B1119869
theorem B746595 : Blo 746329 746595 := bstep (se 1 (by rfl) ⟨559946, by rfl⟩ : syracuseStep 746595 = 1119893) B1119893
theorem B746611 : Blo 746329 746611 := bstep (se 1 (by rfl) ⟨559958, by rfl⟩ : syracuseStep 746611 = 1119917) B1119917
theorem B746627 : Blo 746329 746627 := bstep (se 1 (by rfl) ⟨559970, by rfl⟩ : syracuseStep 746627 = 1119941) B1119941
theorem B746643 : Blo 746329 746643 := bstep (se 1 (by rfl) ⟨559982, by rfl⟩ : syracuseStep 746643 = 1119965) B1119965
theorem B746659 : Blo 746329 746659 := bstep (se 1 (by rfl) ⟨559994, by rfl⟩ : syracuseStep 746659 = 1119989) B1119989
theorem B746675 : Blo 746329 746675 := bstep (se 1 (by rfl) ⟨560006, by rfl⟩ : syracuseStep 746675 = 1120013) B1120013
theorem B746691 : Blo 746329 746691 := bstep (se 1 (by rfl) ⟨560018, by rfl⟩ : syracuseStep 746691 = 1120037) B1120037
theorem B746707 : Blo 746329 746707 := bstep (se 1 (by rfl) ⟨560030, by rfl⟩ : syracuseStep 746707 = 1120061) B1120061
theorem B1008865 : Blo 746329 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B746723 : Blo 746329 746723 := bstep (se 1 (by rfl) ⟨560042, by rfl⟩ : syracuseStep 746723 = 1120085) B1120085
theorem B746739 : Blo 746329 746739 := bstep (se 1 (by rfl) ⟨560054, by rfl⟩ : syracuseStep 746739 = 1120109) B1120109
theorem B746755 : Blo 746329 746755 := bstep (se 1 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 746755 = 1120133) B1120133
theorem B746771 : Blo 746329 746771 := bstep (se 1 (by rfl) ⟨560078, by rfl⟩ : syracuseStep 746771 = 1120157) B1120157
theorem B746787 : Blo 746329 746787 := bstep (se 1 (by rfl) ⟨560090, by rfl⟩ : syracuseStep 746787 = 1120181) B1120181
theorem B746803 : Blo 746329 746803 := bstep (se 1 (by rfl) ⟨560102, by rfl⟩ : syracuseStep 746803 = 1120205) B1120205
theorem B746819 : Blo 746329 746819 := bstep (se 1 (by rfl) ⟨560114, by rfl⟩ : syracuseStep 746819 = 1120229) B1120229
theorem B2843981 : Blo 746329 2843981 := bstep (se 3 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 2843981 = 1066493) B1066493
theorem B746835 : Blo 746329 746835 := bstep (se 1 (by rfl) ⟨560126, by rfl⟩ : syracuseStep 746835 = 1120253) B1120253
theorem B746851 : Blo 746329 746851 := bstep (se 1 (by rfl) ⟨560138, by rfl⟩ : syracuseStep 746851 = 1120277) B1120277
theorem B2024813 : Blo 746329 2024813 := bstep (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) B759305
theorem B746867 : Blo 746329 746867 := bstep (se 1 (by rfl) ⟨560150, by rfl⟩ : syracuseStep 746867 = 1120301) B1120301
theorem B746883 : Blo 746329 746883 := bstep (se 1 (by rfl) ⟨560162, by rfl⟩ : syracuseStep 746883 = 1120325) B1120325
theorem B746899 : Blo 746329 746899 := bstep (se 1 (by rfl) ⟨560174, by rfl⟩ : syracuseStep 746899 = 1120349) B1120349
theorem B746915 : Blo 746329 746915 := bstep (se 1 (by rfl) ⟨560186, by rfl⟩ : syracuseStep 746915 = 1120373) B1120373
theorem B746931 : Blo 746329 746931 := bstep (se 1 (by rfl) ⟨560198, by rfl⟩ : syracuseStep 746931 = 1120397) B1120397
theorem B746947 : Blo 746329 746947 := bstep (se 1 (by rfl) ⟨560210, by rfl⟩ : syracuseStep 746947 = 1120421) B1120421
theorem B746963 : Blo 746329 746963 := bstep (se 1 (by rfl) ⟨560222, by rfl⟩ : syracuseStep 746963 = 1120445) B1120445
theorem B746979 : Blo 746329 746979 := bstep (se 1 (by rfl) ⟨560234, by rfl⟩ : syracuseStep 746979 = 1120469) B1120469
theorem B5694947 : Blo 746329 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B746995 : Blo 746329 746995 := bstep (se 1 (by rfl) ⟨560246, by rfl⟩ : syracuseStep 746995 = 1120493) B1120493
theorem B910835 : Blo 746329 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B747011 : Blo 746329 747011 := bstep (se 1 (by rfl) ⟨560258, by rfl⟩ : syracuseStep 747011 = 1120517) B1120517
theorem B747027 : Blo 746329 747027 := bstep (se 1 (by rfl) ⟨560270, by rfl⟩ : syracuseStep 747027 = 1120541) B1120541
theorem B747043 : Blo 746329 747043 := bstep (se 1 (by rfl) ⟨560282, by rfl⟩ : syracuseStep 747043 = 1120565) B1120565
theorem B747059 : Blo 746329 747059 := bstep (se 1 (by rfl) ⟨560294, by rfl⟩ : syracuseStep 747059 = 1120589) B1120589
theorem B747075 : Blo 746329 747075 := bstep (se 1 (by rfl) ⟨560306, by rfl⟩ : syracuseStep 747075 = 1120613) B1120613
theorem B747091 : Blo 746329 747091 := bstep (se 1 (by rfl) ⟨560318, by rfl⟩ : syracuseStep 747091 = 1120637) B1120637
theorem B6055523 : Blo 746329 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B747107 : Blo 746329 747107 := bstep (se 1 (by rfl) ⟨560330, by rfl⟩ : syracuseStep 747107 = 1120661) B1120661
theorem B747123 : Blo 746329 747123 := bstep (se 1 (by rfl) ⟨560342, by rfl⟩ : syracuseStep 747123 = 1120685) B1120685
theorem B747139 : Blo 746329 747139 := bstep (se 1 (by rfl) ⟨560354, by rfl⟩ : syracuseStep 747139 = 1120709) B1120709
theorem B1599107 : Blo 746329 1599107 := bstep (se 1 (by rfl) ⟨1199330, by rfl⟩ : syracuseStep 1599107 = 2398661) B2398661
theorem B1795729 : Blo 746329 1795729 := bstep (se 2 (by rfl) ⟨673398, by rfl⟩ : syracuseStep 1795729 = 1346797) B1346797
theorem B747155 : Blo 746329 747155 := bstep (se 1 (by rfl) ⟨560366, by rfl⟩ : syracuseStep 747155 = 1120733) B1120733
theorem B747171 : Blo 746329 747171 := bstep (se 1 (by rfl) ⟨560378, by rfl⟩ : syracuseStep 747171 = 1120757) B1120757
theorem B747187 : Blo 746329 747187 := bstep (se 1 (by rfl) ⟨560390, by rfl⟩ : syracuseStep 747187 = 1120781) B1120781
theorem B747203 : Blo 746329 747203 := bstep (se 1 (by rfl) ⟨560402, by rfl⟩ : syracuseStep 747203 = 1120805) B1120805
theorem B747219 : Blo 746329 747219 := bstep (se 1 (by rfl) ⟨560414, by rfl⟩ : syracuseStep 747219 = 1120829) B1120829
theorem B747235 : Blo 746329 747235 := bstep (se 1 (by rfl) ⟨560426, by rfl⟩ : syracuseStep 747235 = 1120853) B1120853
theorem B747251 : Blo 746329 747251 := bstep (se 1 (by rfl) ⟨560438, by rfl⟩ : syracuseStep 747251 = 1120877) B1120877
theorem B747267 : Blo 746329 747267 := bstep (se 1 (by rfl) ⟨560450, by rfl⟩ : syracuseStep 747267 = 1120901) B1120901
theorem B1009427 : Blo 746329 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B747283 : Blo 746329 747283 := bstep (se 1 (by rfl) ⟨560462, by rfl⟩ : syracuseStep 747283 = 1120925) B1120925
theorem B747299 : Blo 746329 747299 := bstep (se 1 (by rfl) ⟨560474, by rfl⟩ : syracuseStep 747299 = 1120949) B1120949
theorem B747315 : Blo 746329 747315 := bstep (se 1 (by rfl) ⟨560486, by rfl⟩ : syracuseStep 747315 = 1120973) B1120973
theorem B747331 : Blo 746329 747331 := bstep (se 1 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 747331 = 1120997) B1120997
theorem B1894225 : Blo 746329 1894225 := bstep (se 2 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 1894225 = 1420669) B1420669
theorem B747347 : Blo 746329 747347 := bstep (se 1 (by rfl) ⟨560510, by rfl⟩ : syracuseStep 747347 = 1121021) B1121021
theorem B747363 : Blo 746329 747363 := bstep (se 1 (by rfl) ⟨560522, by rfl⟩ : syracuseStep 747363 = 1121045) B1121045
theorem B747379 : Blo 746329 747379 := bstep (se 1 (by rfl) ⟨560534, by rfl⟩ : syracuseStep 747379 = 1121069) B1121069
theorem B747395 : Blo 746329 747395 := bstep (se 1 (by rfl) ⟨560546, by rfl⟩ : syracuseStep 747395 = 1121093) B1121093
theorem B747411 : Blo 746329 747411 := bstep (se 1 (by rfl) ⟨560558, by rfl⟩ : syracuseStep 747411 = 1121117) B1121117
theorem B747427 : Blo 746329 747427 := bstep (se 1 (by rfl) ⟨560570, by rfl⟩ : syracuseStep 747427 = 1121141) B1121141
theorem B747443 : Blo 746329 747443 := bstep (se 1 (by rfl) ⟨560582, by rfl⟩ : syracuseStep 747443 = 1121165) B1121165
theorem B747459 : Blo 746329 747459 := bstep (se 1 (by rfl) ⟨560594, by rfl⟩ : syracuseStep 747459 = 1121189) B1121189
theorem B747475 : Blo 746329 747475 := bstep (se 1 (by rfl) ⟨560606, by rfl⟩ : syracuseStep 747475 = 1121213) B1121213
theorem B747491 : Blo 746329 747491 := bstep (se 1 (by rfl) ⟨560618, by rfl⟩ : syracuseStep 747491 = 1121237) B1121237
theorem B10250225 : Blo 746329 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B747507 : Blo 746329 747507 := bstep (se 1 (by rfl) ⟨560630, by rfl⟩ : syracuseStep 747507 = 1121261) B1121261
theorem B747523 : Blo 746329 747523 := bstep (se 1 (by rfl) ⟨560642, by rfl⟩ : syracuseStep 747523 = 1121285) B1121285
theorem B747539 : Blo 746329 747539 := bstep (se 1 (by rfl) ⟨560654, by rfl⟩ : syracuseStep 747539 = 1121309) B1121309
theorem B747555 : Blo 746329 747555 := bstep (se 1 (by rfl) ⟨560666, by rfl⟩ : syracuseStep 747555 = 1121333) B1121333
theorem B747571 : Blo 746329 747571 := bstep (se 1 (by rfl) ⟨560678, by rfl⟩ : syracuseStep 747571 = 1121357) B1121357
theorem B747587 : Blo 746329 747587 := bstep (se 1 (by rfl) ⟨560690, by rfl⟩ : syracuseStep 747587 = 1121381) B1121381
theorem B747603 : Blo 746329 747603 := bstep (se 1 (by rfl) ⟨560702, by rfl⟩ : syracuseStep 747603 = 1121405) B1121405
theorem B747619 : Blo 746329 747619 := bstep (se 1 (by rfl) ⟨560714, by rfl⟩ : syracuseStep 747619 = 1121429) B1121429
theorem B1894499 : Blo 746329 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B3598435 : Blo 746329 3598435 := bstep (se 1 (by rfl) ⟨2698826, by rfl⟩ : syracuseStep 3598435 = 5397653) B5397653
theorem B747635 : Blo 746329 747635 := bstep (se 1 (by rfl) ⟨560726, by rfl⟩ : syracuseStep 747635 = 1121453) B1121453
theorem B747651 : Blo 746329 747651 := bstep (se 1 (by rfl) ⟨560738, by rfl⟩ : syracuseStep 747651 = 1121477) B1121477
theorem B747667 : Blo 746329 747667 := bstep (se 1 (by rfl) ⟨560750, by rfl⟩ : syracuseStep 747667 = 1121501) B1121501
theorem B747683 : Blo 746329 747683 := bstep (se 1 (by rfl) ⟨560762, by rfl⟩ : syracuseStep 747683 = 1121525) B1121525
theorem B747699 : Blo 746329 747699 := bstep (se 1 (by rfl) ⟨560774, by rfl⟩ : syracuseStep 747699 = 1121549) B1121549
theorem B747715 : Blo 746329 747715 := bstep (se 1 (by rfl) ⟨560786, by rfl⟩ : syracuseStep 747715 = 1121573) B1121573
theorem B747731 : Blo 746329 747731 := bstep (se 1 (by rfl) ⟨560798, by rfl⟩ : syracuseStep 747731 = 1121597) B1121597
theorem B747747 : Blo 746329 747747 := bstep (se 1 (by rfl) ⟨560810, by rfl⟩ : syracuseStep 747747 = 1121621) B1121621
theorem B747763 : Blo 746329 747763 := bstep (se 1 (by rfl) ⟨560822, by rfl⟩ : syracuseStep 747763 = 1121645) B1121645
theorem B747779 : Blo 746329 747779 := bstep (se 1 (by rfl) ⟨560834, by rfl⟩ : syracuseStep 747779 = 1121669) B1121669
theorem B747795 : Blo 746329 747795 := bstep (se 1 (by rfl) ⟨560846, by rfl⟩ : syracuseStep 747795 = 1121693) B1121693
theorem B747811 : Blo 746329 747811 := bstep (se 1 (by rfl) ⟨560858, by rfl⟩ : syracuseStep 747811 = 1121717) B1121717
theorem B1894691 : Blo 746329 1894691 := bstep (se 1 (by rfl) ⟨1421018, by rfl⟩ : syracuseStep 1894691 = 2842037) B2842037
theorem B747827 : Blo 746329 747827 := bstep (se 1 (by rfl) ⟨560870, by rfl⟩ : syracuseStep 747827 = 1121741) B1121741
theorem B747843 : Blo 746329 747843 := bstep (se 1 (by rfl) ⟨560882, by rfl⟩ : syracuseStep 747843 = 1121765) B1121765
theorem B747859 : Blo 746329 747859 := bstep (se 1 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 747859 = 1121789) B1121789
theorem B747875 : Blo 746329 747875 := bstep (se 1 (by rfl) ⟨560906, by rfl⟩ : syracuseStep 747875 = 1121813) B1121813
theorem B747891 : Blo 746329 747891 := bstep (se 1 (by rfl) ⟨560918, by rfl⟩ : syracuseStep 747891 = 1121837) B1121837
theorem B747907 : Blo 746329 747907 := bstep (se 1 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 747907 = 1121861) B1121861
theorem B747923 : Blo 746329 747923 := bstep (se 1 (by rfl) ⟨560942, by rfl⟩ : syracuseStep 747923 = 1121885) B1121885
theorem B747939 : Blo 746329 747939 := bstep (se 1 (by rfl) ⟨560954, by rfl⟩ : syracuseStep 747939 = 1121909) B1121909
theorem B747955 : Blo 746329 747955 := bstep (se 1 (by rfl) ⟨560966, by rfl⟩ : syracuseStep 747955 = 1121933) B1121933
theorem B747971 : Blo 746329 747971 := bstep (se 1 (by rfl) ⟨560978, by rfl⟩ : syracuseStep 747971 = 1121957) B1121957
theorem B747987 : Blo 746329 747987 := bstep (se 1 (by rfl) ⟨560990, by rfl⟩ : syracuseStep 747987 = 1121981) B1121981
theorem B748003 : Blo 746329 748003 := bstep (se 1 (by rfl) ⟨561002, by rfl⟩ : syracuseStep 748003 = 1122005) B1122005
theorem B748019 : Blo 746329 748019 := bstep (se 1 (by rfl) ⟨561014, by rfl⟩ : syracuseStep 748019 = 1122029) B1122029
theorem B748035 : Blo 746329 748035 := bstep (se 1 (by rfl) ⟨561026, by rfl⟩ : syracuseStep 748035 = 1122053) B1122053
theorem B748051 : Blo 746329 748051 := bstep (se 1 (by rfl) ⟨561038, by rfl⟩ : syracuseStep 748051 = 1122077) B1122077
theorem B748067 : Blo 746329 748067 := bstep (se 1 (by rfl) ⟨561050, by rfl⟩ : syracuseStep 748067 = 1122101) B1122101
theorem B748083 : Blo 746329 748083 := bstep (se 1 (by rfl) ⟨561062, by rfl⟩ : syracuseStep 748083 = 1122125) B1122125
theorem B748099 : Blo 746329 748099 := bstep (se 1 (by rfl) ⟨561074, by rfl⟩ : syracuseStep 748099 = 1122149) B1122149
theorem B1796689 : Blo 746329 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B944723 : Blo 746329 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B748115 : Blo 746329 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B748131 : Blo 746329 748131 := bstep (se 1 (by rfl) ⟨561098, by rfl⟩ : syracuseStep 748131 = 1122197) B1122197
theorem B748147 : Blo 746329 748147 := bstep (se 1 (by rfl) ⟨561110, by rfl⟩ : syracuseStep 748147 = 1122221) B1122221
theorem B748163 : Blo 746329 748163 := bstep (se 1 (by rfl) ⟨561122, by rfl⟩ : syracuseStep 748163 = 1122245) B1122245
theorem B748179 : Blo 746329 748179 := bstep (se 1 (by rfl) ⟨561134, by rfl⟩ : syracuseStep 748179 = 1122269) B1122269
theorem B748195 : Blo 746329 748195 := bstep (se 1 (by rfl) ⟨561146, by rfl⟩ : syracuseStep 748195 = 1122293) B1122293
theorem B748211 : Blo 746329 748211 := bstep (se 1 (by rfl) ⟨561158, by rfl⟩ : syracuseStep 748211 = 1122317) B1122317
theorem B748227 : Blo 746329 748227 := bstep (se 1 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 748227 = 1122341) B1122341
theorem B748243 : Blo 746329 748243 := bstep (se 1 (by rfl) ⟨561182, by rfl⟩ : syracuseStep 748243 = 1122365) B1122365
theorem B748259 : Blo 746329 748259 := bstep (se 1 (by rfl) ⟨561194, by rfl⟩ : syracuseStep 748259 = 1122389) B1122389
theorem B748275 : Blo 746329 748275 := bstep (se 1 (by rfl) ⟨561206, by rfl⟩ : syracuseStep 748275 = 1122413) B1122413
theorem B748291 : Blo 746329 748291 := bstep (se 1 (by rfl) ⟨561218, by rfl⟩ : syracuseStep 748291 = 1122437) B1122437
theorem B748307 : Blo 746329 748307 := bstep (se 1 (by rfl) ⟨561230, by rfl⟩ : syracuseStep 748307 = 1122461) B1122461
theorem B748323 : Blo 746329 748323 := bstep (se 1 (by rfl) ⟨561242, by rfl⟩ : syracuseStep 748323 = 1122485) B1122485
theorem B748339 : Blo 746329 748339 := bstep (se 1 (by rfl) ⟨561254, by rfl⟩ : syracuseStep 748339 = 1122509) B1122509
theorem B748355 : Blo 746329 748355 := bstep (se 1 (by rfl) ⟨561266, by rfl⟩ : syracuseStep 748355 = 1122533) B1122533
theorem B748371 : Blo 746329 748371 := bstep (se 1 (by rfl) ⟨561278, by rfl⟩ : syracuseStep 748371 = 1122557) B1122557
theorem B748387 : Blo 746329 748387 := bstep (se 1 (by rfl) ⟨561290, by rfl⟩ : syracuseStep 748387 = 1122581) B1122581
theorem B748403 : Blo 746329 748403 := bstep (se 1 (by rfl) ⟨561302, by rfl⟩ : syracuseStep 748403 = 1122605) B1122605
theorem B748419 : Blo 746329 748419 := bstep (se 1 (by rfl) ⟨561314, by rfl⟩ : syracuseStep 748419 = 1122629) B1122629
theorem B4254605 : Blo 746329 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B748435 : Blo 746329 748435 := bstep (se 1 (by rfl) ⟨561326, by rfl⟩ : syracuseStep 748435 = 1122653) B1122653
theorem B748451 : Blo 746329 748451 := bstep (se 1 (by rfl) ⟨561338, by rfl⟩ : syracuseStep 748451 = 1122677) B1122677
theorem B748467 : Blo 746329 748467 := bstep (se 1 (by rfl) ⟨561350, by rfl⟩ : syracuseStep 748467 = 1122701) B1122701
theorem B748483 : Blo 746329 748483 := bstep (se 1 (by rfl) ⟨561362, by rfl⟩ : syracuseStep 748483 = 1122725) B1122725
theorem B748499 : Blo 746329 748499 := bstep (se 1 (by rfl) ⟨561374, by rfl⟩ : syracuseStep 748499 = 1122749) B1122749
theorem B748515 : Blo 746329 748515 := bstep (se 1 (by rfl) ⟨561386, by rfl⟩ : syracuseStep 748515 = 1122773) B1122773
theorem B748531 : Blo 746329 748531 := bstep (se 1 (by rfl) ⟨561398, by rfl⟩ : syracuseStep 748531 = 1122797) B1122797
theorem B748547 : Blo 746329 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B748563 : Blo 746329 748563 := bstep (se 1 (by rfl) ⟨561422, by rfl⟩ : syracuseStep 748563 = 1122845) B1122845
theorem B748579 : Blo 746329 748579 := bstep (se 1 (by rfl) ⟨561434, by rfl⟩ : syracuseStep 748579 = 1122869) B1122869
theorem B748595 : Blo 746329 748595 := bstep (se 1 (by rfl) ⟨561446, by rfl⟩ : syracuseStep 748595 = 1122893) B1122893
theorem B748611 : Blo 746329 748611 := bstep (se 1 (by rfl) ⟨561458, by rfl⟩ : syracuseStep 748611 = 1122917) B1122917
theorem B748627 : Blo 746329 748627 := bstep (se 1 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 748627 = 1122941) B1122941
theorem B748643 : Blo 746329 748643 := bstep (se 1 (by rfl) ⟨561482, by rfl⟩ : syracuseStep 748643 = 1122965) B1122965
theorem B748659 : Blo 746329 748659 := bstep (se 1 (by rfl) ⟨561494, by rfl⟩ : syracuseStep 748659 = 1122989) B1122989
theorem B748675 : Blo 746329 748675 := bstep (se 1 (by rfl) ⟨561506, by rfl⟩ : syracuseStep 748675 = 1123013) B1123013
theorem B748691 : Blo 746329 748691 := bstep (se 1 (by rfl) ⟨561518, by rfl⟩ : syracuseStep 748691 = 1123037) B1123037
theorem B748707 : Blo 746329 748707 := bstep (se 1 (by rfl) ⟨561530, by rfl⟩ : syracuseStep 748707 = 1123061) B1123061
theorem B3796145 : Blo 746329 3796145 := bstep (se 2 (by rfl) ⟨1423554, by rfl⟩ : syracuseStep 3796145 = 2847109) B2847109
theorem B748723 : Blo 746329 748723 := bstep (se 1 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 748723 = 1123085) B1123085
theorem B748739 : Blo 746329 748739 := bstep (se 1 (by rfl) ⟨561554, by rfl⟩ : syracuseStep 748739 = 1123109) B1123109
theorem B1895633 : Blo 746329 1895633 := bstep (se 2 (by rfl) ⟨710862, by rfl⟩ : syracuseStep 1895633 = 1421725) B1421725
theorem B748755 : Blo 746329 748755 := bstep (se 1 (by rfl) ⟨561566, by rfl⟩ : syracuseStep 748755 = 1123133) B1123133
theorem B748771 : Blo 746329 748771 := bstep (se 1 (by rfl) ⟨561578, by rfl⟩ : syracuseStep 748771 = 1123157) B1123157
theorem B748787 : Blo 746329 748787 := bstep (se 1 (by rfl) ⟨561590, by rfl⟩ : syracuseStep 748787 = 1123181) B1123181
theorem B748803 : Blo 746329 748803 := bstep (se 1 (by rfl) ⟨561602, by rfl⟩ : syracuseStep 748803 = 1123205) B1123205
theorem B1895683 : Blo 746329 1895683 := bstep (se 1 (by rfl) ⟨1421762, by rfl⟩ : syracuseStep 1895683 = 2843525) B2843525
theorem B945427 : Blo 746329 945427 := bstep (se 1 (by rfl) ⟨709070, by rfl⟩ : syracuseStep 945427 = 1418141) B1418141
theorem B748819 : Blo 746329 748819 := bstep (se 1 (by rfl) ⟨561614, by rfl⟩ : syracuseStep 748819 = 1123229) B1123229
theorem B748835 : Blo 746329 748835 := bstep (se 1 (by rfl) ⟨561626, by rfl⟩ : syracuseStep 748835 = 1123253) B1123253
theorem B748851 : Blo 746329 748851 := bstep (se 1 (by rfl) ⟨561638, by rfl⟩ : syracuseStep 748851 = 1123277) B1123277
theorem B748867 : Blo 746329 748867 := bstep (se 1 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 748867 = 1123301) B1123301
theorem B748883 : Blo 746329 748883 := bstep (se 1 (by rfl) ⟨561662, by rfl⟩ : syracuseStep 748883 = 1123325) B1123325
theorem B748899 : Blo 746329 748899 := bstep (se 1 (by rfl) ⟨561674, by rfl⟩ : syracuseStep 748899 = 1123349) B1123349
theorem B945523 : Blo 746329 945523 := bstep (se 1 (by rfl) ⟨709142, by rfl⟩ : syracuseStep 945523 = 1418285) B1418285
theorem B748915 : Blo 746329 748915 := bstep (se 1 (by rfl) ⟨561686, by rfl⟩ : syracuseStep 748915 = 1123373) B1123373
theorem B748931 : Blo 746329 748931 := bstep (se 1 (by rfl) ⟨561698, by rfl⟩ : syracuseStep 748931 = 1123397) B1123397
theorem B1895825 : Blo 746329 1895825 := bstep (se 2 (by rfl) ⟨710934, by rfl⟩ : syracuseStep 1895825 = 1421869) B1421869
theorem B748947 : Blo 746329 748947 := bstep (se 1 (by rfl) ⟨561710, by rfl⟩ : syracuseStep 748947 = 1123421) B1123421
theorem B748963 : Blo 746329 748963 := bstep (se 1 (by rfl) ⟨561722, by rfl⟩ : syracuseStep 748963 = 1123445) B1123445
theorem B748979 : Blo 746329 748979 := bstep (se 1 (by rfl) ⟨561734, by rfl⟩ : syracuseStep 748979 = 1123469) B1123469
theorem B748995 : Blo 746329 748995 := bstep (se 1 (by rfl) ⟨561746, by rfl⟩ : syracuseStep 748995 = 1123493) B1123493
theorem B749011 : Blo 746329 749011 := bstep (se 1 (by rfl) ⟨561758, by rfl⟩ : syracuseStep 749011 = 1123517) B1123517
theorem B19131875 : Blo 746329 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B749027 : Blo 746329 749027 := bstep (se 1 (by rfl) ⟨561770, by rfl⟩ : syracuseStep 749027 = 1123541) B1123541
theorem B749043 : Blo 746329 749043 := bstep (se 1 (by rfl) ⟨561782, by rfl⟩ : syracuseStep 749043 = 1123565) B1123565
theorem B749059 : Blo 746329 749059 := bstep (se 1 (by rfl) ⟨561794, by rfl⟩ : syracuseStep 749059 = 1123589) B1123589
theorem B749075 : Blo 746329 749075 := bstep (se 1 (by rfl) ⟨561806, by rfl⟩ : syracuseStep 749075 = 1123613) B1123613
theorem B749091 : Blo 746329 749091 := bstep (se 1 (by rfl) ⟨561818, by rfl⟩ : syracuseStep 749091 = 1123637) B1123637
theorem B749107 : Blo 746329 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B749123 : Blo 746329 749123 := bstep (se 1 (by rfl) ⟨561842, by rfl⟩ : syracuseStep 749123 = 1123685) B1123685
theorem B749139 : Blo 746329 749139 := bstep (se 1 (by rfl) ⟨561854, by rfl⟩ : syracuseStep 749139 = 1123709) B1123709
theorem B749155 : Blo 746329 749155 := bstep (se 1 (by rfl) ⟨561866, by rfl⟩ : syracuseStep 749155 = 1123733) B1123733
theorem B749171 : Blo 746329 749171 := bstep (se 1 (by rfl) ⟨561878, by rfl⟩ : syracuseStep 749171 = 1123757) B1123757
theorem B2158211 : Blo 746329 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B749187 : Blo 746329 749187 := bstep (se 1 (by rfl) ⟨561890, by rfl⟩ : syracuseStep 749187 = 1123781) B1123781
theorem B749203 : Blo 746329 749203 := bstep (se 1 (by rfl) ⟨561902, by rfl⟩ : syracuseStep 749203 = 1123805) B1123805
theorem B749219 : Blo 746329 749219 := bstep (se 1 (by rfl) ⟨561914, by rfl⟩ : syracuseStep 749219 = 1123829) B1123829
theorem B749235 : Blo 746329 749235 := bstep (se 1 (by rfl) ⟨561926, by rfl⟩ : syracuseStep 749235 = 1123853) B1123853
theorem B749251 : Blo 746329 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B749267 : Blo 746329 749267 := bstep (se 1 (by rfl) ⟨561950, by rfl⟩ : syracuseStep 749267 = 1123901) B1123901
theorem B749283 : Blo 746329 749283 := bstep (se 1 (by rfl) ⟨561962, by rfl⟩ : syracuseStep 749283 = 1123925) B1123925
theorem B1732337 : Blo 746329 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B749299 : Blo 746329 749299 := bstep (se 1 (by rfl) ⟨561974, by rfl⟩ : syracuseStep 749299 = 1123949) B1123949
theorem B749315 : Blo 746329 749315 := bstep (se 1 (by rfl) ⟨561986, by rfl⟩ : syracuseStep 749315 = 1123973) B1123973
theorem B749331 : Blo 746329 749331 := bstep (se 1 (by rfl) ⟨561998, by rfl⟩ : syracuseStep 749331 = 1123997) B1123997
theorem B749347 : Blo 746329 749347 := bstep (se 1 (by rfl) ⟨562010, by rfl⟩ : syracuseStep 749347 = 1124021) B1124021
theorem B4255537 : Blo 746329 4255537 := bstep (se 2 (by rfl) ⟨1595826, by rfl⟩ : syracuseStep 4255537 = 3191653) B3191653
theorem B1601329 : Blo 746329 1601329 := bstep (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) B1200997
theorem B749363 : Blo 746329 749363 := bstep (se 1 (by rfl) ⟨562022, by rfl⟩ : syracuseStep 749363 = 1124045) B1124045
theorem B749379 : Blo 746329 749379 := bstep (se 1 (by rfl) ⟨562034, by rfl⟩ : syracuseStep 749379 = 1124069) B1124069
theorem B2158417 : Blo 746329 2158417 := bstep (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) B1618813
theorem B749395 : Blo 746329 749395 := bstep (se 1 (by rfl) ⟨562046, by rfl⟩ : syracuseStep 749395 = 1124093) B1124093
theorem B2518883 : Blo 746329 2518883 := bstep (se 1 (by rfl) ⟨1889162, by rfl⟩ : syracuseStep 2518883 = 3778325) B3778325
theorem B946019 : Blo 746329 946019 := bstep (se 1 (by rfl) ⟨709514, by rfl⟩ : syracuseStep 946019 = 1419029) B1419029
theorem B749411 : Blo 746329 749411 := bstep (se 1 (by rfl) ⟨562058, by rfl⟩ : syracuseStep 749411 = 1124117) B1124117
theorem B749427 : Blo 746329 749427 := bstep (se 1 (by rfl) ⟨562070, by rfl⟩ : syracuseStep 749427 = 1124141) B1124141
theorem B749443 : Blo 746329 749443 := bstep (se 1 (by rfl) ⟨562082, by rfl⟩ : syracuseStep 749443 = 1124165) B1124165
theorem B749459 : Blo 746329 749459 := bstep (se 1 (by rfl) ⟨562094, by rfl⟩ : syracuseStep 749459 = 1124189) B1124189
theorem B749475 : Blo 746329 749475 := bstep (se 1 (by rfl) ⟨562106, by rfl⟩ : syracuseStep 749475 = 1124213) B1124213
theorem B749491 : Blo 746329 749491 := bstep (se 1 (by rfl) ⟨562118, by rfl⟩ : syracuseStep 749491 = 1124237) B1124237
theorem B749507 : Blo 746329 749507 := bstep (se 1 (by rfl) ⟨562130, by rfl⟩ : syracuseStep 749507 = 1124261) B1124261
theorem B749523 : Blo 746329 749523 := bstep (se 1 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 749523 = 1124285) B1124285
theorem B749539 : Blo 746329 749539 := bstep (se 1 (by rfl) ⟨562154, by rfl⟩ : syracuseStep 749539 = 1124309) B1124309
theorem B749555 : Blo 746329 749555 := bstep (se 1 (by rfl) ⟨562166, by rfl⟩ : syracuseStep 749555 = 1124333) B1124333
theorem B749571 : Blo 746329 749571 := bstep (se 1 (by rfl) ⟨562178, by rfl⟩ : syracuseStep 749571 = 1124357) B1124357
theorem B749587 : Blo 746329 749587 := bstep (se 1 (by rfl) ⟨562190, by rfl⟩ : syracuseStep 749587 = 1124381) B1124381
theorem B749603 : Blo 746329 749603 := bstep (se 1 (by rfl) ⟨562202, by rfl⟩ : syracuseStep 749603 = 1124405) B1124405
theorem B749619 : Blo 746329 749619 := bstep (se 1 (by rfl) ⟨562214, by rfl⟩ : syracuseStep 749619 = 1124429) B1124429
theorem B749635 : Blo 746329 749635 := bstep (se 1 (by rfl) ⟨562226, by rfl⟩ : syracuseStep 749635 = 1124453) B1124453
theorem B2125901 : Blo 746329 2125901 := bstep (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) B797213
theorem B749651 : Blo 746329 749651 := bstep (se 1 (by rfl) ⟨562238, by rfl⟩ : syracuseStep 749651 = 1124477) B1124477
theorem B749667 : Blo 746329 749667 := bstep (se 1 (by rfl) ⟨562250, by rfl⟩ : syracuseStep 749667 = 1124501) B1124501
theorem B2519153 : Blo 746329 2519153 := bstep (se 2 (by rfl) ⟨944682, by rfl⟩ : syracuseStep 2519153 = 1889365) B1889365
theorem B749683 : Blo 746329 749683 := bstep (se 1 (by rfl) ⟨562262, by rfl⟩ : syracuseStep 749683 = 1124525) B1124525
theorem B749699 : Blo 746329 749699 := bstep (se 1 (by rfl) ⟨562274, by rfl⟩ : syracuseStep 749699 = 1124549) B1124549
theorem B749715 : Blo 746329 749715 := bstep (se 1 (by rfl) ⟨562286, by rfl⟩ : syracuseStep 749715 = 1124573) B1124573
theorem B749731 : Blo 746329 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B2846897 : Blo 746329 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B749747 : Blo 746329 749747 := bstep (se 1 (by rfl) ⟨562310, by rfl⟩ : syracuseStep 749747 = 1124621) B1124621
theorem B749763 : Blo 746329 749763 := bstep (se 1 (by rfl) ⟨562322, by rfl⟩ : syracuseStep 749763 = 1124645) B1124645
theorem B749779 : Blo 746329 749779 := bstep (se 1 (by rfl) ⟨562334, by rfl⟩ : syracuseStep 749779 = 1124669) B1124669
theorem B749795 : Blo 746329 749795 := bstep (se 1 (by rfl) ⟨562346, by rfl⟩ : syracuseStep 749795 = 1124693) B1124693
theorem B749811 : Blo 746329 749811 := bstep (se 1 (by rfl) ⟨562358, by rfl⟩ : syracuseStep 749811 = 1124717) B1124717
theorem B2126083 : Blo 746329 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B749827 : Blo 746329 749827 := bstep (se 1 (by rfl) ⟨562370, by rfl⟩ : syracuseStep 749827 = 1124741) B1124741
theorem B749843 : Blo 746329 749843 := bstep (se 1 (by rfl) ⟨562382, by rfl⟩ : syracuseStep 749843 = 1124765) B1124765
theorem B749859 : Blo 746329 749859 := bstep (se 1 (by rfl) ⟨562394, by rfl⟩ : syracuseStep 749859 = 1124789) B1124789
theorem B749875 : Blo 746329 749875 := bstep (se 1 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 749875 = 1124813) B1124813
theorem B749891 : Blo 746329 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B749907 : Blo 746329 749907 := bstep (se 1 (by rfl) ⟨562430, by rfl⟩ : syracuseStep 749907 = 1124861) B1124861
theorem B749923 : Blo 746329 749923 := bstep (se 1 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 749923 = 1124885) B1124885
theorem B1896817 : Blo 746329 1896817 := bstep (se 2 (by rfl) ⟨711306, by rfl⟩ : syracuseStep 1896817 = 1422613) B1422613
theorem B749939 : Blo 746329 749939 := bstep (se 1 (by rfl) ⟨562454, by rfl⟩ : syracuseStep 749939 = 1124909) B1124909
theorem B749955 : Blo 746329 749955 := bstep (se 1 (by rfl) ⟨562466, by rfl⟩ : syracuseStep 749955 = 1124933) B1124933
theorem B749971 : Blo 746329 749971 := bstep (se 1 (by rfl) ⟨562478, by rfl⟩ : syracuseStep 749971 = 1124957) B1124957
theorem B2126243 : Blo 746329 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B749987 : Blo 746329 749987 := bstep (se 1 (by rfl) ⟨562490, by rfl⟩ : syracuseStep 749987 = 1124981) B1124981
theorem B2879921 : Blo 746329 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B750003 : Blo 746329 750003 := bstep (se 1 (by rfl) ⟨562502, by rfl⟩ : syracuseStep 750003 = 1125005) B1125005
theorem B750019 : Blo 746329 750019 := bstep (se 1 (by rfl) ⟨562514, by rfl⟩ : syracuseStep 750019 = 1125029) B1125029
theorem B750035 : Blo 746329 750035 := bstep (se 1 (by rfl) ⟨562526, by rfl⟩ : syracuseStep 750035 = 1125053) B1125053
theorem B750051 : Blo 746329 750051 := bstep (se 1 (by rfl) ⟨562538, by rfl⟩ : syracuseStep 750051 = 1125077) B1125077
theorem B750067 : Blo 746329 750067 := bstep (se 1 (by rfl) ⟨562550, by rfl⟩ : syracuseStep 750067 = 1125101) B1125101
theorem B750083 : Blo 746329 750083 := bstep (se 1 (by rfl) ⟨562562, by rfl⟩ : syracuseStep 750083 = 1125125) B1125125
theorem B750099 : Blo 746329 750099 := bstep (se 1 (by rfl) ⟨562574, by rfl⟩ : syracuseStep 750099 = 1125149) B1125149
theorem B946723 : Blo 746329 946723 := bstep (se 1 (by rfl) ⟨710042, by rfl⟩ : syracuseStep 946723 = 1420085) B1420085
theorem B750115 : Blo 746329 750115 := bstep (se 1 (by rfl) ⟨562586, by rfl⟩ : syracuseStep 750115 = 1125173) B1125173
theorem B750131 : Blo 746329 750131 := bstep (se 1 (by rfl) ⟨562598, by rfl⟩ : syracuseStep 750131 = 1125197) B1125197
theorem B750147 : Blo 746329 750147 := bstep (se 1 (by rfl) ⟨562610, by rfl⟩ : syracuseStep 750147 = 1125221) B1125221
theorem B750163 : Blo 746329 750163 := bstep (se 1 (by rfl) ⟨562622, by rfl⟩ : syracuseStep 750163 = 1125245) B1125245
theorem B3797603 : Blo 746329 3797603 := bstep (se 1 (by rfl) ⟨2848202, by rfl⟩ : syracuseStep 3797603 = 5696405) B5696405
theorem B750179 : Blo 746329 750179 := bstep (se 1 (by rfl) ⟨562634, by rfl⟩ : syracuseStep 750179 = 1125269) B1125269
theorem B1733233 : Blo 746329 1733233 := bstep (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) B1299925
theorem B750195 : Blo 746329 750195 := bstep (se 1 (by rfl) ⟨562646, by rfl⟩ : syracuseStep 750195 = 1125293) B1125293
theorem B946819 : Blo 746329 946819 := bstep (se 1 (by rfl) ⟨710114, by rfl⟩ : syracuseStep 946819 = 1420229) B1420229
theorem B1897091 : Blo 746329 1897091 := bstep (se 1 (by rfl) ⟨1422818, by rfl⟩ : syracuseStep 1897091 = 2845637) B2845637
theorem B750211 : Blo 746329 750211 := bstep (se 1 (by rfl) ⟨562658, by rfl⟩ : syracuseStep 750211 = 1125317) B1125317
theorem B2519693 : Blo 746329 2519693 := bstep (se 3 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 2519693 = 944885) B944885
theorem B750227 : Blo 746329 750227 := bstep (se 1 (by rfl) ⟨562670, by rfl⟩ : syracuseStep 750227 = 1125341) B1125341
theorem B750243 : Blo 746329 750243 := bstep (se 1 (by rfl) ⟨562682, by rfl⟩ : syracuseStep 750243 = 1125365) B1125365
theorem B750259 : Blo 746329 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B2519747 : Blo 746329 2519747 := bstep (se 1 (by rfl) ⟨1889810, by rfl⟩ : syracuseStep 2519747 = 3779621) B3779621
theorem B750275 : Blo 746329 750275 := bstep (se 1 (by rfl) ⟨562706, by rfl⟩ : syracuseStep 750275 = 1125413) B1125413
theorem B1012433 : Blo 746329 1012433 := bstep (se 2 (by rfl) ⟨379662, by rfl⟩ : syracuseStep 1012433 = 759325) B759325
theorem B750291 : Blo 746329 750291 := bstep (se 1 (by rfl) ⟨562718, by rfl⟩ : syracuseStep 750291 = 1125437) B1125437
theorem B750307 : Blo 746329 750307 := bstep (se 1 (by rfl) ⟨562730, by rfl⟩ : syracuseStep 750307 = 1125461) B1125461
theorem B750323 : Blo 746329 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B8090381 : Blo 746329 8090381 := bstep (se 3 (by rfl) ⟨1516946, by rfl⟩ : syracuseStep 8090381 = 3033893) B3033893
theorem B1897283 : Blo 746329 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B22999949 : Blo 746329 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B2520017 : Blo 746329 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B9597923 : Blo 746329 9597923 := bstep (se 1 (by rfl) ⟨7198442, by rfl⟩ : syracuseStep 9597923 = 14396885) B14396885
theorem B947315 : Blo 746329 947315 := bstep (se 1 (by rfl) ⟨710486, by rfl⟩ : syracuseStep 947315 = 1420973) B1420973
theorem B4256995 : Blo 746329 4256995 := bstep (se 1 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 4256995 = 6385493) B6385493
theorem B15398257 : Blo 746329 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B3798413 : Blo 746329 3798413 := bstep (se 3 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 3798413 = 1424405) B1424405
theorem B1013185 : Blo 746329 1013185 := bstep (se 2 (by rfl) ⟨379944, by rfl⟩ : syracuseStep 1013185 = 759889) B759889
theorem B2127313 : Blo 746329 2127313 := bstep (se 2 (by rfl) ⟨797742, by rfl⟩ : syracuseStep 2127313 = 1595485) B1595485
theorem B1799651 : Blo 746329 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B2520557 : Blo 746329 2520557 := bstep (se 3 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 2520557 = 945209) B945209
theorem B2520611 : Blo 746329 2520611 := bstep (se 1 (by rfl) ⟨1890458, by rfl⟩ : syracuseStep 2520611 = 3780917) B3780917
theorem B2848355 : Blo 746329 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B4257521 : Blo 746329 4257521 := bstep (se 2 (by rfl) ⟨1596570, by rfl⟩ : syracuseStep 4257521 = 3193141) B3193141
theorem B1898225 : Blo 746329 1898225 := bstep (se 2 (by rfl) ⟨711834, by rfl⟩ : syracuseStep 1898225 = 1423669) B1423669
theorem B1898275 : Blo 746329 1898275 := bstep (se 1 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 1898275 = 2847413) B2847413
theorem B2520881 : Blo 746329 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B948019 : Blo 746329 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B1800035 : Blo 746329 1800035 := bstep (se 1 (by rfl) ⟨1350026, by rfl⟩ : syracuseStep 1800035 = 2700053) B2700053
theorem B948115 : Blo 746329 948115 := bstep (se 1 (by rfl) ⟨711086, by rfl⟩ : syracuseStep 948115 = 1422173) B1422173
theorem B3602339 : Blo 746329 3602339 := bstep (se 1 (by rfl) ⟨2701754, by rfl⟩ : syracuseStep 3602339 = 5403509) B5403509
theorem B1898417 : Blo 746329 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B4782149 : Blo 746329 4782149 := bstep (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) B896653
theorem B1800323 : Blo 746329 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B2521421 : Blo 746329 2521421 := bstep (se 3 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 2521421 = 945533) B945533
theorem B2521475 : Blo 746329 2521475 := bstep (se 1 (by rfl) ⟨1891106, by rfl⟩ : syracuseStep 2521475 = 3782213) B3782213
theorem B948611 : Blo 746329 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B2161133 : Blo 746329 2161133 := bstep (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) B810425
theorem B1800785 : Blo 746329 1800785 := bstep (se 2 (by rfl) ⟨675294, by rfl⟩ : syracuseStep 1800785 = 1350589) B1350589
theorem B2521745 : Blo 746329 2521745 := bstep (se 2 (by rfl) ⟨945654, by rfl⟩ : syracuseStep 2521745 = 1891309) B1891309
theorem B2128589 : Blo 746329 2128589 := bstep (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) B798221
theorem B1440515 : Blo 746329 1440515 := bstep (se 1 (by rfl) ⟨1080386, by rfl⟩ : syracuseStep 1440515 = 2160773) B2160773
theorem B2128771 : Blo 746329 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B5110661 : Blo 746329 5110661 := bstep (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) B958249
theorem B2128817 : Blo 746329 2128817 := bstep (se 2 (by rfl) ⟨798306, by rfl⟩ : syracuseStep 2128817 = 1596613) B1596613
theorem B949315 : Blo 746329 949315 := bstep (se 1 (by rfl) ⟨711986, by rfl⟩ : syracuseStep 949315 = 1423973) B1423973
theorem B4258979 : Blo 746329 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B949411 : Blo 746329 949411 := bstep (se 1 (by rfl) ⟨712058, by rfl⟩ : syracuseStep 949411 = 1424117) B1424117
theorem B2522285 : Blo 746329 2522285 := bstep (se 3 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 2522285 = 945857) B945857
theorem B2522339 : Blo 746329 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B1801457 : Blo 746329 1801457 := bstep (se 2 (by rfl) ⟨675546, by rfl⟩ : syracuseStep 1801457 = 1351093) B1351093
theorem B8519093 : Blo 746329 8519093 := bstep (se 5 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 8519093 = 798665) B798665
theorem B2522609 : Blo 746329 2522609 := bstep (se 2 (by rfl) ⟨945978, by rfl⟩ : syracuseStep 2522609 = 1891957) B1891957
theorem B5111429 : Blo 746329 5111429 := bstep (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) B958393
theorem B3604337 : Blo 746329 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B2392537 : Blo 746329 2392537 := bstep (se 2 (by rfl) ⟨897201, by rfl⟩ : syracuseStep 2392537 = 1794403) B1794403
theorem B1081817 : Blo 746329 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B6062597 : Blo 746329 6062597 := bstep (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) B1136737
theorem B1704577 : Blo 746329 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B4784791 : Blo 746329 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B2130583 : Blo 746329 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B2523851 : Blo 746329 2523851 := bstep (se 1 (by rfl) ⟨1892888, by rfl⟩ : syracuseStep 2523851 = 3785777) B3785777
theorem B2524121 : Blo 746329 2524121 := bstep (se 2 (by rfl) ⟨946545, by rfl⟩ : syracuseStep 2524121 = 1893091) B1893091
theorem B5670161 : Blo 746329 5670161 := bstep (se 2 (by rfl) ⟨2126310, by rfl⟩ : syracuseStep 5670161 = 4252621) B4252621
theorem B1082903 : Blo 746329 1082903 := bstep (se 1 (by rfl) ⟨812177, by rfl⟩ : syracuseStep 1082903 = 1624355) B1624355
theorem B1443379 : Blo 746329 1443379 := bstep (se 1 (by rfl) ⟨1082534, by rfl⟩ : syracuseStep 1443379 = 2165069) B2165069
theorem B2524823 : Blo 746329 2524823 := bstep (se 1 (by rfl) ⟨1893617, by rfl⟩ : syracuseStep 2524823 = 3787235) B3787235
theorem B2557619 : Blo 746329 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B2131915 : Blo 746329 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B2426945 : Blo 746329 2426945 := bstep (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) B1820209
theorem B2525363 : Blo 746329 2525363 := bstep (se 1 (by rfl) ⟨1894022, by rfl⟩ : syracuseStep 2525363 = 3788045) B3788045
theorem B2394305 : Blo 746329 2394305 := bstep (se 2 (by rfl) ⟨897864, by rfl⟩ : syracuseStep 2394305 = 1795729) B1795729
theorem B2132189 : Blo 746329 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B985483 : Blo 746329 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B2525633 : Blo 746329 2525633 := bstep (se 2 (by rfl) ⟨947112, by rfl⟩ : syracuseStep 2525633 = 1894225) B1894225
theorem B2132531 : Blo 746329 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B2526173 : Blo 746329 2526173 := bstep (se 3 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 2526173 = 947315) B947315
theorem B6491153 : Blo 746329 6491153 := bstep (se 2 (by rfl) ⟨2434182, by rfl⟩ : syracuseStep 6491153 = 4868365) B4868365
theorem B756811 : Blo 746329 756811 := bstep (se 1 (by rfl) ⟨567608, by rfl⟩ : syracuseStep 756811 = 1135217) B1135217
theorem B4787275 : Blo 746329 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B2395585 : Blo 746329 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B2428481 : Blo 746329 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1347187 : Blo 746329 1347187 := bstep (se 1 (by rfl) ⟨1010390, by rfl⟩ : syracuseStep 1347187 = 2020781) B2020781
theorem B12160813 : Blo 746329 12160813 := bstep (se 3 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 12160813 = 4560305) B4560305
theorem B3411857 : Blo 746329 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B15175603 : Blo 746329 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B2527307 : Blo 746329 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B2527577 : Blo 746329 2527577 := bstep (se 2 (by rfl) ⟨947841, by rfl⟩ : syracuseStep 2527577 = 1895683) B1895683
theorem B4264285 : Blo 746329 4264285 := bstep (se 3 (by rfl) ⟨799553, by rfl⟩ : syracuseStep 4264285 = 1599107) B1599107
theorem B2920835 : Blo 746329 2920835 := bstep (se 1 (by rfl) ⟨2190626, by rfl⟩ : syracuseStep 2920835 = 4381253) B4381253
theorem B2134603 : Blo 746329 2134603 := bstep (se 1 (by rfl) ⟨1600952, by rfl⟩ : syracuseStep 2134603 = 3201905) B3201905
theorem B2396765 : Blo 746329 2396765 := bstep (se 3 (by rfl) ⟨449393, by rfl⟩ : syracuseStep 2396765 = 898787) B898787
theorem B2691805 : Blo 746329 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B758603 : Blo 746329 758603 := bstep (se 1 (by rfl) ⟨568952, by rfl⟩ : syracuseStep 758603 = 1137905) B1137905
theorem B2528279 : Blo 746329 2528279 := bstep (se 1 (by rfl) ⟨1896209, by rfl⟩ : syracuseStep 2528279 = 3792419) B3792419
theorem B5674049 : Blo 746329 5674049 := bstep (se 2 (by rfl) ⟨2127768, by rfl⟩ : syracuseStep 5674049 = 4255537) B4255537
theorem B2135105 : Blo 746329 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B1119563 : Blo 746329 1119563 := bstep (se 1 (by rfl) ⟨839672, by rfl⟩ : syracuseStep 1119563 = 1679345) B1679345
theorem B1119575 : Blo 746329 1119575 := bstep (se 1 (by rfl) ⟨839681, by rfl⟩ : syracuseStep 1119575 = 1679363) B1679363
theorem B4560229 : Blo 746329 4560229 := bstep (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) B855043
theorem B759179 : Blo 746329 759179 := bstep (se 1 (by rfl) ⟨569384, by rfl⟩ : syracuseStep 759179 = 1138769) B1138769
theorem B2135447 : Blo 746329 2135447 := bstep (se 1 (by rfl) ⟨1601585, by rfl⟩ : syracuseStep 2135447 = 3203171) B3203171
theorem B1119641 : Blo 746329 1119641 := bstep (se 2 (by rfl) ⟨419865, by rfl⟩ : syracuseStep 1119641 = 839731) B839731
theorem B1119755 : Blo 746329 1119755 := bstep (se 1 (by rfl) ⟨839816, by rfl⟩ : syracuseStep 1119755 = 1679633) B1679633
theorem B1119767 : Blo 746329 1119767 := bstep (se 1 (by rfl) ⟨839825, by rfl⟩ : syracuseStep 1119767 = 1679651) B1679651
theorem B2528819 : Blo 746329 2528819 := bstep (se 1 (by rfl) ⟨1896614, by rfl⟩ : syracuseStep 2528819 = 3793229) B3793229
theorem B1480279 : Blo 746329 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B1119833 : Blo 746329 1119833 := bstep (se 2 (by rfl) ⟨419937, by rfl⟩ : syracuseStep 1119833 = 839875) B839875
theorem B1119947 : Blo 746329 1119947 := bstep (se 1 (by rfl) ⟨839960, by rfl⟩ : syracuseStep 1119947 = 1679921) B1679921
theorem B1119959 : Blo 746329 1119959 := bstep (se 1 (by rfl) ⟨839969, by rfl⟩ : syracuseStep 1119959 = 1679939) B1679939
theorem B1120025 : Blo 746329 1120025 := bstep (se 2 (by rfl) ⟨420009, by rfl⟩ : syracuseStep 1120025 = 840019) B840019
theorem B2529089 : Blo 746329 2529089 := bstep (se 2 (by rfl) ⟨948408, by rfl⟩ : syracuseStep 2529089 = 1896817) B1896817
theorem B4560715 : Blo 746329 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B1120139 : Blo 746329 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B1120151 : Blo 746329 1120151 := bstep (se 1 (by rfl) ⟨840113, by rfl⟩ : syracuseStep 1120151 = 1680227) B1680227
theorem B1120217 : Blo 746329 1120217 := bstep (se 2 (by rfl) ⟨420081, by rfl⟩ : syracuseStep 1120217 = 840163) B840163
theorem B1120331 : Blo 746329 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B1120343 : Blo 746329 1120343 := bstep (se 1 (by rfl) ⟨840257, by rfl⟩ : syracuseStep 1120343 = 1680515) B1680515
theorem B1120409 : Blo 746329 1120409 := bstep (se 2 (by rfl) ⟨420153, by rfl⟩ : syracuseStep 1120409 = 840307) B840307
theorem B1513687 : Blo 746329 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B1349875 : Blo 746329 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B1120523 : Blo 746329 1120523 := bstep (se 1 (by rfl) ⟨840392, by rfl⟩ : syracuseStep 1120523 = 1680785) B1680785
theorem B1120535 : Blo 746329 1120535 := bstep (se 1 (by rfl) ⟨840401, by rfl⟩ : syracuseStep 1120535 = 1680803) B1680803
theorem B1120601 : Blo 746329 1120601 := bstep (se 2 (by rfl) ⟨420225, by rfl⟩ : syracuseStep 1120601 = 840451) B840451
theorem B2529629 : Blo 746329 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B4037015 : Blo 746329 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B1120715 : Blo 746329 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B1120727 : Blo 746329 1120727 := bstep (se 1 (by rfl) ⟨840545, by rfl⟩ : syracuseStep 1120727 = 1681091) B1681091
theorem B5380613 : Blo 746329 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B10951181 : Blo 746329 10951181 := bstep (se 3 (by rfl) ⟨2053346, by rfl⟩ : syracuseStep 10951181 = 4106693) B4106693
theorem B5478929 : Blo 746329 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B1120793 : Blo 746329 1120793 := bstep (se 2 (by rfl) ⟨420297, by rfl⟩ : syracuseStep 1120793 = 840595) B840595
theorem B1120907 : Blo 746329 1120907 := bstep (se 1 (by rfl) ⟨840680, by rfl⟩ : syracuseStep 1120907 = 1681361) B1681361
theorem B1120919 : Blo 746329 1120919 := bstep (se 1 (by rfl) ⟨840689, by rfl⟩ : syracuseStep 1120919 = 1681379) B1681379
theorem B1120985 : Blo 746329 1120985 := bstep (se 2 (by rfl) ⟨420369, by rfl⟩ : syracuseStep 1120985 = 840739) B840739
theorem B1121099 : Blo 746329 1121099 := bstep (se 1 (by rfl) ⟨840824, by rfl⟩ : syracuseStep 1121099 = 1681649) B1681649
theorem B1121111 : Blo 746329 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B1514369 : Blo 746329 1514369 := bstep (se 2 (by rfl) ⟨567888, by rfl⟩ : syracuseStep 1514369 = 1135777) B1135777
theorem B1121177 : Blo 746329 1121177 := bstep (se 2 (by rfl) ⟨420441, by rfl⟩ : syracuseStep 1121177 = 840883) B840883
theorem B5675993 : Blo 746329 5675993 := bstep (se 2 (by rfl) ⟨2128497, by rfl⟩ : syracuseStep 5675993 = 4256995) B4256995
theorem B1121291 : Blo 746329 1121291 := bstep (se 1 (by rfl) ⟨840968, by rfl⟩ : syracuseStep 1121291 = 1681937) B1681937
theorem B1121303 : Blo 746329 1121303 := bstep (se 1 (by rfl) ⟨840977, by rfl⟩ : syracuseStep 1121303 = 1681955) B1681955
theorem B1121369 : Blo 746329 1121369 := bstep (se 2 (by rfl) ⟨420513, by rfl⟩ : syracuseStep 1121369 = 841027) B841027
theorem B1121483 : Blo 746329 1121483 := bstep (se 1 (by rfl) ⟨841112, by rfl⟩ : syracuseStep 1121483 = 1682225) B1682225
theorem B1121495 : Blo 746329 1121495 := bstep (se 1 (by rfl) ⟨841121, by rfl⟩ : syracuseStep 1121495 = 1682243) B1682243
theorem B1350913 : Blo 746329 1350913 := bstep (se 2 (by rfl) ⟨506592, by rfl⟩ : syracuseStep 1350913 = 1013185) B1013185
theorem B1121561 : Blo 746329 1121561 := bstep (se 2 (by rfl) ⟨420585, by rfl⟩ : syracuseStep 1121561 = 841171) B841171
theorem B2563379 : Blo 746329 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B2727233 : Blo 746329 2727233 := bstep (se 2 (by rfl) ⟨1022712, by rfl⟩ : syracuseStep 2727233 = 2045425) B2045425
theorem B1121675 : Blo 746329 1121675 := bstep (se 1 (by rfl) ⟨841256, by rfl⟩ : syracuseStep 1121675 = 1682513) B1682513
theorem B1121687 : Blo 746329 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B2530763 : Blo 746329 2530763 := bstep (se 1 (by rfl) ⟨1898072, by rfl⟩ : syracuseStep 2530763 = 3796145) B3796145
theorem B1121753 : Blo 746329 1121753 := bstep (se 2 (by rfl) ⟨420657, by rfl⟩ : syracuseStep 1121753 = 841315) B841315
theorem B1121867 : Blo 746329 1121867 := bstep (se 1 (by rfl) ⟨841400, by rfl⟩ : syracuseStep 1121867 = 1682801) B1682801
theorem B1121879 : Blo 746329 1121879 := bstep (se 1 (by rfl) ⟨841409, by rfl⟩ : syracuseStep 1121879 = 1682819) B1682819
theorem B12754583 : Blo 746329 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B1121945 : Blo 746329 1121945 := bstep (se 2 (by rfl) ⟨420729, by rfl⟩ : syracuseStep 1121945 = 841459) B841459
theorem B2531033 : Blo 746329 2531033 := bstep (se 2 (by rfl) ⟨949137, by rfl⟩ : syracuseStep 2531033 = 1898275) B1898275
theorem B1122059 : Blo 746329 1122059 := bstep (se 1 (by rfl) ⟨841544, by rfl⟩ : syracuseStep 1122059 = 1683089) B1683089
theorem B1122071 : Blo 746329 1122071 := bstep (se 1 (by rfl) ⟨841553, by rfl⟩ : syracuseStep 1122071 = 1683107) B1683107
theorem B1154891 : Blo 746329 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B1122137 : Blo 746329 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B1679255 : Blo 746329 1679255 := bstep (se 1 (by rfl) ⟨1259441, by rfl⟩ : syracuseStep 1679255 = 2518883) B2518883
theorem B1122251 : Blo 746329 1122251 := bstep (se 1 (by rfl) ⟨841688, by rfl⟩ : syracuseStep 1122251 = 1683377) B1683377
theorem B1122263 : Blo 746329 1122263 := bstep (se 1 (by rfl) ⟨841697, by rfl⟩ : syracuseStep 1122263 = 1683395) B1683395
theorem B1122329 : Blo 746329 1122329 := bstep (se 2 (by rfl) ⟨420873, by rfl⟩ : syracuseStep 1122329 = 841747) B841747
theorem B1417267 : Blo 746329 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B1679435 : Blo 746329 1679435 := bstep (se 1 (by rfl) ⟨1259576, by rfl⟩ : syracuseStep 1679435 = 2519153) B2519153
theorem B1679489 : Blo 746329 1679489 := bstep (se 2 (by rfl) ⟨629808, by rfl⟩ : syracuseStep 1679489 = 1259617) B1259617
theorem B1122443 : Blo 746329 1122443 := bstep (se 1 (by rfl) ⟨841832, by rfl⟩ : syracuseStep 1122443 = 1683665) B1683665
theorem B1122455 : Blo 746329 1122455 := bstep (se 1 (by rfl) ⟨841841, by rfl⟩ : syracuseStep 1122455 = 1683683) B1683683
theorem B1122521 : Blo 746329 1122521 := bstep (se 2 (by rfl) ⟨420945, by rfl⟩ : syracuseStep 1122521 = 841891) B841891
theorem B1417495 : Blo 746329 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B1122635 : Blo 746329 1122635 := bstep (se 1 (by rfl) ⟨841976, by rfl⟩ : syracuseStep 1122635 = 1683953) B1683953
theorem B1122647 : Blo 746329 1122647 := bstep (se 1 (by rfl) ⟨841985, by rfl⟩ : syracuseStep 1122647 = 1683971) B1683971
theorem B1679705 : Blo 746329 1679705 := bstep (se 2 (by rfl) ⟨629889, by rfl⟩ : syracuseStep 1679705 = 1259779) B1259779
theorem B1417601 : Blo 746329 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B2531735 : Blo 746329 2531735 := bstep (se 1 (by rfl) ⟨1898801, by rfl⟩ : syracuseStep 2531735 = 3797603) B3797603
theorem B1122713 : Blo 746329 1122713 := bstep (se 2 (by rfl) ⟨421017, by rfl⟩ : syracuseStep 1122713 = 842035) B842035
theorem B1679795 : Blo 746329 1679795 := bstep (se 1 (by rfl) ⟨1259846, by rfl⟩ : syracuseStep 1679795 = 2519693) B2519693
theorem B1679831 : Blo 746329 1679831 := bstep (se 1 (by rfl) ⟨1259873, by rfl⟩ : syracuseStep 1679831 = 2519747) B2519747
theorem B1122827 : Blo 746329 1122827 := bstep (se 1 (by rfl) ⟨842120, by rfl⟩ : syracuseStep 1122827 = 1684241) B1684241
theorem B1122839 : Blo 746329 1122839 := bstep (se 1 (by rfl) ⟨842129, by rfl⟩ : syracuseStep 1122839 = 1684259) B1684259
theorem B1417753 : Blo 746329 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B1122905 : Blo 746329 1122905 := bstep (se 2 (by rfl) ⟨421089, by rfl⟩ : syracuseStep 1122905 = 842179) B842179
theorem B1680011 : Blo 746329 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B6398615 : Blo 746329 6398615 := bstep (se 1 (by rfl) ⟨4798961, by rfl⟩ : syracuseStep 6398615 = 9597923) B9597923
theorem B1680065 : Blo 746329 1680065 := bstep (se 2 (by rfl) ⟨630024, by rfl⟩ : syracuseStep 1680065 = 1260049) B1260049
theorem B1123019 : Blo 746329 1123019 := bstep (se 1 (by rfl) ⟨842264, by rfl⟩ : syracuseStep 1123019 = 1684529) B1684529
theorem B1123031 : Blo 746329 1123031 := bstep (se 1 (by rfl) ⟨842273, by rfl⟩ : syracuseStep 1123031 = 1684547) B1684547
theorem B1123097 : Blo 746329 1123097 := bstep (se 2 (by rfl) ⟨421161, by rfl⟩ : syracuseStep 1123097 = 842323) B842323
theorem B1123211 : Blo 746329 1123211 := bstep (se 1 (by rfl) ⟨842408, by rfl⟩ : syracuseStep 1123211 = 1684817) B1684817
theorem B1123223 : Blo 746329 1123223 := bstep (se 1 (by rfl) ⟨842417, by rfl⟩ : syracuseStep 1123223 = 1684835) B1684835
theorem B1680281 : Blo 746329 1680281 := bstep (se 2 (by rfl) ⟨630105, by rfl⟩ : syracuseStep 1680281 = 1260211) B1260211
theorem B2532275 : Blo 746329 2532275 := bstep (se 1 (by rfl) ⟨1899206, by rfl⟩ : syracuseStep 2532275 = 3798413) B3798413
theorem B1123289 : Blo 746329 1123289 := bstep (se 2 (by rfl) ⟨421233, by rfl⟩ : syracuseStep 1123289 = 842467) B842467
theorem B1680371 : Blo 746329 1680371 := bstep (se 1 (by rfl) ⟨1260278, by rfl⟩ : syracuseStep 1680371 = 2520557) B2520557
theorem B1680407 : Blo 746329 1680407 := bstep (se 1 (by rfl) ⟨1260305, by rfl⟩ : syracuseStep 1680407 = 2520611) B2520611
theorem B1123403 : Blo 746329 1123403 := bstep (se 1 (by rfl) ⟨842552, by rfl⟩ : syracuseStep 1123403 = 1685105) B1685105
theorem B1123415 : Blo 746329 1123415 := bstep (se 1 (by rfl) ⟨842561, by rfl⟩ : syracuseStep 1123415 = 1685123) B1685123
theorem B1123481 : Blo 746329 1123481 := bstep (se 2 (by rfl) ⟨421305, by rfl⟩ : syracuseStep 1123481 = 842611) B842611
theorem B1680587 : Blo 746329 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B1680641 : Blo 746329 1680641 := bstep (se 2 (by rfl) ⟨630240, by rfl⟩ : syracuseStep 1680641 = 1260481) B1260481
theorem B1516801 : Blo 746329 1516801 := bstep (se 2 (by rfl) ⟨568800, by rfl⟩ : syracuseStep 1516801 = 1137601) B1137601
theorem B1123595 : Blo 746329 1123595 := bstep (se 1 (by rfl) ⟨842696, by rfl⟩ : syracuseStep 1123595 = 1685393) B1685393
theorem B1123607 : Blo 746329 1123607 := bstep (se 1 (by rfl) ⟨842705, by rfl⟩ : syracuseStep 1123607 = 1685411) B1685411
theorem B2401559 : Blo 746329 2401559 := bstep (se 1 (by rfl) ⟨1801169, by rfl⟩ : syracuseStep 2401559 = 3602339) B3602339
theorem B1516865 : Blo 746329 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B1123673 : Blo 746329 1123673 := bstep (se 2 (by rfl) ⟨421377, by rfl⟩ : syracuseStep 1123673 = 842755) B842755
theorem B3188099 : Blo 746329 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B1123787 : Blo 746329 1123787 := bstep (se 1 (by rfl) ⟨842840, by rfl⟩ : syracuseStep 1123787 = 1685681) B1685681
theorem B1123799 : Blo 746329 1123799 := bstep (se 1 (by rfl) ⟨842849, by rfl⟩ : syracuseStep 1123799 = 1685699) B1685699
theorem B1680857 : Blo 746329 1680857 := bstep (se 2 (by rfl) ⟨630321, by rfl⟩ : syracuseStep 1680857 = 1260643) B1260643
theorem B1123865 : Blo 746329 1123865 := bstep (se 2 (by rfl) ⟨421449, by rfl⟩ : syracuseStep 1123865 = 842899) B842899
theorem B1680947 : Blo 746329 1680947 := bstep (se 1 (by rfl) ⟨1260710, by rfl⟩ : syracuseStep 1680947 = 2521421) B2521421
theorem B1680983 : Blo 746329 1680983 := bstep (se 1 (by rfl) ⟨1260737, by rfl⟩ : syracuseStep 1680983 = 2521475) B2521475
theorem B1517143 : Blo 746329 1517143 := bstep (se 1 (by rfl) ⟨1137857, by rfl⟩ : syracuseStep 1517143 = 2275715) B2275715
theorem B1123979 : Blo 746329 1123979 := bstep (se 1 (by rfl) ⟨842984, by rfl⟩ : syracuseStep 1123979 = 1685969) B1685969
theorem B1123991 : Blo 746329 1123991 := bstep (se 1 (by rfl) ⟨842993, by rfl⟩ : syracuseStep 1123991 = 1685987) B1685987
theorem B1124057 : Blo 746329 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B1681163 : Blo 746329 1681163 := bstep (se 1 (by rfl) ⟨1260872, by rfl⟩ : syracuseStep 1681163 = 2521745) B2521745
theorem B1419059 : Blo 746329 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B1681217 : Blo 746329 1681217 := bstep (se 2 (by rfl) ⟨630456, by rfl⟩ : syracuseStep 1681217 = 1260913) B1260913
theorem B1124171 : Blo 746329 1124171 := bstep (se 1 (by rfl) ⟨843128, by rfl⟩ : syracuseStep 1124171 = 1686257) B1686257
theorem B960343 : Blo 746329 960343 := bstep (se 1 (by rfl) ⟨720257, by rfl⟩ : syracuseStep 960343 = 1440515) B1440515
theorem B1124183 : Blo 746329 1124183 := bstep (se 1 (by rfl) ⟨843137, by rfl⟩ : syracuseStep 1124183 = 1686275) B1686275
theorem B1124249 : Blo 746329 1124249 := bstep (se 2 (by rfl) ⟨421593, by rfl⟩ : syracuseStep 1124249 = 843187) B843187
theorem B1419211 : Blo 746329 1419211 := bstep (se 1 (by rfl) ⟨1064408, by rfl⟩ : syracuseStep 1419211 = 2128817) B2128817
theorem B1124363 : Blo 746329 1124363 := bstep (se 1 (by rfl) ⟨843272, by rfl⟩ : syracuseStep 1124363 = 1686545) B1686545
theorem B1124375 : Blo 746329 1124375 := bstep (se 1 (by rfl) ⟨843281, by rfl⟩ : syracuseStep 1124375 = 1686563) B1686563
theorem B1681433 : Blo 746329 1681433 := bstep (se 2 (by rfl) ⟨630537, by rfl⟩ : syracuseStep 1681433 = 1261075) B1261075
theorem B1124441 : Blo 746329 1124441 := bstep (se 2 (by rfl) ⟨421665, by rfl⟩ : syracuseStep 1124441 = 843331) B843331
theorem B1681523 : Blo 746329 1681523 := bstep (se 1 (by rfl) ⟨1261142, by rfl⟩ : syracuseStep 1681523 = 2522285) B2522285
theorem B1681559 : Blo 746329 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B1124555 : Blo 746329 1124555 := bstep (se 1 (by rfl) ⟨843416, by rfl⟩ : syracuseStep 1124555 = 1686833) B1686833
theorem B1124567 : Blo 746329 1124567 := bstep (se 1 (by rfl) ⟨843425, by rfl⟩ : syracuseStep 1124567 = 1686851) B1686851
theorem B1419545 : Blo 746329 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B1124633 : Blo 746329 1124633 := bstep (se 2 (by rfl) ⟨421737, by rfl⟩ : syracuseStep 1124633 = 843475) B843475
theorem B5679395 : Blo 746329 5679395 := bstep (se 1 (by rfl) ⟨4259546, by rfl⟩ : syracuseStep 5679395 = 8519093) B8519093
theorem B1681739 : Blo 746329 1681739 := bstep (se 1 (by rfl) ⟨1261304, by rfl⟩ : syracuseStep 1681739 = 2522609) B2522609
theorem B1681793 : Blo 746329 1681793 := bstep (se 2 (by rfl) ⟨630672, by rfl⟩ : syracuseStep 1681793 = 1261345) B1261345
theorem B1124747 : Blo 746329 1124747 := bstep (se 1 (by rfl) ⟨843560, by rfl⟩ : syracuseStep 1124747 = 1687121) B1687121
theorem B1124759 : Blo 746329 1124759 := bstep (se 1 (by rfl) ⟨843569, by rfl⟩ : syracuseStep 1124759 = 1687139) B1687139
theorem B1124825 : Blo 746329 1124825 := bstep (se 2 (by rfl) ⟨421809, by rfl⟩ : syracuseStep 1124825 = 843619) B843619
theorem B2697745 : Blo 746329 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B6400529 : Blo 746329 6400529 := bstep (se 2 (by rfl) ⟨2400198, by rfl⟩ : syracuseStep 6400529 = 4800397) B4800397
theorem B797239 : Blo 746329 797239 := bstep (se 1 (by rfl) ⟨597929, by rfl⟩ : syracuseStep 797239 = 1195859) B1195859
theorem B1124939 : Blo 746329 1124939 := bstep (se 1 (by rfl) ⟨843704, by rfl⟩ : syracuseStep 1124939 = 1687409) B1687409
theorem B2402891 : Blo 746329 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B862807 : Blo 746329 862807 := bstep (se 1 (by rfl) ⟨647105, by rfl⟩ : syracuseStep 862807 = 1294211) B1294211
theorem B1124951 : Blo 746329 1124951 := bstep (se 1 (by rfl) ⟨843713, by rfl⟩ : syracuseStep 1124951 = 1687427) B1687427
theorem B1682009 : Blo 746329 1682009 := bstep (se 2 (by rfl) ⟨630753, by rfl⟩ : syracuseStep 1682009 = 1261507) B1261507
theorem B1125017 : Blo 746329 1125017 := bstep (se 2 (by rfl) ⟨421881, by rfl⟩ : syracuseStep 1125017 = 843763) B843763
theorem B1682099 : Blo 746329 1682099 := bstep (se 1 (by rfl) ⟨1261574, by rfl⟩ : syracuseStep 1682099 = 2523149) B2523149
theorem B1682135 : Blo 746329 1682135 := bstep (se 1 (by rfl) ⟨1261601, by rfl⟩ : syracuseStep 1682135 = 2523203) B2523203
theorem B1125131 : Blo 746329 1125131 := bstep (se 1 (by rfl) ⟨843848, by rfl⟩ : syracuseStep 1125131 = 1687697) B1687697
theorem B1125143 : Blo 746329 1125143 := bstep (se 1 (by rfl) ⟨843857, by rfl⟩ : syracuseStep 1125143 = 1687715) B1687715
theorem B13839169 : Blo 746329 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1125209 : Blo 746329 1125209 := bstep (se 2 (by rfl) ⟨421953, by rfl⟩ : syracuseStep 1125209 = 843907) B843907
theorem B3779459 : Blo 746329 3779459 := bstep (se 1 (by rfl) ⟨2834594, by rfl⟩ : syracuseStep 3779459 = 5669189) B5669189
theorem B1682315 : Blo 746329 1682315 := bstep (se 1 (by rfl) ⟨1261736, by rfl⟩ : syracuseStep 1682315 = 2523473) B2523473
theorem B1420183 : Blo 746329 1420183 := bstep (se 1 (by rfl) ⟨1065137, by rfl⟩ : syracuseStep 1420183 = 2130275) B2130275
theorem B1682369 : Blo 746329 1682369 := bstep (se 2 (by rfl) ⟨630888, by rfl⟩ : syracuseStep 1682369 = 1261777) B1261777
theorem B1125323 : Blo 746329 1125323 := bstep (se 1 (by rfl) ⟨843992, by rfl⟩ : syracuseStep 1125323 = 1687985) B1687985
theorem B1125335 : Blo 746329 1125335 := bstep (se 1 (by rfl) ⟨844001, by rfl⟩ : syracuseStep 1125335 = 1688003) B1688003
theorem B3189725 : Blo 746329 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B7482385 : Blo 746329 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B2436119 : Blo 746329 2436119 := bstep (se 1 (by rfl) ⟨1827089, by rfl⟩ : syracuseStep 2436119 = 3654179) B3654179
theorem B1125401 : Blo 746329 1125401 := bstep (se 2 (by rfl) ⟨422025, by rfl⟩ : syracuseStep 1125401 = 844051) B844051
theorem B9743435 : Blo 746329 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B4041859 : Blo 746329 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2403479 : Blo 746329 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B1682585 : Blo 746329 1682585 := bstep (se 2 (by rfl) ⟨630969, by rfl⟩ : syracuseStep 1682585 = 1261939) B1261939
theorem B5123251 : Blo 746329 5123251 := bstep (se 1 (by rfl) ⟨3842438, by rfl⟩ : syracuseStep 5123251 = 7684877) B7684877
theorem B1682675 : Blo 746329 1682675 := bstep (se 1 (by rfl) ⟨1262006, by rfl⟩ : syracuseStep 1682675 = 2524013) B2524013
theorem B1682711 : Blo 746329 1682711 := bstep (se 1 (by rfl) ⟨1262033, by rfl⟩ : syracuseStep 1682711 = 2524067) B2524067
theorem B798059 : Blo 746329 798059 := bstep (se 1 (by rfl) ⟨598544, by rfl⟩ : syracuseStep 798059 = 1197089) B1197089
theorem B1682891 : Blo 746329 1682891 := bstep (se 1 (by rfl) ⟨1262168, by rfl⟩ : syracuseStep 1682891 = 2524337) B2524337
theorem B1682945 : Blo 746329 1682945 := bstep (se 2 (by rfl) ⟨631104, by rfl⟩ : syracuseStep 1682945 = 1262209) B1262209
theorem B3190423 : Blo 746329 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B1421003 : Blo 746329 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B3124939 : Blo 746329 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B3452633 : Blo 746329 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B1683161 : Blo 746329 1683161 := bstep (se 2 (by rfl) ⟨631185, by rfl⟩ : syracuseStep 1683161 = 1262371) B1262371
theorem B1421057 : Blo 746329 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B10792709 : Blo 746329 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B1683251 : Blo 746329 1683251 := bstep (se 1 (by rfl) ⟨1262438, by rfl⟩ : syracuseStep 1683251 = 2524877) B2524877
theorem B1683287 : Blo 746329 1683287 := bstep (se 1 (by rfl) ⟨1262465, by rfl⟩ : syracuseStep 1683287 = 2524931) B2524931
theorem B1683467 : Blo 746329 1683467 := bstep (se 1 (by rfl) ⟨1262600, by rfl⟩ : syracuseStep 1683467 = 2525201) B2525201
theorem B1683521 : Blo 746329 1683521 := bstep (se 2 (by rfl) ⟨631320, by rfl⟩ : syracuseStep 1683521 = 1262641) B1262641
theorem B3420377 : Blo 746329 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B1683737 : Blo 746329 1683737 := bstep (se 2 (by rfl) ⟨631401, by rfl⟩ : syracuseStep 1683737 = 1262803) B1262803
theorem B1683827 : Blo 746329 1683827 := bstep (se 1 (by rfl) ⟨1262870, by rfl⟩ : syracuseStep 1683827 = 2525741) B2525741
theorem B1683863 : Blo 746329 1683863 := bstep (se 1 (by rfl) ⟨1262897, by rfl⟩ : syracuseStep 1683863 = 2525795) B2525795
theorem B22196753 : Blo 746329 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B799255 : Blo 746329 799255 := bstep (se 1 (by rfl) ⟨599441, by rfl⟩ : syracuseStep 799255 = 1198883) B1198883
theorem B2699821 : Blo 746329 2699821 := bstep (se 3 (by rfl) ⟨506216, by rfl⟩ : syracuseStep 2699821 = 1012433) B1012433
theorem B1684043 : Blo 746329 1684043 := bstep (se 1 (by rfl) ⟨1263032, by rfl⟩ : syracuseStep 1684043 = 2526065) B2526065
theorem B1684097 : Blo 746329 1684097 := bstep (se 2 (by rfl) ⟨631536, by rfl⟩ : syracuseStep 1684097 = 1263073) B1263073
theorem B1421975 : Blo 746329 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B1684313 : Blo 746329 1684313 := bstep (se 2 (by rfl) ⟨631617, by rfl⟩ : syracuseStep 1684313 = 1263235) B1263235
theorem B1684403 : Blo 746329 1684403 := bstep (se 1 (by rfl) ⟨1263302, by rfl⟩ : syracuseStep 1684403 = 2526605) B2526605
theorem B2700211 : Blo 746329 2700211 := bstep (se 1 (by rfl) ⟨2025158, by rfl⟩ : syracuseStep 2700211 = 4050317) B4050317
theorem B1684439 : Blo 746329 1684439 := bstep (se 1 (by rfl) ⟨1263329, by rfl⟩ : syracuseStep 1684439 = 2526659) B2526659
theorem B3191825 : Blo 746329 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B1684619 : Blo 746329 1684619 := bstep (se 1 (by rfl) ⟨1263464, by rfl⟩ : syracuseStep 1684619 = 2526929) B2526929
theorem B1422515 : Blo 746329 1422515 := bstep (se 1 (by rfl) ⟨1066886, by rfl⟩ : syracuseStep 1422515 = 2133773) B2133773
theorem B1684673 : Blo 746329 1684673 := bstep (se 2 (by rfl) ⟨631752, by rfl⟩ : syracuseStep 1684673 = 1263505) B1263505
theorem B800075 : Blo 746329 800075 := bstep (se 1 (by rfl) ⟨600056, by rfl⟩ : syracuseStep 800075 = 1200113) B1200113
theorem B1684889 : Blo 746329 1684889 := bstep (se 2 (by rfl) ⟨631833, by rfl⟩ : syracuseStep 1684889 = 1263667) B1263667
theorem B800203 : Blo 746329 800203 := bstep (se 1 (by rfl) ⟨600152, by rfl⟩ : syracuseStep 800203 = 1200305) B1200305
theorem B4797913 : Blo 746329 4797913 := bstep (se 2 (by rfl) ⟨1799217, by rfl⟩ : syracuseStep 4797913 = 3598435) B3598435
theorem B1684979 : Blo 746329 1684979 := bstep (se 1 (by rfl) ⟨1263734, by rfl⟩ : syracuseStep 1684979 = 2527469) B2527469
theorem B1685015 : Blo 746329 1685015 := bstep (se 1 (by rfl) ⟨1263761, by rfl⟩ : syracuseStep 1685015 = 2527523) B2527523
theorem B1423001 : Blo 746329 1423001 := bstep (se 2 (by rfl) ⟨533625, by rfl⟩ : syracuseStep 1423001 = 1067251) B1067251
theorem B1685195 : Blo 746329 1685195 := bstep (se 1 (by rfl) ⟨1263896, by rfl⟩ : syracuseStep 1685195 = 2527793) B2527793
theorem B1685249 : Blo 746329 1685249 := bstep (se 2 (by rfl) ⟨631968, by rfl⟩ : syracuseStep 1685249 = 1263937) B1263937
theorem B5748515 : Blo 746329 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B3421997 : Blo 746329 3421997 := bstep (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) B1283249
theorem B24262577 : Blo 746329 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B1685465 : Blo 746329 1685465 := bstep (se 2 (by rfl) ⟨632049, by rfl⟩ : syracuseStep 1685465 = 1264099) B1264099
theorem B1259543 : Blo 746329 1259543 := bstep (se 1 (by rfl) ⟨944657, by rfl⟩ : syracuseStep 1259543 = 1889315) B1889315
theorem B899095 : Blo 746329 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B1685555 : Blo 746329 1685555 := bstep (se 1 (by rfl) ⟨1264166, by rfl⟩ : syracuseStep 1685555 = 2528333) B2528333
theorem B1685591 : Blo 746329 1685591 := bstep (se 1 (by rfl) ⟨1264193, by rfl⟩ : syracuseStep 1685591 = 2528387) B2528387
theorem B12793949 : Blo 746329 12793949 := bstep (se 3 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 12793949 = 4797731) B4797731
theorem B1259671 : Blo 746329 1259671 := bstep (se 1 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 1259671 = 1889507) B1889507
theorem B1685771 : Blo 746329 1685771 := bstep (se 1 (by rfl) ⟨1264328, by rfl⟩ : syracuseStep 1685771 = 2528657) B2528657
theorem B1685825 : Blo 746329 1685825 := bstep (se 2 (by rfl) ⟨632184, by rfl⟩ : syracuseStep 1685825 = 1264369) B1264369
theorem B3783185 : Blo 746329 3783185 := bstep (se 2 (by rfl) ⟨1418694, by rfl⟩ : syracuseStep 3783185 = 2837389) B2837389
theorem B2734609 : Blo 746329 2734609 := bstep (se 2 (by rfl) ⟨1025478, by rfl⟩ : syracuseStep 2734609 = 2050957) B2050957
theorem B1686041 : Blo 746329 1686041 := bstep (se 2 (by rfl) ⟨632265, by rfl⟩ : syracuseStep 1686041 = 1264531) B1264531
theorem B1686131 : Blo 746329 1686131 := bstep (se 1 (by rfl) ⟨1264598, by rfl⟩ : syracuseStep 1686131 = 2529197) B2529197
theorem B1686167 : Blo 746329 1686167 := bstep (se 1 (by rfl) ⟨1264625, by rfl⟩ : syracuseStep 1686167 = 2529251) B2529251
theorem B1063577 : Blo 746329 1063577 := bstep (se 2 (by rfl) ⟨398841, by rfl⟩ : syracuseStep 1063577 = 797683) B797683
theorem B3783347 : Blo 746329 3783347 := bstep (se 1 (by rfl) ⟨2837510, by rfl⟩ : syracuseStep 3783347 = 5675021) B5675021
theorem B1260299 : Blo 746329 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B1686347 : Blo 746329 1686347 := bstep (se 1 (by rfl) ⟨1264760, by rfl⟩ : syracuseStep 1686347 = 2529521) B2529521
theorem B1686401 : Blo 746329 1686401 := bstep (se 2 (by rfl) ⟨632400, by rfl⟩ : syracuseStep 1686401 = 1264801) B1264801
theorem B1260427 : Blo 746329 1260427 := bstep (se 1 (by rfl) ⟨945320, by rfl⟩ : syracuseStep 1260427 = 1890641) B1890641
theorem B1620875 : Blo 746329 1620875 := bstep (se 1 (by rfl) ⟨1215656, by rfl⟩ : syracuseStep 1620875 = 2431313) B2431313
theorem B1260569 : Blo 746329 1260569 := bstep (se 2 (by rfl) ⟨472713, by rfl⟩ : syracuseStep 1260569 = 945427) B945427
theorem B1686617 : Blo 746329 1686617 := bstep (se 2 (by rfl) ⟨632481, by rfl⟩ : syracuseStep 1686617 = 1264963) B1264963
theorem B1260697 : Blo 746329 1260697 := bstep (se 2 (by rfl) ⟨472761, by rfl⟩ : syracuseStep 1260697 = 945523) B945523
theorem B1686707 : Blo 746329 1686707 := bstep (se 1 (by rfl) ⟨1265030, by rfl⟩ : syracuseStep 1686707 = 2530061) B2530061
theorem B1686743 : Blo 746329 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B1064215 : Blo 746329 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B1686923 : Blo 746329 1686923 := bstep (se 1 (by rfl) ⟨1265192, by rfl⟩ : syracuseStep 1686923 = 2530385) B2530385
theorem B1686977 : Blo 746329 1686977 := bstep (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) B1265233
theorem B1195481 : Blo 746329 1195481 := bstep (se 2 (by rfl) ⟨448305, by rfl⟩ : syracuseStep 1195481 = 896611) B896611
theorem B5684741 : Blo 746329 5684741 := bstep (se 4 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 5684741 = 1065889) B1065889
theorem B1687193 : Blo 746329 1687193 := bstep (se 2 (by rfl) ⟨632697, by rfl⟩ : syracuseStep 1687193 = 1265395) B1265395
theorem B1261271 : Blo 746329 1261271 := bstep (se 1 (by rfl) ⟨945953, by rfl⟩ : syracuseStep 1261271 = 1891907) B1891907
theorem B1687283 : Blo 746329 1687283 := bstep (se 1 (by rfl) ⟨1265462, by rfl⟩ : syracuseStep 1687283 = 2530925) B2530925
theorem B2703107 : Blo 746329 2703107 := bstep (se 1 (by rfl) ⟨2027330, by rfl⟩ : syracuseStep 2703107 = 4054661) B4054661
theorem B1687319 : Blo 746329 1687319 := bstep (se 1 (by rfl) ⟨1265489, by rfl⟩ : syracuseStep 1687319 = 2530979) B2530979
theorem B1556275 : Blo 746329 1556275 := bstep (se 1 (by rfl) ⟨1167206, by rfl⟩ : syracuseStep 1556275 = 2334413) B2334413
theorem B1261399 : Blo 746329 1261399 := bstep (se 1 (by rfl) ⟨946049, by rfl⟩ : syracuseStep 1261399 = 1892099) B1892099
theorem B9715573 : Blo 746329 9715573 := bstep (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) B910835
theorem B3194797 : Blo 746329 3194797 := bstep (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) B1198049
theorem B1687499 : Blo 746329 1687499 := bstep (se 1 (by rfl) ⟨1265624, by rfl⟩ : syracuseStep 1687499 = 2531249) B2531249
theorem B1195993 : Blo 746329 1195993 := bstep (se 2 (by rfl) ⟨448497, by rfl⟩ : syracuseStep 1195993 = 896995) B896995
theorem B1687553 : Blo 746329 1687553 := bstep (se 2 (by rfl) ⟨632832, by rfl⟩ : syracuseStep 1687553 = 1265665) B1265665
theorem B8306705 : Blo 746329 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1065035 : Blo 746329 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1687769 : Blo 746329 1687769 := bstep (se 2 (by rfl) ⟨632913, by rfl⟩ : syracuseStep 1687769 = 1265827) B1265827
theorem B3195139 : Blo 746329 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B1687859 : Blo 746329 1687859 := bstep (se 1 (by rfl) ⟨1265894, by rfl⟩ : syracuseStep 1687859 = 2531789) B2531789
theorem B1687895 : Blo 746329 1687895 := bstep (se 1 (by rfl) ⟨1265921, by rfl⟩ : syracuseStep 1687895 = 2531843) B2531843
theorem B2834777 : Blo 746329 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B1262027 : Blo 746329 1262027 := bstep (se 1 (by rfl) ⟨946520, by rfl⟩ : syracuseStep 1262027 = 1893041) B1893041
theorem B1688075 : Blo 746329 1688075 := bstep (se 1 (by rfl) ⟨1266056, by rfl⟩ : syracuseStep 1688075 = 2532113) B2532113
theorem B1688129 : Blo 746329 1688129 := bstep (se 2 (by rfl) ⟨633048, by rfl⟩ : syracuseStep 1688129 = 1266097) B1266097
theorem B3785291 : Blo 746329 3785291 := bstep (se 1 (by rfl) ⟨2838968, by rfl⟩ : syracuseStep 3785291 = 5677937) B5677937
theorem B1262155 : Blo 746329 1262155 := bstep (se 1 (by rfl) ⟨946616, by rfl⟩ : syracuseStep 1262155 = 1893233) B1893233
theorem B1262297 : Blo 746329 1262297 := bstep (se 2 (by rfl) ⟨473361, by rfl⟩ : syracuseStep 1262297 = 946723) B946723
theorem B2736947 : Blo 746329 2736947 := bstep (se 1 (by rfl) ⟨2052710, by rfl⟩ : syracuseStep 2736947 = 4105421) B4105421
theorem B2310977 : Blo 746329 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B1262425 : Blo 746329 1262425 := bstep (se 2 (by rfl) ⟨473409, by rfl⟩ : syracuseStep 1262425 = 946819) B946819
theorem B3031901 : Blo 746329 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5391197 : Blo 746329 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B3196097 : Blo 746329 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B6833483 : Blo 746329 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B1262999 : Blo 746329 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B1263127 : Blo 746329 1263127 := bstep (se 1 (by rfl) ⟨947345, by rfl⟩ : syracuseStep 1263127 = 1894691) B1894691
theorem B2279191 : Blo 746329 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B20531009 : Blo 746329 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B5687171 : Blo 746329 5687171 := bstep (se 1 (by rfl) ⟨4265378, by rfl⟩ : syracuseStep 5687171 = 8530757) B8530757
theorem B2836403 : Blo 746329 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B2836417 : Blo 746329 2836417 := bstep (se 2 (by rfl) ⟨1063656, by rfl⟩ : syracuseStep 2836417 = 2127313) B2127313
theorem B8112089 : Blo 746329 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B3590189 : Blo 746329 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B1263755 : Blo 746329 1263755 := bstep (se 1 (by rfl) ⟨947816, by rfl⟩ : syracuseStep 1263755 = 1895633) B1895633
theorem B1263883 : Blo 746329 1263883 := bstep (se 1 (by rfl) ⟨947912, by rfl⟩ : syracuseStep 1263883 = 1895825) B1895825
theorem B3787073 : Blo 746329 3787073 := bstep (se 2 (by rfl) ⟨1420152, by rfl⟩ : syracuseStep 3787073 = 2840305) B2840305
theorem B1264025 : Blo 746329 1264025 := bstep (se 2 (by rfl) ⟨474009, by rfl⟩ : syracuseStep 1264025 = 948019) B948019
theorem B2279897 : Blo 746329 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B1264153 : Blo 746329 1264153 := bstep (se 2 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 1264153 = 948115) B948115
theorem B3197515 : Blo 746329 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B3197789 : Blo 746329 3197789 := bstep (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) B1199171
theorem B1919947 : Blo 746329 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B1264727 : Blo 746329 1264727 := bstep (se 1 (by rfl) ⟨948545, by rfl⟩ : syracuseStep 1264727 = 1897091) B1897091
theorem B5393587 : Blo 746329 5393587 := bstep (se 1 (by rfl) ⟨4045190, by rfl⟩ : syracuseStep 5393587 = 8090381) B8090381
theorem B1264855 : Blo 746329 1264855 := bstep (se 1 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 1264855 = 1897283) B1897283
theorem B1199767 : Blo 746329 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B6082253 : Blo 746329 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B5394221 : Blo 746329 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B2838347 : Blo 746329 2838347 := bstep (se 1 (by rfl) ⟨2128760, by rfl⟩ : syracuseStep 2838347 = 4257521) B4257521
theorem B1265483 : Blo 746329 1265483 := bstep (se 1 (by rfl) ⟨949112, by rfl⟩ : syracuseStep 1265483 = 1898225) B1898225
theorem B2838361 : Blo 746329 2838361 := bstep (se 2 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 2838361 = 2128771) B2128771
theorem B1200023 : Blo 746329 1200023 := bstep (se 1 (by rfl) ⟨900017, by rfl⟩ : syracuseStep 1200023 = 1800035) B1800035
theorem B1265611 : Blo 746329 1265611 := bstep (se 1 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 1265611 = 1898417) B1898417
theorem B839659 : Blo 746329 839659 := bstep (se 1 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 839659 = 1259489) B1259489
theorem B839767 : Blo 746329 839767 := bstep (se 1 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 839767 = 1259651) B1259651
theorem B1200215 : Blo 746329 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B1265753 : Blo 746329 1265753 := bstep (se 2 (by rfl) ⟨474657, by rfl⟩ : syracuseStep 1265753 = 949315) B949315
theorem B3789017 : Blo 746329 3789017 := bstep (se 2 (by rfl) ⟨1420881, by rfl⟩ : syracuseStep 3789017 = 2841763) B2841763
theorem B1265881 : Blo 746329 1265881 := bstep (se 2 (by rfl) ⟨474705, by rfl⟩ : syracuseStep 1265881 = 949411) B949411
theorem B839947 : Blo 746329 839947 := bstep (se 1 (by rfl) ⟨629960, by rfl⟩ : syracuseStep 839947 = 1259921) B1259921
theorem B840055 : Blo 746329 840055 := bstep (se 1 (by rfl) ⟨630041, by rfl⟩ : syracuseStep 840055 = 1260083) B1260083
theorem B1200523 : Blo 746329 1200523 := bstep (se 1 (by rfl) ⟨900392, by rfl⟩ : syracuseStep 1200523 = 1800785) B1800785
theorem B2019763 : Blo 746329 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B1364441 : Blo 746329 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B12767705 : Blo 746329 12767705 := bstep (se 2 (by rfl) ⟨4787889, by rfl⟩ : syracuseStep 12767705 = 9575779) B9575779
theorem B9589265 : Blo 746329 9589265 := bstep (se 2 (by rfl) ⟨3595974, by rfl⟩ : syracuseStep 9589265 = 7191949) B7191949
theorem B840235 : Blo 746329 840235 := bstep (se 1 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 840235 = 1260353) B1260353
theorem B840343 : Blo 746329 840343 := bstep (se 1 (by rfl) ⟨630257, by rfl⟩ : syracuseStep 840343 = 1260515) B1260515
theorem B2839319 : Blo 746329 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B840523 : Blo 746329 840523 := bstep (se 1 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 840523 = 1260785) B1260785
theorem B1200971 : Blo 746329 1200971 := bstep (se 1 (by rfl) ⟨900728, by rfl⟩ : syracuseStep 1200971 = 1801457) B1801457
theorem B1889203 : Blo 746329 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B840631 : Blo 746329 840631 := bstep (se 1 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 840631 = 1260947) B1260947
theorem B1889345 : Blo 746329 1889345 := bstep (se 2 (by rfl) ⟨708504, by rfl⟩ : syracuseStep 1889345 = 1417009) B1417009
theorem B840811 : Blo 746329 840811 := bstep (se 1 (by rfl) ⟨630608, by rfl⟩ : syracuseStep 840811 = 1261217) B1261217
theorem B5690573 : Blo 746329 5690573 := bstep (se 3 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 5690573 = 2133965) B2133965
theorem B840919 : Blo 746329 840919 := bstep (se 1 (by rfl) ⟨630689, by rfl⟩ : syracuseStep 840919 = 1261379) B1261379
theorem B841099 : Blo 746329 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B3200401 : Blo 746329 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B841207 : Blo 746329 841207 := bstep (se 1 (by rfl) ⟨630905, by rfl⟩ : syracuseStep 841207 = 1261811) B1261811
theorem B3462659 : Blo 746329 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1201753 : Blo 746329 1201753 := bstep (se 2 (by rfl) ⟨450657, by rfl⟩ : syracuseStep 1201753 = 901315) B901315
theorem B3593879 : Blo 746329 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B1201817 : Blo 746329 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B841387 : Blo 746329 841387 := bstep (se 1 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 841387 = 1262081) B1262081
theorem B5691059 : Blo 746329 5691059 := bstep (se 1 (by rfl) ⟨4268294, by rfl⟩ : syracuseStep 5691059 = 8536589) B8536589
theorem B841495 : Blo 746329 841495 := bstep (se 1 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 841495 = 1262243) B1262243
theorem B3790637 : Blo 746329 3790637 := bstep (se 3 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 3790637 = 1421489) B1421489
theorem B2021213 : Blo 746329 2021213 := bstep (se 3 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 2021213 = 757955) B757955
theorem B1595315 : Blo 746329 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B841675 : Blo 746329 841675 := bstep (se 1 (by rfl) ⟨631256, by rfl⟩ : syracuseStep 841675 = 1262513) B1262513
theorem B2840579 : Blo 746329 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B87447605 : Blo 746329 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B841783 : Blo 746329 841783 := bstep (se 1 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 841783 = 1262675) B1262675
theorem B3954839 : Blo 746329 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B841963 : Blo 746329 841963 := bstep (se 1 (by rfl) ⟨631472, by rfl⟩ : syracuseStep 841963 = 1262945) B1262945
theorem B1890611 : Blo 746329 1890611 := bstep (se 1 (by rfl) ⟨1417958, by rfl⟩ : syracuseStep 1890611 = 2835917) B2835917
theorem B842071 : Blo 746329 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B842251 : Blo 746329 842251 := bstep (se 1 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 842251 = 1263377) B1263377
theorem B842359 : Blo 746329 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B1596161 : Blo 746329 1596161 := bstep (se 2 (by rfl) ⟨598560, by rfl⟩ : syracuseStep 1596161 = 1197121) B1197121
theorem B842539 : Blo 746329 842539 := bstep (se 1 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 842539 = 1263809) B1263809
theorem B1891147 : Blo 746329 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B842647 : Blo 746329 842647 := bstep (se 1 (by rfl) ⟨631985, by rfl⟩ : syracuseStep 842647 = 1263971) B1263971
theorem B5397425 : Blo 746329 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B1891289 : Blo 746329 1891289 := bstep (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) B1418467
theorem B842827 : Blo 746329 842827 := bstep (se 1 (by rfl) ⟨632120, by rfl⟩ : syracuseStep 842827 = 1264241) B1264241
theorem B1596503 : Blo 746329 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B5692517 : Blo 746329 5692517 := bstep (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) B1067347
theorem B842935 : Blo 746329 842935 := bstep (se 1 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 842935 = 1264403) B1264403
theorem B2022617 : Blo 746329 2022617 := bstep (se 2 (by rfl) ⟨758481, by rfl⟩ : syracuseStep 2022617 = 1516963) B1516963
theorem B4250981 : Blo 746329 4250981 := bstep (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) B797059
theorem B843115 : Blo 746329 843115 := bstep (se 1 (by rfl) ⟨632336, by rfl⟩ : syracuseStep 843115 = 1264673) B1264673
theorem B5397911 : Blo 746329 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B843223 : Blo 746329 843223 := bstep (se 1 (by rfl) ⟨632417, by rfl⟩ : syracuseStep 843223 = 1264835) B1264835
theorem B24305123 : Blo 746329 24305123 := bstep (se 1 (by rfl) ⟨18228842, by rfl⟩ : syracuseStep 24305123 = 36457685) B36457685
theorem B5693003 : Blo 746329 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B843403 : Blo 746329 843403 := bstep (se 1 (by rfl) ⟨632552, by rfl⟩ : syracuseStep 843403 = 1265105) B1265105
theorem B843511 : Blo 746329 843511 := bstep (se 1 (by rfl) ⟨632633, by rfl⟩ : syracuseStep 843511 = 1265267) B1265267
theorem B1892119 : Blo 746329 1892119 := bstep (se 1 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 1892119 = 2838179) B2838179
theorem B4251437 : Blo 746329 4251437 := bstep (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) B1594289
theorem B6053707 : Blo 746329 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B843691 : Blo 746329 843691 := bstep (se 1 (by rfl) ⟨632768, by rfl⟩ : syracuseStep 843691 = 1265537) B1265537
theorem B843799 : Blo 746329 843799 := bstep (se 1 (by rfl) ⟨632849, by rfl⟩ : syracuseStep 843799 = 1265699) B1265699
theorem B1892555 : Blo 746329 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B843979 : Blo 746329 843979 := bstep (se 1 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 843979 = 1265969) B1265969
theorem B844087 : Blo 746329 844087 := bstep (se 1 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 844087 = 1266131) B1266131
theorem B4252121 : Blo 746329 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B3596761 : Blo 746329 3596761 := bstep (se 2 (by rfl) ⟨1348785, by rfl⟩ : syracuseStep 3596761 = 2697571) B2697571
theorem B3203545 : Blo 746329 3203545 := bstep (se 2 (by rfl) ⟨1201329, by rfl⟩ : syracuseStep 3203545 = 2402659) B2402659
theorem B1597963 : Blo 746329 1597963 := bstep (se 1 (by rfl) ⟨1198472, by rfl⟩ : syracuseStep 1597963 = 2396945) B2396945
theorem B1892929 : Blo 746329 1892929 := bstep (se 2 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 1892929 = 1419697) B1419697
theorem B1598219 : Blo 746329 1598219 := bstep (se 1 (by rfl) ⟨1198664, by rfl⟩ : syracuseStep 1598219 = 2397329) B2397329
theorem B746347 : Blo 746329 746347 := bstep (se 1 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 746347 = 1119521) B1119521
theorem B746359 : Blo 746329 746359 := bstep (se 1 (by rfl) ⟨559769, by rfl⟩ : syracuseStep 746359 = 1119539) B1119539
theorem B746379 : Blo 746329 746379 := bstep (se 1 (by rfl) ⟨559784, by rfl⟩ : syracuseStep 746379 = 1119569) B1119569
theorem B746391 : Blo 746329 746391 := bstep (se 1 (by rfl) ⟨559793, by rfl⟩ : syracuseStep 746391 = 1119587) B1119587
theorem B746411 : Blo 746329 746411 := bstep (se 1 (by rfl) ⟨559808, by rfl⟩ : syracuseStep 746411 = 1119617) B1119617
theorem B8217521 : Blo 746329 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B746423 : Blo 746329 746423 := bstep (se 1 (by rfl) ⟨559817, by rfl⟩ : syracuseStep 746423 = 1119635) B1119635
theorem B746443 : Blo 746329 746443 := bstep (se 1 (by rfl) ⟨559832, by rfl⟩ : syracuseStep 746443 = 1119665) B1119665
theorem B746455 : Blo 746329 746455 := bstep (se 1 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 746455 = 1119683) B1119683
theorem B746475 : Blo 746329 746475 := bstep (se 1 (by rfl) ⟨559856, by rfl⟩ : syracuseStep 746475 = 1119713) B1119713
theorem B746487 : Blo 746329 746487 := bstep (se 1 (by rfl) ⟨559865, by rfl⟩ : syracuseStep 746487 = 1119731) B1119731
theorem B3236867 : Blo 746329 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B746507 : Blo 746329 746507 := bstep (se 1 (by rfl) ⟨559880, by rfl⟩ : syracuseStep 746507 = 1119761) B1119761
theorem B746519 : Blo 746329 746519 := bstep (se 1 (by rfl) ⟨559889, by rfl⟩ : syracuseStep 746519 = 1119779) B1119779
theorem B746539 : Blo 746329 746539 := bstep (se 1 (by rfl) ⟨559904, by rfl⟩ : syracuseStep 746539 = 1119809) B1119809
theorem B2843693 : Blo 746329 2843693 := bstep (se 3 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 2843693 = 1066385) B1066385
theorem B746551 : Blo 746329 746551 := bstep (se 1 (by rfl) ⟨559913, by rfl⟩ : syracuseStep 746551 = 1119827) B1119827
theorem B3204161 : Blo 746329 3204161 := bstep (se 2 (by rfl) ⟨1201560, by rfl⟩ : syracuseStep 3204161 = 2403121) B2403121
theorem B746571 : Blo 746329 746571 := bstep (se 1 (by rfl) ⟨559928, by rfl⟩ : syracuseStep 746571 = 1119857) B1119857
theorem B746583 : Blo 746329 746583 := bstep (se 1 (by rfl) ⟨559937, by rfl⟩ : syracuseStep 746583 = 1119875) B1119875
theorem B746603 : Blo 746329 746603 := bstep (se 1 (by rfl) ⟨559952, by rfl⟩ : syracuseStep 746603 = 1119905) B1119905
theorem B746615 : Blo 746329 746615 := bstep (se 1 (by rfl) ⟨559961, by rfl⟩ : syracuseStep 746615 = 1119923) B1119923
theorem B746635 : Blo 746329 746635 := bstep (se 1 (by rfl) ⟨559976, by rfl⟩ : syracuseStep 746635 = 1119953) B1119953
theorem B746647 : Blo 746329 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B1893527 : Blo 746329 1893527 := bstep (se 1 (by rfl) ⟨1420145, by rfl⟩ : syracuseStep 1893527 = 2840291) B2840291
theorem B1139863 : Blo 746329 1139863 := bstep (se 1 (by rfl) ⟨854897, by rfl⟩ : syracuseStep 1139863 = 1709795) B1709795
theorem B746667 : Blo 746329 746667 := bstep (se 1 (by rfl) ⟨560000, by rfl⟩ : syracuseStep 746667 = 1120001) B1120001
theorem B746679 : Blo 746329 746679 := bstep (se 1 (by rfl) ⟨560009, by rfl⟩ : syracuseStep 746679 = 1120019) B1120019
theorem B746699 : Blo 746329 746699 := bstep (se 1 (by rfl) ⟨560024, by rfl⟩ : syracuseStep 746699 = 1120049) B1120049
theorem B746711 : Blo 746329 746711 := bstep (se 1 (by rfl) ⟨560033, by rfl⟩ : syracuseStep 746711 = 1120067) B1120067
theorem B746731 : Blo 746329 746731 := bstep (se 1 (by rfl) ⟨560048, by rfl⟩ : syracuseStep 746731 = 1120097) B1120097
theorem B746743 : Blo 746329 746743 := bstep (se 1 (by rfl) ⟨560057, by rfl⟩ : syracuseStep 746743 = 1120115) B1120115
theorem B746763 : Blo 746329 746763 := bstep (se 1 (by rfl) ⟨560072, by rfl⟩ : syracuseStep 746763 = 1120145) B1120145
theorem B746775 : Blo 746329 746775 := bstep (se 1 (by rfl) ⟨560081, by rfl⟩ : syracuseStep 746775 = 1120163) B1120163
theorem B746795 : Blo 746329 746795 := bstep (se 1 (by rfl) ⟨560096, by rfl⟩ : syracuseStep 746795 = 1120193) B1120193
theorem B746807 : Blo 746329 746807 := bstep (se 1 (by rfl) ⟨560105, by rfl⟩ : syracuseStep 746807 = 1120211) B1120211
theorem B746827 : Blo 746329 746827 := bstep (se 1 (by rfl) ⟨560120, by rfl⟩ : syracuseStep 746827 = 1120241) B1120241
theorem B746839 : Blo 746329 746839 := bstep (se 1 (by rfl) ⟨560129, by rfl⟩ : syracuseStep 746839 = 1120259) B1120259
theorem B746859 : Blo 746329 746859 := bstep (se 1 (by rfl) ⟨560144, by rfl⟩ : syracuseStep 746859 = 1120289) B1120289
theorem B746871 : Blo 746329 746871 := bstep (se 1 (by rfl) ⟨560153, by rfl⟩ : syracuseStep 746871 = 1120307) B1120307
theorem B746891 : Blo 746329 746891 := bstep (se 1 (by rfl) ⟨560168, by rfl⟩ : syracuseStep 746891 = 1120337) B1120337
theorem B746903 : Blo 746329 746903 := bstep (se 1 (by rfl) ⟨560177, by rfl⟩ : syracuseStep 746903 = 1120355) B1120355
theorem B746923 : Blo 746329 746923 := bstep (se 1 (by rfl) ⟨560192, by rfl⟩ : syracuseStep 746923 = 1120385) B1120385
theorem B746935 : Blo 746329 746935 := bstep (se 1 (by rfl) ⟨560201, by rfl⟩ : syracuseStep 746935 = 1120403) B1120403
theorem B746955 : Blo 746329 746955 := bstep (se 1 (by rfl) ⟨560216, by rfl⟩ : syracuseStep 746955 = 1120433) B1120433
theorem B746967 : Blo 746329 746967 := bstep (se 1 (by rfl) ⟨560225, by rfl⟩ : syracuseStep 746967 = 1120451) B1120451
theorem B746987 : Blo 746329 746987 := bstep (se 1 (by rfl) ⟨560240, by rfl⟩ : syracuseStep 746987 = 1120481) B1120481
theorem B746999 : Blo 746329 746999 := bstep (se 1 (by rfl) ⟨560249, by rfl⟩ : syracuseStep 746999 = 1120499) B1120499
theorem B747019 : Blo 746329 747019 := bstep (se 1 (by rfl) ⟨560264, by rfl⟩ : syracuseStep 747019 = 1120529) B1120529
theorem B747031 : Blo 746329 747031 := bstep (se 1 (by rfl) ⟨560273, by rfl⟩ : syracuseStep 747031 = 1120547) B1120547
theorem B747051 : Blo 746329 747051 := bstep (se 1 (by rfl) ⟨560288, by rfl⟩ : syracuseStep 747051 = 1120577) B1120577
theorem B747063 : Blo 746329 747063 := bstep (se 1 (by rfl) ⟨560297, by rfl⟩ : syracuseStep 747063 = 1120595) B1120595
theorem B747083 : Blo 746329 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B747095 : Blo 746329 747095 := bstep (se 1 (by rfl) ⟨560321, by rfl⟩ : syracuseStep 747095 = 1120643) B1120643
theorem B3794525 : Blo 746329 3794525 := bstep (se 3 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 3794525 = 1422947) B1422947
theorem B747115 : Blo 746329 747115 := bstep (se 1 (by rfl) ⟨560336, by rfl⟩ : syracuseStep 747115 = 1120673) B1120673
theorem B747127 : Blo 746329 747127 := bstep (se 1 (by rfl) ⟨560345, by rfl⟩ : syracuseStep 747127 = 1120691) B1120691
theorem B747147 : Blo 746329 747147 := bstep (se 1 (by rfl) ⟨560360, by rfl⟩ : syracuseStep 747147 = 1120721) B1120721
theorem B747159 : Blo 746329 747159 := bstep (se 1 (by rfl) ⟨560369, by rfl⟩ : syracuseStep 747159 = 1120739) B1120739
theorem B1402519 : Blo 746329 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B747179 : Blo 746329 747179 := bstep (se 1 (by rfl) ⟨560384, by rfl⟩ : syracuseStep 747179 = 1120769) B1120769
theorem B747191 : Blo 746329 747191 := bstep (se 1 (by rfl) ⟨560393, by rfl⟩ : syracuseStep 747191 = 1120787) B1120787
theorem B747211 : Blo 746329 747211 := bstep (se 1 (by rfl) ⟨560408, by rfl⟩ : syracuseStep 747211 = 1120817) B1120817
theorem B747223 : Blo 746329 747223 := bstep (se 1 (by rfl) ⟨560417, by rfl⟩ : syracuseStep 747223 = 1120835) B1120835
theorem B1599193 : Blo 746329 1599193 := bstep (se 2 (by rfl) ⟨599697, by rfl⟩ : syracuseStep 1599193 = 1199395) B1199395
theorem B747243 : Blo 746329 747243 := bstep (se 1 (by rfl) ⟨560432, by rfl⟩ : syracuseStep 747243 = 1120865) B1120865
theorem B747255 : Blo 746329 747255 := bstep (se 1 (by rfl) ⟨560441, by rfl⟩ : syracuseStep 747255 = 1120883) B1120883
theorem B747275 : Blo 746329 747275 := bstep (se 1 (by rfl) ⟨560456, by rfl⟩ : syracuseStep 747275 = 1120913) B1120913
theorem B747287 : Blo 746329 747287 := bstep (se 1 (by rfl) ⟨560465, by rfl⟩ : syracuseStep 747287 = 1120931) B1120931
theorem B747307 : Blo 746329 747307 := bstep (se 1 (by rfl) ⟨560480, by rfl⟩ : syracuseStep 747307 = 1120961) B1120961
theorem B2844467 : Blo 746329 2844467 := bstep (se 1 (by rfl) ⟨2133350, by rfl⟩ : syracuseStep 2844467 = 4266701) B4266701
theorem B747319 : Blo 746329 747319 := bstep (se 1 (by rfl) ⟨560489, by rfl⟩ : syracuseStep 747319 = 1120979) B1120979
theorem B747339 : Blo 746329 747339 := bstep (se 1 (by rfl) ⟨560504, by rfl⟩ : syracuseStep 747339 = 1121009) B1121009
theorem B747351 : Blo 746329 747351 := bstep (se 1 (by rfl) ⟨560513, by rfl⟩ : syracuseStep 747351 = 1121027) B1121027
theorem B747371 : Blo 746329 747371 := bstep (se 1 (by rfl) ⟨560528, by rfl⟩ : syracuseStep 747371 = 1121057) B1121057
theorem B1599347 : Blo 746329 1599347 := bstep (se 1 (by rfl) ⟨1199510, by rfl⟩ : syracuseStep 1599347 = 2399021) B2399021
theorem B747383 : Blo 746329 747383 := bstep (se 1 (by rfl) ⟨560537, by rfl⟩ : syracuseStep 747383 = 1121075) B1121075
theorem B747403 : Blo 746329 747403 := bstep (se 1 (by rfl) ⟨560552, by rfl⟩ : syracuseStep 747403 = 1121105) B1121105
theorem B747415 : Blo 746329 747415 := bstep (se 1 (by rfl) ⟨560561, by rfl⟩ : syracuseStep 747415 = 1121123) B1121123
theorem B747435 : Blo 746329 747435 := bstep (se 1 (by rfl) ⟨560576, by rfl⟩ : syracuseStep 747435 = 1121153) B1121153
theorem B747447 : Blo 746329 747447 := bstep (se 1 (by rfl) ⟨560585, by rfl⟩ : syracuseStep 747447 = 1121171) B1121171
theorem B1894337 : Blo 746329 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B747467 : Blo 746329 747467 := bstep (se 1 (by rfl) ⟨560600, by rfl⟩ : syracuseStep 747467 = 1121201) B1121201
theorem B747479 : Blo 746329 747479 := bstep (se 1 (by rfl) ⟨560609, by rfl⟩ : syracuseStep 747479 = 1121219) B1121219
theorem B747499 : Blo 746329 747499 := bstep (se 1 (by rfl) ⟨560624, by rfl⟩ : syracuseStep 747499 = 1121249) B1121249
theorem B747511 : Blo 746329 747511 := bstep (se 1 (by rfl) ⟨560633, by rfl⟩ : syracuseStep 747511 = 1121267) B1121267
theorem B747531 : Blo 746329 747531 := bstep (se 1 (by rfl) ⟨560648, by rfl⟩ : syracuseStep 747531 = 1121297) B1121297
theorem B747543 : Blo 746329 747543 := bstep (se 1 (by rfl) ⟨560657, by rfl⟩ : syracuseStep 747543 = 1121315) B1121315
theorem B747563 : Blo 746329 747563 := bstep (se 1 (by rfl) ⟨560672, by rfl⟩ : syracuseStep 747563 = 1121345) B1121345
theorem B747575 : Blo 746329 747575 := bstep (se 1 (by rfl) ⟨560681, by rfl⟩ : syracuseStep 747575 = 1121363) B1121363
theorem B747595 : Blo 746329 747595 := bstep (se 1 (by rfl) ⟨560696, by rfl⟩ : syracuseStep 747595 = 1121393) B1121393
theorem B747607 : Blo 746329 747607 := bstep (se 1 (by rfl) ⟨560705, by rfl⟩ : syracuseStep 747607 = 1121411) B1121411
theorem B6383717 : Blo 746329 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B747627 : Blo 746329 747627 := bstep (se 1 (by rfl) ⟨560720, by rfl⟩ : syracuseStep 747627 = 1121441) B1121441
theorem B747639 : Blo 746329 747639 := bstep (se 1 (by rfl) ⟨560729, by rfl⟩ : syracuseStep 747639 = 1121459) B1121459
theorem B747659 : Blo 746329 747659 := bstep (se 1 (by rfl) ⟨560744, by rfl⟩ : syracuseStep 747659 = 1121489) B1121489
theorem B747671 : Blo 746329 747671 := bstep (se 1 (by rfl) ⟨560753, by rfl⟩ : syracuseStep 747671 = 1121507) B1121507
theorem B747691 : Blo 746329 747691 := bstep (se 1 (by rfl) ⟨560768, by rfl⟩ : syracuseStep 747691 = 1121537) B1121537
theorem B747703 : Blo 746329 747703 := bstep (se 1 (by rfl) ⟨560777, by rfl⟩ : syracuseStep 747703 = 1121555) B1121555
theorem B747723 : Blo 746329 747723 := bstep (se 1 (by rfl) ⟨560792, by rfl⟩ : syracuseStep 747723 = 1121585) B1121585
theorem B747735 : Blo 746329 747735 := bstep (se 1 (by rfl) ⟨560801, by rfl⟩ : syracuseStep 747735 = 1121603) B1121603
theorem B747755 : Blo 746329 747755 := bstep (se 1 (by rfl) ⟨560816, by rfl⟩ : syracuseStep 747755 = 1121633) B1121633
theorem B747767 : Blo 746329 747767 := bstep (se 1 (by rfl) ⟨560825, by rfl⟩ : syracuseStep 747767 = 1121651) B1121651
theorem B747787 : Blo 746329 747787 := bstep (se 1 (by rfl) ⟨560840, by rfl⟩ : syracuseStep 747787 = 1121681) B1121681
theorem B747799 : Blo 746329 747799 := bstep (se 1 (by rfl) ⟨560849, by rfl⟩ : syracuseStep 747799 = 1121699) B1121699
theorem B747819 : Blo 746329 747819 := bstep (se 1 (by rfl) ⟨560864, by rfl⟩ : syracuseStep 747819 = 1121729) B1121729
theorem B747831 : Blo 746329 747831 := bstep (se 1 (by rfl) ⟨560873, by rfl⟩ : syracuseStep 747831 = 1121747) B1121747
theorem B747851 : Blo 746329 747851 := bstep (se 1 (by rfl) ⟨560888, by rfl⟩ : syracuseStep 747851 = 1121777) B1121777
theorem B747863 : Blo 746329 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B747883 : Blo 746329 747883 := bstep (se 1 (by rfl) ⟨560912, by rfl⟩ : syracuseStep 747883 = 1121825) B1121825
theorem B1599859 : Blo 746329 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B747895 : Blo 746329 747895 := bstep (se 1 (by rfl) ⟨560921, by rfl⟩ : syracuseStep 747895 = 1121843) B1121843
theorem B747915 : Blo 746329 747915 := bstep (se 1 (by rfl) ⟨560936, by rfl⟩ : syracuseStep 747915 = 1121873) B1121873
theorem B747927 : Blo 746329 747927 := bstep (se 1 (by rfl) ⟨560945, by rfl⟩ : syracuseStep 747927 = 1121891) B1121891
theorem B747947 : Blo 746329 747947 := bstep (se 1 (by rfl) ⟨560960, by rfl⟩ : syracuseStep 747947 = 1121921) B1121921
theorem B6056369 : Blo 746329 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B747959 : Blo 746329 747959 := bstep (se 1 (by rfl) ⟨560969, by rfl⟩ : syracuseStep 747959 = 1121939) B1121939
theorem B2877889 : Blo 746329 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B747979 : Blo 746329 747979 := bstep (se 1 (by rfl) ⟨560984, by rfl⟩ : syracuseStep 747979 = 1121969) B1121969
theorem B747991 : Blo 746329 747991 := bstep (se 1 (by rfl) ⟨560993, by rfl⟩ : syracuseStep 747991 = 1121987) B1121987
theorem B1894873 : Blo 746329 1894873 := bstep (se 2 (by rfl) ⟨710577, by rfl⟩ : syracuseStep 1894873 = 1421155) B1421155
theorem B748011 : Blo 746329 748011 := bstep (se 1 (by rfl) ⟨561008, by rfl⟩ : syracuseStep 748011 = 1122017) B1122017
theorem B748023 : Blo 746329 748023 := bstep (se 1 (by rfl) ⟨561017, by rfl⟩ : syracuseStep 748023 = 1122035) B1122035
theorem B748043 : Blo 746329 748043 := bstep (se 1 (by rfl) ⟨561032, by rfl⟩ : syracuseStep 748043 = 1122065) B1122065
theorem B748055 : Blo 746329 748055 := bstep (se 1 (by rfl) ⟨561041, by rfl⟩ : syracuseStep 748055 = 1122083) B1122083
theorem B748075 : Blo 746329 748075 := bstep (se 1 (by rfl) ⟨561056, by rfl⟩ : syracuseStep 748075 = 1122113) B1122113
theorem B748087 : Blo 746329 748087 := bstep (se 1 (by rfl) ⟨561065, by rfl⟩ : syracuseStep 748087 = 1122131) B1122131
theorem B748107 : Blo 746329 748107 := bstep (se 1 (by rfl) ⟨561080, by rfl⟩ : syracuseStep 748107 = 1122161) B1122161
theorem B748119 : Blo 746329 748119 := bstep (se 1 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 748119 = 1122179) B1122179
theorem B748139 : Blo 746329 748139 := bstep (se 1 (by rfl) ⟨561104, by rfl⟩ : syracuseStep 748139 = 1122209) B1122209
theorem B748151 : Blo 746329 748151 := bstep (se 1 (by rfl) ⟨561113, by rfl⟩ : syracuseStep 748151 = 1122227) B1122227
theorem B944779 : Blo 746329 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B748171 : Blo 746329 748171 := bstep (se 1 (by rfl) ⟨561128, by rfl⟩ : syracuseStep 748171 = 1122257) B1122257
theorem B748183 : Blo 746329 748183 := bstep (se 1 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 748183 = 1122275) B1122275
theorem B748203 : Blo 746329 748203 := bstep (se 1 (by rfl) ⟨561152, by rfl⟩ : syracuseStep 748203 = 1122305) B1122305
theorem B748215 : Blo 746329 748215 := bstep (se 1 (by rfl) ⟨561161, by rfl⟩ : syracuseStep 748215 = 1122323) B1122323
theorem B748235 : Blo 746329 748235 := bstep (se 1 (by rfl) ⟨561176, by rfl⟩ : syracuseStep 748235 = 1122353) B1122353
theorem B748247 : Blo 746329 748247 := bstep (se 1 (by rfl) ⟨561185, by rfl⟩ : syracuseStep 748247 = 1122371) B1122371
theorem B748267 : Blo 746329 748267 := bstep (se 1 (by rfl) ⟨561200, by rfl⟩ : syracuseStep 748267 = 1122401) B1122401
theorem B748279 : Blo 746329 748279 := bstep (se 1 (by rfl) ⟨561209, by rfl⟩ : syracuseStep 748279 = 1122419) B1122419
theorem B748299 : Blo 746329 748299 := bstep (se 1 (by rfl) ⟨561224, by rfl⟩ : syracuseStep 748299 = 1122449) B1122449
theorem B748311 : Blo 746329 748311 := bstep (se 1 (by rfl) ⟨561233, by rfl⟩ : syracuseStep 748311 = 1122467) B1122467
theorem B748331 : Blo 746329 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B3074861 : Blo 746329 3074861 := bstep (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) B1153073
theorem B748343 : Blo 746329 748343 := bstep (se 1 (by rfl) ⟨561257, by rfl⟩ : syracuseStep 748343 = 1122515) B1122515
theorem B748363 : Blo 746329 748363 := bstep (se 1 (by rfl) ⟨561272, by rfl⟩ : syracuseStep 748363 = 1122545) B1122545
theorem B748375 : Blo 746329 748375 := bstep (se 1 (by rfl) ⟨561281, by rfl⟩ : syracuseStep 748375 = 1122563) B1122563
theorem B748395 : Blo 746329 748395 := bstep (se 1 (by rfl) ⟨561296, by rfl⟩ : syracuseStep 748395 = 1122593) B1122593
theorem B748407 : Blo 746329 748407 := bstep (se 1 (by rfl) ⟨561305, by rfl⟩ : syracuseStep 748407 = 1122611) B1122611
theorem B748427 : Blo 746329 748427 := bstep (se 1 (by rfl) ⟨561320, by rfl⟩ : syracuseStep 748427 = 1122641) B1122641
theorem B945047 : Blo 746329 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B748439 : Blo 746329 748439 := bstep (se 1 (by rfl) ⟨561329, by rfl⟩ : syracuseStep 748439 = 1122659) B1122659
theorem B748459 : Blo 746329 748459 := bstep (se 1 (by rfl) ⟨561344, by rfl⟩ : syracuseStep 748459 = 1122689) B1122689
theorem B748471 : Blo 746329 748471 := bstep (se 1 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 748471 = 1122707) B1122707
theorem B748491 : Blo 746329 748491 := bstep (se 1 (by rfl) ⟨561368, by rfl⟩ : syracuseStep 748491 = 1122737) B1122737
theorem B748503 : Blo 746329 748503 := bstep (se 1 (by rfl) ⟨561377, by rfl⟩ : syracuseStep 748503 = 1122755) B1122755
theorem B748523 : Blo 746329 748523 := bstep (se 1 (by rfl) ⟨561392, by rfl⟩ : syracuseStep 748523 = 1122785) B1122785
theorem B748535 : Blo 746329 748535 := bstep (se 1 (by rfl) ⟨561401, by rfl⟩ : syracuseStep 748535 = 1122803) B1122803
theorem B748555 : Blo 746329 748555 := bstep (se 1 (by rfl) ⟨561416, by rfl⟩ : syracuseStep 748555 = 1122833) B1122833
theorem B748567 : Blo 746329 748567 := bstep (se 1 (by rfl) ⟨561425, by rfl⟩ : syracuseStep 748567 = 1122851) B1122851
theorem B1600535 : Blo 746329 1600535 := bstep (se 1 (by rfl) ⟨1200401, by rfl⟩ : syracuseStep 1600535 = 2400803) B2400803
theorem B748587 : Blo 746329 748587 := bstep (se 1 (by rfl) ⟨561440, by rfl⟩ : syracuseStep 748587 = 1122881) B1122881
theorem B748599 : Blo 746329 748599 := bstep (se 1 (by rfl) ⟨561449, by rfl⟩ : syracuseStep 748599 = 1122899) B1122899
theorem B1600577 : Blo 746329 1600577 := bstep (se 2 (by rfl) ⟨600216, by rfl⟩ : syracuseStep 1600577 = 1200433) B1200433
theorem B748619 : Blo 746329 748619 := bstep (se 1 (by rfl) ⟨561464, by rfl⟩ : syracuseStep 748619 = 1122929) B1122929
theorem B748631 : Blo 746329 748631 := bstep (se 1 (by rfl) ⟨561473, by rfl⟩ : syracuseStep 748631 = 1122947) B1122947
theorem B3599453 : Blo 746329 3599453 := bstep (se 3 (by rfl) ⟨674897, by rfl⟩ : syracuseStep 3599453 = 1349795) B1349795
theorem B748651 : Blo 746329 748651 := bstep (se 1 (by rfl) ⟨561488, by rfl⟩ : syracuseStep 748651 = 1122977) B1122977
theorem B748663 : Blo 746329 748663 := bstep (se 1 (by rfl) ⟨561497, by rfl⟩ : syracuseStep 748663 = 1122995) B1122995
theorem B748683 : Blo 746329 748683 := bstep (se 1 (by rfl) ⟨561512, by rfl⟩ : syracuseStep 748683 = 1123025) B1123025
theorem B748695 : Blo 746329 748695 := bstep (se 1 (by rfl) ⟨561521, by rfl⟩ : syracuseStep 748695 = 1123043) B1123043
theorem B748715 : Blo 746329 748715 := bstep (se 1 (by rfl) ⟨561536, by rfl⟩ : syracuseStep 748715 = 1123073) B1123073
theorem B748727 : Blo 746329 748727 := bstep (se 1 (by rfl) ⟨561545, by rfl⟩ : syracuseStep 748727 = 1123091) B1123091
theorem B748747 : Blo 746329 748747 := bstep (se 1 (by rfl) ⟨561560, by rfl⟩ : syracuseStep 748747 = 1123121) B1123121
theorem B748759 : Blo 746329 748759 := bstep (se 1 (by rfl) ⟨561569, by rfl⟩ : syracuseStep 748759 = 1123139) B1123139
theorem B748779 : Blo 746329 748779 := bstep (se 1 (by rfl) ⟨561584, by rfl⟩ : syracuseStep 748779 = 1123169) B1123169
theorem B748791 : Blo 746329 748791 := bstep (se 1 (by rfl) ⟨561593, by rfl⟩ : syracuseStep 748791 = 1123187) B1123187
theorem B2845955 : Blo 746329 2845955 := bstep (se 1 (by rfl) ⟨2134466, by rfl⟩ : syracuseStep 2845955 = 4268933) B4268933
theorem B748811 : Blo 746329 748811 := bstep (se 1 (by rfl) ⟨561608, by rfl⟩ : syracuseStep 748811 = 1123217) B1123217
theorem B748823 : Blo 746329 748823 := bstep (se 1 (by rfl) ⟨561617, by rfl⟩ : syracuseStep 748823 = 1123235) B1123235
theorem B748843 : Blo 746329 748843 := bstep (se 1 (by rfl) ⟨561632, by rfl⟩ : syracuseStep 748843 = 1123265) B1123265
theorem B748855 : Blo 746329 748855 := bstep (se 1 (by rfl) ⟨561641, by rfl⟩ : syracuseStep 748855 = 1123283) B1123283
theorem B748875 : Blo 746329 748875 := bstep (se 1 (by rfl) ⟨561656, by rfl⟩ : syracuseStep 748875 = 1123313) B1123313
theorem B748887 : Blo 746329 748887 := bstep (se 1 (by rfl) ⟨561665, by rfl⟩ : syracuseStep 748887 = 1123331) B1123331
theorem B748907 : Blo 746329 748907 := bstep (se 1 (by rfl) ⟨561680, by rfl⟩ : syracuseStep 748907 = 1123361) B1123361
theorem B748919 : Blo 746329 748919 := bstep (se 1 (by rfl) ⟨561689, by rfl⟩ : syracuseStep 748919 = 1123379) B1123379
theorem B748939 : Blo 746329 748939 := bstep (se 1 (by rfl) ⟨561704, by rfl⟩ : syracuseStep 748939 = 1123409) B1123409
theorem B1797527 : Blo 746329 1797527 := bstep (se 1 (by rfl) ⟨1348145, by rfl⟩ : syracuseStep 1797527 = 2696291) B2696291
theorem B748951 : Blo 746329 748951 := bstep (se 1 (by rfl) ⟨561713, by rfl⟩ : syracuseStep 748951 = 1123427) B1123427
theorem B748971 : Blo 746329 748971 := bstep (se 1 (by rfl) ⟨561728, by rfl⟩ : syracuseStep 748971 = 1123457) B1123457
theorem B748983 : Blo 746329 748983 := bstep (se 1 (by rfl) ⟨561737, by rfl⟩ : syracuseStep 748983 = 1123475) B1123475
theorem B749003 : Blo 746329 749003 := bstep (se 1 (by rfl) ⟨561752, by rfl⟩ : syracuseStep 749003 = 1123505) B1123505
theorem B749015 : Blo 746329 749015 := bstep (se 1 (by rfl) ⟨561761, by rfl⟩ : syracuseStep 749015 = 1123523) B1123523
theorem B749035 : Blo 746329 749035 := bstep (se 1 (by rfl) ⟨561776, by rfl⟩ : syracuseStep 749035 = 1123553) B1123553
theorem B749047 : Blo 746329 749047 := bstep (se 1 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 749047 = 1123571) B1123571
theorem B749067 : Blo 746329 749067 := bstep (se 1 (by rfl) ⟨561800, by rfl⟩ : syracuseStep 749067 = 1123601) B1123601
theorem B749079 : Blo 746329 749079 := bstep (se 1 (by rfl) ⟨561809, by rfl⟩ : syracuseStep 749079 = 1123619) B1123619
theorem B749099 : Blo 746329 749099 := bstep (se 1 (by rfl) ⟨561824, by rfl⟩ : syracuseStep 749099 = 1123649) B1123649
theorem B1895987 : Blo 746329 1895987 := bstep (se 1 (by rfl) ⟨1421990, by rfl⟩ : syracuseStep 1895987 = 2843981) B2843981
theorem B749111 : Blo 746329 749111 := bstep (se 1 (by rfl) ⟨561833, by rfl⟩ : syracuseStep 749111 = 1123667) B1123667
theorem B749131 : Blo 746329 749131 := bstep (se 1 (by rfl) ⟨561848, by rfl⟩ : syracuseStep 749131 = 1123697) B1123697
theorem B945751 : Blo 746329 945751 := bstep (se 1 (by rfl) ⟨709313, by rfl⟩ : syracuseStep 945751 = 1418627) B1418627
theorem B749143 : Blo 746329 749143 := bstep (se 1 (by rfl) ⟨561857, by rfl⟩ : syracuseStep 749143 = 1123715) B1123715
theorem B749163 : Blo 746329 749163 := bstep (se 1 (by rfl) ⟨561872, by rfl⟩ : syracuseStep 749163 = 1123745) B1123745
theorem B749175 : Blo 746329 749175 := bstep (se 1 (by rfl) ⟨561881, by rfl⟩ : syracuseStep 749175 = 1123763) B1123763
theorem B749195 : Blo 746329 749195 := bstep (se 1 (by rfl) ⟨561896, by rfl⟩ : syracuseStep 749195 = 1123793) B1123793
theorem B749207 : Blo 746329 749207 := bstep (se 1 (by rfl) ⟨561905, by rfl⟩ : syracuseStep 749207 = 1123811) B1123811
theorem B3796631 : Blo 746329 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B749227 : Blo 746329 749227 := bstep (se 1 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 749227 = 1123841) B1123841
theorem B749239 : Blo 746329 749239 := bstep (se 1 (by rfl) ⟨561929, by rfl⟩ : syracuseStep 749239 = 1123859) B1123859
theorem B749259 : Blo 746329 749259 := bstep (se 1 (by rfl) ⟨561944, by rfl⟩ : syracuseStep 749259 = 1123889) B1123889
theorem B2846411 : Blo 746329 2846411 := bstep (se 1 (by rfl) ⟨2134808, by rfl⟩ : syracuseStep 2846411 = 4269617) B4269617
theorem B749271 : Blo 746329 749271 := bstep (se 1 (by rfl) ⟨561953, by rfl⟩ : syracuseStep 749271 = 1123907) B1123907
theorem B749291 : Blo 746329 749291 := bstep (se 1 (by rfl) ⟨561968, by rfl⟩ : syracuseStep 749291 = 1123937) B1123937
theorem B749303 : Blo 746329 749303 := bstep (se 1 (by rfl) ⟨561977, by rfl⟩ : syracuseStep 749303 = 1123955) B1123955
theorem B749323 : Blo 746329 749323 := bstep (se 1 (by rfl) ⟨561992, by rfl⟩ : syracuseStep 749323 = 1123985) B1123985
theorem B749335 : Blo 746329 749335 := bstep (se 1 (by rfl) ⟨562001, by rfl⟩ : syracuseStep 749335 = 1124003) B1124003
theorem B749355 : Blo 746329 749355 := bstep (se 1 (by rfl) ⟨562016, by rfl⟩ : syracuseStep 749355 = 1124033) B1124033
theorem B749367 : Blo 746329 749367 := bstep (se 1 (by rfl) ⟨562025, by rfl⟩ : syracuseStep 749367 = 1124051) B1124051
theorem B749387 : Blo 746329 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B749399 : Blo 746329 749399 := bstep (se 1 (by rfl) ⟨562049, by rfl⟩ : syracuseStep 749399 = 1124099) B1124099
theorem B1896281 : Blo 746329 1896281 := bstep (se 2 (by rfl) ⟨711105, by rfl⟩ : syracuseStep 1896281 = 1422211) B1422211
theorem B749419 : Blo 746329 749419 := bstep (se 1 (by rfl) ⟨562064, by rfl⟩ : syracuseStep 749419 = 1124129) B1124129
theorem B749431 : Blo 746329 749431 := bstep (se 1 (by rfl) ⟨562073, by rfl⟩ : syracuseStep 749431 = 1124147) B1124147
theorem B749451 : Blo 746329 749451 := bstep (se 1 (by rfl) ⟨562088, by rfl⟩ : syracuseStep 749451 = 1124177) B1124177
theorem B2846609 : Blo 746329 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B749463 : Blo 746329 749463 := bstep (se 1 (by rfl) ⟨562097, by rfl⟩ : syracuseStep 749463 = 1124195) B1124195
theorem B749483 : Blo 746329 749483 := bstep (se 1 (by rfl) ⟨562112, by rfl⟩ : syracuseStep 749483 = 1124225) B1124225
theorem B749495 : Blo 746329 749495 := bstep (se 1 (by rfl) ⟨562121, by rfl⟩ : syracuseStep 749495 = 1124243) B1124243
theorem B749515 : Blo 746329 749515 := bstep (se 1 (by rfl) ⟨562136, by rfl⟩ : syracuseStep 749515 = 1124273) B1124273
theorem B749527 : Blo 746329 749527 := bstep (se 1 (by rfl) ⟨562145, by rfl⟩ : syracuseStep 749527 = 1124291) B1124291
theorem B749547 : Blo 746329 749547 := bstep (se 1 (by rfl) ⟨562160, by rfl⟩ : syracuseStep 749547 = 1124321) B1124321
theorem B749559 : Blo 746329 749559 := bstep (se 1 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 749559 = 1124339) B1124339
theorem B749579 : Blo 746329 749579 := bstep (se 1 (by rfl) ⟨562184, by rfl⟩ : syracuseStep 749579 = 1124369) B1124369
theorem B749591 : Blo 746329 749591 := bstep (se 1 (by rfl) ⟨562193, by rfl⟩ : syracuseStep 749591 = 1124387) B1124387
theorem B749611 : Blo 746329 749611 := bstep (se 1 (by rfl) ⟨562208, by rfl⟩ : syracuseStep 749611 = 1124417) B1124417
theorem B54521909 : Blo 746329 54521909 := bstep (se 5 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 54521909 = 5111429) B5111429
theorem B749623 : Blo 746329 749623 := bstep (se 1 (by rfl) ⟨562217, by rfl⟩ : syracuseStep 749623 = 1124435) B1124435
theorem B749643 : Blo 746329 749643 := bstep (se 1 (by rfl) ⟨562232, by rfl⟩ : syracuseStep 749643 = 1124465) B1124465
theorem B749655 : Blo 746329 749655 := bstep (se 1 (by rfl) ⟨562241, by rfl⟩ : syracuseStep 749655 = 1124483) B1124483
theorem B749675 : Blo 746329 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B749687 : Blo 746329 749687 := bstep (se 1 (by rfl) ⟨562265, by rfl⟩ : syracuseStep 749687 = 1124531) B1124531
theorem B749707 : Blo 746329 749707 := bstep (se 1 (by rfl) ⟨562280, by rfl⟩ : syracuseStep 749707 = 1124561) B1124561
theorem B749719 : Blo 746329 749719 := bstep (se 1 (by rfl) ⟨562289, by rfl⟩ : syracuseStep 749719 = 1124579) B1124579
theorem B749739 : Blo 746329 749739 := bstep (se 1 (by rfl) ⟨562304, by rfl⟩ : syracuseStep 749739 = 1124609) B1124609
theorem B749751 : Blo 746329 749751 := bstep (se 1 (by rfl) ⟨562313, by rfl⟩ : syracuseStep 749751 = 1124627) B1124627
theorem B2126027 : Blo 746329 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B749771 : Blo 746329 749771 := bstep (se 1 (by rfl) ⟨562328, by rfl⟩ : syracuseStep 749771 = 1124657) B1124657
theorem B749783 : Blo 746329 749783 := bstep (se 1 (by rfl) ⟨562337, by rfl⟩ : syracuseStep 749783 = 1124675) B1124675
theorem B2519261 : Blo 746329 2519261 := bstep (se 3 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 2519261 = 944723) B944723
theorem B749803 : Blo 746329 749803 := bstep (se 1 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 749803 = 1124705) B1124705
theorem B749815 : Blo 746329 749815 := bstep (se 1 (by rfl) ⟨562361, by rfl⟩ : syracuseStep 749815 = 1124723) B1124723
theorem B749835 : Blo 746329 749835 := bstep (se 1 (by rfl) ⟨562376, by rfl⟩ : syracuseStep 749835 = 1124753) B1124753
theorem B749847 : Blo 746329 749847 := bstep (se 1 (by rfl) ⟨562385, by rfl⟩ : syracuseStep 749847 = 1124771) B1124771
theorem B749867 : Blo 746329 749867 := bstep (se 1 (by rfl) ⟨562400, by rfl⟩ : syracuseStep 749867 = 1124801) B1124801
theorem B749879 : Blo 746329 749879 := bstep (se 1 (by rfl) ⟨562409, by rfl⟩ : syracuseStep 749879 = 1124819) B1124819
theorem B749899 : Blo 746329 749899 := bstep (se 1 (by rfl) ⟨562424, by rfl⟩ : syracuseStep 749899 = 1124849) B1124849
theorem B749911 : Blo 746329 749911 := bstep (se 1 (by rfl) ⟨562433, by rfl⟩ : syracuseStep 749911 = 1124867) B1124867
theorem B749931 : Blo 746329 749931 := bstep (se 1 (by rfl) ⟨562448, by rfl⟩ : syracuseStep 749931 = 1124897) B1124897
theorem B749943 : Blo 746329 749943 := bstep (se 1 (by rfl) ⟨562457, by rfl⟩ : syracuseStep 749943 = 1124915) B1124915
theorem B749963 : Blo 746329 749963 := bstep (se 1 (by rfl) ⟨562472, by rfl⟩ : syracuseStep 749963 = 1124945) B1124945
theorem B749975 : Blo 746329 749975 := bstep (se 1 (by rfl) ⟨562481, by rfl⟩ : syracuseStep 749975 = 1124963) B1124963
theorem B749995 : Blo 746329 749995 := bstep (se 1 (by rfl) ⟨562496, by rfl⟩ : syracuseStep 749995 = 1124993) B1124993
theorem B750007 : Blo 746329 750007 := bstep (se 1 (by rfl) ⟨562505, by rfl⟩ : syracuseStep 750007 = 1125011) B1125011
theorem B750027 : Blo 746329 750027 := bstep (se 1 (by rfl) ⟨562520, by rfl⟩ : syracuseStep 750027 = 1125041) B1125041
theorem B750039 : Blo 746329 750039 := bstep (se 1 (by rfl) ⟨562529, by rfl⟩ : syracuseStep 750039 = 1125059) B1125059
theorem B750059 : Blo 746329 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B750071 : Blo 746329 750071 := bstep (se 1 (by rfl) ⟨562553, by rfl⟩ : syracuseStep 750071 = 1125107) B1125107
theorem B750091 : Blo 746329 750091 := bstep (se 1 (by rfl) ⟨562568, by rfl⟩ : syracuseStep 750091 = 1125137) B1125137
theorem B6844945 : Blo 746329 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B750103 : Blo 746329 750103 := bstep (se 1 (by rfl) ⟨562577, by rfl⟩ : syracuseStep 750103 = 1125155) B1125155
theorem B750123 : Blo 746329 750123 := bstep (se 1 (by rfl) ⟨562592, by rfl⟩ : syracuseStep 750123 = 1125185) B1125185
theorem B750135 : Blo 746329 750135 := bstep (se 1 (by rfl) ⟨562601, by rfl⟩ : syracuseStep 750135 = 1125203) B1125203
theorem B750155 : Blo 746329 750155 := bstep (se 1 (by rfl) ⟨562616, by rfl⟩ : syracuseStep 750155 = 1125233) B1125233
theorem B750167 : Blo 746329 750167 := bstep (se 1 (by rfl) ⟨562625, by rfl⟩ : syracuseStep 750167 = 1125251) B1125251
theorem B2126425 : Blo 746329 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B750187 : Blo 746329 750187 := bstep (se 1 (by rfl) ⟨562640, by rfl⟩ : syracuseStep 750187 = 1125281) B1125281
theorem B750199 : Blo 746329 750199 := bstep (se 1 (by rfl) ⟨562649, by rfl⟩ : syracuseStep 750199 = 1125299) B1125299
theorem B750219 : Blo 746329 750219 := bstep (se 1 (by rfl) ⟨562664, by rfl⟩ : syracuseStep 750219 = 1125329) B1125329
theorem B2847383 : Blo 746329 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B750231 : Blo 746329 750231 := bstep (se 1 (by rfl) ⟨562673, by rfl⟩ : syracuseStep 750231 = 1125347) B1125347
theorem B750251 : Blo 746329 750251 := bstep (se 1 (by rfl) ⟨562688, by rfl⟩ : syracuseStep 750251 = 1125377) B1125377
theorem B750263 : Blo 746329 750263 := bstep (se 1 (by rfl) ⟨562697, by rfl⟩ : syracuseStep 750263 = 1125395) B1125395
theorem B750283 : Blo 746329 750283 := bstep (se 1 (by rfl) ⟨562712, by rfl⟩ : syracuseStep 750283 = 1125425) B1125425
theorem B750295 : Blo 746329 750295 := bstep (se 1 (by rfl) ⟨562721, by rfl⟩ : syracuseStep 750295 = 1125443) B1125443
theorem B750315 : Blo 746329 750315 := bstep (se 1 (by rfl) ⟨562736, by rfl⟩ : syracuseStep 750315 = 1125473) B1125473
theorem B750327 : Blo 746329 750327 := bstep (se 1 (by rfl) ⟨562745, by rfl⟩ : syracuseStep 750327 = 1125491) B1125491
theorem B2847581 : Blo 746329 2847581 := bstep (se 3 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 2847581 = 1067843) B1067843
theorem B4256813 : Blo 746329 4256813 := bstep (se 3 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 4256813 = 1596305) B1596305
theorem B4060205 : Blo 746329 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B1438807 : Blo 746329 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B947467 : Blo 746329 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B2520395 : Blo 746329 2520395 := bstep (se 1 (by rfl) ⟨1890296, by rfl⟩ : syracuseStep 2520395 = 3780593) B3780593
theorem B2553281 : Blo 746329 2553281 := bstep (se 2 (by rfl) ⟨957480, by rfl⟩ : syracuseStep 2553281 = 1914961) B1914961
theorem B1897931 : Blo 746329 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B2520665 : Blo 746329 2520665 := bstep (se 2 (by rfl) ⟨945249, by rfl⟩ : syracuseStep 2520665 = 1890499) B1890499
theorem B2127667 : Blo 746329 2127667 := bstep (se 1 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 2127667 = 3191501) B3191501
theorem B15333299 : Blo 746329 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B1013963 : Blo 746329 1013963 := bstep (se 1 (by rfl) ⟨760472, by rfl⟩ : syracuseStep 1013963 = 1520945) B1520945
theorem B948439 : Blo 746329 948439 := bstep (se 1 (by rfl) ⟨711329, by rfl⟩ : syracuseStep 948439 = 1422659) B1422659
theorem B2521367 : Blo 746329 2521367 := bstep (se 1 (by rfl) ⟨1891025, by rfl⟩ : syracuseStep 2521367 = 3782051) B3782051
theorem B8092021 : Blo 746329 8092021 := bstep (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) B758627
theorem B1898903 : Blo 746329 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B2521907 : Blo 746329 2521907 := bstep (se 1 (by rfl) ⟨1891430, by rfl⟩ : syracuseStep 2521907 = 3782861) B3782861
theorem B1801111 : Blo 746329 1801111 := bstep (se 1 (by rfl) ⟨1350833, by rfl⟩ : syracuseStep 1801111 = 2701667) B2701667
theorem B1440755 : Blo 746329 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B949259 : Blo 746329 949259 := bstep (se 1 (by rfl) ⟨711944, by rfl⟩ : syracuseStep 949259 = 1423889) B1423889
theorem B2522177 : Blo 746329 2522177 := bstep (se 2 (by rfl) ⟨945816, by rfl⟩ : syracuseStep 2522177 = 1891633) B1891633
theorem B12811445 : Blo 746329 12811445 := bstep (se 5 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 12811445 = 1201073) B1201073
theorem B3407107 : Blo 746329 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B2522717 : Blo 746329 2522717 := bstep (se 3 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 2522717 = 946019) B946019
theorem B6913997 : Blo 746329 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B2555869 : Blo 746329 2555869 := bstep (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) B958451
theorem B5537803 : Blo 746329 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B4260185 : Blo 746329 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B2523527 : Blo 746329 2523527 := bstep (se 1 (by rfl) ⟨1892645, by rfl⟩ : syracuseStep 2523527 = 3785291) B3785291
theorem B932774453 : Blo 746329 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B25887413 : Blo 746329 25887413 := bstep (se 5 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 25887413 = 2426945) B2426945
theorem B2130617 : Blo 746329 2130617 := bstep (se 2 (by rfl) ⟨798981, by rfl⟩ : syracuseStep 2130617 = 1597963) B1597963
theorem B2523905 : Blo 746329 2523905 := bstep (se 2 (by rfl) ⟨946464, by rfl⟩ : syracuseStep 2523905 = 1892929) B1892929
theorem B2130731 : Blo 746329 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B4555655 : Blo 746329 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B1705079 : Blo 746329 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B5408059 : Blo 746329 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B2393459 : Blo 746329 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B2524715 : Blo 746329 2524715 := bstep (se 1 (by rfl) ⟨1893536, by rfl⟩ : syracuseStep 2524715 = 3787073) B3787073
theorem B2131859 : Blo 746329 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B4327435 : Blo 746329 4327435 := bstep (se 1 (by rfl) ⟨3245576, by rfl⟩ : syracuseStep 4327435 = 6491153) B6491153
theorem B10815605 : Blo 746329 10815605 := bstep (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) B1013963
theorem B6162605 : Blo 746329 6162605 := bstep (se 3 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 6162605 = 2310977) B2310977
theorem B1870025 : Blo 746329 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B2132257 : Blo 746329 2132257 := bstep (se 2 (by rfl) ⟨799596, by rfl⟩ : syracuseStep 2132257 = 1599193) B1599193
theorem B2526011 : Blo 746329 2526011 := bstep (se 1 (by rfl) ⟨1894508, by rfl⟩ : syracuseStep 2526011 = 3789017) B3789017
theorem B6392843 : Blo 746329 6392843 := bstep (se 1 (by rfl) ⟨4794632, by rfl⟩ : syracuseStep 6392843 = 9589265) B9589265
theorem B2133145 : Blo 746329 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B1313977 : Blo 746329 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B3837185 : Blo 746329 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B2526497 : Blo 746329 2526497 := bstep (se 2 (by rfl) ⟨947436, by rfl⟩ : syracuseStep 2526497 = 1894873) B1894873
theorem B4263353 : Blo 746329 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B1150409 : Blo 746329 1150409 := bstep (se 2 (by rfl) ⟨431403, by rfl⟩ : syracuseStep 1150409 = 862807) B862807
theorem B2133533 : Blo 746329 2133533 := bstep (se 3 (by rfl) ⟨400037, by rfl⟩ : syracuseStep 2133533 = 800075) B800075
theorem B18452225 : Blo 746329 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B2395919 : Blo 746329 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B2527091 : Blo 746329 2527091 := bstep (se 1 (by rfl) ⟨1895318, by rfl⟩ : syracuseStep 2527091 = 3790637) B3790637
theorem B1347475 : Blo 746329 1347475 := bstep (se 1 (by rfl) ⟨1010606, by rfl⟩ : syracuseStep 1347475 = 2021213) B2021213
theorem B2559929 : Blo 746329 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B2887741 : Blo 746329 2887741 := bstep (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) B1082903
theorem B2691343 : Blo 746329 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B1348411 : Blo 746329 1348411 := bstep (se 1 (by rfl) ⟨1011308, by rfl⟩ : syracuseStep 1348411 = 2022617) B2022617
theorem B1708919 : Blo 746329 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B14554037 : Blo 746329 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B11539381 : Blo 746329 11539381 := bstep (se 5 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 11539381 = 1081817) B1081817
theorem B4166585 : Blo 746329 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B1119503 : Blo 746329 1119503 := bstep (se 1 (by rfl) ⟨839627, by rfl⟩ : syracuseStep 1119503 = 1679255) B1679255
theorem B1119545 : Blo 746329 1119545 := bstep (se 2 (by rfl) ⟨419829, by rfl⟩ : syracuseStep 1119545 = 839659) B839659
theorem B1119623 : Blo 746329 1119623 := bstep (se 1 (by rfl) ⟨839717, by rfl⟩ : syracuseStep 1119623 = 1679435) B1679435
theorem B1119659 : Blo 746329 1119659 := bstep (se 1 (by rfl) ⟨839744, by rfl⟩ : syracuseStep 1119659 = 1679489) B1679489
theorem B1119689 : Blo 746329 1119689 := bstep (se 2 (by rfl) ⟨419883, by rfl⟩ : syracuseStep 1119689 = 839767) B839767
theorem B1119803 : Blo 746329 1119803 := bstep (se 1 (by rfl) ⟨839852, by rfl⟩ : syracuseStep 1119803 = 1679705) B1679705
theorem B1119863 : Blo 746329 1119863 := bstep (se 1 (by rfl) ⟨839897, by rfl⟩ : syracuseStep 1119863 = 1679795) B1679795
theorem B1119887 : Blo 746329 1119887 := bstep (se 1 (by rfl) ⟨839915, by rfl⟩ : syracuseStep 1119887 = 1679831) B1679831
theorem B1119929 : Blo 746329 1119929 := bstep (se 2 (by rfl) ⟨419973, by rfl⟩ : syracuseStep 1119929 = 839947) B839947
theorem B1120007 : Blo 746329 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B4265743 : Blo 746329 4265743 := bstep (se 1 (by rfl) ⟨3199307, by rfl⟩ : syracuseStep 4265743 = 6398615) B6398615
theorem B1120043 : Blo 746329 1120043 := bstep (se 1 (by rfl) ⟨840032, by rfl⟩ : syracuseStep 1120043 = 1680065) B1680065
theorem B1120073 : Blo 746329 1120073 := bstep (se 2 (by rfl) ⟨420027, by rfl⟩ : syracuseStep 1120073 = 840055) B840055
theorem B2693017 : Blo 746329 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B1120187 : Blo 746329 1120187 := bstep (se 1 (by rfl) ⟨840140, by rfl⟩ : syracuseStep 1120187 = 1680281) B1680281
theorem B5478347 : Blo 746329 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B1120247 : Blo 746329 1120247 := bstep (se 1 (by rfl) ⟨840185, by rfl⟩ : syracuseStep 1120247 = 1680371) B1680371
theorem B1120271 : Blo 746329 1120271 := bstep (se 1 (by rfl) ⟨840203, by rfl⟩ : syracuseStep 1120271 = 1680407) B1680407
theorem B2136107 : Blo 746329 2136107 := bstep (se 1 (by rfl) ⟨1602080, by rfl⟩ : syracuseStep 2136107 = 3204161) B3204161
theorem B1120313 : Blo 746329 1120313 := bstep (se 2 (by rfl) ⟨420117, by rfl⟩ : syracuseStep 1120313 = 840235) B840235
theorem B1120391 : Blo 746329 1120391 := bstep (se 1 (by rfl) ⟨840293, by rfl⟩ : syracuseStep 1120391 = 1680587) B1680587
theorem B1120427 : Blo 746329 1120427 := bstep (se 1 (by rfl) ⟨840320, by rfl⟩ : syracuseStep 1120427 = 1680641) B1680641
theorem B1120457 : Blo 746329 1120457 := bstep (se 2 (by rfl) ⟨420171, by rfl⟩ : syracuseStep 1120457 = 840343) B840343
theorem B1120571 : Blo 746329 1120571 := bstep (se 1 (by rfl) ⟨840428, by rfl⟩ : syracuseStep 1120571 = 1680857) B1680857
theorem B1120631 : Blo 746329 1120631 := bstep (se 1 (by rfl) ⟨840473, by rfl⟩ : syracuseStep 1120631 = 1680947) B1680947
theorem B1120655 : Blo 746329 1120655 := bstep (se 1 (by rfl) ⟨840491, by rfl⟩ : syracuseStep 1120655 = 1680983) B1680983
theorem B2529683 : Blo 746329 2529683 := bstep (se 1 (by rfl) ⟨1897262, by rfl⟩ : syracuseStep 2529683 = 3794525) B3794525
theorem B1120697 : Blo 746329 1120697 := bstep (se 2 (by rfl) ⟨420261, by rfl⟩ : syracuseStep 1120697 = 840523) B840523
theorem B1120775 : Blo 746329 1120775 := bstep (se 1 (by rfl) ⟨840581, by rfl⟩ : syracuseStep 1120775 = 1681163) B1681163
theorem B1120811 : Blo 746329 1120811 := bstep (se 1 (by rfl) ⟨840608, by rfl⟩ : syracuseStep 1120811 = 1681217) B1681217
theorem B1120841 : Blo 746329 1120841 := bstep (se 2 (by rfl) ⟨420315, by rfl⟩ : syracuseStep 1120841 = 840631) B840631
theorem B1120955 : Blo 746329 1120955 := bstep (se 1 (by rfl) ⟨840716, by rfl⟩ : syracuseStep 1120955 = 1681433) B1681433
theorem B1121015 : Blo 746329 1121015 := bstep (se 1 (by rfl) ⟨840761, by rfl⟩ : syracuseStep 1121015 = 1681523) B1681523
theorem B1121039 : Blo 746329 1121039 := bstep (se 1 (by rfl) ⟨840779, by rfl⟩ : syracuseStep 1121039 = 1681559) B1681559
theorem B1121081 : Blo 746329 1121081 := bstep (se 2 (by rfl) ⟨420405, by rfl⟩ : syracuseStep 1121081 = 840811) B840811
theorem B1121159 : Blo 746329 1121159 := bstep (se 1 (by rfl) ⟨840869, by rfl⟩ : syracuseStep 1121159 = 1681739) B1681739
theorem B1121195 : Blo 746329 1121195 := bstep (se 1 (by rfl) ⟨840896, by rfl⟩ : syracuseStep 1121195 = 1681793) B1681793
theorem B1121225 : Blo 746329 1121225 := bstep (se 2 (by rfl) ⟨420459, by rfl⟩ : syracuseStep 1121225 = 840919) B840919
theorem B4037579 : Blo 746329 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B4267019 : Blo 746329 4267019 := bstep (se 1 (by rfl) ⟨3200264, by rfl⟩ : syracuseStep 4267019 = 6400529) B6400529
theorem B1121339 : Blo 746329 1121339 := bstep (se 1 (by rfl) ⟨841004, by rfl⟩ : syracuseStep 1121339 = 1682009) B1682009
theorem B1121399 : Blo 746329 1121399 := bstep (se 1 (by rfl) ⟨841049, by rfl⟩ : syracuseStep 1121399 = 1682099) B1682099
theorem B1121423 : Blo 746329 1121423 := bstep (se 1 (by rfl) ⟨841067, by rfl⟩ : syracuseStep 1121423 = 1682135) B1682135
theorem B1121465 : Blo 746329 1121465 := bstep (se 2 (by rfl) ⟨420549, by rfl⟩ : syracuseStep 1121465 = 841099) B841099
theorem B4267201 : Blo 746329 4267201 := bstep (se 2 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 4267201 = 3200401) B3200401
theorem B1121543 : Blo 746329 1121543 := bstep (se 1 (by rfl) ⟨841157, by rfl⟩ : syracuseStep 1121543 = 1682315) B1682315
theorem B6397217 : Blo 746329 6397217 := bstep (se 2 (by rfl) ⟨2398956, by rfl⟩ : syracuseStep 6397217 = 4797913) B4797913
theorem B1121579 : Blo 746329 1121579 := bstep (se 1 (by rfl) ⟨841184, by rfl⟩ : syracuseStep 1121579 = 1682369) B1682369
theorem B1121609 : Blo 746329 1121609 := bstep (se 2 (by rfl) ⟨420603, by rfl⟩ : syracuseStep 1121609 = 841207) B841207
theorem B6495623 : Blo 746329 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B2399635 : Blo 746329 2399635 := bstep (se 1 (by rfl) ⟨1799726, by rfl⟩ : syracuseStep 2399635 = 3599453) B3599453
theorem B1121723 : Blo 746329 1121723 := bstep (se 1 (by rfl) ⟨841292, by rfl⟩ : syracuseStep 1121723 = 1682585) B1682585
theorem B1973705 : Blo 746329 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B1121783 : Blo 746329 1121783 := bstep (se 1 (by rfl) ⟨841337, by rfl⟩ : syracuseStep 1121783 = 1682675) B1682675
theorem B1121807 : Blo 746329 1121807 := bstep (se 1 (by rfl) ⟨841355, by rfl⟩ : syracuseStep 1121807 = 1682711) B1682711
theorem B1121849 : Blo 746329 1121849 := bstep (se 2 (by rfl) ⟨420693, by rfl⟩ : syracuseStep 1121849 = 841387) B841387
theorem B1121927 : Blo 746329 1121927 := bstep (se 1 (by rfl) ⟨841445, by rfl⟩ : syracuseStep 1121927 = 1682891) B1682891
theorem B1121963 : Blo 746329 1121963 := bstep (se 1 (by rfl) ⟨841472, by rfl⟩ : syracuseStep 1121963 = 1682945) B1682945
theorem B1121993 : Blo 746329 1121993 := bstep (se 2 (by rfl) ⟨420747, by rfl⟩ : syracuseStep 1121993 = 841495) B841495
theorem B2531087 : Blo 746329 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B2301755 : Blo 746329 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1122107 : Blo 746329 1122107 := bstep (se 1 (by rfl) ⟨841580, by rfl⟩ : syracuseStep 1122107 = 1683161) B1683161
theorem B1122167 : Blo 746329 1122167 := bstep (se 1 (by rfl) ⟨841625, by rfl⟩ : syracuseStep 1122167 = 1683251) B1683251
theorem B1122191 : Blo 746329 1122191 := bstep (se 1 (by rfl) ⟨841643, by rfl⟩ : syracuseStep 1122191 = 1683287) B1683287
theorem B1122233 : Blo 746329 1122233 := bstep (se 2 (by rfl) ⟨420837, by rfl⟩ : syracuseStep 1122233 = 841675) B841675
theorem B1122311 : Blo 746329 1122311 := bstep (se 1 (by rfl) ⟨841733, by rfl⟩ : syracuseStep 1122311 = 1683467) B1683467
theorem B2531357 : Blo 746329 2531357 := bstep (se 3 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 2531357 = 949259) B949259
theorem B36347939 : Blo 746329 36347939 := bstep (se 1 (by rfl) ⟨27260954, by rfl⟩ : syracuseStep 36347939 = 54521909) B54521909
theorem B1122347 : Blo 746329 1122347 := bstep (se 1 (by rfl) ⟨841760, by rfl⟩ : syracuseStep 1122347 = 1683521) B1683521
theorem B1122377 : Blo 746329 1122377 := bstep (se 2 (by rfl) ⟨420891, by rfl⟩ : syracuseStep 1122377 = 841783) B841783
theorem B1417351 : Blo 746329 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B1679507 : Blo 746329 1679507 := bstep (se 1 (by rfl) ⟨1259630, by rfl⟩ : syracuseStep 1679507 = 2519261) B2519261
theorem B1122491 : Blo 746329 1122491 := bstep (se 1 (by rfl) ⟨841868, by rfl⟩ : syracuseStep 1122491 = 1683737) B1683737
theorem B1679561 : Blo 746329 1679561 := bstep (se 2 (by rfl) ⟨629835, by rfl⟩ : syracuseStep 1679561 = 1259671) B1259671
theorem B1122551 : Blo 746329 1122551 := bstep (se 1 (by rfl) ⟨841913, by rfl⟩ : syracuseStep 1122551 = 1683827) B1683827
theorem B1122575 : Blo 746329 1122575 := bstep (se 1 (by rfl) ⟨841931, by rfl⟩ : syracuseStep 1122575 = 1683863) B1683863
theorem B1122617 : Blo 746329 1122617 := bstep (se 2 (by rfl) ⟨420981, by rfl⟩ : syracuseStep 1122617 = 841963) B841963
theorem B1122695 : Blo 746329 1122695 := bstep (se 1 (by rfl) ⟨842021, by rfl⟩ : syracuseStep 1122695 = 1684043) B1684043
theorem B1122731 : Blo 746329 1122731 := bstep (se 1 (by rfl) ⟨842048, by rfl⟩ : syracuseStep 1122731 = 1684097) B1684097
theorem B1122761 : Blo 746329 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B10789361 : Blo 746329 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B1122875 : Blo 746329 1122875 := bstep (se 1 (by rfl) ⟨842156, by rfl⟩ : syracuseStep 1122875 = 1684313) B1684313
theorem B1122935 : Blo 746329 1122935 := bstep (se 1 (by rfl) ⟨842201, by rfl⟩ : syracuseStep 1122935 = 1684403) B1684403
theorem B1122959 : Blo 746329 1122959 := bstep (se 1 (by rfl) ⟨842219, by rfl⟩ : syracuseStep 1122959 = 1684439) B1684439
theorem B1123001 : Blo 746329 1123001 := bstep (se 2 (by rfl) ⟨421125, by rfl⟩ : syracuseStep 1123001 = 842251) B842251
theorem B3646145 : Blo 746329 3646145 := bstep (se 2 (by rfl) ⟨1367304, by rfl⟩ : syracuseStep 3646145 = 2734609) B2734609
theorem B1123079 : Blo 746329 1123079 := bstep (se 1 (by rfl) ⟨842309, by rfl⟩ : syracuseStep 1123079 = 1684619) B1684619
theorem B1123115 : Blo 746329 1123115 := bstep (se 1 (by rfl) ⟨842336, by rfl⟩ : syracuseStep 1123115 = 1684673) B1684673
theorem B1123145 : Blo 746329 1123145 := bstep (se 2 (by rfl) ⟨421179, by rfl⟩ : syracuseStep 1123145 = 842359) B842359
theorem B1680263 : Blo 746329 1680263 := bstep (se 1 (by rfl) ⟨1260197, by rfl⟩ : syracuseStep 1680263 = 2520395) B2520395
theorem B1123259 : Blo 746329 1123259 := bstep (se 1 (by rfl) ⟨842444, by rfl⟩ : syracuseStep 1123259 = 1684889) B1684889
theorem B1123319 : Blo 746329 1123319 := bstep (se 1 (by rfl) ⟨842489, by rfl⟩ : syracuseStep 1123319 = 1684979) B1684979
theorem B1123343 : Blo 746329 1123343 := bstep (se 1 (by rfl) ⟨842507, by rfl⟩ : syracuseStep 1123343 = 1685015) B1685015
theorem B1123385 : Blo 746329 1123385 := bstep (se 2 (by rfl) ⟨421269, by rfl⟩ : syracuseStep 1123385 = 842539) B842539
theorem B1680443 : Blo 746329 1680443 := bstep (se 1 (by rfl) ⟨1260332, by rfl⟩ : syracuseStep 1680443 = 2520665) B2520665
theorem B1123463 : Blo 746329 1123463 := bstep (se 1 (by rfl) ⟨842597, by rfl⟩ : syracuseStep 1123463 = 1685195) B1685195
theorem B1123499 : Blo 746329 1123499 := bstep (se 1 (by rfl) ⟨842624, by rfl⟩ : syracuseStep 1123499 = 1685249) B1685249
theorem B1680569 : Blo 746329 1680569 := bstep (se 2 (by rfl) ⟨630213, by rfl⟩ : syracuseStep 1680569 = 1260427) B1260427
theorem B1123529 : Blo 746329 1123529 := bstep (se 2 (by rfl) ⟨421323, by rfl⟩ : syracuseStep 1123529 = 842647) B842647
theorem B2401481 : Blo 746329 2401481 := bstep (se 2 (by rfl) ⟨900555, by rfl⟩ : syracuseStep 2401481 = 1801111) B1801111
theorem B1123643 : Blo 746329 1123643 := bstep (se 1 (by rfl) ⟨842732, by rfl⟩ : syracuseStep 1123643 = 1685465) B1685465
theorem B1123703 : Blo 746329 1123703 := bstep (se 1 (by rfl) ⟨842777, by rfl⟩ : syracuseStep 1123703 = 1685555) B1685555
theorem B1123727 : Blo 746329 1123727 := bstep (se 1 (by rfl) ⟨842795, by rfl⟩ : syracuseStep 1123727 = 1685591) B1685591
theorem B8529299 : Blo 746329 8529299 := bstep (se 1 (by rfl) ⟨6396974, by rfl⟩ : syracuseStep 8529299 = 12793949) B12793949
theorem B1123769 : Blo 746329 1123769 := bstep (se 2 (by rfl) ⟨421413, by rfl⟩ : syracuseStep 1123769 = 842827) B842827
theorem B1123847 : Blo 746329 1123847 := bstep (se 1 (by rfl) ⟨842885, by rfl⟩ : syracuseStep 1123847 = 1685771) B1685771
theorem B1680911 : Blo 746329 1680911 := bstep (se 1 (by rfl) ⟨1260683, by rfl⟩ : syracuseStep 1680911 = 2521367) B2521367
theorem B1680929 : Blo 746329 1680929 := bstep (se 2 (by rfl) ⟨630348, by rfl⟩ : syracuseStep 1680929 = 1260697) B1260697
theorem B1123883 : Blo 746329 1123883 := bstep (se 1 (by rfl) ⟨842912, by rfl⟩ : syracuseStep 1123883 = 1685825) B1685825
theorem B1123913 : Blo 746329 1123913 := bstep (se 2 (by rfl) ⟨421467, by rfl⟩ : syracuseStep 1123913 = 842935) B842935
theorem B1124027 : Blo 746329 1124027 := bstep (se 1 (by rfl) ⟨843020, by rfl⟩ : syracuseStep 1124027 = 1686041) B1686041
theorem B1418953 : Blo 746329 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B24323813 : Blo 746329 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B1124087 : Blo 746329 1124087 := bstep (se 1 (by rfl) ⟨843065, by rfl⟩ : syracuseStep 1124087 = 1686131) B1686131
theorem B1124111 : Blo 746329 1124111 := bstep (se 1 (by rfl) ⟨843083, by rfl⟩ : syracuseStep 1124111 = 1686167) B1686167
theorem B5121829 : Blo 746329 5121829 := bstep (se 4 (by rfl) ⟨480171, by rfl⟩ : syracuseStep 5121829 = 960343) B960343
theorem B1124153 : Blo 746329 1124153 := bstep (se 2 (by rfl) ⟨421557, by rfl⟩ : syracuseStep 1124153 = 843115) B843115
theorem B1681271 : Blo 746329 1681271 := bstep (se 1 (by rfl) ⟨1260953, by rfl⟩ : syracuseStep 1681271 = 2521907) B2521907
theorem B1124231 : Blo 746329 1124231 := bstep (se 1 (by rfl) ⟨843173, by rfl⟩ : syracuseStep 1124231 = 1686347) B1686347
theorem B1124267 : Blo 746329 1124267 := bstep (se 1 (by rfl) ⟨843200, by rfl⟩ : syracuseStep 1124267 = 1686401) B1686401
theorem B1124297 : Blo 746329 1124297 := bstep (se 2 (by rfl) ⟨421611, by rfl⟩ : syracuseStep 1124297 = 843223) B843223
theorem B960503 : Blo 746329 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B1681451 : Blo 746329 1681451 := bstep (se 1 (by rfl) ⟨1261088, by rfl⟩ : syracuseStep 1681451 = 2522177) B2522177
theorem B1124411 : Blo 746329 1124411 := bstep (se 1 (by rfl) ⟨843308, by rfl⟩ : syracuseStep 1124411 = 1686617) B1686617
theorem B1124471 : Blo 746329 1124471 := bstep (se 1 (by rfl) ⟨843353, by rfl⟩ : syracuseStep 1124471 = 1686707) B1686707
theorem B1124495 : Blo 746329 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B1124537 : Blo 746329 1124537 := bstep (se 2 (by rfl) ⟨421701, by rfl⟩ : syracuseStep 1124537 = 843403) B843403
theorem B1124615 : Blo 746329 1124615 := bstep (se 1 (by rfl) ⟨843461, by rfl⟩ : syracuseStep 1124615 = 1686923) B1686923
theorem B1124651 : Blo 746329 1124651 := bstep (se 1 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 1124651 = 1686977) B1686977
theorem B796987 : Blo 746329 796987 := bstep (se 1 (by rfl) ⟨597740, by rfl⟩ : syracuseStep 796987 = 1195481) B1195481
theorem B1124681 : Blo 746329 1124681 := bstep (se 2 (by rfl) ⟨421755, by rfl⟩ : syracuseStep 1124681 = 843511) B843511
theorem B1681811 : Blo 746329 1681811 := bstep (se 1 (by rfl) ⟨1261358, by rfl⟩ : syracuseStep 1681811 = 2522717) B2522717
theorem B2075033 : Blo 746329 2075033 := bstep (se 2 (by rfl) ⟨778137, by rfl⟩ : syracuseStep 2075033 = 1556275) B1556275
theorem B8071609 : Blo 746329 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B1124795 : Blo 746329 1124795 := bstep (se 1 (by rfl) ⟨843596, by rfl⟩ : syracuseStep 1124795 = 1687193) B1687193
theorem B1681865 : Blo 746329 1681865 := bstep (se 2 (by rfl) ⟨630699, by rfl⟩ : syracuseStep 1681865 = 1261399) B1261399
theorem B12954097 : Blo 746329 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B1124855 : Blo 746329 1124855 := bstep (se 1 (by rfl) ⟨843641, by rfl⟩ : syracuseStep 1124855 = 1687283) B1687283
theorem B1124879 : Blo 746329 1124879 := bstep (se 1 (by rfl) ⟨843659, by rfl⟩ : syracuseStep 1124879 = 1687319) B1687319
theorem B1124921 : Blo 746329 1124921 := bstep (se 2 (by rfl) ⟨421845, by rfl⟩ : syracuseStep 1124921 = 843691) B843691
theorem B1124999 : Blo 746329 1124999 := bstep (se 1 (by rfl) ⟨843749, by rfl⟩ : syracuseStep 1124999 = 1687499) B1687499
theorem B1125035 : Blo 746329 1125035 := bstep (se 1 (by rfl) ⟨843776, by rfl⟩ : syracuseStep 1125035 = 1687553) B1687553
theorem B1125065 : Blo 746329 1125065 := bstep (se 2 (by rfl) ⟨421899, by rfl⟩ : syracuseStep 1125065 = 843799) B843799
theorem B1125179 : Blo 746329 1125179 := bstep (se 1 (by rfl) ⟨843884, by rfl⟩ : syracuseStep 1125179 = 1687769) B1687769
theorem B1125239 : Blo 746329 1125239 := bstep (se 1 (by rfl) ⟨843929, by rfl⟩ : syracuseStep 1125239 = 1687859) B1687859
theorem B1125263 : Blo 746329 1125263 := bstep (se 1 (by rfl) ⟨843947, by rfl⟩ : syracuseStep 1125263 = 1687895) B1687895
theorem B1125305 : Blo 746329 1125305 := bstep (se 2 (by rfl) ⟨421989, by rfl⟩ : syracuseStep 1125305 = 843979) B843979
theorem B4041731 : Blo 746329 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B1125383 : Blo 746329 1125383 := bstep (se 1 (by rfl) ⟨844037, by rfl⟩ : syracuseStep 1125383 = 1688075) B1688075
theorem B1125419 : Blo 746329 1125419 := bstep (se 1 (by rfl) ⟨844064, by rfl⟩ : syracuseStep 1125419 = 1688129) B1688129
theorem B1125449 : Blo 746329 1125449 := bstep (se 2 (by rfl) ⟨422043, by rfl⟩ : syracuseStep 1125449 = 844087) B844087
theorem B1682567 : Blo 746329 1682567 := bstep (se 1 (by rfl) ⟨1261925, by rfl⟩ : syracuseStep 1682567 = 2523851) B2523851
theorem B3190049 : Blo 746329 3190049 := bstep (se 2 (by rfl) ⟨1196268, by rfl⟩ : syracuseStep 3190049 = 2392537) B2392537
theorem B4795681 : Blo 746329 4795681 := bstep (se 2 (by rfl) ⟨1798380, by rfl⟩ : syracuseStep 4795681 = 3596761) B3596761
theorem B4271393 : Blo 746329 4271393 := bstep (se 2 (by rfl) ⟨1601772, by rfl⟩ : syracuseStep 4271393 = 3203545) B3203545
theorem B1682747 : Blo 746329 1682747 := bstep (se 1 (by rfl) ⟨1262060, by rfl⟩ : syracuseStep 1682747 = 2524121) B2524121
theorem B1682873 : Blo 746329 1682873 := bstep (se 2 (by rfl) ⟨631077, by rfl⟩ : syracuseStep 1682873 = 1262155) B1262155
theorem B2272769 : Blo 746329 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B3780107 : Blo 746329 3780107 := bstep (se 1 (by rfl) ⟨2835080, by rfl⟩ : syracuseStep 3780107 = 5670161) B5670161
theorem B3780269 : Blo 746329 3780269 := bstep (se 3 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 3780269 = 1417601) B1417601
theorem B1683215 : Blo 746329 1683215 := bstep (se 1 (by rfl) ⟨1262411, by rfl⟩ : syracuseStep 1683215 = 2524823) B2524823
theorem B1683233 : Blo 746329 1683233 := bstep (se 2 (by rfl) ⟨631212, by rfl⟩ : syracuseStep 1683233 = 1262425) B1262425
theorem B1683575 : Blo 746329 1683575 := bstep (se 1 (by rfl) ⟨1262681, by rfl⟩ : syracuseStep 1683575 = 2525363) B2525363
theorem B1421459 : Blo 746329 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1519817 : Blo 746329 1519817 := bstep (se 2 (by rfl) ⟨569931, by rfl⟩ : syracuseStep 1519817 = 1139863) B1139863
theorem B1683755 : Blo 746329 1683755 := bstep (se 1 (by rfl) ⟨1262816, by rfl⟩ : syracuseStep 1683755 = 2525633) B2525633
theorem B1519931 : Blo 746329 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B1421687 : Blo 746329 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B1684115 : Blo 746329 1684115 := bstep (se 1 (by rfl) ⟨1263086, by rfl⟩ : syracuseStep 1684115 = 2526173) B2526173
theorem B1684169 : Blo 746329 1684169 := bstep (se 2 (by rfl) ⟨631563, by rfl⟩ : syracuseStep 1684169 = 1263127) B1263127
theorem B3781889 : Blo 746329 3781889 := bstep (se 2 (by rfl) ⟨1418208, by rfl⟩ : syracuseStep 3781889 = 2836417) B2836417
theorem B2274571 : Blo 746329 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B800015 : Blo 746329 800015 := bstep (se 1 (by rfl) ⟨600011, by rfl⟩ : syracuseStep 800015 = 1200023) B1200023
theorem B1684871 : Blo 746329 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B1685051 : Blo 746329 1685051 := bstep (se 1 (by rfl) ⟨1263788, by rfl⟩ : syracuseStep 1685051 = 2527577) B2527577
theorem B1947223 : Blo 746329 1947223 := bstep (se 1 (by rfl) ⟨1460417, by rfl⟩ : syracuseStep 1947223 = 2920835) B2920835
theorem B1685177 : Blo 746329 1685177 := bstep (se 2 (by rfl) ⟨631941, by rfl⟩ : syracuseStep 1685177 = 1263883) B1263883
theorem B800647 : Blo 746329 800647 := bstep (se 1 (by rfl) ⟨600485, by rfl⟩ : syracuseStep 800647 = 1200971) B1200971
theorem B1685519 : Blo 746329 1685519 := bstep (se 1 (by rfl) ⟨1264139, by rfl⟩ : syracuseStep 1685519 = 2528279) B2528279
theorem B1685537 : Blo 746329 1685537 := bstep (se 2 (by rfl) ⟨632076, by rfl⟩ : syracuseStep 1685537 = 1264153) B1264153
theorem B1259563 : Blo 746329 1259563 := bstep (se 1 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 1259563 = 1889345) B1889345
theorem B3782699 : Blo 746329 3782699 := bstep (se 1 (by rfl) ⟨2837024, by rfl⟩ : syracuseStep 3782699 = 5674049) B5674049
theorem B1423403 : Blo 746329 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B1062985 : Blo 746329 1062985 := bstep (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) B797239
theorem B4044973 : Blo 746329 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B1259705 : Blo 746329 1259705 := bstep (se 2 (by rfl) ⟨472389, by rfl⟩ : syracuseStep 1259705 = 944779) B944779
theorem B1423631 : Blo 746329 1423631 := bstep (se 1 (by rfl) ⟨1067723, by rfl⟩ : syracuseStep 1423631 = 2135447) B2135447
theorem B2308439 : Blo 746329 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B8501597 : Blo 746329 8501597 := bstep (se 3 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 8501597 = 3188099) B3188099
theorem B1685879 : Blo 746329 1685879 := bstep (se 1 (by rfl) ⟨1264409, by rfl⟩ : syracuseStep 1685879 = 2528819) B2528819
theorem B1686059 : Blo 746329 1686059 := bstep (se 1 (by rfl) ⟨1264544, by rfl⟩ : syracuseStep 1686059 = 2529089) B2529089
theorem B1063543 : Blo 746329 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B5389145 : Blo 746329 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1260407 : Blo 746329 1260407 := bstep (se 1 (by rfl) ⟨945305, by rfl⟩ : syracuseStep 1260407 = 1890611) B1890611
theorem B1686419 : Blo 746329 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B7191449 : Blo 746329 7191449 := bstep (se 2 (by rfl) ⟨2696793, by rfl⟩ : syracuseStep 7191449 = 5393587) B5393587
theorem B6831001 : Blo 746329 6831001 := bstep (se 2 (by rfl) ⟨2561625, by rfl⟩ : syracuseStep 6831001 = 5123251) B5123251
theorem B1686473 : Blo 746329 1686473 := bstep (se 2 (by rfl) ⟨632427, by rfl⟩ : syracuseStep 1686473 = 1264855) B1264855
theorem B3587075 : Blo 746329 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B3652619 : Blo 746329 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B1064107 : Blo 746329 1064107 := bstep (se 1 (by rfl) ⟨798080, by rfl⟩ : syracuseStep 1064107 = 1596161) B1596161
theorem B1260859 : Blo 746329 1260859 := bstep (se 1 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 1260859 = 1891289) B1891289
theorem B3783995 : Blo 746329 3783995 := bstep (se 1 (by rfl) ⟨2837996, by rfl⟩ : syracuseStep 3783995 = 5675993) B5675993
theorem B1064335 : Blo 746329 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B1261001 : Blo 746329 1261001 := bstep (se 2 (by rfl) ⟨472875, by rfl⟩ : syracuseStep 1261001 = 945751) B945751
theorem B3784157 : Blo 746329 3784157 := bstep (se 3 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 3784157 = 1419059) B1419059
theorem B1818155 : Blo 746329 1818155 := bstep (se 1 (by rfl) ⟨1363616, by rfl⟩ : syracuseStep 1818155 = 2727233) B2727233
theorem B2833987 : Blo 746329 2833987 := bstep (se 1 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 2833987 = 4250981) B4250981
theorem B1687175 : Blo 746329 1687175 := bstep (se 1 (by rfl) ⟨1265381, by rfl⟩ : syracuseStep 1687175 = 2530763) B2530763
theorem B16203415 : Blo 746329 16203415 := bstep (se 1 (by rfl) ⟨12152561, by rfl⟩ : syracuseStep 16203415 = 24305123) B24305123
theorem B8503055 : Blo 746329 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B3784481 : Blo 746329 3784481 := bstep (se 2 (by rfl) ⟨1419180, by rfl⟩ : syracuseStep 3784481 = 2838361) B2838361
theorem B1687355 : Blo 746329 1687355 := bstep (se 1 (by rfl) ⟨1265516, by rfl⟩ : syracuseStep 1687355 = 2531033) B2531033
theorem B2834291 : Blo 746329 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B769927 : Blo 746329 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B20234137 : Blo 746329 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B1687481 : Blo 746329 1687481 := bstep (se 2 (by rfl) ⟨632805, by rfl⟩ : syracuseStep 1687481 = 1265611) B1265611
theorem B1261703 : Blo 746329 1261703 := bstep (se 1 (by rfl) ⟨946277, by rfl⟩ : syracuseStep 1261703 = 1892555) B1892555
theorem B1687823 : Blo 746329 1687823 := bstep (se 1 (by rfl) ⟨1265867, by rfl⟩ : syracuseStep 1687823 = 2531735) B2531735
theorem B1687841 : Blo 746329 1687841 := bstep (se 2 (by rfl) ⟨632940, by rfl⟩ : syracuseStep 1687841 = 1265881) B1265881
theorem B2834747 : Blo 746329 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B5685713 : Blo 746329 5685713 := bstep (se 2 (by rfl) ⟨2132142, by rfl⟩ : syracuseStep 5685713 = 4264285) B4264285
theorem B1065479 : Blo 746329 1065479 := bstep (se 1 (by rfl) ⟨799109, by rfl⟩ : syracuseStep 1065479 = 1598219) B1598219
theorem B1688183 : Blo 746329 1688183 := bstep (se 1 (by rfl) ⟨1266137, by rfl⟩ : syracuseStep 1688183 = 2532275) B2532275
theorem B9126593 : Blo 746329 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B1065673 : Blo 746329 1065673 := bstep (se 2 (by rfl) ⟨399627, by rfl⟩ : syracuseStep 1065673 = 799255) B799255
theorem B3785453 : Blo 746329 3785453 := bstep (se 3 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 3785453 = 1419545) B1419545
theorem B1262351 : Blo 746329 1262351 := bstep (se 1 (by rfl) ⟨946763, by rfl⟩ : syracuseStep 1262351 = 1893527) B1893527
theorem B2835233 : Blo 746329 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B3589073 : Blo 746329 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1066231 : Blo 746329 1066231 := bstep (se 1 (by rfl) ⟨799673, by rfl⟩ : syracuseStep 1066231 = 1599347) B1599347
theorem B1262891 : Blo 746329 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B1918409 : Blo 746329 1918409 := bstep (se 2 (by rfl) ⟨719403, by rfl⟩ : syracuseStep 1918409 = 1438807) B1438807
theorem B3786263 : Blo 746329 3786263 := bstep (se 1 (by rfl) ⟨2839697, by rfl⟩ : syracuseStep 3786263 = 5679395) B5679395
theorem B1263289 : Blo 746329 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B2836205 : Blo 746329 2836205 := bstep (se 3 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 2836205 = 1063577) B1063577
theorem B6080305 : Blo 746329 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B2049907 : Blo 746329 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B1066937 : Blo 746329 1066937 := bstep (se 2 (by rfl) ⟨400101, by rfl⟩ : syracuseStep 1066937 = 800203) B800203
theorem B1067023 : Blo 746329 1067023 := bstep (se 1 (by rfl) ⟨800267, by rfl⟩ : syracuseStep 1067023 = 1600535) B1600535
theorem B1624079 : Blo 746329 1624079 := bstep (se 1 (by rfl) ⟨1218059, by rfl⟩ : syracuseStep 1624079 = 2436119) B2436119
theorem B1067051 : Blo 746329 1067051 := bstep (se 1 (by rfl) ⟨800288, by rfl⟩ : syracuseStep 1067051 = 1600577) B1600577
theorem B1198351 : Blo 746329 1198351 := bstep (se 1 (by rfl) ⟨898763, by rfl⟩ : syracuseStep 1198351 = 1797527) B1797527
theorem B1263991 : Blo 746329 1263991 := bstep (se 1 (by rfl) ⟨947993, by rfl⟩ : syracuseStep 1263991 = 1895987) B1895987
theorem B2836889 : Blo 746329 2836889 := bstep (se 2 (by rfl) ⟨1063833, by rfl⟩ : syracuseStep 2836889 = 2127667) B2127667
theorem B7195139 : Blo 746329 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B1264187 : Blo 746329 1264187 := bstep (se 1 (by rfl) ⟨948140, by rfl⟩ : syracuseStep 1264187 = 1896281) B1896281
theorem B1198793 : Blo 746329 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B2280251 : Blo 746329 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B2018249 : Blo 746329 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1264585 : Blo 746329 1264585 := bstep (se 2 (by rfl) ⟨474219, by rfl⟩ : syracuseStep 1264585 = 948439) B948439
theorem B14797835 : Blo 746329 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B6409277 : Blo 746329 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B2837875 : Blo 746329 2837875 := bstep (se 1 (by rfl) ⟨2128406, by rfl⟩ : syracuseStep 2837875 = 4256813) B4256813
theorem B2706803 : Blo 746329 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B1265287 : Blo 746329 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B2281331 : Blo 746329 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B16175051 : Blo 746329 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B839695 : Blo 746329 839695 := bstep (se 1 (by rfl) ⟨629771, by rfl⟩ : syracuseStep 839695 = 1259543) B1259543
theorem B6475949 : Blo 746329 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B1265935 : Blo 746329 1265935 := bstep (se 1 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 1265935 = 1898903) B1898903
theorem B4542809 : Blo 746329 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B840199 : Blo 746329 840199 := bstep (se 1 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 840199 = 1260299) B1260299
theorem B3789341 : Blo 746329 3789341 := bstep (se 3 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 3789341 = 1421003) B1421003
theorem B840379 : Blo 746329 840379 := bstep (se 1 (by rfl) ⟨630284, by rfl⟩ : syracuseStep 840379 = 1260569) B1260569
theorem B8540963 : Blo 746329 8540963 := bstep (se 1 (by rfl) ⟨6405722, by rfl⟩ : syracuseStep 8540963 = 12811445) B12811445
theorem B3789827 : Blo 746329 3789827 := bstep (se 1 (by rfl) ⟨2842370, by rfl⟩ : syracuseStep 3789827 = 5684741) B5684741
theorem B840847 : Blo 746329 840847 := bstep (se 1 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 840847 = 1261271) B1261271
theorem B1594657 : Blo 746329 1594657 := bstep (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) B1195993
theorem B4609331 : Blo 746329 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B1889689 : Blo 746329 1889689 := bstep (se 2 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 1889689 = 1417267) B1417267
theorem B2840093 : Blo 746329 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B1889851 : Blo 746329 1889851 := bstep (se 1 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 1889851 = 2834777) B2834777
theorem B3200573 : Blo 746329 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B841351 : Blo 746329 841351 := bstep (se 1 (by rfl) ⟨631013, by rfl⟩ : syracuseStep 841351 = 1262027) B1262027
theorem B1889993 : Blo 746329 1889993 := bstep (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) B1417495
theorem B841531 : Blo 746329 841531 := bstep (se 1 (by rfl) ⟨631148, by rfl⟩ : syracuseStep 841531 = 1262297) B1262297
theorem B1824631 : Blo 746329 1824631 := bstep (se 1 (by rfl) ⟨1368473, by rfl⟩ : syracuseStep 1824631 = 2736947) B2736947
theorem B2021267 : Blo 746329 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3594131 : Blo 746329 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1890337 : Blo 746329 1890337 := bstep (se 2 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 1890337 = 1417753) B1417753
theorem B6379721 : Blo 746329 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B2840777 : Blo 746329 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B841999 : Blo 746329 841999 := bstep (se 1 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 841999 = 1262999) B1262999
theorem B13687339 : Blo 746329 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B3791447 : Blo 746329 3791447 := bstep (se 1 (by rfl) ⟨2843585, by rfl⟩ : syracuseStep 3791447 = 5687171) B5687171
theorem B1890935 : Blo 746329 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B842503 : Blo 746329 842503 := bstep (se 1 (by rfl) ⟨631877, by rfl⟩ : syracuseStep 842503 = 1263755) B1263755
theorem B1596203 : Blo 746329 1596203 := bstep (se 1 (by rfl) ⟨1197152, by rfl⟩ : syracuseStep 1596203 = 2394305) B2394305
theorem B842683 : Blo 746329 842683 := bstep (se 1 (by rfl) ⟨632012, by rfl⟩ : syracuseStep 842683 = 1264025) B1264025
theorem B2022401 : Blo 746329 2022401 := bstep (se 2 (by rfl) ⟨758400, by rfl⟩ : syracuseStep 2022401 = 1516801) B1516801
theorem B3791933 : Blo 746329 3791933 := bstep (se 3 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 3791933 = 1421975) B1421975
theorem B843151 : Blo 746329 843151 := bstep (se 1 (by rfl) ⟨632363, by rfl⟩ : syracuseStep 843151 = 1264727) B1264727
theorem B1924505 : Blo 746329 1924505 := bstep (se 2 (by rfl) ⟨721689, by rfl⟩ : syracuseStep 1924505 = 1443379) B1443379
theorem B2022857 : Blo 746329 2022857 := bstep (se 2 (by rfl) ⟨758571, by rfl⟩ : syracuseStep 2022857 = 1517143) B1517143
theorem B2022941 : Blo 746329 2022941 := bstep (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) B758603
theorem B3038921 : Blo 746329 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B4054835 : Blo 746329 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B3596147 : Blo 746329 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B1892231 : Blo 746329 1892231 := bstep (se 1 (by rfl) ⟨1419173, by rfl⟩ : syracuseStep 1892231 = 2838347) B2838347
theorem B843655 : Blo 746329 843655 := bstep (se 1 (by rfl) ⟨632741, by rfl⟩ : syracuseStep 843655 = 1265483) B1265483
theorem B1892281 : Blo 746329 1892281 := bstep (se 2 (by rfl) ⟨709605, by rfl⟩ : syracuseStep 1892281 = 1419211) B1419211
theorem B2842553 : Blo 746329 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B843835 : Blo 746329 843835 := bstep (se 1 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 843835 = 1265753) B1265753
theorem B8511803 : Blo 746329 8511803 := bstep (se 1 (by rfl) ⟨6383852, by rfl⟩ : syracuseStep 8511803 = 12767705) B12767705
theorem B1597843 : Blo 746329 1597843 := bstep (se 1 (by rfl) ⟨1198382, by rfl⟩ : syracuseStep 1597843 = 2396765) B2396765
theorem B1892879 : Blo 746329 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B3596993 : Blo 746329 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B3793715 : Blo 746329 3793715 := bstep (se 1 (by rfl) ⟨2845286, by rfl⟩ : syracuseStep 3793715 = 5690573) B5690573
theorem B746375 : Blo 746329 746375 := bstep (se 1 (by rfl) ⟨559781, by rfl⟩ : syracuseStep 746375 = 1119563) B1119563
theorem B746383 : Blo 746329 746383 := bstep (se 1 (by rfl) ⟨559787, by rfl⟩ : syracuseStep 746383 = 1119575) B1119575
theorem B746427 : Blo 746329 746427 := bstep (se 1 (by rfl) ⟨559820, by rfl⟩ : syracuseStep 746427 = 1119641) B1119641
theorem B746503 : Blo 746329 746503 := bstep (se 1 (by rfl) ⟨559877, by rfl⟩ : syracuseStep 746503 = 1119755) B1119755
theorem B746511 : Blo 746329 746511 := bstep (se 1 (by rfl) ⟨559883, by rfl⟩ : syracuseStep 746511 = 1119767) B1119767
theorem B2024477 : Blo 746329 2024477 := bstep (se 3 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 2024477 = 759179) B759179
theorem B746555 : Blo 746329 746555 := bstep (se 1 (by rfl) ⟨559916, by rfl⟩ : syracuseStep 746555 = 1119833) B1119833
theorem B3794039 : Blo 746329 3794039 := bstep (se 1 (by rfl) ⟨2845529, by rfl⟩ : syracuseStep 3794039 = 5691059) B5691059
theorem B746631 : Blo 746329 746631 := bstep (se 1 (by rfl) ⟨559973, by rfl⟩ : syracuseStep 746631 = 1119947) B1119947
theorem B746639 : Blo 746329 746639 := bstep (se 1 (by rfl) ⟨559979, by rfl⟩ : syracuseStep 746639 = 1119959) B1119959
theorem B746683 : Blo 746329 746683 := bstep (se 1 (by rfl) ⟨560012, by rfl⟩ : syracuseStep 746683 = 1120025) B1120025
theorem B1893577 : Blo 746329 1893577 := bstep (se 2 (by rfl) ⟨710091, by rfl⟩ : syracuseStep 1893577 = 1420183) B1420183
theorem B746759 : Blo 746329 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B746767 : Blo 746329 746767 := bstep (se 1 (by rfl) ⟨560075, by rfl⟩ : syracuseStep 746767 = 1120151) B1120151
theorem B746811 : Blo 746329 746811 := bstep (se 1 (by rfl) ⟨560108, by rfl⟩ : syracuseStep 746811 = 1120217) B1120217
theorem B1893719 : Blo 746329 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B746887 : Blo 746329 746887 := bstep (se 1 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 746887 = 1120331) B1120331
theorem B746895 : Blo 746329 746895 := bstep (se 1 (by rfl) ⟨560171, by rfl⟩ : syracuseStep 746895 = 1120343) B1120343
theorem B1009081 : Blo 746329 1009081 := bstep (se 2 (by rfl) ⟨378405, by rfl⟩ : syracuseStep 1009081 = 756811) B756811
theorem B6383033 : Blo 746329 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B746939 : Blo 746329 746939 := bstep (se 1 (by rfl) ⟨560204, by rfl⟩ : syracuseStep 746939 = 1120409) B1120409
theorem B747015 : Blo 746329 747015 := bstep (se 1 (by rfl) ⟨560261, by rfl⟩ : syracuseStep 747015 = 1120523) B1120523
theorem B747023 : Blo 746329 747023 := bstep (se 1 (by rfl) ⟨560267, by rfl⟩ : syracuseStep 747023 = 1120535) B1120535
theorem B747067 : Blo 746329 747067 := bstep (se 1 (by rfl) ⟨560300, by rfl⟩ : syracuseStep 747067 = 1120601) B1120601
theorem B747143 : Blo 746329 747143 := bstep (se 1 (by rfl) ⟨560357, by rfl⟩ : syracuseStep 747143 = 1120715) B1120715
theorem B747151 : Blo 746329 747151 := bstep (se 1 (by rfl) ⟨560363, by rfl⟩ : syracuseStep 747151 = 1120727) B1120727
theorem B7300787 : Blo 746329 7300787 := bstep (se 1 (by rfl) ⟨5475590, by rfl⟩ : syracuseStep 7300787 = 10951181) B10951181
theorem B747195 : Blo 746329 747195 := bstep (se 1 (by rfl) ⟨560396, by rfl⟩ : syracuseStep 747195 = 1120793) B1120793
theorem B3204845 : Blo 746329 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B747271 : Blo 746329 747271 := bstep (se 1 (by rfl) ⟨560453, by rfl⟩ : syracuseStep 747271 = 1120907) B1120907
theorem B747279 : Blo 746329 747279 := bstep (se 1 (by rfl) ⟨560459, by rfl⟩ : syracuseStep 747279 = 1120919) B1120919
theorem B747323 : Blo 746329 747323 := bstep (se 1 (by rfl) ⟨560492, by rfl⟩ : syracuseStep 747323 = 1120985) B1120985
theorem B747399 : Blo 746329 747399 := bstep (se 1 (by rfl) ⟨560549, by rfl⟩ : syracuseStep 747399 = 1121099) B1121099
theorem B747407 : Blo 746329 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B1009579 : Blo 746329 1009579 := bstep (se 1 (by rfl) ⟨757184, by rfl⟩ : syracuseStep 1009579 = 1514369) B1514369
theorem B747451 : Blo 746329 747451 := bstep (se 1 (by rfl) ⟨560588, by rfl⟩ : syracuseStep 747451 = 1121177) B1121177
theorem B3598283 : Blo 746329 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B747527 : Blo 746329 747527 := bstep (se 1 (by rfl) ⟨560645, by rfl⟩ : syracuseStep 747527 = 1121291) B1121291
theorem B747535 : Blo 746329 747535 := bstep (se 1 (by rfl) ⟨560651, by rfl⟩ : syracuseStep 747535 = 1121303) B1121303
theorem B747579 : Blo 746329 747579 := bstep (se 1 (by rfl) ⟨560684, by rfl⟩ : syracuseStep 747579 = 1121369) B1121369
theorem B3795011 : Blo 746329 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B747655 : Blo 746329 747655 := bstep (se 1 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 747655 = 1121483) B1121483
theorem B747663 : Blo 746329 747663 := bstep (se 1 (by rfl) ⟨560747, by rfl⟩ : syracuseStep 747663 = 1121495) B1121495
theorem B1796249 : Blo 746329 1796249 := bstep (se 2 (by rfl) ⟨673593, by rfl⟩ : syracuseStep 1796249 = 1347187) B1347187
theorem B747707 : Blo 746329 747707 := bstep (se 1 (by rfl) ⟨560780, by rfl⟩ : syracuseStep 747707 = 1121561) B1121561
theorem B4253897 : Blo 746329 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B1599689 : Blo 746329 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B747783 : Blo 746329 747783 := bstep (se 1 (by rfl) ⟨560837, by rfl⟩ : syracuseStep 747783 = 1121675) B1121675
theorem B747791 : Blo 746329 747791 := bstep (se 1 (by rfl) ⟨560843, by rfl⟩ : syracuseStep 747791 = 1121687) B1121687
theorem B3598607 : Blo 746329 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B747835 : Blo 746329 747835 := bstep (se 1 (by rfl) ⟨560876, by rfl⟩ : syracuseStep 747835 = 1121753) B1121753
theorem B747911 : Blo 746329 747911 := bstep (se 1 (by rfl) ⟨560933, by rfl⟩ : syracuseStep 747911 = 1121867) B1121867
theorem B3795335 : Blo 746329 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B747919 : Blo 746329 747919 := bstep (se 1 (by rfl) ⟨560939, by rfl⟩ : syracuseStep 747919 = 1121879) B1121879
theorem B16214417 : Blo 746329 16214417 := bstep (se 2 (by rfl) ⟨6080406, by rfl⟩ : syracuseStep 16214417 = 12160813) B12160813
theorem B747963 : Blo 746329 747963 := bstep (se 1 (by rfl) ⟨560972, by rfl⟩ : syracuseStep 747963 = 1121945) B1121945
theorem B748039 : Blo 746329 748039 := bstep (se 1 (by rfl) ⟨561029, by rfl⟩ : syracuseStep 748039 = 1122059) B1122059
theorem B748047 : Blo 746329 748047 := bstep (se 1 (by rfl) ⟨561035, by rfl⟩ : syracuseStep 748047 = 1122071) B1122071
theorem B748091 : Blo 746329 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B748167 : Blo 746329 748167 := bstep (se 1 (by rfl) ⟨561125, by rfl⟩ : syracuseStep 748167 = 1122251) B1122251
theorem B748175 : Blo 746329 748175 := bstep (se 1 (by rfl) ⟨561131, by rfl⟩ : syracuseStep 748175 = 1122263) B1122263
theorem B748219 : Blo 746329 748219 := bstep (se 1 (by rfl) ⟨561164, by rfl⟩ : syracuseStep 748219 = 1122329) B1122329
theorem B39906053 : Blo 746329 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B748295 : Blo 746329 748295 := bstep (se 1 (by rfl) ⟨561221, by rfl⟩ : syracuseStep 748295 = 1122443) B1122443
theorem B748303 : Blo 746329 748303 := bstep (se 1 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 748303 = 1122455) B1122455
theorem B748347 : Blo 746329 748347 := bstep (se 1 (by rfl) ⟨561260, by rfl⟩ : syracuseStep 748347 = 1122521) B1122521
theorem B748423 : Blo 746329 748423 := bstep (se 1 (by rfl) ⟨561317, by rfl⟩ : syracuseStep 748423 = 1122635) B1122635
theorem B748431 : Blo 746329 748431 := bstep (se 1 (by rfl) ⟨561323, by rfl⟩ : syracuseStep 748431 = 1122647) B1122647
theorem B748475 : Blo 746329 748475 := bstep (se 1 (by rfl) ⟨561356, by rfl⟩ : syracuseStep 748475 = 1122713) B1122713
theorem B748551 : Blo 746329 748551 := bstep (se 1 (by rfl) ⟨561413, by rfl⟩ : syracuseStep 748551 = 1122827) B1122827
theorem B748559 : Blo 746329 748559 := bstep (se 1 (by rfl) ⟨561419, by rfl⟩ : syracuseStep 748559 = 1122839) B1122839
theorem B748603 : Blo 746329 748603 := bstep (se 1 (by rfl) ⟨561452, by rfl⟩ : syracuseStep 748603 = 1122905) B1122905
theorem B10546237 : Blo 746329 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B748679 : Blo 746329 748679 := bstep (se 1 (by rfl) ⟨561509, by rfl⟩ : syracuseStep 748679 = 1123019) B1123019
theorem B748687 : Blo 746329 748687 := bstep (se 1 (by rfl) ⟨561515, by rfl⟩ : syracuseStep 748687 = 1123031) B1123031
theorem B1600697 : Blo 746329 1600697 := bstep (se 2 (by rfl) ⟨600261, by rfl⟩ : syracuseStep 1600697 = 1200523) B1200523
theorem B748731 : Blo 746329 748731 := bstep (se 1 (by rfl) ⟨561548, by rfl⟩ : syracuseStep 748731 = 1123097) B1123097
theorem B748807 : Blo 746329 748807 := bstep (se 1 (by rfl) ⟨561605, by rfl⟩ : syracuseStep 748807 = 1123211) B1123211
theorem B748815 : Blo 746329 748815 := bstep (se 1 (by rfl) ⟨561611, by rfl⟩ : syracuseStep 748815 = 1123223) B1123223
theorem B748859 : Blo 746329 748859 := bstep (se 1 (by rfl) ⟨561644, by rfl⟩ : syracuseStep 748859 = 1123289) B1123289
theorem B2157911 : Blo 746329 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B1895795 : Blo 746329 1895795 := bstep (se 1 (by rfl) ⟨1421846, by rfl⟩ : syracuseStep 1895795 = 2843693) B2843693
theorem B748935 : Blo 746329 748935 := bstep (se 1 (by rfl) ⟨561701, by rfl⟩ : syracuseStep 748935 = 1123403) B1123403
theorem B748943 : Blo 746329 748943 := bstep (se 1 (by rfl) ⟨561707, by rfl⟩ : syracuseStep 748943 = 1123415) B1123415
theorem B3599761 : Blo 746329 3599761 := bstep (se 2 (by rfl) ⟨1349910, by rfl⟩ : syracuseStep 3599761 = 2699821) B2699821
theorem B2846137 : Blo 746329 2846137 := bstep (se 2 (by rfl) ⟨1067301, by rfl⟩ : syracuseStep 2846137 = 2134603) B2134603
theorem B748987 : Blo 746329 748987 := bstep (se 1 (by rfl) ⟨561740, by rfl⟩ : syracuseStep 748987 = 1123481) B1123481
theorem B749063 : Blo 746329 749063 := bstep (se 1 (by rfl) ⟨561797, by rfl⟩ : syracuseStep 749063 = 1123595) B1123595
theorem B749071 : Blo 746329 749071 := bstep (se 1 (by rfl) ⟨561803, by rfl⟩ : syracuseStep 749071 = 1123607) B1123607
theorem B1601039 : Blo 746329 1601039 := bstep (se 1 (by rfl) ⟨1200779, by rfl⟩ : syracuseStep 1601039 = 2401559) B2401559
theorem B749115 : Blo 746329 749115 := bstep (se 1 (by rfl) ⟨561836, by rfl⟩ : syracuseStep 749115 = 1123673) B1123673
theorem B749191 : Blo 746329 749191 := bstep (se 1 (by rfl) ⟨561893, by rfl⟩ : syracuseStep 749191 = 1123787) B1123787
theorem B749199 : Blo 746329 749199 := bstep (se 1 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 749199 = 1123799) B1123799
theorem B749243 : Blo 746329 749243 := bstep (se 1 (by rfl) ⟨561932, by rfl⟩ : syracuseStep 749243 = 1123865) B1123865
theorem B749319 : Blo 746329 749319 := bstep (se 1 (by rfl) ⟨561989, by rfl⟩ : syracuseStep 749319 = 1123979) B1123979
theorem B749327 : Blo 746329 749327 := bstep (se 1 (by rfl) ⟨561995, by rfl⟩ : syracuseStep 749327 = 1123991) B1123991
theorem B749371 : Blo 746329 749371 := bstep (se 1 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 749371 = 1124057) B1124057
theorem B1896311 : Blo 746329 1896311 := bstep (se 1 (by rfl) ⟨1422233, by rfl⟩ : syracuseStep 1896311 = 2844467) B2844467
theorem B749447 : Blo 746329 749447 := bstep (se 1 (by rfl) ⟨562085, by rfl⟩ : syracuseStep 749447 = 1124171) B1124171
theorem B749455 : Blo 746329 749455 := bstep (se 1 (by rfl) ⟨562091, by rfl⟩ : syracuseStep 749455 = 1124183) B1124183
theorem B2518937 : Blo 746329 2518937 := bstep (se 2 (by rfl) ⟨944601, by rfl⟩ : syracuseStep 2518937 = 1889203) B1889203
theorem B3600281 : Blo 746329 3600281 := bstep (se 2 (by rfl) ⟨1350105, by rfl⟩ : syracuseStep 3600281 = 2700211) B2700211
theorem B749499 : Blo 746329 749499 := bstep (se 1 (by rfl) ⟨562124, by rfl⟩ : syracuseStep 749499 = 1124249) B1124249
theorem B749575 : Blo 746329 749575 := bstep (se 1 (by rfl) ⟨562181, by rfl⟩ : syracuseStep 749575 = 1124363) B1124363
theorem B749583 : Blo 746329 749583 := bstep (se 1 (by rfl) ⟨562187, by rfl⟩ : syracuseStep 749583 = 1124375) B1124375
theorem B749627 : Blo 746329 749627 := bstep (se 1 (by rfl) ⟨562220, by rfl⟩ : syracuseStep 749627 = 1124441) B1124441
theorem B4255811 : Blo 746329 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B749703 : Blo 746329 749703 := bstep (se 1 (by rfl) ⟨562277, by rfl⟩ : syracuseStep 749703 = 1124555) B1124555
theorem B749711 : Blo 746329 749711 := bstep (se 1 (by rfl) ⟨562283, by rfl⟩ : syracuseStep 749711 = 1124567) B1124567
theorem B749755 : Blo 746329 749755 := bstep (se 1 (by rfl) ⟨562316, by rfl⟩ : syracuseStep 749755 = 1124633) B1124633
theorem B749831 : Blo 746329 749831 := bstep (se 1 (by rfl) ⟨562373, by rfl⟩ : syracuseStep 749831 = 1124747) B1124747
theorem B749839 : Blo 746329 749839 := bstep (se 1 (by rfl) ⟨562379, by rfl⟩ : syracuseStep 749839 = 1124759) B1124759
theorem B749883 : Blo 746329 749883 := bstep (se 1 (by rfl) ⟨562412, by rfl⟩ : syracuseStep 749883 = 1124825) B1124825
theorem B749959 : Blo 746329 749959 := bstep (se 1 (by rfl) ⟨562469, by rfl⟩ : syracuseStep 749959 = 1124939) B1124939
theorem B1601927 : Blo 746329 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B749967 : Blo 746329 749967 := bstep (se 1 (by rfl) ⟨562475, by rfl⟩ : syracuseStep 749967 = 1124951) B1124951
theorem B750011 : Blo 746329 750011 := bstep (se 1 (by rfl) ⟨562508, by rfl⟩ : syracuseStep 750011 = 1125017) B1125017
theorem B750087 : Blo 746329 750087 := bstep (se 1 (by rfl) ⟨562565, by rfl⟩ : syracuseStep 750087 = 1125131) B1125131
theorem B750095 : Blo 746329 750095 := bstep (se 1 (by rfl) ⟨562571, by rfl⟩ : syracuseStep 750095 = 1125143) B1125143
theorem B750139 : Blo 746329 750139 := bstep (se 1 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 750139 = 1125209) B1125209
theorem B2519639 : Blo 746329 2519639 := bstep (se 1 (by rfl) ⟨1889729, by rfl⟩ : syracuseStep 2519639 = 3779459) B3779459
theorem B750215 : Blo 746329 750215 := bstep (se 1 (by rfl) ⟨562661, by rfl⟩ : syracuseStep 750215 = 1125323) B1125323
theorem B750223 : Blo 746329 750223 := bstep (se 1 (by rfl) ⟨562667, by rfl⟩ : syracuseStep 750223 = 1125335) B1125335
theorem B2126483 : Blo 746329 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B750267 : Blo 746329 750267 := bstep (se 1 (by rfl) ⟨562700, by rfl⟩ : syracuseStep 750267 = 1125401) B1125401
theorem B1602337 : Blo 746329 1602337 := bstep (se 2 (by rfl) ⟨600876, by rfl⟩ : syracuseStep 1602337 = 1201753) B1201753
theorem B1897303 : Blo 746329 1897303 := bstep (se 1 (by rfl) ⟨1422977, by rfl⟩ : syracuseStep 1897303 = 2845955) B2845955
theorem B12776453 : Blo 746329 12776453 := bstep (se 4 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 12776453 = 2395585) B2395585
theorem B2520125 : Blo 746329 2520125 := bstep (se 3 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 2520125 = 945047) B945047
theorem B1897607 : Blo 746329 1897607 := bstep (se 1 (by rfl) ⟨1423205, by rfl⟩ : syracuseStep 1897607 = 2846411) B2846411
theorem B947371 : Blo 746329 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B1897739 : Blo 746329 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B1799833 : Blo 746329 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B1898255 : Blo 746329 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B1898387 : Blo 746329 1898387 := bstep (se 1 (by rfl) ⟨1423790, by rfl⟩ : syracuseStep 1898387 = 2847581) B2847581
theorem B2127883 : Blo 746329 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B948343 : Blo 746329 948343 := bstep (se 1 (by rfl) ⟨711257, by rfl⟩ : syracuseStep 948343 = 1422515) B1422515
theorem B2128157 : Blo 746329 2128157 := bstep (se 3 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 2128157 = 798059) B798059
theorem B1702187 : Blo 746329 1702187 := bstep (se 1 (by rfl) ⟨1276640, by rfl⟩ : syracuseStep 1702187 = 2553281) B2553281
theorem B2521529 : Blo 746329 2521529 := bstep (se 2 (by rfl) ⟨945573, by rfl⟩ : syracuseStep 2521529 = 1891147) B1891147
theorem B948667 : Blo 746329 948667 := bstep (se 1 (by rfl) ⟨711500, by rfl⟩ : syracuseStep 948667 = 1423001) B1423001
theorem B3832343 : Blo 746329 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B10222199 : Blo 746329 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B1801217 : Blo 746329 1801217 := bstep (se 2 (by rfl) ⟨675456, by rfl⟩ : syracuseStep 1801217 = 1350913) B1350913
theorem B2522123 : Blo 746329 2522123 := bstep (se 1 (by rfl) ⟨1891592, by rfl⟩ : syracuseStep 2522123 = 3783185) B3783185
theorem B2522231 : Blo 746329 2522231 := bstep (se 1 (by rfl) ⟨1891673, by rfl⟩ : syracuseStep 2522231 = 3783347) B3783347
theorem B1080583 : Blo 746329 1080583 := bstep (se 1 (by rfl) ⟨810437, by rfl⟩ : syracuseStep 1080583 = 1620875) B1620875
theorem B2522825 : Blo 746329 2522825 := bstep (se 2 (by rfl) ⟨946059, by rfl⟩ : syracuseStep 2522825 = 1892119) B1892119
theorem B1802071 : Blo 746329 1802071 := bstep (se 1 (by rfl) ⟨1351553, by rfl⟩ : syracuseStep 1802071 = 2703107) B2703107
theorem B4259729 : Blo 746329 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B3407825 : Blo 746329 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B38961269 : Blo 746329 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B2523635 : Blo 746329 2523635 := bstep (se 1 (by rfl) ⟨1892726, by rfl⟩ : syracuseStep 2523635 = 3785453) B3785453
theorem B2130457 : Blo 746329 2130457 := bstep (se 2 (by rfl) ⟨798921, by rfl⟩ : syracuseStep 2130457 = 1597843) B1597843
theorem B2392715 : Blo 746329 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B2524175 : Blo 746329 2524175 := bstep (se 1 (by rfl) ⟨1893131, by rfl⟩ : syracuseStep 2524175 = 3786263) B3786263
theorem B1082719 : Blo 746329 1082719 := bstep (se 1 (by rfl) ⟨812039, by rfl⟩ : syracuseStep 1082719 = 1624079) B1624079
theorem B7210403 : Blo 746329 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B2524769 : Blo 746329 2524769 := bstep (se 2 (by rfl) ⟨946788, by rfl⟩ : syracuseStep 2524769 = 1893577) B1893577
theorem B7210745 : Blo 746329 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B1345441 : Blo 746329 1345441 := bstep (se 2 (by rfl) ⟨504540, by rfl⟩ : syracuseStep 1345441 = 1009081) B1009081
theorem B1345499 : Blo 746329 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B4261895 : Blo 746329 4261895 := bstep (se 1 (by rfl) ⟨3196421, by rfl⟩ : syracuseStep 4261895 = 6392843) B6392843
theorem B9865223 : Blo 746329 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B2558123 : Blo 746329 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B1804535 : Blo 746329 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B1346105 : Blo 746329 1346105 := bstep (se 2 (by rfl) ⟨504789, by rfl⟩ : syracuseStep 1346105 = 1009579) B1009579
theorem B10783367 : Blo 746329 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B2526227 : Blo 746329 2526227 := bstep (se 1 (by rfl) ⟨1894670, by rfl⟩ : syracuseStep 2526227 = 3789341) B3789341
theorem B17272129 : Blo 746329 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B2526551 : Blo 746329 2526551 := bstep (se 1 (by rfl) ⟨1894913, by rfl⟩ : syracuseStep 2526551 = 3789827) B3789827
theorem B2133373 : Blo 746329 2133373 := bstep (se 3 (by rfl) ⟨400007, by rfl⟩ : syracuseStep 2133373 = 800015) B800015
theorem B2133715 : Blo 746329 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B5115757 : Blo 746329 5115757 := bstep (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) B1918409
theorem B1347511 : Blo 746329 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2396087 : Blo 746329 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B14061649 : Blo 746329 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B6394241 : Blo 746329 6394241 := bstep (se 2 (by rfl) ⟨2397840, by rfl⟩ : syracuseStep 6394241 = 4795681) B4795681
theorem B2527631 : Blo 746329 2527631 := bstep (se 1 (by rfl) ⟨1895723, by rfl⟩ : syracuseStep 2527631 = 3791447) B3791447
theorem B19468765 : Blo 746329 19468765 := bstep (se 3 (by rfl) ⟨3650393, by rfl⟩ : syracuseStep 19468765 = 7300787) B7300787
theorem B2691719 : Blo 746329 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B1348267 : Blo 746329 1348267 := bstep (se 1 (by rfl) ⟨1011200, by rfl⟩ : syracuseStep 1348267 = 2022401) B2022401
theorem B2527955 : Blo 746329 2527955 := bstep (se 1 (by rfl) ⟨1895966, by rfl⟩ : syracuseStep 2527955 = 3791933) B3791933
theorem B4264811 : Blo 746329 4264811 := bstep (se 1 (by rfl) ⟨3198608, by rfl⟩ : syracuseStep 4264811 = 6397217) B6397217
theorem B4330415 : Blo 746329 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B1283003 : Blo 746329 1283003 := bstep (se 1 (by rfl) ⟨962252, by rfl⟩ : syracuseStep 1283003 = 1924505) B1924505
theorem B1348571 : Blo 746329 1348571 := bstep (se 1 (by rfl) ⟨1011428, by rfl⟩ : syracuseStep 1348571 = 2022857) B2022857
theorem B2397431 : Blo 746329 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B1119593 : Blo 746329 1119593 := bstep (se 2 (by rfl) ⟨419847, by rfl⟩ : syracuseStep 1119593 = 839695) B839695
theorem B1119671 : Blo 746329 1119671 := bstep (se 1 (by rfl) ⟨839753, by rfl⟩ : syracuseStep 1119671 = 1679507) B1679507
theorem B1119707 : Blo 746329 1119707 := bstep (se 1 (by rfl) ⟨839780, by rfl⟩ : syracuseStep 1119707 = 1679561) B1679561
theorem B5674535 : Blo 746329 5674535 := bstep (se 1 (by rfl) ⟨4255901, by rfl⟩ : syracuseStep 5674535 = 8511803) B8511803
theorem B2397995 : Blo 746329 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B2529143 : Blo 746329 2529143 := bstep (se 1 (by rfl) ⟨1896857, by rfl⟩ : syracuseStep 2529143 = 3793715) B3793715
theorem B1120175 : Blo 746329 1120175 := bstep (se 1 (by rfl) ⟨840131, by rfl⟩ : syracuseStep 1120175 = 1680263) B1680263
theorem B1120265 : Blo 746329 1120265 := bstep (se 2 (by rfl) ⟨420099, by rfl⟩ : syracuseStep 1120265 = 840199) B840199
theorem B1349651 : Blo 746329 1349651 := bstep (se 1 (by rfl) ⟨1012238, by rfl⟩ : syracuseStep 1349651 = 2024477) B2024477
theorem B1120295 : Blo 746329 1120295 := bstep (se 1 (by rfl) ⟨840221, by rfl⟩ : syracuseStep 1120295 = 1680443) B1680443
theorem B2529359 : Blo 746329 2529359 := bstep (se 1 (by rfl) ⟨1897019, by rfl⟩ : syracuseStep 2529359 = 3794039) B3794039
theorem B1120379 : Blo 746329 1120379 := bstep (se 1 (by rfl) ⟨840284, by rfl⟩ : syracuseStep 1120379 = 1680569) B1680569
theorem B1120505 : Blo 746329 1120505 := bstep (se 2 (by rfl) ⟨420189, by rfl⟩ : syracuseStep 1120505 = 840379) B840379
theorem B1120607 : Blo 746329 1120607 := bstep (se 1 (by rfl) ⟨840455, by rfl⟩ : syracuseStep 1120607 = 1680911) B1680911
theorem B1120619 : Blo 746329 1120619 := bstep (se 1 (by rfl) ⟨840464, by rfl⟩ : syracuseStep 1120619 = 1680929) B1680929
theorem B2136449 : Blo 746329 2136449 := bstep (se 2 (by rfl) ⟨801168, by rfl⟩ : syracuseStep 2136449 = 1602337) B1602337
theorem B2529737 : Blo 746329 2529737 := bstep (se 2 (by rfl) ⟨948651, by rfl⟩ : syracuseStep 2529737 = 1897303) B1897303
theorem B2136563 : Blo 746329 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B1120847 : Blo 746329 1120847 := bstep (se 1 (by rfl) ⟨840635, by rfl⟩ : syracuseStep 1120847 = 1681271) B1681271
theorem B2398855 : Blo 746329 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B1120967 : Blo 746329 1120967 := bstep (se 1 (by rfl) ⟨840725, by rfl⟩ : syracuseStep 1120967 = 1681451) B1681451
theorem B2530007 : Blo 746329 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B2399071 : Blo 746329 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1121129 : Blo 746329 1121129 := bstep (se 2 (by rfl) ⟨420423, by rfl⟩ : syracuseStep 1121129 = 840847) B840847
theorem B2530223 : Blo 746329 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B1121207 : Blo 746329 1121207 := bstep (se 1 (by rfl) ⟨840905, by rfl⟩ : syracuseStep 1121207 = 1681811) B1681811
theorem B1383355 : Blo 746329 1383355 := bstep (se 1 (by rfl) ⟨1037516, by rfl⟩ : syracuseStep 1383355 = 2075033) B2075033
theorem B1121243 : Blo 746329 1121243 := bstep (se 1 (by rfl) ⟨840932, by rfl⟩ : syracuseStep 1121243 = 1681865) B1681865
theorem B2694487 : Blo 746329 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B1121711 : Blo 746329 1121711 := bstep (se 1 (by rfl) ⟨841283, by rfl⟩ : syracuseStep 1121711 = 1682567) B1682567
theorem B1121801 : Blo 746329 1121801 := bstep (se 2 (by rfl) ⟨420675, by rfl⟩ : syracuseStep 1121801 = 841351) B841351
theorem B2399777 : Blo 746329 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B1121831 : Blo 746329 1121831 := bstep (se 1 (by rfl) ⟨841373, by rfl⟩ : syracuseStep 1121831 = 1682747) B1682747
theorem B1121915 : Blo 746329 1121915 := bstep (se 1 (by rfl) ⟨841436, by rfl⟩ : syracuseStep 1121915 = 1682873) B1682873
theorem B1515179 : Blo 746329 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B1122041 : Blo 746329 1122041 := bstep (se 2 (by rfl) ⟨420765, by rfl⟩ : syracuseStep 1122041 = 841531) B841531
theorem B1122143 : Blo 746329 1122143 := bstep (se 1 (by rfl) ⟨841607, by rfl⟩ : syracuseStep 1122143 = 1683215) B1683215
theorem B1122155 : Blo 746329 1122155 := bstep (se 1 (by rfl) ⟨841616, by rfl⟩ : syracuseStep 1122155 = 1683233) B1683233
theorem B1679291 : Blo 746329 1679291 := bstep (se 1 (by rfl) ⟨1259468, by rfl⟩ : syracuseStep 1679291 = 2518937) B2518937
theorem B2400187 : Blo 746329 2400187 := bstep (se 1 (by rfl) ⟨1800140, by rfl⟩ : syracuseStep 2400187 = 3600281) B3600281
theorem B1679417 : Blo 746329 1679417 := bstep (se 2 (by rfl) ⟨629781, by rfl⟩ : syracuseStep 1679417 = 1259563) B1259563
theorem B1122383 : Blo 746329 1122383 := bstep (se 1 (by rfl) ⟨841787, by rfl⟩ : syracuseStep 1122383 = 1683575) B1683575
theorem B1417313 : Blo 746329 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B16425109 : Blo 746329 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B1122503 : Blo 746329 1122503 := bstep (se 1 (by rfl) ⟨841877, by rfl⟩ : syracuseStep 1122503 = 1683755) B1683755
theorem B1122665 : Blo 746329 1122665 := bstep (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) B841999
theorem B1679759 : Blo 746329 1679759 := bstep (se 1 (by rfl) ⟨1259819, by rfl⟩ : syracuseStep 1679759 = 2519639) B2519639
theorem B1417655 : Blo 746329 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B1122743 : Blo 746329 1122743 := bstep (se 1 (by rfl) ⟨842057, by rfl⟩ : syracuseStep 1122743 = 1684115) B1684115
theorem B1122779 : Blo 746329 1122779 := bstep (se 1 (by rfl) ⟨842084, by rfl⟩ : syracuseStep 1122779 = 1684169) B1684169
theorem B1680083 : Blo 746329 1680083 := bstep (se 1 (by rfl) ⟨1260062, by rfl⟩ : syracuseStep 1680083 = 2520125) B2520125
theorem B1418057 : Blo 746329 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B1123247 : Blo 746329 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B1123337 : Blo 746329 1123337 := bstep (se 2 (by rfl) ⟨421251, by rfl⟩ : syracuseStep 1123337 = 842503) B842503
theorem B1123367 : Blo 746329 1123367 := bstep (se 1 (by rfl) ⟨842525, by rfl⟩ : syracuseStep 1123367 = 1685051) B1685051
theorem B1123451 : Blo 746329 1123451 := bstep (se 1 (by rfl) ⟨842588, by rfl⟩ : syracuseStep 1123451 = 1685177) B1685177
theorem B1123577 : Blo 746329 1123577 := bstep (se 2 (by rfl) ⟨421341, by rfl⟩ : syracuseStep 1123577 = 842683) B842683
theorem B1123679 : Blo 746329 1123679 := bstep (se 1 (by rfl) ⟨842759, by rfl⟩ : syracuseStep 1123679 = 1685519) B1685519
theorem B1123691 : Blo 746329 1123691 := bstep (se 1 (by rfl) ⟨842768, by rfl⟩ : syracuseStep 1123691 = 1685537) B1685537
theorem B1418771 : Blo 746329 1418771 := bstep (se 1 (by rfl) ⟨1064078, by rfl⟩ : syracuseStep 1418771 = 2128157) B2128157
theorem B1418809 : Blo 746329 1418809 := bstep (se 2 (by rfl) ⟨532053, by rfl⟩ : syracuseStep 1418809 = 1064107) B1064107
theorem B1123919 : Blo 746329 1123919 := bstep (se 1 (by rfl) ⟨842939, by rfl⟩ : syracuseStep 1123919 = 1685879) B1685879
theorem B1681019 : Blo 746329 1681019 := bstep (se 1 (by rfl) ⟨1260764, by rfl⟩ : syracuseStep 1681019 = 2521529) B2521529
theorem B1124039 : Blo 746329 1124039 := bstep (se 1 (by rfl) ⟨843029, by rfl⟩ : syracuseStep 1124039 = 1686059) B1686059
theorem B1681145 : Blo 746329 1681145 := bstep (se 2 (by rfl) ⟨630429, by rfl⟩ : syracuseStep 1681145 = 1260859) B1260859
theorem B9611045 : Blo 746329 9611045 := bstep (se 4 (by rfl) ⟨901035, by rfl⟩ : syracuseStep 9611045 = 1802071) B1802071
theorem B1419113 : Blo 746329 1419113 := bstep (se 2 (by rfl) ⟨532167, by rfl⟩ : syracuseStep 1419113 = 1064335) B1064335
theorem B1124201 : Blo 746329 1124201 := bstep (se 2 (by rfl) ⟨421575, by rfl⟩ : syracuseStep 1124201 = 843151) B843151
theorem B1124279 : Blo 746329 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B4794299 : Blo 746329 4794299 := bstep (se 1 (by rfl) ⟨3595724, by rfl⟩ : syracuseStep 4794299 = 7191449) B7191449
theorem B1124315 : Blo 746329 1124315 := bstep (se 1 (by rfl) ⟨843236, by rfl⟩ : syracuseStep 1124315 = 1686473) B1686473
theorem B1681415 : Blo 746329 1681415 := bstep (se 1 (by rfl) ⟨1261061, by rfl⟩ : syracuseStep 1681415 = 2522123) B2522123
theorem B4270117 : Blo 746329 4270117 := bstep (se 4 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 4270117 = 800647) B800647
theorem B1681487 : Blo 746329 1681487 := bstep (se 1 (by rfl) ⟨1261115, by rfl⟩ : syracuseStep 1681487 = 2522231) B2522231
theorem B3778649 : Blo 746329 3778649 := bstep (se 2 (by rfl) ⟨1416993, by rfl⟩ : syracuseStep 3778649 = 2833987) B2833987
theorem B6138013 : Blo 746329 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B21604553 : Blo 746329 21604553 := bstep (se 2 (by rfl) ⟨8101707, by rfl⟩ : syracuseStep 21604553 = 16203415) B16203415
theorem B1124783 : Blo 746329 1124783 := bstep (se 1 (by rfl) ⟨843587, by rfl⟩ : syracuseStep 1124783 = 1687175) B1687175
theorem B1681883 : Blo 746329 1681883 := bstep (se 1 (by rfl) ⟨1261412, by rfl⟩ : syracuseStep 1681883 = 2522825) B2522825
theorem B6826477 : Blo 746329 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B1124873 : Blo 746329 1124873 := bstep (se 2 (by rfl) ⟨421827, by rfl⟩ : syracuseStep 1124873 = 843655) B843655
theorem B26978849 : Blo 746329 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1124903 : Blo 746329 1124903 := bstep (se 1 (by rfl) ⟨843677, by rfl⟩ : syracuseStep 1124903 = 1687355) B1687355
theorem B1124987 : Blo 746329 1124987 := bstep (se 1 (by rfl) ⟨843740, by rfl⟩ : syracuseStep 1124987 = 1687481) B1687481
theorem B2271883 : Blo 746329 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B7383737 : Blo 746329 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B23079653 : Blo 746329 23079653 := bstep (se 4 (by rfl) ⟨2163717, by rfl⟩ : syracuseStep 23079653 = 4327435) B4327435
theorem B1125113 : Blo 746329 1125113 := bstep (se 2 (by rfl) ⟨421917, by rfl⟩ : syracuseStep 1125113 = 843835) B843835
theorem B1125215 : Blo 746329 1125215 := bstep (se 1 (by rfl) ⟨843911, by rfl⟩ : syracuseStep 1125215 = 1687823) B1687823
theorem B1125227 : Blo 746329 1125227 := bstep (se 1 (by rfl) ⟨843920, by rfl⟩ : syracuseStep 1125227 = 1687841) B1687841
theorem B1682351 : Blo 746329 1682351 := bstep (se 1 (by rfl) ⟨1261763, by rfl⟩ : syracuseStep 1682351 = 2523527) B2523527
theorem B621849635 : Blo 746329 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B1125455 : Blo 746329 1125455 := bstep (se 1 (by rfl) ⟨844091, by rfl⟩ : syracuseStep 1125455 = 1688183) B1688183
theorem B1420411 : Blo 746329 1420411 := bstep (se 1 (by rfl) ⟨1065308, by rfl⟩ : syracuseStep 1420411 = 2130617) B2130617
theorem B1682603 : Blo 746329 1682603 := bstep (se 1 (by rfl) ⟨1261952, by rfl⟩ : syracuseStep 1682603 = 2523905) B2523905
theorem B1420487 : Blo 746329 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B1420897 : Blo 746329 1420897 := bstep (se 2 (by rfl) ⟨532836, by rfl⟩ : syracuseStep 1420897 = 1065673) B1065673
theorem B1683143 : Blo 746329 1683143 := bstep (se 1 (by rfl) ⟨1262357, by rfl⟩ : syracuseStep 1683143 = 2524715) B2524715
theorem B1421239 : Blo 746329 1421239 := bstep (se 1 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 1421239 = 2131859) B2131859
theorem B4108403 : Blo 746329 4108403 := bstep (se 1 (by rfl) ⟨3081302, by rfl⟩ : syracuseStep 4108403 = 6162605) B6162605
theorem B1421641 : Blo 746329 1421641 := bstep (se 2 (by rfl) ⟨533115, by rfl⟩ : syracuseStep 1421641 = 1066231) B1066231
theorem B4796759 : Blo 746329 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B799195 : Blo 746329 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B1684007 : Blo 746329 1684007 := bstep (se 1 (by rfl) ⟨1263005, by rfl⟩ : syracuseStep 1684007 = 2526011) B2526011
theorem B1520167 : Blo 746329 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B4272851 : Blo 746329 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B1684331 : Blo 746329 1684331 := bstep (se 1 (by rfl) ⟨1263248, by rfl⟩ : syracuseStep 1684331 = 2526497) B2526497
theorem B1684385 : Blo 746329 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B1422355 : Blo 746329 1422355 := bstep (se 1 (by rfl) ⟨1066766, by rfl⟩ : syracuseStep 1422355 = 2133533) B2133533
theorem B6829105 : Blo 746329 6829105 := bstep (se 2 (by rfl) ⟨2560914, by rfl⟩ : syracuseStep 6829105 = 5121829) B5121829
theorem B8107073 : Blo 746329 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B38810765 : Blo 746329 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B2733209 : Blo 746329 2733209 := bstep (se 2 (by rfl) ⟨1024953, by rfl⟩ : syracuseStep 2733209 = 2049907) B2049907
theorem B12301483 : Blo 746329 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B1684727 : Blo 746329 1684727 := bstep (se 1 (by rfl) ⟨1263545, by rfl⟩ : syracuseStep 1684727 = 2527091) B2527091
theorem B1520887 : Blo 746329 1520887 := bstep (se 1 (by rfl) ⟨1140665, by rfl⟩ : syracuseStep 1520887 = 2281331) B2281331
theorem B1422697 : Blo 746329 1422697 := bstep (se 2 (by rfl) ⟨533511, by rfl⟩ : syracuseStep 1422697 = 1067023) B1067023
theorem B1062649 : Blo 746329 1062649 := bstep (se 2 (by rfl) ⟨398493, by rfl⟩ : syracuseStep 1062649 = 796987) B796987
theorem B1685321 : Blo 746329 1685321 := bstep (se 2 (by rfl) ⟨631995, by rfl⟩ : syracuseStep 1685321 = 1263991) B1263991
theorem B10762145 : Blo 746329 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B1259995 : Blo 746329 1259995 := bstep (se 1 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 1259995 = 1889993) B1889993
theorem B1686113 : Blo 746329 1686113 := bstep (se 2 (by rfl) ⟨632292, by rfl⟩ : syracuseStep 1686113 = 1264585) B1264585
theorem B3652231 : Blo 746329 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B1424071 : Blo 746329 1424071 := bstep (se 1 (by rfl) ⟨1068053, by rfl⟩ : syracuseStep 1424071 = 2136107) B2136107
theorem B1751969 : Blo 746329 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1686455 : Blo 746329 1686455 := bstep (se 1 (by rfl) ⟨1264841, by rfl⟩ : syracuseStep 1686455 = 2529683) B2529683
theorem B1260623 : Blo 746329 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B3783833 : Blo 746329 3783833 := bstep (se 2 (by rfl) ⟨1418937, by rfl⟩ : syracuseStep 3783833 = 2837875) B2837875
theorem B4799681 : Blo 746329 4799681 := bstep (se 2 (by rfl) ⟨1799880, by rfl⟩ : syracuseStep 4799681 = 3599761) B3599761
theorem B1064135 : Blo 746329 1064135 := bstep (se 1 (by rfl) ⟨798101, by rfl⟩ : syracuseStep 1064135 = 1596203) B1596203
theorem B21052853 : Blo 746329 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B1687049 : Blo 746329 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B1687391 : Blo 746329 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B2703223 : Blo 746329 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B1261487 : Blo 746329 1261487 := bstep (se 1 (by rfl) ⟨946115, by rfl⟩ : syracuseStep 1261487 = 1892231) B1892231
theorem B1687571 : Blo 746329 1687571 := bstep (se 1 (by rfl) ⟨1265678, by rfl⟩ : syracuseStep 1687571 = 2531357) B2531357
theorem B24231959 : Blo 746329 24231959 := bstep (se 1 (by rfl) ⟨18173969, by rfl⟩ : syracuseStep 24231959 = 36347939) B36347939
theorem B3850321 : Blo 746329 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B23052437 : Blo 746329 23052437 := bstep (se 6 (by rfl) ⟨540291, by rfl⟩ : syracuseStep 23052437 = 1080583) B1080583
theorem B7192907 : Blo 746329 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B1261919 : Blo 746329 1261919 := bstep (se 1 (by rfl) ⟨946439, by rfl⟩ : syracuseStep 1261919 = 1892879) B1892879
theorem B3588457 : Blo 746329 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B1687913 : Blo 746329 1687913 := bstep (se 2 (by rfl) ⟨632967, by rfl⟩ : syracuseStep 1687913 = 1265935) B1265935
theorem B1262479 : Blo 746329 1262479 := bstep (se 1 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 1262479 = 1893719) B1893719
theorem B5686199 : Blo 746329 5686199 := bstep (se 1 (by rfl) ⟨4264649, by rfl⟩ : syracuseStep 5686199 = 8529299) B8529299
theorem B15385841 : Blo 746329 15385841 := bstep (se 2 (by rfl) ⟨5769690, by rfl⟩ : syracuseStep 15385841 = 11539381) B11539381
theorem B1197499 : Blo 746329 1197499 := bstep (se 1 (by rfl) ⟨898124, by rfl⟩ : syracuseStep 1197499 = 1796249) B1796249
theorem B2835931 : Blo 746329 2835931 := bstep (se 1 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 2835931 = 4253897) B4253897
theorem B1066459 : Blo 746329 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B1263161 : Blo 746329 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B3032761 : Blo 746329 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B1067131 : Blo 746329 1067131 := bstep (se 1 (by rfl) ⟨800348, by rfl⟩ : syracuseStep 1067131 = 1600697) B1600697
theorem B1263863 : Blo 746329 1263863 := bstep (se 1 (by rfl) ⟨947897, by rfl⟩ : syracuseStep 1263863 = 1895795) B1895795
theorem B1067359 : Blo 746329 1067359 := bstep (se 1 (by rfl) ⟨800519, by rfl⟩ : syracuseStep 1067359 = 1601039) B1601039
theorem B5687657 : Blo 746329 5687657 := bstep (se 2 (by rfl) ⟨2132871, by rfl⟩ : syracuseStep 5687657 = 4265743) B4265743
theorem B3590689 : Blo 746329 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B1264207 : Blo 746329 1264207 := bstep (se 1 (by rfl) ⟨948155, by rfl⟩ : syracuseStep 1264207 = 1896311) B1896311
theorem B4803245 : Blo 746329 4803245 := bstep (se 3 (by rfl) ⟨900608, by rfl⟩ : syracuseStep 4803245 = 1801217) B1801217
theorem B2837177 : Blo 746329 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B2837207 : Blo 746329 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B1264457 : Blo 746329 1264457 := bstep (se 2 (by rfl) ⟨474171, by rfl⟩ : syracuseStep 1264457 = 948343) B948343
theorem B5393297 : Blo 746329 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B1067951 : Blo 746329 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B1264889 : Blo 746329 1264889 := bstep (se 2 (by rfl) ⟨474333, by rfl⟩ : syracuseStep 1264889 = 948667) B948667
theorem B1265071 : Blo 746329 1265071 := bstep (se 1 (by rfl) ⟨948803, by rfl⟩ : syracuseStep 1265071 = 1897607) B1897607
theorem B1265159 : Blo 746329 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B1265503 : Blo 746329 1265503 := bstep (se 1 (by rfl) ⟨949127, by rfl⟩ : syracuseStep 1265503 = 1898255) B1898255
theorem B3067757 : Blo 746329 3067757 := bstep (se 3 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 3067757 = 1150409) B1150409
theorem B1265591 : Blo 746329 1265591 := bstep (se 1 (by rfl) ⟨949193, by rfl⟩ : syracuseStep 1265591 = 1898387) B1898387
theorem B5394509 : Blo 746329 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B839803 : Blo 746329 839803 := bstep (se 1 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 839803 = 1259705) B1259705
theorem B1134791 : Blo 746329 1134791 := bstep (se 1 (by rfl) ⟨851093, by rfl⟩ : syracuseStep 1134791 = 1702187) B1702187
theorem B5689601 : Blo 746329 5689601 := bstep (se 2 (by rfl) ⟨2133600, by rfl⟩ : syracuseStep 5689601 = 4267201) B4267201
theorem B3199513 : Blo 746329 3199513 := bstep (se 2 (by rfl) ⟨1199817, by rfl⟩ : syracuseStep 3199513 = 2399635) B2399635
theorem B3592763 : Blo 746329 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B840271 : Blo 746329 840271 := bstep (se 1 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 840271 = 1260407) B1260407
theorem B840667 : Blo 746329 840667 := bstep (se 1 (by rfl) ⟨630500, by rfl⟩ : syracuseStep 840667 = 1261001) B1261001
theorem B10245365 : Blo 746329 10245365 := bstep (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) B960503
theorem B1889527 : Blo 746329 1889527 := bstep (se 1 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 1889527 = 2834291) B2834291
theorem B2839819 : Blo 746329 2839819 := bstep (se 1 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 2839819 = 4259729) B4259729
theorem B841135 : Blo 746329 841135 := bstep (se 1 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 841135 = 1261703) B1261703
theorem B1889801 : Blo 746329 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B1889831 : Blo 746329 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B2840123 : Blo 746329 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B3790475 : Blo 746329 3790475 := bstep (se 1 (by rfl) ⟨2842856, by rfl⟩ : syracuseStep 3790475 = 5685713) B5685713
theorem B17258275 : Blo 746329 17258275 := bstep (se 1 (by rfl) ⟨12943706, by rfl⟩ : syracuseStep 17258275 = 25887413) B25887413
theorem B6084395 : Blo 746329 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B841567 : Blo 746329 841567 := bstep (se 1 (by rfl) ⟨631175, by rfl⟩ : syracuseStep 841567 = 1262351) B1262351
theorem B1890155 : Blo 746329 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B4052845 : Blo 746329 4052845 := bstep (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) B1519817
theorem B3037103 : Blo 746329 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B1136719 : Blo 746329 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B4053149 : Blo 746329 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B841927 : Blo 746329 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B1595639 : Blo 746329 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B1890803 : Blo 746329 1890803 := bstep (se 1 (by rfl) ⟨1418102, by rfl⟩ : syracuseStep 1890803 = 2836205) B2836205
theorem B2841277 : Blo 746329 2841277 := bstep (se 3 (by rfl) ⟨532739, by rfl⟩ : syracuseStep 2841277 = 1065479) B1065479
theorem B1891259 : Blo 746329 1891259 := bstep (se 1 (by rfl) ⟨1418444, by rfl⟩ : syracuseStep 1891259 = 2836889) B2836889
theorem B842791 : Blo 746329 842791 := bstep (se 1 (by rfl) ⟨632093, by rfl⟩ : syracuseStep 842791 = 1264187) B1264187
theorem B9723053 : Blo 746329 9723053 := bstep (se 3 (by rfl) ⟨1823072, by rfl⟩ : syracuseStep 9723053 = 3646145) B3646145
theorem B19946933 : Blo 746329 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1891937 : Blo 746329 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B2842235 : Blo 746329 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B4317299 : Blo 746329 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B1597801 : Blo 746329 1597801 := bstep (se 2 (by rfl) ⟨599175, by rfl⟩ : syracuseStep 1597801 = 1198351) B1198351
theorem B2843009 : Blo 746329 2843009 := bstep (se 2 (by rfl) ⟨1066128, by rfl⟩ : syracuseStep 2843009 = 2132257) B2132257
theorem B5693975 : Blo 746329 5693975 := bstep (se 1 (by rfl) ⟨4270481, by rfl⟩ : syracuseStep 5693975 = 8540963) B8540963
theorem B1139279 : Blo 746329 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B2777723 : Blo 746329 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B746335 : Blo 746329 746335 := bstep (se 1 (by rfl) ⟨559751, by rfl⟩ : syracuseStep 746335 = 1119503) B1119503
theorem B3072887 : Blo 746329 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B746363 : Blo 746329 746363 := bstep (se 1 (by rfl) ⟨559772, by rfl⟩ : syracuseStep 746363 = 1119545) B1119545
theorem B746415 : Blo 746329 746415 := bstep (se 1 (by rfl) ⟨559811, by rfl⟩ : syracuseStep 746415 = 1119623) B1119623
theorem B48456629 : Blo 746329 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B746439 : Blo 746329 746439 := bstep (se 1 (by rfl) ⟨559829, by rfl⟩ : syracuseStep 746439 = 1119659) B1119659
theorem B746459 : Blo 746329 746459 := bstep (se 1 (by rfl) ⟨559844, by rfl⟩ : syracuseStep 746459 = 1119689) B1119689
theorem B1893395 : Blo 746329 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B746535 : Blo 746329 746535 := bstep (se 1 (by rfl) ⟨559901, by rfl⟩ : syracuseStep 746535 = 1119803) B1119803
theorem B746575 : Blo 746329 746575 := bstep (se 1 (by rfl) ⟨559931, by rfl⟩ : syracuseStep 746575 = 1119863) B1119863
theorem B746591 : Blo 746329 746591 := bstep (se 1 (by rfl) ⟨559943, by rfl⟩ : syracuseStep 746591 = 1119887) B1119887
theorem B746619 : Blo 746329 746619 := bstep (se 1 (by rfl) ⟨559964, by rfl⟩ : syracuseStep 746619 = 1119929) B1119929
theorem B746671 : Blo 746329 746671 := bstep (se 1 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 746671 = 1120007) B1120007
theorem B746695 : Blo 746329 746695 := bstep (se 1 (by rfl) ⟨560021, by rfl⟩ : syracuseStep 746695 = 1120043) B1120043
theorem B746715 : Blo 746329 746715 := bstep (se 1 (by rfl) ⟨560036, by rfl⟩ : syracuseStep 746715 = 1120073) B1120073
theorem B746791 : Blo 746329 746791 := bstep (se 1 (by rfl) ⟨560093, by rfl⟩ : syracuseStep 746791 = 1120187) B1120187
theorem B746831 : Blo 746329 746831 := bstep (se 1 (by rfl) ⟨560123, by rfl⟩ : syracuseStep 746831 = 1120247) B1120247
theorem B746847 : Blo 746329 746847 := bstep (se 1 (by rfl) ⟨560135, by rfl⟩ : syracuseStep 746847 = 1120271) B1120271
theorem B746875 : Blo 746329 746875 := bstep (se 1 (by rfl) ⟨560156, by rfl⟩ : syracuseStep 746875 = 1120313) B1120313
theorem B746927 : Blo 746329 746927 := bstep (se 1 (by rfl) ⟨560195, by rfl⟩ : syracuseStep 746927 = 1120391) B1120391
theorem B746951 : Blo 746329 746951 := bstep (se 1 (by rfl) ⟨560213, by rfl⟩ : syracuseStep 746951 = 1120427) B1120427
theorem B4253147 : Blo 746329 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B746971 : Blo 746329 746971 := bstep (se 1 (by rfl) ⟨560228, by rfl⟩ : syracuseStep 746971 = 1120457) B1120457
theorem B1893851 : Blo 746329 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B2844193 : Blo 746329 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B747047 : Blo 746329 747047 := bstep (se 1 (by rfl) ⟨560285, by rfl⟩ : syracuseStep 747047 = 1120571) B1120571
theorem B747087 : Blo 746329 747087 := bstep (se 1 (by rfl) ⟨560315, by rfl⟩ : syracuseStep 747087 = 1120631) B1120631
theorem B747103 : Blo 746329 747103 := bstep (se 1 (by rfl) ⟨560327, by rfl⟩ : syracuseStep 747103 = 1120655) B1120655
theorem B747131 : Blo 746329 747131 := bstep (se 1 (by rfl) ⟨560348, by rfl⟩ : syracuseStep 747131 = 1120697) B1120697
theorem B747183 : Blo 746329 747183 := bstep (se 1 (by rfl) ⟨560387, by rfl⟩ : syracuseStep 747183 = 1120775) B1120775
theorem B747207 : Blo 746329 747207 := bstep (se 1 (by rfl) ⟨560405, by rfl⟩ : syracuseStep 747207 = 1120811) B1120811
theorem B747227 : Blo 746329 747227 := bstep (se 1 (by rfl) ⟨560420, by rfl⟩ : syracuseStep 747227 = 1120841) B1120841
theorem B747303 : Blo 746329 747303 := bstep (se 1 (by rfl) ⟨560477, by rfl⟩ : syracuseStep 747303 = 1120955) B1120955
theorem B747343 : Blo 746329 747343 := bstep (se 1 (by rfl) ⟨560507, by rfl⟩ : syracuseStep 747343 = 1121015) B1121015
theorem B747359 : Blo 746329 747359 := bstep (se 1 (by rfl) ⟨560519, by rfl⟩ : syracuseStep 747359 = 1121039) B1121039
theorem B747387 : Blo 746329 747387 := bstep (se 1 (by rfl) ⟨560540, by rfl⟩ : syracuseStep 747387 = 1121081) B1121081
theorem B3794849 : Blo 746329 3794849 := bstep (se 2 (by rfl) ⟨1423068, by rfl⟩ : syracuseStep 3794849 = 2846137) B2846137
theorem B747439 : Blo 746329 747439 := bstep (se 1 (by rfl) ⟨560579, by rfl⟩ : syracuseStep 747439 = 1121159) B1121159
theorem B747463 : Blo 746329 747463 := bstep (se 1 (by rfl) ⟨560597, by rfl⟩ : syracuseStep 747463 = 1121195) B1121195
theorem B747483 : Blo 746329 747483 := bstep (se 1 (by rfl) ⟨560612, by rfl⟩ : syracuseStep 747483 = 1121225) B1121225
theorem B2844679 : Blo 746329 2844679 := bstep (se 1 (by rfl) ⟨2133509, by rfl⟩ : syracuseStep 2844679 = 4267019) B4267019
theorem B747559 : Blo 746329 747559 := bstep (se 1 (by rfl) ⟨560669, by rfl⟩ : syracuseStep 747559 = 1121339) B1121339
theorem B747599 : Blo 746329 747599 := bstep (se 1 (by rfl) ⟨560699, by rfl⟩ : syracuseStep 747599 = 1121399) B1121399
theorem B747615 : Blo 746329 747615 := bstep (se 1 (by rfl) ⟨560711, by rfl⟩ : syracuseStep 747615 = 1121423) B1121423
theorem B747643 : Blo 746329 747643 := bstep (se 1 (by rfl) ⟨560732, by rfl⟩ : syracuseStep 747643 = 1121465) B1121465
theorem B747695 : Blo 746329 747695 := bstep (se 1 (by rfl) ⟨560771, by rfl⟩ : syracuseStep 747695 = 1121543) B1121543
theorem B747719 : Blo 746329 747719 := bstep (se 1 (by rfl) ⟨560789, by rfl⟩ : syracuseStep 747719 = 1121579) B1121579
theorem B747739 : Blo 746329 747739 := bstep (se 1 (by rfl) ⟨560804, by rfl⟩ : syracuseStep 747739 = 1121609) B1121609
theorem B747815 : Blo 746329 747815 := bstep (se 1 (by rfl) ⟨560861, by rfl⟩ : syracuseStep 747815 = 1121723) B1121723
theorem B747855 : Blo 746329 747855 := bstep (se 1 (by rfl) ⟨560891, by rfl⟩ : syracuseStep 747855 = 1121783) B1121783
theorem B747871 : Blo 746329 747871 := bstep (se 1 (by rfl) ⟨560903, by rfl⟩ : syracuseStep 747871 = 1121807) B1121807
theorem B747899 : Blo 746329 747899 := bstep (se 1 (by rfl) ⟨560924, by rfl⟩ : syracuseStep 747899 = 1121849) B1121849
theorem B747951 : Blo 746329 747951 := bstep (se 1 (by rfl) ⟨560963, by rfl⟩ : syracuseStep 747951 = 1121927) B1121927
theorem B747975 : Blo 746329 747975 := bstep (se 1 (by rfl) ⟨560981, by rfl⟩ : syracuseStep 747975 = 1121963) B1121963
theorem B747995 : Blo 746329 747995 := bstep (se 1 (by rfl) ⟨560996, by rfl⟩ : syracuseStep 747995 = 1121993) B1121993
theorem B2025947 : Blo 746329 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B2845165 : Blo 746329 2845165 := bstep (se 3 (by rfl) ⟨533468, by rfl⟩ : syracuseStep 2845165 = 1066937) B1066937
theorem B1796633 : Blo 746329 1796633 := bstep (se 2 (by rfl) ⟨673737, by rfl⟩ : syracuseStep 1796633 = 1347475) B1347475
theorem B748071 : Blo 746329 748071 := bstep (se 1 (by rfl) ⟨561053, by rfl⟩ : syracuseStep 748071 = 1122107) B1122107
theorem B748111 : Blo 746329 748111 := bstep (se 1 (by rfl) ⟨561083, by rfl⟩ : syracuseStep 748111 = 1122167) B1122167
theorem B748127 : Blo 746329 748127 := bstep (se 1 (by rfl) ⟨561095, by rfl⟩ : syracuseStep 748127 = 1122191) B1122191
theorem B748155 : Blo 746329 748155 := bstep (se 1 (by rfl) ⟨561116, by rfl⟩ : syracuseStep 748155 = 1122233) B1122233
theorem B1895035 : Blo 746329 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B748207 : Blo 746329 748207 := bstep (se 1 (by rfl) ⟨561155, by rfl⟩ : syracuseStep 748207 = 1122311) B1122311
theorem B748231 : Blo 746329 748231 := bstep (se 1 (by rfl) ⟨561173, by rfl⟩ : syracuseStep 748231 = 1122347) B1122347
theorem B748251 : Blo 746329 748251 := bstep (se 1 (by rfl) ⟨561188, by rfl⟩ : syracuseStep 748251 = 1122377) B1122377
theorem B2845469 : Blo 746329 2845469 := bstep (se 3 (by rfl) ⟨533525, by rfl⟩ : syracuseStep 2845469 = 1067051) B1067051
theorem B748327 : Blo 746329 748327 := bstep (se 1 (by rfl) ⟨561245, by rfl⟩ : syracuseStep 748327 = 1122491) B1122491
theorem B748367 : Blo 746329 748367 := bstep (se 1 (by rfl) ⟨561275, by rfl⟩ : syracuseStep 748367 = 1122551) B1122551
theorem B748383 : Blo 746329 748383 := bstep (se 1 (by rfl) ⟨561287, by rfl⟩ : syracuseStep 748383 = 1122575) B1122575
theorem B748411 : Blo 746329 748411 := bstep (se 1 (by rfl) ⟨561308, by rfl⟩ : syracuseStep 748411 = 1122617) B1122617
theorem B748463 : Blo 746329 748463 := bstep (se 1 (by rfl) ⟨561347, by rfl⟩ : syracuseStep 748463 = 1122695) B1122695
theorem B748487 : Blo 746329 748487 := bstep (se 1 (by rfl) ⟨561365, by rfl⟩ : syracuseStep 748487 = 1122731) B1122731
theorem B748507 : Blo 746329 748507 := bstep (se 1 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 748507 = 1122761) B1122761
theorem B748583 : Blo 746329 748583 := bstep (se 1 (by rfl) ⟨561437, by rfl⟩ : syracuseStep 748583 = 1122875) B1122875
theorem B748623 : Blo 746329 748623 := bstep (se 1 (by rfl) ⟨561467, by rfl⟩ : syracuseStep 748623 = 1122935) B1122935
theorem B748639 : Blo 746329 748639 := bstep (se 1 (by rfl) ⟨561479, by rfl⟩ : syracuseStep 748639 = 1122959) B1122959
theorem B748667 : Blo 746329 748667 := bstep (se 1 (by rfl) ⟨561500, by rfl⟩ : syracuseStep 748667 = 1123001) B1123001
theorem B748719 : Blo 746329 748719 := bstep (se 1 (by rfl) ⟨561539, by rfl⟩ : syracuseStep 748719 = 1123079) B1123079
theorem B748743 : Blo 746329 748743 := bstep (se 1 (by rfl) ⟨561557, by rfl⟩ : syracuseStep 748743 = 1123115) B1123115
theorem B748763 : Blo 746329 748763 := bstep (se 1 (by rfl) ⟨561572, by rfl⟩ : syracuseStep 748763 = 1123145) B1123145
theorem B748839 : Blo 746329 748839 := bstep (se 1 (by rfl) ⟨561629, by rfl⟩ : syracuseStep 748839 = 1123259) B1123259
theorem B748879 : Blo 746329 748879 := bstep (se 1 (by rfl) ⟨561659, by rfl⟩ : syracuseStep 748879 = 1123319) B1123319
theorem B748895 : Blo 746329 748895 := bstep (se 1 (by rfl) ⟨561671, by rfl⟩ : syracuseStep 748895 = 1123343) B1123343
theorem B748923 : Blo 746329 748923 := bstep (se 1 (by rfl) ⟨561692, by rfl⟩ : syracuseStep 748923 = 1123385) B1123385
theorem B748975 : Blo 746329 748975 := bstep (se 1 (by rfl) ⟨561731, by rfl⟩ : syracuseStep 748975 = 1123463) B1123463
theorem B748999 : Blo 746329 748999 := bstep (se 1 (by rfl) ⟨561749, by rfl⟩ : syracuseStep 748999 = 1123499) B1123499
theorem B749019 : Blo 746329 749019 := bstep (se 1 (by rfl) ⟨561764, by rfl⟩ : syracuseStep 749019 = 1123529) B1123529
theorem B1600987 : Blo 746329 1600987 := bstep (se 1 (by rfl) ⟨1200740, by rfl⟩ : syracuseStep 1600987 = 2401481) B2401481
theorem B749095 : Blo 746329 749095 := bstep (se 1 (by rfl) ⟨561821, by rfl⟩ : syracuseStep 749095 = 1123643) B1123643
theorem B6155837 : Blo 746329 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B749135 : Blo 746329 749135 := bstep (se 1 (by rfl) ⟨561851, by rfl⟩ : syracuseStep 749135 = 1123703) B1123703
theorem B749151 : Blo 746329 749151 := bstep (se 1 (by rfl) ⟨561863, by rfl⟩ : syracuseStep 749151 = 1123727) B1123727
theorem B4255355 : Blo 746329 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B749179 : Blo 746329 749179 := bstep (se 1 (by rfl) ⟨561884, by rfl⟩ : syracuseStep 749179 = 1123769) B1123769
theorem B749231 : Blo 746329 749231 := bstep (se 1 (by rfl) ⟨561923, by rfl⟩ : syracuseStep 749231 = 1123847) B1123847
theorem B749255 : Blo 746329 749255 := bstep (se 1 (by rfl) ⟨561941, by rfl⟩ : syracuseStep 749255 = 1123883) B1123883
theorem B749275 : Blo 746329 749275 := bstep (se 1 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 749275 = 1123913) B1123913
theorem B1797881 : Blo 746329 1797881 := bstep (se 2 (by rfl) ⟨674205, by rfl⟩ : syracuseStep 1797881 = 1348411) B1348411
theorem B749351 : Blo 746329 749351 := bstep (se 1 (by rfl) ⟨562013, by rfl⟩ : syracuseStep 749351 = 1124027) B1124027
theorem B16215875 : Blo 746329 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B749391 : Blo 746329 749391 := bstep (se 1 (by rfl) ⟨562043, by rfl⟩ : syracuseStep 749391 = 1124087) B1124087
theorem B749407 : Blo 746329 749407 := bstep (se 1 (by rfl) ⟨562055, by rfl⟩ : syracuseStep 749407 = 1124111) B1124111
theorem B749435 : Blo 746329 749435 := bstep (se 1 (by rfl) ⟨562076, by rfl⟩ : syracuseStep 749435 = 1124153) B1124153
theorem B749487 : Blo 746329 749487 := bstep (se 1 (by rfl) ⟨562115, by rfl⟩ : syracuseStep 749487 = 1124231) B1124231
theorem B749511 : Blo 746329 749511 := bstep (se 1 (by rfl) ⟨562133, by rfl⟩ : syracuseStep 749511 = 1124267) B1124267
theorem B749531 : Blo 746329 749531 := bstep (se 1 (by rfl) ⟨562148, by rfl⟩ : syracuseStep 749531 = 1124297) B1124297
theorem B749607 : Blo 746329 749607 := bstep (se 1 (by rfl) ⟨562205, by rfl⟩ : syracuseStep 749607 = 1124411) B1124411
theorem B749647 : Blo 746329 749647 := bstep (se 1 (by rfl) ⟨562235, by rfl⟩ : syracuseStep 749647 = 1124471) B1124471
theorem B749663 : Blo 746329 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B749691 : Blo 746329 749691 := bstep (se 1 (by rfl) ⟨562268, by rfl⟩ : syracuseStep 749691 = 1124537) B1124537
theorem B749743 : Blo 746329 749743 := bstep (se 1 (by rfl) ⟨562307, by rfl⟩ : syracuseStep 749743 = 1124615) B1124615
theorem B749767 : Blo 746329 749767 := bstep (se 1 (by rfl) ⟨562325, by rfl⟩ : syracuseStep 749767 = 1124651) B1124651
theorem B749787 : Blo 746329 749787 := bstep (se 1 (by rfl) ⟨562340, by rfl⟩ : syracuseStep 749787 = 1124681) B1124681
theorem B10809611 : Blo 746329 10809611 := bstep (se 1 (by rfl) ⟨8107208, by rfl⟩ : syracuseStep 10809611 = 16214417) B16214417
theorem B749863 : Blo 746329 749863 := bstep (se 1 (by rfl) ⟨562397, by rfl⟩ : syracuseStep 749863 = 1124795) B1124795
theorem B749903 : Blo 746329 749903 := bstep (se 1 (by rfl) ⟨562427, by rfl⟩ : syracuseStep 749903 = 1124855) B1124855
theorem B749919 : Blo 746329 749919 := bstep (se 1 (by rfl) ⟨562439, by rfl⟩ : syracuseStep 749919 = 1124879) B1124879
theorem B749947 : Blo 746329 749947 := bstep (se 1 (by rfl) ⟨562460, by rfl⟩ : syracuseStep 749947 = 1124921) B1124921
theorem B2126209 : Blo 746329 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B749999 : Blo 746329 749999 := bstep (se 1 (by rfl) ⟨562499, by rfl⟩ : syracuseStep 749999 = 1124999) B1124999
theorem B750023 : Blo 746329 750023 := bstep (se 1 (by rfl) ⟨562517, by rfl⟩ : syracuseStep 750023 = 1125035) B1125035
theorem B750043 : Blo 746329 750043 := bstep (se 1 (by rfl) ⟨562532, by rfl⟩ : syracuseStep 750043 = 1125065) B1125065
theorem B26604035 : Blo 746329 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B2519585 : Blo 746329 2519585 := bstep (se 2 (by rfl) ⟨944844, by rfl⟩ : syracuseStep 2519585 = 1889689) B1889689
theorem B750119 : Blo 746329 750119 := bstep (se 1 (by rfl) ⟨562589, by rfl⟩ : syracuseStep 750119 = 1125179) B1125179
theorem B750159 : Blo 746329 750159 := bstep (se 1 (by rfl) ⟨562619, by rfl⟩ : syracuseStep 750159 = 1125239) B1125239
theorem B750175 : Blo 746329 750175 := bstep (se 1 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 750175 = 1125263) B1125263
theorem B750203 : Blo 746329 750203 := bstep (se 1 (by rfl) ⟨562652, by rfl⟩ : syracuseStep 750203 = 1125305) B1125305
theorem B750255 : Blo 746329 750255 := bstep (se 1 (by rfl) ⟨562691, by rfl⟩ : syracuseStep 750255 = 1125383) B1125383
theorem B750279 : Blo 746329 750279 := bstep (se 1 (by rfl) ⟨562709, by rfl⟩ : syracuseStep 750279 = 1125419) B1125419
theorem B750299 : Blo 746329 750299 := bstep (se 1 (by rfl) ⟨562724, by rfl⟩ : syracuseStep 750299 = 1125449) B1125449
theorem B2519801 : Blo 746329 2519801 := bstep (se 2 (by rfl) ⟨944925, by rfl⟩ : syracuseStep 2519801 = 1889851) B1889851
theorem B2126699 : Blo 746329 2126699 := bstep (se 1 (by rfl) ⟨1595024, by rfl⟩ : syracuseStep 2126699 = 3190049) B3190049
theorem B2847595 : Blo 746329 2847595 := bstep (se 1 (by rfl) ⟨2135696, by rfl⟩ : syracuseStep 2847595 = 4271393) B4271393
theorem B1438607 : Blo 746329 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B2520071 : Blo 746329 2520071 := bstep (se 1 (by rfl) ⟨1890053, by rfl⟩ : syracuseStep 2520071 = 3780107) B3780107
theorem B2520179 : Blo 746329 2520179 := bstep (se 1 (by rfl) ⟨1890134, by rfl⟩ : syracuseStep 2520179 = 3780269) B3780269
theorem B38925461 : Blo 746329 38925461 := bstep (se 6 (by rfl) ⟨912315, by rfl⟩ : syracuseStep 38925461 = 1824631) B1824631
theorem B2520449 : Blo 746329 2520449 := bstep (se 2 (by rfl) ⟨945168, by rfl⟩ : syracuseStep 2520449 = 1890337) B1890337
theorem B947639 : Blo 746329 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B947791 : Blo 746329 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B10385189 : Blo 746329 10385189 := bstep (se 4 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 10385189 = 1947223) B1947223
theorem B8517635 : Blo 746329 8517635 := bstep (se 1 (by rfl) ⟨6388226, by rfl⟩ : syracuseStep 8517635 = 12776453) B12776453
theorem B18249785 : Blo 746329 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B2521259 : Blo 746329 2521259 := bstep (se 1 (by rfl) ⟨1890944, by rfl⟩ : syracuseStep 2521259 = 3781889) B3781889
theorem B9108001 : Blo 746329 9108001 := bstep (se 2 (by rfl) ⟨3415500, by rfl⟩ : syracuseStep 9108001 = 6831001) B6831001
theorem B2521799 : Blo 746329 2521799 := bstep (se 1 (by rfl) ⟨1891349, by rfl⟩ : syracuseStep 2521799 = 3782699) B3782699
theorem B948935 : Blo 746329 948935 := bstep (se 1 (by rfl) ⟨711701, by rfl⟩ : syracuseStep 948935 = 1423403) B1423403
theorem B949087 : Blo 746329 949087 := bstep (se 1 (by rfl) ⟨711815, by rfl⟩ : syracuseStep 949087 = 1423631) B1423631
theorem B5667731 : Blo 746329 5667731 := bstep (se 1 (by rfl) ⟨4250798, by rfl⟩ : syracuseStep 5667731 = 8501597) B8501597
theorem B2554895 : Blo 746329 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B6814799 : Blo 746329 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B2391383 : Blo 746329 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B6389117 : Blo 746329 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B2522663 : Blo 746329 2522663 := bstep (se 1 (by rfl) ⟨1891997, by rfl⟩ : syracuseStep 2522663 = 3783995) B3783995
theorem B2522771 : Blo 746329 2522771 := bstep (se 1 (by rfl) ⟨1892078, by rfl⟩ : syracuseStep 2522771 = 3784157) B3784157
theorem B1212103 : Blo 746329 1212103 := bstep (se 1 (by rfl) ⟨909077, by rfl⟩ : syracuseStep 1212103 = 1818155) B1818155
theorem B5668703 : Blo 746329 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B2522987 : Blo 746329 2522987 := bstep (se 1 (by rfl) ⟨1892240, by rfl⟩ : syracuseStep 2522987 = 3784481) B3784481
theorem B2523041 : Blo 746329 2523041 := bstep (se 2 (by rfl) ⟨946140, by rfl⟩ : syracuseStep 2523041 = 1892281) B1892281
theorem B16154639 : Blo 746329 16154639 := bstep (se 1 (by rfl) ⟨12115979, by rfl⟩ : syracuseStep 16154639 = 24231959) B24231959
theorem B15368291 : Blo 746329 15368291 := bstep (se 1 (by rfl) ⟨11526218, by rfl⟩ : syracuseStep 15368291 = 23052437) B23052437
theorem B6062501 : Blo 746329 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B4784609 : Blo 746329 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B2130401 : Blo 746329 2130401 := bstep (se 2 (by rfl) ⟨798900, by rfl⟩ : syracuseStep 2130401 = 1597801) B1597801
theorem B10257227 : Blo 746329 10257227 := bstep (se 1 (by rfl) ⟨7692920, by rfl⟩ : syracuseStep 10257227 = 15385841) B15385841
theorem B1705415 : Blo 746329 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B1443625 : Blo 746329 1443625 := bstep (se 2 (by rfl) ⟨541359, by rfl⟩ : syracuseStep 1443625 = 1082719) B1082719
theorem B756527 : Blo 746329 756527 := bstep (se 1 (by rfl) ⟨567395, by rfl⟩ : syracuseStep 756527 = 1134791) B1134791
theorem B4262827 : Blo 746329 4262827 := bstep (se 1 (by rfl) ⟨3197120, by rfl⟩ : syracuseStep 4262827 = 6394241) B6394241
theorem B2395175 : Blo 746329 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B2886943 : Blo 746329 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B855335 : Blo 746329 855335 := bstep (se 1 (by rfl) ⟨641501, by rfl⟩ : syracuseStep 855335 = 1283003) B1283003
theorem B4787585 : Blo 746329 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B2526713 : Blo 746329 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B2526983 : Blo 746329 2526983 := bstep (se 1 (by rfl) ⟨1895237, by rfl⟩ : syracuseStep 2526983 = 3790475) B3790475
theorem B2527037 : Blo 746329 2527037 := bstep (se 3 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 2527037 = 947639) B947639
theorem B2134649 : Blo 746329 2134649 := bstep (se 2 (by rfl) ⟨800493, by rfl⟩ : syracuseStep 2134649 = 1600987) B1600987
theorem B6821009 : Blo 746329 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B1119527 : Blo 746329 1119527 := bstep (se 1 (by rfl) ⟨839645, by rfl⟩ : syracuseStep 1119527 = 1679291) B1679291
theorem B1119611 : Blo 746329 1119611 := bstep (se 1 (by rfl) ⟨839708, by rfl⟩ : syracuseStep 1119611 = 1679417) B1679417
theorem B18748865 : Blo 746329 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B1119737 : Blo 746329 1119737 := bstep (se 2 (by rfl) ⟨419901, by rfl⟩ : syracuseStep 1119737 = 839803) B839803
theorem B1119839 : Blo 746329 1119839 := bstep (se 1 (by rfl) ⟨839879, by rfl⟩ : syracuseStep 1119839 = 1679759) B1679759
theorem B1120055 : Blo 746329 1120055 := bstep (se 1 (by rfl) ⟨840041, by rfl⟩ : syracuseStep 1120055 = 1680083) B1680083
theorem B25958353 : Blo 746329 25958353 := bstep (se 2 (by rfl) ⟨9734382, by rfl⟩ : syracuseStep 25958353 = 19468765) B19468765
theorem B4266017 : Blo 746329 4266017 := bstep (se 2 (by rfl) ⟨1599756, by rfl⟩ : syracuseStep 4266017 = 3199513) B3199513
theorem B1120361 : Blo 746329 1120361 := bstep (se 2 (by rfl) ⟨420135, by rfl⟩ : syracuseStep 1120361 = 840271) B840271
theorem B1120679 : Blo 746329 1120679 := bstep (se 1 (by rfl) ⟨840509, by rfl⟩ : syracuseStep 1120679 = 1681019) B1681019
theorem B1120763 : Blo 746329 1120763 := bstep (se 1 (by rfl) ⟨840572, by rfl⟩ : syracuseStep 1120763 = 1681145) B1681145
theorem B2529899 : Blo 746329 2529899 := bstep (se 1 (by rfl) ⟨1897424, by rfl⟩ : syracuseStep 2529899 = 3794849) B3794849
theorem B1120889 : Blo 746329 1120889 := bstep (se 2 (by rfl) ⟨420333, by rfl⟩ : syracuseStep 1120889 = 840667) B840667
theorem B1120943 : Blo 746329 1120943 := bstep (se 1 (by rfl) ⟨840707, by rfl⟩ : syracuseStep 1120943 = 1681415) B1681415
theorem B1120991 : Blo 746329 1120991 := bstep (se 1 (by rfl) ⟨840743, by rfl⟩ : syracuseStep 1120991 = 1681487) B1681487
theorem B1121255 : Blo 746329 1121255 := bstep (se 1 (by rfl) ⟨840941, by rfl⟩ : syracuseStep 1121255 = 1681883) B1681883
theorem B1350631 : Blo 746329 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B4922491 : Blo 746329 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B2530493 : Blo 746329 2530493 := bstep (se 3 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 2530493 = 948935) B948935
theorem B1121513 : Blo 746329 1121513 := bstep (se 2 (by rfl) ⟨420567, by rfl⟩ : syracuseStep 1121513 = 841135) B841135
theorem B1121567 : Blo 746329 1121567 := bstep (se 1 (by rfl) ⟨841175, by rfl⟩ : syracuseStep 1121567 = 1682351) B1682351
theorem B1121735 : Blo 746329 1121735 := bstep (se 1 (by rfl) ⟨841301, by rfl⟩ : syracuseStep 1121735 = 1682603) B1682603
theorem B1416865 : Blo 746329 1416865 := bstep (se 2 (by rfl) ⟨531324, by rfl⟩ : syracuseStep 1416865 = 1062649) B1062649
theorem B4103891 : Blo 746329 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B1122089 : Blo 746329 1122089 := bstep (se 2 (by rfl) ⟨420783, by rfl⟩ : syracuseStep 1122089 = 841567) B841567
theorem B1122095 : Blo 746329 1122095 := bstep (se 1 (by rfl) ⟨841571, by rfl⟩ : syracuseStep 1122095 = 1683143) B1683143
theorem B1122569 : Blo 746329 1122569 := bstep (se 2 (by rfl) ⟨420963, by rfl⟩ : syracuseStep 1122569 = 841927) B841927
theorem B17736023 : Blo 746329 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B1679723 : Blo 746329 1679723 := bstep (se 1 (by rfl) ⟨1259792, by rfl⟩ : syracuseStep 1679723 = 2519585) B2519585
theorem B1122671 : Blo 746329 1122671 := bstep (se 1 (by rfl) ⟨842003, by rfl⟩ : syracuseStep 1122671 = 1684007) B1684007
theorem B1679867 : Blo 746329 1679867 := bstep (se 1 (by rfl) ⟨1259900, by rfl⟩ : syracuseStep 1679867 = 2519801) B2519801
theorem B1417799 : Blo 746329 1417799 := bstep (se 1 (by rfl) ⟨1063349, by rfl⟩ : syracuseStep 1417799 = 2126699) B2126699
theorem B1122887 : Blo 746329 1122887 := bstep (se 1 (by rfl) ⟨842165, by rfl⟩ : syracuseStep 1122887 = 1684331) B1684331
theorem B959071 : Blo 746329 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B1122923 : Blo 746329 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B1679993 : Blo 746329 1679993 := bstep (se 2 (by rfl) ⟨629997, by rfl⟩ : syracuseStep 1679993 = 1259995) B1259995
theorem B1680047 : Blo 746329 1680047 := bstep (se 1 (by rfl) ⟨1260035, by rfl⟩ : syracuseStep 1680047 = 2520071) B2520071
theorem B1680119 : Blo 746329 1680119 := bstep (se 1 (by rfl) ⟨1260089, by rfl⟩ : syracuseStep 1680119 = 2520179) B2520179
theorem B1123151 : Blo 746329 1123151 := bstep (se 1 (by rfl) ⟨842363, by rfl⟩ : syracuseStep 1123151 = 1684727) B1684727
theorem B1680299 : Blo 746329 1680299 := bstep (se 1 (by rfl) ⟨1260224, by rfl⟩ : syracuseStep 1680299 = 2520449) B2520449
theorem B6464549 : Blo 746329 6464549 := bstep (se 4 (by rfl) ⟨606051, by rfl⟩ : syracuseStep 6464549 = 1212103) B1212103
theorem B6923459 : Blo 746329 6923459 := bstep (se 1 (by rfl) ⟨5192594, by rfl⟩ : syracuseStep 6923459 = 10385189) B10385189
theorem B1123547 : Blo 746329 1123547 := bstep (se 1 (by rfl) ⟨842660, by rfl⟩ : syracuseStep 1123547 = 1685321) B1685321
theorem B1844473 : Blo 746329 1844473 := bstep (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) B1383355
theorem B5678423 : Blo 746329 5678423 := bstep (se 1 (by rfl) ⟨4258817, by rfl⟩ : syracuseStep 5678423 = 8517635) B8517635
theorem B12166523 : Blo 746329 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B1123721 : Blo 746329 1123721 := bstep (se 2 (by rfl) ⟨421395, by rfl⟩ : syracuseStep 1123721 = 842791) B842791
theorem B1680839 : Blo 746329 1680839 := bstep (se 1 (by rfl) ⟨1260629, by rfl⟩ : syracuseStep 1680839 = 2521259) B2521259
theorem B1124075 : Blo 746329 1124075 := bstep (se 1 (by rfl) ⟨843056, by rfl⟩ : syracuseStep 1124075 = 1686113) B1686113
theorem B1681199 : Blo 746329 1681199 := bstep (se 1 (by rfl) ⟨1260899, by rfl⟩ : syracuseStep 1681199 = 2521799) B2521799
theorem B3778487 : Blo 746329 3778487 := bstep (se 1 (by rfl) ⟨2833865, by rfl⟩ : syracuseStep 3778487 = 5667731) B5667731
theorem B1124303 : Blo 746329 1124303 := bstep (se 1 (by rfl) ⟨843227, by rfl⟩ : syracuseStep 1124303 = 1686455) B1686455
theorem B4794349 : Blo 746329 4794349 := bstep (se 3 (by rfl) ⟨898940, by rfl⟩ : syracuseStep 4794349 = 1797881) B1797881
theorem B14035235 : Blo 746329 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B1124699 : Blo 746329 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B1681775 : Blo 746329 1681775 := bstep (se 1 (by rfl) ⟨1261331, by rfl⟩ : syracuseStep 1681775 = 2522663) B2522663
theorem B1681847 : Blo 746329 1681847 := bstep (se 1 (by rfl) ⟨1261385, by rfl⟩ : syracuseStep 1681847 = 2522771) B2522771
theorem B3779135 : Blo 746329 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B1124927 : Blo 746329 1124927 := bstep (se 1 (by rfl) ⟨843695, by rfl⟩ : syracuseStep 1124927 = 1687391) B1687391
theorem B1681991 : Blo 746329 1681991 := bstep (se 1 (by rfl) ⟨1261493, by rfl⟩ : syracuseStep 1681991 = 2522987) B2522987
theorem B1682027 : Blo 746329 1682027 := bstep (se 1 (by rfl) ⟨1261520, by rfl⟩ : syracuseStep 1682027 = 2523041) B2523041
theorem B1125047 : Blo 746329 1125047 := bstep (se 1 (by rfl) ⟨843785, by rfl⟩ : syracuseStep 1125047 = 1687571) B1687571
theorem B21900145 : Blo 746329 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B4795271 : Blo 746329 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1125275 : Blo 746329 1125275 := bstep (se 1 (by rfl) ⟨843956, by rfl⟩ : syracuseStep 1125275 = 1687913) B1687913
theorem B1682423 : Blo 746329 1682423 := bstep (se 1 (by rfl) ⟨1261817, by rfl⟩ : syracuseStep 1682423 = 2523635) B2523635
theorem B1682783 : Blo 746329 1682783 := bstep (se 1 (by rfl) ⟨1262087, by rfl⟩ : syracuseStep 1682783 = 2524175) B2524175
theorem B1683179 : Blo 746329 1683179 := bstep (se 1 (by rfl) ⟨1262384, by rfl⟩ : syracuseStep 1683179 = 2524769) B2524769
theorem B1683305 : Blo 746329 1683305 := bstep (se 2 (by rfl) ⟨631239, by rfl⟩ : syracuseStep 1683305 = 1262479) B1262479
theorem B896999 : Blo 746329 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B897403 : Blo 746329 897403 := bstep (se 1 (by rfl) ⟨673052, by rfl⟩ : syracuseStep 897403 = 1346105) B1346105
theorem B7188911 : Blo 746329 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B3781241 : Blo 746329 3781241 := bstep (se 2 (by rfl) ⟨1417965, by rfl⟩ : syracuseStep 3781241 = 2835931) B2835931
theorem B1421945 : Blo 746329 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1684151 : Blo 746329 1684151 := bstep (se 1 (by rfl) ⟨1263113, by rfl⟩ : syracuseStep 1684151 = 2526227) B2526227
theorem B1684367 : Blo 746329 1684367 := bstep (se 1 (by rfl) ⟨1263275, by rfl⟩ : syracuseStep 1684367 = 2526551) B2526551
theorem B4043681 : Blo 746329 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B2045171 : Blo 746329 2045171 := bstep (se 1 (by rfl) ⟨1533878, by rfl⟩ : syracuseStep 2045171 = 3067757) B3067757
theorem B1422841 : Blo 746329 1422841 := bstep (se 2 (by rfl) ⟨533565, by rfl⟩ : syracuseStep 1422841 = 1067131) B1067131
theorem B1685087 : Blo 746329 1685087 := bstep (se 1 (by rfl) ⟨1263815, by rfl⟩ : syracuseStep 1685087 = 2527631) B2527631
theorem B1423145 : Blo 746329 1423145 := bstep (se 2 (by rfl) ⟨533679, by rfl⟩ : syracuseStep 1423145 = 1067359) B1067359
theorem B1685303 : Blo 746329 1685303 := bstep (se 1 (by rfl) ⟨1263977, by rfl⟩ : syracuseStep 1685303 = 2527955) B2527955
theorem B899047 : Blo 746329 899047 := bstep (se 1 (by rfl) ⟨674285, by rfl⟩ : syracuseStep 899047 = 1348571) B1348571
theorem B1685609 : Blo 746329 1685609 := bstep (se 2 (by rfl) ⟨632103, by rfl⟩ : syracuseStep 1685609 = 1264207) B1264207
theorem B6830243 : Blo 746329 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B3029177 : Blo 746329 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B1259867 : Blo 746329 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1259887 : Blo 746329 1259887 := bstep (se 1 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 1259887 = 1889831) B1889831
theorem B3783023 : Blo 746329 3783023 := bstep (se 1 (by rfl) ⟨2837267, by rfl⟩ : syracuseStep 3783023 = 5674535) B5674535
theorem B1260103 : Blo 746329 1260103 := bstep (se 1 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 1260103 = 1890155) B1890155
theorem B1686095 : Blo 746329 1686095 := bstep (se 1 (by rfl) ⟨1264571, by rfl⟩ : syracuseStep 1686095 = 2529143) B2529143
theorem B899767 : Blo 746329 899767 := bstep (se 1 (by rfl) ⟨674825, by rfl⟩ : syracuseStep 899767 = 1349651) B1349651
theorem B1686239 : Blo 746329 1686239 := bstep (se 1 (by rfl) ⟨1264679, by rfl⟩ : syracuseStep 1686239 = 2529359) B2529359
theorem B2702099 : Blo 746329 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B1424299 : Blo 746329 1424299 := bstep (se 1 (by rfl) ⟨1068224, by rfl⟩ : syracuseStep 1424299 = 2136449) B2136449
theorem B1686491 : Blo 746329 1686491 := bstep (se 1 (by rfl) ⟨1264868, by rfl⟩ : syracuseStep 1686491 = 2529737) B2529737
theorem B1260535 : Blo 746329 1260535 := bstep (se 1 (by rfl) ⟨945401, by rfl⟩ : syracuseStep 1260535 = 1890803) B1890803
theorem B1424375 : Blo 746329 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B1686671 : Blo 746329 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B1686761 : Blo 746329 1686761 := bstep (se 2 (by rfl) ⟨632535, by rfl⟩ : syracuseStep 1686761 = 1265071) B1265071
theorem B1686815 : Blo 746329 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B1260839 : Blo 746329 1260839 := bstep (se 1 (by rfl) ⟨945629, by rfl⟩ : syracuseStep 1260839 = 1891259) B1891259
theorem B1261291 : Blo 746329 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B1687337 : Blo 746329 1687337 := bstep (se 2 (by rfl) ⟨632751, by rfl⟩ : syracuseStep 1687337 = 1265503) B1265503
theorem B1851815 : Blo 746329 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B2834945 : Blo 746329 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B2048591 : Blo 746329 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B1065593 : Blo 746329 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B1262263 : Blo 746329 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B2835431 : Blo 746329 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1262567 : Blo 746329 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B6407363 : Blo 746329 6407363 := bstep (se 1 (by rfl) ⟨4805522, by rfl⟩ : syracuseStep 6407363 = 9611045) B9611045
theorem B3196199 : Blo 746329 3196199 := bstep (se 1 (by rfl) ⟨2397149, by rfl⟩ : syracuseStep 3196199 = 4794299) B4794299
theorem B14403035 : Blo 746329 14403035 := bstep (se 1 (by rfl) ⟨10802276, by rfl⟩ : syracuseStep 14403035 = 21604553) B21604553
theorem B16401977 : Blo 746329 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B3786425 : Blo 746329 3786425 := bstep (se 2 (by rfl) ⟨1419909, by rfl⟩ : syracuseStep 3786425 = 2839819) B2839819
theorem B1197755 : Blo 746329 1197755 := bstep (se 1 (by rfl) ⟨898316, by rfl⟩ : syracuseStep 1197755 = 1796633) B1796633
theorem B15386435 : Blo 746329 15386435 := bstep (se 1 (by rfl) ⟨11539826, by rfl⟩ : syracuseStep 15386435 = 23079653) B23079653
theorem B414566423 : Blo 746329 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B1263721 : Blo 746329 1263721 := bstep (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) B947791
theorem B2836903 : Blo 746329 2836903 := bstep (se 1 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 2836903 = 4255355) B4255355
theorem B4671917 : Blo 746329 4671917 := bstep (se 3 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 4671917 = 1751969) B1751969
theorem B2738935 : Blo 746329 2738935 := bstep (se 1 (by rfl) ⟨2054201, by rfl⟩ : syracuseStep 2738935 = 4108403) B4108403
theorem B3197839 : Blo 746329 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B2837693 : Blo 746329 2837693 := bstep (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) B1064135
theorem B12144001 : Blo 746329 12144001 := bstep (se 2 (by rfl) ⟨4554000, by rfl⟩ : syracuseStep 12144001 = 9108001) B9108001
theorem B25873843 : Blo 746329 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B1822139 : Blo 746329 1822139 := bstep (se 1 (by rfl) ⟨1366604, by rfl⟩ : syracuseStep 1822139 = 2733209) B2733209
theorem B3198473 : Blo 746329 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B4869641 : Blo 746329 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B3788369 : Blo 746329 3788369 := bstep (se 2 (by rfl) ⟨1420638, by rfl⟩ : syracuseStep 3788369 = 2841277) B2841277
theorem B3198761 : Blo 746329 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B1265449 : Blo 746329 1265449 := bstep (se 2 (by rfl) ⟨474543, by rfl⟩ : syracuseStep 1265449 = 949087) B949087
theorem B3592649 : Blo 746329 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B4543199 : Blo 746329 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B840415 : Blo 746329 840415 := bstep (se 1 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 840415 = 1260623) B1260623
theorem B3199787 : Blo 746329 3199787 := bstep (se 1 (by rfl) ⟨2399840, by rfl⟩ : syracuseStep 3199787 = 4799681) B4799681
theorem B1594255 : Blo 746329 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B3200249 : Blo 746329 3200249 := bstep (se 2 (by rfl) ⟨1200093, by rfl⟩ : syracuseStep 3200249 = 2400187) B2400187
theorem B840991 : Blo 746329 840991 := bstep (se 1 (by rfl) ⟨630743, by rfl⟩ : syracuseStep 840991 = 1261487) B1261487
theorem B25974179 : Blo 746329 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B5133761 : Blo 746329 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B841279 : Blo 746329 841279 := bstep (se 1 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 841279 = 1261919) B1261919
theorem B1595143 : Blo 746329 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B3790799 : Blo 746329 3790799 := bstep (se 1 (by rfl) ⟨2843099, by rfl⟩ : syracuseStep 3790799 = 5686199) B5686199
theorem B2840609 : Blo 746329 2840609 := bstep (se 2 (by rfl) ⟨1065228, by rfl⟩ : syracuseStep 2840609 = 2130457) B2130457
theorem B4806935 : Blo 746329 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B842107 : Blo 746329 842107 := bstep (se 1 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 842107 = 1263161) B1263161
theorem B4807163 : Blo 746329 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B2841263 : Blo 746329 2841263 := bstep (se 1 (by rfl) ⟨2130947, by rfl⟩ : syracuseStep 2841263 = 4261895) B4261895
theorem B6576815 : Blo 746329 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B842575 : Blo 746329 842575 := bstep (se 1 (by rfl) ⟨631931, by rfl⟩ : syracuseStep 842575 = 1263863) B1263863
theorem B1203023 : Blo 746329 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B3038077 : Blo 746329 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B3791771 : Blo 746329 3791771 := bstep (se 1 (by rfl) ⟨2843828, by rfl⟩ : syracuseStep 3791771 = 5687657) B5687657
theorem B3202163 : Blo 746329 3202163 := bstep (se 1 (by rfl) ⟨2401622, by rfl⟩ : syracuseStep 3202163 = 4803245) B4803245
theorem B1891451 : Blo 746329 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B1891471 : Blo 746329 1891471 := bstep (se 1 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 1891471 = 2837207) B2837207
theorem B842971 : Blo 746329 842971 := bstep (se 1 (by rfl) ⟨632228, by rfl⟩ : syracuseStep 842971 = 1264457) B1264457
theorem B1596665 : Blo 746329 1596665 := bstep (se 2 (by rfl) ⟨598749, by rfl⟩ : syracuseStep 1596665 = 1197499) B1197499
theorem B3595531 : Blo 746329 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B3792257 : Blo 746329 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B1891745 : Blo 746329 1891745 := bstep (se 2 (by rfl) ⟨709404, by rfl⟩ : syracuseStep 1891745 = 1418809) B1418809
theorem B843259 : Blo 746329 843259 := bstep (se 1 (by rfl) ⟨632444, by rfl⟩ : syracuseStep 843259 = 1264889) B1264889
theorem B843439 : Blo 746329 843439 := bstep (se 1 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 843439 = 1265159) B1265159
theorem B1793921 : Blo 746329 1793921 := bstep (se 2 (by rfl) ⟨672720, by rfl⟩ : syracuseStep 1793921 = 1345441) B1345441
theorem B1597391 : Blo 746329 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B843727 : Blo 746329 843727 := bstep (se 1 (by rfl) ⟨632795, by rfl⟩ : syracuseStep 843727 = 1265591) B1265591
theorem B3792905 : Blo 746329 3792905 := bstep (se 2 (by rfl) ⟨1422339, by rfl⟩ : syracuseStep 3792905 = 2844679) B2844679
theorem B5693489 : Blo 746329 5693489 := bstep (se 2 (by rfl) ⟨2135058, by rfl⟩ : syracuseStep 5693489 = 4270117) B4270117
theorem B3596339 : Blo 746329 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B3793067 : Blo 746329 3793067 := bstep (se 1 (by rfl) ⟨2844800, by rfl⟩ : syracuseStep 3793067 = 5689601) B5689601
theorem B8184017 : Blo 746329 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1794479 : Blo 746329 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B2843207 : Blo 746329 2843207 := bstep (se 1 (by rfl) ⟨2132405, by rfl⟩ : syracuseStep 2843207 = 4264811) B4264811
theorem B9101969 : Blo 746329 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B3793553 : Blo 746329 3793553 := bstep (se 2 (by rfl) ⟨1422582, by rfl⟩ : syracuseStep 3793553 = 2845165) B2845165
theorem B1598287 : Blo 746329 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B746395 : Blo 746329 746395 := bstep (se 1 (by rfl) ⟨559796, by rfl⟩ : syracuseStep 746395 = 1119593) B1119593
theorem B746447 : Blo 746329 746447 := bstep (se 1 (by rfl) ⟨559835, by rfl⟩ : syracuseStep 746447 = 1119671) B1119671
theorem B746471 : Blo 746329 746471 := bstep (se 1 (by rfl) ⟨559853, by rfl⟩ : syracuseStep 746471 = 1119707) B1119707
theorem B1893415 : Blo 746329 1893415 := bstep (se 1 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 1893415 = 2840123) B2840123
theorem B1598663 : Blo 746329 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B4056263 : Blo 746329 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B746783 : Blo 746329 746783 := bstep (se 1 (by rfl) ⟨560087, by rfl⟩ : syracuseStep 746783 = 1120175) B1120175
theorem B2024735 : Blo 746329 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B746843 : Blo 746329 746843 := bstep (se 1 (by rfl) ⟨560132, by rfl⟩ : syracuseStep 746843 = 1120265) B1120265
theorem B746863 : Blo 746329 746863 := bstep (se 1 (by rfl) ⟨560147, by rfl⟩ : syracuseStep 746863 = 1120295) B1120295
theorem B746919 : Blo 746329 746919 := bstep (se 1 (by rfl) ⟨560189, by rfl⟩ : syracuseStep 746919 = 1120379) B1120379
theorem B1893881 : Blo 746329 1893881 := bstep (se 2 (by rfl) ⟨710205, by rfl⟩ : syracuseStep 1893881 = 1420411) B1420411
theorem B747003 : Blo 746329 747003 := bstep (se 1 (by rfl) ⟨560252, by rfl⟩ : syracuseStep 747003 = 1120505) B1120505
theorem B747071 : Blo 746329 747071 := bstep (se 1 (by rfl) ⟨560303, by rfl⟩ : syracuseStep 747071 = 1120607) B1120607
theorem B747079 : Blo 746329 747079 := bstep (se 1 (by rfl) ⟨560309, by rfl⟩ : syracuseStep 747079 = 1120619) B1120619
theorem B747231 : Blo 746329 747231 := bstep (se 1 (by rfl) ⟨560423, by rfl⟩ : syracuseStep 747231 = 1120847) B1120847
theorem B23029505 : Blo 746329 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B747311 : Blo 746329 747311 := bstep (se 1 (by rfl) ⟨560483, by rfl⟩ : syracuseStep 747311 = 1120967) B1120967
theorem B2844497 : Blo 746329 2844497 := bstep (se 2 (by rfl) ⟨1066686, by rfl⟩ : syracuseStep 2844497 = 2133373) B2133373
theorem B747419 : Blo 746329 747419 := bstep (se 1 (by rfl) ⟨560564, by rfl⟩ : syracuseStep 747419 = 1121129) B1121129
theorem B747471 : Blo 746329 747471 := bstep (se 1 (by rfl) ⟨560603, by rfl⟩ : syracuseStep 747471 = 1121207) B1121207
theorem B747495 : Blo 746329 747495 := bstep (se 1 (by rfl) ⟨560621, by rfl⟩ : syracuseStep 747495 = 1121243) B1121243
theorem B6482035 : Blo 746329 6482035 := bstep (se 1 (by rfl) ⟨4861526, by rfl⟩ : syracuseStep 6482035 = 9723053) B9723053
theorem B1894529 : Blo 746329 1894529 := bstep (se 2 (by rfl) ⟨710448, by rfl⟩ : syracuseStep 1894529 = 1420897) B1420897
theorem B2844953 : Blo 746329 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B747807 : Blo 746329 747807 := bstep (se 1 (by rfl) ⟨560855, by rfl⟩ : syracuseStep 747807 = 1121711) B1121711
theorem B13297955 : Blo 746329 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B747867 : Blo 746329 747867 := bstep (se 1 (by rfl) ⟨560900, by rfl⟩ : syracuseStep 747867 = 1121801) B1121801
theorem B1599851 : Blo 746329 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B747887 : Blo 746329 747887 := bstep (se 1 (by rfl) ⟨560915, by rfl⟩ : syracuseStep 747887 = 1121831) B1121831
theorem B747943 : Blo 746329 747943 := bstep (se 1 (by rfl) ⟨560957, by rfl⟩ : syracuseStep 747943 = 1121915) B1121915
theorem B1894823 : Blo 746329 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B1010119 : Blo 746329 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B748027 : Blo 746329 748027 := bstep (se 1 (by rfl) ⟨561020, by rfl⟩ : syracuseStep 748027 = 1122041) B1122041
theorem B748095 : Blo 746329 748095 := bstep (se 1 (by rfl) ⟨561071, by rfl⟩ : syracuseStep 748095 = 1122143) B1122143
theorem B748103 : Blo 746329 748103 := bstep (se 1 (by rfl) ⟨561077, by rfl⟩ : syracuseStep 748103 = 1122155) B1122155
theorem B1796681 : Blo 746329 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1894985 : Blo 746329 1894985 := bstep (se 2 (by rfl) ⟨710619, by rfl⟩ : syracuseStep 1894985 = 1421239) B1421239
theorem B748255 : Blo 746329 748255 := bstep (se 1 (by rfl) ⟨561191, by rfl⟩ : syracuseStep 748255 = 1122383) B1122383
theorem B944875 : Blo 746329 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B2878199 : Blo 746329 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B748335 : Blo 746329 748335 := bstep (se 1 (by rfl) ⟨561251, by rfl⟩ : syracuseStep 748335 = 1122503) B1122503
theorem B748443 : Blo 746329 748443 := bstep (se 1 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 748443 = 1122665) B1122665
theorem B1895339 : Blo 746329 1895339 := bstep (se 1 (by rfl) ⟨1421504, by rfl⟩ : syracuseStep 1895339 = 2843009) B2843009
theorem B945103 : Blo 746329 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B748495 : Blo 746329 748495 := bstep (se 1 (by rfl) ⟨561371, by rfl⟩ : syracuseStep 748495 = 1122743) B1122743
theorem B748519 : Blo 746329 748519 := bstep (se 1 (by rfl) ⟨561389, by rfl⟩ : syracuseStep 748519 = 1122779) B1122779
theorem B3795983 : Blo 746329 3795983 := bstep (se 1 (by rfl) ⟨2846987, by rfl⟩ : syracuseStep 3795983 = 5693975) B5693975
theorem B1895521 : Blo 746329 1895521 := bstep (se 2 (by rfl) ⟨710820, by rfl⟩ : syracuseStep 1895521 = 1421641) B1421641
theorem B945371 : Blo 746329 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B748831 : Blo 746329 748831 := bstep (se 1 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 748831 = 1123247) B1123247
theorem B32304419 : Blo 746329 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B4255037 : Blo 746329 4255037 := bstep (se 3 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 4255037 = 1595639) B1595639
theorem B748891 : Blo 746329 748891 := bstep (se 1 (by rfl) ⟨561668, by rfl⟩ : syracuseStep 748891 = 1123337) B1123337
theorem B748911 : Blo 746329 748911 := bstep (se 1 (by rfl) ⟨561683, by rfl⟩ : syracuseStep 748911 = 1123367) B1123367
theorem B2026889 : Blo 746329 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B748967 : Blo 746329 748967 := bstep (se 1 (by rfl) ⟨561725, by rfl⟩ : syracuseStep 748967 = 1123451) B1123451
theorem B749051 : Blo 746329 749051 := bstep (se 1 (by rfl) ⟨561788, by rfl⟩ : syracuseStep 749051 = 1123577) B1123577
theorem B1797689 : Blo 746329 1797689 := bstep (se 2 (by rfl) ⟨674133, by rfl⟩ : syracuseStep 1797689 = 1348267) B1348267
theorem B749119 : Blo 746329 749119 := bstep (se 1 (by rfl) ⟨561839, by rfl⟩ : syracuseStep 749119 = 1123679) B1123679
theorem B749127 : Blo 746329 749127 := bstep (se 1 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 749127 = 1123691) B1123691
theorem B945847 : Blo 746329 945847 := bstep (se 1 (by rfl) ⟨709385, by rfl⟩ : syracuseStep 945847 = 1418771) B1418771
theorem B749279 : Blo 746329 749279 := bstep (se 1 (by rfl) ⟨561959, by rfl⟩ : syracuseStep 749279 = 1123919) B1123919
theorem B749359 : Blo 746329 749359 := bstep (se 1 (by rfl) ⟨562019, by rfl⟩ : syracuseStep 749359 = 1124039) B1124039
theorem B3796793 : Blo 746329 3796793 := bstep (se 2 (by rfl) ⟨1423797, by rfl⟩ : syracuseStep 3796793 = 2847595) B2847595
theorem B946075 : Blo 746329 946075 := bstep (se 1 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 946075 = 1419113) B1419113
theorem B749467 : Blo 746329 749467 := bstep (se 1 (by rfl) ⟨562100, by rfl⟩ : syracuseStep 749467 = 1124201) B1124201
theorem B749519 : Blo 746329 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B749543 : Blo 746329 749543 := bstep (se 1 (by rfl) ⟨562157, by rfl⟩ : syracuseStep 749543 = 1124315) B1124315
theorem B1896473 : Blo 746329 1896473 := bstep (se 2 (by rfl) ⟨711177, by rfl⟩ : syracuseStep 1896473 = 1422355) B1422355
theorem B2519099 : Blo 746329 2519099 := bstep (se 1 (by rfl) ⟨1889324, by rfl⟩ : syracuseStep 2519099 = 3778649) B3778649
theorem B9105473 : Blo 746329 9105473 := bstep (se 2 (by rfl) ⟨3414552, by rfl⟩ : syracuseStep 9105473 = 6829105) B6829105
theorem B749855 : Blo 746329 749855 := bstep (se 1 (by rfl) ⟨562391, by rfl⟩ : syracuseStep 749855 = 1124783) B1124783
theorem B2519369 : Blo 746329 2519369 := bstep (se 2 (by rfl) ⟨944763, by rfl⟩ : syracuseStep 2519369 = 1889527) B1889527
theorem B2027849 : Blo 746329 2027849 := bstep (se 2 (by rfl) ⟨760443, by rfl⟩ : syracuseStep 2027849 = 1520887) B1520887
theorem B749915 : Blo 746329 749915 := bstep (se 1 (by rfl) ⟨562436, by rfl⟩ : syracuseStep 749915 = 1124873) B1124873
theorem B17985899 : Blo 746329 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B749935 : Blo 746329 749935 := bstep (se 1 (by rfl) ⟨562451, by rfl⟩ : syracuseStep 749935 = 1124903) B1124903
theorem B749991 : Blo 746329 749991 := bstep (se 1 (by rfl) ⟨562493, by rfl⟩ : syracuseStep 749991 = 1124987) B1124987
theorem B1896929 : Blo 746329 1896929 := bstep (se 2 (by rfl) ⟨711348, by rfl⟩ : syracuseStep 1896929 = 1422697) B1422697
theorem B750075 : Blo 746329 750075 := bstep (se 1 (by rfl) ⟨562556, by rfl⟩ : syracuseStep 750075 = 1125113) B1125113
theorem B1896979 : Blo 746329 1896979 := bstep (se 1 (by rfl) ⟨1422734, by rfl⟩ : syracuseStep 1896979 = 2845469) B2845469
theorem B750143 : Blo 746329 750143 := bstep (se 1 (by rfl) ⟨562607, by rfl⟩ : syracuseStep 750143 = 1125215) B1125215
theorem B750151 : Blo 746329 750151 := bstep (se 1 (by rfl) ⟨562613, by rfl⟩ : syracuseStep 750151 = 1125227) B1125227
theorem B750303 : Blo 746329 750303 := bstep (se 1 (by rfl) ⟨562727, by rfl⟩ : syracuseStep 750303 = 1125455) B1125455
theorem B946991 : Blo 746329 946991 := bstep (se 1 (by rfl) ⟨710243, by rfl⟩ : syracuseStep 946991 = 1420487) B1420487
theorem B2847869 : Blo 746329 2847869 := bstep (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) B1067951
theorem B5403793 : Blo 746329 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B10810583 : Blo 746329 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B7206407 : Blo 746329 7206407 := bstep (se 1 (by rfl) ⟨5404805, by rfl⟩ : syracuseStep 7206407 = 10809611) B10809611
theorem B2848567 : Blo 746329 2848567 := bstep (se 1 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 2848567 = 4272851) B4272851
theorem B5404715 : Blo 746329 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B25950307 : Blo 746329 25950307 := bstep (se 1 (by rfl) ⟨19462730, by rfl⟩ : syracuseStep 25950307 = 38925461) B38925461
theorem B1898761 : Blo 746329 1898761 := bstep (se 2 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 1898761 = 1424071) B1424071
theorem B7174763 : Blo 746329 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B92044133 : Blo 746329 92044133 := bstep (se 4 (by rfl) ⟨8629137, by rfl⟩ : syracuseStep 92044133 = 17258275) B17258275
theorem B1703263 : Blo 746329 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2522555 : Blo 746329 2522555 := bstep (se 1 (by rfl) ⟨1891916, by rfl⟩ : syracuseStep 2522555 = 3783833) B3783833
theorem B4259411 : Blo 746329 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B3604297 : Blo 746329 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B1278761 : Blo 746329 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B5407597 : Blo 746329 5407597 := bstep (se 3 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 5407597 = 2027849) B2027849
theorem B2130799 : Blo 746329 2130799 := bstep (se 1 (by rfl) ⟨1598099, by rfl⟩ : syracuseStep 2130799 = 3196199) B3196199
theorem B9602023 : Blo 746329 9602023 := bstep (se 1 (by rfl) ⟨7201517, by rfl⟩ : syracuseStep 9602023 = 14403035) B14403035
theorem B2131049 : Blo 746329 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B2524283 : Blo 746329 2524283 := bstep (se 1 (by rfl) ⟨1893212, by rfl⟩ : syracuseStep 2524283 = 3786425) B3786425
theorem B4785277 : Blo 746329 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B10257623 : Blo 746329 10257623 := bstep (se 1 (by rfl) ⟨7693217, by rfl⟩ : syracuseStep 10257623 = 15386435) B15386435
theorem B2524553 : Blo 746329 2524553 := bstep (se 2 (by rfl) ⟨946707, by rfl⟩ : syracuseStep 2524553 = 1893415) B1893415
theorem B3114611 : Blo 746329 3114611 := bstep (se 1 (by rfl) ⟨2335958, by rfl⟩ : syracuseStep 3114611 = 4671917) B4671917
theorem B2459297 : Blo 746329 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B2525309 : Blo 746329 2525309 := bstep (se 3 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 2525309 = 946991) B946991
theorem B1214759 : Blo 746329 1214759 := bstep (se 1 (by rfl) ⟨911069, by rfl⟩ : syracuseStep 1214759 = 1822139) B1822139
theorem B2132315 : Blo 746329 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B3246427 : Blo 746329 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B2525579 : Blo 746329 2525579 := bstep (se 1 (by rfl) ⟨1894184, by rfl⟩ : syracuseStep 2525579 = 3788369) B3788369
theorem B2132507 : Blo 746329 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B6392465 : Blo 746329 6392465 := bstep (se 2 (by rfl) ⟨2397174, by rfl⟩ : syracuseStep 6392465 = 4794349) B4794349
theorem B2395099 : Blo 746329 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B4263101 : Blo 746329 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B2133191 : Blo 746329 2133191 := bstep (se 1 (by rfl) ⟨1599893, by rfl⟩ : syracuseStep 2133191 = 3199787) B3199787
theorem B1346825 : Blo 746329 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B2133499 : Blo 746329 2133499 := bstep (se 1 (by rfl) ⟨1600124, by rfl⟩ : syracuseStep 2133499 = 3200249) B3200249
theorem B29200193 : Blo 746329 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B4263785 : Blo 746329 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B2527199 : Blo 746329 2527199 := bstep (se 1 (by rfl) ⟨1895399, by rfl⟩ : syracuseStep 2527199 = 3790799) B3790799
theorem B2527361 : Blo 746329 2527361 := bstep (se 2 (by rfl) ⟨947760, by rfl⟩ : syracuseStep 2527361 = 1895521) B1895521
theorem B16192001 : Blo 746329 16192001 := bstep (se 2 (by rfl) ⟨6072000, by rfl⟩ : syracuseStep 16192001 = 12144001) B12144001
theorem B2527847 : Blo 746329 2527847 := bstep (se 1 (by rfl) ⟨1895885, by rfl⟩ : syracuseStep 2527847 = 3791771) B3791771
theorem B2134775 : Blo 746329 2134775 := bstep (se 1 (by rfl) ⟨1601081, by rfl⟩ : syracuseStep 2134775 = 3202163) B3202163
theorem B2528171 : Blo 746329 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B2528603 : Blo 746329 2528603 := bstep (se 1 (by rfl) ⟨1896452, by rfl⟩ : syracuseStep 2528603 = 3792905) B3792905
theorem B2528711 : Blo 746329 2528711 := bstep (se 1 (by rfl) ⟨1896533, by rfl⟩ : syracuseStep 2528711 = 3793067) B3793067
theorem B1119815 : Blo 746329 1119815 := bstep (se 1 (by rfl) ⟨839861, by rfl⟩ : syracuseStep 1119815 = 1679723) B1679723
theorem B1119911 : Blo 746329 1119911 := bstep (se 1 (by rfl) ⟨839933, by rfl⟩ : syracuseStep 1119911 = 1679867) B1679867
theorem B1119995 : Blo 746329 1119995 := bstep (se 1 (by rfl) ⟨839996, by rfl⟩ : syracuseStep 1119995 = 1679993) B1679993
theorem B6067979 : Blo 746329 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B2529035 : Blo 746329 2529035 := bstep (se 1 (by rfl) ⟨1896776, by rfl⟩ : syracuseStep 2529035 = 3793553) B3793553
theorem B1120031 : Blo 746329 1120031 := bstep (se 1 (by rfl) ⟨840023, by rfl⟩ : syracuseStep 1120031 = 1680047) B1680047
theorem B1120079 : Blo 746329 1120079 := bstep (se 1 (by rfl) ⟨840059, by rfl⟩ : syracuseStep 1120079 = 1680119) B1680119
theorem B1120199 : Blo 746329 1120199 := bstep (se 1 (by rfl) ⟨840149, by rfl⟩ : syracuseStep 1120199 = 1680299) B1680299
theorem B2529305 : Blo 746329 2529305 := bstep (se 2 (by rfl) ⟨948489, by rfl⟩ : syracuseStep 2529305 = 1896979) B1896979
theorem B37427293 : Blo 746329 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B4266269 : Blo 746329 4266269 := bstep (se 3 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 4266269 = 1599851) B1599851
theorem B1120553 : Blo 746329 1120553 := bstep (se 2 (by rfl) ⟨420207, by rfl⟩ : syracuseStep 1120553 = 840415) B840415
theorem B1120559 : Blo 746329 1120559 := bstep (se 1 (by rfl) ⟨840419, by rfl⟩ : syracuseStep 1120559 = 1680839) B1680839
theorem B1120799 : Blo 746329 1120799 := bstep (se 1 (by rfl) ⟨840599, by rfl⟩ : syracuseStep 1120799 = 1681199) B1681199
theorem B4791149 : Blo 746329 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B1121183 : Blo 746329 1121183 := bstep (se 1 (by rfl) ⟨840887, by rfl⟩ : syracuseStep 1121183 = 1681775) B1681775
theorem B1121231 : Blo 746329 1121231 := bstep (se 1 (by rfl) ⟨840923, by rfl⟩ : syracuseStep 1121231 = 1681847) B1681847
theorem B1121321 : Blo 746329 1121321 := bstep (se 2 (by rfl) ⟨420495, by rfl⟩ : syracuseStep 1121321 = 840991) B840991
theorem B1121327 : Blo 746329 1121327 := bstep (se 1 (by rfl) ⟨840995, by rfl⟩ : syracuseStep 1121327 = 1681991) B1681991
theorem B1121351 : Blo 746329 1121351 := bstep (se 1 (by rfl) ⟨841013, by rfl⟩ : syracuseStep 1121351 = 1682027) B1682027
theorem B1121615 : Blo 746329 1121615 := bstep (se 1 (by rfl) ⟨841211, by rfl⟩ : syracuseStep 1121615 = 1682423) B1682423
theorem B2530655 : Blo 746329 2530655 := bstep (se 1 (by rfl) ⟨1897991, by rfl⟩ : syracuseStep 2530655 = 3795983) B3795983
theorem B1121705 : Blo 746329 1121705 := bstep (se 2 (by rfl) ⟨420639, by rfl⟩ : syracuseStep 1121705 = 841279) B841279
theorem B21536279 : Blo 746329 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B1121855 : Blo 746329 1121855 := bstep (se 1 (by rfl) ⟨841391, by rfl⟩ : syracuseStep 1121855 = 1682783) B1682783
theorem B1351259 : Blo 746329 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B1122119 : Blo 746329 1122119 := bstep (se 1 (by rfl) ⟨841589, by rfl⟩ : syracuseStep 1122119 = 1683179) B1683179
theorem B2531195 : Blo 746329 2531195 := bstep (se 1 (by rfl) ⟨1898396, by rfl⟩ : syracuseStep 2531195 = 3796793) B3796793
theorem B1122203 : Blo 746329 1122203 := bstep (se 1 (by rfl) ⟨841652, by rfl⟩ : syracuseStep 1122203 = 1683305) B1683305
theorem B34611137 : Blo 746329 34611137 := bstep (se 2 (by rfl) ⟨12979176, by rfl⟩ : syracuseStep 34611137 = 25958353) B25958353
theorem B1679399 : Blo 746329 1679399 := bstep (se 1 (by rfl) ⟨1259549, by rfl⟩ : syracuseStep 1679399 = 2519099) B2519099
theorem B6070315 : Blo 746329 6070315 := bstep (se 1 (by rfl) ⟨4552736, by rfl⟩ : syracuseStep 6070315 = 9105473) B9105473
theorem B1679579 : Blo 746329 1679579 := bstep (se 1 (by rfl) ⟨1259684, by rfl⟩ : syracuseStep 1679579 = 2519369) B2519369
theorem B4792607 : Blo 746329 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B2531681 : Blo 746329 2531681 := bstep (se 2 (by rfl) ⟨949380, by rfl⟩ : syracuseStep 2531681 = 1898761) B1898761
theorem B1122767 : Blo 746329 1122767 := bstep (se 1 (by rfl) ⟨842075, by rfl⟩ : syracuseStep 1122767 = 1684151) B1684151
theorem B1679849 : Blo 746329 1679849 := bstep (se 2 (by rfl) ⟨629943, by rfl⟩ : syracuseStep 1679849 = 1259887) B1259887
theorem B1122809 : Blo 746329 1122809 := bstep (se 2 (by rfl) ⟨421053, by rfl⟩ : syracuseStep 1122809 = 842107) B842107
theorem B1122911 : Blo 746329 1122911 := bstep (se 1 (by rfl) ⟨842183, by rfl⟩ : syracuseStep 1122911 = 1684367) B1684367
theorem B2695787 : Blo 746329 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B1680137 : Blo 746329 1680137 := bstep (se 2 (by rfl) ⟨630051, by rfl⟩ : syracuseStep 1680137 = 1260103) B1260103
theorem B1123391 : Blo 746329 1123391 := bstep (se 1 (by rfl) ⟨842543, by rfl⟩ : syracuseStep 1123391 = 1685087) B1685087
theorem B1123433 : Blo 746329 1123433 := bstep (se 2 (by rfl) ⟨421287, by rfl⟩ : syracuseStep 1123433 = 842575) B842575
theorem B1123535 : Blo 746329 1123535 := bstep (se 1 (by rfl) ⟨842651, by rfl⟩ : syracuseStep 1123535 = 1685303) B1685303
theorem B1680713 : Blo 746329 1680713 := bstep (se 2 (by rfl) ⟨630267, by rfl⟩ : syracuseStep 1680713 = 1260535) B1260535
theorem B1123739 : Blo 746329 1123739 := bstep (se 1 (by rfl) ⟨842804, by rfl⟩ : syracuseStep 1123739 = 1685609) B1685609
theorem B6563321 : Blo 746329 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B1123961 : Blo 746329 1123961 := bstep (se 2 (by rfl) ⟨421485, by rfl⟩ : syracuseStep 1123961 = 842971) B842971
theorem B4794041 : Blo 746329 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B1124063 : Blo 746329 1124063 := bstep (se 1 (by rfl) ⟨843047, by rfl⟩ : syracuseStep 1124063 = 1686095) B1686095
theorem B2271017 : Blo 746329 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B1124159 : Blo 746329 1124159 := bstep (se 1 (by rfl) ⟨843119, by rfl⟩ : syracuseStep 1124159 = 1686239) B1686239
theorem B1124327 : Blo 746329 1124327 := bstep (se 1 (by rfl) ⟨843245, by rfl⟩ : syracuseStep 1124327 = 1686491) B1686491
theorem B1124345 : Blo 746329 1124345 := bstep (se 2 (by rfl) ⟨421629, by rfl⟩ : syracuseStep 1124345 = 843259) B843259
theorem B1124447 : Blo 746329 1124447 := bstep (se 1 (by rfl) ⟨843335, by rfl⟩ : syracuseStep 1124447 = 1686671) B1686671
theorem B1124507 : Blo 746329 1124507 := bstep (se 1 (by rfl) ⟨843380, by rfl⟩ : syracuseStep 1124507 = 1686761) B1686761
theorem B1124543 : Blo 746329 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B1124585 : Blo 746329 1124585 := bstep (se 2 (by rfl) ⟨421719, by rfl⟩ : syracuseStep 1124585 = 843439) B843439
theorem B1681703 : Blo 746329 1681703 := bstep (se 1 (by rfl) ⟨1261277, by rfl⟩ : syracuseStep 1681703 = 2522555) B2522555
theorem B1681721 : Blo 746329 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B1124891 : Blo 746329 1124891 := bstep (se 1 (by rfl) ⟨843668, by rfl⟩ : syracuseStep 1124891 = 1687337) B1687337
theorem B1124969 : Blo 746329 1124969 := bstep (se 2 (by rfl) ⟨421863, by rfl⟩ : syracuseStep 1124969 = 843727) B843727
theorem B4041667 : Blo 746329 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B1420267 : Blo 746329 1420267 := bstep (se 1 (by rfl) ⟨1065200, by rfl⟩ : syracuseStep 1420267 = 2130401) B2130401
theorem B4271575 : Blo 746329 4271575 := bstep (se 1 (by rfl) ⟨3203681, by rfl⟩ : syracuseStep 4271575 = 6407363) B6407363
theorem B1683017 : Blo 746329 1683017 := bstep (se 2 (by rfl) ⟨631131, by rfl⟩ : syracuseStep 1683017 = 1262263) B1262263
theorem B798503 : Blo 746329 798503 := bstep (se 1 (by rfl) ⟨598877, by rfl⟩ : syracuseStep 798503 = 1197755) B1197755
theorem B12758957 : Blo 746329 12758957 := bstep (se 3 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 12758957 = 4784609) B4784609
theorem B276377615 : Blo 746329 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B3191723 : Blo 746329 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1684475 : Blo 746329 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B1684655 : Blo 746329 1684655 := bstep (se 1 (by rfl) ⟨1263491, by rfl⟩ : syracuseStep 1684655 = 2526983) B2526983
theorem B1684691 : Blo 746329 1684691 := bstep (se 1 (by rfl) ⟨1263518, by rfl⟩ : syracuseStep 1684691 = 2527037) B2527037
theorem B1684961 : Blo 746329 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B1423099 : Blo 746329 1423099 := bstep (se 1 (by rfl) ⟨1067324, by rfl⟩ : syracuseStep 1423099 = 2134649) B2134649
theorem B3028799 : Blo 746329 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B3782537 : Blo 746329 3782537 := bstep (se 2 (by rfl) ⟨1418451, by rfl⟩ : syracuseStep 3782537 = 2836903) B2836903
theorem B17316119 : Blo 746329 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B4798757 : Blo 746329 4798757 := bstep (se 4 (by rfl) ⟨449883, by rfl⟩ : syracuseStep 4798757 = 899767) B899767
theorem B3422507 : Blo 746329 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B1259833 : Blo 746329 1259833 := bstep (se 2 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 1259833 = 944875) B944875
theorem B3651913 : Blo 746329 3651913 := bstep (se 2 (by rfl) ⟨1369467, by rfl⟩ : syracuseStep 3651913 = 2738935) B2738935
theorem B5683769 : Blo 746329 5683769 := bstep (se 2 (by rfl) ⟨2131413, by rfl⟩ : syracuseStep 5683769 = 4262827) B4262827
theorem B1260137 : Blo 746329 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B3849257 : Blo 746329 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B1686599 : Blo 746329 1686599 := bstep (se 1 (by rfl) ⟨1264949, by rfl⟩ : syracuseStep 1686599 = 2529899) B2529899
theorem B1260967 : Blo 746329 1260967 := bstep (se 1 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 1260967 = 1891451) B1891451
theorem B1686995 : Blo 746329 1686995 := bstep (se 1 (by rfl) ⟨1265246, by rfl⟩ : syracuseStep 1686995 = 2530493) B2530493
theorem B1064443 : Blo 746329 1064443 := bstep (se 1 (by rfl) ⟨798332, by rfl⟩ : syracuseStep 1064443 = 1596665) B1596665
theorem B1261129 : Blo 746329 1261129 := bstep (se 2 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 1261129 = 945847) B945847
theorem B1261163 : Blo 746329 1261163 := bstep (se 1 (by rfl) ⟨945872, by rfl⟩ : syracuseStep 1261163 = 1891745) B1891745
theorem B1687265 : Blo 746329 1687265 := bstep (se 2 (by rfl) ⟨632724, by rfl⟩ : syracuseStep 1687265 = 1265449) B1265449
theorem B2735927 : Blo 746329 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B1261433 : Blo 746329 1261433 := bstep (se 2 (by rfl) ⟨473037, by rfl⟩ : syracuseStep 1261433 = 946075) B946075
theorem B1064927 : Blo 746329 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B5456011 : Blo 746329 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B1196537 : Blo 746329 1196537 := bstep (se 2 (by rfl) ⟨448701, by rfl⟩ : syracuseStep 1196537 = 897403) B897403
theorem B4309699 : Blo 746329 4309699 := bstep (se 1 (by rfl) ⟨3232274, by rfl⟩ : syracuseStep 4309699 = 6464549) B6464549
theorem B2704175 : Blo 746329 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B3785615 : Blo 746329 3785615 := bstep (se 1 (by rfl) ⟨2839211, by rfl⟩ : syracuseStep 3785615 = 5678423) B5678423
theorem B8111015 : Blo 746329 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B1262587 : Blo 746329 1262587 := bstep (se 1 (by rfl) ⟨946940, by rfl⟩ : syracuseStep 1262587 = 1893881) B1893881
theorem B15353003 : Blo 746329 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B1263019 : Blo 746329 1263019 := bstep (se 1 (by rfl) ⟨947264, by rfl⟩ : syracuseStep 1263019 = 1894529) B1894529
theorem B1263215 : Blo 746329 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B1263323 : Blo 746329 1263323 := bstep (se 1 (by rfl) ⟨947492, by rfl⟩ : syracuseStep 1263323 = 1894985) B1894985
theorem B1918799 : Blo 746329 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B3196847 : Blo 746329 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B1263559 : Blo 746329 1263559 := bstep (se 1 (by rfl) ⟨947669, by rfl⟩ : syracuseStep 1263559 = 1895339) B1895339
theorem B2017405 : Blo 746329 2017405 := bstep (se 3 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 2017405 = 756527) B756527
theorem B2836691 : Blo 746329 2836691 := bstep (se 1 (by rfl) ⟨2127518, by rfl⟩ : syracuseStep 2836691 = 4255037) B4255037
theorem B1198459 : Blo 746329 1198459 := bstep (se 1 (by rfl) ⟨898844, by rfl⟩ : syracuseStep 1198459 = 1797689) B1797689
theorem B1198729 : Blo 746329 1198729 := bstep (se 2 (by rfl) ⟨449523, by rfl⟩ : syracuseStep 1198729 = 899047) B899047
theorem B1264315 : Blo 746329 1264315 := bstep (se 1 (by rfl) ⟨948236, by rfl⟩ : syracuseStep 1264315 = 1896473) B1896473
theorem B1264619 : Blo 746329 1264619 := bstep (se 1 (by rfl) ⟨948464, by rfl⟩ : syracuseStep 1264619 = 1896929) B1896929
theorem B2280893 : Blo 746329 2280893 := bstep (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) B855335
theorem B1363447 : Blo 746329 1363447 := bstep (se 1 (by rfl) ⟨1022585, by rfl⟩ : syracuseStep 1363447 = 2045171) B2045171
theorem B4804271 : Blo 746329 4804271 := bstep (se 1 (by rfl) ⟨3603203, by rfl⟩ : syracuseStep 4804271 = 7206407) B7206407
theorem B4050769 : Blo 746329 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B8507429 : Blo 746329 8507429 := bstep (se 4 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 8507429 = 1595143) B1595143
theorem B2019451 : Blo 746329 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B839911 : Blo 746329 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B61362755 : Blo 746329 61362755 := bstep (se 1 (by rfl) ⟨46022066, by rfl⟩ : syracuseStep 61362755 = 92044133) B92044133
theorem B840559 : Blo 746329 840559 := bstep (se 1 (by rfl) ⟨630419, by rfl⟩ : syracuseStep 840559 = 1260839) B1260839
theorem B1889153 : Blo 746329 1889153 := bstep (se 2 (by rfl) ⟨708432, by rfl⟩ : syracuseStep 1889153 = 1416865) B1416865
theorem B2839607 : Blo 746329 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B4805729 : Blo 746329 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B10769759 : Blo 746329 10769759 := bstep (se 1 (by rfl) ⟨8077319, by rfl⟩ : syracuseStep 10769759 = 16154639) B16154639
theorem B10245527 : Blo 746329 10245527 := bstep (se 1 (by rfl) ⟨7684145, by rfl⟩ : syracuseStep 10245527 = 15368291) B15368291
theorem B9590237 : Blo 746329 9590237 := bstep (se 3 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 9590237 = 3596339) B3596339
theorem B1234543 : Blo 746329 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B1889963 : Blo 746329 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B1365727 : Blo 746329 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B6838151 : Blo 746329 6838151 := bstep (se 1 (by rfl) ⟨5128613, by rfl⟩ : syracuseStep 6838151 = 10257227) B10257227
theorem B1890287 : Blo 746329 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B841711 : Blo 746329 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B47962397 : Blo 746329 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B10934651 : Blo 746329 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B2841581 : Blo 746329 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B1891795 : Blo 746329 1891795 := bstep (se 1 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 1891795 = 2837693) B2837693
theorem B8642713 : Blo 746329 8642713 := bstep (se 2 (by rfl) ⟨3241017, by rfl⟩ : syracuseStep 8642713 = 6482035) B6482035
theorem B141844853 : Blo 746329 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B5399293 : Blo 746329 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B4547339 : Blo 746329 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B746351 : Blo 746329 746351 := bstep (se 1 (by rfl) ⟨559763, by rfl⟩ : syracuseStep 746351 = 1119527) B1119527
theorem B746407 : Blo 746329 746407 := bstep (se 1 (by rfl) ⟨559805, by rfl⟩ : syracuseStep 746407 = 1119611) B1119611
theorem B746491 : Blo 746329 746491 := bstep (se 1 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 746491 = 1119737) B1119737
theorem B746559 : Blo 746329 746559 := bstep (se 1 (by rfl) ⟨559919, by rfl⟩ : syracuseStep 746559 = 1119839) B1119839
theorem B49996973 : Blo 746329 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B4547773 : Blo 746329 4547773 := bstep (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) B1705415
theorem B746703 : Blo 746329 746703 := bstep (se 1 (by rfl) ⟨560027, by rfl⟩ : syracuseStep 746703 = 1120055) B1120055
theorem B1893739 : Blo 746329 1893739 := bstep (se 1 (by rfl) ⟨1420304, by rfl⟩ : syracuseStep 1893739 = 2840609) B2840609
theorem B2844011 : Blo 746329 2844011 := bstep (se 1 (by rfl) ⟨2133008, by rfl⟩ : syracuseStep 2844011 = 4266017) B4266017
theorem B746907 : Blo 746329 746907 := bstep (se 1 (by rfl) ⟨560180, by rfl⟩ : syracuseStep 746907 = 1120361) B1120361
theorem B3204623 : Blo 746329 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B747119 : Blo 746329 747119 := bstep (se 1 (by rfl) ⟨560339, by rfl⟩ : syracuseStep 747119 = 1120679) B1120679
theorem B747175 : Blo 746329 747175 := bstep (se 1 (by rfl) ⟨560381, by rfl⟩ : syracuseStep 747175 = 1120763) B1120763
theorem B3204775 : Blo 746329 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B747259 : Blo 746329 747259 := bstep (se 1 (by rfl) ⟨560444, by rfl⟩ : syracuseStep 747259 = 1120889) B1120889
theorem B747295 : Blo 746329 747295 := bstep (se 1 (by rfl) ⟨560471, by rfl⟩ : syracuseStep 747295 = 1120943) B1120943
theorem B1894175 : Blo 746329 1894175 := bstep (se 1 (by rfl) ⟨1420631, by rfl⟩ : syracuseStep 1894175 = 2841263) B2841263
theorem B4384543 : Blo 746329 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B747327 : Blo 746329 747327 := bstep (se 1 (by rfl) ⟨560495, by rfl⟩ : syracuseStep 747327 = 1120991) B1120991
theorem B34498457 : Blo 746329 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B747503 : Blo 746329 747503 := bstep (se 1 (by rfl) ⟨560627, by rfl⟩ : syracuseStep 747503 = 1121255) B1121255
theorem B747675 : Blo 746329 747675 := bstep (se 1 (by rfl) ⟨560756, by rfl⟩ : syracuseStep 747675 = 1121513) B1121513
theorem B747711 : Blo 746329 747711 := bstep (se 1 (by rfl) ⟨560783, by rfl⟩ : syracuseStep 747711 = 1121567) B1121567
theorem B747823 : Blo 746329 747823 := bstep (se 1 (by rfl) ⟨560867, by rfl⟩ : syracuseStep 747823 = 1121735) B1121735
theorem B748059 : Blo 746329 748059 := bstep (se 1 (by rfl) ⟨561044, by rfl⟩ : syracuseStep 748059 = 1122089) B1122089
theorem B748063 : Blo 746329 748063 := bstep (se 1 (by rfl) ⟨561047, by rfl⟩ : syracuseStep 748063 = 1122095) B1122095
theorem B3795659 : Blo 746329 3795659 := bstep (se 1 (by rfl) ⟨2846744, by rfl⟩ : syracuseStep 3795659 = 5693489) B5693489
theorem B748379 : Blo 746329 748379 := bstep (se 1 (by rfl) ⟨561284, by rfl⟩ : syracuseStep 748379 = 1122569) B1122569
theorem B11824015 : Blo 746329 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B748447 : Blo 746329 748447 := bstep (se 1 (by rfl) ⟨561335, by rfl⟩ : syracuseStep 748447 = 1122671) B1122671
theorem B945199 : Blo 746329 945199 := bstep (se 1 (by rfl) ⟨708899, by rfl⟩ : syracuseStep 945199 = 1417799) B1417799
theorem B748591 : Blo 746329 748591 := bstep (se 1 (by rfl) ⟨561443, by rfl⟩ : syracuseStep 748591 = 1122887) B1122887
theorem B1895471 : Blo 746329 1895471 := bstep (se 1 (by rfl) ⟨1421603, by rfl⟩ : syracuseStep 1895471 = 2843207) B2843207
theorem B748615 : Blo 746329 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B748767 : Blo 746329 748767 := bstep (se 1 (by rfl) ⟨561575, by rfl⟩ : syracuseStep 748767 = 1123151) B1123151
theorem B4615639 : Blo 746329 4615639 := bstep (se 1 (by rfl) ⟨3461729, by rfl⟩ : syracuseStep 4615639 = 6923459) B6923459
theorem B749031 : Blo 746329 749031 := bstep (se 1 (by rfl) ⟨561773, by rfl⟩ : syracuseStep 749031 = 1123547) B1123547
theorem B30797333 : Blo 746329 30797333 := bstep (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) B1443625
theorem B749147 : Blo 746329 749147 := bstep (se 1 (by rfl) ⟨561860, by rfl⟩ : syracuseStep 749147 = 1123721) B1123721
theorem B749383 : Blo 746329 749383 := bstep (se 1 (by rfl) ⟨562037, by rfl⟩ : syracuseStep 749383 = 1124075) B1124075
theorem B2125673 : Blo 746329 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B1896331 : Blo 746329 1896331 := bstep (se 1 (by rfl) ⟨1422248, by rfl⟩ : syracuseStep 1896331 = 2844497) B2844497
theorem B2518991 : Blo 746329 2518991 := bstep (se 1 (by rfl) ⟨1889243, by rfl⟩ : syracuseStep 2518991 = 3778487) B3778487
theorem B749535 : Blo 746329 749535 := bstep (se 1 (by rfl) ⟨562151, by rfl⟩ : syracuseStep 749535 = 1124303) B1124303
theorem B1896635 : Blo 746329 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B7205057 : Blo 746329 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B749799 : Blo 746329 749799 := bstep (se 1 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 749799 = 1124699) B1124699
theorem B2519423 : Blo 746329 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B749951 : Blo 746329 749951 := bstep (se 1 (by rfl) ⟨562463, by rfl⟩ : syracuseStep 749951 = 1124927) B1124927
theorem B750031 : Blo 746329 750031 := bstep (se 1 (by rfl) ⟨562523, by rfl⟩ : syracuseStep 750031 = 1125047) B1125047
theorem B750183 : Blo 746329 750183 := bstep (se 1 (by rfl) ⟨562637, by rfl⟩ : syracuseStep 750183 = 1125275) B1125275
theorem B1897121 : Blo 746329 1897121 := bstep (se 2 (by rfl) ⟨711420, by rfl⟩ : syracuseStep 1897121 = 1422841) B1422841
theorem B7205597 : Blo 746329 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B3208061 : Blo 746329 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B3798089 : Blo 746329 3798089 := bstep (se 2 (by rfl) ⟨1424283, by rfl⟩ : syracuseStep 3798089 = 2848567) B2848567
theorem B6387133 : Blo 746329 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B34600409 : Blo 746329 34600409 := bstep (se 2 (by rfl) ⟨12975153, by rfl⟩ : syracuseStep 34600409 = 25950307) B25950307
theorem B2520827 : Blo 746329 2520827 := bstep (se 1 (by rfl) ⟨1890620, by rfl⟩ : syracuseStep 2520827 = 3781241) B3781241
theorem B947963 : Blo 746329 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B2520989 : Blo 746329 2520989 := bstep (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) B945371
theorem B1898579 : Blo 746329 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B7207055 : Blo 746329 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B948763 : Blo 746329 948763 := bstep (se 1 (by rfl) ⟨711572, by rfl⟩ : syracuseStep 948763 = 1423145) B1423145
theorem B1899065 : Blo 746329 1899065 := bstep (se 2 (by rfl) ⟨712149, by rfl⟩ : syracuseStep 1899065 = 1424299) B1424299
theorem B1800841 : Blo 746329 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B3603143 : Blo 746329 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B4553495 : Blo 746329 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B2521961 : Blo 746329 2521961 := bstep (se 2 (by rfl) ⟨945735, by rfl⟩ : syracuseStep 2521961 = 1891471) B1891471
theorem B2522015 : Blo 746329 2522015 := bstep (se 1 (by rfl) ⟨1891511, by rfl⟩ : syracuseStep 2522015 = 3783023) B3783023
theorem B4783175 : Blo 746329 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B949583 : Blo 746329 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B4783789 : Blo 746329 4783789 := bstep (se 3 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 4783789 = 1793921) B1793921
theorem B9567989 : Blo 746329 9567989 := bstep (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) B896999
theorem B8093753 : Blo 746329 8093753 := bstep (se 2 (by rfl) ⟨3035157, by rfl⟩ : syracuseStep 8093753 = 6070315) B6070315
theorem B7274681 : Blo 746329 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B1802783 : Blo 746329 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B2523743 : Blo 746329 2523743 := bstep (se 1 (by rfl) ⟨1892807, by rfl⟩ : syracuseStep 2523743 = 3785615) B3785615
theorem B5407343 : Blo 746329 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B1639531 : Blo 746329 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B7210129 : Blo 746329 7210129 := bstep (se 2 (by rfl) ⟨2703798, by rfl⟩ : syracuseStep 7210129 = 5407597) B5407597
theorem B1279199 : Blo 746329 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B6063697 : Blo 746329 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B4261643 : Blo 746329 4261643 := bstep (se 1 (by rfl) ⟨3196232, by rfl⟩ : syracuseStep 4261643 = 6392465) B6392465
theorem B2524985 : Blo 746329 2524985 := bstep (se 2 (by rfl) ⟨946869, by rfl⟩ : syracuseStep 2524985 = 1893739) B1893739
theorem B6391781 : Blo 746329 6391781 := bstep (se 4 (by rfl) ⟨599229, by rfl⟩ : syracuseStep 6391781 = 1198459) B1198459
theorem B3410029 : Blo 746329 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B19466795 : Blo 746329 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B5671619 : Blo 746329 5671619 := bstep (se 1 (by rfl) ⟨4253714, by rfl⟩ : syracuseStep 5671619 = 8507429) B8507429
theorem B4328569 : Blo 746329 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B7179839 : Blo 746329 7179839 := bstep (se 1 (by rfl) ⟨5384879, by rfl⟩ : syracuseStep 7179839 = 10769759) B10769759
theorem B6393491 : Blo 746329 6393491 := bstep (se 1 (by rfl) ⟨4795118, by rfl⟩ : syracuseStep 6393491 = 9590237) B9590237
theorem B15765353 : Blo 746329 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B2527901 : Blo 746329 2527901 := bstep (se 3 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 2527901 = 947963) B947963
theorem B14357519 : Blo 746329 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B8524925 : Blo 746329 8524925 := bstep (se 3 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 8524925 = 3196847) B3196847
theorem B2528441 : Blo 746329 2528441 := bstep (se 2 (by rfl) ⟨948165, by rfl⟩ : syracuseStep 2528441 = 1896331) B1896331
theorem B23074091 : Blo 746329 23074091 := bstep (se 1 (by rfl) ⟨17305568, by rfl⟩ : syracuseStep 23074091 = 34611137) B34611137
theorem B1119599 : Blo 746329 1119599 := bstep (se 1 (by rfl) ⟨839699, by rfl⟩ : syracuseStep 1119599 = 1679399) B1679399
theorem B1119719 : Blo 746329 1119719 := bstep (se 1 (by rfl) ⟨839789, by rfl⟩ : syracuseStep 1119719 = 1679579) B1679579
theorem B2692601 : Blo 746329 2692601 := bstep (se 2 (by rfl) ⟨1009725, by rfl⟩ : syracuseStep 2692601 = 2019451) B2019451
theorem B1119881 : Blo 746329 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B1119899 : Blo 746329 1119899 := bstep (se 1 (by rfl) ⟨839924, by rfl⟩ : syracuseStep 1119899 = 1679849) B1679849
theorem B1120091 : Blo 746329 1120091 := bstep (se 1 (by rfl) ⟨840068, by rfl⟩ : syracuseStep 1120091 = 1680137) B1680137
theorem B46176317 : Blo 746329 46176317 := bstep (se 3 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 46176317 = 17316119) B17316119
theorem B1120475 : Blo 746329 1120475 := bstep (se 1 (by rfl) ⟨840356, by rfl⟩ : syracuseStep 1120475 = 1680713) B1680713
theorem B2136415 : Blo 746329 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B1120745 : Blo 746329 1120745 := bstep (se 2 (by rfl) ⟨420279, by rfl⟩ : syracuseStep 1120745 = 840559) B840559
theorem B1121135 : Blo 746329 1121135 := bstep (se 1 (by rfl) ⟨840851, by rfl⟩ : syracuseStep 1121135 = 1681703) B1681703
theorem B1121147 : Blo 746329 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B2530439 : Blo 746329 2530439 := bstep (se 1 (by rfl) ⟨1897829, by rfl⟩ : syracuseStep 2530439 = 3795659) B3795659
theorem B9608381 : Blo 746329 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B1646057 : Blo 746329 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B1122011 : Blo 746329 1122011 := bstep (se 1 (by rfl) ⟨841508, by rfl⟩ : syracuseStep 1122011 = 1683017) B1683017
theorem B1417115 : Blo 746329 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B1679327 : Blo 746329 1679327 := bstep (se 1 (by rfl) ⟨1259495, by rfl⟩ : syracuseStep 1679327 = 2518991) B2518991
theorem B1122281 : Blo 746329 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B1679615 : Blo 746329 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B1679777 : Blo 746329 1679777 := bstep (se 2 (by rfl) ⟨629916, by rfl⟩ : syracuseStep 1679777 = 1259833) B1259833
theorem B2138707 : Blo 746329 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1122983 : Blo 746329 1122983 := bstep (se 1 (by rfl) ⟨842237, by rfl⟩ : syracuseStep 1122983 = 1684475) B1684475
theorem B2532059 : Blo 746329 2532059 := bstep (se 1 (by rfl) ⟨1899044, by rfl⟩ : syracuseStep 2532059 = 3798089) B3798089
theorem B1123103 : Blo 746329 1123103 := bstep (se 1 (by rfl) ⟨842327, by rfl⟩ : syracuseStep 1123103 = 1684655) B1684655
theorem B1123127 : Blo 746329 1123127 := bstep (se 1 (by rfl) ⟨842345, by rfl⟩ : syracuseStep 1123127 = 1684691) B1684691
theorem B2401121 : Blo 746329 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B2532221 : Blo 746329 2532221 := bstep (se 3 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 2532221 = 949583) B949583
theorem B1123307 : Blo 746329 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B1680551 : Blo 746329 1680551 := bstep (se 1 (by rfl) ⟨1260413, by rfl⟩ : syracuseStep 1680551 = 2520827) B2520827
theorem B1680659 : Blo 746329 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B1681289 : Blo 746329 1681289 := bstep (se 2 (by rfl) ⟨630483, by rfl⟩ : syracuseStep 1681289 = 1260967) B1260967
theorem B1681307 : Blo 746329 1681307 := bstep (se 1 (by rfl) ⟨1260980, by rfl⟩ : syracuseStep 1681307 = 2521961) B2521961
theorem B1681343 : Blo 746329 1681343 := bstep (se 1 (by rfl) ⟨1261007, by rfl⟩ : syracuseStep 1681343 = 2522015) B2522015
theorem B1419257 : Blo 746329 1419257 := bstep (se 2 (by rfl) ⟨532221, by rfl⟩ : syracuseStep 1419257 = 1064443) B1064443
theorem B2566171 : Blo 746329 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B3188783 : Blo 746329 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B1124399 : Blo 746329 1124399 := bstep (se 1 (by rfl) ⟨843299, by rfl⟩ : syracuseStep 1124399 = 1686599) B1686599
theorem B1681505 : Blo 746329 1681505 := bstep (se 2 (by rfl) ⟨630564, by rfl⟩ : syracuseStep 1681505 = 1261129) B1261129
theorem B1124663 : Blo 746329 1124663 := bstep (se 1 (by rfl) ⟨843497, by rfl⟩ : syracuseStep 1124663 = 1686995) B1686995
theorem B1124843 : Blo 746329 1124843 := bstep (se 1 (by rfl) ⟨843632, by rfl⟩ : syracuseStep 1124843 = 1687265) B1687265
theorem B10759493 : Blo 746329 10759493 := bstep (se 4 (by rfl) ⟨1008702, by rfl⟩ : syracuseStep 10759493 = 2017405) B2017405
theorem B1682855 : Blo 746329 1682855 := bstep (se 1 (by rfl) ⟨1262141, by rfl⟩ : syracuseStep 1682855 = 2524283) B2524283
theorem B10235335 : Blo 746329 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B5746265 : Blo 746329 5746265 := bstep (se 2 (by rfl) ⟨2154849, by rfl⟩ : syracuseStep 5746265 = 4309699) B4309699
theorem B1683035 : Blo 746329 1683035 := bstep (se 1 (by rfl) ⟨1262276, by rfl⟩ : syracuseStep 1683035 = 2524553) B2524553
theorem B2076407 : Blo 746329 2076407 := bstep (se 1 (by rfl) ⟨1557305, by rfl⟩ : syracuseStep 2076407 = 3114611) B3114611
theorem B3190765 : Blo 746329 3190765 := bstep (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) B1196537
theorem B1683449 : Blo 746329 1683449 := bstep (se 2 (by rfl) ⟨631293, by rfl⟩ : syracuseStep 1683449 = 1262587) B1262587
theorem B1683539 : Blo 746329 1683539 := bstep (se 1 (by rfl) ⟨1262654, by rfl⟩ : syracuseStep 1683539 = 2525309) B2525309
theorem B1421543 : Blo 746329 1421543 := bstep (se 1 (by rfl) ⟨1066157, by rfl⟩ : syracuseStep 1421543 = 2132315) B2132315
theorem B1683719 : Blo 746329 1683719 := bstep (se 1 (by rfl) ⟨1262789, by rfl⟩ : syracuseStep 1683719 = 2525579) B2525579
theorem B1684025 : Blo 746329 1684025 := bstep (se 2 (by rfl) ⟨631509, by rfl⟩ : syracuseStep 1684025 = 1263019) B1263019
theorem B1422127 : Blo 746329 1422127 := bstep (se 1 (by rfl) ⟨1066595, by rfl⟩ : syracuseStep 1422127 = 2133191) B2133191
theorem B4273033 : Blo 746329 4273033 := bstep (se 2 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 4273033 = 3204775) B3204775
theorem B5846057 : Blo 746329 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1684745 : Blo 746329 1684745 := bstep (se 2 (by rfl) ⟨631779, by rfl⟩ : syracuseStep 1684745 = 1263559) B1263559
theorem B1684799 : Blo 746329 1684799 := bstep (se 1 (by rfl) ⟨1263599, by rfl⟩ : syracuseStep 1684799 = 2527199) B2527199
theorem B1684907 : Blo 746329 1684907 := bstep (se 1 (by rfl) ⟨1263680, by rfl⟩ : syracuseStep 1684907 = 2527361) B2527361
theorem B5682797 : Blo 746329 5682797 := bstep (se 3 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 5682797 = 2131049) B2131049
theorem B10794667 : Blo 746329 10794667 := bstep (se 1 (by rfl) ⟨8096000, by rfl⟩ : syracuseStep 10794667 = 16192001) B16192001
theorem B40908503 : Blo 746329 40908503 := bstep (se 1 (by rfl) ⟨30681377, by rfl⟩ : syracuseStep 40908503 = 61362755) B61362755
theorem B1685231 : Blo 746329 1685231 := bstep (se 1 (by rfl) ⟨1263923, by rfl⟩ : syracuseStep 1685231 = 2527847) B2527847
theorem B1423183 : Blo 746329 1423183 := bstep (se 1 (by rfl) ⟨1067387, by rfl⟩ : syracuseStep 1423183 = 2134775) B2134775
theorem B1259435 : Blo 746329 1259435 := bstep (se 1 (by rfl) ⟨944576, by rfl⟩ : syracuseStep 1259435 = 1889153) B1889153
theorem B1685447 : Blo 746329 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B1685735 : Blo 746329 1685735 := bstep (se 1 (by rfl) ⟨1264301, by rfl⟩ : syracuseStep 1685735 = 2528603) B2528603
theorem B1685753 : Blo 746329 1685753 := bstep (se 2 (by rfl) ⟨632157, by rfl⟩ : syracuseStep 1685753 = 1264315) B1264315
theorem B6830351 : Blo 746329 6830351 := bstep (se 1 (by rfl) ⟨5122763, by rfl⟩ : syracuseStep 6830351 = 10245527) B10245527
theorem B1685807 : Blo 746329 1685807 := bstep (se 1 (by rfl) ⟨1264355, by rfl⟩ : syracuseStep 1685807 = 2528711) B2528711
theorem B1259975 : Blo 746329 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B4045319 : Blo 746329 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B1686023 : Blo 746329 1686023 := bstep (se 1 (by rfl) ⟨1264517, by rfl⟩ : syracuseStep 1686023 = 2529035) B2529035
theorem B5388889 : Blo 746329 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B3193465 : Blo 746329 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B1260191 : Blo 746329 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B1686203 : Blo 746329 1686203 := bstep (se 1 (by rfl) ⟨1264652, by rfl⟩ : syracuseStep 1686203 = 2529305) B2529305
theorem B1260265 : Blo 746329 1260265 := bstep (se 2 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 1260265 = 945199) B945199
theorem B7289767 : Blo 746329 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B3194099 : Blo 746329 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B1817929 : Blo 746329 1817929 := bstep (se 2 (by rfl) ⟨681723, by rfl⟩ : syracuseStep 1817929 = 1363447) B1363447
theorem B8076797 : Blo 746329 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B1687103 : Blo 746329 1687103 := bstep (se 1 (by rfl) ⟨1265327, by rfl⟩ : syracuseStep 1687103 = 2530655) B2530655
theorem B900839 : Blo 746329 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B1687463 : Blo 746329 1687463 := bstep (se 1 (by rfl) ⟨1265597, by rfl⟩ : syracuseStep 1687463 = 2531195) B2531195
theorem B3195071 : Blo 746329 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B1687787 : Blo 746329 1687787 := bstep (se 1 (by rfl) ⟨1265840, by rfl⟩ : syracuseStep 1687787 = 2531681) B2531681
theorem B3031559 : Blo 746329 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B9126685 : Blo 746329 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B4375547 : Blo 746329 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B3196027 : Blo 746329 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B1262783 : Blo 746329 1262783 := bstep (se 1 (by rfl) ⟨947087, by rfl⟩ : syracuseStep 1262783 = 1894175) B1894175
theorem B5686685 : Blo 746329 5686685 := bstep (se 3 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 5686685 = 2132507) B2132507
theorem B1263647 : Blo 746329 1263647 := bstep (se 1 (by rfl) ⟨947735, by rfl⟩ : syracuseStep 1263647 = 1895471) B1895471
theorem B1820969 : Blo 746329 1820969 := bstep (se 2 (by rfl) ⟨682863, by rfl⟩ : syracuseStep 1820969 = 1365727) B1365727
theorem B20531555 : Blo 746329 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B8505971 : Blo 746329 8505971 := bstep (se 1 (by rfl) ⟨6379478, by rfl⟩ : syracuseStep 8505971 = 12758957) B12758957
theorem B1264423 : Blo 746329 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B4803371 : Blo 746329 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B4869217 : Blo 746329 4869217 := bstep (se 2 (by rfl) ⟨1825956, by rfl⟩ : syracuseStep 4869217 = 3651913) B3651913
theorem B1264747 : Blo 746329 1264747 := bstep (se 1 (by rfl) ⟨948560, by rfl⟩ : syracuseStep 1264747 = 1897121) B1897121
theorem B4803731 : Blo 746329 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B3591533 : Blo 746329 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B1265017 : Blo 746329 1265017 := bstep (se 2 (by rfl) ⟨474381, by rfl⟩ : syracuseStep 1265017 = 948763) B948763
theorem B6082381 : Blo 746329 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B1265719 : Blo 746329 1265719 := bstep (se 1 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 1265719 = 1898579) B1898579
theorem B4804703 : Blo 746329 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B3199171 : Blo 746329 3199171 := bstep (se 1 (by rfl) ⟨2399378, by rfl⟩ : syracuseStep 3199171 = 4798757) B4798757
theorem B3789179 : Blo 746329 3789179 := bstep (se 1 (by rfl) ⟨2841884, by rfl⟩ : syracuseStep 3789179 = 5683769) B5683769
theorem B1266043 : Blo 746329 1266043 := bstep (se 1 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 1266043 = 1899065) B1899065
theorem B840091 : Blo 746329 840091 := bstep (se 1 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 840091 = 1260137) B1260137
theorem B3035663 : Blo 746329 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B6378385 : Blo 746329 6378385 := bstep (se 2 (by rfl) ⟨2391894, by rfl⟩ : syracuseStep 6378385 = 4783789) B4783789
theorem B840775 : Blo 746329 840775 := bstep (se 1 (by rfl) ⟨630581, by rfl⟩ : syracuseStep 840775 = 1261163) B1261163
theorem B6378659 : Blo 746329 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B1823951 : Blo 746329 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B840955 : Blo 746329 840955 := bstep (se 1 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 840955 = 1261433) B1261433
theorem B2839805 : Blo 746329 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B11523617 : Blo 746329 11523617 := bstep (se 2 (by rfl) ⟨4321356, by rfl⟩ : syracuseStep 11523617 = 8642713) B8642713
theorem B6838415 : Blo 746329 6838415 := bstep (se 1 (by rfl) ⟨5128811, by rfl⟩ : syracuseStep 6838415 = 10257623) B10257623
theorem B7199057 : Blo 746329 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B842143 : Blo 746329 842143 := bstep (se 1 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 842143 = 1263215) B1263215
theorem B842215 : Blo 746329 842215 := bstep (se 1 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 842215 = 1263323) B1263323
theorem B2841065 : Blo 746329 2841065 := bstep (se 2 (by rfl) ⟨1065399, by rfl⟩ : syracuseStep 2841065 = 2130799) B2130799
theorem B12802697 : Blo 746329 12802697 := bstep (se 2 (by rfl) ⟨4801011, by rfl⟩ : syracuseStep 12802697 = 9602023) B9602023
theorem B1891127 : Blo 746329 1891127 := bstep (se 1 (by rfl) ⟨1418345, by rfl⟩ : syracuseStep 1891127 = 2836691) B2836691
theorem B6380369 : Blo 746329 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B843079 : Blo 746329 843079 := bstep (se 1 (by rfl) ⟨632309, by rfl⟩ : syracuseStep 843079 = 1264619) B1264619
theorem B2842067 : Blo 746329 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B3202847 : Blo 746329 3202847 := bstep (se 1 (by rfl) ⟨2402135, by rfl⟩ : syracuseStep 3202847 = 4804271) B4804271
theorem B2842523 : Blo 746329 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B133325261 : Blo 746329 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B1893071 : Blo 746329 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B3203819 : Blo 746329 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B1598305 : Blo 746329 1598305 := bstep (se 2 (by rfl) ⟨599364, by rfl⟩ : syracuseStep 1598305 = 1198729) B1198729
theorem B746543 : Blo 746329 746543 := bstep (se 1 (by rfl) ⟨559907, by rfl⟩ : syracuseStep 746543 = 1119815) B1119815
theorem B746607 : Blo 746329 746607 := bstep (se 1 (by rfl) ⟨559955, by rfl⟩ : syracuseStep 746607 = 1119911) B1119911
theorem B746663 : Blo 746329 746663 := bstep (se 1 (by rfl) ⟨559997, by rfl⟩ : syracuseStep 746663 = 1119995) B1119995
theorem B746687 : Blo 746329 746687 := bstep (se 1 (by rfl) ⟨560015, by rfl⟩ : syracuseStep 746687 = 1120031) B1120031
theorem B746719 : Blo 746329 746719 := bstep (se 1 (by rfl) ⟨560039, by rfl⟩ : syracuseStep 746719 = 1120079) B1120079
theorem B746799 : Blo 746329 746799 := bstep (se 1 (by rfl) ⟨560099, by rfl⟩ : syracuseStep 746799 = 1120199) B1120199
theorem B1893689 : Blo 746329 1893689 := bstep (se 2 (by rfl) ⟨710133, by rfl⟩ : syracuseStep 1893689 = 1420267) B1420267
theorem B31974931 : Blo 746329 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B2844179 : Blo 746329 2844179 := bstep (se 1 (by rfl) ⟨2133134, by rfl⟩ : syracuseStep 2844179 = 4266269) B4266269
theorem B747035 : Blo 746329 747035 := bstep (se 1 (by rfl) ⟨560276, by rfl⟩ : syracuseStep 747035 = 1120553) B1120553
theorem B747039 : Blo 746329 747039 := bstep (se 1 (by rfl) ⟨560279, by rfl⟩ : syracuseStep 747039 = 1120559) B1120559
theorem B747199 : Blo 746329 747199 := bstep (se 1 (by rfl) ⟨560399, by rfl⟩ : syracuseStep 747199 = 1120799) B1120799
theorem B747455 : Blo 746329 747455 := bstep (se 1 (by rfl) ⟨560591, by rfl⟩ : syracuseStep 747455 = 1121183) B1121183
theorem B5695433 : Blo 746329 5695433 := bstep (se 2 (by rfl) ⟨2135787, by rfl⟩ : syracuseStep 5695433 = 4271575) B4271575
theorem B747487 : Blo 746329 747487 := bstep (se 1 (by rfl) ⟨560615, by rfl⟩ : syracuseStep 747487 = 1121231) B1121231
theorem B1894387 : Blo 746329 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B2844665 : Blo 746329 2844665 := bstep (se 2 (by rfl) ⟨1066749, by rfl⟩ : syracuseStep 2844665 = 2133499) B2133499
theorem B747547 : Blo 746329 747547 := bstep (se 1 (by rfl) ⟨560660, by rfl⟩ : syracuseStep 747547 = 1121321) B1121321
theorem B747551 : Blo 746329 747551 := bstep (se 1 (by rfl) ⟨560663, by rfl⟩ : syracuseStep 747551 = 1121327) B1121327
theorem B747567 : Blo 746329 747567 := bstep (se 1 (by rfl) ⟨560675, by rfl⟩ : syracuseStep 747567 = 1121351) B1121351
theorem B6056045 : Blo 746329 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B747743 : Blo 746329 747743 := bstep (se 1 (by rfl) ⟨560807, by rfl⟩ : syracuseStep 747743 = 1121615) B1121615
theorem B747803 : Blo 746329 747803 := bstep (se 1 (by rfl) ⟨560852, by rfl⟩ : syracuseStep 747803 = 1121705) B1121705
theorem B747903 : Blo 746329 747903 := bstep (se 1 (by rfl) ⟨560927, by rfl⟩ : syracuseStep 747903 = 1121855) B1121855
theorem B5401025 : Blo 746329 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B748079 : Blo 746329 748079 := bstep (se 1 (by rfl) ⟨561059, by rfl⟩ : syracuseStep 748079 = 1122119) B1122119
theorem B748135 : Blo 746329 748135 := bstep (se 1 (by rfl) ⟨561101, by rfl⟩ : syracuseStep 748135 = 1122203) B1122203
theorem B94563235 : Blo 746329 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B748511 : Blo 746329 748511 := bstep (se 1 (by rfl) ⟨561383, by rfl⟩ : syracuseStep 748511 = 1122767) B1122767
theorem B748539 : Blo 746329 748539 := bstep (se 1 (by rfl) ⟨561404, by rfl⟩ : syracuseStep 748539 = 1122809) B1122809
theorem B748607 : Blo 746329 748607 := bstep (se 1 (by rfl) ⟨561455, by rfl⟩ : syracuseStep 748607 = 1122911) B1122911
theorem B1797191 : Blo 746329 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B748927 : Blo 746329 748927 := bstep (se 1 (by rfl) ⟨561695, by rfl⟩ : syracuseStep 748927 = 1123391) B1123391
theorem B748955 : Blo 746329 748955 := bstep (se 1 (by rfl) ⟨561716, by rfl⟩ : syracuseStep 748955 = 1123433) B1123433
theorem B3239357 : Blo 746329 3239357 := bstep (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) B1214759
theorem B749023 : Blo 746329 749023 := bstep (se 1 (by rfl) ⟨561767, by rfl⟩ : syracuseStep 749023 = 1123535) B1123535
theorem B1896007 : Blo 746329 1896007 := bstep (se 1 (by rfl) ⟨1422005, by rfl⟩ : syracuseStep 1896007 = 2844011) B2844011
theorem B749159 : Blo 746329 749159 := bstep (se 1 (by rfl) ⟨561869, by rfl⟩ : syracuseStep 749159 = 1123739) B1123739
theorem B749307 : Blo 746329 749307 := bstep (se 1 (by rfl) ⟨561980, by rfl⟩ : syracuseStep 749307 = 1123961) B1123961
theorem B749375 : Blo 746329 749375 := bstep (se 1 (by rfl) ⟨562031, by rfl⟩ : syracuseStep 749375 = 1124063) B1124063
theorem B749439 : Blo 746329 749439 := bstep (se 1 (by rfl) ⟨562079, by rfl⟩ : syracuseStep 749439 = 1124159) B1124159
theorem B22998971 : Blo 746329 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B749551 : Blo 746329 749551 := bstep (se 1 (by rfl) ⟨562163, by rfl⟩ : syracuseStep 749551 = 1124327) B1124327
theorem B749563 : Blo 746329 749563 := bstep (se 1 (by rfl) ⟨562172, by rfl⟩ : syracuseStep 749563 = 1124345) B1124345
theorem B749631 : Blo 746329 749631 := bstep (se 1 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 749631 = 1124447) B1124447
theorem B749671 : Blo 746329 749671 := bstep (se 1 (by rfl) ⟨562253, by rfl⟩ : syracuseStep 749671 = 1124507) B1124507
theorem B749695 : Blo 746329 749695 := bstep (se 1 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 749695 = 1124543) B1124543
theorem B749723 : Blo 746329 749723 := bstep (se 1 (by rfl) ⟨562292, by rfl⟩ : syracuseStep 749723 = 1124585) B1124585
theorem B749927 : Blo 746329 749927 := bstep (se 1 (by rfl) ⟨562445, by rfl⟩ : syracuseStep 749927 = 1124891) B1124891
theorem B749979 : Blo 746329 749979 := bstep (se 1 (by rfl) ⟨562484, by rfl⟩ : syracuseStep 749979 = 1124969) B1124969
theorem B8516177 : Blo 746329 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1897465 : Blo 746329 1897465 := bstep (se 2 (by rfl) ⟨711549, by rfl⟩ : syracuseStep 1897465 = 1423099) B1423099
theorem B184251743 : Blo 746329 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B49903057 : Blo 746329 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B2127815 : Blo 746329 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B23066939 : Blo 746329 23066939 := bstep (se 1 (by rfl) ⟨17300204, by rfl⟩ : syracuseStep 23066939 = 34600409) B34600409
theorem B2521691 : Blo 746329 2521691 := bstep (se 1 (by rfl) ⟨1891268, by rfl⟩ : syracuseStep 2521691 = 3782537) B3782537
theorem B72940277 : Blo 746329 72940277 := bstep (se 5 (by rfl) ⟨3419075, by rfl⟩ : syracuseStep 72940277 = 6838151) B6838151
theorem B98466965 : Blo 746329 98466965 := bstep (se 6 (by rfl) ⟨2307819, by rfl⟩ : syracuseStep 98466965 = 4615639) B4615639
theorem B2522393 : Blo 746329 2522393 := bstep (se 2 (by rfl) ⟨945897, by rfl⟩ : syracuseStep 2522393 = 1891795) B1891795
theorem B2129341 : Blo 746329 2129341 := bstep (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) B798503
theorem B4849787 : Blo 746329 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B2130047 : Blo 746329 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B3604895 : Blo 746329 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B2917031 : Blo 746329 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B2851609 : Blo 746329 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B2131073 : Blo 746329 2131073 := bstep (se 2 (by rfl) ⟨799152, by rfl⟩ : syracuseStep 2131073 = 1598305) B1598305
theorem B4261187 : Blo 746329 4261187 := bstep (se 1 (by rfl) ⟨3195890, by rfl⟩ : syracuseStep 4261187 = 6391781) B6391781
theorem B4261369 : Blo 746329 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1213979 : Blo 746329 1213979 := bstep (se 1 (by rfl) ⟨910484, by rfl⟩ : syracuseStep 1213979 = 1820969) B1820969
theorem B12977863 : Blo 746329 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B5670647 : Blo 746329 5670647 := bstep (se 1 (by rfl) ⟨4252985, by rfl⟩ : syracuseStep 5670647 = 8505971) B8505971
theorem B2394355 : Blo 746329 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B4786559 : Blo 746329 4786559 := bstep (se 1 (by rfl) ⟨3589919, by rfl⟩ : syracuseStep 4786559 = 7179839) B7179839
theorem B4262327 : Blo 746329 4262327 := bstep (se 1 (by rfl) ⟨3196745, by rfl⟩ : syracuseStep 4262327 = 6393491) B6393491
theorem B2525849 : Blo 746329 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B2526119 : Blo 746329 2526119 := bstep (se 1 (by rfl) ⟨1894589, by rfl⟩ : syracuseStep 2526119 = 3789179) B3789179
theorem B3411197 : Blo 746329 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B9571679 : Blo 746329 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B1215967 : Blo 746329 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B4558943 : Blo 746329 4558943 := bstep (se 1 (by rfl) ⟨3419207, by rfl⟩ : syracuseStep 4558943 = 6838415) B6838415
theorem B5771425 : Blo 746329 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B2528009 : Blo 746329 2528009 := bstep (se 2 (by rfl) ⟨948003, by rfl⟩ : syracuseStep 2528009 = 1896007) B1896007
theorem B2135231 : Blo 746329 2135231 := bstep (se 1 (by rfl) ⟨1601423, by rfl⟩ : syracuseStep 2135231 = 3202847) B3202847
theorem B1119551 : Blo 746329 1119551 := bstep (se 1 (by rfl) ⟨839663, by rfl⟩ : syracuseStep 1119551 = 1679327) B1679327
theorem B1119743 : Blo 746329 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B4265561 : Blo 746329 4265561 := bstep (se 2 (by rfl) ⟨1599585, by rfl⟩ : syracuseStep 4265561 = 3199171) B3199171
theorem B1119851 : Blo 746329 1119851 := bstep (se 1 (by rfl) ⟨839888, by rfl⟩ : syracuseStep 1119851 = 1679777) B1679777
theorem B2135879 : Blo 746329 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B1120121 : Blo 746329 1120121 := bstep (se 2 (by rfl) ⟨420045, by rfl⟩ : syracuseStep 1120121 = 840091) B840091
theorem B1120367 : Blo 746329 1120367 := bstep (se 1 (by rfl) ⟨840275, by rfl⟩ : syracuseStep 1120367 = 1680551) B1680551
theorem B1120439 : Blo 746329 1120439 := bstep (se 1 (by rfl) ⟨840329, by rfl⟩ : syracuseStep 1120439 = 1680659) B1680659
theorem B1120859 : Blo 746329 1120859 := bstep (se 1 (by rfl) ⟨840644, by rfl⟩ : syracuseStep 1120859 = 1681289) B1681289
theorem B1120871 : Blo 746329 1120871 := bstep (se 1 (by rfl) ⟨840653, by rfl⟩ : syracuseStep 1120871 = 1681307) B1681307
theorem B1120895 : Blo 746329 1120895 := bstep (se 1 (by rfl) ⟨840671, by rfl⟩ : syracuseStep 1120895 = 1681343) B1681343
theorem B2529953 : Blo 746329 2529953 := bstep (se 2 (by rfl) ⟨948732, by rfl⟩ : syracuseStep 2529953 = 1897465) B1897465
theorem B1121003 : Blo 746329 1121003 := bstep (se 1 (by rfl) ⟨840752, by rfl⟩ : syracuseStep 1121003 = 1681505) B1681505
theorem B4037363 : Blo 746329 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1121033 : Blo 746329 1121033 := bstep (se 2 (by rfl) ⟨420387, by rfl⟩ : syracuseStep 1121033 = 840775) B840775
theorem B1121273 : Blo 746329 1121273 := bstep (se 2 (by rfl) ⟨420477, by rfl⟩ : syracuseStep 1121273 = 840955) B840955
theorem B14392889 : Blo 746329 14392889 := bstep (se 2 (by rfl) ⟨5397333, by rfl⟩ : syracuseStep 14392889 = 10794667) B10794667
theorem B1121903 : Blo 746329 1121903 := bstep (se 1 (by rfl) ⟨841427, by rfl⟩ : syracuseStep 1121903 = 1682855) B1682855
theorem B1122023 : Blo 746329 1122023 := bstep (se 1 (by rfl) ⟨841517, by rfl⟩ : syracuseStep 1122023 = 1683035) B1683035
theorem B1384271 : Blo 746329 1384271 := bstep (se 1 (by rfl) ⟨1038203, by rfl⟩ : syracuseStep 1384271 = 2076407) B2076407
theorem B1122299 : Blo 746329 1122299 := bstep (se 1 (by rfl) ⟨841724, by rfl⟩ : syracuseStep 1122299 = 1683449) B1683449
theorem B1122359 : Blo 746329 1122359 := bstep (se 1 (by rfl) ⟨841769, by rfl⟩ : syracuseStep 1122359 = 1683539) B1683539
theorem B170532965 : Blo 746329 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B1122479 : Blo 746329 1122479 := bstep (se 1 (by rfl) ⟨841859, by rfl⟩ : syracuseStep 1122479 = 1683719) B1683719
theorem B1122683 : Blo 746329 1122683 := bstep (se 1 (by rfl) ⟨842012, by rfl⟩ : syracuseStep 1122683 = 1684025) B1684025
theorem B5677451 : Blo 746329 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B1122857 : Blo 746329 1122857 := bstep (se 2 (by rfl) ⟨421071, by rfl⟩ : syracuseStep 1122857 = 842143) B842143
theorem B1122953 : Blo 746329 1122953 := bstep (se 2 (by rfl) ⟨421107, by rfl⟩ : syracuseStep 1122953 = 842215) B842215
theorem B7185185 : Blo 746329 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B1123163 : Blo 746329 1123163 := bstep (se 1 (by rfl) ⟨842372, by rfl⟩ : syracuseStep 1123163 = 1684745) B1684745
theorem B1123199 : Blo 746329 1123199 := bstep (se 1 (by rfl) ⟨842399, by rfl⟩ : syracuseStep 1123199 = 1684799) B1684799
theorem B1123271 : Blo 746329 1123271 := bstep (se 1 (by rfl) ⟨842453, by rfl⟩ : syracuseStep 1123271 = 1684907) B1684907
theorem B1680353 : Blo 746329 1680353 := bstep (se 2 (by rfl) ⟨630132, by rfl⟩ : syracuseStep 1680353 = 1260265) B1260265
theorem B27272335 : Blo 746329 27272335 := bstep (se 1 (by rfl) ⟨20454251, by rfl⟩ : syracuseStep 27272335 = 40908503) B40908503
theorem B1123487 : Blo 746329 1123487 := bstep (se 1 (by rfl) ⟨842615, by rfl⟩ : syracuseStep 1123487 = 1685231) B1685231
theorem B1418543 : Blo 746329 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B1123631 : Blo 746329 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B1123823 : Blo 746329 1123823 := bstep (se 1 (by rfl) ⟨842867, by rfl⟩ : syracuseStep 1123823 = 1685735) B1685735
theorem B1123835 : Blo 746329 1123835 := bstep (se 1 (by rfl) ⟨842876, by rfl⟩ : syracuseStep 1123835 = 1685753) B1685753
theorem B1123871 : Blo 746329 1123871 := bstep (se 1 (by rfl) ⟨842903, by rfl⟩ : syracuseStep 1123871 = 1685807) B1685807
theorem B15377959 : Blo 746329 15377959 := bstep (se 1 (by rfl) ⟨11533469, by rfl⟩ : syracuseStep 15377959 = 23066939) B23066939
theorem B2696879 : Blo 746329 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B1124015 : Blo 746329 1124015 := bstep (se 1 (by rfl) ⟨843011, by rfl⟩ : syracuseStep 1124015 = 1686023) B1686023
theorem B1681127 : Blo 746329 1681127 := bstep (se 1 (by rfl) ⟨1260845, by rfl⟩ : syracuseStep 1681127 = 2521691) B2521691
theorem B1124105 : Blo 746329 1124105 := bstep (se 2 (by rfl) ⟨421539, by rfl⟩ : syracuseStep 1124105 = 843079) B843079
theorem B1124135 : Blo 746329 1124135 := bstep (se 1 (by rfl) ⟨843101, by rfl⟩ : syracuseStep 1124135 = 1686203) B1686203
theorem B2402237 : Blo 746329 2402237 := bstep (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) B900839
theorem B65644643 : Blo 746329 65644643 := bstep (se 1 (by rfl) ⟨49233482, by rfl⟩ : syracuseStep 65644643 = 98466965) B98466965
theorem B1681595 : Blo 746329 1681595 := bstep (se 1 (by rfl) ⟨1261196, by rfl⟩ : syracuseStep 1681595 = 2522393) B2522393
theorem B5384531 : Blo 746329 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B1124735 : Blo 746329 1124735 := bstep (se 1 (by rfl) ⟨843551, by rfl⟩ : syracuseStep 1124735 = 1687103) B1687103
theorem B3778973 : Blo 746329 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B1124975 : Blo 746329 1124975 := bstep (se 1 (by rfl) ⟨843731, by rfl⟩ : syracuseStep 1124975 = 1687463) B1687463
theorem B1125191 : Blo 746329 1125191 := bstep (se 1 (by rfl) ⟨843893, by rfl⟩ : syracuseStep 1125191 = 1687787) B1687787
theorem B1682495 : Blo 746329 1682495 := bstep (se 1 (by rfl) ⟨1261871, by rfl⟩ : syracuseStep 1682495 = 2523743) B2523743
theorem B12168913 : Blo 746329 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B1683323 : Blo 746329 1683323 := bstep (se 1 (by rfl) ⟨1262492, by rfl⟩ : syracuseStep 1683323 = 2524985) B2524985
theorem B9613505 : Blo 746329 9613505 := bstep (se 2 (by rfl) ⟨3605064, by rfl⟩ : syracuseStep 9613505 = 7210129) B7210129
theorem B3781079 : Blo 746329 3781079 := bstep (se 1 (by rfl) ⟨2835809, by rfl⟩ : syracuseStep 3781079 = 5671619) B5671619
theorem B6402989 : Blo 746329 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B1685267 : Blo 746329 1685267 := bstep (se 1 (by rfl) ⟨1263950, by rfl⟩ : syracuseStep 1685267 = 2527901) B2527901
theorem B5683283 : Blo 746329 5683283 := bstep (se 1 (by rfl) ⟨4262462, by rfl⟩ : syracuseStep 5683283 = 8524925) B8524925
theorem B1685627 : Blo 746329 1685627 := bstep (se 1 (by rfl) ⟨1264220, by rfl⟩ : syracuseStep 1685627 = 2528441) B2528441
theorem B15382727 : Blo 746329 15382727 := bstep (se 1 (by rfl) ⟨11537045, by rfl⟩ : syracuseStep 15382727 = 23074091) B23074091
theorem B7682411 : Blo 746329 7682411 := bstep (se 1 (by rfl) ⟨5761808, by rfl⟩ : syracuseStep 7682411 = 11523617) B11523617
theorem B1685897 : Blo 746329 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B30784211 : Blo 746329 30784211 := bstep (se 1 (by rfl) ⟨23088158, by rfl⟩ : syracuseStep 30784211 = 46176317) B46176317
theorem B1686329 : Blo 746329 1686329 := bstep (se 2 (by rfl) ⟨632373, by rfl⟩ : syracuseStep 1686329 = 1264747) B1264747
theorem B8535131 : Blo 746329 8535131 := bstep (se 1 (by rfl) ⟨6401348, by rfl⟩ : syracuseStep 8535131 = 12802697) B12802697
theorem B1686689 : Blo 746329 1686689 := bstep (se 2 (by rfl) ⟨632508, by rfl⟩ : syracuseStep 1686689 = 1265017) B1265017
theorem B1260751 : Blo 746329 1260751 := bstep (se 1 (by rfl) ⟨945563, by rfl⟩ : syracuseStep 1260751 = 1891127) B1891127
theorem B13647113 : Blo 746329 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B1686959 : Blo 746329 1686959 := bstep (se 1 (by rfl) ⟨1265219, by rfl⟩ : syracuseStep 1686959 = 2530439) B2530439
theorem B6405587 : Blo 746329 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B1097371 : Blo 746329 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B8109841 : Blo 746329 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B1687625 : Blo 746329 1687625 := bstep (se 2 (by rfl) ⟨632859, by rfl⟩ : syracuseStep 1687625 = 1265719) B1265719
theorem B88883507 : Blo 746329 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B1262047 : Blo 746329 1262047 := bstep (se 1 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 1262047 = 1893071) B1893071
theorem B1688039 : Blo 746329 1688039 := bstep (se 1 (by rfl) ⟨1266029, by rfl⟩ : syracuseStep 1688039 = 2532059) B2532059
theorem B1688057 : Blo 746329 1688057 := bstep (se 2 (by rfl) ⟨633021, by rfl⟩ : syracuseStep 1688057 = 1266043) B1266043
theorem B25969157 : Blo 746329 25969157 := bstep (se 4 (by rfl) ⟨2434608, by rfl⟩ : syracuseStep 25969157 = 4869217) B4869217
theorem B1688147 : Blo 746329 1688147 := bstep (se 1 (by rfl) ⟨1266110, by rfl⟩ : syracuseStep 1688147 = 2532221) B2532221
theorem B1262459 : Blo 746329 1262459 := bstep (se 1 (by rfl) ⟨946844, by rfl⟩ : syracuseStep 1262459 = 1893689) B1893689
theorem B8504513 : Blo 746329 8504513 := bstep (se 2 (by rfl) ⟨3189192, by rfl⟩ : syracuseStep 8504513 = 6378385) B6378385
theorem B66537409 : Blo 746329 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B1198127 : Blo 746329 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B122834495 : Blo 746329 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B3788531 : Blo 746329 3788531 := bstep (se 1 (by rfl) ⟨2841398, by rfl⟩ : syracuseStep 3788531 = 5682797) B5682797
theorem B8638285 : Blo 746329 8638285 := bstep (se 3 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 8638285 = 3239357) B3239357
theorem B9719689 : Blo 746329 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B839623 : Blo 746329 839623 := bstep (se 1 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 839623 = 1259435) B1259435
theorem B839983 : Blo 746329 839983 := bstep (se 1 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 839983 = 1259975) B1259975
theorem B840127 : Blo 746329 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B2839121 : Blo 746329 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B5395835 : Blo 746329 5395835 := bstep (se 1 (by rfl) ⟨4046876, by rfl⟩ : syracuseStep 5395835 = 8093753) B8093753
theorem B13686245 : Blo 746329 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B2021039 : Blo 746329 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B841855 : Blo 746329 841855 := bstep (se 1 (by rfl) ⟨631391, by rfl⟩ : syracuseStep 841855 = 1262783) B1262783
theorem B3791123 : Blo 746329 3791123 := bstep (se 1 (by rfl) ⟨2843342, by rfl⟩ : syracuseStep 3791123 = 5686685) B5686685
theorem B2841095 : Blo 746329 2841095 := bstep (se 1 (by rfl) ⟨2130821, by rfl⟩ : syracuseStep 2841095 = 4261643) B4261643
theorem B842431 : Blo 746329 842431 := bstep (se 1 (by rfl) ⟨631823, by rfl⟩ : syracuseStep 842431 = 1263647) B1263647
theorem B4807421 : Blo 746329 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B2186041 : Blo 746329 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B13687703 : Blo 746329 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B3202247 : Blo 746329 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B3202487 : Blo 746329 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B8084929 : Blo 746329 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B10510235 : Blo 746329 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B3203135 : Blo 746329 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B4546705 : Blo 746329 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B2023775 : Blo 746329 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B4252439 : Blo 746329 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B1893203 : Blo 746329 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B746399 : Blo 746329 746399 := bstep (se 1 (by rfl) ⟨559799, by rfl⟩ : syracuseStep 746399 = 1119599) B1119599
theorem B746479 : Blo 746329 746479 := bstep (se 1 (by rfl) ⟨559859, by rfl⟩ : syracuseStep 746479 = 1119719) B1119719
theorem B1795067 : Blo 746329 1795067 := bstep (se 1 (by rfl) ⟨1346300, by rfl⟩ : syracuseStep 1795067 = 2692601) B2692601
theorem B746587 : Blo 746329 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B746599 : Blo 746329 746599 := bstep (se 1 (by rfl) ⟨559949, by rfl⟩ : syracuseStep 746599 = 1119899) B1119899
theorem B126084313 : Blo 746329 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B746727 : Blo 746329 746727 := bstep (se 1 (by rfl) ⟨560045, by rfl⟩ : syracuseStep 746727 = 1120091) B1120091
theorem B746983 : Blo 746329 746983 := bstep (se 1 (by rfl) ⟨560237, by rfl⟩ : syracuseStep 746983 = 1120475) B1120475
theorem B747163 : Blo 746329 747163 := bstep (se 1 (by rfl) ⟨560372, by rfl⟩ : syracuseStep 747163 = 1120745) B1120745
theorem B1894043 : Blo 746329 1894043 := bstep (se 1 (by rfl) ⟨1420532, by rfl⟩ : syracuseStep 1894043 = 2841065) B2841065
theorem B4253579 : Blo 746329 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B747423 : Blo 746329 747423 := bstep (se 1 (by rfl) ⟨560567, by rfl⟩ : syracuseStep 747423 = 1121135) B1121135
theorem B747431 : Blo 746329 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B1894711 : Blo 746329 1894711 := bstep (se 1 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 1894711 = 2842067) B2842067
theorem B748007 : Blo 746329 748007 := bstep (se 1 (by rfl) ⟨561005, by rfl⟩ : syracuseStep 748007 = 1122011) B1122011
theorem B1895015 : Blo 746329 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B4254353 : Blo 746329 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B748187 : Blo 746329 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B748655 : Blo 746329 748655 := bstep (se 1 (by rfl) ⟨561491, by rfl⟩ : syracuseStep 748655 = 1122983) B1122983
theorem B748735 : Blo 746329 748735 := bstep (se 1 (by rfl) ⟨561551, by rfl⟩ : syracuseStep 748735 = 1123103) B1123103
theorem B748751 : Blo 746329 748751 := bstep (se 1 (by rfl) ⟨561563, by rfl⟩ : syracuseStep 748751 = 1123127) B1123127
theorem B748871 : Blo 746329 748871 := bstep (se 1 (by rfl) ⟨561653, by rfl⟩ : syracuseStep 748871 = 1123307) B1123307
theorem B19197485 : Blo 746329 19197485 := bstep (se 3 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 19197485 = 7199057) B7199057
theorem B1896119 : Blo 746329 1896119 := bstep (se 1 (by rfl) ⟨1422089, by rfl⟩ : syracuseStep 1896119 = 2844179) B2844179
theorem B1896169 : Blo 746329 1896169 := bstep (se 2 (by rfl) ⟨711063, by rfl⟩ : syracuseStep 1896169 = 1422127) B1422127
theorem B5697377 : Blo 746329 5697377 := bstep (se 2 (by rfl) ⟨2136516, by rfl⟩ : syracuseStep 5697377 = 4273033) B4273033
theorem B3796955 : Blo 746329 3796955 := bstep (se 1 (by rfl) ⟨2847716, by rfl⟩ : syracuseStep 3796955 = 5695433) B5695433
theorem B946171 : Blo 746329 946171 := bstep (se 1 (by rfl) ⟨709628, by rfl⟩ : syracuseStep 946171 = 1419257) B1419257
theorem B1896443 : Blo 746329 1896443 := bstep (se 1 (by rfl) ⟨1422332, by rfl⟩ : syracuseStep 1896443 = 2844665) B2844665
theorem B2125855 : Blo 746329 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B749599 : Blo 746329 749599 := bstep (se 1 (by rfl) ⟨562199, by rfl⟩ : syracuseStep 749599 = 1124399) B1124399
theorem B749775 : Blo 746329 749775 := bstep (se 1 (by rfl) ⟨562331, by rfl⟩ : syracuseStep 749775 = 1124663) B1124663
theorem B3600683 : Blo 746329 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B749895 : Blo 746329 749895 := bstep (se 1 (by rfl) ⟨562421, by rfl⟩ : syracuseStep 749895 = 1124843) B1124843
theorem B9695621 : Blo 746329 9695621 := bstep (se 4 (by rfl) ⟨908964, by rfl⟩ : syracuseStep 9695621 = 1817929) B1817929
theorem B7172995 : Blo 746329 7172995 := bstep (se 1 (by rfl) ⟨5379746, by rfl⟩ : syracuseStep 7172995 = 10759493) B10759493
theorem B3830843 : Blo 746329 3830843 := bstep (se 1 (by rfl) ⟨2873132, by rfl⟩ : syracuseStep 3830843 = 5746265) B5746265
theorem B1897577 : Blo 746329 1897577 := bstep (se 2 (by rfl) ⟨711591, by rfl⟩ : syracuseStep 1897577 = 1423183) B1423183
theorem B15332647 : Blo 746329 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B947695 : Blo 746329 947695 := bstep (se 1 (by rfl) ⟨710771, by rfl⟩ : syracuseStep 947695 = 1421543) B1421543
theorem B2848553 : Blo 746329 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B3897371 : Blo 746329 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B4257953 : Blo 746329 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B4553567 : Blo 746329 4553567 := bstep (se 1 (by rfl) ⟨3415175, by rfl⟩ : syracuseStep 4553567 = 6830351) B6830351
theorem B48626851 : Blo 746329 48626851 := bstep (se 1 (by rfl) ⟨36470138, by rfl⟩ : syracuseStep 48626851 = 72940277) B72940277
theorem B2129399 : Blo 746329 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B6062273 : Blo 746329 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B5669675 : Blo 746329 5669675 := bstep (se 1 (by rfl) ⟨4252256, by rfl⟩ : syracuseStep 5669675 = 8504513) B8504513
theorem B3802145 : Blo 746329 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B81889663 : Blo 746329 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B2525687 : Blo 746329 2525687 := bstep (se 1 (by rfl) ⟨1894265, by rfl⟩ : syracuseStep 2525687 = 3788531) B3788531
theorem B2526281 : Blo 746329 2526281 := bstep (se 2 (by rfl) ⟨947355, by rfl⟩ : syracuseStep 2526281 = 1894711) B1894711
theorem B1347359 : Blo 746329 1347359 := bstep (se 1 (by rfl) ⟨1010519, by rfl⟩ : syracuseStep 1347359 = 2021039) B2021039
theorem B2527415 : Blo 746329 2527415 := bstep (se 1 (by rfl) ⟨1895561, by rfl⟩ : syracuseStep 2527415 = 3791123) B3791123
theorem B2691575 : Blo 746329 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B2134831 : Blo 746329 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B16225217 : Blo 746329 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B2134991 : Blo 746329 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B2528225 : Blo 746329 2528225 := bstep (se 2 (by rfl) ⟨948084, by rfl⟩ : syracuseStep 2528225 = 1896169) B1896169
theorem B1119497 : Blo 746329 1119497 := bstep (se 2 (by rfl) ⟨419811, by rfl⟩ : syracuseStep 1119497 = 839623) B839623
theorem B2135423 : Blo 746329 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B1349183 : Blo 746329 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B12949109 : Blo 746329 12949109 := bstep (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) B1213979
theorem B1119977 : Blo 746329 1119977 := bstep (se 2 (by rfl) ⟨419991, by rfl⟩ : syracuseStep 1119977 = 839983) B839983
theorem B4790123 : Blo 746329 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B1120169 : Blo 746329 1120169 := bstep (se 2 (by rfl) ⟨420063, by rfl⟩ : syracuseStep 1120169 = 840127) B840127
theorem B1120235 : Blo 746329 1120235 := bstep (se 1 (by rfl) ⟨840176, by rfl⟩ : syracuseStep 1120235 = 1680353) B1680353
theorem B20486429 : Blo 746329 20486429 := bstep (se 3 (by rfl) ⟨3841205, by rfl⟩ : syracuseStep 20486429 = 7682411) B7682411
theorem B1120751 : Blo 746329 1120751 := bstep (se 1 (by rfl) ⟨840563, by rfl⟩ : syracuseStep 1120751 = 1681127) B1681127
theorem B1121063 : Blo 746329 1121063 := bstep (se 1 (by rfl) ⟨840797, by rfl⟩ : syracuseStep 1121063 = 1681595) B1681595
theorem B1121663 : Blo 746329 1121663 := bstep (se 1 (by rfl) ⟨841247, by rfl⟩ : syracuseStep 1121663 = 1682495) B1682495
theorem B1122215 : Blo 746329 1122215 := bstep (se 1 (by rfl) ⟨841661, by rfl⟩ : syracuseStep 1122215 = 1683323) B1683323
theorem B2531303 : Blo 746329 2531303 := bstep (se 1 (by rfl) ⟨1898477, by rfl⟩ : syracuseStep 2531303 = 3796955) B3796955
theorem B1122473 : Blo 746329 1122473 := bstep (se 2 (by rfl) ⟨420927, by rfl⟩ : syracuseStep 1122473 = 841855) B841855
theorem B2400455 : Blo 746329 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B6463747 : Blo 746329 6463747 := bstep (se 1 (by rfl) ⟨4847810, by rfl⟩ : syracuseStep 6463747 = 9695621) B9695621
theorem B4268659 : Blo 746329 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B1123241 : Blo 746329 1123241 := bstep (se 2 (by rfl) ⟨421215, by rfl⟩ : syracuseStep 1123241 = 842431) B842431
theorem B69215269 : Blo 746329 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B1123511 : Blo 746329 1123511 := bstep (se 1 (by rfl) ⟨842633, by rfl⟩ : syracuseStep 1123511 = 1685267) B1685267
theorem B2598247 : Blo 746329 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B1123751 : Blo 746329 1123751 := bstep (se 1 (by rfl) ⟨842813, by rfl⟩ : syracuseStep 1123751 = 1685627) B1685627
theorem B1123931 : Blo 746329 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B1681001 : Blo 746329 1681001 := bstep (se 2 (by rfl) ⟨630375, by rfl⟩ : syracuseStep 1681001 = 1260751) B1260751
theorem B20522807 : Blo 746329 20522807 := bstep (se 1 (by rfl) ⟨15392105, by rfl⟩ : syracuseStep 20522807 = 30784211) B30784211
theorem B1124219 : Blo 746329 1124219 := bstep (se 1 (by rfl) ⟨843164, by rfl⟩ : syracuseStep 1124219 = 1686329) B1686329
theorem B1124459 : Blo 746329 1124459 := bstep (se 1 (by rfl) ⟨843344, by rfl⟩ : syracuseStep 1124459 = 1686689) B1686689
theorem B1124639 : Blo 746329 1124639 := bstep (se 1 (by rfl) ⟨843479, by rfl⟩ : syracuseStep 1124639 = 1686959) B1686959
theorem B4270391 : Blo 746329 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B1419599 : Blo 746329 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B1125083 : Blo 746329 1125083 := bstep (se 1 (by rfl) ⟨843812, by rfl⟩ : syracuseStep 1125083 = 1687625) B1687625
theorem B1420031 : Blo 746329 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B2403263 : Blo 746329 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B1125359 : Blo 746329 1125359 := bstep (se 1 (by rfl) ⟨844019, by rfl⟩ : syracuseStep 1125359 = 1688039) B1688039
theorem B1125371 : Blo 746329 1125371 := bstep (se 1 (by rfl) ⟨844028, by rfl⟩ : syracuseStep 1125371 = 1688057) B1688057
theorem B17312771 : Blo 746329 17312771 := bstep (se 1 (by rfl) ⟨12984578, by rfl⟩ : syracuseStep 17312771 = 25969157) B25969157
theorem B1125431 : Blo 746329 1125431 := bstep (se 1 (by rfl) ⟨844073, by rfl⟩ : syracuseStep 1125431 = 1688147) B1688147
theorem B1682729 : Blo 746329 1682729 := bstep (se 2 (by rfl) ⟨631023, by rfl⟩ : syracuseStep 1682729 = 1262047) B1262047
theorem B1420715 : Blo 746329 1420715 := bstep (se 1 (by rfl) ⟨1065536, by rfl⟩ : syracuseStep 1420715 = 2131073) B2131073
theorem B237022685 : Blo 746329 237022685 := bstep (se 3 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 237022685 = 88883507) B88883507
theorem B3780431 : Blo 746329 3780431 := bstep (se 1 (by rfl) ⟨2835323, by rfl⟩ : syracuseStep 3780431 = 5670647) B5670647
theorem B798751 : Blo 746329 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B3191039 : Blo 746329 3191039 := bstep (se 1 (by rfl) ⟨2393279, by rfl⟩ : syracuseStep 3191039 = 4786559) B4786559
theorem B168112417 : Blo 746329 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B1683899 : Blo 746329 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B7778749 : Blo 746329 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B1684079 : Blo 746329 1684079 := bstep (se 1 (by rfl) ⟨1263059, by rfl⟩ : syracuseStep 1684079 = 2526119) B2526119
theorem B5681825 : Blo 746329 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B2274131 : Blo 746329 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B88716545 : Blo 746329 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B3192473 : Blo 746329 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B1685339 : Blo 746329 1685339 := bstep (se 1 (by rfl) ⟨1264004, by rfl⟩ : syracuseStep 1685339 = 2528009) B2528009
theorem B59062229 : Blo 746329 59062229 := bstep (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) B1384271
theorem B1423487 : Blo 746329 1423487 := bstep (se 1 (by rfl) ⟨1067615, by rfl⟩ : syracuseStep 1423487 = 2135231) B2135231
theorem B9124163 : Blo 746329 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B1423919 : Blo 746329 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B1686635 : Blo 746329 1686635 := bstep (se 1 (by rfl) ⟨1264976, by rfl⟩ : syracuseStep 1686635 = 2529953) B2529953
theorem B9125135 : Blo 746329 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B1621289 : Blo 746329 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B11517713 : Blo 746329 11517713 := bstep (se 2 (by rfl) ⟨4319142, by rfl⟩ : syracuseStep 11517713 = 8638285) B8638285
theorem B6405965 : Blo 746329 6405965 := bstep (se 3 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 6405965 = 2402237) B2402237
theorem B12959585 : Blo 746329 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B1261561 : Blo 746329 1261561 := bstep (se 2 (by rfl) ⟨473085, by rfl⟩ : syracuseStep 1261561 = 946171) B946171
theorem B2834473 : Blo 746329 2834473 := bstep (se 2 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 2834473 = 2125855) B2125855
theorem B113688643 : Blo 746329 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B3784967 : Blo 746329 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B2834959 : Blo 746329 2834959 := bstep (se 1 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 2834959 = 4252439) B4252439
theorem B1262135 : Blo 746329 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B1196711 : Blo 746329 1196711 := bstep (se 1 (by rfl) ⟨897533, by rfl⟩ : syracuseStep 1196711 = 1795067) B1795067
theorem B1262695 : Blo 746329 1262695 := bstep (se 1 (by rfl) ⟨947021, by rfl⟩ : syracuseStep 1262695 = 1894043) B1894043
theorem B2835719 : Blo 746329 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B43763095 : Blo 746329 43763095 := bstep (se 1 (by rfl) ⟨32822321, by rfl⟩ : syracuseStep 43763095 = 65644643) B65644643
theorem B3589687 : Blo 746329 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B1263343 : Blo 746329 1263343 := bstep (se 1 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 1263343 = 1895015) B1895015
theorem B2836235 : Blo 746329 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B1263593 : Blo 746329 1263593 := bstep (se 2 (by rfl) ⟨473847, by rfl⟩ : syracuseStep 1263593 = 947695) B947695
theorem B12798323 : Blo 746329 12798323 := bstep (se 1 (by rfl) ⟨9598742, by rfl⟩ : syracuseStep 12798323 = 19197485) B19197485
theorem B1264079 : Blo 746329 1264079 := bstep (se 1 (by rfl) ⟨948059, by rfl⟩ : syracuseStep 1264079 = 1896119) B1896119
theorem B1264295 : Blo 746329 1264295 := bstep (se 1 (by rfl) ⟨948221, by rfl⟩ : syracuseStep 1264295 = 1896443) B1896443
theorem B6409003 : Blo 746329 6409003 := bstep (se 1 (by rfl) ⟨4806752, by rfl⟩ : syracuseStep 6409003 = 9613505) B9613505
theorem B1265051 : Blo 746329 1265051 := bstep (se 1 (by rfl) ⟨948788, by rfl⟩ : syracuseStep 1265051 = 1897577) B1897577
theorem B5852645 : Blo 746329 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B3788855 : Blo 746329 3788855 := bstep (se 1 (by rfl) ⟨2841641, by rfl⟩ : syracuseStep 3788855 = 5683283) B5683283
theorem B2838635 : Blo 746329 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B64835801 : Blo 746329 64835801 := bstep (se 2 (by rfl) ⟨24313425, by rfl⟩ : syracuseStep 64835801 = 48626851) B48626851
theorem B3035711 : Blo 746329 3035711 := bstep (se 1 (by rfl) ⟨2276783, by rfl⟩ : syracuseStep 3035711 = 4553567) B4553567
theorem B5690087 : Blo 746329 5690087 := bstep (se 1 (by rfl) ⟨4267565, by rfl⟩ : syracuseStep 5690087 = 8535131) B8535131
theorem B9098075 : Blo 746329 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B3233191 : Blo 746329 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B841639 : Blo 746329 841639 := bstep (se 1 (by rfl) ⟨631229, by rfl⟩ : syracuseStep 841639 = 1262459) B1262459
theorem B2840791 : Blo 746329 2840791 := bstep (se 1 (by rfl) ⟨2130593, by rfl⟩ : syracuseStep 2840791 = 4261187) B4261187
theorem B36363113 : Blo 746329 36363113 := bstep (se 2 (by rfl) ⟨13636167, by rfl⟩ : syracuseStep 36363113 = 27272335) B27272335
theorem B2841551 : Blo 746329 2841551 := bstep (se 1 (by rfl) ⟨2131163, by rfl⟩ : syracuseStep 2841551 = 4262327) B4262327
theorem B20503945 : Blo 746329 20503945 := bstep (se 2 (by rfl) ⟨7688979, by rfl⟩ : syracuseStep 20503945 = 15377959) B15377959
theorem B6381119 : Blo 746329 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B3039295 : Blo 746329 3039295 := bstep (se 1 (by rfl) ⟨2279471, by rfl⟩ : syracuseStep 3039295 = 4558943) B4558943
theorem B1892747 : Blo 746329 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B746367 : Blo 746329 746367 := bstep (se 1 (by rfl) ⟨559775, by rfl⟩ : syracuseStep 746367 = 1119551) B1119551
theorem B3597223 : Blo 746329 3597223 := bstep (se 1 (by rfl) ⟨2697917, by rfl⟩ : syracuseStep 3597223 = 5395835) B5395835
theorem B746495 : Blo 746329 746495 := bstep (se 1 (by rfl) ⟨559871, by rfl⟩ : syracuseStep 746495 = 1119743) B1119743
theorem B2843707 : Blo 746329 2843707 := bstep (se 1 (by rfl) ⟨2132780, by rfl⟩ : syracuseStep 2843707 = 4265561) B4265561
theorem B746567 : Blo 746329 746567 := bstep (se 1 (by rfl) ⟨559925, by rfl⟩ : syracuseStep 746567 = 1119851) B1119851
theorem B746747 : Blo 746329 746747 := bstep (se 1 (by rfl) ⟨560060, by rfl⟩ : syracuseStep 746747 = 1120121) B1120121
theorem B746911 : Blo 746329 746911 := bstep (se 1 (by rfl) ⟨560183, by rfl⟩ : syracuseStep 746911 = 1120367) B1120367
theorem B746959 : Blo 746329 746959 := bstep (se 1 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 746959 = 1120439) B1120439
theorem B1894063 : Blo 746329 1894063 := bstep (se 1 (by rfl) ⟨1420547, by rfl⟩ : syracuseStep 1894063 = 2841095) B2841095
theorem B747239 : Blo 746329 747239 := bstep (se 1 (by rfl) ⟨560429, by rfl⟩ : syracuseStep 747239 = 1120859) B1120859
theorem B747247 : Blo 746329 747247 := bstep (se 1 (by rfl) ⟨560435, by rfl⟩ : syracuseStep 747247 = 1120871) B1120871
theorem B747263 : Blo 746329 747263 := bstep (se 1 (by rfl) ⟨560447, by rfl⟩ : syracuseStep 747263 = 1120895) B1120895
theorem B747335 : Blo 746329 747335 := bstep (se 1 (by rfl) ⟨560501, by rfl⟩ : syracuseStep 747335 = 1121003) B1121003
theorem B3204947 : Blo 746329 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B747355 : Blo 746329 747355 := bstep (se 1 (by rfl) ⟨560516, by rfl⟩ : syracuseStep 747355 = 1121033) B1121033
theorem B747515 : Blo 746329 747515 := bstep (se 1 (by rfl) ⟨560636, by rfl⟩ : syracuseStep 747515 = 1121273) B1121273
theorem B9595259 : Blo 746329 9595259 := bstep (se 1 (by rfl) ⟨7196444, by rfl⟩ : syracuseStep 9595259 = 14392889) B14392889
theorem B747935 : Blo 746329 747935 := bstep (se 1 (by rfl) ⟨560951, by rfl⟩ : syracuseStep 747935 = 1121903) B1121903
theorem B748015 : Blo 746329 748015 := bstep (se 1 (by rfl) ⟨561011, by rfl⟩ : syracuseStep 748015 = 1122023) B1122023
theorem B7006823 : Blo 746329 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B748199 : Blo 746329 748199 := bstep (se 1 (by rfl) ⟨561149, by rfl⟩ : syracuseStep 748199 = 1122299) B1122299
theorem B748239 : Blo 746329 748239 := bstep (se 1 (by rfl) ⟨561179, by rfl⟩ : syracuseStep 748239 = 1122359) B1122359
theorem B748319 : Blo 746329 748319 := bstep (se 1 (by rfl) ⟨561239, by rfl⟩ : syracuseStep 748319 = 1122479) B1122479
theorem B7695233 : Blo 746329 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B748455 : Blo 746329 748455 := bstep (se 1 (by rfl) ⟨561341, by rfl⟩ : syracuseStep 748455 = 1122683) B1122683
theorem B748571 : Blo 746329 748571 := bstep (se 1 (by rfl) ⟨561428, by rfl⟩ : syracuseStep 748571 = 1122857) B1122857
theorem B748635 : Blo 746329 748635 := bstep (se 1 (by rfl) ⟨561476, by rfl⟩ : syracuseStep 748635 = 1122953) B1122953
theorem B748775 : Blo 746329 748775 := bstep (se 1 (by rfl) ⟨561581, by rfl⟩ : syracuseStep 748775 = 1123163) B1123163
theorem B748799 : Blo 746329 748799 := bstep (se 1 (by rfl) ⟨561599, by rfl⟩ : syracuseStep 748799 = 1123199) B1123199
theorem B748847 : Blo 746329 748847 := bstep (se 1 (by rfl) ⟨561635, by rfl⟩ : syracuseStep 748847 = 1123271) B1123271
theorem B748991 : Blo 746329 748991 := bstep (se 1 (by rfl) ⟨561743, by rfl⟩ : syracuseStep 748991 = 1123487) B1123487
theorem B945695 : Blo 746329 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B749087 : Blo 746329 749087 := bstep (se 1 (by rfl) ⟨561815, by rfl⟩ : syracuseStep 749087 = 1123631) B1123631
theorem B749215 : Blo 746329 749215 := bstep (se 1 (by rfl) ⟨561911, by rfl⟩ : syracuseStep 749215 = 1123823) B1123823
theorem B749223 : Blo 746329 749223 := bstep (se 1 (by rfl) ⟨561917, by rfl⟩ : syracuseStep 749223 = 1123835) B1123835
theorem B749247 : Blo 746329 749247 := bstep (se 1 (by rfl) ⟨561935, by rfl⟩ : syracuseStep 749247 = 1123871) B1123871
theorem B1797919 : Blo 746329 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B749343 : Blo 746329 749343 := bstep (se 1 (by rfl) ⟨562007, by rfl⟩ : syracuseStep 749343 = 1124015) B1124015
theorem B9563993 : Blo 746329 9563993 := bstep (se 2 (by rfl) ⟨3586497, by rfl⟩ : syracuseStep 9563993 = 7172995) B7172995
theorem B749403 : Blo 746329 749403 := bstep (se 1 (by rfl) ⟨562052, by rfl⟩ : syracuseStep 749403 = 1124105) B1124105
theorem B749423 : Blo 746329 749423 := bstep (se 1 (by rfl) ⟨562067, by rfl⟩ : syracuseStep 749423 = 1124135) B1124135
theorem B749823 : Blo 746329 749823 := bstep (se 1 (by rfl) ⟨562367, by rfl⟩ : syracuseStep 749823 = 1124735) B1124735
theorem B2519315 : Blo 746329 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B20443529 : Blo 746329 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B749983 : Blo 746329 749983 := bstep (se 1 (by rfl) ⟨562487, by rfl⟩ : syracuseStep 749983 = 1124975) B1124975
theorem B750127 : Blo 746329 750127 := bstep (se 1 (by rfl) ⟨562595, by rfl⟩ : syracuseStep 750127 = 1125191) B1125191
theorem B3798251 : Blo 746329 3798251 := bstep (se 1 (by rfl) ⟨2848688, by rfl⟩ : syracuseStep 3798251 = 5697377) B5697377
theorem B2520719 : Blo 746329 2520719 := bstep (se 1 (by rfl) ⟨1890539, by rfl⟩ : syracuseStep 2520719 = 3781079) B3781079
theorem B2553895 : Blo 746329 2553895 := bstep (se 1 (by rfl) ⟨1915421, by rfl⟩ : syracuseStep 2553895 = 3830843) B3830843
theorem B2914721 : Blo 746329 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B1899035 : Blo 746329 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B10255151 : Blo 746329 10255151 := bstep (se 1 (by rfl) ⟨7691363, by rfl⟩ : syracuseStep 10255151 = 15382727) B15382727
theorem B10779905 : Blo 746329 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B10813121 : Blo 746329 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B151584857 : Blo 746329 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B2523311 : Blo 746329 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B8618329 : Blo 746329 8618329 := bstep (se 2 (by rfl) ⟨3231873, by rfl⟩ : syracuseStep 8618329 = 6463747) B6463747
theorem B2525417 : Blo 746329 2525417 := bstep (se 2 (by rfl) ⟨947031, by rfl⟩ : syracuseStep 2525417 = 1894063) B1894063
theorem B3901763 : Blo 746329 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2525903 : Blo 746329 2525903 := bstep (se 1 (by rfl) ⟨1894427, by rfl⟩ : syracuseStep 2525903 = 3788855) B3788855
theorem B43223867 : Blo 746329 43223867 := bstep (se 1 (by rfl) ⟨32417900, by rfl⟩ : syracuseStep 43223867 = 64835801) B64835801
theorem B109186217 : Blo 746329 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B6065383 : Blo 746329 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B10816811 : Blo 746329 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B1120667 : Blo 746329 1120667 := bstep (se 1 (by rfl) ⟨840500, by rfl⟩ : syracuseStep 1120667 = 1681001) B1681001
theorem B2136631 : Blo 746329 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B6396839 : Blo 746329 6396839 := bstep (se 1 (by rfl) ⟨4797629, by rfl⟩ : syracuseStep 6396839 = 9595259) B9595259
theorem B11541847 : Blo 746329 11541847 := bstep (se 1 (by rfl) ⟨8656385, by rfl⟩ : syracuseStep 11541847 = 17312771) B17312771
theorem B109354373 : Blo 746329 109354373 := bstep (se 4 (by rfl) ⟨10251972, by rfl⟩ : syracuseStep 109354373 = 20503945) B20503945
theorem B1121819 : Blo 746329 1121819 := bstep (se 1 (by rfl) ⟨841364, by rfl⟩ : syracuseStep 1121819 = 1682729) B1682729
theorem B158015123 : Blo 746329 158015123 := bstep (se 1 (by rfl) ⟨118511342, by rfl⟩ : syracuseStep 158015123 = 237022685) B237022685
theorem B1122185 : Blo 746329 1122185 := bstep (se 2 (by rfl) ⟨420819, by rfl⟩ : syracuseStep 1122185 = 841639) B841639
theorem B1679543 : Blo 746329 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B19144997 : Blo 746329 19144997 := bstep (se 4 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 19144997 = 3589687) B3589687
theorem B1122599 : Blo 746329 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B1122719 : Blo 746329 1122719 := bstep (se 1 (by rfl) ⟨842039, by rfl⟩ : syracuseStep 1122719 = 1684079) B1684079
theorem B1516087 : Blo 746329 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B2532167 : Blo 746329 2532167 := bstep (se 1 (by rfl) ⟨1899125, by rfl⟩ : syracuseStep 2532167 = 3798251) B3798251
theorem B1680479 : Blo 746329 1680479 := bstep (se 1 (by rfl) ⟨1260359, by rfl⟩ : syracuseStep 1680479 = 2520719) B2520719
theorem B1123559 : Blo 746329 1123559 := bstep (se 1 (by rfl) ⟨842669, by rfl⟩ : syracuseStep 1123559 = 1685339) B1685339
theorem B1943147 : Blo 746329 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B1124423 : Blo 746329 1124423 := bstep (se 1 (by rfl) ⟨843317, by rfl⟩ : syracuseStep 1124423 = 1686635) B1686635
theorem B7186603 : Blo 746329 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B7678475 : Blo 746329 7678475 := bstep (se 1 (by rfl) ⟨5758856, by rfl⟩ : syracuseStep 7678475 = 11517713) B11517713
theorem B4270643 : Blo 746329 4270643 := bstep (se 1 (by rfl) ⟨3202982, by rfl⟩ : syracuseStep 4270643 = 6405965) B6405965
theorem B1682081 : Blo 746329 1682081 := bstep (se 2 (by rfl) ⟨630780, by rfl⟩ : syracuseStep 1682081 = 1261561) B1261561
theorem B3779297 : Blo 746329 3779297 := bstep (se 2 (by rfl) ⟨1417236, by rfl⟩ : syracuseStep 3779297 = 2834473) B2834473
theorem B4041515 : Blo 746329 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B797807 : Blo 746329 797807 := bstep (se 1 (by rfl) ⟨598355, by rfl⟩ : syracuseStep 797807 = 1196711) B1196711
theorem B6401213 : Blo 746329 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B3779783 : Blo 746329 3779783 := bstep (se 1 (by rfl) ⟨2834837, by rfl⟩ : syracuseStep 3779783 = 5669675) B5669675
theorem B3779945 : Blo 746329 3779945 := bstep (se 2 (by rfl) ⟨1417479, by rfl⟩ : syracuseStep 3779945 = 2834959) B2834959
theorem B4796297 : Blo 746329 4796297 := bstep (se 2 (by rfl) ⟨1798611, by rfl⟩ : syracuseStep 4796297 = 3597223) B3597223
theorem B92287025 : Blo 746329 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B1683593 : Blo 746329 1683593 := bstep (se 2 (by rfl) ⟨631347, by rfl⟩ : syracuseStep 1683593 = 1262695) B1262695
theorem B8532215 : Blo 746329 8532215 := bstep (se 1 (by rfl) ⟨6399161, by rfl⟩ : syracuseStep 8532215 = 12798323) B12798323
theorem B1683791 : Blo 746329 1683791 := bstep (se 1 (by rfl) ⟨1262843, by rfl⟩ : syracuseStep 1683791 = 2525687) B2525687
theorem B1684187 : Blo 746329 1684187 := bstep (se 1 (by rfl) ⟨1263140, by rfl⟩ : syracuseStep 1684187 = 2526281) B2526281
theorem B1684457 : Blo 746329 1684457 := bstep (se 2 (by rfl) ⟨631671, by rfl⟩ : syracuseStep 1684457 = 1263343) B1263343
theorem B10139053 : Blo 746329 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B1684943 : Blo 746329 1684943 := bstep (se 1 (by rfl) ⟨1263707, by rfl⟩ : syracuseStep 1684943 = 2527415) B2527415
theorem B1423327 : Blo 746329 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B1685483 : Blo 746329 1685483 := bstep (se 1 (by rfl) ⟨1264112, by rfl⟩ : syracuseStep 1685483 = 2528225) B2528225
theorem B8632739 : Blo 746329 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B3193415 : Blo 746329 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B1687535 : Blo 746329 1687535 := bstep (se 1 (by rfl) ⟨1265651, by rfl⟩ : syracuseStep 1687535 = 2531303) B2531303
theorem B1065001 : Blo 746329 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B1261831 : Blo 746329 1261831 := bstep (se 1 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 1261831 = 1892747) B1892747
theorem B224149889 : Blo 746329 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B10371665 : Blo 746329 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B13681871 : Blo 746329 13681871 := bstep (se 1 (by rfl) ⟨10261403, by rfl⟩ : syracuseStep 13681871 = 20522807) B20522807
theorem B4671215 : Blo 746329 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B4310921 : Blo 746329 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B5130155 : Blo 746329 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B3786749 : Blo 746329 3786749 := bstep (se 3 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 3786749 = 1420031) B1420031
theorem B6375995 : Blo 746329 6375995 := bstep (se 1 (by rfl) ⟨4781996, by rfl⟩ : syracuseStep 6375995 = 9563993) B9563993
theorem B3787721 : Blo 746329 3787721 := bstep (se 2 (by rfl) ⟨1420395, by rfl⟩ : syracuseStep 3787721 = 2840791) B2840791
theorem B3787883 : Blo 746329 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B39374819 : Blo 746329 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B9588901 : Blo 746329 9588901 := bstep (se 4 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 9588901 = 1797919) B1797919
theorem B6082775 : Blo 746329 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B1266023 : Blo 746329 1266023 := bstep (se 1 (by rfl) ⟨949517, by rfl⟩ : syracuseStep 1266023 = 1899035) B1899035
theorem B6836767 : Blo 746329 6836767 := bstep (se 1 (by rfl) ⟨5127575, by rfl⟩ : syracuseStep 6836767 = 10255151) B10255151
theorem B3592957 : Blo 746329 3592957 := bstep (se 3 (by rfl) ⟨673679, by rfl⟩ : syracuseStep 3592957 = 1347359) B1347359
theorem B6083423 : Blo 746329 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B8639723 : Blo 746329 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B4052393 : Blo 746329 4052393 := bstep (se 2 (by rfl) ⟨1519647, by rfl⟩ : syracuseStep 4052393 = 3039295) B3039295
theorem B13620773 : Blo 746329 13620773 := bstep (se 4 (by rfl) ⟨1276947, by rfl⟩ : syracuseStep 13620773 = 2553895) B2553895
theorem B841423 : Blo 746329 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B5691545 : Blo 746329 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B1890479 : Blo 746329 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B1890823 : Blo 746329 1890823 := bstep (se 1 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 1890823 = 2836235) B2836235
theorem B842395 : Blo 746329 842395 := bstep (se 1 (by rfl) ⟨631796, by rfl⟩ : syracuseStep 842395 = 1263593) B1263593
theorem B3791609 : Blo 746329 3791609 := bstep (se 2 (by rfl) ⟨1421853, by rfl⟩ : syracuseStep 3791609 = 2843707) B2843707
theorem B842719 : Blo 746329 842719 := bstep (se 1 (by rfl) ⟨632039, by rfl⟩ : syracuseStep 842719 = 1264079) B1264079
theorem B842863 : Blo 746329 842863 := bstep (se 1 (by rfl) ⟨632147, by rfl⟩ : syracuseStep 842863 = 1264295) B1264295
theorem B3464329 : Blo 746329 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B58350793 : Blo 746329 58350793 := bstep (se 2 (by rfl) ⟨21881547, by rfl⟩ : syracuseStep 58350793 = 43763095) B43763095
theorem B843367 : Blo 746329 843367 := bstep (se 1 (by rfl) ⟨632525, by rfl⟩ : syracuseStep 843367 = 1265051) B1265051
theorem B1892423 : Blo 746329 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B1794383 : Blo 746329 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B2023807 : Blo 746329 2023807 := bstep (se 1 (by rfl) ⟨1517855, by rfl⟩ : syracuseStep 2023807 = 3035711) B3035711
theorem B3793391 : Blo 746329 3793391 := bstep (se 1 (by rfl) ⟨2845043, by rfl⟩ : syracuseStep 3793391 = 5690087) B5690087
theorem B746331 : Blo 746329 746331 := bstep (se 1 (by rfl) ⟨559748, by rfl⟩ : syracuseStep 746331 = 1119497) B1119497
theorem B5694461 : Blo 746329 5694461 := bstep (se 3 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 5694461 = 2135423) B2135423
theorem B8545337 : Blo 746329 8545337 := bstep (se 2 (by rfl) ⟨3204501, by rfl⟩ : syracuseStep 8545337 = 6409003) B6409003
theorem B746651 : Blo 746329 746651 := bstep (se 1 (by rfl) ⟨559988, by rfl⟩ : syracuseStep 746651 = 1119977) B1119977
theorem B746779 : Blo 746329 746779 := bstep (se 1 (by rfl) ⟨560084, by rfl⟩ : syracuseStep 746779 = 1120169) B1120169
theorem B746823 : Blo 746329 746823 := bstep (se 1 (by rfl) ⟨560117, by rfl⟩ : syracuseStep 746823 = 1120235) B1120235
theorem B3597821 : Blo 746329 3597821 := bstep (se 3 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 3597821 = 1349183) B1349183
theorem B13657619 : Blo 746329 13657619 := bstep (se 1 (by rfl) ⟨10243214, by rfl⟩ : syracuseStep 13657619 = 20486429) B20486429
theorem B747167 : Blo 746329 747167 := bstep (se 1 (by rfl) ⟨560375, by rfl⟩ : syracuseStep 747167 = 1120751) B1120751
theorem B8513261 : Blo 746329 8513261 := bstep (se 3 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 8513261 = 3192473) B3192473
theorem B747375 : Blo 746329 747375 := bstep (se 1 (by rfl) ⟨560531, by rfl⟩ : syracuseStep 747375 = 1121063) B1121063
theorem B24242075 : Blo 746329 24242075 := bstep (se 1 (by rfl) ⟨18181556, by rfl⟩ : syracuseStep 24242075 = 36363113) B36363113
theorem B1894367 : Blo 746329 1894367 := bstep (se 1 (by rfl) ⟨1420775, by rfl⟩ : syracuseStep 1894367 = 2841551) B2841551
theorem B747775 : Blo 746329 747775 := bstep (se 1 (by rfl) ⟨560831, by rfl⟩ : syracuseStep 747775 = 1121663) B1121663
theorem B4254079 : Blo 746329 4254079 := bstep (se 1 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 4254079 = 6381119) B6381119
theorem B748143 : Blo 746329 748143 := bstep (se 1 (by rfl) ⟨561107, by rfl⟩ : syracuseStep 748143 = 1122215) B1122215
theorem B748315 : Blo 746329 748315 := bstep (se 1 (by rfl) ⟨561236, by rfl⟩ : syracuseStep 748315 = 1122473) B1122473
theorem B748827 : Blo 746329 748827 := bstep (se 1 (by rfl) ⟨561620, by rfl⟩ : syracuseStep 748827 = 1123241) B1123241
theorem B749007 : Blo 746329 749007 := bstep (se 1 (by rfl) ⟨561755, by rfl⟩ : syracuseStep 749007 = 1123511) B1123511
theorem B749167 : Blo 746329 749167 := bstep (se 1 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 749167 = 1123751) B1123751
theorem B749287 : Blo 746329 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B2846441 : Blo 746329 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B749479 : Blo 746329 749479 := bstep (se 1 (by rfl) ⟨562109, by rfl⟩ : syracuseStep 749479 = 1124219) B1124219
theorem B749639 : Blo 746329 749639 := bstep (se 1 (by rfl) ⟨562229, by rfl⟩ : syracuseStep 749639 = 1124459) B1124459
theorem B3797117 : Blo 746329 3797117 := bstep (se 3 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 3797117 = 1423919) B1423919
theorem B749759 : Blo 746329 749759 := bstep (se 1 (by rfl) ⟨562319, by rfl⟩ : syracuseStep 749759 = 1124639) B1124639
theorem B2846927 : Blo 746329 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B946399 : Blo 746329 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B750055 : Blo 746329 750055 := bstep (se 1 (by rfl) ⟨562541, by rfl⟩ : syracuseStep 750055 = 1125083) B1125083
theorem B1602175 : Blo 746329 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B750239 : Blo 746329 750239 := bstep (se 1 (by rfl) ⟨562679, by rfl⟩ : syracuseStep 750239 = 1125359) B1125359
theorem B750247 : Blo 746329 750247 := bstep (se 1 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 750247 = 1125371) B1125371
theorem B750287 : Blo 746329 750287 := bstep (se 1 (by rfl) ⟨562715, by rfl⟩ : syracuseStep 750287 = 1125431) B1125431
theorem B947143 : Blo 746329 947143 := bstep (se 1 (by rfl) ⟨710357, by rfl⟩ : syracuseStep 947143 = 1420715) B1420715
theorem B2520287 : Blo 746329 2520287 := bstep (se 1 (by rfl) ⟨1890215, by rfl⟩ : syracuseStep 2520287 = 3780431) B3780431
theorem B2127359 : Blo 746329 2127359 := bstep (se 1 (by rfl) ⟨1595519, by rfl⟩ : syracuseStep 2127359 = 3191039) B3191039
theorem B13629019 : Blo 746329 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B4323437 : Blo 746329 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B59144363 : Blo 746329 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B2521853 : Blo 746329 2521853 := bstep (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) B945695
theorem B948991 : Blo 746329 948991 := bstep (se 1 (by rfl) ⟨711743, by rfl⟩ : syracuseStep 948991 = 1423487) B1423487
theorem B7208747 : Blo 746329 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B101056571 : Blo 746329 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B6914443 : Blo 746329 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B3114143 : Blo 746329 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B2524499 : Blo 746329 2524499 := bstep (se 1 (by rfl) ⟨1893374, by rfl⟩ : syracuseStep 2524499 = 3786749) B3786749
theorem B2525147 : Blo 746329 2525147 := bstep (se 1 (by rfl) ⟨1893860, by rfl⟩ : syracuseStep 2525147 = 3787721) B3787721
theorem B2525255 : Blo 746329 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B7211207 : Blo 746329 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B26249879 : Blo 746329 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B5672105 : Blo 746329 5672105 := bstep (se 2 (by rfl) ⟨2127039, by rfl⟩ : syracuseStep 5672105 = 4254079) B4254079
theorem B23039261 : Blo 746329 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B9080515 : Blo 746329 9080515 := bstep (se 1 (by rfl) ⟨6810386, by rfl⟩ : syracuseStep 9080515 = 13620773) B13620773
theorem B5181725 : Blo 746329 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B2527739 : Blo 746329 2527739 := bstep (se 1 (by rfl) ⟨1895804, by rfl⟩ : syracuseStep 2527739 = 3791609) B3791609
theorem B4264559 : Blo 746329 4264559 := bstep (se 1 (by rfl) ⟨3198419, by rfl⟩ : syracuseStep 4264559 = 6396839) B6396839
theorem B1119695 : Blo 746329 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B12785201 : Blo 746329 12785201 := bstep (se 2 (by rfl) ⟨4794450, by rfl⟩ : syracuseStep 12785201 = 9588901) B9588901
theorem B2528927 : Blo 746329 2528927 := bstep (se 1 (by rfl) ⟨1896695, by rfl⟩ : syracuseStep 2528927 = 3793391) B3793391
theorem B1120319 : Blo 746329 1120319 := bstep (se 1 (by rfl) ⟨840239, by rfl⟩ : syracuseStep 1120319 = 1680479) B1680479
theorem B2136233 : Blo 746329 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B4790609 : Blo 746329 4790609 := bstep (se 2 (by rfl) ⟨1796478, by rfl⟩ : syracuseStep 4790609 = 3592957) B3592957
theorem B2398547 : Blo 746329 2398547 := bstep (se 1 (by rfl) ⟨1798910, by rfl⟩ : syracuseStep 2398547 = 3597821) B3597821
theorem B5675507 : Blo 746329 5675507 := bstep (se 1 (by rfl) ⟨4256630, by rfl⟩ : syracuseStep 5675507 = 8513261) B8513261
theorem B16161383 : Blo 746329 16161383 := bstep (se 1 (by rfl) ⟨12121037, by rfl⟩ : syracuseStep 16161383 = 24242075) B24242075
theorem B5118983 : Blo 746329 5118983 := bstep (se 1 (by rfl) ⟨3839237, by rfl⟩ : syracuseStep 5118983 = 7678475) B7678475
theorem B1121387 : Blo 746329 1121387 := bstep (se 1 (by rfl) ⟨841040, by rfl⟩ : syracuseStep 1121387 = 1682081) B1682081
theorem B2694343 : Blo 746329 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B4267475 : Blo 746329 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B1121897 : Blo 746329 1121897 := bstep (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) B841423
theorem B2531411 : Blo 746329 2531411 := bstep (se 1 (by rfl) ⟨1898558, by rfl⟩ : syracuseStep 2531411 = 3797117) B3797117
theorem B1122395 : Blo 746329 1122395 := bstep (se 1 (by rfl) ⟨841796, by rfl⟩ : syracuseStep 1122395 = 1683593) B1683593
theorem B1122527 : Blo 746329 1122527 := bstep (se 1 (by rfl) ⟨841895, by rfl⟩ : syracuseStep 1122527 = 1683791) B1683791
theorem B1122791 : Blo 746329 1122791 := bstep (se 1 (by rfl) ⟨842093, by rfl⟩ : syracuseStep 1122791 = 1684187) B1684187
theorem B1122971 : Blo 746329 1122971 := bstep (se 1 (by rfl) ⟨842228, by rfl⟩ : syracuseStep 1122971 = 1684457) B1684457
theorem B1680191 : Blo 746329 1680191 := bstep (se 1 (by rfl) ⟨1260143, by rfl⟩ : syracuseStep 1680191 = 2520287) B2520287
theorem B1123193 : Blo 746329 1123193 := bstep (se 2 (by rfl) ⟨421197, by rfl⟩ : syracuseStep 1123193 = 842395) B842395
theorem B1123295 : Blo 746329 1123295 := bstep (se 1 (by rfl) ⟨842471, by rfl⟩ : syracuseStep 1123295 = 1684943) B1684943
theorem B1418239 : Blo 746329 1418239 := bstep (se 1 (by rfl) ⟨1063679, by rfl⟩ : syracuseStep 1418239 = 2127359) B2127359
theorem B1123625 : Blo 746329 1123625 := bstep (se 2 (by rfl) ⟨421359, by rfl⟩ : syracuseStep 1123625 = 842719) B842719
theorem B1123655 : Blo 746329 1123655 := bstep (se 1 (by rfl) ⟨842741, by rfl⟩ : syracuseStep 1123655 = 1685483) B1685483
theorem B39429575 : Blo 746329 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B1123817 : Blo 746329 1123817 := bstep (se 2 (by rfl) ⟨421431, by rfl⟩ : syracuseStep 1123817 = 842863) B842863
theorem B77801057 : Blo 746329 77801057 := bstep (se 2 (by rfl) ⟨29175396, by rfl⟩ : syracuseStep 77801057 = 58350793) B58350793
theorem B1681235 : Blo 746329 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B1124489 : Blo 746329 1124489 := bstep (se 2 (by rfl) ⟨421683, by rfl⟩ : syracuseStep 1124489 = 843367) B843367
theorem B1125023 : Blo 746329 1125023 := bstep (se 1 (by rfl) ⟨843767, by rfl⟩ : syracuseStep 1125023 = 1687535) B1687535
theorem B1420001 : Blo 746329 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B1682207 : Blo 746329 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B1682441 : Blo 746329 1682441 := bstep (se 2 (by rfl) ⟨630915, by rfl⟩ : syracuseStep 1682441 = 1261831) B1261831
theorem B2698409 : Blo 746329 2698409 := bstep (se 2 (by rfl) ⟨1011903, by rfl⟩ : syracuseStep 2698409 = 2023807) B2023807
theorem B9121247 : Blo 746329 9121247 := bstep (se 1 (by rfl) ⟨6840935, by rfl⟩ : syracuseStep 9121247 = 13681871) B13681871
theorem B597733037 : Blo 746329 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B3420103 : Blo 746329 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B1683611 : Blo 746329 1683611 := bstep (se 1 (by rfl) ⟨1262708, by rfl⟩ : syracuseStep 1683611 = 2525417) B2525417
theorem B2601175 : Blo 746329 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B1683935 : Blo 746329 1683935 := bstep (se 1 (by rfl) ⟨1262951, by rfl⟩ : syracuseStep 1683935 = 2525903) B2525903
theorem B28815911 : Blo 746329 28815911 := bstep (se 1 (by rfl) ⟨21611933, by rfl⟩ : syracuseStep 28815911 = 43223867) B43223867
theorem B72790811 : Blo 746329 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B9582137 : Blo 746329 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B2701595 : Blo 746329 2701595 := bstep (se 1 (by rfl) ⟨2026196, by rfl⟩ : syracuseStep 2701595 = 4052393) B4052393
theorem B36420317 : Blo 746329 36420317 := bstep (se 3 (by rfl) ⟨6828809, by rfl⟩ : syracuseStep 36420317 = 13657619) B13657619
theorem B1260319 : Blo 746329 1260319 := bstep (se 1 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 1260319 = 1890479) B1890479
theorem B1261615 : Blo 746329 1261615 := bstep (se 1 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 1261615 = 1892423) B1892423
theorem B12763331 : Blo 746329 12763331 := bstep (se 1 (by rfl) ⟨9572498, by rfl⟩ : syracuseStep 12763331 = 19144997) B19144997
theorem B1196255 : Blo 746329 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1261865 : Blo 746329 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B1688111 : Blo 746329 1688111 := bstep (se 1 (by rfl) ⟨1266083, by rfl⟩ : syracuseStep 1688111 = 2532167) B2532167
theorem B1262857 : Blo 746329 1262857 := bstep (se 2 (by rfl) ⟨473571, by rfl⟩ : syracuseStep 1262857 = 947143) B947143
theorem B1262911 : Blo 746329 1262911 := bstep (se 1 (by rfl) ⟨947183, by rfl⟩ : syracuseStep 1262911 = 1894367) B1894367
theorem B13518737 : Blo 746329 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B18172025 : Blo 746329 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B3197531 : Blo 746329 3197531 := bstep (se 1 (by rfl) ⟨2398148, by rfl⟩ : syracuseStep 3197531 = 4796297) B4796297
theorem B61524683 : Blo 746329 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B5688143 : Blo 746329 5688143 := bstep (se 1 (by rfl) ⟨4266107, by rfl⟩ : syracuseStep 5688143 = 8532215) B8532215
theorem B1265321 : Blo 746329 1265321 := bstep (se 2 (by rfl) ⟨474495, by rfl⟩ : syracuseStep 1265321 = 948991) B948991
theorem B5755159 : Blo 746329 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B15389129 : Blo 746329 15389129 := bstep (se 2 (by rfl) ⟨5770923, by rfl⟩ : syracuseStep 15389129 = 11541847) B11541847
theorem B4805831 : Blo 746329 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B2021449 : Blo 746329 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B4250663 : Blo 746329 4250663 := bstep (se 1 (by rfl) ⟨3187997, by rfl⟩ : syracuseStep 4250663 = 6375995) B6375995
theorem B45964421 : Blo 746329 45964421 := bstep (se 4 (by rfl) ⟨4309164, by rfl⟩ : syracuseStep 45964421 = 8618329) B8618329
theorem B4055183 : Blo 746329 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B36462757 : Blo 746329 36462757 := bstep (se 4 (by rfl) ⟨3418383, by rfl⟩ : syracuseStep 36462757 = 6836767) B6836767
theorem B844015 : Blo 746329 844015 := bstep (se 1 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 844015 = 1266023) B1266023
theorem B4055615 : Blo 746329 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B3794363 : Blo 746329 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B747111 : Blo 746329 747111 := bstep (se 1 (by rfl) ⟨560333, by rfl⟩ : syracuseStep 747111 = 1120667) B1120667
theorem B8087177 : Blo 746329 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B72902915 : Blo 746329 72902915 := bstep (se 1 (by rfl) ⟨54677186, by rfl⟩ : syracuseStep 72902915 = 109354373) B109354373
theorem B747879 : Blo 746329 747879 := bstep (se 1 (by rfl) ⟨560909, by rfl⟩ : syracuseStep 747879 = 1121819) B1121819
theorem B11495789 : Blo 746329 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B105343415 : Blo 746329 105343415 := bstep (se 1 (by rfl) ⟨79007561, by rfl⟩ : syracuseStep 105343415 = 158015123) B158015123
theorem B748123 : Blo 746329 748123 := bstep (se 1 (by rfl) ⟨561092, by rfl⟩ : syracuseStep 748123 = 1122185) B1122185
theorem B748399 : Blo 746329 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B748479 : Blo 746329 748479 := bstep (se 1 (by rfl) ⟨561359, by rfl⟩ : syracuseStep 748479 = 1122719) B1122719
theorem B3796307 : Blo 746329 3796307 := bstep (se 1 (by rfl) ⟨2847230, by rfl⟩ : syracuseStep 3796307 = 5694461) B5694461
theorem B5696891 : Blo 746329 5696891 := bstep (se 1 (by rfl) ⟨4272668, by rfl⟩ : syracuseStep 5696891 = 8545337) B8545337
theorem B749039 : Blo 746329 749039 := bstep (se 1 (by rfl) ⟨561779, by rfl⟩ : syracuseStep 749039 = 1123559) B1123559
theorem B749615 : Blo 746329 749615 := bstep (se 1 (by rfl) ⟨562211, by rfl⟩ : syracuseStep 749615 = 1124423) B1124423
theorem B2847095 : Blo 746329 2847095 := bstep (se 1 (by rfl) ⟨2135321, by rfl⟩ : syracuseStep 2847095 = 4270643) B4270643
theorem B2519531 : Blo 746329 2519531 := bstep (se 1 (by rfl) ⟨1889648, by rfl⟩ : syracuseStep 2519531 = 3779297) B3779297
theorem B2519855 : Blo 746329 2519855 := bstep (se 1 (by rfl) ⟨1889891, by rfl⟩ : syracuseStep 2519855 = 3779783) B3779783
theorem B2519963 : Blo 746329 2519963 := bstep (se 1 (by rfl) ⟨1889972, by rfl⟩ : syracuseStep 2519963 = 3779945) B3779945
theorem B1897627 : Blo 746329 1897627 := bstep (se 1 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 1897627 = 2846441) B2846441
theorem B1897769 : Blo 746329 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B1897951 : Blo 746329 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B2127485 : Blo 746329 2127485 := bstep (se 3 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 2127485 = 797807) B797807
theorem B2521097 : Blo 746329 2521097 := bstep (se 2 (by rfl) ⟨945411, by rfl⟩ : syracuseStep 2521097 = 1890823) B1890823
theorem B2848841 : Blo 746329 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B2882291 : Blo 746329 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B4619105 : Blo 746329 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B2128943 : Blo 746329 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B67371047 : Blo 746329 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B9012491 : Blo 746329 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B2131687 : Blo 746329 2131687 := bstep (se 1 (by rfl) ⟨1598765, by rfl⟩ : syracuseStep 2131687 = 3197531) B3197531
theorem B17499919 : Blo 746329 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B10259419 : Blo 746329 10259419 := bstep (se 1 (by rfl) ⟨7694564, by rfl⟩ : syracuseStep 10259419 = 15389129) B15389129
theorem B8523467 : Blo 746329 8523467 := bstep (se 1 (by rfl) ⟨6392600, by rfl⟩ : syracuseStep 8523467 = 12785201) B12785201
theorem B3412655 : Blo 746329 3412655 := bstep (se 1 (by rfl) ⟨2559491, by rfl⟩ : syracuseStep 3412655 = 5118983) B5118983
theorem B30642947 : Blo 746329 30642947 := bstep (se 1 (by rfl) ⟨22982210, by rfl⟩ : syracuseStep 30642947 = 45964421) B45964421
theorem B4560137 : Blo 746329 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B7673545 : Blo 746329 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B1120127 : Blo 746329 1120127 := bstep (se 1 (by rfl) ⟨840095, by rfl⟩ : syracuseStep 1120127 = 1680191) B1680191
theorem B2529575 : Blo 746329 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B26286383 : Blo 746329 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B1120823 : Blo 746329 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B48601943 : Blo 746329 48601943 := bstep (se 1 (by rfl) ⟨36451457, by rfl⟩ : syracuseStep 48601943 = 72902915) B72902915
theorem B2530169 : Blo 746329 2530169 := bstep (se 2 (by rfl) ⟨948813, by rfl⟩ : syracuseStep 2530169 = 1897627) B1897627
theorem B70228943 : Blo 746329 70228943 := bstep (se 1 (by rfl) ⟨52671707, by rfl⟩ : syracuseStep 70228943 = 105343415) B105343415
theorem B1121471 : Blo 746329 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B2530601 : Blo 746329 2530601 := bstep (se 2 (by rfl) ⟨948975, by rfl⟩ : syracuseStep 2530601 = 1897951) B1897951
theorem B1121627 : Blo 746329 1121627 := bstep (se 1 (by rfl) ⟨841220, by rfl⟩ : syracuseStep 1121627 = 1682441) B1682441
theorem B2530871 : Blo 746329 2530871 := bstep (se 1 (by rfl) ⟨1898153, by rfl⟩ : syracuseStep 2530871 = 3796307) B3796307
theorem B2695265 : Blo 746329 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1122407 : Blo 746329 1122407 := bstep (se 1 (by rfl) ⟨841805, by rfl⟩ : syracuseStep 1122407 = 1683611) B1683611
theorem B1122623 : Blo 746329 1122623 := bstep (se 1 (by rfl) ⟨841967, by rfl⟩ : syracuseStep 1122623 = 1683935) B1683935
theorem B1679687 : Blo 746329 1679687 := bstep (se 1 (by rfl) ⟨1259765, by rfl⟩ : syracuseStep 1679687 = 2519531) B2519531
theorem B19210607 : Blo 746329 19210607 := bstep (se 1 (by rfl) ⟨14407955, by rfl⟩ : syracuseStep 19210607 = 28815911) B28815911
theorem B1679903 : Blo 746329 1679903 := bstep (se 1 (by rfl) ⟨1259927, by rfl⟩ : syracuseStep 1679903 = 2519855) B2519855
theorem B1679975 : Blo 746329 1679975 := bstep (se 1 (by rfl) ⟨1259981, by rfl⟩ : syracuseStep 1679975 = 2519963) B2519963
theorem B1680425 : Blo 746329 1680425 := bstep (se 2 (by rfl) ⟨630159, by rfl⟩ : syracuseStep 1680425 = 1260319) B1260319
theorem B1418323 : Blo 746329 1418323 := bstep (se 1 (by rfl) ⟨1063742, by rfl⟩ : syracuseStep 1418323 = 2127485) B2127485
theorem B1680731 : Blo 746329 1680731 := bstep (se 1 (by rfl) ⟨1260548, by rfl⟩ : syracuseStep 1680731 = 2521097) B2521097
theorem B1419295 : Blo 746329 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B1682153 : Blo 746329 1682153 := bstep (se 2 (by rfl) ⟨630807, by rfl⟩ : syracuseStep 1682153 = 1261615) B1261615
theorem B1125353 : Blo 746329 1125353 := bstep (se 2 (by rfl) ⟨422007, by rfl⟩ : syracuseStep 1125353 = 844015) B844015
theorem B1125407 : Blo 746329 1125407 := bstep (se 1 (by rfl) ⟨844055, by rfl⟩ : syracuseStep 1125407 = 1688111) B1688111
theorem B9219257 : Blo 746329 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B3190013 : Blo 746329 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B2076095 : Blo 746329 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B1682999 : Blo 746329 1682999 := bstep (se 1 (by rfl) ⟨1262249, by rfl⟩ : syracuseStep 1682999 = 2524499) B2524499
theorem B1683431 : Blo 746329 1683431 := bstep (se 1 (by rfl) ⟨1262573, by rfl⟩ : syracuseStep 1683431 = 2525147) B2525147
theorem B1683503 : Blo 746329 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B1683809 : Blo 746329 1683809 := bstep (se 2 (by rfl) ⟨631428, by rfl⟩ : syracuseStep 1683809 = 1262857) B1262857
theorem B1683881 : Blo 746329 1683881 := bstep (se 2 (by rfl) ⟨631455, by rfl⟩ : syracuseStep 1683881 = 1262911) B1262911
theorem B3781403 : Blo 746329 3781403 := bstep (se 1 (by rfl) ⟨2836052, by rfl⟩ : syracuseStep 3781403 = 5672105) B5672105
theorem B3454483 : Blo 746329 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B1685159 : Blo 746329 1685159 := bstep (se 1 (by rfl) ⟨1263869, by rfl⟩ : syracuseStep 1685159 = 2527739) B2527739
theorem B1685951 : Blo 746329 1685951 := bstep (se 1 (by rfl) ⟨1264463, by rfl⟩ : syracuseStep 1685951 = 2528927) B2528927
theorem B1424155 : Blo 746329 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B3193739 : Blo 746329 3193739 := bstep (se 1 (by rfl) ⟨2395304, by rfl⟩ : syracuseStep 3193739 = 4790609) B4790609
theorem B3783671 : Blo 746329 3783671 := bstep (se 1 (by rfl) ⟨2837753, by rfl⟩ : syracuseStep 3783671 = 5675507) B5675507
theorem B2833775 : Blo 746329 2833775 := bstep (se 1 (by rfl) ⟨2125331, by rfl⟩ : syracuseStep 2833775 = 4250663) B4250663
theorem B12107353 : Blo 746329 12107353 := bstep (se 2 (by rfl) ⟨4540257, by rfl⟩ : syracuseStep 12107353 = 9080515) B9080515
theorem B1687607 : Blo 746329 1687607 := bstep (se 1 (by rfl) ⟨1265705, by rfl⟩ : syracuseStep 1687607 = 2531411) B2531411
theorem B2703455 : Blo 746329 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B2703743 : Blo 746329 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B5391451 : Blo 746329 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B7686109 : Blo 746329 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B6080831 : Blo 746329 6080831 := bstep (se 1 (by rfl) ⟨4560623, by rfl⟩ : syracuseStep 6080831 = 9121247) B9121247
theorem B1265179 : Blo 746329 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B3592457 : Blo 746329 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B8508887 : Blo 746329 8508887 := bstep (se 1 (by rfl) ⟨6381665, by rfl⟩ : syracuseStep 8508887 = 12763331) B12763331
theorem B841243 : Blo 746329 841243 := bstep (se 1 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 841243 = 1261865) B1261865
theorem B48617009 : Blo 746329 48617009 := bstep (se 2 (by rfl) ⟨18231378, by rfl⟩ : syracuseStep 48617009 = 36462757) B36462757
theorem B1890985 : Blo 746329 1890985 := bstep (se 2 (by rfl) ⟨709119, by rfl⟩ : syracuseStep 1890985 = 1418239) B1418239
theorem B12114683 : Blo 746329 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B4807471 : Blo 746329 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B41016455 : Blo 746329 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B3792095 : Blo 746329 3792095 := bstep (se 1 (by rfl) ⟨2844071, by rfl⟩ : syracuseStep 3792095 = 5688143) B5688143
theorem B15359507 : Blo 746329 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B843547 : Blo 746329 843547 := bstep (se 1 (by rfl) ⟨632660, by rfl⟩ : syracuseStep 843547 = 1265321) B1265321
theorem B2843039 : Blo 746329 2843039 := bstep (se 1 (by rfl) ⟨2132279, by rfl⟩ : syracuseStep 2843039 = 4264559) B4264559
theorem B3203887 : Blo 746329 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B746463 : Blo 746329 746463 := bstep (se 1 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 746463 = 1119695) B1119695
theorem B746879 : Blo 746329 746879 := bstep (se 1 (by rfl) ⟨560159, by rfl⟩ : syracuseStep 746879 = 1120319) B1120319
theorem B1599031 : Blo 746329 1599031 := bstep (se 1 (by rfl) ⟨1199273, by rfl⟩ : syracuseStep 1599031 = 2398547) B2398547
theorem B10774255 : Blo 746329 10774255 := bstep (se 1 (by rfl) ⟨8080691, by rfl⟩ : syracuseStep 10774255 = 16161383) B16161383
theorem B747591 : Blo 746329 747591 := bstep (se 1 (by rfl) ⟨560693, by rfl⟩ : syracuseStep 747591 = 1121387) B1121387
theorem B2844983 : Blo 746329 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B747931 : Blo 746329 747931 := bstep (se 1 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 747931 = 1121897) B1121897
theorem B748263 : Blo 746329 748263 := bstep (se 1 (by rfl) ⟨561197, by rfl⟩ : syracuseStep 748263 = 1122395) B1122395
theorem B748351 : Blo 746329 748351 := bstep (se 1 (by rfl) ⟨561263, by rfl⟩ : syracuseStep 748351 = 1122527) B1122527
theorem B3468233 : Blo 746329 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B748527 : Blo 746329 748527 := bstep (se 1 (by rfl) ⟨561395, by rfl⟩ : syracuseStep 748527 = 1122791) B1122791
theorem B748647 : Blo 746329 748647 := bstep (se 1 (by rfl) ⟨561485, by rfl⟩ : syracuseStep 748647 = 1122971) B1122971
theorem B748795 : Blo 746329 748795 := bstep (se 1 (by rfl) ⟨561596, by rfl⟩ : syracuseStep 748795 = 1123193) B1123193
theorem B748863 : Blo 746329 748863 := bstep (se 1 (by rfl) ⟨561647, by rfl⟩ : syracuseStep 748863 = 1123295) B1123295
theorem B749083 : Blo 746329 749083 := bstep (se 1 (by rfl) ⟨561812, by rfl⟩ : syracuseStep 749083 = 1123625) B1123625
theorem B749103 : Blo 746329 749103 := bstep (se 1 (by rfl) ⟨561827, by rfl⟩ : syracuseStep 749103 = 1123655) B1123655
theorem B749211 : Blo 746329 749211 := bstep (se 1 (by rfl) ⟨561908, by rfl⟩ : syracuseStep 749211 = 1123817) B1123817
theorem B51867371 : Blo 746329 51867371 := bstep (se 1 (by rfl) ⟨38900528, by rfl⟩ : syracuseStep 51867371 = 77801057) B77801057
theorem B749659 : Blo 746329 749659 := bstep (se 1 (by rfl) ⟨562244, by rfl⟩ : syracuseStep 749659 = 1124489) B1124489
theorem B7663859 : Blo 746329 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B750015 : Blo 746329 750015 := bstep (se 1 (by rfl) ⟨562511, by rfl⟩ : syracuseStep 750015 = 1125023) B1125023
theorem B946667 : Blo 746329 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B1798939 : Blo 746329 1798939 := bstep (se 1 (by rfl) ⟨1349204, by rfl⟩ : syracuseStep 1798939 = 2698409) B2698409
theorem B3797927 : Blo 746329 3797927 := bstep (se 1 (by rfl) ⟨2848445, by rfl⟩ : syracuseStep 3797927 = 5696891) B5696891
theorem B398488691 : Blo 746329 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B1898063 : Blo 746329 1898063 := bstep (se 1 (by rfl) ⟨1423547, by rfl⟩ : syracuseStep 1898063 = 2847095) B2847095
theorem B48527207 : Blo 746329 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B6388091 : Blo 746329 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B1899227 : Blo 746329 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B1801063 : Blo 746329 1801063 := bstep (se 1 (by rfl) ⟨1350797, by rfl⟩ : syracuseStep 1801063 = 2701595) B2701595
theorem B24280211 : Blo 746329 24280211 := bstep (se 1 (by rfl) ⟨18210158, by rfl⟩ : syracuseStep 24280211 = 36420317) B36420317
theorem B3079403 : Blo 746329 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B1802303 : Blo 746329 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B1802495 : Blo 746329 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B2524445 : Blo 746329 2524445 := bstep (se 3 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 2524445 = 946667) B946667
theorem B2132041 : Blo 746329 2132041 := bstep (se 2 (by rfl) ⟨799515, by rfl⟩ : syracuseStep 2132041 = 1599031) B1599031
theorem B23333225 : Blo 746329 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B2394971 : Blo 746329 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B1062636509 : Blo 746329 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B5672591 : Blo 746329 5672591 := bstep (se 1 (by rfl) ⟨4254443, by rfl⟩ : syracuseStep 5672591 = 8508887) B8508887
theorem B32411339 : Blo 746329 32411339 := bstep (se 1 (by rfl) ⟨24308504, by rfl⟩ : syracuseStep 32411339 = 48617009) B48617009
theorem B2528063 : Blo 746329 2528063 := bstep (se 1 (by rfl) ⟨1896047, by rfl⟩ : syracuseStep 2528063 = 3792095) B3792095
theorem B1119791 : Blo 746329 1119791 := bstep (se 1 (by rfl) ⟨839843, by rfl⟩ : syracuseStep 1119791 = 1679687) B1679687
theorem B1119935 : Blo 746329 1119935 := bstep (se 1 (by rfl) ⟨839951, by rfl⟩ : syracuseStep 1119935 = 1679903) B1679903
theorem B1119983 : Blo 746329 1119983 := bstep (se 1 (by rfl) ⟨839987, by rfl⟩ : syracuseStep 1119983 = 1679975) B1679975
theorem B1120283 : Blo 746329 1120283 := bstep (se 1 (by rfl) ⟨840212, by rfl⟩ : syracuseStep 1120283 = 1680425) B1680425
theorem B1120487 : Blo 746329 1120487 := bstep (se 1 (by rfl) ⟨840365, by rfl⟩ : syracuseStep 1120487 = 1680731) B1680731
theorem B2398585 : Blo 746329 2398585 := bstep (se 2 (by rfl) ⟨899469, by rfl⟩ : syracuseStep 2398585 = 1798939) B1798939
theorem B1121435 : Blo 746329 1121435 := bstep (se 1 (by rfl) ⟨841076, by rfl⟩ : syracuseStep 1121435 = 1682153) B1682153
theorem B1121657 : Blo 746329 1121657 := bstep (se 2 (by rfl) ⟨420621, by rfl⟩ : syracuseStep 1121657 = 841243) B841243
theorem B1121999 : Blo 746329 1121999 := bstep (se 1 (by rfl) ⟨841499, by rfl⟩ : syracuseStep 1121999 = 1682999) B1682999
theorem B34578247 : Blo 746329 34578247 := bstep (se 1 (by rfl) ⟨25933685, by rfl⟩ : syracuseStep 34578247 = 51867371) B51867371
theorem B1122287 : Blo 746329 1122287 := bstep (se 1 (by rfl) ⟨841715, by rfl⟩ : syracuseStep 1122287 = 1683431) B1683431
theorem B1122335 : Blo 746329 1122335 := bstep (se 1 (by rfl) ⟨841751, by rfl⟩ : syracuseStep 1122335 = 1683503) B1683503
theorem B1122539 : Blo 746329 1122539 := bstep (se 1 (by rfl) ⟨841904, by rfl⟩ : syracuseStep 1122539 = 1683809) B1683809
theorem B1122587 : Blo 746329 1122587 := bstep (se 1 (by rfl) ⟨841940, by rfl⟩ : syracuseStep 1122587 = 1683881) B1683881
theorem B2531951 : Blo 746329 2531951 := bstep (se 1 (by rfl) ⟨1898963, by rfl⟩ : syracuseStep 2531951 = 3797927) B3797927
theorem B1123439 : Blo 746329 1123439 := bstep (se 1 (by rfl) ⟨842579, by rfl⟩ : syracuseStep 1123439 = 1685159) B1685159
theorem B2401417 : Blo 746329 2401417 := bstep (se 2 (by rfl) ⟨900531, by rfl⟩ : syracuseStep 2401417 = 1801063) B1801063
theorem B32351471 : Blo 746329 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B1123967 : Blo 746329 1123967 := bstep (se 1 (by rfl) ⟨842975, by rfl⟩ : syracuseStep 1123967 = 1685951) B1685951
theorem B1124729 : Blo 746329 1124729 := bstep (se 2 (by rfl) ⟨421773, by rfl⟩ : syracuseStep 1124729 = 843547) B843547
theorem B1125071 : Blo 746329 1125071 := bstep (se 1 (by rfl) ⟨843803, by rfl⟩ : syracuseStep 1125071 = 1687607) B1687607
theorem B6008327 : Blo 746329 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B4271849 : Blo 746329 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B7188601 : Blo 746329 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B14365673 : Blo 746329 14365673 := bstep (se 2 (by rfl) ⟨5387127, by rfl⟩ : syracuseStep 14365673 = 10774255) B10774255
theorem B5682311 : Blo 746329 5682311 := bstep (se 1 (by rfl) ⟨4261733, by rfl⟩ : syracuseStep 5682311 = 8523467) B8523467
theorem B2275103 : Blo 746329 2275103 := bstep (se 1 (by rfl) ⟨1706327, by rfl⟩ : syracuseStep 2275103 = 3412655) B3412655
theorem B20428631 : Blo 746329 20428631 := bstep (se 1 (by rfl) ⟨15321473, by rfl⟩ : syracuseStep 20428631 = 30642947) B30642947
theorem B13679225 : Blo 746329 13679225 := bstep (se 2 (by rfl) ⟨5129709, by rfl⟩ : syracuseStep 13679225 = 10259419) B10259419
theorem B1686383 : Blo 746329 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B8076455 : Blo 746329 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B1686779 : Blo 746329 1686779 := bstep (se 1 (by rfl) ⟨1265084, by rfl⟩ : syracuseStep 1686779 = 2530169) B2530169
theorem B1686905 : Blo 746329 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B27344303 : Blo 746329 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B1687067 : Blo 746329 1687067 := bstep (se 1 (by rfl) ⟨1265300, by rfl⟩ : syracuseStep 1687067 = 2530601) B2530601
theorem B10239671 : Blo 746329 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B1687247 : Blo 746329 1687247 := bstep (se 1 (by rfl) ⟨1265435, by rfl⟩ : syracuseStep 1687247 = 2530871) B2530871
theorem B2312155 : Blo 746329 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B4605977 : Blo 746329 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B6146171 : Blo 746329 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B1265375 : Blo 746329 1265375 := bstep (se 1 (by rfl) ⟨949031, by rfl⟩ : syracuseStep 1265375 = 1898063) B1898063
theorem B6409961 : Blo 746329 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B1266151 : Blo 746329 1266151 := bstep (se 1 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 1266151 = 1899227) B1899227
theorem B16143137 : Blo 746329 16143137 := bstep (se 2 (by rfl) ⟨6053676, by rfl⟩ : syracuseStep 16143137 = 12107353) B12107353
theorem B2052935 : Blo 746329 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1889183 : Blo 746329 1889183 := bstep (se 1 (by rfl) ⟨1416887, by rfl⟩ : syracuseStep 1889183 = 2833775) B2833775
theorem B44914031 : Blo 746329 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B1891097 : Blo 746329 1891097 := bstep (se 2 (by rfl) ⟨709161, by rfl⟩ : syracuseStep 1891097 = 1418323) B1418323
theorem B4053887 : Blo 746329 4053887 := bstep (se 1 (by rfl) ⟨3040415, by rfl⟩ : syracuseStep 4053887 = 6080831) B6080831
theorem B2842249 : Blo 746329 2842249 := bstep (se 2 (by rfl) ⟨1065843, by rfl⟩ : syracuseStep 2842249 = 2131687) B2131687
theorem B1892393 : Blo 746329 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B3040091 : Blo 746329 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B746751 : Blo 746329 746751 := bstep (se 1 (by rfl) ⟨560063, by rfl⟩ : syracuseStep 746751 = 1120127) B1120127
theorem B17524255 : Blo 746329 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B747215 : Blo 746329 747215 := bstep (se 1 (by rfl) ⟨560411, by rfl⟩ : syracuseStep 747215 = 1120823) B1120823
theorem B32401295 : Blo 746329 32401295 := bstep (se 1 (by rfl) ⟨24300971, by rfl⟩ : syracuseStep 32401295 = 48601943) B48601943
theorem B46819295 : Blo 746329 46819295 := bstep (se 1 (by rfl) ⟨35114471, by rfl⟩ : syracuseStep 46819295 = 70228943) B70228943
theorem B747647 : Blo 746329 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B747751 : Blo 746329 747751 := bstep (se 1 (by rfl) ⟨560813, by rfl⟩ : syracuseStep 747751 = 1121627) B1121627
theorem B1796843 : Blo 746329 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B748271 : Blo 746329 748271 := bstep (se 1 (by rfl) ⟨561203, by rfl⟩ : syracuseStep 748271 = 1122407) B1122407
theorem B748415 : Blo 746329 748415 := bstep (se 1 (by rfl) ⟨561311, by rfl⟩ : syracuseStep 748415 = 1122623) B1122623
theorem B12807071 : Blo 746329 12807071 := bstep (se 1 (by rfl) ⟨9605303, by rfl⟩ : syracuseStep 12807071 = 19210607) B19210607
theorem B1895359 : Blo 746329 1895359 := bstep (se 1 (by rfl) ⟨1421519, by rfl⟩ : syracuseStep 1895359 = 2843039) B2843039
theorem B1896655 : Blo 746329 1896655 := bstep (se 1 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 1896655 = 2844983) B2844983
theorem B750235 : Blo 746329 750235 := bstep (se 1 (by rfl) ⟨562676, by rfl⟩ : syracuseStep 750235 = 1125353) B1125353
theorem B750271 : Blo 746329 750271 := bstep (se 1 (by rfl) ⟨562703, by rfl⟩ : syracuseStep 750271 = 1125407) B1125407
theorem B2126675 : Blo 746329 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B5109239 : Blo 746329 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B2520935 : Blo 746329 2520935 := bstep (se 1 (by rfl) ⟨1890701, by rfl⟩ : syracuseStep 2520935 = 3781403) B3781403
theorem B2521313 : Blo 746329 2521313 := bstep (se 2 (by rfl) ⟨945492, by rfl⟩ : syracuseStep 2521313 = 1890985) B1890985
theorem B1898873 : Blo 746329 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B40925573 : Blo 746329 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B5536253 : Blo 746329 5536253 := bstep (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) B2076095
theorem B4258727 : Blo 746329 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B2129159 : Blo 746329 2129159 := bstep (se 1 (by rfl) ⟨1596869, by rfl⟩ : syracuseStep 2129159 = 3193739) B3193739
theorem B2522447 : Blo 746329 2522447 := bstep (se 1 (by rfl) ⟨1891835, by rfl⟩ : syracuseStep 2522447 = 3783671) B3783671
theorem B16186807 : Blo 746329 16186807 := bstep (se 1 (by rfl) ⟨12140105, by rfl⟩ : syracuseStep 16186807 = 24280211) B24280211
theorem B40992581 : Blo 746329 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B4097447 : Blo 746329 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B23365673 : Blo 746329 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B5671133 : Blo 746329 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B3082873 : Blo 746329 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B2527145 : Blo 746329 2527145 := bstep (se 2 (by rfl) ⟨947679, by rfl⟩ : syracuseStep 2527145 = 1895359) B1895359
theorem B2528873 : Blo 746329 2528873 := bstep (se 2 (by rfl) ⟨948327, by rfl⟩ : syracuseStep 2528873 = 1896655) B1896655
theorem B21567647 : Blo 746329 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B21600863 : Blo 746329 21600863 := bstep (se 1 (by rfl) ⟨16200647, by rfl⟩ : syracuseStep 21600863 = 32401295) B32401295
theorem B4791581 : Blo 746329 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B4005551 : Blo 746329 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B9577115 : Blo 746329 9577115 := bstep (se 1 (by rfl) ⟨7182836, by rfl⟩ : syracuseStep 9577115 = 14365673) B14365673
theorem B1516735 : Blo 746329 1516735 := bstep (se 1 (by rfl) ⟨1137551, by rfl⟩ : syracuseStep 1516735 = 2275103) B2275103
theorem B1680623 : Blo 746329 1680623 := bstep (se 1 (by rfl) ⟨1260467, by rfl⟩ : syracuseStep 1680623 = 2520935) B2520935
theorem B1680875 : Blo 746329 1680875 := bstep (se 1 (by rfl) ⟨1260656, by rfl⟩ : syracuseStep 1680875 = 2521313) B2521313
theorem B9119483 : Blo 746329 9119483 := bstep (se 1 (by rfl) ⟨6839612, by rfl⟩ : syracuseStep 9119483 = 13679225) B13679225
theorem B1124255 : Blo 746329 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B5384303 : Blo 746329 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B1124519 : Blo 746329 1124519 := bstep (se 1 (by rfl) ⟨843389, by rfl⟩ : syracuseStep 1124519 = 1686779) B1686779
theorem B1419439 : Blo 746329 1419439 := bstep (se 1 (by rfl) ⟨1064579, by rfl⟩ : syracuseStep 1419439 = 2129159) B2129159
theorem B1681631 : Blo 746329 1681631 := bstep (se 1 (by rfl) ⟨1261223, by rfl⟩ : syracuseStep 1681631 = 2522447) B2522447
theorem B1124603 : Blo 746329 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B18229535 : Blo 746329 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1124711 : Blo 746329 1124711 := bstep (se 1 (by rfl) ⟨843533, by rfl⟩ : syracuseStep 1124711 = 1687067) B1687067
theorem B6826447 : Blo 746329 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B1124831 : Blo 746329 1124831 := bstep (se 1 (by rfl) ⟨843623, by rfl⟩ : syracuseStep 1124831 = 1687247) B1687247
theorem B1682963 : Blo 746329 1682963 := bstep (se 1 (by rfl) ⟨1262222, by rfl⟩ : syracuseStep 1682963 = 2524445) B2524445
theorem B3781727 : Blo 746329 3781727 := bstep (se 1 (by rfl) ⟨2836295, by rfl⟩ : syracuseStep 3781727 = 5672591) B5672591
theorem B21607559 : Blo 746329 21607559 := bstep (se 1 (by rfl) ⟨16205669, by rfl⟩ : syracuseStep 21607559 = 32411339) B32411339
theorem B4273307 : Blo 746329 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B10762091 : Blo 746329 10762091 := bstep (se 1 (by rfl) ⟨8071568, by rfl⟩ : syracuseStep 10762091 = 16143137) B16143137
theorem B1685375 : Blo 746329 1685375 := bstep (se 1 (by rfl) ⟨1264031, by rfl⟩ : syracuseStep 1685375 = 2528063) B2528063
theorem B1259455 : Blo 746329 1259455 := bstep (se 1 (by rfl) ⟨944591, by rfl⟩ : syracuseStep 1259455 = 1889183) B1889183
theorem B1260731 : Blo 746329 1260731 := bstep (se 1 (by rfl) ⟨945548, by rfl⟩ : syracuseStep 1260731 = 1891097) B1891097
theorem B2702591 : Blo 746329 2702591 := bstep (se 1 (by rfl) ⟨2026943, by rfl⟩ : syracuseStep 2702591 = 4053887) B4053887
theorem B1261595 : Blo 746329 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B9584801 : Blo 746329 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B1687967 : Blo 746329 1687967 := bstep (se 1 (by rfl) ⟨1265975, by rfl⟩ : syracuseStep 1687967 = 2531951) B2531951
theorem B1688201 : Blo 746329 1688201 := bstep (se 2 (by rfl) ⟨633075, by rfl⟩ : syracuseStep 1688201 = 1266151) B1266151
theorem B31212863 : Blo 746329 31212863 := bstep (se 1 (by rfl) ⟨23409647, by rfl⟩ : syracuseStep 31212863 = 46819295) B46819295
theorem B8538047 : Blo 746329 8538047 := bstep (se 1 (by rfl) ⟨6403535, by rfl⟩ : syracuseStep 8538047 = 12807071) B12807071
theorem B2833697357 : Blo 746329 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B3198113 : Blo 746329 3198113 := bstep (se 2 (by rfl) ⟨1199292, by rfl⟩ : syracuseStep 3198113 = 2398585) B2398585
theorem B3788207 : Blo 746329 3788207 := bstep (se 1 (by rfl) ⟨2841155, by rfl⟩ : syracuseStep 3788207 = 5682311) B5682311
theorem B13619087 : Blo 746329 13619087 := bstep (se 1 (by rfl) ⟨10214315, by rfl⟩ : syracuseStep 13619087 = 20428631) B20428631
theorem B1265915 : Blo 746329 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B27283715 : Blo 746329 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B3690835 : Blo 746329 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B21582409 : Blo 746329 21582409 := bstep (se 2 (by rfl) ⟨8093403, by rfl⟩ : syracuseStep 21582409 = 16186807) B16186807
theorem B2839151 : Blo 746329 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B3789665 : Blo 746329 3789665 := bstep (se 2 (by rfl) ⟨1421124, by rfl⟩ : syracuseStep 3789665 = 2842249) B2842249
theorem B1201535 : Blo 746329 1201535 := bstep (se 1 (by rfl) ⟨901151, by rfl⟩ : syracuseStep 1201535 = 1802303) B1802303
theorem B1201663 : Blo 746329 1201663 := bstep (se 1 (by rfl) ⟨901247, by rfl⟩ : syracuseStep 1201663 = 1802495) B1802495
theorem B3070651 : Blo 746329 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B3201889 : Blo 746329 3201889 := bstep (se 2 (by rfl) ⟨1200708, by rfl⟩ : syracuseStep 3201889 = 2401417) B2401417
theorem B1596647 : Blo 746329 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B843583 : Blo 746329 843583 := bstep (se 1 (by rfl) ⟨632687, by rfl⟩ : syracuseStep 843583 = 1265375) B1265375
theorem B2842721 : Blo 746329 2842721 := bstep (se 2 (by rfl) ⟨1066020, by rfl⟩ : syracuseStep 2842721 = 2132041) B2132041
theorem B1368623 : Blo 746329 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B29942687 : Blo 746329 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B746527 : Blo 746329 746527 := bstep (se 1 (by rfl) ⟨559895, by rfl⟩ : syracuseStep 746527 = 1119791) B1119791
theorem B746623 : Blo 746329 746623 := bstep (se 1 (by rfl) ⟨559967, by rfl⟩ : syracuseStep 746623 = 1119935) B1119935
theorem B746655 : Blo 746329 746655 := bstep (se 1 (by rfl) ⟨559991, by rfl⟩ : syracuseStep 746655 = 1119983) B1119983
theorem B746855 : Blo 746329 746855 := bstep (se 1 (by rfl) ⟨560141, by rfl⟩ : syracuseStep 746855 = 1120283) B1120283
theorem B746991 : Blo 746329 746991 := bstep (se 1 (by rfl) ⟨560243, by rfl⟩ : syracuseStep 746991 = 1120487) B1120487
theorem B747623 : Blo 746329 747623 := bstep (se 1 (by rfl) ⟨560717, by rfl⟩ : syracuseStep 747623 = 1121435) B1121435
theorem B747771 : Blo 746329 747771 := bstep (se 1 (by rfl) ⟨560828, by rfl⟩ : syracuseStep 747771 = 1121657) B1121657
theorem B747999 : Blo 746329 747999 := bstep (se 1 (by rfl) ⟨560999, by rfl⟩ : syracuseStep 747999 = 1121999) B1121999
theorem B748191 : Blo 746329 748191 := bstep (se 1 (by rfl) ⟨561143, by rfl⟩ : syracuseStep 748191 = 1122287) B1122287
theorem B748223 : Blo 746329 748223 := bstep (se 1 (by rfl) ⟨561167, by rfl⟩ : syracuseStep 748223 = 1122335) B1122335
theorem B748359 : Blo 746329 748359 := bstep (se 1 (by rfl) ⟨561269, by rfl⟩ : syracuseStep 748359 = 1122539) B1122539
theorem B748391 : Blo 746329 748391 := bstep (se 1 (by rfl) ⟨561293, by rfl⟩ : syracuseStep 748391 = 1122587) B1122587
theorem B2026727 : Blo 746329 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B748959 : Blo 746329 748959 := bstep (se 1 (by rfl) ⟨561719, by rfl⟩ : syracuseStep 748959 = 1123439) B1123439
theorem B62221933 : Blo 746329 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B749311 : Blo 746329 749311 := bstep (se 1 (by rfl) ⟨561983, by rfl⟩ : syracuseStep 749311 = 1123967) B1123967
theorem B749819 : Blo 746329 749819 := bstep (se 1 (by rfl) ⟨562364, by rfl⟩ : syracuseStep 749819 = 1124729) B1124729
theorem B750047 : Blo 746329 750047 := bstep (se 1 (by rfl) ⟨562535, by rfl⟩ : syracuseStep 750047 = 1125071) B1125071
theorem B2847899 : Blo 746329 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B3406159 : Blo 746329 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B46104329 : Blo 746329 46104329 := bstep (se 2 (by rfl) ⟨17289123, by rfl⟩ : syracuseStep 46104329 = 34578247) B34578247
theorem B27328387 : Blo 746329 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B6389867 : Blo 746329 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B20808575 : Blo 746329 20808575 := bstep (se 1 (by rfl) ⟨15606431, by rfl⟩ : syracuseStep 20808575 = 31212863) B31212863
theorem B2132075 : Blo 746329 2132075 := bstep (se 1 (by rfl) ⟨1599056, by rfl⟩ : syracuseStep 2132075 = 3198113) B3198113
theorem B2525471 : Blo 746329 2525471 := bstep (se 1 (by rfl) ⟨1894103, by rfl⟩ : syracuseStep 2525471 = 3788207) B3788207
theorem B9079391 : Blo 746329 9079391 := bstep (se 1 (by rfl) ⟨6809543, by rfl⟩ : syracuseStep 9079391 = 13619087) B13619087
theorem B18189143 : Blo 746329 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B2526443 : Blo 746329 2526443 := bstep (se 1 (by rfl) ⟨1894832, by rfl⟩ : syracuseStep 2526443 = 3789665) B3789665
theorem B28776545 : Blo 746329 28776545 := bstep (se 2 (by rfl) ⟨10791204, by rfl⟩ : syracuseStep 28776545 = 21582409) B21582409
theorem B1120415 : Blo 746329 1120415 := bstep (se 1 (by rfl) ⟨840311, by rfl⟩ : syracuseStep 1120415 = 1680623) B1680623
theorem B1120583 : Blo 746329 1120583 := bstep (se 1 (by rfl) ⟨840437, by rfl⟩ : syracuseStep 1120583 = 1680875) B1680875
theorem B1121087 : Blo 746329 1121087 := bstep (se 1 (by rfl) ⟨840815, by rfl⟩ : syracuseStep 1121087 = 1681631) B1681631
theorem B1351151 : Blo 746329 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B1121975 : Blo 746329 1121975 := bstep (se 1 (by rfl) ⟨841481, by rfl⟩ : syracuseStep 1121975 = 1682963) B1682963
theorem B1679273 : Blo 746329 1679273 := bstep (se 2 (by rfl) ⟨629727, by rfl⟩ : syracuseStep 1679273 = 1259455) B1259455
theorem B4269185 : Blo 746329 4269185 := bstep (se 2 (by rfl) ⟨1600944, by rfl⟩ : syracuseStep 4269185 = 3201889) B3201889
theorem B1123583 : Blo 746329 1123583 := bstep (se 1 (by rfl) ⟨842687, by rfl⟩ : syracuseStep 1123583 = 1685375) B1685375
theorem B1124777 : Blo 746329 1124777 := bstep (se 2 (by rfl) ⟨421791, by rfl⟩ : syracuseStep 1124777 = 843583) B843583
theorem B1125311 : Blo 746329 1125311 := bstep (se 1 (by rfl) ⟨843983, by rfl⟩ : syracuseStep 1125311 = 1687967) B1687967
theorem B1125467 : Blo 746329 1125467 := bstep (se 1 (by rfl) ⟨844100, by rfl⟩ : syracuseStep 1125467 = 1688201) B1688201
theorem B15577115 : Blo 746329 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B3780755 : Blo 746329 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B1684763 : Blo 746329 1684763 := bstep (se 1 (by rfl) ⟨1263572, by rfl⟩ : syracuseStep 1684763 = 2527145) B2527145
theorem B4110497 : Blo 746329 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B801023 : Blo 746329 801023 := bstep (se 1 (by rfl) ⟨600767, by rfl⟩ : syracuseStep 801023 = 1201535) B1201535
theorem B1685915 : Blo 746329 1685915 := bstep (se 1 (by rfl) ⟨1264436, by rfl⟩ : syracuseStep 1685915 = 2528873) B2528873
theorem B14400575 : Blo 746329 14400575 := bstep (se 1 (by rfl) ⟨10800431, by rfl⟩ : syracuseStep 14400575 = 21600863) B21600863
theorem B1064431 : Blo 746329 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B3194387 : Blo 746329 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B6079655 : Blo 746329 6079655 := bstep (se 1 (by rfl) ⟨4559741, by rfl⟩ : syracuseStep 6079655 = 9119483) B9119483
theorem B3589535 : Blo 746329 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B4541545 : Blo 746329 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B14405039 : Blo 746329 14405039 := bstep (se 1 (by rfl) ⟨10803779, by rfl⟩ : syracuseStep 14405039 = 21607559) B21607559
theorem B840487 : Blo 746329 840487 := bstep (se 1 (by rfl) ⟨630365, by rfl⟩ : syracuseStep 840487 = 1260731) B1260731
theorem B841063 : Blo 746329 841063 := bstep (se 1 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 841063 = 1261595) B1261595
theorem B5692031 : Blo 746329 5692031 := bstep (se 1 (by rfl) ⟨4269023, by rfl⟩ : syracuseStep 5692031 = 8538047) B8538047
theorem B1889131571 : Blo 746329 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B19684453 : Blo 746329 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B79847165 : Blo 746329 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B843943 : Blo 746329 843943 := bstep (se 1 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 843943 = 1265915) B1265915
theorem B1892585 : Blo 746329 1892585 := bstep (se 2 (by rfl) ⟨709719, by rfl⟩ : syracuseStep 1892585 = 1419439) B1419439
theorem B1892767 : Blo 746329 1892767 := bstep (se 1 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 1892767 = 2839151) B2839151
theorem B9101929 : Blo 746329 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B14378431 : Blo 746329 14378431 := bstep (se 1 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 14378431 = 21567647) B21567647
theorem B43706101 : Blo 746329 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B82962577 : Blo 746329 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B1895147 : Blo 746329 1895147 := bstep (se 1 (by rfl) ⟨1421360, by rfl⟩ : syracuseStep 1895147 = 2842721) B2842721
theorem B912415 : Blo 746329 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B6384743 : Blo 746329 6384743 := bstep (se 1 (by rfl) ⟨4788557, by rfl⟩ : syracuseStep 6384743 = 9577115) B9577115
theorem B8089253 : Blo 746329 8089253 := bstep (se 4 (by rfl) ⟨758367, by rfl⟩ : syracuseStep 8089253 = 1516735) B1516735
theorem B749503 : Blo 746329 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B749679 : Blo 746329 749679 := bstep (se 1 (by rfl) ⟨562259, by rfl⟩ : syracuseStep 749679 = 1124519) B1124519
theorem B749735 : Blo 746329 749735 := bstep (se 1 (by rfl) ⟨562301, by rfl⟩ : syracuseStep 749735 = 1124603) B1124603
theorem B12153023 : Blo 746329 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B749807 : Blo 746329 749807 := bstep (se 1 (by rfl) ⟨562355, by rfl⟩ : syracuseStep 749807 = 1124711) B1124711
theorem B749887 : Blo 746329 749887 := bstep (se 1 (by rfl) ⟨562415, by rfl⟩ : syracuseStep 749887 = 1124831) B1124831
theorem B1602217 : Blo 746329 1602217 := bstep (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) B1201663
theorem B2521151 : Blo 746329 2521151 := bstep (se 1 (by rfl) ⟨1890863, by rfl⟩ : syracuseStep 2521151 = 3781727) B3781727
theorem B1898599 : Blo 746329 1898599 := bstep (se 1 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 1898599 = 2847899) B2847899
theorem B2848871 : Blo 746329 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B4094201 : Blo 746329 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B7174727 : Blo 746329 7174727 := bstep (se 1 (by rfl) ⟨5381045, by rfl⟩ : syracuseStep 7174727 = 10762091) B10762091
theorem B10681469 : Blo 746329 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B1801727 : Blo 746329 1801727 := bstep (se 1 (by rfl) ⟨1351295, by rfl⟩ : syracuseStep 1801727 = 2702591) B2702591
theorem B36437849 : Blo 746329 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B30736219 : Blo 746329 30736219 := bstep (se 1 (by rfl) ⟨23052164, by rfl⟩ : syracuseStep 30736219 = 46104329) B46104329
theorem B4259911 : Blo 746329 4259911 := bstep (se 1 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 4259911 = 6389867) B6389867
theorem B2523689 : Blo 746329 2523689 := bstep (se 2 (by rfl) ⟨946383, by rfl⟩ : syracuseStep 2523689 = 1892767) B1892767
theorem B2393023 : Blo 746329 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B12126095 : Blo 746329 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B19171241 : Blo 746329 19171241 := bstep (se 2 (by rfl) ⟨7189215, by rfl⟩ : syracuseStep 19171241 = 14378431) B14378431
theorem B9603359 : Blo 746329 9603359 := bstep (se 1 (by rfl) ⟨7202519, by rfl⟩ : syracuseStep 9603359 = 14405039) B14405039
theorem B1216553 : Blo 746329 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B1119515 : Blo 746329 1119515 := bstep (se 1 (by rfl) ⟨839636, by rfl⟩ : syracuseStep 1119515 = 1679273) B1679273
theorem B2136061 : Blo 746329 2136061 := bstep (se 3 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 2136061 = 801023) B801023
theorem B2136289 : Blo 746329 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B1120649 : Blo 746329 1120649 := bstep (se 2 (by rfl) ⟨420243, by rfl⟩ : syracuseStep 1120649 = 840487) B840487
theorem B1121417 : Blo 746329 1121417 := bstep (se 2 (by rfl) ⟨420531, by rfl⟩ : syracuseStep 1121417 = 841063) B841063
theorem B5676965 : Blo 746329 5676965 := bstep (se 4 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 5676965 = 1064431) B1064431
theorem B8102015 : Blo 746329 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B2531465 : Blo 746329 2531465 := bstep (se 2 (by rfl) ⟨949299, by rfl⟩ : syracuseStep 2531465 = 1898599) B1898599
theorem B1123175 : Blo 746329 1123175 := bstep (se 1 (by rfl) ⟨842381, by rfl⟩ : syracuseStep 1123175 = 1684763) B1684763
theorem B1680767 : Blo 746329 1680767 := bstep (se 1 (by rfl) ⟨1260575, by rfl⟩ : syracuseStep 1680767 = 2521151) B2521151
theorem B2729467 : Blo 746329 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B1123943 : Blo 746329 1123943 := bstep (se 1 (by rfl) ⟨842957, by rfl⟩ : syracuseStep 1123943 = 1685915) B1685915
theorem B7120979 : Blo 746329 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B24291899 : Blo 746329 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B1125257 : Blo 746329 1125257 := bstep (se 2 (by rfl) ⟨421971, by rfl⟩ : syracuseStep 1125257 = 843943) B843943
theorem B13872383 : Blo 746329 13872383 := bstep (se 1 (by rfl) ⟨10404287, by rfl⟩ : syracuseStep 13872383 = 20808575) B20808575
theorem B12135905 : Blo 746329 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B1421383 : Blo 746329 1421383 := bstep (se 1 (by rfl) ⟨1066037, by rfl⟩ : syracuseStep 1421383 = 2132075) B2132075
theorem B1683647 : Blo 746329 1683647 := bstep (se 1 (by rfl) ⟨1262735, by rfl⟩ : syracuseStep 1683647 = 2525471) B2525471
theorem B1684295 : Blo 746329 1684295 := bstep (se 1 (by rfl) ⟨1263221, by rfl⟩ : syracuseStep 1684295 = 2526443) B2526443
theorem B58274801 : Blo 746329 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B19184363 : Blo 746329 19184363 := bstep (se 1 (by rfl) ⟨14388272, by rfl⟩ : syracuseStep 19184363 = 28776545) B28776545
theorem B1259421047 : Blo 746329 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B900767 : Blo 746329 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1261723 : Blo 746329 1261723 := bstep (se 1 (by rfl) ⟨946292, by rfl⟩ : syracuseStep 1261723 = 1892585) B1892585
theorem B1263431 : Blo 746329 1263431 := bstep (se 1 (by rfl) ⟨947573, by rfl⟩ : syracuseStep 1263431 = 1895147) B1895147
theorem B5392835 : Blo 746329 5392835 := bstep (se 1 (by rfl) ⟨4044626, by rfl⟩ : syracuseStep 5392835 = 8089253) B8089253
theorem B2740331 : Blo 746329 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B1201151 : Blo 746329 1201151 := bstep (se 1 (by rfl) ⟨900863, by rfl⟩ : syracuseStep 1201151 = 1801727) B1801727
theorem B40981625 : Blo 746329 40981625 := bstep (se 2 (by rfl) ⟨15368109, by rfl⟩ : syracuseStep 40981625 = 30736219) B30736219
theorem B41538973 : Blo 746329 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B110616769 : Blo 746329 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B16212413 : Blo 746329 16212413 := bstep (se 3 (by rfl) ⟨3039827, by rfl⟩ : syracuseStep 16212413 = 6079655) B6079655
theorem B746943 : Blo 746329 746943 := bstep (se 1 (by rfl) ⟨560207, by rfl⟩ : syracuseStep 746943 = 1120415) B1120415
theorem B6055393 : Blo 746329 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B747055 : Blo 746329 747055 := bstep (se 1 (by rfl) ⟨560291, by rfl⟩ : syracuseStep 747055 = 1120583) B1120583
theorem B3794687 : Blo 746329 3794687 := bstep (se 1 (by rfl) ⟨2846015, by rfl⟩ : syracuseStep 3794687 = 5692031) B5692031
theorem B747391 : Blo 746329 747391 := bstep (se 1 (by rfl) ⟨560543, by rfl⟩ : syracuseStep 747391 = 1121087) B1121087
theorem B747983 : Blo 746329 747983 := bstep (se 1 (by rfl) ⟨560987, by rfl⟩ : syracuseStep 747983 = 1121975) B1121975
theorem B2846123 : Blo 746329 2846123 := bstep (se 1 (by rfl) ⟨2134592, by rfl⟩ : syracuseStep 2846123 = 4269185) B4269185
theorem B749055 : Blo 746329 749055 := bstep (se 1 (by rfl) ⟨561791, by rfl⟩ : syracuseStep 749055 = 1123583) B1123583
theorem B24211709 : Blo 746329 24211709 := bstep (se 3 (by rfl) ⟨4539695, by rfl⟩ : syracuseStep 24211709 = 9079391) B9079391
theorem B749851 : Blo 746329 749851 := bstep (se 1 (by rfl) ⟨562388, by rfl⟩ : syracuseStep 749851 = 1124777) B1124777
theorem B750207 : Blo 746329 750207 := bstep (se 1 (by rfl) ⟨562655, by rfl⟩ : syracuseStep 750207 = 1125311) B1125311
theorem B750311 : Blo 746329 750311 := bstep (se 1 (by rfl) ⟨562733, by rfl⟩ : syracuseStep 750311 = 1125467) B1125467
theorem B4256495 : Blo 746329 4256495 := bstep (se 1 (by rfl) ⟨3192371, by rfl⟩ : syracuseStep 4256495 = 6384743) B6384743
theorem B2520503 : Blo 746329 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B1899247 : Blo 746329 1899247 := bstep (se 1 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 1899247 = 2848871) B2848871
theorem B26245937 : Blo 746329 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B4783151 : Blo 746329 4783151 := bstep (se 1 (by rfl) ⟨3587363, by rfl⟩ : syracuseStep 4783151 = 7174727) B7174727
theorem B212925773 : Blo 746329 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B9600383 : Blo 746329 9600383 := bstep (se 1 (by rfl) ⟨7200287, by rfl⟩ : syracuseStep 9600383 = 14400575) B14400575
theorem B2129591 : Blo 746329 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B3244141 : Blo 746329 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B147489025 : Blo 746329 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B12780827 : Blo 746329 12780827 := bstep (se 1 (by rfl) ⟨9585620, by rfl⟩ : syracuseStep 12780827 = 19171241) B19171241
theorem B3639289 : Blo 746329 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B1120511 : Blo 746329 1120511 := bstep (se 1 (by rfl) ⟨840383, by rfl⟩ : syracuseStep 1120511 = 1680767) B1680767
theorem B2529791 : Blo 746329 2529791 := bstep (se 1 (by rfl) ⟨1897343, by rfl⟩ : syracuseStep 2529791 = 3794687) B3794687
theorem B16194599 : Blo 746329 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B55385297 : Blo 746329 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B9248255 : Blo 746329 9248255 := bstep (se 1 (by rfl) ⟨6936191, by rfl⟩ : syracuseStep 9248255 = 13872383) B13872383
theorem B1122431 : Blo 746329 1122431 := bstep (se 1 (by rfl) ⟨841823, by rfl⟩ : syracuseStep 1122431 = 1683647) B1683647
theorem B1122863 : Blo 746329 1122863 := bstep (se 1 (by rfl) ⟨842147, by rfl⟩ : syracuseStep 1122863 = 1684295) B1684295
theorem B1680335 : Blo 746329 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B2532329 : Blo 746329 2532329 := bstep (se 2 (by rfl) ⟨949623, by rfl⟩ : syracuseStep 2532329 = 1899247) B1899247
theorem B2402045 : Blo 746329 2402045 := bstep (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) B900767
theorem B5678909 : Blo 746329 5678909 := bstep (se 3 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 5678909 = 2129591) B2129591
theorem B12789575 : Blo 746329 12789575 := bstep (se 1 (by rfl) ⟨9592181, by rfl⟩ : syracuseStep 12789575 = 19184363) B19184363
theorem B3188767 : Blo 746329 3188767 := bstep (se 1 (by rfl) ⟨2391575, by rfl⟩ : syracuseStep 3188767 = 4783151) B4783151
theorem B6400255 : Blo 746329 6400255 := bstep (se 1 (by rfl) ⟨4800191, by rfl⟩ : syracuseStep 6400255 = 9600383) B9600383
theorem B5679881 : Blo 746329 5679881 := bstep (se 2 (by rfl) ⟨2129955, by rfl⟩ : syracuseStep 5679881 = 4259911) B4259911
theorem B1682297 : Blo 746329 1682297 := bstep (se 2 (by rfl) ⟨630861, by rfl⟩ : syracuseStep 1682297 = 1261723) B1261723
theorem B1682459 : Blo 746329 1682459 := bstep (se 1 (by rfl) ⟨1261844, by rfl⟩ : syracuseStep 1682459 = 2523689) B2523689
theorem B3190697 : Blo 746329 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B6402239 : Blo 746329 6402239 := bstep (se 1 (by rfl) ⟨4801679, by rfl⟩ : syracuseStep 6402239 = 9603359) B9603359
theorem B8073857 : Blo 746329 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B800767 : Blo 746329 800767 := bstep (se 1 (by rfl) ⟨600575, by rfl⟩ : syracuseStep 800767 = 1201151) B1201151
theorem B3784643 : Blo 746329 3784643 := bstep (se 1 (by rfl) ⟨2838482, by rfl⟩ : syracuseStep 3784643 = 5676965) B5676965
theorem B1687643 : Blo 746329 1687643 := bstep (se 1 (by rfl) ⟨1265732, by rfl⟩ : syracuseStep 1687643 = 2531465) B2531465
theorem B16141139 : Blo 746329 16141139 := bstep (se 1 (by rfl) ⟨12105854, by rfl⟩ : syracuseStep 16141139 = 24211709) B24211709
theorem B2837663 : Blo 746329 2837663 := bstep (se 1 (by rfl) ⟨2128247, by rfl⟩ : syracuseStep 2837663 = 4256495) B4256495
theorem B38849867 : Blo 746329 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B842287 : Blo 746329 842287 := bstep (se 1 (by rfl) ⟨631715, by rfl⟩ : syracuseStep 842287 = 1263431) B1263431
theorem B8084063 : Blo 746329 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B3595223 : Blo 746329 3595223 := bstep (se 1 (by rfl) ⟨2696417, by rfl⟩ : syracuseStep 3595223 = 5392835) B5392835
theorem B1826887 : Blo 746329 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B27321083 : Blo 746329 27321083 := bstep (se 1 (by rfl) ⟨20490812, by rfl⟩ : syracuseStep 27321083 = 40981625) B40981625
theorem B746343 : Blo 746329 746343 := bstep (se 1 (by rfl) ⟨559757, by rfl⟩ : syracuseStep 746343 = 1119515) B1119515
theorem B747099 : Blo 746329 747099 := bstep (se 1 (by rfl) ⟨560324, by rfl⟩ : syracuseStep 747099 = 1120649) B1120649
theorem B747611 : Blo 746329 747611 := bstep (se 1 (by rfl) ⟨560708, by rfl⟩ : syracuseStep 747611 = 1121417) B1121417
theorem B5401343 : Blo 746329 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B1895177 : Blo 746329 1895177 := bstep (se 2 (by rfl) ⟨710691, by rfl⟩ : syracuseStep 1895177 = 1421383) B1421383
theorem B10808275 : Blo 746329 10808275 := bstep (se 1 (by rfl) ⟨8106206, by rfl⟩ : syracuseStep 10808275 = 16212413) B16212413
theorem B748783 : Blo 746329 748783 := bstep (se 1 (by rfl) ⟨561587, by rfl⟩ : syracuseStep 748783 = 1123175) B1123175
theorem B749295 : Blo 746329 749295 := bstep (se 1 (by rfl) ⟨561971, by rfl⟩ : syracuseStep 749295 = 1123943) B1123943
theorem B4747319 : Blo 746329 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B750171 : Blo 746329 750171 := bstep (se 1 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 750171 = 1125257) B1125257
theorem B1897415 : Blo 746329 1897415 := bstep (se 1 (by rfl) ⟨1423061, by rfl⟩ : syracuseStep 1897415 = 2846123) B2846123
theorem B8090603 : Blo 746329 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B2848081 : Blo 746329 2848081 := bstep (se 2 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 2848081 = 2136061) B2136061
theorem B2848385 : Blo 746329 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B17497291 : Blo 746329 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B141950515 : Blo 746329 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B839614031 : Blo 746329 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B4325521 : Blo 746329 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B8520551 : Blo 746329 8520551 := bstep (se 1 (by rfl) ⟨6390413, by rfl⟩ : syracuseStep 8520551 = 12780827) B12780827
theorem B21530285 : Blo 746329 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B4852385 : Blo 746329 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B6165503 : Blo 746329 6165503 := bstep (se 1 (by rfl) ⟨4624127, by rfl⟩ : syracuseStep 6165503 = 9248255) B9248255
theorem B1120223 : Blo 746329 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B8526383 : Blo 746329 8526383 := bstep (se 1 (by rfl) ⟨6394787, by rfl⟩ : syracuseStep 8526383 = 12789575) B12789575
theorem B1121531 : Blo 746329 1121531 := bstep (se 1 (by rfl) ⟨841148, by rfl⟩ : syracuseStep 1121531 = 1682297) B1682297
theorem B1121639 : Blo 746329 1121639 := bstep (se 1 (by rfl) ⟨841229, by rfl⟩ : syracuseStep 1121639 = 1682459) B1682459
theorem B4268159 : Blo 746329 4268159 := bstep (se 1 (by rfl) ⟨3201119, by rfl⟩ : syracuseStep 4268159 = 6402239) B6402239
theorem B1123049 : Blo 746329 1123049 := bstep (se 2 (by rfl) ⟨421143, by rfl⟩ : syracuseStep 1123049 = 842287) B842287
theorem B1125095 : Blo 746329 1125095 := bstep (se 1 (by rfl) ⟨843821, by rfl⟩ : syracuseStep 1125095 = 1687643) B1687643
theorem B2435849 : Blo 746329 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B196652033 : Blo 746329 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B10760759 : Blo 746329 10760759 := bstep (se 1 (by rfl) ⟨8070569, by rfl⟩ : syracuseStep 10760759 = 16141139) B16141139
theorem B25899911 : Blo 746329 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B8533673 : Blo 746329 8533673 := bstep (se 2 (by rfl) ⟨3200127, by rfl⟩ : syracuseStep 8533673 = 6400255) B6400255
theorem B1686527 : Blo 746329 1686527 := bstep (se 1 (by rfl) ⟨1264895, by rfl⟩ : syracuseStep 1686527 = 2529791) B2529791
theorem B10796399 : Blo 746329 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B1688219 : Blo 746329 1688219 := bstep (se 1 (by rfl) ⟨1266164, by rfl⟩ : syracuseStep 1688219 = 2532329) B2532329
theorem B3785939 : Blo 746329 3785939 := bstep (se 1 (by rfl) ⟨2839454, by rfl⟩ : syracuseStep 3785939 = 5678909) B5678909
theorem B3786587 : Blo 746329 3786587 := bstep (se 1 (by rfl) ⟨2839940, by rfl⟩ : syracuseStep 3786587 = 5679881) B5679881
theorem B1263451 : Blo 746329 1263451 := bstep (se 1 (by rfl) ⟨947588, by rfl⟩ : syracuseStep 1263451 = 1895177) B1895177
theorem B14403581 : Blo 746329 14403581 := bstep (se 3 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 14403581 = 5401343) B5401343
theorem B9587261 : Blo 746329 9587261 := bstep (se 3 (by rfl) ⟨1797611, by rfl⟩ : syracuseStep 9587261 = 3595223) B3595223
theorem B1067689 : Blo 746329 1067689 := bstep (se 2 (by rfl) ⟨400383, by rfl⟩ : syracuseStep 1067689 = 800767) B800767
theorem B3164879 : Blo 746329 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B1264943 : Blo 746329 1264943 := bstep (se 1 (by rfl) ⟨948707, by rfl⟩ : syracuseStep 1264943 = 1897415) B1897415
theorem B5393735 : Blo 746329 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B1891775 : Blo 746329 1891775 := bstep (se 1 (by rfl) ⟨1418831, by rfl⟩ : syracuseStep 1891775 = 2837663) B2837663
theorem B4251689 : Blo 746329 4251689 := bstep (se 2 (by rfl) ⟨1594383, by rfl⟩ : syracuseStep 4251689 = 3188767) B3188767
theorem B14411033 : Blo 746329 14411033 := bstep (se 2 (by rfl) ⟨5404137, by rfl⟩ : syracuseStep 14411033 = 10808275) B10808275
theorem B747007 : Blo 746329 747007 := bstep (se 1 (by rfl) ⟨560255, by rfl⟩ : syracuseStep 747007 = 1120511) B1120511
theorem B36923531 : Blo 746329 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B748287 : Blo 746329 748287 := bstep (se 1 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 748287 = 1122431) B1122431
theorem B748575 : Blo 746329 748575 := bstep (se 1 (by rfl) ⟨561431, by rfl⟩ : syracuseStep 748575 = 1122863) B1122863
theorem B18214055 : Blo 746329 18214055 := bstep (se 1 (by rfl) ⟨13660541, by rfl⟩ : syracuseStep 18214055 = 27321083) B27321083
theorem B1601363 : Blo 746329 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B21557501 : Blo 746329 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B3797441 : Blo 746329 3797441 := bstep (se 2 (by rfl) ⟨1424040, by rfl⟩ : syracuseStep 3797441 = 2848081) B2848081
theorem B2127131 : Blo 746329 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B1898923 : Blo 746329 1898923 := bstep (se 1 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 1898923 = 2848385) B2848385
theorem B23329721 : Blo 746329 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B189267353 : Blo 746329 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B559742687 : Blo 746329 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B2523095 : Blo 746329 2523095 := bstep (se 1 (by rfl) ⟨1892321, by rfl⟩ : syracuseStep 2523095 = 3784643) B3784643
theorem B5767361 : Blo 746329 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B2523959 : Blo 746329 2523959 := bstep (se 1 (by rfl) ⟨1892969, by rfl⟩ : syracuseStep 2523959 = 3785939) B3785939
theorem B14353523 : Blo 746329 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B2524391 : Blo 746329 2524391 := bstep (se 1 (by rfl) ⟨1893293, by rfl⟩ : syracuseStep 2524391 = 3786587) B3786587
theorem B9602387 : Blo 746329 9602387 := bstep (se 1 (by rfl) ⟨7201790, by rfl⟩ : syracuseStep 9602387 = 14403581) B14403581
theorem B6391507 : Blo 746329 6391507 := bstep (se 1 (by rfl) ⟨4793630, by rfl⟩ : syracuseStep 6391507 = 9587261) B9587261
theorem B9607355 : Blo 746329 9607355 := bstep (se 1 (by rfl) ⟨7205516, by rfl⟩ : syracuseStep 9607355 = 14411033) B14411033
theorem B2531627 : Blo 746329 2531627 := bstep (se 1 (by rfl) ⟨1898720, by rfl⟩ : syracuseStep 2531627 = 3797441) B3797441
theorem B2531897 : Blo 746329 2531897 := bstep (se 2 (by rfl) ⟨949461, by rfl⟩ : syracuseStep 2531897 = 1898923) B1898923
theorem B1418087 : Blo 746329 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1124351 : Blo 746329 1124351 := bstep (se 1 (by rfl) ⟨843263, by rfl⟩ : syracuseStep 1124351 = 1686527) B1686527
theorem B1682063 : Blo 746329 1682063 := bstep (se 1 (by rfl) ⟨1261547, by rfl⟩ : syracuseStep 1682063 = 2523095) B2523095
theorem B1125479 : Blo 746329 1125479 := bstep (se 1 (by rfl) ⟨844109, by rfl⟩ : syracuseStep 1125479 = 1688219) B1688219
theorem B5680367 : Blo 746329 5680367 := bstep (se 1 (by rfl) ⟨4260275, by rfl⟩ : syracuseStep 5680367 = 8520551) B8520551
theorem B1684601 : Blo 746329 1684601 := bstep (se 2 (by rfl) ⟨631725, by rfl⟩ : syracuseStep 1684601 = 1263451) B1263451
theorem B4110335 : Blo 746329 4110335 := bstep (se 1 (by rfl) ⟨3082751, by rfl⟩ : syracuseStep 4110335 = 6165503) B6165503
theorem B1423585 : Blo 746329 1423585 := bstep (se 2 (by rfl) ⟨533844, by rfl⟩ : syracuseStep 1423585 = 1067689) B1067689
theorem B5684255 : Blo 746329 5684255 := bstep (se 1 (by rfl) ⟨4263191, by rfl⟩ : syracuseStep 5684255 = 8526383) B8526383
theorem B1261183 : Blo 746329 1261183 := bstep (se 1 (by rfl) ⟨945887, by rfl⟩ : syracuseStep 1261183 = 1891775) B1891775
theorem B2834459 : Blo 746329 2834459 := bstep (se 1 (by rfl) ⟨2125844, by rfl⟩ : syracuseStep 2834459 = 4251689) B4251689
theorem B1623899 : Blo 746329 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B8439677 : Blo 746329 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B12142703 : Blo 746329 12142703 := bstep (se 1 (by rfl) ⟨9107027, by rfl⟩ : syracuseStep 12142703 = 18214055) B18214055
theorem B1067575 : Blo 746329 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B14371667 : Blo 746329 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B5689115 : Blo 746329 5689115 := bstep (se 1 (by rfl) ⟨4266836, by rfl⟩ : syracuseStep 5689115 = 8533673) B8533673
theorem B15553147 : Blo 746329 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B7197599 : Blo 746329 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B126178235 : Blo 746329 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B3234923 : Blo 746329 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B843295 : Blo 746329 843295 := bstep (se 1 (by rfl) ⟨632471, by rfl⟩ : syracuseStep 843295 = 1264943) B1264943
theorem B3595823 : Blo 746329 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B746815 : Blo 746329 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B747687 : Blo 746329 747687 := bstep (se 1 (by rfl) ⟨560765, by rfl⟩ : syracuseStep 747687 = 1121531) B1121531
theorem B747759 : Blo 746329 747759 := bstep (se 1 (by rfl) ⟨560819, by rfl⟩ : syracuseStep 747759 = 1121639) B1121639
theorem B2845439 : Blo 746329 2845439 := bstep (se 1 (by rfl) ⟨2134079, by rfl⟩ : syracuseStep 2845439 = 4268159) B4268159
theorem B98462749 : Blo 746329 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B748699 : Blo 746329 748699 := bstep (se 1 (by rfl) ⟨561524, by rfl⟩ : syracuseStep 748699 = 1123049) B1123049
theorem B750063 : Blo 746329 750063 := bstep (se 1 (by rfl) ⟨562547, by rfl⟩ : syracuseStep 750063 = 1125095) B1125095
theorem B131101355 : Blo 746329 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B7173839 : Blo 746329 7173839 := bstep (se 1 (by rfl) ⟨5380379, by rfl⟩ : syracuseStep 7173839 = 10760759) B10760759
theorem B17266607 : Blo 746329 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B373161791 : Blo 746329 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B9569015 : Blo 746329 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B8095135 : Blo 746329 8095135 := bstep (se 1 (by rfl) ⟨6071351, by rfl⟩ : syracuseStep 8095135 = 12142703) B12142703
theorem B8522009 : Blo 746329 8522009 := bstep (se 2 (by rfl) ⟨3195753, by rfl⟩ : syracuseStep 8522009 = 6391507) B6391507
theorem B84118823 : Blo 746329 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B4330397 : Blo 746329 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B2397215 : Blo 746329 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B1121375 : Blo 746329 1121375 := bstep (se 1 (by rfl) ⟨841031, by rfl⟩ : syracuseStep 1121375 = 1682063) B1682063
theorem B87400903 : Blo 746329 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B1123067 : Blo 746329 1123067 := bstep (se 1 (by rfl) ⟨842300, by rfl⟩ : syracuseStep 1123067 = 1684601) B1684601
theorem B11511071 : Blo 746329 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B1124393 : Blo 746329 1124393 := bstep (se 2 (by rfl) ⟨421647, by rfl⟩ : syracuseStep 1124393 = 843295) B843295
theorem B1681577 : Blo 746329 1681577 := bstep (se 2 (by rfl) ⟨630591, by rfl⟩ : syracuseStep 1681577 = 1261183) B1261183
theorem B3844907 : Blo 746329 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B1682639 : Blo 746329 1682639 := bstep (se 1 (by rfl) ⟨1261979, by rfl⟩ : syracuseStep 1682639 = 2523959) B2523959
theorem B1682927 : Blo 746329 1682927 := bstep (se 1 (by rfl) ⟨1262195, by rfl⟩ : syracuseStep 1682927 = 2524391) B2524391
theorem B6401591 : Blo 746329 6401591 := bstep (se 1 (by rfl) ⟨4801193, by rfl⟩ : syracuseStep 6401591 = 9602387) B9602387
theorem B9581111 : Blo 746329 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B3781565 : Blo 746329 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B4798399 : Blo 746329 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B1423433 : Blo 746329 1423433 := bstep (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) B1067575
theorem B131283665 : Blo 746329 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B6404903 : Blo 746329 6404903 := bstep (se 1 (by rfl) ⟨4803677, by rfl⟩ : syracuseStep 6404903 = 9607355) B9607355
theorem B1687751 : Blo 746329 1687751 := bstep (se 1 (by rfl) ⟨1265813, by rfl⟩ : syracuseStep 1687751 = 2531627) B2531627
theorem B1687931 : Blo 746329 1687931 := bstep (se 1 (by rfl) ⟨1265948, by rfl⟩ : syracuseStep 1687931 = 2531897) B2531897
theorem B3786911 : Blo 746329 3786911 := bstep (se 1 (by rfl) ⟨2840183, by rfl⟩ : syracuseStep 3786911 = 5680367) B5680367
theorem B2740223 : Blo 746329 2740223 := bstep (se 1 (by rfl) ⟨2055167, by rfl⟩ : syracuseStep 2740223 = 4110335) B4110335
theorem B3789503 : Blo 746329 3789503 := bstep (se 1 (by rfl) ⟨2842127, by rfl⟩ : syracuseStep 3789503 = 5684255) B5684255
theorem B1889639 : Blo 746329 1889639 := bstep (se 1 (by rfl) ⟨1417229, by rfl⟩ : syracuseStep 1889639 = 2834459) B2834459
theorem B5626451 : Blo 746329 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B3792743 : Blo 746329 3792743 := bstep (se 1 (by rfl) ⟨2844557, by rfl⟩ : syracuseStep 3792743 = 5689115) B5689115
theorem B2156615 : Blo 746329 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B20737529 : Blo 746329 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B749567 : Blo 746329 749567 := bstep (se 1 (by rfl) ⟨562175, by rfl⟩ : syracuseStep 749567 = 1124351) B1124351
theorem B1896959 : Blo 746329 1896959 := bstep (se 1 (by rfl) ⟨1422719, by rfl⟩ : syracuseStep 1896959 = 2845439) B2845439
theorem B750319 : Blo 746329 750319 := bstep (se 1 (by rfl) ⟨562739, by rfl⟩ : syracuseStep 750319 = 1125479) B1125479
theorem B1898113 : Blo 746329 1898113 := bstep (se 2 (by rfl) ⟨711792, by rfl⟩ : syracuseStep 1898113 = 1423585) B1423585
theorem B4782559 : Blo 746329 4782559 := bstep (se 1 (by rfl) ⟨3586919, by rfl⟩ : syracuseStep 4782559 = 7173839) B7173839
theorem B248774527 : Blo 746329 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B2524607 : Blo 746329 2524607 := bstep (se 1 (by rfl) ⟨1893455, by rfl⟩ : syracuseStep 2524607 = 3786911) B3786911
theorem B2526335 : Blo 746329 2526335 := bstep (se 1 (by rfl) ⟨1894751, by rfl⟩ : syracuseStep 2526335 = 3789503) B3789503
theorem B2886931 : Blo 746329 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B2528495 : Blo 746329 2528495 := bstep (se 1 (by rfl) ⟨1896371, by rfl⟩ : syracuseStep 2528495 = 3792743) B3792743
theorem B7674047 : Blo 746329 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B1121051 : Blo 746329 1121051 := bstep (se 1 (by rfl) ⟨840788, by rfl⟩ : syracuseStep 1121051 = 1681577) B1681577
theorem B2563271 : Blo 746329 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B1121759 : Blo 746329 1121759 := bstep (se 1 (by rfl) ⟨841319, by rfl⟩ : syracuseStep 1121759 = 1682639) B1682639
theorem B2530817 : Blo 746329 2530817 := bstep (se 2 (by rfl) ⟨949056, by rfl⟩ : syracuseStep 2530817 = 1898113) B1898113
theorem B1121951 : Blo 746329 1121951 := bstep (se 1 (by rfl) ⟨841463, by rfl⟩ : syracuseStep 1121951 = 1682927) B1682927
theorem B4267727 : Blo 746329 4267727 := bstep (se 1 (by rfl) ⟨3200795, by rfl⟩ : syracuseStep 4267727 = 6401591) B6401591
theorem B6397865 : Blo 746329 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B4269935 : Blo 746329 4269935 := bstep (se 1 (by rfl) ⟨3202451, by rfl⟩ : syracuseStep 4269935 = 6404903) B6404903
theorem B1125167 : Blo 746329 1125167 := bstep (se 1 (by rfl) ⟨843875, by rfl⟩ : syracuseStep 1125167 = 1687751) B1687751
theorem B1125287 : Blo 746329 1125287 := bstep (se 1 (by rfl) ⟨843965, by rfl⟩ : syracuseStep 1125287 = 1687931) B1687931
theorem B116534537 : Blo 746329 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B5681339 : Blo 746329 5681339 := bstep (se 1 (by rfl) ⟨4261004, by rfl⟩ : syracuseStep 5681339 = 8522009) B8522009
theorem B10793513 : Blo 746329 10793513 := bstep (se 2 (by rfl) ⟨4047567, by rfl⟩ : syracuseStep 10793513 = 8095135) B8095135
theorem B56079215 : Blo 746329 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B1259759 : Blo 746329 1259759 := bstep (se 1 (by rfl) ⟨944819, by rfl⟩ : syracuseStep 1259759 = 1889639) B1889639
theorem B3750967 : Blo 746329 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B1264639 : Blo 746329 1264639 := bstep (se 1 (by rfl) ⟨948479, by rfl⟩ : syracuseStep 1264639 = 1896959) B1896959
theorem B6376745 : Blo 746329 6376745 := bstep (se 2 (by rfl) ⟨2391279, by rfl⟩ : syracuseStep 6376745 = 4782559) B4782559
theorem B331699369 : Blo 746329 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B6379343 : Blo 746329 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B1826815 : Blo 746329 1826815 := bstep (se 1 (by rfl) ⟨1370111, by rfl⟩ : syracuseStep 1826815 = 2740223) B2740223
theorem B1598143 : Blo 746329 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B747583 : Blo 746329 747583 := bstep (se 1 (by rfl) ⟨560687, by rfl⟩ : syracuseStep 747583 = 1121375) B1121375
theorem B3795821 : Blo 746329 3795821 := bstep (se 3 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 3795821 = 1423433) B1423433
theorem B748711 : Blo 746329 748711 := bstep (se 1 (by rfl) ⟨561533, by rfl⟩ : syracuseStep 748711 = 1123067) B1123067
theorem B749595 : Blo 746329 749595 := bstep (se 1 (by rfl) ⟨562196, by rfl⟩ : syracuseStep 749595 = 1124393) B1124393
theorem B1437743 : Blo 746329 1437743 := bstep (se 1 (by rfl) ⟨1078307, by rfl⟩ : syracuseStep 1437743 = 2156615) B2156615
theorem B13825019 : Blo 746329 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B6387407 : Blo 746329 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B2521043 : Blo 746329 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B87522443 : Blo 746329 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B3833981 : Blo 746329 3833981 := bstep (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) B1437743
theorem B2130857 : Blo 746329 2130857 := bstep (se 2 (by rfl) ⟨799071, by rfl⟩ : syracuseStep 2130857 = 1598143) B1598143
theorem B5116031 : Blo 746329 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B1708847 : Blo 746329 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B4265243 : Blo 746329 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B2530547 : Blo 746329 2530547 := bstep (se 1 (by rfl) ⟨1897910, by rfl⟩ : syracuseStep 2530547 = 3795821) B3795821
theorem B9216679 : Blo 746329 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B1680695 : Blo 746329 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B2435753 : Blo 746329 2435753 := bstep (se 2 (by rfl) ⟨913407, by rfl⟩ : syracuseStep 2435753 = 1826815) B1826815
theorem B1683071 : Blo 746329 1683071 := bstep (se 1 (by rfl) ⟨1262303, by rfl⟩ : syracuseStep 1683071 = 2524607) B2524607
theorem B1684223 : Blo 746329 1684223 := bstep (se 1 (by rfl) ⟨1263167, by rfl⟩ : syracuseStep 1684223 = 2526335) B2526335
theorem B1685663 : Blo 746329 1685663 := bstep (se 1 (by rfl) ⟨1264247, by rfl⟩ : syracuseStep 1685663 = 2528495) B2528495
theorem B1686185 : Blo 746329 1686185 := bstep (se 2 (by rfl) ⟨632319, by rfl⟩ : syracuseStep 1686185 = 1264639) B1264639
theorem B3849241 : Blo 746329 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B1687211 : Blo 746329 1687211 := bstep (se 1 (by rfl) ⟨1265408, by rfl⟩ : syracuseStep 1687211 = 2530817) B2530817
theorem B20005157 : Blo 746329 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B3787559 : Blo 746329 3787559 := bstep (se 1 (by rfl) ⟨2840669, by rfl⟩ : syracuseStep 3787559 = 5681339) B5681339
theorem B7195675 : Blo 746329 7195675 := bstep (se 1 (by rfl) ⟨5396756, by rfl⟩ : syracuseStep 7195675 = 10793513) B10793513
theorem B839839 : Blo 746329 839839 := bstep (se 1 (by rfl) ⟨629879, by rfl⟩ : syracuseStep 839839 = 1259759) B1259759
theorem B58348295 : Blo 746329 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B4251163 : Blo 746329 4251163 := bstep (se 1 (by rfl) ⟨3188372, by rfl⟩ : syracuseStep 4251163 = 6376745) B6376745
theorem B4252895 : Blo 746329 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B747367 : Blo 746329 747367 := bstep (se 1 (by rfl) ⟨560525, by rfl⟩ : syracuseStep 747367 = 1121051) B1121051
theorem B747839 : Blo 746329 747839 := bstep (se 1 (by rfl) ⟨560879, by rfl⟩ : syracuseStep 747839 = 1121759) B1121759
theorem B747967 : Blo 746329 747967 := bstep (se 1 (by rfl) ⟨560975, by rfl⟩ : syracuseStep 747967 = 1121951) B1121951
theorem B2845151 : Blo 746329 2845151 := bstep (se 1 (by rfl) ⟨2133863, by rfl⟩ : syracuseStep 2845151 = 4267727) B4267727
theorem B2846623 : Blo 746329 2846623 := bstep (se 1 (by rfl) ⟨2134967, by rfl⟩ : syracuseStep 2846623 = 4269935) B4269935
theorem B442265825 : Blo 746329 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B750111 : Blo 746329 750111 := bstep (se 1 (by rfl) ⟨562583, by rfl⟩ : syracuseStep 750111 = 1125167) B1125167
theorem B750191 : Blo 746329 750191 := bstep (se 1 (by rfl) ⟨562643, by rfl⟩ : syracuseStep 750191 = 1125287) B1125287
theorem B77689691 : Blo 746329 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B37386143 : Blo 746329 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B4258271 : Blo 746329 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B2555987 : Blo 746329 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B13336771 : Blo 746329 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B12288905 : Blo 746329 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B2525039 : Blo 746329 2525039 := bstep (se 1 (by rfl) ⟨1893779, by rfl⟩ : syracuseStep 2525039 = 3787559) B3787559
theorem B3410687 : Blo 746329 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B38898863 : Blo 746329 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B1119785 : Blo 746329 1119785 := bstep (se 2 (by rfl) ⟨419919, by rfl⟩ : syracuseStep 1119785 = 839839) B839839
theorem B1120463 : Blo 746329 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B1122047 : Blo 746329 1122047 := bstep (se 1 (by rfl) ⟨841535, by rfl⟩ : syracuseStep 1122047 = 1683071) B1683071
theorem B1122815 : Blo 746329 1122815 := bstep (se 1 (by rfl) ⟨842111, by rfl⟩ : syracuseStep 1122815 = 1684223) B1684223
theorem B1123775 : Blo 746329 1123775 := bstep (se 1 (by rfl) ⟨842831, by rfl⟩ : syracuseStep 1123775 = 1685663) B1685663
theorem B1124123 : Blo 746329 1124123 := bstep (se 1 (by rfl) ⟨843092, by rfl⟩ : syracuseStep 1124123 = 1686185) B1686185
theorem B1124807 : Blo 746329 1124807 := bstep (se 1 (by rfl) ⟨843605, by rfl⟩ : syracuseStep 1124807 = 1687211) B1687211
theorem B1420571 : Blo 746329 1420571 := bstep (se 1 (by rfl) ⟨1065428, by rfl⟩ : syracuseStep 1420571 = 2130857) B2130857
theorem B1687031 : Blo 746329 1687031 := bstep (se 1 (by rfl) ⟨1265273, by rfl⟩ : syracuseStep 1687031 = 2530547) B2530547
theorem B2835263 : Blo 746329 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B1623835 : Blo 746329 1623835 := bstep (se 1 (by rfl) ⟨1217876, by rfl⟩ : syracuseStep 1623835 = 2435753) B2435753
theorem B51793127 : Blo 746329 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B24924095 : Blo 746329 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B5132321 : Blo 746329 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B2838847 : Blo 746329 2838847 := bstep (se 1 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 2838847 = 4258271) B4258271
theorem B1139231 : Blo 746329 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B2843495 : Blo 746329 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B9594233 : Blo 746329 9594233 := bstep (se 2 (by rfl) ⟨3597837, by rfl⟩ : syracuseStep 9594233 = 7195675) B7195675
theorem B3795497 : Blo 746329 3795497 := bstep (se 2 (by rfl) ⟨1423311, by rfl⟩ : syracuseStep 3795497 = 2846623) B2846623
theorem B1896767 : Blo 746329 1896767 := bstep (se 1 (by rfl) ⟨1422575, by rfl⟩ : syracuseStep 1896767 = 2845151) B2845151
theorem B294843883 : Blo 746329 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B5668217 : Blo 746329 5668217 := bstep (se 2 (by rfl) ⟨2125581, by rfl⟩ : syracuseStep 5668217 = 4251163) B4251163
theorem B8192603 : Blo 746329 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B27263861 : Blo 746329 27263861 := bstep (se 5 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 27263861 = 2555987) B2555987
theorem B2165113 : Blo 746329 2165113 := bstep (se 2 (by rfl) ⟨811917, by rfl⟩ : syracuseStep 2165113 = 1623835) B1623835
theorem B16616063 : Blo 746329 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B6396155 : Blo 746329 6396155 := bstep (se 1 (by rfl) ⟨4797116, by rfl⟩ : syracuseStep 6396155 = 9594233) B9594233
theorem B2530331 : Blo 746329 2530331 := bstep (se 1 (by rfl) ⟨1897748, by rfl⟩ : syracuseStep 2530331 = 3795497) B3795497
theorem B393125177 : Blo 746329 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B3778811 : Blo 746329 3778811 := bstep (se 1 (by rfl) ⟨2834108, by rfl⟩ : syracuseStep 3778811 = 5668217) B5668217
theorem B1124687 : Blo 746329 1124687 := bstep (se 1 (by rfl) ⟨843515, by rfl⟩ : syracuseStep 1124687 = 1687031) B1687031
theorem B1683359 : Blo 746329 1683359 := bstep (se 1 (by rfl) ⟨1262519, by rfl⟩ : syracuseStep 1683359 = 2525039) B2525039
theorem B25932575 : Blo 746329 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B3421547 : Blo 746329 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B3785129 : Blo 746329 3785129 := bstep (se 2 (by rfl) ⟨1419423, by rfl⟩ : syracuseStep 3785129 = 2838847) B2838847
theorem B9095165 : Blo 746329 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B1264511 : Blo 746329 1264511 := bstep (se 1 (by rfl) ⟨948383, by rfl⟩ : syracuseStep 1264511 = 1896767) B1896767
theorem B17782361 : Blo 746329 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B1890175 : Blo 746329 1890175 := bstep (se 1 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 1890175 = 2835263) B2835263
theorem B3037949 : Blo 746329 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B34528751 : Blo 746329 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B746523 : Blo 746329 746523 := bstep (se 1 (by rfl) ⟨559892, by rfl⟩ : syracuseStep 746523 = 1119785) B1119785
theorem B746975 : Blo 746329 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B748031 : Blo 746329 748031 := bstep (se 1 (by rfl) ⟨561023, by rfl⟩ : syracuseStep 748031 = 1122047) B1122047
theorem B748543 : Blo 746329 748543 := bstep (se 1 (by rfl) ⟨561407, by rfl⟩ : syracuseStep 748543 = 1122815) B1122815
theorem B1895663 : Blo 746329 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B749183 : Blo 746329 749183 := bstep (se 1 (by rfl) ⟨561887, by rfl⟩ : syracuseStep 749183 = 1123775) B1123775
theorem B749415 : Blo 746329 749415 := bstep (se 1 (by rfl) ⟨562061, by rfl⟩ : syracuseStep 749415 = 1124123) B1124123
theorem B749871 : Blo 746329 749871 := bstep (se 1 (by rfl) ⟨562403, by rfl⟩ : syracuseStep 749871 = 1124807) B1124807
theorem B947047 : Blo 746329 947047 := bstep (se 1 (by rfl) ⟨710285, by rfl⟩ : syracuseStep 947047 = 1420571) B1420571
theorem B2523419 : Blo 746329 2523419 := bstep (se 1 (by rfl) ⟨1892564, by rfl⟩ : syracuseStep 2523419 = 3785129) B3785129
theorem B6063443 : Blo 746329 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B4264103 : Blo 746329 4264103 := bstep (se 1 (by rfl) ⟨3198077, by rfl⟩ : syracuseStep 4264103 = 6396155) B6396155
theorem B262083451 : Blo 746329 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B44309501 : Blo 746329 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B1122239 : Blo 746329 1122239 := bstep (se 1 (by rfl) ⟨841679, by rfl⟩ : syracuseStep 1122239 = 1683359) B1683359
theorem B11547269 : Blo 746329 11547269 := bstep (se 4 (by rfl) ⟨1082556, by rfl⟩ : syracuseStep 11547269 = 2165113) B2165113
theorem B69153533 : Blo 746329 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B1686887 : Blo 746329 1686887 := bstep (se 1 (by rfl) ⟨1265165, by rfl⟩ : syracuseStep 1686887 = 2530331) B2530331
theorem B23019167 : Blo 746329 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B1262729 : Blo 746329 1262729 := bstep (se 2 (by rfl) ⟨473523, by rfl⟩ : syracuseStep 1262729 = 947047) B947047
theorem B1263775 : Blo 746329 1263775 := bstep (se 1 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 1263775 = 1895663) B1895663
theorem B2281031 : Blo 746329 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B5461735 : Blo 746329 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B18175907 : Blo 746329 18175907 := bstep (se 1 (by rfl) ⟨13631930, by rfl⟩ : syracuseStep 18175907 = 27263861) B27263861
theorem B843007 : Blo 746329 843007 := bstep (se 1 (by rfl) ⟨632255, by rfl⟩ : syracuseStep 843007 = 1264511) B1264511
theorem B11854907 : Blo 746329 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B2025299 : Blo 746329 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B2519207 : Blo 746329 2519207 := bstep (se 1 (by rfl) ⟨1889405, by rfl⟩ : syracuseStep 2519207 = 3778811) B3778811
theorem B749791 : Blo 746329 749791 := bstep (se 1 (by rfl) ⟨562343, by rfl⟩ : syracuseStep 749791 = 1124687) B1124687
theorem B2520233 : Blo 746329 2520233 := bstep (se 2 (by rfl) ⟨945087, by rfl⟩ : syracuseStep 2520233 = 1890175) B1890175
theorem B7903271 : Blo 746329 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B349444601 : Blo 746329 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B1350199 : Blo 746329 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B7282313 : Blo 746329 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B1679471 : Blo 746329 1679471 := bstep (se 1 (by rfl) ⟨1259603, by rfl⟩ : syracuseStep 1679471 = 2519207) B2519207
theorem B1680155 : Blo 746329 1680155 := bstep (se 1 (by rfl) ⟨1260116, by rfl⟩ : syracuseStep 1680155 = 2520233) B2520233
theorem B1124009 : Blo 746329 1124009 := bstep (se 2 (by rfl) ⟨421503, by rfl⟩ : syracuseStep 1124009 = 843007) B843007
theorem B1124591 : Blo 746329 1124591 := bstep (se 1 (by rfl) ⟨843443, by rfl⟩ : syracuseStep 1124591 = 1686887) B1686887
theorem B15346111 : Blo 746329 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B1682279 : Blo 746329 1682279 := bstep (se 1 (by rfl) ⟨1261709, by rfl⟩ : syracuseStep 1682279 = 2523419) B2523419
theorem B4042295 : Blo 746329 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B1520687 : Blo 746329 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B1685033 : Blo 746329 1685033 := bstep (se 2 (by rfl) ⟨631887, by rfl⟩ : syracuseStep 1685033 = 1263775) B1263775
theorem B29539667 : Blo 746329 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B841819 : Blo 746329 841819 := bstep (se 1 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 841819 = 1262729) B1262729
theorem B2842735 : Blo 746329 2842735 := bstep (se 1 (by rfl) ⟨2132051, by rfl⟩ : syracuseStep 2842735 = 4264103) B4264103
theorem B12117271 : Blo 746329 12117271 := bstep (se 1 (by rfl) ⟨9087953, by rfl⟩ : syracuseStep 12117271 = 18175907) B18175907
theorem B748159 : Blo 746329 748159 := bstep (se 1 (by rfl) ⟨561119, by rfl⟩ : syracuseStep 748159 = 1122239) B1122239
theorem B7698179 : Blo 746329 7698179 := bstep (se 1 (by rfl) ⟨5773634, by rfl⟩ : syracuseStep 7698179 = 11547269) B11547269
theorem B46102355 : Blo 746329 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B16156361 : Blo 746329 16156361 := bstep (se 2 (by rfl) ⟨6058635, by rfl⟩ : syracuseStep 16156361 = 12117271) B12117271
theorem B4854875 : Blo 746329 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B1119647 : Blo 746329 1119647 := bstep (se 1 (by rfl) ⟨839735, by rfl⟩ : syracuseStep 1119647 = 1679471) B1679471
theorem B1120103 : Blo 746329 1120103 := bstep (se 1 (by rfl) ⟨840077, by rfl⟩ : syracuseStep 1120103 = 1680155) B1680155
theorem B1121519 : Blo 746329 1121519 := bstep (se 1 (by rfl) ⟨841139, by rfl⟩ : syracuseStep 1121519 = 1682279) B1682279
theorem B2694863 : Blo 746329 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B1122425 : Blo 746329 1122425 := bstep (se 2 (by rfl) ⟨420909, by rfl⟩ : syracuseStep 1122425 = 841819) B841819
theorem B1123355 : Blo 746329 1123355 := bstep (se 1 (by rfl) ⟨842516, by rfl⟩ : syracuseStep 1123355 = 1685033) B1685033
theorem B20461481 : Blo 746329 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B232963067 : Blo 746329 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B5132119 : Blo 746329 5132119 := bstep (se 1 (by rfl) ⟨3849089, by rfl⟩ : syracuseStep 5132119 = 7698179) B7698179
theorem B3790313 : Blo 746329 3790313 := bstep (se 2 (by rfl) ⟨1421367, by rfl⟩ : syracuseStep 3790313 = 2842735) B2842735
theorem B7201061 : Blo 746329 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B5268847 : Blo 746329 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B749339 : Blo 746329 749339 := bstep (se 1 (by rfl) ⟨562004, by rfl⟩ : syracuseStep 749339 = 1124009) B1124009
theorem B749727 : Blo 746329 749727 := bstep (se 1 (by rfl) ⟨562295, by rfl⟩ : syracuseStep 749727 = 1124591) B1124591
theorem B1013791 : Blo 746329 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B78772445 : Blo 746329 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B30734903 : Blo 746329 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B2526875 : Blo 746329 2526875 := bstep (se 1 (by rfl) ⟨1895156, by rfl⟩ : syracuseStep 2526875 = 3790313) B3790313
theorem B1351721 : Blo 746329 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B13640987 : Blo 746329 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B20489935 : Blo 746329 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B51785333 : Blo 746329 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B7025129 : Blo 746329 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B4800707 : Blo 746329 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B52514963 : Blo 746329 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B155308711 : Blo 746329 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B10770907 : Blo 746329 10770907 := bstep (se 1 (by rfl) ⟨8078180, by rfl⟩ : syracuseStep 10770907 = 16156361) B16156361
theorem B746431 : Blo 746329 746431 := bstep (se 1 (by rfl) ⟨559823, by rfl⟩ : syracuseStep 746431 = 1119647) B1119647
theorem B746735 : Blo 746329 746735 := bstep (se 1 (by rfl) ⟨560051, by rfl⟩ : syracuseStep 746735 = 1120103) B1120103
theorem B747679 : Blo 746329 747679 := bstep (se 1 (by rfl) ⟨560759, by rfl⟩ : syracuseStep 747679 = 1121519) B1121519
theorem B6842825 : Blo 746329 6842825 := bstep (se 2 (by rfl) ⟨2566059, by rfl⟩ : syracuseStep 6842825 = 5132119) B5132119
theorem B1796575 : Blo 746329 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B748283 : Blo 746329 748283 := bstep (se 1 (by rfl) ⟨561212, by rfl⟩ : syracuseStep 748283 = 1122425) B1122425
theorem B748903 : Blo 746329 748903 := bstep (se 1 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 748903 = 1123355) B1123355
theorem B2395433 : Blo 746329 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B4561883 : Blo 746329 4561883 := bstep (se 1 (by rfl) ⟨3421412, by rfl⟩ : syracuseStep 4561883 = 6842825) B6842825
theorem B14361209 : Blo 746329 14361209 := bstep (se 2 (by rfl) ⟨5385453, by rfl⟩ : syracuseStep 14361209 = 10770907) B10770907
theorem B1684583 : Blo 746329 1684583 := bstep (se 1 (by rfl) ⟨1263437, by rfl⟩ : syracuseStep 1684583 = 2526875) B2526875
theorem B35009975 : Blo 746329 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B901147 : Blo 746329 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B9093991 : Blo 746329 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B207078281 : Blo 746329 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B34523555 : Blo 746329 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B3200471 : Blo 746329 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B27319913 : Blo 746329 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B4683419 : Blo 746329 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B138052187 : Blo 746329 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B12125321 : Blo 746329 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B2133647 : Blo 746329 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B9574139 : Blo 746329 9574139 := bstep (se 1 (by rfl) ⟨7180604, by rfl⟩ : syracuseStep 9574139 = 14361209) B14361209
theorem B1123055 : Blo 746329 1123055 := bstep (se 1 (by rfl) ⟨842291, by rfl⟩ : syracuseStep 1123055 = 1684583) B1684583
theorem B23339983 : Blo 746329 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B3122279 : Blo 746329 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B92062813 : Blo 746329 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B1201529 : Blo 746329 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B1596955 : Blo 746329 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B3041255 : Blo 746329 3041255 := bstep (se 1 (by rfl) ⟨2280941, by rfl⟩ : syracuseStep 3041255 = 4561883) B4561883
theorem B18213275 : Blo 746329 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B122750417 : Blo 746329 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B1422431 : Blo 746329 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B801019 : Blo 746329 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B2081519 : Blo 746329 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B12142183 : Blo 746329 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B92034791 : Blo 746329 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B8083547 : Blo 746329 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B31119977 : Blo 746329 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B6382759 : Blo 746329 6382759 := bstep (se 1 (by rfl) ⟨4787069, by rfl⟩ : syracuseStep 6382759 = 9574139) B9574139
theorem B748703 : Blo 746329 748703 := bstep (se 1 (by rfl) ⟨561527, by rfl⟩ : syracuseStep 748703 = 1123055) B1123055
theorem B2027503 : Blo 746329 2027503 := bstep (se 1 (by rfl) ⟨1520627, by rfl⟩ : syracuseStep 2027503 = 3041255) B3041255
theorem B2129273 : Blo 746329 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B16189577 : Blo 746329 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B1419515 : Blo 746329 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B81833611 : Blo 746329 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B4272101 : Blo 746329 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B61356527 : Blo 746329 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B5389031 : Blo 746329 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B2703337 : Blo 746329 2703337 := bstep (se 2 (by rfl) ⟨1013751, by rfl⟩ : syracuseStep 2703337 = 2027503) B2027503
theorem B82986605 : Blo 746329 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B22202869 : Blo 746329 22202869 := bstep (se 5 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 22202869 = 2081519) B2081519
theorem B8510345 : Blo 746329 8510345 := bstep (se 2 (by rfl) ⟨3191379, by rfl⟩ : syracuseStep 8510345 = 6382759) B6382759
theorem B948287 : Blo 746329 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B5673563 : Blo 746329 5673563 := bstep (se 1 (by rfl) ⟨4255172, by rfl⟩ : syracuseStep 5673563 = 8510345) B8510345
theorem B2528765 : Blo 746329 2528765 := bstep (se 3 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 2528765 = 948287) B948287
theorem B40904351 : Blo 746329 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B55324403 : Blo 746329 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B10793051 : Blo 746329 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B29603825 : Blo 746329 29603825 := bstep (se 2 (by rfl) ⟨11101434, by rfl⟩ : syracuseStep 29603825 = 22202869) B22202869
theorem B3592687 : Blo 746329 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B109111481 : Blo 746329 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B946343 : Blo 746329 946343 := bstep (se 1 (by rfl) ⟨709757, by rfl⟩ : syracuseStep 946343 = 1419515) B1419515
theorem B2848067 : Blo 746329 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B14417797 : Blo 746329 14417797 := bstep (se 4 (by rfl) ⟨1351668, by rfl⟩ : syracuseStep 14417797 = 2703337) B2703337
theorem B2523581 : Blo 746329 2523581 := bstep (se 3 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 2523581 = 946343) B946343
theorem B4790249 : Blo 746329 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B27269567 : Blo 746329 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B19735883 : Blo 746329 19735883 := bstep (se 1 (by rfl) ⟨14801912, by rfl⟩ : syracuseStep 19735883 = 29603825) B29603825
theorem B3782375 : Blo 746329 3782375 := bstep (se 1 (by rfl) ⟨2836781, by rfl⟩ : syracuseStep 3782375 = 5673563) B5673563
theorem B1685843 : Blo 746329 1685843 := bstep (se 1 (by rfl) ⟨1264382, by rfl⟩ : syracuseStep 1685843 = 2528765) B2528765
theorem B36882935 : Blo 746329 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B7195367 : Blo 746329 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B19223729 : Blo 746329 19223729 := bstep (se 2 (by rfl) ⟨7208898, by rfl⟩ : syracuseStep 19223729 = 14417797) B14417797
theorem B72740987 : Blo 746329 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B1898711 : Blo 746329 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B12815819 : Blo 746329 12815819 := bstep (se 1 (by rfl) ⟨9611864, by rfl⟩ : syracuseStep 12815819 = 19223729) B19223729
theorem B1123895 : Blo 746329 1123895 := bstep (se 1 (by rfl) ⟨842921, by rfl⟩ : syracuseStep 1123895 = 1685843) B1685843
theorem B1682387 : Blo 746329 1682387 := bstep (se 1 (by rfl) ⟨1261790, by rfl⟩ : syracuseStep 1682387 = 2523581) B2523581
theorem B24588623 : Blo 746329 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B4796911 : Blo 746329 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B3193499 : Blo 746329 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B13157255 : Blo 746329 13157255 := bstep (se 1 (by rfl) ⟨9867941, by rfl⟩ : syracuseStep 13157255 = 19735883) B19735883
theorem B1265807 : Blo 746329 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B18179711 : Blo 746329 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B48493991 : Blo 746329 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B2521583 : Blo 746329 2521583 := bstep (se 1 (by rfl) ⟨1891187, by rfl⟩ : syracuseStep 2521583 = 3782375) B3782375
theorem B6395881 : Blo 746329 6395881 := bstep (se 2 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 6395881 = 4796911) B4796911
theorem B1121591 : Blo 746329 1121591 := bstep (se 1 (by rfl) ⟨841193, by rfl⟩ : syracuseStep 1121591 = 1682387) B1682387
theorem B16392415 : Blo 746329 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B1681055 : Blo 746329 1681055 := bstep (se 1 (by rfl) ⟨1260791, by rfl⟩ : syracuseStep 1681055 = 2521583) B2521583
theorem B32329327 : Blo 746329 32329327 := bstep (se 1 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 32329327 = 48493991) B48493991
theorem B8771503 : Blo 746329 8771503 := bstep (se 1 (by rfl) ⟨6578627, by rfl⟩ : syracuseStep 8771503 = 13157255) B13157255
theorem B8543879 : Blo 746329 8543879 := bstep (se 1 (by rfl) ⟨6407909, by rfl⟩ : syracuseStep 8543879 = 12815819) B12815819
theorem B843871 : Blo 746329 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B749263 : Blo 746329 749263 := bstep (se 1 (by rfl) ⟨561947, by rfl⟩ : syracuseStep 749263 = 1123895) B1123895
theorem B12119807 : Blo 746329 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B2128999 : Blo 746329 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B21856553 : Blo 746329 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B1120703 : Blo 746329 1120703 := bstep (se 1 (by rfl) ⟨840527, by rfl⟩ : syracuseStep 1120703 = 1681055) B1681055
theorem B8527841 : Blo 746329 8527841 := bstep (se 2 (by rfl) ⟨3197940, by rfl⟩ : syracuseStep 8527841 = 6395881) B6395881
theorem B32319485 : Blo 746329 32319485 := bstep (se 3 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 32319485 = 12119807) B12119807
theorem B1125161 : Blo 746329 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B43105769 : Blo 746329 43105769 := bstep (se 2 (by rfl) ⟨16164663, by rfl⟩ : syracuseStep 43105769 = 32329327) B32329327
theorem B2838665 : Blo 746329 2838665 := bstep (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) B2128999
theorem B747727 : Blo 746329 747727 := bstep (se 1 (by rfl) ⟨560795, by rfl⟩ : syracuseStep 747727 = 1121591) B1121591
theorem B5695919 : Blo 746329 5695919 := bstep (se 1 (by rfl) ⟨4271939, by rfl⟩ : syracuseStep 5695919 = 8543879) B8543879
theorem B11695337 : Blo 746329 11695337 := bstep (se 2 (by rfl) ⟨4385751, by rfl⟩ : syracuseStep 11695337 = 8771503) B8771503
theorem B5685227 : Blo 746329 5685227 := bstep (se 1 (by rfl) ⟨4263920, by rfl⟩ : syracuseStep 5685227 = 8527841) B8527841
theorem B21546323 : Blo 746329 21546323 := bstep (se 1 (by rfl) ⟨16159742, by rfl⟩ : syracuseStep 21546323 = 32319485) B32319485
theorem B14571035 : Blo 746329 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B1892443 : Blo 746329 1892443 := bstep (se 1 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 1892443 = 2838665) B2838665
theorem B747135 : Blo 746329 747135 := bstep (se 1 (by rfl) ⟨560351, by rfl⟩ : syracuseStep 747135 = 1120703) B1120703
theorem B3797279 : Blo 746329 3797279 := bstep (se 1 (by rfl) ⟨2847959, by rfl⟩ : syracuseStep 3797279 = 5695919) B5695919
theorem B750107 : Blo 746329 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B7796891 : Blo 746329 7796891 := bstep (se 1 (by rfl) ⟨5847668, by rfl⟩ : syracuseStep 7796891 = 11695337) B11695337
theorem B28737179 : Blo 746329 28737179 := bstep (se 1 (by rfl) ⟨21552884, by rfl⟩ : syracuseStep 28737179 = 43105769) B43105769
theorem B2523257 : Blo 746329 2523257 := bstep (se 2 (by rfl) ⟨946221, by rfl⟩ : syracuseStep 2523257 = 1892443) B1892443
theorem B2531519 : Blo 746329 2531519 := bstep (se 1 (by rfl) ⟨1898639, by rfl⟩ : syracuseStep 2531519 = 3797279) B3797279
theorem B14364215 : Blo 746329 14364215 := bstep (se 1 (by rfl) ⟨10773161, by rfl⟩ : syracuseStep 14364215 = 21546323) B21546323
theorem B9714023 : Blo 746329 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B5197927 : Blo 746329 5197927 := bstep (se 1 (by rfl) ⟨3898445, by rfl⟩ : syracuseStep 5197927 = 7796891) B7796891
theorem B19158119 : Blo 746329 19158119 := bstep (se 1 (by rfl) ⟨14368589, by rfl⟩ : syracuseStep 19158119 = 28737179) B28737179
theorem B3790151 : Blo 746329 3790151 := bstep (se 1 (by rfl) ⟨2842613, by rfl⟩ : syracuseStep 3790151 = 5685227) B5685227
theorem B2526767 : Blo 746329 2526767 := bstep (se 1 (by rfl) ⟨1895075, by rfl⟩ : syracuseStep 2526767 = 3790151) B3790151
theorem B9576143 : Blo 746329 9576143 := bstep (se 1 (by rfl) ⟨7182107, by rfl⟩ : syracuseStep 9576143 = 14364215) B14364215
theorem B1682171 : Blo 746329 1682171 := bstep (se 1 (by rfl) ⟨1261628, by rfl⟩ : syracuseStep 1682171 = 2523257) B2523257
theorem B1687679 : Blo 746329 1687679 := bstep (se 1 (by rfl) ⟨1265759, by rfl⟩ : syracuseStep 1687679 = 2531519) B2531519
theorem B6930569 : Blo 746329 6930569 := bstep (se 2 (by rfl) ⟨2598963, by rfl⟩ : syracuseStep 6930569 = 5197927) B5197927
theorem B6476015 : Blo 746329 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B12772079 : Blo 746329 12772079 := bstep (se 1 (by rfl) ⟨9579059, by rfl⟩ : syracuseStep 12772079 = 19158119) B19158119
theorem B18481517 : Blo 746329 18481517 := bstep (se 3 (by rfl) ⟨3465284, by rfl⟩ : syracuseStep 18481517 = 6930569) B6930569
theorem B1121447 : Blo 746329 1121447 := bstep (se 1 (by rfl) ⟨841085, by rfl⟩ : syracuseStep 1121447 = 1682171) B1682171
theorem B1125119 : Blo 746329 1125119 := bstep (se 1 (by rfl) ⟨843839, by rfl⟩ : syracuseStep 1125119 = 1687679) B1687679
theorem B1684511 : Blo 746329 1684511 := bstep (se 1 (by rfl) ⟨1263383, by rfl⟩ : syracuseStep 1684511 = 2526767) B2526767
theorem B4317343 : Blo 746329 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B6384095 : Blo 746329 6384095 := bstep (se 1 (by rfl) ⟨4788071, by rfl⟩ : syracuseStep 6384095 = 9576143) B9576143
theorem B8514719 : Blo 746329 8514719 := bstep (se 1 (by rfl) ⟨6386039, by rfl⟩ : syracuseStep 8514719 = 12772079) B12772079
theorem B12321011 : Blo 746329 12321011 := bstep (se 1 (by rfl) ⟨9240758, by rfl⟩ : syracuseStep 12321011 = 18481517) B18481517
theorem B5676479 : Blo 746329 5676479 := bstep (se 1 (by rfl) ⟨4257359, by rfl⟩ : syracuseStep 5676479 = 8514719) B8514719
theorem B1123007 : Blo 746329 1123007 := bstep (se 1 (by rfl) ⟨842255, by rfl⟩ : syracuseStep 1123007 = 1684511) B1684511
theorem B23025829 : Blo 746329 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B747631 : Blo 746329 747631 := bstep (se 1 (by rfl) ⟨560723, by rfl⟩ : syracuseStep 747631 = 1121447) B1121447
theorem B4256063 : Blo 746329 4256063 := bstep (se 1 (by rfl) ⟨3192047, by rfl⟩ : syracuseStep 4256063 = 6384095) B6384095
theorem B750079 : Blo 746329 750079 := bstep (se 1 (by rfl) ⟨562559, by rfl⟩ : syracuseStep 750079 = 1125119) B1125119
theorem B3784319 : Blo 746329 3784319 := bstep (se 1 (by rfl) ⟨2838239, by rfl⟩ : syracuseStep 3784319 = 5676479) B5676479
theorem B2837375 : Blo 746329 2837375 := bstep (se 1 (by rfl) ⟨2128031, by rfl⟩ : syracuseStep 2837375 = 4256063) B4256063
theorem B8214007 : Blo 746329 8214007 := bstep (se 1 (by rfl) ⟨6160505, by rfl⟩ : syracuseStep 8214007 = 12321011) B12321011
theorem B748671 : Blo 746329 748671 := bstep (se 1 (by rfl) ⟨561503, by rfl⟩ : syracuseStep 748671 = 1123007) B1123007
theorem B30701105 : Blo 746329 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B10952009 : Blo 746329 10952009 := bstep (se 2 (by rfl) ⟨4107003, by rfl⟩ : syracuseStep 10952009 = 8214007) B8214007
theorem B20467403 : Blo 746329 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B1891583 : Blo 746329 1891583 := bstep (se 1 (by rfl) ⟨1418687, by rfl⟩ : syracuseStep 1891583 = 2837375) B2837375
theorem B2522879 : Blo 746329 2522879 := bstep (se 1 (by rfl) ⟨1892159, by rfl⟩ : syracuseStep 2522879 = 3784319) B3784319
theorem B1681919 : Blo 746329 1681919 := bstep (se 1 (by rfl) ⟨1261439, by rfl⟩ : syracuseStep 1681919 = 2522879) B2522879
theorem B13644935 : Blo 746329 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B1261055 : Blo 746329 1261055 := bstep (se 1 (by rfl) ⟨945791, by rfl⟩ : syracuseStep 1261055 = 1891583) B1891583
theorem B7301339 : Blo 746329 7301339 := bstep (se 1 (by rfl) ⟨5476004, by rfl⟩ : syracuseStep 7301339 = 10952009) B10952009
theorem B1121279 : Blo 746329 1121279 := bstep (se 1 (by rfl) ⟨840959, by rfl⟩ : syracuseStep 1121279 = 1681919) B1681919
theorem B4867559 : Blo 746329 4867559 := bstep (se 1 (by rfl) ⟨3650669, by rfl⟩ : syracuseStep 4867559 = 7301339) B7301339
theorem B9096623 : Blo 746329 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B840703 : Blo 746329 840703 := bstep (se 1 (by rfl) ⟨630527, by rfl⟩ : syracuseStep 840703 = 1261055) B1261055
theorem B3245039 : Blo 746329 3245039 := bstep (se 1 (by rfl) ⟨2433779, by rfl⟩ : syracuseStep 3245039 = 4867559) B4867559
theorem B6064415 : Blo 746329 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B1120937 : Blo 746329 1120937 := bstep (se 2 (by rfl) ⟨420351, by rfl⟩ : syracuseStep 1120937 = 840703) B840703
theorem B747519 : Blo 746329 747519 := bstep (se 1 (by rfl) ⟨560639, by rfl⟩ : syracuseStep 747519 = 1121279) B1121279
theorem B2163359 : Blo 746329 2163359 := bstep (se 1 (by rfl) ⟨1622519, by rfl⟩ : syracuseStep 2163359 = 3245039) B3245039
theorem B4042943 : Blo 746329 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B747291 : Blo 746329 747291 := bstep (se 1 (by rfl) ⟨560468, by rfl⟩ : syracuseStep 747291 = 1120937) B1120937
theorem B5768957 : Blo 746329 5768957 := bstep (se 3 (by rfl) ⟨1081679, by rfl⟩ : syracuseStep 5768957 = 2163359) B2163359
theorem B2695295 : Blo 746329 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B7187453 : Blo 746329 7187453 := bstep (se 3 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 7187453 = 2695295) B2695295
theorem B3845971 : Blo 746329 3845971 := bstep (se 1 (by rfl) ⟨2884478, by rfl⟩ : syracuseStep 3845971 = 5768957) B5768957
theorem B4791635 : Blo 746329 4791635 := bstep (se 1 (by rfl) ⟨3593726, by rfl⟩ : syracuseStep 4791635 = 7187453) B7187453
theorem B5127961 : Blo 746329 5127961 := bstep (se 2 (by rfl) ⟨1922985, by rfl⟩ : syracuseStep 5127961 = 3845971) B3845971
theorem B3194423 : Blo 746329 3194423 := bstep (se 1 (by rfl) ⟨2395817, by rfl⟩ : syracuseStep 3194423 = 4791635) B4791635
theorem B6837281 : Blo 746329 6837281 := bstep (se 2 (by rfl) ⟨2563980, by rfl⟩ : syracuseStep 6837281 = 5127961) B5127961
theorem B4558187 : Blo 746329 4558187 := bstep (se 1 (by rfl) ⟨3418640, by rfl⟩ : syracuseStep 4558187 = 6837281) B6837281
theorem B2129615 : Blo 746329 2129615 := bstep (se 1 (by rfl) ⟨1597211, by rfl⟩ : syracuseStep 2129615 = 3194423) B3194423
theorem B1419743 : Blo 746329 1419743 := bstep (se 1 (by rfl) ⟨1064807, by rfl⟩ : syracuseStep 1419743 = 2129615) B2129615
theorem B3038791 : Blo 746329 3038791 := bstep (se 1 (by rfl) ⟨2279093, by rfl⟩ : syracuseStep 3038791 = 4558187) B4558187
theorem B4051721 : Blo 746329 4051721 := bstep (se 2 (by rfl) ⟨1519395, by rfl⟩ : syracuseStep 4051721 = 3038791) B3038791
theorem B946495 : Blo 746329 946495 := bstep (se 1 (by rfl) ⟨709871, by rfl⟩ : syracuseStep 946495 = 1419743) B1419743
theorem B2701147 : Blo 746329 2701147 := bstep (se 1 (by rfl) ⟨2025860, by rfl⟩ : syracuseStep 2701147 = 4051721) B4051721
theorem B1261993 : Blo 746329 1261993 := bstep (se 2 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 1261993 = 946495) B946495
theorem B1682657 : Blo 746329 1682657 := bstep (se 2 (by rfl) ⟨630996, by rfl⟩ : syracuseStep 1682657 = 1261993) B1261993
theorem B3601529 : Blo 746329 3601529 := bstep (se 2 (by rfl) ⟨1350573, by rfl⟩ : syracuseStep 3601529 = 2701147) B2701147
theorem B1121771 : Blo 746329 1121771 := bstep (se 1 (by rfl) ⟨841328, by rfl⟩ : syracuseStep 1121771 = 1682657) B1682657
theorem B2401019 : Blo 746329 2401019 := bstep (se 1 (by rfl) ⟨1800764, by rfl⟩ : syracuseStep 2401019 = 3601529) B3601529
theorem B747847 : Blo 746329 747847 := bstep (se 1 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 747847 = 1121771) B1121771
theorem B1600679 : Blo 746329 1600679 := bstep (se 1 (by rfl) ⟨1200509, by rfl⟩ : syracuseStep 1600679 = 2401019) B2401019
theorem B4268477 : Blo 746329 4268477 := bstep (se 3 (by rfl) ⟨800339, by rfl⟩ : syracuseStep 4268477 = 1600679) B1600679
theorem B2845651 : Blo 746329 2845651 := bstep (se 1 (by rfl) ⟨2134238, by rfl⟩ : syracuseStep 2845651 = 4268477) B4268477
theorem B3794201 : Blo 746329 3794201 := bstep (se 2 (by rfl) ⟨1422825, by rfl⟩ : syracuseStep 3794201 = 2845651) B2845651
theorem B2529467 : Blo 746329 2529467 := bstep (se 1 (by rfl) ⟨1897100, by rfl⟩ : syracuseStep 2529467 = 3794201) B3794201
theorem B1686311 : Blo 746329 1686311 := bstep (se 1 (by rfl) ⟨1264733, by rfl⟩ : syracuseStep 1686311 = 2529467) B2529467
theorem B1124207 : Blo 746329 1124207 := bstep (se 1 (by rfl) ⟨843155, by rfl⟩ : syracuseStep 1124207 = 1686311) B1686311
theorem B749471 : Blo 746329 749471 := bstep (se 1 (by rfl) ⟨562103, by rfl⟩ : syracuseStep 749471 = 1124207) B1124207

theorem C0 (j : ℕ) (h1 : 186582 ≤ j) (h2 : j ≤ 187281) : Blo 746329 (4 * j + 3) := by
  interval_cases j
  · exact B746331
  · exact B746335
  · exact B746339
  · exact B746343
  · exact B746347
  · exact B746351
  · exact B746355
  · exact B746359
  · exact B746363
  · exact B746367
  · exact B746371
  · exact B746375
  · exact B746379
  · exact B746383
  · exact B746387
  · exact B746391
  · exact B746395
  · exact B746399
  · exact B746403
  · exact B746407
  · exact B746411
  · exact B746415
  · exact B746419
  · exact B746423
  · exact B746427
  · exact B746431
  · exact B746435
  · exact B746439
  · exact B746443
  · exact B746447
  · exact B746451
  · exact B746455
  · exact B746459
  · exact B746463
  · exact B746467
  · exact B746471
  · exact B746475
  · exact B746479
  · exact B746483
  · exact B746487
  · exact B746491
  · exact B746495
  · exact B746499
  · exact B746503
  · exact B746507
  · exact B746511
  · exact B746515
  · exact B746519
  · exact B746523
  · exact B746527
  · exact B746531
  · exact B746535
  · exact B746539
  · exact B746543
  · exact B746547
  · exact B746551
  · exact B746555
  · exact B746559
  · exact B746563
  · exact B746567
  · exact B746571
  · exact B746575
  · exact B746579
  · exact B746583
  · exact B746587
  · exact B746591
  · exact B746595
  · exact B746599
  · exact B746603
  · exact B746607
  · exact B746611
  · exact B746615
  · exact B746619
  · exact B746623
  · exact B746627
  · exact B746631
  · exact B746635
  · exact B746639
  · exact B746643
  · exact B746647
  · exact B746651
  · exact B746655
  · exact B746659
  · exact B746663
  · exact B746667
  · exact B746671
  · exact B746675
  · exact B746679
  · exact B746683
  · exact B746687
  · exact B746691
  · exact B746695
  · exact B746699
  · exact B746703
  · exact B746707
  · exact B746711
  · exact B746715
  · exact B746719
  · exact B746723
  · exact B746727
  · exact B746731
  · exact B746735
  · exact B746739
  · exact B746743
  · exact B746747
  · exact B746751
  · exact B746755
  · exact B746759
  · exact B746763
  · exact B746767
  · exact B746771
  · exact B746775
  · exact B746779
  · exact B746783
  · exact B746787
  · exact B746791
  · exact B746795
  · exact B746799
  · exact B746803
  · exact B746807
  · exact B746811
  · exact B746815
  · exact B746819
  · exact B746823
  · exact B746827
  · exact B746831
  · exact B746835
  · exact B746839
  · exact B746843
  · exact B746847
  · exact B746851
  · exact B746855
  · exact B746859
  · exact B746863
  · exact B746867
  · exact B746871
  · exact B746875
  · exact B746879
  · exact B746883
  · exact B746887
  · exact B746891
  · exact B746895
  · exact B746899
  · exact B746903
  · exact B746907
  · exact B746911
  · exact B746915
  · exact B746919
  · exact B746923
  · exact B746927
  · exact B746931
  · exact B746935
  · exact B746939
  · exact B746943
  · exact B746947
  · exact B746951
  · exact B746955
  · exact B746959
  · exact B746963
  · exact B746967
  · exact B746971
  · exact B746975
  · exact B746979
  · exact B746983
  · exact B746987
  · exact B746991
  · exact B746995
  · exact B746999
  · exact B747003
  · exact B747007
  · exact B747011
  · exact B747015
  · exact B747019
  · exact B747023
  · exact B747027
  · exact B747031
  · exact B747035
  · exact B747039
  · exact B747043
  · exact B747047
  · exact B747051
  · exact B747055
  · exact B747059
  · exact B747063
  · exact B747067
  · exact B747071
  · exact B747075
  · exact B747079
  · exact B747083
  · exact B747087
  · exact B747091
  · exact B747095
  · exact B747099
  · exact B747103
  · exact B747107
  · exact B747111
  · exact B747115
  · exact B747119
  · exact B747123
  · exact B747127
  · exact B747131
  · exact B747135
  · exact B747139
  · exact B747143
  · exact B747147
  · exact B747151
  · exact B747155
  · exact B747159
  · exact B747163
  · exact B747167
  · exact B747171
  · exact B747175
  · exact B747179
  · exact B747183
  · exact B747187
  · exact B747191
  · exact B747195
  · exact B747199
  · exact B747203
  · exact B747207
  · exact B747211
  · exact B747215
  · exact B747219
  · exact B747223
  · exact B747227
  · exact B747231
  · exact B747235
  · exact B747239
  · exact B747243
  · exact B747247
  · exact B747251
  · exact B747255
  · exact B747259
  · exact B747263
  · exact B747267
  · exact B747271
  · exact B747275
  · exact B747279
  · exact B747283
  · exact B747287
  · exact B747291
  · exact B747295
  · exact B747299
  · exact B747303
  · exact B747307
  · exact B747311
  · exact B747315
  · exact B747319
  · exact B747323
  · exact B747327
  · exact B747331
  · exact B747335
  · exact B747339
  · exact B747343
  · exact B747347
  · exact B747351
  · exact B747355
  · exact B747359
  · exact B747363
  · exact B747367
  · exact B747371
  · exact B747375
  · exact B747379
  · exact B747383
  · exact B747387
  · exact B747391
  · exact B747395
  · exact B747399
  · exact B747403
  · exact B747407
  · exact B747411
  · exact B747415
  · exact B747419
  · exact B747423
  · exact B747427
  · exact B747431
  · exact B747435
  · exact B747439
  · exact B747443
  · exact B747447
  · exact B747451
  · exact B747455
  · exact B747459
  · exact B747463
  · exact B747467
  · exact B747471
  · exact B747475
  · exact B747479
  · exact B747483
  · exact B747487
  · exact B747491
  · exact B747495
  · exact B747499
  · exact B747503
  · exact B747507
  · exact B747511
  · exact B747515
  · exact B747519
  · exact B747523
  · exact B747527
  · exact B747531
  · exact B747535
  · exact B747539
  · exact B747543
  · exact B747547
  · exact B747551
  · exact B747555
  · exact B747559
  · exact B747563
  · exact B747567
  · exact B747571
  · exact B747575
  · exact B747579
  · exact B747583
  · exact B747587
  · exact B747591
  · exact B747595
  · exact B747599
  · exact B747603
  · exact B747607
  · exact B747611
  · exact B747615
  · exact B747619
  · exact B747623
  · exact B747627
  · exact B747631
  · exact B747635
  · exact B747639
  · exact B747643
  · exact B747647
  · exact B747651
  · exact B747655
  · exact B747659
  · exact B747663
  · exact B747667
  · exact B747671
  · exact B747675
  · exact B747679
  · exact B747683
  · exact B747687
  · exact B747691
  · exact B747695
  · exact B747699
  · exact B747703
  · exact B747707
  · exact B747711
  · exact B747715
  · exact B747719
  · exact B747723
  · exact B747727
  · exact B747731
  · exact B747735
  · exact B747739
  · exact B747743
  · exact B747747
  · exact B747751
  · exact B747755
  · exact B747759
  · exact B747763
  · exact B747767
  · exact B747771
  · exact B747775
  · exact B747779
  · exact B747783
  · exact B747787
  · exact B747791
  · exact B747795
  · exact B747799
  · exact B747803
  · exact B747807
  · exact B747811
  · exact B747815
  · exact B747819
  · exact B747823
  · exact B747827
  · exact B747831
  · exact B747835
  · exact B747839
  · exact B747843
  · exact B747847
  · exact B747851
  · exact B747855
  · exact B747859
  · exact B747863
  · exact B747867
  · exact B747871
  · exact B747875
  · exact B747879
  · exact B747883
  · exact B747887
  · exact B747891
  · exact B747895
  · exact B747899
  · exact B747903
  · exact B747907
  · exact B747911
  · exact B747915
  · exact B747919
  · exact B747923
  · exact B747927
  · exact B747931
  · exact B747935
  · exact B747939
  · exact B747943
  · exact B747947
  · exact B747951
  · exact B747955
  · exact B747959
  · exact B747963
  · exact B747967
  · exact B747971
  · exact B747975
  · exact B747979
  · exact B747983
  · exact B747987
  · exact B747991
  · exact B747995
  · exact B747999
  · exact B748003
  · exact B748007
  · exact B748011
  · exact B748015
  · exact B748019
  · exact B748023
  · exact B748027
  · exact B748031
  · exact B748035
  · exact B748039
  · exact B748043
  · exact B748047
  · exact B748051
  · exact B748055
  · exact B748059
  · exact B748063
  · exact B748067
  · exact B748071
  · exact B748075
  · exact B748079
  · exact B748083
  · exact B748087
  · exact B748091
  · exact B748095
  · exact B748099
  · exact B748103
  · exact B748107
  · exact B748111
  · exact B748115
  · exact B748119
  · exact B748123
  · exact B748127
  · exact B748131
  · exact B748135
  · exact B748139
  · exact B748143
  · exact B748147
  · exact B748151
  · exact B748155
  · exact B748159
  · exact B748163
  · exact B748167
  · exact B748171
  · exact B748175
  · exact B748179
  · exact B748183
  · exact B748187
  · exact B748191
  · exact B748195
  · exact B748199
  · exact B748203
  · exact B748207
  · exact B748211
  · exact B748215
  · exact B748219
  · exact B748223
  · exact B748227
  · exact B748231
  · exact B748235
  · exact B748239
  · exact B748243
  · exact B748247
  · exact B748251
  · exact B748255
  · exact B748259
  · exact B748263
  · exact B748267
  · exact B748271
  · exact B748275
  · exact B748279
  · exact B748283
  · exact B748287
  · exact B748291
  · exact B748295
  · exact B748299
  · exact B748303
  · exact B748307
  · exact B748311
  · exact B748315
  · exact B748319
  · exact B748323
  · exact B748327
  · exact B748331
  · exact B748335
  · exact B748339
  · exact B748343
  · exact B748347
  · exact B748351
  · exact B748355
  · exact B748359
  · exact B748363
  · exact B748367
  · exact B748371
  · exact B748375
  · exact B748379
  · exact B748383
  · exact B748387
  · exact B748391
  · exact B748395
  · exact B748399
  · exact B748403
  · exact B748407
  · exact B748411
  · exact B748415
  · exact B748419
  · exact B748423
  · exact B748427
  · exact B748431
  · exact B748435
  · exact B748439
  · exact B748443
  · exact B748447
  · exact B748451
  · exact B748455
  · exact B748459
  · exact B748463
  · exact B748467
  · exact B748471
  · exact B748475
  · exact B748479
  · exact B748483
  · exact B748487
  · exact B748491
  · exact B748495
  · exact B748499
  · exact B748503
  · exact B748507
  · exact B748511
  · exact B748515
  · exact B748519
  · exact B748523
  · exact B748527
  · exact B748531
  · exact B748535
  · exact B748539
  · exact B748543
  · exact B748547
  · exact B748551
  · exact B748555
  · exact B748559
  · exact B748563
  · exact B748567
  · exact B748571
  · exact B748575
  · exact B748579
  · exact B748583
  · exact B748587
  · exact B748591
  · exact B748595
  · exact B748599
  · exact B748603
  · exact B748607
  · exact B748611
  · exact B748615
  · exact B748619
  · exact B748623
  · exact B748627
  · exact B748631
  · exact B748635
  · exact B748639
  · exact B748643
  · exact B748647
  · exact B748651
  · exact B748655
  · exact B748659
  · exact B748663
  · exact B748667
  · exact B748671
  · exact B748675
  · exact B748679
  · exact B748683
  · exact B748687
  · exact B748691
  · exact B748695
  · exact B748699
  · exact B748703
  · exact B748707
  · exact B748711
  · exact B748715
  · exact B748719
  · exact B748723
  · exact B748727
  · exact B748731
  · exact B748735
  · exact B748739
  · exact B748743
  · exact B748747
  · exact B748751
  · exact B748755
  · exact B748759
  · exact B748763
  · exact B748767
  · exact B748771
  · exact B748775
  · exact B748779
  · exact B748783
  · exact B748787
  · exact B748791
  · exact B748795
  · exact B748799
  · exact B748803
  · exact B748807
  · exact B748811
  · exact B748815
  · exact B748819
  · exact B748823
  · exact B748827
  · exact B748831
  · exact B748835
  · exact B748839
  · exact B748843
  · exact B748847
  · exact B748851
  · exact B748855
  · exact B748859
  · exact B748863
  · exact B748867
  · exact B748871
  · exact B748875
  · exact B748879
  · exact B748883
  · exact B748887
  · exact B748891
  · exact B748895
  · exact B748899
  · exact B748903
  · exact B748907
  · exact B748911
  · exact B748915
  · exact B748919
  · exact B748923
  · exact B748927
  · exact B748931
  · exact B748935
  · exact B748939
  · exact B748943
  · exact B748947
  · exact B748951
  · exact B748955
  · exact B748959
  · exact B748963
  · exact B748967
  · exact B748971
  · exact B748975
  · exact B748979
  · exact B748983
  · exact B748987
  · exact B748991
  · exact B748995
  · exact B748999
  · exact B749003
  · exact B749007
  · exact B749011
  · exact B749015
  · exact B749019
  · exact B749023
  · exact B749027
  · exact B749031
  · exact B749035
  · exact B749039
  · exact B749043
  · exact B749047
  · exact B749051
  · exact B749055
  · exact B749059
  · exact B749063
  · exact B749067
  · exact B749071
  · exact B749075
  · exact B749079
  · exact B749083
  · exact B749087
  · exact B749091
  · exact B749095
  · exact B749099
  · exact B749103
  · exact B749107
  · exact B749111
  · exact B749115
  · exact B749119
  · exact B749123
  · exact B749127

theorem C1 (j : ℕ) (h1 : 187282 ≤ j) (h2 : j ≤ 187581) : Blo 746329 (4 * j + 3) := by
  interval_cases j
  · exact B749131
  · exact B749135
  · exact B749139
  · exact B749143
  · exact B749147
  · exact B749151
  · exact B749155
  · exact B749159
  · exact B749163
  · exact B749167
  · exact B749171
  · exact B749175
  · exact B749179
  · exact B749183
  · exact B749187
  · exact B749191
  · exact B749195
  · exact B749199
  · exact B749203
  · exact B749207
  · exact B749211
  · exact B749215
  · exact B749219
  · exact B749223
  · exact B749227
  · exact B749231
  · exact B749235
  · exact B749239
  · exact B749243
  · exact B749247
  · exact B749251
  · exact B749255
  · exact B749259
  · exact B749263
  · exact B749267
  · exact B749271
  · exact B749275
  · exact B749279
  · exact B749283
  · exact B749287
  · exact B749291
  · exact B749295
  · exact B749299
  · exact B749303
  · exact B749307
  · exact B749311
  · exact B749315
  · exact B749319
  · exact B749323
  · exact B749327
  · exact B749331
  · exact B749335
  · exact B749339
  · exact B749343
  · exact B749347
  · exact B749351
  · exact B749355
  · exact B749359
  · exact B749363
  · exact B749367
  · exact B749371
  · exact B749375
  · exact B749379
  · exact B749383
  · exact B749387
  · exact B749391
  · exact B749395
  · exact B749399
  · exact B749403
  · exact B749407
  · exact B749411
  · exact B749415
  · exact B749419
  · exact B749423
  · exact B749427
  · exact B749431
  · exact B749435
  · exact B749439
  · exact B749443
  · exact B749447
  · exact B749451
  · exact B749455
  · exact B749459
  · exact B749463
  · exact B749467
  · exact B749471
  · exact B749475
  · exact B749479
  · exact B749483
  · exact B749487
  · exact B749491
  · exact B749495
  · exact B749499
  · exact B749503
  · exact B749507
  · exact B749511
  · exact B749515
  · exact B749519
  · exact B749523
  · exact B749527
  · exact B749531
  · exact B749535
  · exact B749539
  · exact B749543
  · exact B749547
  · exact B749551
  · exact B749555
  · exact B749559
  · exact B749563
  · exact B749567
  · exact B749571
  · exact B749575
  · exact B749579
  · exact B749583
  · exact B749587
  · exact B749591
  · exact B749595
  · exact B749599
  · exact B749603
  · exact B749607
  · exact B749611
  · exact B749615
  · exact B749619
  · exact B749623
  · exact B749627
  · exact B749631
  · exact B749635
  · exact B749639
  · exact B749643
  · exact B749647
  · exact B749651
  · exact B749655
  · exact B749659
  · exact B749663
  · exact B749667
  · exact B749671
  · exact B749675
  · exact B749679
  · exact B749683
  · exact B749687
  · exact B749691
  · exact B749695
  · exact B749699
  · exact B749703
  · exact B749707
  · exact B749711
  · exact B749715
  · exact B749719
  · exact B749723
  · exact B749727
  · exact B749731
  · exact B749735
  · exact B749739
  · exact B749743
  · exact B749747
  · exact B749751
  · exact B749755
  · exact B749759
  · exact B749763
  · exact B749767
  · exact B749771
  · exact B749775
  · exact B749779
  · exact B749783
  · exact B749787
  · exact B749791
  · exact B749795
  · exact B749799
  · exact B749803
  · exact B749807
  · exact B749811
  · exact B749815
  · exact B749819
  · exact B749823
  · exact B749827
  · exact B749831
  · exact B749835
  · exact B749839
  · exact B749843
  · exact B749847
  · exact B749851
  · exact B749855
  · exact B749859
  · exact B749863
  · exact B749867
  · exact B749871
  · exact B749875
  · exact B749879
  · exact B749883
  · exact B749887
  · exact B749891
  · exact B749895
  · exact B749899
  · exact B749903
  · exact B749907
  · exact B749911
  · exact B749915
  · exact B749919
  · exact B749923
  · exact B749927
  · exact B749931
  · exact B749935
  · exact B749939
  · exact B749943
  · exact B749947
  · exact B749951
  · exact B749955
  · exact B749959
  · exact B749963
  · exact B749967
  · exact B749971
  · exact B749975
  · exact B749979
  · exact B749983
  · exact B749987
  · exact B749991
  · exact B749995
  · exact B749999
  · exact B750003
  · exact B750007
  · exact B750011
  · exact B750015
  · exact B750019
  · exact B750023
  · exact B750027
  · exact B750031
  · exact B750035
  · exact B750039
  · exact B750043
  · exact B750047
  · exact B750051
  · exact B750055
  · exact B750059
  · exact B750063
  · exact B750067
  · exact B750071
  · exact B750075
  · exact B750079
  · exact B750083
  · exact B750087
  · exact B750091
  · exact B750095
  · exact B750099
  · exact B750103
  · exact B750107
  · exact B750111
  · exact B750115
  · exact B750119
  · exact B750123
  · exact B750127
  · exact B750131
  · exact B750135
  · exact B750139
  · exact B750143
  · exact B750147
  · exact B750151
  · exact B750155
  · exact B750159
  · exact B750163
  · exact B750167
  · exact B750171
  · exact B750175
  · exact B750179
  · exact B750183
  · exact B750187
  · exact B750191
  · exact B750195
  · exact B750199
  · exact B750203
  · exact B750207
  · exact B750211
  · exact B750215
  · exact B750219
  · exact B750223
  · exact B750227
  · exact B750231
  · exact B750235
  · exact B750239
  · exact B750243
  · exact B750247
  · exact B750251
  · exact B750255
  · exact B750259
  · exact B750263
  · exact B750267
  · exact B750271
  · exact B750275
  · exact B750279
  · exact B750283
  · exact B750287
  · exact B750291
  · exact B750295
  · exact B750299
  · exact B750303
  · exact B750307
  · exact B750311
  · exact B750315
  · exact B750319
  · exact B750323
  · exact B750327

theorem solution (m : ℕ) (hlo : 746329 ≤ m) (hhi : m ≤ 750329) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 186582 ≤ j := by omega
    have hj2 : j ≤ 187581 := by omega
    have hb : Blo 746329 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 187282 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
