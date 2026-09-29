-- Prove2me | solution 1 for syracuse_descends_range_630300_634300
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:37.730126+00:00
-- url     : https://prove2.me/submissions/0c0d96aa-3471-4fed-823e-7ec9243c1541

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


theorem B950285 : Blo 630300 950285 := bbase (se 3 (by rfl) ⟨178178, by rfl⟩ : syracuseStep 950285 = 356357) (by norm_num)
theorem B950309 : Blo 630300 950309 := bbase (se 4 (by rfl) ⟨89091, by rfl⟩ : syracuseStep 950309 = 178183) (by norm_num)
theorem B950333 : Blo 630300 950333 := bbase (se 3 (by rfl) ⟨178187, by rfl⟩ : syracuseStep 950333 = 356375) (by norm_num)
theorem B950357 : Blo 630300 950357 := bbase (se 8 (by rfl) ⟨5568, by rfl⟩ : syracuseStep 950357 = 11137) (by norm_num)
theorem B950381 : Blo 630300 950381 := bbase (se 3 (by rfl) ⟨178196, by rfl⟩ : syracuseStep 950381 = 356393) (by norm_num)
theorem B950405 : Blo 630300 950405 := bbase (se 4 (by rfl) ⟨89100, by rfl⟩ : syracuseStep 950405 = 178201) (by norm_num)
theorem B950429 : Blo 630300 950429 := bbase (se 3 (by rfl) ⟨178205, by rfl⟩ : syracuseStep 950429 = 356411) (by norm_num)
theorem B950453 : Blo 630300 950453 := bbase (se 5 (by rfl) ⟨44552, by rfl⟩ : syracuseStep 950453 = 89105) (by norm_num)
theorem B950477 : Blo 630300 950477 := bbase (se 3 (by rfl) ⟨178214, by rfl⟩ : syracuseStep 950477 = 356429) (by norm_num)
theorem B950501 : Blo 630300 950501 := bbase (se 4 (by rfl) ⟨89109, by rfl⟩ : syracuseStep 950501 = 178219) (by norm_num)
theorem B950525 : Blo 630300 950525 := bbase (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) (by norm_num)
theorem B950549 : Blo 630300 950549 := bbase (se 6 (by rfl) ⟨22278, by rfl⟩ : syracuseStep 950549 = 44557) (by norm_num)
theorem B1802533 : Blo 630300 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B950573 : Blo 630300 950573 := bbase (se 3 (by rfl) ⟨178232, by rfl⟩ : syracuseStep 950573 = 356465) (by norm_num)
theorem B2130245 : Blo 630300 2130245 := bbase (se 4 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 2130245 = 399421) (by norm_num)
theorem B950597 : Blo 630300 950597 := bbase (se 4 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 950597 = 178237) (by norm_num)
theorem B950621 : Blo 630300 950621 := bbase (se 3 (by rfl) ⟨178241, by rfl⟩ : syracuseStep 950621 = 356483) (by norm_num)
theorem B950645 : Blo 630300 950645 := bbase (se 5 (by rfl) ⟨44561, by rfl⟩ : syracuseStep 950645 = 89123) (by norm_num)
theorem B950669 : Blo 630300 950669 := bbase (se 3 (by rfl) ⟨178250, by rfl⟩ : syracuseStep 950669 = 356501) (by norm_num)
theorem B1704341 : Blo 630300 1704341 := bbase (se 6 (by rfl) ⟨39945, by rfl⟩ : syracuseStep 1704341 = 79891) (by norm_num)
theorem B950693 : Blo 630300 950693 := bbase (se 4 (by rfl) ⟨89127, by rfl⟩ : syracuseStep 950693 = 178255) (by norm_num)
theorem B950717 : Blo 630300 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B950741 : Blo 630300 950741 := bbase (se 7 (by rfl) ⟨11141, by rfl⟩ : syracuseStep 950741 = 22283) (by norm_num)
theorem B950765 : Blo 630300 950765 := bbase (se 3 (by rfl) ⟨178268, by rfl⟩ : syracuseStep 950765 = 356537) (by norm_num)
theorem B950789 : Blo 630300 950789 := bbase (se 4 (by rfl) ⟨89136, by rfl⟩ : syracuseStep 950789 = 178273) (by norm_num)
theorem B950813 : Blo 630300 950813 := bbase (se 3 (by rfl) ⟨178277, by rfl⟩ : syracuseStep 950813 = 356555) (by norm_num)
theorem B950837 : Blo 630300 950837 := bbase (se 5 (by rfl) ⟨44570, by rfl⟩ : syracuseStep 950837 = 89141) (by norm_num)
theorem B950861 : Blo 630300 950861 := bbase (se 3 (by rfl) ⟨178286, by rfl⟩ : syracuseStep 950861 = 356573) (by norm_num)
theorem B950885 : Blo 630300 950885 := bbase (se 4 (by rfl) ⟨89145, by rfl⟩ : syracuseStep 950885 = 178291) (by norm_num)
theorem B950909 : Blo 630300 950909 := bbase (se 3 (by rfl) ⟨178295, by rfl⟩ : syracuseStep 950909 = 356591) (by norm_num)
theorem B950933 : Blo 630300 950933 := bbase (se 6 (by rfl) ⟨22287, by rfl⟩ : syracuseStep 950933 = 44575) (by norm_num)
theorem B950957 : Blo 630300 950957 := bbase (se 3 (by rfl) ⟨178304, by rfl⟩ : syracuseStep 950957 = 356609) (by norm_num)
theorem B4063925 : Blo 630300 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B950981 : Blo 630300 950981 := bbase (se 4 (by rfl) ⟨89154, by rfl⟩ : syracuseStep 950981 = 178309) (by norm_num)
theorem B951005 : Blo 630300 951005 := bbase (se 3 (by rfl) ⟨178313, by rfl⟩ : syracuseStep 951005 = 356627) (by norm_num)
theorem B2130677 : Blo 630300 2130677 := bbase (se 5 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 2130677 = 199751) (by norm_num)
theorem B951029 : Blo 630300 951029 := bbase (se 5 (by rfl) ⟨44579, by rfl⟩ : syracuseStep 951029 = 89159) (by norm_num)
theorem B951053 : Blo 630300 951053 := bbase (se 3 (by rfl) ⟨178322, by rfl⟩ : syracuseStep 951053 = 356645) (by norm_num)
theorem B3605269 : Blo 630300 3605269 := bbase (se 6 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 3605269 = 168997) (by norm_num)
theorem B951077 : Blo 630300 951077 := bbase (se 4 (by rfl) ⟨89163, by rfl⟩ : syracuseStep 951077 = 178327) (by norm_num)
theorem B951101 : Blo 630300 951101 := bbase (se 3 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 951101 = 356663) (by norm_num)
theorem B951125 : Blo 630300 951125 := bbase (se 9 (by rfl) ⟨2786, by rfl⟩ : syracuseStep 951125 = 5573) (by norm_num)
theorem B951149 : Blo 630300 951149 := bbase (se 3 (by rfl) ⟨178340, by rfl⟩ : syracuseStep 951149 = 356681) (by norm_num)
theorem B951173 : Blo 630300 951173 := bbase (se 4 (by rfl) ⟨89172, by rfl⟩ : syracuseStep 951173 = 178345) (by norm_num)
theorem B951197 : Blo 630300 951197 := bbase (se 3 (by rfl) ⟨178349, by rfl⟩ : syracuseStep 951197 = 356699) (by norm_num)
theorem B951221 : Blo 630300 951221 := bbase (se 5 (by rfl) ⟨44588, by rfl⟩ : syracuseStep 951221 = 89177) (by norm_num)
theorem B951245 : Blo 630300 951245 := bbase (se 3 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 951245 = 356717) (by norm_num)
theorem B951269 : Blo 630300 951269 := bbase (se 4 (by rfl) ⟨89181, by rfl⟩ : syracuseStep 951269 = 178363) (by norm_num)
theorem B951293 : Blo 630300 951293 := bbase (se 3 (by rfl) ⟨178367, by rfl⟩ : syracuseStep 951293 = 356735) (by norm_num)
theorem B951317 : Blo 630300 951317 := bbase (se 6 (by rfl) ⟨22296, by rfl⟩ : syracuseStep 951317 = 44593) (by norm_num)
theorem B951341 : Blo 630300 951341 := bbase (se 3 (by rfl) ⟨178376, by rfl⟩ : syracuseStep 951341 = 356753) (by norm_num)
theorem B951365 : Blo 630300 951365 := bbase (se 4 (by rfl) ⟨89190, by rfl⟩ : syracuseStep 951365 = 178381) (by norm_num)
theorem B951389 : Blo 630300 951389 := bbase (se 3 (by rfl) ⟨178385, by rfl⟩ : syracuseStep 951389 = 356771) (by norm_num)
theorem B951413 : Blo 630300 951413 := bbase (se 5 (by rfl) ⟨44597, by rfl⟩ : syracuseStep 951413 = 89195) (by norm_num)
theorem B951437 : Blo 630300 951437 := bbase (se 3 (by rfl) ⟨178394, by rfl⟩ : syracuseStep 951437 = 356789) (by norm_num)
theorem B2131109 : Blo 630300 2131109 := bbase (se 4 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 2131109 = 399583) (by norm_num)
theorem B10781909 : Blo 630300 10781909 := bbase (se 7 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 10781909 = 252701) (by norm_num)
theorem B722197 : Blo 630300 722197 := bbase (se 6 (by rfl) ⟨16926, by rfl⟩ : syracuseStep 722197 = 33853) (by norm_num)
theorem B10257749 : Blo 630300 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B1803637 : Blo 630300 1803637 := bbase (se 5 (by rfl) ⟨84545, by rfl⟩ : syracuseStep 1803637 = 169091) (by norm_num)
theorem B853429 : Blo 630300 853429 := bbase (se 5 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 853429 = 80009) (by norm_num)
theorem B2131541 : Blo 630300 2131541 := bbase (se 8 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 2131541 = 24979) (by norm_num)
theorem B5408693 : Blo 630300 5408693 := bbase (se 5 (by rfl) ⟨253532, by rfl⟩ : syracuseStep 5408693 = 507065) (by norm_num)
theorem B2131973 : Blo 630300 2131973 := bbase (se 4 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 2131973 = 399745) (by norm_num)
theorem B4786613 : Blo 630300 4786613 := bbase (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) (by norm_num)
theorem B2132405 : Blo 630300 2132405 := bbase (se 5 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 2132405 = 199913) (by norm_num)
theorem B1280485 : Blo 630300 1280485 := bbase (se 4 (by rfl) ⟨120045, by rfl⟩ : syracuseStep 1280485 = 240091) (by norm_num)
theorem B2394629 : Blo 630300 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B3410581 : Blo 630300 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B3607253 : Blo 630300 3607253 := bbase (se 7 (by rfl) ⟨42272, by rfl⟩ : syracuseStep 3607253 = 84545) (by norm_num)
theorem B2394917 : Blo 630300 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B1805141 : Blo 630300 1805141 := bbase (se 9 (by rfl) ⟨5288, by rfl⟩ : syracuseStep 1805141 = 10577) (by norm_num)
theorem B2132837 : Blo 630300 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B1281005 : Blo 630300 1281005 := bbase (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) (by norm_num)
theorem B4557845 : Blo 630300 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B2428181 : Blo 630300 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B2133269 : Blo 630300 2133269 := bbase (se 6 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 2133269 = 99997) (by norm_num)
theorem B1346885 : Blo 630300 1346885 := bbase (se 4 (by rfl) ⟨126270, by rfl⟩ : syracuseStep 1346885 = 252541) (by norm_num)
theorem B2198869 : Blo 630300 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B1347005 : Blo 630300 1347005 := bbase (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) (by norm_num)
theorem B2559509 : Blo 630300 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B2133701 : Blo 630300 2133701 := bbase (se 4 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 2133701 = 400069) (by norm_num)
theorem B757469 : Blo 630300 757469 := bbase (se 3 (by rfl) ⟨142025, by rfl⟩ : syracuseStep 757469 = 284051) (by norm_num)
theorem B855949 : Blo 630300 855949 := bbase (se 3 (by rfl) ⟨160490, by rfl⟩ : syracuseStep 855949 = 320981) (by norm_num)
theorem B2396101 : Blo 630300 2396101 := bbase (se 4 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 2396101 = 449269) (by norm_num)
theorem B757777 : Blo 630300 757777 := bbase (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) (by norm_num)
theorem B1347637 : Blo 630300 1347637 := bbase (se 5 (by rfl) ⟨63170, by rfl⟩ : syracuseStep 1347637 = 126341) (by norm_num)
theorem B757873 : Blo 630300 757873 := bbase (se 2 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 757873 = 568405) (by norm_num)
theorem B2134133 : Blo 630300 2134133 := bbase (se 5 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 2134133 = 200075) (by norm_num)
theorem B757921 : Blo 630300 757921 := bbase (se 2 (by rfl) ⟨284220, by rfl⟩ : syracuseStep 757921 = 568441) (by norm_num)
theorem B2396405 : Blo 630300 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B1446365 : Blo 630300 1446365 := bbase (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) (by norm_num)
theorem B8098325 : Blo 630300 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B1217045 : Blo 630300 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B2134565 : Blo 630300 2134565 := bbase (se 4 (by rfl) ⟨200115, by rfl⟩ : syracuseStep 2134565 = 400231) (by norm_num)
theorem B3609461 : Blo 630300 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B1708933 : Blo 630300 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B1348525 : Blo 630300 1348525 := bbase (se 3 (by rfl) ⟨252848, by rfl⟩ : syracuseStep 1348525 = 505697) (by norm_num)
theorem B2134997 : Blo 630300 2134997 := bbase (se 7 (by rfl) ⟨25019, by rfl⟩ : syracuseStep 2134997 = 50039) (by norm_num)
theorem B693257 : Blo 630300 693257 := bbase (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) (by norm_num)
theorem B1348645 : Blo 630300 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B1348901 : Blo 630300 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B759137 : Blo 630300 759137 := bbase (se 2 (by rfl) ⟨284676, by rfl⟩ : syracuseStep 759137 = 569353) (by norm_num)
theorem B2135429 : Blo 630300 2135429 := bbase (se 4 (by rfl) ⟨200196, by rfl⟩ : syracuseStep 2135429 = 400393) (by norm_num)
theorem B759305 : Blo 630300 759305 := bbase (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) (by norm_num)
theorem B1218277 : Blo 630300 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B5117717 : Blo 630300 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B2135861 : Blo 630300 2135861 := bbase (se 5 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 2135861 = 200237) (by norm_num)
theorem B759613 : Blo 630300 759613 := bbase (se 3 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 759613 = 284855) (by norm_num)
theorem B759829 : Blo 630300 759829 := bbase (se 6 (by rfl) ⟨17808, by rfl⟩ : syracuseStep 759829 = 35617) (by norm_num)
theorem B1251389 : Blo 630300 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B2693189 : Blo 630300 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B1349789 : Blo 630300 1349789 := bbase (se 3 (by rfl) ⟨253085, by rfl⟩ : syracuseStep 1349789 = 506171) (by norm_num)
theorem B2136293 : Blo 630300 2136293 := bbase (se 4 (by rfl) ⟨200277, by rfl⟩ : syracuseStep 2136293 = 400555) (by norm_num)
theorem B1710341 : Blo 630300 1710341 := bbase (se 4 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 1710341 = 320689) (by norm_num)
theorem B2398517 : Blo 630300 2398517 := bbase (se 5 (by rfl) ⟨112430, by rfl⟩ : syracuseStep 2398517 = 224861) (by norm_num)
theorem B760141 : Blo 630300 760141 := bbase (se 3 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 760141 = 285053) (by norm_num)
theorem B1350029 : Blo 630300 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B2169317 : Blo 630300 2169317 := bbase (se 4 (by rfl) ⟨203373, by rfl⟩ : syracuseStep 2169317 = 406747) (by norm_num)
theorem B7281173 : Blo 630300 7281173 := bbase (se 6 (by rfl) ⟨170652, by rfl⟩ : syracuseStep 7281173 = 341305) (by norm_num)
theorem B2595349 : Blo 630300 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B6068789 : Blo 630300 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B3414581 : Blo 630300 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B1055285 : Blo 630300 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B2398805 : Blo 630300 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B1284749 : Blo 630300 1284749 := bbase (se 3 (by rfl) ⟨240890, by rfl⟩ : syracuseStep 1284749 = 481781) (by norm_num)
theorem B2136725 : Blo 630300 2136725 := bbase (se 6 (by rfl) ⟨50079, by rfl⟩ : syracuseStep 2136725 = 100159) (by norm_num)
theorem B1350533 : Blo 630300 1350533 := bbase (se 4 (by rfl) ⟨126612, by rfl⟩ : syracuseStep 1350533 = 253225) (by norm_num)
theorem B1350541 : Blo 630300 1350541 := bbase (se 3 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 1350541 = 506453) (by norm_num)
theorem B1514477 : Blo 630300 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B2137157 : Blo 630300 2137157 := bbase (se 4 (by rfl) ⟨200358, by rfl⟩ : syracuseStep 2137157 = 400717) (by norm_num)
theorem B3251285 : Blo 630300 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B2137589 : Blo 630300 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B2399989 : Blo 630300 2399989 := bbase (se 5 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 2399989 = 224999) (by norm_num)
theorem B761621 : Blo 630300 761621 := bbase (se 6 (by rfl) ⟨17850, by rfl⟩ : syracuseStep 761621 = 35701) (by norm_num)
theorem B761717 : Blo 630300 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B761737 : Blo 630300 761737 := bbase (se 2 (by rfl) ⟨285651, by rfl⟩ : syracuseStep 761737 = 571303) (by norm_num)
theorem B2138021 : Blo 630300 2138021 := bbase (se 4 (by rfl) ⟨200439, by rfl⟩ : syracuseStep 2138021 = 400879) (by norm_num)
theorem B1351669 : Blo 630300 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B761881 : Blo 630300 761881 := bbase (se 2 (by rfl) ⟨285705, by rfl⟩ : syracuseStep 761881 = 571411) (by norm_num)
theorem B2400293 : Blo 630300 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B3416309 : Blo 630300 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B2138453 : Blo 630300 2138453 := bbase (se 10 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 2138453 = 6265) (by norm_num)
theorem B1352045 : Blo 630300 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B1024453 : Blo 630300 1024453 := bbase (se 4 (by rfl) ⟨96042, by rfl⟩ : syracuseStep 1024453 = 192085) (by norm_num)
theorem B1253981 : Blo 630300 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B959197 : Blo 630300 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B2138885 : Blo 630300 2138885 := bbase (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) (by norm_num)
theorem B6595445 : Blo 630300 6595445 := bbase (se 5 (by rfl) ⟨309161, by rfl⟩ : syracuseStep 6595445 = 618323) (by norm_num)
theorem B1713109 : Blo 630300 1713109 := bbase (se 7 (by rfl) ⟨20075, by rfl⟩ : syracuseStep 1713109 = 40151) (by norm_num)
theorem B1418237 : Blo 630300 1418237 := bbase (se 3 (by rfl) ⟨265919, by rfl⟩ : syracuseStep 1418237 = 531839) (by norm_num)
theorem B1418309 : Blo 630300 1418309 := bbase (se 4 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 1418309 = 265933) (by norm_num)
theorem B1418381 : Blo 630300 1418381 := bbase (se 3 (by rfl) ⟨265946, by rfl⟩ : syracuseStep 1418381 = 531893) (by norm_num)
theorem B2139317 : Blo 630300 2139317 := bbase (se 5 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 2139317 = 200561) (by norm_num)
theorem B1418453 : Blo 630300 1418453 := bbase (se 7 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 1418453 = 33245) (by norm_num)
theorem B1516765 : Blo 630300 1516765 := bbase (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) (by norm_num)
theorem B1418525 : Blo 630300 1418525 := bbase (se 3 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 1418525 = 531947) (by norm_num)
theorem B1418597 : Blo 630300 1418597 := bbase (se 4 (by rfl) ⟨132993, by rfl⟩ : syracuseStep 1418597 = 265987) (by norm_num)
theorem B1418669 : Blo 630300 1418669 := bbase (se 3 (by rfl) ⟨266000, by rfl⟩ : syracuseStep 1418669 = 532001) (by norm_num)
theorem B1418741 : Blo 630300 1418741 := bbase (se 5 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 1418741 = 133007) (by norm_num)
theorem B2336261 : Blo 630300 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1418813 : Blo 630300 1418813 := bbase (se 3 (by rfl) ⟨266027, by rfl⟩ : syracuseStep 1418813 = 532055) (by norm_num)
theorem B1025597 : Blo 630300 1025597 := bbase (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) (by norm_num)
theorem B2139749 : Blo 630300 2139749 := bbase (se 4 (by rfl) ⟨200601, by rfl⟩ : syracuseStep 2139749 = 401203) (by norm_num)
theorem B1418885 : Blo 630300 1418885 := bbase (se 4 (by rfl) ⟨133020, by rfl⟩ : syracuseStep 1418885 = 266041) (by norm_num)
theorem B1418957 : Blo 630300 1418957 := bbase (se 3 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 1418957 = 532109) (by norm_num)
theorem B3155669 : Blo 630300 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B960229 : Blo 630300 960229 := bbase (se 4 (by rfl) ⟨90021, by rfl⟩ : syracuseStep 960229 = 180043) (by norm_num)
theorem B1419029 : Blo 630300 1419029 := bbase (se 6 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 1419029 = 66517) (by norm_num)
theorem B1713973 : Blo 630300 1713973 := bbase (se 5 (by rfl) ⟨80342, by rfl⟩ : syracuseStep 1713973 = 160685) (by norm_num)
theorem B1419101 : Blo 630300 1419101 := bbase (se 3 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 1419101 = 532163) (by norm_num)
theorem B1517429 : Blo 630300 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B1419173 : Blo 630300 1419173 := bbase (se 4 (by rfl) ⟨133047, by rfl⟩ : syracuseStep 1419173 = 266095) (by norm_num)
theorem B1353685 : Blo 630300 1353685 := bbase (se 7 (by rfl) ⟨15863, by rfl⟩ : syracuseStep 1353685 = 31727) (by norm_num)
theorem B1419245 : Blo 630300 1419245 := bbase (se 3 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 1419245 = 532217) (by norm_num)
theorem B4794389 : Blo 630300 4794389 := bbase (se 6 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 4794389 = 224737) (by norm_num)
theorem B2140181 : Blo 630300 2140181 := bbase (se 6 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 2140181 = 100321) (by norm_num)
theorem B1419317 : Blo 630300 1419317 := bbase (se 5 (by rfl) ⟨66530, by rfl⟩ : syracuseStep 1419317 = 133061) (by norm_num)
theorem B13674581 : Blo 630300 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B2402405 : Blo 630300 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B1419389 : Blo 630300 1419389 := bbase (se 3 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 1419389 = 532271) (by norm_num)
theorem B1419461 : Blo 630300 1419461 := bbase (se 4 (by rfl) ⟨133074, by rfl⟩ : syracuseStep 1419461 = 266149) (by norm_num)
theorem B2697461 : Blo 630300 2697461 := bbase (se 5 (by rfl) ⟨126443, by rfl⟩ : syracuseStep 2697461 = 252887) (by norm_num)
theorem B1419533 : Blo 630300 1419533 := bbase (se 3 (by rfl) ⟨266162, by rfl⟩ : syracuseStep 1419533 = 532325) (by norm_num)
theorem B1419605 : Blo 630300 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B2402693 : Blo 630300 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B1419677 : Blo 630300 1419677 := bbase (se 3 (by rfl) ⟨266189, by rfl⟩ : syracuseStep 1419677 = 532379) (by norm_num)
theorem B2140613 : Blo 630300 2140613 := bbase (se 4 (by rfl) ⟨200682, by rfl⟩ : syracuseStep 2140613 = 401365) (by norm_num)
theorem B1419749 : Blo 630300 1419749 := bbase (se 4 (by rfl) ⟨133101, by rfl⟩ : syracuseStep 1419749 = 266203) (by norm_num)
theorem B1419821 : Blo 630300 1419821 := bbase (se 3 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 1419821 = 532433) (by norm_num)
theorem B2108005 : Blo 630300 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B1419893 : Blo 630300 1419893 := bbase (se 5 (by rfl) ⟨66557, by rfl⟩ : syracuseStep 1419893 = 133115) (by norm_num)
theorem B1419965 : Blo 630300 1419965 := bbase (se 3 (by rfl) ⟨266243, by rfl⟩ : syracuseStep 1419965 = 532487) (by norm_num)
theorem B1420037 : Blo 630300 1420037 := bbase (se 4 (by rfl) ⟨133128, by rfl⟩ : syracuseStep 1420037 = 266257) (by norm_num)
theorem B1944341 : Blo 630300 1944341 := bbase (se 6 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 1944341 = 91141) (by norm_num)
theorem B1420109 : Blo 630300 1420109 := bbase (se 3 (by rfl) ⟨266270, by rfl⟩ : syracuseStep 1420109 = 532541) (by norm_num)
theorem B1354573 : Blo 630300 1354573 := bbase (se 3 (by rfl) ⟨253982, by rfl⟩ : syracuseStep 1354573 = 507965) (by norm_num)
theorem B961373 : Blo 630300 961373 := bbase (se 3 (by rfl) ⟨180257, by rfl⟩ : syracuseStep 961373 = 360515) (by norm_num)
theorem B1420181 : Blo 630300 1420181 := bbase (se 6 (by rfl) ⟨33285, by rfl⟩ : syracuseStep 1420181 = 66571) (by norm_num)
theorem B1420253 : Blo 630300 1420253 := bbase (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) (by norm_num)
theorem B1420325 : Blo 630300 1420325 := bbase (se 4 (by rfl) ⟨133155, by rfl⟩ : syracuseStep 1420325 = 266311) (by norm_num)
theorem B797789 : Blo 630300 797789 := bbase (se 3 (by rfl) ⟨149585, by rfl⟩ : syracuseStep 797789 = 299171) (by norm_num)
theorem B1420397 : Blo 630300 1420397 := bbase (se 3 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 1420397 = 532649) (by norm_num)
theorem B797845 : Blo 630300 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B1420469 : Blo 630300 1420469 := bbase (se 5 (by rfl) ⟨66584, by rfl⟩ : syracuseStep 1420469 = 133169) (by norm_num)
theorem B1518821 : Blo 630300 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B797941 : Blo 630300 797941 := bbase (se 5 (by rfl) ⟨37403, by rfl⟩ : syracuseStep 797941 = 74807) (by norm_num)
theorem B1420541 : Blo 630300 1420541 := bbase (se 3 (by rfl) ⟨266351, by rfl⟩ : syracuseStep 1420541 = 532703) (by norm_num)
theorem B1420613 : Blo 630300 1420613 := bbase (se 4 (by rfl) ⟨133182, by rfl⟩ : syracuseStep 1420613 = 266365) (by norm_num)
theorem B1518917 : Blo 630300 1518917 := bbase (se 4 (by rfl) ⟨142398, by rfl⟩ : syracuseStep 1518917 = 284797) (by norm_num)
theorem B1420685 : Blo 630300 1420685 := bbase (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) (by norm_num)
theorem B798113 : Blo 630300 798113 := bbase (se 2 (by rfl) ⟨299292, by rfl⟩ : syracuseStep 798113 = 598585) (by norm_num)
theorem B1420757 : Blo 630300 1420757 := bbase (se 7 (by rfl) ⟨16649, by rfl⟩ : syracuseStep 1420757 = 33299) (by norm_num)
theorem B962005 : Blo 630300 962005 := bbase (se 7 (by rfl) ⟨11273, by rfl⟩ : syracuseStep 962005 = 22547) (by norm_num)
theorem B798169 : Blo 630300 798169 := bbase (se 2 (by rfl) ⟨299313, by rfl⟩ : syracuseStep 798169 = 598627) (by norm_num)
theorem B1420829 : Blo 630300 1420829 := bbase (se 3 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 1420829 = 532811) (by norm_num)
theorem B2403877 : Blo 630300 2403877 := bbase (se 4 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 2403877 = 450727) (by norm_num)
theorem B798265 : Blo 630300 798265 := bbase (se 2 (by rfl) ⟨299349, by rfl⟩ : syracuseStep 798265 = 598699) (by norm_num)
theorem B831061 : Blo 630300 831061 := bbase (se 8 (by rfl) ⟨4869, by rfl⟩ : syracuseStep 831061 = 9739) (by norm_num)
theorem B1420901 : Blo 630300 1420901 := bbase (se 4 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 1420901 = 266419) (by norm_num)
theorem B1420973 : Blo 630300 1420973 := bbase (se 3 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 1420973 = 532865) (by norm_num)
theorem B798437 : Blo 630300 798437 := bbase (se 4 (by rfl) ⟨74853, by rfl⟩ : syracuseStep 798437 = 149707) (by norm_num)
theorem B1421045 : Blo 630300 1421045 := bbase (se 5 (by rfl) ⟨66611, by rfl⟩ : syracuseStep 1421045 = 133223) (by norm_num)
theorem B798493 : Blo 630300 798493 := bbase (se 3 (by rfl) ⟨149717, by rfl⟩ : syracuseStep 798493 = 299435) (by norm_num)
theorem B1027885 : Blo 630300 1027885 := bbase (se 3 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 1027885 = 385457) (by norm_num)
theorem B1421117 : Blo 630300 1421117 := bbase (se 3 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 1421117 = 532919) (by norm_num)
theorem B2404181 : Blo 630300 2404181 := bbase (se 9 (by rfl) ⟨7043, by rfl⟩ : syracuseStep 2404181 = 14087) (by norm_num)
theorem B4566901 : Blo 630300 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B798589 : Blo 630300 798589 := bbase (se 3 (by rfl) ⟨149735, by rfl⟩ : syracuseStep 798589 = 299471) (by norm_num)
theorem B1421189 : Blo 630300 1421189 := bbase (se 4 (by rfl) ⟨133236, by rfl⟩ : syracuseStep 1421189 = 266473) (by norm_num)
theorem B1421261 : Blo 630300 1421261 := bbase (se 3 (by rfl) ⟨266486, by rfl⟩ : syracuseStep 1421261 = 532973) (by norm_num)
theorem B2699237 : Blo 630300 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B1421333 : Blo 630300 1421333 := bbase (se 6 (by rfl) ⟨33312, by rfl⟩ : syracuseStep 1421333 = 66625) (by norm_num)
theorem B798761 : Blo 630300 798761 := bbase (se 2 (by rfl) ⟨299535, by rfl⟩ : syracuseStep 798761 = 599071) (by norm_num)
theorem B1421405 : Blo 630300 1421405 := bbase (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) (by norm_num)
theorem B798817 : Blo 630300 798817 := bbase (se 2 (by rfl) ⟨299556, by rfl⟩ : syracuseStep 798817 = 599113) (by norm_num)
theorem B1421477 : Blo 630300 1421477 := bbase (se 4 (by rfl) ⟨133263, by rfl⟩ : syracuseStep 1421477 = 266527) (by norm_num)
theorem B798913 : Blo 630300 798913 := bbase (se 2 (by rfl) ⟨299592, by rfl⟩ : syracuseStep 798913 = 599185) (by norm_num)
theorem B2699477 : Blo 630300 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1421549 : Blo 630300 1421549 := bbase (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) (by norm_num)
theorem B1618213 : Blo 630300 1618213 := bbase (se 4 (by rfl) ⟨151707, by rfl⟩ : syracuseStep 1618213 = 303415) (by norm_num)
theorem B1421621 : Blo 630300 1421621 := bbase (se 5 (by rfl) ⟨66638, by rfl⟩ : syracuseStep 1421621 = 133277) (by norm_num)
theorem B799085 : Blo 630300 799085 := bbase (se 3 (by rfl) ⟨149828, by rfl⟩ : syracuseStep 799085 = 299657) (by norm_num)
theorem B1421693 : Blo 630300 1421693 := bbase (se 3 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 1421693 = 533135) (by norm_num)
theorem B799141 : Blo 630300 799141 := bbase (se 4 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 799141 = 149839) (by norm_num)
theorem B1388981 : Blo 630300 1388981 := bbase (se 5 (by rfl) ⟨65108, by rfl⟩ : syracuseStep 1388981 = 130217) (by norm_num)
theorem B3191237 : Blo 630300 3191237 := bbase (se 4 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 3191237 = 598357) (by norm_num)
theorem B1421765 : Blo 630300 1421765 := bbase (se 4 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 1421765 = 266581) (by norm_num)
theorem B799237 : Blo 630300 799237 := bbase (se 4 (by rfl) ⟨74928, by rfl⟩ : syracuseStep 799237 = 149857) (by norm_num)
theorem B1421837 : Blo 630300 1421837 := bbase (se 3 (by rfl) ⟨266594, by rfl⟩ : syracuseStep 1421837 = 533189) (by norm_num)
theorem B1421909 : Blo 630300 1421909 := bbase (se 8 (by rfl) ⟨8331, by rfl⟩ : syracuseStep 1421909 = 16663) (by norm_num)
theorem B963173 : Blo 630300 963173 := bbase (se 4 (by rfl) ⟨90297, by rfl⟩ : syracuseStep 963173 = 180595) (by norm_num)
theorem B1421981 : Blo 630300 1421981 := bbase (se 3 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 1421981 = 533243) (by norm_num)
theorem B799409 : Blo 630300 799409 := bbase (se 2 (by rfl) ⟨299778, by rfl⟩ : syracuseStep 799409 = 599557) (by norm_num)
theorem B1422053 : Blo 630300 1422053 := bbase (se 4 (by rfl) ⟨133317, by rfl⟩ : syracuseStep 1422053 = 266635) (by norm_num)
theorem B799465 : Blo 630300 799465 := bbase (se 2 (by rfl) ⟨299799, by rfl⟩ : syracuseStep 799465 = 599599) (by norm_num)
theorem B1422125 : Blo 630300 1422125 := bbase (se 3 (by rfl) ⟨266648, by rfl⟩ : syracuseStep 1422125 = 533297) (by norm_num)
theorem B799561 : Blo 630300 799561 := bbase (se 2 (by rfl) ⟨299835, by rfl⟩ : syracuseStep 799561 = 599671) (by norm_num)
theorem B1422197 : Blo 630300 1422197 := bbase (se 5 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 1422197 = 133331) (by norm_num)
theorem B7189397 : Blo 630300 7189397 := bbase (se 6 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 7189397 = 337003) (by norm_num)
theorem B1422269 : Blo 630300 1422269 := bbase (se 3 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 1422269 = 533351) (by norm_num)
theorem B799733 : Blo 630300 799733 := bbase (se 5 (by rfl) ⟨37487, by rfl⟩ : syracuseStep 799733 = 74975) (by norm_num)
theorem B1422341 : Blo 630300 1422341 := bbase (se 4 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 1422341 = 266689) (by norm_num)
theorem B799789 : Blo 630300 799789 := bbase (se 3 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 799789 = 299921) (by norm_num)
theorem B1422413 : Blo 630300 1422413 := bbase (se 3 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 1422413 = 533405) (by norm_num)
theorem B799885 : Blo 630300 799885 := bbase (se 3 (by rfl) ⟨149978, by rfl⟩ : syracuseStep 799885 = 299957) (by norm_num)
theorem B1422485 : Blo 630300 1422485 := bbase (se 6 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 1422485 = 66679) (by norm_num)
theorem B963733 : Blo 630300 963733 := bbase (se 6 (by rfl) ⟨22587, by rfl⟩ : syracuseStep 963733 = 45175) (by norm_num)
theorem B2929829 : Blo 630300 2929829 := bbase (se 4 (by rfl) ⟨274671, by rfl⟩ : syracuseStep 2929829 = 549343) (by norm_num)
theorem B1422557 : Blo 630300 1422557 := bbase (se 3 (by rfl) ⟨266729, by rfl⟩ : syracuseStep 1422557 = 533459) (by norm_num)
theorem B1422629 : Blo 630300 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B800057 : Blo 630300 800057 := bbase (se 2 (by rfl) ⟨300021, by rfl⟩ : syracuseStep 800057 = 600043) (by norm_num)
theorem B1422701 : Blo 630300 1422701 := bbase (se 3 (by rfl) ⟨266756, by rfl⟩ : syracuseStep 1422701 = 533513) (by norm_num)
theorem B800113 : Blo 630300 800113 := bbase (se 2 (by rfl) ⟨300042, by rfl⟩ : syracuseStep 800113 = 600085) (by norm_num)
theorem B1521013 : Blo 630300 1521013 := bbase (se 5 (by rfl) ⟨71297, by rfl⟩ : syracuseStep 1521013 = 142595) (by norm_num)
theorem B1422773 : Blo 630300 1422773 := bbase (se 5 (by rfl) ⟨66692, by rfl⟩ : syracuseStep 1422773 = 133385) (by norm_num)
theorem B800209 : Blo 630300 800209 := bbase (se 2 (by rfl) ⟨300078, by rfl⟩ : syracuseStep 800209 = 600157) (by norm_num)
theorem B1422845 : Blo 630300 1422845 := bbase (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) (by norm_num)
theorem B1619525 : Blo 630300 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B1422917 : Blo 630300 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B800381 : Blo 630300 800381 := bbase (se 3 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 800381 = 300143) (by norm_num)
theorem B1422989 : Blo 630300 1422989 := bbase (se 3 (by rfl) ⟨266810, by rfl⟩ : syracuseStep 1422989 = 533621) (by norm_num)
theorem B800437 : Blo 630300 800437 := bbase (se 5 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 800437 = 75041) (by norm_num)
theorem B3192533 : Blo 630300 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B1423061 : Blo 630300 1423061 := bbase (se 7 (by rfl) ⟨16676, by rfl⟩ : syracuseStep 1423061 = 33353) (by norm_num)
theorem B898789 : Blo 630300 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B3847925 : Blo 630300 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B800533 : Blo 630300 800533 := bbase (se 6 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 800533 = 37525) (by norm_num)
theorem B1423133 : Blo 630300 1423133 := bbase (se 3 (by rfl) ⟨266837, by rfl⟩ : syracuseStep 1423133 = 533675) (by norm_num)
theorem B1423205 : Blo 630300 1423205 := bbase (se 4 (by rfl) ⟨133425, by rfl⟩ : syracuseStep 1423205 = 266851) (by norm_num)
theorem B2406293 : Blo 630300 2406293 := bbase (se 6 (by rfl) ⟨56397, by rfl⟩ : syracuseStep 2406293 = 112795) (by norm_num)
theorem B1423277 : Blo 630300 1423277 := bbase (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) (by norm_num)
theorem B800705 : Blo 630300 800705 := bbase (se 2 (by rfl) ⟨300264, by rfl⟩ : syracuseStep 800705 = 600529) (by norm_num)
theorem B1521629 : Blo 630300 1521629 := bbase (se 3 (by rfl) ⟨285305, by rfl⟩ : syracuseStep 1521629 = 570611) (by norm_num)
theorem B1423349 : Blo 630300 1423349 := bbase (se 5 (by rfl) ⟨66719, by rfl⟩ : syracuseStep 1423349 = 133439) (by norm_num)
theorem B800761 : Blo 630300 800761 := bbase (se 2 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 800761 = 600571) (by norm_num)
theorem B1423421 : Blo 630300 1423421 := bbase (se 3 (by rfl) ⟨266891, by rfl⟩ : syracuseStep 1423421 = 533783) (by norm_num)
theorem B800857 : Blo 630300 800857 := bbase (se 2 (by rfl) ⟨300321, by rfl⟩ : syracuseStep 800857 = 600643) (by norm_num)
theorem B1620101 : Blo 630300 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B1423493 : Blo 630300 1423493 := bbase (se 4 (by rfl) ⟨133452, by rfl⟩ : syracuseStep 1423493 = 266905) (by norm_num)
theorem B2406581 : Blo 630300 2406581 := bbase (se 5 (by rfl) ⟨112808, by rfl⟩ : syracuseStep 2406581 = 225617) (by norm_num)
theorem B1423565 : Blo 630300 1423565 := bbase (se 3 (by rfl) ⟨266918, by rfl⟩ : syracuseStep 1423565 = 533837) (by norm_num)
theorem B801029 : Blo 630300 801029 := bbase (se 4 (by rfl) ⟨75096, by rfl⟩ : syracuseStep 801029 = 150193) (by norm_num)
theorem B1423637 : Blo 630300 1423637 := bbase (se 6 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 1423637 = 66733) (by norm_num)
theorem B1521965 : Blo 630300 1521965 := bbase (se 3 (by rfl) ⟨285368, by rfl⟩ : syracuseStep 1521965 = 570737) (by norm_num)
theorem B899381 : Blo 630300 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B801085 : Blo 630300 801085 := bbase (se 3 (by rfl) ⟨150203, by rfl⟩ : syracuseStep 801085 = 300407) (by norm_num)
theorem B1423709 : Blo 630300 1423709 := bbase (se 3 (by rfl) ⟨266945, by rfl⟩ : syracuseStep 1423709 = 533891) (by norm_num)
theorem B899461 : Blo 630300 899461 := bbase (se 4 (by rfl) ⟨84324, by rfl⟩ : syracuseStep 899461 = 168649) (by norm_num)
theorem B801181 : Blo 630300 801181 := bbase (se 3 (by rfl) ⟨150221, by rfl⟩ : syracuseStep 801181 = 300443) (by norm_num)
theorem B1423781 : Blo 630300 1423781 := bbase (se 4 (by rfl) ⟨133479, by rfl⟩ : syracuseStep 1423781 = 266959) (by norm_num)
theorem B2701765 : Blo 630300 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B1423853 : Blo 630300 1423853 := bbase (se 3 (by rfl) ⟨266972, by rfl⟩ : syracuseStep 1423853 = 533945) (by norm_num)
theorem B899581 : Blo 630300 899581 := bbase (se 3 (by rfl) ⟨168671, by rfl⟩ : syracuseStep 899581 = 337343) (by norm_num)
theorem B1423925 : Blo 630300 1423925 := bbase (se 5 (by rfl) ⟨66746, by rfl⟩ : syracuseStep 1423925 = 133493) (by norm_num)
theorem B801353 : Blo 630300 801353 := bbase (se 2 (by rfl) ⟨300507, by rfl⟩ : syracuseStep 801353 = 601015) (by norm_num)
theorem B899677 : Blo 630300 899677 := bbase (se 3 (by rfl) ⟨168689, by rfl⟩ : syracuseStep 899677 = 337379) (by norm_num)
theorem B1423997 : Blo 630300 1423997 := bbase (se 3 (by rfl) ⟨266999, by rfl⟩ : syracuseStep 1423997 = 533999) (by norm_num)
theorem B801409 : Blo 630300 801409 := bbase (se 2 (by rfl) ⟨300528, by rfl⟩ : syracuseStep 801409 = 601057) (by norm_num)
theorem B1522357 : Blo 630300 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B1424069 : Blo 630300 1424069 := bbase (se 4 (by rfl) ⟨133506, by rfl⟩ : syracuseStep 1424069 = 267013) (by norm_num)
theorem B801505 : Blo 630300 801505 := bbase (se 2 (by rfl) ⟨300564, by rfl⟩ : syracuseStep 801505 = 601129) (by norm_num)
theorem B1063685 : Blo 630300 1063685 := bbase (se 4 (by rfl) ⟨99720, by rfl⟩ : syracuseStep 1063685 = 199441) (by norm_num)
theorem B1424141 : Blo 630300 1424141 := bbase (se 3 (by rfl) ⟨267026, by rfl⟩ : syracuseStep 1424141 = 534053) (by norm_num)
theorem B1424213 : Blo 630300 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B1063813 : Blo 630300 1063813 := bbase (se 4 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 1063813 = 199465) (by norm_num)
theorem B801677 : Blo 630300 801677 := bbase (se 3 (by rfl) ⟨150314, by rfl⟩ : syracuseStep 801677 = 300629) (by norm_num)
theorem B1424285 : Blo 630300 1424285 := bbase (se 3 (by rfl) ⟨267053, by rfl⟩ : syracuseStep 1424285 = 534107) (by norm_num)
theorem B801733 : Blo 630300 801733 := bbase (se 4 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 801733 = 150325) (by norm_num)
theorem B1063901 : Blo 630300 1063901 := bbase (se 3 (by rfl) ⟨199481, by rfl⟩ : syracuseStep 1063901 = 398963) (by norm_num)
theorem B3193829 : Blo 630300 3193829 := bbase (se 4 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 3193829 = 598843) (by norm_num)
theorem B1424357 : Blo 630300 1424357 := bbase (se 4 (by rfl) ⟨133533, by rfl⟩ : syracuseStep 1424357 = 267067) (by norm_num)
theorem B801829 : Blo 630300 801829 := bbase (se 4 (by rfl) ⟨75171, by rfl⟩ : syracuseStep 801829 = 150343) (by norm_num)
theorem B1424429 : Blo 630300 1424429 := bbase (se 3 (by rfl) ⟨267080, by rfl⟩ : syracuseStep 1424429 = 534161) (by norm_num)
theorem B900173 : Blo 630300 900173 := bbase (se 3 (by rfl) ⟨168782, by rfl⟩ : syracuseStep 900173 = 337565) (by norm_num)
theorem B15416405 : Blo 630300 15416405 := bbase (se 8 (by rfl) ⟨90330, by rfl⟩ : syracuseStep 15416405 = 180661) (by norm_num)
theorem B1064029 : Blo 630300 1064029 := bbase (se 3 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 1064029 = 399011) (by norm_num)
theorem B1424501 : Blo 630300 1424501 := bbase (se 5 (by rfl) ⟨66773, by rfl⟩ : syracuseStep 1424501 = 133547) (by norm_num)
theorem B1064117 : Blo 630300 1064117 := bbase (se 5 (by rfl) ⟨49880, by rfl⟩ : syracuseStep 1064117 = 99761) (by norm_num)
theorem B1424573 : Blo 630300 1424573 := bbase (se 3 (by rfl) ⟨267107, by rfl⟩ : syracuseStep 1424573 = 534215) (by norm_num)
theorem B802001 : Blo 630300 802001 := bbase (se 2 (by rfl) ⟨300750, by rfl⟩ : syracuseStep 802001 = 601501) (by norm_num)
theorem B1424645 : Blo 630300 1424645 := bbase (se 4 (by rfl) ⟨133560, by rfl⟩ : syracuseStep 1424645 = 267121) (by norm_num)
theorem B802057 : Blo 630300 802057 := bbase (se 2 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 802057 = 601543) (by norm_num)
theorem B1064245 : Blo 630300 1064245 := bbase (se 5 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 1064245 = 99773) (by norm_num)
theorem B1424717 : Blo 630300 1424717 := bbase (se 3 (by rfl) ⟨267134, by rfl⟩ : syracuseStep 1424717 = 534269) (by norm_num)
theorem B2407765 : Blo 630300 2407765 := bbase (se 11 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 2407765 = 3527) (by norm_num)
theorem B802153 : Blo 630300 802153 := bbase (se 2 (by rfl) ⟨300807, by rfl⟩ : syracuseStep 802153 = 601615) (by norm_num)
theorem B1064333 : Blo 630300 1064333 := bbase (se 3 (by rfl) ⟨199562, by rfl⟩ : syracuseStep 1064333 = 399125) (by norm_num)
theorem B1424789 : Blo 630300 1424789 := bbase (se 6 (by rfl) ⟨33393, by rfl⟩ : syracuseStep 1424789 = 66787) (by norm_num)
theorem B1424861 : Blo 630300 1424861 := bbase (se 3 (by rfl) ⟨267161, by rfl⟩ : syracuseStep 1424861 = 534323) (by norm_num)
theorem B1064461 : Blo 630300 1064461 := bbase (se 3 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 1064461 = 399173) (by norm_num)
theorem B802325 : Blo 630300 802325 := bbase (se 6 (by rfl) ⟨18804, by rfl⟩ : syracuseStep 802325 = 37609) (by norm_num)
theorem B1424933 : Blo 630300 1424933 := bbase (se 4 (by rfl) ⟨133587, by rfl⟩ : syracuseStep 1424933 = 267175) (by norm_num)
theorem B802381 : Blo 630300 802381 := bbase (se 3 (by rfl) ⟨150446, by rfl⟩ : syracuseStep 802381 = 300893) (by norm_num)
theorem B1064549 : Blo 630300 1064549 := bbase (se 4 (by rfl) ⟨99801, by rfl⟩ : syracuseStep 1064549 = 199603) (by norm_num)
theorem B2637413 : Blo 630300 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B1425005 : Blo 630300 1425005 := bbase (se 3 (by rfl) ⟨267188, by rfl⟩ : syracuseStep 1425005 = 534377) (by norm_num)
theorem B900725 : Blo 630300 900725 := bbase (se 5 (by rfl) ⟨42221, by rfl⟩ : syracuseStep 900725 = 84443) (by norm_num)
theorem B2408069 : Blo 630300 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B802477 : Blo 630300 802477 := bbase (se 3 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 802477 = 300929) (by norm_num)
theorem B1425077 : Blo 630300 1425077 := bbase (se 5 (by rfl) ⟨66800, by rfl⟩ : syracuseStep 1425077 = 133601) (by norm_num)
theorem B2277077 : Blo 630300 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B1064677 : Blo 630300 1064677 := bbase (se 4 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 1064677 = 199627) (by norm_num)
theorem B1425149 : Blo 630300 1425149 := bbase (se 3 (by rfl) ⟨267215, by rfl⟩ : syracuseStep 1425149 = 534431) (by norm_num)
theorem B6176533 : Blo 630300 6176533 := bbase (se 6 (by rfl) ⟨144762, by rfl⟩ : syracuseStep 6176533 = 289525) (by norm_num)
theorem B1064765 : Blo 630300 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B1425221 : Blo 630300 1425221 := bbase (se 4 (by rfl) ⟨133614, by rfl⟩ : syracuseStep 1425221 = 267229) (by norm_num)
theorem B802649 : Blo 630300 802649 := bbase (se 2 (by rfl) ⟨300993, by rfl⟩ : syracuseStep 802649 = 601987) (by norm_num)
theorem B1425293 : Blo 630300 1425293 := bbase (se 3 (by rfl) ⟨267242, by rfl⟩ : syracuseStep 1425293 = 534485) (by norm_num)
theorem B802705 : Blo 630300 802705 := bbase (se 2 (by rfl) ⟨301014, by rfl⟩ : syracuseStep 802705 = 602029) (by norm_num)
theorem B2703253 : Blo 630300 2703253 := bbase (se 6 (by rfl) ⟨63357, by rfl⟩ : syracuseStep 2703253 = 126715) (by norm_num)
theorem B2703269 : Blo 630300 2703269 := bbase (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) (by norm_num)
theorem B1458109 : Blo 630300 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1064893 : Blo 630300 1064893 := bbase (se 3 (by rfl) ⟨199667, by rfl⟩ : syracuseStep 1064893 = 399335) (by norm_num)
theorem B1425365 : Blo 630300 1425365 := bbase (se 7 (by rfl) ⟨16703, by rfl⟩ : syracuseStep 1425365 = 33407) (by norm_num)
theorem B1064981 : Blo 630300 1064981 := bbase (se 6 (by rfl) ⟨24960, by rfl⟩ : syracuseStep 1064981 = 49921) (by norm_num)
theorem B639001 : Blo 630300 639001 := bbase (se 2 (by rfl) ⟨239625, by rfl⟩ : syracuseStep 639001 = 479251) (by norm_num)
theorem B1425437 : Blo 630300 1425437 := bbase (se 3 (by rfl) ⟨267269, by rfl⟩ : syracuseStep 1425437 = 534539) (by norm_num)
theorem B1425509 : Blo 630300 1425509 := bbase (se 4 (by rfl) ⟨133641, by rfl⟩ : syracuseStep 1425509 = 267283) (by norm_num)
theorem B1065109 : Blo 630300 1065109 := bbase (se 6 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 1065109 = 49927) (by norm_num)
theorem B1425581 : Blo 630300 1425581 := bbase (se 3 (by rfl) ⟨267296, by rfl⟩ : syracuseStep 1425581 = 534593) (by norm_num)
theorem B1065197 : Blo 630300 1065197 := bbase (se 3 (by rfl) ⟨199724, by rfl⟩ : syracuseStep 1065197 = 399449) (by norm_num)
theorem B3195125 : Blo 630300 3195125 := bbase (se 5 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 3195125 = 299543) (by norm_num)
theorem B1425653 : Blo 630300 1425653 := bbase (se 5 (by rfl) ⟨66827, by rfl⟩ : syracuseStep 1425653 = 133655) (by norm_num)
theorem B1425725 : Blo 630300 1425725 := bbase (se 3 (by rfl) ⟨267323, by rfl⟩ : syracuseStep 1425725 = 534647) (by norm_num)
theorem B901477 : Blo 630300 901477 := bbase (se 4 (by rfl) ⟨84513, by rfl⟩ : syracuseStep 901477 = 169027) (by norm_num)
theorem B1065325 : Blo 630300 1065325 := bbase (se 3 (by rfl) ⟨199748, by rfl⟩ : syracuseStep 1065325 = 399497) (by norm_num)
theorem B1425797 : Blo 630300 1425797 := bbase (se 4 (by rfl) ⟨133668, by rfl⟩ : syracuseStep 1425797 = 267337) (by norm_num)
theorem B1065413 : Blo 630300 1065413 := bbase (se 4 (by rfl) ⟨99882, by rfl⟩ : syracuseStep 1065413 = 199765) (by norm_num)
theorem B1425869 : Blo 630300 1425869 := bbase (se 3 (by rfl) ⟨267350, by rfl⟩ : syracuseStep 1425869 = 534701) (by norm_num)
theorem B4047317 : Blo 630300 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B6242837 : Blo 630300 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1425941 : Blo 630300 1425941 := bbase (se 6 (by rfl) ⟨33420, by rfl⟩ : syracuseStep 1425941 = 66841) (by norm_num)
theorem B1065541 : Blo 630300 1065541 := bbase (se 4 (by rfl) ⟨99894, by rfl⟩ : syracuseStep 1065541 = 199789) (by norm_num)
theorem B1426013 : Blo 630300 1426013 := bbase (se 3 (by rfl) ⟨267377, by rfl⟩ : syracuseStep 1426013 = 534755) (by norm_num)
theorem B2277989 : Blo 630300 2277989 := bbase (se 4 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 2277989 = 427123) (by norm_num)
theorem B1196669 : Blo 630300 1196669 := bbase (se 3 (by rfl) ⟨224375, by rfl⟩ : syracuseStep 1196669 = 448751) (by norm_num)
theorem B1917589 : Blo 630300 1917589 := bbase (se 6 (by rfl) ⟨44943, by rfl⟩ : syracuseStep 1917589 = 89887) (by norm_num)
theorem B1065629 : Blo 630300 1065629 := bbase (se 3 (by rfl) ⟨199805, by rfl⟩ : syracuseStep 1065629 = 399611) (by norm_num)
theorem B1426085 : Blo 630300 1426085 := bbase (se 4 (by rfl) ⟨133695, by rfl⟩ : syracuseStep 1426085 = 267391) (by norm_num)
theorem B1426157 : Blo 630300 1426157 := bbase (se 3 (by rfl) ⟨267404, by rfl⟩ : syracuseStep 1426157 = 534809) (by norm_num)
theorem B1065757 : Blo 630300 1065757 := bbase (se 3 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 1065757 = 399659) (by norm_num)
theorem B1426229 : Blo 630300 1426229 := bbase (se 5 (by rfl) ⟨66854, by rfl⟩ : syracuseStep 1426229 = 133709) (by norm_num)
theorem B1065845 : Blo 630300 1065845 := bbase (se 5 (by rfl) ⟨49961, by rfl⟩ : syracuseStep 1065845 = 99923) (by norm_num)
theorem B1426301 : Blo 630300 1426301 := bbase (se 3 (by rfl) ⟨267431, by rfl⟩ : syracuseStep 1426301 = 534863) (by norm_num)
theorem B1196957 : Blo 630300 1196957 := bbase (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) (by norm_num)
theorem B1426373 : Blo 630300 1426373 := bbase (se 4 (by rfl) ⟨133722, by rfl⟩ : syracuseStep 1426373 = 267445) (by norm_num)
theorem B1065973 : Blo 630300 1065973 := bbase (se 5 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 1065973 = 99935) (by norm_num)
theorem B1426445 : Blo 630300 1426445 := bbase (se 3 (by rfl) ⟨267458, by rfl⟩ : syracuseStep 1426445 = 534917) (by norm_num)
theorem B1197109 : Blo 630300 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B1066061 : Blo 630300 1066061 := bbase (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) (by norm_num)
theorem B1426517 : Blo 630300 1426517 := bbase (se 8 (by rfl) ⟨8358, by rfl⟩ : syracuseStep 1426517 = 16717) (by norm_num)
theorem B902269 : Blo 630300 902269 := bbase (se 3 (by rfl) ⟨169175, by rfl⟩ : syracuseStep 902269 = 338351) (by norm_num)
theorem B1426589 : Blo 630300 1426589 := bbase (se 3 (by rfl) ⟨267485, by rfl⟩ : syracuseStep 1426589 = 534971) (by norm_num)
theorem B3032261 : Blo 630300 3032261 := bbase (se 4 (by rfl) ⟨284274, by rfl⟩ : syracuseStep 3032261 = 568549) (by norm_num)
theorem B1066189 : Blo 630300 1066189 := bbase (se 3 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 1066189 = 399821) (by norm_num)
theorem B1426661 : Blo 630300 1426661 := bbase (se 4 (by rfl) ⟨133749, by rfl⟩ : syracuseStep 1426661 = 267499) (by norm_num)
theorem B1066277 : Blo 630300 1066277 := bbase (se 4 (by rfl) ⟨99963, by rfl⟩ : syracuseStep 1066277 = 199927) (by norm_num)
theorem B1426733 : Blo 630300 1426733 := bbase (se 3 (by rfl) ⟨267512, by rfl⟩ : syracuseStep 1426733 = 535025) (by norm_num)
theorem B1197413 : Blo 630300 1197413 := bbase (se 4 (by rfl) ⟨112257, by rfl⟩ : syracuseStep 1197413 = 224515) (by norm_num)
theorem B1426805 : Blo 630300 1426805 := bbase (se 5 (by rfl) ⟨66881, by rfl⟩ : syracuseStep 1426805 = 133763) (by norm_num)
theorem B673169 : Blo 630300 673169 := bbase (se 2 (by rfl) ⟨252438, by rfl⟩ : syracuseStep 673169 = 504877) (by norm_num)
theorem B1066405 : Blo 630300 1066405 := bbase (se 4 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 1066405 = 199951) (by norm_num)
theorem B1426877 : Blo 630300 1426877 := bbase (se 3 (by rfl) ⟨267539, by rfl⟩ : syracuseStep 1426877 = 535079) (by norm_num)
theorem B673229 : Blo 630300 673229 := bbase (se 3 (by rfl) ⟨126230, by rfl⟩ : syracuseStep 673229 = 252461) (by norm_num)
theorem B902605 : Blo 630300 902605 := bbase (se 3 (by rfl) ⟨169238, by rfl⟩ : syracuseStep 902605 = 338477) (by norm_num)
theorem B3032549 : Blo 630300 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1066493 : Blo 630300 1066493 := bbase (se 3 (by rfl) ⟨199967, by rfl⟩ : syracuseStep 1066493 = 399935) (by norm_num)
theorem B3196421 : Blo 630300 3196421 := bbase (se 4 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 3196421 = 599329) (by norm_num)
theorem B1426949 : Blo 630300 1426949 := bbase (se 4 (by rfl) ⟨133776, by rfl⟩ : syracuseStep 1426949 = 267553) (by norm_num)
theorem B673357 : Blo 630300 673357 := bbase (se 3 (by rfl) ⟨126254, by rfl⟩ : syracuseStep 673357 = 252509) (by norm_num)
theorem B1427021 : Blo 630300 1427021 := bbase (se 3 (by rfl) ⟨267566, by rfl⟩ : syracuseStep 1427021 = 535133) (by norm_num)
theorem B4802165 : Blo 630300 4802165 := bbase (se 5 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 4802165 = 450203) (by norm_num)
theorem B1066621 : Blo 630300 1066621 := bbase (se 3 (by rfl) ⟨199991, by rfl⟩ : syracuseStep 1066621 = 399983) (by norm_num)
theorem B1427093 : Blo 630300 1427093 := bbase (se 6 (by rfl) ⟨33447, by rfl⟩ : syracuseStep 1427093 = 66895) (by norm_num)
theorem B902821 : Blo 630300 902821 := bbase (se 4 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 902821 = 169279) (by norm_num)
theorem B1066709 : Blo 630300 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B1427165 : Blo 630300 1427165 := bbase (se 3 (by rfl) ⟨267593, by rfl⟩ : syracuseStep 1427165 = 535187) (by norm_num)
theorem B1066837 : Blo 630300 1066837 := bbase (se 9 (by rfl) ⟨3125, by rfl⟩ : syracuseStep 1066837 = 6251) (by norm_num)
theorem B1066925 : Blo 630300 1066925 := bbase (se 3 (by rfl) ⟨200048, by rfl⟩ : syracuseStep 1066925 = 400097) (by norm_num)
theorem B1558493 : Blo 630300 1558493 := bbase (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) (by norm_num)
theorem B673801 : Blo 630300 673801 := bbase (se 2 (by rfl) ⟨252675, by rfl⟩ : syracuseStep 673801 = 505351) (by norm_num)
theorem B641053 : Blo 630300 641053 := bbase (se 3 (by rfl) ⟨120197, by rfl⟩ : syracuseStep 641053 = 240395) (by norm_num)
theorem B1067053 : Blo 630300 1067053 := bbase (se 3 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 1067053 = 400145) (by norm_num)
theorem B3655733 : Blo 630300 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B1198165 : Blo 630300 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B2705525 : Blo 630300 2705525 := bbase (se 5 (by rfl) ⟨126821, by rfl⟩ : syracuseStep 2705525 = 253643) (by norm_num)
theorem B673921 : Blo 630300 673921 := bbase (se 2 (by rfl) ⟨252720, by rfl⟩ : syracuseStep 673921 = 505441) (by norm_num)
theorem B1067141 : Blo 630300 1067141 := bbase (se 4 (by rfl) ⟨100044, by rfl⟩ : syracuseStep 1067141 = 200089) (by norm_num)
theorem B1460405 : Blo 630300 1460405 := bbase (se 5 (by rfl) ⟨68456, by rfl⟩ : syracuseStep 1460405 = 136913) (by norm_num)
theorem B1198309 : Blo 630300 1198309 := bbase (se 4 (by rfl) ⟨112341, by rfl⟩ : syracuseStep 1198309 = 224683) (by norm_num)
theorem B1067269 : Blo 630300 1067269 := bbase (se 4 (by rfl) ⟨100056, by rfl⟩ : syracuseStep 1067269 = 200113) (by norm_num)
theorem B1067357 : Blo 630300 1067357 := bbase (se 3 (by rfl) ⟨200129, by rfl⟩ : syracuseStep 1067357 = 400259) (by norm_num)
theorem B1296749 : Blo 630300 1296749 := bbase (se 3 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 1296749 = 486281) (by norm_num)
theorem B674173 : Blo 630300 674173 := bbase (se 3 (by rfl) ⟨126407, by rfl⟩ : syracuseStep 674173 = 252815) (by norm_num)
theorem B674177 : Blo 630300 674177 := bbase (se 2 (by rfl) ⟨252816, by rfl⟩ : syracuseStep 674177 = 505633) (by norm_num)
theorem B1198469 : Blo 630300 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B2279845 : Blo 630300 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B1067485 : Blo 630300 1067485 := bbase (se 3 (by rfl) ⟨200153, by rfl⟩ : syracuseStep 1067485 = 400307) (by norm_num)
theorem B1198613 : Blo 630300 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B1067573 : Blo 630300 1067573 := bbase (se 5 (by rfl) ⟨50042, by rfl⟩ : syracuseStep 1067573 = 100085) (by norm_num)
theorem B1624637 : Blo 630300 1624637 := bbase (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) (by norm_num)
theorem B1067701 : Blo 630300 1067701 := bbase (se 5 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 1067701 = 100097) (by norm_num)
theorem B1067789 : Blo 630300 1067789 := bbase (se 3 (by rfl) ⟨200210, by rfl⟩ : syracuseStep 1067789 = 400421) (by norm_num)
theorem B3197717 : Blo 630300 3197717 := bbase (se 6 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 3197717 = 149893) (by norm_num)
theorem B1198901 : Blo 630300 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B1067917 : Blo 630300 1067917 := bbase (se 3 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 1067917 = 400469) (by norm_num)
theorem B674741 : Blo 630300 674741 := bbase (se 5 (by rfl) ⟨31628, by rfl⟩ : syracuseStep 674741 = 63257) (by norm_num)
theorem B1199053 : Blo 630300 1199053 := bbase (se 3 (by rfl) ⟨224822, by rfl⟩ : syracuseStep 1199053 = 449645) (by norm_num)
theorem B1068005 : Blo 630300 1068005 := bbase (se 4 (by rfl) ⟨100125, by rfl⟩ : syracuseStep 1068005 = 200251) (by norm_num)
theorem B1068133 : Blo 630300 1068133 := bbase (se 4 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 1068133 = 200275) (by norm_num)
theorem B674929 : Blo 630300 674929 := bbase (se 2 (by rfl) ⟨253098, by rfl⟩ : syracuseStep 674929 = 506197) (by norm_num)
theorem B1068221 : Blo 630300 1068221 := bbase (se 3 (by rfl) ⟨200291, by rfl⟩ : syracuseStep 1068221 = 400583) (by norm_num)
theorem B1199357 : Blo 630300 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B2280757 : Blo 630300 2280757 := bbase (se 5 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 2280757 = 213821) (by norm_num)
theorem B1068349 : Blo 630300 1068349 := bbase (se 3 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 1068349 = 400631) (by norm_num)
theorem B1625437 : Blo 630300 1625437 := bbase (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) (by norm_num)
theorem B1068437 : Blo 630300 1068437 := bbase (se 6 (by rfl) ⟨25041, by rfl⟩ : syracuseStep 1068437 = 50083) (by norm_num)
theorem B642533 : Blo 630300 642533 := bbase (se 4 (by rfl) ⟨60237, by rfl⟩ : syracuseStep 642533 = 120475) (by norm_num)
theorem B1068565 : Blo 630300 1068565 := bbase (se 6 (by rfl) ⟨25044, by rfl⟩ : syracuseStep 1068565 = 50089) (by norm_num)
theorem B1068653 : Blo 630300 1068653 := bbase (se 3 (by rfl) ⟨200372, by rfl⟩ : syracuseStep 1068653 = 400745) (by norm_num)
theorem B1068781 : Blo 630300 1068781 := bbase (se 3 (by rfl) ⟨200396, by rfl⟩ : syracuseStep 1068781 = 400793) (by norm_num)
theorem B1068869 : Blo 630300 1068869 := bbase (se 4 (by rfl) ⟨100206, by rfl⟩ : syracuseStep 1068869 = 200413) (by norm_num)
theorem B675749 : Blo 630300 675749 := bbase (se 4 (by rfl) ⟨63351, by rfl⟩ : syracuseStep 675749 = 126703) (by norm_num)
theorem B1068997 : Blo 630300 1068997 := bbase (se 4 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 1068997 = 200437) (by norm_num)
theorem B1200109 : Blo 630300 1200109 := bbase (se 3 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 1200109 = 450041) (by norm_num)
theorem B1069085 : Blo 630300 1069085 := bbase (se 3 (by rfl) ⟨200453, by rfl⟩ : syracuseStep 1069085 = 400907) (by norm_num)
theorem B3199013 : Blo 630300 3199013 := bbase (se 4 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 3199013 = 599815) (by norm_num)
theorem B1200253 : Blo 630300 1200253 := bbase (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) (by norm_num)
theorem B1069213 : Blo 630300 1069213 := bbase (se 3 (by rfl) ⟨200477, by rfl⟩ : syracuseStep 1069213 = 400955) (by norm_num)
theorem B1069301 : Blo 630300 1069301 := bbase (se 5 (by rfl) ⟨50123, by rfl⟩ : syracuseStep 1069301 = 100247) (by norm_num)
theorem B1200413 : Blo 630300 1200413 := bbase (se 3 (by rfl) ⟨225077, by rfl⟩ : syracuseStep 1200413 = 450155) (by norm_num)
theorem B676193 : Blo 630300 676193 := bbase (se 2 (by rfl) ⟨253572, by rfl⟩ : syracuseStep 676193 = 507145) (by norm_num)
theorem B1069429 : Blo 630300 1069429 := bbase (se 5 (by rfl) ⟨50129, by rfl⟩ : syracuseStep 1069429 = 100259) (by norm_num)
theorem B1200557 : Blo 630300 1200557 := bbase (se 3 (by rfl) ⟨225104, by rfl⟩ : syracuseStep 1200557 = 450209) (by norm_num)
theorem B1069517 : Blo 630300 1069517 := bbase (se 3 (by rfl) ⟨200534, by rfl⟩ : syracuseStep 1069517 = 401069) (by norm_num)
theorem B709105 : Blo 630300 709105 := bbase (se 2 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 709105 = 531829) (by norm_num)
theorem B709141 : Blo 630300 709141 := bbase (se 6 (by rfl) ⟨16620, by rfl⟩ : syracuseStep 709141 = 33241) (by norm_num)
theorem B709177 : Blo 630300 709177 := bbase (se 2 (by rfl) ⟨265941, by rfl⟩ : syracuseStep 709177 = 531883) (by norm_num)
theorem B1069645 : Blo 630300 1069645 := bbase (se 3 (by rfl) ⟨200558, by rfl⟩ : syracuseStep 1069645 = 401117) (by norm_num)
theorem B676441 : Blo 630300 676441 := bbase (se 2 (by rfl) ⟨253665, by rfl⟩ : syracuseStep 676441 = 507331) (by norm_num)
theorem B709213 : Blo 630300 709213 := bbase (se 3 (by rfl) ⟨132977, by rfl⟩ : syracuseStep 709213 = 265955) (by norm_num)
theorem B709249 : Blo 630300 709249 := bbase (se 2 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 709249 = 531937) (by norm_num)
theorem B709285 : Blo 630300 709285 := bbase (se 4 (by rfl) ⟨66495, by rfl⟩ : syracuseStep 709285 = 132991) (by norm_num)
theorem B1069733 : Blo 630300 1069733 := bbase (se 4 (by rfl) ⟨100287, by rfl⟩ : syracuseStep 1069733 = 200575) (by norm_num)
theorem B709321 : Blo 630300 709321 := bbase (se 2 (by rfl) ⟨265995, by rfl⟩ : syracuseStep 709321 = 531991) (by norm_num)
theorem B1200845 : Blo 630300 1200845 := bbase (se 3 (by rfl) ⟨225158, by rfl⟩ : syracuseStep 1200845 = 450317) (by norm_num)
theorem B709357 : Blo 630300 709357 := bbase (se 3 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 709357 = 266009) (by norm_num)
theorem B709393 : Blo 630300 709393 := bbase (se 2 (by rfl) ⟨266022, by rfl⟩ : syracuseStep 709393 = 532045) (by norm_num)
theorem B1069861 : Blo 630300 1069861 := bbase (se 4 (by rfl) ⟨100299, by rfl⟩ : syracuseStep 1069861 = 200599) (by norm_num)
theorem B709429 : Blo 630300 709429 := bbase (se 5 (by rfl) ⟨33254, by rfl⟩ : syracuseStep 709429 = 66509) (by norm_num)
theorem B1299253 : Blo 630300 1299253 := bbase (se 5 (by rfl) ⟨60902, by rfl⟩ : syracuseStep 1299253 = 121805) (by norm_num)
theorem B709465 : Blo 630300 709465 := bbase (se 2 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 709465 = 532099) (by norm_num)
theorem B1200997 : Blo 630300 1200997 := bbase (se 4 (by rfl) ⟨112593, by rfl⟩ : syracuseStep 1200997 = 225187) (by norm_num)
theorem B3855221 : Blo 630300 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B709501 : Blo 630300 709501 := bbase (se 3 (by rfl) ⟨133031, by rfl⟩ : syracuseStep 709501 = 266063) (by norm_num)
theorem B1069949 : Blo 630300 1069949 := bbase (se 3 (by rfl) ⟨200615, by rfl⟩ : syracuseStep 1069949 = 401231) (by norm_num)
theorem B709537 : Blo 630300 709537 := bbase (se 2 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 709537 = 532153) (by norm_num)
theorem B1627069 : Blo 630300 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B709573 : Blo 630300 709573 := bbase (se 4 (by rfl) ⟨66522, by rfl⟩ : syracuseStep 709573 = 133045) (by norm_num)
theorem B709609 : Blo 630300 709609 := bbase (se 2 (by rfl) ⟨266103, by rfl⟩ : syracuseStep 709609 = 532207) (by norm_num)
theorem B1070077 : Blo 630300 1070077 := bbase (se 3 (by rfl) ⟨200639, by rfl⟩ : syracuseStep 1070077 = 401279) (by norm_num)
theorem B676873 : Blo 630300 676873 := bbase (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) (by norm_num)
theorem B709645 : Blo 630300 709645 := bbase (se 3 (by rfl) ⟨133058, by rfl⟩ : syracuseStep 709645 = 266117) (by norm_num)
theorem B709681 : Blo 630300 709681 := bbase (se 2 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 709681 = 532261) (by norm_num)
theorem B676945 : Blo 630300 676945 := bbase (se 2 (by rfl) ⟨253854, by rfl⟩ : syracuseStep 676945 = 507709) (by norm_num)
theorem B709717 : Blo 630300 709717 := bbase (se 8 (by rfl) ⟨4158, by rfl⟩ : syracuseStep 709717 = 8317) (by norm_num)
theorem B1070165 : Blo 630300 1070165 := bbase (se 8 (by rfl) ⟨6270, by rfl⟩ : syracuseStep 1070165 = 12541) (by norm_num)
theorem B1922149 : Blo 630300 1922149 := bbase (se 4 (by rfl) ⟨180201, by rfl⟩ : syracuseStep 1922149 = 360403) (by norm_num)
theorem B709753 : Blo 630300 709753 := bbase (se 2 (by rfl) ⟨266157, by rfl⟩ : syracuseStep 709753 = 532315) (by norm_num)
theorem B1201301 : Blo 630300 1201301 := bbase (se 6 (by rfl) ⟨28155, by rfl⟩ : syracuseStep 1201301 = 56311) (by norm_num)
theorem B709789 : Blo 630300 709789 := bbase (se 3 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 709789 = 266171) (by norm_num)
theorem B709825 : Blo 630300 709825 := bbase (se 2 (by rfl) ⟨266184, by rfl⟩ : syracuseStep 709825 = 532369) (by norm_num)
theorem B1135829 : Blo 630300 1135829 := bbase (se 7 (by rfl) ⟨13310, by rfl⟩ : syracuseStep 1135829 = 26621) (by norm_num)
theorem B1070293 : Blo 630300 1070293 := bbase (se 7 (by rfl) ⟨12542, by rfl⟩ : syracuseStep 1070293 = 25085) (by norm_num)
theorem B709861 : Blo 630300 709861 := bbase (se 4 (by rfl) ⟨66549, by rfl⟩ : syracuseStep 709861 = 133099) (by norm_num)
theorem B1365245 : Blo 630300 1365245 := bbase (se 3 (by rfl) ⟨255983, by rfl⟩ : syracuseStep 1365245 = 511967) (by norm_num)
theorem B709897 : Blo 630300 709897 := bbase (se 2 (by rfl) ⟨266211, by rfl⟩ : syracuseStep 709897 = 532423) (by norm_num)
theorem B709933 : Blo 630300 709933 := bbase (se 3 (by rfl) ⟨133112, by rfl⟩ : syracuseStep 709933 = 266225) (by norm_num)
theorem B1070381 : Blo 630300 1070381 := bbase (se 3 (by rfl) ⟨200696, by rfl⟩ : syracuseStep 1070381 = 401393) (by norm_num)
theorem B3200309 : Blo 630300 3200309 := bbase (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) (by norm_num)
theorem B709969 : Blo 630300 709969 := bbase (se 2 (by rfl) ⟨266238, by rfl⟩ : syracuseStep 709969 = 532477) (by norm_num)
theorem B710005 : Blo 630300 710005 := bbase (se 5 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 710005 = 66563) (by norm_num)
theorem B710041 : Blo 630300 710041 := bbase (se 2 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 710041 = 532531) (by norm_num)
theorem B1136053 : Blo 630300 1136053 := bbase (se 5 (by rfl) ⟨53252, by rfl⟩ : syracuseStep 1136053 = 106505) (by norm_num)
theorem B710077 : Blo 630300 710077 := bbase (se 3 (by rfl) ⟨133139, by rfl⟩ : syracuseStep 710077 = 266279) (by norm_num)
theorem B677317 : Blo 630300 677317 := bbase (se 4 (by rfl) ⟨63498, by rfl⟩ : syracuseStep 677317 = 126997) (by norm_num)
theorem B710113 : Blo 630300 710113 := bbase (se 2 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 710113 = 532585) (by norm_num)
theorem B1136117 : Blo 630300 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B710149 : Blo 630300 710149 := bbase (se 4 (by rfl) ⟨66576, by rfl⟩ : syracuseStep 710149 = 133153) (by norm_num)
theorem B710185 : Blo 630300 710185 := bbase (se 2 (by rfl) ⟨266319, by rfl⟩ : syracuseStep 710185 = 532639) (by norm_num)
theorem B710221 : Blo 630300 710221 := bbase (se 3 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 710221 = 266333) (by norm_num)
theorem B710257 : Blo 630300 710257 := bbase (se 2 (by rfl) ⟨266346, by rfl⟩ : syracuseStep 710257 = 532693) (by norm_num)
theorem B710293 : Blo 630300 710293 := bbase (se 6 (by rfl) ⟨16647, by rfl⟩ : syracuseStep 710293 = 33295) (by norm_num)
theorem B1562285 : Blo 630300 1562285 := bbase (se 3 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 1562285 = 585857) (by norm_num)
theorem B710329 : Blo 630300 710329 := bbase (se 2 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 710329 = 532747) (by norm_num)
theorem B2741957 : Blo 630300 2741957 := bbase (se 4 (by rfl) ⟨257058, by rfl⟩ : syracuseStep 2741957 = 514117) (by norm_num)
theorem B2283221 : Blo 630300 2283221 := bbase (se 7 (by rfl) ⟨26756, by rfl⟩ : syracuseStep 2283221 = 53513) (by norm_num)
theorem B710365 : Blo 630300 710365 := bbase (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) (by norm_num)
theorem B710401 : Blo 630300 710401 := bbase (se 2 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 710401 = 532801) (by norm_num)
theorem B710437 : Blo 630300 710437 := bbase (se 4 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 710437 = 133207) (by norm_num)
theorem B710473 : Blo 630300 710473 := bbase (se 2 (by rfl) ⟨266427, by rfl⟩ : syracuseStep 710473 = 532855) (by norm_num)
theorem B2283365 : Blo 630300 2283365 := bbase (se 4 (by rfl) ⟨214065, by rfl⟩ : syracuseStep 2283365 = 428131) (by norm_num)
theorem B710509 : Blo 630300 710509 := bbase (se 3 (by rfl) ⟨133220, by rfl⟩ : syracuseStep 710509 = 266441) (by norm_num)
theorem B1202053 : Blo 630300 1202053 := bbase (se 4 (by rfl) ⟨112692, by rfl⟩ : syracuseStep 1202053 = 225385) (by norm_num)
theorem B710545 : Blo 630300 710545 := bbase (se 2 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 710545 = 532909) (by norm_num)
theorem B710581 : Blo 630300 710581 := bbase (se 5 (by rfl) ⟨33308, by rfl⟩ : syracuseStep 710581 = 66617) (by norm_num)
theorem B2742229 : Blo 630300 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B710617 : Blo 630300 710617 := bbase (se 2 (by rfl) ⟨266481, by rfl⟩ : syracuseStep 710617 = 532963) (by norm_num)
theorem B710653 : Blo 630300 710653 := bbase (se 3 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 710653 = 266495) (by norm_num)
theorem B1202197 : Blo 630300 1202197 := bbase (se 6 (by rfl) ⟨28176, by rfl⟩ : syracuseStep 1202197 = 56353) (by norm_num)
theorem B710689 : Blo 630300 710689 := bbase (se 2 (by rfl) ⟨266508, by rfl⟩ : syracuseStep 710689 = 533017) (by norm_num)
theorem B710725 : Blo 630300 710725 := bbase (se 4 (by rfl) ⟨66630, by rfl⟩ : syracuseStep 710725 = 133261) (by norm_num)
theorem B1595477 : Blo 630300 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710761 : Blo 630300 710761 := bbase (se 2 (by rfl) ⟨266535, by rfl⟩ : syracuseStep 710761 = 533071) (by norm_num)
theorem B2283653 : Blo 630300 2283653 := bbase (se 4 (by rfl) ⟨214092, by rfl⟩ : syracuseStep 2283653 = 428185) (by norm_num)
theorem B710797 : Blo 630300 710797 := bbase (se 3 (by rfl) ⟨133274, by rfl⟩ : syracuseStep 710797 = 266549) (by norm_num)
theorem B3037333 : Blo 630300 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B710833 : Blo 630300 710833 := bbase (se 2 (by rfl) ⟨266562, by rfl⟩ : syracuseStep 710833 = 533125) (by norm_num)
theorem B1202357 : Blo 630300 1202357 := bbase (se 5 (by rfl) ⟨56360, by rfl⟩ : syracuseStep 1202357 = 112721) (by norm_num)
theorem B710869 : Blo 630300 710869 := bbase (se 7 (by rfl) ⟨8330, by rfl⟩ : syracuseStep 710869 = 16661) (by norm_num)
theorem B710905 : Blo 630300 710905 := bbase (se 2 (by rfl) ⟨266589, by rfl⟩ : syracuseStep 710905 = 533179) (by norm_num)
theorem B710941 : Blo 630300 710941 := bbase (se 3 (by rfl) ⟨133301, by rfl⟩ : syracuseStep 710941 = 266603) (by norm_num)
theorem B710977 : Blo 630300 710977 := bbase (se 2 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 710977 = 533233) (by norm_num)
theorem B1202501 : Blo 630300 1202501 := bbase (se 4 (by rfl) ⟨112734, by rfl⟩ : syracuseStep 1202501 = 225469) (by norm_num)
theorem B711013 : Blo 630300 711013 := bbase (se 4 (by rfl) ⟨66657, by rfl⟩ : syracuseStep 711013 = 133315) (by norm_num)
theorem B2677093 : Blo 630300 2677093 := bbase (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) (by norm_num)
theorem B711049 : Blo 630300 711049 := bbase (se 2 (by rfl) ⟨266643, by rfl⟩ : syracuseStep 711049 = 533287) (by norm_num)
theorem B1595821 : Blo 630300 1595821 := bbase (se 3 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 1595821 = 598433) (by norm_num)
theorem B711085 : Blo 630300 711085 := bbase (se 3 (by rfl) ⟨133328, by rfl⟩ : syracuseStep 711085 = 266657) (by norm_num)
theorem B711121 : Blo 630300 711121 := bbase (se 2 (by rfl) ⟨266670, by rfl⟩ : syracuseStep 711121 = 533341) (by norm_num)
theorem B711157 : Blo 630300 711157 := bbase (se 5 (by rfl) ⟨33335, by rfl⟩ : syracuseStep 711157 = 66671) (by norm_num)
theorem B711193 : Blo 630300 711193 := bbase (se 2 (by rfl) ⟨266697, by rfl⟩ : syracuseStep 711193 = 533395) (by norm_num)
theorem B1595933 : Blo 630300 1595933 := bbase (se 3 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 1595933 = 598475) (by norm_num)
theorem B711229 : Blo 630300 711229 := bbase (se 3 (by rfl) ⟨133355, by rfl⟩ : syracuseStep 711229 = 266711) (by norm_num)
theorem B2808389 : Blo 630300 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B3201605 : Blo 630300 3201605 := bbase (se 4 (by rfl) ⟨300150, by rfl⟩ : syracuseStep 3201605 = 600301) (by norm_num)
theorem B6085205 : Blo 630300 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B711265 : Blo 630300 711265 := bbase (se 2 (by rfl) ⟨266724, by rfl⟩ : syracuseStep 711265 = 533449) (by norm_num)
theorem B1202789 : Blo 630300 1202789 := bbase (se 4 (by rfl) ⟨112761, by rfl⟩ : syracuseStep 1202789 = 225523) (by norm_num)
theorem B711301 : Blo 630300 711301 := bbase (se 4 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 711301 = 133369) (by norm_num)
theorem B711337 : Blo 630300 711337 := bbase (se 2 (by rfl) ⟨266751, by rfl⟩ : syracuseStep 711337 = 533503) (by norm_num)
theorem B711373 : Blo 630300 711373 := bbase (se 3 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 711373 = 266765) (by norm_num)
theorem B1596125 : Blo 630300 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B711409 : Blo 630300 711409 := bbase (se 2 (by rfl) ⟨266778, by rfl⟩ : syracuseStep 711409 = 533557) (by norm_num)
theorem B1202941 : Blo 630300 1202941 := bbase (se 3 (by rfl) ⟨225551, by rfl⟩ : syracuseStep 1202941 = 451103) (by norm_num)
theorem B711445 : Blo 630300 711445 := bbase (se 6 (by rfl) ⟨16674, by rfl⟩ : syracuseStep 711445 = 33349) (by norm_num)
theorem B711481 : Blo 630300 711481 := bbase (se 2 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 711481 = 533611) (by norm_num)
theorem B711517 : Blo 630300 711517 := bbase (se 3 (by rfl) ⟨133409, by rfl⟩ : syracuseStep 711517 = 266819) (by norm_num)
theorem B711553 : Blo 630300 711553 := bbase (se 2 (by rfl) ⟨266832, by rfl⟩ : syracuseStep 711553 = 533665) (by norm_num)
theorem B711589 : Blo 630300 711589 := bbase (se 4 (by rfl) ⟨66711, by rfl⟩ : syracuseStep 711589 = 133423) (by norm_num)
theorem B711625 : Blo 630300 711625 := bbase (se 2 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 711625 = 533719) (by norm_num)
theorem B711661 : Blo 630300 711661 := bbase (se 3 (by rfl) ⟨133436, by rfl⟩ : syracuseStep 711661 = 266873) (by norm_num)
theorem B711697 : Blo 630300 711697 := bbase (se 2 (by rfl) ⟨266886, by rfl⟩ : syracuseStep 711697 = 533773) (by norm_num)
theorem B1203245 : Blo 630300 1203245 := bbase (se 3 (by rfl) ⟨225608, by rfl⟩ : syracuseStep 1203245 = 451217) (by norm_num)
theorem B1596469 : Blo 630300 1596469 := bbase (se 5 (by rfl) ⟨74834, by rfl⟩ : syracuseStep 1596469 = 149669) (by norm_num)
theorem B711733 : Blo 630300 711733 := bbase (se 5 (by rfl) ⟨33362, by rfl⟩ : syracuseStep 711733 = 66725) (by norm_num)
theorem B711769 : Blo 630300 711769 := bbase (se 2 (by rfl) ⟨266913, by rfl⟩ : syracuseStep 711769 = 533827) (by norm_num)
theorem B711805 : Blo 630300 711805 := bbase (se 3 (by rfl) ⟨133463, by rfl⟩ : syracuseStep 711805 = 266927) (by norm_num)
theorem B711841 : Blo 630300 711841 := bbase (se 2 (by rfl) ⟨266940, by rfl⟩ : syracuseStep 711841 = 533881) (by norm_num)
theorem B1596581 : Blo 630300 1596581 := bbase (se 4 (by rfl) ⟨149679, by rfl⟩ : syracuseStep 1596581 = 299359) (by norm_num)
theorem B711877 : Blo 630300 711877 := bbase (se 4 (by rfl) ⟨66738, by rfl⟩ : syracuseStep 711877 = 133477) (by norm_num)
theorem B711913 : Blo 630300 711913 := bbase (se 2 (by rfl) ⟨266967, by rfl⟩ : syracuseStep 711913 = 533935) (by norm_num)
theorem B711949 : Blo 630300 711949 := bbase (se 3 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 711949 = 266981) (by norm_num)
theorem B711985 : Blo 630300 711985 := bbase (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) (by norm_num)
theorem B2022725 : Blo 630300 2022725 := bbase (se 4 (by rfl) ⟨189630, by rfl⟩ : syracuseStep 2022725 = 379261) (by norm_num)
theorem B712021 : Blo 630300 712021 := bbase (se 11 (by rfl) ⟨521, by rfl⟩ : syracuseStep 712021 = 1043) (by norm_num)
theorem B1596773 : Blo 630300 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B712057 : Blo 630300 712057 := bbase (se 2 (by rfl) ⟨267021, by rfl⟩ : syracuseStep 712057 = 534043) (by norm_num)
theorem B712093 : Blo 630300 712093 := bbase (se 3 (by rfl) ⟨133517, by rfl⟩ : syracuseStep 712093 = 267035) (by norm_num)
theorem B1236397 : Blo 630300 1236397 := bbase (se 3 (by rfl) ⟨231824, by rfl⟩ : syracuseStep 1236397 = 463649) (by norm_num)
theorem B712129 : Blo 630300 712129 := bbase (se 2 (by rfl) ⟨267048, by rfl⟩ : syracuseStep 712129 = 534097) (by norm_num)
theorem B712165 : Blo 630300 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B712201 : Blo 630300 712201 := bbase (se 2 (by rfl) ⟨267075, by rfl⟩ : syracuseStep 712201 = 534151) (by norm_num)
theorem B712237 : Blo 630300 712237 := bbase (se 3 (by rfl) ⟨133544, by rfl⟩ : syracuseStep 712237 = 267089) (by norm_num)
theorem B712273 : Blo 630300 712273 := bbase (se 2 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 712273 = 534205) (by norm_num)
theorem B20012629 : Blo 630300 20012629 := bbase (se 8 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 20012629 = 234523) (by norm_num)
theorem B712309 : Blo 630300 712309 := bbase (se 5 (by rfl) ⟨33389, by rfl⟩ : syracuseStep 712309 = 66779) (by norm_num)
theorem B712345 : Blo 630300 712345 := bbase (se 2 (by rfl) ⟨267129, by rfl⟩ : syracuseStep 712345 = 534259) (by norm_num)
theorem B1597117 : Blo 630300 1597117 := bbase (se 3 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 1597117 = 598919) (by norm_num)
theorem B712381 : Blo 630300 712381 := bbase (se 3 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 712381 = 267143) (by norm_num)
theorem B712417 : Blo 630300 712417 := bbase (se 2 (by rfl) ⟨267156, by rfl⟩ : syracuseStep 712417 = 534313) (by norm_num)
theorem B1236709 : Blo 630300 1236709 := bbase (se 4 (by rfl) ⟨115941, by rfl⟩ : syracuseStep 1236709 = 231883) (by norm_num)
theorem B3596021 : Blo 630300 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B712453 : Blo 630300 712453 := bbase (se 4 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 712453 = 133585) (by norm_num)
theorem B1924885 : Blo 630300 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B1203997 : Blo 630300 1203997 := bbase (se 3 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 1203997 = 451499) (by norm_num)
theorem B712489 : Blo 630300 712489 := bbase (se 2 (by rfl) ⟨267183, by rfl⟩ : syracuseStep 712489 = 534367) (by norm_num)
theorem B1597229 : Blo 630300 1597229 := bbase (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) (by norm_num)
theorem B2285381 : Blo 630300 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B712525 : Blo 630300 712525 := bbase (se 3 (by rfl) ⟨133598, by rfl⟩ : syracuseStep 712525 = 267197) (by norm_num)
theorem B3202901 : Blo 630300 3202901 := bbase (se 9 (by rfl) ⟨9383, by rfl⟩ : syracuseStep 3202901 = 18767) (by norm_num)
theorem B712561 : Blo 630300 712561 := bbase (se 2 (by rfl) ⟨267210, by rfl⟩ : syracuseStep 712561 = 534421) (by norm_num)
theorem B712597 : Blo 630300 712597 := bbase (se 6 (by rfl) ⟨16701, by rfl⟩ : syracuseStep 712597 = 33403) (by norm_num)
theorem B1204141 : Blo 630300 1204141 := bbase (se 3 (by rfl) ⟨225776, by rfl⟩ : syracuseStep 1204141 = 451553) (by norm_num)
theorem B712633 : Blo 630300 712633 := bbase (se 2 (by rfl) ⟨267237, by rfl⟩ : syracuseStep 712633 = 534475) (by norm_num)
theorem B712669 : Blo 630300 712669 := bbase (se 3 (by rfl) ⟨133625, by rfl⟩ : syracuseStep 712669 = 267251) (by norm_num)
theorem B1597421 : Blo 630300 1597421 := bbase (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) (by norm_num)
theorem B712705 : Blo 630300 712705 := bbase (se 2 (by rfl) ⟨267264, by rfl⟩ : syracuseStep 712705 = 534529) (by norm_num)
theorem B1204229 : Blo 630300 1204229 := bbase (se 4 (by rfl) ⟨112896, by rfl⟩ : syracuseStep 1204229 = 225793) (by norm_num)
theorem B712741 : Blo 630300 712741 := bbase (se 4 (by rfl) ⟨66819, by rfl⟩ : syracuseStep 712741 = 133639) (by norm_num)
theorem B712777 : Blo 630300 712777 := bbase (se 2 (by rfl) ⟨267291, by rfl⟩ : syracuseStep 712777 = 534583) (by norm_num)
theorem B712813 : Blo 630300 712813 := bbase (se 3 (by rfl) ⟨133652, by rfl⟩ : syracuseStep 712813 = 267305) (by norm_num)
theorem B712849 : Blo 630300 712849 := bbase (se 2 (by rfl) ⟨267318, by rfl⟩ : syracuseStep 712849 = 534637) (by norm_num)
theorem B712885 : Blo 630300 712885 := bbase (se 5 (by rfl) ⟨33416, by rfl⟩ : syracuseStep 712885 = 66833) (by norm_num)
theorem B712921 : Blo 630300 712921 := bbase (se 2 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 712921 = 534691) (by norm_num)
theorem B712957 : Blo 630300 712957 := bbase (se 3 (by rfl) ⟨133679, by rfl⟩ : syracuseStep 712957 = 267359) (by norm_num)
theorem B712993 : Blo 630300 712993 := bbase (se 2 (by rfl) ⟨267372, by rfl⟩ : syracuseStep 712993 = 534745) (by norm_num)
theorem B1597765 : Blo 630300 1597765 := bbase (se 4 (by rfl) ⟨149790, by rfl⟩ : syracuseStep 1597765 = 299581) (by norm_num)
theorem B713029 : Blo 630300 713029 := bbase (se 4 (by rfl) ⟨66846, by rfl⟩ : syracuseStep 713029 = 133693) (by norm_num)
theorem B713065 : Blo 630300 713065 := bbase (se 2 (by rfl) ⟨267399, by rfl⟩ : syracuseStep 713065 = 534799) (by norm_num)
theorem B713101 : Blo 630300 713101 := bbase (se 3 (by rfl) ⟨133706, by rfl⟩ : syracuseStep 713101 = 267413) (by norm_num)
theorem B713137 : Blo 630300 713137 := bbase (se 2 (by rfl) ⟨267426, by rfl⟩ : syracuseStep 713137 = 534853) (by norm_num)
theorem B1597877 : Blo 630300 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B1171925 : Blo 630300 1171925 := bbase (se 7 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 1171925 = 27467) (by norm_num)
theorem B713173 : Blo 630300 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B713209 : Blo 630300 713209 := bbase (se 2 (by rfl) ⟨267453, by rfl⟩ : syracuseStep 713209 = 534907) (by norm_num)
theorem B713245 : Blo 630300 713245 := bbase (se 3 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 713245 = 267467) (by norm_num)
theorem B713281 : Blo 630300 713281 := bbase (se 2 (by rfl) ⟨267480, by rfl⟩ : syracuseStep 713281 = 534961) (by norm_num)
theorem B713317 : Blo 630300 713317 := bbase (se 4 (by rfl) ⟨66873, by rfl⟩ : syracuseStep 713317 = 133747) (by norm_num)
theorem B1598069 : Blo 630300 1598069 := bbase (se 5 (by rfl) ⟨74909, by rfl⟩ : syracuseStep 1598069 = 149819) (by norm_num)
theorem B713353 : Blo 630300 713353 := bbase (se 2 (by rfl) ⟨267507, by rfl⟩ : syracuseStep 713353 = 535015) (by norm_num)
theorem B811661 : Blo 630300 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B713389 : Blo 630300 713389 := bbase (se 3 (by rfl) ⟨133760, by rfl⟩ : syracuseStep 713389 = 267521) (by norm_num)
theorem B713425 : Blo 630300 713425 := bbase (se 2 (by rfl) ⟨267534, by rfl⟩ : syracuseStep 713425 = 535069) (by norm_num)
theorem B8086229 : Blo 630300 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B713461 : Blo 630300 713461 := bbase (se 5 (by rfl) ⟨33443, by rfl⟩ : syracuseStep 713461 = 66887) (by norm_num)
theorem B713497 : Blo 630300 713497 := bbase (se 2 (by rfl) ⟨267561, by rfl⟩ : syracuseStep 713497 = 535123) (by norm_num)
theorem B713533 : Blo 630300 713533 := bbase (se 3 (by rfl) ⟨133787, by rfl⟩ : syracuseStep 713533 = 267575) (by norm_num)
theorem B713569 : Blo 630300 713569 := bbase (se 2 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 713569 = 535177) (by norm_num)
theorem B1139629 : Blo 630300 1139629 := bbase (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) (by norm_num)
theorem B1598413 : Blo 630300 1598413 := bbase (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) (by norm_num)
theorem B1795061 : Blo 630300 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B1598525 : Blo 630300 1598525 := bbase (se 3 (by rfl) ⟨299723, by rfl⟩ : syracuseStep 1598525 = 599447) (by norm_num)
theorem B3204197 : Blo 630300 3204197 := bbase (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) (by norm_num)
theorem B910453 : Blo 630300 910453 := bbase (se 5 (by rfl) ⟨42677, by rfl⟩ : syracuseStep 910453 = 85355) (by norm_num)
theorem B1139837 : Blo 630300 1139837 := bbase (se 3 (by rfl) ⟨213719, by rfl⟩ : syracuseStep 1139837 = 427439) (by norm_num)
theorem B4809941 : Blo 630300 4809941 := bbase (se 7 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 4809941 = 112733) (by norm_num)
theorem B1598717 : Blo 630300 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B1041677 : Blo 630300 1041677 := bbase (se 3 (by rfl) ⟨195314, by rfl⟩ : syracuseStep 1041677 = 390629) (by norm_num)
theorem B1599061 : Blo 630300 1599061 := bbase (se 8 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 1599061 = 18739) (by norm_num)
theorem B1795733 : Blo 630300 1795733 := bbase (se 6 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 1795733 = 84175) (by norm_num)
theorem B1926821 : Blo 630300 1926821 := bbase (se 4 (by rfl) ⟨180639, by rfl⟩ : syracuseStep 1926821 = 361279) (by norm_num)
theorem B1599173 : Blo 630300 1599173 := bbase (se 4 (by rfl) ⟨149922, by rfl⟩ : syracuseStep 1599173 = 299845) (by norm_num)
theorem B812837 : Blo 630300 812837 := bbase (se 4 (by rfl) ⟨76203, by rfl⟩ : syracuseStep 812837 = 152407) (by norm_num)
theorem B1828709 : Blo 630300 1828709 := bbase (se 4 (by rfl) ⟨171441, by rfl⟩ : syracuseStep 1828709 = 342883) (by norm_num)
theorem B1599365 : Blo 630300 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B3041333 : Blo 630300 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B1796165 : Blo 630300 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1009741 : Blo 630300 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B2025557 : Blo 630300 2025557 := bbase (se 8 (by rfl) ⟨11868, by rfl⟩ : syracuseStep 2025557 = 23737) (by norm_num)
theorem B1599709 : Blo 630300 1599709 := bbase (se 3 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 1599709 = 599891) (by norm_num)
theorem B813289 : Blo 630300 813289 := bbase (se 2 (by rfl) ⟨304983, by rfl⟩ : syracuseStep 813289 = 609967) (by norm_num)
theorem B3041525 : Blo 630300 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B1599821 : Blo 630300 1599821 := bbase (se 3 (by rfl) ⟨299966, by rfl⟩ : syracuseStep 1599821 = 599933) (by norm_num)
theorem B3205493 : Blo 630300 3205493 := bbase (se 5 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 3205493 = 300515) (by norm_num)
theorem B1010189 : Blo 630300 1010189 := bbase (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) (by norm_num)
theorem B1600013 : Blo 630300 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1010389 : Blo 630300 1010389 := bbase (se 7 (by rfl) ⟨11840, by rfl⟩ : syracuseStep 1010389 = 23681) (by norm_num)
theorem B4057877 : Blo 630300 4057877 := bbase (se 6 (by rfl) ⟨95106, by rfl⟩ : syracuseStep 4057877 = 190213) (by norm_num)
theorem B1796917 : Blo 630300 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B1141589 : Blo 630300 1141589 := bbase (se 9 (by rfl) ⟨3344, by rfl⟩ : syracuseStep 1141589 = 6689) (by norm_num)
theorem B1600357 : Blo 630300 1600357 := bbase (se 4 (by rfl) ⟨150033, by rfl⟩ : syracuseStep 1600357 = 300067) (by norm_num)
theorem B1010645 : Blo 630300 1010645 := bbase (se 7 (by rfl) ⟨11843, by rfl⟩ : syracuseStep 1010645 = 23687) (by norm_num)
theorem B1600469 : Blo 630300 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B2026453 : Blo 630300 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B1600661 : Blo 630300 1600661 := bbase (se 6 (by rfl) ⟨37515, by rfl⟩ : syracuseStep 1600661 = 75031) (by norm_num)
theorem B683177 : Blo 630300 683177 := bbase (se 2 (by rfl) ⟨256191, by rfl⟩ : syracuseStep 683177 = 512383) (by norm_num)
theorem B945461 : Blo 630300 945461 := bbase (se 5 (by rfl) ⟨44318, by rfl⟩ : syracuseStep 945461 = 88637) (by norm_num)
theorem B945485 : Blo 630300 945485 := bbase (se 3 (by rfl) ⟨177278, by rfl⟩ : syracuseStep 945485 = 354557) (by norm_num)
theorem B945509 : Blo 630300 945509 := bbase (se 4 (by rfl) ⟨88641, by rfl⟩ : syracuseStep 945509 = 177283) (by norm_num)
theorem B945533 : Blo 630300 945533 := bbase (se 3 (by rfl) ⟨177287, by rfl⟩ : syracuseStep 945533 = 354575) (by norm_num)
theorem B945557 : Blo 630300 945557 := bbase (se 6 (by rfl) ⟨22161, by rfl⟩ : syracuseStep 945557 = 44323) (by norm_num)
theorem B945581 : Blo 630300 945581 := bbase (se 3 (by rfl) ⟨177296, by rfl⟩ : syracuseStep 945581 = 354593) (by norm_num)
theorem B945605 : Blo 630300 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B945629 : Blo 630300 945629 := bbase (se 3 (by rfl) ⟨177305, by rfl⟩ : syracuseStep 945629 = 354611) (by norm_num)
theorem B1601005 : Blo 630300 1601005 := bbase (se 3 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 1601005 = 600377) (by norm_num)
theorem B945653 : Blo 630300 945653 := bbase (se 5 (by rfl) ⟨44327, by rfl⟩ : syracuseStep 945653 = 88655) (by norm_num)
theorem B945677 : Blo 630300 945677 := bbase (se 3 (by rfl) ⟨177314, by rfl⟩ : syracuseStep 945677 = 354629) (by norm_num)
theorem B945701 : Blo 630300 945701 := bbase (se 4 (by rfl) ⟨88659, by rfl⟩ : syracuseStep 945701 = 177319) (by norm_num)
theorem B945725 : Blo 630300 945725 := bbase (se 3 (by rfl) ⟨177323, by rfl⟩ : syracuseStep 945725 = 354647) (by norm_num)
theorem B945749 : Blo 630300 945749 := bbase (se 8 (by rfl) ⟨5541, by rfl⟩ : syracuseStep 945749 = 11083) (by norm_num)
theorem B1601117 : Blo 630300 1601117 := bbase (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) (by norm_num)
theorem B945773 : Blo 630300 945773 := bbase (se 3 (by rfl) ⟨177332, by rfl⟩ : syracuseStep 945773 = 354665) (by norm_num)
theorem B945797 : Blo 630300 945797 := bbase (se 4 (by rfl) ⟨88668, by rfl⟩ : syracuseStep 945797 = 177337) (by norm_num)
theorem B3206789 : Blo 630300 3206789 := bbase (se 4 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 3206789 = 601273) (by norm_num)
theorem B945821 : Blo 630300 945821 := bbase (se 3 (by rfl) ⟨177341, by rfl⟩ : syracuseStep 945821 = 354683) (by norm_num)
theorem B945845 : Blo 630300 945845 := bbase (se 5 (by rfl) ⟨44336, by rfl⟩ : syracuseStep 945845 = 88673) (by norm_num)
theorem B945869 : Blo 630300 945869 := bbase (se 3 (by rfl) ⟨177350, by rfl⟩ : syracuseStep 945869 = 354701) (by norm_num)
theorem B945893 : Blo 630300 945893 := bbase (se 4 (by rfl) ⟨88677, by rfl⟩ : syracuseStep 945893 = 177355) (by norm_num)
theorem B945917 : Blo 630300 945917 := bbase (se 3 (by rfl) ⟨177359, by rfl⟩ : syracuseStep 945917 = 354719) (by norm_num)
theorem B1142533 : Blo 630300 1142533 := bbase (se 4 (by rfl) ⟨107112, by rfl⟩ : syracuseStep 1142533 = 214225) (by norm_num)
theorem B945941 : Blo 630300 945941 := bbase (se 6 (by rfl) ⟨22170, by rfl⟩ : syracuseStep 945941 = 44341) (by norm_num)
theorem B1601309 : Blo 630300 1601309 := bbase (se 3 (by rfl) ⟨300245, by rfl⟩ : syracuseStep 1601309 = 600491) (by norm_num)
theorem B945965 : Blo 630300 945965 := bbase (se 3 (by rfl) ⟨177368, by rfl⟩ : syracuseStep 945965 = 354737) (by norm_num)
theorem B945989 : Blo 630300 945989 := bbase (se 4 (by rfl) ⟨88686, by rfl⟩ : syracuseStep 945989 = 177373) (by norm_num)
theorem B683861 : Blo 630300 683861 := bbase (se 9 (by rfl) ⟨2003, by rfl⟩ : syracuseStep 683861 = 4007) (by norm_num)
theorem B946013 : Blo 630300 946013 := bbase (se 3 (by rfl) ⟨177377, by rfl⟩ : syracuseStep 946013 = 354755) (by norm_num)
theorem B946037 : Blo 630300 946037 := bbase (se 5 (by rfl) ⟨44345, by rfl⟩ : syracuseStep 946037 = 88691) (by norm_num)
theorem B946061 : Blo 630300 946061 := bbase (se 3 (by rfl) ⟨177386, by rfl⟩ : syracuseStep 946061 = 354773) (by norm_num)
theorem B946085 : Blo 630300 946085 := bbase (se 4 (by rfl) ⟨88695, by rfl⟩ : syracuseStep 946085 = 177391) (by norm_num)
theorem B946109 : Blo 630300 946109 := bbase (se 3 (by rfl) ⟨177395, by rfl⟩ : syracuseStep 946109 = 354791) (by norm_num)
theorem B946133 : Blo 630300 946133 := bbase (se 7 (by rfl) ⟨11087, by rfl⟩ : syracuseStep 946133 = 22175) (by norm_num)
theorem B946157 : Blo 630300 946157 := bbase (se 3 (by rfl) ⟨177404, by rfl⟩ : syracuseStep 946157 = 354809) (by norm_num)
theorem B946181 : Blo 630300 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B946205 : Blo 630300 946205 := bbase (se 3 (by rfl) ⟨177413, by rfl⟩ : syracuseStep 946205 = 354827) (by norm_num)
theorem B946229 : Blo 630300 946229 := bbase (se 5 (by rfl) ⟨44354, by rfl⟩ : syracuseStep 946229 = 88709) (by norm_num)
theorem B1011773 : Blo 630300 1011773 := bbase (se 3 (by rfl) ⟨189707, by rfl⟩ : syracuseStep 1011773 = 379415) (by norm_num)
theorem B946253 : Blo 630300 946253 := bbase (se 3 (by rfl) ⟨177422, by rfl⟩ : syracuseStep 946253 = 354845) (by norm_num)
theorem B946277 : Blo 630300 946277 := bbase (se 4 (by rfl) ⟨88713, by rfl⟩ : syracuseStep 946277 = 177427) (by norm_num)
theorem B1601653 : Blo 630300 1601653 := bbase (se 5 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 1601653 = 150155) (by norm_num)
theorem B946301 : Blo 630300 946301 := bbase (se 3 (by rfl) ⟨177431, by rfl⟩ : syracuseStep 946301 = 354863) (by norm_num)
theorem B946325 : Blo 630300 946325 := bbase (se 6 (by rfl) ⟨22179, by rfl⟩ : syracuseStep 946325 = 44359) (by norm_num)
theorem B946349 : Blo 630300 946349 := bbase (se 3 (by rfl) ⟨177440, by rfl⟩ : syracuseStep 946349 = 354881) (by norm_num)
theorem B946373 : Blo 630300 946373 := bbase (se 4 (by rfl) ⟨88722, by rfl⟩ : syracuseStep 946373 = 177445) (by norm_num)
theorem B946397 : Blo 630300 946397 := bbase (se 3 (by rfl) ⟨177449, by rfl⟩ : syracuseStep 946397 = 354899) (by norm_num)
theorem B1601765 : Blo 630300 1601765 := bbase (se 4 (by rfl) ⟨150165, by rfl⟩ : syracuseStep 1601765 = 300331) (by norm_num)
theorem B946421 : Blo 630300 946421 := bbase (se 5 (by rfl) ⟨44363, by rfl⟩ : syracuseStep 946421 = 88727) (by norm_num)
theorem B946445 : Blo 630300 946445 := bbase (se 3 (by rfl) ⟨177458, by rfl⟩ : syracuseStep 946445 = 354917) (by norm_num)
theorem B913685 : Blo 630300 913685 := bbase (se 6 (by rfl) ⟨21414, by rfl⟩ : syracuseStep 913685 = 42829) (by norm_num)
theorem B946469 : Blo 630300 946469 := bbase (se 4 (by rfl) ⟨88731, by rfl⟩ : syracuseStep 946469 = 177463) (by norm_num)
theorem B946493 : Blo 630300 946493 := bbase (se 3 (by rfl) ⟨177467, by rfl⟩ : syracuseStep 946493 = 354935) (by norm_num)
theorem B2879813 : Blo 630300 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B946517 : Blo 630300 946517 := bbase (se 10 (by rfl) ⟨1386, by rfl⟩ : syracuseStep 946517 = 2773) (by norm_num)
theorem B1536349 : Blo 630300 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B946541 : Blo 630300 946541 := bbase (se 3 (by rfl) ⟨177476, by rfl⟩ : syracuseStep 946541 = 354953) (by norm_num)
theorem B946565 : Blo 630300 946565 := bbase (se 4 (by rfl) ⟨88740, by rfl⟩ : syracuseStep 946565 = 177481) (by norm_num)
theorem B1438109 : Blo 630300 1438109 := bbase (se 3 (by rfl) ⟨269645, by rfl⟩ : syracuseStep 1438109 = 539291) (by norm_num)
theorem B946589 : Blo 630300 946589 := bbase (se 3 (by rfl) ⟨177485, by rfl⟩ : syracuseStep 946589 = 354971) (by norm_num)
theorem B1601957 : Blo 630300 1601957 := bbase (se 4 (by rfl) ⟨150183, by rfl⟩ : syracuseStep 1601957 = 300367) (by norm_num)
theorem B946613 : Blo 630300 946613 := bbase (se 5 (by rfl) ⟨44372, by rfl⟩ : syracuseStep 946613 = 88745) (by norm_num)
theorem B946637 : Blo 630300 946637 := bbase (se 3 (by rfl) ⟨177494, by rfl⟩ : syracuseStep 946637 = 354989) (by norm_num)
theorem B946661 : Blo 630300 946661 := bbase (se 4 (by rfl) ⟨88749, by rfl⟩ : syracuseStep 946661 = 177499) (by norm_num)
theorem B946685 : Blo 630300 946685 := bbase (se 3 (by rfl) ⟨177503, by rfl⟩ : syracuseStep 946685 = 355007) (by norm_num)
theorem B946709 : Blo 630300 946709 := bbase (se 6 (by rfl) ⟨22188, by rfl⟩ : syracuseStep 946709 = 44377) (by norm_num)
theorem B946733 : Blo 630300 946733 := bbase (se 3 (by rfl) ⟨177512, by rfl⟩ : syracuseStep 946733 = 355025) (by norm_num)
theorem B1012285 : Blo 630300 1012285 := bbase (se 3 (by rfl) ⟨189803, by rfl⟩ : syracuseStep 1012285 = 379607) (by norm_num)
theorem B946757 : Blo 630300 946757 := bbase (se 4 (by rfl) ⟨88758, by rfl⟩ : syracuseStep 946757 = 177517) (by norm_num)
theorem B946781 : Blo 630300 946781 := bbase (se 3 (by rfl) ⟨177521, by rfl⟩ : syracuseStep 946781 = 355043) (by norm_num)
theorem B946805 : Blo 630300 946805 := bbase (se 5 (by rfl) ⟨44381, by rfl⟩ : syracuseStep 946805 = 88763) (by norm_num)
theorem B946829 : Blo 630300 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B946853 : Blo 630300 946853 := bbase (se 4 (by rfl) ⟨88767, by rfl⟩ : syracuseStep 946853 = 177535) (by norm_num)
theorem B946877 : Blo 630300 946877 := bbase (se 3 (by rfl) ⟨177539, by rfl⟩ : syracuseStep 946877 = 355079) (by norm_num)
theorem B946901 : Blo 630300 946901 := bbase (se 7 (by rfl) ⟨11096, by rfl⟩ : syracuseStep 946901 = 22193) (by norm_num)
theorem B946925 : Blo 630300 946925 := bbase (se 3 (by rfl) ⟨177548, by rfl⟩ : syracuseStep 946925 = 355097) (by norm_num)
theorem B1602301 : Blo 630300 1602301 := bbase (se 3 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 1602301 = 600863) (by norm_num)
theorem B946949 : Blo 630300 946949 := bbase (se 4 (by rfl) ⟨88776, by rfl⟩ : syracuseStep 946949 = 177553) (by norm_num)
theorem B946973 : Blo 630300 946973 := bbase (se 3 (by rfl) ⟨177557, by rfl⟩ : syracuseStep 946973 = 355115) (by norm_num)
theorem B946997 : Blo 630300 946997 := bbase (se 5 (by rfl) ⟨44390, by rfl⟩ : syracuseStep 946997 = 88781) (by norm_num)
theorem B947021 : Blo 630300 947021 := bbase (se 3 (by rfl) ⟨177566, by rfl⟩ : syracuseStep 947021 = 355133) (by norm_num)
theorem B947045 : Blo 630300 947045 := bbase (se 4 (by rfl) ⟨88785, by rfl⟩ : syracuseStep 947045 = 177571) (by norm_num)
theorem B1602413 : Blo 630300 1602413 := bbase (se 3 (by rfl) ⟨300452, by rfl⟩ : syracuseStep 1602413 = 600905) (by norm_num)
theorem B947069 : Blo 630300 947069 := bbase (se 3 (by rfl) ⟨177575, by rfl⟩ : syracuseStep 947069 = 355151) (by norm_num)
theorem B947093 : Blo 630300 947093 := bbase (se 6 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 947093 = 44395) (by norm_num)
theorem B3208085 : Blo 630300 3208085 := bbase (se 6 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 3208085 = 150379) (by norm_num)
theorem B947117 : Blo 630300 947117 := bbase (se 3 (by rfl) ⟨177584, by rfl⟩ : syracuseStep 947117 = 355169) (by norm_num)
theorem B947141 : Blo 630300 947141 := bbase (se 4 (by rfl) ⟨88794, by rfl⟩ : syracuseStep 947141 = 177589) (by norm_num)
theorem B947165 : Blo 630300 947165 := bbase (se 3 (by rfl) ⟨177593, by rfl⟩ : syracuseStep 947165 = 355187) (by norm_num)
theorem B947189 : Blo 630300 947189 := bbase (se 5 (by rfl) ⟨44399, by rfl⟩ : syracuseStep 947189 = 88799) (by norm_num)
theorem B947213 : Blo 630300 947213 := bbase (se 3 (by rfl) ⟨177602, by rfl⟩ : syracuseStep 947213 = 355205) (by norm_num)
theorem B947237 : Blo 630300 947237 := bbase (se 4 (by rfl) ⟨88803, by rfl⟩ : syracuseStep 947237 = 177607) (by norm_num)
theorem B1602605 : Blo 630300 1602605 := bbase (se 3 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 1602605 = 600977) (by norm_num)
theorem B947261 : Blo 630300 947261 := bbase (se 3 (by rfl) ⟨177611, by rfl⟩ : syracuseStep 947261 = 355223) (by norm_num)
theorem B947285 : Blo 630300 947285 := bbase (se 8 (by rfl) ⟨5550, by rfl⟩ : syracuseStep 947285 = 11101) (by norm_num)
theorem B6157397 : Blo 630300 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1012829 : Blo 630300 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B947309 : Blo 630300 947309 := bbase (se 3 (by rfl) ⟨177620, by rfl⟩ : syracuseStep 947309 = 355241) (by norm_num)
theorem B947333 : Blo 630300 947333 := bbase (se 4 (by rfl) ⟨88812, by rfl⟩ : syracuseStep 947333 = 177625) (by norm_num)
theorem B947357 : Blo 630300 947357 := bbase (se 3 (by rfl) ⟨177629, by rfl⟩ : syracuseStep 947357 = 355259) (by norm_num)
theorem B947381 : Blo 630300 947381 := bbase (se 5 (by rfl) ⟨44408, by rfl⟩ : syracuseStep 947381 = 88817) (by norm_num)
theorem B947405 : Blo 630300 947405 := bbase (se 3 (by rfl) ⟨177638, by rfl⟩ : syracuseStep 947405 = 355277) (by norm_num)
theorem B947429 : Blo 630300 947429 := bbase (se 4 (by rfl) ⟨88821, by rfl⟩ : syracuseStep 947429 = 177643) (by norm_num)
theorem B947453 : Blo 630300 947453 := bbase (se 3 (by rfl) ⟨177647, by rfl⟩ : syracuseStep 947453 = 355295) (by norm_num)
theorem B947477 : Blo 630300 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B947501 : Blo 630300 947501 := bbase (se 3 (by rfl) ⟨177656, by rfl⟩ : syracuseStep 947501 = 355313) (by norm_num)
theorem B947525 : Blo 630300 947525 := bbase (se 4 (by rfl) ⟨88830, by rfl⟩ : syracuseStep 947525 = 177661) (by norm_num)
theorem B947549 : Blo 630300 947549 := bbase (se 3 (by rfl) ⟨177665, by rfl⟩ : syracuseStep 947549 = 355331) (by norm_num)
theorem B947573 : Blo 630300 947573 := bbase (se 5 (by rfl) ⟨44417, by rfl⟩ : syracuseStep 947573 = 88835) (by norm_num)
theorem B1602949 : Blo 630300 1602949 := bbase (se 4 (by rfl) ⟨150276, by rfl⟩ : syracuseStep 1602949 = 300553) (by norm_num)
theorem B947597 : Blo 630300 947597 := bbase (se 3 (by rfl) ⟨177674, by rfl⟩ : syracuseStep 947597 = 355349) (by norm_num)
theorem B947621 : Blo 630300 947621 := bbase (se 4 (by rfl) ⟨88839, by rfl⟩ : syracuseStep 947621 = 177679) (by norm_num)
theorem B947645 : Blo 630300 947645 := bbase (se 3 (by rfl) ⟨177683, by rfl⟩ : syracuseStep 947645 = 355367) (by norm_num)
theorem B947669 : Blo 630300 947669 := bbase (se 7 (by rfl) ⟨11105, by rfl⟩ : syracuseStep 947669 = 22211) (by norm_num)
theorem B947693 : Blo 630300 947693 := bbase (se 3 (by rfl) ⟨177692, by rfl⟩ : syracuseStep 947693 = 355385) (by norm_num)
theorem B1603061 : Blo 630300 1603061 := bbase (se 5 (by rfl) ⟨75143, by rfl⟩ : syracuseStep 1603061 = 150287) (by norm_num)
theorem B947717 : Blo 630300 947717 := bbase (se 4 (by rfl) ⟨88848, by rfl⟩ : syracuseStep 947717 = 177697) (by norm_num)
theorem B947741 : Blo 630300 947741 := bbase (se 3 (by rfl) ⟨177701, by rfl⟩ : syracuseStep 947741 = 355403) (by norm_num)
theorem B947765 : Blo 630300 947765 := bbase (se 5 (by rfl) ⟨44426, by rfl⟩ : syracuseStep 947765 = 88853) (by norm_num)
theorem B947789 : Blo 630300 947789 := bbase (se 3 (by rfl) ⟨177710, by rfl⟩ : syracuseStep 947789 = 355421) (by norm_num)
theorem B1799765 : Blo 630300 1799765 := bbase (se 8 (by rfl) ⟨10545, by rfl⟩ : syracuseStep 1799765 = 21091) (by norm_num)
theorem B947813 : Blo 630300 947813 := bbase (se 4 (by rfl) ⟨88857, by rfl⟩ : syracuseStep 947813 = 177715) (by norm_num)
theorem B4552309 : Blo 630300 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B947837 : Blo 630300 947837 := bbase (se 3 (by rfl) ⟨177719, by rfl⟩ : syracuseStep 947837 = 355439) (by norm_num)
theorem B1013381 : Blo 630300 1013381 := bbase (se 4 (by rfl) ⟨95004, by rfl⟩ : syracuseStep 1013381 = 190009) (by norm_num)
theorem B947861 : Blo 630300 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B1013413 : Blo 630300 1013413 := bbase (se 4 (by rfl) ⟨95007, by rfl⟩ : syracuseStep 1013413 = 190015) (by norm_num)
theorem B947885 : Blo 630300 947885 := bbase (se 3 (by rfl) ⟨177728, by rfl⟩ : syracuseStep 947885 = 355457) (by norm_num)
theorem B1603253 : Blo 630300 1603253 := bbase (se 5 (by rfl) ⟨75152, by rfl⟩ : syracuseStep 1603253 = 150305) (by norm_num)
theorem B947909 : Blo 630300 947909 := bbase (se 4 (by rfl) ⟨88866, by rfl⟩ : syracuseStep 947909 = 177733) (by norm_num)
theorem B947933 : Blo 630300 947933 := bbase (se 3 (by rfl) ⟨177737, by rfl⟩ : syracuseStep 947933 = 355475) (by norm_num)
theorem B1079021 : Blo 630300 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B947957 : Blo 630300 947957 := bbase (se 5 (by rfl) ⟨44435, by rfl⟩ : syracuseStep 947957 = 88871) (by norm_num)
theorem B947981 : Blo 630300 947981 := bbase (se 3 (by rfl) ⟨177746, by rfl⟩ : syracuseStep 947981 = 355493) (by norm_num)
theorem B2127653 : Blo 630300 2127653 := bbase (se 4 (by rfl) ⟨199467, by rfl⟩ : syracuseStep 2127653 = 398935) (by norm_num)
theorem B948005 : Blo 630300 948005 := bbase (se 4 (by rfl) ⟨88875, by rfl⟩ : syracuseStep 948005 = 177751) (by norm_num)
theorem B2029349 : Blo 630300 2029349 := bbase (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) (by norm_num)
theorem B948029 : Blo 630300 948029 := bbase (se 3 (by rfl) ⟨177755, by rfl⟩ : syracuseStep 948029 = 355511) (by norm_num)
theorem B948053 : Blo 630300 948053 := bbase (se 9 (by rfl) ⟨2777, by rfl⟩ : syracuseStep 948053 = 5555) (by norm_num)
theorem B948077 : Blo 630300 948077 := bbase (se 3 (by rfl) ⟨177764, by rfl⟩ : syracuseStep 948077 = 355529) (by norm_num)
theorem B948101 : Blo 630300 948101 := bbase (se 4 (by rfl) ⟨88884, by rfl⟩ : syracuseStep 948101 = 177769) (by norm_num)
theorem B948125 : Blo 630300 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B948149 : Blo 630300 948149 := bbase (se 5 (by rfl) ⟨44444, by rfl⟩ : syracuseStep 948149 = 88889) (by norm_num)
theorem B1079245 : Blo 630300 1079245 := bbase (se 3 (by rfl) ⟨202358, by rfl⟩ : syracuseStep 1079245 = 404717) (by norm_num)
theorem B948173 : Blo 630300 948173 := bbase (se 3 (by rfl) ⟨177782, by rfl⟩ : syracuseStep 948173 = 355565) (by norm_num)
theorem B948197 : Blo 630300 948197 := bbase (se 4 (by rfl) ⟨88893, by rfl⟩ : syracuseStep 948197 = 177787) (by norm_num)
theorem B948221 : Blo 630300 948221 := bbase (se 3 (by rfl) ⟨177791, by rfl⟩ : syracuseStep 948221 = 355583) (by norm_num)
theorem B1603597 : Blo 630300 1603597 := bbase (se 3 (by rfl) ⟨300674, by rfl⟩ : syracuseStep 1603597 = 601349) (by norm_num)
theorem B948245 : Blo 630300 948245 := bbase (se 6 (by rfl) ⟨22224, by rfl⟩ : syracuseStep 948245 = 44449) (by norm_num)
theorem B948269 : Blo 630300 948269 := bbase (se 3 (by rfl) ⟨177800, by rfl⟩ : syracuseStep 948269 = 355601) (by norm_num)
theorem B718913 : Blo 630300 718913 := bbase (se 2 (by rfl) ⟨269592, by rfl⟩ : syracuseStep 718913 = 539185) (by norm_num)
theorem B948293 : Blo 630300 948293 := bbase (se 4 (by rfl) ⟨88902, by rfl⟩ : syracuseStep 948293 = 177805) (by norm_num)
theorem B948317 : Blo 630300 948317 := bbase (se 3 (by rfl) ⟨177809, by rfl⟩ : syracuseStep 948317 = 355619) (by norm_num)
theorem B948341 : Blo 630300 948341 := bbase (se 5 (by rfl) ⟨44453, by rfl⟩ : syracuseStep 948341 = 88907) (by norm_num)
theorem B1603709 : Blo 630300 1603709 := bbase (se 3 (by rfl) ⟨300695, by rfl⟩ : syracuseStep 1603709 = 601391) (by norm_num)
theorem B948365 : Blo 630300 948365 := bbase (se 3 (by rfl) ⟨177818, by rfl⟩ : syracuseStep 948365 = 355637) (by norm_num)
theorem B948389 : Blo 630300 948389 := bbase (se 4 (by rfl) ⟨88911, by rfl⟩ : syracuseStep 948389 = 177823) (by norm_num)
theorem B3209381 : Blo 630300 3209381 := bbase (se 4 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 3209381 = 601759) (by norm_num)
theorem B948413 : Blo 630300 948413 := bbase (se 3 (by rfl) ⟨177827, by rfl⟩ : syracuseStep 948413 = 355655) (by norm_num)
theorem B2128085 : Blo 630300 2128085 := bbase (se 7 (by rfl) ⟨24938, by rfl⟩ : syracuseStep 2128085 = 49877) (by norm_num)
theorem B948437 : Blo 630300 948437 := bbase (se 7 (by rfl) ⟨11114, by rfl⟩ : syracuseStep 948437 = 22229) (by norm_num)
theorem B948461 : Blo 630300 948461 := bbase (se 3 (by rfl) ⟨177836, by rfl⟩ : syracuseStep 948461 = 355673) (by norm_num)
theorem B948485 : Blo 630300 948485 := bbase (se 4 (by rfl) ⟨88920, by rfl⟩ : syracuseStep 948485 = 177841) (by norm_num)
theorem B3045637 : Blo 630300 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B948509 : Blo 630300 948509 := bbase (se 3 (by rfl) ⟨177845, by rfl⟩ : syracuseStep 948509 = 355691) (by norm_num)
theorem B948533 : Blo 630300 948533 := bbase (se 5 (by rfl) ⟨44462, by rfl⟩ : syracuseStep 948533 = 88925) (by norm_num)
theorem B1603901 : Blo 630300 1603901 := bbase (se 3 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 1603901 = 601463) (by norm_num)
theorem B948557 : Blo 630300 948557 := bbase (se 3 (by rfl) ⟨177854, by rfl⟩ : syracuseStep 948557 = 355709) (by norm_num)
theorem B948581 : Blo 630300 948581 := bbase (se 4 (by rfl) ⟨88929, by rfl⟩ : syracuseStep 948581 = 177859) (by norm_num)
theorem B948605 : Blo 630300 948605 := bbase (se 3 (by rfl) ⟨177863, by rfl⟩ : syracuseStep 948605 = 355727) (by norm_num)
theorem B948629 : Blo 630300 948629 := bbase (se 6 (by rfl) ⟨22233, by rfl⟩ : syracuseStep 948629 = 44467) (by norm_num)
theorem B948653 : Blo 630300 948653 := bbase (se 3 (by rfl) ⟨177872, by rfl⟩ : syracuseStep 948653 = 355745) (by norm_num)
theorem B948677 : Blo 630300 948677 := bbase (se 4 (by rfl) ⟨88938, by rfl⟩ : syracuseStep 948677 = 177877) (by norm_num)
theorem B948701 : Blo 630300 948701 := bbase (se 3 (by rfl) ⟨177881, by rfl⟩ : syracuseStep 948701 = 355763) (by norm_num)
theorem B948725 : Blo 630300 948725 := bbase (se 5 (by rfl) ⟨44471, by rfl⟩ : syracuseStep 948725 = 88943) (by norm_num)
theorem B948749 : Blo 630300 948749 := bbase (se 3 (by rfl) ⟨177890, by rfl⟩ : syracuseStep 948749 = 355781) (by norm_num)
theorem B948773 : Blo 630300 948773 := bbase (se 4 (by rfl) ⟨88947, by rfl⟩ : syracuseStep 948773 = 177895) (by norm_num)
theorem B948797 : Blo 630300 948797 := bbase (se 3 (by rfl) ⟨177899, by rfl⟩ : syracuseStep 948797 = 355799) (by norm_num)
theorem B1014341 : Blo 630300 1014341 := bbase (se 4 (by rfl) ⟨95094, by rfl⟩ : syracuseStep 1014341 = 190189) (by norm_num)
theorem B948821 : Blo 630300 948821 := bbase (se 8 (by rfl) ⟨5559, by rfl⟩ : syracuseStep 948821 = 11119) (by norm_num)
theorem B948845 : Blo 630300 948845 := bbase (se 3 (by rfl) ⟨177908, by rfl⟩ : syracuseStep 948845 = 355817) (by norm_num)
theorem B2128517 : Blo 630300 2128517 := bbase (se 4 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 2128517 = 399097) (by norm_num)
theorem B948869 : Blo 630300 948869 := bbase (se 4 (by rfl) ⟨88956, by rfl⟩ : syracuseStep 948869 = 177913) (by norm_num)
theorem B1604245 : Blo 630300 1604245 := bbase (se 6 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 1604245 = 75199) (by norm_num)
theorem B948893 : Blo 630300 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B948917 : Blo 630300 948917 := bbase (se 5 (by rfl) ⟨44480, by rfl⟩ : syracuseStep 948917 = 88961) (by norm_num)
theorem B1440445 : Blo 630300 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B948941 : Blo 630300 948941 := bbase (se 3 (by rfl) ⟨177926, by rfl⟩ : syracuseStep 948941 = 355853) (by norm_num)
theorem B948965 : Blo 630300 948965 := bbase (se 4 (by rfl) ⟨88965, by rfl⟩ : syracuseStep 948965 = 177931) (by norm_num)
theorem B1800949 : Blo 630300 1800949 := bbase (se 5 (by rfl) ⟨84419, by rfl⟩ : syracuseStep 1800949 = 168839) (by norm_num)
theorem B948989 : Blo 630300 948989 := bbase (se 3 (by rfl) ⟨177935, by rfl⟩ : syracuseStep 948989 = 355871) (by norm_num)
theorem B1604357 : Blo 630300 1604357 := bbase (se 4 (by rfl) ⟨150408, by rfl⟩ : syracuseStep 1604357 = 300817) (by norm_num)
theorem B949013 : Blo 630300 949013 := bbase (se 6 (by rfl) ⟨22242, by rfl⟩ : syracuseStep 949013 = 44485) (by norm_num)
theorem B949037 : Blo 630300 949037 := bbase (se 3 (by rfl) ⟨177944, by rfl⟩ : syracuseStep 949037 = 355889) (by norm_num)
theorem B949061 : Blo 630300 949061 := bbase (se 4 (by rfl) ⟨88974, by rfl⟩ : syracuseStep 949061 = 177949) (by norm_num)
theorem B719689 : Blo 630300 719689 := bbase (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) (by norm_num)
theorem B949085 : Blo 630300 949085 := bbase (se 3 (by rfl) ⟨177953, by rfl⟩ : syracuseStep 949085 = 355907) (by norm_num)
theorem B2882405 : Blo 630300 2882405 := bbase (se 4 (by rfl) ⟨270225, by rfl⟩ : syracuseStep 2882405 = 540451) (by norm_num)
theorem B949109 : Blo 630300 949109 := bbase (se 5 (by rfl) ⟨44489, by rfl⟩ : syracuseStep 949109 = 88979) (by norm_num)
theorem B949133 : Blo 630300 949133 := bbase (se 3 (by rfl) ⟨177962, by rfl⟩ : syracuseStep 949133 = 355925) (by norm_num)
theorem B1801109 : Blo 630300 1801109 := bbase (se 6 (by rfl) ⟨42213, by rfl⟩ : syracuseStep 1801109 = 84427) (by norm_num)
theorem B949157 : Blo 630300 949157 := bbase (se 4 (by rfl) ⟨88983, by rfl⟩ : syracuseStep 949157 = 177967) (by norm_num)
theorem B719785 : Blo 630300 719785 := bbase (se 2 (by rfl) ⟨269919, by rfl⟩ : syracuseStep 719785 = 539839) (by norm_num)
theorem B1080245 : Blo 630300 1080245 := bbase (se 5 (by rfl) ⟨50636, by rfl⟩ : syracuseStep 1080245 = 101273) (by norm_num)
theorem B949181 : Blo 630300 949181 := bbase (se 3 (by rfl) ⟨177971, by rfl⟩ : syracuseStep 949181 = 355943) (by norm_num)
theorem B1604549 : Blo 630300 1604549 := bbase (se 4 (by rfl) ⟨150426, by rfl⟩ : syracuseStep 1604549 = 300853) (by norm_num)
theorem B719825 : Blo 630300 719825 := bbase (se 2 (by rfl) ⟨269934, by rfl⟩ : syracuseStep 719825 = 539869) (by norm_num)
theorem B949205 : Blo 630300 949205 := bbase (se 7 (by rfl) ⟨11123, by rfl⟩ : syracuseStep 949205 = 22247) (by norm_num)
theorem B949229 : Blo 630300 949229 := bbase (se 3 (by rfl) ⟨177980, by rfl⟩ : syracuseStep 949229 = 355961) (by norm_num)
theorem B949253 : Blo 630300 949253 := bbase (se 4 (by rfl) ⟨88992, by rfl⟩ : syracuseStep 949253 = 177985) (by norm_num)
theorem B5405717 : Blo 630300 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B949277 : Blo 630300 949277 := bbase (se 3 (by rfl) ⟨177989, by rfl⟩ : syracuseStep 949277 = 355979) (by norm_num)
theorem B2128949 : Blo 630300 2128949 := bbase (se 5 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 2128949 = 199589) (by norm_num)
theorem B949301 : Blo 630300 949301 := bbase (se 5 (by rfl) ⟨44498, by rfl⟩ : syracuseStep 949301 = 88997) (by norm_num)
theorem B949325 : Blo 630300 949325 := bbase (se 3 (by rfl) ⟨177998, by rfl⟩ : syracuseStep 949325 = 355997) (by norm_num)
theorem B949349 : Blo 630300 949349 := bbase (se 4 (by rfl) ⟨89001, by rfl⟩ : syracuseStep 949349 = 178003) (by norm_num)
theorem B949373 : Blo 630300 949373 := bbase (se 3 (by rfl) ⟨178007, by rfl⟩ : syracuseStep 949373 = 356015) (by norm_num)
theorem B1801349 : Blo 630300 1801349 := bbase (se 4 (by rfl) ⟨168876, by rfl⟩ : syracuseStep 1801349 = 337753) (by norm_num)
theorem B949397 : Blo 630300 949397 := bbase (se 6 (by rfl) ⟨22251, by rfl⟩ : syracuseStep 949397 = 44503) (by norm_num)
theorem B949421 : Blo 630300 949421 := bbase (se 3 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 949421 = 356033) (by norm_num)
theorem B949445 : Blo 630300 949445 := bbase (se 4 (by rfl) ⟨89010, by rfl⟩ : syracuseStep 949445 = 178021) (by norm_num)
theorem B949469 : Blo 630300 949469 := bbase (se 3 (by rfl) ⟨178025, by rfl⟩ : syracuseStep 949469 = 356051) (by norm_num)
theorem B1015021 : Blo 630300 1015021 := bbase (se 3 (by rfl) ⟨190316, by rfl⟩ : syracuseStep 1015021 = 380633) (by norm_num)
theorem B949493 : Blo 630300 949493 := bbase (se 5 (by rfl) ⟨44507, by rfl⟩ : syracuseStep 949493 = 89015) (by norm_num)
theorem B1441037 : Blo 630300 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B949517 : Blo 630300 949517 := bbase (se 3 (by rfl) ⟨178034, by rfl⟩ : syracuseStep 949517 = 356069) (by norm_num)
theorem B1604893 : Blo 630300 1604893 := bbase (se 3 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 1604893 = 601835) (by norm_num)
theorem B1080613 : Blo 630300 1080613 := bbase (se 4 (by rfl) ⟨101307, by rfl⟩ : syracuseStep 1080613 = 202615) (by norm_num)
theorem B949541 : Blo 630300 949541 := bbase (se 4 (by rfl) ⟨89019, by rfl⟩ : syracuseStep 949541 = 178039) (by norm_num)
theorem B1015085 : Blo 630300 1015085 := bbase (se 3 (by rfl) ⟨190328, by rfl⟩ : syracuseStep 1015085 = 380657) (by norm_num)
theorem B949565 : Blo 630300 949565 := bbase (se 3 (by rfl) ⟨178043, by rfl⟩ : syracuseStep 949565 = 356087) (by norm_num)
theorem B1801541 : Blo 630300 1801541 := bbase (se 4 (by rfl) ⟨168894, by rfl⟩ : syracuseStep 1801541 = 337789) (by norm_num)
theorem B949589 : Blo 630300 949589 := bbase (se 11 (by rfl) ⟨695, by rfl⟩ : syracuseStep 949589 = 1391) (by norm_num)
theorem B949613 : Blo 630300 949613 := bbase (se 3 (by rfl) ⟨178052, by rfl⟩ : syracuseStep 949613 = 356105) (by norm_num)
theorem B949637 : Blo 630300 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B1605005 : Blo 630300 1605005 := bbase (se 3 (by rfl) ⟨300938, by rfl⟩ : syracuseStep 1605005 = 601877) (by norm_num)
theorem B949661 : Blo 630300 949661 := bbase (se 3 (by rfl) ⟨178061, by rfl⟩ : syracuseStep 949661 = 356123) (by norm_num)
theorem B949685 : Blo 630300 949685 := bbase (se 5 (by rfl) ⟨44516, by rfl⟩ : syracuseStep 949685 = 89033) (by norm_num)
theorem B3210677 : Blo 630300 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B949709 : Blo 630300 949709 := bbase (se 3 (by rfl) ⟨178070, by rfl⟩ : syracuseStep 949709 = 356141) (by norm_num)
theorem B8224213 : Blo 630300 8224213 := bbase (se 7 (by rfl) ⟨96377, by rfl⟩ : syracuseStep 8224213 = 192755) (by norm_num)
theorem B2129381 : Blo 630300 2129381 := bbase (se 4 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 2129381 = 399259) (by norm_num)
theorem B949733 : Blo 630300 949733 := bbase (se 4 (by rfl) ⟨89037, by rfl⟩ : syracuseStep 949733 = 178075) (by norm_num)
theorem B949757 : Blo 630300 949757 := bbase (se 3 (by rfl) ⟨178079, by rfl⟩ : syracuseStep 949757 = 356159) (by norm_num)
theorem B949781 : Blo 630300 949781 := bbase (se 6 (by rfl) ⟨22260, by rfl⟩ : syracuseStep 949781 = 44521) (by norm_num)
theorem B949805 : Blo 630300 949805 := bbase (se 3 (by rfl) ⟨178088, by rfl⟩ : syracuseStep 949805 = 356177) (by norm_num)
theorem B949829 : Blo 630300 949829 := bbase (se 4 (by rfl) ⟨89046, by rfl⟩ : syracuseStep 949829 = 178093) (by norm_num)
theorem B1605197 : Blo 630300 1605197 := bbase (se 3 (by rfl) ⟨300974, by rfl⟩ : syracuseStep 1605197 = 601949) (by norm_num)
theorem B949853 : Blo 630300 949853 := bbase (se 3 (by rfl) ⟨178097, by rfl⟩ : syracuseStep 949853 = 356195) (by norm_num)
theorem B3604085 : Blo 630300 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B949877 : Blo 630300 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B949901 : Blo 630300 949901 := bbase (se 3 (by rfl) ⟨178106, by rfl⟩ : syracuseStep 949901 = 356213) (by norm_num)
theorem B949925 : Blo 630300 949925 := bbase (se 4 (by rfl) ⟨89055, by rfl⟩ : syracuseStep 949925 = 178111) (by norm_num)
theorem B949949 : Blo 630300 949949 := bbase (se 3 (by rfl) ⟨178115, by rfl⟩ : syracuseStep 949949 = 356231) (by norm_num)
theorem B949973 : Blo 630300 949973 := bbase (se 7 (by rfl) ⟨11132, by rfl⟩ : syracuseStep 949973 = 22265) (by norm_num)
theorem B949997 : Blo 630300 949997 := bbase (se 3 (by rfl) ⟨178124, by rfl⟩ : syracuseStep 949997 = 356249) (by norm_num)
theorem B950021 : Blo 630300 950021 := bbase (se 4 (by rfl) ⟨89064, by rfl⟩ : syracuseStep 950021 = 178129) (by norm_num)
theorem B950045 : Blo 630300 950045 := bbase (se 3 (by rfl) ⟨178133, by rfl⟩ : syracuseStep 950045 = 356267) (by norm_num)
theorem B950069 : Blo 630300 950069 := bbase (se 5 (by rfl) ⟨44534, by rfl⟩ : syracuseStep 950069 = 89069) (by norm_num)
theorem B950093 : Blo 630300 950093 := bbase (se 3 (by rfl) ⟨178142, by rfl⟩ : syracuseStep 950093 = 356285) (by norm_num)
theorem B950117 : Blo 630300 950117 := bbase (se 4 (by rfl) ⟨89073, by rfl⟩ : syracuseStep 950117 = 178147) (by norm_num)
theorem B950141 : Blo 630300 950141 := bbase (se 3 (by rfl) ⟨178151, by rfl⟩ : syracuseStep 950141 = 356303) (by norm_num)
theorem B2129813 : Blo 630300 2129813 := bbase (se 6 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 2129813 = 99835) (by norm_num)
theorem B950165 : Blo 630300 950165 := bbase (se 6 (by rfl) ⟨22269, by rfl⟩ : syracuseStep 950165 = 44539) (by norm_num)
theorem B1605541 : Blo 630300 1605541 := bbase (se 4 (by rfl) ⟨150519, by rfl⟩ : syracuseStep 1605541 = 301039) (by norm_num)
theorem B950189 : Blo 630300 950189 := bbase (se 3 (by rfl) ⟨178160, by rfl⟩ : syracuseStep 950189 = 356321) (by norm_num)
theorem B950213 : Blo 630300 950213 := bbase (se 4 (by rfl) ⟨89082, by rfl⟩ : syracuseStep 950213 = 178165) (by norm_num)
theorem B720857 : Blo 630300 720857 := bbase (se 2 (by rfl) ⟨270321, by rfl⟩ : syracuseStep 720857 = 540643) (by norm_num)
theorem B950237 : Blo 630300 950237 := bbase (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) (by norm_num)
theorem B950261 : Blo 630300 950261 := bbase (se 5 (by rfl) ⟨44543, by rfl⟩ : syracuseStep 950261 = 89087) (by norm_num)
theorem B2031605 : Blo 630300 2031605 := bbase (se 5 (by rfl) ⟨95231, by rfl⟩ : syracuseStep 2031605 = 190463) (by norm_num)
theorem B950273 : Blo 630300 950273 := bstep (se 2 (by rfl) ⟨356352, by rfl⟩ : syracuseStep 950273 = 712705) B712705
theorem B950291 : Blo 630300 950291 := bstep (se 1 (by rfl) ⟨712718, by rfl⟩ : syracuseStep 950291 = 1425437) B1425437
theorem B852001 : Blo 630300 852001 := bstep (se 2 (by rfl) ⟨319500, by rfl⟩ : syracuseStep 852001 = 639001) B639001
theorem B1015841 : Blo 630300 1015841 := bstep (se 2 (by rfl) ⟨380940, by rfl⟩ : syracuseStep 1015841 = 761881) B761881
theorem B950321 : Blo 630300 950321 := bstep (se 2 (by rfl) ⟨356370, by rfl⟩ : syracuseStep 950321 = 712741) B712741
theorem B950339 : Blo 630300 950339 := bstep (se 1 (by rfl) ⟨712754, by rfl⟩ : syracuseStep 950339 = 1425509) B1425509
theorem B950369 : Blo 630300 950369 := bstep (se 2 (by rfl) ⟨356388, by rfl⟩ : syracuseStep 950369 = 712777) B712777
theorem B2130029 : Blo 630300 2130029 := bstep (se 3 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 2130029 = 798761) B798761
theorem B950387 : Blo 630300 950387 := bstep (se 1 (by rfl) ⟨712790, by rfl⟩ : syracuseStep 950387 = 1425581) B1425581
theorem B950417 : Blo 630300 950417 := bstep (se 2 (by rfl) ⟨356406, by rfl⟩ : syracuseStep 950417 = 712813) B712813
theorem B2130083 : Blo 630300 2130083 := bstep (se 1 (by rfl) ⟨1597562, by rfl⟩ : syracuseStep 2130083 = 3195125) B3195125
theorem B950435 : Blo 630300 950435 := bstep (se 1 (by rfl) ⟨712826, by rfl⟩ : syracuseStep 950435 = 1425653) B1425653
theorem B950465 : Blo 630300 950465 := bstep (se 2 (by rfl) ⟨356424, by rfl⟩ : syracuseStep 950465 = 712849) B712849
theorem B950483 : Blo 630300 950483 := bstep (se 1 (by rfl) ⟨712862, by rfl⟩ : syracuseStep 950483 = 1425725) B1425725
theorem B950513 : Blo 630300 950513 := bstep (se 2 (by rfl) ⟨356442, by rfl⟩ : syracuseStep 950513 = 712885) B712885
theorem B950531 : Blo 630300 950531 := bstep (se 1 (by rfl) ⟨712898, by rfl⟩ : syracuseStep 950531 = 1425797) B1425797
theorem B950561 : Blo 630300 950561 := bstep (se 2 (by rfl) ⟨356460, by rfl⟩ : syracuseStep 950561 = 712921) B712921
theorem B950579 : Blo 630300 950579 := bstep (se 1 (by rfl) ⟨712934, by rfl⟩ : syracuseStep 950579 = 1425869) B1425869
theorem B950609 : Blo 630300 950609 := bstep (se 2 (by rfl) ⟨356478, by rfl⟩ : syracuseStep 950609 = 712957) B712957
theorem B950627 : Blo 630300 950627 := bstep (se 1 (by rfl) ⟨712970, by rfl⟩ : syracuseStep 950627 = 1425941) B1425941
theorem B950657 : Blo 630300 950657 := bstep (se 2 (by rfl) ⟨356496, by rfl⟩ : syracuseStep 950657 = 712993) B712993
theorem B950675 : Blo 630300 950675 := bstep (se 1 (by rfl) ⟨713006, by rfl⟩ : syracuseStep 950675 = 1426013) B1426013
theorem B2130353 : Blo 630300 2130353 := bstep (se 2 (by rfl) ⟨798882, by rfl⟩ : syracuseStep 2130353 = 1597765) B1597765
theorem B950705 : Blo 630300 950705 := bstep (se 2 (by rfl) ⟨356514, by rfl⟩ : syracuseStep 950705 = 713029) B713029
theorem B950723 : Blo 630300 950723 := bstep (se 1 (by rfl) ⟨713042, by rfl⟩ : syracuseStep 950723 = 1426085) B1426085
theorem B950753 : Blo 630300 950753 := bstep (se 2 (by rfl) ⟨356532, by rfl⟩ : syracuseStep 950753 = 713065) B713065
theorem B950771 : Blo 630300 950771 := bstep (se 1 (by rfl) ⟨713078, by rfl⟩ : syracuseStep 950771 = 1426157) B1426157
theorem B950801 : Blo 630300 950801 := bstep (se 2 (by rfl) ⟨356550, by rfl⟩ : syracuseStep 950801 = 713101) B713101
theorem B950819 : Blo 630300 950819 := bstep (se 1 (by rfl) ⟨713114, by rfl⟩ : syracuseStep 950819 = 1426229) B1426229
theorem B950849 : Blo 630300 950849 := bstep (se 2 (by rfl) ⟨356568, by rfl⟩ : syracuseStep 950849 = 713137) B713137
theorem B950867 : Blo 630300 950867 := bstep (se 1 (by rfl) ⟨713150, by rfl⟩ : syracuseStep 950867 = 1426301) B1426301
theorem B950897 : Blo 630300 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B950915 : Blo 630300 950915 := bstep (se 1 (by rfl) ⟨713186, by rfl⟩ : syracuseStep 950915 = 1426373) B1426373
theorem B950945 : Blo 630300 950945 := bstep (se 2 (by rfl) ⟨356604, by rfl⟩ : syracuseStep 950945 = 713209) B713209
theorem B950963 : Blo 630300 950963 := bstep (se 1 (by rfl) ⟨713222, by rfl⟩ : syracuseStep 950963 = 1426445) B1426445
theorem B950993 : Blo 630300 950993 := bstep (se 2 (by rfl) ⟨356622, by rfl⟩ : syracuseStep 950993 = 713245) B713245
theorem B951011 : Blo 630300 951011 := bstep (se 1 (by rfl) ⟨713258, by rfl⟩ : syracuseStep 951011 = 1426517) B1426517
theorem B951041 : Blo 630300 951041 := bstep (se 2 (by rfl) ⟨356640, by rfl⟩ : syracuseStep 951041 = 713281) B713281
theorem B951059 : Blo 630300 951059 := bstep (se 1 (by rfl) ⟨713294, by rfl⟩ : syracuseStep 951059 = 1426589) B1426589
theorem B951089 : Blo 630300 951089 := bstep (se 2 (by rfl) ⟨356658, by rfl⟩ : syracuseStep 951089 = 713317) B713317
theorem B951107 : Blo 630300 951107 := bstep (se 1 (by rfl) ⟨713330, by rfl⟩ : syracuseStep 951107 = 1426661) B1426661
theorem B951137 : Blo 630300 951137 := bstep (se 2 (by rfl) ⟨356676, by rfl⟩ : syracuseStep 951137 = 713353) B713353
theorem B2556785 : Blo 630300 2556785 := bstep (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) B1917589
theorem B951155 : Blo 630300 951155 := bstep (se 1 (by rfl) ⟨713366, by rfl⟩ : syracuseStep 951155 = 1426733) B1426733
theorem B951185 : Blo 630300 951185 := bstep (se 2 (by rfl) ⟨356694, by rfl⟩ : syracuseStep 951185 = 713389) B713389
theorem B951203 : Blo 630300 951203 := bstep (se 1 (by rfl) ⟨713402, by rfl⟩ : syracuseStep 951203 = 1426805) B1426805
theorem B951233 : Blo 630300 951233 := bstep (se 2 (by rfl) ⟨356712, by rfl⟩ : syracuseStep 951233 = 713425) B713425
theorem B2130893 : Blo 630300 2130893 := bstep (se 3 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 2130893 = 799085) B799085
theorem B1278929 : Blo 630300 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B951251 : Blo 630300 951251 := bstep (se 1 (by rfl) ⟨713438, by rfl⟩ : syracuseStep 951251 = 1426877) B1426877
theorem B951281 : Blo 630300 951281 := bstep (se 2 (by rfl) ⟨356730, by rfl⟩ : syracuseStep 951281 = 713461) B713461
theorem B2130947 : Blo 630300 2130947 := bstep (se 1 (by rfl) ⟨1598210, by rfl⟩ : syracuseStep 2130947 = 3196421) B3196421
theorem B951299 : Blo 630300 951299 := bstep (se 1 (by rfl) ⟨713474, by rfl⟩ : syracuseStep 951299 = 1426949) B1426949
theorem B951329 : Blo 630300 951329 := bstep (se 2 (by rfl) ⟨356748, by rfl⟩ : syracuseStep 951329 = 713497) B713497
theorem B951347 : Blo 630300 951347 := bstep (se 1 (by rfl) ⟨713510, by rfl⟩ : syracuseStep 951347 = 1427021) B1427021
theorem B951377 : Blo 630300 951377 := bstep (se 2 (by rfl) ⟨356766, by rfl⟩ : syracuseStep 951377 = 713533) B713533
theorem B951395 : Blo 630300 951395 := bstep (se 1 (by rfl) ⟨713546, by rfl⟩ : syracuseStep 951395 = 1427093) B1427093
theorem B951425 : Blo 630300 951425 := bstep (se 2 (by rfl) ⟨356784, by rfl⟩ : syracuseStep 951425 = 713569) B713569
theorem B951443 : Blo 630300 951443 := bstep (se 1 (by rfl) ⟨713582, by rfl⟩ : syracuseStep 951443 = 1427165) B1427165
theorem B2131217 : Blo 630300 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B3605795 : Blo 630300 3605795 := bstep (se 1 (by rfl) ⟨2704346, by rfl⟩ : syracuseStep 3605795 = 5408693) B5408693
theorem B16647565 : Blo 630300 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B1803683 : Blo 630300 1803683 := bstep (se 1 (by rfl) ⟨1352762, by rfl⟩ : syracuseStep 1803683 = 2705525) B2705525
theorem B1213937 : Blo 630300 1213937 := bstep (se 2 (by rfl) ⟨455226, by rfl⟩ : syracuseStep 1213937 = 910453) B910453
theorem B2164429 : Blo 630300 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B2131757 : Blo 630300 2131757 := bstep (se 3 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 2131757 = 799409) B799409
theorem B2131811 : Blo 630300 2131811 := bstep (se 1 (by rfl) ⟨1598858, by rfl⟩ : syracuseStep 2131811 = 3197717) B3197717
theorem B854003 : Blo 630300 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B2132081 : Blo 630300 2132081 := bstep (se 2 (by rfl) ⟨799530, by rfl⟩ : syracuseStep 2132081 = 1599061) B1599061
theorem B12159173 : Blo 630300 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B1280305 : Blo 630300 1280305 := bstep (se 2 (by rfl) ⟨480114, by rfl⟩ : syracuseStep 1280305 = 960229) B960229
theorem B1706339 : Blo 630300 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B1804913 : Blo 630300 1804913 := bstep (se 2 (by rfl) ⟨676842, by rfl⟩ : syracuseStep 1804913 = 1353685) B1353685
theorem B2132621 : Blo 630300 2132621 := bstep (se 3 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 2132621 = 799733) B799733
theorem B2132675 : Blo 630300 2132675 := bstep (se 1 (by rfl) ⟨1599506, by rfl⟩ : syracuseStep 2132675 = 3199013) B3199013
theorem B1346321 : Blo 630300 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B2132945 : Blo 630300 2132945 := bstep (se 2 (by rfl) ⟨799854, by rfl⟩ : syracuseStep 2132945 = 1599709) B1599709
theorem B1084385 : Blo 630300 1084385 := bstep (se 2 (by rfl) ⟨406644, by rfl⟩ : syracuseStep 1084385 = 813289) B813289
theorem B3607685 : Blo 630300 3607685 := bstep (se 4 (by rfl) ⟨338220, by rfl⟩ : syracuseStep 3607685 = 676441) B676441
theorem B1707313 : Blo 630300 1707313 := bstep (se 2 (by rfl) ⟨640242, by rfl⟩ : syracuseStep 1707313 = 1280485) B1280485
theorem B2133485 : Blo 630300 2133485 := bstep (se 3 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 2133485 = 800057) B800057
theorem B2133539 : Blo 630300 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B1347185 : Blo 630300 1347185 := bstep (se 2 (by rfl) ⟨505194, by rfl⟩ : syracuseStep 1347185 = 1010389) B1010389
theorem B7212725 : Blo 630300 7212725 := bstep (se 5 (by rfl) ⟨338096, by rfl⟩ : syracuseStep 7212725 = 676193) B676193
theorem B2395889 : Blo 630300 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B2133809 : Blo 630300 2133809 := bstep (se 2 (by rfl) ⟨800178, by rfl⟩ : syracuseStep 2133809 = 1600357) B1600357
theorem B3411811 : Blo 630300 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B6230029 : Blo 630300 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B1446211 : Blo 630300 1446211 := bstep (se 1 (by rfl) ⟨1084658, by rfl⟩ : syracuseStep 1446211 = 2169317) B2169317
theorem B2134349 : Blo 630300 2134349 := bstep (se 3 (by rfl) ⟨400190, by rfl⟩ : syracuseStep 2134349 = 800381) B800381
theorem B4854115 : Blo 630300 4854115 := bstep (se 1 (by rfl) ⟨3640586, by rfl⟩ : syracuseStep 4854115 = 7281173) B7281173
theorem B2134403 : Blo 630300 2134403 := bstep (se 1 (by rfl) ⟨1600802, by rfl⟩ : syracuseStep 2134403 = 3201605) B3201605
theorem B856499 : Blo 630300 856499 := bstep (se 1 (by rfl) ⟨642374, by rfl⟩ : syracuseStep 856499 = 1284749) B1284749
theorem B2167249 : Blo 630300 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B1282673 : Blo 630300 1282673 := bstep (se 2 (by rfl) ⟨481002, by rfl⟩ : syracuseStep 1282673 = 962005) B962005
theorem B2134673 : Blo 630300 2134673 := bstep (se 2 (by rfl) ⟨800502, by rfl⟩ : syracuseStep 2134673 = 1601005) B1601005
theorem B2167523 : Blo 630300 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B2167565 : Blo 630300 2167565 := bstep (se 3 (by rfl) ⟨406418, by rfl⟩ : syracuseStep 2167565 = 812837) B812837
theorem B1348483 : Blo 630300 1348483 := bstep (se 1 (by rfl) ⟨1011362, by rfl⟩ : syracuseStep 1348483 = 2022725) B2022725
theorem B3838853 : Blo 630300 3838853 := bstep (se 4 (by rfl) ⟨359892, by rfl⟩ : syracuseStep 3838853 = 719785) B719785
theorem B2397347 : Blo 630300 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B2135213 : Blo 630300 2135213 := bstep (se 3 (by rfl) ⟨400352, by rfl⟩ : syracuseStep 2135213 = 800705) B800705
theorem B2135267 : Blo 630300 2135267 := bstep (se 1 (by rfl) ⟨1601450, by rfl⟩ : syracuseStep 2135267 = 3202901) B3202901
theorem B2135537 : Blo 630300 2135537 := bstep (se 2 (by rfl) ⟨800826, by rfl⟩ : syracuseStep 2135537 = 1601653) B1601653
theorem B4396963 : Blo 630300 4396963 := bstep (se 1 (by rfl) ⟨3297722, by rfl⟩ : syracuseStep 4396963 = 6595445) B6595445
theorem B2136077 : Blo 630300 2136077 := bstep (se 3 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 2136077 = 801029) B801029
theorem B2136131 : Blo 630300 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B1349713 : Blo 630300 1349713 := bstep (se 2 (by rfl) ⟨506142, by rfl⟩ : syracuseStep 1349713 = 1012285) B1012285
theorem B2398349 : Blo 630300 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B694451 : Blo 630300 694451 := bstep (se 1 (by rfl) ⟨520838, by rfl⟩ : syracuseStep 694451 = 1041677) B1041677
theorem B2136401 : Blo 630300 2136401 := bstep (se 2 (by rfl) ⟨801150, by rfl⟩ : syracuseStep 2136401 = 1602301) B1602301
theorem B1284547 : Blo 630300 1284547 := bstep (se 1 (by rfl) ⟨963410, by rfl⟩ : syracuseStep 1284547 = 1926821) B1926821
theorem B2103779 : Blo 630300 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B1219139 : Blo 630300 1219139 := bstep (se 1 (by rfl) ⟨914354, by rfl⟩ : syracuseStep 1219139 = 1828709) B1828709
theorem B2169425 : Blo 630300 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B2693837 : Blo 630300 2693837 := bstep (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) B1010189
theorem B1350371 : Blo 630300 1350371 := bstep (se 1 (by rfl) ⟨1012778, by rfl⟩ : syracuseStep 1350371 = 2025557) B2025557
theorem B9116387 : Blo 630300 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B4332365 : Blo 630300 4332365 := bstep (se 3 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 4332365 = 1624637) B1624637
theorem B2136941 : Blo 630300 2136941 := bstep (se 3 (by rfl) ⟨400676, by rfl⟩ : syracuseStep 2136941 = 801353) B801353
theorem B1284977 : Blo 630300 1284977 := bstep (se 2 (by rfl) ⟨481866, by rfl⟩ : syracuseStep 1284977 = 963733) B963733
theorem B2136995 : Blo 630300 2136995 := bstep (se 1 (by rfl) ⟨1602746, by rfl⟩ : syracuseStep 2136995 = 3205493) B3205493
theorem B2137265 : Blo 630300 2137265 := bstep (se 2 (by rfl) ⟨801474, by rfl⟩ : syracuseStep 2137265 = 1602949) B1602949
theorem B761059 : Blo 630300 761059 := bstep (se 1 (by rfl) ⟨570794, by rfl⟩ : syracuseStep 761059 = 1141589) B1141589
theorem B1514737 : Blo 630300 1514737 := bstep (se 2 (by rfl) ⟨568026, by rfl⟩ : syracuseStep 1514737 = 1136053) B1136053
theorem B6069745 : Blo 630300 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B630307 : Blo 630300 630307 := bstep (se 1 (by rfl) ⟨472730, by rfl⟩ : syracuseStep 630307 = 945461) B945461
theorem B1351217 : Blo 630300 1351217 := bstep (se 2 (by rfl) ⟨506706, by rfl⟩ : syracuseStep 1351217 = 1013413) B1013413
theorem B630323 : Blo 630300 630323 := bstep (se 1 (by rfl) ⟨472742, by rfl⟩ : syracuseStep 630323 = 945485) B945485
theorem B24288821 : Blo 630300 24288821 := bstep (se 5 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 24288821 = 2277077) B2277077
theorem B630339 : Blo 630300 630339 := bstep (se 1 (by rfl) ⟨472754, by rfl⟩ : syracuseStep 630339 = 945509) B945509
theorem B630355 : Blo 630300 630355 := bstep (se 1 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 630355 = 945533) B945533
theorem B630371 : Blo 630300 630371 := bstep (se 1 (by rfl) ⟨472778, by rfl⟩ : syracuseStep 630371 = 945557) B945557
theorem B630387 : Blo 630300 630387 := bstep (se 1 (by rfl) ⟨472790, by rfl⟩ : syracuseStep 630387 = 945581) B945581
theorem B630403 : Blo 630300 630403 := bstep (se 1 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 630403 = 945605) B945605
theorem B630419 : Blo 630300 630419 := bstep (se 1 (by rfl) ⟨472814, by rfl⟩ : syracuseStep 630419 = 945629) B945629
theorem B630435 : Blo 630300 630435 := bstep (se 1 (by rfl) ⟨472826, by rfl⟩ : syracuseStep 630435 = 945653) B945653
theorem B630451 : Blo 630300 630451 := bstep (se 1 (by rfl) ⟨472838, by rfl⟩ : syracuseStep 630451 = 945677) B945677
theorem B630467 : Blo 630300 630467 := bstep (se 1 (by rfl) ⟨472850, by rfl⟩ : syracuseStep 630467 = 945701) B945701
theorem B2137805 : Blo 630300 2137805 := bstep (se 3 (by rfl) ⟨400838, by rfl⟩ : syracuseStep 2137805 = 801677) B801677
theorem B630483 : Blo 630300 630483 := bstep (se 1 (by rfl) ⟨472862, by rfl⟩ : syracuseStep 630483 = 945725) B945725
theorem B630499 : Blo 630300 630499 := bstep (se 1 (by rfl) ⟨472874, by rfl⟩ : syracuseStep 630499 = 945749) B945749
theorem B630515 : Blo 630300 630515 := bstep (se 1 (by rfl) ⟨472886, by rfl⟩ : syracuseStep 630515 = 945773) B945773
theorem B630531 : Blo 630300 630531 := bstep (se 1 (by rfl) ⟨472898, by rfl⟩ : syracuseStep 630531 = 945797) B945797
theorem B2137859 : Blo 630300 2137859 := bstep (se 1 (by rfl) ⟨1603394, by rfl⟩ : syracuseStep 2137859 = 3206789) B3206789
theorem B630547 : Blo 630300 630547 := bstep (se 1 (by rfl) ⟨472910, by rfl⟩ : syracuseStep 630547 = 945821) B945821
theorem B630563 : Blo 630300 630563 := bstep (se 1 (by rfl) ⟨472922, by rfl⟩ : syracuseStep 630563 = 945845) B945845
theorem B630579 : Blo 630300 630579 := bstep (se 1 (by rfl) ⟨472934, by rfl⟩ : syracuseStep 630579 = 945869) B945869
theorem B630595 : Blo 630300 630595 := bstep (se 1 (by rfl) ⟨472946, by rfl⟩ : syracuseStep 630595 = 945893) B945893
theorem B630611 : Blo 630300 630611 := bstep (se 1 (by rfl) ⟨472958, by rfl⟩ : syracuseStep 630611 = 945917) B945917
theorem B630627 : Blo 630300 630627 := bstep (se 1 (by rfl) ⟨472970, by rfl⟩ : syracuseStep 630627 = 945941) B945941
theorem B630643 : Blo 630300 630643 := bstep (se 1 (by rfl) ⟨472982, by rfl⟩ : syracuseStep 630643 = 945965) B945965
theorem B630659 : Blo 630300 630659 := bstep (se 1 (by rfl) ⟨472994, by rfl⟩ : syracuseStep 630659 = 945989) B945989
theorem B630675 : Blo 630300 630675 := bstep (se 1 (by rfl) ⟨473006, by rfl⟩ : syracuseStep 630675 = 946013) B946013
theorem B630691 : Blo 630300 630691 := bstep (se 1 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 630691 = 946037) B946037
theorem B630707 : Blo 630300 630707 := bstep (se 1 (by rfl) ⟨473030, by rfl⟩ : syracuseStep 630707 = 946061) B946061
theorem B630723 : Blo 630300 630723 := bstep (se 1 (by rfl) ⟨473042, by rfl⟩ : syracuseStep 630723 = 946085) B946085
theorem B4038605 : Blo 630300 4038605 := bstep (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) B1514477
theorem B630739 : Blo 630300 630739 := bstep (se 1 (by rfl) ⟨473054, by rfl⟩ : syracuseStep 630739 = 946109) B946109
theorem B630755 : Blo 630300 630755 := bstep (se 1 (by rfl) ⟨473066, by rfl⟩ : syracuseStep 630755 = 946133) B946133
theorem B630771 : Blo 630300 630771 := bstep (se 1 (by rfl) ⟨473078, by rfl⟩ : syracuseStep 630771 = 946157) B946157
theorem B630787 : Blo 630300 630787 := bstep (se 1 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 630787 = 946181) B946181
theorem B2138129 : Blo 630300 2138129 := bstep (se 2 (by rfl) ⟨801798, by rfl⟩ : syracuseStep 2138129 = 1603597) B1603597
theorem B630803 : Blo 630300 630803 := bstep (se 1 (by rfl) ⟨473102, by rfl⟩ : syracuseStep 630803 = 946205) B946205
theorem B630819 : Blo 630300 630819 := bstep (se 1 (by rfl) ⟨473114, by rfl⟩ : syracuseStep 630819 = 946229) B946229
theorem B630835 : Blo 630300 630835 := bstep (se 1 (by rfl) ⟨473126, by rfl⟩ : syracuseStep 630835 = 946253) B946253
theorem B630851 : Blo 630300 630851 := bstep (se 1 (by rfl) ⟨473138, by rfl⟩ : syracuseStep 630851 = 946277) B946277
theorem B630867 : Blo 630300 630867 := bstep (se 1 (by rfl) ⟨473150, by rfl⟩ : syracuseStep 630867 = 946301) B946301
theorem B630883 : Blo 630300 630883 := bstep (se 1 (by rfl) ⟨473162, by rfl⟩ : syracuseStep 630883 = 946325) B946325
theorem B630899 : Blo 630300 630899 := bstep (se 1 (by rfl) ⟨473174, by rfl⟩ : syracuseStep 630899 = 946349) B946349
theorem B630915 : Blo 630300 630915 := bstep (se 1 (by rfl) ⟨473186, by rfl⟩ : syracuseStep 630915 = 946373) B946373
theorem B630931 : Blo 630300 630931 := bstep (se 1 (by rfl) ⟨473198, by rfl⟩ : syracuseStep 630931 = 946397) B946397
theorem B630947 : Blo 630300 630947 := bstep (se 1 (by rfl) ⟨473210, by rfl⟩ : syracuseStep 630947 = 946421) B946421
theorem B630963 : Blo 630300 630963 := bstep (se 1 (by rfl) ⟨473222, by rfl⟩ : syracuseStep 630963 = 946445) B946445
theorem B630979 : Blo 630300 630979 := bstep (se 1 (by rfl) ⟨473234, by rfl⟩ : syracuseStep 630979 = 946469) B946469
theorem B2400461 : Blo 630300 2400461 := bstep (se 3 (by rfl) ⟨450086, by rfl⟩ : syracuseStep 2400461 = 900173) B900173
theorem B630995 : Blo 630300 630995 := bstep (se 1 (by rfl) ⟨473246, by rfl⟩ : syracuseStep 630995 = 946493) B946493
theorem B631011 : Blo 630300 631011 := bstep (se 1 (by rfl) ⟨473258, by rfl⟩ : syracuseStep 631011 = 946517) B946517
theorem B631027 : Blo 630300 631027 := bstep (se 1 (by rfl) ⟨473270, by rfl⟩ : syracuseStep 631027 = 946541) B946541
theorem B631043 : Blo 630300 631043 := bstep (se 1 (by rfl) ⟨473282, by rfl⟩ : syracuseStep 631043 = 946565) B946565
theorem B958739 : Blo 630300 958739 := bstep (se 1 (by rfl) ⟨719054, by rfl⟩ : syracuseStep 958739 = 1438109) B1438109
theorem B631059 : Blo 630300 631059 := bstep (se 1 (by rfl) ⟨473294, by rfl⟩ : syracuseStep 631059 = 946589) B946589
theorem B631075 : Blo 630300 631075 := bstep (se 1 (by rfl) ⟨473306, by rfl⟩ : syracuseStep 631075 = 946613) B946613
theorem B925987 : Blo 630300 925987 := bstep (se 1 (by rfl) ⟨694490, by rfl⟩ : syracuseStep 925987 = 1388981) B1388981
theorem B631091 : Blo 630300 631091 := bstep (se 1 (by rfl) ⟨473318, by rfl⟩ : syracuseStep 631091 = 946637) B946637
theorem B631107 : Blo 630300 631107 := bstep (se 1 (by rfl) ⟨473330, by rfl⟩ : syracuseStep 631107 = 946661) B946661
theorem B631123 : Blo 630300 631123 := bstep (se 1 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 631123 = 946685) B946685
theorem B631139 : Blo 630300 631139 := bstep (se 1 (by rfl) ⟨473354, by rfl⟩ : syracuseStep 631139 = 946709) B946709
theorem B631155 : Blo 630300 631155 := bstep (se 1 (by rfl) ⟨473366, by rfl⟩ : syracuseStep 631155 = 946733) B946733
theorem B631171 : Blo 630300 631171 := bstep (se 1 (by rfl) ⟨473378, by rfl⟩ : syracuseStep 631171 = 946757) B946757
theorem B631187 : Blo 630300 631187 := bstep (se 1 (by rfl) ⟨473390, by rfl⟩ : syracuseStep 631187 = 946781) B946781
theorem B631203 : Blo 630300 631203 := bstep (se 1 (by rfl) ⟨473402, by rfl⟩ : syracuseStep 631203 = 946805) B946805
theorem B631219 : Blo 630300 631219 := bstep (se 1 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 631219 = 946829) B946829
theorem B631235 : Blo 630300 631235 := bstep (se 1 (by rfl) ⟨473426, by rfl⟩ : syracuseStep 631235 = 946853) B946853
theorem B631251 : Blo 630300 631251 := bstep (se 1 (by rfl) ⟨473438, by rfl⟩ : syracuseStep 631251 = 946877) B946877
theorem B631267 : Blo 630300 631267 := bstep (se 1 (by rfl) ⟨473450, by rfl⟩ : syracuseStep 631267 = 946901) B946901
theorem B631283 : Blo 630300 631283 := bstep (se 1 (by rfl) ⟨473462, by rfl⟩ : syracuseStep 631283 = 946925) B946925
theorem B631299 : Blo 630300 631299 := bstep (se 1 (by rfl) ⟨473474, by rfl⟩ : syracuseStep 631299 = 946949) B946949
theorem B631315 : Blo 630300 631315 := bstep (se 1 (by rfl) ⟨473486, by rfl⟩ : syracuseStep 631315 = 946973) B946973
theorem B631331 : Blo 630300 631331 := bstep (se 1 (by rfl) ⟨473498, by rfl⟩ : syracuseStep 631331 = 946997) B946997
theorem B2138669 : Blo 630300 2138669 := bstep (se 3 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 2138669 = 802001) B802001
theorem B631347 : Blo 630300 631347 := bstep (se 1 (by rfl) ⟨473510, by rfl⟩ : syracuseStep 631347 = 947021) B947021
theorem B631363 : Blo 630300 631363 := bstep (se 1 (by rfl) ⟨473522, by rfl⟩ : syracuseStep 631363 = 947045) B947045
theorem B631379 : Blo 630300 631379 := bstep (se 1 (by rfl) ⟨473534, by rfl⟩ : syracuseStep 631379 = 947069) B947069
theorem B4792931 : Blo 630300 4792931 := bstep (se 1 (by rfl) ⟨3594698, by rfl⟩ : syracuseStep 4792931 = 7189397) B7189397
theorem B631395 : Blo 630300 631395 := bstep (se 1 (by rfl) ⟨473546, by rfl⟩ : syracuseStep 631395 = 947093) B947093
theorem B2138723 : Blo 630300 2138723 := bstep (se 1 (by rfl) ⟨1604042, by rfl⟩ : syracuseStep 2138723 = 3208085) B3208085
theorem B631411 : Blo 630300 631411 := bstep (se 1 (by rfl) ⟨473558, by rfl⟩ : syracuseStep 631411 = 947117) B947117
theorem B631427 : Blo 630300 631427 := bstep (se 1 (by rfl) ⟨473570, by rfl⟩ : syracuseStep 631427 = 947141) B947141
theorem B631443 : Blo 630300 631443 := bstep (se 1 (by rfl) ⟨473582, by rfl⟩ : syracuseStep 631443 = 947165) B947165
theorem B631459 : Blo 630300 631459 := bstep (se 1 (by rfl) ⟨473594, by rfl⟩ : syracuseStep 631459 = 947189) B947189
theorem B631475 : Blo 630300 631475 := bstep (se 1 (by rfl) ⟨473606, by rfl⟩ : syracuseStep 631475 = 947213) B947213
theorem B631491 : Blo 630300 631491 := bstep (se 1 (by rfl) ⟨473618, by rfl⟩ : syracuseStep 631491 = 947237) B947237
theorem B3842765 : Blo 630300 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B631507 : Blo 630300 631507 := bstep (se 1 (by rfl) ⟨473630, by rfl⟩ : syracuseStep 631507 = 947261) B947261
theorem B631523 : Blo 630300 631523 := bstep (se 1 (by rfl) ⟨473642, by rfl⟩ : syracuseStep 631523 = 947285) B947285
theorem B4104931 : Blo 630300 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B631539 : Blo 630300 631539 := bstep (se 1 (by rfl) ⟨473654, by rfl⟩ : syracuseStep 631539 = 947309) B947309
theorem B631555 : Blo 630300 631555 := bstep (se 1 (by rfl) ⟨473666, by rfl⟩ : syracuseStep 631555 = 947333) B947333
theorem B631571 : Blo 630300 631571 := bstep (se 1 (by rfl) ⟨473678, by rfl⟩ : syracuseStep 631571 = 947357) B947357
theorem B631587 : Blo 630300 631587 := bstep (se 1 (by rfl) ⟨473690, by rfl⟩ : syracuseStep 631587 = 947381) B947381
theorem B631603 : Blo 630300 631603 := bstep (se 1 (by rfl) ⟨473702, by rfl⟩ : syracuseStep 631603 = 947405) B947405
theorem B631619 : Blo 630300 631619 := bstep (se 1 (by rfl) ⟨473714, by rfl⟩ : syracuseStep 631619 = 947429) B947429
theorem B631635 : Blo 630300 631635 := bstep (se 1 (by rfl) ⟨473726, by rfl⟩ : syracuseStep 631635 = 947453) B947453
theorem B631651 : Blo 630300 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B2138993 : Blo 630300 2138993 := bstep (se 2 (by rfl) ⟨802122, by rfl⟩ : syracuseStep 2138993 = 1604245) B1604245
theorem B631667 : Blo 630300 631667 := bstep (se 1 (by rfl) ⟨473750, by rfl⟩ : syracuseStep 631667 = 947501) B947501
theorem B631683 : Blo 630300 631683 := bstep (se 1 (by rfl) ⟨473762, by rfl⟩ : syracuseStep 631683 = 947525) B947525
theorem B631699 : Blo 630300 631699 := bstep (se 1 (by rfl) ⟨473774, by rfl⟩ : syracuseStep 631699 = 947549) B947549
theorem B631715 : Blo 630300 631715 := bstep (se 1 (by rfl) ⟨473786, by rfl⟩ : syracuseStep 631715 = 947573) B947573
theorem B631731 : Blo 630300 631731 := bstep (se 1 (by rfl) ⟨473798, by rfl⟩ : syracuseStep 631731 = 947597) B947597
theorem B631747 : Blo 630300 631747 := bstep (se 1 (by rfl) ⟨473810, by rfl⟩ : syracuseStep 631747 = 947621) B947621
theorem B631763 : Blo 630300 631763 := bstep (se 1 (by rfl) ⟨473822, by rfl⟩ : syracuseStep 631763 = 947645) B947645
theorem B631779 : Blo 630300 631779 := bstep (se 1 (by rfl) ⟨473834, by rfl⟩ : syracuseStep 631779 = 947669) B947669
theorem B2401265 : Blo 630300 2401265 := bstep (se 2 (by rfl) ⟨900474, by rfl⟩ : syracuseStep 2401265 = 1800949) B1800949
theorem B631795 : Blo 630300 631795 := bstep (se 1 (by rfl) ⟨473846, by rfl⟩ : syracuseStep 631795 = 947693) B947693
theorem B631811 : Blo 630300 631811 := bstep (se 1 (by rfl) ⟨473858, by rfl⟩ : syracuseStep 631811 = 947717) B947717
theorem B631827 : Blo 630300 631827 := bstep (se 1 (by rfl) ⟨473870, by rfl⟩ : syracuseStep 631827 = 947741) B947741
theorem B631843 : Blo 630300 631843 := bstep (se 1 (by rfl) ⟨473882, by rfl⟩ : syracuseStep 631843 = 947765) B947765
theorem B631859 : Blo 630300 631859 := bstep (se 1 (by rfl) ⟨473894, by rfl⟩ : syracuseStep 631859 = 947789) B947789
theorem B631875 : Blo 630300 631875 := bstep (se 1 (by rfl) ⟨473906, by rfl⟩ : syracuseStep 631875 = 947813) B947813
theorem B631891 : Blo 630300 631891 := bstep (se 1 (by rfl) ⟨473918, by rfl⟩ : syracuseStep 631891 = 947837) B947837
theorem B959585 : Blo 630300 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B631907 : Blo 630300 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B631923 : Blo 630300 631923 := bstep (se 1 (by rfl) ⟨473942, by rfl⟩ : syracuseStep 631923 = 947885) B947885
theorem B631939 : Blo 630300 631939 := bstep (se 1 (by rfl) ⟨473954, by rfl⟩ : syracuseStep 631939 = 947909) B947909
theorem B631955 : Blo 630300 631955 := bstep (se 1 (by rfl) ⟨473966, by rfl⟩ : syracuseStep 631955 = 947933) B947933
theorem B631971 : Blo 630300 631971 := bstep (se 1 (by rfl) ⟨473978, by rfl⟩ : syracuseStep 631971 = 947957) B947957
theorem B2565283 : Blo 630300 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B1418417 : Blo 630300 1418417 := bstep (se 2 (by rfl) ⟨531906, by rfl⟩ : syracuseStep 1418417 = 1063813) B1063813
theorem B631987 : Blo 630300 631987 := bstep (se 1 (by rfl) ⟨473990, by rfl⟩ : syracuseStep 631987 = 947981) B947981
theorem B1418435 : Blo 630300 1418435 := bstep (se 1 (by rfl) ⟨1063826, by rfl⟩ : syracuseStep 1418435 = 2127653) B2127653
theorem B632003 : Blo 630300 632003 := bstep (se 1 (by rfl) ⟨474002, by rfl⟩ : syracuseStep 632003 = 948005) B948005
theorem B1352899 : Blo 630300 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B632019 : Blo 630300 632019 := bstep (se 1 (by rfl) ⟨474014, by rfl⟩ : syracuseStep 632019 = 948029) B948029
theorem B632035 : Blo 630300 632035 := bstep (se 1 (by rfl) ⟨474026, by rfl⟩ : syracuseStep 632035 = 948053) B948053
theorem B632051 : Blo 630300 632051 := bstep (se 1 (by rfl) ⟨474038, by rfl⟩ : syracuseStep 632051 = 948077) B948077
theorem B632067 : Blo 630300 632067 := bstep (se 1 (by rfl) ⟨474050, by rfl⟩ : syracuseStep 632067 = 948101) B948101
theorem B1713421 : Blo 630300 1713421 := bstep (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) B642533
theorem B632083 : Blo 630300 632083 := bstep (se 1 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 632083 = 948125) B948125
theorem B632099 : Blo 630300 632099 := bstep (se 1 (by rfl) ⟨474074, by rfl⟩ : syracuseStep 632099 = 948149) B948149
theorem B632115 : Blo 630300 632115 := bstep (se 1 (by rfl) ⟨474086, by rfl⟩ : syracuseStep 632115 = 948173) B948173
theorem B632131 : Blo 630300 632131 := bstep (se 1 (by rfl) ⟨474098, by rfl⟩ : syracuseStep 632131 = 948197) B948197
theorem B632147 : Blo 630300 632147 := bstep (se 1 (by rfl) ⟨474110, by rfl⟩ : syracuseStep 632147 = 948221) B948221
theorem B632163 : Blo 630300 632163 := bstep (se 1 (by rfl) ⟨474122, by rfl⟩ : syracuseStep 632163 = 948245) B948245
theorem B632179 : Blo 630300 632179 := bstep (se 1 (by rfl) ⟨474134, by rfl⟩ : syracuseStep 632179 = 948269) B948269
theorem B632195 : Blo 630300 632195 := bstep (se 1 (by rfl) ⟨474146, by rfl⟩ : syracuseStep 632195 = 948293) B948293
theorem B2139533 : Blo 630300 2139533 := bstep (se 3 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 2139533 = 802325) B802325
theorem B632211 : Blo 630300 632211 := bstep (se 1 (by rfl) ⟨474158, by rfl⟩ : syracuseStep 632211 = 948317) B948317
theorem B632227 : Blo 630300 632227 := bstep (se 1 (by rfl) ⟨474170, by rfl⟩ : syracuseStep 632227 = 948341) B948341
theorem B632243 : Blo 630300 632243 := bstep (se 1 (by rfl) ⟨474182, by rfl⟩ : syracuseStep 632243 = 948365) B948365
theorem B632259 : Blo 630300 632259 := bstep (se 1 (by rfl) ⟨474194, by rfl⟩ : syracuseStep 632259 = 948389) B948389
theorem B2139587 : Blo 630300 2139587 := bstep (se 1 (by rfl) ⟨1604690, by rfl⟩ : syracuseStep 2139587 = 3209381) B3209381
theorem B1418705 : Blo 630300 1418705 := bstep (se 2 (by rfl) ⟨532014, by rfl⟩ : syracuseStep 1418705 = 1064029) B1064029
theorem B632275 : Blo 630300 632275 := bstep (se 1 (by rfl) ⟨474206, by rfl⟩ : syracuseStep 632275 = 948413) B948413
theorem B1418723 : Blo 630300 1418723 := bstep (se 1 (by rfl) ⟨1064042, by rfl⟩ : syracuseStep 1418723 = 2128085) B2128085
theorem B632291 : Blo 630300 632291 := bstep (se 1 (by rfl) ⟨474218, by rfl⟩ : syracuseStep 632291 = 948437) B948437
theorem B632307 : Blo 630300 632307 := bstep (se 1 (by rfl) ⟨474230, by rfl⟩ : syracuseStep 632307 = 948461) B948461
theorem B632323 : Blo 630300 632323 := bstep (se 1 (by rfl) ⟨474242, by rfl⟩ : syracuseStep 632323 = 948485) B948485
theorem B632339 : Blo 630300 632339 := bstep (se 1 (by rfl) ⟨474254, by rfl⟩ : syracuseStep 632339 = 948509) B948509
theorem B632355 : Blo 630300 632355 := bstep (se 1 (by rfl) ⟨474266, by rfl⟩ : syracuseStep 632355 = 948533) B948533
theorem B632371 : Blo 630300 632371 := bstep (se 1 (by rfl) ⟨474278, by rfl⟩ : syracuseStep 632371 = 948557) B948557
theorem B632387 : Blo 630300 632387 := bstep (se 1 (by rfl) ⟨474290, by rfl⟩ : syracuseStep 632387 = 948581) B948581
theorem B632403 : Blo 630300 632403 := bstep (se 1 (by rfl) ⟨474302, by rfl⟩ : syracuseStep 632403 = 948605) B948605
theorem B632419 : Blo 630300 632419 := bstep (se 1 (by rfl) ⟨474314, by rfl⟩ : syracuseStep 632419 = 948629) B948629
theorem B632435 : Blo 630300 632435 := bstep (se 1 (by rfl) ⟨474326, by rfl⟩ : syracuseStep 632435 = 948653) B948653
theorem B632451 : Blo 630300 632451 := bstep (se 1 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 632451 = 948677) B948677
theorem B2401933 : Blo 630300 2401933 := bstep (se 3 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 2401933 = 900725) B900725
theorem B1353361 : Blo 630300 1353361 := bstep (se 2 (by rfl) ⟨507510, by rfl⟩ : syracuseStep 1353361 = 1015021) B1015021
theorem B632467 : Blo 630300 632467 := bstep (se 1 (by rfl) ⟨474350, by rfl⟩ : syracuseStep 632467 = 948701) B948701
theorem B632483 : Blo 630300 632483 := bstep (se 1 (by rfl) ⟨474362, by rfl⟩ : syracuseStep 632483 = 948725) B948725
theorem B632499 : Blo 630300 632499 := bstep (se 1 (by rfl) ⟨474374, by rfl⟩ : syracuseStep 632499 = 948749) B948749
theorem B632515 : Blo 630300 632515 := bstep (se 1 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 632515 = 948773) B948773
theorem B2139857 : Blo 630300 2139857 := bstep (se 2 (by rfl) ⟨802446, by rfl⟩ : syracuseStep 2139857 = 1604893) B1604893
theorem B632531 : Blo 630300 632531 := bstep (se 1 (by rfl) ⟨474398, by rfl⟩ : syracuseStep 632531 = 948797) B948797
theorem B632547 : Blo 630300 632547 := bstep (se 1 (by rfl) ⟨474410, by rfl⟩ : syracuseStep 632547 = 948821) B948821
theorem B1418993 : Blo 630300 1418993 := bstep (se 2 (by rfl) ⟨532122, by rfl⟩ : syracuseStep 1418993 = 1064245) B1064245
theorem B632563 : Blo 630300 632563 := bstep (se 1 (by rfl) ⟨474422, by rfl⟩ : syracuseStep 632563 = 948845) B948845
theorem B1419011 : Blo 630300 1419011 := bstep (se 1 (by rfl) ⟨1064258, by rfl⟩ : syracuseStep 1419011 = 2128517) B2128517
theorem B632579 : Blo 630300 632579 := bstep (se 1 (by rfl) ⟨474434, by rfl⟩ : syracuseStep 632579 = 948869) B948869
theorem B632595 : Blo 630300 632595 := bstep (se 1 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 632595 = 948893) B948893
theorem B632611 : Blo 630300 632611 := bstep (se 1 (by rfl) ⟨474458, by rfl⟩ : syracuseStep 632611 = 948917) B948917
theorem B632627 : Blo 630300 632627 := bstep (se 1 (by rfl) ⟨474470, by rfl⟩ : syracuseStep 632627 = 948941) B948941
theorem B632643 : Blo 630300 632643 := bstep (se 1 (by rfl) ⟨474482, by rfl⟩ : syracuseStep 632643 = 948965) B948965
theorem B632659 : Blo 630300 632659 := bstep (se 1 (by rfl) ⟨474494, by rfl⟩ : syracuseStep 632659 = 948989) B948989
theorem B632675 : Blo 630300 632675 := bstep (se 1 (by rfl) ⟨474506, by rfl⟩ : syracuseStep 632675 = 949013) B949013
theorem B632691 : Blo 630300 632691 := bstep (se 1 (by rfl) ⟨474518, by rfl⟩ : syracuseStep 632691 = 949037) B949037
theorem B632707 : Blo 630300 632707 := bstep (se 1 (by rfl) ⟨474530, by rfl⟩ : syracuseStep 632707 = 949061) B949061
theorem B1648529 : Blo 630300 1648529 := bstep (se 2 (by rfl) ⟨618198, by rfl⟩ : syracuseStep 1648529 = 1236397) B1236397
theorem B632723 : Blo 630300 632723 := bstep (se 1 (by rfl) ⟨474542, by rfl⟩ : syracuseStep 632723 = 949085) B949085
theorem B632739 : Blo 630300 632739 := bstep (se 1 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 632739 = 949109) B949109
theorem B632755 : Blo 630300 632755 := bstep (se 1 (by rfl) ⟨474566, by rfl⟩ : syracuseStep 632755 = 949133) B949133
theorem B632771 : Blo 630300 632771 := bstep (se 1 (by rfl) ⟨474578, by rfl⟩ : syracuseStep 632771 = 949157) B949157
theorem B632787 : Blo 630300 632787 := bstep (se 1 (by rfl) ⟨474590, by rfl⟩ : syracuseStep 632787 = 949181) B949181
theorem B632803 : Blo 630300 632803 := bstep (se 1 (by rfl) ⟨474602, by rfl⟩ : syracuseStep 632803 = 949205) B949205
theorem B632819 : Blo 630300 632819 := bstep (se 1 (by rfl) ⟨474614, by rfl⟩ : syracuseStep 632819 = 949229) B949229
theorem B632835 : Blo 630300 632835 := bstep (se 1 (by rfl) ⟨474626, by rfl⟩ : syracuseStep 632835 = 949253) B949253
theorem B1419281 : Blo 630300 1419281 := bstep (se 2 (by rfl) ⟨532230, by rfl⟩ : syracuseStep 1419281 = 1064461) B1064461
theorem B632851 : Blo 630300 632851 := bstep (se 1 (by rfl) ⟨474638, by rfl⟩ : syracuseStep 632851 = 949277) B949277
theorem B1419299 : Blo 630300 1419299 := bstep (se 1 (by rfl) ⟨1064474, by rfl⟩ : syracuseStep 1419299 = 2128949) B2128949
theorem B632867 : Blo 630300 632867 := bstep (se 1 (by rfl) ⟨474650, by rfl⟩ : syracuseStep 632867 = 949301) B949301
theorem B632883 : Blo 630300 632883 := bstep (se 1 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 632883 = 949325) B949325
theorem B632899 : Blo 630300 632899 := bstep (se 1 (by rfl) ⟨474674, by rfl⟩ : syracuseStep 632899 = 949349) B949349
theorem B632915 : Blo 630300 632915 := bstep (se 1 (by rfl) ⟨474686, by rfl⟩ : syracuseStep 632915 = 949373) B949373
theorem B632931 : Blo 630300 632931 := bstep (se 1 (by rfl) ⟨474698, by rfl⟩ : syracuseStep 632931 = 949397) B949397
theorem B26683505 : Blo 630300 26683505 := bstep (se 2 (by rfl) ⟨10006314, by rfl⟩ : syracuseStep 26683505 = 20012629) B20012629
theorem B632947 : Blo 630300 632947 := bstep (se 1 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 632947 = 949421) B949421
theorem B632963 : Blo 630300 632963 := bstep (se 1 (by rfl) ⟨474722, by rfl⟩ : syracuseStep 632963 = 949445) B949445
theorem B632979 : Blo 630300 632979 := bstep (se 1 (by rfl) ⟨474734, by rfl⟩ : syracuseStep 632979 = 949469) B949469
theorem B632995 : Blo 630300 632995 := bstep (se 1 (by rfl) ⟨474746, by rfl⟩ : syracuseStep 632995 = 949493) B949493
theorem B633011 : Blo 630300 633011 := bstep (se 1 (by rfl) ⟨474758, by rfl⟩ : syracuseStep 633011 = 949517) B949517
theorem B633027 : Blo 630300 633027 := bstep (se 1 (by rfl) ⟨474770, by rfl⟩ : syracuseStep 633027 = 949541) B949541
theorem B633043 : Blo 630300 633043 := bstep (se 1 (by rfl) ⟨474782, by rfl⟩ : syracuseStep 633043 = 949565) B949565
theorem B633059 : Blo 630300 633059 := bstep (se 1 (by rfl) ⟨474794, by rfl⟩ : syracuseStep 633059 = 949589) B949589
theorem B2140397 : Blo 630300 2140397 := bstep (se 3 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 2140397 = 802649) B802649
theorem B633075 : Blo 630300 633075 := bstep (se 1 (by rfl) ⟨474806, by rfl⟩ : syracuseStep 633075 = 949613) B949613
theorem B633091 : Blo 630300 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B633107 : Blo 630300 633107 := bstep (se 1 (by rfl) ⟨474830, by rfl⟩ : syracuseStep 633107 = 949661) B949661
theorem B633123 : Blo 630300 633123 := bstep (se 1 (by rfl) ⟨474842, by rfl⟩ : syracuseStep 633123 = 949685) B949685
theorem B2140451 : Blo 630300 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B1419569 : Blo 630300 1419569 := bstep (se 2 (by rfl) ⟨532338, by rfl⟩ : syracuseStep 1419569 = 1064677) B1064677
theorem B1648945 : Blo 630300 1648945 := bstep (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) B1236709
theorem B633139 : Blo 630300 633139 := bstep (se 1 (by rfl) ⟨474854, by rfl⟩ : syracuseStep 633139 = 949709) B949709
theorem B1419587 : Blo 630300 1419587 := bstep (se 1 (by rfl) ⟨1064690, by rfl⟩ : syracuseStep 1419587 = 2129381) B2129381
theorem B633155 : Blo 630300 633155 := bstep (se 1 (by rfl) ⟨474866, by rfl⟩ : syracuseStep 633155 = 949733) B949733
theorem B633171 : Blo 630300 633171 := bstep (se 1 (by rfl) ⟨474878, by rfl⟩ : syracuseStep 633171 = 949757) B949757
theorem B633187 : Blo 630300 633187 := bstep (se 1 (by rfl) ⟨474890, by rfl⟩ : syracuseStep 633187 = 949781) B949781
theorem B2566513 : Blo 630300 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B8235377 : Blo 630300 8235377 := bstep (se 2 (by rfl) ⟨3088266, by rfl⟩ : syracuseStep 8235377 = 6176533) B6176533
theorem B633203 : Blo 630300 633203 := bstep (se 1 (by rfl) ⟨474902, by rfl⟩ : syracuseStep 633203 = 949805) B949805
theorem B633219 : Blo 630300 633219 := bstep (se 1 (by rfl) ⟨474914, by rfl⟩ : syracuseStep 633219 = 949829) B949829
theorem B633235 : Blo 630300 633235 := bstep (se 1 (by rfl) ⟨474926, by rfl⟩ : syracuseStep 633235 = 949853) B949853
theorem B2402723 : Blo 630300 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B633251 : Blo 630300 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B633267 : Blo 630300 633267 := bstep (se 1 (by rfl) ⟨474950, by rfl⟩ : syracuseStep 633267 = 949901) B949901
theorem B633283 : Blo 630300 633283 := bstep (se 1 (by rfl) ⟨474962, by rfl⟩ : syracuseStep 633283 = 949925) B949925
theorem B633299 : Blo 630300 633299 := bstep (se 1 (by rfl) ⟨474974, by rfl⟩ : syracuseStep 633299 = 949949) B949949
theorem B633315 : Blo 630300 633315 := bstep (se 1 (by rfl) ⟨474986, by rfl⟩ : syracuseStep 633315 = 949973) B949973
theorem B633331 : Blo 630300 633331 := bstep (se 1 (by rfl) ⟨474998, by rfl⟩ : syracuseStep 633331 = 949997) B949997
theorem B633347 : Blo 630300 633347 := bstep (se 1 (by rfl) ⟨475010, by rfl⟩ : syracuseStep 633347 = 950021) B950021
theorem B633363 : Blo 630300 633363 := bstep (se 1 (by rfl) ⟨475022, by rfl⟩ : syracuseStep 633363 = 950045) B950045
theorem B633379 : Blo 630300 633379 := bstep (se 1 (by rfl) ⟨475034, by rfl⟩ : syracuseStep 633379 = 950069) B950069
theorem B2140721 : Blo 630300 2140721 := bstep (se 2 (by rfl) ⟨802770, by rfl⟩ : syracuseStep 2140721 = 1605541) B1605541
theorem B633395 : Blo 630300 633395 := bstep (se 1 (by rfl) ⟨475046, by rfl⟩ : syracuseStep 633395 = 950093) B950093
theorem B633411 : Blo 630300 633411 := bstep (se 1 (by rfl) ⟨475058, by rfl⟩ : syracuseStep 633411 = 950117) B950117
theorem B1944145 : Blo 630300 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B1419857 : Blo 630300 1419857 := bstep (se 2 (by rfl) ⟨532446, by rfl⟩ : syracuseStep 1419857 = 1064893) B1064893
theorem B633427 : Blo 630300 633427 := bstep (se 1 (by rfl) ⟨475070, by rfl⟩ : syracuseStep 633427 = 950141) B950141
theorem B1419875 : Blo 630300 1419875 := bstep (se 1 (by rfl) ⟨1064906, by rfl⟩ : syracuseStep 1419875 = 2129813) B2129813
theorem B633443 : Blo 630300 633443 := bstep (se 1 (by rfl) ⟨475082, by rfl⟩ : syracuseStep 633443 = 950165) B950165
theorem B633459 : Blo 630300 633459 := bstep (se 1 (by rfl) ⟨475094, by rfl⟩ : syracuseStep 633459 = 950189) B950189
theorem B633475 : Blo 630300 633475 := bstep (se 1 (by rfl) ⟨475106, by rfl⟩ : syracuseStep 633475 = 950213) B950213
theorem B633491 : Blo 630300 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B633507 : Blo 630300 633507 := bstep (se 1 (by rfl) ⟨475130, by rfl⟩ : syracuseStep 633507 = 950261) B950261
theorem B1354403 : Blo 630300 1354403 := bstep (se 1 (by rfl) ⟨1015802, by rfl⟩ : syracuseStep 1354403 = 2031605) B2031605
theorem B633523 : Blo 630300 633523 := bstep (se 1 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 633523 = 950285) B950285
theorem B633539 : Blo 630300 633539 := bstep (se 1 (by rfl) ⟨475154, by rfl⟩ : syracuseStep 633539 = 950309) B950309
theorem B633555 : Blo 630300 633555 := bstep (se 1 (by rfl) ⟨475166, by rfl⟩ : syracuseStep 633555 = 950333) B950333
theorem B633571 : Blo 630300 633571 := bstep (se 1 (by rfl) ⟨475178, by rfl⟩ : syracuseStep 633571 = 950357) B950357
theorem B633587 : Blo 630300 633587 := bstep (se 1 (by rfl) ⟨475190, by rfl⟩ : syracuseStep 633587 = 950381) B950381
theorem B633603 : Blo 630300 633603 := bstep (se 1 (by rfl) ⟨475202, by rfl⟩ : syracuseStep 633603 = 950405) B950405
theorem B633619 : Blo 630300 633619 := bstep (se 1 (by rfl) ⟨475214, by rfl⟩ : syracuseStep 633619 = 950429) B950429
theorem B633635 : Blo 630300 633635 := bstep (se 1 (by rfl) ⟨475226, by rfl⟩ : syracuseStep 633635 = 950453) B950453
theorem B633651 : Blo 630300 633651 := bstep (se 1 (by rfl) ⟨475238, by rfl⟩ : syracuseStep 633651 = 950477) B950477
theorem B633667 : Blo 630300 633667 := bstep (se 1 (by rfl) ⟨475250, by rfl⟩ : syracuseStep 633667 = 950501) B950501
theorem B3418949 : Blo 630300 3418949 := bstep (se 4 (by rfl) ⟨320526, by rfl⟩ : syracuseStep 3418949 = 641053) B641053
theorem B633683 : Blo 630300 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B633699 : Blo 630300 633699 := bstep (se 1 (by rfl) ⟨475274, by rfl⟩ : syracuseStep 633699 = 950549) B950549
theorem B1420145 : Blo 630300 1420145 := bstep (se 2 (by rfl) ⟨532554, by rfl⟩ : syracuseStep 1420145 = 1065109) B1065109
theorem B633715 : Blo 630300 633715 := bstep (se 1 (by rfl) ⟨475286, by rfl⟩ : syracuseStep 633715 = 950573) B950573
theorem B1420163 : Blo 630300 1420163 := bstep (se 1 (by rfl) ⟨1065122, by rfl⟩ : syracuseStep 1420163 = 2130245) B2130245
theorem B633731 : Blo 630300 633731 := bstep (se 1 (by rfl) ⟨475298, by rfl⟩ : syracuseStep 633731 = 950597) B950597
theorem B633747 : Blo 630300 633747 := bstep (se 1 (by rfl) ⟨475310, by rfl⟩ : syracuseStep 633747 = 950621) B950621
theorem B633763 : Blo 630300 633763 := bstep (se 1 (by rfl) ⟨475322, by rfl⟩ : syracuseStep 633763 = 950645) B950645
theorem B633779 : Blo 630300 633779 := bstep (se 1 (by rfl) ⟨475334, by rfl⟩ : syracuseStep 633779 = 950669) B950669
theorem B633795 : Blo 630300 633795 := bstep (se 1 (by rfl) ⟨475346, by rfl⟩ : syracuseStep 633795 = 950693) B950693
theorem B633811 : Blo 630300 633811 := bstep (se 1 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 633811 = 950717) B950717
theorem B2698211 : Blo 630300 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B633827 : Blo 630300 633827 := bstep (se 1 (by rfl) ⟨475370, by rfl⟩ : syracuseStep 633827 = 950741) B950741
theorem B633843 : Blo 630300 633843 := bstep (se 1 (by rfl) ⟨475382, by rfl⟩ : syracuseStep 633843 = 950765) B950765
theorem B633859 : Blo 630300 633859 := bstep (se 1 (by rfl) ⟨475394, by rfl⟩ : syracuseStep 633859 = 950789) B950789
theorem B633875 : Blo 630300 633875 := bstep (se 1 (by rfl) ⟨475406, by rfl⟩ : syracuseStep 633875 = 950813) B950813
theorem B633891 : Blo 630300 633891 := bstep (se 1 (by rfl) ⟨475418, by rfl⟩ : syracuseStep 633891 = 950837) B950837
theorem B2403377 : Blo 630300 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B633907 : Blo 630300 633907 := bstep (se 1 (by rfl) ⟨475430, by rfl⟩ : syracuseStep 633907 = 950861) B950861
theorem B1518659 : Blo 630300 1518659 := bstep (se 1 (by rfl) ⟨1138994, by rfl⟩ : syracuseStep 1518659 = 2277989) B2277989
theorem B633923 : Blo 630300 633923 := bstep (se 1 (by rfl) ⟨475442, by rfl⟩ : syracuseStep 633923 = 950885) B950885
theorem B797779 : Blo 630300 797779 := bstep (se 1 (by rfl) ⟨598334, by rfl⟩ : syracuseStep 797779 = 1196669) B1196669
theorem B633939 : Blo 630300 633939 := bstep (se 1 (by rfl) ⟨475454, by rfl⟩ : syracuseStep 633939 = 950909) B950909
theorem B633955 : Blo 630300 633955 := bstep (se 1 (by rfl) ⟨475466, by rfl⟩ : syracuseStep 633955 = 950933) B950933
theorem B633971 : Blo 630300 633971 := bstep (se 1 (by rfl) ⟨475478, by rfl⟩ : syracuseStep 633971 = 950957) B950957
theorem B633987 : Blo 630300 633987 := bstep (se 1 (by rfl) ⟨475490, by rfl⟩ : syracuseStep 633987 = 950981) B950981
theorem B1420433 : Blo 630300 1420433 := bstep (se 2 (by rfl) ⟨532662, by rfl⟩ : syracuseStep 1420433 = 1065325) B1065325
theorem B634003 : Blo 630300 634003 := bstep (se 1 (by rfl) ⟨475502, by rfl⟩ : syracuseStep 634003 = 951005) B951005
theorem B1420451 : Blo 630300 1420451 := bstep (se 1 (by rfl) ⟨1065338, by rfl⟩ : syracuseStep 1420451 = 2130677) B2130677
theorem B634019 : Blo 630300 634019 := bstep (se 1 (by rfl) ⟨475514, by rfl⟩ : syracuseStep 634019 = 951029) B951029
theorem B634035 : Blo 630300 634035 := bstep (se 1 (by rfl) ⟨475526, by rfl⟩ : syracuseStep 634035 = 951053) B951053
theorem B634051 : Blo 630300 634051 := bstep (se 1 (by rfl) ⟨475538, by rfl⟩ : syracuseStep 634051 = 951077) B951077
theorem B634067 : Blo 630300 634067 := bstep (se 1 (by rfl) ⟨475550, by rfl⟩ : syracuseStep 634067 = 951101) B951101
theorem B634083 : Blo 630300 634083 := bstep (se 1 (by rfl) ⟨475562, by rfl⟩ : syracuseStep 634083 = 951125) B951125
theorem B634099 : Blo 630300 634099 := bstep (se 1 (by rfl) ⟨475574, by rfl⟩ : syracuseStep 634099 = 951149) B951149
theorem B634115 : Blo 630300 634115 := bstep (se 1 (by rfl) ⟨475586, by rfl⟩ : syracuseStep 634115 = 951173) B951173
theorem B634131 : Blo 630300 634131 := bstep (se 1 (by rfl) ⟨475598, by rfl⟩ : syracuseStep 634131 = 951197) B951197
theorem B634147 : Blo 630300 634147 := bstep (se 1 (by rfl) ⟨475610, by rfl⟩ : syracuseStep 634147 = 951221) B951221
theorem B634163 : Blo 630300 634163 := bstep (se 1 (by rfl) ⟨475622, by rfl⟩ : syracuseStep 634163 = 951245) B951245
theorem B634179 : Blo 630300 634179 := bstep (se 1 (by rfl) ⟨475634, by rfl⟩ : syracuseStep 634179 = 951269) B951269
theorem B634195 : Blo 630300 634195 := bstep (se 1 (by rfl) ⟨475646, by rfl⟩ : syracuseStep 634195 = 951293) B951293
theorem B634211 : Blo 630300 634211 := bstep (se 1 (by rfl) ⟨475658, by rfl⟩ : syracuseStep 634211 = 951317) B951317
theorem B634227 : Blo 630300 634227 := bstep (se 1 (by rfl) ⟨475670, by rfl⟩ : syracuseStep 634227 = 951341) B951341
theorem B634243 : Blo 630300 634243 := bstep (se 1 (by rfl) ⟨475682, by rfl⟩ : syracuseStep 634243 = 951365) B951365
theorem B2436493 : Blo 630300 2436493 := bstep (se 3 (by rfl) ⟨456842, by rfl⟩ : syracuseStep 2436493 = 913685) B913685
theorem B634259 : Blo 630300 634259 := bstep (se 1 (by rfl) ⟨475694, by rfl⟩ : syracuseStep 634259 = 951389) B951389
theorem B634275 : Blo 630300 634275 := bstep (se 1 (by rfl) ⟨475706, by rfl⟩ : syracuseStep 634275 = 951413) B951413
theorem B1420721 : Blo 630300 1420721 := bstep (se 2 (by rfl) ⟨532770, by rfl⟩ : syracuseStep 1420721 = 1065541) B1065541
theorem B634291 : Blo 630300 634291 := bstep (se 1 (by rfl) ⟨475718, by rfl⟩ : syracuseStep 634291 = 951437) B951437
theorem B1420739 : Blo 630300 1420739 := bstep (se 1 (by rfl) ⟨1065554, by rfl⟩ : syracuseStep 1420739 = 2131109) B2131109
theorem B7187939 : Blo 630300 7187939 := bstep (se 1 (by rfl) ⟨5390954, by rfl⟩ : syracuseStep 7187939 = 10781909) B10781909
theorem B798275 : Blo 630300 798275 := bstep (se 1 (by rfl) ⟨598706, by rfl⟩ : syracuseStep 798275 = 1197413) B1197413
theorem B1421009 : Blo 630300 1421009 := bstep (se 2 (by rfl) ⟨532878, by rfl⟩ : syracuseStep 1421009 = 1065757) B1065757
theorem B1421027 : Blo 630300 1421027 := bstep (se 1 (by rfl) ⟨1065770, by rfl⟩ : syracuseStep 1421027 = 2131541) B2131541
theorem B1519505 : Blo 630300 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B1421297 : Blo 630300 1421297 := bstep (se 2 (by rfl) ⟨532986, by rfl⟩ : syracuseStep 1421297 = 1065973) B1065973
theorem B1421315 : Blo 630300 1421315 := bstep (se 1 (by rfl) ⟨1065986, by rfl⟩ : syracuseStep 1421315 = 2131973) B2131973
theorem B798979 : Blo 630300 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B1421585 : Blo 630300 1421585 := bstep (se 2 (by rfl) ⟨533094, by rfl⟩ : syracuseStep 1421585 = 1066189) B1066189
theorem B3191075 : Blo 630300 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B1421603 : Blo 630300 1421603 := bstep (se 1 (by rfl) ⟨1066202, by rfl⟩ : syracuseStep 1421603 = 2132405) B2132405
theorem B799075 : Blo 630300 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B7287221 : Blo 630300 7287221 := bstep (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) B683177
theorem B2404835 : Blo 630300 2404835 := bstep (se 1 (by rfl) ⟨1803626, by rfl⟩ : syracuseStep 2404835 = 3607253) B3607253
theorem B2404849 : Blo 630300 2404849 := bstep (se 2 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 2404849 = 1803637) B1803637
theorem B1421873 : Blo 630300 1421873 := bstep (se 2 (by rfl) ⟨533202, by rfl⟩ : syracuseStep 1421873 = 1066405) B1066405
theorem B1421891 : Blo 630300 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B897809 : Blo 630300 897809 := bstep (se 2 (by rfl) ⟨336678, by rfl⟩ : syracuseStep 897809 = 673357) B673357
theorem B44970773 : Blo 630300 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B1422161 : Blo 630300 1422161 := bstep (se 2 (by rfl) ⟨533310, by rfl⟩ : syracuseStep 1422161 = 1066621) B1066621
theorem B799571 : Blo 630300 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B1618787 : Blo 630300 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B1422179 : Blo 630300 1422179 := bstep (se 1 (by rfl) ⟨1066634, by rfl⟩ : syracuseStep 1422179 = 2133269) B2133269
theorem B897923 : Blo 630300 897923 := bstep (se 1 (by rfl) ⟨673442, by rfl⟩ : syracuseStep 897923 = 1346885) B1346885
theorem B898003 : Blo 630300 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B3191885 : Blo 630300 3191885 := bstep (se 3 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 3191885 = 1196957) B1196957
theorem B1422449 : Blo 630300 1422449 := bstep (se 2 (by rfl) ⟨533418, by rfl⟩ : syracuseStep 1422449 = 1066837) B1066837
theorem B1422467 : Blo 630300 1422467 := bstep (se 1 (by rfl) ⟨1066850, by rfl⟩ : syracuseStep 1422467 = 2133701) B2133701
theorem B1848685 : Blo 630300 1848685 := bstep (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) B693257
theorem B1422737 : Blo 630300 1422737 := bstep (se 2 (by rfl) ⟨533526, by rfl⟩ : syracuseStep 1422737 = 1067053) B1067053
theorem B1422755 : Blo 630300 1422755 := bstep (se 1 (by rfl) ⟨1067066, by rfl⟩ : syracuseStep 1422755 = 2134133) B2134133
theorem B898561 : Blo 630300 898561 := bstep (se 2 (by rfl) ⟨336960, by rfl⟩ : syracuseStep 898561 = 673921) B673921
theorem B800275 : Blo 630300 800275 := bstep (se 1 (by rfl) ⟨600206, by rfl⟩ : syracuseStep 800275 = 1200413) B1200413
theorem B2700877 : Blo 630300 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B800371 : Blo 630300 800371 := bstep (se 1 (by rfl) ⟨600278, by rfl⟩ : syracuseStep 800371 = 1200557) B1200557
theorem B964243 : Blo 630300 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B1423025 : Blo 630300 1423025 := bstep (se 2 (by rfl) ⟨533634, by rfl⟩ : syracuseStep 1423025 = 1067269) B1067269
theorem B1423043 : Blo 630300 1423043 := bstep (se 1 (by rfl) ⟨1067282, by rfl⟩ : syracuseStep 1423043 = 2134565) B2134565
theorem B7812877 : Blo 630300 7812877 := bstep (se 3 (by rfl) ⟨1464914, by rfl⟩ : syracuseStep 7812877 = 2929829) B2929829
theorem B4798277 : Blo 630300 4798277 := bstep (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) B899677
theorem B3028877 : Blo 630300 3028877 := bstep (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) B1135829
theorem B2406307 : Blo 630300 2406307 := bstep (se 1 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 2406307 = 3609461) B3609461
theorem B2570147 : Blo 630300 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B1423313 : Blo 630300 1423313 := bstep (se 2 (by rfl) ⟨533742, by rfl⟩ : syracuseStep 1423313 = 1067485) B1067485
theorem B1423331 : Blo 630300 1423331 := bstep (se 1 (by rfl) ⟨1067498, by rfl⟩ : syracuseStep 1423331 = 2134997) B2134997
theorem B800867 : Blo 630300 800867 := bstep (se 1 (by rfl) ⟨600650, by rfl⟩ : syracuseStep 800867 = 1201301) B1201301
theorem B899267 : Blo 630300 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B1423601 : Blo 630300 1423601 := bstep (se 2 (by rfl) ⟨533850, by rfl⟩ : syracuseStep 1423601 = 1067701) B1067701
theorem B1423619 : Blo 630300 1423619 := bstep (se 1 (by rfl) ⟨1067714, by rfl⟩ : syracuseStep 1423619 = 2135429) B2135429
theorem B1522147 : Blo 630300 1522147 := bstep (se 1 (by rfl) ⟨1141610, by rfl⟩ : syracuseStep 1522147 = 2283221) B2283221
theorem B1423889 : Blo 630300 1423889 := bstep (se 2 (by rfl) ⟨533958, by rfl⟩ : syracuseStep 1423889 = 1067917) B1067917
theorem B1423907 : Blo 630300 1423907 := bstep (se 1 (by rfl) ⟨1067930, by rfl⟩ : syracuseStep 1423907 = 2135861) B2135861
theorem B1522243 : Blo 630300 1522243 := bstep (se 1 (by rfl) ⟨1141682, by rfl⟩ : syracuseStep 1522243 = 2283365) B2283365
theorem B2701937 : Blo 630300 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B3029645 : Blo 630300 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B1063651 : Blo 630300 1063651 := bstep (se 1 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 1063651 = 1595477) B1595477
theorem B1522435 : Blo 630300 1522435 := bstep (se 1 (by rfl) ⟨1141826, by rfl⟩ : syracuseStep 1522435 = 2283653) B2283653
theorem B801571 : Blo 630300 801571 := bstep (se 1 (by rfl) ⟨601178, by rfl⟩ : syracuseStep 801571 = 1202357) B1202357
theorem B1424177 : Blo 630300 1424177 := bstep (se 2 (by rfl) ⟨534066, by rfl⟩ : syracuseStep 1424177 = 1068133) B1068133
theorem B899905 : Blo 630300 899905 := bstep (se 2 (by rfl) ⟨337464, by rfl⟩ : syracuseStep 899905 = 674929) B674929
theorem B1424195 : Blo 630300 1424195 := bstep (se 1 (by rfl) ⟨1068146, by rfl⟩ : syracuseStep 1424195 = 2136293) B2136293
theorem B1063793 : Blo 630300 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B801667 : Blo 630300 801667 := bstep (se 1 (by rfl) ⟨601250, by rfl⟩ : syracuseStep 801667 = 1202501) B1202501
theorem B900019 : Blo 630300 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B1063921 : Blo 630300 1063921 := bstep (se 2 (by rfl) ⟨398970, by rfl⟩ : syracuseStep 1063921 = 797941) B797941
theorem B1063955 : Blo 630300 1063955 := bstep (se 1 (by rfl) ⟨797966, by rfl⟩ : syracuseStep 1063955 = 1595933) B1595933
theorem B4045859 : Blo 630300 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B2276387 : Blo 630300 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B703523 : Blo 630300 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B7224389 : Blo 630300 7224389 := bstep (se 4 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 7224389 = 1354573) B1354573
theorem B1424465 : Blo 630300 1424465 := bstep (se 2 (by rfl) ⟨534174, by rfl⟩ : syracuseStep 1424465 = 1068349) B1068349
theorem B1424483 : Blo 630300 1424483 := bstep (se 1 (by rfl) ⟨1068362, by rfl⟩ : syracuseStep 1424483 = 2136725) B2136725
theorem B1064083 : Blo 630300 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B1064225 : Blo 630300 1064225 := bstep (se 2 (by rfl) ⟨399084, by rfl⟩ : syracuseStep 1064225 = 798169) B798169
theorem B1424753 : Blo 630300 1424753 := bstep (se 2 (by rfl) ⟨534282, by rfl⟩ : syracuseStep 1424753 = 1068565) B1068565
theorem B802163 : Blo 630300 802163 := bstep (se 1 (by rfl) ⟨601622, by rfl⟩ : syracuseStep 802163 = 1203245) B1203245
theorem B1424771 : Blo 630300 1424771 := bstep (se 1 (by rfl) ⟨1068578, by rfl⟩ : syracuseStep 1424771 = 2137157) B2137157
theorem B1064353 : Blo 630300 1064353 := bstep (se 2 (by rfl) ⟨399132, by rfl⟩ : syracuseStep 1064353 = 798265) B798265
theorem B1064387 : Blo 630300 1064387 := bstep (se 1 (by rfl) ⟨798290, by rfl⟩ : syracuseStep 1064387 = 1596581) B1596581
theorem B1064515 : Blo 630300 1064515 := bstep (se 1 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 1064515 = 1596773) B1596773
theorem B1425041 : Blo 630300 1425041 := bstep (se 2 (by rfl) ⟨534390, by rfl⟩ : syracuseStep 1425041 = 1068781) B1068781
theorem B1425059 : Blo 630300 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B1523377 : Blo 630300 1523377 := bstep (se 2 (by rfl) ⟨571266, by rfl⟩ : syracuseStep 1523377 = 1142533) B1142533
theorem B1064657 : Blo 630300 1064657 := bstep (se 2 (by rfl) ⟨399246, by rfl⟩ : syracuseStep 1064657 = 798493) B798493
theorem B1064785 : Blo 630300 1064785 := bstep (se 2 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 1064785 = 798589) B798589
theorem B1064819 : Blo 630300 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B3194801 : Blo 630300 3194801 := bstep (se 2 (by rfl) ⟨1198050, by rfl⟩ : syracuseStep 3194801 = 2396101) B2396101
theorem B1425329 : Blo 630300 1425329 := bstep (se 2 (by rfl) ⟨534498, by rfl⟩ : syracuseStep 1425329 = 1068997) B1068997
theorem B1425347 : Blo 630300 1425347 := bstep (se 1 (by rfl) ⟨1069010, by rfl⟩ : syracuseStep 1425347 = 2138021) B2138021
theorem B1064947 : Blo 630300 1064947 := bstep (se 1 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 1064947 = 1597421) B1597421
theorem B802819 : Blo 630300 802819 := bstep (se 1 (by rfl) ⟨602114, by rfl⟩ : syracuseStep 802819 = 1204229) B1204229
theorem B1065089 : Blo 630300 1065089 := bstep (se 2 (by rfl) ⟨399408, by rfl⟩ : syracuseStep 1065089 = 798817) B798817
theorem B9748621 : Blo 630300 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B2277539 : Blo 630300 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B1917101 : Blo 630300 1917101 := bstep (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) B718913
theorem B1425617 : Blo 630300 1425617 := bstep (se 2 (by rfl) ⟨534606, by rfl⟩ : syracuseStep 1425617 = 1069213) B1069213
theorem B1425635 : Blo 630300 1425635 := bstep (se 1 (by rfl) ⟨1069226, by rfl⟩ : syracuseStep 1425635 = 2138453) B2138453
theorem B901363 : Blo 630300 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B1065217 : Blo 630300 1065217 := bstep (se 2 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 1065217 = 798913) B798913
theorem B1065251 : Blo 630300 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B835987 : Blo 630300 835987 := bstep (se 1 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 835987 = 1253981) B1253981
theorem B1065379 : Blo 630300 1065379 := bstep (se 1 (by rfl) ⟨799034, by rfl⟩ : syracuseStep 1065379 = 1598069) B1598069
theorem B2048465 : Blo 630300 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B5390819 : Blo 630300 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B1425905 : Blo 630300 1425905 := bstep (se 2 (by rfl) ⟨534714, by rfl⟩ : syracuseStep 1425905 = 1069429) B1069429
theorem B1425923 : Blo 630300 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B1065521 : Blo 630300 1065521 := bstep (se 2 (by rfl) ⟨399570, by rfl⟩ : syracuseStep 1065521 = 799141) B799141
theorem B1196707 : Blo 630300 1196707 := bstep (se 1 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 1196707 = 1795061) B1795061
theorem B1065649 : Blo 630300 1065649 := bstep (se 2 (by rfl) ⟨399618, by rfl⟩ : syracuseStep 1065649 = 799237) B799237
theorem B1065683 : Blo 630300 1065683 := bstep (se 1 (by rfl) ⟨799262, by rfl⟩ : syracuseStep 1065683 = 1598525) B1598525
theorem B1426193 : Blo 630300 1426193 := bstep (se 2 (by rfl) ⟨534822, by rfl⟩ : syracuseStep 1426193 = 1069645) B1069645
theorem B1426211 : Blo 630300 1426211 := bstep (se 1 (by rfl) ⟨1069658, by rfl⟩ : syracuseStep 1426211 = 2139317) B2139317
theorem B1065811 : Blo 630300 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B3457997 : Blo 630300 3457997 := bstep (se 3 (by rfl) ⟨648374, by rfl⟩ : syracuseStep 3457997 = 1296749) B1296749
theorem B1065953 : Blo 630300 1065953 := bstep (se 2 (by rfl) ⟨399732, by rfl⟩ : syracuseStep 1065953 = 799465) B799465
theorem B1426481 : Blo 630300 1426481 := bstep (se 2 (by rfl) ⟨534930, by rfl⟩ : syracuseStep 1426481 = 1069861) B1069861
theorem B1426499 : Blo 630300 1426499 := bstep (se 1 (by rfl) ⟨1069874, by rfl⟩ : syracuseStep 1426499 = 2139749) B2139749
theorem B1066081 : Blo 630300 1066081 := bstep (se 2 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 1066081 = 799561) B799561
theorem B1197155 : Blo 630300 1197155 := bstep (se 1 (by rfl) ⟨897866, by rfl⟩ : syracuseStep 1197155 = 1795733) B1795733
theorem B1066115 : Blo 630300 1066115 := bstep (se 1 (by rfl) ⟨799586, by rfl⟩ : syracuseStep 1066115 = 1599173) B1599173
theorem B2278577 : Blo 630300 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B1066243 : Blo 630300 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B1426769 : Blo 630300 1426769 := bstep (se 2 (by rfl) ⟨535038, by rfl⟩ : syracuseStep 1426769 = 1070077) B1070077
theorem B902497 : Blo 630300 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B3196259 : Blo 630300 3196259 := bstep (se 1 (by rfl) ⟨2397194, by rfl⟩ : syracuseStep 3196259 = 4794389) B4794389
theorem B1426787 : Blo 630300 1426787 := bstep (se 1 (by rfl) ⟨1070090, by rfl⟩ : syracuseStep 1426787 = 2140181) B2140181
theorem B1197443 : Blo 630300 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B1066385 : Blo 630300 1066385 := bstep (se 2 (by rfl) ⟨399894, by rfl⟩ : syracuseStep 1066385 = 799789) B799789
theorem B902593 : Blo 630300 902593 := bstep (se 2 (by rfl) ⟨338472, by rfl⟩ : syracuseStep 902593 = 676945) B676945
theorem B3851717 : Blo 630300 3851717 := bstep (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) B722197
theorem B7489037 : Blo 630300 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B2704909 : Blo 630300 2704909 := bstep (se 3 (by rfl) ⟨507170, by rfl⟩ : syracuseStep 2704909 = 1014341) B1014341
theorem B1066513 : Blo 630300 1066513 := bstep (se 2 (by rfl) ⟨399942, by rfl⟩ : syracuseStep 1066513 = 799885) B799885
theorem B1066547 : Blo 630300 1066547 := bstep (se 1 (by rfl) ⟨799910, by rfl⟩ : syracuseStep 1066547 = 1599821) B1599821
theorem B1427057 : Blo 630300 1427057 := bstep (se 2 (by rfl) ⟨535146, by rfl⟩ : syracuseStep 1427057 = 1070293) B1070293
theorem B1427075 : Blo 630300 1427075 := bstep (se 1 (by rfl) ⟨1070306, by rfl⟩ : syracuseStep 1427075 = 2140613) B2140613
theorem B1066675 : Blo 630300 1066675 := bstep (se 1 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 1066675 = 1600013) B1600013
theorem B46909205 : Blo 630300 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B1066817 : Blo 630300 1066817 := bstep (se 2 (by rfl) ⟨400056, by rfl⟩ : syracuseStep 1066817 = 800113) B800113
theorem B1296227 : Blo 630300 1296227 := bstep (se 1 (by rfl) ⟨972170, by rfl⟩ : syracuseStep 1296227 = 1944341) B1944341
theorem B2705251 : Blo 630300 2705251 := bstep (se 1 (by rfl) ⟨2028938, by rfl⟩ : syracuseStep 2705251 = 4057877) B4057877
theorem B640915 : Blo 630300 640915 := bstep (se 1 (by rfl) ⟨480686, by rfl⟩ : syracuseStep 640915 = 961373) B961373
theorem B903089 : Blo 630300 903089 := bstep (se 2 (by rfl) ⟨338658, by rfl⟩ : syracuseStep 903089 = 677317) B677317
theorem B1066945 : Blo 630300 1066945 := bstep (se 2 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 1066945 = 800209) B800209
theorem B673763 : Blo 630300 673763 := bstep (se 1 (by rfl) ⟨505322, by rfl⟩ : syracuseStep 673763 = 1010645) B1010645
theorem B1066979 : Blo 630300 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B1067107 : Blo 630300 1067107 := bstep (se 1 (by rfl) ⟨800330, by rfl⟩ : syracuseStep 1067107 = 1600661) B1600661
theorem B3197069 : Blo 630300 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B1067249 : Blo 630300 1067249 := bstep (se 2 (by rfl) ⟨400218, by rfl⟩ : syracuseStep 1067249 = 800437) B800437
theorem B1198385 : Blo 630300 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B1624369 : Blo 630300 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B1067377 : Blo 630300 1067377 := bstep (se 2 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 1067377 = 800533) B800533
theorem B1067411 : Blo 630300 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1067539 : Blo 630300 1067539 := bstep (se 1 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 1067539 = 1601309) B1601309
theorem B1919533 : Blo 630300 1919533 := bstep (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) B719825
theorem B3656305 : Blo 630300 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B1067681 : Blo 630300 1067681 := bstep (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) B800761
theorem B674515 : Blo 630300 674515 := bstep (se 1 (by rfl) ⟨505886, by rfl⟩ : syracuseStep 674515 = 1011773) B1011773
theorem B1067809 : Blo 630300 1067809 := bstep (se 2 (by rfl) ⟨400428, by rfl⟩ : syracuseStep 1067809 = 800857) B800857
theorem B1067843 : Blo 630300 1067843 := bstep (se 1 (by rfl) ⟨800882, by rfl⟩ : syracuseStep 1067843 = 1601765) B1601765
theorem B4049777 : Blo 630300 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B1919875 : Blo 630300 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B1067971 : Blo 630300 1067971 := bstep (se 1 (by rfl) ⟨800978, by rfl⟩ : syracuseStep 1067971 = 1601957) B1601957
theorem B642115 : Blo 630300 642115 := bstep (se 1 (by rfl) ⟨481586, by rfl⟩ : syracuseStep 642115 = 963173) B963173
theorem B1068113 : Blo 630300 1068113 := bstep (se 2 (by rfl) ⟨400542, by rfl⟩ : syracuseStep 1068113 = 801085) B801085
theorem B1199281 : Blo 630300 1199281 := bstep (se 2 (by rfl) ⟨449730, by rfl⟩ : syracuseStep 1199281 = 899461) B899461
theorem B1068241 : Blo 630300 1068241 := bstep (se 2 (by rfl) ⟨400590, by rfl⟩ : syracuseStep 1068241 = 801181) B801181
theorem B1068275 : Blo 630300 1068275 := bstep (se 1 (by rfl) ⟨801206, by rfl⟩ : syracuseStep 1068275 = 1602413) B1602413
theorem B1199441 : Blo 630300 1199441 := bstep (se 2 (by rfl) ⟨449790, by rfl⟩ : syracuseStep 1199441 = 899581) B899581
theorem B3460465 : Blo 630300 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B1068403 : Blo 630300 1068403 := bstep (se 1 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 1068403 = 1602605) B1602605
theorem B1068545 : Blo 630300 1068545 := bstep (se 2 (by rfl) ⟨400704, by rfl⟩ : syracuseStep 1068545 = 801409) B801409
theorem B4050445 : Blo 630300 4050445 := bstep (se 3 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 4050445 = 1518917) B1518917
theorem B4804109 : Blo 630300 4804109 := bstep (se 3 (by rfl) ⟨900770, by rfl⟩ : syracuseStep 4804109 = 1801541) B1801541
theorem B1920593 : Blo 630300 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1068673 : Blo 630300 1068673 := bstep (se 2 (by rfl) ⟨400752, by rfl⟩ : syracuseStep 1068673 = 801505) B801505
theorem B1068707 : Blo 630300 1068707 := bstep (se 1 (by rfl) ⟨801530, by rfl⟩ : syracuseStep 1068707 = 1603061) B1603061
theorem B1199843 : Blo 630300 1199843 := bstep (se 1 (by rfl) ⟨899882, by rfl⟩ : syracuseStep 1199843 = 1799765) B1799765
theorem B675587 : Blo 630300 675587 := bstep (se 1 (by rfl) ⟨506690, by rfl⟩ : syracuseStep 675587 = 1013381) B1013381
theorem B1068835 : Blo 630300 1068835 := bstep (se 1 (by rfl) ⟨801626, by rfl⟩ : syracuseStep 1068835 = 1603253) B1603253
theorem B1068977 : Blo 630300 1068977 := bstep (se 2 (by rfl) ⟨400866, by rfl⟩ : syracuseStep 1068977 = 801733) B801733
theorem B1069105 : Blo 630300 1069105 := bstep (se 2 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 1069105 = 801829) B801829
theorem B1069139 : Blo 630300 1069139 := bstep (se 1 (by rfl) ⟨801854, by rfl⟩ : syracuseStep 1069139 = 1603709) B1603709
theorem B1069267 : Blo 630300 1069267 := bstep (se 1 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 1069267 = 1603901) B1603901
theorem B1069409 : Blo 630300 1069409 := bstep (se 2 (by rfl) ⟨401028, by rfl⟩ : syracuseStep 1069409 = 802057) B802057
theorem B1069537 : Blo 630300 1069537 := bstep (se 2 (by rfl) ⟨401076, by rfl⟩ : syracuseStep 1069537 = 802153) B802153
theorem B709123 : Blo 630300 709123 := bstep (se 1 (by rfl) ⟨531842, by rfl⟩ : syracuseStep 709123 = 1063685) B1063685
theorem B1069571 : Blo 630300 1069571 := bstep (se 1 (by rfl) ⟨802178, by rfl⟩ : syracuseStep 1069571 = 1604357) B1604357
theorem B1921603 : Blo 630300 1921603 := bstep (se 1 (by rfl) ⟨1441202, by rfl⟩ : syracuseStep 1921603 = 2882405) B2882405
theorem B2019917 : Blo 630300 2019917 := bstep (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) B757469
theorem B1200739 : Blo 630300 1200739 := bstep (se 1 (by rfl) ⟨900554, by rfl⟩ : syracuseStep 1200739 = 1801109) B1801109
theorem B10965617 : Blo 630300 10965617 := bstep (se 2 (by rfl) ⟨4112106, by rfl⟩ : syracuseStep 10965617 = 8224213) B8224213
theorem B1069699 : Blo 630300 1069699 := bstep (se 1 (by rfl) ⟨802274, by rfl⟩ : syracuseStep 1069699 = 1604549) B1604549
theorem B709267 : Blo 630300 709267 := bstep (se 1 (by rfl) ⟨531950, by rfl⟩ : syracuseStep 709267 = 1063901) B1063901
theorem B10277603 : Blo 630300 10277603 := bstep (se 1 (by rfl) ⟨7708202, by rfl⟩ : syracuseStep 10277603 = 15416405) B15416405
theorem B1200899 : Blo 630300 1200899 := bstep (se 1 (by rfl) ⟨900674, by rfl⟩ : syracuseStep 1200899 = 1801349) B1801349
theorem B1069841 : Blo 630300 1069841 := bstep (se 2 (by rfl) ⟨401190, by rfl⟩ : syracuseStep 1069841 = 802381) B802381
theorem B709411 : Blo 630300 709411 := bstep (se 1 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 709411 = 1064117) B1064117
theorem B676723 : Blo 630300 676723 := bstep (se 1 (by rfl) ⟨507542, by rfl⟩ : syracuseStep 676723 = 1015085) B1015085
theorem B1823629 : Blo 630300 1823629 := bstep (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) B683861
theorem B1069969 : Blo 630300 1069969 := bstep (se 2 (by rfl) ⟨401238, by rfl⟩ : syracuseStep 1069969 = 802477) B802477
theorem B709555 : Blo 630300 709555 := bstep (se 1 (by rfl) ⟨532166, by rfl⟩ : syracuseStep 709555 = 1064333) B1064333
theorem B1070003 : Blo 630300 1070003 := bstep (se 1 (by rfl) ⟨802502, by rfl⟩ : syracuseStep 1070003 = 1605005) B1605005
theorem B3199985 : Blo 630300 3199985 := bstep (se 2 (by rfl) ⟨1199994, by rfl⟩ : syracuseStep 3199985 = 2399989) B2399989
theorem B1070131 : Blo 630300 1070131 := bstep (se 1 (by rfl) ⟨802598, by rfl⟩ : syracuseStep 1070131 = 1605197) B1605197
theorem B709699 : Blo 630300 709699 := bstep (se 1 (by rfl) ⟨532274, by rfl⟩ : syracuseStep 709699 = 1064549) B1064549
theorem B1758275 : Blo 630300 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1070273 : Blo 630300 1070273 := bstep (se 2 (by rfl) ⟨401352, by rfl⟩ : syracuseStep 1070273 = 802705) B802705
theorem B709843 : Blo 630300 709843 := bstep (se 1 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 709843 = 1064765) B1064765
theorem B1922285 : Blo 630300 1922285 := bstep (se 3 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 1922285 = 720857) B720857
theorem B709987 : Blo 630300 709987 := bstep (se 1 (by rfl) ⟨532490, by rfl⟩ : syracuseStep 709987 = 1064981) B1064981
theorem B3593605 : Blo 630300 3593605 := bstep (se 4 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 3593605 = 673801) B673801
theorem B710131 : Blo 630300 710131 := bstep (se 1 (by rfl) ⟨532598, by rfl⟩ : syracuseStep 710131 = 1065197) B1065197
theorem B1136227 : Blo 630300 1136227 := bstep (se 1 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 1136227 = 1704341) B1704341
theorem B710275 : Blo 630300 710275 := bstep (se 1 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 710275 = 1065413) B1065413
theorem B710419 : Blo 630300 710419 := bstep (se 1 (by rfl) ⟨532814, by rfl⟩ : syracuseStep 710419 = 1065629) B1065629
theorem B2709283 : Blo 630300 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B1201969 : Blo 630300 1201969 := bstep (se 2 (by rfl) ⟨450738, by rfl⟩ : syracuseStep 1201969 = 901477) B901477
theorem B710563 : Blo 630300 710563 := bstep (se 1 (by rfl) ⟨532922, by rfl⟩ : syracuseStep 710563 = 1065845) B1065845
theorem B710707 : Blo 630300 710707 := bstep (se 1 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 710707 = 1066061) B1066061
theorem B2021507 : Blo 630300 2021507 := bstep (se 1 (by rfl) ⟨1516130, by rfl⟩ : syracuseStep 2021507 = 3032261) B3032261
theorem B710851 : Blo 630300 710851 := bstep (se 1 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 710851 = 1066277) B1066277
theorem B6838499 : Blo 630300 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B2021699 : Blo 630300 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B710995 : Blo 630300 710995 := bstep (se 1 (by rfl) ⟨533246, by rfl⟩ : syracuseStep 710995 = 1066493) B1066493
theorem B4807025 : Blo 630300 4807025 := bstep (se 2 (by rfl) ⟨1802634, by rfl⟩ : syracuseStep 4807025 = 3605269) B3605269
theorem B3201443 : Blo 630300 3201443 := bstep (se 1 (by rfl) ⟨2401082, by rfl⟩ : syracuseStep 3201443 = 4802165) B4802165
theorem B711139 : Blo 630300 711139 := bstep (se 1 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 711139 = 1066709) B1066709
theorem B2284145 : Blo 630300 2284145 := bstep (se 2 (by rfl) ⟨856554, by rfl⟩ : syracuseStep 2284145 = 1713109) B1713109
theorem B711283 : Blo 630300 711283 := bstep (se 1 (by rfl) ⟨533462, by rfl⟩ : syracuseStep 711283 = 1066925) B1066925
theorem B1038995 : Blo 630300 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B1596145 : Blo 630300 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B711427 : Blo 630300 711427 := bstep (se 1 (by rfl) ⟨533570, by rfl⟩ : syracuseStep 711427 = 1067141) B1067141
theorem B973603 : Blo 630300 973603 := bstep (se 1 (by rfl) ⟨730202, by rfl⟩ : syracuseStep 973603 = 1460405) B1460405
theorem B1203025 : Blo 630300 1203025 := bstep (se 2 (by rfl) ⟨451134, by rfl⟩ : syracuseStep 1203025 = 902269) B902269
theorem B711571 : Blo 630300 711571 := bstep (se 1 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 711571 = 1067357) B1067357
theorem B2022353 : Blo 630300 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B1596419 : Blo 630300 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B711715 : Blo 630300 711715 := bstep (se 1 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 711715 = 1067573) B1067573
theorem B711859 : Blo 630300 711859 := bstep (se 1 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 711859 = 1067789) B1067789
theorem B1596611 : Blo 630300 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B14277829 : Blo 630300 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B3202253 : Blo 630300 3202253 := bstep (se 3 (by rfl) ⟨600422, by rfl⟩ : syracuseStep 3202253 = 1200845) B1200845
theorem B1203427 : Blo 630300 1203427 := bstep (se 1 (by rfl) ⟨902570, by rfl⟩ : syracuseStep 1203427 = 1805141) B1805141
theorem B1137905 : Blo 630300 1137905 := bstep (se 2 (by rfl) ⟨426714, by rfl⟩ : syracuseStep 1137905 = 853429) B853429
theorem B1203473 : Blo 630300 1203473 := bstep (se 2 (by rfl) ⟨451302, by rfl⟩ : syracuseStep 1203473 = 902605) B902605
theorem B712003 : Blo 630300 712003 := bstep (se 1 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 712003 = 1068005) B1068005
theorem B3595589 : Blo 630300 3595589 := bstep (se 4 (by rfl) ⟨337086, by rfl⟩ : syracuseStep 3595589 = 674173) B674173
theorem B3038563 : Blo 630300 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B712147 : Blo 630300 712147 := bstep (se 1 (by rfl) ⟨534110, by rfl⟩ : syracuseStep 712147 = 1068221) B1068221
theorem B1203761 : Blo 630300 1203761 := bstep (se 2 (by rfl) ⟨451410, by rfl⟩ : syracuseStep 1203761 = 902821) B902821
theorem B712291 : Blo 630300 712291 := bstep (se 1 (by rfl) ⟨534218, by rfl⟩ : syracuseStep 712291 = 1068437) B1068437
theorem B5463749 : Blo 630300 5463749 := bstep (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) B1024453
theorem B2285297 : Blo 630300 2285297 := bstep (se 2 (by rfl) ⟨856986, by rfl⟩ : syracuseStep 2285297 = 1713973) B1713973
theorem B712435 : Blo 630300 712435 := bstep (se 1 (by rfl) ⟨534326, by rfl⟩ : syracuseStep 712435 = 1068653) B1068653
theorem B712579 : Blo 630300 712579 := bstep (se 1 (by rfl) ⟨534434, by rfl⟩ : syracuseStep 712579 = 1068869) B1068869
theorem B712723 : Blo 630300 712723 := bstep (se 1 (by rfl) ⟨534542, by rfl⟩ : syracuseStep 712723 = 1069085) B1069085
theorem B1597553 : Blo 630300 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B1597603 : Blo 630300 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B712867 : Blo 630300 712867 := bstep (se 1 (by rfl) ⟨534650, by rfl⟩ : syracuseStep 712867 = 1069301) B1069301
theorem B1597745 : Blo 630300 1597745 := bstep (se 2 (by rfl) ⟨599154, by rfl⟩ : syracuseStep 1597745 = 1198309) B1198309
theorem B713011 : Blo 630300 713011 := bstep (se 1 (by rfl) ⟨534758, by rfl⟩ : syracuseStep 713011 = 1069517) B1069517
theorem B3039565 : Blo 630300 3039565 := bstep (se 3 (by rfl) ⟨569918, by rfl⟩ : syracuseStep 3039565 = 1139837) B1139837
theorem B5398883 : Blo 630300 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B811363 : Blo 630300 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B713155 : Blo 630300 713155 := bstep (se 1 (by rfl) ⟨534866, by rfl⟩ : syracuseStep 713155 = 1069733) B1069733
theorem B713299 : Blo 630300 713299 := bstep (se 1 (by rfl) ⟨534974, by rfl⟩ : syracuseStep 713299 = 1069949) B1069949
theorem B713443 : Blo 630300 713443 := bstep (se 1 (by rfl) ⟨535082, by rfl⟩ : syracuseStep 713443 = 1070165) B1070165
theorem B910163 : Blo 630300 910163 := bstep (se 1 (by rfl) ⟨682622, by rfl⟩ : syracuseStep 910163 = 1365245) B1365245
theorem B4547441 : Blo 630300 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B713587 : Blo 630300 713587 := bstep (se 1 (by rfl) ⟨535190, by rfl⟩ : syracuseStep 713587 = 1070381) B1070381
theorem B2024365 : Blo 630300 2024365 := bstep (se 3 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 2024365 = 759137) B759137
theorem B8119237 : Blo 630300 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B1795117 : Blo 630300 1795117 := bstep (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) B673169
theorem B1041523 : Blo 630300 1041523 := bstep (se 1 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 1041523 = 1562285) B1562285
theorem B1827971 : Blo 630300 1827971 := bstep (se 1 (by rfl) ⟨1370978, by rfl⟩ : syracuseStep 1827971 = 2741957) B2741957
theorem B1795277 : Blo 630300 1795277 := bstep (se 3 (by rfl) ⟨336614, by rfl⟩ : syracuseStep 1795277 = 673229) B673229
theorem B1598737 : Blo 630300 1598737 := bstep (se 2 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 1598737 = 1199053) B1199053
theorem B2024813 : Blo 630300 2024813 := bstep (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) B759305
theorem B1795459 : Blo 630300 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B1140227 : Blo 630300 1140227 := bstep (se 1 (by rfl) ⟨855170, by rfl⟩ : syracuseStep 1140227 = 1710341) B1710341
theorem B4318733 : Blo 630300 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B1599011 : Blo 630300 1599011 := bstep (se 1 (by rfl) ⟨1199258, by rfl⟩ : syracuseStep 1599011 = 2398517) B2398517
theorem B1599203 : Blo 630300 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B4056803 : Blo 630300 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B3041009 : Blo 630300 3041009 := bstep (se 2 (by rfl) ⟨1140378, by rfl⟩ : syracuseStep 3041009 = 2280757) B2280757
theorem B3205169 : Blo 630300 3205169 := bstep (se 2 (by rfl) ⟨1201938, by rfl⟩ : syracuseStep 3205169 = 2403877) B2403877
theorem B1108081 : Blo 630300 1108081 := bstep (se 2 (by rfl) ⟨415530, by rfl⟩ : syracuseStep 1108081 = 831061) B831061
theorem B1370513 : Blo 630300 1370513 := bstep (se 2 (by rfl) ⟨513942, by rfl⟩ : syracuseStep 1370513 = 1027885) B1027885
theorem B6089201 : Blo 630300 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B1141265 : Blo 630300 1141265 := bstep (se 2 (by rfl) ⟨427974, by rfl⟩ : syracuseStep 1141265 = 855949) B855949
theorem B1600145 : Blo 630300 1600145 := bstep (se 2 (by rfl) ⟨600054, by rfl⟩ : syracuseStep 1600145 = 1200109) B1200109
theorem B1010369 : Blo 630300 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B1600195 : Blo 630300 1600195 := bstep (se 1 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 1600195 = 2400293) B2400293
theorem B1796849 : Blo 630300 1796849 := bstep (se 2 (by rfl) ⟨673818, by rfl⟩ : syracuseStep 1796849 = 1347637) B1347637
theorem B1010497 : Blo 630300 1010497 := bstep (se 2 (by rfl) ⟨378936, by rfl⟩ : syracuseStep 1010497 = 757873) B757873
theorem B3337037 : Blo 630300 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1600337 : Blo 630300 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B1010561 : Blo 630300 1010561 := bstep (se 2 (by rfl) ⟨378960, by rfl⟩ : syracuseStep 1010561 = 757921) B757921
theorem B781283 : Blo 630300 781283 := bstep (se 1 (by rfl) ⟨585962, by rfl⟩ : syracuseStep 781283 = 1171925) B1171925
theorem B2157617 : Blo 630300 2157617 := bstep (se 2 (by rfl) ⟨809106, by rfl⟩ : syracuseStep 2157617 = 1618213) B1618213
theorem B3599437 : Blo 630300 3599437 := bstep (se 3 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 3599437 = 1349789) B1349789
theorem B10251461 : Blo 630300 10251461 := bstep (se 4 (by rfl) ⟨961074, by rfl⟩ : syracuseStep 10251461 = 1922149) B1922149
theorem B945473 : Blo 630300 945473 := bstep (se 2 (by rfl) ⟨354552, by rfl⟩ : syracuseStep 945473 = 709105) B709105
theorem B945491 : Blo 630300 945491 := bstep (se 1 (by rfl) ⟨709118, by rfl⟩ : syracuseStep 945491 = 1418237) B1418237
theorem B945521 : Blo 630300 945521 := bstep (se 2 (by rfl) ⟨354570, by rfl⟩ : syracuseStep 945521 = 709141) B709141
theorem B945539 : Blo 630300 945539 := bstep (se 1 (by rfl) ⟨709154, by rfl⟩ : syracuseStep 945539 = 1418309) B1418309
theorem B945569 : Blo 630300 945569 := bstep (se 2 (by rfl) ⟨354588, by rfl⟩ : syracuseStep 945569 = 709177) B709177
theorem B945587 : Blo 630300 945587 := bstep (se 1 (by rfl) ⟨709190, by rfl⟩ : syracuseStep 945587 = 1418381) B1418381
theorem B945617 : Blo 630300 945617 := bstep (se 2 (by rfl) ⟨354606, by rfl⟩ : syracuseStep 945617 = 709213) B709213
theorem B945635 : Blo 630300 945635 := bstep (se 1 (by rfl) ⟨709226, by rfl⟩ : syracuseStep 945635 = 1418453) B1418453
theorem B3206627 : Blo 630300 3206627 := bstep (se 1 (by rfl) ⟨2404970, by rfl⟩ : syracuseStep 3206627 = 4809941) B4809941
theorem B945665 : Blo 630300 945665 := bstep (se 2 (by rfl) ⟨354624, by rfl⟩ : syracuseStep 945665 = 709249) B709249
theorem B945683 : Blo 630300 945683 := bstep (se 1 (by rfl) ⟨709262, by rfl⟩ : syracuseStep 945683 = 1418525) B1418525
theorem B945713 : Blo 630300 945713 := bstep (se 2 (by rfl) ⟨354642, by rfl⟩ : syracuseStep 945713 = 709285) B709285
theorem B945731 : Blo 630300 945731 := bstep (se 1 (by rfl) ⟨709298, by rfl⟩ : syracuseStep 945731 = 1418597) B1418597
theorem B945761 : Blo 630300 945761 := bstep (se 2 (by rfl) ⟨354660, by rfl⟩ : syracuseStep 945761 = 709321) B709321
theorem B945779 : Blo 630300 945779 := bstep (se 1 (by rfl) ⟨709334, by rfl⟩ : syracuseStep 945779 = 1418669) B1418669
theorem B945809 : Blo 630300 945809 := bstep (se 2 (by rfl) ⟨354678, by rfl⟩ : syracuseStep 945809 = 709357) B709357
theorem B945827 : Blo 630300 945827 := bstep (se 1 (by rfl) ⟨709370, by rfl⟩ : syracuseStep 945827 = 1418741) B1418741
theorem B1797805 : Blo 630300 1797805 := bstep (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) B674177
theorem B945857 : Blo 630300 945857 := bstep (se 2 (by rfl) ⟨354696, by rfl⟩ : syracuseStep 945857 = 709393) B709393
theorem B945875 : Blo 630300 945875 := bstep (se 1 (by rfl) ⟨709406, by rfl⟩ : syracuseStep 945875 = 1418813) B1418813
theorem B683731 : Blo 630300 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B945905 : Blo 630300 945905 := bstep (se 2 (by rfl) ⟨354714, by rfl⟩ : syracuseStep 945905 = 709429) B709429
theorem B1732337 : Blo 630300 1732337 := bstep (se 2 (by rfl) ⟨649626, by rfl⟩ : syracuseStep 1732337 = 1299253) B1299253
theorem B945923 : Blo 630300 945923 := bstep (se 1 (by rfl) ⟨709442, by rfl⟩ : syracuseStep 945923 = 1418885) B1418885
theorem B945953 : Blo 630300 945953 := bstep (se 2 (by rfl) ⟨354732, by rfl⟩ : syracuseStep 945953 = 709465) B709465
theorem B1601329 : Blo 630300 1601329 := bstep (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) B1200997
theorem B945971 : Blo 630300 945971 := bstep (se 1 (by rfl) ⟨709478, by rfl⟩ : syracuseStep 945971 = 1418957) B1418957
theorem B946001 : Blo 630300 946001 := bstep (se 2 (by rfl) ⟨354750, by rfl⟩ : syracuseStep 946001 = 709501) B709501
theorem B946019 : Blo 630300 946019 := bstep (se 1 (by rfl) ⟨709514, by rfl⟩ : syracuseStep 946019 = 1419029) B1419029
theorem B946049 : Blo 630300 946049 := bstep (se 2 (by rfl) ⟨354768, by rfl⟩ : syracuseStep 946049 = 709537) B709537
theorem B1798033 : Blo 630300 1798033 := bstep (se 2 (by rfl) ⟨674262, by rfl⟩ : syracuseStep 1798033 = 1348525) B1348525
theorem B946067 : Blo 630300 946067 := bstep (se 1 (by rfl) ⟨709550, by rfl⟩ : syracuseStep 946067 = 1419101) B1419101
theorem B1011619 : Blo 630300 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B946097 : Blo 630300 946097 := bstep (se 2 (by rfl) ⟨354786, by rfl⟩ : syracuseStep 946097 = 709573) B709573
theorem B946115 : Blo 630300 946115 := bstep (se 1 (by rfl) ⟨709586, by rfl⟩ : syracuseStep 946115 = 1419173) B1419173
theorem B946145 : Blo 630300 946145 := bstep (se 2 (by rfl) ⟨354804, by rfl⟩ : syracuseStep 946145 = 709609) B709609
theorem B946163 : Blo 630300 946163 := bstep (se 1 (by rfl) ⟨709622, by rfl⟩ : syracuseStep 946163 = 1419245) B1419245
theorem B946193 : Blo 630300 946193 := bstep (se 2 (by rfl) ⟨354822, by rfl⟩ : syracuseStep 946193 = 709645) B709645
theorem B946211 : Blo 630300 946211 := bstep (se 1 (by rfl) ⟨709658, by rfl⟩ : syracuseStep 946211 = 1419317) B1419317
theorem B2027555 : Blo 630300 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B1798193 : Blo 630300 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B946241 : Blo 630300 946241 := bstep (se 2 (by rfl) ⟨354840, by rfl⟩ : syracuseStep 946241 = 709681) B709681
theorem B1601603 : Blo 630300 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B946259 : Blo 630300 946259 := bstep (se 1 (by rfl) ⟨709694, by rfl⟩ : syracuseStep 946259 = 1419389) B1419389
theorem B946289 : Blo 630300 946289 := bstep (se 2 (by rfl) ⟨354858, by rfl⟩ : syracuseStep 946289 = 709717) B709717
theorem B946307 : Blo 630300 946307 := bstep (se 1 (by rfl) ⟨709730, by rfl⟩ : syracuseStep 946307 = 1419461) B1419461
theorem B946337 : Blo 630300 946337 := bstep (se 2 (by rfl) ⟨354876, by rfl⟩ : syracuseStep 946337 = 709753) B709753
theorem B1798307 : Blo 630300 1798307 := bstep (se 1 (by rfl) ⟨1348730, by rfl⟩ : syracuseStep 1798307 = 2697461) B2697461
theorem B2027683 : Blo 630300 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B946355 : Blo 630300 946355 := bstep (se 1 (by rfl) ⟨709766, by rfl⟩ : syracuseStep 946355 = 1419533) B1419533
theorem B5763269 : Blo 630300 5763269 := bstep (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) B1080613
theorem B946385 : Blo 630300 946385 := bstep (se 2 (by rfl) ⟨354894, by rfl⟩ : syracuseStep 946385 = 709789) B709789
theorem B946403 : Blo 630300 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B946433 : Blo 630300 946433 := bstep (se 2 (by rfl) ⟨354912, by rfl⟩ : syracuseStep 946433 = 709825) B709825
theorem B1601795 : Blo 630300 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B3207437 : Blo 630300 3207437 := bstep (se 3 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 3207437 = 1202789) B1202789
theorem B946451 : Blo 630300 946451 := bstep (se 1 (by rfl) ⟨709838, by rfl⟩ : syracuseStep 946451 = 1419677) B1419677
theorem B946481 : Blo 630300 946481 := bstep (se 2 (by rfl) ⟨354930, by rfl⟩ : syracuseStep 946481 = 709861) B709861
theorem B946499 : Blo 630300 946499 := bstep (se 1 (by rfl) ⟨709874, by rfl⟩ : syracuseStep 946499 = 1419749) B1419749
theorem B946529 : Blo 630300 946529 := bstep (se 2 (by rfl) ⟨354948, by rfl⟩ : syracuseStep 946529 = 709897) B709897
theorem B946547 : Blo 630300 946547 := bstep (se 1 (by rfl) ⟨709910, by rfl⟩ : syracuseStep 946547 = 1419821) B1419821
theorem B946577 : Blo 630300 946577 := bstep (se 2 (by rfl) ⟨354966, by rfl⟩ : syracuseStep 946577 = 709933) B709933
theorem B946595 : Blo 630300 946595 := bstep (se 1 (by rfl) ⟨709946, by rfl⟩ : syracuseStep 946595 = 1419893) B1419893
theorem B946625 : Blo 630300 946625 := bstep (se 2 (by rfl) ⟨354984, by rfl⟩ : syracuseStep 946625 = 709969) B709969
theorem B946643 : Blo 630300 946643 := bstep (se 1 (by rfl) ⟨709982, by rfl⟩ : syracuseStep 946643 = 1419965) B1419965
theorem B946673 : Blo 630300 946673 := bstep (se 2 (by rfl) ⟨355002, by rfl⟩ : syracuseStep 946673 = 710005) B710005
theorem B2028017 : Blo 630300 2028017 := bstep (se 2 (by rfl) ⟨760506, by rfl⟩ : syracuseStep 2028017 = 1521013) B1521013
theorem B946691 : Blo 630300 946691 := bstep (se 1 (by rfl) ⟨710018, by rfl⟩ : syracuseStep 946691 = 1420037) B1420037
theorem B946721 : Blo 630300 946721 := bstep (se 2 (by rfl) ⟨355020, by rfl⟩ : syracuseStep 946721 = 710041) B710041
theorem B946739 : Blo 630300 946739 := bstep (se 1 (by rfl) ⟨710054, by rfl⟩ : syracuseStep 946739 = 1420109) B1420109
theorem B946769 : Blo 630300 946769 := bstep (se 2 (by rfl) ⟨355038, by rfl⟩ : syracuseStep 946769 = 710077) B710077
theorem B946787 : Blo 630300 946787 := bstep (se 1 (by rfl) ⟨710090, by rfl⟩ : syracuseStep 946787 = 1420181) B1420181
theorem B946817 : Blo 630300 946817 := bstep (se 2 (by rfl) ⟨355056, by rfl⟩ : syracuseStep 946817 = 710113) B710113
theorem B946835 : Blo 630300 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B946865 : Blo 630300 946865 := bstep (se 2 (by rfl) ⟨355074, by rfl⟩ : syracuseStep 946865 = 710149) B710149
theorem B946883 : Blo 630300 946883 := bstep (se 1 (by rfl) ⟨710162, by rfl⟩ : syracuseStep 946883 = 1420325) B1420325
theorem B946913 : Blo 630300 946913 := bstep (se 2 (by rfl) ⟨355092, by rfl⟩ : syracuseStep 946913 = 710185) B710185
theorem B946931 : Blo 630300 946931 := bstep (se 1 (by rfl) ⟨710198, by rfl⟩ : syracuseStep 946931 = 1420397) B1420397
theorem B946961 : Blo 630300 946961 := bstep (se 2 (by rfl) ⟨355110, by rfl⟩ : syracuseStep 946961 = 710221) B710221
theorem B946979 : Blo 630300 946979 := bstep (se 1 (by rfl) ⟨710234, by rfl⟩ : syracuseStep 946979 = 1420469) B1420469
theorem B947009 : Blo 630300 947009 := bstep (se 2 (by rfl) ⟨355128, by rfl⟩ : syracuseStep 947009 = 710257) B710257
theorem B1012547 : Blo 630300 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B947027 : Blo 630300 947027 := bstep (se 1 (by rfl) ⟨710270, by rfl⟩ : syracuseStep 947027 = 1420541) B1420541
theorem B947057 : Blo 630300 947057 := bstep (se 2 (by rfl) ⟨355146, by rfl⟩ : syracuseStep 947057 = 710293) B710293
theorem B947075 : Blo 630300 947075 := bstep (se 1 (by rfl) ⟨710306, by rfl⟩ : syracuseStep 947075 = 1420613) B1420613
theorem B947105 : Blo 630300 947105 := bstep (se 2 (by rfl) ⟨355164, by rfl⟩ : syracuseStep 947105 = 710329) B710329
theorem B947123 : Blo 630300 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B947153 : Blo 630300 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B947171 : Blo 630300 947171 := bstep (se 1 (by rfl) ⟨710378, by rfl⟩ : syracuseStep 947171 = 1420757) B1420757
theorem B947201 : Blo 630300 947201 := bstep (se 2 (by rfl) ⟨355200, by rfl⟩ : syracuseStep 947201 = 710401) B710401
theorem B3601421 : Blo 630300 3601421 := bstep (se 3 (by rfl) ⟨675266, by rfl⟩ : syracuseStep 3601421 = 1350533) B1350533
theorem B947219 : Blo 630300 947219 := bstep (se 1 (by rfl) ⟨710414, by rfl⟩ : syracuseStep 947219 = 1420829) B1420829
theorem B947249 : Blo 630300 947249 := bstep (se 2 (by rfl) ⟨355218, by rfl⟩ : syracuseStep 947249 = 710437) B710437
theorem B947267 : Blo 630300 947267 := bstep (se 1 (by rfl) ⟨710450, by rfl⟩ : syracuseStep 947267 = 1420901) B1420901
theorem B1012817 : Blo 630300 1012817 := bstep (se 2 (by rfl) ⟨379806, by rfl⟩ : syracuseStep 1012817 = 759613) B759613
theorem B947297 : Blo 630300 947297 := bstep (se 2 (by rfl) ⟨355236, by rfl⟩ : syracuseStep 947297 = 710473) B710473
theorem B947315 : Blo 630300 947315 := bstep (se 1 (by rfl) ⟨710486, by rfl⟩ : syracuseStep 947315 = 1420973) B1420973
theorem B1799309 : Blo 630300 1799309 := bstep (se 3 (by rfl) ⟨337370, by rfl⟩ : syracuseStep 1799309 = 674741) B674741
theorem B947345 : Blo 630300 947345 := bstep (se 2 (by rfl) ⟨355254, by rfl⟩ : syracuseStep 947345 = 710509) B710509
theorem B947363 : Blo 630300 947363 := bstep (se 1 (by rfl) ⟨710522, by rfl⟩ : syracuseStep 947363 = 1421045) B1421045
theorem B1602737 : Blo 630300 1602737 := bstep (se 2 (by rfl) ⟨601026, by rfl⟩ : syracuseStep 1602737 = 1202053) B1202053
theorem B947393 : Blo 630300 947393 := bstep (se 2 (by rfl) ⟨355272, by rfl⟩ : syracuseStep 947393 = 710545) B710545
theorem B947411 : Blo 630300 947411 := bstep (se 1 (by rfl) ⟨710558, by rfl⟩ : syracuseStep 947411 = 1421117) B1421117
theorem B1602787 : Blo 630300 1602787 := bstep (se 1 (by rfl) ⟨1202090, by rfl⟩ : syracuseStep 1602787 = 2404181) B2404181
theorem B947441 : Blo 630300 947441 := bstep (se 2 (by rfl) ⟨355290, by rfl⟩ : syracuseStep 947441 = 710581) B710581
theorem B947459 : Blo 630300 947459 := bstep (se 1 (by rfl) ⟨710594, by rfl⟩ : syracuseStep 947459 = 1421189) B1421189
theorem B1438993 : Blo 630300 1438993 := bstep (se 2 (by rfl) ⟨539622, by rfl⟩ : syracuseStep 1438993 = 1079245) B1079245
theorem B947489 : Blo 630300 947489 := bstep (se 2 (by rfl) ⟨355308, by rfl⟩ : syracuseStep 947489 = 710617) B710617
theorem B947507 : Blo 630300 947507 := bstep (se 1 (by rfl) ⟨710630, by rfl⟩ : syracuseStep 947507 = 1421261) B1421261
theorem B1799491 : Blo 630300 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B947537 : Blo 630300 947537 := bstep (se 2 (by rfl) ⟨355326, by rfl⟩ : syracuseStep 947537 = 710653) B710653
theorem B947555 : Blo 630300 947555 := bstep (se 1 (by rfl) ⟨710666, by rfl⟩ : syracuseStep 947555 = 1421333) B1421333
theorem B1013105 : Blo 630300 1013105 := bstep (se 2 (by rfl) ⟨379914, by rfl⟩ : syracuseStep 1013105 = 759829) B759829
theorem B1602929 : Blo 630300 1602929 := bstep (se 2 (by rfl) ⟨601098, by rfl⟩ : syracuseStep 1602929 = 1202197) B1202197
theorem B947585 : Blo 630300 947585 := bstep (se 2 (by rfl) ⟨355344, by rfl⟩ : syracuseStep 947585 = 710689) B710689
theorem B947603 : Blo 630300 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B947633 : Blo 630300 947633 := bstep (se 2 (by rfl) ⟨355362, by rfl⟩ : syracuseStep 947633 = 710725) B710725
theorem B947651 : Blo 630300 947651 := bstep (se 1 (by rfl) ⟨710738, by rfl⟩ : syracuseStep 947651 = 1421477) B1421477
theorem B947681 : Blo 630300 947681 := bstep (se 2 (by rfl) ⟨355380, by rfl⟩ : syracuseStep 947681 = 710761) B710761
theorem B1799651 : Blo 630300 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B947699 : Blo 630300 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B947729 : Blo 630300 947729 := bstep (se 2 (by rfl) ⟨355398, by rfl⟩ : syracuseStep 947729 = 710797) B710797
theorem B947747 : Blo 630300 947747 := bstep (se 1 (by rfl) ⟨710810, by rfl⟩ : syracuseStep 947747 = 1421621) B1421621
theorem B947777 : Blo 630300 947777 := bstep (se 2 (by rfl) ⟨355416, by rfl⟩ : syracuseStep 947777 = 710833) B710833
theorem B2127437 : Blo 630300 2127437 := bstep (se 3 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 2127437 = 797789) B797789
theorem B947795 : Blo 630300 947795 := bstep (se 1 (by rfl) ⟨710846, by rfl⟩ : syracuseStep 947795 = 1421693) B1421693
theorem B947825 : Blo 630300 947825 := bstep (se 2 (by rfl) ⟨355434, by rfl⟩ : syracuseStep 947825 = 710869) B710869
theorem B2127491 : Blo 630300 2127491 := bstep (se 1 (by rfl) ⟨1595618, by rfl⟩ : syracuseStep 2127491 = 3191237) B3191237
theorem B947843 : Blo 630300 947843 := bstep (se 1 (by rfl) ⟨710882, by rfl⟩ : syracuseStep 947843 = 1421765) B1421765
theorem B947873 : Blo 630300 947873 := bstep (se 2 (by rfl) ⟨355452, by rfl⟩ : syracuseStep 947873 = 710905) B710905
theorem B4060849 : Blo 630300 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B947891 : Blo 630300 947891 := bstep (se 1 (by rfl) ⟨710918, by rfl⟩ : syracuseStep 947891 = 1421837) B1421837
theorem B947921 : Blo 630300 947921 := bstep (se 2 (by rfl) ⟨355470, by rfl⟩ : syracuseStep 947921 = 710941) B710941
theorem B947939 : Blo 630300 947939 := bstep (se 1 (by rfl) ⟨710954, by rfl⟩ : syracuseStep 947939 = 1421909) B1421909
theorem B947969 : Blo 630300 947969 := bstep (se 2 (by rfl) ⟨355488, by rfl⟩ : syracuseStep 947969 = 710977) B710977
theorem B1013521 : Blo 630300 1013521 := bstep (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) B760141
theorem B947987 : Blo 630300 947987 := bstep (se 1 (by rfl) ⟨710990, by rfl⟩ : syracuseStep 947987 = 1421981) B1421981
theorem B948017 : Blo 630300 948017 := bstep (se 2 (by rfl) ⟨355506, by rfl⟩ : syracuseStep 948017 = 711013) B711013
theorem B948035 : Blo 630300 948035 := bstep (se 1 (by rfl) ⟨711026, by rfl⟩ : syracuseStep 948035 = 1422053) B1422053
theorem B948065 : Blo 630300 948065 := bstep (se 2 (by rfl) ⟨355524, by rfl⟩ : syracuseStep 948065 = 711049) B711049
theorem B948083 : Blo 630300 948083 := bstep (se 1 (by rfl) ⟨711062, by rfl⟩ : syracuseStep 948083 = 1422125) B1422125
theorem B2127761 : Blo 630300 2127761 := bstep (se 2 (by rfl) ⟨797910, by rfl⟩ : syracuseStep 2127761 = 1595821) B1595821
theorem B948113 : Blo 630300 948113 := bstep (se 2 (by rfl) ⟨355542, by rfl⟩ : syracuseStep 948113 = 711085) B711085
theorem B948131 : Blo 630300 948131 := bstep (se 1 (by rfl) ⟨711098, by rfl⟩ : syracuseStep 948131 = 1422197) B1422197
theorem B3602353 : Blo 630300 3602353 := bstep (se 2 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 3602353 = 2701765) B2701765
theorem B948161 : Blo 630300 948161 := bstep (se 2 (by rfl) ⟨355560, by rfl⟩ : syracuseStep 948161 = 711121) B711121
theorem B948179 : Blo 630300 948179 := bstep (se 1 (by rfl) ⟨711134, by rfl⟩ : syracuseStep 948179 = 1422269) B1422269
theorem B948209 : Blo 630300 948209 := bstep (se 2 (by rfl) ⟨355578, by rfl⟩ : syracuseStep 948209 = 711157) B711157
theorem B948227 : Blo 630300 948227 := bstep (se 1 (by rfl) ⟨711170, by rfl⟩ : syracuseStep 948227 = 1422341) B1422341
theorem B948257 : Blo 630300 948257 := bstep (se 2 (by rfl) ⟨355596, by rfl⟩ : syracuseStep 948257 = 711193) B711193
theorem B948275 : Blo 630300 948275 := bstep (se 1 (by rfl) ⟨711206, by rfl⟩ : syracuseStep 948275 = 1422413) B1422413
theorem B948305 : Blo 630300 948305 := bstep (se 2 (by rfl) ⟨355614, by rfl⟩ : syracuseStep 948305 = 711229) B711229
theorem B948323 : Blo 630300 948323 := bstep (se 1 (by rfl) ⟨711242, by rfl⟩ : syracuseStep 948323 = 1422485) B1422485
theorem B948353 : Blo 630300 948353 := bstep (se 2 (by rfl) ⟨355632, by rfl⟩ : syracuseStep 948353 = 711265) B711265
theorem B948371 : Blo 630300 948371 := bstep (se 1 (by rfl) ⟨711278, by rfl⟩ : syracuseStep 948371 = 1422557) B1422557
theorem B948401 : Blo 630300 948401 := bstep (se 2 (by rfl) ⟨355650, by rfl⟩ : syracuseStep 948401 = 711301) B711301
theorem B948419 : Blo 630300 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B948449 : Blo 630300 948449 := bstep (se 2 (by rfl) ⟨355668, by rfl⟩ : syracuseStep 948449 = 711337) B711337
theorem B948467 : Blo 630300 948467 := bstep (se 1 (by rfl) ⟨711350, by rfl⟩ : syracuseStep 948467 = 1422701) B1422701
theorem B948497 : Blo 630300 948497 := bstep (se 2 (by rfl) ⟨355686, by rfl⟩ : syracuseStep 948497 = 711373) B711373
theorem B948515 : Blo 630300 948515 := bstep (se 1 (by rfl) ⟨711386, by rfl⟩ : syracuseStep 948515 = 1422773) B1422773
theorem B948545 : Blo 630300 948545 := bstep (se 2 (by rfl) ⟨355704, by rfl⟩ : syracuseStep 948545 = 711409) B711409
theorem B1603921 : Blo 630300 1603921 := bstep (se 2 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 1603921 = 1202941) B1202941
theorem B948563 : Blo 630300 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B948593 : Blo 630300 948593 := bstep (se 2 (by rfl) ⟨355722, by rfl⟩ : syracuseStep 948593 = 711445) B711445
theorem B948611 : Blo 630300 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B948641 : Blo 630300 948641 := bstep (se 2 (by rfl) ⟨355740, by rfl⟩ : syracuseStep 948641 = 711481) B711481
theorem B2128301 : Blo 630300 2128301 := bstep (se 3 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 2128301 = 798113) B798113
theorem B948659 : Blo 630300 948659 := bstep (se 1 (by rfl) ⟨711494, by rfl⟩ : syracuseStep 948659 = 1422989) B1422989
theorem B948689 : Blo 630300 948689 := bstep (se 2 (by rfl) ⟨355758, by rfl⟩ : syracuseStep 948689 = 711517) B711517
theorem B2128355 : Blo 630300 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B948707 : Blo 630300 948707 := bstep (se 1 (by rfl) ⟨711530, by rfl⟩ : syracuseStep 948707 = 1423061) B1423061
theorem B719347 : Blo 630300 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B948737 : Blo 630300 948737 := bstep (se 2 (by rfl) ⟨355776, by rfl⟩ : syracuseStep 948737 = 711553) B711553
theorem B1800721 : Blo 630300 1800721 := bstep (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) B1350541
theorem B948755 : Blo 630300 948755 := bstep (se 1 (by rfl) ⟨711566, by rfl⟩ : syracuseStep 948755 = 1423133) B1423133
theorem B948785 : Blo 630300 948785 := bstep (se 2 (by rfl) ⟨355794, by rfl⟩ : syracuseStep 948785 = 711589) B711589
theorem B948803 : Blo 630300 948803 := bstep (se 1 (by rfl) ⟨711602, by rfl⟩ : syracuseStep 948803 = 1423205) B1423205
theorem B948833 : Blo 630300 948833 := bstep (se 2 (by rfl) ⟨355812, by rfl⟩ : syracuseStep 948833 = 711625) B711625
theorem B1604195 : Blo 630300 1604195 := bstep (se 1 (by rfl) ⟨1203146, by rfl⟩ : syracuseStep 1604195 = 2406293) B2406293
theorem B948851 : Blo 630300 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B948881 : Blo 630300 948881 := bstep (se 2 (by rfl) ⟨355830, by rfl⟩ : syracuseStep 948881 = 711661) B711661
theorem B1014419 : Blo 630300 1014419 := bstep (se 1 (by rfl) ⟨760814, by rfl⟩ : syracuseStep 1014419 = 1521629) B1521629
theorem B948899 : Blo 630300 948899 := bstep (se 1 (by rfl) ⟨711674, by rfl⟩ : syracuseStep 948899 = 1423349) B1423349
theorem B948929 : Blo 630300 948929 := bstep (se 2 (by rfl) ⟨355848, by rfl⟩ : syracuseStep 948929 = 711697) B711697
theorem B948947 : Blo 630300 948947 := bstep (se 1 (by rfl) ⟨711710, by rfl⟩ : syracuseStep 948947 = 1423421) B1423421
theorem B2128625 : Blo 630300 2128625 := bstep (se 2 (by rfl) ⟨798234, by rfl⟩ : syracuseStep 2128625 = 1596469) B1596469
theorem B948977 : Blo 630300 948977 := bstep (se 2 (by rfl) ⟨355866, by rfl⟩ : syracuseStep 948977 = 711733) B711733
theorem B1080067 : Blo 630300 1080067 := bstep (se 1 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 1080067 = 1620101) B1620101
theorem B948995 : Blo 630300 948995 := bstep (se 1 (by rfl) ⟨711746, by rfl⟩ : syracuseStep 948995 = 1423493) B1423493
theorem B949025 : Blo 630300 949025 := bstep (se 2 (by rfl) ⟨355884, by rfl⟩ : syracuseStep 949025 = 711769) B711769
theorem B1604387 : Blo 630300 1604387 := bstep (se 1 (by rfl) ⟨1203290, by rfl⟩ : syracuseStep 1604387 = 2406581) B2406581
theorem B949043 : Blo 630300 949043 := bstep (se 1 (by rfl) ⟨711782, by rfl⟩ : syracuseStep 949043 = 1423565) B1423565
theorem B949073 : Blo 630300 949073 := bstep (se 2 (by rfl) ⟨355902, by rfl⟩ : syracuseStep 949073 = 711805) B711805
theorem B949091 : Blo 630300 949091 := bstep (se 1 (by rfl) ⟨711818, by rfl⟩ : syracuseStep 949091 = 1423637) B1423637
theorem B1014643 : Blo 630300 1014643 := bstep (se 1 (by rfl) ⟨760982, by rfl⟩ : syracuseStep 1014643 = 1521965) B1521965
theorem B949121 : Blo 630300 949121 := bstep (se 2 (by rfl) ⟨355920, by rfl⟩ : syracuseStep 949121 = 711841) B711841
theorem B949139 : Blo 630300 949139 := bstep (se 1 (by rfl) ⟨711854, by rfl⟩ : syracuseStep 949139 = 1423709) B1423709
theorem B949169 : Blo 630300 949169 := bstep (se 2 (by rfl) ⟨355938, by rfl⟩ : syracuseStep 949169 = 711877) B711877
theorem B949187 : Blo 630300 949187 := bstep (se 1 (by rfl) ⟨711890, by rfl⟩ : syracuseStep 949187 = 1423781) B1423781
theorem B949217 : Blo 630300 949217 := bstep (se 2 (by rfl) ⟨355956, by rfl⟩ : syracuseStep 949217 = 711913) B711913
theorem B949235 : Blo 630300 949235 := bstep (se 1 (by rfl) ⟨711926, by rfl⟩ : syracuseStep 949235 = 1423853) B1423853
theorem B949265 : Blo 630300 949265 := bstep (se 2 (by rfl) ⟨355974, by rfl⟩ : syracuseStep 949265 = 711949) B711949
theorem B949283 : Blo 630300 949283 := bstep (se 1 (by rfl) ⟨711962, by rfl⟩ : syracuseStep 949283 = 1423925) B1423925
theorem B949313 : Blo 630300 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B949331 : Blo 630300 949331 := bstep (se 1 (by rfl) ⟨711998, by rfl⟩ : syracuseStep 949331 = 1423997) B1423997
theorem B949361 : Blo 630300 949361 := bstep (se 2 (by rfl) ⟨356010, by rfl⟩ : syracuseStep 949361 = 712021) B712021
theorem B3210353 : Blo 630300 3210353 := bstep (se 2 (by rfl) ⟨1203882, by rfl⟩ : syracuseStep 3210353 = 2407765) B2407765
theorem B949379 : Blo 630300 949379 := bstep (se 1 (by rfl) ⟨712034, by rfl⟩ : syracuseStep 949379 = 1424069) B1424069
theorem B949409 : Blo 630300 949409 := bstep (se 2 (by rfl) ⟨356028, by rfl⟩ : syracuseStep 949409 = 712057) B712057
theorem B949427 : Blo 630300 949427 := bstep (se 1 (by rfl) ⟨712070, by rfl⟩ : syracuseStep 949427 = 1424141) B1424141
theorem B949457 : Blo 630300 949457 := bstep (se 2 (by rfl) ⟨356046, by rfl⟩ : syracuseStep 949457 = 712093) B712093
theorem B949475 : Blo 630300 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B949505 : Blo 630300 949505 := bstep (se 2 (by rfl) ⟨356064, by rfl⟩ : syracuseStep 949505 = 712129) B712129
theorem B2129165 : Blo 630300 2129165 := bstep (se 3 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 2129165 = 798437) B798437
theorem B949523 : Blo 630300 949523 := bstep (se 1 (by rfl) ⟨712142, by rfl⟩ : syracuseStep 949523 = 1424285) B1424285
theorem B720163 : Blo 630300 720163 := bstep (se 1 (by rfl) ⟨540122, by rfl⟩ : syracuseStep 720163 = 1080245) B1080245
theorem B949553 : Blo 630300 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B2129219 : Blo 630300 2129219 := bstep (se 1 (by rfl) ⟨1596914, by rfl⟩ : syracuseStep 2129219 = 3193829) B3193829
theorem B949571 : Blo 630300 949571 := bstep (se 1 (by rfl) ⟨712178, by rfl⟩ : syracuseStep 949571 = 1424357) B1424357
theorem B949601 : Blo 630300 949601 := bstep (se 2 (by rfl) ⟨356100, by rfl⟩ : syracuseStep 949601 = 712201) B712201
theorem B3603811 : Blo 630300 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B949619 : Blo 630300 949619 := bstep (se 1 (by rfl) ⟨712214, by rfl⟩ : syracuseStep 949619 = 1424429) B1424429
theorem B2030989 : Blo 630300 2030989 := bstep (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) B761621
theorem B949649 : Blo 630300 949649 := bstep (se 2 (by rfl) ⟨356118, by rfl⟩ : syracuseStep 949649 = 712237) B712237
theorem B949667 : Blo 630300 949667 := bstep (se 1 (by rfl) ⟨712250, by rfl⟩ : syracuseStep 949667 = 1424501) B1424501
theorem B949697 : Blo 630300 949697 := bstep (se 2 (by rfl) ⟨356136, by rfl⟩ : syracuseStep 949697 = 712273) B712273
theorem B949715 : Blo 630300 949715 := bstep (se 1 (by rfl) ⟨712286, by rfl⟩ : syracuseStep 949715 = 1424573) B1424573
theorem B949745 : Blo 630300 949745 := bstep (se 2 (by rfl) ⟨356154, by rfl⟩ : syracuseStep 949745 = 712309) B712309
theorem B949763 : Blo 630300 949763 := bstep (se 1 (by rfl) ⟨712322, by rfl⟩ : syracuseStep 949763 = 1424645) B1424645
theorem B6094349 : Blo 630300 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B949793 : Blo 630300 949793 := bstep (se 2 (by rfl) ⟨356172, by rfl⟩ : syracuseStep 949793 = 712345) B712345
theorem B949811 : Blo 630300 949811 := bstep (se 1 (by rfl) ⟨712358, by rfl⟩ : syracuseStep 949811 = 1424717) B1424717
theorem B2129489 : Blo 630300 2129489 := bstep (se 2 (by rfl) ⟨798558, by rfl⟩ : syracuseStep 2129489 = 1597117) B1597117
theorem B949841 : Blo 630300 949841 := bstep (se 2 (by rfl) ⟨356190, by rfl⟩ : syracuseStep 949841 = 712381) B712381
theorem B949859 : Blo 630300 949859 := bstep (se 1 (by rfl) ⟨712394, by rfl⟩ : syracuseStep 949859 = 1424789) B1424789
theorem B949889 : Blo 630300 949889 := bstep (se 2 (by rfl) ⟨356208, by rfl⟩ : syracuseStep 949889 = 712417) B712417
theorem B2031245 : Blo 630300 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B949907 : Blo 630300 949907 := bstep (se 1 (by rfl) ⟨712430, by rfl⟩ : syracuseStep 949907 = 1424861) B1424861
theorem B949937 : Blo 630300 949937 := bstep (se 2 (by rfl) ⟨356226, by rfl⟩ : syracuseStep 949937 = 712453) B712453
theorem B949955 : Blo 630300 949955 := bstep (se 1 (by rfl) ⟨712466, by rfl⟩ : syracuseStep 949955 = 1424933) B1424933
theorem B1605329 : Blo 630300 1605329 := bstep (se 2 (by rfl) ⟨601998, by rfl⟩ : syracuseStep 1605329 = 1203997) B1203997
theorem B949985 : Blo 630300 949985 := bstep (se 2 (by rfl) ⟨356244, by rfl⟩ : syracuseStep 949985 = 712489) B712489
theorem B950003 : Blo 630300 950003 := bstep (se 1 (by rfl) ⟨712502, by rfl⟩ : syracuseStep 950003 = 1425005) B1425005
theorem B1605379 : Blo 630300 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B1801997 : Blo 630300 1801997 := bstep (se 3 (by rfl) ⟨337874, by rfl⟩ : syracuseStep 1801997 = 675749) B675749
theorem B950033 : Blo 630300 950033 := bstep (se 2 (by rfl) ⟨356262, by rfl⟩ : syracuseStep 950033 = 712525) B712525
theorem B950051 : Blo 630300 950051 := bstep (se 1 (by rfl) ⟨712538, by rfl⟩ : syracuseStep 950051 = 1425077) B1425077
theorem B950081 : Blo 630300 950081 := bstep (se 2 (by rfl) ⟨356280, by rfl⟩ : syracuseStep 950081 = 712561) B712561
theorem B950099 : Blo 630300 950099 := bstep (se 1 (by rfl) ⟨712574, by rfl⟩ : syracuseStep 950099 = 1425149) B1425149
theorem B1015649 : Blo 630300 1015649 := bstep (se 2 (by rfl) ⟨380868, by rfl⟩ : syracuseStep 1015649 = 761737) B761737
theorem B3604337 : Blo 630300 3604337 := bstep (se 2 (by rfl) ⟨1351626, by rfl⟩ : syracuseStep 3604337 = 2703253) B2703253
theorem B950129 : Blo 630300 950129 := bstep (se 2 (by rfl) ⟨356298, by rfl⟩ : syracuseStep 950129 = 712597) B712597
theorem B950147 : Blo 630300 950147 := bstep (se 1 (by rfl) ⟨712610, by rfl⟩ : syracuseStep 950147 = 1425221) B1425221
theorem B1605521 : Blo 630300 1605521 := bstep (se 2 (by rfl) ⟨602070, by rfl⟩ : syracuseStep 1605521 = 1204141) B1204141
theorem B950177 : Blo 630300 950177 := bstep (se 2 (by rfl) ⟨356316, by rfl⟩ : syracuseStep 950177 = 712633) B712633
theorem B950195 : Blo 630300 950195 := bstep (se 1 (by rfl) ⟨712646, by rfl⟩ : syracuseStep 950195 = 1425293) B1425293
theorem B1802179 : Blo 630300 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B950225 : Blo 630300 950225 := bstep (se 2 (by rfl) ⟨356334, by rfl⟩ : syracuseStep 950225 = 712669) B712669
theorem B950243 : Blo 630300 950243 := bstep (se 1 (by rfl) ⟨712682, by rfl⟩ : syracuseStep 950243 = 1425365) B1425365
theorem B1802225 : Blo 630300 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B950297 : Blo 630300 950297 := bstep (se 2 (by rfl) ⟨356361, by rfl⟩ : syracuseStep 950297 = 712723) B712723
theorem B1278067 : Blo 630300 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B950411 : Blo 630300 950411 := bstep (se 1 (by rfl) ⟨712808, by rfl⟩ : syracuseStep 950411 = 1425617) B1425617
theorem B950423 : Blo 630300 950423 := bstep (se 1 (by rfl) ⟨712817, by rfl⟩ : syracuseStep 950423 = 1425635) B1425635
theorem B2130137 : Blo 630300 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B950489 : Blo 630300 950489 := bstep (se 2 (by rfl) ⟨356433, by rfl⟩ : syracuseStep 950489 = 712867) B712867
theorem B950603 : Blo 630300 950603 := bstep (se 1 (by rfl) ⟨712952, by rfl⟩ : syracuseStep 950603 = 1425905) B1425905
theorem B950615 : Blo 630300 950615 := bstep (se 1 (by rfl) ⟨712961, by rfl⟩ : syracuseStep 950615 = 1425923) B1425923
theorem B950681 : Blo 630300 950681 := bstep (se 2 (by rfl) ⟨356505, by rfl⟩ : syracuseStep 950681 = 713011) B713011
theorem B1081817 : Blo 630300 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B950795 : Blo 630300 950795 := bstep (se 1 (by rfl) ⟨713096, by rfl⟩ : syracuseStep 950795 = 1426193) B1426193
theorem B15368717 : Blo 630300 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B950807 : Blo 630300 950807 := bstep (se 1 (by rfl) ⟨713105, by rfl⟩ : syracuseStep 950807 = 1426211) B1426211
theorem B1114649 : Blo 630300 1114649 := bstep (se 2 (by rfl) ⟨417993, by rfl⟩ : syracuseStep 1114649 = 835987) B835987
theorem B1704523 : Blo 630300 1704523 := bstep (se 1 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 1704523 = 2556785) B2556785
theorem B950873 : Blo 630300 950873 := bstep (se 2 (by rfl) ⟨356577, by rfl⟩ : syracuseStep 950873 = 713155) B713155
theorem B852619 : Blo 630300 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B950987 : Blo 630300 950987 := bstep (se 1 (by rfl) ⟨713240, by rfl⟩ : syracuseStep 950987 = 1426481) B1426481
theorem B950999 : Blo 630300 950999 := bstep (se 1 (by rfl) ⟨713249, by rfl⟩ : syracuseStep 950999 = 1426499) B1426499
theorem B951065 : Blo 630300 951065 := bstep (se 2 (by rfl) ⟨356649, by rfl⟩ : syracuseStep 951065 = 713299) B713299
theorem B951179 : Blo 630300 951179 := bstep (se 1 (by rfl) ⟨713384, by rfl⟩ : syracuseStep 951179 = 1426769) B1426769
theorem B2130839 : Blo 630300 2130839 := bstep (se 1 (by rfl) ⟨1598129, by rfl⟩ : syracuseStep 2130839 = 3196259) B3196259
theorem B951191 : Blo 630300 951191 := bstep (se 1 (by rfl) ⟨713393, by rfl⟩ : syracuseStep 951191 = 1426787) B1426787
theorem B5473241 : Blo 630300 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B951257 : Blo 630300 951257 := bstep (se 2 (by rfl) ⟨356721, by rfl⟩ : syracuseStep 951257 = 713443) B713443
theorem B951371 : Blo 630300 951371 := bstep (se 1 (by rfl) ⟨713528, by rfl⟩ : syracuseStep 951371 = 1427057) B1427057
theorem B951383 : Blo 630300 951383 := bstep (se 1 (by rfl) ⟨713537, by rfl⟩ : syracuseStep 951383 = 1427075) B1427075
theorem B951449 : Blo 630300 951449 := bstep (se 2 (by rfl) ⟨356793, by rfl⟩ : syracuseStep 951449 = 713587) B713587
theorem B2393489 : Blo 630300 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B2131379 : Blo 630300 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B1803865 : Blo 630300 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B2131649 : Blo 630300 2131649 := bstep (se 2 (by rfl) ⟨799368, by rfl⟩ : syracuseStep 2131649 = 1598737) B1598737
theorem B2393945 : Blo 630300 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B3606545 : Blo 630300 3606545 := bstep (se 2 (by rfl) ⟨1352454, by rfl⟩ : syracuseStep 3606545 = 2704909) B2704909
theorem B2394157 : Blo 630300 2394157 := bstep (se 3 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 2394157 = 897809) B897809
theorem B1804481 : Blo 630300 1804481 := bstep (se 2 (by rfl) ⟨676680, by rfl⟩ : syracuseStep 1804481 = 1353361) B1353361
theorem B2427101 : Blo 630300 2427101 := bstep (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) B910163
theorem B2132189 : Blo 630300 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B2885905 : Blo 630300 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B2394461 : Blo 630300 2394461 := bstep (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) B897923
theorem B1280395 : Blo 630300 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B22219157 : Blo 630300 22219157 := bstep (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) B1041523
theorem B3607001 : Blo 630300 3607001 := bstep (se 2 (by rfl) ⟨1352625, by rfl⟩ : syracuseStep 3607001 = 2705251) B2705251
theorem B1477441 : Blo 630300 1477441 := bstep (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) B1108081
theorem B10226549 : Blo 630300 10226549 := bstep (se 5 (by rfl) ⟨479369, by rfl⟩ : syracuseStep 10226549 = 958739) B958739
theorem B2558893 : Blo 630300 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B2165825 : Blo 630300 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B2198593 : Blo 630300 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B7310411 : Blo 630300 7310411 := bstep (se 1 (by rfl) ⟨5482808, by rfl⟩ : syracuseStep 7310411 = 10965617) B10965617
theorem B1445015 : Blo 630300 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B6851735 : Blo 630300 6851735 := bstep (se 1 (by rfl) ⟨5138801, by rfl⟩ : syracuseStep 6851735 = 10277603) B10277603
theorem B2559235 : Blo 630300 2559235 := bstep (se 1 (by rfl) ⟨1919426, by rfl⟩ : syracuseStep 2559235 = 3838853) B3838853
theorem B2133323 : Blo 630300 2133323 := bstep (se 1 (by rfl) ⟨1599992, by rfl⟩ : syracuseStep 2133323 = 3199985) B3199985
theorem B2559377 : Blo 630300 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B1281523 : Blo 630300 1281523 := bstep (se 1 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 1281523 = 1922285) B1922285
theorem B2133593 : Blo 630300 2133593 := bstep (se 2 (by rfl) ⟨800097, by rfl⟩ : syracuseStep 2133593 = 1600195) B1600195
theorem B1347329 : Blo 630300 1347329 := bstep (se 2 (by rfl) ⟨505248, by rfl⟩ : syracuseStep 1347329 = 1010497) B1010497
theorem B2559833 : Blo 630300 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B1347671 : Blo 630300 1347671 := bstep (se 1 (by rfl) ⟨1010753, by rfl⟩ : syracuseStep 1347671 = 2021507) B2021507
theorem B856153 : Blo 630300 856153 := bstep (se 2 (by rfl) ⟨321057, by rfl⟩ : syracuseStep 856153 = 642115) B642115
theorem B4558999 : Blo 630300 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B2134295 : Blo 630300 2134295 := bstep (se 1 (by rfl) ⟨1600721, by rfl⟩ : syracuseStep 2134295 = 3201443) B3201443
theorem B1446283 : Blo 630300 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B3248657 : Blo 630300 3248657 := bstep (se 2 (by rfl) ⟨1218246, by rfl⟩ : syracuseStep 3248657 = 2436493) B2436493
theorem B2888243 : Blo 630300 2888243 := bstep (se 1 (by rfl) ⟨2166182, by rfl⟩ : syracuseStep 2888243 = 4332365) B4332365
theorem B856651 : Blo 630300 856651 := bstep (se 1 (by rfl) ⟨642488, by rfl⟩ : syracuseStep 856651 = 1284977) B1284977
theorem B1348235 : Blo 630300 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B2134835 : Blo 630300 2134835 := bstep (se 1 (by rfl) ⟨1601126, by rfl⟩ : syracuseStep 2134835 = 3202253) B3202253
theorem B758603 : Blo 630300 758603 := bstep (se 1 (by rfl) ⟨568952, by rfl⟩ : syracuseStep 758603 = 1137905) B1137905
theorem B2397059 : Blo 630300 2397059 := bstep (se 1 (by rfl) ⟨1797794, by rfl⟩ : syracuseStep 2397059 = 3595589) B3595589
theorem B2397073 : Blo 630300 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B16192547 : Blo 630300 16192547 := bstep (se 1 (by rfl) ⟨12144410, by rfl⟩ : syracuseStep 16192547 = 24288821) B24288821
theorem B2135105 : Blo 630300 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B3642499 : Blo 630300 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B2397377 : Blo 630300 2397377 := bstep (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) B1798033
theorem B1348825 : Blo 630300 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B2692403 : Blo 630300 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B2135645 : Blo 630300 2135645 := bstep (se 3 (by rfl) ⟨400433, by rfl⟩ : syracuseStep 2135645 = 800867) B800867
theorem B2561843 : Blo 630300 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B2398045 : Blo 630300 2398045 := bstep (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) B899267
theorem B2889665 : Blo 630300 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B1218647 : Blo 630300 1218647 := bstep (se 1 (by rfl) ⟨913985, by rfl⟩ : syracuseStep 1218647 = 1827971) B1827971
theorem B2562137 : Blo 630300 2562137 := bstep (se 2 (by rfl) ⟨960801, by rfl⟩ : syracuseStep 2562137 = 1921603) B1921603
theorem B1349875 : Blo 630300 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B760151 : Blo 630300 760151 := bstep (se 1 (by rfl) ⟨570113, by rfl⟩ : syracuseStep 760151 = 1140227) B1140227
theorem B2431505 : Blo 630300 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B2136779 : Blo 630300 2136779 := bstep (se 1 (by rfl) ⟨1602584, by rfl⟩ : syracuseStep 2136779 = 3205169) B3205169
theorem B2137049 : Blo 630300 2137049 := bstep (se 2 (by rfl) ⟨801393, by rfl⟩ : syracuseStep 2137049 = 1602787) B1602787
theorem B760843 : Blo 630300 760843 := bstep (se 1 (by rfl) ⟨570632, by rfl⟩ : syracuseStep 760843 = 1141265) B1141265
theorem B2399321 : Blo 630300 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B2464913 : Blo 630300 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B4791473 : Blo 630300 4791473 := bstep (se 2 (by rfl) ⟨1796802, by rfl⟩ : syracuseStep 4791473 = 3593605) B3593605
theorem B7183565 : Blo 630300 7183565 := bstep (se 3 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 7183565 = 2693837) B2693837
theorem B18455813 : Blo 630300 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B1514969 : Blo 630300 1514969 := bstep (se 2 (by rfl) ⟨568113, by rfl⟩ : syracuseStep 1514969 = 1136227) B1136227
theorem B630315 : Blo 630300 630315 := bstep (se 1 (by rfl) ⟨472736, by rfl⟩ : syracuseStep 630315 = 945473) B945473
theorem B630327 : Blo 630300 630327 := bstep (se 1 (by rfl) ⟨472745, by rfl⟩ : syracuseStep 630327 = 945491) B945491
theorem B5414465 : Blo 630300 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B630347 : Blo 630300 630347 := bstep (se 1 (by rfl) ⟨472760, by rfl⟩ : syracuseStep 630347 = 945521) B945521
theorem B630359 : Blo 630300 630359 := bstep (se 1 (by rfl) ⟨472769, by rfl⟩ : syracuseStep 630359 = 945539) B945539
theorem B630379 : Blo 630300 630379 := bstep (se 1 (by rfl) ⟨472784, by rfl⟩ : syracuseStep 630379 = 945569) B945569
theorem B630391 : Blo 630300 630391 := bstep (se 1 (by rfl) ⟨472793, by rfl⟩ : syracuseStep 630391 = 945587) B945587
theorem B630411 : Blo 630300 630411 := bstep (se 1 (by rfl) ⟨472808, by rfl⟩ : syracuseStep 630411 = 945617) B945617
theorem B2137751 : Blo 630300 2137751 := bstep (se 1 (by rfl) ⟨1603313, by rfl⟩ : syracuseStep 2137751 = 3206627) B3206627
theorem B4791959 : Blo 630300 4791959 := bstep (se 1 (by rfl) ⟨3593969, by rfl⟩ : syracuseStep 4791959 = 7187939) B7187939
theorem B630423 : Blo 630300 630423 := bstep (se 1 (by rfl) ⟨472817, by rfl⟩ : syracuseStep 630423 = 945635) B945635
theorem B630443 : Blo 630300 630443 := bstep (se 1 (by rfl) ⟨472832, by rfl⟩ : syracuseStep 630443 = 945665) B945665
theorem B2694829 : Blo 630300 2694829 := bstep (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) B1010561
theorem B630455 : Blo 630300 630455 := bstep (se 1 (by rfl) ⟨472841, by rfl⟩ : syracuseStep 630455 = 945683) B945683
theorem B1351361 : Blo 630300 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B630475 : Blo 630300 630475 := bstep (se 1 (by rfl) ⟨472856, by rfl⟩ : syracuseStep 630475 = 945713) B945713
theorem B630487 : Blo 630300 630487 := bstep (se 1 (by rfl) ⟨472865, by rfl⟩ : syracuseStep 630487 = 945731) B945731
theorem B3612377 : Blo 630300 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B630507 : Blo 630300 630507 := bstep (se 1 (by rfl) ⟨472880, by rfl⟩ : syracuseStep 630507 = 945761) B945761
theorem B630519 : Blo 630300 630519 := bstep (se 1 (by rfl) ⟨472889, by rfl⟩ : syracuseStep 630519 = 945779) B945779
theorem B630539 : Blo 630300 630539 := bstep (se 1 (by rfl) ⟨472904, by rfl⟩ : syracuseStep 630539 = 945809) B945809
theorem B630551 : Blo 630300 630551 := bstep (se 1 (by rfl) ⟨472913, by rfl⟩ : syracuseStep 630551 = 945827) B945827
theorem B630571 : Blo 630300 630571 := bstep (se 1 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 630571 = 945857) B945857
theorem B630583 : Blo 630300 630583 := bstep (se 1 (by rfl) ⟨472937, by rfl⟩ : syracuseStep 630583 = 945875) B945875
theorem B630603 : Blo 630300 630603 := bstep (se 1 (by rfl) ⟨472952, by rfl⟩ : syracuseStep 630603 = 945905) B945905
theorem B1154891 : Blo 630300 1154891 := bstep (se 1 (by rfl) ⟨866168, by rfl⟩ : syracuseStep 1154891 = 1732337) B1732337
theorem B630615 : Blo 630300 630615 := bstep (se 1 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 630615 = 945923) B945923
theorem B630635 : Blo 630300 630635 := bstep (se 1 (by rfl) ⟨472976, by rfl⟩ : syracuseStep 630635 = 945953) B945953
theorem B630647 : Blo 630300 630647 := bstep (se 1 (by rfl) ⟨472985, by rfl⟩ : syracuseStep 630647 = 945971) B945971
theorem B630667 : Blo 630300 630667 := bstep (se 1 (by rfl) ⟨473000, by rfl⟩ : syracuseStep 630667 = 946001) B946001
theorem B630679 : Blo 630300 630679 := bstep (se 1 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 630679 = 946019) B946019
theorem B630699 : Blo 630300 630699 := bstep (se 1 (by rfl) ⟨473024, by rfl⟩ : syracuseStep 630699 = 946049) B946049
theorem B2891693 : Blo 630300 2891693 := bstep (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) B1084385
theorem B630711 : Blo 630300 630711 := bstep (se 1 (by rfl) ⟨473033, by rfl⟩ : syracuseStep 630711 = 946067) B946067
theorem B630731 : Blo 630300 630731 := bstep (se 1 (by rfl) ⟨473048, by rfl⟩ : syracuseStep 630731 = 946097) B946097
theorem B630743 : Blo 630300 630743 := bstep (se 1 (by rfl) ⟨473057, by rfl⟩ : syracuseStep 630743 = 946115) B946115
theorem B630763 : Blo 630300 630763 := bstep (se 1 (by rfl) ⟨473072, by rfl⟩ : syracuseStep 630763 = 946145) B946145
theorem B630775 : Blo 630300 630775 := bstep (se 1 (by rfl) ⟨473081, by rfl⟩ : syracuseStep 630775 = 946163) B946163
theorem B630795 : Blo 630300 630795 := bstep (se 1 (by rfl) ⟨473096, by rfl⟩ : syracuseStep 630795 = 946193) B946193
theorem B630807 : Blo 630300 630807 := bstep (se 1 (by rfl) ⟨473105, by rfl⟩ : syracuseStep 630807 = 946211) B946211
theorem B1351703 : Blo 630300 1351703 := bstep (se 1 (by rfl) ⟨1013777, by rfl⟩ : syracuseStep 1351703 = 2027555) B2027555
theorem B630827 : Blo 630300 630827 := bstep (se 1 (by rfl) ⟨473120, by rfl⟩ : syracuseStep 630827 = 946241) B946241
theorem B630839 : Blo 630300 630839 := bstep (se 1 (by rfl) ⟨473129, by rfl⟩ : syracuseStep 630839 = 946259) B946259
theorem B630859 : Blo 630300 630859 := bstep (se 1 (by rfl) ⟨473144, by rfl⟩ : syracuseStep 630859 = 946289) B946289
theorem B630871 : Blo 630300 630871 := bstep (se 1 (by rfl) ⟨473153, by rfl⟩ : syracuseStep 630871 = 946307) B946307
theorem B1876061 : Blo 630300 1876061 := bstep (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) B703523
theorem B630891 : Blo 630300 630891 := bstep (se 1 (by rfl) ⟨473168, by rfl⟩ : syracuseStep 630891 = 946337) B946337
theorem B630903 : Blo 630300 630903 := bstep (se 1 (by rfl) ⟨473177, by rfl⟩ : syracuseStep 630903 = 946355) B946355
theorem B630923 : Blo 630300 630923 := bstep (se 1 (by rfl) ⟨473192, by rfl⟩ : syracuseStep 630923 = 946385) B946385
theorem B630935 : Blo 630300 630935 := bstep (se 1 (by rfl) ⟨473201, by rfl⟩ : syracuseStep 630935 = 946403) B946403
theorem B630955 : Blo 630300 630955 := bstep (se 1 (by rfl) ⟨473216, by rfl⟩ : syracuseStep 630955 = 946433) B946433
theorem B2138291 : Blo 630300 2138291 := bstep (se 1 (by rfl) ⟨1603718, by rfl⟩ : syracuseStep 2138291 = 3207437) B3207437
theorem B630967 : Blo 630300 630967 := bstep (se 1 (by rfl) ⟨473225, by rfl⟩ : syracuseStep 630967 = 946451) B946451
theorem B630987 : Blo 630300 630987 := bstep (se 1 (by rfl) ⟨473240, by rfl⟩ : syracuseStep 630987 = 946481) B946481
theorem B630999 : Blo 630300 630999 := bstep (se 1 (by rfl) ⟨473249, by rfl⟩ : syracuseStep 630999 = 946499) B946499
theorem B631019 : Blo 630300 631019 := bstep (se 1 (by rfl) ⟨473264, by rfl⟩ : syracuseStep 631019 = 946529) B946529
theorem B631031 : Blo 630300 631031 := bstep (se 1 (by rfl) ⟨473273, by rfl⟩ : syracuseStep 631031 = 946547) B946547
theorem B631051 : Blo 630300 631051 := bstep (se 1 (by rfl) ⟨473288, by rfl⟩ : syracuseStep 631051 = 946577) B946577
theorem B631063 : Blo 630300 631063 := bstep (se 1 (by rfl) ⟨473297, by rfl⟩ : syracuseStep 631063 = 946595) B946595
theorem B4858147 : Blo 630300 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B631083 : Blo 630300 631083 := bstep (se 1 (by rfl) ⟨473312, by rfl⟩ : syracuseStep 631083 = 946625) B946625
theorem B631095 : Blo 630300 631095 := bstep (se 1 (by rfl) ⟨473321, by rfl⟩ : syracuseStep 631095 = 946643) B946643
theorem B631115 : Blo 630300 631115 := bstep (se 1 (by rfl) ⟨473336, by rfl⟩ : syracuseStep 631115 = 946673) B946673
theorem B1352011 : Blo 630300 1352011 := bstep (se 1 (by rfl) ⟨1014008, by rfl⟩ : syracuseStep 1352011 = 2028017) B2028017
theorem B631127 : Blo 630300 631127 := bstep (se 1 (by rfl) ⟨473345, by rfl⟩ : syracuseStep 631127 = 946691) B946691
theorem B631147 : Blo 630300 631147 := bstep (se 1 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 631147 = 946721) B946721
theorem B631159 : Blo 630300 631159 := bstep (se 1 (by rfl) ⟨473369, by rfl⟩ : syracuseStep 631159 = 946739) B946739
theorem B631179 : Blo 630300 631179 := bstep (se 1 (by rfl) ⟨473384, by rfl⟩ : syracuseStep 631179 = 946769) B946769
theorem B631191 : Blo 630300 631191 := bstep (se 1 (by rfl) ⟨473393, by rfl⟩ : syracuseStep 631191 = 946787) B946787
theorem B631211 : Blo 630300 631211 := bstep (se 1 (by rfl) ⟨473408, by rfl⟩ : syracuseStep 631211 = 946817) B946817
theorem B631223 : Blo 630300 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B2138561 : Blo 630300 2138561 := bstep (se 2 (by rfl) ⟨801960, by rfl⟩ : syracuseStep 2138561 = 1603921) B1603921
theorem B631243 : Blo 630300 631243 := bstep (se 1 (by rfl) ⟨473432, by rfl⟩ : syracuseStep 631243 = 946865) B946865
theorem B631255 : Blo 630300 631255 := bstep (se 1 (by rfl) ⟨473441, by rfl⟩ : syracuseStep 631255 = 946883) B946883
theorem B631275 : Blo 630300 631275 := bstep (se 1 (by rfl) ⟨473456, by rfl⟩ : syracuseStep 631275 = 946913) B946913
theorem B631287 : Blo 630300 631287 := bstep (se 1 (by rfl) ⟨473465, by rfl⟩ : syracuseStep 631287 = 946931) B946931
theorem B631307 : Blo 630300 631307 := bstep (se 1 (by rfl) ⟨473480, by rfl⟩ : syracuseStep 631307 = 946961) B946961
theorem B631319 : Blo 630300 631319 := bstep (se 1 (by rfl) ⟨473489, by rfl⟩ : syracuseStep 631319 = 946979) B946979
theorem B631339 : Blo 630300 631339 := bstep (se 1 (by rfl) ⟨473504, by rfl⟩ : syracuseStep 631339 = 947009) B947009
theorem B631351 : Blo 630300 631351 := bstep (se 1 (by rfl) ⟨473513, by rfl⟩ : syracuseStep 631351 = 947027) B947027
theorem B631371 : Blo 630300 631371 := bstep (se 1 (by rfl) ⟨473528, by rfl⟩ : syracuseStep 631371 = 947057) B947057
theorem B631383 : Blo 630300 631383 := bstep (se 1 (by rfl) ⟨473537, by rfl⟩ : syracuseStep 631383 = 947075) B947075
theorem B1712729 : Blo 630300 1712729 := bstep (se 2 (by rfl) ⟨642273, by rfl⟩ : syracuseStep 1712729 = 1284547) B1284547
theorem B631403 : Blo 630300 631403 := bstep (se 1 (by rfl) ⟨473552, by rfl⟩ : syracuseStep 631403 = 947105) B947105
theorem B631415 : Blo 630300 631415 := bstep (se 1 (by rfl) ⟨473561, by rfl⟩ : syracuseStep 631415 = 947123) B947123
theorem B631435 : Blo 630300 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B631447 : Blo 630300 631447 := bstep (se 1 (by rfl) ⟨473585, by rfl⟩ : syracuseStep 631447 = 947171) B947171
theorem B959129 : Blo 630300 959129 := bstep (se 2 (by rfl) ⟨359673, by rfl⟩ : syracuseStep 959129 = 719347) B719347
theorem B631467 : Blo 630300 631467 := bstep (se 1 (by rfl) ⟨473600, by rfl⟩ : syracuseStep 631467 = 947201) B947201
theorem B2400947 : Blo 630300 2400947 := bstep (se 1 (by rfl) ⟨1800710, by rfl⟩ : syracuseStep 2400947 = 3601421) B3601421
theorem B631479 : Blo 630300 631479 := bstep (se 1 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 631479 = 947219) B947219
theorem B2400961 : Blo 630300 2400961 := bstep (se 2 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 2400961 = 1800721) B1800721
theorem B631499 : Blo 630300 631499 := bstep (se 1 (by rfl) ⟨473624, by rfl⟩ : syracuseStep 631499 = 947249) B947249
theorem B631511 : Blo 630300 631511 := bstep (se 1 (by rfl) ⟨473633, by rfl⟩ : syracuseStep 631511 = 947267) B947267
theorem B631531 : Blo 630300 631531 := bstep (se 1 (by rfl) ⟨473648, by rfl⟩ : syracuseStep 631531 = 947297) B947297
theorem B631543 : Blo 630300 631543 := bstep (se 1 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 631543 = 947315) B947315
theorem B631563 : Blo 630300 631563 := bstep (se 1 (by rfl) ⟨473672, by rfl⟩ : syracuseStep 631563 = 947345) B947345
theorem B631575 : Blo 630300 631575 := bstep (se 1 (by rfl) ⟨473681, by rfl⟩ : syracuseStep 631575 = 947363) B947363
theorem B631595 : Blo 630300 631595 := bstep (se 1 (by rfl) ⟨473696, by rfl⟩ : syracuseStep 631595 = 947393) B947393
theorem B631607 : Blo 630300 631607 := bstep (se 1 (by rfl) ⟨473705, by rfl⟩ : syracuseStep 631607 = 947411) B947411
theorem B631627 : Blo 630300 631627 := bstep (se 1 (by rfl) ⟨473720, by rfl⟩ : syracuseStep 631627 = 947441) B947441
theorem B631639 : Blo 630300 631639 := bstep (se 1 (by rfl) ⟨473729, by rfl⟩ : syracuseStep 631639 = 947459) B947459
theorem B631659 : Blo 630300 631659 := bstep (se 1 (by rfl) ⟨473744, by rfl⟩ : syracuseStep 631659 = 947489) B947489
theorem B631671 : Blo 630300 631671 := bstep (se 1 (by rfl) ⟨473753, by rfl⟩ : syracuseStep 631671 = 947507) B947507
theorem B631691 : Blo 630300 631691 := bstep (se 1 (by rfl) ⟨473768, by rfl⟩ : syracuseStep 631691 = 947537) B947537
theorem B631703 : Blo 630300 631703 := bstep (se 1 (by rfl) ⟨473777, by rfl⟩ : syracuseStep 631703 = 947555) B947555
theorem B631723 : Blo 630300 631723 := bstep (se 1 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 631723 = 947585) B947585
theorem B631735 : Blo 630300 631735 := bstep (se 1 (by rfl) ⟨473801, by rfl⟩ : syracuseStep 631735 = 947603) B947603
theorem B631755 : Blo 630300 631755 := bstep (se 1 (by rfl) ⟨473816, by rfl⟩ : syracuseStep 631755 = 947633) B947633
theorem B631767 : Blo 630300 631767 := bstep (se 1 (by rfl) ⟨473825, by rfl⟩ : syracuseStep 631767 = 947651) B947651
theorem B1418201 : Blo 630300 1418201 := bstep (se 2 (by rfl) ⟨531825, by rfl⟩ : syracuseStep 1418201 = 1063651) B1063651
theorem B2139101 : Blo 630300 2139101 := bstep (se 3 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 2139101 = 802163) B802163
theorem B631787 : Blo 630300 631787 := bstep (se 1 (by rfl) ⟨473840, by rfl⟩ : syracuseStep 631787 = 947681) B947681
theorem B631799 : Blo 630300 631799 := bstep (se 1 (by rfl) ⟨473849, by rfl⟩ : syracuseStep 631799 = 947699) B947699
theorem B631819 : Blo 630300 631819 := bstep (se 1 (by rfl) ⟨473864, by rfl⟩ : syracuseStep 631819 = 947729) B947729
theorem B631831 : Blo 630300 631831 := bstep (se 1 (by rfl) ⟨473873, by rfl⟩ : syracuseStep 631831 = 947747) B947747
theorem B631851 : Blo 630300 631851 := bstep (se 1 (by rfl) ⟨473888, by rfl⟩ : syracuseStep 631851 = 947777) B947777
theorem B1418291 : Blo 630300 1418291 := bstep (se 1 (by rfl) ⟨1063718, by rfl⟩ : syracuseStep 1418291 = 2127437) B2127437
theorem B631863 : Blo 630300 631863 := bstep (se 1 (by rfl) ⟨473897, by rfl⟩ : syracuseStep 631863 = 947795) B947795
theorem B631883 : Blo 630300 631883 := bstep (se 1 (by rfl) ⟨473912, by rfl⟩ : syracuseStep 631883 = 947825) B947825
theorem B1418327 : Blo 630300 1418327 := bstep (se 1 (by rfl) ⟨1063745, by rfl⟩ : syracuseStep 1418327 = 2127491) B2127491
theorem B631895 : Blo 630300 631895 := bstep (se 1 (by rfl) ⟨473921, by rfl⟩ : syracuseStep 631895 = 947843) B947843
theorem B3646565 : Blo 630300 3646565 := bstep (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) B683731
theorem B631915 : Blo 630300 631915 := bstep (se 1 (by rfl) ⟨473936, by rfl⟩ : syracuseStep 631915 = 947873) B947873
theorem B631927 : Blo 630300 631927 := bstep (se 1 (by rfl) ⟨473945, by rfl⟩ : syracuseStep 631927 = 947891) B947891
theorem B631947 : Blo 630300 631947 := bstep (se 1 (by rfl) ⟨473960, by rfl⟩ : syracuseStep 631947 = 947921) B947921
theorem B631959 : Blo 630300 631959 := bstep (se 1 (by rfl) ⟨473969, by rfl⟩ : syracuseStep 631959 = 947939) B947939
theorem B1352857 : Blo 630300 1352857 := bstep (se 2 (by rfl) ⟨507321, by rfl⟩ : syracuseStep 1352857 = 1014643) B1014643
theorem B631979 : Blo 630300 631979 := bstep (se 1 (by rfl) ⟨473984, by rfl⟩ : syracuseStep 631979 = 947969) B947969
theorem B631991 : Blo 630300 631991 := bstep (se 1 (by rfl) ⟨473993, by rfl⟩ : syracuseStep 631991 = 947987) B947987
theorem B632011 : Blo 630300 632011 := bstep (se 1 (by rfl) ⟨474008, by rfl⟩ : syracuseStep 632011 = 948017) B948017
theorem B632023 : Blo 630300 632023 := bstep (se 1 (by rfl) ⟨474017, by rfl⟩ : syracuseStep 632023 = 948035) B948035
theorem B632043 : Blo 630300 632043 := bstep (se 1 (by rfl) ⟨474032, by rfl⟩ : syracuseStep 632043 = 948065) B948065
theorem B632055 : Blo 630300 632055 := bstep (se 1 (by rfl) ⟨474041, by rfl⟩ : syracuseStep 632055 = 948083) B948083
theorem B1418507 : Blo 630300 1418507 := bstep (se 1 (by rfl) ⟨1063880, by rfl⟩ : syracuseStep 1418507 = 2127761) B2127761
theorem B632075 : Blo 630300 632075 := bstep (se 1 (by rfl) ⟨474056, by rfl⟩ : syracuseStep 632075 = 948113) B948113
theorem B632087 : Blo 630300 632087 := bstep (se 1 (by rfl) ⟨474065, by rfl⟩ : syracuseStep 632087 = 948131) B948131
theorem B1713431 : Blo 630300 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B632107 : Blo 630300 632107 := bstep (se 1 (by rfl) ⟨474080, by rfl⟩ : syracuseStep 632107 = 948161) B948161
theorem B632119 : Blo 630300 632119 := bstep (se 1 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 632119 = 948179) B948179
theorem B1418561 : Blo 630300 1418561 := bstep (se 2 (by rfl) ⟨531960, by rfl⟩ : syracuseStep 1418561 = 1063921) B1063921
theorem B632139 : Blo 630300 632139 := bstep (se 1 (by rfl) ⟨474104, by rfl⟩ : syracuseStep 632139 = 948209) B948209
theorem B632151 : Blo 630300 632151 := bstep (se 1 (by rfl) ⟨474113, by rfl⟩ : syracuseStep 632151 = 948227) B948227
theorem B632171 : Blo 630300 632171 := bstep (se 1 (by rfl) ⟨474128, by rfl⟩ : syracuseStep 632171 = 948257) B948257
theorem B632183 : Blo 630300 632183 := bstep (se 1 (by rfl) ⟨474137, by rfl⟩ : syracuseStep 632183 = 948275) B948275
theorem B632203 : Blo 630300 632203 := bstep (se 1 (by rfl) ⟨474152, by rfl⟩ : syracuseStep 632203 = 948305) B948305
theorem B632215 : Blo 630300 632215 := bstep (se 1 (by rfl) ⟨474161, by rfl⟩ : syracuseStep 632215 = 948323) B948323
theorem B632235 : Blo 630300 632235 := bstep (se 1 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 632235 = 948353) B948353
theorem B632247 : Blo 630300 632247 := bstep (se 1 (by rfl) ⟨474185, by rfl⟩ : syracuseStep 632247 = 948371) B948371
theorem B632267 : Blo 630300 632267 := bstep (se 1 (by rfl) ⟨474200, by rfl⟩ : syracuseStep 632267 = 948401) B948401
theorem B632279 : Blo 630300 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B632299 : Blo 630300 632299 := bstep (se 1 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 632299 = 948449) B948449
theorem B632311 : Blo 630300 632311 := bstep (se 1 (by rfl) ⟨474233, by rfl⟩ : syracuseStep 632311 = 948467) B948467
theorem B632331 : Blo 630300 632331 := bstep (se 1 (by rfl) ⟨474248, by rfl⟩ : syracuseStep 632331 = 948497) B948497
theorem B632343 : Blo 630300 632343 := bstep (se 1 (by rfl) ⟨474257, by rfl⟩ : syracuseStep 632343 = 948515) B948515
theorem B1418777 : Blo 630300 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B632363 : Blo 630300 632363 := bstep (se 1 (by rfl) ⟨474272, by rfl⟩ : syracuseStep 632363 = 948545) B948545
theorem B632375 : Blo 630300 632375 := bstep (se 1 (by rfl) ⟨474281, by rfl⟩ : syracuseStep 632375 = 948563) B948563
theorem B632395 : Blo 630300 632395 := bstep (se 1 (by rfl) ⟨474296, by rfl⟩ : syracuseStep 632395 = 948593) B948593
theorem B632407 : Blo 630300 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B632427 : Blo 630300 632427 := bstep (se 1 (by rfl) ⟨474320, by rfl⟩ : syracuseStep 632427 = 948641) B948641
theorem B1418867 : Blo 630300 1418867 := bstep (se 1 (by rfl) ⟨1064150, by rfl⟩ : syracuseStep 1418867 = 2128301) B2128301
theorem B632439 : Blo 630300 632439 := bstep (se 1 (by rfl) ⟨474329, by rfl⟩ : syracuseStep 632439 = 948659) B948659
theorem B632459 : Blo 630300 632459 := bstep (se 1 (by rfl) ⟨474344, by rfl⟩ : syracuseStep 632459 = 948689) B948689
theorem B1418903 : Blo 630300 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B632471 : Blo 630300 632471 := bstep (se 1 (by rfl) ⟨474353, by rfl⟩ : syracuseStep 632471 = 948707) B948707
theorem B632491 : Blo 630300 632491 := bstep (se 1 (by rfl) ⟨474368, by rfl⟩ : syracuseStep 632491 = 948737) B948737
theorem B632503 : Blo 630300 632503 := bstep (se 1 (by rfl) ⟨474377, by rfl⟩ : syracuseStep 632503 = 948755) B948755
theorem B632523 : Blo 630300 632523 := bstep (se 1 (by rfl) ⟨474392, by rfl⟩ : syracuseStep 632523 = 948785) B948785
theorem B632535 : Blo 630300 632535 := bstep (se 1 (by rfl) ⟨474401, by rfl⟩ : syracuseStep 632535 = 948803) B948803
theorem B960217 : Blo 630300 960217 := bstep (se 2 (by rfl) ⟨360081, by rfl⟩ : syracuseStep 960217 = 720163) B720163
theorem B632555 : Blo 630300 632555 := bstep (se 1 (by rfl) ⟨474416, by rfl⟩ : syracuseStep 632555 = 948833) B948833
theorem B632567 : Blo 630300 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B632587 : Blo 630300 632587 := bstep (se 1 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 632587 = 948881) B948881
theorem B632599 : Blo 630300 632599 := bstep (se 1 (by rfl) ⟨474449, by rfl⟩ : syracuseStep 632599 = 948899) B948899
theorem B632619 : Blo 630300 632619 := bstep (se 1 (by rfl) ⟨474464, by rfl⟩ : syracuseStep 632619 = 948929) B948929
theorem B632631 : Blo 630300 632631 := bstep (se 1 (by rfl) ⟨474473, by rfl⟩ : syracuseStep 632631 = 948947) B948947
theorem B1419083 : Blo 630300 1419083 := bstep (se 1 (by rfl) ⟨1064312, by rfl⟩ : syracuseStep 1419083 = 2128625) B2128625
theorem B632651 : Blo 630300 632651 := bstep (se 1 (by rfl) ⟨474488, by rfl⟩ : syracuseStep 632651 = 948977) B948977
theorem B632663 : Blo 630300 632663 := bstep (se 1 (by rfl) ⟨474497, by rfl⟩ : syracuseStep 632663 = 948995) B948995
theorem B632683 : Blo 630300 632683 := bstep (se 1 (by rfl) ⟨474512, by rfl⟩ : syracuseStep 632683 = 949025) B949025
theorem B632695 : Blo 630300 632695 := bstep (se 1 (by rfl) ⟨474521, by rfl⟩ : syracuseStep 632695 = 949043) B949043
theorem B1419137 : Blo 630300 1419137 := bstep (se 2 (by rfl) ⟨532176, by rfl⟩ : syracuseStep 1419137 = 1064353) B1064353
theorem B632715 : Blo 630300 632715 := bstep (se 1 (by rfl) ⟨474536, by rfl⟩ : syracuseStep 632715 = 949073) B949073
theorem B632727 : Blo 630300 632727 := bstep (se 1 (by rfl) ⟨474545, by rfl⟩ : syracuseStep 632727 = 949091) B949091
theorem B632747 : Blo 630300 632747 := bstep (se 1 (by rfl) ⟨474560, by rfl⟩ : syracuseStep 632747 = 949121) B949121
theorem B632759 : Blo 630300 632759 := bstep (se 1 (by rfl) ⟨474569, by rfl⟩ : syracuseStep 632759 = 949139) B949139
theorem B632779 : Blo 630300 632779 := bstep (se 1 (by rfl) ⟨474584, by rfl⟩ : syracuseStep 632779 = 949169) B949169
theorem B632791 : Blo 630300 632791 := bstep (se 1 (by rfl) ⟨474593, by rfl⟩ : syracuseStep 632791 = 949187) B949187
theorem B632811 : Blo 630300 632811 := bstep (se 1 (by rfl) ⟨474608, by rfl⟩ : syracuseStep 632811 = 949217) B949217
theorem B632823 : Blo 630300 632823 := bstep (se 1 (by rfl) ⟨474617, by rfl⟩ : syracuseStep 632823 = 949235) B949235
theorem B632843 : Blo 630300 632843 := bstep (se 1 (by rfl) ⟨474632, by rfl⟩ : syracuseStep 632843 = 949265) B949265
theorem B2697239 : Blo 630300 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B1517591 : Blo 630300 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B632855 : Blo 630300 632855 := bstep (se 1 (by rfl) ⟨474641, by rfl⟩ : syracuseStep 632855 = 949283) B949283
theorem B632875 : Blo 630300 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B632887 : Blo 630300 632887 := bstep (se 1 (by rfl) ⟨474665, by rfl⟩ : syracuseStep 632887 = 949331) B949331
theorem B632907 : Blo 630300 632907 := bstep (se 1 (by rfl) ⟨474680, by rfl⟩ : syracuseStep 632907 = 949361) B949361
theorem B2140235 : Blo 630300 2140235 := bstep (se 1 (by rfl) ⟨1605176, by rfl⟩ : syracuseStep 2140235 = 3210353) B3210353
theorem B632919 : Blo 630300 632919 := bstep (se 1 (by rfl) ⟨474689, by rfl⟩ : syracuseStep 632919 = 949379) B949379
theorem B1419353 : Blo 630300 1419353 := bstep (se 2 (by rfl) ⟨532257, by rfl⟩ : syracuseStep 1419353 = 1064515) B1064515
theorem B3418213 : Blo 630300 3418213 := bstep (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) B640915
theorem B632939 : Blo 630300 632939 := bstep (se 1 (by rfl) ⟨474704, by rfl⟩ : syracuseStep 632939 = 949409) B949409
theorem B632951 : Blo 630300 632951 := bstep (se 1 (by rfl) ⟨474713, by rfl⟩ : syracuseStep 632951 = 949427) B949427
theorem B632971 : Blo 630300 632971 := bstep (se 1 (by rfl) ⟨474728, by rfl⟩ : syracuseStep 632971 = 949457) B949457
theorem B632983 : Blo 630300 632983 := bstep (se 1 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 632983 = 949475) B949475
theorem B633003 : Blo 630300 633003 := bstep (se 1 (by rfl) ⟨474752, by rfl⟩ : syracuseStep 633003 = 949505) B949505
theorem B1419443 : Blo 630300 1419443 := bstep (se 1 (by rfl) ⟨1064582, by rfl⟩ : syracuseStep 1419443 = 2129165) B2129165
theorem B633015 : Blo 630300 633015 := bstep (se 1 (by rfl) ⟨474761, by rfl⟩ : syracuseStep 633015 = 949523) B949523
theorem B633035 : Blo 630300 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B1419479 : Blo 630300 1419479 := bstep (se 1 (by rfl) ⟨1064609, by rfl⟩ : syracuseStep 1419479 = 2129219) B2129219
theorem B633047 : Blo 630300 633047 := bstep (se 1 (by rfl) ⟨474785, by rfl⟩ : syracuseStep 633047 = 949571) B949571
theorem B633067 : Blo 630300 633067 := bstep (se 1 (by rfl) ⟨474800, by rfl⟩ : syracuseStep 633067 = 949601) B949601
theorem B633079 : Blo 630300 633079 := bstep (se 1 (by rfl) ⟨474809, by rfl⟩ : syracuseStep 633079 = 949619) B949619
theorem B633099 : Blo 630300 633099 := bstep (se 1 (by rfl) ⟨474824, by rfl⟩ : syracuseStep 633099 = 949649) B949649
theorem B633111 : Blo 630300 633111 := bstep (se 1 (by rfl) ⟨474833, by rfl⟩ : syracuseStep 633111 = 949667) B949667
theorem B633131 : Blo 630300 633131 := bstep (se 1 (by rfl) ⟨474848, by rfl⟩ : syracuseStep 633131 = 949697) B949697
theorem B633143 : Blo 630300 633143 := bstep (se 1 (by rfl) ⟨474857, by rfl⟩ : syracuseStep 633143 = 949715) B949715
theorem B633163 : Blo 630300 633163 := bstep (se 1 (by rfl) ⟨474872, by rfl⟩ : syracuseStep 633163 = 949745) B949745
theorem B633175 : Blo 630300 633175 := bstep (se 1 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 633175 = 949763) B949763
theorem B2140505 : Blo 630300 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B633195 : Blo 630300 633195 := bstep (se 1 (by rfl) ⟨474896, by rfl⟩ : syracuseStep 633195 = 949793) B949793
theorem B633207 : Blo 630300 633207 := bstep (se 1 (by rfl) ⟨474905, by rfl⟩ : syracuseStep 633207 = 949811) B949811
theorem B1419659 : Blo 630300 1419659 := bstep (se 1 (by rfl) ⟨1064744, by rfl⟩ : syracuseStep 1419659 = 2129489) B2129489
theorem B633227 : Blo 630300 633227 := bstep (se 1 (by rfl) ⟨474920, by rfl⟩ : syracuseStep 633227 = 949841) B949841
theorem B633239 : Blo 630300 633239 := bstep (se 1 (by rfl) ⟨474929, by rfl⟩ : syracuseStep 633239 = 949859) B949859
theorem B633259 : Blo 630300 633259 := bstep (se 1 (by rfl) ⟨474944, by rfl⟩ : syracuseStep 633259 = 949889) B949889
theorem B1354163 : Blo 630300 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B633271 : Blo 630300 633271 := bstep (se 1 (by rfl) ⟨474953, by rfl⟩ : syracuseStep 633271 = 949907) B949907
theorem B1419713 : Blo 630300 1419713 := bstep (se 2 (by rfl) ⟨532392, by rfl⟩ : syracuseStep 1419713 = 1064785) B1064785
theorem B633291 : Blo 630300 633291 := bstep (se 1 (by rfl) ⟨474968, by rfl⟩ : syracuseStep 633291 = 949937) B949937
theorem B633303 : Blo 630300 633303 := bstep (se 1 (by rfl) ⟨474977, by rfl⟩ : syracuseStep 633303 = 949955) B949955
theorem B633323 : Blo 630300 633323 := bstep (se 1 (by rfl) ⟨474992, by rfl⟩ : syracuseStep 633323 = 949985) B949985
theorem B633335 : Blo 630300 633335 := bstep (se 1 (by rfl) ⟨475001, by rfl⟩ : syracuseStep 633335 = 950003) B950003
theorem B633355 : Blo 630300 633355 := bstep (se 1 (by rfl) ⟨475016, by rfl⟩ : syracuseStep 633355 = 950033) B950033
theorem B633367 : Blo 630300 633367 := bstep (se 1 (by rfl) ⟨475025, by rfl⟩ : syracuseStep 633367 = 950051) B950051
theorem B633387 : Blo 630300 633387 := bstep (se 1 (by rfl) ⟨475040, by rfl⟩ : syracuseStep 633387 = 950081) B950081
theorem B633399 : Blo 630300 633399 := bstep (se 1 (by rfl) ⟨475049, by rfl⟩ : syracuseStep 633399 = 950099) B950099
theorem B2402891 : Blo 630300 2402891 := bstep (se 1 (by rfl) ⟨1802168, by rfl⟩ : syracuseStep 2402891 = 3604337) B3604337
theorem B633419 : Blo 630300 633419 := bstep (se 1 (by rfl) ⟨475064, by rfl⟩ : syracuseStep 633419 = 950129) B950129
theorem B633431 : Blo 630300 633431 := bstep (se 1 (by rfl) ⟨475073, by rfl⟩ : syracuseStep 633431 = 950147) B950147
theorem B2402905 : Blo 630300 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B633451 : Blo 630300 633451 := bstep (se 1 (by rfl) ⟨475088, by rfl⟩ : syracuseStep 633451 = 950177) B950177
theorem B633463 : Blo 630300 633463 := bstep (se 1 (by rfl) ⟨475097, by rfl⟩ : syracuseStep 633463 = 950195) B950195
theorem B633483 : Blo 630300 633483 := bstep (se 1 (by rfl) ⟨475112, by rfl⟩ : syracuseStep 633483 = 950225) B950225
theorem B633495 : Blo 630300 633495 := bstep (se 1 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 633495 = 950243) B950243
theorem B1419929 : Blo 630300 1419929 := bstep (se 2 (by rfl) ⟨532473, by rfl⟩ : syracuseStep 1419929 = 1064947) B1064947
theorem B633515 : Blo 630300 633515 := bstep (se 1 (by rfl) ⟨475136, by rfl⟩ : syracuseStep 633515 = 950273) B950273
theorem B633527 : Blo 630300 633527 := bstep (se 1 (by rfl) ⟨475145, by rfl⟩ : syracuseStep 633527 = 950291) B950291
theorem B633547 : Blo 630300 633547 := bstep (se 1 (by rfl) ⟨475160, by rfl⟩ : syracuseStep 633547 = 950321) B950321
theorem B633559 : Blo 630300 633559 := bstep (se 1 (by rfl) ⟨475169, by rfl⟩ : syracuseStep 633559 = 950339) B950339
theorem B633579 : Blo 630300 633579 := bstep (se 1 (by rfl) ⟨475184, by rfl⟩ : syracuseStep 633579 = 950369) B950369
theorem B1420019 : Blo 630300 1420019 := bstep (se 1 (by rfl) ⟨1065014, by rfl⟩ : syracuseStep 1420019 = 2130029) B2130029
theorem B633591 : Blo 630300 633591 := bstep (se 1 (by rfl) ⟨475193, by rfl⟩ : syracuseStep 633591 = 950387) B950387
theorem B633611 : Blo 630300 633611 := bstep (se 1 (by rfl) ⟨475208, by rfl⟩ : syracuseStep 633611 = 950417) B950417
theorem B1420055 : Blo 630300 1420055 := bstep (se 1 (by rfl) ⟨1065041, by rfl⟩ : syracuseStep 1420055 = 2130083) B2130083
theorem B1518359 : Blo 630300 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B633623 : Blo 630300 633623 := bstep (se 1 (by rfl) ⟨475217, by rfl⟩ : syracuseStep 633623 = 950435) B950435
theorem B633643 : Blo 630300 633643 := bstep (se 1 (by rfl) ⟨475232, by rfl⟩ : syracuseStep 633643 = 950465) B950465
theorem B633655 : Blo 630300 633655 := bstep (se 1 (by rfl) ⟨475241, by rfl⟩ : syracuseStep 633655 = 950483) B950483
theorem B633675 : Blo 630300 633675 := bstep (se 1 (by rfl) ⟨475256, by rfl⟩ : syracuseStep 633675 = 950513) B950513
theorem B633687 : Blo 630300 633687 := bstep (se 1 (by rfl) ⟨475265, by rfl⟩ : syracuseStep 633687 = 950531) B950531
theorem B633707 : Blo 630300 633707 := bstep (se 1 (by rfl) ⟨475280, by rfl⟩ : syracuseStep 633707 = 950561) B950561
theorem B633719 : Blo 630300 633719 := bstep (se 1 (by rfl) ⟨475289, by rfl⟩ : syracuseStep 633719 = 950579) B950579
theorem B633739 : Blo 630300 633739 := bstep (se 1 (by rfl) ⟨475304, by rfl⟩ : syracuseStep 633739 = 950609) B950609
theorem B633751 : Blo 630300 633751 := bstep (se 1 (by rfl) ⟨475313, by rfl⟩ : syracuseStep 633751 = 950627) B950627
theorem B633771 : Blo 630300 633771 := bstep (se 1 (by rfl) ⟨475328, by rfl⟩ : syracuseStep 633771 = 950657) B950657
theorem B633783 : Blo 630300 633783 := bstep (se 1 (by rfl) ⟨475337, by rfl⟩ : syracuseStep 633783 = 950675) B950675
theorem B1420235 : Blo 630300 1420235 := bstep (se 1 (by rfl) ⟨1065176, by rfl⟩ : syracuseStep 1420235 = 2130353) B2130353
theorem B633803 : Blo 630300 633803 := bstep (se 1 (by rfl) ⟨475352, by rfl⟩ : syracuseStep 633803 = 950705) B950705
theorem B633815 : Blo 630300 633815 := bstep (se 1 (by rfl) ⟨475361, by rfl⟩ : syracuseStep 633815 = 950723) B950723
theorem B633835 : Blo 630300 633835 := bstep (se 1 (by rfl) ⟨475376, by rfl⟩ : syracuseStep 633835 = 950753) B950753
theorem B633847 : Blo 630300 633847 := bstep (se 1 (by rfl) ⟨475385, by rfl⟩ : syracuseStep 633847 = 950771) B950771
theorem B1420289 : Blo 630300 1420289 := bstep (se 2 (by rfl) ⟨532608, by rfl⟩ : syracuseStep 1420289 = 1065217) B1065217
theorem B633867 : Blo 630300 633867 := bstep (se 1 (by rfl) ⟨475400, by rfl⟩ : syracuseStep 633867 = 950801) B950801
theorem B633879 : Blo 630300 633879 := bstep (se 1 (by rfl) ⟨475409, by rfl⟩ : syracuseStep 633879 = 950819) B950819
theorem B633899 : Blo 630300 633899 := bstep (se 1 (by rfl) ⟨475424, by rfl⟩ : syracuseStep 633899 = 950849) B950849
theorem B633911 : Blo 630300 633911 := bstep (se 1 (by rfl) ⟨475433, by rfl⟩ : syracuseStep 633911 = 950867) B950867
theorem B633931 : Blo 630300 633931 := bstep (se 1 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 633931 = 950897) B950897
theorem B633943 : Blo 630300 633943 := bstep (se 1 (by rfl) ⟨475457, by rfl⟩ : syracuseStep 633943 = 950915) B950915
theorem B633963 : Blo 630300 633963 := bstep (se 1 (by rfl) ⟨475472, by rfl⟩ : syracuseStep 633963 = 950945) B950945
theorem B633975 : Blo 630300 633975 := bstep (se 1 (by rfl) ⟨475481, by rfl⟩ : syracuseStep 633975 = 950963) B950963
theorem B633995 : Blo 630300 633995 := bstep (se 1 (by rfl) ⟨475496, by rfl⟩ : syracuseStep 633995 = 950993) B950993
theorem B634007 : Blo 630300 634007 := bstep (se 1 (by rfl) ⟨475505, by rfl⟩ : syracuseStep 634007 = 951011) B951011
theorem B634027 : Blo 630300 634027 := bstep (se 1 (by rfl) ⟨475520, by rfl⟩ : syracuseStep 634027 = 951041) B951041
theorem B634039 : Blo 630300 634039 := bstep (se 1 (by rfl) ⟨475529, by rfl⟩ : syracuseStep 634039 = 951059) B951059
theorem B634059 : Blo 630300 634059 := bstep (se 1 (by rfl) ⟨475544, by rfl⟩ : syracuseStep 634059 = 951089) B951089
theorem B634071 : Blo 630300 634071 := bstep (se 1 (by rfl) ⟨475553, by rfl⟩ : syracuseStep 634071 = 951107) B951107
theorem B1420505 : Blo 630300 1420505 := bstep (se 2 (by rfl) ⟨532689, by rfl⟩ : syracuseStep 1420505 = 1065379) B1065379
theorem B634091 : Blo 630300 634091 := bstep (se 1 (by rfl) ⟨475568, by rfl⟩ : syracuseStep 634091 = 951137) B951137
theorem B634103 : Blo 630300 634103 := bstep (se 1 (by rfl) ⟨475577, by rfl⟩ : syracuseStep 634103 = 951155) B951155
theorem B634123 : Blo 630300 634123 := bstep (se 1 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 634123 = 951185) B951185
theorem B634135 : Blo 630300 634135 := bstep (se 1 (by rfl) ⟨475601, by rfl⟩ : syracuseStep 634135 = 951203) B951203
theorem B634155 : Blo 630300 634155 := bstep (se 1 (by rfl) ⟨475616, by rfl⟩ : syracuseStep 634155 = 951233) B951233
theorem B2305331 : Blo 630300 2305331 := bstep (se 1 (by rfl) ⟨1728998, by rfl⟩ : syracuseStep 2305331 = 3457997) B3457997
theorem B1420595 : Blo 630300 1420595 := bstep (se 1 (by rfl) ⟨1065446, by rfl⟩ : syracuseStep 1420595 = 2130893) B2130893
theorem B634167 : Blo 630300 634167 := bstep (se 1 (by rfl) ⟨475625, by rfl⟩ : syracuseStep 634167 = 951251) B951251
theorem B634187 : Blo 630300 634187 := bstep (se 1 (by rfl) ⟨475640, by rfl⟩ : syracuseStep 634187 = 951281) B951281
theorem B1420631 : Blo 630300 1420631 := bstep (se 1 (by rfl) ⟨1065473, by rfl⟩ : syracuseStep 1420631 = 2130947) B2130947
theorem B634199 : Blo 630300 634199 := bstep (se 1 (by rfl) ⟨475649, by rfl⟩ : syracuseStep 634199 = 951299) B951299
theorem B634219 : Blo 630300 634219 := bstep (se 1 (by rfl) ⟨475664, by rfl⟩ : syracuseStep 634219 = 951329) B951329
theorem B634231 : Blo 630300 634231 := bstep (se 1 (by rfl) ⟨475673, by rfl⟩ : syracuseStep 634231 = 951347) B951347
theorem B634251 : Blo 630300 634251 := bstep (se 1 (by rfl) ⟨475688, by rfl⟩ : syracuseStep 634251 = 951377) B951377
theorem B798103 : Blo 630300 798103 := bstep (se 1 (by rfl) ⟨598577, by rfl⟩ : syracuseStep 798103 = 1197155) B1197155
theorem B634263 : Blo 630300 634263 := bstep (se 1 (by rfl) ⟨475697, by rfl⟩ : syracuseStep 634263 = 951395) B951395
theorem B634283 : Blo 630300 634283 := bstep (se 1 (by rfl) ⟨475712, by rfl⟩ : syracuseStep 634283 = 951425) B951425
theorem B634295 : Blo 630300 634295 := bstep (se 1 (by rfl) ⟨475721, by rfl⟩ : syracuseStep 634295 = 951443) B951443
theorem B1420811 : Blo 630300 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B2403863 : Blo 630300 2403863 := bstep (se 1 (by rfl) ⟨1802897, by rfl⟩ : syracuseStep 2403863 = 3605795) B3605795
theorem B1420865 : Blo 630300 1420865 := bstep (se 2 (by rfl) ⟨532824, by rfl⟩ : syracuseStep 1420865 = 1065649) B1065649
theorem B4992691 : Blo 630300 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B1421081 : Blo 630300 1421081 := bstep (se 2 (by rfl) ⟨532905, by rfl⟩ : syracuseStep 1421081 = 1065811) B1065811
theorem B31272803 : Blo 630300 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B1421171 : Blo 630300 1421171 := bstep (se 1 (by rfl) ⟨1065878, by rfl⟩ : syracuseStep 1421171 = 2131757) B2131757
theorem B2699153 : Blo 630300 2699153 := bstep (se 2 (by rfl) ⟨1012182, by rfl⟩ : syracuseStep 2699153 = 2024365) B2024365
theorem B1421207 : Blo 630300 1421207 := bstep (se 1 (by rfl) ⟨1065905, by rfl⟩ : syracuseStep 1421207 = 2131811) B2131811
theorem B10825649 : Blo 630300 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B1421387 : Blo 630300 1421387 := bstep (se 1 (by rfl) ⟨1066040, by rfl⟩ : syracuseStep 1421387 = 2132081) B2132081
theorem B1421441 : Blo 630300 1421441 := bstep (se 2 (by rfl) ⟨533040, by rfl⟩ : syracuseStep 1421441 = 1066081) B1066081
theorem B8106115 : Blo 630300 8106115 := bstep (se 1 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 8106115 = 12159173) B12159173
theorem B798923 : Blo 630300 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B5386445 : Blo 630300 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B3420377 : Blo 630300 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B6828293 : Blo 630300 6828293 := bstep (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) B1280305
theorem B3420461 : Blo 630300 3420461 := bstep (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) B1282673
theorem B1421657 : Blo 630300 1421657 := bstep (se 2 (by rfl) ⟨533121, by rfl⟩ : syracuseStep 1421657 = 1066243) B1066243
theorem B1421747 : Blo 630300 1421747 := bstep (se 1 (by rfl) ⟨1066310, by rfl⟩ : syracuseStep 1421747 = 2132621) B2132621
theorem B1421783 : Blo 630300 1421783 := bstep (se 1 (by rfl) ⟨1066337, by rfl⟩ : syracuseStep 1421783 = 2132675) B2132675
theorem B22196753 : Blo 630300 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B1421963 : Blo 630300 1421963 := bstep (se 1 (by rfl) ⟨1066472, by rfl⟩ : syracuseStep 1421963 = 2132945) B2132945
theorem B1422017 : Blo 630300 1422017 := bstep (se 2 (by rfl) ⟨533256, by rfl⟩ : syracuseStep 1422017 = 1066513) B1066513
theorem B5780173 : Blo 630300 5780173 := bstep (se 3 (by rfl) ⟨1083782, by rfl⟩ : syracuseStep 5780173 = 2167565) B2167565
theorem B2405123 : Blo 630300 2405123 := bstep (se 1 (by rfl) ⟨1803842, by rfl⟩ : syracuseStep 2405123 = 3607685) B3607685
theorem B2700125 : Blo 630300 2700125 := bstep (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) B1012547
theorem B799627 : Blo 630300 799627 := bstep (se 1 (by rfl) ⟨599720, by rfl⟩ : syracuseStep 799627 = 1199441) B1199441
theorem B1422233 : Blo 630300 1422233 := bstep (se 2 (by rfl) ⟨533337, by rfl⟩ : syracuseStep 1422233 = 1066675) B1066675
theorem B1422323 : Blo 630300 1422323 := bstep (se 1 (by rfl) ⟨1066742, by rfl⟩ : syracuseStep 1422323 = 2133485) B2133485
theorem B1422359 : Blo 630300 1422359 := bstep (se 1 (by rfl) ⟨1066769, by rfl⟩ : syracuseStep 1422359 = 2133539) B2133539
theorem B898123 : Blo 630300 898123 := bstep (se 1 (by rfl) ⟨673592, by rfl⟩ : syracuseStep 898123 = 1347185) B1347185
theorem B799895 : Blo 630300 799895 := bstep (se 1 (by rfl) ⟨599921, by rfl⟩ : syracuseStep 799895 = 1199843) B1199843
theorem B1422539 : Blo 630300 1422539 := bstep (se 1 (by rfl) ⟨1066904, by rfl⟩ : syracuseStep 1422539 = 2133809) B2133809
theorem B1422593 : Blo 630300 1422593 := bstep (se 2 (by rfl) ⟨533472, by rfl⟩ : syracuseStep 1422593 = 1066945) B1066945
theorem B1422809 : Blo 630300 1422809 := bstep (se 2 (by rfl) ⟨533553, by rfl⟩ : syracuseStep 1422809 = 1067107) B1067107
theorem B1422899 : Blo 630300 1422899 := bstep (se 1 (by rfl) ⟨1067174, by rfl⟩ : syracuseStep 1422899 = 2134349) B2134349
theorem B1422935 : Blo 630300 1422935 := bstep (se 1 (by rfl) ⟨1067201, by rfl⟩ : syracuseStep 1422935 = 2134403) B2134403
theorem B10368773 : Blo 630300 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B1423115 : Blo 630300 1423115 := bstep (se 1 (by rfl) ⟨1067336, by rfl⟩ : syracuseStep 1423115 = 2134673) B2134673
theorem B6076205 : Blo 630300 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B1423169 : Blo 630300 1423169 := bstep (se 2 (by rfl) ⟨533688, by rfl⟩ : syracuseStep 1423169 = 1067377) B1067377
theorem B3422017 : Blo 630300 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B800599 : Blo 630300 800599 := bstep (se 1 (by rfl) ⟨600449, by rfl⟩ : syracuseStep 800599 = 1200899) B1200899
theorem B1423385 : Blo 630300 1423385 := bstep (se 2 (by rfl) ⟨533769, by rfl⟩ : syracuseStep 1423385 = 1067539) B1067539
theorem B1423475 : Blo 630300 1423475 := bstep (se 1 (by rfl) ⟨1067606, by rfl⟩ : syracuseStep 1423475 = 2135213) B2135213
theorem B1423511 : Blo 630300 1423511 := bstep (se 1 (by rfl) ⟨1067633, by rfl⟩ : syracuseStep 1423511 = 2135267) B2135267
theorem B899353 : Blo 630300 899353 := bstep (se 2 (by rfl) ⟨337257, by rfl⟩ : syracuseStep 899353 = 674515) B674515
theorem B2701613 : Blo 630300 2701613 := bstep (se 3 (by rfl) ⟨506552, by rfl⟩ : syracuseStep 2701613 = 1013105) B1013105
theorem B1423691 : Blo 630300 1423691 := bstep (se 1 (by rfl) ⟨1067768, by rfl⟩ : syracuseStep 1423691 = 2135537) B2135537
theorem B3193181 : Blo 630300 3193181 := bstep (se 3 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 3193181 = 1197443) B1197443
theorem B1423745 : Blo 630300 1423745 := bstep (se 2 (by rfl) ⟨533904, by rfl⟩ : syracuseStep 1423745 = 1067809) B1067809
theorem B10271245 : Blo 630300 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B1423961 : Blo 630300 1423961 := bstep (se 2 (by rfl) ⟨533985, by rfl⟩ : syracuseStep 1423961 = 1067971) B1067971
theorem B1424051 : Blo 630300 1424051 := bstep (se 1 (by rfl) ⟨1068038, by rfl⟩ : syracuseStep 1424051 = 2136077) B2136077
theorem B1424087 : Blo 630300 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B4799249 : Blo 630300 4799249 := bstep (se 2 (by rfl) ⟨1799718, by rfl⟩ : syracuseStep 4799249 = 3599437) B3599437
theorem B1063705 : Blo 630300 1063705 := bstep (se 2 (by rfl) ⟨398889, by rfl⟩ : syracuseStep 1063705 = 797779) B797779
theorem B5192549 : Blo 630300 5192549 := bstep (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) B973603
theorem B1424267 : Blo 630300 1424267 := bstep (se 1 (by rfl) ⟨1068200, by rfl⟩ : syracuseStep 1424267 = 2136401) B2136401
theorem B1424321 : Blo 630300 1424321 := bstep (se 2 (by rfl) ⟨534120, by rfl⟩ : syracuseStep 1424321 = 1068241) B1068241
theorem B2276417 : Blo 630300 2276417 := bstep (se 2 (by rfl) ⟨853656, by rfl⟩ : syracuseStep 2276417 = 1707313) B1707313
theorem B1522763 : Blo 630300 1522763 := bstep (se 1 (by rfl) ⟨1142072, by rfl⟩ : syracuseStep 1522763 = 2284145) B2284145
theorem B900247 : Blo 630300 900247 := bstep (se 1 (by rfl) ⟨675185, by rfl⟩ : syracuseStep 900247 = 1350371) B1350371
theorem B6077591 : Blo 630300 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B1424537 : Blo 630300 1424537 := bstep (se 2 (by rfl) ⟨534201, by rfl⟩ : syracuseStep 1424537 = 1068403) B1068403
theorem B1424627 : Blo 630300 1424627 := bstep (se 1 (by rfl) ⟨1068470, by rfl⟩ : syracuseStep 1424627 = 2136941) B2136941
theorem B1424663 : Blo 630300 1424663 := bstep (se 1 (by rfl) ⟨1068497, by rfl⟩ : syracuseStep 1424663 = 2136995) B2136995
theorem B1064279 : Blo 630300 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B1424843 : Blo 630300 1424843 := bstep (se 1 (by rfl) ⟨1068632, by rfl⟩ : syracuseStep 1424843 = 2137265) B2137265
theorem B1064407 : Blo 630300 1064407 := bstep (se 1 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 1064407 = 1596611) B1596611
theorem B1424897 : Blo 630300 1424897 := bstep (se 2 (by rfl) ⟨534336, by rfl⟩ : syracuseStep 1424897 = 1068673) B1068673
theorem B802315 : Blo 630300 802315 := bstep (se 1 (by rfl) ⟨601736, by rfl⟩ : syracuseStep 802315 = 1203473) B1203473
theorem B3456605 : Blo 630300 3456605 := bstep (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) B1296227
theorem B900811 : Blo 630300 900811 := bstep (se 1 (by rfl) ⟨675608, by rfl⟩ : syracuseStep 900811 = 1351217) B1351217
theorem B1425113 : Blo 630300 1425113 := bstep (se 2 (by rfl) ⟨534417, by rfl⟩ : syracuseStep 1425113 = 1068835) B1068835
theorem B2408237 : Blo 630300 2408237 := bstep (se 3 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 2408237 = 903089) B903089
theorem B1425203 : Blo 630300 1425203 := bstep (se 1 (by rfl) ⟨1068902, by rfl⟩ : syracuseStep 1425203 = 2137805) B2137805
theorem B1523531 : Blo 630300 1523531 := bstep (se 1 (by rfl) ⟨1142648, by rfl⟩ : syracuseStep 1523531 = 2285297) B2285297
theorem B1425239 : Blo 630300 1425239 := bstep (se 1 (by rfl) ⟨1068929, by rfl⟩ : syracuseStep 1425239 = 2137859) B2137859
theorem B2277341 : Blo 630300 2277341 := bstep (se 3 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 2277341 = 854003) B854003
theorem B1425419 : Blo 630300 1425419 := bstep (se 1 (by rfl) ⟨1069064, by rfl⟩ : syracuseStep 1425419 = 2138129) B2138129
theorem B8306705 : Blo 630300 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1425473 : Blo 630300 1425473 := bstep (se 2 (by rfl) ⟨534552, by rfl⟩ : syracuseStep 1425473 = 1069105) B1069105
theorem B1065035 : Blo 630300 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1065163 : Blo 630300 1065163 := bstep (se 1 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 1065163 = 1597745) B1597745
theorem B2703577 : Blo 630300 2703577 := bstep (se 2 (by rfl) ⟨1013841, by rfl⟩ : syracuseStep 2703577 = 2027683) B2027683
theorem B1425689 : Blo 630300 1425689 := bstep (se 2 (by rfl) ⟨534633, by rfl⟩ : syracuseStep 1425689 = 1069267) B1069267
theorem B1065305 : Blo 630300 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B1425779 : Blo 630300 1425779 := bstep (se 1 (by rfl) ⟨1069334, by rfl⟩ : syracuseStep 1425779 = 2138669) B2138669
theorem B3195287 : Blo 630300 3195287 := bstep (se 1 (by rfl) ⟨2396465, by rfl⟩ : syracuseStep 3195287 = 4792931) B4792931
theorem B1425815 : Blo 630300 1425815 := bstep (se 1 (by rfl) ⟨1069361, by rfl⟩ : syracuseStep 1425815 = 2138723) B2138723
theorem B6472153 : Blo 630300 6472153 := bstep (se 2 (by rfl) ⟨2427057, by rfl⟩ : syracuseStep 6472153 = 4854115) B4854115
theorem B1065433 : Blo 630300 1065433 := bstep (se 2 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 1065433 = 799075) B799075
theorem B1851869 : Blo 630300 1851869 := bstep (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) B694451
theorem B3031627 : Blo 630300 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B1425995 : Blo 630300 1425995 := bstep (se 1 (by rfl) ⟨1069496, by rfl⟩ : syracuseStep 1425995 = 2138993) B2138993
theorem B1426049 : Blo 630300 1426049 := bstep (se 2 (by rfl) ⟨534768, by rfl⟩ : syracuseStep 1426049 = 1069537) B1069537
theorem B1196851 : Blo 630300 1196851 := bstep (se 1 (by rfl) ⟨897638, by rfl⟩ : syracuseStep 1196851 = 1795277) B1795277
theorem B1426265 : Blo 630300 1426265 := bstep (se 2 (by rfl) ⟨534849, by rfl⟩ : syracuseStep 1426265 = 1069699) B1069699
theorem B5391197 : Blo 630300 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1426355 : Blo 630300 1426355 := bstep (se 1 (by rfl) ⟨1069766, by rfl⟩ : syracuseStep 1426355 = 2139533) B2139533
theorem B1426391 : Blo 630300 1426391 := bstep (se 1 (by rfl) ⟨1069793, by rfl⟩ : syracuseStep 1426391 = 2139587) B2139587
theorem B1066007 : Blo 630300 1066007 := bstep (se 1 (by rfl) ⟨799505, by rfl⟩ : syracuseStep 1066007 = 1599011) B1599011
theorem B1426571 : Blo 630300 1426571 := bstep (se 1 (by rfl) ⟨1069928, by rfl⟩ : syracuseStep 1426571 = 2139857) B2139857
theorem B1066135 : Blo 630300 1066135 := bstep (se 1 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 1066135 = 1599203) B1599203
theorem B2704535 : Blo 630300 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B902297 : Blo 630300 902297 := bstep (se 2 (by rfl) ⟨338361, by rfl⟩ : syracuseStep 902297 = 676723) B676723
theorem B1426625 : Blo 630300 1426625 := bstep (se 2 (by rfl) ⟨534984, by rfl⟩ : syracuseStep 1426625 = 1069969) B1069969
theorem B1099019 : Blo 630300 1099019 := bstep (se 1 (by rfl) ⟨824264, by rfl⟩ : syracuseStep 1099019 = 1648529) B1648529
theorem B1197337 : Blo 630300 1197337 := bstep (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) B898003
theorem B1426841 : Blo 630300 1426841 := bstep (se 2 (by rfl) ⟨535065, by rfl⟩ : syracuseStep 1426841 = 1070131) B1070131
theorem B1426931 : Blo 630300 1426931 := bstep (se 1 (by rfl) ⟨1070198, by rfl⟩ : syracuseStep 1426931 = 2140397) B2140397
theorem B1426967 : Blo 630300 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B5490251 : Blo 630300 5490251 := bstep (se 1 (by rfl) ⟨4117688, by rfl⟩ : syracuseStep 5490251 = 8235377) B8235377
theorem B1918657 : Blo 630300 1918657 := bstep (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) B1438993
theorem B1427147 : Blo 630300 1427147 := bstep (se 1 (by rfl) ⟨1070360, by rfl⟩ : syracuseStep 1427147 = 2140721) B2140721
theorem B1066763 : Blo 630300 1066763 := bstep (se 1 (by rfl) ⟨800072, by rfl⟩ : syracuseStep 1066763 = 1600145) B1600145
theorem B902935 : Blo 630300 902935 := bstep (se 1 (by rfl) ⟨677201, by rfl⟩ : syracuseStep 902935 = 1354403) B1354403
theorem B673579 : Blo 630300 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B1197899 : Blo 630300 1197899 := bstep (se 1 (by rfl) ⟨898424, by rfl⟩ : syracuseStep 1197899 = 1796849) B1796849
theorem B16205669 : Blo 630300 16205669 := bstep (se 4 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 16205669 = 3038563) B3038563
theorem B2279299 : Blo 630300 2279299 := bstep (se 1 (by rfl) ⟨1709474, by rfl⟩ : syracuseStep 2279299 = 3418949) B3418949
theorem B1066891 : Blo 630300 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B1198081 : Blo 630300 1198081 := bstep (se 2 (by rfl) ⟨449280, by rfl⟩ : syracuseStep 1198081 = 898561) B898561
theorem B1067033 : Blo 630300 1067033 := bstep (se 2 (by rfl) ⟨400137, by rfl⟩ : syracuseStep 1067033 = 800275) B800275
theorem B3590189 : Blo 630300 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B6834307 : Blo 630300 6834307 := bstep (se 1 (by rfl) ⟨5125730, by rfl⟩ : syracuseStep 6834307 = 10251461) B10251461
theorem B1067161 : Blo 630300 1067161 := bstep (se 2 (by rfl) ⟨400185, by rfl⟩ : syracuseStep 1067161 = 800371) B800371
theorem B10799405 : Blo 630300 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B4803137 : Blo 630300 4803137 := bstep (se 2 (by rfl) ⟨1801176, by rfl⟩ : syracuseStep 4803137 = 3602353) B3602353
theorem B7195229 : Blo 630300 7195229 := bstep (se 3 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 7195229 = 2698211) B2698211
theorem B2083421 : Blo 630300 2083421 := bstep (se 3 (by rfl) ⟨390641, by rfl⟩ : syracuseStep 2083421 = 781283) B781283
theorem B1198795 : Blo 630300 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B1067735 : Blo 630300 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B1198871 : Blo 630300 1198871 := bstep (se 1 (by rfl) ⟨899153, by rfl⟩ : syracuseStep 1198871 = 1798307) B1798307
theorem B1067863 : Blo 630300 1067863 := bstep (se 1 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 1067863 = 1601795) B1601795
theorem B675211 : Blo 630300 675211 := bstep (se 1 (by rfl) ⟨506408, by rfl⟩ : syracuseStep 675211 = 1012817) B1012817
theorem B1199539 : Blo 630300 1199539 := bstep (se 1 (by rfl) ⟨899654, by rfl⟩ : syracuseStep 1199539 = 1799309) B1799309
theorem B1068491 : Blo 630300 1068491 := bstep (se 1 (by rfl) ⟨801368, by rfl⟩ : syracuseStep 1068491 = 1602737) B1602737
theorem B1068619 : Blo 630300 1068619 := bstep (se 1 (by rfl) ⟨801464, by rfl⟩ : syracuseStep 1068619 = 1602929) B1602929
theorem B1199767 : Blo 630300 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B1068761 : Blo 630300 1068761 := bstep (se 2 (by rfl) ⟨400785, by rfl⟩ : syracuseStep 1068761 = 801571) B801571
theorem B1199873 : Blo 630300 1199873 := bstep (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) B899905
theorem B1068889 : Blo 630300 1068889 := bstep (se 2 (by rfl) ⟨400833, by rfl⟩ : syracuseStep 1068889 = 801667) B801667
theorem B3198851 : Blo 630300 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B1200025 : Blo 630300 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B2019251 : Blo 630300 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B2019649 : Blo 630300 2019649 := bstep (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) B1514737
theorem B1069463 : Blo 630300 1069463 := bstep (se 1 (by rfl) ⟨802097, by rfl⟩ : syracuseStep 1069463 = 1604195) B1604195
theorem B2019763 : Blo 630300 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B676279 : Blo 630300 676279 := bstep (se 1 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 676279 = 1014419) B1014419
theorem B4805081 : Blo 630300 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B2707985 : Blo 630300 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B1069591 : Blo 630300 1069591 := bstep (se 1 (by rfl) ⟨802193, by rfl⟩ : syracuseStep 1069591 = 1604387) B1604387
theorem B709195 : Blo 630300 709195 := bstep (se 1 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 709195 = 1063793) B1063793
theorem B709303 : Blo 630300 709303 := bstep (se 1 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 709303 = 1063955) B1063955
theorem B709483 : Blo 630300 709483 := bstep (se 1 (by rfl) ⟨532112, by rfl⟩ : syracuseStep 709483 = 1064225) B1064225
theorem B709591 : Blo 630300 709591 := bstep (se 1 (by rfl) ⟨532193, by rfl⟩ : syracuseStep 709591 = 1064387) B1064387
theorem B709771 : Blo 630300 709771 := bstep (se 1 (by rfl) ⟨532328, by rfl⟩ : syracuseStep 709771 = 1064657) B1064657
theorem B1070219 : Blo 630300 1070219 := bstep (se 1 (by rfl) ⟨802664, by rfl⟩ : syracuseStep 1070219 = 1605329) B1605329
theorem B1201331 : Blo 630300 1201331 := bstep (se 1 (by rfl) ⟨900998, by rfl⟩ : syracuseStep 1201331 = 1801997) B1801997
theorem B677099 : Blo 630300 677099 := bstep (se 1 (by rfl) ⟨507824, by rfl⟩ : syracuseStep 677099 = 1015649) B1015649
theorem B709879 : Blo 630300 709879 := bstep (se 1 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 709879 = 1064819) B1064819
theorem B1070347 : Blo 630300 1070347 := bstep (se 1 (by rfl) ⟨802760, by rfl⟩ : syracuseStep 1070347 = 1605521) B1605521
theorem B1201483 : Blo 630300 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B1070425 : Blo 630300 1070425 := bstep (se 2 (by rfl) ⟨401409, by rfl⟩ : syracuseStep 1070425 = 802819) B802819
theorem B710059 : Blo 630300 710059 := bstep (se 1 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 710059 = 1065089) B1065089
theorem B2708909 : Blo 630300 2708909 := bstep (se 3 (by rfl) ⟨507920, by rfl⟩ : syracuseStep 2708909 = 1015841) B1015841
theorem B12998161 : Blo 630300 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B710167 : Blo 630300 710167 := bstep (se 1 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 710167 = 1065251) B1065251
theorem B1365643 : Blo 630300 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B3593879 : Blo 630300 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B1201817 : Blo 630300 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B710347 : Blo 630300 710347 := bstep (se 1 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 710347 = 1065521) B1065521
theorem B1234649 : Blo 630300 1234649 := bstep (se 2 (by rfl) ⟨462993, by rfl⟩ : syracuseStep 1234649 = 925987) B925987
theorem B4052753 : Blo 630300 4052753 := bstep (se 2 (by rfl) ⟨1519782, by rfl⟩ : syracuseStep 4052753 = 3039565) B3039565
theorem B710455 : Blo 630300 710455 := bstep (se 1 (by rfl) ⟨532841, by rfl⟩ : syracuseStep 710455 = 1065683) B1065683
theorem B710635 : Blo 630300 710635 := bstep (se 1 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 710635 = 1065953) B1065953
theorem B18176021 : Blo 630300 18176021 := bstep (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) B852001
theorem B710743 : Blo 630300 710743 := bstep (se 1 (by rfl) ⟨533057, by rfl⟩ : syracuseStep 710743 = 1066115) B1066115
theorem B1595609 : Blo 630300 1595609 := bstep (se 2 (by rfl) ⟨598353, by rfl⟩ : syracuseStep 1595609 = 1196707) B1196707
theorem B710923 : Blo 630300 710923 := bstep (se 1 (by rfl) ⟨533192, by rfl⟩ : syracuseStep 710923 = 1066385) B1066385
theorem B1202455 : Blo 630300 1202455 := bstep (se 1 (by rfl) ⟨901841, by rfl⟩ : syracuseStep 1202455 = 1803683) B1803683
theorem B809291 : Blo 630300 809291 := bstep (se 1 (by rfl) ⟨606968, by rfl⟩ : syracuseStep 809291 = 1213937) B1213937
theorem B711031 : Blo 630300 711031 := bstep (se 1 (by rfl) ⟨533273, by rfl⟩ : syracuseStep 711031 = 1066547) B1066547
theorem B711211 : Blo 630300 711211 := bstep (se 1 (by rfl) ⟨533408, by rfl⟩ : syracuseStep 711211 = 1066817) B1066817
theorem B711319 : Blo 630300 711319 := bstep (se 1 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 711319 = 1066979) B1066979
theorem B711499 : Blo 630300 711499 := bstep (se 1 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 711499 = 1067249) B1067249
theorem B1137559 : Blo 630300 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B711607 : Blo 630300 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B2284561 : Blo 630300 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B1203275 : Blo 630300 1203275 := bstep (se 1 (by rfl) ⟨902456, by rfl⟩ : syracuseStep 1203275 = 1804913) B1804913
theorem B711787 : Blo 630300 711787 := bstep (se 1 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 711787 = 1067681) B1067681
theorem B1203329 : Blo 630300 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B711895 : Blo 630300 711895 := bstep (se 1 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 711895 = 1067843) B1067843
theorem B712075 : Blo 630300 712075 := bstep (se 1 (by rfl) ⟨534056, by rfl⟩ : syracuseStep 712075 = 1068113) B1068113
theorem B119922061 : Blo 630300 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B712183 : Blo 630300 712183 := bstep (se 1 (by rfl) ⟨534137, by rfl⟩ : syracuseStep 712183 = 1068275) B1068275
theorem B3202577 : Blo 630300 3202577 := bstep (se 2 (by rfl) ⟨1200966, by rfl⟩ : syracuseStep 3202577 = 2401933) B2401933
theorem B712363 : Blo 630300 712363 := bstep (se 1 (by rfl) ⟨534272, by rfl⟩ : syracuseStep 712363 = 1068545) B1068545
theorem B3202739 : Blo 630300 3202739 := bstep (se 1 (by rfl) ⟨2402054, by rfl⟩ : syracuseStep 3202739 = 4804109) B4804109
theorem B712471 : Blo 630300 712471 := bstep (se 1 (by rfl) ⟨534353, by rfl⟩ : syracuseStep 712471 = 1068707) B1068707
theorem B4808483 : Blo 630300 4808483 := bstep (se 1 (by rfl) ⟨3606362, by rfl⟩ : syracuseStep 4808483 = 7212725) B7212725
theorem B1597259 : Blo 630300 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B712651 : Blo 630300 712651 := bstep (se 1 (by rfl) ⟨534488, by rfl⟩ : syracuseStep 712651 = 1068977) B1068977
theorem B712759 : Blo 630300 712759 := bstep (se 1 (by rfl) ⟨534569, by rfl⟩ : syracuseStep 712759 = 1069139) B1069139
theorem B712939 : Blo 630300 712939 := bstep (se 1 (by rfl) ⟨534704, by rfl⟩ : syracuseStep 712939 = 1069409) B1069409
theorem B713047 : Blo 630300 713047 := bstep (se 1 (by rfl) ⟨534785, by rfl⟩ : syracuseStep 713047 = 1069571) B1069571
theorem B713227 : Blo 630300 713227 := bstep (se 1 (by rfl) ⟨534920, by rfl⟩ : syracuseStep 713227 = 1069841) B1069841
theorem B713335 : Blo 630300 713335 := bstep (se 1 (by rfl) ⟨535001, by rfl⟩ : syracuseStep 713335 = 1070003) B1070003
theorem B1172183 : Blo 630300 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1598231 : Blo 630300 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B713515 : Blo 630300 713515 := bstep (se 1 (by rfl) ⟨535136, by rfl⟩ : syracuseStep 713515 = 1070273) B1070273
theorem B4875073 : Blo 630300 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B1598899 : Blo 630300 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1599041 : Blo 630300 1599041 := bstep (se 2 (by rfl) ⟨599640, by rfl⟩ : syracuseStep 1599041 = 1199281) B1199281
theorem B3204683 : Blo 630300 3204683 := bstep (se 1 (by rfl) ⟨2403512, by rfl⟩ : syracuseStep 3204683 = 4807025) B4807025
theorem B1402519 : Blo 630300 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B812759 : Blo 630300 812759 := bstep (se 1 (by rfl) ⟨609569, by rfl⟩ : syracuseStep 812759 = 1219139) B1219139
theorem B9135989 : Blo 630300 9135989 := bstep (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) B856499
theorem B5400593 : Blo 630300 5400593 := bstep (se 2 (by rfl) ⟨2025222, by rfl⟩ : syracuseStep 5400593 = 4050445) B4050445
theorem B4549081 : Blo 630300 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B1796701 : Blo 630300 1796701 := bstep (se 3 (by rfl) ⟨336881, by rfl⟩ : syracuseStep 1796701 = 673763) B673763
theorem B1600307 : Blo 630300 1600307 := bstep (se 1 (by rfl) ⟨1200230, by rfl⟩ : syracuseStep 1600307 = 2400461) B2400461
theorem B3599255 : Blo 630300 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B1928281 : Blo 630300 1928281 := bstep (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) B1446211
theorem B3206465 : Blo 630300 3206465 := bstep (se 2 (by rfl) ⟨1202424, by rfl⟩ : syracuseStep 3206465 = 2404849) B2404849
theorem B1600843 : Blo 630300 1600843 := bstep (se 1 (by rfl) ⟨1200632, by rfl⟩ : syracuseStep 1600843 = 2401265) B2401265
theorem B945497 : Blo 630300 945497 := bstep (se 2 (by rfl) ⟨354561, by rfl⟩ : syracuseStep 945497 = 709123) B709123
theorem B945611 : Blo 630300 945611 := bstep (se 1 (by rfl) ⟨709208, by rfl⟩ : syracuseStep 945611 = 1418417) B1418417
theorem B44330453 : Blo 630300 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B945623 : Blo 630300 945623 := bstep (se 1 (by rfl) ⟨709217, by rfl⟩ : syracuseStep 945623 = 1418435) B1418435
theorem B1600985 : Blo 630300 1600985 := bstep (se 2 (by rfl) ⟨600369, by rfl⟩ : syracuseStep 1600985 = 1200739) B1200739
theorem B945689 : Blo 630300 945689 := bstep (se 2 (by rfl) ⟨354633, by rfl⟩ : syracuseStep 945689 = 709267) B709267
theorem B945803 : Blo 630300 945803 := bstep (se 1 (by rfl) ⟨709352, by rfl⟩ : syracuseStep 945803 = 1418705) B1418705
theorem B945815 : Blo 630300 945815 := bstep (se 1 (by rfl) ⟨709361, by rfl⟩ : syracuseStep 945815 = 1418723) B1418723
theorem B2879155 : Blo 630300 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B945881 : Blo 630300 945881 := bstep (se 2 (by rfl) ⟨354705, by rfl⟩ : syracuseStep 945881 = 709411) B709411
theorem B945995 : Blo 630300 945995 := bstep (se 1 (by rfl) ⟨709496, by rfl⟩ : syracuseStep 945995 = 1418993) B1418993
theorem B2027339 : Blo 630300 2027339 := bstep (se 1 (by rfl) ⟨1520504, by rfl⟩ : syracuseStep 2027339 = 3041009) B3041009
theorem B946007 : Blo 630300 946007 := bstep (se 1 (by rfl) ⟨709505, by rfl⟩ : syracuseStep 946007 = 1419011) B1419011
theorem B1797977 : Blo 630300 1797977 := bstep (se 2 (by rfl) ⟨674241, by rfl⟩ : syracuseStep 1797977 = 1348483) B1348483
theorem B4058981 : Blo 630300 4058981 := bstep (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) B761059
theorem B946073 : Blo 630300 946073 := bstep (se 2 (by rfl) ⟨354777, by rfl⟩ : syracuseStep 946073 = 709555) B709555
theorem B946187 : Blo 630300 946187 := bstep (se 1 (by rfl) ⟨709640, by rfl⟩ : syracuseStep 946187 = 1419281) B1419281
theorem B946199 : Blo 630300 946199 := bstep (se 1 (by rfl) ⟨709649, by rfl⟩ : syracuseStep 946199 = 1419299) B1419299
theorem B17789003 : Blo 630300 17789003 := bstep (se 1 (by rfl) ⟨13341752, by rfl⟩ : syracuseStep 17789003 = 26683505) B26683505
theorem B946265 : Blo 630300 946265 := bstep (se 2 (by rfl) ⟨354849, by rfl⟩ : syracuseStep 946265 = 709699) B709699
theorem B946379 : Blo 630300 946379 := bstep (se 1 (by rfl) ⟨709784, by rfl⟩ : syracuseStep 946379 = 1419569) B1419569
theorem B946391 : Blo 630300 946391 := bstep (se 1 (by rfl) ⟨709793, by rfl⟩ : syracuseStep 946391 = 1419587) B1419587
theorem B913675 : Blo 630300 913675 := bstep (se 1 (by rfl) ⟨685256, by rfl⟩ : syracuseStep 913675 = 1370513) B1370513
theorem B1601815 : Blo 630300 1601815 := bstep (se 1 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 1601815 = 2402723) B2402723
theorem B946457 : Blo 630300 946457 := bstep (se 2 (by rfl) ⟨354921, by rfl⟩ : syracuseStep 946457 = 709843) B709843
theorem B4059467 : Blo 630300 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B946571 : Blo 630300 946571 := bstep (se 1 (by rfl) ⟨709928, by rfl⟩ : syracuseStep 946571 = 1419857) B1419857
theorem B946583 : Blo 630300 946583 := bstep (se 1 (by rfl) ⟨709937, by rfl⟩ : syracuseStep 946583 = 1419875) B1419875
theorem B946649 : Blo 630300 946649 := bstep (se 2 (by rfl) ⟨354993, by rfl⟩ : syracuseStep 946649 = 709987) B709987
theorem B2224691 : Blo 630300 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B946763 : Blo 630300 946763 := bstep (se 1 (by rfl) ⟨710072, by rfl⟩ : syracuseStep 946763 = 1420145) B1420145
theorem B946775 : Blo 630300 946775 := bstep (se 1 (by rfl) ⟨710081, by rfl⟩ : syracuseStep 946775 = 1420163) B1420163
theorem B946841 : Blo 630300 946841 := bstep (se 2 (by rfl) ⟨355065, by rfl⟩ : syracuseStep 946841 = 710131) B710131
theorem B1438411 : Blo 630300 1438411 := bstep (se 1 (by rfl) ⟨1078808, by rfl⟩ : syracuseStep 1438411 = 2157617) B2157617
theorem B1602251 : Blo 630300 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B1012439 : Blo 630300 1012439 := bstep (se 1 (by rfl) ⟨759329, by rfl⟩ : syracuseStep 1012439 = 1518659) B1518659
theorem B946955 : Blo 630300 946955 := bstep (se 1 (by rfl) ⟨710216, by rfl⟩ : syracuseStep 946955 = 1420433) B1420433
theorem B3601169 : Blo 630300 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B946967 : Blo 630300 946967 := bstep (se 1 (by rfl) ⟨710225, by rfl⟩ : syracuseStep 946967 = 1420451) B1420451
theorem B947033 : Blo 630300 947033 := bstep (se 2 (by rfl) ⟨355137, by rfl⟩ : syracuseStep 947033 = 710275) B710275
theorem B947147 : Blo 630300 947147 := bstep (se 1 (by rfl) ⟨710360, by rfl⟩ : syracuseStep 947147 = 1420721) B1420721
theorem B947159 : Blo 630300 947159 := bstep (se 1 (by rfl) ⟨710369, by rfl⟩ : syracuseStep 947159 = 1420739) B1420739
theorem B4813829 : Blo 630300 4813829 := bstep (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) B902593
theorem B10417169 : Blo 630300 10417169 := bstep (se 2 (by rfl) ⟨3906438, by rfl⟩ : syracuseStep 10417169 = 7812877) B7812877
theorem B947225 : Blo 630300 947225 := bstep (se 2 (by rfl) ⟨355209, by rfl⟩ : syracuseStep 947225 = 710419) B710419
theorem B1602625 : Blo 630300 1602625 := bstep (se 2 (by rfl) ⟨600984, by rfl⟩ : syracuseStep 1602625 = 1201969) B1201969
theorem B947339 : Blo 630300 947339 := bstep (se 1 (by rfl) ⟨710504, by rfl⟩ : syracuseStep 947339 = 1421009) B1421009
theorem B947351 : Blo 630300 947351 := bstep (se 1 (by rfl) ⟨710513, by rfl⟩ : syracuseStep 947351 = 1421027) B1421027
theorem B947417 : Blo 630300 947417 := bstep (se 2 (by rfl) ⟨355281, by rfl⟩ : syracuseStep 947417 = 710563) B710563
theorem B3208409 : Blo 630300 3208409 := bstep (se 2 (by rfl) ⟨1203153, by rfl⟩ : syracuseStep 3208409 = 2406307) B2406307
theorem B5862617 : Blo 630300 5862617 := bstep (se 2 (by rfl) ⟨2198481, by rfl⟩ : syracuseStep 5862617 = 4396963) B4396963
theorem B1013003 : Blo 630300 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B947531 : Blo 630300 947531 := bstep (se 1 (by rfl) ⟨710648, by rfl⟩ : syracuseStep 947531 = 1421297) B1421297
theorem B947543 : Blo 630300 947543 := bstep (se 1 (by rfl) ⟨710657, by rfl⟩ : syracuseStep 947543 = 1421315) B1421315
theorem B947609 : Blo 630300 947609 := bstep (se 2 (by rfl) ⟨355353, by rfl⟩ : syracuseStep 947609 = 710707) B710707
theorem B1799617 : Blo 630300 1799617 := bstep (se 2 (by rfl) ⟨674856, by rfl⟩ : syracuseStep 1799617 = 1349713) B1349713
theorem B947723 : Blo 630300 947723 := bstep (se 1 (by rfl) ⟨710792, by rfl⟩ : syracuseStep 947723 = 1421585) B1421585
theorem B2127383 : Blo 630300 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B947735 : Blo 630300 947735 := bstep (se 1 (by rfl) ⟨710801, by rfl⟩ : syracuseStep 947735 = 1421603) B1421603
theorem B947801 : Blo 630300 947801 := bstep (se 2 (by rfl) ⟨355425, by rfl⟩ : syracuseStep 947801 = 710851) B710851
theorem B1603223 : Blo 630300 1603223 := bstep (se 1 (by rfl) ⟨1202417, by rfl⟩ : syracuseStep 1603223 = 2404835) B2404835
theorem B947915 : Blo 630300 947915 := bstep (se 1 (by rfl) ⟨710936, by rfl⟩ : syracuseStep 947915 = 1421873) B1421873
theorem B947927 : Blo 630300 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B947993 : Blo 630300 947993 := bstep (se 2 (by rfl) ⟨355497, by rfl⟩ : syracuseStep 947993 = 710995) B710995
theorem B948107 : Blo 630300 948107 := bstep (se 1 (by rfl) ⟨711080, by rfl⟩ : syracuseStep 948107 = 1422161) B1422161
theorem B1079191 : Blo 630300 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B948119 : Blo 630300 948119 := bstep (se 1 (by rfl) ⟨711089, by rfl⟩ : syracuseStep 948119 = 1422179) B1422179
theorem B948185 : Blo 630300 948185 := bstep (se 2 (by rfl) ⟨355569, by rfl⟩ : syracuseStep 948185 = 711139) B711139
theorem B2029529 : Blo 630300 2029529 := bstep (se 2 (by rfl) ⟨761073, by rfl⟩ : syracuseStep 2029529 = 1522147) B1522147
theorem B2127923 : Blo 630300 2127923 := bstep (se 1 (by rfl) ⟨1595942, by rfl⟩ : syracuseStep 2127923 = 3191885) B3191885
theorem B948299 : Blo 630300 948299 := bstep (se 1 (by rfl) ⟨711224, by rfl⟩ : syracuseStep 948299 = 1422449) B1422449
theorem B948311 : Blo 630300 948311 := bstep (se 1 (by rfl) ⟨711233, by rfl⟩ : syracuseStep 948311 = 1422467) B1422467
theorem B2029657 : Blo 630300 2029657 := bstep (se 2 (by rfl) ⟨761121, by rfl⟩ : syracuseStep 2029657 = 1522243) B1522243
theorem B5142629 : Blo 630300 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B948377 : Blo 630300 948377 := bstep (se 2 (by rfl) ⟨355641, by rfl⟩ : syracuseStep 948377 = 711283) B711283
theorem B948491 : Blo 630300 948491 := bstep (se 1 (by rfl) ⟨711368, by rfl⟩ : syracuseStep 948491 = 1422737) B1422737
theorem B948503 : Blo 630300 948503 := bstep (se 1 (by rfl) ⟨711377, by rfl⟩ : syracuseStep 948503 = 1422755) B1422755
theorem B2128193 : Blo 630300 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B1440089 : Blo 630300 1440089 := bstep (se 2 (by rfl) ⟨540033, by rfl⟩ : syracuseStep 1440089 = 1080067) B1080067
theorem B948569 : Blo 630300 948569 := bstep (se 2 (by rfl) ⟨355713, by rfl⟩ : syracuseStep 948569 = 711427) B711427
theorem B2029913 : Blo 630300 2029913 := bstep (se 2 (by rfl) ⟨761217, by rfl⟩ : syracuseStep 2029913 = 1522435) B1522435
theorem B1604033 : Blo 630300 1604033 := bstep (se 2 (by rfl) ⟨601512, by rfl⟩ : syracuseStep 1604033 = 1203025) B1203025
theorem B948683 : Blo 630300 948683 := bstep (se 1 (by rfl) ⟨711512, by rfl⟩ : syracuseStep 948683 = 1423025) B1423025
theorem B948695 : Blo 630300 948695 := bstep (se 1 (by rfl) ⟨711521, by rfl⟩ : syracuseStep 948695 = 1423043) B1423043
theorem B948761 : Blo 630300 948761 := bstep (se 2 (by rfl) ⟨355785, by rfl⟩ : syracuseStep 948761 = 711571) B711571
theorem B948875 : Blo 630300 948875 := bstep (se 1 (by rfl) ⟨711656, by rfl⟩ : syracuseStep 948875 = 1423313) B1423313
theorem B948887 : Blo 630300 948887 := bstep (se 1 (by rfl) ⟨711665, by rfl⟩ : syracuseStep 948887 = 1423331) B1423331
theorem B948953 : Blo 630300 948953 := bstep (se 2 (by rfl) ⟨355857, by rfl⟩ : syracuseStep 948953 = 711715) B711715
theorem B3210029 : Blo 630300 3210029 := bstep (se 3 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 3210029 = 1203761) B1203761
theorem B949067 : Blo 630300 949067 := bstep (se 1 (by rfl) ⟨711800, by rfl⟩ : syracuseStep 949067 = 1423601) B1423601
theorem B949079 : Blo 630300 949079 := bstep (se 1 (by rfl) ⟨711809, by rfl⟩ : syracuseStep 949079 = 1423619) B1423619
theorem B2128733 : Blo 630300 2128733 := bstep (se 3 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 2128733 = 798275) B798275
theorem B949145 : Blo 630300 949145 := bstep (se 2 (by rfl) ⟨355929, by rfl⟩ : syracuseStep 949145 = 711859) B711859
theorem B19037105 : Blo 630300 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B1604569 : Blo 630300 1604569 := bstep (se 2 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 1604569 = 1203427) B1203427
theorem B949259 : Blo 630300 949259 := bstep (se 1 (by rfl) ⟨711944, by rfl⟩ : syracuseStep 949259 = 1423889) B1423889
theorem B949271 : Blo 630300 949271 := bstep (se 1 (by rfl) ⟨711953, by rfl⟩ : syracuseStep 949271 = 1423907) B1423907
theorem B1801291 : Blo 630300 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B949337 : Blo 630300 949337 := bstep (se 2 (by rfl) ⟨356001, by rfl⟩ : syracuseStep 949337 = 712003) B712003
theorem B949451 : Blo 630300 949451 := bstep (se 1 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 949451 = 1424177) B1424177
theorem B949463 : Blo 630300 949463 := bstep (se 1 (by rfl) ⟨712097, by rfl⟩ : syracuseStep 949463 = 1424195) B1424195
theorem B949529 : Blo 630300 949529 := bstep (se 2 (by rfl) ⟨356073, by rfl⟩ : syracuseStep 949529 = 712147) B712147
theorem B8092993 : Blo 630300 8092993 := bstep (se 2 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 8092993 = 6069745) B6069745
theorem B1801565 : Blo 630300 1801565 := bstep (se 3 (by rfl) ⟨337793, by rfl⟩ : syracuseStep 1801565 = 675587) B675587
theorem B4816259 : Blo 630300 4816259 := bstep (se 1 (by rfl) ⟨3612194, by rfl⟩ : syracuseStep 4816259 = 7224389) B7224389
theorem B949643 : Blo 630300 949643 := bstep (se 1 (by rfl) ⟨712232, by rfl⟩ : syracuseStep 949643 = 1424465) B1424465
theorem B949655 : Blo 630300 949655 := bstep (se 1 (by rfl) ⟨712241, by rfl⟩ : syracuseStep 949655 = 1424483) B1424483
theorem B949721 : Blo 630300 949721 := bstep (se 2 (by rfl) ⟨356145, by rfl⟩ : syracuseStep 949721 = 712291) B712291
theorem B2031169 : Blo 630300 2031169 := bstep (se 2 (by rfl) ⟨761688, by rfl⟩ : syracuseStep 2031169 = 1523377) B1523377
theorem B949835 : Blo 630300 949835 := bstep (se 1 (by rfl) ⟨712376, by rfl⟩ : syracuseStep 949835 = 1424753) B1424753
theorem B949847 : Blo 630300 949847 := bstep (se 1 (by rfl) ⟨712385, by rfl⟩ : syracuseStep 949847 = 1424771) B1424771
theorem B949913 : Blo 630300 949913 := bstep (se 2 (by rfl) ⟨356217, by rfl⟩ : syracuseStep 949913 = 712435) B712435
theorem B4062899 : Blo 630300 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B950027 : Blo 630300 950027 := bstep (se 1 (by rfl) ⟨712520, by rfl⟩ : syracuseStep 950027 = 1425041) B1425041
theorem B950039 : Blo 630300 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B950105 : Blo 630300 950105 := bstep (se 2 (by rfl) ⟨356289, by rfl⟩ : syracuseStep 950105 = 712579) B712579
theorem B2129867 : Blo 630300 2129867 := bstep (se 1 (by rfl) ⟨1597400, by rfl⟩ : syracuseStep 2129867 = 3194801) B3194801
theorem B950219 : Blo 630300 950219 := bstep (se 1 (by rfl) ⟨712664, by rfl⟩ : syracuseStep 950219 = 1425329) B1425329
theorem B950231 : Blo 630300 950231 := bstep (se 1 (by rfl) ⟨712673, by rfl⟩ : syracuseStep 950231 = 1425347) B1425347
theorem B950279 : Blo 630300 950279 := bstep (se 1 (by rfl) ⟨712709, by rfl⟩ : syracuseStep 950279 = 1425419) B1425419
theorem B5537803 : Blo 630300 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B950315 : Blo 630300 950315 := bstep (se 1 (by rfl) ⟨712736, by rfl⟩ : syracuseStep 950315 = 1425473) B1425473
theorem B950345 : Blo 630300 950345 := bstep (se 2 (by rfl) ⟨356379, by rfl⟩ : syracuseStep 950345 = 712759) B712759
theorem B1704089 : Blo 630300 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B950459 : Blo 630300 950459 := bstep (se 1 (by rfl) ⟨712844, by rfl⟩ : syracuseStep 950459 = 1425689) B1425689
theorem B950519 : Blo 630300 950519 := bstep (se 1 (by rfl) ⟨712889, by rfl⟩ : syracuseStep 950519 = 1425779) B1425779
theorem B2130191 : Blo 630300 2130191 := bstep (se 1 (by rfl) ⟨1597643, by rfl⟩ : syracuseStep 2130191 = 3195287) B3195287
theorem B950543 : Blo 630300 950543 := bstep (se 1 (by rfl) ⟨712907, by rfl⟩ : syracuseStep 950543 = 1425815) B1425815
theorem B3604769 : Blo 630300 3604769 := bstep (se 2 (by rfl) ⟨1351788, by rfl⟩ : syracuseStep 3604769 = 2703577) B2703577
theorem B950585 : Blo 630300 950585 := bstep (se 2 (by rfl) ⟨356469, by rfl⟩ : syracuseStep 950585 = 712939) B712939
theorem B950663 : Blo 630300 950663 := bstep (se 1 (by rfl) ⟨712997, by rfl⟩ : syracuseStep 950663 = 1425995) B1425995
theorem B950699 : Blo 630300 950699 := bstep (se 1 (by rfl) ⟨713024, by rfl⟩ : syracuseStep 950699 = 1426049) B1426049
theorem B1802681 : Blo 630300 1802681 := bstep (se 2 (by rfl) ⟨676005, by rfl⟩ : syracuseStep 1802681 = 1352011) B1352011
theorem B950729 : Blo 630300 950729 := bstep (se 2 (by rfl) ⟨356523, by rfl⟩ : syracuseStep 950729 = 713047) B713047
theorem B2130461 : Blo 630300 2130461 := bstep (se 3 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 2130461 = 798923) B798923
theorem B950843 : Blo 630300 950843 := bstep (se 1 (by rfl) ⟨713132, by rfl⟩ : syracuseStep 950843 = 1426265) B1426265
theorem B950903 : Blo 630300 950903 := bstep (se 1 (by rfl) ⟨713177, by rfl⟩ : syracuseStep 950903 = 1426355) B1426355
theorem B950927 : Blo 630300 950927 := bstep (se 1 (by rfl) ⟨713195, by rfl⟩ : syracuseStep 950927 = 1426391) B1426391
theorem B950969 : Blo 630300 950969 := bstep (se 2 (by rfl) ⟨356613, by rfl⟩ : syracuseStep 950969 = 713227) B713227
theorem B951047 : Blo 630300 951047 := bstep (se 1 (by rfl) ⟨713285, by rfl⟩ : syracuseStep 951047 = 1426571) B1426571
theorem B1803023 : Blo 630300 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B951083 : Blo 630300 951083 := bstep (se 1 (by rfl) ⟨713312, by rfl⟩ : syracuseStep 951083 = 1426625) B1426625
theorem B951113 : Blo 630300 951113 := bstep (se 2 (by rfl) ⟨356667, by rfl⟩ : syracuseStep 951113 = 713335) B713335
theorem B951227 : Blo 630300 951227 := bstep (se 1 (by rfl) ⟨713420, by rfl⟩ : syracuseStep 951227 = 1426841) B1426841
theorem B951287 : Blo 630300 951287 := bstep (se 1 (by rfl) ⟨713465, by rfl⟩ : syracuseStep 951287 = 1426931) B1426931
theorem B951311 : Blo 630300 951311 := bstep (se 1 (by rfl) ⟨713483, by rfl⟩ : syracuseStep 951311 = 1426967) B1426967
theorem B951353 : Blo 630300 951353 := bstep (se 2 (by rfl) ⟨356757, by rfl⟩ : syracuseStep 951353 = 713515) B713515
theorem B951431 : Blo 630300 951431 := bstep (se 1 (by rfl) ⟨713573, by rfl⟩ : syracuseStep 951431 = 1427147) B1427147
theorem B2393459 : Blo 630300 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B1803809 : Blo 630300 1803809 := bstep (se 2 (by rfl) ⟨676428, by rfl⟩ : syracuseStep 1803809 = 1352857) B1352857
theorem B2131865 : Blo 630300 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B6817699 : Blo 630300 6817699 := bstep (se 1 (by rfl) ⟨5113274, by rfl⟩ : syracuseStep 6817699 = 10226549) B10226549
theorem B1870025 : Blo 630300 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B1706555 : Blo 630300 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B2132567 : Blo 630300 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B1346167 : Blo 630300 1346167 := bstep (se 1 (by rfl) ⟨1009625, by rfl⟩ : syracuseStep 1346167 = 2019251) B2019251
theorem B4557617 : Blo 630300 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B9112409 : Blo 630300 9112409 := bstep (se 2 (by rfl) ⟨3417153, by rfl⟩ : syracuseStep 9112409 = 6834307) B6834307
theorem B2165771 : Blo 630300 2165771 := bstep (se 1 (by rfl) ⟨1624328, by rfl⟩ : syracuseStep 2165771 = 3248657) B3248657
theorem B1805323 : Blo 630300 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B2133053 : Blo 630300 2133053 := bstep (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) B799895
theorem B1707193 : Blo 630300 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B1805597 : Blo 630300 1805597 := bstep (se 3 (by rfl) ⟨338549, by rfl⟩ : syracuseStep 1805597 = 677099) B677099
theorem B6065441 : Blo 630300 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B2395601 : Blo 630300 2395601 := bstep (se 2 (by rfl) ⟨898350, by rfl⟩ : syracuseStep 2395601 = 1796701) B1796701
theorem B1805939 : Blo 630300 1805939 := bstep (se 1 (by rfl) ⟨1354454, by rfl⟩ : syracuseStep 1805939 = 2708909) B2708909
theorem B1969921 : Blo 630300 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B2395919 : Blo 630300 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B823099 : Blo 630300 823099 := bstep (se 1 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 823099 = 1234649) B1234649
theorem B1707895 : Blo 630300 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B3411857 : Blo 630300 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B1708091 : Blo 630300 1708091 := bstep (se 1 (by rfl) ⟨1281068, by rfl⟩ : syracuseStep 1708091 = 2562137) B2562137
theorem B3412313 : Blo 630300 3412313 := bstep (se 2 (by rfl) ⟨1279617, by rfl⟩ : syracuseStep 3412313 = 2559235) B2559235
theorem B2134457 : Blo 630300 2134457 := bstep (se 2 (by rfl) ⟨800421, by rfl⟩ : syracuseStep 2134457 = 1600843) B1600843
theorem B1708697 : Blo 630300 1708697 := bstep (se 2 (by rfl) ⟨640761, by rfl⟩ : syracuseStep 1708697 = 1281523) B1281523
theorem B1643275 : Blo 630300 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B4789043 : Blo 630300 4789043 := bstep (se 1 (by rfl) ⟨3591782, by rfl⟩ : syracuseStep 4789043 = 7183565) B7183565
theorem B3838873 : Blo 630300 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6656921 : Blo 630300 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B2135051 : Blo 630300 2135051 := bstep (se 1 (by rfl) ⟨1601288, by rfl⟩ : syracuseStep 2135051 = 3202577) B3202577
theorem B3609643 : Blo 630300 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B2135159 : Blo 630300 2135159 := bstep (se 1 (by rfl) ⟨1601369, by rfl⟩ : syracuseStep 2135159 = 3202739) B3202739
theorem B1250707 : Blo 630300 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1218233 : Blo 630300 1218233 := bstep (se 2 (by rfl) ⟨456837, by rfl⟩ : syracuseStep 1218233 = 913675) B913675
theorem B2135753 : Blo 630300 2135753 := bstep (se 2 (by rfl) ⟨800907, by rfl⟩ : syracuseStep 2135753 = 1601815) B1601815
theorem B2692865 : Blo 630300 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B2693017 : Blo 630300 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B2431043 : Blo 630300 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B7706897 : Blo 630300 7706897 := bstep (se 2 (by rfl) ⟨2890086, by rfl⟩ : syracuseStep 7706897 = 5780173) B5780173
theorem B2136455 : Blo 630300 2136455 := bstep (se 1 (by rfl) ⟨1602341, by rfl⟩ : syracuseStep 2136455 = 3204683) B3204683
theorem B59251085 : Blo 630300 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B3611101 : Blo 630300 3611101 := bstep (se 3 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 3611101 = 1354163) B1354163
theorem B2136833 : Blo 630300 2136833 := bstep (se 2 (by rfl) ⟨801312, by rfl⟩ : syracuseStep 2136833 = 1602625) B1602625
theorem B2399489 : Blo 630300 2399489 := bstep (se 2 (by rfl) ⟨899808, by rfl⟩ : syracuseStep 2399489 = 1799617) B1799617
theorem B2399503 : Blo 630300 2399503 := bstep (se 1 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 2399503 = 3599255) B3599255
theorem B2137643 : Blo 630300 2137643 := bstep (se 1 (by rfl) ⟨1603232, by rfl⟩ : syracuseStep 2137643 = 3206465) B3206465
theorem B630331 : Blo 630300 630331 := bstep (se 1 (by rfl) ⟨472748, by rfl⟩ : syracuseStep 630331 = 945497) B945497
theorem B630407 : Blo 630300 630407 := bstep (se 1 (by rfl) ⟨472805, by rfl⟩ : syracuseStep 630407 = 945611) B945611
theorem B630415 : Blo 630300 630415 := bstep (se 1 (by rfl) ⟨472811, by rfl⟩ : syracuseStep 630415 = 945623) B945623
theorem B630459 : Blo 630300 630459 := bstep (se 1 (by rfl) ⟨472844, by rfl⟩ : syracuseStep 630459 = 945689) B945689
theorem B630535 : Blo 630300 630535 := bstep (se 1 (by rfl) ⟨472901, by rfl⟩ : syracuseStep 630535 = 945803) B945803
theorem B630543 : Blo 630300 630543 := bstep (se 1 (by rfl) ⟨472907, by rfl⟩ : syracuseStep 630543 = 945815) B945815
theorem B630587 : Blo 630300 630587 := bstep (se 1 (by rfl) ⟨472940, by rfl⟩ : syracuseStep 630587 = 945881) B945881
theorem B630663 : Blo 630300 630663 := bstep (se 1 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 630663 = 945995) B945995
theorem B1351559 : Blo 630300 1351559 := bstep (se 1 (by rfl) ⟨1013669, by rfl⟩ : syracuseStep 1351559 = 2027339) B2027339
theorem B630671 : Blo 630300 630671 := bstep (se 1 (by rfl) ⟨473003, by rfl⟩ : syracuseStep 630671 = 946007) B946007
theorem B20848535 : Blo 630300 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B630715 : Blo 630300 630715 := bstep (se 1 (by rfl) ⟨473036, by rfl⟩ : syracuseStep 630715 = 946073) B946073
theorem B7217099 : Blo 630300 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B630791 : Blo 630300 630791 := bstep (se 1 (by rfl) ⟨473093, by rfl⟩ : syracuseStep 630791 = 946187) B946187
theorem B630799 : Blo 630300 630799 := bstep (se 1 (by rfl) ⟨473099, by rfl⟩ : syracuseStep 630799 = 946199) B946199
theorem B630843 : Blo 630300 630843 := bstep (se 1 (by rfl) ⟨473132, by rfl⟩ : syracuseStep 630843 = 946265) B946265
theorem B630919 : Blo 630300 630919 := bstep (se 1 (by rfl) ⟨473189, by rfl⟩ : syracuseStep 630919 = 946379) B946379
theorem B630927 : Blo 630300 630927 := bstep (se 1 (by rfl) ⟨473195, by rfl⟩ : syracuseStep 630927 = 946391) B946391
theorem B5775533 : Blo 630300 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B630971 : Blo 630300 630971 := bstep (se 1 (by rfl) ⟨473228, by rfl⟩ : syracuseStep 630971 = 946457) B946457
theorem B631047 : Blo 630300 631047 := bstep (se 1 (by rfl) ⟨473285, by rfl⟩ : syracuseStep 631047 = 946571) B946571
theorem B631055 : Blo 630300 631055 := bstep (se 1 (by rfl) ⟨473291, by rfl⟩ : syracuseStep 631055 = 946583) B946583
theorem B631099 : Blo 630300 631099 := bstep (se 1 (by rfl) ⟨473324, by rfl⟩ : syracuseStep 631099 = 946649) B946649
theorem B1483127 : Blo 630300 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B631175 : Blo 630300 631175 := bstep (se 1 (by rfl) ⟨473381, by rfl⟩ : syracuseStep 631175 = 946763) B946763
theorem B631183 : Blo 630300 631183 := bstep (se 1 (by rfl) ⟨473387, by rfl⟩ : syracuseStep 631183 = 946775) B946775
theorem B631227 : Blo 630300 631227 := bstep (se 1 (by rfl) ⟨473420, by rfl⟩ : syracuseStep 631227 = 946841) B946841
theorem B631303 : Blo 630300 631303 := bstep (se 1 (by rfl) ⟨473477, by rfl⟩ : syracuseStep 631303 = 946955) B946955
theorem B2400779 : Blo 630300 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B631311 : Blo 630300 631311 := bstep (se 1 (by rfl) ⟨473483, by rfl⟩ : syracuseStep 631311 = 946967) B946967
theorem B631355 : Blo 630300 631355 := bstep (se 1 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 631355 = 947033) B947033
theorem B631431 : Blo 630300 631431 := bstep (se 1 (by rfl) ⟨473573, by rfl⟩ : syracuseStep 631431 = 947147) B947147
theorem B631439 : Blo 630300 631439 := bstep (se 1 (by rfl) ⟨473579, by rfl⟩ : syracuseStep 631439 = 947159) B947159
theorem B631483 : Blo 630300 631483 := bstep (se 1 (by rfl) ⟨473612, by rfl⟩ : syracuseStep 631483 = 947225) B947225
theorem B7283429 : Blo 630300 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B631559 : Blo 630300 631559 := bstep (se 1 (by rfl) ⟨473669, by rfl⟩ : syracuseStep 631559 = 947339) B947339
theorem B631567 : Blo 630300 631567 := bstep (se 1 (by rfl) ⟨473675, by rfl⟩ : syracuseStep 631567 = 947351) B947351
theorem B631611 : Blo 630300 631611 := bstep (se 1 (by rfl) ⟨473708, by rfl⟩ : syracuseStep 631611 = 947417) B947417
theorem B2138939 : Blo 630300 2138939 := bstep (se 1 (by rfl) ⟨1604204, by rfl⟩ : syracuseStep 2138939 = 3208409) B3208409
theorem B3908411 : Blo 630300 3908411 := bstep (se 1 (by rfl) ⟨2931308, by rfl⟩ : syracuseStep 3908411 = 5862617) B5862617
theorem B631687 : Blo 630300 631687 := bstep (se 1 (by rfl) ⟨473765, by rfl⟩ : syracuseStep 631687 = 947531) B947531
theorem B631695 : Blo 630300 631695 := bstep (se 1 (by rfl) ⟨473771, by rfl⟩ : syracuseStep 631695 = 947543) B947543
theorem B631739 : Blo 630300 631739 := bstep (se 1 (by rfl) ⟨473804, by rfl⟩ : syracuseStep 631739 = 947609) B947609
theorem B10232837 : Blo 630300 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B631815 : Blo 630300 631815 := bstep (se 1 (by rfl) ⟨473861, by rfl⟩ : syracuseStep 631815 = 947723) B947723
theorem B1418255 : Blo 630300 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B631823 : Blo 630300 631823 := bstep (se 1 (by rfl) ⟨473867, by rfl⟩ : syracuseStep 631823 = 947735) B947735
theorem B1418273 : Blo 630300 1418273 := bstep (se 2 (by rfl) ⟨531852, by rfl⟩ : syracuseStep 1418273 = 1063705) B1063705
theorem B6825005 : Blo 630300 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B631867 : Blo 630300 631867 := bstep (se 1 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 631867 = 947801) B947801
theorem B5121157 : Blo 630300 5121157 := bstep (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) B960217
theorem B631943 : Blo 630300 631943 := bstep (se 1 (by rfl) ⟨473957, by rfl⟩ : syracuseStep 631943 = 947915) B947915
theorem B631951 : Blo 630300 631951 := bstep (se 1 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 631951 = 947927) B947927
theorem B631995 : Blo 630300 631995 := bstep (se 1 (by rfl) ⟨473996, by rfl⟩ : syracuseStep 631995 = 947993) B947993
theorem B1516745 : Blo 630300 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B632071 : Blo 630300 632071 := bstep (se 1 (by rfl) ⟨474053, by rfl⟩ : syracuseStep 632071 = 948107) B948107
theorem B632079 : Blo 630300 632079 := bstep (se 1 (by rfl) ⟨474059, by rfl⟩ : syracuseStep 632079 = 948119) B948119
theorem B2139425 : Blo 630300 2139425 := bstep (se 2 (by rfl) ⟨802284, by rfl⟩ : syracuseStep 2139425 = 1604569) B1604569
theorem B632123 : Blo 630300 632123 := bstep (se 1 (by rfl) ⟨474092, by rfl⟩ : syracuseStep 632123 = 948185) B948185
theorem B1353019 : Blo 630300 1353019 := bstep (se 1 (by rfl) ⟨1014764, by rfl⟩ : syracuseStep 1353019 = 2029529) B2029529
theorem B1418615 : Blo 630300 1418615 := bstep (se 1 (by rfl) ⟨1063961, by rfl⟩ : syracuseStep 1418615 = 2127923) B2127923
theorem B632199 : Blo 630300 632199 := bstep (se 1 (by rfl) ⟨474149, by rfl⟩ : syracuseStep 632199 = 948299) B948299
theorem B632207 : Blo 630300 632207 := bstep (se 1 (by rfl) ⟨474155, by rfl⟩ : syracuseStep 632207 = 948311) B948311
theorem B2401721 : Blo 630300 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B632251 : Blo 630300 632251 := bstep (se 1 (by rfl) ⟨474188, by rfl⟩ : syracuseStep 632251 = 948377) B948377
theorem B632327 : Blo 630300 632327 := bstep (se 1 (by rfl) ⟨474245, by rfl⟩ : syracuseStep 632327 = 948491) B948491
theorem B632335 : Blo 630300 632335 := bstep (se 1 (by rfl) ⟨474251, by rfl⟩ : syracuseStep 632335 = 948503) B948503
theorem B1418795 : Blo 630300 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B960059 : Blo 630300 960059 := bstep (se 1 (by rfl) ⟨720044, by rfl⟩ : syracuseStep 960059 = 1440089) B1440089
theorem B632379 : Blo 630300 632379 := bstep (se 1 (by rfl) ⟨474284, by rfl⟩ : syracuseStep 632379 = 948569) B948569
theorem B1353275 : Blo 630300 1353275 := bstep (se 1 (by rfl) ⟨1014956, by rfl⟩ : syracuseStep 1353275 = 2029913) B2029913
theorem B9217613 : Blo 630300 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B632455 : Blo 630300 632455 := bstep (se 1 (by rfl) ⟨474341, by rfl⟩ : syracuseStep 632455 = 948683) B948683
theorem B632463 : Blo 630300 632463 := bstep (se 1 (by rfl) ⟨474347, by rfl⟩ : syracuseStep 632463 = 948695) B948695
theorem B632507 : Blo 630300 632507 := bstep (se 1 (by rfl) ⟨474380, by rfl⟩ : syracuseStep 632507 = 948761) B948761
theorem B10790657 : Blo 630300 10790657 := bstep (se 2 (by rfl) ⟨4046496, by rfl⟩ : syracuseStep 10790657 = 8092993) B8092993
theorem B632583 : Blo 630300 632583 := bstep (se 1 (by rfl) ⟨474437, by rfl⟩ : syracuseStep 632583 = 948875) B948875
theorem B632591 : Blo 630300 632591 := bstep (se 1 (by rfl) ⟨474443, by rfl⟩ : syracuseStep 632591 = 948887) B948887
theorem B632635 : Blo 630300 632635 := bstep (se 1 (by rfl) ⟨474476, by rfl⟩ : syracuseStep 632635 = 948953) B948953
theorem B2140019 : Blo 630300 2140019 := bstep (se 1 (by rfl) ⟨1605014, by rfl⟩ : syracuseStep 2140019 = 3210029) B3210029
theorem B632711 : Blo 630300 632711 := bstep (se 1 (by rfl) ⟨474533, by rfl⟩ : syracuseStep 632711 = 949067) B949067
theorem B632719 : Blo 630300 632719 := bstep (se 1 (by rfl) ⟨474539, by rfl⟩ : syracuseStep 632719 = 949079) B949079
theorem B1419155 : Blo 630300 1419155 := bstep (se 1 (by rfl) ⟨1064366, by rfl⟩ : syracuseStep 1419155 = 2128733) B2128733
theorem B632763 : Blo 630300 632763 := bstep (se 1 (by rfl) ⟨474572, by rfl⟩ : syracuseStep 632763 = 949145) B949145
theorem B1419209 : Blo 630300 1419209 := bstep (se 2 (by rfl) ⟨532203, by rfl⟩ : syracuseStep 1419209 = 1064407) B1064407
theorem B12691403 : Blo 630300 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B632839 : Blo 630300 632839 := bstep (se 1 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 632839 = 949259) B949259
theorem B632847 : Blo 630300 632847 := bstep (se 1 (by rfl) ⟨474635, by rfl⟩ : syracuseStep 632847 = 949271) B949271
theorem B1517611 : Blo 630300 1517611 := bstep (se 1 (by rfl) ⟨1138208, by rfl⟩ : syracuseStep 1517611 = 2276417) B2276417
theorem B632891 : Blo 630300 632891 := bstep (se 1 (by rfl) ⟨474668, by rfl⟩ : syracuseStep 632891 = 949337) B949337
theorem B632967 : Blo 630300 632967 := bstep (se 1 (by rfl) ⟨474725, by rfl⟩ : syracuseStep 632967 = 949451) B949451
theorem B632975 : Blo 630300 632975 := bstep (se 1 (by rfl) ⟨474731, by rfl⟩ : syracuseStep 632975 = 949463) B949463
theorem B633019 : Blo 630300 633019 := bstep (se 1 (by rfl) ⟨474764, by rfl⟩ : syracuseStep 633019 = 949529) B949529
theorem B633095 : Blo 630300 633095 := bstep (se 1 (by rfl) ⟨474821, by rfl⟩ : syracuseStep 633095 = 949643) B949643
theorem B633103 : Blo 630300 633103 := bstep (se 1 (by rfl) ⟨474827, by rfl⟩ : syracuseStep 633103 = 949655) B949655
theorem B633147 : Blo 630300 633147 := bstep (se 1 (by rfl) ⟨474860, by rfl⟩ : syracuseStep 633147 = 949721) B949721
theorem B633223 : Blo 630300 633223 := bstep (se 1 (by rfl) ⟨474917, by rfl⟩ : syracuseStep 633223 = 949835) B949835
theorem B633231 : Blo 630300 633231 := bstep (se 1 (by rfl) ⟨474923, by rfl⟩ : syracuseStep 633231 = 949847) B949847
theorem B633275 : Blo 630300 633275 := bstep (se 1 (by rfl) ⟨474956, by rfl⟩ : syracuseStep 633275 = 949913) B949913
theorem B633351 : Blo 630300 633351 := bstep (se 1 (by rfl) ⟨475013, by rfl⟩ : syracuseStep 633351 = 950027) B950027
theorem B633359 : Blo 630300 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B633403 : Blo 630300 633403 := bstep (se 1 (by rfl) ⟨475052, by rfl⟩ : syracuseStep 633403 = 950105) B950105
theorem B1419911 : Blo 630300 1419911 := bstep (se 1 (by rfl) ⟨1064933, by rfl⟩ : syracuseStep 1419911 = 2129867) B2129867
theorem B633479 : Blo 630300 633479 := bstep (se 1 (by rfl) ⟨475109, by rfl⟩ : syracuseStep 633479 = 950219) B950219
theorem B633487 : Blo 630300 633487 := bstep (se 1 (by rfl) ⟨475115, by rfl⟩ : syracuseStep 633487 = 950231) B950231
theorem B1518227 : Blo 630300 1518227 := bstep (se 1 (by rfl) ⟨1138670, by rfl⟩ : syracuseStep 1518227 = 2277341) B2277341
theorem B633531 : Blo 630300 633531 := bstep (se 1 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 633531 = 950297) B950297
theorem B633607 : Blo 630300 633607 := bstep (se 1 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 633607 = 950411) B950411
theorem B633615 : Blo 630300 633615 := bstep (se 1 (by rfl) ⟨475211, by rfl⟩ : syracuseStep 633615 = 950423) B950423
theorem B1420091 : Blo 630300 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B633659 : Blo 630300 633659 := bstep (se 1 (by rfl) ⟨475244, by rfl⟩ : syracuseStep 633659 = 950489) B950489
theorem B633735 : Blo 630300 633735 := bstep (se 1 (by rfl) ⟨475301, by rfl⟩ : syracuseStep 633735 = 950603) B950603
theorem B633743 : Blo 630300 633743 := bstep (se 1 (by rfl) ⟨475307, by rfl⟩ : syracuseStep 633743 = 950615) B950615
theorem B1420217 : Blo 630300 1420217 := bstep (se 2 (by rfl) ⟨532581, by rfl⟩ : syracuseStep 1420217 = 1065163) B1065163
theorem B633787 : Blo 630300 633787 := bstep (se 1 (by rfl) ⟨475340, by rfl⟩ : syracuseStep 633787 = 950681) B950681
theorem B633863 : Blo 630300 633863 := bstep (se 1 (by rfl) ⟨475397, by rfl⟩ : syracuseStep 633863 = 950795) B950795
theorem B633871 : Blo 630300 633871 := bstep (se 1 (by rfl) ⟨475403, by rfl⟩ : syracuseStep 633871 = 950807) B950807
theorem B633915 : Blo 630300 633915 := bstep (se 1 (by rfl) ⟨475436, by rfl⟩ : syracuseStep 633915 = 950873) B950873
theorem B4566149 : Blo 630300 4566149 := bstep (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) B856153
theorem B633991 : Blo 630300 633991 := bstep (se 1 (by rfl) ⟨475493, by rfl⟩ : syracuseStep 633991 = 950987) B950987
theorem B633999 : Blo 630300 633999 := bstep (se 1 (by rfl) ⟨475499, by rfl⟩ : syracuseStep 633999 = 950999) B950999
theorem B634043 : Blo 630300 634043 := bstep (se 1 (by rfl) ⟨475532, by rfl⟩ : syracuseStep 634043 = 951065) B951065
theorem B634119 : Blo 630300 634119 := bstep (se 1 (by rfl) ⟨475589, by rfl⟩ : syracuseStep 634119 = 951179) B951179
theorem B1420559 : Blo 630300 1420559 := bstep (se 1 (by rfl) ⟨1065419, by rfl⟩ : syracuseStep 1420559 = 2130839) B2130839
theorem B634127 : Blo 630300 634127 := bstep (se 1 (by rfl) ⟨475595, by rfl⟩ : syracuseStep 634127 = 951191) B951191
theorem B8629537 : Blo 630300 8629537 := bstep (se 2 (by rfl) ⟨3236076, by rfl⟩ : syracuseStep 8629537 = 6472153) B6472153
theorem B1420577 : Blo 630300 1420577 := bstep (se 2 (by rfl) ⟨532716, by rfl⟩ : syracuseStep 1420577 = 1065433) B1065433
theorem B3648827 : Blo 630300 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B634171 : Blo 630300 634171 := bstep (se 1 (by rfl) ⟨475628, by rfl⟩ : syracuseStep 634171 = 951257) B951257
theorem B634247 : Blo 630300 634247 := bstep (se 1 (by rfl) ⟨475685, by rfl⟩ : syracuseStep 634247 = 951371) B951371
theorem B634255 : Blo 630300 634255 := bstep (se 1 (by rfl) ⟨475691, by rfl⟩ : syracuseStep 634255 = 951383) B951383
theorem B2272697 : Blo 630300 2272697 := bstep (se 2 (by rfl) ⟨852261, by rfl⟩ : syracuseStep 2272697 = 1704523) B1704523
theorem B4042169 : Blo 630300 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B634299 : Blo 630300 634299 := bstep (se 1 (by rfl) ⟨475724, by rfl⟩ : syracuseStep 634299 = 951449) B951449
theorem B1420919 : Blo 630300 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B1421099 : Blo 630300 1421099 := bstep (se 1 (by rfl) ⟨1065824, by rfl⟩ : syracuseStep 1421099 = 2131649) B2131649
theorem B798599 : Blo 630300 798599 := bstep (se 1 (by rfl) ⟨598949, by rfl⟩ : syracuseStep 798599 = 1197899) B1197899
theorem B2404363 : Blo 630300 2404363 := bstep (se 1 (by rfl) ⟨1803272, by rfl⟩ : syracuseStep 2404363 = 3606545) B3606545
theorem B1618067 : Blo 630300 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1421459 : Blo 630300 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1421513 : Blo 630300 1421513 := bstep (se 2 (by rfl) ⟨533067, by rfl⟩ : syracuseStep 1421513 = 1066135) B1066135
theorem B2404667 : Blo 630300 2404667 := bstep (se 1 (by rfl) ⟨1803500, by rfl⟩ : syracuseStep 2404667 = 3607001) B3607001
theorem B4796819 : Blo 630300 4796819 := bstep (se 1 (by rfl) ⟨3597614, by rfl⟩ : syracuseStep 4796819 = 7195229) B7195229
theorem B1388947 : Blo 630300 1388947 := bstep (se 1 (by rfl) ⟨1041710, by rfl⟩ : syracuseStep 1388947 = 2083421) B2083421
theorem B799247 : Blo 630300 799247 := bstep (se 1 (by rfl) ⟨599435, by rfl⟩ : syracuseStep 799247 = 1198871) B1198871
theorem B2699837 : Blo 630300 2699837 := bstep (se 3 (by rfl) ⟨506219, by rfl⟩ : syracuseStep 2699837 = 1012439) B1012439
theorem B963343 : Blo 630300 963343 := bstep (se 1 (by rfl) ⟨722507, by rfl⟩ : syracuseStep 963343 = 1445015) B1445015
theorem B4567823 : Blo 630300 4567823 := bstep (se 1 (by rfl) ⟨3425867, by rfl⟩ : syracuseStep 4567823 = 6851735) B6851735
theorem B2405153 : Blo 630300 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B1422215 : Blo 630300 1422215 := bstep (se 1 (by rfl) ⟨1066661, by rfl⟩ : syracuseStep 1422215 = 2133323) B2133323
theorem B1422395 : Blo 630300 1422395 := bstep (se 1 (by rfl) ⟨1066796, by rfl⟩ : syracuseStep 1422395 = 2133593) B2133593
theorem B898219 : Blo 630300 898219 := bstep (se 1 (by rfl) ⟨673664, by rfl⟩ : syracuseStep 898219 = 1347329) B1347329
theorem B1422521 : Blo 630300 1422521 := bstep (se 2 (by rfl) ⟨533445, by rfl⟩ : syracuseStep 1422521 = 1066891) B1066891
theorem B898447 : Blo 630300 898447 := bstep (se 1 (by rfl) ⟨673835, by rfl⟩ : syracuseStep 898447 = 1347671) B1347671
theorem B3192209 : Blo 630300 3192209 := bstep (se 2 (by rfl) ⟨1197078, by rfl⟩ : syracuseStep 3192209 = 2394157) B2394157
theorem B1422863 : Blo 630300 1422863 := bstep (se 1 (by rfl) ⟨1067147, by rfl⟩ : syracuseStep 1422863 = 2134295) B2134295
theorem B1422881 : Blo 630300 1422881 := bstep (se 2 (by rfl) ⟨533580, by rfl⟩ : syracuseStep 1422881 = 1067161) B1067161
theorem B3847873 : Blo 630300 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2406125 : Blo 630300 2406125 := bstep (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) B902297
theorem B898823 : Blo 630300 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B1423223 : Blo 630300 1423223 := bstep (se 1 (by rfl) ⟨1067417, by rfl⟩ : syracuseStep 1423223 = 2134835) B2134835
theorem B10795031 : Blo 630300 10795031 := bstep (se 1 (by rfl) ⟨8096273, by rfl⟩ : syracuseStep 10795031 = 16192547) B16192547
theorem B2930717 : Blo 630300 2930717 := bstep (se 3 (by rfl) ⟨549509, by rfl⟩ : syracuseStep 2930717 = 1099019) B1099019
theorem B1423403 : Blo 630300 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B4569149 : Blo 630300 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B1423763 : Blo 630300 1423763 := bstep (se 1 (by rfl) ⟨1067822, by rfl⟩ : syracuseStep 1423763 = 2135645) B2135645
theorem B1423817 : Blo 630300 1423817 := bstep (se 2 (by rfl) ⟨533931, by rfl⟩ : syracuseStep 1423817 = 1067863) B1067863
theorem B2701835 : Blo 630300 2701835 := bstep (se 1 (by rfl) ⟨2026376, by rfl⟩ : syracuseStep 2701835 = 4052753) B4052753
theorem B2571041 : Blo 630300 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B1063739 : Blo 630300 1063739 := bstep (se 1 (by rfl) ⟨797804, by rfl⟩ : syracuseStep 1063739 = 1595609) B1595609
theorem B26000389 : Blo 630300 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B1621003 : Blo 630300 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B1424519 : Blo 630300 1424519 := bstep (se 1 (by rfl) ⟨1068389, by rfl⟩ : syracuseStep 1424519 = 2136779) B2136779
theorem B900281 : Blo 630300 900281 := bstep (se 2 (by rfl) ⟨337605, by rfl⟩ : syracuseStep 900281 = 675211) B675211
theorem B1064137 : Blo 630300 1064137 := bstep (se 2 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 1064137 = 798103) B798103
theorem B1424699 : Blo 630300 1424699 := bstep (se 1 (by rfl) ⟨1068524, by rfl⟩ : syracuseStep 1424699 = 2137049) B2137049
theorem B802219 : Blo 630300 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B1424825 : Blo 630300 1424825 := bstep (se 2 (by rfl) ⟨534309, by rfl⟩ : syracuseStep 1424825 = 1068619) B1068619
theorem B3194315 : Blo 630300 3194315 := bstep (se 1 (by rfl) ⟨2395736, by rfl⟩ : syracuseStep 3194315 = 4791473) B4791473
theorem B12303875 : Blo 630300 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B472858165 : Blo 630300 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B3194639 : Blo 630300 3194639 := bstep (se 1 (by rfl) ⟨2395979, by rfl⟩ : syracuseStep 3194639 = 4791959) B4791959
theorem B1425167 : Blo 630300 1425167 := bstep (se 1 (by rfl) ⟨1068875, by rfl⟩ : syracuseStep 1425167 = 2137751) B2137751
theorem B1425185 : Blo 630300 1425185 := bstep (se 2 (by rfl) ⟨534444, by rfl⟩ : syracuseStep 1425185 = 1068889) B1068889
theorem B2408251 : Blo 630300 2408251 := bstep (se 1 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 2408251 = 3612377) B3612377
theorem B1064839 : Blo 630300 1064839 := bstep (se 1 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 1064839 = 1597259) B1597259
theorem B769927 : Blo 630300 769927 := bstep (se 1 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 769927 = 1154891) B1154891
theorem B901135 : Blo 630300 901135 := bstep (se 1 (by rfl) ⟨675851, by rfl⟩ : syracuseStep 901135 = 1351703) B1351703
theorem B1425527 : Blo 630300 1425527 := bstep (se 1 (by rfl) ⟨1069145, by rfl⟩ : syracuseStep 1425527 = 2138291) B2138291
theorem B6078665 : Blo 630300 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B1425707 : Blo 630300 1425707 := bstep (se 1 (by rfl) ⟨1069280, by rfl⟩ : syracuseStep 1425707 = 2138561) B2138561
theorem B639419 : Blo 630300 639419 := bstep (se 1 (by rfl) ⟨479564, by rfl⟩ : syracuseStep 639419 = 959129) B959129
theorem B1065487 : Blo 630300 1065487 := bstep (se 1 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 1065487 = 1598231) B1598231
theorem B901705 : Blo 630300 901705 := bstep (se 2 (by rfl) ⟨338139, by rfl⟩ : syracuseStep 901705 = 676279) B676279
theorem B1426067 : Blo 630300 1426067 := bstep (se 1 (by rfl) ⟨1069550, by rfl⟩ : syracuseStep 1426067 = 2139101) B2139101
theorem B1426121 : Blo 630300 1426121 := bstep (se 2 (by rfl) ⟨534795, by rfl⟩ : syracuseStep 1426121 = 1069591) B1069591
theorem B1917881 : Blo 630300 1917881 := bstep (se 2 (by rfl) ⟨719205, by rfl⟩ : syracuseStep 1917881 = 1438411) B1438411
theorem B1066027 : Blo 630300 1066027 := bstep (se 1 (by rfl) ⟨799520, by rfl⟩ : syracuseStep 1066027 = 1599041) B1599041
theorem B1066169 : Blo 630300 1066169 := bstep (se 2 (by rfl) ⟨399813, by rfl⟩ : syracuseStep 1066169 = 799627) B799627
theorem B3196097 : Blo 630300 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B1426823 : Blo 630300 1426823 := bstep (se 1 (by rfl) ⟨1070117, by rfl⟩ : syracuseStep 1426823 = 2140235) B2140235
theorem B1197497 : Blo 630300 1197497 := bstep (se 2 (by rfl) ⟨449061, by rfl⟩ : syracuseStep 1197497 = 898123) B898123
theorem B1427003 : Blo 630300 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B1427129 : Blo 630300 1427129 := bstep (se 2 (by rfl) ⟨535173, by rfl⟩ : syracuseStep 1427129 = 1070347) B1070347
theorem B1427233 : Blo 630300 1427233 := bstep (se 2 (by rfl) ⟨535212, by rfl⟩ : syracuseStep 1427233 = 1070425) B1070425
theorem B1066871 : Blo 630300 1066871 := bstep (se 1 (by rfl) ⟨800153, by rfl⟩ : syracuseStep 1066871 = 1600307) B1600307
theorem B4048957 : Blo 630300 4048957 := bstep (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) B1518359
theorem B12503285 : Blo 630300 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B8669429 : Blo 630300 8669429 := bstep (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) B812759
theorem B1067323 : Blo 630300 1067323 := bstep (se 1 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 1067323 = 1600985) B1600985
theorem B1067465 : Blo 630300 1067465 := bstep (se 2 (by rfl) ⟨400299, by rfl⟩ : syracuseStep 1067465 = 800599) B800599
theorem B3197393 : Blo 630300 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B1198651 : Blo 630300 1198651 := bstep (se 1 (by rfl) ⟨898988, by rfl⟩ : syracuseStep 1198651 = 1797977) B1797977
theorem B2705987 : Blo 630300 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B2706209 : Blo 630300 2706209 := bstep (se 2 (by rfl) ⟨1014828, by rfl⟩ : syracuseStep 2706209 = 2029657) B2029657
theorem B3590963 : Blo 630300 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B2280251 : Blo 630300 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B2280307 : Blo 630300 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B2706311 : Blo 630300 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B14797835 : Blo 630300 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B1199137 : Blo 630300 1199137 := bstep (se 2 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 1199137 = 899353) B899353
theorem B1068167 : Blo 630300 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B675335 : Blo 630300 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B46157525 : Blo 630300 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B1068815 : Blo 630300 1068815 := bstep (se 1 (by rfl) ⟨801611, by rfl⟩ : syracuseStep 1068815 = 1603223) B1603223
theorem B4050803 : Blo 630300 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B3428419 : Blo 630300 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B1200329 : Blo 630300 1200329 := bstep (se 2 (by rfl) ⟨450123, by rfl⟩ : syracuseStep 1200329 = 900247) B900247
theorem B3592421 : Blo 630300 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B1069355 : Blo 630300 1069355 := bstep (se 1 (by rfl) ⟨802016, by rfl⟩ : syracuseStep 1069355 = 1604033) B1604033
theorem B10834397 : Blo 630300 10834397 := bstep (se 3 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 10834397 = 4062899) B4062899
theorem B3199499 : Blo 630300 3199499 := bstep (se 1 (by rfl) ⟨2399624, by rfl⟩ : syracuseStep 3199499 = 4799249) B4799249
theorem B159896081 : Blo 630300 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B3461699 : Blo 630300 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B3199661 : Blo 630300 3199661 := bstep (se 3 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 3199661 = 1199873) B1199873
theorem B1069753 : Blo 630300 1069753 := bstep (se 2 (by rfl) ⟨401157, by rfl⟩ : syracuseStep 1069753 = 802315) B802315
theorem B2708225 : Blo 630300 2708225 := bstep (se 2 (by rfl) ⟨1015584, by rfl⟩ : syracuseStep 2708225 = 2031169) B2031169
theorem B4051727 : Blo 630300 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B709519 : Blo 630300 709519 := bstep (se 1 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 709519 = 1064279) B1064279
theorem B3593105 : Blo 630300 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B1201043 : Blo 630300 1201043 := bstep (se 1 (by rfl) ⟨900782, by rfl⟩ : syracuseStep 1201043 = 1801565) B1801565
theorem B1201081 : Blo 630300 1201081 := bstep (se 2 (by rfl) ⟨450405, by rfl⟩ : syracuseStep 1201081 = 900811) B900811
theorem B710023 : Blo 630300 710023 := bstep (se 1 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 710023 = 1065035) B1065035
theorem B710203 : Blo 630300 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B10245811 : Blo 630300 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B743099 : Blo 630300 743099 := bstep (se 1 (by rfl) ⟨557324, by rfl⟩ : syracuseStep 743099 = 1114649) B1114649
theorem B6477529 : Blo 630300 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B3594131 : Blo 630300 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B710671 : Blo 630300 710671 := bstep (se 1 (by rfl) ⟨533003, by rfl⟩ : syracuseStep 710671 = 1066007) B1066007
theorem B1136825 : Blo 630300 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B3201281 : Blo 630300 3201281 := bstep (se 2 (by rfl) ⟨1200480, by rfl⟩ : syracuseStep 3201281 = 2400961) B2400961
theorem B1595659 : Blo 630300 1595659 := bstep (se 1 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 1595659 = 2393489) B2393489
theorem B3660167 : Blo 630300 3660167 := bstep (se 1 (by rfl) ⟨2745125, by rfl⟩ : syracuseStep 3660167 = 5490251) B5490251
theorem B1595801 : Blo 630300 1595801 := bstep (se 2 (by rfl) ⟨598425, by rfl⟩ : syracuseStep 1595801 = 1196851) B1196851
theorem B711175 : Blo 630300 711175 := bstep (se 1 (by rfl) ⟨533381, by rfl⟩ : syracuseStep 711175 = 1066763) B1066763
theorem B1595963 : Blo 630300 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B10803779 : Blo 630300 10803779 := bstep (se 1 (by rfl) ⟨8102834, by rfl⟩ : syracuseStep 10803779 = 16205669) B16205669
theorem B4938317 : Blo 630300 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B711355 : Blo 630300 711355 := bstep (se 1 (by rfl) ⟨533516, by rfl⟩ : syracuseStep 711355 = 1067033) B1067033
theorem B1202987 : Blo 630300 1202987 := bstep (se 1 (by rfl) ⟨902240, by rfl⟩ : syracuseStep 1202987 = 1804481) B1804481
theorem B7199603 : Blo 630300 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B1596307 : Blo 630300 1596307 := bstep (se 1 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 1596307 = 2394461) B2394461
theorem B1596449 : Blo 630300 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B3202091 : Blo 630300 3202091 := bstep (se 1 (by rfl) ⟨2401568, by rfl⟩ : syracuseStep 3202091 = 4803137) B4803137
theorem B711823 : Blo 630300 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B4873607 : Blo 630300 4873607 := bstep (se 1 (by rfl) ⟨3655205, by rfl⟩ : syracuseStep 4873607 = 7310411) B7310411
theorem B2022941 : Blo 630300 2022941 := bstep (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) B758603
theorem B712327 : Blo 630300 712327 := bstep (se 1 (by rfl) ⟨534245, by rfl⟩ : syracuseStep 712327 = 1068491) B1068491
theorem B1203913 : Blo 630300 1203913 := bstep (se 2 (by rfl) ⟨451467, by rfl⟩ : syracuseStep 1203913 = 902935) B902935
theorem B712507 : Blo 630300 712507 := bstep (se 1 (by rfl) ⟨534380, by rfl⟩ : syracuseStep 712507 = 1068761) B1068761
theorem B3039065 : Blo 630300 3039065 := bstep (se 2 (by rfl) ⟨1139649, by rfl⟩ : syracuseStep 3039065 = 2279299) B2279299
theorem B1597441 : Blo 630300 1597441 := bstep (se 2 (by rfl) ⟨599040, by rfl⟩ : syracuseStep 1597441 = 1198081) B1198081
theorem B712975 : Blo 630300 712975 := bstep (se 1 (by rfl) ⟨534731, by rfl⟩ : syracuseStep 712975 = 1069463) B1069463
theorem B3203387 : Blo 630300 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B1925495 : Blo 630300 1925495 := bstep (se 1 (by rfl) ⟨1444121, by rfl⟩ : syracuseStep 1925495 = 2888243) B2888243
theorem B3203549 : Blo 630300 3203549 := bstep (se 3 (by rfl) ⟨600665, by rfl⟩ : syracuseStep 3203549 = 1201331) B1201331
theorem B1598039 : Blo 630300 1598039 := bstep (se 1 (by rfl) ⟨1198529, by rfl⟩ : syracuseStep 1598039 = 2397059) B2397059
theorem B713479 : Blo 630300 713479 := bstep (se 1 (by rfl) ⟨535109, by rfl⟩ : syracuseStep 713479 = 1070219) B1070219
theorem B3203873 : Blo 630300 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B1598251 : Blo 630300 1598251 := bstep (se 1 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 1598251 = 2397377) B2397377
theorem B1794935 : Blo 630300 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B1598393 : Blo 630300 1598393 := bstep (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) B1198795
theorem B1926443 : Blo 630300 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B12117347 : Blo 630300 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B812431 : Blo 630300 812431 := bstep (se 1 (by rfl) ⟨609323, by rfl⟩ : syracuseStep 812431 = 1218647) B1218647
theorem B3204845 : Blo 630300 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B1599385 : Blo 630300 1599385 := bstep (se 2 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 1599385 = 1199539) B1199539
theorem B1599547 : Blo 630300 1599547 := bstep (se 1 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 1599547 = 2399321) B2399321
theorem B1599689 : Blo 630300 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1009979 : Blo 630300 1009979 := bstep (se 1 (by rfl) ⟨757484, by rfl⟩ : syracuseStep 1009979 = 1514969) B1514969
theorem B3205655 : Blo 630300 3205655 := bstep (se 1 (by rfl) ⟨2404241, by rfl⟩ : syracuseStep 3205655 = 4808483) B4808483
theorem B1600033 : Blo 630300 1600033 := bstep (se 2 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 1600033 = 1200025) B1200025
theorem B1927795 : Blo 630300 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B10808153 : Blo 630300 10808153 := bstep (se 2 (by rfl) ⟨4053057, by rfl⟩ : syracuseStep 10808153 = 8106115) B8106115
theorem B11725829 : Blo 630300 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B1141819 : Blo 630300 1141819 := bstep (se 1 (by rfl) ⟨856364, by rfl⟩ : syracuseStep 1141819 = 1712729) B1712729
theorem B1600631 : Blo 630300 1600631 := bstep (se 1 (by rfl) ⟨1200473, by rfl⟩ : syracuseStep 1600631 = 2400947) B2400947
theorem B1928377 : Blo 630300 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B945467 : Blo 630300 945467 := bstep (se 1 (by rfl) ⟨709100, by rfl⟩ : syracuseStep 945467 = 1418201) B1418201
theorem B19426661 : Blo 630300 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B945527 : Blo 630300 945527 := bstep (se 1 (by rfl) ⟨709145, by rfl⟩ : syracuseStep 945527 = 1418291) B1418291
theorem B945551 : Blo 630300 945551 := bstep (se 1 (by rfl) ⟨709163, by rfl⟩ : syracuseStep 945551 = 1418327) B1418327
theorem B945593 : Blo 630300 945593 := bstep (se 2 (by rfl) ⟨354597, by rfl⟩ : syracuseStep 945593 = 709195) B709195
theorem B1142201 : Blo 630300 1142201 := bstep (se 2 (by rfl) ⟨428325, by rfl⟩ : syracuseStep 1142201 = 856651) B856651
theorem B945671 : Blo 630300 945671 := bstep (se 1 (by rfl) ⟨709253, by rfl⟩ : syracuseStep 945671 = 1418507) B1418507
theorem B2158109 : Blo 630300 2158109 := bstep (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) B809291
theorem B945707 : Blo 630300 945707 := bstep (se 1 (by rfl) ⟨709280, by rfl⟩ : syracuseStep 945707 = 1418561) B1418561
theorem B2027069 : Blo 630300 2027069 := bstep (se 3 (by rfl) ⟨380075, by rfl⟩ : syracuseStep 2027069 = 760151) B760151
theorem B945737 : Blo 630300 945737 := bstep (se 2 (by rfl) ⟨354651, by rfl⟩ : syracuseStep 945737 = 709303) B709303
theorem B945851 : Blo 630300 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B945911 : Blo 630300 945911 := bstep (se 1 (by rfl) ⟨709433, by rfl⟩ : syracuseStep 945911 = 1418867) B1418867
theorem B945935 : Blo 630300 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B945977 : Blo 630300 945977 := bstep (se 2 (by rfl) ⟨354741, by rfl⟩ : syracuseStep 945977 = 709483) B709483
theorem B946055 : Blo 630300 946055 := bstep (se 1 (by rfl) ⟨709541, by rfl⟩ : syracuseStep 946055 = 1419083) B1419083
theorem B6090659 : Blo 630300 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B946091 : Blo 630300 946091 := bstep (se 1 (by rfl) ⟨709568, by rfl⟩ : syracuseStep 946091 = 1419137) B1419137
theorem B946121 : Blo 630300 946121 := bstep (se 2 (by rfl) ⟨354795, by rfl⟩ : syracuseStep 946121 = 709591) B709591
theorem B3600395 : Blo 630300 3600395 := bstep (se 1 (by rfl) ⟨2700296, by rfl⟩ : syracuseStep 3600395 = 5400593) B5400593
theorem B1798159 : Blo 630300 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B1011727 : Blo 630300 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B946235 : Blo 630300 946235 := bstep (se 1 (by rfl) ⟨709676, by rfl⟩ : syracuseStep 946235 = 1419353) B1419353
theorem B946295 : Blo 630300 946295 := bstep (se 1 (by rfl) ⟨709721, by rfl⟩ : syracuseStep 946295 = 1419443) B1419443
theorem B946319 : Blo 630300 946319 := bstep (se 1 (by rfl) ⟨709739, by rfl⟩ : syracuseStep 946319 = 1419479) B1419479
theorem B946361 : Blo 630300 946361 := bstep (se 2 (by rfl) ⟨354885, by rfl⟩ : syracuseStep 946361 = 709771) B709771
theorem B946439 : Blo 630300 946439 := bstep (se 1 (by rfl) ⟨709829, by rfl⟩ : syracuseStep 946439 = 1419659) B1419659
theorem B1798433 : Blo 630300 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B946475 : Blo 630300 946475 := bstep (se 1 (by rfl) ⟨709856, by rfl⟩ : syracuseStep 946475 = 1419713) B1419713
theorem B946505 : Blo 630300 946505 := bstep (se 2 (by rfl) ⟨354939, by rfl⟩ : syracuseStep 946505 = 709879) B709879
theorem B1601927 : Blo 630300 1601927 := bstep (se 1 (by rfl) ⟨1201445, by rfl⟩ : syracuseStep 1601927 = 2402891) B2402891
theorem B1601977 : Blo 630300 1601977 := bstep (se 2 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 1601977 = 1201483) B1201483
theorem B946619 : Blo 630300 946619 := bstep (se 1 (by rfl) ⟨709964, by rfl⟩ : syracuseStep 946619 = 1419929) B1419929
theorem B946679 : Blo 630300 946679 := bstep (se 1 (by rfl) ⟨710009, by rfl⟩ : syracuseStep 946679 = 1420019) B1420019
theorem B946703 : Blo 630300 946703 := bstep (se 1 (by rfl) ⟨710027, by rfl⟩ : syracuseStep 946703 = 1420055) B1420055
theorem B946745 : Blo 630300 946745 := bstep (se 2 (by rfl) ⟨355029, by rfl⟩ : syracuseStep 946745 = 710059) B710059
theorem B946823 : Blo 630300 946823 := bstep (se 1 (by rfl) ⟨710117, by rfl⟩ : syracuseStep 946823 = 1420235) B1420235
theorem B946859 : Blo 630300 946859 := bstep (se 1 (by rfl) ⟨710144, by rfl⟩ : syracuseStep 946859 = 1420289) B1420289
theorem B17330881 : Blo 630300 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B946889 : Blo 630300 946889 := bstep (se 2 (by rfl) ⟨355083, by rfl⟩ : syracuseStep 946889 = 710167) B710167
theorem B947003 : Blo 630300 947003 := bstep (se 1 (by rfl) ⟨710252, by rfl⟩ : syracuseStep 947003 = 1420505) B1420505
theorem B1536887 : Blo 630300 1536887 := bstep (se 1 (by rfl) ⟨1152665, by rfl⟩ : syracuseStep 1536887 = 2305331) B2305331
theorem B947063 : Blo 630300 947063 := bstep (se 1 (by rfl) ⟨710297, by rfl⟩ : syracuseStep 947063 = 1420595) B1420595
theorem B947087 : Blo 630300 947087 := bstep (se 1 (by rfl) ⟨710315, by rfl⟩ : syracuseStep 947087 = 1420631) B1420631
theorem B947129 : Blo 630300 947129 := bstep (se 2 (by rfl) ⟨355173, by rfl⟩ : syracuseStep 947129 = 710347) B710347
theorem B947207 : Blo 630300 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B1602575 : Blo 630300 1602575 := bstep (se 1 (by rfl) ⟨1201931, by rfl⟩ : syracuseStep 1602575 = 2403863) B2403863
theorem B947243 : Blo 630300 947243 := bstep (se 1 (by rfl) ⟨710432, by rfl⟩ : syracuseStep 947243 = 1420865) B1420865
theorem B947273 : Blo 630300 947273 := bstep (se 2 (by rfl) ⟨355227, by rfl⟩ : syracuseStep 947273 = 710455) B710455
theorem B947387 : Blo 630300 947387 := bstep (se 1 (by rfl) ⟨710540, by rfl⟩ : syracuseStep 947387 = 1421081) B1421081
theorem B1438921 : Blo 630300 1438921 := bstep (se 2 (by rfl) ⟨539595, by rfl⟩ : syracuseStep 1438921 = 1079191) B1079191
theorem B947447 : Blo 630300 947447 := bstep (se 1 (by rfl) ⟨710585, by rfl⟩ : syracuseStep 947447 = 1421171) B1421171
theorem B1799435 : Blo 630300 1799435 := bstep (se 1 (by rfl) ⟨1349576, by rfl⟩ : syracuseStep 1799435 = 2699153) B2699153
theorem B947471 : Blo 630300 947471 := bstep (se 1 (by rfl) ⟨710603, by rfl⟩ : syracuseStep 947471 = 1421207) B1421207
theorem B947513 : Blo 630300 947513 := bstep (se 2 (by rfl) ⟨355317, by rfl⟩ : syracuseStep 947513 = 710635) B710635
theorem B947591 : Blo 630300 947591 := bstep (se 1 (by rfl) ⟨710693, by rfl⟩ : syracuseStep 947591 = 1421387) B1421387
theorem B11859335 : Blo 630300 11859335 := bstep (se 1 (by rfl) ⟨8894501, by rfl⟩ : syracuseStep 11859335 = 17789003) B17789003
theorem B947627 : Blo 630300 947627 := bstep (se 1 (by rfl) ⟨710720, by rfl⟩ : syracuseStep 947627 = 1421441) B1421441
theorem B947657 : Blo 630300 947657 := bstep (se 2 (by rfl) ⟨355371, by rfl⟩ : syracuseStep 947657 = 710743) B710743
theorem B4552195 : Blo 630300 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B3208733 : Blo 630300 3208733 := bstep (se 3 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 3208733 = 1203275) B1203275
theorem B947771 : Blo 630300 947771 := bstep (se 1 (by rfl) ⟨710828, by rfl⟩ : syracuseStep 947771 = 1421657) B1421657
theorem B947831 : Blo 630300 947831 := bstep (se 1 (by rfl) ⟨710873, by rfl⟩ : syracuseStep 947831 = 1421747) B1421747
theorem B947855 : Blo 630300 947855 := bstep (se 1 (by rfl) ⟨710891, by rfl⟩ : syracuseStep 947855 = 1421783) B1421783
theorem B1799833 : Blo 630300 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B947897 : Blo 630300 947897 := bstep (se 2 (by rfl) ⟨355461, by rfl⟩ : syracuseStep 947897 = 710923) B710923
theorem B1603273 : Blo 630300 1603273 := bstep (se 2 (by rfl) ⟨601227, by rfl⟩ : syracuseStep 1603273 = 1202455) B1202455
theorem B947975 : Blo 630300 947975 := bstep (se 1 (by rfl) ⟨710981, by rfl⟩ : syracuseStep 947975 = 1421963) B1421963
theorem B948011 : Blo 630300 948011 := bstep (se 1 (by rfl) ⟨711008, by rfl⟩ : syracuseStep 948011 = 1422017) B1422017
theorem B948041 : Blo 630300 948041 := bstep (se 2 (by rfl) ⟨355515, by rfl⟩ : syracuseStep 948041 = 711031) B711031
theorem B1603415 : Blo 630300 1603415 := bstep (se 1 (by rfl) ⟨1202561, by rfl⟩ : syracuseStep 1603415 = 2405123) B2405123
theorem B1800083 : Blo 630300 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B948155 : Blo 630300 948155 := bstep (se 1 (by rfl) ⟨711116, by rfl⟩ : syracuseStep 948155 = 1422233) B1422233
theorem B948215 : Blo 630300 948215 := bstep (se 1 (by rfl) ⟨711161, by rfl⟩ : syracuseStep 948215 = 1422323) B1422323
theorem B3209219 : Blo 630300 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B6944779 : Blo 630300 6944779 := bstep (se 1 (by rfl) ⟨5208584, by rfl⟩ : syracuseStep 6944779 = 10417169) B10417169
theorem B948239 : Blo 630300 948239 := bstep (se 1 (by rfl) ⟨711179, by rfl⟩ : syracuseStep 948239 = 1422359) B1422359
theorem B13694993 : Blo 630300 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B948281 : Blo 630300 948281 := bstep (se 2 (by rfl) ⟨355605, by rfl⟩ : syracuseStep 948281 = 711211) B711211
theorem B948359 : Blo 630300 948359 := bstep (se 1 (by rfl) ⟨711269, by rfl⟩ : syracuseStep 948359 = 1422539) B1422539
theorem B948395 : Blo 630300 948395 := bstep (se 1 (by rfl) ⟨711296, by rfl⟩ : syracuseStep 948395 = 1422593) B1422593
theorem B948425 : Blo 630300 948425 := bstep (se 2 (by rfl) ⟨355659, by rfl⟩ : syracuseStep 948425 = 711319) B711319
theorem B948539 : Blo 630300 948539 := bstep (se 1 (by rfl) ⟨711404, by rfl⟩ : syracuseStep 948539 = 1422809) B1422809
theorem B948599 : Blo 630300 948599 := bstep (se 1 (by rfl) ⟨711449, by rfl⟩ : syracuseStep 948599 = 1422899) B1422899
theorem B948623 : Blo 630300 948623 := bstep (se 1 (by rfl) ⟨711467, by rfl⟩ : syracuseStep 948623 = 1422935) B1422935
theorem B948665 : Blo 630300 948665 := bstep (se 2 (by rfl) ⟨355749, by rfl⟩ : syracuseStep 948665 = 711499) B711499
theorem B6912515 : Blo 630300 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B948743 : Blo 630300 948743 := bstep (se 1 (by rfl) ⟨711557, by rfl⟩ : syracuseStep 948743 = 1423115) B1423115
theorem B948779 : Blo 630300 948779 := bstep (se 1 (by rfl) ⟨711584, by rfl⟩ : syracuseStep 948779 = 1423169) B1423169
theorem B948809 : Blo 630300 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B1014457 : Blo 630300 1014457 := bstep (se 2 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 1014457 = 760843) B760843
theorem B948923 : Blo 630300 948923 := bstep (se 1 (by rfl) ⟨711692, by rfl⟩ : syracuseStep 948923 = 1423385) B1423385
theorem B3046081 : Blo 630300 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B948983 : Blo 630300 948983 := bstep (se 1 (by rfl) ⟨711737, by rfl⟩ : syracuseStep 948983 = 1423475) B1423475
theorem B949007 : Blo 630300 949007 := bstep (se 1 (by rfl) ⟨711755, by rfl⟩ : syracuseStep 949007 = 1423511) B1423511
theorem B949049 : Blo 630300 949049 := bstep (se 2 (by rfl) ⟨355893, by rfl⟩ : syracuseStep 949049 = 711787) B711787
theorem B1801075 : Blo 630300 1801075 := bstep (se 1 (by rfl) ⟨1350806, by rfl⟩ : syracuseStep 1801075 = 2701613) B2701613
theorem B949127 : Blo 630300 949127 := bstep (se 1 (by rfl) ⟨711845, by rfl⟩ : syracuseStep 949127 = 1423691) B1423691
theorem B2128787 : Blo 630300 2128787 := bstep (se 1 (by rfl) ⟨1596590, by rfl⟩ : syracuseStep 2128787 = 3193181) B3193181
theorem B949163 : Blo 630300 949163 := bstep (se 1 (by rfl) ⟨711872, by rfl⟩ : syracuseStep 949163 = 1423745) B1423745
theorem B949193 : Blo 630300 949193 := bstep (se 2 (by rfl) ⟨355947, by rfl⟩ : syracuseStep 949193 = 711895) B711895
theorem B18250757 : Blo 630300 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B949307 : Blo 630300 949307 := bstep (se 1 (by rfl) ⟨711980, by rfl⟩ : syracuseStep 949307 = 1423961) B1423961
theorem B949367 : Blo 630300 949367 := bstep (se 1 (by rfl) ⟨712025, by rfl⟩ : syracuseStep 949367 = 1424051) B1424051
theorem B949391 : Blo 630300 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B3603629 : Blo 630300 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B949433 : Blo 630300 949433 := bstep (se 2 (by rfl) ⟨356037, by rfl⟩ : syracuseStep 949433 = 712075) B712075
theorem B949511 : Blo 630300 949511 := bstep (se 1 (by rfl) ⟨712133, by rfl⟩ : syracuseStep 949511 = 1424267) B1424267
theorem B949547 : Blo 630300 949547 := bstep (se 1 (by rfl) ⟨712160, by rfl⟩ : syracuseStep 949547 = 1424321) B1424321
theorem B949577 : Blo 630300 949577 := bstep (se 2 (by rfl) ⟨356091, by rfl⟩ : syracuseStep 949577 = 712183) B712183
theorem B1015175 : Blo 630300 1015175 := bstep (se 1 (by rfl) ⟨761381, by rfl⟩ : syracuseStep 1015175 = 1522763) B1522763
theorem B949691 : Blo 630300 949691 := bstep (se 1 (by rfl) ⟨712268, by rfl⟩ : syracuseStep 949691 = 1424537) B1424537
theorem B949751 : Blo 630300 949751 := bstep (se 1 (by rfl) ⟨712313, by rfl⟩ : syracuseStep 949751 = 1424627) B1424627
theorem B949775 : Blo 630300 949775 := bstep (se 1 (by rfl) ⟨712331, by rfl⟩ : syracuseStep 949775 = 1424663) B1424663
theorem B949817 : Blo 630300 949817 := bstep (se 2 (by rfl) ⟨356181, by rfl⟩ : syracuseStep 949817 = 712363) B712363
theorem B3210839 : Blo 630300 3210839 := bstep (se 1 (by rfl) ⟨2408129, by rfl⟩ : syracuseStep 3210839 = 4816259) B4816259
theorem B949895 : Blo 630300 949895 := bstep (se 1 (by rfl) ⟨712421, by rfl⟩ : syracuseStep 949895 = 1424843) B1424843
theorem B949931 : Blo 630300 949931 := bstep (se 1 (by rfl) ⟨712448, by rfl⟩ : syracuseStep 949931 = 1424897) B1424897
theorem B949961 : Blo 630300 949961 := bstep (se 2 (by rfl) ⟨356235, by rfl⟩ : syracuseStep 949961 = 712471) B712471
theorem B950075 : Blo 630300 950075 := bstep (se 1 (by rfl) ⟨712556, by rfl⟩ : syracuseStep 950075 = 1425113) B1425113
theorem B1605491 : Blo 630300 1605491 := bstep (se 1 (by rfl) ⟨1204118, by rfl⟩ : syracuseStep 1605491 = 2408237) B2408237
theorem B950135 : Blo 630300 950135 := bstep (se 1 (by rfl) ⟨712601, by rfl⟩ : syracuseStep 950135 = 1425203) B1425203
theorem B1015687 : Blo 630300 1015687 := bstep (se 1 (by rfl) ⟨761765, by rfl⟩ : syracuseStep 1015687 = 1523531) B1523531
theorem B950159 : Blo 630300 950159 := bstep (se 1 (by rfl) ⟨712619, by rfl⟩ : syracuseStep 950159 = 1425239) B1425239
theorem B950201 : Blo 630300 950201 := bstep (se 2 (by rfl) ⟨356325, by rfl⟩ : syracuseStep 950201 = 712651) B712651
theorem B2129921 : Blo 630300 2129921 := bstep (se 2 (by rfl) ⟨798720, by rfl⟩ : syracuseStep 2129921 = 1597441) B1597441
theorem B950351 : Blo 630300 950351 := bstep (se 1 (by rfl) ⟨712763, by rfl⟩ : syracuseStep 950351 = 1425527) B1425527
theorem B950471 : Blo 630300 950471 := bstep (se 1 (by rfl) ⟨712853, by rfl⟩ : syracuseStep 950471 = 1425707) B1425707
theorem B950633 : Blo 630300 950633 := bstep (se 2 (by rfl) ⟨356487, by rfl⟩ : syracuseStep 950633 = 712975) B712975
theorem B950711 : Blo 630300 950711 := bstep (se 1 (by rfl) ⟨713033, by rfl⟩ : syracuseStep 950711 = 1426067) B1426067
theorem B950747 : Blo 630300 950747 := bstep (se 1 (by rfl) ⟨713060, by rfl⟩ : syracuseStep 950747 = 1426121) B1426121
theorem B1278587 : Blo 630300 1278587 := bstep (se 1 (by rfl) ⟨958940, by rfl⟩ : syracuseStep 1278587 = 1917881) B1917881
theorem B2130731 : Blo 630300 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B951215 : Blo 630300 951215 := bstep (se 1 (by rfl) ⟨713411, by rfl⟩ : syracuseStep 951215 = 1426823) B1426823
theorem B951305 : Blo 630300 951305 := bstep (se 2 (by rfl) ⟨356739, by rfl⟩ : syracuseStep 951305 = 713479) B713479
theorem B951335 : Blo 630300 951335 := bstep (se 1 (by rfl) ⟨713501, by rfl⟩ : syracuseStep 951335 = 1427003) B1427003
theorem B2131001 : Blo 630300 2131001 := bstep (se 2 (by rfl) ⟨799125, by rfl⟩ : syracuseStep 2131001 = 1598251) B1598251
theorem B951419 : Blo 630300 951419 := bstep (se 1 (by rfl) ⟨713564, by rfl⟩ : syracuseStep 951419 = 1427129) B1427129
theorem B2131325 : Blo 630300 2131325 := bstep (se 3 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 2131325 = 799247) B799247
theorem B2131595 : Blo 630300 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B1803991 : Blo 630300 1803991 := bstep (se 1 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 1803991 = 2705987) B2705987
theorem B1804025 : Blo 630300 1804025 := bstep (se 2 (by rfl) ⟨676509, by rfl⟩ : syracuseStep 1804025 = 1353019) B1353019
theorem B1083241 : Blo 630300 1083241 := bstep (se 2 (by rfl) ⟨406215, by rfl⟩ : syracuseStep 1083241 = 812431) B812431
theorem B1804139 : Blo 630300 1804139 := bstep (se 1 (by rfl) ⟨1353104, by rfl⟩ : syracuseStep 1804139 = 2706209) B2706209
theorem B2393975 : Blo 630300 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B1804207 : Blo 630300 1804207 := bstep (se 1 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 1804207 = 2706311) B2706311
theorem B9865223 : Blo 630300 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B1443847 : Blo 630300 1443847 := bstep (se 1 (by rfl) ⟨1082885, by rfl⟩ : syracuseStep 1443847 = 2165771) B2165771
theorem B1902977 : Blo 630300 1902977 := bstep (se 2 (by rfl) ⟨713616, by rfl⟩ : syracuseStep 1902977 = 1427233) B1427233
theorem B30771683 : Blo 630300 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B2132513 : Blo 630300 2132513 := bstep (se 2 (by rfl) ⟨799692, by rfl⟩ : syracuseStep 2132513 = 1599385) B1599385
theorem B2132729 : Blo 630300 2132729 := bstep (se 2 (by rfl) ⟨799773, by rfl⟩ : syracuseStep 2132729 = 1599547) B1599547
theorem B2394947 : Blo 630300 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B2132999 : Blo 630300 2132999 := bstep (se 1 (by rfl) ⟨1599749, by rfl⟩ : syracuseStep 2132999 = 3199499) B3199499
theorem B106597387 : Blo 630300 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B2133107 : Blo 630300 2133107 := bstep (se 1 (by rfl) ⟨1599830, by rfl⟩ : syracuseStep 2133107 = 3199661) B3199661
theorem B1805483 : Blo 630300 1805483 := bstep (se 1 (by rfl) ⟨1354112, by rfl⟩ : syracuseStep 1805483 = 2708225) B2708225
theorem B2395403 : Blo 630300 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B2133377 : Blo 630300 2133377 := bstep (se 2 (by rfl) ⟨800016, by rfl⟩ : syracuseStep 2133377 = 1600033) B1600033
theorem B2396087 : Blo 630300 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B757883 : Blo 630300 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B2134187 : Blo 630300 2134187 := bstep (se 1 (by rfl) ⟨1600640, by rfl⟩ : syracuseStep 2134187 = 3201281) B3201281
theorem B11506049 : Blo 630300 11506049 := bstep (se 2 (by rfl) ⟨4314768, by rfl⟩ : syracuseStep 11506049 = 8629537) B8629537
theorem B6820469 : Blo 630300 6820469 := bstep (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) B639419
theorem B2396861 : Blo 630300 2396861 := bstep (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) B898823
theorem B2134727 : Blo 630300 2134727 := bstep (se 1 (by rfl) ⟨1601045, by rfl⟩ : syracuseStep 2134727 = 3202091) B3202091
theorem B3249071 : Blo 630300 3249071 := bstep (se 1 (by rfl) ⟨2436803, by rfl⟩ : syracuseStep 3249071 = 4873607) B4873607
theorem B2626561 : Blo 630300 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B13899023 : Blo 630300 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B2397545 : Blo 630300 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B1348969 : Blo 630300 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B2135591 : Blo 630300 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B988751 : Blo 630300 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B1283663 : Blo 630300 1283663 := bstep (se 1 (by rfl) ⟨962747, by rfl⟩ : syracuseStep 1283663 = 1925495) B1925495
theorem B2135699 : Blo 630300 2135699 := bstep (se 1 (by rfl) ⟨1601774, by rfl⟩ : syracuseStep 2135699 = 3203549) B3203549
theorem B4855619 : Blo 630300 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B2135915 : Blo 630300 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B2135969 : Blo 630300 2135969 := bstep (se 2 (by rfl) ⟨800988, by rfl⟩ : syracuseStep 2135969 = 1601977) B1601977
theorem B6821891 : Blo 630300 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B4790501 : Blo 630300 4790501 := bstep (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) B898219
theorem B23107841 : Blo 630300 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B2136563 : Blo 630300 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B5118497 : Blo 630300 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B8460935 : Blo 630300 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B2137103 : Blo 630300 2137103 := bstep (se 1 (by rfl) ⟨1602827, by rfl⟩ : syracuseStep 2137103 = 3205655) B3205655
theorem B6069593 : Blo 630300 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B6856109 : Blo 630300 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B2399777 : Blo 630300 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B630311 : Blo 630300 630311 := bstep (se 1 (by rfl) ⟨472733, by rfl⟩ : syracuseStep 630311 = 945467) B945467
theorem B12951107 : Blo 630300 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B630351 : Blo 630300 630351 := bstep (se 1 (by rfl) ⟨472763, by rfl⟩ : syracuseStep 630351 = 945527) B945527
theorem B630367 : Blo 630300 630367 := bstep (se 1 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 630367 = 945551) B945551
theorem B2137697 : Blo 630300 2137697 := bstep (se 2 (by rfl) ⟨801636, by rfl⟩ : syracuseStep 2137697 = 1603273) B1603273
theorem B630395 : Blo 630300 630395 := bstep (se 1 (by rfl) ⟨472796, by rfl⟩ : syracuseStep 630395 = 945593) B945593
theorem B1515131 : Blo 630300 1515131 := bstep (se 1 (by rfl) ⟨1136348, by rfl⟩ : syracuseStep 1515131 = 2272697) B2272697
theorem B2694779 : Blo 630300 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B630447 : Blo 630300 630447 := bstep (se 1 (by rfl) ⟨472835, by rfl⟩ : syracuseStep 630447 = 945671) B945671
theorem B630471 : Blo 630300 630471 := bstep (se 1 (by rfl) ⟨472853, by rfl⟩ : syracuseStep 630471 = 945707) B945707
theorem B1351379 : Blo 630300 1351379 := bstep (se 1 (by rfl) ⟨1013534, by rfl⟩ : syracuseStep 1351379 = 2027069) B2027069
theorem B630491 : Blo 630300 630491 := bstep (se 1 (by rfl) ⟨472868, by rfl⟩ : syracuseStep 630491 = 945737) B945737
theorem B630567 : Blo 630300 630567 := bstep (se 1 (by rfl) ⟨472925, by rfl⟩ : syracuseStep 630567 = 945851) B945851
theorem B630607 : Blo 630300 630607 := bstep (se 1 (by rfl) ⟨472955, by rfl⟩ : syracuseStep 630607 = 945911) B945911
theorem B630623 : Blo 630300 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B630651 : Blo 630300 630651 := bstep (se 1 (by rfl) ⟨472988, by rfl⟩ : syracuseStep 630651 = 945977) B945977
theorem B630703 : Blo 630300 630703 := bstep (se 1 (by rfl) ⟨473027, by rfl⟩ : syracuseStep 630703 = 946055) B946055
theorem B630727 : Blo 630300 630727 := bstep (se 1 (by rfl) ⟨473045, by rfl⟩ : syracuseStep 630727 = 946091) B946091
theorem B630747 : Blo 630300 630747 := bstep (se 1 (by rfl) ⟨473060, by rfl⟩ : syracuseStep 630747 = 946121) B946121
theorem B2400263 : Blo 630300 2400263 := bstep (se 1 (by rfl) ⟨1800197, by rfl⟩ : syracuseStep 2400263 = 3600395) B3600395
theorem B630823 : Blo 630300 630823 := bstep (se 1 (by rfl) ⟨473117, by rfl⟩ : syracuseStep 630823 = 946235) B946235
theorem B630863 : Blo 630300 630863 := bstep (se 1 (by rfl) ⟨473147, by rfl⟩ : syracuseStep 630863 = 946295) B946295
theorem B630879 : Blo 630300 630879 := bstep (se 1 (by rfl) ⟨473159, by rfl⟩ : syracuseStep 630879 = 946319) B946319
theorem B630907 : Blo 630300 630907 := bstep (se 1 (by rfl) ⟨473180, by rfl⟩ : syracuseStep 630907 = 946361) B946361
theorem B16425109 : Blo 630300 16425109 := bstep (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) B769927
theorem B630959 : Blo 630300 630959 := bstep (se 1 (by rfl) ⟨473219, by rfl⟩ : syracuseStep 630959 = 946439) B946439
theorem B630983 : Blo 630300 630983 := bstep (se 1 (by rfl) ⟨473237, by rfl⟩ : syracuseStep 630983 = 946475) B946475
theorem B631003 : Blo 630300 631003 := bstep (se 1 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 631003 = 946505) B946505
theorem B631079 : Blo 630300 631079 := bstep (se 1 (by rfl) ⟨473309, by rfl⟩ : syracuseStep 631079 = 946619) B946619
theorem B631119 : Blo 630300 631119 := bstep (se 1 (by rfl) ⟨473339, by rfl⟩ : syracuseStep 631119 = 946679) B946679
theorem B631135 : Blo 630300 631135 := bstep (se 1 (by rfl) ⟨473351, by rfl⟩ : syracuseStep 631135 = 946703) B946703
theorem B631163 : Blo 630300 631163 := bstep (se 1 (by rfl) ⟨473372, by rfl⟩ : syracuseStep 631163 = 946745) B946745
theorem B631215 : Blo 630300 631215 := bstep (se 1 (by rfl) ⟨473411, by rfl⟩ : syracuseStep 631215 = 946823) B946823
theorem B631239 : Blo 630300 631239 := bstep (se 1 (by rfl) ⟨473429, by rfl⟩ : syracuseStep 631239 = 946859) B946859
theorem B631259 : Blo 630300 631259 := bstep (se 1 (by rfl) ⟨473444, by rfl⟩ : syracuseStep 631259 = 946889) B946889
theorem B2400749 : Blo 630300 2400749 := bstep (se 3 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 2400749 = 900281) B900281
theorem B631335 : Blo 630300 631335 := bstep (se 1 (by rfl) ⟨473501, by rfl⟩ : syracuseStep 631335 = 947003) B947003
theorem B1024591 : Blo 630300 1024591 := bstep (se 1 (by rfl) ⟨768443, by rfl⟩ : syracuseStep 1024591 = 1536887) B1536887
theorem B631375 : Blo 630300 631375 := bstep (se 1 (by rfl) ⟨473531, by rfl⟩ : syracuseStep 631375 = 947063) B947063
theorem B631391 : Blo 630300 631391 := bstep (se 1 (by rfl) ⟨473543, by rfl⟩ : syracuseStep 631391 = 947087) B947087
theorem B631419 : Blo 630300 631419 := bstep (se 1 (by rfl) ⟨473564, by rfl⟩ : syracuseStep 631419 = 947129) B947129
theorem B631471 : Blo 630300 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B631495 : Blo 630300 631495 := bstep (se 1 (by rfl) ⟨473621, by rfl⟩ : syracuseStep 631495 = 947243) B947243
theorem B631515 : Blo 630300 631515 := bstep (se 1 (by rfl) ⟨473636, by rfl⟩ : syracuseStep 631515 = 947273) B947273
theorem B631591 : Blo 630300 631591 := bstep (se 1 (by rfl) ⟨473693, by rfl⟩ : syracuseStep 631591 = 947387) B947387
theorem B631631 : Blo 630300 631631 := bstep (se 1 (by rfl) ⟨473723, by rfl⟩ : syracuseStep 631631 = 947447) B947447
theorem B631647 : Blo 630300 631647 := bstep (se 1 (by rfl) ⟨473735, by rfl⟩ : syracuseStep 631647 = 947471) B947471
theorem B631675 : Blo 630300 631675 := bstep (se 1 (by rfl) ⟨473756, by rfl⟩ : syracuseStep 631675 = 947513) B947513
theorem B1352609 : Blo 630300 1352609 := bstep (se 2 (by rfl) ⟨507228, by rfl⟩ : syracuseStep 1352609 = 1014457) B1014457
theorem B631727 : Blo 630300 631727 := bstep (se 1 (by rfl) ⟨473795, by rfl⟩ : syracuseStep 631727 = 947591) B947591
theorem B7906223 : Blo 630300 7906223 := bstep (se 1 (by rfl) ⟨5929667, by rfl⟩ : syracuseStep 7906223 = 11859335) B11859335
theorem B631751 : Blo 630300 631751 := bstep (se 1 (by rfl) ⟨473813, by rfl⟩ : syracuseStep 631751 = 947627) B947627
theorem B631771 : Blo 630300 631771 := bstep (se 1 (by rfl) ⟨473828, by rfl⟩ : syracuseStep 631771 = 947657) B947657
theorem B2139155 : Blo 630300 2139155 := bstep (se 1 (by rfl) ⟨1604366, by rfl⟩ : syracuseStep 2139155 = 3208733) B3208733
theorem B631847 : Blo 630300 631847 := bstep (se 1 (by rfl) ⟨473885, by rfl⟩ : syracuseStep 631847 = 947771) B947771
theorem B631887 : Blo 630300 631887 := bstep (se 1 (by rfl) ⟨473915, by rfl⟩ : syracuseStep 631887 = 947831) B947831
theorem B631903 : Blo 630300 631903 := bstep (se 1 (by rfl) ⟨473927, by rfl⟩ : syracuseStep 631903 = 947855) B947855
theorem B631931 : Blo 630300 631931 := bstep (se 1 (by rfl) ⟨473948, by rfl⟩ : syracuseStep 631931 = 947897) B947897
theorem B2401433 : Blo 630300 2401433 := bstep (se 2 (by rfl) ⟨900537, by rfl⟩ : syracuseStep 2401433 = 1801075) B1801075
theorem B631983 : Blo 630300 631983 := bstep (se 1 (by rfl) ⟨473987, by rfl⟩ : syracuseStep 631983 = 947975) B947975
theorem B632007 : Blo 630300 632007 := bstep (se 1 (by rfl) ⟨474005, by rfl⟩ : syracuseStep 632007 = 948011) B948011
theorem B632027 : Blo 630300 632027 := bstep (se 1 (by rfl) ⟨474020, by rfl⟩ : syracuseStep 632027 = 948041) B948041
theorem B632103 : Blo 630300 632103 := bstep (se 1 (by rfl) ⟨474077, by rfl⟩ : syracuseStep 632103 = 948155) B948155
theorem B632143 : Blo 630300 632143 := bstep (se 1 (by rfl) ⟨474107, by rfl⟩ : syracuseStep 632143 = 948215) B948215
theorem B2139479 : Blo 630300 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B632159 : Blo 630300 632159 := bstep (se 1 (by rfl) ⟨474119, by rfl⟩ : syracuseStep 632159 = 948239) B948239
theorem B632187 : Blo 630300 632187 := bstep (se 1 (by rfl) ⟨474140, by rfl⟩ : syracuseStep 632187 = 948281) B948281
theorem B632239 : Blo 630300 632239 := bstep (se 1 (by rfl) ⟨474179, by rfl⟩ : syracuseStep 632239 = 948359) B948359
theorem B632263 : Blo 630300 632263 := bstep (se 1 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 632263 = 948395) B948395
theorem B632283 : Blo 630300 632283 := bstep (se 1 (by rfl) ⟨474212, by rfl⟩ : syracuseStep 632283 = 948425) B948425
theorem B632359 : Blo 630300 632359 := bstep (se 1 (by rfl) ⟨474269, by rfl⟩ : syracuseStep 632359 = 948539) B948539
theorem B632399 : Blo 630300 632399 := bstep (se 1 (by rfl) ⟨474299, by rfl⟩ : syracuseStep 632399 = 948599) B948599
theorem B632415 : Blo 630300 632415 := bstep (se 1 (by rfl) ⟨474311, by rfl⟩ : syracuseStep 632415 = 948623) B948623
theorem B1418849 : Blo 630300 1418849 := bstep (se 2 (by rfl) ⟨532068, by rfl⟩ : syracuseStep 1418849 = 1064137) B1064137
theorem B632443 : Blo 630300 632443 := bstep (se 1 (by rfl) ⟨474332, by rfl⟩ : syracuseStep 632443 = 948665) B948665
theorem B632495 : Blo 630300 632495 := bstep (se 1 (by rfl) ⟨474371, by rfl⟩ : syracuseStep 632495 = 948743) B948743
theorem B632519 : Blo 630300 632519 := bstep (se 1 (by rfl) ⟨474389, by rfl⟩ : syracuseStep 632519 = 948779) B948779
theorem B632539 : Blo 630300 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B632615 : Blo 630300 632615 := bstep (se 1 (by rfl) ⟨474461, by rfl⟩ : syracuseStep 632615 = 948923) B948923
theorem B632655 : Blo 630300 632655 := bstep (se 1 (by rfl) ⟨474491, by rfl⟩ : syracuseStep 632655 = 948983) B948983
theorem B632671 : Blo 630300 632671 := bstep (se 1 (by rfl) ⟨474503, by rfl⟩ : syracuseStep 632671 = 949007) B949007
theorem B632699 : Blo 630300 632699 := bstep (se 1 (by rfl) ⟨474524, by rfl⟩ : syracuseStep 632699 = 949049) B949049
theorem B632751 : Blo 630300 632751 := bstep (se 1 (by rfl) ⟨474563, by rfl⟩ : syracuseStep 632751 = 949127) B949127
theorem B1419191 : Blo 630300 1419191 := bstep (se 1 (by rfl) ⟨1064393, by rfl⟩ : syracuseStep 1419191 = 2128787) B2128787
theorem B632775 : Blo 630300 632775 := bstep (se 1 (by rfl) ⟨474581, by rfl⟩ : syracuseStep 632775 = 949163) B949163
theorem B632795 : Blo 630300 632795 := bstep (se 1 (by rfl) ⟨474596, by rfl⟩ : syracuseStep 632795 = 949193) B949193
theorem B12167171 : Blo 630300 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B632871 : Blo 630300 632871 := bstep (se 1 (by rfl) ⟨474653, by rfl⟩ : syracuseStep 632871 = 949307) B949307
theorem B632911 : Blo 630300 632911 := bstep (se 1 (by rfl) ⟨474683, by rfl⟩ : syracuseStep 632911 = 949367) B949367
theorem B632927 : Blo 630300 632927 := bstep (se 1 (by rfl) ⟨474695, by rfl⟩ : syracuseStep 632927 = 949391) B949391
theorem B2402419 : Blo 630300 2402419 := bstep (se 1 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 2402419 = 3603629) B3603629
theorem B632955 : Blo 630300 632955 := bstep (se 1 (by rfl) ⟨474716, by rfl⟩ : syracuseStep 632955 = 949433) B949433
theorem B633007 : Blo 630300 633007 := bstep (se 1 (by rfl) ⟨474755, by rfl⟩ : syracuseStep 633007 = 949511) B949511
theorem B633031 : Blo 630300 633031 := bstep (se 1 (by rfl) ⟨474773, by rfl⟩ : syracuseStep 633031 = 949547) B949547
theorem B633051 : Blo 630300 633051 := bstep (se 1 (by rfl) ⟨474788, by rfl⟩ : syracuseStep 633051 = 949577) B949577
theorem B633127 : Blo 630300 633127 := bstep (se 1 (by rfl) ⟨474845, by rfl⟩ : syracuseStep 633127 = 949691) B949691
theorem B633167 : Blo 630300 633167 := bstep (se 1 (by rfl) ⟨474875, by rfl⟩ : syracuseStep 633167 = 949751) B949751
theorem B8202583 : Blo 630300 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B633183 : Blo 630300 633183 := bstep (se 1 (by rfl) ⟨474887, by rfl⟩ : syracuseStep 633183 = 949775) B949775
theorem B633211 : Blo 630300 633211 := bstep (se 1 (by rfl) ⟨474908, by rfl⟩ : syracuseStep 633211 = 949817) B949817
theorem B2140559 : Blo 630300 2140559 := bstep (se 1 (by rfl) ⟨1605419, by rfl⟩ : syracuseStep 2140559 = 3210839) B3210839
theorem B633263 : Blo 630300 633263 := bstep (se 1 (by rfl) ⟨474947, by rfl⟩ : syracuseStep 633263 = 949895) B949895
theorem B633287 : Blo 630300 633287 := bstep (se 1 (by rfl) ⟨474965, by rfl⟩ : syracuseStep 633287 = 949931) B949931
theorem B633307 : Blo 630300 633307 := bstep (se 1 (by rfl) ⟨474980, by rfl⟩ : syracuseStep 633307 = 949961) B949961
theorem B1419785 : Blo 630300 1419785 := bstep (se 2 (by rfl) ⟨532419, by rfl⟩ : syracuseStep 1419785 = 1064839) B1064839
theorem B1354249 : Blo 630300 1354249 := bstep (se 2 (by rfl) ⟨507843, by rfl⟩ : syracuseStep 1354249 = 1015687) B1015687
theorem B633383 : Blo 630300 633383 := bstep (se 1 (by rfl) ⟨475037, by rfl⟩ : syracuseStep 633383 = 950075) B950075
theorem B633423 : Blo 630300 633423 := bstep (se 1 (by rfl) ⟨475067, by rfl⟩ : syracuseStep 633423 = 950135) B950135
theorem B633439 : Blo 630300 633439 := bstep (se 1 (by rfl) ⟨475079, by rfl⟩ : syracuseStep 633439 = 950159) B950159
theorem B633467 : Blo 630300 633467 := bstep (se 1 (by rfl) ⟨475100, by rfl⟩ : syracuseStep 633467 = 950201) B950201
theorem B633519 : Blo 630300 633519 := bstep (se 1 (by rfl) ⟨475139, by rfl⟩ : syracuseStep 633519 = 950279) B950279
theorem B7383737 : Blo 630300 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B633543 : Blo 630300 633543 := bstep (se 1 (by rfl) ⟨475157, by rfl⟩ : syracuseStep 633543 = 950315) B950315
theorem B633563 : Blo 630300 633563 := bstep (se 1 (by rfl) ⟨475172, by rfl⟩ : syracuseStep 633563 = 950345) B950345
theorem B633639 : Blo 630300 633639 := bstep (se 1 (by rfl) ⟨475229, by rfl⟩ : syracuseStep 633639 = 950459) B950459
theorem B633679 : Blo 630300 633679 := bstep (se 1 (by rfl) ⟨475259, by rfl⟩ : syracuseStep 633679 = 950519) B950519
theorem B1420127 : Blo 630300 1420127 := bstep (se 1 (by rfl) ⟨1065095, by rfl⟩ : syracuseStep 1420127 = 2130191) B2130191
theorem B633695 : Blo 630300 633695 := bstep (se 1 (by rfl) ⟨475271, by rfl⟩ : syracuseStep 633695 = 950543) B950543
theorem B2403179 : Blo 630300 2403179 := bstep (se 1 (by rfl) ⟨1802384, by rfl⟩ : syracuseStep 2403179 = 3604769) B3604769
theorem B633723 : Blo 630300 633723 := bstep (se 1 (by rfl) ⟨475292, by rfl⟩ : syracuseStep 633723 = 950585) B950585
theorem B633775 : Blo 630300 633775 := bstep (se 1 (by rfl) ⟨475331, by rfl⟩ : syracuseStep 633775 = 950663) B950663
theorem B633799 : Blo 630300 633799 := bstep (se 1 (by rfl) ⟨475349, by rfl⟩ : syracuseStep 633799 = 950699) B950699
theorem B633819 : Blo 630300 633819 := bstep (se 1 (by rfl) ⟨475364, by rfl⟩ : syracuseStep 633819 = 950729) B950729
theorem B1420307 : Blo 630300 1420307 := bstep (se 1 (by rfl) ⟨1065230, by rfl⟩ : syracuseStep 1420307 = 2130461) B2130461
theorem B633895 : Blo 630300 633895 := bstep (se 1 (by rfl) ⟨475421, by rfl⟩ : syracuseStep 633895 = 950843) B950843
theorem B633935 : Blo 630300 633935 := bstep (se 1 (by rfl) ⟨475451, by rfl⟩ : syracuseStep 633935 = 950903) B950903
theorem B633951 : Blo 630300 633951 := bstep (se 1 (by rfl) ⟨475463, by rfl⟩ : syracuseStep 633951 = 950927) B950927
theorem B633979 : Blo 630300 633979 := bstep (se 1 (by rfl) ⟨475484, by rfl⟩ : syracuseStep 633979 = 950969) B950969
theorem B634031 : Blo 630300 634031 := bstep (se 1 (by rfl) ⟨475523, by rfl⟩ : syracuseStep 634031 = 951047) B951047
theorem B634055 : Blo 630300 634055 := bstep (se 1 (by rfl) ⟨475541, by rfl⟩ : syracuseStep 634055 = 951083) B951083
theorem B634075 : Blo 630300 634075 := bstep (se 1 (by rfl) ⟨475556, by rfl⟩ : syracuseStep 634075 = 951113) B951113
theorem B634151 : Blo 630300 634151 := bstep (se 1 (by rfl) ⟨475613, by rfl⟩ : syracuseStep 634151 = 951227) B951227
theorem B634191 : Blo 630300 634191 := bstep (se 1 (by rfl) ⟨475643, by rfl⟩ : syracuseStep 634191 = 951287) B951287
theorem B634207 : Blo 630300 634207 := bstep (se 1 (by rfl) ⟨475655, by rfl⟩ : syracuseStep 634207 = 951311) B951311
theorem B1420649 : Blo 630300 1420649 := bstep (se 2 (by rfl) ⟨532743, by rfl⟩ : syracuseStep 1420649 = 1065487) B1065487
theorem B634235 : Blo 630300 634235 := bstep (se 1 (by rfl) ⟨475676, by rfl⟩ : syracuseStep 634235 = 951353) B951353
theorem B634287 : Blo 630300 634287 := bstep (se 1 (by rfl) ⟨475715, by rfl⟩ : syracuseStep 634287 = 951431) B951431
theorem B798331 : Blo 630300 798331 := bstep (se 1 (by rfl) ⟨598748, by rfl⟩ : syracuseStep 798331 = 1197497) B1197497
theorem B1421243 : Blo 630300 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B1421369 : Blo 630300 1421369 := bstep (se 2 (by rfl) ⟨533013, by rfl⟩ : syracuseStep 1421369 = 1066027) B1066027
theorem B8335523 : Blo 630300 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B5779619 : Blo 630300 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B6828209 : Blo 630300 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B1421711 : Blo 630300 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B1520167 : Blo 630300 1520167 := bstep (se 1 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 1520167 = 2280251) B2280251
theorem B6074939 : Blo 630300 6074939 := bstep (se 1 (by rfl) ⟨4556204, by rfl⟩ : syracuseStep 6074939 = 9112409) B9112409
theorem B1422035 : Blo 630300 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B4043627 : Blo 630300 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B9090265 : Blo 630300 9090265 := bstep (se 2 (by rfl) ⟨3408849, by rfl⟩ : syracuseStep 9090265 = 6817699) B6817699
theorem B2700535 : Blo 630300 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B2274571 : Blo 630300 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B800219 : Blo 630300 800219 := bstep (se 1 (by rfl) ⟨600164, by rfl⟩ : syracuseStep 800219 = 1200329) B1200329
theorem B2274875 : Blo 630300 2274875 := bstep (se 1 (by rfl) ⟨1706156, by rfl⟩ : syracuseStep 2274875 = 3412313) B3412313
theorem B1422971 : Blo 630300 1422971 := bstep (se 1 (by rfl) ⟨1067228, by rfl⟩ : syracuseStep 1422971 = 2134457) B2134457
theorem B7222931 : Blo 630300 7222931 := bstep (se 1 (by rfl) ⟨5417198, by rfl⟩ : syracuseStep 7222931 = 10834397) B10834397
theorem B2307799 : Blo 630300 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B1423097 : Blo 630300 1423097 := bstep (se 2 (by rfl) ⟨533661, by rfl⟩ : syracuseStep 1423097 = 1067323) B1067323
theorem B2701151 : Blo 630300 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B4044653 : Blo 630300 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B3192695 : Blo 630300 3192695 := bstep (se 1 (by rfl) ⟨2394521, by rfl⟩ : syracuseStep 3192695 = 4789043) B4789043
theorem B800695 : Blo 630300 800695 := bstep (se 1 (by rfl) ⟨600521, by rfl⟩ : syracuseStep 800695 = 1201043) B1201043
theorem B4437947 : Blo 630300 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B1423367 : Blo 630300 1423367 := bstep (se 1 (by rfl) ⟨1067525, by rfl⟩ : syracuseStep 1423367 = 2135051) B2135051
theorem B1423439 : Blo 630300 1423439 := bstep (se 1 (by rfl) ⟨1067579, by rfl⟩ : syracuseStep 1423439 = 2135159) B2135159
theorem B2570393 : Blo 630300 2570393 := bstep (se 2 (by rfl) ⟨963897, by rfl⟩ : syracuseStep 2570393 = 1927795) B1927795
theorem B1423835 : Blo 630300 1423835 := bstep (se 1 (by rfl) ⟨1067876, by rfl⟩ : syracuseStep 1423835 = 2135753) B2135753
theorem B2407097 : Blo 630300 2407097 := bstep (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) B1805323
theorem B1620695 : Blo 630300 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B2276257 : Blo 630300 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B1424303 : Blo 630300 1424303 := bstep (se 1 (by rfl) ⟨1068227, by rfl⟩ : syracuseStep 1424303 = 2136455) B2136455
theorem B39500723 : Blo 630300 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B1063867 : Blo 630300 1063867 := bstep (se 1 (by rfl) ⟨797900, by rfl⟩ : syracuseStep 1063867 = 1595801) B1595801
theorem B1063975 : Blo 630300 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B3292211 : Blo 630300 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B1981597 : Blo 630300 1981597 := bstep (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) B743099
theorem B1424555 : Blo 630300 1424555 := bstep (se 1 (by rfl) ⟨1068416, by rfl⟩ : syracuseStep 1424555 = 2136833) B2136833
theorem B801991 : Blo 630300 801991 := bstep (se 1 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 801991 = 1202987) B1202987
theorem B4799735 : Blo 630300 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B1064299 : Blo 630300 1064299 := bstep (se 1 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 1064299 = 1596449) B1596449
theorem B1425095 : Blo 630300 1425095 := bstep (se 1 (by rfl) ⟨1068821, by rfl⟩ : syracuseStep 1425095 = 2137643) B2137643
theorem B4800221 : Blo 630300 4800221 := bstep (se 3 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 4800221 = 1800083) B1800083
theorem B1097465 : Blo 630300 1097465 := bstep (se 2 (by rfl) ⟨411549, by rfl⟩ : syracuseStep 1097465 = 823099) B823099
theorem B901039 : Blo 630300 901039 := bstep (se 1 (by rfl) ⟨675779, by rfl⟩ : syracuseStep 901039 = 1351559) B1351559
theorem B4571225 : Blo 630300 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B3850355 : Blo 630300 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B1065359 : Blo 630300 1065359 := bstep (se 1 (by rfl) ⟨799019, by rfl⟩ : syracuseStep 1065359 = 1598039) B1598039
theorem B1851929 : Blo 630300 1851929 := bstep (se 2 (by rfl) ⟨694473, by rfl⟩ : syracuseStep 1851929 = 1388947) B1388947
theorem B1425959 : Blo 630300 1425959 := bstep (se 1 (by rfl) ⟨1069469, by rfl⟩ : syracuseStep 1425959 = 2138939) B2138939
theorem B2605607 : Blo 630300 2605607 := bstep (se 1 (by rfl) ⟨1954205, by rfl⟩ : syracuseStep 2605607 = 3908411) B3908411
theorem B1196623 : Blo 630300 1196623 := bstep (se 1 (by rfl) ⟨897467, by rfl⟩ : syracuseStep 1196623 = 1794935) B1794935
theorem B1065595 : Blo 630300 1065595 := bstep (se 1 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 1065595 = 1598393) B1598393
theorem B1426283 : Blo 630300 1426283 := bstep (se 1 (by rfl) ⟨1069712, by rfl⟩ : syracuseStep 1426283 = 2139425) B2139425
theorem B8078231 : Blo 630300 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B1426337 : Blo 630300 1426337 := bstep (se 2 (by rfl) ⟨534876, by rfl⟩ : syracuseStep 1426337 = 1069753) B1069753
theorem B640039 : Blo 630300 640039 := bstep (se 1 (by rfl) ⟨480029, by rfl⟩ : syracuseStep 640039 = 960059) B960059
theorem B902183 : Blo 630300 902183 := bstep (se 1 (by rfl) ⟨676637, by rfl⟩ : syracuseStep 902183 = 1353275) B1353275
theorem B6145075 : Blo 630300 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B7193771 : Blo 630300 7193771 := bstep (se 1 (by rfl) ⟨5395328, by rfl⟩ : syracuseStep 7193771 = 10790657) B10790657
theorem B1426679 : Blo 630300 1426679 := bstep (se 1 (by rfl) ⟨1070009, by rfl⟩ : syracuseStep 1426679 = 2140019) B2140019
theorem B1066459 : Blo 630300 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B673319 : Blo 630300 673319 := bstep (se 1 (by rfl) ⟨504989, by rfl⟩ : syracuseStep 673319 = 1009979) B1009979
theorem B1918561 : Blo 630300 1918561 := bstep (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) B1438921
theorem B1197929 : Blo 630300 1197929 := bstep (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) B898447
theorem B7817219 : Blo 630300 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B1067087 : Blo 630300 1067087 := bstep (se 1 (by rfl) ⟨800315, by rfl⟩ : syracuseStep 1067087 = 1600631) B1600631
theorem B5130497 : Blo 630300 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B8636705 : Blo 630300 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B3590689 : Blo 630300 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B9259705 : Blo 630300 9259705 := bstep (se 2 (by rfl) ⟨3472389, by rfl⟩ : syracuseStep 9259705 = 6944779) B6944779
theorem B1198955 : Blo 630300 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B1067951 : Blo 630300 1067951 := bstep (se 1 (by rfl) ⟨800963, by rfl⟩ : syracuseStep 1067951 = 1601927) B1601927
theorem B3197879 : Blo 630300 3197879 := bstep (se 1 (by rfl) ⟨2398409, by rfl⟩ : syracuseStep 3197879 = 4796819) B4796819
theorem B1068383 : Blo 630300 1068383 := bstep (se 1 (by rfl) ⟨801287, by rfl⟩ : syracuseStep 1068383 = 1602575) B1602575
theorem B1199623 : Blo 630300 1199623 := bstep (se 1 (by rfl) ⟨899717, by rfl⟩ : syracuseStep 1199623 = 1799435) B1799435
theorem B1068943 : Blo 630300 1068943 := bstep (se 1 (by rfl) ⟨801707, by rfl⟩ : syracuseStep 1068943 = 1603415) B1603415
theorem B9129995 : Blo 630300 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B7196687 : Blo 630300 7196687 := bstep (se 1 (by rfl) ⟨5397515, by rfl⟩ : syracuseStep 7196687 = 10795031) B10795031
theorem B1953811 : Blo 630300 1953811 := bstep (se 1 (by rfl) ⟨1465358, by rfl⟩ : syracuseStep 1953811 = 2930717) B2930717
theorem B5394509 : Blo 630300 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B4608343 : Blo 630300 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B3199337 : Blo 630300 3199337 := bstep (se 2 (by rfl) ⟨1199751, by rfl⟩ : syracuseStep 3199337 = 2399503) B2399503
theorem B709159 : Blo 630300 709159 := bstep (se 1 (by rfl) ⟨531869, by rfl⟩ : syracuseStep 709159 = 1063739) B1063739
theorem B1069625 : Blo 630300 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B630477553 : Blo 630300 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B676783 : Blo 630300 676783 := bstep (se 1 (by rfl) ⟨507587, by rfl⟩ : syracuseStep 676783 = 1015175) B1015175
theorem B1070327 : Blo 630300 1070327 := bstep (se 1 (by rfl) ⟨802745, by rfl⟩ : syracuseStep 1070327 = 1605491) B1605491
theorem B4806053 : Blo 630300 4806053 := bstep (se 4 (by rfl) ⟨450567, by rfl⟩ : syracuseStep 4806053 = 901135) B901135
theorem B4052443 : Blo 630300 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B1201787 : Blo 630300 1201787 := bstep (se 1 (by rfl) ⟨901340, by rfl⟩ : syracuseStep 1201787 = 1802681) B1802681
theorem B4314845 : Blo 630300 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B4544237 : Blo 630300 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B1202015 : Blo 630300 1202015 := bstep (se 1 (by rfl) ⟨901511, by rfl⟩ : syracuseStep 1202015 = 1803023) B1803023
theorem B1202273 : Blo 630300 1202273 := bstep (se 2 (by rfl) ⟨450852, by rfl⟩ : syracuseStep 1202273 = 901705) B901705
theorem B710779 : Blo 630300 710779 := bstep (se 1 (by rfl) ⟨533084, by rfl⟩ : syracuseStep 710779 = 1066169) B1066169
theorem B1595639 : Blo 630300 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B1202539 : Blo 630300 1202539 := bstep (se 1 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 1202539 = 1803809) B1803809
theorem B711247 : Blo 630300 711247 := bstep (se 1 (by rfl) ⟨533435, by rfl⟩ : syracuseStep 711247 = 1066871) B1066871
theorem B711643 : Blo 630300 711643 := bstep (se 1 (by rfl) ⟨533732, by rfl⟩ : syracuseStep 711643 = 1067465) B1067465
theorem B3038411 : Blo 630300 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B712111 : Blo 630300 712111 := bstep (se 1 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 712111 = 1068167) B1068167
theorem B19946933 : Blo 630300 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1203731 : Blo 630300 1203731 := bstep (se 1 (by rfl) ⟨902798, by rfl⟩ : syracuseStep 1203731 = 1805597) B1805597
theorem B1597067 : Blo 630300 1597067 := bstep (se 1 (by rfl) ⟨1197800, by rfl⟩ : syracuseStep 1597067 = 2395601) B2395601
theorem B1203959 : Blo 630300 1203959 := bstep (se 1 (by rfl) ⟨902969, by rfl⟩ : syracuseStep 1203959 = 1805939) B1805939
theorem B1597279 : Blo 630300 1597279 := bstep (se 1 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 1597279 = 2395919) B2395919
theorem B712543 : Blo 630300 712543 := bstep (se 1 (by rfl) ⟨534407, by rfl⟩ : syracuseStep 712543 = 1068815) B1068815
theorem B1138727 : Blo 630300 1138727 := bstep (se 1 (by rfl) ⟨854045, by rfl⟩ : syracuseStep 1138727 = 1708091) B1708091
theorem B2023481 : Blo 630300 2023481 := bstep (se 2 (by rfl) ⟨758805, by rfl⟩ : syracuseStep 2023481 = 1517611) B1517611
theorem B5398609 : Blo 630300 5398609 := bstep (se 2 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 5398609 = 4048957) B4048957
theorem B712903 : Blo 630300 712903 := bstep (se 1 (by rfl) ⟨534677, by rfl⟩ : syracuseStep 712903 = 1069355) B1069355
theorem B1139131 : Blo 630300 1139131 := bstep (se 1 (by rfl) ⟨854348, by rfl⟩ : syracuseStep 1139131 = 1708697) B1708697
theorem B1598201 : Blo 630300 1598201 := bstep (se 2 (by rfl) ⟨599325, by rfl⟩ : syracuseStep 1598201 = 1198651) B1198651
theorem B5137181 : Blo 630300 5137181 := bstep (se 3 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 5137181 = 1926443) B1926443
theorem B1794889 : Blo 630300 1794889 := bstep (se 2 (by rfl) ⟨673083, by rfl⟩ : syracuseStep 1794889 = 1346167) B1346167
theorem B812155 : Blo 630300 812155 := bstep (se 1 (by rfl) ⟨609116, by rfl⟩ : syracuseStep 812155 = 1218233) B1218233
theorem B3040409 : Blo 630300 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B1795243 : Blo 630300 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B1598849 : Blo 630300 1598849 := bstep (se 2 (by rfl) ⟨599568, by rfl⟩ : syracuseStep 1598849 = 1199137) B1199137
theorem B5137829 : Blo 630300 5137829 := bstep (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) B963343
theorem B5137931 : Blo 630300 5137931 := bstep (se 1 (by rfl) ⟨3853448, by rfl⟩ : syracuseStep 5137931 = 7706897) B7706897
theorem B7202519 : Blo 630300 7202519 := bstep (se 1 (by rfl) ⟨5401889, by rfl⟩ : syracuseStep 7202519 = 10803779) B10803779
theorem B1599659 : Blo 630300 1599659 := bstep (se 1 (by rfl) ⟨1199744, by rfl⟩ : syracuseStep 1599659 = 2399489) B2399489
theorem B2026043 : Blo 630300 2026043 := bstep (se 1 (by rfl) ⟨1519532, by rfl⟩ : syracuseStep 2026043 = 3039065) B3039065
theorem B4811399 : Blo 630300 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B3205817 : Blo 630300 3205817 := bstep (se 2 (by rfl) ⟨1202181, by rfl⟩ : syracuseStep 3205817 = 2404363) B2404363
theorem B6089701 : Blo 630300 6089701 := bstep (se 4 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 6089701 = 1141819) B1141819
theorem B1600519 : Blo 630300 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B945503 : Blo 630300 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B945515 : Blo 630300 945515 := bstep (se 1 (by rfl) ⟨709136, by rfl⟩ : syracuseStep 945515 = 1418273) B1418273
theorem B4550003 : Blo 630300 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B945743 : Blo 630300 945743 := bstep (se 1 (by rfl) ⟨709307, by rfl⟩ : syracuseStep 945743 = 1418615) B1418615
theorem B1601147 : Blo 630300 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B10284677 : Blo 630300 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B2191033 : Blo 630300 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B9760445 : Blo 630300 9760445 := bstep (se 3 (by rfl) ⟨1830083, by rfl⟩ : syracuseStep 9760445 = 3660167) B3660167
theorem B945863 : Blo 630300 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B946025 : Blo 630300 946025 := bstep (se 2 (by rfl) ⟨354759, by rfl⟩ : syracuseStep 946025 = 709519) B709519
theorem B1601441 : Blo 630300 1601441 := bstep (se 2 (by rfl) ⟨600540, by rfl⟩ : syracuseStep 1601441 = 1201081) B1201081
theorem B946103 : Blo 630300 946103 := bstep (se 1 (by rfl) ⟨709577, by rfl⟩ : syracuseStep 946103 = 1419155) B1419155
theorem B946139 : Blo 630300 946139 := bstep (se 1 (by rfl) ⟨709604, by rfl⟩ : syracuseStep 946139 = 1419209) B1419209
theorem B4812857 : Blo 630300 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B4550813 : Blo 630300 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B946607 : Blo 630300 946607 := bstep (se 1 (by rfl) ⟨709955, by rfl⟩ : syracuseStep 946607 = 1419911) B1419911
theorem B1012151 : Blo 630300 1012151 := bstep (se 1 (by rfl) ⟨759113, by rfl⟩ : syracuseStep 1012151 = 1518227) B1518227
theorem B946697 : Blo 630300 946697 := bstep (se 2 (by rfl) ⟨355011, by rfl⟩ : syracuseStep 946697 = 710023) B710023
theorem B1667609 : Blo 630300 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B946727 : Blo 630300 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B7205435 : Blo 630300 7205435 := bstep (se 1 (by rfl) ⟨5404076, by rfl⟩ : syracuseStep 7205435 = 10808153) B10808153
theorem B946811 : Blo 630300 946811 := bstep (se 1 (by rfl) ⟨710108, by rfl⟩ : syracuseStep 946811 = 1420217) B1420217
theorem B946937 : Blo 630300 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B3044099 : Blo 630300 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B947039 : Blo 630300 947039 := bstep (se 1 (by rfl) ⟨710279, by rfl⟩ : syracuseStep 947039 = 1420559) B1420559
theorem B947051 : Blo 630300 947051 := bstep (se 1 (by rfl) ⟨710288, by rfl⟩ : syracuseStep 947051 = 1420577) B1420577
theorem B13661081 : Blo 630300 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B1438739 : Blo 630300 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B947279 : Blo 630300 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B947399 : Blo 630300 947399 := bstep (se 1 (by rfl) ⟨710549, by rfl⟩ : syracuseStep 947399 = 1421099) B1421099
theorem B4060439 : Blo 630300 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B947561 : Blo 630300 947561 := bstep (se 2 (by rfl) ⟨355335, by rfl⟩ : syracuseStep 947561 = 710671) B710671
theorem B947639 : Blo 630300 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B947675 : Blo 630300 947675 := bstep (se 1 (by rfl) ⟨710756, by rfl⟩ : syracuseStep 947675 = 1421513) B1421513
theorem B1603111 : Blo 630300 1603111 := bstep (se 1 (by rfl) ⟨1202333, by rfl⟩ : syracuseStep 1603111 = 2404667) B2404667
theorem B2127545 : Blo 630300 2127545 := bstep (se 2 (by rfl) ⟨797829, by rfl⟩ : syracuseStep 2127545 = 1595659) B1595659
theorem B1799891 : Blo 630300 1799891 := bstep (se 1 (by rfl) ⟨1349918, by rfl⟩ : syracuseStep 1799891 = 2699837) B2699837
theorem B3045215 : Blo 630300 3045215 := bstep (se 1 (by rfl) ⟨2283911, by rfl⟩ : syracuseStep 3045215 = 4567823) B4567823
theorem B1603435 : Blo 630300 1603435 := bstep (se 1 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 1603435 = 2405153) B2405153
theorem B948143 : Blo 630300 948143 := bstep (se 1 (by rfl) ⟨711107, by rfl⟩ : syracuseStep 948143 = 1422215) B1422215
theorem B4814801 : Blo 630300 4814801 := bstep (se 2 (by rfl) ⟨1805550, by rfl⟩ : syracuseStep 4814801 = 3611101) B3611101
theorem B948233 : Blo 630300 948233 := bstep (se 2 (by rfl) ⟨355587, by rfl⟩ : syracuseStep 948233 = 711175) B711175
theorem B948263 : Blo 630300 948263 := bstep (se 1 (by rfl) ⟨711197, by rfl⟩ : syracuseStep 948263 = 1422395) B1422395
theorem B948347 : Blo 630300 948347 := bstep (se 1 (by rfl) ⟨711260, by rfl⟩ : syracuseStep 948347 = 1422521) B1422521
theorem B9730205 : Blo 630300 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B948473 : Blo 630300 948473 := bstep (se 2 (by rfl) ⟨355677, by rfl⟩ : syracuseStep 948473 = 711355) B711355
theorem B4061441 : Blo 630300 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B2128139 : Blo 630300 2128139 := bstep (se 1 (by rfl) ⟨1596104, by rfl⟩ : syracuseStep 2128139 = 3192209) B3192209
theorem B948575 : Blo 630300 948575 := bstep (se 1 (by rfl) ⟨711431, by rfl⟩ : syracuseStep 948575 = 1422863) B1422863
theorem B948587 : Blo 630300 948587 := bstep (se 1 (by rfl) ⟨711440, by rfl⟩ : syracuseStep 948587 = 1422881) B1422881
theorem B3045869 : Blo 630300 3045869 := bstep (se 3 (by rfl) ⟨571100, by rfl⟩ : syracuseStep 3045869 = 1142201) B1142201
theorem B1604083 : Blo 630300 1604083 := bstep (se 1 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 1604083 = 2406125) B2406125
theorem B2128409 : Blo 630300 2128409 := bstep (se 2 (by rfl) ⟨798153, by rfl⟩ : syracuseStep 2128409 = 1596307) B1596307
theorem B948815 : Blo 630300 948815 := bstep (se 1 (by rfl) ⟨711611, by rfl⟩ : syracuseStep 948815 = 1423223) B1423223
theorem B34667185 : Blo 630300 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B2161337 : Blo 630300 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B1800893 : Blo 630300 1800893 := bstep (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) B675335
theorem B948935 : Blo 630300 948935 := bstep (se 1 (by rfl) ⟨711701, by rfl⟩ : syracuseStep 948935 = 1423403) B1423403
theorem B3046099 : Blo 630300 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B949097 : Blo 630300 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B949175 : Blo 630300 949175 := bstep (se 1 (by rfl) ⟨711881, by rfl⟩ : syracuseStep 949175 = 1423763) B1423763
theorem B949211 : Blo 630300 949211 := bstep (se 1 (by rfl) ⟨711908, by rfl⟩ : syracuseStep 949211 = 1423817) B1423817
theorem B1801223 : Blo 630300 1801223 := bstep (se 1 (by rfl) ⟨1350917, by rfl⟩ : syracuseStep 1801223 = 2701835) B2701835
theorem B9108773 : Blo 630300 9108773 := bstep (se 4 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 9108773 = 1707895) B1707895
theorem B949679 : Blo 630300 949679 := bstep (se 1 (by rfl) ⟨712259, by rfl⟩ : syracuseStep 949679 = 1424519) B1424519
theorem B949769 : Blo 630300 949769 := bstep (se 2 (by rfl) ⟨356163, by rfl⟩ : syracuseStep 949769 = 712327) B712327
theorem B949799 : Blo 630300 949799 := bstep (se 1 (by rfl) ⟨712349, by rfl⟩ : syracuseStep 949799 = 1424699) B1424699
theorem B1605217 : Blo 630300 1605217 := bstep (se 2 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 1605217 = 1203913) B1203913
theorem B949883 : Blo 630300 949883 := bstep (se 1 (by rfl) ⟨712412, by rfl⟩ : syracuseStep 949883 = 1424825) B1424825
theorem B2129543 : Blo 630300 2129543 := bstep (se 1 (by rfl) ⟨1597157, by rfl⟩ : syracuseStep 2129543 = 3194315) B3194315
theorem B2129597 : Blo 630300 2129597 := bstep (se 3 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 2129597 = 798599) B798599
theorem B950009 : Blo 630300 950009 := bstep (se 2 (by rfl) ⟨356253, by rfl⟩ : syracuseStep 950009 = 712507) B712507
theorem B3211001 : Blo 630300 3211001 := bstep (se 2 (by rfl) ⟨1204125, by rfl⟩ : syracuseStep 3211001 = 2408251) B2408251
theorem B2129759 : Blo 630300 2129759 := bstep (se 1 (by rfl) ⟨1597319, by rfl⟩ : syracuseStep 2129759 = 3194639) B3194639
theorem B950111 : Blo 630300 950111 := bstep (se 1 (by rfl) ⟨712583, by rfl⟩ : syracuseStep 950111 = 1425167) B1425167
theorem B950123 : Blo 630300 950123 := bstep (se 1 (by rfl) ⟨712592, by rfl⟩ : syracuseStep 950123 = 1425185) B1425185
theorem B3047483 : Blo 630300 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B10420325 : Blo 630300 10420325 := bstep (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) B1953811
theorem B950537 : Blo 630300 950537 := bstep (se 2 (by rfl) ⟨356451, by rfl⟩ : syracuseStep 950537 = 712903) B712903
theorem B950639 : Blo 630300 950639 := bstep (se 1 (by rfl) ⟨712979, by rfl⟩ : syracuseStep 950639 = 1425959) B1425959
theorem B1737071 : Blo 630300 1737071 := bstep (se 1 (by rfl) ⟨1302803, by rfl⟩ : syracuseStep 1737071 = 2605607) B2605607
theorem B852391 : Blo 630300 852391 := bstep (se 1 (by rfl) ⟨639293, by rfl⟩ : syracuseStep 852391 = 1278587) B1278587
theorem B950855 : Blo 630300 950855 := bstep (se 1 (by rfl) ⟨713141, by rfl⟩ : syracuseStep 950855 = 1426283) B1426283
theorem B950891 : Blo 630300 950891 := bstep (se 1 (by rfl) ⟨713168, by rfl⟩ : syracuseStep 950891 = 1426337) B1426337
theorem B951119 : Blo 630300 951119 := bstep (se 1 (by rfl) ⟨713339, by rfl⟩ : syracuseStep 951119 = 1426679) B1426679
theorem B2393185 : Blo 630300 2393185 := bstep (se 2 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 2393185 = 1794889) B1794889
theorem B5211479 : Blo 630300 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B853385 : Blo 630300 853385 := bstep (se 2 (by rfl) ⟨320019, by rfl⟩ : syracuseStep 853385 = 640039) B640039
theorem B1082873 : Blo 630300 1082873 := bstep (se 2 (by rfl) ⟨406077, by rfl⟩ : syracuseStep 1082873 = 812155) B812155
theorem B2393657 : Blo 630300 2393657 := bstep (se 2 (by rfl) ⟨897621, by rfl⟩ : syracuseStep 2393657 = 1795243) B1795243
theorem B20514455 : Blo 630300 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B2131919 : Blo 630300 2131919 := bstep (se 1 (by rfl) ⟨1598939, by rfl⟩ : syracuseStep 2131919 = 3197879) B3197879
theorem B2558081 : Blo 630300 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B1444321 : Blo 630300 1444321 := bstep (se 2 (by rfl) ⟨541620, by rfl⟩ : syracuseStep 1444321 = 1083241) B1083241
theorem B2132891 : Blo 630300 2132891 := bstep (se 1 (by rfl) ⟨1599668, by rfl⟩ : syracuseStep 2132891 = 3199337) B3199337
theorem B7670699 : Blo 630300 7670699 := bstep (se 1 (by rfl) ⟨5753024, by rfl⟩ : syracuseStep 7670699 = 11506049) B11506049
theorem B2166047 : Blo 630300 2166047 := bstep (se 1 (by rfl) ⟨1624535, by rfl⟩ : syracuseStep 2166047 = 3249071) B3249071
theorem B1805665 : Blo 630300 1805665 := bstep (se 2 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 1805665 = 1354249) B1354249
theorem B4787585 : Blo 630300 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B659167 : Blo 630300 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B855775 : Blo 630300 855775 := bstep (se 1 (by rfl) ⟨641831, by rfl⟩ : syracuseStep 855775 = 1283663) B1283663
theorem B2133917 : Blo 630300 2133917 := bstep (se 3 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 2133917 = 800219) B800219
theorem B2134025 : Blo 630300 2134025 := bstep (se 2 (by rfl) ⟨800259, by rfl⟩ : syracuseStep 2134025 = 1600519) B1600519
theorem B15405227 : Blo 630300 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B3412331 : Blo 630300 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B5640623 : Blo 630300 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B11834525 : Blo 630300 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B759151 : Blo 630300 759151 := bstep (se 1 (by rfl) ⟨569363, by rfl⟩ : syracuseStep 759151 = 1138727) B1138727
theorem B1348987 : Blo 630300 1348987 := bstep (se 1 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 1348987 = 2023481) B2023481
theorem B32773733 : Blo 630300 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B840636737 : Blo 630300 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B1350695 : Blo 630300 1350695 := bstep (se 1 (by rfl) ⟨1013021, by rfl⟩ : syracuseStep 1350695 = 2026043) B2026043
theorem B4922491 : Blo 630300 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B2137211 : Blo 630300 2137211 := bstep (se 1 (by rfl) ⟨1602908, by rfl⟩ : syracuseStep 2137211 = 3205817) B3205817
theorem B2137481 : Blo 630300 2137481 := bstep (se 2 (by rfl) ⟨801555, by rfl⟩ : syracuseStep 2137481 = 1603111) B1603111
theorem B630335 : Blo 630300 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B630343 : Blo 630300 630343 := bstep (se 1 (by rfl) ⟨472757, by rfl⟩ : syracuseStep 630343 = 945515) B945515
theorem B630495 : Blo 630300 630495 := bstep (se 1 (by rfl) ⟨472871, by rfl⟩ : syracuseStep 630495 = 945743) B945743
theorem B6856451 : Blo 630300 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B630575 : Blo 630300 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B2137913 : Blo 630300 2137913 := bstep (se 2 (by rfl) ⟨801717, by rfl⟩ : syracuseStep 2137913 = 1603435) B1603435
theorem B630683 : Blo 630300 630683 := bstep (se 1 (by rfl) ⟨473012, by rfl⟩ : syracuseStep 630683 = 946025) B946025
theorem B630735 : Blo 630300 630735 := bstep (se 1 (by rfl) ⟨473051, by rfl⟩ : syracuseStep 630735 = 946103) B946103
theorem B630759 : Blo 630300 630759 := bstep (se 1 (by rfl) ⟨473069, by rfl⟩ : syracuseStep 630759 = 946139) B946139
theorem B631071 : Blo 630300 631071 := bstep (se 1 (by rfl) ⟨473303, by rfl⟩ : syracuseStep 631071 = 946607) B946607
theorem B631131 : Blo 630300 631131 := bstep (se 1 (by rfl) ⟨473348, by rfl⟩ : syracuseStep 631131 = 946697) B946697
theorem B631151 : Blo 630300 631151 := bstep (se 1 (by rfl) ⟨473363, by rfl⟩ : syracuseStep 631151 = 946727) B946727
theorem B631207 : Blo 630300 631207 := bstep (se 1 (by rfl) ⟨473405, by rfl⟩ : syracuseStep 631207 = 946811) B946811
theorem B631291 : Blo 630300 631291 := bstep (se 1 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 631291 = 946937) B946937
theorem B631359 : Blo 630300 631359 := bstep (se 1 (by rfl) ⟨473519, by rfl⟩ : syracuseStep 631359 = 947039) B947039
theorem B2695751 : Blo 630300 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B631367 : Blo 630300 631367 := bstep (se 1 (by rfl) ⟨473525, by rfl⟩ : syracuseStep 631367 = 947051) B947051
theorem B2138777 : Blo 630300 2138777 := bstep (se 2 (by rfl) ⟨802041, by rfl⟩ : syracuseStep 2138777 = 1604083) B1604083
theorem B959159 : Blo 630300 959159 := bstep (se 1 (by rfl) ⟨719369, by rfl⟩ : syracuseStep 959159 = 1438739) B1438739
theorem B631519 : Blo 630300 631519 := bstep (se 1 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 631519 = 947279) B947279
theorem B631599 : Blo 630300 631599 := bstep (se 1 (by rfl) ⟨473699, by rfl⟩ : syracuseStep 631599 = 947399) B947399
theorem B631707 : Blo 630300 631707 := bstep (se 1 (by rfl) ⟨473780, by rfl⟩ : syracuseStep 631707 = 947561) B947561
theorem B631759 : Blo 630300 631759 := bstep (se 1 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 631759 = 947639) B947639
theorem B631783 : Blo 630300 631783 := bstep (se 1 (by rfl) ⟨473837, by rfl⟩ : syracuseStep 631783 = 947675) B947675
theorem B1516583 : Blo 630300 1516583 := bstep (se 1 (by rfl) ⟨1137437, by rfl⟩ : syracuseStep 1516583 = 2274875) B2274875
theorem B1418363 : Blo 630300 1418363 := bstep (se 1 (by rfl) ⟨1063772, by rfl⟩ : syracuseStep 1418363 = 2127545) B2127545
theorem B2696435 : Blo 630300 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B1418489 : Blo 630300 1418489 := bstep (se 2 (by rfl) ⟨531933, by rfl⟩ : syracuseStep 1418489 = 1063867) B1063867
theorem B632095 : Blo 630300 632095 := bstep (se 1 (by rfl) ⟨474071, by rfl⟩ : syracuseStep 632095 = 948143) B948143
theorem B632155 : Blo 630300 632155 := bstep (se 1 (by rfl) ⟨474116, by rfl⟩ : syracuseStep 632155 = 948233) B948233
theorem B632175 : Blo 630300 632175 := bstep (se 1 (by rfl) ⟨474131, by rfl⟩ : syracuseStep 632175 = 948263) B948263
theorem B1418633 : Blo 630300 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B632231 : Blo 630300 632231 := bstep (se 1 (by rfl) ⟨474173, by rfl⟩ : syracuseStep 632231 = 948347) B948347
theorem B1713595 : Blo 630300 1713595 := bstep (se 1 (by rfl) ⟨1285196, by rfl⟩ : syracuseStep 1713595 = 2570393) B2570393
theorem B632315 : Blo 630300 632315 := bstep (se 1 (by rfl) ⟨474236, by rfl⟩ : syracuseStep 632315 = 948473) B948473
theorem B1418759 : Blo 630300 1418759 := bstep (se 1 (by rfl) ⟨1064069, by rfl⟩ : syracuseStep 1418759 = 2128139) B2128139
theorem B632383 : Blo 630300 632383 := bstep (se 1 (by rfl) ⟨474287, by rfl⟩ : syracuseStep 632383 = 948575) B948575
theorem B632391 : Blo 630300 632391 := bstep (se 1 (by rfl) ⟨474293, by rfl⟩ : syracuseStep 632391 = 948587) B948587
theorem B1418939 : Blo 630300 1418939 := bstep (se 1 (by rfl) ⟨1064204, by rfl⟩ : syracuseStep 1418939 = 2128409) B2128409
theorem B632543 : Blo 630300 632543 := bstep (se 1 (by rfl) ⟨474407, by rfl⟩ : syracuseStep 632543 = 948815) B948815
theorem B632623 : Blo 630300 632623 := bstep (se 1 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 632623 = 948935) B948935
theorem B1419065 : Blo 630300 1419065 := bstep (se 2 (by rfl) ⟨532149, by rfl⟩ : syracuseStep 1419065 = 1064299) B1064299
theorem B632731 : Blo 630300 632731 := bstep (se 1 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 632731 = 949097) B949097
theorem B632783 : Blo 630300 632783 := bstep (se 1 (by rfl) ⟨474587, by rfl⟩ : syracuseStep 632783 = 949175) B949175
theorem B632807 : Blo 630300 632807 := bstep (se 1 (by rfl) ⟨474605, by rfl⟩ : syracuseStep 632807 = 949211) B949211
theorem B2926573 : Blo 630300 2926573 := bstep (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) B1097465
theorem B2140289 : Blo 630300 2140289 := bstep (se 2 (by rfl) ⟨802608, by rfl⟩ : syracuseStep 2140289 = 1605217) B1605217
theorem B6072515 : Blo 630300 6072515 := bstep (se 1 (by rfl) ⟨4554386, by rfl⟩ : syracuseStep 6072515 = 9108773) B9108773
theorem B633119 : Blo 630300 633119 := bstep (se 1 (by rfl) ⟨474839, by rfl⟩ : syracuseStep 633119 = 949679) B949679
theorem B633179 : Blo 630300 633179 := bstep (se 1 (by rfl) ⟨474884, by rfl⟩ : syracuseStep 633179 = 949769) B949769
theorem B633199 : Blo 630300 633199 := bstep (se 1 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 633199 = 949799) B949799
theorem B633255 : Blo 630300 633255 := bstep (se 1 (by rfl) ⟨474941, by rfl⟩ : syracuseStep 633255 = 949883) B949883
theorem B1419695 : Blo 630300 1419695 := bstep (se 1 (by rfl) ⟨1064771, by rfl⟩ : syracuseStep 1419695 = 2129543) B2129543
theorem B1419731 : Blo 630300 1419731 := bstep (se 1 (by rfl) ⟨1064798, by rfl⟩ : syracuseStep 1419731 = 2129597) B2129597
theorem B633339 : Blo 630300 633339 := bstep (se 1 (by rfl) ⟨475004, by rfl⟩ : syracuseStep 633339 = 950009) B950009
theorem B2140667 : Blo 630300 2140667 := bstep (se 1 (by rfl) ⟨1605500, by rfl⟩ : syracuseStep 2140667 = 3211001) B3211001
theorem B1419839 : Blo 630300 1419839 := bstep (se 1 (by rfl) ⟨1064879, by rfl⟩ : syracuseStep 1419839 = 2129759) B2129759
theorem B633407 : Blo 630300 633407 := bstep (se 1 (by rfl) ⟨475055, by rfl⟩ : syracuseStep 633407 = 950111) B950111
theorem B633415 : Blo 630300 633415 := bstep (se 1 (by rfl) ⟨475061, by rfl⟩ : syracuseStep 633415 = 950123) B950123
theorem B1419947 : Blo 630300 1419947 := bstep (se 1 (by rfl) ⟨1064960, by rfl⟩ : syracuseStep 1419947 = 2129921) B2129921
theorem B633567 : Blo 630300 633567 := bstep (se 1 (by rfl) ⟨475175, by rfl⟩ : syracuseStep 633567 = 950351) B950351
theorem B2566903 : Blo 630300 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B633647 : Blo 630300 633647 := bstep (se 1 (by rfl) ⟨475235, by rfl⟩ : syracuseStep 633647 = 950471) B950471
theorem B21900145 : Blo 630300 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B633755 : Blo 630300 633755 := bstep (se 1 (by rfl) ⟨475316, by rfl⟩ : syracuseStep 633755 = 950633) B950633
theorem B633807 : Blo 630300 633807 := bstep (se 1 (by rfl) ⟨475355, by rfl⟩ : syracuseStep 633807 = 950711) B950711
theorem B633831 : Blo 630300 633831 := bstep (se 1 (by rfl) ⟨475373, by rfl⟩ : syracuseStep 633831 = 950747) B950747
theorem B1420487 : Blo 630300 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B1518841 : Blo 630300 1518841 := bstep (se 2 (by rfl) ⟨569565, by rfl⟩ : syracuseStep 1518841 = 1139131) B1139131
theorem B5385487 : Blo 630300 5385487 := bstep (se 1 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 5385487 = 8078231) B8078231
theorem B634143 : Blo 630300 634143 := bstep (se 1 (by rfl) ⟨475607, by rfl⟩ : syracuseStep 634143 = 951215) B951215
theorem B634203 : Blo 630300 634203 := bstep (se 1 (by rfl) ⟨475652, by rfl⟩ : syracuseStep 634203 = 951305) B951305
theorem B634223 : Blo 630300 634223 := bstep (se 1 (by rfl) ⟨475667, by rfl⟩ : syracuseStep 634223 = 951335) B951335
theorem B1420667 : Blo 630300 1420667 := bstep (se 1 (by rfl) ⟨1065500, by rfl⟩ : syracuseStep 1420667 = 2131001) B2131001
theorem B634279 : Blo 630300 634279 := bstep (se 1 (by rfl) ⟨475709, by rfl⟩ : syracuseStep 634279 = 951419) B951419
theorem B4795847 : Blo 630300 4795847 := bstep (se 1 (by rfl) ⟨3596885, by rfl⟩ : syracuseStep 4795847 = 7193771) B7193771
theorem B1420793 : Blo 630300 1420793 := bstep (se 2 (by rfl) ⟨532797, by rfl⟩ : syracuseStep 1420793 = 1065595) B1065595
theorem B1420883 : Blo 630300 1420883 := bstep (se 1 (by rfl) ⟨1065662, by rfl⟩ : syracuseStep 1420883 = 2131325) B2131325
theorem B1421063 : Blo 630300 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B1421675 : Blo 630300 1421675 := bstep (se 1 (by rfl) ⟨1066256, by rfl⟩ : syracuseStep 1421675 = 2132513) B2132513
theorem B1421819 : Blo 630300 1421819 := bstep (se 1 (by rfl) ⟨1066364, by rfl⟩ : syracuseStep 1421819 = 2132729) B2132729
theorem B799303 : Blo 630300 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B1421945 : Blo 630300 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1421999 : Blo 630300 1421999 := bstep (se 1 (by rfl) ⟨1066499, by rfl⟩ : syracuseStep 1421999 = 2132999) B2132999
theorem B1422071 : Blo 630300 1422071 := bstep (se 1 (by rfl) ⟨1066553, by rfl⟩ : syracuseStep 1422071 = 2133107) B2133107
theorem B1422251 : Blo 630300 1422251 := bstep (se 1 (by rfl) ⟨1066688, by rfl⟩ : syracuseStep 1422251 = 2133377) B2133377
theorem B2405321 : Blo 630300 2405321 := bstep (se 2 (by rfl) ⟨901995, by rfl⟩ : syracuseStep 2405321 = 1803991) B1803991
theorem B21083261 : Blo 630300 21083261 := bstep (se 3 (by rfl) ⟨3953111, by rfl⟩ : syracuseStep 21083261 = 7906223) B7906223
theorem B2405609 : Blo 630300 2405609 := bstep (se 2 (by rfl) ⟨902103, by rfl⟩ : syracuseStep 2405609 = 1804207) B1804207
theorem B4797791 : Blo 630300 4797791 := bstep (se 1 (by rfl) ⟨3598343, by rfl⟩ : syracuseStep 4797791 = 7196687) B7196687
theorem B2405821 : Blo 630300 2405821 := bstep (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) B902183
theorem B1422791 : Blo 630300 1422791 := bstep (se 1 (by rfl) ⟨1067093, by rfl⟩ : syracuseStep 1422791 = 2134187) B2134187
theorem B1423151 : Blo 630300 1423151 := bstep (se 1 (by rfl) ⟨1067363, by rfl⟩ : syracuseStep 1423151 = 2134727) B2134727
theorem B1423727 : Blo 630300 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B801191 : Blo 630300 801191 := bstep (se 1 (by rfl) ⟨600893, by rfl⟩ : syracuseStep 801191 = 1201787) B1201787
theorem B1423799 : Blo 630300 1423799 := bstep (se 1 (by rfl) ⟨1067849, by rfl⟩ : syracuseStep 1423799 = 2135699) B2135699
theorem B3029491 : Blo 630300 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B801343 : Blo 630300 801343 := bstep (se 1 (by rfl) ⟨601007, by rfl⟩ : syracuseStep 801343 = 1202015) B1202015
theorem B1423943 : Blo 630300 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B1423979 : Blo 630300 1423979 := bstep (se 1 (by rfl) ⟨1067984, by rfl⟩ : syracuseStep 1423979 = 2135969) B2135969
theorem B801515 : Blo 630300 801515 := bstep (se 1 (by rfl) ⟨601136, by rfl⟩ : syracuseStep 801515 = 1202273) B1202273
theorem B3193667 : Blo 630300 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B1063759 : Blo 630300 1063759 := bstep (se 1 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 1063759 = 1595639) B1595639
theorem B1424375 : Blo 630300 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B1424735 : Blo 630300 1424735 := bstep (se 1 (by rfl) ⟨1068551, by rfl⟩ : syracuseStep 1424735 = 2137103) B2137103
theorem B1064441 : Blo 630300 1064441 := bstep (se 2 (by rfl) ⟨399165, by rfl⟩ : syracuseStep 1064441 = 798331) B798331
theorem B4046395 : Blo 630300 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B3194477 : Blo 630300 3194477 := bstep (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) B1197929
theorem B4570739 : Blo 630300 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B802487 : Blo 630300 802487 := bstep (se 1 (by rfl) ⟨601865, by rfl⟩ : syracuseStep 802487 = 1203731) B1203731
theorem B8634071 : Blo 630300 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B1425131 : Blo 630300 1425131 := bstep (se 1 (by rfl) ⟨1068848, by rfl⟩ : syracuseStep 1425131 = 2137697) B2137697
theorem B1064711 : Blo 630300 1064711 := bstep (se 1 (by rfl) ⟨798533, by rfl⟩ : syracuseStep 1064711 = 1597067) B1597067
theorem B900919 : Blo 630300 900919 := bstep (se 1 (by rfl) ⟨675689, by rfl⟩ : syracuseStep 900919 = 1351379) B1351379
theorem B802639 : Blo 630300 802639 := bstep (se 1 (by rfl) ⟨601979, by rfl⟩ : syracuseStep 802639 = 1203959) B1203959
theorem B1425257 : Blo 630300 1425257 := bstep (se 2 (by rfl) ⟨534471, by rfl⟩ : syracuseStep 1425257 = 1068943) B1068943
theorem B6144457 : Blo 630300 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B1065467 : Blo 630300 1065467 := bstep (se 1 (by rfl) ⟨799100, by rfl⟩ : syracuseStep 1065467 = 1598201) B1598201
theorem B3424787 : Blo 630300 3424787 := bstep (se 1 (by rfl) ⟨2568590, by rfl⟩ : syracuseStep 3424787 = 5137181) B5137181
theorem B901739 : Blo 630300 901739 := bstep (se 1 (by rfl) ⟨676304, by rfl⟩ : syracuseStep 901739 = 1352609) B1352609
theorem B13681325 : Blo 630300 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B1426103 : Blo 630300 1426103 := bstep (se 1 (by rfl) ⟨1069577, by rfl⟩ : syracuseStep 1426103 = 2139155) B2139155
theorem B1426319 : Blo 630300 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B1065899 : Blo 630300 1065899 := bstep (se 1 (by rfl) ⟨799424, by rfl⟩ : syracuseStep 1065899 = 1598849) B1598849
theorem B3425219 : Blo 630300 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B3425287 : Blo 630300 3425287 := bstep (se 1 (by rfl) ⟨2568965, by rfl⟩ : syracuseStep 3425287 = 5137931) B5137931
theorem B4801679 : Blo 630300 4801679 := bstep (se 1 (by rfl) ⟨3601259, by rfl⟩ : syracuseStep 4801679 = 7202519) B7202519
theorem B902377 : Blo 630300 902377 := bstep (se 2 (by rfl) ⟨338391, by rfl⟩ : syracuseStep 902377 = 676783) B676783
theorem B8111447 : Blo 630300 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B1066439 : Blo 630300 1066439 := bstep (se 1 (by rfl) ⟨799829, by rfl⟩ : syracuseStep 1066439 = 1599659) B1599659
theorem B1427039 : Blo 630300 1427039 := bstep (se 1 (by rfl) ⟨1070279, by rfl⟩ : syracuseStep 1427039 = 2140559) B2140559
theorem B3032761 : Blo 630300 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B3033335 : Blo 630300 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B1067431 : Blo 630300 1067431 := bstep (se 1 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 1067431 = 1601147) B1601147
theorem B6506963 : Blo 630300 6506963 := bstep (se 1 (by rfl) ⟨4880222, by rfl⟩ : syracuseStep 6506963 = 9760445) B9760445
theorem B105335261 : Blo 630300 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B1067593 : Blo 630300 1067593 := bstep (se 2 (by rfl) ⟨400347, by rfl⟩ : syracuseStep 1067593 = 800695) B800695
theorem B1067627 : Blo 630300 1067627 := bstep (se 1 (by rfl) ⟨800720, by rfl⟩ : syracuseStep 1067627 = 1601441) B1601441
theorem B3033875 : Blo 630300 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B5557015 : Blo 630300 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B3853079 : Blo 630300 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B674767 : Blo 630300 674767 := bstep (se 1 (by rfl) ⟨506075, by rfl⟩ : syracuseStep 674767 = 1012151) B1012151
theorem B4049959 : Blo 630300 4049959 := bstep (se 1 (by rfl) ⟨3037469, by rfl⟩ : syracuseStep 4049959 = 6074939) B6074939
theorem B4803623 : Blo 630300 4803623 := bstep (se 1 (by rfl) ⟨3602717, by rfl⟩ : syracuseStep 4803623 = 7205435) B7205435
theorem B2706959 : Blo 630300 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B46222913 : Blo 630300 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B11685509 : Blo 630300 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B1199927 : Blo 630300 1199927 := bstep (se 1 (by rfl) ⟨899945, by rfl⟩ : syracuseStep 1199927 = 1799891) B1799891
theorem B3035009 : Blo 630300 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B2707627 : Blo 630300 2707627 := bstep (se 1 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 2707627 = 4061441) B4061441
theorem B2642129 : Blo 630300 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B1069321 : Blo 630300 1069321 := bstep (se 2 (by rfl) ⟨400995, by rfl⟩ : syracuseStep 1069321 = 801991) B801991
theorem B1200595 : Blo 630300 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B1200815 : Blo 630300 1200815 := bstep (se 1 (by rfl) ⟨900611, by rfl⟩ : syracuseStep 1200815 = 1801223) B1801223
theorem B3199823 : Blo 630300 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B3200147 : Blo 630300 3200147 := bstep (se 1 (by rfl) ⟨2400110, by rfl⟩ : syracuseStep 3200147 = 4800221) B4800221
theorem B1201385 : Blo 630300 1201385 := bstep (se 2 (by rfl) ⟨450519, by rfl⟩ : syracuseStep 1201385 = 901039) B901039
theorem B7198145 : Blo 630300 7198145 := bstep (se 2 (by rfl) ⟨2699304, by rfl⟩ : syracuseStep 7198145 = 5398609) B5398609
theorem B710239 : Blo 630300 710239 := bstep (se 1 (by rfl) ⟨532679, by rfl⟩ : syracuseStep 710239 = 1065359) B1065359
theorem B2021021 : Blo 630300 2021021 := bstep (se 3 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 2021021 = 757883) B757883
theorem B1234619 : Blo 630300 1234619 := bstep (se 1 (by rfl) ⟨925964, by rfl⟩ : syracuseStep 1234619 = 1851929) B1851929
theorem B1595497 : Blo 630300 1595497 := bstep (se 2 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 1595497 = 1196623) B1196623
theorem B1366121 : Blo 630300 1366121 := bstep (se 2 (by rfl) ⟨512295, by rfl⟩ : syracuseStep 1366121 = 1024591) B1024591
theorem B1202683 : Blo 630300 1202683 := bstep (se 1 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 1202683 = 1804025) B1804025
theorem B1202759 : Blo 630300 1202759 := bstep (se 1 (by rfl) ⟨902069, by rfl⟩ : syracuseStep 1202759 = 1804139) B1804139
theorem B1595983 : Blo 630300 1595983 := bstep (se 1 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 1595983 = 2393975) B2393975
theorem B6576815 : Blo 630300 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B711391 : Blo 630300 711391 := bstep (se 1 (by rfl) ⟨533543, by rfl⟩ : syracuseStep 711391 = 1067087) B1067087
theorem B5757803 : Blo 630300 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B1268651 : Blo 630300 1268651 := bstep (se 1 (by rfl) ⟨951488, by rfl⟩ : syracuseStep 1268651 = 1902977) B1902977
theorem B1596631 : Blo 630300 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B711967 : Blo 630300 711967 := bstep (se 1 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 711967 = 1067951) B1067951
theorem B8117597 : Blo 630300 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B1203655 : Blo 630300 1203655 := bstep (se 1 (by rfl) ⟨902741, by rfl⟩ : syracuseStep 1203655 = 1805483) B1805483
theorem B1596935 : Blo 630300 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B712255 : Blo 630300 712255 := bstep (se 1 (by rfl) ⟨534191, by rfl⟩ : syracuseStep 712255 = 1068383) B1068383
theorem B1597391 : Blo 630300 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B6086663 : Blo 630300 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B1925129 : Blo 630300 1925129 := bstep (se 2 (by rfl) ⟨721923, by rfl⟩ : syracuseStep 1925129 = 1443847) B1443847
theorem B3596339 : Blo 630300 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B3203225 : Blo 630300 3203225 := bstep (se 2 (by rfl) ⟨1201209, by rfl⟩ : syracuseStep 3203225 = 2402419) B2402419
theorem B713083 : Blo 630300 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B4546979 : Blo 630300 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B10936777 : Blo 630300 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B1597907 : Blo 630300 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B713551 : Blo 630300 713551 := bstep (se 1 (by rfl) ⟨535163, by rfl⟩ : syracuseStep 713551 = 1070327) B1070327
theorem B9266015 : Blo 630300 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B1598363 : Blo 630300 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B12346273 : Blo 630300 12346273 := bstep (se 2 (by rfl) ⟨4629852, by rfl⟩ : syracuseStep 12346273 = 9259705) B9259705
theorem B3204035 : Blo 630300 3204035 := bstep (se 1 (by rfl) ⟨2403026, by rfl⟩ : syracuseStep 3204035 = 4806053) B4806053
theorem B2876563 : Blo 630300 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B3237079 : Blo 630300 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B8119601 : Blo 630300 8119601 := bstep (se 2 (by rfl) ⟨3044850, by rfl⟩ : syracuseStep 8119601 = 6089701) B6089701
theorem B4547927 : Blo 630300 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B1795517 : Blo 630300 1795517 := bstep (se 3 (by rfl) ⟨336659, by rfl⟩ : syracuseStep 1795517 = 673319) B673319
theorem B1599497 : Blo 630300 1599497 := bstep (se 2 (by rfl) ⟨599811, by rfl⟩ : syracuseStep 1599497 = 1199623) B1199623
theorem B2025607 : Blo 630300 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B8120573 : Blo 630300 8120573 := bstep (se 3 (by rfl) ⟨1522607, by rfl⟩ : syracuseStep 8120573 = 3045215) B3045215
theorem B13297955 : Blo 630300 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B1599851 : Blo 630300 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B1010087 : Blo 630300 1010087 := bstep (se 1 (by rfl) ⟨757565, by rfl⟩ : syracuseStep 1010087 = 1515131) B1515131
theorem B1796519 : Blo 630300 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B1600175 : Blo 630300 1600175 := bstep (se 1 (by rfl) ⟨1200131, by rfl⟩ : syracuseStep 1600175 = 2400263) B2400263
theorem B568519397 : Blo 630300 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B1600499 : Blo 630300 1600499 := bstep (se 1 (by rfl) ⟨1200374, by rfl⟩ : syracuseStep 1600499 = 2400749) B2400749
theorem B945545 : Blo 630300 945545 := bstep (se 2 (by rfl) ⟨354579, by rfl⟩ : syracuseStep 945545 = 709159) B709159
theorem B2026889 : Blo 630300 2026889 := bstep (se 2 (by rfl) ⟨760083, by rfl⟩ : syracuseStep 2026889 = 1520167) B1520167
theorem B1600955 : Blo 630300 1600955 := bstep (se 1 (by rfl) ⟨1200716, by rfl⟩ : syracuseStep 1600955 = 2401433) B2401433
theorem B2026939 : Blo 630300 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B945899 : Blo 630300 945899 := bstep (se 1 (by rfl) ⟨709424, by rfl⟩ : syracuseStep 945899 = 1418849) B1418849
theorem B946127 : Blo 630300 946127 := bstep (se 1 (by rfl) ⟨709595, by rfl⟩ : syracuseStep 946127 = 1419191) B1419191
theorem B3502081 : Blo 630300 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B12120353 : Blo 630300 12120353 := bstep (se 2 (by rfl) ⟨4545132, by rfl⟩ : syracuseStep 12120353 = 9090265) B9090265
theorem B3600713 : Blo 630300 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B946523 : Blo 630300 946523 := bstep (se 1 (by rfl) ⟨709892, by rfl⟩ : syracuseStep 946523 = 1419785) B1419785
theorem B3207599 : Blo 630300 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B1798625 : Blo 630300 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B5763565 : Blo 630300 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B946751 : Blo 630300 946751 := bstep (se 1 (by rfl) ⟨710063, by rfl⟩ : syracuseStep 946751 = 1420127) B1420127
theorem B1602119 : Blo 630300 1602119 := bstep (se 1 (by rfl) ⟨1201589, by rfl⟩ : syracuseStep 1602119 = 2403179) B2403179
theorem B5403257 : Blo 630300 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B946871 : Blo 630300 946871 := bstep (se 1 (by rfl) ⟨710153, by rfl⟩ : syracuseStep 946871 = 1420307) B1420307
theorem B947099 : Blo 630300 947099 := bstep (se 1 (by rfl) ⟨710324, by rfl⟩ : syracuseStep 947099 = 1420649) B1420649
theorem B3077065 : Blo 630300 3077065 := bstep (se 2 (by rfl) ⟨1153899, by rfl⟩ : syracuseStep 3077065 = 2307799) B2307799
theorem B947495 : Blo 630300 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B947579 : Blo 630300 947579 := bstep (se 1 (by rfl) ⟨710684, by rfl⟩ : syracuseStep 947579 = 1421369) B1421369
theorem B3208571 : Blo 630300 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B4552139 : Blo 630300 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B8779229 : Blo 630300 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B947705 : Blo 630300 947705 := bstep (se 2 (by rfl) ⟨355389, by rfl⟩ : syracuseStep 947705 = 710779) B710779
theorem B947807 : Blo 630300 947807 := bstep (se 1 (by rfl) ⟨710855, by rfl⟩ : syracuseStep 947807 = 1421711) B1421711
theorem B1111739 : Blo 630300 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B948023 : Blo 630300 948023 := bstep (se 1 (by rfl) ⟨711017, by rfl⟩ : syracuseStep 948023 = 1422035) B1422035
theorem B1603385 : Blo 630300 1603385 := bstep (se 2 (by rfl) ⟨601269, by rfl⟩ : syracuseStep 1603385 = 1202539) B1202539
theorem B9107387 : Blo 630300 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B948329 : Blo 630300 948329 := bstep (se 2 (by rfl) ⟨355623, by rfl⟩ : syracuseStep 948329 = 711247) B711247
theorem B4061465 : Blo 630300 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B948647 : Blo 630300 948647 := bstep (se 1 (by rfl) ⟨711485, by rfl⟩ : syracuseStep 948647 = 1422971) B1422971
theorem B4815287 : Blo 630300 4815287 := bstep (se 1 (by rfl) ⟨3611465, by rfl⟩ : syracuseStep 4815287 = 7222931) B7222931
theorem B948731 : Blo 630300 948731 := bstep (se 1 (by rfl) ⟨711548, by rfl⟩ : syracuseStep 948731 = 1423097) B1423097
theorem B1800767 : Blo 630300 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B2128463 : Blo 630300 2128463 := bstep (se 1 (by rfl) ⟨1596347, by rfl⟩ : syracuseStep 2128463 = 3192695) B3192695
theorem B948857 : Blo 630300 948857 := bstep (se 2 (by rfl) ⟨355821, by rfl⟩ : syracuseStep 948857 = 711643) B711643
theorem B3209867 : Blo 630300 3209867 := bstep (se 1 (by rfl) ⟨2407400, by rfl⟩ : syracuseStep 3209867 = 4814801) B4814801
theorem B948911 : Blo 630300 948911 := bstep (se 1 (by rfl) ⟨711683, by rfl⟩ : syracuseStep 948911 = 1423367) B1423367
theorem B948959 : Blo 630300 948959 := bstep (se 1 (by rfl) ⟨711719, by rfl⟩ : syracuseStep 948959 = 1423439) B1423439
theorem B6486803 : Blo 630300 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B949223 : Blo 630300 949223 := bstep (se 1 (by rfl) ⟨711917, by rfl⟩ : syracuseStep 949223 = 1423835) B1423835
theorem B2030579 : Blo 630300 2030579 := bstep (se 1 (by rfl) ⟨1522934, by rfl⟩ : syracuseStep 2030579 = 3045869) B3045869
theorem B1604731 : Blo 630300 1604731 := bstep (se 1 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 1604731 = 2407097) B2407097
theorem B1080463 : Blo 630300 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B949481 : Blo 630300 949481 := bstep (se 2 (by rfl) ⟨356055, by rfl⟩ : syracuseStep 949481 = 712111) B712111
theorem B949535 : Blo 630300 949535 := bstep (se 1 (by rfl) ⟨712151, by rfl⟩ : syracuseStep 949535 = 1424303) B1424303
theorem B949703 : Blo 630300 949703 := bstep (se 1 (by rfl) ⟨712277, by rfl⟩ : syracuseStep 949703 = 1424555) B1424555
theorem B2129705 : Blo 630300 2129705 := bstep (se 2 (by rfl) ⟨798639, by rfl⟩ : syracuseStep 2129705 = 1597279) B1597279
theorem B950057 : Blo 630300 950057 := bstep (se 2 (by rfl) ⟨356271, by rfl⟩ : syracuseStep 950057 = 712543) B712543
theorem B950063 : Blo 630300 950063 := bstep (se 1 (by rfl) ⟨712547, by rfl⟩ : syracuseStep 950063 = 1425095) B1425095
theorem B18677765 : Blo 630300 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B2031655 : Blo 630300 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B6946883 : Blo 630300 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B950735 : Blo 630300 950735 := bstep (se 1 (by rfl) ⟨713051, by rfl⟩ : syracuseStep 950735 = 1426103) B1426103
theorem B950777 : Blo 630300 950777 := bstep (se 2 (by rfl) ⟨356541, by rfl⟩ : syracuseStep 950777 = 713083) B713083
theorem B950879 : Blo 630300 950879 := bstep (se 1 (by rfl) ⟨713159, by rfl⟩ : syracuseStep 950879 = 1426319) B1426319
theorem B8192609 : Blo 630300 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B14582369 : Blo 630300 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B5407631 : Blo 630300 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B721915 : Blo 630300 721915 := bstep (se 1 (by rfl) ⟨541436, by rfl⟩ : syracuseStep 721915 = 1082873) B1082873
theorem B951359 : Blo 630300 951359 := bstep (se 1 (by rfl) ⟨713519, by rfl⟩ : syracuseStep 951359 = 1427039) B1427039
theorem B951401 : Blo 630300 951401 := bstep (se 2 (by rfl) ⟨356775, by rfl⟩ : syracuseStep 951401 = 713551) B713551
theorem B1705387 : Blo 630300 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B70223507 : Blo 630300 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B2557757 : Blo 630300 2557757 := bstep (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) B959159
theorem B5113799 : Blo 630300 5113799 := bstep (se 1 (by rfl) ⟨3835349, by rfl⟩ : syracuseStep 5113799 = 7670699) B7670699
theorem B1444031 : Blo 630300 1444031 := bstep (se 1 (by rfl) ⟨1083023, by rfl⟩ : syracuseStep 1444031 = 2166047) B2166047
theorem B24709373 : Blo 630300 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B2133215 : Blo 630300 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B2133431 : Blo 630300 2133431 := bstep (se 1 (by rfl) ⟨1600073, by rfl⟩ : syracuseStep 2133431 = 3200147) B3200147
theorem B12127805 : Blo 630300 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B13897277 : Blo 630300 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B1347347 : Blo 630300 1347347 := bstep (se 1 (by rfl) ⟨1010510, by rfl⟩ : syracuseStep 1347347 = 2021021) B2021021
theorem B823079 : Blo 630300 823079 := bstep (se 1 (by rfl) ⟨617309, by rfl⟩ : syracuseStep 823079 = 1234619) B1234619
theorem B29200193 : Blo 630300 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B7180649 : Blo 630300 7180649 := bstep (se 2 (by rfl) ⟨2692743, by rfl⟩ : syracuseStep 7180649 = 5385487) B5385487
theorem B3838535 : Blo 630300 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B5411731 : Blo 630300 5411731 := bstep (se 1 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 5411731 = 8117597) B8117597
theorem B1283419 : Blo 630300 1283419 := bstep (se 1 (by rfl) ⟨962564, by rfl⟩ : syracuseStep 1283419 = 1925129) B1925129
theorem B2397559 : Blo 630300 2397559 := bstep (se 1 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 2397559 = 3596339) B3596339
theorem B2135483 : Blo 630300 2135483 := bstep (se 1 (by rfl) ⟨1601612, by rfl⟩ : syracuseStep 2135483 = 3203225) B3203225
theorem B3610169 : Blo 630300 3610169 := bstep (se 2 (by rfl) ⟨1353813, by rfl⟩ : syracuseStep 3610169 = 2707627) B2707627
theorem B2136023 : Blo 630300 2136023 := bstep (se 1 (by rfl) ⟨1602017, by rfl⟩ : syracuseStep 2136023 = 3204035) B3204035
theorem B15341669 : Blo 630300 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B5413067 : Blo 630300 5413067 := bstep (se 1 (by rfl) ⟨4059800, by rfl⟩ : syracuseStep 5413067 = 8119601) B8119601
theorem B2136509 : Blo 630300 2136509 := bstep (se 3 (by rfl) ⟨400595, by rfl⟩ : syracuseStep 2136509 = 801191) B801191
theorem B4102753 : Blo 630300 4102753 := bstep (se 2 (by rfl) ⟨1538532, by rfl⟩ : syracuseStep 4102753 = 3077065) B3077065
theorem B5413715 : Blo 630300 5413715 := bstep (se 1 (by rfl) ⟨4060286, by rfl⟩ : syracuseStep 5413715 = 8120573) B8120573
theorem B2137373 : Blo 630300 2137373 := bstep (se 3 (by rfl) ⟨400757, by rfl⟩ : syracuseStep 2137373 = 801515) B801515
theorem B630363 : Blo 630300 630363 := bstep (se 1 (by rfl) ⟨472772, by rfl⟩ : syracuseStep 630363 = 945545) B945545
theorem B1351259 : Blo 630300 1351259 := bstep (se 1 (by rfl) ⟨1013444, by rfl⟩ : syracuseStep 1351259 = 2026889) B2026889
theorem B630599 : Blo 630300 630599 := bstep (se 1 (by rfl) ⟨472949, by rfl⟩ : syracuseStep 630599 = 945899) B945899
theorem B630751 : Blo 630300 630751 := bstep (se 1 (by rfl) ⟨473063, by rfl⟩ : syracuseStep 630751 = 946127) B946127
theorem B2400475 : Blo 630300 2400475 := bstep (se 1 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 2400475 = 3600713) B3600713
theorem B631015 : Blo 630300 631015 := bstep (se 1 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 631015 = 946523) B946523
theorem B2138399 : Blo 630300 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B631167 : Blo 630300 631167 := bstep (se 1 (by rfl) ⟨473375, by rfl⟩ : syracuseStep 631167 = 946751) B946751
theorem B631247 : Blo 630300 631247 := bstep (se 1 (by rfl) ⟨473435, by rfl⟩ : syracuseStep 631247 = 946871) B946871
theorem B631399 : Blo 630300 631399 := bstep (se 1 (by rfl) ⟨473549, by rfl⟩ : syracuseStep 631399 = 947099) B947099
theorem B4039321 : Blo 630300 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B631663 : Blo 630300 631663 := bstep (se 1 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 631663 = 947495) B947495
theorem B631719 : Blo 630300 631719 := bstep (se 1 (by rfl) ⟨473789, by rfl⟩ : syracuseStep 631719 = 947579) B947579
theorem B2139047 : Blo 630300 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B631803 : Blo 630300 631803 := bstep (se 1 (by rfl) ⟨473852, by rfl⟩ : syracuseStep 631803 = 947705) B947705
theorem B631871 : Blo 630300 631871 := bstep (se 1 (by rfl) ⟨473903, by rfl⟩ : syracuseStep 631871 = 947807) B947807
theorem B1418345 : Blo 630300 1418345 := bstep (se 2 (by rfl) ⟨531879, by rfl⟩ : syracuseStep 1418345 = 1063759) B1063759
theorem B3515557 : Blo 630300 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B4564133 : Blo 630300 4564133 := bstep (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) B855775
theorem B632015 : Blo 630300 632015 := bstep (se 1 (by rfl) ⟨474011, by rfl⟩ : syracuseStep 632015 = 948023) B948023
theorem B6071591 : Blo 630300 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B7218557 : Blo 630300 7218557 := bstep (se 3 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 7218557 = 2706959) B2706959
theorem B632219 : Blo 630300 632219 := bstep (se 1 (by rfl) ⟨474164, by rfl⟩ : syracuseStep 632219 = 948329) B948329
theorem B6563321 : Blo 630300 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B2139641 : Blo 630300 2139641 := bstep (se 2 (by rfl) ⟨802365, by rfl⟩ : syracuseStep 2139641 = 1604731) B1604731
theorem B632431 : Blo 630300 632431 := bstep (se 1 (by rfl) ⟨474323, by rfl⟩ : syracuseStep 632431 = 948647) B948647
theorem B632487 : Blo 630300 632487 := bstep (se 1 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 632487 = 948731) B948731
theorem B1418975 : Blo 630300 1418975 := bstep (se 1 (by rfl) ⟨1064231, by rfl⟩ : syracuseStep 1418975 = 2128463) B2128463
theorem B632571 : Blo 630300 632571 := bstep (se 1 (by rfl) ⟨474428, by rfl⟩ : syracuseStep 632571 = 948857) B948857
theorem B2139911 : Blo 630300 2139911 := bstep (se 1 (by rfl) ⟨1604933, by rfl⟩ : syracuseStep 2139911 = 3209867) B3209867
theorem B632607 : Blo 630300 632607 := bstep (se 1 (by rfl) ⟨474455, by rfl⟩ : syracuseStep 632607 = 948911) B948911
theorem B2139965 : Blo 630300 2139965 := bstep (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) B802487
theorem B632639 : Blo 630300 632639 := bstep (se 1 (by rfl) ⟨474479, by rfl⟩ : syracuseStep 632639 = 948959) B948959
theorem B632815 : Blo 630300 632815 := bstep (se 1 (by rfl) ⟨474611, by rfl⟩ : syracuseStep 632815 = 949223) B949223
theorem B1353719 : Blo 630300 1353719 := bstep (se 1 (by rfl) ⟨1015289, by rfl⟩ : syracuseStep 1353719 = 2030579) B2030579
theorem B632987 : Blo 630300 632987 := bstep (se 1 (by rfl) ⟨474740, by rfl⟩ : syracuseStep 632987 = 949481) B949481
theorem B633023 : Blo 630300 633023 := bstep (se 1 (by rfl) ⟨474767, by rfl⟩ : syracuseStep 633023 = 949535) B949535
theorem B633135 : Blo 630300 633135 := bstep (se 1 (by rfl) ⟨474851, by rfl⟩ : syracuseStep 633135 = 949703) B949703
theorem B1419803 : Blo 630300 1419803 := bstep (se 1 (by rfl) ⟨1064852, by rfl⟩ : syracuseStep 1419803 = 2129705) B2129705
theorem B633371 : Blo 630300 633371 := bstep (se 1 (by rfl) ⟨475028, by rfl⟩ : syracuseStep 633371 = 950057) B950057
theorem B633375 : Blo 630300 633375 := bstep (se 1 (by rfl) ⟨475031, by rfl⟩ : syracuseStep 633375 = 950063) B950063
theorem B15608389 : Blo 630300 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B633691 : Blo 630300 633691 := bstep (se 1 (by rfl) ⟨475268, by rfl⟩ : syracuseStep 633691 = 950537) B950537
theorem B633759 : Blo 630300 633759 := bstep (se 1 (by rfl) ⟨475319, by rfl⟩ : syracuseStep 633759 = 950639) B950639
theorem B1158047 : Blo 630300 1158047 := bstep (se 1 (by rfl) ⟨868535, by rfl⟩ : syracuseStep 1158047 = 1737071) B1737071
theorem B633903 : Blo 630300 633903 := bstep (se 1 (by rfl) ⟨475427, by rfl⟩ : syracuseStep 633903 = 950855) B950855
theorem B633927 : Blo 630300 633927 := bstep (se 1 (by rfl) ⟨475445, by rfl⟩ : syracuseStep 633927 = 950891) B950891
theorem B9120883 : Blo 630300 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B634079 : Blo 630300 634079 := bstep (se 1 (by rfl) ⟨475559, by rfl⟩ : syracuseStep 634079 = 951119) B951119
theorem B13676303 : Blo 630300 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B4796333 : Blo 630300 4796333 := bstep (se 3 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 4796333 = 1798625) B1798625
theorem B1421279 : Blo 630300 1421279 := bstep (se 1 (by rfl) ⟨1065959, by rfl⟩ : syracuseStep 1421279 = 2131919) B2131919
theorem B4567049 : Blo 630300 4567049 := bstep (se 2 (by rfl) ⟨1712643, by rfl⟩ : syracuseStep 4567049 = 3425287) B3425287
theorem B3190913 : Blo 630300 3190913 := bstep (se 2 (by rfl) ⟨1196592, by rfl⟩ : syracuseStep 3190913 = 2393185) B2393185
theorem B2404637 : Blo 630300 2404637 := bstep (se 3 (by rfl) ⟨450869, by rfl⟩ : syracuseStep 2404637 = 901739) B901739
theorem B4337975 : Blo 630300 4337975 := bstep (se 1 (by rfl) ⟨3253481, by rfl⟩ : syracuseStep 4337975 = 6506963) B6506963
theorem B2568719 : Blo 630300 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B1421927 : Blo 630300 1421927 := bstep (se 1 (by rfl) ⟨1066445, by rfl⟩ : syracuseStep 1421927 = 2132891) B2132891
theorem B4043681 : Blo 630300 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B3191723 : Blo 630300 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B30815275 : Blo 630300 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B799951 : Blo 630300 799951 := bstep (se 1 (by rfl) ⟨599963, by rfl⟩ : syracuseStep 799951 = 1199927) B1199927
theorem B1422611 : Blo 630300 1422611 := bstep (se 1 (by rfl) ⟨1066958, by rfl⟩ : syracuseStep 1422611 = 2133917) B2133917
theorem B1422683 : Blo 630300 1422683 := bstep (se 1 (by rfl) ⟨1067012, by rfl⟩ : syracuseStep 1422683 = 2134025) B2134025
theorem B10270151 : Blo 630300 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B2700809 : Blo 630300 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B2274887 : Blo 630300 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B800543 : Blo 630300 800543 := bstep (se 1 (by rfl) ⟨600407, by rfl⟩ : syracuseStep 800543 = 1200815) B1200815
theorem B1423241 : Blo 630300 1423241 := bstep (se 2 (by rfl) ⟨533715, by rfl⟩ : syracuseStep 1423241 = 1067431) B1067431
theorem B1423457 : Blo 630300 1423457 := bstep (se 2 (by rfl) ⟨533796, by rfl⟩ : syracuseStep 1423457 = 1067593) B1067593
theorem B800923 : Blo 630300 800923 := bstep (se 1 (by rfl) ⟨600692, by rfl⟩ : syracuseStep 800923 = 1201385) B1201385
theorem B4798763 : Blo 630300 4798763 := bstep (se 1 (by rfl) ⟨3599072, by rfl⟩ : syracuseStep 4798763 = 7198145) B7198145
theorem B3422537 : Blo 630300 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B899689 : Blo 630300 899689 := bstep (se 2 (by rfl) ⟨337383, by rfl⟩ : syracuseStep 899689 = 674767) B674767
theorem B29637413 : Blo 630300 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B801839 : Blo 630300 801839 := bstep (se 1 (by rfl) ⟨601379, by rfl⟩ : syracuseStep 801839 = 1202759) B1202759
theorem B2407553 : Blo 630300 2407553 := bstep (se 2 (by rfl) ⟨902832, by rfl⟩ : syracuseStep 2407553 = 1805665) B1805665
theorem B2964637 : Blo 630300 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B2702585 : Blo 630300 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B1424807 : Blo 630300 1424807 := bstep (se 1 (by rfl) ⟨1068605, by rfl⟩ : syracuseStep 1424807 = 2137211) B2137211
theorem B65846789 : Blo 630300 65846789 := bstep (se 4 (by rfl) ⟨6173136, by rfl⟩ : syracuseStep 65846789 = 12346273) B12346273
theorem B1424987 : Blo 630300 1424987 := bstep (se 1 (by rfl) ⟨1068740, by rfl⟩ : syracuseStep 1424987 = 2137481) B2137481
theorem B1064623 : Blo 630300 1064623 := bstep (se 1 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 1064623 = 1596935) B1596935
theorem B4570967 : Blo 630300 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B1425275 : Blo 630300 1425275 := bstep (se 1 (by rfl) ⟨1068956, by rfl⟩ : syracuseStep 1425275 = 2137913) B2137913
theorem B1064927 : Blo 630300 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B3031319 : Blo 630300 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B1065271 : Blo 630300 1065271 := bstep (se 1 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 1065271 = 1597907) B1597907
theorem B1425761 : Blo 630300 1425761 := bstep (se 2 (by rfl) ⟨534660, by rfl⟩ : syracuseStep 1425761 = 1069321) B1069321
theorem B1425851 : Blo 630300 1425851 := bstep (se 1 (by rfl) ⟨1069388, by rfl⟩ : syracuseStep 1425851 = 2138777) B2138777
theorem B1065575 : Blo 630300 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B7684753 : Blo 630300 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B1065737 : Blo 630300 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B1197011 : Blo 630300 1197011 := bstep (se 1 (by rfl) ⟨897758, by rfl⟩ : syracuseStep 1197011 = 1795517) B1795517
theorem B1066331 : Blo 630300 1066331 := bstep (se 1 (by rfl) ⟨799748, by rfl⟩ : syracuseStep 1066331 = 1599497) B1599497
theorem B1426859 : Blo 630300 1426859 := bstep (se 1 (by rfl) ⟨1070144, by rfl⟩ : syracuseStep 1426859 = 2140289) B2140289
theorem B4048343 : Blo 630300 4048343 := bstep (se 1 (by rfl) ⟨3036257, by rfl⟩ : syracuseStep 4048343 = 6072515) B6072515
theorem B1066567 : Blo 630300 1066567 := bstep (se 1 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 1066567 = 1599851) B1599851
theorem B673391 : Blo 630300 673391 := bstep (se 1 (by rfl) ⟨505043, by rfl⟩ : syracuseStep 673391 = 1010087) B1010087
theorem B1197679 : Blo 630300 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B1427111 : Blo 630300 1427111 := bstep (se 1 (by rfl) ⟨1070333, by rfl⟩ : syracuseStep 1427111 = 2140667) B2140667
theorem B1066783 : Blo 630300 1066783 := bstep (se 1 (by rfl) ⟨800087, by rfl⟩ : syracuseStep 1066783 = 1600175) B1600175
theorem B379012931 : Blo 630300 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B4048805 : Blo 630300 4048805 := bstep (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) B759151
theorem B1066999 : Blo 630300 1066999 := bstep (se 1 (by rfl) ⟨800249, by rfl⟩ : syracuseStep 1066999 = 1600499) B1600499
theorem B1067303 : Blo 630300 1067303 := bstep (se 1 (by rfl) ⟨800477, by rfl⟩ : syracuseStep 1067303 = 1600955) B1600955
theorem B3197231 : Blo 630300 3197231 := bstep (se 1 (by rfl) ⟨2397923, by rfl⟩ : syracuseStep 3197231 = 4795847) B4795847
theorem B8080235 : Blo 630300 8080235 := bstep (se 1 (by rfl) ⟨6060176, by rfl⟩ : syracuseStep 8080235 = 12120353) B12120353
theorem B1068079 : Blo 630300 1068079 := bstep (se 1 (by rfl) ⟨801059, by rfl⟩ : syracuseStep 1068079 = 1602119) B1602119
theorem B1068457 : Blo 630300 1068457 := bstep (se 2 (by rfl) ⟨400671, by rfl⟩ : syracuseStep 1068457 = 801343) B801343
theorem B3198527 : Blo 630300 3198527 := bstep (se 1 (by rfl) ⟨2398895, by rfl⟩ : syracuseStep 3198527 = 4797791) B4797791
theorem B3034759 : Blo 630300 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B5852819 : Blo 630300 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B1068923 : Blo 630300 1068923 := bstep (se 1 (by rfl) ⟨801692, by rfl⟩ : syracuseStep 1068923 = 1603385) B1603385
theorem B2707643 : Blo 630300 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B1200511 : Blo 630300 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B23024189 : Blo 630300 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B5395193 : Blo 630300 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B709627 : Blo 630300 709627 := bstep (se 1 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 709627 = 1064441) B1064441
theorem B1201225 : Blo 630300 1201225 := bstep (se 2 (by rfl) ⟨450459, by rfl⟩ : syracuseStep 1201225 = 900919) B900919
theorem B1070185 : Blo 630300 1070185 := bstep (se 2 (by rfl) ⟨401319, by rfl⟩ : syracuseStep 1070185 = 802639) B802639
theorem B709807 : Blo 630300 709807 := bstep (se 1 (by rfl) ⟨532355, by rfl⟩ : syracuseStep 709807 = 1064711) B1064711
theorem B710311 : Blo 630300 710311 := bstep (se 1 (by rfl) ⟨532733, by rfl⟩ : syracuseStep 710311 = 1065467) B1065467
theorem B2283191 : Blo 630300 2283191 := bstep (se 1 (by rfl) ⟨1712393, by rfl⟩ : syracuseStep 2283191 = 3424787) B3424787
theorem B1136521 : Blo 630300 1136521 := bstep (se 2 (by rfl) ⟨426195, by rfl⟩ : syracuseStep 1136521 = 852391) B852391
theorem B710599 : Blo 630300 710599 := bstep (se 1 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 710599 = 1065899) B1065899
theorem B2283479 : Blo 630300 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B3201119 : Blo 630300 3201119 := bstep (se 1 (by rfl) ⟨2400839, by rfl⟩ : syracuseStep 3201119 = 4801679) B4801679
theorem B710959 : Blo 630300 710959 := bstep (se 1 (by rfl) ⟨533219, by rfl⟩ : syracuseStep 710959 = 1066439) B1066439
theorem B1595771 : Blo 630300 1595771 := bstep (se 1 (by rfl) ⟨1196828, by rfl⟩ : syracuseStep 1595771 = 2393657) B2393657
theorem B4316105 : Blo 630300 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B1203169 : Blo 630300 1203169 := bstep (se 2 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 1203169 = 902377) B902377
theorem B711751 : Blo 630300 711751 := bstep (se 1 (by rfl) ⟨533813, by rfl⟩ : syracuseStep 711751 = 1067627) B1067627
theorem B2022583 : Blo 630300 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B2284793 : Blo 630300 2284793 := bstep (se 2 (by rfl) ⟨856797, by rfl⟩ : syracuseStep 2284793 = 1713595) B1713595
theorem B3202415 : Blo 630300 3202415 := bstep (se 1 (by rfl) ⟨2401811, by rfl⟩ : syracuseStep 3202415 = 4803623) B4803623
theorem B7790339 : Blo 630300 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B1761419 : Blo 630300 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B3760415 : Blo 630300 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B56222029 : Blo 630300 56222029 := bstep (se 3 (by rfl) ⟨10541630, by rfl⟩ : syracuseStep 56222029 = 21083261) B21083261
theorem B141844853 : Blo 630300 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B1925761 : Blo 630300 1925761 := bstep (se 2 (by rfl) ⟨722160, by rfl⟩ : syracuseStep 1925761 = 1444321) B1444321
theorem B7889683 : Blo 630300 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B21849155 : Blo 630300 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B5399945 : Blo 630300 5399945 := bstep (se 2 (by rfl) ⟨2024979, by rfl⟩ : syracuseStep 5399945 = 4049959) B4049959
theorem B910747 : Blo 630300 910747 := bstep (se 1 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 910747 = 1366121) B1366121
theorem B9102773 : Blo 630300 9102773 := bstep (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) B853385
theorem B560424491 : Blo 630300 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B2025121 : Blo 630300 2025121 := bstep (se 2 (by rfl) ⟨759420, by rfl⟩ : syracuseStep 2025121 = 1518841) B1518841
theorem B4384543 : Blo 630300 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B845767 : Blo 630300 845767 := bstep (se 1 (by rfl) ⟨634325, by rfl⟩ : syracuseStep 845767 = 1268651) B1268651
theorem B4057775 : Blo 630300 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B1797167 : Blo 630300 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B1600793 : Blo 630300 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B8088893 : Blo 630300 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B1011055 : Blo 630300 1011055 := bstep (se 1 (by rfl) ⟨758291, by rfl⟩ : syracuseStep 1011055 = 1516583) B1516583
theorem B945575 : Blo 630300 945575 := bstep (se 1 (by rfl) ⟨709181, by rfl⟩ : syracuseStep 945575 = 1418363) B1418363
theorem B1797623 : Blo 630300 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B945659 : Blo 630300 945659 := bstep (se 1 (by rfl) ⟨709244, by rfl⟩ : syracuseStep 945659 = 1418489) B1418489
theorem B945755 : Blo 630300 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B945839 : Blo 630300 945839 := bstep (se 1 (by rfl) ⟨709379, by rfl⟩ : syracuseStep 945839 = 1418759) B1418759
theorem B945959 : Blo 630300 945959 := bstep (se 1 (by rfl) ⟨709469, by rfl⟩ : syracuseStep 945959 = 1418939) B1418939
theorem B946043 : Blo 630300 946043 := bstep (se 1 (by rfl) ⟨709532, by rfl⟩ : syracuseStep 946043 = 1419065) B1419065
theorem B946463 : Blo 630300 946463 := bstep (se 1 (by rfl) ⟨709847, by rfl⟩ : syracuseStep 946463 = 1419695) B1419695
theorem B946487 : Blo 630300 946487 := bstep (se 1 (by rfl) ⟨709865, by rfl⟩ : syracuseStep 946487 = 1419731) B1419731
theorem B946559 : Blo 630300 946559 := bstep (se 1 (by rfl) ⟨709919, by rfl⟩ : syracuseStep 946559 = 1419839) B1419839
theorem B946631 : Blo 630300 946631 := bstep (se 1 (by rfl) ⟨709973, by rfl⟩ : syracuseStep 946631 = 1419947) B1419947
theorem B1798649 : Blo 630300 1798649 := bstep (se 2 (by rfl) ⟨674493, by rfl⟩ : syracuseStep 1798649 = 1348987) B1348987
theorem B3207761 : Blo 630300 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B946985 : Blo 630300 946985 := bstep (se 2 (by rfl) ⟨355119, by rfl⟩ : syracuseStep 946985 = 710239) B710239
theorem B946991 : Blo 630300 946991 := bstep (se 1 (by rfl) ⟨710243, by rfl⟩ : syracuseStep 946991 = 1420487) B1420487
theorem B947111 : Blo 630300 947111 := bstep (se 1 (by rfl) ⟨710333, by rfl⟩ : syracuseStep 947111 = 1420667) B1420667
theorem B947195 : Blo 630300 947195 := bstep (se 1 (by rfl) ⟨710396, by rfl⟩ : syracuseStep 947195 = 1420793) B1420793
theorem B947255 : Blo 630300 947255 := bstep (se 1 (by rfl) ⟨710441, by rfl⟩ : syracuseStep 947255 = 1420883) B1420883
theorem B947375 : Blo 630300 947375 := bstep (se 1 (by rfl) ⟨710531, by rfl⟩ : syracuseStep 947375 = 1421063) B1421063
theorem B3601853 : Blo 630300 3601853 := bstep (se 3 (by rfl) ⟨675347, by rfl⟩ : syracuseStep 3601853 = 1350695) B1350695
theorem B2127329 : Blo 630300 2127329 := bstep (se 2 (by rfl) ⟨797748, by rfl⟩ : syracuseStep 2127329 = 1595497) B1595497
theorem B947783 : Blo 630300 947783 := bstep (se 1 (by rfl) ⟨710837, by rfl⟩ : syracuseStep 947783 = 1421675) B1421675
theorem B947879 : Blo 630300 947879 := bstep (se 1 (by rfl) ⟨710909, by rfl⟩ : syracuseStep 947879 = 1421819) B1421819
theorem B947963 : Blo 630300 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B3602171 : Blo 630300 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B947999 : Blo 630300 947999 := bstep (se 1 (by rfl) ⟨710999, by rfl⟩ : syracuseStep 947999 = 1421999) B1421999
theorem B948047 : Blo 630300 948047 := bstep (se 1 (by rfl) ⟨711035, by rfl⟩ : syracuseStep 948047 = 1422071) B1422071
theorem B948167 : Blo 630300 948167 := bstep (se 1 (by rfl) ⟨711125, by rfl⟩ : syracuseStep 948167 = 1422251) B1422251
theorem B1603547 : Blo 630300 1603547 := bstep (se 1 (by rfl) ⟨1202660, by rfl⟩ : syracuseStep 1603547 = 2405321) B2405321
theorem B1603577 : Blo 630300 1603577 := bstep (se 2 (by rfl) ⟨601341, by rfl⟩ : syracuseStep 1603577 = 1202683) B1202683
theorem B2127977 : Blo 630300 2127977 := bstep (se 2 (by rfl) ⟨797991, by rfl⟩ : syracuseStep 2127977 = 1595983) B1595983
theorem B1603739 : Blo 630300 1603739 := bstep (se 1 (by rfl) ⟨1202804, by rfl⟩ : syracuseStep 1603739 = 2405609) B2405609
theorem B948521 : Blo 630300 948521 := bstep (se 2 (by rfl) ⟨355695, by rfl⟩ : syracuseStep 948521 = 711391) B711391
theorem B948527 : Blo 630300 948527 := bstep (se 1 (by rfl) ⟨711395, by rfl⟩ : syracuseStep 948527 = 1422791) B1422791
theorem B948767 : Blo 630300 948767 := bstep (se 1 (by rfl) ⟨711575, by rfl⟩ : syracuseStep 948767 = 1423151) B1423151
theorem B1440617 : Blo 630300 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B949151 : Blo 630300 949151 := bstep (se 1 (by rfl) ⟨711863, by rfl⟩ : syracuseStep 949151 = 1423727) B1423727
theorem B2128841 : Blo 630300 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B949199 : Blo 630300 949199 := bstep (se 1 (by rfl) ⟨711899, by rfl⟩ : syracuseStep 949199 = 1423799) B1423799
theorem B3210191 : Blo 630300 3210191 := bstep (se 1 (by rfl) ⟨2407643, by rfl⟩ : syracuseStep 3210191 = 4815287) B4815287
theorem B949289 : Blo 630300 949289 := bstep (se 2 (by rfl) ⟨355983, by rfl⟩ : syracuseStep 949289 = 711967) B711967
theorem B949295 : Blo 630300 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B949319 : Blo 630300 949319 := bstep (se 1 (by rfl) ⟨711989, by rfl⟩ : syracuseStep 949319 = 1423979) B1423979
theorem B4324535 : Blo 630300 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B2129111 : Blo 630300 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B1604873 : Blo 630300 1604873 := bstep (se 2 (by rfl) ⟨601827, by rfl⟩ : syracuseStep 1604873 = 1203655) B1203655
theorem B949583 : Blo 630300 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B949673 : Blo 630300 949673 := bstep (se 2 (by rfl) ⟨356127, by rfl⟩ : syracuseStep 949673 = 712255) B712255
theorem B949823 : Blo 630300 949823 := bstep (se 1 (by rfl) ⟨712367, by rfl⟩ : syracuseStep 949823 = 1424735) B1424735
theorem B8093357 : Blo 630300 8093357 := bstep (se 3 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 8093357 = 3035009) B3035009
theorem B2129651 : Blo 630300 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B3047159 : Blo 630300 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B950087 : Blo 630300 950087 := bstep (se 1 (by rfl) ⟨712565, by rfl⟩ : syracuseStep 950087 = 1425131) B1425131
theorem B950171 : Blo 630300 950171 := bstep (se 1 (by rfl) ⟨712628, by rfl⟩ : syracuseStep 950171 = 1425257) B1425257
theorem B12451843 : Blo 630300 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B950507 : Blo 630300 950507 := bstep (se 1 (by rfl) ⟨712880, by rfl⟩ : syracuseStep 950507 = 1425761) B1425761
theorem B950567 : Blo 630300 950567 := bstep (se 1 (by rfl) ⟨712925, by rfl⟩ : syracuseStep 950567 = 1425851) B1425851
theorem B3605087 : Blo 630300 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B11567933 : Blo 630300 11567933 := bstep (se 3 (by rfl) ⟨2168987, by rfl⟩ : syracuseStep 11567933 = 4337975) B4337975
theorem B951239 : Blo 630300 951239 := bstep (se 1 (by rfl) ⟨713429, by rfl⟩ : syracuseStep 951239 = 1426859) B1426859
theorem B10519577 : Blo 630300 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B951407 : Blo 630300 951407 := bstep (se 1 (by rfl) ⟨713555, by rfl⟩ : syracuseStep 951407 = 1427111) B1427111
theorem B252675287 : Blo 630300 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B3409199 : Blo 630300 3409199 := bstep (se 1 (by rfl) ⟨2556899, by rfl⟩ : syracuseStep 3409199 = 5113799) B5113799
theorem B6849917 : Blo 630300 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B2131487 : Blo 630300 2131487 := bstep (se 1 (by rfl) ⟨1598615, by rfl⟩ : syracuseStep 2131487 = 3197231) B3197231
theorem B4687409 : Blo 630300 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B2132351 : Blo 630300 2132351 := bstep (se 1 (by rfl) ⟨1599263, by rfl⟩ : syracuseStep 2132351 = 3198527) B3198527
theorem B3901879 : Blo 630300 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B19466795 : Blo 630300 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B1805095 : Blo 630300 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B4787099 : Blo 630300 4787099 := bstep (se 1 (by rfl) ⟨3590324, by rfl⟩ : syracuseStep 4787099 = 7180649) B7180649
theorem B2559023 : Blo 630300 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B20811185 : Blo 630300 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B2134079 : Blo 630300 2134079 := bstep (se 1 (by rfl) ⟨1600559, by rfl⟩ : syracuseStep 2134079 = 3201119) B3201119
theorem B10227779 : Blo 630300 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B3608711 : Blo 630300 3608711 := bstep (se 1 (by rfl) ⟨2706533, by rfl⟩ : syracuseStep 3608711 = 5413067) B5413067
theorem B12161177 : Blo 630300 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B1348073 : Blo 630300 1348073 := bstep (se 2 (by rfl) ⟨505527, by rfl⟩ : syracuseStep 1348073 = 1011055) B1011055
theorem B3609143 : Blo 630300 3609143 := bstep (se 1 (by rfl) ⟨2706857, by rfl⟩ : syracuseStep 3609143 = 5413715) B5413715
theorem B2134781 : Blo 630300 2134781 := bstep (se 3 (by rfl) ⟨400271, by rfl⟩ : syracuseStep 2134781 = 800543) B800543
theorem B6820685 : Blo 630300 6820685 := bstep (se 3 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 6820685 = 2557757) B2557757
theorem B2134943 : Blo 630300 2134943 := bstep (se 1 (by rfl) ⟨1601207, by rfl⟩ : syracuseStep 2134943 = 3202415) B3202415
theorem B3609917 : Blo 630300 3609917 := bstep (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) B1353719
theorem B6068515 : Blo 630300 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B7215641 : Blo 630300 7215641 := bstep (se 2 (by rfl) ⟨2705865, by rfl⟩ : syracuseStep 7215641 = 5411731) B5411731
theorem B1711225 : Blo 630300 1711225 := bstep (se 2 (by rfl) ⟨641709, by rfl⟩ : syracuseStep 1711225 = 1283419) B1283419
theorem B4857317 : Blo 630300 4857317 := bstep (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) B910747
theorem B630383 : Blo 630300 630383 := bstep (se 1 (by rfl) ⟨472787, by rfl⟩ : syracuseStep 630383 = 945575) B945575
theorem B630439 : Blo 630300 630439 := bstep (se 1 (by rfl) ⟨472829, by rfl⟩ : syracuseStep 630439 = 945659) B945659
theorem B630503 : Blo 630300 630503 := bstep (se 1 (by rfl) ⟨472877, by rfl⟩ : syracuseStep 630503 = 945755) B945755
theorem B630559 : Blo 630300 630559 := bstep (se 1 (by rfl) ⟨472919, by rfl⟩ : syracuseStep 630559 = 945839) B945839
theorem B9117535 : Blo 630300 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B1515361 : Blo 630300 1515361 := bstep (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) B1136521
theorem B11509613 : Blo 630300 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B630639 : Blo 630300 630639 := bstep (se 1 (by rfl) ⟨472979, by rfl⟩ : syracuseStep 630639 = 945959) B945959
theorem B630695 : Blo 630300 630695 := bstep (se 1 (by rfl) ⟨473021, by rfl⟩ : syracuseStep 630695 = 946043) B946043
theorem B4792445 : Blo 630300 4792445 := bstep (se 3 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 4792445 = 1797167) B1797167
theorem B2138237 : Blo 630300 2138237 := bstep (se 3 (by rfl) ⟨400919, by rfl⟩ : syracuseStep 2138237 = 801839) B801839
theorem B630975 : Blo 630300 630975 := bstep (se 1 (by rfl) ⟨473231, by rfl⟩ : syracuseStep 630975 = 946463) B946463
theorem B630991 : Blo 630300 630991 := bstep (se 1 (by rfl) ⟨473243, by rfl⟩ : syracuseStep 630991 = 946487) B946487
theorem B631039 : Blo 630300 631039 := bstep (se 1 (by rfl) ⟨473279, by rfl⟩ : syracuseStep 631039 = 946559) B946559
theorem B631087 : Blo 630300 631087 := bstep (se 1 (by rfl) ⟨473315, by rfl⟩ : syracuseStep 631087 = 946631) B946631
theorem B2138507 : Blo 630300 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B631323 : Blo 630300 631323 := bstep (se 1 (by rfl) ⟨473492, by rfl⟩ : syracuseStep 631323 = 946985) B946985
theorem B631327 : Blo 630300 631327 := bstep (se 1 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 631327 = 946991) B946991
theorem B2695787 : Blo 630300 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B631407 : Blo 630300 631407 := bstep (se 1 (by rfl) ⟨473555, by rfl⟩ : syracuseStep 631407 = 947111) B947111
theorem B631463 : Blo 630300 631463 := bstep (se 1 (by rfl) ⟨473597, by rfl⟩ : syracuseStep 631463 = 947195) B947195
theorem B631503 : Blo 630300 631503 := bstep (se 1 (by rfl) ⟨473627, by rfl⟩ : syracuseStep 631503 = 947255) B947255
theorem B631583 : Blo 630300 631583 := bstep (se 1 (by rfl) ⟨473687, by rfl⟩ : syracuseStep 631583 = 947375) B947375
theorem B2401235 : Blo 630300 2401235 := bstep (se 1 (by rfl) ⟨1800926, by rfl⟩ : syracuseStep 2401235 = 3601853) B3601853
theorem B1418219 : Blo 630300 1418219 := bstep (se 1 (by rfl) ⟨1063664, by rfl⟩ : syracuseStep 1418219 = 2127329) B2127329
theorem B1516591 : Blo 630300 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B631855 : Blo 630300 631855 := bstep (se 1 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 631855 = 947783) B947783
theorem B631919 : Blo 630300 631919 := bstep (se 1 (by rfl) ⟨473939, by rfl⟩ : syracuseStep 631919 = 947879) B947879
theorem B631975 : Blo 630300 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B2401447 : Blo 630300 2401447 := bstep (se 1 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 2401447 = 3602171) B3602171
theorem B631999 : Blo 630300 631999 := bstep (se 1 (by rfl) ⟨473999, by rfl⟩ : syracuseStep 631999 = 947999) B947999
theorem B632031 : Blo 630300 632031 := bstep (se 1 (by rfl) ⟨474023, by rfl⟩ : syracuseStep 632031 = 948047) B948047
theorem B632111 : Blo 630300 632111 := bstep (se 1 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 632111 = 948167) B948167
theorem B1418651 : Blo 630300 1418651 := bstep (se 1 (by rfl) ⟨1063988, by rfl⟩ : syracuseStep 1418651 = 2127977) B2127977
theorem B632347 : Blo 630300 632347 := bstep (se 1 (by rfl) ⟨474260, by rfl⟩ : syracuseStep 632347 = 948521) B948521
theorem B632351 : Blo 630300 632351 := bstep (se 1 (by rfl) ⟨474263, by rfl⟩ : syracuseStep 632351 = 948527) B948527
theorem B2696777 : Blo 630300 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B632511 : Blo 630300 632511 := bstep (se 1 (by rfl) ⟨474383, by rfl⟩ : syracuseStep 632511 = 948767) B948767
theorem B632767 : Blo 630300 632767 := bstep (se 1 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 632767 = 949151) B949151
theorem B1419227 : Blo 630300 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B632799 : Blo 630300 632799 := bstep (se 1 (by rfl) ⟨474599, by rfl⟩ : syracuseStep 632799 = 949199) B949199
theorem B2140127 : Blo 630300 2140127 := bstep (se 1 (by rfl) ⟨1605095, by rfl⟩ : syracuseStep 2140127 = 3210191) B3210191
theorem B632859 : Blo 630300 632859 := bstep (se 1 (by rfl) ⟨474644, by rfl⟩ : syracuseStep 632859 = 949289) B949289
theorem B632863 : Blo 630300 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B632879 : Blo 630300 632879 := bstep (se 1 (by rfl) ⟨474659, by rfl⟩ : syracuseStep 632879 = 949319) B949319
theorem B1419407 : Blo 630300 1419407 := bstep (se 1 (by rfl) ⟨1064555, by rfl⟩ : syracuseStep 1419407 = 2129111) B2129111
theorem B633055 : Blo 630300 633055 := bstep (se 1 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 633055 = 949583) B949583
theorem B1419497 : Blo 630300 1419497 := bstep (se 2 (by rfl) ⟨532311, by rfl⟩ : syracuseStep 1419497 = 1064623) B1064623
theorem B633115 : Blo 630300 633115 := bstep (se 1 (by rfl) ⟨474836, by rfl⟩ : syracuseStep 633115 = 949673) B949673
theorem B633215 : Blo 630300 633215 := bstep (se 1 (by rfl) ⟨474911, by rfl⟩ : syracuseStep 633215 = 949823) B949823
theorem B1419767 : Blo 630300 1419767 := bstep (se 1 (by rfl) ⟨1064825, by rfl⟩ : syracuseStep 1419767 = 2129651) B2129651
theorem B633391 : Blo 630300 633391 := bstep (se 1 (by rfl) ⟨475043, by rfl⟩ : syracuseStep 633391 = 950087) B950087
theorem B633447 : Blo 630300 633447 := bstep (se 1 (by rfl) ⟨475085, by rfl⟩ : syracuseStep 633447 = 950171) B950171
theorem B4631255 : Blo 630300 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B633823 : Blo 630300 633823 := bstep (se 1 (by rfl) ⟨475367, by rfl⟩ : syracuseStep 633823 = 950735) B950735
theorem B633851 : Blo 630300 633851 := bstep (se 1 (by rfl) ⟨475388, by rfl⟩ : syracuseStep 633851 = 950777) B950777
theorem B633919 : Blo 630300 633919 := bstep (se 1 (by rfl) ⟨475439, by rfl⟩ : syracuseStep 633919 = 950879) B950879
theorem B1420361 : Blo 630300 1420361 := bstep (se 2 (by rfl) ⟨532635, by rfl⟩ : syracuseStep 1420361 = 1065271) B1065271
theorem B798007 : Blo 630300 798007 := bstep (se 1 (by rfl) ⟨598505, by rfl⟩ : syracuseStep 798007 = 1197011) B1197011
theorem B634239 : Blo 630300 634239 := bstep (se 1 (by rfl) ⟨475679, by rfl⟩ : syracuseStep 634239 = 951359) B951359
theorem B634267 : Blo 630300 634267 := bstep (se 1 (by rfl) ⟨475700, by rfl⟩ : syracuseStep 634267 = 951401) B951401
theorem B2567681 : Blo 630300 2567681 := bstep (se 2 (by rfl) ⟨962880, by rfl⟩ : syracuseStep 2567681 = 1925761) B1925761
theorem B5385761 : Blo 630300 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B2698895 : Blo 630300 2698895 := bstep (se 1 (by rfl) ⟨2024171, by rfl⟩ : syracuseStep 2698895 = 4048343) B4048343
theorem B2699203 : Blo 630300 2699203 := bstep (se 1 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 2699203 = 4048805) B4048805
theorem B962687 : Blo 630300 962687 := bstep (se 1 (by rfl) ⟨722015, by rfl⟩ : syracuseStep 962687 = 1444031) B1444031
theorem B2273849 : Blo 630300 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B5386823 : Blo 630300 5386823 := bstep (se 1 (by rfl) ⟨4040117, by rfl⟩ : syracuseStep 5386823 = 8080235) B8080235
theorem B1422089 : Blo 630300 1422089 := bstep (se 2 (by rfl) ⟨533283, by rfl⟩ : syracuseStep 1422089 = 1066567) B1066567
theorem B1422143 : Blo 630300 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B2700161 : Blo 630300 2700161 := bstep (se 2 (by rfl) ⟨1012560, by rfl⟩ : syracuseStep 2700161 = 2025121) B2025121
theorem B1422287 : Blo 630300 1422287 := bstep (se 1 (by rfl) ⟨1066715, by rfl⟩ : syracuseStep 1422287 = 2133431) B2133431
theorem B1422377 : Blo 630300 1422377 := bstep (se 2 (by rfl) ⟨533391, by rfl⟩ : syracuseStep 1422377 = 1066783) B1066783
theorem B5846057 : Blo 630300 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B898231 : Blo 630300 898231 := bstep (se 1 (by rfl) ⟨673673, by rfl⟩ : syracuseStep 898231 = 1347347) B1347347
theorem B1127689 : Blo 630300 1127689 := bstep (se 2 (by rfl) ⟨422883, by rfl⟩ : syracuseStep 1127689 = 845767) B845767
theorem B1422665 : Blo 630300 1422665 := bstep (se 2 (by rfl) ⟨533499, by rfl⟩ : syracuseStep 1422665 = 1066999) B1066999
theorem B15349459 : Blo 630300 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B1423655 : Blo 630300 1423655 := bstep (se 1 (by rfl) ⟨1067741, by rfl⟩ : syracuseStep 1423655 = 2135483) B2135483
theorem B2406779 : Blo 630300 2406779 := bstep (se 1 (by rfl) ⟨1805084, by rfl⟩ : syracuseStep 2406779 = 3610169) B3610169
theorem B1522127 : Blo 630300 1522127 := bstep (se 1 (by rfl) ⟨1141595, by rfl⟩ : syracuseStep 1522127 = 2283191) B2283191
theorem B1424015 : Blo 630300 1424015 := bstep (se 1 (by rfl) ⟨1068011, by rfl⟩ : syracuseStep 1424015 = 2136023) B2136023
theorem B1522319 : Blo 630300 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B1424105 : Blo 630300 1424105 := bstep (se 2 (by rfl) ⟨534039, by rfl⟩ : syracuseStep 1424105 = 1068079) B1068079
theorem B1063847 : Blo 630300 1063847 := bstep (se 1 (by rfl) ⟨797885, by rfl⟩ : syracuseStep 1063847 = 1595771) B1595771
theorem B1424339 : Blo 630300 1424339 := bstep (se 1 (by rfl) ⟨1068254, by rfl⟩ : syracuseStep 1424339 = 2136509) B2136509
theorem B1424609 : Blo 630300 1424609 := bstep (se 2 (by rfl) ⟨534228, by rfl⟩ : syracuseStep 1424609 = 1068457) B1068457
theorem B1523195 : Blo 630300 1523195 := bstep (se 1 (by rfl) ⟨1142396, by rfl⟩ : syracuseStep 1523195 = 2284793) B2284793
theorem B4046345 : Blo 630300 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B1424915 : Blo 630300 1424915 := bstep (se 1 (by rfl) ⟨1068686, by rfl⟩ : syracuseStep 1424915 = 2137373) B2137373
theorem B900839 : Blo 630300 900839 := bstep (se 1 (by rfl) ⟨675629, by rfl⟩ : syracuseStep 900839 = 1351259) B1351259
theorem B5193559 : Blo 630300 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B3850213 : Blo 630300 3850213 := bstep (se 4 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 3850213 = 721915) B721915
theorem B1425599 : Blo 630300 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B2506943 : Blo 630300 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B1426031 : Blo 630300 1426031 := bstep (se 1 (by rfl) ⟨1069523, by rfl⟩ : syracuseStep 1426031 = 2139047) B2139047
theorem B14566103 : Blo 630300 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B4047727 : Blo 630300 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B4375547 : Blo 630300 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1426427 : Blo 630300 1426427 := bstep (se 1 (by rfl) ⟨1069820, by rfl⟩ : syracuseStep 1426427 = 2139641) B2139641
theorem B1426607 : Blo 630300 1426607 := bstep (se 1 (by rfl) ⟨1069955, by rfl⟩ : syracuseStep 1426607 = 2139911) B2139911
theorem B1426643 : Blo 630300 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B1426913 : Blo 630300 1426913 := bstep (se 2 (by rfl) ⟨535092, by rfl⟩ : syracuseStep 1426913 = 1070185) B1070185
theorem B1066601 : Blo 630300 1066601 := bstep (se 2 (by rfl) ⟨399975, by rfl⟩ : syracuseStep 1066601 = 799951) B799951
theorem B2705183 : Blo 630300 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B3196745 : Blo 630300 3196745 := bstep (se 2 (by rfl) ⟨1198779, by rfl⟩ : syracuseStep 3196745 = 2397559) B2397559
theorem B1067195 : Blo 630300 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B5392595 : Blo 630300 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B1198415 : Blo 630300 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B3197555 : Blo 630300 3197555 := bstep (se 1 (by rfl) ⟨2398166, by rfl⟩ : syracuseStep 3197555 = 4796333) B4796333
theorem B1067897 : Blo 630300 1067897 := bstep (se 2 (by rfl) ⟨400461, by rfl⟩ : syracuseStep 1067897 = 800923) B800923
theorem B1199099 : Blo 630300 1199099 := bstep (se 1 (by rfl) ⟨899324, by rfl⟩ : syracuseStep 1199099 = 1798649) B1798649
theorem B1199585 : Blo 630300 1199585 := bstep (se 2 (by rfl) ⟨449844, by rfl⟩ : syracuseStep 1199585 = 899689) B899689
theorem B1069031 : Blo 630300 1069031 := bstep (se 1 (by rfl) ⟨801773, by rfl⟩ : syracuseStep 1069031 = 1603547) B1603547
theorem B1069051 : Blo 630300 1069051 := bstep (se 1 (by rfl) ⟨801788, by rfl⟩ : syracuseStep 1069051 = 1603577) B1603577
theorem B1069159 : Blo 630300 1069159 := bstep (se 1 (by rfl) ⟨801869, by rfl⟩ : syracuseStep 1069159 = 1603739) B1603739
theorem B3199175 : Blo 630300 3199175 := bstep (se 1 (by rfl) ⟨2399381, by rfl⟩ : syracuseStep 3199175 = 4798763) B4798763
theorem B3952849 : Blo 630300 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B2281691 : Blo 630300 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B1069915 : Blo 630300 1069915 := bstep (se 1 (by rfl) ⟨802436, by rfl⟩ : syracuseStep 1069915 = 1604873) B1604873
theorem B43897859 : Blo 630300 43897859 := bstep (se 1 (by rfl) ⟨32923394, by rfl⟩ : syracuseStep 43897859 = 65846789) B65846789
theorem B5395571 : Blo 630300 5395571 := bstep (se 1 (by rfl) ⟨4046678, by rfl⟩ : syracuseStep 5395571 = 8093357) B8093357
theorem B709951 : Blo 630300 709951 := bstep (se 1 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 709951 = 1064927) B1064927
theorem B2708873 : Blo 630300 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B2020879 : Blo 630300 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B3200633 : Blo 630300 3200633 := bstep (se 2 (by rfl) ⟨1200237, by rfl⟩ : syracuseStep 3200633 = 2400475) B2400475
theorem B5461739 : Blo 630300 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B9721579 : Blo 630300 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B710383 : Blo 630300 710383 := bstep (se 1 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 710383 = 1065575) B1065575
theorem B710491 : Blo 630300 710491 := bstep (se 1 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 710491 = 1065737) B1065737
theorem B10246337 : Blo 630300 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B710887 : Blo 630300 710887 := bstep (se 1 (by rfl) ⟨533165, by rfl⟩ : syracuseStep 710887 = 1066331) B1066331
theorem B46815671 : Blo 630300 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B16472915 : Blo 630300 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B711535 : Blo 630300 711535 := bstep (se 1 (by rfl) ⟨533651, by rfl⟩ : syracuseStep 711535 = 1067303) B1067303
theorem B299850821 : Blo 630300 299850821 := bstep (se 4 (by rfl) ⟨28111014, by rfl⟩ : syracuseStep 299850821 = 56222029) B56222029
theorem B1596905 : Blo 630300 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B8085203 : Blo 630300 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B9264851 : Blo 630300 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B712615 : Blo 630300 712615 := bstep (se 1 (by rfl) ⟨534461, by rfl⟩ : syracuseStep 712615 = 1068923) B1068923
theorem B3596795 : Blo 630300 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B1795709 : Blo 630300 1795709 := bstep (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) B673391
theorem B1174279 : Blo 630300 1174279 := bstep (se 1 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 1174279 = 1761419) B1761419
theorem B94563235 : Blo 630300 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B1600681 : Blo 630300 1600681 := bstep (se 2 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 1600681 = 1200511) B1200511
theorem B945563 : Blo 630300 945563 := bstep (se 1 (by rfl) ⟨709172, by rfl⟩ : syracuseStep 945563 = 1418345) B1418345
theorem B3042755 : Blo 630300 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B4812371 : Blo 630300 4812371 := bstep (se 1 (by rfl) ⟨3609278, by rfl⟩ : syracuseStep 4812371 = 7218557) B7218557
theorem B3599963 : Blo 630300 3599963 := bstep (se 1 (by rfl) ⟨2699972, by rfl⟩ : syracuseStep 3599963 = 5399945) B5399945
theorem B373616327 : Blo 630300 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B945983 : Blo 630300 945983 := bstep (se 1 (by rfl) ⟨709487, by rfl⟩ : syracuseStep 945983 = 1418975) B1418975
theorem B946169 : Blo 630300 946169 := bstep (se 2 (by rfl) ⟨354813, by rfl⟩ : syracuseStep 946169 = 709627) B709627
theorem B41087033 : Blo 630300 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B1601633 : Blo 630300 1601633 := bstep (se 2 (by rfl) ⟨600612, by rfl⟩ : syracuseStep 1601633 = 1201225) B1201225
theorem B946409 : Blo 630300 946409 := bstep (se 2 (by rfl) ⟨354903, by rfl⟩ : syracuseStep 946409 = 709807) B709807
theorem B946535 : Blo 630300 946535 := bstep (se 1 (by rfl) ⟨709901, by rfl⟩ : syracuseStep 946535 = 1419803) B1419803
theorem B947081 : Blo 630300 947081 := bstep (se 2 (by rfl) ⟨355155, by rfl⟩ : syracuseStep 947081 = 710311) B710311
theorem B947465 : Blo 630300 947465 := bstep (se 2 (by rfl) ⟨355299, by rfl⟩ : syracuseStep 947465 = 710599) B710599
theorem B947519 : Blo 630300 947519 := bstep (se 1 (by rfl) ⟨710639, by rfl⟩ : syracuseStep 947519 = 1421279) B1421279
theorem B3044699 : Blo 630300 3044699 := bstep (se 1 (by rfl) ⟨2283524, by rfl⟩ : syracuseStep 3044699 = 4567049) B4567049
theorem B2127275 : Blo 630300 2127275 := bstep (se 1 (by rfl) ⟨1595456, by rfl⟩ : syracuseStep 2127275 = 3190913) B3190913
theorem B1603091 : Blo 630300 1603091 := bstep (se 1 (by rfl) ⟨1202318, by rfl⟩ : syracuseStep 1603091 = 2404637) B2404637
theorem B947945 : Blo 630300 947945 := bstep (se 2 (by rfl) ⟨355479, by rfl⟩ : syracuseStep 947945 = 710959) B710959
theorem B947951 : Blo 630300 947951 := bstep (se 1 (by rfl) ⟨710963, by rfl⟩ : syracuseStep 947951 = 1421927) B1421927
theorem B2127815 : Blo 630300 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B7206893 : Blo 630300 7206893 := bstep (se 3 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 7206893 = 2702585) B2702585
theorem B5470337 : Blo 630300 5470337 := bstep (se 2 (by rfl) ⟨2051376, by rfl⟩ : syracuseStep 5470337 = 4102753) B4102753
theorem B948407 : Blo 630300 948407 := bstep (se 1 (by rfl) ⟨711305, by rfl⟩ : syracuseStep 948407 = 1422611) B1422611
theorem B948455 : Blo 630300 948455 := bstep (se 1 (by rfl) ⟨711341, by rfl⟩ : syracuseStep 948455 = 1422683) B1422683
theorem B6846767 : Blo 630300 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B1800539 : Blo 630300 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B15366581 : Blo 630300 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B948827 : Blo 630300 948827 := bstep (se 1 (by rfl) ⟨711620, by rfl⟩ : syracuseStep 948827 = 1423241) B1423241
theorem B1604225 : Blo 630300 1604225 := bstep (se 2 (by rfl) ⟨601584, by rfl⟩ : syracuseStep 1604225 = 1203169) B1203169
theorem B948971 : Blo 630300 948971 := bstep (se 1 (by rfl) ⟨711728, by rfl⟩ : syracuseStep 948971 = 1423457) B1423457
theorem B949001 : Blo 630300 949001 := bstep (se 2 (by rfl) ⟨355875, by rfl⟩ : syracuseStep 949001 = 711751) B711751
theorem B12352501 : Blo 630300 12352501 := bstep (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) B1158047
theorem B19758275 : Blo 630300 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1605035 : Blo 630300 1605035 := bstep (se 1 (by rfl) ⟨1203776, by rfl⟩ : syracuseStep 1605035 = 2407553) B2407553
theorem B2194877 : Blo 630300 2194877 := bstep (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) B823079
theorem B2883023 : Blo 630300 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B949871 : Blo 630300 949871 := bstep (se 1 (by rfl) ⟨712403, by rfl⟩ : syracuseStep 949871 = 1424807) B1424807
theorem B949991 : Blo 630300 949991 := bstep (se 1 (by rfl) ⟨712493, by rfl⟩ : syracuseStep 949991 = 1424987) B1424987
theorem B2031439 : Blo 630300 2031439 := bstep (se 1 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 2031439 = 3047159) B3047159
theorem B3047311 : Blo 630300 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B950183 : Blo 630300 950183 := bstep (se 1 (by rfl) ⟨712637, by rfl⟩ : syracuseStep 950183 = 1425275) B1425275
theorem B950399 : Blo 630300 950399 := bstep (se 1 (by rfl) ⟨712799, by rfl⟩ : syracuseStep 950399 = 1425599) B1425599
theorem B950687 : Blo 630300 950687 := bstep (se 1 (by rfl) ⟨713015, by rfl⟩ : syracuseStep 950687 = 1426031) B1426031
theorem B6685181 : Blo 630300 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B2917031 : Blo 630300 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B950951 : Blo 630300 950951 := bstep (se 1 (by rfl) ⟨713213, by rfl⟩ : syracuseStep 950951 = 1426427) B1426427
theorem B7013051 : Blo 630300 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B951071 : Blo 630300 951071 := bstep (se 1 (by rfl) ⟨713303, by rfl⟩ : syracuseStep 951071 = 1426607) B1426607
theorem B951095 : Blo 630300 951095 := bstep (se 1 (by rfl) ⟨713321, by rfl⟩ : syracuseStep 951095 = 1426643) B1426643
theorem B951275 : Blo 630300 951275 := bstep (se 1 (by rfl) ⟨713456, by rfl⟩ : syracuseStep 951275 = 1426913) B1426913
theorem B1803455 : Blo 630300 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2131163 : Blo 630300 2131163 := bstep (se 1 (by rfl) ⟨1598372, by rfl⟩ : syracuseStep 2131163 = 3196745) B3196745
theorem B12977863 : Blo 630300 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B2131703 : Blo 630300 2131703 := bstep (se 1 (by rfl) ⟨1598777, by rfl⟩ : syracuseStep 2131703 = 3197555) B3197555
theorem B1706015 : Blo 630300 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B6818519 : Blo 630300 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B2132783 : Blo 630300 2132783 := bstep (se 1 (by rfl) ⟨1599587, by rfl⟩ : syracuseStep 2132783 = 3199175) B3199175
theorem B29265239 : Blo 630300 29265239 := bstep (se 1 (by rfl) ⟨21948929, by rfl⟩ : syracuseStep 29265239 = 43897859) B43897859
theorem B1805915 : Blo 630300 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B2133755 : Blo 630300 2133755 := bstep (se 1 (by rfl) ⟨1600316, by rfl⟩ : syracuseStep 2133755 = 3200633) B3200633
theorem B3641159 : Blo 630300 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B2134241 : Blo 630300 2134241 := bstep (se 2 (by rfl) ⟨800340, by rfl⟩ : syracuseStep 2134241 = 1600681) B1600681
theorem B4788557 : Blo 630300 4788557 := bstep (se 3 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 4788557 = 1795709) B1795709
theorem B10981943 : Blo 630300 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B7673075 : Blo 630300 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B2397863 : Blo 630300 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B3087503 : Blo 630300 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B2694505 : Blo 630300 2694505 := bstep (se 2 (by rfl) ⟨1010439, by rfl⟩ : syracuseStep 2694505 = 2020879) B2020879
theorem B630375 : Blo 630300 630375 := bstep (se 1 (by rfl) ⟨472781, by rfl⟩ : syracuseStep 630375 = 945563) B945563
theorem B1711787 : Blo 630300 1711787 := bstep (se 1 (by rfl) ⟨1283840, by rfl⟩ : syracuseStep 1711787 = 2567681) B2567681
theorem B2399975 : Blo 630300 2399975 := bstep (se 1 (by rfl) ⟨1799981, by rfl⟩ : syracuseStep 2399975 = 3599963) B3599963
theorem B249077551 : Blo 630300 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B630655 : Blo 630300 630655 := bstep (se 1 (by rfl) ⟨472991, by rfl⟩ : syracuseStep 630655 = 945983) B945983
theorem B630779 : Blo 630300 630779 := bstep (se 1 (by rfl) ⟨473084, by rfl⟩ : syracuseStep 630779 = 946169) B946169
theorem B630939 : Blo 630300 630939 := bstep (se 1 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 630939 = 946409) B946409
theorem B631023 : Blo 630300 631023 := bstep (se 1 (by rfl) ⟨473267, by rfl⟩ : syracuseStep 631023 = 946535) B946535
theorem B1515899 : Blo 630300 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B631387 : Blo 630300 631387 := bstep (se 1 (by rfl) ⟨473540, by rfl⟩ : syracuseStep 631387 = 947081) B947081
theorem B631643 : Blo 630300 631643 := bstep (se 1 (by rfl) ⟨473732, by rfl⟩ : syracuseStep 631643 = 947465) B947465
theorem B631679 : Blo 630300 631679 := bstep (se 1 (by rfl) ⟨473759, by rfl⟩ : syracuseStep 631679 = 947519) B947519
theorem B1418183 : Blo 630300 1418183 := bstep (se 1 (by rfl) ⟨1063637, by rfl⟩ : syracuseStep 1418183 = 2127275) B2127275
theorem B631963 : Blo 630300 631963 := bstep (se 1 (by rfl) ⟨473972, by rfl⟩ : syracuseStep 631963 = 947945) B947945
theorem B631967 : Blo 630300 631967 := bstep (se 1 (by rfl) ⟨473975, by rfl⟩ : syracuseStep 631967 = 947951) B947951
theorem B1418543 : Blo 630300 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B3646891 : Blo 630300 3646891 := bstep (se 1 (by rfl) ⟨2735168, by rfl⟩ : syracuseStep 3646891 = 5470337) B5470337
theorem B632271 : Blo 630300 632271 := bstep (se 1 (by rfl) ⟨474203, by rfl⟩ : syracuseStep 632271 = 948407) B948407
theorem B632303 : Blo 630300 632303 := bstep (se 1 (by rfl) ⟨474227, by rfl⟩ : syracuseStep 632303 = 948455) B948455
theorem B4564511 : Blo 630300 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B632551 : Blo 630300 632551 := bstep (se 1 (by rfl) ⟨474413, by rfl⟩ : syracuseStep 632551 = 948827) B948827
theorem B632647 : Blo 630300 632647 := bstep (se 1 (by rfl) ⟨474485, by rfl⟩ : syracuseStep 632647 = 948971) B948971
theorem B632667 : Blo 630300 632667 := bstep (se 1 (by rfl) ⟨474500, by rfl⟩ : syracuseStep 632667 = 949001) B949001
theorem B2402237 : Blo 630300 2402237 := bstep (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) B900839
theorem B2697563 : Blo 630300 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B633247 : Blo 630300 633247 := bstep (se 1 (by rfl) ⟨474935, by rfl⟩ : syracuseStep 633247 = 949871) B949871
theorem B6924745 : Blo 630300 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B633327 : Blo 630300 633327 := bstep (se 1 (by rfl) ⟨474995, by rfl⟩ : syracuseStep 633327 = 949991) B949991
theorem B633455 : Blo 630300 633455 := bstep (se 1 (by rfl) ⟨475091, by rfl⟩ : syracuseStep 633455 = 950183) B950183
theorem B633671 : Blo 630300 633671 := bstep (se 1 (by rfl) ⟨475253, by rfl⟩ : syracuseStep 633671 = 950507) B950507
theorem B633711 : Blo 630300 633711 := bstep (se 1 (by rfl) ⟨475283, by rfl⟩ : syracuseStep 633711 = 950567) B950567
theorem B2403391 : Blo 630300 2403391 := bstep (se 1 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 2403391 = 3605087) B3605087
theorem B9710735 : Blo 630300 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B7711955 : Blo 630300 7711955 := bstep (se 1 (by rfl) ⟨5783966, by rfl⟩ : syracuseStep 7711955 = 11567933) B11567933
theorem B634159 : Blo 630300 634159 := bstep (se 1 (by rfl) ⟨475619, by rfl⟩ : syracuseStep 634159 = 951239) B951239
theorem B634271 : Blo 630300 634271 := bstep (se 1 (by rfl) ⟨475703, by rfl⟩ : syracuseStep 634271 = 951407) B951407
theorem B2272799 : Blo 630300 2272799 := bstep (se 1 (by rfl) ⟨1704599, by rfl⟩ : syracuseStep 2272799 = 3409199) B3409199
theorem B4566611 : Blo 630300 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B1420991 : Blo 630300 1420991 := bstep (se 1 (by rfl) ⟨1065743, by rfl⟩ : syracuseStep 1420991 = 2131487) B2131487
theorem B3124939 : Blo 630300 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B1421567 : Blo 630300 1421567 := bstep (se 1 (by rfl) ⟨1066175, by rfl⟩ : syracuseStep 1421567 = 2132351) B2132351
theorem B3191399 : Blo 630300 3191399 := bstep (se 1 (by rfl) ⟨2393549, by rfl⟩ : syracuseStep 3191399 = 4787099) B4787099
theorem B799399 : Blo 630300 799399 := bstep (se 1 (by rfl) ⟨599549, by rfl⟩ : syracuseStep 799399 = 1199099) B1199099
theorem B13874123 : Blo 630300 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B799723 : Blo 630300 799723 := bstep (se 1 (by rfl) ⟨599792, by rfl⟩ : syracuseStep 799723 = 1199585) B1199585
theorem B1422719 : Blo 630300 1422719 := bstep (se 1 (by rfl) ⟨1067039, by rfl⟩ : syracuseStep 1422719 = 2134079) B2134079
theorem B2405807 : Blo 630300 2405807 := bstep (se 1 (by rfl) ⟨1804355, by rfl⟩ : syracuseStep 2405807 = 3608711) B3608711
theorem B8107451 : Blo 630300 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B1521127 : Blo 630300 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B898715 : Blo 630300 898715 := bstep (se 1 (by rfl) ⟨674036, by rfl⟩ : syracuseStep 898715 = 1348073) B1348073
theorem B2406095 : Blo 630300 2406095 := bstep (se 1 (by rfl) ⟨1804571, by rfl⟩ : syracuseStep 2406095 = 3609143) B3609143
theorem B1423187 : Blo 630300 1423187 := bstep (se 1 (by rfl) ⟨1067390, by rfl⟩ : syracuseStep 1423187 = 2134781) B2134781
theorem B1423295 : Blo 630300 1423295 := bstep (se 1 (by rfl) ⟨1067471, by rfl⟩ : syracuseStep 1423295 = 2134943) B2134943
theorem B2406611 : Blo 630300 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B2406793 : Blo 630300 2406793 := bstep (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) B1805095
theorem B6830891 : Blo 630300 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B31210447 : Blo 630300 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B1064009 : Blo 630300 1064009 := bstep (se 2 (by rfl) ⟨399003, by rfl⟩ : syracuseStep 1064009 = 798007) B798007
theorem B199900547 : Blo 630300 199900547 := bstep (se 1 (by rfl) ⟨149925410, by rfl⟩ : syracuseStep 199900547 = 299850821) B299850821
theorem B1064603 : Blo 630300 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B5390135 : Blo 630300 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B6176567 : Blo 630300 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B1425401 : Blo 630300 1425401 := bstep (se 2 (by rfl) ⟨534525, by rfl⟩ : syracuseStep 1425401 = 1069051) B1069051
theorem B3194963 : Blo 630300 3194963 := bstep (se 1 (by rfl) ⟨2396222, by rfl⟩ : syracuseStep 3194963 = 4792445) B4792445
theorem B1425491 : Blo 630300 1425491 := bstep (se 1 (by rfl) ⟨1069118, by rfl⟩ : syracuseStep 1425491 = 2138237) B2138237
theorem B1425545 : Blo 630300 1425545 := bstep (se 2 (by rfl) ⟨534579, by rfl⟩ : syracuseStep 1425545 = 1069159) B1069159
theorem B1425671 : Blo 630300 1425671 := bstep (se 1 (by rfl) ⟨1069253, by rfl⟩ : syracuseStep 1425671 = 2138507) B2138507
theorem B9126533 : Blo 630300 9126533 := bstep (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) B1711225
theorem B3195773 : Blo 630300 3195773 := bstep (se 3 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 3195773 = 1198415) B1198415
theorem B1426553 : Blo 630300 1426553 := bstep (se 2 (by rfl) ⟨534957, by rfl⟩ : syracuseStep 1426553 = 1069915) B1069915
theorem B1426751 : Blo 630300 1426751 := bstep (se 1 (by rfl) ⟨1070063, by rfl⟩ : syracuseStep 1426751 = 2140127) B2140127
theorem B6014341 : Blo 630300 6014341 := bstep (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) B1127689
theorem B1197641 : Blo 630300 1197641 := bstep (se 2 (by rfl) ⟨449115, by rfl⟩ : syracuseStep 1197641 = 898231) B898231
theorem B20465945 : Blo 630300 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B12962105 : Blo 630300 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B3590507 : Blo 630300 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B1067755 : Blo 630300 1067755 := bstep (se 1 (by rfl) ⟨800816, by rfl⟩ : syracuseStep 1067755 = 1601633) B1601633
theorem B641791 : Blo 630300 641791 := bstep (se 1 (by rfl) ⟨481343, by rfl⟩ : syracuseStep 641791 = 962687) B962687
theorem B3591215 : Blo 630300 3591215 := bstep (se 1 (by rfl) ⟨2693411, by rfl⟩ : syracuseStep 3591215 = 5386823) B5386823
theorem B1068727 : Blo 630300 1068727 := bstep (se 1 (by rfl) ⟨801545, by rfl⟩ : syracuseStep 1068727 = 1603091) B1603091
theorem B16470001 : Blo 630300 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B4804595 : Blo 630300 4804595 := bstep (se 1 (by rfl) ⟨3603446, by rfl⟩ : syracuseStep 4804595 = 7206893) B7206893
theorem B1200359 : Blo 630300 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B10244387 : Blo 630300 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B1069483 : Blo 630300 1069483 := bstep (se 1 (by rfl) ⟨802112, by rfl⟩ : syracuseStep 1069483 = 1604225) B1604225
theorem B709231 : Blo 630300 709231 := bstep (se 1 (by rfl) ⟨531923, by rfl⟩ : syracuseStep 709231 = 1063847) B1063847
theorem B1070023 : Blo 630300 1070023 := bstep (se 1 (by rfl) ⟨802517, by rfl⟩ : syracuseStep 1070023 = 1605035) B1605035
theorem B1463251 : Blo 630300 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B1922015 : Blo 630300 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B2708585 : Blo 630300 2708585 := bstep (se 2 (by rfl) ⟨1015719, by rfl⟩ : syracuseStep 2708585 = 2031439) B2031439
theorem B2020481 : Blo 630300 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B5133617 : Blo 630300 5133617 := bstep (se 2 (by rfl) ⟨1925106, by rfl⟩ : syracuseStep 5133617 = 3850213) B3850213
theorem B16602457 : Blo 630300 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B168450191 : Blo 630300 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B711067 : Blo 630300 711067 := bstep (se 1 (by rfl) ⟨533300, by rfl⟩ : syracuseStep 711067 = 1066601) B1066601
theorem B5396969 : Blo 630300 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B2022121 : Blo 630300 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B711463 : Blo 630300 711463 := bstep (se 1 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 711463 = 1067195) B1067195
theorem B3595063 : Blo 630300 3595063 := bstep (se 1 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 3595063 = 5392595) B5392595
theorem B3201929 : Blo 630300 3201929 := bstep (se 2 (by rfl) ⟨1200723, by rfl⟩ : syracuseStep 3201929 = 2401447) B2401447
theorem B711931 : Blo 630300 711931 := bstep (se 1 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 711931 = 1067897) B1067897
theorem B712687 : Blo 630300 712687 := bstep (se 1 (by rfl) ⟨534515, by rfl⟩ : syracuseStep 712687 = 1069031) B1069031
theorem B4547123 : Blo 630300 4547123 := bstep (se 1 (by rfl) ⟨3410342, by rfl⟩ : syracuseStep 4547123 = 6820685) B6820685
theorem B5202505 : Blo 630300 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B3597047 : Blo 630300 3597047 := bstep (se 1 (by rfl) ⟨2697785, by rfl⟩ : syracuseStep 3597047 = 5395571) B5395571
theorem B1565705 : Blo 630300 1565705 := bstep (se 2 (by rfl) ⟨587139, by rfl⟩ : syracuseStep 1565705 = 1174279) B1174279
theorem B126084313 : Blo 630300 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B4810427 : Blo 630300 4810427 := bstep (se 1 (by rfl) ⟨3607820, by rfl⟩ : syracuseStep 4810427 = 7215641) B7215641
theorem B3238211 : Blo 630300 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B3598937 : Blo 630300 3598937 := bstep (se 2 (by rfl) ⟨1349601, by rfl⟩ : syracuseStep 3598937 = 2699203) B2699203
theorem B5270465 : Blo 630300 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B1797191 : Blo 630300 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B1600823 : Blo 630300 1600823 := bstep (se 1 (by rfl) ⟨1200617, by rfl⟩ : syracuseStep 1600823 = 2401235) B2401235
theorem B945479 : Blo 630300 945479 := bstep (se 1 (by rfl) ⟨709109, by rfl⟩ : syracuseStep 945479 = 1418219) B1418219
theorem B945767 : Blo 630300 945767 := bstep (se 1 (by rfl) ⟨709325, by rfl⟩ : syracuseStep 945767 = 1418651) B1418651
theorem B1797851 : Blo 630300 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B946151 : Blo 630300 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B946271 : Blo 630300 946271 := bstep (se 1 (by rfl) ⟨709703, by rfl⟩ : syracuseStep 946271 = 1419407) B1419407
theorem B946331 : Blo 630300 946331 := bstep (se 1 (by rfl) ⟨709748, by rfl⟩ : syracuseStep 946331 = 1419497) B1419497
theorem B946511 : Blo 630300 946511 := bstep (se 1 (by rfl) ⟨709883, by rfl⟩ : syracuseStep 946511 = 1419767) B1419767
theorem B4059517 : Blo 630300 4059517 := bstep (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) B1522319
theorem B946601 : Blo 630300 946601 := bstep (se 2 (by rfl) ⟨354975, by rfl⟩ : syracuseStep 946601 = 709951) B709951
theorem B946907 : Blo 630300 946907 := bstep (se 1 (by rfl) ⟨710180, by rfl⟩ : syracuseStep 946907 = 1420361) B1420361
theorem B2028503 : Blo 630300 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B947177 : Blo 630300 947177 := bstep (se 2 (by rfl) ⟨355191, by rfl⟩ : syracuseStep 947177 = 710383) B710383
theorem B3208247 : Blo 630300 3208247 := bstep (se 1 (by rfl) ⟨2406185, by rfl⟩ : syracuseStep 3208247 = 4812371) B4812371
theorem B1799263 : Blo 630300 1799263 := bstep (se 1 (by rfl) ⟨1349447, by rfl⟩ : syracuseStep 1799263 = 2698895) B2698895
theorem B947321 : Blo 630300 947321 := bstep (se 2 (by rfl) ⟨355245, by rfl⟩ : syracuseStep 947321 = 710491) B710491
theorem B27391355 : Blo 630300 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B947849 : Blo 630300 947849 := bstep (se 2 (by rfl) ⟨355443, by rfl⟩ : syracuseStep 947849 = 710887) B710887
theorem B8091353 : Blo 630300 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B948059 : Blo 630300 948059 := bstep (se 1 (by rfl) ⟨711044, by rfl⟩ : syracuseStep 948059 = 1422089) B1422089
theorem B948095 : Blo 630300 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B1800107 : Blo 630300 1800107 := bstep (se 1 (by rfl) ⟨1350080, by rfl⟩ : syracuseStep 1800107 = 2700161) B2700161
theorem B948191 : Blo 630300 948191 := bstep (se 1 (by rfl) ⟨711143, by rfl⟩ : syracuseStep 948191 = 1422287) B1422287
theorem B948251 : Blo 630300 948251 := bstep (se 1 (by rfl) ⟨711188, by rfl⟩ : syracuseStep 948251 = 1422377) B1422377
theorem B3897371 : Blo 630300 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B948443 : Blo 630300 948443 := bstep (se 1 (by rfl) ⟨711332, by rfl⟩ : syracuseStep 948443 = 1422665) B1422665
theorem B2029799 : Blo 630300 2029799 := bstep (se 1 (by rfl) ⟨1522349, by rfl⟩ : syracuseStep 2029799 = 3044699) B3044699
theorem B948713 : Blo 630300 948713 := bstep (se 2 (by rfl) ⟨355767, by rfl⟩ : syracuseStep 948713 = 711535) B711535
theorem B949103 : Blo 630300 949103 := bstep (se 1 (by rfl) ⟨711827, by rfl⟩ : syracuseStep 949103 = 1423655) B1423655
theorem B1604519 : Blo 630300 1604519 := bstep (se 1 (by rfl) ⟨1203389, by rfl⟩ : syracuseStep 1604519 = 2406779) B2406779
theorem B1014751 : Blo 630300 1014751 := bstep (se 1 (by rfl) ⟨761063, by rfl⟩ : syracuseStep 1014751 = 1522127) B1522127
theorem B949343 : Blo 630300 949343 := bstep (se 1 (by rfl) ⟨712007, by rfl⟩ : syracuseStep 949343 = 1424015) B1424015
theorem B949403 : Blo 630300 949403 := bstep (se 1 (by rfl) ⟨712052, by rfl⟩ : syracuseStep 949403 = 1424105) B1424105
theorem B949559 : Blo 630300 949559 := bstep (se 1 (by rfl) ⟨712169, by rfl⟩ : syracuseStep 949559 = 1424339) B1424339
theorem B13172183 : Blo 630300 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B949739 : Blo 630300 949739 := bstep (se 1 (by rfl) ⟨712304, by rfl⟩ : syracuseStep 949739 = 1424609) B1424609
theorem B1015463 : Blo 630300 1015463 := bstep (se 1 (by rfl) ⟨761597, by rfl⟩ : syracuseStep 1015463 = 1523195) B1523195
theorem B949943 : Blo 630300 949943 := bstep (se 1 (by rfl) ⟨712457, by rfl⟩ : syracuseStep 949943 = 1424915) B1424915
theorem B12156713 : Blo 630300 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B4063081 : Blo 630300 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B950153 : Blo 630300 950153 := bstep (se 2 (by rfl) ⟨356307, by rfl⟩ : syracuseStep 950153 = 712615) B712615
theorem B2129975 : Blo 630300 2129975 := bstep (se 1 (by rfl) ⟨1597481, by rfl⟩ : syracuseStep 2129975 = 3194963) B3194963
theorem B950327 : Blo 630300 950327 := bstep (se 1 (by rfl) ⟨712745, by rfl⟩ : syracuseStep 950327 = 1425491) B1425491
theorem B950363 : Blo 630300 950363 := bstep (se 1 (by rfl) ⟨712772, by rfl⟩ : syracuseStep 950363 = 1425545) B1425545
theorem B950447 : Blo 630300 950447 := bstep (se 1 (by rfl) ⟨712835, by rfl⟩ : syracuseStep 950447 = 1425671) B1425671
theorem B4456787 : Blo 630300 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B2130515 : Blo 630300 2130515 := bstep (se 1 (by rfl) ⟨1597886, by rfl⟩ : syracuseStep 2130515 = 3195773) B3195773
theorem B951035 : Blo 630300 951035 := bstep (se 1 (by rfl) ⟨713276, by rfl⟩ : syracuseStep 951035 = 1426553) B1426553
theorem B951167 : Blo 630300 951167 := bstep (se 1 (by rfl) ⟨713375, by rfl⟩ : syracuseStep 951167 = 1426751) B1426751
theorem B103581173 : Blo 630300 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B2393671 : Blo 630300 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B2394143 : Blo 630300 2394143 := bstep (se 1 (by rfl) ⟨1795607, by rfl⟩ : syracuseStep 2394143 = 3591215) B3591215
theorem B36997661 : Blo 630300 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B5409341 : Blo 630300 5409341 := bstep (se 3 (by rfl) ⟨1014251, by rfl⟩ : syracuseStep 5409341 = 2028503) B2028503
theorem B1281343 : Blo 630300 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B1805723 : Blo 630300 1805723 := bstep (se 1 (by rfl) ⟨1354292, by rfl⟩ : syracuseStep 1805723 = 2708585) B2708585
theorem B1346987 : Blo 630300 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B5115383 : Blo 630300 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B855721 : Blo 630300 855721 := bstep (se 2 (by rfl) ⟨320895, by rfl⟩ : syracuseStep 855721 = 641791) B641791
theorem B112300127 : Blo 630300 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B2396573 : Blo 630300 2396573 := bstep (se 3 (by rfl) ⟨449357, by rfl⟩ : syracuseStep 2396573 = 898715) B898715
theorem B2134619 : Blo 630300 2134619 := bstep (se 1 (by rfl) ⟨1600964, by rfl⟩ : syracuseStep 2134619 = 3201929) B3201929
theorem B4166585 : Blo 630300 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B5412005 : Blo 630300 5412005 := bstep (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) B1014751
theorem B21960001 : Blo 630300 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B2398031 : Blo 630300 2398031 := bstep (se 1 (by rfl) ⟨1798523, by rfl⟩ : syracuseStep 2398031 = 3597047) B3597047
theorem B5412689 : Blo 630300 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B2399017 : Blo 630300 2399017 := bstep (se 2 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 2399017 = 1799263) B1799263
theorem B2399291 : Blo 630300 2399291 := bstep (se 1 (by rfl) ⟨1799468, by rfl⟩ : syracuseStep 2399291 = 3598937) B3598937
theorem B630319 : Blo 630300 630319 := bstep (se 1 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 630319 = 945479) B945479
theorem B1515199 : Blo 630300 1515199 := bstep (se 1 (by rfl) ⟨1136399, by rfl⟩ : syracuseStep 1515199 = 2272799) B2272799
theorem B630511 : Blo 630300 630511 := bstep (se 1 (by rfl) ⟨472883, by rfl⟩ : syracuseStep 630511 = 945767) B945767
theorem B630767 : Blo 630300 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B630847 : Blo 630300 630847 := bstep (se 1 (by rfl) ⟨473135, by rfl⟩ : syracuseStep 630847 = 946271) B946271
theorem B630887 : Blo 630300 630887 := bstep (se 1 (by rfl) ⟨473165, by rfl⟩ : syracuseStep 630887 = 946331) B946331
theorem B631007 : Blo 630300 631007 := bstep (se 1 (by rfl) ⟨473255, by rfl⟩ : syracuseStep 631007 = 946511) B946511
theorem B631067 : Blo 630300 631067 := bstep (se 1 (by rfl) ⟨473300, by rfl⟩ : syracuseStep 631067 = 946601) B946601
theorem B631271 : Blo 630300 631271 := bstep (se 1 (by rfl) ⟨473453, by rfl⟩ : syracuseStep 631271 = 946907) B946907
theorem B631451 : Blo 630300 631451 := bstep (se 1 (by rfl) ⟨473588, by rfl⟩ : syracuseStep 631451 = 947177) B947177
theorem B2138831 : Blo 630300 2138831 := bstep (se 1 (by rfl) ⟨1604123, by rfl⟩ : syracuseStep 2138831 = 3208247) B3208247
theorem B631547 : Blo 630300 631547 := bstep (se 1 (by rfl) ⟨473660, by rfl⟩ : syracuseStep 631547 = 947321) B947321
theorem B18260903 : Blo 630300 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B2696161 : Blo 630300 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B69215269 : Blo 630300 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B4793417 : Blo 630300 4793417 := bstep (se 2 (by rfl) ⟨1797531, by rfl⟩ : syracuseStep 4793417 = 3595063) B3595063
theorem B631899 : Blo 630300 631899 := bstep (se 1 (by rfl) ⟨473924, by rfl⟩ : syracuseStep 631899 = 947849) B947849
theorem B632039 : Blo 630300 632039 := bstep (se 1 (by rfl) ⟨474029, by rfl⟩ : syracuseStep 632039 = 948059) B948059
theorem B632063 : Blo 630300 632063 := bstep (se 1 (by rfl) ⟨474047, by rfl⟩ : syracuseStep 632063 = 948095) B948095
theorem B632127 : Blo 630300 632127 := bstep (se 1 (by rfl) ⟨474095, by rfl⟩ : syracuseStep 632127 = 948191) B948191
theorem B632167 : Blo 630300 632167 := bstep (se 1 (by rfl) ⟨474125, by rfl⟩ : syracuseStep 632167 = 948251) B948251
theorem B2598247 : Blo 630300 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B632295 : Blo 630300 632295 := bstep (se 1 (by rfl) ⟨474221, by rfl⟩ : syracuseStep 632295 = 948443) B948443
theorem B1353199 : Blo 630300 1353199 := bstep (se 1 (by rfl) ⟨1014899, by rfl⟩ : syracuseStep 1353199 = 2029799) B2029799
theorem B632475 : Blo 630300 632475 := bstep (se 1 (by rfl) ⟨474356, by rfl⟩ : syracuseStep 632475 = 948713) B948713
theorem B4564765 : Blo 630300 4564765 := bstep (se 3 (by rfl) ⟨855893, by rfl⟩ : syracuseStep 4564765 = 1711787) B1711787
theorem B632735 : Blo 630300 632735 := bstep (se 1 (by rfl) ⟨474551, by rfl⟩ : syracuseStep 632735 = 949103) B949103
theorem B632895 : Blo 630300 632895 := bstep (se 1 (by rfl) ⟨474671, by rfl⟩ : syracuseStep 632895 = 949343) B949343
theorem B632935 : Blo 630300 632935 := bstep (se 1 (by rfl) ⟨474701, by rfl⟩ : syracuseStep 632935 = 949403) B949403
theorem B9709757 : Blo 630300 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B633039 : Blo 630300 633039 := bstep (se 1 (by rfl) ⟨474779, by rfl⟩ : syracuseStep 633039 = 949559) B949559
theorem B633159 : Blo 630300 633159 := bstep (se 1 (by rfl) ⟨474869, by rfl⟩ : syracuseStep 633159 = 949739) B949739
theorem B633295 : Blo 630300 633295 := bstep (se 1 (by rfl) ⟨474971, by rfl⟩ : syracuseStep 633295 = 949943) B949943
theorem B5417441 : Blo 630300 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B8104475 : Blo 630300 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B633435 : Blo 630300 633435 := bstep (se 1 (by rfl) ⟨475076, by rfl⟩ : syracuseStep 633435 = 950153) B950153
theorem B633599 : Blo 630300 633599 := bstep (se 1 (by rfl) ⟨475199, by rfl⟩ : syracuseStep 633599 = 950399) B950399
theorem B633791 : Blo 630300 633791 := bstep (se 1 (by rfl) ⟨475343, by rfl⟩ : syracuseStep 633791 = 950687) B950687
theorem B633967 : Blo 630300 633967 := bstep (se 1 (by rfl) ⟨475475, by rfl⟩ : syracuseStep 633967 = 950951) B950951
theorem B634047 : Blo 630300 634047 := bstep (se 1 (by rfl) ⟨475535, by rfl⟩ : syracuseStep 634047 = 951071) B951071
theorem B634063 : Blo 630300 634063 := bstep (se 1 (by rfl) ⟨475547, by rfl⟩ : syracuseStep 634063 = 951095) B951095
theorem B634183 : Blo 630300 634183 := bstep (se 1 (by rfl) ⟨475637, by rfl⟩ : syracuseStep 634183 = 951275) B951275
theorem B1420775 : Blo 630300 1420775 := bstep (se 1 (by rfl) ⟨1065581, by rfl⟩ : syracuseStep 1420775 = 2131163) B2131163
theorem B798427 : Blo 630300 798427 := bstep (se 1 (by rfl) ⟨598820, by rfl⟩ : syracuseStep 798427 = 1197641) B1197641
theorem B1421135 : Blo 630300 1421135 := bstep (se 1 (by rfl) ⟨1065851, by rfl⟩ : syracuseStep 1421135 = 2131703) B2131703
theorem B13643963 : Blo 630300 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B168112417 : Blo 630300 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B7778749 : Blo 630300 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B1421855 : Blo 630300 1421855 := bstep (se 1 (by rfl) ⟨1066391, by rfl⟩ : syracuseStep 1421855 = 2132783) B2132783
theorem B4862521 : Blo 630300 4862521 := bstep (se 2 (by rfl) ⟨1823445, by rfl⟩ : syracuseStep 4862521 = 3646891) B3646891
theorem B19510159 : Blo 630300 19510159 := bstep (se 1 (by rfl) ⟨14632619, by rfl⟩ : syracuseStep 19510159 = 29265239) B29265239
theorem B1422503 : Blo 630300 1422503 := bstep (se 1 (by rfl) ⟨1066877, by rfl⟩ : syracuseStep 1422503 = 2133755) B2133755
theorem B1422827 : Blo 630300 1422827 := bstep (se 1 (by rfl) ⟨1067120, by rfl⟩ : syracuseStep 1422827 = 2134241) B2134241
theorem B6829591 : Blo 630300 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B3192371 : Blo 630300 3192371 := bstep (se 1 (by rfl) ⟨2394278, by rfl⟩ : syracuseStep 3192371 = 4788557) B4788557
theorem B7321295 : Blo 630300 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B3422411 : Blo 630300 3422411 := bstep (se 1 (by rfl) ⟨2566808, by rfl⟩ : syracuseStep 3422411 = 5133617) B5133617
theorem B1423673 : Blo 630300 1423673 := bstep (se 2 (by rfl) ⟨533877, by rfl⟩ : syracuseStep 1423673 = 1067755) B1067755
theorem B1424969 : Blo 630300 1424969 := bstep (se 2 (by rfl) ⟨534363, by rfl⟩ : syracuseStep 1424969 = 1068727) B1068727
theorem B3031415 : Blo 630300 3031415 := bstep (se 1 (by rfl) ⟨2273561, by rfl⟩ : syracuseStep 3031415 = 4547123) B4547123
theorem B1425977 : Blo 630300 1425977 := bstep (se 2 (by rfl) ⟨534741, by rfl⟩ : syracuseStep 1425977 = 1069483) B1069483
theorem B1065865 : Blo 630300 1065865 := bstep (se 2 (by rfl) ⟨399699, by rfl⟩ : syracuseStep 1065865 = 799399) B799399
theorem B1426697 : Blo 630300 1426697 := bstep (se 2 (by rfl) ⟨535011, by rfl⟩ : syracuseStep 1426697 = 1070023) B1070023
theorem B1951001 : Blo 630300 1951001 := bstep (se 2 (by rfl) ⟨731625, by rfl⟩ : syracuseStep 1951001 = 1463251) B1463251
theorem B1066297 : Blo 630300 1066297 := bstep (se 2 (by rfl) ⟨399861, by rfl⟩ : syracuseStep 1066297 = 799723) B799723
theorem B22136609 : Blo 630300 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B1198127 : Blo 630300 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B1067215 : Blo 630300 1067215 := bstep (se 1 (by rfl) ⟨800411, by rfl⟩ : syracuseStep 1067215 = 1600823) B1600823
theorem B1198567 : Blo 630300 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B5394235 : Blo 630300 5394235 := bstep (se 1 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 5394235 = 8091353) B8091353
theorem B1200071 : Blo 630300 1200071 := bstep (se 1 (by rfl) ⟨900053, by rfl⟩ : syracuseStep 1200071 = 1800107) B1800107
theorem B2707901 : Blo 630300 2707901 := bstep (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) B1015463
theorem B3592673 : Blo 630300 3592673 := bstep (se 2 (by rfl) ⟨1347252, by rfl⟩ : syracuseStep 3592673 = 2694505) B2694505
theorem B1069679 : Blo 630300 1069679 := bstep (se 1 (by rfl) ⟨802259, by rfl⟩ : syracuseStep 1069679 = 1604519) B1604519
theorem B709339 : Blo 630300 709339 := bstep (se 1 (by rfl) ⟨532004, by rfl⟩ : syracuseStep 709339 = 1064009) B1064009
theorem B709735 : Blo 630300 709735 := bstep (se 1 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 709735 = 1064603) B1064603
theorem B3593423 : Blo 630300 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B4117711 : Blo 630300 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B6084355 : Blo 630300 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B4675367 : Blo 630300 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B3200957 : Blo 630300 3200957 := bstep (se 3 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 3200957 = 1200359) B1200359
theorem B6936673 : Blo 630300 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B1202303 : Blo 630300 1202303 := bstep (se 1 (by rfl) ⟨901727, by rfl⟩ : syracuseStep 1202303 = 1803455) B1803455
theorem B1137343 : Blo 630300 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B8641403 : Blo 630300 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B8019121 : Blo 630300 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B3203063 : Blo 630300 3203063 := bstep (se 1 (by rfl) ⟨2402297, by rfl⟩ : syracuseStep 3203063 = 4804595) B4804595
theorem B9232993 : Blo 630300 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B1598575 : Blo 630300 1598575 := bstep (se 1 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 1598575 = 2397863) B2397863
theorem B3204521 : Blo 630300 3204521 := bstep (se 2 (by rfl) ⟨1201695, by rfl⟩ : syracuseStep 3204521 = 2403391) B2403391
theorem B3597979 : Blo 630300 3597979 := bstep (se 1 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 3597979 = 5396969) B5396969
theorem B2058335 : Blo 630300 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B1599983 : Blo 630300 1599983 := bstep (se 1 (by rfl) ⟨1199987, by rfl⟩ : syracuseStep 1599983 = 2399975) B2399975
theorem B1010599 : Blo 630300 1010599 := bstep (se 1 (by rfl) ⟨757949, by rfl⟩ : syracuseStep 1010599 = 1515899) B1515899
theorem B945455 : Blo 630300 945455 := bstep (se 1 (by rfl) ⟨709091, by rfl⟩ : syracuseStep 945455 = 1418183) B1418183
theorem B1043803 : Blo 630300 1043803 := bstep (se 1 (by rfl) ⟨782852, by rfl⟩ : syracuseStep 1043803 = 1565705) B1565705
theorem B945641 : Blo 630300 945641 := bstep (se 2 (by rfl) ⟨354615, by rfl⟩ : syracuseStep 945641 = 709231) B709231
theorem B945695 : Blo 630300 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B3043007 : Blo 630300 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B3206951 : Blo 630300 3206951 := bstep (se 1 (by rfl) ⟨2405213, by rfl⟩ : syracuseStep 3206951 = 4810427) B4810427
theorem B1601491 : Blo 630300 1601491 := bstep (se 1 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 1601491 = 2402237) B2402237
theorem B2158807 : Blo 630300 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B1798375 : Blo 630300 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B18182717 : Blo 630300 18182717 := bstep (se 3 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 18182717 = 6818519) B6818519
theorem B2028169 : Blo 630300 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B5141303 : Blo 630300 5141303 := bstep (se 1 (by rfl) ⟨3855977, by rfl⟩ : syracuseStep 5141303 = 7711955) B7711955
theorem B3044407 : Blo 630300 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B947327 : Blo 630300 947327 := bstep (se 1 (by rfl) ⟨710495, by rfl⟩ : syracuseStep 947327 = 1420991) B1420991
theorem B14054573 : Blo 630300 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B947711 : Blo 630300 947711 := bstep (se 1 (by rfl) ⟨710783, by rfl⟩ : syracuseStep 947711 = 1421567) B1421567
theorem B2127599 : Blo 630300 2127599 := bstep (se 1 (by rfl) ⟨1595699, by rfl⟩ : syracuseStep 2127599 = 3191399) B3191399
theorem B3209057 : Blo 630300 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B948089 : Blo 630300 948089 := bstep (se 2 (by rfl) ⟨355533, by rfl⟩ : syracuseStep 948089 = 711067) B711067
theorem B948479 : Blo 630300 948479 := bstep (se 1 (by rfl) ⟨711359, by rfl⟩ : syracuseStep 948479 = 1422719) B1422719
theorem B1603871 : Blo 630300 1603871 := bstep (se 1 (by rfl) ⟨1202903, by rfl⟩ : syracuseStep 1603871 = 2405807) B2405807
theorem B5404967 : Blo 630300 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B948617 : Blo 630300 948617 := bstep (se 2 (by rfl) ⟨355731, by rfl⟩ : syracuseStep 948617 = 711463) B711463
theorem B1604063 : Blo 630300 1604063 := bstep (se 1 (by rfl) ⟨1203047, by rfl⟩ : syracuseStep 1604063 = 2406095) B2406095
theorem B948791 : Blo 630300 948791 := bstep (se 1 (by rfl) ⟨711593, by rfl⟩ : syracuseStep 948791 = 1423187) B1423187
theorem B41613929 : Blo 630300 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B948863 : Blo 630300 948863 := bstep (se 1 (by rfl) ⟨711647, by rfl⟩ : syracuseStep 948863 = 1423295) B1423295
theorem B1604407 : Blo 630300 1604407 := bstep (se 1 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 1604407 = 2406611) B2406611
theorem B4815773 : Blo 630300 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B949241 : Blo 630300 949241 := bstep (se 2 (by rfl) ⟨355965, by rfl⟩ : syracuseStep 949241 = 711931) B711931
theorem B4553927 : Blo 630300 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B133267031 : Blo 630300 133267031 := bstep (se 1 (by rfl) ⟨99950273, by rfl⟩ : syracuseStep 133267031 = 199900547) B199900547
theorem B8781455 : Blo 630300 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B332103401 : Blo 630300 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B950249 : Blo 630300 950249 := bstep (se 2 (by rfl) ⟨356343, by rfl⟩ : syracuseStep 950249 = 712687) B712687
theorem B950267 : Blo 630300 950267 := bstep (se 1 (by rfl) ⟨712700, by rfl⟩ : syracuseStep 950267 = 1425401) B1425401
theorem B950651 : Blo 630300 950651 := bstep (se 1 (by rfl) ⟨712988, by rfl⟩ : syracuseStep 950651 = 1425977) B1425977
theorem B951131 : Blo 630300 951131 := bstep (se 1 (by rfl) ⟨713348, by rfl⟩ : syracuseStep 951131 = 1426697) B1426697
theorem B2131433 : Blo 630300 2131433 := bstep (se 2 (by rfl) ⟨799287, by rfl⟩ : syracuseStep 2131433 = 1598575) B1598575
theorem B3606227 : Blo 630300 3606227 := bstep (se 1 (by rfl) ⟨2704670, by rfl⟩ : syracuseStep 3606227 = 5409341) B5409341
theorem B1804265 : Blo 630300 1804265 := bstep (se 2 (by rfl) ⟨676599, by rfl⟩ : syracuseStep 1804265 = 1353199) B1353199
theorem B3410255 : Blo 630300 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B1805267 : Blo 630300 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B2395115 : Blo 630300 2395115 := bstep (se 1 (by rfl) ⟨1796336, by rfl⟩ : syracuseStep 2395115 = 3592673) B3592673
theorem B10816901 : Blo 630300 10816901 := bstep (se 4 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 10816901 = 2028169) B2028169
theorem B3608003 : Blo 630300 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B2395615 : Blo 630300 2395615 := bstep (se 1 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 2395615 = 3593423) B3593423
theorem B3116911 : Blo 630300 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B3608459 : Blo 630300 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B2133971 : Blo 630300 2133971 := bstep (se 1 (by rfl) ⟨1600478, by rfl⟩ : syracuseStep 2133971 = 3200957) B3200957
theorem B1708457 : Blo 630300 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B2135321 : Blo 630300 2135321 := bstep (se 2 (by rfl) ⟨800745, by rfl⟩ : syracuseStep 2135321 = 1601491) B1601491
theorem B2135375 : Blo 630300 2135375 := bstep (se 1 (by rfl) ⟨1601531, by rfl⟩ : syracuseStep 2135375 = 3203063) B3203063
theorem B2397833 : Blo 630300 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B2136347 : Blo 630300 2136347 := bstep (se 1 (by rfl) ⟨1602260, by rfl⟩ : syracuseStep 2136347 = 3204521) B3204521
theorem B3611627 : Blo 630300 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B630303 : Blo 630300 630303 := bstep (se 1 (by rfl) ⟨472727, by rfl⟩ : syracuseStep 630303 = 945455) B945455
theorem B630427 : Blo 630300 630427 := bstep (se 1 (by rfl) ⟨472820, by rfl⟩ : syracuseStep 630427 = 945641) B945641
theorem B630463 : Blo 630300 630463 := bstep (se 1 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 630463 = 945695) B945695
theorem B2137967 : Blo 630300 2137967 := bstep (se 1 (by rfl) ⟨1603475, by rfl⟩ : syracuseStep 2137967 = 3206951) B3206951
theorem B9248897 : Blo 630300 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B631551 : Blo 630300 631551 := bstep (se 1 (by rfl) ⟨473663, by rfl⟩ : syracuseStep 631551 = 947327) B947327
theorem B1516457 : Blo 630300 1516457 := bstep (se 2 (by rfl) ⟨568671, by rfl⟩ : syracuseStep 1516457 = 1137343) B1137343
theorem B631807 : Blo 630300 631807 := bstep (se 1 (by rfl) ⟨473855, by rfl⟩ : syracuseStep 631807 = 947711) B947711
theorem B2139209 : Blo 630300 2139209 := bstep (se 2 (by rfl) ⟨802203, by rfl⟩ : syracuseStep 2139209 = 1604407) B1604407
theorem B1418399 : Blo 630300 1418399 := bstep (se 1 (by rfl) ⟨1063799, by rfl⟩ : syracuseStep 1418399 = 2127599) B2127599
theorem B2139371 : Blo 630300 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B632059 : Blo 630300 632059 := bstep (se 1 (by rfl) ⟨474044, by rfl⟩ : syracuseStep 632059 = 948089) B948089
theorem B632319 : Blo 630300 632319 := bstep (se 1 (by rfl) ⟨474239, by rfl⟩ : syracuseStep 632319 = 948479) B948479
theorem B10692161 : Blo 630300 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B632411 : Blo 630300 632411 := bstep (se 1 (by rfl) ⟨474308, by rfl⟩ : syracuseStep 632411 = 948617) B948617
theorem B632527 : Blo 630300 632527 := bstep (se 1 (by rfl) ⟨474395, by rfl⟩ : syracuseStep 632527 = 948791) B948791
theorem B632575 : Blo 630300 632575 := bstep (se 1 (by rfl) ⟨474431, by rfl⟩ : syracuseStep 632575 = 948863) B948863
theorem B632827 : Blo 630300 632827 := bstep (se 1 (by rfl) ⟨474620, by rfl⟩ : syracuseStep 632827 = 949241) B949241
theorem B88844687 : Blo 630300 88844687 := bstep (se 1 (by rfl) ⟨66633515, by rfl⟩ : syracuseStep 88844687 = 133267031) B133267031
theorem B633499 : Blo 630300 633499 := bstep (se 1 (by rfl) ⟨475124, by rfl⟩ : syracuseStep 633499 = 950249) B950249
theorem B633511 : Blo 630300 633511 := bstep (se 1 (by rfl) ⟨475133, by rfl⟩ : syracuseStep 633511 = 950267) B950267
theorem B1419983 : Blo 630300 1419983 := bstep (se 1 (by rfl) ⟨1064987, by rfl⟩ : syracuseStep 1419983 = 2129975) B2129975
theorem B633551 : Blo 630300 633551 := bstep (se 1 (by rfl) ⟨475163, by rfl⟩ : syracuseStep 633551 = 950327) B950327
theorem B633575 : Blo 630300 633575 := bstep (se 1 (by rfl) ⟨475181, by rfl⟩ : syracuseStep 633575 = 950363) B950363
theorem B633631 : Blo 630300 633631 := bstep (se 1 (by rfl) ⟨475223, by rfl⟩ : syracuseStep 633631 = 950447) B950447
theorem B1420343 : Blo 630300 1420343 := bstep (se 1 (by rfl) ⟨1065257, by rfl⟩ : syracuseStep 1420343 = 2130515) B2130515
theorem B634023 : Blo 630300 634023 := bstep (se 1 (by rfl) ⟨475517, by rfl⟩ : syracuseStep 634023 = 951035) B951035
theorem B634111 : Blo 630300 634111 := bstep (se 1 (by rfl) ⟨475583, by rfl⟩ : syracuseStep 634111 = 951167) B951167
theorem B69054115 : Blo 630300 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B1421153 : Blo 630300 1421153 := bstep (se 2 (by rfl) ⟨532932, by rfl⟩ : syracuseStep 1421153 = 1065865) B1065865
theorem B798751 : Blo 630300 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B92287025 : Blo 630300 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B1421729 : Blo 630300 1421729 := bstep (se 2 (by rfl) ⟨533148, by rfl⟩ : syracuseStep 1421729 = 1066297) B1066297
theorem B3191561 : Blo 630300 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B4797305 : Blo 630300 4797305 := bstep (se 2 (by rfl) ⟨1798989, by rfl⟩ : syracuseStep 4797305 = 3597979) B3597979
theorem B800047 : Blo 630300 800047 := bstep (se 1 (by rfl) ⟨600035, by rfl⟩ : syracuseStep 800047 = 1200071) B1200071
theorem B1422953 : Blo 630300 1422953 := bstep (se 2 (by rfl) ⟨533607, by rfl⟩ : syracuseStep 1422953 = 1067215) B1067215
theorem B1423079 : Blo 630300 1423079 := bstep (se 1 (by rfl) ⟨1067309, by rfl⟩ : syracuseStep 1423079 = 2134619) B2134619
theorem B1391737 : Blo 630300 1391737 := bstep (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) B1043803
theorem B59030957 : Blo 630300 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B5389861 : Blo 630300 5389861 := bstep (se 4 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 5389861 = 1010599) B1010599
theorem B1064569 : Blo 630300 1064569 := bstep (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) B798427
theorem B7192313 : Blo 630300 7192313 := bstep (se 2 (by rfl) ⟨2697117, by rfl⟩ : syracuseStep 7192313 = 5394235) B5394235
theorem B224149889 : Blo 630300 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B1425887 : Blo 630300 1425887 := bstep (se 1 (by rfl) ⟨1069415, by rfl⟩ : syracuseStep 1425887 = 2138831) B2138831
theorem B10371665 : Blo 630300 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B12173935 : Blo 630300 12173935 := bstep (se 1 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 12173935 = 18260903) B18260903
theorem B3195611 : Blo 630300 3195611 := bstep (se 1 (by rfl) ⟨2396708, by rfl⟩ : syracuseStep 3195611 = 4793417) B4793417
theorem B6473171 : Blo 630300 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B5490281 : Blo 630300 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B1066655 : Blo 630300 1066655 := bstep (se 1 (by rfl) ⟨799991, by rfl⟩ : syracuseStep 1066655 = 1599983) B1599983
theorem B29280001 : Blo 630300 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B8112473 : Blo 630300 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B9095975 : Blo 630300 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B3427535 : Blo 630300 3427535 := bstep (se 1 (by rfl) ⟨2570651, by rfl⟩ : syracuseStep 3427535 = 5141303) B5141303
theorem B3198689 : Blo 630300 3198689 := bstep (se 2 (by rfl) ⟨1199508, by rfl⟩ : syracuseStep 3198689 = 2399017) B2399017
theorem B3591965 : Blo 630300 3591965 := bstep (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) B1346987
theorem B2281607 : Blo 630300 2281607 := bstep (se 1 (by rfl) ⟨1711205, by rfl⟩ : syracuseStep 2281607 = 3422411) B3422411
theorem B1069247 : Blo 630300 1069247 := bstep (se 1 (by rfl) ⟨801935, by rfl⟩ : syracuseStep 1069247 = 1603871) B1603871
theorem B1069375 : Blo 630300 1069375 := bstep (se 1 (by rfl) ⟨802031, by rfl⟩ : syracuseStep 1069375 = 1604063) B1604063
theorem B27742619 : Blo 630300 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B3035951 : Blo 630300 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B2020265 : Blo 630300 2020265 := bstep (se 2 (by rfl) ⟨757599, by rfl⟩ : syracuseStep 2020265 = 1515199) B1515199
theorem B5854303 : Blo 630300 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B221402267 : Blo 630300 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B2020943 : Blo 630300 2020943 := bstep (se 1 (by rfl) ⟨1515707, by rfl⟩ : syracuseStep 2020943 = 3031415) B3031415
theorem B1300667 : Blo 630300 1300667 := bstep (se 1 (by rfl) ⟨975500, by rfl⟩ : syracuseStep 1300667 = 1951001) B1951001
theorem B3594881 : Blo 630300 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B1596095 : Blo 630300 1596095 := bstep (se 1 (by rfl) ⟨1197071, by rfl⟩ : syracuseStep 1596095 = 2394143) B2394143
theorem B24665107 : Blo 630300 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B3464329 : Blo 630300 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B1203815 : Blo 630300 1203815 := bstep (se 1 (by rfl) ⟨902861, by rfl⟩ : syracuseStep 1203815 = 1805723) B1805723
theorem B6086353 : Blo 630300 6086353 := bstep (se 2 (by rfl) ⟨2282382, by rfl⟩ : syracuseStep 6086353 = 4564765) B4564765
theorem B74866751 : Blo 630300 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B1597715 : Blo 630300 1597715 := bstep (se 1 (by rfl) ⟨1198286, by rfl⟩ : syracuseStep 1597715 = 2396573) B2396573
theorem B713119 : Blo 630300 713119 := bstep (se 1 (by rfl) ⟨534839, by rfl⟩ : syracuseStep 713119 = 1069679) B1069679
theorem B37478861 : Blo 630300 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B49242629 : Blo 630300 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B2777723 : Blo 630300 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B1598089 : Blo 630300 1598089 := bstep (se 2 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 1598089 = 1198567) B1198567
theorem B47539061 : Blo 630300 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B1598687 : Blo 630300 1598687 := bstep (se 1 (by rfl) ⟨1199015, by rfl⟩ : syracuseStep 1598687 = 2398031) B2398031
theorem B5760935 : Blo 630300 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B1599527 : Blo 630300 1599527 := bstep (se 1 (by rfl) ⟨1199645, by rfl⟩ : syracuseStep 1599527 = 2399291) B2399291
theorem B1140961 : Blo 630300 1140961 := bstep (se 2 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 1140961 = 855721) B855721
theorem B2878409 : Blo 630300 2878409 := bstep (se 2 (by rfl) ⟨1079403, by rfl⟩ : syracuseStep 2878409 = 2158807) B2158807
theorem B3206141 : Blo 630300 3206141 := bstep (se 3 (by rfl) ⟨601151, by rfl⟩ : syracuseStep 3206141 = 1202303) B1202303
theorem B6483361 : Blo 630300 6483361 := bstep (se 2 (by rfl) ⟨2431260, by rfl⟩ : syracuseStep 6483361 = 4862521) B4862521
theorem B945785 : Blo 630300 945785 := bstep (se 2 (by rfl) ⟨354669, by rfl⟩ : syracuseStep 945785 = 709339) B709339
theorem B26013545 : Blo 630300 26013545 := bstep (se 2 (by rfl) ⟨9755079, by rfl⟩ : syracuseStep 26013545 = 19510159) B19510159
theorem B1372223 : Blo 630300 1372223 := bstep (se 1 (by rfl) ⟨1029167, by rfl⟩ : syracuseStep 1372223 = 2058335) B2058335
theorem B4059209 : Blo 630300 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B946313 : Blo 630300 946313 := bstep (se 2 (by rfl) ⟨354867, by rfl⟩ : syracuseStep 946313 = 709735) B709735
theorem B5402983 : Blo 630300 5402983 := bstep (se 1 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 5402983 = 8104475) B8104475
theorem B9106121 : Blo 630300 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B947183 : Blo 630300 947183 := bstep (se 1 (by rfl) ⟨710387, by rfl⟩ : syracuseStep 947183 = 1420775) B1420775
theorem B2028671 : Blo 630300 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B947423 : Blo 630300 947423 := bstep (se 1 (by rfl) ⟨710567, by rfl⟩ : syracuseStep 947423 = 1421135) B1421135
theorem B947903 : Blo 630300 947903 := bstep (se 1 (by rfl) ⟨710927, by rfl⟩ : syracuseStep 947903 = 1421855) B1421855
theorem B12121811 : Blo 630300 12121811 := bstep (se 1 (by rfl) ⟨9091358, by rfl⟩ : syracuseStep 12121811 = 18182717) B18182717
theorem B948335 : Blo 630300 948335 := bstep (se 1 (by rfl) ⟨711251, by rfl⟩ : syracuseStep 948335 = 1422503) B1422503
theorem B948551 : Blo 630300 948551 := bstep (se 1 (by rfl) ⟨711413, by rfl⟩ : syracuseStep 948551 = 1422827) B1422827
theorem B2128247 : Blo 630300 2128247 := bstep (se 1 (by rfl) ⟨1596185, by rfl⟩ : syracuseStep 2128247 = 3192371) B3192371
theorem B4880863 : Blo 630300 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B3603311 : Blo 630300 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B949115 : Blo 630300 949115 := bstep (se 1 (by rfl) ⟨711836, by rfl⟩ : syracuseStep 949115 = 1423673) B1423673
theorem B3210515 : Blo 630300 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B949979 : Blo 630300 949979 := bstep (se 1 (by rfl) ⟨712484, by rfl⟩ : syracuseStep 949979 = 1424969) B1424969
theorem B950591 : Blo 630300 950591 := bstep (se 1 (by rfl) ⟨712943, by rfl⟩ : syracuseStep 950591 = 1425887) B1425887
theorem B6914443 : Blo 630300 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B2130407 : Blo 630300 2130407 := bstep (se 1 (by rfl) ⟨1597805, by rfl⟩ : syracuseStep 2130407 = 3195611) B3195611
theorem B950825 : Blo 630300 950825 := bstep (se 2 (by rfl) ⟨356559, by rfl⟩ : syracuseStep 950825 = 713119) B713119
theorem B2130785 : Blo 630300 2130785 := bstep (se 2 (by rfl) ⟨799044, by rfl⟩ : syracuseStep 2130785 = 1598089) B1598089
theorem B5408315 : Blo 630300 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B6063983 : Blo 630300 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B7211267 : Blo 630300 7211267 := bstep (se 1 (by rfl) ⟨5408450, by rfl⟩ : syracuseStep 7211267 = 10816901) B10816901
theorem B2132459 : Blo 630300 2132459 := bstep (se 1 (by rfl) ⟨1599344, by rfl⟩ : syracuseStep 2132459 = 3198689) B3198689
theorem B2394643 : Blo 630300 2394643 := bstep (se 1 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 2394643 = 3591965) B3591965
theorem B1346843 : Blo 630300 1346843 := bstep (se 1 (by rfl) ⟨1010132, by rfl⟩ : syracuseStep 1346843 = 2020265) B2020265
theorem B1347295 : Blo 630300 1347295 := bstep (se 1 (by rfl) ⟨1010471, by rfl⟩ : syracuseStep 1347295 = 2020943) B2020943
theorem B2396587 : Blo 630300 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B18223541 : Blo 630300 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B49911167 : Blo 630300 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B6165931 : Blo 630300 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B31692707 : Blo 630300 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B3840623 : Blo 630300 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B7805737 : Blo 630300 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B2137427 : Blo 630300 2137427 := bstep (se 1 (by rfl) ⟨1603070, by rfl⟩ : syracuseStep 2137427 = 3206141) B3206141
theorem B630523 : Blo 630300 630523 := bstep (se 1 (by rfl) ⟨472892, by rfl⟩ : syracuseStep 630523 = 945785) B945785
theorem B17342363 : Blo 630300 17342363 := bstep (se 1 (by rfl) ⟨13006772, by rfl⟩ : syracuseStep 17342363 = 26013545) B26013545
theorem B630875 : Blo 630300 630875 := bstep (se 1 (by rfl) ⟨473156, by rfl⟩ : syracuseStep 630875 = 946313) B946313
theorem B6070747 : Blo 630300 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B631455 : Blo 630300 631455 := bstep (se 1 (by rfl) ⟨473591, by rfl⟩ : syracuseStep 631455 = 947183) B947183
theorem B1352447 : Blo 630300 1352447 := bstep (se 1 (by rfl) ⟨1014335, by rfl⟩ : syracuseStep 1352447 = 2028671) B2028671
theorem B631615 : Blo 630300 631615 := bstep (se 1 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 631615 = 947423) B947423
theorem B631935 : Blo 630300 631935 := bstep (se 1 (by rfl) ⟨473951, by rfl⟩ : syracuseStep 631935 = 947903) B947903
theorem B632223 : Blo 630300 632223 := bstep (se 1 (by rfl) ⟨474167, by rfl⟩ : syracuseStep 632223 = 948335) B948335
theorem B632367 : Blo 630300 632367 := bstep (se 1 (by rfl) ⟨474275, by rfl⟩ : syracuseStep 632367 = 948551) B948551
theorem B1418831 : Blo 630300 1418831 := bstep (se 1 (by rfl) ⟨1064123, by rfl⟩ : syracuseStep 1418831 = 2128247) B2128247
theorem B2402207 : Blo 630300 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B632743 : Blo 630300 632743 := bstep (se 1 (by rfl) ⟨474557, by rfl⟩ : syracuseStep 632743 = 949115) B949115
theorem B7186481 : Blo 630300 7186481 := bstep (se 2 (by rfl) ⟨2694930, by rfl⟩ : syracuseStep 7186481 = 5389861) B5389861
theorem B1419425 : Blo 630300 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B2140343 : Blo 630300 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B633319 : Blo 630300 633319 := bstep (se 1 (by rfl) ⟨474989, by rfl⟩ : syracuseStep 633319 = 949979) B949979
theorem B4794875 : Blo 630300 4794875 := bstep (se 1 (by rfl) ⟨3596156, by rfl⟩ : syracuseStep 4794875 = 7192313) B7192313
theorem B633767 : Blo 630300 633767 := bstep (se 1 (by rfl) ⟨475325, by rfl⟩ : syracuseStep 633767 = 950651) B950651
theorem B634087 : Blo 630300 634087 := bstep (se 1 (by rfl) ⟨475565, by rfl⟩ : syracuseStep 634087 = 951131) B951131
theorem B16231913 : Blo 630300 16231913 := bstep (se 2 (by rfl) ⟨6086967, by rfl⟩ : syracuseStep 16231913 = 12173935) B12173935
theorem B1420955 : Blo 630300 1420955 := bstep (se 1 (by rfl) ⟨1065716, by rfl⟩ : syracuseStep 1420955 = 2131433) B2131433
theorem B597733037 : Blo 630300 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B2404151 : Blo 630300 2404151 := bstep (se 1 (by rfl) ⟨1803113, by rfl⟩ : syracuseStep 2404151 = 3606227) B3606227
theorem B2273503 : Blo 630300 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B13873781 : Blo 630300 13873781 := bstep (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) B1300667
theorem B2405335 : Blo 630300 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B39040001 : Blo 630300 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B26031269 : Blo 630300 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B2405639 : Blo 630300 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B1422647 : Blo 630300 1422647 := bstep (se 1 (by rfl) ⟨1066985, by rfl⟩ : syracuseStep 1422647 = 2133971) B2133971
theorem B1521071 : Blo 630300 1521071 := bstep (se 1 (by rfl) ⟨1140803, by rfl⟩ : syracuseStep 1521071 = 2281607) B2281607
theorem B1521281 : Blo 630300 1521281 := bstep (se 2 (by rfl) ⟨570480, by rfl⟩ : syracuseStep 1521281 = 1140961) B1140961
theorem B147601511 : Blo 630300 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B1423547 : Blo 630300 1423547 := bstep (se 1 (by rfl) ⟨1067660, by rfl⟩ : syracuseStep 1423547 = 2135321) B2135321
theorem B1423583 : Blo 630300 1423583 := bstep (se 1 (by rfl) ⟨1067687, by rfl⟩ : syracuseStep 1423583 = 2135375) B2135375
theorem B1424231 : Blo 630300 1424231 := bstep (se 1 (by rfl) ⟨1068173, by rfl⟩ : syracuseStep 1424231 = 2136347) B2136347
theorem B1064063 : Blo 630300 1064063 := bstep (se 1 (by rfl) ⟨798047, by rfl⟩ : syracuseStep 1064063 = 1596095) B1596095
theorem B3194153 : Blo 630300 3194153 := bstep (se 2 (by rfl) ⟨1197807, by rfl⟩ : syracuseStep 3194153 = 2395615) B2395615
theorem B2407751 : Blo 630300 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B802543 : Blo 630300 802543 := bstep (se 1 (by rfl) ⟨601907, by rfl⟩ : syracuseStep 802543 = 1203815) B1203815
theorem B1425311 : Blo 630300 1425311 := bstep (se 1 (by rfl) ⟨1068983, by rfl⟩ : syracuseStep 1425311 = 2137967) B2137967
theorem B1065001 : Blo 630300 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B1065143 : Blo 630300 1065143 := bstep (se 1 (by rfl) ⟨798857, by rfl⟩ : syracuseStep 1065143 = 1597715) B1597715
theorem B24985907 : Blo 630300 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B1851815 : Blo 630300 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B1425833 : Blo 630300 1425833 := bstep (se 2 (by rfl) ⟨534687, by rfl⟩ : syracuseStep 1425833 = 1069375) B1069375
theorem B1426139 : Blo 630300 1426139 := bstep (se 1 (by rfl) ⟨1069604, by rfl⟩ : syracuseStep 1426139 = 2139209) B2139209
theorem B1065791 : Blo 630300 1065791 := bstep (se 1 (by rfl) ⟨799343, by rfl⟩ : syracuseStep 1065791 = 1598687) B1598687
theorem B1426247 : Blo 630300 1426247 := bstep (se 1 (by rfl) ⟨1069685, by rfl⟩ : syracuseStep 1426247 = 2139371) B2139371
theorem B7128107 : Blo 630300 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B1066351 : Blo 630300 1066351 := bstep (se 1 (by rfl) ⟨799763, by rfl⟩ : syracuseStep 1066351 = 1599527) B1599527
theorem B59229791 : Blo 630300 59229791 := bstep (se 1 (by rfl) ⟨44422343, by rfl⟩ : syracuseStep 59229791 = 88844687) B88844687
theorem B1066729 : Blo 630300 1066729 := bstep (se 2 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 1066729 = 800047) B800047
theorem B1918939 : Blo 630300 1918939 := bstep (se 1 (by rfl) ⟨1439204, by rfl⟩ : syracuseStep 1918939 = 2878409) B2878409
theorem B61524683 : Blo 630300 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B2706139 : Blo 630300 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B3198203 : Blo 630300 3198203 := bstep (se 1 (by rfl) ⟨2398652, by rfl⟩ : syracuseStep 3198203 = 4797305) B4797305
theorem B8081207 : Blo 630300 8081207 := bstep (se 1 (by rfl) ⟨6060905, by rfl⟩ : syracuseStep 8081207 = 12121811) B12121811
theorem B32886809 : Blo 630300 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B1855649 : Blo 630300 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B8115137 : Blo 630300 8115137 := bstep (se 2 (by rfl) ⟨3043176, by rfl⟩ : syracuseStep 8115137 = 6086353) B6086353
theorem B3659261 : Blo 630300 3659261 := bstep (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) B1372223
theorem B4315447 : Blo 630300 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B73980317 : Blo 630300 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B711103 : Blo 630300 711103 := bstep (se 1 (by rfl) ⟨533327, by rfl⟩ : syracuseStep 711103 = 1066655) B1066655
theorem B1202843 : Blo 630300 1202843 := bstep (se 1 (by rfl) ⟨902132, by rfl⟩ : syracuseStep 1202843 = 1804265) B1804265
theorem B1203511 : Blo 630300 1203511 := bstep (se 1 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 1203511 = 1805267) B1805267
theorem B1596743 : Blo 630300 1596743 := bstep (se 1 (by rfl) ⟨1197557, by rfl⟩ : syracuseStep 1596743 = 2395115) B2395115
theorem B2285023 : Blo 630300 2285023 := bstep (se 1 (by rfl) ⟨1713767, by rfl⟩ : syracuseStep 2285023 = 3427535) B3427535
theorem B712831 : Blo 630300 712831 := bstep (se 1 (by rfl) ⟨534623, by rfl⟩ : syracuseStep 712831 = 1069247) B1069247
theorem B2023967 : Blo 630300 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B1598555 : Blo 630300 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B14640749 : Blo 630300 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B8644481 : Blo 630300 8644481 := bstep (se 2 (by rfl) ⟨3241680, by rfl⟩ : syracuseStep 8644481 = 6483361) B6483361
theorem B92072153 : Blo 630300 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B4155881 : Blo 630300 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B32828419 : Blo 630300 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B7203977 : Blo 630300 7203977 := bstep (se 2 (by rfl) ⟨2701491, by rfl⟩ : syracuseStep 7203977 = 5402983) B5402983
theorem B1010971 : Blo 630300 1010971 := bstep (se 1 (by rfl) ⟨758228, by rfl⟩ : syracuseStep 1010971 = 1516457) B1516457
theorem B945599 : Blo 630300 945599 := bstep (se 1 (by rfl) ⟨709199, by rfl⟩ : syracuseStep 945599 = 1418399) B1418399
theorem B946655 : Blo 630300 946655 := bstep (se 1 (by rfl) ⟨709991, by rfl⟩ : syracuseStep 946655 = 1419983) B1419983
theorem B946895 : Blo 630300 946895 := bstep (se 1 (by rfl) ⟨710171, by rfl⟩ : syracuseStep 946895 = 1420343) B1420343
theorem B947435 : Blo 630300 947435 := bstep (se 1 (by rfl) ⟨710576, by rfl⟩ : syracuseStep 947435 = 1421153) B1421153
theorem B947819 : Blo 630300 947819 := bstep (se 1 (by rfl) ⟨710864, by rfl⟩ : syracuseStep 947819 = 1421729) B1421729
theorem B2127707 : Blo 630300 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B948635 : Blo 630300 948635 := bstep (se 1 (by rfl) ⟨711476, by rfl⟩ : syracuseStep 948635 = 1422953) B1422953
theorem B948719 : Blo 630300 948719 := bstep (se 1 (by rfl) ⟨711539, by rfl⟩ : syracuseStep 948719 = 1423079) B1423079
theorem B4619105 : Blo 630300 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B39353971 : Blo 630300 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B950441 : Blo 630300 950441 := bstep (se 2 (by rfl) ⟨356415, by rfl⟩ : syracuseStep 950441 = 712831) B712831
theorem B950555 : Blo 630300 950555 := bstep (se 1 (by rfl) ⟨712916, by rfl⟩ : syracuseStep 950555 = 1425833) B1425833
theorem B4948397 : Blo 630300 4948397 := bstep (se 3 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 4948397 = 1855649) B1855649
theorem B950759 : Blo 630300 950759 := bstep (se 1 (by rfl) ⟨713069, by rfl⟩ : syracuseStep 950759 = 1426139) B1426139
theorem B950831 : Blo 630300 950831 := bstep (se 1 (by rfl) ⟨713123, by rfl⟩ : syracuseStep 950831 = 1426247) B1426247
theorem B8094329 : Blo 630300 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B4752071 : Blo 630300 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B3605543 : Blo 630300 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B39486527 : Blo 630300 39486527 := bstep (se 1 (by rfl) ⟨29614895, by rfl⟩ : syracuseStep 39486527 = 59229791) B59229791
theorem B2132135 : Blo 630300 2132135 := bstep (se 1 (by rfl) ⟨1599101, by rfl⟩ : syracuseStep 2132135 = 3198203) B3198203
theorem B2558585 : Blo 630300 2558585 := bstep (se 2 (by rfl) ⟨959469, by rfl⟩ : syracuseStep 2558585 = 1918939) B1918939
theorem B21924539 : Blo 630300 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B5410091 : Blo 630300 5410091 := bstep (se 1 (by rfl) ⟨4057568, by rfl⟩ : syracuseStep 5410091 = 8115137) B8115137
theorem B3608185 : Blo 630300 3608185 := bstep (se 2 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 3608185 = 2706139) B2706139
theorem B49320211 : Blo 630300 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B2560415 : Blo 630300 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B39032117 : Blo 630300 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B175084901 : Blo 630300 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B1349311 : Blo 630300 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B11082349 : Blo 630300 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B4790987 : Blo 630300 4790987 := bstep (se 1 (by rfl) ⟨3593240, by rfl⟩ : syracuseStep 4790987 = 7186481) B7186481
theorem B61381435 : Blo 630300 61381435 := bstep (se 1 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 61381435 = 92072153) B92072153
theorem B630399 : Blo 630300 630399 := bstep (se 1 (by rfl) ⟨472799, by rfl⟩ : syracuseStep 630399 = 945599) B945599
theorem B10821275 : Blo 630300 10821275 := bstep (se 1 (by rfl) ⟨8115956, by rfl⟩ : syracuseStep 10821275 = 16231913) B16231913
theorem B631103 : Blo 630300 631103 := bstep (se 1 (by rfl) ⟨473327, by rfl⟩ : syracuseStep 631103 = 946655) B946655
theorem B9249187 : Blo 630300 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B631263 : Blo 630300 631263 := bstep (se 1 (by rfl) ⟨473447, by rfl⟩ : syracuseStep 631263 = 946895) B946895
theorem B26026667 : Blo 630300 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B631623 : Blo 630300 631623 := bstep (se 1 (by rfl) ⟨473717, by rfl⟩ : syracuseStep 631623 = 947435) B947435
theorem B631879 : Blo 630300 631879 := bstep (se 1 (by rfl) ⟨473909, by rfl⟩ : syracuseStep 631879 = 947819) B947819
theorem B1418471 : Blo 630300 1418471 := bstep (se 1 (by rfl) ⟨1063853, by rfl⟩ : syracuseStep 1418471 = 2127707) B2127707
theorem B632423 : Blo 630300 632423 := bstep (se 1 (by rfl) ⟨474317, by rfl⟩ : syracuseStep 632423 = 948635) B948635
theorem B632479 : Blo 630300 632479 := bstep (se 1 (by rfl) ⟨474359, by rfl⟩ : syracuseStep 632479 = 948719) B948719
theorem B52471961 : Blo 630300 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B1420001 : Blo 630300 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B16657271 : Blo 630300 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B633727 : Blo 630300 633727 := bstep (se 1 (by rfl) ⟨475295, by rfl⟩ : syracuseStep 633727 = 950591) B950591
theorem B1420271 : Blo 630300 1420271 := bstep (se 1 (by rfl) ⟨1065203, by rfl⟩ : syracuseStep 1420271 = 2130407) B2130407
theorem B633883 : Blo 630300 633883 := bstep (se 1 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 633883 = 950825) B950825
theorem B9219257 : Blo 630300 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B1420523 : Blo 630300 1420523 := bstep (se 1 (by rfl) ⟨1065392, by rfl⟩ : syracuseStep 1420523 = 2130785) B2130785
theorem B4042655 : Blo 630300 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B1421639 : Blo 630300 1421639 := bstep (se 1 (by rfl) ⟨1066229, by rfl⟩ : syracuseStep 1421639 = 2132459) B2132459
theorem B1421801 : Blo 630300 1421801 := bstep (se 2 (by rfl) ⟨533175, by rfl⟩ : syracuseStep 1421801 = 1066351) B1066351
theorem B897895 : Blo 630300 897895 := bstep (se 1 (by rfl) ⟨673421, by rfl⟩ : syracuseStep 897895 = 1346843) B1346843
theorem B1422305 : Blo 630300 1422305 := bstep (se 2 (by rfl) ⟨533364, by rfl⟩ : syracuseStep 1422305 = 1066729) B1066729
theorem B5387471 : Blo 630300 5387471 := bstep (se 1 (by rfl) ⟨4040603, by rfl⟩ : syracuseStep 5387471 = 8081207) B8081207
theorem B3192857 : Blo 630300 3192857 := bstep (se 2 (by rfl) ⟨1197321, by rfl⟩ : syracuseStep 3192857 = 2394643) B2394643
theorem B33274111 : Blo 630300 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B801895 : Blo 630300 801895 := bstep (se 1 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 801895 = 1202843) B1202843
theorem B1064495 : Blo 630300 1064495 := bstep (se 1 (by rfl) ⟨798371, by rfl⟩ : syracuseStep 1064495 = 1596743) B1596743
theorem B1424951 : Blo 630300 1424951 := bstep (se 1 (by rfl) ⟨1068713, by rfl⟩ : syracuseStep 1424951 = 2137427) B2137427
theorem B3031337 : Blo 630300 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B901631 : Blo 630300 901631 := bstep (se 1 (by rfl) ⟨676223, by rfl⟩ : syracuseStep 901631 = 1352447) B1352447
theorem B3195449 : Blo 630300 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B1065703 : Blo 630300 1065703 := bstep (se 1 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 1065703 = 1598555) B1598555
theorem B1426895 : Blo 630300 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B5391845 : Blo 630300 5391845 := bstep (se 4 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 5391845 = 1010971) B1010971
theorem B3196583 : Blo 630300 3196583 := bstep (se 1 (by rfl) ⟨2397437, by rfl⟩ : syracuseStep 3196583 = 4794875) B4794875
theorem B4802651 : Blo 630300 4802651 := bstep (se 1 (by rfl) ⟨3601988, by rfl⟩ : syracuseStep 4802651 = 7203977) B7203977
theorem B5753929 : Blo 630300 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B17354179 : Blo 630300 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B10407649 : Blo 630300 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B709375 : Blo 630300 709375 := bstep (se 1 (by rfl) ⟨532031, by rfl⟩ : syracuseStep 709375 = 1064063) B1064063
theorem B1070057 : Blo 630300 1070057 := bstep (se 2 (by rfl) ⟨401271, by rfl⟩ : syracuseStep 1070057 = 802543) B802543
theorem B710095 : Blo 630300 710095 := bstep (se 1 (by rfl) ⟨532571, by rfl⟩ : syracuseStep 710095 = 1065143) B1065143
theorem B1234543 : Blo 630300 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B710527 : Blo 630300 710527 := bstep (se 1 (by rfl) ⟨532895, by rfl⟩ : syracuseStep 710527 = 1065791) B1065791
theorem B4807511 : Blo 630300 4807511 := bstep (se 1 (by rfl) ⟨3605633, by rfl⟩ : syracuseStep 4807511 = 7211267) B7211267
theorem B41016455 : Blo 630300 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B12149027 : Blo 630300 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B21128471 : Blo 630300 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B4056749 : Blo 630300 4056749 := bstep (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) B1521281
theorem B1796393 : Blo 630300 1796393 := bstep (se 2 (by rfl) ⟨673647, by rfl⟩ : syracuseStep 1796393 = 1347295) B1347295
theorem B11561575 : Blo 630300 11561575 := bstep (se 1 (by rfl) ⟨8671181, by rfl⟩ : syracuseStep 11561575 = 17342363) B17342363
theorem B945887 : Blo 630300 945887 := bstep (se 1 (by rfl) ⟨709415, by rfl⟩ : syracuseStep 945887 = 1418831) B1418831
theorem B9760499 : Blo 630300 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B5762987 : Blo 630300 5762987 := bstep (se 1 (by rfl) ⟨4322240, by rfl⟩ : syracuseStep 5762987 = 8644481) B8644481
theorem B1601471 : Blo 630300 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B3207113 : Blo 630300 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B946283 : Blo 630300 946283 := bstep (se 1 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 946283 = 1419425) B1419425
theorem B8221241 : Blo 630300 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B947303 : Blo 630300 947303 := bstep (se 1 (by rfl) ⟨710477, by rfl⟩ : syracuseStep 947303 = 1420955) B1420955
theorem B398488691 : Blo 630300 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B1602767 : Blo 630300 1602767 := bstep (se 1 (by rfl) ⟨1202075, by rfl⟩ : syracuseStep 1602767 = 2404151) B2404151
theorem B948137 : Blo 630300 948137 := bstep (se 2 (by rfl) ⟨355551, by rfl⟩ : syracuseStep 948137 = 711103) B711103
theorem B1603759 : Blo 630300 1603759 := bstep (se 1 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 1603759 = 2405639) B2405639
theorem B948431 : Blo 630300 948431 := bstep (se 1 (by rfl) ⟨711323, by rfl⟩ : syracuseStep 948431 = 1422647) B1422647
theorem B1014047 : Blo 630300 1014047 := bstep (se 1 (by rfl) ⟨760535, by rfl⟩ : syracuseStep 1014047 = 1521071) B1521071
theorem B98401007 : Blo 630300 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B949031 : Blo 630300 949031 := bstep (se 1 (by rfl) ⟨711773, by rfl⟩ : syracuseStep 949031 = 1423547) B1423547
theorem B949055 : Blo 630300 949055 := bstep (se 1 (by rfl) ⟨711791, by rfl⟩ : syracuseStep 949055 = 1423583) B1423583
theorem B1604681 : Blo 630300 1604681 := bstep (se 2 (by rfl) ⟨601755, by rfl⟩ : syracuseStep 1604681 = 1203511) B1203511
theorem B3079403 : Blo 630300 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B949487 : Blo 630300 949487 := bstep (se 1 (by rfl) ⟨712115, by rfl⟩ : syracuseStep 949487 = 1424231) B1424231
theorem B3046697 : Blo 630300 3046697 := bstep (se 2 (by rfl) ⟨1142511, by rfl⟩ : syracuseStep 3046697 = 2285023) B2285023
theorem B2129435 : Blo 630300 2129435 := bstep (se 1 (by rfl) ⟨1597076, by rfl⟩ : syracuseStep 2129435 = 3194153) B3194153
theorem B1605167 : Blo 630300 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B950207 : Blo 630300 950207 := bstep (se 1 (by rfl) ⟨712655, by rfl⟩ : syracuseStep 950207 = 1425311) B1425311
theorem B2130299 : Blo 630300 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B951263 : Blo 630300 951263 := bstep (se 1 (by rfl) ⟨713447, by rfl⟩ : syracuseStep 951263 = 1426895) B1426895
theorem B2131055 : Blo 630300 2131055 := bstep (se 1 (by rfl) ⟨1598291, by rfl⟩ : syracuseStep 2131055 = 3196583) B3196583
theorem B14616359 : Blo 630300 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B3606727 : Blo 630300 3606727 := bstep (se 1 (by rfl) ⟨2705045, by rfl⟩ : syracuseStep 3606727 = 5410091) B5410091
theorem B1062636509 : Blo 630300 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B26021411 : Blo 630300 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B116723267 : Blo 630300 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B7671905 : Blo 630300 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B23138905 : Blo 630300 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B7214183 : Blo 630300 7214183 := bstep (se 1 (by rfl) ⟨5410637, by rfl⟩ : syracuseStep 7214183 = 10821275) B10821275
theorem B8099351 : Blo 630300 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B6822893 : Blo 630300 6822893 := bstep (se 3 (by rfl) ⟨1279292, by rfl⟩ : syracuseStep 6822893 = 2558585) B2558585
theorem B1646057 : Blo 630300 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B630591 : Blo 630300 630591 := bstep (se 1 (by rfl) ⟨472943, by rfl⟩ : syracuseStep 630591 = 945887) B945887
theorem B2695103 : Blo 630300 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B3841991 : Blo 630300 3841991 := bstep (se 1 (by rfl) ⟨2881493, by rfl⟩ : syracuseStep 3841991 = 5762987) B5762987
theorem B2138075 : Blo 630300 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B630855 : Blo 630300 630855 := bstep (se 1 (by rfl) ⟨473141, by rfl⟩ : syracuseStep 630855 = 946283) B946283
theorem B2138345 : Blo 630300 2138345 := bstep (se 2 (by rfl) ⟨801879, by rfl⟩ : syracuseStep 2138345 = 1603759) B1603759
theorem B5480827 : Blo 630300 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B631535 : Blo 630300 631535 := bstep (se 1 (by rfl) ⟨473651, by rfl⟩ : syracuseStep 631535 = 947303) B947303
theorem B632091 : Blo 630300 632091 := bstep (se 1 (by rfl) ⟨474068, by rfl⟩ : syracuseStep 632091 = 948137) B948137
theorem B632287 : Blo 630300 632287 := bstep (se 1 (by rfl) ⟨474215, by rfl⟩ : syracuseStep 632287 = 948431) B948431
theorem B632687 : Blo 630300 632687 := bstep (se 1 (by rfl) ⟨474515, by rfl⟩ : syracuseStep 632687 = 949031) B949031
theorem B632703 : Blo 630300 632703 := bstep (se 1 (by rfl) ⟨474527, by rfl⟩ : syracuseStep 632703 = 949055) B949055
theorem B632991 : Blo 630300 632991 := bstep (se 1 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 632991 = 949487) B949487
theorem B1419623 : Blo 630300 1419623 := bstep (se 1 (by rfl) ⟨1064717, by rfl⟩ : syracuseStep 1419623 = 2129435) B2129435
theorem B633471 : Blo 630300 633471 := bstep (se 1 (by rfl) ⟨475103, by rfl⟩ : syracuseStep 633471 = 950207) B950207
theorem B633627 : Blo 630300 633627 := bstep (se 1 (by rfl) ⟨475220, by rfl⟩ : syracuseStep 633627 = 950441) B950441
theorem B633703 : Blo 630300 633703 := bstep (se 1 (by rfl) ⟨475277, by rfl⟩ : syracuseStep 633703 = 950555) B950555
theorem B633839 : Blo 630300 633839 := bstep (se 1 (by rfl) ⟨475379, by rfl⟩ : syracuseStep 633839 = 950759) B950759
theorem B633887 : Blo 630300 633887 := bstep (se 1 (by rfl) ⟨475415, by rfl⟩ : syracuseStep 633887 = 950831) B950831
theorem B12332249 : Blo 630300 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B2403695 : Blo 630300 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B26324351 : Blo 630300 26324351 := bstep (se 1 (by rfl) ⟨19743263, by rfl⟩ : syracuseStep 26324351 = 39486527) B39486527
theorem B1420937 : Blo 630300 1420937 := bstep (se 2 (by rfl) ⟨532851, by rfl⟩ : syracuseStep 1420937 = 1065703) B1065703
theorem B6827773 : Blo 630300 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B2404349 : Blo 630300 2404349 := bstep (se 3 (by rfl) ⟨450815, by rfl⟩ : syracuseStep 2404349 = 901631) B901631
theorem B1421423 : Blo 630300 1421423 := bstep (se 1 (by rfl) ⟨1066067, by rfl⟩ : syracuseStep 1421423 = 2132135) B2132135
theorem B15415433 : Blo 630300 15415433 := bstep (se 2 (by rfl) ⟨5780787, by rfl⟩ : syracuseStep 15415433 = 11561575) B11561575
theorem B3193991 : Blo 630300 3193991 := bstep (se 1 (by rfl) ⟨2395493, by rfl⟩ : syracuseStep 3193991 = 4790987) B4790987
theorem B27344303 : Blo 630300 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B13876865 : Blo 630300 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B17351111 : Blo 630300 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B2704499 : Blo 630300 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B1197193 : Blo 630300 1197193 := bstep (se 2 (by rfl) ⟨448947, by rfl⟩ : syracuseStep 1197193 = 897895) B897895
theorem B34981307 : Blo 630300 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B1197595 : Blo 630300 1197595 := bstep (se 1 (by rfl) ⟨898196, by rfl⟩ : syracuseStep 1197595 = 1796393) B1796393
theorem B6146171 : Blo 630300 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B6506999 : Blo 630300 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B1067647 : Blo 630300 1067647 := bstep (se 1 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 1067647 = 1601471) B1601471
theorem B3591647 : Blo 630300 3591647 := bstep (se 1 (by rfl) ⟨2693735, by rfl⟩ : syracuseStep 3591647 = 5387471) B5387471
theorem B1068511 : Blo 630300 1068511 := bstep (se 1 (by rfl) ⟨801383, by rfl⟩ : syracuseStep 1068511 = 1602767) B1602767
theorem B81841913 : Blo 630300 81841913 := bstep (se 2 (by rfl) ⟨30690717, by rfl⟩ : syracuseStep 81841913 = 61381435) B61381435
theorem B1069193 : Blo 630300 1069193 := bstep (se 2 (by rfl) ⟨400947, by rfl⟩ : syracuseStep 1069193 = 801895) B801895
theorem B676031 : Blo 630300 676031 := bstep (se 1 (by rfl) ⟨507023, by rfl⟩ : syracuseStep 676031 = 1014047) B1014047
theorem B1069787 : Blo 630300 1069787 := bstep (se 1 (by rfl) ⟨802340, by rfl⟩ : syracuseStep 1069787 = 1604681) B1604681
theorem B2052935 : Blo 630300 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B709663 : Blo 630300 709663 := bstep (se 1 (by rfl) ⟨532247, by rfl⟩ : syracuseStep 709663 = 1064495) B1064495
theorem B1070111 : Blo 630300 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B2020891 : Blo 630300 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B3298931 : Blo 630300 3298931 := bstep (se 1 (by rfl) ⟨2474198, by rfl⟩ : syracuseStep 3298931 = 4948397) B4948397
theorem B5396219 : Blo 630300 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B3168047 : Blo 630300 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B3594563 : Blo 630300 3594563 := bstep (se 1 (by rfl) ⟨2695922, by rfl⟩ : syracuseStep 3594563 = 5391845) B5391845
theorem B3201767 : Blo 630300 3201767 := bstep (se 1 (by rfl) ⟨2401325, by rfl⟩ : syracuseStep 3201767 = 4802651) B4802651
theorem B713371 : Blo 630300 713371 := bstep (se 1 (by rfl) ⟨535028, by rfl⟩ : syracuseStep 713371 = 1070057) B1070057
theorem B3205007 : Blo 630300 3205007 := bstep (se 1 (by rfl) ⟨2403755, by rfl⟩ : syracuseStep 3205007 = 4807511) B4807511
theorem B4810913 : Blo 630300 4810913 := bstep (se 2 (by rfl) ⟨1804092, by rfl⟩ : syracuseStep 4810913 = 3608185) B3608185
theorem B65760281 : Blo 630300 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B945647 : Blo 630300 945647 := bstep (se 1 (by rfl) ⟨709235, by rfl⟩ : syracuseStep 945647 = 1418471) B1418471
theorem B14085647 : Blo 630300 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B945833 : Blo 630300 945833 := bstep (se 2 (by rfl) ⟨354687, by rfl⟩ : syracuseStep 945833 = 709375) B709375
theorem B946667 : Blo 630300 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B11104847 : Blo 630300 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B946793 : Blo 630300 946793 := bstep (se 2 (by rfl) ⟨355047, by rfl⟩ : syracuseStep 946793 = 710095) B710095
theorem B262402685 : Blo 630300 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B946847 : Blo 630300 946847 := bstep (se 1 (by rfl) ⟨710135, by rfl⟩ : syracuseStep 946847 = 1420271) B1420271
theorem B947015 : Blo 630300 947015 := bstep (se 1 (by rfl) ⟨710261, by rfl⟩ : syracuseStep 947015 = 1420523) B1420523
theorem B1799081 : Blo 630300 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B947369 : Blo 630300 947369 := bstep (se 2 (by rfl) ⟨355263, by rfl⟩ : syracuseStep 947369 = 710527) B710527
theorem B947759 : Blo 630300 947759 := bstep (se 1 (by rfl) ⟨710819, by rfl⟩ : syracuseStep 947759 = 1421639) B1421639
theorem B947867 : Blo 630300 947867 := bstep (se 1 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 947867 = 1421801) B1421801
theorem B44365481 : Blo 630300 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B948203 : Blo 630300 948203 := bstep (se 1 (by rfl) ⟨711152, by rfl⟩ : syracuseStep 948203 = 1422305) B1422305
theorem B14776465 : Blo 630300 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B2128571 : Blo 630300 2128571 := bstep (se 1 (by rfl) ⟨1596428, by rfl⟩ : syracuseStep 2128571 = 3192857) B3192857
theorem B2031131 : Blo 630300 2031131 := bstep (se 1 (by rfl) ⟨1523348, by rfl⟩ : syracuseStep 2031131 = 3046697) B3046697
theorem B949967 : Blo 630300 949967 := bstep (se 1 (by rfl) ⟨712475, by rfl⟩ : syracuseStep 949967 = 1424951) B1424951
theorem B1802749 : Blo 630300 1802749 := bstep (se 3 (by rfl) ⟨338015, by rfl⟩ : syracuseStep 1802749 = 676031) B676031
theorem B1802999 : Blo 630300 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B951161 : Blo 630300 951161 := bstep (se 2 (by rfl) ⟨356685, by rfl⟩ : syracuseStep 951161 = 713371) B713371
theorem B46269629 : Blo 630300 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B4097447 : Blo 630300 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B29231077 : Blo 630300 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B2394431 : Blo 630300 2394431 := bstep (se 1 (by rfl) ⟨1795823, by rfl⟩ : syracuseStep 2394431 = 3591647) B3591647
theorem B54561275 : Blo 630300 54561275 := bstep (se 1 (by rfl) ⟨40920956, by rfl⟩ : syracuseStep 54561275 = 81841913) B81841913
theorem B5114603 : Blo 630300 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B2199287 : Blo 630300 2199287 := bstep (se 1 (by rfl) ⟨1649465, by rfl⟩ : syracuseStep 2199287 = 3298931) B3298931
theorem B2396375 : Blo 630300 2396375 := bstep (se 1 (by rfl) ⟨1797281, by rfl⟩ : syracuseStep 2396375 = 3594563) B3594563
theorem B2134511 : Blo 630300 2134511 := bstep (se 1 (by rfl) ⟨1600883, by rfl⟩ : syracuseStep 2134511 = 3201767) B3201767
theorem B2561327 : Blo 630300 2561327 := bstep (se 1 (by rfl) ⟨1920995, by rfl⟩ : syracuseStep 2561327 = 3841991) B3841991
theorem B2136671 : Blo 630300 2136671 := bstep (se 1 (by rfl) ⟨1602503, by rfl⟩ : syracuseStep 2136671 = 3205007) B3205007
theorem B2694521 : Blo 630300 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B630431 : Blo 630300 630431 := bstep (se 1 (by rfl) ⟨472823, by rfl⟩ : syracuseStep 630431 = 945647) B945647
theorem B630555 : Blo 630300 630555 := bstep (se 1 (by rfl) ⟨472916, by rfl⟩ : syracuseStep 630555 = 945833) B945833
theorem B19701953 : Blo 630300 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B631111 : Blo 630300 631111 := bstep (se 1 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 631111 = 946667) B946667
theorem B631195 : Blo 630300 631195 := bstep (se 1 (by rfl) ⟨473396, by rfl⟩ : syracuseStep 631195 = 946793) B946793
theorem B631231 : Blo 630300 631231 := bstep (se 1 (by rfl) ⟨473423, by rfl⟩ : syracuseStep 631231 = 946847) B946847
theorem B631343 : Blo 630300 631343 := bstep (se 1 (by rfl) ⟨473507, by rfl⟩ : syracuseStep 631343 = 947015) B947015
theorem B631579 : Blo 630300 631579 := bstep (se 1 (by rfl) ⟨473684, by rfl⟩ : syracuseStep 631579 = 947369) B947369
theorem B631839 : Blo 630300 631839 := bstep (se 1 (by rfl) ⟨473879, by rfl⟩ : syracuseStep 631839 = 947759) B947759
theorem B631911 : Blo 630300 631911 := bstep (se 1 (by rfl) ⟨473933, by rfl⟩ : syracuseStep 631911 = 947867) B947867
theorem B632135 : Blo 630300 632135 := bstep (se 1 (by rfl) ⟨474101, by rfl⟩ : syracuseStep 632135 = 948203) B948203
theorem B1419047 : Blo 630300 1419047 := bstep (se 1 (by rfl) ⟨1064285, by rfl⟩ : syracuseStep 1419047 = 2128571) B2128571
theorem B18229535 : Blo 630300 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1354087 : Blo 630300 1354087 := bstep (se 1 (by rfl) ⟨1015565, by rfl⟩ : syracuseStep 1354087 = 2031131) B2031131
theorem B9251243 : Blo 630300 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B633311 : Blo 630300 633311 := bstep (se 1 (by rfl) ⟨474983, by rfl⟩ : syracuseStep 633311 = 949967) B949967
theorem B1420199 : Blo 630300 1420199 := bstep (se 1 (by rfl) ⟨1065149, by rfl⟩ : syracuseStep 1420199 = 2130299) B2130299
theorem B634175 : Blo 630300 634175 := bstep (se 1 (by rfl) ⟨475631, by rfl⟩ : syracuseStep 634175 = 951263) B951263
theorem B1420703 : Blo 630300 1420703 := bstep (se 1 (by rfl) ⟨1065527, by rfl⟩ : syracuseStep 1420703 = 2131055) B2131055
theorem B9744239 : Blo 630300 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B4337999 : Blo 630300 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B17347607 : Blo 630300 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B1423529 : Blo 630300 1423529 := bstep (se 2 (by rfl) ⟨533823, by rfl⟩ : syracuseStep 1423529 = 1067647) B1067647
theorem B2112031 : Blo 630300 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B1424681 : Blo 630300 1424681 := bstep (se 2 (by rfl) ⟨534255, by rfl⟩ : syracuseStep 1424681 = 1068511) B1068511
theorem B1097371 : Blo 630300 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B1425383 : Blo 630300 1425383 := bstep (se 1 (by rfl) ⟨1069037, by rfl⟩ : syracuseStep 1425383 = 2138075) B2138075
theorem B1425563 : Blo 630300 1425563 := bstep (se 1 (by rfl) ⟨1069172, by rfl⟩ : syracuseStep 1425563 = 2138345) B2138345
theorem B30851873 : Blo 630300 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B17549567 : Blo 630300 17549567 := bstep (se 1 (by rfl) ⟨13162175, by rfl⟩ : syracuseStep 17549567 = 26324351) B26324351
theorem B9390431 : Blo 630300 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B2833697357 : Blo 630300 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B174935123 : Blo 630300 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B1199387 : Blo 630300 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B29576987 : Blo 630300 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B10276955 : Blo 630300 10276955 := bstep (se 1 (by rfl) ⟨7707716, by rfl⟩ : syracuseStep 10276955 = 15415433) B15415433
theorem B23320871 : Blo 630300 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B1596257 : Blo 630300 1596257 := bstep (se 2 (by rfl) ⟨598596, by rfl⟩ : syracuseStep 1596257 = 1197193) B1197193
theorem B1596793 : Blo 630300 1596793 := bstep (se 2 (by rfl) ⟨598797, by rfl⟩ : syracuseStep 1596793 = 1197595) B1197595
theorem B77815511 : Blo 630300 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B712795 : Blo 630300 712795 := bstep (se 1 (by rfl) ⟨534596, by rfl⟩ : syracuseStep 712795 = 1069193) B1069193
theorem B4808969 : Blo 630300 4808969 := bstep (se 2 (by rfl) ⟨1803363, by rfl⟩ : syracuseStep 4808969 = 3606727) B3606727
theorem B713191 : Blo 630300 713191 := bstep (se 1 (by rfl) ⟨534893, by rfl⟩ : syracuseStep 713191 = 1069787) B1069787
theorem B1368623 : Blo 630300 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B713407 : Blo 630300 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B4809455 : Blo 630300 4809455 := bstep (se 1 (by rfl) ⟨3607091, by rfl⟩ : syracuseStep 4809455 = 7214183) B7214183
theorem B5399567 : Blo 630300 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B3597479 : Blo 630300 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B4548595 : Blo 630300 4548595 := bstep (se 1 (by rfl) ⟨3411446, by rfl⟩ : syracuseStep 4548595 = 6822893) B6822893
theorem B9103697 : Blo 630300 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B1796735 : Blo 630300 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B946217 : Blo 630300 946217 := bstep (se 2 (by rfl) ⟨354831, by rfl⟩ : syracuseStep 946217 = 709663) B709663
theorem B3207275 : Blo 630300 3207275 := bstep (se 1 (by rfl) ⟨2405456, by rfl⟩ : syracuseStep 3207275 = 4810913) B4810913
theorem B946415 : Blo 630300 946415 := bstep (se 1 (by rfl) ⟨709811, by rfl⟩ : syracuseStep 946415 = 1419623) B1419623
theorem B43840187 : Blo 630300 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B8221499 : Blo 630300 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B1602463 : Blo 630300 1602463 := bstep (se 1 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 1602463 = 2403695) B2403695
theorem B947291 : Blo 630300 947291 := bstep (se 1 (by rfl) ⟨710468, by rfl⟩ : syracuseStep 947291 = 1420937) B1420937
theorem B1602899 : Blo 630300 1602899 := bstep (se 1 (by rfl) ⟨1202174, by rfl⟩ : syracuseStep 1602899 = 2404349) B2404349
theorem B947615 : Blo 630300 947615 := bstep (se 1 (by rfl) ⟨710711, by rfl⟩ : syracuseStep 947615 = 1421423) B1421423
theorem B7403231 : Blo 630300 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B2129327 : Blo 630300 2129327 := bstep (se 1 (by rfl) ⟨1596995, by rfl⟩ : syracuseStep 2129327 = 3193991) B3193991
theorem B950375 : Blo 630300 950375 := bstep (se 1 (by rfl) ⟨712781, by rfl⟩ : syracuseStep 950375 = 1425563) B1425563
theorem B950393 : Blo 630300 950393 := bstep (se 2 (by rfl) ⟨356397, by rfl⟩ : syracuseStep 950393 = 712795) B712795
theorem B950921 : Blo 630300 950921 := bstep (se 2 (by rfl) ⟨356595, by rfl⟩ : syracuseStep 950921 = 713191) B713191
theorem B951209 : Blo 630300 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B11699711 : Blo 630300 11699711 := bstep (se 1 (by rfl) ⟨8774783, by rfl⟩ : syracuseStep 11699711 = 17549567) B17549567
theorem B6260287 : Blo 630300 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B36374183 : Blo 630300 36374183 := bstep (se 1 (by rfl) ⟨27280637, by rfl⟩ : syracuseStep 36374183 = 54561275) B54561275
theorem B3409735 : Blo 630300 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B116623415 : Blo 630300 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B6064793 : Blo 630300 6064793 := bstep (se 2 (by rfl) ⟨2274297, by rfl⟩ : syracuseStep 6064793 = 4548595) B4548595
theorem B6851303 : Blo 630300 6851303 := bstep (se 1 (by rfl) ⟨5138477, by rfl⟩ : syracuseStep 6851303 = 10276955) B10276955
theorem B1805449 : Blo 630300 1805449 := bstep (se 2 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 1805449 = 1354087) B1354087
theorem B1707551 : Blo 630300 1707551 := bstep (se 1 (by rfl) ⟨1280663, by rfl⟩ : syracuseStep 1707551 = 2561327) B2561327
theorem B51877007 : Blo 630300 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B2398319 : Blo 630300 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B2136617 : Blo 630300 2136617 := bstep (se 2 (by rfl) ⟨801231, by rfl⟩ : syracuseStep 2136617 = 1602463) B1602463
theorem B6069131 : Blo 630300 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B6167495 : Blo 630300 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B630811 : Blo 630300 630811 := bstep (se 1 (by rfl) ⟨473108, by rfl⟩ : syracuseStep 630811 = 946217) B946217
theorem B2138183 : Blo 630300 2138183 := bstep (se 1 (by rfl) ⟨1603637, by rfl⟩ : syracuseStep 2138183 = 3207275) B3207275
theorem B630943 : Blo 630300 630943 := bstep (se 1 (by rfl) ⟨473207, by rfl⟩ : syracuseStep 630943 = 946415) B946415
theorem B2891999 : Blo 630300 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B5480999 : Blo 630300 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B631527 : Blo 630300 631527 := bstep (se 1 (by rfl) ⟨473645, by rfl⟩ : syracuseStep 631527 = 947291) B947291
theorem B631743 : Blo 630300 631743 := bstep (se 1 (by rfl) ⟨473807, by rfl⟩ : syracuseStep 631743 = 947615) B947615
theorem B1419551 : Blo 630300 1419551 := bstep (se 1 (by rfl) ⟨1064663, by rfl⟩ : syracuseStep 1419551 = 2129327) B2129327
theorem B634107 : Blo 630300 634107 := bstep (se 1 (by rfl) ⟨475580, by rfl⟩ : syracuseStep 634107 = 951161) B951161
theorem B2403665 : Blo 630300 2403665 := bstep (se 2 (by rfl) ⟨901374, by rfl⟩ : syracuseStep 2403665 = 1802749) B1802749
theorem B30846419 : Blo 630300 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B38974769 : Blo 630300 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B1423007 : Blo 630300 1423007 := bstep (se 1 (by rfl) ⟨1067255, by rfl⟩ : syracuseStep 1423007 = 2134511) B2134511
theorem B15547247 : Blo 630300 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B1424447 : Blo 630300 1424447 := bstep (se 1 (by rfl) ⟨1068335, by rfl⟩ : syracuseStep 1424447 = 2136671) B2136671
theorem B1064171 : Blo 630300 1064171 := bstep (se 1 (by rfl) ⟨798128, by rfl⟩ : syracuseStep 1064171 = 1596257) B1596257
theorem B1197823 : Blo 630300 1197823 := bstep (se 1 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 1197823 = 1796735) B1796735
theorem B3198365 : Blo 630300 3198365 := bstep (se 3 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 3198365 = 1199387) B1199387
theorem B5852645 : Blo 630300 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B1068599 : Blo 630300 1068599 := bstep (se 1 (by rfl) ⟨801449, by rfl⟩ : syracuseStep 1068599 = 1602899) B1602899
theorem B4935487 : Blo 630300 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B20567915 : Blo 630300 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B1596287 : Blo 630300 1596287 := bstep (se 1 (by rfl) ⟨1197215, by rfl⟩ : syracuseStep 1596287 = 2394431) B2394431
theorem B1889131571 : Blo 630300 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B4807997 : Blo 630300 4807997 := bstep (se 3 (by rfl) ⟨901499, by rfl⟩ : syracuseStep 4807997 = 1802999) B1802999
theorem B1466191 : Blo 630300 1466191 := bstep (se 1 (by rfl) ⟨1099643, by rfl⟩ : syracuseStep 1466191 = 2199287) B2199287
theorem B19717991 : Blo 630300 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B1597583 : Blo 630300 1597583 := bstep (se 1 (by rfl) ⟨1198187, by rfl⟩ : syracuseStep 1597583 = 2396375) B2396375
theorem B43706101 : Blo 630300 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B1796347 : Blo 630300 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B13134635 : Blo 630300 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B3205979 : Blo 630300 3205979 := bstep (se 1 (by rfl) ⟨2404484, by rfl⟩ : syracuseStep 3205979 = 4808969) B4808969
theorem B912415 : Blo 630300 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B3206303 : Blo 630300 3206303 := bstep (se 1 (by rfl) ⟨2404727, by rfl⟩ : syracuseStep 3206303 = 4809455) B4809455
theorem B3599711 : Blo 630300 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B946031 : Blo 630300 946031 := bstep (se 1 (by rfl) ⟨709523, by rfl⟩ : syracuseStep 946031 = 1419047) B1419047
theorem B12153023 : Blo 630300 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B946799 : Blo 630300 946799 := bstep (se 1 (by rfl) ⟨710099, by rfl⟩ : syracuseStep 946799 = 1420199) B1420199
theorem B947135 : Blo 630300 947135 := bstep (se 1 (by rfl) ⟨710351, by rfl⟩ : syracuseStep 947135 = 1420703) B1420703
theorem B29226791 : Blo 630300 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B11565071 : Blo 630300 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B2816041 : Blo 630300 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B949019 : Blo 630300 949019 := bstep (se 1 (by rfl) ⟨711764, by rfl⟩ : syracuseStep 949019 = 1423529) B1423529
theorem B2129057 : Blo 630300 2129057 := bstep (se 2 (by rfl) ⟨798396, by rfl⟩ : syracuseStep 2129057 = 1596793) B1596793
theorem B949787 : Blo 630300 949787 := bstep (se 1 (by rfl) ⟨712340, by rfl⟩ : syracuseStep 949787 = 1424681) B1424681
theorem B25984637 : Blo 630300 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B950255 : Blo 630300 950255 := bstep (se 1 (by rfl) ⟨712691, by rfl⟩ : syracuseStep 950255 = 1425383) B1425383
theorem B7799807 : Blo 630300 7799807 := bstep (se 1 (by rfl) ⟨5849855, by rfl⟩ : syracuseStep 7799807 = 11699711) B11699711
theorem B24249455 : Blo 630300 24249455 := bstep (se 1 (by rfl) ⟨18187091, by rfl⟩ : syracuseStep 24249455 = 36374183) B36374183
theorem B2132243 : Blo 630300 2132243 := bstep (se 1 (by rfl) ⟨1599182, by rfl⟩ : syracuseStep 2132243 = 3198365) B3198365
theorem B3901763 : Blo 630300 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B2395129 : Blo 630300 2395129 := bstep (se 2 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 2395129 = 1796347) B1796347
theorem B1216553 : Blo 630300 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B13145327 : Blo 630300 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B8756423 : Blo 630300 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B2137319 : Blo 630300 2137319 := bstep (se 1 (by rfl) ⟨1602989, by rfl⟩ : syracuseStep 2137319 = 3205979) B3205979
theorem B2137535 : Blo 630300 2137535 := bstep (se 1 (by rfl) ⟨1603151, by rfl⟩ : syracuseStep 2137535 = 3206303) B3206303
theorem B2399807 : Blo 630300 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B630687 : Blo 630300 630687 := bstep (se 1 (by rfl) ⟨473015, by rfl⟩ : syracuseStep 630687 = 946031) B946031
theorem B8102015 : Blo 630300 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B631199 : Blo 630300 631199 := bstep (se 1 (by rfl) ⟨473399, by rfl⟩ : syracuseStep 631199 = 946799) B946799
theorem B631423 : Blo 630300 631423 := bstep (se 1 (by rfl) ⟨473567, by rfl⟩ : syracuseStep 631423 = 947135) B947135
theorem B7710047 : Blo 630300 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B632679 : Blo 630300 632679 := bstep (se 1 (by rfl) ⟨474509, by rfl⟩ : syracuseStep 632679 = 949019) B949019
theorem B10364831 : Blo 630300 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B1419371 : Blo 630300 1419371 := bstep (se 1 (by rfl) ⟨1064528, by rfl⟩ : syracuseStep 1419371 = 2129057) B2129057
theorem B633191 : Blo 630300 633191 := bstep (se 1 (by rfl) ⟨474893, by rfl⟩ : syracuseStep 633191 = 949787) B949787
theorem B633503 : Blo 630300 633503 := bstep (se 1 (by rfl) ⟨475127, by rfl⟩ : syracuseStep 633503 = 950255) B950255
theorem B633583 : Blo 630300 633583 := bstep (se 1 (by rfl) ⟨475187, by rfl⟩ : syracuseStep 633583 = 950375) B950375
theorem B633595 : Blo 630300 633595 := bstep (se 1 (by rfl) ⟨475196, by rfl⟩ : syracuseStep 633595 = 950393) B950393
theorem B633947 : Blo 630300 633947 := bstep (se 1 (by rfl) ⟨475460, by rfl⟩ : syracuseStep 633947 = 950921) B950921
theorem B634139 : Blo 630300 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B4043195 : Blo 630300 4043195 := bstep (se 1 (by rfl) ⟨3032396, by rfl⟩ : syracuseStep 4043195 = 6064793) B6064793
theorem B4567535 : Blo 630300 4567535 := bstep (se 1 (by rfl) ⟨3425651, by rfl⟩ : syracuseStep 4567535 = 6851303) B6851303
theorem B58274801 : Blo 630300 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B34584671 : Blo 630300 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B13711943 : Blo 630300 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B2407265 : Blo 630300 2407265 := bstep (se 2 (by rfl) ⟨902724, by rfl⟩ : syracuseStep 2407265 = 1805449) B1805449
theorem B1424411 : Blo 630300 1424411 := bstep (se 1 (by rfl) ⟨1068308, by rfl⟩ : syracuseStep 1424411 = 2136617) B2136617
theorem B1064191 : Blo 630300 1064191 := bstep (se 1 (by rfl) ⟨798143, by rfl⟩ : syracuseStep 1064191 = 1596287) B1596287
theorem B4046087 : Blo 630300 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B4111663 : Blo 630300 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B1259421047 : Blo 630300 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B77938109 : Blo 630300 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B1425455 : Blo 630300 1425455 := bstep (se 1 (by rfl) ⟨1069091, by rfl⟩ : syracuseStep 1425455 = 2138183) B2138183
theorem B1065055 : Blo 630300 1065055 := bstep (se 1 (by rfl) ⟨798791, by rfl⟩ : syracuseStep 1065055 = 1597583) B1597583
theorem B3653999 : Blo 630300 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B20564279 : Blo 630300 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B3754721 : Blo 630300 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B7819685 : Blo 630300 7819685 := bstep (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) B1466191
theorem B709447 : Blo 630300 709447 := bstep (se 1 (by rfl) ⟨532085, by rfl⟩ : syracuseStep 709447 = 1064171) B1064171
theorem B17323091 : Blo 630300 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B77748943 : Blo 630300 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B8347049 : Blo 630300 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B1597097 : Blo 630300 1597097 := bstep (se 2 (by rfl) ⟨598911, by rfl⟩ : syracuseStep 1597097 = 1197823) B1197823
theorem B1138367 : Blo 630300 1138367 := bstep (se 1 (by rfl) ⟨853775, by rfl⟩ : syracuseStep 1138367 = 1707551) B1707551
theorem B712399 : Blo 630300 712399 := bstep (se 1 (by rfl) ⟨534299, by rfl⟩ : syracuseStep 712399 = 1068599) B1068599
theorem B4546313 : Blo 630300 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B1598879 : Blo 630300 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B3205331 : Blo 630300 3205331 := bstep (se 1 (by rfl) ⟨2403998, by rfl⟩ : syracuseStep 3205331 = 4807997) B4807997
theorem B6580649 : Blo 630300 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B1927999 : Blo 630300 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B946367 : Blo 630300 946367 := bstep (se 1 (by rfl) ⟨709775, by rfl⟩ : syracuseStep 946367 = 1419551) B1419551
theorem B1602443 : Blo 630300 1602443 := bstep (se 1 (by rfl) ⟨1201832, by rfl⟩ : syracuseStep 1602443 = 2403665) B2403665
theorem B25983179 : Blo 630300 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B948671 : Blo 630300 948671 := bstep (se 1 (by rfl) ⟨711503, by rfl⟩ : syracuseStep 948671 = 1423007) B1423007
theorem B949631 : Blo 630300 949631 := bstep (se 1 (by rfl) ⟨712223, by rfl⟩ : syracuseStep 949631 = 1424447) B1424447
theorem B950303 : Blo 630300 950303 := bstep (se 1 (by rfl) ⟨712727, by rfl⟩ : syracuseStep 950303 = 1425455) B1425455
theorem B3244141 : Blo 630300 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B5213123 : Blo 630300 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B5837615 : Blo 630300 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B758911 : Blo 630300 758911 := bstep (se 1 (by rfl) ⟨569183, by rfl⟩ : syracuseStep 758911 = 1138367) B1138367
theorem B2136887 : Blo 630300 2136887 := bstep (se 1 (by rfl) ⟨1602665, by rfl⟩ : syracuseStep 2136887 = 3205331) B3205331
theorem B630911 : Blo 630300 630911 := bstep (se 1 (by rfl) ⟨473183, by rfl⟩ : syracuseStep 630911 = 946367) B946367
theorem B2695463 : Blo 630300 2695463 := bstep (se 1 (by rfl) ⟨2021597, by rfl⟩ : syracuseStep 2695463 = 4043195) B4043195
theorem B632447 : Blo 630300 632447 := bstep (se 1 (by rfl) ⟨474335, by rfl⟩ : syracuseStep 632447 = 948671) B948671
theorem B1418921 : Blo 630300 1418921 := bstep (se 2 (by rfl) ⟨532095, by rfl⟩ : syracuseStep 1418921 = 1064191) B1064191
theorem B5482217 : Blo 630300 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B2697391 : Blo 630300 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B633087 : Blo 630300 633087 := bstep (se 1 (by rfl) ⟨474815, by rfl⟩ : syracuseStep 633087 = 949631) B949631
theorem B1420073 : Blo 630300 1420073 := bstep (se 2 (by rfl) ⟨532527, by rfl⟩ : syracuseStep 1420073 = 1065055) B1065055
theorem B2435999 : Blo 630300 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B16166303 : Blo 630300 16166303 := bstep (se 1 (by rfl) ⟨12124727, by rfl⟩ : syracuseStep 16166303 = 24249455) B24249455
theorem B1421495 : Blo 630300 1421495 := bstep (se 1 (by rfl) ⟨1066121, by rfl⟩ : syracuseStep 1421495 = 2132243) B2132243
theorem B13709519 : Blo 630300 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B2601175 : Blo 630300 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2503147 : Blo 630300 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B11548727 : Blo 630300 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B8763551 : Blo 630300 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B2570665 : Blo 630300 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B3193505 : Blo 630300 3193505 := bstep (se 2 (by rfl) ⟨1197564, by rfl⟩ : syracuseStep 3193505 = 2395129) B2395129
theorem B1424879 : Blo 630300 1424879 := bstep (se 1 (by rfl) ⟨1068659, by rfl⟩ : syracuseStep 1424879 = 2137319) B2137319
theorem B1425023 : Blo 630300 1425023 := bstep (se 1 (by rfl) ⟨1068767, by rfl⟩ : syracuseStep 1425023 = 2137535) B2137535
theorem B1064731 : Blo 630300 1064731 := bstep (se 1 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 1064731 = 1597097) B1597097
theorem B3030875 : Blo 630300 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B1065919 : Blo 630300 1065919 := bstep (se 1 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 1065919 = 1598879) B1598879
theorem B17548397 : Blo 630300 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B1068295 : Blo 630300 1068295 := bstep (se 1 (by rfl) ⟨801221, by rfl⟩ : syracuseStep 1068295 = 1602443) B1602443
theorem B38849867 : Blo 630300 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B103665257 : Blo 630300 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B23056447 : Blo 630300 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B17322119 : Blo 630300 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B51958739 : Blo 630300 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B5199871 : Blo 630300 5199871 := bstep (se 1 (by rfl) ⟨3899903, by rfl⟩ : syracuseStep 5199871 = 7799807) B7799807
theorem B5564699 : Blo 630300 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B1599871 : Blo 630300 1599871 := bstep (se 1 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 1599871 = 2399807) B2399807
theorem B5401343 : Blo 630300 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B5140031 : Blo 630300 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B945929 : Blo 630300 945929 := bstep (se 2 (by rfl) ⟨354723, by rfl⟩ : syracuseStep 945929 = 709447) B709447
theorem B6909887 : Blo 630300 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B946247 : Blo 630300 946247 := bstep (se 1 (by rfl) ⟨709685, by rfl⟩ : syracuseStep 946247 = 1419371) B1419371
theorem B3045023 : Blo 630300 3045023 := bstep (se 1 (by rfl) ⟨2283767, by rfl⟩ : syracuseStep 3045023 = 4567535) B4567535
theorem B9141295 : Blo 630300 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B1604843 : Blo 630300 1604843 := bstep (se 1 (by rfl) ⟨1203632, by rfl⟩ : syracuseStep 1604843 = 2407265) B2407265
theorem B949607 : Blo 630300 949607 := bstep (se 1 (by rfl) ⟨712205, by rfl⟩ : syracuseStep 949607 = 1424411) B1424411
theorem B839614031 : Blo 630300 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B949865 : Blo 630300 949865 := bstep (se 2 (by rfl) ⟨356199, by rfl⟩ : syracuseStep 949865 = 712399) B712399
theorem B4325521 : Blo 630300 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B11698931 : Blo 630300 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B3475415 : Blo 630300 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B69110171 : Blo 630300 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B2133161 : Blo 630300 2133161 := bstep (se 2 (by rfl) ⟨799935, by rfl⟩ : syracuseStep 2133161 = 1599871) B1599871
theorem B34639159 : Blo 630300 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B30741929 : Blo 630300 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B3709799 : Blo 630300 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B630619 : Blo 630300 630619 := bstep (se 1 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 630619 = 945929) B945929
theorem B630831 : Blo 630300 630831 := bstep (se 1 (by rfl) ⟨473123, by rfl⟩ : syracuseStep 630831 = 946247) B946247
theorem B5842367 : Blo 630300 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B13706749 : Blo 630300 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B633071 : Blo 630300 633071 := bstep (se 1 (by rfl) ⟨474803, by rfl⟩ : syracuseStep 633071 = 949607) B949607
theorem B1419641 : Blo 630300 1419641 := bstep (se 2 (by rfl) ⟨532365, by rfl⟩ : syracuseStep 1419641 = 1064731) B1064731
theorem B633243 : Blo 630300 633243 := bstep (se 1 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 633243 = 949865) B949865
theorem B18426365 : Blo 630300 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B633535 : Blo 630300 633535 := bstep (se 1 (by rfl) ⟨475151, by rfl⟩ : syracuseStep 633535 = 950303) B950303
theorem B1421225 : Blo 630300 1421225 := bstep (se 2 (by rfl) ⟨532959, by rfl⟩ : syracuseStep 1421225 = 1065919) B1065919
theorem B25899911 : Blo 630300 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B11548079 : Blo 630300 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B1424393 : Blo 630300 1424393 := bstep (se 2 (by rfl) ⟨534147, by rfl⟩ : syracuseStep 1424393 = 1068295) B1068295
theorem B1424591 : Blo 630300 1424591 := bstep (se 1 (by rfl) ⟨1068443, by rfl⟩ : syracuseStep 1424591 = 2136887) B2136887
theorem B3654811 : Blo 630300 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B6933161 : Blo 630300 6933161 := bstep (se 2 (by rfl) ⟨2599935, by rfl⟩ : syracuseStep 6933161 = 5199871) B5199871
theorem B3427553 : Blo 630300 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B1069895 : Blo 630300 1069895 := bstep (se 1 (by rfl) ⟨802421, by rfl⟩ : syracuseStep 1069895 = 1604843) B1604843
theorem B2020583 : Blo 630300 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B3596521 : Blo 630300 3596521 := bstep (se 2 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 3596521 = 2697391) B2697391
theorem B3891743 : Blo 630300 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B1796975 : Blo 630300 1796975 := bstep (se 1 (by rfl) ⟨1347731, by rfl⟩ : syracuseStep 1796975 = 2695463) B2695463
theorem B3468233 : Blo 630300 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B3337529 : Blo 630300 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B945947 : Blo 630300 945947 := bstep (se 1 (by rfl) ⟨709460, by rfl⟩ : syracuseStep 945947 = 1418921) B1418921
theorem B1011881 : Blo 630300 1011881 := bstep (se 2 (by rfl) ⟨379455, by rfl⟩ : syracuseStep 1011881 = 758911) B758911
theorem B3600895 : Blo 630300 3600895 := bstep (se 1 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 3600895 = 5401343) B5401343
theorem B946715 : Blo 630300 946715 := bstep (se 1 (by rfl) ⟨710036, by rfl⟩ : syracuseStep 946715 = 1420073) B1420073
theorem B10777535 : Blo 630300 10777535 := bstep (se 1 (by rfl) ⟨8083151, by rfl⟩ : syracuseStep 10777535 = 16166303) B16166303
theorem B947663 : Blo 630300 947663 := bstep (se 1 (by rfl) ⟨710747, by rfl⟩ : syracuseStep 947663 = 1421495) B1421495
theorem B9139679 : Blo 630300 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B2030015 : Blo 630300 2030015 := bstep (se 1 (by rfl) ⟨1522511, by rfl⟩ : syracuseStep 2030015 = 3045023) B3045023
theorem B7699151 : Blo 630300 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B12188393 : Blo 630300 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B25983989 : Blo 630300 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B2129003 : Blo 630300 2129003 := bstep (se 1 (by rfl) ⟨1596752, by rfl⟩ : syracuseStep 2129003 = 3193505) B3193505
theorem B949919 : Blo 630300 949919 := bstep (se 1 (by rfl) ⟨712439, by rfl⟩ : syracuseStep 949919 = 1424879) B1424879
theorem B559742687 : Blo 630300 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B950015 : Blo 630300 950015 := bstep (se 1 (by rfl) ⟨712511, by rfl⟩ : syracuseStep 950015 = 1425023) B1425023
theorem B5767361 : Blo 630300 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B7799287 : Blo 630300 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B46073447 : Blo 630300 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B2594495 : Blo 630300 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B18488429 : Blo 630300 18488429 := bstep (se 3 (by rfl) ⟨3466580, by rfl⟩ : syracuseStep 18488429 = 6933161) B6933161
theorem B630631 : Blo 630300 630631 := bstep (se 1 (by rfl) ⟨472973, by rfl⟩ : syracuseStep 630631 = 945947) B945947
theorem B631143 : Blo 630300 631143 := bstep (se 1 (by rfl) ⟨473357, by rfl⟩ : syracuseStep 631143 = 946715) B946715
theorem B7185023 : Blo 630300 7185023 := bstep (se 1 (by rfl) ⟨5388767, by rfl⟩ : syracuseStep 7185023 = 10777535) B10777535
theorem B631775 : Blo 630300 631775 := bstep (se 1 (by rfl) ⟨473831, by rfl⟩ : syracuseStep 631775 = 947663) B947663
theorem B1353343 : Blo 630300 1353343 := bstep (se 1 (by rfl) ⟨1015007, by rfl⟩ : syracuseStep 1353343 = 2030015) B2030015
theorem B1419335 : Blo 630300 1419335 := bstep (se 1 (by rfl) ⟨1064501, by rfl⟩ : syracuseStep 1419335 = 2129003) B2129003
theorem B633279 : Blo 630300 633279 := bstep (se 1 (by rfl) ⟨474959, by rfl⟩ : syracuseStep 633279 = 949919) B949919
theorem B633343 : Blo 630300 633343 := bstep (se 1 (by rfl) ⟨475007, by rfl⟩ : syracuseStep 633343 = 950015) B950015
theorem B4795361 : Blo 630300 4795361 := bstep (se 2 (by rfl) ⟨1798260, by rfl⟩ : syracuseStep 4795361 = 3596521) B3596521
theorem B1422107 : Blo 630300 1422107 := bstep (se 1 (by rfl) ⟨1066580, by rfl⟩ : syracuseStep 1422107 = 2133161) B2133161
theorem B5388221 : Blo 630300 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B20494619 : Blo 630300 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B46185545 : Blo 630300 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B2473199 : Blo 630300 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B4801193 : Blo 630300 4801193 := bstep (se 2 (by rfl) ⟨1800447, by rfl⟩ : syracuseStep 4801193 = 3600895) B3600895
theorem B1197983 : Blo 630300 1197983 := bstep (se 1 (by rfl) ⟨898487, by rfl⟩ : syracuseStep 1197983 = 1796975) B1796975
theorem B2312155 : Blo 630300 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B674587 : Blo 630300 674587 := bstep (se 1 (by rfl) ⟨505940, by rfl⟩ : syracuseStep 674587 = 1011881) B1011881
theorem B8900077 : Blo 630300 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B5132767 : Blo 630300 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B17322659 : Blo 630300 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B2316943 : Blo 630300 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B4873081 : Blo 630300 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B18275665 : Blo 630300 18275665 := bstep (se 2 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 18275665 = 13706749) B13706749
theorem B713263 : Blo 630300 713263 := bstep (se 1 (by rfl) ⟨534947, by rfl⟩ : syracuseStep 713263 = 1069895) B1069895
theorem B3894911 : Blo 630300 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B946427 : Blo 630300 946427 := bstep (se 1 (by rfl) ⟨709820, by rfl⟩ : syracuseStep 946427 = 1419641) B1419641
theorem B12284243 : Blo 630300 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B947483 : Blo 630300 947483 := bstep (se 1 (by rfl) ⟨710612, by rfl⟩ : syracuseStep 947483 = 1421225) B1421225
theorem B9140141 : Blo 630300 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B17266607 : Blo 630300 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B7698719 : Blo 630300 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B6093119 : Blo 630300 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B8125595 : Blo 630300 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B949595 : Blo 630300 949595 := bstep (se 1 (by rfl) ⟨712196, by rfl⟩ : syracuseStep 949595 = 1424393) B1424393
theorem B949727 : Blo 630300 949727 := bstep (se 1 (by rfl) ⟨712295, by rfl⟩ : syracuseStep 949727 = 1424591) B1424591
theorem B373161791 : Blo 630300 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B951017 : Blo 630300 951017 := bstep (se 2 (by rfl) ⟨356631, by rfl⟩ : syracuseStep 951017 = 713263) B713263
theorem B1804457 : Blo 630300 1804457 := bstep (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) B1353343
theorem B3082873 : Blo 630300 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B12357029 : Blo 630300 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B11866769 : Blo 630300 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B12325619 : Blo 630300 12325619 := bstep (se 1 (by rfl) ⟨9244214, by rfl⟩ : syracuseStep 12325619 = 18488429) B18488429
theorem B4790015 : Blo 630300 4790015 := bstep (se 1 (by rfl) ⟨3592511, by rfl⟩ : syracuseStep 4790015 = 7185023) B7185023
theorem B2596607 : Blo 630300 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B630951 : Blo 630300 630951 := bstep (se 1 (by rfl) ⟨473213, by rfl⟩ : syracuseStep 630951 = 946427) B946427
theorem B631655 : Blo 630300 631655 := bstep (se 1 (by rfl) ⟨473741, by rfl⟩ : syracuseStep 631655 = 947483) B947483
theorem B6497441 : Blo 630300 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B11511071 : Blo 630300 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B5417063 : Blo 630300 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B1648799 : Blo 630300 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B633063 : Blo 630300 633063 := bstep (se 1 (by rfl) ⟨474797, by rfl⟩ : syracuseStep 633063 = 949595) B949595
theorem B633151 : Blo 630300 633151 := bstep (se 1 (by rfl) ⟨474863, by rfl⟩ : syracuseStep 633151 = 949727) B949727
theorem B3844907 : Blo 630300 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B10399049 : Blo 630300 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B30715631 : Blo 630300 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B798655 : Blo 630300 798655 := bstep (se 1 (by rfl) ⟨598991, by rfl⟩ : syracuseStep 798655 = 1197983) B1197983
theorem B11548439 : Blo 630300 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B3196907 : Blo 630300 3196907 := bstep (se 1 (by rfl) ⟨2397680, by rfl⟩ : syracuseStep 3196907 = 4795361) B4795361
theorem B3592147 : Blo 630300 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B5132479 : Blo 630300 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B24367553 : Blo 630300 24367553 := bstep (se 2 (by rfl) ⟨9137832, by rfl⟩ : syracuseStep 24367553 = 18275665) B18275665
theorem B30790363 : Blo 630300 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B3200795 : Blo 630300 3200795 := bstep (se 1 (by rfl) ⟨2400596, by rfl⟩ : syracuseStep 3200795 = 4801193) B4801193
theorem B1729663 : Blo 630300 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B3597797 : Blo 630300 3597797 := bstep (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) B674587
theorem B6843689 : Blo 630300 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B946223 : Blo 630300 946223 := bstep (se 1 (by rfl) ⟨709667, by rfl⟩ : syracuseStep 946223 = 1419335) B1419335
theorem B8189495 : Blo 630300 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B948071 : Blo 630300 948071 := bstep (se 1 (by rfl) ⟨711053, by rfl⟩ : syracuseStep 948071 = 1422107) B1422107
theorem B6093427 : Blo 630300 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B13663079 : Blo 630300 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B4062079 : Blo 630300 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B248774527 : Blo 630300 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B2131271 : Blo 630300 2131271 := bstep (se 1 (by rfl) ⟨1598453, by rfl⟩ : syracuseStep 2131271 = 3196907) B3196907
theorem B32868317 : Blo 630300 32868317 := bstep (se 3 (by rfl) ⟨6162809, by rfl⟩ : syracuseStep 32868317 = 12325619) B12325619
theorem B2133863 : Blo 630300 2133863 := bstep (se 1 (by rfl) ⟨1600397, by rfl⟩ : syracuseStep 2133863 = 3200795) B3200795
theorem B4789529 : Blo 630300 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B4331627 : Blo 630300 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B7674047 : Blo 630300 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B2398531 : Blo 630300 2398531 := bstep (se 1 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 2398531 = 3597797) B3597797
theorem B3611375 : Blo 630300 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B2563271 : Blo 630300 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B4562459 : Blo 630300 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B630815 : Blo 630300 630815 := bstep (se 1 (by rfl) ⟨473111, by rfl⟩ : syracuseStep 630815 = 946223) B946223
theorem B5416105 : Blo 630300 5416105 := bstep (se 2 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 5416105 = 4062079) B4062079
theorem B632047 : Blo 630300 632047 := bstep (se 1 (by rfl) ⟨474035, by rfl⟩ : syracuseStep 632047 = 948071) B948071
theorem B634011 : Blo 630300 634011 := bstep (se 1 (by rfl) ⟨475508, by rfl⟩ : syracuseStep 634011 = 951017) B951017
theorem B8238019 : Blo 630300 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B7911179 : Blo 630300 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B4110497 : Blo 630300 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B3193343 : Blo 630300 3193343 := bstep (se 1 (by rfl) ⟨2395007, by rfl⟩ : syracuseStep 3193343 = 4790015) B4790015
theorem B1064873 : Blo 630300 1064873 := bstep (se 2 (by rfl) ⟨399327, by rfl⟩ : syracuseStep 1064873 = 798655) B798655
theorem B9224869 : Blo 630300 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B1099199 : Blo 630300 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B6932699 : Blo 630300 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B5459663 : Blo 630300 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B331699369 : Blo 630300 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B16245035 : Blo 630300 16245035 := bstep (se 1 (by rfl) ⟨12183776, by rfl⟩ : syracuseStep 16245035 = 24367553) B24367553
theorem B1731071 : Blo 630300 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B6843305 : Blo 630300 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B4811885 : Blo 630300 4811885 := bstep (se 3 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 4811885 = 1804457) B1804457
theorem B41053817 : Blo 630300 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B20477087 : Blo 630300 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B8124569 : Blo 630300 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B7698959 : Blo 630300 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B9108719 : Blo 630300 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B4621799 : Blo 630300 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B2887751 : Blo 630300 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B5116031 : Blo 630300 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B1708847 : Blo 630300 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B10984025 : Blo 630300 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B4562203 : Blo 630300 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B27369211 : Blo 630300 27369211 := bstep (se 1 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 27369211 = 41053817) B41053817
theorem B5416379 : Blo 630300 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B14559101 : Blo 630300 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B6072479 : Blo 630300 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B1420847 : Blo 630300 1420847 := bstep (se 1 (by rfl) ⟨1065635, by rfl⟩ : syracuseStep 1420847 = 2131271) B2131271
theorem B12299825 : Blo 630300 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B7221473 : Blo 630300 7221473 := bstep (se 2 (by rfl) ⟨2708052, by rfl⟩ : syracuseStep 7221473 = 5416105) B5416105
theorem B1422575 : Blo 630300 1422575 := bstep (se 1 (by rfl) ⟨1066931, by rfl⟩ : syracuseStep 1422575 = 2133863) B2133863
theorem B3193019 : Blo 630300 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B2931197 : Blo 630300 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B2407583 : Blo 630300 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B10830023 : Blo 630300 10830023 := bstep (se 1 (by rfl) ⟨8122517, by rfl⟩ : syracuseStep 10830023 = 16245035) B16245035
theorem B3198041 : Blo 630300 3198041 := bstep (se 2 (by rfl) ⟨1199265, by rfl⟩ : syracuseStep 3198041 = 2398531) B2398531
theorem B13651391 : Blo 630300 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B2740331 : Blo 630300 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B5132639 : Blo 630300 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B709915 : Blo 630300 709915 := bstep (se 1 (by rfl) ⟨532436, by rfl⟩ : syracuseStep 709915 = 1064873) B1064873
theorem B21912211 : Blo 630300 21912211 := bstep (se 1 (by rfl) ⟨16434158, by rfl⟩ : syracuseStep 21912211 = 32868317) B32868317
theorem B3041639 : Blo 630300 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B4616189 : Blo 630300 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B442265825 : Blo 630300 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B3207923 : Blo 630300 3207923 := bstep (se 1 (by rfl) ⟨2405942, by rfl⟩ : syracuseStep 3207923 = 4811885) B4811885
theorem B5274119 : Blo 630300 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B2128895 : Blo 630300 2128895 := bstep (se 1 (by rfl) ⟨1596671, by rfl⟩ : syracuseStep 2128895 = 3193343) B3193343
theorem B7700669 : Blo 630300 7700669 := bstep (se 3 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 7700669 = 2887751) B2887751
theorem B3081199 : Blo 630300 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B2132027 : Blo 630300 2132027 := bstep (se 1 (by rfl) ⟨1599020, by rfl⟩ : syracuseStep 2132027 = 3198041) B3198041
theorem B3410687 : Blo 630300 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B31266101 : Blo 630300 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B3610919 : Blo 630300 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B9706067 : Blo 630300 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B14064317 : Blo 630300 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B8199883 : Blo 630300 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B2138615 : Blo 630300 2138615 := bstep (se 1 (by rfl) ⟨1603961, by rfl⟩ : syracuseStep 2138615 = 3207923) B3207923
theorem B1419263 : Blo 630300 1419263 := bstep (se 1 (by rfl) ⟨1064447, by rfl⟩ : syracuseStep 1419263 = 2128895) B2128895
theorem B7220015 : Blo 630300 7220015 := bstep (se 1 (by rfl) ⟨5415011, by rfl⟩ : syracuseStep 7220015 = 10830023) B10830023
theorem B3421759 : Blo 630300 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B116865125 : Blo 630300 116865125 := bstep (se 4 (by rfl) ⟨10956105, by rfl⟩ : syracuseStep 116865125 = 21912211) B21912211
theorem B4048319 : Blo 630300 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B6082937 : Blo 630300 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B36492281 : Blo 630300 36492281 := bstep (se 2 (by rfl) ⟨13684605, by rfl⟩ : syracuseStep 36492281 = 27369211) B27369211
theorem B9100927 : Blo 630300 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B1826887 : Blo 630300 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B1139231 : Blo 630300 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B29290733 : Blo 630300 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B2027759 : Blo 630300 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B946553 : Blo 630300 946553 := bstep (se 2 (by rfl) ⟨354957, by rfl⟩ : syracuseStep 946553 = 709915) B709915
theorem B947231 : Blo 630300 947231 := bstep (se 1 (by rfl) ⟨710423, by rfl⟩ : syracuseStep 947231 = 1420847) B1420847
theorem B3077459 : Blo 630300 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B294843883 : Blo 630300 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B4814315 : Blo 630300 4814315 := bstep (se 1 (by rfl) ⟨3610736, by rfl⟩ : syracuseStep 4814315 = 7221473) B7221473
theorem B948383 : Blo 630300 948383 := bstep (se 1 (by rfl) ⟨711287, by rfl⟩ : syracuseStep 948383 = 1422575) B1422575
theorem B2128679 : Blo 630300 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B1605055 : Blo 630300 1605055 := bstep (se 1 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 1605055 = 2407583) B2407583
theorem B5407357 : Blo 630300 5407357 := bstep (se 3 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 5407357 = 2027759) B2027759
theorem B20844067 : Blo 630300 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B9376211 : Blo 630300 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B393125177 : Blo 630300 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B4562345 : Blo 630300 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B631035 : Blo 630300 631035 := bstep (se 1 (by rfl) ⟨473276, by rfl⟩ : syracuseStep 631035 = 946553) B946553
theorem B631487 : Blo 630300 631487 := bstep (se 1 (by rfl) ⟨473615, by rfl⟩ : syracuseStep 631487 = 947231) B947231
theorem B632255 : Blo 630300 632255 := bstep (se 1 (by rfl) ⟨474191, by rfl⟩ : syracuseStep 632255 = 948383) B948383
theorem B1419119 : Blo 630300 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B2140073 : Blo 630300 2140073 := bstep (se 2 (by rfl) ⟨802527, by rfl⟩ : syracuseStep 2140073 = 1605055) B1605055
theorem B12134569 : Blo 630300 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B2435849 : Blo 630300 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B2698879 : Blo 630300 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B4108265 : Blo 630300 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B1421351 : Blo 630300 1421351 := bstep (se 1 (by rfl) ⟨1066013, by rfl⟩ : syracuseStep 1421351 = 2132027) B2132027
theorem B24328187 : Blo 630300 24328187 := bstep (se 1 (by rfl) ⟨18246140, by rfl⟩ : syracuseStep 24328187 = 36492281) B36492281
theorem B2407279 : Blo 630300 2407279 := bstep (se 1 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 2407279 = 3610919) B3610919
theorem B6470711 : Blo 630300 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B1425743 : Blo 630300 1425743 := bstep (se 1 (by rfl) ⟨1069307, by rfl⟩ : syracuseStep 1425743 = 2138615) B2138615
theorem B9095165 : Blo 630300 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B2051639 : Blo 630300 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B43732709 : Blo 630300 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B77910083 : Blo 630300 77910083 := bstep (se 1 (by rfl) ⟨58432562, by rfl⟩ : syracuseStep 77910083 = 116865125) B116865125
theorem B5133779 : Blo 630300 5133779 := bstep (se 1 (by rfl) ⟨3850334, by rfl⟩ : syracuseStep 5133779 = 7700669) B7700669
theorem B3037949 : Blo 630300 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B4055291 : Blo 630300 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B946175 : Blo 630300 946175 := bstep (se 1 (by rfl) ⟨709631, by rfl⟩ : syracuseStep 946175 = 1419263) B1419263
theorem B4813343 : Blo 630300 4813343 := bstep (se 1 (by rfl) ⟨3610007, by rfl⟩ : syracuseStep 4813343 = 7220015) B7220015
theorem B19527155 : Blo 630300 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B3209543 : Blo 630300 3209543 := bstep (se 1 (by rfl) ⟨2407157, by rfl⟩ : syracuseStep 3209543 = 4814315) B4814315
theorem B950495 : Blo 630300 950495 := bstep (se 1 (by rfl) ⟨712871, by rfl⟩ : syracuseStep 950495 = 1425743) B1425743
theorem B7209809 : Blo 630300 7209809 := bstep (se 2 (by rfl) ⟨2703678, by rfl⟩ : syracuseStep 7209809 = 5407357) B5407357
theorem B6063443 : Blo 630300 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B51940055 : Blo 630300 51940055 := bstep (se 1 (by rfl) ⟨38955041, by rfl⟩ : syracuseStep 51940055 = 77910083) B77910083
theorem B27792089 : Blo 630300 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B262083451 : Blo 630300 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B630783 : Blo 630300 630783 := bstep (se 1 (by rfl) ⟨473087, by rfl⟩ : syracuseStep 630783 = 946175) B946175
theorem B13018103 : Blo 630300 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B2139695 : Blo 630300 2139695 := bstep (se 1 (by rfl) ⟨1604771, by rfl⟩ : syracuseStep 2139695 = 3209543) B3209543
theorem B3422519 : Blo 630300 3422519 := bstep (se 1 (by rfl) ⟨2566889, by rfl⟩ : syracuseStep 3422519 = 5133779) B5133779
theorem B2703527 : Blo 630300 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B1426715 : Blo 630300 1426715 := bstep (se 1 (by rfl) ⟨1070036, by rfl⟩ : syracuseStep 1426715 = 2140073) B2140073
theorem B1623899 : Blo 630300 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B2738843 : Blo 630300 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B4313807 : Blo 630300 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B1367759 : Blo 630300 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B29155139 : Blo 630300 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B16179425 : Blo 630300 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B6250807 : Blo 630300 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B2025299 : Blo 630300 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B3598505 : Blo 630300 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B3041563 : Blo 630300 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B946079 : Blo 630300 946079 := bstep (se 1 (by rfl) ⟨709559, by rfl⟩ : syracuseStep 946079 = 1419119) B1419119
theorem B947567 : Blo 630300 947567 := bstep (se 1 (by rfl) ⟨710675, by rfl⟩ : syracuseStep 947567 = 1421351) B1421351
theorem B3208895 : Blo 630300 3208895 := bstep (se 1 (by rfl) ⟨2406671, by rfl⟩ : syracuseStep 3208895 = 4813343) B4813343
theorem B3209705 : Blo 630300 3209705 := bstep (se 2 (by rfl) ⟨1203639, by rfl⟩ : syracuseStep 3209705 = 2407279) B2407279
theorem B16218791 : Blo 630300 16218791 := bstep (se 1 (by rfl) ⟨12164093, by rfl⟩ : syracuseStep 16218791 = 24328187) B24328187
theorem B1802351 : Blo 630300 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B951143 : Blo 630300 951143 := bstep (se 1 (by rfl) ⟨713357, by rfl⟩ : syracuseStep 951143 = 1426715) B1426715
theorem B4330397 : Blo 630300 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B19436759 : Blo 630300 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B10786283 : Blo 630300 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B349444601 : Blo 630300 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B1350199 : Blo 630300 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B2399003 : Blo 630300 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B630719 : Blo 630300 630719 := bstep (se 1 (by rfl) ⟨473039, by rfl⟩ : syracuseStep 630719 = 946079) B946079
theorem B631711 : Blo 630300 631711 := bstep (se 1 (by rfl) ⟨473783, by rfl⟩ : syracuseStep 631711 = 947567) B947567
theorem B2139263 : Blo 630300 2139263 := bstep (se 1 (by rfl) ⟨1604447, by rfl⟩ : syracuseStep 2139263 = 3208895) B3208895
theorem B2139803 : Blo 630300 2139803 := bstep (se 1 (by rfl) ⟨1604852, by rfl⟩ : syracuseStep 2139803 = 3209705) B3209705
theorem B633663 : Blo 630300 633663 := bstep (se 1 (by rfl) ⟨475247, by rfl⟩ : syracuseStep 633663 = 950495) B950495
theorem B8334409 : Blo 630300 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B4042295 : Blo 630300 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B18528059 : Blo 630300 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B1426463 : Blo 630300 1426463 := bstep (se 1 (by rfl) ⟨1069847, by rfl⟩ : syracuseStep 1426463 = 2139695) B2139695
theorem B2281679 : Blo 630300 2281679 := bstep (se 1 (by rfl) ⟨1711259, by rfl⟩ : syracuseStep 2281679 = 3422519) B3422519
theorem B4806539 : Blo 630300 4806539 := bstep (se 1 (by rfl) ⟨3604904, by rfl⟩ : syracuseStep 4806539 = 7209809) B7209809
theorem B1825895 : Blo 630300 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B34626703 : Blo 630300 34626703 := bstep (se 1 (by rfl) ⟨25970027, by rfl⟩ : syracuseStep 34626703 = 51940055) B51940055
theorem B4055417 : Blo 630300 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B2875871 : Blo 630300 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B911839 : Blo 630300 911839 := bstep (se 1 (by rfl) ⟨683879, by rfl⟩ : syracuseStep 911839 = 1367759) B1367759
theorem B8678735 : Blo 630300 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B10812527 : Blo 630300 10812527 := bstep (se 1 (by rfl) ⟨8109395, by rfl⟩ : syracuseStep 10812527 = 16218791) B16218791
theorem B950975 : Blo 630300 950975 := bstep (se 1 (by rfl) ⟨713231, by rfl⟩ : syracuseStep 950975 = 1426463) B1426463
theorem B7668989 : Blo 630300 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B2886931 : Blo 630300 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B1215785 : Blo 630300 1215785 := bstep (se 2 (by rfl) ⟨455919, by rfl⟩ : syracuseStep 1215785 = 911839) B911839
theorem B11112545 : Blo 630300 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B1217263 : Blo 630300 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B2694863 : Blo 630300 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B634095 : Blo 630300 634095 := bstep (se 1 (by rfl) ⟨475571, by rfl⟩ : syracuseStep 634095 = 951143) B951143
theorem B1521119 : Blo 630300 1521119 := bstep (se 1 (by rfl) ⟨1140839, by rfl⟩ : syracuseStep 1521119 = 2281679) B2281679
theorem B12957839 : Blo 630300 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B7190855 : Blo 630300 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B232963067 : Blo 630300 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B2703611 : Blo 630300 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B1426175 : Blo 630300 1426175 := bstep (se 1 (by rfl) ⟨1069631, by rfl⟩ : syracuseStep 1426175 = 2139263) B2139263
theorem B1426535 : Blo 630300 1426535 := bstep (se 1 (by rfl) ⟨1069901, by rfl⟩ : syracuseStep 1426535 = 2139803) B2139803
theorem B5785823 : Blo 630300 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B1201567 : Blo 630300 1201567 := bstep (se 1 (by rfl) ⟨901175, by rfl⟩ : syracuseStep 1201567 = 1802351) B1802351
theorem B7201061 : Blo 630300 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B3204359 : Blo 630300 3204359 := bstep (se 1 (by rfl) ⟨2403269, by rfl⟩ : syracuseStep 3204359 = 4806539) B4806539
theorem B1599335 : Blo 630300 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B49408157 : Blo 630300 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B46168937 : Blo 630300 46168937 := bstep (se 2 (by rfl) ⟨17313351, by rfl⟩ : syracuseStep 46168937 = 34626703) B34626703
theorem B7208351 : Blo 630300 7208351 := bstep (se 1 (by rfl) ⟨5406263, by rfl⟩ : syracuseStep 7208351 = 10812527) B10812527
theorem B1802407 : Blo 630300 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B950783 : Blo 630300 950783 := bstep (se 1 (by rfl) ⟨713087, by rfl⟩ : syracuseStep 950783 = 1426175) B1426175
theorem B951023 : Blo 630300 951023 := bstep (se 1 (by rfl) ⟨713267, by rfl⟩ : syracuseStep 951023 = 1426535) B1426535
theorem B5112659 : Blo 630300 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B7408363 : Blo 630300 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B2136239 : Blo 630300 2136239 := bstep (se 1 (by rfl) ⟨1602179, by rfl⟩ : syracuseStep 2136239 = 3204359) B3204359
theorem B4793903 : Blo 630300 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B30779291 : Blo 630300 30779291 := bstep (se 1 (by rfl) ⟨23084468, by rfl⟩ : syracuseStep 30779291 = 46168937) B46168937
theorem B633983 : Blo 630300 633983 := bstep (se 1 (by rfl) ⟨475487, by rfl⟩ : syracuseStep 633983 = 950975) B950975
theorem B3849241 : Blo 630300 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B4800707 : Blo 630300 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1623017 : Blo 630300 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B1066223 : Blo 630300 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B8638559 : Blo 630300 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B155308711 : Blo 630300 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B4805567 : Blo 630300 4805567 := bstep (se 1 (by rfl) ⟨3604175, by rfl⟩ : syracuseStep 4805567 = 7208351) B7208351
theorem B3857215 : Blo 630300 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B810523 : Blo 630300 810523 := bstep (se 1 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 810523 = 1215785) B1215785
theorem B4056317 : Blo 630300 4056317 := bstep (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) B1521119
theorem B1796575 : Blo 630300 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B131755085 : Blo 630300 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B1602089 : Blo 630300 1602089 := bstep (se 2 (by rfl) ⟨600783, by rfl⟩ : syracuseStep 1602089 = 1201567) B1201567
theorem B1082011 : Blo 630300 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B13633757 : Blo 630300 13633757 := bstep (se 3 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 13633757 = 5112659) B5112659
theorem B2395433 : Blo 630300 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B20519527 : Blo 630300 20519527 := bstep (se 1 (by rfl) ⟨15389645, by rfl⟩ : syracuseStep 20519527 = 30779291) B30779291
theorem B2403209 : Blo 630300 2403209 := bstep (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) B1802407
theorem B633855 : Blo 630300 633855 := bstep (se 1 (by rfl) ⟨475391, by rfl⟩ : syracuseStep 633855 = 950783) B950783
theorem B634015 : Blo 630300 634015 := bstep (se 1 (by rfl) ⟨475511, by rfl⟩ : syracuseStep 634015 = 951023) B951023
theorem B9877817 : Blo 630300 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B1424159 : Blo 630300 1424159 := bstep (se 1 (by rfl) ⟨1068119, by rfl⟩ : syracuseStep 1424159 = 2136239) B2136239
theorem B2704211 : Blo 630300 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B207078281 : Blo 630300 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B3195935 : Blo 630300 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B87836723 : Blo 630300 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B1068059 : Blo 630300 1068059 := bstep (se 1 (by rfl) ⟨801044, by rfl⟩ : syracuseStep 1068059 = 1602089) B1602089
theorem B5132321 : Blo 630300 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B3200471 : Blo 630300 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B710815 : Blo 630300 710815 := bstep (se 1 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 710815 = 1066223) B1066223
theorem B5759039 : Blo 630300 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B3203711 : Blo 630300 3203711 := bstep (se 1 (by rfl) ⟨2402783, by rfl⟩ : syracuseStep 3203711 = 4805567) B4805567
theorem B5142953 : Blo 630300 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B1080697 : Blo 630300 1080697 := bstep (se 2 (by rfl) ⟨405261, by rfl⟩ : syracuseStep 1080697 = 810523) B810523
theorem B1802807 : Blo 630300 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B138052187 : Blo 630300 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B2130623 : Blo 630300 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B1442681 : Blo 630300 1442681 := bstep (se 2 (by rfl) ⟨541005, by rfl⟩ : syracuseStep 1442681 = 1082011) B1082011
theorem B58557815 : Blo 630300 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B2133647 : Blo 630300 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B3839359 : Blo 630300 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B2135807 : Blo 630300 2135807 := bstep (se 1 (by rfl) ⟨1601855, by rfl⟩ : syracuseStep 2135807 = 3203711) B3203711
theorem B9089171 : Blo 630300 9089171 := bstep (se 1 (by rfl) ⟨6816878, by rfl⟩ : syracuseStep 9089171 = 13633757) B13633757
theorem B3421547 : Blo 630300 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B13714541 : Blo 630300 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B712039 : Blo 630300 712039 := bstep (se 1 (by rfl) ⟨534029, by rfl⟩ : syracuseStep 712039 = 1068059) B1068059
theorem B1596955 : Blo 630300 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B1602139 : Blo 630300 1602139 := bstep (se 1 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 1602139 = 2403209) B2403209
theorem B947753 : Blo 630300 947753 := bstep (se 2 (by rfl) ⟨355407, by rfl⟩ : syracuseStep 947753 = 710815) B710815
theorem B27359369 : Blo 630300 27359369 := bstep (se 2 (by rfl) ⟨10259763, by rfl⟩ : syracuseStep 27359369 = 20519527) B20519527
theorem B6585211 : Blo 630300 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B1440929 : Blo 630300 1440929 := bstep (se 2 (by rfl) ⟨540348, by rfl⟩ : syracuseStep 1440929 = 1080697) B1080697
theorem B949439 : Blo 630300 949439 := bstep (se 1 (by rfl) ⟨712079, by rfl⟩ : syracuseStep 949439 = 1424159) B1424159
theorem B9143027 : Blo 630300 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B2136185 : Blo 630300 2136185 := bstep (se 2 (by rfl) ⟨801069, by rfl⟩ : syracuseStep 2136185 = 1602139) B1602139
theorem B5119145 : Blo 630300 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B3842477 : Blo 630300 3842477 := bstep (se 3 (by rfl) ⟨720464, by rfl⟩ : syracuseStep 3842477 = 1440929) B1440929
theorem B631835 : Blo 630300 631835 := bstep (se 1 (by rfl) ⟨473876, by rfl⟩ : syracuseStep 631835 = 947753) B947753
theorem B632959 : Blo 630300 632959 := bstep (se 1 (by rfl) ⟨474719, by rfl⟩ : syracuseStep 632959 = 949439) B949439
theorem B1420415 : Blo 630300 1420415 := bstep (se 1 (by rfl) ⟨1065311, by rfl⟩ : syracuseStep 1420415 = 2130623) B2130623
theorem B961787 : Blo 630300 961787 := bstep (se 1 (by rfl) ⟨721340, by rfl⟩ : syracuseStep 961787 = 1442681) B1442681
theorem B39038543 : Blo 630300 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B1422431 : Blo 630300 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B1423871 : Blo 630300 1423871 := bstep (se 1 (by rfl) ⟨1067903, by rfl⟩ : syracuseStep 1423871 = 2135807) B2135807
theorem B2281031 : Blo 630300 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B18239579 : Blo 630300 18239579 := bstep (se 1 (by rfl) ⟨13679684, by rfl⟩ : syracuseStep 18239579 = 27359369) B27359369
theorem B1201871 : Blo 630300 1201871 := bstep (se 1 (by rfl) ⟨901403, by rfl⟩ : syracuseStep 1201871 = 1802807) B1802807
theorem B92034791 : Blo 630300 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B6059447 : Blo 630300 6059447 := bstep (se 1 (by rfl) ⟨4544585, by rfl⟩ : syracuseStep 6059447 = 9089171) B9089171
theorem B8780281 : Blo 630300 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B949385 : Blo 630300 949385 := bstep (se 2 (by rfl) ⟨356019, by rfl⟩ : syracuseStep 949385 = 712039) B712039
theorem B2129273 : Blo 630300 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B6095351 : Blo 630300 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B46828165 : Blo 630300 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B12159719 : Blo 630300 12159719 := bstep (se 1 (by rfl) ⟨9119789, by rfl⟩ : syracuseStep 12159719 = 18239579) B18239579
theorem B3412763 : Blo 630300 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B2561651 : Blo 630300 2561651 := bstep (se 1 (by rfl) ⟨1921238, by rfl⟩ : syracuseStep 2561651 = 3842477) B3842477
theorem B26025695 : Blo 630300 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B4039631 : Blo 630300 4039631 := bstep (se 1 (by rfl) ⟨3029723, by rfl⟩ : syracuseStep 4039631 = 6059447) B6059447
theorem B632923 : Blo 630300 632923 := bstep (se 1 (by rfl) ⟨474692, by rfl⟩ : syracuseStep 632923 = 949385) B949385
theorem B1419515 : Blo 630300 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B1520687 : Blo 630300 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B801247 : Blo 630300 801247 := bstep (se 1 (by rfl) ⟨600935, by rfl⟩ : syracuseStep 801247 = 1201871) B1201871
theorem B61356527 : Blo 630300 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B1424123 : Blo 630300 1424123 := bstep (se 1 (by rfl) ⟨1068092, by rfl⟩ : syracuseStep 1424123 = 2136185) B2136185
theorem B641191 : Blo 630300 641191 := bstep (se 1 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 641191 = 961787) B961787
theorem B946943 : Blo 630300 946943 := bstep (se 1 (by rfl) ⟨710207, by rfl⟩ : syracuseStep 946943 = 1420415) B1420415
theorem B948287 : Blo 630300 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B949247 : Blo 630300 949247 := bstep (se 1 (by rfl) ⟨711935, by rfl⟩ : syracuseStep 949247 = 1423871) B1423871
theorem B4063567 : Blo 630300 4063567 := bstep (se 1 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 4063567 = 6095351) B6095351
theorem B854921 : Blo 630300 854921 := bstep (se 2 (by rfl) ⟨320595, by rfl⟩ : syracuseStep 854921 = 641191) B641191
theorem B1707767 : Blo 630300 1707767 := bstep (se 1 (by rfl) ⟨1280825, by rfl⟩ : syracuseStep 1707767 = 2561651) B2561651
theorem B2693087 : Blo 630300 2693087 := bstep (se 1 (by rfl) ⟨2019815, by rfl⟩ : syracuseStep 2693087 = 4039631) B4039631
theorem B631295 : Blo 630300 631295 := bstep (se 1 (by rfl) ⟨473471, by rfl⟩ : syracuseStep 631295 = 946943) B946943
theorem B632191 : Blo 630300 632191 := bstep (se 1 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 632191 = 948287) B948287
theorem B40904351 : Blo 630300 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B632831 : Blo 630300 632831 := bstep (se 1 (by rfl) ⟨474623, by rfl⟩ : syracuseStep 632831 = 949247) B949247
theorem B8106479 : Blo 630300 8106479 := bstep (se 1 (by rfl) ⟨6079859, by rfl⟩ : syracuseStep 8106479 = 12159719) B12159719
theorem B2275175 : Blo 630300 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B62437553 : Blo 630300 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B17350463 : Blo 630300 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B1068329 : Blo 630300 1068329 := bstep (se 2 (by rfl) ⟨400623, by rfl⟩ : syracuseStep 1068329 = 801247) B801247
theorem B946343 : Blo 630300 946343 := bstep (se 1 (by rfl) ⟨709757, by rfl⟩ : syracuseStep 946343 = 1419515) B1419515
theorem B1013791 : Blo 630300 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B949415 : Blo 630300 949415 := bstep (se 1 (by rfl) ⟨712061, by rfl⟩ : syracuseStep 949415 = 1424123) B1424123
theorem B6067133 : Blo 630300 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B27269567 : Blo 630300 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B1351721 : Blo 630300 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B630895 : Blo 630300 630895 := bstep (se 1 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 630895 = 946343) B946343
theorem B41625035 : Blo 630300 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B632943 : Blo 630300 632943 := bstep (se 1 (by rfl) ⟨474707, by rfl⟩ : syracuseStep 632943 = 949415) B949415
theorem B5418089 : Blo 630300 5418089 := bstep (se 2 (by rfl) ⟨2031783, by rfl⟩ : syracuseStep 5418089 = 4063567) B4063567
theorem B2279789 : Blo 630300 2279789 := bstep (se 3 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 2279789 = 854921) B854921
theorem B712219 : Blo 630300 712219 := bstep (se 1 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 712219 = 1068329) B1068329
theorem B1138511 : Blo 630300 1138511 := bstep (se 1 (by rfl) ⟨853883, by rfl⟩ : syracuseStep 1138511 = 1707767) B1707767
theorem B1795391 : Blo 630300 1795391 := bstep (se 1 (by rfl) ⟨1346543, by rfl⟩ : syracuseStep 1795391 = 2693087) B2693087
theorem B5404319 : Blo 630300 5404319 := bstep (se 1 (by rfl) ⟨4053239, by rfl⟩ : syracuseStep 5404319 = 8106479) B8106479
theorem B11566975 : Blo 630300 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B759007 : Blo 630300 759007 := bstep (se 1 (by rfl) ⟨569255, by rfl⟩ : syracuseStep 759007 = 1138511) B1138511
theorem B3612059 : Blo 630300 3612059 := bstep (se 1 (by rfl) ⟨2709044, by rfl⟩ : syracuseStep 3612059 = 5418089) B5418089
theorem B1519859 : Blo 630300 1519859 := bstep (se 1 (by rfl) ⟨1139894, by rfl⟩ : syracuseStep 1519859 = 2279789) B2279789
theorem B4044755 : Blo 630300 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B901147 : Blo 630300 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B1196927 : Blo 630300 1196927 := bstep (se 1 (by rfl) ⟨897695, by rfl⟩ : syracuseStep 1196927 = 1795391) B1795391
theorem B15422633 : Blo 630300 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B18179711 : Blo 630300 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B27750023 : Blo 630300 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B3602879 : Blo 630300 3602879 := bstep (se 1 (by rfl) ⟨2702159, by rfl⟩ : syracuseStep 3602879 = 5404319) B5404319
theorem B949625 : Blo 630300 949625 := bstep (se 2 (by rfl) ⟨356109, by rfl⟩ : syracuseStep 949625 = 712219) B712219
theorem B2696503 : Blo 630300 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B2401919 : Blo 630300 2401919 := bstep (se 1 (by rfl) ⟨1801439, by rfl⟩ : syracuseStep 2401919 = 3602879) B3602879
theorem B633083 : Blo 630300 633083 := bstep (se 1 (by rfl) ⟨474812, by rfl⟩ : syracuseStep 633083 = 949625) B949625
theorem B797951 : Blo 630300 797951 := bstep (se 1 (by rfl) ⟨598463, by rfl⟩ : syracuseStep 797951 = 1196927) B1196927
theorem B2408039 : Blo 630300 2408039 := bstep (se 1 (by rfl) ⟨1806029, by rfl⟩ : syracuseStep 2408039 = 3612059) B3612059
theorem B18500015 : Blo 630300 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B1201529 : Blo 630300 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B10281755 : Blo 630300 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B12119807 : Blo 630300 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B1012009 : Blo 630300 1012009 := bstep (se 2 (by rfl) ⟨379503, by rfl⟩ : syracuseStep 1012009 = 759007) B759007
theorem B1013239 : Blo 630300 1013239 := bstep (se 1 (by rfl) ⟨759929, by rfl⟩ : syracuseStep 1013239 = 1519859) B1519859
theorem B1349345 : Blo 630300 1349345 := bstep (se 2 (by rfl) ⟨506004, by rfl⟩ : syracuseStep 1349345 = 1012009) B1012009
theorem B6854503 : Blo 630300 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B12333343 : Blo 630300 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B801019 : Blo 630300 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B8079871 : Blo 630300 8079871 := bstep (se 1 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 8079871 = 12119807) B12119807
theorem B3595337 : Blo 630300 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B1601279 : Blo 630300 1601279 := bstep (se 1 (by rfl) ⟨1200959, by rfl⟩ : syracuseStep 1601279 = 2401919) B2401919
theorem B5403941 : Blo 630300 5403941 := bstep (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) B1013239
theorem B2127869 : Blo 630300 2127869 := bstep (se 3 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 2127869 = 797951) B797951
theorem B1605359 : Blo 630300 1605359 := bstep (se 1 (by rfl) ⟨1204019, by rfl⟩ : syracuseStep 1605359 = 2408039) B2408039
theorem B2396891 : Blo 630300 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B1418579 : Blo 630300 1418579 := bstep (se 1 (by rfl) ⟨1063934, by rfl⟩ : syracuseStep 1418579 = 2127869) B2127869
theorem B1067519 : Blo 630300 1067519 := bstep (se 1 (by rfl) ⟨800639, by rfl⟩ : syracuseStep 1067519 = 1601279) B1601279
theorem B1068025 : Blo 630300 1068025 := bstep (se 2 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 1068025 = 801019) B801019
theorem B1070239 : Blo 630300 1070239 := bstep (se 1 (by rfl) ⟨802679, by rfl⟩ : syracuseStep 1070239 = 1605359) B1605359
theorem B10773161 : Blo 630300 10773161 := bstep (se 2 (by rfl) ⟨4039935, by rfl⟩ : syracuseStep 10773161 = 8079871) B8079871
theorem B3598253 : Blo 630300 3598253 := bstep (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) B1349345
theorem B16444457 : Blo 630300 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B9139337 : Blo 630300 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B3602627 : Blo 630300 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B7182107 : Blo 630300 7182107 := bstep (se 1 (by rfl) ⟨5386580, by rfl⟩ : syracuseStep 7182107 = 10773161) B10773161
theorem B2398835 : Blo 630300 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B2401751 : Blo 630300 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B1424033 : Blo 630300 1424033 := bstep (se 2 (by rfl) ⟨534012, by rfl⟩ : syracuseStep 1424033 = 1068025) B1068025
theorem B1426985 : Blo 630300 1426985 := bstep (se 2 (by rfl) ⟨535119, by rfl⟩ : syracuseStep 1426985 = 1070239) B1070239
theorem B10962971 : Blo 630300 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B711679 : Blo 630300 711679 := bstep (se 1 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 711679 = 1067519) B1067519
theorem B1597927 : Blo 630300 1597927 := bstep (se 1 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 1597927 = 2396891) B2396891
theorem B945719 : Blo 630300 945719 := bstep (se 1 (by rfl) ⟨709289, by rfl⟩ : syracuseStep 945719 = 1418579) B1418579
theorem B6092891 : Blo 630300 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B2130569 : Blo 630300 2130569 := bstep (se 2 (by rfl) ⟨798963, by rfl⟩ : syracuseStep 2130569 = 1597927) B1597927
theorem B951323 : Blo 630300 951323 := bstep (se 1 (by rfl) ⟨713492, by rfl⟩ : syracuseStep 951323 = 1426985) B1426985
theorem B7308647 : Blo 630300 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B4788071 : Blo 630300 4788071 := bstep (se 1 (by rfl) ⟨3591053, by rfl⟩ : syracuseStep 4788071 = 7182107) B7182107
theorem B630479 : Blo 630300 630479 := bstep (se 1 (by rfl) ⟨472859, by rfl⟩ : syracuseStep 630479 = 945719) B945719
theorem B1599223 : Blo 630300 1599223 := bstep (se 1 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 1599223 = 2398835) B2398835
theorem B1601167 : Blo 630300 1601167 := bstep (se 1 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 1601167 = 2401751) B2401751
theorem B948905 : Blo 630300 948905 := bstep (se 2 (by rfl) ⟨355839, by rfl⟩ : syracuseStep 948905 = 711679) B711679
theorem B4061927 : Blo 630300 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B949355 : Blo 630300 949355 := bstep (se 1 (by rfl) ⟨712016, by rfl⟩ : syracuseStep 949355 = 1424033) B1424033
theorem B2132297 : Blo 630300 2132297 := bstep (se 2 (by rfl) ⟨799611, by rfl⟩ : syracuseStep 2132297 = 1599223) B1599223
theorem B2134889 : Blo 630300 2134889 := bstep (se 2 (by rfl) ⟨800583, by rfl⟩ : syracuseStep 2134889 = 1601167) B1601167
theorem B632603 : Blo 630300 632603 := bstep (se 1 (by rfl) ⟨474452, by rfl⟩ : syracuseStep 632603 = 948905) B948905
theorem B632903 : Blo 630300 632903 := bstep (se 1 (by rfl) ⟨474677, by rfl⟩ : syracuseStep 632903 = 949355) B949355
theorem B1420379 : Blo 630300 1420379 := bstep (se 1 (by rfl) ⟨1065284, by rfl⟩ : syracuseStep 1420379 = 2130569) B2130569
theorem B634215 : Blo 630300 634215 := bstep (se 1 (by rfl) ⟨475661, by rfl⟩ : syracuseStep 634215 = 951323) B951323
theorem B3192047 : Blo 630300 3192047 := bstep (se 1 (by rfl) ⟨2394035, by rfl⟩ : syracuseStep 3192047 = 4788071) B4788071
theorem B2707951 : Blo 630300 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B4872431 : Blo 630300 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B3610601 : Blo 630300 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B1421531 : Blo 630300 1421531 := bstep (se 1 (by rfl) ⟨1066148, by rfl⟩ : syracuseStep 1421531 = 2132297) B2132297
theorem B1423259 : Blo 630300 1423259 := bstep (se 1 (by rfl) ⟨1067444, by rfl⟩ : syracuseStep 1423259 = 2134889) B2134889
theorem B12993149 : Blo 630300 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B946919 : Blo 630300 946919 := bstep (se 1 (by rfl) ⟨710189, by rfl⟩ : syracuseStep 946919 = 1420379) B1420379
theorem B2128031 : Blo 630300 2128031 := bstep (se 1 (by rfl) ⟨1596023, by rfl⟩ : syracuseStep 2128031 = 3192047) B3192047
theorem B631279 : Blo 630300 631279 := bstep (se 1 (by rfl) ⟨473459, by rfl⟩ : syracuseStep 631279 = 946919) B946919
theorem B1418687 : Blo 630300 1418687 := bstep (se 1 (by rfl) ⟨1064015, by rfl⟩ : syracuseStep 1418687 = 2128031) B2128031
theorem B8662099 : Blo 630300 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B2407067 : Blo 630300 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B947687 : Blo 630300 947687 := bstep (se 1 (by rfl) ⟨710765, by rfl⟩ : syracuseStep 947687 = 1421531) B1421531
theorem B948839 : Blo 630300 948839 := bstep (se 1 (by rfl) ⟨711629, by rfl⟩ : syracuseStep 948839 = 1423259) B1423259
theorem B631791 : Blo 630300 631791 := bstep (se 1 (by rfl) ⟨473843, by rfl⟩ : syracuseStep 631791 = 947687) B947687
theorem B632559 : Blo 630300 632559 := bstep (se 1 (by rfl) ⟨474419, by rfl⟩ : syracuseStep 632559 = 948839) B948839
theorem B11549465 : Blo 630300 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B945791 : Blo 630300 945791 := bstep (se 1 (by rfl) ⟨709343, by rfl⟩ : syracuseStep 945791 = 1418687) B1418687
theorem B1604711 : Blo 630300 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B630527 : Blo 630300 630527 := bstep (se 1 (by rfl) ⟨472895, by rfl⟩ : syracuseStep 630527 = 945791) B945791
theorem B1069807 : Blo 630300 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B7699643 : Blo 630300 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B1426409 : Blo 630300 1426409 := bstep (se 2 (by rfl) ⟨534903, by rfl⟩ : syracuseStep 1426409 = 1069807) B1069807
theorem B5133095 : Blo 630300 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B950939 : Blo 630300 950939 := bstep (se 1 (by rfl) ⟨713204, by rfl⟩ : syracuseStep 950939 = 1426409) B1426409
theorem B3422063 : Blo 630300 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B633959 : Blo 630300 633959 := bstep (se 1 (by rfl) ⟨475469, by rfl⟩ : syracuseStep 633959 = 950939) B950939
theorem B2281375 : Blo 630300 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B3041833 : Blo 630300 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B4055777 : Blo 630300 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B2703851 : Blo 630300 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B1802567 : Blo 630300 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B1201711 : Blo 630300 1201711 := bstep (se 1 (by rfl) ⟨901283, by rfl⟩ : syracuseStep 1201711 = 1802567) B1802567
theorem B1602281 : Blo 630300 1602281 := bstep (se 2 (by rfl) ⟨600855, by rfl⟩ : syracuseStep 1602281 = 1201711) B1201711
theorem B1068187 : Blo 630300 1068187 := bstep (se 1 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 1068187 = 1602281) B1602281
theorem B1424249 : Blo 630300 1424249 := bstep (se 2 (by rfl) ⟨534093, by rfl⟩ : syracuseStep 1424249 = 1068187) B1068187
theorem B949499 : Blo 630300 949499 := bstep (se 1 (by rfl) ⟨712124, by rfl⟩ : syracuseStep 949499 = 1424249) B1424249
theorem B632999 : Blo 630300 632999 := bstep (se 1 (by rfl) ⟨474749, by rfl⟩ : syracuseStep 632999 = 949499) B949499

theorem C0 (j : ℕ) (h1 : 157575 ≤ j) (h2 : j ≤ 158274) : Blo 630300 (4 * j + 3) := by
  interval_cases j
  · exact B630303
  · exact B630307
  · exact B630311
  · exact B630315
  · exact B630319
  · exact B630323
  · exact B630327
  · exact B630331
  · exact B630335
  · exact B630339
  · exact B630343
  · exact B630347
  · exact B630351
  · exact B630355
  · exact B630359
  · exact B630363
  · exact B630367
  · exact B630371
  · exact B630375
  · exact B630379
  · exact B630383
  · exact B630387
  · exact B630391
  · exact B630395
  · exact B630399
  · exact B630403
  · exact B630407
  · exact B630411
  · exact B630415
  · exact B630419
  · exact B630423
  · exact B630427
  · exact B630431
  · exact B630435
  · exact B630439
  · exact B630443
  · exact B630447
  · exact B630451
  · exact B630455
  · exact B630459
  · exact B630463
  · exact B630467
  · exact B630471
  · exact B630475
  · exact B630479
  · exact B630483
  · exact B630487
  · exact B630491
  · exact B630495
  · exact B630499
  · exact B630503
  · exact B630507
  · exact B630511
  · exact B630515
  · exact B630519
  · exact B630523
  · exact B630527
  · exact B630531
  · exact B630535
  · exact B630539
  · exact B630543
  · exact B630547
  · exact B630551
  · exact B630555
  · exact B630559
  · exact B630563
  · exact B630567
  · exact B630571
  · exact B630575
  · exact B630579
  · exact B630583
  · exact B630587
  · exact B630591
  · exact B630595
  · exact B630599
  · exact B630603
  · exact B630607
  · exact B630611
  · exact B630615
  · exact B630619
  · exact B630623
  · exact B630627
  · exact B630631
  · exact B630635
  · exact B630639
  · exact B630643
  · exact B630647
  · exact B630651
  · exact B630655
  · exact B630659
  · exact B630663
  · exact B630667
  · exact B630671
  · exact B630675
  · exact B630679
  · exact B630683
  · exact B630687
  · exact B630691
  · exact B630695
  · exact B630699
  · exact B630703
  · exact B630707
  · exact B630711
  · exact B630715
  · exact B630719
  · exact B630723
  · exact B630727
  · exact B630731
  · exact B630735
  · exact B630739
  · exact B630743
  · exact B630747
  · exact B630751
  · exact B630755
  · exact B630759
  · exact B630763
  · exact B630767
  · exact B630771
  · exact B630775
  · exact B630779
  · exact B630783
  · exact B630787
  · exact B630791
  · exact B630795
  · exact B630799
  · exact B630803
  · exact B630807
  · exact B630811
  · exact B630815
  · exact B630819
  · exact B630823
  · exact B630827
  · exact B630831
  · exact B630835
  · exact B630839
  · exact B630843
  · exact B630847
  · exact B630851
  · exact B630855
  · exact B630859
  · exact B630863
  · exact B630867
  · exact B630871
  · exact B630875
  · exact B630879
  · exact B630883
  · exact B630887
  · exact B630891
  · exact B630895
  · exact B630899
  · exact B630903
  · exact B630907
  · exact B630911
  · exact B630915
  · exact B630919
  · exact B630923
  · exact B630927
  · exact B630931
  · exact B630935
  · exact B630939
  · exact B630943
  · exact B630947
  · exact B630951
  · exact B630955
  · exact B630959
  · exact B630963
  · exact B630967
  · exact B630971
  · exact B630975
  · exact B630979
  · exact B630983
  · exact B630987
  · exact B630991
  · exact B630995
  · exact B630999
  · exact B631003
  · exact B631007
  · exact B631011
  · exact B631015
  · exact B631019
  · exact B631023
  · exact B631027
  · exact B631031
  · exact B631035
  · exact B631039
  · exact B631043
  · exact B631047
  · exact B631051
  · exact B631055
  · exact B631059
  · exact B631063
  · exact B631067
  · exact B631071
  · exact B631075
  · exact B631079
  · exact B631083
  · exact B631087
  · exact B631091
  · exact B631095
  · exact B631099
  · exact B631103
  · exact B631107
  · exact B631111
  · exact B631115
  · exact B631119
  · exact B631123
  · exact B631127
  · exact B631131
  · exact B631135
  · exact B631139
  · exact B631143
  · exact B631147
  · exact B631151
  · exact B631155
  · exact B631159
  · exact B631163
  · exact B631167
  · exact B631171
  · exact B631175
  · exact B631179
  · exact B631183
  · exact B631187
  · exact B631191
  · exact B631195
  · exact B631199
  · exact B631203
  · exact B631207
  · exact B631211
  · exact B631215
  · exact B631219
  · exact B631223
  · exact B631227
  · exact B631231
  · exact B631235
  · exact B631239
  · exact B631243
  · exact B631247
  · exact B631251
  · exact B631255
  · exact B631259
  · exact B631263
  · exact B631267
  · exact B631271
  · exact B631275
  · exact B631279
  · exact B631283
  · exact B631287
  · exact B631291
  · exact B631295
  · exact B631299
  · exact B631303
  · exact B631307
  · exact B631311
  · exact B631315
  · exact B631319
  · exact B631323
  · exact B631327
  · exact B631331
  · exact B631335
  · exact B631339
  · exact B631343
  · exact B631347
  · exact B631351
  · exact B631355
  · exact B631359
  · exact B631363
  · exact B631367
  · exact B631371
  · exact B631375
  · exact B631379
  · exact B631383
  · exact B631387
  · exact B631391
  · exact B631395
  · exact B631399
  · exact B631403
  · exact B631407
  · exact B631411
  · exact B631415
  · exact B631419
  · exact B631423
  · exact B631427
  · exact B631431
  · exact B631435
  · exact B631439
  · exact B631443
  · exact B631447
  · exact B631451
  · exact B631455
  · exact B631459
  · exact B631463
  · exact B631467
  · exact B631471
  · exact B631475
  · exact B631479
  · exact B631483
  · exact B631487
  · exact B631491
  · exact B631495
  · exact B631499
  · exact B631503
  · exact B631507
  · exact B631511
  · exact B631515
  · exact B631519
  · exact B631523
  · exact B631527
  · exact B631531
  · exact B631535
  · exact B631539
  · exact B631543
  · exact B631547
  · exact B631551
  · exact B631555
  · exact B631559
  · exact B631563
  · exact B631567
  · exact B631571
  · exact B631575
  · exact B631579
  · exact B631583
  · exact B631587
  · exact B631591
  · exact B631595
  · exact B631599
  · exact B631603
  · exact B631607
  · exact B631611
  · exact B631615
  · exact B631619
  · exact B631623
  · exact B631627
  · exact B631631
  · exact B631635
  · exact B631639
  · exact B631643
  · exact B631647
  · exact B631651
  · exact B631655
  · exact B631659
  · exact B631663
  · exact B631667
  · exact B631671
  · exact B631675
  · exact B631679
  · exact B631683
  · exact B631687
  · exact B631691
  · exact B631695
  · exact B631699
  · exact B631703
  · exact B631707
  · exact B631711
  · exact B631715
  · exact B631719
  · exact B631723
  · exact B631727
  · exact B631731
  · exact B631735
  · exact B631739
  · exact B631743
  · exact B631747
  · exact B631751
  · exact B631755
  · exact B631759
  · exact B631763
  · exact B631767
  · exact B631771
  · exact B631775
  · exact B631779
  · exact B631783
  · exact B631787
  · exact B631791
  · exact B631795
  · exact B631799
  · exact B631803
  · exact B631807
  · exact B631811
  · exact B631815
  · exact B631819
  · exact B631823
  · exact B631827
  · exact B631831
  · exact B631835
  · exact B631839
  · exact B631843
  · exact B631847
  · exact B631851
  · exact B631855
  · exact B631859
  · exact B631863
  · exact B631867
  · exact B631871
  · exact B631875
  · exact B631879
  · exact B631883
  · exact B631887
  · exact B631891
  · exact B631895
  · exact B631899
  · exact B631903
  · exact B631907
  · exact B631911
  · exact B631915
  · exact B631919
  · exact B631923
  · exact B631927
  · exact B631931
  · exact B631935
  · exact B631939
  · exact B631943
  · exact B631947
  · exact B631951
  · exact B631955
  · exact B631959
  · exact B631963
  · exact B631967
  · exact B631971
  · exact B631975
  · exact B631979
  · exact B631983
  · exact B631987
  · exact B631991
  · exact B631995
  · exact B631999
  · exact B632003
  · exact B632007
  · exact B632011
  · exact B632015
  · exact B632019
  · exact B632023
  · exact B632027
  · exact B632031
  · exact B632035
  · exact B632039
  · exact B632043
  · exact B632047
  · exact B632051
  · exact B632055
  · exact B632059
  · exact B632063
  · exact B632067
  · exact B632071
  · exact B632075
  · exact B632079
  · exact B632083
  · exact B632087
  · exact B632091
  · exact B632095
  · exact B632099
  · exact B632103
  · exact B632107
  · exact B632111
  · exact B632115
  · exact B632119
  · exact B632123
  · exact B632127
  · exact B632131
  · exact B632135
  · exact B632139
  · exact B632143
  · exact B632147
  · exact B632151
  · exact B632155
  · exact B632159
  · exact B632163
  · exact B632167
  · exact B632171
  · exact B632175
  · exact B632179
  · exact B632183
  · exact B632187
  · exact B632191
  · exact B632195
  · exact B632199
  · exact B632203
  · exact B632207
  · exact B632211
  · exact B632215
  · exact B632219
  · exact B632223
  · exact B632227
  · exact B632231
  · exact B632235
  · exact B632239
  · exact B632243
  · exact B632247
  · exact B632251
  · exact B632255
  · exact B632259
  · exact B632263
  · exact B632267
  · exact B632271
  · exact B632275
  · exact B632279
  · exact B632283
  · exact B632287
  · exact B632291
  · exact B632295
  · exact B632299
  · exact B632303
  · exact B632307
  · exact B632311
  · exact B632315
  · exact B632319
  · exact B632323
  · exact B632327
  · exact B632331
  · exact B632335
  · exact B632339
  · exact B632343
  · exact B632347
  · exact B632351
  · exact B632355
  · exact B632359
  · exact B632363
  · exact B632367
  · exact B632371
  · exact B632375
  · exact B632379
  · exact B632383
  · exact B632387
  · exact B632391
  · exact B632395
  · exact B632399
  · exact B632403
  · exact B632407
  · exact B632411
  · exact B632415
  · exact B632419
  · exact B632423
  · exact B632427
  · exact B632431
  · exact B632435
  · exact B632439
  · exact B632443
  · exact B632447
  · exact B632451
  · exact B632455
  · exact B632459
  · exact B632463
  · exact B632467
  · exact B632471
  · exact B632475
  · exact B632479
  · exact B632483
  · exact B632487
  · exact B632491
  · exact B632495
  · exact B632499
  · exact B632503
  · exact B632507
  · exact B632511
  · exact B632515
  · exact B632519
  · exact B632523
  · exact B632527
  · exact B632531
  · exact B632535
  · exact B632539
  · exact B632543
  · exact B632547
  · exact B632551
  · exact B632555
  · exact B632559
  · exact B632563
  · exact B632567
  · exact B632571
  · exact B632575
  · exact B632579
  · exact B632583
  · exact B632587
  · exact B632591
  · exact B632595
  · exact B632599
  · exact B632603
  · exact B632607
  · exact B632611
  · exact B632615
  · exact B632619
  · exact B632623
  · exact B632627
  · exact B632631
  · exact B632635
  · exact B632639
  · exact B632643
  · exact B632647
  · exact B632651
  · exact B632655
  · exact B632659
  · exact B632663
  · exact B632667
  · exact B632671
  · exact B632675
  · exact B632679
  · exact B632683
  · exact B632687
  · exact B632691
  · exact B632695
  · exact B632699
  · exact B632703
  · exact B632707
  · exact B632711
  · exact B632715
  · exact B632719
  · exact B632723
  · exact B632727
  · exact B632731
  · exact B632735
  · exact B632739
  · exact B632743
  · exact B632747
  · exact B632751
  · exact B632755
  · exact B632759
  · exact B632763
  · exact B632767
  · exact B632771
  · exact B632775
  · exact B632779
  · exact B632783
  · exact B632787
  · exact B632791
  · exact B632795
  · exact B632799
  · exact B632803
  · exact B632807
  · exact B632811
  · exact B632815
  · exact B632819
  · exact B632823
  · exact B632827
  · exact B632831
  · exact B632835
  · exact B632839
  · exact B632843
  · exact B632847
  · exact B632851
  · exact B632855
  · exact B632859
  · exact B632863
  · exact B632867
  · exact B632871
  · exact B632875
  · exact B632879
  · exact B632883
  · exact B632887
  · exact B632891
  · exact B632895
  · exact B632899
  · exact B632903
  · exact B632907
  · exact B632911
  · exact B632915
  · exact B632919
  · exact B632923
  · exact B632927
  · exact B632931
  · exact B632935
  · exact B632939
  · exact B632943
  · exact B632947
  · exact B632951
  · exact B632955
  · exact B632959
  · exact B632963
  · exact B632967
  · exact B632971
  · exact B632975
  · exact B632979
  · exact B632983
  · exact B632987
  · exact B632991
  · exact B632995
  · exact B632999
  · exact B633003
  · exact B633007
  · exact B633011
  · exact B633015
  · exact B633019
  · exact B633023
  · exact B633027
  · exact B633031
  · exact B633035
  · exact B633039
  · exact B633043
  · exact B633047
  · exact B633051
  · exact B633055
  · exact B633059
  · exact B633063
  · exact B633067
  · exact B633071
  · exact B633075
  · exact B633079
  · exact B633083
  · exact B633087
  · exact B633091
  · exact B633095
  · exact B633099

theorem C1 (j : ℕ) (h1 : 158275 ≤ j) (h2 : j ≤ 158574) : Blo 630300 (4 * j + 3) := by
  interval_cases j
  · exact B633103
  · exact B633107
  · exact B633111
  · exact B633115
  · exact B633119
  · exact B633123
  · exact B633127
  · exact B633131
  · exact B633135
  · exact B633139
  · exact B633143
  · exact B633147
  · exact B633151
  · exact B633155
  · exact B633159
  · exact B633163
  · exact B633167
  · exact B633171
  · exact B633175
  · exact B633179
  · exact B633183
  · exact B633187
  · exact B633191
  · exact B633195
  · exact B633199
  · exact B633203
  · exact B633207
  · exact B633211
  · exact B633215
  · exact B633219
  · exact B633223
  · exact B633227
  · exact B633231
  · exact B633235
  · exact B633239
  · exact B633243
  · exact B633247
  · exact B633251
  · exact B633255
  · exact B633259
  · exact B633263
  · exact B633267
  · exact B633271
  · exact B633275
  · exact B633279
  · exact B633283
  · exact B633287
  · exact B633291
  · exact B633295
  · exact B633299
  · exact B633303
  · exact B633307
  · exact B633311
  · exact B633315
  · exact B633319
  · exact B633323
  · exact B633327
  · exact B633331
  · exact B633335
  · exact B633339
  · exact B633343
  · exact B633347
  · exact B633351
  · exact B633355
  · exact B633359
  · exact B633363
  · exact B633367
  · exact B633371
  · exact B633375
  · exact B633379
  · exact B633383
  · exact B633387
  · exact B633391
  · exact B633395
  · exact B633399
  · exact B633403
  · exact B633407
  · exact B633411
  · exact B633415
  · exact B633419
  · exact B633423
  · exact B633427
  · exact B633431
  · exact B633435
  · exact B633439
  · exact B633443
  · exact B633447
  · exact B633451
  · exact B633455
  · exact B633459
  · exact B633463
  · exact B633467
  · exact B633471
  · exact B633475
  · exact B633479
  · exact B633483
  · exact B633487
  · exact B633491
  · exact B633495
  · exact B633499
  · exact B633503
  · exact B633507
  · exact B633511
  · exact B633515
  · exact B633519
  · exact B633523
  · exact B633527
  · exact B633531
  · exact B633535
  · exact B633539
  · exact B633543
  · exact B633547
  · exact B633551
  · exact B633555
  · exact B633559
  · exact B633563
  · exact B633567
  · exact B633571
  · exact B633575
  · exact B633579
  · exact B633583
  · exact B633587
  · exact B633591
  · exact B633595
  · exact B633599
  · exact B633603
  · exact B633607
  · exact B633611
  · exact B633615
  · exact B633619
  · exact B633623
  · exact B633627
  · exact B633631
  · exact B633635
  · exact B633639
  · exact B633643
  · exact B633647
  · exact B633651
  · exact B633655
  · exact B633659
  · exact B633663
  · exact B633667
  · exact B633671
  · exact B633675
  · exact B633679
  · exact B633683
  · exact B633687
  · exact B633691
  · exact B633695
  · exact B633699
  · exact B633703
  · exact B633707
  · exact B633711
  · exact B633715
  · exact B633719
  · exact B633723
  · exact B633727
  · exact B633731
  · exact B633735
  · exact B633739
  · exact B633743
  · exact B633747
  · exact B633751
  · exact B633755
  · exact B633759
  · exact B633763
  · exact B633767
  · exact B633771
  · exact B633775
  · exact B633779
  · exact B633783
  · exact B633787
  · exact B633791
  · exact B633795
  · exact B633799
  · exact B633803
  · exact B633807
  · exact B633811
  · exact B633815
  · exact B633819
  · exact B633823
  · exact B633827
  · exact B633831
  · exact B633835
  · exact B633839
  · exact B633843
  · exact B633847
  · exact B633851
  · exact B633855
  · exact B633859
  · exact B633863
  · exact B633867
  · exact B633871
  · exact B633875
  · exact B633879
  · exact B633883
  · exact B633887
  · exact B633891
  · exact B633895
  · exact B633899
  · exact B633903
  · exact B633907
  · exact B633911
  · exact B633915
  · exact B633919
  · exact B633923
  · exact B633927
  · exact B633931
  · exact B633935
  · exact B633939
  · exact B633943
  · exact B633947
  · exact B633951
  · exact B633955
  · exact B633959
  · exact B633963
  · exact B633967
  · exact B633971
  · exact B633975
  · exact B633979
  · exact B633983
  · exact B633987
  · exact B633991
  · exact B633995
  · exact B633999
  · exact B634003
  · exact B634007
  · exact B634011
  · exact B634015
  · exact B634019
  · exact B634023
  · exact B634027
  · exact B634031
  · exact B634035
  · exact B634039
  · exact B634043
  · exact B634047
  · exact B634051
  · exact B634055
  · exact B634059
  · exact B634063
  · exact B634067
  · exact B634071
  · exact B634075
  · exact B634079
  · exact B634083
  · exact B634087
  · exact B634091
  · exact B634095
  · exact B634099
  · exact B634103
  · exact B634107
  · exact B634111
  · exact B634115
  · exact B634119
  · exact B634123
  · exact B634127
  · exact B634131
  · exact B634135
  · exact B634139
  · exact B634143
  · exact B634147
  · exact B634151
  · exact B634155
  · exact B634159
  · exact B634163
  · exact B634167
  · exact B634171
  · exact B634175
  · exact B634179
  · exact B634183
  · exact B634187
  · exact B634191
  · exact B634195
  · exact B634199
  · exact B634203
  · exact B634207
  · exact B634211
  · exact B634215
  · exact B634219
  · exact B634223
  · exact B634227
  · exact B634231
  · exact B634235
  · exact B634239
  · exact B634243
  · exact B634247
  · exact B634251
  · exact B634255
  · exact B634259
  · exact B634263
  · exact B634267
  · exact B634271
  · exact B634275
  · exact B634279
  · exact B634283
  · exact B634287
  · exact B634291
  · exact B634295
  · exact B634299

theorem solution (m : ℕ) (hlo : 630300 ≤ m) (hhi : m ≤ 634300) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 157575 ≤ j := by omega
    have hj2 : j ≤ 158574 := by omega
    have hb : Blo 630300 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 158275 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
