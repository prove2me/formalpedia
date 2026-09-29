-- Prove2me | solution 1 for syracuse_descends_range_944585_948585
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:58.606173+00:00
-- url     : https://prove2.me/submissions/1604be05-ce66-4a83-8e42-dc915aecf1df

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


theorem B2129957 : Blo 944585 2129957 := bbase (se 4 (by rfl) ⟨199683, by rfl⟩ : syracuseStep 2129957 = 399367) (by norm_num)
theorem B2130029 : Blo 944585 2130029 := bbase (se 3 (by rfl) ⟨399380, by rfl⟩ : syracuseStep 2130029 = 798761) (by norm_num)
theorem B1441901 : Blo 944585 1441901 := bbase (se 3 (by rfl) ⟨270356, by rfl⟩ : syracuseStep 1441901 = 540713) (by norm_num)
theorem B1081453 : Blo 944585 1081453 := bbase (se 3 (by rfl) ⟨202772, by rfl⟩ : syracuseStep 1081453 = 405545) (by norm_num)
theorem B2392213 : Blo 944585 2392213 := bbase (se 6 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 2392213 = 112135) (by norm_num)
theorem B2130101 : Blo 944585 2130101 := bbase (se 5 (by rfl) ⟨99848, by rfl⟩ : syracuseStep 2130101 = 199697) (by norm_num)
theorem B2130173 : Blo 944585 2130173 := bbase (se 3 (by rfl) ⟨399407, by rfl⟩ : syracuseStep 2130173 = 798815) (by norm_num)
theorem B2392325 : Blo 944585 2392325 := bbase (se 4 (by rfl) ⟨224280, by rfl⟩ : syracuseStep 2392325 = 448561) (by norm_num)
theorem B2130245 : Blo 944585 2130245 := bbase (se 4 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 2130245 = 399421) (by norm_num)
theorem B2130317 : Blo 944585 2130317 := bbase (se 3 (by rfl) ⟨399434, by rfl⟩ : syracuseStep 2130317 = 798869) (by norm_num)
theorem B2392517 : Blo 944585 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B2130389 : Blo 944585 2130389 := bbase (se 7 (by rfl) ⟨24965, by rfl⟩ : syracuseStep 2130389 = 49931) (by norm_num)
theorem B2130461 : Blo 944585 2130461 := bbase (se 3 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 2130461 = 798923) (by norm_num)
theorem B1704493 : Blo 944585 1704493 := bbase (se 3 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 1704493 = 639185) (by norm_num)
theorem B2130533 : Blo 944585 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B2130605 : Blo 944585 2130605 := bbase (se 3 (by rfl) ⟨399488, by rfl⟩ : syracuseStep 2130605 = 798977) (by norm_num)
theorem B6816469 : Blo 944585 6816469 := bbase (se 7 (by rfl) ⟨79880, by rfl⟩ : syracuseStep 6816469 = 159761) (by norm_num)
theorem B2130677 : Blo 944585 2130677 := bbase (se 5 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 2130677 = 199751) (by norm_num)
theorem B2392861 : Blo 944585 2392861 := bbase (se 3 (by rfl) ⟨448661, by rfl⟩ : syracuseStep 2392861 = 897323) (by norm_num)
theorem B2130749 : Blo 944585 2130749 := bbase (se 3 (by rfl) ⟨399515, by rfl⟩ : syracuseStep 2130749 = 799031) (by norm_num)
theorem B2556805 : Blo 944585 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B2130821 : Blo 944585 2130821 := bbase (se 4 (by rfl) ⟨199764, by rfl⟩ : syracuseStep 2130821 = 399529) (by norm_num)
theorem B2392973 : Blo 944585 2392973 := bbase (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) (by norm_num)
theorem B2130893 : Blo 944585 2130893 := bbase (se 3 (by rfl) ⟨399542, by rfl⟩ : syracuseStep 2130893 = 799085) (by norm_num)
theorem B1704925 : Blo 944585 1704925 := bbase (se 3 (by rfl) ⟨319673, by rfl⟩ : syracuseStep 1704925 = 639347) (by norm_num)
theorem B4490245 : Blo 944585 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B2130965 : Blo 944585 2130965 := bbase (se 6 (by rfl) ⟨49944, by rfl⟩ : syracuseStep 2130965 = 99889) (by norm_num)
theorem B2393165 : Blo 944585 2393165 := bbase (se 3 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 2393165 = 897437) (by norm_num)
theorem B41976917 : Blo 944585 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B2131037 : Blo 944585 2131037 := bbase (se 3 (by rfl) ⟨399569, by rfl⟩ : syracuseStep 2131037 = 799139) (by norm_num)
theorem B2425981 : Blo 944585 2425981 := bbase (se 3 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 2425981 = 909743) (by norm_num)
theorem B4555925 : Blo 944585 4555925 := bbase (se 6 (by rfl) ⟨106779, by rfl⟩ : syracuseStep 4555925 = 213559) (by norm_num)
theorem B4785317 : Blo 944585 4785317 := bbase (se 4 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 4785317 = 897247) (by norm_num)
theorem B2131109 : Blo 944585 2131109 := bbase (se 4 (by rfl) ⟨199791, by rfl⟩ : syracuseStep 2131109 = 399583) (by norm_num)
theorem B1279165 : Blo 944585 1279165 := bbase (se 3 (by rfl) ⟨239843, by rfl⟩ : syracuseStep 1279165 = 479687) (by norm_num)
theorem B10781909 : Blo 944585 10781909 := bbase (se 7 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 10781909 = 252701) (by norm_num)
theorem B2131181 : Blo 944585 2131181 := bbase (se 3 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 2131181 = 799193) (by norm_num)
theorem B2131253 : Blo 944585 2131253 := bbase (se 5 (by rfl) ⟨99902, by rfl⟩ : syracuseStep 2131253 = 199805) (by norm_num)
theorem B2131325 : Blo 944585 2131325 := bbase (se 3 (by rfl) ⟨399623, by rfl⟩ : syracuseStep 2131325 = 799247) (by norm_num)
theorem B2393509 : Blo 944585 2393509 := bbase (se 4 (by rfl) ⟨224391, by rfl⟩ : syracuseStep 2393509 = 448783) (by norm_num)
theorem B2131397 : Blo 944585 2131397 := bbase (se 4 (by rfl) ⟨199818, by rfl⟩ : syracuseStep 2131397 = 399637) (by norm_num)
theorem B1705445 : Blo 944585 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B2131469 : Blo 944585 2131469 := bbase (se 3 (by rfl) ⟨399650, by rfl⟩ : syracuseStep 2131469 = 799301) (by norm_num)
theorem B2393621 : Blo 944585 2393621 := bbase (se 6 (by rfl) ⟨56100, by rfl⟩ : syracuseStep 2393621 = 112201) (by norm_num)
theorem B2131541 : Blo 944585 2131541 := bbase (se 8 (by rfl) ⟨12489, by rfl⟩ : syracuseStep 2131541 = 24979) (by norm_num)
theorem B1279645 : Blo 944585 1279645 := bbase (se 3 (by rfl) ⟨239933, by rfl⟩ : syracuseStep 1279645 = 479867) (by norm_num)
theorem B2131613 : Blo 944585 2131613 := bbase (se 3 (by rfl) ⟨399677, by rfl⟩ : syracuseStep 2131613 = 799355) (by norm_num)
theorem B2393813 : Blo 944585 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B2131685 : Blo 944585 2131685 := bbase (se 4 (by rfl) ⟨199845, by rfl⟩ : syracuseStep 2131685 = 399691) (by norm_num)
theorem B2131757 : Blo 944585 2131757 := bbase (se 3 (by rfl) ⟨399704, by rfl⟩ : syracuseStep 2131757 = 799409) (by norm_num)
theorem B2131829 : Blo 944585 2131829 := bbase (se 5 (by rfl) ⟨99929, by rfl⟩ : syracuseStep 2131829 = 199859) (by norm_num)
theorem B2131901 : Blo 944585 2131901 := bbase (se 3 (by rfl) ⟨399731, by rfl⟩ : syracuseStep 2131901 = 799463) (by norm_num)
theorem B1345501 : Blo 944585 1345501 := bbase (se 3 (by rfl) ⟨252281, by rfl⟩ : syracuseStep 1345501 = 504563) (by norm_num)
theorem B2131973 : Blo 944585 2131973 := bbase (se 4 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 2131973 = 399745) (by norm_num)
theorem B2394157 : Blo 944585 2394157 := bbase (se 3 (by rfl) ⟨448904, by rfl⟩ : syracuseStep 2394157 = 897809) (by norm_num)
theorem B2132045 : Blo 944585 2132045 := bbase (se 3 (by rfl) ⟨399758, by rfl⟩ : syracuseStep 2132045 = 799517) (by norm_num)
theorem B2132117 : Blo 944585 2132117 := bbase (se 6 (by rfl) ⟨49971, by rfl⟩ : syracuseStep 2132117 = 99943) (by norm_num)
theorem B2394269 : Blo 944585 2394269 := bbase (se 3 (by rfl) ⟨448925, by rfl⟩ : syracuseStep 2394269 = 897851) (by norm_num)
theorem B2427101 : Blo 944585 2427101 := bbase (se 3 (by rfl) ⟨455081, by rfl⟩ : syracuseStep 2427101 = 910163) (by norm_num)
theorem B2132189 : Blo 944585 2132189 := bbase (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) (by norm_num)
theorem B2132261 : Blo 944585 2132261 := bbase (se 4 (by rfl) ⟨199899, by rfl⟩ : syracuseStep 2132261 = 399799) (by norm_num)
theorem B1345837 : Blo 944585 1345837 := bbase (se 3 (by rfl) ⟨252344, by rfl⟩ : syracuseStep 1345837 = 504689) (by norm_num)
theorem B6064469 : Blo 944585 6064469 := bbase (se 10 (by rfl) ⟨8883, by rfl⟩ : syracuseStep 6064469 = 17767) (by norm_num)
theorem B2394461 : Blo 944585 2394461 := bbase (se 3 (by rfl) ⟨448961, by rfl⟩ : syracuseStep 2394461 = 897923) (by norm_num)
theorem B2132333 : Blo 944585 2132333 := bbase (se 3 (by rfl) ⟨399812, by rfl⟩ : syracuseStep 2132333 = 799625) (by norm_num)
theorem B4786613 : Blo 944585 4786613 := bbase (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) (by norm_num)
theorem B2132405 : Blo 944585 2132405 := bbase (se 5 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 2132405 = 199913) (by norm_num)
theorem B2132477 : Blo 944585 2132477 := bbase (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) (by norm_num)
theorem B1346053 : Blo 944585 1346053 := bbase (se 4 (by rfl) ⟨126192, by rfl⟩ : syracuseStep 1346053 = 252385) (by norm_num)
theorem B2132549 : Blo 944585 2132549 := bbase (se 4 (by rfl) ⟨199926, by rfl⟩ : syracuseStep 2132549 = 399853) (by norm_num)
theorem B2132621 : Blo 944585 2132621 := bbase (se 3 (by rfl) ⟨399866, by rfl⟩ : syracuseStep 2132621 = 799733) (by norm_num)
theorem B2394805 : Blo 944585 2394805 := bbase (se 5 (by rfl) ⟨112256, by rfl⟩ : syracuseStep 2394805 = 224513) (by norm_num)
theorem B2132693 : Blo 944585 2132693 := bbase (se 7 (by rfl) ⟨24992, by rfl⟩ : syracuseStep 2132693 = 49985) (by norm_num)
theorem B2132765 : Blo 944585 2132765 := bbase (se 3 (by rfl) ⟨399893, by rfl⟩ : syracuseStep 2132765 = 799787) (by norm_num)
theorem B2394917 : Blo 944585 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B2132837 : Blo 944585 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B1346429 : Blo 944585 1346429 := bbase (se 3 (by rfl) ⟨252455, by rfl⟩ : syracuseStep 1346429 = 504911) (by norm_num)
theorem B2132909 : Blo 944585 2132909 := bbase (se 3 (by rfl) ⟨399920, by rfl⟩ : syracuseStep 2132909 = 799841) (by norm_num)
theorem B2395109 : Blo 944585 2395109 := bbase (se 4 (by rfl) ⟨224541, by rfl⟩ : syracuseStep 2395109 = 449083) (by norm_num)
theorem B2132981 : Blo 944585 2132981 := bbase (se 5 (by rfl) ⟨99983, by rfl⟩ : syracuseStep 2132981 = 199967) (by norm_num)
theorem B1281029 : Blo 944585 1281029 := bbase (se 4 (by rfl) ⟨120096, by rfl⟩ : syracuseStep 1281029 = 240193) (by norm_num)
theorem B4557829 : Blo 944585 4557829 := bbase (se 4 (by rfl) ⟨427296, by rfl⟩ : syracuseStep 4557829 = 854593) (by norm_num)
theorem B4557845 : Blo 944585 4557845 := bbase (se 6 (by rfl) ⟨106824, by rfl⟩ : syracuseStep 4557845 = 213649) (by norm_num)
theorem B2690101 : Blo 944585 2690101 := bbase (se 5 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 2690101 = 252197) (by norm_num)
theorem B2133053 : Blo 944585 2133053 := bbase (se 3 (by rfl) ⟨399947, by rfl⟩ : syracuseStep 2133053 = 799895) (by norm_num)
theorem B2133125 : Blo 944585 2133125 := bbase (se 4 (by rfl) ⟨199980, by rfl⟩ : syracuseStep 2133125 = 399961) (by norm_num)
theorem B2133197 : Blo 944585 2133197 := bbase (se 3 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 2133197 = 799949) (by norm_num)
theorem B2428181 : Blo 944585 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B2133269 : Blo 944585 2133269 := bbase (se 6 (by rfl) ⟨49998, by rfl⟩ : syracuseStep 2133269 = 99997) (by norm_num)
theorem B2395453 : Blo 944585 2395453 := bbase (se 3 (by rfl) ⟨449147, by rfl⟩ : syracuseStep 2395453 = 898295) (by norm_num)
theorem B2133341 : Blo 944585 2133341 := bbase (se 3 (by rfl) ⟨400001, by rfl⟩ : syracuseStep 2133341 = 800003) (by norm_num)
theorem B2133413 : Blo 944585 2133413 := bbase (se 4 (by rfl) ⟨200007, by rfl⟩ : syracuseStep 2133413 = 400015) (by norm_num)
theorem B2395565 : Blo 944585 2395565 := bbase (se 3 (by rfl) ⟨449168, by rfl⟩ : syracuseStep 2395565 = 898337) (by norm_num)
theorem B2133485 : Blo 944585 2133485 := bbase (se 3 (by rfl) ⟨400028, by rfl⟩ : syracuseStep 2133485 = 800057) (by norm_num)
theorem B2559509 : Blo 944585 2559509 := bbase (se 6 (by rfl) ⟨59988, by rfl⟩ : syracuseStep 2559509 = 119977) (by norm_num)
theorem B2133557 : Blo 944585 2133557 := bbase (se 5 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 2133557 = 200021) (by norm_num)
theorem B1150529 : Blo 944585 1150529 := bbase (se 2 (by rfl) ⟨431448, by rfl⟩ : syracuseStep 1150529 = 862897) (by norm_num)
theorem B2395757 : Blo 944585 2395757 := bbase (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) (by norm_num)
theorem B2133629 : Blo 944585 2133629 := bbase (se 3 (by rfl) ⟨400055, by rfl⟩ : syracuseStep 2133629 = 800111) (by norm_num)
theorem B1216141 : Blo 944585 1216141 := bbase (se 3 (by rfl) ⟨228026, by rfl⟩ : syracuseStep 1216141 = 456053) (by norm_num)
theorem B4787909 : Blo 944585 4787909 := bbase (se 4 (by rfl) ⟨448866, by rfl⟩ : syracuseStep 4787909 = 897733) (by norm_num)
theorem B2133701 : Blo 944585 2133701 := bbase (se 4 (by rfl) ⟨200034, by rfl⟩ : syracuseStep 2133701 = 400069) (by norm_num)
theorem B2133773 : Blo 944585 2133773 := bbase (se 3 (by rfl) ⟨400082, by rfl⟩ : syracuseStep 2133773 = 800165) (by norm_num)
theorem B2133845 : Blo 944585 2133845 := bbase (se 9 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 2133845 = 12503) (by norm_num)
theorem B2133917 : Blo 944585 2133917 := bbase (se 3 (by rfl) ⟨400109, by rfl⟩ : syracuseStep 2133917 = 800219) (by norm_num)
theorem B2396101 : Blo 944585 2396101 := bbase (se 4 (by rfl) ⟨224634, by rfl⟩ : syracuseStep 2396101 = 449269) (by norm_num)
theorem B3411925 : Blo 944585 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B2133989 : Blo 944585 2133989 := bbase (se 4 (by rfl) ⟨200061, by rfl⟩ : syracuseStep 2133989 = 400123) (by norm_num)
theorem B1216553 : Blo 944585 1216553 := bbase (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) (by norm_num)
theorem B2134061 : Blo 944585 2134061 := bbase (se 3 (by rfl) ⟨400136, by rfl⟩ : syracuseStep 2134061 = 800273) (by norm_num)
theorem B2396213 : Blo 944585 2396213 := bbase (se 5 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 2396213 = 224645) (by norm_num)
theorem B2134133 : Blo 944585 2134133 := bbase (se 5 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 2134133 = 200075) (by norm_num)
theorem B2134205 : Blo 944585 2134205 := bbase (se 3 (by rfl) ⟨400163, by rfl⟩ : syracuseStep 2134205 = 800327) (by norm_num)
theorem B2396405 : Blo 944585 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B2134277 : Blo 944585 2134277 := bbase (se 4 (by rfl) ⟨200088, by rfl⟩ : syracuseStep 2134277 = 400177) (by norm_num)
theorem B1347853 : Blo 944585 1347853 := bbase (se 3 (by rfl) ⟨252722, by rfl⟩ : syracuseStep 1347853 = 505445) (by norm_num)
theorem B2560405 : Blo 944585 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B2691605 : Blo 944585 2691605 := bbase (se 6 (by rfl) ⟨63084, by rfl⟩ : syracuseStep 2691605 = 126169) (by norm_num)
theorem B8098325 : Blo 944585 8098325 := bbase (se 6 (by rfl) ⟨189804, by rfl⟩ : syracuseStep 8098325 = 379609) (by norm_num)
theorem B2396749 : Blo 944585 2396749 := bbase (se 3 (by rfl) ⟨449390, by rfl⟩ : syracuseStep 2396749 = 898781) (by norm_num)
theorem B3838549 : Blo 944585 3838549 := bbase (se 8 (by rfl) ⟨22491, by rfl⟩ : syracuseStep 3838549 = 44983) (by norm_num)
theorem B4035221 : Blo 944585 4035221 := bbase (se 6 (by rfl) ⟨94575, by rfl⟩ : syracuseStep 4035221 = 189151) (by norm_num)
theorem B2396861 : Blo 944585 2396861 := bbase (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) (by norm_num)
theorem B1708789 : Blo 944585 1708789 := bbase (se 5 (by rfl) ⟨80099, by rfl⟩ : syracuseStep 1708789 = 160199) (by norm_num)
theorem B1348445 : Blo 944585 1348445 := bbase (se 3 (by rfl) ⟨252833, by rfl⟩ : syracuseStep 1348445 = 505667) (by norm_num)
theorem B2397053 : Blo 944585 2397053 := bbase (se 3 (by rfl) ⟨449447, by rfl⟩ : syracuseStep 2397053 = 898895) (by norm_num)
theorem B1708933 : Blo 944585 1708933 := bbase (se 4 (by rfl) ⟨160212, by rfl⟩ : syracuseStep 1708933 = 320425) (by norm_num)
theorem B1348525 : Blo 944585 1348525 := bbase (se 3 (by rfl) ⟨252848, by rfl⟩ : syracuseStep 1348525 = 505697) (by norm_num)
theorem B4789205 : Blo 944585 4789205 := bbase (se 7 (by rfl) ⟨56123, by rfl⟩ : syracuseStep 4789205 = 112247) (by norm_num)
theorem B1348645 : Blo 944585 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B1348741 : Blo 944585 1348741 := bbase (se 4 (by rfl) ⟨126444, by rfl⟩ : syracuseStep 1348741 = 252889) (by norm_num)
theorem B2397397 : Blo 944585 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B7181621 : Blo 944585 7181621 := bbase (se 5 (by rfl) ⟨336638, by rfl⟩ : syracuseStep 7181621 = 673277) (by norm_num)
theorem B2397509 : Blo 944585 2397509 := bbase (se 4 (by rfl) ⟨224766, by rfl⟩ : syracuseStep 2397509 = 449533) (by norm_num)
theorem B2397701 : Blo 944585 2397701 := bbase (se 4 (by rfl) ⟨224784, by rfl⟩ : syracuseStep 2397701 = 449569) (by norm_num)
theorem B1349237 : Blo 944585 1349237 := bbase (se 5 (by rfl) ⟨63245, by rfl⟩ : syracuseStep 1349237 = 126491) (by norm_num)
theorem B1513093 : Blo 944585 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B5117717 : Blo 944585 5117717 := bbase (se 6 (by rfl) ⟨119946, by rfl⟩ : syracuseStep 5117717 = 239893) (by norm_num)
theorem B2398045 : Blo 944585 2398045 := bbase (se 3 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 2398045 = 899267) (by norm_num)
theorem B2398157 : Blo 944585 2398157 := bbase (se 3 (by rfl) ⟨449654, by rfl⟩ : syracuseStep 2398157 = 899309) (by norm_num)
theorem B2693189 : Blo 944585 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B5380181 : Blo 944585 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B25860181 : Blo 944585 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B2398349 : Blo 944585 2398349 := bbase (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) (by norm_num)
theorem B1349789 : Blo 944585 1349789 := bbase (se 3 (by rfl) ⟨253085, by rfl⟩ : syracuseStep 1349789 = 506171) (by norm_num)
theorem B4790501 : Blo 944585 4790501 := bbase (se 4 (by rfl) ⟨449109, by rfl⟩ : syracuseStep 4790501 = 898219) (by norm_num)
theorem B2398693 : Blo 944585 2398693 := bbase (se 4 (by rfl) ⟨224877, by rfl⟩ : syracuseStep 2398693 = 449755) (by norm_num)
theorem B2595349 : Blo 944585 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B3414581 : Blo 944585 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B15964757 : Blo 944585 15964757 := bbase (se 8 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 15964757 = 187087) (by norm_num)
theorem B2398805 : Blo 944585 2398805 := bbase (se 8 (by rfl) ⟨14055, by rfl⟩ : syracuseStep 2398805 = 28111) (by norm_num)
theorem B2693861 : Blo 944585 2693861 := bbase (se 4 (by rfl) ⟨252549, by rfl⟩ : syracuseStep 2693861 = 505099) (by norm_num)
theorem B1022725 : Blo 944585 1022725 := bbase (se 4 (by rfl) ⟨95880, by rfl⟩ : syracuseStep 1022725 = 191761) (by norm_num)
theorem B2398997 : Blo 944585 2398997 := bbase (se 6 (by rfl) ⟨56226, by rfl⟩ : syracuseStep 2398997 = 112453) (by norm_num)
theorem B1514285 : Blo 944585 1514285 := bbase (se 3 (by rfl) ⟨283928, by rfl⟩ : syracuseStep 1514285 = 567857) (by norm_num)
theorem B3414869 : Blo 944585 3414869 := bbase (se 9 (by rfl) ⟨10004, by rfl⟩ : syracuseStep 3414869 = 20009) (by norm_num)
theorem B1350541 : Blo 944585 1350541 := bbase (se 3 (by rfl) ⟨253226, by rfl⟩ : syracuseStep 1350541 = 506453) (by norm_num)
theorem B1514477 : Blo 944585 1514477 := bbase (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) (by norm_num)
theorem B1776629 : Blo 944585 1776629 := bbase (se 5 (by rfl) ⟨83279, by rfl⟩ : syracuseStep 1776629 = 166559) (by norm_num)
theorem B2399341 : Blo 944585 2399341 := bbase (se 3 (by rfl) ⟨449876, by rfl⟩ : syracuseStep 2399341 = 899753) (by norm_num)
theorem B2694293 : Blo 944585 2694293 := bbase (se 6 (by rfl) ⟨63147, by rfl⟩ : syracuseStep 2694293 = 126295) (by norm_num)
theorem B2399453 : Blo 944585 2399453 := bbase (se 3 (by rfl) ⟨449897, by rfl⟩ : syracuseStep 2399453 = 899795) (by norm_num)
theorem B957853 : Blo 944585 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B2399645 : Blo 944585 2399645 := bbase (se 3 (by rfl) ⟨449933, by rfl⟩ : syracuseStep 2399645 = 899867) (by norm_num)
theorem B4791797 : Blo 944585 4791797 := bbase (se 5 (by rfl) ⟨224615, by rfl⟩ : syracuseStep 4791797 = 449231) (by norm_num)
theorem B4562453 : Blo 944585 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B3415733 : Blo 944585 3415733 := bbase (se 5 (by rfl) ⟨160112, by rfl⟩ : syracuseStep 3415733 = 320225) (by norm_num)
theorem B1416893 : Blo 944585 1416893 := bbase (se 3 (by rfl) ⟨265667, by rfl⟩ : syracuseStep 1416893 = 531335) (by norm_num)
theorem B958153 : Blo 944585 958153 := bbase (se 2 (by rfl) ⟨359307, by rfl⟩ : syracuseStep 958153 = 718615) (by norm_num)
theorem B1416917 : Blo 944585 1416917 := bbase (se 7 (by rfl) ⟨16604, by rfl⟩ : syracuseStep 1416917 = 33209) (by norm_num)
theorem B1416941 : Blo 944585 1416941 := bbase (se 3 (by rfl) ⟨265676, by rfl⟩ : syracuseStep 1416941 = 531353) (by norm_num)
theorem B2399989 : Blo 944585 2399989 := bbase (se 5 (by rfl) ⟨112499, by rfl⟩ : syracuseStep 2399989 = 224999) (by norm_num)
theorem B1416965 : Blo 944585 1416965 := bbase (se 4 (by rfl) ⟨132840, by rfl⟩ : syracuseStep 1416965 = 265681) (by norm_num)
theorem B1416989 : Blo 944585 1416989 := bbase (se 3 (by rfl) ⟨265685, by rfl⟩ : syracuseStep 1416989 = 531371) (by norm_num)
theorem B1417013 : Blo 944585 1417013 := bbase (se 5 (by rfl) ⟨66422, by rfl⟩ : syracuseStep 1417013 = 132845) (by norm_num)
theorem B1417037 : Blo 944585 1417037 := bbase (se 3 (by rfl) ⟨265694, by rfl⟩ : syracuseStep 1417037 = 531389) (by norm_num)
theorem B1417061 : Blo 944585 1417061 := bbase (se 4 (by rfl) ⟨132849, by rfl⟩ : syracuseStep 1417061 = 265699) (by norm_num)
theorem B2400101 : Blo 944585 2400101 := bbase (se 4 (by rfl) ⟨225009, by rfl⟩ : syracuseStep 2400101 = 450019) (by norm_num)
theorem B1417085 : Blo 944585 1417085 := bbase (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) (by norm_num)
theorem B2695045 : Blo 944585 2695045 := bbase (se 4 (by rfl) ⟨252660, by rfl⟩ : syracuseStep 2695045 = 505321) (by norm_num)
theorem B1417109 : Blo 944585 1417109 := bbase (se 6 (by rfl) ⟨33213, by rfl⟩ : syracuseStep 1417109 = 66427) (by norm_num)
theorem B1417133 : Blo 944585 1417133 := bbase (se 3 (by rfl) ⟨265712, by rfl⟩ : syracuseStep 1417133 = 531425) (by norm_num)
theorem B1417157 : Blo 944585 1417157 := bbase (se 4 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 1417157 = 265717) (by norm_num)
theorem B1417181 : Blo 944585 1417181 := bbase (se 3 (by rfl) ⟨265721, by rfl⟩ : syracuseStep 1417181 = 531443) (by norm_num)
theorem B1417205 : Blo 944585 1417205 := bbase (se 5 (by rfl) ⟨66431, by rfl⟩ : syracuseStep 1417205 = 132863) (by norm_num)
theorem B1417229 : Blo 944585 1417229 := bbase (se 3 (by rfl) ⟨265730, by rfl⟩ : syracuseStep 1417229 = 531461) (by norm_num)
theorem B1417253 : Blo 944585 1417253 := bbase (se 4 (by rfl) ⟨132867, by rfl⟩ : syracuseStep 1417253 = 265735) (by norm_num)
theorem B2400293 : Blo 944585 2400293 := bbase (se 4 (by rfl) ⟨225027, by rfl⟩ : syracuseStep 2400293 = 450055) (by norm_num)
theorem B1417277 : Blo 944585 1417277 := bbase (se 3 (by rfl) ⟨265739, by rfl⟩ : syracuseStep 1417277 = 531479) (by norm_num)
theorem B1417301 : Blo 944585 1417301 := bbase (se 8 (by rfl) ⟨8304, by rfl⟩ : syracuseStep 1417301 = 16609) (by norm_num)
theorem B1417325 : Blo 944585 1417325 := bbase (se 3 (by rfl) ⟨265748, by rfl⟩ : syracuseStep 1417325 = 531497) (by norm_num)
theorem B1417349 : Blo 944585 1417349 := bbase (se 4 (by rfl) ⟨132876, by rfl⟩ : syracuseStep 1417349 = 265753) (by norm_num)
theorem B16425109 : Blo 944585 16425109 := bbase (se 6 (by rfl) ⟨384963, by rfl⟩ : syracuseStep 16425109 = 769927) (by norm_num)
theorem B1417373 : Blo 944585 1417373 := bbase (se 3 (by rfl) ⟨265757, by rfl⟩ : syracuseStep 1417373 = 531515) (by norm_num)
theorem B1417397 : Blo 944585 1417397 := bbase (se 5 (by rfl) ⟨66440, by rfl⟩ : syracuseStep 1417397 = 132881) (by norm_num)
theorem B1417421 : Blo 944585 1417421 := bbase (se 3 (by rfl) ⟨265766, by rfl⟩ : syracuseStep 1417421 = 531533) (by norm_num)
theorem B1417445 : Blo 944585 1417445 := bbase (se 4 (by rfl) ⟨132885, by rfl⟩ : syracuseStep 1417445 = 265771) (by norm_num)
theorem B5382389 : Blo 944585 5382389 := bbase (se 5 (by rfl) ⟨252299, by rfl⟩ : syracuseStep 5382389 = 504599) (by norm_num)
theorem B3416309 : Blo 944585 3416309 := bbase (se 5 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 3416309 = 320279) (by norm_num)
theorem B1417469 : Blo 944585 1417469 := bbase (se 3 (by rfl) ⟨265775, by rfl⟩ : syracuseStep 1417469 = 531551) (by norm_num)
theorem B1417493 : Blo 944585 1417493 := bbase (se 6 (by rfl) ⟨33222, by rfl⟩ : syracuseStep 1417493 = 66445) (by norm_num)
theorem B1417517 : Blo 944585 1417517 := bbase (se 3 (by rfl) ⟨265784, by rfl⟩ : syracuseStep 1417517 = 531569) (by norm_num)
theorem B1417541 : Blo 944585 1417541 := bbase (se 4 (by rfl) ⟨132894, by rfl⟩ : syracuseStep 1417541 = 265789) (by norm_num)
theorem B2466133 : Blo 944585 2466133 := bbase (se 10 (by rfl) ⟨3612, by rfl⟩ : syracuseStep 2466133 = 7225) (by norm_num)
theorem B1417565 : Blo 944585 1417565 := bbase (se 3 (by rfl) ⟨265793, by rfl⟩ : syracuseStep 1417565 = 531587) (by norm_num)
theorem B1417589 : Blo 944585 1417589 := bbase (se 5 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 1417589 = 132899) (by norm_num)
theorem B2400637 : Blo 944585 2400637 := bbase (se 3 (by rfl) ⟨450119, by rfl⟩ : syracuseStep 2400637 = 900239) (by norm_num)
theorem B1417613 : Blo 944585 1417613 := bbase (se 3 (by rfl) ⟨265802, by rfl⟩ : syracuseStep 1417613 = 531605) (by norm_num)
theorem B1515925 : Blo 944585 1515925 := bbase (se 6 (by rfl) ⟨35529, by rfl⟩ : syracuseStep 1515925 = 71059) (by norm_num)
theorem B1417637 : Blo 944585 1417637 := bbase (se 4 (by rfl) ⟨132903, by rfl⟩ : syracuseStep 1417637 = 265807) (by norm_num)
theorem B1417661 : Blo 944585 1417661 := bbase (se 3 (by rfl) ⟨265811, by rfl⟩ : syracuseStep 1417661 = 531623) (by norm_num)
theorem B1024453 : Blo 944585 1024453 := bbase (se 4 (by rfl) ⟨96042, by rfl⟩ : syracuseStep 1024453 = 192085) (by norm_num)
theorem B1417685 : Blo 944585 1417685 := bbase (se 7 (by rfl) ⟨16613, by rfl⟩ : syracuseStep 1417685 = 33227) (by norm_num)
theorem B1417709 : Blo 944585 1417709 := bbase (se 3 (by rfl) ⟨265820, by rfl⟩ : syracuseStep 1417709 = 531641) (by norm_num)
theorem B2400749 : Blo 944585 2400749 := bbase (se 3 (by rfl) ⟨450140, by rfl⟩ : syracuseStep 2400749 = 900281) (by norm_num)
theorem B1417733 : Blo 944585 1417733 := bbase (se 4 (by rfl) ⟨132912, by rfl⟩ : syracuseStep 1417733 = 265825) (by norm_num)
theorem B958997 : Blo 944585 958997 := bbase (se 6 (by rfl) ⟨22476, by rfl⟩ : syracuseStep 958997 = 44953) (by norm_num)
theorem B2433557 : Blo 944585 2433557 := bbase (se 6 (by rfl) ⟨57036, by rfl⟩ : syracuseStep 2433557 = 114073) (by norm_num)
theorem B1417757 : Blo 944585 1417757 := bbase (se 3 (by rfl) ⟨265829, by rfl⟩ : syracuseStep 1417757 = 531659) (by norm_num)
theorem B1417781 : Blo 944585 1417781 := bbase (se 5 (by rfl) ⟨66458, by rfl⟩ : syracuseStep 1417781 = 132917) (by norm_num)
theorem B1417805 : Blo 944585 1417805 := bbase (se 3 (by rfl) ⟨265838, by rfl⟩ : syracuseStep 1417805 = 531677) (by norm_num)
theorem B4039253 : Blo 944585 4039253 := bbase (se 8 (by rfl) ⟨23667, by rfl⟩ : syracuseStep 4039253 = 47335) (by norm_num)
theorem B1417829 : Blo 944585 1417829 := bbase (se 4 (by rfl) ⟨132921, by rfl⟩ : syracuseStep 1417829 = 265843) (by norm_num)
theorem B1417853 : Blo 944585 1417853 := bbase (se 3 (by rfl) ⟨265847, by rfl⟩ : syracuseStep 1417853 = 531695) (by norm_num)
theorem B1417877 : Blo 944585 1417877 := bbase (se 6 (by rfl) ⟨33231, by rfl⟩ : syracuseStep 1417877 = 66463) (by norm_num)
theorem B1417901 : Blo 944585 1417901 := bbase (se 3 (by rfl) ⟨265856, by rfl⟩ : syracuseStep 1417901 = 531713) (by norm_num)
theorem B2400941 : Blo 944585 2400941 := bbase (se 3 (by rfl) ⟨450176, by rfl⟩ : syracuseStep 2400941 = 900353) (by norm_num)
theorem B1417925 : Blo 944585 1417925 := bbase (se 4 (by rfl) ⟨132930, by rfl⟩ : syracuseStep 1417925 = 265861) (by norm_num)
theorem B1417949 : Blo 944585 1417949 := bbase (se 3 (by rfl) ⟨265865, by rfl⟩ : syracuseStep 1417949 = 531731) (by norm_num)
theorem B1417973 : Blo 944585 1417973 := bbase (se 5 (by rfl) ⟨66467, by rfl⟩ : syracuseStep 1417973 = 132935) (by norm_num)
theorem B4793093 : Blo 944585 4793093 := bbase (se 4 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 4793093 = 898705) (by norm_num)
theorem B1417997 : Blo 944585 1417997 := bbase (se 3 (by rfl) ⟨265874, by rfl⟩ : syracuseStep 1417997 = 531749) (by norm_num)
theorem B1418021 : Blo 944585 1418021 := bbase (se 4 (by rfl) ⟨132939, by rfl⟩ : syracuseStep 1418021 = 265879) (by norm_num)
theorem B1418045 : Blo 944585 1418045 := bbase (se 3 (by rfl) ⟨265883, by rfl⟩ : syracuseStep 1418045 = 531767) (by norm_num)
theorem B1418069 : Blo 944585 1418069 := bbase (se 9 (by rfl) ⟨4154, by rfl⟩ : syracuseStep 1418069 = 8309) (by norm_num)
theorem B1418093 : Blo 944585 1418093 := bbase (se 3 (by rfl) ⟨265892, by rfl⟩ : syracuseStep 1418093 = 531785) (by norm_num)
theorem B1418117 : Blo 944585 1418117 := bbase (se 4 (by rfl) ⟨132948, by rfl⟩ : syracuseStep 1418117 = 265897) (by norm_num)
theorem B2270101 : Blo 944585 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B1418141 : Blo 944585 1418141 := bbase (se 3 (by rfl) ⟨265901, by rfl⟩ : syracuseStep 1418141 = 531803) (by norm_num)
theorem B1418165 : Blo 944585 1418165 := bbase (se 5 (by rfl) ⟨66476, by rfl⟩ : syracuseStep 1418165 = 132953) (by norm_num)
theorem B1418189 : Blo 944585 1418189 := bbase (se 3 (by rfl) ⟨265910, by rfl⟩ : syracuseStep 1418189 = 531821) (by norm_num)
theorem B1516501 : Blo 944585 1516501 := bbase (se 7 (by rfl) ⟨17771, by rfl⟩ : syracuseStep 1516501 = 35543) (by norm_num)
theorem B1418213 : Blo 944585 1418213 := bbase (se 4 (by rfl) ⟨132957, by rfl⟩ : syracuseStep 1418213 = 265915) (by norm_num)
theorem B2270197 : Blo 944585 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B1418237 : Blo 944585 1418237 := bbase (se 3 (by rfl) ⟨265919, by rfl⟩ : syracuseStep 1418237 = 531839) (by norm_num)
theorem B1418261 : Blo 944585 1418261 := bbase (se 6 (by rfl) ⟨33240, by rfl⟩ : syracuseStep 1418261 = 66481) (by norm_num)
theorem B1418285 : Blo 944585 1418285 := bbase (se 3 (by rfl) ⟨265928, by rfl⟩ : syracuseStep 1418285 = 531857) (by norm_num)
theorem B1418309 : Blo 944585 1418309 := bbase (se 4 (by rfl) ⟨132966, by rfl⟩ : syracuseStep 1418309 = 265933) (by norm_num)
theorem B1418333 : Blo 944585 1418333 := bbase (se 3 (by rfl) ⟨265937, by rfl⟩ : syracuseStep 1418333 = 531875) (by norm_num)
theorem B3646565 : Blo 944585 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B1418357 : Blo 944585 1418357 := bbase (se 5 (by rfl) ⟨66485, by rfl⟩ : syracuseStep 1418357 = 132971) (by norm_num)
theorem B1418381 : Blo 944585 1418381 := bbase (se 3 (by rfl) ⟨265946, by rfl⟩ : syracuseStep 1418381 = 531893) (by norm_num)
theorem B1418405 : Blo 944585 1418405 := bbase (se 4 (by rfl) ⟨132975, by rfl⟩ : syracuseStep 1418405 = 265951) (by norm_num)
theorem B2270389 : Blo 944585 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B1418429 : Blo 944585 1418429 := bbase (se 3 (by rfl) ⟨265955, by rfl⟩ : syracuseStep 1418429 = 531911) (by norm_num)
theorem B9086165 : Blo 944585 9086165 := bbase (se 7 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 9086165 = 212957) (by norm_num)
theorem B1418453 : Blo 944585 1418453 := bbase (se 7 (by rfl) ⟨16622, by rfl⟩ : syracuseStep 1418453 = 33245) (by norm_num)
theorem B1418477 : Blo 944585 1418477 := bbase (se 3 (by rfl) ⟨265964, by rfl⟩ : syracuseStep 1418477 = 531929) (by norm_num)
theorem B1418501 : Blo 944585 1418501 := bbase (se 4 (by rfl) ⟨132984, by rfl⟩ : syracuseStep 1418501 = 265969) (by norm_num)
theorem B1418525 : Blo 944585 1418525 := bbase (se 3 (by rfl) ⟨265973, by rfl⟩ : syracuseStep 1418525 = 531947) (by norm_num)
theorem B1418549 : Blo 944585 1418549 := bbase (se 5 (by rfl) ⟨66494, by rfl⟩ : syracuseStep 1418549 = 132989) (by norm_num)
theorem B1418573 : Blo 944585 1418573 := bbase (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) (by norm_num)
theorem B1418597 : Blo 944585 1418597 := bbase (se 4 (by rfl) ⟨132993, by rfl⟩ : syracuseStep 1418597 = 265987) (by norm_num)
theorem B1418621 : Blo 944585 1418621 := bbase (se 3 (by rfl) ⟨265991, by rfl⟩ : syracuseStep 1418621 = 531983) (by norm_num)
theorem B1418645 : Blo 944585 1418645 := bbase (se 6 (by rfl) ⟨33249, by rfl⟩ : syracuseStep 1418645 = 66499) (by norm_num)
theorem B959897 : Blo 944585 959897 := bbase (se 2 (by rfl) ⟨359961, by rfl⟩ : syracuseStep 959897 = 719923) (by norm_num)
theorem B1418669 : Blo 944585 1418669 := bbase (se 3 (by rfl) ⟨266000, by rfl⟩ : syracuseStep 1418669 = 532001) (by norm_num)
theorem B1418693 : Blo 944585 1418693 := bbase (se 4 (by rfl) ⟨133002, by rfl⟩ : syracuseStep 1418693 = 266005) (by norm_num)
theorem B1418717 : Blo 944585 1418717 := bbase (se 3 (by rfl) ⟨266009, by rfl⟩ : syracuseStep 1418717 = 532019) (by norm_num)
theorem B3188213 : Blo 944585 3188213 := bbase (se 5 (by rfl) ⟨149447, by rfl⟩ : syracuseStep 3188213 = 298895) (by norm_num)
theorem B1418741 : Blo 944585 1418741 := bbase (se 5 (by rfl) ⟨66503, by rfl⟩ : syracuseStep 1418741 = 133007) (by norm_num)
theorem B2270717 : Blo 944585 2270717 := bbase (se 3 (by rfl) ⟨425759, by rfl⟩ : syracuseStep 2270717 = 851519) (by norm_num)
theorem B2336261 : Blo 944585 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B1418765 : Blo 944585 1418765 := bbase (se 3 (by rfl) ⟨266018, by rfl⟩ : syracuseStep 1418765 = 532037) (by norm_num)
theorem B1418789 : Blo 944585 1418789 := bbase (se 4 (by rfl) ⟨133011, by rfl⟩ : syracuseStep 1418789 = 266023) (by norm_num)
theorem B1418813 : Blo 944585 1418813 := bbase (se 3 (by rfl) ⟨266027, by rfl⟩ : syracuseStep 1418813 = 532055) (by norm_num)
theorem B1386053 : Blo 944585 1386053 := bbase (se 4 (by rfl) ⟨129942, by rfl⟩ : syracuseStep 1386053 = 259885) (by norm_num)
theorem B1418837 : Blo 944585 1418837 := bbase (se 8 (by rfl) ⟨8313, by rfl⟩ : syracuseStep 1418837 = 16627) (by norm_num)
theorem B1418861 : Blo 944585 1418861 := bbase (se 3 (by rfl) ⟨266036, by rfl⟩ : syracuseStep 1418861 = 532073) (by norm_num)
theorem B1418885 : Blo 944585 1418885 := bbase (se 4 (by rfl) ⟨133020, by rfl⟩ : syracuseStep 1418885 = 266041) (by norm_num)
theorem B1418909 : Blo 944585 1418909 := bbase (se 3 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 1418909 = 532091) (by norm_num)
theorem B1418933 : Blo 944585 1418933 := bbase (se 5 (by rfl) ⟨66512, by rfl⟩ : syracuseStep 1418933 = 133025) (by norm_num)
theorem B1418957 : Blo 944585 1418957 := bbase (se 3 (by rfl) ⟨266054, by rfl⟩ : syracuseStep 1418957 = 532109) (by norm_num)
theorem B3155669 : Blo 944585 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B960217 : Blo 944585 960217 := bbase (se 2 (by rfl) ⟨360081, by rfl⟩ : syracuseStep 960217 = 720163) (by norm_num)
theorem B1418981 : Blo 944585 1418981 := bbase (se 4 (by rfl) ⟨133029, by rfl⟩ : syracuseStep 1418981 = 266059) (by norm_num)
theorem B960229 : Blo 944585 960229 := bbase (se 4 (by rfl) ⟨90021, by rfl⟩ : syracuseStep 960229 = 180043) (by norm_num)
theorem B1419005 : Blo 944585 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B1517309 : Blo 944585 1517309 := bbase (se 3 (by rfl) ⟨284495, by rfl⟩ : syracuseStep 1517309 = 568991) (by norm_num)
theorem B1419029 : Blo 944585 1419029 := bbase (se 6 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 1419029 = 66517) (by norm_num)
theorem B1419053 : Blo 944585 1419053 := bbase (se 3 (by rfl) ⟨266072, by rfl⟩ : syracuseStep 1419053 = 532145) (by norm_num)
theorem B1419077 : Blo 944585 1419077 := bbase (se 4 (by rfl) ⟨133038, by rfl⟩ : syracuseStep 1419077 = 266077) (by norm_num)
theorem B1419101 : Blo 944585 1419101 := bbase (se 3 (by rfl) ⟨266081, by rfl⟩ : syracuseStep 1419101 = 532163) (by norm_num)
theorem B1419125 : Blo 944585 1419125 := bbase (se 5 (by rfl) ⟨66521, by rfl⟩ : syracuseStep 1419125 = 133043) (by norm_num)
theorem B1419149 : Blo 944585 1419149 := bbase (se 3 (by rfl) ⟨266090, by rfl⟩ : syracuseStep 1419149 = 532181) (by norm_num)
theorem B3188645 : Blo 944585 3188645 := bbase (se 4 (by rfl) ⟨298935, by rfl⟩ : syracuseStep 3188645 = 597871) (by norm_num)
theorem B1419173 : Blo 944585 1419173 := bbase (se 4 (by rfl) ⟨133047, by rfl⟩ : syracuseStep 1419173 = 266095) (by norm_num)
theorem B2271149 : Blo 944585 2271149 := bbase (se 3 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 2271149 = 851681) (by norm_num)
theorem B1419197 : Blo 944585 1419197 := bbase (se 3 (by rfl) ⟨266099, by rfl⟩ : syracuseStep 1419197 = 532199) (by norm_num)
theorem B1517501 : Blo 944585 1517501 := bbase (se 3 (by rfl) ⟨284531, by rfl⟩ : syracuseStep 1517501 = 569063) (by norm_num)
theorem B1419221 : Blo 944585 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B1419245 : Blo 944585 1419245 := bbase (se 3 (by rfl) ⟨266108, by rfl⟩ : syracuseStep 1419245 = 532217) (by norm_num)
theorem B1419269 : Blo 944585 1419269 := bbase (se 4 (by rfl) ⟨133056, by rfl⟩ : syracuseStep 1419269 = 266113) (by norm_num)
theorem B4794389 : Blo 944585 4794389 := bbase (se 6 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 4794389 = 224737) (by norm_num)
theorem B1419293 : Blo 944585 1419293 := bbase (se 3 (by rfl) ⟨266117, by rfl⟩ : syracuseStep 1419293 = 532235) (by norm_num)
theorem B1419317 : Blo 944585 1419317 := bbase (se 5 (by rfl) ⟨66530, by rfl⟩ : syracuseStep 1419317 = 133061) (by norm_num)
theorem B1419341 : Blo 944585 1419341 := bbase (se 3 (by rfl) ⟨266126, by rfl⟩ : syracuseStep 1419341 = 532253) (by norm_num)
theorem B13674581 : Blo 944585 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B1419365 : Blo 944585 1419365 := bbase (se 4 (by rfl) ⟨133065, by rfl⟩ : syracuseStep 1419365 = 266131) (by norm_num)
theorem B3418213 : Blo 944585 3418213 := bbase (se 4 (by rfl) ⟨320457, by rfl⟩ : syracuseStep 3418213 = 640915) (by norm_num)
theorem B1419389 : Blo 944585 1419389 := bbase (se 3 (by rfl) ⟨266135, by rfl⟩ : syracuseStep 1419389 = 532271) (by norm_num)
theorem B1419413 : Blo 944585 1419413 := bbase (se 6 (by rfl) ⟨33267, by rfl⟩ : syracuseStep 1419413 = 66535) (by norm_num)
theorem B1419437 : Blo 944585 1419437 := bbase (se 3 (by rfl) ⟨266144, by rfl⟩ : syracuseStep 1419437 = 532289) (by norm_num)
theorem B1419461 : Blo 944585 1419461 := bbase (se 4 (by rfl) ⟨133074, by rfl⟩ : syracuseStep 1419461 = 266149) (by norm_num)
theorem B1419485 : Blo 944585 1419485 := bbase (se 3 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 1419485 = 532307) (by norm_num)
theorem B1419509 : Blo 944585 1419509 := bbase (se 5 (by rfl) ⟨66539, by rfl⟩ : syracuseStep 1419509 = 133079) (by norm_num)
theorem B2271485 : Blo 944585 2271485 := bbase (se 3 (by rfl) ⟨425903, by rfl⟩ : syracuseStep 2271485 = 851807) (by norm_num)
theorem B1419533 : Blo 944585 1419533 := bbase (se 3 (by rfl) ⟨266162, by rfl⟩ : syracuseStep 1419533 = 532325) (by norm_num)
theorem B1419557 : Blo 944585 1419557 := bbase (se 4 (by rfl) ⟨133083, by rfl⟩ : syracuseStep 1419557 = 266167) (by norm_num)
theorem B1419581 : Blo 944585 1419581 := bbase (se 3 (by rfl) ⟨266171, by rfl⟩ : syracuseStep 1419581 = 532343) (by norm_num)
theorem B4041029 : Blo 944585 4041029 := bbase (se 4 (by rfl) ⟨378846, by rfl⟩ : syracuseStep 4041029 = 757693) (by norm_num)
theorem B3189077 : Blo 944585 3189077 := bbase (se 10 (by rfl) ⟨4671, by rfl⟩ : syracuseStep 3189077 = 9343) (by norm_num)
theorem B1419605 : Blo 944585 1419605 := bbase (se 10 (by rfl) ⟨2079, by rfl⟩ : syracuseStep 1419605 = 4159) (by norm_num)
theorem B1419629 : Blo 944585 1419629 := bbase (se 3 (by rfl) ⟨266180, by rfl⟩ : syracuseStep 1419629 = 532361) (by norm_num)
theorem B1419653 : Blo 944585 1419653 := bbase (se 4 (by rfl) ⟨133092, by rfl⟩ : syracuseStep 1419653 = 266185) (by norm_num)
theorem B1419677 : Blo 944585 1419677 := bbase (se 3 (by rfl) ⟨266189, by rfl⟩ : syracuseStep 1419677 = 532379) (by norm_num)
theorem B1419701 : Blo 944585 1419701 := bbase (se 5 (by rfl) ⟨66548, by rfl⟩ : syracuseStep 1419701 = 133097) (by norm_num)
theorem B1419725 : Blo 944585 1419725 := bbase (se 3 (by rfl) ⟨266198, by rfl⟩ : syracuseStep 1419725 = 532397) (by norm_num)
theorem B1419749 : Blo 944585 1419749 := bbase (se 4 (by rfl) ⟨133101, by rfl⟩ : syracuseStep 1419749 = 266203) (by norm_num)
theorem B1419773 : Blo 944585 1419773 := bbase (se 3 (by rfl) ⟨266207, by rfl⟩ : syracuseStep 1419773 = 532415) (by norm_num)
theorem B1419797 : Blo 944585 1419797 := bbase (se 6 (by rfl) ⟨33276, by rfl⟩ : syracuseStep 1419797 = 66553) (by norm_num)
theorem B12134933 : Blo 944585 12134933 := bbase (se 6 (by rfl) ⟨284412, by rfl⟩ : syracuseStep 12134933 = 568825) (by norm_num)
theorem B1419821 : Blo 944585 1419821 := bbase (se 3 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 1419821 = 532433) (by norm_num)
theorem B1419845 : Blo 944585 1419845 := bbase (se 4 (by rfl) ⟨133110, by rfl⟩ : syracuseStep 1419845 = 266221) (by norm_num)
theorem B4106821 : Blo 944585 4106821 := bbase (se 4 (by rfl) ⟨385014, by rfl⟩ : syracuseStep 4106821 = 770029) (by norm_num)
theorem B1419869 : Blo 944585 1419869 := bbase (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) (by norm_num)
theorem B1419893 : Blo 944585 1419893 := bbase (se 5 (by rfl) ⟨66557, by rfl⟩ : syracuseStep 1419893 = 133115) (by norm_num)
theorem B1419917 : Blo 944585 1419917 := bbase (se 3 (by rfl) ⟨266234, by rfl⟩ : syracuseStep 1419917 = 532469) (by norm_num)
theorem B1419941 : Blo 944585 1419941 := bbase (se 4 (by rfl) ⟨133119, by rfl⟩ : syracuseStep 1419941 = 266239) (by norm_num)
theorem B2697893 : Blo 944585 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B1419965 : Blo 944585 1419965 := bbase (se 3 (by rfl) ⟨266243, by rfl⟩ : syracuseStep 1419965 = 532487) (by norm_num)
theorem B1419989 : Blo 944585 1419989 := bbase (se 7 (by rfl) ⟨16640, by rfl⟩ : syracuseStep 1419989 = 33281) (by norm_num)
theorem B1420013 : Blo 944585 1420013 := bbase (se 3 (by rfl) ⟨266252, by rfl⟩ : syracuseStep 1420013 = 532505) (by norm_num)
theorem B3189509 : Blo 944585 3189509 := bbase (se 4 (by rfl) ⟨299016, by rfl⟩ : syracuseStep 3189509 = 598033) (by norm_num)
theorem B1420037 : Blo 944585 1420037 := bbase (se 4 (by rfl) ⟨133128, by rfl⟩ : syracuseStep 1420037 = 266257) (by norm_num)
theorem B1944341 : Blo 944585 1944341 := bbase (se 6 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 1944341 = 91141) (by norm_num)
theorem B1420061 : Blo 944585 1420061 := bbase (se 3 (by rfl) ⟨266261, by rfl⟩ : syracuseStep 1420061 = 532523) (by norm_num)
theorem B1420085 : Blo 944585 1420085 := bbase (se 5 (by rfl) ⟨66566, by rfl⟩ : syracuseStep 1420085 = 133133) (by norm_num)
theorem B1420109 : Blo 944585 1420109 := bbase (se 3 (by rfl) ⟨266270, by rfl⟩ : syracuseStep 1420109 = 532541) (by norm_num)
theorem B1420133 : Blo 944585 1420133 := bbase (se 4 (by rfl) ⟨133137, by rfl⟩ : syracuseStep 1420133 = 266275) (by norm_num)
theorem B1420157 : Blo 944585 1420157 := bbase (se 3 (by rfl) ⟨266279, by rfl⟩ : syracuseStep 1420157 = 532559) (by norm_num)
theorem B1420181 : Blo 944585 1420181 := bbase (se 6 (by rfl) ⟨33285, by rfl⟩ : syracuseStep 1420181 = 66571) (by norm_num)
theorem B1420205 : Blo 944585 1420205 := bbase (se 3 (by rfl) ⟨266288, by rfl⟩ : syracuseStep 1420205 = 532577) (by norm_num)
theorem B1420229 : Blo 944585 1420229 := bbase (se 4 (by rfl) ⟨133146, by rfl⟩ : syracuseStep 1420229 = 266293) (by norm_num)
theorem B1420253 : Blo 944585 1420253 := bbase (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) (by norm_num)
theorem B1420277 : Blo 944585 1420277 := bbase (se 5 (by rfl) ⟨66575, by rfl⟩ : syracuseStep 1420277 = 133151) (by norm_num)
theorem B1420301 : Blo 944585 1420301 := bbase (se 3 (by rfl) ⟨266306, by rfl⟩ : syracuseStep 1420301 = 532613) (by norm_num)
theorem B1420325 : Blo 944585 1420325 := bbase (se 4 (by rfl) ⟨133155, by rfl⟩ : syracuseStep 1420325 = 266311) (by norm_num)
theorem B1420349 : Blo 944585 1420349 := bbase (se 3 (by rfl) ⟨266315, by rfl⟩ : syracuseStep 1420349 = 532631) (by norm_num)
theorem B1420373 : Blo 944585 1420373 := bbase (se 8 (by rfl) ⟨8322, by rfl⟩ : syracuseStep 1420373 = 16645) (by norm_num)
theorem B1420397 : Blo 944585 1420397 := bbase (se 3 (by rfl) ⟨266324, by rfl⟩ : syracuseStep 1420397 = 532649) (by norm_num)
theorem B1420421 : Blo 944585 1420421 := bbase (se 4 (by rfl) ⟨133164, by rfl⟩ : syracuseStep 1420421 = 266329) (by norm_num)
theorem B1420445 : Blo 944585 1420445 := bbase (se 3 (by rfl) ⟨266333, by rfl⟩ : syracuseStep 1420445 = 532667) (by norm_num)
theorem B3189941 : Blo 944585 3189941 := bbase (se 5 (by rfl) ⟨149528, by rfl⟩ : syracuseStep 3189941 = 299057) (by norm_num)
theorem B1420469 : Blo 944585 1420469 := bbase (se 5 (by rfl) ⟨66584, by rfl⟩ : syracuseStep 1420469 = 133169) (by norm_num)
theorem B1420493 : Blo 944585 1420493 := bbase (se 3 (by rfl) ⟨266342, by rfl⟩ : syracuseStep 1420493 = 532685) (by norm_num)
theorem B1420517 : Blo 944585 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B1518821 : Blo 944585 1518821 := bbase (se 4 (by rfl) ⟨142389, by rfl⟩ : syracuseStep 1518821 = 284779) (by norm_num)
theorem B1420541 : Blo 944585 1420541 := bbase (se 3 (by rfl) ⟨266351, by rfl⟩ : syracuseStep 1420541 = 532703) (by norm_num)
theorem B1420565 : Blo 944585 1420565 := bbase (se 6 (by rfl) ⟨33294, by rfl⟩ : syracuseStep 1420565 = 66589) (by norm_num)
theorem B2272541 : Blo 944585 2272541 := bbase (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) (by norm_num)
theorem B4042021 : Blo 944585 4042021 := bbase (se 4 (by rfl) ⟨378939, by rfl⟩ : syracuseStep 4042021 = 757879) (by norm_num)
theorem B4795685 : Blo 944585 4795685 := bbase (se 4 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 4795685 = 899191) (by norm_num)
theorem B1420589 : Blo 944585 1420589 := bbase (se 3 (by rfl) ⟨266360, by rfl⟩ : syracuseStep 1420589 = 532721) (by norm_num)
theorem B1420613 : Blo 944585 1420613 := bbase (se 4 (by rfl) ⟨133182, by rfl⟩ : syracuseStep 1420613 = 266365) (by norm_num)
theorem B1518917 : Blo 944585 1518917 := bbase (se 4 (by rfl) ⟨142398, by rfl⟩ : syracuseStep 1518917 = 284797) (by norm_num)
theorem B1420637 : Blo 944585 1420637 := bbase (se 3 (by rfl) ⟨266369, by rfl⟩ : syracuseStep 1420637 = 532739) (by norm_num)
theorem B1518949 : Blo 944585 1518949 := bbase (se 4 (by rfl) ⟨142401, by rfl⟩ : syracuseStep 1518949 = 284803) (by norm_num)
theorem B1420661 : Blo 944585 1420661 := bbase (se 5 (by rfl) ⟨66593, by rfl⟩ : syracuseStep 1420661 = 133187) (by norm_num)
theorem B1420685 : Blo 944585 1420685 := bbase (se 3 (by rfl) ⟨266378, by rfl⟩ : syracuseStep 1420685 = 532757) (by norm_num)
theorem B1420709 : Blo 944585 1420709 := bbase (se 4 (by rfl) ⟨133191, by rfl⟩ : syracuseStep 1420709 = 266383) (by norm_num)
theorem B1420733 : Blo 944585 1420733 := bbase (se 3 (by rfl) ⟨266387, by rfl⟩ : syracuseStep 1420733 = 532775) (by norm_num)
theorem B1420757 : Blo 944585 1420757 := bbase (se 7 (by rfl) ⟨16649, by rfl⟩ : syracuseStep 1420757 = 33299) (by norm_num)
theorem B1420781 : Blo 944585 1420781 := bbase (se 3 (by rfl) ⟨266396, by rfl⟩ : syracuseStep 1420781 = 532793) (by norm_num)
theorem B1420805 : Blo 944585 1420805 := bbase (se 4 (by rfl) ⟨133200, by rfl⟩ : syracuseStep 1420805 = 266401) (by norm_num)
theorem B1420829 : Blo 944585 1420829 := bbase (se 3 (by rfl) ⟨266405, by rfl⟩ : syracuseStep 1420829 = 532811) (by norm_num)
theorem B1420853 : Blo 944585 1420853 := bbase (se 5 (by rfl) ⟨66602, by rfl⟩ : syracuseStep 1420853 = 133205) (by norm_num)
theorem B1420877 : Blo 944585 1420877 := bbase (se 3 (by rfl) ⟨266414, by rfl⟩ : syracuseStep 1420877 = 532829) (by norm_num)
theorem B3190373 : Blo 944585 3190373 := bbase (se 4 (by rfl) ⟨299097, by rfl⟩ : syracuseStep 3190373 = 598195) (by norm_num)
theorem B1420901 : Blo 944585 1420901 := bbase (se 4 (by rfl) ⟨133209, by rfl⟩ : syracuseStep 1420901 = 266419) (by norm_num)
theorem B1420925 : Blo 944585 1420925 := bbase (se 3 (by rfl) ⟨266423, by rfl⟩ : syracuseStep 1420925 = 532847) (by norm_num)
theorem B1420949 : Blo 944585 1420949 := bbase (se 6 (by rfl) ⟨33303, by rfl⟩ : syracuseStep 1420949 = 66607) (by norm_num)
theorem B1420973 : Blo 944585 1420973 := bbase (se 3 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 1420973 = 532865) (by norm_num)
theorem B1420997 : Blo 944585 1420997 := bbase (se 4 (by rfl) ⟨133218, by rfl⟩ : syracuseStep 1420997 = 266437) (by norm_num)
theorem B10235605 : Blo 944585 10235605 := bbase (se 7 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 10235605 = 239897) (by norm_num)
theorem B1421021 : Blo 944585 1421021 := bbase (se 3 (by rfl) ⟨266441, by rfl⟩ : syracuseStep 1421021 = 532883) (by norm_num)
theorem B1421045 : Blo 944585 1421045 := bbase (se 5 (by rfl) ⟨66611, by rfl⟩ : syracuseStep 1421045 = 133223) (by norm_num)
theorem B1421069 : Blo 944585 1421069 := bbase (se 3 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 1421069 = 532901) (by norm_num)
theorem B1421093 : Blo 944585 1421093 := bbase (se 4 (by rfl) ⟨133227, by rfl⟩ : syracuseStep 1421093 = 266455) (by norm_num)
theorem B1421117 : Blo 944585 1421117 := bbase (se 3 (by rfl) ⟨266459, by rfl⟩ : syracuseStep 1421117 = 532919) (by norm_num)
theorem B2699077 : Blo 944585 2699077 := bbase (se 4 (by rfl) ⟨253038, by rfl⟩ : syracuseStep 2699077 = 506077) (by norm_num)
theorem B1421141 : Blo 944585 1421141 := bbase (se 9 (by rfl) ⟨4163, by rfl⟩ : syracuseStep 1421141 = 8327) (by norm_num)
theorem B1421165 : Blo 944585 1421165 := bbase (se 3 (by rfl) ⟨266468, by rfl⟩ : syracuseStep 1421165 = 532937) (by norm_num)
theorem B1421189 : Blo 944585 1421189 := bbase (se 4 (by rfl) ⟨133236, by rfl⟩ : syracuseStep 1421189 = 266473) (by norm_num)
theorem B1421213 : Blo 944585 1421213 := bbase (se 3 (by rfl) ⟨266477, by rfl⟩ : syracuseStep 1421213 = 532955) (by norm_num)
theorem B1421237 : Blo 944585 1421237 := bbase (se 5 (by rfl) ⟨66620, by rfl⟩ : syracuseStep 1421237 = 133241) (by norm_num)
theorem B1421261 : Blo 944585 1421261 := bbase (se 3 (by rfl) ⟨266486, by rfl⟩ : syracuseStep 1421261 = 532973) (by norm_num)
theorem B1421285 : Blo 944585 1421285 := bbase (se 4 (by rfl) ⟨133245, by rfl⟩ : syracuseStep 1421285 = 266491) (by norm_num)
theorem B2699237 : Blo 944585 2699237 := bbase (se 4 (by rfl) ⟨253053, by rfl⟩ : syracuseStep 2699237 = 506107) (by norm_num)
theorem B1421309 : Blo 944585 1421309 := bbase (se 3 (by rfl) ⟨266495, by rfl⟩ : syracuseStep 1421309 = 532991) (by norm_num)
theorem B3190805 : Blo 944585 3190805 := bbase (se 6 (by rfl) ⟨74784, by rfl⟩ : syracuseStep 3190805 = 149569) (by norm_num)
theorem B1421333 : Blo 944585 1421333 := bbase (se 6 (by rfl) ⟨33312, by rfl⟩ : syracuseStep 1421333 = 66625) (by norm_num)
theorem B1421357 : Blo 944585 1421357 := bbase (se 3 (by rfl) ⟨266504, by rfl⟩ : syracuseStep 1421357 = 533009) (by norm_num)
theorem B1421381 : Blo 944585 1421381 := bbase (se 4 (by rfl) ⟨133254, by rfl⟩ : syracuseStep 1421381 = 266509) (by norm_num)
theorem B1421405 : Blo 944585 1421405 := bbase (se 3 (by rfl) ⟨266513, by rfl⟩ : syracuseStep 1421405 = 533027) (by norm_num)
theorem B1421429 : Blo 944585 1421429 := bbase (se 5 (by rfl) ⟨66629, by rfl⟩ : syracuseStep 1421429 = 133259) (by norm_num)
theorem B1421453 : Blo 944585 1421453 := bbase (se 3 (by rfl) ⟨266522, by rfl⟩ : syracuseStep 1421453 = 533045) (by norm_num)
theorem B1421477 : Blo 944585 1421477 := bbase (se 4 (by rfl) ⟨133263, by rfl⟩ : syracuseStep 1421477 = 266527) (by norm_num)
theorem B1421501 : Blo 944585 1421501 := bbase (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) (by norm_num)
theorem B1421525 : Blo 944585 1421525 := bbase (se 7 (by rfl) ⟨16658, by rfl⟩ : syracuseStep 1421525 = 33317) (by norm_num)
theorem B2699477 : Blo 944585 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1421549 : Blo 944585 1421549 := bbase (se 3 (by rfl) ⟨266540, by rfl⟩ : syracuseStep 1421549 = 533081) (by norm_num)
theorem B1421573 : Blo 944585 1421573 := bbase (se 4 (by rfl) ⟨133272, by rfl⟩ : syracuseStep 1421573 = 266545) (by norm_num)
theorem B12955925 : Blo 944585 12955925 := bbase (se 6 (by rfl) ⟨303654, by rfl⟩ : syracuseStep 12955925 = 607309) (by norm_num)
theorem B1421597 : Blo 944585 1421597 := bbase (se 3 (by rfl) ⟨266549, by rfl⟩ : syracuseStep 1421597 = 533099) (by norm_num)
theorem B1421621 : Blo 944585 1421621 := bbase (se 5 (by rfl) ⟨66638, by rfl⟩ : syracuseStep 1421621 = 133277) (by norm_num)
theorem B1421645 : Blo 944585 1421645 := bbase (se 3 (by rfl) ⟨266558, by rfl⟩ : syracuseStep 1421645 = 533117) (by norm_num)
theorem B1421669 : Blo 944585 1421669 := bbase (se 4 (by rfl) ⟨133281, by rfl⟩ : syracuseStep 1421669 = 266563) (by norm_num)
theorem B1421693 : Blo 944585 1421693 := bbase (se 3 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 1421693 = 533135) (by norm_num)
theorem B18428309 : Blo 944585 18428309 := bbase (se 6 (by rfl) ⟨431913, by rfl⟩ : syracuseStep 18428309 = 863827) (by norm_num)
theorem B1421717 : Blo 944585 1421717 := bbase (se 6 (by rfl) ⟨33321, by rfl⟩ : syracuseStep 1421717 = 66643) (by norm_num)
theorem B2699669 : Blo 944585 2699669 := bbase (se 6 (by rfl) ⟨63273, by rfl⟩ : syracuseStep 2699669 = 126547) (by norm_num)
theorem B1421741 : Blo 944585 1421741 := bbase (se 3 (by rfl) ⟨266576, by rfl⟩ : syracuseStep 1421741 = 533153) (by norm_num)
theorem B7287221 : Blo 944585 7287221 := bbase (se 5 (by rfl) ⟨341588, by rfl⟩ : syracuseStep 7287221 = 683177) (by norm_num)
theorem B3191237 : Blo 944585 3191237 := bbase (se 4 (by rfl) ⟨299178, by rfl⟩ : syracuseStep 3191237 = 598357) (by norm_num)
theorem B1421765 : Blo 944585 1421765 := bbase (se 4 (by rfl) ⟨133290, by rfl⟩ : syracuseStep 1421765 = 266581) (by norm_num)
theorem B1421789 : Blo 944585 1421789 := bbase (se 3 (by rfl) ⟨266585, by rfl⟩ : syracuseStep 1421789 = 533171) (by norm_num)
theorem B1421813 : Blo 944585 1421813 := bbase (se 5 (by rfl) ⟨66647, by rfl⟩ : syracuseStep 1421813 = 133295) (by norm_num)
theorem B1421837 : Blo 944585 1421837 := bbase (se 3 (by rfl) ⟨266594, by rfl⟩ : syracuseStep 1421837 = 533189) (by norm_num)
theorem B1421861 : Blo 944585 1421861 := bbase (se 4 (by rfl) ⟨133299, by rfl⟩ : syracuseStep 1421861 = 266599) (by norm_num)
theorem B4796981 : Blo 944585 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B1421885 : Blo 944585 1421885 := bbase (se 3 (by rfl) ⟨266603, by rfl⟩ : syracuseStep 1421885 = 533207) (by norm_num)
theorem B1421909 : Blo 944585 1421909 := bbase (se 8 (by rfl) ⟨8331, by rfl⟩ : syracuseStep 1421909 = 16663) (by norm_num)
theorem B1421933 : Blo 944585 1421933 := bbase (se 3 (by rfl) ⟨266612, by rfl⟩ : syracuseStep 1421933 = 533225) (by norm_num)
theorem B1421957 : Blo 944585 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B1421981 : Blo 944585 1421981 := bbase (se 3 (by rfl) ⟨266621, by rfl⟩ : syracuseStep 1421981 = 533243) (by norm_num)
theorem B1422005 : Blo 944585 1422005 := bbase (se 5 (by rfl) ⟨66656, by rfl⟩ : syracuseStep 1422005 = 133313) (by norm_num)
theorem B1422029 : Blo 944585 1422029 := bbase (se 3 (by rfl) ⟨266630, by rfl⟩ : syracuseStep 1422029 = 533261) (by norm_num)
theorem B1422053 : Blo 944585 1422053 := bbase (se 4 (by rfl) ⟨133317, by rfl⟩ : syracuseStep 1422053 = 266635) (by norm_num)
theorem B1422077 : Blo 944585 1422077 := bbase (se 3 (by rfl) ⟨266639, by rfl⟩ : syracuseStep 1422077 = 533279) (by norm_num)
theorem B1422101 : Blo 944585 1422101 := bbase (se 6 (by rfl) ⟨33330, by rfl⟩ : syracuseStep 1422101 = 66661) (by norm_num)
theorem B1422125 : Blo 944585 1422125 := bbase (se 3 (by rfl) ⟨266648, by rfl⟩ : syracuseStep 1422125 = 533297) (by norm_num)
theorem B1422149 : Blo 944585 1422149 := bbase (se 4 (by rfl) ⟨133326, by rfl⟩ : syracuseStep 1422149 = 266653) (by norm_num)
theorem B1422173 : Blo 944585 1422173 := bbase (se 3 (by rfl) ⟨266657, by rfl⟩ : syracuseStep 1422173 = 533315) (by norm_num)
theorem B3191669 : Blo 944585 3191669 := bbase (se 5 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 3191669 = 299219) (by norm_num)
theorem B1422197 : Blo 944585 1422197 := bbase (se 5 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 1422197 = 133331) (by norm_num)
theorem B1422221 : Blo 944585 1422221 := bbase (se 3 (by rfl) ⟨266666, by rfl⟩ : syracuseStep 1422221 = 533333) (by norm_num)
theorem B7189397 : Blo 944585 7189397 := bbase (se 6 (by rfl) ⟨168501, by rfl⟩ : syracuseStep 7189397 = 337003) (by norm_num)
theorem B1422245 : Blo 944585 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B1422269 : Blo 944585 1422269 := bbase (se 3 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 1422269 = 533351) (by norm_num)
theorem B1422293 : Blo 944585 1422293 := bbase (se 7 (by rfl) ⟨16667, by rfl⟩ : syracuseStep 1422293 = 33335) (by norm_num)
theorem B1422317 : Blo 944585 1422317 := bbase (se 3 (by rfl) ⟨266684, by rfl⟩ : syracuseStep 1422317 = 533369) (by norm_num)
theorem B1422341 : Blo 944585 1422341 := bbase (se 4 (by rfl) ⟨133344, by rfl⟩ : syracuseStep 1422341 = 266689) (by norm_num)
theorem B1422365 : Blo 944585 1422365 := bbase (se 3 (by rfl) ⟨266693, by rfl⟩ : syracuseStep 1422365 = 533387) (by norm_num)
theorem B1422389 : Blo 944585 1422389 := bbase (se 5 (by rfl) ⟨66674, by rfl⟩ : syracuseStep 1422389 = 133349) (by norm_num)
theorem B1422413 : Blo 944585 1422413 := bbase (se 3 (by rfl) ⟨266702, by rfl⟩ : syracuseStep 1422413 = 533405) (by norm_num)
theorem B1422437 : Blo 944585 1422437 := bbase (se 4 (by rfl) ⟨133353, by rfl⟩ : syracuseStep 1422437 = 266707) (by norm_num)
theorem B1422461 : Blo 944585 1422461 := bbase (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) (by norm_num)
theorem B1422485 : Blo 944585 1422485 := bbase (se 6 (by rfl) ⟨33339, by rfl⟩ : syracuseStep 1422485 = 66679) (by norm_num)
theorem B1422509 : Blo 944585 1422509 := bbase (se 3 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 1422509 = 533441) (by norm_num)
theorem B1422533 : Blo 944585 1422533 := bbase (se 4 (by rfl) ⟨133362, by rfl⟩ : syracuseStep 1422533 = 266725) (by norm_num)
theorem B1422557 : Blo 944585 1422557 := bbase (se 3 (by rfl) ⟨266729, by rfl⟩ : syracuseStep 1422557 = 533459) (by norm_num)
theorem B1422581 : Blo 944585 1422581 := bbase (se 5 (by rfl) ⟨66683, by rfl⟩ : syracuseStep 1422581 = 133367) (by norm_num)
theorem B2733317 : Blo 944585 2733317 := bbase (se 4 (by rfl) ⟨256248, by rfl⟩ : syracuseStep 2733317 = 512497) (by norm_num)
theorem B1422605 : Blo 944585 1422605 := bbase (se 3 (by rfl) ⟨266738, by rfl⟩ : syracuseStep 1422605 = 533477) (by norm_num)
theorem B3028261 : Blo 944585 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B3192101 : Blo 944585 3192101 := bbase (se 4 (by rfl) ⟨299259, by rfl⟩ : syracuseStep 3192101 = 598519) (by norm_num)
theorem B1422629 : Blo 944585 1422629 := bbase (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) (by norm_num)
theorem B1422653 : Blo 944585 1422653 := bbase (se 3 (by rfl) ⟨266747, by rfl⟩ : syracuseStep 1422653 = 533495) (by norm_num)
theorem B1422677 : Blo 944585 1422677 := bbase (se 13 (by rfl) ⟨260, by rfl⟩ : syracuseStep 1422677 = 521) (by norm_num)
theorem B1619293 : Blo 944585 1619293 := bbase (se 3 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 1619293 = 607235) (by norm_num)
theorem B1422701 : Blo 944585 1422701 := bbase (se 3 (by rfl) ⟨266756, by rfl⟩ : syracuseStep 1422701 = 533513) (by norm_num)
theorem B2700661 : Blo 944585 2700661 := bbase (se 5 (by rfl) ⟨126593, by rfl⟩ : syracuseStep 2700661 = 253187) (by norm_num)
theorem B1422725 : Blo 944585 1422725 := bbase (se 4 (by rfl) ⟨133380, by rfl⟩ : syracuseStep 1422725 = 266761) (by norm_num)
theorem B1422749 : Blo 944585 1422749 := bbase (se 3 (by rfl) ⟨266765, by rfl⟩ : syracuseStep 1422749 = 533531) (by norm_num)
theorem B2274733 : Blo 944585 2274733 := bbase (se 3 (by rfl) ⟨426512, by rfl⟩ : syracuseStep 2274733 = 853025) (by norm_num)
theorem B1422773 : Blo 944585 1422773 := bbase (se 5 (by rfl) ⟨66692, by rfl⟩ : syracuseStep 1422773 = 133385) (by norm_num)
theorem B1422797 : Blo 944585 1422797 := bbase (se 3 (by rfl) ⟨266774, by rfl⟩ : syracuseStep 1422797 = 533549) (by norm_num)
theorem B1422821 : Blo 944585 1422821 := bbase (se 4 (by rfl) ⟨133389, by rfl⟩ : syracuseStep 1422821 = 266779) (by norm_num)
theorem B1422845 : Blo 944585 1422845 := bbase (se 3 (by rfl) ⟨266783, by rfl⟩ : syracuseStep 1422845 = 533567) (by norm_num)
theorem B1422869 : Blo 944585 1422869 := bbase (se 6 (by rfl) ⟨33348, by rfl⟩ : syracuseStep 1422869 = 66697) (by norm_num)
theorem B3028517 : Blo 944585 3028517 := bbase (se 4 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 3028517 = 567847) (by norm_num)
theorem B1619525 : Blo 944585 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B6305365 : Blo 944585 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B3192533 : Blo 944585 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B1062661 : Blo 944585 1062661 := bbase (se 4 (by rfl) ⟨99624, by rfl⟩ : syracuseStep 1062661 = 199249) (by norm_num)
theorem B1062697 : Blo 944585 1062697 := bbase (se 2 (by rfl) ⟨398511, by rfl⟩ : syracuseStep 1062697 = 797023) (by norm_num)
theorem B4798277 : Blo 944585 4798277 := bbase (se 4 (by rfl) ⟨449838, by rfl⟩ : syracuseStep 4798277 = 899677) (by norm_num)
theorem B1062733 : Blo 944585 1062733 := bbase (se 3 (by rfl) ⟨199262, by rfl⟩ : syracuseStep 1062733 = 398525) (by norm_num)
theorem B1062769 : Blo 944585 1062769 := bbase (se 2 (by rfl) ⟨398538, by rfl⟩ : syracuseStep 1062769 = 797077) (by norm_num)
theorem B1062805 : Blo 944585 1062805 := bbase (se 6 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 1062805 = 49819) (by norm_num)
theorem B1062841 : Blo 944585 1062841 := bbase (se 2 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 1062841 = 797131) (by norm_num)
theorem B1062877 : Blo 944585 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B1062913 : Blo 944585 1062913 := bbase (se 2 (by rfl) ⟨398592, by rfl⟩ : syracuseStep 1062913 = 797185) (by norm_num)
theorem B1619989 : Blo 944585 1619989 := bbase (se 6 (by rfl) ⟨37968, by rfl⟩ : syracuseStep 1619989 = 75937) (by norm_num)
theorem B1062949 : Blo 944585 1062949 := bbase (se 4 (by rfl) ⟨99651, by rfl⟩ : syracuseStep 1062949 = 199303) (by norm_num)
theorem B1062985 : Blo 944585 1062985 := bbase (se 2 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 1062985 = 797239) (by norm_num)
theorem B1063021 : Blo 944585 1063021 := bbase (se 3 (by rfl) ⟨199316, by rfl⟩ : syracuseStep 1063021 = 398633) (by norm_num)
theorem B3192965 : Blo 944585 3192965 := bbase (se 4 (by rfl) ⟨299340, by rfl⟩ : syracuseStep 3192965 = 598681) (by norm_num)
theorem B1063057 : Blo 944585 1063057 := bbase (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) (by norm_num)
theorem B6076565 : Blo 944585 6076565 := bbase (se 6 (by rfl) ⟨142419, by rfl⟩ : syracuseStep 6076565 = 284839) (by norm_num)
theorem B1063093 : Blo 944585 1063093 := bbase (se 5 (by rfl) ⟨49832, by rfl⟩ : syracuseStep 1063093 = 99665) (by norm_num)
theorem B1063129 : Blo 944585 1063129 := bbase (se 2 (by rfl) ⟨398673, by rfl⟩ : syracuseStep 1063129 = 797347) (by norm_num)
theorem B1063165 : Blo 944585 1063165 := bbase (se 3 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 1063165 = 398687) (by norm_num)
theorem B1063201 : Blo 944585 1063201 := bbase (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) (by norm_num)
theorem B1063237 : Blo 944585 1063237 := bbase (se 4 (by rfl) ⟨99678, by rfl⟩ : syracuseStep 1063237 = 199357) (by norm_num)
theorem B1063273 : Blo 944585 1063273 := bbase (se 2 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 1063273 = 797455) (by norm_num)
theorem B1063309 : Blo 944585 1063309 := bbase (se 3 (by rfl) ⟨199370, by rfl⟩ : syracuseStep 1063309 = 398741) (by norm_num)
theorem B1915285 : Blo 944585 1915285 := bbase (se 6 (by rfl) ⟨44889, by rfl⟩ : syracuseStep 1915285 = 89779) (by norm_num)
theorem B1063345 : Blo 944585 1063345 := bbase (se 2 (by rfl) ⟨398754, by rfl⟩ : syracuseStep 1063345 = 797509) (by norm_num)
theorem B1063381 : Blo 944585 1063381 := bbase (se 7 (by rfl) ⟨12461, by rfl⟩ : syracuseStep 1063381 = 24923) (by norm_num)
theorem B1063417 : Blo 944585 1063417 := bbase (se 2 (by rfl) ⟨398781, by rfl⟩ : syracuseStep 1063417 = 797563) (by norm_num)
theorem B1063453 : Blo 944585 1063453 := bbase (se 3 (by rfl) ⟨199397, by rfl⟩ : syracuseStep 1063453 = 398795) (by norm_num)
theorem B3193397 : Blo 944585 3193397 := bbase (se 5 (by rfl) ⟨149690, by rfl⟩ : syracuseStep 3193397 = 299381) (by norm_num)
theorem B1063489 : Blo 944585 1063489 := bbase (se 2 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 1063489 = 797617) (by norm_num)
theorem B1063525 : Blo 944585 1063525 := bbase (se 4 (by rfl) ⟨99705, by rfl⟩ : syracuseStep 1063525 = 199411) (by norm_num)
theorem B1063561 : Blo 944585 1063561 := bbase (se 2 (by rfl) ⟨398835, by rfl⟩ : syracuseStep 1063561 = 797671) (by norm_num)
theorem B1063597 : Blo 944585 1063597 := bbase (se 3 (by rfl) ⟨199424, by rfl⟩ : syracuseStep 1063597 = 398849) (by norm_num)
theorem B1063633 : Blo 944585 1063633 := bbase (se 2 (by rfl) ⟨398862, by rfl⟩ : syracuseStep 1063633 = 797725) (by norm_num)
theorem B1063669 : Blo 944585 1063669 := bbase (se 5 (by rfl) ⟨49859, by rfl⟩ : syracuseStep 1063669 = 99719) (by norm_num)
theorem B2276117 : Blo 944585 2276117 := bbase (se 6 (by rfl) ⟨53346, by rfl⟩ : syracuseStep 2276117 = 106693) (by norm_num)
theorem B1063705 : Blo 944585 1063705 := bbase (se 2 (by rfl) ⟨398889, by rfl⟩ : syracuseStep 1063705 = 797779) (by norm_num)
theorem B1063741 : Blo 944585 1063741 := bbase (se 3 (by rfl) ⟨199451, by rfl⟩ : syracuseStep 1063741 = 398903) (by norm_num)
theorem B1063777 : Blo 944585 1063777 := bbase (se 2 (by rfl) ⟨398916, by rfl⟩ : syracuseStep 1063777 = 797833) (by norm_num)
theorem B1063813 : Blo 944585 1063813 := bbase (se 4 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 1063813 = 199465) (by norm_num)
theorem B1915805 : Blo 944585 1915805 := bbase (se 3 (by rfl) ⟨359213, by rfl⟩ : syracuseStep 1915805 = 718427) (by norm_num)
theorem B1063849 : Blo 944585 1063849 := bbase (se 2 (by rfl) ⟨398943, by rfl⟩ : syracuseStep 1063849 = 797887) (by norm_num)
theorem B1063885 : Blo 944585 1063885 := bbase (se 3 (by rfl) ⟨199478, by rfl⟩ : syracuseStep 1063885 = 398957) (by norm_num)
theorem B2276309 : Blo 944585 2276309 := bbase (se 7 (by rfl) ⟨26675, by rfl⟩ : syracuseStep 2276309 = 53351) (by norm_num)
theorem B3193829 : Blo 944585 3193829 := bbase (se 4 (by rfl) ⟨299421, by rfl⟩ : syracuseStep 3193829 = 598843) (by norm_num)
theorem B1063921 : Blo 944585 1063921 := bbase (se 2 (by rfl) ⟨398970, by rfl⟩ : syracuseStep 1063921 = 797941) (by norm_num)
theorem B1063957 : Blo 944585 1063957 := bbase (se 6 (by rfl) ⟨24936, by rfl⟩ : syracuseStep 1063957 = 49873) (by norm_num)
theorem B3456053 : Blo 944585 3456053 := bbase (se 5 (by rfl) ⟨162002, by rfl⟩ : syracuseStep 3456053 = 324005) (by norm_num)
theorem B1063993 : Blo 944585 1063993 := bbase (se 2 (by rfl) ⟨398997, by rfl⟩ : syracuseStep 1063993 = 797995) (by norm_num)
theorem B4799573 : Blo 944585 4799573 := bbase (se 8 (by rfl) ⟨28122, by rfl⟩ : syracuseStep 4799573 = 56245) (by norm_num)
theorem B1064029 : Blo 944585 1064029 := bbase (se 3 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 1064029 = 399011) (by norm_num)
theorem B1064065 : Blo 944585 1064065 := bbase (se 2 (by rfl) ⟨399024, by rfl⟩ : syracuseStep 1064065 = 798049) (by norm_num)
theorem B1064101 : Blo 944585 1064101 := bbase (se 4 (by rfl) ⟨99759, by rfl⟩ : syracuseStep 1064101 = 199519) (by norm_num)
theorem B1064137 : Blo 944585 1064137 := bbase (se 2 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 1064137 = 798103) (by norm_num)
theorem B1064173 : Blo 944585 1064173 := bbase (se 3 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 1064173 = 399065) (by norm_num)
theorem B1064209 : Blo 944585 1064209 := bbase (se 2 (by rfl) ⟨399078, by rfl⟩ : syracuseStep 1064209 = 798157) (by norm_num)
theorem B1064245 : Blo 944585 1064245 := bbase (se 5 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 1064245 = 99773) (by norm_num)
theorem B1064281 : Blo 944585 1064281 := bbase (se 2 (by rfl) ⟨399105, by rfl⟩ : syracuseStep 1064281 = 798211) (by norm_num)
theorem B1064317 : Blo 944585 1064317 := bbase (se 3 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 1064317 = 399119) (by norm_num)
theorem B3194261 : Blo 944585 3194261 := bbase (se 6 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 3194261 = 149731) (by norm_num)
theorem B1064353 : Blo 944585 1064353 := bbase (se 2 (by rfl) ⟨399132, by rfl⟩ : syracuseStep 1064353 = 798265) (by norm_num)
theorem B1064389 : Blo 944585 1064389 := bbase (se 4 (by rfl) ⟨99786, by rfl⟩ : syracuseStep 1064389 = 199573) (by norm_num)
theorem B1064425 : Blo 944585 1064425 := bbase (se 2 (by rfl) ⟨399159, by rfl⟩ : syracuseStep 1064425 = 798319) (by norm_num)
theorem B1064461 : Blo 944585 1064461 := bbase (se 3 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 1064461 = 399173) (by norm_num)
theorem B1064497 : Blo 944585 1064497 := bbase (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) (by norm_num)
theorem B1064533 : Blo 944585 1064533 := bbase (se 8 (by rfl) ⟨6237, by rfl⟩ : syracuseStep 1064533 = 12475) (by norm_num)
theorem B1064569 : Blo 944585 1064569 := bbase (se 2 (by rfl) ⟨399213, by rfl⟩ : syracuseStep 1064569 = 798427) (by norm_num)
theorem B1195661 : Blo 944585 1195661 := bbase (se 3 (by rfl) ⟨224186, by rfl⟩ : syracuseStep 1195661 = 448373) (by norm_num)
theorem B1064605 : Blo 944585 1064605 := bbase (se 3 (by rfl) ⟨199613, by rfl⟩ : syracuseStep 1064605 = 399227) (by norm_num)
theorem B1064641 : Blo 944585 1064641 := bbase (se 2 (by rfl) ⟨399240, by rfl⟩ : syracuseStep 1064641 = 798481) (by norm_num)
theorem B1195717 : Blo 944585 1195717 := bbase (se 4 (by rfl) ⟨112098, by rfl⟩ : syracuseStep 1195717 = 224197) (by norm_num)
theorem B2277077 : Blo 944585 2277077 := bbase (se 7 (by rfl) ⟨26684, by rfl⟩ : syracuseStep 2277077 = 53369) (by norm_num)
theorem B1064677 : Blo 944585 1064677 := bbase (se 4 (by rfl) ⟨99813, by rfl⟩ : syracuseStep 1064677 = 199627) (by norm_num)
theorem B1064713 : Blo 944585 1064713 := bbase (se 2 (by rfl) ⟨399267, by rfl⟩ : syracuseStep 1064713 = 798535) (by norm_num)
theorem B1195813 : Blo 944585 1195813 := bbase (se 4 (by rfl) ⟨112107, by rfl⟩ : syracuseStep 1195813 = 224215) (by norm_num)
theorem B1064749 : Blo 944585 1064749 := bbase (se 3 (by rfl) ⟨199640, by rfl⟩ : syracuseStep 1064749 = 399281) (by norm_num)
theorem B3194693 : Blo 944585 3194693 := bbase (se 4 (by rfl) ⟨299502, by rfl⟩ : syracuseStep 3194693 = 599005) (by norm_num)
theorem B1064785 : Blo 944585 1064785 := bbase (se 2 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 1064785 = 798589) (by norm_num)
theorem B1064821 : Blo 944585 1064821 := bbase (se 5 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 1064821 = 99827) (by norm_num)
theorem B1064857 : Blo 944585 1064857 := bbase (se 2 (by rfl) ⟨399321, by rfl⟩ : syracuseStep 1064857 = 798643) (by norm_num)
theorem B1458109 : Blo 944585 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1064893 : Blo 944585 1064893 := bbase (se 3 (by rfl) ⟨199667, by rfl⟩ : syracuseStep 1064893 = 399335) (by norm_num)
theorem B1195985 : Blo 944585 1195985 := bbase (se 2 (by rfl) ⟨448494, by rfl⟩ : syracuseStep 1195985 = 896989) (by norm_num)
theorem B1064929 : Blo 944585 1064929 := bbase (se 2 (by rfl) ⟨399348, by rfl⟩ : syracuseStep 1064929 = 798697) (by norm_num)
theorem B1064965 : Blo 944585 1064965 := bbase (se 4 (by rfl) ⟨99840, by rfl⟩ : syracuseStep 1064965 = 199681) (by norm_num)
theorem B1196041 : Blo 944585 1196041 := bbase (se 2 (by rfl) ⟨448515, by rfl⟩ : syracuseStep 1196041 = 897031) (by norm_num)
theorem B1065001 : Blo 944585 1065001 := bbase (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) (by norm_num)
theorem B1065037 : Blo 944585 1065037 := bbase (se 3 (by rfl) ⟨199694, by rfl⟩ : syracuseStep 1065037 = 399389) (by norm_num)
theorem B1196137 : Blo 944585 1196137 := bbase (se 2 (by rfl) ⟨448551, by rfl⟩ : syracuseStep 1196137 = 897103) (by norm_num)
theorem B1917037 : Blo 944585 1917037 := bbase (se 3 (by rfl) ⟨359444, by rfl⟩ : syracuseStep 1917037 = 718889) (by norm_num)
theorem B1065073 : Blo 944585 1065073 := bbase (se 2 (by rfl) ⟨399402, by rfl⟩ : syracuseStep 1065073 = 798805) (by norm_num)
theorem B3588245 : Blo 944585 3588245 := bbase (se 6 (by rfl) ⟨84099, by rfl⟩ : syracuseStep 3588245 = 168199) (by norm_num)
theorem B1065109 : Blo 944585 1065109 := bbase (se 6 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 1065109 = 49927) (by norm_num)
theorem B1917101 : Blo 944585 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B4047029 : Blo 944585 4047029 := bbase (se 5 (by rfl) ⟨189704, by rfl⟩ : syracuseStep 4047029 = 379409) (by norm_num)
theorem B1065145 : Blo 944585 1065145 := bbase (se 2 (by rfl) ⟨399429, by rfl⟩ : syracuseStep 1065145 = 798859) (by norm_num)
theorem B8536277 : Blo 944585 8536277 := bbase (se 7 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 8536277 = 200069) (by norm_num)
theorem B1065181 : Blo 944585 1065181 := bbase (se 3 (by rfl) ⟨199721, by rfl⟩ : syracuseStep 1065181 = 399443) (by norm_num)
theorem B3031285 : Blo 944585 3031285 := bbase (se 5 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 3031285 = 284183) (by norm_num)
theorem B3195125 : Blo 944585 3195125 := bbase (se 5 (by rfl) ⟨149771, by rfl⟩ : syracuseStep 3195125 = 299543) (by norm_num)
theorem B1065217 : Blo 944585 1065217 := bbase (se 2 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 1065217 = 798913) (by norm_num)
theorem B1196309 : Blo 944585 1196309 := bbase (se 6 (by rfl) ⟨28038, by rfl⟩ : syracuseStep 1196309 = 56077) (by norm_num)
theorem B1065253 : Blo 944585 1065253 := bbase (se 4 (by rfl) ⟨99867, by rfl⟩ : syracuseStep 1065253 = 199735) (by norm_num)
theorem B4309301 : Blo 944585 4309301 := bbase (se 5 (by rfl) ⟨201998, by rfl⟩ : syracuseStep 4309301 = 403997) (by norm_num)
theorem B1065289 : Blo 944585 1065289 := bbase (se 2 (by rfl) ⟨399483, by rfl⟩ : syracuseStep 1065289 = 798967) (by norm_num)
theorem B1196365 : Blo 944585 1196365 := bbase (se 3 (by rfl) ⟨224318, by rfl⟩ : syracuseStep 1196365 = 448637) (by norm_num)
theorem B4800869 : Blo 944585 4800869 := bbase (se 4 (by rfl) ⟨450081, by rfl⟩ : syracuseStep 4800869 = 900163) (by norm_num)
theorem B1065325 : Blo 944585 1065325 := bbase (se 3 (by rfl) ⟨199748, by rfl⟩ : syracuseStep 1065325 = 399497) (by norm_num)
theorem B1065361 : Blo 944585 1065361 := bbase (se 2 (by rfl) ⟨399510, by rfl⟩ : syracuseStep 1065361 = 799021) (by norm_num)
theorem B1196461 : Blo 944585 1196461 := bbase (se 3 (by rfl) ⟨224336, by rfl⟩ : syracuseStep 1196461 = 448673) (by norm_num)
theorem B3588533 : Blo 944585 3588533 := bbase (se 5 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 3588533 = 336425) (by norm_num)
theorem B1065397 : Blo 944585 1065397 := bbase (se 5 (by rfl) ⟨49940, by rfl⟩ : syracuseStep 1065397 = 99881) (by norm_num)
theorem B4047317 : Blo 944585 4047317 := bbase (se 7 (by rfl) ⟨47429, by rfl⟩ : syracuseStep 4047317 = 94859) (by norm_num)
theorem B1065433 : Blo 944585 1065433 := bbase (se 2 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 1065433 = 799075) (by norm_num)
theorem B1065469 : Blo 944585 1065469 := bbase (se 3 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 1065469 = 399551) (by norm_num)
theorem B1065505 : Blo 944585 1065505 := bbase (se 2 (by rfl) ⟨399564, by rfl⟩ : syracuseStep 1065505 = 799129) (by norm_num)
theorem B1065541 : Blo 944585 1065541 := bbase (se 4 (by rfl) ⟨99894, by rfl⟩ : syracuseStep 1065541 = 199789) (by norm_num)
theorem B1229401 : Blo 944585 1229401 := bbase (se 2 (by rfl) ⟨461025, by rfl⟩ : syracuseStep 1229401 = 922051) (by norm_num)
theorem B1196633 : Blo 944585 1196633 := bbase (se 2 (by rfl) ⟨448737, by rfl⟩ : syracuseStep 1196633 = 897475) (by norm_num)
theorem B1065577 : Blo 944585 1065577 := bbase (se 2 (by rfl) ⟨399591, by rfl⟩ : syracuseStep 1065577 = 799183) (by norm_num)
theorem B1065613 : Blo 944585 1065613 := bbase (se 3 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 1065613 = 399605) (by norm_num)
theorem B1196689 : Blo 944585 1196689 := bbase (se 2 (by rfl) ⟨448758, by rfl⟩ : syracuseStep 1196689 = 897517) (by norm_num)
theorem B3195557 : Blo 944585 3195557 := bbase (se 4 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 3195557 = 599167) (by norm_num)
theorem B1065649 : Blo 944585 1065649 := bbase (se 2 (by rfl) ⟨399618, by rfl⟩ : syracuseStep 1065649 = 799237) (by norm_num)
theorem B1065685 : Blo 944585 1065685 := bbase (se 7 (by rfl) ⟨12488, by rfl⟩ : syracuseStep 1065685 = 24977) (by norm_num)
theorem B1196785 : Blo 944585 1196785 := bbase (se 2 (by rfl) ⟨448794, by rfl⟩ : syracuseStep 1196785 = 897589) (by norm_num)
theorem B1065721 : Blo 944585 1065721 := bbase (se 2 (by rfl) ⟨399645, by rfl⟩ : syracuseStep 1065721 = 799291) (by norm_num)
theorem B1065757 : Blo 944585 1065757 := bbase (se 3 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 1065757 = 399659) (by norm_num)
theorem B1065793 : Blo 944585 1065793 := bbase (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) (by norm_num)
theorem B1065829 : Blo 944585 1065829 := bbase (se 4 (by rfl) ⟨99921, by rfl⟩ : syracuseStep 1065829 = 199843) (by norm_num)
theorem B1065865 : Blo 944585 1065865 := bbase (se 2 (by rfl) ⟨399699, by rfl⟩ : syracuseStep 1065865 = 799399) (by norm_num)
theorem B14599061 : Blo 944585 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B1196957 : Blo 944585 1196957 := bbase (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) (by norm_num)
theorem B1065901 : Blo 944585 1065901 := bbase (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) (by norm_num)
theorem B1065937 : Blo 944585 1065937 := bbase (se 2 (by rfl) ⟨399726, by rfl⟩ : syracuseStep 1065937 = 799453) (by norm_num)
theorem B1197013 : Blo 944585 1197013 := bbase (se 7 (by rfl) ⟨14027, by rfl⟩ : syracuseStep 1197013 = 28055) (by norm_num)
theorem B1065973 : Blo 944585 1065973 := bbase (se 5 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 1065973 = 99935) (by norm_num)
theorem B1066009 : Blo 944585 1066009 := bbase (se 2 (by rfl) ⟨399753, by rfl⟩ : syracuseStep 1066009 = 799507) (by norm_num)
theorem B1197109 : Blo 944585 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B1066045 : Blo 944585 1066045 := bbase (se 3 (by rfl) ⟨199883, by rfl⟩ : syracuseStep 1066045 = 399767) (by norm_num)
theorem B3195989 : Blo 944585 3195989 := bbase (se 8 (by rfl) ⟨18726, by rfl⟩ : syracuseStep 3195989 = 37453) (by norm_num)
theorem B1066081 : Blo 944585 1066081 := bbase (se 2 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 1066081 = 799561) (by norm_num)
theorem B1066117 : Blo 944585 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B1066153 : Blo 944585 1066153 := bbase (se 2 (by rfl) ⟨399807, by rfl⟩ : syracuseStep 1066153 = 799615) (by norm_num)
theorem B3884213 : Blo 944585 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B4048069 : Blo 944585 4048069 := bbase (se 4 (by rfl) ⟨379506, by rfl⟩ : syracuseStep 4048069 = 759013) (by norm_num)
theorem B1066189 : Blo 944585 1066189 := bbase (se 3 (by rfl) ⟨199910, by rfl⟩ : syracuseStep 1066189 = 399821) (by norm_num)
theorem B1197281 : Blo 944585 1197281 := bbase (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) (by norm_num)
theorem B1557733 : Blo 944585 1557733 := bbase (se 4 (by rfl) ⟨146037, by rfl⟩ : syracuseStep 1557733 = 292075) (by norm_num)
theorem B1066225 : Blo 944585 1066225 := bbase (se 2 (by rfl) ⟨399834, by rfl⟩ : syracuseStep 1066225 = 799669) (by norm_num)
theorem B1066261 : Blo 944585 1066261 := bbase (se 6 (by rfl) ⟨24990, by rfl⟩ : syracuseStep 1066261 = 49981) (by norm_num)
theorem B1197337 : Blo 944585 1197337 := bbase (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) (by norm_num)
theorem B1066297 : Blo 944585 1066297 := bbase (se 2 (by rfl) ⟨399861, by rfl⟩ : syracuseStep 1066297 = 799723) (by norm_num)
theorem B1066333 : Blo 944585 1066333 := bbase (se 3 (by rfl) ⟨199937, by rfl⟩ : syracuseStep 1066333 = 399875) (by norm_num)
theorem B1197433 : Blo 944585 1197433 := bbase (se 2 (by rfl) ⟨449037, by rfl⟩ : syracuseStep 1197433 = 898075) (by norm_num)
theorem B1066369 : Blo 944585 1066369 := bbase (se 2 (by rfl) ⟨399888, by rfl⟩ : syracuseStep 1066369 = 799777) (by norm_num)
theorem B1066405 : Blo 944585 1066405 := bbase (se 4 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 1066405 = 199951) (by norm_num)
theorem B1066441 : Blo 944585 1066441 := bbase (se 2 (by rfl) ⟨399915, by rfl⟩ : syracuseStep 1066441 = 799831) (by norm_num)
theorem B1066477 : Blo 944585 1066477 := bbase (se 3 (by rfl) ⟨199964, by rfl⟩ : syracuseStep 1066477 = 399929) (by norm_num)
theorem B3196421 : Blo 944585 3196421 := bbase (se 4 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 3196421 = 599329) (by norm_num)
theorem B1066513 : Blo 944585 1066513 := bbase (se 2 (by rfl) ⟨399942, by rfl⟩ : syracuseStep 1066513 = 799885) (by norm_num)
theorem B1197605 : Blo 944585 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1066549 : Blo 944585 1066549 := bbase (se 5 (by rfl) ⟨49994, by rfl⟩ : syracuseStep 1066549 = 99989) (by norm_num)
theorem B3589717 : Blo 944585 3589717 := bbase (se 8 (by rfl) ⟨21033, by rfl⟩ : syracuseStep 3589717 = 42067) (by norm_num)
theorem B1066585 : Blo 944585 1066585 := bbase (se 2 (by rfl) ⟨399969, by rfl⟩ : syracuseStep 1066585 = 799939) (by norm_num)
theorem B1197661 : Blo 944585 1197661 := bbase (se 3 (by rfl) ⟨224561, by rfl⟩ : syracuseStep 1197661 = 449123) (by norm_num)
theorem B4802165 : Blo 944585 4802165 := bbase (se 5 (by rfl) ⟨225101, by rfl⟩ : syracuseStep 4802165 = 450203) (by norm_num)
theorem B1066621 : Blo 944585 1066621 := bbase (se 3 (by rfl) ⟨199991, by rfl⟩ : syracuseStep 1066621 = 399983) (by norm_num)
theorem B1066657 : Blo 944585 1066657 := bbase (se 2 (by rfl) ⟨399996, by rfl⟩ : syracuseStep 1066657 = 799993) (by norm_num)
theorem B1197757 : Blo 944585 1197757 := bbase (se 3 (by rfl) ⟨224579, by rfl⟩ : syracuseStep 1197757 = 449159) (by norm_num)
theorem B1066693 : Blo 944585 1066693 := bbase (se 4 (by rfl) ⟨100002, by rfl⟩ : syracuseStep 1066693 = 200005) (by norm_num)
theorem B1066729 : Blo 944585 1066729 := bbase (se 2 (by rfl) ⟨400023, by rfl⟩ : syracuseStep 1066729 = 800047) (by norm_num)
theorem B2279173 : Blo 944585 2279173 := bbase (se 4 (by rfl) ⟨213672, by rfl⟩ : syracuseStep 2279173 = 427345) (by norm_num)
theorem B1066765 : Blo 944585 1066765 := bbase (se 3 (by rfl) ⟨200018, by rfl⟩ : syracuseStep 1066765 = 400037) (by norm_num)
theorem B1066801 : Blo 944585 1066801 := bbase (se 2 (by rfl) ⟨400050, by rfl⟩ : syracuseStep 1066801 = 800101) (by norm_num)
theorem B1066837 : Blo 944585 1066837 := bbase (se 9 (by rfl) ⟨3125, by rfl⟩ : syracuseStep 1066837 = 6251) (by norm_num)
theorem B1197929 : Blo 944585 1197929 := bbase (se 2 (by rfl) ⟨449223, by rfl⟩ : syracuseStep 1197929 = 898447) (by norm_num)
theorem B1066873 : Blo 944585 1066873 := bbase (se 2 (by rfl) ⟨400077, by rfl⟩ : syracuseStep 1066873 = 800155) (by norm_num)
theorem B3590021 : Blo 944585 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B5392277 : Blo 944585 5392277 := bbase (se 6 (by rfl) ⟨126381, by rfl⟩ : syracuseStep 5392277 = 252763) (by norm_num)
theorem B1066909 : Blo 944585 1066909 := bbase (se 3 (by rfl) ⟨200045, by rfl⟩ : syracuseStep 1066909 = 400091) (by norm_num)
theorem B1197985 : Blo 944585 1197985 := bbase (se 2 (by rfl) ⟨449244, by rfl⟩ : syracuseStep 1197985 = 898489) (by norm_num)
theorem B4048805 : Blo 944585 4048805 := bbase (se 4 (by rfl) ⟨379575, by rfl⟩ : syracuseStep 4048805 = 759151) (by norm_num)
theorem B3196853 : Blo 944585 3196853 := bbase (se 5 (by rfl) ⟨149852, by rfl⟩ : syracuseStep 3196853 = 299705) (by norm_num)
theorem B1066945 : Blo 944585 1066945 := bbase (se 2 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 1066945 = 800209) (by norm_num)
theorem B1558493 : Blo 944585 1558493 := bbase (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) (by norm_num)
theorem B1066981 : Blo 944585 1066981 := bbase (se 4 (by rfl) ⟨100029, by rfl⟩ : syracuseStep 1066981 = 200059) (by norm_num)
theorem B1198081 : Blo 944585 1198081 := bbase (se 2 (by rfl) ⟨449280, by rfl⟩ : syracuseStep 1198081 = 898561) (by norm_num)
theorem B1067017 : Blo 944585 1067017 := bbase (se 2 (by rfl) ⟨400131, by rfl⟩ : syracuseStep 1067017 = 800263) (by norm_num)
theorem B1067053 : Blo 944585 1067053 := bbase (se 3 (by rfl) ⟨200072, by rfl⟩ : syracuseStep 1067053 = 400145) (by norm_num)
theorem B1067089 : Blo 944585 1067089 := bbase (se 2 (by rfl) ⟨400158, by rfl⟩ : syracuseStep 1067089 = 800317) (by norm_num)
theorem B7784533 : Blo 944585 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B6834293 : Blo 944585 6834293 := bbase (se 5 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 6834293 = 640715) (by norm_num)
theorem B1067125 : Blo 944585 1067125 := bbase (se 5 (by rfl) ⟨50021, by rfl⟩ : syracuseStep 1067125 = 100043) (by norm_num)
theorem B1198253 : Blo 944585 1198253 := bbase (se 3 (by rfl) ⟨224672, by rfl⟩ : syracuseStep 1198253 = 449345) (by norm_num)
theorem B1198309 : Blo 944585 1198309 := bbase (se 4 (by rfl) ⟨112341, by rfl⟩ : syracuseStep 1198309 = 224683) (by norm_num)
theorem B1198405 : Blo 944585 1198405 := bbase (se 4 (by rfl) ⟨112350, by rfl⟩ : syracuseStep 1198405 = 224701) (by norm_num)
theorem B3197285 : Blo 944585 3197285 := bbase (se 4 (by rfl) ⟨299745, by rfl⟩ : syracuseStep 3197285 = 599491) (by norm_num)
theorem B1198577 : Blo 944585 1198577 := bbase (se 2 (by rfl) ⟨449466, by rfl⟩ : syracuseStep 1198577 = 898933) (by norm_num)
theorem B1198633 : Blo 944585 1198633 := bbase (se 2 (by rfl) ⟨449487, by rfl⟩ : syracuseStep 1198633 = 898975) (by norm_num)
theorem B1919533 : Blo 944585 1919533 := bbase (se 3 (by rfl) ⟨359912, by rfl⟩ : syracuseStep 1919533 = 719825) (by norm_num)
theorem B1198729 : Blo 944585 1198729 := bbase (se 2 (by rfl) ⟨449523, by rfl⟩ : syracuseStep 1198729 = 899047) (by norm_num)
theorem B3197717 : Blo 944585 3197717 := bbase (se 6 (by rfl) ⟨74946, by rfl⟩ : syracuseStep 3197717 = 149893) (by norm_num)
theorem B1198901 : Blo 944585 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B1231697 : Blo 944585 1231697 := bbase (se 2 (by rfl) ⟨461886, by rfl⟩ : syracuseStep 1231697 = 923773) (by norm_num)
theorem B1198957 : Blo 944585 1198957 := bbase (se 3 (by rfl) ⟨224804, by rfl⟩ : syracuseStep 1198957 = 449609) (by norm_num)
theorem B1199053 : Blo 944585 1199053 := bbase (se 3 (by rfl) ⟨224822, by rfl⟩ : syracuseStep 1199053 = 449645) (by norm_num)
theorem B12471317 : Blo 944585 12471317 := bbase (se 6 (by rfl) ⟨292296, by rfl⟩ : syracuseStep 12471317 = 584593) (by norm_num)
theorem B1199225 : Blo 944585 1199225 := bbase (se 2 (by rfl) ⟨449709, by rfl⟩ : syracuseStep 1199225 = 899419) (by norm_num)
theorem B1199281 : Blo 944585 1199281 := bbase (se 2 (by rfl) ⟨449730, by rfl⟩ : syracuseStep 1199281 = 899461) (by norm_num)
theorem B3198149 : Blo 944585 3198149 := bbase (se 4 (by rfl) ⟨299826, by rfl⟩ : syracuseStep 3198149 = 599653) (by norm_num)
theorem B2018533 : Blo 944585 2018533 := bbase (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) (by norm_num)
theorem B1199377 : Blo 944585 1199377 := bbase (se 2 (by rfl) ⟨449766, by rfl⟩ : syracuseStep 1199377 = 899533) (by norm_num)
theorem B1199549 : Blo 944585 1199549 := bbase (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) (by norm_num)
theorem B1199605 : Blo 944585 1199605 := bbase (se 5 (by rfl) ⟨56231, by rfl⟩ : syracuseStep 1199605 = 112463) (by norm_num)
theorem B1297949 : Blo 944585 1297949 := bbase (se 3 (by rfl) ⟨243365, by rfl⟩ : syracuseStep 1297949 = 486731) (by norm_num)
theorem B4541989 : Blo 944585 4541989 := bbase (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) (by norm_num)
theorem B1199701 : Blo 944585 1199701 := bbase (se 8 (by rfl) ⟨7029, by rfl⟩ : syracuseStep 1199701 = 14059) (by norm_num)
theorem B3198581 : Blo 944585 3198581 := bbase (se 5 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 3198581 = 299867) (by norm_num)
theorem B1199873 : Blo 944585 1199873 := bbase (se 2 (by rfl) ⟨449952, by rfl⟩ : syracuseStep 1199873 = 899905) (by norm_num)
theorem B1199929 : Blo 944585 1199929 := bbase (se 2 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 1199929 = 899947) (by norm_num)
theorem B1232705 : Blo 944585 1232705 := bbase (se 2 (by rfl) ⟨462264, by rfl⟩ : syracuseStep 1232705 = 924529) (by norm_num)
theorem B1200025 : Blo 944585 1200025 := bbase (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) (by norm_num)
theorem B3592133 : Blo 944585 3592133 := bbase (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) (by norm_num)
theorem B3199013 : Blo 944585 3199013 := bbase (se 4 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 3199013 = 599815) (by norm_num)
theorem B1200197 : Blo 944585 1200197 := bbase (se 4 (by rfl) ⟨112518, by rfl⟩ : syracuseStep 1200197 = 225037) (by norm_num)
theorem B2019421 : Blo 944585 2019421 := bbase (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) (by norm_num)
theorem B1200253 : Blo 944585 1200253 := bbase (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) (by norm_num)
theorem B1200349 : Blo 944585 1200349 := bbase (se 3 (by rfl) ⟨225065, by rfl⟩ : syracuseStep 1200349 = 450131) (by norm_num)
theorem B3592421 : Blo 944585 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B1134829 : Blo 944585 1134829 := bbase (se 3 (by rfl) ⟨212780, by rfl⟩ : syracuseStep 1134829 = 425561) (by norm_num)
theorem B1200521 : Blo 944585 1200521 := bbase (se 2 (by rfl) ⟨450195, by rfl⟩ : syracuseStep 1200521 = 900391) (by norm_num)
theorem B3199445 : Blo 944585 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B7197173 : Blo 944585 7197173 := bbase (se 5 (by rfl) ⟨337367, by rfl⟩ : syracuseStep 7197173 = 674735) (by norm_num)
theorem B1364557 : Blo 944585 1364557 := bbase (se 3 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 1364557 = 511709) (by norm_num)
theorem B2019917 : Blo 944585 2019917 := bbase (se 3 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 2019917 = 757469) (by norm_num)
theorem B3232453 : Blo 944585 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B1594093 : Blo 944585 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1594181 : Blo 944585 1594181 := bbase (se 4 (by rfl) ⟨149454, by rfl⟩ : syracuseStep 1594181 = 298909) (by norm_num)
theorem B3199877 : Blo 944585 3199877 := bbase (se 4 (by rfl) ⟨299988, by rfl⟩ : syracuseStep 3199877 = 599977) (by norm_num)
theorem B1823629 : Blo 944585 1823629 := bbase (se 3 (by rfl) ⟨341930, by rfl⟩ : syracuseStep 1823629 = 683861) (by norm_num)
theorem B1299341 : Blo 944585 1299341 := bbase (se 3 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 1299341 = 487253) (by norm_num)
theorem B1594309 : Blo 944585 1594309 := bbase (se 4 (by rfl) ⟨149466, by rfl⟩ : syracuseStep 1594309 = 298933) (by norm_num)
theorem B1594397 : Blo 944585 1594397 := bbase (se 3 (by rfl) ⟨298949, by rfl⟩ : syracuseStep 1594397 = 597899) (by norm_num)
theorem B1594525 : Blo 944585 1594525 := bbase (se 3 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 1594525 = 597947) (by norm_num)
theorem B1135829 : Blo 944585 1135829 := bbase (se 7 (by rfl) ⟨13310, by rfl⟩ : syracuseStep 1135829 = 26621) (by norm_num)
theorem B1594613 : Blo 944585 1594613 := bbase (se 5 (by rfl) ⟨74747, by rfl⟩ : syracuseStep 1594613 = 149495) (by norm_num)
theorem B3036437 : Blo 944585 3036437 := bbase (se 6 (by rfl) ⟨71166, by rfl⟩ : syracuseStep 3036437 = 142333) (by norm_num)
theorem B3200309 : Blo 944585 3200309 := bbase (se 5 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 3200309 = 300029) (by norm_num)
theorem B1594741 : Blo 944585 1594741 := bbase (se 5 (by rfl) ⟨74753, by rfl⟩ : syracuseStep 1594741 = 149507) (by norm_num)
theorem B3593605 : Blo 944585 3593605 := bbase (se 4 (by rfl) ⟨336900, by rfl⟩ : syracuseStep 3593605 = 673801) (by norm_num)
theorem B2020781 : Blo 944585 2020781 := bbase (se 3 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 2020781 = 757793) (by norm_num)
theorem B1594829 : Blo 944585 1594829 := bbase (se 3 (by rfl) ⟨299030, by rfl⟩ : syracuseStep 1594829 = 598061) (by norm_num)
theorem B1136117 : Blo 944585 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B2020925 : Blo 944585 2020925 := bbase (se 3 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 2020925 = 757847) (by norm_num)
theorem B1594957 : Blo 944585 1594957 := bbase (se 3 (by rfl) ⟨299054, by rfl⟩ : syracuseStep 1594957 = 598109) (by norm_num)
theorem B1136281 : Blo 944585 1136281 := bbase (se 2 (by rfl) ⟨426105, by rfl⟩ : syracuseStep 1136281 = 852211) (by norm_num)
theorem B1595045 : Blo 944585 1595045 := bbase (se 4 (by rfl) ⟨149535, by rfl⟩ : syracuseStep 1595045 = 299071) (by norm_num)
theorem B1136309 : Blo 944585 1136309 := bbase (se 5 (by rfl) ⟨53264, by rfl⟩ : syracuseStep 1136309 = 106529) (by norm_num)
theorem B3593909 : Blo 944585 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B3200741 : Blo 944585 3200741 := bbase (se 4 (by rfl) ⟨300069, by rfl⟩ : syracuseStep 3200741 = 600139) (by norm_num)
theorem B1595173 : Blo 944585 1595173 := bbase (se 4 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 1595173 = 299095) (by norm_num)
theorem B1136425 : Blo 944585 1136425 := bbase (se 2 (by rfl) ⟨426159, by rfl⟩ : syracuseStep 1136425 = 852319) (by norm_num)
theorem B1595261 : Blo 944585 1595261 := bbase (se 3 (by rfl) ⟨299111, by rfl⟩ : syracuseStep 1595261 = 598223) (by norm_num)
theorem B1136521 : Blo 944585 1136521 := bbase (se 2 (by rfl) ⟨426195, by rfl⟩ : syracuseStep 1136521 = 852391) (by norm_num)
theorem B1595389 : Blo 944585 1595389 := bbase (se 3 (by rfl) ⟨299135, by rfl⟩ : syracuseStep 1595389 = 598271) (by norm_num)
theorem B18176021 : Blo 944585 18176021 := bbase (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) (by norm_num)
theorem B1595477 : Blo 944585 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B3037333 : Blo 944585 3037333 := bbase (se 6 (by rfl) ⟨71187, by rfl⟩ : syracuseStep 3037333 = 142375) (by norm_num)
theorem B3201173 : Blo 944585 3201173 := bbase (se 6 (by rfl) ⟨75027, by rfl⟩ : syracuseStep 3201173 = 150055) (by norm_num)
theorem B1595605 : Blo 944585 1595605 := bbase (se 7 (by rfl) ⟨18698, by rfl⟩ : syracuseStep 1595605 = 37397) (by norm_num)
theorem B2021669 : Blo 944585 2021669 := bbase (se 4 (by rfl) ⟨189531, by rfl⟩ : syracuseStep 2021669 = 379063) (by norm_num)
theorem B1595693 : Blo 944585 1595693 := bbase (se 3 (by rfl) ⟨299192, by rfl⟩ : syracuseStep 1595693 = 598385) (by norm_num)
theorem B1137001 : Blo 944585 1137001 := bbase (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) (by norm_num)
theorem B1595821 : Blo 944585 1595821 := bbase (se 3 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 1595821 = 598433) (by norm_num)
theorem B1595909 : Blo 944585 1595909 := bbase (se 4 (by rfl) ⟨149616, by rfl⟩ : syracuseStep 1595909 = 299233) (by norm_num)
theorem B3037733 : Blo 944585 3037733 := bbase (se 4 (by rfl) ⟨284787, by rfl⟩ : syracuseStep 3037733 = 569575) (by norm_num)
theorem B1366589 : Blo 944585 1366589 := bbase (se 3 (by rfl) ⟨256235, by rfl⟩ : syracuseStep 1366589 = 512471) (by norm_num)
theorem B2808389 : Blo 944585 2808389 := bbase (se 4 (by rfl) ⟨263286, by rfl⟩ : syracuseStep 2808389 = 526573) (by norm_num)
theorem B1596037 : Blo 944585 1596037 := bbase (se 4 (by rfl) ⟨149628, by rfl⟩ : syracuseStep 1596037 = 299257) (by norm_num)
theorem B1596125 : Blo 944585 1596125 := bbase (se 3 (by rfl) ⟨299273, by rfl⟩ : syracuseStep 1596125 = 598547) (by norm_num)
theorem B8084245 : Blo 944585 8084245 := bbase (se 6 (by rfl) ⟨189474, by rfl⟩ : syracuseStep 8084245 = 378949) (by norm_num)
theorem B1596253 : Blo 944585 1596253 := bbase (se 3 (by rfl) ⟨299297, by rfl⟩ : syracuseStep 1596253 = 598595) (by norm_num)
theorem B1596341 : Blo 944585 1596341 := bbase (se 5 (by rfl) ⟨74828, by rfl⟩ : syracuseStep 1596341 = 149657) (by norm_num)
theorem B2022421 : Blo 944585 2022421 := bbase (se 6 (by rfl) ⟨47400, by rfl⟩ : syracuseStep 2022421 = 94801) (by norm_num)
theorem B1596469 : Blo 944585 1596469 := bbase (se 5 (by rfl) ⟨74834, by rfl⟩ : syracuseStep 1596469 = 149669) (by norm_num)
theorem B1596557 : Blo 944585 1596557 := bbase (se 3 (by rfl) ⟨299354, by rfl⟩ : syracuseStep 1596557 = 598709) (by norm_num)
theorem B2022565 : Blo 944585 2022565 := bbase (se 4 (by rfl) ⟨189615, by rfl⟩ : syracuseStep 2022565 = 379231) (by norm_num)
theorem B1596685 : Blo 944585 1596685 := bbase (se 3 (by rfl) ⟨299378, by rfl⟩ : syracuseStep 1596685 = 598757) (by norm_num)
theorem B1793333 : Blo 944585 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B1596773 : Blo 944585 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B1793477 : Blo 944585 1793477 := bbase (se 4 (by rfl) ⟨168138, by rfl⟩ : syracuseStep 1793477 = 336277) (by norm_num)
theorem B4545989 : Blo 944585 4545989 := bbase (se 4 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 4545989 = 852373) (by norm_num)
theorem B1596901 : Blo 944585 1596901 := bbase (se 4 (by rfl) ⟨149709, by rfl⟩ : syracuseStep 1596901 = 299419) (by norm_num)
theorem B2022941 : Blo 944585 2022941 := bbase (se 3 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 2022941 = 758603) (by norm_num)
theorem B1596989 : Blo 944585 1596989 := bbase (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) (by norm_num)
theorem B6053525 : Blo 944585 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B1597117 : Blo 944585 1597117 := bbase (se 3 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 1597117 = 598919) (by norm_num)
theorem B1138385 : Blo 944585 1138385 := bbase (se 2 (by rfl) ⟨426894, by rfl⟩ : syracuseStep 1138385 = 853789) (by norm_num)
theorem B1793765 : Blo 944585 1793765 := bbase (se 4 (by rfl) ⟨168165, by rfl⟩ : syracuseStep 1793765 = 336331) (by norm_num)
theorem B3596021 : Blo 944585 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B1597205 : Blo 944585 1597205 := bbase (se 6 (by rfl) ⟨37434, by rfl⟩ : syracuseStep 1597205 = 74869) (by norm_num)
theorem B1793917 : Blo 944585 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B2023309 : Blo 944585 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B1138573 : Blo 944585 1138573 := bbase (se 3 (by rfl) ⟨213482, by rfl⟩ : syracuseStep 1138573 = 426965) (by norm_num)
theorem B1597333 : Blo 944585 1597333 := bbase (se 6 (by rfl) ⟨37437, by rfl⟩ : syracuseStep 1597333 = 74875) (by norm_num)
theorem B1597421 : Blo 944585 1597421 := bbase (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) (by norm_num)
theorem B3596309 : Blo 944585 3596309 := bbase (se 6 (by rfl) ⟨84288, by rfl⟩ : syracuseStep 3596309 = 168577) (by norm_num)
theorem B1138789 : Blo 944585 1138789 := bbase (se 4 (by rfl) ⟨106761, by rfl⟩ : syracuseStep 1138789 = 213523) (by norm_num)
theorem B1597549 : Blo 944585 1597549 := bbase (se 3 (by rfl) ⟨299540, by rfl⟩ : syracuseStep 1597549 = 599081) (by norm_num)
theorem B1794221 : Blo 944585 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B1597637 : Blo 944585 1597637 := bbase (se 4 (by rfl) ⟨149778, by rfl⟩ : syracuseStep 1597637 = 299557) (by norm_num)
theorem B1597765 : Blo 944585 1597765 := bbase (se 4 (by rfl) ⟨149790, by rfl⟩ : syracuseStep 1597765 = 299581) (by norm_num)
theorem B1139077 : Blo 944585 1139077 := bbase (se 4 (by rfl) ⟨106788, by rfl⟩ : syracuseStep 1139077 = 213577) (by norm_num)
theorem B1597853 : Blo 944585 1597853 := bbase (se 3 (by rfl) ⟨299597, by rfl⟩ : syracuseStep 1597853 = 599195) (by norm_num)
theorem B1597981 : Blo 944585 1597981 := bbase (se 3 (by rfl) ⟨299621, by rfl⟩ : syracuseStep 1597981 = 599243) (by norm_num)
theorem B1598069 : Blo 944585 1598069 := bbase (se 5 (by rfl) ⟨74909, by rfl⟩ : syracuseStep 1598069 = 149819) (by norm_num)
theorem B8086229 : Blo 944585 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1598197 : Blo 944585 1598197 := bbase (se 5 (by rfl) ⟨74915, by rfl⟩ : syracuseStep 1598197 = 149831) (by norm_num)
theorem B2155261 : Blo 944585 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B1598285 : Blo 944585 1598285 := bbase (se 3 (by rfl) ⟨299678, by rfl⟩ : syracuseStep 1598285 = 599357) (by norm_num)
theorem B1794973 : Blo 944585 1794973 := bbase (se 3 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 1794973 = 673115) (by norm_num)
theorem B1598413 : Blo 944585 1598413 := bbase (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) (by norm_num)
theorem B1598501 : Blo 944585 1598501 := bbase (se 4 (by rfl) ⟨149859, by rfl⟩ : syracuseStep 1598501 = 299719) (by norm_num)
theorem B1795117 : Blo 944585 1795117 := bbase (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) (by norm_num)
theorem B1598629 : Blo 944585 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B3597493 : Blo 944585 3597493 := bbase (se 5 (by rfl) ⟨168632, by rfl⟩ : syracuseStep 3597493 = 337265) (by norm_num)
theorem B1795277 : Blo 944585 1795277 := bbase (se 3 (by rfl) ⟨336614, by rfl⟩ : syracuseStep 1795277 = 673229) (by norm_num)
theorem B1008865 : Blo 944585 1008865 := bbase (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) (by norm_num)
theorem B1598717 : Blo 944585 1598717 := bbase (se 3 (by rfl) ⟨299759, by rfl⟩ : syracuseStep 1598717 = 599519) (by norm_num)
theorem B1795421 : Blo 944585 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B2024813 : Blo 944585 2024813 := bbase (se 3 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 2024813 = 759305) (by norm_num)
theorem B1598845 : Blo 944585 1598845 := bbase (se 3 (by rfl) ⟨299783, by rfl⟩ : syracuseStep 1598845 = 599567) (by norm_num)
theorem B9102773 : Blo 944585 9102773 := bbase (se 5 (by rfl) ⟨426692, by rfl⟩ : syracuseStep 9102773 = 853385) (by norm_num)
theorem B1598933 : Blo 944585 1598933 := bbase (se 7 (by rfl) ⟨18737, by rfl⟩ : syracuseStep 1598933 = 37475) (by norm_num)
theorem B3597797 : Blo 944585 3597797 := bbase (se 4 (by rfl) ⟨337293, by rfl⟩ : syracuseStep 3597797 = 674587) (by norm_num)
theorem B2024957 : Blo 944585 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B3237461 : Blo 944585 3237461 := bbase (se 8 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 3237461 = 37939) (by norm_num)
theorem B1599061 : Blo 944585 1599061 := bbase (se 8 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 1599061 = 18739) (by norm_num)
theorem B1795709 : Blo 944585 1795709 := bbase (se 3 (by rfl) ⟨336695, by rfl⟩ : syracuseStep 1795709 = 673391) (by norm_num)
theorem B1009297 : Blo 944585 1009297 := bbase (se 2 (by rfl) ⟨378486, by rfl⟩ : syracuseStep 1009297 = 756973) (by norm_num)
theorem B1599149 : Blo 944585 1599149 := bbase (se 3 (by rfl) ⟨299840, by rfl⟩ : syracuseStep 1599149 = 599681) (by norm_num)
theorem B4318933 : Blo 944585 4318933 := bbase (se 7 (by rfl) ⟨50612, by rfl⟩ : syracuseStep 4318933 = 101225) (by norm_num)
theorem B1009369 : Blo 944585 1009369 := bbase (se 2 (by rfl) ⟨378513, by rfl⟩ : syracuseStep 1009369 = 757027) (by norm_num)
theorem B1795861 : Blo 944585 1795861 := bbase (se 6 (by rfl) ⟨42090, by rfl⟩ : syracuseStep 1795861 = 84181) (by norm_num)
theorem B5400341 : Blo 944585 5400341 := bbase (se 6 (by rfl) ⟨126570, by rfl⟩ : syracuseStep 5400341 = 253141) (by norm_num)
theorem B1599277 : Blo 944585 1599277 := bbase (se 3 (by rfl) ⟨299864, by rfl⟩ : syracuseStep 1599277 = 599729) (by norm_num)
theorem B2025317 : Blo 944585 2025317 := bbase (se 4 (by rfl) ⟨189873, by rfl⟩ : syracuseStep 2025317 = 379747) (by norm_num)
theorem B1599365 : Blo 944585 1599365 := bbase (se 4 (by rfl) ⟨149940, by rfl⟩ : syracuseStep 1599365 = 299881) (by norm_num)
theorem B1599493 : Blo 944585 1599493 := bbase (se 4 (by rfl) ⟨149952, by rfl⟩ : syracuseStep 1599493 = 299905) (by norm_num)
theorem B2156557 : Blo 944585 2156557 := bbase (se 3 (by rfl) ⟨404354, by rfl⟩ : syracuseStep 2156557 = 808709) (by norm_num)
theorem B1796165 : Blo 944585 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1009741 : Blo 944585 1009741 := bbase (se 3 (by rfl) ⟨189326, by rfl⟩ : syracuseStep 1009741 = 378653) (by norm_num)
theorem B1599581 : Blo 944585 1599581 := bbase (se 3 (by rfl) ⟨299921, by rfl⟩ : syracuseStep 1599581 = 599843) (by norm_num)
theorem B4548773 : Blo 944585 4548773 := bbase (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) (by norm_num)
theorem B1599709 : Blo 944585 1599709 := bbase (se 3 (by rfl) ⟨299945, by rfl⟩ : syracuseStep 1599709 = 599891) (by norm_num)
theorem B1599797 : Blo 944585 1599797 := bbase (se 5 (by rfl) ⟨74990, by rfl⟩ : syracuseStep 1599797 = 149981) (by norm_num)
theorem B2156885 : Blo 944585 2156885 := bbase (se 10 (by rfl) ⟨3159, by rfl⟩ : syracuseStep 2156885 = 6319) (by norm_num)
theorem B1599925 : Blo 944585 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B1010117 : Blo 944585 1010117 := bbase (se 4 (by rfl) ⟨94698, by rfl⟩ : syracuseStep 1010117 = 189397) (by norm_num)
theorem B1731053 : Blo 944585 1731053 := bbase (se 3 (by rfl) ⟨324572, by rfl⟩ : syracuseStep 1731053 = 649145) (by norm_num)
theorem B1010189 : Blo 944585 1010189 := bbase (se 3 (by rfl) ⟨189410, by rfl⟩ : syracuseStep 1010189 = 378821) (by norm_num)
theorem B1600013 : Blo 944585 1600013 := bbase (se 3 (by rfl) ⟨300002, by rfl⟩ : syracuseStep 1600013 = 600005) (by norm_num)
theorem B1436221 : Blo 944585 1436221 := bbase (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) (by norm_num)
theorem B1600141 : Blo 944585 1600141 := bbase (se 3 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 1600141 = 600053) (by norm_num)
theorem B1010377 : Blo 944585 1010377 := bbase (se 2 (by rfl) ⟨378891, by rfl⟩ : syracuseStep 1010377 = 757783) (by norm_num)
theorem B1600229 : Blo 944585 1600229 := bbase (se 4 (by rfl) ⟨150021, by rfl⟩ : syracuseStep 1600229 = 300043) (by norm_num)
theorem B1796917 : Blo 944585 1796917 := bbase (se 5 (by rfl) ⟨84230, by rfl⟩ : syracuseStep 1796917 = 168461) (by norm_num)
theorem B1600357 : Blo 944585 1600357 := bbase (se 4 (by rfl) ⟨150033, by rfl⟩ : syracuseStep 1600357 = 300067) (by norm_num)
theorem B1010561 : Blo 944585 1010561 := bbase (se 2 (by rfl) ⟨378960, by rfl⟩ : syracuseStep 1010561 = 757921) (by norm_num)
theorem B14740373 : Blo 944585 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B5401525 : Blo 944585 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B1600445 : Blo 944585 1600445 := bbase (se 3 (by rfl) ⟨300083, by rfl⟩ : syracuseStep 1600445 = 600167) (by norm_num)
theorem B1797061 : Blo 944585 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B14576597 : Blo 944585 14576597 := bbase (se 7 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 14576597 = 341639) (by norm_num)
theorem B1534997 : Blo 944585 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B1731629 : Blo 944585 1731629 := bbase (se 3 (by rfl) ⟨324680, by rfl⟩ : syracuseStep 1731629 = 649361) (by norm_num)
theorem B1436725 : Blo 944585 1436725 := bbase (se 5 (by rfl) ⟨67346, by rfl⟩ : syracuseStep 1436725 = 134693) (by norm_num)
theorem B1600573 : Blo 944585 1600573 := bbase (se 3 (by rfl) ⟨300107, by rfl⟩ : syracuseStep 1600573 = 600215) (by norm_num)
theorem B1797221 : Blo 944585 1797221 := bbase (se 4 (by rfl) ⟨168489, by rfl⟩ : syracuseStep 1797221 = 336979) (by norm_num)
theorem B1600661 : Blo 944585 1600661 := bbase (se 6 (by rfl) ⟨37515, by rfl⟩ : syracuseStep 1600661 = 75031) (by norm_num)
theorem B1797365 : Blo 944585 1797365 := bbase (se 5 (by rfl) ⟨84251, by rfl⟩ : syracuseStep 1797365 = 168503) (by norm_num)
theorem B1797653 : Blo 944585 1797653 := bbase (se 6 (by rfl) ⟨42132, by rfl⟩ : syracuseStep 1797653 = 84265) (by norm_num)
theorem B2158109 : Blo 944585 2158109 := bbase (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) (by norm_num)
theorem B2125349 : Blo 944585 2125349 := bbase (se 4 (by rfl) ⟨199251, by rfl⟩ : syracuseStep 2125349 = 398503) (by norm_num)
theorem B3599909 : Blo 944585 3599909 := bbase (se 4 (by rfl) ⟨337491, by rfl⟩ : syracuseStep 3599909 = 674983) (by norm_num)
theorem B2125421 : Blo 944585 2125421 := bbase (se 3 (by rfl) ⟨398516, by rfl⟩ : syracuseStep 2125421 = 797033) (by norm_num)
theorem B1011313 : Blo 944585 1011313 := bbase (se 2 (by rfl) ⟨379242, by rfl⟩ : syracuseStep 1011313 = 758485) (by norm_num)
theorem B1797805 : Blo 944585 1797805 := bbase (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) (by norm_num)
theorem B2125493 : Blo 944585 2125493 := bbase (se 5 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 2125493 = 199265) (by norm_num)
theorem B1011385 : Blo 944585 1011385 := bbase (se 2 (by rfl) ⟨379269, by rfl⟩ : syracuseStep 1011385 = 758539) (by norm_num)
theorem B2125565 : Blo 944585 2125565 := bbase (se 3 (by rfl) ⟨398543, by rfl⟩ : syracuseStep 2125565 = 797087) (by norm_num)
theorem B2125637 : Blo 944585 2125637 := bbase (se 4 (by rfl) ⟨199278, by rfl⟩ : syracuseStep 2125637 = 398557) (by norm_num)
theorem B3600197 : Blo 944585 3600197 := bbase (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) (by norm_num)
theorem B1011565 : Blo 944585 1011565 := bbase (se 3 (by rfl) ⟨189668, by rfl⟩ : syracuseStep 1011565 = 379337) (by norm_num)
theorem B2125709 : Blo 944585 2125709 := bbase (se 3 (by rfl) ⟨398570, by rfl⟩ : syracuseStep 2125709 = 797141) (by norm_num)
theorem B2125781 : Blo 944585 2125781 := bbase (se 7 (by rfl) ⟨24911, by rfl⟩ : syracuseStep 2125781 = 49823) (by norm_num)
theorem B1798109 : Blo 944585 1798109 := bbase (se 3 (by rfl) ⟨337145, by rfl⟩ : syracuseStep 1798109 = 674291) (by norm_num)
theorem B15331349 : Blo 944585 15331349 := bbase (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) (by norm_num)
theorem B2125853 : Blo 944585 2125853 := bbase (se 3 (by rfl) ⟨398597, by rfl⟩ : syracuseStep 2125853 = 797195) (by norm_num)
theorem B2125925 : Blo 944585 2125925 := bbase (se 4 (by rfl) ⟨199305, by rfl⟩ : syracuseStep 2125925 = 398611) (by norm_num)
theorem B2125997 : Blo 944585 2125997 := bbase (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) (by norm_num)
theorem B2126069 : Blo 944585 2126069 := bbase (se 5 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 2126069 = 199319) (by norm_num)
theorem B1012009 : Blo 944585 1012009 := bbase (se 2 (by rfl) ⟨379503, by rfl⟩ : syracuseStep 1012009 = 759007) (by norm_num)
theorem B2126141 : Blo 944585 2126141 := bbase (se 3 (by rfl) ⟨398651, by rfl⟩ : syracuseStep 2126141 = 797303) (by norm_num)
theorem B1536317 : Blo 944585 1536317 := bbase (se 3 (by rfl) ⟨288059, by rfl⟩ : syracuseStep 1536317 = 576119) (by norm_num)
theorem B1438021 : Blo 944585 1438021 := bbase (se 4 (by rfl) ⟨134814, by rfl⟩ : syracuseStep 1438021 = 269629) (by norm_num)
theorem B2879813 : Blo 944585 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B34959701 : Blo 944585 34959701 := bbase (se 10 (by rfl) ⟨51210, by rfl⟩ : syracuseStep 34959701 = 102421) (by norm_num)
theorem B1536349 : Blo 944585 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B2126213 : Blo 944585 2126213 := bbase (se 4 (by rfl) ⟨199332, by rfl⟩ : syracuseStep 2126213 = 398665) (by norm_num)
theorem B1012133 : Blo 944585 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B2126285 : Blo 944585 2126285 := bbase (se 3 (by rfl) ⟨398678, by rfl⟩ : syracuseStep 2126285 = 797357) (by norm_num)
theorem B15364565 : Blo 944585 15364565 := bbase (se 7 (by rfl) ⟨180053, by rfl⟩ : syracuseStep 15364565 = 360107) (by norm_num)
theorem B2126357 : Blo 944585 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B2126429 : Blo 944585 2126429 := bbase (se 3 (by rfl) ⟨398705, by rfl⟩ : syracuseStep 2126429 = 797411) (by norm_num)
theorem B1012385 : Blo 944585 1012385 := bbase (se 2 (by rfl) ⟨379644, by rfl⟩ : syracuseStep 1012385 = 759289) (by norm_num)
theorem B2126501 : Blo 944585 2126501 := bbase (se 4 (by rfl) ⟨199359, by rfl⟩ : syracuseStep 2126501 = 398719) (by norm_num)
theorem B1077949 : Blo 944585 1077949 := bbase (se 3 (by rfl) ⟨202115, by rfl⟩ : syracuseStep 1077949 = 404231) (by norm_num)
theorem B1798861 : Blo 944585 1798861 := bbase (se 3 (by rfl) ⟨337286, by rfl⟩ : syracuseStep 1798861 = 674573) (by norm_num)
theorem B2126573 : Blo 944585 2126573 := bbase (se 3 (by rfl) ⟨398732, by rfl⟩ : syracuseStep 2126573 = 797465) (by norm_num)
theorem B2126645 : Blo 944585 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B1799005 : Blo 944585 1799005 := bbase (se 3 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 1799005 = 674627) (by norm_num)
theorem B2126717 : Blo 944585 2126717 := bbase (se 3 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 2126717 = 797519) (by norm_num)
theorem B2126789 : Blo 944585 2126789 := bbase (se 4 (by rfl) ⟨199386, by rfl⟩ : syracuseStep 2126789 = 398773) (by norm_num)
theorem B3601381 : Blo 944585 3601381 := bbase (se 4 (by rfl) ⟨337629, by rfl⟩ : syracuseStep 3601381 = 675259) (by norm_num)
theorem B1799165 : Blo 944585 1799165 := bbase (se 3 (by rfl) ⟨337343, by rfl⟩ : syracuseStep 1799165 = 674687) (by norm_num)
theorem B2126861 : Blo 944585 2126861 := bbase (se 3 (by rfl) ⟨398786, by rfl⟩ : syracuseStep 2126861 = 797573) (by norm_num)
theorem B2126933 : Blo 944585 2126933 := bbase (se 8 (by rfl) ⟨12462, by rfl⟩ : syracuseStep 2126933 = 24925) (by norm_num)
theorem B6157397 : Blo 944585 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1012829 : Blo 944585 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B1799309 : Blo 944585 1799309 := bbase (se 3 (by rfl) ⟨337370, by rfl⟩ : syracuseStep 1799309 = 674741) (by norm_num)
theorem B2127005 : Blo 944585 2127005 := bbase (se 3 (by rfl) ⟨398813, by rfl⟩ : syracuseStep 2127005 = 797627) (by norm_num)
theorem B2127077 : Blo 944585 2127077 := bbase (se 4 (by rfl) ⟨199413, by rfl⟩ : syracuseStep 2127077 = 398827) (by norm_num)
theorem B4322597 : Blo 944585 4322597 := bbase (se 4 (by rfl) ⟨405243, by rfl⟩ : syracuseStep 4322597 = 810487) (by norm_num)
theorem B2127149 : Blo 944585 2127149 := bbase (se 3 (by rfl) ⟨398840, by rfl⟩ : syracuseStep 2127149 = 797681) (by norm_num)
theorem B2127221 : Blo 944585 2127221 := bbase (se 5 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 2127221 = 199427) (by norm_num)
theorem B1078661 : Blo 944585 1078661 := bbase (se 4 (by rfl) ⟨101124, by rfl⟩ : syracuseStep 1078661 = 202249) (by norm_num)
theorem B1799597 : Blo 944585 1799597 := bbase (se 3 (by rfl) ⟨337424, by rfl⟩ : syracuseStep 1799597 = 674849) (by norm_num)
theorem B2127293 : Blo 944585 2127293 := bbase (se 3 (by rfl) ⟨398867, by rfl⟩ : syracuseStep 2127293 = 797735) (by norm_num)
theorem B2192861 : Blo 944585 2192861 := bbase (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) (by norm_num)
theorem B2127365 : Blo 944585 2127365 := bbase (se 4 (by rfl) ⟨199440, by rfl⟩ : syracuseStep 2127365 = 398881) (by norm_num)
theorem B3241541 : Blo 944585 3241541 := bbase (se 4 (by rfl) ⟨303894, by rfl⟩ : syracuseStep 3241541 = 607789) (by norm_num)
theorem B1799749 : Blo 944585 1799749 := bbase (se 4 (by rfl) ⟨168726, by rfl⟩ : syracuseStep 1799749 = 337453) (by norm_num)
theorem B2127437 : Blo 944585 2127437 := bbase (se 3 (by rfl) ⟨398894, by rfl⟩ : syracuseStep 2127437 = 797789) (by norm_num)
theorem B5535317 : Blo 944585 5535317 := bbase (se 8 (by rfl) ⟨32433, by rfl⟩ : syracuseStep 5535317 = 64867) (by norm_num)
theorem B4552309 : Blo 944585 4552309 := bbase (se 5 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 4552309 = 426779) (by norm_num)
theorem B2127509 : Blo 944585 2127509 := bbase (se 6 (by rfl) ⟨49863, by rfl⟩ : syracuseStep 2127509 = 99727) (by norm_num)
theorem B7173845 : Blo 944585 7173845 := bbase (se 7 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 7173845 = 168137) (by norm_num)
theorem B2127581 : Blo 944585 2127581 := bbase (se 3 (by rfl) ⟨398921, by rfl⟩ : syracuseStep 2127581 = 797843) (by norm_num)
theorem B2127653 : Blo 944585 2127653 := bbase (se 4 (by rfl) ⟨199467, by rfl⟩ : syracuseStep 2127653 = 398935) (by norm_num)
theorem B1079077 : Blo 944585 1079077 := bbase (se 4 (by rfl) ⟨101163, by rfl⟩ : syracuseStep 1079077 = 202327) (by norm_num)
theorem B2127725 : Blo 944585 2127725 := bbase (se 3 (by rfl) ⟨398948, by rfl⟩ : syracuseStep 2127725 = 797897) (by norm_num)
theorem B1800053 : Blo 944585 1800053 := bbase (se 5 (by rfl) ⟨84377, by rfl⟩ : syracuseStep 1800053 = 168755) (by norm_num)
theorem B2127797 : Blo 944585 2127797 := bbase (se 5 (by rfl) ⟨99740, by rfl⟩ : syracuseStep 2127797 = 199481) (by norm_num)
theorem B1079245 : Blo 944585 1079245 := bbase (se 3 (by rfl) ⟨202358, by rfl⟩ : syracuseStep 1079245 = 404717) (by norm_num)
theorem B2127869 : Blo 944585 2127869 := bbase (se 3 (by rfl) ⟨398975, by rfl⟩ : syracuseStep 2127869 = 797951) (by norm_num)
theorem B2127941 : Blo 944585 2127941 := bbase (se 4 (by rfl) ⟨199494, by rfl⟩ : syracuseStep 2127941 = 398989) (by norm_num)
theorem B2128013 : Blo 944585 2128013 := bbase (se 3 (by rfl) ⟨399002, by rfl⟩ : syracuseStep 2128013 = 798005) (by norm_num)
theorem B2128085 : Blo 944585 2128085 := bbase (se 7 (by rfl) ⟨24938, by rfl⟩ : syracuseStep 2128085 = 49877) (by norm_num)
theorem B2128157 : Blo 944585 2128157 := bbase (se 3 (by rfl) ⟨399029, by rfl⟩ : syracuseStep 2128157 = 798059) (by norm_num)
theorem B2128229 : Blo 944585 2128229 := bbase (se 4 (by rfl) ⟨199521, by rfl⟩ : syracuseStep 2128229 = 399043) (by norm_num)
theorem B2128301 : Blo 944585 2128301 := bbase (se 3 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 2128301 = 798113) (by norm_num)
theorem B2128373 : Blo 944585 2128373 := bbase (se 5 (by rfl) ⟨99767, by rfl⟩ : syracuseStep 2128373 = 199535) (by norm_num)
theorem B2128445 : Blo 944585 2128445 := bbase (se 3 (by rfl) ⟨399083, by rfl⟩ : syracuseStep 2128445 = 798167) (by norm_num)
theorem B1800805 : Blo 944585 1800805 := bbase (se 4 (by rfl) ⟨168825, by rfl⟩ : syracuseStep 1800805 = 337651) (by norm_num)
theorem B4782725 : Blo 944585 4782725 := bbase (se 4 (by rfl) ⟨448380, by rfl⟩ : syracuseStep 4782725 = 896761) (by norm_num)
theorem B2128517 : Blo 944585 2128517 := bbase (se 4 (by rfl) ⟨199548, by rfl⟩ : syracuseStep 2128517 = 399097) (by norm_num)
theorem B2128589 : Blo 944585 2128589 := bbase (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) (by norm_num)
theorem B1440509 : Blo 944585 1440509 := bbase (se 3 (by rfl) ⟨270095, by rfl⟩ : syracuseStep 1440509 = 540191) (by norm_num)
theorem B2128661 : Blo 944585 2128661 := bbase (se 6 (by rfl) ⟨49890, by rfl⟩ : syracuseStep 2128661 = 99781) (by norm_num)
theorem B2128733 : Blo 944585 2128733 := bbase (se 3 (by rfl) ⟨399137, by rfl⟩ : syracuseStep 2128733 = 798275) (by norm_num)
theorem B2128805 : Blo 944585 2128805 := bbase (se 4 (by rfl) ⟨199575, by rfl⟩ : syracuseStep 2128805 = 399151) (by norm_num)
theorem B1440733 : Blo 944585 1440733 := bbase (se 3 (by rfl) ⟨270137, by rfl⟩ : syracuseStep 1440733 = 540275) (by norm_num)
theorem B2128877 : Blo 944585 2128877 := bbase (se 3 (by rfl) ⟨399164, by rfl⟩ : syracuseStep 2128877 = 798329) (by norm_num)
theorem B2391029 : Blo 944585 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B2128949 : Blo 944585 2128949 := bbase (se 5 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 2128949 = 199589) (by norm_num)
theorem B1277029 : Blo 944585 1277029 := bbase (se 4 (by rfl) ⟨119721, by rfl⟩ : syracuseStep 1277029 = 239443) (by norm_num)
theorem B2129021 : Blo 944585 2129021 := bbase (se 3 (by rfl) ⟨399191, by rfl⟩ : syracuseStep 2129021 = 798383) (by norm_num)
theorem B3406997 : Blo 944585 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B2391221 : Blo 944585 2391221 := bbase (se 5 (by rfl) ⟨112088, by rfl⟩ : syracuseStep 2391221 = 224177) (by norm_num)
theorem B2129093 : Blo 944585 2129093 := bbase (se 4 (by rfl) ⟨199602, by rfl⟩ : syracuseStep 2129093 = 399205) (by norm_num)
theorem B1277149 : Blo 944585 1277149 := bbase (se 3 (by rfl) ⟨239465, by rfl⟩ : syracuseStep 1277149 = 478931) (by norm_num)
theorem B2129165 : Blo 944585 2129165 := bbase (se 3 (by rfl) ⟨399218, by rfl⟩ : syracuseStep 2129165 = 798437) (by norm_num)
theorem B1441037 : Blo 944585 1441037 := bbase (se 3 (by rfl) ⟨270194, by rfl⟩ : syracuseStep 1441037 = 540389) (by norm_num)
theorem B1080613 : Blo 944585 1080613 := bbase (se 4 (by rfl) ⟨101307, by rfl⟩ : syracuseStep 1080613 = 202615) (by norm_num)
theorem B2129237 : Blo 944585 2129237 := bbase (se 11 (by rfl) ⟨1559, by rfl⟩ : syracuseStep 2129237 = 3119) (by norm_num)
theorem B14548373 : Blo 944585 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B2129309 : Blo 944585 2129309 := bbase (se 3 (by rfl) ⟨399245, by rfl⟩ : syracuseStep 2129309 = 798491) (by norm_num)
theorem B2129381 : Blo 944585 2129381 := bbase (se 4 (by rfl) ⟨199629, by rfl⟩ : syracuseStep 2129381 = 399259) (by norm_num)
theorem B2391565 : Blo 944585 2391565 := bbase (se 3 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 2391565 = 896837) (by norm_num)
theorem B2129453 : Blo 944585 2129453 := bbase (se 3 (by rfl) ⟨399272, by rfl⟩ : syracuseStep 2129453 = 798545) (by norm_num)
theorem B1703477 : Blo 944585 1703477 := bbase (se 5 (by rfl) ⟨79850, by rfl⟩ : syracuseStep 1703477 = 159701) (by norm_num)
theorem B1080905 : Blo 944585 1080905 := bbase (se 2 (by rfl) ⟨405339, by rfl⟩ : syracuseStep 1080905 = 810679) (by norm_num)
theorem B2129525 : Blo 944585 2129525 := bbase (se 5 (by rfl) ⟨99821, by rfl⟩ : syracuseStep 2129525 = 199643) (by norm_num)
theorem B2391677 : Blo 944585 2391677 := bbase (se 3 (by rfl) ⟨448439, by rfl⟩ : syracuseStep 2391677 = 896879) (by norm_num)
theorem B2129597 : Blo 944585 2129597 := bbase (se 3 (by rfl) ⟨399299, by rfl⟩ : syracuseStep 2129597 = 798599) (by norm_num)
theorem B2129669 : Blo 944585 2129669 := bbase (se 4 (by rfl) ⟨199656, by rfl⟩ : syracuseStep 2129669 = 399313) (by norm_num)
theorem B2391869 : Blo 944585 2391869 := bbase (se 3 (by rfl) ⟨448475, by rfl⟩ : syracuseStep 2391869 = 896951) (by norm_num)
theorem B2129741 : Blo 944585 2129741 := bbase (se 3 (by rfl) ⟨399326, by rfl⟩ : syracuseStep 2129741 = 798653) (by norm_num)
theorem B6225749 : Blo 944585 6225749 := bbase (se 9 (by rfl) ⟨18239, by rfl⟩ : syracuseStep 6225749 = 36479) (by norm_num)
theorem B4784021 : Blo 944585 4784021 := bbase (se 6 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 4784021 = 224251) (by norm_num)
theorem B2129813 : Blo 944585 2129813 := bbase (se 6 (by rfl) ⟨49917, by rfl⟩ : syracuseStep 2129813 = 99835) (by norm_num)
theorem B20742101 : Blo 944585 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B2129885 : Blo 944585 2129885 := bbase (se 3 (by rfl) ⟨399353, by rfl⟩ : syracuseStep 2129885 = 798707) (by norm_num)
theorem B2392163 : Blo 944585 2392163 := bstep (se 1 (by rfl) ⟨1794122, by rfl⟩ : syracuseStep 2392163 = 3588245) B3588245
theorem B3244141 : Blo 944585 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B1278067 : Blo 944585 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B2556049 : Blo 944585 2556049 := bstep (se 2 (by rfl) ⟨958518, by rfl⟩ : syracuseStep 2556049 = 1917037) B1917037
theorem B2130065 : Blo 944585 2130065 := bstep (se 2 (by rfl) ⟨798774, by rfl⟩ : syracuseStep 2130065 = 1597549) B1597549
theorem B1441937 : Blo 944585 1441937 := bstep (se 2 (by rfl) ⟨540726, by rfl⟩ : syracuseStep 1441937 = 1081453) B1081453
theorem B2130083 : Blo 944585 2130083 := bstep (se 1 (by rfl) ⟨1597562, by rfl⟩ : syracuseStep 2130083 = 3195125) B3195125
theorem B2392355 : Blo 944585 2392355 := bstep (se 1 (by rfl) ⟨1794266, by rfl⟩ : syracuseStep 2392355 = 3588533) B3588533
theorem B2130353 : Blo 944585 2130353 := bstep (se 2 (by rfl) ⟨798882, by rfl⟩ : syracuseStep 2130353 = 1597765) B1597765
theorem B2130371 : Blo 944585 2130371 := bstep (se 1 (by rfl) ⟨1597778, by rfl⟩ : syracuseStep 2130371 = 3195557) B3195557
theorem B9732707 : Blo 944585 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B2130641 : Blo 944585 2130641 := bstep (se 2 (by rfl) ⟨798990, by rfl⟩ : syracuseStep 2130641 = 1597981) B1597981
theorem B27984611 : Blo 944585 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B2130659 : Blo 944585 2130659 := bstep (se 1 (by rfl) ⟨1597994, by rfl⟩ : syracuseStep 2130659 = 3195989) B3195989
theorem B1639201 : Blo 944585 1639201 := bstep (se 2 (by rfl) ⟨614700, by rfl⟩ : syracuseStep 1639201 = 1229401) B1229401
theorem B2589475 : Blo 944585 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B2130929 : Blo 944585 2130929 := bstep (se 2 (by rfl) ⟨799098, by rfl⟩ : syracuseStep 2130929 = 1598197) B1598197
theorem B2130947 : Blo 944585 2130947 := bstep (se 1 (by rfl) ⟨1598210, by rfl⟩ : syracuseStep 2130947 = 3196421) B3196421
theorem B3409073 : Blo 944585 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B2393297 : Blo 944585 2393297 := bstep (se 2 (by rfl) ⟨897486, by rfl⟩ : syracuseStep 2393297 = 1794973) B1794973
theorem B2393347 : Blo 944585 2393347 := bstep (se 1 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 2393347 = 3590021) B3590021
theorem B2131217 : Blo 944585 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B2131235 : Blo 944585 2131235 := bstep (se 1 (by rfl) ⟨1598426, by rfl⟩ : syracuseStep 2131235 = 3196853) B3196853
theorem B2557325 : Blo 944585 2557325 := bstep (se 3 (by rfl) ⟨479498, by rfl⟩ : syracuseStep 2557325 = 958997) B958997
theorem B2393489 : Blo 944585 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B4556195 : Blo 944585 4556195 := bstep (se 1 (by rfl) ⟨3417146, by rfl⟩ : syracuseStep 4556195 = 6834293) B6834293
theorem B2131505 : Blo 944585 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B2131523 : Blo 944585 2131523 := bstep (se 1 (by rfl) ⟨1598642, by rfl⟩ : syracuseStep 2131523 = 3197285) B3197285
theorem B1705553 : Blo 944585 1705553 := bstep (se 2 (by rfl) ⟨639582, by rfl⟩ : syracuseStep 1705553 = 1279165) B1279165
theorem B2131793 : Blo 944585 2131793 := bstep (se 2 (by rfl) ⟨799422, by rfl⟩ : syracuseStep 2131793 = 1598845) B1598845
theorem B2131811 : Blo 944585 2131811 := bstep (se 1 (by rfl) ⟨1598858, by rfl⟩ : syracuseStep 2131811 = 3197717) B3197717
theorem B4786289 : Blo 944585 4786289 := bstep (se 2 (by rfl) ⟨1794858, by rfl⟩ : syracuseStep 4786289 = 3589717) B3589717
theorem B2132081 : Blo 944585 2132081 := bstep (se 2 (by rfl) ⟨799530, by rfl⟩ : syracuseStep 2132081 = 1599061) B1599061
theorem B2132099 : Blo 944585 2132099 := bstep (se 1 (by rfl) ⟨1599074, by rfl⟩ : syracuseStep 2132099 = 3198149) B3198149
theorem B1345729 : Blo 944585 1345729 := bstep (se 2 (by rfl) ⟨504648, by rfl⟩ : syracuseStep 1345729 = 1009297) B1009297
theorem B1345825 : Blo 944585 1345825 := bstep (se 2 (by rfl) ⟨504684, by rfl⟩ : syracuseStep 1345825 = 1009369) B1009369
theorem B1280305 : Blo 944585 1280305 := bstep (se 2 (by rfl) ⟨480114, by rfl⟩ : syracuseStep 1280305 = 960229) B960229
theorem B1706339 : Blo 944585 1706339 := bstep (se 1 (by rfl) ⟨1279754, by rfl⟩ : syracuseStep 1706339 = 2559509) B2559509
theorem B2394481 : Blo 944585 2394481 := bstep (se 2 (by rfl) ⟨897930, by rfl⟩ : syracuseStep 2394481 = 1795861) B1795861
theorem B2132369 : Blo 944585 2132369 := bstep (se 2 (by rfl) ⟨799638, by rfl⟩ : syracuseStep 2132369 = 1599277) B1599277
theorem B2132387 : Blo 944585 2132387 := bstep (se 1 (by rfl) ⟨1599290, by rfl⟩ : syracuseStep 2132387 = 3198581) B3198581
theorem B2394755 : Blo 944585 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B2132657 : Blo 944585 2132657 := bstep (se 2 (by rfl) ⟨799746, by rfl⟩ : syracuseStep 2132657 = 1599493) B1599493
theorem B2132675 : Blo 944585 2132675 := bstep (se 1 (by rfl) ⟨1599506, by rfl⟩ : syracuseStep 2132675 = 3199013) B3199013
theorem B1346321 : Blo 944585 1346321 := bstep (se 2 (by rfl) ⟨504870, by rfl⟩ : syracuseStep 1346321 = 1009741) B1009741
theorem B4557617 : Blo 944585 4557617 := bstep (se 2 (by rfl) ⟨1709106, by rfl⟩ : syracuseStep 4557617 = 3418213) B3418213
theorem B2394947 : Blo 944585 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B2132945 : Blo 944585 2132945 := bstep (se 2 (by rfl) ⟨799854, by rfl⟩ : syracuseStep 2132945 = 1599709) B1599709
theorem B2132963 : Blo 944585 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B46107701 : Blo 944585 46107701 := bstep (se 5 (by rfl) ⟨2161298, by rfl⟩ : syracuseStep 46107701 = 4322597) B4322597
theorem B2690147 : Blo 944585 2690147 := bstep (se 1 (by rfl) ⟨2017610, by rfl⟩ : syracuseStep 2690147 = 4035221) B4035221
theorem B2133233 : Blo 944585 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B2133251 : Blo 944585 2133251 := bstep (se 1 (by rfl) ⟨1599938, by rfl⟩ : syracuseStep 2133251 = 3199877) B3199877
theorem B2559377 : Blo 944585 2559377 := bstep (se 2 (by rfl) ⟨959766, by rfl⟩ : syracuseStep 2559377 = 1919533) B1919533
theorem B5475761 : Blo 944585 5475761 := bstep (se 2 (by rfl) ⟨2053410, by rfl⟩ : syracuseStep 5475761 = 4106821) B4106821
theorem B2133521 : Blo 944585 2133521 := bstep (se 2 (by rfl) ⟨800070, by rfl⟩ : syracuseStep 2133521 = 1600141) B1600141
theorem B4787747 : Blo 944585 4787747 := bstep (se 1 (by rfl) ⟨3590810, by rfl⟩ : syracuseStep 4787747 = 7181621) B7181621
theorem B2133539 : Blo 944585 2133539 := bstep (se 1 (by rfl) ⟨1600154, by rfl⟩ : syracuseStep 2133539 = 3200309) B3200309
theorem B1347187 : Blo 944585 1347187 := bstep (se 1 (by rfl) ⟨1010390, by rfl⟩ : syracuseStep 1347187 = 2020781) B2020781
theorem B1347283 : Blo 944585 1347283 := bstep (se 1 (by rfl) ⟨1010462, by rfl⟩ : syracuseStep 1347283 = 2020925) B2020925
theorem B2559725 : Blo 944585 2559725 := bstep (se 3 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 2559725 = 959897) B959897
theorem B2395889 : Blo 944585 2395889 := bstep (se 2 (by rfl) ⟨898458, by rfl⟩ : syracuseStep 2395889 = 1796917) B1796917
theorem B2395939 : Blo 944585 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B2133809 : Blo 944585 2133809 := bstep (se 2 (by rfl) ⟨800178, by rfl⟩ : syracuseStep 2133809 = 1600357) B1600357
theorem B2133827 : Blo 944585 2133827 := bstep (se 1 (by rfl) ⟨1600370, by rfl⟩ : syracuseStep 2133827 = 3200741) B3200741
theorem B3411811 : Blo 944585 3411811 := bstep (se 1 (by rfl) ⟨2558858, by rfl⟩ : syracuseStep 3411811 = 5117717) B5117717
theorem B2396081 : Blo 944585 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B6230029 : Blo 944585 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B2134097 : Blo 944585 2134097 := bstep (se 2 (by rfl) ⟨800286, by rfl⟩ : syracuseStep 2134097 = 1600573) B1600573
theorem B2134115 : Blo 944585 2134115 := bstep (se 1 (by rfl) ⟨1600586, by rfl⟩ : syracuseStep 2134115 = 3201173) B3201173
theorem B1347779 : Blo 944585 1347779 := bstep (se 1 (by rfl) ⟨1010834, by rfl⟩ : syracuseStep 1347779 = 2021669) B2021669
theorem B2691377 : Blo 944585 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B4788557 : Blo 944585 4788557 := bstep (se 3 (by rfl) ⟨897854, by rfl⟩ : syracuseStep 4788557 = 1795709) B1795709
theorem B1184419 : Blo 944585 1184419 := bstep (se 1 (by rfl) ⟨888314, by rfl⟩ : syracuseStep 1184419 = 1776629) B1776629
theorem B1348417 : Blo 944585 1348417 := bstep (se 2 (by rfl) ⟨505656, by rfl⟩ : syracuseStep 1348417 = 1011313) B1011313
theorem B2397073 : Blo 944585 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B4035683 : Blo 944585 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B1348753 : Blo 944585 1348753 := bstep (se 2 (by rfl) ⟨505782, by rfl⟩ : syracuseStep 1348753 = 1011565) B1011565
theorem B2397347 : Blo 944585 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B2397539 : Blo 944585 2397539 := bstep (se 1 (by rfl) ⟨1798154, by rfl⟩ : syracuseStep 2397539 = 3596309) B3596309
theorem B1349345 : Blo 944585 1349345 := bstep (se 2 (by rfl) ⟨506004, by rfl⟩ : syracuseStep 1349345 = 1012009) B1012009
theorem B2692835 : Blo 944585 2692835 := bstep (se 1 (by rfl) ⟨2019626, by rfl⟩ : syracuseStep 2692835 = 4039253) B4039253
theorem B3413873 : Blo 944585 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B14784565 : Blo 944585 14784565 := bstep (se 5 (by rfl) ⟨693026, by rfl⟩ : syracuseStep 14784565 = 1386053) B1386053
theorem B2431043 : Blo 944585 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B5118065 : Blo 944585 5118065 := bstep (se 2 (by rfl) ⟨1919274, by rfl⟩ : syracuseStep 5118065 = 3838549) B3838549
theorem B1349875 : Blo 944585 1349875 := bstep (se 1 (by rfl) ⟨1012406, by rfl⟩ : syracuseStep 1349875 = 2024813) B2024813
theorem B2398481 : Blo 944585 2398481 := bstep (se 2 (by rfl) ⟨899430, by rfl⟩ : syracuseStep 2398481 = 1798861) B1798861
theorem B6068515 : Blo 944585 6068515 := bstep (se 1 (by rfl) ⟨4551386, by rfl⟩ : syracuseStep 6068515 = 9102773) B9102773
theorem B2398531 : Blo 944585 2398531 := bstep (se 1 (by rfl) ⟨1798898, by rfl⟩ : syracuseStep 2398531 = 3597797) B3597797
theorem B1513811 : Blo 944585 1513811 := bstep (se 1 (by rfl) ⟨1135358, by rfl⟩ : syracuseStep 1513811 = 2270717) B2270717
theorem B2398673 : Blo 944585 2398673 := bstep (se 2 (by rfl) ⟨899502, by rfl⟩ : syracuseStep 2398673 = 1799005) B1799005
theorem B2103779 : Blo 944585 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B5380613 : Blo 944585 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B2693645 : Blo 944585 2693645 := bstep (se 3 (by rfl) ⟨505058, by rfl⟩ : syracuseStep 2693645 = 1010117) B1010117
theorem B2431505 : Blo 944585 2431505 := bstep (se 2 (by rfl) ⟨911814, by rfl⟩ : syracuseStep 2431505 = 1823629) B1823629
theorem B1350211 : Blo 944585 1350211 := bstep (se 1 (by rfl) ⟨1012658, by rfl⟩ : syracuseStep 1350211 = 2025317) B2025317
theorem B1514099 : Blo 944585 1514099 := bstep (se 1 (by rfl) ⟨1135574, by rfl⟩ : syracuseStep 1514099 = 2271149) B2271149
theorem B2693837 : Blo 944585 2693837 := bstep (se 3 (by rfl) ⟨505094, by rfl⟩ : syracuseStep 2693837 = 1010189) B1010189
theorem B9116387 : Blo 944585 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B3644237 : Blo 944585 3644237 := bstep (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) B1366589
theorem B1514323 : Blo 944585 1514323 := bstep (se 1 (by rfl) ⟨1135742, by rfl⟩ : syracuseStep 1514323 = 2271485) B2271485
theorem B1154035 : Blo 944585 1154035 := bstep (se 1 (by rfl) ⟨865526, by rfl⟩ : syracuseStep 1154035 = 1731053) B1731053
theorem B4037681 : Blo 944585 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B4791473 : Blo 944585 4791473 := bstep (se 2 (by rfl) ⟨1796802, by rfl⟩ : syracuseStep 4791473 = 3593605) B3593605
theorem B1023331 : Blo 944585 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B1154419 : Blo 944585 1154419 := bstep (se 1 (by rfl) ⟨865814, by rfl⟩ : syracuseStep 1154419 = 1731629) B1731629
theorem B2399665 : Blo 944585 2399665 := bstep (se 2 (by rfl) ⟨899874, by rfl⟩ : syracuseStep 2399665 = 1799749) B1799749
theorem B6069745 : Blo 944585 6069745 := bstep (se 2 (by rfl) ⟨2276154, by rfl⟩ : syracuseStep 6069745 = 4552309) B4552309
theorem B1515041 : Blo 944585 1515041 := bstep (se 2 (by rfl) ⟨568140, by rfl⟩ : syracuseStep 1515041 = 1136281) B1136281
theorem B3284525 : Blo 944585 3284525 := bstep (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) B1231697
theorem B24288821 : Blo 944585 24288821 := bstep (se 5 (by rfl) ⟨1138538, by rfl⟩ : syracuseStep 24288821 = 2277077) B2277077
theorem B2694829 : Blo 944585 2694829 := bstep (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) B1010561
theorem B1416881 : Blo 944585 1416881 := bstep (se 2 (by rfl) ⟨531330, by rfl⟩ : syracuseStep 1416881 = 1062661) B1062661
theorem B1416899 : Blo 944585 1416899 := bstep (se 1 (by rfl) ⟨1062674, by rfl⟩ : syracuseStep 1416899 = 2125349) B2125349
theorem B2399939 : Blo 944585 2399939 := bstep (se 1 (by rfl) ⟨1799954, by rfl⟩ : syracuseStep 2399939 = 3599909) B3599909
theorem B1416929 : Blo 944585 1416929 := bstep (se 2 (by rfl) ⟨531348, by rfl⟩ : syracuseStep 1416929 = 1062697) B1062697
theorem B1515233 : Blo 944585 1515233 := bstep (se 2 (by rfl) ⟨568212, by rfl⟩ : syracuseStep 1515233 = 1136425) B1136425
theorem B1416947 : Blo 944585 1416947 := bstep (se 1 (by rfl) ⟨1062710, by rfl⟩ : syracuseStep 1416947 = 2125421) B2125421
theorem B1416977 : Blo 944585 1416977 := bstep (se 2 (by rfl) ⟨531366, by rfl⟩ : syracuseStep 1416977 = 1062733) B1062733
theorem B1416995 : Blo 944585 1416995 := bstep (se 1 (by rfl) ⟨1062746, by rfl⟩ : syracuseStep 1416995 = 2125493) B2125493
theorem B1417025 : Blo 944585 1417025 := bstep (se 2 (by rfl) ⟨531384, by rfl⟩ : syracuseStep 1417025 = 1062769) B1062769
theorem B1417043 : Blo 944585 1417043 := bstep (se 1 (by rfl) ⟨1062782, by rfl⟩ : syracuseStep 1417043 = 2125565) B2125565
theorem B1515361 : Blo 944585 1515361 := bstep (se 2 (by rfl) ⟨568260, by rfl⟩ : syracuseStep 1515361 = 1136521) B1136521
theorem B1417073 : Blo 944585 1417073 := bstep (se 2 (by rfl) ⟨531402, by rfl⟩ : syracuseStep 1417073 = 1062805) B1062805
theorem B1417091 : Blo 944585 1417091 := bstep (se 1 (by rfl) ⟨1062818, by rfl⟩ : syracuseStep 1417091 = 2125637) B2125637
theorem B2400131 : Blo 944585 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B1417121 : Blo 944585 1417121 := bstep (se 2 (by rfl) ⟨531420, by rfl⟩ : syracuseStep 1417121 = 1062841) B1062841
theorem B1417139 : Blo 944585 1417139 := bstep (se 1 (by rfl) ⟨1062854, by rfl⟩ : syracuseStep 1417139 = 2125709) B2125709
theorem B4038605 : Blo 944585 4038605 := bstep (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) B1514477
theorem B1417169 : Blo 944585 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B1417187 : Blo 944585 1417187 := bstep (se 1 (by rfl) ⟨1062890, by rfl⟩ : syracuseStep 1417187 = 2125781) B2125781
theorem B1417217 : Blo 944585 1417217 := bstep (se 2 (by rfl) ⟨531456, by rfl⟩ : syracuseStep 1417217 = 1062913) B1062913
theorem B3416077 : Blo 944585 3416077 := bstep (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) B1281029
theorem B1417235 : Blo 944585 1417235 := bstep (se 1 (by rfl) ⟨1062926, by rfl⟩ : syracuseStep 1417235 = 2125853) B2125853
theorem B1417265 : Blo 944585 1417265 := bstep (se 2 (by rfl) ⟨531474, by rfl⟩ : syracuseStep 1417265 = 1062949) B1062949
theorem B1417283 : Blo 944585 1417283 := bstep (se 1 (by rfl) ⟨1062962, by rfl⟩ : syracuseStep 1417283 = 2125925) B2125925
theorem B1417313 : Blo 944585 1417313 := bstep (se 2 (by rfl) ⟨531492, by rfl⟩ : syracuseStep 1417313 = 1062985) B1062985
theorem B34480241 : Blo 944585 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B1417331 : Blo 944585 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B1417361 : Blo 944585 1417361 := bstep (se 2 (by rfl) ⟨531510, by rfl⟩ : syracuseStep 1417361 = 1063021) B1063021
theorem B1417379 : Blo 944585 1417379 := bstep (se 1 (by rfl) ⟨1063034, by rfl⟩ : syracuseStep 1417379 = 2126069) B2126069
theorem B1417409 : Blo 944585 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B1417427 : Blo 944585 1417427 := bstep (se 1 (by rfl) ⟨1063070, by rfl⟩ : syracuseStep 1417427 = 2126141) B2126141
theorem B1024211 : Blo 944585 1024211 := bstep (se 1 (by rfl) ⟨768158, by rfl⟩ : syracuseStep 1024211 = 1536317) B1536317
theorem B23306467 : Blo 944585 23306467 := bstep (se 1 (by rfl) ⟨17479850, by rfl⟩ : syracuseStep 23306467 = 34959701) B34959701
theorem B1417457 : Blo 944585 1417457 := bstep (se 2 (by rfl) ⟨531546, by rfl⟩ : syracuseStep 1417457 = 1063093) B1063093
theorem B1417475 : Blo 944585 1417475 := bstep (se 1 (by rfl) ⟨1063106, by rfl⟩ : syracuseStep 1417475 = 2126213) B2126213
theorem B1417505 : Blo 944585 1417505 := bstep (se 2 (by rfl) ⟨531564, by rfl⟩ : syracuseStep 1417505 = 1063129) B1063129
theorem B4858147 : Blo 944585 4858147 := bstep (se 1 (by rfl) ⟨3643610, by rfl⟩ : syracuseStep 4858147 = 7287221) B7287221
theorem B1417523 : Blo 944585 1417523 := bstep (se 1 (by rfl) ⟨1063142, by rfl⟩ : syracuseStep 1417523 = 2126285) B2126285
theorem B1417553 : Blo 944585 1417553 := bstep (se 2 (by rfl) ⟨531582, by rfl⟩ : syracuseStep 1417553 = 1063165) B1063165
theorem B1417571 : Blo 944585 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B1417601 : Blo 944585 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B1417619 : Blo 944585 1417619 := bstep (se 1 (by rfl) ⟨1063214, by rfl⟩ : syracuseStep 1417619 = 2126429) B2126429
theorem B1417649 : Blo 944585 1417649 := bstep (se 2 (by rfl) ⟨531618, by rfl⟩ : syracuseStep 1417649 = 1063237) B1063237
theorem B1417667 : Blo 944585 1417667 := bstep (se 1 (by rfl) ⟨1063250, by rfl⟩ : syracuseStep 1417667 = 2126501) B2126501
theorem B1417697 : Blo 944585 1417697 := bstep (se 2 (by rfl) ⟨531636, by rfl⟩ : syracuseStep 1417697 = 1063273) B1063273
theorem B1516001 : Blo 944585 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B1417715 : Blo 944585 1417715 := bstep (se 1 (by rfl) ⟨1063286, by rfl⟩ : syracuseStep 1417715 = 2126573) B2126573
theorem B1417745 : Blo 944585 1417745 := bstep (se 2 (by rfl) ⟨531654, by rfl⟩ : syracuseStep 1417745 = 1063309) B1063309
theorem B1417763 : Blo 944585 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B1417793 : Blo 944585 1417793 := bstep (se 2 (by rfl) ⟨531672, by rfl⟩ : syracuseStep 1417793 = 1063345) B1063345
theorem B1417811 : Blo 944585 1417811 := bstep (se 1 (by rfl) ⟨1063358, by rfl⟩ : syracuseStep 1417811 = 2126717) B2126717
theorem B4792931 : Blo 944585 4792931 := bstep (se 1 (by rfl) ⟨3594698, by rfl⟩ : syracuseStep 4792931 = 7189397) B7189397
theorem B1417841 : Blo 944585 1417841 := bstep (se 2 (by rfl) ⟨531690, by rfl⟩ : syracuseStep 1417841 = 1063381) B1063381
theorem B1417859 : Blo 944585 1417859 := bstep (se 1 (by rfl) ⟨1063394, by rfl⟩ : syracuseStep 1417859 = 2126789) B2126789
theorem B1417889 : Blo 944585 1417889 := bstep (se 2 (by rfl) ⟨531708, by rfl⟩ : syracuseStep 1417889 = 1063417) B1063417
theorem B1417907 : Blo 944585 1417907 := bstep (se 1 (by rfl) ⟨1063430, by rfl⟩ : syracuseStep 1417907 = 2126861) B2126861
theorem B3842765 : Blo 944585 3842765 := bstep (se 3 (by rfl) ⟨720518, by rfl⟩ : syracuseStep 3842765 = 1441037) B1441037
theorem B1417937 : Blo 944585 1417937 := bstep (se 2 (by rfl) ⟨531726, by rfl⟩ : syracuseStep 1417937 = 1063453) B1063453
theorem B1417955 : Blo 944585 1417955 := bstep (se 1 (by rfl) ⟨1063466, by rfl⟩ : syracuseStep 1417955 = 2126933) B2126933
theorem B4104931 : Blo 944585 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B1417985 : Blo 944585 1417985 := bstep (se 2 (by rfl) ⟨531744, by rfl⟩ : syracuseStep 1417985 = 1063489) B1063489
theorem B1418003 : Blo 944585 1418003 := bstep (se 1 (by rfl) ⟨1063502, by rfl⟩ : syracuseStep 1418003 = 2127005) B2127005
theorem B1418033 : Blo 944585 1418033 := bstep (se 2 (by rfl) ⟨531762, by rfl⟩ : syracuseStep 1418033 = 1063525) B1063525
theorem B2401073 : Blo 944585 2401073 := bstep (se 2 (by rfl) ⟨900402, by rfl⟩ : syracuseStep 2401073 = 1800805) B1800805
theorem B1418051 : Blo 944585 1418051 := bstep (se 1 (by rfl) ⟨1063538, by rfl⟩ : syracuseStep 1418051 = 2127077) B2127077
theorem B6824773 : Blo 944585 6824773 := bstep (se 4 (by rfl) ⟨639822, by rfl⟩ : syracuseStep 6824773 = 1279645) B1279645
theorem B1418081 : Blo 944585 1418081 := bstep (se 2 (by rfl) ⟨531780, by rfl⟩ : syracuseStep 1418081 = 1063561) B1063561
theorem B1418099 : Blo 944585 1418099 := bstep (se 1 (by rfl) ⟨1063574, by rfl⟩ : syracuseStep 1418099 = 2127149) B2127149
theorem B1418129 : Blo 944585 1418129 := bstep (se 2 (by rfl) ⟨531798, by rfl⟩ : syracuseStep 1418129 = 1063597) B1063597
theorem B1418147 : Blo 944585 1418147 := bstep (se 1 (by rfl) ⟨1063610, by rfl⟩ : syracuseStep 1418147 = 2127221) B2127221
theorem B1418177 : Blo 944585 1418177 := bstep (se 2 (by rfl) ⟨531816, by rfl⟩ : syracuseStep 1418177 = 1063633) B1063633
theorem B1418195 : Blo 944585 1418195 := bstep (se 1 (by rfl) ⟨1063646, by rfl⟩ : syracuseStep 1418195 = 2127293) B2127293
theorem B1418225 : Blo 944585 1418225 := bstep (se 2 (by rfl) ⟨531834, by rfl⟩ : syracuseStep 1418225 = 1063669) B1063669
theorem B1418243 : Blo 944585 1418243 := bstep (se 1 (by rfl) ⟨1063682, by rfl⟩ : syracuseStep 1418243 = 2127365) B2127365
theorem B1418273 : Blo 944585 1418273 := bstep (se 2 (by rfl) ⟨531852, by rfl⟩ : syracuseStep 1418273 = 1063705) B1063705
theorem B1418291 : Blo 944585 1418291 := bstep (se 1 (by rfl) ⟨1063718, by rfl⟩ : syracuseStep 1418291 = 2127437) B2127437
theorem B1418321 : Blo 944585 1418321 := bstep (se 2 (by rfl) ⟨531870, by rfl⟩ : syracuseStep 1418321 = 1063741) B1063741
theorem B1418339 : Blo 944585 1418339 := bstep (se 1 (by rfl) ⟨1063754, by rfl⟩ : syracuseStep 1418339 = 2127509) B2127509
theorem B1418369 : Blo 944585 1418369 := bstep (se 2 (by rfl) ⟨531888, by rfl⟩ : syracuseStep 1418369 = 1063777) B1063777
theorem B5121157 : Blo 944585 5121157 := bstep (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) B960217
theorem B1418387 : Blo 944585 1418387 := bstep (se 1 (by rfl) ⟨1063790, by rfl⟩ : syracuseStep 1418387 = 2127581) B2127581
theorem B1418417 : Blo 944585 1418417 := bstep (se 2 (by rfl) ⟨531906, by rfl⟩ : syracuseStep 1418417 = 1063813) B1063813
theorem B1418435 : Blo 944585 1418435 := bstep (se 1 (by rfl) ⟨1063826, by rfl⟩ : syracuseStep 1418435 = 2127653) B2127653
theorem B1418465 : Blo 944585 1418465 := bstep (se 2 (by rfl) ⟨531924, by rfl⟩ : syracuseStep 1418465 = 1063849) B1063849
theorem B1418483 : Blo 944585 1418483 := bstep (se 1 (by rfl) ⟨1063862, by rfl⟩ : syracuseStep 1418483 = 2127725) B2127725
theorem B1418513 : Blo 944585 1418513 := bstep (se 2 (by rfl) ⟨531942, by rfl⟩ : syracuseStep 1418513 = 1063885) B1063885
theorem B1418531 : Blo 944585 1418531 := bstep (se 1 (by rfl) ⟨1063898, by rfl⟩ : syracuseStep 1418531 = 2127797) B2127797
theorem B1418561 : Blo 944585 1418561 := bstep (se 2 (by rfl) ⟨531960, by rfl⟩ : syracuseStep 1418561 = 1063921) B1063921
theorem B1418579 : Blo 944585 1418579 := bstep (se 1 (by rfl) ⟨1063934, by rfl⟩ : syracuseStep 1418579 = 2127869) B2127869
theorem B1418609 : Blo 944585 1418609 := bstep (se 2 (by rfl) ⟨531978, by rfl⟩ : syracuseStep 1418609 = 1063957) B1063957
theorem B2696561 : Blo 944585 2696561 := bstep (se 2 (by rfl) ⟨1011210, by rfl⟩ : syracuseStep 2696561 = 2022421) B2022421
theorem B1418627 : Blo 944585 1418627 := bstep (se 1 (by rfl) ⟨1063970, by rfl⟩ : syracuseStep 1418627 = 2127941) B2127941
theorem B4793741 : Blo 944585 4793741 := bstep (se 3 (by rfl) ⟨898826, by rfl⟩ : syracuseStep 4793741 = 1797653) B1797653
theorem B12166541 : Blo 944585 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B1418657 : Blo 944585 1418657 := bstep (se 2 (by rfl) ⟨531996, by rfl⟩ : syracuseStep 1418657 = 1063993) B1063993
theorem B1418675 : Blo 944585 1418675 := bstep (se 1 (by rfl) ⟨1064006, by rfl⟩ : syracuseStep 1418675 = 2128013) B2128013
theorem B1418705 : Blo 944585 1418705 := bstep (se 2 (by rfl) ⟨532014, by rfl⟩ : syracuseStep 1418705 = 1064029) B1064029
theorem B1418723 : Blo 944585 1418723 := bstep (se 1 (by rfl) ⟨1064042, by rfl⟩ : syracuseStep 1418723 = 2128085) B2128085
theorem B1418753 : Blo 944585 1418753 := bstep (se 2 (by rfl) ⟨532032, by rfl⟩ : syracuseStep 1418753 = 1064065) B1064065
theorem B1418771 : Blo 944585 1418771 := bstep (se 1 (by rfl) ⟨1064078, by rfl⟩ : syracuseStep 1418771 = 2128157) B2128157
theorem B1418801 : Blo 944585 1418801 := bstep (se 2 (by rfl) ⟨532050, by rfl⟩ : syracuseStep 1418801 = 1064101) B1064101
theorem B2696753 : Blo 944585 2696753 := bstep (se 2 (by rfl) ⟨1011282, by rfl⟩ : syracuseStep 2696753 = 2022565) B2022565
theorem B1418819 : Blo 944585 1418819 := bstep (se 1 (by rfl) ⟨1064114, by rfl⟩ : syracuseStep 1418819 = 2128229) B2128229
theorem B1418849 : Blo 944585 1418849 := bstep (se 2 (by rfl) ⟨532068, by rfl⟩ : syracuseStep 1418849 = 1064137) B1064137
theorem B1418867 : Blo 944585 1418867 := bstep (se 1 (by rfl) ⟨1064150, by rfl⟩ : syracuseStep 1418867 = 2128301) B2128301
theorem B1418897 : Blo 944585 1418897 := bstep (se 2 (by rfl) ⟨532086, by rfl⟩ : syracuseStep 1418897 = 1064173) B1064173
theorem B1418915 : Blo 944585 1418915 := bstep (se 1 (by rfl) ⟨1064186, by rfl⟩ : syracuseStep 1418915 = 2128373) B2128373
theorem B1418945 : Blo 944585 1418945 := bstep (se 2 (by rfl) ⟨532104, by rfl⟩ : syracuseStep 1418945 = 1064209) B1064209
theorem B3188429 : Blo 944585 3188429 := bstep (se 3 (by rfl) ⟨597830, by rfl⟩ : syracuseStep 3188429 = 1195661) B1195661
theorem B1418963 : Blo 944585 1418963 := bstep (se 1 (by rfl) ⟨1064222, by rfl⟩ : syracuseStep 1418963 = 2128445) B2128445
theorem B1418993 : Blo 944585 1418993 := bstep (se 2 (by rfl) ⟨532122, by rfl⟩ : syracuseStep 1418993 = 1064245) B1064245
theorem B3188483 : Blo 944585 3188483 := bstep (se 1 (by rfl) ⟨2391362, by rfl⟩ : syracuseStep 3188483 = 4782725) B4782725
theorem B1419011 : Blo 944585 1419011 := bstep (se 1 (by rfl) ⟨1064258, by rfl⟩ : syracuseStep 1419011 = 2128517) B2128517
theorem B1419041 : Blo 944585 1419041 := bstep (se 2 (by rfl) ⟨532140, by rfl⟩ : syracuseStep 1419041 = 1064281) B1064281
theorem B1419059 : Blo 944585 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B1419089 : Blo 944585 1419089 := bstep (se 2 (by rfl) ⟨532158, by rfl⟩ : syracuseStep 1419089 = 1064317) B1064317
theorem B1419107 : Blo 944585 1419107 := bstep (se 1 (by rfl) ⟨1064330, by rfl⟩ : syracuseStep 1419107 = 2128661) B2128661
theorem B1517411 : Blo 944585 1517411 := bstep (se 1 (by rfl) ⟨1138058, by rfl⟩ : syracuseStep 1517411 = 2276117) B2276117
theorem B1419137 : Blo 944585 1419137 := bstep (se 2 (by rfl) ⟨532176, by rfl⟩ : syracuseStep 1419137 = 1064353) B1064353
theorem B1419155 : Blo 944585 1419155 := bstep (se 1 (by rfl) ⟨1064366, by rfl⟩ : syracuseStep 1419155 = 2128733) B2128733
theorem B1419185 : Blo 944585 1419185 := bstep (se 2 (by rfl) ⟨532194, by rfl⟩ : syracuseStep 1419185 = 1064389) B1064389
theorem B1419203 : Blo 944585 1419203 := bstep (se 1 (by rfl) ⟨1064402, by rfl⟩ : syracuseStep 1419203 = 2128805) B2128805
theorem B1419233 : Blo 944585 1419233 := bstep (se 2 (by rfl) ⟨532212, by rfl⟩ : syracuseStep 1419233 = 1064425) B1064425
theorem B1517539 : Blo 944585 1517539 := bstep (se 1 (by rfl) ⟨1138154, by rfl⟩ : syracuseStep 1517539 = 2276309) B2276309
theorem B1419251 : Blo 944585 1419251 := bstep (se 1 (by rfl) ⟨1064438, by rfl⟩ : syracuseStep 1419251 = 2128877) B2128877
theorem B3188753 : Blo 944585 3188753 := bstep (se 2 (by rfl) ⟨1195782, by rfl⟩ : syracuseStep 3188753 = 2391565) B2391565
theorem B1419281 : Blo 944585 1419281 := bstep (se 2 (by rfl) ⟨532230, by rfl⟩ : syracuseStep 1419281 = 1064461) B1064461
theorem B2304035 : Blo 944585 2304035 := bstep (se 1 (by rfl) ⟨1728026, by rfl⟩ : syracuseStep 2304035 = 3456053) B3456053
theorem B1419299 : Blo 944585 1419299 := bstep (se 1 (by rfl) ⟨1064474, by rfl⟩ : syracuseStep 1419299 = 2128949) B2128949
theorem B1419329 : Blo 944585 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B1419347 : Blo 944585 1419347 := bstep (se 1 (by rfl) ⟨1064510, by rfl⟩ : syracuseStep 1419347 = 2129021) B2129021
theorem B2271331 : Blo 944585 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B1419377 : Blo 944585 1419377 := bstep (se 2 (by rfl) ⟨532266, by rfl⟩ : syracuseStep 1419377 = 1064533) B1064533
theorem B1419395 : Blo 944585 1419395 := bstep (se 1 (by rfl) ⟨1064546, by rfl⟩ : syracuseStep 1419395 = 2129093) B2129093
theorem B1419425 : Blo 944585 1419425 := bstep (se 2 (by rfl) ⟨532284, by rfl⟩ : syracuseStep 1419425 = 1064569) B1064569
theorem B3287213 : Blo 944585 3287213 := bstep (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) B1232705
theorem B1419443 : Blo 944585 1419443 := bstep (se 1 (by rfl) ⟨1064582, by rfl⟩ : syracuseStep 1419443 = 2129165) B2129165
theorem B1419473 : Blo 944585 1419473 := bstep (se 2 (by rfl) ⟨532302, by rfl⟩ : syracuseStep 1419473 = 1064605) B1064605
theorem B1419491 : Blo 944585 1419491 := bstep (se 1 (by rfl) ⟨1064618, by rfl⟩ : syracuseStep 1419491 = 2129237) B2129237
theorem B1419521 : Blo 944585 1419521 := bstep (se 2 (by rfl) ⟨532320, by rfl⟩ : syracuseStep 1419521 = 1064641) B1064641
theorem B1419539 : Blo 944585 1419539 := bstep (se 1 (by rfl) ⟨1064654, by rfl⟩ : syracuseStep 1419539 = 2129309) B2129309
theorem B1419569 : Blo 944585 1419569 := bstep (se 2 (by rfl) ⟨532338, by rfl⟩ : syracuseStep 1419569 = 1064677) B1064677
theorem B1419587 : Blo 944585 1419587 := bstep (se 1 (by rfl) ⟨1064690, by rfl⟩ : syracuseStep 1419587 = 2129381) B2129381
theorem B1419617 : Blo 944585 1419617 := bstep (se 2 (by rfl) ⟨532356, by rfl⟩ : syracuseStep 1419617 = 1064713) B1064713
theorem B1419635 : Blo 944585 1419635 := bstep (se 1 (by rfl) ⟨1064726, by rfl⟩ : syracuseStep 1419635 = 2129453) B2129453
theorem B1419665 : Blo 944585 1419665 := bstep (se 2 (by rfl) ⟨532374, by rfl⟩ : syracuseStep 1419665 = 1064749) B1064749
theorem B1419683 : Blo 944585 1419683 := bstep (se 1 (by rfl) ⟨1064762, by rfl⟩ : syracuseStep 1419683 = 2129525) B2129525
theorem B1419713 : Blo 944585 1419713 := bstep (se 2 (by rfl) ⟨532392, by rfl⟩ : syracuseStep 1419713 = 1064785) B1064785
theorem B18196933 : Blo 944585 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B1419731 : Blo 944585 1419731 := bstep (se 1 (by rfl) ⟨1064798, by rfl⟩ : syracuseStep 1419731 = 2129597) B2129597
theorem B1419761 : Blo 944585 1419761 := bstep (se 2 (by rfl) ⟨532410, by rfl⟩ : syracuseStep 1419761 = 1064821) B1064821
theorem B1419779 : Blo 944585 1419779 := bstep (se 1 (by rfl) ⟨1064834, by rfl⟩ : syracuseStep 1419779 = 2129669) B2129669
theorem B2697745 : Blo 944585 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B1518097 : Blo 944585 1518097 := bstep (se 2 (by rfl) ⟨569286, by rfl⟩ : syracuseStep 1518097 = 1138573) B1138573
theorem B1419809 : Blo 944585 1419809 := bstep (se 2 (by rfl) ⟨532428, by rfl⟩ : syracuseStep 1419809 = 1064857) B1064857
theorem B3189293 : Blo 944585 3189293 := bstep (se 3 (by rfl) ⟨597992, by rfl⟩ : syracuseStep 3189293 = 1195985) B1195985
theorem B1419827 : Blo 944585 1419827 := bstep (se 1 (by rfl) ⟨1064870, by rfl⟩ : syracuseStep 1419827 = 2129741) B2129741
theorem B1944145 : Blo 944585 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B1419857 : Blo 944585 1419857 := bstep (se 2 (by rfl) ⟨532446, by rfl⟩ : syracuseStep 1419857 = 1064893) B1064893
theorem B3189347 : Blo 944585 3189347 := bstep (se 1 (by rfl) ⟨2392010, by rfl⟩ : syracuseStep 3189347 = 4784021) B4784021
theorem B1419875 : Blo 944585 1419875 := bstep (se 1 (by rfl) ⟨1064906, by rfl⟩ : syracuseStep 1419875 = 2129813) B2129813
theorem B1419905 : Blo 944585 1419905 := bstep (se 2 (by rfl) ⟨532464, by rfl⟩ : syracuseStep 1419905 = 1064929) B1064929
theorem B1419923 : Blo 944585 1419923 := bstep (se 1 (by rfl) ⟨1064942, by rfl⟩ : syracuseStep 1419923 = 2129885) B2129885
theorem B1419953 : Blo 944585 1419953 := bstep (se 2 (by rfl) ⟨532482, by rfl⟩ : syracuseStep 1419953 = 1064965) B1064965
theorem B1419971 : Blo 944585 1419971 := bstep (se 1 (by rfl) ⟨1064978, by rfl⟩ : syracuseStep 1419971 = 2129957) B2129957
theorem B1420001 : Blo 944585 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B1420019 : Blo 944585 1420019 := bstep (se 1 (by rfl) ⟨1065014, by rfl⟩ : syracuseStep 1420019 = 2130029) B2130029
theorem B1420049 : Blo 944585 1420049 := bstep (se 2 (by rfl) ⟨532518, by rfl⟩ : syracuseStep 1420049 = 1065037) B1065037
theorem B1420067 : Blo 944585 1420067 := bstep (se 1 (by rfl) ⟨1065050, by rfl⟩ : syracuseStep 1420067 = 2130101) B2130101
theorem B2698019 : Blo 944585 2698019 := bstep (se 1 (by rfl) ⟨2023514, by rfl⟩ : syracuseStep 2698019 = 4047029) B4047029
theorem B1420097 : Blo 944585 1420097 := bstep (se 2 (by rfl) ⟨532536, by rfl⟩ : syracuseStep 1420097 = 1065073) B1065073
theorem B1420115 : Blo 944585 1420115 := bstep (se 1 (by rfl) ⟨1065086, by rfl⟩ : syracuseStep 1420115 = 2130173) B2130173
theorem B3189617 : Blo 944585 3189617 := bstep (se 2 (by rfl) ⟨1196106, by rfl⟩ : syracuseStep 3189617 = 2392213) B2392213
theorem B1420145 : Blo 944585 1420145 := bstep (se 2 (by rfl) ⟨532554, by rfl⟩ : syracuseStep 1420145 = 1065109) B1065109
theorem B21900145 : Blo 944585 21900145 := bstep (se 2 (by rfl) ⟨8212554, by rfl⟩ : syracuseStep 21900145 = 16425109) B16425109
theorem B1420163 : Blo 944585 1420163 := bstep (se 1 (by rfl) ⟨1065122, by rfl⟩ : syracuseStep 1420163 = 2130245) B2130245
theorem B1420193 : Blo 944585 1420193 := bstep (se 2 (by rfl) ⟨532572, by rfl⟩ : syracuseStep 1420193 = 1065145) B1065145
theorem B1420211 : Blo 944585 1420211 := bstep (se 1 (by rfl) ⟨1065158, by rfl⟩ : syracuseStep 1420211 = 2130317) B2130317
theorem B3845069 : Blo 944585 3845069 := bstep (se 3 (by rfl) ⟨720950, by rfl⟩ : syracuseStep 3845069 = 1441901) B1441901
theorem B1420241 : Blo 944585 1420241 := bstep (se 2 (by rfl) ⟨532590, by rfl⟩ : syracuseStep 1420241 = 1065181) B1065181
theorem B2698211 : Blo 944585 2698211 := bstep (se 1 (by rfl) ⟨2023658, by rfl⟩ : syracuseStep 2698211 = 4047317) B4047317
theorem B1420259 : Blo 944585 1420259 := bstep (se 1 (by rfl) ⟨1065194, by rfl⟩ : syracuseStep 1420259 = 2130389) B2130389
theorem B4041713 : Blo 944585 4041713 := bstep (se 2 (by rfl) ⟨1515642, by rfl⟩ : syracuseStep 4041713 = 3031285) B3031285
theorem B1420289 : Blo 944585 1420289 := bstep (se 2 (by rfl) ⟨532608, by rfl⟩ : syracuseStep 1420289 = 1065217) B1065217
theorem B1420307 : Blo 944585 1420307 := bstep (se 1 (by rfl) ⟨1065230, by rfl⟩ : syracuseStep 1420307 = 2130461) B2130461
theorem B1420337 : Blo 944585 1420337 := bstep (se 2 (by rfl) ⟨532626, by rfl⟩ : syracuseStep 1420337 = 1065253) B1065253
theorem B1420355 : Blo 944585 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B1420385 : Blo 944585 1420385 := bstep (se 2 (by rfl) ⟨532644, by rfl⟩ : syracuseStep 1420385 = 1065289) B1065289
theorem B1420403 : Blo 944585 1420403 := bstep (se 1 (by rfl) ⟨1065302, by rfl⟩ : syracuseStep 1420403 = 2130605) B2130605
theorem B1420433 : Blo 944585 1420433 := bstep (se 2 (by rfl) ⟨532662, by rfl⟩ : syracuseStep 1420433 = 1065325) B1065325
theorem B1420451 : Blo 944585 1420451 := bstep (se 1 (by rfl) ⟨1065338, by rfl⟩ : syracuseStep 1420451 = 2130677) B2130677
theorem B1518769 : Blo 944585 1518769 := bstep (se 2 (by rfl) ⟨569538, by rfl⟩ : syracuseStep 1518769 = 1139077) B1139077
theorem B1420481 : Blo 944585 1420481 := bstep (se 2 (by rfl) ⟨532680, by rfl⟩ : syracuseStep 1420481 = 1065361) B1065361
theorem B6073541 : Blo 944585 6073541 := bstep (se 4 (by rfl) ⟨569394, by rfl⟩ : syracuseStep 6073541 = 1138789) B1138789
theorem B1420499 : Blo 944585 1420499 := bstep (se 1 (by rfl) ⟨1065374, by rfl⟩ : syracuseStep 1420499 = 2130749) B2130749
theorem B1420529 : Blo 944585 1420529 := bstep (se 2 (by rfl) ⟨532698, by rfl⟩ : syracuseStep 1420529 = 1065397) B1065397
theorem B1420547 : Blo 944585 1420547 := bstep (se 1 (by rfl) ⟨1065410, by rfl⟩ : syracuseStep 1420547 = 2130821) B2130821
theorem B1420577 : Blo 944585 1420577 := bstep (se 2 (by rfl) ⟨532716, by rfl⟩ : syracuseStep 1420577 = 1065433) B1065433
theorem B1420595 : Blo 944585 1420595 := bstep (se 1 (by rfl) ⟨1065446, by rfl⟩ : syracuseStep 1420595 = 2130893) B2130893
theorem B1420625 : Blo 944585 1420625 := bstep (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) B1065469
theorem B1420643 : Blo 944585 1420643 := bstep (se 1 (by rfl) ⟨1065482, by rfl⟩ : syracuseStep 1420643 = 2130965) B2130965
theorem B1420673 : Blo 944585 1420673 := bstep (se 2 (by rfl) ⟨532752, by rfl⟩ : syracuseStep 1420673 = 1065505) B1065505
theorem B3190157 : Blo 944585 3190157 := bstep (se 3 (by rfl) ⟨598154, by rfl⟩ : syracuseStep 3190157 = 1196309) B1196309
theorem B1420691 : Blo 944585 1420691 := bstep (se 1 (by rfl) ⟨1065518, by rfl⟩ : syracuseStep 1420691 = 2131037) B2131037
theorem B1420721 : Blo 944585 1420721 := bstep (se 2 (by rfl) ⟨532770, by rfl⟩ : syracuseStep 1420721 = 1065541) B1065541
theorem B3190211 : Blo 944585 3190211 := bstep (se 1 (by rfl) ⟨2392658, by rfl⟩ : syracuseStep 3190211 = 4785317) B4785317
theorem B1420739 : Blo 944585 1420739 := bstep (se 1 (by rfl) ⟨1065554, by rfl⟩ : syracuseStep 1420739 = 2131109) B2131109
theorem B1420769 : Blo 944585 1420769 := bstep (se 2 (by rfl) ⟨532788, by rfl⟩ : syracuseStep 1420769 = 1065577) B1065577
theorem B7187939 : Blo 944585 7187939 := bstep (se 1 (by rfl) ⟨5390954, by rfl⟩ : syracuseStep 7187939 = 10781909) B10781909
theorem B1420787 : Blo 944585 1420787 := bstep (se 1 (by rfl) ⟨1065590, by rfl⟩ : syracuseStep 1420787 = 2131181) B2131181
theorem B1420817 : Blo 944585 1420817 := bstep (se 2 (by rfl) ⟨532806, by rfl⟩ : syracuseStep 1420817 = 1065613) B1065613
theorem B1420835 : Blo 944585 1420835 := bstep (se 1 (by rfl) ⟨1065626, by rfl⟩ : syracuseStep 1420835 = 2131253) B2131253
theorem B1420865 : Blo 944585 1420865 := bstep (se 2 (by rfl) ⟨532824, by rfl⟩ : syracuseStep 1420865 = 1065649) B1065649
theorem B1420883 : Blo 944585 1420883 := bstep (se 1 (by rfl) ⟨1065662, by rfl⟩ : syracuseStep 1420883 = 2131325) B2131325
theorem B9088625 : Blo 944585 9088625 := bstep (se 2 (by rfl) ⟨3408234, by rfl⟩ : syracuseStep 9088625 = 6816469) B6816469
theorem B1420913 : Blo 944585 1420913 := bstep (se 2 (by rfl) ⟨532842, by rfl⟩ : syracuseStep 1420913 = 1065685) B1065685
theorem B1420931 : Blo 944585 1420931 := bstep (se 1 (by rfl) ⟨1065698, by rfl⟩ : syracuseStep 1420931 = 2131397) B2131397
theorem B1420961 : Blo 944585 1420961 := bstep (se 2 (by rfl) ⟨532860, by rfl⟩ : syracuseStep 1420961 = 1065721) B1065721
theorem B1420979 : Blo 944585 1420979 := bstep (se 1 (by rfl) ⟨1065734, by rfl⟩ : syracuseStep 1420979 = 2131469) B2131469
theorem B3190481 : Blo 944585 3190481 := bstep (se 2 (by rfl) ⟨1196430, by rfl⟩ : syracuseStep 3190481 = 2392861) B2392861
theorem B1421009 : Blo 944585 1421009 := bstep (se 2 (by rfl) ⟨532878, by rfl⟩ : syracuseStep 1421009 = 1065757) B1065757
theorem B1421027 : Blo 944585 1421027 := bstep (se 1 (by rfl) ⟨1065770, by rfl⟩ : syracuseStep 1421027 = 2131541) B2131541
theorem B1421057 : Blo 944585 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B2699021 : Blo 944585 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B1421075 : Blo 944585 1421075 := bstep (se 1 (by rfl) ⟨1065806, by rfl⟩ : syracuseStep 1421075 = 2131613) B2131613
theorem B1421105 : Blo 944585 1421105 := bstep (se 2 (by rfl) ⟨532914, by rfl⟩ : syracuseStep 1421105 = 1065829) B1065829
theorem B1421123 : Blo 944585 1421123 := bstep (se 1 (by rfl) ⟨1065842, by rfl⟩ : syracuseStep 1421123 = 2131685) B2131685
theorem B1421153 : Blo 944585 1421153 := bstep (se 2 (by rfl) ⟨532932, by rfl⟩ : syracuseStep 1421153 = 1065865) B1065865
theorem B3026801 : Blo 944585 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B1421171 : Blo 944585 1421171 := bstep (se 1 (by rfl) ⟨1065878, by rfl⟩ : syracuseStep 1421171 = 2131757) B2131757
theorem B1421201 : Blo 944585 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B1421219 : Blo 944585 1421219 := bstep (se 1 (by rfl) ⟨1065914, by rfl⟩ : syracuseStep 1421219 = 2131829) B2131829
theorem B1421249 : Blo 944585 1421249 := bstep (se 2 (by rfl) ⟨532968, by rfl⟩ : syracuseStep 1421249 = 1065937) B1065937
theorem B2699203 : Blo 944585 2699203 := bstep (se 1 (by rfl) ⟨2024402, by rfl⟩ : syracuseStep 2699203 = 4048805) B4048805
theorem B2273233 : Blo 944585 2273233 := bstep (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) B1704925
theorem B1421267 : Blo 944585 1421267 := bstep (se 1 (by rfl) ⟨1065950, by rfl⟩ : syracuseStep 1421267 = 2131901) B2131901
theorem B3026929 : Blo 944585 3026929 := bstep (se 2 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 3026929 = 2270197) B2270197
theorem B1421297 : Blo 944585 1421297 := bstep (se 2 (by rfl) ⟨532986, by rfl⟩ : syracuseStep 1421297 = 1065973) B1065973
theorem B1421315 : Blo 944585 1421315 := bstep (se 1 (by rfl) ⟨1065986, by rfl⟩ : syracuseStep 1421315 = 2131973) B2131973
theorem B1421345 : Blo 944585 1421345 := bstep (se 2 (by rfl) ⟨533004, by rfl⟩ : syracuseStep 1421345 = 1066009) B1066009
theorem B1421363 : Blo 944585 1421363 := bstep (se 1 (by rfl) ⟨1066022, by rfl⟩ : syracuseStep 1421363 = 2132045) B2132045
theorem B1421393 : Blo 944585 1421393 := bstep (se 2 (by rfl) ⟨533022, by rfl⟩ : syracuseStep 1421393 = 1066045) B1066045
theorem B1421411 : Blo 944585 1421411 := bstep (se 1 (by rfl) ⟨1066058, by rfl⟩ : syracuseStep 1421411 = 2132117) B2132117
theorem B1421441 : Blo 944585 1421441 := bstep (se 2 (by rfl) ⟨533040, by rfl⟩ : syracuseStep 1421441 = 1066081) B1066081
theorem B1618067 : Blo 944585 1618067 := bstep (se 1 (by rfl) ⟨1213550, by rfl⟩ : syracuseStep 1618067 = 2427101) B2427101
theorem B1421459 : Blo 944585 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B1421489 : Blo 944585 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B1421507 : Blo 944585 1421507 := bstep (se 1 (by rfl) ⟨1066130, by rfl⟩ : syracuseStep 1421507 = 2132261) B2132261
theorem B5386445 : Blo 944585 5386445 := bstep (se 3 (by rfl) ⟨1009958, by rfl⟩ : syracuseStep 5386445 = 2019917) B2019917
theorem B1421537 : Blo 944585 1421537 := bstep (se 2 (by rfl) ⟨533076, by rfl⟩ : syracuseStep 1421537 = 1066153) B1066153
theorem B4042979 : Blo 944585 4042979 := bstep (se 1 (by rfl) ⟨3032234, by rfl⟩ : syracuseStep 4042979 = 6064469) B6064469
theorem B3191021 : Blo 944585 3191021 := bstep (se 3 (by rfl) ⟨598316, by rfl⟩ : syracuseStep 3191021 = 1196633) B1196633
theorem B3027185 : Blo 944585 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B4796657 : Blo 944585 4796657 := bstep (se 2 (by rfl) ⟨1798746, by rfl⟩ : syracuseStep 4796657 = 3597493) B3597493
theorem B1421555 : Blo 944585 1421555 := bstep (se 1 (by rfl) ⟨1066166, by rfl⟩ : syracuseStep 1421555 = 2132333) B2132333
theorem B1421585 : Blo 944585 1421585 := bstep (se 2 (by rfl) ⟨533094, by rfl⟩ : syracuseStep 1421585 = 1066189) B1066189
theorem B3191075 : Blo 944585 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B1421603 : Blo 944585 1421603 := bstep (se 1 (by rfl) ⟨1066202, by rfl⟩ : syracuseStep 1421603 = 2132405) B2132405
theorem B2076977 : Blo 944585 2076977 := bstep (se 2 (by rfl) ⟨778866, by rfl⟩ : syracuseStep 2076977 = 1557733) B1557733
theorem B1421633 : Blo 944585 1421633 := bstep (se 2 (by rfl) ⟨533112, by rfl⟩ : syracuseStep 1421633 = 1066225) B1066225
theorem B1421651 : Blo 944585 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B1421681 : Blo 944585 1421681 := bstep (se 2 (by rfl) ⟨533130, by rfl⟩ : syracuseStep 1421681 = 1066261) B1066261
theorem B1421699 : Blo 944585 1421699 := bstep (se 1 (by rfl) ⟨1066274, by rfl⟩ : syracuseStep 1421699 = 2132549) B2132549
theorem B1421729 : Blo 944585 1421729 := bstep (se 2 (by rfl) ⟨533148, by rfl⟩ : syracuseStep 1421729 = 1066297) B1066297
theorem B2699693 : Blo 944585 2699693 := bstep (se 3 (by rfl) ⟨506192, by rfl⟩ : syracuseStep 2699693 = 1012385) B1012385
theorem B1421747 : Blo 944585 1421747 := bstep (se 1 (by rfl) ⟨1066310, by rfl⟩ : syracuseStep 1421747 = 2132621) B2132621
theorem B13152709 : Blo 944585 13152709 := bstep (se 4 (by rfl) ⟨1233066, by rfl⟩ : syracuseStep 13152709 = 2466133) B2466133
theorem B1421777 : Blo 944585 1421777 := bstep (se 2 (by rfl) ⟨533166, by rfl⟩ : syracuseStep 1421777 = 1066333) B1066333
theorem B1421795 : Blo 944585 1421795 := bstep (se 1 (by rfl) ⟨1066346, by rfl⟩ : syracuseStep 1421795 = 2132693) B2132693
theorem B1421825 : Blo 944585 1421825 := bstep (se 2 (by rfl) ⟨533184, by rfl⟩ : syracuseStep 1421825 = 1066369) B1066369
theorem B1421843 : Blo 944585 1421843 := bstep (se 1 (by rfl) ⟨1066382, by rfl⟩ : syracuseStep 1421843 = 2132765) B2132765
theorem B3191345 : Blo 944585 3191345 := bstep (se 2 (by rfl) ⟨1196754, by rfl⟩ : syracuseStep 3191345 = 2393509) B2393509
theorem B1421873 : Blo 944585 1421873 := bstep (se 2 (by rfl) ⟨533202, by rfl⟩ : syracuseStep 1421873 = 1066405) B1066405
theorem B1421891 : Blo 944585 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B1421921 : Blo 944585 1421921 := bstep (se 2 (by rfl) ⟨533220, by rfl⟩ : syracuseStep 1421921 = 1066441) B1066441
theorem B1421939 : Blo 944585 1421939 := bstep (se 1 (by rfl) ⟨1066454, by rfl⟩ : syracuseStep 1421939 = 2132909) B2132909
theorem B1421969 : Blo 944585 1421969 := bstep (se 2 (by rfl) ⟨533238, by rfl⟩ : syracuseStep 1421969 = 1066477) B1066477
theorem B1421987 : Blo 944585 1421987 := bstep (se 1 (by rfl) ⟨1066490, by rfl⟩ : syracuseStep 1421987 = 2132981) B2132981
theorem B1422017 : Blo 944585 1422017 := bstep (se 2 (by rfl) ⟨533256, by rfl⟩ : syracuseStep 1422017 = 1066513) B1066513
theorem B1422035 : Blo 944585 1422035 := bstep (se 1 (by rfl) ⟨1066526, by rfl⟩ : syracuseStep 1422035 = 2133053) B2133053
theorem B1422065 : Blo 944585 1422065 := bstep (se 2 (by rfl) ⟨533274, by rfl⟩ : syracuseStep 1422065 = 1066549) B1066549
theorem B1422083 : Blo 944585 1422083 := bstep (se 1 (by rfl) ⟨1066562, by rfl⟩ : syracuseStep 1422083 = 2133125) B2133125
theorem B1422113 : Blo 944585 1422113 := bstep (se 2 (by rfl) ⟨533292, by rfl⟩ : syracuseStep 1422113 = 1066585) B1066585
theorem B1422131 : Blo 944585 1422131 := bstep (se 1 (by rfl) ⟨1066598, by rfl⟩ : syracuseStep 1422131 = 2133197) B2133197
theorem B1422161 : Blo 944585 1422161 := bstep (se 2 (by rfl) ⟨533310, by rfl⟩ : syracuseStep 1422161 = 1066621) B1066621
theorem B1618787 : Blo 944585 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B1422179 : Blo 944585 1422179 := bstep (se 1 (by rfl) ⟨1066634, by rfl⟩ : syracuseStep 1422179 = 2133269) B2133269
theorem B1422209 : Blo 944585 1422209 := bstep (se 2 (by rfl) ⟨533328, by rfl⟩ : syracuseStep 1422209 = 1066657) B1066657
theorem B1422227 : Blo 944585 1422227 := bstep (se 1 (by rfl) ⟨1066670, by rfl⟩ : syracuseStep 1422227 = 2133341) B2133341
theorem B1422257 : Blo 944585 1422257 := bstep (se 2 (by rfl) ⟨533346, by rfl⟩ : syracuseStep 1422257 = 1066693) B1066693
theorem B1422275 : Blo 944585 1422275 := bstep (se 1 (by rfl) ⟨1066706, by rfl⟩ : syracuseStep 1422275 = 2133413) B2133413
theorem B1422305 : Blo 944585 1422305 := bstep (se 2 (by rfl) ⟨533364, by rfl⟩ : syracuseStep 1422305 = 1066729) B1066729
theorem B1422323 : Blo 944585 1422323 := bstep (se 1 (by rfl) ⟨1066742, by rfl⟩ : syracuseStep 1422323 = 2133485) B2133485
theorem B1422353 : Blo 944585 1422353 := bstep (se 2 (by rfl) ⟨533382, by rfl⟩ : syracuseStep 1422353 = 1066765) B1066765
theorem B1422371 : Blo 944585 1422371 := bstep (se 1 (by rfl) ⟨1066778, by rfl⟩ : syracuseStep 1422371 = 2133557) B2133557
theorem B1422401 : Blo 944585 1422401 := bstep (se 2 (by rfl) ⟨533400, by rfl⟩ : syracuseStep 1422401 = 1066801) B1066801
theorem B3191885 : Blo 944585 3191885 := bstep (se 3 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 3191885 = 1196957) B1196957
theorem B1422419 : Blo 944585 1422419 := bstep (se 1 (by rfl) ⟨1066814, by rfl⟩ : syracuseStep 1422419 = 2133629) B2133629
theorem B1422449 : Blo 944585 1422449 := bstep (se 2 (by rfl) ⟨533418, by rfl⟩ : syracuseStep 1422449 = 1066837) B1066837
theorem B3191939 : Blo 944585 3191939 := bstep (se 1 (by rfl) ⟨2393954, by rfl⟩ : syracuseStep 3191939 = 4787909) B4787909
theorem B1422467 : Blo 944585 1422467 := bstep (se 1 (by rfl) ⟨1066850, by rfl⟩ : syracuseStep 1422467 = 2133701) B2133701
theorem B1422497 : Blo 944585 1422497 := bstep (se 2 (by rfl) ⟨533436, by rfl⟩ : syracuseStep 1422497 = 1066873) B1066873
theorem B1422515 : Blo 944585 1422515 := bstep (se 1 (by rfl) ⟨1066886, by rfl⟩ : syracuseStep 1422515 = 2133773) B2133773
theorem B1422545 : Blo 944585 1422545 := bstep (se 2 (by rfl) ⟨533454, by rfl⟩ : syracuseStep 1422545 = 1066909) B1066909
theorem B1422563 : Blo 944585 1422563 := bstep (se 1 (by rfl) ⟨1066922, by rfl⟩ : syracuseStep 1422563 = 2133845) B2133845
theorem B1422593 : Blo 944585 1422593 := bstep (se 2 (by rfl) ⟨533472, by rfl⟩ : syracuseStep 1422593 = 1066945) B1066945
theorem B1422611 : Blo 944585 1422611 := bstep (se 1 (by rfl) ⟨1066958, by rfl⟩ : syracuseStep 1422611 = 2133917) B2133917
theorem B51754261 : Blo 944585 51754261 := bstep (se 6 (by rfl) ⟨1212990, by rfl⟩ : syracuseStep 51754261 = 2425981) B2425981
theorem B1422641 : Blo 944585 1422641 := bstep (se 2 (by rfl) ⟨533490, by rfl⟩ : syracuseStep 1422641 = 1066981) B1066981
theorem B1422659 : Blo 944585 1422659 := bstep (se 1 (by rfl) ⟨1066994, by rfl⟩ : syracuseStep 1422659 = 2133989) B2133989
theorem B1422689 : Blo 944585 1422689 := bstep (se 2 (by rfl) ⟨533508, by rfl⟩ : syracuseStep 1422689 = 1067017) B1067017
theorem B1422707 : Blo 944585 1422707 := bstep (se 1 (by rfl) ⟨1067030, by rfl⟩ : syracuseStep 1422707 = 2134061) B2134061
theorem B3192209 : Blo 944585 3192209 := bstep (se 2 (by rfl) ⟨1197078, by rfl⟩ : syracuseStep 3192209 = 2394157) B2394157
theorem B1422737 : Blo 944585 1422737 := bstep (se 2 (by rfl) ⟨533526, by rfl⟩ : syracuseStep 1422737 = 1067053) B1067053
theorem B1422755 : Blo 944585 1422755 := bstep (se 1 (by rfl) ⟨1067066, by rfl⟩ : syracuseStep 1422755 = 2134133) B2134133
theorem B1422785 : Blo 944585 1422785 := bstep (se 2 (by rfl) ⟨533544, by rfl⟩ : syracuseStep 1422785 = 1067089) B1067089
theorem B1422803 : Blo 944585 1422803 := bstep (se 1 (by rfl) ⟨1067102, by rfl⟩ : syracuseStep 1422803 = 2134205) B2134205
theorem B1422833 : Blo 944585 1422833 := bstep (se 2 (by rfl) ⟨533562, by rfl⟩ : syracuseStep 1422833 = 1067125) B1067125
theorem B1422851 : Blo 944585 1422851 := bstep (se 1 (by rfl) ⟨1067138, by rfl⟩ : syracuseStep 1422851 = 2134277) B2134277
theorem B9090629 : Blo 944585 9090629 := bstep (se 4 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 9090629 = 1704493) B1704493
theorem B2700877 : Blo 944585 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B4798115 : Blo 944585 4798115 := bstep (se 1 (by rfl) ⟨3598586, by rfl⟩ : syracuseStep 4798115 = 7197173) B7197173
theorem B1062787 : Blo 944585 1062787 := bstep (se 1 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 1062787 = 1594181) B1594181
theorem B3028877 : Blo 944585 3028877 := bstep (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) B1135829
theorem B3192749 : Blo 944585 3192749 := bstep (se 3 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 3192749 = 1197281) B1197281
theorem B3192803 : Blo 944585 3192803 := bstep (se 1 (by rfl) ⟨2394602, by rfl⟩ : syracuseStep 3192803 = 4789205) B4789205
theorem B1062931 : Blo 944585 1062931 := bstep (se 1 (by rfl) ⟨797198, by rfl⟩ : syracuseStep 1062931 = 1594397) B1594397
theorem B1063075 : Blo 944585 1063075 := bstep (se 1 (by rfl) ⟨797306, by rfl⟩ : syracuseStep 1063075 = 1594613) B1594613
theorem B3193073 : Blo 944585 3193073 := bstep (se 2 (by rfl) ⟨1197402, by rfl⟩ : syracuseStep 3193073 = 2394805) B2394805
theorem B1063219 : Blo 944585 1063219 := bstep (se 1 (by rfl) ⟨797414, by rfl⟩ : syracuseStep 1063219 = 1594829) B1594829
theorem B5749061 : Blo 944585 5749061 := bstep (se 4 (by rfl) ⟨538974, by rfl⟩ : syracuseStep 5749061 = 1077949) B1077949
theorem B5388677 : Blo 944585 5388677 := bstep (se 4 (by rfl) ⟨505188, by rfl⟩ : syracuseStep 5388677 = 1010377) B1010377
theorem B1063363 : Blo 944585 1063363 := bstep (se 1 (by rfl) ⟨797522, by rfl⟩ : syracuseStep 1063363 = 1595045) B1595045
theorem B4798925 : Blo 944585 4798925 := bstep (se 3 (by rfl) ⟨899798, by rfl⟩ : syracuseStep 4798925 = 1799597) B1799597
theorem B1063507 : Blo 944585 1063507 := bstep (se 1 (by rfl) ⟨797630, by rfl⟩ : syracuseStep 1063507 = 1595261) B1595261
theorem B3029645 : Blo 944585 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B6077105 : Blo 944585 6077105 := bstep (se 2 (by rfl) ⟨2278914, by rfl⟩ : syracuseStep 6077105 = 4557829) B4557829
theorem B5454533 : Blo 944585 5454533 := bstep (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) B1022725
theorem B3586787 : Blo 944585 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B1063651 : Blo 944585 1063651 := bstep (se 1 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 1063651 = 1595477) B1595477
theorem B3586801 : Blo 944585 3586801 := bstep (se 2 (by rfl) ⟨1345050, by rfl⟩ : syracuseStep 3586801 = 2690101) B2690101
theorem B1915633 : Blo 944585 1915633 := bstep (se 2 (by rfl) ⟨718362, by rfl⟩ : syracuseStep 1915633 = 1436725) B1436725
theorem B3193613 : Blo 944585 3193613 := bstep (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) B1197605
theorem B3193667 : Blo 944585 3193667 := bstep (se 1 (by rfl) ⟨2395250, by rfl⟩ : syracuseStep 3193667 = 4790501) B4790501
theorem B1063795 : Blo 944585 1063795 := bstep (se 1 (by rfl) ⟨797846, by rfl⟩ : syracuseStep 1063795 = 1595693) B1595693
theorem B1063939 : Blo 944585 1063939 := bstep (se 1 (by rfl) ⟨797954, by rfl⟩ : syracuseStep 1063939 = 1595909) B1595909
theorem B2276387 : Blo 944585 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B5389361 : Blo 944585 5389361 := bstep (se 2 (by rfl) ⟨2021010, by rfl⟩ : syracuseStep 5389361 = 4042021) B4042021
theorem B3193937 : Blo 944585 3193937 := bstep (se 2 (by rfl) ⟨1197726, by rfl⟩ : syracuseStep 3193937 = 2395453) B2395453
theorem B3030157 : Blo 944585 3030157 := bstep (se 3 (by rfl) ⟨568154, by rfl⟩ : syracuseStep 3030157 = 1136309) B1136309
theorem B1064083 : Blo 944585 1064083 := bstep (se 1 (by rfl) ⟨798062, by rfl⟩ : syracuseStep 1064083 = 1596125) B1596125
theorem B2276579 : Blo 944585 2276579 := bstep (se 1 (by rfl) ⟨1707434, by rfl⟩ : syracuseStep 2276579 = 3414869) B3414869
theorem B1064227 : Blo 944585 1064227 := bstep (se 1 (by rfl) ⟨798170, by rfl⟩ : syracuseStep 1064227 = 1596341) B1596341
theorem B1064371 : Blo 944585 1064371 := bstep (se 1 (by rfl) ⟨798278, by rfl⟩ : syracuseStep 1064371 = 1596557) B1596557
theorem B1195555 : Blo 944585 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B1064515 : Blo 944585 1064515 := bstep (se 1 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 1064515 = 1596773) B1596773
theorem B3194477 : Blo 944585 3194477 := bstep (se 3 (by rfl) ⟨598964, by rfl⟩ : syracuseStep 3194477 = 1197929) B1197929
theorem B13647473 : Blo 944585 13647473 := bstep (se 2 (by rfl) ⟨5117802, by rfl⟩ : syracuseStep 13647473 = 10235605) B10235605
theorem B1195651 : Blo 944585 1195651 := bstep (se 1 (by rfl) ⟨896738, by rfl⟩ : syracuseStep 1195651 = 1793477) B1793477
theorem B3030659 : Blo 944585 3030659 := bstep (se 1 (by rfl) ⟨2272994, by rfl⟩ : syracuseStep 3030659 = 4545989) B4545989
theorem B3194531 : Blo 944585 3194531 := bstep (se 1 (by rfl) ⟨2395898, by rfl⟩ : syracuseStep 3194531 = 4791797) B4791797
theorem B1064659 : Blo 944585 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B2277155 : Blo 944585 2277155 := bstep (se 1 (by rfl) ⟨1707866, by rfl⟩ : syracuseStep 2277155 = 3415733) B3415733
theorem B4046669 : Blo 944585 4046669 := bstep (se 3 (by rfl) ⟨758750, by rfl⟩ : syracuseStep 4046669 = 1517501) B1517501
theorem B1064803 : Blo 944585 1064803 := bstep (se 1 (by rfl) ⟨798602, by rfl⟩ : syracuseStep 1064803 = 1597205) B1597205
theorem B3194801 : Blo 944585 3194801 := bstep (se 2 (by rfl) ⟨1198050, by rfl⟩ : syracuseStep 3194801 = 2396101) B2396101
theorem B1064947 : Blo 944585 1064947 := bstep (se 1 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 1064947 = 1597421) B1597421
theorem B1196147 : Blo 944585 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1065091 : Blo 944585 1065091 := bstep (se 1 (by rfl) ⟨798818, by rfl⟩ : syracuseStep 1065091 = 1597637) B1597637
theorem B3588259 : Blo 944585 3588259 := bstep (se 1 (by rfl) ⟨2691194, by rfl⟩ : syracuseStep 3588259 = 5382389) B5382389
theorem B2277539 : Blo 944585 2277539 := bstep (se 1 (by rfl) ⟨1708154, by rfl⟩ : syracuseStep 2277539 = 3416309) B3416309
theorem B1065235 : Blo 944585 1065235 := bstep (se 1 (by rfl) ⟨798926, by rfl⟩ : syracuseStep 1065235 = 1597853) B1597853
theorem B13844789 : Blo 944585 13844789 := bstep (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) B1297949
theorem B1622371 : Blo 944585 1622371 := bstep (se 1 (by rfl) ⟨1216778, by rfl⟩ : syracuseStep 1622371 = 2433557) B2433557
theorem B1065379 : Blo 944585 1065379 := bstep (se 1 (by rfl) ⟨799034, by rfl⟩ : syracuseStep 1065379 = 1598069) B1598069
theorem B1917361 : Blo 944585 1917361 := bstep (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) B1438021
theorem B3195341 : Blo 944585 3195341 := bstep (se 3 (by rfl) ⟨599126, by rfl⟩ : syracuseStep 3195341 = 1198253) B1198253
theorem B2048465 : Blo 944585 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B5390819 : Blo 944585 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B3195395 : Blo 944585 3195395 := bstep (se 1 (by rfl) ⟨2396546, by rfl⟩ : syracuseStep 3195395 = 4793093) B4793093
theorem B1065523 : Blo 944585 1065523 := bstep (se 1 (by rfl) ⟨799142, by rfl⟩ : syracuseStep 1065523 = 1598285) B1598285
theorem B1065667 : Blo 944585 1065667 := bstep (se 1 (by rfl) ⟨799250, by rfl⟩ : syracuseStep 1065667 = 1598501) B1598501
theorem B7193285 : Blo 944585 7193285 := bstep (se 4 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 7193285 = 1348741) B1348741
theorem B1819409 : Blo 944585 1819409 := bstep (se 2 (by rfl) ⟨682278, by rfl⟩ : syracuseStep 1819409 = 1364557) B1364557
theorem B3195665 : Blo 944585 3195665 := bstep (se 2 (by rfl) ⟨1198374, by rfl⟩ : syracuseStep 3195665 = 2396749) B2396749
theorem B1196851 : Blo 944585 1196851 := bstep (se 1 (by rfl) ⟨897638, by rfl⟩ : syracuseStep 1196851 = 1795277) B1795277
theorem B1065811 : Blo 944585 1065811 := bstep (se 1 (by rfl) ⟨799358, by rfl⟩ : syracuseStep 1065811 = 1598717) B1598717
theorem B1196947 : Blo 944585 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B4309937 : Blo 944585 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B1065955 : Blo 944585 1065955 := bstep (se 1 (by rfl) ⟨799466, by rfl⟩ : syracuseStep 1065955 = 1598933) B1598933
theorem B2278385 : Blo 944585 2278385 := bstep (se 2 (by rfl) ⟨854394, by rfl⟩ : syracuseStep 2278385 = 1708789) B1708789
theorem B1066099 : Blo 944585 1066099 := bstep (se 1 (by rfl) ⟨799574, by rfl⟩ : syracuseStep 1066099 = 1599149) B1599149
theorem B2278577 : Blo 944585 2278577 := bstep (se 2 (by rfl) ⟨854466, by rfl⟩ : syracuseStep 2278577 = 1708933) B1708933
theorem B1066243 : Blo 944585 1066243 := bstep (se 1 (by rfl) ⟨799682, by rfl⟩ : syracuseStep 1066243 = 1599365) B1599365
theorem B3196205 : Blo 944585 3196205 := bstep (se 3 (by rfl) ⟨599288, by rfl⟩ : syracuseStep 3196205 = 1198577) B1198577
theorem B4801841 : Blo 944585 4801841 := bstep (se 2 (by rfl) ⟨1800690, by rfl⟩ : syracuseStep 4801841 = 3601381) B3601381
theorem B3196259 : Blo 944585 3196259 := bstep (se 1 (by rfl) ⟨2397194, by rfl⟩ : syracuseStep 3196259 = 4794389) B4794389
theorem B1197443 : Blo 944585 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B1066387 : Blo 944585 1066387 := bstep (se 1 (by rfl) ⟨799790, by rfl⟩ : syracuseStep 1066387 = 1599581) B1599581
theorem B3032515 : Blo 944585 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B7489037 : Blo 944585 7489037 := bstep (se 3 (by rfl) ⟨1404194, by rfl⟩ : syracuseStep 7489037 = 2808389) B2808389
theorem B1066531 : Blo 944585 1066531 := bstep (se 1 (by rfl) ⟨799898, by rfl⟩ : syracuseStep 1066531 = 1599797) B1599797
theorem B3196529 : Blo 944585 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B1066675 : Blo 944585 1066675 := bstep (se 1 (by rfl) ⟨800006, by rfl⟩ : syracuseStep 1066675 = 1600013) B1600013
theorem B1066819 : Blo 944585 1066819 := bstep (se 1 (by rfl) ⟨800114, by rfl⟩ : syracuseStep 1066819 = 1600229) B1600229
theorem B1296227 : Blo 944585 1296227 := bstep (se 1 (by rfl) ⟨972170, by rfl⟩ : syracuseStep 1296227 = 1944341) B1944341
theorem B3032977 : Blo 944585 3032977 := bstep (se 2 (by rfl) ⟨1137366, by rfl⟩ : syracuseStep 3032977 = 2274733) B2274733
theorem B1066963 : Blo 944585 1066963 := bstep (se 1 (by rfl) ⟨800222, by rfl⟩ : syracuseStep 1066963 = 1600445) B1600445
theorem B9717731 : Blo 944585 9717731 := bstep (se 1 (by rfl) ⟨7288298, by rfl⟩ : syracuseStep 9717731 = 14576597) B14576597
theorem B1198147 : Blo 944585 1198147 := bstep (se 1 (by rfl) ⟨898610, by rfl⟩ : syracuseStep 1198147 = 1797221) B1797221
theorem B1067107 : Blo 944585 1067107 := bstep (se 1 (by rfl) ⟨800330, by rfl⟩ : syracuseStep 1067107 = 1600661) B1600661
theorem B8407153 : Blo 944585 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B3197069 : Blo 944585 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B1198243 : Blo 944585 1198243 := bstep (se 1 (by rfl) ⟨898682, by rfl⟩ : syracuseStep 1198243 = 1797365) B1797365
theorem B2017457 : Blo 944585 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B3197123 : Blo 944585 3197123 := bstep (se 1 (by rfl) ⟨2397842, by rfl⟩ : syracuseStep 3197123 = 4795685) B4795685
theorem B3590477 : Blo 944585 3590477 := bstep (se 3 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 3590477 = 1346429) B1346429
theorem B3197393 : Blo 944585 3197393 := bstep (se 2 (by rfl) ⟨1199022, by rfl⟩ : syracuseStep 3197393 = 2398045) B2398045
theorem B1198739 : Blo 944585 1198739 := bstep (se 1 (by rfl) ⟨899054, by rfl⟩ : syracuseStep 1198739 = 1798109) B1798109
theorem B8637283 : Blo 944585 8637283 := bstep (se 1 (by rfl) ⟨6477962, by rfl⟩ : syracuseStep 8637283 = 12955925) B12955925
theorem B4049777 : Blo 944585 4049777 := bstep (se 2 (by rfl) ⟨1518666, by rfl⟩ : syracuseStep 4049777 = 3037333) B3037333
theorem B1919875 : Blo 944585 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B10243043 : Blo 944585 10243043 := bstep (se 1 (by rfl) ⟨7682282, by rfl⟩ : syracuseStep 10243043 = 15364565) B15364565
theorem B3197933 : Blo 944585 3197933 := bstep (se 3 (by rfl) ⟨599612, by rfl⟩ : syracuseStep 3197933 = 1199225) B1199225
theorem B3197987 : Blo 944585 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B3198257 : Blo 944585 3198257 := bstep (se 2 (by rfl) ⟨1199346, by rfl⟩ : syracuseStep 3198257 = 2398693) B2398693
theorem B1199443 : Blo 944585 1199443 := bstep (se 1 (by rfl) ⟨899582, by rfl⟩ : syracuseStep 1199443 = 1799165) B1799165
theorem B3460465 : Blo 944585 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B1199539 : Blo 944585 1199539 := bstep (se 1 (by rfl) ⟨899654, by rfl⟩ : syracuseStep 1199539 = 1799309) B1799309
theorem B1822211 : Blo 944585 1822211 := bstep (se 1 (by rfl) ⟨1366658, by rfl⟩ : syracuseStep 1822211 = 2733317) B2733317
theorem B4050445 : Blo 944585 4050445 := bstep (se 3 (by rfl) ⟨759458, by rfl⟩ : syracuseStep 4050445 = 1518917) B1518917
theorem B5394053 : Blo 944585 5394053 := bstep (se 4 (by rfl) ⟨505692, by rfl⟩ : syracuseStep 5394053 = 1011385) B1011385
theorem B1461907 : Blo 944585 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B2019011 : Blo 944585 2019011 := bstep (se 1 (by rfl) ⟨1514258, by rfl⟩ : syracuseStep 2019011 = 3028517) B3028517
theorem B3690211 : Blo 944585 3690211 := bstep (se 1 (by rfl) ⟨2767658, by rfl⟩ : syracuseStep 3690211 = 5535317) B5535317
theorem B3198797 : Blo 944585 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B3198851 : Blo 944585 3198851 := bstep (se 1 (by rfl) ⟨2399138, by rfl⟩ : syracuseStep 3198851 = 4798277) B4798277
theorem B1200035 : Blo 944585 1200035 := bstep (se 1 (by rfl) ⟨900026, by rfl⟩ : syracuseStep 1200035 = 1800053) B1800053
theorem B1920977 : Blo 944585 1920977 := bstep (se 2 (by rfl) ⟨720366, by rfl⟩ : syracuseStep 1920977 = 1440733) B1440733
theorem B5394509 : Blo 944585 5394509 := bstep (se 3 (by rfl) ⟨1011470, by rfl⟩ : syracuseStep 5394509 = 2022941) B2022941
theorem B4051043 : Blo 944585 4051043 := bstep (se 1 (by rfl) ⟨3038282, by rfl⟩ : syracuseStep 4051043 = 6076565) B6076565
theorem B4542605 : Blo 944585 4542605 := bstep (se 3 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 4542605 = 1703477) B1703477
theorem B3199121 : Blo 944585 3199121 := bstep (se 2 (by rfl) ⟨1199670, by rfl⟩ : syracuseStep 3199121 = 2399341) B2399341
theorem B3068077 : Blo 944585 3068077 := bstep (se 3 (by rfl) ⟨575264, by rfl⟩ : syracuseStep 3068077 = 1150529) B1150529
theorem B3035693 : Blo 944585 3035693 := bstep (se 3 (by rfl) ⟨569192, by rfl⟩ : syracuseStep 3035693 = 1138385) B1138385
theorem B1594019 : Blo 944585 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B3199661 : Blo 944585 3199661 := bstep (se 3 (by rfl) ⟨599936, by rfl⟩ : syracuseStep 3199661 = 1199873) B1199873
theorem B3199715 : Blo 944585 3199715 := bstep (se 1 (by rfl) ⟨2399786, by rfl⟩ : syracuseStep 3199715 = 4799573) B4799573
theorem B1594147 : Blo 944585 1594147 := bstep (se 1 (by rfl) ⟨1195610, by rfl⟩ : syracuseStep 1594147 = 2391221) B2391221
theorem B1594289 : Blo 944585 1594289 := bstep (se 2 (by rfl) ⟨597858, by rfl⟩ : syracuseStep 1594289 = 1195717) B1195717
theorem B3199985 : Blo 944585 3199985 := bstep (se 2 (by rfl) ⟨1199994, by rfl⟩ : syracuseStep 3199985 = 2399989) B2399989
theorem B1594417 : Blo 944585 1594417 := bstep (se 2 (by rfl) ⟨597906, by rfl⟩ : syracuseStep 1594417 = 1195813) B1195813
theorem B1594451 : Blo 944585 1594451 := bstep (se 1 (by rfl) ⟨1195838, by rfl⟩ : syracuseStep 1594451 = 2391677) B2391677
theorem B3593393 : Blo 944585 3593393 := bstep (se 2 (by rfl) ⟨1347522, by rfl⟩ : syracuseStep 3593393 = 2695045) B2695045
theorem B1594579 : Blo 944585 1594579 := bstep (se 1 (by rfl) ⟨1195934, by rfl⟩ : syracuseStep 1594579 = 2391869) B2391869
theorem B4150499 : Blo 944585 4150499 := bstep (se 1 (by rfl) ⟨3112874, by rfl⟩ : syracuseStep 4150499 = 6225749) B6225749
theorem B1594721 : Blo 944585 1594721 := bstep (se 2 (by rfl) ⟨598020, by rfl⟩ : syracuseStep 1594721 = 1196041) B1196041
theorem B8639941 : Blo 944585 8639941 := bstep (se 4 (by rfl) ⟨809994, by rfl⟩ : syracuseStep 8639941 = 1619989) B1619989
theorem B1594849 : Blo 944585 1594849 := bstep (se 2 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 1594849 = 1196137) B1196137
theorem B1594883 : Blo 944585 1594883 := bstep (se 1 (by rfl) ⟨1196162, by rfl⟩ : syracuseStep 1594883 = 2392325) B2392325
theorem B3200525 : Blo 944585 3200525 := bstep (se 3 (by rfl) ⟨600098, by rfl⟩ : syracuseStep 3200525 = 1200197) B1200197
theorem B3200579 : Blo 944585 3200579 := bstep (se 1 (by rfl) ⟨2400434, by rfl⟩ : syracuseStep 3200579 = 4800869) B4800869
theorem B1595011 : Blo 944585 1595011 := bstep (se 1 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 1595011 = 2392517) B2392517
theorem B1595153 : Blo 944585 1595153 := bstep (se 2 (by rfl) ⟨598182, by rfl⟩ : syracuseStep 1595153 = 1196365) B1196365
theorem B10770245 : Blo 944585 10770245 := bstep (se 4 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 10770245 = 2019421) B2019421
theorem B3200849 : Blo 944585 3200849 := bstep (se 2 (by rfl) ⟨1200318, by rfl⟩ : syracuseStep 3200849 = 2400637) B2400637
theorem B2021233 : Blo 944585 2021233 := bstep (se 2 (by rfl) ⟨757962, by rfl⟩ : syracuseStep 2021233 = 1515925) B1515925
theorem B22763405 : Blo 944585 22763405 := bstep (se 3 (by rfl) ⟨4268138, by rfl⟩ : syracuseStep 22763405 = 8536277) B8536277
theorem B1595281 : Blo 944585 1595281 := bstep (se 2 (by rfl) ⟨598230, by rfl⟩ : syracuseStep 1595281 = 1196461) B1196461
theorem B1595315 : Blo 944585 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1595443 : Blo 944585 1595443 := bstep (se 1 (by rfl) ⟨1196582, by rfl⟩ : syracuseStep 1595443 = 2393165) B2393165
theorem B3037283 : Blo 944585 3037283 := bstep (se 1 (by rfl) ⟨2277962, by rfl⟩ : syracuseStep 3037283 = 4555925) B4555925
theorem B11491469 : Blo 944585 11491469 := bstep (se 3 (by rfl) ⟨2154650, by rfl⟩ : syracuseStep 11491469 = 4309301) B4309301
theorem B1595585 : Blo 944585 1595585 := bstep (se 2 (by rfl) ⟨598344, by rfl⟩ : syracuseStep 1595585 = 1196689) B1196689
theorem B1595713 : Blo 944585 1595713 := bstep (se 2 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 1595713 = 1196785) B1196785
theorem B1136963 : Blo 944585 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2873681 : Blo 944585 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1595747 : Blo 944585 1595747 := bstep (se 1 (by rfl) ⟨1196810, by rfl⟩ : syracuseStep 1595747 = 2393621) B2393621
theorem B3201389 : Blo 944585 3201389 := bstep (se 3 (by rfl) ⟨600260, by rfl⟩ : syracuseStep 3201389 = 1200521) B1200521
theorem B7199117 : Blo 944585 7199117 := bstep (se 3 (by rfl) ⟨1349834, by rfl⟩ : syracuseStep 7199117 = 2699669) B2699669
theorem B3201443 : Blo 944585 3201443 := bstep (se 1 (by rfl) ⟨2401082, by rfl⟩ : syracuseStep 3201443 = 4802165) B4802165
theorem B1595875 : Blo 944585 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B6052421 : Blo 944585 6052421 := bstep (se 4 (by rfl) ⟨567414, by rfl⟩ : syracuseStep 6052421 = 1134829) B1134829
theorem B3594851 : Blo 944585 3594851 := bstep (se 1 (by rfl) ⟨2696138, by rfl⟩ : syracuseStep 3594851 = 5392277) B5392277
theorem B1596017 : Blo 944585 1596017 := bstep (se 2 (by rfl) ⟨598506, by rfl⟩ : syracuseStep 1596017 = 1197013) B1197013
theorem B1038995 : Blo 944585 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B5986993 : Blo 944585 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B1596145 : Blo 944585 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B1596179 : Blo 944585 1596179 := bstep (se 1 (by rfl) ⟨1197134, by rfl⟩ : syracuseStep 1596179 = 2394269) B2394269
theorem B1596307 : Blo 944585 1596307 := bstep (se 1 (by rfl) ⟨1197230, by rfl⟩ : syracuseStep 1596307 = 2394461) B2394461
theorem B5397425 : Blo 944585 5397425 := bstep (se 2 (by rfl) ⟨2024034, by rfl⟩ : syracuseStep 5397425 = 4048069) B4048069
theorem B1596449 : Blo 944585 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B1596577 : Blo 944585 1596577 := bstep (se 2 (by rfl) ⟨598716, by rfl⟩ : syracuseStep 1596577 = 1197433) B1197433
theorem B1596611 : Blo 944585 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B1596739 : Blo 944585 1596739 := bstep (se 1 (by rfl) ⟨1197554, by rfl⟩ : syracuseStep 1596739 = 2395109) B2395109
theorem B8314211 : Blo 944585 8314211 := bstep (se 1 (by rfl) ⟨6235658, by rfl⟩ : syracuseStep 8314211 = 12471317) B12471317
theorem B3038563 : Blo 944585 3038563 := bstep (se 1 (by rfl) ⟨2278922, by rfl⟩ : syracuseStep 3038563 = 4557845) B4557845
theorem B1596881 : Blo 944585 1596881 := bstep (se 2 (by rfl) ⟨598830, by rfl⟩ : syracuseStep 1596881 = 1197661) B1197661
theorem B3595853 : Blo 944585 3595853 := bstep (se 3 (by rfl) ⟨674222, by rfl⟩ : syracuseStep 3595853 = 1348445) B1348445
theorem B1597009 : Blo 944585 1597009 := bstep (se 2 (by rfl) ⟨598878, by rfl⟩ : syracuseStep 1597009 = 1197757) B1197757
theorem B5758577 : Blo 944585 5758577 := bstep (se 2 (by rfl) ⟨2159466, by rfl⟩ : syracuseStep 5758577 = 4318933) B4318933
theorem B1597043 : Blo 944585 1597043 := bstep (se 1 (by rfl) ⟨1197782, by rfl⟩ : syracuseStep 1597043 = 2395565) B2395565
theorem B3038897 : Blo 944585 3038897 := bstep (se 2 (by rfl) ⟨1139586, by rfl⟩ : syracuseStep 3038897 = 2279173) B2279173
theorem B5463749 : Blo 944585 5463749 := bstep (se 4 (by rfl) ⟨512226, by rfl⟩ : syracuseStep 5463749 = 1024453) B1024453
theorem B3464909 : Blo 944585 3464909 := bstep (se 3 (by rfl) ⟨649670, by rfl⟩ : syracuseStep 3464909 = 1299341) B1299341
theorem B1597171 : Blo 944585 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B1597313 : Blo 944585 1597313 := bstep (se 2 (by rfl) ⟨598992, by rfl⟩ : syracuseStep 1597313 = 1197985) B1197985
theorem B1794001 : Blo 944585 1794001 := bstep (se 2 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 1794001 = 1345501) B1345501
theorem B1597441 : Blo 944585 1597441 := bstep (se 2 (by rfl) ⟨599040, by rfl⟩ : syracuseStep 1597441 = 1198081) B1198081
theorem B2875409 : Blo 944585 2875409 := bstep (se 2 (by rfl) ⟨1078278, by rfl⟩ : syracuseStep 2875409 = 2156557) B2156557
theorem B1597475 : Blo 944585 1597475 := bstep (se 1 (by rfl) ⟨1198106, by rfl⟩ : syracuseStep 1597475 = 2396213) B2396213
theorem B10379377 : Blo 944585 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B1597603 : Blo 944585 1597603 := bstep (se 1 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 1597603 = 2396405) B2396405
theorem B1597745 : Blo 944585 1597745 := bstep (se 2 (by rfl) ⟨599154, by rfl⟩ : syracuseStep 1597745 = 1198309) B1198309
theorem B7659845 : Blo 944585 7659845 := bstep (se 4 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 7659845 = 1436221) B1436221
theorem B1794403 : Blo 944585 1794403 := bstep (se 1 (by rfl) ⟨1345802, by rfl⟩ : syracuseStep 1794403 = 2691605) B2691605
theorem B5398883 : Blo 944585 5398883 := bstep (se 1 (by rfl) ⟨4049162, by rfl⟩ : syracuseStep 5398883 = 8098325) B8098325
theorem B1794449 : Blo 944585 1794449 := bstep (se 2 (by rfl) ⟨672918, by rfl⟩ : syracuseStep 1794449 = 1345837) B1345837
theorem B1597873 : Blo 944585 1597873 := bstep (se 2 (by rfl) ⟨599202, by rfl⟩ : syracuseStep 1597873 = 1198405) B1198405
theorem B1597907 : Blo 944585 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B1598035 : Blo 944585 1598035 := bstep (se 1 (by rfl) ⟨1198526, by rfl⟩ : syracuseStep 1598035 = 2397053) B2397053
theorem B1794737 : Blo 944585 1794737 := bstep (se 2 (by rfl) ⟨673026, by rfl⟩ : syracuseStep 1794737 = 1346053) B1346053
theorem B1598177 : Blo 944585 1598177 := bstep (se 2 (by rfl) ⟨599316, by rfl⟩ : syracuseStep 1598177 = 1198633) B1198633
theorem B1598305 : Blo 944585 1598305 := bstep (se 2 (by rfl) ⟨599364, by rfl⟩ : syracuseStep 1598305 = 1198729) B1198729
theorem B2024291 : Blo 944585 2024291 := bstep (se 1 (by rfl) ⟨1518218, by rfl⟩ : syracuseStep 2024291 = 3036437) B3036437
theorem B1598339 : Blo 944585 1598339 := bstep (se 1 (by rfl) ⟨1198754, by rfl⟩ : syracuseStep 1598339 = 2397509) B2397509
theorem B1598467 : Blo 944585 1598467 := bstep (se 1 (by rfl) ⟨1198850, by rfl⟩ : syracuseStep 1598467 = 2397701) B2397701
theorem B2876429 : Blo 944585 2876429 := bstep (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) B1078661
theorem B1598609 : Blo 944585 1598609 := bstep (se 2 (by rfl) ⟨599478, by rfl⟩ : syracuseStep 1598609 = 1198957) B1198957
theorem B7202033 : Blo 944585 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B1598737 : Blo 944585 1598737 := bstep (se 2 (by rfl) ⟨599526, by rfl⟩ : syracuseStep 1598737 = 1199053) B1199053
theorem B1598771 : Blo 944585 1598771 := bstep (se 1 (by rfl) ⟨1199078, by rfl⟩ : syracuseStep 1598771 = 2398157) B2398157
theorem B5399885 : Blo 944585 5399885 := bstep (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) B2024957
theorem B12117347 : Blo 944585 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B1795459 : Blo 944585 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B1598899 : Blo 944585 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B4318733 : Blo 944585 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B1599041 : Blo 944585 1599041 := bstep (se 2 (by rfl) ⟨599640, by rfl⟩ : syracuseStep 1599041 = 1199281) B1199281
theorem B3597965 : Blo 944585 3597965 := bstep (se 3 (by rfl) ⟨674618, by rfl⟩ : syracuseStep 3597965 = 1349237) B1349237
theorem B1599169 : Blo 944585 1599169 := bstep (se 2 (by rfl) ⟨599688, by rfl⟩ : syracuseStep 1599169 = 1199377) B1199377
theorem B2025155 : Blo 944585 2025155 := bstep (se 1 (by rfl) ⟨1518866, by rfl⟩ : syracuseStep 2025155 = 3037733) B3037733
theorem B10643171 : Blo 944585 10643171 := bstep (se 1 (by rfl) ⟨7982378, by rfl⟩ : syracuseStep 10643171 = 15964757) B15964757
theorem B1599203 : Blo 944585 1599203 := bstep (se 1 (by rfl) ⟨1199402, by rfl⟩ : syracuseStep 1599203 = 2398805) B2398805
theorem B2025265 : Blo 944585 2025265 := bstep (se 2 (by rfl) ⟨759474, by rfl⟩ : syracuseStep 2025265 = 1518949) B1518949
theorem B1795907 : Blo 944585 1795907 := bstep (se 1 (by rfl) ⟨1346930, by rfl⟩ : syracuseStep 1795907 = 2693861) B2693861
theorem B1599331 : Blo 944585 1599331 := bstep (se 1 (by rfl) ⟨1199498, by rfl⟩ : syracuseStep 1599331 = 2398997) B2398997
theorem B1009523 : Blo 944585 1009523 := bstep (se 1 (by rfl) ⟨757142, by rfl⟩ : syracuseStep 1009523 = 1514285) B1514285
theorem B1599473 : Blo 944585 1599473 := bstep (se 2 (by rfl) ⟨599802, by rfl⟩ : syracuseStep 1599473 = 1199605) B1199605
theorem B6055985 : Blo 944585 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B1796195 : Blo 944585 1796195 := bstep (se 1 (by rfl) ⟨1347146, by rfl⟩ : syracuseStep 1796195 = 2694293) B2694293
theorem B1599601 : Blo 944585 1599601 := bstep (se 2 (by rfl) ⟨599850, by rfl⟩ : syracuseStep 1599601 = 1199701) B1199701
theorem B1599635 : Blo 944585 1599635 := bstep (se 1 (by rfl) ⟨1199726, by rfl⟩ : syracuseStep 1599635 = 2399453) B2399453
theorem B1599763 : Blo 944585 1599763 := bstep (se 1 (by rfl) ⟨1199822, by rfl⟩ : syracuseStep 1599763 = 2399645) B2399645
theorem B1599905 : Blo 944585 1599905 := bstep (se 2 (by rfl) ⟨599964, by rfl⟩ : syracuseStep 1599905 = 1199929) B1199929
theorem B3598769 : Blo 944585 3598769 := bstep (se 2 (by rfl) ⟨1349538, by rfl⟩ : syracuseStep 3598769 = 2699077) B2699077
theorem B8088005 : Blo 944585 8088005 := bstep (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) B1516501
theorem B944595 : Blo 944585 944595 := bstep (se 1 (by rfl) ⟨708446, by rfl⟩ : syracuseStep 944595 = 1416893) B1416893
theorem B944611 : Blo 944585 944611 := bstep (se 1 (by rfl) ⟨708458, by rfl⟩ : syracuseStep 944611 = 1416917) B1416917
theorem B944627 : Blo 944585 944627 := bstep (se 1 (by rfl) ⟨708470, by rfl⟩ : syracuseStep 944627 = 1416941) B1416941
theorem B944643 : Blo 944585 944643 := bstep (se 1 (by rfl) ⟨708482, by rfl⟩ : syracuseStep 944643 = 1416965) B1416965
theorem B944659 : Blo 944585 944659 := bstep (se 1 (by rfl) ⟨708494, by rfl⟩ : syracuseStep 944659 = 1416989) B1416989
theorem B1600033 : Blo 944585 1600033 := bstep (se 2 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 1600033 = 1200025) B1200025
theorem B944675 : Blo 944585 944675 := bstep (se 1 (by rfl) ⟨708506, by rfl⟩ : syracuseStep 944675 = 1417013) B1417013
theorem B944691 : Blo 944585 944691 := bstep (se 1 (by rfl) ⟨708518, by rfl⟩ : syracuseStep 944691 = 1417037) B1417037
theorem B944707 : Blo 944585 944707 := bstep (se 1 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 944707 = 1417061) B1417061
theorem B1600067 : Blo 944585 1600067 := bstep (se 1 (by rfl) ⟨1200050, by rfl⟩ : syracuseStep 1600067 = 2400101) B2400101
theorem B944723 : Blo 944585 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B944739 : Blo 944585 944739 := bstep (se 1 (by rfl) ⟨708554, by rfl⟩ : syracuseStep 944739 = 1417109) B1417109
theorem B944755 : Blo 944585 944755 := bstep (se 1 (by rfl) ⟨708566, by rfl⟩ : syracuseStep 944755 = 1417133) B1417133
theorem B944771 : Blo 944585 944771 := bstep (se 1 (by rfl) ⟨708578, by rfl⟩ : syracuseStep 944771 = 1417157) B1417157
theorem B944787 : Blo 944585 944787 := bstep (se 1 (by rfl) ⟨708590, by rfl⟩ : syracuseStep 944787 = 1417181) B1417181
theorem B944803 : Blo 944585 944803 := bstep (se 1 (by rfl) ⟨708602, by rfl⟩ : syracuseStep 944803 = 1417205) B1417205
theorem B944819 : Blo 944585 944819 := bstep (se 1 (by rfl) ⟨708614, by rfl⟩ : syracuseStep 944819 = 1417229) B1417229
theorem B944835 : Blo 944585 944835 := bstep (se 1 (by rfl) ⟨708626, by rfl⟩ : syracuseStep 944835 = 1417253) B1417253
theorem B1600195 : Blo 944585 1600195 := bstep (se 1 (by rfl) ⟨1200146, by rfl⟩ : syracuseStep 1600195 = 2400293) B2400293
theorem B944851 : Blo 944585 944851 := bstep (se 1 (by rfl) ⟨708638, by rfl⟩ : syracuseStep 944851 = 1417277) B1417277
theorem B944867 : Blo 944585 944867 := bstep (se 1 (by rfl) ⟨708650, by rfl⟩ : syracuseStep 944867 = 1417301) B1417301
theorem B944883 : Blo 944585 944883 := bstep (se 1 (by rfl) ⟨708662, by rfl⟩ : syracuseStep 944883 = 1417325) B1417325
theorem B944899 : Blo 944585 944899 := bstep (se 1 (by rfl) ⟨708674, by rfl⟩ : syracuseStep 944899 = 1417349) B1417349
theorem B944915 : Blo 944585 944915 := bstep (se 1 (by rfl) ⟨708686, by rfl⟩ : syracuseStep 944915 = 1417373) B1417373
theorem B944931 : Blo 944585 944931 := bstep (se 1 (by rfl) ⟨708698, by rfl⟩ : syracuseStep 944931 = 1417397) B1417397
theorem B944947 : Blo 944585 944947 := bstep (se 1 (by rfl) ⟨708710, by rfl⟩ : syracuseStep 944947 = 1417421) B1417421
theorem B944963 : Blo 944585 944963 := bstep (se 1 (by rfl) ⟨708722, by rfl⟩ : syracuseStep 944963 = 1417445) B1417445
theorem B1600337 : Blo 944585 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B944979 : Blo 944585 944979 := bstep (se 1 (by rfl) ⟨708734, by rfl⟩ : syracuseStep 944979 = 1417469) B1417469
theorem B944995 : Blo 944585 944995 := bstep (se 1 (by rfl) ⟨708746, by rfl⟩ : syracuseStep 944995 = 1417493) B1417493
theorem B945011 : Blo 944585 945011 := bstep (se 1 (by rfl) ⟨708758, by rfl⟩ : syracuseStep 945011 = 1417517) B1417517
theorem B945027 : Blo 944585 945027 := bstep (se 1 (by rfl) ⟨708770, by rfl⟩ : syracuseStep 945027 = 1417541) B1417541
theorem B945043 : Blo 944585 945043 := bstep (se 1 (by rfl) ⟨708782, by rfl⟩ : syracuseStep 945043 = 1417565) B1417565
theorem B945059 : Blo 944585 945059 := bstep (se 1 (by rfl) ⟨708794, by rfl⟩ : syracuseStep 945059 = 1417589) B1417589
theorem B945075 : Blo 944585 945075 := bstep (se 1 (by rfl) ⟨708806, by rfl⟩ : syracuseStep 945075 = 1417613) B1417613
theorem B945091 : Blo 944585 945091 := bstep (se 1 (by rfl) ⟨708818, by rfl⟩ : syracuseStep 945091 = 1417637) B1417637
theorem B1600465 : Blo 944585 1600465 := bstep (se 2 (by rfl) ⟨600174, by rfl⟩ : syracuseStep 1600465 = 1200349) B1200349
theorem B945107 : Blo 944585 945107 := bstep (se 1 (by rfl) ⟨708830, by rfl⟩ : syracuseStep 945107 = 1417661) B1417661
theorem B945123 : Blo 944585 945123 := bstep (se 1 (by rfl) ⟨708842, by rfl⟩ : syracuseStep 945123 = 1417685) B1417685
theorem B945139 : Blo 944585 945139 := bstep (se 1 (by rfl) ⟨708854, by rfl⟩ : syracuseStep 945139 = 1417709) B1417709
theorem B1600499 : Blo 944585 1600499 := bstep (se 1 (by rfl) ⟨1200374, by rfl⟩ : syracuseStep 1600499 = 2400749) B2400749
theorem B945155 : Blo 944585 945155 := bstep (se 1 (by rfl) ⟨708866, by rfl⟩ : syracuseStep 945155 = 1417733) B1417733
theorem B1797137 : Blo 944585 1797137 := bstep (se 2 (by rfl) ⟨673926, by rfl⟩ : syracuseStep 1797137 = 1347853) B1347853
theorem B945171 : Blo 944585 945171 := bstep (se 1 (by rfl) ⟨708878, by rfl⟩ : syracuseStep 945171 = 1417757) B1417757
theorem B945187 : Blo 944585 945187 := bstep (se 1 (by rfl) ⟨708890, by rfl⟩ : syracuseStep 945187 = 1417781) B1417781
theorem B945203 : Blo 944585 945203 := bstep (se 1 (by rfl) ⟨708902, by rfl⟩ : syracuseStep 945203 = 1417805) B1417805
theorem B945219 : Blo 944585 945219 := bstep (se 1 (by rfl) ⟨708914, by rfl⟩ : syracuseStep 945219 = 1417829) B1417829
theorem B3599437 : Blo 944585 3599437 := bstep (se 3 (by rfl) ⟨674894, by rfl⟩ : syracuseStep 3599437 = 1349789) B1349789
theorem B945235 : Blo 944585 945235 := bstep (se 1 (by rfl) ⟨708926, by rfl⟩ : syracuseStep 945235 = 1417853) B1417853
theorem B945251 : Blo 944585 945251 := bstep (se 1 (by rfl) ⟨708938, by rfl⟩ : syracuseStep 945251 = 1417877) B1417877
theorem B945267 : Blo 944585 945267 := bstep (se 1 (by rfl) ⟨708950, by rfl⟩ : syracuseStep 945267 = 1417901) B1417901
theorem B1600627 : Blo 944585 1600627 := bstep (se 1 (by rfl) ⟨1200470, by rfl⟩ : syracuseStep 1600627 = 2400941) B2400941
theorem B945283 : Blo 944585 945283 := bstep (se 1 (by rfl) ⟨708962, by rfl⟩ : syracuseStep 945283 = 1417925) B1417925
theorem B945299 : Blo 944585 945299 := bstep (se 1 (by rfl) ⟨708974, by rfl⟩ : syracuseStep 945299 = 1417949) B1417949
theorem B945315 : Blo 944585 945315 := bstep (se 1 (by rfl) ⟨708986, by rfl⟩ : syracuseStep 945315 = 1417973) B1417973
theorem B945331 : Blo 944585 945331 := bstep (se 1 (by rfl) ⟨708998, by rfl⟩ : syracuseStep 945331 = 1417997) B1417997
theorem B945347 : Blo 944585 945347 := bstep (se 1 (by rfl) ⟨709010, by rfl⟩ : syracuseStep 945347 = 1418021) B1418021
theorem B945363 : Blo 944585 945363 := bstep (se 1 (by rfl) ⟨709022, by rfl⟩ : syracuseStep 945363 = 1418045) B1418045
theorem B945379 : Blo 944585 945379 := bstep (se 1 (by rfl) ⟨709034, by rfl⟩ : syracuseStep 945379 = 1418069) B1418069
theorem B945395 : Blo 944585 945395 := bstep (se 1 (by rfl) ⟨709046, by rfl⟩ : syracuseStep 945395 = 1418093) B1418093
theorem B945411 : Blo 944585 945411 := bstep (se 1 (by rfl) ⟨709058, by rfl⟩ : syracuseStep 945411 = 1418117) B1418117
theorem B945427 : Blo 944585 945427 := bstep (se 1 (by rfl) ⟨709070, by rfl⟩ : syracuseStep 945427 = 1418141) B1418141
theorem B945443 : Blo 944585 945443 := bstep (se 1 (by rfl) ⟨709082, by rfl⟩ : syracuseStep 945443 = 1418165) B1418165
theorem B945459 : Blo 944585 945459 := bstep (se 1 (by rfl) ⟨709094, by rfl⟩ : syracuseStep 945459 = 1418189) B1418189
theorem B945475 : Blo 944585 945475 := bstep (se 1 (by rfl) ⟨709106, by rfl⟩ : syracuseStep 945475 = 1418213) B1418213
theorem B945491 : Blo 944585 945491 := bstep (se 1 (by rfl) ⟨709118, by rfl⟩ : syracuseStep 945491 = 1418237) B1418237
theorem B945507 : Blo 944585 945507 := bstep (se 1 (by rfl) ⟨709130, by rfl⟩ : syracuseStep 945507 = 1418261) B1418261
theorem B945523 : Blo 944585 945523 := bstep (se 1 (by rfl) ⟨709142, by rfl⟩ : syracuseStep 945523 = 1418285) B1418285
theorem B945539 : Blo 944585 945539 := bstep (se 1 (by rfl) ⟨709154, by rfl⟩ : syracuseStep 945539 = 1418309) B1418309
theorem B945555 : Blo 944585 945555 := bstep (se 1 (by rfl) ⟨709166, by rfl⟩ : syracuseStep 945555 = 1418333) B1418333
theorem B945571 : Blo 944585 945571 := bstep (se 1 (by rfl) ⟨709178, by rfl⟩ : syracuseStep 945571 = 1418357) B1418357
theorem B945587 : Blo 944585 945587 := bstep (se 1 (by rfl) ⟨709190, by rfl⟩ : syracuseStep 945587 = 1418381) B1418381
theorem B945603 : Blo 944585 945603 := bstep (se 1 (by rfl) ⟨709202, by rfl⟩ : syracuseStep 945603 = 1418405) B1418405
theorem B945619 : Blo 944585 945619 := bstep (se 1 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 945619 = 1418429) B1418429
theorem B6057443 : Blo 944585 6057443 := bstep (se 1 (by rfl) ⟨4543082, by rfl⟩ : syracuseStep 6057443 = 9086165) B9086165
theorem B945635 : Blo 944585 945635 := bstep (se 1 (by rfl) ⟨709226, by rfl⟩ : syracuseStep 945635 = 1418453) B1418453
theorem B945651 : Blo 944585 945651 := bstep (se 1 (by rfl) ⟨709238, by rfl⟩ : syracuseStep 945651 = 1418477) B1418477
theorem B945667 : Blo 944585 945667 := bstep (se 1 (by rfl) ⟨709250, by rfl⟩ : syracuseStep 945667 = 1418501) B1418501
theorem B10776077 : Blo 944585 10776077 := bstep (se 3 (by rfl) ⟨2020514, by rfl⟩ : syracuseStep 10776077 = 4041029) B4041029
theorem B945683 : Blo 944585 945683 := bstep (se 1 (by rfl) ⟨709262, by rfl⟩ : syracuseStep 945683 = 1418525) B1418525
theorem B945699 : Blo 944585 945699 := bstep (se 1 (by rfl) ⟨709274, by rfl⟩ : syracuseStep 945699 = 1418549) B1418549
theorem B945715 : Blo 944585 945715 := bstep (se 1 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 945715 = 1418573) B1418573
theorem B945731 : Blo 944585 945731 := bstep (se 1 (by rfl) ⟨709298, by rfl⟩ : syracuseStep 945731 = 1418597) B1418597
theorem B945747 : Blo 944585 945747 := bstep (se 1 (by rfl) ⟨709310, by rfl⟩ : syracuseStep 945747 = 1418621) B1418621
theorem B945763 : Blo 944585 945763 := bstep (se 1 (by rfl) ⟨709322, by rfl⟩ : syracuseStep 945763 = 1418645) B1418645
theorem B945779 : Blo 944585 945779 := bstep (se 1 (by rfl) ⟨709334, by rfl⟩ : syracuseStep 945779 = 1418669) B1418669
theorem B945795 : Blo 944585 945795 := bstep (se 1 (by rfl) ⟨709346, by rfl⟩ : syracuseStep 945795 = 1418693) B1418693
theorem B2125457 : Blo 944585 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B945811 : Blo 944585 945811 := bstep (se 1 (by rfl) ⟨709358, by rfl⟩ : syracuseStep 945811 = 1418717) B1418717
theorem B2125475 : Blo 944585 2125475 := bstep (se 1 (by rfl) ⟨1594106, by rfl⟩ : syracuseStep 2125475 = 3188213) B3188213
theorem B945827 : Blo 944585 945827 := bstep (se 1 (by rfl) ⟨709370, by rfl⟩ : syracuseStep 945827 = 1418741) B1418741
theorem B945843 : Blo 944585 945843 := bstep (se 1 (by rfl) ⟨709382, by rfl⟩ : syracuseStep 945843 = 1418765) B1418765
theorem B945859 : Blo 944585 945859 := bstep (se 1 (by rfl) ⟨709394, by rfl⟩ : syracuseStep 945859 = 1418789) B1418789
theorem B945875 : Blo 944585 945875 := bstep (se 1 (by rfl) ⟨709406, by rfl⟩ : syracuseStep 945875 = 1418813) B1418813
theorem B945891 : Blo 944585 945891 := bstep (se 1 (by rfl) ⟨709418, by rfl⟩ : syracuseStep 945891 = 1418837) B1418837
theorem B2158307 : Blo 944585 2158307 := bstep (se 1 (by rfl) ⟨1618730, by rfl⟩ : syracuseStep 2158307 = 3237461) B3237461
theorem B945907 : Blo 944585 945907 := bstep (se 1 (by rfl) ⟨709430, by rfl⟩ : syracuseStep 945907 = 1418861) B1418861
theorem B945923 : Blo 944585 945923 := bstep (se 1 (by rfl) ⟨709442, by rfl⟩ : syracuseStep 945923 = 1418885) B1418885
theorem B945939 : Blo 944585 945939 := bstep (se 1 (by rfl) ⟨709454, by rfl⟩ : syracuseStep 945939 = 1418909) B1418909
theorem B945955 : Blo 944585 945955 := bstep (se 1 (by rfl) ⟨709466, by rfl⟩ : syracuseStep 945955 = 1418933) B1418933
theorem B945971 : Blo 944585 945971 := bstep (se 1 (by rfl) ⟨709478, by rfl⟩ : syracuseStep 945971 = 1418957) B1418957
theorem B945987 : Blo 944585 945987 := bstep (se 1 (by rfl) ⟨709490, by rfl⟩ : syracuseStep 945987 = 1418981) B1418981
theorem B946003 : Blo 944585 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B1011539 : Blo 944585 1011539 := bstep (se 1 (by rfl) ⟨758654, by rfl⟩ : syracuseStep 1011539 = 1517309) B1517309
theorem B946019 : Blo 944585 946019 := bstep (se 1 (by rfl) ⟨709514, by rfl⟩ : syracuseStep 946019 = 1419029) B1419029
theorem B3600227 : Blo 944585 3600227 := bstep (se 1 (by rfl) ⟨2700170, by rfl⟩ : syracuseStep 3600227 = 5400341) B5400341
theorem B946035 : Blo 944585 946035 := bstep (se 1 (by rfl) ⟨709526, by rfl⟩ : syracuseStep 946035 = 1419053) B1419053
theorem B946051 : Blo 944585 946051 := bstep (se 1 (by rfl) ⟨709538, by rfl⟩ : syracuseStep 946051 = 1419077) B1419077
theorem B1798033 : Blo 944585 1798033 := bstep (se 2 (by rfl) ⟨674262, by rfl⟩ : syracuseStep 1798033 = 1348525) B1348525
theorem B946067 : Blo 944585 946067 := bstep (se 1 (by rfl) ⟨709550, by rfl⟩ : syracuseStep 946067 = 1419101) B1419101
theorem B946083 : Blo 944585 946083 := bstep (se 1 (by rfl) ⟨709562, by rfl⟩ : syracuseStep 946083 = 1419125) B1419125
theorem B2125745 : Blo 944585 2125745 := bstep (se 2 (by rfl) ⟨797154, by rfl⟩ : syracuseStep 2125745 = 1594309) B1594309
theorem B946099 : Blo 944585 946099 := bstep (se 1 (by rfl) ⟨709574, by rfl⟩ : syracuseStep 946099 = 1419149) B1419149
theorem B2125763 : Blo 944585 2125763 := bstep (se 1 (by rfl) ⟨1594322, by rfl⟩ : syracuseStep 2125763 = 3188645) B3188645
theorem B946115 : Blo 944585 946115 := bstep (se 1 (by rfl) ⟨709586, by rfl⟩ : syracuseStep 946115 = 1419173) B1419173
theorem B946131 : Blo 944585 946131 := bstep (se 1 (by rfl) ⟨709598, by rfl⟩ : syracuseStep 946131 = 1419197) B1419197
theorem B946147 : Blo 944585 946147 := bstep (se 1 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 946147 = 1419221) B1419221
theorem B946163 : Blo 944585 946163 := bstep (se 1 (by rfl) ⟨709622, by rfl⟩ : syracuseStep 946163 = 1419245) B1419245
theorem B946179 : Blo 944585 946179 := bstep (se 1 (by rfl) ⟨709634, by rfl⟩ : syracuseStep 946179 = 1419269) B1419269
theorem B946195 : Blo 944585 946195 := bstep (se 1 (by rfl) ⟨709646, by rfl⟩ : syracuseStep 946195 = 1419293) B1419293
theorem B946211 : Blo 944585 946211 := bstep (se 1 (by rfl) ⟨709658, by rfl⟩ : syracuseStep 946211 = 1419317) B1419317
theorem B1798193 : Blo 944585 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B946227 : Blo 944585 946227 := bstep (se 1 (by rfl) ⟨709670, by rfl⟩ : syracuseStep 946227 = 1419341) B1419341
theorem B946243 : Blo 944585 946243 := bstep (se 1 (by rfl) ⟨709682, by rfl⟩ : syracuseStep 946243 = 1419365) B1419365
theorem B946259 : Blo 944585 946259 := bstep (se 1 (by rfl) ⟨709694, by rfl⟩ : syracuseStep 946259 = 1419389) B1419389
theorem B946275 : Blo 944585 946275 := bstep (se 1 (by rfl) ⟨709706, by rfl⟩ : syracuseStep 946275 = 1419413) B1419413
theorem B946291 : Blo 944585 946291 := bstep (se 1 (by rfl) ⟨709718, by rfl⟩ : syracuseStep 946291 = 1419437) B1419437
theorem B946307 : Blo 944585 946307 := bstep (se 1 (by rfl) ⟨709730, by rfl⟩ : syracuseStep 946307 = 1419461) B1419461
theorem B946323 : Blo 944585 946323 := bstep (se 1 (by rfl) ⟨709742, by rfl⟩ : syracuseStep 946323 = 1419485) B1419485
theorem B946339 : Blo 944585 946339 := bstep (se 1 (by rfl) ⟨709754, by rfl⟩ : syracuseStep 946339 = 1419509) B1419509
theorem B946355 : Blo 944585 946355 := bstep (se 1 (by rfl) ⟨709766, by rfl⟩ : syracuseStep 946355 = 1419533) B1419533
theorem B946371 : Blo 944585 946371 := bstep (se 1 (by rfl) ⟨709778, by rfl⟩ : syracuseStep 946371 = 1419557) B1419557
theorem B5763269 : Blo 944585 5763269 := bstep (se 4 (by rfl) ⟨540306, by rfl⟩ : syracuseStep 5763269 = 1080613) B1080613
theorem B2126033 : Blo 944585 2126033 := bstep (se 2 (by rfl) ⟨797262, by rfl⟩ : syracuseStep 2126033 = 1594525) B1594525
theorem B946387 : Blo 944585 946387 := bstep (se 1 (by rfl) ⟨709790, by rfl⟩ : syracuseStep 946387 = 1419581) B1419581
theorem B2126051 : Blo 944585 2126051 := bstep (se 1 (by rfl) ⟨1594538, by rfl⟩ : syracuseStep 2126051 = 3189077) B3189077
theorem B1437923 : Blo 944585 1437923 := bstep (se 1 (by rfl) ⟨1078442, by rfl⟩ : syracuseStep 1437923 = 2156885) B2156885
theorem B946403 : Blo 944585 946403 := bstep (se 1 (by rfl) ⟨709802, by rfl⟩ : syracuseStep 946403 = 1419605) B1419605
theorem B946419 : Blo 944585 946419 := bstep (se 1 (by rfl) ⟨709814, by rfl⟩ : syracuseStep 946419 = 1419629) B1419629
theorem B946435 : Blo 944585 946435 := bstep (se 1 (by rfl) ⟨709826, by rfl⟩ : syracuseStep 946435 = 1419653) B1419653
theorem B946451 : Blo 944585 946451 := bstep (se 1 (by rfl) ⟨709838, by rfl⟩ : syracuseStep 946451 = 1419677) B1419677
theorem B946467 : Blo 944585 946467 := bstep (se 1 (by rfl) ⟨709850, by rfl⟩ : syracuseStep 946467 = 1419701) B1419701
theorem B946483 : Blo 944585 946483 := bstep (se 1 (by rfl) ⟨709862, by rfl⟩ : syracuseStep 946483 = 1419725) B1419725
theorem B946499 : Blo 944585 946499 := bstep (se 1 (by rfl) ⟨709874, by rfl⟩ : syracuseStep 946499 = 1419749) B1419749
theorem B946515 : Blo 944585 946515 := bstep (se 1 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 946515 = 1419773) B1419773
theorem B946531 : Blo 944585 946531 := bstep (se 1 (by rfl) ⟨709898, by rfl⟩ : syracuseStep 946531 = 1419797) B1419797
theorem B8089955 : Blo 944585 8089955 := bstep (se 1 (by rfl) ⟨6067466, by rfl⟩ : syracuseStep 8089955 = 12134933) B12134933
theorem B946547 : Blo 944585 946547 := bstep (se 1 (by rfl) ⟨709910, by rfl⟩ : syracuseStep 946547 = 1419821) B1419821
theorem B946563 : Blo 944585 946563 := bstep (se 1 (by rfl) ⟨709922, by rfl⟩ : syracuseStep 946563 = 1419845) B1419845
theorem B946579 : Blo 944585 946579 := bstep (se 1 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 946579 = 1419869) B1419869
theorem B946595 : Blo 944585 946595 := bstep (se 1 (by rfl) ⟨709946, by rfl⟩ : syracuseStep 946595 = 1419893) B1419893
theorem B946611 : Blo 944585 946611 := bstep (se 1 (by rfl) ⟨709958, by rfl⟩ : syracuseStep 946611 = 1419917) B1419917
theorem B946627 : Blo 944585 946627 := bstep (se 1 (by rfl) ⟨709970, by rfl⟩ : syracuseStep 946627 = 1419941) B1419941
theorem B1798595 : Blo 944585 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B2159057 : Blo 944585 2159057 := bstep (se 2 (by rfl) ⟨809646, by rfl⟩ : syracuseStep 2159057 = 1619293) B1619293
theorem B946643 : Blo 944585 946643 := bstep (se 1 (by rfl) ⟨709982, by rfl⟩ : syracuseStep 946643 = 1419965) B1419965
theorem B946659 : Blo 944585 946659 := bstep (se 1 (by rfl) ⟨709994, by rfl⟩ : syracuseStep 946659 = 1419989) B1419989
theorem B2126321 : Blo 944585 2126321 := bstep (se 2 (by rfl) ⟨797370, by rfl⟩ : syracuseStep 2126321 = 1594741) B1594741
theorem B3600881 : Blo 944585 3600881 := bstep (se 2 (by rfl) ⟨1350330, by rfl⟩ : syracuseStep 3600881 = 2700661) B2700661
theorem B946675 : Blo 944585 946675 := bstep (se 1 (by rfl) ⟨710006, by rfl⟩ : syracuseStep 946675 = 1420013) B1420013
theorem B2126339 : Blo 944585 2126339 := bstep (se 1 (by rfl) ⟨1594754, by rfl⟩ : syracuseStep 2126339 = 3189509) B3189509
theorem B946691 : Blo 944585 946691 := bstep (se 1 (by rfl) ⟨710018, by rfl⟩ : syracuseStep 946691 = 1420037) B1420037
theorem B946707 : Blo 944585 946707 := bstep (se 1 (by rfl) ⟨710030, by rfl⟩ : syracuseStep 946707 = 1420061) B1420061
theorem B946723 : Blo 944585 946723 := bstep (se 1 (by rfl) ⟨710042, by rfl⟩ : syracuseStep 946723 = 1420085) B1420085
theorem B946739 : Blo 944585 946739 := bstep (se 1 (by rfl) ⟨710054, by rfl⟩ : syracuseStep 946739 = 1420109) B1420109
theorem B946755 : Blo 944585 946755 := bstep (se 1 (by rfl) ⟨710066, by rfl⟩ : syracuseStep 946755 = 1420133) B1420133
theorem B946771 : Blo 944585 946771 := bstep (se 1 (by rfl) ⟨710078, by rfl⟩ : syracuseStep 946771 = 1420157) B1420157
theorem B9826915 : Blo 944585 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B946787 : Blo 944585 946787 := bstep (se 1 (by rfl) ⟨710090, by rfl⟩ : syracuseStep 946787 = 1420181) B1420181
theorem B946803 : Blo 944585 946803 := bstep (se 1 (by rfl) ⟨710102, by rfl⟩ : syracuseStep 946803 = 1420205) B1420205
theorem B946819 : Blo 944585 946819 := bstep (se 1 (by rfl) ⟨710114, by rfl⟩ : syracuseStep 946819 = 1420229) B1420229
theorem B946835 : Blo 944585 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B946851 : Blo 944585 946851 := bstep (se 1 (by rfl) ⟨710138, by rfl⟩ : syracuseStep 946851 = 1420277) B1420277
theorem B946867 : Blo 944585 946867 := bstep (se 1 (by rfl) ⟨710150, by rfl⟩ : syracuseStep 946867 = 1420301) B1420301
theorem B946883 : Blo 944585 946883 := bstep (se 1 (by rfl) ⟨710162, by rfl⟩ : syracuseStep 946883 = 1420325) B1420325
theorem B946899 : Blo 944585 946899 := bstep (se 1 (by rfl) ⟨710174, by rfl⟩ : syracuseStep 946899 = 1420349) B1420349
theorem B946915 : Blo 944585 946915 := bstep (se 1 (by rfl) ⟨710186, by rfl⟩ : syracuseStep 946915 = 1420373) B1420373
theorem B946931 : Blo 944585 946931 := bstep (se 1 (by rfl) ⟨710198, by rfl⟩ : syracuseStep 946931 = 1420397) B1420397
theorem B946947 : Blo 944585 946947 := bstep (se 1 (by rfl) ⟨710210, by rfl⟩ : syracuseStep 946947 = 1420421) B1420421
theorem B2126609 : Blo 944585 2126609 := bstep (se 2 (by rfl) ⟨797478, by rfl⟩ : syracuseStep 2126609 = 1594957) B1594957
theorem B946963 : Blo 944585 946963 := bstep (se 1 (by rfl) ⟨710222, by rfl⟩ : syracuseStep 946963 = 1420445) B1420445
theorem B2126627 : Blo 944585 2126627 := bstep (se 1 (by rfl) ⟨1594970, by rfl⟩ : syracuseStep 2126627 = 3189941) B3189941
theorem B946979 : Blo 944585 946979 := bstep (se 1 (by rfl) ⟨710234, by rfl⟩ : syracuseStep 946979 = 1420469) B1420469
theorem B946995 : Blo 944585 946995 := bstep (se 1 (by rfl) ⟨710246, by rfl⟩ : syracuseStep 946995 = 1420493) B1420493
theorem B947011 : Blo 944585 947011 := bstep (se 1 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 947011 = 1420517) B1420517
theorem B1012547 : Blo 944585 1012547 := bstep (se 1 (by rfl) ⟨759410, by rfl⟩ : syracuseStep 1012547 = 1518821) B1518821
theorem B947027 : Blo 944585 947027 := bstep (se 1 (by rfl) ⟨710270, by rfl⟩ : syracuseStep 947027 = 1420541) B1420541
theorem B947043 : Blo 944585 947043 := bstep (se 1 (by rfl) ⟨710282, by rfl⟩ : syracuseStep 947043 = 1420565) B1420565
theorem B947059 : Blo 944585 947059 := bstep (se 1 (by rfl) ⟨710294, by rfl⟩ : syracuseStep 947059 = 1420589) B1420589
theorem B947075 : Blo 944585 947075 := bstep (se 1 (by rfl) ⟨710306, by rfl⟩ : syracuseStep 947075 = 1420613) B1420613
theorem B947091 : Blo 944585 947091 := bstep (se 1 (by rfl) ⟨710318, by rfl⟩ : syracuseStep 947091 = 1420637) B1420637
theorem B947107 : Blo 944585 947107 := bstep (se 1 (by rfl) ⟨710330, by rfl⟩ : syracuseStep 947107 = 1420661) B1420661
theorem B947123 : Blo 944585 947123 := bstep (se 1 (by rfl) ⟨710342, by rfl⟩ : syracuseStep 947123 = 1420685) B1420685
theorem B947139 : Blo 944585 947139 := bstep (se 1 (by rfl) ⟨710354, by rfl⟩ : syracuseStep 947139 = 1420709) B1420709
theorem B947155 : Blo 944585 947155 := bstep (se 1 (by rfl) ⟨710366, by rfl⟩ : syracuseStep 947155 = 1420733) B1420733
theorem B947171 : Blo 944585 947171 := bstep (se 1 (by rfl) ⟨710378, by rfl⟩ : syracuseStep 947171 = 1420757) B1420757
theorem B947187 : Blo 944585 947187 := bstep (se 1 (by rfl) ⟨710390, by rfl⟩ : syracuseStep 947187 = 1420781) B1420781
theorem B947203 : Blo 944585 947203 := bstep (se 1 (by rfl) ⟨710402, by rfl⟩ : syracuseStep 947203 = 1420805) B1420805
theorem B1438739 : Blo 944585 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B947219 : Blo 944585 947219 := bstep (se 1 (by rfl) ⟨710414, by rfl⟩ : syracuseStep 947219 = 1420829) B1420829
theorem B947235 : Blo 944585 947235 := bstep (se 1 (by rfl) ⟨710426, by rfl⟩ : syracuseStep 947235 = 1420853) B1420853
theorem B2126897 : Blo 944585 2126897 := bstep (se 2 (by rfl) ⟨797586, by rfl⟩ : syracuseStep 2126897 = 1595173) B1595173
theorem B1438769 : Blo 944585 1438769 := bstep (se 2 (by rfl) ⟨539538, by rfl⟩ : syracuseStep 1438769 = 1079077) B1079077
theorem B947251 : Blo 944585 947251 := bstep (se 1 (by rfl) ⟨710438, by rfl⟩ : syracuseStep 947251 = 1420877) B1420877
theorem B2126915 : Blo 944585 2126915 := bstep (se 1 (by rfl) ⟨1595186, by rfl⟩ : syracuseStep 2126915 = 3190373) B3190373
theorem B947267 : Blo 944585 947267 := bstep (se 1 (by rfl) ⟨710450, by rfl⟩ : syracuseStep 947267 = 1420901) B1420901
theorem B947283 : Blo 944585 947283 := bstep (se 1 (by rfl) ⟨710462, by rfl⟩ : syracuseStep 947283 = 1420925) B1420925
theorem B947299 : Blo 944585 947299 := bstep (se 1 (by rfl) ⟨710474, by rfl⟩ : syracuseStep 947299 = 1420949) B1420949
theorem B947315 : Blo 944585 947315 := bstep (se 1 (by rfl) ⟨710486, by rfl⟩ : syracuseStep 947315 = 1420973) B1420973
theorem B947331 : Blo 944585 947331 := bstep (se 1 (by rfl) ⟨710498, by rfl⟩ : syracuseStep 947331 = 1420997) B1420997
theorem B947347 : Blo 944585 947347 := bstep (se 1 (by rfl) ⟨710510, by rfl⟩ : syracuseStep 947347 = 1421021) B1421021
theorem B947363 : Blo 944585 947363 := bstep (se 1 (by rfl) ⟨710522, by rfl⟩ : syracuseStep 947363 = 1421045) B1421045
theorem B947379 : Blo 944585 947379 := bstep (se 1 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 947379 = 1421069) B1421069
theorem B947395 : Blo 944585 947395 := bstep (se 1 (by rfl) ⟨710546, by rfl⟩ : syracuseStep 947395 = 1421093) B1421093
theorem B947411 : Blo 944585 947411 := bstep (se 1 (by rfl) ⟨710558, by rfl⟩ : syracuseStep 947411 = 1421117) B1421117
theorem B947427 : Blo 944585 947427 := bstep (se 1 (by rfl) ⟨710570, by rfl⟩ : syracuseStep 947427 = 1421141) B1421141
theorem B947443 : Blo 944585 947443 := bstep (se 1 (by rfl) ⟨710582, by rfl⟩ : syracuseStep 947443 = 1421165) B1421165
theorem B947459 : Blo 944585 947459 := bstep (se 1 (by rfl) ⟨710594, by rfl⟩ : syracuseStep 947459 = 1421189) B1421189
theorem B1438993 : Blo 944585 1438993 := bstep (se 2 (by rfl) ⟨539622, by rfl⟩ : syracuseStep 1438993 = 1079245) B1079245
theorem B947475 : Blo 944585 947475 := bstep (se 1 (by rfl) ⟨710606, by rfl⟩ : syracuseStep 947475 = 1421213) B1421213
theorem B947491 : Blo 944585 947491 := bstep (se 1 (by rfl) ⟨710618, by rfl⟩ : syracuseStep 947491 = 1421237) B1421237
theorem B947507 : Blo 944585 947507 := bstep (se 1 (by rfl) ⟨710630, by rfl⟩ : syracuseStep 947507 = 1421261) B1421261
theorem B15365429 : Blo 944585 15365429 := bstep (se 5 (by rfl) ⟨720254, by rfl⟩ : syracuseStep 15365429 = 1440509) B1440509
theorem B947523 : Blo 944585 947523 := bstep (se 1 (by rfl) ⟨710642, by rfl⟩ : syracuseStep 947523 = 1421285) B1421285
theorem B1799491 : Blo 944585 1799491 := bstep (se 1 (by rfl) ⟨1349618, by rfl⟩ : syracuseStep 1799491 = 2699237) B2699237
theorem B2127185 : Blo 944585 2127185 := bstep (se 2 (by rfl) ⟨797694, by rfl⟩ : syracuseStep 2127185 = 1595389) B1595389
theorem B947539 : Blo 944585 947539 := bstep (se 1 (by rfl) ⟨710654, by rfl⟩ : syracuseStep 947539 = 1421309) B1421309
theorem B10220899 : Blo 944585 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B2127203 : Blo 944585 2127203 := bstep (se 1 (by rfl) ⟨1595402, by rfl⟩ : syracuseStep 2127203 = 3190805) B3190805
theorem B947555 : Blo 944585 947555 := bstep (se 1 (by rfl) ⟨710666, by rfl⟩ : syracuseStep 947555 = 1421333) B1421333
theorem B947571 : Blo 944585 947571 := bstep (se 1 (by rfl) ⟨710678, by rfl⟩ : syracuseStep 947571 = 1421357) B1421357
theorem B947587 : Blo 944585 947587 := bstep (se 1 (by rfl) ⟨710690, by rfl⟩ : syracuseStep 947587 = 1421381) B1421381
theorem B947603 : Blo 944585 947603 := bstep (se 1 (by rfl) ⟨710702, by rfl⟩ : syracuseStep 947603 = 1421405) B1421405
theorem B947619 : Blo 944585 947619 := bstep (se 1 (by rfl) ⟨710714, by rfl⟩ : syracuseStep 947619 = 1421429) B1421429
theorem B947635 : Blo 944585 947635 := bstep (se 1 (by rfl) ⟨710726, by rfl⟩ : syracuseStep 947635 = 1421453) B1421453
theorem B947651 : Blo 944585 947651 := bstep (se 1 (by rfl) ⟨710738, by rfl⟩ : syracuseStep 947651 = 1421477) B1421477
theorem B947667 : Blo 944585 947667 := bstep (se 1 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 947667 = 1421501) B1421501
theorem B947683 : Blo 944585 947683 := bstep (se 1 (by rfl) ⟨710762, by rfl⟩ : syracuseStep 947683 = 1421525) B1421525
theorem B1799651 : Blo 944585 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B947699 : Blo 944585 947699 := bstep (se 1 (by rfl) ⟨710774, by rfl⟩ : syracuseStep 947699 = 1421549) B1421549
theorem B947715 : Blo 944585 947715 := bstep (se 1 (by rfl) ⟨710786, by rfl⟩ : syracuseStep 947715 = 1421573) B1421573
theorem B947731 : Blo 944585 947731 := bstep (se 1 (by rfl) ⟨710798, by rfl⟩ : syracuseStep 947731 = 1421597) B1421597
theorem B947747 : Blo 944585 947747 := bstep (se 1 (by rfl) ⟨710810, by rfl⟩ : syracuseStep 947747 = 1421621) B1421621
theorem B947763 : Blo 944585 947763 := bstep (se 1 (by rfl) ⟨710822, by rfl⟩ : syracuseStep 947763 = 1421645) B1421645
theorem B947779 : Blo 944585 947779 := bstep (se 1 (by rfl) ⟨710834, by rfl⟩ : syracuseStep 947779 = 1421669) B1421669
theorem B947795 : Blo 944585 947795 := bstep (se 1 (by rfl) ⟨710846, by rfl⟩ : syracuseStep 947795 = 1421693) B1421693
theorem B12285539 : Blo 944585 12285539 := bstep (se 1 (by rfl) ⟨9214154, by rfl⟩ : syracuseStep 12285539 = 18428309) B18428309
theorem B947811 : Blo 944585 947811 := bstep (se 1 (by rfl) ⟨710858, by rfl⟩ : syracuseStep 947811 = 1421717) B1421717
theorem B2127473 : Blo 944585 2127473 := bstep (se 2 (by rfl) ⟨797802, by rfl⟩ : syracuseStep 2127473 = 1595605) B1595605
theorem B947827 : Blo 944585 947827 := bstep (se 1 (by rfl) ⟨710870, by rfl⟩ : syracuseStep 947827 = 1421741) B1421741
theorem B2127491 : Blo 944585 2127491 := bstep (se 1 (by rfl) ⟨1595618, by rfl⟩ : syracuseStep 2127491 = 3191237) B3191237
theorem B947843 : Blo 944585 947843 := bstep (se 1 (by rfl) ⟨710882, by rfl⟩ : syracuseStep 947843 = 1421765) B1421765
theorem B947859 : Blo 944585 947859 := bstep (se 1 (by rfl) ⟨710894, by rfl⟩ : syracuseStep 947859 = 1421789) B1421789
theorem B947875 : Blo 944585 947875 := bstep (se 1 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 947875 = 1421813) B1421813
theorem B947891 : Blo 944585 947891 := bstep (se 1 (by rfl) ⟨710918, by rfl⟩ : syracuseStep 947891 = 1421837) B1421837
theorem B947907 : Blo 944585 947907 := bstep (se 1 (by rfl) ⟨710930, by rfl⟩ : syracuseStep 947907 = 1421861) B1421861
theorem B947923 : Blo 944585 947923 := bstep (se 1 (by rfl) ⟨710942, by rfl⟩ : syracuseStep 947923 = 1421885) B1421885
theorem B947939 : Blo 944585 947939 := bstep (se 1 (by rfl) ⟨710954, by rfl⟩ : syracuseStep 947939 = 1421909) B1421909
theorem B947955 : Blo 944585 947955 := bstep (se 1 (by rfl) ⟨710966, by rfl⟩ : syracuseStep 947955 = 1421933) B1421933
theorem B947971 : Blo 944585 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B947987 : Blo 944585 947987 := bstep (se 1 (by rfl) ⟨710990, by rfl⟩ : syracuseStep 947987 = 1421981) B1421981
theorem B948003 : Blo 944585 948003 := bstep (se 1 (by rfl) ⟨711002, by rfl⟩ : syracuseStep 948003 = 1422005) B1422005
theorem B948019 : Blo 944585 948019 := bstep (se 1 (by rfl) ⟨711014, by rfl⟩ : syracuseStep 948019 = 1422029) B1422029
theorem B948035 : Blo 944585 948035 := bstep (se 1 (by rfl) ⟨711026, by rfl⟩ : syracuseStep 948035 = 1422053) B1422053
theorem B948051 : Blo 944585 948051 := bstep (se 1 (by rfl) ⟨711038, by rfl⟩ : syracuseStep 948051 = 1422077) B1422077
theorem B948067 : Blo 944585 948067 := bstep (se 1 (by rfl) ⟨711050, by rfl⟩ : syracuseStep 948067 = 1422101) B1422101
theorem B2553713 : Blo 944585 2553713 := bstep (se 2 (by rfl) ⟨957642, by rfl⟩ : syracuseStep 2553713 = 1915285) B1915285
theorem B948083 : Blo 944585 948083 := bstep (se 1 (by rfl) ⟨711062, by rfl⟩ : syracuseStep 948083 = 1422125) B1422125
theorem B948099 : Blo 944585 948099 := bstep (se 1 (by rfl) ⟨711074, by rfl⟩ : syracuseStep 948099 = 1422149) B1422149
theorem B2127761 : Blo 944585 2127761 := bstep (se 2 (by rfl) ⟨797910, by rfl⟩ : syracuseStep 2127761 = 1595821) B1595821
theorem B948115 : Blo 944585 948115 := bstep (se 1 (by rfl) ⟨711086, by rfl⟩ : syracuseStep 948115 = 1422173) B1422173
theorem B2127779 : Blo 944585 2127779 := bstep (se 1 (by rfl) ⟨1595834, by rfl⟩ : syracuseStep 2127779 = 3191669) B3191669
theorem B948131 : Blo 944585 948131 := bstep (se 1 (by rfl) ⟨711098, by rfl⟩ : syracuseStep 948131 = 1422197) B1422197
theorem B948147 : Blo 944585 948147 := bstep (se 1 (by rfl) ⟨711110, by rfl⟩ : syracuseStep 948147 = 1422221) B1422221
theorem B948163 : Blo 944585 948163 := bstep (se 1 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 948163 = 1422245) B1422245
theorem B948179 : Blo 944585 948179 := bstep (se 1 (by rfl) ⟨711134, by rfl⟩ : syracuseStep 948179 = 1422269) B1422269
theorem B948195 : Blo 944585 948195 := bstep (se 1 (by rfl) ⟨711146, by rfl⟩ : syracuseStep 948195 = 1422293) B1422293
theorem B948211 : Blo 944585 948211 := bstep (se 1 (by rfl) ⟨711158, by rfl⟩ : syracuseStep 948211 = 1422317) B1422317
theorem B948227 : Blo 944585 948227 := bstep (se 1 (by rfl) ⟨711170, by rfl⟩ : syracuseStep 948227 = 1422341) B1422341
theorem B948243 : Blo 944585 948243 := bstep (se 1 (by rfl) ⟨711182, by rfl⟩ : syracuseStep 948243 = 1422365) B1422365
theorem B948259 : Blo 944585 948259 := bstep (se 1 (by rfl) ⟨711194, by rfl⟩ : syracuseStep 948259 = 1422389) B1422389
theorem B948275 : Blo 944585 948275 := bstep (se 1 (by rfl) ⟨711206, by rfl⟩ : syracuseStep 948275 = 1422413) B1422413
theorem B948291 : Blo 944585 948291 := bstep (se 1 (by rfl) ⟨711218, by rfl⟩ : syracuseStep 948291 = 1422437) B1422437
theorem B6486085 : Blo 944585 6486085 := bstep (se 4 (by rfl) ⟨608070, by rfl⟩ : syracuseStep 6486085 = 1216141) B1216141
theorem B6060109 : Blo 944585 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B948307 : Blo 944585 948307 := bstep (se 1 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 948307 = 1422461) B1422461
theorem B948323 : Blo 944585 948323 := bstep (se 1 (by rfl) ⟨711242, by rfl⟩ : syracuseStep 948323 = 1422485) B1422485
theorem B948339 : Blo 944585 948339 := bstep (se 1 (by rfl) ⟨711254, by rfl⟩ : syracuseStep 948339 = 1422509) B1422509
theorem B948355 : Blo 944585 948355 := bstep (se 1 (by rfl) ⟨711266, by rfl⟩ : syracuseStep 948355 = 1422533) B1422533
theorem B948371 : Blo 944585 948371 := bstep (se 1 (by rfl) ⟨711278, by rfl⟩ : syracuseStep 948371 = 1422557) B1422557
theorem B948387 : Blo 944585 948387 := bstep (se 1 (by rfl) ⟨711290, by rfl⟩ : syracuseStep 948387 = 1422581) B1422581
theorem B2128049 : Blo 944585 2128049 := bstep (se 2 (by rfl) ⟨798018, by rfl⟩ : syracuseStep 2128049 = 1596037) B1596037
theorem B948403 : Blo 944585 948403 := bstep (se 1 (by rfl) ⟨711302, by rfl⟩ : syracuseStep 948403 = 1422605) B1422605
theorem B2128067 : Blo 944585 2128067 := bstep (se 1 (by rfl) ⟨1596050, by rfl⟩ : syracuseStep 2128067 = 3192101) B3192101
theorem B948419 : Blo 944585 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B948435 : Blo 944585 948435 := bstep (se 1 (by rfl) ⟨711326, by rfl⟩ : syracuseStep 948435 = 1422653) B1422653
theorem B948451 : Blo 944585 948451 := bstep (se 1 (by rfl) ⟨711338, by rfl⟩ : syracuseStep 948451 = 1422677) B1422677
theorem B948467 : Blo 944585 948467 := bstep (se 1 (by rfl) ⟨711350, by rfl⟩ : syracuseStep 948467 = 1422701) B1422701
theorem B948483 : Blo 944585 948483 := bstep (se 1 (by rfl) ⟨711362, by rfl⟩ : syracuseStep 948483 = 1422725) B1422725
theorem B948499 : Blo 944585 948499 := bstep (se 1 (by rfl) ⟨711374, by rfl⟩ : syracuseStep 948499 = 1422749) B1422749
theorem B948515 : Blo 944585 948515 := bstep (se 1 (by rfl) ⟨711386, by rfl⟩ : syracuseStep 948515 = 1422773) B1422773
theorem B948531 : Blo 944585 948531 := bstep (se 1 (by rfl) ⟨711398, by rfl⟩ : syracuseStep 948531 = 1422797) B1422797
theorem B948547 : Blo 944585 948547 := bstep (se 1 (by rfl) ⟨711410, by rfl⟩ : syracuseStep 948547 = 1422821) B1422821
theorem B948563 : Blo 944585 948563 := bstep (se 1 (by rfl) ⟨711422, by rfl⟩ : syracuseStep 948563 = 1422845) B1422845
theorem B948579 : Blo 944585 948579 := bstep (se 1 (by rfl) ⟨711434, by rfl⟩ : syracuseStep 948579 = 1422869) B1422869
theorem B10778993 : Blo 944585 10778993 := bstep (se 2 (by rfl) ⟨4042122, by rfl⟩ : syracuseStep 10778993 = 8084245) B8084245
theorem B2161027 : Blo 944585 2161027 := bstep (se 1 (by rfl) ⟨1620770, by rfl⟩ : syracuseStep 2161027 = 3241541) B3241541
theorem B2128337 : Blo 944585 2128337 := bstep (se 2 (by rfl) ⟨798126, by rfl⟩ : syracuseStep 2128337 = 1596253) B1596253
theorem B4782563 : Blo 944585 4782563 := bstep (se 1 (by rfl) ⟨3586922, by rfl⟩ : syracuseStep 4782563 = 7173845) B7173845
theorem B2128355 : Blo 944585 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B1800721 : Blo 944585 1800721 := bstep (se 2 (by rfl) ⟨675270, by rfl⟩ : syracuseStep 1800721 = 1350541) B1350541
theorem B2128625 : Blo 944585 2128625 := bstep (se 2 (by rfl) ⟨798234, by rfl⟩ : syracuseStep 2128625 = 1596469) B1596469
theorem B2128643 : Blo 944585 2128643 := bstep (se 1 (by rfl) ⟨1596482, by rfl⟩ : syracuseStep 2128643 = 3192965) B3192965
theorem B1702705 : Blo 944585 1702705 := bstep (se 2 (by rfl) ⟨638514, by rfl⟩ : syracuseStep 1702705 = 1277029) B1277029
theorem B2882413 : Blo 944585 2882413 := bstep (se 3 (by rfl) ⟨540452, by rfl⟩ : syracuseStep 2882413 = 1080905) B1080905
theorem B1702865 : Blo 944585 1702865 := bstep (se 2 (by rfl) ⟨638574, by rfl⟩ : syracuseStep 1702865 = 1277149) B1277149
theorem B2128913 : Blo 944585 2128913 := bstep (se 2 (by rfl) ⟨798342, by rfl⟩ : syracuseStep 2128913 = 1596685) B1596685
theorem B2128931 : Blo 944585 2128931 := bstep (se 1 (by rfl) ⟨1596698, by rfl⟩ : syracuseStep 2128931 = 3193397) B3193397
theorem B1277137 : Blo 944585 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B4783373 : Blo 944585 4783373 := bstep (se 3 (by rfl) ⟨896882, by rfl⟩ : syracuseStep 4783373 = 1793765) B1793765
theorem B1277203 : Blo 944585 1277203 := bstep (se 1 (by rfl) ⟨957902, by rfl⟩ : syracuseStep 1277203 = 1915805) B1915805
theorem B2129201 : Blo 944585 2129201 := bstep (se 2 (by rfl) ⟨798450, by rfl⟩ : syracuseStep 2129201 = 1596901) B1596901
theorem B2129219 : Blo 944585 2129219 := bstep (se 1 (by rfl) ⟨1596914, by rfl⟩ : syracuseStep 2129219 = 3193829) B3193829
theorem B2129489 : Blo 944585 2129489 := bstep (se 2 (by rfl) ⟨798558, by rfl⟩ : syracuseStep 2129489 = 1597117) B1597117
theorem B1277537 : Blo 944585 1277537 := bstep (se 2 (by rfl) ⟨479076, by rfl⟩ : syracuseStep 1277537 = 958153) B958153
theorem B9698915 : Blo 944585 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B2129507 : Blo 944585 2129507 := bstep (se 1 (by rfl) ⟨1597130, by rfl⟩ : syracuseStep 2129507 = 3194261) B3194261
theorem B2391889 : Blo 944585 2391889 := bstep (se 2 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 2391889 = 1793917) B1793917
theorem B2129777 : Blo 944585 2129777 := bstep (se 2 (by rfl) ⟨798666, by rfl⟩ : syracuseStep 2129777 = 1597333) B1597333
theorem B2129795 : Blo 944585 2129795 := bstep (se 1 (by rfl) ⟨1597346, by rfl⟩ : syracuseStep 2129795 = 3194693) B3194693
theorem B13828067 : Blo 944585 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B2129921 : Blo 944585 2129921 := bstep (se 2 (by rfl) ⟨798720, by rfl⟩ : syracuseStep 2129921 = 1597441) B1597441
theorem B18219077 : Blo 944585 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B4325521 : Blo 944585 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B1704089 : Blo 944585 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B3408065 : Blo 944585 3408065 := bstep (se 2 (by rfl) ⟨1278024, by rfl⟩ : syracuseStep 3408065 = 2556049) B2556049
theorem B4784345 : Blo 944585 4784345 := bstep (se 2 (by rfl) ⟨1794129, by rfl⟩ : syracuseStep 4784345 = 3588259) B3588259
theorem B2130137 : Blo 944585 2130137 := bstep (se 2 (by rfl) ⟨798801, by rfl⟩ : syracuseStep 2130137 = 1597603) B1597603
theorem B2130227 : Blo 944585 2130227 := bstep (se 1 (by rfl) ⟨1597670, by rfl⟩ : syracuseStep 2130227 = 3195341) B3195341
theorem B2130263 : Blo 944585 2130263 := bstep (se 1 (by rfl) ⟨1597697, by rfl⟩ : syracuseStep 2130263 = 3195395) B3195395
theorem B6488471 : Blo 944585 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B2392537 : Blo 944585 2392537 := bstep (se 2 (by rfl) ⟨897201, by rfl⟩ : syracuseStep 2392537 = 1794403) B1794403
theorem B2163161 : Blo 944585 2163161 := bstep (se 2 (by rfl) ⟨811185, by rfl⟩ : syracuseStep 2163161 = 1622371) B1622371
theorem B2130443 : Blo 944585 2130443 := bstep (se 1 (by rfl) ⟨1597832, by rfl⟩ : syracuseStep 2130443 = 3195665) B3195665
theorem B15368717 : Blo 944585 15368717 := bstep (se 3 (by rfl) ⟨2881634, by rfl⟩ : syracuseStep 15368717 = 5763269) B5763269
theorem B2556481 : Blo 944585 2556481 := bstep (se 2 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 2556481 = 1917361) B1917361
theorem B2130497 : Blo 944585 2130497 := bstep (se 2 (by rfl) ⟨798936, by rfl⟩ : syracuseStep 2130497 = 1597873) B1597873
theorem B3834461 : Blo 944585 3834461 := bstep (se 3 (by rfl) ⟨718961, by rfl⟩ : syracuseStep 3834461 = 1437923) B1437923
theorem B2130713 : Blo 944585 2130713 := bstep (se 2 (by rfl) ⟨799017, by rfl⟩ : syracuseStep 2130713 = 1598035) B1598035
theorem B2130803 : Blo 944585 2130803 := bstep (se 1 (by rfl) ⟨1598102, by rfl⟩ : syracuseStep 2130803 = 3196205) B3196205
theorem B2130839 : Blo 944585 2130839 := bstep (se 1 (by rfl) ⟨1598129, by rfl⟩ : syracuseStep 2130839 = 3196259) B3196259
theorem B1704883 : Blo 944585 1704883 := bstep (se 1 (by rfl) ⟨1278662, by rfl⟩ : syracuseStep 1704883 = 2557325) B2557325
theorem B5473241 : Blo 944585 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B2131019 : Blo 944585 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B2131073 : Blo 944585 2131073 := bstep (se 2 (by rfl) ⟨799152, by rfl⟩ : syracuseStep 2131073 = 1598305) B1598305
theorem B2131289 : Blo 944585 2131289 := bstep (se 2 (by rfl) ⟨799233, by rfl⟩ : syracuseStep 2131289 = 1598467) B1598467
theorem B2131379 : Blo 944585 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B1344971 : Blo 944585 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B2131415 : Blo 944585 2131415 := bstep (se 1 (by rfl) ⟨1598561, by rfl⟩ : syracuseStep 2131415 = 3197123) B3197123
theorem B7177733 : Blo 944585 7177733 := bstep (se 4 (by rfl) ⟨672912, by rfl⟩ : syracuseStep 7177733 = 1345825) B1345825
theorem B2393651 : Blo 944585 2393651 := bstep (se 1 (by rfl) ⟨1795238, by rfl⟩ : syracuseStep 2393651 = 3590477) B3590477
theorem B2131595 : Blo 944585 2131595 := bstep (se 1 (by rfl) ⟨1598696, by rfl⟩ : syracuseStep 2131595 = 3197393) B3197393
theorem B2131649 : Blo 944585 2131649 := bstep (se 2 (by rfl) ⟨799368, by rfl⟩ : syracuseStep 2131649 = 1598737) B1598737
theorem B4785965 : Blo 944585 4785965 := bstep (se 3 (by rfl) ⟨897368, by rfl⟩ : syracuseStep 4785965 = 1794737) B1794737
theorem B2393945 : Blo 944585 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B2131865 : Blo 944585 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B2131955 : Blo 944585 2131955 := bstep (se 1 (by rfl) ⟨1598966, by rfl⟩ : syracuseStep 2131955 = 3197933) B3197933
theorem B2131991 : Blo 944585 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B30738467 : Blo 944585 30738467 := bstep (se 1 (by rfl) ⟨23053850, by rfl⟩ : syracuseStep 30738467 = 46107701) B46107701
theorem B4851757 : Blo 944585 4851757 := bstep (se 3 (by rfl) ⟨909704, by rfl⟩ : syracuseStep 4851757 = 1819409) B1819409
theorem B2132171 : Blo 944585 2132171 := bstep (se 1 (by rfl) ⟨1599128, by rfl⟩ : syracuseStep 2132171 = 3198257) B3198257
theorem B655591637 : Blo 944585 655591637 := bstep (se 7 (by rfl) ⟨7682714, by rfl⟩ : syracuseStep 655591637 = 15365429) B15365429
theorem B2132225 : Blo 944585 2132225 := bstep (se 2 (by rfl) ⟨799584, by rfl⟩ : syracuseStep 2132225 = 1599169) B1599169
theorem B1214807 : Blo 944585 1214807 := bstep (se 1 (by rfl) ⟨911105, by rfl⟩ : syracuseStep 1214807 = 1822211) B1822211
theorem B2132441 : Blo 944585 2132441 := bstep (se 2 (by rfl) ⟨799665, by rfl⟩ : syracuseStep 2132441 = 1599331) B1599331
theorem B1706483 : Blo 944585 1706483 := bstep (se 1 (by rfl) ⟨1279862, by rfl⟩ : syracuseStep 1706483 = 2559725) B2559725
theorem B2132531 : Blo 944585 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B2132567 : Blo 944585 2132567 := bstep (se 1 (by rfl) ⟨1599425, by rfl⟩ : syracuseStep 2132567 = 3198851) B3198851
theorem B1280651 : Blo 944585 1280651 := bstep (se 1 (by rfl) ⟨960488, by rfl⟩ : syracuseStep 1280651 = 1920977) B1920977
theorem B7670477 : Blo 944585 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B2132747 : Blo 944585 2132747 := bstep (se 1 (by rfl) ⟨1599560, by rfl⟩ : syracuseStep 2132747 = 3199121) B3199121
theorem B3836717 : Blo 944585 3836717 := bstep (se 3 (by rfl) ⟨719384, by rfl⟩ : syracuseStep 3836717 = 1438769) B1438769
theorem B11209537 : Blo 944585 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B2132801 : Blo 944585 2132801 := bstep (se 2 (by rfl) ⟨799800, by rfl⟩ : syracuseStep 2132801 = 1599601) B1599601
theorem B2133017 : Blo 944585 2133017 := bstep (se 2 (by rfl) ⟨799881, by rfl⟩ : syracuseStep 2133017 = 1599763) B1599763
theorem B2133107 : Blo 944585 2133107 := bstep (se 1 (by rfl) ⟨1599830, by rfl⟩ : syracuseStep 2133107 = 3199661) B3199661
theorem B2133143 : Blo 944585 2133143 := bstep (se 1 (by rfl) ⟨1599857, by rfl⟩ : syracuseStep 2133143 = 3199715) B3199715
theorem B2133323 : Blo 944585 2133323 := bstep (se 1 (by rfl) ⟨1599992, by rfl⟩ : syracuseStep 2133323 = 3199985) B3199985
theorem B2133377 : Blo 944585 2133377 := bstep (se 2 (by rfl) ⟨800016, by rfl⟩ : syracuseStep 2133377 = 1600033) B1600033
theorem B2690455 : Blo 944585 2690455 := bstep (se 1 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 2690455 = 4035683) B4035683
theorem B2395595 : Blo 944585 2395595 := bstep (se 1 (by rfl) ⟨1796696, by rfl⟩ : syracuseStep 2395595 = 3593393) B3593393
theorem B2133593 : Blo 944585 2133593 := bstep (se 2 (by rfl) ⟨800097, by rfl⟩ : syracuseStep 2133593 = 1600195) B1600195
theorem B2133683 : Blo 944585 2133683 := bstep (se 1 (by rfl) ⟨1600262, by rfl⟩ : syracuseStep 2133683 = 3200525) B3200525
theorem B2133719 : Blo 944585 2133719 := bstep (se 1 (by rfl) ⟨1600289, by rfl⟩ : syracuseStep 2133719 = 3200579) B3200579
theorem B29200193 : Blo 944585 29200193 := bstep (se 2 (by rfl) ⟨10950072, by rfl⟩ : syracuseStep 29200193 = 21900145) B21900145
theorem B2559833 : Blo 944585 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B7180163 : Blo 944585 7180163 := bstep (se 1 (by rfl) ⟨5385122, by rfl⟩ : syracuseStep 7180163 = 10770245) B10770245
theorem B2133899 : Blo 944585 2133899 := bstep (se 1 (by rfl) ⟨1600424, by rfl⟩ : syracuseStep 2133899 = 3200849) B3200849
theorem B15175603 : Blo 944585 15175603 := bstep (se 1 (by rfl) ⟨11381702, by rfl⟩ : syracuseStep 15175603 = 22763405) B22763405
theorem B2133953 : Blo 944585 2133953 := bstep (se 2 (by rfl) ⟨800232, by rfl⟩ : syracuseStep 2133953 = 1600465) B1600465
theorem B3412043 : Blo 944585 3412043 := bstep (se 1 (by rfl) ⟨2559032, by rfl⟩ : syracuseStep 3412043 = 5118065) B5118065
theorem B2134169 : Blo 944585 2134169 := bstep (se 2 (by rfl) ⟨800313, by rfl⟩ : syracuseStep 2134169 = 1600627) B1600627
theorem B2134259 : Blo 944585 2134259 := bstep (se 1 (by rfl) ⟨1600694, by rfl⟩ : syracuseStep 2134259 = 3201389) B3201389
theorem B2134295 : Blo 944585 2134295 := bstep (se 1 (by rfl) ⟨1600721, by rfl⟩ : syracuseStep 2134295 = 3201443) B3201443
theorem B4034947 : Blo 944585 4034947 := bstep (se 1 (by rfl) ⟨3026210, by rfl⟩ : syracuseStep 4034947 = 6052421) B6052421
theorem B2396567 : Blo 944585 2396567 := bstep (se 1 (by rfl) ⟨1797425, by rfl⟩ : syracuseStep 2396567 = 3594851) B3594851
theorem B28381789 : Blo 944585 28381789 := bstep (se 3 (by rfl) ⟨5321585, by rfl⟩ : syracuseStep 28381789 = 10643171) B10643171
theorem B2691787 : Blo 944585 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B4920281 : Blo 944585 4920281 := bstep (se 2 (by rfl) ⟨1845105, by rfl⟩ : syracuseStep 4920281 = 3690211) B3690211
theorem B2692061 : Blo 944585 2692061 := bstep (se 3 (by rfl) ⟨504761, by rfl⟩ : syracuseStep 2692061 = 1009523) B1009523
theorem B16192547 : Blo 944585 16192547 := bstep (se 1 (by rfl) ⟨12144410, by rfl⟩ : syracuseStep 16192547 = 24288821) B24288821
theorem B2397235 : Blo 944585 2397235 := bstep (se 1 (by rfl) ⟨1797926, by rfl⟩ : syracuseStep 2397235 = 3595853) B3595853
theorem B3839051 : Blo 944585 3839051 := bstep (se 1 (by rfl) ⟨2879288, by rfl⟩ : syracuseStep 3839051 = 5758577) B5758577
theorem B3642499 : Blo 944585 3642499 := bstep (se 1 (by rfl) ⟨2731874, by rfl⟩ : syracuseStep 3642499 = 5463749) B5463749
theorem B2397377 : Blo 944585 2397377 := bstep (se 2 (by rfl) ⟨899016, by rfl⟩ : syracuseStep 2397377 = 1798033) B1798033
theorem B2692403 : Blo 944585 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B4035905 : Blo 944585 4035905 := bstep (se 2 (by rfl) ⟨1513464, by rfl⟩ : syracuseStep 4035905 = 3026929) B3026929
theorem B4789853 : Blo 944585 4789853 := bstep (se 3 (by rfl) ⟨898097, by rfl⟩ : syracuseStep 4789853 = 1796195) B1796195
theorem B2561843 : Blo 944585 2561843 := bstep (se 1 (by rfl) ⟨1921382, by rfl⟩ : syracuseStep 2561843 = 3842765) B3842765
theorem B17536945 : Blo 944585 17536945 := bstep (se 2 (by rfl) ⟨6576354, by rfl⟩ : syracuseStep 17536945 = 13152709) B13152709
theorem B1579225 : Blo 944585 1579225 := bstep (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) B1184419
theorem B8100101 : Blo 944585 8100101 := bstep (se 4 (by rfl) ⟨759384, by rfl⟩ : syracuseStep 8100101 = 1518769) B1518769
theorem B2398643 : Blo 944585 2398643 := bstep (se 1 (by rfl) ⟨1798982, by rfl⟩ : syracuseStep 2398643 = 3597965) B3597965
theorem B1350103 : Blo 944585 1350103 := bstep (se 1 (by rfl) ⟨1012577, by rfl⟩ : syracuseStep 1350103 = 2025155) B2025155
theorem B4037323 : Blo 944585 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B2399179 : Blo 944585 2399179 := bstep (se 1 (by rfl) ⟨1799384, by rfl⟩ : syracuseStep 2399179 = 3598769) B3598769
theorem B4037597 : Blo 944585 4037597 := bstep (se 3 (by rfl) ⟨757049, by rfl⟩ : syracuseStep 4037597 = 1514099) B1514099
theorem B2399321 : Blo 944585 2399321 := bstep (se 2 (by rfl) ⟨899745, by rfl⟩ : syracuseStep 2399321 = 1799491) B1799491
theorem B7183565 : Blo 944585 7183565 := bstep (se 3 (by rfl) ⟨1346918, by rfl⟩ : syracuseStep 7183565 = 2693837) B2693837
theorem B18455813 : Blo 944585 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B2563379 : Blo 944585 2563379 := bstep (se 1 (by rfl) ⟨1922534, by rfl⟩ : syracuseStep 2563379 = 3845069) B3845069
theorem B2694475 : Blo 944585 2694475 := bstep (se 1 (by rfl) ⟨2020856, by rfl⟩ : syracuseStep 2694475 = 4041713) B4041713
theorem B4791959 : Blo 944585 4791959 := bstep (se 1 (by rfl) ⟨3593969, by rfl⟩ : syracuseStep 4791959 = 7187939) B7187939
theorem B7184051 : Blo 944585 7184051 := bstep (se 1 (by rfl) ⟨5388038, by rfl⟩ : syracuseStep 7184051 = 10776077) B10776077
theorem B1416971 : Blo 944585 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B1416983 : Blo 944585 1416983 := bstep (se 1 (by rfl) ⟨1062737, by rfl⟩ : syracuseStep 1416983 = 2125475) B2125475
theorem B2694977 : Blo 944585 2694977 := bstep (se 2 (by rfl) ⟨1010616, by rfl⟩ : syracuseStep 2694977 = 2021233) B2021233
theorem B1417049 : Blo 944585 1417049 := bstep (se 2 (by rfl) ⟨531393, by rfl⟩ : syracuseStep 1417049 = 1062787) B1062787
theorem B2400151 : Blo 944585 2400151 := bstep (se 1 (by rfl) ⟨1800113, by rfl⟩ : syracuseStep 2400151 = 3600227) B3600227
theorem B1417163 : Blo 944585 1417163 := bstep (se 1 (by rfl) ⟨1062872, by rfl⟩ : syracuseStep 1417163 = 2125745) B2125745
theorem B1417175 : Blo 944585 1417175 := bstep (se 1 (by rfl) ⟨1062881, by rfl⟩ : syracuseStep 1417175 = 2125763) B2125763
theorem B1417241 : Blo 944585 1417241 := bstep (se 2 (by rfl) ⟨531465, by rfl⟩ : syracuseStep 1417241 = 1062931) B1062931
theorem B1417355 : Blo 944585 1417355 := bstep (se 1 (by rfl) ⟨1063016, by rfl⟩ : syracuseStep 1417355 = 2126033) B2126033
theorem B1417367 : Blo 944585 1417367 := bstep (se 1 (by rfl) ⟨1063025, by rfl⟩ : syracuseStep 1417367 = 2126051) B2126051
theorem B2695319 : Blo 944585 2695319 := bstep (se 1 (by rfl) ⟨2021489, by rfl⟩ : syracuseStep 2695319 = 4042979) B4042979
theorem B1384651 : Blo 944585 1384651 := bstep (se 1 (by rfl) ⟨1038488, by rfl⟩ : syracuseStep 1384651 = 2076977) B2076977
theorem B1417433 : Blo 944585 1417433 := bstep (se 2 (by rfl) ⟨531537, by rfl⟩ : syracuseStep 1417433 = 1063075) B1063075
theorem B1417547 : Blo 944585 1417547 := bstep (se 1 (by rfl) ⟨1063160, by rfl⟩ : syracuseStep 1417547 = 2126321) B2126321
theorem B2400587 : Blo 944585 2400587 := bstep (se 1 (by rfl) ⟨1800440, by rfl⟩ : syracuseStep 2400587 = 3600881) B3600881
theorem B1417559 : Blo 944585 1417559 := bstep (se 1 (by rfl) ⟨1063169, by rfl⟩ : syracuseStep 1417559 = 2126339) B2126339
theorem B1417625 : Blo 944585 1417625 := bstep (se 2 (by rfl) ⟨531609, by rfl⟩ : syracuseStep 1417625 = 1063219) B1063219
theorem B1417739 : Blo 944585 1417739 := bstep (se 1 (by rfl) ⟨1063304, by rfl⟩ : syracuseStep 1417739 = 2126609) B2126609
theorem B1417751 : Blo 944585 1417751 := bstep (se 1 (by rfl) ⟨1063313, by rfl⟩ : syracuseStep 1417751 = 2126627) B2126627
theorem B1417817 : Blo 944585 1417817 := bstep (se 2 (by rfl) ⟨531681, by rfl⟩ : syracuseStep 1417817 = 1063363) B1063363
theorem B959159 : Blo 944585 959159 := bstep (se 1 (by rfl) ⟨719369, by rfl⟩ : syracuseStep 959159 = 1438739) B1438739
theorem B2400961 : Blo 944585 2400961 := bstep (se 2 (by rfl) ⟨900360, by rfl⟩ : syracuseStep 2400961 = 1800721) B1800721
theorem B1417931 : Blo 944585 1417931 := bstep (se 1 (by rfl) ⟨1063448, by rfl⟩ : syracuseStep 1417931 = 2126897) B2126897
theorem B1417943 : Blo 944585 1417943 := bstep (se 1 (by rfl) ⟨1063457, by rfl⟩ : syracuseStep 1417943 = 2126915) B2126915
theorem B1418009 : Blo 944585 1418009 := bstep (se 2 (by rfl) ⟨531753, by rfl⟩ : syracuseStep 1418009 = 1063507) B1063507
theorem B1418123 : Blo 944585 1418123 := bstep (se 1 (by rfl) ⟨1063592, by rfl⟩ : syracuseStep 1418123 = 2127185) B2127185
theorem B1418135 : Blo 944585 1418135 := bstep (se 1 (by rfl) ⟨1063601, by rfl⟩ : syracuseStep 1418135 = 2127203) B2127203
theorem B1418201 : Blo 944585 1418201 := bstep (se 2 (by rfl) ⟨531825, by rfl⟩ : syracuseStep 1418201 = 1063651) B1063651
theorem B6825005 : Blo 944585 6825005 := bstep (se 3 (by rfl) ⟨1279688, by rfl⟩ : syracuseStep 6825005 = 2559377) B2559377
theorem B2270273 : Blo 944585 2270273 := bstep (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) B1702705
theorem B1418315 : Blo 944585 1418315 := bstep (se 1 (by rfl) ⟨1063736, by rfl⟩ : syracuseStep 1418315 = 2127473) B2127473
theorem B1418327 : Blo 944585 1418327 := bstep (se 1 (by rfl) ⟨1063745, by rfl⟩ : syracuseStep 1418327 = 2127491) B2127491
theorem B7185509 : Blo 944585 7185509 := bstep (se 4 (by rfl) ⟨673641, by rfl⟩ : syracuseStep 7185509 = 1347283) B1347283
theorem B3843217 : Blo 944585 3843217 := bstep (se 2 (by rfl) ⟨1441206, by rfl⟩ : syracuseStep 3843217 = 2882413) B2882413
theorem B1418393 : Blo 944585 1418393 := bstep (se 2 (by rfl) ⟨531897, by rfl⟩ : syracuseStep 1418393 = 1063795) B1063795
theorem B1418507 : Blo 944585 1418507 := bstep (se 1 (by rfl) ⟨1063880, by rfl⟩ : syracuseStep 1418507 = 2127761) B2127761
theorem B1418519 : Blo 944585 1418519 := bstep (se 1 (by rfl) ⟨1063889, by rfl⟩ : syracuseStep 1418519 = 2127779) B2127779
theorem B1418585 : Blo 944585 1418585 := bstep (se 2 (by rfl) ⟨531969, by rfl⟩ : syracuseStep 1418585 = 1063939) B1063939
theorem B1418699 : Blo 944585 1418699 := bstep (se 1 (by rfl) ⟨1064024, by rfl⟩ : syracuseStep 1418699 = 2128049) B2128049
theorem B1418711 : Blo 944585 1418711 := bstep (se 1 (by rfl) ⟨1064033, by rfl⟩ : syracuseStep 1418711 = 2128067) B2128067
theorem B4040209 : Blo 944585 4040209 := bstep (se 2 (by rfl) ⟨1515078, by rfl⟩ : syracuseStep 4040209 = 3030157) B3030157
theorem B1418777 : Blo 944585 1418777 := bstep (se 2 (by rfl) ⟨532041, by rfl⟩ : syracuseStep 1418777 = 1064083) B1064083
theorem B7185995 : Blo 944585 7185995 := bstep (se 1 (by rfl) ⟨5389496, by rfl⟩ : syracuseStep 7185995 = 10778993) B10778993
theorem B1418891 : Blo 944585 1418891 := bstep (se 1 (by rfl) ⟨1064168, by rfl⟩ : syracuseStep 1418891 = 2128337) B2128337
theorem B3188375 : Blo 944585 3188375 := bstep (se 1 (by rfl) ⟨2391281, by rfl⟩ : syracuseStep 3188375 = 4782563) B4782563
theorem B1418903 : Blo 944585 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B1418969 : Blo 944585 1418969 := bstep (se 2 (by rfl) ⟨532113, by rfl⟩ : syracuseStep 1418969 = 1064227) B1064227
theorem B8103725 : Blo 944585 8103725 := bstep (se 3 (by rfl) ⟨1519448, by rfl⟩ : syracuseStep 8103725 = 3038897) B3038897
theorem B1419083 : Blo 944585 1419083 := bstep (se 1 (by rfl) ⟨1064312, by rfl⟩ : syracuseStep 1419083 = 2128625) B2128625
theorem B1419095 : Blo 944585 1419095 := bstep (se 1 (by rfl) ⟨1064321, by rfl⟩ : syracuseStep 1419095 = 2128643) B2128643
theorem B5384029 : Blo 944585 5384029 := bstep (se 3 (by rfl) ⟨1009505, by rfl⟩ : syracuseStep 5384029 = 2019011) B2019011
theorem B1419161 : Blo 944585 1419161 := bstep (se 2 (by rfl) ⟨532185, by rfl⟩ : syracuseStep 1419161 = 1064371) B1064371
theorem B1419275 : Blo 944585 1419275 := bstep (se 1 (by rfl) ⟨1064456, by rfl⟩ : syracuseStep 1419275 = 2128913) B2128913
theorem B1419287 : Blo 944585 1419287 := bstep (se 1 (by rfl) ⟨1064465, by rfl⟩ : syracuseStep 1419287 = 2128931) B2128931
theorem B1517591 : Blo 944585 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B1419353 : Blo 944585 1419353 := bstep (se 2 (by rfl) ⟨532257, by rfl⟩ : syracuseStep 1419353 = 1064515) B1064515
theorem B1517719 : Blo 944585 1517719 := bstep (se 1 (by rfl) ⟨1138289, by rfl⟩ : syracuseStep 1517719 = 2276579) B2276579
theorem B3188915 : Blo 944585 3188915 := bstep (se 1 (by rfl) ⟨2391686, by rfl⟩ : syracuseStep 3188915 = 4783373) B4783373
theorem B1419467 : Blo 944585 1419467 := bstep (se 1 (by rfl) ⟨1064600, by rfl⟩ : syracuseStep 1419467 = 2129201) B2129201
theorem B1419479 : Blo 944585 1419479 := bstep (se 1 (by rfl) ⟨1064609, by rfl⟩ : syracuseStep 1419479 = 2129219) B2129219
theorem B2697437 : Blo 944585 2697437 := bstep (se 3 (by rfl) ⟨505769, by rfl⟩ : syracuseStep 2697437 = 1011539) B1011539
theorem B1419545 : Blo 944585 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B1419659 : Blo 944585 1419659 := bstep (se 1 (by rfl) ⟨1064744, by rfl⟩ : syracuseStep 1419659 = 2129489) B2129489
theorem B6465943 : Blo 944585 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B1419671 : Blo 944585 1419671 := bstep (se 1 (by rfl) ⟨1064753, by rfl⟩ : syracuseStep 1419671 = 2129507) B2129507
theorem B3189185 : Blo 944585 3189185 := bstep (se 2 (by rfl) ⟨1195944, by rfl⟩ : syracuseStep 3189185 = 2391889) B2391889
theorem B1419737 : Blo 944585 1419737 := bstep (se 2 (by rfl) ⟨532401, by rfl⟩ : syracuseStep 1419737 = 1064803) B1064803
theorem B1518103 : Blo 944585 1518103 := bstep (se 1 (by rfl) ⟨1138577, by rfl⟩ : syracuseStep 1518103 = 2277155) B2277155
theorem B2697779 : Blo 944585 2697779 := bstep (se 1 (by rfl) ⟨2023334, by rfl⟩ : syracuseStep 2697779 = 4046669) B4046669
theorem B1419851 : Blo 944585 1419851 := bstep (se 1 (by rfl) ⟨1064888, by rfl⟩ : syracuseStep 1419851 = 2129777) B2129777
theorem B1419863 : Blo 944585 1419863 := bstep (se 1 (by rfl) ⟨1064897, by rfl⟩ : syracuseStep 1419863 = 2129795) B2129795
theorem B9218711 : Blo 944585 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B1419929 : Blo 944585 1419929 := bstep (se 2 (by rfl) ⟨532473, by rfl⟩ : syracuseStep 1419929 = 1064947) B1064947
theorem B1420043 : Blo 944585 1420043 := bstep (se 1 (by rfl) ⟨1065032, by rfl⟩ : syracuseStep 1420043 = 2130065) B2130065
theorem B961291 : Blo 944585 961291 := bstep (se 1 (by rfl) ⟨720968, by rfl⟩ : syracuseStep 961291 = 1441937) B1441937
theorem B1420055 : Blo 944585 1420055 := bstep (se 1 (by rfl) ⟨1065041, by rfl⟩ : syracuseStep 1420055 = 2130083) B2130083
theorem B1518359 : Blo 944585 1518359 := bstep (se 1 (by rfl) ⟨1138769, by rfl⟩ : syracuseStep 1518359 = 2277539) B2277539
theorem B13839169 : Blo 944585 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1420121 : Blo 944585 1420121 := bstep (se 2 (by rfl) ⟨532545, by rfl⟩ : syracuseStep 1420121 = 1065091) B1065091
theorem B1420235 : Blo 944585 1420235 := bstep (se 1 (by rfl) ⟨1065176, by rfl⟩ : syracuseStep 1420235 = 2130353) B2130353
theorem B1420247 : Blo 944585 1420247 := bstep (se 1 (by rfl) ⟨1065185, by rfl⟩ : syracuseStep 1420247 = 2130371) B2130371
theorem B31075289 : Blo 944585 31075289 := bstep (se 2 (by rfl) ⟨11653233, by rfl⟩ : syracuseStep 31075289 = 23306467) B23306467
theorem B3189725 : Blo 944585 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B1420313 : Blo 944585 1420313 := bstep (se 2 (by rfl) ⟨532617, by rfl⟩ : syracuseStep 1420313 = 1065235) B1065235
theorem B4795523 : Blo 944585 4795523 := bstep (se 1 (by rfl) ⟨3596642, by rfl⟩ : syracuseStep 4795523 = 7193285) B7193285
theorem B1420427 : Blo 944585 1420427 := bstep (se 1 (by rfl) ⟨1065320, by rfl⟩ : syracuseStep 1420427 = 2130641) B2130641
theorem B18656407 : Blo 944585 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B1420439 : Blo 944585 1420439 := bstep (se 1 (by rfl) ⟨1065329, by rfl⟩ : syracuseStep 1420439 = 2130659) B2130659
theorem B1420505 : Blo 944585 1420505 := bstep (se 2 (by rfl) ⟨532689, by rfl⟩ : syracuseStep 1420505 = 1065379) B1065379
theorem B2731229 : Blo 944585 2731229 := bstep (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) B1024211
theorem B1420619 : Blo 944585 1420619 := bstep (se 1 (by rfl) ⟨1065464, by rfl⟩ : syracuseStep 1420619 = 2130929) B2130929
theorem B1518923 : Blo 944585 1518923 := bstep (se 1 (by rfl) ⟨1139192, by rfl⟩ : syracuseStep 1518923 = 2278385) B2278385
theorem B1420631 : Blo 944585 1420631 := bstep (se 1 (by rfl) ⟨1065473, by rfl⟩ : syracuseStep 1420631 = 2130947) B2130947
theorem B1420697 : Blo 944585 1420697 := bstep (se 2 (by rfl) ⟨532761, by rfl⟩ : syracuseStep 1420697 = 1065523) B1065523
theorem B2272715 : Blo 944585 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B1420811 : Blo 944585 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B1420823 : Blo 944585 1420823 := bstep (se 1 (by rfl) ⟨1065617, by rfl⟩ : syracuseStep 1420823 = 2131235) B2131235
theorem B1420889 : Blo 944585 1420889 := bstep (se 2 (by rfl) ⟨532833, by rfl⟩ : syracuseStep 1420889 = 1065667) B1065667
theorem B4992691 : Blo 944585 4992691 := bstep (se 1 (by rfl) ⟨3744518, by rfl⟩ : syracuseStep 4992691 = 7489037) B7489037
theorem B1421003 : Blo 944585 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B1421015 : Blo 944585 1421015 := bstep (se 1 (by rfl) ⟨1065761, by rfl⟩ : syracuseStep 1421015 = 2131523) B2131523
theorem B3452633 : Blo 944585 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B1421081 : Blo 944585 1421081 := bstep (se 2 (by rfl) ⟨532905, by rfl⟩ : syracuseStep 1421081 = 1065811) B1065811
theorem B1421195 : Blo 944585 1421195 := bstep (se 1 (by rfl) ⟨1065896, by rfl⟩ : syracuseStep 1421195 = 2131793) B2131793
theorem B1421207 : Blo 944585 1421207 := bstep (se 1 (by rfl) ⟨1065905, by rfl⟩ : syracuseStep 1421207 = 2131811) B2131811
theorem B1421273 : Blo 944585 1421273 := bstep (se 2 (by rfl) ⟨532977, by rfl⟩ : syracuseStep 1421273 = 1065955) B1065955
theorem B3190859 : Blo 944585 3190859 := bstep (se 1 (by rfl) ⟨2393144, by rfl⟩ : syracuseStep 3190859 = 4786289) B4786289
theorem B1421387 : Blo 944585 1421387 := bstep (se 1 (by rfl) ⟨1066040, by rfl⟩ : syracuseStep 1421387 = 2132081) B2132081
theorem B1421399 : Blo 944585 1421399 := bstep (se 1 (by rfl) ⟨1066049, by rfl⟩ : syracuseStep 1421399 = 2132099) B2132099
theorem B1421465 : Blo 944585 1421465 := bstep (se 2 (by rfl) ⟨533049, by rfl⟩ : syracuseStep 1421465 = 1066099) B1066099
theorem B6828209 : Blo 944585 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B6828293 : Blo 944585 6828293 := bstep (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) B1280305
theorem B1421579 : Blo 944585 1421579 := bstep (se 1 (by rfl) ⟨1066184, by rfl⟩ : syracuseStep 1421579 = 2132369) B2132369
theorem B1421591 : Blo 944585 1421591 := bstep (se 1 (by rfl) ⟨1066193, by rfl⟩ : syracuseStep 1421591 = 2132387) B2132387
theorem B3191129 : Blo 944585 3191129 := bstep (se 2 (by rfl) ⟨1196673, by rfl⟩ : syracuseStep 3191129 = 2393347) B2393347
theorem B1421657 : Blo 944585 1421657 := bstep (se 2 (by rfl) ⟨533121, by rfl⟩ : syracuseStep 1421657 = 1066243) B1066243
theorem B1421771 : Blo 944585 1421771 := bstep (se 1 (by rfl) ⟨1066328, by rfl⟩ : syracuseStep 1421771 = 2132657) B2132657
theorem B1421783 : Blo 944585 1421783 := bstep (se 1 (by rfl) ⟨1066337, by rfl⟩ : syracuseStep 1421783 = 2132675) B2132675
theorem B1421849 : Blo 944585 1421849 := bstep (se 2 (by rfl) ⟨533193, by rfl⟩ : syracuseStep 1421849 = 1066387) B1066387
theorem B4043353 : Blo 944585 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B1421963 : Blo 944585 1421963 := bstep (se 1 (by rfl) ⟨1066472, by rfl⟩ : syracuseStep 1421963 = 2132945) B2132945
theorem B6828695 : Blo 944585 6828695 := bstep (se 1 (by rfl) ⟨5121521, by rfl⟩ : syracuseStep 6828695 = 10243043) B10243043
theorem B1421975 : Blo 944585 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B1422041 : Blo 944585 1422041 := bstep (se 2 (by rfl) ⟨533265, by rfl⟩ : syracuseStep 1422041 = 1066531) B1066531
theorem B1422155 : Blo 944585 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1422167 : Blo 944585 1422167 := bstep (se 1 (by rfl) ⟨1066625, by rfl⟩ : syracuseStep 1422167 = 2133251) B2133251
theorem B2700125 : Blo 944585 2700125 := bstep (se 3 (by rfl) ⟨506273, by rfl⟩ : syracuseStep 2700125 = 1012547) B1012547
theorem B1422233 : Blo 944585 1422233 := bstep (se 2 (by rfl) ⟨533337, by rfl⟩ : syracuseStep 1422233 = 1066675) B1066675
theorem B3650507 : Blo 944585 3650507 := bstep (se 1 (by rfl) ⟨2737880, by rfl⟩ : syracuseStep 3650507 = 5475761) B5475761
theorem B1422347 : Blo 944585 1422347 := bstep (se 1 (by rfl) ⟨1066760, by rfl⟩ : syracuseStep 1422347 = 2133521) B2133521
theorem B3191831 : Blo 944585 3191831 := bstep (se 1 (by rfl) ⟨2393873, by rfl⟩ : syracuseStep 3191831 = 4787747) B4787747
theorem B1422359 : Blo 944585 1422359 := bstep (se 1 (by rfl) ⟨1066769, by rfl⟩ : syracuseStep 1422359 = 2133539) B2133539
theorem B2700353 : Blo 944585 2700353 := bstep (se 2 (by rfl) ⟨1012632, by rfl⟩ : syracuseStep 2700353 = 2025265) B2025265
theorem B1422425 : Blo 944585 1422425 := bstep (se 2 (by rfl) ⟨533409, by rfl⟩ : syracuseStep 1422425 = 1066819) B1066819
theorem B4043969 : Blo 944585 4043969 := bstep (se 2 (by rfl) ⟨1516488, by rfl⟩ : syracuseStep 4043969 = 3032977) B3032977
theorem B1422539 : Blo 944585 1422539 := bstep (se 1 (by rfl) ⟨1066904, by rfl⟩ : syracuseStep 1422539 = 2133809) B2133809
theorem B1422551 : Blo 944585 1422551 := bstep (se 1 (by rfl) ⟨1066913, by rfl⟩ : syracuseStep 1422551 = 2133827) B2133827
theorem B1422617 : Blo 944585 1422617 := bstep (se 2 (by rfl) ⟨533481, by rfl⟩ : syracuseStep 1422617 = 1066963) B1066963
theorem B1422731 : Blo 944585 1422731 := bstep (se 1 (by rfl) ⟨1067048, by rfl⟩ : syracuseStep 1422731 = 2134097) B2134097
theorem B2700695 : Blo 944585 2700695 := bstep (se 1 (by rfl) ⟨2025521, by rfl⟩ : syracuseStep 2700695 = 4051043) B4051043
theorem B1422743 : Blo 944585 1422743 := bstep (se 1 (by rfl) ⟨1067057, by rfl⟩ : syracuseStep 1422743 = 2134115) B2134115
theorem B3028403 : Blo 944585 3028403 := bstep (se 1 (by rfl) ⟨2271302, by rfl⟩ : syracuseStep 3028403 = 4542605) B4542605
theorem B3028441 : Blo 944585 3028441 := bstep (se 2 (by rfl) ⟨1135665, by rfl⟩ : syracuseStep 3028441 = 2271331) B2271331
theorem B1422809 : Blo 944585 1422809 := bstep (se 2 (by rfl) ⟨533553, by rfl⟩ : syracuseStep 1422809 = 1067107) B1067107
theorem B3192371 : Blo 944585 3192371 := bstep (se 1 (by rfl) ⟨2394278, by rfl⟩ : syracuseStep 3192371 = 4788557) B4788557
theorem B10368773 : Blo 944585 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B1062679 : Blo 944585 1062679 := bstep (se 1 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 1062679 = 1594019) B1594019
theorem B6076205 : Blo 944585 6076205 := bstep (se 3 (by rfl) ⟨1139288, by rfl⟩ : syracuseStep 6076205 = 2278577) B2278577
theorem B3192641 : Blo 944585 3192641 := bstep (se 2 (by rfl) ⟨1197240, by rfl⟩ : syracuseStep 3192641 = 2394481) B2394481
theorem B24262577 : Blo 944585 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B1062859 : Blo 944585 1062859 := bstep (se 1 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 1062859 = 1594289) B1594289
theorem B1062967 : Blo 944585 1062967 := bstep (se 1 (by rfl) ⟨797225, by rfl⟩ : syracuseStep 1062967 = 1594451) B1594451
theorem B1063147 : Blo 944585 1063147 := bstep (se 1 (by rfl) ⟨797360, by rfl⟩ : syracuseStep 1063147 = 1594721) B1594721
theorem B1063255 : Blo 944585 1063255 := bstep (se 1 (by rfl) ⟨797441, by rfl⟩ : syracuseStep 1063255 = 1594883) B1594883
theorem B3193181 : Blo 944585 3193181 := bstep (se 3 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 3193181 = 1197443) B1197443
theorem B11516377 : Blo 944585 11516377 := bstep (se 2 (by rfl) ⟨4318641, by rfl⟩ : syracuseStep 11516377 = 8637283) B8637283
theorem B1063435 : Blo 944585 1063435 := bstep (se 1 (by rfl) ⟨797576, by rfl⟩ : syracuseStep 1063435 = 1595153) B1595153
theorem B1063543 : Blo 944585 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B1620695 : Blo 944585 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B4799249 : Blo 944585 4799249 := bstep (se 2 (by rfl) ⟨1799718, by rfl⟩ : syracuseStep 4799249 = 3599437) B3599437
theorem B1063723 : Blo 944585 1063723 := bstep (se 1 (by rfl) ⟨797792, by rfl⟩ : syracuseStep 1063723 = 1595585) B1595585
theorem B7191341 : Blo 944585 7191341 := bstep (se 3 (by rfl) ⟨1348376, by rfl⟩ : syracuseStep 7191341 = 2696753) B2696753
theorem B1915787 : Blo 944585 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1063831 : Blo 944585 1063831 := bstep (se 1 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 1063831 = 1595747) B1595747
theorem B4799411 : Blo 944585 4799411 := bstep (se 1 (by rfl) ⟨3599558, by rfl⟩ : syracuseStep 4799411 = 7199117) B7199117
theorem B3587075 : Blo 944585 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B1621003 : Blo 944585 1621003 := bstep (se 1 (by rfl) ⟨1215752, by rfl⟩ : syracuseStep 1621003 = 2431505) B2431505
theorem B1064011 : Blo 944585 1064011 := bstep (se 1 (by rfl) ⟨798008, by rfl⟩ : syracuseStep 1064011 = 1596017) B1596017
theorem B6077591 : Blo 944585 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B1064119 : Blo 944585 1064119 := bstep (se 1 (by rfl) ⟨798089, by rfl⟩ : syracuseStep 1064119 = 1596179) B1596179
theorem B1064299 : Blo 944585 1064299 := bstep (se 1 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 1064299 = 1596449) B1596449
theorem B3194315 : Blo 944585 3194315 := bstep (se 1 (by rfl) ⟨2395736, by rfl⟩ : syracuseStep 3194315 = 4791473) B4791473
theorem B1064407 : Blo 944585 1064407 := bstep (se 1 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 1064407 = 1596611) B1596611
theorem B3456605 : Blo 944585 3456605 := bstep (se 3 (by rfl) ⟨648113, by rfl⟩ : syracuseStep 3456605 = 1296227) B1296227
theorem B4046429 : Blo 944585 4046429 := bstep (se 3 (by rfl) ⟨758705, by rfl⟩ : syracuseStep 4046429 = 1517411) B1517411
theorem B1064587 : Blo 944585 1064587 := bstep (se 1 (by rfl) ⟨798440, by rfl⟩ : syracuseStep 1064587 = 1596881) B1596881
theorem B16170677 : Blo 944585 16170677 := bstep (se 5 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 16170677 = 1516001) B1516001
theorem B3194585 : Blo 944585 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B1064695 : Blo 944585 1064695 := bstep (se 1 (by rfl) ⟨798521, by rfl⟩ : syracuseStep 1064695 = 1597043) B1597043
theorem B2309939 : Blo 944585 2309939 := bstep (se 1 (by rfl) ⟨1732454, by rfl⟩ : syracuseStep 2309939 = 3464909) B3464909
theorem B1064875 : Blo 944585 1064875 := bstep (se 1 (by rfl) ⟨798656, by rfl⟩ : syracuseStep 1064875 = 1597313) B1597313
theorem B3030977 : Blo 944585 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B1916939 : Blo 944585 1916939 := bstep (se 1 (by rfl) ⟨1437704, by rfl⟩ : syracuseStep 1916939 = 2875409) B2875409
theorem B8306705 : Blo 944585 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1064983 : Blo 944585 1064983 := bstep (se 1 (by rfl) ⟨798737, by rfl⟩ : syracuseStep 1064983 = 1597475) B1597475
theorem B22986827 : Blo 944585 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1065163 : Blo 944585 1065163 := bstep (se 1 (by rfl) ⟨798872, by rfl⟩ : syracuseStep 1065163 = 1597745) B1597745
theorem B1196299 : Blo 944585 1196299 := bstep (se 1 (by rfl) ⟨897224, by rfl⟩ : syracuseStep 1196299 = 1794449) B1794449
theorem B1065271 : Blo 944585 1065271 := bstep (se 1 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 1065271 = 1597907) B1597907
theorem B3195287 : Blo 944585 3195287 := bstep (se 1 (by rfl) ⟨2396465, by rfl⟩ : syracuseStep 3195287 = 4792931) B4792931
theorem B1065451 : Blo 944585 1065451 := bstep (se 1 (by rfl) ⟨799088, by rfl⟩ : syracuseStep 1065451 = 1598177) B1598177
theorem B1065559 : Blo 944585 1065559 := bstep (se 1 (by rfl) ⟨799169, by rfl⟩ : syracuseStep 1065559 = 1598339) B1598339
theorem B1065739 : Blo 944585 1065739 := bstep (se 1 (by rfl) ⟨799304, by rfl⟩ : syracuseStep 1065739 = 1598609) B1598609
theorem B4801355 : Blo 944585 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B3031901 : Blo 944585 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B1065847 : Blo 944585 1065847 := bstep (se 1 (by rfl) ⟨799385, by rfl⟩ : syracuseStep 1065847 = 1598771) B1598771
theorem B8078231 : Blo 944585 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B3195827 : Blo 944585 3195827 := bstep (se 1 (by rfl) ⟨2396870, by rfl⟩ : syracuseStep 3195827 = 4793741) B4793741
theorem B8111027 : Blo 944585 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B1066027 : Blo 944585 1066027 := bstep (se 1 (by rfl) ⟨799520, by rfl⟩ : syracuseStep 1066027 = 1599041) B1599041
theorem B1066135 : Blo 944585 1066135 := bstep (se 1 (by rfl) ⟨799601, by rfl⟩ : syracuseStep 1066135 = 1599203) B1599203
theorem B3196097 : Blo 944585 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B1197271 : Blo 944585 1197271 := bstep (se 1 (by rfl) ⟨897953, by rfl⟩ : syracuseStep 1197271 = 1795907) B1795907
theorem B1066315 : Blo 944585 1066315 := bstep (se 1 (by rfl) ⟨799736, by rfl⟩ : syracuseStep 1066315 = 1599473) B1599473
theorem B1066423 : Blo 944585 1066423 := bstep (se 1 (by rfl) ⟨799817, by rfl⟩ : syracuseStep 1066423 = 1599635) B1599635
theorem B1066603 : Blo 944585 1066603 := bstep (se 1 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 1066603 = 1599905) B1599905
theorem B5392003 : Blo 944585 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B1918657 : Blo 944585 1918657 := bstep (se 2 (by rfl) ⟨719496, by rfl⟩ : syracuseStep 1918657 = 1438993) B1438993
theorem B1066711 : Blo 944585 1066711 := bstep (se 1 (by rfl) ⟨800033, by rfl⟩ : syracuseStep 1066711 = 1600067) B1600067
theorem B3196637 : Blo 944585 3196637 := bstep (se 3 (by rfl) ⟨599369, by rfl⟩ : syracuseStep 3196637 = 1198739) B1198739
theorem B16205669 : Blo 944585 16205669 := bstep (se 4 (by rfl) ⟨1519281, by rfl⟩ : syracuseStep 16205669 = 3038563) B3038563
theorem B1066891 : Blo 944585 1066891 := bstep (se 1 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 1066891 = 1600337) B1600337
theorem B11519921 : Blo 944585 11519921 := bstep (se 2 (by rfl) ⟨4319970, by rfl⟩ : syracuseStep 11519921 = 8639941) B8639941
theorem B1066999 : Blo 944585 1066999 := bstep (se 1 (by rfl) ⟨800249, by rfl⟩ : syracuseStep 1066999 = 1600499) B1600499
theorem B1198091 : Blo 944585 1198091 := bstep (se 1 (by rfl) ⟨898568, by rfl⟩ : syracuseStep 1198091 = 1797137) B1797137
theorem B3590189 : Blo 944585 3590189 := bstep (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) B1346321
theorem B4049027 : Blo 944585 4049027 := bstep (se 1 (by rfl) ⟨3036770, by rfl⟩ : syracuseStep 4049027 = 6073541) B6073541
theorem B9717965 : Blo 944585 9717965 := bstep (se 3 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 9717965 = 3644237) B3644237
theorem B10799405 : Blo 944585 10799405 := bstep (se 3 (by rfl) ⟨2024888, by rfl⟩ : syracuseStep 10799405 = 4049777) B4049777
theorem B2017867 : Blo 944585 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B7195229 : Blo 944585 7195229 := bstep (se 3 (by rfl) ⟨1349105, by rfl⟩ : syracuseStep 7195229 = 2698211) B2698211
theorem B1198795 : Blo 944585 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B19712753 : Blo 944585 19712753 := bstep (se 2 (by rfl) ⟨7392282, by rfl⟩ : syracuseStep 19712753 = 14784565) B14784565
theorem B8080145 : Blo 944585 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B3590963 : Blo 944585 3590963 := bstep (se 1 (by rfl) ⟨2693222, by rfl⟩ : syracuseStep 3590963 = 5386445) B5386445
theorem B2018123 : Blo 944585 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B3197771 : Blo 944585 3197771 := bstep (se 1 (by rfl) ⟨2398328, by rfl⟩ : syracuseStep 3197771 = 4796657) B4796657
theorem B5393303 : Blo 944585 5393303 := bstep (se 1 (by rfl) ⟨4044977, by rfl⟩ : syracuseStep 5393303 = 8089955) B8089955
theorem B1199063 : Blo 944585 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B3198041 : Blo 944585 3198041 := bstep (se 2 (by rfl) ⟨1199265, by rfl⟩ : syracuseStep 3198041 = 2398531) B2398531
theorem B7982657 : Blo 944585 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B22171229 : Blo 944585 22171229 := bstep (se 3 (by rfl) ⟨4157105, by rfl⟩ : syracuseStep 22171229 = 8314211) B8314211
theorem B1199767 : Blo 944585 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B3198743 : Blo 944585 3198743 := bstep (se 1 (by rfl) ⟨2399057, by rfl⟩ : syracuseStep 3198743 = 4798115) B4798115
theorem B2019097 : Blo 944585 2019097 := bstep (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) B1514323
theorem B2019251 : Blo 944585 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B3592451 : Blo 944585 3592451 := bstep (se 1 (by rfl) ⟨2694338, by rfl⟩ : syracuseStep 3592451 = 5388677) B5388677
theorem B24236333 : Blo 944585 24236333 := bstep (se 3 (by rfl) ⟨4544312, by rfl⟩ : syracuseStep 24236333 = 9088625) B9088625
theorem B3199283 : Blo 944585 3199283 := bstep (se 1 (by rfl) ⟨2399462, by rfl⟩ : syracuseStep 3199283 = 4798925) B4798925
theorem B2019763 : Blo 944585 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B4051403 : Blo 944585 4051403 := bstep (se 1 (by rfl) ⟨3038552, by rfl⟩ : syracuseStep 4051403 = 6077105) B6077105
theorem B1364441 : Blo 944585 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B3199553 : Blo 944585 3199553 := bstep (se 2 (by rfl) ⟨1199832, by rfl⟩ : syracuseStep 3199553 = 2399665) B2399665
theorem B1135243 : Blo 944585 1135243 := bstep (se 1 (by rfl) ⟨851432, by rfl⟩ : syracuseStep 1135243 = 1702865) B1702865
theorem B3592907 : Blo 944585 3592907 := bstep (se 1 (by rfl) ⟨2694680, by rfl⟩ : syracuseStep 3592907 = 5389361) B5389361
theorem B1594073 : Blo 944585 1594073 := bstep (se 2 (by rfl) ⟨597777, by rfl⟩ : syracuseStep 1594073 = 1195555) B1195555
theorem B1594201 : Blo 944585 1594201 := bstep (se 2 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 1594201 = 1195651) B1195651
theorem B3593105 : Blo 944585 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B9098315 : Blo 944585 9098315 := bstep (se 1 (by rfl) ⟨6823736, by rfl⟩ : syracuseStep 9098315 = 13647473) B13647473
theorem B2020439 : Blo 944585 2020439 := bstep (se 1 (by rfl) ⟨1515329, by rfl⟩ : syracuseStep 2020439 = 3030659) B3030659
theorem B3200093 : Blo 944585 3200093 := bstep (se 3 (by rfl) ⟨600017, by rfl⟩ : syracuseStep 3200093 = 1200035) B1200035
theorem B2020481 : Blo 944585 2020481 := bstep (se 2 (by rfl) ⟨757680, by rfl⟩ : syracuseStep 2020481 = 1515361) B1515361
theorem B1594775 : Blo 944585 1594775 := bstep (se 1 (by rfl) ⟨1196081, by rfl⟩ : syracuseStep 1594775 = 2392163) B2392163
theorem B1594903 : Blo 944585 1594903 := bstep (se 1 (by rfl) ⟨1196177, by rfl⟩ : syracuseStep 1594903 = 2392355) B2392355
theorem B9229859 : Blo 944585 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B1365643 : Blo 944585 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B3593879 : Blo 944585 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B34592453 : Blo 944585 34592453 := bstep (se 4 (by rfl) ⟨3243042, by rfl⟩ : syracuseStep 34592453 = 6486085) B6486085
theorem B6477529 : Blo 944585 6477529 := bstep (se 2 (by rfl) ⟨2429073, by rfl⟩ : syracuseStep 6477529 = 4858147) B4858147
theorem B4314845 : Blo 944585 4314845 := bstep (se 3 (by rfl) ⟨809033, by rfl⟩ : syracuseStep 4314845 = 1618067) B1618067
theorem B3594077 : Blo 944585 3594077 := bstep (se 3 (by rfl) ⟨673889, by rfl⟩ : syracuseStep 3594077 = 1347779) B1347779
theorem B2873291 : Blo 944585 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1595531 : Blo 944585 1595531 := bstep (se 1 (by rfl) ⟨1196648, by rfl⟩ : syracuseStep 1595531 = 2393297) B2393297
theorem B3201227 : Blo 944585 3201227 := bstep (se 1 (by rfl) ⟨2400920, by rfl⟩ : syracuseStep 3201227 = 4801841) B4801841
theorem B1595659 : Blo 944585 1595659 := bstep (se 1 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 1595659 = 2393489) B2393489
theorem B3037463 : Blo 944585 3037463 := bstep (se 1 (by rfl) ⟨2278097, by rfl⟩ : syracuseStep 3037463 = 4556195) B4556195
theorem B2185601 : Blo 944585 2185601 := bstep (se 2 (by rfl) ⟨819600, by rfl⟩ : syracuseStep 2185601 = 1639201) B1639201
theorem B1137035 : Blo 944585 1137035 := bstep (se 1 (by rfl) ⟨852776, by rfl⟩ : syracuseStep 1137035 = 1705553) B1705553
theorem B1595801 : Blo 944585 1595801 := bstep (se 2 (by rfl) ⟨598425, by rfl⟩ : syracuseStep 1595801 = 1196851) B1196851
theorem B9099697 : Blo 944585 9099697 := bstep (se 2 (by rfl) ⟨3412386, by rfl⟩ : syracuseStep 9099697 = 6824773) B6824773
theorem B1595929 : Blo 944585 1595929 := bstep (se 2 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 1595929 = 1196947) B1196947
theorem B6478487 : Blo 944585 6478487 := bstep (se 1 (by rfl) ⟨4858865, by rfl⟩ : syracuseStep 6478487 = 9717731) B9717731
theorem B1137559 : Blo 944585 1137559 := bstep (se 1 (by rfl) ⟨853169, by rfl⟩ : syracuseStep 1137559 = 1706339) B1706339
theorem B1596503 : Blo 944585 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B3038411 : Blo 944585 3038411 := bstep (se 1 (by rfl) ⟨2278808, by rfl⟩ : syracuseStep 3038411 = 4557617) B4557617
theorem B1596631 : Blo 944585 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B1793431 : Blo 944585 1793431 := bstep (se 1 (by rfl) ⟨1345073, by rfl⟩ : syracuseStep 1793431 = 2690147) B2690147
theorem B5398109 : Blo 944585 5398109 := bstep (se 3 (by rfl) ⟨1012145, by rfl⟩ : syracuseStep 5398109 = 2024291) B2024291
theorem B3596035 : Blo 944585 3596035 := bstep (se 1 (by rfl) ⟨2697026, by rfl⟩ : syracuseStep 3596035 = 5394053) B5394053
theorem B1597259 : Blo 944585 1597259 := bstep (se 1 (by rfl) ⟨1197944, by rfl⟩ : syracuseStep 1597259 = 2395889) B2395889
theorem B1597387 : Blo 944585 1597387 := bstep (se 1 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 1597387 = 2396081) B2396081
theorem B2023385 : Blo 944585 2023385 := bstep (se 2 (by rfl) ⟨758769, by rfl⟩ : syracuseStep 2023385 = 1517539) B1517539
theorem B3596339 : Blo 944585 3596339 := bstep (se 1 (by rfl) ⟨2697254, by rfl⟩ : syracuseStep 3596339 = 5394509) B5394509
theorem B1597529 : Blo 944585 1597529 := bstep (se 2 (by rfl) ⟨599073, by rfl⟩ : syracuseStep 1597529 = 1198147) B1198147
theorem B1794251 : Blo 944585 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B1597657 : Blo 944585 1597657 := bstep (se 2 (by rfl) ⟨599121, by rfl⟩ : syracuseStep 1597657 = 1198243) B1198243
theorem B1794305 : Blo 944585 1794305 := bstep (se 2 (by rfl) ⟨672864, by rfl⟩ : syracuseStep 1794305 = 1345729) B1345729
theorem B2023795 : Blo 944585 2023795 := bstep (se 1 (by rfl) ⟨1517846, by rfl⟩ : syracuseStep 2023795 = 3035693) B3035693
theorem B11067997 : Blo 944585 11067997 := bstep (se 3 (by rfl) ⟨2075249, by rfl⟩ : syracuseStep 11067997 = 4150499) B4150499
theorem B3596993 : Blo 944585 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B2024129 : Blo 944585 2024129 := bstep (se 2 (by rfl) ⟨759048, by rfl⟩ : syracuseStep 2024129 = 1518097) B1518097
theorem B1598231 : Blo 944585 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B1598359 : Blo 944585 1598359 := bstep (se 1 (by rfl) ⟨1198769, by rfl⟩ : syracuseStep 1598359 = 2397539) B2397539
theorem B1795223 : Blo 944585 1795223 := bstep (se 1 (by rfl) ⟨1346417, by rfl⟩ : syracuseStep 1795223 = 2692835) B2692835
theorem B2024855 : Blo 944585 2024855 := bstep (se 1 (by rfl) ⟨1518641, by rfl⟩ : syracuseStep 2024855 = 3037283) B3037283
theorem B7660979 : Blo 944585 7660979 := bstep (se 1 (by rfl) ⟨5745734, by rfl⟩ : syracuseStep 7660979 = 11491469) B11491469
theorem B1598987 : Blo 944585 1598987 := bstep (se 1 (by rfl) ⟨1199240, by rfl⟩ : syracuseStep 1598987 = 2398481) B2398481
theorem B1009207 : Blo 944585 1009207 := bstep (se 1 (by rfl) ⟨756905, by rfl⟩ : syracuseStep 1009207 = 1513811) B1513811
theorem B1599115 : Blo 944585 1599115 := bstep (se 1 (by rfl) ⟨1199336, by rfl⟩ : syracuseStep 1599115 = 2398673) B2398673
theorem B1402519 : Blo 944585 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B1795763 : Blo 944585 1795763 := bstep (se 1 (by rfl) ⟨1346822, by rfl⟩ : syracuseStep 1795763 = 2693645) B2693645
theorem B1599257 : Blo 944585 1599257 := bstep (se 2 (by rfl) ⟨599721, by rfl⟩ : syracuseStep 1599257 = 1199443) B1199443
theorem B1599385 : Blo 944585 1599385 := bstep (se 2 (by rfl) ⟨599769, by rfl⟩ : syracuseStep 1599385 = 1199539) B1199539
theorem B3598253 : Blo 944585 3598253 := bstep (se 3 (by rfl) ⟨674672, by rfl⟩ : syracuseStep 3598253 = 1349345) B1349345
theorem B3598283 : Blo 944585 3598283 := bstep (se 1 (by rfl) ⟨2698712, by rfl⟩ : syracuseStep 3598283 = 5397425) B5397425
theorem B5400593 : Blo 944585 5400593 := bstep (se 2 (by rfl) ⟨2025222, by rfl⟩ : syracuseStep 5400593 = 4050445) B4050445
theorem B1796249 : Blo 944585 1796249 := bstep (se 2 (by rfl) ⟨673593, by rfl⟩ : syracuseStep 1796249 = 1347187) B1347187
theorem B9103661 : Blo 944585 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B1010027 : Blo 944585 1010027 := bstep (se 1 (by rfl) ⟨757520, by rfl⟩ : syracuseStep 1010027 = 1515041) B1515041
theorem B2189683 : Blo 944585 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B944587 : Blo 944585 944587 := bstep (se 1 (by rfl) ⟨708440, by rfl⟩ : syracuseStep 944587 = 1416881) B1416881
theorem B944599 : Blo 944585 944599 := bstep (se 1 (by rfl) ⟨708449, by rfl⟩ : syracuseStep 944599 = 1416899) B1416899
theorem B1599959 : Blo 944585 1599959 := bstep (se 1 (by rfl) ⟨1199969, by rfl⟩ : syracuseStep 1599959 = 2399939) B2399939
theorem B4549081 : Blo 944585 4549081 := bstep (se 2 (by rfl) ⟨1705905, by rfl⟩ : syracuseStep 4549081 = 3411811) B3411811
theorem B944619 : Blo 944585 944619 := bstep (se 1 (by rfl) ⟨708464, by rfl⟩ : syracuseStep 944619 = 1416929) B1416929
theorem B1010155 : Blo 944585 1010155 := bstep (se 1 (by rfl) ⟨757616, by rfl⟩ : syracuseStep 1010155 = 1515233) B1515233
theorem B944631 : Blo 944585 944631 := bstep (se 1 (by rfl) ⟨708473, by rfl⟩ : syracuseStep 944631 = 1416947) B1416947
theorem B944651 : Blo 944585 944651 := bstep (se 1 (by rfl) ⟨708488, by rfl⟩ : syracuseStep 944651 = 1416977) B1416977
theorem B944663 : Blo 944585 944663 := bstep (se 1 (by rfl) ⟨708497, by rfl⟩ : syracuseStep 944663 = 1416995) B1416995
theorem B944683 : Blo 944585 944683 := bstep (se 1 (by rfl) ⟨708512, by rfl⟩ : syracuseStep 944683 = 1417025) B1417025
theorem B944695 : Blo 944585 944695 := bstep (se 1 (by rfl) ⟨708521, by rfl⟩ : syracuseStep 944695 = 1417043) B1417043
theorem B944715 : Blo 944585 944715 := bstep (se 1 (by rfl) ⟨708536, by rfl⟩ : syracuseStep 944715 = 1417073) B1417073
theorem B944727 : Blo 944585 944727 := bstep (se 1 (by rfl) ⟨708545, by rfl⟩ : syracuseStep 944727 = 1417091) B1417091
theorem B1600087 : Blo 944585 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B3598937 : Blo 944585 3598937 := bstep (se 2 (by rfl) ⟨1349601, by rfl⟩ : syracuseStep 3598937 = 2699203) B2699203
theorem B944747 : Blo 944585 944747 := bstep (se 1 (by rfl) ⟨708560, by rfl⟩ : syracuseStep 944747 = 1417121) B1417121
theorem B944759 : Blo 944585 944759 := bstep (se 1 (by rfl) ⟨708569, by rfl⟩ : syracuseStep 944759 = 1417139) B1417139
theorem B944779 : Blo 944585 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B944791 : Blo 944585 944791 := bstep (se 1 (by rfl) ⟨708593, by rfl⟩ : syracuseStep 944791 = 1417187) B1417187
theorem B944811 : Blo 944585 944811 := bstep (se 1 (by rfl) ⟨708608, by rfl⟩ : syracuseStep 944811 = 1417217) B1417217
theorem B944823 : Blo 944585 944823 := bstep (se 1 (by rfl) ⟨708617, by rfl⟩ : syracuseStep 944823 = 1417235) B1417235
theorem B944843 : Blo 944585 944843 := bstep (se 1 (by rfl) ⟨708632, by rfl⟩ : syracuseStep 944843 = 1417265) B1417265
theorem B944855 : Blo 944585 944855 := bstep (se 1 (by rfl) ⟨708641, by rfl⟩ : syracuseStep 944855 = 1417283) B1417283
theorem B944875 : Blo 944585 944875 := bstep (se 1 (by rfl) ⟨708656, by rfl⟩ : syracuseStep 944875 = 1417313) B1417313
theorem B944887 : Blo 944585 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B944907 : Blo 944585 944907 := bstep (se 1 (by rfl) ⟨708680, by rfl⟩ : syracuseStep 944907 = 1417361) B1417361
theorem B944919 : Blo 944585 944919 := bstep (se 1 (by rfl) ⟨708689, by rfl⟩ : syracuseStep 944919 = 1417379) B1417379
theorem B944939 : Blo 944585 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B944951 : Blo 944585 944951 := bstep (se 1 (by rfl) ⟨708713, by rfl⟩ : syracuseStep 944951 = 1417427) B1417427
theorem B944971 : Blo 944585 944971 := bstep (se 1 (by rfl) ⟨708728, by rfl⟩ : syracuseStep 944971 = 1417457) B1417457
theorem B944983 : Blo 944585 944983 := bstep (se 1 (by rfl) ⟨708737, by rfl⟩ : syracuseStep 944983 = 1417475) B1417475
theorem B945003 : Blo 944585 945003 := bstep (se 1 (by rfl) ⟨708752, by rfl⟩ : syracuseStep 945003 = 1417505) B1417505
theorem B945015 : Blo 944585 945015 := bstep (se 1 (by rfl) ⟨708761, by rfl⟩ : syracuseStep 945015 = 1417523) B1417523
theorem B5106563 : Blo 944585 5106563 := bstep (se 1 (by rfl) ⟨3829922, by rfl⟩ : syracuseStep 5106563 = 7659845) B7659845
theorem B945035 : Blo 944585 945035 := bstep (se 1 (by rfl) ⟨708776, by rfl⟩ : syracuseStep 945035 = 1417553) B1417553
theorem B4090769 : Blo 944585 4090769 := bstep (se 2 (by rfl) ⟨1534038, by rfl⟩ : syracuseStep 4090769 = 3068077) B3068077
theorem B945047 : Blo 944585 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B3599255 : Blo 944585 3599255 := bstep (se 1 (by rfl) ⟨2699441, by rfl⟩ : syracuseStep 3599255 = 5398883) B5398883
theorem B945067 : Blo 944585 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B945079 : Blo 944585 945079 := bstep (se 1 (by rfl) ⟨708809, by rfl⟩ : syracuseStep 945079 = 1417619) B1417619
theorem B945099 : Blo 944585 945099 := bstep (se 1 (by rfl) ⟨708824, by rfl⟩ : syracuseStep 945099 = 1417649) B1417649
theorem B945111 : Blo 944585 945111 := bstep (se 1 (by rfl) ⟨708833, by rfl⟩ : syracuseStep 945111 = 1417667) B1417667
theorem B945131 : Blo 944585 945131 := bstep (se 1 (by rfl) ⟨708848, by rfl⟩ : syracuseStep 945131 = 1417697) B1417697
theorem B945143 : Blo 944585 945143 := bstep (se 1 (by rfl) ⟨708857, by rfl⟩ : syracuseStep 945143 = 1417715) B1417715
theorem B945163 : Blo 944585 945163 := bstep (se 1 (by rfl) ⟨708872, by rfl⟩ : syracuseStep 945163 = 1417745) B1417745
theorem B945175 : Blo 944585 945175 := bstep (se 1 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 945175 = 1417763) B1417763
theorem B945195 : Blo 944585 945195 := bstep (se 1 (by rfl) ⟨708896, by rfl⟩ : syracuseStep 945195 = 1417793) B1417793
theorem B945207 : Blo 944585 945207 := bstep (se 1 (by rfl) ⟨708905, by rfl⟩ : syracuseStep 945207 = 1417811) B1417811
theorem B945227 : Blo 944585 945227 := bstep (se 1 (by rfl) ⟨708920, by rfl⟩ : syracuseStep 945227 = 1417841) B1417841
theorem B945239 : Blo 944585 945239 := bstep (se 1 (by rfl) ⟨708929, by rfl⟩ : syracuseStep 945239 = 1417859) B1417859
theorem B945259 : Blo 944585 945259 := bstep (se 1 (by rfl) ⟨708944, by rfl⟩ : syracuseStep 945259 = 1417889) B1417889
theorem B945271 : Blo 944585 945271 := bstep (se 1 (by rfl) ⟨708953, by rfl⟩ : syracuseStep 945271 = 1417907) B1417907
theorem B945291 : Blo 944585 945291 := bstep (se 1 (by rfl) ⟨708968, by rfl⟩ : syracuseStep 945291 = 1417937) B1417937
theorem B945303 : Blo 944585 945303 := bstep (se 1 (by rfl) ⟨708977, by rfl⟩ : syracuseStep 945303 = 1417955) B1417955
theorem B945323 : Blo 944585 945323 := bstep (se 1 (by rfl) ⟨708992, by rfl⟩ : syracuseStep 945323 = 1417985) B1417985
theorem B945335 : Blo 944585 945335 := bstep (se 1 (by rfl) ⟨709001, by rfl⟩ : syracuseStep 945335 = 1418003) B1418003
theorem B945355 : Blo 944585 945355 := bstep (se 1 (by rfl) ⟨709016, by rfl⟩ : syracuseStep 945355 = 1418033) B1418033
theorem B1600715 : Blo 944585 1600715 := bstep (se 1 (by rfl) ⟨1200536, by rfl⟩ : syracuseStep 1600715 = 2401073) B2401073
theorem B945367 : Blo 944585 945367 := bstep (se 1 (by rfl) ⟨709025, by rfl⟩ : syracuseStep 945367 = 1418051) B1418051
theorem B945387 : Blo 944585 945387 := bstep (se 1 (by rfl) ⟨709040, by rfl⟩ : syracuseStep 945387 = 1418081) B1418081
theorem B945399 : Blo 944585 945399 := bstep (se 1 (by rfl) ⟨709049, by rfl⟩ : syracuseStep 945399 = 1418099) B1418099
theorem B945419 : Blo 944585 945419 := bstep (se 1 (by rfl) ⟨709064, by rfl⟩ : syracuseStep 945419 = 1418129) B1418129
theorem B945431 : Blo 944585 945431 := bstep (se 1 (by rfl) ⟨709073, by rfl⟩ : syracuseStep 945431 = 1418147) B1418147
theorem B945451 : Blo 944585 945451 := bstep (se 1 (by rfl) ⟨709088, by rfl⟩ : syracuseStep 945451 = 1418177) B1418177
theorem B945463 : Blo 944585 945463 := bstep (se 1 (by rfl) ⟨709097, by rfl⟩ : syracuseStep 945463 = 1418195) B1418195
theorem B945483 : Blo 944585 945483 := bstep (se 1 (by rfl) ⟨709112, by rfl⟩ : syracuseStep 945483 = 1418225) B1418225
theorem B945495 : Blo 944585 945495 := bstep (se 1 (by rfl) ⟨709121, by rfl⟩ : syracuseStep 945495 = 1418243) B1418243
theorem B945515 : Blo 944585 945515 := bstep (se 1 (by rfl) ⟨709136, by rfl⟩ : syracuseStep 945515 = 1418273) B1418273
theorem B945527 : Blo 944585 945527 := bstep (se 1 (by rfl) ⟨709145, by rfl⟩ : syracuseStep 945527 = 1418291) B1418291
theorem B945547 : Blo 944585 945547 := bstep (se 1 (by rfl) ⟨709160, by rfl⟩ : syracuseStep 945547 = 1418321) B1418321
theorem B945559 : Blo 944585 945559 := bstep (se 1 (by rfl) ⟨709169, by rfl⟩ : syracuseStep 945559 = 1418339) B1418339
theorem B945579 : Blo 944585 945579 := bstep (se 1 (by rfl) ⟨709184, by rfl⟩ : syracuseStep 945579 = 1418369) B1418369
theorem B945591 : Blo 944585 945591 := bstep (se 1 (by rfl) ⟨709193, by rfl⟩ : syracuseStep 945591 = 1418387) B1418387
theorem B945611 : Blo 944585 945611 := bstep (se 1 (by rfl) ⟨709208, by rfl⟩ : syracuseStep 945611 = 1418417) B1418417
theorem B44330453 : Blo 944585 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B945623 : Blo 944585 945623 := bstep (se 1 (by rfl) ⟨709217, by rfl⟩ : syracuseStep 945623 = 1418435) B1418435
theorem B13102553 : Blo 944585 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B945643 : Blo 944585 945643 := bstep (se 1 (by rfl) ⟨709232, by rfl⟩ : syracuseStep 945643 = 1418465) B1418465
theorem B945655 : Blo 944585 945655 := bstep (se 1 (by rfl) ⟨709241, by rfl⟩ : syracuseStep 945655 = 1418483) B1418483
theorem B945675 : Blo 944585 945675 := bstep (se 1 (by rfl) ⟨709256, by rfl⟩ : syracuseStep 945675 = 1418513) B1418513
theorem B15330829 : Blo 944585 15330829 := bstep (se 3 (by rfl) ⟨2874530, by rfl⟩ : syracuseStep 15330829 = 5749061) B5749061
theorem B945687 : Blo 944585 945687 := bstep (se 1 (by rfl) ⟨709265, by rfl⟩ : syracuseStep 945687 = 1418531) B1418531
theorem B945707 : Blo 944585 945707 := bstep (se 1 (by rfl) ⟨709280, by rfl⟩ : syracuseStep 945707 = 1418561) B1418561
theorem B3599923 : Blo 944585 3599923 := bstep (se 1 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 3599923 = 5399885) B5399885
theorem B945719 : Blo 944585 945719 := bstep (se 1 (by rfl) ⟨709289, by rfl⟩ : syracuseStep 945719 = 1418579) B1418579
theorem B945739 : Blo 944585 945739 := bstep (se 1 (by rfl) ⟨709304, by rfl⟩ : syracuseStep 945739 = 1418609) B1418609
theorem B1797707 : Blo 944585 1797707 := bstep (se 1 (by rfl) ⟨1348280, by rfl⟩ : syracuseStep 1797707 = 2696561) B2696561
theorem B945751 : Blo 944585 945751 := bstep (se 1 (by rfl) ⟨709313, by rfl⟩ : syracuseStep 945751 = 1418627) B1418627
theorem B945771 : Blo 944585 945771 := bstep (se 1 (by rfl) ⟨709328, by rfl⟩ : syracuseStep 945771 = 1418657) B1418657
theorem B945783 : Blo 944585 945783 := bstep (se 1 (by rfl) ⟨709337, by rfl⟩ : syracuseStep 945783 = 1418675) B1418675
theorem B945803 : Blo 944585 945803 := bstep (se 1 (by rfl) ⟨709352, by rfl⟩ : syracuseStep 945803 = 1418705) B1418705
theorem B945815 : Blo 944585 945815 := bstep (se 1 (by rfl) ⟨709361, by rfl⟩ : syracuseStep 945815 = 1418723) B1418723
theorem B945835 : Blo 944585 945835 := bstep (se 1 (by rfl) ⟨709376, by rfl⟩ : syracuseStep 945835 = 1418753) B1418753
theorem B2879155 : Blo 944585 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B13627061 : Blo 944585 13627061 := bstep (se 5 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 13627061 = 1277537) B1277537
theorem B945847 : Blo 944585 945847 := bstep (se 1 (by rfl) ⟨709385, by rfl⟩ : syracuseStep 945847 = 1418771) B1418771
theorem B945867 : Blo 944585 945867 := bstep (se 1 (by rfl) ⟨709400, by rfl⟩ : syracuseStep 945867 = 1418801) B1418801
theorem B945879 : Blo 944585 945879 := bstep (se 1 (by rfl) ⟨709409, by rfl⟩ : syracuseStep 945879 = 1418819) B1418819
theorem B2125529 : Blo 944585 2125529 := bstep (se 2 (by rfl) ⟨797073, by rfl⟩ : syracuseStep 2125529 = 1594147) B1594147
theorem B945899 : Blo 944585 945899 := bstep (se 1 (by rfl) ⟨709424, by rfl⟩ : syracuseStep 945899 = 1418849) B1418849
theorem B945911 : Blo 944585 945911 := bstep (se 1 (by rfl) ⟨709433, by rfl⟩ : syracuseStep 945911 = 1418867) B1418867
theorem B1797889 : Blo 944585 1797889 := bstep (se 2 (by rfl) ⟨674208, by rfl⟩ : syracuseStep 1797889 = 1348417) B1348417
theorem B6811397 : Blo 944585 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B945931 : Blo 944585 945931 := bstep (se 1 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 945931 = 1418897) B1418897
theorem B945943 : Blo 944585 945943 := bstep (se 1 (by rfl) ⟨709457, by rfl⟩ : syracuseStep 945943 = 1418915) B1418915
theorem B945963 : Blo 944585 945963 := bstep (se 1 (by rfl) ⟨709472, by rfl⟩ : syracuseStep 945963 = 1418945) B1418945
theorem B2125619 : Blo 944585 2125619 := bstep (se 1 (by rfl) ⟨1594214, by rfl⟩ : syracuseStep 2125619 = 3188429) B3188429
theorem B945975 : Blo 944585 945975 := bstep (se 1 (by rfl) ⟨709481, by rfl⟩ : syracuseStep 945975 = 1418963) B1418963
theorem B945995 : Blo 944585 945995 := bstep (se 1 (by rfl) ⟨709496, by rfl⟩ : syracuseStep 945995 = 1418993) B1418993
theorem B2125655 : Blo 944585 2125655 := bstep (se 1 (by rfl) ⟨1594241, by rfl⟩ : syracuseStep 2125655 = 3188483) B3188483
theorem B946007 : Blo 944585 946007 := bstep (se 1 (by rfl) ⟨709505, by rfl⟩ : syracuseStep 946007 = 1419011) B1419011
theorem B946027 : Blo 944585 946027 := bstep (se 1 (by rfl) ⟨709520, by rfl⟩ : syracuseStep 946027 = 1419041) B1419041
theorem B946039 : Blo 944585 946039 := bstep (se 1 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 946039 = 1419059) B1419059
theorem B946059 : Blo 944585 946059 := bstep (se 1 (by rfl) ⟨709544, by rfl⟩ : syracuseStep 946059 = 1419089) B1419089
theorem B946071 : Blo 944585 946071 := bstep (se 1 (by rfl) ⟨709553, by rfl⟩ : syracuseStep 946071 = 1419107) B1419107
theorem B946091 : Blo 944585 946091 := bstep (se 1 (by rfl) ⟨709568, by rfl⟩ : syracuseStep 946091 = 1419137) B1419137
theorem B946103 : Blo 944585 946103 := bstep (se 1 (by rfl) ⟨709577, by rfl⟩ : syracuseStep 946103 = 1419155) B1419155
theorem B946123 : Blo 944585 946123 := bstep (se 1 (by rfl) ⟨709592, by rfl⟩ : syracuseStep 946123 = 1419185) B1419185
theorem B946135 : Blo 944585 946135 := bstep (se 1 (by rfl) ⟨709601, by rfl⟩ : syracuseStep 946135 = 1419203) B1419203
theorem B946155 : Blo 944585 946155 := bstep (se 1 (by rfl) ⟨709616, by rfl⟩ : syracuseStep 946155 = 1419233) B1419233
theorem B946167 : Blo 944585 946167 := bstep (se 1 (by rfl) ⟨709625, by rfl⟩ : syracuseStep 946167 = 1419251) B1419251
theorem B2125835 : Blo 944585 2125835 := bstep (se 1 (by rfl) ⟨1594376, by rfl⟩ : syracuseStep 2125835 = 3188753) B3188753
theorem B946187 : Blo 944585 946187 := bstep (se 1 (by rfl) ⟨709640, by rfl⟩ : syracuseStep 946187 = 1419281) B1419281
theorem B1536023 : Blo 944585 1536023 := bstep (se 1 (by rfl) ⟨1152017, by rfl⟩ : syracuseStep 1536023 = 2304035) B2304035
theorem B946199 : Blo 944585 946199 := bstep (se 1 (by rfl) ⟨709649, by rfl⟩ : syracuseStep 946199 = 1419299) B1419299
theorem B946219 : Blo 944585 946219 := bstep (se 1 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 946219 = 1419329) B1419329
theorem B946231 : Blo 944585 946231 := bstep (se 1 (by rfl) ⟨709673, by rfl⟩ : syracuseStep 946231 = 1419347) B1419347
theorem B2125889 : Blo 944585 2125889 := bstep (se 2 (by rfl) ⟨797208, by rfl⟩ : syracuseStep 2125889 = 1594417) B1594417
theorem B946251 : Blo 944585 946251 := bstep (se 1 (by rfl) ⟨709688, by rfl⟩ : syracuseStep 946251 = 1419377) B1419377
theorem B946263 : Blo 944585 946263 := bstep (se 1 (by rfl) ⟨709697, by rfl⟩ : syracuseStep 946263 = 1419395) B1419395
theorem B946283 : Blo 944585 946283 := bstep (se 1 (by rfl) ⟨709712, by rfl⟩ : syracuseStep 946283 = 1419425) B1419425
theorem B2191475 : Blo 944585 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B946295 : Blo 944585 946295 := bstep (se 1 (by rfl) ⟨709721, by rfl⟩ : syracuseStep 946295 = 1419443) B1419443
theorem B946315 : Blo 944585 946315 := bstep (se 1 (by rfl) ⟨709736, by rfl⟩ : syracuseStep 946315 = 1419473) B1419473
theorem B946327 : Blo 944585 946327 := bstep (se 1 (by rfl) ⟨709745, by rfl⟩ : syracuseStep 946327 = 1419491) B1419491
theorem B946347 : Blo 944585 946347 := bstep (se 1 (by rfl) ⟨709760, by rfl⟩ : syracuseStep 946347 = 1419521) B1419521
theorem B946359 : Blo 944585 946359 := bstep (se 1 (by rfl) ⟨709769, by rfl⟩ : syracuseStep 946359 = 1419539) B1419539
theorem B1798337 : Blo 944585 1798337 := bstep (se 2 (by rfl) ⟨674376, by rfl⟩ : syracuseStep 1798337 = 1348753) B1348753
theorem B946379 : Blo 944585 946379 := bstep (se 1 (by rfl) ⟨709784, by rfl⟩ : syracuseStep 946379 = 1419569) B1419569
theorem B946391 : Blo 944585 946391 := bstep (se 1 (by rfl) ⟨709793, by rfl⟩ : syracuseStep 946391 = 1419587) B1419587
theorem B946411 : Blo 944585 946411 := bstep (se 1 (by rfl) ⟨709808, by rfl⟩ : syracuseStep 946411 = 1419617) B1419617
theorem B946423 : Blo 944585 946423 := bstep (se 1 (by rfl) ⟨709817, by rfl⟩ : syracuseStep 946423 = 1419635) B1419635
theorem B946443 : Blo 944585 946443 := bstep (se 1 (by rfl) ⟨709832, by rfl⟩ : syracuseStep 946443 = 1419665) B1419665
theorem B946455 : Blo 944585 946455 := bstep (se 1 (by rfl) ⟨709841, by rfl⟩ : syracuseStep 946455 = 1419683) B1419683
theorem B2126105 : Blo 944585 2126105 := bstep (se 2 (by rfl) ⟨797289, by rfl⟩ : syracuseStep 2126105 = 1594579) B1594579
theorem B946475 : Blo 944585 946475 := bstep (se 1 (by rfl) ⟨709856, by rfl⟩ : syracuseStep 946475 = 1419713) B1419713
theorem B946487 : Blo 944585 946487 := bstep (se 1 (by rfl) ⟨709865, by rfl⟩ : syracuseStep 946487 = 1419731) B1419731
theorem B946507 : Blo 944585 946507 := bstep (se 1 (by rfl) ⟨709880, by rfl⟩ : syracuseStep 946507 = 1419761) B1419761
theorem B946519 : Blo 944585 946519 := bstep (se 1 (by rfl) ⟨709889, by rfl⟩ : syracuseStep 946519 = 1419779) B1419779
theorem B946539 : Blo 944585 946539 := bstep (se 1 (by rfl) ⟨709904, by rfl⟩ : syracuseStep 946539 = 1419809) B1419809
theorem B69005681 : Blo 944585 69005681 := bstep (se 2 (by rfl) ⟨25877130, by rfl⟩ : syracuseStep 69005681 = 51754261) B51754261
theorem B2126195 : Blo 944585 2126195 := bstep (se 1 (by rfl) ⟨1594646, by rfl⟩ : syracuseStep 2126195 = 3189293) B3189293
theorem B946551 : Blo 944585 946551 := bstep (se 1 (by rfl) ⟨709913, by rfl⟩ : syracuseStep 946551 = 1419827) B1419827
theorem B946571 : Blo 944585 946571 := bstep (se 1 (by rfl) ⟨709928, by rfl⟩ : syracuseStep 946571 = 1419857) B1419857
theorem B2126231 : Blo 944585 2126231 := bstep (se 1 (by rfl) ⟨1594673, by rfl⟩ : syracuseStep 2126231 = 3189347) B3189347
theorem B946583 : Blo 944585 946583 := bstep (se 1 (by rfl) ⟨709937, by rfl⟩ : syracuseStep 946583 = 1419875) B1419875
theorem B946603 : Blo 944585 946603 := bstep (se 1 (by rfl) ⟨709952, by rfl⟩ : syracuseStep 946603 = 1419905) B1419905
theorem B946615 : Blo 944585 946615 := bstep (se 1 (by rfl) ⟨709961, by rfl⟩ : syracuseStep 946615 = 1419923) B1419923
theorem B946635 : Blo 944585 946635 := bstep (se 1 (by rfl) ⟨709976, by rfl⟩ : syracuseStep 946635 = 1419953) B1419953
theorem B946647 : Blo 944585 946647 := bstep (se 1 (by rfl) ⟨709985, by rfl⟩ : syracuseStep 946647 = 1419971) B1419971
theorem B13627865 : Blo 944585 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B946667 : Blo 944585 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B946679 : Blo 944585 946679 := bstep (se 1 (by rfl) ⟨710009, by rfl⟩ : syracuseStep 946679 = 1420019) B1420019
theorem B946699 : Blo 944585 946699 := bstep (se 1 (by rfl) ⟨710024, by rfl⟩ : syracuseStep 946699 = 1420049) B1420049
theorem B946711 : Blo 944585 946711 := bstep (se 1 (by rfl) ⟨710033, by rfl⟩ : syracuseStep 946711 = 1420067) B1420067
theorem B1798679 : Blo 944585 1798679 := bstep (se 1 (by rfl) ⟨1349009, by rfl⟩ : syracuseStep 1798679 = 2698019) B2698019
theorem B946731 : Blo 944585 946731 := bstep (se 1 (by rfl) ⟨710048, by rfl⟩ : syracuseStep 946731 = 1420097) B1420097
theorem B946743 : Blo 944585 946743 := bstep (se 1 (by rfl) ⟨710057, by rfl⟩ : syracuseStep 946743 = 1420115) B1420115
theorem B2126411 : Blo 944585 2126411 := bstep (se 1 (by rfl) ⟨1594808, by rfl⟩ : syracuseStep 2126411 = 3189617) B3189617
theorem B946763 : Blo 944585 946763 := bstep (se 1 (by rfl) ⟨710072, by rfl⟩ : syracuseStep 946763 = 1420145) B1420145
theorem B946775 : Blo 944585 946775 := bstep (se 1 (by rfl) ⟨710081, by rfl⟩ : syracuseStep 946775 = 1420163) B1420163
theorem B6156901 : Blo 944585 6156901 := bstep (se 4 (by rfl) ⟨577209, by rfl⟩ : syracuseStep 6156901 = 1154419) B1154419
theorem B946795 : Blo 944585 946795 := bstep (se 1 (by rfl) ⟨710096, by rfl⟩ : syracuseStep 946795 = 1420193) B1420193
theorem B946807 : Blo 944585 946807 := bstep (se 1 (by rfl) ⟨710105, by rfl⟩ : syracuseStep 946807 = 1420211) B1420211
theorem B2126465 : Blo 944585 2126465 := bstep (se 2 (by rfl) ⟨797424, by rfl⟩ : syracuseStep 2126465 = 1594849) B1594849
theorem B946827 : Blo 944585 946827 := bstep (se 1 (by rfl) ⟨710120, by rfl⟩ : syracuseStep 946827 = 1420241) B1420241
theorem B946839 : Blo 944585 946839 := bstep (se 1 (by rfl) ⟨710129, by rfl⟩ : syracuseStep 946839 = 1420259) B1420259
theorem B946859 : Blo 944585 946859 := bstep (se 1 (by rfl) ⟨710144, by rfl⟩ : syracuseStep 946859 = 1420289) B1420289
theorem B946871 : Blo 944585 946871 := bstep (se 1 (by rfl) ⟨710153, by rfl⟩ : syracuseStep 946871 = 1420307) B1420307
theorem B946891 : Blo 944585 946891 := bstep (se 1 (by rfl) ⟨710168, by rfl⟩ : syracuseStep 946891 = 1420337) B1420337
theorem B946903 : Blo 944585 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B946923 : Blo 944585 946923 := bstep (se 1 (by rfl) ⟨710192, by rfl⟩ : syracuseStep 946923 = 1420385) B1420385
theorem B946935 : Blo 944585 946935 := bstep (se 1 (by rfl) ⟨710201, by rfl⟩ : syracuseStep 946935 = 1420403) B1420403
theorem B946955 : Blo 944585 946955 := bstep (se 1 (by rfl) ⟨710216, by rfl⟩ : syracuseStep 946955 = 1420433) B1420433
theorem B3601169 : Blo 944585 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B946967 : Blo 944585 946967 := bstep (se 1 (by rfl) ⟨710225, by rfl⟩ : syracuseStep 946967 = 1420451) B1420451
theorem B946987 : Blo 944585 946987 := bstep (se 1 (by rfl) ⟨710240, by rfl⟩ : syracuseStep 946987 = 1420481) B1420481
theorem B946999 : Blo 944585 946999 := bstep (se 1 (by rfl) ⟨710249, by rfl⟩ : syracuseStep 946999 = 1420499) B1420499
theorem B947019 : Blo 944585 947019 := bstep (se 1 (by rfl) ⟨710264, by rfl⟩ : syracuseStep 947019 = 1420529) B1420529
theorem B947031 : Blo 944585 947031 := bstep (se 1 (by rfl) ⟨710273, by rfl⟩ : syracuseStep 947031 = 1420547) B1420547
theorem B2126681 : Blo 944585 2126681 := bstep (se 2 (by rfl) ⟨797505, by rfl⟩ : syracuseStep 2126681 = 1595011) B1595011
theorem B947051 : Blo 944585 947051 := bstep (se 1 (by rfl) ⟨710288, by rfl⟩ : syracuseStep 947051 = 1420577) B1420577
theorem B947063 : Blo 944585 947063 := bstep (se 1 (by rfl) ⟨710297, by rfl⟩ : syracuseStep 947063 = 1420595) B1420595
theorem B947083 : Blo 944585 947083 := bstep (se 1 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 947083 = 1420625) B1420625
theorem B947095 : Blo 944585 947095 := bstep (se 1 (by rfl) ⟨710321, by rfl⟩ : syracuseStep 947095 = 1420643) B1420643
theorem B947115 : Blo 944585 947115 := bstep (se 1 (by rfl) ⟨710336, by rfl⟩ : syracuseStep 947115 = 1420673) B1420673
theorem B2126771 : Blo 944585 2126771 := bstep (se 1 (by rfl) ⟨1595078, by rfl⟩ : syracuseStep 2126771 = 3190157) B3190157
theorem B947127 : Blo 944585 947127 := bstep (se 1 (by rfl) ⟨710345, by rfl⟩ : syracuseStep 947127 = 1420691) B1420691
theorem B947147 : Blo 944585 947147 := bstep (se 1 (by rfl) ⟨710360, by rfl⟩ : syracuseStep 947147 = 1420721) B1420721
theorem B2126807 : Blo 944585 2126807 := bstep (se 1 (by rfl) ⟨1595105, by rfl⟩ : syracuseStep 2126807 = 3190211) B3190211
theorem B947159 : Blo 944585 947159 := bstep (se 1 (by rfl) ⟨710369, by rfl⟩ : syracuseStep 947159 = 1420739) B1420739
theorem B947179 : Blo 944585 947179 := bstep (se 1 (by rfl) ⟨710384, by rfl⟩ : syracuseStep 947179 = 1420769) B1420769
theorem B947191 : Blo 944585 947191 := bstep (se 1 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 947191 = 1420787) B1420787
theorem B947211 : Blo 944585 947211 := bstep (se 1 (by rfl) ⟨710408, by rfl⟩ : syracuseStep 947211 = 1420817) B1420817
theorem B947223 : Blo 944585 947223 := bstep (se 1 (by rfl) ⟨710417, by rfl⟩ : syracuseStep 947223 = 1420835) B1420835
theorem B947243 : Blo 944585 947243 := bstep (se 1 (by rfl) ⟨710432, by rfl⟩ : syracuseStep 947243 = 1420865) B1420865
theorem B947255 : Blo 944585 947255 := bstep (se 1 (by rfl) ⟨710441, by rfl⟩ : syracuseStep 947255 = 1420883) B1420883
theorem B947275 : Blo 944585 947275 := bstep (se 1 (by rfl) ⟨710456, by rfl⟩ : syracuseStep 947275 = 1420913) B1420913
theorem B947287 : Blo 944585 947287 := bstep (se 1 (by rfl) ⟨710465, by rfl⟩ : syracuseStep 947287 = 1420931) B1420931
theorem B947307 : Blo 944585 947307 := bstep (se 1 (by rfl) ⟨710480, by rfl⟩ : syracuseStep 947307 = 1420961) B1420961
theorem B947319 : Blo 944585 947319 := bstep (se 1 (by rfl) ⟨710489, by rfl⟩ : syracuseStep 947319 = 1420979) B1420979
theorem B2126987 : Blo 944585 2126987 := bstep (se 1 (by rfl) ⟨1595240, by rfl⟩ : syracuseStep 2126987 = 3190481) B3190481
theorem B947339 : Blo 944585 947339 := bstep (se 1 (by rfl) ⟨710504, by rfl⟩ : syracuseStep 947339 = 1421009) B1421009
theorem B1438871 : Blo 944585 1438871 := bstep (se 1 (by rfl) ⟨1079153, by rfl⟩ : syracuseStep 1438871 = 2158307) B2158307
theorem B947351 : Blo 944585 947351 := bstep (se 1 (by rfl) ⟨710513, by rfl⟩ : syracuseStep 947351 = 1421027) B1421027
theorem B947371 : Blo 944585 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B1799347 : Blo 944585 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B947383 : Blo 944585 947383 := bstep (se 1 (by rfl) ⟨710537, by rfl⟩ : syracuseStep 947383 = 1421075) B1421075
theorem B2127041 : Blo 944585 2127041 := bstep (se 2 (by rfl) ⟨797640, by rfl⟩ : syracuseStep 2127041 = 1595281) B1595281
theorem B947403 : Blo 944585 947403 := bstep (se 1 (by rfl) ⟨710552, by rfl⟩ : syracuseStep 947403 = 1421105) B1421105
theorem B947415 : Blo 944585 947415 := bstep (se 1 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 947415 = 1421123) B1421123
theorem B947435 : Blo 944585 947435 := bstep (se 1 (by rfl) ⟨710576, by rfl⟩ : syracuseStep 947435 = 1421153) B1421153
theorem B947447 : Blo 944585 947447 := bstep (se 1 (by rfl) ⟨710585, by rfl⟩ : syracuseStep 947447 = 1421171) B1421171
theorem B947467 : Blo 944585 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B947479 : Blo 944585 947479 := bstep (se 1 (by rfl) ⟨710609, by rfl⟩ : syracuseStep 947479 = 1421219) B1421219
theorem B947499 : Blo 944585 947499 := bstep (se 1 (by rfl) ⟨710624, by rfl⟩ : syracuseStep 947499 = 1421249) B1421249
theorem B947511 : Blo 944585 947511 := bstep (se 1 (by rfl) ⟨710633, by rfl⟩ : syracuseStep 947511 = 1421267) B1421267
theorem B947531 : Blo 944585 947531 := bstep (se 1 (by rfl) ⟨710648, by rfl⟩ : syracuseStep 947531 = 1421297) B1421297
theorem B947543 : Blo 944585 947543 := bstep (se 1 (by rfl) ⟨710657, by rfl⟩ : syracuseStep 947543 = 1421315) B1421315
theorem B947563 : Blo 944585 947563 := bstep (se 1 (by rfl) ⟨710672, by rfl⟩ : syracuseStep 947563 = 1421345) B1421345
theorem B947575 : Blo 944585 947575 := bstep (se 1 (by rfl) ⟨710681, by rfl⟩ : syracuseStep 947575 = 1421363) B1421363
theorem B947595 : Blo 944585 947595 := bstep (se 1 (by rfl) ⟨710696, by rfl⟩ : syracuseStep 947595 = 1421393) B1421393
theorem B947607 : Blo 944585 947607 := bstep (se 1 (by rfl) ⟨710705, by rfl⟩ : syracuseStep 947607 = 1421411) B1421411
theorem B2127257 : Blo 944585 2127257 := bstep (se 2 (by rfl) ⟨797721, by rfl⟩ : syracuseStep 2127257 = 1595443) B1595443
theorem B947627 : Blo 944585 947627 := bstep (se 1 (by rfl) ⟨710720, by rfl⟩ : syracuseStep 947627 = 1421441) B1421441
theorem B947639 : Blo 944585 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B947659 : Blo 944585 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B947671 : Blo 944585 947671 := bstep (se 1 (by rfl) ⟨710753, by rfl⟩ : syracuseStep 947671 = 1421507) B1421507
theorem B947691 : Blo 944585 947691 := bstep (se 1 (by rfl) ⟨710768, by rfl⟩ : syracuseStep 947691 = 1421537) B1421537
theorem B2127347 : Blo 944585 2127347 := bstep (se 1 (by rfl) ⟨1595510, by rfl⟩ : syracuseStep 2127347 = 3191021) B3191021
theorem B947703 : Blo 944585 947703 := bstep (se 1 (by rfl) ⟨710777, by rfl⟩ : syracuseStep 947703 = 1421555) B1421555
theorem B947723 : Blo 944585 947723 := bstep (se 1 (by rfl) ⟨710792, by rfl⟩ : syracuseStep 947723 = 1421585) B1421585
theorem B2127383 : Blo 944585 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B947735 : Blo 944585 947735 := bstep (se 1 (by rfl) ⟨710801, by rfl⟩ : syracuseStep 947735 = 1421603) B1421603
theorem B947755 : Blo 944585 947755 := bstep (se 1 (by rfl) ⟨710816, by rfl⟩ : syracuseStep 947755 = 1421633) B1421633
theorem B947767 : Blo 944585 947767 := bstep (se 1 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 947767 = 1421651) B1421651
theorem B947787 : Blo 944585 947787 := bstep (se 1 (by rfl) ⟨710840, by rfl⟩ : syracuseStep 947787 = 1421681) B1421681
theorem B947799 : Blo 944585 947799 := bstep (se 1 (by rfl) ⟨710849, by rfl⟩ : syracuseStep 947799 = 1421699) B1421699
theorem B947819 : Blo 944585 947819 := bstep (se 1 (by rfl) ⟨710864, by rfl⟩ : syracuseStep 947819 = 1421729) B1421729
theorem B1799795 : Blo 944585 1799795 := bstep (se 1 (by rfl) ⟨1349846, by rfl⟩ : syracuseStep 1799795 = 2699693) B2699693
theorem B947831 : Blo 944585 947831 := bstep (se 1 (by rfl) ⟨710873, by rfl⟩ : syracuseStep 947831 = 1421747) B1421747
theorem B1439371 : Blo 944585 1439371 := bstep (se 1 (by rfl) ⟨1079528, by rfl⟩ : syracuseStep 1439371 = 2159057) B2159057
theorem B947851 : Blo 944585 947851 := bstep (se 1 (by rfl) ⟨710888, by rfl⟩ : syracuseStep 947851 = 1421777) B1421777
theorem B947863 : Blo 944585 947863 := bstep (se 1 (by rfl) ⟨710897, by rfl⟩ : syracuseStep 947863 = 1421795) B1421795
theorem B1799833 : Blo 944585 1799833 := bstep (se 2 (by rfl) ⟨674937, by rfl⟩ : syracuseStep 1799833 = 1349875) B1349875
theorem B947883 : Blo 944585 947883 := bstep (se 1 (by rfl) ⟨710912, by rfl⟩ : syracuseStep 947883 = 1421825) B1421825
theorem B947895 : Blo 944585 947895 := bstep (se 1 (by rfl) ⟨710921, by rfl⟩ : syracuseStep 947895 = 1421843) B1421843
theorem B2127563 : Blo 944585 2127563 := bstep (se 1 (by rfl) ⟨1595672, by rfl⟩ : syracuseStep 2127563 = 3191345) B3191345
theorem B947915 : Blo 944585 947915 := bstep (se 1 (by rfl) ⟨710936, by rfl⟩ : syracuseStep 947915 = 1421873) B1421873
theorem B947927 : Blo 944585 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B8091353 : Blo 944585 8091353 := bstep (se 2 (by rfl) ⟨3034257, by rfl⟩ : syracuseStep 8091353 = 6068515) B6068515
theorem B947947 : Blo 944585 947947 := bstep (se 1 (by rfl) ⟨710960, by rfl⟩ : syracuseStep 947947 = 1421921) B1421921
theorem B947959 : Blo 944585 947959 := bstep (se 1 (by rfl) ⟨710969, by rfl⟩ : syracuseStep 947959 = 1421939) B1421939
theorem B2127617 : Blo 944585 2127617 := bstep (se 2 (by rfl) ⟨797856, by rfl⟩ : syracuseStep 2127617 = 1595713) B1595713
theorem B947979 : Blo 944585 947979 := bstep (se 1 (by rfl) ⟨710984, by rfl⟩ : syracuseStep 947979 = 1421969) B1421969
theorem B947991 : Blo 944585 947991 := bstep (se 1 (by rfl) ⟨710993, by rfl⟩ : syracuseStep 947991 = 1421987) B1421987
theorem B948011 : Blo 944585 948011 := bstep (se 1 (by rfl) ⟨711008, by rfl⟩ : syracuseStep 948011 = 1422017) B1422017
theorem B948023 : Blo 944585 948023 := bstep (se 1 (by rfl) ⟨711017, by rfl⟩ : syracuseStep 948023 = 1422035) B1422035
theorem B948043 : Blo 944585 948043 := bstep (se 1 (by rfl) ⟨711032, by rfl⟩ : syracuseStep 948043 = 1422065) B1422065
theorem B948055 : Blo 944585 948055 := bstep (se 1 (by rfl) ⟨711041, by rfl⟩ : syracuseStep 948055 = 1422083) B1422083
theorem B2881369 : Blo 944585 2881369 := bstep (se 2 (by rfl) ⟨1080513, by rfl⟩ : syracuseStep 2881369 = 2161027) B2161027
theorem B948075 : Blo 944585 948075 := bstep (se 1 (by rfl) ⟨711056, by rfl⟩ : syracuseStep 948075 = 1422113) B1422113
theorem B948087 : Blo 944585 948087 := bstep (se 1 (by rfl) ⟨711065, by rfl⟩ : syracuseStep 948087 = 1422131) B1422131
theorem B948107 : Blo 944585 948107 := bstep (se 1 (by rfl) ⟨711080, by rfl⟩ : syracuseStep 948107 = 1422161) B1422161
theorem B1079191 : Blo 944585 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B948119 : Blo 944585 948119 := bstep (se 1 (by rfl) ⟨711089, by rfl⟩ : syracuseStep 948119 = 1422179) B1422179
theorem B948139 : Blo 944585 948139 := bstep (se 1 (by rfl) ⟨711104, by rfl⟩ : syracuseStep 948139 = 1422209) B1422209
theorem B948151 : Blo 944585 948151 := bstep (se 1 (by rfl) ⟨711113, by rfl⟩ : syracuseStep 948151 = 1422227) B1422227
theorem B948171 : Blo 944585 948171 := bstep (se 1 (by rfl) ⟨711128, by rfl⟩ : syracuseStep 948171 = 1422257) B1422257
theorem B948183 : Blo 944585 948183 := bstep (se 1 (by rfl) ⟨711137, by rfl⟩ : syracuseStep 948183 = 1422275) B1422275
theorem B2127833 : Blo 944585 2127833 := bstep (se 2 (by rfl) ⟨797937, by rfl⟩ : syracuseStep 2127833 = 1595875) B1595875
theorem B948203 : Blo 944585 948203 := bstep (se 1 (by rfl) ⟨711152, by rfl⟩ : syracuseStep 948203 = 1422305) B1422305
theorem B948215 : Blo 944585 948215 := bstep (se 1 (by rfl) ⟨711161, by rfl⟩ : syracuseStep 948215 = 1422323) B1422323
theorem B948235 : Blo 944585 948235 := bstep (se 1 (by rfl) ⟨711176, by rfl⟩ : syracuseStep 948235 = 1422353) B1422353
theorem B948247 : Blo 944585 948247 := bstep (se 1 (by rfl) ⟨711185, by rfl⟩ : syracuseStep 948247 = 1422371) B1422371
theorem B948267 : Blo 944585 948267 := bstep (se 1 (by rfl) ⟨711200, by rfl⟩ : syracuseStep 948267 = 1422401) B1422401
theorem B2127923 : Blo 944585 2127923 := bstep (se 1 (by rfl) ⟨1595942, by rfl⟩ : syracuseStep 2127923 = 3191885) B3191885
theorem B948279 : Blo 944585 948279 := bstep (se 1 (by rfl) ⟨711209, by rfl⟩ : syracuseStep 948279 = 1422419) B1422419
theorem B948299 : Blo 944585 948299 := bstep (se 1 (by rfl) ⟨711224, by rfl⟩ : syracuseStep 948299 = 1422449) B1422449
theorem B2127959 : Blo 944585 2127959 := bstep (se 1 (by rfl) ⟨1595969, by rfl⟩ : syracuseStep 2127959 = 3191939) B3191939
theorem B948311 : Blo 944585 948311 := bstep (se 1 (by rfl) ⟨711233, by rfl⟩ : syracuseStep 948311 = 1422467) B1422467
theorem B1800281 : Blo 944585 1800281 := bstep (se 2 (by rfl) ⟨675105, by rfl⟩ : syracuseStep 1800281 = 1350211) B1350211
theorem B7796837 : Blo 944585 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B948331 : Blo 944585 948331 := bstep (se 1 (by rfl) ⟨711248, by rfl⟩ : syracuseStep 948331 = 1422497) B1422497
theorem B948343 : Blo 944585 948343 := bstep (se 1 (by rfl) ⟨711257, by rfl⟩ : syracuseStep 948343 = 1422515) B1422515
theorem B948363 : Blo 944585 948363 := bstep (se 1 (by rfl) ⟨711272, by rfl⟩ : syracuseStep 948363 = 1422545) B1422545
theorem B948375 : Blo 944585 948375 := bstep (se 1 (by rfl) ⟨711281, by rfl⟩ : syracuseStep 948375 = 1422563) B1422563
theorem B948395 : Blo 944585 948395 := bstep (se 1 (by rfl) ⟨711296, by rfl⟩ : syracuseStep 948395 = 1422593) B1422593
theorem B948407 : Blo 944585 948407 := bstep (se 1 (by rfl) ⟨711305, by rfl⟩ : syracuseStep 948407 = 1422611) B1422611
theorem B948427 : Blo 944585 948427 := bstep (se 1 (by rfl) ⟨711320, by rfl⟩ : syracuseStep 948427 = 1422641) B1422641
theorem B948439 : Blo 944585 948439 := bstep (se 1 (by rfl) ⟨711329, by rfl⟩ : syracuseStep 948439 = 1422659) B1422659
theorem B948459 : Blo 944585 948459 := bstep (se 1 (by rfl) ⟨711344, by rfl⟩ : syracuseStep 948459 = 1422689) B1422689
theorem B948471 : Blo 944585 948471 := bstep (se 1 (by rfl) ⟨711353, by rfl⟩ : syracuseStep 948471 = 1422707) B1422707
theorem B2128139 : Blo 944585 2128139 := bstep (se 1 (by rfl) ⟨1596104, by rfl⟩ : syracuseStep 2128139 = 3192209) B3192209
theorem B948491 : Blo 944585 948491 := bstep (se 1 (by rfl) ⟨711368, by rfl⟩ : syracuseStep 948491 = 1422737) B1422737
theorem B948503 : Blo 944585 948503 := bstep (se 1 (by rfl) ⟨711377, by rfl⟩ : syracuseStep 948503 = 1422755) B1422755
theorem B948523 : Blo 944585 948523 := bstep (se 1 (by rfl) ⟨711392, by rfl⟩ : syracuseStep 948523 = 1422785) B1422785
theorem B948535 : Blo 944585 948535 := bstep (se 1 (by rfl) ⟨711401, by rfl⟩ : syracuseStep 948535 = 1422803) B1422803
theorem B4782401 : Blo 944585 4782401 := bstep (se 2 (by rfl) ⟨1793400, by rfl⟩ : syracuseStep 4782401 = 3586801) B3586801
theorem B2554177 : Blo 944585 2554177 := bstep (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) B1915633
theorem B2128193 : Blo 944585 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B948555 : Blo 944585 948555 := bstep (se 1 (by rfl) ⟨711416, by rfl⟩ : syracuseStep 948555 = 1422833) B1422833
theorem B948567 : Blo 944585 948567 := bstep (se 1 (by rfl) ⟨711425, by rfl⟩ : syracuseStep 948567 = 1422851) B1422851
theorem B6060419 : Blo 944585 6060419 := bstep (se 1 (by rfl) ⟨4545314, by rfl⟩ : syracuseStep 6060419 = 9090629) B9090629
theorem B8190359 : Blo 944585 8190359 := bstep (se 1 (by rfl) ⟨6142769, by rfl⟩ : syracuseStep 8190359 = 12285539) B12285539
theorem B2128409 : Blo 944585 2128409 := bstep (se 2 (by rfl) ⟨798153, by rfl⟩ : syracuseStep 2128409 = 1596307) B1596307
theorem B1702475 : Blo 944585 1702475 := bstep (se 1 (by rfl) ⟨1276856, by rfl⟩ : syracuseStep 1702475 = 2553713) B2553713
theorem B16153181 : Blo 944585 16153181 := bstep (se 3 (by rfl) ⟨3028721, by rfl⟩ : syracuseStep 16153181 = 6057443) B6057443
theorem B2128499 : Blo 944585 2128499 := bstep (se 1 (by rfl) ⟨1596374, by rfl⟩ : syracuseStep 2128499 = 3192749) B3192749
theorem B2128535 : Blo 944585 2128535 := bstep (se 1 (by rfl) ⟨1596401, by rfl⟩ : syracuseStep 2128535 = 3192803) B3192803
theorem B1538713 : Blo 944585 1538713 := bstep (se 2 (by rfl) ⟨577017, by rfl⟩ : syracuseStep 1538713 = 1154035) B1154035
theorem B2128715 : Blo 944585 2128715 := bstep (se 1 (by rfl) ⟨1596536, by rfl⟩ : syracuseStep 2128715 = 3193073) B3193073
theorem B2128769 : Blo 944585 2128769 := bstep (se 2 (by rfl) ⟨798288, by rfl⟩ : syracuseStep 2128769 = 1596577) B1596577
theorem B1702937 : Blo 944585 1702937 := bstep (se 2 (by rfl) ⟨638601, by rfl⟩ : syracuseStep 1702937 = 1277203) B1277203
theorem B2128985 : Blo 944585 2128985 := bstep (se 2 (by rfl) ⟨798369, by rfl⟩ : syracuseStep 2128985 = 1596739) B1596739
theorem B3636355 : Blo 944585 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B2391191 : Blo 944585 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B2129075 : Blo 944585 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B2129111 : Blo 944585 2129111 := bstep (se 1 (by rfl) ⟨1596833, by rfl⟩ : syracuseStep 2129111 = 3193667) B3193667
theorem B8092993 : Blo 944585 8092993 := bstep (se 2 (by rfl) ⟨3034872, by rfl⟩ : syracuseStep 8092993 = 6069745) B6069745
theorem B2129291 : Blo 944585 2129291 := bstep (se 1 (by rfl) ⟨1596968, by rfl⟩ : syracuseStep 2129291 = 3193937) B3193937
theorem B2129345 : Blo 944585 2129345 := bstep (se 2 (by rfl) ⟨798504, by rfl⟩ : syracuseStep 2129345 = 1597009) B1597009
theorem B2129561 : Blo 944585 2129561 := bstep (se 2 (by rfl) ⟨798585, by rfl⟩ : syracuseStep 2129561 = 1597171) B1597171
theorem B2129651 : Blo 944585 2129651 := bstep (se 1 (by rfl) ⟨1597238, by rfl⟩ : syracuseStep 2129651 = 3194477) B3194477
theorem B2129687 : Blo 944585 2129687 := bstep (se 1 (by rfl) ⟨1597265, by rfl⟩ : syracuseStep 2129687 = 3194531) B3194531
theorem B2392001 : Blo 944585 2392001 := bstep (se 2 (by rfl) ⟨897000, by rfl⟩ : syracuseStep 2392001 = 1794001) B1794001
theorem B2129867 : Blo 944585 2129867 := bstep (se 1 (by rfl) ⟨1597400, by rfl⟩ : syracuseStep 2129867 = 3194801) B3194801
theorem B1277959 : Blo 944585 1277959 := bstep (se 1 (by rfl) ⟨958469, by rfl⟩ : syracuseStep 1277959 = 1916939) B1916939
theorem B5537803 : Blo 944585 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B4096061 : Blo 944585 4096061 := bstep (se 3 (by rfl) ⟨768011, by rfl⟩ : syracuseStep 4096061 = 1536023) B1536023
theorem B5767361 : Blo 944585 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B2130191 : Blo 944585 2130191 := bstep (se 1 (by rfl) ⟨1597643, by rfl⟩ : syracuseStep 2130191 = 3195287) B3195287
theorem B4325647 : Blo 944585 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B2130209 : Blo 944585 2130209 := bstep (se 2 (by rfl) ⟨798828, by rfl⟩ : syracuseStep 2130209 = 1597657) B1597657
theorem B1442107 : Blo 944585 1442107 := bstep (se 1 (by rfl) ⟨1081580, by rfl⟩ : syracuseStep 1442107 = 2163161) B2163161
theorem B2556307 : Blo 944585 2556307 := bstep (se 1 (by rfl) ⟨1917230, by rfl⟩ : syracuseStep 2556307 = 3834461) B3834461
theorem B4784669 : Blo 944585 4784669 := bstep (se 3 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 4784669 = 1794251) B1794251
theorem B2130551 : Blo 944585 2130551 := bstep (se 1 (by rfl) ⟨1597913, by rfl⟩ : syracuseStep 2130551 = 3195827) B3195827
theorem B3408641 : Blo 944585 3408641 := bstep (se 2 (by rfl) ⟨1278240, by rfl⟩ : syracuseStep 3408641 = 2556481) B2556481
theorem B2130731 : Blo 944585 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B4785155 : Blo 944585 4785155 := bstep (se 1 (by rfl) ⟨3588866, by rfl⟩ : syracuseStep 4785155 = 7177733) B7177733
theorem B2131091 : Blo 944585 2131091 := bstep (se 1 (by rfl) ⟨1598318, by rfl⟩ : syracuseStep 2131091 = 3196637) B3196637
theorem B2131145 : Blo 944585 2131145 := bstep (se 2 (by rfl) ⟨799179, by rfl⟩ : syracuseStep 2131145 = 1598359) B1598359
theorem B2393459 : Blo 944585 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B437061091 : Blo 944585 437061091 := bstep (se 1 (by rfl) ⟨327795818, by rfl⟩ : syracuseStep 437061091 = 655591637) B655591637
theorem B5113651 : Blo 944585 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B2557757 : Blo 944585 2557757 := bstep (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) B959159
theorem B13141835 : Blo 944585 13141835 := bstep (se 1 (by rfl) ⟨9856376, by rfl⟩ : syracuseStep 13141835 = 19712753) B19712753
theorem B2557811 : Blo 944585 2557811 := bstep (se 1 (by rfl) ⟨1918358, by rfl⟩ : syracuseStep 2557811 = 3836717) B3836717
theorem B2393975 : Blo 944585 2393975 := bstep (se 1 (by rfl) ⟨1795481, by rfl⟩ : syracuseStep 2393975 = 3590963) B3590963
theorem B1345415 : Blo 944585 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B2131847 : Blo 944585 2131847 := bstep (se 1 (by rfl) ⟨1598885, by rfl⟩ : syracuseStep 2131847 = 3197771) B3197771
theorem B2132027 : Blo 944585 2132027 := bstep (se 1 (by rfl) ⟨1599020, by rfl⟩ : syracuseStep 2132027 = 3198041) B3198041
theorem B1345609 : Blo 944585 1345609 := bstep (se 2 (by rfl) ⟨504603, by rfl⟩ : syracuseStep 1345609 = 1009207) B1009207
theorem B2132153 : Blo 944585 2132153 := bstep (se 2 (by rfl) ⟨799557, by rfl⟩ : syracuseStep 2132153 = 1599115) B1599115
theorem B1870025 : Blo 944585 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B14780819 : Blo 944585 14780819 := bstep (se 1 (by rfl) ⟨11085614, by rfl⟩ : syracuseStep 14780819 = 22171229) B22171229
theorem B7178705 : Blo 944585 7178705 := bstep (se 2 (by rfl) ⟨2692014, by rfl⟩ : syracuseStep 7178705 = 5384029) B5384029
theorem B21629405 : Blo 944585 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B2132495 : Blo 944585 2132495 := bstep (se 1 (by rfl) ⟨1599371, by rfl⟩ : syracuseStep 2132495 = 3198743) B3198743
theorem B2132513 : Blo 944585 2132513 := bstep (se 2 (by rfl) ⟨799692, by rfl⟩ : syracuseStep 2132513 = 1599385) B1599385
theorem B19466795 : Blo 944585 19466795 := bstep (se 1 (by rfl) ⟨14600096, by rfl⟩ : syracuseStep 19466795 = 29200193) B29200193
theorem B1706555 : Blo 944585 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B4786775 : Blo 944585 4786775 := bstep (se 1 (by rfl) ⟨3590081, by rfl⟩ : syracuseStep 4786775 = 7180163) B7180163
theorem B1346167 : Blo 944585 1346167 := bstep (se 1 (by rfl) ⟨1009625, by rfl⟩ : syracuseStep 1346167 = 2019251) B2019251
theorem B2394967 : Blo 944585 2394967 := bstep (se 1 (by rfl) ⟨1796225, by rfl⟩ : syracuseStep 2394967 = 3592451) B3592451
theorem B16157555 : Blo 944585 16157555 := bstep (se 1 (by rfl) ⟨12118166, by rfl⟩ : syracuseStep 16157555 = 24236333) B24236333
theorem B2132855 : Blo 944585 2132855 := bstep (se 1 (by rfl) ⟨1599641, by rfl⟩ : syracuseStep 2132855 = 3199283) B3199283
theorem B2133035 : Blo 944585 2133035 := bstep (se 1 (by rfl) ⟨1599776, by rfl⟩ : syracuseStep 2133035 = 3199553) B3199553
theorem B4787261 : Blo 944585 4787261 := bstep (se 3 (by rfl) ⟨897611, by rfl⟩ : syracuseStep 4787261 = 1795223) B1795223
theorem B3836989 : Blo 944585 3836989 := bstep (se 3 (by rfl) ⟨719435, by rfl⟩ : syracuseStep 3836989 = 1438871) B1438871
theorem B2395271 : Blo 944585 2395271 := bstep (se 1 (by rfl) ⟨1796453, by rfl⟩ : syracuseStep 2395271 = 3592907) B3592907
theorem B2919577 : Blo 944585 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B8621257 : Blo 944585 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B2395403 : Blo 944585 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B6065441 : Blo 944585 6065441 := bstep (se 2 (by rfl) ⟨2274540, by rfl⟩ : syracuseStep 6065441 = 4549081) B4549081
theorem B1346873 : Blo 944585 1346873 := bstep (se 2 (by rfl) ⟨505077, by rfl⟩ : syracuseStep 1346873 = 1010155) B1010155
theorem B3280187 : Blo 944585 3280187 := bstep (se 1 (by rfl) ⟨2460140, by rfl⟩ : syracuseStep 3280187 = 4920281) B4920281
theorem B6065543 : Blo 944585 6065543 := bstep (se 1 (by rfl) ⟨4549157, by rfl⟩ : syracuseStep 6065543 = 9098315) B9098315
theorem B2559367 : Blo 944585 2559367 := bstep (se 1 (by rfl) ⟨1919525, by rfl⟩ : syracuseStep 2559367 = 3839051) B3839051
theorem B1346959 : Blo 944585 1346959 := bstep (se 1 (by rfl) ⟨1010219, by rfl⟩ : syracuseStep 1346959 = 2020439) B2020439
theorem B2133395 : Blo 944585 2133395 := bstep (se 1 (by rfl) ⟨1600046, by rfl⟩ : syracuseStep 2133395 = 3200093) B3200093
theorem B1346987 : Blo 944585 1346987 := bstep (se 1 (by rfl) ⟨1010240, by rfl⟩ : syracuseStep 1346987 = 2020481) B2020481
theorem B2690489 : Blo 944585 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B2133449 : Blo 944585 2133449 := bstep (se 2 (by rfl) ⟨800043, by rfl⟩ : syracuseStep 2133449 = 1600087) B1600087
theorem B2690603 : Blo 944585 2690603 := bstep (se 1 (by rfl) ⟨2017952, by rfl⟩ : syracuseStep 2690603 = 4035905) B4035905
theorem B14946049 : Blo 944585 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B18452225 : Blo 944585 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B2395919 : Blo 944585 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B1707895 : Blo 944585 1707895 := bstep (se 1 (by rfl) ⟨1280921, by rfl⟩ : syracuseStep 1707895 = 2561843) B2561843
theorem B2396051 : Blo 944585 2396051 := bstep (se 1 (by rfl) ⟨1797038, by rfl⟩ : syracuseStep 2396051 = 3594077) B3594077
theorem B2134151 : Blo 944585 2134151 := bstep (se 1 (by rfl) ⟨1600613, by rfl⟩ : syracuseStep 2134151 = 3201227) B3201227
theorem B24875209 : Blo 944585 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B2691731 : Blo 944585 2691731 := bstep (se 1 (by rfl) ⟨2018798, by rfl⟩ : syracuseStep 2691731 = 4037597) B4037597
theorem B4789043 : Blo 944585 4789043 := bstep (se 1 (by rfl) ⟨3591782, by rfl⟩ : syracuseStep 4789043 = 7183565) B7183565
theorem B1708919 : Blo 944585 1708919 := bstep (se 1 (by rfl) ⟨1281689, by rfl⟩ : syracuseStep 1708919 = 2563379) B2563379
theorem B3838873 : Blo 944585 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6656921 : Blo 944585 6656921 := bstep (se 2 (by rfl) ⟨2496345, by rfl⟩ : syracuseStep 6656921 = 4992691) B4992691
theorem B14554037 : Blo 944585 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B2397185 : Blo 944585 2397185 := bstep (se 2 (by rfl) ⟨898944, by rfl⟩ : syracuseStep 2397185 = 1797889) B1797889
theorem B2692129 : Blo 944585 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B4789367 : Blo 944585 4789367 := bstep (se 1 (by rfl) ⟨3592025, by rfl⟩ : syracuseStep 4789367 = 7184051) B7184051
theorem B2397559 : Blo 944585 2397559 := bstep (se 1 (by rfl) ⟨1798169, by rfl⟩ : syracuseStep 2397559 = 3596339) B3596339
theorem B2397995 : Blo 944585 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B5379929 : Blo 944585 5379929 := bstep (se 2 (by rfl) ⟨2017473, by rfl⟩ : syracuseStep 5379929 = 4034947) B4034947
theorem B2693017 : Blo 944585 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B4790339 : Blo 944585 4790339 := bstep (se 1 (by rfl) ⟨3592754, by rfl⟩ : syracuseStep 4790339 = 7185509) B7185509
theorem B1513657 : Blo 944585 1513657 := bstep (se 2 (by rfl) ⟨567621, by rfl⟩ : syracuseStep 1513657 = 1135243) B1135243
theorem B1349903 : Blo 944585 1349903 := bstep (se 1 (by rfl) ⟨1012427, by rfl⟩ : syracuseStep 1349903 = 2024855) B2024855
theorem B2693405 : Blo 944585 2693405 := bstep (se 3 (by rfl) ⟨505013, by rfl⟩ : syracuseStep 2693405 = 1010027) B1010027
theorem B4790663 : Blo 944585 4790663 := bstep (se 1 (by rfl) ⟨3592997, by rfl⟩ : syracuseStep 4790663 = 7185995) B7185995
theorem B2398835 : Blo 944585 2398835 := bstep (se 1 (by rfl) ⟨1799126, by rfl⟩ : syracuseStep 2398835 = 3598253) B3598253
theorem B2398855 : Blo 944585 2398855 := bstep (se 1 (by rfl) ⟨1799141, by rfl⟩ : syracuseStep 2398855 = 3598283) B3598283
theorem B6069107 : Blo 944585 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B2399129 : Blo 944585 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B3415069 : Blo 944585 3415069 := bstep (se 3 (by rfl) ⟨640325, by rfl⟩ : syracuseStep 3415069 = 1280651) B1280651
theorem B2399291 : Blo 944585 2399291 := bstep (se 1 (by rfl) ⟨1799468, by rfl⟩ : syracuseStep 2399291 = 3598937) B3598937
theorem B2727179 : Blo 944585 2727179 := bstep (se 1 (by rfl) ⟨2045384, by rfl⟩ : syracuseStep 2727179 = 4090769) B4090769
theorem B2399503 : Blo 944585 2399503 := bstep (se 1 (by rfl) ⟨1799627, by rfl⟩ : syracuseStep 2399503 = 3599255) B3599255
theorem B4037921 : Blo 944585 4037921 := bstep (se 2 (by rfl) ⟨1514220, by rfl⟩ : syracuseStep 4037921 = 3028441) B3028441
theorem B20716859 : Blo 944585 20716859 := bstep (se 1 (by rfl) ⟨15537644, by rfl⟩ : syracuseStep 20716859 = 31075289) B31075289
theorem B2399777 : Blo 944585 2399777 := bstep (se 2 (by rfl) ⟨899916, by rfl⟩ : syracuseStep 2399777 = 1799833) B1799833
theorem B1515143 : Blo 944585 1515143 := bstep (se 1 (by rfl) ⟨1136357, by rfl⟩ : syracuseStep 1515143 = 2272715) B2272715
theorem B1416905 : Blo 944585 1416905 := bstep (se 2 (by rfl) ⟨531339, by rfl⟩ : syracuseStep 1416905 = 1062679) B1062679
theorem B3841825 : Blo 944585 3841825 := bstep (se 2 (by rfl) ⟨1440684, by rfl⟩ : syracuseStep 3841825 = 2881369) B2881369
theorem B9084707 : Blo 944585 9084707 := bstep (se 1 (by rfl) ⟨6813530, by rfl⟩ : syracuseStep 9084707 = 13627061) B13627061
theorem B1417019 : Blo 944585 1417019 := bstep (se 1 (by rfl) ⟨1062764, by rfl⟩ : syracuseStep 1417019 = 2125529) B2125529
theorem B2301755 : Blo 944585 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1417079 : Blo 944585 1417079 := bstep (se 1 (by rfl) ⟨1062809, by rfl⟩ : syracuseStep 1417079 = 2125619) B2125619
theorem B1417103 : Blo 944585 1417103 := bstep (se 1 (by rfl) ⟨1062827, by rfl⟩ : syracuseStep 1417103 = 2125655) B2125655
theorem B1417145 : Blo 944585 1417145 := bstep (se 2 (by rfl) ⟨531429, by rfl⟩ : syracuseStep 1417145 = 1062859) B1062859
theorem B1417223 : Blo 944585 1417223 := bstep (se 1 (by rfl) ⟨1062917, by rfl⟩ : syracuseStep 1417223 = 2125835) B2125835
theorem B1417259 : Blo 944585 1417259 := bstep (se 1 (by rfl) ⟨1062944, by rfl⟩ : syracuseStep 1417259 = 2125889) B2125889
theorem B1417289 : Blo 944585 1417289 := bstep (se 2 (by rfl) ⟨531483, by rfl⟩ : syracuseStep 1417289 = 1062967) B1062967
theorem B1417403 : Blo 944585 1417403 := bstep (se 1 (by rfl) ⟨1063052, by rfl⟩ : syracuseStep 1417403 = 2126105) B2126105
theorem B1417463 : Blo 944585 1417463 := bstep (se 1 (by rfl) ⟨1063097, by rfl⟩ : syracuseStep 1417463 = 2126195) B2126195
theorem B1417487 : Blo 944585 1417487 := bstep (se 1 (by rfl) ⟨1063115, by rfl⟩ : syracuseStep 1417487 = 2126231) B2126231
theorem B2105633 : Blo 944585 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B1417529 : Blo 944585 1417529 := bstep (se 2 (by rfl) ⟨531573, by rfl⟩ : syracuseStep 1417529 = 1063147) B1063147
theorem B9085243 : Blo 944585 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B1417607 : Blo 944585 1417607 := bstep (se 1 (by rfl) ⟨1063205, by rfl⟩ : syracuseStep 1417607 = 2126411) B2126411
theorem B1417643 : Blo 944585 1417643 := bstep (se 1 (by rfl) ⟨1063232, by rfl⟩ : syracuseStep 1417643 = 2126465) B2126465
theorem B1417673 : Blo 944585 1417673 := bstep (se 2 (by rfl) ⟨531627, by rfl⟩ : syracuseStep 1417673 = 1063255) B1063255
theorem B2400779 : Blo 944585 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B1417787 : Blo 944585 1417787 := bstep (se 1 (by rfl) ⟨1063340, by rfl⟩ : syracuseStep 1417787 = 2126681) B2126681
theorem B12132929 : Blo 944585 12132929 := bstep (se 2 (by rfl) ⟨4549848, by rfl⟩ : syracuseStep 12132929 = 9099697) B9099697
theorem B1417847 : Blo 944585 1417847 := bstep (se 1 (by rfl) ⟨1063385, by rfl⟩ : syracuseStep 1417847 = 2126771) B2126771
theorem B2433671 : Blo 944585 2433671 := bstep (se 1 (by rfl) ⟨1825253, by rfl⟩ : syracuseStep 2433671 = 3650507) B3650507
theorem B1417871 : Blo 944585 1417871 := bstep (se 1 (by rfl) ⟨1063403, by rfl⟩ : syracuseStep 1417871 = 2126807) B2126807
theorem B1417913 : Blo 944585 1417913 := bstep (se 2 (by rfl) ⟨531717, by rfl⟩ : syracuseStep 1417913 = 1063435) B1063435
theorem B7283429 : Blo 944585 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B1417991 : Blo 944585 1417991 := bstep (se 1 (by rfl) ⟨1063493, by rfl⟩ : syracuseStep 1417991 = 2126987) B2126987
theorem B1418027 : Blo 944585 1418027 := bstep (se 1 (by rfl) ⟨1063520, by rfl⟩ : syracuseStep 1418027 = 2127041) B2127041
theorem B2695979 : Blo 944585 2695979 := bstep (se 1 (by rfl) ⟨2021984, by rfl⟩ : syracuseStep 2695979 = 4043969) B4043969
theorem B1418057 : Blo 944585 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B5383097 : Blo 944585 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B1418171 : Blo 944585 1418171 := bstep (se 1 (by rfl) ⟨1063628, by rfl⟩ : syracuseStep 1418171 = 2127257) B2127257
theorem B1418231 : Blo 944585 1418231 := bstep (se 1 (by rfl) ⟨1063673, by rfl⟩ : syracuseStep 1418231 = 2127347) B2127347
theorem B10232837 : Blo 944585 10232837 := bstep (se 4 (by rfl) ⟨959328, by rfl⟩ : syracuseStep 10232837 = 1918657) B1918657
theorem B1418255 : Blo 944585 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B1418297 : Blo 944585 1418297 := bstep (se 2 (by rfl) ⟨531861, by rfl⟩ : syracuseStep 1418297 = 1063723) B1063723
theorem B1418375 : Blo 944585 1418375 := bstep (se 1 (by rfl) ⟨1063781, by rfl⟩ : syracuseStep 1418375 = 2127563) B2127563
theorem B1418411 : Blo 944585 1418411 := bstep (se 1 (by rfl) ⟨1063808, by rfl⟩ : syracuseStep 1418411 = 2127617) B2127617
theorem B1418441 : Blo 944585 1418441 := bstep (se 2 (by rfl) ⟨531915, by rfl⟩ : syracuseStep 1418441 = 1063831) B1063831
theorem B1516745 : Blo 944585 1516745 := bstep (se 2 (by rfl) ⟨568779, by rfl⟩ : syracuseStep 1516745 = 1137559) B1137559
theorem B1418555 : Blo 944585 1418555 := bstep (se 1 (by rfl) ⟨1063916, by rfl⟩ : syracuseStep 1418555 = 2127833) B2127833
theorem B1418615 : Blo 944585 1418615 := bstep (se 1 (by rfl) ⟨1063961, by rfl⟩ : syracuseStep 1418615 = 2127923) B2127923
theorem B1418639 : Blo 944585 1418639 := bstep (se 1 (by rfl) ⟨1063979, by rfl⟩ : syracuseStep 1418639 = 2127959) B2127959
theorem B1418681 : Blo 944585 1418681 := bstep (se 2 (by rfl) ⟨532005, by rfl⟩ : syracuseStep 1418681 = 1064011) B1064011
theorem B1418759 : Blo 944585 1418759 := bstep (se 1 (by rfl) ⟨1064069, by rfl⟩ : syracuseStep 1418759 = 2128139) B2128139
theorem B3188267 : Blo 944585 3188267 := bstep (se 1 (by rfl) ⟨2391200, by rfl⟩ : syracuseStep 3188267 = 4782401) B4782401
theorem B1418795 : Blo 944585 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B1418825 : Blo 944585 1418825 := bstep (se 2 (by rfl) ⟨532059, by rfl⟩ : syracuseStep 1418825 = 1064119) B1064119
theorem B9217613 : Blo 944585 9217613 := bstep (se 3 (by rfl) ⟨1728302, by rfl⟩ : syracuseStep 9217613 = 3456605) B3456605
theorem B4040279 : Blo 944585 4040279 := bstep (se 1 (by rfl) ⟨3030209, by rfl⟩ : syracuseStep 4040279 = 6060419) B6060419
theorem B1418939 : Blo 944585 1418939 := bstep (se 1 (by rfl) ⟨1064204, by rfl⟩ : syracuseStep 1418939 = 2128409) B2128409
theorem B1418999 : Blo 944585 1418999 := bstep (se 1 (by rfl) ⟨1064249, by rfl⟩ : syracuseStep 1418999 = 2128499) B2128499
theorem B10790657 : Blo 944585 10790657 := bstep (se 2 (by rfl) ⟨4046496, by rfl⟩ : syracuseStep 10790657 = 8092993) B8092993
theorem B1419023 : Blo 944585 1419023 := bstep (se 1 (by rfl) ⟨1064267, by rfl⟩ : syracuseStep 1419023 = 2128535) B2128535
theorem B1419065 : Blo 944585 1419065 := bstep (se 2 (by rfl) ⟨532149, by rfl⟩ : syracuseStep 1419065 = 1064299) B1064299
theorem B4794227 : Blo 944585 4794227 := bstep (se 1 (by rfl) ⟨3595670, by rfl⟩ : syracuseStep 4794227 = 7191341) B7191341
theorem B1419143 : Blo 944585 1419143 := bstep (se 1 (by rfl) ⟨1064357, by rfl⟩ : syracuseStep 1419143 = 2128715) B2128715
theorem B1419179 : Blo 944585 1419179 := bstep (se 1 (by rfl) ⟨1064384, by rfl⟩ : syracuseStep 1419179 = 2128769) B2128769
theorem B1419209 : Blo 944585 1419209 := bstep (se 2 (by rfl) ⟨532203, by rfl⟩ : syracuseStep 1419209 = 1064407) B1064407
theorem B1419323 : Blo 944585 1419323 := bstep (se 1 (by rfl) ⟨1064492, by rfl⟩ : syracuseStep 1419323 = 2128985) B2128985
theorem B1419383 : Blo 944585 1419383 := bstep (se 1 (by rfl) ⟨1064537, by rfl⟩ : syracuseStep 1419383 = 2129075) B2129075
theorem B1419407 : Blo 944585 1419407 := bstep (se 1 (by rfl) ⟨1064555, by rfl⟩ : syracuseStep 1419407 = 2129111) B2129111
theorem B1419449 : Blo 944585 1419449 := bstep (se 2 (by rfl) ⟨532293, by rfl⟩ : syracuseStep 1419449 = 1064587) B1064587
theorem B1419527 : Blo 944585 1419527 := bstep (se 1 (by rfl) ⟨1064645, by rfl⟩ : syracuseStep 1419527 = 2129291) B2129291
theorem B1419563 : Blo 944585 1419563 := bstep (se 1 (by rfl) ⟨1064672, by rfl⟩ : syracuseStep 1419563 = 2129345) B2129345
theorem B1419593 : Blo 944585 1419593 := bstep (se 2 (by rfl) ⟨532347, by rfl⟩ : syracuseStep 1419593 = 1064695) B1064695
theorem B4794713 : Blo 944585 4794713 := bstep (se 2 (by rfl) ⟨1798017, by rfl⟩ : syracuseStep 4794713 = 3596035) B3596035
theorem B2697619 : Blo 944585 2697619 := bstep (se 1 (by rfl) ⟨2023214, by rfl⟩ : syracuseStep 2697619 = 4046429) B4046429
theorem B1419707 : Blo 944585 1419707 := bstep (se 1 (by rfl) ⟨1064780, by rfl⟩ : syracuseStep 1419707 = 2129561) B2129561
theorem B1419767 : Blo 944585 1419767 := bstep (se 1 (by rfl) ⟨1064825, by rfl⟩ : syracuseStep 1419767 = 2129651) B2129651
theorem B1419791 : Blo 944585 1419791 := bstep (se 1 (by rfl) ⟨1064843, by rfl⟩ : syracuseStep 1419791 = 2129687) B2129687
theorem B1419833 : Blo 944585 1419833 := bstep (se 2 (by rfl) ⟨532437, by rfl⟩ : syracuseStep 1419833 = 1064875) B1064875
theorem B1419911 : Blo 944585 1419911 := bstep (se 1 (by rfl) ⟨1064933, by rfl⟩ : syracuseStep 1419911 = 2129867) B2129867
theorem B1419947 : Blo 944585 1419947 := bstep (se 1 (by rfl) ⟨1064960, by rfl⟩ : syracuseStep 1419947 = 2129921) B2129921
theorem B1419977 : Blo 944585 1419977 := bstep (se 2 (by rfl) ⟨532491, by rfl⟩ : syracuseStep 1419977 = 1064983) B1064983
theorem B2272043 : Blo 944585 2272043 := bstep (se 1 (by rfl) ⟨1704032, by rfl⟩ : syracuseStep 2272043 = 3408065) B3408065
theorem B3189563 : Blo 944585 3189563 := bstep (se 1 (by rfl) ⟨2392172, by rfl⟩ : syracuseStep 3189563 = 4784345) B4784345
theorem B1420091 : Blo 944585 1420091 := bstep (se 1 (by rfl) ⟨1065068, by rfl⟩ : syracuseStep 1420091 = 2130137) B2130137
theorem B1420151 : Blo 944585 1420151 := bstep (se 1 (by rfl) ⟨1065113, by rfl⟩ : syracuseStep 1420151 = 2130227) B2130227
theorem B1420175 : Blo 944585 1420175 := bstep (se 1 (by rfl) ⟨1065131, by rfl⟩ : syracuseStep 1420175 = 2130263) B2130263
theorem B1846201 : Blo 944585 1846201 := bstep (se 2 (by rfl) ⟨692325, by rfl⟩ : syracuseStep 1846201 = 1384651) B1384651
theorem B1420217 : Blo 944585 1420217 := bstep (se 2 (by rfl) ⟨532581, by rfl⟩ : syracuseStep 1420217 = 1065163) B1065163
theorem B1420295 : Blo 944585 1420295 := bstep (se 1 (by rfl) ⟨1065221, by rfl⟩ : syracuseStep 1420295 = 2130443) B2130443
theorem B1420331 : Blo 944585 1420331 := bstep (se 1 (by rfl) ⟨1065248, by rfl⟩ : syracuseStep 1420331 = 2130497) B2130497
theorem B1420361 : Blo 944585 1420361 := bstep (se 2 (by rfl) ⟨532635, by rfl⟩ : syracuseStep 1420361 = 1065271) B1065271
theorem B1420475 : Blo 944585 1420475 := bstep (se 1 (by rfl) ⟨1065356, by rfl⟩ : syracuseStep 1420475 = 2130713) B2130713
theorem B1420535 : Blo 944585 1420535 := bstep (se 1 (by rfl) ⟨1065401, by rfl⟩ : syracuseStep 1420535 = 2130803) B2130803
theorem B5385487 : Blo 944585 5385487 := bstep (se 1 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 5385487 = 8078231) B8078231
theorem B1420559 : Blo 944585 1420559 := bstep (se 1 (by rfl) ⟨1065419, by rfl⟩ : syracuseStep 1420559 = 2130839) B2130839
theorem B3190049 : Blo 944585 3190049 := bstep (se 2 (by rfl) ⟨1196268, by rfl⟩ : syracuseStep 3190049 = 2392537) B2392537
theorem B1420601 : Blo 944585 1420601 := bstep (se 2 (by rfl) ⟨532725, by rfl⟩ : syracuseStep 1420601 = 1065451) B1065451
theorem B3648827 : Blo 944585 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B1420679 : Blo 944585 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B1420715 : Blo 944585 1420715 := bstep (se 1 (by rfl) ⟨1065536, by rfl⟩ : syracuseStep 1420715 = 2131073) B2131073
theorem B1420745 : Blo 944585 1420745 := bstep (se 2 (by rfl) ⟨532779, by rfl⟩ : syracuseStep 1420745 = 1065559) B1065559
theorem B14757329 : Blo 944585 14757329 := bstep (se 2 (by rfl) ⟨5533998, by rfl⟩ : syracuseStep 14757329 = 11067997) B11067997
theorem B1420859 : Blo 944585 1420859 := bstep (se 1 (by rfl) ⟨1065644, by rfl⟩ : syracuseStep 1420859 = 2131289) B2131289
theorem B1420919 : Blo 944585 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B1420943 : Blo 944585 1420943 := bstep (se 1 (by rfl) ⟨1065707, by rfl⟩ : syracuseStep 1420943 = 2131415) B2131415
theorem B1420985 : Blo 944585 1420985 := bstep (se 2 (by rfl) ⟨532869, by rfl⟩ : syracuseStep 1420985 = 1065739) B1065739
theorem B1421063 : Blo 944585 1421063 := bstep (se 1 (by rfl) ⟨1065797, by rfl⟩ : syracuseStep 1421063 = 2131595) B2131595
theorem B1421099 : Blo 944585 1421099 := bstep (se 1 (by rfl) ⟨1065824, by rfl⟩ : syracuseStep 1421099 = 2131649) B2131649
theorem B1421129 : Blo 944585 1421129 := bstep (se 2 (by rfl) ⟨532923, by rfl⟩ : syracuseStep 1421129 = 1065847) B1065847
theorem B3190643 : Blo 944585 3190643 := bstep (se 1 (by rfl) ⟨2392982, by rfl⟩ : syracuseStep 3190643 = 4785965) B4785965
theorem B2273177 : Blo 944585 2273177 := bstep (se 2 (by rfl) ⟨852441, by rfl⟩ : syracuseStep 2273177 = 1704883) B1704883
theorem B1421243 : Blo 944585 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B7679947 : Blo 944585 7679947 := bstep (se 1 (by rfl) ⟨5759960, by rfl⟩ : syracuseStep 7679947 = 11519921) B11519921
theorem B1421303 : Blo 944585 1421303 := bstep (se 1 (by rfl) ⟨1065977, by rfl⟩ : syracuseStep 1421303 = 2131955) B2131955
theorem B1421327 : Blo 944585 1421327 := bstep (se 1 (by rfl) ⟨1065995, by rfl⟩ : syracuseStep 1421327 = 2131991) B2131991
theorem B20492311 : Blo 944585 20492311 := bstep (se 1 (by rfl) ⟨15369233, by rfl⟩ : syracuseStep 20492311 = 30738467) B30738467
theorem B1421369 : Blo 944585 1421369 := bstep (se 2 (by rfl) ⟨533013, by rfl⟩ : syracuseStep 1421369 = 1066027) B1066027
theorem B2699351 : Blo 944585 2699351 := bstep (se 1 (by rfl) ⟨2024513, by rfl⟩ : syracuseStep 2699351 = 4049027) B4049027
theorem B1421447 : Blo 944585 1421447 := bstep (se 1 (by rfl) ⟨1066085, by rfl⟩ : syracuseStep 1421447 = 2132171) B2132171
theorem B1421483 : Blo 944585 1421483 := bstep (se 1 (by rfl) ⟨1066112, by rfl⟩ : syracuseStep 1421483 = 2132225) B2132225
theorem B1421513 : Blo 944585 1421513 := bstep (se 2 (by rfl) ⟨533067, by rfl⟩ : syracuseStep 1421513 = 1066135) B1066135
theorem B1421627 : Blo 944585 1421627 := bstep (se 1 (by rfl) ⟨1066220, by rfl⟩ : syracuseStep 1421627 = 2132441) B2132441
theorem B1421687 : Blo 944585 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B1421711 : Blo 944585 1421711 := bstep (se 1 (by rfl) ⟨1066283, by rfl⟩ : syracuseStep 1421711 = 2132567) B2132567
theorem B4796819 : Blo 944585 4796819 := bstep (se 1 (by rfl) ⟨3597614, by rfl⟩ : syracuseStep 4796819 = 7195229) B7195229
theorem B1421753 : Blo 944585 1421753 := bstep (se 2 (by rfl) ⟨533157, by rfl⟩ : syracuseStep 1421753 = 1066315) B1066315
theorem B1421831 : Blo 944585 1421831 := bstep (se 1 (by rfl) ⟨1066373, by rfl⟩ : syracuseStep 1421831 = 2132747) B2132747
theorem B5386763 : Blo 944585 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B1421867 : Blo 944585 1421867 := bstep (se 1 (by rfl) ⟨1066400, by rfl⟩ : syracuseStep 1421867 = 2132801) B2132801
theorem B1421897 : Blo 944585 1421897 := bstep (se 2 (by rfl) ⟨533211, by rfl⟩ : syracuseStep 1421897 = 1066423) B1066423
theorem B10793573 : Blo 944585 10793573 := bstep (se 4 (by rfl) ⟨1011897, by rfl⟩ : syracuseStep 10793573 = 2023795) B2023795
theorem B1422011 : Blo 944585 1422011 := bstep (se 1 (by rfl) ⟨1066508, by rfl⟩ : syracuseStep 1422011 = 2133017) B2133017
theorem B5386945 : Blo 944585 5386945 := bstep (se 2 (by rfl) ⟨2020104, by rfl⟩ : syracuseStep 5386945 = 4040209) B4040209
theorem B1422071 : Blo 944585 1422071 := bstep (se 1 (by rfl) ⟨1066553, by rfl⟩ : syracuseStep 1422071 = 2133107) B2133107
theorem B1422095 : Blo 944585 1422095 := bstep (se 1 (by rfl) ⟨1066571, by rfl⟩ : syracuseStep 1422095 = 2133143) B2133143
theorem B1422137 : Blo 944585 1422137 := bstep (se 2 (by rfl) ⟨533301, by rfl⟩ : syracuseStep 1422137 = 1066603) B1066603
theorem B7189337 : Blo 944585 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B1422215 : Blo 944585 1422215 := bstep (se 1 (by rfl) ⟨1066661, by rfl⟩ : syracuseStep 1422215 = 2133323) B2133323
theorem B1422251 : Blo 944585 1422251 := bstep (se 1 (by rfl) ⟨1066688, by rfl⟩ : syracuseStep 1422251 = 2133377) B2133377
theorem B1422281 : Blo 944585 1422281 := bstep (se 2 (by rfl) ⟨533355, by rfl⟩ : syracuseStep 1422281 = 1066711) B1066711
theorem B5321771 : Blo 944585 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B1422395 : Blo 944585 1422395 := bstep (se 1 (by rfl) ⟨1066796, by rfl⟩ : syracuseStep 1422395 = 2133593) B2133593
theorem B1422455 : Blo 944585 1422455 := bstep (se 1 (by rfl) ⟨1066841, by rfl⟩ : syracuseStep 1422455 = 2133683) B2133683
theorem B1422479 : Blo 944585 1422479 := bstep (se 1 (by rfl) ⟨1066859, by rfl⟩ : syracuseStep 1422479 = 2133719) B2133719
theorem B1422521 : Blo 944585 1422521 := bstep (se 2 (by rfl) ⟨533445, by rfl⟩ : syracuseStep 1422521 = 1066891) B1066891
theorem B1422599 : Blo 944585 1422599 := bstep (se 1 (by rfl) ⟨1066949, by rfl⟩ : syracuseStep 1422599 = 2133899) B2133899
theorem B1422635 : Blo 944585 1422635 := bstep (se 1 (by rfl) ⟨1066976, by rfl⟩ : syracuseStep 1422635 = 2133953) B2133953
theorem B1422665 : Blo 944585 1422665 := bstep (se 2 (by rfl) ⟨533499, by rfl⟩ : syracuseStep 1422665 = 1066999) B1066999
theorem B2274695 : Blo 944585 2274695 := bstep (se 1 (by rfl) ⟨1706021, by rfl⟩ : syracuseStep 2274695 = 3412043) B3412043
theorem B1422779 : Blo 944585 1422779 := bstep (se 1 (by rfl) ⟨1067084, by rfl⟩ : syracuseStep 1422779 = 2134169) B2134169
theorem B1422839 : Blo 944585 1422839 := bstep (se 1 (by rfl) ⟨1067129, by rfl⟩ : syracuseStep 1422839 = 2134259) B2134259
theorem B1422863 : Blo 944585 1422863 := bstep (se 1 (by rfl) ⟨1067147, by rfl⟩ : syracuseStep 1422863 = 2134295) B2134295
theorem B2700935 : Blo 944585 2700935 := bstep (se 1 (by rfl) ⟨2025701, by rfl⟩ : syracuseStep 2700935 = 4051403) B4051403
theorem B1062715 : Blo 944585 1062715 := bstep (se 1 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 1062715 = 1594073) B1594073
theorem B10795031 : Blo 944585 10795031 := bstep (se 1 (by rfl) ⟨8096273, by rfl⟩ : syracuseStep 10795031 = 16192547) B16192547
theorem B12957941 : Blo 944585 12957941 := bstep (se 5 (by rfl) ⟨607403, by rfl⟩ : syracuseStep 12957941 = 1214807) B1214807
theorem B1063183 : Blo 944585 1063183 := bstep (se 1 (by rfl) ⟨797387, by rfl⟩ : syracuseStep 1063183 = 1594775) B1594775
theorem B3193235 : Blo 944585 3193235 := bstep (se 1 (by rfl) ⟨2394926, by rfl⟩ : syracuseStep 3193235 = 4789853) B4789853
theorem B3586589 : Blo 944585 3586589 := bstep (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) B1344971
theorem B5126885 : Blo 944585 5126885 := bstep (se 4 (by rfl) ⟨480645, by rfl⟩ : syracuseStep 5126885 = 961291) B961291
theorem B1063687 : Blo 944585 1063687 := bstep (se 1 (by rfl) ⟨797765, by rfl⟩ : syracuseStep 1063687 = 1595531) B1595531
theorem B1063867 : Blo 944585 1063867 := bstep (se 1 (by rfl) ⟨797900, by rfl⟩ : syracuseStep 1063867 = 1595801) B1595801
theorem B3587273 : Blo 944585 3587273 := bstep (se 2 (by rfl) ⟨1345227, by rfl⟩ : syracuseStep 3587273 = 2690455) B2690455
theorem B1064335 : Blo 944585 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B4799897 : Blo 944585 4799897 := bstep (se 2 (by rfl) ⟨1799961, by rfl⟩ : syracuseStep 4799897 = 3599923) B3599923
theorem B12303875 : Blo 944585 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B472858165 : Blo 944585 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B3194639 : Blo 944585 3194639 := bstep (se 1 (by rfl) ⟨2395979, by rfl⟩ : syracuseStep 3194639 = 4791959) B4791959
theorem B1064839 : Blo 944585 1064839 := bstep (se 1 (by rfl) ⟨798629, by rfl⟩ : syracuseStep 1064839 = 1597259) B1597259
theorem B20234137 : Blo 944585 20234137 := bstep (se 2 (by rfl) ⟨7587801, by rfl⟩ : syracuseStep 20234137 = 15175603) B15175603
theorem B3194909 : Blo 944585 3194909 := bstep (se 3 (by rfl) ⟨599045, by rfl⟩ : syracuseStep 3194909 = 1198091) B1198091
theorem B1065019 : Blo 944585 1065019 := bstep (se 1 (by rfl) ⟨798764, by rfl⟩ : syracuseStep 1065019 = 1597529) B1597529
theorem B1196203 : Blo 944585 1196203 := bstep (se 1 (by rfl) ⟨897152, by rfl⟩ : syracuseStep 1196203 = 1794305) B1794305
theorem B1065487 : Blo 944585 1065487 := bstep (se 1 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 1065487 = 1598231) B1598231
theorem B20497157 : Blo 944585 20497157 := bstep (se 4 (by rfl) ⟨1921608, by rfl⟩ : syracuseStep 20497157 = 3843217) B3843217
theorem B5391137 : Blo 944585 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B8209201 : Blo 944585 8209201 := bstep (se 2 (by rfl) ⟨3078450, by rfl⟩ : syracuseStep 8209201 = 6156901) B6156901
theorem B3589049 : Blo 944585 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1065991 : Blo 944585 1065991 := bstep (se 1 (by rfl) ⟨799493, by rfl⟩ : syracuseStep 1065991 = 1598987) B1598987
theorem B3032093 : Blo 944585 3032093 := bstep (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) B1137035
theorem B1197175 : Blo 944585 1197175 := bstep (se 1 (by rfl) ⟨897881, by rfl⟩ : syracuseStep 1197175 = 1795763) B1795763
theorem B1066171 : Blo 944585 1066171 := bstep (se 1 (by rfl) ⟨799628, by rfl⟩ : syracuseStep 1066171 = 1599257) B1599257
theorem B3196313 : Blo 944585 3196313 := bstep (se 2 (by rfl) ⟨1198617, by rfl⟩ : syracuseStep 3196313 = 2397235) B2397235
theorem B1197499 : Blo 944585 1197499 := bstep (se 1 (by rfl) ⟨898124, by rfl⟩ : syracuseStep 1197499 = 1796249) B1796249
theorem B1066639 : Blo 944585 1066639 := bstep (se 1 (by rfl) ⟨799979, by rfl⟩ : syracuseStep 1066639 = 1599959) B1599959
theorem B6145807 : Blo 944585 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B4048957 : Blo 944585 4048957 := bstep (se 3 (by rfl) ⟨759179, by rfl⟩ : syracuseStep 4048957 = 1518359) B1518359
theorem B3197015 : Blo 944585 3197015 := bstep (se 1 (by rfl) ⟨2397761, by rfl⟩ : syracuseStep 3197015 = 4795523) B4795523
theorem B1067143 : Blo 944585 1067143 := bstep (se 1 (by rfl) ⟨800357, by rfl⟩ : syracuseStep 1067143 = 1600715) B1600715
theorem B1820819 : Blo 944585 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B1919161 : Blo 944585 1919161 := bstep (se 2 (by rfl) ⟨719685, by rfl⟩ : syracuseStep 1919161 = 1439371) B1439371
theorem B8636705 : Blo 944585 8636705 := bstep (se 2 (by rfl) ⟨3238764, by rfl⟩ : syracuseStep 8636705 = 6477529) B6477529
theorem B8735035 : Blo 944585 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B1198471 : Blo 944585 1198471 := bstep (se 1 (by rfl) ⟨898853, by rfl⟩ : syracuseStep 1198471 = 1797707) B1797707
theorem B4540931 : Blo 944585 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B3197501 : Blo 944585 3197501 := bstep (se 3 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 3197501 = 1199063) B1199063
theorem B23382593 : Blo 944585 23382593 := bstep (se 2 (by rfl) ⟨8768472, by rfl⟩ : syracuseStep 23382593 = 17536945) B17536945
theorem B1460983 : Blo 944585 1460983 := bstep (se 1 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 1460983 = 2191475) B2191475
theorem B1198891 : Blo 944585 1198891 := bstep (se 1 (by rfl) ⟨899168, by rfl⟩ : syracuseStep 1198891 = 1798337) B1798337
theorem B1199119 : Blo 944585 1199119 := bstep (se 1 (by rfl) ⟨899339, by rfl⟩ : syracuseStep 1199119 = 1798679) B1798679
theorem B15355169 : Blo 944585 15355169 := bstep (se 2 (by rfl) ⟨5758188, by rfl⟩ : syracuseStep 15355169 = 11516377) B11516377
theorem B4050461 : Blo 944585 4050461 := bstep (se 3 (by rfl) ⟨759461, by rfl⟩ : syracuseStep 4050461 = 1518923) B1518923
theorem B2051617 : Blo 944585 2051617 := bstep (se 2 (by rfl) ⟨769356, by rfl⟩ : syracuseStep 2051617 = 1538713) B1538713
theorem B2018935 : Blo 944585 2018935 := bstep (se 1 (by rfl) ⟨1514201, by rfl⟩ : syracuseStep 2018935 = 3028403) B3028403
theorem B1199863 : Blo 944585 1199863 := bstep (se 1 (by rfl) ⟨899897, by rfl⟩ : syracuseStep 1199863 = 1799795) B1799795
theorem B5394235 : Blo 944585 5394235 := bstep (se 1 (by rfl) ⟨4045676, by rfl⟩ : syracuseStep 5394235 = 8091353) B8091353
theorem B4050803 : Blo 944585 4050803 := bstep (se 1 (by rfl) ⟨3038102, by rfl⟩ : syracuseStep 4050803 = 6076205) B6076205
theorem B3198905 : Blo 944585 3198905 := bstep (se 2 (by rfl) ⟨1199589, by rfl⟩ : syracuseStep 3198905 = 2399179) B2399179
theorem B16175051 : Blo 944585 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B1200187 : Blo 944585 1200187 := bstep (se 1 (by rfl) ⟨900140, by rfl⟩ : syracuseStep 1200187 = 1800281) B1800281
theorem B5197891 : Blo 944585 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B5460239 : Blo 944585 5460239 := bstep (se 1 (by rfl) ⟨4095179, by rfl⟩ : syracuseStep 5460239 = 8190359) B8190359
theorem B1134983 : Blo 944585 1134983 := bstep (se 1 (by rfl) ⟨851237, by rfl⟩ : syracuseStep 1134983 = 1702475) B1702475
theorem B10768787 : Blo 944585 10768787 := bstep (se 1 (by rfl) ⟨8076590, by rfl⟩ : syracuseStep 10768787 = 16153181) B16153181
theorem B3592633 : Blo 944585 3592633 := bstep (se 2 (by rfl) ⟨1347237, by rfl⟩ : syracuseStep 3592633 = 2694475) B2694475
theorem B3199499 : Blo 944585 3199499 := bstep (se 1 (by rfl) ⟨2399624, by rfl⟩ : syracuseStep 3199499 = 4799249) B4799249
theorem B3199607 : Blo 944585 3199607 := bstep (se 1 (by rfl) ⟨2399705, by rfl⟩ : syracuseStep 3199607 = 4799411) B4799411
theorem B1135291 : Blo 944585 1135291 := bstep (se 1 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 1135291 = 1702937) B1702937
theorem B1594127 : Blo 944585 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B4051727 : Blo 944585 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B8082605 : Blo 944585 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B3200201 : Blo 944585 3200201 := bstep (se 2 (by rfl) ⟨1200075, by rfl⟩ : syracuseStep 3200201 = 2400151) B2400151
theorem B5395693 : Blo 944585 5395693 := bstep (se 3 (by rfl) ⟨1011692, by rfl⟩ : syracuseStep 5395693 = 2023385) B2023385
theorem B1594667 : Blo 944585 1594667 := bstep (se 1 (by rfl) ⟨1196000, by rfl⟩ : syracuseStep 1594667 = 2392001) B2392001
theorem B12146051 : Blo 944585 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B15324551 : Blo 944585 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B25876037 : Blo 944585 25876037 := bstep (se 4 (by rfl) ⟨2425878, by rfl⟩ : syracuseStep 25876037 = 4851757) B4851757
theorem B10245811 : Blo 944585 10245811 := bstep (se 1 (by rfl) ⟨7684358, by rfl⟩ : syracuseStep 10245811 = 15368717) B15368717
theorem B1595065 : Blo 944585 1595065 := bstep (se 2 (by rfl) ⟨598149, by rfl⟩ : syracuseStep 1595065 = 1196299) B1196299
theorem B4544237 : Blo 944585 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B3200903 : Blo 944585 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B2021267 : Blo 944585 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3201281 : Blo 944585 3201281 := bstep (se 2 (by rfl) ⟨1200480, by rfl⟩ : syracuseStep 3201281 = 2400961) B2400961
theorem B1595767 : Blo 944585 1595767 := bstep (se 1 (by rfl) ⟨1196825, by rfl⟩ : syracuseStep 1595767 = 2393651) B2393651
theorem B1595963 : Blo 944585 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B10803779 : Blo 944585 10803779 := bstep (se 1 (by rfl) ⟨8102834, by rfl⟩ : syracuseStep 10803779 = 16205669) B16205669
theorem B6478643 : Blo 944585 6478643 := bstep (se 1 (by rfl) ⟨4858982, by rfl⟩ : syracuseStep 6478643 = 9717965) B9717965
theorem B7199603 : Blo 944585 7199603 := bstep (se 1 (by rfl) ⟨5399702, by rfl⟩ : syracuseStep 7199603 = 10799405) B10799405
theorem B1596361 : Blo 944585 1596361 := bstep (se 2 (by rfl) ⟨598635, by rfl⟩ : syracuseStep 1596361 = 1197271) B1197271
theorem B1137655 : Blo 944585 1137655 := bstep (se 1 (by rfl) ⟨853241, by rfl⟩ : syracuseStep 1137655 = 1706483) B1706483
theorem B5397677 : Blo 944585 5397677 := bstep (se 3 (by rfl) ⟨1012064, by rfl⟩ : syracuseStep 5397677 = 2024129) B2024129
theorem B3595535 : Blo 944585 3595535 := bstep (se 1 (by rfl) ⟨2696651, by rfl⟩ : syracuseStep 3595535 = 5393303) B5393303
theorem B98557397 : Blo 944585 98557397 := bstep (se 7 (by rfl) ⟨1154969, by rfl⟩ : syracuseStep 98557397 = 2309939) B2309939
theorem B1597063 : Blo 944585 1597063 := bstep (se 1 (by rfl) ⟨1197797, by rfl⟩ : syracuseStep 1597063 = 2395595) B2395595
theorem B6054061 : Blo 944585 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B2023625 : Blo 944585 2023625 := bstep (se 2 (by rfl) ⟨758859, by rfl⟩ : syracuseStep 2023625 = 1517719) B1517719
theorem B1597711 : Blo 944585 1597711 := bstep (se 1 (by rfl) ⟨1198283, by rfl⟩ : syracuseStep 1597711 = 2396567) B2396567
theorem B1794707 : Blo 944585 1794707 := bstep (se 1 (by rfl) ⟨1346030, by rfl⟩ : syracuseStep 1794707 = 2692061) B2692061
theorem B2024137 : Blo 944585 2024137 := bstep (se 2 (by rfl) ⟨759051, by rfl⟩ : syracuseStep 2024137 = 1518103) B1518103
theorem B1598251 : Blo 944585 1598251 := bstep (se 1 (by rfl) ⟨1198688, by rfl⟩ : syracuseStep 1598251 = 2397377) B2397377
theorem B1794935 : Blo 944585 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B1598393 : Blo 944585 1598393 := bstep (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) B1198795
theorem B6153239 : Blo 944585 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B23061635 : Blo 944585 23061635 := bstep (se 1 (by rfl) ⟨17296226, by rfl⟩ : syracuseStep 23061635 = 34592453) B34592453
theorem B2876563 : Blo 944585 2876563 := bstep (se 1 (by rfl) ⟨2157422, by rfl⟩ : syracuseStep 2876563 = 4314845) B4314845
theorem B5400067 : Blo 944585 5400067 := bstep (se 1 (by rfl) ⟨4050050, by rfl⟩ : syracuseStep 5400067 = 8100101) B8100101
theorem B2024975 : Blo 944585 2024975 := bstep (se 1 (by rfl) ⟨1518731, by rfl⟩ : syracuseStep 2024975 = 3037463) B3037463
theorem B1599095 : Blo 944585 1599095 := bstep (se 1 (by rfl) ⟨1199321, by rfl⟩ : syracuseStep 1599095 = 2398643) B2398643
theorem B4318991 : Blo 944585 4318991 := bstep (se 1 (by rfl) ⟨3239243, by rfl⟩ : syracuseStep 4318991 = 6478487) B6478487
theorem B20441105 : Blo 944585 20441105 := bstep (se 2 (by rfl) ⟨7665414, by rfl⟩ : syracuseStep 20441105 = 15330829) B15330829
theorem B1599547 : Blo 944585 1599547 := bstep (se 1 (by rfl) ⟨1199660, by rfl⟩ : syracuseStep 1599547 = 2399321) B2399321
theorem B2025607 : Blo 944585 2025607 := bstep (se 1 (by rfl) ⟨1519205, by rfl⟩ : syracuseStep 2025607 = 3038411) B3038411
theorem B1599689 : Blo 944585 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B3598739 : Blo 944585 3598739 := bstep (se 1 (by rfl) ⟨2699054, by rfl⟩ : syracuseStep 3598739 = 5398109) B5398109
theorem B944647 : Blo 944585 944647 := bstep (se 1 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 944647 = 1416971) B1416971
theorem B944655 : Blo 944585 944655 := bstep (se 1 (by rfl) ⟨708491, by rfl⟩ : syracuseStep 944655 = 1416983) B1416983
theorem B7662109 : Blo 944585 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B1796651 : Blo 944585 1796651 := bstep (se 1 (by rfl) ⟨1347488, by rfl⟩ : syracuseStep 1796651 = 2694977) B2694977
theorem B944699 : Blo 944585 944699 := bstep (se 1 (by rfl) ⟨708524, by rfl⟩ : syracuseStep 944699 = 1417049) B1417049
theorem B944775 : Blo 944585 944775 := bstep (se 1 (by rfl) ⟨708581, by rfl⟩ : syracuseStep 944775 = 1417163) B1417163
theorem B944783 : Blo 944585 944783 := bstep (se 1 (by rfl) ⟨708587, by rfl⟩ : syracuseStep 944783 = 1417175) B1417175
theorem B944827 : Blo 944585 944827 := bstep (se 1 (by rfl) ⟨708620, by rfl⟩ : syracuseStep 944827 = 1417241) B1417241
theorem B944903 : Blo 944585 944903 := bstep (se 1 (by rfl) ⟨708677, by rfl⟩ : syracuseStep 944903 = 1417355) B1417355
theorem B944911 : Blo 944585 944911 := bstep (se 1 (by rfl) ⟨708683, by rfl⟩ : syracuseStep 944911 = 1417367) B1417367
theorem B1796879 : Blo 944585 1796879 := bstep (se 1 (by rfl) ⟨1347659, by rfl⟩ : syracuseStep 1796879 = 2695319) B2695319
theorem B944955 : Blo 944585 944955 := bstep (se 1 (by rfl) ⟨708716, by rfl⟩ : syracuseStep 944955 = 1417433) B1417433
theorem B945031 : Blo 944585 945031 := bstep (se 1 (by rfl) ⟨708773, by rfl⟩ : syracuseStep 945031 = 1417547) B1417547
theorem B1600391 : Blo 944585 1600391 := bstep (se 1 (by rfl) ⟨1200293, by rfl⟩ : syracuseStep 1600391 = 2400587) B2400587
theorem B945039 : Blo 944585 945039 := bstep (se 1 (by rfl) ⟨708779, by rfl⟩ : syracuseStep 945039 = 1417559) B1417559
theorem B945083 : Blo 944585 945083 := bstep (se 1 (by rfl) ⟨708812, by rfl⟩ : syracuseStep 945083 = 1417625) B1417625
theorem B945159 : Blo 944585 945159 := bstep (se 1 (by rfl) ⟨708869, by rfl⟩ : syracuseStep 945159 = 1417739) B1417739
theorem B945167 : Blo 944585 945167 := bstep (se 1 (by rfl) ⟨708875, by rfl⟩ : syracuseStep 945167 = 1417751) B1417751
theorem B945211 : Blo 944585 945211 := bstep (se 1 (by rfl) ⟨708908, by rfl⟩ : syracuseStep 945211 = 1417817) B1417817
theorem B945287 : Blo 944585 945287 := bstep (se 1 (by rfl) ⟨708965, by rfl⟩ : syracuseStep 945287 = 1417931) B1417931
theorem B945295 : Blo 944585 945295 := bstep (se 1 (by rfl) ⟨708971, by rfl⟩ : syracuseStep 945295 = 1417943) B1417943
theorem B945339 : Blo 944585 945339 := bstep (se 1 (by rfl) ⟨709004, by rfl⟩ : syracuseStep 945339 = 1418009) B1418009
theorem B945415 : Blo 944585 945415 := bstep (se 1 (by rfl) ⟨709061, by rfl⟩ : syracuseStep 945415 = 1418123) B1418123
theorem B945423 : Blo 944585 945423 := bstep (se 1 (by rfl) ⟨709067, by rfl⟩ : syracuseStep 945423 = 1418135) B1418135
theorem B945467 : Blo 944585 945467 := bstep (se 1 (by rfl) ⟨709100, by rfl⟩ : syracuseStep 945467 = 1418201) B1418201
theorem B19426661 : Blo 944585 19426661 := bstep (se 4 (by rfl) ⟨1821249, by rfl⟩ : syracuseStep 19426661 = 3642499) B3642499
theorem B4550003 : Blo 944585 4550003 := bstep (se 1 (by rfl) ⟨3412502, by rfl⟩ : syracuseStep 4550003 = 6825005) B6825005
theorem B945543 : Blo 944585 945543 := bstep (se 1 (by rfl) ⟨709157, by rfl⟩ : syracuseStep 945543 = 1418315) B1418315
theorem B945551 : Blo 944585 945551 := bstep (se 1 (by rfl) ⟨709163, by rfl⟩ : syracuseStep 945551 = 1418327) B1418327
theorem B945595 : Blo 944585 945595 := bstep (se 1 (by rfl) ⟨709196, by rfl⟩ : syracuseStep 945595 = 1418393) B1418393
theorem B37842385 : Blo 944585 37842385 := bstep (se 2 (by rfl) ⟨14190894, by rfl⟩ : syracuseStep 37842385 = 28381789) B28381789
theorem B945671 : Blo 944585 945671 := bstep (se 1 (by rfl) ⟨709253, by rfl⟩ : syracuseStep 945671 = 1418507) B1418507
theorem B945679 : Blo 944585 945679 := bstep (se 1 (by rfl) ⟨709259, by rfl⟩ : syracuseStep 945679 = 1418519) B1418519
theorem B945723 : Blo 944585 945723 := bstep (se 1 (by rfl) ⟨709292, by rfl⟩ : syracuseStep 945723 = 1418585) B1418585
theorem B5107319 : Blo 944585 5107319 := bstep (se 1 (by rfl) ⟨3830489, by rfl⟩ : syracuseStep 5107319 = 7660979) B7660979
theorem B945799 : Blo 944585 945799 := bstep (se 1 (by rfl) ⟨709349, by rfl⟩ : syracuseStep 945799 = 1418699) B1418699
theorem B945807 : Blo 944585 945807 := bstep (se 1 (by rfl) ⟨709355, by rfl⟩ : syracuseStep 945807 = 1418711) B1418711
theorem B5828269 : Blo 944585 5828269 := bstep (se 3 (by rfl) ⟨1092800, by rfl⟩ : syracuseStep 5828269 = 2185601) B2185601
theorem B945851 : Blo 944585 945851 := bstep (se 1 (by rfl) ⟨709388, by rfl⟩ : syracuseStep 945851 = 1418777) B1418777
theorem B945927 : Blo 944585 945927 := bstep (se 1 (by rfl) ⟨709445, by rfl⟩ : syracuseStep 945927 = 1418891) B1418891
theorem B2125583 : Blo 944585 2125583 := bstep (se 1 (by rfl) ⟨1594187, by rfl⟩ : syracuseStep 2125583 = 3188375) B3188375
theorem B945935 : Blo 944585 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B2125601 : Blo 944585 2125601 := bstep (se 2 (by rfl) ⟨797100, by rfl⟩ : syracuseStep 2125601 = 1594201) B1594201
theorem B945979 : Blo 944585 945979 := bstep (se 1 (by rfl) ⟨709484, by rfl⟩ : syracuseStep 945979 = 1418969) B1418969
theorem B5402483 : Blo 944585 5402483 := bstep (se 1 (by rfl) ⟨4051862, by rfl⟩ : syracuseStep 5402483 = 8103725) B8103725
theorem B946055 : Blo 944585 946055 := bstep (se 1 (by rfl) ⟨709541, by rfl⟩ : syracuseStep 946055 = 1419083) B1419083
theorem B946063 : Blo 944585 946063 := bstep (se 1 (by rfl) ⟨709547, by rfl⟩ : syracuseStep 946063 = 1419095) B1419095
theorem B946107 : Blo 944585 946107 := bstep (se 1 (by rfl) ⟨709580, by rfl⟩ : syracuseStep 946107 = 1419161) B1419161
theorem B946183 : Blo 944585 946183 := bstep (se 1 (by rfl) ⟨709637, by rfl⟩ : syracuseStep 946183 = 1419275) B1419275
theorem B3600395 : Blo 944585 3600395 := bstep (se 1 (by rfl) ⟨2700296, by rfl⟩ : syracuseStep 3600395 = 5400593) B5400593
theorem B946191 : Blo 944585 946191 := bstep (se 1 (by rfl) ⟨709643, by rfl⟩ : syracuseStep 946191 = 1419287) B1419287
theorem B1011727 : Blo 944585 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B946235 : Blo 944585 946235 := bstep (se 1 (by rfl) ⟨709676, by rfl⟩ : syracuseStep 946235 = 1419353) B1419353
theorem B2125943 : Blo 944585 2125943 := bstep (se 1 (by rfl) ⟨1594457, by rfl⟩ : syracuseStep 2125943 = 3188915) B3188915
theorem B946311 : Blo 944585 946311 := bstep (se 1 (by rfl) ⟨709733, by rfl⟩ : syracuseStep 946311 = 1419467) B1419467
theorem B946319 : Blo 944585 946319 := bstep (se 1 (by rfl) ⟨709739, by rfl⟩ : syracuseStep 946319 = 1419479) B1419479
theorem B1798291 : Blo 944585 1798291 := bstep (se 1 (by rfl) ⟨1348718, by rfl⟩ : syracuseStep 1798291 = 2697437) B2697437
theorem B946363 : Blo 944585 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B946439 : Blo 944585 946439 := bstep (se 1 (by rfl) ⟨709829, by rfl⟩ : syracuseStep 946439 = 1419659) B1419659
theorem B946447 : Blo 944585 946447 := bstep (se 1 (by rfl) ⟨709835, by rfl⟩ : syracuseStep 946447 = 1419671) B1419671
theorem B2126123 : Blo 944585 2126123 := bstep (se 1 (by rfl) ⟨1594592, by rfl⟩ : syracuseStep 2126123 = 3189185) B3189185
theorem B946491 : Blo 944585 946491 := bstep (se 1 (by rfl) ⟨709868, by rfl⟩ : syracuseStep 946491 = 1419737) B1419737
theorem B1798519 : Blo 944585 1798519 := bstep (se 1 (by rfl) ⟨1348889, by rfl⟩ : syracuseStep 1798519 = 2697779) B2697779
theorem B946567 : Blo 944585 946567 := bstep (se 1 (by rfl) ⟨709925, by rfl⟩ : syracuseStep 946567 = 1419851) B1419851
theorem B946575 : Blo 944585 946575 := bstep (se 1 (by rfl) ⟨709931, by rfl⟩ : syracuseStep 946575 = 1419863) B1419863
theorem B946619 : Blo 944585 946619 := bstep (se 1 (by rfl) ⟨709964, by rfl⟩ : syracuseStep 946619 = 1419929) B1419929
theorem B946695 : Blo 944585 946695 := bstep (se 1 (by rfl) ⟨710021, by rfl⟩ : syracuseStep 946695 = 1420043) B1420043
theorem B946703 : Blo 944585 946703 := bstep (se 1 (by rfl) ⟨710027, by rfl⟩ : syracuseStep 946703 = 1420055) B1420055
theorem B946747 : Blo 944585 946747 := bstep (se 1 (by rfl) ⟨710060, by rfl⟩ : syracuseStep 946747 = 1420121) B1420121
theorem B3404375 : Blo 944585 3404375 := bstep (se 1 (by rfl) ⟨2553281, by rfl⟩ : syracuseStep 3404375 = 5106563) B5106563
theorem B946823 : Blo 944585 946823 := bstep (se 1 (by rfl) ⟨710117, by rfl⟩ : syracuseStep 946823 = 1420235) B1420235
theorem B946831 : Blo 944585 946831 := bstep (se 1 (by rfl) ⟨710123, by rfl⟩ : syracuseStep 946831 = 1420247) B1420247
theorem B2126483 : Blo 944585 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B946875 : Blo 944585 946875 := bstep (se 1 (by rfl) ⟨710156, by rfl⟩ : syracuseStep 946875 = 1420313) B1420313
theorem B2126537 : Blo 944585 2126537 := bstep (se 2 (by rfl) ⟨797451, by rfl⟩ : syracuseStep 2126537 = 1594903) B1594903
theorem B946951 : Blo 944585 946951 := bstep (se 1 (by rfl) ⟨710213, by rfl⟩ : syracuseStep 946951 = 1420427) B1420427
theorem B946959 : Blo 944585 946959 := bstep (se 1 (by rfl) ⟨710219, by rfl⟩ : syracuseStep 946959 = 1420439) B1420439
theorem B947003 : Blo 944585 947003 := bstep (se 1 (by rfl) ⟨710252, by rfl⟩ : syracuseStep 947003 = 1420505) B1420505
theorem B947079 : Blo 944585 947079 := bstep (se 1 (by rfl) ⟨710309, by rfl⟩ : syracuseStep 947079 = 1420619) B1420619
theorem B947087 : Blo 944585 947087 := bstep (se 1 (by rfl) ⟨710315, by rfl⟩ : syracuseStep 947087 = 1420631) B1420631
theorem B947131 : Blo 944585 947131 := bstep (se 1 (by rfl) ⟨710348, by rfl⟩ : syracuseStep 947131 = 1420697) B1420697
theorem B947207 : Blo 944585 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B947215 : Blo 944585 947215 := bstep (se 1 (by rfl) ⟨710411, by rfl⟩ : syracuseStep 947215 = 1420823) B1420823
theorem B947259 : Blo 944585 947259 := bstep (se 1 (by rfl) ⟨710444, by rfl⟩ : syracuseStep 947259 = 1420889) B1420889
theorem B947335 : Blo 944585 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B947343 : Blo 944585 947343 := bstep (se 1 (by rfl) ⟨710507, by rfl⟩ : syracuseStep 947343 = 1421015) B1421015
theorem B947387 : Blo 944585 947387 := bstep (se 1 (by rfl) ⟨710540, by rfl⟩ : syracuseStep 947387 = 1421081) B1421081
theorem B1438921 : Blo 944585 1438921 := bstep (se 2 (by rfl) ⟨539595, by rfl⟩ : syracuseStep 1438921 = 1079191) B1079191
theorem B947463 : Blo 944585 947463 := bstep (se 1 (by rfl) ⟨710597, by rfl⟩ : syracuseStep 947463 = 1421195) B1421195
theorem B947471 : Blo 944585 947471 := bstep (se 1 (by rfl) ⟨710603, by rfl⟩ : syracuseStep 947471 = 1421207) B1421207
theorem B947515 : Blo 944585 947515 := bstep (se 1 (by rfl) ⟨710636, by rfl⟩ : syracuseStep 947515 = 1421273) B1421273
theorem B2127239 : Blo 944585 2127239 := bstep (se 1 (by rfl) ⟨1595429, by rfl⟩ : syracuseStep 2127239 = 3190859) B3190859
theorem B947591 : Blo 944585 947591 := bstep (se 1 (by rfl) ⟨710693, by rfl⟩ : syracuseStep 947591 = 1421387) B1421387
theorem B947599 : Blo 944585 947599 := bstep (se 1 (by rfl) ⟨710699, by rfl⟩ : syracuseStep 947599 = 1421399) B1421399
theorem B947643 : Blo 944585 947643 := bstep (se 1 (by rfl) ⟨710732, by rfl⟩ : syracuseStep 947643 = 1421465) B1421465
theorem B4552139 : Blo 944585 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B4552195 : Blo 944585 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B947719 : Blo 944585 947719 := bstep (se 1 (by rfl) ⟨710789, by rfl⟩ : syracuseStep 947719 = 1421579) B1421579
theorem B947727 : Blo 944585 947727 := bstep (se 1 (by rfl) ⟨710795, by rfl⟩ : syracuseStep 947727 = 1421591) B1421591
theorem B2127419 : Blo 944585 2127419 := bstep (se 1 (by rfl) ⟨1595564, by rfl⟩ : syracuseStep 2127419 = 3191129) B3191129
theorem B947771 : Blo 944585 947771 := bstep (se 1 (by rfl) ⟨710828, by rfl⟩ : syracuseStep 947771 = 1421657) B1421657
theorem B46003787 : Blo 944585 46003787 := bstep (se 1 (by rfl) ⟨34502840, by rfl⟩ : syracuseStep 46003787 = 69005681) B69005681
theorem B947847 : Blo 944585 947847 := bstep (se 1 (by rfl) ⟨710885, by rfl⟩ : syracuseStep 947847 = 1421771) B1421771
theorem B947855 : Blo 944585 947855 := bstep (se 1 (by rfl) ⟨710891, by rfl⟩ : syracuseStep 947855 = 1421783) B1421783
theorem B2127545 : Blo 944585 2127545 := bstep (se 2 (by rfl) ⟨797829, by rfl⟩ : syracuseStep 2127545 = 1595659) B1595659
theorem B947899 : Blo 944585 947899 := bstep (se 1 (by rfl) ⟨710924, by rfl⟩ : syracuseStep 947899 = 1421849) B1421849
theorem B3405569 : Blo 944585 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B947975 : Blo 944585 947975 := bstep (se 1 (by rfl) ⟨710981, by rfl⟩ : syracuseStep 947975 = 1421963) B1421963
theorem B4552463 : Blo 944585 4552463 := bstep (se 1 (by rfl) ⟨3414347, by rfl⟩ : syracuseStep 4552463 = 6828695) B6828695
theorem B947983 : Blo 944585 947983 := bstep (se 1 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 947983 = 1421975) B1421975
theorem B948027 : Blo 944585 948027 := bstep (se 1 (by rfl) ⟨711020, by rfl⟩ : syracuseStep 948027 = 1422041) B1422041
theorem B948103 : Blo 944585 948103 := bstep (se 1 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 948103 = 1422155) B1422155
theorem B948111 : Blo 944585 948111 := bstep (se 1 (by rfl) ⟨711083, by rfl⟩ : syracuseStep 948111 = 1422167) B1422167
theorem B1800083 : Blo 944585 1800083 := bstep (se 1 (by rfl) ⟨1350062, by rfl⟩ : syracuseStep 1800083 = 2700125) B2700125
theorem B948155 : Blo 944585 948155 := bstep (se 1 (by rfl) ⟨711116, by rfl⟩ : syracuseStep 948155 = 1422233) B1422233
theorem B1800137 : Blo 944585 1800137 := bstep (se 2 (by rfl) ⟨675051, by rfl⟩ : syracuseStep 1800137 = 1350103) B1350103
theorem B948231 : Blo 944585 948231 := bstep (se 1 (by rfl) ⟨711173, by rfl⟩ : syracuseStep 948231 = 1422347) B1422347
theorem B2127887 : Blo 944585 2127887 := bstep (se 1 (by rfl) ⟨1595915, by rfl⟩ : syracuseStep 2127887 = 3191831) B3191831
theorem B948239 : Blo 944585 948239 := bstep (se 1 (by rfl) ⟨711179, by rfl⟩ : syracuseStep 948239 = 1422359) B1422359
theorem B2127905 : Blo 944585 2127905 := bstep (se 2 (by rfl) ⟨797964, by rfl⟩ : syracuseStep 2127905 = 1595929) B1595929
theorem B1800235 : Blo 944585 1800235 := bstep (se 1 (by rfl) ⟨1350176, by rfl⟩ : syracuseStep 1800235 = 2700353) B2700353
theorem B948283 : Blo 944585 948283 := bstep (se 1 (by rfl) ⟨711212, by rfl⟩ : syracuseStep 948283 = 1422425) B1422425
theorem B948359 : Blo 944585 948359 := bstep (se 1 (by rfl) ⟨711269, by rfl⟩ : syracuseStep 948359 = 1422539) B1422539
theorem B948367 : Blo 944585 948367 := bstep (se 1 (by rfl) ⟨711275, by rfl⟩ : syracuseStep 948367 = 1422551) B1422551
theorem B948411 : Blo 944585 948411 := bstep (se 1 (by rfl) ⟨711308, by rfl⟩ : syracuseStep 948411 = 1422617) B1422617
theorem B948487 : Blo 944585 948487 := bstep (se 1 (by rfl) ⟨711365, by rfl⟩ : syracuseStep 948487 = 1422731) B1422731
theorem B1800463 : Blo 944585 1800463 := bstep (se 1 (by rfl) ⟨1350347, by rfl⟩ : syracuseStep 1800463 = 2700695) B2700695
theorem B948495 : Blo 944585 948495 := bstep (se 1 (by rfl) ⟨711371, by rfl⟩ : syracuseStep 948495 = 1422743) B1422743
theorem B948539 : Blo 944585 948539 := bstep (se 1 (by rfl) ⟨711404, by rfl⟩ : syracuseStep 948539 = 1422809) B1422809
theorem B2128247 : Blo 944585 2128247 := bstep (se 1 (by rfl) ⟨1596185, by rfl⟩ : syracuseStep 2128247 = 3192371) B3192371
theorem B6912515 : Blo 944585 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B2128427 : Blo 944585 2128427 := bstep (se 1 (by rfl) ⟨1596320, by rfl⟩ : syracuseStep 2128427 = 3192641) B3192641
theorem B2161337 : Blo 944585 2161337 := bstep (se 2 (by rfl) ⟨810501, by rfl⟩ : syracuseStep 2161337 = 1621003) B1621003
theorem B4848473 : Blo 944585 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B2128787 : Blo 944585 2128787 := bstep (se 1 (by rfl) ⟨1596590, by rfl⟩ : syracuseStep 2128787 = 3193181) B3193181
theorem B2128841 : Blo 944585 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B1080463 : Blo 944585 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B2391241 : Blo 944585 2391241 := bstep (se 2 (by rfl) ⟨896715, by rfl⟩ : syracuseStep 2391241 = 1793431) B1793431
theorem B1277191 : Blo 944585 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B2391383 : Blo 944585 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B2129543 : Blo 944585 2129543 := bstep (se 1 (by rfl) ⟨1597157, by rfl⟩ : syracuseStep 2129543 = 3194315) B3194315
theorem B10780451 : Blo 944585 10780451 := bstep (se 1 (by rfl) ⟨8085338, by rfl⟩ : syracuseStep 10780451 = 16170677) B16170677
theorem B2129723 : Blo 944585 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B2129849 : Blo 944585 2129849 := bstep (se 2 (by rfl) ⟨798693, by rfl⟩ : syracuseStep 2129849 = 1597387) B1597387
theorem B1703945 : Blo 944585 1703945 := bstep (se 2 (by rfl) ⟨638979, by rfl⟩ : syracuseStep 1703945 = 1277959) B1277959
theorem B2129939 : Blo 944585 2129939 := bstep (se 1 (by rfl) ⟨1597454, by rfl⟩ : syracuseStep 2129939 = 3194909) B3194909
theorem B2130281 : Blo 944585 2130281 := bstep (se 2 (by rfl) ⟨798855, by rfl⟩ : syracuseStep 2130281 = 1597711) B1597711
theorem B5767529 : Blo 944585 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B13664771 : Blo 944585 13664771 := bstep (se 1 (by rfl) ⟨10248578, by rfl⟩ : syracuseStep 13664771 = 20497157) B20497157
theorem B3408409 : Blo 944585 3408409 := bstep (se 2 (by rfl) ⟨1278153, by rfl⟩ : syracuseStep 3408409 = 2556307) B2556307
theorem B2392699 : Blo 944585 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B2130875 : Blo 944585 2130875 := bstep (se 1 (by rfl) ⟨1598156, by rfl⟩ : syracuseStep 2130875 = 3196313) B3196313
theorem B2131001 : Blo 944585 2131001 := bstep (se 2 (by rfl) ⟨799125, by rfl⟩ : syracuseStep 2131001 = 1598251) B1598251
theorem B10945601 : Blo 944585 10945601 := bstep (se 2 (by rfl) ⟨4104600, by rfl⟩ : syracuseStep 10945601 = 8209201) B8209201
theorem B1705207 : Blo 944585 1705207 := bstep (se 1 (by rfl) ⟨1278905, by rfl⟩ : syracuseStep 1705207 = 2557811) B2557811
theorem B2131343 : Blo 944585 2131343 := bstep (se 1 (by rfl) ⟨1598507, by rfl⟩ : syracuseStep 2131343 = 3197015) B3197015
theorem B4785803 : Blo 944585 4785803 := bstep (se 1 (by rfl) ⟨3589352, by rfl⟩ : syracuseStep 4785803 = 7178705) B7178705
theorem B14419603 : Blo 944585 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B12977863 : Blo 944585 12977863 := bstep (se 1 (by rfl) ⟨9733397, by rfl⟩ : syracuseStep 12977863 = 19466795) B19466795
theorem B2131667 : Blo 944585 2131667 := bstep (se 1 (by rfl) ⟨1598750, by rfl⟩ : syracuseStep 2131667 = 3197501) B3197501
theorem B582748121 : Blo 944585 582748121 := bstep (se 2 (by rfl) ⟨218530545, by rfl⟩ : syracuseStep 582748121 = 437061091) B437061091
theorem B8194409 : Blo 944585 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B6818201 : Blo 944585 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B2132603 : Blo 944585 2132603 := bstep (se 1 (by rfl) ⟨1599452, by rfl⟩ : syracuseStep 2132603 = 3198905) B3198905
theorem B10783367 : Blo 944585 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B2132729 : Blo 944585 2132729 := bstep (se 2 (by rfl) ⟨799773, by rfl⟩ : syracuseStep 2132729 = 1599547) B1599547
theorem B3640159 : Blo 944585 3640159 := bstep (se 1 (by rfl) ⟨2730119, by rfl⟩ : syracuseStep 3640159 = 5460239) B5460239
theorem B2558881 : Blo 944585 2558881 := bstep (se 2 (by rfl) ⟨959580, by rfl⟩ : syracuseStep 2558881 = 1919161) B1919161
theorem B7179191 : Blo 944585 7179191 := bstep (se 1 (by rfl) ⟨5384393, by rfl⟩ : syracuseStep 7179191 = 10768787) B10768787
theorem B2132999 : Blo 944585 2132999 := bstep (se 1 (by rfl) ⟨1599749, by rfl⟩ : syracuseStep 2132999 = 3199499) B3199499
theorem B2133071 : Blo 944585 2133071 := bstep (se 1 (by rfl) ⟨1599803, by rfl⟩ : syracuseStep 2133071 = 3199607) B3199607
theorem B2133467 : Blo 944585 2133467 := bstep (se 1 (by rfl) ⟨1600100, by rfl⟩ : syracuseStep 2133467 = 3200201) B3200201
theorem B8097367 : Blo 944585 8097367 := bstep (se 1 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 8097367 = 12146051) B12146051
theorem B2461601 : Blo 944585 2461601 := bstep (se 2 (by rfl) ⟨923100, by rfl⟩ : syracuseStep 2461601 = 1846201) B1846201
theorem B2133935 : Blo 944585 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B1347511 : Blo 944585 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2134187 : Blo 944585 2134187 := bstep (se 1 (by rfl) ⟨1600640, by rfl⟩ : syracuseStep 2134187 = 3201281) B3201281
theorem B7180649 : Blo 944585 7180649 := bstep (se 2 (by rfl) ⟨2692743, by rfl⟩ : syracuseStep 7180649 = 5385487) B5385487
theorem B9081517 : Blo 944585 9081517 := bstep (se 3 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 9081517 = 3405569) B3405569
theorem B2691913 : Blo 944585 2691913 := bstep (se 2 (by rfl) ⟨1009467, by rfl⟩ : syracuseStep 2691913 = 2018935) B2018935
theorem B6820685 : Blo 944585 6820685 := bstep (se 3 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 6820685 = 2557757) B2557757
theorem B2397023 : Blo 944585 2397023 := bstep (se 1 (by rfl) ⟨1797767, by rfl⟩ : syracuseStep 2397023 = 3595535) B3595535
theorem B2691947 : Blo 944585 2691947 := bstep (se 1 (by rfl) ⟨2018960, by rfl⟩ : syracuseStep 2691947 = 4037921) B4037921
theorem B7771025 : Blo 944585 7771025 := bstep (se 2 (by rfl) ⟨2914134, by rfl⟩ : syracuseStep 7771025 = 5828269) B5828269
theorem B65704931 : Blo 944585 65704931 := bstep (se 1 (by rfl) ⟨49278698, by rfl⟩ : syracuseStep 65704931 = 98557397) B98557397
theorem B19928065 : Blo 944585 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B1348969 : Blo 944585 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B1349083 : Blo 944585 1349083 := bstep (se 1 (by rfl) ⟨1011812, by rfl⟩ : syracuseStep 1349083 = 2023625) B2023625
theorem B2397721 : Blo 944585 2397721 := bstep (se 2 (by rfl) ⟨899145, by rfl⟩ : syracuseStep 2397721 = 1798291) B1798291
theorem B33166945 : Blo 944585 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B4855517 : Blo 944585 4855517 := bstep (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) B1820819
theorem B4855619 : Blo 944585 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B2398025 : Blo 944585 2398025 := bstep (se 2 (by rfl) ⟨899259, by rfl⟩ : syracuseStep 2398025 = 1798519) B1798519
theorem B4790177 : Blo 944585 4790177 := bstep (se 2 (by rfl) ⟨1796316, by rfl⟩ : syracuseStep 4790177 = 3592633) B3592633
theorem B6821891 : Blo 944585 6821891 := bstep (se 1 (by rfl) ⟨5116418, by rfl⟩ : syracuseStep 6821891 = 10232837) B10232837
theorem B4102159 : Blo 944585 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B15374423 : Blo 944585 15374423 := bstep (se 1 (by rfl) ⟨11530817, by rfl⟩ : syracuseStep 15374423 = 23061635) B23061635
theorem B15341669 : Blo 944585 15341669 := bstep (se 4 (by rfl) ⟨1438281, by rfl⟩ : syracuseStep 15341669 = 2876563) B2876563
theorem B1513721 : Blo 944585 1513721 := bstep (se 2 (by rfl) ⟨567645, by rfl⟩ : syracuseStep 1513721 = 1135291) B1135291
theorem B7182593 : Blo 944585 7182593 := bstep (se 2 (by rfl) ⟨2693472, by rfl⟩ : syracuseStep 7182593 = 5386945) B5386945
theorem B1349983 : Blo 944585 1349983 := bstep (se 1 (by rfl) ⟨1012487, by rfl⟩ : syracuseStep 1349983 = 2024975) B2024975
theorem B2693519 : Blo 944585 2693519 := bstep (se 1 (by rfl) ⟨2020139, by rfl⟩ : syracuseStep 2693519 = 4040279) B4040279
theorem B5118497 : Blo 944585 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B2399159 : Blo 944585 2399159 := bstep (se 1 (by rfl) ⟨1799369, by rfl⟩ : syracuseStep 2399159 = 3598739) B3598739
theorem B1514695 : Blo 944585 1514695 := bstep (se 1 (by rfl) ⟨1136021, by rfl⟩ : syracuseStep 1514695 = 2272043) B2272043
theorem B6069593 : Blo 944585 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B12951107 : Blo 944585 12951107 := bstep (se 1 (by rfl) ⟨9713330, by rfl⟩ : syracuseStep 12951107 = 19426661) B19426661
theorem B9838219 : Blo 944585 9838219 := bstep (se 1 (by rfl) ⟨7378664, by rfl⟩ : syracuseStep 9838219 = 14757329) B14757329
theorem B1416953 : Blo 944585 1416953 := bstep (se 2 (by rfl) ⟨531357, by rfl⟩ : syracuseStep 1416953 = 1062715) B1062715
theorem B1417055 : Blo 944585 1417055 := bstep (se 1 (by rfl) ⟨1062791, by rfl⟩ : syracuseStep 1417055 = 2125583) B2125583
theorem B1417067 : Blo 944585 1417067 := bstep (se 1 (by rfl) ⟨1062800, by rfl⟩ : syracuseStep 1417067 = 2125601) B2125601
theorem B1515451 : Blo 944585 1515451 := bstep (se 1 (by rfl) ⟨1136588, by rfl⟩ : syracuseStep 1515451 = 2273177) B2273177
theorem B2400263 : Blo 944585 2400263 := bstep (se 1 (by rfl) ⟨1800197, by rfl⟩ : syracuseStep 2400263 = 3600395) B3600395
theorem B2400313 : Blo 944585 2400313 := bstep (se 2 (by rfl) ⟨900117, by rfl⟩ : syracuseStep 2400313 = 1800235) B1800235
theorem B1417295 : Blo 944585 1417295 := bstep (se 1 (by rfl) ⟨1062971, by rfl⟩ : syracuseStep 1417295 = 2125943) B2125943
theorem B1417415 : Blo 944585 1417415 := bstep (se 1 (by rfl) ⟨1063061, by rfl⟩ : syracuseStep 1417415 = 2126123) B2126123
theorem B1417577 : Blo 944585 1417577 := bstep (se 2 (by rfl) ⟨531591, by rfl⟩ : syracuseStep 1417577 = 1063183) B1063183
theorem B2400617 : Blo 944585 2400617 := bstep (se 2 (by rfl) ⟨900231, by rfl⟩ : syracuseStep 2400617 = 1800463) B1800463
theorem B2269583 : Blo 944585 2269583 := bstep (se 1 (by rfl) ⟨1702187, by rfl⟩ : syracuseStep 2269583 = 3404375) B3404375
theorem B1417655 : Blo 944585 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B1417691 : Blo 944585 1417691 := bstep (se 1 (by rfl) ⟨1063268, by rfl⟩ : syracuseStep 1417691 = 2126537) B2126537
theorem B4792891 : Blo 944585 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B3547847 : Blo 944585 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B1418159 : Blo 944585 1418159 := bstep (se 1 (by rfl) ⟨1063619, by rfl⟩ : syracuseStep 1418159 = 2127239) B2127239
theorem B1516463 : Blo 944585 1516463 := bstep (se 1 (by rfl) ⟨1137347, by rfl⟩ : syracuseStep 1516463 = 2274695) B2274695
theorem B1418249 : Blo 944585 1418249 := bstep (se 2 (by rfl) ⟨531843, by rfl⟩ : syracuseStep 1418249 = 1063687) B1063687
theorem B1418279 : Blo 944585 1418279 := bstep (se 1 (by rfl) ⟨1063709, by rfl⟩ : syracuseStep 1418279 = 2127419) B2127419
theorem B1418363 : Blo 944585 1418363 := bstep (se 1 (by rfl) ⟨1063772, by rfl⟩ : syracuseStep 1418363 = 2127545) B2127545
theorem B1418489 : Blo 944585 1418489 := bstep (se 2 (by rfl) ⟨531933, by rfl⟩ : syracuseStep 1418489 = 1063867) B1063867
theorem B1516873 : Blo 944585 1516873 := bstep (se 2 (by rfl) ⟨568827, by rfl⟩ : syracuseStep 1516873 = 1137655) B1137655
theorem B1418591 : Blo 944585 1418591 := bstep (se 1 (by rfl) ⟨1063943, by rfl⟩ : syracuseStep 1418591 = 2127887) B2127887
theorem B1418603 : Blo 944585 1418603 := bstep (se 1 (by rfl) ⟨1063952, by rfl⟩ : syracuseStep 1418603 = 2127905) B2127905
theorem B1418831 : Blo 944585 1418831 := bstep (se 1 (by rfl) ⟨1064123, by rfl⟩ : syracuseStep 1418831 = 2128247) B2128247
theorem B3188321 : Blo 944585 3188321 := bstep (se 2 (by rfl) ⟨1195620, by rfl⟩ : syracuseStep 3188321 = 2391241) B2391241
theorem B4040381 : Blo 944585 4040381 := bstep (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) B1515143
theorem B1418951 : Blo 944585 1418951 := bstep (se 1 (by rfl) ⟨1064213, by rfl⟩ : syracuseStep 1418951 = 2128427) B2128427
theorem B3417923 : Blo 944585 3417923 := bstep (se 1 (by rfl) ⟨2563442, by rfl⟩ : syracuseStep 3417923 = 5126885) B5126885
theorem B1419113 : Blo 944585 1419113 := bstep (se 2 (by rfl) ⟨532167, by rfl⟩ : syracuseStep 1419113 = 1064335) B1064335
theorem B1419191 : Blo 944585 1419191 := bstep (se 1 (by rfl) ⟨1064393, by rfl⟩ : syracuseStep 1419191 = 2128787) B2128787
theorem B1419227 : Blo 944585 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B6138013 : Blo 944585 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B8202583 : Blo 944585 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B5122433 : Blo 944585 5122433 := bstep (se 2 (by rfl) ⟨1920912, by rfl⟩ : syracuseStep 5122433 = 3841825) B3841825
theorem B1419695 : Blo 944585 1419695 := bstep (se 1 (by rfl) ⟨1064771, by rfl⟩ : syracuseStep 1419695 = 2129543) B2129543
theorem B1419785 : Blo 944585 1419785 := bstep (se 2 (by rfl) ⟨532419, by rfl⟩ : syracuseStep 1419785 = 1064839) B1064839
theorem B7186967 : Blo 944585 7186967 := bstep (se 1 (by rfl) ⟨5390225, by rfl⟩ : syracuseStep 7186967 = 10780451) B10780451
theorem B26978849 : Blo 944585 26978849 := bstep (se 2 (by rfl) ⟨10117068, by rfl⟩ : syracuseStep 26978849 = 20234137) B20234137
theorem B1419815 : Blo 944585 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B1419899 : Blo 944585 1419899 := bstep (se 1 (by rfl) ⟨1064924, by rfl⟩ : syracuseStep 1419899 = 2129849) B2129849
theorem B7383737 : Blo 944585 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B2730707 : Blo 944585 2730707 := bstep (se 1 (by rfl) ⟨2048030, by rfl⟩ : syracuseStep 2730707 = 4096061) B4096061
theorem B1420025 : Blo 944585 1420025 := bstep (se 2 (by rfl) ⟨532509, by rfl⟩ : syracuseStep 1420025 = 1065019) B1065019
theorem B3844907 : Blo 944585 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B1420127 : Blo 944585 1420127 := bstep (se 1 (by rfl) ⟨1065095, by rfl⟩ : syracuseStep 1420127 = 2130191) B2130191
theorem B1420139 : Blo 944585 1420139 := bstep (se 1 (by rfl) ⟨1065104, by rfl⟩ : syracuseStep 1420139 = 2130209) B2130209
theorem B8072081 : Blo 944585 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B3189779 : Blo 944585 3189779 := bstep (se 1 (by rfl) ⟨2392334, by rfl⟩ : syracuseStep 3189779 = 4784669) B4784669
theorem B1420367 : Blo 944585 1420367 := bstep (se 1 (by rfl) ⟨1065275, by rfl⟩ : syracuseStep 1420367 = 2130551) B2130551
theorem B2272427 : Blo 944585 2272427 := bstep (se 1 (by rfl) ⟨1704320, by rfl⟩ : syracuseStep 2272427 = 3408641) B3408641
theorem B1420487 : Blo 944585 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B3190103 : Blo 944585 3190103 := bstep (se 1 (by rfl) ⟨2392577, by rfl⟩ : syracuseStep 3190103 = 4785155) B4785155
theorem B1420649 : Blo 944585 1420649 := bstep (se 2 (by rfl) ⟨532743, by rfl⟩ : syracuseStep 1420649 = 1065487) B1065487
theorem B5615021 : Blo 944585 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B1420727 : Blo 944585 1420727 := bstep (se 1 (by rfl) ⟨1065545, by rfl⟩ : syracuseStep 1420727 = 2131091) B2131091
theorem B1420763 : Blo 944585 1420763 := bstep (se 1 (by rfl) ⟨1065572, by rfl⟩ : syracuseStep 1420763 = 2131145) B2131145
theorem B2698849 : Blo 944585 2698849 := bstep (se 2 (by rfl) ⟨1012068, by rfl⟩ : syracuseStep 2698849 = 2024137) B2024137
theorem B3026621 : Blo 944585 3026621 := bstep (se 3 (by rfl) ⟨567491, by rfl⟩ : syracuseStep 3026621 = 1134983) B1134983
theorem B8761223 : Blo 944585 8761223 := bstep (se 1 (by rfl) ⟨6570917, by rfl⟩ : syracuseStep 8761223 = 13141835) B13141835
theorem B1421231 : Blo 944585 1421231 := bstep (se 1 (by rfl) ⟨1065923, by rfl⟩ : syracuseStep 1421231 = 2131847) B2131847
theorem B1421321 : Blo 944585 1421321 := bstep (se 2 (by rfl) ⟨532995, by rfl⟩ : syracuseStep 1421321 = 1065991) B1065991
theorem B1421351 : Blo 944585 1421351 := bstep (se 1 (by rfl) ⟨1066013, by rfl⟩ : syracuseStep 1421351 = 2132027) B2132027
theorem B1421435 : Blo 944585 1421435 := bstep (se 1 (by rfl) ⟨1066076, by rfl⟩ : syracuseStep 1421435 = 2132153) B2132153
theorem B1421561 : Blo 944585 1421561 := bstep (se 2 (by rfl) ⟨533085, by rfl⟩ : syracuseStep 1421561 = 1066171) B1066171
theorem B3027287 : Blo 944585 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B1421663 : Blo 944585 1421663 := bstep (se 1 (by rfl) ⟨1066247, by rfl⟩ : syracuseStep 1421663 = 2132495) B2132495
theorem B1421675 : Blo 944585 1421675 := bstep (se 1 (by rfl) ⟨1066256, by rfl⟩ : syracuseStep 1421675 = 2132513) B2132513
theorem B3191183 : Blo 944585 3191183 := bstep (se 1 (by rfl) ⟨2393387, by rfl⟩ : syracuseStep 3191183 = 4786775) B4786775
theorem B1421903 : Blo 944585 1421903 := bstep (se 1 (by rfl) ⟨1066427, by rfl⟩ : syracuseStep 1421903 = 2132855) B2132855
theorem B1422023 : Blo 944585 1422023 := bstep (se 1 (by rfl) ⟨1066517, by rfl⟩ : syracuseStep 1422023 = 2133035) B2133035
theorem B3191507 : Blo 944585 3191507 := bstep (se 1 (by rfl) ⟨2393630, by rfl⟩ : syracuseStep 3191507 = 4787261) B4787261
theorem B1422185 : Blo 944585 1422185 := bstep (se 2 (by rfl) ⟨533319, by rfl⟩ : syracuseStep 1422185 = 1066639) B1066639
theorem B4043627 : Blo 944585 4043627 := bstep (se 1 (by rfl) ⟨3032720, by rfl⟩ : syracuseStep 4043627 = 6065441) B6065441
theorem B10236779 : Blo 944585 10236779 := bstep (se 1 (by rfl) ⟨7677584, by rfl⟩ : syracuseStep 10236779 = 15355169) B15355169
theorem B4043695 : Blo 944585 4043695 := bstep (se 1 (by rfl) ⟨3032771, by rfl⟩ : syracuseStep 4043695 = 6065543) B6065543
theorem B1422263 : Blo 944585 1422263 := bstep (se 1 (by rfl) ⟨1066697, by rfl⟩ : syracuseStep 1422263 = 2133395) B2133395
theorem B1422299 : Blo 944585 1422299 := bstep (se 1 (by rfl) ⟨1066724, by rfl⟩ : syracuseStep 1422299 = 2133449) B2133449
theorem B2700307 : Blo 944585 2700307 := bstep (se 1 (by rfl) ⟨2025230, by rfl⟩ : syracuseStep 2700307 = 4050461) B4050461
theorem B38810765 : Blo 944585 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B12301483 : Blo 944585 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B2700535 : Blo 944585 2700535 := bstep (se 1 (by rfl) ⟨2025401, by rfl⟩ : syracuseStep 2700535 = 4050803) B4050803
theorem B1422767 : Blo 944585 1422767 := bstep (se 1 (by rfl) ⟨1067075, by rfl⟩ : syracuseStep 1422767 = 2134151) B2134151
theorem B2700809 : Blo 944585 2700809 := bstep (se 2 (by rfl) ⟨1012803, by rfl⟩ : syracuseStep 2700809 = 2025607) B2025607
theorem B1422857 : Blo 944585 1422857 := bstep (se 2 (by rfl) ⟨533571, by rfl⟩ : syracuseStep 1422857 = 1067143) B1067143
theorem B11646713 : Blo 944585 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B1062751 : Blo 944585 1062751 := bstep (se 1 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 1062751 = 1594127) B1594127
theorem B2701151 : Blo 944585 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B4044653 : Blo 944585 4044653 := bstep (se 3 (by rfl) ⟨758372, by rfl⟩ : syracuseStep 4044653 = 1516745) B1516745
theorem B3192695 : Blo 944585 3192695 := bstep (se 1 (by rfl) ⟨2394521, by rfl⟩ : syracuseStep 3192695 = 4789043) B4789043
theorem B4437947 : Blo 944585 4437947 := bstep (se 1 (by rfl) ⟨3328460, by rfl⟩ : syracuseStep 4437947 = 6656921) B6656921
theorem B3192911 : Blo 944585 3192911 := bstep (se 1 (by rfl) ⟨2394683, by rfl⟩ : syracuseStep 3192911 = 4789367) B4789367
theorem B5388403 : Blo 944585 5388403 := bstep (se 1 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 5388403 = 8082605) B8082605
theorem B1063111 : Blo 944585 1063111 := bstep (se 1 (by rfl) ⟨797333, by rfl⟩ : syracuseStep 1063111 = 1594667) B1594667
theorem B1947977 : Blo 944585 1947977 := bstep (se 2 (by rfl) ⟨730491, by rfl⟩ : syracuseStep 1947977 = 1460983) B1460983
theorem B17250691 : Blo 944585 17250691 := bstep (se 1 (by rfl) ⟨12938018, by rfl⟩ : syracuseStep 17250691 = 25876037) B25876037
theorem B3193289 : Blo 944585 3193289 := bstep (se 2 (by rfl) ⟨1197483, by rfl⟩ : syracuseStep 3193289 = 2394967) B2394967
theorem B3029491 : Blo 944585 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B3586619 : Blo 944585 3586619 := bstep (se 1 (by rfl) ⟨2689964, by rfl⟩ : syracuseStep 3586619 = 5379929) B5379929
theorem B3193559 : Blo 944585 3193559 := bstep (se 1 (by rfl) ⟨2395169, by rfl⟩ : syracuseStep 3193559 = 4790339) B4790339
theorem B3193775 : Blo 944585 3193775 := bstep (se 1 (by rfl) ⟨2395331, by rfl⟩ : syracuseStep 3193775 = 4790663) B4790663
theorem B1063975 : Blo 944585 1063975 := bstep (se 1 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 1063975 = 1595963) B1595963
theorem B4046071 : Blo 944585 4046071 := bstep (se 1 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 4046071 = 6069107) B6069107
theorem B4799735 : Blo 944585 4799735 := bstep (se 1 (by rfl) ⟨3599801, by rfl⟩ : syracuseStep 4799735 = 7199603) B7199603
theorem B12139901 : Blo 944585 12139901 := bstep (se 3 (by rfl) ⟨2276231, by rfl⟩ : syracuseStep 12139901 = 4552463) B4552463
theorem B2735489 : Blo 944585 2735489 := bstep (se 2 (by rfl) ⟨1025808, by rfl⟩ : syracuseStep 2735489 = 2051617) B2051617
theorem B1818119 : Blo 944585 1818119 := bstep (se 1 (by rfl) ⟨1363589, by rfl⟩ : syracuseStep 1818119 = 2727179) B2727179
theorem B13811239 : Blo 944585 13811239 := bstep (se 1 (by rfl) ⟨10358429, by rfl⟩ : syracuseStep 13811239 = 20716859) B20716859
theorem B3587773 : Blo 944585 3587773 := bstep (se 3 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 3587773 = 1345415) B1345415
theorem B4800221 : Blo 944585 4800221 := bstep (se 3 (by rfl) ⟨900041, by rfl⟩ : syracuseStep 4800221 = 1800083) B1800083
theorem B7192313 : Blo 944585 7192313 := bstep (se 2 (by rfl) ⟨2697117, by rfl⟩ : syracuseStep 7192313 = 5394235) B5394235
theorem B10239929 : Blo 944585 10239929 := bstep (se 2 (by rfl) ⟨3839973, by rfl⟩ : syracuseStep 10239929 = 7679947) B7679947
theorem B6930521 : Blo 944585 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B20463941 : Blo 944585 20463941 := bstep (se 4 (by rfl) ⟨1918494, by rfl⟩ : syracuseStep 20463941 = 3836989) B3836989
theorem B1622447 : Blo 944585 1622447 := bstep (se 1 (by rfl) ⟨1216835, by rfl⟩ : syracuseStep 1622447 = 2433671) B2433671
theorem B1196471 : Blo 944585 1196471 := bstep (se 1 (by rfl) ⟨897353, by rfl⟩ : syracuseStep 1196471 = 1794707) B1794707
theorem B1196623 : Blo 944585 1196623 := bstep (se 1 (by rfl) ⟨897467, by rfl⟩ : syracuseStep 1196623 = 1794935) B1794935
theorem B3588731 : Blo 944585 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B1065595 : Blo 944585 1065595 := bstep (se 1 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 1065595 = 1598393) B1598393
theorem B34554509 : Blo 944585 34554509 := bstep (se 3 (by rfl) ⟨6478970, by rfl⟩ : syracuseStep 34554509 = 12957941) B12957941
theorem B6145075 : Blo 944585 6145075 := bstep (se 1 (by rfl) ⟨4608806, by rfl⟩ : syracuseStep 6145075 = 9217613) B9217613
theorem B1066063 : Blo 944585 1066063 := bstep (se 1 (by rfl) ⟨799547, by rfl⟩ : syracuseStep 1066063 = 1599095) B1599095
theorem B7193771 : Blo 944585 7193771 := bstep (se 1 (by rfl) ⟨5395328, by rfl⟩ : syracuseStep 7193771 = 10790657) B10790657
theorem B3196151 : Blo 944585 3196151 := bstep (se 1 (by rfl) ⟨2397113, by rfl⟩ : syracuseStep 3196151 = 4794227) B4794227
theorem B3589505 : Blo 944585 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B1066459 : Blo 944585 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B3196475 : Blo 944585 3196475 := bstep (se 1 (by rfl) ⟨2397356, by rfl⟩ : syracuseStep 3196475 = 4794713) B4794713
theorem B1918561 : Blo 944585 1918561 := bstep (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) B1438921
theorem B7194257 : Blo 944585 7194257 := bstep (se 2 (by rfl) ⟨2697846, by rfl⟩ : syracuseStep 7194257 = 5395693) B5395693
theorem B1197767 : Blo 944585 1197767 := bstep (se 1 (by rfl) ⟨898325, by rfl⟩ : syracuseStep 1197767 = 1796651) B1796651
theorem B3196745 : Blo 944585 3196745 := bstep (se 2 (by rfl) ⟨1198779, by rfl⟩ : syracuseStep 3196745 = 2397559) B2397559
theorem B1197919 : Blo 944585 1197919 := bstep (se 1 (by rfl) ⟨898439, by rfl⟩ : syracuseStep 1197919 = 1796879) B1796879
theorem B1066927 : Blo 944585 1066927 := bstep (se 1 (by rfl) ⟨800195, by rfl⟩ : syracuseStep 1066927 = 1600391) B1600391
theorem B13649957 : Blo 944585 13649957 := bstep (se 4 (by rfl) ⟨1279683, by rfl⟩ : syracuseStep 13649957 = 2559367) B2559367
theorem B3033335 : Blo 944585 3033335 := bstep (se 1 (by rfl) ⟨2275001, by rfl⟩ : syracuseStep 3033335 = 4550003) B4550003
theorem B3590689 : Blo 944585 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B2018209 : Blo 944585 2018209 := bstep (se 2 (by rfl) ⟨756828, by rfl⟩ : syracuseStep 2018209 = 1513657) B1513657
theorem B3197879 : Blo 944585 3197879 := bstep (se 1 (by rfl) ⟨2398409, by rfl⟩ : syracuseStep 3197879 = 4796819) B4796819
theorem B3591175 : Blo 944585 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B7195715 : Blo 944585 7195715 := bstep (se 1 (by rfl) ⟨5396786, by rfl⟩ : syracuseStep 7195715 = 10793573) B10793573
theorem B3591661 : Blo 944585 3591661 := bstep (se 3 (by rfl) ⟨673436, by rfl⟩ : syracuseStep 3591661 = 1346873) B1346873
theorem B3198473 : Blo 944585 3198473 := bstep (se 2 (by rfl) ⟨1199427, by rfl⟩ : syracuseStep 3198473 = 2398855) B2398855
theorem B3034759 : Blo 944585 3034759 := bstep (se 1 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 3034759 = 4552139) B4552139
theorem B3591965 : Blo 944585 3591965 := bstep (se 3 (by rfl) ⟨673493, by rfl⟩ : syracuseStep 3591965 = 1346987) B1346987
theorem B1200091 : Blo 944585 1200091 := bstep (se 1 (by rfl) ⟨900068, by rfl⟩ : syracuseStep 1200091 = 1800137) B1800137
theorem B7196687 : Blo 944585 7196687 := bstep (se 1 (by rfl) ⟨5397515, by rfl⟩ : syracuseStep 7196687 = 10795031) B10795031
theorem B4608343 : Blo 944585 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B3199337 : Blo 944585 3199337 := bstep (se 2 (by rfl) ⟨1199751, by rfl⟩ : syracuseStep 3199337 = 2399503) B2399503
theorem B3232315 : Blo 944585 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B630477553 : Blo 944585 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B1594255 : Blo 944585 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B3199931 : Blo 944585 3199931 := bstep (se 1 (by rfl) ⟨2399948, by rfl⟩ : syracuseStep 3199931 = 4799897) B4799897
theorem B1594937 : Blo 944585 1594937 := bstep (se 2 (by rfl) ⟨598101, by rfl⟩ : syracuseStep 1594937 = 1196203) B1196203
theorem B12113657 : Blo 944585 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B1922809 : Blo 944585 1922809 := bstep (se 2 (by rfl) ⟨721053, by rfl⟩ : syracuseStep 1922809 = 1442107) B1442107
theorem B3594091 : Blo 944585 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B1595639 : Blo 944585 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B1595983 : Blo 944585 1595983 := bstep (se 1 (by rfl) ⟨1196987, by rfl⟩ : syracuseStep 1595983 = 2393975) B2393975
theorem B1596233 : Blo 944585 1596233 := bstep (se 2 (by rfl) ⟨598587, by rfl⟩ : syracuseStep 1596233 = 1197175) B1197175
theorem B5757803 : Blo 944585 5757803 := bstep (se 1 (by rfl) ⟨4318352, by rfl⟩ : syracuseStep 5757803 = 8636705) B8636705
theorem B15588395 : Blo 944585 15588395 := bstep (se 1 (by rfl) ⟨11691296, by rfl⟩ : syracuseStep 15588395 = 23382593) B23382593
theorem B10771703 : Blo 944585 10771703 := bstep (se 1 (by rfl) ⟨8078777, by rfl⟩ : syracuseStep 10771703 = 16157555) B16157555
theorem B1596665 : Blo 944585 1596665 := bstep (se 2 (by rfl) ⟨598749, by rfl⟩ : syracuseStep 1596665 = 1197499) B1197499
theorem B7200089 : Blo 944585 7200089 := bstep (se 2 (by rfl) ⟨2700033, by rfl⟩ : syracuseStep 7200089 = 5400067) B5400067
theorem B1596847 : Blo 944585 1596847 := bstep (se 1 (by rfl) ⟨1197635, by rfl⟩ : syracuseStep 1596847 = 2395271) B2395271
theorem B19946933 : Blo 944585 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1596935 : Blo 944585 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B1793659 : Blo 944585 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B1793735 : Blo 944585 1793735 := bstep (se 1 (by rfl) ⟨1345301, by rfl⟩ : syracuseStep 1793735 = 2690603) B2690603
theorem B1597279 : Blo 944585 1597279 := bstep (se 1 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 1597279 = 2395919) B2395919
theorem B1597367 : Blo 944585 1597367 := bstep (se 1 (by rfl) ⟨1198025, by rfl⟩ : syracuseStep 1597367 = 2396051) B2396051
theorem B8085581 : Blo 944585 8085581 := bstep (se 3 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 8085581 = 3032093) B3032093
theorem B5398609 : Blo 944585 5398609 := bstep (se 2 (by rfl) ⟨2024478, by rfl⟩ : syracuseStep 5398609 = 4048957) B4048957
theorem B1794145 : Blo 944585 1794145 := bstep (se 2 (by rfl) ⟨672804, by rfl⟩ : syracuseStep 1794145 = 1345609) B1345609
theorem B1794487 : Blo 944585 1794487 := bstep (se 1 (by rfl) ⟨1345865, by rfl⟩ : syracuseStep 1794487 = 2691731) B2691731
theorem B1597961 : Blo 944585 1597961 := bstep (se 2 (by rfl) ⟨599235, by rfl⟩ : syracuseStep 1597961 = 1198471) B1198471
theorem B3596825 : Blo 944585 3596825 := bstep (se 2 (by rfl) ⟨1348809, by rfl⟩ : syracuseStep 3596825 = 2697619) B2697619
theorem B1139279 : Blo 944585 1139279 := bstep (se 1 (by rfl) ⟨854459, by rfl⟩ : syracuseStep 1139279 = 1708919) B1708919
theorem B1598123 : Blo 944585 1598123 := bstep (se 1 (by rfl) ⟨1198592, by rfl⟩ : syracuseStep 1598123 = 2397185) B2397185
theorem B10216145 : Blo 944585 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B1794889 : Blo 944585 1794889 := bstep (se 2 (by rfl) ⟨673083, by rfl⟩ : syracuseStep 1794889 = 1346167) B1346167
theorem B10216367 : Blo 944585 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B1598521 : Blo 944585 1598521 := bstep (se 2 (by rfl) ⟨599445, by rfl⟩ : syracuseStep 1598521 = 1198891) B1198891
theorem B1598663 : Blo 944585 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B1598825 : Blo 944585 1598825 := bstep (se 2 (by rfl) ⟨599559, by rfl⟩ : syracuseStep 1598825 = 1199119) B1199119
theorem B1795603 : Blo 944585 1795603 := bstep (se 1 (by rfl) ⟨1346702, by rfl⟩ : syracuseStep 1795603 = 2693405) B2693405
theorem B3892769 : Blo 944585 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B11495009 : Blo 944585 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B7202519 : Blo 944585 7202519 := bstep (se 1 (by rfl) ⟨5401889, by rfl⟩ : syracuseStep 7202519 = 10803779) B10803779
theorem B1599223 : Blo 944585 1599223 := bstep (se 1 (by rfl) ⟨1199417, by rfl⟩ : syracuseStep 1599223 = 2398835) B2398835
theorem B1795945 : Blo 944585 1795945 := bstep (se 2 (by rfl) ⟨673479, by rfl⟩ : syracuseStep 1795945 = 1346959) B1346959
theorem B4319095 : Blo 944585 4319095 := bstep (se 1 (by rfl) ⟨3239321, by rfl⟩ : syracuseStep 4319095 = 6478643) B6478643
theorem B1599419 : Blo 944585 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B50456513 : Blo 944585 50456513 := bstep (se 2 (by rfl) ⟨18921192, by rfl⟩ : syracuseStep 50456513 = 37842385) B37842385
theorem B1599527 : Blo 944585 1599527 := bstep (se 1 (by rfl) ⟨1199645, by rfl⟩ : syracuseStep 1599527 = 2399291) B2399291
theorem B3598451 : Blo 944585 3598451 := bstep (se 1 (by rfl) ⟨2698838, by rfl⟩ : syracuseStep 3598451 = 5397677) B5397677
theorem B1599817 : Blo 944585 1599817 := bstep (se 2 (by rfl) ⟨599931, by rfl⟩ : syracuseStep 1599817 = 1199863) B1199863
theorem B1599851 : Blo 944585 1599851 := bstep (se 1 (by rfl) ⟨1199888, by rfl⟩ : syracuseStep 1599851 = 2399777) B2399777
theorem B944603 : Blo 944585 944603 := bstep (se 1 (by rfl) ⟨708452, by rfl⟩ : syracuseStep 944603 = 1416905) B1416905
theorem B6056471 : Blo 944585 6056471 := bstep (se 1 (by rfl) ⟨4542353, by rfl⟩ : syracuseStep 6056471 = 9084707) B9084707
theorem B944679 : Blo 944585 944679 := bstep (se 1 (by rfl) ⟨708509, by rfl⟩ : syracuseStep 944679 = 1417019) B1417019
theorem B944719 : Blo 944585 944719 := bstep (se 1 (by rfl) ⟨708539, by rfl⟩ : syracuseStep 944719 = 1417079) B1417079
theorem B944735 : Blo 944585 944735 := bstep (se 1 (by rfl) ⟨708551, by rfl⟩ : syracuseStep 944735 = 1417103) B1417103
theorem B944763 : Blo 944585 944763 := bstep (se 1 (by rfl) ⟨708572, by rfl⟩ : syracuseStep 944763 = 1417145) B1417145
theorem B944815 : Blo 944585 944815 := bstep (se 1 (by rfl) ⟨708611, by rfl⟩ : syracuseStep 944815 = 1417223) B1417223
theorem B944839 : Blo 944585 944839 := bstep (se 1 (by rfl) ⟨708629, by rfl⟩ : syracuseStep 944839 = 1417259) B1417259
theorem B27323081 : Blo 944585 27323081 := bstep (se 2 (by rfl) ⟨10246155, by rfl⟩ : syracuseStep 27323081 = 20492311) B20492311
theorem B944859 : Blo 944585 944859 := bstep (se 1 (by rfl) ⟨708644, by rfl⟩ : syracuseStep 944859 = 1417289) B1417289
theorem B1600249 : Blo 944585 1600249 := bstep (se 2 (by rfl) ⟨600093, by rfl⟩ : syracuseStep 1600249 = 1200187) B1200187
theorem B944935 : Blo 944585 944935 := bstep (se 1 (by rfl) ⟨708701, by rfl⟩ : syracuseStep 944935 = 1417403) B1417403
theorem B944975 : Blo 944585 944975 := bstep (se 1 (by rfl) ⟨708731, by rfl⟩ : syracuseStep 944975 = 1417463) B1417463
theorem B944991 : Blo 944585 944991 := bstep (se 1 (by rfl) ⟨708743, by rfl⟩ : syracuseStep 944991 = 1417487) B1417487
theorem B945019 : Blo 944585 945019 := bstep (se 1 (by rfl) ⟨708764, by rfl⟩ : syracuseStep 945019 = 1417529) B1417529
theorem B945071 : Blo 944585 945071 := bstep (se 1 (by rfl) ⟨708803, by rfl⟩ : syracuseStep 945071 = 1417607) B1417607
theorem B945095 : Blo 944585 945095 := bstep (se 1 (by rfl) ⟨708821, by rfl⟩ : syracuseStep 945095 = 1417643) B1417643
theorem B945115 : Blo 944585 945115 := bstep (se 1 (by rfl) ⟨708836, by rfl⟩ : syracuseStep 945115 = 1417673) B1417673
theorem B1600519 : Blo 944585 1600519 := bstep (se 1 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 1600519 = 2400779) B2400779
theorem B945191 : Blo 944585 945191 := bstep (se 1 (by rfl) ⟨708893, by rfl⟩ : syracuseStep 945191 = 1417787) B1417787
theorem B8088619 : Blo 944585 8088619 := bstep (se 1 (by rfl) ⟨6066464, by rfl⟩ : syracuseStep 8088619 = 12132929) B12132929
theorem B945231 : Blo 944585 945231 := bstep (se 1 (by rfl) ⟨708923, by rfl⟩ : syracuseStep 945231 = 1417847) B1417847
theorem B945247 : Blo 944585 945247 := bstep (se 1 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 945247 = 1417871) B1417871
theorem B945275 : Blo 944585 945275 := bstep (se 1 (by rfl) ⟨708956, by rfl⟩ : syracuseStep 945275 = 1417913) B1417913
theorem B945327 : Blo 944585 945327 := bstep (se 1 (by rfl) ⟨708995, by rfl⟩ : syracuseStep 945327 = 1417991) B1417991
theorem B945351 : Blo 944585 945351 := bstep (se 1 (by rfl) ⟨709013, by rfl⟩ : syracuseStep 945351 = 1418027) B1418027
theorem B1797319 : Blo 944585 1797319 := bstep (se 1 (by rfl) ⟨1347989, by rfl⟩ : syracuseStep 1797319 = 2695979) B2695979
theorem B945371 : Blo 944585 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B945447 : Blo 944585 945447 := bstep (se 1 (by rfl) ⟨709085, by rfl⟩ : syracuseStep 945447 = 1418171) B1418171
theorem B945487 : Blo 944585 945487 := bstep (se 1 (by rfl) ⟨709115, by rfl⟩ : syracuseStep 945487 = 1418231) B1418231
theorem B945503 : Blo 944585 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B945531 : Blo 944585 945531 := bstep (se 1 (by rfl) ⟨709148, by rfl⟩ : syracuseStep 945531 = 1418297) B1418297
theorem B3599741 : Blo 944585 3599741 := bstep (se 3 (by rfl) ⟨674951, by rfl⟩ : syracuseStep 3599741 = 1349903) B1349903
theorem B945583 : Blo 944585 945583 := bstep (se 1 (by rfl) ⟨709187, by rfl⟩ : syracuseStep 945583 = 1418375) B1418375
theorem B945607 : Blo 944585 945607 := bstep (se 1 (by rfl) ⟨709205, by rfl⟩ : syracuseStep 945607 = 1418411) B1418411
theorem B945627 : Blo 944585 945627 := bstep (se 1 (by rfl) ⟨709220, by rfl⟩ : syracuseStep 945627 = 1418441) B1418441
theorem B945703 : Blo 944585 945703 := bstep (se 1 (by rfl) ⟨709277, by rfl⟩ : syracuseStep 945703 = 1418555) B1418555
theorem B945743 : Blo 944585 945743 := bstep (se 1 (by rfl) ⟨709307, by rfl⟩ : syracuseStep 945743 = 1418615) B1418615
theorem B945759 : Blo 944585 945759 := bstep (se 1 (by rfl) ⟨709319, by rfl⟩ : syracuseStep 945759 = 1418639) B1418639
theorem B945787 : Blo 944585 945787 := bstep (se 1 (by rfl) ⟨709340, by rfl⟩ : syracuseStep 945787 = 1418681) B1418681
theorem B945839 : Blo 944585 945839 := bstep (se 1 (by rfl) ⟨709379, by rfl⟩ : syracuseStep 945839 = 1418759) B1418759
theorem B2125511 : Blo 944585 2125511 := bstep (se 1 (by rfl) ⟨1594133, by rfl⟩ : syracuseStep 2125511 = 3188267) B3188267
theorem B945863 : Blo 944585 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B945883 : Blo 944585 945883 := bstep (se 1 (by rfl) ⟨709412, by rfl⟩ : syracuseStep 945883 = 1418825) B1418825
theorem B39415517 : Blo 944585 39415517 := bstep (se 3 (by rfl) ⟨7390409, by rfl⟩ : syracuseStep 39415517 = 14780819) B14780819
theorem B945959 : Blo 944585 945959 := bstep (se 1 (by rfl) ⟨709469, by rfl⟩ : syracuseStep 945959 = 1418939) B1418939
theorem B945999 : Blo 944585 945999 := bstep (se 1 (by rfl) ⟨709499, by rfl⟩ : syracuseStep 945999 = 1418999) B1418999
theorem B946015 : Blo 944585 946015 := bstep (se 1 (by rfl) ⟨709511, by rfl⟩ : syracuseStep 946015 = 1419023) B1419023
theorem B2879327 : Blo 944585 2879327 := bstep (se 1 (by rfl) ⟨2159495, by rfl⟩ : syracuseStep 2879327 = 4318991) B4318991
theorem B946043 : Blo 944585 946043 := bstep (se 1 (by rfl) ⟨709532, by rfl⟩ : syracuseStep 946043 = 1419065) B1419065
theorem B946095 : Blo 944585 946095 := bstep (se 1 (by rfl) ⟨709571, by rfl⟩ : syracuseStep 946095 = 1419143) B1419143
theorem B946119 : Blo 944585 946119 := bstep (se 1 (by rfl) ⟨709589, by rfl⟩ : syracuseStep 946119 = 1419179) B1419179
theorem B946139 : Blo 944585 946139 := bstep (se 1 (by rfl) ⟨709604, by rfl⟩ : syracuseStep 946139 = 1419209) B1419209
theorem B13627403 : Blo 944585 13627403 := bstep (se 1 (by rfl) ⟨10220552, by rfl⟩ : syracuseStep 13627403 = 20441105) B20441105
theorem B6811685 : Blo 944585 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B946215 : Blo 944585 946215 := bstep (se 1 (by rfl) ⟨709661, by rfl⟩ : syracuseStep 946215 = 1419323) B1419323
theorem B946255 : Blo 944585 946255 := bstep (se 1 (by rfl) ⟨709691, by rfl⟩ : syracuseStep 946255 = 1419383) B1419383
theorem B946271 : Blo 944585 946271 := bstep (se 1 (by rfl) ⟨709703, by rfl⟩ : syracuseStep 946271 = 1419407) B1419407
theorem B946299 : Blo 944585 946299 := bstep (se 1 (by rfl) ⟨709724, by rfl⟩ : syracuseStep 946299 = 1419449) B1419449
theorem B4550813 : Blo 944585 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B946351 : Blo 944585 946351 := bstep (se 1 (by rfl) ⟨709763, by rfl⟩ : syracuseStep 946351 = 1419527) B1419527
theorem B946375 : Blo 944585 946375 := bstep (se 1 (by rfl) ⟨709781, by rfl⟩ : syracuseStep 946375 = 1419563) B1419563
theorem B946395 : Blo 944585 946395 := bstep (se 1 (by rfl) ⟨709796, by rfl⟩ : syracuseStep 946395 = 1419593) B1419593
theorem B946471 : Blo 944585 946471 := bstep (se 1 (by rfl) ⟨709853, by rfl⟩ : syracuseStep 946471 = 1419707) B1419707
theorem B946511 : Blo 944585 946511 := bstep (se 1 (by rfl) ⟨709883, by rfl⟩ : syracuseStep 946511 = 1419767) B1419767
theorem B946527 : Blo 944585 946527 := bstep (se 1 (by rfl) ⟨709895, by rfl⟩ : syracuseStep 946527 = 1419791) B1419791
theorem B946555 : Blo 944585 946555 := bstep (se 1 (by rfl) ⟨709916, by rfl⟩ : syracuseStep 946555 = 1419833) B1419833
theorem B946607 : Blo 944585 946607 := bstep (se 1 (by rfl) ⟨709955, by rfl⟩ : syracuseStep 946607 = 1419911) B1419911
theorem B946631 : Blo 944585 946631 := bstep (se 1 (by rfl) ⟨709973, by rfl⟩ : syracuseStep 946631 = 1419947) B1419947
theorem B946651 : Blo 944585 946651 := bstep (se 1 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 946651 = 1419977) B1419977
theorem B5763565 : Blo 944585 5763565 := bstep (se 3 (by rfl) ⟨1080668, by rfl⟩ : syracuseStep 5763565 = 2161337) B2161337
theorem B2126375 : Blo 944585 2126375 := bstep (se 1 (by rfl) ⟨1594781, by rfl⟩ : syracuseStep 2126375 = 3189563) B3189563
theorem B946727 : Blo 944585 946727 := bstep (se 1 (by rfl) ⟨710045, by rfl⟩ : syracuseStep 946727 = 1420091) B1420091
theorem B946767 : Blo 944585 946767 := bstep (se 1 (by rfl) ⟨710075, by rfl⟩ : syracuseStep 946767 = 1420151) B1420151
theorem B946783 : Blo 944585 946783 := bstep (se 1 (by rfl) ⟨710087, by rfl⟩ : syracuseStep 946783 = 1420175) B1420175
theorem B946811 : Blo 944585 946811 := bstep (se 1 (by rfl) ⟨710108, by rfl⟩ : syracuseStep 946811 = 1420217) B1420217
theorem B946863 : Blo 944585 946863 := bstep (se 1 (by rfl) ⟨710147, by rfl⟩ : syracuseStep 946863 = 1420295) B1420295
theorem B946887 : Blo 944585 946887 := bstep (se 1 (by rfl) ⟨710165, by rfl⟩ : syracuseStep 946887 = 1420331) B1420331
theorem B946907 : Blo 944585 946907 := bstep (se 1 (by rfl) ⟨710180, by rfl⟩ : syracuseStep 946907 = 1420361) B1420361
theorem B946983 : Blo 944585 946983 := bstep (se 1 (by rfl) ⟨710237, by rfl⟩ : syracuseStep 946983 = 1420475) B1420475
theorem B947023 : Blo 944585 947023 := bstep (se 1 (by rfl) ⟨710267, by rfl⟩ : syracuseStep 947023 = 1420535) B1420535
theorem B947039 : Blo 944585 947039 := bstep (se 1 (by rfl) ⟨710279, by rfl⟩ : syracuseStep 947039 = 1420559) B1420559
theorem B2126699 : Blo 944585 2126699 := bstep (se 1 (by rfl) ⟨1595024, by rfl⟩ : syracuseStep 2126699 = 3190049) B3190049
theorem B947067 : Blo 944585 947067 := bstep (se 1 (by rfl) ⟨710300, by rfl⟩ : syracuseStep 947067 = 1420601) B1420601
theorem B13661081 : Blo 944585 13661081 := bstep (se 2 (by rfl) ⟨5122905, by rfl⟩ : syracuseStep 13661081 = 10245811) B10245811
theorem B2126753 : Blo 944585 2126753 := bstep (se 2 (by rfl) ⟨797532, by rfl⟩ : syracuseStep 2126753 = 1595065) B1595065
theorem B947119 : Blo 944585 947119 := bstep (se 1 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 947119 = 1420679) B1420679
theorem B947143 : Blo 944585 947143 := bstep (se 1 (by rfl) ⟨710357, by rfl⟩ : syracuseStep 947143 = 1420715) B1420715
theorem B947163 : Blo 944585 947163 := bstep (se 1 (by rfl) ⟨710372, by rfl⟩ : syracuseStep 947163 = 1420745) B1420745
theorem B947239 : Blo 944585 947239 := bstep (se 1 (by rfl) ⟨710429, by rfl⟩ : syracuseStep 947239 = 1420859) B1420859
theorem B3404879 : Blo 944585 3404879 := bstep (se 1 (by rfl) ⟨2553659, by rfl⟩ : syracuseStep 3404879 = 5107319) B5107319
theorem B947279 : Blo 944585 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B947295 : Blo 944585 947295 := bstep (se 1 (by rfl) ⟨710471, by rfl⟩ : syracuseStep 947295 = 1420943) B1420943
theorem B947323 : Blo 944585 947323 := bstep (se 1 (by rfl) ⟨710492, by rfl⟩ : syracuseStep 947323 = 1420985) B1420985
theorem B947375 : Blo 944585 947375 := bstep (se 1 (by rfl) ⟨710531, by rfl⟩ : syracuseStep 947375 = 1421063) B1421063
theorem B947399 : Blo 944585 947399 := bstep (se 1 (by rfl) ⟨710549, by rfl⟩ : syracuseStep 947399 = 1421099) B1421099
theorem B947419 : Blo 944585 947419 := bstep (se 1 (by rfl) ⟨710564, by rfl⟩ : syracuseStep 947419 = 1421129) B1421129
theorem B2127095 : Blo 944585 2127095 := bstep (se 1 (by rfl) ⟨1595321, by rfl⟩ : syracuseStep 2127095 = 3190643) B3190643
theorem B3601655 : Blo 944585 3601655 := bstep (se 1 (by rfl) ⟨2701241, by rfl⟩ : syracuseStep 3601655 = 5402483) B5402483
theorem B947495 : Blo 944585 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B947535 : Blo 944585 947535 := bstep (se 1 (by rfl) ⟨710651, by rfl⟩ : syracuseStep 947535 = 1421303) B1421303
theorem B947551 : Blo 944585 947551 := bstep (se 1 (by rfl) ⟨710663, by rfl⟩ : syracuseStep 947551 = 1421327) B1421327
theorem B947579 : Blo 944585 947579 := bstep (se 1 (by rfl) ⟨710684, by rfl⟩ : syracuseStep 947579 = 1421369) B1421369
theorem B1799567 : Blo 944585 1799567 := bstep (se 1 (by rfl) ⟨1349675, by rfl⟩ : syracuseStep 1799567 = 2699351) B2699351
theorem B947631 : Blo 944585 947631 := bstep (se 1 (by rfl) ⟨710723, by rfl⟩ : syracuseStep 947631 = 1421447) B1421447
theorem B947655 : Blo 944585 947655 := bstep (se 1 (by rfl) ⟨710741, by rfl⟩ : syracuseStep 947655 = 1421483) B1421483
theorem B947675 : Blo 944585 947675 := bstep (se 1 (by rfl) ⟨710756, by rfl⟩ : syracuseStep 947675 = 1421513) B1421513
theorem B947751 : Blo 944585 947751 := bstep (se 1 (by rfl) ⟨710813, by rfl⟩ : syracuseStep 947751 = 1421627) B1421627
theorem B947791 : Blo 944585 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B947807 : Blo 944585 947807 := bstep (se 1 (by rfl) ⟨710855, by rfl⟩ : syracuseStep 947807 = 1421711) B1421711
theorem B947835 : Blo 944585 947835 := bstep (se 1 (by rfl) ⟨710876, by rfl⟩ : syracuseStep 947835 = 1421753) B1421753
theorem B947887 : Blo 944585 947887 := bstep (se 1 (by rfl) ⟨710915, by rfl⟩ : syracuseStep 947887 = 1421831) B1421831
theorem B947911 : Blo 944585 947911 := bstep (se 1 (by rfl) ⟨710933, by rfl⟩ : syracuseStep 947911 = 1421867) B1421867
theorem B947931 : Blo 944585 947931 := bstep (se 1 (by rfl) ⟨710948, by rfl⟩ : syracuseStep 947931 = 1421897) B1421897
theorem B948007 : Blo 944585 948007 := bstep (se 1 (by rfl) ⟨711005, by rfl⟩ : syracuseStep 948007 = 1422011) B1422011
theorem B2127689 : Blo 944585 2127689 := bstep (se 2 (by rfl) ⟨797883, by rfl⟩ : syracuseStep 2127689 = 1595767) B1595767
theorem B948047 : Blo 944585 948047 := bstep (se 1 (by rfl) ⟨711035, by rfl⟩ : syracuseStep 948047 = 1422071) B1422071
theorem B948063 : Blo 944585 948063 := bstep (se 1 (by rfl) ⟨711047, by rfl⟩ : syracuseStep 948063 = 1422095) B1422095
theorem B948091 : Blo 944585 948091 := bstep (se 1 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 948091 = 1422137) B1422137
theorem B948143 : Blo 944585 948143 := bstep (se 1 (by rfl) ⟨711107, by rfl⟩ : syracuseStep 948143 = 1422215) B1422215
theorem B948167 : Blo 944585 948167 := bstep (se 1 (by rfl) ⟨711125, by rfl⟩ : syracuseStep 948167 = 1422251) B1422251
theorem B948187 : Blo 944585 948187 := bstep (se 1 (by rfl) ⟨711140, by rfl⟩ : syracuseStep 948187 = 1422281) B1422281
theorem B948263 : Blo 944585 948263 := bstep (se 1 (by rfl) ⟨711197, by rfl⟩ : syracuseStep 948263 = 1422395) B1422395
theorem B948303 : Blo 944585 948303 := bstep (se 1 (by rfl) ⟨711227, by rfl⟩ : syracuseStep 948303 = 1422455) B1422455
theorem B948319 : Blo 944585 948319 := bstep (se 1 (by rfl) ⟨711239, by rfl⟩ : syracuseStep 948319 = 1422479) B1422479
theorem B948347 : Blo 944585 948347 := bstep (se 1 (by rfl) ⟨711260, by rfl⟩ : syracuseStep 948347 = 1422521) B1422521
theorem B8747165 : Blo 944585 8747165 := bstep (se 3 (by rfl) ⟨1640093, by rfl⟩ : syracuseStep 8747165 = 3280187) B3280187
theorem B9730205 : Blo 944585 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B948399 : Blo 944585 948399 := bstep (se 1 (by rfl) ⟨711299, by rfl⟩ : syracuseStep 948399 = 1422599) B1422599
theorem B948423 : Blo 944585 948423 := bstep (se 1 (by rfl) ⟨711317, by rfl⟩ : syracuseStep 948423 = 1422635) B1422635
theorem B948443 : Blo 944585 948443 := bstep (se 1 (by rfl) ⟨711332, by rfl⟩ : syracuseStep 948443 = 1422665) B1422665
theorem B948519 : Blo 944585 948519 := bstep (se 1 (by rfl) ⟨711389, by rfl⟩ : syracuseStep 948519 = 1422779) B1422779
theorem B948559 : Blo 944585 948559 := bstep (se 1 (by rfl) ⟨711419, by rfl⟩ : syracuseStep 948559 = 1422839) B1422839
theorem B948575 : Blo 944585 948575 := bstep (se 1 (by rfl) ⟨711431, by rfl⟩ : syracuseStep 948575 = 1422863) B1422863
theorem B30669191 : Blo 944585 30669191 := bstep (se 1 (by rfl) ⟨23001893, by rfl⟩ : syracuseStep 30669191 = 46003787) B46003787
theorem B1800623 : Blo 944585 1800623 := bstep (se 1 (by rfl) ⟨1350467, by rfl⟩ : syracuseStep 1800623 = 2700935) B2700935
theorem B2128481 : Blo 944585 2128481 := bstep (se 2 (by rfl) ⟨798180, by rfl⟩ : syracuseStep 2128481 = 1596361) B1596361
theorem B4553425 : Blo 944585 4553425 := bstep (se 2 (by rfl) ⟨1707534, by rfl⟩ : syracuseStep 4553425 = 3415069) B3415069
theorem B1440617 : Blo 944585 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B2128823 : Blo 944585 2128823 := bstep (se 1 (by rfl) ⟨1596617, by rfl⟩ : syracuseStep 2128823 = 3193235) B3193235
theorem B2391059 : Blo 944585 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B9108773 : Blo 944585 9108773 := bstep (se 4 (by rfl) ⟨853947, by rfl⟩ : syracuseStep 9108773 = 1707895) B1707895
theorem B2391515 : Blo 944585 2391515 := bstep (se 1 (by rfl) ⟨1793636, by rfl⟩ : syracuseStep 2391515 = 3587273) B3587273
theorem B2129417 : Blo 944585 2129417 := bstep (se 2 (by rfl) ⟨798531, by rfl⟩ : syracuseStep 2129417 = 1597063) B1597063
theorem B2129759 : Blo 944585 2129759 := bstep (se 1 (by rfl) ⟨1597319, by rfl⟩ : syracuseStep 2129759 = 3194639) B3194639
theorem B4620347 : Blo 944585 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B2392193 : Blo 944585 2392193 := bstep (se 2 (by rfl) ⟨897072, by rfl⟩ : syracuseStep 2392193 = 1794145) B1794145
theorem B1081631 : Blo 944585 1081631 := bstep (se 1 (by rfl) ⟨811223, by rfl⟩ : syracuseStep 1081631 = 1622447) B1622447
theorem B9109847 : Blo 944585 9109847 := bstep (se 1 (by rfl) ⟨6832385, by rfl⟩ : syracuseStep 9109847 = 13664771) B13664771
theorem B2392487 : Blo 944585 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B23036339 : Blo 944585 23036339 := bstep (se 1 (by rfl) ⟨17277254, by rfl⟩ : syracuseStep 23036339 = 34554509) B34554509
theorem B2392649 : Blo 944585 2392649 := bstep (se 2 (by rfl) ⟨897243, by rfl⟩ : syracuseStep 2392649 = 1794487) B1794487
theorem B6390521 : Blo 944585 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B2130767 : Blo 944585 2130767 := bstep (se 1 (by rfl) ⟨1598075, by rfl⟩ : syracuseStep 2130767 = 3196151) B3196151
theorem B2393003 : Blo 944585 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B2130983 : Blo 944585 2130983 := bstep (se 1 (by rfl) ⟨1598237, by rfl⟩ : syracuseStep 2130983 = 3196475) B3196475
theorem B2393185 : Blo 944585 2393185 := bstep (se 2 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 2393185 = 1794889) B1794889
theorem B2131163 : Blo 944585 2131163 := bstep (se 1 (by rfl) ⟨1598372, by rfl⟩ : syracuseStep 2131163 = 3196745) B3196745
theorem B388498747 : Blo 944585 388498747 := bstep (se 1 (by rfl) ⟨291374060, by rfl⟩ : syracuseStep 388498747 = 582748121) B582748121
theorem B2131361 : Blo 944585 2131361 := bstep (se 2 (by rfl) ⟨799260, by rfl⟩ : syracuseStep 2131361 = 1598521) B1598521
theorem B4786127 : Blo 944585 4786127 := bstep (se 1 (by rfl) ⟨3589595, by rfl⟩ : syracuseStep 4786127 = 7179191) B7179191
theorem B2131919 : Blo 944585 2131919 := bstep (se 1 (by rfl) ⟨1598939, by rfl⟩ : syracuseStep 2131919 = 3197879) B3197879
theorem B2394137 : Blo 944585 2394137 := bstep (se 2 (by rfl) ⟨897801, by rfl⟩ : syracuseStep 2394137 = 1795603) B1795603
theorem B2558081 : Blo 944585 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B2132297 : Blo 944585 2132297 := bstep (se 2 (by rfl) ⟨799611, by rfl⟩ : syracuseStep 2132297 = 1599223) B1599223
theorem B2132315 : Blo 944585 2132315 := bstep (se 1 (by rfl) ⟨1599236, by rfl⟩ : syracuseStep 2132315 = 3198473) B3198473
theorem B2394593 : Blo 944585 2394593 := bstep (se 2 (by rfl) ⟨897972, by rfl⟩ : syracuseStep 2394593 = 1795945) B1795945
theorem B2394643 : Blo 944585 2394643 := bstep (se 1 (by rfl) ⟨1795982, by rfl⟩ : syracuseStep 2394643 = 3591965) B3591965
theorem B1641067 : Blo 944585 1641067 := bstep (se 1 (by rfl) ⟨1230800, by rfl⟩ : syracuseStep 1641067 = 2461601) B2461601
theorem B4787099 : Blo 944585 4787099 := bstep (se 1 (by rfl) ⟨3590324, by rfl⟩ : syracuseStep 4787099 = 7180649) B7180649
theorem B2132891 : Blo 944585 2132891 := bstep (se 1 (by rfl) ⟨1599668, by rfl⟩ : syracuseStep 2132891 = 3199337) B3199337
theorem B17239013 : Blo 944585 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B2133089 : Blo 944585 2133089 := bstep (se 2 (by rfl) ⟨799908, by rfl⟩ : syracuseStep 2133089 = 1599817) B1599817
theorem B5180683 : Blo 944585 5180683 := bstep (se 1 (by rfl) ⟨3885512, by rfl⟩ : syracuseStep 5180683 = 7771025) B7771025
theorem B2133287 : Blo 944585 2133287 := bstep (se 1 (by rfl) ⟨1599965, by rfl⟩ : syracuseStep 2133287 = 3199931) B3199931
theorem B4787585 : Blo 944585 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B2133665 : Blo 944585 2133665 := bstep (se 2 (by rfl) ⟨800124, by rfl⟩ : syracuseStep 2133665 = 1600249) B1600249
theorem B2690945 : Blo 944585 2690945 := bstep (se 2 (by rfl) ⟨1009104, by rfl⟩ : syracuseStep 2690945 = 2018209) B2018209
theorem B3411841 : Blo 944585 3411841 := bstep (se 2 (by rfl) ⟨1279440, by rfl⟩ : syracuseStep 3411841 = 2558881) B2558881
theorem B4788233 : Blo 944585 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B2134025 : Blo 944585 2134025 := bstep (se 2 (by rfl) ⟨800259, by rfl⟩ : syracuseStep 2134025 = 1600519) B1600519
theorem B10784825 : Blo 944585 10784825 := bstep (se 2 (by rfl) ⟨4044309, by rfl⟩ : syracuseStep 10784825 = 8088619) B8088619
theorem B10227779 : Blo 944585 10227779 := bstep (se 1 (by rfl) ⟨7670834, by rfl⟩ : syracuseStep 10227779 = 15341669) B15341669
theorem B4788395 : Blo 944585 4788395 := bstep (se 1 (by rfl) ⟨3591296, by rfl⟩ : syracuseStep 4788395 = 7182593) B7182593
theorem B2396425 : Blo 944585 2396425 := bstep (se 2 (by rfl) ⟨898659, by rfl⟩ : syracuseStep 2396425 = 1797319) B1797319
theorem B3412331 : Blo 944585 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B3838535 : Blo 944585 3838535 := bstep (se 1 (by rfl) ⟨2878901, by rfl⟩ : syracuseStep 3838535 = 5757803) B5757803
theorem B4788881 : Blo 944585 4788881 := bstep (se 2 (by rfl) ⟨1795830, by rfl⟩ : syracuseStep 4788881 = 3591661) B3591661
theorem B10392263 : Blo 944585 10392263 := bstep (se 1 (by rfl) ⟨7794197, by rfl⟩ : syracuseStep 10392263 = 15588395) B15588395
theorem B7181135 : Blo 944585 7181135 := bstep (se 1 (by rfl) ⟨5385851, by rfl⟩ : syracuseStep 7181135 = 10771703) B10771703
theorem B11834525 : Blo 944585 11834525 := bstep (se 3 (by rfl) ⟨2218973, by rfl⟩ : syracuseStep 11834525 = 4437947) B4437947
theorem B1513055 : Blo 944585 1513055 := bstep (se 1 (by rfl) ⟨1134791, by rfl⟩ : syracuseStep 1513055 = 2269583) B2269583
theorem B32773733 : Blo 944585 32773733 := bstep (se 4 (by rfl) ⟨3072537, by rfl⟩ : syracuseStep 32773733 = 6145075) B6145075
theorem B2397883 : Blo 944585 2397883 := bstep (se 1 (by rfl) ⟨1798412, by rfl⟩ : syracuseStep 2397883 = 3596825) B3596825
theorem B840636737 : Blo 944585 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B2595179 : Blo 944585 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B2693587 : Blo 944585 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B2398967 : Blo 944585 2398967 := bstep (se 1 (by rfl) ⟨1799225, by rfl⟩ : syracuseStep 2398967 = 3598451) B3598451
theorem B3414955 : Blo 944585 3414955 := bstep (se 1 (by rfl) ⟨2561216, by rfl⟩ : syracuseStep 3414955 = 5122433) B5122433
theorem B4037647 : Blo 944585 4037647 := bstep (se 1 (by rfl) ⟨3028235, by rfl⟩ : syracuseStep 4037647 = 6056471) B6056471
theorem B4791311 : Blo 944585 4791311 := bstep (se 1 (by rfl) ⟨3593483, by rfl⟩ : syracuseStep 4791311 = 7186967) B7186967
theorem B4922491 : Blo 944585 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B2563271 : Blo 944585 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B5381387 : Blo 944585 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B1514951 : Blo 944585 1514951 := bstep (se 1 (by rfl) ⟨1136213, by rfl⟩ : syracuseStep 1514951 = 2272427) B2272427
theorem B2399827 : Blo 944585 2399827 := bstep (se 1 (by rfl) ⟨1799870, by rfl⟩ : syracuseStep 2399827 = 3599741) B3599741
theorem B3743347 : Blo 944585 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B2563745 : Blo 944585 2563745 := bstep (se 2 (by rfl) ⟨961404, by rfl⟩ : syracuseStep 2563745 = 1922809) B1922809
theorem B1417001 : Blo 944585 1417001 := bstep (se 2 (by rfl) ⟨531375, by rfl⟩ : syracuseStep 1417001 = 1062751) B1062751
theorem B1417007 : Blo 944585 1417007 := bstep (se 1 (by rfl) ⟨1062755, by rfl⟩ : syracuseStep 1417007 = 2125511) B2125511
theorem B4792121 : Blo 944585 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B9084935 : Blo 944585 9084935 := bstep (se 1 (by rfl) ⟨6813701, by rfl⟩ : syracuseStep 9084935 = 13627403) B13627403
theorem B7184537 : Blo 944585 7184537 := bstep (se 2 (by rfl) ⟨2694201, by rfl⟩ : syracuseStep 7184537 = 5388403) B5388403
theorem B1417481 : Blo 944585 1417481 := bstep (se 2 (by rfl) ⟨531555, by rfl⟩ : syracuseStep 1417481 = 1063111) B1063111
theorem B1417583 : Blo 944585 1417583 := bstep (se 1 (by rfl) ⟨1063187, by rfl⟩ : syracuseStep 1417583 = 2126375) B2126375
theorem B1417799 : Blo 944585 1417799 := bstep (se 1 (by rfl) ⟨1063349, by rfl⟩ : syracuseStep 1417799 = 2126699) B2126699
theorem B2695751 : Blo 944585 2695751 := bstep (se 1 (by rfl) ⟨2021813, by rfl⟩ : syracuseStep 2695751 = 4043627) B4043627
theorem B6824519 : Blo 944585 6824519 := bstep (se 1 (by rfl) ⟨5118389, by rfl⟩ : syracuseStep 6824519 = 10236779) B10236779
theorem B1417835 : Blo 944585 1417835 := bstep (se 1 (by rfl) ⟨1063376, by rfl⟩ : syracuseStep 1417835 = 2126753) B2126753
theorem B4039321 : Blo 944585 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B2269919 : Blo 944585 2269919 := bstep (se 1 (by rfl) ⟨1702439, by rfl⟩ : syracuseStep 2269919 = 3404879) B3404879
theorem B1418063 : Blo 944585 1418063 := bstep (se 1 (by rfl) ⟨1063547, by rfl⟩ : syracuseStep 1418063 = 2127095) B2127095
theorem B2401103 : Blo 944585 2401103 := bstep (se 1 (by rfl) ⟨1800827, by rfl⟩ : syracuseStep 2401103 = 3601655) B3601655
theorem B6071233 : Blo 944585 6071233 := bstep (se 2 (by rfl) ⟨2276712, by rfl⟩ : syracuseStep 6071233 = 4553425) B4553425
theorem B69215269 : Blo 944585 69215269 := bstep (se 4 (by rfl) ⟨6488931, by rfl⟩ : syracuseStep 69215269 = 12977863) B12977863
theorem B1418459 : Blo 944585 1418459 := bstep (se 1 (by rfl) ⟨1063844, by rfl⟩ : syracuseStep 1418459 = 2127689) B2127689
theorem B2696435 : Blo 944585 2696435 := bstep (se 1 (by rfl) ⟨2022326, by rfl⟩ : syracuseStep 2696435 = 4044653) B4044653
theorem B1418633 : Blo 944585 1418633 := bstep (se 2 (by rfl) ⟨531987, by rfl⟩ : syracuseStep 1418633 = 1063975) B1063975
theorem B1418987 : Blo 944585 1418987 := bstep (se 1 (by rfl) ⟨1064240, by rfl⟩ : syracuseStep 1418987 = 2128481) B2128481
theorem B1419215 : Blo 944585 1419215 := bstep (se 1 (by rfl) ⟨1064411, by rfl⟩ : syracuseStep 1419215 = 2128823) B2128823
theorem B13117625 : Blo 944585 13117625 := bstep (se 2 (by rfl) ⟨4919109, by rfl⟩ : syracuseStep 13117625 = 9838219) B9838219
theorem B6072515 : Blo 944585 6072515 := bstep (se 1 (by rfl) ⟨4554386, by rfl⟩ : syracuseStep 6072515 = 9108773) B9108773
theorem B1419611 : Blo 944585 1419611 := bstep (se 1 (by rfl) ⟨1064708, by rfl⟩ : syracuseStep 1419611 = 2129417) B2129417
theorem B4794875 : Blo 944585 4794875 := bstep (se 1 (by rfl) ⟨3596156, by rfl⟩ : syracuseStep 4794875 = 7192313) B7192313
theorem B1419839 : Blo 944585 1419839 := bstep (se 1 (by rfl) ⟨1064879, by rfl⟩ : syracuseStep 1419839 = 2129759) B2129759
theorem B6826619 : Blo 944585 6826619 := bstep (se 1 (by rfl) ⟨5119964, by rfl⟩ : syracuseStep 6826619 = 10239929) B10239929
theorem B1419959 : Blo 944585 1419959 := bstep (se 1 (by rfl) ⟨1064969, by rfl⟩ : syracuseStep 1419959 = 2129939) B2129939
theorem B13642627 : Blo 944585 13642627 := bstep (se 1 (by rfl) ⟨10231970, by rfl⟩ : syracuseStep 13642627 = 20463941) B20463941
theorem B1420187 : Blo 944585 1420187 := bstep (se 1 (by rfl) ⟨1065140, by rfl⟩ : syracuseStep 1420187 = 2130281) B2130281
theorem B1420583 : Blo 944585 1420583 := bstep (se 1 (by rfl) ⟨1065437, by rfl⟩ : syracuseStep 1420583 = 2130875) B2130875
theorem B1420667 : Blo 944585 1420667 := bstep (se 1 (by rfl) ⟨1065500, by rfl⟩ : syracuseStep 1420667 = 2131001) B2131001
theorem B4795847 : Blo 944585 4795847 := bstep (se 1 (by rfl) ⟨3596885, by rfl⟩ : syracuseStep 4795847 = 7193771) B7193771
theorem B3190265 : Blo 944585 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B1420793 : Blo 944585 1420793 := bstep (se 2 (by rfl) ⟨532797, by rfl⟩ : syracuseStep 1420793 = 1065595) B1065595
theorem B1420895 : Blo 944585 1420895 := bstep (se 1 (by rfl) ⟨1065671, by rfl⟩ : syracuseStep 1420895 = 2131343) B2131343
theorem B15380077 : Blo 944585 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B3190535 : Blo 944585 3190535 := bstep (se 1 (by rfl) ⟨2392901, by rfl⟩ : syracuseStep 3190535 = 4785803) B4785803
theorem B4796171 : Blo 944585 4796171 := bstep (se 1 (by rfl) ⟨3597128, by rfl⟩ : syracuseStep 4796171 = 7194257) B7194257
theorem B1421111 : Blo 944585 1421111 := bstep (se 1 (by rfl) ⟨1065833, by rfl⟩ : syracuseStep 1421111 = 2131667) B2131667
theorem B3190589 : Blo 944585 3190589 := bstep (se 3 (by rfl) ⟨598235, by rfl⟩ : syracuseStep 3190589 = 1196471) B1196471
theorem B1421417 : Blo 944585 1421417 := bstep (se 2 (by rfl) ⟨533031, by rfl⟩ : syracuseStep 1421417 = 1066063) B1066063
theorem B2273609 : Blo 944585 2273609 := bstep (se 2 (by rfl) ⟨852603, by rfl⟩ : syracuseStep 2273609 = 1705207) B1705207
theorem B1421735 : Blo 944585 1421735 := bstep (se 1 (by rfl) ⟨1066301, by rfl⟩ : syracuseStep 1421735 = 2132603) B2132603
theorem B7188911 : Blo 944585 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B1421819 : Blo 944585 1421819 := bstep (se 1 (by rfl) ⟨1066364, by rfl⟩ : syracuseStep 1421819 = 2132729) B2132729
theorem B1421945 : Blo 944585 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1421999 : Blo 944585 1421999 := bstep (se 1 (by rfl) ⟨1066499, by rfl⟩ : syracuseStep 1421999 = 2132999) B2132999
theorem B4797143 : Blo 944585 4797143 := bstep (se 1 (by rfl) ⟨3597857, by rfl⟩ : syracuseStep 4797143 = 7195715) B7195715
theorem B1422047 : Blo 944585 1422047 := bstep (se 1 (by rfl) ⟨1066535, by rfl⟩ : syracuseStep 1422047 = 2133071) B2133071
theorem B1422311 : Blo 944585 1422311 := bstep (se 1 (by rfl) ⟨1066733, by rfl⟩ : syracuseStep 1422311 = 2133467) B2133467
theorem B1422569 : Blo 944585 1422569 := bstep (se 2 (by rfl) ⟨533463, by rfl⟩ : syracuseStep 1422569 = 1066927) B1066927
theorem B1422623 : Blo 944585 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B4797791 : Blo 944585 4797791 := bstep (se 1 (by rfl) ⟨3598343, by rfl⟩ : syracuseStep 4797791 = 7196687) B7196687
theorem B1422791 : Blo 944585 1422791 := bstep (se 1 (by rfl) ⟨1067093, by rfl⟩ : syracuseStep 1422791 = 2134187) B2134187
theorem B1063291 : Blo 944585 1063291 := bstep (se 1 (by rfl) ⟨797468, by rfl⟩ : syracuseStep 1063291 = 1594937) B1594937
theorem B8075771 : Blo 944585 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B3193451 : Blo 944585 3193451 := bstep (se 1 (by rfl) ⟨2395088, by rfl⟩ : syracuseStep 3193451 = 4790177) B4790177
theorem B1063759 : Blo 944585 1063759 := bstep (se 1 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 1063759 = 1595639) B1595639
theorem B19414181 : Blo 944585 19414181 := bstep (se 4 (by rfl) ⟨1820079, by rfl⟩ : syracuseStep 19414181 = 3640159) B3640159
theorem B3194045 : Blo 944585 3194045 := bstep (se 3 (by rfl) ⟨598883, by rfl⟩ : syracuseStep 3194045 = 1197767) B1197767
theorem B1064155 : Blo 944585 1064155 := bstep (se 1 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 1064155 = 1596233) B1596233
theorem B10796489 : Blo 944585 10796489 := bstep (se 2 (by rfl) ⟨4048683, by rfl⟩ : syracuseStep 10796489 = 8097367) B8097367
theorem B1064443 : Blo 944585 1064443 := bstep (se 1 (by rfl) ⟨798332, by rfl⟩ : syracuseStep 1064443 = 1596665) B1596665
theorem B4046345 : Blo 944585 4046345 := bstep (se 2 (by rfl) ⟨1517379, by rfl⟩ : syracuseStep 4046345 = 3034759) B3034759
theorem B4046395 : Blo 944585 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B4800059 : Blo 944585 4800059 := bstep (se 1 (by rfl) ⟨3600044, by rfl⟩ : syracuseStep 4800059 = 7200089) B7200089
theorem B1064623 : Blo 944585 1064623 := bstep (se 1 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 1064623 = 1596935) B1596935
theorem B8634071 : Blo 944585 8634071 := bstep (se 1 (by rfl) ⟨6475553, by rfl⟩ : syracuseStep 8634071 = 12951107) B12951107
theorem B1195823 : Blo 944585 1195823 := bstep (se 1 (by rfl) ⟨896867, by rfl⟩ : syracuseStep 1195823 = 1793735) B1793735
theorem B1064911 : Blo 944585 1064911 := bstep (se 1 (by rfl) ⟨798683, by rfl⟩ : syracuseStep 1064911 = 1597367) B1597367
theorem B5390387 : Blo 944585 5390387 := bstep (se 1 (by rfl) ⟨4042790, by rfl⟩ : syracuseStep 5390387 = 8085581) B8085581
theorem B1065307 : Blo 944585 1065307 := bstep (se 1 (by rfl) ⟨798980, by rfl⟩ : syracuseStep 1065307 = 1597961) B1597961
theorem B1065415 : Blo 944585 1065415 := bstep (se 1 (by rfl) ⟨799061, by rfl⟩ : syracuseStep 1065415 = 1598123) B1598123
theorem B6144457 : Blo 944585 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B7684753 : Blo 944585 7684753 := bstep (se 2 (by rfl) ⟨2881782, by rfl⟩ : syracuseStep 7684753 = 5763565) B5763565
theorem B1065775 : Blo 944585 1065775 := bstep (se 1 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 1065775 = 1598663) B1598663
theorem B12108689 : Blo 944585 12108689 := bstep (se 2 (by rfl) ⟨4540758, by rfl⟩ : syracuseStep 12108689 = 9081517) B9081517
theorem B1065883 : Blo 944585 1065883 := bstep (se 1 (by rfl) ⟨799412, by rfl⟩ : syracuseStep 1065883 = 1598825) B1598825
theorem B3589217 : Blo 944585 3589217 := bstep (se 2 (by rfl) ⟨1345956, by rfl⟩ : syracuseStep 3589217 = 2691913) B2691913
theorem B4801679 : Blo 944585 4801679 := bstep (se 1 (by rfl) ⟨3601259, by rfl⟩ : syracuseStep 4801679 = 7202519) B7202519
theorem B2278615 : Blo 944585 2278615 := bstep (se 1 (by rfl) ⟨1708961, by rfl⟩ : syracuseStep 2278615 = 3417923) B3417923
theorem B5391593 : Blo 944585 5391593 := bstep (se 2 (by rfl) ⟨2021847, by rfl⟩ : syracuseStep 5391593 = 4043695) B4043695
theorem B1066279 : Blo 944585 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B33637675 : Blo 944585 33637675 := bstep (se 1 (by rfl) ⟨25228256, by rfl⟩ : syracuseStep 33637675 = 50456513) B50456513
theorem B1066351 : Blo 944585 1066351 := bstep (se 1 (by rfl) ⟨799763, by rfl⟩ : syracuseStep 1066351 = 1599527) B1599527
theorem B16401977 : Blo 944585 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B1066567 : Blo 944585 1066567 := bstep (se 1 (by rfl) ⟨799925, by rfl⟩ : syracuseStep 1066567 = 1599851) B1599851
theorem B1820471 : Blo 944585 1820471 := bstep (se 1 (by rfl) ⟨1365353, by rfl⟩ : syracuseStep 1820471 = 2730707) B2730707
theorem B3196961 : Blo 944585 3196961 := bstep (se 2 (by rfl) ⟨1198860, by rfl⟩ : syracuseStep 3196961 = 2397721) B2397721
theorem B44222593 : Blo 944585 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B2017747 : Blo 944585 2017747 := bstep (se 1 (by rfl) ⟨1513310, by rfl⟩ : syracuseStep 2017747 = 3026621) B3026621
theorem B1919551 : Blo 944585 1919551 := bstep (se 1 (by rfl) ⟨1439663, by rfl⟩ : syracuseStep 1919551 = 2879327) B2879327
theorem B4541123 : Blo 944585 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B3033875 : Blo 944585 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B2018191 : Blo 944585 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B25873843 : Blo 944585 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B1199711 : Blo 944585 1199711 := bstep (se 1 (by rfl) ⟨899783, by rfl⟩ : syracuseStep 1199711 = 1799567) B1799567
theorem B7294637 : Blo 944585 7294637 := bstep (se 3 (by rfl) ⟨1367744, by rfl⟩ : syracuseStep 7294637 = 2735489) B2735489
theorem B1298651 : Blo 944585 1298651 := bstep (se 1 (by rfl) ⟨973988, by rfl⟩ : syracuseStep 1298651 = 1947977) B1947977
theorem B2019593 : Blo 944585 2019593 := bstep (se 2 (by rfl) ⟨757347, by rfl⟩ : syracuseStep 2019593 = 1514695) B1514695
theorem B1200415 : Blo 944585 1200415 := bstep (se 1 (by rfl) ⟨900311, by rfl⟩ : syracuseStep 1200415 = 1800623) B1800623
theorem B5394761 : Blo 944585 5394761 := bstep (se 2 (by rfl) ⟨2023035, by rfl⟩ : syracuseStep 5394761 = 4046071) B4046071
theorem B1594039 : Blo 944585 1594039 := bstep (se 1 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 1594039 = 2391059) B2391059
theorem B3199823 : Blo 944585 3199823 := bstep (se 1 (by rfl) ⟨2399867, by rfl⟩ : syracuseStep 3199823 = 4799735) B4799735
theorem B1594343 : Blo 944585 1594343 := bstep (se 1 (by rfl) ⟨1195757, by rfl⟩ : syracuseStep 1594343 = 2391515) B2391515
theorem B3200147 : Blo 944585 3200147 := bstep (se 1 (by rfl) ⟨2400110, by rfl⟩ : syracuseStep 3200147 = 4800221) B4800221
theorem B2020601 : Blo 944585 2020601 := bstep (se 2 (by rfl) ⟨757725, by rfl⟩ : syracuseStep 2020601 = 1515451) B1515451
theorem B1135963 : Blo 944585 1135963 := bstep (se 1 (by rfl) ⟨851972, by rfl⟩ : syracuseStep 1135963 = 1703945) B1703945
theorem B3200417 : Blo 944585 3200417 := bstep (se 2 (by rfl) ⟨1200156, by rfl⟩ : syracuseStep 3200417 = 2400313) B2400313
theorem B7198145 : Blo 944585 7198145 := bstep (se 2 (by rfl) ⟨2699304, by rfl⟩ : syracuseStep 7198145 = 5398609) B5398609
theorem B4544545 : Blo 944585 4544545 := bstep (se 2 (by rfl) ⟨1704204, by rfl⟩ : syracuseStep 4544545 = 3408409) B3408409
theorem B7297067 : Blo 944585 7297067 := bstep (se 1 (by rfl) ⟨5472800, by rfl⟩ : syracuseStep 7297067 = 10945601) B10945601
theorem B1595497 : Blo 944585 1595497 := bstep (se 2 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 1595497 = 1196623) B1196623
theorem B9099971 : Blo 944585 9099971 := bstep (se 1 (by rfl) ⟨6824978, by rfl⟩ : syracuseStep 9099971 = 13649957) B13649957
theorem B3038077 : Blo 944585 3038077 := bstep (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) B1139279
theorem B5462939 : Blo 944585 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B4545467 : Blo 944585 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B2022497 : Blo 944585 2022497 := bstep (se 2 (by rfl) ⟨758436, by rfl⟩ : syracuseStep 2022497 = 1516873) B1516873
theorem B9460925 : Blo 944585 9460925 := bstep (se 3 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 9460925 = 3547847) B3547847
theorem B1597225 : Blo 944585 1597225 := bstep (se 2 (by rfl) ⟨598959, by rfl⟩ : syracuseStep 1597225 = 1197919) B1197919
theorem B5758793 : Blo 944585 5758793 := bstep (se 2 (by rfl) ⟨2159547, by rfl⟩ : syracuseStep 5758793 = 4319095) B4319095
theorem B8184017 : Blo 944585 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B10936777 : Blo 944585 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B4547123 : Blo 944585 4547123 := bstep (se 1 (by rfl) ⟨3410342, by rfl⟩ : syracuseStep 4547123 = 6820685) B6820685
theorem B1598015 : Blo 944585 1598015 := bstep (se 1 (by rfl) ⟨1198511, by rfl⟩ : syracuseStep 1598015 = 2397023) B2397023
theorem B1794631 : Blo 944585 1794631 := bstep (se 1 (by rfl) ⟨1345973, by rfl⟩ : syracuseStep 1794631 = 2691947) B2691947
theorem B43803287 : Blo 944585 43803287 := bstep (se 1 (by rfl) ⟨32852465, by rfl⟩ : syracuseStep 43803287 = 65704931) B65704931
theorem B3237011 : Blo 944585 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B3237079 : Blo 944585 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B1598683 : Blo 944585 1598683 := bstep (se 1 (by rfl) ⟨1199012, by rfl⟩ : syracuseStep 1598683 = 2398025) B2398025
theorem B4547927 : Blo 944585 4547927 := bstep (se 1 (by rfl) ⟨3410945, by rfl⟩ : syracuseStep 4547927 = 6821891) B6821891
theorem B10249615 : Blo 944585 10249615 := bstep (se 1 (by rfl) ⟨7687211, by rfl⟩ : syracuseStep 10249615 = 15374423) B15374423
theorem B1009147 : Blo 944585 1009147 := bstep (se 1 (by rfl) ⟨756860, by rfl⟩ : syracuseStep 1009147 = 1513721) B1513721
theorem B1795679 : Blo 944585 1795679 := bstep (se 1 (by rfl) ⟨1346759, by rfl⟩ : syracuseStep 1795679 = 2693519) B2693519
theorem B1599439 : Blo 944585 1599439 := bstep (se 1 (by rfl) ⟨1199579, by rfl⟩ : syracuseStep 1599439 = 2399159) B2399159
theorem B31057901 : Blo 944585 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B3598465 : Blo 944585 3598465 := bstep (se 2 (by rfl) ⟨1349424, by rfl⟩ : syracuseStep 3598465 = 2698849) B2698849
theorem B13297955 : Blo 944585 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B944635 : Blo 944585 944635 := bstep (se 1 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 944635 = 1416953) B1416953
theorem B944703 : Blo 944585 944703 := bstep (se 1 (by rfl) ⟨708527, by rfl⟩ : syracuseStep 944703 = 1417055) B1417055
theorem B944711 : Blo 944585 944711 := bstep (se 1 (by rfl) ⟨708533, by rfl⟩ : syracuseStep 944711 = 1417067) B1417067
theorem B1796681 : Blo 944585 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1600121 : Blo 944585 1600121 := bstep (se 2 (by rfl) ⟨600045, by rfl⟩ : syracuseStep 1600121 = 1200091) B1200091
theorem B1600175 : Blo 944585 1600175 := bstep (se 1 (by rfl) ⟨1200131, by rfl⟩ : syracuseStep 1600175 = 2400263) B2400263
theorem B944863 : Blo 944585 944863 := bstep (se 1 (by rfl) ⟨708647, by rfl⟩ : syracuseStep 944863 = 1417295) B1417295
theorem B944943 : Blo 944585 944943 := bstep (se 1 (by rfl) ⟨708707, by rfl⟩ : syracuseStep 944943 = 1417415) B1417415
theorem B945051 : Blo 944585 945051 := bstep (se 1 (by rfl) ⟨708788, by rfl⟩ : syracuseStep 945051 = 1417577) B1417577
theorem B1600411 : Blo 944585 1600411 := bstep (se 1 (by rfl) ⟨1200308, by rfl⟩ : syracuseStep 1600411 = 2400617) B2400617
theorem B945103 : Blo 944585 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B945127 : Blo 944585 945127 := bstep (se 1 (by rfl) ⟨708845, by rfl⟩ : syracuseStep 945127 = 1417691) B1417691
theorem B6810763 : Blo 944585 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B6810911 : Blo 944585 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B945439 : Blo 944585 945439 := bstep (se 1 (by rfl) ⟨709079, by rfl⟩ : syracuseStep 945439 = 1418159) B1418159
theorem B1010975 : Blo 944585 1010975 := bstep (se 1 (by rfl) ⟨758231, by rfl⟩ : syracuseStep 1010975 = 1516463) B1516463
theorem B8088893 : Blo 944585 8088893 := bstep (se 3 (by rfl) ⟨1516667, by rfl⟩ : syracuseStep 8088893 = 3033335) B3033335
theorem B945499 : Blo 944585 945499 := bstep (se 1 (by rfl) ⟨709124, by rfl⟩ : syracuseStep 945499 = 1418249) B1418249
theorem B945519 : Blo 944585 945519 := bstep (se 1 (by rfl) ⟨709139, by rfl⟩ : syracuseStep 945519 = 1418279) B1418279
theorem B945575 : Blo 944585 945575 := bstep (se 1 (by rfl) ⟨709181, by rfl⟩ : syracuseStep 945575 = 1418363) B1418363
theorem B945659 : Blo 944585 945659 := bstep (se 1 (by rfl) ⟨709244, by rfl⟩ : syracuseStep 945659 = 1418489) B1418489
theorem B945727 : Blo 944585 945727 := bstep (se 1 (by rfl) ⟨709295, by rfl⟩ : syracuseStep 945727 = 1418591) B1418591
theorem B945735 : Blo 944585 945735 := bstep (se 1 (by rfl) ⟨709301, by rfl⟩ : syracuseStep 945735 = 1418603) B1418603
theorem B945887 : Blo 944585 945887 := bstep (se 1 (by rfl) ⟨709415, by rfl⟩ : syracuseStep 945887 = 1418831) B1418831
theorem B2125547 : Blo 944585 2125547 := bstep (se 1 (by rfl) ⟨1594160, by rfl⟩ : syracuseStep 2125547 = 3188321) B3188321
theorem B7663339 : Blo 944585 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B945967 : Blo 944585 945967 := bstep (se 1 (by rfl) ⟨709475, by rfl⟩ : syracuseStep 945967 = 1418951) B1418951
theorem B2125673 : Blo 944585 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B946075 : Blo 944585 946075 := bstep (se 1 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 946075 = 1419113) B1419113
theorem B946127 : Blo 944585 946127 := bstep (se 1 (by rfl) ⟨709595, by rfl⟩ : syracuseStep 946127 = 1419191) B1419191
theorem B946151 : Blo 944585 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B26570753 : Blo 944585 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B3600409 : Blo 944585 3600409 := bstep (se 2 (by rfl) ⟨1350153, by rfl⟩ : syracuseStep 3600409 = 2700307) B2700307
theorem B946463 : Blo 944585 946463 := bstep (se 1 (by rfl) ⟨709847, by rfl⟩ : syracuseStep 946463 = 1419695) B1419695
theorem B3600713 : Blo 944585 3600713 := bstep (se 2 (by rfl) ⟨1350267, by rfl⟩ : syracuseStep 3600713 = 2700535) B2700535
theorem B946523 : Blo 944585 946523 := bstep (se 1 (by rfl) ⟨709892, by rfl⟩ : syracuseStep 946523 = 1419785) B1419785
theorem B17985899 : Blo 944585 17985899 := bstep (se 1 (by rfl) ⟨13489424, by rfl⟩ : syracuseStep 17985899 = 26978849) B26978849
theorem B946543 : Blo 944585 946543 := bstep (se 1 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 946543 = 1419815) B1419815
theorem B946599 : Blo 944585 946599 := bstep (se 1 (by rfl) ⟨709949, by rfl⟩ : syracuseStep 946599 = 1419899) B1419899
theorem B18215387 : Blo 944585 18215387 := bstep (se 1 (by rfl) ⟨13661540, by rfl⟩ : syracuseStep 18215387 = 27323081) B27323081
theorem B1798625 : Blo 944585 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B946683 : Blo 944585 946683 := bstep (se 1 (by rfl) ⟨710012, by rfl⟩ : syracuseStep 946683 = 1420025) B1420025
theorem B946751 : Blo 944585 946751 := bstep (se 1 (by rfl) ⟨710063, by rfl⟩ : syracuseStep 946751 = 1420127) B1420127
theorem B946759 : Blo 944585 946759 := bstep (se 1 (by rfl) ⟨710069, by rfl⟩ : syracuseStep 946759 = 1420139) B1420139
theorem B1798777 : Blo 944585 1798777 := bstep (se 2 (by rfl) ⟨674541, by rfl⟩ : syracuseStep 1798777 = 1349083) B1349083
theorem B2126519 : Blo 944585 2126519 := bstep (se 1 (by rfl) ⟨1594889, by rfl⟩ : syracuseStep 2126519 = 3189779) B3189779
theorem B946911 : Blo 944585 946911 := bstep (se 1 (by rfl) ⟨710183, by rfl⟩ : syracuseStep 946911 = 1420367) B1420367
theorem B946991 : Blo 944585 946991 := bstep (se 1 (by rfl) ⟨710243, by rfl⟩ : syracuseStep 946991 = 1420487) B1420487
theorem B2126735 : Blo 944585 2126735 := bstep (se 1 (by rfl) ⟨1595051, by rfl⟩ : syracuseStep 2126735 = 3190103) B3190103
theorem B947099 : Blo 944585 947099 := bstep (se 1 (by rfl) ⟨710324, by rfl⟩ : syracuseStep 947099 = 1420649) B1420649
theorem B947151 : Blo 944585 947151 := bstep (se 1 (by rfl) ⟨710363, by rfl⟩ : syracuseStep 947151 = 1420727) B1420727
theorem B947175 : Blo 944585 947175 := bstep (se 1 (by rfl) ⟨710381, by rfl⟩ : syracuseStep 947175 = 1420763) B1420763
theorem B26277011 : Blo 944585 26277011 := bstep (se 1 (by rfl) ⟨19707758, by rfl⟩ : syracuseStep 26277011 = 39415517) B39415517
theorem B947487 : Blo 944585 947487 := bstep (se 1 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 947487 = 1421231) B1421231
theorem B947547 : Blo 944585 947547 := bstep (se 1 (by rfl) ⟨710660, by rfl⟩ : syracuseStep 947547 = 1421321) B1421321
theorem B5469545 : Blo 944585 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B947567 : Blo 944585 947567 := bstep (se 1 (by rfl) ⟨710675, by rfl⟩ : syracuseStep 947567 = 1421351) B1421351
theorem B947623 : Blo 944585 947623 := bstep (se 1 (by rfl) ⟨710717, by rfl⟩ : syracuseStep 947623 = 1421435) B1421435
theorem B947707 : Blo 944585 947707 := bstep (se 1 (by rfl) ⟨710780, by rfl⟩ : syracuseStep 947707 = 1421561) B1421561
theorem B947775 : Blo 944585 947775 := bstep (se 1 (by rfl) ⟨710831, by rfl⟩ : syracuseStep 947775 = 1421663) B1421663
theorem B947783 : Blo 944585 947783 := bstep (se 1 (by rfl) ⟨710837, by rfl⟩ : syracuseStep 947783 = 1421675) B1421675
theorem B2127455 : Blo 944585 2127455 := bstep (se 1 (by rfl) ⟨1595591, by rfl⟩ : syracuseStep 2127455 = 3191183) B3191183
theorem B947935 : Blo 944585 947935 := bstep (se 1 (by rfl) ⟨710951, by rfl⟩ : syracuseStep 947935 = 1421903) B1421903
theorem B1799977 : Blo 944585 1799977 := bstep (se 2 (by rfl) ⟨674991, by rfl⟩ : syracuseStep 1799977 = 1349983) B1349983
theorem B948015 : Blo 944585 948015 := bstep (se 1 (by rfl) ⟨711011, by rfl⟩ : syracuseStep 948015 = 1422023) B1422023
theorem B2127671 : Blo 944585 2127671 := bstep (se 1 (by rfl) ⟨1595753, by rfl⟩ : syracuseStep 2127671 = 3191507) B3191507
theorem B23000921 : Blo 944585 23000921 := bstep (se 2 (by rfl) ⟨8625345, by rfl⟩ : syracuseStep 23000921 = 17250691) B17250691
theorem B948123 : Blo 944585 948123 := bstep (se 1 (by rfl) ⟨711092, by rfl⟩ : syracuseStep 948123 = 1422185) B1422185
theorem B9107387 : Blo 944585 9107387 := bstep (se 1 (by rfl) ⟨6830540, by rfl⟩ : syracuseStep 9107387 = 13661081) B13661081
theorem B948175 : Blo 944585 948175 := bstep (se 1 (by rfl) ⟨711131, by rfl⟩ : syracuseStep 948175 = 1422263) B1422263
theorem B948199 : Blo 944585 948199 := bstep (se 1 (by rfl) ⟨711149, by rfl⟩ : syracuseStep 948199 = 1422299) B1422299
theorem B76904549 : Blo 944585 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B2127977 : Blo 944585 2127977 := bstep (se 2 (by rfl) ⟨797991, by rfl⟩ : syracuseStep 2127977 = 1595983) B1595983
theorem B948511 : Blo 944585 948511 := bstep (se 1 (by rfl) ⟨711383, by rfl⟩ : syracuseStep 948511 = 1422767) B1422767
theorem B1800539 : Blo 944585 1800539 := bstep (se 1 (by rfl) ⟨1350404, by rfl⟩ : syracuseStep 1800539 = 2700809) B2700809
theorem B948571 : Blo 944585 948571 := bstep (se 1 (by rfl) ⟨711428, by rfl⟩ : syracuseStep 948571 = 1422857) B1422857
theorem B15366581 : Blo 944585 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B1800767 : Blo 944585 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B2128463 : Blo 944585 2128463 := bstep (se 1 (by rfl) ⟨1596347, by rfl⟩ : syracuseStep 2128463 = 3192695) B3192695
theorem B2128607 : Blo 944585 2128607 := bstep (se 1 (by rfl) ⟨1596455, by rfl⟩ : syracuseStep 2128607 = 3192911) B3192911
theorem B5831443 : Blo 944585 5831443 := bstep (se 1 (by rfl) ⟨4373582, by rfl⟩ : syracuseStep 5831443 = 8747165) B8747165
theorem B6486803 : Blo 944585 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B20446127 : Blo 944585 20446127 := bstep (se 1 (by rfl) ⟨15334595, by rfl⟩ : syracuseStep 20446127 = 30669191) B30669191
theorem B2128859 : Blo 944585 2128859 := bstep (se 1 (by rfl) ⟨1596644, by rfl⟩ : syracuseStep 2128859 = 3193289) B3193289
theorem B2391079 : Blo 944585 2391079 := bstep (se 1 (by rfl) ⟨1793309, by rfl⟩ : syracuseStep 2391079 = 3586619) B3586619
theorem B2129039 : Blo 944585 2129039 := bstep (se 1 (by rfl) ⟨1596779, by rfl⟩ : syracuseStep 2129039 = 3193559) B3193559
theorem B2129129 : Blo 944585 2129129 := bstep (se 2 (by rfl) ⟨798423, by rfl⟩ : syracuseStep 2129129 = 1596847) B1596847
theorem B2129183 : Blo 944585 2129183 := bstep (se 1 (by rfl) ⟨1596887, by rfl⟩ : syracuseStep 2129183 = 3193775) B3193775
theorem B18414985 : Blo 944585 18414985 := bstep (se 2 (by rfl) ⟨6905619, by rfl⟩ : syracuseStep 18414985 = 13811239) B13811239
theorem B2391545 : Blo 944585 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B4783697 : Blo 944585 4783697 := bstep (se 2 (by rfl) ⟨1793886, by rfl⟩ : syracuseStep 4783697 = 3587773) B3587773
theorem B8093267 : Blo 944585 8093267 := bstep (se 1 (by rfl) ⟨6069950, by rfl⟩ : syracuseStep 8093267 = 12139901) B12139901
theorem B1212079 : Blo 944585 1212079 := bstep (se 1 (by rfl) ⟨909059, by rfl⟩ : syracuseStep 1212079 = 1818119) B1818119
theorem B23363261 : Blo 944585 23363261 := bstep (se 3 (by rfl) ⟨4380611, by rfl⟩ : syracuseStep 23363261 = 8761223) B8761223
theorem B2129705 : Blo 944585 2129705 := bstep (se 2 (by rfl) ⟨798639, by rfl⟩ : syracuseStep 2129705 = 1597279) B1597279
theorem B3080231 : Blo 944585 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B4260347 : Blo 944585 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B8192609 : Blo 944585 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B14582369 : Blo 944585 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B2392811 : Blo 944585 2392811 := bstep (se 1 (by rfl) ⟨1794608, by rfl⟩ : syracuseStep 2392811 = 3589217) B3589217
theorem B2884349 : Blo 944585 2884349 := bstep (se 3 (by rfl) ⟨540815, by rfl⟩ : syracuseStep 2884349 = 1081631) B1081631
theorem B2392841 : Blo 944585 2392841 := bstep (se 2 (by rfl) ⟨897315, by rfl⟩ : syracuseStep 2392841 = 1794631) B1794631
theorem B6062957 : Blo 944585 6062957 := bstep (se 3 (by rfl) ⟨1136804, by rfl⟩ : syracuseStep 6062957 = 2273609) B2273609
theorem B8094977 : Blo 944585 8094977 := bstep (se 2 (by rfl) ⟨3035616, by rfl⟩ : syracuseStep 8094977 = 6071233) B6071233
theorem B2131307 : Blo 944585 2131307 := bstep (se 1 (by rfl) ⟨1598480, by rfl⟩ : syracuseStep 2131307 = 3196961) B3196961
theorem B1705387 : Blo 944585 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B2131577 : Blo 944585 2131577 := bstep (se 2 (by rfl) ⟨799341, by rfl⟩ : syracuseStep 2131577 = 1598683) B1598683
theorem B517998329 : Blo 944585 517998329 := bstep (se 2 (by rfl) ⟨194249373, by rfl⟩ : syracuseStep 517998329 = 388498747) B388498747
theorem B13666153 : Blo 944585 13666153 := bstep (se 2 (by rfl) ⟨5124807, by rfl⟩ : syracuseStep 13666153 = 10249615) B10249615
theorem B1345529 : Blo 944585 1345529 := bstep (se 2 (by rfl) ⟨504573, by rfl⟩ : syracuseStep 1345529 = 1009147) B1009147
theorem B2132585 : Blo 944585 2132585 := bstep (se 2 (by rfl) ⟨799719, by rfl⟩ : syracuseStep 2132585 = 1599439) B1599439
theorem B6818519 : Blo 944585 6818519 := bstep (se 1 (by rfl) ⟨5113889, by rfl⟩ : syracuseStep 6818519 = 10227779) B10227779
theorem B1346395 : Blo 944585 1346395 := bstep (se 1 (by rfl) ⟨1009796, by rfl⟩ : syracuseStep 1346395 = 2019593) B2019593
theorem B2559023 : Blo 944585 2559023 := bstep (se 1 (by rfl) ⟨1919267, by rfl⟩ : syracuseStep 2559023 = 3838535) B3838535
theorem B4787423 : Blo 944585 4787423 := bstep (se 1 (by rfl) ⟨3590567, by rfl⟩ : syracuseStep 4787423 = 7181135) B7181135
theorem B2133215 : Blo 944585 2133215 := bstep (se 1 (by rfl) ⟨1599911, by rfl⟩ : syracuseStep 2133215 = 3199823) B3199823
theorem B8752357 : Blo 944585 8752357 := bstep (se 4 (by rfl) ⟨820533, by rfl⟩ : syracuseStep 8752357 = 1641067) B1641067
theorem B2690329 : Blo 944585 2690329 := bstep (se 2 (by rfl) ⟨1008873, by rfl⟩ : syracuseStep 2690329 = 2017747) B2017747
theorem B2559401 : Blo 944585 2559401 := bstep (se 2 (by rfl) ⟨959775, by rfl⟩ : syracuseStep 2559401 = 1919551) B1919551
theorem B2133431 : Blo 944585 2133431 := bstep (se 1 (by rfl) ⟨1600073, by rfl⟩ : syracuseStep 2133431 = 3200147) B3200147
theorem B1347067 : Blo 944585 1347067 := bstep (se 1 (by rfl) ⟨1010300, by rfl⟩ : syracuseStep 1347067 = 2020601) B2020601
theorem B12127805 : Blo 944585 12127805 := bstep (se 3 (by rfl) ⟨2273963, by rfl⟩ : syracuseStep 12127805 = 4547927) B4547927
theorem B2133611 : Blo 944585 2133611 := bstep (se 1 (by rfl) ⟨1600208, by rfl⟩ : syracuseStep 2133611 = 3200417) B3200417
theorem B14585453 : Blo 944585 14585453 := bstep (se 3 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 14585453 = 5469545) B5469545
theorem B18190169 : Blo 944585 18190169 := bstep (se 2 (by rfl) ⟨6821313, by rfl⟩ : syracuseStep 18190169 = 13642627) B13642627
theorem B2690921 : Blo 944585 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B2133881 : Blo 944585 2133881 := bstep (se 2 (by rfl) ⟨800205, by rfl⟩ : syracuseStep 2133881 = 1600411) B1600411
theorem B9081017 : Blo 944585 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B6066647 : Blo 944585 6066647 := bstep (se 1 (by rfl) ⟨4549985, by rfl⟩ : syracuseStep 6066647 = 9099971) B9099971
theorem B3641959 : Blo 944585 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B1348331 : Blo 944585 1348331 := bstep (se 1 (by rfl) ⟨1011248, by rfl⟩ : syracuseStep 1348331 = 2022497) B2022497
theorem B1708847 : Blo 944585 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B4854589 : Blo 944585 4854589 := bstep (se 3 (by rfl) ⟨910235, by rfl⟩ : syracuseStep 4854589 = 1820471) B1820471
theorem B3839195 : Blo 944585 3839195 := bstep (se 1 (by rfl) ⟨2879396, by rfl⟩ : syracuseStep 3839195 = 5758793) B5758793
theorem B4789691 : Blo 944585 4789691 := bstep (se 1 (by rfl) ⟨3592268, by rfl⟩ : syracuseStep 4789691 = 7184537) B7184537
theorem B29202191 : Blo 944585 29202191 := bstep (se 1 (by rfl) ⟨21901643, by rfl⟩ : syracuseStep 29202191 = 43803287) B43803287
theorem B1513279 : Blo 944585 1513279 := bstep (se 1 (by rfl) ⟨1134959, by rfl⟩ : syracuseStep 1513279 = 2269919) B2269919
theorem B2398369 : Blo 944585 2398369 := bstep (se 2 (by rfl) ⟨899388, by rfl⟩ : syracuseStep 2398369 = 1798777) B1798777
theorem B4791149 : Blo 944585 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B2399969 : Blo 944585 2399969 := bstep (se 2 (by rfl) ⟨899988, by rfl⟩ : syracuseStep 2399969 = 1799977) B1799977
theorem B1417031 : Blo 944585 1417031 := bstep (se 1 (by rfl) ⟨1062773, by rfl⟩ : syracuseStep 1417031 = 2125547) B2125547
theorem B1417115 : Blo 944585 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B2400475 : Blo 944585 2400475 := bstep (se 1 (by rfl) ⟨1800356, by rfl⟩ : syracuseStep 2400475 = 3600713) B3600713
theorem B4792607 : Blo 944585 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B1417679 : Blo 944585 1417679 := bstep (se 1 (by rfl) ⟨1063259, by rfl⟩ : syracuseStep 1417679 = 2126519) B2126519
theorem B1417721 : Blo 944585 1417721 := bstep (se 2 (by rfl) ⟨531645, by rfl⟩ : syracuseStep 1417721 = 1063291) B1063291
theorem B1417823 : Blo 944585 1417823 := bstep (se 1 (by rfl) ⟨1063367, by rfl⟩ : syracuseStep 1417823 = 2126735) B2126735
theorem B2695933 : Blo 944585 2695933 := bstep (se 3 (by rfl) ⟨505487, by rfl⟩ : syracuseStep 2695933 = 1010975) B1010975
theorem B7775257 : Blo 944585 7775257 := bstep (se 2 (by rfl) ⟨2915721, by rfl⟩ : syracuseStep 7775257 = 5831443) B5831443
theorem B1418303 : Blo 944585 1418303 := bstep (se 1 (by rfl) ⟨1063727, by rfl⟩ : syracuseStep 1418303 = 2127455) B2127455
theorem B1418345 : Blo 944585 1418345 := bstep (se 2 (by rfl) ⟨531879, by rfl⟩ : syracuseStep 1418345 = 1063759) B1063759
theorem B1418447 : Blo 944585 1418447 := bstep (se 1 (by rfl) ⟨1063835, by rfl⟩ : syracuseStep 1418447 = 2127671) B2127671
theorem B6071591 : Blo 944585 6071591 := bstep (se 1 (by rfl) ⟨4553693, by rfl⟩ : syracuseStep 6071591 = 9107387) B9107387
theorem B5383529 : Blo 944585 5383529 := bstep (se 2 (by rfl) ⟨2018823, by rfl⟩ : syracuseStep 5383529 = 4037647) B4037647
theorem B3188105 : Blo 944585 3188105 := bstep (se 2 (by rfl) ⟨1195539, by rfl⟩ : syracuseStep 3188105 = 2391079) B2391079
theorem B1418651 : Blo 944585 1418651 := bstep (se 1 (by rfl) ⟨1063988, by rfl⟩ : syracuseStep 1418651 = 2127977) B2127977
theorem B6563321 : Blo 944585 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B1418873 : Blo 944585 1418873 := bstep (se 2 (by rfl) ⟨532077, by rfl⟩ : syracuseStep 1418873 = 1064155) B1064155
theorem B5383847 : Blo 944585 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B1418975 : Blo 944585 1418975 := bstep (se 1 (by rfl) ⟨1064231, by rfl⟩ : syracuseStep 1418975 = 2128463) B2128463
theorem B1419071 : Blo 944585 1419071 := bstep (se 1 (by rfl) ⟨1064303, by rfl⟩ : syracuseStep 1419071 = 2128607) B2128607
theorem B24553313 : Blo 944585 24553313 := bstep (se 2 (by rfl) ⟨9207492, by rfl⟩ : syracuseStep 24553313 = 18414985) B18414985
theorem B1419239 : Blo 944585 1419239 := bstep (se 1 (by rfl) ⟨1064429, by rfl⟩ : syracuseStep 1419239 = 2128859) B2128859
theorem B1419257 : Blo 944585 1419257 := bstep (se 2 (by rfl) ⟨532221, by rfl⟩ : syracuseStep 1419257 = 1064443) B1064443
theorem B1419359 : Blo 944585 1419359 := bstep (se 1 (by rfl) ⟨1064519, by rfl⟩ : syracuseStep 1419359 = 2129039) B2129039
theorem B3188861 : Blo 944585 3188861 := bstep (se 3 (by rfl) ⟨597911, by rfl⟩ : syracuseStep 3188861 = 1195823) B1195823
theorem B4991129 : Blo 944585 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B1419419 : Blo 944585 1419419 := bstep (se 1 (by rfl) ⟨1064564, by rfl⟩ : syracuseStep 1419419 = 2129129) B2129129
theorem B1419455 : Blo 944585 1419455 := bstep (se 1 (by rfl) ⟨1064591, by rfl⟩ : syracuseStep 1419455 = 2129183) B2129183
theorem B1616105 : Blo 944585 1616105 := bstep (se 2 (by rfl) ⟨606039, by rfl⟩ : syracuseStep 1616105 = 1212079) B1212079
theorem B1419497 : Blo 944585 1419497 := bstep (se 2 (by rfl) ⟨532311, by rfl⟩ : syracuseStep 1419497 = 1064623) B1064623
theorem B2697563 : Blo 944585 2697563 := bstep (se 1 (by rfl) ⟨2023172, by rfl⟩ : syracuseStep 2697563 = 4046345) B4046345
theorem B3189131 : Blo 944585 3189131 := bstep (se 1 (by rfl) ⟨2391848, by rfl⟩ : syracuseStep 3189131 = 4783697) B4783697
theorem B15575507 : Blo 944585 15575507 := bstep (se 1 (by rfl) ⟨11681630, by rfl⟩ : syracuseStep 15575507 = 23363261) B23363261
theorem B1419803 : Blo 944585 1419803 := bstep (se 1 (by rfl) ⟨1064852, by rfl⟩ : syracuseStep 1419803 = 2129705) B2129705
theorem B1419881 : Blo 944585 1419881 := bstep (se 2 (by rfl) ⟨532455, by rfl⟩ : syracuseStep 1419881 = 1064911) B1064911
theorem B6073231 : Blo 944585 6073231 := bstep (se 1 (by rfl) ⟨4554923, by rfl⟩ : syracuseStep 6073231 = 9109847) B9109847
theorem B1420409 : Blo 944585 1420409 := bstep (se 2 (by rfl) ⟨532653, by rfl⟩ : syracuseStep 1420409 = 1065307) B1065307
theorem B1420511 : Blo 944585 1420511 := bstep (se 1 (by rfl) ⟨1065383, by rfl⟩ : syracuseStep 1420511 = 2130767) B2130767
theorem B1420553 : Blo 944585 1420553 := bstep (se 2 (by rfl) ⟨532707, by rfl⟩ : syracuseStep 1420553 = 1065415) B1065415
theorem B8072459 : Blo 944585 8072459 := bstep (se 1 (by rfl) ⟨6054344, by rfl⟩ : syracuseStep 8072459 = 12108689) B12108689
theorem B1420655 : Blo 944585 1420655 := bstep (se 1 (by rfl) ⟨1065491, by rfl⟩ : syracuseStep 1420655 = 2130983) B2130983
theorem B1420775 : Blo 944585 1420775 := bstep (se 1 (by rfl) ⟨1065581, by rfl⟩ : syracuseStep 1420775 = 2131163) B2131163
theorem B5385761 : Blo 944585 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B1420907 : Blo 944585 1420907 := bstep (se 1 (by rfl) ⟨1065680, by rfl⟩ : syracuseStep 1420907 = 2131361) B2131361
theorem B1421033 : Blo 944585 1421033 := bstep (se 2 (by rfl) ⟨532887, by rfl⟩ : syracuseStep 1421033 = 1065775) B1065775
theorem B1421177 : Blo 944585 1421177 := bstep (se 2 (by rfl) ⟨532941, by rfl⟩ : syracuseStep 1421177 = 1065883) B1065883
theorem B4796333 : Blo 944585 4796333 := bstep (se 3 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 4796333 = 1798625) B1798625
theorem B3190751 : Blo 944585 3190751 := bstep (se 1 (by rfl) ⟨2393063, by rfl⟩ : syracuseStep 3190751 = 4786127) B4786127
theorem B1421279 : Blo 944585 1421279 := bstep (se 1 (by rfl) ⟨1065959, by rfl⟩ : syracuseStep 1421279 = 2131919) B2131919
theorem B92287025 : Blo 944585 92287025 := bstep (se 2 (by rfl) ⟨34607634, by rfl⟩ : syracuseStep 92287025 = 69215269) B69215269
theorem B3190913 : Blo 944585 3190913 := bstep (se 2 (by rfl) ⟨1196592, by rfl⟩ : syracuseStep 3190913 = 2393185) B2393185
theorem B1421531 : Blo 944585 1421531 := bstep (se 1 (by rfl) ⟨1066148, by rfl⟩ : syracuseStep 1421531 = 2132297) B2132297
theorem B1421543 : Blo 944585 1421543 := bstep (se 1 (by rfl) ⟨1066157, by rfl⟩ : syracuseStep 1421543 = 2132315) B2132315
theorem B1421705 : Blo 944585 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B1421801 : Blo 944585 1421801 := bstep (se 2 (by rfl) ⟨533175, by rfl⟩ : syracuseStep 1421801 = 1066351) B1066351
theorem B3191399 : Blo 944585 3191399 := bstep (se 1 (by rfl) ⟨2393549, by rfl⟩ : syracuseStep 3191399 = 4787099) B4787099
theorem B1421927 : Blo 944585 1421927 := bstep (se 1 (by rfl) ⟨1066445, by rfl⟩ : syracuseStep 1421927 = 2132891) B2132891
theorem B1422059 : Blo 944585 1422059 := bstep (se 1 (by rfl) ⟨1066544, by rfl⟩ : syracuseStep 1422059 = 2133089) B2133089
theorem B1422089 : Blo 944585 1422089 := bstep (se 2 (by rfl) ⟨533283, by rfl⟩ : syracuseStep 1422089 = 1066567) B1066567
theorem B1422191 : Blo 944585 1422191 := bstep (se 1 (by rfl) ⟨1066643, by rfl⟩ : syracuseStep 1422191 = 2133287) B2133287
theorem B3191723 : Blo 944585 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1422443 : Blo 944585 1422443 := bstep (se 1 (by rfl) ⟨1066832, by rfl⟩ : syracuseStep 1422443 = 2133665) B2133665
theorem B4863091 : Blo 944585 4863091 := bstep (se 1 (by rfl) ⟨3647318, by rfl⟩ : syracuseStep 4863091 = 7294637) B7294637
theorem B3192155 : Blo 944585 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B1422683 : Blo 944585 1422683 := bstep (se 1 (by rfl) ⟨1067012, by rfl⟩ : syracuseStep 1422683 = 2134025) B2134025
theorem B7189883 : Blo 944585 7189883 := bstep (se 1 (by rfl) ⟨5392412, by rfl⟩ : syracuseStep 7189883 = 10784825) B10784825
theorem B3192263 : Blo 944585 3192263 := bstep (se 1 (by rfl) ⟨2394197, by rfl⟩ : syracuseStep 3192263 = 4788395) B4788395
theorem B58963457 : Blo 944585 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B4797953 : Blo 944585 4797953 := bstep (se 2 (by rfl) ⟨1799232, by rfl⟩ : syracuseStep 4797953 = 3598465) B3598465
theorem B2274887 : Blo 944585 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B3192587 : Blo 944585 3192587 := bstep (se 1 (by rfl) ⟨2394440, by rfl⟩ : syracuseStep 3192587 = 4788881) B4788881
theorem B6928175 : Blo 944585 6928175 := bstep (se 1 (by rfl) ⟨5196131, by rfl⟩ : syracuseStep 6928175 = 10392263) B10392263
theorem B1062895 : Blo 944585 1062895 := bstep (se 1 (by rfl) ⟨797171, by rfl⟩ : syracuseStep 1062895 = 1594343) B1594343
theorem B3192857 : Blo 944585 3192857 := bstep (se 2 (by rfl) ⟨1197321, by rfl⟩ : syracuseStep 3192857 = 2394643) B2394643
theorem B4798763 : Blo 944585 4798763 := bstep (se 1 (by rfl) ⟨3599072, by rfl⟩ : syracuseStep 4798763 = 7198145) B7198145
theorem B4864711 : Blo 944585 4864711 := bstep (se 1 (by rfl) ⟨3648533, by rfl⟩ : syracuseStep 4864711 = 7297067) B7297067
theorem B3030311 : Blo 944585 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B3194207 : Blo 944585 3194207 := bstep (se 1 (by rfl) ⟨2395655, by rfl⟩ : syracuseStep 3194207 = 4791311) B4791311
theorem B6307283 : Blo 944585 6307283 := bstep (se 1 (by rfl) ⟨4730462, by rfl⟩ : syracuseStep 6307283 = 9460925) B9460925
theorem B3587591 : Blo 944585 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B3194747 : Blo 944585 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B4800545 : Blo 944585 4800545 := bstep (se 2 (by rfl) ⟨1800204, by rfl⟩ : syracuseStep 4800545 = 3600409) B3600409
theorem B5456011 : Blo 944585 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B3195233 : Blo 944585 3195233 := bstep (se 2 (by rfl) ⟨1198212, by rfl⟩ : syracuseStep 3195233 = 2396425) B2396425
theorem B3031415 : Blo 944585 3031415 := bstep (se 1 (by rfl) ⟨2273561, by rfl⟩ : syracuseStep 3031415 = 4547123) B4547123
theorem B1065343 : Blo 944585 1065343 := bstep (se 1 (by rfl) ⟨799007, by rfl⟩ : syracuseStep 1065343 = 1598015) B1598015
theorem B1197119 : Blo 944585 1197119 := bstep (se 1 (by rfl) ⟨897839, by rfl⟩ : syracuseStep 1197119 = 1795679) B1795679
theorem B4048343 : Blo 944585 4048343 := bstep (se 1 (by rfl) ⟨3036257, by rfl⟩ : syracuseStep 4048343 = 6072515) B6072515
theorem B3196583 : Blo 944585 3196583 := bstep (se 1 (by rfl) ⟨2397437, by rfl⟩ : syracuseStep 3196583 = 4794875) B4794875
theorem B1066747 : Blo 944585 1066747 := bstep (se 1 (by rfl) ⟨800060, by rfl⟩ : syracuseStep 1066747 = 1600121) B1600121
theorem B1066783 : Blo 944585 1066783 := bstep (se 1 (by rfl) ⟨800087, by rfl⟩ : syracuseStep 1066783 = 1600175) B1600175
theorem B12109661 : Blo 944585 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B4540607 : Blo 944585 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B5392595 : Blo 944585 5392595 := bstep (se 1 (by rfl) ⟨4044446, by rfl⟩ : syracuseStep 5392595 = 8088893) B8088893
theorem B3197177 : Blo 944585 3197177 := bstep (se 2 (by rfl) ⟨1198941, by rfl⟩ : syracuseStep 3197177 = 2397883) B2397883
theorem B3197231 : Blo 944585 3197231 := bstep (se 1 (by rfl) ⟨2397923, by rfl⟩ : syracuseStep 3197231 = 4795847) B4795847
theorem B3197447 : Blo 944585 3197447 := bstep (se 1 (by rfl) ⟨2398085, by rfl⟩ : syracuseStep 3197447 = 4796171) B4796171
theorem B17713835 : Blo 944585 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B12143591 : Blo 944585 12143591 := bstep (se 1 (by rfl) ⟨9107693, by rfl⟩ : syracuseStep 12143591 = 18215387) B18215387
theorem B3198095 : Blo 944585 3198095 := bstep (se 1 (by rfl) ⟨2398571, by rfl⟩ : syracuseStep 3198095 = 4797143) B4797143
theorem B3591449 : Blo 944585 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B17518007 : Blo 944585 17518007 := bstep (se 1 (by rfl) ⟨13138505, by rfl⟩ : syracuseStep 17518007 = 26277011) B26277011
theorem B3198527 : Blo 944585 3198527 := bstep (se 1 (by rfl) ⟨2398895, by rfl⟩ : syracuseStep 3198527 = 4797791) B4797791
theorem B4050769 : Blo 944585 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B51269699 : Blo 944585 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B1200359 : Blo 944585 1200359 := bstep (se 1 (by rfl) ⟨900269, by rfl⟩ : syracuseStep 1200359 = 1800539) B1800539
theorem B3199229 : Blo 944585 3199229 := bstep (se 3 (by rfl) ⟨599855, by rfl⟩ : syracuseStep 3199229 = 1199711) B1199711
theorem B10244387 : Blo 944585 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B1200511 : Blo 944585 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B6836653 : Blo 944585 6836653 := bstep (se 3 (by rfl) ⟨1281872, by rfl⟩ : syracuseStep 6836653 = 2563745) B2563745
theorem B23024189 : Blo 944585 23024189 := bstep (se 3 (by rfl) ⟨4317035, by rfl⟩ : syracuseStep 23024189 = 8634071) B8634071
theorem B5395193 : Blo 944585 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B3199769 : Blo 944585 3199769 := bstep (se 2 (by rfl) ⟨1199913, by rfl⟩ : syracuseStep 3199769 = 2399827) B2399827
theorem B7197659 : Blo 944585 7197659 := bstep (se 1 (by rfl) ⟨5398244, by rfl⟩ : syracuseStep 7197659 = 10796489) B10796489
theorem B1594363 : Blo 944585 1594363 := bstep (se 1 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 1594363 = 2391545) B2391545
theorem B3200039 : Blo 944585 3200039 := bstep (se 1 (by rfl) ⟨2400029, by rfl⟩ : syracuseStep 3200039 = 4800059) B4800059
theorem B5395511 : Blo 944585 5395511 := bstep (se 1 (by rfl) ⟨4046633, by rfl⟩ : syracuseStep 5395511 = 8093267) B8093267
theorem B3593591 : Blo 944585 3593591 := bstep (se 1 (by rfl) ⟨2695193, by rfl⟩ : syracuseStep 3593591 = 5390387) B5390387
theorem B1594795 : Blo 944585 1594795 := bstep (se 1 (by rfl) ⟨1196096, by rfl⟩ : syracuseStep 1594795 = 2392193) B2392193
theorem B1594991 : Blo 944585 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B15357559 : Blo 944585 15357559 := bstep (se 1 (by rfl) ⟨11518169, by rfl⟩ : syracuseStep 15357559 = 23036339) B23036339
theorem B1595099 : Blo 944585 1595099 := bstep (se 1 (by rfl) ⟨1196324, by rfl⟩ : syracuseStep 1595099 = 2392649) B2392649
theorem B3463069 : Blo 944585 3463069 := bstep (se 3 (by rfl) ⟨649325, by rfl⟩ : syracuseStep 3463069 = 1298651) B1298651
theorem B1595335 : Blo 944585 1595335 := bstep (se 1 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 1595335 = 2393003) B2393003
theorem B3201119 : Blo 944585 3201119 := bstep (se 1 (by rfl) ⟨2400839, by rfl⟩ : syracuseStep 3201119 = 4801679) B4801679
theorem B3594395 : Blo 944585 3594395 := bstep (se 1 (by rfl) ⟨2695796, by rfl⟩ : syracuseStep 3594395 = 5391593) B5391593
theorem B10246337 : Blo 944585 10246337 := bstep (se 2 (by rfl) ⟨3842376, by rfl⟩ : syracuseStep 10246337 = 7684753) B7684753
theorem B47962397 : Blo 944585 47962397 := bstep (se 3 (by rfl) ⟨8992949, by rfl⟩ : syracuseStep 47962397 = 17985899) B17985899
theorem B10934651 : Blo 944585 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B1596091 : Blo 944585 1596091 := bstep (se 1 (by rfl) ⟨1197068, by rfl⟩ : syracuseStep 1596091 = 2394137) B2394137
theorem B4316105 : Blo 944585 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B3038153 : Blo 944585 3038153 := bstep (se 2 (by rfl) ⟨1139307, by rfl⟩ : syracuseStep 3038153 = 2278615) B2278615
theorem B1596395 : Blo 944585 1596395 := bstep (se 1 (by rfl) ⟨1197296, by rfl⟩ : syracuseStep 1596395 = 2394593) B2394593
theorem B44850233 : Blo 944585 44850233 := bstep (se 2 (by rfl) ⟨16818837, by rfl⟩ : syracuseStep 44850233 = 33637675) B33637675
theorem B2022583 : Blo 944585 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B11492675 : Blo 944585 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B1793963 : Blo 944585 1793963 := bstep (se 1 (by rfl) ⟨1345472, by rfl⟩ : syracuseStep 1793963 = 2690945) B2690945
theorem B3596507 : Blo 944585 3596507 := bstep (se 1 (by rfl) ⟨2697380, by rfl⟩ : syracuseStep 3596507 = 5394761) B5394761
theorem B141844853 : Blo 944585 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B7889683 : Blo 944585 7889683 := bstep (se 1 (by rfl) ⟨5917262, by rfl⟩ : syracuseStep 7889683 = 11834525) B11834525
theorem B1008703 : Blo 944585 1008703 := bstep (se 1 (by rfl) ⟨756527, by rfl⟩ : syracuseStep 1008703 = 1513055) B1513055
theorem B21849155 : Blo 944585 21849155 := bstep (se 1 (by rfl) ⟨16386866, by rfl⟩ : syracuseStep 21849155 = 32773733) B32773733
theorem B560424491 : Blo 944585 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B1730119 : Blo 944585 1730119 := bstep (se 1 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 1730119 = 2595179) B2595179
theorem B6907577 : Blo 944585 6907577 := bstep (se 2 (by rfl) ⟨2590341, by rfl⟩ : syracuseStep 6907577 = 5180683) B5180683
theorem B1599311 : Blo 944585 1599311 := bstep (se 1 (by rfl) ⟨1199483, by rfl⟩ : syracuseStep 1599311 = 2398967) B2398967
theorem B34498457 : Blo 944585 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B20506769 : Blo 944585 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B1009967 : Blo 944585 1009967 := bstep (se 1 (by rfl) ⟨757475, by rfl⟩ : syracuseStep 1009967 = 1514951) B1514951
theorem B10217785 : Blo 944585 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B4549121 : Blo 944585 4549121 := bstep (se 2 (by rfl) ⟨1705920, by rfl⟩ : syracuseStep 4549121 = 3411841) B3411841
theorem B944667 : Blo 944585 944667 := bstep (se 1 (by rfl) ⟨708500, by rfl⟩ : syracuseStep 944667 = 1417001) B1417001
theorem B944671 : Blo 944585 944671 := bstep (se 1 (by rfl) ⟨708503, by rfl⟩ : syracuseStep 944671 = 1417007) B1417007
theorem B6056623 : Blo 944585 6056623 := bstep (se 1 (by rfl) ⟨4542467, by rfl⟩ : syracuseStep 6056623 = 9084935) B9084935
theorem B944987 : Blo 944585 944987 := bstep (se 1 (by rfl) ⟨708740, by rfl⟩ : syracuseStep 944987 = 1417481) B1417481
theorem B945055 : Blo 944585 945055 := bstep (se 1 (by rfl) ⟨708791, by rfl⟩ : syracuseStep 945055 = 1417583) B1417583
theorem B1600553 : Blo 944585 1600553 := bstep (se 2 (by rfl) ⟨600207, by rfl⟩ : syracuseStep 1600553 = 1200415) B1200415
theorem B945199 : Blo 944585 945199 := bstep (se 1 (by rfl) ⟨708899, by rfl⟩ : syracuseStep 945199 = 1417799) B1417799
theorem B1797167 : Blo 944585 1797167 := bstep (se 1 (by rfl) ⟨1347875, by rfl⟩ : syracuseStep 1797167 = 2695751) B2695751
theorem B4549679 : Blo 944585 4549679 := bstep (se 1 (by rfl) ⟨3412259, by rfl⟩ : syracuseStep 4549679 = 6824519) B6824519
theorem B945223 : Blo 944585 945223 := bstep (se 1 (by rfl) ⟨708917, by rfl⟩ : syracuseStep 945223 = 1417835) B1417835
theorem B945375 : Blo 944585 945375 := bstep (se 1 (by rfl) ⟨709031, by rfl⟩ : syracuseStep 945375 = 1418063) B1418063
theorem B1600735 : Blo 944585 1600735 := bstep (se 1 (by rfl) ⟨1200551, by rfl⟩ : syracuseStep 1600735 = 2401103) B2401103
theorem B2158007 : Blo 944585 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B945639 : Blo 944585 945639 := bstep (se 1 (by rfl) ⟨709229, by rfl⟩ : syracuseStep 945639 = 1418459) B1418459
theorem B1797623 : Blo 944585 1797623 := bstep (se 1 (by rfl) ⟨1348217, by rfl⟩ : syracuseStep 1797623 = 2696435) B2696435
theorem B2125385 : Blo 944585 2125385 := bstep (se 2 (by rfl) ⟨797019, by rfl⟩ : syracuseStep 2125385 = 1594039) B1594039
theorem B945755 : Blo 944585 945755 := bstep (se 1 (by rfl) ⟨709316, by rfl⟩ : syracuseStep 945755 = 1418633) B1418633
theorem B945991 : Blo 944585 945991 := bstep (se 1 (by rfl) ⟨709493, by rfl⟩ : syracuseStep 945991 = 1418987) B1418987
theorem B946143 : Blo 944585 946143 := bstep (se 1 (by rfl) ⟨709607, by rfl⟩ : syracuseStep 946143 = 1419215) B1419215
theorem B20705267 : Blo 944585 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B8745083 : Blo 944585 8745083 := bstep (se 1 (by rfl) ⟨6558812, by rfl⟩ : syracuseStep 8745083 = 13117625) B13117625
theorem B946407 : Blo 944585 946407 := bstep (se 1 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 946407 = 1419611) B1419611
theorem B946559 : Blo 944585 946559 := bstep (se 1 (by rfl) ⟨709919, by rfl⟩ : syracuseStep 946559 = 1419839) B1419839
theorem B4551079 : Blo 944585 4551079 := bstep (se 1 (by rfl) ⟨3413309, by rfl⟩ : syracuseStep 4551079 = 6826619) B6826619
theorem B946639 : Blo 944585 946639 := bstep (se 1 (by rfl) ⟨709979, by rfl⟩ : syracuseStep 946639 = 1419959) B1419959
theorem B6058469 : Blo 944585 6058469 := bstep (se 4 (by rfl) ⟨567981, by rfl⟩ : syracuseStep 6058469 = 1135963) B1135963
theorem B946791 : Blo 944585 946791 := bstep (se 1 (by rfl) ⟨710093, by rfl⟩ : syracuseStep 946791 = 1420187) B1420187
theorem B947055 : Blo 944585 947055 := bstep (se 1 (by rfl) ⟨710291, by rfl⟩ : syracuseStep 947055 = 1420583) B1420583
theorem B947111 : Blo 944585 947111 := bstep (se 1 (by rfl) ⟨710333, by rfl⟩ : syracuseStep 947111 = 1420667) B1420667
theorem B2126843 : Blo 944585 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B947195 : Blo 944585 947195 := bstep (se 1 (by rfl) ⟨710396, by rfl⟩ : syracuseStep 947195 = 1420793) B1420793
theorem B947263 : Blo 944585 947263 := bstep (se 1 (by rfl) ⟨710447, by rfl⟩ : syracuseStep 947263 = 1420895) B1420895
theorem B2127023 : Blo 944585 2127023 := bstep (se 1 (by rfl) ⟨1595267, by rfl⟩ : syracuseStep 2127023 = 3190535) B3190535
theorem B947407 : Blo 944585 947407 := bstep (se 1 (by rfl) ⟨710555, by rfl⟩ : syracuseStep 947407 = 1421111) B1421111
theorem B2127059 : Blo 944585 2127059 := bstep (se 1 (by rfl) ⟨1595294, by rfl⟩ : syracuseStep 2127059 = 3190589) B3190589
theorem B6059393 : Blo 944585 6059393 := bstep (se 2 (by rfl) ⟨2272272, by rfl⟩ : syracuseStep 6059393 = 4544545) B4544545
theorem B947611 : Blo 944585 947611 := bstep (se 1 (by rfl) ⟨710708, by rfl⟩ : syracuseStep 947611 = 1421417) B1421417
theorem B2127329 : Blo 944585 2127329 := bstep (se 2 (by rfl) ⟨797748, by rfl⟩ : syracuseStep 2127329 = 1595497) B1595497
theorem B947823 : Blo 944585 947823 := bstep (se 1 (by rfl) ⟨710867, by rfl⟩ : syracuseStep 947823 = 1421735) B1421735
theorem B947879 : Blo 944585 947879 := bstep (se 1 (by rfl) ⟨710909, by rfl⟩ : syracuseStep 947879 = 1421819) B1421819
theorem B947963 : Blo 944585 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B947999 : Blo 944585 947999 := bstep (se 1 (by rfl) ⟨710999, by rfl⟩ : syracuseStep 947999 = 1421999) B1421999
theorem B948031 : Blo 944585 948031 := bstep (se 1 (by rfl) ⟨711023, by rfl⟩ : syracuseStep 948031 = 1422047) B1422047
theorem B948207 : Blo 944585 948207 := bstep (se 1 (by rfl) ⟨711155, by rfl⟩ : syracuseStep 948207 = 1422311) B1422311
theorem B948379 : Blo 944585 948379 := bstep (se 1 (by rfl) ⟨711284, by rfl⟩ : syracuseStep 948379 = 1422569) B1422569
theorem B948415 : Blo 944585 948415 := bstep (se 1 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 948415 = 1422623) B1422623
theorem B948527 : Blo 944585 948527 := bstep (se 1 (by rfl) ⟨711395, by rfl⟩ : syracuseStep 948527 = 1422791) B1422791
theorem B4553273 : Blo 944585 4553273 := bstep (se 2 (by rfl) ⟨1707477, by rfl⟩ : syracuseStep 4553273 = 3414955) B3414955
theorem B15333947 : Blo 944585 15333947 := bstep (se 1 (by rfl) ⟨11500460, by rfl⟩ : syracuseStep 15333947 = 23000921) B23000921
theorem B2128967 : Blo 944585 2128967 := bstep (se 1 (by rfl) ⟨1596725, by rfl⟩ : syracuseStep 2128967 = 3193451) B3193451
theorem B4324535 : Blo 944585 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B13630751 : Blo 944585 13630751 := bstep (se 1 (by rfl) ⟨10223063, by rfl⟩ : syracuseStep 13630751 = 20446127) B20446127
theorem B12942787 : Blo 944585 12942787 := bstep (se 1 (by rfl) ⟨9707090, by rfl⟩ : syracuseStep 12942787 = 19414181) B19414181
theorem B2129363 : Blo 944585 2129363 := bstep (se 1 (by rfl) ⟨1597022, by rfl⟩ : syracuseStep 2129363 = 3194045) B3194045
theorem B2129633 : Blo 944585 2129633 := bstep (se 2 (by rfl) ⟨798612, by rfl⟩ : syracuseStep 2129633 = 1597225) B1597225
theorem B7274681 : Blo 944585 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B2130155 : Blo 944585 2130155 := bstep (se 1 (by rfl) ⟨1597616, by rfl⟩ : syracuseStep 2130155 = 3195233) B3195233
theorem B10519577 : Blo 944585 10519577 := bstep (se 2 (by rfl) ⟨3944841, by rfl⟩ : syracuseStep 10519577 = 7889683) B7889683
theorem B2131055 : Blo 944585 2131055 := bstep (se 1 (by rfl) ⟨1598291, by rfl⟩ : syracuseStep 2131055 = 3196583) B3196583
theorem B1344937 : Blo 944585 1344937 := bstep (se 2 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 1344937 = 1008703) B1008703
theorem B2131451 : Blo 944585 2131451 := bstep (se 1 (by rfl) ⟨1598588, by rfl⟩ : syracuseStep 2131451 = 3197177) B3197177
theorem B2131487 : Blo 944585 2131487 := bstep (se 1 (by rfl) ⟨1598615, by rfl⟩ : syracuseStep 2131487 = 3197231) B3197231
theorem B2131631 : Blo 944585 2131631 := bstep (se 1 (by rfl) ⟨1598723, by rfl⟩ : syracuseStep 2131631 = 3197447) B3197447
theorem B8095727 : Blo 944585 8095727 := bstep (se 1 (by rfl) ⟨6071795, by rfl⟩ : syracuseStep 8095727 = 12143591) B12143591
theorem B1706015 : Blo 944585 1706015 := bstep (se 1 (by rfl) ⟨1279511, by rfl⟩ : syracuseStep 1706015 = 2559023) B2559023
theorem B2132063 : Blo 944585 2132063 := bstep (se 1 (by rfl) ⟨1599047, by rfl⟩ : syracuseStep 2132063 = 3198095) B3198095
theorem B2394299 : Blo 944585 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B1706267 : Blo 944585 1706267 := bstep (se 1 (by rfl) ⟨1279700, by rfl⟩ : syracuseStep 1706267 = 2559401) B2559401
theorem B2132351 : Blo 944585 2132351 := bstep (se 1 (by rfl) ⟨1599263, by rfl⟩ : syracuseStep 2132351 = 3198527) B3198527
theorem B18221537 : Blo 944585 18221537 := bstep (se 2 (by rfl) ⟨6833076, by rfl⟩ : syracuseStep 18221537 = 13666153) B13666153
theorem B12126779 : Blo 944585 12126779 := bstep (se 1 (by rfl) ⟨9095084, by rfl⟩ : syracuseStep 12126779 = 18190169) B18190169
theorem B2132819 : Blo 944585 2132819 := bstep (se 1 (by rfl) ⟨1599614, by rfl⟩ : syracuseStep 2132819 = 3199229) B3199229
theorem B2133179 : Blo 944585 2133179 := bstep (se 1 (by rfl) ⟨1599884, by rfl⟩ : syracuseStep 2133179 = 3199769) B3199769
theorem B2133359 : Blo 944585 2133359 := bstep (se 1 (by rfl) ⟨1600019, by rfl⟩ : syracuseStep 2133359 = 3200039) B3200039
theorem B2395727 : Blo 944585 2395727 := bstep (se 1 (by rfl) ⟨1796795, by rfl⟩ : syracuseStep 2395727 = 3593591) B3593591
theorem B19468127 : Blo 944585 19468127 := bstep (se 1 (by rfl) ⟨14601095, by rfl⟩ : syracuseStep 19468127 = 29202191) B29202191
theorem B8097641 : Blo 944585 8097641 := bstep (se 2 (by rfl) ⟨3036615, by rfl⟩ : syracuseStep 8097641 = 6073231) B6073231
theorem B2134079 : Blo 944585 2134079 := bstep (se 1 (by rfl) ⟨1600559, by rfl⟩ : syracuseStep 2134079 = 3201119) B3201119
theorem B2396263 : Blo 944585 2396263 := bstep (se 1 (by rfl) ⟨1797197, by rfl⟩ : syracuseStep 2396263 = 3594395) B3594395
theorem B2134313 : Blo 944585 2134313 := bstep (se 2 (by rfl) ⟨800367, by rfl⟩ : syracuseStep 2134313 = 1600735) B1600735
theorem B18420205 : Blo 944585 18420205 := bstep (se 3 (by rfl) ⟨3453788, by rfl⟩ : syracuseStep 18420205 = 6907577) B6907577
theorem B2397671 : Blo 944585 2397671 := bstep (se 1 (by rfl) ⟨1798253, by rfl⟩ : syracuseStep 2397671 = 3596507) B3596507
theorem B6068105 : Blo 944585 6068105 := bstep (se 2 (by rfl) ⟨2275539, by rfl⟩ : syracuseStep 6068105 = 4551079) B4551079
theorem B9115537 : Blo 944585 9115537 := bstep (se 2 (by rfl) ⟨3418326, by rfl⟩ : syracuseStep 9115537 = 6836653) B6836653
theorem B2693245 : Blo 944585 2693245 := bstep (se 3 (by rfl) ⟨504983, by rfl⟩ : syracuseStep 2693245 = 1009967) B1009967
theorem B4855945 : Blo 944585 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B13671179 : Blo 944585 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B5381639 : Blo 944585 5381639 := bstep (se 1 (by rfl) ⟨4036229, by rfl⟩ : syracuseStep 5381639 = 8072459) B8072459
theorem B1416923 : Blo 944585 1416923 := bstep (se 1 (by rfl) ⟨1062692, by rfl⟩ : syracuseStep 1416923 = 2125385) B2125385
theorem B11509613 : Blo 944585 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B8101741 : Blo 944585 8101741 := bstep (se 3 (by rfl) ⟨1519076, by rfl⟩ : syracuseStep 8101741 = 3038153) B3038153
theorem B1417193 : Blo 944585 1417193 := bstep (se 2 (by rfl) ⟨531447, by rfl⟩ : syracuseStep 1417193 = 1062895) B1062895
theorem B4792445 : Blo 944585 4792445 := bstep (se 3 (by rfl) ⟨898583, by rfl⟩ : syracuseStep 4792445 = 1797167) B1797167
theorem B4038979 : Blo 944585 4038979 := bstep (se 1 (by rfl) ⟨3029234, by rfl⟩ : syracuseStep 4038979 = 6058469) B6058469
theorem B1417895 : Blo 944585 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B1418015 : Blo 944585 1418015 := bstep (se 1 (by rfl) ⟨1063511, by rfl⟩ : syracuseStep 1418015 = 2127023) B2127023
theorem B1418039 : Blo 944585 1418039 := bstep (se 1 (by rfl) ⟨1063529, by rfl⟩ : syracuseStep 1418039 = 2127059) B2127059
theorem B4793255 : Blo 944585 4793255 := bstep (se 1 (by rfl) ⟨3594941, by rfl⟩ : syracuseStep 4793255 = 7189883) B7189883
theorem B4039595 : Blo 944585 4039595 := bstep (se 1 (by rfl) ⟨3029696, by rfl⟩ : syracuseStep 4039595 = 6059393) B6059393
theorem B1418219 : Blo 944585 1418219 := bstep (se 1 (by rfl) ⟨1063664, by rfl⟩ : syracuseStep 1418219 = 2127329) B2127329
theorem B1516591 : Blo 944585 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B2696777 : Blo 944585 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B1419311 : Blo 944585 1419311 := bstep (se 1 (by rfl) ⟨1064483, by rfl⟩ : syracuseStep 1419311 = 2128967) B2128967
theorem B9087167 : Blo 944585 9087167 := bstep (se 1 (by rfl) ⟨6815375, by rfl⟩ : syracuseStep 9087167 = 13630751) B13630751
theorem B4204855 : Blo 944585 4204855 := bstep (se 1 (by rfl) ⟨3153641, by rfl⟩ : syracuseStep 4204855 = 6307283) B6307283
theorem B1419575 : Blo 944585 1419575 := bstep (se 1 (by rfl) ⟨1064681, by rfl⟩ : syracuseStep 1419575 = 2129363) B2129363
theorem B1419755 : Blo 944585 1419755 := bstep (se 1 (by rfl) ⟨1064816, by rfl⟩ : syracuseStep 1419755 = 2129633) B2129633
theorem B136719197 : Blo 944585 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B1420457 : Blo 944585 1420457 := bstep (se 2 (by rfl) ⟨532671, by rfl⟩ : syracuseStep 1420457 = 1065343) B1065343
theorem B4041971 : Blo 944585 4041971 := bstep (se 1 (by rfl) ⟨3031478, by rfl⟩ : syracuseStep 4041971 = 6062957) B6062957
theorem B1420871 : Blo 944585 1420871 := bstep (se 1 (by rfl) ⟨1065653, by rfl⟩ : syracuseStep 1420871 = 2131307) B2131307
theorem B2698895 : Blo 944585 2698895 := bstep (se 1 (by rfl) ⟨2024171, by rfl⟩ : syracuseStep 2698895 = 4048343) B4048343
theorem B1421051 : Blo 944585 1421051 := bstep (se 1 (by rfl) ⟨1065788, by rfl⟩ : syracuseStep 1421051 = 2131577) B2131577
theorem B8073107 : Blo 944585 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B10367009 : Blo 944585 10367009 := bstep (se 2 (by rfl) ⟨3887628, by rfl⟩ : syracuseStep 10367009 = 7775257) B7775257
theorem B3027071 : Blo 944585 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B1421723 : Blo 944585 1421723 := bstep (se 1 (by rfl) ⟨1066292, by rfl⟩ : syracuseStep 1421723 = 2132585) B2132585
theorem B11809223 : Blo 944585 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B2273849 : Blo 944585 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B2306825 : Blo 944585 2306825 := bstep (se 2 (by rfl) ⟨865059, by rfl⟩ : syracuseStep 2306825 = 1730119) B1730119
theorem B3191615 : Blo 944585 3191615 := bstep (se 1 (by rfl) ⟨2393711, by rfl⟩ : syracuseStep 3191615 = 4787423) B4787423
theorem B1422143 : Blo 944585 1422143 := bstep (se 1 (by rfl) ⟨1066607, by rfl⟩ : syracuseStep 1422143 = 2133215) B2133215
theorem B11678671 : Blo 944585 11678671 := bstep (se 1 (by rfl) ⟨8759003, by rfl⟩ : syracuseStep 11678671 = 17518007) B17518007
theorem B1422287 : Blo 944585 1422287 := bstep (se 1 (by rfl) ⟨1066715, by rfl⟩ : syracuseStep 1422287 = 2133431) B2133431
theorem B1422329 : Blo 944585 1422329 := bstep (se 2 (by rfl) ⟨533373, by rfl⟩ : syracuseStep 1422329 = 1066747) B1066747
theorem B1422377 : Blo 944585 1422377 := bstep (se 2 (by rfl) ⟨533391, by rfl⟩ : syracuseStep 1422377 = 1066783) B1066783
theorem B1422407 : Blo 944585 1422407 := bstep (se 1 (by rfl) ⟨1066805, by rfl⟩ : syracuseStep 1422407 = 2133611) B2133611
theorem B1422587 : Blo 944585 1422587 := bstep (se 1 (by rfl) ⟨1066940, by rfl⟩ : syracuseStep 1422587 = 2133881) B2133881
theorem B3192317 : Blo 944585 3192317 := bstep (se 3 (by rfl) ⟨598559, by rfl⟩ : syracuseStep 3192317 = 1197119) B1197119
theorem B6829591 : Blo 944585 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B4044431 : Blo 944585 4044431 := bstep (se 1 (by rfl) ⟨3033323, by rfl⟩ : syracuseStep 4044431 = 6066647) B6066647
theorem B15349459 : Blo 944585 15349459 := bstep (se 1 (by rfl) ⟨11512094, by rfl⟩ : syracuseStep 15349459 = 23024189) B23024189
theorem B10237853 : Blo 944585 10237853 := bstep (se 3 (by rfl) ⟨1919597, by rfl⟩ : syracuseStep 10237853 = 3839195) B3839195
theorem B4798439 : Blo 944585 4798439 := bstep (se 1 (by rfl) ⟨3598829, by rfl⟩ : syracuseStep 4798439 = 7197659) B7197659
theorem B8075497 : Blo 944585 8075497 := bstep (se 2 (by rfl) ⟨3028311, by rfl⟩ : syracuseStep 8075497 = 6056623) B6056623
theorem B3193127 : Blo 944585 3193127 := bstep (se 1 (by rfl) ⟨2394845, by rfl⟩ : syracuseStep 3193127 = 4789691) B4789691
theorem B1063327 : Blo 944585 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B1063399 : Blo 944585 1063399 := bstep (se 1 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 1063399 = 1595099) B1595099
theorem B6830891 : Blo 944585 6830891 := bstep (se 1 (by rfl) ⟨5123168, by rfl⟩ : syracuseStep 6830891 = 10246337) B10246337
theorem B7289767 : Blo 944585 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B3587105 : Blo 944585 3587105 := bstep (se 2 (by rfl) ⟨1345164, by rfl⟩ : syracuseStep 3587105 = 2690329) B2690329
theorem B3194099 : Blo 944585 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B1064263 : Blo 944585 1064263 := bstep (se 1 (by rfl) ⟨798197, by rfl⟩ : syracuseStep 1064263 = 1596395) B1596395
theorem B1195975 : Blo 944585 1195975 := bstep (se 1 (by rfl) ⟨896981, by rfl⟩ : syracuseStep 1195975 = 1793963) B1793963
theorem B3588077 : Blo 944585 3588077 := bstep (se 3 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 3588077 = 1345529) B1345529
theorem B3195071 : Blo 944585 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B14566103 : Blo 944585 14566103 := bstep (se 1 (by rfl) ⟨10924577, by rfl⟩ : syracuseStep 14566103 = 21849155) B21849155
theorem B4047727 : Blo 944585 4047727 := bstep (se 1 (by rfl) ⟨3035795, by rfl⟩ : syracuseStep 4047727 = 6071591) B6071591
theorem B3589019 : Blo 944585 3589019 := bstep (se 1 (by rfl) ⟨2691764, by rfl⟩ : syracuseStep 3589019 = 5383529) B5383529
theorem B4375547 : Blo 944585 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B3589231 : Blo 944585 3589231 := bstep (se 1 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 3589231 = 5383847) B5383847
theorem B46679237 : Blo 944585 46679237 := bstep (se 4 (by rfl) ⟨4376178, by rfl⟩ : syracuseStep 46679237 = 8752357) B8752357
theorem B1066207 : Blo 944585 1066207 := bstep (se 1 (by rfl) ⟨799655, by rfl⟩ : syracuseStep 1066207 = 1599311) B1599311
theorem B16368875 : Blo 944585 16368875 := bstep (se 1 (by rfl) ⟨12276656, by rfl⟩ : syracuseStep 16368875 = 24553313) B24553313
theorem B103564565 : Blo 944585 103564565 := bstep (se 6 (by rfl) ⟨2427294, by rfl⟩ : syracuseStep 103564565 = 4854589) B4854589
theorem B3327419 : Blo 944585 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B3032747 : Blo 944585 3032747 := bstep (se 1 (by rfl) ⟨2274560, by rfl⟩ : syracuseStep 3032747 = 4549121) B4549121
theorem B1067035 : Blo 944585 1067035 := bstep (se 1 (by rfl) ⟨800276, by rfl⟩ : syracuseStep 1067035 = 1600553) B1600553
theorem B3033119 : Blo 944585 3033119 := bstep (se 1 (by rfl) ⟨2274839, by rfl⟩ : syracuseStep 3033119 = 4549679) B4549679
theorem B1198415 : Blo 944585 1198415 := bstep (se 1 (by rfl) ⟨898811, by rfl⟩ : syracuseStep 1198415 = 1797623) B1797623
theorem B3590507 : Blo 944585 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B2017705 : Blo 944585 2017705 := bstep (se 2 (by rfl) ⟨756639, by rfl⟩ : syracuseStep 2017705 = 1513279) B1513279
theorem B3197555 : Blo 944585 3197555 := bstep (se 1 (by rfl) ⟨2398166, by rfl⟩ : syracuseStep 3197555 = 4796333) B4796333
theorem B61524683 : Blo 944585 61524683 := bstep (se 1 (by rfl) ⟨46143512, by rfl⟩ : syracuseStep 61524683 = 92287025) B92287025
theorem B3197825 : Blo 944585 3197825 := bstep (se 2 (by rfl) ⟨1199184, by rfl⟩ : syracuseStep 3197825 = 2398369) B2398369
theorem B8080829 : Blo 944585 8080829 := bstep (se 3 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 8080829 = 3030311) B3030311
theorem B39308971 : Blo 944585 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B3198635 : Blo 944585 3198635 := bstep (se 1 (by rfl) ⟨2398976, by rfl⟩ : syracuseStep 3198635 = 4797953) B4797953
theorem B5754685 : Blo 944585 5754685 := bstep (se 3 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 5754685 = 2158007) B2158007
theorem B3199175 : Blo 944585 3199175 := bstep (se 1 (by rfl) ⟨2399381, by rfl⟩ : syracuseStep 3199175 = 4798763) B4798763
theorem B3035515 : Blo 944585 3035515 := bstep (se 1 (by rfl) ⟨2276636, by rfl⟩ : syracuseStep 3035515 = 4553273) B4553273
theorem B17257049 : Blo 944585 17257049 := bstep (se 2 (by rfl) ⟨6471393, by rfl⟩ : syracuseStep 17257049 = 12942787) B12942787
theorem B3200363 : Blo 944585 3200363 := bstep (se 1 (by rfl) ⟨2400272, by rfl⟩ : syracuseStep 3200363 = 4800545) B4800545
theorem B2053487 : Blo 944585 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B2020943 : Blo 944585 2020943 := bstep (se 1 (by rfl) ⟨1515707, by rfl⟩ : syracuseStep 2020943 = 3031415) B3031415
theorem B3200633 : Blo 944585 3200633 := bstep (se 2 (by rfl) ⟨1200237, by rfl⟩ : syracuseStep 3200633 = 2400475) B2400475
theorem B2840231 : Blo 944585 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B5461739 : Blo 944585 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B9721579 : Blo 944585 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B1595207 : Blo 944585 1595207 := bstep (se 1 (by rfl) ⟨1196405, by rfl⟩ : syracuseStep 1595207 = 2392811) B2392811
theorem B1595227 : Blo 944585 1595227 := bstep (se 1 (by rfl) ⟨1196420, by rfl⟩ : syracuseStep 1595227 = 2392841) B2392841
theorem B3200957 : Blo 944585 3200957 := bstep (se 3 (by rfl) ⟨600179, by rfl⟩ : syracuseStep 3200957 = 1200359) B1200359
theorem B5396651 : Blo 944585 5396651 := bstep (se 1 (by rfl) ⟨4047488, by rfl⟩ : syracuseStep 5396651 = 8094977) B8094977
theorem B3594577 : Blo 944585 3594577 := bstep (se 2 (by rfl) ⟨1347966, by rfl⟩ : syracuseStep 3594577 = 2695933) B2695933
theorem B345332219 : Blo 944585 345332219 := bstep (se 1 (by rfl) ⟨258999164, by rfl⟩ : syracuseStep 345332219 = 517998329) B517998329
theorem B3595063 : Blo 944585 3595063 := bstep (se 1 (by rfl) ⟨2696297, by rfl⟩ : syracuseStep 3595063 = 5392595) B5392595
theorem B3595549 : Blo 944585 3595549 := bstep (se 3 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 3595549 = 1348331) B1348331
theorem B7691597 : Blo 944585 7691597 := bstep (se 3 (by rfl) ⟨1442174, by rfl⟩ : syracuseStep 7691597 = 2884349) B2884349
theorem B8085203 : Blo 944585 8085203 := bstep (se 1 (by rfl) ⟨6063902, by rfl⟩ : syracuseStep 8085203 = 12127805) B12127805
theorem B9723635 : Blo 944585 9723635 := bstep (se 1 (by rfl) ⟨7292726, by rfl⟩ : syracuseStep 9723635 = 14585453) B14585453
theorem B6054011 : Blo 944585 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B13623713 : Blo 944585 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B3596795 : Blo 944585 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B1139231 : Blo 944585 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B3597007 : Blo 944585 3597007 := bstep (se 1 (by rfl) ⟨2697755, by rfl⟩ : syracuseStep 3597007 = 5395511) B5395511
theorem B1795193 : Blo 944585 1795193 := bstep (se 2 (by rfl) ⟨673197, by rfl⟩ : syracuseStep 1795193 = 1346395) B1346395
theorem B31974931 : Blo 944585 31974931 := bstep (se 1 (by rfl) ⟨23981198, by rfl⟩ : syracuseStep 31974931 = 47962397) B47962397
theorem B1796089 : Blo 944585 1796089 := bstep (se 2 (by rfl) ⟨673533, by rfl⟩ : syracuseStep 1796089 = 1347067) B1347067
theorem B7661783 : Blo 944585 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B5401025 : Blo 944585 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B1599979 : Blo 944585 1599979 := bstep (se 1 (by rfl) ⟨1199984, by rfl⟩ : syracuseStep 1599979 = 2399969) B2399969
theorem B944687 : Blo 944585 944687 := bstep (se 1 (by rfl) ⟨708515, by rfl⟩ : syracuseStep 944687 = 1417031) B1417031
theorem B944743 : Blo 944585 944743 := bstep (se 1 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 944743 = 1417115) B1417115
theorem B94563235 : Blo 944585 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B945119 : Blo 944585 945119 := bstep (se 1 (by rfl) ⟨708839, by rfl⟩ : syracuseStep 945119 = 1417679) B1417679
theorem B945147 : Blo 944585 945147 := bstep (se 1 (by rfl) ⟨708860, by rfl⟩ : syracuseStep 945147 = 1417721) B1417721
theorem B945215 : Blo 944585 945215 := bstep (se 1 (by rfl) ⟨708911, by rfl⟩ : syracuseStep 945215 = 1417823) B1417823
theorem B1600681 : Blo 944585 1600681 := bstep (se 2 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 1600681 = 1200511) B1200511
theorem B945535 : Blo 944585 945535 := bstep (se 1 (by rfl) ⟨709151, by rfl⟩ : syracuseStep 945535 = 1418303) B1418303
theorem B945563 : Blo 944585 945563 := bstep (se 1 (by rfl) ⟨709172, by rfl⟩ : syracuseStep 945563 = 1418345) B1418345
theorem B945631 : Blo 944585 945631 := bstep (se 1 (by rfl) ⟨709223, by rfl⟩ : syracuseStep 945631 = 1418447) B1418447
theorem B2125403 : Blo 944585 2125403 := bstep (se 1 (by rfl) ⟨1594052, by rfl⟩ : syracuseStep 2125403 = 3188105) B3188105
theorem B945767 : Blo 944585 945767 := bstep (se 1 (by rfl) ⟨709325, by rfl⟩ : syracuseStep 945767 = 1418651) B1418651
theorem B373616327 : Blo 944585 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B945915 : Blo 944585 945915 := bstep (se 1 (by rfl) ⟨709436, by rfl⟩ : syracuseStep 945915 = 1418873) B1418873
theorem B945983 : Blo 944585 945983 := bstep (se 1 (by rfl) ⟨709487, by rfl⟩ : syracuseStep 945983 = 1418975) B1418975
theorem B946047 : Blo 944585 946047 := bstep (se 1 (by rfl) ⟨709535, by rfl⟩ : syracuseStep 946047 = 1419071) B1419071
theorem B22998971 : Blo 944585 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B946159 : Blo 944585 946159 := bstep (se 1 (by rfl) ⟨709619, by rfl⟩ : syracuseStep 946159 = 1419239) B1419239
theorem B2125817 : Blo 944585 2125817 := bstep (se 2 (by rfl) ⟨797181, by rfl⟩ : syracuseStep 2125817 = 1594363) B1594363
theorem B946171 : Blo 944585 946171 := bstep (se 1 (by rfl) ⟨709628, by rfl⟩ : syracuseStep 946171 = 1419257) B1419257
theorem B946239 : Blo 944585 946239 := bstep (se 1 (by rfl) ⟨709679, by rfl⟩ : syracuseStep 946239 = 1419359) B1419359
theorem B2125907 : Blo 944585 2125907 := bstep (se 1 (by rfl) ⟨1594430, by rfl⟩ : syracuseStep 2125907 = 3188861) B3188861
theorem B946279 : Blo 944585 946279 := bstep (se 1 (by rfl) ⟨709709, by rfl⟩ : syracuseStep 946279 = 1419419) B1419419
theorem B946303 : Blo 944585 946303 := bstep (se 1 (by rfl) ⟨709727, by rfl⟩ : syracuseStep 946303 = 1419455) B1419455
theorem B6484121 : Blo 944585 6484121 := bstep (se 2 (by rfl) ⟨2431545, by rfl⟩ : syracuseStep 6484121 = 4863091) B4863091
theorem B1077403 : Blo 944585 1077403 := bstep (se 1 (by rfl) ⟨808052, by rfl⟩ : syracuseStep 1077403 = 1616105) B1616105
theorem B946331 : Blo 944585 946331 := bstep (se 1 (by rfl) ⟨709748, by rfl⟩ : syracuseStep 946331 = 1419497) B1419497
theorem B1798375 : Blo 944585 1798375 := bstep (se 1 (by rfl) ⟨1348781, by rfl⟩ : syracuseStep 1798375 = 2697563) B2697563
theorem B2126087 : Blo 944585 2126087 := bstep (se 1 (by rfl) ⟨1594565, by rfl⟩ : syracuseStep 2126087 = 3189131) B3189131
theorem B10383671 : Blo 944585 10383671 := bstep (se 1 (by rfl) ⟨7787753, by rfl⟩ : syracuseStep 10383671 = 15575507) B15575507
theorem B946535 : Blo 944585 946535 := bstep (se 1 (by rfl) ⟨709901, by rfl⟩ : syracuseStep 946535 = 1419803) B1419803
theorem B946587 : Blo 944585 946587 := bstep (se 1 (by rfl) ⟨709940, by rfl⟩ : syracuseStep 946587 = 1419881) B1419881
theorem B2126393 : Blo 944585 2126393 := bstep (se 2 (by rfl) ⟨797397, by rfl⟩ : syracuseStep 2126393 = 1594795) B1594795
theorem B18182717 : Blo 944585 18182717 := bstep (se 3 (by rfl) ⟨3409259, by rfl⟩ : syracuseStep 18182717 = 6818519) B6818519
theorem B946939 : Blo 944585 946939 := bstep (se 1 (by rfl) ⟨710204, by rfl⟩ : syracuseStep 946939 = 1420409) B1420409
theorem B947007 : Blo 944585 947007 := bstep (se 1 (by rfl) ⟨710255, by rfl⟩ : syracuseStep 947007 = 1420511) B1420511
theorem B20476745 : Blo 944585 20476745 := bstep (se 2 (by rfl) ⟨7678779, by rfl⟩ : syracuseStep 20476745 = 15357559) B15357559
theorem B947035 : Blo 944585 947035 := bstep (se 1 (by rfl) ⟨710276, by rfl⟩ : syracuseStep 947035 = 1420553) B1420553
theorem B947103 : Blo 944585 947103 := bstep (se 1 (by rfl) ⟨710327, by rfl⟩ : syracuseStep 947103 = 1420655) B1420655
theorem B947183 : Blo 944585 947183 := bstep (se 1 (by rfl) ⟨710387, by rfl⟩ : syracuseStep 947183 = 1420775) B1420775
theorem B947271 : Blo 944585 947271 := bstep (se 1 (by rfl) ⟨710453, by rfl⟩ : syracuseStep 947271 = 1420907) B1420907
theorem B947355 : Blo 944585 947355 := bstep (se 1 (by rfl) ⟨710516, by rfl⟩ : syracuseStep 947355 = 1421033) B1421033
theorem B4617425 : Blo 944585 4617425 := bstep (se 2 (by rfl) ⟨1731534, by rfl⟩ : syracuseStep 4617425 = 3463069) B3463069
theorem B947451 : Blo 944585 947451 := bstep (se 1 (by rfl) ⟨710588, by rfl⟩ : syracuseStep 947451 = 1421177) B1421177
theorem B2127113 : Blo 944585 2127113 := bstep (se 2 (by rfl) ⟨797667, by rfl⟩ : syracuseStep 2127113 = 1595335) B1595335
theorem B2127167 : Blo 944585 2127167 := bstep (se 1 (by rfl) ⟨1595375, by rfl⟩ : syracuseStep 2127167 = 3190751) B3190751
theorem B947519 : Blo 944585 947519 := bstep (se 1 (by rfl) ⟨710639, by rfl⟩ : syracuseStep 947519 = 1421279) B1421279
theorem B5830055 : Blo 944585 5830055 := bstep (se 1 (by rfl) ⟨4372541, by rfl⟩ : syracuseStep 5830055 = 8745083) B8745083
theorem B2127275 : Blo 944585 2127275 := bstep (se 1 (by rfl) ⟨1595456, by rfl⟩ : syracuseStep 2127275 = 3190913) B3190913
theorem B947687 : Blo 944585 947687 := bstep (se 1 (by rfl) ⟨710765, by rfl⟩ : syracuseStep 947687 = 1421531) B1421531
theorem B119600621 : Blo 944585 119600621 := bstep (se 3 (by rfl) ⟨22425116, by rfl⟩ : syracuseStep 119600621 = 44850233) B44850233
theorem B947695 : Blo 944585 947695 := bstep (se 1 (by rfl) ⟨710771, by rfl⟩ : syracuseStep 947695 = 1421543) B1421543
theorem B947803 : Blo 944585 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B947867 : Blo 944585 947867 := bstep (se 1 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 947867 = 1421801) B1421801
theorem B2127599 : Blo 944585 2127599 := bstep (se 1 (by rfl) ⟨1595699, by rfl⟩ : syracuseStep 2127599 = 3191399) B3191399
theorem B947951 : Blo 944585 947951 := bstep (se 1 (by rfl) ⟨710963, by rfl⟩ : syracuseStep 947951 = 1421927) B1421927
theorem B948039 : Blo 944585 948039 := bstep (se 1 (by rfl) ⟨711029, by rfl⟩ : syracuseStep 948039 = 1422059) B1422059
theorem B948059 : Blo 944585 948059 := bstep (se 1 (by rfl) ⟨711044, by rfl⟩ : syracuseStep 948059 = 1422089) B1422089
theorem B948127 : Blo 944585 948127 := bstep (se 1 (by rfl) ⟨711095, by rfl⟩ : syracuseStep 948127 = 1422191) B1422191
theorem B2127815 : Blo 944585 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B948295 : Blo 944585 948295 := bstep (se 1 (by rfl) ⟨711221, by rfl⟩ : syracuseStep 948295 = 1422443) B1422443
theorem B2128103 : Blo 944585 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B948455 : Blo 944585 948455 := bstep (se 1 (by rfl) ⟨711341, by rfl⟩ : syracuseStep 948455 = 1422683) B1422683
theorem B2128121 : Blo 944585 2128121 := bstep (se 2 (by rfl) ⟨798045, by rfl⟩ : syracuseStep 2128121 = 1596091) B1596091
theorem B6486281 : Blo 944585 6486281 := bstep (se 2 (by rfl) ⟨2432355, by rfl⟩ : syracuseStep 6486281 = 4864711) B4864711
theorem B2128175 : Blo 944585 2128175 := bstep (se 1 (by rfl) ⟨1596131, by rfl⟩ : syracuseStep 2128175 = 3192263) B3192263
theorem B2128391 : Blo 944585 2128391 := bstep (se 1 (by rfl) ⟨1596293, by rfl⟩ : syracuseStep 2128391 = 3192587) B3192587
theorem B4618783 : Blo 944585 4618783 := bstep (se 1 (by rfl) ⟨3464087, by rfl⟩ : syracuseStep 4618783 = 6928175) B6928175
theorem B2128571 : Blo 944585 2128571 := bstep (se 1 (by rfl) ⟨1596428, by rfl⟩ : syracuseStep 2128571 = 3192857) B3192857
theorem B10222631 : Blo 944585 10222631 := bstep (se 1 (by rfl) ⟨7666973, by rfl⟩ : syracuseStep 10222631 = 15333947) B15333947
theorem B2883023 : Blo 944585 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B2129471 : Blo 944585 2129471 := bstep (se 1 (by rfl) ⟨1597103, by rfl⟩ : syracuseStep 2129471 = 3194207) B3194207
theorem B7175789 : Blo 944585 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B2391727 : Blo 944585 2391727 := bstep (se 1 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 2391727 = 3587591) B3587591
theorem B2129831 : Blo 944585 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B55214045 : Blo 944585 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B4849787 : Blo 944585 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B2130047 : Blo 944585 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B2392679 : Blo 944585 2392679 := bstep (se 1 (by rfl) ⟨1794509, by rfl⟩ : syracuseStep 2392679 = 3589019) B3589019
theorem B2917031 : Blo 944585 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7013051 : Blo 944585 7013051 := bstep (se 1 (by rfl) ⟨5259788, by rfl⟩ : syracuseStep 7013051 = 10519577) B10519577
theorem B27689789 : Blo 944585 27689789 := bstep (se 3 (by rfl) ⟨5191835, by rfl⟩ : syracuseStep 27689789 = 10383671) B10383671
theorem B10912583 : Blo 944585 10912583 := bstep (se 1 (by rfl) ⟨8184437, by rfl⟩ : syracuseStep 10912583 = 16368875) B16368875
theorem B69043043 : Blo 944585 69043043 := bstep (se 1 (by rfl) ⟨51782282, by rfl⟩ : syracuseStep 69043043 = 103564565) B103564565
theorem B4785641 : Blo 944585 4785641 := bstep (se 2 (by rfl) ⟨1794615, by rfl⟩ : syracuseStep 4785641 = 3589231) B3589231
theorem B2393671 : Blo 944585 2393671 := bstep (se 1 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 2393671 = 3590507) B3590507
theorem B2131703 : Blo 944585 2131703 := bstep (se 1 (by rfl) ⟨1598777, by rfl⟩ : syracuseStep 2131703 = 3197555) B3197555
theorem B2131883 : Blo 944585 2131883 := bstep (se 1 (by rfl) ⟨1598912, by rfl⟩ : syracuseStep 2131883 = 3197825) B3197825
theorem B2132423 : Blo 944585 2132423 := bstep (se 1 (by rfl) ⟨1599317, by rfl⟩ : syracuseStep 2132423 = 3198635) B3198635
theorem B12978751 : Blo 944585 12978751 := bstep (se 1 (by rfl) ⟨9734063, by rfl⟩ : syracuseStep 12978751 = 19468127) B19468127
theorem B2394785 : Blo 944585 2394785 := bstep (se 2 (by rfl) ⟨898044, by rfl⟩ : syracuseStep 2394785 = 1796089) B1796089
theorem B2132783 : Blo 944585 2132783 := bstep (se 1 (by rfl) ⟨1599587, by rfl⟩ : syracuseStep 2132783 = 3199175) B3199175
theorem B11504699 : Blo 944585 11504699 := bstep (se 1 (by rfl) ⟨8628524, by rfl⟩ : syracuseStep 11504699 = 17257049) B17257049
theorem B2690273 : Blo 944585 2690273 := bstep (se 2 (by rfl) ⟨1008852, by rfl⟩ : syracuseStep 2690273 = 2017705) B2017705
theorem B2133305 : Blo 944585 2133305 := bstep (se 2 (by rfl) ⟨799989, by rfl⟩ : syracuseStep 2133305 = 1599979) B1599979
theorem B2133575 : Blo 944585 2133575 := bstep (se 1 (by rfl) ⟨1600181, by rfl⟩ : syracuseStep 2133575 = 3200363) B3200363
theorem B1347295 : Blo 944585 1347295 := bstep (se 1 (by rfl) ⟨1010471, by rfl⟩ : syracuseStep 1347295 = 2020943) B2020943
theorem B2133755 : Blo 944585 2133755 := bstep (se 1 (by rfl) ⟨1600316, by rfl⟩ : syracuseStep 2133755 = 3200633) B3200633
theorem B3641159 : Blo 944585 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B2133971 : Blo 944585 2133971 := bstep (se 1 (by rfl) ⟨1600478, by rfl⟩ : syracuseStep 2133971 = 3200957) B3200957
theorem B2134241 : Blo 944585 2134241 := bstep (se 2 (by rfl) ⟨800340, by rfl⟩ : syracuseStep 2134241 = 1600681) B1600681
theorem B7573949 : Blo 944585 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B9114119 : Blo 944585 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B7672913 : Blo 944585 7672913 := bstep (se 2 (by rfl) ⟨2877342, by rfl⟩ : syracuseStep 7672913 = 5754685) B5754685
theorem B7673075 : Blo 944585 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B4036007 : Blo 944585 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B9082475 : Blo 944585 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B2397833 : Blo 944585 2397833 := bstep (se 2 (by rfl) ⟨899187, by rfl⟩ : syracuseStep 2397833 = 1798375) B1798375
theorem B2397863 : Blo 944585 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B2693063 : Blo 944585 2693063 := bstep (se 1 (by rfl) ⟨2019797, by rfl⟩ : syracuseStep 2693063 = 4039595) B4039595
theorem B15571561 : Blo 944585 15571561 := bstep (se 2 (by rfl) ⟨5839335, by rfl⟩ : syracuseStep 15571561 = 11678671) B11678671
theorem B920885917 : Blo 944585 920885917 := bstep (se 3 (by rfl) ⟨172666109, by rfl⟩ : syracuseStep 920885917 = 345332219) B345332219
theorem B2694647 : Blo 944585 2694647 := bstep (se 1 (by rfl) ⟨2020985, by rfl⟩ : syracuseStep 2694647 = 4041971) B4041971
theorem B1416935 : Blo 944585 1416935 := bstep (se 1 (by rfl) ⟨1062701, by rfl⟩ : syracuseStep 1416935 = 2125403) B2125403
theorem B249077551 : Blo 944585 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B5382071 : Blo 944585 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1417211 : Blo 944585 1417211 := bstep (se 1 (by rfl) ⟨1062908, by rfl⟩ : syracuseStep 1417211 = 2125817) B2125817
theorem B1417271 : Blo 944585 1417271 := bstep (se 1 (by rfl) ⟨1062953, by rfl⟩ : syracuseStep 1417271 = 2125907) B2125907
theorem B170532965 : Blo 944585 170532965 := bstep (se 4 (by rfl) ⟨15987465, by rfl⟩ : syracuseStep 170532965 = 31974931) B31974931
theorem B1417391 : Blo 944585 1417391 := bstep (se 1 (by rfl) ⟨1063043, by rfl⟩ : syracuseStep 1417391 = 2126087) B2126087
theorem B7872815 : Blo 944585 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B1417595 : Blo 944585 1417595 := bstep (se 1 (by rfl) ⟨1063196, by rfl⟩ : syracuseStep 1417595 = 2126393) B2126393
theorem B1515899 : Blo 944585 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B4792769 : Blo 944585 4792769 := bstep (se 2 (by rfl) ⟨1797288, by rfl⟩ : syracuseStep 4792769 = 3594577) B3594577
theorem B1417769 : Blo 944585 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B1417865 : Blo 944585 1417865 := bstep (se 2 (by rfl) ⟨531699, by rfl⟩ : syracuseStep 1417865 = 1063399) B1063399
theorem B1418075 : Blo 944585 1418075 := bstep (se 1 (by rfl) ⟨1063556, by rfl⟩ : syracuseStep 1418075 = 2127113) B2127113
theorem B1418111 : Blo 944585 1418111 := bstep (se 1 (by rfl) ⟨1063583, by rfl⟩ : syracuseStep 1418111 = 2127167) B2127167
theorem B1418183 : Blo 944585 1418183 := bstep (se 1 (by rfl) ⟨1063637, by rfl⟩ : syracuseStep 1418183 = 2127275) B2127275
theorem B79733747 : Blo 944585 79733747 := bstep (se 1 (by rfl) ⟨59800310, by rfl⟩ : syracuseStep 79733747 = 119600621) B119600621
theorem B4793417 : Blo 944585 4793417 := bstep (se 2 (by rfl) ⟨1797531, by rfl⟩ : syracuseStep 4793417 = 3595063) B3595063
theorem B2696287 : Blo 944585 2696287 := bstep (se 1 (by rfl) ⟨2022215, by rfl⟩ : syracuseStep 2696287 = 4044431) B4044431
theorem B1418399 : Blo 944585 1418399 := bstep (se 1 (by rfl) ⟨1063799, by rfl⟩ : syracuseStep 1418399 = 2127599) B2127599
theorem B6825235 : Blo 944585 6825235 := bstep (se 1 (by rfl) ⟨5118926, by rfl⟩ : syracuseStep 6825235 = 10237853) B10237853
theorem B1418543 : Blo 944585 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B1418735 : Blo 944585 1418735 := bstep (se 1 (by rfl) ⟨1064051, by rfl⟩ : syracuseStep 1418735 = 2128103) B2128103
theorem B1418747 : Blo 944585 1418747 := bstep (se 1 (by rfl) ⟨1064060, by rfl⟩ : syracuseStep 1418747 = 2128121) B2128121
theorem B1418783 : Blo 944585 1418783 := bstep (se 1 (by rfl) ⟨1064087, by rfl⟩ : syracuseStep 1418783 = 2128175) B2128175
theorem B1418927 : Blo 944585 1418927 := bstep (se 1 (by rfl) ⟨1064195, by rfl⟩ : syracuseStep 1418927 = 2128391) B2128391
theorem B4794065 : Blo 944585 4794065 := bstep (se 2 (by rfl) ⟨1797774, by rfl⟩ : syracuseStep 4794065 = 3595549) B3595549
theorem B1419017 : Blo 944585 1419017 := bstep (se 2 (by rfl) ⟨532131, by rfl⟩ : syracuseStep 1419017 = 1064263) B1064263
theorem B1419047 : Blo 944585 1419047 := bstep (se 1 (by rfl) ⟨1064285, by rfl⟩ : syracuseStep 1419047 = 2128571) B2128571
theorem B3188969 : Blo 944585 3188969 := bstep (se 2 (by rfl) ⟨1195863, by rfl⟩ : syracuseStep 3188969 = 2391727) B2391727
theorem B1419647 : Blo 944585 1419647 := bstep (se 1 (by rfl) ⟨1064735, by rfl⟩ : syracuseStep 1419647 = 2129471) B2129471
theorem B1419887 : Blo 944585 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B36809363 : Blo 944585 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B1420103 : Blo 944585 1420103 := bstep (se 1 (by rfl) ⟨1065077, by rfl⟩ : syracuseStep 1420103 = 2130155) B2130155
theorem B5385305 : Blo 944585 5385305 := bstep (se 2 (by rfl) ⟨2019489, by rfl⟩ : syracuseStep 5385305 = 4038979) B4038979
theorem B9710735 : Blo 944585 9710735 := bstep (se 1 (by rfl) ⟨7283051, by rfl⟩ : syracuseStep 9710735 = 14566103) B14566103
theorem B1420703 : Blo 944585 1420703 := bstep (se 1 (by rfl) ⟨1065527, by rfl⟩ : syracuseStep 1420703 = 2131055) B2131055
theorem B4796009 : Blo 944585 4796009 := bstep (se 2 (by rfl) ⟨1798503, by rfl⟩ : syracuseStep 4796009 = 3597007) B3597007
theorem B1420967 : Blo 944585 1420967 := bstep (se 1 (by rfl) ⟨1065725, by rfl⟩ : syracuseStep 1420967 = 2131451) B2131451
theorem B1420991 : Blo 944585 1420991 := bstep (se 1 (by rfl) ⟨1065743, by rfl⟩ : syracuseStep 1420991 = 2131487) B2131487
theorem B1421087 : Blo 944585 1421087 := bstep (se 1 (by rfl) ⟨1065815, by rfl⟩ : syracuseStep 1421087 = 2131631) B2131631
theorem B1421375 : Blo 944585 1421375 := bstep (se 1 (by rfl) ⟨1066031, by rfl⟩ : syracuseStep 1421375 = 2132063) B2132063
theorem B1421567 : Blo 944585 1421567 := bstep (se 1 (by rfl) ⟨1066175, by rfl⟩ : syracuseStep 1421567 = 2132351) B2132351
theorem B22425893 : Blo 944585 22425893 := bstep (se 4 (by rfl) ⟨2102427, by rfl⟩ : syracuseStep 22425893 = 4204855) B4204855
theorem B1421609 : Blo 944585 1421609 := bstep (se 2 (by rfl) ⟨533103, by rfl⟩ : syracuseStep 1421609 = 1066207) B1066207
theorem B1421879 : Blo 944585 1421879 := bstep (se 1 (by rfl) ⟨1066409, by rfl⟩ : syracuseStep 1421879 = 2132819) B2132819
theorem B1422119 : Blo 944585 1422119 := bstep (se 1 (by rfl) ⟨1066589, by rfl⟩ : syracuseStep 1422119 = 2133179) B2133179
theorem B1422239 : Blo 944585 1422239 := bstep (se 1 (by rfl) ⟨1066679, by rfl⟩ : syracuseStep 1422239 = 2133359) B2133359
theorem B5387219 : Blo 944585 5387219 := bstep (se 1 (by rfl) ⟨4040414, by rfl⟩ : syracuseStep 5387219 = 8080829) B8080829
theorem B1422713 : Blo 944585 1422713 := bstep (se 2 (by rfl) ⟨533517, by rfl⟩ : syracuseStep 1422713 = 1067035) B1067035
theorem B1422719 : Blo 944585 1422719 := bstep (se 1 (by rfl) ⟨1067039, by rfl⟩ : syracuseStep 1422719 = 2134079) B2134079
theorem B1422875 : Blo 944585 1422875 := bstep (se 1 (by rfl) ⟨1067156, by rfl⟩ : syracuseStep 1422875 = 2134313) B2134313
theorem B1063471 : Blo 944585 1063471 := bstep (se 1 (by rfl) ⟨797603, by rfl⟩ : syracuseStep 1063471 = 1595207) B1595207
theorem B4045403 : Blo 944585 4045403 := bstep (se 1 (by rfl) ⟨3034052, by rfl⟩ : syracuseStep 4045403 = 6068105) B6068105
theorem B5127731 : Blo 944585 5127731 := bstep (se 1 (by rfl) ⟨3845798, by rfl⟩ : syracuseStep 5127731 = 7691597) B7691597
theorem B52411961 : Blo 944585 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B3587759 : Blo 944585 3587759 := bstep (se 1 (by rfl) ⟨2690819, by rfl⟩ : syracuseStep 3587759 = 5381639) B5381639
theorem B5390135 : Blo 944585 5390135 := bstep (se 1 (by rfl) ⟨4042601, by rfl⟩ : syracuseStep 5390135 = 8085203) B8085203
theorem B3194963 : Blo 944585 3194963 := bstep (se 1 (by rfl) ⟨2396222, by rfl⟩ : syracuseStep 3194963 = 4792445) B4792445
theorem B3195017 : Blo 944585 3195017 := bstep (se 2 (by rfl) ⟨1198131, by rfl⟩ : syracuseStep 3195017 = 2396263) B2396263
theorem B4047353 : Blo 944585 4047353 := bstep (se 2 (by rfl) ⟨1517757, by rfl⟩ : syracuseStep 4047353 = 3035515) B3035515
theorem B3195503 : Blo 944585 3195503 := bstep (se 1 (by rfl) ⟨2396627, by rfl⟩ : syracuseStep 3195503 = 4793255) B4793255
theorem B24560273 : Blo 944585 24560273 := bstep (se 2 (by rfl) ⟨9210102, by rfl⟩ : syracuseStep 24560273 = 18420205) B18420205
theorem B1196795 : Blo 944585 1196795 := bstep (se 1 (by rfl) ⟨897596, by rfl⟩ : syracuseStep 1196795 = 1795193) B1795193
theorem B3195773 : Blo 944585 3195773 := bstep (se 3 (by rfl) ⟨599207, by rfl⟩ : syracuseStep 3195773 = 1198415) B1198415
theorem B91146131 : Blo 944585 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B20465945 : Blo 944585 20465945 := bstep (se 2 (by rfl) ⟨7674729, by rfl⟩ : syracuseStep 20465945 = 15349459) B15349459
theorem B12962105 : Blo 944585 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B2018047 : Blo 944585 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B3590993 : Blo 944585 3590993 := bstep (se 2 (by rfl) ⟨1346622, by rfl⟩ : syracuseStep 3590993 = 2693245) B2693245
theorem B6474593 : Blo 944585 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B10767329 : Blo 944585 10767329 := bstep (se 2 (by rfl) ⟨4037748, by rfl⟩ : syracuseStep 10767329 = 8075497) B8075497
theorem B13651163 : Blo 944585 13651163 := bstep (se 1 (by rfl) ⟨10238372, by rfl⟩ : syracuseStep 13651163 = 20476745) B20476745
theorem B3886703 : Blo 944585 3886703 := bstep (se 1 (by rfl) ⟨2915027, by rfl⟩ : syracuseStep 3886703 = 5830055) B5830055
theorem B9719689 : Blo 944585 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B3198959 : Blo 944585 3198959 := bstep (se 1 (by rfl) ⟨2399219, by rfl⟩ : syracuseStep 3198959 = 4798439) B4798439
theorem B1922015 : Blo 944585 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B10802321 : Blo 944585 10802321 := bstep (se 2 (by rfl) ⟨4050870, by rfl⟩ : syracuseStep 10802321 = 8101741) B8101741
theorem B1594633 : Blo 944585 1594633 := bstep (se 2 (by rfl) ⟨597987, by rfl⟩ : syracuseStep 1594633 = 1195975) B1195975
theorem B31119491 : Blo 944585 31119491 := bstep (se 1 (by rfl) ⟨23339618, by rfl⟩ : syracuseStep 31119491 = 46679237) B46679237
theorem B2218279 : Blo 944585 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2021831 : Blo 944585 2021831 := bstep (se 1 (by rfl) ⟨1516373, by rfl⟩ : syracuseStep 2021831 = 3032747) B3032747
theorem B5396969 : Blo 944585 5396969 := bstep (se 2 (by rfl) ⟨2023863, by rfl⟩ : syracuseStep 5396969 = 4047727) B4047727
theorem B5397151 : Blo 944585 5397151 := bstep (se 1 (by rfl) ⟨4047863, by rfl⟩ : syracuseStep 5397151 = 8095727) B8095727
theorem B1137343 : Blo 944585 1137343 := bstep (se 1 (by rfl) ⟨853007, by rfl⟩ : syracuseStep 1137343 = 1706015) B1706015
theorem B2022079 : Blo 944585 2022079 := bstep (se 1 (by rfl) ⟨1516559, by rfl⟩ : syracuseStep 2022079 = 3033119) B3033119
theorem B2022121 : Blo 944585 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B3037949 : Blo 944585 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B1596199 : Blo 944585 1596199 := bstep (se 1 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 1596199 = 2394299) B2394299
theorem B1137511 : Blo 944585 1137511 := bstep (se 1 (by rfl) ⟨853133, by rfl⟩ : syracuseStep 1137511 = 1706267) B1706267
theorem B12147691 : Blo 944585 12147691 := bstep (se 1 (by rfl) ⟨9110768, by rfl⟩ : syracuseStep 12147691 = 18221537) B18221537
theorem B8084519 : Blo 944585 8084519 := bstep (se 1 (by rfl) ⟨6063389, by rfl⟩ : syracuseStep 8084519 = 12126779) B12126779
theorem B41016455 : Blo 944585 41016455 := bstep (se 1 (by rfl) ⟨30762341, by rfl⟩ : syracuseStep 41016455 = 61524683) B61524683
theorem B1793249 : Blo 944585 1793249 := bstep (se 2 (by rfl) ⟨672468, by rfl⟩ : syracuseStep 1793249 = 1344937) B1344937
theorem B1597151 : Blo 944585 1597151 := bstep (se 1 (by rfl) ⟨1197863, by rfl⟩ : syracuseStep 1597151 = 2395727) B2395727
theorem B5398427 : Blo 944585 5398427 := bstep (se 1 (by rfl) ⟨4048820, by rfl⟩ : syracuseStep 5398427 = 8097641) B8097641
theorem B1368991 : Blo 944585 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B1598447 : Blo 944585 1598447 := bstep (se 1 (by rfl) ⟨1198835, by rfl⟩ : syracuseStep 1598447 = 2397671) B2397671
theorem B126084313 : Blo 944585 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B3597767 : Blo 944585 3597767 := bstep (se 1 (by rfl) ⟨2698325, by rfl⟩ : syracuseStep 3597767 = 5396651) B5396651
theorem B944615 : Blo 944585 944615 := bstep (se 1 (by rfl) ⟨708461, by rfl⟩ : syracuseStep 944615 = 1416923) B1416923
theorem B6482423 : Blo 944585 6482423 := bstep (se 1 (by rfl) ⟨4861817, by rfl⟩ : syracuseStep 6482423 = 9723635) B9723635
theorem B944795 : Blo 944585 944795 := bstep (se 1 (by rfl) ⟨708596, by rfl⟩ : syracuseStep 944795 = 1417193) B1417193
theorem B1436537 : Blo 944585 1436537 := bstep (se 2 (by rfl) ⟨538701, by rfl⟩ : syracuseStep 1436537 = 1077403) B1077403
theorem B945263 : Blo 944585 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B945343 : Blo 944585 945343 := bstep (se 1 (by rfl) ⟨709007, by rfl⟩ : syracuseStep 945343 = 1418015) B1418015
theorem B945359 : Blo 944585 945359 := bstep (se 1 (by rfl) ⟨709019, by rfl⟩ : syracuseStep 945359 = 1418039) B1418039
theorem B945479 : Blo 944585 945479 := bstep (se 1 (by rfl) ⟨709109, by rfl⟩ : syracuseStep 945479 = 1418219) B1418219
theorem B1797851 : Blo 944585 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B946207 : Blo 944585 946207 := bstep (se 1 (by rfl) ⟨709655, by rfl⟩ : syracuseStep 946207 = 1419311) B1419311
theorem B6058111 : Blo 944585 6058111 := bstep (se 1 (by rfl) ⟨4543583, by rfl⟩ : syracuseStep 6058111 = 9087167) B9087167
theorem B5107855 : Blo 944585 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B946383 : Blo 944585 946383 := bstep (se 1 (by rfl) ⟨709787, by rfl⟩ : syracuseStep 946383 = 1419575) B1419575
theorem B3600683 : Blo 944585 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B946503 : Blo 944585 946503 := bstep (se 1 (by rfl) ⟨709877, by rfl⟩ : syracuseStep 946503 = 1419755) B1419755
theorem B9106121 : Blo 944585 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B946971 : Blo 944585 946971 := bstep (se 1 (by rfl) ⟨710228, by rfl⟩ : syracuseStep 946971 = 1420457) B1420457
theorem B947247 : Blo 944585 947247 := bstep (se 1 (by rfl) ⟨710435, by rfl⟩ : syracuseStep 947247 = 1420871) B1420871
theorem B1799263 : Blo 944585 1799263 := bstep (se 1 (by rfl) ⟨1349447, by rfl⟩ : syracuseStep 1799263 = 2698895) B2698895
theorem B2126969 : Blo 944585 2126969 := bstep (se 2 (by rfl) ⟨797613, by rfl⟩ : syracuseStep 2126969 = 1595227) B1595227
theorem B947367 : Blo 944585 947367 := bstep (se 1 (by rfl) ⟨710525, by rfl⟩ : syracuseStep 947367 = 1421051) B1421051
theorem B12154049 : Blo 944585 12154049 := bstep (se 2 (by rfl) ⟨4557768, by rfl⟩ : syracuseStep 12154049 = 9115537) B9115537
theorem B15332647 : Blo 944585 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B6911339 : Blo 944585 6911339 := bstep (se 1 (by rfl) ⟨5183504, by rfl⟩ : syracuseStep 6911339 = 10367009) B10367009
theorem B4322747 : Blo 944585 4322747 := bstep (se 1 (by rfl) ⟨3242060, by rfl⟩ : syracuseStep 4322747 = 6484121) B6484121
theorem B947815 : Blo 944585 947815 := bstep (se 1 (by rfl) ⟨710861, by rfl⟩ : syracuseStep 947815 = 1421723) B1421723
theorem B12121811 : Blo 944585 12121811 := bstep (se 1 (by rfl) ⟨9091358, by rfl⟩ : syracuseStep 12121811 = 18182717) B18182717
theorem B1537883 : Blo 944585 1537883 := bstep (se 1 (by rfl) ⟨1153412, by rfl⟩ : syracuseStep 1537883 = 2306825) B2306825
theorem B2127743 : Blo 944585 2127743 := bstep (se 1 (by rfl) ⟨1595807, by rfl⟩ : syracuseStep 2127743 = 3191615) B3191615
theorem B948095 : Blo 944585 948095 := bstep (se 1 (by rfl) ⟨711071, by rfl⟩ : syracuseStep 948095 = 1422143) B1422143
theorem B948191 : Blo 944585 948191 := bstep (se 1 (by rfl) ⟨711143, by rfl⟩ : syracuseStep 948191 = 1422287) B1422287
theorem B948219 : Blo 944585 948219 := bstep (se 1 (by rfl) ⟨711164, by rfl⟩ : syracuseStep 948219 = 1422329) B1422329
theorem B948251 : Blo 944585 948251 := bstep (se 1 (by rfl) ⟨711188, by rfl⟩ : syracuseStep 948251 = 1422377) B1422377
theorem B6158377 : Blo 944585 6158377 := bstep (se 2 (by rfl) ⟨2309391, by rfl⟩ : syracuseStep 6158377 = 4618783) B4618783
theorem B948271 : Blo 944585 948271 := bstep (se 1 (by rfl) ⟨711203, by rfl⟩ : syracuseStep 948271 = 1422407) B1422407
theorem B3078283 : Blo 944585 3078283 := bstep (se 1 (by rfl) ⟨2308712, by rfl⟩ : syracuseStep 3078283 = 4617425) B4617425
theorem B948391 : Blo 944585 948391 := bstep (se 1 (by rfl) ⟨711293, by rfl⟩ : syracuseStep 948391 = 1422587) B1422587
theorem B2128211 : Blo 944585 2128211 := bstep (se 1 (by rfl) ⟨1596158, by rfl⟩ : syracuseStep 2128211 = 3192317) B3192317
theorem B4324187 : Blo 944585 4324187 := bstep (se 1 (by rfl) ⟨3243140, by rfl⟩ : syracuseStep 4324187 = 6486281) B6486281
theorem B2128751 : Blo 944585 2128751 := bstep (se 1 (by rfl) ⟨1596563, by rfl⟩ : syracuseStep 2128751 = 3193127) B3193127
theorem B4553927 : Blo 944585 4553927 := bstep (se 1 (by rfl) ⟨3415445, by rfl⟩ : syracuseStep 4553927 = 6830891) B6830891
theorem B2391403 : Blo 944585 2391403 := bstep (se 1 (by rfl) ⟨1793552, by rfl⟩ : syracuseStep 2391403 = 3587105) B3587105
theorem B6815087 : Blo 944585 6815087 := bstep (se 1 (by rfl) ⟨5111315, by rfl⟩ : syracuseStep 6815087 = 10222631) B10222631
theorem B2129399 : Blo 944585 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B4783859 : Blo 944585 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B2392051 : Blo 944585 2392051 := bstep (se 1 (by rfl) ⟨1794038, by rfl⟩ : syracuseStep 2392051 = 3588077) B3588077
theorem B2129975 : Blo 944585 2129975 := bstep (se 1 (by rfl) ⟨1597481, by rfl⟩ : syracuseStep 2129975 = 3194963) B3194963
theorem B2130011 : Blo 944585 2130011 := bstep (se 1 (by rfl) ⟨1597508, by rfl⟩ : syracuseStep 2130011 = 3195017) B3195017
theorem B2130335 : Blo 944585 2130335 := bstep (se 1 (by rfl) ⟨1597751, by rfl⟩ : syracuseStep 2130335 = 3195503) B3195503
theorem B7275055 : Blo 944585 7275055 := bstep (se 1 (by rfl) ⟨5456291, by rfl⟩ : syracuseStep 7275055 = 10912583) B10912583
theorem B2130515 : Blo 944585 2130515 := bstep (se 1 (by rfl) ⟨1597886, by rfl⟩ : syracuseStep 2130515 = 3195773) B3195773
theorem B103581173 : Blo 944585 103581173 := bstep (se 5 (by rfl) ⟨4855367, by rfl⟩ : syracuseStep 103581173 = 9710735) B9710735
theorem B2393995 : Blo 944585 2393995 := bstep (se 1 (by rfl) ⟨1795496, by rfl⟩ : syracuseStep 2393995 = 3590993) B3590993
theorem B7178219 : Blo 944585 7178219 := bstep (se 1 (by rfl) ⟨5383664, by rfl⟩ : syracuseStep 7178219 = 10767329) B10767329
theorem B7669799 : Blo 944585 7669799 := bstep (se 1 (by rfl) ⟨5752349, by rfl⟩ : syracuseStep 7669799 = 11504699) B11504699
theorem B2591135 : Blo 944585 2591135 := bstep (se 1 (by rfl) ⟨1943351, by rfl⟩ : syracuseStep 2591135 = 3886703) B3886703
theorem B2132639 : Blo 944585 2132639 := bstep (se 1 (by rfl) ⟨1599479, by rfl⟩ : syracuseStep 2132639 = 3198959) B3198959
theorem B5049299 : Blo 944585 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B1281343 : Blo 944585 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B5115275 : Blo 944585 5115275 := bstep (se 1 (by rfl) ⟨3836456, by rfl⟩ : syracuseStep 5115275 = 7672913) B7672913
theorem B17305001 : Blo 944585 17305001 := bstep (se 2 (by rfl) ⟨6489375, by rfl⟩ : syracuseStep 17305001 = 12978751) B12978751
theorem B5115383 : Blo 944585 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B2690671 : Blo 944585 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B2690729 : Blo 944585 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B20746327 : Blo 944585 20746327 := bstep (se 1 (by rfl) ⟨15559745, by rfl⟩ : syracuseStep 20746327 = 31119491) B31119491
theorem B1347887 : Blo 944585 1347887 := bstep (se 1 (by rfl) ⟨1010915, by rfl⟩ : syracuseStep 1347887 = 2021831) B2021831
theorem B5248543 : Blo 944585 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B53155831 : Blo 944585 53155831 := bstep (se 1 (by rfl) ⟨39866873, by rfl⟩ : syracuseStep 53155831 = 79733747) B79733747
theorem B2398511 : Blo 944585 2398511 := bstep (se 1 (by rfl) ⟨1798883, by rfl⟩ : syracuseStep 2398511 = 3597767) B3597767
theorem B2399017 : Blo 944585 2399017 := bstep (se 2 (by rfl) ⟨899631, by rfl⟩ : syracuseStep 2399017 = 1799263) B1799263
theorem B10787741 : Blo 944585 10787741 := bstep (se 3 (by rfl) ⟨2022701, by rfl⟩ : syracuseStep 10787741 = 4045403) B4045403
theorem B957691 : Blo 944585 957691 := bstep (se 1 (by rfl) ⟨718268, by rfl⟩ : syracuseStep 957691 = 1436537) B1436537
theorem B4104377 : Blo 944585 4104377 := bstep (se 2 (by rfl) ⟨1539141, by rfl⟩ : syracuseStep 4104377 = 3078283) B3078283
theorem B14950595 : Blo 944585 14950595 := bstep (se 1 (by rfl) ⟨11212946, by rfl⟩ : syracuseStep 14950595 = 22425893) B22425893
theorem B2400455 : Blo 944585 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B2957705 : Blo 944585 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B6070747 : Blo 944585 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B1417961 : Blo 944585 1417961 := bstep (se 2 (by rfl) ⟨531735, by rfl⟩ : syracuseStep 1417961 = 1063471) B1063471
theorem B1417979 : Blo 944585 1417979 := bstep (se 1 (by rfl) ⟨1063484, by rfl⟩ : syracuseStep 1417979 = 2126969) B2126969
theorem B8102699 : Blo 944585 8102699 := bstep (se 1 (by rfl) ⟨6077024, by rfl⟩ : syracuseStep 8102699 = 12154049) B12154049
theorem B1516457 : Blo 944585 1516457 := bstep (se 2 (by rfl) ⟨568671, by rfl⟩ : syracuseStep 1516457 = 1137343) B1137343
theorem B2696105 : Blo 944585 2696105 := bstep (se 2 (by rfl) ⟨1011039, by rfl⟩ : syracuseStep 2696105 = 2022079) B2022079
theorem B2696161 : Blo 944585 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B1516681 : Blo 944585 1516681 := bstep (se 2 (by rfl) ⟨568755, by rfl⟩ : syracuseStep 1516681 = 1137511) B1137511
theorem B1025255 : Blo 944585 1025255 := bstep (se 1 (by rfl) ⟨768941, by rfl⟩ : syracuseStep 1025255 = 1537883) B1537883
theorem B1418495 : Blo 944585 1418495 := bstep (se 1 (by rfl) ⟨1063871, by rfl⟩ : syracuseStep 1418495 = 2127743) B2127743
theorem B16196921 : Blo 944585 16196921 := bstep (se 2 (by rfl) ⟨6073845, by rfl⟩ : syracuseStep 16196921 = 12147691) B12147691
theorem B1418807 : Blo 944585 1418807 := bstep (se 1 (by rfl) ⟨1064105, by rfl⟩ : syracuseStep 1418807 = 2128211) B2128211
theorem B3188537 : Blo 944585 3188537 := bstep (se 2 (by rfl) ⟨1195701, by rfl⟩ : syracuseStep 3188537 = 2391403) B2391403
theorem B1419167 : Blo 944585 1419167 := bstep (se 1 (by rfl) ⟨1064375, by rfl⟩ : syracuseStep 1419167 = 2128751) B2128751
theorem B9709757 : Blo 944585 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B1419599 : Blo 944585 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B3418487 : Blo 944585 3418487 := bstep (se 1 (by rfl) ⟨2563865, by rfl⟩ : syracuseStep 3418487 = 5127731) B5127731
theorem B34941307 : Blo 944585 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B3189239 : Blo 944585 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B3189401 : Blo 944585 3189401 := bstep (se 2 (by rfl) ⟨1196025, by rfl⟩ : syracuseStep 3189401 = 2392051) B2392051
theorem B1420031 : Blo 944585 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B2698235 : Blo 944585 2698235 := bstep (se 1 (by rfl) ⟨2023676, by rfl⟩ : syracuseStep 2698235 = 4047353) B4047353
theorem B18459859 : Blo 944585 18459859 := bstep (se 1 (by rfl) ⟨13844894, by rfl⟩ : syracuseStep 18459859 = 27689789) B27689789
theorem B3190427 : Blo 944585 3190427 := bstep (se 1 (by rfl) ⟨2392820, by rfl⟩ : syracuseStep 3190427 = 4785641) B4785641
theorem B1421135 : Blo 944585 1421135 := bstep (se 1 (by rfl) ⟨1065851, by rfl⟩ : syracuseStep 1421135 = 2131703) B2131703
theorem B60764087 : Blo 944585 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B1421255 : Blo 944585 1421255 := bstep (se 1 (by rfl) ⟨1065941, by rfl⟩ : syracuseStep 1421255 = 2131883) B2131883
theorem B13643963 : Blo 944585 13643963 := bstep (se 1 (by rfl) ⟨10232972, by rfl⟩ : syracuseStep 13643963 = 20465945) B20465945
theorem B168112417 : Blo 944585 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B1421615 : Blo 944585 1421615 := bstep (se 1 (by rfl) ⟨1066211, by rfl⟩ : syracuseStep 1421615 = 2132423) B2132423
theorem B7778749 : Blo 944585 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B1421855 : Blo 944585 1421855 := bstep (se 1 (by rfl) ⟨1066391, by rfl⟩ : syracuseStep 1421855 = 2132783) B2132783
theorem B3191453 : Blo 944585 3191453 := bstep (se 3 (by rfl) ⟨598397, by rfl⟩ : syracuseStep 3191453 = 1196795) B1196795
theorem B3191561 : Blo 944585 3191561 := bstep (se 2 (by rfl) ⟨1196835, by rfl⟩ : syracuseStep 3191561 = 2393671) B2393671
theorem B1422203 : Blo 944585 1422203 := bstep (se 1 (by rfl) ⟨1066652, by rfl⟩ : syracuseStep 1422203 = 2133305) B2133305
theorem B1422383 : Blo 944585 1422383 := bstep (se 1 (by rfl) ⟨1066787, by rfl⟩ : syracuseStep 1422383 = 2133575) B2133575
theorem B1422503 : Blo 944585 1422503 := bstep (se 1 (by rfl) ⟨1066877, by rfl⟩ : syracuseStep 1422503 = 2133755) B2133755
theorem B1422647 : Blo 944585 1422647 := bstep (se 1 (by rfl) ⟨1066985, by rfl⟩ : syracuseStep 1422647 = 2133971) B2133971
theorem B1422827 : Blo 944585 1422827 := bstep (se 1 (by rfl) ⟨1067120, by rfl⟩ : syracuseStep 1422827 = 2134241) B2134241
theorem B6076079 : Blo 944585 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B18430237 : Blo 944585 18430237 := bstep (se 3 (by rfl) ⟨3455669, by rfl⟩ : syracuseStep 18430237 = 6911339) B6911339
theorem B5389679 : Blo 944585 5389679 := bstep (se 1 (by rfl) ⟨4042259, by rfl⟩ : syracuseStep 5389679 = 8084519) B8084519
theorem B27344303 : Blo 944585 27344303 := bstep (se 1 (by rfl) ⟨20508227, by rfl⟩ : syracuseStep 27344303 = 41016455) B41016455
theorem B1195499 : Blo 944585 1195499 := bstep (se 1 (by rfl) ⟨896624, by rfl⟩ : syracuseStep 1195499 = 1793249) B1793249
theorem B1064767 : Blo 944585 1064767 := bstep (se 1 (by rfl) ⟨798575, by rfl⟩ : syracuseStep 1064767 = 1597151) B1597151
theorem B12959585 : Blo 944585 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B3588047 : Blo 944585 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B113688643 : Blo 944585 113688643 := bstep (se 1 (by rfl) ⟨85266482, by rfl⟩ : syracuseStep 113688643 = 170532965) B170532965
theorem B8077481 : Blo 944585 8077481 := bstep (se 2 (by rfl) ⟨3029055, by rfl⟩ : syracuseStep 8077481 = 6058111) B6058111
theorem B3195179 : Blo 944585 3195179 := bstep (se 1 (by rfl) ⟨2396384, by rfl⟩ : syracuseStep 3195179 = 4792769) B4792769
theorem B1065631 : Blo 944585 1065631 := bstep (se 1 (by rfl) ⟨799223, by rfl⟩ : syracuseStep 1065631 = 1598447) B1598447
theorem B3195611 : Blo 944585 3195611 := bstep (se 1 (by rfl) ⟨2396708, by rfl⟩ : syracuseStep 3195611 = 4793417) B4793417
theorem B3196043 : Blo 944585 3196043 := bstep (se 1 (by rfl) ⟨2397032, by rfl⟩ : syracuseStep 3196043 = 4794065) B4794065
theorem B98158301 : Blo 944585 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B3590203 : Blo 944585 3590203 := bstep (se 1 (by rfl) ⟨2692652, by rfl⟩ : syracuseStep 3590203 = 5385305) B5385305
theorem B3197339 : Blo 944585 3197339 := bstep (se 1 (by rfl) ⟨2398004, by rfl⟩ : syracuseStep 3197339 = 4796009) B4796009
theorem B1198567 : Blo 944585 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B8211169 : Blo 944585 8211169 := bstep (se 2 (by rfl) ⟨3079188, by rfl⟩ : syracuseStep 8211169 = 6158377) B6158377
theorem B3591479 : Blo 944585 3591479 := bstep (se 1 (by rfl) ⟨2693609, by rfl⟩ : syracuseStep 3591479 = 5387219) B5387219
theorem B20762081 : Blo 944585 20762081 := bstep (se 2 (by rfl) ⟨7785780, by rfl⟩ : syracuseStep 20762081 = 15571561) B15571561
theorem B7196201 : Blo 944585 7196201 := bstep (se 2 (by rfl) ⟨2698575, by rfl⟩ : syracuseStep 7196201 = 5397151) B5397151
theorem B8081207 : Blo 944585 8081207 := bstep (se 1 (by rfl) ⟨6060905, by rfl⟩ : syracuseStep 8081207 = 12121811) B12121811
theorem B3035951 : Blo 944585 3035951 := bstep (se 1 (by rfl) ⟨2276963, by rfl⟩ : syracuseStep 3035951 = 4553927) B4553927
theorem B4543391 : Blo 944585 4543391 := bstep (se 1 (by rfl) ⟨3407543, by rfl⟩ : syracuseStep 4543391 = 6815087) B6815087
theorem B3593423 : Blo 944585 3593423 := bstep (se 1 (by rfl) ⟨2695067, by rfl⟩ : syracuseStep 3593423 = 5390135) B5390135
theorem B3233191 : Blo 944585 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B1595119 : Blo 944585 1595119 := bstep (se 1 (by rfl) ⟨1196339, by rfl⟩ : syracuseStep 1595119 = 2392679) B2392679
theorem B16373515 : Blo 944585 16373515 := bstep (se 1 (by rfl) ⟨12280136, by rfl⟩ : syracuseStep 16373515 = 24560273) B24560273
theorem B4675367 : Blo 944585 4675367 := bstep (se 1 (by rfl) ⟨3506525, by rfl⟩ : syracuseStep 4675367 = 7013051) B7013051
theorem B46028695 : Blo 944585 46028695 := bstep (se 1 (by rfl) ⟨34521521, by rfl⟩ : syracuseStep 46028695 = 69043043) B69043043
theorem B3595049 : Blo 944585 3595049 := bstep (se 2 (by rfl) ⟨1348143, by rfl⟩ : syracuseStep 3595049 = 2696287) B2696287
theorem B8641403 : Blo 944585 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B9100313 : Blo 944585 9100313 := bstep (se 2 (by rfl) ⟨3412617, by rfl⟩ : syracuseStep 9100313 = 6825235) B6825235
theorem B1596523 : Blo 944585 1596523 := bstep (se 1 (by rfl) ⟨1197392, by rfl⟩ : syracuseStep 1596523 = 2394785) B2394785
theorem B9100775 : Blo 944585 9100775 := bstep (se 1 (by rfl) ⟨6825581, by rfl⟩ : syracuseStep 9100775 = 13651163) B13651163
theorem B1793515 : Blo 944585 1793515 := bstep (se 1 (by rfl) ⟨1345136, by rfl⟩ : syracuseStep 1793515 = 2690273) B2690273
theorem B7201547 : Blo 944585 7201547 := bstep (se 1 (by rfl) ⟨5401160, by rfl⟩ : syracuseStep 7201547 = 10802321) B10802321
theorem B6054983 : Blo 944585 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B1598555 : Blo 944585 1598555 := bstep (se 1 (by rfl) ⟨1198916, by rfl⟩ : syracuseStep 1598555 = 2397833) B2397833
theorem B1598575 : Blo 944585 1598575 := bstep (se 1 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 1598575 = 2397863) B2397863
theorem B1795375 : Blo 944585 1795375 := bstep (se 1 (by rfl) ⟨1346531, by rfl⟩ : syracuseStep 1795375 = 2693063) B2693063
theorem B3597979 : Blo 944585 3597979 := bstep (se 1 (by rfl) ⟨2698484, by rfl⟩ : syracuseStep 3597979 = 5396969) B5396969
theorem B2025299 : Blo 944585 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B7301285 : Blo 944585 7301285 := bstep (se 4 (by rfl) ⟨684495, by rfl⟩ : syracuseStep 7301285 = 1368991) B1368991
theorem B1796393 : Blo 944585 1796393 := bstep (se 2 (by rfl) ⟨673647, by rfl⟩ : syracuseStep 1796393 = 1347295) B1347295
theorem B1796431 : Blo 944585 1796431 := bstep (se 1 (by rfl) ⟨1347323, by rfl⟩ : syracuseStep 1796431 = 2694647) B2694647
theorem B944623 : Blo 944585 944623 := bstep (se 1 (by rfl) ⟨708467, by rfl⟩ : syracuseStep 944623 = 1416935) B1416935
theorem B3598951 : Blo 944585 3598951 := bstep (se 1 (by rfl) ⟨2699213, by rfl⟩ : syracuseStep 3598951 = 5398427) B5398427
theorem B944807 : Blo 944585 944807 := bstep (se 1 (by rfl) ⟨708605, by rfl⟩ : syracuseStep 944807 = 1417211) B1417211
theorem B944847 : Blo 944585 944847 := bstep (se 1 (by rfl) ⟨708635, by rfl⟩ : syracuseStep 944847 = 1417271) B1417271
theorem B944927 : Blo 944585 944927 := bstep (se 1 (by rfl) ⟨708695, by rfl⟩ : syracuseStep 944927 = 1417391) B1417391
theorem B6810473 : Blo 944585 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B945063 : Blo 944585 945063 := bstep (se 1 (by rfl) ⟨708797, by rfl⟩ : syracuseStep 945063 = 1417595) B1417595
theorem B1010599 : Blo 944585 1010599 := bstep (se 1 (by rfl) ⟨757949, by rfl⟩ : syracuseStep 1010599 = 1515899) B1515899
theorem B945179 : Blo 944585 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B945243 : Blo 944585 945243 := bstep (se 1 (by rfl) ⟨708932, by rfl⟩ : syracuseStep 945243 = 1417865) B1417865
theorem B945383 : Blo 944585 945383 := bstep (se 1 (by rfl) ⟨709037, by rfl⟩ : syracuseStep 945383 = 1418075) B1418075
theorem B945407 : Blo 944585 945407 := bstep (se 1 (by rfl) ⟨709055, by rfl⟩ : syracuseStep 945407 = 1418111) B1418111
theorem B945455 : Blo 944585 945455 := bstep (se 1 (by rfl) ⟨709091, by rfl⟩ : syracuseStep 945455 = 1418183) B1418183
theorem B945599 : Blo 944585 945599 := bstep (se 1 (by rfl) ⟨709199, by rfl⟩ : syracuseStep 945599 = 1418399) B1418399
theorem B945695 : Blo 944585 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B945823 : Blo 944585 945823 := bstep (se 1 (by rfl) ⟨709367, by rfl⟩ : syracuseStep 945823 = 1418735) B1418735
theorem B945831 : Blo 944585 945831 := bstep (se 1 (by rfl) ⟨709373, by rfl⟩ : syracuseStep 945831 = 1418747) B1418747
theorem B945855 : Blo 944585 945855 := bstep (se 1 (by rfl) ⟨709391, by rfl⟩ : syracuseStep 945855 = 1418783) B1418783
theorem B945951 : Blo 944585 945951 := bstep (se 1 (by rfl) ⟨709463, by rfl⟩ : syracuseStep 945951 = 1418927) B1418927
theorem B946011 : Blo 944585 946011 := bstep (se 1 (by rfl) ⟨709508, by rfl⟩ : syracuseStep 946011 = 1419017) B1419017
theorem B946031 : Blo 944585 946031 := bstep (se 1 (by rfl) ⟨709523, by rfl⟩ : syracuseStep 946031 = 1419047) B1419047
theorem B2125979 : Blo 944585 2125979 := bstep (se 1 (by rfl) ⟨1594484, by rfl⟩ : syracuseStep 2125979 = 3188969) B3188969
theorem B946431 : Blo 944585 946431 := bstep (se 1 (by rfl) ⟨709823, by rfl⟩ : syracuseStep 946431 = 1419647) B1419647
theorem B4321615 : Blo 944585 4321615 := bstep (se 1 (by rfl) ⟨3241211, by rfl⟩ : syracuseStep 4321615 = 6482423) B6482423
theorem B2126177 : Blo 944585 2126177 := bstep (se 2 (by rfl) ⟨797316, by rfl⟩ : syracuseStep 2126177 = 1594633) B1594633
theorem B20443529 : Blo 944585 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B946591 : Blo 944585 946591 := bstep (se 1 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 946591 = 1419887) B1419887
theorem B946735 : Blo 944585 946735 := bstep (se 1 (by rfl) ⟨710051, by rfl⟩ : syracuseStep 946735 = 1420103) B1420103
theorem B17265581 : Blo 944585 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B947135 : Blo 944585 947135 := bstep (se 1 (by rfl) ⟨710351, by rfl⟩ : syracuseStep 947135 = 1420703) B1420703
theorem B947311 : Blo 944585 947311 := bstep (se 1 (by rfl) ⟨710483, by rfl⟩ : syracuseStep 947311 = 1420967) B1420967
theorem B947327 : Blo 944585 947327 := bstep (se 1 (by rfl) ⟨710495, by rfl⟩ : syracuseStep 947327 = 1420991) B1420991
theorem B947391 : Blo 944585 947391 := bstep (se 1 (by rfl) ⟨710543, by rfl⟩ : syracuseStep 947391 = 1421087) B1421087
theorem B947583 : Blo 944585 947583 := bstep (se 1 (by rfl) ⟨710687, by rfl⟩ : syracuseStep 947583 = 1421375) B1421375
theorem B947711 : Blo 944585 947711 := bstep (se 1 (by rfl) ⟨710783, by rfl⟩ : syracuseStep 947711 = 1421567) B1421567
theorem B947739 : Blo 944585 947739 := bstep (se 1 (by rfl) ⟨710804, by rfl⟩ : syracuseStep 947739 = 1421609) B1421609
theorem B947919 : Blo 944585 947919 := bstep (se 1 (by rfl) ⟨710939, by rfl⟩ : syracuseStep 947919 = 1421879) B1421879
theorem B948079 : Blo 944585 948079 := bstep (se 1 (by rfl) ⟨711059, by rfl⟩ : syracuseStep 948079 = 1422119) B1422119
theorem B948159 : Blo 944585 948159 := bstep (se 1 (by rfl) ⟨711119, by rfl⟩ : syracuseStep 948159 = 1422239) B1422239
theorem B1227847889 : Blo 944585 1227847889 := bstep (se 2 (by rfl) ⟨460442958, by rfl⟩ : syracuseStep 1227847889 = 920885917) B920885917
theorem B948475 : Blo 944585 948475 := bstep (se 1 (by rfl) ⟨711356, by rfl⟩ : syracuseStep 948475 = 1422713) B1422713
theorem B948479 : Blo 944585 948479 := bstep (se 1 (by rfl) ⟨711359, by rfl⟩ : syracuseStep 948479 = 1422719) B1422719
theorem B2881831 : Blo 944585 2881831 := bstep (se 1 (by rfl) ⟨2161373, by rfl⟩ : syracuseStep 2881831 = 4322747) B4322747
theorem B948583 : Blo 944585 948583 := bstep (se 1 (by rfl) ⟨711437, by rfl⟩ : syracuseStep 948583 = 1422875) B1422875
theorem B2128265 : Blo 944585 2128265 := bstep (se 2 (by rfl) ⟨798099, by rfl⟩ : syracuseStep 2128265 = 1596199) B1596199
theorem B2882791 : Blo 944585 2882791 := bstep (se 1 (by rfl) ⟨2162093, by rfl⟩ : syracuseStep 2882791 = 4324187) B4324187
theorem B332103401 : Blo 944585 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B2391839 : Blo 944585 2391839 := bstep (se 1 (by rfl) ⟨1793879, by rfl⟩ : syracuseStep 2391839 = 3587759) B3587759
theorem B151584857 : Blo 944585 151584857 := bstep (se 2 (by rfl) ⟨56844321, by rfl⟩ : syracuseStep 151584857 = 113688643) B113688643
theorem B2130119 : Blo 944585 2130119 := bstep (se 1 (by rfl) ⟨1597589, by rfl⟩ : syracuseStep 2130119 = 3195179) B3195179
theorem B2130407 : Blo 944585 2130407 := bstep (se 1 (by rfl) ⟨1597805, by rfl⟩ : syracuseStep 2130407 = 3195611) B3195611
theorem B8094329 : Blo 944585 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B9700073 : Blo 944585 9700073 := bstep (se 2 (by rfl) ⟨3637527, by rfl⟩ : syracuseStep 9700073 = 7275055) B7275055
theorem B2130695 : Blo 944585 2130695 := bstep (se 1 (by rfl) ⟨1598021, by rfl⟩ : syracuseStep 2130695 = 3196043) B3196043
theorem B65438867 : Blo 944585 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B4785479 : Blo 944585 4785479 := bstep (se 1 (by rfl) ⟨3589109, by rfl⟩ : syracuseStep 4785479 = 7178219) B7178219
theorem B5113199 : Blo 944585 5113199 := bstep (se 1 (by rfl) ⟨3834899, by rfl⟩ : syracuseStep 5113199 = 7669799) B7669799
theorem B2131433 : Blo 944585 2131433 := bstep (se 2 (by rfl) ⟨799287, by rfl⟩ : syracuseStep 2131433 = 1598575) B1598575
theorem B2131559 : Blo 944585 2131559 := bstep (se 1 (by rfl) ⟨1598669, by rfl⟩ : syracuseStep 2131559 = 3197339) B3197339
theorem B2393833 : Blo 944585 2393833 := bstep (se 2 (by rfl) ⟨897687, by rfl⟩ : syracuseStep 2393833 = 1795375) B1795375
theorem B2394319 : Blo 944585 2394319 := bstep (se 1 (by rfl) ⟨1795739, by rfl⟩ : syracuseStep 2394319 = 3591479) B3591479
theorem B3410183 : Blo 944585 3410183 := bstep (se 1 (by rfl) ⟨2557637, by rfl⟩ : syracuseStep 3410183 = 5115275) B5115275
theorem B11536667 : Blo 944585 11536667 := bstep (se 1 (by rfl) ⟨8652500, by rfl⟩ : syracuseStep 11536667 = 17305001) B17305001
theorem B3410255 : Blo 944585 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B4786937 : Blo 944585 4786937 := bstep (se 2 (by rfl) ⟨1795101, by rfl⟩ : syracuseStep 4786937 = 3590203) B3590203
theorem B2395241 : Blo 944585 2395241 := bstep (se 2 (by rfl) ⟨898215, by rfl⟩ : syracuseStep 2395241 = 1796431) B1796431
theorem B2395615 : Blo 944585 2395615 := bstep (se 1 (by rfl) ⟨1796711, by rfl⟩ : syracuseStep 2395615 = 3593423) B3593423
theorem B10948225 : Blo 944585 10948225 := bstep (se 2 (by rfl) ⟨4105584, by rfl⟩ : syracuseStep 10948225 = 8211169) B8211169
theorem B3116911 : Blo 944585 3116911 := bstep (se 1 (by rfl) ⟨2337683, by rfl⟩ : syracuseStep 3116911 = 4675367) B4675367
theorem B24613145 : Blo 944585 24613145 := bstep (se 2 (by rfl) ⟨9229929, by rfl⟩ : syracuseStep 24613145 = 18459859) B18459859
theorem B1708457 : Blo 944585 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B2396699 : Blo 944585 2396699 := bstep (se 1 (by rfl) ⟨1797524, by rfl⟩ : syracuseStep 2396699 = 3595049) B3595049
theorem B6066875 : Blo 944585 6066875 := bstep (se 1 (by rfl) ⟨4550156, by rfl⟩ : syracuseStep 6066875 = 9100313) B9100313
theorem B6067183 : Blo 944585 6067183 := bstep (se 1 (by rfl) ⟨4550387, by rfl⟩ : syracuseStep 6067183 = 9100775) B9100775
theorem B27661769 : Blo 944585 27661769 := bstep (se 2 (by rfl) ⟨10373163, by rfl⟩ : syracuseStep 27661769 = 20746327) B20746327
theorem B9967063 : Blo 944585 9967063 := bstep (se 1 (by rfl) ⟨7475297, by rfl⟩ : syracuseStep 9967063 = 14950595) B14950595
theorem B1971803 : Blo 944585 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B4036655 : Blo 944585 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B1350199 : Blo 944585 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B21831353 : Blo 944585 21831353 := bstep (se 2 (by rfl) ⟨8186757, by rfl⟩ : syracuseStep 21831353 = 16373515) B16373515
theorem B40509391 : Blo 944585 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B1417319 : Blo 944585 1417319 := bstep (se 1 (by rfl) ⟨1062989, by rfl⟩ : syracuseStep 1417319 = 2125979) B2125979
theorem B1417451 : Blo 944585 1417451 := bstep (se 1 (by rfl) ⟨1063088, by rfl⟩ : syracuseStep 1417451 = 2126177) B2126177
theorem B3842441 : Blo 944585 3842441 := bstep (se 2 (by rfl) ⟨1440915, by rfl⟩ : syracuseStep 3842441 = 2881831) B2881831
theorem B11510387 : Blo 944585 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B3187997 : Blo 944585 3187997 := bstep (se 3 (by rfl) ⟨597749, by rfl⟩ : syracuseStep 3187997 = 1195499) B1195499
theorem B1418843 : Blo 944585 1418843 := bstep (se 1 (by rfl) ⟨1064132, by rfl⟩ : syracuseStep 1418843 = 2128265) B2128265
theorem B3843721 : Blo 944585 3843721 := bstep (se 2 (by rfl) ⟨1441395, by rfl⟩ : syracuseStep 3843721 = 2882791) B2882791
theorem B18229535 : Blo 944585 18229535 := bstep (se 1 (by rfl) ⟨13672151, by rfl⟩ : syracuseStep 18229535 = 27344303) B27344303
theorem B1419689 : Blo 944585 1419689 := bstep (se 2 (by rfl) ⟨532383, by rfl⟩ : syracuseStep 1419689 = 1064767) B1064767
theorem B1419983 : Blo 944585 1419983 := bstep (se 1 (by rfl) ⟨1064987, by rfl⟩ : syracuseStep 1419983 = 2129975) B2129975
theorem B1420007 : Blo 944585 1420007 := bstep (se 1 (by rfl) ⟨1065005, by rfl⟩ : syracuseStep 1420007 = 2130011) B2130011
theorem B5384987 : Blo 944585 5384987 := bstep (se 1 (by rfl) ⟨4038740, by rfl⟩ : syracuseStep 5384987 = 8077481) B8077481
theorem B1420223 : Blo 944585 1420223 := bstep (se 1 (by rfl) ⟨1065167, by rfl⟩ : syracuseStep 1420223 = 2130335) B2130335
theorem B1420343 : Blo 944585 1420343 := bstep (se 1 (by rfl) ⟨1065257, by rfl⟩ : syracuseStep 1420343 = 2130515) B2130515
theorem B1420841 : Blo 944585 1420841 := bstep (se 2 (by rfl) ⟨532815, by rfl⟩ : syracuseStep 1420841 = 1065631) B1065631
theorem B69054115 : Blo 944585 69054115 := bstep (se 1 (by rfl) ⟨51790586, by rfl⟩ : syracuseStep 69054115 = 103581173) B103581173
theorem B1421759 : Blo 944585 1421759 := bstep (se 1 (by rfl) ⟨1066319, by rfl⟩ : syracuseStep 1421759 = 2132639) B2132639
theorem B4797305 : Blo 944585 4797305 := bstep (se 2 (by rfl) ⟨1798989, by rfl⟩ : syracuseStep 4797305 = 3597979) B3597979
theorem B13841387 : Blo 944585 13841387 := bstep (se 1 (by rfl) ⟨10381040, by rfl⟩ : syracuseStep 13841387 = 20762081) B20762081
theorem B4797467 : Blo 944585 4797467 := bstep (se 1 (by rfl) ⟨3598100, by rfl⟩ : syracuseStep 4797467 = 7196201) B7196201
theorem B3191993 : Blo 944585 3191993 := bstep (se 2 (by rfl) ⟨1196997, by rfl⟩ : syracuseStep 3191993 = 2393995) B2393995
theorem B5387471 : Blo 944585 5387471 := bstep (se 1 (by rfl) ⟨4040603, by rfl⟩ : syracuseStep 5387471 = 8081207) B8081207
theorem B2734013 : Blo 944585 2734013 := bstep (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) B1025255
theorem B3028927 : Blo 944585 3028927 := bstep (se 1 (by rfl) ⟨2271695, by rfl⟩ : syracuseStep 3028927 = 4543391) B4543391
theorem B4798601 : Blo 944585 4798601 := bstep (se 2 (by rfl) ⟨1799475, by rfl⟩ : syracuseStep 4798601 = 3598951) B3598951
theorem B7191827 : Blo 944585 7191827 := bstep (se 1 (by rfl) ⟨5393870, by rfl⟩ : syracuseStep 7191827 = 10787741) B10787741
theorem B3587561 : Blo 944585 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B5389861 : Blo 944585 5389861 := bstep (se 4 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 5389861 = 1010599) B1010599
theorem B2736251 : Blo 944585 2736251 := bstep (se 1 (by rfl) ⟨2052188, by rfl⟩ : syracuseStep 2736251 = 4104377) B4104377
theorem B224149889 : Blo 944585 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B4801031 : Blo 944585 4801031 := bstep (se 1 (by rfl) ⟨3600773, by rfl⟩ : syracuseStep 4801031 = 7201547) B7201547
theorem B10371665 : Blo 944585 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B1065703 : Blo 944585 1065703 := bstep (se 1 (by rfl) ⟨799277, by rfl⟩ : syracuseStep 1065703 = 1598555) B1598555
theorem B10797947 : Blo 944585 10797947 := bstep (se 1 (by rfl) ⟨8098460, by rfl⟩ : syracuseStep 10797947 = 16196921) B16196921
theorem B4867523 : Blo 944585 4867523 := bstep (se 1 (by rfl) ⟨3650642, by rfl⟩ : syracuseStep 4867523 = 7301285) B7301285
theorem B6473171 : Blo 944585 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B1197595 : Blo 944585 1197595 := bstep (se 1 (by rfl) ⟨898196, by rfl⟩ : syracuseStep 1197595 = 1796393) B1796393
theorem B2278991 : Blo 944585 2278991 := bstep (se 1 (by rfl) ⟨1709243, by rfl⟩ : syracuseStep 2278991 = 3418487) B3418487
theorem B4310921 : Blo 944585 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B4540315 : Blo 944585 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B6998057 : Blo 944585 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B9095975 : Blo 944585 9095975 := bstep (se 1 (by rfl) ⟨6821981, by rfl⟩ : syracuseStep 9095975 = 13643963) B13643963
theorem B3198689 : Blo 944585 3198689 := bstep (se 2 (by rfl) ⟨1199508, by rfl⟩ : syracuseStep 3198689 = 2399017) B2399017
theorem B4050719 : Blo 944585 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B818565259 : Blo 944585 818565259 := bstep (se 1 (by rfl) ⟨613923944, by rfl⟩ : syracuseStep 818565259 = 1227847889) B1227847889
theorem B3593119 : Blo 944585 3593119 := bstep (se 1 (by rfl) ⟨2694839, by rfl⟩ : syracuseStep 3593119 = 5389679) B5389679
theorem B221402267 : Blo 944585 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B1594559 : Blo 944585 1594559 := bstep (se 1 (by rfl) ⟨1195919, by rfl⟩ : syracuseStep 1594559 = 2391839) B2391839
theorem B8639723 : Blo 944585 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B3594365 : Blo 944585 3594365 := bstep (se 3 (by rfl) ⟨673943, by rfl⟩ : syracuseStep 3594365 = 1347887) B1347887
theorem B3594881 : Blo 944585 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B98294597 : Blo 944585 98294597 := bstep (se 4 (by rfl) ⟨9215118, by rfl⟩ : syracuseStep 98294597 = 18430237) B18430237
theorem B2022241 : Blo 944585 2022241 := bstep (se 2 (by rfl) ⟨758340, by rfl⟩ : syracuseStep 2022241 = 1516681) B1516681
theorem B1727423 : Blo 944585 1727423 := bstep (se 1 (by rfl) ⟨1295567, by rfl⟩ : syracuseStep 1727423 = 2591135) B2591135
theorem B1793819 : Blo 944585 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B46588409 : Blo 944585 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B2023967 : Blo 944585 2023967 := bstep (se 1 (by rfl) ⟨1517975, by rfl⟩ : syracuseStep 2023967 = 3035951) B3035951
theorem B1598089 : Blo 944585 1598089 := bstep (se 2 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 1598089 = 1198567) B1198567
theorem B1599007 : Blo 944585 1599007 := bstep (se 1 (by rfl) ⟨1199255, by rfl⟩ : syracuseStep 1599007 = 2398511) B2398511
theorem B5760935 : Blo 944585 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B1600303 : Blo 944585 1600303 := bstep (se 1 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 1600303 = 2400455) B2400455
theorem B5762153 : Blo 944585 5762153 := bstep (se 2 (by rfl) ⟨2160807, by rfl⟩ : syracuseStep 5762153 = 4321615) B4321615
theorem B945307 : Blo 944585 945307 := bstep (se 1 (by rfl) ⟨708980, by rfl⟩ : syracuseStep 945307 = 1417961) B1417961
theorem B945319 : Blo 944585 945319 := bstep (se 1 (by rfl) ⟨708989, by rfl⟩ : syracuseStep 945319 = 1417979) B1417979
theorem B5401799 : Blo 944585 5401799 := bstep (se 1 (by rfl) ⟨4051349, by rfl⟩ : syracuseStep 5401799 = 8102699) B8102699
theorem B1010971 : Blo 944585 1010971 := bstep (se 1 (by rfl) ⟨758228, by rfl⟩ : syracuseStep 1010971 = 1516457) B1516457
theorem B1797403 : Blo 944585 1797403 := bstep (se 1 (by rfl) ⟨1348052, by rfl⟩ : syracuseStep 1797403 = 2696105) B2696105
theorem B945663 : Blo 944585 945663 := bstep (se 1 (by rfl) ⟨709247, by rfl⟩ : syracuseStep 945663 = 1418495) B1418495
theorem B945871 : Blo 944585 945871 := bstep (se 1 (by rfl) ⟨709403, by rfl⟩ : syracuseStep 945871 = 1418807) B1418807
theorem B2125691 : Blo 944585 2125691 := bstep (se 1 (by rfl) ⟨1594268, by rfl⟩ : syracuseStep 2125691 = 3188537) B3188537
theorem B946111 : Blo 944585 946111 := bstep (se 1 (by rfl) ⟨709583, by rfl⟩ : syracuseStep 946111 = 1419167) B1419167
theorem B946399 : Blo 944585 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B2126159 : Blo 944585 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B2126267 : Blo 944585 2126267 := bstep (se 1 (by rfl) ⟨1594700, by rfl⟩ : syracuseStep 2126267 = 3189401) B3189401
theorem B946687 : Blo 944585 946687 := bstep (se 1 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 946687 = 1420031) B1420031
theorem B1798823 : Blo 944585 1798823 := bstep (se 1 (by rfl) ⟨1349117, by rfl⟩ : syracuseStep 1798823 = 2698235) B2698235
theorem B2126825 : Blo 944585 2126825 := bstep (se 2 (by rfl) ⟨797559, by rfl⟩ : syracuseStep 2126825 = 1595119) B1595119
theorem B2126951 : Blo 944585 2126951 := bstep (se 1 (by rfl) ⟨1595213, by rfl⟩ : syracuseStep 2126951 = 3190427) B3190427
theorem B61371593 : Blo 944585 61371593 := bstep (se 2 (by rfl) ⟨23014347, by rfl⟩ : syracuseStep 61371593 = 46028695) B46028695
theorem B13464797 : Blo 944585 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B947423 : Blo 944585 947423 := bstep (se 1 (by rfl) ⟨710567, by rfl⟩ : syracuseStep 947423 = 1421135) B1421135
theorem B947503 : Blo 944585 947503 := bstep (se 1 (by rfl) ⟨710627, by rfl⟩ : syracuseStep 947503 = 1421255) B1421255
theorem B70874441 : Blo 944585 70874441 := bstep (se 2 (by rfl) ⟨26577915, by rfl⟩ : syracuseStep 70874441 = 53155831) B53155831
theorem B947743 : Blo 944585 947743 := bstep (se 1 (by rfl) ⟨710807, by rfl⟩ : syracuseStep 947743 = 1421615) B1421615
theorem B13629019 : Blo 944585 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B947903 : Blo 944585 947903 := bstep (se 1 (by rfl) ⟨710927, by rfl⟩ : syracuseStep 947903 = 1421855) B1421855
theorem B2127635 : Blo 944585 2127635 := bstep (se 1 (by rfl) ⟨1595726, by rfl⟩ : syracuseStep 2127635 = 3191453) B3191453
theorem B2127707 : Blo 944585 2127707 := bstep (se 1 (by rfl) ⟨1595780, by rfl⟩ : syracuseStep 2127707 = 3191561) B3191561
theorem B948135 : Blo 944585 948135 := bstep (se 1 (by rfl) ⟨711101, by rfl⟩ : syracuseStep 948135 = 1422203) B1422203
theorem B948255 : Blo 944585 948255 := bstep (se 1 (by rfl) ⟨711191, by rfl⟩ : syracuseStep 948255 = 1422383) B1422383
theorem B948335 : Blo 944585 948335 := bstep (se 1 (by rfl) ⟨711251, by rfl⟩ : syracuseStep 948335 = 1422503) B1422503
theorem B948431 : Blo 944585 948431 := bstep (se 1 (by rfl) ⟨711323, by rfl⟩ : syracuseStep 948431 = 1422647) B1422647
theorem B948551 : Blo 944585 948551 := bstep (se 1 (by rfl) ⟨711413, by rfl⟩ : syracuseStep 948551 = 1422827) B1422827
theorem B2128697 : Blo 944585 2128697 := bstep (se 2 (by rfl) ⟨798261, by rfl⟩ : syracuseStep 2128697 = 1596523) B1596523
theorem B1276921 : Blo 944585 1276921 := bstep (se 2 (by rfl) ⟨478845, by rfl⟩ : syracuseStep 1276921 = 957691) B957691
theorem B2391353 : Blo 944585 2391353 := bstep (se 2 (by rfl) ⟨896757, by rfl⟩ : syracuseStep 2391353 = 1793515) B1793515
theorem B2392031 : Blo 944585 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B101056571 : Blo 944585 101056571 := bstep (se 1 (by rfl) ⟨75792428, by rfl⟩ : syracuseStep 101056571 = 151584857) B151584857
theorem B6914443 : Blo 944585 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B2130785 : Blo 944585 2130785 := bstep (se 2 (by rfl) ⟨799044, by rfl⟩ : syracuseStep 2130785 = 1598089) B1598089
theorem B3408799 : Blo 944585 3408799 := bstep (se 1 (by rfl) ⟨2556599, by rfl⟩ : syracuseStep 3408799 = 5113199) B5113199
theorem B3245015 : Blo 944585 3245015 := bstep (se 1 (by rfl) ⟨2433761, by rfl⟩ : syracuseStep 3245015 = 4867523) B4867523
theorem B6063983 : Blo 944585 6063983 := bstep (se 1 (by rfl) ⟨4547987, by rfl⟩ : syracuseStep 6063983 = 9095975) B9095975
theorem B2132009 : Blo 944585 2132009 := bstep (se 2 (by rfl) ⟨799503, by rfl⟩ : syracuseStep 2132009 = 1599007) B1599007
theorem B2132459 : Blo 944585 2132459 := bstep (se 1 (by rfl) ⟨1599344, by rfl⟩ : syracuseStep 2132459 = 3198689) B3198689
theorem B23039261 : Blo 944585 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B2133737 : Blo 944585 2133737 := bstep (se 2 (by rfl) ⟨800151, by rfl⟩ : syracuseStep 2133737 = 1600303) B1600303
theorem B2396243 : Blo 944585 2396243 := bstep (se 1 (by rfl) ⟨1797182, by rfl⟩ : syracuseStep 2396243 = 3594365) B3594365
theorem B2396537 : Blo 944585 2396537 := bstep (se 2 (by rfl) ⟨898701, by rfl⟩ : syracuseStep 2396537 = 1797403) B1797403
theorem B2396587 : Blo 944585 2396587 := bstep (se 1 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 2396587 = 3594881) B3594881
theorem B18223541 : Blo 944585 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B1151615 : Blo 944585 1151615 := bstep (se 1 (by rfl) ⟨863711, by rfl⟩ : syracuseStep 1151615 = 1727423) B1727423
theorem B14554235 : Blo 944585 14554235 := bstep (se 1 (by rfl) ⟨10915676, by rfl⟩ : syracuseStep 14554235 = 21831353) B21831353
theorem B2561627 : Blo 944585 2561627 := bstep (se 1 (by rfl) ⟨1921220, by rfl⟩ : syracuseStep 2561627 = 3842441) B3842441
theorem B1349311 : Blo 944585 1349311 := bstep (se 1 (by rfl) ⟨1011983, by rfl⟩ : syracuseStep 1349311 = 2023967) B2023967
theorem B7673591 : Blo 944585 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B4790825 : Blo 944585 4790825 := bstep (se 2 (by rfl) ⟨1796559, by rfl⟩ : syracuseStep 4790825 = 3593119) B3593119
theorem B3840623 : Blo 944585 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B3841435 : Blo 944585 3841435 := bstep (se 1 (by rfl) ⟨2881076, by rfl⟩ : syracuseStep 3841435 = 5762153) B5762153
theorem B1417127 : Blo 944585 1417127 := bstep (se 1 (by rfl) ⟨1062845, by rfl⟩ : syracuseStep 1417127 = 2125691) B2125691
theorem B4038569 : Blo 944585 4038569 := bstep (se 2 (by rfl) ⟨1514463, by rfl⟩ : syracuseStep 4038569 = 3028927) B3028927
theorem B1417439 : Blo 944585 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B1417511 : Blo 944585 1417511 := bstep (se 1 (by rfl) ⟨1063133, by rfl⟩ : syracuseStep 1417511 = 2126267) B2126267
theorem B1417883 : Blo 944585 1417883 := bstep (se 1 (by rfl) ⟨1063412, by rfl⟩ : syracuseStep 1417883 = 2126825) B2126825
theorem B1417967 : Blo 944585 1417967 := bstep (se 1 (by rfl) ⟨1063475, by rfl⟩ : syracuseStep 1417967 = 2126951) B2126951
theorem B2696321 : Blo 944585 2696321 := bstep (se 2 (by rfl) ⟨1011120, by rfl⟩ : syracuseStep 2696321 = 2022241) B2022241
theorem B1418423 : Blo 944585 1418423 := bstep (se 1 (by rfl) ⟨1063817, by rfl⟩ : syracuseStep 1418423 = 2127635) B2127635
theorem B1418471 : Blo 944585 1418471 := bstep (se 1 (by rfl) ⟨1063853, by rfl⟩ : syracuseStep 1418471 = 2127707) B2127707
theorem B1419131 : Blo 944585 1419131 := bstep (se 1 (by rfl) ⟨1064348, by rfl⟩ : syracuseStep 1419131 = 2128697) B2128697
theorem B7186481 : Blo 944585 7186481 := bstep (se 2 (by rfl) ⟨2694930, by rfl⟩ : syracuseStep 7186481 = 5389861) B5389861
theorem B4794551 : Blo 944585 4794551 := bstep (se 1 (by rfl) ⟨3595913, by rfl⟩ : syracuseStep 4794551 = 7191827) B7191827
theorem B54012521 : Blo 944585 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B1420079 : Blo 944585 1420079 := bstep (se 1 (by rfl) ⟨1065059, by rfl⟩ : syracuseStep 1420079 = 2130119) B2130119
theorem B1420271 : Blo 944585 1420271 := bstep (se 1 (by rfl) ⟨1065203, by rfl⟩ : syracuseStep 1420271 = 2130407) B2130407
theorem B6466715 : Blo 944585 6466715 := bstep (se 1 (by rfl) ⟨4850036, by rfl⟩ : syracuseStep 6466715 = 9700073) B9700073
theorem B1420463 : Blo 944585 1420463 := bstep (se 1 (by rfl) ⟨1065347, by rfl⟩ : syracuseStep 1420463 = 2130695) B2130695
theorem B43625911 : Blo 944585 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B3190319 : Blo 944585 3190319 := bstep (se 1 (by rfl) ⟨2392739, by rfl⟩ : syracuseStep 3190319 = 4785479) B4785479
theorem B1420937 : Blo 944585 1420937 := bstep (se 2 (by rfl) ⟨532851, by rfl⟩ : syracuseStep 1420937 = 1065703) B1065703
theorem B1420955 : Blo 944585 1420955 := bstep (se 1 (by rfl) ⟨1065716, by rfl⟩ : syracuseStep 1420955 = 2131433) B2131433
theorem B597733037 : Blo 944585 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B1519327 : Blo 944585 1519327 := bstep (se 1 (by rfl) ⟨1139495, by rfl⟩ : syracuseStep 1519327 = 2278991) B2278991
theorem B1421039 : Blo 944585 1421039 := bstep (se 1 (by rfl) ⟨1065779, by rfl⟩ : syracuseStep 1421039 = 2131559) B2131559
theorem B4665371 : Blo 944585 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B2273455 : Blo 944585 2273455 := bstep (se 1 (by rfl) ⟨1705091, by rfl⟩ : syracuseStep 2273455 = 3410183) B3410183
theorem B2273503 : Blo 944585 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B3191291 : Blo 944585 3191291 := bstep (se 1 (by rfl) ⟨2393468, by rfl⟩ : syracuseStep 3191291 = 4786937) B4786937
theorem B5124961 : Blo 944585 5124961 := bstep (se 2 (by rfl) ⟨1921860, by rfl⟩ : syracuseStep 5124961 = 3843721) B3843721
theorem B3191777 : Blo 944585 3191777 := bstep (se 2 (by rfl) ⟨1196916, by rfl⟩ : syracuseStep 3191777 = 2393833) B2393833
theorem B2700479 : Blo 944585 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B3192425 : Blo 944585 3192425 := bstep (se 2 (by rfl) ⟨1197159, by rfl⟩ : syracuseStep 3192425 = 2394319) B2394319
theorem B4044583 : Blo 944585 4044583 := bstep (se 1 (by rfl) ⟨3033437, by rfl⟩ : syracuseStep 4044583 = 6066875) B6066875
theorem B147601511 : Blo 944585 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B1063039 : Blo 944585 1063039 := bstep (se 1 (by rfl) ⟨797279, by rfl⟩ : syracuseStep 1063039 = 1594559) B1594559
theorem B5258141 : Blo 944585 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B3194153 : Blo 944585 3194153 := bstep (se 2 (by rfl) ⟨1197807, by rfl⟩ : syracuseStep 3194153 = 2395615) B2395615
theorem B14597633 : Blo 944585 14597633 := bstep (se 2 (by rfl) ⟨5474112, by rfl⟩ : syracuseStep 14597633 = 10948225) B10948225
theorem B1195879 : Blo 944585 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B10764413 : Blo 944585 10764413 := bstep (se 3 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 10764413 = 4036655) B4036655
theorem B1091420345 : Blo 944585 1091420345 := bstep (se 2 (by rfl) ⟨409282629, by rfl⟩ : syracuseStep 1091420345 = 818565259) B818565259
theorem B5391845 : Blo 944585 5391845 := bstep (se 4 (by rfl) ⟨505485, by rfl⟩ : syracuseStep 5391845 = 1010971) B1010971
theorem B3589991 : Blo 944585 3589991 := bstep (se 1 (by rfl) ⟨2692493, by rfl⟩ : syracuseStep 3589991 = 5384987) B5384987
theorem B13289417 : Blo 944585 13289417 := bstep (se 2 (by rfl) ⟨4983531, by rfl⟩ : syracuseStep 13289417 = 9967063) B9967063
theorem B18172025 : Blo 944585 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1199215 : Blo 944585 1199215 := bstep (se 1 (by rfl) ⟨899411, by rfl⟩ : syracuseStep 1199215 = 1798823) B1798823
theorem B3198203 : Blo 944585 3198203 := bstep (se 1 (by rfl) ⟨2398652, by rfl⟩ : syracuseStep 3198203 = 4797305) B4797305
theorem B9227591 : Blo 944585 9227591 := bstep (se 1 (by rfl) ⟨6920693, by rfl⟩ : syracuseStep 9227591 = 13841387) B13841387
theorem B3198311 : Blo 944585 3198311 := bstep (se 1 (by rfl) ⟨2398733, by rfl⟩ : syracuseStep 3198311 = 4797467) B4797467
theorem B40914395 : Blo 944585 40914395 := bstep (se 1 (by rfl) ⟨30685796, by rfl⟩ : syracuseStep 40914395 = 61371593) B61371593
theorem B3591647 : Blo 944585 3591647 := bstep (se 1 (by rfl) ⟨2693735, by rfl⟩ : syracuseStep 3591647 = 5387471) B5387471
theorem B1822675 : Blo 944585 1822675 := bstep (se 1 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 1822675 = 2734013) B2734013
theorem B3199067 : Blo 944585 3199067 := bstep (se 1 (by rfl) ⟨2399300, by rfl⟩ : syracuseStep 3199067 = 4798601) B4798601
theorem B1594235 : Blo 944585 1594235 := bstep (se 1 (by rfl) ⟨1195676, by rfl⟩ : syracuseStep 1594235 = 2391353) B2391353
theorem B1594687 : Blo 944585 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B1824167 : Blo 944585 1824167 := bstep (se 1 (by rfl) ⟨1368125, by rfl⟩ : syracuseStep 1824167 = 2736251) B2736251
theorem B3200687 : Blo 944585 3200687 := bstep (se 1 (by rfl) ⟨2400515, by rfl⟩ : syracuseStep 3200687 = 4801031) B4801031
theorem B5396219 : Blo 944585 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B7198631 : Blo 944585 7198631 := bstep (se 1 (by rfl) ⟨5398973, by rfl⟩ : syracuseStep 7198631 = 10797947) B10797947
theorem B4315447 : Blo 944585 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B7691111 : Blo 944585 7691111 := bstep (se 1 (by rfl) ⟨5768333, by rfl⟩ : syracuseStep 7691111 = 11536667) B11536667
theorem B1596793 : Blo 944585 1596793 := bstep (se 2 (by rfl) ⟨598797, by rfl⟩ : syracuseStep 1596793 = 1197595) B1197595
theorem B1596827 : Blo 944585 1596827 := bstep (se 1 (by rfl) ⟨1197620, by rfl⟩ : syracuseStep 1596827 = 2395241) B2395241
theorem B6053753 : Blo 944585 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B16408763 : Blo 944585 16408763 := bstep (se 1 (by rfl) ⟨12306572, by rfl⟩ : syracuseStep 16408763 = 24613145) B24613145
theorem B7201061 : Blo 944585 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B1597799 : Blo 944585 1597799 := bstep (se 1 (by rfl) ⟨1198349, by rfl⟩ : syracuseStep 1597799 = 2396699) B2396699
theorem B35906125 : Blo 944585 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B18441179 : Blo 944585 18441179 := bstep (se 1 (by rfl) ⟨13830884, by rfl⟩ : syracuseStep 18441179 = 27661769) B27661769
theorem B65529731 : Blo 944585 65529731 := bstep (se 1 (by rfl) ⟨49147298, by rfl⟩ : syracuseStep 65529731 = 98294597) B98294597
theorem B92072153 : Blo 944585 92072153 := bstep (se 2 (by rfl) ⟨34527057, by rfl⟩ : syracuseStep 92072153 = 69054115) B69054115
theorem B11495789 : Blo 944585 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B4155881 : Blo 944585 4155881 := bstep (se 2 (by rfl) ⟨1558455, by rfl⟩ : syracuseStep 4155881 = 3116911) B3116911
theorem B944879 : Blo 944585 944879 := bstep (se 1 (by rfl) ⟨708659, by rfl⟩ : syracuseStep 944879 = 1417319) B1417319
theorem B944967 : Blo 944585 944967 := bstep (se 1 (by rfl) ⟨708725, by rfl⟩ : syracuseStep 944967 = 1417451) B1417451
theorem B31058939 : Blo 944585 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B2125331 : Blo 944585 2125331 := bstep (se 1 (by rfl) ⟨1593998, by rfl⟩ : syracuseStep 2125331 = 3187997) B3187997
theorem B945895 : Blo 944585 945895 := bstep (se 1 (by rfl) ⟨709421, by rfl⟩ : syracuseStep 945895 = 1418843) B1418843
theorem B8089577 : Blo 944585 8089577 := bstep (se 2 (by rfl) ⟨3033591, by rfl⟩ : syracuseStep 8089577 = 6067183) B6067183
theorem B12153023 : Blo 944585 12153023 := bstep (se 1 (by rfl) ⟨9114767, by rfl⟩ : syracuseStep 12153023 = 18229535) B18229535
theorem B946459 : Blo 944585 946459 := bstep (se 1 (by rfl) ⟨709844, by rfl⟩ : syracuseStep 946459 = 1419689) B1419689
theorem B946655 : Blo 944585 946655 := bstep (se 1 (by rfl) ⟨709991, by rfl⟩ : syracuseStep 946655 = 1419983) B1419983
theorem B946671 : Blo 944585 946671 := bstep (se 1 (by rfl) ⟨710003, by rfl⟩ : syracuseStep 946671 = 1420007) B1420007
theorem B946815 : Blo 944585 946815 := bstep (se 1 (by rfl) ⟨710111, by rfl⟩ : syracuseStep 946815 = 1420223) B1420223
theorem B946895 : Blo 944585 946895 := bstep (se 1 (by rfl) ⟨710171, by rfl⟩ : syracuseStep 946895 = 1420343) B1420343
theorem B3601199 : Blo 944585 3601199 := bstep (se 1 (by rfl) ⟨2700899, by rfl⟩ : syracuseStep 3601199 = 5401799) B5401799
theorem B947227 : Blo 944585 947227 := bstep (se 1 (by rfl) ⟨710420, by rfl⟩ : syracuseStep 947227 = 1420841) B1420841
theorem B947839 : Blo 944585 947839 := bstep (se 1 (by rfl) ⟨710879, by rfl⟩ : syracuseStep 947839 = 1421759) B1421759
theorem B2127995 : Blo 944585 2127995 := bstep (se 1 (by rfl) ⟨1595996, by rfl⟩ : syracuseStep 2127995 = 3191993) B3191993
theorem B47249627 : Blo 944585 47249627 := bstep (se 1 (by rfl) ⟨35437220, by rfl⟩ : syracuseStep 47249627 = 70874441) B70874441
theorem B1702561 : Blo 944585 1702561 := bstep (se 2 (by rfl) ⟨638460, by rfl⟩ : syracuseStep 1702561 = 1276921) B1276921
theorem B2391707 : Blo 944585 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B67371047 : Blo 944585 67371047 := bstep (se 1 (by rfl) ⟨50528285, by rfl⟩ : syracuseStep 67371047 = 101056571) B101056571
theorem B7176275 : Blo 944585 7176275 := bstep (se 1 (by rfl) ⟨5382206, by rfl⟩ : syracuseStep 7176275 = 10764413) B10764413
theorem B727613563 : Blo 944585 727613563 := bstep (se 1 (by rfl) ⟨545710172, by rfl⟩ : syracuseStep 727613563 = 1091420345) B1091420345
theorem B2163343 : Blo 944585 2163343 := bstep (se 1 (by rfl) ⟨1622507, by rfl⟩ : syracuseStep 2163343 = 3245015) B3245015
theorem B47874833 : Blo 944585 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B2393327 : Blo 944585 2393327 := bstep (se 1 (by rfl) ⟨1794995, by rfl⟩ : syracuseStep 2393327 = 3589991) B3589991
theorem B2132135 : Blo 944585 2132135 := bstep (se 1 (by rfl) ⟨1599101, by rfl⟩ : syracuseStep 2132135 = 3198203) B3198203
theorem B2132207 : Blo 944585 2132207 := bstep (se 1 (by rfl) ⟨1599155, by rfl⟩ : syracuseStep 2132207 = 3198311) B3198311
theorem B2394431 : Blo 944585 2394431 := bstep (se 1 (by rfl) ⟨1795823, by rfl⟩ : syracuseStep 2394431 = 3591647) B3591647
theorem B2132711 : Blo 944585 2132711 := bstep (se 1 (by rfl) ⟨1599533, by rfl⟩ : syracuseStep 2132711 = 3199067) B3199067
theorem B9702823 : Blo 944585 9702823 := bstep (se 1 (by rfl) ⟨7277117, by rfl⟩ : syracuseStep 9702823 = 14554235) B14554235
theorem B1707751 : Blo 944585 1707751 := bstep (se 1 (by rfl) ⟨1280813, by rfl⟩ : syracuseStep 1707751 = 2561627) B2561627
theorem B2133791 : Blo 944585 2133791 := bstep (se 1 (by rfl) ⟨1600343, by rfl⟩ : syracuseStep 2133791 = 3200687) B3200687
theorem B5115727 : Blo 944585 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B2560415 : Blo 944585 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B27333125 : Blo 944585 27333125 := bstep (se 4 (by rfl) ⟨2562480, by rfl⟩ : syracuseStep 27333125 = 5124961) B5124961
theorem B58167881 : Blo 944585 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B4035835 : Blo 944585 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B2430233 : Blo 944585 2430233 := bstep (se 2 (by rfl) ⟨911337, by rfl⟩ : syracuseStep 2430233 = 1822675) B1822675
theorem B2692379 : Blo 944585 2692379 := bstep (se 1 (by rfl) ⟨2019284, by rfl⟩ : syracuseStep 2692379 = 4038569) B4038569
theorem B125999005 : Blo 944585 125999005 := bstep (se 3 (by rfl) ⟨23624813, by rfl⟩ : syracuseStep 125999005 = 47249627) B47249627
theorem B12294119 : Blo 944585 12294119 := bstep (se 1 (by rfl) ⟨9220589, by rfl⟩ : syracuseStep 12294119 = 18441179) B18441179
theorem B43686487 : Blo 944585 43686487 := bstep (se 1 (by rfl) ⟨32764865, by rfl⟩ : syracuseStep 43686487 = 65529731) B65529731
theorem B11082349 : Blo 944585 11082349 := bstep (se 3 (by rfl) ⟨2077940, by rfl⟩ : syracuseStep 11082349 = 4155881) B4155881
theorem B4790987 : Blo 944585 4790987 := bstep (se 1 (by rfl) ⟨3593240, by rfl⟩ : syracuseStep 4790987 = 7186481) B7186481
theorem B61381435 : Blo 944585 61381435 := bstep (se 1 (by rfl) ⟨46036076, by rfl⟩ : syracuseStep 61381435 = 92072153) B92072153
theorem B1416887 : Blo 944585 1416887 := bstep (se 1 (by rfl) ⟨1062665, by rfl⟩ : syracuseStep 1416887 = 2125331) B2125331
theorem B8102015 : Blo 944585 8102015 := bstep (se 1 (by rfl) ⟨6076511, by rfl⟩ : syracuseStep 8102015 = 12153023) B12153023
theorem B1417385 : Blo 944585 1417385 := bstep (se 2 (by rfl) ⟨531519, by rfl⟩ : syracuseStep 1417385 = 1063039) B1063039
theorem B2400799 : Blo 944585 2400799 := bstep (se 1 (by rfl) ⟨1800599, by rfl⟩ : syracuseStep 2400799 = 3601199) B3601199
theorem B2270081 : Blo 944585 2270081 := bstep (se 2 (by rfl) ⟨851280, by rfl⟩ : syracuseStep 2270081 = 1702561) B1702561
theorem B8103077 : Blo 944585 8103077 := bstep (se 4 (by rfl) ⟨759663, by rfl⟩ : syracuseStep 8103077 = 1519327) B1519327
theorem B1418663 : Blo 944585 1418663 := bstep (se 1 (by rfl) ⟨1063997, by rfl⟩ : syracuseStep 1418663 = 2127995) B2127995
theorem B5121913 : Blo 944585 5121913 := bstep (se 2 (by rfl) ⟨1920717, by rfl⟩ : syracuseStep 5121913 = 3841435) B3841435
theorem B9219257 : Blo 944585 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B1420523 : Blo 944585 1420523 := bstep (se 1 (by rfl) ⟨1065392, by rfl⟩ : syracuseStep 1420523 = 2130785) B2130785
theorem B4042655 : Blo 944585 4042655 := bstep (se 1 (by rfl) ⟨3031991, by rfl⟩ : syracuseStep 4042655 = 6063983) B6063983
theorem B8859611 : Blo 944585 8859611 := bstep (se 1 (by rfl) ⟨6644708, by rfl⟩ : syracuseStep 8859611 = 13289417) B13289417
theorem B1421339 : Blo 944585 1421339 := bstep (se 1 (by rfl) ⟨1066004, by rfl⟩ : syracuseStep 1421339 = 2132009) B2132009
theorem B1421639 : Blo 944585 1421639 := bstep (se 1 (by rfl) ⟨1066229, by rfl⟩ : syracuseStep 1421639 = 2132459) B2132459
theorem B27276263 : Blo 944585 27276263 := bstep (se 1 (by rfl) ⟨20457197, by rfl⟩ : syracuseStep 27276263 = 40914395) B40914395
theorem B1422491 : Blo 944585 1422491 := bstep (se 1 (by rfl) ⟨1066868, by rfl⟩ : syracuseStep 1422491 = 2133737) B2133737
theorem B1062823 : Blo 944585 1062823 := bstep (se 1 (by rfl) ⟨797117, by rfl⟩ : syracuseStep 1062823 = 1594235) B1594235
theorem B4864445 : Blo 944585 4864445 := bstep (se 3 (by rfl) ⟨912083, by rfl⟩ : syracuseStep 4864445 = 1824167) B1824167
theorem B4799087 : Blo 944585 4799087 := bstep (se 1 (by rfl) ⟨3599315, by rfl⟩ : syracuseStep 4799087 = 7198631) B7198631
theorem B3193883 : Blo 944585 3193883 := bstep (se 1 (by rfl) ⟨2395412, by rfl⟩ : syracuseStep 3193883 = 4790825) B4790825
theorem B5127407 : Blo 944585 5127407 := bstep (se 1 (by rfl) ⟨3845555, by rfl⟩ : syracuseStep 5127407 = 7691111) B7691111
theorem B1064551 : Blo 944585 1064551 := bstep (se 1 (by rfl) ⟨798413, by rfl⟩ : syracuseStep 1064551 = 1596827) B1596827
theorem B4800707 : Blo 944585 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B3031273 : Blo 944585 3031273 := bstep (se 2 (by rfl) ⟨1136727, by rfl⟩ : syracuseStep 3031273 = 2273455) B2273455
theorem B1065199 : Blo 944585 1065199 := bstep (se 1 (by rfl) ⟨798899, by rfl⟩ : syracuseStep 1065199 = 1597799) B1597799
theorem B3031337 : Blo 944585 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B3195449 : Blo 944585 3195449 := bstep (se 2 (by rfl) ⟨1198293, by rfl⟩ : syracuseStep 3195449 = 2396587) B2396587
theorem B3196367 : Blo 944585 3196367 := bstep (se 1 (by rfl) ⟨2397275, by rfl⟩ : syracuseStep 3196367 = 4794551) B4794551
theorem B4311143 : Blo 944585 4311143 := bstep (se 1 (by rfl) ⟨3233357, by rfl⟩ : syracuseStep 4311143 = 6466715) B6466715
theorem B5392777 : Blo 944585 5392777 := bstep (se 2 (by rfl) ⟨2022291, by rfl⟩ : syracuseStep 5392777 = 4044583) B4044583
theorem B5393051 : Blo 944585 5393051 := bstep (se 1 (by rfl) ⟨4044788, by rfl⟩ : syracuseStep 5393051 = 8089577) B8089577
theorem B5753929 : Blo 944585 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B1594471 : Blo 944585 1594471 := bstep (se 1 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 1594471 = 2391707) B2391707
theorem B1594505 : Blo 944585 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B12440989 : Blo 944585 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B3594563 : Blo 944585 3594563 := bstep (se 1 (by rfl) ⟨2695922, by rfl⟩ : syracuseStep 3594563 = 5391845) B5391845
theorem B4545065 : Blo 944585 4545065 := bstep (se 2 (by rfl) ⟨1704399, by rfl⟩ : syracuseStep 4545065 = 3408799) B3408799
theorem B12114683 : Blo 944585 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B3070973 : Blo 944585 3070973 := bstep (se 3 (by rfl) ⟨575807, by rfl⟩ : syracuseStep 3070973 = 1151615) B1151615
theorem B15359507 : Blo 944585 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B6151727 : Blo 944585 6151727 := bstep (se 1 (by rfl) ⟨4613795, by rfl⟩ : syracuseStep 6151727 = 9227591) B9227591
theorem B1597495 : Blo 944585 1597495 := bstep (se 1 (by rfl) ⟨1198121, by rfl⟩ : syracuseStep 1597495 = 2396243) B2396243
theorem B1597691 : Blo 944585 1597691 := bstep (se 1 (by rfl) ⟨1198268, by rfl⟩ : syracuseStep 1597691 = 2396537) B2396537
theorem B12149027 : Blo 944585 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B3597479 : Blo 944585 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B1598953 : Blo 944585 1598953 := bstep (se 2 (by rfl) ⟨599607, by rfl⟩ : syracuseStep 1598953 = 1199215) B1199215
theorem B944751 : Blo 944585 944751 := bstep (se 1 (by rfl) ⟨708563, by rfl⟩ : syracuseStep 944751 = 1417127) B1417127
theorem B10939175 : Blo 944585 10939175 := bstep (se 1 (by rfl) ⟨8204381, by rfl⟩ : syracuseStep 10939175 = 16408763) B16408763
theorem B944959 : Blo 944585 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B945007 : Blo 944585 945007 := bstep (se 1 (by rfl) ⟨708755, by rfl⟩ : syracuseStep 945007 = 1417511) B1417511
theorem B945255 : Blo 944585 945255 := bstep (se 1 (by rfl) ⟨708941, by rfl⟩ : syracuseStep 945255 = 1417883) B1417883
theorem B945311 : Blo 944585 945311 := bstep (se 1 (by rfl) ⟨708983, by rfl⟩ : syracuseStep 945311 = 1417967) B1417967
theorem B1797547 : Blo 944585 1797547 := bstep (se 1 (by rfl) ⟨1348160, by rfl⟩ : syracuseStep 1797547 = 2696321) B2696321
theorem B945615 : Blo 944585 945615 := bstep (se 1 (by rfl) ⟨709211, by rfl⟩ : syracuseStep 945615 = 1418423) B1418423
theorem B945647 : Blo 944585 945647 := bstep (se 1 (by rfl) ⟨709235, by rfl⟩ : syracuseStep 945647 = 1418471) B1418471
theorem B946087 : Blo 944585 946087 := bstep (se 1 (by rfl) ⟨709565, by rfl⟩ : syracuseStep 946087 = 1419131) B1419131
theorem B7663859 : Blo 944585 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B36008347 : Blo 944585 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B2126249 : Blo 944585 2126249 := bstep (se 2 (by rfl) ⟨797343, by rfl⟩ : syracuseStep 2126249 = 1594687) B1594687
theorem B946719 : Blo 944585 946719 := bstep (se 1 (by rfl) ⟨710039, by rfl⟩ : syracuseStep 946719 = 1420079) B1420079
theorem B946847 : Blo 944585 946847 := bstep (se 1 (by rfl) ⟨710135, by rfl⟩ : syracuseStep 946847 = 1420271) B1420271
theorem B20705959 : Blo 944585 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B946975 : Blo 944585 946975 := bstep (se 1 (by rfl) ⟨710231, by rfl⟩ : syracuseStep 946975 = 1420463) B1420463
theorem B1799081 : Blo 944585 1799081 := bstep (se 2 (by rfl) ⟨674655, by rfl⟩ : syracuseStep 1799081 = 1349311) B1349311
theorem B2126879 : Blo 944585 2126879 := bstep (se 1 (by rfl) ⟨1595159, by rfl⟩ : syracuseStep 2126879 = 3190319) B3190319
theorem B947291 : Blo 944585 947291 := bstep (se 1 (by rfl) ⟨710468, by rfl⟩ : syracuseStep 947291 = 1420937) B1420937
theorem B947303 : Blo 944585 947303 := bstep (se 1 (by rfl) ⟨710477, by rfl⟩ : syracuseStep 947303 = 1420955) B1420955
theorem B398488691 : Blo 944585 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B947359 : Blo 944585 947359 := bstep (se 1 (by rfl) ⟨710519, by rfl⟩ : syracuseStep 947359 = 1421039) B1421039
theorem B2127527 : Blo 944585 2127527 := bstep (se 1 (by rfl) ⟨1595645, by rfl⟩ : syracuseStep 2127527 = 3191291) B3191291
theorem B2127851 : Blo 944585 2127851 := bstep (se 1 (by rfl) ⟨1595888, by rfl⟩ : syracuseStep 2127851 = 3191777) B3191777
theorem B1800319 : Blo 944585 1800319 := bstep (se 1 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 1800319 = 2700479) B2700479
theorem B2128283 : Blo 944585 2128283 := bstep (se 1 (by rfl) ⟨1596212, by rfl⟩ : syracuseStep 2128283 = 3192425) B3192425
theorem B98401007 : Blo 944585 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B2129057 : Blo 944585 2129057 := bstep (se 2 (by rfl) ⟨798396, by rfl⟩ : syracuseStep 2129057 = 1596793) B1596793
theorem B3505427 : Blo 944585 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B2129435 : Blo 944585 2129435 := bstep (se 1 (by rfl) ⟨1597076, by rfl⟩ : syracuseStep 2129435 = 3194153) B3194153
theorem B9731755 : Blo 944585 9731755 := bstep (se 1 (by rfl) ⟨7298816, by rfl⟩ : syracuseStep 9731755 = 14597633) B14597633
theorem B4784183 : Blo 944585 4784183 := bstep (se 1 (by rfl) ⟨3588137, by rfl⟩ : syracuseStep 4784183 = 7176275) B7176275
theorem B2129993 : Blo 944585 2129993 := bstep (se 2 (by rfl) ⟨798747, by rfl⟩ : syracuseStep 2129993 = 1597495) B1597495
theorem B2130299 : Blo 944585 2130299 := bstep (se 1 (by rfl) ⟨1597724, by rfl⟩ : syracuseStep 2130299 = 3195449) B3195449
theorem B31916555 : Blo 944585 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B2884457 : Blo 944585 2884457 := bstep (se 2 (by rfl) ⟨1081671, by rfl⟩ : syracuseStep 2884457 = 2163343) B2163343
theorem B2130911 : Blo 944585 2130911 := bstep (se 1 (by rfl) ⟨1598183, by rfl⟩ : syracuseStep 2130911 = 3196367) B3196367
theorem B2131937 : Blo 944585 2131937 := bstep (se 2 (by rfl) ⟨799476, by rfl⟩ : syracuseStep 2131937 = 1598953) B1598953
theorem B1062636509 : Blo 944585 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B18222083 : Blo 944585 18222083 := bstep (se 1 (by rfl) ⟨13666562, by rfl⟩ : syracuseStep 18222083 = 27333125) B27333125
theorem B7179677 : Blo 944585 7179677 := bstep (se 3 (by rfl) ⟨1346189, by rfl⟩ : syracuseStep 7179677 = 2692379) B2692379
theorem B8196079 : Blo 944585 8196079 := bstep (se 1 (by rfl) ⟨6147059, by rfl⟩ : syracuseStep 8196079 = 12294119) B12294119
theorem B7671905 : Blo 944585 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B2396375 : Blo 944585 2396375 := bstep (se 1 (by rfl) ⟨1797281, by rfl⟩ : syracuseStep 2396375 = 3594563) B3594563
theorem B2396729 : Blo 944585 2396729 := bstep (se 2 (by rfl) ⟨898773, by rfl⟩ : syracuseStep 2396729 = 1797547) B1797547
theorem B4101151 : Blo 944585 4101151 := bstep (se 1 (by rfl) ⟨3075863, by rfl⟩ : syracuseStep 4101151 = 6151727) B6151727
theorem B6820969 : Blo 944585 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B8099351 : Blo 944585 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B48011129 : Blo 944585 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B1513387 : Blo 944585 1513387 := bstep (se 1 (by rfl) ⟨1135040, by rfl⟩ : syracuseStep 1513387 = 2270081) B2270081
theorem B2398319 : Blo 944585 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B5381113 : Blo 944585 5381113 := bstep (se 2 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 5381113 = 4035835) B4035835
theorem B16587985 : Blo 944585 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B1417097 : Blo 944585 1417097 := bstep (se 2 (by rfl) ⟨531411, by rfl⟩ : syracuseStep 1417097 = 1062823) B1062823
theorem B2695103 : Blo 944585 2695103 := bstep (se 1 (by rfl) ⟨2021327, by rfl⟩ : syracuseStep 2695103 = 4042655) B4042655
theorem B5906407 : Blo 944585 5906407 := bstep (se 1 (by rfl) ⟨4429805, by rfl⟩ : syracuseStep 5906407 = 8859611) B8859611
theorem B2400425 : Blo 944585 2400425 := bstep (se 2 (by rfl) ⟨900159, by rfl⟩ : syracuseStep 2400425 = 1800319) B1800319
theorem B1417499 : Blo 944585 1417499 := bstep (se 1 (by rfl) ⟨1063124, by rfl⟩ : syracuseStep 1417499 = 2126249) B2126249
theorem B1417919 : Blo 944585 1417919 := bstep (se 1 (by rfl) ⟨1063439, by rfl⟩ : syracuseStep 1417919 = 2126879) B2126879
theorem B1418351 : Blo 944585 1418351 := bstep (se 1 (by rfl) ⟨1063763, by rfl⟩ : syracuseStep 1418351 = 2127527) B2127527
theorem B1418567 : Blo 944585 1418567 := bstep (se 1 (by rfl) ⟨1063925, by rfl⟩ : syracuseStep 1418567 = 2127851) B2127851
theorem B1418855 : Blo 944585 1418855 := bstep (se 1 (by rfl) ⟨1064141, by rfl⟩ : syracuseStep 1418855 = 2128283) B2128283
theorem B1419371 : Blo 944585 1419371 := bstep (se 1 (by rfl) ⟨1064528, by rfl⟩ : syracuseStep 1419371 = 2129057) B2129057
theorem B1419401 : Blo 944585 1419401 := bstep (se 2 (by rfl) ⟨532275, by rfl⟩ : syracuseStep 1419401 = 1064551) B1064551
theorem B3418271 : Blo 944585 3418271 := bstep (se 1 (by rfl) ⟨2563703, by rfl⟩ : syracuseStep 3418271 = 5127407) B5127407
theorem B2336951 : Blo 944585 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B1419623 : Blo 944585 1419623 := bstep (se 1 (by rfl) ⟨1064717, by rfl⟩ : syracuseStep 1419623 = 2129435) B2129435
theorem B4041697 : Blo 944585 4041697 := bstep (se 2 (by rfl) ⟨1515636, by rfl⟩ : syracuseStep 4041697 = 3031273) B3031273
theorem B1420265 : Blo 944585 1420265 := bstep (se 2 (by rfl) ⟨532599, by rfl⟩ : syracuseStep 1420265 = 1065199) B1065199
theorem B6827773 : Blo 944585 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B1421423 : Blo 944585 1421423 := bstep (se 1 (by rfl) ⟨1066067, by rfl⟩ : syracuseStep 1421423 = 2132135) B2132135
theorem B1421471 : Blo 944585 1421471 := bstep (se 1 (by rfl) ⟨1066103, by rfl⟩ : syracuseStep 1421471 = 2132207) B2132207
theorem B1421807 : Blo 944585 1421807 := bstep (se 1 (by rfl) ⟨1066355, by rfl⟩ : syracuseStep 1421807 = 2132711) B2132711
theorem B6829217 : Blo 944585 6829217 := bstep (se 2 (by rfl) ⟨2560956, by rfl⟩ : syracuseStep 6829217 = 5121913) B5121913
theorem B1422527 : Blo 944585 1422527 := bstep (se 1 (by rfl) ⟨1066895, by rfl⟩ : syracuseStep 1422527 = 2133791) B2133791
theorem B38778587 : Blo 944585 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B7190369 : Blo 944585 7190369 := bstep (se 2 (by rfl) ⟨2696388, by rfl⟩ : syracuseStep 7190369 = 5392777) B5392777
theorem B1063003 : Blo 944585 1063003 := bstep (se 1 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 1063003 = 1594505) B1594505
theorem B1620155 : Blo 944585 1620155 := bstep (se 1 (by rfl) ⟨1215116, by rfl⟩ : syracuseStep 1620155 = 2430233) B2430233
theorem B3030043 : Blo 944585 3030043 := bstep (se 1 (by rfl) ⟨2272532, by rfl⟩ : syracuseStep 3030043 = 4545065) B4545065
theorem B3193991 : Blo 944585 3193991 := bstep (se 1 (by rfl) ⟨2395493, by rfl⟩ : syracuseStep 3193991 = 4790987) B4790987
theorem B8076455 : Blo 944585 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B2047315 : Blo 944585 2047315 := bstep (se 1 (by rfl) ⟨1535486, by rfl⟩ : syracuseStep 2047315 = 3070973) B3070973
theorem B2277001 : Blo 944585 2277001 := bstep (se 2 (by rfl) ⟨853875, by rfl⟩ : syracuseStep 2277001 = 1707751) B1707751
theorem B10239671 : Blo 944585 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B1065127 : Blo 944585 1065127 := bstep (se 1 (by rfl) ⟨798845, by rfl⟩ : syracuseStep 1065127 = 1597691) B1597691
theorem B27607945 : Blo 944585 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B7292783 : Blo 944585 7292783 := bstep (se 1 (by rfl) ⟨5469587, by rfl⟩ : syracuseStep 7292783 = 10939175) B10939175
theorem B6146171 : Blo 944585 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B1199387 : Blo 944585 1199387 := bstep (se 1 (by rfl) ⟨899540, by rfl⟩ : syracuseStep 1199387 = 1799081) B1799081
theorem B58248649 : Blo 944585 58248649 := bstep (se 2 (by rfl) ⟨21843243, by rfl⟩ : syracuseStep 58248649 = 43686487) B43686487
theorem B81841913 : Blo 944585 81841913 := bstep (se 2 (by rfl) ⟨30690717, by rfl⟩ : syracuseStep 81841913 = 61381435) B61381435
theorem B3199391 : Blo 944585 3199391 := bstep (se 1 (by rfl) ⟨2399543, by rfl⟩ : syracuseStep 3199391 = 4799087) B4799087
theorem B44914031 : Blo 944585 44914031 := bstep (se 1 (by rfl) ⟨33685523, by rfl⟩ : syracuseStep 44914031 = 67371047) B67371047
theorem B3200471 : Blo 944585 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B970151417 : Blo 944585 970151417 := bstep (se 2 (by rfl) ⟨363806781, by rfl⟩ : syracuseStep 970151417 = 727613563) B727613563
theorem B2020891 : Blo 944585 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B3201065 : Blo 944585 3201065 := bstep (se 2 (by rfl) ⟨1200399, by rfl⟩ : syracuseStep 3201065 = 2400799) B2400799
theorem B1595551 : Blo 944585 1595551 := bstep (se 1 (by rfl) ⟨1196663, by rfl⟩ : syracuseStep 1595551 = 2393327) B2393327
theorem B2874095 : Blo 944585 2874095 := bstep (se 1 (by rfl) ⟨2155571, by rfl⟩ : syracuseStep 2874095 = 4311143) B4311143
theorem B1596287 : Blo 944585 1596287 := bstep (se 1 (by rfl) ⟨1197215, by rfl⟩ : syracuseStep 1596287 = 2394431) B2394431
theorem B3595367 : Blo 944585 3595367 := bstep (se 1 (by rfl) ⟨2696525, by rfl⟩ : syracuseStep 3595367 = 5393051) B5393051
theorem B12937097 : Blo 944585 12937097 := bstep (se 2 (by rfl) ⟨4851411, by rfl⟩ : syracuseStep 12937097 = 9702823) B9702823
theorem B944591 : Blo 944585 944591 := bstep (se 1 (by rfl) ⟨708443, by rfl⟩ : syracuseStep 944591 = 1416887) B1416887
theorem B5401343 : Blo 944585 5401343 := bstep (se 1 (by rfl) ⟨4051007, by rfl⟩ : syracuseStep 5401343 = 8102015) B8102015
theorem B944923 : Blo 944585 944923 := bstep (se 1 (by rfl) ⟨708692, by rfl⟩ : syracuseStep 944923 = 1417385) B1417385
theorem B5402051 : Blo 944585 5402051 := bstep (se 1 (by rfl) ⟨4051538, by rfl⟩ : syracuseStep 5402051 = 8103077) B8103077
theorem B945775 : Blo 944585 945775 := bstep (se 1 (by rfl) ⟨709331, by rfl⟩ : syracuseStep 945775 = 1418663) B1418663
theorem B2125961 : Blo 944585 2125961 := bstep (se 2 (by rfl) ⟨797235, by rfl⟩ : syracuseStep 2125961 = 1594471) B1594471
theorem B262402685 : Blo 944585 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B947015 : Blo 944585 947015 := bstep (se 1 (by rfl) ⟨710261, by rfl⟩ : syracuseStep 947015 = 1420523) B1420523
theorem B167998673 : Blo 944585 167998673 := bstep (se 2 (by rfl) ⟨62999502, by rfl⟩ : syracuseStep 167998673 = 125999005) B125999005
theorem B947559 : Blo 944585 947559 := bstep (se 1 (by rfl) ⟨710669, by rfl⟩ : syracuseStep 947559 = 1421339) B1421339
theorem B5109239 : Blo 944585 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B947759 : Blo 944585 947759 := bstep (se 1 (by rfl) ⟨710819, by rfl⟩ : syracuseStep 947759 = 1421639) B1421639
theorem B18184175 : Blo 944585 18184175 := bstep (se 1 (by rfl) ⟨13638131, by rfl⟩ : syracuseStep 18184175 = 27276263) B27276263
theorem B948327 : Blo 944585 948327 := bstep (se 1 (by rfl) ⟨711245, by rfl⟩ : syracuseStep 948327 = 1422491) B1422491
theorem B14776465 : Blo 944585 14776465 := bstep (se 2 (by rfl) ⟨5541174, by rfl⟩ : syracuseStep 14776465 = 11082349) B11082349
theorem B3242963 : Blo 944585 3242963 := bstep (se 1 (by rfl) ⟨2432222, by rfl⟩ : syracuseStep 3242963 = 4864445) B4864445
theorem B2129255 : Blo 944585 2129255 := bstep (se 1 (by rfl) ⟨1596941, by rfl⟩ : syracuseStep 2129255 = 3193883) B3193883
theorem B12975673 : Blo 944585 12975673 := bstep (se 2 (by rfl) ⟨4865877, by rfl⟩ : syracuseStep 12975673 = 9731755) B9731755
theorem B4097447 : Blo 944585 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B4786451 : Blo 944585 4786451 := bstep (se 1 (by rfl) ⟨3589838, by rfl⟩ : syracuseStep 4786451 = 7179677) B7179677
theorem B54561275 : Blo 944585 54561275 := bstep (se 1 (by rfl) ⟨40920956, by rfl⟩ : syracuseStep 54561275 = 81841913) B81841913
theorem B5114603 : Blo 944585 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B2132927 : Blo 944585 2132927 := bstep (se 1 (by rfl) ⟨1599695, by rfl⟩ : syracuseStep 2132927 = 3199391) B3199391
theorem B2133647 : Blo 944585 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B2134043 : Blo 944585 2134043 := bstep (se 1 (by rfl) ⟨1600532, by rfl⟩ : syracuseStep 2134043 = 3201065) B3201065
theorem B77664865 : Blo 944585 77664865 := bstep (se 2 (by rfl) ⟨29124324, by rfl⟩ : syracuseStep 77664865 = 58248649) B58248649
theorem B2396911 : Blo 944585 2396911 := bstep (se 1 (by rfl) ⟨1797683, by rfl⟩ : syracuseStep 2396911 = 3595367) B3595367
theorem B6231869 : Blo 944585 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B8624731 : Blo 944585 8624731 := bstep (se 1 (by rfl) ⟨6468548, by rfl⟩ : syracuseStep 8624731 = 12937097) B12937097
theorem B2694521 : Blo 944585 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B1417307 : Blo 944585 1417307 := bstep (se 1 (by rfl) ⟨1062980, by rfl⟩ : syracuseStep 1417307 = 2125961) B2125961
theorem B1417337 : Blo 944585 1417337 := bstep (se 2 (by rfl) ⟨531501, by rfl⟩ : syracuseStep 1417337 = 1063003) B1063003
theorem B19701953 : Blo 944585 19701953 := bstep (se 2 (by rfl) ⟨7388232, by rfl⟩ : syracuseStep 19701953 = 14776465) B14776465
theorem B4793579 : Blo 944585 4793579 := bstep (se 1 (by rfl) ⟨3595184, by rfl⟩ : syracuseStep 4793579 = 7190369) B7190369
theorem B4040057 : Blo 944585 4040057 := bstep (se 2 (by rfl) ⟨1515021, by rfl⟩ : syracuseStep 4040057 = 3030043) B3030043
theorem B2729753 : Blo 944585 2729753 := bstep (se 2 (by rfl) ⟨1023657, by rfl⟩ : syracuseStep 2729753 = 2047315) B2047315
theorem B5384303 : Blo 944585 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B8071397 : Blo 944585 8071397 := bstep (se 4 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 8071397 = 1513387) B1513387
theorem B1419503 : Blo 944585 1419503 := bstep (se 1 (by rfl) ⟨1064627, by rfl⟩ : syracuseStep 1419503 = 2129255) B2129255
theorem B6826447 : Blo 944585 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B7875209 : Blo 944585 7875209 := bstep (se 2 (by rfl) ⟨2953203, by rfl⟩ : syracuseStep 7875209 = 5906407) B5906407
theorem B3189455 : Blo 944585 3189455 := bstep (se 1 (by rfl) ⟨2392091, by rfl⟩ : syracuseStep 3189455 = 4784183) B4784183
theorem B1419995 : Blo 944585 1419995 := bstep (se 1 (by rfl) ⟨1064996, by rfl⟩ : syracuseStep 1419995 = 2129993) B2129993
theorem B1420169 : Blo 944585 1420169 := bstep (se 2 (by rfl) ⟨532563, by rfl⟩ : syracuseStep 1420169 = 1065127) B1065127
theorem B1420199 : Blo 944585 1420199 := bstep (se 1 (by rfl) ⟨1065149, by rfl⟩ : syracuseStep 1420199 = 2130299) B2130299
theorem B21277703 : Blo 944585 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B1420607 : Blo 944585 1420607 := bstep (se 1 (by rfl) ⟨1065455, by rfl⟩ : syracuseStep 1420607 = 2130911) B2130911
theorem B36810593 : Blo 944585 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B4861855 : Blo 944585 4861855 := bstep (se 1 (by rfl) ⟨3646391, by rfl⟩ : syracuseStep 4861855 = 7292783) B7292783
theorem B1421291 : Blo 944585 1421291 := bstep (se 1 (by rfl) ⟨1065968, by rfl⟩ : syracuseStep 1421291 = 2131937) B2131937
theorem B5388929 : Blo 944585 5388929 := bstep (se 2 (by rfl) ⟨2020848, by rfl⟩ : syracuseStep 5388929 = 4041697) B4041697
theorem B1916063 : Blo 944585 1916063 := bstep (se 1 (by rfl) ⟨1437047, by rfl⟩ : syracuseStep 1916063 = 2874095) B2874095
theorem B1064191 : Blo 944585 1064191 := bstep (se 1 (by rfl) ⟨798143, by rfl⟩ : syracuseStep 1064191 = 1596287) B1596287
theorem B10928105 : Blo 944585 10928105 := bstep (se 2 (by rfl) ⟨4098039, by rfl⟩ : syracuseStep 10928105 = 8196079) B8196079
theorem B2278847 : Blo 944585 2278847 := bstep (se 1 (by rfl) ⟨1709135, by rfl⟩ : syracuseStep 2278847 = 3418271) B3418271
theorem B9094625 : Blo 944585 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B2833697357 : Blo 944585 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B174935123 : Blo 944585 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B3198365 : Blo 944585 3198365 := bstep (se 3 (by rfl) ⟨599693, by rfl⟩ : syracuseStep 3198365 = 1199387) B1199387
theorem B3036001 : Blo 944585 3036001 := bstep (se 2 (by rfl) ⟨1138500, by rfl⟩ : syracuseStep 3036001 = 2277001) B2277001
theorem B12148055 : Blo 944585 12148055 := bstep (se 1 (by rfl) ⟨9111041, by rfl⟩ : syracuseStep 12148055 = 18222083) B18222083
theorem B7691885 : Blo 944585 7691885 := bstep (se 3 (by rfl) ⟨1442228, by rfl⟩ : syracuseStep 7691885 = 2884457) B2884457
theorem B1597583 : Blo 944585 1597583 := bstep (se 1 (by rfl) ⟨1198187, by rfl⟩ : syracuseStep 1597583 = 2396375) B2396375
theorem B1597819 : Blo 944585 1597819 := bstep (se 1 (by rfl) ⟨1198364, by rfl⟩ : syracuseStep 1597819 = 2396729) B2396729
theorem B29942687 : Blo 944585 29942687 := bstep (se 1 (by rfl) ⟨22457015, by rfl⟩ : syracuseStep 29942687 = 44914031) B44914031
theorem B646767611 : Blo 944585 646767611 := bstep (se 1 (by rfl) ⟨485075708, by rfl⟩ : syracuseStep 646767611 = 970151417) B970151417
theorem B5399567 : Blo 944585 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B32007419 : Blo 944585 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B1598879 : Blo 944585 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B9103697 : Blo 944585 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B944731 : Blo 944585 944731 := bstep (se 1 (by rfl) ⟨708548, by rfl⟩ : syracuseStep 944731 = 1417097) B1417097
theorem B1796735 : Blo 944585 1796735 := bstep (se 1 (by rfl) ⟨1347551, by rfl⟩ : syracuseStep 1796735 = 2695103) B2695103
theorem B1600283 : Blo 944585 1600283 := bstep (se 1 (by rfl) ⟨1200212, by rfl⟩ : syracuseStep 1600283 = 2400425) B2400425
theorem B944999 : Blo 944585 944999 := bstep (se 1 (by rfl) ⟨708749, by rfl⟩ : syracuseStep 944999 = 1417499) B1417499
theorem B945279 : Blo 944585 945279 := bstep (se 1 (by rfl) ⟨708959, by rfl⟩ : syracuseStep 945279 = 1417919) B1417919
theorem B945567 : Blo 944585 945567 := bstep (se 1 (by rfl) ⟨709175, by rfl⟩ : syracuseStep 945567 = 1418351) B1418351
theorem B945711 : Blo 944585 945711 := bstep (se 1 (by rfl) ⟨709283, by rfl⟩ : syracuseStep 945711 = 1418567) B1418567
theorem B945903 : Blo 944585 945903 := bstep (se 1 (by rfl) ⟨709427, by rfl⟩ : syracuseStep 945903 = 1418855) B1418855
theorem B5468201 : Blo 944585 5468201 := bstep (se 2 (by rfl) ⟨2050575, by rfl⟩ : syracuseStep 5468201 = 4101151) B4101151
theorem B946247 : Blo 944585 946247 := bstep (se 1 (by rfl) ⟨709685, by rfl⟩ : syracuseStep 946247 = 1419371) B1419371
theorem B946267 : Blo 944585 946267 := bstep (se 1 (by rfl) ⟨709700, by rfl⟩ : syracuseStep 946267 = 1419401) B1419401
theorem B946415 : Blo 944585 946415 := bstep (se 1 (by rfl) ⟨709811, by rfl⟩ : syracuseStep 946415 = 1419623) B1419623
theorem B3600895 : Blo 944585 3600895 := bstep (se 1 (by rfl) ⟨2700671, by rfl⟩ : syracuseStep 3600895 = 5401343) B5401343
theorem B946843 : Blo 944585 946843 := bstep (se 1 (by rfl) ⟨710132, by rfl⟩ : syracuseStep 946843 = 1420265) B1420265
theorem B3601367 : Blo 944585 3601367 := bstep (se 1 (by rfl) ⟨2701025, by rfl⟩ : syracuseStep 3601367 = 5402051) B5402051
theorem B947615 : Blo 944585 947615 := bstep (se 1 (by rfl) ⟨710711, by rfl⟩ : syracuseStep 947615 = 1421423) B1421423
theorem B947647 : Blo 944585 947647 := bstep (se 1 (by rfl) ⟨710735, by rfl⟩ : syracuseStep 947647 = 1421471) B1421471
theorem B2127401 : Blo 944585 2127401 := bstep (se 2 (by rfl) ⟨797775, by rfl⟩ : syracuseStep 2127401 = 1595551) B1595551
theorem B947871 : Blo 944585 947871 := bstep (se 1 (by rfl) ⟨710903, by rfl⟩ : syracuseStep 947871 = 1421807) B1421807
theorem B4552811 : Blo 944585 4552811 := bstep (se 1 (by rfl) ⟨3414608, by rfl⟩ : syracuseStep 4552811 = 6829217) B6829217
theorem B948351 : Blo 944585 948351 := bstep (se 1 (by rfl) ⟨711263, by rfl⟩ : syracuseStep 948351 = 1422527) B1422527
theorem B111999115 : Blo 944585 111999115 := bstep (se 1 (by rfl) ⟨83999336, by rfl⟩ : syracuseStep 111999115 = 167998673) B167998673
theorem B3406159 : Blo 944585 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B25852391 : Blo 944585 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B12122783 : Blo 944585 12122783 := bstep (se 1 (by rfl) ⟨9092087, by rfl⟩ : syracuseStep 12122783 = 18184175) B18184175
theorem B7174817 : Blo 944585 7174817 := bstep (se 2 (by rfl) ⟨2690556, by rfl⟩ : syracuseStep 7174817 = 5381113) B5381113
theorem B1080103 : Blo 944585 1080103 := bstep (se 1 (by rfl) ⟨810077, by rfl⟩ : syracuseStep 1080103 = 1620155) B1620155
theorem B22117313 : Blo 944585 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B2161975 : Blo 944585 2161975 := bstep (se 1 (by rfl) ⟨1621481, by rfl⟩ : syracuseStep 2161975 = 3242963) B3242963
theorem B17300897 : Blo 944585 17300897 := bstep (se 2 (by rfl) ⟨6487836, by rfl⟩ : syracuseStep 17300897 = 12975673) B12975673
theorem B2129327 : Blo 944585 2129327 := bstep (se 1 (by rfl) ⟨1596995, by rfl⟩ : syracuseStep 2129327 = 3193991) B3193991
theorem B2130425 : Blo 944585 2130425 := bstep (se 2 (by rfl) ⟨798909, by rfl⟩ : syracuseStep 2130425 = 1597819) B1597819
theorem B597328613 : Blo 944585 597328613 := bstep (se 4 (by rfl) ⟨55999557, by rfl⟩ : syracuseStep 597328613 = 111999115) B111999115
theorem B6063083 : Blo 944585 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B36374183 : Blo 944585 36374183 := bstep (se 1 (by rfl) ⟨27280637, by rfl⟩ : syracuseStep 36374183 = 54561275) B54561275
theorem B3409735 : Blo 944585 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B116623415 : Blo 944585 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B2132243 : Blo 944585 2132243 := bstep (se 1 (by rfl) ⟨1599182, by rfl⟩ : syracuseStep 2132243 = 3198365) B3198365
theorem B8098703 : Blo 944585 8098703 := bstep (se 1 (by rfl) ⟨6074027, by rfl⟩ : syracuseStep 8098703 = 12148055) B12148055
theorem B103553153 : Blo 944585 103553153 := bstep (se 2 (by rfl) ⟨38832432, by rfl⟩ : syracuseStep 103553153 = 77664865) B77664865
theorem B21338279 : Blo 944585 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B2693371 : Blo 944585 2693371 := bstep (se 1 (by rfl) ⟨2020028, by rfl⟩ : syracuseStep 2693371 = 4040057) B4040057
theorem B5380931 : Blo 944585 5380931 := bstep (se 1 (by rfl) ⟨4035698, by rfl⟩ : syracuseStep 5380931 = 8071397) B8071397
theorem B6069131 : Blo 944585 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B3645467 : Blo 944585 3645467 := bstep (se 1 (by rfl) ⟨2734100, by rfl⟩ : syracuseStep 3645467 = 5468201) B5468201
theorem B2400911 : Blo 944585 2400911 := bstep (se 1 (by rfl) ⟨1800683, by rfl⟩ : syracuseStep 2400911 = 3601367) B3601367
theorem B1418267 : Blo 944585 1418267 := bstep (se 1 (by rfl) ⟨1063700, by rfl⟩ : syracuseStep 1418267 = 2127401) B2127401
theorem B1418921 : Blo 944585 1418921 := bstep (se 2 (by rfl) ⟨532095, by rfl⟩ : syracuseStep 1418921 = 1064191) B1064191
theorem B1419551 : Blo 944585 1419551 := bstep (se 1 (by rfl) ⟨1064663, by rfl⟩ : syracuseStep 1419551 = 2129327) B2129327
theorem B7285403 : Blo 944585 7285403 := bstep (se 1 (by rfl) ⟨5464052, by rfl⟩ : syracuseStep 7285403 = 10928105) B10928105
theorem B1519231 : Blo 944585 1519231 := bstep (se 1 (by rfl) ⟨1139423, by rfl⟩ : syracuseStep 1519231 = 2278847) B2278847
theorem B3190967 : Blo 944585 3190967 := bstep (se 1 (by rfl) ⟨2393225, by rfl⟩ : syracuseStep 3190967 = 4786451) B4786451
theorem B1421951 : Blo 944585 1421951 := bstep (se 1 (by rfl) ⟨1066463, by rfl⟩ : syracuseStep 1421951 = 2132927) B2132927
theorem B1422431 : Blo 944585 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B1422695 : Blo 944585 1422695 := bstep (se 1 (by rfl) ⟨1067021, by rfl⟩ : syracuseStep 1422695 = 2134043) B2134043
theorem B1570585301 : Blo 944585 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B5127923 : Blo 944585 5127923 := bstep (se 1 (by rfl) ⟨3845942, by rfl⟩ : syracuseStep 5127923 = 7691885) B7691885
theorem B1065055 : Blo 944585 1065055 := bstep (se 1 (by rfl) ⟨798791, by rfl⟩ : syracuseStep 1065055 = 1597583) B1597583
theorem B431178407 : Blo 944585 431178407 := bstep (se 1 (by rfl) ⟨323383805, by rfl⟩ : syracuseStep 431178407 = 646767611) B646767611
theorem B4801193 : Blo 944585 4801193 := bstep (se 2 (by rfl) ⟨1800447, by rfl⟩ : syracuseStep 4801193 = 3600895) B3600895
theorem B3195719 : Blo 944585 3195719 := bstep (se 1 (by rfl) ⟨2396789, by rfl⟩ : syracuseStep 3195719 = 4793579) B4793579
theorem B1065919 : Blo 944585 1065919 := bstep (se 1 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 1065919 = 1598879) B1598879
theorem B3195881 : Blo 944585 3195881 := bstep (se 2 (by rfl) ⟨1198455, by rfl⟩ : syracuseStep 3195881 = 2396911) B2396911
theorem B4048001 : Blo 944585 4048001 := bstep (se 2 (by rfl) ⟨1518000, by rfl⟩ : syracuseStep 4048001 = 3036001) B3036001
theorem B1819835 : Blo 944585 1819835 := bstep (se 1 (by rfl) ⟨1364876, by rfl⟩ : syracuseStep 1819835 = 2729753) B2729753
theorem B3589535 : Blo 944585 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1197823 : Blo 944585 1197823 := bstep (se 1 (by rfl) ⟨898367, by rfl⟩ : syracuseStep 1197823 = 1796735) B1796735
theorem B1066855 : Blo 944585 1066855 := bstep (se 1 (by rfl) ⟨800141, by rfl⟩ : syracuseStep 1066855 = 1600283) B1600283
theorem B4541545 : Blo 944585 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B3035207 : Blo 944585 3035207 := bstep (se 1 (by rfl) ⟨2276405, by rfl⟩ : syracuseStep 3035207 = 4552811) B4552811
theorem B3592619 : Blo 944585 3592619 := bstep (se 1 (by rfl) ⟨2694464, by rfl⟩ : syracuseStep 3592619 = 5388929) B5388929
theorem B8081855 : Blo 944585 8081855 := bstep (se 1 (by rfl) ⟨6061391, by rfl⟩ : syracuseStep 8081855 = 12122783) B12122783
theorem B1889131571 : Blo 944585 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B79847165 : Blo 944585 79847165 := bstep (se 3 (by rfl) ⟨14971343, by rfl⟩ : syracuseStep 79847165 = 29942687) B29942687
theorem B9101929 : Blo 944585 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B4154579 : Blo 944585 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B43706101 : Blo 944585 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B1796347 : Blo 944585 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B6482473 : Blo 944585 6482473 := bstep (se 2 (by rfl) ⟨2430927, by rfl⟩ : syracuseStep 6482473 = 4861855) B4861855
theorem B944871 : Blo 944585 944871 := bstep (se 1 (by rfl) ⟨708653, by rfl⟩ : syracuseStep 944871 = 1417307) B1417307
theorem B944891 : Blo 944585 944891 := bstep (se 1 (by rfl) ⟨708668, by rfl⟩ : syracuseStep 944891 = 1417337) B1417337
theorem B13134635 : Blo 944585 13134635 := bstep (se 1 (by rfl) ⟨9850976, by rfl⟩ : syracuseStep 13134635 = 19701953) B19701953
theorem B3599711 : Blo 944585 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B946335 : Blo 944585 946335 := bstep (se 1 (by rfl) ⟨709751, by rfl⟩ : syracuseStep 946335 = 1419503) B1419503
theorem B21000557 : Blo 944585 21000557 := bstep (se 3 (by rfl) ⟨3937604, by rfl⟩ : syracuseStep 21000557 = 7875209) B7875209
theorem B2126303 : Blo 944585 2126303 := bstep (se 1 (by rfl) ⟨1594727, by rfl⟩ : syracuseStep 2126303 = 3189455) B3189455
theorem B946663 : Blo 944585 946663 := bstep (se 1 (by rfl) ⟨709997, by rfl⟩ : syracuseStep 946663 = 1419995) B1419995
theorem B946779 : Blo 944585 946779 := bstep (se 1 (by rfl) ⟨710084, by rfl⟩ : syracuseStep 946779 = 1420169) B1420169
theorem B946799 : Blo 944585 946799 := bstep (se 1 (by rfl) ⟨710099, by rfl⟩ : syracuseStep 946799 = 1420199) B1420199
theorem B14185135 : Blo 944585 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B947071 : Blo 944585 947071 := bstep (se 1 (by rfl) ⟨710303, by rfl⟩ : syracuseStep 947071 = 1420607) B1420607
theorem B947527 : Blo 944585 947527 := bstep (se 1 (by rfl) ⟨710645, by rfl⟩ : syracuseStep 947527 = 1421291) B1421291
theorem B11499641 : Blo 944585 11499641 := bstep (se 2 (by rfl) ⟨4312365, by rfl⟩ : syracuseStep 11499641 = 8624731) B8624731
theorem B1440137 : Blo 944585 1440137 := bstep (se 2 (by rfl) ⟨540051, by rfl⟩ : syracuseStep 1440137 = 1080103) B1080103
theorem B17234927 : Blo 944585 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B2882633 : Blo 944585 2882633 := bstep (se 2 (by rfl) ⟨1080987, by rfl⟩ : syracuseStep 2882633 = 2161975) B2161975
theorem B4783211 : Blo 944585 4783211 := bstep (se 1 (by rfl) ⟨3587408, by rfl⟩ : syracuseStep 4783211 = 7174817) B7174817
theorem B14744875 : Blo 944585 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B1277375 : Blo 944585 1277375 := bstep (se 1 (by rfl) ⟨958031, by rfl⟩ : syracuseStep 1277375 = 1916063) B1916063
theorem B11533931 : Blo 944585 11533931 := bstep (se 1 (by rfl) ⟨8650448, by rfl⟩ : syracuseStep 11533931 = 17300897) B17300897
theorem B2130479 : Blo 944585 2130479 := bstep (se 1 (by rfl) ⟨1597859, by rfl⟩ : syracuseStep 2130479 = 3195719) B3195719
theorem B2130587 : Blo 944585 2130587 := bstep (se 1 (by rfl) ⟨1597940, by rfl⟩ : syracuseStep 2130587 = 3195881) B3195881
theorem B1213223 : Blo 944585 1213223 := bstep (se 1 (by rfl) ⟨909917, by rfl⟩ : syracuseStep 1213223 = 1819835) B1819835
theorem B2393023 : Blo 944585 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B24249455 : Blo 944585 24249455 := bstep (se 1 (by rfl) ⟨18187091, by rfl⟩ : syracuseStep 24249455 = 36374183) B36374183
theorem B2395079 : Blo 944585 2395079 := bstep (se 1 (by rfl) ⟨1796309, by rfl⟩ : syracuseStep 2395079 = 3592619) B3592619
theorem B2395129 : Blo 944585 2395129 := bstep (se 2 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 2395129 = 1796347) B1796347
theorem B14225519 : Blo 944585 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B18913513 : Blo 944585 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B3840365 : Blo 944585 3840365 := bstep (se 3 (by rfl) ⟨720068, by rfl⟩ : syracuseStep 3840365 = 1440137) B1440137
theorem B4856935 : Blo 944585 4856935 := bstep (se 1 (by rfl) ⟨3642701, by rfl⟩ : syracuseStep 4856935 = 7285403) B7285403
theorem B8756423 : Blo 944585 8756423 := bstep (se 1 (by rfl) ⟨6567317, by rfl⟩ : syracuseStep 8756423 = 13134635) B13134635
theorem B2399807 : Blo 944585 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B14000371 : Blo 944585 14000371 := bstep (se 1 (by rfl) ⟨10500278, by rfl⟩ : syracuseStep 14000371 = 21000557) B21000557
theorem B1417535 : Blo 944585 1417535 := bstep (se 1 (by rfl) ⟨1063151, by rfl⟩ : syracuseStep 1417535 = 2126303) B2126303
theorem B3188807 : Blo 944585 3188807 := bstep (se 1 (by rfl) ⟨2391605, by rfl⟩ : syracuseStep 3188807 = 4783211) B4783211
theorem B3418615 : Blo 944585 3418615 := bstep (se 1 (by rfl) ⟨2563961, by rfl⟩ : syracuseStep 3418615 = 5127923) B5127923
theorem B1420073 : Blo 944585 1420073 := bstep (se 2 (by rfl) ⟨532527, by rfl⟩ : syracuseStep 1420073 = 1065055) B1065055
theorem B1420283 : Blo 944585 1420283 := bstep (se 1 (by rfl) ⟨1065212, by rfl⟩ : syracuseStep 1420283 = 2130425) B2130425
theorem B287452271 : Blo 944585 287452271 := bstep (se 1 (by rfl) ⟨215589203, by rfl⟩ : syracuseStep 287452271 = 431178407) B431178407
theorem B4042055 : Blo 944585 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B2698667 : Blo 944585 2698667 := bstep (se 1 (by rfl) ⟨2024000, by rfl⟩ : syracuseStep 2698667 = 4048001) B4048001
theorem B12135905 : Blo 944585 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B138292757 : Blo 944585 138292757 := bstep (se 6 (by rfl) ⟨3241236, by rfl⟩ : syracuseStep 138292757 = 6482473) B6482473
theorem B1421225 : Blo 944585 1421225 := bstep (se 2 (by rfl) ⟨532959, by rfl⟩ : syracuseStep 1421225 = 1065919) B1065919
theorem B1421495 : Blo 944585 1421495 := bstep (se 1 (by rfl) ⟨1066121, by rfl⟩ : syracuseStep 1421495 = 2132243) B2132243
theorem B58274801 : Blo 944585 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B1422473 : Blo 944585 1422473 := bstep (se 2 (by rfl) ⟨533427, by rfl⟩ : syracuseStep 1422473 = 1066855) B1066855
theorem B5387903 : Blo 944585 5387903 := bstep (se 1 (by rfl) ⟨4040927, by rfl⟩ : syracuseStep 5387903 = 8081855) B8081855
theorem B3587287 : Blo 944585 3587287 := bstep (se 1 (by rfl) ⟨2690465, by rfl⟩ : syracuseStep 3587287 = 5380931) B5380931
theorem B4046087 : Blo 944585 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B1259421047 : Blo 944585 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B2769719 : Blo 944585 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B7687021 : Blo 944585 7687021 := bstep (se 3 (by rfl) ⟨1441316, by rfl⟩ : syracuseStep 7687021 = 2882633) B2882633
theorem B3591161 : Blo 944585 3591161 := bstep (se 2 (by rfl) ⟨1346685, by rfl⟩ : syracuseStep 3591161 = 2693371) B2693371
theorem B1047056867 : Blo 944585 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B11489951 : Blo 944585 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B7689287 : Blo 944585 7689287 := bstep (se 1 (by rfl) ⟨5766965, by rfl⟩ : syracuseStep 7689287 = 11533931) B11533931
theorem B38884981 : Blo 944585 38884981 := bstep (se 5 (by rfl) ⟨1822733, by rfl⟩ : syracuseStep 38884981 = 3645467) B3645467
theorem B3200795 : Blo 944585 3200795 := bstep (se 1 (by rfl) ⟨2400596, by rfl⟩ : syracuseStep 3200795 = 4801193) B4801193
theorem B398219075 : Blo 944585 398219075 := bstep (se 1 (by rfl) ⟨298664306, by rfl⟩ : syracuseStep 398219075 = 597328613) B597328613
theorem B77748943 : Blo 944585 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B1597097 : Blo 944585 1597097 := bstep (se 2 (by rfl) ⟨598911, by rfl⟩ : syracuseStep 1597097 = 1197823) B1197823
theorem B4546313 : Blo 944585 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B2023471 : Blo 944585 2023471 := bstep (se 1 (by rfl) ⟨1517603, by rfl⟩ : syracuseStep 2023471 = 3035207) B3035207
theorem B5399135 : Blo 944585 5399135 := bstep (se 1 (by rfl) ⟨4049351, by rfl⟩ : syracuseStep 5399135 = 8098703) B8098703
theorem B69035435 : Blo 944585 69035435 := bstep (se 1 (by rfl) ⟨51776576, by rfl⟩ : syracuseStep 69035435 = 103553153) B103553153
theorem B6055393 : Blo 944585 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B2025641 : Blo 944585 2025641 := bstep (se 2 (by rfl) ⟨759615, by rfl⟩ : syracuseStep 2025641 = 1519231) B1519231
theorem B1600607 : Blo 944585 1600607 := bstep (se 1 (by rfl) ⟨1200455, by rfl⟩ : syracuseStep 1600607 = 2400911) B2400911
theorem B945511 : Blo 944585 945511 := bstep (se 1 (by rfl) ⟨709133, by rfl⟩ : syracuseStep 945511 = 1418267) B1418267
theorem B945947 : Blo 944585 945947 := bstep (se 1 (by rfl) ⟨709460, by rfl⟩ : syracuseStep 945947 = 1418921) B1418921
theorem B946367 : Blo 944585 946367 := bstep (se 1 (by rfl) ⟨709775, by rfl⟩ : syracuseStep 946367 = 1419551) B1419551
theorem B2127311 : Blo 944585 2127311 := bstep (se 1 (by rfl) ⟨1595483, by rfl⟩ : syracuseStep 2127311 = 3190967) B3190967
theorem B947967 : Blo 944585 947967 := bstep (se 1 (by rfl) ⟨710975, by rfl⟩ : syracuseStep 947967 = 1421951) B1421951
theorem B948287 : Blo 944585 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B948463 : Blo 944585 948463 := bstep (se 1 (by rfl) ⟨711347, by rfl⟩ : syracuseStep 948463 = 1422695) B1422695
theorem B3406333 : Blo 944585 3406333 := bstep (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) B1277375
theorem B7666427 : Blo 944585 7666427 := bstep (se 1 (by rfl) ⟨5749820, by rfl⟩ : syracuseStep 7666427 = 11499641) B11499641
theorem B19659833 : Blo 944585 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B212925773 : Blo 944585 212925773 := bstep (se 3 (by rfl) ⟨39923582, by rfl⟩ : syracuseStep 212925773 = 79847165) B79847165
theorem B30639869 : Blo 944585 30639869 := bstep (se 3 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 30639869 = 11489951) B11489951
theorem B2394107 : Blo 944585 2394107 := bstep (se 1 (by rfl) ⟨1795580, by rfl⟩ : syracuseStep 2394107 = 3591161) B3591161
theorem B4558153 : Blo 944585 4558153 := bstep (se 2 (by rfl) ⟨1709307, by rfl⟩ : syracuseStep 4558153 = 3418615) B3418615
theorem B2133863 : Blo 944585 2133863 := bstep (se 1 (by rfl) ⟨1600397, by rfl⟩ : syracuseStep 2133863 = 3200795) B3200795
theorem B2560243 : Blo 944585 2560243 := bstep (se 1 (by rfl) ⟨1920182, by rfl⟩ : syracuseStep 2560243 = 3840365) B3840365
theorem B5837615 : Blo 944585 5837615 := bstep (se 1 (by rfl) ⟨4378211, by rfl⟩ : syracuseStep 5837615 = 8756423) B8756423
theorem B1350427 : Blo 944585 1350427 := bstep (se 1 (by rfl) ⟨1012820, by rfl⟩ : syracuseStep 1350427 = 2025641) B2025641
theorem B51846641 : Blo 944585 51846641 := bstep (se 2 (by rfl) ⟨19442490, by rfl⟩ : syracuseStep 51846641 = 38884981) B38884981
theorem B2694703 : Blo 944585 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B1418207 : Blo 944585 1418207 := bstep (se 1 (by rfl) ⟨1063655, by rfl⟩ : syracuseStep 1418207 = 2127311) B2127311
theorem B2697391 : Blo 944585 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B2697961 : Blo 944585 2697961 := bstep (se 2 (by rfl) ⟨1011735, by rfl⟩ : syracuseStep 2697961 = 2023471) B2023471
theorem B1420319 : Blo 944585 1420319 := bstep (se 1 (by rfl) ⟨1065239, by rfl⟩ : syracuseStep 1420319 = 2130479) B2130479
theorem B1420391 : Blo 944585 1420391 := bstep (se 1 (by rfl) ⟨1065293, by rfl⟩ : syracuseStep 1420391 = 2130587) B2130587
theorem B16166303 : Blo 944585 16166303 := bstep (se 1 (by rfl) ⟨12124727, by rfl⟩ : syracuseStep 16166303 = 24249455) B24249455
theorem B3190697 : Blo 944585 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B8073857 : Blo 944585 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B7385917 : Blo 944585 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B9483679 : Blo 944585 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B698037911 : Blo 944585 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B3193505 : Blo 944585 3193505 := bstep (se 2 (by rfl) ⟨1197564, by rfl⟩ : syracuseStep 3193505 = 2395129) B2395129
theorem B1064731 : Blo 944585 1064731 := bstep (se 1 (by rfl) ⟨798548, by rfl⟩ : syracuseStep 1064731 = 1597097) B1597097
theorem B3030875 : Blo 944585 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B46023623 : Blo 944585 46023623 := bstep (se 1 (by rfl) ⟨34517717, by rfl⟩ : syracuseStep 46023623 = 69035435) B69035435
theorem B1067071 : Blo 944585 1067071 := bstep (se 1 (by rfl) ⟨800303, by rfl⟩ : syracuseStep 1067071 = 1600607) B1600607
theorem B92195171 : Blo 944585 92195171 := bstep (se 1 (by rfl) ⟨69146378, by rfl⟩ : syracuseStep 92195171 = 138292757) B138292757
theorem B25218017 : Blo 944585 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B38849867 : Blo 944585 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B4541777 : Blo 944585 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B103665257 : Blo 944585 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B3591935 : Blo 944585 3591935 := bstep (se 1 (by rfl) ⟨2693951, by rfl⟩ : syracuseStep 3591935 = 5387903) B5387903
theorem B6475913 : Blo 944585 6475913 := bstep (se 2 (by rfl) ⟨2428467, by rfl⟩ : syracuseStep 6475913 = 4856935) B4856935
theorem B74668645 : Blo 944585 74668645 := bstep (se 4 (by rfl) ⟨7000185, by rfl⟩ : syracuseStep 74668645 = 14000371) B14000371
theorem B1596719 : Blo 944585 1596719 := bstep (se 1 (by rfl) ⟨1197539, by rfl⟩ : syracuseStep 1596719 = 2395079) B2395079
theorem B3235261 : Blo 944585 3235261 := bstep (se 3 (by rfl) ⟨606611, by rfl⟩ : syracuseStep 3235261 = 1213223) B1213223
theorem B20504765 : Blo 944585 20504765 := bstep (se 3 (by rfl) ⟨3844643, by rfl⟩ : syracuseStep 20504765 = 7689287) B7689287
theorem B10249361 : Blo 944585 10249361 := bstep (se 2 (by rfl) ⟨3843510, by rfl⟩ : syracuseStep 10249361 = 7687021) B7687021
theorem B265479383 : Blo 944585 265479383 := bstep (se 1 (by rfl) ⟨199109537, by rfl⟩ : syracuseStep 265479383 = 398219075) B398219075
theorem B1599871 : Blo 944585 1599871 := bstep (se 1 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 1599871 = 2399807) B2399807
theorem B945023 : Blo 944585 945023 := bstep (se 1 (by rfl) ⟨708767, by rfl⟩ : syracuseStep 945023 = 1417535) B1417535
theorem B3599423 : Blo 944585 3599423 := bstep (se 1 (by rfl) ⟨2699567, by rfl⟩ : syracuseStep 3599423 = 5399135) B5399135
theorem B2125871 : Blo 944585 2125871 := bstep (se 1 (by rfl) ⟨1594403, by rfl⟩ : syracuseStep 2125871 = 3188807) B3188807
theorem B946715 : Blo 944585 946715 := bstep (se 1 (by rfl) ⟨710036, by rfl⟩ : syracuseStep 946715 = 1420073) B1420073
theorem B946855 : Blo 944585 946855 := bstep (se 1 (by rfl) ⟨710141, by rfl⟩ : syracuseStep 946855 = 1420283) B1420283
theorem B1799111 : Blo 944585 1799111 := bstep (se 1 (by rfl) ⟨1349333, by rfl⟩ : syracuseStep 1799111 = 2698667) B2698667
theorem B8090603 : Blo 944585 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B947483 : Blo 944585 947483 := bstep (se 1 (by rfl) ⟨710612, by rfl⟩ : syracuseStep 947483 = 1421225) B1421225
theorem B947663 : Blo 944585 947663 := bstep (se 1 (by rfl) ⟨710747, by rfl⟩ : syracuseStep 947663 = 1421495) B1421495
theorem B766539389 : Blo 944585 766539389 := bstep (se 3 (by rfl) ⟨143726135, by rfl⟩ : syracuseStep 766539389 = 287452271) B287452271
theorem B948315 : Blo 944585 948315 := bstep (se 1 (by rfl) ⟨711236, by rfl⟩ : syracuseStep 948315 = 1422473) B1422473
theorem B4783049 : Blo 944585 4783049 := bstep (se 2 (by rfl) ⟨1793643, by rfl⟩ : syracuseStep 4783049 = 3587287) B3587287
theorem B5110951 : Blo 944585 5110951 := bstep (se 1 (by rfl) ⟨3833213, by rfl⟩ : syracuseStep 5110951 = 7666427) B7666427
theorem B13106555 : Blo 944585 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B141950515 : Blo 944585 141950515 := bstep (se 1 (by rfl) ⟨106462886, by rfl⟩ : syracuseStep 141950515 = 212925773) B212925773
theorem B839614031 : Blo 944585 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B16812011 : Blo 944585 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B69110171 : Blo 944585 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B2394623 : Blo 944585 2394623 := bstep (se 1 (by rfl) ⟨1795967, by rfl⟩ : syracuseStep 2394623 = 3591935) B3591935
theorem B2133161 : Blo 944585 2133161 := bstep (se 2 (by rfl) ⟨799935, by rfl⟩ : syracuseStep 2133161 = 1599871) B1599871
theorem B3413657 : Blo 944585 3413657 := bstep (se 2 (by rfl) ⟨1280121, by rfl⟩ : syracuseStep 3413657 = 2560243) B2560243
theorem B176986255 : Blo 944585 176986255 := bstep (se 1 (by rfl) ⟨132739691, by rfl⟩ : syracuseStep 176986255 = 265479383) B265479383
theorem B2399615 : Blo 944585 2399615 := bstep (se 1 (by rfl) ⟨1799711, by rfl⟩ : syracuseStep 2399615 = 3599423) B3599423
theorem B1417247 : Blo 944585 1417247 := bstep (se 1 (by rfl) ⟨1062935, by rfl⟩ : syracuseStep 1417247 = 2125871) B2125871
theorem B5382571 : Blo 944585 5382571 := bstep (se 1 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 5382571 = 8073857) B8073857
theorem B99558193 : Blo 944585 99558193 := bstep (se 2 (by rfl) ⟨37334322, by rfl⟩ : syracuseStep 99558193 = 74668645) B74668645
theorem B511026259 : Blo 944585 511026259 := bstep (se 1 (by rfl) ⟨383269694, by rfl⟩ : syracuseStep 511026259 = 766539389) B766539389
theorem B3188699 : Blo 944585 3188699 := bstep (se 1 (by rfl) ⟨2391524, by rfl⟩ : syracuseStep 3188699 = 4783049) B4783049
theorem B1419641 : Blo 944585 1419641 := bstep (se 2 (by rfl) ⟨532365, by rfl⟩ : syracuseStep 1419641 = 1064731) B1064731
theorem B30682415 : Blo 944585 30682415 := bstep (se 1 (by rfl) ⟨23011811, by rfl⟩ : syracuseStep 30682415 = 46023623) B46023623
theorem B20426579 : Blo 944585 20426579 := bstep (se 1 (by rfl) ⟨15319934, by rfl⟩ : syracuseStep 20426579 = 30639869) B30639869
theorem B25899911 : Blo 944585 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B3027851 : Blo 944585 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B4797629 : Blo 944585 4797629 := bstep (se 3 (by rfl) ⟨899555, by rfl⟩ : syracuseStep 4797629 = 1799111) B1799111
theorem B1422575 : Blo 944585 1422575 := bstep (se 1 (by rfl) ⟨1066931, by rfl⟩ : syracuseStep 1422575 = 2133863) B2133863
theorem B1422761 : Blo 944585 1422761 := bstep (se 2 (by rfl) ⟨533535, by rfl⟩ : syracuseStep 1422761 = 1067071) B1067071
theorem B6077537 : Blo 944585 6077537 := bstep (se 2 (by rfl) ⟨2279076, by rfl⟩ : syracuseStep 6077537 = 4558153) B4558153
theorem B1064479 : Blo 944585 1064479 := bstep (se 1 (by rfl) ⟨798359, by rfl⟩ : syracuseStep 1064479 = 1596719) B1596719
theorem B6832907 : Blo 944585 6832907 := bstep (se 1 (by rfl) ⟨5124680, by rfl⟩ : syracuseStep 6832907 = 10249361) B10249361
theorem B9847889 : Blo 944585 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B50579621 : Blo 944585 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B5393735 : Blo 944585 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B465358607 : Blo 944585 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B4313681 : Blo 944585 4313681 := bstep (se 2 (by rfl) ⟨1617630, by rfl⟩ : syracuseStep 4313681 = 3235261) B3235261
theorem B3592937 : Blo 944585 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B8737703 : Blo 944585 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B2020583 : Blo 944585 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B54679373 : Blo 944585 54679373 := bstep (se 3 (by rfl) ⟨10252382, by rfl⟩ : syracuseStep 54679373 = 20504765) B20504765
theorem B1596071 : Blo 944585 1596071 := bstep (se 1 (by rfl) ⟨1197053, by rfl⟩ : syracuseStep 1596071 = 2394107) B2394107
theorem B61463447 : Blo 944585 61463447 := bstep (se 1 (by rfl) ⟨46097585, by rfl⟩ : syracuseStep 61463447 = 92195171) B92195171
theorem B4317275 : Blo 944585 4317275 := bstep (se 1 (by rfl) ⟨3237956, by rfl⟩ : syracuseStep 4317275 = 6475913) B6475913
theorem B3596521 : Blo 944585 3596521 := bstep (se 2 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 3596521 = 2697391) B2697391
theorem B3891743 : Blo 944585 3891743 := bstep (se 1 (by rfl) ⟨2918807, by rfl⟩ : syracuseStep 3891743 = 5837615) B5837615
theorem B3597281 : Blo 944585 3597281 := bstep (se 2 (by rfl) ⟨1348980, by rfl⟩ : syracuseStep 3597281 = 2697961) B2697961
theorem B34564427 : Blo 944585 34564427 := bstep (se 1 (by rfl) ⟨25923320, by rfl⟩ : syracuseStep 34564427 = 51846641) B51846641
theorem B945471 : Blo 944585 945471 := bstep (se 1 (by rfl) ⟨709103, by rfl⟩ : syracuseStep 945471 = 1418207) B1418207
theorem B946879 : Blo 944585 946879 := bstep (se 1 (by rfl) ⟨710159, by rfl⟩ : syracuseStep 946879 = 1420319) B1420319
theorem B946927 : Blo 944585 946927 := bstep (se 1 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 946927 = 1420391) B1420391
theorem B10777535 : Blo 944585 10777535 := bstep (se 1 (by rfl) ⟨8083151, by rfl⟩ : syracuseStep 10777535 = 16166303) B16166303
theorem B2127131 : Blo 944585 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B1800569 : Blo 944585 1800569 := bstep (se 2 (by rfl) ⟨675213, by rfl⟩ : syracuseStep 1800569 = 1350427) B1350427
theorem B6814601 : Blo 944585 6814601 := bstep (se 2 (by rfl) ⟨2555475, by rfl⟩ : syracuseStep 6814601 = 5110951) B5110951
theorem B2129003 : Blo 944585 2129003 := bstep (se 1 (by rfl) ⟨1596752, by rfl⟩ : syracuseStep 2129003 = 3193505) B3193505
theorem B189267353 : Blo 944585 189267353 := bstep (se 2 (by rfl) ⟨70975257, by rfl⟩ : syracuseStep 189267353 = 141950515) B141950515
theorem B559742687 : Blo 944585 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B4555271 : Blo 944585 4555271 := bstep (se 1 (by rfl) ⟨3416453, by rfl⟩ : syracuseStep 4555271 = 6832907) B6832907
theorem B7176761 : Blo 944585 7176761 := bstep (se 2 (by rfl) ⟨2691285, by rfl⟩ : syracuseStep 7176761 = 5382571) B5382571
theorem B132744257 : Blo 944585 132744257 := bstep (se 2 (by rfl) ⟨49779096, by rfl⟩ : syracuseStep 132744257 = 99558193) B99558193
theorem B11208007 : Blo 944585 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B33719747 : Blo 944585 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B46073447 : Blo 944585 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B2395291 : Blo 944585 2395291 := bstep (se 1 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 2395291 = 3592937) B3592937
theorem B2594495 : Blo 944585 2594495 := bstep (se 1 (by rfl) ⟨1945871, by rfl⟩ : syracuseStep 2594495 = 3891743) B3891743
theorem B2398187 : Blo 944585 2398187 := bstep (se 1 (by rfl) ⟨1798640, by rfl⟩ : syracuseStep 2398187 = 3597281) B3597281
theorem B23042951 : Blo 944585 23042951 := bstep (se 1 (by rfl) ⟨17282213, by rfl⟩ : syracuseStep 23042951 = 34564427) B34564427
theorem B20454943 : Blo 944585 20454943 := bstep (se 1 (by rfl) ⟨15341207, by rfl⟩ : syracuseStep 20454943 = 30682415) B30682415
theorem B7185023 : Blo 944585 7185023 := bstep (se 1 (by rfl) ⟨5388767, by rfl⟩ : syracuseStep 7185023 = 10777535) B10777535
theorem B1418087 : Blo 944585 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1419305 : Blo 944585 1419305 := bstep (se 2 (by rfl) ⟨532239, by rfl⟩ : syracuseStep 1419305 = 1064479) B1064479
theorem B1419335 : Blo 944585 1419335 := bstep (se 1 (by rfl) ⟨1064501, by rfl⟩ : syracuseStep 1419335 = 2129003) B2129003
theorem B4795361 : Blo 944585 4795361 := bstep (se 2 (by rfl) ⟨1798260, by rfl⟩ : syracuseStep 4795361 = 3596521) B3596521
theorem B6565259 : Blo 944585 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B1422107 : Blo 944585 1422107 := bstep (se 1 (by rfl) ⟨1066580, by rfl⟩ : syracuseStep 1422107 = 2133161) B2133161
theorem B5388221 : Blo 944585 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B2275771 : Blo 944585 2275771 := bstep (se 1 (by rfl) ⟨1706828, by rfl⟩ : syracuseStep 2275771 = 3413657) B3413657
theorem B36452915 : Blo 944585 36452915 := bstep (se 1 (by rfl) ⟨27339686, by rfl⟩ : syracuseStep 36452915 = 54679373) B54679373
theorem B1064047 : Blo 944585 1064047 := bstep (se 1 (by rfl) ⟨798035, by rfl⟩ : syracuseStep 1064047 = 1596071) B1596071
theorem B40975631 : Blo 944585 40975631 := bstep (se 1 (by rfl) ⟨30731723, by rfl⟩ : syracuseStep 40975631 = 61463447) B61463447
theorem B4801517 : Blo 944585 4801517 := bstep (se 3 (by rfl) ⟨900284, by rfl⟩ : syracuseStep 4801517 = 1800569) B1800569
theorem B13617719 : Blo 944585 13617719 := bstep (se 1 (by rfl) ⟨10213289, by rfl⟩ : syracuseStep 13617719 = 20426579) B20426579
theorem B235981673 : Blo 944585 235981673 := bstep (se 2 (by rfl) ⟨88493127, by rfl⟩ : syracuseStep 235981673 = 176986255) B176986255
theorem B2018567 : Blo 944585 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B3198419 : Blo 944585 3198419 := bstep (se 1 (by rfl) ⟨2398814, by rfl⟩ : syracuseStep 3198419 = 4797629) B4797629
theorem B4543067 : Blo 944585 4543067 := bstep (se 1 (by rfl) ⟨3407300, by rfl⟩ : syracuseStep 4543067 = 6814601) B6814601
theorem B4051691 : Blo 944585 4051691 := bstep (se 1 (by rfl) ⟨3038768, by rfl⟩ : syracuseStep 4051691 = 6077537) B6077537
theorem B126178235 : Blo 944585 126178235 := bstep (se 1 (by rfl) ⟨94633676, by rfl⟩ : syracuseStep 126178235 = 189267353) B189267353
theorem B681368345 : Blo 944585 681368345 := bstep (se 2 (by rfl) ⟨255513129, by rfl⟩ : syracuseStep 681368345 = 511026259) B511026259
theorem B1596415 : Blo 944585 1596415 := bstep (se 1 (by rfl) ⟨1197311, by rfl⟩ : syracuseStep 1596415 = 2394623) B2394623
theorem B3595823 : Blo 944585 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B310239071 : Blo 944585 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B2875787 : Blo 944585 2875787 := bstep (se 1 (by rfl) ⟨2156840, by rfl⟩ : syracuseStep 2875787 = 4313681) B4313681
theorem B5825135 : Blo 944585 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B1599743 : Blo 944585 1599743 := bstep (se 1 (by rfl) ⟨1199807, by rfl⟩ : syracuseStep 1599743 = 2399615) B2399615
theorem B944831 : Blo 944585 944831 := bstep (se 1 (by rfl) ⟨708623, by rfl⟩ : syracuseStep 944831 = 1417247) B1417247
theorem B2878183 : Blo 944585 2878183 := bstep (se 1 (by rfl) ⟨2158637, by rfl⟩ : syracuseStep 2878183 = 4317275) B4317275
theorem B2125799 : Blo 944585 2125799 := bstep (se 1 (by rfl) ⟨1594349, by rfl⟩ : syracuseStep 2125799 = 3188699) B3188699
theorem B946427 : Blo 944585 946427 := bstep (se 1 (by rfl) ⟨709820, by rfl⟩ : syracuseStep 946427 = 1419641) B1419641
theorem B17266607 : Blo 944585 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B948383 : Blo 944585 948383 := bstep (se 1 (by rfl) ⟨711287, by rfl⟩ : syracuseStep 948383 = 1422575) B1422575
theorem B948507 : Blo 944585 948507 := bstep (se 1 (by rfl) ⟨711380, by rfl⟩ : syracuseStep 948507 = 1422761) B1422761
theorem B373161791 : Blo 944585 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B4784507 : Blo 944585 4784507 := bstep (se 1 (by rfl) ⟨3588380, by rfl⟩ : syracuseStep 4784507 = 7176761) B7176761
theorem B15533693 : Blo 944585 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B9078479 : Blo 944585 9078479 := bstep (se 1 (by rfl) ⟨6808859, by rfl⟩ : syracuseStep 9078479 = 13617719) B13617719
theorem B14944009 : Blo 944585 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B157321115 : Blo 944585 157321115 := bstep (se 1 (by rfl) ⟨117990836, by rfl⟩ : syracuseStep 157321115 = 235981673) B235981673
theorem B2132279 : Blo 944585 2132279 := bstep (se 1 (by rfl) ⟨1599209, by rfl⟩ : syracuseStep 2132279 = 3198419) B3198419
theorem B84118823 : Blo 944585 84118823 := bstep (se 1 (by rfl) ⟨63089117, by rfl⟩ : syracuseStep 84118823 = 126178235) B126178235
theorem B3837577 : Blo 944585 3837577 := bstep (se 2 (by rfl) ⟨1439091, by rfl⟩ : syracuseStep 3837577 = 2878183) B2878183
theorem B89919325 : Blo 944585 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B2397215 : Blo 944585 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B4790015 : Blo 944585 4790015 := bstep (se 1 (by rfl) ⟨3592511, by rfl⟩ : syracuseStep 4790015 = 7185023) B7185023
theorem B1417199 : Blo 944585 1417199 := bstep (se 1 (by rfl) ⟨1062899, by rfl⟩ : syracuseStep 1417199 = 2125799) B2125799
theorem B5382845 : Blo 944585 5382845 := bstep (se 3 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 5382845 = 2018567) B2018567
theorem B17507357 : Blo 944585 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B11511071 : Blo 944585 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B1418729 : Blo 944585 1418729 := bstep (se 2 (by rfl) ⟨532023, by rfl⟩ : syracuseStep 1418729 = 1064047) B1064047
theorem B27273257 : Blo 944585 27273257 := bstep (se 2 (by rfl) ⟨10227471, by rfl⟩ : syracuseStep 27273257 = 20454943) B20454943
theorem B30715631 : Blo 944585 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B3028711 : Blo 944585 3028711 := bstep (se 1 (by rfl) ⟨2271533, by rfl⟩ : syracuseStep 3028711 = 4543067) B4543067
theorem B2701127 : Blo 944585 2701127 := bstep (se 1 (by rfl) ⟨2025845, by rfl⟩ : syracuseStep 2701127 = 4051691) B4051691
theorem B3193721 : Blo 944585 3193721 := bstep (se 2 (by rfl) ⟨1197645, by rfl⟩ : syracuseStep 3193721 = 2395291) B2395291
theorem B454245563 : Blo 944585 454245563 := bstep (se 1 (by rfl) ⟨340684172, by rfl⟩ : syracuseStep 454245563 = 681368345) B681368345
theorem B1917191 : Blo 944585 1917191 := bstep (se 1 (by rfl) ⟨1437893, by rfl⟩ : syracuseStep 1917191 = 2875787) B2875787
theorem B1066495 : Blo 944585 1066495 := bstep (se 1 (by rfl) ⟨799871, by rfl⟩ : syracuseStep 1066495 = 1599743) B1599743
theorem B3196907 : Blo 944585 3196907 := bstep (se 1 (by rfl) ⟨2397680, by rfl⟩ : syracuseStep 3196907 = 4795361) B4795361
theorem B3034361 : Blo 944585 3034361 := bstep (se 2 (by rfl) ⟨1137885, by rfl⟩ : syracuseStep 3034361 = 2275771) B2275771
theorem B3592147 : Blo 944585 3592147 := bstep (se 1 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 3592147 = 5388221) B5388221
theorem B24301943 : Blo 944585 24301943 := bstep (se 1 (by rfl) ⟨18226457, by rfl⟩ : syracuseStep 24301943 = 36452915) B36452915
theorem B27317087 : Blo 944585 27317087 := bstep (se 1 (by rfl) ⟨20487815, by rfl⟩ : syracuseStep 27317087 = 40975631) B40975631
theorem B3036847 : Blo 944585 3036847 := bstep (se 1 (by rfl) ⟨2277635, by rfl⟩ : syracuseStep 3036847 = 4555271) B4555271
theorem B3201011 : Blo 944585 3201011 := bstep (se 1 (by rfl) ⟨2400758, by rfl⟩ : syracuseStep 3201011 = 4801517) B4801517
theorem B88496171 : Blo 944585 88496171 := bstep (se 1 (by rfl) ⟨66372128, by rfl⟩ : syracuseStep 88496171 = 132744257) B132744257
theorem B1729663 : Blo 944585 1729663 := bstep (se 1 (by rfl) ⟨1297247, by rfl⟩ : syracuseStep 1729663 = 2594495) B2594495
theorem B1598791 : Blo 944585 1598791 := bstep (se 1 (by rfl) ⟨1199093, by rfl⟩ : syracuseStep 1598791 = 2398187) B2398187
theorem B15361967 : Blo 944585 15361967 := bstep (se 1 (by rfl) ⟨11521475, by rfl⟩ : syracuseStep 15361967 = 23042951) B23042951
theorem B206826047 : Blo 944585 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B945391 : Blo 944585 945391 := bstep (se 1 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 945391 = 1418087) B1418087
theorem B946203 : Blo 944585 946203 := bstep (se 1 (by rfl) ⟨709652, by rfl⟩ : syracuseStep 946203 = 1419305) B1419305
theorem B946223 : Blo 944585 946223 := bstep (se 1 (by rfl) ⟨709667, by rfl⟩ : syracuseStep 946223 = 1419335) B1419335
theorem B948071 : Blo 944585 948071 := bstep (se 1 (by rfl) ⟨711053, by rfl⟩ : syracuseStep 948071 = 1422107) B1422107
theorem B2128553 : Blo 944585 2128553 := bstep (se 2 (by rfl) ⟨798207, by rfl⟩ : syracuseStep 2128553 = 1596415) B1596415
theorem B248774527 : Blo 944585 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B1278127 : Blo 944585 1278127 := bstep (se 1 (by rfl) ⟨958595, by rfl⟩ : syracuseStep 1278127 = 1917191) B1917191
theorem B10355795 : Blo 944585 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B2131271 : Blo 944585 2131271 := bstep (se 1 (by rfl) ⟨1598453, by rfl⟩ : syracuseStep 2131271 = 3196907) B3196907
theorem B2131721 : Blo 944585 2131721 := bstep (se 2 (by rfl) ⟨799395, by rfl⟩ : syracuseStep 2131721 = 1598791) B1598791
theorem B19925345 : Blo 944585 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B2134007 : Blo 944585 2134007 := bstep (se 1 (by rfl) ⟨1600505, by rfl⟩ : syracuseStep 2134007 = 3201011) B3201011
theorem B5116769 : Blo 944585 5116769 := bstep (se 2 (by rfl) ⟨1918788, by rfl⟩ : syracuseStep 5116769 = 3837577) B3837577
theorem B4789529 : Blo 944585 4789529 := bstep (se 2 (by rfl) ⟨1796073, by rfl⟩ : syracuseStep 4789529 = 3592147) B3592147
theorem B11671571 : Blo 944585 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B7674047 : Blo 944585 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B4038281 : Blo 944585 4038281 := bstep (se 2 (by rfl) ⟨1514355, by rfl⟩ : syracuseStep 4038281 = 3028711) B3028711
theorem B1419035 : Blo 944585 1419035 := bstep (se 1 (by rfl) ⟨1064276, by rfl⟩ : syracuseStep 1419035 = 2128553) B2128553
theorem B479569733 : Blo 944585 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B3189671 : Blo 944585 3189671 := bstep (se 1 (by rfl) ⟨2392253, by rfl⟩ : syracuseStep 3189671 = 4784507) B4784507
theorem B1421519 : Blo 944585 1421519 := bstep (se 1 (by rfl) ⟨1066139, by rfl⟩ : syracuseStep 1421519 = 2132279) B2132279
theorem B1421993 : Blo 944585 1421993 := bstep (se 2 (by rfl) ⟨533247, by rfl⟩ : syracuseStep 1421993 = 1066495) B1066495
theorem B56079215 : Blo 944585 56079215 := bstep (se 1 (by rfl) ⟨42059411, by rfl⟩ : syracuseStep 56079215 = 84118823) B84118823
theorem B16201295 : Blo 944585 16201295 := bstep (se 1 (by rfl) ⟨12150971, by rfl⟩ : syracuseStep 16201295 = 24301943) B24301943
theorem B3193343 : Blo 944585 3193343 := bstep (se 1 (by rfl) ⟨2395007, by rfl⟩ : syracuseStep 3193343 = 4790015) B4790015
theorem B58997447 : Blo 944585 58997447 := bstep (se 1 (by rfl) ⟨44248085, by rfl⟩ : syracuseStep 58997447 = 88496171) B88496171
theorem B3588563 : Blo 944585 3588563 := bstep (se 1 (by rfl) ⟨2691422, by rfl⟩ : syracuseStep 3588563 = 5382845) B5382845
theorem B9224869 : Blo 944585 9224869 := bstep (se 4 (by rfl) ⟨864831, by rfl⟩ : syracuseStep 9224869 = 1729663) B1729663
theorem B10241311 : Blo 944585 10241311 := bstep (se 1 (by rfl) ⟨7680983, by rfl⟩ : syracuseStep 10241311 = 15361967) B15361967
theorem B4049129 : Blo 944585 4049129 := bstep (se 2 (by rfl) ⟨1518423, by rfl⟩ : syracuseStep 4049129 = 3036847) B3036847
theorem B302830375 : Blo 944585 302830375 := bstep (se 1 (by rfl) ⟨227122781, by rfl⟩ : syracuseStep 302830375 = 454245563) B454245563
theorem B331699369 : Blo 944585 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B6052319 : Blo 944585 6052319 := bstep (se 1 (by rfl) ⟨4539239, by rfl⟩ : syracuseStep 6052319 = 9078479) B9078479
theorem B104880743 : Blo 944585 104880743 := bstep (se 1 (by rfl) ⟨78660557, by rfl⟩ : syracuseStep 104880743 = 157321115) B157321115
theorem B2022907 : Blo 944585 2022907 := bstep (se 1 (by rfl) ⟨1517180, by rfl⟩ : syracuseStep 2022907 = 3034361) B3034361
theorem B18211391 : Blo 944585 18211391 := bstep (se 1 (by rfl) ⟨13658543, by rfl⟩ : syracuseStep 18211391 = 27317087) B27317087
theorem B1598143 : Blo 944585 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B7203005 : Blo 944585 7203005 := bstep (se 3 (by rfl) ⟨1350563, by rfl⟩ : syracuseStep 7203005 = 2701127) B2701127
theorem B944799 : Blo 944585 944799 := bstep (se 1 (by rfl) ⟨708599, by rfl⟩ : syracuseStep 944799 = 1417199) B1417199
theorem B945819 : Blo 944585 945819 := bstep (se 1 (by rfl) ⟨709364, by rfl⟩ : syracuseStep 945819 = 1418729) B1418729
theorem B18182171 : Blo 944585 18182171 := bstep (se 1 (by rfl) ⟨13636628, by rfl⟩ : syracuseStep 18182171 = 27273257) B27273257
theorem B137884031 : Blo 944585 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B20477087 : Blo 944585 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B2129147 : Blo 944585 2129147 := bstep (se 1 (by rfl) ⟨1596860, by rfl⟩ : syracuseStep 2129147 = 3193721) B3193721
theorem B1704169 : Blo 944585 1704169 := bstep (se 2 (by rfl) ⟨639063, by rfl⟩ : syracuseStep 1704169 = 1278127) B1278127
theorem B2392375 : Blo 944585 2392375 := bstep (se 1 (by rfl) ⟨1794281, by rfl⟩ : syracuseStep 2392375 = 3588563) B3588563
theorem B2130857 : Blo 944585 2130857 := bstep (se 2 (by rfl) ⟨799071, by rfl⟩ : syracuseStep 2130857 = 1598143) B1598143
theorem B3411179 : Blo 944585 3411179 := bstep (se 1 (by rfl) ⟨2558384, by rfl⟩ : syracuseStep 3411179 = 5116769) B5116769
theorem B5116031 : Blo 944585 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B4034879 : Blo 944585 4034879 := bstep (se 1 (by rfl) ⟨3026159, by rfl⟩ : syracuseStep 4034879 = 6052319) B6052319
theorem B2692187 : Blo 944585 2692187 := bstep (se 1 (by rfl) ⟨2019140, by rfl⟩ : syracuseStep 2692187 = 4038281) B4038281
theorem B403773833 : Blo 944585 403773833 := bstep (se 2 (by rfl) ⟨151415187, by rfl⟩ : syracuseStep 403773833 = 302830375) B302830375
theorem B91922687 : Blo 944585 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B39331631 : Blo 944585 39331631 := bstep (se 1 (by rfl) ⟨29498723, by rfl⟩ : syracuseStep 39331631 = 58997447) B58997447
theorem B2697209 : Blo 944585 2697209 := bstep (se 2 (by rfl) ⟨1011453, by rfl⟩ : syracuseStep 2697209 = 2022907) B2022907
theorem B1419431 : Blo 944585 1419431 := bstep (se 1 (by rfl) ⟨1064573, by rfl⟩ : syracuseStep 1419431 = 2129147) B2129147
theorem B1420847 : Blo 944585 1420847 := bstep (se 1 (by rfl) ⟨1065635, by rfl⟩ : syracuseStep 1420847 = 2131271) B2131271
theorem B12299825 : Blo 944585 12299825 := bstep (se 2 (by rfl) ⟨4612434, by rfl⟩ : syracuseStep 12299825 = 9224869) B9224869
theorem B1421147 : Blo 944585 1421147 := bstep (se 1 (by rfl) ⟨1065860, by rfl⟩ : syracuseStep 1421147 = 2131721) B2131721
theorem B2699419 : Blo 944585 2699419 := bstep (se 1 (by rfl) ⟨2024564, by rfl⟩ : syracuseStep 2699419 = 4049129) B4049129
theorem B13283563 : Blo 944585 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B1422671 : Blo 944585 1422671 := bstep (se 1 (by rfl) ⟨1067003, by rfl⟩ : syracuseStep 1422671 = 2134007) B2134007
theorem B3193019 : Blo 944585 3193019 := bstep (se 1 (by rfl) ⟨2394764, by rfl⟩ : syracuseStep 3193019 = 4789529) B4789529
theorem B12140927 : Blo 944585 12140927 := bstep (se 1 (by rfl) ⟨9105695, by rfl⟩ : syracuseStep 12140927 = 18211391) B18211391
theorem B4802003 : Blo 944585 4802003 := bstep (se 1 (by rfl) ⟨3601502, by rfl⟩ : syracuseStep 4802003 = 7203005) B7203005
theorem B13651391 : Blo 944585 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B10800863 : Blo 944585 10800863 := bstep (se 1 (by rfl) ⟨8100647, by rfl⟩ : syracuseStep 10800863 = 16201295) B16201295
theorem B6903863 : Blo 944585 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B13655081 : Blo 944585 13655081 := bstep (se 2 (by rfl) ⟨5120655, by rfl⟩ : syracuseStep 13655081 = 10241311) B10241311
theorem B69920495 : Blo 944585 69920495 := bstep (se 1 (by rfl) ⟨52440371, by rfl⟩ : syracuseStep 69920495 = 104880743) B104880743
theorem B31124189 : Blo 944585 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B946023 : Blo 944585 946023 := bstep (se 1 (by rfl) ⟨709517, by rfl⟩ : syracuseStep 946023 = 1419035) B1419035
theorem B319713155 : Blo 944585 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B442265825 : Blo 944585 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B2126447 : Blo 944585 2126447 := bstep (se 1 (by rfl) ⟨1594835, by rfl⟩ : syracuseStep 2126447 = 3189671) B3189671
theorem B12121447 : Blo 944585 12121447 := bstep (se 1 (by rfl) ⟨9091085, by rfl⟩ : syracuseStep 12121447 = 18182171) B18182171
theorem B947679 : Blo 944585 947679 := bstep (se 1 (by rfl) ⟨710759, by rfl⟩ : syracuseStep 947679 = 1421519) B1421519
theorem B947995 : Blo 944585 947995 := bstep (se 1 (by rfl) ⟨710996, by rfl⟩ : syracuseStep 947995 = 1421993) B1421993
theorem B37386143 : Blo 944585 37386143 := bstep (se 1 (by rfl) ⟨28039607, by rfl⟩ : syracuseStep 37386143 = 56079215) B56079215
theorem B2128895 : Blo 944585 2128895 := bstep (se 1 (by rfl) ⟨1596671, by rfl⟩ : syracuseStep 2128895 = 3193343) B3193343
theorem B8093951 : Blo 944585 8093951 := bstep (se 1 (by rfl) ⟨6070463, by rfl⟩ : syracuseStep 8093951 = 12140927) B12140927
theorem B3410687 : Blo 944585 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B2689919 : Blo 944585 2689919 := bstep (se 1 (by rfl) ⟨2017439, by rfl⟩ : syracuseStep 2689919 = 4034879) B4034879
theorem B61281791 : Blo 944585 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B1076730221 : Blo 944585 1076730221 := bstep (se 3 (by rfl) ⟨201886916, by rfl⟩ : syracuseStep 1076730221 = 403773833) B403773833
theorem B26221087 : Blo 944585 26221087 := bstep (se 1 (by rfl) ⟨19665815, by rfl⟩ : syracuseStep 26221087 = 39331631) B39331631
theorem B16161929 : Blo 944585 16161929 := bstep (se 2 (by rfl) ⟨6060723, by rfl⟩ : syracuseStep 16161929 = 12121447) B12121447
theorem B20749459 : Blo 944585 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B8199883 : Blo 944585 8199883 := bstep (se 1 (by rfl) ⟨6149912, by rfl⟩ : syracuseStep 8199883 = 12299825) B12299825
theorem B36413549 : Blo 944585 36413549 := bstep (se 3 (by rfl) ⟨6827540, by rfl⟩ : syracuseStep 36413549 = 13655081) B13655081
theorem B1417631 : Blo 944585 1417631 := bstep (se 1 (by rfl) ⟨1063223, by rfl⟩ : syracuseStep 1417631 = 2126447) B2126447
theorem B1419263 : Blo 944585 1419263 := bstep (se 1 (by rfl) ⟨1064447, by rfl⟩ : syracuseStep 1419263 = 2128895) B2128895
theorem B2272225 : Blo 944585 2272225 := bstep (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) B1704169
theorem B3189833 : Blo 944585 3189833 := bstep (se 2 (by rfl) ⟨1196187, by rfl⟩ : syracuseStep 3189833 = 2392375) B2392375
theorem B1420571 : Blo 944585 1420571 := bstep (se 1 (by rfl) ⟨1065428, by rfl⟩ : syracuseStep 1420571 = 2130857) B2130857
theorem B2274119 : Blo 944585 2274119 := bstep (se 1 (by rfl) ⟨1705589, by rfl⟩ : syracuseStep 2274119 = 3411179) B3411179
theorem B4602575 : Blo 944585 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B17711417 : Blo 944585 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B46613663 : Blo 944585 46613663 := bstep (se 1 (by rfl) ⟨34960247, by rfl⟩ : syracuseStep 46613663 = 69920495) B69920495
theorem B213142103 : Blo 944585 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B24924095 : Blo 944585 24924095 := bstep (se 1 (by rfl) ⟨18693071, by rfl⟩ : syracuseStep 24924095 = 37386143) B37386143
theorem B3201335 : Blo 944585 3201335 := bstep (se 1 (by rfl) ⟨2401001, by rfl⟩ : syracuseStep 3201335 = 4802003) B4802003
theorem B9100927 : Blo 944585 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B7200575 : Blo 944585 7200575 := bstep (se 1 (by rfl) ⟨5400431, by rfl⟩ : syracuseStep 7200575 = 10800863) B10800863
theorem B1794791 : Blo 944585 1794791 := bstep (se 1 (by rfl) ⟨1346093, by rfl⟩ : syracuseStep 1794791 = 2692187) B2692187
theorem B3599225 : Blo 944585 3599225 := bstep (se 2 (by rfl) ⟨1349709, by rfl⟩ : syracuseStep 3599225 = 2699419) B2699419
theorem B1798139 : Blo 944585 1798139 := bstep (se 1 (by rfl) ⟨1348604, by rfl⟩ : syracuseStep 1798139 = 2697209) B2697209
theorem B946287 : Blo 944585 946287 := bstep (se 1 (by rfl) ⟨709715, by rfl⟩ : syracuseStep 946287 = 1419431) B1419431
theorem B947231 : Blo 944585 947231 := bstep (se 1 (by rfl) ⟨710423, by rfl⟩ : syracuseStep 947231 = 1420847) B1420847
theorem B947431 : Blo 944585 947431 := bstep (se 1 (by rfl) ⟨710573, by rfl⟩ : syracuseStep 947431 = 1421147) B1421147
theorem B294843883 : Blo 944585 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B948447 : Blo 944585 948447 := bstep (se 1 (by rfl) ⟨711335, by rfl⟩ : syracuseStep 948447 = 1422671) B1422671
theorem B2128679 : Blo 944585 2128679 := bstep (se 1 (by rfl) ⟨1596509, by rfl⟩ : syracuseStep 2128679 = 3193019) B3193019
theorem B16616063 : Blo 944585 16616063 := bstep (se 1 (by rfl) ⟨12462047, by rfl⟩ : syracuseStep 16616063 = 24924095) B24924095
theorem B2134223 : Blo 944585 2134223 := bstep (se 1 (by rfl) ⟨1600667, by rfl⟩ : syracuseStep 2134223 = 3201335) B3201335
theorem B717820147 : Blo 944585 717820147 := bstep (se 1 (by rfl) ⟨538365110, by rfl⟩ : syracuseStep 717820147 = 1076730221) B1076730221
theorem B2399483 : Blo 944585 2399483 := bstep (se 1 (by rfl) ⟨1799612, by rfl⟩ : syracuseStep 2399483 = 3599225) B3599225
theorem B393125177 : Blo 944585 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B1516079 : Blo 944585 1516079 := bstep (se 1 (by rfl) ⟨1137059, by rfl⟩ : syracuseStep 1516079 = 2274119) B2274119
theorem B27665945 : Blo 944585 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B1419119 : Blo 944585 1419119 := bstep (se 1 (by rfl) ⟨1064339, by rfl⟩ : syracuseStep 1419119 = 2128679) B2128679
theorem B12134569 : Blo 944585 12134569 := bstep (se 2 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 12134569 = 9100927) B9100927
theorem B4795037 : Blo 944585 4795037 := bstep (se 3 (by rfl) ⟨899069, by rfl⟩ : syracuseStep 4795037 = 1798139) B1798139
theorem B31075775 : Blo 944585 31075775 := bstep (se 1 (by rfl) ⟨23306831, by rfl⟩ : syracuseStep 31075775 = 46613663) B46613663
theorem B47230445 : Blo 944585 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B142094735 : Blo 944585 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B3029633 : Blo 944585 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B4800383 : Blo 944585 4800383 := bstep (se 1 (by rfl) ⟨3600287, by rfl⟩ : syracuseStep 4800383 = 7200575) B7200575
theorem B1196527 : Blo 944585 1196527 := bstep (se 1 (by rfl) ⟨897395, by rfl⟩ : syracuseStep 1196527 = 1794791) B1794791
theorem B9095165 : Blo 944585 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B43732709 : Blo 944585 43732709 := bstep (se 4 (by rfl) ⟨4099941, by rfl⟩ : syracuseStep 43732709 = 8199883) B8199883
theorem B3068383 : Blo 944585 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B5395967 : Blo 944585 5395967 := bstep (se 1 (by rfl) ⟨4046975, by rfl⟩ : syracuseStep 5395967 = 8093951) B8093951
theorem B1793279 : Blo 944585 1793279 := bstep (se 1 (by rfl) ⟨1344959, by rfl⟩ : syracuseStep 1793279 = 2689919) B2689919
theorem B40854527 : Blo 944585 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B10774619 : Blo 944585 10774619 := bstep (se 1 (by rfl) ⟨8080964, by rfl⟩ : syracuseStep 10774619 = 16161929) B16161929
theorem B24275699 : Blo 944585 24275699 := bstep (se 1 (by rfl) ⟨18206774, by rfl⟩ : syracuseStep 24275699 = 36413549) B36413549
theorem B945087 : Blo 944585 945087 := bstep (se 1 (by rfl) ⟨708815, by rfl⟩ : syracuseStep 945087 = 1417631) B1417631
theorem B946175 : Blo 944585 946175 := bstep (se 1 (by rfl) ⟨709631, by rfl⟩ : syracuseStep 946175 = 1419263) B1419263
theorem B2126555 : Blo 944585 2126555 := bstep (se 1 (by rfl) ⟨1594916, by rfl⟩ : syracuseStep 2126555 = 3189833) B3189833
theorem B947047 : Blo 944585 947047 := bstep (se 1 (by rfl) ⟨710285, by rfl⟩ : syracuseStep 947047 = 1420571) B1420571
theorem B34961449 : Blo 944585 34961449 := bstep (se 2 (by rfl) ⟨13110543, by rfl⟩ : syracuseStep 34961449 = 26221087) B26221087
theorem B6063443 : Blo 944585 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B262083451 : Blo 944585 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B957093529 : Blo 944585 957093529 := bstep (se 2 (by rfl) ⟨358910073, by rfl⟩ : syracuseStep 957093529 = 717820147) B717820147
theorem B27236351 : Blo 944585 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B7183079 : Blo 944585 7183079 := bstep (se 1 (by rfl) ⟨5387309, by rfl⟩ : syracuseStep 7183079 = 10774619) B10774619
theorem B44309501 : Blo 944585 44309501 := bstep (se 3 (by rfl) ⟨8308031, by rfl⟩ : syracuseStep 44309501 = 16616063) B16616063
theorem B20717183 : Blo 944585 20717183 := bstep (se 1 (by rfl) ⟨15537887, by rfl⟩ : syracuseStep 20717183 = 31075775) B31075775
theorem B1417703 : Blo 944585 1417703 := bstep (se 1 (by rfl) ⟨1063277, by rfl⟩ : syracuseStep 1417703 = 2126555) B2126555
theorem B1422815 : Blo 944585 1422815 := bstep (se 1 (by rfl) ⟨1067111, by rfl⟩ : syracuseStep 1422815 = 2134223) B2134223
theorem B3196691 : Blo 944585 3196691 := bstep (se 1 (by rfl) ⟨2397518, by rfl⟩ : syracuseStep 3196691 = 4795037) B4795037
theorem B46615265 : Blo 944585 46615265 := bstep (se 2 (by rfl) ⟨17480724, by rfl⟩ : syracuseStep 46615265 = 34961449) B34961449
theorem B2019755 : Blo 944585 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B3200255 : Blo 944585 3200255 := bstep (se 1 (by rfl) ⟨2400191, by rfl⟩ : syracuseStep 3200255 = 4800383) B4800383
theorem B1595369 : Blo 944585 1595369 := bstep (se 2 (by rfl) ⟨598263, by rfl⟩ : syracuseStep 1595369 = 1196527) B1196527
theorem B29155139 : Blo 944585 29155139 := bstep (se 1 (by rfl) ⟨21866354, by rfl⟩ : syracuseStep 29155139 = 43732709) B43732709
theorem B16179425 : Blo 944585 16179425 := bstep (se 2 (by rfl) ⟨6067284, by rfl⟩ : syracuseStep 16179425 = 12134569) B12134569
theorem B3597311 : Blo 944585 3597311 := bstep (se 1 (by rfl) ⟨2697983, by rfl⟩ : syracuseStep 3597311 = 5395967) B5395967
theorem B1599655 : Blo 944585 1599655 := bstep (se 1 (by rfl) ⟨1199741, by rfl⟩ : syracuseStep 1599655 = 2399483) B2399483
theorem B1010719 : Blo 944585 1010719 := bstep (se 1 (by rfl) ⟨758039, by rfl⟩ : syracuseStep 1010719 = 1516079) B1516079
theorem B4091177 : Blo 944585 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B18443963 : Blo 944585 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B946079 : Blo 944585 946079 := bstep (se 1 (by rfl) ⟨709559, by rfl⟩ : syracuseStep 946079 = 1419119) B1419119
theorem B16183799 : Blo 944585 16183799 := bstep (se 1 (by rfl) ⟨12137849, by rfl⟩ : syracuseStep 16183799 = 24275699) B24275699
theorem B31486963 : Blo 944585 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B94729823 : Blo 944585 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B4782077 : Blo 944585 4782077 := bstep (se 3 (by rfl) ⟨896639, by rfl⟩ : syracuseStep 4782077 = 1793279) B1793279
theorem B2131127 : Blo 944585 2131127 := bstep (se 1 (by rfl) ⟨1598345, by rfl⟩ : syracuseStep 2131127 = 3196691) B3196691
theorem B2132873 : Blo 944585 2132873 := bstep (se 2 (by rfl) ⟨799827, by rfl⟩ : syracuseStep 2132873 = 1599655) B1599655
theorem B2133503 : Blo 944585 2133503 := bstep (se 1 (by rfl) ⟨1600127, by rfl⟩ : syracuseStep 2133503 = 3200255) B3200255
theorem B18157567 : Blo 944585 18157567 := bstep (se 1 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 18157567 = 27236351) B27236351
theorem B1347625 : Blo 944585 1347625 := bstep (se 2 (by rfl) ⟨505359, by rfl⟩ : syracuseStep 1347625 = 1010719) B1010719
theorem B4788719 : Blo 944585 4788719 := bstep (se 1 (by rfl) ⟨3591539, by rfl⟩ : syracuseStep 4788719 = 7183079) B7183079
theorem B19436759 : Blo 944585 19436759 := bstep (se 1 (by rfl) ⟨14577569, by rfl⟩ : syracuseStep 19436759 = 29155139) B29155139
theorem B10786283 : Blo 944585 10786283 := bstep (se 1 (by rfl) ⟨8089712, by rfl⟩ : syracuseStep 10786283 = 16179425) B16179425
theorem B2398207 : Blo 944585 2398207 := bstep (se 1 (by rfl) ⟨1798655, by rfl⟩ : syracuseStep 2398207 = 3597311) B3597311
theorem B349444601 : Blo 944585 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B41982617 : Blo 944585 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B2727451 : Blo 944585 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B1276124705 : Blo 944585 1276124705 := bstep (se 2 (by rfl) ⟨478546764, by rfl⟩ : syracuseStep 1276124705 = 957093529) B957093529
theorem B12295975 : Blo 944585 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B10789199 : Blo 944585 10789199 := bstep (se 1 (by rfl) ⟨8091899, by rfl⟩ : syracuseStep 10789199 = 16183799) B16183799
theorem B63153215 : Blo 944585 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B3188051 : Blo 944585 3188051 := bstep (se 1 (by rfl) ⟨2391038, by rfl⟩ : syracuseStep 3188051 = 4782077) B4782077
theorem B4042295 : Blo 944585 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B5386013 : Blo 944585 5386013 := bstep (se 3 (by rfl) ⟨1009877, by rfl⟩ : syracuseStep 5386013 = 2019755) B2019755
theorem B31076843 : Blo 944585 31076843 := bstep (se 1 (by rfl) ⟨23307632, by rfl⟩ : syracuseStep 31076843 = 46615265) B46615265
theorem B1063579 : Blo 944585 1063579 := bstep (se 1 (by rfl) ⟨797684, by rfl⟩ : syracuseStep 1063579 = 1595369) B1595369
theorem B29539667 : Blo 944585 29539667 := bstep (se 1 (by rfl) ⟨22154750, by rfl⟩ : syracuseStep 29539667 = 44309501) B44309501
theorem B13811455 : Blo 944585 13811455 := bstep (se 1 (by rfl) ⟨10358591, by rfl⟩ : syracuseStep 13811455 = 20717183) B20717183
theorem B945135 : Blo 944585 945135 := bstep (se 1 (by rfl) ⟨708851, by rfl⟩ : syracuseStep 945135 = 1417703) B1417703
theorem B948543 : Blo 944585 948543 := bstep (se 1 (by rfl) ⟨711407, by rfl⟩ : syracuseStep 948543 = 1422815) B1422815
theorem B82871581 : Blo 944585 82871581 := bstep (se 3 (by rfl) ⟨15538421, by rfl⟩ : syracuseStep 82871581 = 31076843) B31076843
theorem B27988411 : Blo 944585 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B2694863 : Blo 944585 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B1418105 : Blo 944585 1418105 := bstep (se 2 (by rfl) ⟨531789, by rfl⟩ : syracuseStep 1418105 = 1063579) B1063579
theorem B16394633 : Blo 944585 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B1420751 : Blo 944585 1420751 := bstep (se 1 (by rfl) ⟨1065563, by rfl⟩ : syracuseStep 1420751 = 2131127) B2131127
theorem B1421915 : Blo 944585 1421915 := bstep (se 1 (by rfl) ⟨1066436, by rfl⟩ : syracuseStep 1421915 = 2132873) B2132873
theorem B1422335 : Blo 944585 1422335 := bstep (se 1 (by rfl) ⟨1066751, by rfl⟩ : syracuseStep 1422335 = 2133503) B2133503
theorem B3192479 : Blo 944585 3192479 := bstep (se 1 (by rfl) ⟨2394359, by rfl⟩ : syracuseStep 3192479 = 4788719) B4788719
theorem B12957839 : Blo 944585 12957839 := bstep (se 1 (by rfl) ⟨9718379, by rfl⟩ : syracuseStep 12957839 = 19436759) B19436759
theorem B7190855 : Blo 944585 7190855 := bstep (se 1 (by rfl) ⟨5393141, by rfl⟩ : syracuseStep 7190855 = 10786283) B10786283
theorem B232963067 : Blo 944585 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B7192799 : Blo 944585 7192799 := bstep (se 1 (by rfl) ⟨5394599, by rfl⟩ : syracuseStep 7192799 = 10789199) B10789199
theorem B3590675 : Blo 944585 3590675 := bstep (se 1 (by rfl) ⟨2693006, by rfl⟩ : syracuseStep 3590675 = 5386013) B5386013
theorem B3197609 : Blo 944585 3197609 := bstep (se 2 (by rfl) ⟨1199103, by rfl⟩ : syracuseStep 3197609 = 2398207) B2398207
theorem B850749803 : Blo 944585 850749803 := bstep (se 1 (by rfl) ⟨638062352, by rfl⟩ : syracuseStep 850749803 = 1276124705) B1276124705
theorem B24210089 : Blo 944585 24210089 := bstep (se 2 (by rfl) ⟨9078783, by rfl⟩ : syracuseStep 24210089 = 18157567) B18157567
theorem B1796833 : Blo 944585 1796833 := bstep (se 2 (by rfl) ⟨673812, by rfl⟩ : syracuseStep 1796833 = 1347625) B1347625
theorem B42102143 : Blo 944585 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B2125367 : Blo 944585 2125367 := bstep (se 1 (by rfl) ⟨1594025, by rfl⟩ : syracuseStep 2125367 = 3188051) B3188051
theorem B14546405 : Blo 944585 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B78772445 : Blo 944585 78772445 := bstep (se 3 (by rfl) ⟨14769833, by rfl⟩ : syracuseStep 78772445 = 29539667) B29539667
theorem B18415273 : Blo 944585 18415273 := bstep (se 2 (by rfl) ⟨6905727, by rfl⟩ : syracuseStep 18415273 = 13811455) B13811455
theorem B2393783 : Blo 944585 2393783 := bstep (se 1 (by rfl) ⟨1795337, by rfl⟩ : syracuseStep 2393783 = 3590675) B3590675
theorem B110495441 : Blo 944585 110495441 := bstep (se 2 (by rfl) ⟨41435790, by rfl⟩ : syracuseStep 110495441 = 82871581) B82871581
theorem B2131739 : Blo 944585 2131739 := bstep (se 1 (by rfl) ⟨1598804, by rfl⟩ : syracuseStep 2131739 = 3197609) B3197609
theorem B2395777 : Blo 944585 2395777 := bstep (se 2 (by rfl) ⟨898416, by rfl⟩ : syracuseStep 2395777 = 1796833) B1796833
theorem B1416911 : Blo 944585 1416911 := bstep (se 1 (by rfl) ⟨1062683, by rfl⟩ : syracuseStep 1416911 = 2125367) B2125367
theorem B4793903 : Blo 944585 4793903 := bstep (se 1 (by rfl) ⟨3595427, by rfl⟩ : syracuseStep 4793903 = 7190855) B7190855
theorem B24553697 : Blo 944585 24553697 := bstep (se 2 (by rfl) ⟨9207636, by rfl⟩ : syracuseStep 24553697 = 18415273) B18415273
theorem B4795199 : Blo 944585 4795199 := bstep (se 1 (by rfl) ⟨3596399, by rfl⟩ : syracuseStep 4795199 = 7192799) B7192799
theorem B567166535 : Blo 944585 567166535 := bstep (se 1 (by rfl) ⟨425374901, by rfl⟩ : syracuseStep 567166535 = 850749803) B850749803
theorem B10929755 : Blo 944585 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B16140059 : Blo 944585 16140059 := bstep (se 1 (by rfl) ⟨12105044, by rfl⟩ : syracuseStep 16140059 = 24210089) B24210089
theorem B28068095 : Blo 944585 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B8638559 : Blo 944585 8638559 := bstep (se 1 (by rfl) ⟨6478919, by rfl⟩ : syracuseStep 8638559 = 12957839) B12957839
theorem B52514963 : Blo 944585 52514963 := bstep (se 1 (by rfl) ⟨39386222, by rfl⟩ : syracuseStep 52514963 = 78772445) B78772445
theorem B155308711 : Blo 944585 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B1796575 : Blo 944585 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B37317881 : Blo 944585 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B945403 : Blo 944585 945403 := bstep (se 1 (by rfl) ⟨709052, by rfl⟩ : syracuseStep 945403 = 1418105) B1418105
theorem B947167 : Blo 944585 947167 := bstep (se 1 (by rfl) ⟨710375, by rfl⟩ : syracuseStep 947167 = 1420751) B1420751
theorem B947943 : Blo 944585 947943 := bstep (se 1 (by rfl) ⟨710957, by rfl⟩ : syracuseStep 947943 = 1421915) B1421915
theorem B948223 : Blo 944585 948223 := bstep (se 1 (by rfl) ⟨711167, by rfl⟩ : syracuseStep 948223 = 1422335) B1422335
theorem B9697603 : Blo 944585 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B2128319 : Blo 944585 2128319 := bstep (se 1 (by rfl) ⟨1596239, by rfl⟩ : syracuseStep 2128319 = 3192479) B3192479
theorem B378111023 : Blo 944585 378111023 := bstep (se 1 (by rfl) ⟨283583267, by rfl⟩ : syracuseStep 378111023 = 567166535) B567166535
theorem B73663627 : Blo 944585 73663627 := bstep (se 1 (by rfl) ⟨55247720, by rfl⟩ : syracuseStep 73663627 = 110495441) B110495441
theorem B18712063 : Blo 944585 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B2395433 : Blo 944585 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B65476525 : Blo 944585 65476525 := bstep (se 3 (by rfl) ⟨12276848, by rfl⟩ : syracuseStep 65476525 = 24553697) B24553697
theorem B24878587 : Blo 944585 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B1418879 : Blo 944585 1418879 := bstep (se 1 (by rfl) ⟨1064159, by rfl⟩ : syracuseStep 1418879 = 2128319) B2128319
theorem B10760039 : Blo 944585 10760039 := bstep (se 1 (by rfl) ⟨8070029, by rfl⟩ : syracuseStep 10760039 = 16140059) B16140059
theorem B1421159 : Blo 944585 1421159 := bstep (se 1 (by rfl) ⟨1065869, by rfl⟩ : syracuseStep 1421159 = 2131739) B2131739
theorem B35009975 : Blo 944585 35009975 := bstep (se 1 (by rfl) ⟨26257481, by rfl⟩ : syracuseStep 35009975 = 52514963) B52514963
theorem B29146013 : Blo 944585 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B3194369 : Blo 944585 3194369 := bstep (se 2 (by rfl) ⟨1197888, by rfl⟩ : syracuseStep 3194369 = 2395777) B2395777
theorem B207078281 : Blo 944585 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B3195935 : Blo 944585 3195935 := bstep (se 1 (by rfl) ⟨2396951, by rfl⟩ : syracuseStep 3195935 = 4793903) B4793903
theorem B3196799 : Blo 944585 3196799 := bstep (se 1 (by rfl) ⟨2397599, by rfl⟩ : syracuseStep 3196799 = 4795199) B4795199
theorem B12930137 : Blo 944585 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B1595855 : Blo 944585 1595855 := bstep (se 1 (by rfl) ⟨1196891, by rfl⟩ : syracuseStep 1595855 = 2393783) B2393783
theorem B5759039 : Blo 944585 5759039 := bstep (se 1 (by rfl) ⟨4319279, by rfl⟩ : syracuseStep 5759039 = 8638559) B8638559
theorem B944607 : Blo 944585 944607 := bstep (se 1 (by rfl) ⟨708455, by rfl⟩ : syracuseStep 944607 = 1416911) B1416911
theorem B138052187 : Blo 944585 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B2130623 : Blo 944585 2130623 := bstep (se 1 (by rfl) ⟨1597967, by rfl⟩ : syracuseStep 2130623 = 3195935) B3195935
theorem B2131199 : Blo 944585 2131199 := bstep (se 1 (by rfl) ⟨1598399, by rfl⟩ : syracuseStep 2131199 = 3196799) B3196799
theorem B8620091 : Blo 944585 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B3839359 : Blo 944585 3839359 := bstep (se 1 (by rfl) ⟨2879519, by rfl⟩ : syracuseStep 3839359 = 5759039) B5759039
theorem B87302033 : Blo 944585 87302033 := bstep (se 2 (by rfl) ⟨32738262, by rfl⟩ : syracuseStep 87302033 = 65476525) B65476525
theorem B23339983 : Blo 944585 23339983 := bstep (se 1 (by rfl) ⟨17504987, by rfl⟩ : syracuseStep 23339983 = 35009975) B35009975
theorem B33171449 : Blo 944585 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B98218169 : Blo 944585 98218169 := bstep (se 2 (by rfl) ⟨36831813, by rfl⟩ : syracuseStep 98218169 = 73663627) B73663627
theorem B24949417 : Blo 944585 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B1063903 : Blo 944585 1063903 := bstep (se 1 (by rfl) ⟨797927, by rfl⟩ : syracuseStep 1063903 = 1595855) B1595855
theorem B252074015 : Blo 944585 252074015 := bstep (se 1 (by rfl) ⟨189055511, by rfl⟩ : syracuseStep 252074015 = 378111023) B378111023
theorem B1596955 : Blo 944585 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B945919 : Blo 944585 945919 := bstep (se 1 (by rfl) ⟨709439, by rfl⟩ : syracuseStep 945919 = 1418879) B1418879
theorem B7173359 : Blo 944585 7173359 := bstep (se 1 (by rfl) ⟨5380019, by rfl⟩ : syracuseStep 7173359 = 10760039) B10760039
theorem B947439 : Blo 944585 947439 := bstep (se 1 (by rfl) ⟨710579, by rfl⟩ : syracuseStep 947439 = 1421159) B1421159
theorem B19430675 : Blo 944585 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B2129579 : Blo 944585 2129579 := bstep (se 1 (by rfl) ⟨1597184, by rfl⟩ : syracuseStep 2129579 = 3194369) B3194369
theorem B58201355 : Blo 944585 58201355 := bstep (se 1 (by rfl) ⟨43651016, by rfl⟩ : syracuseStep 58201355 = 87302033) B87302033
theorem B33265889 : Blo 944585 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B5119145 : Blo 944585 5119145 := bstep (se 2 (by rfl) ⟨1919679, by rfl⟩ : syracuseStep 5119145 = 3839359) B3839359
theorem B65478779 : Blo 944585 65478779 := bstep (se 1 (by rfl) ⟨49109084, by rfl⟩ : syracuseStep 65478779 = 98218169) B98218169
theorem B1418537 : Blo 944585 1418537 := bstep (se 2 (by rfl) ⟨531951, by rfl⟩ : syracuseStep 1418537 = 1063903) B1063903
theorem B12953783 : Blo 944585 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B1419719 : Blo 944585 1419719 := bstep (se 1 (by rfl) ⟨1064789, by rfl⟩ : syracuseStep 1419719 = 2129579) B2129579
theorem B1420415 : Blo 944585 1420415 := bstep (se 1 (by rfl) ⟨1065311, by rfl⟩ : syracuseStep 1420415 = 2130623) B2130623
theorem B1420799 : Blo 944585 1420799 := bstep (se 1 (by rfl) ⟨1065599, by rfl⟩ : syracuseStep 1420799 = 2131199) B2131199
theorem B5746727 : Blo 944585 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B168049343 : Blo 944585 168049343 := bstep (se 1 (by rfl) ⟨126037007, by rfl⟩ : syracuseStep 168049343 = 252074015) B252074015
theorem B88457197 : Blo 944585 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B92034791 : Blo 944585 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B31119977 : Blo 944585 31119977 := bstep (se 2 (by rfl) ⟨11669991, by rfl⟩ : syracuseStep 31119977 = 23339983) B23339983
theorem B4782239 : Blo 944585 4782239 := bstep (se 1 (by rfl) ⟨3586679, by rfl⟩ : syracuseStep 4782239 = 7173359) B7173359
theorem B2129273 : Blo 944585 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B3412763 : Blo 944585 3412763 := bstep (se 1 (by rfl) ⟨2559572, by rfl⟩ : syracuseStep 3412763 = 5119145) B5119145
theorem B43652519 : Blo 944585 43652519 := bstep (se 1 (by rfl) ⟨32739389, by rfl⟩ : syracuseStep 43652519 = 65478779) B65478779
theorem B3188159 : Blo 944585 3188159 := bstep (se 1 (by rfl) ⟨2391119, by rfl⟩ : syracuseStep 3188159 = 4782239) B4782239
theorem B1419515 : Blo 944585 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B117942929 : Blo 944585 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B155203613 : Blo 944585 155203613 := bstep (se 3 (by rfl) ⟨29100677, by rfl⟩ : syracuseStep 155203613 = 58201355) B58201355
theorem B61356527 : Blo 944585 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B8635855 : Blo 944585 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B82986605 : Blo 944585 82986605 := bstep (se 3 (by rfl) ⟨15559988, by rfl⟩ : syracuseStep 82986605 = 31119977) B31119977
theorem B22177259 : Blo 944585 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B945691 : Blo 944585 945691 := bstep (se 1 (by rfl) ⟨709268, by rfl⟩ : syracuseStep 945691 = 1418537) B1418537
theorem B946479 : Blo 944585 946479 := bstep (se 1 (by rfl) ⟨709859, by rfl⟩ : syracuseStep 946479 = 1419719) B1419719
theorem B946943 : Blo 944585 946943 := bstep (se 1 (by rfl) ⟨710207, by rfl⟩ : syracuseStep 946943 = 1420415) B1420415
theorem B947199 : Blo 944585 947199 := bstep (se 1 (by rfl) ⟨710399, by rfl⟩ : syracuseStep 947199 = 1420799) B1420799
theorem B3831151 : Blo 944585 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B112032895 : Blo 944585 112032895 := bstep (se 1 (by rfl) ⟨84024671, by rfl⟩ : syracuseStep 112032895 = 168049343) B168049343
theorem B29101679 : Blo 944585 29101679 := bstep (se 1 (by rfl) ⟨21826259, by rfl⟩ : syracuseStep 29101679 = 43652519) B43652519
theorem B14784839 : Blo 944585 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B40904351 : Blo 944585 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B55324403 : Blo 944585 55324403 := bstep (se 1 (by rfl) ⟨41493302, by rfl⟩ : syracuseStep 55324403 = 82986605) B82986605
theorem B11514473 : Blo 944585 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B2275175 : Blo 944585 2275175 := bstep (se 1 (by rfl) ⟨1706381, by rfl⟩ : syracuseStep 2275175 = 3412763) B3412763
theorem B78628619 : Blo 944585 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B103469075 : Blo 944585 103469075 := bstep (se 1 (by rfl) ⟨77601806, by rfl⟩ : syracuseStep 103469075 = 155203613) B155203613
theorem B149377193 : Blo 944585 149377193 := bstep (se 2 (by rfl) ⟨56016447, by rfl⟩ : syracuseStep 149377193 = 112032895) B112032895
theorem B2125439 : Blo 944585 2125439 := bstep (se 1 (by rfl) ⟨1594079, by rfl⟩ : syracuseStep 2125439 = 3188159) B3188159
theorem B946343 : Blo 944585 946343 := bstep (se 1 (by rfl) ⟨709757, by rfl⟩ : syracuseStep 946343 = 1419515) B1419515
theorem B5108201 : Blo 944585 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B19401119 : Blo 944585 19401119 := bstep (se 1 (by rfl) ⟨14550839, by rfl⟩ : syracuseStep 19401119 = 29101679) B29101679
theorem B68979383 : Blo 944585 68979383 := bstep (se 1 (by rfl) ⟨51734537, by rfl⟩ : syracuseStep 68979383 = 103469075) B103469075
theorem B99584795 : Blo 944585 99584795 := bstep (se 1 (by rfl) ⟨74688596, by rfl⟩ : syracuseStep 99584795 = 149377193) B149377193
theorem B6067133 : Blo 944585 6067133 := bstep (se 3 (by rfl) ⟨1137587, by rfl⟩ : syracuseStep 6067133 = 2275175) B2275175
theorem B27269567 : Blo 944585 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B1416959 : Blo 944585 1416959 := bstep (se 1 (by rfl) ⟨1062719, by rfl⟩ : syracuseStep 1416959 = 2125439) B2125439
theorem B7676315 : Blo 944585 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B36882935 : Blo 944585 36882935 := bstep (se 1 (by rfl) ⟨27662201, by rfl⟩ : syracuseStep 36882935 = 55324403) B55324403
theorem B52419079 : Blo 944585 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B9856559 : Blo 944585 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B3405467 : Blo 944585 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B66389863 : Blo 944585 66389863 := bstep (se 1 (by rfl) ⟨49792397, by rfl⟩ : syracuseStep 66389863 = 99584795) B99584795
theorem B5117543 : Blo 944585 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B2270311 : Blo 944585 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B24588623 : Blo 944585 24588623 := bstep (se 1 (by rfl) ⟨18441467, by rfl⟩ : syracuseStep 24588623 = 36882935) B36882935
theorem B45986255 : Blo 944585 45986255 := bstep (se 1 (by rfl) ⟨34489691, by rfl⟩ : syracuseStep 45986255 = 68979383) B68979383
theorem B4044755 : Blo 944585 4044755 := bstep (se 1 (by rfl) ⟨3033566, by rfl⟩ : syracuseStep 4044755 = 6067133) B6067133
theorem B6571039 : Blo 944585 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B12934079 : Blo 944585 12934079 := bstep (se 1 (by rfl) ⟨9700559, by rfl⟩ : syracuseStep 12934079 = 19401119) B19401119
theorem B18179711 : Blo 944585 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B944639 : Blo 944585 944639 := bstep (se 1 (by rfl) ⟨708479, by rfl⟩ : syracuseStep 944639 = 1416959) B1416959
theorem B69892105 : Blo 944585 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B3411695 : Blo 944585 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B8622719 : Blo 944585 8622719 := bstep (se 1 (by rfl) ⟨6467039, by rfl⟩ : syracuseStep 8622719 = 12934079) B12934079
theorem B16392415 : Blo 944585 16392415 := bstep (se 1 (by rfl) ⟨12294311, by rfl⟩ : syracuseStep 16392415 = 24588623) B24588623
theorem B2696503 : Blo 944585 2696503 := bstep (se 1 (by rfl) ⟨2022377, by rfl⟩ : syracuseStep 2696503 = 4044755) B4044755
theorem B8761385 : Blo 944585 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B88519817 : Blo 944585 88519817 := bstep (se 2 (by rfl) ⟨33194931, by rfl⟩ : syracuseStep 88519817 = 66389863) B66389863
theorem B12108325 : Blo 944585 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B30657503 : Blo 944585 30657503 := bstep (se 1 (by rfl) ⟨22993127, by rfl⟩ : syracuseStep 30657503 = 45986255) B45986255
theorem B12119807 : Blo 944585 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B93189473 : Blo 944585 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B21856553 : Blo 944585 21856553 := bstep (se 2 (by rfl) ⟨8196207, by rfl⟩ : syracuseStep 21856553 = 16392415) B16392415
theorem B5840923 : Blo 944585 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B2274463 : Blo 944585 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B5748479 : Blo 944585 5748479 := bstep (se 1 (by rfl) ⟨4311359, by rfl⟩ : syracuseStep 5748479 = 8622719) B8622719
theorem B8079871 : Blo 944585 8079871 := bstep (se 1 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 8079871 = 12119807) B12119807
theorem B16144433 : Blo 944585 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B3595337 : Blo 944585 3595337 := bstep (se 2 (by rfl) ⟨1348251, by rfl⟩ : syracuseStep 3595337 = 2696503) B2696503
theorem B20438335 : Blo 944585 20438335 := bstep (se 1 (by rfl) ⟨15328751, by rfl⟩ : syracuseStep 20438335 = 30657503) B30657503
theorem B59013211 : Blo 944585 59013211 := bstep (se 1 (by rfl) ⟨44259908, by rfl⟩ : syracuseStep 59013211 = 88519817) B88519817
theorem B62126315 : Blo 944585 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B2396891 : Blo 944585 2396891 := bstep (se 1 (by rfl) ⟨1797668, by rfl⟩ : syracuseStep 2396891 = 3595337) B3595337
theorem B12130469 : Blo 944585 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B78684281 : Blo 944585 78684281 := bstep (se 2 (by rfl) ⟨29506605, by rfl⟩ : syracuseStep 78684281 = 59013211) B59013211
theorem B10762955 : Blo 944585 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B27251113 : Blo 944585 27251113 := bstep (se 2 (by rfl) ⟨10219167, by rfl⟩ : syracuseStep 27251113 = 20438335) B20438335
theorem B7787897 : Blo 944585 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B14571035 : Blo 944585 14571035 := bstep (se 1 (by rfl) ⟨10928276, by rfl⟩ : syracuseStep 14571035 = 21856553) B21856553
theorem B10773161 : Blo 944585 10773161 := bstep (se 2 (by rfl) ⟨4039935, by rfl⟩ : syracuseStep 10773161 = 8079871) B8079871
theorem B3832319 : Blo 944585 3832319 := bstep (se 1 (by rfl) ⟨2874239, by rfl⟩ : syracuseStep 3832319 = 5748479) B5748479
theorem B41417543 : Blo 944585 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B7182107 : Blo 944585 7182107 := bstep (se 1 (by rfl) ⟨5386580, by rfl⟩ : syracuseStep 7182107 = 10773161) B10773161
theorem B5191931 : Blo 944585 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B9714023 : Blo 944585 9714023 := bstep (se 1 (by rfl) ⟨7285517, by rfl⟩ : syracuseStep 9714023 = 14571035) B14571035
theorem B27611695 : Blo 944585 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B1597927 : Blo 944585 1597927 := bstep (se 1 (by rfl) ⟨1198445, by rfl⟩ : syracuseStep 1597927 = 2396891) B2396891
theorem B8086979 : Blo 944585 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B52456187 : Blo 944585 52456187 := bstep (se 1 (by rfl) ⟨39342140, by rfl⟩ : syracuseStep 52456187 = 78684281) B78684281
theorem B36334817 : Blo 944585 36334817 := bstep (se 2 (by rfl) ⟨13625556, by rfl⟩ : syracuseStep 36334817 = 27251113) B27251113
theorem B10219517 : Blo 944585 10219517 := bstep (se 3 (by rfl) ⟨1916159, by rfl⟩ : syracuseStep 10219517 = 3832319) B3832319
theorem B7175303 : Blo 944585 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B2130569 : Blo 944585 2130569 := bstep (se 2 (by rfl) ⟨798963, by rfl⟩ : syracuseStep 2130569 = 1597927) B1597927
theorem B4788071 : Blo 944585 4788071 := bstep (se 1 (by rfl) ⟨3591053, by rfl⟩ : syracuseStep 4788071 = 7182107) B7182107
theorem B34970791 : Blo 944585 34970791 := bstep (se 1 (by rfl) ⟨26228093, by rfl⟩ : syracuseStep 34970791 = 52456187) B52456187
theorem B24223211 : Blo 944585 24223211 := bstep (se 1 (by rfl) ⟨18167408, by rfl⟩ : syracuseStep 24223211 = 36334817) B36334817
theorem B36815593 : Blo 944585 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B5391319 : Blo 944585 5391319 := bstep (se 1 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 5391319 = 8086979) B8086979
theorem B3461287 : Blo 944585 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B6476015 : Blo 944585 6476015 := bstep (se 1 (by rfl) ⟨4857011, by rfl⟩ : syracuseStep 6476015 = 9714023) B9714023
theorem B6813011 : Blo 944585 6813011 := bstep (se 1 (by rfl) ⟨5109758, by rfl⟩ : syracuseStep 6813011 = 10219517) B10219517
theorem B4783535 : Blo 944585 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B49087457 : Blo 944585 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B3189023 : Blo 944585 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B1420379 : Blo 944585 1420379 := bstep (se 1 (by rfl) ⟨1065284, by rfl⟩ : syracuseStep 1420379 = 2130569) B2130569
theorem B7188425 : Blo 944585 7188425 := bstep (se 2 (by rfl) ⟨2695659, by rfl⟩ : syracuseStep 7188425 = 5391319) B5391319
theorem B3192047 : Blo 944585 3192047 := bstep (se 1 (by rfl) ⟨2394035, by rfl⟩ : syracuseStep 3192047 = 4788071) B4788071
theorem B4542007 : Blo 944585 4542007 := bstep (se 1 (by rfl) ⟨3406505, by rfl⟩ : syracuseStep 4542007 = 6813011) B6813011
theorem B4317343 : Blo 944585 4317343 := bstep (se 1 (by rfl) ⟨3238007, by rfl⟩ : syracuseStep 4317343 = 6476015) B6476015
theorem B16148807 : Blo 944585 16148807 := bstep (se 1 (by rfl) ⟨12111605, by rfl⟩ : syracuseStep 16148807 = 24223211) B24223211
theorem B4615049 : Blo 944585 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B46627721 : Blo 944585 46627721 := bstep (se 2 (by rfl) ⟨17485395, by rfl⟩ : syracuseStep 46627721 = 34970791) B34970791
theorem B4792283 : Blo 944585 4792283 := bstep (se 1 (by rfl) ⟨3594212, by rfl⟩ : syracuseStep 4792283 = 7188425) B7188425
theorem B10765871 : Blo 944585 10765871 := bstep (se 1 (by rfl) ⟨8074403, by rfl⟩ : syracuseStep 10765871 = 16148807) B16148807
theorem B31085147 : Blo 944585 31085147 := bstep (se 1 (by rfl) ⟨23313860, by rfl⟩ : syracuseStep 31085147 = 46627721) B46627721
theorem B32724971 : Blo 944585 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B23025829 : Blo 944585 23025829 := bstep (se 4 (by rfl) ⟨2158671, by rfl⟩ : syracuseStep 23025829 = 4317343) B4317343
theorem B6056009 : Blo 944585 6056009 := bstep (se 2 (by rfl) ⟨2271003, by rfl⟩ : syracuseStep 6056009 = 4542007) B4542007
theorem B2126015 : Blo 944585 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B3076699 : Blo 944585 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B946919 : Blo 944585 946919 := bstep (se 1 (by rfl) ⟨710189, by rfl⟩ : syracuseStep 946919 = 1420379) B1420379
theorem B2128031 : Blo 944585 2128031 := bstep (se 1 (by rfl) ⟨1596023, by rfl⟩ : syracuseStep 2128031 = 3192047) B3192047
theorem B7177247 : Blo 944585 7177247 := bstep (se 1 (by rfl) ⟨5382935, by rfl⟩ : syracuseStep 7177247 = 10765871) B10765871
theorem B4102265 : Blo 944585 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B4037339 : Blo 944585 4037339 := bstep (se 1 (by rfl) ⟨3028004, by rfl⟩ : syracuseStep 4037339 = 6056009) B6056009
theorem B1417343 : Blo 944585 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B1418687 : Blo 944585 1418687 := bstep (se 1 (by rfl) ⟨1064015, by rfl⟩ : syracuseStep 1418687 = 2128031) B2128031
theorem B3194855 : Blo 944585 3194855 := bstep (se 1 (by rfl) ⟨2396141, by rfl⟩ : syracuseStep 3194855 = 4792283) B4792283
theorem B82893725 : Blo 944585 82893725 := bstep (se 3 (by rfl) ⟨15542573, by rfl⟩ : syracuseStep 82893725 = 31085147) B31085147
theorem B21816647 : Blo 944585 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B30701105 : Blo 944585 30701105 := bstep (se 2 (by rfl) ⟨11512914, by rfl⟩ : syracuseStep 30701105 = 23025829) B23025829
theorem B4784831 : Blo 944585 4784831 := bstep (se 1 (by rfl) ⟨3588623, by rfl⟩ : syracuseStep 4784831 = 7177247) B7177247
theorem B2691559 : Blo 944585 2691559 := bstep (se 1 (by rfl) ⟨2018669, by rfl⟩ : syracuseStep 2691559 = 4037339) B4037339
theorem B55262483 : Blo 944585 55262483 := bstep (se 1 (by rfl) ⟨41446862, by rfl⟩ : syracuseStep 55262483 = 82893725) B82893725
theorem B20467403 : Blo 944585 20467403 := bstep (se 1 (by rfl) ⟨15350552, by rfl⟩ : syracuseStep 20467403 = 30701105) B30701105
theorem B944895 : Blo 944585 944895 := bstep (se 1 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 944895 = 1417343) B1417343
theorem B10939373 : Blo 944585 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B14544431 : Blo 944585 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B945791 : Blo 944585 945791 := bstep (se 1 (by rfl) ⟨709343, by rfl⟩ : syracuseStep 945791 = 1418687) B1418687
theorem B2129903 : Blo 944585 2129903 := bstep (se 1 (by rfl) ⟨1597427, by rfl⟩ : syracuseStep 2129903 = 3194855) B3194855
theorem B36841655 : Blo 944585 36841655 := bstep (se 1 (by rfl) ⟨27631241, by rfl⟩ : syracuseStep 36841655 = 55262483) B55262483
theorem B1419935 : Blo 944585 1419935 := bstep (se 1 (by rfl) ⟨1064951, by rfl⟩ : syracuseStep 1419935 = 2129903) B2129903
theorem B3189887 : Blo 944585 3189887 := bstep (se 1 (by rfl) ⟨2392415, by rfl⟩ : syracuseStep 3189887 = 4784831) B4784831
theorem B13644935 : Blo 944585 13644935 := bstep (se 1 (by rfl) ⟨10233701, by rfl⟩ : syracuseStep 13644935 = 20467403) B20467403
theorem B3588745 : Blo 944585 3588745 := bstep (se 2 (by rfl) ⟨1345779, by rfl⟩ : syracuseStep 3588745 = 2691559) B2691559
theorem B7292915 : Blo 944585 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B9696287 : Blo 944585 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B4784993 : Blo 944585 4784993 := bstep (se 2 (by rfl) ⟨1794372, by rfl⟩ : syracuseStep 4784993 = 3588745) B3588745
theorem B25856765 : Blo 944585 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B4861943 : Blo 944585 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B24561103 : Blo 944585 24561103 := bstep (se 1 (by rfl) ⟨18420827, by rfl⟩ : syracuseStep 24561103 = 36841655) B36841655
theorem B9096623 : Blo 944585 9096623 := bstep (se 1 (by rfl) ⟨6822467, by rfl⟩ : syracuseStep 9096623 = 13644935) B13644935
theorem B946623 : Blo 944585 946623 := bstep (se 1 (by rfl) ⟨709967, by rfl⟩ : syracuseStep 946623 = 1419935) B1419935
theorem B2126591 : Blo 944585 2126591 := bstep (se 1 (by rfl) ⟨1594943, by rfl⟩ : syracuseStep 2126591 = 3189887) B3189887
theorem B17237843 : Blo 944585 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B6064415 : Blo 944585 6064415 := bstep (se 1 (by rfl) ⟨4548311, by rfl⟩ : syracuseStep 6064415 = 9096623) B9096623
theorem B1417727 : Blo 944585 1417727 := bstep (se 1 (by rfl) ⟨1063295, by rfl⟩ : syracuseStep 1417727 = 2126591) B2126591
theorem B3189995 : Blo 944585 3189995 := bstep (se 1 (by rfl) ⟨2392496, by rfl⟩ : syracuseStep 3189995 = 4784993) B4784993
theorem B32748137 : Blo 944585 32748137 := bstep (se 2 (by rfl) ⟨12280551, by rfl⟩ : syracuseStep 32748137 = 24561103) B24561103
theorem B3241295 : Blo 944585 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B21832091 : Blo 944585 21832091 := bstep (se 1 (by rfl) ⟨16374068, by rfl⟩ : syracuseStep 21832091 = 32748137) B32748137
theorem B4042943 : Blo 944585 4042943 := bstep (se 1 (by rfl) ⟨3032207, by rfl⟩ : syracuseStep 4042943 = 6064415) B6064415
theorem B11491895 : Blo 944585 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B945151 : Blo 944585 945151 := bstep (se 1 (by rfl) ⟨708863, by rfl⟩ : syracuseStep 945151 = 1417727) B1417727
theorem B2126663 : Blo 944585 2126663 := bstep (se 1 (by rfl) ⟨1594997, by rfl⟩ : syracuseStep 2126663 = 3189995) B3189995
theorem B2160863 : Blo 944585 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B14554727 : Blo 944585 14554727 := bstep (se 1 (by rfl) ⟨10916045, by rfl⟩ : syracuseStep 14554727 = 21832091) B21832091
theorem B2695295 : Blo 944585 2695295 := bstep (se 1 (by rfl) ⟨2021471, by rfl⟩ : syracuseStep 2695295 = 4042943) B4042943
theorem B1417775 : Blo 944585 1417775 := bstep (se 1 (by rfl) ⟨1063331, by rfl⟩ : syracuseStep 1417775 = 2126663) B2126663
theorem B7661263 : Blo 944585 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B1440575 : Blo 944585 1440575 := bstep (se 1 (by rfl) ⟨1080431, by rfl⟩ : syracuseStep 1440575 = 2160863) B2160863
theorem B9703151 : Blo 944585 9703151 := bstep (se 1 (by rfl) ⟨7277363, by rfl⟩ : syracuseStep 9703151 = 14554727) B14554727
theorem B960383 : Blo 944585 960383 := bstep (se 1 (by rfl) ⟨720287, by rfl⟩ : syracuseStep 960383 = 1440575) B1440575
theorem B7187453 : Blo 944585 7187453 := bstep (se 3 (by rfl) ⟨1347647, by rfl⟩ : syracuseStep 7187453 = 2695295) B2695295
theorem B10215017 : Blo 944585 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B945183 : Blo 944585 945183 := bstep (se 1 (by rfl) ⟨708887, by rfl⟩ : syracuseStep 945183 = 1417775) B1417775
theorem B2561021 : Blo 944585 2561021 := bstep (se 3 (by rfl) ⟨480191, by rfl⟩ : syracuseStep 2561021 = 960383) B960383
theorem B4791635 : Blo 944585 4791635 := bstep (se 1 (by rfl) ⟨3593726, by rfl⟩ : syracuseStep 4791635 = 7187453) B7187453
theorem B6468767 : Blo 944585 6468767 := bstep (se 1 (by rfl) ⟨4851575, by rfl⟩ : syracuseStep 6468767 = 9703151) B9703151
theorem B6810011 : Blo 944585 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B1707347 : Blo 944585 1707347 := bstep (se 1 (by rfl) ⟨1280510, by rfl⟩ : syracuseStep 1707347 = 2561021) B2561021
theorem B3194423 : Blo 944585 3194423 := bstep (se 1 (by rfl) ⟨2395817, by rfl⟩ : syracuseStep 3194423 = 4791635) B4791635
theorem B4540007 : Blo 944585 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B4312511 : Blo 944585 4312511 := bstep (se 1 (by rfl) ⟨3234383, by rfl⟩ : syracuseStep 4312511 = 6468767) B6468767
theorem B12106685 : Blo 944585 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B1138231 : Blo 944585 1138231 := bstep (se 1 (by rfl) ⟨853673, by rfl⟩ : syracuseStep 1138231 = 1707347) B1707347
theorem B2875007 : Blo 944585 2875007 := bstep (se 1 (by rfl) ⟨2156255, by rfl⟩ : syracuseStep 2875007 = 4312511) B4312511
theorem B2129615 : Blo 944585 2129615 := bstep (se 1 (by rfl) ⟨1597211, by rfl⟩ : syracuseStep 2129615 = 3194423) B3194423
theorem B6070565 : Blo 944585 6070565 := bstep (se 4 (by rfl) ⟨569115, by rfl⟩ : syracuseStep 6070565 = 1138231) B1138231
theorem B8071123 : Blo 944585 8071123 := bstep (se 1 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 8071123 = 12106685) B12106685
theorem B1419743 : Blo 944585 1419743 := bstep (se 1 (by rfl) ⟨1064807, by rfl⟩ : syracuseStep 1419743 = 2129615) B2129615
theorem B1916671 : Blo 944585 1916671 := bstep (se 1 (by rfl) ⟨1437503, by rfl⟩ : syracuseStep 1916671 = 2875007) B2875007
theorem B16188173 : Blo 944585 16188173 := bstep (se 3 (by rfl) ⟨3035282, by rfl⟩ : syracuseStep 16188173 = 6070565) B6070565
theorem B10761497 : Blo 944585 10761497 := bstep (se 2 (by rfl) ⟨4035561, by rfl⟩ : syracuseStep 10761497 = 8071123) B8071123
theorem B946495 : Blo 944585 946495 := bstep (se 1 (by rfl) ⟨709871, by rfl⟩ : syracuseStep 946495 = 1419743) B1419743
theorem B2555561 : Blo 944585 2555561 := bstep (se 2 (by rfl) ⟨958335, by rfl⟩ : syracuseStep 2555561 = 1916671) B1916671
theorem B10792115 : Blo 944585 10792115 := bstep (se 1 (by rfl) ⟨8094086, by rfl⟩ : syracuseStep 10792115 = 16188173) B16188173
theorem B7174331 : Blo 944585 7174331 := bstep (se 1 (by rfl) ⟨5380748, by rfl⟩ : syracuseStep 7174331 = 10761497) B10761497
theorem B6814829 : Blo 944585 6814829 := bstep (se 3 (by rfl) ⟨1277780, by rfl⟩ : syracuseStep 6814829 = 2555561) B2555561
theorem B7194743 : Blo 944585 7194743 := bstep (se 1 (by rfl) ⟨5396057, by rfl⟩ : syracuseStep 7194743 = 10792115) B10792115
theorem B4543219 : Blo 944585 4543219 := bstep (se 1 (by rfl) ⟨3407414, by rfl⟩ : syracuseStep 4543219 = 6814829) B6814829
theorem B4782887 : Blo 944585 4782887 := bstep (se 1 (by rfl) ⟨3587165, by rfl⟩ : syracuseStep 4782887 = 7174331) B7174331
theorem B3188591 : Blo 944585 3188591 := bstep (se 1 (by rfl) ⟨2391443, by rfl⟩ : syracuseStep 3188591 = 4782887) B4782887
theorem B4796495 : Blo 944585 4796495 := bstep (se 1 (by rfl) ⟨3597371, by rfl⟩ : syracuseStep 4796495 = 7194743) B7194743
theorem B6057625 : Blo 944585 6057625 := bstep (se 2 (by rfl) ⟨2271609, by rfl⟩ : syracuseStep 6057625 = 4543219) B4543219
theorem B8076833 : Blo 944585 8076833 := bstep (se 2 (by rfl) ⟨3028812, by rfl⟩ : syracuseStep 8076833 = 6057625) B6057625
theorem B3197663 : Blo 944585 3197663 := bstep (se 1 (by rfl) ⟨2398247, by rfl⟩ : syracuseStep 3197663 = 4796495) B4796495
theorem B2125727 : Blo 944585 2125727 := bstep (se 1 (by rfl) ⟨1594295, by rfl⟩ : syracuseStep 2125727 = 3188591) B3188591
theorem B2131775 : Blo 944585 2131775 := bstep (se 1 (by rfl) ⟨1598831, by rfl⟩ : syracuseStep 2131775 = 3197663) B3197663
theorem B1417151 : Blo 944585 1417151 := bstep (se 1 (by rfl) ⟨1062863, by rfl⟩ : syracuseStep 1417151 = 2125727) B2125727
theorem B5384555 : Blo 944585 5384555 := bstep (se 1 (by rfl) ⟨4038416, by rfl⟩ : syracuseStep 5384555 = 8076833) B8076833
theorem B1421183 : Blo 944585 1421183 := bstep (se 1 (by rfl) ⟨1065887, by rfl⟩ : syracuseStep 1421183 = 2131775) B2131775
theorem B3589703 : Blo 944585 3589703 := bstep (se 1 (by rfl) ⟨2692277, by rfl⟩ : syracuseStep 3589703 = 5384555) B5384555
theorem B944767 : Blo 944585 944767 := bstep (se 1 (by rfl) ⟨708575, by rfl⟩ : syracuseStep 944767 = 1417151) B1417151
theorem B2393135 : Blo 944585 2393135 := bstep (se 1 (by rfl) ⟨1794851, by rfl⟩ : syracuseStep 2393135 = 3589703) B3589703
theorem B947455 : Blo 944585 947455 := bstep (se 1 (by rfl) ⟨710591, by rfl⟩ : syracuseStep 947455 = 1421183) B1421183
theorem B1595423 : Blo 944585 1595423 := bstep (se 1 (by rfl) ⟨1196567, by rfl⟩ : syracuseStep 1595423 = 2393135) B2393135
theorem B1063615 : Blo 944585 1063615 := bstep (se 1 (by rfl) ⟨797711, by rfl⟩ : syracuseStep 1063615 = 1595423) B1595423
theorem B1418153 : Blo 944585 1418153 := bstep (se 2 (by rfl) ⟨531807, by rfl⟩ : syracuseStep 1418153 = 1063615) B1063615
theorem B945435 : Blo 944585 945435 := bstep (se 1 (by rfl) ⟨709076, by rfl⟩ : syracuseStep 945435 = 1418153) B1418153

theorem C0 (j : ℕ) (h1 : 236146 ≤ j) (h2 : j ≤ 236845) : Blo 944585 (4 * j + 3) := by
  interval_cases j
  · exact B944587
  · exact B944591
  · exact B944595
  · exact B944599
  · exact B944603
  · exact B944607
  · exact B944611
  · exact B944615
  · exact B944619
  · exact B944623
  · exact B944627
  · exact B944631
  · exact B944635
  · exact B944639
  · exact B944643
  · exact B944647
  · exact B944651
  · exact B944655
  · exact B944659
  · exact B944663
  · exact B944667
  · exact B944671
  · exact B944675
  · exact B944679
  · exact B944683
  · exact B944687
  · exact B944691
  · exact B944695
  · exact B944699
  · exact B944703
  · exact B944707
  · exact B944711
  · exact B944715
  · exact B944719
  · exact B944723
  · exact B944727
  · exact B944731
  · exact B944735
  · exact B944739
  · exact B944743
  · exact B944747
  · exact B944751
  · exact B944755
  · exact B944759
  · exact B944763
  · exact B944767
  · exact B944771
  · exact B944775
  · exact B944779
  · exact B944783
  · exact B944787
  · exact B944791
  · exact B944795
  · exact B944799
  · exact B944803
  · exact B944807
  · exact B944811
  · exact B944815
  · exact B944819
  · exact B944823
  · exact B944827
  · exact B944831
  · exact B944835
  · exact B944839
  · exact B944843
  · exact B944847
  · exact B944851
  · exact B944855
  · exact B944859
  · exact B944863
  · exact B944867
  · exact B944871
  · exact B944875
  · exact B944879
  · exact B944883
  · exact B944887
  · exact B944891
  · exact B944895
  · exact B944899
  · exact B944903
  · exact B944907
  · exact B944911
  · exact B944915
  · exact B944919
  · exact B944923
  · exact B944927
  · exact B944931
  · exact B944935
  · exact B944939
  · exact B944943
  · exact B944947
  · exact B944951
  · exact B944955
  · exact B944959
  · exact B944963
  · exact B944967
  · exact B944971
  · exact B944975
  · exact B944979
  · exact B944983
  · exact B944987
  · exact B944991
  · exact B944995
  · exact B944999
  · exact B945003
  · exact B945007
  · exact B945011
  · exact B945015
  · exact B945019
  · exact B945023
  · exact B945027
  · exact B945031
  · exact B945035
  · exact B945039
  · exact B945043
  · exact B945047
  · exact B945051
  · exact B945055
  · exact B945059
  · exact B945063
  · exact B945067
  · exact B945071
  · exact B945075
  · exact B945079
  · exact B945083
  · exact B945087
  · exact B945091
  · exact B945095
  · exact B945099
  · exact B945103
  · exact B945107
  · exact B945111
  · exact B945115
  · exact B945119
  · exact B945123
  · exact B945127
  · exact B945131
  · exact B945135
  · exact B945139
  · exact B945143
  · exact B945147
  · exact B945151
  · exact B945155
  · exact B945159
  · exact B945163
  · exact B945167
  · exact B945171
  · exact B945175
  · exact B945179
  · exact B945183
  · exact B945187
  · exact B945191
  · exact B945195
  · exact B945199
  · exact B945203
  · exact B945207
  · exact B945211
  · exact B945215
  · exact B945219
  · exact B945223
  · exact B945227
  · exact B945231
  · exact B945235
  · exact B945239
  · exact B945243
  · exact B945247
  · exact B945251
  · exact B945255
  · exact B945259
  · exact B945263
  · exact B945267
  · exact B945271
  · exact B945275
  · exact B945279
  · exact B945283
  · exact B945287
  · exact B945291
  · exact B945295
  · exact B945299
  · exact B945303
  · exact B945307
  · exact B945311
  · exact B945315
  · exact B945319
  · exact B945323
  · exact B945327
  · exact B945331
  · exact B945335
  · exact B945339
  · exact B945343
  · exact B945347
  · exact B945351
  · exact B945355
  · exact B945359
  · exact B945363
  · exact B945367
  · exact B945371
  · exact B945375
  · exact B945379
  · exact B945383
  · exact B945387
  · exact B945391
  · exact B945395
  · exact B945399
  · exact B945403
  · exact B945407
  · exact B945411
  · exact B945415
  · exact B945419
  · exact B945423
  · exact B945427
  · exact B945431
  · exact B945435
  · exact B945439
  · exact B945443
  · exact B945447
  · exact B945451
  · exact B945455
  · exact B945459
  · exact B945463
  · exact B945467
  · exact B945471
  · exact B945475
  · exact B945479
  · exact B945483
  · exact B945487
  · exact B945491
  · exact B945495
  · exact B945499
  · exact B945503
  · exact B945507
  · exact B945511
  · exact B945515
  · exact B945519
  · exact B945523
  · exact B945527
  · exact B945531
  · exact B945535
  · exact B945539
  · exact B945543
  · exact B945547
  · exact B945551
  · exact B945555
  · exact B945559
  · exact B945563
  · exact B945567
  · exact B945571
  · exact B945575
  · exact B945579
  · exact B945583
  · exact B945587
  · exact B945591
  · exact B945595
  · exact B945599
  · exact B945603
  · exact B945607
  · exact B945611
  · exact B945615
  · exact B945619
  · exact B945623
  · exact B945627
  · exact B945631
  · exact B945635
  · exact B945639
  · exact B945643
  · exact B945647
  · exact B945651
  · exact B945655
  · exact B945659
  · exact B945663
  · exact B945667
  · exact B945671
  · exact B945675
  · exact B945679
  · exact B945683
  · exact B945687
  · exact B945691
  · exact B945695
  · exact B945699
  · exact B945703
  · exact B945707
  · exact B945711
  · exact B945715
  · exact B945719
  · exact B945723
  · exact B945727
  · exact B945731
  · exact B945735
  · exact B945739
  · exact B945743
  · exact B945747
  · exact B945751
  · exact B945755
  · exact B945759
  · exact B945763
  · exact B945767
  · exact B945771
  · exact B945775
  · exact B945779
  · exact B945783
  · exact B945787
  · exact B945791
  · exact B945795
  · exact B945799
  · exact B945803
  · exact B945807
  · exact B945811
  · exact B945815
  · exact B945819
  · exact B945823
  · exact B945827
  · exact B945831
  · exact B945835
  · exact B945839
  · exact B945843
  · exact B945847
  · exact B945851
  · exact B945855
  · exact B945859
  · exact B945863
  · exact B945867
  · exact B945871
  · exact B945875
  · exact B945879
  · exact B945883
  · exact B945887
  · exact B945891
  · exact B945895
  · exact B945899
  · exact B945903
  · exact B945907
  · exact B945911
  · exact B945915
  · exact B945919
  · exact B945923
  · exact B945927
  · exact B945931
  · exact B945935
  · exact B945939
  · exact B945943
  · exact B945947
  · exact B945951
  · exact B945955
  · exact B945959
  · exact B945963
  · exact B945967
  · exact B945971
  · exact B945975
  · exact B945979
  · exact B945983
  · exact B945987
  · exact B945991
  · exact B945995
  · exact B945999
  · exact B946003
  · exact B946007
  · exact B946011
  · exact B946015
  · exact B946019
  · exact B946023
  · exact B946027
  · exact B946031
  · exact B946035
  · exact B946039
  · exact B946043
  · exact B946047
  · exact B946051
  · exact B946055
  · exact B946059
  · exact B946063
  · exact B946067
  · exact B946071
  · exact B946075
  · exact B946079
  · exact B946083
  · exact B946087
  · exact B946091
  · exact B946095
  · exact B946099
  · exact B946103
  · exact B946107
  · exact B946111
  · exact B946115
  · exact B946119
  · exact B946123
  · exact B946127
  · exact B946131
  · exact B946135
  · exact B946139
  · exact B946143
  · exact B946147
  · exact B946151
  · exact B946155
  · exact B946159
  · exact B946163
  · exact B946167
  · exact B946171
  · exact B946175
  · exact B946179
  · exact B946183
  · exact B946187
  · exact B946191
  · exact B946195
  · exact B946199
  · exact B946203
  · exact B946207
  · exact B946211
  · exact B946215
  · exact B946219
  · exact B946223
  · exact B946227
  · exact B946231
  · exact B946235
  · exact B946239
  · exact B946243
  · exact B946247
  · exact B946251
  · exact B946255
  · exact B946259
  · exact B946263
  · exact B946267
  · exact B946271
  · exact B946275
  · exact B946279
  · exact B946283
  · exact B946287
  · exact B946291
  · exact B946295
  · exact B946299
  · exact B946303
  · exact B946307
  · exact B946311
  · exact B946315
  · exact B946319
  · exact B946323
  · exact B946327
  · exact B946331
  · exact B946335
  · exact B946339
  · exact B946343
  · exact B946347
  · exact B946351
  · exact B946355
  · exact B946359
  · exact B946363
  · exact B946367
  · exact B946371
  · exact B946375
  · exact B946379
  · exact B946383
  · exact B946387
  · exact B946391
  · exact B946395
  · exact B946399
  · exact B946403
  · exact B946407
  · exact B946411
  · exact B946415
  · exact B946419
  · exact B946423
  · exact B946427
  · exact B946431
  · exact B946435
  · exact B946439
  · exact B946443
  · exact B946447
  · exact B946451
  · exact B946455
  · exact B946459
  · exact B946463
  · exact B946467
  · exact B946471
  · exact B946475
  · exact B946479
  · exact B946483
  · exact B946487
  · exact B946491
  · exact B946495
  · exact B946499
  · exact B946503
  · exact B946507
  · exact B946511
  · exact B946515
  · exact B946519
  · exact B946523
  · exact B946527
  · exact B946531
  · exact B946535
  · exact B946539
  · exact B946543
  · exact B946547
  · exact B946551
  · exact B946555
  · exact B946559
  · exact B946563
  · exact B946567
  · exact B946571
  · exact B946575
  · exact B946579
  · exact B946583
  · exact B946587
  · exact B946591
  · exact B946595
  · exact B946599
  · exact B946603
  · exact B946607
  · exact B946611
  · exact B946615
  · exact B946619
  · exact B946623
  · exact B946627
  · exact B946631
  · exact B946635
  · exact B946639
  · exact B946643
  · exact B946647
  · exact B946651
  · exact B946655
  · exact B946659
  · exact B946663
  · exact B946667
  · exact B946671
  · exact B946675
  · exact B946679
  · exact B946683
  · exact B946687
  · exact B946691
  · exact B946695
  · exact B946699
  · exact B946703
  · exact B946707
  · exact B946711
  · exact B946715
  · exact B946719
  · exact B946723
  · exact B946727
  · exact B946731
  · exact B946735
  · exact B946739
  · exact B946743
  · exact B946747
  · exact B946751
  · exact B946755
  · exact B946759
  · exact B946763
  · exact B946767
  · exact B946771
  · exact B946775
  · exact B946779
  · exact B946783
  · exact B946787
  · exact B946791
  · exact B946795
  · exact B946799
  · exact B946803
  · exact B946807
  · exact B946811
  · exact B946815
  · exact B946819
  · exact B946823
  · exact B946827
  · exact B946831
  · exact B946835
  · exact B946839
  · exact B946843
  · exact B946847
  · exact B946851
  · exact B946855
  · exact B946859
  · exact B946863
  · exact B946867
  · exact B946871
  · exact B946875
  · exact B946879
  · exact B946883
  · exact B946887
  · exact B946891
  · exact B946895
  · exact B946899
  · exact B946903
  · exact B946907
  · exact B946911
  · exact B946915
  · exact B946919
  · exact B946923
  · exact B946927
  · exact B946931
  · exact B946935
  · exact B946939
  · exact B946943
  · exact B946947
  · exact B946951
  · exact B946955
  · exact B946959
  · exact B946963
  · exact B946967
  · exact B946971
  · exact B946975
  · exact B946979
  · exact B946983
  · exact B946987
  · exact B946991
  · exact B946995
  · exact B946999
  · exact B947003
  · exact B947007
  · exact B947011
  · exact B947015
  · exact B947019
  · exact B947023
  · exact B947027
  · exact B947031
  · exact B947035
  · exact B947039
  · exact B947043
  · exact B947047
  · exact B947051
  · exact B947055
  · exact B947059
  · exact B947063
  · exact B947067
  · exact B947071
  · exact B947075
  · exact B947079
  · exact B947083
  · exact B947087
  · exact B947091
  · exact B947095
  · exact B947099
  · exact B947103
  · exact B947107
  · exact B947111
  · exact B947115
  · exact B947119
  · exact B947123
  · exact B947127
  · exact B947131
  · exact B947135
  · exact B947139
  · exact B947143
  · exact B947147
  · exact B947151
  · exact B947155
  · exact B947159
  · exact B947163
  · exact B947167
  · exact B947171
  · exact B947175
  · exact B947179
  · exact B947183
  · exact B947187
  · exact B947191
  · exact B947195
  · exact B947199
  · exact B947203
  · exact B947207
  · exact B947211
  · exact B947215
  · exact B947219
  · exact B947223
  · exact B947227
  · exact B947231
  · exact B947235
  · exact B947239
  · exact B947243
  · exact B947247
  · exact B947251
  · exact B947255
  · exact B947259
  · exact B947263
  · exact B947267
  · exact B947271
  · exact B947275
  · exact B947279
  · exact B947283
  · exact B947287
  · exact B947291
  · exact B947295
  · exact B947299
  · exact B947303
  · exact B947307
  · exact B947311
  · exact B947315
  · exact B947319
  · exact B947323
  · exact B947327
  · exact B947331
  · exact B947335
  · exact B947339
  · exact B947343
  · exact B947347
  · exact B947351
  · exact B947355
  · exact B947359
  · exact B947363
  · exact B947367
  · exact B947371
  · exact B947375
  · exact B947379
  · exact B947383

theorem C1 (j : ℕ) (h1 : 236846 ≤ j) (h2 : j ≤ 237145) : Blo 944585 (4 * j + 3) := by
  interval_cases j
  · exact B947387
  · exact B947391
  · exact B947395
  · exact B947399
  · exact B947403
  · exact B947407
  · exact B947411
  · exact B947415
  · exact B947419
  · exact B947423
  · exact B947427
  · exact B947431
  · exact B947435
  · exact B947439
  · exact B947443
  · exact B947447
  · exact B947451
  · exact B947455
  · exact B947459
  · exact B947463
  · exact B947467
  · exact B947471
  · exact B947475
  · exact B947479
  · exact B947483
  · exact B947487
  · exact B947491
  · exact B947495
  · exact B947499
  · exact B947503
  · exact B947507
  · exact B947511
  · exact B947515
  · exact B947519
  · exact B947523
  · exact B947527
  · exact B947531
  · exact B947535
  · exact B947539
  · exact B947543
  · exact B947547
  · exact B947551
  · exact B947555
  · exact B947559
  · exact B947563
  · exact B947567
  · exact B947571
  · exact B947575
  · exact B947579
  · exact B947583
  · exact B947587
  · exact B947591
  · exact B947595
  · exact B947599
  · exact B947603
  · exact B947607
  · exact B947611
  · exact B947615
  · exact B947619
  · exact B947623
  · exact B947627
  · exact B947631
  · exact B947635
  · exact B947639
  · exact B947643
  · exact B947647
  · exact B947651
  · exact B947655
  · exact B947659
  · exact B947663
  · exact B947667
  · exact B947671
  · exact B947675
  · exact B947679
  · exact B947683
  · exact B947687
  · exact B947691
  · exact B947695
  · exact B947699
  · exact B947703
  · exact B947707
  · exact B947711
  · exact B947715
  · exact B947719
  · exact B947723
  · exact B947727
  · exact B947731
  · exact B947735
  · exact B947739
  · exact B947743
  · exact B947747
  · exact B947751
  · exact B947755
  · exact B947759
  · exact B947763
  · exact B947767
  · exact B947771
  · exact B947775
  · exact B947779
  · exact B947783
  · exact B947787
  · exact B947791
  · exact B947795
  · exact B947799
  · exact B947803
  · exact B947807
  · exact B947811
  · exact B947815
  · exact B947819
  · exact B947823
  · exact B947827
  · exact B947831
  · exact B947835
  · exact B947839
  · exact B947843
  · exact B947847
  · exact B947851
  · exact B947855
  · exact B947859
  · exact B947863
  · exact B947867
  · exact B947871
  · exact B947875
  · exact B947879
  · exact B947883
  · exact B947887
  · exact B947891
  · exact B947895
  · exact B947899
  · exact B947903
  · exact B947907
  · exact B947911
  · exact B947915
  · exact B947919
  · exact B947923
  · exact B947927
  · exact B947931
  · exact B947935
  · exact B947939
  · exact B947943
  · exact B947947
  · exact B947951
  · exact B947955
  · exact B947959
  · exact B947963
  · exact B947967
  · exact B947971
  · exact B947975
  · exact B947979
  · exact B947983
  · exact B947987
  · exact B947991
  · exact B947995
  · exact B947999
  · exact B948003
  · exact B948007
  · exact B948011
  · exact B948015
  · exact B948019
  · exact B948023
  · exact B948027
  · exact B948031
  · exact B948035
  · exact B948039
  · exact B948043
  · exact B948047
  · exact B948051
  · exact B948055
  · exact B948059
  · exact B948063
  · exact B948067
  · exact B948071
  · exact B948075
  · exact B948079
  · exact B948083
  · exact B948087
  · exact B948091
  · exact B948095
  · exact B948099
  · exact B948103
  · exact B948107
  · exact B948111
  · exact B948115
  · exact B948119
  · exact B948123
  · exact B948127
  · exact B948131
  · exact B948135
  · exact B948139
  · exact B948143
  · exact B948147
  · exact B948151
  · exact B948155
  · exact B948159
  · exact B948163
  · exact B948167
  · exact B948171
  · exact B948175
  · exact B948179
  · exact B948183
  · exact B948187
  · exact B948191
  · exact B948195
  · exact B948199
  · exact B948203
  · exact B948207
  · exact B948211
  · exact B948215
  · exact B948219
  · exact B948223
  · exact B948227
  · exact B948231
  · exact B948235
  · exact B948239
  · exact B948243
  · exact B948247
  · exact B948251
  · exact B948255
  · exact B948259
  · exact B948263
  · exact B948267
  · exact B948271
  · exact B948275
  · exact B948279
  · exact B948283
  · exact B948287
  · exact B948291
  · exact B948295
  · exact B948299
  · exact B948303
  · exact B948307
  · exact B948311
  · exact B948315
  · exact B948319
  · exact B948323
  · exact B948327
  · exact B948331
  · exact B948335
  · exact B948339
  · exact B948343
  · exact B948347
  · exact B948351
  · exact B948355
  · exact B948359
  · exact B948363
  · exact B948367
  · exact B948371
  · exact B948375
  · exact B948379
  · exact B948383
  · exact B948387
  · exact B948391
  · exact B948395
  · exact B948399
  · exact B948403
  · exact B948407
  · exact B948411
  · exact B948415
  · exact B948419
  · exact B948423
  · exact B948427
  · exact B948431
  · exact B948435
  · exact B948439
  · exact B948443
  · exact B948447
  · exact B948451
  · exact B948455
  · exact B948459
  · exact B948463
  · exact B948467
  · exact B948471
  · exact B948475
  · exact B948479
  · exact B948483
  · exact B948487
  · exact B948491
  · exact B948495
  · exact B948499
  · exact B948503
  · exact B948507
  · exact B948511
  · exact B948515
  · exact B948519
  · exact B948523
  · exact B948527
  · exact B948531
  · exact B948535
  · exact B948539
  · exact B948543
  · exact B948547
  · exact B948551
  · exact B948555
  · exact B948559
  · exact B948563
  · exact B948567
  · exact B948571
  · exact B948575
  · exact B948579
  · exact B948583

theorem solution (m : ℕ) (hlo : 944585 ≤ m) (hhi : m ≤ 948585) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 236146 ≤ j := by omega
    have hj2 : j ≤ 237145 := by omega
    have hb : Blo 944585 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 236846 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
