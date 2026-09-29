-- Prove2me | solution 1 for syracuse_descends_range_1731066_1733066
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:31:59.007307+00:00
-- url     : https://prove2.me/submissions/fb21e537-c5d3-43ab-9d91-3889387f3b46

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


theorem B2465797 : Blo 1731066 2465797 := bbase (se 4 (by rfl) ⟨231168, by rfl⟩ : syracuseStep 2465797 = 462337) (by norm_num)
theorem B2596877 : Blo 1731066 2596877 := bbase (se 3 (by rfl) ⟨486914, by rfl⟩ : syracuseStep 2596877 = 973829) (by norm_num)
theorem B2596901 : Blo 1731066 2596901 := bbase (se 4 (by rfl) ⟨243459, by rfl⟩ : syracuseStep 2596901 = 486919) (by norm_num)
theorem B2596925 : Blo 1731066 2596925 := bbase (se 3 (by rfl) ⟨486923, by rfl⟩ : syracuseStep 2596925 = 973847) (by norm_num)
theorem B2596949 : Blo 1731066 2596949 := bbase (se 8 (by rfl) ⟨15216, by rfl⟩ : syracuseStep 2596949 = 30433) (by norm_num)
theorem B2596973 : Blo 1731066 2596973 := bbase (se 3 (by rfl) ⟨486932, by rfl⟩ : syracuseStep 2596973 = 973865) (by norm_num)
theorem B2596997 : Blo 1731066 2596997 := bbase (se 4 (by rfl) ⟨243468, by rfl⟩ : syracuseStep 2596997 = 486937) (by norm_num)
theorem B2080901 : Blo 1731066 2080901 := bbase (se 4 (by rfl) ⟨195084, by rfl⟩ : syracuseStep 2080901 = 390169) (by norm_num)
theorem B4382869 : Blo 1731066 4382869 := bbase (se 6 (by rfl) ⟨102723, by rfl⟩ : syracuseStep 4382869 = 205447) (by norm_num)
theorem B2597021 : Blo 1731066 2597021 := bbase (se 3 (by rfl) ⟨486941, by rfl⟩ : syracuseStep 2597021 = 973883) (by norm_num)
theorem B2498725 : Blo 1731066 2498725 := bbase (se 4 (by rfl) ⟨234255, by rfl⟩ : syracuseStep 2498725 = 468511) (by norm_num)
theorem B2597045 : Blo 1731066 2597045 := bbase (se 5 (by rfl) ⟨121736, by rfl⟩ : syracuseStep 2597045 = 243473) (by norm_num)
theorem B2597069 : Blo 1731066 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B2597093 : Blo 1731066 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B6578405 : Blo 1731066 6578405 := bbase (se 4 (by rfl) ⟨616725, by rfl⟩ : syracuseStep 6578405 = 1233451) (by norm_num)
theorem B2597117 : Blo 1731066 2597117 := bbase (se 3 (by rfl) ⟨486959, by rfl⟩ : syracuseStep 2597117 = 973919) (by norm_num)
theorem B4382981 : Blo 1731066 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B2597141 : Blo 1731066 2597141 := bbase (se 6 (by rfl) ⟨60870, by rfl⟩ : syracuseStep 2597141 = 121741) (by norm_num)
theorem B33292565 : Blo 1731066 33292565 := bbase (se 6 (by rfl) ⟨780294, by rfl⟩ : syracuseStep 33292565 = 1560589) (by norm_num)
theorem B2081065 : Blo 1731066 2081065 := bbase (se 2 (by rfl) ⟨780399, by rfl⟩ : syracuseStep 2081065 = 1560799) (by norm_num)
theorem B2597165 : Blo 1731066 2597165 := bbase (se 3 (by rfl) ⟨486968, by rfl⟩ : syracuseStep 2597165 = 973937) (by norm_num)
theorem B2597189 : Blo 1731066 2597189 := bbase (se 4 (by rfl) ⟨243486, by rfl⟩ : syracuseStep 2597189 = 486973) (by norm_num)
theorem B2081093 : Blo 1731066 2081093 := bbase (se 4 (by rfl) ⟨195102, by rfl⟩ : syracuseStep 2081093 = 390205) (by norm_num)
theorem B35537237 : Blo 1731066 35537237 := bbase (se 10 (by rfl) ⟨52056, by rfl⟩ : syracuseStep 35537237 = 104113) (by norm_num)
theorem B2597213 : Blo 1731066 2597213 := bbase (se 3 (by rfl) ⟨486977, by rfl⟩ : syracuseStep 2597213 = 973955) (by norm_num)
theorem B2597237 : Blo 1731066 2597237 := bbase (se 5 (by rfl) ⟨121745, by rfl⟩ : syracuseStep 2597237 = 243491) (by norm_num)
theorem B2466173 : Blo 1731066 2466173 := bbase (se 3 (by rfl) ⟨462407, by rfl⟩ : syracuseStep 2466173 = 924815) (by norm_num)
theorem B2597261 : Blo 1731066 2597261 := bbase (se 3 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 2597261 = 973973) (by norm_num)
theorem B11092373 : Blo 1731066 11092373 := bbase (se 6 (by rfl) ⟨259977, by rfl⟩ : syracuseStep 11092373 = 519955) (by norm_num)
theorem B2597285 : Blo 1731066 2597285 := bbase (se 4 (by rfl) ⟨243495, by rfl⟩ : syracuseStep 2597285 = 486991) (by norm_num)
theorem B7020965 : Blo 1731066 7020965 := bbase (se 4 (by rfl) ⟨658215, by rfl⟩ : syracuseStep 7020965 = 1316431) (by norm_num)
theorem B2081209 : Blo 1731066 2081209 := bbase (se 2 (by rfl) ⟨780453, by rfl⟩ : syracuseStep 2081209 = 1560907) (by norm_num)
theorem B2597309 : Blo 1731066 2597309 := bbase (se 3 (by rfl) ⟨486995, by rfl⟩ : syracuseStep 2597309 = 973991) (by norm_num)
theorem B4383173 : Blo 1731066 4383173 := bbase (se 4 (by rfl) ⟨410922, by rfl⟩ : syracuseStep 4383173 = 821845) (by norm_num)
theorem B2597333 : Blo 1731066 2597333 := bbase (se 7 (by rfl) ⟨30437, by rfl⟩ : syracuseStep 2597333 = 60875) (by norm_num)
theorem B2597357 : Blo 1731066 2597357 := bbase (se 3 (by rfl) ⟨487004, by rfl⟩ : syracuseStep 2597357 = 974009) (by norm_num)
theorem B2597381 : Blo 1731066 2597381 := bbase (se 4 (by rfl) ⟨243504, by rfl⟩ : syracuseStep 2597381 = 487009) (by norm_num)
theorem B3121669 : Blo 1731066 3121669 := bbase (se 4 (by rfl) ⟨292656, by rfl⟩ : syracuseStep 3121669 = 585313) (by norm_num)
theorem B2081305 : Blo 1731066 2081305 := bbase (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) (by norm_num)
theorem B2597405 : Blo 1731066 2597405 := bbase (se 3 (by rfl) ⟨487013, by rfl⟩ : syracuseStep 2597405 = 974027) (by norm_num)
theorem B2597429 : Blo 1731066 2597429 := bbase (se 5 (by rfl) ⟨121754, by rfl⟩ : syracuseStep 2597429 = 243509) (by norm_num)
theorem B12485173 : Blo 1731066 12485173 := bbase (se 5 (by rfl) ⟨585242, by rfl⟩ : syracuseStep 12485173 = 1170485) (by norm_num)
theorem B1925689 : Blo 1731066 1925689 := bbase (se 2 (by rfl) ⟨722133, by rfl⟩ : syracuseStep 1925689 = 1444267) (by norm_num)
theorem B4162109 : Blo 1731066 4162109 := bbase (se 3 (by rfl) ⟨780395, by rfl⟩ : syracuseStep 4162109 = 1560791) (by norm_num)
theorem B2597453 : Blo 1731066 2597453 := bbase (se 3 (by rfl) ⟨487022, by rfl⟩ : syracuseStep 2597453 = 974045) (by norm_num)
theorem B2597477 : Blo 1731066 2597477 := bbase (se 4 (by rfl) ⟨243513, by rfl⟩ : syracuseStep 2597477 = 487027) (by norm_num)
theorem B2597501 : Blo 1731066 2597501 := bbase (se 3 (by rfl) ⟨487031, by rfl⟩ : syracuseStep 2597501 = 974063) (by norm_num)
theorem B2597525 : Blo 1731066 2597525 := bbase (se 6 (by rfl) ⟨60879, by rfl⟩ : syracuseStep 2597525 = 121759) (by norm_num)
theorem B2597549 : Blo 1731066 2597549 := bbase (se 3 (by rfl) ⟨487040, by rfl⟩ : syracuseStep 2597549 = 974081) (by norm_num)
theorem B2597573 : Blo 1731066 2597573 := bbase (se 4 (by rfl) ⟨243522, by rfl⟩ : syracuseStep 2597573 = 487045) (by norm_num)
theorem B2597597 : Blo 1731066 2597597 := bbase (se 3 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 2597597 = 974099) (by norm_num)
theorem B2851549 : Blo 1731066 2851549 := bbase (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) (by norm_num)
theorem B2597621 : Blo 1731066 2597621 := bbase (se 5 (by rfl) ⟨121763, by rfl⟩ : syracuseStep 2597621 = 243527) (by norm_num)
theorem B2597645 : Blo 1731066 2597645 := bbase (se 3 (by rfl) ⟨487058, by rfl⟩ : syracuseStep 2597645 = 974117) (by norm_num)
theorem B18735893 : Blo 1731066 18735893 := bbase (se 6 (by rfl) ⟨439122, by rfl⟩ : syracuseStep 18735893 = 878245) (by norm_num)
theorem B4383517 : Blo 1731066 4383517 := bbase (se 3 (by rfl) ⟨821909, by rfl⟩ : syracuseStep 4383517 = 1643819) (by norm_num)
theorem B2597669 : Blo 1731066 2597669 := bbase (se 4 (by rfl) ⟨243531, by rfl⟩ : syracuseStep 2597669 = 487063) (by norm_num)
theorem B2597693 : Blo 1731066 2597693 := bbase (se 3 (by rfl) ⟨487067, by rfl⟩ : syracuseStep 2597693 = 974135) (by norm_num)
theorem B2597717 : Blo 1731066 2597717 := bbase (se 9 (by rfl) ⟨7610, by rfl⟩ : syracuseStep 2597717 = 15221) (by norm_num)
theorem B2597741 : Blo 1731066 2597741 := bbase (se 3 (by rfl) ⟨487076, by rfl⟩ : syracuseStep 2597741 = 974153) (by norm_num)
theorem B2597765 : Blo 1731066 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B4383629 : Blo 1731066 4383629 := bbase (se 3 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 4383629 = 1643861) (by norm_num)
theorem B2597789 : Blo 1731066 2597789 := bbase (se 3 (by rfl) ⟨487085, by rfl⟩ : syracuseStep 2597789 = 974171) (by norm_num)
theorem B2597813 : Blo 1731066 2597813 := bbase (se 5 (by rfl) ⟨121772, by rfl⟩ : syracuseStep 2597813 = 243545) (by norm_num)
theorem B3122101 : Blo 1731066 3122101 := bbase (se 5 (by rfl) ⟨146348, by rfl⟩ : syracuseStep 3122101 = 292697) (by norm_num)
theorem B2597837 : Blo 1731066 2597837 := bbase (se 3 (by rfl) ⟨487094, by rfl⟩ : syracuseStep 2597837 = 974189) (by norm_num)
theorem B1975249 : Blo 1731066 1975249 := bbase (se 2 (by rfl) ⟨740718, by rfl⟩ : syracuseStep 1975249 = 1481437) (by norm_num)
theorem B2597861 : Blo 1731066 2597861 := bbase (se 4 (by rfl) ⟨243549, by rfl⟩ : syracuseStep 2597861 = 487099) (by norm_num)
theorem B2081785 : Blo 1731066 2081785 := bbase (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) (by norm_num)
theorem B2597885 : Blo 1731066 2597885 := bbase (se 3 (by rfl) ⟨487103, by rfl⟩ : syracuseStep 2597885 = 974207) (by norm_num)
theorem B2597909 : Blo 1731066 2597909 := bbase (se 6 (by rfl) ⟨60888, by rfl⟩ : syracuseStep 2597909 = 121777) (by norm_num)
theorem B2597933 : Blo 1731066 2597933 := bbase (se 3 (by rfl) ⟨487112, by rfl⟩ : syracuseStep 2597933 = 974225) (by norm_num)
theorem B2597957 : Blo 1731066 2597957 := bbase (se 4 (by rfl) ⟨243558, by rfl⟩ : syracuseStep 2597957 = 487117) (by norm_num)
theorem B4932677 : Blo 1731066 4932677 := bbase (se 4 (by rfl) ⟨462438, by rfl⟩ : syracuseStep 4932677 = 924877) (by norm_num)
theorem B4383821 : Blo 1731066 4383821 := bbase (se 3 (by rfl) ⟨821966, by rfl⟩ : syracuseStep 4383821 = 1643933) (by norm_num)
theorem B7398485 : Blo 1731066 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B2597981 : Blo 1731066 2597981 := bbase (se 3 (by rfl) ⟨487121, by rfl⟩ : syracuseStep 2597981 = 974243) (by norm_num)
theorem B2598005 : Blo 1731066 2598005 := bbase (se 5 (by rfl) ⟨121781, by rfl⟩ : syracuseStep 2598005 = 243563) (by norm_num)
theorem B2598029 : Blo 1731066 2598029 := bbase (se 3 (by rfl) ⟨487130, by rfl⟩ : syracuseStep 2598029 = 974261) (by norm_num)
theorem B8766629 : Blo 1731066 8766629 := bbase (se 4 (by rfl) ⟨821871, by rfl⟩ : syracuseStep 8766629 = 1643743) (by norm_num)
theorem B2598053 : Blo 1731066 2598053 := bbase (se 4 (by rfl) ⟨243567, by rfl⟩ : syracuseStep 2598053 = 487135) (by norm_num)
theorem B2598077 : Blo 1731066 2598077 := bbase (se 3 (by rfl) ⟨487139, by rfl⟩ : syracuseStep 2598077 = 974279) (by norm_num)
theorem B2598101 : Blo 1731066 2598101 := bbase (se 7 (by rfl) ⟨30446, by rfl⟩ : syracuseStep 2598101 = 60893) (by norm_num)
theorem B2598125 : Blo 1731066 2598125 := bbase (se 3 (by rfl) ⟨487148, by rfl⟩ : syracuseStep 2598125 = 974297) (by norm_num)
theorem B2598149 : Blo 1731066 2598149 := bbase (se 4 (by rfl) ⟨243576, by rfl⟩ : syracuseStep 2598149 = 487153) (by norm_num)
theorem B8889605 : Blo 1731066 8889605 := bbase (se 4 (by rfl) ⟨833400, by rfl⟩ : syracuseStep 8889605 = 1666801) (by norm_num)
theorem B1778969 : Blo 1731066 1778969 := bbase (se 2 (by rfl) ⟨667113, by rfl⟩ : syracuseStep 1778969 = 1334227) (by norm_num)
theorem B2598173 : Blo 1731066 2598173 := bbase (se 3 (by rfl) ⟨487157, by rfl⟩ : syracuseStep 2598173 = 974315) (by norm_num)
theorem B3286325 : Blo 1731066 3286325 := bbase (se 5 (by rfl) ⟨154046, by rfl⟩ : syracuseStep 3286325 = 308093) (by norm_num)
theorem B2598197 : Blo 1731066 2598197 := bbase (se 5 (by rfl) ⟨121790, by rfl⟩ : syracuseStep 2598197 = 243581) (by norm_num)
theorem B2598221 : Blo 1731066 2598221 := bbase (se 3 (by rfl) ⟨487166, by rfl⟩ : syracuseStep 2598221 = 974333) (by norm_num)
theorem B2598245 : Blo 1731066 2598245 := bbase (se 4 (by rfl) ⟨243585, by rfl⟩ : syracuseStep 2598245 = 487171) (by norm_num)
theorem B2598269 : Blo 1731066 2598269 := bbase (se 3 (by rfl) ⟨487175, by rfl⟩ : syracuseStep 2598269 = 974351) (by norm_num)
theorem B6579589 : Blo 1731066 6579589 := bbase (se 4 (by rfl) ⟨616836, by rfl⟩ : syracuseStep 6579589 = 1233673) (by norm_num)
theorem B2598293 : Blo 1731066 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B4384165 : Blo 1731066 4384165 := bbase (se 4 (by rfl) ⟨411015, by rfl⟩ : syracuseStep 4384165 = 822031) (by norm_num)
theorem B2598317 : Blo 1731066 2598317 := bbase (se 3 (by rfl) ⟨487184, by rfl⟩ : syracuseStep 2598317 = 974369) (by norm_num)
theorem B3122621 : Blo 1731066 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B3286469 : Blo 1731066 3286469 := bbase (se 4 (by rfl) ⟨308106, by rfl⟩ : syracuseStep 3286469 = 616213) (by norm_num)
theorem B2598341 : Blo 1731066 2598341 := bbase (se 4 (by rfl) ⟨243594, by rfl⟩ : syracuseStep 2598341 = 487189) (by norm_num)
theorem B2598365 : Blo 1731066 2598365 := bbase (se 3 (by rfl) ⟨487193, by rfl⟩ : syracuseStep 2598365 = 974387) (by norm_num)
theorem B5842421 : Blo 1731066 5842421 := bbase (se 5 (by rfl) ⟨273863, by rfl⟩ : syracuseStep 5842421 = 547727) (by norm_num)
theorem B2598389 : Blo 1731066 2598389 := bbase (se 5 (by rfl) ⟨121799, by rfl⟩ : syracuseStep 2598389 = 243599) (by norm_num)
theorem B2598413 : Blo 1731066 2598413 := bbase (se 3 (by rfl) ⟨487202, by rfl⟩ : syracuseStep 2598413 = 974405) (by norm_num)
theorem B4384277 : Blo 1731066 4384277 := bbase (se 6 (by rfl) ⟨102756, by rfl⟩ : syracuseStep 4384277 = 205513) (by norm_num)
theorem B2598437 : Blo 1731066 2598437 := bbase (se 4 (by rfl) ⟨243603, by rfl⟩ : syracuseStep 2598437 = 487207) (by norm_num)
theorem B1975861 : Blo 1731066 1975861 := bbase (se 5 (by rfl) ⟨92618, by rfl⟩ : syracuseStep 1975861 = 185237) (by norm_num)
theorem B2598461 : Blo 1731066 2598461 := bbase (se 3 (by rfl) ⟨487211, by rfl⟩ : syracuseStep 2598461 = 974423) (by norm_num)
theorem B2598485 : Blo 1731066 2598485 := bbase (se 8 (by rfl) ⟨15225, by rfl⟩ : syracuseStep 2598485 = 30451) (by norm_num)
theorem B2598509 : Blo 1731066 2598509 := bbase (se 3 (by rfl) ⟨487220, by rfl⟩ : syracuseStep 2598509 = 974441) (by norm_num)
theorem B2598533 : Blo 1731066 2598533 := bbase (se 4 (by rfl) ⟨243612, by rfl⟩ : syracuseStep 2598533 = 487225) (by norm_num)
theorem B2598557 : Blo 1731066 2598557 := bbase (se 3 (by rfl) ⟨487229, by rfl⟩ : syracuseStep 2598557 = 974459) (by norm_num)
theorem B5547685 : Blo 1731066 5547685 := bbase (se 4 (by rfl) ⟨520095, by rfl⟩ : syracuseStep 5547685 = 1040191) (by norm_num)
theorem B2598581 : Blo 1731066 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B6579893 : Blo 1731066 6579893 := bbase (se 5 (by rfl) ⟨308432, by rfl⟩ : syracuseStep 6579893 = 616865) (by norm_num)
theorem B2598605 : Blo 1731066 2598605 := bbase (se 3 (by rfl) ⟨487238, by rfl⟩ : syracuseStep 2598605 = 974477) (by norm_num)
theorem B4384469 : Blo 1731066 4384469 := bbase (se 7 (by rfl) ⟨51380, by rfl⟩ : syracuseStep 4384469 = 102761) (by norm_num)
theorem B14804693 : Blo 1731066 14804693 := bbase (se 7 (by rfl) ⟨173492, by rfl⟩ : syracuseStep 14804693 = 346985) (by norm_num)
theorem B3286757 : Blo 1731066 3286757 := bbase (se 4 (by rfl) ⟨308133, by rfl⟩ : syracuseStep 3286757 = 616267) (by norm_num)
theorem B2598629 : Blo 1731066 2598629 := bbase (se 4 (by rfl) ⟨243621, by rfl⟩ : syracuseStep 2598629 = 487243) (by norm_num)
theorem B4933349 : Blo 1731066 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B2598653 : Blo 1731066 2598653 := bbase (se 3 (by rfl) ⟨487247, by rfl⟩ : syracuseStep 2598653 = 974495) (by norm_num)
theorem B2598677 : Blo 1731066 2598677 := bbase (se 6 (by rfl) ⟨60906, by rfl⟩ : syracuseStep 2598677 = 121813) (by norm_num)
theorem B2598701 : Blo 1731066 2598701 := bbase (se 3 (by rfl) ⟨487256, by rfl⟩ : syracuseStep 2598701 = 974513) (by norm_num)
theorem B4679477 : Blo 1731066 4679477 := bbase (se 5 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 4679477 = 438701) (by norm_num)
theorem B2598725 : Blo 1731066 2598725 := bbase (se 4 (by rfl) ⟨243630, by rfl⟩ : syracuseStep 2598725 = 487261) (by norm_num)
theorem B2598749 : Blo 1731066 2598749 := bbase (se 3 (by rfl) ⟨487265, by rfl⟩ : syracuseStep 2598749 = 974531) (by norm_num)
theorem B2598773 : Blo 1731066 2598773 := bbase (se 5 (by rfl) ⟨121817, by rfl⟩ : syracuseStep 2598773 = 243635) (by norm_num)
theorem B3286909 : Blo 1731066 3286909 := bbase (se 3 (by rfl) ⟨616295, by rfl⟩ : syracuseStep 3286909 = 1232591) (by norm_num)
theorem B2598797 : Blo 1731066 2598797 := bbase (se 3 (by rfl) ⟨487274, by rfl⟩ : syracuseStep 2598797 = 974549) (by norm_num)
theorem B5842853 : Blo 1731066 5842853 := bbase (se 4 (by rfl) ⟨547767, by rfl⟩ : syracuseStep 5842853 = 1095535) (by norm_num)
theorem B5547941 : Blo 1731066 5547941 := bbase (se 4 (by rfl) ⟨520119, by rfl⟩ : syracuseStep 5547941 = 1040239) (by norm_num)
theorem B2598821 : Blo 1731066 2598821 := bbase (se 4 (by rfl) ⟨243639, by rfl⟩ : syracuseStep 2598821 = 487279) (by norm_num)
theorem B2598845 : Blo 1731066 2598845 := bbase (se 3 (by rfl) ⟨487283, by rfl⟩ : syracuseStep 2598845 = 974567) (by norm_num)
theorem B2598869 : Blo 1731066 2598869 := bbase (se 7 (by rfl) ⟨30455, by rfl⟩ : syracuseStep 2598869 = 60911) (by norm_num)
theorem B2598893 : Blo 1731066 2598893 := bbase (se 3 (by rfl) ⟨487292, by rfl⟩ : syracuseStep 2598893 = 974585) (by norm_num)
theorem B8325125 : Blo 1731066 8325125 := bbase (se 4 (by rfl) ⟨780480, by rfl⟩ : syracuseStep 8325125 = 1560961) (by norm_num)
theorem B2598917 : Blo 1731066 2598917 := bbase (se 4 (by rfl) ⟨243648, by rfl⟩ : syracuseStep 2598917 = 487297) (by norm_num)
theorem B4057109 : Blo 1731066 4057109 := bbase (se 6 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 4057109 = 190177) (by norm_num)
theorem B2598941 : Blo 1731066 2598941 := bbase (se 3 (by rfl) ⟨487301, by rfl⟩ : syracuseStep 2598941 = 974603) (by norm_num)
theorem B4384813 : Blo 1731066 4384813 := bbase (se 3 (by rfl) ⟨822152, by rfl⟩ : syracuseStep 4384813 = 1644305) (by norm_num)
theorem B2598965 : Blo 1731066 2598965 := bbase (se 5 (by rfl) ⟨121826, by rfl⟩ : syracuseStep 2598965 = 243653) (by norm_num)
theorem B1755193 : Blo 1731066 1755193 := bbase (se 2 (by rfl) ⟨658197, by rfl⟩ : syracuseStep 1755193 = 1316395) (by norm_num)
theorem B2598989 : Blo 1731066 2598989 := bbase (se 3 (by rfl) ⟨487310, by rfl⟩ : syracuseStep 2598989 = 974621) (by norm_num)
theorem B2599013 : Blo 1731066 2599013 := bbase (se 4 (by rfl) ⟨243657, by rfl⟩ : syracuseStep 2599013 = 487315) (by norm_num)
theorem B2599037 : Blo 1731066 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B4933781 : Blo 1731066 4933781 := bbase (se 6 (by rfl) ⟨115635, by rfl⟩ : syracuseStep 4933781 = 231271) (by norm_num)
theorem B2599061 : Blo 1731066 2599061 := bbase (se 6 (by rfl) ⟨60915, by rfl⟩ : syracuseStep 2599061 = 121831) (by norm_num)
theorem B4384925 : Blo 1731066 4384925 := bbase (se 3 (by rfl) ⟨822173, by rfl⟩ : syracuseStep 4384925 = 1644347) (by norm_num)
theorem B1927325 : Blo 1731066 1927325 := bbase (se 3 (by rfl) ⟨361373, by rfl⟩ : syracuseStep 1927325 = 722747) (by norm_num)
theorem B3287213 : Blo 1731066 3287213 := bbase (se 3 (by rfl) ⟨616352, by rfl⟩ : syracuseStep 3287213 = 1232705) (by norm_num)
theorem B2599085 : Blo 1731066 2599085 := bbase (se 3 (by rfl) ⟨487328, by rfl⟩ : syracuseStep 2599085 = 974657) (by norm_num)
theorem B2599109 : Blo 1731066 2599109 := bbase (se 4 (by rfl) ⟨243666, by rfl⟩ : syracuseStep 2599109 = 487333) (by norm_num)
theorem B2599133 : Blo 1731066 2599133 := bbase (se 3 (by rfl) ⟨487337, by rfl⟩ : syracuseStep 2599133 = 974675) (by norm_num)
theorem B2599157 : Blo 1731066 2599157 := bbase (se 5 (by rfl) ⟨121835, by rfl⟩ : syracuseStep 2599157 = 243671) (by norm_num)
theorem B4679941 : Blo 1731066 4679941 := bbase (se 4 (by rfl) ⟨438744, by rfl⟩ : syracuseStep 4679941 = 877489) (by norm_num)
theorem B2599181 : Blo 1731066 2599181 := bbase (se 3 (by rfl) ⟨487346, by rfl⟩ : syracuseStep 2599181 = 974693) (by norm_num)
theorem B2599205 : Blo 1731066 2599205 := bbase (se 4 (by rfl) ⟨243675, by rfl⟩ : syracuseStep 2599205 = 487351) (by norm_num)
theorem B2599229 : Blo 1731066 2599229 := bbase (se 3 (by rfl) ⟨487355, by rfl⟩ : syracuseStep 2599229 = 974711) (by norm_num)
theorem B5843285 : Blo 1731066 5843285 := bbase (se 10 (by rfl) ⟨8559, by rfl⟩ : syracuseStep 5843285 = 17119) (by norm_num)
theorem B2599253 : Blo 1731066 2599253 := bbase (se 10 (by rfl) ⟨3807, by rfl⟩ : syracuseStep 2599253 = 7615) (by norm_num)
theorem B4385117 : Blo 1731066 4385117 := bbase (se 3 (by rfl) ⟨822209, by rfl⟩ : syracuseStep 4385117 = 1644419) (by norm_num)
theorem B1755497 : Blo 1731066 1755497 := bbase (se 2 (by rfl) ⟨658311, by rfl⟩ : syracuseStep 1755497 = 1316623) (by norm_num)
theorem B2599277 : Blo 1731066 2599277 := bbase (se 3 (by rfl) ⟨487364, by rfl⟩ : syracuseStep 2599277 = 974729) (by norm_num)
theorem B4442485 : Blo 1731066 4442485 := bbase (se 5 (by rfl) ⟨208241, by rfl⟩ : syracuseStep 4442485 = 416483) (by norm_num)
theorem B2599301 : Blo 1731066 2599301 := bbase (se 4 (by rfl) ⟨243684, by rfl⟩ : syracuseStep 2599301 = 487369) (by norm_num)
theorem B2599325 : Blo 1731066 2599325 := bbase (se 3 (by rfl) ⟨487373, by rfl⟩ : syracuseStep 2599325 = 974747) (by norm_num)
theorem B8767925 : Blo 1731066 8767925 := bbase (se 5 (by rfl) ⟨410996, by rfl⟩ : syracuseStep 8767925 = 821993) (by norm_num)
theorem B2599349 : Blo 1731066 2599349 := bbase (se 5 (by rfl) ⟨121844, by rfl⟩ : syracuseStep 2599349 = 243689) (by norm_num)
theorem B2599373 : Blo 1731066 2599373 := bbase (se 3 (by rfl) ⟨487382, by rfl⟩ : syracuseStep 2599373 = 974765) (by norm_num)
theorem B2599397 : Blo 1731066 2599397 := bbase (se 4 (by rfl) ⟨243693, by rfl⟩ : syracuseStep 2599397 = 487387) (by norm_num)
theorem B2599421 : Blo 1731066 2599421 := bbase (se 3 (by rfl) ⟨487391, by rfl⟩ : syracuseStep 2599421 = 974783) (by norm_num)
theorem B2599445 : Blo 1731066 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B2599469 : Blo 1731066 2599469 := bbase (se 3 (by rfl) ⟨487400, by rfl⟩ : syracuseStep 2599469 = 974801) (by norm_num)
theorem B2599493 : Blo 1731066 2599493 := bbase (se 4 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 2599493 = 487405) (by norm_num)
theorem B2599517 : Blo 1731066 2599517 := bbase (se 3 (by rfl) ⟨487409, by rfl⟩ : syracuseStep 2599517 = 974819) (by norm_num)
theorem B2108005 : Blo 1731066 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B1755757 : Blo 1731066 1755757 := bbase (se 3 (by rfl) ⟨329204, by rfl⟩ : syracuseStep 1755757 = 658409) (by norm_num)
theorem B2599541 : Blo 1731066 2599541 := bbase (se 5 (by rfl) ⟨121853, by rfl⟩ : syracuseStep 2599541 = 243707) (by norm_num)
theorem B2599565 : Blo 1731066 2599565 := bbase (se 3 (by rfl) ⟨487418, by rfl⟩ : syracuseStep 2599565 = 974837) (by norm_num)
theorem B2599589 : Blo 1731066 2599589 := bbase (se 4 (by rfl) ⟨243711, by rfl⟩ : syracuseStep 2599589 = 487423) (by norm_num)
theorem B4385461 : Blo 1731066 4385461 := bbase (se 5 (by rfl) ⟨205568, by rfl⟩ : syracuseStep 4385461 = 411137) (by norm_num)
theorem B5843717 : Blo 1731066 5843717 := bbase (se 4 (by rfl) ⟨547848, by rfl⟩ : syracuseStep 5843717 = 1095697) (by norm_num)
theorem B4385573 : Blo 1731066 4385573 := bbase (se 4 (by rfl) ⟨411147, by rfl⟩ : syracuseStep 4385573 = 822295) (by norm_num)
theorem B7400261 : Blo 1731066 7400261 := bbase (se 4 (by rfl) ⟨693774, by rfl⟩ : syracuseStep 7400261 = 1387549) (by norm_num)
theorem B4934533 : Blo 1731066 4934533 := bbase (se 4 (by rfl) ⟨462612, by rfl⟩ : syracuseStep 4934533 = 925225) (by norm_num)
theorem B3287965 : Blo 1731066 3287965 := bbase (se 3 (by rfl) ⟨616493, by rfl⟩ : syracuseStep 3287965 = 1232987) (by norm_num)
theorem B4385765 : Blo 1731066 4385765 := bbase (se 4 (by rfl) ⟨411165, by rfl⟩ : syracuseStep 4385765 = 822331) (by norm_num)
theorem B8432645 : Blo 1731066 8432645 := bbase (se 4 (by rfl) ⟨790560, by rfl⟩ : syracuseStep 8432645 = 1581121) (by norm_num)
theorem B3288109 : Blo 1731066 3288109 := bbase (se 3 (by rfl) ⟨616520, by rfl⟩ : syracuseStep 3288109 = 1233041) (by norm_num)
theorem B8891477 : Blo 1731066 8891477 := bbase (se 8 (by rfl) ⟨52098, by rfl⟩ : syracuseStep 8891477 = 104197) (by norm_num)
theorem B11103317 : Blo 1731066 11103317 := bbase (se 8 (by rfl) ⟨65058, by rfl⟩ : syracuseStep 11103317 = 130117) (by norm_num)
theorem B6327413 : Blo 1731066 6327413 := bbase (se 5 (by rfl) ⟨296597, by rfl⟩ : syracuseStep 6327413 = 593195) (by norm_num)
theorem B5844149 : Blo 1731066 5844149 := bbase (se 5 (by rfl) ⟨273944, by rfl⟩ : syracuseStep 5844149 = 547889) (by norm_num)
theorem B3288269 : Blo 1731066 3288269 := bbase (se 3 (by rfl) ⟨616550, by rfl⟩ : syracuseStep 3288269 = 1233101) (by norm_num)
theorem B5926117 : Blo 1731066 5926117 := bbase (se 4 (by rfl) ⟨555573, by rfl⟩ : syracuseStep 5926117 = 1111147) (by norm_num)
theorem B4386109 : Blo 1731066 4386109 := bbase (se 3 (by rfl) ⟨822395, by rfl⟩ : syracuseStep 4386109 = 1644791) (by norm_num)
theorem B3288413 : Blo 1731066 3288413 := bbase (se 3 (by rfl) ⟨616577, by rfl⟩ : syracuseStep 3288413 = 1233155) (by norm_num)
theorem B4386221 : Blo 1731066 4386221 := bbase (se 3 (by rfl) ⟨822416, by rfl⟩ : syracuseStep 4386221 = 1644833) (by norm_num)
theorem B10538453 : Blo 1731066 10538453 := bbase (se 7 (by rfl) ⟨123497, by rfl⟩ : syracuseStep 10538453 = 246995) (by norm_num)
theorem B3698149 : Blo 1731066 3698149 := bbase (se 4 (by rfl) ⟨346701, by rfl⟩ : syracuseStep 3698149 = 693403) (by norm_num)
theorem B5844581 : Blo 1731066 5844581 := bbase (se 4 (by rfl) ⟨547929, by rfl⟩ : syracuseStep 5844581 = 1095859) (by norm_num)
theorem B4386413 : Blo 1731066 4386413 := bbase (se 3 (by rfl) ⟨822452, by rfl⟩ : syracuseStep 4386413 = 1644905) (by norm_num)
theorem B3288701 : Blo 1731066 3288701 := bbase (se 3 (by rfl) ⟨616631, by rfl⟩ : syracuseStep 3288701 = 1233263) (by norm_num)
theorem B2190989 : Blo 1731066 2190989 := bbase (se 3 (by rfl) ⟨410810, by rfl⟩ : syracuseStep 2190989 = 821621) (by norm_num)
theorem B3894965 : Blo 1731066 3894965 := bbase (se 5 (by rfl) ⟨182576, by rfl⟩ : syracuseStep 3894965 = 365153) (by norm_num)
theorem B2191045 : Blo 1731066 2191045 := bbase (se 4 (by rfl) ⟨205410, by rfl⟩ : syracuseStep 2191045 = 410821) (by norm_num)
theorem B8769221 : Blo 1731066 8769221 := bbase (se 4 (by rfl) ⟨822114, by rfl⟩ : syracuseStep 8769221 = 1644229) (by norm_num)
theorem B3895037 : Blo 1731066 3895037 := bbase (se 3 (by rfl) ⟨730319, by rfl⟩ : syracuseStep 3895037 = 1460639) (by norm_num)
theorem B3510029 : Blo 1731066 3510029 := bbase (se 3 (by rfl) ⟨658130, by rfl⟩ : syracuseStep 3510029 = 1316261) (by norm_num)
theorem B3288853 : Blo 1731066 3288853 := bbase (se 6 (by rfl) ⟨77082, by rfl⟩ : syracuseStep 3288853 = 154165) (by norm_num)
theorem B2191141 : Blo 1731066 2191141 := bbase (se 4 (by rfl) ⟨205419, by rfl⟩ : syracuseStep 2191141 = 410839) (by norm_num)
theorem B7401253 : Blo 1731066 7401253 := bbase (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) (by norm_num)
theorem B3895109 : Blo 1731066 3895109 := bbase (se 4 (by rfl) ⟨365166, by rfl⟩ : syracuseStep 3895109 = 730333) (by norm_num)
theorem B3895181 : Blo 1731066 3895181 := bbase (se 3 (by rfl) ⟨730346, by rfl⟩ : syracuseStep 3895181 = 1460693) (by norm_num)
theorem B4386757 : Blo 1731066 4386757 := bbase (se 4 (by rfl) ⟨411258, by rfl⟩ : syracuseStep 4386757 = 822517) (by norm_num)
theorem B2191313 : Blo 1731066 2191313 := bbase (se 2 (by rfl) ⟨821742, by rfl⟩ : syracuseStep 2191313 = 1643485) (by norm_num)
theorem B3895253 : Blo 1731066 3895253 := bbase (se 7 (by rfl) ⟨45647, by rfl⟩ : syracuseStep 3895253 = 91295) (by norm_num)
theorem B2191369 : Blo 1731066 2191369 := bbase (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) (by norm_num)
theorem B5845013 : Blo 1731066 5845013 := bbase (se 6 (by rfl) ⟨136992, by rfl⟩ : syracuseStep 5845013 = 273985) (by norm_num)
theorem B3895325 : Blo 1731066 3895325 := bbase (se 3 (by rfl) ⟨730373, by rfl⟩ : syracuseStep 3895325 = 1460747) (by norm_num)
theorem B3289157 : Blo 1731066 3289157 := bbase (se 4 (by rfl) ⟨308358, by rfl⟩ : syracuseStep 3289157 = 616717) (by norm_num)
theorem B9859157 : Blo 1731066 9859157 := bbase (se 8 (by rfl) ⟨57768, by rfl⟩ : syracuseStep 9859157 = 115537) (by norm_num)
theorem B4681813 : Blo 1731066 4681813 := bbase (se 8 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 4681813 = 54865) (by norm_num)
theorem B3895397 : Blo 1731066 3895397 := bbase (se 4 (by rfl) ⟨365193, by rfl⟩ : syracuseStep 3895397 = 730387) (by norm_num)
theorem B2191465 : Blo 1731066 2191465 := bbase (se 2 (by rfl) ⟨821799, by rfl⟩ : syracuseStep 2191465 = 1643599) (by norm_num)
theorem B6574229 : Blo 1731066 6574229 := bbase (se 6 (by rfl) ⟨154083, by rfl⟩ : syracuseStep 6574229 = 308167) (by norm_num)
theorem B3895469 : Blo 1731066 3895469 := bbase (se 3 (by rfl) ⟨730400, by rfl⟩ : syracuseStep 3895469 = 1460801) (by norm_num)
theorem B3895541 : Blo 1731066 3895541 := bbase (se 5 (by rfl) ⟨182603, by rfl⟩ : syracuseStep 3895541 = 365207) (by norm_num)
theorem B2191637 : Blo 1731066 2191637 := bbase (se 6 (by rfl) ⟨51366, by rfl⟩ : syracuseStep 2191637 = 102733) (by norm_num)
theorem B3895613 : Blo 1731066 3895613 := bbase (se 3 (by rfl) ⟨730427, by rfl⟩ : syracuseStep 3895613 = 1460855) (by norm_num)
theorem B2191693 : Blo 1731066 2191693 := bbase (se 3 (by rfl) ⟨410942, by rfl⟩ : syracuseStep 2191693 = 821885) (by norm_num)
theorem B3699037 : Blo 1731066 3699037 := bbase (se 3 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 3699037 = 1387139) (by norm_num)
theorem B3510629 : Blo 1731066 3510629 := bbase (se 4 (by rfl) ⟨329121, by rfl⟩ : syracuseStep 3510629 = 658243) (by norm_num)
theorem B3895685 : Blo 1731066 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B2191789 : Blo 1731066 2191789 := bbase (se 3 (by rfl) ⟨410960, by rfl⟩ : syracuseStep 2191789 = 821921) (by norm_num)
theorem B6574517 : Blo 1731066 6574517 := bbase (se 5 (by rfl) ⟨308180, by rfl⟩ : syracuseStep 6574517 = 616361) (by norm_num)
theorem B5845445 : Blo 1731066 5845445 := bbase (se 4 (by rfl) ⟨548010, by rfl⟩ : syracuseStep 5845445 = 1096021) (by norm_num)
theorem B3895757 : Blo 1731066 3895757 := bbase (se 3 (by rfl) ⟨730454, by rfl⟩ : syracuseStep 3895757 = 1460909) (by norm_num)
theorem B3379709 : Blo 1731066 3379709 := bbase (se 3 (by rfl) ⟨633695, by rfl⟩ : syracuseStep 3379709 = 1267391) (by norm_num)
theorem B4682245 : Blo 1731066 4682245 := bbase (se 4 (by rfl) ⟨438960, by rfl⟩ : syracuseStep 4682245 = 877921) (by norm_num)
theorem B3895829 : Blo 1731066 3895829 := bbase (se 6 (by rfl) ⟨91308, by rfl⟩ : syracuseStep 3895829 = 182617) (by norm_num)
theorem B2191961 : Blo 1731066 2191961 := bbase (se 2 (by rfl) ⟨821985, by rfl⟩ : syracuseStep 2191961 = 1643971) (by norm_num)
theorem B3895901 : Blo 1731066 3895901 := bbase (se 3 (by rfl) ⟨730481, by rfl⟩ : syracuseStep 3895901 = 1460963) (by norm_num)
theorem B5550709 : Blo 1731066 5550709 := bbase (se 5 (by rfl) ⟨260189, by rfl⟩ : syracuseStep 5550709 = 520379) (by norm_num)
theorem B2192017 : Blo 1731066 2192017 := bbase (se 2 (by rfl) ⟨822006, by rfl⟩ : syracuseStep 2192017 = 1644013) (by norm_num)
theorem B28488341 : Blo 1731066 28488341 := bbase (se 6 (by rfl) ⟨667695, by rfl⟩ : syracuseStep 28488341 = 1335391) (by norm_num)
theorem B3895973 : Blo 1731066 3895973 := bbase (se 4 (by rfl) ⟨365247, by rfl⟩ : syracuseStep 3895973 = 730495) (by norm_num)
theorem B8327909 : Blo 1731066 8327909 := bbase (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) (by norm_num)
theorem B2921197 : Blo 1731066 2921197 := bbase (se 3 (by rfl) ⟨547724, by rfl⟩ : syracuseStep 2921197 = 1095449) (by norm_num)
theorem B3896045 : Blo 1731066 3896045 := bbase (se 3 (by rfl) ⟨730508, by rfl⟩ : syracuseStep 3896045 = 1461017) (by norm_num)
theorem B2192113 : Blo 1731066 2192113 := bbase (se 2 (by rfl) ⟨822042, by rfl⟩ : syracuseStep 2192113 = 1644085) (by norm_num)
theorem B3560221 : Blo 1731066 3560221 := bbase (se 3 (by rfl) ⟨667541, by rfl⟩ : syracuseStep 3560221 = 1335083) (by norm_num)
theorem B5927717 : Blo 1731066 5927717 := bbase (se 4 (by rfl) ⟨555723, by rfl⟩ : syracuseStep 5927717 = 1111447) (by norm_num)
theorem B3896117 : Blo 1731066 3896117 := bbase (se 5 (by rfl) ⟨182630, by rfl⟩ : syracuseStep 3896117 = 365261) (by norm_num)
theorem B3289909 : Blo 1731066 3289909 := bbase (se 5 (by rfl) ⟨154214, by rfl⟩ : syracuseStep 3289909 = 308429) (by norm_num)
theorem B2921285 : Blo 1731066 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B3699533 : Blo 1731066 3699533 := bbase (se 3 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 3699533 = 1387325) (by norm_num)
theorem B5845877 : Blo 1731066 5845877 := bbase (se 5 (by rfl) ⟨274025, by rfl⟩ : syracuseStep 5845877 = 548051) (by norm_num)
theorem B3896189 : Blo 1731066 3896189 := bbase (se 3 (by rfl) ⟨730535, by rfl⟩ : syracuseStep 3896189 = 1461071) (by norm_num)
theorem B2192285 : Blo 1731066 2192285 := bbase (se 3 (by rfl) ⟨411053, by rfl⟩ : syracuseStep 2192285 = 822107) (by norm_num)
theorem B3085237 : Blo 1731066 3085237 := bbase (se 5 (by rfl) ⟨144620, by rfl⟩ : syracuseStep 3085237 = 289241) (by norm_num)
theorem B2921413 : Blo 1731066 2921413 := bbase (se 4 (by rfl) ⟨273882, by rfl⟩ : syracuseStep 2921413 = 547765) (by norm_num)
theorem B3896261 : Blo 1731066 3896261 := bbase (se 4 (by rfl) ⟨365274, by rfl⟩ : syracuseStep 3896261 = 730549) (by norm_num)
theorem B3290053 : Blo 1731066 3290053 := bbase (se 4 (by rfl) ⟨308442, by rfl⟩ : syracuseStep 3290053 = 616885) (by norm_num)
theorem B2192341 : Blo 1731066 2192341 := bbase (se 7 (by rfl) ⟨25691, by rfl⟩ : syracuseStep 2192341 = 51383) (by norm_num)
theorem B8770517 : Blo 1731066 8770517 := bbase (se 7 (by rfl) ⟨102779, by rfl⟩ : syracuseStep 8770517 = 205559) (by norm_num)
theorem B5927909 : Blo 1731066 5927909 := bbase (se 4 (by rfl) ⟨555741, by rfl⟩ : syracuseStep 5927909 = 1111483) (by norm_num)
theorem B2773997 : Blo 1731066 2773997 := bbase (se 3 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 2773997 = 1040249) (by norm_num)
theorem B3896333 : Blo 1731066 3896333 := bbase (se 3 (by rfl) ⟨730562, by rfl⟩ : syracuseStep 3896333 = 1461125) (by norm_num)
theorem B2921501 : Blo 1731066 2921501 := bbase (se 3 (by rfl) ⟨547781, by rfl⟩ : syracuseStep 2921501 = 1095563) (by norm_num)
theorem B2192437 : Blo 1731066 2192437 := bbase (se 5 (by rfl) ⟨102770, by rfl⟩ : syracuseStep 2192437 = 205541) (by norm_num)
theorem B3896405 : Blo 1731066 3896405 := bbase (se 8 (by rfl) ⟨22830, by rfl⟩ : syracuseStep 3896405 = 45661) (by norm_num)
theorem B12178549 : Blo 1731066 12178549 := bbase (se 5 (by rfl) ⟨570869, by rfl⟩ : syracuseStep 12178549 = 1141739) (by norm_num)
theorem B7394453 : Blo 1731066 7394453 := bbase (se 6 (by rfl) ⟨173307, by rfl⟩ : syracuseStep 7394453 = 346615) (by norm_num)
theorem B2921629 : Blo 1731066 2921629 := bbase (se 3 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 2921629 = 1095611) (by norm_num)
theorem B3749021 : Blo 1731066 3749021 := bbase (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) (by norm_num)
theorem B3896477 : Blo 1731066 3896477 := bbase (se 3 (by rfl) ⟨730589, by rfl⟩ : syracuseStep 3896477 = 1461179) (by norm_num)
theorem B2774189 : Blo 1731066 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B19739861 : Blo 1731066 19739861 := bbase (se 7 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 19739861 = 462653) (by norm_num)
theorem B2192609 : Blo 1731066 2192609 := bbase (se 2 (by rfl) ⟨822228, by rfl⟩ : syracuseStep 2192609 = 1644457) (by norm_num)
theorem B3896549 : Blo 1731066 3896549 := bbase (se 4 (by rfl) ⟨365301, by rfl⟩ : syracuseStep 3896549 = 730603) (by norm_num)
theorem B2921717 : Blo 1731066 2921717 := bbase (se 5 (by rfl) ⟨136955, by rfl⟩ : syracuseStep 2921717 = 273911) (by norm_num)
theorem B2340085 : Blo 1731066 2340085 := bbase (se 5 (by rfl) ⟨109691, by rfl⟩ : syracuseStep 2340085 = 219383) (by norm_num)
theorem B2192665 : Blo 1731066 2192665 := bbase (se 2 (by rfl) ⟨822249, by rfl⟩ : syracuseStep 2192665 = 1644499) (by norm_num)
theorem B5846309 : Blo 1731066 5846309 := bbase (se 4 (by rfl) ⟨548091, by rfl⟩ : syracuseStep 5846309 = 1096183) (by norm_num)
theorem B3896621 : Blo 1731066 3896621 := bbase (se 3 (by rfl) ⟨730616, by rfl⟩ : syracuseStep 3896621 = 1461233) (by norm_num)
theorem B13153589 : Blo 1731066 13153589 := bbase (se 5 (by rfl) ⟨616574, by rfl⟩ : syracuseStep 13153589 = 1233149) (by norm_num)
theorem B1848673 : Blo 1731066 1848673 := bbase (se 2 (by rfl) ⟨693252, by rfl⟩ : syracuseStep 1848673 = 1386505) (by norm_num)
theorem B3749221 : Blo 1731066 3749221 := bbase (se 4 (by rfl) ⟨351489, by rfl⟩ : syracuseStep 3749221 = 702979) (by norm_num)
theorem B2921845 : Blo 1731066 2921845 := bbase (se 5 (by rfl) ⟨136961, by rfl⟩ : syracuseStep 2921845 = 273923) (by norm_num)
theorem B3896693 : Blo 1731066 3896693 := bbase (se 5 (by rfl) ⟨182657, by rfl⟩ : syracuseStep 3896693 = 365315) (by norm_num)
theorem B2192761 : Blo 1731066 2192761 := bbase (se 2 (by rfl) ⟨822285, by rfl⟩ : syracuseStep 2192761 = 1644571) (by norm_num)
theorem B4216237 : Blo 1731066 4216237 := bbase (se 3 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 4216237 = 1581089) (by norm_num)
theorem B3896765 : Blo 1731066 3896765 := bbase (se 3 (by rfl) ⟨730643, by rfl⟩ : syracuseStep 3896765 = 1461287) (by norm_num)
theorem B8435141 : Blo 1731066 8435141 := bbase (se 4 (by rfl) ⟨790794, by rfl⟩ : syracuseStep 8435141 = 1581589) (by norm_num)
theorem B2921933 : Blo 1731066 2921933 := bbase (se 3 (by rfl) ⟨547862, by rfl⟩ : syracuseStep 2921933 = 1095725) (by norm_num)
theorem B2373085 : Blo 1731066 2373085 := bbase (se 3 (by rfl) ⟨444953, by rfl⟩ : syracuseStep 2373085 = 889907) (by norm_num)
theorem B3896837 : Blo 1731066 3896837 := bbase (se 4 (by rfl) ⟨365328, by rfl⟩ : syracuseStep 3896837 = 730657) (by norm_num)
theorem B2192933 : Blo 1731066 2192933 := bbase (se 4 (by rfl) ⟨205587, by rfl⟩ : syracuseStep 2192933 = 411175) (by norm_num)
theorem B2922061 : Blo 1731066 2922061 := bbase (se 3 (by rfl) ⟨547886, by rfl⟩ : syracuseStep 2922061 = 1095773) (by norm_num)
theorem B3749453 : Blo 1731066 3749453 := bbase (se 3 (by rfl) ⟨703022, by rfl⟩ : syracuseStep 3749453 = 1406045) (by norm_num)
theorem B3896909 : Blo 1731066 3896909 := bbase (se 3 (by rfl) ⟨730670, by rfl⟩ : syracuseStep 3896909 = 1461341) (by norm_num)
theorem B25302613 : Blo 1731066 25302613 := bbase (se 8 (by rfl) ⟨148257, by rfl⟩ : syracuseStep 25302613 = 296515) (by norm_num)
theorem B6575701 : Blo 1731066 6575701 := bbase (se 8 (by rfl) ⟨38529, by rfl⟩ : syracuseStep 6575701 = 77059) (by norm_num)
theorem B2192989 : Blo 1731066 2192989 := bbase (se 3 (by rfl) ⟨411185, by rfl⟩ : syracuseStep 2192989 = 822371) (by norm_num)
theorem B3896981 : Blo 1731066 3896981 := bbase (se 6 (by rfl) ⟨91335, by rfl⟩ : syracuseStep 3896981 = 182671) (by norm_num)
theorem B2922149 : Blo 1731066 2922149 := bbase (se 4 (by rfl) ⟨273951, by rfl⟩ : syracuseStep 2922149 = 547903) (by norm_num)
theorem B3700397 : Blo 1731066 3700397 := bbase (se 3 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 3700397 = 1387649) (by norm_num)
theorem B2193085 : Blo 1731066 2193085 := bbase (se 3 (by rfl) ⟨411203, by rfl⟩ : syracuseStep 2193085 = 822407) (by norm_num)
theorem B13145813 : Blo 1731066 13145813 := bbase (se 7 (by rfl) ⟨154052, by rfl⟩ : syracuseStep 13145813 = 308105) (by norm_num)
theorem B5846741 : Blo 1731066 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B3897053 : Blo 1731066 3897053 := bbase (se 3 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 3897053 = 1461395) (by norm_num)
theorem B2963189 : Blo 1731066 2963189 := bbase (se 5 (by rfl) ⟨138899, by rfl⟩ : syracuseStep 2963189 = 277799) (by norm_num)
theorem B1849105 : Blo 1731066 1849105 := bbase (se 2 (by rfl) ⟨693414, by rfl⟩ : syracuseStep 1849105 = 1386829) (by norm_num)
theorem B2922277 : Blo 1731066 2922277 := bbase (se 4 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 2922277 = 547927) (by norm_num)
theorem B3897125 : Blo 1731066 3897125 := bbase (se 4 (by rfl) ⟨365355, by rfl⟩ : syracuseStep 3897125 = 730711) (by norm_num)
theorem B3700541 : Blo 1731066 3700541 := bbase (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) (by norm_num)
theorem B1947469 : Blo 1731066 1947469 := bbase (se 3 (by rfl) ⟨365150, by rfl⟩ : syracuseStep 1947469 = 730301) (by norm_num)
theorem B1849177 : Blo 1731066 1849177 := bbase (se 2 (by rfl) ⟨693441, by rfl⟩ : syracuseStep 1849177 = 1386883) (by norm_num)
theorem B2193257 : Blo 1731066 2193257 := bbase (se 2 (by rfl) ⟨822471, by rfl⟩ : syracuseStep 2193257 = 1644943) (by norm_num)
theorem B3897197 : Blo 1731066 3897197 := bbase (se 3 (by rfl) ⟨730724, by rfl⟩ : syracuseStep 3897197 = 1461449) (by norm_num)
theorem B1947505 : Blo 1731066 1947505 := bbase (se 2 (by rfl) ⟨730314, by rfl⟩ : syracuseStep 1947505 = 1460629) (by norm_num)
theorem B2922365 : Blo 1731066 2922365 := bbase (se 3 (by rfl) ⟨547943, by rfl⟩ : syracuseStep 2922365 = 1095887) (by norm_num)
theorem B6576005 : Blo 1731066 6576005 := bbase (se 4 (by rfl) ⟨616500, by rfl⟩ : syracuseStep 6576005 = 1233001) (by norm_num)
theorem B1947541 : Blo 1731066 1947541 := bbase (se 6 (by rfl) ⟨45645, by rfl⟩ : syracuseStep 1947541 = 91291) (by norm_num)
theorem B2193313 : Blo 1731066 2193313 := bbase (se 2 (by rfl) ⟨822492, by rfl⟩ : syracuseStep 2193313 = 1644985) (by norm_num)
theorem B3897269 : Blo 1731066 3897269 := bbase (se 5 (by rfl) ⟨182684, by rfl⟩ : syracuseStep 3897269 = 365369) (by norm_num)
theorem B1947577 : Blo 1731066 1947577 := bbase (se 2 (by rfl) ⟨730341, by rfl⟩ : syracuseStep 1947577 = 1460683) (by norm_num)
theorem B1947613 : Blo 1731066 1947613 := bbase (se 3 (by rfl) ⟨365177, by rfl⟩ : syracuseStep 1947613 = 730355) (by norm_num)
theorem B2922493 : Blo 1731066 2922493 := bbase (se 3 (by rfl) ⟨547967, by rfl⟩ : syracuseStep 2922493 = 1095935) (by norm_num)
theorem B3897341 : Blo 1731066 3897341 := bbase (se 3 (by rfl) ⟨730751, by rfl⟩ : syracuseStep 3897341 = 1461503) (by norm_num)
theorem B3512317 : Blo 1731066 3512317 := bbase (se 3 (by rfl) ⟨658559, by rfl⟩ : syracuseStep 3512317 = 1317119) (by norm_num)
theorem B1947649 : Blo 1731066 1947649 := bbase (se 2 (by rfl) ⟨730368, by rfl⟩ : syracuseStep 1947649 = 1460737) (by norm_num)
theorem B2193409 : Blo 1731066 2193409 := bbase (se 2 (by rfl) ⟨822528, by rfl⟩ : syracuseStep 2193409 = 1645057) (by norm_num)
theorem B1947685 : Blo 1731066 1947685 := bbase (se 4 (by rfl) ⟨182595, by rfl⟩ : syracuseStep 1947685 = 365191) (by norm_num)
theorem B4929589 : Blo 1731066 4929589 := bbase (se 5 (by rfl) ⟨231074, by rfl⟩ : syracuseStep 4929589 = 462149) (by norm_num)
theorem B15005749 : Blo 1731066 15005749 := bbase (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) (by norm_num)
theorem B3897413 : Blo 1731066 3897413 := bbase (se 4 (by rfl) ⟨365382, by rfl⟩ : syracuseStep 3897413 = 730765) (by norm_num)
theorem B4683845 : Blo 1731066 4683845 := bbase (se 4 (by rfl) ⟨439110, by rfl⟩ : syracuseStep 4683845 = 878221) (by norm_num)
theorem B1947721 : Blo 1731066 1947721 := bbase (se 2 (by rfl) ⟨730395, by rfl⟩ : syracuseStep 1947721 = 1460791) (by norm_num)
theorem B2922581 : Blo 1731066 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B2340949 : Blo 1731066 2340949 := bbase (se 8 (by rfl) ⟨13716, by rfl⟩ : syracuseStep 2340949 = 27433) (by norm_num)
theorem B2283617 : Blo 1731066 2283617 := bbase (se 2 (by rfl) ⟨856356, by rfl⟩ : syracuseStep 2283617 = 1712713) (by norm_num)
theorem B8321125 : Blo 1731066 8321125 := bbase (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) (by norm_num)
theorem B1947757 : Blo 1731066 1947757 := bbase (se 3 (by rfl) ⟨365204, by rfl⟩ : syracuseStep 1947757 = 730409) (by norm_num)
theorem B5847173 : Blo 1731066 5847173 := bbase (se 4 (by rfl) ⟨548172, by rfl⟩ : syracuseStep 5847173 = 1096345) (by norm_num)
theorem B3897485 : Blo 1731066 3897485 := bbase (se 3 (by rfl) ⟨730778, by rfl⟩ : syracuseStep 3897485 = 1461557) (by norm_num)
theorem B1947793 : Blo 1731066 1947793 := bbase (se 2 (by rfl) ⟨730422, by rfl⟩ : syracuseStep 1947793 = 1460845) (by norm_num)
theorem B4159669 : Blo 1731066 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B1947829 : Blo 1731066 1947829 := bbase (se 5 (by rfl) ⟨91304, by rfl⟩ : syracuseStep 1947829 = 182609) (by norm_num)
theorem B1849549 : Blo 1731066 1849549 := bbase (se 3 (by rfl) ⟨346790, by rfl⟩ : syracuseStep 1849549 = 693581) (by norm_num)
theorem B2922709 : Blo 1731066 2922709 := bbase (se 7 (by rfl) ⟨34250, by rfl⟩ : syracuseStep 2922709 = 68501) (by norm_num)
theorem B3897557 : Blo 1731066 3897557 := bbase (se 7 (by rfl) ⟨45674, by rfl⟩ : syracuseStep 3897557 = 91349) (by norm_num)
theorem B1947865 : Blo 1731066 1947865 := bbase (se 2 (by rfl) ⟨730449, by rfl⟩ : syracuseStep 1947865 = 1460899) (by norm_num)
theorem B8771813 : Blo 1731066 8771813 := bbase (se 4 (by rfl) ⟨822357, by rfl⟩ : syracuseStep 8771813 = 1644715) (by norm_num)
theorem B9861365 : Blo 1731066 9861365 := bbase (se 5 (by rfl) ⟨462251, by rfl⟩ : syracuseStep 9861365 = 924503) (by norm_num)
theorem B1947901 : Blo 1731066 1947901 := bbase (se 3 (by rfl) ⟨365231, by rfl⟩ : syracuseStep 1947901 = 730463) (by norm_num)
theorem B4159765 : Blo 1731066 4159765 := bbase (se 6 (by rfl) ⟨97494, by rfl⟩ : syracuseStep 4159765 = 194989) (by norm_num)
theorem B3897629 : Blo 1731066 3897629 := bbase (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) (by norm_num)
theorem B1947937 : Blo 1731066 1947937 := bbase (se 2 (by rfl) ⟨730476, by rfl⟩ : syracuseStep 1947937 = 1460953) (by norm_num)
theorem B2922797 : Blo 1731066 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B1947973 : Blo 1731066 1947973 := bbase (se 4 (by rfl) ⟨182622, by rfl⟩ : syracuseStep 1947973 = 365245) (by norm_num)
theorem B16644437 : Blo 1731066 16644437 := bbase (se 10 (by rfl) ⟨24381, by rfl⟩ : syracuseStep 16644437 = 48763) (by norm_num)
theorem B3897701 : Blo 1731066 3897701 := bbase (se 4 (by rfl) ⟨365409, by rfl⟩ : syracuseStep 3897701 = 730819) (by norm_num)
theorem B1948009 : Blo 1731066 1948009 := bbase (se 2 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 1948009 = 1461007) (by norm_num)
theorem B1948045 : Blo 1731066 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B2922925 : Blo 1731066 2922925 := bbase (se 3 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 2922925 = 1096097) (by norm_num)
theorem B1948081 : Blo 1731066 1948081 := bbase (se 2 (by rfl) ⟨730530, by rfl⟩ : syracuseStep 1948081 = 1461061) (by norm_num)
theorem B3897773 : Blo 1731066 3897773 := bbase (se 3 (by rfl) ⟨730832, by rfl⟩ : syracuseStep 3897773 = 1461665) (by norm_num)
theorem B4159957 : Blo 1731066 4159957 := bbase (se 7 (by rfl) ⟨48749, by rfl⟩ : syracuseStep 4159957 = 97499) (by norm_num)
theorem B1948117 : Blo 1731066 1948117 := bbase (se 7 (by rfl) ⟨22829, by rfl⟩ : syracuseStep 1948117 = 45659) (by norm_num)
theorem B3897845 : Blo 1731066 3897845 := bbase (se 5 (by rfl) ⟨182711, by rfl⟩ : syracuseStep 3897845 = 365423) (by norm_num)
theorem B1948153 : Blo 1731066 1948153 := bbase (se 2 (by rfl) ⟨730557, by rfl⟩ : syracuseStep 1948153 = 1461115) (by norm_num)
theorem B2923013 : Blo 1731066 2923013 := bbase (se 4 (by rfl) ⟨274032, by rfl⟩ : syracuseStep 2923013 = 548065) (by norm_num)
theorem B1948189 : Blo 1731066 1948189 := bbase (se 3 (by rfl) ⟨365285, by rfl⟩ : syracuseStep 1948189 = 730571) (by norm_num)
theorem B3701285 : Blo 1731066 3701285 := bbase (se 4 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 3701285 = 693991) (by norm_num)
theorem B5847605 : Blo 1731066 5847605 := bbase (se 5 (by rfl) ⟨274106, by rfl⟩ : syracuseStep 5847605 = 548213) (by norm_num)
theorem B3897917 : Blo 1731066 3897917 := bbase (se 3 (by rfl) ⟨730859, by rfl⟩ : syracuseStep 3897917 = 1461719) (by norm_num)
theorem B1948225 : Blo 1731066 1948225 := bbase (se 2 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 1948225 = 1461169) (by norm_num)
theorem B1849925 : Blo 1731066 1849925 := bbase (se 4 (by rfl) ⟨173430, by rfl⟩ : syracuseStep 1849925 = 346861) (by norm_num)
theorem B2775637 : Blo 1731066 2775637 := bbase (se 8 (by rfl) ⟨16263, by rfl⟩ : syracuseStep 2775637 = 32527) (by norm_num)
theorem B1948261 : Blo 1731066 1948261 := bbase (se 4 (by rfl) ⟨182649, by rfl⟩ : syracuseStep 1948261 = 365299) (by norm_num)
theorem B4274797 : Blo 1731066 4274797 := bbase (se 3 (by rfl) ⟨801524, by rfl⟩ : syracuseStep 4274797 = 1603049) (by norm_num)
theorem B8764037 : Blo 1731066 8764037 := bbase (se 4 (by rfl) ⟨821628, by rfl⟩ : syracuseStep 8764037 = 1643257) (by norm_num)
theorem B2923141 : Blo 1731066 2923141 := bbase (se 4 (by rfl) ⟨274044, by rfl⟩ : syracuseStep 2923141 = 548089) (by norm_num)
theorem B3897989 : Blo 1731066 3897989 := bbase (se 4 (by rfl) ⟨365436, by rfl⟩ : syracuseStep 3897989 = 730873) (by norm_num)
theorem B1948297 : Blo 1731066 1948297 := bbase (se 2 (by rfl) ⟨730611, by rfl⟩ : syracuseStep 1948297 = 1461223) (by norm_num)
theorem B1849997 : Blo 1731066 1849997 := bbase (se 3 (by rfl) ⟨346874, by rfl⟩ : syracuseStep 1849997 = 693749) (by norm_num)
theorem B1948333 : Blo 1731066 1948333 := bbase (se 3 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 1948333 = 730625) (by norm_num)
theorem B3898061 : Blo 1731066 3898061 := bbase (se 3 (by rfl) ⟨730886, by rfl⟩ : syracuseStep 3898061 = 1461773) (by norm_num)
theorem B1948369 : Blo 1731066 1948369 := bbase (se 2 (by rfl) ⟨730638, by rfl⟩ : syracuseStep 1948369 = 1461277) (by norm_num)
theorem B2923229 : Blo 1731066 2923229 := bbase (se 3 (by rfl) ⟨548105, by rfl⟩ : syracuseStep 2923229 = 1096211) (by norm_num)
theorem B1948405 : Blo 1731066 1948405 := bbase (se 5 (by rfl) ⟨91331, by rfl⟩ : syracuseStep 1948405 = 182663) (by norm_num)
theorem B3898133 : Blo 1731066 3898133 := bbase (se 6 (by rfl) ⟨91362, by rfl⟩ : syracuseStep 3898133 = 182725) (by norm_num)
theorem B1948441 : Blo 1731066 1948441 := bbase (se 2 (by rfl) ⟨730665, by rfl⟩ : syracuseStep 1948441 = 1461331) (by norm_num)
theorem B4160285 : Blo 1731066 4160285 := bbase (se 3 (by rfl) ⟨780053, by rfl⟩ : syracuseStep 4160285 = 1560107) (by norm_num)
theorem B2030393 : Blo 1731066 2030393 := bbase (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) (by norm_num)
theorem B1948477 : Blo 1731066 1948477 := bbase (se 3 (by rfl) ⟨365339, by rfl⟩ : syracuseStep 1948477 = 730679) (by norm_num)
theorem B1850185 : Blo 1731066 1850185 := bbase (se 2 (by rfl) ⟨693819, by rfl⟩ : syracuseStep 1850185 = 1387639) (by norm_num)
theorem B2923357 : Blo 1731066 2923357 := bbase (se 3 (by rfl) ⟨548129, by rfl⟩ : syracuseStep 2923357 = 1096259) (by norm_num)
theorem B3898205 : Blo 1731066 3898205 := bbase (se 3 (by rfl) ⟨730913, by rfl⟩ : syracuseStep 3898205 = 1461827) (by norm_num)
theorem B1948513 : Blo 1731066 1948513 := bbase (se 2 (by rfl) ⟨730692, by rfl⟩ : syracuseStep 1948513 = 1461385) (by norm_num)
theorem B2284409 : Blo 1731066 2284409 := bbase (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) (by norm_num)
theorem B1948549 : Blo 1731066 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B3898277 : Blo 1731066 3898277 := bbase (se 4 (by rfl) ⟨365463, by rfl⟩ : syracuseStep 3898277 = 730927) (by norm_num)
theorem B1948585 : Blo 1731066 1948585 := bbase (se 2 (by rfl) ⟨730719, by rfl⟩ : syracuseStep 1948585 = 1461439) (by norm_num)
theorem B2923445 : Blo 1731066 2923445 := bbase (se 5 (by rfl) ⟨137036, by rfl⟩ : syracuseStep 2923445 = 274073) (by norm_num)
theorem B1948621 : Blo 1731066 1948621 := bbase (se 3 (by rfl) ⟨365366, by rfl⟩ : syracuseStep 1948621 = 730733) (by norm_num)
theorem B5848037 : Blo 1731066 5848037 := bbase (se 4 (by rfl) ⟨548253, by rfl⟩ : syracuseStep 5848037 = 1096507) (by norm_num)
theorem B3898349 : Blo 1731066 3898349 := bbase (se 3 (by rfl) ⟨730940, by rfl⟩ : syracuseStep 3898349 = 1461881) (by norm_num)
theorem B1948657 : Blo 1731066 1948657 := bbase (se 2 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 1948657 = 1461493) (by norm_num)
theorem B1850369 : Blo 1731066 1850369 := bbase (se 2 (by rfl) ⟨693888, by rfl⟩ : syracuseStep 1850369 = 1387777) (by norm_num)
theorem B1948693 : Blo 1731066 1948693 := bbase (se 6 (by rfl) ⟨45672, by rfl⟩ : syracuseStep 1948693 = 91345) (by norm_num)
theorem B2923573 : Blo 1731066 2923573 := bbase (se 5 (by rfl) ⟨137042, by rfl⟩ : syracuseStep 2923573 = 274085) (by norm_num)
theorem B3898421 : Blo 1731066 3898421 := bbase (se 5 (by rfl) ⟨182738, by rfl⟩ : syracuseStep 3898421 = 365477) (by norm_num)
theorem B1948729 : Blo 1731066 1948729 := bbase (se 2 (by rfl) ⟨730773, by rfl⟩ : syracuseStep 1948729 = 1461547) (by norm_num)
theorem B6241349 : Blo 1731066 6241349 := bbase (se 4 (by rfl) ⟨585126, by rfl⟩ : syracuseStep 6241349 = 1170253) (by norm_num)
theorem B57736277 : Blo 1731066 57736277 := bbase (se 8 (by rfl) ⟨338298, by rfl⟩ : syracuseStep 57736277 = 676597) (by norm_num)
theorem B10681429 : Blo 1731066 10681429 := bbase (se 8 (by rfl) ⟨62586, by rfl⟩ : syracuseStep 10681429 = 125173) (by norm_num)
theorem B1948765 : Blo 1731066 1948765 := bbase (se 3 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 1948765 = 730787) (by norm_num)
theorem B3898493 : Blo 1731066 3898493 := bbase (se 3 (by rfl) ⟨730967, by rfl⟩ : syracuseStep 3898493 = 1461935) (by norm_num)
theorem B1948801 : Blo 1731066 1948801 := bbase (se 2 (by rfl) ⟨730800, by rfl⟩ : syracuseStep 1948801 = 1461601) (by norm_num)
theorem B2923661 : Blo 1731066 2923661 := bbase (se 3 (by rfl) ⟨548186, by rfl⟩ : syracuseStep 2923661 = 1096373) (by norm_num)
theorem B1948837 : Blo 1731066 1948837 := bbase (se 4 (by rfl) ⟨182703, by rfl⟩ : syracuseStep 1948837 = 365407) (by norm_num)
theorem B4381877 : Blo 1731066 4381877 := bbase (se 5 (by rfl) ⟨205400, by rfl⟩ : syracuseStep 4381877 = 410801) (by norm_num)
theorem B3898565 : Blo 1731066 3898565 := bbase (se 4 (by rfl) ⟨365490, by rfl⟩ : syracuseStep 3898565 = 730981) (by norm_num)
theorem B1948873 : Blo 1731066 1948873 := bbase (se 2 (by rfl) ⟨730827, by rfl⟩ : syracuseStep 1948873 = 1461655) (by norm_num)
theorem B4160717 : Blo 1731066 4160717 := bbase (se 3 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 4160717 = 1560269) (by norm_num)
theorem B1948909 : Blo 1731066 1948909 := bbase (se 3 (by rfl) ⟨365420, by rfl⟩ : syracuseStep 1948909 = 730841) (by norm_num)
theorem B2923789 : Blo 1731066 2923789 := bbase (se 3 (by rfl) ⟨548210, by rfl⟩ : syracuseStep 2923789 = 1096421) (by norm_num)
theorem B3898637 : Blo 1731066 3898637 := bbase (se 3 (by rfl) ⟨730994, by rfl⟩ : syracuseStep 3898637 = 1461989) (by norm_num)
theorem B1948945 : Blo 1731066 1948945 := bbase (se 2 (by rfl) ⟨730854, by rfl⟩ : syracuseStep 1948945 = 1461709) (by norm_num)
theorem B7019797 : Blo 1731066 7019797 := bbase (se 6 (by rfl) ⟨164526, by rfl⟩ : syracuseStep 7019797 = 329053) (by norm_num)
theorem B1948981 : Blo 1731066 1948981 := bbase (se 5 (by rfl) ⟨91358, by rfl⟩ : syracuseStep 1948981 = 182717) (by norm_num)
theorem B3898709 : Blo 1731066 3898709 := bbase (se 11 (by rfl) ⟨2855, by rfl⟩ : syracuseStep 3898709 = 5711) (by norm_num)
theorem B1949017 : Blo 1731066 1949017 := bbase (se 2 (by rfl) ⟨730881, by rfl⟩ : syracuseStep 1949017 = 1461763) (by norm_num)
theorem B2923877 : Blo 1731066 2923877 := bbase (se 4 (by rfl) ⟨274113, by rfl⟩ : syracuseStep 2923877 = 548227) (by norm_num)
theorem B1949053 : Blo 1731066 1949053 := bbase (se 3 (by rfl) ⟨365447, by rfl⟩ : syracuseStep 1949053 = 730895) (by norm_num)
theorem B2252161 : Blo 1731066 2252161 := bbase (se 2 (by rfl) ⟨844560, by rfl⟩ : syracuseStep 2252161 = 1689121) (by norm_num)
theorem B5848469 : Blo 1731066 5848469 := bbase (se 6 (by rfl) ⟨137073, by rfl⟩ : syracuseStep 5848469 = 274147) (by norm_num)
theorem B3898781 : Blo 1731066 3898781 := bbase (se 3 (by rfl) ⟨731021, by rfl⟩ : syracuseStep 3898781 = 1462043) (by norm_num)
theorem B1949089 : Blo 1731066 1949089 := bbase (se 2 (by rfl) ⟨730908, by rfl⟩ : syracuseStep 1949089 = 1461817) (by norm_num)
theorem B1949125 : Blo 1731066 1949125 := bbase (se 4 (by rfl) ⟨182730, by rfl⟩ : syracuseStep 1949125 = 365461) (by norm_num)
theorem B2465245 : Blo 1731066 2465245 := bbase (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) (by norm_num)
theorem B2924005 : Blo 1731066 2924005 := bbase (se 4 (by rfl) ⟨274125, by rfl⟩ : syracuseStep 2924005 = 548251) (by norm_num)
theorem B3898853 : Blo 1731066 3898853 := bbase (se 4 (by rfl) ⟨365517, by rfl⟩ : syracuseStep 3898853 = 731035) (by norm_num)
theorem B1949161 : Blo 1731066 1949161 := bbase (se 2 (by rfl) ⟨730935, by rfl⟩ : syracuseStep 1949161 = 1461871) (by norm_num)
theorem B8773109 : Blo 1731066 8773109 := bbase (se 5 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 8773109 = 822479) (by norm_num)
theorem B4382221 : Blo 1731066 4382221 := bbase (se 3 (by rfl) ⟨821666, by rfl⟩ : syracuseStep 4382221 = 1643333) (by norm_num)
theorem B3120653 : Blo 1731066 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B1949197 : Blo 1731066 1949197 := bbase (se 3 (by rfl) ⟨365474, by rfl⟩ : syracuseStep 1949197 = 730949) (by norm_num)
theorem B4931093 : Blo 1731066 4931093 := bbase (se 6 (by rfl) ⟨115572, by rfl⟩ : syracuseStep 4931093 = 231145) (by norm_num)
theorem B4161053 : Blo 1731066 4161053 := bbase (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) (by norm_num)
theorem B3898925 : Blo 1731066 3898925 := bbase (se 3 (by rfl) ⟨731048, by rfl⟩ : syracuseStep 3898925 = 1462097) (by norm_num)
theorem B1949233 : Blo 1731066 1949233 := bbase (se 2 (by rfl) ⟨730962, by rfl⟩ : syracuseStep 1949233 = 1461925) (by norm_num)
theorem B2924093 : Blo 1731066 2924093 := bbase (se 3 (by rfl) ⟨548267, by rfl⟩ : syracuseStep 2924093 = 1096535) (by norm_num)
theorem B1949269 : Blo 1731066 1949269 := bbase (se 8 (by rfl) ⟨11421, by rfl⟩ : syracuseStep 1949269 = 22843) (by norm_num)
theorem B3898997 : Blo 1731066 3898997 := bbase (se 5 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 3898997 = 365531) (by norm_num)
theorem B1949305 : Blo 1731066 1949305 := bbase (se 2 (by rfl) ⟨730989, by rfl⟩ : syracuseStep 1949305 = 1461979) (by norm_num)
theorem B4382333 : Blo 1731066 4382333 := bbase (se 3 (by rfl) ⟨821687, by rfl⟩ : syracuseStep 4382333 = 1643375) (by norm_num)
theorem B1949341 : Blo 1731066 1949341 := bbase (se 3 (by rfl) ⟨365501, by rfl⟩ : syracuseStep 1949341 = 731003) (by norm_num)
theorem B2924221 : Blo 1731066 2924221 := bbase (se 3 (by rfl) ⟨548291, by rfl⟩ : syracuseStep 2924221 = 1096583) (by norm_num)
theorem B3899069 : Blo 1731066 3899069 := bbase (se 3 (by rfl) ⟨731075, by rfl⟩ : syracuseStep 3899069 = 1462151) (by norm_num)
theorem B1949377 : Blo 1731066 1949377 := bbase (se 2 (by rfl) ⟨731016, by rfl⟩ : syracuseStep 1949377 = 1462033) (by norm_num)
theorem B1949413 : Blo 1731066 1949413 := bbase (se 4 (by rfl) ⟨182757, by rfl⟩ : syracuseStep 1949413 = 365515) (by norm_num)
theorem B2596613 : Blo 1731066 2596613 := bbase (se 4 (by rfl) ⟨243432, by rfl⟩ : syracuseStep 2596613 = 486865) (by norm_num)
theorem B3899141 : Blo 1731066 3899141 := bbase (se 4 (by rfl) ⟨365544, by rfl⟩ : syracuseStep 3899141 = 731089) (by norm_num)
theorem B1949449 : Blo 1731066 1949449 := bbase (se 2 (by rfl) ⟨731043, by rfl⟩ : syracuseStep 1949449 = 1462087) (by norm_num)
theorem B14802709 : Blo 1731066 14802709 := bbase (se 6 (by rfl) ⟨346938, by rfl⟩ : syracuseStep 14802709 = 693877) (by norm_num)
theorem B2924309 : Blo 1731066 2924309 := bbase (se 6 (by rfl) ⟨68538, by rfl⟩ : syracuseStep 2924309 = 137077) (by norm_num)
theorem B2596637 : Blo 1731066 2596637 := bbase (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) (by norm_num)
theorem B2465581 : Blo 1731066 2465581 := bbase (se 3 (by rfl) ⟨462296, by rfl⟩ : syracuseStep 2465581 = 924593) (by norm_num)
theorem B1949485 : Blo 1731066 1949485 := bbase (se 3 (by rfl) ⟨365528, by rfl⟩ : syracuseStep 1949485 = 731057) (by norm_num)
theorem B2596661 : Blo 1731066 2596661 := bbase (se 5 (by rfl) ⟨121718, by rfl⟩ : syracuseStep 2596661 = 243437) (by norm_num)
theorem B4382525 : Blo 1731066 4382525 := bbase (se 3 (by rfl) ⟨821723, by rfl⟩ : syracuseStep 4382525 = 1643447) (by norm_num)
theorem B5922629 : Blo 1731066 5922629 := bbase (se 4 (by rfl) ⟨555246, by rfl⟩ : syracuseStep 5922629 = 1110493) (by norm_num)
theorem B5848901 : Blo 1731066 5848901 := bbase (se 4 (by rfl) ⟨548334, by rfl⟩ : syracuseStep 5848901 = 1096669) (by norm_num)
theorem B2596685 : Blo 1731066 2596685 := bbase (se 3 (by rfl) ⟨486878, by rfl⟩ : syracuseStep 2596685 = 973757) (by norm_num)
theorem B3899213 : Blo 1731066 3899213 := bbase (se 3 (by rfl) ⟨731102, by rfl⟩ : syracuseStep 3899213 = 1462205) (by norm_num)
theorem B1949521 : Blo 1731066 1949521 := bbase (se 2 (by rfl) ⟨731070, by rfl⟩ : syracuseStep 1949521 = 1462141) (by norm_num)
theorem B2596709 : Blo 1731066 2596709 := bbase (se 4 (by rfl) ⟨243441, by rfl⟩ : syracuseStep 2596709 = 486883) (by norm_num)
theorem B2080613 : Blo 1731066 2080613 := bbase (se 4 (by rfl) ⟨195057, by rfl⟩ : syracuseStep 2080613 = 390115) (by norm_num)
theorem B1949557 : Blo 1731066 1949557 := bbase (se 5 (by rfl) ⟨91385, by rfl⟩ : syracuseStep 1949557 = 182771) (by norm_num)
theorem B2596733 : Blo 1731066 2596733 := bbase (se 3 (by rfl) ⟨486887, by rfl⟩ : syracuseStep 2596733 = 973775) (by norm_num)
theorem B2596757 : Blo 1731066 2596757 := bbase (se 6 (by rfl) ⟨60861, by rfl⟩ : syracuseStep 2596757 = 121723) (by norm_num)
theorem B8765333 : Blo 1731066 8765333 := bbase (se 6 (by rfl) ⟨205437, by rfl⟩ : syracuseStep 8765333 = 410875) (by norm_num)
theorem B2924437 : Blo 1731066 2924437 := bbase (se 6 (by rfl) ⟨68541, by rfl⟩ : syracuseStep 2924437 = 137083) (by norm_num)
theorem B3899285 : Blo 1731066 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1949593 : Blo 1731066 1949593 := bbase (se 2 (by rfl) ⟨731097, by rfl⟩ : syracuseStep 1949593 = 1462195) (by norm_num)
theorem B2596781 : Blo 1731066 2596781 := bbase (se 3 (by rfl) ⟨486896, by rfl⟩ : syracuseStep 2596781 = 973793) (by norm_num)
theorem B1949629 : Blo 1731066 1949629 := bbase (se 3 (by rfl) ⟨365555, by rfl⟩ : syracuseStep 1949629 = 731111) (by norm_num)
theorem B2596805 : Blo 1731066 2596805 := bbase (se 4 (by rfl) ⟨243450, by rfl⟩ : syracuseStep 2596805 = 486901) (by norm_num)
theorem B6578117 : Blo 1731066 6578117 := bbase (se 4 (by rfl) ⟨616698, by rfl⟩ : syracuseStep 6578117 = 1233397) (by norm_num)
theorem B2596829 : Blo 1731066 2596829 := bbase (se 3 (by rfl) ⟨486905, by rfl⟩ : syracuseStep 2596829 = 973811) (by norm_num)
theorem B3899357 : Blo 1731066 3899357 := bbase (se 3 (by rfl) ⟨731129, by rfl⟩ : syracuseStep 3899357 = 1462259) (by norm_num)
theorem B1949665 : Blo 1731066 1949665 := bbase (se 2 (by rfl) ⟨731124, by rfl⟩ : syracuseStep 1949665 = 1462249) (by norm_num)
theorem B1974245 : Blo 1731066 1974245 := bbase (se 4 (by rfl) ⟨185085, by rfl⟩ : syracuseStep 1974245 = 370171) (by norm_num)
theorem B2924525 : Blo 1731066 2924525 := bbase (se 3 (by rfl) ⟨548348, by rfl⟩ : syracuseStep 2924525 = 1096697) (by norm_num)
theorem B2596853 : Blo 1731066 2596853 := bbase (se 5 (by rfl) ⟨121727, by rfl⟩ : syracuseStep 2596853 = 243455) (by norm_num)
theorem B2596865 : Blo 1731066 2596865 := bstep (se 2 (by rfl) ⟨973824, by rfl⟩ : syracuseStep 2596865 = 1947649) B1947649
theorem B2924545 : Blo 1731066 2924545 := bstep (se 2 (by rfl) ⟨1096704, by rfl⟩ : syracuseStep 2924545 = 2193409) B2193409
theorem B22487053 : Blo 1731066 22487053 := bstep (se 3 (by rfl) ⟨4216322, by rfl⟩ : syracuseStep 22487053 = 8432645) B8432645
theorem B2596883 : Blo 1731066 2596883 := bstep (se 1 (by rfl) ⟨1947662, by rfl⟩ : syracuseStep 2596883 = 3895325) B3895325
theorem B2596913 : Blo 1731066 2596913 := bstep (se 2 (by rfl) ⟨973842, by rfl⟩ : syracuseStep 2596913 = 1947685) B1947685
theorem B2596931 : Blo 1731066 2596931 := bstep (se 1 (by rfl) ⟨1947698, by rfl⟩ : syracuseStep 2596931 = 3895397) B3895397
theorem B2596961 : Blo 1731066 2596961 := bstep (se 2 (by rfl) ⟨973860, by rfl⟩ : syracuseStep 2596961 = 1947721) B1947721
theorem B4382819 : Blo 1731066 4382819 := bstep (se 1 (by rfl) ⟨3287114, by rfl⟩ : syracuseStep 4382819 = 6574229) B6574229
theorem B6242417 : Blo 1731066 6242417 := bstep (se 2 (by rfl) ⟨2340906, by rfl⟩ : syracuseStep 6242417 = 4681813) B4681813
theorem B3121265 : Blo 1731066 3121265 := bstep (se 2 (by rfl) ⟨1170474, by rfl⟩ : syracuseStep 3121265 = 2340949) B2340949
theorem B2596979 : Blo 1731066 2596979 := bstep (se 1 (by rfl) ⟨1947734, by rfl⟩ : syracuseStep 2596979 = 3895469) B3895469
theorem B2597009 : Blo 1731066 2597009 := bstep (se 2 (by rfl) ⟨973878, by rfl⟩ : syracuseStep 2597009 = 1947757) B1947757
theorem B2597027 : Blo 1731066 2597027 := bstep (se 1 (by rfl) ⟨1947770, by rfl⟩ : syracuseStep 2597027 = 3895541) B3895541
theorem B2597057 : Blo 1731066 2597057 := bstep (se 2 (by rfl) ⟨973896, by rfl⟩ : syracuseStep 2597057 = 1947793) B1947793
theorem B2597075 : Blo 1731066 2597075 := bstep (se 1 (by rfl) ⟨1947806, by rfl⟩ : syracuseStep 2597075 = 3895613) B3895613
theorem B23691491 : Blo 1731066 23691491 := bstep (se 1 (by rfl) ⟨17768618, by rfl⟩ : syracuseStep 23691491 = 35537237) B35537237
theorem B5546225 : Blo 1731066 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B2597105 : Blo 1731066 2597105 := bstep (se 2 (by rfl) ⟨973914, by rfl⟩ : syracuseStep 2597105 = 1947829) B1947829
theorem B2597123 : Blo 1731066 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B2466065 : Blo 1731066 2466065 := bstep (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) B1849549
theorem B2597153 : Blo 1731066 2597153 := bstep (se 2 (by rfl) ⟨973932, by rfl⟩ : syracuseStep 2597153 = 1947865) B1947865
theorem B4383011 : Blo 1731066 4383011 := bstep (se 1 (by rfl) ⟨3287258, by rfl⟩ : syracuseStep 4383011 = 6574517) B6574517
theorem B2597171 : Blo 1731066 2597171 := bstep (se 1 (by rfl) ⟨1947878, by rfl⟩ : syracuseStep 2597171 = 3895757) B3895757
theorem B2597201 : Blo 1731066 2597201 := bstep (se 2 (by rfl) ⟨973950, by rfl⟩ : syracuseStep 2597201 = 1947901) B1947901
theorem B2253139 : Blo 1731066 2253139 := bstep (se 1 (by rfl) ⟨1689854, by rfl⟩ : syracuseStep 2253139 = 3379709) B3379709
theorem B2597219 : Blo 1731066 2597219 := bstep (se 1 (by rfl) ⟨1947914, by rfl⟩ : syracuseStep 2597219 = 3895829) B3895829
theorem B5546353 : Blo 1731066 5546353 := bstep (se 2 (by rfl) ⟨2079882, by rfl⟩ : syracuseStep 5546353 = 4159765) B4159765
theorem B2597249 : Blo 1731066 2597249 := bstep (se 2 (by rfl) ⟨973968, by rfl⟩ : syracuseStep 2597249 = 1947937) B1947937
theorem B2597267 : Blo 1731066 2597267 := bstep (se 1 (by rfl) ⟨1947950, by rfl⟩ : syracuseStep 2597267 = 3895901) B3895901
theorem B2597297 : Blo 1731066 2597297 := bstep (se 2 (by rfl) ⟨973986, by rfl⟩ : syracuseStep 2597297 = 1947973) B1947973
theorem B2597315 : Blo 1731066 2597315 := bstep (se 1 (by rfl) ⟨1947986, by rfl⟩ : syracuseStep 2597315 = 3895973) B3895973
theorem B7397837 : Blo 1731066 7397837 := bstep (se 3 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 7397837 = 2774189) B2774189
theorem B2597345 : Blo 1731066 2597345 := bstep (se 2 (by rfl) ⟨974004, by rfl⟩ : syracuseStep 2597345 = 1948009) B1948009
theorem B5923313 : Blo 1731066 5923313 := bstep (se 2 (by rfl) ⟨2221242, by rfl⟩ : syracuseStep 5923313 = 4442485) B4442485
theorem B2597363 : Blo 1731066 2597363 := bstep (se 1 (by rfl) ⟨1948022, by rfl⟩ : syracuseStep 2597363 = 3896045) B3896045
theorem B2597393 : Blo 1731066 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B2597411 : Blo 1731066 2597411 := bstep (se 1 (by rfl) ⟨1948058, by rfl⟩ : syracuseStep 2597411 = 3896117) B3896117
theorem B2597441 : Blo 1731066 2597441 := bstep (se 2 (by rfl) ⟨974040, by rfl⟩ : syracuseStep 2597441 = 1948081) B1948081
theorem B2597459 : Blo 1731066 2597459 := bstep (se 1 (by rfl) ⟨1948094, by rfl⟩ : syracuseStep 2597459 = 3896189) B3896189
theorem B5546609 : Blo 1731066 5546609 := bstep (se 2 (by rfl) ⟨2079978, by rfl⟩ : syracuseStep 5546609 = 4159957) B4159957
theorem B2597489 : Blo 1731066 2597489 := bstep (se 2 (by rfl) ⟨974058, by rfl⟩ : syracuseStep 2597489 = 1948117) B1948117
theorem B2597507 : Blo 1731066 2597507 := bstep (se 1 (by rfl) ⟨1948130, by rfl⟩ : syracuseStep 2597507 = 3896261) B3896261
theorem B2597537 : Blo 1731066 2597537 := bstep (se 2 (by rfl) ⟨974076, by rfl⟩ : syracuseStep 2597537 = 1948153) B1948153
theorem B6242993 : Blo 1731066 6242993 := bstep (se 2 (by rfl) ⟨2341122, by rfl⟩ : syracuseStep 6242993 = 4682245) B4682245
theorem B2597555 : Blo 1731066 2597555 := bstep (se 1 (by rfl) ⟨1948166, by rfl⟩ : syracuseStep 2597555 = 3896333) B3896333
theorem B2597585 : Blo 1731066 2597585 := bstep (se 2 (by rfl) ⟨974094, by rfl⟩ : syracuseStep 2597585 = 1948189) B1948189
theorem B2597603 : Blo 1731066 2597603 := bstep (se 1 (by rfl) ⟨1948202, by rfl⟩ : syracuseStep 2597603 = 3896405) B3896405
theorem B4932323 : Blo 1731066 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B4743917 : Blo 1731066 4743917 := bstep (se 3 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 4743917 = 1778969) B1778969
theorem B16646897 : Blo 1731066 16646897 := bstep (se 2 (by rfl) ⟨6242586, by rfl⟩ : syracuseStep 16646897 = 12485173) B12485173
theorem B2597633 : Blo 1731066 2597633 := bstep (se 2 (by rfl) ⟨974112, by rfl⟩ : syracuseStep 2597633 = 1948225) B1948225
theorem B2499347 : Blo 1731066 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B2597651 : Blo 1731066 2597651 := bstep (se 1 (by rfl) ⟨1948238, by rfl⟩ : syracuseStep 2597651 = 3896477) B3896477
theorem B2597681 : Blo 1731066 2597681 := bstep (se 2 (by rfl) ⟨974130, by rfl⟩ : syracuseStep 2597681 = 1948261) B1948261
theorem B39994165 : Blo 1731066 39994165 := bstep (se 5 (by rfl) ⟨1874726, by rfl⟩ : syracuseStep 39994165 = 3749453) B3749453
theorem B2597699 : Blo 1731066 2597699 := bstep (se 1 (by rfl) ⟨1948274, by rfl⟩ : syracuseStep 2597699 = 3896549) B3896549
theorem B2597729 : Blo 1731066 2597729 := bstep (se 2 (by rfl) ⟨974148, by rfl⟩ : syracuseStep 2597729 = 1948297) B1948297
theorem B2597747 : Blo 1731066 2597747 := bstep (se 1 (by rfl) ⟨1948310, by rfl⟩ : syracuseStep 2597747 = 3896621) B3896621
theorem B2597777 : Blo 1731066 2597777 := bstep (se 2 (by rfl) ⟨974166, by rfl⟩ : syracuseStep 2597777 = 1948333) B1948333
theorem B2597795 : Blo 1731066 2597795 := bstep (se 1 (by rfl) ⟨1948346, by rfl⟩ : syracuseStep 2597795 = 3896693) B3896693
theorem B2597825 : Blo 1731066 2597825 := bstep (se 2 (by rfl) ⟨974184, by rfl⟩ : syracuseStep 2597825 = 1948369) B1948369
theorem B2597843 : Blo 1731066 2597843 := bstep (se 1 (by rfl) ⟨1948382, by rfl⟩ : syracuseStep 2597843 = 3896765) B3896765
theorem B2081747 : Blo 1731066 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B2597873 : Blo 1731066 2597873 := bstep (se 2 (by rfl) ⟨974202, by rfl⟩ : syracuseStep 2597873 = 1948405) B1948405
theorem B2597891 : Blo 1731066 2597891 := bstep (se 1 (by rfl) ⟨1948418, by rfl⟩ : syracuseStep 2597891 = 3896837) B3896837
theorem B2597921 : Blo 1731066 2597921 := bstep (se 2 (by rfl) ⟨974220, by rfl⟩ : syracuseStep 2597921 = 1948441) B1948441
theorem B2597939 : Blo 1731066 2597939 := bstep (se 1 (by rfl) ⟨1948454, by rfl⟩ : syracuseStep 2597939 = 3896909) B3896909
theorem B2597969 : Blo 1731066 2597969 := bstep (se 2 (by rfl) ⟨974238, by rfl⟩ : syracuseStep 2597969 = 1948477) B1948477
theorem B2597987 : Blo 1731066 2597987 := bstep (se 1 (by rfl) ⟨1948490, by rfl⟩ : syracuseStep 2597987 = 3896981) B3896981
theorem B2466931 : Blo 1731066 2466931 := bstep (se 1 (by rfl) ⟨1850198, by rfl⟩ : syracuseStep 2466931 = 3700397) B3700397
theorem B2598017 : Blo 1731066 2598017 := bstep (se 2 (by rfl) ⟨974256, by rfl⟩ : syracuseStep 2598017 = 1948513) B1948513
theorem B2598035 : Blo 1731066 2598035 := bstep (se 1 (by rfl) ⟨1948526, by rfl⟩ : syracuseStep 2598035 = 3897053) B3897053
theorem B2598065 : Blo 1731066 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B6579377 : Blo 1731066 6579377 := bstep (se 2 (by rfl) ⟨2467266, by rfl⟩ : syracuseStep 6579377 = 4934533) B4934533
theorem B2598083 : Blo 1731066 2598083 := bstep (se 1 (by rfl) ⟨1948562, by rfl⟩ : syracuseStep 2598083 = 3897125) B3897125
theorem B4383953 : Blo 1731066 4383953 := bstep (se 2 (by rfl) ⟨1643982, by rfl⟩ : syracuseStep 4383953 = 3287965) B3287965
theorem B2467027 : Blo 1731066 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B2598113 : Blo 1731066 2598113 := bstep (se 2 (by rfl) ⟨974292, by rfl⟩ : syracuseStep 2598113 = 1948585) B1948585
theorem B4113649 : Blo 1731066 4113649 := bstep (se 2 (by rfl) ⟨1542618, by rfl⟩ : syracuseStep 4113649 = 3085237) B3085237
theorem B4162801 : Blo 1731066 4162801 := bstep (se 2 (by rfl) ⟨1561050, by rfl⟩ : syracuseStep 4162801 = 3122101) B3122101
theorem B2598131 : Blo 1731066 2598131 := bstep (se 1 (by rfl) ⟨1948598, by rfl⟩ : syracuseStep 2598131 = 3897197) B3897197
theorem B4384003 : Blo 1731066 4384003 := bstep (se 1 (by rfl) ⟨3288002, by rfl⟩ : syracuseStep 4384003 = 6576005) B6576005
theorem B2598161 : Blo 1731066 2598161 := bstep (se 2 (by rfl) ⟨974310, by rfl⟩ : syracuseStep 2598161 = 1948621) B1948621
theorem B2598179 : Blo 1731066 2598179 := bstep (se 1 (by rfl) ⟨1948634, by rfl⟩ : syracuseStep 2598179 = 3897269) B3897269
theorem B2598209 : Blo 1731066 2598209 := bstep (se 2 (by rfl) ⟨974328, by rfl⟩ : syracuseStep 2598209 = 1948657) B1948657
theorem B2598227 : Blo 1731066 2598227 := bstep (se 1 (by rfl) ⟨1948670, by rfl⟩ : syracuseStep 2598227 = 3897341) B3897341
theorem B2704739 : Blo 1731066 2704739 := bstep (se 1 (by rfl) ⟨2028554, by rfl⟩ : syracuseStep 2704739 = 4057109) B4057109
theorem B2598257 : Blo 1731066 2598257 := bstep (se 2 (by rfl) ⟨974346, by rfl⟩ : syracuseStep 2598257 = 1948693) B1948693
theorem B2598275 : Blo 1731066 2598275 := bstep (se 1 (by rfl) ⟨1948706, by rfl⟩ : syracuseStep 2598275 = 3897413) B3897413
theorem B3122563 : Blo 1731066 3122563 := bstep (se 1 (by rfl) ⟨2341922, by rfl⟩ : syracuseStep 3122563 = 4683845) B4683845
theorem B4384145 : Blo 1731066 4384145 := bstep (se 2 (by rfl) ⟨1644054, by rfl⟩ : syracuseStep 4384145 = 3288109) B3288109
theorem B2598305 : Blo 1731066 2598305 := bstep (se 2 (by rfl) ⟨974364, by rfl⟩ : syracuseStep 2598305 = 1948729) B1948729
theorem B2598323 : Blo 1731066 2598323 := bstep (se 1 (by rfl) ⟨1948742, by rfl⟩ : syracuseStep 2598323 = 3897485) B3897485
theorem B2598353 : Blo 1731066 2598353 := bstep (se 2 (by rfl) ⟨974382, by rfl⟩ : syracuseStep 2598353 = 1948765) B1948765
theorem B2598371 : Blo 1731066 2598371 := bstep (se 1 (by rfl) ⟨1948778, by rfl⟩ : syracuseStep 2598371 = 3897557) B3897557
theorem B16238065 : Blo 1731066 16238065 := bstep (se 2 (by rfl) ⟨6089274, by rfl⟩ : syracuseStep 16238065 = 12178549) B12178549
theorem B2598401 : Blo 1731066 2598401 := bstep (se 2 (by rfl) ⟨974400, by rfl⟩ : syracuseStep 2598401 = 1948801) B1948801
theorem B4933133 : Blo 1731066 4933133 := bstep (se 3 (by rfl) ⟨924962, by rfl⟩ : syracuseStep 4933133 = 1849925) B1849925
theorem B2598419 : Blo 1731066 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B2598449 : Blo 1731066 2598449 := bstep (se 2 (by rfl) ⟨974418, by rfl⟩ : syracuseStep 2598449 = 1948837) B1948837
theorem B2598467 : Blo 1731066 2598467 := bstep (se 1 (by rfl) ⟨1948850, by rfl⟩ : syracuseStep 2598467 = 3897701) B3897701
theorem B2598497 : Blo 1731066 2598497 := bstep (se 2 (by rfl) ⟨974436, by rfl⟩ : syracuseStep 2598497 = 1948873) B1948873
theorem B2598515 : Blo 1731066 2598515 := bstep (se 1 (by rfl) ⟨1948886, by rfl⟩ : syracuseStep 2598515 = 3897773) B3897773
theorem B2598545 : Blo 1731066 2598545 := bstep (se 2 (by rfl) ⟨974454, by rfl⟩ : syracuseStep 2598545 = 1948909) B1948909
theorem B2598563 : Blo 1731066 2598563 := bstep (se 1 (by rfl) ⟨1948922, by rfl⟩ : syracuseStep 2598563 = 3897845) B3897845
theorem B2598593 : Blo 1731066 2598593 := bstep (se 2 (by rfl) ⟨974472, by rfl⟩ : syracuseStep 2598593 = 1948945) B1948945
theorem B2467523 : Blo 1731066 2467523 := bstep (se 1 (by rfl) ⟨1850642, by rfl⟩ : syracuseStep 2467523 = 3701285) B3701285
theorem B5842637 : Blo 1731066 5842637 := bstep (se 3 (by rfl) ⟨1095494, by rfl⟩ : syracuseStep 5842637 = 2190989) B2190989
theorem B4933325 : Blo 1731066 4933325 := bstep (se 3 (by rfl) ⟨924998, by rfl⟩ : syracuseStep 4933325 = 1849997) B1849997
theorem B2598611 : Blo 1731066 2598611 := bstep (se 1 (by rfl) ⟨1948958, by rfl⟩ : syracuseStep 2598611 = 3897917) B3897917
theorem B2598641 : Blo 1731066 2598641 := bstep (se 2 (by rfl) ⟨974490, by rfl⟩ : syracuseStep 2598641 = 1948981) B1948981
theorem B5842691 : Blo 1731066 5842691 := bstep (se 1 (by rfl) ⟨4382018, by rfl⟩ : syracuseStep 5842691 = 8764037) B8764037
theorem B2598659 : Blo 1731066 2598659 := bstep (se 1 (by rfl) ⟨1948994, by rfl⟩ : syracuseStep 2598659 = 3897989) B3897989
theorem B2598689 : Blo 1731066 2598689 := bstep (se 2 (by rfl) ⟨974508, by rfl⟩ : syracuseStep 2598689 = 1949017) B1949017
theorem B4998961 : Blo 1731066 4998961 := bstep (se 2 (by rfl) ⟨1874610, by rfl⟩ : syracuseStep 4998961 = 3749221) B3749221
theorem B2598707 : Blo 1731066 2598707 := bstep (se 1 (by rfl) ⟨1949030, by rfl⟩ : syracuseStep 2598707 = 3898061) B3898061
theorem B19728197 : Blo 1731066 19728197 := bstep (se 4 (by rfl) ⟨1849518, by rfl⟩ : syracuseStep 19728197 = 3699037) B3699037
theorem B2598737 : Blo 1731066 2598737 := bstep (se 2 (by rfl) ⟨974526, by rfl⟩ : syracuseStep 2598737 = 1949053) B1949053
theorem B2598755 : Blo 1731066 2598755 := bstep (se 1 (by rfl) ⟨1949066, by rfl⟩ : syracuseStep 2598755 = 3898133) B3898133
theorem B2598785 : Blo 1731066 2598785 := bstep (se 2 (by rfl) ⟨974544, by rfl⟩ : syracuseStep 2598785 = 1949089) B1949089
theorem B2598803 : Blo 1731066 2598803 := bstep (se 1 (by rfl) ⟨1949102, by rfl⟩ : syracuseStep 2598803 = 3898205) B3898205
theorem B2598833 : Blo 1731066 2598833 := bstep (se 2 (by rfl) ⟨974562, by rfl⟩ : syracuseStep 2598833 = 1949125) B1949125
theorem B2598851 : Blo 1731066 2598851 := bstep (se 1 (by rfl) ⟨1949138, by rfl⟩ : syracuseStep 2598851 = 3898277) B3898277
theorem B3286993 : Blo 1731066 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B3164113 : Blo 1731066 3164113 := bstep (se 2 (by rfl) ⟨1186542, by rfl⟩ : syracuseStep 3164113 = 2373085) B2373085
theorem B2598881 : Blo 1731066 2598881 := bstep (se 2 (by rfl) ⟨974580, by rfl⟩ : syracuseStep 2598881 = 1949161) B1949161
theorem B2598899 : Blo 1731066 2598899 := bstep (se 1 (by rfl) ⟨1949174, by rfl⟩ : syracuseStep 2598899 = 3898349) B3898349
theorem B5842961 : Blo 1731066 5842961 := bstep (se 2 (by rfl) ⟨2191110, by rfl⟩ : syracuseStep 5842961 = 4382221) B4382221
theorem B2598929 : Blo 1731066 2598929 := bstep (se 2 (by rfl) ⟨974598, by rfl⟩ : syracuseStep 2598929 = 1949197) B1949197
theorem B2598947 : Blo 1731066 2598947 := bstep (se 1 (by rfl) ⟨1949210, by rfl⟩ : syracuseStep 2598947 = 3898421) B3898421
theorem B2598977 : Blo 1731066 2598977 := bstep (se 2 (by rfl) ⟨974616, by rfl⟩ : syracuseStep 2598977 = 1949233) B1949233
theorem B2598995 : Blo 1731066 2598995 := bstep (se 1 (by rfl) ⟨1949246, by rfl⟩ : syracuseStep 2598995 = 3898493) B3898493
theorem B33736817 : Blo 1731066 33736817 := bstep (se 2 (by rfl) ⟨12651306, by rfl⟩ : syracuseStep 33736817 = 25302613) B25302613
theorem B8767601 : Blo 1731066 8767601 := bstep (se 2 (by rfl) ⟨3287850, by rfl⟩ : syracuseStep 8767601 = 6575701) B6575701
theorem B2599025 : Blo 1731066 2599025 := bstep (se 2 (by rfl) ⟨974634, by rfl⟩ : syracuseStep 2599025 = 1949269) B1949269
theorem B2599043 : Blo 1731066 2599043 := bstep (se 1 (by rfl) ⟨1949282, by rfl⟩ : syracuseStep 2599043 = 3898565) B3898565
theorem B2599073 : Blo 1731066 2599073 := bstep (se 2 (by rfl) ⟨974652, by rfl⟩ : syracuseStep 2599073 = 1949305) B1949305
theorem B2599091 : Blo 1731066 2599091 := bstep (se 1 (by rfl) ⟨1949318, by rfl⟩ : syracuseStep 2599091 = 3898637) B3898637
theorem B9865421 : Blo 1731066 9865421 := bstep (se 3 (by rfl) ⟨1849766, by rfl⟩ : syracuseStep 9865421 = 3699533) B3699533
theorem B2599121 : Blo 1731066 2599121 := bstep (se 2 (by rfl) ⟨974670, by rfl⟩ : syracuseStep 2599121 = 1949341) B1949341
theorem B2599139 : Blo 1731066 2599139 := bstep (se 1 (by rfl) ⟨1949354, by rfl⟩ : syracuseStep 2599139 = 3898709) B3898709
theorem B2599169 : Blo 1731066 2599169 := bstep (se 2 (by rfl) ⟨974688, by rfl⟩ : syracuseStep 2599169 = 1949377) B1949377
theorem B5548301 : Blo 1731066 5548301 := bstep (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) B2080613
theorem B2599187 : Blo 1731066 2599187 := bstep (se 1 (by rfl) ⟨1949390, by rfl⟩ : syracuseStep 2599187 = 3898781) B3898781
theorem B2599217 : Blo 1731066 2599217 := bstep (se 2 (by rfl) ⟨974706, by rfl⟩ : syracuseStep 2599217 = 1949413) B1949413
theorem B2599235 : Blo 1731066 2599235 := bstep (se 1 (by rfl) ⟨1949426, by rfl⟩ : syracuseStep 2599235 = 3898853) B3898853
theorem B2599265 : Blo 1731066 2599265 := bstep (se 2 (by rfl) ⟨974724, by rfl⟩ : syracuseStep 2599265 = 1949449) B1949449
theorem B3287395 : Blo 1731066 3287395 := bstep (se 1 (by rfl) ⟨2465546, by rfl⟩ : syracuseStep 3287395 = 4931093) B4931093
theorem B4385137 : Blo 1731066 4385137 := bstep (se 2 (by rfl) ⟨1644426, by rfl⟩ : syracuseStep 4385137 = 3288853) B3288853
theorem B19736945 : Blo 1731066 19736945 := bstep (se 2 (by rfl) ⟨7401354, by rfl⟩ : syracuseStep 19736945 = 14802709) B14802709
theorem B2599283 : Blo 1731066 2599283 := bstep (se 1 (by rfl) ⟨1949462, by rfl⟩ : syracuseStep 2599283 = 3898925) B3898925
theorem B3287441 : Blo 1731066 3287441 := bstep (se 2 (by rfl) ⟨1232790, by rfl⟩ : syracuseStep 3287441 = 2465581) B2465581
theorem B2599313 : Blo 1731066 2599313 := bstep (se 2 (by rfl) ⟨974742, by rfl⟩ : syracuseStep 2599313 = 1949485) B1949485
theorem B2599331 : Blo 1731066 2599331 := bstep (se 1 (by rfl) ⟨1949498, by rfl⟩ : syracuseStep 2599331 = 3898997) B3898997
theorem B2599361 : Blo 1731066 2599361 := bstep (se 2 (by rfl) ⟨974760, by rfl⟩ : syracuseStep 2599361 = 1949521) B1949521
theorem B2599379 : Blo 1731066 2599379 := bstep (se 1 (by rfl) ⟨1949534, by rfl⟩ : syracuseStep 2599379 = 3899069) B3899069
theorem B2599409 : Blo 1731066 2599409 := bstep (se 2 (by rfl) ⟨974778, by rfl⟩ : syracuseStep 2599409 = 1949557) B1949557
theorem B1731075 : Blo 1731066 1731075 := bstep (se 1 (by rfl) ⟨1298306, by rfl⟩ : syracuseStep 1731075 = 2596613) B2596613
theorem B2599427 : Blo 1731066 2599427 := bstep (se 1 (by rfl) ⟨1949570, by rfl⟩ : syracuseStep 2599427 = 3899141) B3899141
theorem B1731091 : Blo 1731066 1731091 := bstep (se 1 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 1731091 = 2596637) B2596637
theorem B2599457 : Blo 1731066 2599457 := bstep (se 2 (by rfl) ⟨974796, by rfl⟩ : syracuseStep 2599457 = 1949593) B1949593
theorem B1731107 : Blo 1731066 1731107 := bstep (se 1 (by rfl) ⟨1298330, by rfl⟩ : syracuseStep 1731107 = 2596661) B2596661
theorem B5843501 : Blo 1731066 5843501 := bstep (se 3 (by rfl) ⟨1095656, by rfl⟩ : syracuseStep 5843501 = 2191313) B2191313
theorem B1731123 : Blo 1731066 1731123 := bstep (se 1 (by rfl) ⟨1298342, by rfl⟩ : syracuseStep 1731123 = 2596685) B2596685
theorem B2599475 : Blo 1731066 2599475 := bstep (se 1 (by rfl) ⟨1949606, by rfl⟩ : syracuseStep 2599475 = 3899213) B3899213
theorem B1731139 : Blo 1731066 1731139 := bstep (se 1 (by rfl) ⟨1298354, by rfl⟩ : syracuseStep 1731139 = 2596709) B2596709
theorem B2599505 : Blo 1731066 2599505 := bstep (se 2 (by rfl) ⟨974814, by rfl⟩ : syracuseStep 2599505 = 1949629) B1949629
theorem B1731155 : Blo 1731066 1731155 := bstep (se 1 (by rfl) ⟨1298366, by rfl⟩ : syracuseStep 1731155 = 2596733) B2596733
theorem B1731171 : Blo 1731066 1731171 := bstep (se 1 (by rfl) ⟨1298378, by rfl⟩ : syracuseStep 1731171 = 2596757) B2596757
theorem B5843555 : Blo 1731066 5843555 := bstep (se 1 (by rfl) ⟨4382666, by rfl⟩ : syracuseStep 5843555 = 8765333) B8765333
theorem B2599523 : Blo 1731066 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B1731187 : Blo 1731066 1731187 := bstep (se 1 (by rfl) ⟨1298390, by rfl⟩ : syracuseStep 1731187 = 2596781) B2596781
theorem B2599553 : Blo 1731066 2599553 := bstep (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) B1949665
theorem B1731203 : Blo 1731066 1731203 := bstep (se 1 (by rfl) ⟨1298402, by rfl⟩ : syracuseStep 1731203 = 2596805) B2596805
theorem B4385411 : Blo 1731066 4385411 := bstep (se 1 (by rfl) ⟨3289058, by rfl⟩ : syracuseStep 4385411 = 6578117) B6578117
theorem B1731219 : Blo 1731066 1731219 := bstep (se 1 (by rfl) ⟨1298414, by rfl⟩ : syracuseStep 1731219 = 2596829) B2596829
theorem B2599571 : Blo 1731066 2599571 := bstep (se 1 (by rfl) ⟨1949678, by rfl⟩ : syracuseStep 2599571 = 3899357) B3899357
theorem B1731235 : Blo 1731066 1731235 := bstep (se 1 (by rfl) ⟨1298426, by rfl⟩ : syracuseStep 1731235 = 2596853) B2596853
theorem B4934317 : Blo 1731066 4934317 := bstep (se 3 (by rfl) ⟨925184, by rfl⟩ : syracuseStep 4934317 = 1850369) B1850369
theorem B3287729 : Blo 1731066 3287729 := bstep (se 2 (by rfl) ⟨1232898, by rfl⟩ : syracuseStep 3287729 = 2465797) B2465797
theorem B1731251 : Blo 1731066 1731251 := bstep (se 1 (by rfl) ⟨1298438, by rfl⟩ : syracuseStep 1731251 = 2596877) B2596877
theorem B1731267 : Blo 1731066 1731267 := bstep (se 1 (by rfl) ⟨1298450, by rfl⟩ : syracuseStep 1731267 = 2596901) B2596901
theorem B16648901 : Blo 1731066 16648901 := bstep (se 4 (by rfl) ⟨1560834, by rfl⟩ : syracuseStep 16648901 = 3121669) B3121669
theorem B1731283 : Blo 1731066 1731283 := bstep (se 1 (by rfl) ⟨1298462, by rfl⟩ : syracuseStep 1731283 = 2596925) B2596925
theorem B6572771 : Blo 1731066 6572771 := bstep (se 1 (by rfl) ⟨4929578, by rfl⟩ : syracuseStep 6572771 = 9859157) B9859157
theorem B1731299 : Blo 1731066 1731299 := bstep (se 1 (by rfl) ⟨1298474, by rfl⟩ : syracuseStep 1731299 = 2596949) B2596949
theorem B6572785 : Blo 1731066 6572785 := bstep (se 2 (by rfl) ⟨2464794, by rfl⟩ : syracuseStep 6572785 = 4929589) B4929589
theorem B20007665 : Blo 1731066 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B1731315 : Blo 1731066 1731315 := bstep (se 1 (by rfl) ⟨1298486, by rfl⟩ : syracuseStep 1731315 = 2596973) B2596973
theorem B1731331 : Blo 1731066 1731331 := bstep (se 1 (by rfl) ⟨1298498, by rfl⟩ : syracuseStep 1731331 = 2596997) B2596997
theorem B1731347 : Blo 1731066 1731347 := bstep (se 1 (by rfl) ⟨1298510, by rfl⟩ : syracuseStep 1731347 = 2597021) B2597021
theorem B1731363 : Blo 1731066 1731363 := bstep (se 1 (by rfl) ⟨1298522, by rfl⟩ : syracuseStep 1731363 = 2597045) B2597045
theorem B11094833 : Blo 1731066 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B1731379 : Blo 1731066 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B1731395 : Blo 1731066 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B4385603 : Blo 1731066 4385603 := bstep (se 1 (by rfl) ⟨3289202, by rfl⟩ : syracuseStep 4385603 = 6578405) B6578405
theorem B1731411 : Blo 1731066 1731411 := bstep (se 1 (by rfl) ⟨1298558, by rfl⟩ : syracuseStep 1731411 = 2597117) B2597117
theorem B1731427 : Blo 1731066 1731427 := bstep (se 1 (by rfl) ⟨1298570, by rfl⟩ : syracuseStep 1731427 = 2597141) B2597141
theorem B22195043 : Blo 1731066 22195043 := bstep (se 1 (by rfl) ⟨16646282, by rfl⟩ : syracuseStep 22195043 = 33292565) B33292565
theorem B5843825 : Blo 1731066 5843825 := bstep (se 2 (by rfl) ⟨2191434, by rfl⟩ : syracuseStep 5843825 = 4382869) B4382869
theorem B1731443 : Blo 1731066 1731443 := bstep (se 1 (by rfl) ⟨1298582, by rfl⟩ : syracuseStep 1731443 = 2597165) B2597165
theorem B1731459 : Blo 1731066 1731459 := bstep (se 1 (by rfl) ⟨1298594, by rfl⟩ : syracuseStep 1731459 = 2597189) B2597189
theorem B1731475 : Blo 1731066 1731475 := bstep (se 1 (by rfl) ⟨1298606, by rfl⟩ : syracuseStep 1731475 = 2597213) B2597213
theorem B1731491 : Blo 1731066 1731491 := bstep (se 1 (by rfl) ⟨1298618, by rfl⟩ : syracuseStep 1731491 = 2597237) B2597237
theorem B6089645 : Blo 1731066 6089645 := bstep (se 3 (by rfl) ⟨1141808, by rfl⟩ : syracuseStep 6089645 = 2283617) B2283617
theorem B1731507 : Blo 1731066 1731507 := bstep (se 1 (by rfl) ⟨1298630, by rfl⟩ : syracuseStep 1731507 = 2597261) B2597261
theorem B1731523 : Blo 1731066 1731523 := bstep (se 1 (by rfl) ⟨1298642, by rfl⟩ : syracuseStep 1731523 = 2597285) B2597285
theorem B1731539 : Blo 1731066 1731539 := bstep (se 1 (by rfl) ⟨1298654, by rfl⟩ : syracuseStep 1731539 = 2597309) B2597309
theorem B1731555 : Blo 1731066 1731555 := bstep (se 1 (by rfl) ⟨1298666, by rfl⟩ : syracuseStep 1731555 = 2597333) B2597333
theorem B1731571 : Blo 1731066 1731571 := bstep (se 1 (by rfl) ⟨1298678, by rfl⟩ : syracuseStep 1731571 = 2597357) B2597357
theorem B1731587 : Blo 1731066 1731587 := bstep (se 1 (by rfl) ⟨1298690, by rfl⟩ : syracuseStep 1731587 = 2597381) B2597381
theorem B5549069 : Blo 1731066 5549069 := bstep (se 3 (by rfl) ⟨1040450, by rfl⟩ : syracuseStep 5549069 = 2080901) B2080901
theorem B1731603 : Blo 1731066 1731603 := bstep (se 1 (by rfl) ⟨1298702, by rfl⟩ : syracuseStep 1731603 = 2597405) B2597405
theorem B1731619 : Blo 1731066 1731619 := bstep (se 1 (by rfl) ⟨1298714, by rfl⟩ : syracuseStep 1731619 = 2597429) B2597429
theorem B1731635 : Blo 1731066 1731635 := bstep (se 1 (by rfl) ⟨1298726, by rfl⟩ : syracuseStep 1731635 = 2597453) B2597453
theorem B1731651 : Blo 1731066 1731651 := bstep (se 1 (by rfl) ⟨1298738, by rfl⟩ : syracuseStep 1731651 = 2597477) B2597477
theorem B5139533 : Blo 1731066 5139533 := bstep (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) B1927325
theorem B1731667 : Blo 1731066 1731667 := bstep (se 1 (by rfl) ⟨1298750, by rfl⟩ : syracuseStep 1731667 = 2597501) B2597501
theorem B1731683 : Blo 1731066 1731683 := bstep (se 1 (by rfl) ⟨1298762, by rfl⟩ : syracuseStep 1731683 = 2597525) B2597525
theorem B18992227 : Blo 1731066 18992227 := bstep (se 1 (by rfl) ⟨14244170, by rfl⟩ : syracuseStep 18992227 = 28488341) B28488341
theorem B1731699 : Blo 1731066 1731699 := bstep (se 1 (by rfl) ⟨1298774, by rfl⟩ : syracuseStep 1731699 = 2597549) B2597549
theorem B1731715 : Blo 1731066 1731715 := bstep (se 1 (by rfl) ⟨1298786, by rfl⟩ : syracuseStep 1731715 = 2597573) B2597573
theorem B1731731 : Blo 1731066 1731731 := bstep (se 1 (by rfl) ⟨1298798, by rfl⟩ : syracuseStep 1731731 = 2597597) B2597597
theorem B1731747 : Blo 1731066 1731747 := bstep (se 1 (by rfl) ⟨1298810, by rfl⟩ : syracuseStep 1731747 = 2597621) B2597621
theorem B1731763 : Blo 1731066 1731763 := bstep (se 1 (by rfl) ⟨1298822, by rfl⟩ : syracuseStep 1731763 = 2597645) B2597645
theorem B1731779 : Blo 1731066 1731779 := bstep (se 1 (by rfl) ⟨1298834, by rfl⟩ : syracuseStep 1731779 = 2597669) B2597669
theorem B3951811 : Blo 1731066 3951811 := bstep (se 1 (by rfl) ⟨2963858, by rfl⟩ : syracuseStep 3951811 = 5927717) B5927717
theorem B1731795 : Blo 1731066 1731795 := bstep (se 1 (by rfl) ⟨1298846, by rfl⟩ : syracuseStep 1731795 = 2597693) B2597693
theorem B1731811 : Blo 1731066 1731811 := bstep (se 1 (by rfl) ⟨1298858, by rfl⟩ : syracuseStep 1731811 = 2597717) B2597717
theorem B1731827 : Blo 1731066 1731827 := bstep (se 1 (by rfl) ⟨1298870, by rfl⟩ : syracuseStep 1731827 = 2597741) B2597741
theorem B1731843 : Blo 1731066 1731843 := bstep (se 1 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 1731843 = 2597765) B2597765
theorem B1731859 : Blo 1731066 1731859 := bstep (se 1 (by rfl) ⟨1298894, by rfl⟩ : syracuseStep 1731859 = 2597789) B2597789
theorem B1731875 : Blo 1731066 1731875 := bstep (se 1 (by rfl) ⟨1298906, by rfl⟩ : syracuseStep 1731875 = 2597813) B2597813
theorem B1731891 : Blo 1731066 1731891 := bstep (se 1 (by rfl) ⟨1298918, by rfl⟩ : syracuseStep 1731891 = 2597837) B2597837
theorem B1731907 : Blo 1731066 1731907 := bstep (se 1 (by rfl) ⟨1298930, by rfl⟩ : syracuseStep 1731907 = 2597861) B2597861
theorem B1731923 : Blo 1731066 1731923 := bstep (se 1 (by rfl) ⟨1298942, by rfl⟩ : syracuseStep 1731923 = 2597885) B2597885
theorem B1731939 : Blo 1731066 1731939 := bstep (se 1 (by rfl) ⟨1298954, by rfl⟩ : syracuseStep 1731939 = 2597909) B2597909
theorem B1731955 : Blo 1731066 1731955 := bstep (se 1 (by rfl) ⟨1298966, by rfl⟩ : syracuseStep 1731955 = 2597933) B2597933
theorem B1731971 : Blo 1731066 1731971 := bstep (se 1 (by rfl) ⟨1298978, by rfl⟩ : syracuseStep 1731971 = 2597957) B2597957
theorem B3288451 : Blo 1731066 3288451 := bstep (se 1 (by rfl) ⟨2466338, by rfl⟩ : syracuseStep 3288451 = 4932677) B4932677
theorem B5844365 : Blo 1731066 5844365 := bstep (se 3 (by rfl) ⟨1095818, by rfl⟩ : syracuseStep 5844365 = 2191637) B2191637
theorem B1731987 : Blo 1731066 1731987 := bstep (se 1 (by rfl) ⟨1298990, by rfl⟩ : syracuseStep 1731987 = 2597981) B2597981
theorem B2567585 : Blo 1731066 2567585 := bstep (se 2 (by rfl) ⟨962844, by rfl⟩ : syracuseStep 2567585 = 1925689) B1925689
theorem B1732003 : Blo 1731066 1732003 := bstep (se 1 (by rfl) ⟨1299002, by rfl⟩ : syracuseStep 1732003 = 2598005) B2598005
theorem B1732019 : Blo 1731066 1732019 := bstep (se 1 (by rfl) ⟨1299014, by rfl⟩ : syracuseStep 1732019 = 2598029) B2598029
theorem B5844419 : Blo 1731066 5844419 := bstep (se 1 (by rfl) ⟨4383314, by rfl⟩ : syracuseStep 5844419 = 8766629) B8766629
theorem B1732035 : Blo 1731066 1732035 := bstep (se 1 (by rfl) ⟨1299026, by rfl⟩ : syracuseStep 1732035 = 2598053) B2598053
theorem B1732051 : Blo 1731066 1732051 := bstep (se 1 (by rfl) ⟨1299038, by rfl⟩ : syracuseStep 1732051 = 2598077) B2598077
theorem B1732067 : Blo 1731066 1732067 := bstep (se 1 (by rfl) ⟨1299050, by rfl⟩ : syracuseStep 1732067 = 2598101) B2598101
theorem B13159907 : Blo 1731066 13159907 := bstep (se 1 (by rfl) ⟨9869930, by rfl⟩ : syracuseStep 13159907 = 19739861) B19739861
theorem B7400945 : Blo 1731066 7400945 := bstep (se 2 (by rfl) ⟨2775354, by rfl⟩ : syracuseStep 7400945 = 5550709) B5550709
theorem B1732083 : Blo 1731066 1732083 := bstep (se 1 (by rfl) ⟨1299062, by rfl⟩ : syracuseStep 1732083 = 2598125) B2598125
theorem B1732099 : Blo 1731066 1732099 := bstep (se 1 (by rfl) ⟨1299074, by rfl⟩ : syracuseStep 1732099 = 2598149) B2598149
theorem B5926403 : Blo 1731066 5926403 := bstep (se 1 (by rfl) ⟨4444802, by rfl⟩ : syracuseStep 5926403 = 8889605) B8889605
theorem B5549581 : Blo 1731066 5549581 := bstep (se 3 (by rfl) ⟨1040546, by rfl⟩ : syracuseStep 5549581 = 2081093) B2081093
theorem B1732115 : Blo 1731066 1732115 := bstep (se 1 (by rfl) ⟨1299086, by rfl⟩ : syracuseStep 1732115 = 2598173) B2598173
theorem B2190883 : Blo 1731066 2190883 := bstep (se 1 (by rfl) ⟨1643162, by rfl⟩ : syracuseStep 2190883 = 3286325) B3286325
theorem B1732131 : Blo 1731066 1732131 := bstep (se 1 (by rfl) ⟨1299098, by rfl⟩ : syracuseStep 1732131 = 2598197) B2598197
theorem B8769059 : Blo 1731066 8769059 := bstep (se 1 (by rfl) ⟨6576794, by rfl⟩ : syracuseStep 8769059 = 13153589) B13153589
theorem B1732147 : Blo 1731066 1732147 := bstep (se 1 (by rfl) ⟨1299110, by rfl⟩ : syracuseStep 1732147 = 2598221) B2598221
theorem B1732163 : Blo 1731066 1732163 := bstep (se 1 (by rfl) ⟨1299122, by rfl⟩ : syracuseStep 1732163 = 2598245) B2598245
theorem B1732179 : Blo 1731066 1732179 := bstep (se 1 (by rfl) ⟨1299134, by rfl⟩ : syracuseStep 1732179 = 2598269) B2598269
theorem B1732195 : Blo 1731066 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B4681325 : Blo 1731066 4681325 := bstep (se 3 (by rfl) ⟨877748, by rfl⟩ : syracuseStep 4681325 = 1755497) B1755497
theorem B1732211 : Blo 1731066 1732211 := bstep (se 1 (by rfl) ⟨1299158, by rfl⟩ : syracuseStep 1732211 = 2598317) B2598317
theorem B2190979 : Blo 1731066 2190979 := bstep (se 1 (by rfl) ⟨1643234, by rfl⟩ : syracuseStep 2190979 = 3286469) B3286469
theorem B5623427 : Blo 1731066 5623427 := bstep (se 1 (by rfl) ⟨4217570, by rfl⟩ : syracuseStep 5623427 = 8435141) B8435141
theorem B1732227 : Blo 1731066 1732227 := bstep (se 1 (by rfl) ⟨1299170, by rfl⟩ : syracuseStep 1732227 = 2598341) B2598341
theorem B3894929 : Blo 1731066 3894929 := bstep (se 2 (by rfl) ⟨1460598, by rfl⟩ : syracuseStep 3894929 = 2921197) B2921197
theorem B1732243 : Blo 1731066 1732243 := bstep (se 1 (by rfl) ⟨1299182, by rfl⟩ : syracuseStep 1732243 = 2598365) B2598365
theorem B3894947 : Blo 1731066 3894947 := bstep (se 1 (by rfl) ⟨2921210, by rfl⟩ : syracuseStep 3894947 = 5842421) B5842421
theorem B1732259 : Blo 1731066 1732259 := bstep (se 1 (by rfl) ⟨1299194, by rfl⟩ : syracuseStep 1732259 = 2598389) B2598389
theorem B1732275 : Blo 1731066 1732275 := bstep (se 1 (by rfl) ⟨1299206, by rfl⟩ : syracuseStep 1732275 = 2598413) B2598413
theorem B1732291 : Blo 1731066 1732291 := bstep (se 1 (by rfl) ⟨1299218, by rfl⟩ : syracuseStep 1732291 = 2598437) B2598437
theorem B5844689 : Blo 1731066 5844689 := bstep (se 2 (by rfl) ⟨2191758, by rfl⟩ : syracuseStep 5844689 = 4383517) B4383517
theorem B4746961 : Blo 1731066 4746961 := bstep (se 2 (by rfl) ⟨1780110, by rfl⟩ : syracuseStep 4746961 = 3560221) B3560221
theorem B1732307 : Blo 1731066 1732307 := bstep (se 1 (by rfl) ⟨1299230, by rfl⟩ : syracuseStep 1732307 = 2598461) B2598461
theorem B1732323 : Blo 1731066 1732323 := bstep (se 1 (by rfl) ⟨1299242, by rfl⟩ : syracuseStep 1732323 = 2598485) B2598485
theorem B4386545 : Blo 1731066 4386545 := bstep (se 2 (by rfl) ⟨1644954, by rfl⟩ : syracuseStep 4386545 = 3289909) B3289909
theorem B1732339 : Blo 1731066 1732339 := bstep (se 1 (by rfl) ⟨1299254, by rfl⟩ : syracuseStep 1732339 = 2598509) B2598509
theorem B1732355 : Blo 1731066 1732355 := bstep (se 1 (by rfl) ⟨1299266, by rfl⟩ : syracuseStep 1732355 = 2598533) B2598533
theorem B18722573 : Blo 1731066 18722573 := bstep (se 3 (by rfl) ⟨3510482, by rfl⟩ : syracuseStep 18722573 = 7020965) B7020965
theorem B1732371 : Blo 1731066 1732371 := bstep (se 1 (by rfl) ⟨1299278, by rfl⟩ : syracuseStep 1732371 = 2598557) B2598557
theorem B1732387 : Blo 1731066 1732387 := bstep (se 1 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 1732387 = 2598581) B2598581
theorem B4386595 : Blo 1731066 4386595 := bstep (se 1 (by rfl) ⟨3289946, by rfl⟩ : syracuseStep 4386595 = 6579893) B6579893
theorem B1732403 : Blo 1731066 1732403 := bstep (se 1 (by rfl) ⟨1299302, by rfl⟩ : syracuseStep 1732403 = 2598605) B2598605
theorem B1732419 : Blo 1731066 1732419 := bstep (se 1 (by rfl) ⟨1299314, by rfl⟩ : syracuseStep 1732419 = 2598629) B2598629
theorem B3288899 : Blo 1731066 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B1732435 : Blo 1731066 1732435 := bstep (se 1 (by rfl) ⟨1299326, by rfl⟩ : syracuseStep 1732435 = 2598653) B2598653
theorem B1732451 : Blo 1731066 1732451 := bstep (se 1 (by rfl) ⟨1299338, by rfl⟩ : syracuseStep 1732451 = 2598677) B2598677
theorem B1732467 : Blo 1731066 1732467 := bstep (se 1 (by rfl) ⟨1299350, by rfl⟩ : syracuseStep 1732467 = 2598701) B2598701
theorem B1732483 : Blo 1731066 1732483 := bstep (se 1 (by rfl) ⟨1299362, by rfl⟩ : syracuseStep 1732483 = 2598725) B2598725
theorem B1732499 : Blo 1731066 1732499 := bstep (se 1 (by rfl) ⟨1299374, by rfl⟩ : syracuseStep 1732499 = 2598749) B2598749
theorem B1732515 : Blo 1731066 1732515 := bstep (se 1 (by rfl) ⟨1299386, by rfl⟩ : syracuseStep 1732515 = 2598773) B2598773
theorem B3895217 : Blo 1731066 3895217 := bstep (se 2 (by rfl) ⟨1460706, by rfl⟩ : syracuseStep 3895217 = 2921413) B2921413
theorem B4386737 : Blo 1731066 4386737 := bstep (se 2 (by rfl) ⟨1645026, by rfl⟩ : syracuseStep 4386737 = 3290053) B3290053
theorem B1732531 : Blo 1731066 1732531 := bstep (se 1 (by rfl) ⟨1299398, by rfl⟩ : syracuseStep 1732531 = 2598797) B2598797
theorem B3895235 : Blo 1731066 3895235 := bstep (se 1 (by rfl) ⟨2921426, by rfl⟩ : syracuseStep 3895235 = 5842853) B5842853
theorem B3698627 : Blo 1731066 3698627 := bstep (se 1 (by rfl) ⟨2773970, by rfl⟩ : syracuseStep 3698627 = 5547941) B5547941
theorem B1732547 : Blo 1731066 1732547 := bstep (se 1 (by rfl) ⟨1299410, by rfl⟩ : syracuseStep 1732547 = 2598821) B2598821
theorem B1732563 : Blo 1731066 1732563 := bstep (se 1 (by rfl) ⟨1299422, by rfl⟩ : syracuseStep 1732563 = 2598845) B2598845
theorem B1732579 : Blo 1731066 1732579 := bstep (se 1 (by rfl) ⟨1299434, by rfl⟩ : syracuseStep 1732579 = 2598869) B2598869
theorem B1732595 : Blo 1731066 1732595 := bstep (se 1 (by rfl) ⟨1299446, by rfl⟩ : syracuseStep 1732595 = 2598893) B2598893
theorem B5550083 : Blo 1731066 5550083 := bstep (se 1 (by rfl) ⟨4162562, by rfl⟩ : syracuseStep 5550083 = 8325125) B8325125
theorem B1732611 : Blo 1731066 1732611 := bstep (se 1 (by rfl) ⟨1299458, by rfl⟩ : syracuseStep 1732611 = 2598917) B2598917
theorem B1732627 : Blo 1731066 1732627 := bstep (se 1 (by rfl) ⟨1299470, by rfl⟩ : syracuseStep 1732627 = 2598941) B2598941
theorem B1732643 : Blo 1731066 1732643 := bstep (se 1 (by rfl) ⟨1299482, by rfl⟩ : syracuseStep 1732643 = 2598965) B2598965
theorem B1732659 : Blo 1731066 1732659 := bstep (se 1 (by rfl) ⟨1299494, by rfl⟩ : syracuseStep 1732659 = 2598989) B2598989
theorem B1732675 : Blo 1731066 1732675 := bstep (se 1 (by rfl) ⟨1299506, by rfl⟩ : syracuseStep 1732675 = 2599013) B2599013
theorem B1732691 : Blo 1731066 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B3289187 : Blo 1731066 3289187 := bstep (se 1 (by rfl) ⟨2466890, by rfl⟩ : syracuseStep 3289187 = 4933781) B4933781
theorem B1732707 : Blo 1731066 1732707 := bstep (se 1 (by rfl) ⟨1299530, by rfl⟩ : syracuseStep 1732707 = 2599061) B2599061
theorem B14241905 : Blo 1731066 14241905 := bstep (se 2 (by rfl) ⟨5340714, by rfl⟩ : syracuseStep 14241905 = 10681429) B10681429
theorem B2191475 : Blo 1731066 2191475 := bstep (se 1 (by rfl) ⟨1643606, by rfl⟩ : syracuseStep 2191475 = 3287213) B3287213
theorem B1732723 : Blo 1731066 1732723 := bstep (se 1 (by rfl) ⟨1299542, by rfl⟩ : syracuseStep 1732723 = 2599085) B2599085
theorem B1732739 : Blo 1731066 1732739 := bstep (se 1 (by rfl) ⟨1299554, by rfl⟩ : syracuseStep 1732739 = 2599109) B2599109
theorem B1732755 : Blo 1731066 1732755 := bstep (se 1 (by rfl) ⟨1299566, by rfl⟩ : syracuseStep 1732755 = 2599133) B2599133
theorem B6574243 : Blo 1731066 6574243 := bstep (se 1 (by rfl) ⟨4930682, by rfl⟩ : syracuseStep 6574243 = 9861365) B9861365
theorem B1732771 : Blo 1731066 1732771 := bstep (se 1 (by rfl) ⟨1299578, by rfl⟩ : syracuseStep 1732771 = 2599157) B2599157
theorem B1732787 : Blo 1731066 1732787 := bstep (se 1 (by rfl) ⟨1299590, by rfl⟩ : syracuseStep 1732787 = 2599181) B2599181
theorem B1732803 : Blo 1731066 1732803 := bstep (se 1 (by rfl) ⟨1299602, by rfl⟩ : syracuseStep 1732803 = 2599205) B2599205
theorem B3895505 : Blo 1731066 3895505 := bstep (se 2 (by rfl) ⟨1460814, by rfl⟩ : syracuseStep 3895505 = 2921629) B2921629
theorem B1732819 : Blo 1731066 1732819 := bstep (se 1 (by rfl) ⟨1299614, by rfl⟩ : syracuseStep 1732819 = 2599229) B2599229
theorem B3895523 : Blo 1731066 3895523 := bstep (se 1 (by rfl) ⟨2921642, by rfl⟩ : syracuseStep 3895523 = 5843285) B5843285
theorem B11096291 : Blo 1731066 11096291 := bstep (se 1 (by rfl) ⟨8322218, by rfl⟩ : syracuseStep 11096291 = 16644437) B16644437
theorem B1732835 : Blo 1731066 1732835 := bstep (se 1 (by rfl) ⟨1299626, by rfl⟩ : syracuseStep 1732835 = 2599253) B2599253
theorem B5845229 : Blo 1731066 5845229 := bstep (se 3 (by rfl) ⟨1095980, by rfl⟩ : syracuseStep 5845229 = 2191961) B2191961
theorem B1732851 : Blo 1731066 1732851 := bstep (se 1 (by rfl) ⟨1299638, by rfl⟩ : syracuseStep 1732851 = 2599277) B2599277
theorem B1732867 : Blo 1731066 1732867 := bstep (se 1 (by rfl) ⟨1299650, by rfl⟩ : syracuseStep 1732867 = 2599301) B2599301
theorem B1732883 : Blo 1731066 1732883 := bstep (se 1 (by rfl) ⟨1299662, by rfl⟩ : syracuseStep 1732883 = 2599325) B2599325
theorem B5845283 : Blo 1731066 5845283 := bstep (se 1 (by rfl) ⟨4383962, by rfl⟩ : syracuseStep 5845283 = 8767925) B8767925
theorem B1732899 : Blo 1731066 1732899 := bstep (se 1 (by rfl) ⟨1299674, by rfl⟩ : syracuseStep 1732899 = 2599349) B2599349
theorem B7901489 : Blo 1731066 7901489 := bstep (se 2 (by rfl) ⟨2963058, by rfl⟩ : syracuseStep 7901489 = 5926117) B5926117
theorem B1732915 : Blo 1731066 1732915 := bstep (se 1 (by rfl) ⟨1299686, by rfl⟩ : syracuseStep 1732915 = 2599373) B2599373
theorem B1732931 : Blo 1731066 1732931 := bstep (se 1 (by rfl) ⟨1299698, by rfl⟩ : syracuseStep 1732931 = 2599397) B2599397
theorem B8769869 : Blo 1731066 8769869 := bstep (se 3 (by rfl) ⟨1644350, by rfl⟩ : syracuseStep 8769869 = 3288701) B3288701
theorem B1732947 : Blo 1731066 1732947 := bstep (se 1 (by rfl) ⟨1299710, by rfl⟩ : syracuseStep 1732947 = 2599421) B2599421
theorem B1732963 : Blo 1731066 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B9359729 : Blo 1731066 9359729 := bstep (se 2 (by rfl) ⟨3509898, by rfl⟩ : syracuseStep 9359729 = 7019797) B7019797
theorem B1732979 : Blo 1731066 1732979 := bstep (se 1 (by rfl) ⟨1299734, by rfl⟩ : syracuseStep 1732979 = 2599469) B2599469
theorem B1732995 : Blo 1731066 1732995 := bstep (se 1 (by rfl) ⟨1299746, by rfl⟩ : syracuseStep 1732995 = 2599493) B2599493
theorem B9867653 : Blo 1731066 9867653 := bstep (se 4 (by rfl) ⟨925092, by rfl⟩ : syracuseStep 9867653 = 1850185) B1850185
theorem B1733011 : Blo 1731066 1733011 := bstep (se 1 (by rfl) ⟨1299758, by rfl⟩ : syracuseStep 1733011 = 2599517) B2599517
theorem B1733027 : Blo 1731066 1733027 := bstep (se 1 (by rfl) ⟨1299770, by rfl⟩ : syracuseStep 1733027 = 2599541) B2599541
theorem B1733043 : Blo 1731066 1733043 := bstep (se 1 (by rfl) ⟨1299782, by rfl⟩ : syracuseStep 1733043 = 2599565) B2599565
theorem B1733059 : Blo 1731066 1733059 := bstep (se 1 (by rfl) ⟨1299794, by rfl⟩ : syracuseStep 1733059 = 2599589) B2599589
theorem B3895793 : Blo 1731066 3895793 := bstep (se 2 (by rfl) ⟨1460922, by rfl⟩ : syracuseStep 3895793 = 2921845) B2921845
theorem B3002881 : Blo 1731066 3002881 := bstep (se 2 (by rfl) ⟨1126080, by rfl⟩ : syracuseStep 3002881 = 2252161) B2252161
theorem B3895811 : Blo 1731066 3895811 := bstep (se 1 (by rfl) ⟨2921858, by rfl⟩ : syracuseStep 3895811 = 5843717) B5843717
theorem B9859589 : Blo 1731066 9859589 := bstep (se 4 (by rfl) ⟨924336, by rfl⟩ : syracuseStep 9859589 = 1848673) B1848673
theorem B2773523 : Blo 1731066 2773523 := bstep (se 1 (by rfl) ⟨2080142, by rfl⟩ : syracuseStep 2773523 = 4160285) B4160285
theorem B5845553 : Blo 1731066 5845553 := bstep (se 2 (by rfl) ⟨2192082, by rfl⟩ : syracuseStep 5845553 = 4384165) B4384165
theorem B7901837 : Blo 1731066 7901837 := bstep (se 3 (by rfl) ⟨1481594, by rfl⟩ : syracuseStep 7901837 = 2963189) B2963189
theorem B38490851 : Blo 1731066 38490851 := bstep (se 1 (by rfl) ⟨28868138, by rfl⟩ : syracuseStep 38490851 = 57736277) B57736277
theorem B5927651 : Blo 1731066 5927651 := bstep (se 1 (by rfl) ⟨4445738, by rfl⟩ : syracuseStep 5927651 = 8891477) B8891477
theorem B7402211 : Blo 1731066 7402211 := bstep (se 1 (by rfl) ⟨5551658, by rfl⟩ : syracuseStep 7402211 = 11103317) B11103317
theorem B2634481 : Blo 1731066 2634481 := bstep (se 2 (by rfl) ⟨987930, by rfl⟩ : syracuseStep 2634481 = 1975861) B1975861
theorem B3896081 : Blo 1731066 3896081 := bstep (se 2 (by rfl) ⟨1461030, by rfl⟩ : syracuseStep 3896081 = 2922061) B2922061
theorem B44970773 : Blo 1731066 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B2921251 : Blo 1731066 2921251 := bstep (se 1 (by rfl) ⟨2190938, by rfl⟩ : syracuseStep 2921251 = 4381877) B4381877
theorem B3896099 : Blo 1731066 3896099 := bstep (se 1 (by rfl) ⟨2922074, by rfl⟩ : syracuseStep 3896099 = 5844149) B5844149
theorem B2773811 : Blo 1731066 2773811 := bstep (se 1 (by rfl) ⟨2080358, by rfl⟩ : syracuseStep 2773811 = 4160717) B4160717
theorem B2192179 : Blo 1731066 2192179 := bstep (se 1 (by rfl) ⟨1644134, by rfl⟩ : syracuseStep 2192179 = 3288269) B3288269
theorem B2192275 : Blo 1731066 2192275 := bstep (se 1 (by rfl) ⟨1644206, by rfl⟩ : syracuseStep 2192275 = 3288413) B3288413
theorem B2921393 : Blo 1731066 2921393 := bstep (se 2 (by rfl) ⟨1095522, by rfl⟩ : syracuseStep 2921393 = 2191045) B2191045
theorem B7025635 : Blo 1731066 7025635 := bstep (se 1 (by rfl) ⟨5269226, by rfl⟩ : syracuseStep 7025635 = 10538453) B10538453
theorem B6091757 : Blo 1731066 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B2774035 : Blo 1731066 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B2921521 : Blo 1731066 2921521 := bstep (se 2 (by rfl) ⟨1095570, by rfl⟩ : syracuseStep 2921521 = 2191141) B2191141
theorem B3896369 : Blo 1731066 3896369 := bstep (se 2 (by rfl) ⟨1461138, by rfl⟩ : syracuseStep 3896369 = 2922277) B2922277
theorem B9868337 : Blo 1731066 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B21058613 : Blo 1731066 21058613 := bstep (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) B1974245
theorem B3896387 : Blo 1731066 3896387 := bstep (se 1 (by rfl) ⟨2922290, by rfl⟩ : syracuseStep 3896387 = 5844581) B5844581
theorem B5846093 : Blo 1731066 5846093 := bstep (se 3 (by rfl) ⟨1096142, by rfl⟩ : syracuseStep 5846093 = 2192285) B2192285
theorem B2921555 : Blo 1731066 2921555 := bstep (se 1 (by rfl) ⟨2191166, by rfl⟩ : syracuseStep 2921555 = 4382333) B4382333
theorem B5846147 : Blo 1731066 5846147 := bstep (se 1 (by rfl) ⟨4384610, by rfl⟩ : syracuseStep 5846147 = 8769221) B8769221
theorem B2340019 : Blo 1731066 2340019 := bstep (se 1 (by rfl) ⟨1755014, by rfl⟩ : syracuseStep 2340019 = 3510029) B3510029
theorem B2921683 : Blo 1731066 2921683 := bstep (se 1 (by rfl) ⟨2191262, by rfl⟩ : syracuseStep 2921683 = 4382525) B4382525
theorem B15807757 : Blo 1731066 15807757 := bstep (se 3 (by rfl) ⟨2963954, by rfl⟩ : syracuseStep 15807757 = 5927909) B5927909
theorem B3896657 : Blo 1731066 3896657 := bstep (se 2 (by rfl) ⟨1461246, by rfl⟩ : syracuseStep 3896657 = 2922493) B2922493
theorem B4683089 : Blo 1731066 4683089 := bstep (se 2 (by rfl) ⟨1756158, by rfl⟩ : syracuseStep 4683089 = 3512317) B3512317
theorem B2921825 : Blo 1731066 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B3896675 : Blo 1731066 3896675 := bstep (se 1 (by rfl) ⟨2922506, by rfl⟩ : syracuseStep 3896675 = 5845013) B5845013
theorem B2192771 : Blo 1731066 2192771 := bstep (se 1 (by rfl) ⟨1644578, by rfl⟩ : syracuseStep 2192771 = 3289157) B3289157
theorem B5846417 : Blo 1731066 5846417 := bstep (se 2 (by rfl) ⟨2192406, by rfl⟩ : syracuseStep 5846417 = 4384813) B4384813
theorem B2340257 : Blo 1731066 2340257 := bstep (se 2 (by rfl) ⟨877596, by rfl⟩ : syracuseStep 2340257 = 1755193) B1755193
theorem B2921953 : Blo 1731066 2921953 := bstep (se 2 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 2921953 = 2191465) B2191465
theorem B2921987 : Blo 1731066 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B3331633 : Blo 1731066 3331633 := bstep (se 2 (by rfl) ⟨1249362, by rfl⟩ : syracuseStep 3331633 = 2498725) B2498725
theorem B2340419 : Blo 1731066 2340419 := bstep (se 1 (by rfl) ⟨1755314, by rfl⟩ : syracuseStep 2340419 = 3510629) B3510629
theorem B7394915 : Blo 1731066 7394915 := bstep (se 1 (by rfl) ⟨5546186, by rfl⟩ : syracuseStep 7394915 = 11092373) B11092373
theorem B3896945 : Blo 1731066 3896945 := bstep (se 2 (by rfl) ⟨1461354, by rfl⟩ : syracuseStep 3896945 = 2922709) B2922709
theorem B2922115 : Blo 1731066 2922115 := bstep (se 1 (by rfl) ⟨2191586, by rfl⟩ : syracuseStep 2922115 = 4383173) B4383173
theorem B3896963 : Blo 1731066 3896963 := bstep (se 1 (by rfl) ⟨2922722, by rfl⟩ : syracuseStep 3896963 = 5845445) B5845445
theorem B6239921 : Blo 1731066 6239921 := bstep (se 2 (by rfl) ⟨2339970, by rfl⟩ : syracuseStep 6239921 = 4679941) B4679941
theorem B2774753 : Blo 1731066 2774753 := bstep (se 2 (by rfl) ⟨1040532, by rfl⟩ : syracuseStep 2774753 = 2081065) B2081065
theorem B2922257 : Blo 1731066 2922257 := bstep (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) B2191693
theorem B5551939 : Blo 1731066 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B12490595 : Blo 1731066 12490595 := bstep (se 1 (by rfl) ⟨9367946, by rfl⟩ : syracuseStep 12490595 = 18735893) B18735893
theorem B1947523 : Blo 1731066 1947523 := bstep (se 1 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 1947523 = 2921285) B2921285
theorem B2922385 : Blo 1731066 2922385 := bstep (se 2 (by rfl) ⟨1095894, by rfl⟩ : syracuseStep 2922385 = 2191789) B2191789
theorem B3897233 : Blo 1731066 3897233 := bstep (se 2 (by rfl) ⟨1461462, by rfl⟩ : syracuseStep 3897233 = 2922925) B2922925
theorem B2774945 : Blo 1731066 2774945 := bstep (se 2 (by rfl) ⟨1040604, by rfl⟩ : syracuseStep 2774945 = 2081209) B2081209
theorem B3897251 : Blo 1731066 3897251 := bstep (se 1 (by rfl) ⟨2922938, by rfl⟩ : syracuseStep 3897251 = 5845877) B5845877
theorem B5846957 : Blo 1731066 5846957 := bstep (se 3 (by rfl) ⟨1096304, by rfl⟩ : syracuseStep 5846957 = 2192609) B2192609
theorem B2922419 : Blo 1731066 2922419 := bstep (se 1 (by rfl) ⟨2191814, by rfl⟩ : syracuseStep 2922419 = 4383629) B4383629
theorem B5847011 : Blo 1731066 5847011 := bstep (se 1 (by rfl) ⟨4385258, by rfl⟩ : syracuseStep 5847011 = 8770517) B8770517
theorem B1849331 : Blo 1731066 1849331 := bstep (se 1 (by rfl) ⟨1386998, by rfl⟩ : syracuseStep 1849331 = 2773997) B2773997
theorem B1947667 : Blo 1731066 1947667 := bstep (se 1 (by rfl) ⟨1460750, by rfl⟩ : syracuseStep 1947667 = 2921501) B2921501
theorem B2775073 : Blo 1731066 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2922547 : Blo 1731066 2922547 := bstep (se 1 (by rfl) ⟨2191910, by rfl⟩ : syracuseStep 2922547 = 4383821) B4383821
theorem B4929635 : Blo 1731066 4929635 := bstep (se 1 (by rfl) ⟨3697226, by rfl⟩ : syracuseStep 4929635 = 7394453) B7394453
theorem B3700849 : Blo 1731066 3700849 := bstep (se 2 (by rfl) ⟨1387818, by rfl⟩ : syracuseStep 3700849 = 2775637) B2775637
theorem B5699729 : Blo 1731066 5699729 := bstep (se 2 (by rfl) ⟨2137398, by rfl⟩ : syracuseStep 5699729 = 4274797) B4274797
theorem B2341009 : Blo 1731066 2341009 := bstep (se 2 (by rfl) ⟨877878, by rfl⟩ : syracuseStep 2341009 = 1755757) B1755757
theorem B1947811 : Blo 1731066 1947811 := bstep (se 1 (by rfl) ⟨1460858, by rfl⟩ : syracuseStep 1947811 = 2921717) B2921717
theorem B3897521 : Blo 1731066 3897521 := bstep (se 2 (by rfl) ⟨1461570, by rfl⟩ : syracuseStep 3897521 = 2923141) B2923141
theorem B2922689 : Blo 1731066 2922689 := bstep (se 2 (by rfl) ⟨1096008, by rfl⟩ : syracuseStep 2922689 = 2192017) B2192017
theorem B3897539 : Blo 1731066 3897539 := bstep (se 1 (by rfl) ⟨2923154, by rfl⟩ : syracuseStep 3897539 = 5846309) B5846309
theorem B5847281 : Blo 1731066 5847281 := bstep (se 2 (by rfl) ⟨2192730, by rfl⟩ : syracuseStep 5847281 = 4385461) B4385461
theorem B89946389 : Blo 1731066 89946389 := bstep (se 6 (by rfl) ⟨2108118, by rfl⟩ : syracuseStep 89946389 = 4216237) B4216237
theorem B1947955 : Blo 1731066 1947955 := bstep (se 1 (by rfl) ⟨1460966, by rfl⟩ : syracuseStep 1947955 = 2921933) B2921933
theorem B2922817 : Blo 1731066 2922817 := bstep (se 2 (by rfl) ⟨1096056, by rfl⟩ : syracuseStep 2922817 = 2192113) B2192113
theorem B6576461 : Blo 1731066 6576461 := bstep (se 3 (by rfl) ⟨1233086, by rfl⟩ : syracuseStep 6576461 = 2466173) B2466173
theorem B2922851 : Blo 1731066 2922851 := bstep (se 1 (by rfl) ⟨2192138, by rfl⟩ : syracuseStep 2922851 = 4384277) B4384277
theorem B1948099 : Blo 1731066 1948099 := bstep (se 1 (by rfl) ⟨1461074, by rfl⟩ : syracuseStep 1948099 = 2922149) B2922149
theorem B3897809 : Blo 1731066 3897809 := bstep (se 2 (by rfl) ⟨1461678, by rfl⟩ : syracuseStep 3897809 = 2923357) B2923357
theorem B8763875 : Blo 1731066 8763875 := bstep (se 1 (by rfl) ⟨6572906, by rfl⟩ : syracuseStep 8763875 = 13145813) B13145813
theorem B2922979 : Blo 1731066 2922979 := bstep (se 1 (by rfl) ⟨2192234, by rfl⟩ : syracuseStep 2922979 = 4384469) B4384469
theorem B3897827 : Blo 1731066 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B9869795 : Blo 1731066 9869795 := bstep (se 1 (by rfl) ⟨7402346, by rfl⟩ : syracuseStep 9869795 = 14804693) B14804693
theorem B3119651 : Blo 1731066 3119651 := bstep (se 1 (by rfl) ⟨2339738, by rfl⟩ : syracuseStep 3119651 = 4679477) B4679477
theorem B1948243 : Blo 1731066 1948243 := bstep (se 1 (by rfl) ⟨1461182, by rfl⟩ : syracuseStep 1948243 = 2922365) B2922365
theorem B2923121 : Blo 1731066 2923121 := bstep (se 2 (by rfl) ⟨1096170, by rfl⟩ : syracuseStep 2923121 = 2192341) B2192341
theorem B2775713 : Blo 1731066 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B8321741 : Blo 1731066 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B1948387 : Blo 1731066 1948387 := bstep (se 1 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 1948387 = 2922581) B2922581
theorem B2923249 : Blo 1731066 2923249 := bstep (se 2 (by rfl) ⟨1096218, by rfl⟩ : syracuseStep 2923249 = 2192437) B2192437
theorem B3898097 : Blo 1731066 3898097 := bstep (se 2 (by rfl) ⟨1461786, by rfl⟩ : syracuseStep 3898097 = 2923573) B2923573
theorem B3898115 : Blo 1731066 3898115 := bstep (se 1 (by rfl) ⟨2923586, by rfl⟩ : syracuseStep 3898115 = 5847173) B5847173
theorem B5847821 : Blo 1731066 5847821 := bstep (se 3 (by rfl) ⟨1096466, by rfl⟩ : syracuseStep 5847821 = 2192933) B2192933
theorem B2923283 : Blo 1731066 2923283 := bstep (se 1 (by rfl) ⟨2192462, by rfl⟩ : syracuseStep 2923283 = 4384925) B4384925
theorem B5847875 : Blo 1731066 5847875 := bstep (se 1 (by rfl) ⟨4385906, by rfl⟩ : syracuseStep 5847875 = 8771813) B8771813
theorem B11098957 : Blo 1731066 11098957 := bstep (se 3 (by rfl) ⟨2081054, by rfl⟩ : syracuseStep 11098957 = 4162109) B4162109
theorem B1948531 : Blo 1731066 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B2923411 : Blo 1731066 2923411 := bstep (se 1 (by rfl) ⟨2192558, by rfl⟩ : syracuseStep 2923411 = 4385117) B4385117
theorem B3120113 : Blo 1731066 3120113 := bstep (se 2 (by rfl) ⟨1170042, by rfl⟩ : syracuseStep 3120113 = 2340085) B2340085
theorem B1948675 : Blo 1731066 1948675 := bstep (se 1 (by rfl) ⟨1461506, by rfl⟩ : syracuseStep 1948675 = 2923013) B2923013
theorem B3898385 : Blo 1731066 3898385 := bstep (se 2 (by rfl) ⟨1461894, by rfl⟩ : syracuseStep 3898385 = 2923789) B2923789
theorem B2923553 : Blo 1731066 2923553 := bstep (se 2 (by rfl) ⟨1096332, by rfl⟩ : syracuseStep 2923553 = 2192665) B2192665
theorem B3898403 : Blo 1731066 3898403 := bstep (se 1 (by rfl) ⟨2923802, by rfl⟩ : syracuseStep 3898403 = 5847605) B5847605
theorem B5848145 : Blo 1731066 5848145 := bstep (se 2 (by rfl) ⟨2193054, by rfl⟩ : syracuseStep 5848145 = 4386109) B4386109
theorem B1948819 : Blo 1731066 1948819 := bstep (se 1 (by rfl) ⟨1461614, by rfl⟩ : syracuseStep 1948819 = 2923229) B2923229
theorem B2923681 : Blo 1731066 2923681 := bstep (se 2 (by rfl) ⟨1096380, by rfl⟩ : syracuseStep 2923681 = 2192761) B2192761
theorem B8772785 : Blo 1731066 8772785 := bstep (se 2 (by rfl) ⟨3289794, by rfl⟩ : syracuseStep 8772785 = 6579589) B6579589
theorem B2923715 : Blo 1731066 2923715 := bstep (se 1 (by rfl) ⟨2192786, by rfl⟩ : syracuseStep 2923715 = 4385573) B4385573
theorem B8764685 : Blo 1731066 8764685 := bstep (se 3 (by rfl) ⟨1643378, by rfl⟩ : syracuseStep 8764685 = 3286757) B3286757
theorem B60833045 : Blo 1731066 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B1948963 : Blo 1731066 1948963 := bstep (se 1 (by rfl) ⟨1461722, by rfl⟩ : syracuseStep 1948963 = 2923445) B2923445
theorem B4930865 : Blo 1731066 4930865 := bstep (se 2 (by rfl) ⟨1849074, by rfl⟩ : syracuseStep 4930865 = 3698149) B3698149
theorem B3898673 : Blo 1731066 3898673 := bstep (se 2 (by rfl) ⟨1462002, by rfl⟩ : syracuseStep 3898673 = 2924005) B2924005
theorem B2923843 : Blo 1731066 2923843 := bstep (se 1 (by rfl) ⟨2192882, by rfl⟩ : syracuseStep 2923843 = 4385765) B4385765
theorem B3898691 : Blo 1731066 3898691 := bstep (se 1 (by rfl) ⟨2924018, by rfl⟩ : syracuseStep 3898691 = 5848037) B5848037
theorem B4160899 : Blo 1731066 4160899 := bstep (se 1 (by rfl) ⟨3120674, by rfl⟩ : syracuseStep 4160899 = 6241349) B6241349
theorem B4218275 : Blo 1731066 4218275 := bstep (se 1 (by rfl) ⟨3163706, by rfl⟩ : syracuseStep 4218275 = 6327413) B6327413
theorem B1949107 : Blo 1731066 1949107 := bstep (se 1 (by rfl) ⟨1461830, by rfl⟩ : syracuseStep 1949107 = 2923661) B2923661
theorem B2923985 : Blo 1731066 2923985 := bstep (se 2 (by rfl) ⟨1096494, by rfl⟩ : syracuseStep 2923985 = 2192989) B2192989
theorem B5414381 : Blo 1731066 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B19734029 : Blo 1731066 19734029 := bstep (se 3 (by rfl) ⟨3700130, by rfl⟩ : syracuseStep 19734029 = 7400261) B7400261
theorem B7396913 : Blo 1731066 7396913 := bstep (se 2 (by rfl) ⟨2773842, by rfl⟩ : syracuseStep 7396913 = 5547685) B5547685
theorem B1949251 : Blo 1731066 1949251 := bstep (se 1 (by rfl) ⟨1461938, by rfl⟩ : syracuseStep 1949251 = 2923877) B2923877
theorem B2924113 : Blo 1731066 2924113 := bstep (se 2 (by rfl) ⟨1096542, by rfl⟩ : syracuseStep 2924113 = 2193085) B2193085
theorem B3898961 : Blo 1731066 3898961 := bstep (se 2 (by rfl) ⟨1462110, by rfl⟩ : syracuseStep 3898961 = 2924221) B2924221
theorem B3898979 : Blo 1731066 3898979 := bstep (se 1 (by rfl) ⟨2924234, by rfl⟩ : syracuseStep 3898979 = 5848469) B5848469
theorem B5848685 : Blo 1731066 5848685 := bstep (se 3 (by rfl) ⟨1096628, by rfl⟩ : syracuseStep 5848685 = 2193257) B2193257
theorem B2924147 : Blo 1731066 2924147 := bstep (se 1 (by rfl) ⟨2193110, by rfl⟩ : syracuseStep 2924147 = 4386221) B4386221
theorem B5848739 : Blo 1731066 5848739 := bstep (se 1 (by rfl) ⟨4386554, by rfl⟩ : syracuseStep 5848739 = 8773109) B8773109
theorem B2465473 : Blo 1731066 2465473 := bstep (se 2 (by rfl) ⟨924552, by rfl⟩ : syracuseStep 2465473 = 1849105) B1849105
theorem B1949395 : Blo 1731066 1949395 := bstep (se 1 (by rfl) ⟨1462046, by rfl⟩ : syracuseStep 1949395 = 2924093) B2924093
theorem B2924275 : Blo 1731066 2924275 := bstep (se 1 (by rfl) ⟨2193206, by rfl⟩ : syracuseStep 2924275 = 4386413) B4386413
theorem B10534661 : Blo 1731066 10534661 := bstep (se 4 (by rfl) ⟨987624, by rfl⟩ : syracuseStep 10534661 = 1975249) B1975249
theorem B2596625 : Blo 1731066 2596625 := bstep (se 2 (by rfl) ⟨973734, by rfl⟩ : syracuseStep 2596625 = 1947469) B1947469
theorem B2465569 : Blo 1731066 2465569 := bstep (se 2 (by rfl) ⟨924588, by rfl⟩ : syracuseStep 2465569 = 1849177) B1849177
theorem B2596643 : Blo 1731066 2596643 := bstep (se 1 (by rfl) ⟨1947482, by rfl⟩ : syracuseStep 2596643 = 3894965) B3894965
theorem B2596673 : Blo 1731066 2596673 := bstep (se 2 (by rfl) ⟨973752, by rfl⟩ : syracuseStep 2596673 = 1947505) B1947505
theorem B4382545 : Blo 1731066 4382545 := bstep (se 2 (by rfl) ⟨1643454, by rfl⟩ : syracuseStep 4382545 = 3286909) B3286909
theorem B2596691 : Blo 1731066 2596691 := bstep (se 1 (by rfl) ⟨1947518, by rfl⟩ : syracuseStep 2596691 = 3895037) B3895037
theorem B1949539 : Blo 1731066 1949539 := bstep (se 1 (by rfl) ⟨1462154, by rfl⟩ : syracuseStep 1949539 = 2924309) B2924309
theorem B2596721 : Blo 1731066 2596721 := bstep (se 2 (by rfl) ⟨973770, by rfl⟩ : syracuseStep 2596721 = 1947541) B1947541
theorem B3899249 : Blo 1731066 3899249 := bstep (se 2 (by rfl) ⟨1462218, by rfl⟩ : syracuseStep 3899249 = 2924437) B2924437
theorem B2924417 : Blo 1731066 2924417 := bstep (se 2 (by rfl) ⟨1096656, by rfl⟩ : syracuseStep 2924417 = 2193313) B2193313
theorem B2596739 : Blo 1731066 2596739 := bstep (se 1 (by rfl) ⟨1947554, by rfl⟩ : syracuseStep 2596739 = 3895109) B3895109
theorem B3948419 : Blo 1731066 3948419 := bstep (se 1 (by rfl) ⟨2961314, by rfl⟩ : syracuseStep 3948419 = 5922629) B5922629
theorem B3899267 : Blo 1731066 3899267 := bstep (se 1 (by rfl) ⟨2924450, by rfl⟩ : syracuseStep 3899267 = 5848901) B5848901
theorem B2596769 : Blo 1731066 2596769 := bstep (se 2 (by rfl) ⟨973788, by rfl⟩ : syracuseStep 2596769 = 1947577) B1947577
theorem B5849009 : Blo 1731066 5849009 := bstep (se 2 (by rfl) ⟨2193378, by rfl⟩ : syracuseStep 5849009 = 4386757) B4386757
theorem B2596787 : Blo 1731066 2596787 := bstep (se 1 (by rfl) ⟨1947590, by rfl⟩ : syracuseStep 2596787 = 3895181) B3895181
theorem B2596817 : Blo 1731066 2596817 := bstep (se 2 (by rfl) ⟨973806, by rfl⟩ : syracuseStep 2596817 = 1947613) B1947613
theorem B2596835 : Blo 1731066 2596835 := bstep (se 1 (by rfl) ⟨1947626, by rfl⟩ : syracuseStep 2596835 = 3895253) B3895253
theorem B1949683 : Blo 1731066 1949683 := bstep (se 1 (by rfl) ⟨1462262, by rfl⟩ : syracuseStep 1949683 = 2924525) B2924525
theorem B3899393 : Blo 1731066 3899393 := bstep (se 2 (by rfl) ⟨1462272, by rfl⟩ : syracuseStep 3899393 = 2924545) B2924545
theorem B29982737 : Blo 1731066 29982737 := bstep (se 2 (by rfl) ⟨11243526, by rfl⟩ : syracuseStep 29982737 = 22487053) B22487053
theorem B2596889 : Blo 1731066 2596889 := bstep (se 2 (by rfl) ⟨973833, by rfl⟩ : syracuseStep 2596889 = 1947667) B1947667
theorem B4161611 : Blo 1731066 4161611 := bstep (se 1 (by rfl) ⟨3121208, by rfl⟩ : syracuseStep 4161611 = 6242417) B6242417
theorem B9494603 : Blo 1731066 9494603 := bstep (se 1 (by rfl) ⟨7120952, by rfl⟩ : syracuseStep 9494603 = 14241905) B14241905
theorem B2597003 : Blo 1731066 2597003 := bstep (se 1 (by rfl) ⟨1947752, by rfl⟩ : syracuseStep 2597003 = 3895505) B3895505
theorem B15794327 : Blo 1731066 15794327 := bstep (se 1 (by rfl) ⟨11845745, by rfl⟩ : syracuseStep 15794327 = 23691491) B23691491
theorem B2597015 : Blo 1731066 2597015 := bstep (se 1 (by rfl) ⟨1947761, by rfl⟩ : syracuseStep 2597015 = 3895523) B3895523
theorem B3121345 : Blo 1731066 3121345 := bstep (se 2 (by rfl) ⟨1170504, by rfl⟩ : syracuseStep 3121345 = 2341009) B2341009
theorem B13705421 : Blo 1731066 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B2597081 : Blo 1731066 2597081 := bstep (se 2 (by rfl) ⟨973905, by rfl⟩ : syracuseStep 2597081 = 1947811) B1947811
theorem B8765657 : Blo 1731066 8765657 := bstep (se 2 (by rfl) ⟨3287121, by rfl⟩ : syracuseStep 8765657 = 6574243) B6574243
theorem B6578435 : Blo 1731066 6578435 := bstep (se 1 (by rfl) ⟨4933826, by rfl⟩ : syracuseStep 6578435 = 9867653) B9867653
theorem B8323373 : Blo 1731066 8323373 := bstep (se 3 (by rfl) ⟨1560632, by rfl⟩ : syracuseStep 8323373 = 3121265) B3121265
theorem B4931891 : Blo 1731066 4931891 := bstep (se 1 (by rfl) ⟨3698918, by rfl⟩ : syracuseStep 4931891 = 7397837) B7397837
theorem B3948875 : Blo 1731066 3948875 := bstep (se 1 (by rfl) ⟨2961656, by rfl⟩ : syracuseStep 3948875 = 5923313) B5923313
theorem B2597195 : Blo 1731066 2597195 := bstep (se 1 (by rfl) ⟨1947896, by rfl⟩ : syracuseStep 2597195 = 3895793) B3895793
theorem B2597207 : Blo 1731066 2597207 := bstep (se 1 (by rfl) ⟨1947905, by rfl⟩ : syracuseStep 2597207 = 3895811) B3895811
theorem B2597273 : Blo 1731066 2597273 := bstep (se 2 (by rfl) ⟨973977, by rfl⟩ : syracuseStep 2597273 = 1947955) B1947955
theorem B5267891 : Blo 1731066 5267891 := bstep (se 1 (by rfl) ⟨3950918, by rfl⟩ : syracuseStep 5267891 = 7901837) B7901837
theorem B4161995 : Blo 1731066 4161995 := bstep (se 1 (by rfl) ⟨3121496, by rfl⟩ : syracuseStep 4161995 = 6242993) B6242993
theorem B4383193 : Blo 1731066 4383193 := bstep (se 2 (by rfl) ⟨1643697, by rfl⟩ : syracuseStep 4383193 = 3287395) B3287395
theorem B3162611 : Blo 1731066 3162611 := bstep (se 1 (by rfl) ⟨2371958, by rfl⟩ : syracuseStep 3162611 = 4743917) B4743917
theorem B2597387 : Blo 1731066 2597387 := bstep (se 1 (by rfl) ⟨1948040, by rfl⟩ : syracuseStep 2597387 = 3896081) B3896081
theorem B2597399 : Blo 1731066 2597399 := bstep (se 1 (by rfl) ⟨1948049, by rfl⟩ : syracuseStep 2597399 = 3896099) B3896099
theorem B2597465 : Blo 1731066 2597465 := bstep (se 2 (by rfl) ⟨974049, by rfl⟩ : syracuseStep 2597465 = 1948099) B1948099
theorem B29590109 : Blo 1731066 29590109 := bstep (se 3 (by rfl) ⟨5548145, by rfl⟩ : syracuseStep 29590109 = 11096291) B11096291
theorem B2597579 : Blo 1731066 2597579 := bstep (se 1 (by rfl) ⟨1948184, by rfl⟩ : syracuseStep 2597579 = 3896369) B3896369
theorem B6578891 : Blo 1731066 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B2597591 : Blo 1731066 2597591 := bstep (se 1 (by rfl) ⟨1948193, by rfl⟩ : syracuseStep 2597591 = 3896387) B3896387
theorem B2597657 : Blo 1731066 2597657 := bstep (se 2 (by rfl) ⟨974121, by rfl⟩ : syracuseStep 2597657 = 1948243) B1948243
theorem B21070637 : Blo 1731066 21070637 := bstep (se 3 (by rfl) ⟨3950744, by rfl⟩ : syracuseStep 21070637 = 7901489) B7901489
theorem B2597771 : Blo 1731066 2597771 := bstep (se 1 (by rfl) ⟨1948328, by rfl⟩ : syracuseStep 2597771 = 3896657) B3896657
theorem B3122059 : Blo 1731066 3122059 := bstep (se 1 (by rfl) ⟨2341544, by rfl⟩ : syracuseStep 3122059 = 4683089) B4683089
theorem B6579089 : Blo 1731066 6579089 := bstep (se 2 (by rfl) ⟨2467158, by rfl⟩ : syracuseStep 6579089 = 4934317) B4934317
theorem B2597783 : Blo 1731066 2597783 := bstep (se 1 (by rfl) ⟨1948337, by rfl⟩ : syracuseStep 2597783 = 3896675) B3896675
theorem B2597849 : Blo 1731066 2597849 := bstep (se 2 (by rfl) ⟨974193, by rfl⟩ : syracuseStep 2597849 = 1948387) B1948387
theorem B2597963 : Blo 1731066 2597963 := bstep (se 1 (by rfl) ⟨1948472, by rfl⟩ : syracuseStep 2597963 = 3896945) B3896945
theorem B2597975 : Blo 1731066 2597975 := bstep (se 1 (by rfl) ⟨1948481, by rfl⟩ : syracuseStep 2597975 = 3896963) B3896963
theorem B11248733 : Blo 1731066 11248733 := bstep (se 3 (by rfl) ⟨2109137, by rfl⟩ : syracuseStep 11248733 = 4218275) B4218275
theorem B13157477 : Blo 1731066 13157477 := bstep (se 4 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 13157477 = 2467027) B2467027
theorem B2598041 : Blo 1731066 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B21939461 : Blo 1731066 21939461 := bstep (se 4 (by rfl) ⟨2056824, by rfl⟩ : syracuseStep 21939461 = 4113649) B4113649
theorem B2598155 : Blo 1731066 2598155 := bstep (se 1 (by rfl) ⟨1948616, by rfl⟩ : syracuseStep 2598155 = 3897233) B3897233
theorem B2598167 : Blo 1731066 2598167 := bstep (se 1 (by rfl) ⟨1948625, by rfl⟩ : syracuseStep 2598167 = 3897251) B3897251
theorem B2598233 : Blo 1731066 2598233 := bstep (se 2 (by rfl) ⟨974337, by rfl⟩ : syracuseStep 2598233 = 1948675) B1948675
theorem B15803741 : Blo 1731066 15803741 := bstep (se 3 (by rfl) ⟨2963201, by rfl⟩ : syracuseStep 15803741 = 5926403) B5926403
theorem B3286423 : Blo 1731066 3286423 := bstep (se 1 (by rfl) ⟨2464817, by rfl⟩ : syracuseStep 3286423 = 4929635) B4929635
theorem B2598347 : Blo 1731066 2598347 := bstep (se 1 (by rfl) ⟨1948760, by rfl⟩ : syracuseStep 2598347 = 3897521) B3897521
theorem B2598359 : Blo 1731066 2598359 := bstep (se 1 (by rfl) ⟨1948769, by rfl⟩ : syracuseStep 2598359 = 3897539) B3897539
theorem B25322969 : Blo 1731066 25322969 := bstep (se 2 (by rfl) ⟨9496113, by rfl⟩ : syracuseStep 25322969 = 18992227) B18992227
theorem B13149701 : Blo 1731066 13149701 := bstep (se 4 (by rfl) ⟨1232784, by rfl⟩ : syracuseStep 13149701 = 2465569) B2465569
theorem B2598425 : Blo 1731066 2598425 := bstep (se 2 (by rfl) ⟨974409, by rfl⟩ : syracuseStep 2598425 = 1948819) B1948819
theorem B4384307 : Blo 1731066 4384307 := bstep (se 1 (by rfl) ⟨3288230, by rfl⟩ : syracuseStep 4384307 = 6576461) B6576461
theorem B13157963 : Blo 1731066 13157963 := bstep (se 1 (by rfl) ⟨9868472, by rfl⟩ : syracuseStep 13157963 = 19736945) B19736945
theorem B2598539 : Blo 1731066 2598539 := bstep (se 1 (by rfl) ⟨1948904, by rfl⟩ : syracuseStep 2598539 = 3897809) B3897809
theorem B5842583 : Blo 1731066 5842583 := bstep (se 1 (by rfl) ⟨4381937, by rfl⟩ : syracuseStep 5842583 = 8763875) B8763875
theorem B2598551 : Blo 1731066 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B6579863 : Blo 1731066 6579863 := bstep (se 1 (by rfl) ⟨4934897, by rfl⟩ : syracuseStep 6579863 = 9869795) B9869795
theorem B29607605 : Blo 1731066 29607605 := bstep (se 5 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 29607605 = 2775713) B2775713
theorem B2598617 : Blo 1731066 2598617 := bstep (se 2 (by rfl) ⟨974481, by rfl⟩ : syracuseStep 2598617 = 1948963) B1948963
theorem B16639789 : Blo 1731066 16639789 := bstep (se 3 (by rfl) ⟨3119960, by rfl⟩ : syracuseStep 16639789 = 6239921) B6239921
theorem B8767277 : Blo 1731066 8767277 := bstep (se 3 (by rfl) ⟨1643864, by rfl⟩ : syracuseStep 8767277 = 3287729) B3287729
theorem B5547827 : Blo 1731066 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B2598731 : Blo 1731066 2598731 := bstep (se 1 (by rfl) ⟨1949048, by rfl⟩ : syracuseStep 2598731 = 3898097) B3898097
theorem B13338443 : Blo 1731066 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B2598743 : Blo 1731066 2598743 := bstep (se 1 (by rfl) ⟨1949057, by rfl⟩ : syracuseStep 2598743 = 3898115) B3898115
theorem B5547865 : Blo 1731066 5547865 := bstep (se 2 (by rfl) ⟨2080449, by rfl⟩ : syracuseStep 5547865 = 4160899) B4160899
theorem B4384601 : Blo 1731066 4384601 := bstep (se 2 (by rfl) ⟨1644225, by rfl⟩ : syracuseStep 4384601 = 3288451) B3288451
theorem B4163417 : Blo 1731066 4163417 := bstep (se 2 (by rfl) ⟨1561281, by rfl⟩ : syracuseStep 4163417 = 3122563) B3122563
theorem B6580061 : Blo 1731066 6580061 := bstep (se 3 (by rfl) ⟨1233761, by rfl⟩ : syracuseStep 6580061 = 2467523) B2467523
theorem B14796695 : Blo 1731066 14796695 := bstep (se 1 (by rfl) ⟨11097521, by rfl⟩ : syracuseStep 14796695 = 22195043) B22195043
theorem B2598809 : Blo 1731066 2598809 := bstep (se 2 (by rfl) ⟨974553, by rfl⟩ : syracuseStep 2598809 = 1949107) B1949107
theorem B2598923 : Blo 1731066 2598923 := bstep (se 1 (by rfl) ⟨1949192, by rfl⟩ : syracuseStep 2598923 = 3898385) B3898385
theorem B7399441 : Blo 1731066 7399441 := bstep (se 2 (by rfl) ⟨2774790, by rfl⟩ : syracuseStep 7399441 = 5549581) B5549581
theorem B2598935 : Blo 1731066 2598935 := bstep (se 1 (by rfl) ⟨1949201, by rfl⟩ : syracuseStep 2598935 = 3898403) B3898403
theorem B4442177 : Blo 1731066 4442177 := bstep (se 2 (by rfl) ⟨1665816, by rfl⟩ : syracuseStep 4442177 = 3331633) B3331633
theorem B2599001 : Blo 1731066 2599001 := bstep (se 2 (by rfl) ⟨974625, by rfl⟩ : syracuseStep 2599001 = 1949251) B1949251
theorem B5843123 : Blo 1731066 5843123 := bstep (se 1 (by rfl) ⟨4382342, by rfl⟩ : syracuseStep 5843123 = 8764685) B8764685
theorem B3287243 : Blo 1731066 3287243 := bstep (se 1 (by rfl) ⟨2465432, by rfl⟩ : syracuseStep 3287243 = 4930865) B4930865
theorem B2599115 : Blo 1731066 2599115 := bstep (se 1 (by rfl) ⟨1949336, by rfl⟩ : syracuseStep 2599115 = 3898673) B3898673
theorem B2599127 : Blo 1731066 2599127 := bstep (se 1 (by rfl) ⟨1949345, by rfl⟩ : syracuseStep 2599127 = 3898691) B3898691
theorem B3287297 : Blo 1731066 3287297 := bstep (se 2 (by rfl) ⟨1232736, by rfl⟩ : syracuseStep 3287297 = 2465473) B2465473
theorem B2599193 : Blo 1731066 2599193 := bstep (se 2 (by rfl) ⟨974697, by rfl⟩ : syracuseStep 2599193 = 1949395) B1949395
theorem B4933963 : Blo 1731066 4933963 := bstep (se 1 (by rfl) ⟨3700472, by rfl⟩ : syracuseStep 4933963 = 7400945) B7400945
theorem B2599307 : Blo 1731066 2599307 := bstep (se 1 (by rfl) ⟨1949480, by rfl⟩ : syracuseStep 2599307 = 3898961) B3898961
theorem B2599319 : Blo 1731066 2599319 := bstep (se 1 (by rfl) ⟨1949489, by rfl⟩ : syracuseStep 2599319 = 3898979) B3898979
theorem B5843393 : Blo 1731066 5843393 := bstep (se 2 (by rfl) ⟨2191272, by rfl⟩ : syracuseStep 5843393 = 4382545) B4382545
theorem B2599385 : Blo 1731066 2599385 := bstep (se 2 (by rfl) ⟨974769, by rfl⟩ : syracuseStep 2599385 = 1949539) B1949539
theorem B7023107 : Blo 1731066 7023107 := bstep (se 1 (by rfl) ⟨5267330, by rfl⟩ : syracuseStep 7023107 = 10534661) B10534661
theorem B1731083 : Blo 1731066 1731083 := bstep (se 1 (by rfl) ⟨1298312, by rfl⟩ : syracuseStep 1731083 = 2596625) B2596625
theorem B1731095 : Blo 1731066 1731095 := bstep (se 1 (by rfl) ⟨1298321, by rfl⟩ : syracuseStep 1731095 = 2596643) B2596643
theorem B1731115 : Blo 1731066 1731115 := bstep (se 1 (by rfl) ⟨1298336, by rfl⟩ : syracuseStep 1731115 = 2596673) B2596673
theorem B1731127 : Blo 1731066 1731127 := bstep (se 1 (by rfl) ⟨1298345, by rfl⟩ : syracuseStep 1731127 = 2596691) B2596691
theorem B1731147 : Blo 1731066 1731147 := bstep (se 1 (by rfl) ⟨1298360, by rfl⟩ : syracuseStep 1731147 = 2596721) B2596721
theorem B2599499 : Blo 1731066 2599499 := bstep (se 1 (by rfl) ⟨1949624, by rfl⟩ : syracuseStep 2599499 = 3899249) B3899249
theorem B1731159 : Blo 1731066 1731159 := bstep (se 1 (by rfl) ⟨1298369, by rfl⟩ : syracuseStep 1731159 = 2596739) B2596739
theorem B2632279 : Blo 1731066 2632279 := bstep (se 1 (by rfl) ⟨1974209, by rfl⟩ : syracuseStep 2632279 = 3948419) B3948419
theorem B2599511 : Blo 1731066 2599511 := bstep (se 1 (by rfl) ⟨1949633, by rfl⟩ : syracuseStep 2599511 = 3899267) B3899267
theorem B1731179 : Blo 1731066 1731179 := bstep (se 1 (by rfl) ⟨1298384, by rfl⟩ : syracuseStep 1731179 = 2596769) B2596769
theorem B1731191 : Blo 1731066 1731191 := bstep (se 1 (by rfl) ⟨1298393, by rfl⟩ : syracuseStep 1731191 = 2596787) B2596787
theorem B1731211 : Blo 1731066 1731211 := bstep (se 1 (by rfl) ⟨1298408, by rfl⟩ : syracuseStep 1731211 = 2596817) B2596817
theorem B1731223 : Blo 1731066 1731223 := bstep (se 1 (by rfl) ⟨1298417, by rfl⟩ : syracuseStep 1731223 = 2596835) B2596835
theorem B2599577 : Blo 1731066 2599577 := bstep (se 2 (by rfl) ⟨974841, by rfl⟩ : syracuseStep 2599577 = 1949683) B1949683
theorem B1731243 : Blo 1731066 1731243 := bstep (se 1 (by rfl) ⟨1298432, by rfl⟩ : syracuseStep 1731243 = 2596865) B2596865
theorem B1731255 : Blo 1731066 1731255 := bstep (se 1 (by rfl) ⟨1298441, by rfl⟩ : syracuseStep 1731255 = 2596883) B2596883
theorem B1731275 : Blo 1731066 1731275 := bstep (se 1 (by rfl) ⟨1298456, by rfl⟩ : syracuseStep 1731275 = 2596913) B2596913
theorem B1731287 : Blo 1731066 1731287 := bstep (se 1 (by rfl) ⟨1298465, by rfl⟩ : syracuseStep 1731287 = 2596931) B2596931
theorem B1731307 : Blo 1731066 1731307 := bstep (se 1 (by rfl) ⟨1298480, by rfl⟩ : syracuseStep 1731307 = 2596961) B2596961
theorem B1731319 : Blo 1731066 1731319 := bstep (se 1 (by rfl) ⟨1298489, by rfl⟩ : syracuseStep 1731319 = 2596979) B2596979
theorem B1731339 : Blo 1731066 1731339 := bstep (se 1 (by rfl) ⟨1298504, by rfl⟩ : syracuseStep 1731339 = 2597009) B2597009
theorem B1731351 : Blo 1731066 1731351 := bstep (se 1 (by rfl) ⟨1298513, by rfl⟩ : syracuseStep 1731351 = 2597027) B2597027
theorem B1731371 : Blo 1731066 1731371 := bstep (se 1 (by rfl) ⟨1298528, by rfl⟩ : syracuseStep 1731371 = 2597057) B2597057
theorem B1731383 : Blo 1731066 1731383 := bstep (se 1 (by rfl) ⟨1298537, by rfl⟩ : syracuseStep 1731383 = 2597075) B2597075
theorem B4934465 : Blo 1731066 4934465 := bstep (se 2 (by rfl) ⟨1850424, by rfl⟩ : syracuseStep 4934465 = 3700849) B3700849
theorem B3697483 : Blo 1731066 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B1731403 : Blo 1731066 1731403 := bstep (se 1 (by rfl) ⟨1298552, by rfl⟩ : syracuseStep 1731403 = 2597105) B2597105
theorem B1731415 : Blo 1731066 1731415 := bstep (se 1 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 1731415 = 2597123) B2597123
theorem B1731435 : Blo 1731066 1731435 := bstep (se 1 (by rfl) ⟨1298576, by rfl⟩ : syracuseStep 1731435 = 2597153) B2597153
theorem B1731447 : Blo 1731066 1731447 := bstep (se 1 (by rfl) ⟨1298585, by rfl⟩ : syracuseStep 1731447 = 2597171) B2597171
theorem B1731467 : Blo 1731066 1731467 := bstep (se 1 (by rfl) ⟨1298600, by rfl⟩ : syracuseStep 1731467 = 2597201) B2597201
theorem B1731479 : Blo 1731066 1731479 := bstep (se 1 (by rfl) ⟨1298609, by rfl⟩ : syracuseStep 1731479 = 2597219) B2597219
theorem B1731499 : Blo 1731066 1731499 := bstep (se 1 (by rfl) ⟨1298624, by rfl⟩ : syracuseStep 1731499 = 2597249) B2597249
theorem B1731511 : Blo 1731066 1731511 := bstep (se 1 (by rfl) ⟨1298633, by rfl⟩ : syracuseStep 1731511 = 2597267) B2597267
theorem B1731531 : Blo 1731066 1731531 := bstep (se 1 (by rfl) ⟨1298648, by rfl⟩ : syracuseStep 1731531 = 2597297) B2597297
theorem B1731543 : Blo 1731066 1731543 := bstep (se 1 (by rfl) ⟨1298657, by rfl⟩ : syracuseStep 1731543 = 2597315) B2597315
theorem B5843933 : Blo 1731066 5843933 := bstep (se 3 (by rfl) ⟨1095737, by rfl⟩ : syracuseStep 5843933 = 2191475) B2191475
theorem B1731563 : Blo 1731066 1731563 := bstep (se 1 (by rfl) ⟨1298672, by rfl⟩ : syracuseStep 1731563 = 2597345) B2597345
theorem B1731575 : Blo 1731066 1731575 := bstep (se 1 (by rfl) ⟨1298681, by rfl⟩ : syracuseStep 1731575 = 2597363) B2597363
theorem B6573059 : Blo 1731066 6573059 := bstep (se 1 (by rfl) ⟨4929794, by rfl⟩ : syracuseStep 6573059 = 9859589) B9859589
theorem B1731595 : Blo 1731066 1731595 := bstep (se 1 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 1731595 = 2597393) B2597393
theorem B1731607 : Blo 1731066 1731607 := bstep (se 1 (by rfl) ⟨1298705, by rfl⟩ : syracuseStep 1731607 = 2597411) B2597411
theorem B1731627 : Blo 1731066 1731627 := bstep (se 1 (by rfl) ⟨1298720, by rfl⟩ : syracuseStep 1731627 = 2597441) B2597441
theorem B1731639 : Blo 1731066 1731639 := bstep (se 1 (by rfl) ⟨1298729, by rfl⟩ : syracuseStep 1731639 = 2597459) B2597459
theorem B3697739 : Blo 1731066 3697739 := bstep (se 1 (by rfl) ⟨2773304, by rfl⟩ : syracuseStep 3697739 = 5546609) B5546609
theorem B1731659 : Blo 1731066 1731659 := bstep (se 1 (by rfl) ⟨1298744, by rfl⟩ : syracuseStep 1731659 = 2597489) B2597489
theorem B1731671 : Blo 1731066 1731671 := bstep (se 1 (by rfl) ⟨1298753, by rfl⟩ : syracuseStep 1731671 = 2597507) B2597507
theorem B1731691 : Blo 1731066 1731691 := bstep (se 1 (by rfl) ⟨1298768, by rfl⟩ : syracuseStep 1731691 = 2597537) B2597537
theorem B1731703 : Blo 1731066 1731703 := bstep (se 1 (by rfl) ⟨1298777, by rfl⟩ : syracuseStep 1731703 = 2597555) B2597555
theorem B1731723 : Blo 1731066 1731723 := bstep (se 1 (by rfl) ⟨1298792, by rfl⟩ : syracuseStep 1731723 = 2597585) B2597585
theorem B1731735 : Blo 1731066 1731735 := bstep (se 1 (by rfl) ⟨1298801, by rfl⟩ : syracuseStep 1731735 = 2597603) B2597603
theorem B3288215 : Blo 1731066 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B25660567 : Blo 1731066 25660567 := bstep (se 1 (by rfl) ⟨19245425, by rfl⟩ : syracuseStep 25660567 = 38490851) B38490851
theorem B3951767 : Blo 1731066 3951767 := bstep (se 1 (by rfl) ⟨2963825, by rfl⟩ : syracuseStep 3951767 = 5927651) B5927651
theorem B4934807 : Blo 1731066 4934807 := bstep (se 1 (by rfl) ⟨3701105, by rfl⟩ : syracuseStep 4934807 = 7402211) B7402211
theorem B1731755 : Blo 1731066 1731755 := bstep (se 1 (by rfl) ⟨1298816, by rfl⟩ : syracuseStep 1731755 = 2597633) B2597633
theorem B1731767 : Blo 1731066 1731767 := bstep (se 1 (by rfl) ⟨1298825, by rfl⟩ : syracuseStep 1731767 = 2597651) B2597651
theorem B1731787 : Blo 1731066 1731787 := bstep (se 1 (by rfl) ⟨1298840, by rfl⟩ : syracuseStep 1731787 = 2597681) B2597681
theorem B1731799 : Blo 1731066 1731799 := bstep (se 1 (by rfl) ⟨1298849, by rfl⟩ : syracuseStep 1731799 = 2597699) B2597699
theorem B1731819 : Blo 1731066 1731819 := bstep (se 1 (by rfl) ⟨1298864, by rfl⟩ : syracuseStep 1731819 = 2597729) B2597729
theorem B1731831 : Blo 1731066 1731831 := bstep (se 1 (by rfl) ⟨1298873, by rfl⟩ : syracuseStep 1731831 = 2597747) B2597747
theorem B1731851 : Blo 1731066 1731851 := bstep (se 1 (by rfl) ⟨1298888, by rfl⟩ : syracuseStep 1731851 = 2597777) B2597777
theorem B1731863 : Blo 1731066 1731863 := bstep (se 1 (by rfl) ⟨1298897, by rfl⟩ : syracuseStep 1731863 = 2597795) B2597795
theorem B1731883 : Blo 1731066 1731883 := bstep (se 1 (by rfl) ⟨1298912, by rfl⟩ : syracuseStep 1731883 = 2597825) B2597825
theorem B1731895 : Blo 1731066 1731895 := bstep (se 1 (by rfl) ⟨1298921, by rfl⟩ : syracuseStep 1731895 = 2597843) B2597843
theorem B1731915 : Blo 1731066 1731915 := bstep (se 1 (by rfl) ⟨1298936, by rfl⟩ : syracuseStep 1731915 = 2597873) B2597873
theorem B1731927 : Blo 1731066 1731927 := bstep (se 1 (by rfl) ⟨1298945, by rfl⟩ : syracuseStep 1731927 = 2597891) B2597891
theorem B1731947 : Blo 1731066 1731947 := bstep (se 1 (by rfl) ⟨1298960, by rfl⟩ : syracuseStep 1731947 = 2597921) B2597921
theorem B24964469 : Blo 1731066 24964469 := bstep (se 5 (by rfl) ⟨1170209, by rfl⟩ : syracuseStep 24964469 = 2340419) B2340419
theorem B1731959 : Blo 1731066 1731959 := bstep (se 1 (by rfl) ⟨1298969, by rfl⟩ : syracuseStep 1731959 = 2597939) B2597939
theorem B1731979 : Blo 1731066 1731979 := bstep (se 1 (by rfl) ⟨1298984, by rfl⟩ : syracuseStep 1731979 = 2597969) B2597969
theorem B239857037 : Blo 1731066 239857037 := bstep (se 3 (by rfl) ⟨44973194, by rfl⟩ : syracuseStep 239857037 = 89946389) B89946389
theorem B1731991 : Blo 1731066 1731991 := bstep (se 1 (by rfl) ⟨1298993, by rfl⟩ : syracuseStep 1731991 = 2597987) B2597987
theorem B1732011 : Blo 1731066 1732011 := bstep (se 1 (by rfl) ⟨1299008, by rfl⟩ : syracuseStep 1732011 = 2598017) B2598017
theorem B1732023 : Blo 1731066 1732023 := bstep (se 1 (by rfl) ⟨1299017, by rfl⟩ : syracuseStep 1732023 = 2598035) B2598035
theorem B1732043 : Blo 1731066 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B4386251 : Blo 1731066 4386251 := bstep (se 1 (by rfl) ⟨3289688, by rfl⟩ : syracuseStep 4386251 = 6579377) B6579377
theorem B1732055 : Blo 1731066 1732055 := bstep (se 1 (by rfl) ⟨1299041, by rfl⟩ : syracuseStep 1732055 = 2598083) B2598083
theorem B1732075 : Blo 1731066 1732075 := bstep (se 1 (by rfl) ⟨1299056, by rfl⟩ : syracuseStep 1732075 = 2598113) B2598113
theorem B1732087 : Blo 1731066 1732087 := bstep (se 1 (by rfl) ⟨1299065, by rfl⟩ : syracuseStep 1732087 = 2598131) B2598131
theorem B1732107 : Blo 1731066 1732107 := bstep (se 1 (by rfl) ⟨1299080, by rfl⟩ : syracuseStep 1732107 = 2598161) B2598161
theorem B1732119 : Blo 1731066 1732119 := bstep (se 1 (by rfl) ⟨1299089, by rfl⟩ : syracuseStep 1732119 = 2598179) B2598179
theorem B1732139 : Blo 1731066 1732139 := bstep (se 1 (by rfl) ⟨1299104, by rfl⟩ : syracuseStep 1732139 = 2598209) B2598209
theorem B1732151 : Blo 1731066 1732151 := bstep (se 1 (by rfl) ⟨1299113, by rfl⟩ : syracuseStep 1732151 = 2598227) B2598227
theorem B1732171 : Blo 1731066 1732171 := bstep (se 1 (by rfl) ⟨1299128, by rfl⟩ : syracuseStep 1732171 = 2598257) B2598257
theorem B1732183 : Blo 1731066 1732183 := bstep (se 1 (by rfl) ⟨1299137, by rfl⟩ : syracuseStep 1732183 = 2598275) B2598275
theorem B7212637 : Blo 1731066 7212637 := bstep (se 3 (by rfl) ⟨1352369, by rfl⟩ : syracuseStep 7212637 = 2704739) B2704739
theorem B12480101 : Blo 1731066 12480101 := bstep (se 4 (by rfl) ⟨1170009, by rfl⟩ : syracuseStep 12480101 = 2340019) B2340019
theorem B1732203 : Blo 1731066 1732203 := bstep (se 1 (by rfl) ⟨1299152, by rfl⟩ : syracuseStep 1732203 = 2598305) B2598305
theorem B1732215 : Blo 1731066 1732215 := bstep (se 1 (by rfl) ⟨1299161, by rfl⟩ : syracuseStep 1732215 = 2598323) B2598323
theorem B1732235 : Blo 1731066 1732235 := bstep (se 1 (by rfl) ⟨1299176, by rfl⟩ : syracuseStep 1732235 = 2598353) B2598353
theorem B1732247 : Blo 1731066 1732247 := bstep (se 1 (by rfl) ⟨1299185, by rfl⟩ : syracuseStep 1732247 = 2598371) B2598371
theorem B1732267 : Blo 1731066 1732267 := bstep (se 1 (by rfl) ⟨1299200, by rfl⟩ : syracuseStep 1732267 = 2598401) B2598401
theorem B3288755 : Blo 1731066 3288755 := bstep (se 1 (by rfl) ⟨2466566, by rfl⟩ : syracuseStep 3288755 = 4933133) B4933133
theorem B1732279 : Blo 1731066 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B1732299 : Blo 1731066 1732299 := bstep (se 1 (by rfl) ⟨1299224, by rfl⟩ : syracuseStep 1732299 = 2598449) B2598449
theorem B1732311 : Blo 1731066 1732311 := bstep (se 1 (by rfl) ⟨1299233, by rfl⟩ : syracuseStep 1732311 = 2598467) B2598467
theorem B3895001 : Blo 1731066 3895001 := bstep (se 2 (by rfl) ⟨1460625, by rfl⟩ : syracuseStep 3895001 = 2921251) B2921251
theorem B1732331 : Blo 1731066 1732331 := bstep (se 1 (by rfl) ⟨1299248, by rfl⟩ : syracuseStep 1732331 = 2598497) B2598497
theorem B53325553 : Blo 1731066 53325553 := bstep (se 2 (by rfl) ⟨19997082, by rfl⟩ : syracuseStep 53325553 = 39994165) B39994165
theorem B1732343 : Blo 1731066 1732343 := bstep (se 1 (by rfl) ⟨1299257, by rfl⟩ : syracuseStep 1732343 = 2598515) B2598515
theorem B1732363 : Blo 1731066 1732363 := bstep (se 1 (by rfl) ⟨1299272, by rfl⟩ : syracuseStep 1732363 = 2598545) B2598545
theorem B14798609 : Blo 1731066 14798609 := bstep (se 2 (by rfl) ⟨5549478, by rfl⟩ : syracuseStep 14798609 = 11098957) B11098957
theorem B1732375 : Blo 1731066 1732375 := bstep (se 1 (by rfl) ⟨1299281, by rfl⟩ : syracuseStep 1732375 = 2598563) B2598563
theorem B1732395 : Blo 1731066 1732395 := bstep (se 1 (by rfl) ⟨1299296, by rfl⟩ : syracuseStep 1732395 = 2598593) B2598593
theorem B3895091 : Blo 1731066 3895091 := bstep (se 1 (by rfl) ⟨2921318, by rfl⟩ : syracuseStep 3895091 = 5842637) B5842637
theorem B1732407 : Blo 1731066 1732407 := bstep (se 1 (by rfl) ⟨1299305, by rfl⟩ : syracuseStep 1732407 = 2598611) B2598611
theorem B1732427 : Blo 1731066 1732427 := bstep (se 1 (by rfl) ⟨1299320, by rfl⟩ : syracuseStep 1732427 = 2598641) B2598641
theorem B3895127 : Blo 1731066 3895127 := bstep (se 1 (by rfl) ⟨2921345, by rfl⟩ : syracuseStep 3895127 = 5842691) B5842691
theorem B1732439 : Blo 1731066 1732439 := bstep (se 1 (by rfl) ⟨1299329, by rfl⟩ : syracuseStep 1732439 = 2598659) B2598659
theorem B1732459 : Blo 1731066 1732459 := bstep (se 1 (by rfl) ⟨1299344, by rfl⟩ : syracuseStep 1732459 = 2598689) B2598689
theorem B1732471 : Blo 1731066 1732471 := bstep (se 1 (by rfl) ⟨1299353, by rfl⟩ : syracuseStep 1732471 = 2598707) B2598707
theorem B13152131 : Blo 1731066 13152131 := bstep (se 1 (by rfl) ⟨9864098, by rfl⟩ : syracuseStep 13152131 = 19728197) B19728197
theorem B1732491 : Blo 1731066 1732491 := bstep (se 1 (by rfl) ⟨1299368, by rfl⟩ : syracuseStep 1732491 = 2598737) B2598737
theorem B1732503 : Blo 1731066 1732503 := bstep (se 1 (by rfl) ⟨1299377, by rfl⟩ : syracuseStep 1732503 = 2598755) B2598755
theorem B8327063 : Blo 1731066 8327063 := bstep (se 1 (by rfl) ⟨6245297, by rfl⟩ : syracuseStep 8327063 = 12490595) B12490595
theorem B1732523 : Blo 1731066 1732523 := bstep (se 1 (by rfl) ⟨1299392, by rfl⟩ : syracuseStep 1732523 = 2598785) B2598785
theorem B1732535 : Blo 1731066 1732535 := bstep (se 1 (by rfl) ⟨1299401, by rfl⟩ : syracuseStep 1732535 = 2598803) B2598803
theorem B1732555 : Blo 1731066 1732555 := bstep (se 1 (by rfl) ⟨1299416, by rfl⟩ : syracuseStep 1732555 = 2598833) B2598833
theorem B1732567 : Blo 1731066 1732567 := bstep (se 1 (by rfl) ⟨1299425, by rfl⟩ : syracuseStep 1732567 = 2598851) B2598851
theorem B1732587 : Blo 1731066 1732587 := bstep (se 1 (by rfl) ⟨1299440, by rfl⟩ : syracuseStep 1732587 = 2598881) B2598881
theorem B1732599 : Blo 1731066 1732599 := bstep (se 1 (by rfl) ⟨1299449, by rfl⟩ : syracuseStep 1732599 = 2598899) B2598899
theorem B3895307 : Blo 1731066 3895307 := bstep (se 1 (by rfl) ⟨2921480, by rfl⟩ : syracuseStep 3895307 = 5842961) B5842961
theorem B1732619 : Blo 1731066 1732619 := bstep (se 1 (by rfl) ⟨1299464, by rfl⟩ : syracuseStep 1732619 = 2598929) B2598929
theorem B1732631 : Blo 1731066 1732631 := bstep (se 1 (by rfl) ⟨1299473, by rfl⟩ : syracuseStep 1732631 = 2598947) B2598947
theorem B3698713 : Blo 1731066 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B1732651 : Blo 1731066 1732651 := bstep (se 1 (by rfl) ⟨1299488, by rfl⟩ : syracuseStep 1732651 = 2598977) B2598977
theorem B1732663 : Blo 1731066 1732663 := bstep (se 1 (by rfl) ⟨1299497, by rfl⟩ : syracuseStep 1732663 = 2598995) B2598995
theorem B3895361 : Blo 1731066 3895361 := bstep (se 2 (by rfl) ⟨1460760, by rfl⟩ : syracuseStep 3895361 = 2921521) B2921521
theorem B22491211 : Blo 1731066 22491211 := bstep (se 1 (by rfl) ⟨16868408, by rfl⟩ : syracuseStep 22491211 = 33736817) B33736817
theorem B5845067 : Blo 1731066 5845067 := bstep (se 1 (by rfl) ⟨4383800, by rfl⟩ : syracuseStep 5845067 = 8767601) B8767601
theorem B1732683 : Blo 1731066 1732683 := bstep (se 1 (by rfl) ⟨1299512, by rfl⟩ : syracuseStep 1732683 = 2599025) B2599025
theorem B1732695 : Blo 1731066 1732695 := bstep (se 1 (by rfl) ⟨1299521, by rfl⟩ : syracuseStep 1732695 = 2599043) B2599043
theorem B1732715 : Blo 1731066 1732715 := bstep (se 1 (by rfl) ⟨1299536, by rfl⟩ : syracuseStep 1732715 = 2599073) B2599073
theorem B1732727 : Blo 1731066 1732727 := bstep (se 1 (by rfl) ⟨1299545, by rfl⟩ : syracuseStep 1732727 = 2599091) B2599091
theorem B1732747 : Blo 1731066 1732747 := bstep (se 1 (by rfl) ⟨1299560, by rfl⟩ : syracuseStep 1732747 = 2599121) B2599121
theorem B1732759 : Blo 1731066 1732759 := bstep (se 1 (by rfl) ⟨1299569, by rfl⟩ : syracuseStep 1732759 = 2599139) B2599139
theorem B3289241 : Blo 1731066 3289241 := bstep (se 2 (by rfl) ⟨1233465, by rfl⟩ : syracuseStep 3289241 = 2466931) B2466931
theorem B1732779 : Blo 1731066 1732779 := bstep (se 1 (by rfl) ⟨1299584, by rfl⟩ : syracuseStep 1732779 = 2599169) B2599169
theorem B3698867 : Blo 1731066 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B1732791 : Blo 1731066 1732791 := bstep (se 1 (by rfl) ⟨1299593, by rfl⟩ : syracuseStep 1732791 = 2599187) B2599187
theorem B1732811 : Blo 1731066 1732811 := bstep (se 1 (by rfl) ⟨1299608, by rfl⟩ : syracuseStep 1732811 = 2599217) B2599217
theorem B1732823 : Blo 1731066 1732823 := bstep (se 1 (by rfl) ⟨1299617, by rfl⟩ : syracuseStep 1732823 = 2599235) B2599235
theorem B1732843 : Blo 1731066 1732843 := bstep (se 1 (by rfl) ⟨1299632, by rfl⟩ : syracuseStep 1732843 = 2599265) B2599265
theorem B1732855 : Blo 1731066 1732855 := bstep (se 1 (by rfl) ⟨1299641, by rfl⟩ : syracuseStep 1732855 = 2599283) B2599283
theorem B26661125 : Blo 1731066 26661125 := bstep (se 4 (by rfl) ⟨2499480, by rfl⟩ : syracuseStep 26661125 = 4998961) B4998961
theorem B2191627 : Blo 1731066 2191627 := bstep (se 1 (by rfl) ⟨1643720, by rfl⟩ : syracuseStep 2191627 = 3287441) B3287441
theorem B1732875 : Blo 1731066 1732875 := bstep (se 1 (by rfl) ⟨1299656, by rfl⟩ : syracuseStep 1732875 = 2599313) B2599313
theorem B1732887 : Blo 1731066 1732887 := bstep (se 1 (by rfl) ⟨1299665, by rfl⟩ : syracuseStep 1732887 = 2599331) B2599331
theorem B3895577 : Blo 1731066 3895577 := bstep (se 2 (by rfl) ⟨1460841, by rfl⟩ : syracuseStep 3895577 = 2921683) B2921683
theorem B1732907 : Blo 1731066 1732907 := bstep (se 1 (by rfl) ⟨1299680, by rfl⟩ : syracuseStep 1732907 = 2599361) B2599361
theorem B1732919 : Blo 1731066 1732919 := bstep (se 1 (by rfl) ⟨1299689, by rfl⟩ : syracuseStep 1732919 = 2599379) B2599379
theorem B5550401 : Blo 1731066 5550401 := bstep (se 2 (by rfl) ⟨2081400, by rfl⟩ : syracuseStep 5550401 = 4162801) B4162801
theorem B1732939 : Blo 1731066 1732939 := bstep (se 1 (by rfl) ⟨1299704, by rfl⟩ : syracuseStep 1732939 = 2599409) B2599409
theorem B1732951 : Blo 1731066 1732951 := bstep (se 1 (by rfl) ⟨1299713, by rfl⟩ : syracuseStep 1732951 = 2599427) B2599427
theorem B5845337 : Blo 1731066 5845337 := bstep (se 2 (by rfl) ⟨2192001, by rfl⟩ : syracuseStep 5845337 = 4384003) B4384003
theorem B1732971 : Blo 1731066 1732971 := bstep (se 1 (by rfl) ⟨1299728, by rfl⟩ : syracuseStep 1732971 = 2599457) B2599457
theorem B3895667 : Blo 1731066 3895667 := bstep (se 1 (by rfl) ⟨2921750, by rfl⟩ : syracuseStep 3895667 = 5843501) B5843501
theorem B1732983 : Blo 1731066 1732983 := bstep (se 1 (by rfl) ⟨1299737, by rfl⟩ : syracuseStep 1732983 = 2599475) B2599475
theorem B1733003 : Blo 1731066 1733003 := bstep (se 1 (by rfl) ⟨1299752, by rfl⟩ : syracuseStep 1733003 = 2599505) B2599505
theorem B48066965 : Blo 1731066 48066965 := bstep (se 6 (by rfl) ⟨1126569, by rfl⟩ : syracuseStep 48066965 = 2253139) B2253139
theorem B3895703 : Blo 1731066 3895703 := bstep (se 1 (by rfl) ⟨2921777, by rfl⟩ : syracuseStep 3895703 = 5843555) B5843555
theorem B1733015 : Blo 1731066 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B1733035 : Blo 1731066 1733035 := bstep (se 1 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 1733035 = 2599553) B2599553
theorem B1733047 : Blo 1731066 1733047 := bstep (se 1 (by rfl) ⟨1299785, by rfl⟩ : syracuseStep 1733047 = 2599571) B2599571
theorem B3895883 : Blo 1731066 3895883 := bstep (se 1 (by rfl) ⟨2921912, by rfl⟩ : syracuseStep 3895883 = 5843825) B5843825
theorem B4059763 : Blo 1731066 4059763 := bstep (se 1 (by rfl) ⟨3044822, by rfl⟩ : syracuseStep 4059763 = 6089645) B6089645
theorem B3895937 : Blo 1731066 3895937 := bstep (se 2 (by rfl) ⟨1460976, by rfl⟩ : syracuseStep 3895937 = 2921953) B2921953
theorem B3699379 : Blo 1731066 3699379 := bstep (se 1 (by rfl) ⟨2774534, by rfl⟩ : syracuseStep 3699379 = 5549069) B5549069
theorem B2921177 : Blo 1731066 2921177 := bstep (se 2 (by rfl) ⟨1095441, by rfl⟩ : syracuseStep 2921177 = 2190883) B2190883
theorem B6664925 : Blo 1731066 6664925 := bstep (se 3 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 6664925 = 2499347) B2499347
theorem B2921305 : Blo 1731066 2921305 := bstep (se 2 (by rfl) ⟨1095489, by rfl⟩ : syracuseStep 2921305 = 2190979) B2190979
theorem B3896153 : Blo 1731066 3896153 := bstep (se 2 (by rfl) ⟨1461057, by rfl⟩ : syracuseStep 3896153 = 2922115) B2922115
theorem B40555363 : Blo 1731066 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B3896243 : Blo 1731066 3896243 := bstep (se 1 (by rfl) ⟨2922182, by rfl⟩ : syracuseStep 3896243 = 5844365) B5844365
theorem B6329281 : Blo 1731066 6329281 := bstep (se 2 (by rfl) ⟨2373480, by rfl⟩ : syracuseStep 6329281 = 4746961) B4746961
theorem B3896279 : Blo 1731066 3896279 := bstep (se 1 (by rfl) ⟨2922209, by rfl⟩ : syracuseStep 3896279 = 5844419) B5844419
theorem B3609587 : Blo 1731066 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B5846039 : Blo 1731066 5846039 := bstep (se 1 (by rfl) ⟨4384529, by rfl⟩ : syracuseStep 5846039 = 8769059) B8769059
theorem B3748951 : Blo 1731066 3748951 := bstep (se 1 (by rfl) ⟨2811713, by rfl⟩ : syracuseStep 3748951 = 5623427) B5623427
theorem B7402585 : Blo 1731066 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B3896459 : Blo 1731066 3896459 := bstep (se 1 (by rfl) ⟨2922344, by rfl⟩ : syracuseStep 3896459 = 5844689) B5844689
theorem B12481715 : Blo 1731066 12481715 := bstep (se 1 (by rfl) ⟨9361286, by rfl⟩ : syracuseStep 12481715 = 18722573) B18722573
theorem B3896513 : Blo 1731066 3896513 := bstep (se 2 (by rfl) ⟨1461192, by rfl⟩ : syracuseStep 3896513 = 2922385) B2922385
theorem B2192599 : Blo 1731066 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B5551325 : Blo 1731066 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B3700055 : Blo 1731066 3700055 := bstep (se 1 (by rfl) ⟨2775041, by rfl⟩ : syracuseStep 3700055 = 5550083) B5550083
theorem B3700097 : Blo 1731066 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2921879 : Blo 1731066 2921879 := bstep (se 1 (by rfl) ⟨2191409, by rfl⟩ : syracuseStep 2921879 = 4382819) B4382819
theorem B3896729 : Blo 1731066 3896729 := bstep (se 2 (by rfl) ⟨1461273, by rfl⟩ : syracuseStep 3896729 = 2922547) B2922547
theorem B3896819 : Blo 1731066 3896819 := bstep (se 1 (by rfl) ⟨2922614, by rfl⟩ : syracuseStep 3896819 = 5845229) B5845229
theorem B2922007 : Blo 1731066 2922007 := bstep (se 1 (by rfl) ⟨2191505, by rfl⟩ : syracuseStep 2922007 = 4383011) B4383011
theorem B3896855 : Blo 1731066 3896855 := bstep (se 1 (by rfl) ⟨2922641, by rfl⟩ : syracuseStep 3896855 = 5845283) B5845283
theorem B5846579 : Blo 1731066 5846579 := bstep (se 1 (by rfl) ⟨4384934, by rfl⟩ : syracuseStep 5846579 = 8769869) B8769869
theorem B6239819 : Blo 1731066 6239819 := bstep (se 1 (by rfl) ⟨4679864, by rfl⟩ : syracuseStep 6239819 = 9359729) B9359729
theorem B8771165 : Blo 1731066 8771165 := bstep (se 3 (by rfl) ⟨1644593, by rfl⟩ : syracuseStep 8771165 = 3289187) B3289187
theorem B1849015 : Blo 1731066 1849015 := bstep (se 1 (by rfl) ⟨1386761, by rfl⟩ : syracuseStep 1849015 = 2773523) B2773523
theorem B3897035 : Blo 1731066 3897035 := bstep (se 1 (by rfl) ⟨2922776, by rfl⟩ : syracuseStep 3897035 = 5845553) B5845553
theorem B3897089 : Blo 1731066 3897089 := bstep (se 2 (by rfl) ⟨1461408, by rfl⟩ : syracuseStep 3897089 = 2922817) B2922817
theorem B7395137 : Blo 1731066 7395137 := bstep (se 2 (by rfl) ⟨2773176, by rfl⟩ : syracuseStep 7395137 = 5546353) B5546353
theorem B5846849 : Blo 1731066 5846849 := bstep (se 2 (by rfl) ⟨2192568, by rfl⟩ : syracuseStep 5846849 = 4385137) B4385137
theorem B1947595 : Blo 1731066 1947595 := bstep (se 1 (by rfl) ⟨1460696, by rfl⟩ : syracuseStep 1947595 = 2921393) B2921393
theorem B3897305 : Blo 1731066 3897305 := bstep (se 2 (by rfl) ⟨1461489, by rfl⟩ : syracuseStep 3897305 = 2922979) B2922979
theorem B4061171 : Blo 1731066 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B4003841 : Blo 1731066 4003841 := bstep (se 2 (by rfl) ⟨1501440, by rfl⟩ : syracuseStep 4003841 = 3002881) B3002881
theorem B14039075 : Blo 1731066 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B6576173 : Blo 1731066 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B3897395 : Blo 1731066 3897395 := bstep (se 1 (by rfl) ⟨2923046, by rfl⟩ : syracuseStep 3897395 = 5846093) B5846093
theorem B1947703 : Blo 1731066 1947703 := bstep (se 1 (by rfl) ⟨1460777, by rfl⟩ : syracuseStep 1947703 = 2921555) B2921555
theorem B3897431 : Blo 1731066 3897431 := bstep (se 1 (by rfl) ⟨2923073, by rfl⟩ : syracuseStep 3897431 = 5846147) B5846147
theorem B2922635 : Blo 1731066 2922635 := bstep (se 1 (by rfl) ⟨2191976, by rfl⟩ : syracuseStep 2922635 = 4383953) B4383953
theorem B1947883 : Blo 1731066 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B2922763 : Blo 1731066 2922763 := bstep (se 1 (by rfl) ⟨2192072, by rfl⟩ : syracuseStep 2922763 = 4384145) B4384145
theorem B3897611 : Blo 1731066 3897611 := bstep (se 1 (by rfl) ⟨2923208, by rfl⟩ : syracuseStep 3897611 = 5846417) B5846417
theorem B8763713 : Blo 1731066 8763713 := bstep (se 2 (by rfl) ⟨3286392, by rfl⟩ : syracuseStep 8763713 = 6572785) B6572785
theorem B3897665 : Blo 1731066 3897665 := bstep (se 2 (by rfl) ⟨1461624, by rfl⟩ : syracuseStep 3897665 = 2923249) B2923249
theorem B3512641 : Blo 1731066 3512641 := bstep (se 2 (by rfl) ⟨1317240, by rfl⟩ : syracuseStep 3512641 = 2634481) B2634481
theorem B1947991 : Blo 1731066 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B5847389 : Blo 1731066 5847389 := bstep (se 3 (by rfl) ⟨1096385, by rfl⟩ : syracuseStep 5847389 = 2192771) B2192771
theorem B21076325 : Blo 1731066 21076325 := bstep (se 4 (by rfl) ⟨1975905, by rfl⟩ : syracuseStep 21076325 = 3951811) B3951811
theorem B4929943 : Blo 1731066 4929943 := bstep (se 1 (by rfl) ⟨3697457, by rfl⟩ : syracuseStep 4929943 = 7394915) B7394915
theorem B2922905 : Blo 1731066 2922905 := bstep (se 2 (by rfl) ⟨1096089, by rfl⟩ : syracuseStep 2922905 = 2192179) B2192179
theorem B6846893 : Blo 1731066 6846893 := bstep (se 3 (by rfl) ⟨1283792, by rfl⟩ : syracuseStep 6846893 = 2567585) B2567585
theorem B6240685 : Blo 1731066 6240685 := bstep (se 3 (by rfl) ⟨1170128, by rfl⟩ : syracuseStep 6240685 = 2340257) B2340257
theorem B1849835 : Blo 1731066 1849835 := bstep (se 1 (by rfl) ⟨1387376, by rfl⟩ : syracuseStep 1849835 = 2774753) B2774753
theorem B1948171 : Blo 1731066 1948171 := bstep (se 1 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 1948171 = 2922257) B2922257
theorem B2923033 : Blo 1731066 2923033 := bstep (se 2 (by rfl) ⟨1096137, by rfl⟩ : syracuseStep 2923033 = 2192275) B2192275
theorem B3897881 : Blo 1731066 3897881 := bstep (se 2 (by rfl) ⟨1461705, by rfl⟩ : syracuseStep 3897881 = 2923411) B2923411
theorem B1849963 : Blo 1731066 1849963 := bstep (se 1 (by rfl) ⟨1387472, by rfl⟩ : syracuseStep 1849963 = 2774945) B2774945
theorem B3897971 : Blo 1731066 3897971 := bstep (se 1 (by rfl) ⟨2923478, by rfl⟩ : syracuseStep 3897971 = 5846957) B5846957
theorem B1948279 : Blo 1731066 1948279 := bstep (se 1 (by rfl) ⟨1461209, by rfl⟩ : syracuseStep 1948279 = 2922419) B2922419
theorem B3898007 : Blo 1731066 3898007 := bstep (se 1 (by rfl) ⟨2923505, by rfl⟩ : syracuseStep 3898007 = 5847011) B5847011
theorem B3799819 : Blo 1731066 3799819 := bstep (se 1 (by rfl) ⟨2849864, by rfl⟩ : syracuseStep 3799819 = 5699729) B5699729
theorem B1948459 : Blo 1731066 1948459 := bstep (se 1 (by rfl) ⟨1461344, by rfl⟩ : syracuseStep 1948459 = 2922689) B2922689
theorem B6576947 : Blo 1731066 6576947 := bstep (se 1 (by rfl) ⟨4932710, by rfl⟩ : syracuseStep 6576947 = 9865421) B9865421
theorem B3898187 : Blo 1731066 3898187 := bstep (se 1 (by rfl) ⟨2923640, by rfl⟩ : syracuseStep 3898187 = 5847281) B5847281
theorem B3898241 : Blo 1731066 3898241 := bstep (se 2 (by rfl) ⟨1461840, by rfl⟩ : syracuseStep 3898241 = 2923681) B2923681
theorem B1948567 : Blo 1731066 1948567 := bstep (se 1 (by rfl) ⟨1461425, by rfl⟩ : syracuseStep 1948567 = 2922851) B2922851
theorem B12483533 : Blo 1731066 12483533 := bstep (se 3 (by rfl) ⟨2340662, by rfl⟩ : syracuseStep 12483533 = 4681325) B4681325
theorem B21077009 : Blo 1731066 21077009 := bstep (se 2 (by rfl) ⟨7903878, by rfl⟩ : syracuseStep 21077009 = 15807757) B15807757
theorem B2079767 : Blo 1731066 2079767 := bstep (se 1 (by rfl) ⟨1559825, by rfl⟩ : syracuseStep 2079767 = 3119651) B3119651
theorem B1948747 : Blo 1731066 1948747 := bstep (se 1 (by rfl) ⟨1461560, by rfl⟩ : syracuseStep 1948747 = 2923121) B2923121
theorem B2923607 : Blo 1731066 2923607 := bstep (se 1 (by rfl) ⟨2192705, by rfl⟩ : syracuseStep 2923607 = 4385411) B4385411
theorem B3898457 : Blo 1731066 3898457 := bstep (se 2 (by rfl) ⟨1461921, by rfl⟩ : syracuseStep 3898457 = 2923843) B2923843
theorem B11099267 : Blo 1731066 11099267 := bstep (se 1 (by rfl) ⟨8324450, by rfl⟩ : syracuseStep 11099267 = 16648901) B16648901
theorem B4381847 : Blo 1731066 4381847 := bstep (se 1 (by rfl) ⟨3286385, by rfl⟩ : syracuseStep 4381847 = 6572771) B6572771
theorem B3898547 : Blo 1731066 3898547 := bstep (se 1 (by rfl) ⟨2923910, by rfl⟩ : syracuseStep 3898547 = 5847821) B5847821
theorem B1948855 : Blo 1731066 1948855 := bstep (se 1 (by rfl) ⟨1461641, by rfl⟩ : syracuseStep 1948855 = 2923283) B2923283
theorem B7396555 : Blo 1731066 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B13155533 : Blo 1731066 13155533 := bstep (se 3 (by rfl) ⟨2466662, by rfl⟩ : syracuseStep 13155533 = 4933325) B4933325
theorem B2923735 : Blo 1731066 2923735 := bstep (se 1 (by rfl) ⟨2192801, by rfl⟩ : syracuseStep 2923735 = 4385603) B4385603
theorem B3898583 : Blo 1731066 3898583 := bstep (se 1 (by rfl) ⟨2923937, by rfl⟩ : syracuseStep 3898583 = 5847875) B5847875
theorem B44391725 : Blo 1731066 44391725 := bstep (se 3 (by rfl) ⟨8323448, by rfl⟩ : syracuseStep 44391725 = 16646897) B16646897
theorem B21650753 : Blo 1731066 21650753 := bstep (se 2 (by rfl) ⟨8119032, by rfl⟩ : syracuseStep 21650753 = 16238065) B16238065
theorem B2080075 : Blo 1731066 2080075 := bstep (se 1 (by rfl) ⟨1560056, by rfl⟩ : syracuseStep 2080075 = 3120113) B3120113
theorem B1949035 : Blo 1731066 1949035 := bstep (se 1 (by rfl) ⟨1461776, by rfl⟩ : syracuseStep 1949035 = 2923553) B2923553
theorem B3898763 : Blo 1731066 3898763 := bstep (se 1 (by rfl) ⟨2924072, by rfl⟩ : syracuseStep 3898763 = 5848145) B5848145
theorem B119922061 : Blo 1731066 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B3898817 : Blo 1731066 3898817 := bstep (se 2 (by rfl) ⟨1462056, by rfl⟩ : syracuseStep 3898817 = 2924113) B2924113
theorem B5848523 : Blo 1731066 5848523 := bstep (se 1 (by rfl) ⟨4386392, by rfl⟩ : syracuseStep 5848523 = 8772785) B8772785
theorem B1949143 : Blo 1731066 1949143 := bstep (se 1 (by rfl) ⟨1461857, by rfl⟩ : syracuseStep 1949143 = 2923715) B2923715
theorem B7396829 : Blo 1731066 7396829 := bstep (se 3 (by rfl) ⟨1386905, by rfl⟩ : syracuseStep 7396829 = 2773811) B2773811
theorem B1949323 : Blo 1731066 1949323 := bstep (se 1 (by rfl) ⟨1461992, by rfl⟩ : syracuseStep 1949323 = 2923985) B2923985
theorem B8773271 : Blo 1731066 8773271 := bstep (se 1 (by rfl) ⟨6579953, by rfl⟩ : syracuseStep 8773271 = 13159907) B13159907
theorem B3899033 : Blo 1731066 3899033 := bstep (se 2 (by rfl) ⟨1462137, by rfl⟩ : syracuseStep 3899033 = 2924275) B2924275
theorem B13156019 : Blo 1731066 13156019 := bstep (se 1 (by rfl) ⟨9867014, by rfl⟩ : syracuseStep 13156019 = 19734029) B19734029
theorem B4931275 : Blo 1731066 4931275 := bstep (se 1 (by rfl) ⟨3698456, by rfl⟩ : syracuseStep 4931275 = 7396913) B7396913
theorem B5848793 : Blo 1731066 5848793 := bstep (se 2 (by rfl) ⟨2193297, by rfl⟩ : syracuseStep 5848793 = 4386595) B4386595
theorem B3899123 : Blo 1731066 3899123 := bstep (se 1 (by rfl) ⟨2924342, by rfl⟩ : syracuseStep 3899123 = 5848685) B5848685
theorem B1949431 : Blo 1731066 1949431 := bstep (se 1 (by rfl) ⟨1462073, by rfl⟩ : syracuseStep 1949431 = 2924147) B2924147
theorem B2596619 : Blo 1731066 2596619 := bstep (se 1 (by rfl) ⟨1947464, by rfl⟩ : syracuseStep 2596619 = 3894929) B3894929
theorem B2596631 : Blo 1731066 2596631 := bstep (se 1 (by rfl) ⟨1947473, by rfl⟩ : syracuseStep 2596631 = 3894947) B3894947
theorem B3899159 : Blo 1731066 3899159 := bstep (se 1 (by rfl) ⟨2924369, by rfl⟩ : syracuseStep 3899159 = 5848739) B5848739
theorem B2924363 : Blo 1731066 2924363 := bstep (se 1 (by rfl) ⟨2193272, by rfl⟩ : syracuseStep 2924363 = 4386545) B4386545
theorem B2596697 : Blo 1731066 2596697 := bstep (se 2 (by rfl) ⟨973761, by rfl⟩ : syracuseStep 2596697 = 1947523) B1947523
theorem B9863005 : Blo 1731066 9863005 := bstep (se 3 (by rfl) ⟨1849313, by rfl⟩ : syracuseStep 9863005 = 3698627) B3698627
theorem B37470053 : Blo 1731066 37470053 := bstep (se 4 (by rfl) ⟨3512817, by rfl⟩ : syracuseStep 37470053 = 7025635) B7025635
theorem B1949611 : Blo 1731066 1949611 := bstep (se 1 (by rfl) ⟨1462208, by rfl⟩ : syracuseStep 1949611 = 2924417) B2924417
theorem B4382657 : Blo 1731066 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B4218817 : Blo 1731066 4218817 := bstep (se 2 (by rfl) ⟨1582056, by rfl⟩ : syracuseStep 4218817 = 3164113) B3164113
theorem B2596811 : Blo 1731066 2596811 := bstep (se 1 (by rfl) ⟨1947608, by rfl⟩ : syracuseStep 2596811 = 3895217) B3895217
theorem B2924491 : Blo 1731066 2924491 := bstep (se 1 (by rfl) ⟨2193368, by rfl⟩ : syracuseStep 2924491 = 4386737) B4386737
theorem B3899339 : Blo 1731066 3899339 := bstep (se 1 (by rfl) ⟨2924504, by rfl⟩ : syracuseStep 3899339 = 5849009) B5849009
theorem B2596823 : Blo 1731066 2596823 := bstep (se 1 (by rfl) ⟨1947617, by rfl⟩ : syracuseStep 2596823 = 3895235) B3895235
theorem B4931549 : Blo 1731066 4931549 := bstep (se 3 (by rfl) ⟨924665, by rfl⟩ : syracuseStep 4931549 = 1849331) B1849331
theorem B2596871 : Blo 1731066 2596871 := bstep (se 1 (by rfl) ⟨1947653, by rfl⟩ : syracuseStep 2596871 = 3895307) B3895307
theorem B4931617 : Blo 1731066 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B2596907 : Blo 1731066 2596907 := bstep (se 1 (by rfl) ⟨1947680, by rfl⟩ : syracuseStep 2596907 = 3895361) B3895361
theorem B79953965 : Blo 1731066 79953965 := bstep (se 3 (by rfl) ⟨14991368, by rfl⟩ : syracuseStep 79953965 = 29982737) B29982737
theorem B5546045 : Blo 1731066 5546045 := bstep (se 3 (by rfl) ⟨1039883, by rfl⟩ : syracuseStep 5546045 = 2079767) B2079767
theorem B2596937 : Blo 1731066 2596937 := bstep (se 2 (by rfl) ⟨973851, by rfl⟩ : syracuseStep 2596937 = 1947703) B1947703
theorem B2465911 : Blo 1731066 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B2597051 : Blo 1731066 2597051 := bstep (se 1 (by rfl) ⟨1947788, by rfl⟩ : syracuseStep 2597051 = 3895577) B3895577
theorem B2597111 : Blo 1731066 2597111 := bstep (se 1 (by rfl) ⟨1947833, by rfl⟩ : syracuseStep 2597111 = 3895667) B3895667
theorem B4161793 : Blo 1731066 4161793 := bstep (se 2 (by rfl) ⟨1560672, by rfl⟩ : syracuseStep 4161793 = 3121345) B3121345
theorem B2597135 : Blo 1731066 2597135 := bstep (se 1 (by rfl) ⟨1947851, by rfl⟩ : syracuseStep 2597135 = 3895703) B3895703
theorem B2597177 : Blo 1731066 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B2597255 : Blo 1731066 2597255 := bstep (se 1 (by rfl) ⟨1947941, by rfl⟩ : syracuseStep 2597255 = 3895883) B3895883
theorem B19726739 : Blo 1731066 19726739 := bstep (se 1 (by rfl) ⟨14795054, by rfl⟩ : syracuseStep 19726739 = 29590109) B29590109
theorem B2597291 : Blo 1731066 2597291 := bstep (se 1 (by rfl) ⟨1947968, by rfl⟩ : syracuseStep 2597291 = 3895937) B3895937
theorem B6578617 : Blo 1731066 6578617 := bstep (se 2 (by rfl) ⟨2466981, by rfl⟩ : syracuseStep 6578617 = 4933963) B4933963
theorem B2597321 : Blo 1731066 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B8765981 : Blo 1731066 8765981 := bstep (se 3 (by rfl) ⟨1643621, by rfl⟩ : syracuseStep 8765981 = 3287243) B3287243
theorem B2597435 : Blo 1731066 2597435 := bstep (se 1 (by rfl) ⟨1948076, by rfl⟩ : syracuseStep 2597435 = 3896153) B3896153
theorem B2597495 : Blo 1731066 2597495 := bstep (se 1 (by rfl) ⟨1948121, by rfl⟩ : syracuseStep 2597495 = 3896243) B3896243
theorem B2597519 : Blo 1731066 2597519 := bstep (se 1 (by rfl) ⟨1948139, by rfl⟩ : syracuseStep 2597519 = 3896279) B3896279
theorem B2597561 : Blo 1731066 2597561 := bstep (se 2 (by rfl) ⟨974085, by rfl⟩ : syracuseStep 2597561 = 1948171) B1948171
theorem B2597639 : Blo 1731066 2597639 := bstep (se 1 (by rfl) ⟨1948229, by rfl⟩ : syracuseStep 2597639 = 3896459) B3896459
theorem B2597675 : Blo 1731066 2597675 := bstep (se 1 (by rfl) ⟨1948256, by rfl⟩ : syracuseStep 2597675 = 3896513) B3896513
theorem B2466617 : Blo 1731066 2466617 := bstep (se 2 (by rfl) ⟨924981, by rfl⟩ : syracuseStep 2466617 = 1849963) B1849963
theorem B2597705 : Blo 1731066 2597705 := bstep (se 2 (by rfl) ⟨974139, by rfl⟩ : syracuseStep 2597705 = 1948279) B1948279
theorem B2466703 : Blo 1731066 2466703 := bstep (se 1 (by rfl) ⟨1850027, by rfl⟩ : syracuseStep 2466703 = 3700055) B3700055
theorem B10535827 : Blo 1731066 10535827 := bstep (se 1 (by rfl) ⟨7901870, by rfl⟩ : syracuseStep 10535827 = 15803741) B15803741
theorem B4932505 : Blo 1731066 4932505 := bstep (se 2 (by rfl) ⟨1849689, by rfl⟩ : syracuseStep 4932505 = 3699379) B3699379
theorem B2466731 : Blo 1731066 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B2597819 : Blo 1731066 2597819 := bstep (se 1 (by rfl) ⟨1948364, by rfl⟩ : syracuseStep 2597819 = 3896729) B3896729
theorem B2597879 : Blo 1731066 2597879 := bstep (se 1 (by rfl) ⟨1948409, by rfl⟩ : syracuseStep 2597879 = 3896819) B3896819
theorem B8766467 : Blo 1731066 8766467 := bstep (se 1 (by rfl) ⟨6574850, by rfl⟩ : syracuseStep 8766467 = 13149701) B13149701
theorem B2597903 : Blo 1731066 2597903 := bstep (se 1 (by rfl) ⟨1948427, by rfl⟩ : syracuseStep 2597903 = 3896855) B3896855
theorem B2597945 : Blo 1731066 2597945 := bstep (se 2 (by rfl) ⟨974229, by rfl⟩ : syracuseStep 2597945 = 1948459) B1948459
theorem B2598023 : Blo 1731066 2598023 := bstep (se 1 (by rfl) ⟨1948517, by rfl⟩ : syracuseStep 2598023 = 3897035) B3897035
theorem B2598059 : Blo 1731066 2598059 := bstep (se 1 (by rfl) ⟨1948544, by rfl⟩ : syracuseStep 2598059 = 3897089) B3897089
theorem B4162745 : Blo 1731066 4162745 := bstep (se 2 (by rfl) ⟨1561029, by rfl⟩ : syracuseStep 4162745 = 3122059) B3122059
theorem B2598089 : Blo 1731066 2598089 := bstep (se 2 (by rfl) ⟨974283, by rfl⟩ : syracuseStep 2598089 = 1948567) B1948567
theorem B67527917 : Blo 1731066 67527917 := bstep (se 3 (by rfl) ⟨12661484, by rfl⟩ : syracuseStep 67527917 = 25322969) B25322969
theorem B8439041 : Blo 1731066 8439041 := bstep (se 2 (by rfl) ⟨3164640, by rfl⟩ : syracuseStep 8439041 = 6329281) B6329281
theorem B9864463 : Blo 1731066 9864463 := bstep (se 1 (by rfl) ⟨7398347, by rfl⟩ : syracuseStep 9864463 = 14796695) B14796695
theorem B4932893 : Blo 1731066 4932893 := bstep (se 3 (by rfl) ⟨924917, by rfl⟩ : syracuseStep 4932893 = 1849835) B1849835
theorem B2598203 : Blo 1731066 2598203 := bstep (se 1 (by rfl) ⟨1948652, by rfl⟩ : syracuseStep 2598203 = 3897305) B3897305
theorem B4384115 : Blo 1731066 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B2598263 : Blo 1731066 2598263 := bstep (se 1 (by rfl) ⟨1948697, by rfl⟩ : syracuseStep 2598263 = 3897395) B3897395
theorem B2598287 : Blo 1731066 2598287 := bstep (se 1 (by rfl) ⟨1948715, by rfl⟩ : syracuseStep 2598287 = 3897431) B3897431
theorem B2598329 : Blo 1731066 2598329 := bstep (se 2 (by rfl) ⟨974373, by rfl⟩ : syracuseStep 2598329 = 1948747) B1948747
theorem B4998601 : Blo 1731066 4998601 := bstep (se 2 (by rfl) ⟨1874475, by rfl⟩ : syracuseStep 4998601 = 3748951) B3748951
theorem B2598407 : Blo 1731066 2598407 := bstep (se 1 (by rfl) ⟨1948805, by rfl⟩ : syracuseStep 2598407 = 3897611) B3897611
theorem B5842475 : Blo 1731066 5842475 := bstep (se 1 (by rfl) ⟨4381856, by rfl⟩ : syracuseStep 5842475 = 8763713) B8763713
theorem B2598443 : Blo 1731066 2598443 := bstep (se 1 (by rfl) ⟨1948832, by rfl⟩ : syracuseStep 2598443 = 3897665) B3897665
theorem B14050883 : Blo 1731066 14050883 := bstep (se 1 (by rfl) ⟨10538162, by rfl⟩ : syracuseStep 14050883 = 21076325) B21076325
theorem B2598473 : Blo 1731066 2598473 := bstep (se 2 (by rfl) ⟨974427, by rfl⟩ : syracuseStep 2598473 = 1948855) B1948855
theorem B4564595 : Blo 1731066 4564595 := bstep (se 1 (by rfl) ⟨3423446, by rfl⟩ : syracuseStep 4564595 = 6846893) B6846893
theorem B2598587 : Blo 1731066 2598587 := bstep (se 1 (by rfl) ⟨1948940, by rfl⟩ : syracuseStep 2598587 = 3897881) B3897881
theorem B2598647 : Blo 1731066 2598647 := bstep (se 1 (by rfl) ⟨1948985, by rfl⟩ : syracuseStep 2598647 = 3897971) B3897971
theorem B2598671 : Blo 1731066 2598671 := bstep (se 1 (by rfl) ⟨1949003, by rfl⟩ : syracuseStep 2598671 = 3898007) B3898007
theorem B2598713 : Blo 1731066 2598713 := bstep (se 2 (by rfl) ⟨974517, by rfl⟩ : syracuseStep 2598713 = 1949035) B1949035
theorem B4384631 : Blo 1731066 4384631 := bstep (se 1 (by rfl) ⟨3288473, by rfl⟩ : syracuseStep 4384631 = 6576947) B6576947
theorem B2598791 : Blo 1731066 2598791 := bstep (se 1 (by rfl) ⟨1949093, by rfl⟩ : syracuseStep 2598791 = 3898187) B3898187
theorem B2598827 : Blo 1731066 2598827 := bstep (se 1 (by rfl) ⟨1949120, by rfl⟩ : syracuseStep 2598827 = 3898241) B3898241
theorem B2598857 : Blo 1731066 2598857 := bstep (se 2 (by rfl) ⟨974571, by rfl⟩ : syracuseStep 2598857 = 1949143) B1949143
theorem B14051339 : Blo 1731066 14051339 := bstep (se 1 (by rfl) ⟨10538504, by rfl⟩ : syracuseStep 14051339 = 21077009) B21077009
theorem B2598971 : Blo 1731066 2598971 := bstep (se 1 (by rfl) ⟨1949228, by rfl⟩ : syracuseStep 2598971 = 3898457) B3898457
theorem B7399511 : Blo 1731066 7399511 := bstep (se 1 (by rfl) ⟨5549633, by rfl⟩ : syracuseStep 7399511 = 11099267) B11099267
theorem B2599031 : Blo 1731066 2599031 := bstep (se 1 (by rfl) ⟨1949273, by rfl⟩ : syracuseStep 2599031 = 3898547) B3898547
theorem B2599055 : Blo 1731066 2599055 := bstep (se 1 (by rfl) ⟨1949291, by rfl⟩ : syracuseStep 2599055 = 3898583) B3898583
theorem B2599097 : Blo 1731066 2599097 := bstep (se 2 (by rfl) ⟨974661, by rfl⟩ : syracuseStep 2599097 = 1949323) B1949323
theorem B2599175 : Blo 1731066 2599175 := bstep (se 1 (by rfl) ⟨1949381, by rfl⟩ : syracuseStep 2599175 = 3898763) B3898763
theorem B2599211 : Blo 1731066 2599211 := bstep (se 1 (by rfl) ⟨1949408, by rfl⟩ : syracuseStep 2599211 = 3898817) B3898817
theorem B71100737 : Blo 1731066 71100737 := bstep (se 2 (by rfl) ⟨26662776, by rfl⟩ : syracuseStep 71100737 = 53325553) B53325553
theorem B2599241 : Blo 1731066 2599241 := bstep (se 2 (by rfl) ⟨974715, by rfl⟩ : syracuseStep 2599241 = 1949431) B1949431
theorem B22186385 : Blo 1731066 22186385 := bstep (se 2 (by rfl) ⟨8319894, by rfl⟩ : syracuseStep 22186385 = 16639789) B16639789
theorem B86608277 : Blo 1731066 86608277 := bstep (se 6 (by rfl) ⟨2029881, by rfl⟩ : syracuseStep 86608277 = 4059763) B4059763
theorem B2599355 : Blo 1731066 2599355 := bstep (se 1 (by rfl) ⟨1949516, by rfl⟩ : syracuseStep 2599355 = 3899033) B3899033
theorem B13150673 : Blo 1731066 13150673 := bstep (se 2 (by rfl) ⟨4931502, by rfl⟩ : syracuseStep 13150673 = 9863005) B9863005
theorem B2599415 : Blo 1731066 2599415 := bstep (se 1 (by rfl) ⟨1949561, by rfl⟩ : syracuseStep 2599415 = 3899123) B3899123
theorem B1731079 : Blo 1731066 1731079 := bstep (se 1 (by rfl) ⟨1298309, by rfl⟩ : syracuseStep 1731079 = 2596619) B2596619
theorem B9865739 : Blo 1731066 9865739 := bstep (se 1 (by rfl) ⟨7399304, by rfl⟩ : syracuseStep 9865739 = 14798609) B14798609
theorem B1731087 : Blo 1731066 1731087 := bstep (se 1 (by rfl) ⟨1298315, by rfl⟩ : syracuseStep 1731087 = 2596631) B2596631
theorem B2599439 : Blo 1731066 2599439 := bstep (se 1 (by rfl) ⟨1949579, by rfl⟩ : syracuseStep 2599439 = 3899159) B3899159
theorem B2599481 : Blo 1731066 2599481 := bstep (se 2 (by rfl) ⟨974805, by rfl⟩ : syracuseStep 2599481 = 1949611) B1949611
theorem B1731131 : Blo 1731066 1731131 := bstep (se 1 (by rfl) ⟨1298348, by rfl⟩ : syracuseStep 1731131 = 2596697) B2596697
theorem B24980035 : Blo 1731066 24980035 := bstep (se 1 (by rfl) ⟨18735026, by rfl⟩ : syracuseStep 24980035 = 37470053) B37470053
theorem B8768087 : Blo 1731066 8768087 := bstep (se 1 (by rfl) ⟨6576065, by rfl⟩ : syracuseStep 8768087 = 13152131) B13152131
theorem B1731207 : Blo 1731066 1731207 := bstep (se 1 (by rfl) ⟨1298405, by rfl⟩ : syracuseStep 1731207 = 2596811) B2596811
theorem B2599559 : Blo 1731066 2599559 := bstep (se 1 (by rfl) ⟨1949669, by rfl⟩ : syracuseStep 2599559 = 3899339) B3899339
theorem B1731215 : Blo 1731066 1731215 := bstep (se 1 (by rfl) ⟨1298411, by rfl⟩ : syracuseStep 1731215 = 2596823) B2596823
theorem B3287699 : Blo 1731066 3287699 := bstep (se 1 (by rfl) ⟨2465774, by rfl⟩ : syracuseStep 3287699 = 4931549) B4931549
theorem B2599595 : Blo 1731066 2599595 := bstep (se 1 (by rfl) ⟨1949696, by rfl⟩ : syracuseStep 2599595 = 3899393) B3899393
theorem B10676909 : Blo 1731066 10676909 := bstep (se 3 (by rfl) ⟨2001920, by rfl⟩ : syracuseStep 10676909 = 4003841) B4003841
theorem B1731259 : Blo 1731066 1731259 := bstep (se 1 (by rfl) ⟨1298444, by rfl⟩ : syracuseStep 1731259 = 2596889) B2596889
theorem B9865921 : Blo 1731066 9865921 := bstep (se 2 (by rfl) ⟨3699720, by rfl⟩ : syracuseStep 9865921 = 7399441) B7399441
theorem B1731335 : Blo 1731066 1731335 := bstep (se 1 (by rfl) ⟨1298501, by rfl⟩ : syracuseStep 1731335 = 2597003) B2597003
theorem B10529551 : Blo 1731066 10529551 := bstep (se 1 (by rfl) ⟨7897163, by rfl⟩ : syracuseStep 10529551 = 15794327) B15794327
theorem B1731343 : Blo 1731066 1731343 := bstep (se 1 (by rfl) ⟨1298507, by rfl⟩ : syracuseStep 1731343 = 2597015) B2597015
theorem B1731387 : Blo 1731066 1731387 := bstep (se 1 (by rfl) ⟨1298540, by rfl⟩ : syracuseStep 1731387 = 2597081) B2597081
theorem B5843771 : Blo 1731066 5843771 := bstep (se 1 (by rfl) ⟨4382828, by rfl⟩ : syracuseStep 5843771 = 8765657) B8765657
theorem B4385623 : Blo 1731066 4385623 := bstep (se 1 (by rfl) ⟨3289217, by rfl⟩ : syracuseStep 4385623 = 6578435) B6578435
theorem B5548915 : Blo 1731066 5548915 := bstep (se 1 (by rfl) ⟨4161686, by rfl⟩ : syracuseStep 5548915 = 8323373) B8323373
theorem B3287927 : Blo 1731066 3287927 := bstep (se 1 (by rfl) ⟨2465945, by rfl⟩ : syracuseStep 3287927 = 4931891) B4931891
theorem B2632583 : Blo 1731066 2632583 := bstep (se 1 (by rfl) ⟨1974437, by rfl⟩ : syracuseStep 2632583 = 3948875) B3948875
theorem B1731463 : Blo 1731066 1731463 := bstep (se 1 (by rfl) ⟨1298597, by rfl⟩ : syracuseStep 1731463 = 2597195) B2597195
theorem B1731471 : Blo 1731066 1731471 := bstep (se 1 (by rfl) ⟨1298603, by rfl⟩ : syracuseStep 1731471 = 2597207) B2597207
theorem B1731515 : Blo 1731066 1731515 := bstep (se 1 (by rfl) ⟨1298636, by rfl⟩ : syracuseStep 1731515 = 2597273) B2597273
theorem B1731591 : Blo 1731066 1731591 := bstep (se 1 (by rfl) ⟨1298693, by rfl⟩ : syracuseStep 1731591 = 2597387) B2597387
theorem B1731599 : Blo 1731066 1731599 := bstep (se 1 (by rfl) ⟨1298699, by rfl⟩ : syracuseStep 1731599 = 2597399) B2597399
theorem B1731643 : Blo 1731066 1731643 := bstep (se 1 (by rfl) ⟨1298732, by rfl⟩ : syracuseStep 1731643 = 2597465) B2597465
theorem B8768573 : Blo 1731066 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B10538045 : Blo 1731066 10538045 := bstep (se 3 (by rfl) ⟨1975883, by rfl⟩ : syracuseStep 10538045 = 3951767) B3951767
theorem B1731719 : Blo 1731066 1731719 := bstep (se 1 (by rfl) ⟨1298789, by rfl⟩ : syracuseStep 1731719 = 2597579) B2597579
theorem B4385927 : Blo 1731066 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B1731727 : Blo 1731066 1731727 := bstep (se 1 (by rfl) ⟨1298795, by rfl⟩ : syracuseStep 1731727 = 2597591) B2597591
theorem B4443283 : Blo 1731066 4443283 := bstep (se 1 (by rfl) ⟨3332462, by rfl⟩ : syracuseStep 4443283 = 6664925) B6664925
theorem B1731771 : Blo 1731066 1731771 := bstep (se 1 (by rfl) ⟨1298828, by rfl⟩ : syracuseStep 1731771 = 2597657) B2597657
theorem B6573257 : Blo 1731066 6573257 := bstep (se 2 (by rfl) ⟨2464971, by rfl⟩ : syracuseStep 6573257 = 4929943) B4929943
theorem B36547789 : Blo 1731066 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B1731847 : Blo 1731066 1731847 := bstep (se 1 (by rfl) ⟨1298885, by rfl⟩ : syracuseStep 1731847 = 2597771) B2597771
theorem B4386059 : Blo 1731066 4386059 := bstep (se 1 (by rfl) ⟨3289544, by rfl⟩ : syracuseStep 4386059 = 6579089) B6579089
theorem B1731855 : Blo 1731066 1731855 := bstep (se 1 (by rfl) ⟨1298891, by rfl⟩ : syracuseStep 1731855 = 2597783) B2597783
theorem B5844257 : Blo 1731066 5844257 := bstep (se 2 (by rfl) ⟨2191596, by rfl⟩ : syracuseStep 5844257 = 4383193) B4383193
theorem B1731899 : Blo 1731066 1731899 := bstep (se 1 (by rfl) ⟨1298924, by rfl⟩ : syracuseStep 1731899 = 2597849) B2597849
theorem B1731975 : Blo 1731066 1731975 := bstep (se 1 (by rfl) ⟨1298981, by rfl⟩ : syracuseStep 1731975 = 2597963) B2597963
theorem B1731983 : Blo 1731066 1731983 := bstep (se 1 (by rfl) ⟨1298987, by rfl⟩ : syracuseStep 1731983 = 2597975) B2597975
theorem B7499155 : Blo 1731066 7499155 := bstep (se 1 (by rfl) ⟨5624366, by rfl⟩ : syracuseStep 7499155 = 11248733) B11248733
theorem B1732027 : Blo 1731066 1732027 := bstep (se 1 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 1732027 = 2598041) B2598041
theorem B3509705 : Blo 1731066 3509705 := bstep (se 2 (by rfl) ⟨1316139, by rfl⟩ : syracuseStep 3509705 = 2632279) B2632279
theorem B14626307 : Blo 1731066 14626307 := bstep (se 1 (by rfl) ⟨10969730, by rfl⟩ : syracuseStep 14626307 = 21939461) B21939461
theorem B1732103 : Blo 1731066 1732103 := bstep (se 1 (by rfl) ⟨1299077, by rfl⟩ : syracuseStep 1732103 = 2598155) B2598155
theorem B1732111 : Blo 1731066 1732111 := bstep (se 1 (by rfl) ⟨1299083, by rfl⟩ : syracuseStep 1732111 = 2598167) B2598167
theorem B1732155 : Blo 1731066 1732155 := bstep (se 1 (by rfl) ⟨1299116, by rfl⟩ : syracuseStep 1732155 = 2598233) B2598233
theorem B1732231 : Blo 1731066 1732231 := bstep (se 1 (by rfl) ⟨1299173, by rfl⟩ : syracuseStep 1732231 = 2598347) B2598347
theorem B1732239 : Blo 1731066 1732239 := bstep (se 1 (by rfl) ⟨1299179, by rfl⟩ : syracuseStep 1732239 = 2598359) B2598359
theorem B5066425 : Blo 1731066 5066425 := bstep (se 2 (by rfl) ⟨1899909, by rfl⟩ : syracuseStep 5066425 = 3799819) B3799819
theorem B1732283 : Blo 1731066 1732283 := bstep (se 1 (by rfl) ⟨1299212, by rfl⟩ : syracuseStep 1732283 = 2598425) B2598425
theorem B1732359 : Blo 1731066 1732359 := bstep (se 1 (by rfl) ⟨1299269, by rfl⟩ : syracuseStep 1732359 = 2598539) B2598539
theorem B3895055 : Blo 1731066 3895055 := bstep (se 1 (by rfl) ⟨2921291, by rfl⟩ : syracuseStep 3895055 = 5842583) B5842583
theorem B1732367 : Blo 1731066 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B4386575 : Blo 1731066 4386575 := bstep (se 1 (by rfl) ⟨3289931, by rfl⟩ : syracuseStep 4386575 = 6579863) B6579863
theorem B3895073 : Blo 1731066 3895073 := bstep (se 2 (by rfl) ⟨1460652, by rfl⟩ : syracuseStep 3895073 = 2921305) B2921305
theorem B19738403 : Blo 1731066 19738403 := bstep (se 1 (by rfl) ⟨14803802, by rfl⟩ : syracuseStep 19738403 = 29607605) B29607605
theorem B1732411 : Blo 1731066 1732411 := bstep (se 1 (by rfl) ⟨1299308, by rfl⟩ : syracuseStep 1732411 = 2598617) B2598617
theorem B5844851 : Blo 1731066 5844851 := bstep (se 1 (by rfl) ⟨4383638, by rfl⟩ : syracuseStep 5844851 = 8767277) B8767277
theorem B3698551 : Blo 1731066 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B1732487 : Blo 1731066 1732487 := bstep (se 1 (by rfl) ⟨1299365, by rfl⟩ : syracuseStep 1732487 = 2598731) B2598731
theorem B1732495 : Blo 1731066 1732495 := bstep (se 1 (by rfl) ⟨1299371, by rfl⟩ : syracuseStep 1732495 = 2598743) B2598743
theorem B4386707 : Blo 1731066 4386707 := bstep (se 1 (by rfl) ⟨3290030, by rfl⟩ : syracuseStep 4386707 = 6580061) B6580061
theorem B1732539 : Blo 1731066 1732539 := bstep (se 1 (by rfl) ⟨1299404, by rfl⟩ : syracuseStep 1732539 = 2598809) B2598809
theorem B8433629 : Blo 1731066 8433629 := bstep (se 3 (by rfl) ⟨1581305, by rfl⟩ : syracuseStep 8433629 = 3162611) B3162611
theorem B2707447 : Blo 1731066 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B1732615 : Blo 1731066 1732615 := bstep (se 1 (by rfl) ⟨1299461, by rfl⟩ : syracuseStep 1732615 = 2598923) B2598923
theorem B1732623 : Blo 1731066 1732623 := bstep (se 1 (by rfl) ⟨1299467, by rfl⟩ : syracuseStep 1732623 = 2598935) B2598935
theorem B9359383 : Blo 1731066 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B2961451 : Blo 1731066 2961451 := bstep (se 1 (by rfl) ⟨2221088, by rfl⟩ : syracuseStep 2961451 = 4442177) B4442177
theorem B1732667 : Blo 1731066 1732667 := bstep (se 1 (by rfl) ⟨1299500, by rfl⟩ : syracuseStep 1732667 = 2599001) B2599001
theorem B3895415 : Blo 1731066 3895415 := bstep (se 1 (by rfl) ⟨2921561, by rfl⟩ : syracuseStep 3895415 = 5843123) B5843123
theorem B1732743 : Blo 1731066 1732743 := bstep (se 1 (by rfl) ⟨1299557, by rfl⟩ : syracuseStep 1732743 = 2599115) B2599115
theorem B1732751 : Blo 1731066 1732751 := bstep (se 1 (by rfl) ⟨1299563, by rfl⟩ : syracuseStep 1732751 = 2599127) B2599127
theorem B2191531 : Blo 1731066 2191531 := bstep (se 1 (by rfl) ⟨1643648, by rfl⟩ : syracuseStep 2191531 = 3287297) B3287297
theorem B1732795 : Blo 1731066 1732795 := bstep (se 1 (by rfl) ⟨1299596, by rfl⟩ : syracuseStep 1732795 = 2599193) B2599193
theorem B34214089 : Blo 1731066 34214089 := bstep (se 2 (by rfl) ⟨12830283, by rfl⟩ : syracuseStep 34214089 = 25660567) B25660567
theorem B1732871 : Blo 1731066 1732871 := bstep (se 1 (by rfl) ⟨1299653, by rfl⟩ : syracuseStep 1732871 = 2599307) B2599307
theorem B1732879 : Blo 1731066 1732879 := bstep (se 1 (by rfl) ⟨1299659, by rfl⟩ : syracuseStep 1732879 = 2599319) B2599319
theorem B3895595 : Blo 1731066 3895595 := bstep (se 1 (by rfl) ⟨2921696, by rfl⟩ : syracuseStep 3895595 = 5843393) B5843393
theorem B1732923 : Blo 1731066 1732923 := bstep (se 1 (by rfl) ⟨1299692, by rfl⟩ : syracuseStep 1732923 = 2599385) B2599385
theorem B4682071 : Blo 1731066 4682071 := bstep (se 1 (by rfl) ⟨3511553, by rfl⟩ : syracuseStep 4682071 = 7023107) B7023107
theorem B1732999 : Blo 1731066 1732999 := bstep (se 1 (by rfl) ⟨1299749, by rfl⟩ : syracuseStep 1732999 = 2599499) B2599499
theorem B1733007 : Blo 1731066 1733007 := bstep (se 1 (by rfl) ⟨1299755, by rfl⟩ : syracuseStep 1733007 = 2599511) B2599511
theorem B2773433 : Blo 1731066 2773433 := bstep (se 2 (by rfl) ⟨1040037, by rfl⟩ : syracuseStep 2773433 = 2080075) B2080075
theorem B1733051 : Blo 1731066 1733051 := bstep (se 1 (by rfl) ⟨1299788, by rfl⟩ : syracuseStep 1733051 = 2599577) B2599577
theorem B159896081 : Blo 1731066 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B3289643 : Blo 1731066 3289643 := bstep (se 1 (by rfl) ⟨2467232, by rfl⟩ : syracuseStep 3289643 = 4934465) B4934465
theorem B3895955 : Blo 1731066 3895955 := bstep (se 1 (by rfl) ⟨2921966, by rfl⟩ : syracuseStep 3895955 = 5843933) B5843933
theorem B3896009 : Blo 1731066 3896009 := bstep (se 2 (by rfl) ⟨1461003, by rfl⟩ : syracuseStep 3896009 = 2922007) B2922007
theorem B2921231 : Blo 1731066 2921231 := bstep (se 1 (by rfl) ⟨2190923, by rfl⟩ : syracuseStep 2921231 = 4381847) B4381847
theorem B3289871 : Blo 1731066 3289871 := bstep (se 1 (by rfl) ⟨2467403, by rfl⟩ : syracuseStep 3289871 = 4934807) B4934807
theorem B8770355 : Blo 1731066 8770355 := bstep (se 1 (by rfl) ⟨6577766, by rfl⟩ : syracuseStep 8770355 = 13155533) B13155533
theorem B29594483 : Blo 1731066 29594483 := bstep (se 1 (by rfl) ⟨22195862, by rfl⟩ : syracuseStep 29594483 = 44391725) B44391725
theorem B16642979 : Blo 1731066 16642979 := bstep (se 1 (by rfl) ⟨12482234, by rfl⟩ : syracuseStep 16642979 = 24964469) B24964469
theorem B159904691 : Blo 1731066 159904691 := bstep (se 1 (by rfl) ⟨119928518, by rfl⟩ : syracuseStep 159904691 = 239857037) B239857037
theorem B6575033 : Blo 1731066 6575033 := bstep (se 2 (by rfl) ⟨2465637, by rfl⟩ : syracuseStep 6575033 = 4931275) B4931275
theorem B22205501 : Blo 1731066 22205501 := bstep (se 3 (by rfl) ⟨4163531, by rfl⟩ : syracuseStep 22205501 = 8327063) B8327063
theorem B8320067 : Blo 1731066 8320067 := bstep (se 1 (by rfl) ⟨6240050, by rfl⟩ : syracuseStep 8320067 = 12480101) B12480101
theorem B2192503 : Blo 1731066 2192503 := bstep (se 1 (by rfl) ⟨1644377, by rfl⟩ : syracuseStep 2192503 = 3288755) B3288755
theorem B8770679 : Blo 1731066 8770679 := bstep (se 1 (by rfl) ⟨6578009, by rfl⟩ : syracuseStep 8770679 = 13156019) B13156019
theorem B5625089 : Blo 1731066 5625089 := bstep (se 2 (by rfl) ⟨2109408, by rfl⟩ : syracuseStep 5625089 = 4218817) B4218817
theorem B2921771 : Blo 1731066 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B3896711 : Blo 1731066 3896711 := bstep (se 1 (by rfl) ⟨2922533, by rfl⟩ : syracuseStep 3896711 = 5845067) B5845067
theorem B2774407 : Blo 1731066 2774407 := bstep (se 1 (by rfl) ⟨2080805, by rfl⟩ : syracuseStep 2774407 = 4161611) B4161611
theorem B6329735 : Blo 1731066 6329735 := bstep (se 1 (by rfl) ⟨4747301, by rfl⟩ : syracuseStep 6329735 = 9494603) B9494603
theorem B29988281 : Blo 1731066 29988281 := bstep (se 2 (by rfl) ⟨11245605, by rfl⟩ : syracuseStep 29988281 = 22491211) B22491211
theorem B2192827 : Blo 1731066 2192827 := bstep (se 1 (by rfl) ⟨1644620, by rfl⟩ : syracuseStep 2192827 = 3289241) B3289241
theorem B17774083 : Blo 1731066 17774083 := bstep (se 1 (by rfl) ⟨13330562, by rfl⟩ : syracuseStep 17774083 = 26661125) B26661125
theorem B3896891 : Blo 1731066 3896891 := bstep (se 1 (by rfl) ⟨2922668, by rfl⟩ : syracuseStep 3896891 = 5845337) B5845337
theorem B32044643 : Blo 1731066 32044643 := bstep (se 1 (by rfl) ⟨24033482, by rfl⟩ : syracuseStep 32044643 = 48066965) B48066965
theorem B3511927 : Blo 1731066 3511927 := bstep (se 1 (by rfl) ⟨2633945, by rfl⟩ : syracuseStep 3511927 = 5267891) B5267891
theorem B2774663 : Blo 1731066 2774663 := bstep (se 1 (by rfl) ⟨2080997, by rfl⟩ : syracuseStep 2774663 = 4161995) B4161995
theorem B2922169 : Blo 1731066 2922169 := bstep (se 2 (by rfl) ⟨1095813, by rfl⟩ : syracuseStep 2922169 = 2191627) B2191627
theorem B3897017 : Blo 1731066 3897017 := bstep (se 2 (by rfl) ⟨1461381, by rfl⟩ : syracuseStep 3897017 = 2922763) B2922763
theorem B4683521 : Blo 1731066 4683521 := bstep (se 2 (by rfl) ⟨1756320, by rfl⟩ : syracuseStep 4683521 = 3512641) B3512641
theorem B1947451 : Blo 1731066 1947451 := bstep (se 1 (by rfl) ⟨1460588, by rfl⟩ : syracuseStep 1947451 = 2921177) B2921177
theorem B14047091 : Blo 1731066 14047091 := bstep (se 1 (by rfl) ⟨10535318, by rfl⟩ : syracuseStep 14047091 = 21070637) B21070637
theorem B8320913 : Blo 1731066 8320913 := bstep (se 2 (by rfl) ⟨3120342, by rfl⟩ : syracuseStep 8320913 = 6240685) B6240685
theorem B2406391 : Blo 1731066 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B3897359 : Blo 1731066 3897359 := bstep (se 1 (by rfl) ⟨2923019, by rfl⟩ : syracuseStep 3897359 = 5846039) B5846039
theorem B3897377 : Blo 1731066 3897377 := bstep (se 2 (by rfl) ⟨1461516, by rfl⟩ : syracuseStep 3897377 = 2923033) B2923033
theorem B8771651 : Blo 1731066 8771651 := bstep (se 1 (by rfl) ⟨6578738, by rfl⟩ : syracuseStep 8771651 = 13157477) B13157477
theorem B8321143 : Blo 1731066 8321143 := bstep (se 1 (by rfl) ⟨6240857, by rfl⟩ : syracuseStep 8321143 = 12481715) B12481715
theorem B3700883 : Blo 1731066 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B14801069 : Blo 1731066 14801069 := bstep (se 3 (by rfl) ⟨2775200, by rfl⟩ : syracuseStep 14801069 = 5550401) B5550401
theorem B1947919 : Blo 1731066 1947919 := bstep (se 1 (by rfl) ⟨1460939, by rfl⟩ : syracuseStep 1947919 = 2921879) B2921879
theorem B2922871 : Blo 1731066 2922871 := bstep (se 1 (by rfl) ⟨2192153, by rfl⟩ : syracuseStep 2922871 = 4384307) B4384307
theorem B3897719 : Blo 1731066 3897719 := bstep (se 1 (by rfl) ⟨2923289, by rfl⟩ : syracuseStep 3897719 = 5846579) B5846579
theorem B4159879 : Blo 1731066 4159879 := bstep (se 1 (by rfl) ⟨3119909, by rfl⟩ : syracuseStep 4159879 = 6239819) B6239819
theorem B8771975 : Blo 1731066 8771975 := bstep (se 1 (by rfl) ⟨6578981, by rfl⟩ : syracuseStep 8771975 = 13157963) B13157963
theorem B5847443 : Blo 1731066 5847443 := bstep (se 1 (by rfl) ⟨4385582, by rfl⟩ : syracuseStep 5847443 = 8771165) B8771165
theorem B4929977 : Blo 1731066 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B54073817 : Blo 1731066 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B4930091 : Blo 1731066 4930091 := bstep (se 1 (by rfl) ⟨3697568, by rfl⟩ : syracuseStep 4930091 = 7395137) B7395137
theorem B3897899 : Blo 1731066 3897899 := bstep (se 1 (by rfl) ⟨2923424, by rfl⟩ : syracuseStep 3897899 = 5846849) B5846849
theorem B2923067 : Blo 1731066 2923067 := bstep (se 1 (by rfl) ⟨2192300, by rfl⟩ : syracuseStep 2923067 = 4384601) B4384601
theorem B2775611 : Blo 1731066 2775611 := bstep (se 1 (by rfl) ⟨2081708, by rfl⟩ : syracuseStep 2775611 = 4163417) B4163417
theorem B1948423 : Blo 1731066 1948423 := bstep (se 1 (by rfl) ⟨1461317, by rfl⟩ : syracuseStep 1948423 = 2922635) B2922635
theorem B9870113 : Blo 1731066 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B3898259 : Blo 1731066 3898259 := bstep (se 1 (by rfl) ⟨2923694, by rfl⟩ : syracuseStep 3898259 = 5847389) B5847389
theorem B9862073 : Blo 1731066 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B1948603 : Blo 1731066 1948603 := bstep (se 1 (by rfl) ⟨1461452, by rfl⟩ : syracuseStep 1948603 = 2922905) B2922905
theorem B2923465 : Blo 1731066 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B3898313 : Blo 1731066 3898313 := bstep (se 2 (by rfl) ⟨1461867, by rfl⟩ : syracuseStep 3898313 = 2923735) B2923735
theorem B4381897 : Blo 1731066 4381897 := bstep (se 2 (by rfl) ⟨1643211, by rfl⟩ : syracuseStep 4381897 = 3286423) B3286423
theorem B8322355 : Blo 1731066 8322355 := bstep (se 1 (by rfl) ⟨6241766, by rfl⟩ : syracuseStep 8322355 = 12483533) B12483533
theorem B4382039 : Blo 1731066 4382039 := bstep (se 1 (by rfl) ⟨3286529, by rfl⟩ : syracuseStep 4382039 = 6573059) B6573059
theorem B2465159 : Blo 1731066 2465159 := bstep (se 1 (by rfl) ⟨1848869, by rfl⟩ : syracuseStep 2465159 = 3697739) B3697739
theorem B1949071 : Blo 1731066 1949071 := bstep (se 1 (by rfl) ⟨1461803, by rfl⟩ : syracuseStep 1949071 = 2923607) B2923607
theorem B9616849 : Blo 1731066 9616849 := bstep (se 2 (by rfl) ⟨3606318, by rfl⟩ : syracuseStep 9616849 = 7212637) B7212637
theorem B35569181 : Blo 1731066 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B14433835 : Blo 1731066 14433835 := bstep (se 1 (by rfl) ⟨10825376, by rfl⟩ : syracuseStep 14433835 = 21650753) B21650753
theorem B2465353 : Blo 1731066 2465353 := bstep (se 2 (by rfl) ⟨924507, by rfl⟩ : syracuseStep 2465353 = 1849015) B1849015
theorem B2924167 : Blo 1731066 2924167 := bstep (se 1 (by rfl) ⟨2193125, by rfl⟩ : syracuseStep 2924167 = 4386251) B4386251
theorem B3899015 : Blo 1731066 3899015 := bstep (se 1 (by rfl) ⟨2924261, by rfl⟩ : syracuseStep 3899015 = 5848523) B5848523
theorem B4931219 : Blo 1731066 4931219 := bstep (se 1 (by rfl) ⟨3698414, by rfl⟩ : syracuseStep 4931219 = 7396829) B7396829
theorem B5848847 : Blo 1731066 5848847 := bstep (se 1 (by rfl) ⟨4386635, by rfl⟩ : syracuseStep 5848847 = 8773271) B8773271
theorem B7397153 : Blo 1731066 7397153 := bstep (se 2 (by rfl) ⟨2773932, by rfl⟩ : syracuseStep 7397153 = 5547865) B5547865
theorem B2596667 : Blo 1731066 2596667 := bstep (se 1 (by rfl) ⟨1947500, by rfl⟩ : syracuseStep 2596667 = 3895001) B3895001
theorem B3899195 : Blo 1731066 3899195 := bstep (se 1 (by rfl) ⟨2924396, by rfl⟩ : syracuseStep 3899195 = 5848793) B5848793
theorem B2596727 : Blo 1731066 2596727 := bstep (se 1 (by rfl) ⟨1947545, by rfl⟩ : syracuseStep 2596727 = 3895091) B3895091
theorem B1949575 : Blo 1731066 1949575 := bstep (se 1 (by rfl) ⟨1462181, by rfl⟩ : syracuseStep 1949575 = 2924363) B2924363
theorem B2596751 : Blo 1731066 2596751 := bstep (se 1 (by rfl) ⟨1947563, by rfl⟩ : syracuseStep 2596751 = 3895127) B3895127
theorem B2596793 : Blo 1731066 2596793 := bstep (se 2 (by rfl) ⟨973797, by rfl⟩ : syracuseStep 2596793 = 1947595) B1947595
theorem B3899321 : Blo 1731066 3899321 := bstep (se 2 (by rfl) ⟨1462245, by rfl⟩ : syracuseStep 3899321 = 2924491) B2924491
theorem B3948601 : Blo 1731066 3948601 := bstep (se 2 (by rfl) ⟨1480725, by rfl⟩ : syracuseStep 3948601 = 2961451) B2961451
theorem B2596943 : Blo 1731066 2596943 := bstep (se 1 (by rfl) ⟨1947707, by rfl⟩ : syracuseStep 2596943 = 3895415) B3895415
theorem B2597063 : Blo 1731066 2597063 := bstep (se 1 (by rfl) ⟨1947797, by rfl⟩ : syracuseStep 2597063 = 3895595) B3895595
theorem B2597225 : Blo 1731066 2597225 := bstep (se 2 (by rfl) ⟨973959, by rfl⟩ : syracuseStep 2597225 = 1947919) B1947919
theorem B2597303 : Blo 1731066 2597303 := bstep (se 1 (by rfl) ⟨1947977, by rfl⟩ : syracuseStep 2597303 = 3895955) B3895955
theorem B6242761 : Blo 1731066 6242761 := bstep (se 2 (by rfl) ⟨2341035, by rfl⟩ : syracuseStep 6242761 = 4682071) B4682071
theorem B2597339 : Blo 1731066 2597339 := bstep (se 1 (by rfl) ⟨1948004, by rfl⟩ : syracuseStep 2597339 = 3896009) B3896009
theorem B106603127 : Blo 1731066 106603127 := bstep (se 1 (by rfl) ⟨79952345, by rfl⟩ : syracuseStep 106603127 = 159904691) B159904691
theorem B4383355 : Blo 1731066 4383355 := bstep (se 1 (by rfl) ⟨3287516, by rfl⟩ : syracuseStep 4383355 = 6575033) B6575033
theorem B14803667 : Blo 1731066 14803667 := bstep (se 1 (by rfl) ⟨11102750, by rfl⟩ : syracuseStep 14803667 = 22205501) B22205501
theorem B5546711 : Blo 1731066 5546711 := bstep (se 1 (by rfl) ⟨4160033, by rfl⟩ : syracuseStep 5546711 = 8320067) B8320067
theorem B2597807 : Blo 1731066 2597807 := bstep (se 1 (by rfl) ⟨1948355, by rfl⟩ : syracuseStep 2597807 = 3896711) B3896711
theorem B4219823 : Blo 1731066 4219823 := bstep (se 1 (by rfl) ⟨3164867, by rfl⟩ : syracuseStep 4219823 = 6329735) B6329735
theorem B2597897 : Blo 1731066 2597897 := bstep (se 2 (by rfl) ⟨974211, by rfl⟩ : syracuseStep 2597897 = 1948423) B1948423
theorem B2597927 : Blo 1731066 2597927 := bstep (se 1 (by rfl) ⟨1948445, by rfl⟩ : syracuseStep 2597927 = 3896891) B3896891
theorem B2598011 : Blo 1731066 2598011 := bstep (se 1 (by rfl) ⟨1948508, by rfl⟩ : syracuseStep 2598011 = 3897017) B3897017
theorem B7398553 : Blo 1731066 7398553 := bstep (se 2 (by rfl) ⟨2774457, by rfl⟩ : syracuseStep 7398553 = 5548915) B5548915
theorem B9364727 : Blo 1731066 9364727 := bstep (se 1 (by rfl) ⟨7023545, by rfl⟩ : syracuseStep 9364727 = 14047091) B14047091
theorem B2598137 : Blo 1731066 2598137 := bstep (se 2 (by rfl) ⟨974301, by rfl⟩ : syracuseStep 2598137 = 1948603) B1948603
theorem B5547275 : Blo 1731066 5547275 := bstep (se 1 (by rfl) ⟨4160456, by rfl⟩ : syracuseStep 5547275 = 8320913) B8320913
theorem B2598239 : Blo 1731066 2598239 := bstep (se 1 (by rfl) ⟨1948679, by rfl⟩ : syracuseStep 2598239 = 3897359) B3897359
theorem B2598251 : Blo 1731066 2598251 := bstep (se 1 (by rfl) ⟨1948688, by rfl⟩ : syracuseStep 2598251 = 3897377) B3897377
theorem B4933007 : Blo 1731066 4933007 := bstep (se 1 (by rfl) ⟨3699755, by rfl⟩ : syracuseStep 4933007 = 7399511) B7399511
theorem B2467255 : Blo 1731066 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B5924377 : Blo 1731066 5924377 := bstep (se 2 (by rfl) ⟨2221641, by rfl⟩ : syracuseStep 5924377 = 4443283) B4443283
theorem B47400491 : Blo 1731066 47400491 := bstep (se 1 (by rfl) ⟨35550368, by rfl⟩ : syracuseStep 47400491 = 71100737) B71100737
theorem B2598479 : Blo 1731066 2598479 := bstep (se 1 (by rfl) ⟨1948859, by rfl⟩ : syracuseStep 2598479 = 3897719) B3897719
theorem B5842529 : Blo 1731066 5842529 := bstep (se 2 (by rfl) ⟨2190948, by rfl⟩ : syracuseStep 5842529 = 4381897) B4381897
theorem B57738851 : Blo 1731066 57738851 := bstep (se 1 (by rfl) ⟨43304138, by rfl⟩ : syracuseStep 57738851 = 86608277) B86608277
theorem B3286651 : Blo 1731066 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B8767115 : Blo 1731066 8767115 := bstep (se 1 (by rfl) ⟨6575336, by rfl⟩ : syracuseStep 8767115 = 13150673) B13150673
theorem B3286727 : Blo 1731066 3286727 := bstep (se 1 (by rfl) ⟨2465045, by rfl⟩ : syracuseStep 3286727 = 4930091) B4930091
theorem B2598599 : Blo 1731066 2598599 := bstep (se 1 (by rfl) ⟨1948949, by rfl⟩ : syracuseStep 2598599 = 3897899) B3897899
theorem B2598761 : Blo 1731066 2598761 := bstep (se 2 (by rfl) ⟨974535, by rfl⟩ : syracuseStep 2598761 = 1949071) B1949071
theorem B6580075 : Blo 1731066 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B1755055 : Blo 1731066 1755055 := bstep (se 1 (by rfl) ⟨1316291, by rfl⟩ : syracuseStep 1755055 = 2632583) B2632583
theorem B2598839 : Blo 1731066 2598839 := bstep (se 1 (by rfl) ⟨1949129, by rfl⟩ : syracuseStep 2598839 = 3898259) B3898259
theorem B2598875 : Blo 1731066 2598875 := bstep (se 1 (by rfl) ⟨1949156, by rfl⟩ : syracuseStep 2598875 = 3898313) B3898313
theorem B22186021 : Blo 1731066 22186021 := bstep (se 4 (by rfl) ⟨2079939, by rfl⟩ : syracuseStep 22186021 = 4159879) B4159879
theorem B19245113 : Blo 1731066 19245113 := bstep (se 2 (by rfl) ⟨7216917, by rfl⟩ : syracuseStep 19245113 = 14433835) B14433835
theorem B3287137 : Blo 1731066 3287137 := bstep (se 2 (by rfl) ⟨1232676, by rfl⟩ : syracuseStep 3287137 = 2465353) B2465353
theorem B9750871 : Blo 1731066 9750871 := bstep (se 1 (by rfl) ⟨7313153, by rfl⟩ : syracuseStep 9750871 = 14626307) B14626307
theorem B26659205 : Blo 1731066 26659205 := bstep (se 4 (by rfl) ⟨2499300, by rfl⟩ : syracuseStep 26659205 = 4998601) B4998601
theorem B2599343 : Blo 1731066 2599343 := bstep (se 1 (by rfl) ⟨1949507, by rfl⟩ : syracuseStep 2599343 = 3899015) B3899015
theorem B3287479 : Blo 1731066 3287479 := bstep (se 1 (by rfl) ⟨2465609, by rfl⟩ : syracuseStep 3287479 = 4931219) B4931219
theorem B2599433 : Blo 1731066 2599433 := bstep (se 2 (by rfl) ⟨974787, by rfl⟩ : syracuseStep 2599433 = 1949575) B1949575
theorem B13158935 : Blo 1731066 13158935 := bstep (se 1 (by rfl) ⟨9869201, by rfl⟩ : syracuseStep 13158935 = 19738403) B19738403
theorem B1731111 : Blo 1731066 1731111 := bstep (se 1 (by rfl) ⟨1298333, by rfl⟩ : syracuseStep 1731111 = 2596667) B2596667
theorem B2599463 : Blo 1731066 2599463 := bstep (se 1 (by rfl) ⟨1949597, by rfl⟩ : syracuseStep 2599463 = 3899195) B3899195
theorem B1731151 : Blo 1731066 1731151 := bstep (se 1 (by rfl) ⟨1298363, by rfl⟩ : syracuseStep 1731151 = 2596727) B2596727
theorem B1731167 : Blo 1731066 1731167 := bstep (se 1 (by rfl) ⟨1298375, by rfl⟩ : syracuseStep 1731167 = 2596751) B2596751
theorem B1731195 : Blo 1731066 1731195 := bstep (se 1 (by rfl) ⟨1298396, by rfl⟩ : syracuseStep 1731195 = 2596793) B2596793
theorem B2599547 : Blo 1731066 2599547 := bstep (se 1 (by rfl) ⟨1949660, by rfl⟩ : syracuseStep 2599547 = 3899321) B3899321
theorem B5622419 : Blo 1731066 5622419 := bstep (se 1 (by rfl) ⟨4216814, by rfl⟩ : syracuseStep 5622419 = 8433629) B8433629
theorem B1731247 : Blo 1731066 1731247 := bstep (se 1 (by rfl) ⟨1298435, by rfl⟩ : syracuseStep 1731247 = 2596871) B2596871
theorem B1731271 : Blo 1731066 1731271 := bstep (se 1 (by rfl) ⟨1298453, by rfl⟩ : syracuseStep 1731271 = 2596907) B2596907
theorem B12479177 : Blo 1731066 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B3697363 : Blo 1731066 3697363 := bstep (se 1 (by rfl) ⟨2773022, by rfl⟩ : syracuseStep 3697363 = 5546045) B5546045
theorem B1731291 : Blo 1731066 1731291 := bstep (se 1 (by rfl) ⟨1298468, by rfl⟩ : syracuseStep 1731291 = 2596937) B2596937
theorem B1731367 : Blo 1731066 1731367 := bstep (se 1 (by rfl) ⟨1298525, by rfl⟩ : syracuseStep 1731367 = 2597051) B2597051
theorem B11094857 : Blo 1731066 11094857 := bstep (se 2 (by rfl) ⟨4160571, by rfl⟩ : syracuseStep 11094857 = 8321143) B8321143
theorem B3287881 : Blo 1731066 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B1731407 : Blo 1731066 1731407 := bstep (se 1 (by rfl) ⟨1298555, by rfl⟩ : syracuseStep 1731407 = 2597111) B2597111
theorem B1731423 : Blo 1731066 1731423 := bstep (se 1 (by rfl) ⟨1298567, by rfl⟩ : syracuseStep 1731423 = 2597135) B2597135
theorem B1731451 : Blo 1731066 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B1731503 : Blo 1731066 1731503 := bstep (se 1 (by rfl) ⟨1298627, by rfl⟩ : syracuseStep 1731503 = 2597255) B2597255
theorem B13151159 : Blo 1731066 13151159 := bstep (se 1 (by rfl) ⟨9863369, by rfl⟩ : syracuseStep 13151159 = 19726739) B19726739
theorem B1731527 : Blo 1731066 1731527 := bstep (se 1 (by rfl) ⟨1298645, by rfl⟩ : syracuseStep 1731527 = 2597291) B2597291
theorem B1731547 : Blo 1731066 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B5549057 : Blo 1731066 5549057 := bstep (se 2 (by rfl) ⟨2080896, by rfl⟩ : syracuseStep 5549057 = 4161793) B4161793
theorem B106597387 : Blo 1731066 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B5843987 : Blo 1731066 5843987 := bstep (se 1 (by rfl) ⟨4382990, by rfl⟩ : syracuseStep 5843987 = 8765981) B8765981
theorem B1731623 : Blo 1731066 1731623 := bstep (se 1 (by rfl) ⟨1298717, by rfl⟩ : syracuseStep 1731623 = 2597435) B2597435
theorem B1731663 : Blo 1731066 1731663 := bstep (se 1 (by rfl) ⟨1298747, by rfl⟩ : syracuseStep 1731663 = 2597495) B2597495
theorem B1731679 : Blo 1731066 1731679 := bstep (se 1 (by rfl) ⟨1298759, by rfl⟩ : syracuseStep 1731679 = 2597519) B2597519
theorem B1731707 : Blo 1731066 1731707 := bstep (se 1 (by rfl) ⟨1298780, by rfl⟩ : syracuseStep 1731707 = 2597561) B2597561
theorem B1731759 : Blo 1731066 1731759 := bstep (se 1 (by rfl) ⟨1298819, by rfl⟩ : syracuseStep 1731759 = 2597639) B2597639
theorem B1731783 : Blo 1731066 1731783 := bstep (se 1 (by rfl) ⟨1298837, by rfl⟩ : syracuseStep 1731783 = 2597675) B2597675
theorem B1731803 : Blo 1731066 1731803 := bstep (se 1 (by rfl) ⟨1298852, by rfl⟩ : syracuseStep 1731803 = 2597705) B2597705
theorem B19729655 : Blo 1731066 19729655 := bstep (se 1 (by rfl) ⟨14797241, by rfl⟩ : syracuseStep 19729655 = 29594483) B29594483
theorem B11095319 : Blo 1731066 11095319 := bstep (se 1 (by rfl) ⟨8321489, by rfl⟩ : syracuseStep 11095319 = 16642979) B16642979
theorem B1731879 : Blo 1731066 1731879 := bstep (se 1 (by rfl) ⟨1298909, by rfl⟩ : syracuseStep 1731879 = 2597819) B2597819
theorem B1731919 : Blo 1731066 1731919 := bstep (se 1 (by rfl) ⟨1298939, by rfl⟩ : syracuseStep 1731919 = 2597879) B2597879
theorem B5844311 : Blo 1731066 5844311 := bstep (se 1 (by rfl) ⟨4383233, by rfl⟩ : syracuseStep 5844311 = 8766467) B8766467
theorem B1731935 : Blo 1731066 1731935 := bstep (se 1 (by rfl) ⟨1298951, by rfl⟩ : syracuseStep 1731935 = 2597903) B2597903
theorem B1731963 : Blo 1731066 1731963 := bstep (se 1 (by rfl) ⟨1298972, by rfl⟩ : syracuseStep 1731963 = 2597945) B2597945
theorem B1732015 : Blo 1731066 1732015 := bstep (se 1 (by rfl) ⟨1299011, by rfl⟩ : syracuseStep 1732015 = 2598023) B2598023
theorem B1732039 : Blo 1731066 1732039 := bstep (se 1 (by rfl) ⟨1299029, by rfl⟩ : syracuseStep 1732039 = 2598059) B2598059
theorem B1732059 : Blo 1731066 1732059 := bstep (se 1 (by rfl) ⟨1299044, by rfl⟩ : syracuseStep 1732059 = 2598089) B2598089
theorem B45018611 : Blo 1731066 45018611 := bstep (se 1 (by rfl) ⟨33763958, by rfl⟩ : syracuseStep 45018611 = 67527917) B67527917
theorem B3288595 : Blo 1731066 3288595 := bstep (se 1 (by rfl) ⟨2466446, by rfl⟩ : syracuseStep 3288595 = 4932893) B4932893
theorem B1732135 : Blo 1731066 1732135 := bstep (se 1 (by rfl) ⟨1299101, by rfl⟩ : syracuseStep 1732135 = 2598203) B2598203
theorem B1732175 : Blo 1731066 1732175 := bstep (se 1 (by rfl) ⟨1299131, by rfl⟩ : syracuseStep 1732175 = 2598263) B2598263
theorem B1732191 : Blo 1731066 1732191 := bstep (se 1 (by rfl) ⟨1299143, by rfl⟩ : syracuseStep 1732191 = 2598287) B2598287
theorem B19992187 : Blo 1731066 19992187 := bstep (se 1 (by rfl) ⟨14994140, by rfl⟩ : syracuseStep 19992187 = 29988281) B29988281
theorem B1732219 : Blo 1731066 1732219 := bstep (se 1 (by rfl) ⟨1299164, by rfl⟩ : syracuseStep 1732219 = 2598329) B2598329
theorem B1732271 : Blo 1731066 1732271 := bstep (se 1 (by rfl) ⟨1299203, by rfl⟩ : syracuseStep 1732271 = 2598407) B2598407
theorem B6573757 : Blo 1731066 6573757 := bstep (se 3 (by rfl) ⟨1232579, by rfl⟩ : syracuseStep 6573757 = 2465159) B2465159
theorem B3894983 : Blo 1731066 3894983 := bstep (se 1 (by rfl) ⟨2921237, by rfl⟩ : syracuseStep 3894983 = 5842475) B5842475
theorem B1732295 : Blo 1731066 1732295 := bstep (se 1 (by rfl) ⟨1299221, by rfl⟩ : syracuseStep 1732295 = 2598443) B2598443
theorem B9367255 : Blo 1731066 9367255 := bstep (se 1 (by rfl) ⟨7025441, by rfl⟩ : syracuseStep 9367255 = 14050883) B14050883
theorem B1732315 : Blo 1731066 1732315 := bstep (se 1 (by rfl) ⟨1299236, by rfl⟩ : syracuseStep 1732315 = 2598473) B2598473
theorem B3043063 : Blo 1731066 3043063 := bstep (se 1 (by rfl) ⟨2282297, by rfl⟩ : syracuseStep 3043063 = 4564595) B4564595
theorem B1732391 : Blo 1731066 1732391 := bstep (se 1 (by rfl) ⟨1299293, by rfl⟩ : syracuseStep 1732391 = 2598587) B2598587
theorem B1732431 : Blo 1731066 1732431 := bstep (se 1 (by rfl) ⟨1299323, by rfl⟩ : syracuseStep 1732431 = 2598647) B2598647
theorem B1732447 : Blo 1731066 1732447 := bstep (se 1 (by rfl) ⟨1299335, by rfl⟩ : syracuseStep 1732447 = 2598671) B2598671
theorem B3288937 : Blo 1731066 3288937 := bstep (se 2 (by rfl) ⟨1233351, by rfl⟩ : syracuseStep 3288937 = 2466703) B2466703
theorem B1732475 : Blo 1731066 1732475 := bstep (se 1 (by rfl) ⟨1299356, by rfl⟩ : syracuseStep 1732475 = 2598713) B2598713
theorem B1732527 : Blo 1731066 1732527 := bstep (se 1 (by rfl) ⟨1299395, by rfl⟩ : syracuseStep 1732527 = 2598791) B2598791
theorem B1732551 : Blo 1731066 1732551 := bstep (se 1 (by rfl) ⟨1299413, by rfl⟩ : syracuseStep 1732551 = 2598827) B2598827
theorem B1732571 : Blo 1731066 1732571 := bstep (se 1 (by rfl) ⟨1299428, by rfl⟩ : syracuseStep 1732571 = 2598857) B2598857
theorem B9367559 : Blo 1731066 9367559 := bstep (se 1 (by rfl) ⟨7025669, by rfl⟩ : syracuseStep 9367559 = 14051339) B14051339
theorem B1732647 : Blo 1731066 1732647 := bstep (se 1 (by rfl) ⟨1299485, by rfl⟩ : syracuseStep 1732647 = 2598971) B2598971
theorem B1732687 : Blo 1731066 1732687 := bstep (se 1 (by rfl) ⟨1299515, by rfl⟩ : syracuseStep 1732687 = 2599031) B2599031
theorem B1732703 : Blo 1731066 1732703 := bstep (se 1 (by rfl) ⟨1299527, by rfl⟩ : syracuseStep 1732703 = 2599055) B2599055
theorem B9867379 : Blo 1731066 9867379 := bstep (se 1 (by rfl) ⟨7400534, by rfl⟩ : syracuseStep 9867379 = 14801069) B14801069
theorem B1732731 : Blo 1731066 1732731 := bstep (se 1 (by rfl) ⟨1299548, by rfl⟩ : syracuseStep 1732731 = 2599097) B2599097
theorem B1732783 : Blo 1731066 1732783 := bstep (se 1 (by rfl) ⟨1299587, by rfl⟩ : syracuseStep 1732783 = 2599175) B2599175
theorem B1732807 : Blo 1731066 1732807 := bstep (se 1 (by rfl) ⟨1299605, by rfl⟩ : syracuseStep 1732807 = 2599211) B2599211
theorem B1732827 : Blo 1731066 1732827 := bstep (se 1 (by rfl) ⟨1299620, by rfl⟩ : syracuseStep 1732827 = 2599241) B2599241
theorem B14790923 : Blo 1731066 14790923 := bstep (se 1 (by rfl) ⟨11093192, by rfl⟩ : syracuseStep 14790923 = 22186385) B22186385
theorem B48730385 : Blo 1731066 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B1732903 : Blo 1731066 1732903 := bstep (se 1 (by rfl) ⟨1299677, by rfl⟩ : syracuseStep 1732903 = 2599355) B2599355
theorem B36049211 : Blo 1731066 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B1732943 : Blo 1731066 1732943 := bstep (se 1 (by rfl) ⟨1299707, by rfl⟩ : syracuseStep 1732943 = 2599415) B2599415
theorem B1732959 : Blo 1731066 1732959 := bstep (se 1 (by rfl) ⟨1299719, by rfl⟩ : syracuseStep 1732959 = 2599439) B2599439
theorem B13152617 : Blo 1731066 13152617 := bstep (se 2 (by rfl) ⟨4932231, by rfl⟩ : syracuseStep 13152617 = 9864463) B9864463
theorem B1732987 : Blo 1731066 1732987 := bstep (se 1 (by rfl) ⟨1299740, by rfl⟩ : syracuseStep 1732987 = 2599481) B2599481
theorem B5845391 : Blo 1731066 5845391 := bstep (se 1 (by rfl) ⟨4384043, by rfl⟩ : syracuseStep 5845391 = 8768087) B8768087
theorem B11096473 : Blo 1731066 11096473 := bstep (se 2 (by rfl) ⟨4161177, by rfl⟩ : syracuseStep 11096473 = 8322355) B8322355
theorem B1733039 : Blo 1731066 1733039 := bstep (se 1 (by rfl) ⟨1299779, by rfl⟩ : syracuseStep 1733039 = 2599559) B2599559
theorem B2191799 : Blo 1731066 2191799 := bstep (se 1 (by rfl) ⟨1643849, by rfl⟩ : syracuseStep 2191799 = 3287699) B3287699
theorem B1733063 : Blo 1731066 1733063 := bstep (se 1 (by rfl) ⟨1299797, by rfl⟩ : syracuseStep 1733063 = 2599595) B2599595
theorem B3699209 : Blo 1731066 3699209 := bstep (se 2 (by rfl) ⟨1387203, by rfl⟩ : syracuseStep 3699209 = 2774407) B2774407
theorem B9998873 : Blo 1731066 9998873 := bstep (se 2 (by rfl) ⟨3749577, by rfl⟩ : syracuseStep 9998873 = 7499155) B7499155
theorem B3895847 : Blo 1731066 3895847 := bstep (se 1 (by rfl) ⟨2921885, by rfl⟩ : syracuseStep 3895847 = 5843771) B5843771
theorem B2191951 : Blo 1731066 2191951 := bstep (se 1 (by rfl) ⟨1643963, by rfl⟩ : syracuseStep 2191951 = 3287927) B3287927
theorem B6574715 : Blo 1731066 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B12489389 : Blo 1731066 12489389 := bstep (se 3 (by rfl) ⟨2341760, by rfl⟩ : syracuseStep 12489389 = 4683521) B4683521
theorem B5845715 : Blo 1731066 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B7025363 : Blo 1731066 7025363 := bstep (se 1 (by rfl) ⟨5269022, by rfl⟩ : syracuseStep 7025363 = 10538045) B10538045
theorem B4682569 : Blo 1731066 4682569 := bstep (se 2 (by rfl) ⟨1755963, by rfl⟩ : syracuseStep 4682569 = 3511927) B3511927
theorem B3896171 : Blo 1731066 3896171 := bstep (se 1 (by rfl) ⟨2922128, by rfl⟩ : syracuseStep 3896171 = 5844257) B5844257
theorem B2921359 : Blo 1731066 2921359 := bstep (se 1 (by rfl) ⟨2191019, by rfl⟩ : syracuseStep 2921359 = 4382039) B4382039
theorem B6755233 : Blo 1731066 6755233 := bstep (se 2 (by rfl) ⟨2533212, by rfl⟩ : syracuseStep 6755233 = 5066425) B5066425
theorem B3896225 : Blo 1731066 3896225 := bstep (se 2 (by rfl) ⟨1461084, by rfl⟩ : syracuseStep 3896225 = 2922169) B2922169
theorem B2339803 : Blo 1731066 2339803 := bstep (se 1 (by rfl) ⟨1754852, by rfl⟩ : syracuseStep 2339803 = 3509705) B3509705
theorem B23712787 : Blo 1731066 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B51336341 : Blo 1731066 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B3896567 : Blo 1731066 3896567 := bstep (se 1 (by rfl) ⟨2922425, by rfl⟩ : syracuseStep 3896567 = 5844851) B5844851
theorem B3609929 : Blo 1731066 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B53302643 : Blo 1731066 53302643 := bstep (se 1 (by rfl) ⟨39976982, by rfl⟩ : syracuseStep 53302643 = 79953965) B79953965
theorem B6575489 : Blo 1731066 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B2922041 : Blo 1731066 2922041 := bstep (se 2 (by rfl) ⟨1095765, by rfl⟩ : syracuseStep 2922041 = 2191531) B2191531
theorem B45618785 : Blo 1731066 45618785 := bstep (se 2 (by rfl) ⟨17107044, by rfl⟩ : syracuseStep 45618785 = 34214089) B34214089
theorem B1848955 : Blo 1731066 1848955 := bstep (se 1 (by rfl) ⟨1386716, by rfl⟩ : syracuseStep 1848955 = 2773433) B2773433
theorem B2193095 : Blo 1731066 2193095 := bstep (se 1 (by rfl) ⟨1644821, by rfl⟩ : syracuseStep 2193095 = 3289643) B3289643
theorem B3897161 : Blo 1731066 3897161 := bstep (se 2 (by rfl) ⟨1461435, by rfl⟩ : syracuseStep 3897161 = 2922871) B2922871
theorem B1947487 : Blo 1731066 1947487 := bstep (se 1 (by rfl) ⟨1460615, by rfl⟩ : syracuseStep 1947487 = 2921231) B2921231
theorem B2193247 : Blo 1731066 2193247 := bstep (se 1 (by rfl) ⟨1644935, by rfl⟩ : syracuseStep 2193247 = 3289871) B3289871
theorem B5846903 : Blo 1731066 5846903 := bstep (se 1 (by rfl) ⟨4385177, by rfl⟩ : syracuseStep 5846903 = 8770355) B8770355
theorem B8771489 : Blo 1731066 8771489 := bstep (se 2 (by rfl) ⟨3289308, by rfl⟩ : syracuseStep 8771489 = 6578617) B6578617
theorem B5847119 : Blo 1731066 5847119 := bstep (se 1 (by rfl) ⟨4385339, by rfl⟩ : syracuseStep 5847119 = 8770679) B8770679
theorem B33306713 : Blo 1731066 33306713 := bstep (se 2 (by rfl) ⟨12490017, by rfl⟩ : syracuseStep 33306713 = 24980035) B24980035
theorem B2775163 : Blo 1731066 2775163 := bstep (se 1 (by rfl) ⟨2081372, by rfl⟩ : syracuseStep 2775163 = 4162745) B4162745
theorem B3750059 : Blo 1731066 3750059 := bstep (se 1 (by rfl) ⟨2812544, by rfl⟩ : syracuseStep 3750059 = 5625089) B5625089
theorem B5626027 : Blo 1731066 5626027 := bstep (se 1 (by rfl) ⟨4219520, by rfl⟩ : syracuseStep 5626027 = 8439041) B8439041
theorem B1947847 : Blo 1731066 1947847 := bstep (se 1 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 1947847 = 2921771) B2921771
theorem B2922743 : Blo 1731066 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B13154561 : Blo 1731066 13154561 := bstep (se 2 (by rfl) ⟨4932960, by rfl⟩ : syracuseStep 13154561 = 9865921) B9865921
theorem B14039401 : Blo 1731066 14039401 := bstep (se 2 (by rfl) ⟨5264775, by rfl⟩ : syracuseStep 14039401 = 10529551) B10529551
theorem B21363095 : Blo 1731066 21363095 := bstep (se 1 (by rfl) ⟨16022321, by rfl⟩ : syracuseStep 21363095 = 32044643) B32044643
theorem B1849775 : Blo 1731066 1849775 := bstep (se 1 (by rfl) ⟨1387331, by rfl⟩ : syracuseStep 1849775 = 2774663) B2774663
theorem B5847497 : Blo 1731066 5847497 := bstep (se 2 (by rfl) ⟨2192811, by rfl⟩ : syracuseStep 5847497 = 4385623) B4385623
theorem B14047769 : Blo 1731066 14047769 := bstep (se 2 (by rfl) ⟨5267913, by rfl⟩ : syracuseStep 14047769 = 10535827) B10535827
theorem B6576673 : Blo 1731066 6576673 := bstep (se 2 (by rfl) ⟨2466252, by rfl⟩ : syracuseStep 6576673 = 4932505) B4932505
theorem B2923087 : Blo 1731066 2923087 := bstep (se 1 (by rfl) ⟨2192315, by rfl⟩ : syracuseStep 2923087 = 4384631) B4384631
theorem B3897953 : Blo 1731066 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B5847767 : Blo 1731066 5847767 := bstep (se 1 (by rfl) ⟨4385825, by rfl⟩ : syracuseStep 5847767 = 8771651) B8771651
theorem B2923337 : Blo 1731066 2923337 := bstep (se 2 (by rfl) ⟨1096251, by rfl⟩ : syracuseStep 2923337 = 2192503) B2192503
theorem B5847983 : Blo 1731066 5847983 := bstep (se 1 (by rfl) ⟨4385987, by rfl⟩ : syracuseStep 5847983 = 8771975) B8771975
theorem B3898295 : Blo 1731066 3898295 := bstep (se 1 (by rfl) ⟨2923721, by rfl⟩ : syracuseStep 3898295 = 5847443) B5847443
theorem B6577159 : Blo 1731066 6577159 := bstep (se 1 (by rfl) ⟨4932869, by rfl⟩ : syracuseStep 6577159 = 9865739) B9865739
theorem B1948711 : Blo 1731066 1948711 := bstep (se 1 (by rfl) ⟨1461533, by rfl⟩ : syracuseStep 1948711 = 2923067) B2923067
theorem B1850407 : Blo 1731066 1850407 := bstep (se 1 (by rfl) ⟨1387805, by rfl⟩ : syracuseStep 1850407 = 2775611) B2775611
theorem B7117939 : Blo 1731066 7117939 := bstep (se 1 (by rfl) ⟨5338454, by rfl⟩ : syracuseStep 7117939 = 10676909) B10676909
theorem B2923769 : Blo 1731066 2923769 := bstep (se 2 (by rfl) ⟨1096413, by rfl⟩ : syracuseStep 2923769 = 2192827) B2192827
theorem B23698777 : Blo 1731066 23698777 := bstep (se 2 (by rfl) ⟨8887041, by rfl⟩ : syracuseStep 23698777 = 17774083) B17774083
theorem B2923951 : Blo 1731066 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B4382171 : Blo 1731066 4382171 := bstep (se 1 (by rfl) ⟨3286628, by rfl⟩ : syracuseStep 4382171 = 6573257) B6573257
theorem B6577645 : Blo 1731066 6577645 := bstep (se 3 (by rfl) ⟨1233308, by rfl⟩ : syracuseStep 6577645 = 2466617) B2466617
theorem B2924039 : Blo 1731066 2924039 := bstep (se 1 (by rfl) ⟨2193029, by rfl⟩ : syracuseStep 2924039 = 4386059) B4386059
theorem B3898889 : Blo 1731066 3898889 := bstep (se 2 (by rfl) ⟨1462083, by rfl⟩ : syracuseStep 3898889 = 2924167) B2924167
theorem B2596601 : Blo 1731066 2596601 := bstep (se 2 (by rfl) ⟨973725, by rfl⟩ : syracuseStep 2596601 = 1947451) B1947451
theorem B51289861 : Blo 1731066 51289861 := bstep (se 4 (by rfl) ⟨4808424, by rfl⟩ : syracuseStep 51289861 = 9616849) B9616849
theorem B6577949 : Blo 1731066 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B4931401 : Blo 1731066 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B2596703 : Blo 1731066 2596703 := bstep (se 1 (by rfl) ⟨1947527, by rfl⟩ : syracuseStep 2596703 = 3895055) B3895055
theorem B2924383 : Blo 1731066 2924383 := bstep (se 1 (by rfl) ⟨2193287, by rfl⟩ : syracuseStep 2924383 = 4386575) B4386575
theorem B3899231 : Blo 1731066 3899231 := bstep (se 1 (by rfl) ⟨2924423, by rfl⟩ : syracuseStep 3899231 = 5848847) B5848847
theorem B2596715 : Blo 1731066 2596715 := bstep (se 1 (by rfl) ⟨1947536, by rfl⟩ : syracuseStep 2596715 = 3895073) B3895073
theorem B4931435 : Blo 1731066 4931435 := bstep (se 1 (by rfl) ⟨3698576, by rfl⟩ : syracuseStep 4931435 = 7397153) B7397153
theorem B2924471 : Blo 1731066 2924471 := bstep (se 1 (by rfl) ⟨2193353, by rfl⟩ : syracuseStep 2924471 = 4386707) B4386707
theorem B29581361 : Blo 1731066 29581361 := bstep (se 2 (by rfl) ⟨11093010, by rfl⟩ : syracuseStep 29581361 = 22186021) B22186021
theorem B4382849 : Blo 1731066 4382849 := bstep (se 2 (by rfl) ⟨1643568, by rfl⟩ : syracuseStep 4382849 = 3287137) B3287137
theorem B13156505 : Blo 1731066 13156505 := bstep (se 2 (by rfl) ⟨4933689, by rfl⟩ : syracuseStep 13156505 = 9867379) B9867379
theorem B2597129 : Blo 1731066 2597129 := bstep (se 2 (by rfl) ⟨973923, by rfl⟩ : syracuseStep 2597129 = 1947847) B1947847
theorem B2466139 : Blo 1731066 2466139 := bstep (se 1 (by rfl) ⟨1849604, by rfl⟩ : syracuseStep 2466139 = 3699209) B3699209
theorem B2597231 : Blo 1731066 2597231 := bstep (se 1 (by rfl) ⟨1947923, by rfl⟩ : syracuseStep 2597231 = 3895847) B3895847
theorem B4383143 : Blo 1731066 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B13001161 : Blo 1731066 13001161 := bstep (se 2 (by rfl) ⟨4875435, by rfl⟩ : syracuseStep 13001161 = 9750871) B9750871
theorem B18719201 : Blo 1731066 18719201 := bstep (se 2 (by rfl) ⟨7019700, by rfl⟩ : syracuseStep 18719201 = 14039401) B14039401
theorem B14795297 : Blo 1731066 14795297 := bstep (se 2 (by rfl) ⟨5548236, by rfl⟩ : syracuseStep 14795297 = 11096473) B11096473
theorem B2597447 : Blo 1731066 2597447 := bstep (se 1 (by rfl) ⟨1948085, by rfl⟩ : syracuseStep 2597447 = 3896171) B3896171
theorem B4383305 : Blo 1731066 4383305 := bstep (se 2 (by rfl) ⟨1643739, by rfl⟩ : syracuseStep 4383305 = 3287479) B3287479
theorem B8323681 : Blo 1731066 8323681 := bstep (se 2 (by rfl) ⟨3121380, by rfl⟩ : syracuseStep 8323681 = 6242761) B6242761
theorem B37962341 : Blo 1731066 37962341 := bstep (se 4 (by rfl) ⟨3558969, by rfl⟩ : syracuseStep 37962341 = 7117939) B7117939
theorem B2597483 : Blo 1731066 2597483 := bstep (se 1 (by rfl) ⟨1948112, by rfl⟩ : syracuseStep 2597483 = 3896225) B3896225
theorem B2597711 : Blo 1731066 2597711 := bstep (se 1 (by rfl) ⟨1948283, by rfl⟩ : syracuseStep 2597711 = 3896567) B3896567
theorem B6243151 : Blo 1731066 6243151 := bstep (se 1 (by rfl) ⟨4682363, by rfl⟩ : syracuseStep 6243151 = 9364727) B9364727
theorem B4383659 : Blo 1731066 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B4383841 : Blo 1731066 4383841 := bstep (se 2 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 4383841 = 3287881) B3287881
theorem B6243425 : Blo 1731066 6243425 := bstep (se 2 (by rfl) ⟨2341284, by rfl⟩ : syracuseStep 6243425 = 4682569) B4682569
theorem B4932733 : Blo 1731066 4932733 := bstep (se 3 (by rfl) ⟨924887, by rfl⟩ : syracuseStep 4932733 = 1849775) B1849775
theorem B2598107 : Blo 1731066 2598107 := bstep (se 1 (by rfl) ⟨1948580, by rfl⟩ : syracuseStep 2598107 = 3897161) B3897161
theorem B12830075 : Blo 1731066 12830075 := bstep (se 1 (by rfl) ⟨9622556, by rfl⟩ : syracuseStep 12830075 = 19245113) B19245113
theorem B2598281 : Blo 1731066 2598281 := bstep (se 2 (by rfl) ⟨974355, by rfl⟩ : syracuseStep 2598281 = 1948711) B1948711
theorem B2500039 : Blo 1731066 2500039 := bstep (se 1 (by rfl) ⟨1875029, by rfl⟩ : syracuseStep 2500039 = 3750059) B3750059
theorem B9864737 : Blo 1731066 9864737 := bstep (se 2 (by rfl) ⟨3699276, by rfl⟩ : syracuseStep 9864737 = 7398553) B7398553
theorem B9365179 : Blo 1731066 9365179 := bstep (se 1 (by rfl) ⟨7023884, by rfl⟩ : syracuseStep 9365179 = 14047769) B14047769
theorem B2598635 : Blo 1731066 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B31598369 : Blo 1731066 31598369 := bstep (se 2 (by rfl) ⟨11849388, by rfl⟩ : syracuseStep 31598369 = 23698777) B23698777
theorem B8767439 : Blo 1731066 8767439 := bstep (se 1 (by rfl) ⟨6575579, by rfl⟩ : syracuseStep 8767439 = 13151159) B13151159
theorem B2598863 : Blo 1731066 2598863 := bstep (se 1 (by rfl) ⟨1949147, by rfl⟩ : syracuseStep 2598863 = 3898295) B3898295
theorem B4384793 : Blo 1731066 4384793 := bstep (se 2 (by rfl) ⟨1644297, by rfl⟩ : syracuseStep 4384793 = 3288595) B3288595
theorem B7899169 : Blo 1731066 7899169 := bstep (se 2 (by rfl) ⟨2962188, by rfl⟩ : syracuseStep 7899169 = 5924377) B5924377
theorem B4057417 : Blo 1731066 4057417 := bstep (se 2 (by rfl) ⟨1521531, by rfl⟩ : syracuseStep 4057417 = 3043063) B3043063
theorem B2599259 : Blo 1731066 2599259 := bstep (se 1 (by rfl) ⟨1949444, by rfl⟩ : syracuseStep 2599259 = 3898889) B3898889
theorem B4385249 : Blo 1731066 4385249 := bstep (se 2 (by rfl) ⟨1644468, by rfl⟩ : syracuseStep 4385249 = 3288937) B3288937
theorem B1731067 : Blo 1731066 1731067 := bstep (se 1 (by rfl) ⟨1298300, by rfl⟩ : syracuseStep 1731067 = 2596601) B2596601
theorem B4385299 : Blo 1731066 4385299 := bstep (se 1 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 4385299 = 6577949) B6577949
theorem B1731135 : Blo 1731066 1731135 := bstep (se 1 (by rfl) ⟨1298351, by rfl⟩ : syracuseStep 1731135 = 2596703) B2596703
theorem B2599487 : Blo 1731066 2599487 := bstep (se 1 (by rfl) ⟨1949615, by rfl⟩ : syracuseStep 2599487 = 3899231) B3899231
theorem B1731143 : Blo 1731066 1731143 := bstep (se 1 (by rfl) ⟨1298357, by rfl⟩ : syracuseStep 1731143 = 2596715) B2596715
theorem B3287623 : Blo 1731066 3287623 := bstep (se 1 (by rfl) ⟨2465717, by rfl⟩ : syracuseStep 3287623 = 4931435) B4931435
theorem B6245039 : Blo 1731066 6245039 := bstep (se 1 (by rfl) ⟨4683779, by rfl⟩ : syracuseStep 6245039 = 9367559) B9367559
theorem B1731295 : Blo 1731066 1731295 := bstep (se 1 (by rfl) ⟨1298471, by rfl⟩ : syracuseStep 1731295 = 2596943) B2596943
theorem B568519397 : Blo 1731066 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B1731375 : Blo 1731066 1731375 := bstep (se 1 (by rfl) ⟨1298531, by rfl⟩ : syracuseStep 1731375 = 2597063) B2597063
theorem B1731483 : Blo 1731066 1731483 := bstep (se 1 (by rfl) ⟨1298612, by rfl⟩ : syracuseStep 1731483 = 2597225) B2597225
theorem B8768411 : Blo 1731066 8768411 := bstep (se 1 (by rfl) ⟨6576308, by rfl⟩ : syracuseStep 8768411 = 13152617) B13152617
theorem B1731535 : Blo 1731066 1731535 := bstep (se 1 (by rfl) ⟨1298651, by rfl⟩ : syracuseStep 1731535 = 2597303) B2597303
theorem B1731559 : Blo 1731066 1731559 := bstep (se 1 (by rfl) ⟨1298669, by rfl⟩ : syracuseStep 1731559 = 2597339) B2597339
theorem B71068751 : Blo 1731066 71068751 := bstep (se 1 (by rfl) ⟨53301563, by rfl⟩ : syracuseStep 71068751 = 106603127) B106603127
theorem B8326259 : Blo 1731066 8326259 := bstep (se 1 (by rfl) ⟨6244694, by rfl⟩ : syracuseStep 8326259 = 12489389) B12489389
theorem B3697807 : Blo 1731066 3697807 := bstep (se 1 (by rfl) ⟨2773355, by rfl⟩ : syracuseStep 3697807 = 5546711) B5546711
theorem B1731871 : Blo 1731066 1731871 := bstep (se 1 (by rfl) ⟨1298903, by rfl⟩ : syracuseStep 1731871 = 2597807) B2597807
theorem B2813215 : Blo 1731066 2813215 := bstep (se 1 (by rfl) ⟨2109911, by rfl⟩ : syracuseStep 2813215 = 4219823) B4219823
theorem B1731931 : Blo 1731066 1731931 := bstep (se 1 (by rfl) ⟨1298948, by rfl⟩ : syracuseStep 1731931 = 2597897) B2597897
theorem B1731951 : Blo 1731066 1731951 := bstep (se 1 (by rfl) ⟨1298963, by rfl⟩ : syracuseStep 1731951 = 2597927) B2597927
theorem B8768897 : Blo 1731066 8768897 := bstep (se 2 (by rfl) ⟨3288336, by rfl⟩ : syracuseStep 8768897 = 6576673) B6576673
theorem B1732007 : Blo 1731066 1732007 := bstep (se 1 (by rfl) ⟨1299005, by rfl⟩ : syracuseStep 1732007 = 2598011) B2598011
theorem B5844473 : Blo 1731066 5844473 := bstep (se 2 (by rfl) ⟨2191677, by rfl⟩ : syracuseStep 5844473 = 4383355) B4383355
theorem B1732091 : Blo 1731066 1732091 := bstep (se 1 (by rfl) ⟨1299068, by rfl⟩ : syracuseStep 1732091 = 2598137) B2598137
theorem B3698183 : Blo 1731066 3698183 := bstep (se 1 (by rfl) ⟨2773637, by rfl⟩ : syracuseStep 3698183 = 5547275) B5547275
theorem B1732159 : Blo 1731066 1732159 := bstep (se 1 (by rfl) ⟨1299119, by rfl⟩ : syracuseStep 1732159 = 2598239) B2598239
theorem B1732167 : Blo 1731066 1732167 := bstep (se 1 (by rfl) ⟨1299125, by rfl⟩ : syracuseStep 1732167 = 2598251) B2598251
theorem B3288671 : Blo 1731066 3288671 := bstep (se 1 (by rfl) ⟨2466503, by rfl⟩ : syracuseStep 3288671 = 4933007) B4933007
theorem B1732319 : Blo 1731066 1732319 := bstep (se 1 (by rfl) ⟨1299239, by rfl⟩ : syracuseStep 1732319 = 2598479) B2598479
theorem B3895019 : Blo 1731066 3895019 := bstep (se 1 (by rfl) ⟨2921264, by rfl⟩ : syracuseStep 3895019 = 5842529) B5842529
theorem B30412523 : Blo 1731066 30412523 := bstep (se 1 (by rfl) ⟨22809392, by rfl⟩ : syracuseStep 30412523 = 45618785) B45618785
theorem B5844743 : Blo 1731066 5844743 := bstep (se 1 (by rfl) ⟨4383557, by rfl⟩ : syracuseStep 5844743 = 8767115) B8767115
theorem B2191151 : Blo 1731066 2191151 := bstep (se 1 (by rfl) ⟨1643363, by rfl⟩ : syracuseStep 2191151 = 3286727) B3286727
theorem B1732399 : Blo 1731066 1732399 := bstep (se 1 (by rfl) ⟨1299299, by rfl⟩ : syracuseStep 1732399 = 2598599) B2598599
theorem B5844797 : Blo 1731066 5844797 := bstep (se 3 (by rfl) ⟨1095899, by rfl⟩ : syracuseStep 5844797 = 2191799) B2191799
theorem B3895145 : Blo 1731066 3895145 := bstep (se 2 (by rfl) ⟨1460679, by rfl⟩ : syracuseStep 3895145 = 2921359) B2921359
theorem B9006977 : Blo 1731066 9006977 := bstep (se 2 (by rfl) ⟨3377616, by rfl⟩ : syracuseStep 9006977 = 6755233) B6755233
theorem B1732507 : Blo 1731066 1732507 := bstep (se 1 (by rfl) ⟨1299380, by rfl⟩ : syracuseStep 1732507 = 2598761) B2598761
theorem B1732559 : Blo 1731066 1732559 := bstep (se 1 (by rfl) ⟨1299419, by rfl⟩ : syracuseStep 1732559 = 2598839) B2598839
theorem B1732583 : Blo 1731066 1732583 := bstep (se 1 (by rfl) ⟨1299437, by rfl⟩ : syracuseStep 1732583 = 2598875) B2598875
theorem B8769545 : Blo 1731066 8769545 := bstep (se 2 (by rfl) ⟨3288579, by rfl⟩ : syracuseStep 8769545 = 6577159) B6577159
theorem B31617049 : Blo 1731066 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B22204475 : Blo 1731066 22204475 := bstep (se 1 (by rfl) ⟨16653356, by rfl⟩ : syracuseStep 22204475 = 33306713) B33306713
theorem B8769707 : Blo 1731066 8769707 := bstep (se 1 (by rfl) ⟨6577280, by rfl⟩ : syracuseStep 8769707 = 13154561) B13154561
theorem B17772803 : Blo 1731066 17772803 := bstep (se 1 (by rfl) ⟨13329602, by rfl⟩ : syracuseStep 17772803 = 26659205) B26659205
theorem B14242063 : Blo 1731066 14242063 := bstep (se 1 (by rfl) ⟨10681547, by rfl⟩ : syracuseStep 14242063 = 21363095) B21363095
theorem B1732895 : Blo 1731066 1732895 := bstep (se 1 (by rfl) ⟨1299671, by rfl⟩ : syracuseStep 1732895 = 2599343) B2599343
theorem B1732955 : Blo 1731066 1732955 := bstep (se 1 (by rfl) ⟨1299716, by rfl⟩ : syracuseStep 1732955 = 2599433) B2599433
theorem B1732975 : Blo 1731066 1732975 := bstep (se 1 (by rfl) ⟨1299731, by rfl⟩ : syracuseStep 1732975 = 2599463) B2599463
theorem B1733031 : Blo 1731066 1733031 := bstep (se 1 (by rfl) ⟨1299773, by rfl⟩ : syracuseStep 1733031 = 2599547) B2599547
theorem B3748279 : Blo 1731066 3748279 := bstep (se 1 (by rfl) ⟨2811209, by rfl⟩ : syracuseStep 3748279 = 5622419) B5622419
theorem B8319451 : Blo 1731066 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B3289673 : Blo 1731066 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B8770193 : Blo 1731066 8770193 := bstep (se 2 (by rfl) ⟨3288822, by rfl⟩ : syracuseStep 8770193 = 6577645) B6577645
theorem B3699371 : Blo 1731066 3699371 := bstep (se 1 (by rfl) ⟨2774528, by rfl⟩ : syracuseStep 3699371 = 5549057) B5549057
theorem B3895991 : Blo 1731066 3895991 := bstep (se 1 (by rfl) ⟨2921993, by rfl⟩ : syracuseStep 3895991 = 5843987) B5843987
theorem B13153103 : Blo 1731066 13153103 := bstep (se 1 (by rfl) ⟨9864827, by rfl⟩ : syracuseStep 13153103 = 19729655) B19729655
theorem B3896207 : Blo 1731066 3896207 := bstep (se 1 (by rfl) ⟨2922155, by rfl⟩ : syracuseStep 3896207 = 5844311) B5844311
theorem B12489673 : Blo 1731066 12489673 := bstep (se 2 (by rfl) ⟨4683627, by rfl⟩ : syracuseStep 12489673 = 9367255) B9367255
theorem B2921447 : Blo 1731066 2921447 := bstep (se 1 (by rfl) ⟨2191085, by rfl⟩ : syracuseStep 2921447 = 4382171) B4382171
theorem B30012407 : Blo 1731066 30012407 := bstep (se 1 (by rfl) ⟨22509305, by rfl⟩ : syracuseStep 30012407 = 45018611) B45018611
theorem B6575201 : Blo 1731066 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B2340073 : Blo 1731066 2340073 := bstep (se 2 (by rfl) ⟨877527, by rfl⟩ : syracuseStep 2340073 = 1755055) B1755055
theorem B5264801 : Blo 1731066 5264801 := bstep (se 2 (by rfl) ⟨1974300, by rfl⟩ : syracuseStep 5264801 = 3948601) B3948601
theorem B3700217 : Blo 1731066 3700217 := bstep (se 2 (by rfl) ⟨1387581, by rfl⟩ : syracuseStep 3700217 = 2775163) B2775163
theorem B9860615 : Blo 1731066 9860615 := bstep (se 1 (by rfl) ⟨7395461, by rfl⟩ : syracuseStep 9860615 = 14790923) B14790923
theorem B32486923 : Blo 1731066 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B9868837 : Blo 1731066 9868837 := bstep (se 4 (by rfl) ⟨925203, by rfl⟩ : syracuseStep 9868837 = 1850407) B1850407
theorem B24032807 : Blo 1731066 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B7501369 : Blo 1731066 7501369 := bstep (se 2 (by rfl) ⟨2813013, by rfl⟩ : syracuseStep 7501369 = 5626027) B5626027
theorem B3896927 : Blo 1731066 3896927 := bstep (se 1 (by rfl) ⟨2922695, by rfl⟩ : syracuseStep 3896927 = 5845391) B5845391
theorem B6665915 : Blo 1731066 6665915 := bstep (se 1 (by rfl) ⟨4999436, by rfl⟩ : syracuseStep 6665915 = 9998873) B9998873
theorem B3897143 : Blo 1731066 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B4683575 : Blo 1731066 4683575 := bstep (se 1 (by rfl) ⟨3512681, by rfl⟩ : syracuseStep 4683575 = 7025363) B7025363
theorem B9869111 : Blo 1731066 9869111 := bstep (se 1 (by rfl) ⟨7401833, by rfl⟩ : syracuseStep 9869111 = 14803667) B14803667
theorem B106624997 : Blo 1731066 106624997 := bstep (se 4 (by rfl) ⟨9996093, by rfl⟩ : syracuseStep 106624997 = 19992187) B19992187
theorem B34224227 : Blo 1731066 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B2922601 : Blo 1731066 2922601 := bstep (se 2 (by rfl) ⟨1095975, by rfl⟩ : syracuseStep 2922601 = 2191951) B2191951
theorem B3897449 : Blo 1731066 3897449 := bstep (se 2 (by rfl) ⟨1461543, by rfl⟩ : syracuseStep 3897449 = 2923087) B2923087
theorem B2406619 : Blo 1731066 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B35535095 : Blo 1731066 35535095 := bstep (se 1 (by rfl) ⟨26651321, by rfl⟩ : syracuseStep 35535095 = 53302643) B53302643
theorem B4929817 : Blo 1731066 4929817 := bstep (se 2 (by rfl) ⟨1848681, by rfl⟩ : syracuseStep 4929817 = 3697363) B3697363
theorem B1948027 : Blo 1731066 1948027 := bstep (se 1 (by rfl) ⟨1461020, by rfl⟩ : syracuseStep 1948027 = 2922041) B2922041
theorem B38492567 : Blo 1731066 38492567 := bstep (se 1 (by rfl) ⟨28869425, by rfl⟩ : syracuseStep 38492567 = 57738851) B57738851
theorem B3897935 : Blo 1731066 3897935 := bstep (se 1 (by rfl) ⟨2923451, by rfl⟩ : syracuseStep 3897935 = 5846903) B5846903
theorem B5847659 : Blo 1731066 5847659 := bstep (se 1 (by rfl) ⟨4385744, by rfl⟩ : syracuseStep 5847659 = 8771489) B8771489
theorem B3119737 : Blo 1731066 3119737 := bstep (se 2 (by rfl) ⟨1169901, by rfl⟩ : syracuseStep 3119737 = 2339803) B2339803
theorem B3898079 : Blo 1731066 3898079 := bstep (se 1 (by rfl) ⟨2923559, by rfl⟩ : syracuseStep 3898079 = 5847119) B5847119
theorem B126401309 : Blo 1731066 126401309 := bstep (se 3 (by rfl) ⟨23700245, by rfl⟩ : syracuseStep 126401309 = 47400491) B47400491
theorem B1948495 : Blo 1731066 1948495 := bstep (se 1 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 1948495 = 2922743) B2922743
theorem B3898331 : Blo 1731066 3898331 := bstep (se 1 (by rfl) ⟨2923748, by rfl⟩ : syracuseStep 3898331 = 5847497) B5847497
theorem B8772623 : Blo 1731066 8772623 := bstep (se 1 (by rfl) ⟨6579467, by rfl⟩ : syracuseStep 8772623 = 13158935) B13158935
theorem B3898511 : Blo 1731066 3898511 := bstep (se 1 (by rfl) ⟨2923883, by rfl⟩ : syracuseStep 3898511 = 5847767) B5847767
theorem B5848253 : Blo 1731066 5848253 := bstep (se 3 (by rfl) ⟨1096547, by rfl⟩ : syracuseStep 5848253 = 2193095) B2193095
theorem B7396571 : Blo 1731066 7396571 := bstep (se 1 (by rfl) ⟨5547428, by rfl⟩ : syracuseStep 7396571 = 11094857) B11094857
theorem B1948891 : Blo 1731066 1948891 := bstep (se 1 (by rfl) ⟨1461668, by rfl⟩ : syracuseStep 1948891 = 2923337) B2923337
theorem B3898601 : Blo 1731066 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B3898655 : Blo 1731066 3898655 := bstep (se 1 (by rfl) ⟨2923991, by rfl⟩ : syracuseStep 3898655 = 5847983) B5847983
theorem B4382201 : Blo 1731066 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B2465273 : Blo 1731066 2465273 := bstep (se 2 (by rfl) ⟨924477, by rfl⟩ : syracuseStep 2465273 = 1848955) B1848955
theorem B1949179 : Blo 1731066 1949179 := bstep (se 1 (by rfl) ⟨1461884, by rfl⟩ : syracuseStep 1949179 = 2923769) B2923769
theorem B7396879 : Blo 1731066 7396879 := bstep (se 1 (by rfl) ⟨5547659, by rfl⟩ : syracuseStep 7396879 = 11095319) B11095319
theorem B8765009 : Blo 1731066 8765009 := bstep (se 2 (by rfl) ⟨3286878, by rfl⟩ : syracuseStep 8765009 = 6573757) B6573757
theorem B1949359 : Blo 1731066 1949359 := bstep (se 1 (by rfl) ⟨1462019, by rfl⟩ : syracuseStep 1949359 = 2924039) B2924039
theorem B68386481 : Blo 1731066 68386481 := bstep (se 2 (by rfl) ⟨25644930, by rfl⟩ : syracuseStep 68386481 = 51289861) B51289861
theorem B2596649 : Blo 1731066 2596649 := bstep (se 2 (by rfl) ⟨973743, by rfl⟩ : syracuseStep 2596649 = 1947487) B1947487
theorem B2924329 : Blo 1731066 2924329 := bstep (se 2 (by rfl) ⟨1096623, by rfl⟩ : syracuseStep 2924329 = 2193247) B2193247
theorem B3899177 : Blo 1731066 3899177 := bstep (se 2 (by rfl) ⟨1462191, by rfl⟩ : syracuseStep 3899177 = 2924383) B2924383
theorem B2596655 : Blo 1731066 2596655 := bstep (se 1 (by rfl) ⟨1947491, by rfl⟩ : syracuseStep 2596655 = 3894983) B3894983
theorem B8773433 : Blo 1731066 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B1949647 : Blo 1731066 1949647 := bstep (se 1 (by rfl) ⟨1462235, by rfl⟩ : syracuseStep 1949647 = 2924471) B2924471
theorem B42156065 : Blo 1731066 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B14802983 : Blo 1731066 14802983 := bstep (se 1 (by rfl) ⟨11102237, by rfl⟩ : syracuseStep 14802983 = 22204475) B22204475
theorem B18989417 : Blo 1731066 18989417 := bstep (se 2 (by rfl) ⟨7121031, by rfl⟩ : syracuseStep 18989417 = 14242063) B14242063
theorem B9863531 : Blo 1731066 9863531 := bstep (se 1 (by rfl) ⟨7397648, by rfl⟩ : syracuseStep 9863531 = 14795297) B14795297
theorem B2597327 : Blo 1731066 2597327 := bstep (se 1 (by rfl) ⟨1947995, by rfl⟩ : syracuseStep 2597327 = 3895991) B3895991
theorem B2597369 : Blo 1731066 2597369 := bstep (se 2 (by rfl) ⟨974013, by rfl⟩ : syracuseStep 2597369 = 1948027) B1948027
theorem B4997705 : Blo 1731066 4997705 := bstep (se 2 (by rfl) ⟨1874139, by rfl⟩ : syracuseStep 4997705 = 3748279) B3748279
theorem B2597471 : Blo 1731066 2597471 := bstep (se 1 (by rfl) ⟨1948103, by rfl⟩ : syracuseStep 2597471 = 3896207) B3896207
theorem B17334881 : Blo 1731066 17334881 := bstep (se 2 (by rfl) ⟨6500580, by rfl⟩ : syracuseStep 17334881 = 13001161) B13001161
theorem B11092601 : Blo 1731066 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B4383467 : Blo 1731066 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B4162283 : Blo 1731066 4162283 := bstep (se 1 (by rfl) ⟨3121712, by rfl⟩ : syracuseStep 4162283 = 6243425) B6243425
theorem B4383497 : Blo 1731066 4383497 := bstep (se 2 (by rfl) ⟨1643811, by rfl⟩ : syracuseStep 4383497 = 3287623) B3287623
theorem B8553383 : Blo 1731066 8553383 := bstep (se 1 (by rfl) ⟨6415037, by rfl⟩ : syracuseStep 8553383 = 12830075) B12830075
theorem B2466811 : Blo 1731066 2466811 := bstep (se 1 (by rfl) ⟨1850108, by rfl⟩ : syracuseStep 2466811 = 3700217) B3700217
theorem B2597951 : Blo 1731066 2597951 := bstep (se 1 (by rfl) ⟨1948463, by rfl⟩ : syracuseStep 2597951 = 3896927) B3896927
theorem B2597993 : Blo 1731066 2597993 := bstep (se 2 (by rfl) ⟨974247, by rfl⟩ : syracuseStep 2597993 = 1948495) B1948495
theorem B8324201 : Blo 1731066 8324201 := bstep (se 2 (by rfl) ⟨3121575, by rfl⟩ : syracuseStep 8324201 = 6243151) B6243151
theorem B2598095 : Blo 1731066 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B3122383 : Blo 1731066 3122383 := bstep (se 1 (by rfl) ⟨2341787, by rfl⟩ : syracuseStep 3122383 = 4683575) B4683575
theorem B6579407 : Blo 1731066 6579407 := bstep (se 1 (by rfl) ⟨4934555, by rfl⟩ : syracuseStep 6579407 = 9869111) B9869111
theorem B71083331 : Blo 1731066 71083331 := bstep (se 1 (by rfl) ⟨53312498, by rfl⟩ : syracuseStep 71083331 = 106624997) B106624997
theorem B22816151 : Blo 1731066 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B2598299 : Blo 1731066 2598299 := bstep (se 1 (by rfl) ⟨1948724, by rfl⟩ : syracuseStep 2598299 = 3897449) B3897449
theorem B2598521 : Blo 1731066 2598521 := bstep (se 2 (by rfl) ⟨974445, by rfl⟩ : syracuseStep 2598521 = 1948891) B1948891
theorem B2598623 : Blo 1731066 2598623 := bstep (se 1 (by rfl) ⟨1948967, by rfl⟩ : syracuseStep 2598623 = 3897935) B3897935
theorem B9864989 : Blo 1731066 9864989 := bstep (se 3 (by rfl) ⟨1849685, by rfl⟩ : syracuseStep 9864989 = 3699371) B3699371
theorem B2598719 : Blo 1731066 2598719 := bstep (se 1 (by rfl) ⟨1949039, by rfl⟩ : syracuseStep 2598719 = 3898079) B3898079
theorem B379012931 : Blo 1731066 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B2598887 : Blo 1731066 2598887 := bstep (se 1 (by rfl) ⟨1949165, by rfl⟩ : syracuseStep 2598887 = 3898331) B3898331
theorem B2598905 : Blo 1731066 2598905 := bstep (se 2 (by rfl) ⟨974589, by rfl⟩ : syracuseStep 2598905 = 1949179) B1949179
theorem B13158449 : Blo 1731066 13158449 := bstep (se 2 (by rfl) ⟨4934418, by rfl⟩ : syracuseStep 13158449 = 9868837) B9868837
theorem B2599007 : Blo 1731066 2599007 := bstep (se 1 (by rfl) ⟨1949255, by rfl⟩ : syracuseStep 2599007 = 3898511) B3898511
theorem B5843069 : Blo 1731066 5843069 := bstep (se 3 (by rfl) ⟨1095575, by rfl⟩ : syracuseStep 5843069 = 2191151) B2191151
theorem B2599067 : Blo 1731066 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B2599103 : Blo 1731066 2599103 := bstep (se 1 (by rfl) ⟨1949327, by rfl⟩ : syracuseStep 2599103 = 3898655) B3898655
theorem B2599145 : Blo 1731066 2599145 := bstep (se 2 (by rfl) ⟨974679, by rfl⟩ : syracuseStep 2599145 = 1949359) B1949359
theorem B12486905 : Blo 1731066 12486905 := bstep (se 2 (by rfl) ⟨4682589, by rfl⟩ : syracuseStep 12486905 = 9365179) B9365179
theorem B5843339 : Blo 1731066 5843339 := bstep (se 1 (by rfl) ⟨4382504, by rfl⟩ : syracuseStep 5843339 = 8765009) B8765009
theorem B45590987 : Blo 1731066 45590987 := bstep (se 1 (by rfl) ⟨34193240, by rfl⟩ : syracuseStep 45590987 = 68386481) B68386481
theorem B1731099 : Blo 1731066 1731099 := bstep (se 1 (by rfl) ⟨1298324, by rfl⟩ : syracuseStep 1731099 = 2596649) B2596649
theorem B2599451 : Blo 1731066 2599451 := bstep (se 1 (by rfl) ⟨1949588, by rfl⟩ : syracuseStep 2599451 = 3899177) B3899177
theorem B1731103 : Blo 1731066 1731103 := bstep (se 1 (by rfl) ⟨1298327, by rfl⟩ : syracuseStep 1731103 = 2596655) B2596655
theorem B2599529 : Blo 1731066 2599529 := bstep (se 2 (by rfl) ⟨974823, by rfl⟩ : syracuseStep 2599529 = 1949647) B1949647
theorem B19720907 : Blo 1731066 19720907 := bstep (se 1 (by rfl) ⟨14790680, by rfl⟩ : syracuseStep 19720907 = 29581361) B29581361
theorem B11848535 : Blo 1731066 11848535 := bstep (se 1 (by rfl) ⟨8886401, by rfl⟩ : syracuseStep 11848535 = 17772803) B17772803
theorem B1731419 : Blo 1731066 1731419 := bstep (se 1 (by rfl) ⟨1298564, by rfl⟩ : syracuseStep 1731419 = 2597129) B2597129
theorem B1731487 : Blo 1731066 1731487 := bstep (se 1 (by rfl) ⟨1298615, by rfl⟩ : syracuseStep 1731487 = 2597231) B2597231
theorem B12479467 : Blo 1731066 12479467 := bstep (se 1 (by rfl) ⟨9359600, by rfl⟩ : syracuseStep 12479467 = 18719201) B18719201
theorem B6573089 : Blo 1731066 6573089 := bstep (se 2 (by rfl) ⟨2464908, by rfl⟩ : syracuseStep 6573089 = 4929817) B4929817
theorem B1731631 : Blo 1731066 1731631 := bstep (se 1 (by rfl) ⟨1298723, by rfl⟩ : syracuseStep 1731631 = 2597447) B2597447
theorem B25308227 : Blo 1731066 25308227 := bstep (se 1 (by rfl) ⟨18981170, by rfl⟩ : syracuseStep 25308227 = 37962341) B37962341
theorem B1731655 : Blo 1731066 1731655 := bstep (se 1 (by rfl) ⟨1298741, by rfl⟩ : syracuseStep 1731655 = 2597483) B2597483
theorem B3288185 : Blo 1731066 3288185 := bstep (se 2 (by rfl) ⟨1233069, by rfl⟩ : syracuseStep 3288185 = 2466139) B2466139
theorem B1731807 : Blo 1731066 1731807 := bstep (se 1 (by rfl) ⟨1298855, by rfl⟩ : syracuseStep 1731807 = 2597711) B2597711
theorem B8768735 : Blo 1731066 8768735 := bstep (se 1 (by rfl) ⟨6576551, by rfl⟩ : syracuseStep 8768735 = 13153103) B13153103
theorem B20008271 : Blo 1731066 20008271 := bstep (se 1 (by rfl) ⟨15006203, by rfl⟩ : syracuseStep 20008271 = 30012407) B30012407
theorem B1732071 : Blo 1731066 1732071 := bstep (se 1 (by rfl) ⟨1299053, by rfl⟩ : syracuseStep 1732071 = 2598107) B2598107
theorem B1732187 : Blo 1731066 1732187 := bstep (se 1 (by rfl) ⟨1299140, by rfl⟩ : syracuseStep 1732187 = 2598281) B2598281
theorem B3509867 : Blo 1731066 3509867 := bstep (se 1 (by rfl) ⟨2632400, by rfl⟩ : syracuseStep 3509867 = 5264801) B5264801
theorem B6573743 : Blo 1731066 6573743 := bstep (se 1 (by rfl) ⟨4930307, by rfl⟩ : syracuseStep 6573743 = 9860615) B9860615
theorem B4443943 : Blo 1731066 4443943 := bstep (se 1 (by rfl) ⟨3332957, by rfl⟩ : syracuseStep 4443943 = 6665915) B6665915
theorem B1732423 : Blo 1731066 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B21065579 : Blo 1731066 21065579 := bstep (se 1 (by rfl) ⟨15799184, by rfl⟩ : syracuseStep 21065579 = 31598369) B31598369
theorem B12480389 : Blo 1731066 12480389 := bstep (se 4 (by rfl) ⟨1170036, by rfl⟩ : syracuseStep 12480389 = 2340073) B2340073
theorem B5844959 : Blo 1731066 5844959 := bstep (se 1 (by rfl) ⟨4383719, by rfl⟩ : syracuseStep 5844959 = 8767439) B8767439
theorem B1732575 : Blo 1731066 1732575 := bstep (se 1 (by rfl) ⟨1299431, by rfl⟩ : syracuseStep 1732575 = 2598863) B2598863
theorem B6574061 : Blo 1731066 6574061 := bstep (se 3 (by rfl) ⟨1232636, by rfl⟩ : syracuseStep 6574061 = 2465273) B2465273
theorem B5845121 : Blo 1731066 5845121 := bstep (se 2 (by rfl) ⟨2191920, by rfl⟩ : syracuseStep 5845121 = 4383841) B4383841
theorem B1732839 : Blo 1731066 1732839 := bstep (se 1 (by rfl) ⟨1299629, by rfl⟩ : syracuseStep 1732839 = 2599259) B2599259
theorem B25661711 : Blo 1731066 25661711 := bstep (se 1 (by rfl) ⟨19246283, by rfl⟩ : syracuseStep 25661711 = 38492567) B38492567
theorem B1732991 : Blo 1731066 1732991 := bstep (se 1 (by rfl) ⟨1299743, by rfl⟩ : syracuseStep 1732991 = 2599487) B2599487
theorem B21639557 : Blo 1731066 21639557 := bstep (se 4 (by rfl) ⟨2028708, by rfl⟩ : syracuseStep 21639557 = 4057417) B4057417
theorem B84267539 : Blo 1731066 84267539 := bstep (se 1 (by rfl) ⟨63200654, by rfl⟩ : syracuseStep 84267539 = 126401309) B126401309
theorem B5845607 : Blo 1731066 5845607 := bstep (se 1 (by rfl) ⟨4384205, by rfl⟩ : syracuseStep 5845607 = 8768411) B8768411
theorem B43315897 : Blo 1731066 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B47379167 : Blo 1731066 47379167 := bstep (se 1 (by rfl) ⟨35534375, by rfl⟩ : syracuseStep 47379167 = 71068751) B71068751
theorem B5550839 : Blo 1731066 5550839 := bstep (se 1 (by rfl) ⟨4163129, by rfl⟩ : syracuseStep 5550839 = 8326259) B8326259
theorem B5845931 : Blo 1731066 5845931 := bstep (se 1 (by rfl) ⟨4384448, by rfl⟩ : syracuseStep 5845931 = 8768897) B8768897
theorem B2921467 : Blo 1731066 2921467 := bstep (se 1 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 2921467 = 4382201) B4382201
theorem B3896315 : Blo 1731066 3896315 := bstep (se 1 (by rfl) ⟨2922236, by rfl⟩ : syracuseStep 3896315 = 5844473) B5844473
theorem B13333541 : Blo 1731066 13333541 := bstep (se 4 (by rfl) ⟨1250019, by rfl⟩ : syracuseStep 13333541 = 2500039) B2500039
theorem B2192447 : Blo 1731066 2192447 := bstep (se 1 (by rfl) ⟨1644335, by rfl⟩ : syracuseStep 2192447 = 3288671) B3288671
theorem B3896495 : Blo 1731066 3896495 := bstep (se 1 (by rfl) ⟨2922371, by rfl⟩ : syracuseStep 3896495 = 5844743) B5844743
theorem B3896531 : Blo 1731066 3896531 := bstep (se 1 (by rfl) ⟨2922398, by rfl⟩ : syracuseStep 3896531 = 5844797) B5844797
theorem B5846363 : Blo 1731066 5846363 := bstep (se 1 (by rfl) ⟨4384772, by rfl⟩ : syracuseStep 5846363 = 8769545) B8769545
theorem B10532225 : Blo 1731066 10532225 := bstep (se 2 (by rfl) ⟨3949584, by rfl⟩ : syracuseStep 10532225 = 7899169) B7899169
theorem B2921899 : Blo 1731066 2921899 := bstep (se 1 (by rfl) ⟨2191424, by rfl⟩ : syracuseStep 2921899 = 4382849) B4382849
theorem B8771003 : Blo 1731066 8771003 := bstep (se 1 (by rfl) ⟨6578252, by rfl⟩ : syracuseStep 8771003 = 13156505) B13156505
theorem B5846471 : Blo 1731066 5846471 := bstep (se 1 (by rfl) ⟨4384853, by rfl⟩ : syracuseStep 5846471 = 8769707) B8769707
theorem B3896801 : Blo 1731066 3896801 := bstep (se 2 (by rfl) ⟨1461300, by rfl⟩ : syracuseStep 3896801 = 2922601) B2922601
theorem B2922095 : Blo 1731066 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B3208825 : Blo 1731066 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B2922203 : Blo 1731066 2922203 := bstep (se 1 (by rfl) ⟨2191652, by rfl⟩ : syracuseStep 2922203 = 4383305) B4383305
theorem B5846795 : Blo 1731066 5846795 := bstep (se 1 (by rfl) ⟨4385096, by rfl⟩ : syracuseStep 5846795 = 8770193) B8770193
theorem B2922439 : Blo 1731066 2922439 := bstep (se 1 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 2922439 = 4383659) B4383659
theorem B1947631 : Blo 1731066 1947631 := bstep (se 1 (by rfl) ⟨1460723, by rfl⟩ : syracuseStep 1947631 = 2921447) B2921447
theorem B5847065 : Blo 1731066 5847065 := bstep (se 2 (by rfl) ⟨2192649, by rfl⟩ : syracuseStep 5847065 = 4385299) B4385299
theorem B11098241 : Blo 1731066 11098241 := bstep (se 2 (by rfl) ⟨4161840, by rfl⟩ : syracuseStep 11098241 = 8323681) B8323681
theorem B4159649 : Blo 1731066 4159649 := bstep (se 2 (by rfl) ⟨1559868, by rfl⟩ : syracuseStep 4159649 = 3119737) B3119737
theorem B6576491 : Blo 1731066 6576491 := bstep (se 1 (by rfl) ⟨4932368, by rfl⟩ : syracuseStep 6576491 = 9864737) B9864737
theorem B16021871 : Blo 1731066 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B16652897 : Blo 1731066 16652897 := bstep (se 2 (by rfl) ⟨6244836, by rfl⟩ : syracuseStep 16652897 = 12489673) B12489673
theorem B2923195 : Blo 1731066 2923195 := bstep (se 1 (by rfl) ⟨2192396, by rfl⟩ : syracuseStep 2923195 = 4384793) B4384793
theorem B9861821 : Blo 1731066 9861821 := bstep (se 3 (by rfl) ⟨1849091, by rfl⟩ : syracuseStep 9861821 = 3698183) B3698183
theorem B23690063 : Blo 1731066 23690063 := bstep (se 1 (by rfl) ⟨17767547, by rfl⟩ : syracuseStep 23690063 = 35535095) B35535095
theorem B6576977 : Blo 1731066 6576977 := bstep (se 2 (by rfl) ⟨2466366, by rfl⟩ : syracuseStep 6576977 = 4932733) B4932733
theorem B4930409 : Blo 1731066 4930409 := bstep (se 2 (by rfl) ⟨1848903, by rfl⟩ : syracuseStep 4930409 = 3697807) B3697807
theorem B8772461 : Blo 1731066 8772461 := bstep (se 3 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 8772461 = 3289673) B3289673
theorem B2923499 : Blo 1731066 2923499 := bstep (se 1 (by rfl) ⟨2192624, by rfl⟩ : syracuseStep 2923499 = 4385249) B4385249
theorem B3750953 : Blo 1731066 3750953 := bstep (se 2 (by rfl) ⟨1406607, by rfl⟩ : syracuseStep 3750953 = 2813215) B2813215
theorem B3898439 : Blo 1731066 3898439 := bstep (se 1 (by rfl) ⟨2923829, by rfl⟩ : syracuseStep 3898439 = 5847659) B5847659
theorem B16653437 : Blo 1731066 16653437 := bstep (se 3 (by rfl) ⟨3122519, by rfl⟩ : syracuseStep 16653437 = 6245039) B6245039
theorem B81100061 : Blo 1731066 81100061 := bstep (se 3 (by rfl) ⟨15206261, by rfl⟩ : syracuseStep 81100061 = 30412523) B30412523
theorem B5848415 : Blo 1731066 5848415 := bstep (se 1 (by rfl) ⟨4386311, by rfl⟩ : syracuseStep 5848415 = 8772623) B8772623
theorem B9862505 : Blo 1731066 9862505 := bstep (se 2 (by rfl) ⟨3698439, by rfl⟩ : syracuseStep 9862505 = 7396879) B7396879
theorem B10001825 : Blo 1731066 10001825 := bstep (se 2 (by rfl) ⟨3750684, by rfl⟩ : syracuseStep 10001825 = 7501369) B7501369
theorem B3898835 : Blo 1731066 3898835 := bstep (se 1 (by rfl) ⟨2924126, by rfl⟩ : syracuseStep 3898835 = 5848253) B5848253
theorem B4931047 : Blo 1731066 4931047 := bstep (se 1 (by rfl) ⟨3698285, by rfl⟩ : syracuseStep 4931047 = 7396571) B7396571
theorem B3899105 : Blo 1731066 3899105 := bstep (se 2 (by rfl) ⟨1462164, by rfl⟩ : syracuseStep 3899105 = 2924329) B2924329
theorem B2596679 : Blo 1731066 2596679 := bstep (se 1 (by rfl) ⟨1947509, by rfl⟩ : syracuseStep 2596679 = 3895019) B3895019
theorem B5848955 : Blo 1731066 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B2596763 : Blo 1731066 2596763 := bstep (se 1 (by rfl) ⟨1947572, by rfl⟩ : syracuseStep 2596763 = 3895145) B3895145
theorem B6004651 : Blo 1731066 6004651 := bstep (se 1 (by rfl) ⟨4503488, by rfl⟩ : syracuseStep 6004651 = 9006977) B9006977
theorem B10002541 : Blo 1731066 10002541 := bstep (se 3 (by rfl) ⟨1875476, by rfl⟩ : syracuseStep 10002541 = 3750953) B3750953
theorem B14426371 : Blo 1731066 14426371 := bstep (se 1 (by rfl) ⟨10819778, by rfl⟩ : syracuseStep 14426371 = 21639557) B21639557
theorem B5702255 : Blo 1731066 5702255 := bstep (se 1 (by rfl) ⟨4276691, by rfl⟩ : syracuseStep 5702255 = 8553383) B8553383
theorem B2597543 : Blo 1731066 2597543 := bstep (se 1 (by rfl) ⟨1948157, by rfl⟩ : syracuseStep 2597543 = 3896315) B3896315
theorem B2597663 : Blo 1731066 2597663 := bstep (se 1 (by rfl) ⟨1948247, by rfl⟩ : syracuseStep 2597663 = 3896495) B3896495
theorem B2597687 : Blo 1731066 2597687 := bstep (se 1 (by rfl) ⟨1948265, by rfl⟩ : syracuseStep 2597687 = 3896531) B3896531
theorem B57754529 : Blo 1731066 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B2597867 : Blo 1731066 2597867 := bstep (se 1 (by rfl) ⟨1948400, by rfl⟩ : syracuseStep 2597867 = 3896801) B3896801
theorem B252675287 : Blo 1731066 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B16639289 : Blo 1731066 16639289 := bstep (se 2 (by rfl) ⟨6239733, by rfl⟩ : syracuseStep 16639289 = 12479467) B12479467
theorem B7398827 : Blo 1731066 7398827 := bstep (se 1 (by rfl) ⟨5549120, by rfl⟩ : syracuseStep 7398827 = 11098241) B11098241
theorem B8324603 : Blo 1731066 8324603 := bstep (se 1 (by rfl) ⟨6243452, by rfl⟩ : syracuseStep 8324603 = 12486905) B12486905
theorem B4384327 : Blo 1731066 4384327 := bstep (se 1 (by rfl) ⟨3288245, by rfl⟩ : syracuseStep 4384327 = 6576491) B6576491
theorem B4163177 : Blo 1731066 4163177 := bstep (se 2 (by rfl) ⟨1561191, by rfl⟩ : syracuseStep 4163177 = 3122383) B3122383
theorem B30393991 : Blo 1731066 30393991 := bstep (se 1 (by rfl) ⟨22795493, by rfl⟩ : syracuseStep 30393991 = 45590987) B45590987
theorem B11101931 : Blo 1731066 11101931 := bstep (se 1 (by rfl) ⟨8326448, by rfl⟩ : syracuseStep 11101931 = 16652897) B16652897
theorem B4384651 : Blo 1731066 4384651 := bstep (se 1 (by rfl) ⟨3288488, by rfl⟩ : syracuseStep 4384651 = 6576977) B6576977
theorem B7899023 : Blo 1731066 7899023 := bstep (se 1 (by rfl) ⟨5924267, by rfl⟩ : syracuseStep 7899023 = 11848535) B11848535
theorem B2598959 : Blo 1731066 2598959 := bstep (se 1 (by rfl) ⟨1949219, by rfl⟩ : syracuseStep 2598959 = 3898439) B3898439
theorem B11102291 : Blo 1731066 11102291 := bstep (se 1 (by rfl) ⟨8326718, by rfl⟩ : syracuseStep 11102291 = 16653437) B16653437
theorem B4278433 : Blo 1731066 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B13338847 : Blo 1731066 13338847 := bstep (se 1 (by rfl) ⟨10004135, by rfl⟩ : syracuseStep 13338847 = 20008271) B20008271
theorem B2599223 : Blo 1731066 2599223 := bstep (se 1 (by rfl) ⟨1949417, by rfl⟩ : syracuseStep 2599223 = 3898835) B3898835
theorem B5925257 : Blo 1731066 5925257 := bstep (se 2 (by rfl) ⟨2221971, by rfl⟩ : syracuseStep 5925257 = 4443943) B4443943
theorem B2599403 : Blo 1731066 2599403 := bstep (se 1 (by rfl) ⟨1949552, by rfl⟩ : syracuseStep 2599403 = 3899105) B3899105
theorem B1731119 : Blo 1731066 1731119 := bstep (se 1 (by rfl) ⟨1298339, by rfl⟩ : syracuseStep 1731119 = 2596679) B2596679
theorem B8006201 : Blo 1731066 8006201 := bstep (se 2 (by rfl) ⟨3002325, by rfl⟩ : syracuseStep 8006201 = 6004651) B6004651
theorem B14043719 : Blo 1731066 14043719 := bstep (se 1 (by rfl) ⟨10532789, by rfl⟩ : syracuseStep 14043719 = 21065579) B21065579
theorem B1731175 : Blo 1731066 1731175 := bstep (se 1 (by rfl) ⟨1298381, by rfl⟩ : syracuseStep 1731175 = 2596763) B2596763
theorem B12659611 : Blo 1731066 12659611 := bstep (se 1 (by rfl) ⟨9494708, by rfl⟩ : syracuseStep 12659611 = 18989417) B18989417
theorem B1731551 : Blo 1731066 1731551 := bstep (se 1 (by rfl) ⟨1298663, by rfl⟩ : syracuseStep 1731551 = 2597327) B2597327
theorem B1731579 : Blo 1731066 1731579 := bstep (se 1 (by rfl) ⟨1298684, by rfl⟩ : syracuseStep 1731579 = 2597369) B2597369
theorem B142224437 : Blo 1731066 142224437 := bstep (se 5 (by rfl) ⟨6666770, by rfl⟩ : syracuseStep 142224437 = 13333541) B13333541
theorem B1731647 : Blo 1731066 1731647 := bstep (se 1 (by rfl) ⟨1298735, by rfl⟩ : syracuseStep 1731647 = 2597471) B2597471
theorem B68431229 : Blo 1731066 68431229 := bstep (se 3 (by rfl) ⟨12830855, by rfl⟩ : syracuseStep 68431229 = 25661711) B25661711
theorem B1731967 : Blo 1731066 1731967 := bstep (se 1 (by rfl) ⟨1298975, by rfl⟩ : syracuseStep 1731967 = 2597951) B2597951
theorem B1731995 : Blo 1731066 1731995 := bstep (se 1 (by rfl) ⟨1298996, by rfl⟩ : syracuseStep 1731995 = 2597993) B2597993
theorem B5549467 : Blo 1731066 5549467 := bstep (se 1 (by rfl) ⟨4162100, by rfl⟩ : syracuseStep 5549467 = 8324201) B8324201
theorem B1732063 : Blo 1731066 1732063 := bstep (se 1 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 1732063 = 2598095) B2598095
theorem B4386271 : Blo 1731066 4386271 := bstep (se 1 (by rfl) ⟨3289703, by rfl⟩ : syracuseStep 4386271 = 6579407) B6579407
theorem B1732199 : Blo 1731066 1732199 := bstep (se 1 (by rfl) ⟨1299149, by rfl⟩ : syracuseStep 1732199 = 2598299) B2598299
theorem B28085933 : Blo 1731066 28085933 := bstep (se 3 (by rfl) ⟨5266112, by rfl⟩ : syracuseStep 28085933 = 10532225) B10532225
theorem B1732347 : Blo 1731066 1732347 := bstep (se 1 (by rfl) ⟨1299260, by rfl⟩ : syracuseStep 1732347 = 2598521) B2598521
theorem B1732415 : Blo 1731066 1732415 := bstep (se 1 (by rfl) ⟨1299311, by rfl⟩ : syracuseStep 1732415 = 2598623) B2598623
theorem B1732479 : Blo 1731066 1732479 := bstep (se 1 (by rfl) ⟨1299359, by rfl⟩ : syracuseStep 1732479 = 2598719) B2598719
theorem B1732591 : Blo 1731066 1732591 := bstep (se 1 (by rfl) ⟨1299443, by rfl⟩ : syracuseStep 1732591 = 2598887) B2598887
theorem B3895289 : Blo 1731066 3895289 := bstep (se 2 (by rfl) ⟨1460733, by rfl⟩ : syracuseStep 3895289 = 2921467) B2921467
theorem B3289081 : Blo 1731066 3289081 := bstep (se 2 (by rfl) ⟨1233405, by rfl⟩ : syracuseStep 3289081 = 2466811) B2466811
theorem B1732603 : Blo 1731066 1732603 := bstep (se 1 (by rfl) ⟨1299452, by rfl⟩ : syracuseStep 1732603 = 2598905) B2598905
theorem B1732671 : Blo 1731066 1732671 := bstep (se 1 (by rfl) ⟨1299503, by rfl⟩ : syracuseStep 1732671 = 2599007) B2599007
theorem B3895379 : Blo 1731066 3895379 := bstep (se 1 (by rfl) ⟨2921534, by rfl⟩ : syracuseStep 3895379 = 5843069) B5843069
theorem B1732711 : Blo 1731066 1732711 := bstep (se 1 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 1732711 = 2599067) B2599067
theorem B2773099 : Blo 1731066 2773099 := bstep (se 1 (by rfl) ⟨2079824, by rfl⟩ : syracuseStep 2773099 = 4159649) B4159649
theorem B1732735 : Blo 1731066 1732735 := bstep (se 1 (by rfl) ⟨1299551, by rfl⟩ : syracuseStep 1732735 = 2599103) B2599103
theorem B1732763 : Blo 1731066 1732763 := bstep (se 1 (by rfl) ⟨1299572, by rfl⟩ : syracuseStep 1732763 = 2599145) B2599145
theorem B3895559 : Blo 1731066 3895559 := bstep (se 1 (by rfl) ⟨2921669, by rfl⟩ : syracuseStep 3895559 = 5843339) B5843339
theorem B1732967 : Blo 1731066 1732967 := bstep (se 1 (by rfl) ⟨1299725, by rfl⟩ : syracuseStep 1732967 = 2599451) B2599451
theorem B1733019 : Blo 1731066 1733019 := bstep (se 1 (by rfl) ⟨1299764, by rfl⟩ : syracuseStep 1733019 = 2599529) B2599529
theorem B6574547 : Blo 1731066 6574547 := bstep (se 1 (by rfl) ⟨4930910, by rfl⟩ : syracuseStep 6574547 = 9861821) B9861821
theorem B3895865 : Blo 1731066 3895865 := bstep (se 2 (by rfl) ⟨1460949, by rfl⟩ : syracuseStep 3895865 = 2921899) B2921899
theorem B6574729 : Blo 1731066 6574729 := bstep (se 2 (by rfl) ⟨2465523, by rfl⟩ : syracuseStep 6574729 = 4931047) B4931047
theorem B16872151 : Blo 1731066 16872151 := bstep (se 1 (by rfl) ⟨12654113, by rfl⟩ : syracuseStep 16872151 = 25308227) B25308227
theorem B2192123 : Blo 1731066 2192123 := bstep (se 1 (by rfl) ⟨1644092, by rfl⟩ : syracuseStep 2192123 = 3288185) B3288185
theorem B5845823 : Blo 1731066 5845823 := bstep (se 1 (by rfl) ⟨4384367, by rfl⟩ : syracuseStep 5845823 = 8768735) B8768735
theorem B6575003 : Blo 1731066 6575003 := bstep (se 1 (by rfl) ⟨4931252, by rfl⟩ : syracuseStep 6575003 = 9862505) B9862505
theorem B2339911 : Blo 1731066 2339911 := bstep (se 1 (by rfl) ⟨1754933, by rfl⟩ : syracuseStep 2339911 = 3509867) B3509867
theorem B8320259 : Blo 1731066 8320259 := bstep (se 1 (by rfl) ⟨6240194, by rfl⟩ : syracuseStep 8320259 = 12480389) B12480389
theorem B3896585 : Blo 1731066 3896585 := bstep (se 2 (by rfl) ⟨1461219, by rfl⟩ : syracuseStep 3896585 = 2922439) B2922439
theorem B3896639 : Blo 1731066 3896639 := bstep (se 1 (by rfl) ⟨2922479, by rfl⟩ : syracuseStep 3896639 = 5844959) B5844959
theorem B28104043 : Blo 1731066 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B9868655 : Blo 1731066 9868655 := bstep (se 1 (by rfl) ⟨7401491, by rfl⟩ : syracuseStep 9868655 = 14802983) B14802983
theorem B3896747 : Blo 1731066 3896747 := bstep (se 1 (by rfl) ⟨2922560, by rfl⟩ : syracuseStep 3896747 = 5845121) B5845121
theorem B5846525 : Blo 1731066 5846525 := bstep (se 3 (by rfl) ⟨1096223, by rfl⟩ : syracuseStep 5846525 = 2192447) B2192447
theorem B6575687 : Blo 1731066 6575687 := bstep (se 1 (by rfl) ⟨4931765, by rfl⟩ : syracuseStep 6575687 = 9863531) B9863531
theorem B56178359 : Blo 1731066 56178359 := bstep (se 1 (by rfl) ⟨42133769, by rfl⟩ : syracuseStep 56178359 = 84267539) B84267539
theorem B11556587 : Blo 1731066 11556587 := bstep (se 1 (by rfl) ⟨8667440, by rfl⟩ : syracuseStep 11556587 = 17334881) B17334881
theorem B3897071 : Blo 1731066 3897071 := bstep (se 1 (by rfl) ⟨2922803, by rfl⟩ : syracuseStep 3897071 = 5845607) B5845607
theorem B7395067 : Blo 1731066 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B31586111 : Blo 1731066 31586111 := bstep (se 1 (by rfl) ⟨23689583, by rfl⟩ : syracuseStep 31586111 = 47379167) B47379167
theorem B2922311 : Blo 1731066 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B2774855 : Blo 1731066 2774855 := bstep (se 1 (by rfl) ⟨2081141, by rfl⟩ : syracuseStep 2774855 = 4162283) B4162283
theorem B3700559 : Blo 1731066 3700559 := bstep (se 1 (by rfl) ⟨2775419, by rfl⟩ : syracuseStep 3700559 = 5550839) B5550839
theorem B2922331 : Blo 1731066 2922331 := bstep (se 1 (by rfl) ⟨2191748, by rfl⟩ : syracuseStep 2922331 = 4383497) B4383497
theorem B3897287 : Blo 1731066 3897287 := bstep (se 1 (by rfl) ⟨2922965, by rfl⟩ : syracuseStep 3897287 = 5845931) B5845931
theorem B47388887 : Blo 1731066 47388887 := bstep (se 1 (by rfl) ⟨35541665, by rfl⟩ : syracuseStep 47388887 = 71083331) B71083331
theorem B3897575 : Blo 1731066 3897575 := bstep (se 1 (by rfl) ⟨2923181, by rfl⟩ : syracuseStep 3897575 = 5846363) B5846363
theorem B3897593 : Blo 1731066 3897593 := bstep (se 2 (by rfl) ⟨1461597, by rfl⟩ : syracuseStep 3897593 = 2923195) B2923195
theorem B15210767 : Blo 1731066 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B5847335 : Blo 1731066 5847335 := bstep (se 1 (by rfl) ⟨4385501, by rfl⟩ : syracuseStep 5847335 = 8771003) B8771003
theorem B3897647 : Blo 1731066 3897647 := bstep (se 1 (by rfl) ⟨2923235, by rfl⟩ : syracuseStep 3897647 = 5846471) B5846471
theorem B1948063 : Blo 1731066 1948063 := bstep (se 1 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 1948063 = 2922095) B2922095
theorem B1948135 : Blo 1731066 1948135 := bstep (se 1 (by rfl) ⟨1461101, by rfl⟩ : syracuseStep 1948135 = 2922203) B2922203
theorem B3897863 : Blo 1731066 3897863 := bstep (se 1 (by rfl) ⟨2923397, by rfl⟩ : syracuseStep 3897863 = 5846795) B5846795
theorem B6576659 : Blo 1731066 6576659 := bstep (se 1 (by rfl) ⟨4932494, by rfl⟩ : syracuseStep 6576659 = 9864989) B9864989
theorem B3898043 : Blo 1731066 3898043 := bstep (se 1 (by rfl) ⟨2923532, by rfl⟩ : syracuseStep 3898043 = 5847065) B5847065
theorem B8772299 : Blo 1731066 8772299 := bstep (se 1 (by rfl) ⟨6579224, by rfl⟩ : syracuseStep 8772299 = 13158449) B13158449
theorem B13327213 : Blo 1731066 13327213 := bstep (se 3 (by rfl) ⟨2498852, by rfl⟩ : syracuseStep 13327213 = 4997705) B4997705
theorem B10681247 : Blo 1731066 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B13147271 : Blo 1731066 13147271 := bstep (se 1 (by rfl) ⟨9860453, by rfl⟩ : syracuseStep 13147271 = 19720907) B19720907
theorem B15793375 : Blo 1731066 15793375 := bstep (se 1 (by rfl) ⟨11845031, by rfl⟩ : syracuseStep 15793375 = 23690063) B23690063
theorem B5848307 : Blo 1731066 5848307 := bstep (se 1 (by rfl) ⟨4386230, by rfl⟩ : syracuseStep 5848307 = 8772461) B8772461
theorem B1948999 : Blo 1731066 1948999 := bstep (se 1 (by rfl) ⟨1461749, by rfl⟩ : syracuseStep 1948999 = 2923499) B2923499
theorem B4382059 : Blo 1731066 4382059 := bstep (se 1 (by rfl) ⟨3286544, by rfl⟩ : syracuseStep 4382059 = 6573089) B6573089
theorem B54066707 : Blo 1731066 54066707 := bstep (se 1 (by rfl) ⟨40550030, by rfl⟩ : syracuseStep 54066707 = 81100061) B81100061
theorem B3898943 : Blo 1731066 3898943 := bstep (se 1 (by rfl) ⟨2924207, by rfl⟩ : syracuseStep 3898943 = 5848415) B5848415
theorem B6667883 : Blo 1731066 6667883 := bstep (se 1 (by rfl) ⟨5000912, by rfl⟩ : syracuseStep 6667883 = 10001825) B10001825
theorem B13147757 : Blo 1731066 13147757 := bstep (se 3 (by rfl) ⟨2465204, by rfl⟩ : syracuseStep 13147757 = 4930409) B4930409
theorem B4382495 : Blo 1731066 4382495 := bstep (se 1 (by rfl) ⟨3286871, by rfl⟩ : syracuseStep 4382495 = 6573743) B6573743
theorem B3899303 : Blo 1731066 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B2596841 : Blo 1731066 2596841 := bstep (se 2 (by rfl) ⟨973815, by rfl⟩ : syracuseStep 2596841 = 1947631) B1947631
theorem B4382707 : Blo 1731066 4382707 := bstep (se 1 (by rfl) ⟨3287030, by rfl⟩ : syracuseStep 4382707 = 6574061) B6574061
theorem B2596919 : Blo 1731066 2596919 := bstep (se 1 (by rfl) ⟨1947689, by rfl⟩ : syracuseStep 2596919 = 3895379) B3895379
theorem B379265165 : Blo 1731066 379265165 := bstep (se 3 (by rfl) ⟨71112218, by rfl⟩ : syracuseStep 379265165 = 142224437) B142224437
theorem B13336721 : Blo 1731066 13336721 := bstep (se 2 (by rfl) ⟨5001270, by rfl⟩ : syracuseStep 13336721 = 10002541) B10002541
theorem B2597039 : Blo 1731066 2597039 := bstep (se 1 (by rfl) ⟨1947779, by rfl⟩ : syracuseStep 2597039 = 3895559) B3895559
theorem B17785129 : Blo 1731066 17785129 := bstep (se 2 (by rfl) ⟨6669423, by rfl⟩ : syracuseStep 17785129 = 13338847) B13338847
theorem B4383031 : Blo 1731066 4383031 := bstep (se 1 (by rfl) ⟨3287273, by rfl⟩ : syracuseStep 4383031 = 6574547) B6574547
theorem B19235161 : Blo 1731066 19235161 := bstep (se 2 (by rfl) ⟨7213185, by rfl⟩ : syracuseStep 19235161 = 14426371) B14426371
theorem B2597243 : Blo 1731066 2597243 := bstep (se 1 (by rfl) ⟨1947932, by rfl⟩ : syracuseStep 2597243 = 3895865) B3895865
theorem B3801503 : Blo 1731066 3801503 := bstep (se 1 (by rfl) ⟨2851127, by rfl⟩ : syracuseStep 3801503 = 5702255) B5702255
theorem B2597417 : Blo 1731066 2597417 := bstep (se 2 (by rfl) ⟨974031, by rfl⟩ : syracuseStep 2597417 = 1948063) B1948063
theorem B4383335 : Blo 1731066 4383335 := bstep (se 1 (by rfl) ⟨3287501, by rfl⟩ : syracuseStep 4383335 = 6575003) B6575003
theorem B38503019 : Blo 1731066 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B2597513 : Blo 1731066 2597513 := bstep (se 2 (by rfl) ⟨974067, by rfl⟩ : syracuseStep 2597513 = 1948135) B1948135
theorem B2597723 : Blo 1731066 2597723 := bstep (se 1 (by rfl) ⟨1948292, by rfl⟩ : syracuseStep 2597723 = 3896585) B3896585
theorem B8766305 : Blo 1731066 8766305 := bstep (se 2 (by rfl) ⟨3287364, by rfl⟩ : syracuseStep 8766305 = 6574729) B6574729
theorem B11092859 : Blo 1731066 11092859 := bstep (se 1 (by rfl) ⟨8319644, by rfl⟩ : syracuseStep 11092859 = 16639289) B16639289
theorem B2597759 : Blo 1731066 2597759 := bstep (se 1 (by rfl) ⟨1948319, by rfl⟩ : syracuseStep 2597759 = 3896639) B3896639
theorem B6579103 : Blo 1731066 6579103 := bstep (se 1 (by rfl) ⟨4934327, by rfl⟩ : syracuseStep 6579103 = 9868655) B9868655
theorem B2597831 : Blo 1731066 2597831 := bstep (se 1 (by rfl) ⟨1948373, by rfl⟩ : syracuseStep 2597831 = 3896747) B3896747
theorem B4932551 : Blo 1731066 4932551 := bstep (se 1 (by rfl) ⟨3699413, by rfl⟩ : syracuseStep 4932551 = 7398827) B7398827
theorem B22496201 : Blo 1731066 22496201 := bstep (se 2 (by rfl) ⟨8436075, by rfl⟩ : syracuseStep 22496201 = 16872151) B16872151
theorem B4383791 : Blo 1731066 4383791 := bstep (se 1 (by rfl) ⟨3287843, by rfl⟩ : syracuseStep 4383791 = 6575687) B6575687
theorem B17769617 : Blo 1731066 17769617 := bstep (se 2 (by rfl) ⟨6663606, by rfl⟩ : syracuseStep 17769617 = 13327213) B13327213
theorem B2598047 : Blo 1731066 2598047 := bstep (se 1 (by rfl) ⟨1948535, by rfl⟩ : syracuseStep 2598047 = 3897071) B3897071
theorem B2467039 : Blo 1731066 2467039 := bstep (se 1 (by rfl) ⟨1850279, by rfl⟩ : syracuseStep 2467039 = 3700559) B3700559
theorem B2598191 : Blo 1731066 2598191 := bstep (se 1 (by rfl) ⟨1948643, by rfl⟩ : syracuseStep 2598191 = 3897287) B3897287
theorem B2598383 : Blo 1731066 2598383 := bstep (se 1 (by rfl) ⟨1948787, by rfl⟩ : syracuseStep 2598383 = 3897575) B3897575
theorem B2598395 : Blo 1731066 2598395 := bstep (se 1 (by rfl) ⟨1948796, by rfl⟩ : syracuseStep 2598395 = 3897593) B3897593
theorem B2598431 : Blo 1731066 2598431 := bstep (se 1 (by rfl) ⟨1948823, by rfl⟩ : syracuseStep 2598431 = 3897647) B3897647
theorem B3950171 : Blo 1731066 3950171 := bstep (se 1 (by rfl) ⟨2962628, by rfl⟩ : syracuseStep 3950171 = 5925257) B5925257
theorem B11101805 : Blo 1731066 11101805 := bstep (se 3 (by rfl) ⟨2081588, by rfl⟩ : syracuseStep 11101805 = 4163177) B4163177
theorem B2598575 : Blo 1731066 2598575 := bstep (se 1 (by rfl) ⟨1948931, by rfl⟩ : syracuseStep 2598575 = 3897863) B3897863
theorem B4384439 : Blo 1731066 4384439 := bstep (se 1 (by rfl) ⟨3288329, by rfl⟩ : syracuseStep 4384439 = 6576659) B6576659
theorem B2598665 : Blo 1731066 2598665 := bstep (se 2 (by rfl) ⟨974499, by rfl⟩ : syracuseStep 2598665 = 1948999) B1948999
theorem B2598695 : Blo 1731066 2598695 := bstep (se 1 (by rfl) ⟨1949021, by rfl⟩ : syracuseStep 2598695 = 3898043) B3898043
theorem B5842745 : Blo 1731066 5842745 := bstep (se 2 (by rfl) ⟨2191029, by rfl⟩ : syracuseStep 5842745 = 4382059) B4382059
theorem B37472057 : Blo 1731066 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B7399289 : Blo 1731066 7399289 := bstep (se 2 (by rfl) ⟨2774733, by rfl⟩ : syracuseStep 7399289 = 5549467) B5549467
theorem B7120831 : Blo 1731066 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B7399613 : Blo 1731066 7399613 := bstep (se 3 (by rfl) ⟨1387427, by rfl⟩ : syracuseStep 7399613 = 2774855) B2774855
theorem B2599295 : Blo 1731066 2599295 := bstep (se 1 (by rfl) ⟨1949471, by rfl⟩ : syracuseStep 2599295 = 3898943) B3898943
theorem B2599535 : Blo 1731066 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B5843609 : Blo 1731066 5843609 := bstep (se 2 (by rfl) ⟨2191353, by rfl⟩ : syracuseStep 5843609 = 4382707) B4382707
theorem B1731227 : Blo 1731066 1731227 := bstep (se 1 (by rfl) ⟨1298420, by rfl⟩ : syracuseStep 1731227 = 2596841) B2596841
theorem B4385441 : Blo 1731066 4385441 := bstep (se 2 (by rfl) ⟨1644540, by rfl⟩ : syracuseStep 4385441 = 3289081) B3289081
theorem B5704577 : Blo 1731066 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B1731695 : Blo 1731066 1731695 := bstep (se 1 (by rfl) ⟨1298771, by rfl⟩ : syracuseStep 1731695 = 2597543) B2597543
theorem B1731775 : Blo 1731066 1731775 := bstep (se 1 (by rfl) ⟨1298831, by rfl⟩ : syracuseStep 1731775 = 2597663) B2597663
theorem B1731791 : Blo 1731066 1731791 := bstep (se 1 (by rfl) ⟨1298843, by rfl⟩ : syracuseStep 1731791 = 2597687) B2597687
theorem B14789861 : Blo 1731066 14789861 := bstep (se 4 (by rfl) ⟨1386549, by rfl⟩ : syracuseStep 14789861 = 2773099) B2773099
theorem B1731911 : Blo 1731066 1731911 := bstep (se 1 (by rfl) ⟨1298933, by rfl⟩ : syracuseStep 1731911 = 2597867) B2597867
theorem B22187357 : Blo 1731066 22187357 := bstep (se 3 (by rfl) ⟨4160129, by rfl⟩ : syracuseStep 22187357 = 8320259) B8320259
theorem B40562045 : Blo 1731066 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B5549735 : Blo 1731066 5549735 := bstep (se 1 (by rfl) ⟨4162301, by rfl⟩ : syracuseStep 5549735 = 8324603) B8324603
theorem B7704391 : Blo 1731066 7704391 := bstep (se 1 (by rfl) ⟨5778293, by rfl⟩ : syracuseStep 7704391 = 11556587) B11556587
theorem B7401287 : Blo 1731066 7401287 := bstep (se 1 (by rfl) ⟨5550965, by rfl⟩ : syracuseStep 7401287 = 11101931) B11101931
theorem B16879481 : Blo 1731066 16879481 := bstep (se 2 (by rfl) ⟨6329805, by rfl⟩ : syracuseStep 16879481 = 12659611) B12659611
theorem B21057407 : Blo 1731066 21057407 := bstep (se 1 (by rfl) ⟨15793055, by rfl⟩ : syracuseStep 21057407 = 31586111) B31586111
theorem B1732639 : Blo 1731066 1732639 := bstep (se 1 (by rfl) ⟨1299479, by rfl⟩ : syracuseStep 1732639 = 2598959) B2598959
theorem B7401527 : Blo 1731066 7401527 := bstep (se 1 (by rfl) ⟨5551145, by rfl⟩ : syracuseStep 7401527 = 11102291) B11102291
theorem B31592591 : Blo 1731066 31592591 := bstep (se 1 (by rfl) ⟨23694443, by rfl⟩ : syracuseStep 31592591 = 47388887) B47388887
theorem B1732815 : Blo 1731066 1732815 := bstep (se 1 (by rfl) ⟨1299611, by rfl⟩ : syracuseStep 1732815 = 2599223) B2599223
theorem B21057833 : Blo 1731066 21057833 := bstep (se 2 (by rfl) ⟨7896687, by rfl⟩ : syracuseStep 21057833 = 15793375) B15793375
theorem B1732935 : Blo 1731066 1732935 := bstep (se 1 (by rfl) ⟨1299701, by rfl⟩ : syracuseStep 1732935 = 2599403) B2599403
theorem B5337467 : Blo 1731066 5337467 := bstep (se 1 (by rfl) ⟨4003100, by rfl⟩ : syracuseStep 5337467 = 8006201) B8006201
theorem B5845661 : Blo 1731066 5845661 := bstep (se 3 (by rfl) ⟨1096061, by rfl⟩ : syracuseStep 5845661 = 2192123) B2192123
theorem B5845769 : Blo 1731066 5845769 := bstep (se 2 (by rfl) ⟨2192163, by rfl⟩ : syracuseStep 5845769 = 4384327) B4384327
theorem B9860089 : Blo 1731066 9860089 := bstep (se 2 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 9860089 = 7395067) B7395067
theorem B4445255 : Blo 1731066 4445255 := bstep (se 1 (by rfl) ⟨3333941, by rfl⟩ : syracuseStep 4445255 = 6667883) B6667883
theorem B18723955 : Blo 1731066 18723955 := bstep (se 1 (by rfl) ⟨14042966, by rfl⟩ : syracuseStep 18723955 = 28085933) B28085933
theorem B3896441 : Blo 1731066 3896441 := bstep (se 2 (by rfl) ⟨1461165, by rfl⟩ : syracuseStep 3896441 = 2922331) B2922331
theorem B5846201 : Blo 1731066 5846201 := bstep (se 2 (by rfl) ⟨2192325, by rfl⟩ : syracuseStep 5846201 = 4384651) B4384651
theorem B2921663 : Blo 1731066 2921663 := bstep (se 1 (by rfl) ⟨2191247, by rfl⟩ : syracuseStep 2921663 = 4382495) B4382495
theorem B3897215 : Blo 1731066 3897215 := bstep (se 1 (by rfl) ⟨2922911, by rfl⟩ : syracuseStep 3897215 = 5845823) B5845823
theorem B168450191 : Blo 1731066 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B3897683 : Blo 1731066 3897683 := bstep (se 1 (by rfl) ⟨2923262, by rfl⟩ : syracuseStep 3897683 = 5846525) B5846525
theorem B37452239 : Blo 1731066 37452239 := bstep (se 1 (by rfl) ⟨28089179, by rfl⟩ : syracuseStep 37452239 = 56178359) B56178359
theorem B1948207 : Blo 1731066 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B5266015 : Blo 1731066 5266015 := bstep (se 1 (by rfl) ⟨3949511, by rfl⟩ : syracuseStep 5266015 = 7899023) B7899023
theorem B3119881 : Blo 1731066 3119881 := bstep (se 2 (by rfl) ⟨1169955, by rfl⟩ : syracuseStep 3119881 = 2339911) B2339911
theorem B3898223 : Blo 1731066 3898223 := bstep (se 1 (by rfl) ⟨2923667, by rfl⟩ : syracuseStep 3898223 = 5847335) B5847335
theorem B9362479 : Blo 1731066 9362479 := bstep (se 1 (by rfl) ⟨7021859, by rfl⟩ : syracuseStep 9362479 = 14043719) B14043719
theorem B5848199 : Blo 1731066 5848199 := bstep (se 1 (by rfl) ⟨4386149, by rfl⟩ : syracuseStep 5848199 = 8772299) B8772299
theorem B5848361 : Blo 1731066 5848361 := bstep (se 2 (by rfl) ⟨2193135, by rfl⟩ : syracuseStep 5848361 = 4386271) B4386271
theorem B8764847 : Blo 1731066 8764847 := bstep (se 1 (by rfl) ⟨6573635, by rfl⟩ : syracuseStep 8764847 = 13147271) B13147271
theorem B3898871 : Blo 1731066 3898871 := bstep (se 1 (by rfl) ⟨2924153, by rfl⟩ : syracuseStep 3898871 = 5848307) B5848307
theorem B40525321 : Blo 1731066 40525321 := bstep (se 2 (by rfl) ⟨15196995, by rfl⟩ : syracuseStep 40525321 = 30393991) B30393991
theorem B45620819 : Blo 1731066 45620819 := bstep (se 1 (by rfl) ⟨34215614, by rfl⟩ : syracuseStep 45620819 = 68431229) B68431229
theorem B36044471 : Blo 1731066 36044471 := bstep (se 1 (by rfl) ⟨27033353, by rfl⟩ : syracuseStep 36044471 = 54066707) B54066707
theorem B8765171 : Blo 1731066 8765171 := bstep (se 1 (by rfl) ⟨6573878, by rfl⟩ : syracuseStep 8765171 = 13147757) B13147757
theorem B2596859 : Blo 1731066 2596859 := bstep (se 1 (by rfl) ⟨1947644, by rfl⟩ : syracuseStep 2596859 = 3895289) B3895289
theorem B21061727 : Blo 1731066 21061727 := bstep (se 1 (by rfl) ⟨15796295, by rfl⟩ : syracuseStep 21061727 = 31592591) B31592591
theorem B2597609 : Blo 1731066 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B2597627 : Blo 1731066 2597627 := bstep (se 1 (by rfl) ⟨1948220, by rfl⟩ : syracuseStep 2597627 = 3896441) B3896441
theorem B11846411 : Blo 1731066 11846411 := bstep (se 1 (by rfl) ⟨8884808, by rfl⟩ : syracuseStep 11846411 = 17769617) B17769617
theorem B4932859 : Blo 1731066 4932859 := bstep (se 1 (by rfl) ⟨3699644, by rfl⟩ : syracuseStep 4932859 = 7399289) B7399289
theorem B2598143 : Blo 1731066 2598143 := bstep (se 1 (by rfl) ⟨1948607, by rfl⟩ : syracuseStep 2598143 = 3897215) B3897215
theorem B4933075 : Blo 1731066 4933075 := bstep (se 1 (by rfl) ⟨3699806, by rfl⟩ : syracuseStep 4933075 = 7399613) B7399613
theorem B2598455 : Blo 1731066 2598455 := bstep (se 1 (by rfl) ⟨1948841, by rfl⟩ : syracuseStep 2598455 = 3897683) B3897683
theorem B96118589 : Blo 1731066 96118589 := bstep (se 3 (by rfl) ⟨18022235, by rfl⟩ : syracuseStep 96118589 = 36044471) B36044471
theorem B2598815 : Blo 1731066 2598815 := bstep (se 1 (by rfl) ⟨1949111, by rfl⟩ : syracuseStep 2598815 = 3898223) B3898223
theorem B3803051 : Blo 1731066 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B5843231 : Blo 1731066 5843231 := bstep (se 1 (by rfl) ⟨4382423, by rfl⟩ : syracuseStep 5843231 = 8764847) B8764847
theorem B2599247 : Blo 1731066 2599247 := bstep (se 1 (by rfl) ⟨1949435, by rfl⟩ : syracuseStep 2599247 = 3898871) B3898871
theorem B5843447 : Blo 1731066 5843447 := bstep (se 1 (by rfl) ⟨4382585, by rfl⟩ : syracuseStep 5843447 = 8765171) B8765171
theorem B4934191 : Blo 1731066 4934191 := bstep (se 1 (by rfl) ⟨3700643, by rfl⟩ : syracuseStep 4934191 = 7401287) B7401287
theorem B1731239 : Blo 1731066 1731239 := bstep (se 1 (by rfl) ⟨1298429, by rfl⟩ : syracuseStep 1731239 = 2596859) B2596859
theorem B1731279 : Blo 1731066 1731279 := bstep (se 1 (by rfl) ⟨1298459, by rfl⟩ : syracuseStep 1731279 = 2596919) B2596919
theorem B4934351 : Blo 1731066 4934351 := bstep (se 1 (by rfl) ⟨3700763, by rfl⟩ : syracuseStep 4934351 = 7401527) B7401527
theorem B8891147 : Blo 1731066 8891147 := bstep (se 1 (by rfl) ⟨6668360, by rfl⟩ : syracuseStep 8891147 = 13336721) B13336721
theorem B1731359 : Blo 1731066 1731359 := bstep (se 1 (by rfl) ⟨1298519, by rfl⟩ : syracuseStep 1731359 = 2597039) B2597039
theorem B1731495 : Blo 1731066 1731495 := bstep (se 1 (by rfl) ⟨1298621, by rfl⟩ : syracuseStep 1731495 = 2597243) B2597243
theorem B3558311 : Blo 1731066 3558311 := bstep (se 1 (by rfl) ⟨2668733, by rfl⟩ : syracuseStep 3558311 = 5337467) B5337467
theorem B1731611 : Blo 1731066 1731611 := bstep (se 1 (by rfl) ⟨1298708, by rfl⟩ : syracuseStep 1731611 = 2597417) B2597417
theorem B25668679 : Blo 1731066 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B5844041 : Blo 1731066 5844041 := bstep (se 2 (by rfl) ⟨2191515, by rfl⟩ : syracuseStep 5844041 = 4383031) B4383031
theorem B1731675 : Blo 1731066 1731675 := bstep (se 1 (by rfl) ⟨1298756, by rfl⟩ : syracuseStep 1731675 = 2597513) B2597513
theorem B28085413 : Blo 1731066 28085413 := bstep (se 4 (by rfl) ⟨2633007, by rfl⟩ : syracuseStep 28085413 = 5266015) B5266015
theorem B1731815 : Blo 1731066 1731815 := bstep (se 1 (by rfl) ⟨1298861, by rfl⟩ : syracuseStep 1731815 = 2597723) B2597723
theorem B5844203 : Blo 1731066 5844203 := bstep (se 1 (by rfl) ⟨4383152, by rfl⟩ : syracuseStep 5844203 = 8766305) B8766305
theorem B1731839 : Blo 1731066 1731839 := bstep (se 1 (by rfl) ⟨1298879, by rfl⟩ : syracuseStep 1731839 = 2597759) B2597759
theorem B1731887 : Blo 1731066 1731887 := bstep (se 1 (by rfl) ⟨1298915, by rfl⟩ : syracuseStep 1731887 = 2597831) B2597831
theorem B3288367 : Blo 1731066 3288367 := bstep (se 1 (by rfl) ⟨2466275, by rfl⟩ : syracuseStep 3288367 = 4932551) B4932551
theorem B1732031 : Blo 1731066 1732031 := bstep (se 1 (by rfl) ⟨1299023, by rfl⟩ : syracuseStep 1732031 = 2598047) B2598047
theorem B1732127 : Blo 1731066 1732127 := bstep (se 1 (by rfl) ⟨1299095, by rfl⟩ : syracuseStep 1732127 = 2598191) B2598191
theorem B1732255 : Blo 1731066 1732255 := bstep (se 1 (by rfl) ⟨1299191, by rfl⟩ : syracuseStep 1732255 = 2598383) B2598383
theorem B1732263 : Blo 1731066 1732263 := bstep (se 1 (by rfl) ⟨1299197, by rfl⟩ : syracuseStep 1732263 = 2598395) B2598395
theorem B1732287 : Blo 1731066 1732287 := bstep (se 1 (by rfl) ⟨1299215, by rfl⟩ : syracuseStep 1732287 = 2598431) B2598431
theorem B2633447 : Blo 1731066 2633447 := bstep (se 1 (by rfl) ⟨1975085, by rfl⟩ : syracuseStep 2633447 = 3950171) B3950171
theorem B7401203 : Blo 1731066 7401203 := bstep (se 1 (by rfl) ⟨5550902, by rfl⟩ : syracuseStep 7401203 = 11101805) B11101805
theorem B10137341 : Blo 1731066 10137341 := bstep (se 3 (by rfl) ⟨1900751, by rfl⟩ : syracuseStep 10137341 = 3801503) B3801503
theorem B1732383 : Blo 1731066 1732383 := bstep (se 1 (by rfl) ⟨1299287, by rfl⟩ : syracuseStep 1732383 = 2598575) B2598575
theorem B1732443 : Blo 1731066 1732443 := bstep (se 1 (by rfl) ⟨1299332, by rfl⟩ : syracuseStep 1732443 = 2598665) B2598665
theorem B1732463 : Blo 1731066 1732463 := bstep (se 1 (by rfl) ⟨1299347, by rfl⟩ : syracuseStep 1732463 = 2598695) B2598695
theorem B3895163 : Blo 1731066 3895163 := bstep (se 1 (by rfl) ⟨2921372, by rfl⟩ : syracuseStep 3895163 = 5842745) B5842745
theorem B24981371 : Blo 1731066 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B112300127 : Blo 1731066 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B24965273 : Blo 1731066 24965273 := bstep (se 2 (by rfl) ⟨9361977, by rfl⟩ : syracuseStep 24965273 = 18723955) B18723955
theorem B1732863 : Blo 1731066 1732863 := bstep (se 1 (by rfl) ⟨1299647, by rfl⟩ : syracuseStep 1732863 = 2599295) B2599295
theorem B3289385 : Blo 1731066 3289385 := bstep (se 2 (by rfl) ⟨1233519, by rfl⟩ : syracuseStep 3289385 = 2467039) B2467039
theorem B1733023 : Blo 1731066 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B3895739 : Blo 1731066 3895739 := bstep (se 1 (by rfl) ⟨2921804, by rfl⟩ : syracuseStep 3895739 = 5843609) B5843609
theorem B14799293 : Blo 1731066 14799293 := bstep (se 3 (by rfl) ⟨2774867, by rfl⟩ : syracuseStep 14799293 = 5549735) B5549735
theorem B9859907 : Blo 1731066 9859907 := bstep (se 1 (by rfl) ⟨7394930, by rfl⟩ : syracuseStep 9859907 = 14789861) B14789861
theorem B14791571 : Blo 1731066 14791571 := bstep (se 1 (by rfl) ⟨11093678, by rfl⟩ : syracuseStep 14791571 = 22187357) B22187357
theorem B30413879 : Blo 1731066 30413879 := bstep (se 1 (by rfl) ⟨22810409, by rfl⟩ : syracuseStep 30413879 = 45620819) B45620819
theorem B11252987 : Blo 1731066 11252987 := bstep (se 1 (by rfl) ⟨8439740, by rfl⟩ : syracuseStep 11252987 = 16879481) B16879481
theorem B14038271 : Blo 1731066 14038271 := bstep (se 1 (by rfl) ⟨10528703, by rfl⟩ : syracuseStep 14038271 = 21057407) B21057407
theorem B252843443 : Blo 1731066 252843443 := bstep (se 1 (by rfl) ⟨189632582, by rfl⟩ : syracuseStep 252843443 = 379265165) B379265165
theorem B14038555 : Blo 1731066 14038555 := bstep (se 1 (by rfl) ⟨10528916, by rfl⟩ : syracuseStep 14038555 = 21057833) B21057833
theorem B23713505 : Blo 1731066 23713505 := bstep (se 2 (by rfl) ⟨8892564, by rfl⟩ : syracuseStep 23713505 = 17785129) B17785129
theorem B2922223 : Blo 1731066 2922223 := bstep (se 1 (by rfl) ⟨2191667, by rfl⟩ : syracuseStep 2922223 = 4383335) B4383335
theorem B3897107 : Blo 1731066 3897107 := bstep (se 1 (by rfl) ⟨2922830, by rfl⟩ : syracuseStep 3897107 = 5845661) B5845661
theorem B25646881 : Blo 1731066 25646881 := bstep (se 2 (by rfl) ⟨9617580, by rfl⟩ : syracuseStep 25646881 = 19235161) B19235161
theorem B3897179 : Blo 1731066 3897179 := bstep (se 1 (by rfl) ⟨2922884, by rfl⟩ : syracuseStep 3897179 = 5845769) B5845769
theorem B7395239 : Blo 1731066 7395239 := bstep (se 1 (by rfl) ⟨5546429, by rfl⟩ : syracuseStep 7395239 = 11092859) B11092859
theorem B14997467 : Blo 1731066 14997467 := bstep (se 1 (by rfl) ⟨11248100, by rfl⟩ : syracuseStep 14997467 = 22496201) B22496201
theorem B2922527 : Blo 1731066 2922527 := bstep (se 1 (by rfl) ⟨2191895, by rfl⟩ : syracuseStep 2922527 = 4383791) B4383791
theorem B2963503 : Blo 1731066 2963503 := bstep (se 1 (by rfl) ⟨2222627, by rfl⟩ : syracuseStep 2963503 = 4445255) B4445255
theorem B3897467 : Blo 1731066 3897467 := bstep (se 1 (by rfl) ⟨2923100, by rfl⟩ : syracuseStep 3897467 = 5846201) B5846201
theorem B1947775 : Blo 1731066 1947775 := bstep (se 1 (by rfl) ⟨1460831, by rfl⟩ : syracuseStep 1947775 = 2921663) B2921663
theorem B4159841 : Blo 1731066 4159841 := bstep (se 2 (by rfl) ⟨1559940, by rfl⟩ : syracuseStep 4159841 = 3119881) B3119881
theorem B2922959 : Blo 1731066 2922959 := bstep (se 1 (by rfl) ⟨2192219, by rfl⟩ : syracuseStep 2922959 = 4384439) B4384439
theorem B8772137 : Blo 1731066 8772137 := bstep (se 2 (by rfl) ⟨3289551, by rfl⟩ : syracuseStep 8772137 = 6579103) B6579103
theorem B13146785 : Blo 1731066 13146785 := bstep (se 2 (by rfl) ⟨4930044, by rfl⟩ : syracuseStep 13146785 = 9860089) B9860089
theorem B12483305 : Blo 1731066 12483305 := bstep (se 2 (by rfl) ⟨4681239, by rfl⟩ : syracuseStep 12483305 = 9362479) B9362479
theorem B24968159 : Blo 1731066 24968159 := bstep (se 1 (by rfl) ⟨18726119, by rfl⟩ : syracuseStep 24968159 = 37452239) B37452239
theorem B2923627 : Blo 1731066 2923627 := bstep (se 1 (by rfl) ⟨2192720, by rfl⟩ : syracuseStep 2923627 = 4385441) B4385441
theorem B54033761 : Blo 1731066 54033761 := bstep (se 2 (by rfl) ⟨20262660, by rfl⟩ : syracuseStep 54033761 = 40525321) B40525321
theorem B3898799 : Blo 1731066 3898799 := bstep (se 1 (by rfl) ⟨2924099, by rfl⟩ : syracuseStep 3898799 = 5848199) B5848199
theorem B3898907 : Blo 1731066 3898907 := bstep (se 1 (by rfl) ⟨2924180, by rfl⟩ : syracuseStep 3898907 = 5848361) B5848361
theorem B27041363 : Blo 1731066 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B10272521 : Blo 1731066 10272521 := bstep (se 2 (by rfl) ⟨3852195, by rfl⟩ : syracuseStep 10272521 = 7704391) B7704391
theorem B9494441 : Blo 1731066 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B74866751 : Blo 1731066 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B14041151 : Blo 1731066 14041151 := bstep (se 1 (by rfl) ⟨10530863, by rfl⟩ : syracuseStep 14041151 = 21061727) B21061727
theorem B2597033 : Blo 1731066 2597033 := bstep (se 2 (by rfl) ⟨973887, by rfl⟩ : syracuseStep 2597033 = 1947775) B1947775
theorem B2597159 : Blo 1731066 2597159 := bstep (se 1 (by rfl) ⟨1947869, by rfl⟩ : syracuseStep 2597159 = 3895739) B3895739
theorem B7897607 : Blo 1731066 7897607 := bstep (se 1 (by rfl) ⟨5923205, by rfl⟩ : syracuseStep 7897607 = 11846411) B11846411
theorem B20275919 : Blo 1731066 20275919 := bstep (se 1 (by rfl) ⟨15206939, by rfl⟩ : syracuseStep 20275919 = 30413879) B30413879
theorem B6578921 : Blo 1731066 6578921 := bstep (se 2 (by rfl) ⟨2467095, by rfl⟩ : syracuseStep 6578921 = 4934191) B4934191
theorem B11092909 : Blo 1731066 11092909 := bstep (se 3 (by rfl) ⟨2079920, by rfl⟩ : syracuseStep 11092909 = 4159841) B4159841
theorem B144090029 : Blo 1731066 144090029 := bstep (se 3 (by rfl) ⟨27016880, by rfl⟩ : syracuseStep 144090029 = 54033761) B54033761
theorem B2598071 : Blo 1731066 2598071 := bstep (se 1 (by rfl) ⟨1948553, by rfl⟩ : syracuseStep 2598071 = 3897107) B3897107
theorem B64079059 : Blo 1731066 64079059 := bstep (se 1 (by rfl) ⟨48059294, by rfl⟩ : syracuseStep 64079059 = 96118589) B96118589
theorem B2598119 : Blo 1731066 2598119 := bstep (se 1 (by rfl) ⟨1948589, by rfl⟩ : syracuseStep 2598119 = 3897179) B3897179
theorem B2598311 : Blo 1731066 2598311 := bstep (se 1 (by rfl) ⟨1948733, by rfl⟩ : syracuseStep 2598311 = 3897467) B3897467
theorem B37447217 : Blo 1731066 37447217 := bstep (se 2 (by rfl) ⟨14042706, by rfl⟩ : syracuseStep 37447217 = 28085413) B28085413
theorem B4384489 : Blo 1731066 4384489 := bstep (se 2 (by rfl) ⟨1644183, by rfl⟩ : syracuseStep 4384489 = 3288367) B3288367
theorem B37955317 : Blo 1731066 37955317 := bstep (se 5 (by rfl) ⟨1779155, by rfl⟩ : syracuseStep 37955317 = 3558311) B3558311
theorem B2599199 : Blo 1731066 2599199 := bstep (se 1 (by rfl) ⟨1949399, by rfl⟩ : syracuseStep 2599199 = 3898799) B3898799
theorem B2599271 : Blo 1731066 2599271 := bstep (se 1 (by rfl) ⟨1949453, by rfl⟩ : syracuseStep 2599271 = 3898907) B3898907
theorem B34195841 : Blo 1731066 34195841 := bstep (se 2 (by rfl) ⟨12823440, by rfl⟩ : syracuseStep 34195841 = 25646881) B25646881
theorem B1755631 : Blo 1731066 1755631 := bstep (se 1 (by rfl) ⟨1316723, by rfl⟩ : syracuseStep 1755631 = 2633447) B2633447
theorem B4934135 : Blo 1731066 4934135 := bstep (se 1 (by rfl) ⟨3700601, by rfl⟩ : syracuseStep 4934135 = 7401203) B7401203
theorem B3951337 : Blo 1731066 3951337 := bstep (se 2 (by rfl) ⟨1481751, by rfl⟩ : syracuseStep 3951337 = 2963503) B2963503
theorem B9866195 : Blo 1731066 9866195 := bstep (se 1 (by rfl) ⟨7399646, by rfl⟩ : syracuseStep 9866195 = 14799293) B14799293
theorem B1731739 : Blo 1731066 1731739 := bstep (se 1 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 1731739 = 2597609) B2597609
theorem B1731751 : Blo 1731066 1731751 := bstep (se 1 (by rfl) ⟨1298813, by rfl⟩ : syracuseStep 1731751 = 2597627) B2597627
theorem B6573271 : Blo 1731066 6573271 := bstep (se 1 (by rfl) ⟨4929953, by rfl⟩ : syracuseStep 6573271 = 9859907) B9859907
theorem B9358847 : Blo 1731066 9358847 := bstep (se 1 (by rfl) ⟨7019135, by rfl⟩ : syracuseStep 9358847 = 14038271) B14038271
theorem B1732095 : Blo 1731066 1732095 := bstep (se 1 (by rfl) ⟨1299071, by rfl⟩ : syracuseStep 1732095 = 2598143) B2598143
theorem B168562295 : Blo 1731066 168562295 := bstep (se 1 (by rfl) ⟨126421721, by rfl⟩ : syracuseStep 168562295 = 252843443) B252843443
theorem B1732303 : Blo 1731066 1732303 := bstep (se 1 (by rfl) ⟨1299227, by rfl⟩ : syracuseStep 1732303 = 2598455) B2598455
theorem B1732543 : Blo 1731066 1732543 := bstep (se 1 (by rfl) ⟨1299407, by rfl⟩ : syracuseStep 1732543 = 2598815) B2598815
theorem B9998311 : Blo 1731066 9998311 := bstep (se 1 (by rfl) ⟨7498733, by rfl⟩ : syracuseStep 9998311 = 14997467) B14997467
theorem B3895487 : Blo 1731066 3895487 := bstep (se 1 (by rfl) ⟨2921615, by rfl⟩ : syracuseStep 3895487 = 5843231) B5843231
theorem B1732831 : Blo 1731066 1732831 := bstep (se 1 (by rfl) ⟨1299623, by rfl⟩ : syracuseStep 1732831 = 2599247) B2599247
theorem B3895631 : Blo 1731066 3895631 := bstep (se 1 (by rfl) ⟨2921723, by rfl⟩ : syracuseStep 3895631 = 5843447) B5843447
theorem B3289567 : Blo 1731066 3289567 := bstep (se 1 (by rfl) ⟨2467175, by rfl⟩ : syracuseStep 3289567 = 4934351) B4934351
theorem B5927431 : Blo 1731066 5927431 := bstep (se 1 (by rfl) ⟨4445573, by rfl⟩ : syracuseStep 5927431 = 8891147) B8891147
theorem B3896027 : Blo 1731066 3896027 := bstep (se 1 (by rfl) ⟨2922020, by rfl⟩ : syracuseStep 3896027 = 5844041) B5844041
theorem B3896135 : Blo 1731066 3896135 := bstep (se 1 (by rfl) ⟨2922101, by rfl⟩ : syracuseStep 3896135 = 5844203) B5844203
theorem B3896297 : Blo 1731066 3896297 := bstep (se 2 (by rfl) ⟨1461111, by rfl⟩ : syracuseStep 3896297 = 2922223) B2922223
theorem B18027575 : Blo 1731066 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B6329627 : Blo 1731066 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B16643515 : Blo 1731066 16643515 := bstep (se 1 (by rfl) ⟨12482636, by rfl⟩ : syracuseStep 16643515 = 24965273) B24965273
theorem B2192923 : Blo 1731066 2192923 := bstep (se 1 (by rfl) ⟨1644692, by rfl⟩ : syracuseStep 2192923 = 3289385) B3289385
theorem B9861047 : Blo 1731066 9861047 := bstep (se 1 (by rfl) ⟨7395785, by rfl⟩ : syracuseStep 9861047 = 14791571) B14791571
theorem B7501991 : Blo 1731066 7501991 := bstep (se 1 (by rfl) ⟨5626493, by rfl⟩ : syracuseStep 7501991 = 11252987) B11252987
theorem B15809003 : Blo 1731066 15809003 := bstep (se 1 (by rfl) ⟨11856752, by rfl⟩ : syracuseStep 15809003 = 23713505) B23713505
theorem B4930159 : Blo 1731066 4930159 := bstep (se 1 (by rfl) ⟨3697619, by rfl⟩ : syracuseStep 4930159 = 7395239) B7395239
theorem B1948351 : Blo 1731066 1948351 := bstep (se 1 (by rfl) ⟨1461263, by rfl⟩ : syracuseStep 1948351 = 2922527) B2922527
theorem B34224905 : Blo 1731066 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B3898169 : Blo 1731066 3898169 := bstep (se 2 (by rfl) ⟨1461813, by rfl⟩ : syracuseStep 3898169 = 2923627) B2923627
theorem B1948639 : Blo 1731066 1948639 := bstep (se 1 (by rfl) ⟨1461479, by rfl⟩ : syracuseStep 1948639 = 2922959) B2922959
theorem B6577145 : Blo 1731066 6577145 := bstep (se 2 (by rfl) ⟨2466429, by rfl⟩ : syracuseStep 6577145 = 4932859) B4932859
theorem B5848091 : Blo 1731066 5848091 := bstep (se 1 (by rfl) ⟨4386068, by rfl⟩ : syracuseStep 5848091 = 8772137) B8772137
theorem B8764523 : Blo 1731066 8764523 := bstep (se 1 (by rfl) ⟨6573392, by rfl⟩ : syracuseStep 8764523 = 13146785) B13146785
theorem B8322203 : Blo 1731066 8322203 := bstep (se 1 (by rfl) ⟨6241652, by rfl⟩ : syracuseStep 8322203 = 12483305) B12483305
theorem B6577433 : Blo 1731066 6577433 := bstep (se 2 (by rfl) ⟨2466537, by rfl⟩ : syracuseStep 6577433 = 4933075) B4933075
theorem B16645439 : Blo 1731066 16645439 := bstep (se 1 (by rfl) ⟨12484079, by rfl⟩ : syracuseStep 16645439 = 24968159) B24968159
theorem B18718073 : Blo 1731066 18718073 := bstep (se 2 (by rfl) ⟨7019277, by rfl⟩ : syracuseStep 18718073 = 14038555) B14038555
theorem B10141469 : Blo 1731066 10141469 := bstep (se 3 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 10141469 = 3803051) B3803051
theorem B6758227 : Blo 1731066 6758227 := bstep (se 1 (by rfl) ⟨5068670, by rfl⟩ : syracuseStep 6758227 = 10137341) B10137341
theorem B6848347 : Blo 1731066 6848347 := bstep (se 1 (by rfl) ⟨5136260, by rfl⟩ : syracuseStep 6848347 = 10272521) B10272521
theorem B2596775 : Blo 1731066 2596775 := bstep (se 1 (by rfl) ⟨1947581, by rfl⟩ : syracuseStep 2596775 = 3895163) B3895163
theorem B16654247 : Blo 1731066 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B2596991 : Blo 1731066 2596991 := bstep (se 1 (by rfl) ⟨1947743, by rfl⟩ : syracuseStep 2596991 = 3895487) B3895487
theorem B2597087 : Blo 1731066 2597087 := bstep (se 1 (by rfl) ⟨1947815, by rfl⟩ : syracuseStep 2597087 = 3895631) B3895631
theorem B20005309 : Blo 1731066 20005309 := bstep (se 3 (by rfl) ⟨3750995, by rfl⟩ : syracuseStep 20005309 = 7501991) B7501991
theorem B13517279 : Blo 1731066 13517279 := bstep (se 1 (by rfl) ⟨10137959, by rfl⟩ : syracuseStep 13517279 = 20275919) B20275919
theorem B2597351 : Blo 1731066 2597351 := bstep (se 1 (by rfl) ⟨1948013, by rfl⟩ : syracuseStep 2597351 = 3896027) B3896027
theorem B2597423 : Blo 1731066 2597423 := bstep (se 1 (by rfl) ⟨1948067, by rfl⟩ : syracuseStep 2597423 = 3896135) B3896135
theorem B96060019 : Blo 1731066 96060019 := bstep (se 1 (by rfl) ⟨72045014, by rfl⟩ : syracuseStep 96060019 = 144090029) B144090029
theorem B2597531 : Blo 1731066 2597531 := bstep (se 1 (by rfl) ⟨1948148, by rfl⟩ : syracuseStep 2597531 = 3896297) B3896297
theorem B12018383 : Blo 1731066 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B4219751 : Blo 1731066 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B2597801 : Blo 1731066 2597801 := bstep (se 2 (by rfl) ⟨974175, by rfl⟩ : syracuseStep 2597801 = 1948351) B1948351
theorem B5268449 : Blo 1731066 5268449 := bstep (se 2 (by rfl) ⟨1975668, by rfl⟩ : syracuseStep 5268449 = 3951337) B3951337
theorem B2598185 : Blo 1731066 2598185 := bstep (se 2 (by rfl) ⟨974319, by rfl⟩ : syracuseStep 2598185 = 1948639) B1948639
theorem B22816603 : Blo 1731066 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B2598779 : Blo 1731066 2598779 := bstep (se 1 (by rfl) ⟨1949084, by rfl⟩ : syracuseStep 2598779 = 3898169) B3898169
theorem B4384763 : Blo 1731066 4384763 := bstep (se 1 (by rfl) ⟨3288572, by rfl⟩ : syracuseStep 4384763 = 6577145) B6577145
theorem B5843015 : Blo 1731066 5843015 := bstep (se 1 (by rfl) ⟨4382261, by rfl⟩ : syracuseStep 5843015 = 8764523) B8764523
theorem B5548135 : Blo 1731066 5548135 := bstep (se 1 (by rfl) ⟨4161101, by rfl⟩ : syracuseStep 5548135 = 8322203) B8322203
theorem B4384955 : Blo 1731066 4384955 := bstep (se 1 (by rfl) ⟨3288716, by rfl⟩ : syracuseStep 4384955 = 6577433) B6577433
theorem B12478715 : Blo 1731066 12478715 := bstep (se 1 (by rfl) ⟨9359036, by rfl⟩ : syracuseStep 12478715 = 18718073) B18718073
theorem B6760979 : Blo 1731066 6760979 := bstep (se 1 (by rfl) ⟨5070734, by rfl⟩ : syracuseStep 6760979 = 10141469) B10141469
theorem B1731183 : Blo 1731066 1731183 := bstep (se 1 (by rfl) ⟨1298387, by rfl⟩ : syracuseStep 1731183 = 2596775) B2596775
theorem B11102831 : Blo 1731066 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B13331081 : Blo 1731066 13331081 := bstep (se 2 (by rfl) ⟨4999155, by rfl⟩ : syracuseStep 13331081 = 9998311) B9998311
theorem B1731355 : Blo 1731066 1731355 := bstep (se 1 (by rfl) ⟨1298516, by rfl⟩ : syracuseStep 1731355 = 2597033) B2597033
theorem B1731439 : Blo 1731066 1731439 := bstep (se 1 (by rfl) ⟨1298579, by rfl⟩ : syracuseStep 1731439 = 2597159) B2597159
theorem B4385947 : Blo 1731066 4385947 := bstep (se 1 (by rfl) ⟨3289460, by rfl⟩ : syracuseStep 4385947 = 6578921) B6578921
theorem B4386089 : Blo 1731066 4386089 := bstep (se 2 (by rfl) ⟨1644783, by rfl⟩ : syracuseStep 4386089 = 3289567) B3289567
theorem B1732047 : Blo 1731066 1732047 := bstep (se 1 (by rfl) ⟨1299035, by rfl⟩ : syracuseStep 1732047 = 2598071) B2598071
theorem B6573545 : Blo 1731066 6573545 := bstep (se 2 (by rfl) ⟨2465079, by rfl⟩ : syracuseStep 6573545 = 4930159) B4930159
theorem B1732079 : Blo 1731066 1732079 := bstep (se 1 (by rfl) ⟨1299059, by rfl⟩ : syracuseStep 1732079 = 2598119) B2598119
theorem B1732207 : Blo 1731066 1732207 := bstep (se 1 (by rfl) ⟨1299155, by rfl⟩ : syracuseStep 1732207 = 2598311) B2598311
theorem B24964811 : Blo 1731066 24964811 := bstep (se 1 (by rfl) ⟨18723608, by rfl⟩ : syracuseStep 24964811 = 37447217) B37447217
theorem B14790545 : Blo 1731066 14790545 := bstep (se 2 (by rfl) ⟨5546454, by rfl⟩ : syracuseStep 14790545 = 11092909) B11092909
theorem B6574031 : Blo 1731066 6574031 := bstep (se 1 (by rfl) ⟨4930523, by rfl⟩ : syracuseStep 6574031 = 9861047) B9861047
theorem B1732799 : Blo 1731066 1732799 := bstep (se 1 (by rfl) ⟨1299599, by rfl⟩ : syracuseStep 1732799 = 2599199) B2599199
theorem B1732847 : Blo 1731066 1732847 := bstep (se 1 (by rfl) ⟨1299635, by rfl⟩ : syracuseStep 1732847 = 2599271) B2599271
theorem B85438745 : Blo 1731066 85438745 := bstep (se 2 (by rfl) ⟨32039529, by rfl⟩ : syracuseStep 85438745 = 64079059) B64079059
theorem B10539335 : Blo 1731066 10539335 := bstep (se 1 (by rfl) ⟨7904501, by rfl⟩ : syracuseStep 10539335 = 15809003) B15809003
theorem B3289423 : Blo 1731066 3289423 := bstep (se 1 (by rfl) ⟨2467067, by rfl⟩ : syracuseStep 3289423 = 4934135) B4934135
theorem B11096959 : Blo 1731066 11096959 := bstep (se 1 (by rfl) ⟨8322719, by rfl⟩ : syracuseStep 11096959 = 16645439) B16645439
theorem B5845985 : Blo 1731066 5845985 := bstep (se 2 (by rfl) ⟨2192244, by rfl⟩ : syracuseStep 5845985 = 4384489) B4384489
theorem B50607089 : Blo 1731066 50607089 := bstep (se 2 (by rfl) ⟨18977658, by rfl⟩ : syracuseStep 50607089 = 37955317) B37955317
theorem B6239231 : Blo 1731066 6239231 := bstep (se 1 (by rfl) ⟨4679423, by rfl⟩ : syracuseStep 6239231 = 9358847) B9358847
theorem B112374863 : Blo 1731066 112374863 := bstep (se 1 (by rfl) ⟨84281147, by rfl⟩ : syracuseStep 112374863 = 168562295) B168562295
theorem B9131129 : Blo 1731066 9131129 := bstep (se 2 (by rfl) ⟨3424173, by rfl⟩ : syracuseStep 9131129 = 6848347) B6848347
theorem B49911167 : Blo 1731066 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B9360767 : Blo 1731066 9360767 := bstep (se 1 (by rfl) ⟨7020575, by rfl⟩ : syracuseStep 9360767 = 14041151) B14041151
theorem B5265071 : Blo 1731066 5265071 := bstep (se 1 (by rfl) ⟨3948803, by rfl⟩ : syracuseStep 5265071 = 7897607) B7897607
theorem B2340841 : Blo 1731066 2340841 := bstep (se 2 (by rfl) ⟨877815, by rfl⟩ : syracuseStep 2340841 = 1755631) B1755631
theorem B7903241 : Blo 1731066 7903241 := bstep (se 2 (by rfl) ⟨2963715, by rfl⟩ : syracuseStep 7903241 = 5927431) B5927431
theorem B22797227 : Blo 1731066 22797227 := bstep (se 1 (by rfl) ⟨17097920, by rfl⟩ : syracuseStep 22797227 = 34195841) B34195841
theorem B8764361 : Blo 1731066 8764361 := bstep (se 2 (by rfl) ⟨3286635, by rfl⟩ : syracuseStep 8764361 = 6573271) B6573271
theorem B22191353 : Blo 1731066 22191353 := bstep (se 2 (by rfl) ⟨8321757, by rfl⟩ : syracuseStep 22191353 = 16643515) B16643515
theorem B6577463 : Blo 1731066 6577463 := bstep (se 1 (by rfl) ⟨4933097, by rfl⟩ : syracuseStep 6577463 = 9866195) B9866195
theorem B3898727 : Blo 1731066 3898727 := bstep (se 1 (by rfl) ⟨2924045, by rfl⟩ : syracuseStep 3898727 = 5848091) B5848091
theorem B2923897 : Blo 1731066 2923897 := bstep (se 2 (by rfl) ⟨1096461, by rfl⟩ : syracuseStep 2923897 = 2192923) B2192923
theorem B9010969 : Blo 1731066 9010969 := bstep (se 2 (by rfl) ⟨3379113, by rfl⟩ : syracuseStep 9010969 = 6758227) B6758227
theorem B7397513 : Blo 1731066 7397513 := bstep (se 2 (by rfl) ⟨2774067, by rfl⟩ : syracuseStep 7397513 = 5548135) B5548135
theorem B56959163 : Blo 1731066 56959163 := bstep (se 1 (by rfl) ⟨42719372, by rfl⟩ : syracuseStep 56959163 = 85438745) B85438745
theorem B9011519 : Blo 1731066 9011519 := bstep (se 1 (by rfl) ⟨6758639, by rfl⟩ : syracuseStep 9011519 = 13517279) B13517279
theorem B8012255 : Blo 1731066 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B192234005 : Blo 1731066 192234005 := bstep (se 6 (by rfl) ⟨4505484, by rfl⟩ : syracuseStep 192234005 = 9010969) B9010969
theorem B74916575 : Blo 1731066 74916575 := bstep (se 1 (by rfl) ⟨56187431, by rfl⟩ : syracuseStep 74916575 = 112374863) B112374863
theorem B6087419 : Blo 1731066 6087419 := bstep (se 1 (by rfl) ⟨4565564, by rfl⟩ : syracuseStep 6087419 = 9131129) B9131129
theorem B14795945 : Blo 1731066 14795945 := bstep (se 2 (by rfl) ⟨5548479, by rfl⟩ : syracuseStep 14795945 = 11096959) B11096959
theorem B5268827 : Blo 1731066 5268827 := bstep (se 1 (by rfl) ⟨3951620, by rfl⟩ : syracuseStep 5268827 = 7903241) B7903241
theorem B4507319 : Blo 1731066 4507319 := bstep (se 1 (by rfl) ⟨3380489, by rfl⟩ : syracuseStep 4507319 = 6760979) B6760979
theorem B15198151 : Blo 1731066 15198151 := bstep (se 1 (by rfl) ⟨11398613, by rfl⟩ : syracuseStep 15198151 = 22797227) B22797227
theorem B5842907 : Blo 1731066 5842907 := bstep (se 1 (by rfl) ⟨4382180, by rfl⟩ : syracuseStep 5842907 = 8764361) B8764361
theorem B4384975 : Blo 1731066 4384975 := bstep (se 1 (by rfl) ⟨3288731, by rfl⟩ : syracuseStep 4384975 = 6577463) B6577463
theorem B2599151 : Blo 1731066 2599151 := bstep (se 1 (by rfl) ⟨1949363, by rfl⟩ : syracuseStep 2599151 = 3898727) B3898727
theorem B106694981 : Blo 1731066 106694981 := bstep (se 4 (by rfl) ⟨10002654, by rfl⟩ : syracuseStep 106694981 = 20005309) B20005309
theorem B1731327 : Blo 1731066 1731327 := bstep (se 1 (by rfl) ⟨1298495, by rfl⟩ : syracuseStep 1731327 = 2596991) B2596991
theorem B1731391 : Blo 1731066 1731391 := bstep (se 1 (by rfl) ⟨1298543, by rfl⟩ : syracuseStep 1731391 = 2597087) B2597087
theorem B1731567 : Blo 1731066 1731567 := bstep (se 1 (by rfl) ⟨1298675, by rfl⟩ : syracuseStep 1731567 = 2597351) B2597351
theorem B1731615 : Blo 1731066 1731615 := bstep (se 1 (by rfl) ⟨1298711, by rfl⟩ : syracuseStep 1731615 = 2597423) B2597423
theorem B1731687 : Blo 1731066 1731687 := bstep (se 1 (by rfl) ⟨1298765, by rfl⟩ : syracuseStep 1731687 = 2597531) B2597531
theorem B4385897 : Blo 1731066 4385897 := bstep (se 2 (by rfl) ⟨1644711, by rfl⟩ : syracuseStep 4385897 = 3289423) B3289423
theorem B1731867 : Blo 1731066 1731867 := bstep (se 1 (by rfl) ⟨1298900, by rfl⟩ : syracuseStep 1731867 = 2597801) B2597801
theorem B33738059 : Blo 1731066 33738059 := bstep (se 1 (by rfl) ⟨25303544, by rfl⟩ : syracuseStep 33738059 = 50607089) B50607089
theorem B1732123 : Blo 1731066 1732123 := bstep (se 1 (by rfl) ⟨1299092, by rfl⟩ : syracuseStep 1732123 = 2598185) B2598185
theorem B3510047 : Blo 1731066 3510047 := bstep (se 1 (by rfl) ⟨2632535, by rfl⟩ : syracuseStep 3510047 = 5265071) B5265071
theorem B1732519 : Blo 1731066 1732519 := bstep (se 1 (by rfl) ⟨1299389, by rfl⟩ : syracuseStep 1732519 = 2598779) B2598779
theorem B3895343 : Blo 1731066 3895343 := bstep (se 1 (by rfl) ⟨2921507, by rfl⟩ : syracuseStep 3895343 = 5843015) B5843015
theorem B8319143 : Blo 1731066 8319143 := bstep (se 1 (by rfl) ⟨6239357, by rfl⟩ : syracuseStep 8319143 = 12478715) B12478715
theorem B35549549 : Blo 1731066 35549549 := bstep (se 3 (by rfl) ⟨6665540, by rfl⟩ : syracuseStep 35549549 = 13331081) B13331081
theorem B7401887 : Blo 1731066 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B11252669 : Blo 1731066 11252669 := bstep (se 3 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 11252669 = 4219751) B4219751
theorem B30422137 : Blo 1731066 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B16643207 : Blo 1731066 16643207 := bstep (se 1 (by rfl) ⟨12482405, by rfl⟩ : syracuseStep 16643207 = 24964811) B24964811
theorem B9860363 : Blo 1731066 9860363 := bstep (se 1 (by rfl) ⟨7395272, by rfl⟩ : syracuseStep 9860363 = 14790545) B14790545
theorem B7026223 : Blo 1731066 7026223 := bstep (se 1 (by rfl) ⟨5269667, by rfl⟩ : syracuseStep 7026223 = 10539335) B10539335
theorem B3897323 : Blo 1731066 3897323 := bstep (se 1 (by rfl) ⟨2922992, by rfl⟩ : syracuseStep 3897323 = 5845985) B5845985
theorem B4159487 : Blo 1731066 4159487 := bstep (se 1 (by rfl) ⟨3119615, by rfl⟩ : syracuseStep 4159487 = 6239231) B6239231
theorem B128080025 : Blo 1731066 128080025 := bstep (se 2 (by rfl) ⟨48030009, by rfl⟩ : syracuseStep 128080025 = 96060019) B96060019
theorem B33274111 : Blo 1731066 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B6240511 : Blo 1731066 6240511 := bstep (se 1 (by rfl) ⟨4680383, by rfl⟩ : syracuseStep 6240511 = 9360767) B9360767
theorem B2923175 : Blo 1731066 2923175 := bstep (se 1 (by rfl) ⟨2192381, by rfl⟩ : syracuseStep 2923175 = 4384763) B4384763
theorem B2923303 : Blo 1731066 2923303 := bstep (se 1 (by rfl) ⟨2192477, by rfl⟩ : syracuseStep 2923303 = 4384955) B4384955
theorem B5847929 : Blo 1731066 5847929 := bstep (se 2 (by rfl) ⟨2192973, by rfl⟩ : syracuseStep 5847929 = 4385947) B4385947
theorem B3898529 : Blo 1731066 3898529 := bstep (se 2 (by rfl) ⟨1461948, by rfl⟩ : syracuseStep 3898529 = 2923897) B2923897
theorem B14794235 : Blo 1731066 14794235 := bstep (se 1 (by rfl) ⟨11095676, by rfl⟩ : syracuseStep 14794235 = 22191353) B22191353
theorem B2924059 : Blo 1731066 2924059 := bstep (se 1 (by rfl) ⟨2193044, by rfl⟩ : syracuseStep 2924059 = 4386089) B4386089
theorem B4382363 : Blo 1731066 4382363 := bstep (se 1 (by rfl) ⟨3286772, by rfl⟩ : syracuseStep 4382363 = 6573545) B6573545
theorem B14049197 : Blo 1731066 14049197 := bstep (se 3 (by rfl) ⟨2634224, by rfl⟩ : syracuseStep 14049197 = 5268449) B5268449
theorem B4382687 : Blo 1731066 4382687 := bstep (se 1 (by rfl) ⟨3287015, by rfl⟩ : syracuseStep 4382687 = 6574031) B6574031
theorem B3121121 : Blo 1731066 3121121 := bstep (se 2 (by rfl) ⟨1170420, by rfl⟩ : syracuseStep 3121121 = 2340841) B2340841
theorem B2596895 : Blo 1731066 2596895 := bstep (se 1 (by rfl) ⟨1947671, by rfl⟩ : syracuseStep 2596895 = 3895343) B3895343
theorem B4931675 : Blo 1731066 4931675 := bstep (se 1 (by rfl) ⟨3698756, by rfl⟩ : syracuseStep 4931675 = 7397513) B7397513
theorem B23699699 : Blo 1731066 23699699 := bstep (se 1 (by rfl) ⟨17774774, by rfl⟩ : syracuseStep 23699699 = 35549549) B35549549
theorem B128156003 : Blo 1731066 128156003 := bstep (se 1 (by rfl) ⟨96117002, by rfl⟩ : syracuseStep 128156003 = 192234005) B192234005
theorem B22184381 : Blo 1731066 22184381 := bstep (se 3 (by rfl) ⟨4159571, by rfl⟩ : syracuseStep 22184381 = 8319143) B8319143
theorem B9863963 : Blo 1731066 9863963 := bstep (se 1 (by rfl) ⟨7397972, by rfl⟩ : syracuseStep 9863963 = 14795945) B14795945
theorem B14050205 : Blo 1731066 14050205 := bstep (se 3 (by rfl) ⟨2634413, by rfl⟩ : syracuseStep 14050205 = 5268827) B5268827
theorem B21366013 : Blo 1731066 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B2598215 : Blo 1731066 2598215 := bstep (se 1 (by rfl) ⟨1948661, by rfl⟩ : syracuseStep 2598215 = 3897323) B3897323
theorem B85386683 : Blo 1731066 85386683 := bstep (se 1 (by rfl) ⟨64040012, by rfl⟩ : syracuseStep 85386683 = 128080025) B128080025
theorem B2599019 : Blo 1731066 2599019 := bstep (se 1 (by rfl) ⟨1949264, by rfl⟩ : syracuseStep 2599019 = 3898529) B3898529
theorem B9366131 : Blo 1731066 9366131 := bstep (se 1 (by rfl) ⟨7024598, by rfl⟩ : syracuseStep 9366131 = 14049197) B14049197
theorem B37972775 : Blo 1731066 37972775 := bstep (se 1 (by rfl) ⟨28479581, by rfl⟩ : syracuseStep 37972775 = 56959163) B56959163
theorem B6007679 : Blo 1731066 6007679 := bstep (se 1 (by rfl) ⟨4505759, by rfl⟩ : syracuseStep 6007679 = 9011519) B9011519
theorem B4934591 : Blo 1731066 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B4058279 : Blo 1731066 4058279 := bstep (se 1 (by rfl) ⟨3043709, by rfl⟩ : syracuseStep 4058279 = 6087419) B6087419
theorem B11095471 : Blo 1731066 11095471 := bstep (se 1 (by rfl) ⟨8321603, by rfl⟩ : syracuseStep 11095471 = 16643207) B16643207
theorem B6573575 : Blo 1731066 6573575 := bstep (se 1 (by rfl) ⟨4930181, by rfl⟩ : syracuseStep 6573575 = 9860363) B9860363
theorem B3895271 : Blo 1731066 3895271 := bstep (se 1 (by rfl) ⟨2921453, by rfl⟩ : syracuseStep 3895271 = 5842907) B5842907
theorem B2772991 : Blo 1731066 2772991 := bstep (se 1 (by rfl) ⟨2079743, by rfl⟩ : syracuseStep 2772991 = 4159487) B4159487
theorem B1732767 : Blo 1731066 1732767 := bstep (se 1 (by rfl) ⟨1299575, by rfl⟩ : syracuseStep 1732767 = 2599151) B2599151
theorem B40562849 : Blo 1731066 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B9368297 : Blo 1731066 9368297 := bstep (se 2 (by rfl) ⟨3513111, by rfl⟩ : syracuseStep 9368297 = 7026223) B7026223
theorem B22492039 : Blo 1731066 22492039 := bstep (se 1 (by rfl) ⟨16869029, by rfl⟩ : syracuseStep 22492039 = 33738059) B33738059
theorem B2921575 : Blo 1731066 2921575 := bstep (se 1 (by rfl) ⟨2191181, by rfl⟩ : syracuseStep 2921575 = 4382363) B4382363
theorem B2340031 : Blo 1731066 2340031 := bstep (se 1 (by rfl) ⟨1755023, by rfl⟩ : syracuseStep 2340031 = 3510047) B3510047
theorem B20264201 : Blo 1731066 20264201 := bstep (se 2 (by rfl) ⟨7599075, by rfl⟩ : syracuseStep 20264201 = 15198151) B15198151
theorem B2921791 : Blo 1731066 2921791 := bstep (se 1 (by rfl) ⟨2191343, by rfl⟩ : syracuseStep 2921791 = 4382687) B4382687
theorem B5846633 : Blo 1731066 5846633 := bstep (se 2 (by rfl) ⟨2192487, by rfl⟩ : syracuseStep 5846633 = 4384975) B4384975
theorem B44365481 : Blo 1731066 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B8320681 : Blo 1731066 8320681 := bstep (se 2 (by rfl) ⟨3120255, by rfl⟩ : syracuseStep 8320681 = 6240511) B6240511
theorem B49944383 : Blo 1731066 49944383 := bstep (se 1 (by rfl) ⟨37458287, by rfl⟩ : syracuseStep 49944383 = 74916575) B74916575
theorem B3897737 : Blo 1731066 3897737 := bstep (se 2 (by rfl) ⟨1461651, by rfl⟩ : syracuseStep 3897737 = 2923303) B2923303
theorem B3004879 : Blo 1731066 3004879 := bstep (se 1 (by rfl) ⟨2253659, by rfl⟩ : syracuseStep 3004879 = 4507319) B4507319
theorem B71129987 : Blo 1731066 71129987 := bstep (se 1 (by rfl) ⟨53347490, by rfl⟩ : syracuseStep 71129987 = 106694981) B106694981
theorem B1948783 : Blo 1731066 1948783 := bstep (se 1 (by rfl) ⟨1461587, by rfl⟩ : syracuseStep 1948783 = 2923175) B2923175
theorem B3898619 : Blo 1731066 3898619 := bstep (se 1 (by rfl) ⟨2923964, by rfl⟩ : syracuseStep 3898619 = 5847929) B5847929
theorem B3898745 : Blo 1731066 3898745 := bstep (se 2 (by rfl) ⟨1462029, by rfl⟩ : syracuseStep 3898745 = 2924059) B2924059
theorem B2923931 : Blo 1731066 2923931 := bstep (se 1 (by rfl) ⟨2192948, by rfl⟩ : syracuseStep 2923931 = 4385897) B4385897
theorem B9862823 : Blo 1731066 9862823 := bstep (se 1 (by rfl) ⟨7397117, by rfl⟩ : syracuseStep 9862823 = 14794235) B14794235
theorem B30007117 : Blo 1731066 30007117 := bstep (se 3 (by rfl) ⟨5626334, by rfl⟩ : syracuseStep 30007117 = 11252669) B11252669
theorem B2080747 : Blo 1731066 2080747 := bstep (se 1 (by rfl) ⟨1560560, by rfl⟩ : syracuseStep 2080747 = 3121121) B3121121
theorem B27041899 : Blo 1731066 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B4006505 : Blo 1731066 4006505 := bstep (se 2 (by rfl) ⟨1502439, by rfl⟩ : syracuseStep 4006505 = 3004879) B3004879
theorem B13509467 : Blo 1731066 13509467 := bstep (se 1 (by rfl) ⟨10132100, by rfl⟩ : syracuseStep 13509467 = 20264201) B20264201
theorem B2598377 : Blo 1731066 2598377 := bstep (se 2 (by rfl) ⟨974391, by rfl⟩ : syracuseStep 2598377 = 1948783) B1948783
theorem B2598491 : Blo 1731066 2598491 := bstep (se 1 (by rfl) ⟨1948868, by rfl⟩ : syracuseStep 2598491 = 3897737) B3897737
theorem B6244087 : Blo 1731066 6244087 := bstep (se 1 (by rfl) ⟨4683065, by rfl⟩ : syracuseStep 6244087 = 9366131) B9366131
theorem B25315183 : Blo 1731066 25315183 := bstep (se 1 (by rfl) ⟨18986387, by rfl⟩ : syracuseStep 25315183 = 37972775) B37972775
theorem B2705519 : Blo 1731066 2705519 := bstep (se 1 (by rfl) ⟨2029139, by rfl⟩ : syracuseStep 2705519 = 4058279) B4058279
theorem B2599079 : Blo 1731066 2599079 := bstep (se 1 (by rfl) ⟨1949309, by rfl⟩ : syracuseStep 2599079 = 3898619) B3898619
theorem B11094241 : Blo 1731066 11094241 := bstep (se 2 (by rfl) ⟨4160340, by rfl⟩ : syracuseStep 11094241 = 8320681) B8320681
theorem B2599163 : Blo 1731066 2599163 := bstep (se 1 (by rfl) ⟨1949372, by rfl⟩ : syracuseStep 2599163 = 3898745) B3898745
theorem B3697321 : Blo 1731066 3697321 := bstep (se 2 (by rfl) ⟨1386495, by rfl⟩ : syracuseStep 3697321 = 2772991) B2772991
theorem B1731263 : Blo 1731066 1731263 := bstep (se 1 (by rfl) ⟨1298447, by rfl⟩ : syracuseStep 1731263 = 2596895) B2596895
theorem B3287783 : Blo 1731066 3287783 := bstep (se 1 (by rfl) ⟨2465837, by rfl⟩ : syracuseStep 3287783 = 4931675) B4931675
theorem B85437335 : Blo 1731066 85437335 := bstep (se 1 (by rfl) ⟨64078001, by rfl⟩ : syracuseStep 85437335 = 128156003) B128156003
theorem B14789587 : Blo 1731066 14789587 := bstep (se 1 (by rfl) ⟨11092190, by rfl⟩ : syracuseStep 14789587 = 22184381) B22184381
theorem B6245531 : Blo 1731066 6245531 := bstep (se 1 (by rfl) ⟨4684148, by rfl⟩ : syracuseStep 6245531 = 9368297) B9368297
theorem B9366803 : Blo 1731066 9366803 := bstep (se 1 (by rfl) ⟨7025102, by rfl⟩ : syracuseStep 9366803 = 14050205) B14050205
theorem B1732143 : Blo 1731066 1732143 := bstep (se 1 (by rfl) ⟨1299107, by rfl⟩ : syracuseStep 1732143 = 2598215) B2598215
theorem B29576987 : Blo 1731066 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B33296255 : Blo 1731066 33296255 := bstep (se 1 (by rfl) ⟨24972191, by rfl⟩ : syracuseStep 33296255 = 49944383) B49944383
theorem B1732679 : Blo 1731066 1732679 := bstep (se 1 (by rfl) ⟨1299509, by rfl⟩ : syracuseStep 1732679 = 2599019) B2599019
theorem B3895433 : Blo 1731066 3895433 := bstep (se 2 (by rfl) ⟨1460787, by rfl⟩ : syracuseStep 3895433 = 2921575) B2921575
theorem B28488017 : Blo 1731066 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B3895721 : Blo 1731066 3895721 := bstep (se 2 (by rfl) ⟨1460895, by rfl⟩ : syracuseStep 3895721 = 2921791) B2921791
theorem B47419991 : Blo 1731066 47419991 := bstep (se 1 (by rfl) ⟨35564993, by rfl⟩ : syracuseStep 47419991 = 71129987) B71129987
theorem B3289727 : Blo 1731066 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B6575215 : Blo 1731066 6575215 := bstep (se 1 (by rfl) ⟨4931411, by rfl⟩ : syracuseStep 6575215 = 9862823) B9862823
theorem B11097317 : Blo 1731066 11097317 := bstep (se 4 (by rfl) ⟨1040373, by rfl⟩ : syracuseStep 11097317 = 2080747) B2080747
theorem B15799799 : Blo 1731066 15799799 := bstep (se 1 (by rfl) ⟨11849849, by rfl⟩ : syracuseStep 15799799 = 23699699) B23699699
theorem B6575975 : Blo 1731066 6575975 := bstep (se 1 (by rfl) ⟨4931981, by rfl⟩ : syracuseStep 6575975 = 9863963) B9863963
theorem B56924455 : Blo 1731066 56924455 := bstep (se 1 (by rfl) ⟨42693341, by rfl⟩ : syracuseStep 56924455 = 85386683) B85386683
theorem B3897755 : Blo 1731066 3897755 := bstep (se 1 (by rfl) ⟨2923316, by rfl⟩ : syracuseStep 3897755 = 5846633) B5846633
theorem B29989385 : Blo 1731066 29989385 := bstep (se 2 (by rfl) ⟨11246019, by rfl⟩ : syracuseStep 29989385 = 22492039) B22492039
theorem B3120041 : Blo 1731066 3120041 := bstep (se 2 (by rfl) ⟨1170015, by rfl⟩ : syracuseStep 3120041 = 2340031) B2340031
theorem B160037957 : Blo 1731066 160037957 := bstep (se 4 (by rfl) ⟨15003558, by rfl⟩ : syracuseStep 160037957 = 30007117) B30007117
theorem B14793961 : Blo 1731066 14793961 := bstep (se 2 (by rfl) ⟨5547735, by rfl⟩ : syracuseStep 14793961 = 11095471) B11095471
theorem B4005119 : Blo 1731066 4005119 := bstep (se 1 (by rfl) ⟨3003839, by rfl⟩ : syracuseStep 4005119 = 6007679) B6007679
theorem B1949287 : Blo 1731066 1949287 := bstep (se 1 (by rfl) ⟨1461965, by rfl⟩ : syracuseStep 1949287 = 2923931) B2923931
theorem B4382383 : Blo 1731066 4382383 := bstep (se 1 (by rfl) ⟨3286787, by rfl⟩ : syracuseStep 4382383 = 6573575) B6573575
theorem B2596847 : Blo 1731066 2596847 := bstep (se 1 (by rfl) ⟨1947635, by rfl⟩ : syracuseStep 2596847 = 3895271) B3895271
theorem B2596955 : Blo 1731066 2596955 := bstep (se 1 (by rfl) ⟨1947716, by rfl⟩ : syracuseStep 2596955 = 3895433) B3895433
theorem B2597147 : Blo 1731066 2597147 := bstep (se 1 (by rfl) ⟨1947860, by rfl⟩ : syracuseStep 2597147 = 3895721) B3895721
theorem B75899273 : Blo 1731066 75899273 := bstep (se 2 (by rfl) ⟨28462227, by rfl⟩ : syracuseStep 75899273 = 56924455) B56924455
theorem B31613327 : Blo 1731066 31613327 := bstep (se 1 (by rfl) ⟨23709995, by rfl⟩ : syracuseStep 31613327 = 47419991) B47419991
theorem B2671003 : Blo 1731066 2671003 := bstep (se 1 (by rfl) ⟨2003252, by rfl⟩ : syracuseStep 2671003 = 4006505) B4006505
theorem B7398211 : Blo 1731066 7398211 := bstep (se 1 (by rfl) ⟨5548658, by rfl⟩ : syracuseStep 7398211 = 11097317) B11097317
theorem B4383983 : Blo 1731066 4383983 := bstep (se 1 (by rfl) ⟨3287987, by rfl⟩ : syracuseStep 4383983 = 6575975) B6575975
theorem B19719449 : Blo 1731066 19719449 := bstep (se 2 (by rfl) ⟨7394793, by rfl⟩ : syracuseStep 19719449 = 14789587) B14789587
theorem B42132797 : Blo 1731066 42132797 := bstep (se 3 (by rfl) ⟨7899899, by rfl⟩ : syracuseStep 42132797 = 15799799) B15799799
theorem B8766953 : Blo 1731066 8766953 := bstep (se 2 (by rfl) ⟨3287607, by rfl⟩ : syracuseStep 8766953 = 6575215) B6575215
theorem B2598503 : Blo 1731066 2598503 := bstep (se 1 (by rfl) ⟨1948877, by rfl⟩ : syracuseStep 2598503 = 3897755) B3897755
theorem B135014309 : Blo 1731066 135014309 := bstep (se 4 (by rfl) ⟨12657591, by rfl⟩ : syracuseStep 135014309 = 25315183) B25315183
theorem B4163687 : Blo 1731066 4163687 := bstep (se 1 (by rfl) ⟨3122765, by rfl⟩ : syracuseStep 4163687 = 6245531) B6245531
theorem B2599049 : Blo 1731066 2599049 := bstep (se 2 (by rfl) ⟨974643, by rfl⟩ : syracuseStep 2599049 = 1949287) B1949287
theorem B6244535 : Blo 1731066 6244535 := bstep (se 1 (by rfl) ⟨4683401, by rfl⟩ : syracuseStep 6244535 = 9366803) B9366803
theorem B5843177 : Blo 1731066 5843177 := bstep (se 2 (by rfl) ⟨2191191, by rfl⟩ : syracuseStep 5843177 = 4382383) B4382383
theorem B8325449 : Blo 1731066 8325449 := bstep (se 2 (by rfl) ⟨3122043, by rfl⟩ : syracuseStep 8325449 = 6244087) B6244087
theorem B1731231 : Blo 1731066 1731231 := bstep (se 1 (by rfl) ⟨1298423, by rfl⟩ : syracuseStep 1731231 = 2596847) B2596847
theorem B36055865 : Blo 1731066 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B18992011 : Blo 1731066 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B9006311 : Blo 1731066 9006311 := bstep (se 1 (by rfl) ⟨6754733, by rfl⟩ : syracuseStep 9006311 = 13509467) B13509467
theorem B1732251 : Blo 1731066 1732251 := bstep (se 1 (by rfl) ⟨1299188, by rfl⟩ : syracuseStep 1732251 = 2598377) B2598377
theorem B1732327 : Blo 1731066 1732327 := bstep (se 1 (by rfl) ⟨1299245, by rfl⟩ : syracuseStep 1732327 = 2598491) B2598491
theorem B1732719 : Blo 1731066 1732719 := bstep (se 1 (by rfl) ⟨1299539, by rfl⟩ : syracuseStep 1732719 = 2599079) B2599079
theorem B1732775 : Blo 1731066 1732775 := bstep (se 1 (by rfl) ⟨1299581, by rfl⟩ : syracuseStep 1732775 = 2599163) B2599163
theorem B19992923 : Blo 1731066 19992923 := bstep (se 1 (by rfl) ⟨14994692, by rfl⟩ : syracuseStep 19992923 = 29989385) B29989385
theorem B2191855 : Blo 1731066 2191855 := bstep (se 1 (by rfl) ⟨1643891, by rfl⟩ : syracuseStep 2191855 = 3287783) B3287783
theorem B22197503 : Blo 1731066 22197503 := bstep (se 1 (by rfl) ⟨16648127, by rfl⟩ : syracuseStep 22197503 = 33296255) B33296255
theorem B426767885 : Blo 1731066 426767885 := bstep (se 3 (by rfl) ⟨80018978, by rfl⟩ : syracuseStep 426767885 = 160037957) B160037957
theorem B7214717 : Blo 1731066 7214717 := bstep (se 3 (by rfl) ⟨1352759, by rfl⟩ : syracuseStep 7214717 = 2705519) B2705519
theorem B14792321 : Blo 1731066 14792321 := bstep (se 2 (by rfl) ⟨5547120, by rfl⟩ : syracuseStep 14792321 = 11094241) B11094241
theorem B2193151 : Blo 1731066 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B4929761 : Blo 1731066 4929761 := bstep (se 2 (by rfl) ⟨1848660, by rfl⟩ : syracuseStep 4929761 = 3697321) B3697321
theorem B19725281 : Blo 1731066 19725281 := bstep (se 2 (by rfl) ⟨7396980, by rfl⟩ : syracuseStep 19725281 = 14793961) B14793961
theorem B56958223 : Blo 1731066 56958223 := bstep (se 1 (by rfl) ⟨42718667, by rfl⟩ : syracuseStep 56958223 = 85437335) B85437335
theorem B2080027 : Blo 1731066 2080027 := bstep (se 1 (by rfl) ⟨1560020, by rfl⟩ : syracuseStep 2080027 = 3120041) B3120041
theorem B2670079 : Blo 1731066 2670079 := bstep (se 1 (by rfl) ⟨2002559, by rfl⟩ : syracuseStep 2670079 = 4005119) B4005119
theorem B19717991 : Blo 1731066 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B13328615 : Blo 1731066 13328615 := bstep (se 1 (by rfl) ⟨9996461, by rfl⟩ : syracuseStep 13328615 = 19992923) B19992923
theorem B9864281 : Blo 1731066 9864281 := bstep (se 2 (by rfl) ⟨3699105, by rfl⟩ : syracuseStep 9864281 = 7398211) B7398211
theorem B25322681 : Blo 1731066 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B4163023 : Blo 1731066 4163023 := bstep (se 1 (by rfl) ⟨3122267, by rfl⟩ : syracuseStep 4163023 = 6244535) B6244535
theorem B3286507 : Blo 1731066 3286507 := bstep (se 1 (by rfl) ⟨2464880, by rfl⟩ : syracuseStep 3286507 = 4929761) B4929761
theorem B24037243 : Blo 1731066 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B13150187 : Blo 1731066 13150187 := bstep (se 1 (by rfl) ⟨9862640, by rfl⟩ : syracuseStep 13150187 = 19725281) B19725281
theorem B1731303 : Blo 1731066 1731303 := bstep (se 1 (by rfl) ⟨1298477, by rfl⟩ : syracuseStep 1731303 = 2596955) B2596955
theorem B1731431 : Blo 1731066 1731431 := bstep (se 1 (by rfl) ⟨1298573, by rfl⟩ : syracuseStep 1731431 = 2597147) B2597147
theorem B14798335 : Blo 1731066 14798335 := bstep (se 1 (by rfl) ⟨11098751, by rfl⟩ : syracuseStep 14798335 = 22197503) B22197503
theorem B5844635 : Blo 1731066 5844635 := bstep (se 1 (by rfl) ⟨4383476, by rfl⟩ : syracuseStep 5844635 = 8766953) B8766953
theorem B284511923 : Blo 1731066 284511923 := bstep (se 1 (by rfl) ⟨213383942, by rfl⟩ : syracuseStep 284511923 = 426767885) B426767885
theorem B1732335 : Blo 1731066 1732335 := bstep (se 1 (by rfl) ⟨1299251, by rfl⟩ : syracuseStep 1732335 = 2598503) B2598503
theorem B90009539 : Blo 1731066 90009539 := bstep (se 1 (by rfl) ⟨67507154, by rfl⟩ : syracuseStep 90009539 = 135014309) B135014309
theorem B1732699 : Blo 1731066 1732699 := bstep (se 1 (by rfl) ⟨1299524, by rfl⟩ : syracuseStep 1732699 = 2599049) B2599049
theorem B3895451 : Blo 1731066 3895451 := bstep (se 1 (by rfl) ⟨2921588, by rfl⟩ : syracuseStep 3895451 = 5843177) B5843177
theorem B5550299 : Blo 1731066 5550299 := bstep (se 1 (by rfl) ⟨4162724, by rfl⟩ : syracuseStep 5550299 = 8325449) B8325449
theorem B19239245 : Blo 1731066 19239245 := bstep (se 3 (by rfl) ⟨3607358, by rfl⟩ : syracuseStep 19239245 = 7214717) B7214717
theorem B75944297 : Blo 1731066 75944297 := bstep (se 2 (by rfl) ⟨28479111, by rfl⟩ : syracuseStep 75944297 = 56958223) B56958223
theorem B2773369 : Blo 1731066 2773369 := bstep (se 2 (by rfl) ⟨1040013, by rfl⟩ : syracuseStep 2773369 = 2080027) B2080027
theorem B3560105 : Blo 1731066 3560105 := bstep (se 2 (by rfl) ⟨1335039, by rfl⟩ : syracuseStep 3560105 = 2670079) B2670079
theorem B13145327 : Blo 1731066 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B21075551 : Blo 1731066 21075551 := bstep (se 1 (by rfl) ⟨15806663, by rfl⟩ : syracuseStep 21075551 = 31613327) B31613327
theorem B3561337 : Blo 1731066 3561337 := bstep (se 2 (by rfl) ⟨1335501, by rfl⟩ : syracuseStep 3561337 = 2671003) B2671003
theorem B2922473 : Blo 1731066 2922473 := bstep (se 2 (by rfl) ⟨1095927, by rfl⟩ : syracuseStep 2922473 = 2191855) B2191855
theorem B2922655 : Blo 1731066 2922655 := bstep (se 1 (by rfl) ⟨2191991, by rfl⟩ : syracuseStep 2922655 = 4383983) B4383983
theorem B13146299 : Blo 1731066 13146299 := bstep (se 1 (by rfl) ⟨9859724, by rfl⟩ : syracuseStep 13146299 = 19719449) B19719449
theorem B28088531 : Blo 1731066 28088531 := bstep (se 1 (by rfl) ⟨21066398, by rfl⟩ : syracuseStep 28088531 = 42132797) B42132797
theorem B202398061 : Blo 1731066 202398061 := bstep (se 3 (by rfl) ⟨37949636, by rfl⟩ : syracuseStep 202398061 = 75899273) B75899273
theorem B9861547 : Blo 1731066 9861547 := bstep (se 1 (by rfl) ⟨7396160, by rfl⟩ : syracuseStep 9861547 = 14792321) B14792321
theorem B2775791 : Blo 1731066 2775791 := bstep (se 1 (by rfl) ⟨2081843, by rfl⟩ : syracuseStep 2775791 = 4163687) B4163687
theorem B6004207 : Blo 1731066 6004207 := bstep (se 1 (by rfl) ⟨4503155, by rfl⟩ : syracuseStep 6004207 = 9006311) B9006311
theorem B2924201 : Blo 1731066 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B2596967 : Blo 1731066 2596967 := bstep (se 1 (by rfl) ⟨1947725, by rfl⟩ : syracuseStep 2596967 = 3895451) B3895451
theorem B13148729 : Blo 1731066 13148729 := bstep (se 2 (by rfl) ⟨4930773, by rfl⟩ : syracuseStep 13148729 = 9861547) B9861547
theorem B14050367 : Blo 1731066 14050367 := bstep (se 1 (by rfl) ⟨10537775, by rfl⟩ : syracuseStep 14050367 = 21075551) B21075551
theorem B8766791 : Blo 1731066 8766791 := bstep (se 1 (by rfl) ⟨6575093, by rfl⟩ : syracuseStep 8766791 = 13150187) B13150187
theorem B128198629 : Blo 1731066 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B8005609 : Blo 1731066 8005609 := bstep (se 2 (by rfl) ⟨3002103, by rfl⟩ : syracuseStep 8005609 = 6004207) B6004207
theorem B50629531 : Blo 1731066 50629531 := bstep (se 1 (by rfl) ⟨37972148, by rfl⟩ : syracuseStep 50629531 = 75944297) B75944297
theorem B269864081 : Blo 1731066 269864081 := bstep (se 2 (by rfl) ⟨101199030, by rfl⟩ : syracuseStep 269864081 = 202398061) B202398061
theorem B3697825 : Blo 1731066 3697825 := bstep (se 2 (by rfl) ⟨1386684, by rfl⟩ : syracuseStep 3697825 = 2773369) B2773369
theorem B5550697 : Blo 1731066 5550697 := bstep (se 2 (by rfl) ⟨2081511, by rfl⟩ : syracuseStep 5550697 = 4163023) B4163023
theorem B18993797 : Blo 1731066 18993797 := bstep (se 4 (by rfl) ⟨1780668, by rfl⟩ : syracuseStep 18993797 = 3561337) B3561337
theorem B19731113 : Blo 1731066 19731113 := bstep (se 2 (by rfl) ⟨7399167, by rfl⟩ : syracuseStep 19731113 = 14798335) B14798335
theorem B3896423 : Blo 1731066 3896423 := bstep (se 1 (by rfl) ⟨2922317, by rfl⟩ : syracuseStep 3896423 = 5844635) B5844635
theorem B189674615 : Blo 1731066 189674615 := bstep (se 1 (by rfl) ⟨142255961, by rfl⟩ : syracuseStep 189674615 = 284511923) B284511923
theorem B3700199 : Blo 1731066 3700199 := bstep (se 1 (by rfl) ⟨2775149, by rfl⟩ : syracuseStep 3700199 = 5550299) B5550299
theorem B8885743 : Blo 1731066 8885743 := bstep (se 1 (by rfl) ⟨6664307, by rfl⟩ : syracuseStep 8885743 = 13328615) B13328615
theorem B3896873 : Blo 1731066 3896873 := bstep (se 2 (by rfl) ⟨1461327, by rfl⟩ : syracuseStep 3896873 = 2922655) B2922655
theorem B12826163 : Blo 1731066 12826163 := bstep (se 1 (by rfl) ⟨9619622, by rfl⟩ : syracuseStep 12826163 = 19239245) B19239245
theorem B2373403 : Blo 1731066 2373403 := bstep (se 1 (by rfl) ⟨1780052, by rfl⟩ : syracuseStep 2373403 = 3560105) B3560105
theorem B6576187 : Blo 1731066 6576187 := bstep (se 1 (by rfl) ⟨4932140, by rfl⟩ : syracuseStep 6576187 = 9864281) B9864281
theorem B16881787 : Blo 1731066 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B8763551 : Blo 1731066 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B1948315 : Blo 1731066 1948315 := bstep (se 1 (by rfl) ⟨1461236, by rfl⟩ : syracuseStep 1948315 = 2922473) B2922473
theorem B8764199 : Blo 1731066 8764199 := bstep (se 1 (by rfl) ⟨6573149, by rfl⟩ : syracuseStep 8764199 = 13146299) B13146299
theorem B18725687 : Blo 1731066 18725687 := bstep (se 1 (by rfl) ⟨14044265, by rfl⟩ : syracuseStep 18725687 = 28088531) B28088531
theorem B1850527 : Blo 1731066 1850527 := bstep (se 1 (by rfl) ⟨1387895, by rfl⟩ : syracuseStep 1850527 = 2775791) B2775791
theorem B4382009 : Blo 1731066 4382009 := bstep (se 2 (by rfl) ⟨1643253, by rfl⟩ : syracuseStep 4382009 = 3286507) B3286507
theorem B1949467 : Blo 1731066 1949467 := bstep (se 1 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 1949467 = 2924201) B2924201
theorem B60006359 : Blo 1731066 60006359 := bstep (se 1 (by rfl) ⟨45004769, by rfl⟩ : syracuseStep 60006359 = 90009539) B90009539
theorem B8765819 : Blo 1731066 8765819 := bstep (se 1 (by rfl) ⟨6574364, by rfl⟩ : syracuseStep 8765819 = 13148729) B13148729
theorem B2597615 : Blo 1731066 2597615 := bstep (se 1 (by rfl) ⟨1948211, by rfl⟩ : syracuseStep 2597615 = 3896423) B3896423
theorem B2597753 : Blo 1731066 2597753 := bstep (se 2 (by rfl) ⟨974157, by rfl⟩ : syracuseStep 2597753 = 1948315) B1948315
theorem B2597915 : Blo 1731066 2597915 := bstep (se 1 (by rfl) ⟨1948436, by rfl⟩ : syracuseStep 2597915 = 3896873) B3896873
theorem B5842367 : Blo 1731066 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B2467369 : Blo 1731066 2467369 := bstep (se 2 (by rfl) ⟨925263, by rfl⟩ : syracuseStep 2467369 = 1850527) B1850527
theorem B5842799 : Blo 1731066 5842799 := bstep (se 1 (by rfl) ⟨4382099, by rfl⟩ : syracuseStep 5842799 = 8764199) B8764199
theorem B3164537 : Blo 1731066 3164537 := bstep (se 2 (by rfl) ⟨1186701, by rfl⟩ : syracuseStep 3164537 = 2373403) B2373403
theorem B2599289 : Blo 1731066 2599289 := bstep (se 2 (by rfl) ⟨974733, by rfl⟩ : syracuseStep 2599289 = 1949467) B1949467
theorem B40004239 : Blo 1731066 40004239 := bstep (se 1 (by rfl) ⟨30003179, by rfl⟩ : syracuseStep 40004239 = 60006359) B60006359
theorem B1731311 : Blo 1731066 1731311 := bstep (se 1 (by rfl) ⟨1298483, by rfl⟩ : syracuseStep 1731311 = 2596967) B2596967
theorem B8768249 : Blo 1731066 8768249 := bstep (se 2 (by rfl) ⟨3288093, by rfl⟩ : syracuseStep 8768249 = 6576187) B6576187
theorem B9366911 : Blo 1731066 9366911 := bstep (se 1 (by rfl) ⟨7025183, by rfl⟩ : syracuseStep 9366911 = 14050367) B14050367
theorem B7400929 : Blo 1731066 7400929 := bstep (se 2 (by rfl) ⟨2775348, by rfl⟩ : syracuseStep 7400929 = 5550697) B5550697
theorem B5844527 : Blo 1731066 5844527 := bstep (se 1 (by rfl) ⟨4383395, by rfl⟩ : syracuseStep 5844527 = 8766791) B8766791
theorem B67506041 : Blo 1731066 67506041 := bstep (se 2 (by rfl) ⟨25314765, by rfl⟩ : syracuseStep 67506041 = 50629531) B50629531
theorem B9867197 : Blo 1731066 9867197 := bstep (se 3 (by rfl) ⟨1850099, by rfl⟩ : syracuseStep 9867197 = 3700199) B3700199
theorem B179909387 : Blo 1731066 179909387 := bstep (se 1 (by rfl) ⟨134932040, by rfl⟩ : syracuseStep 179909387 = 269864081) B269864081
theorem B2921339 : Blo 1731066 2921339 := bstep (se 1 (by rfl) ⟨2191004, by rfl⟩ : syracuseStep 2921339 = 4382009) B4382009
theorem B170931505 : Blo 1731066 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B22509049 : Blo 1731066 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B12662531 : Blo 1731066 12662531 := bstep (se 1 (by rfl) ⟨9496898, by rfl⟩ : syracuseStep 12662531 = 18993797) B18993797
theorem B13154075 : Blo 1731066 13154075 := bstep (se 1 (by rfl) ⟨9865556, by rfl⟩ : syracuseStep 13154075 = 19731113) B19731113
theorem B126449743 : Blo 1731066 126449743 := bstep (se 1 (by rfl) ⟨94837307, by rfl⟩ : syracuseStep 126449743 = 189674615) B189674615
theorem B8550775 : Blo 1731066 8550775 := bstep (se 1 (by rfl) ⟨6413081, by rfl⟩ : syracuseStep 8550775 = 12826163) B12826163
theorem B4930433 : Blo 1731066 4930433 := bstep (se 2 (by rfl) ⟨1848912, by rfl⟩ : syracuseStep 4930433 = 3697825) B3697825
theorem B12483791 : Blo 1731066 12483791 := bstep (se 1 (by rfl) ⟨9362843, by rfl⟩ : syracuseStep 12483791 = 18725687) B18725687
theorem B189562517 : Blo 1731066 189562517 := bstep (se 6 (by rfl) ⟨4442871, by rfl⟩ : syracuseStep 189562517 = 8885743) B8885743
theorem B10674145 : Blo 1731066 10674145 := bstep (se 2 (by rfl) ⟨4002804, by rfl⟩ : syracuseStep 10674145 = 8005609) B8005609
theorem B168599657 : Blo 1731066 168599657 := bstep (se 2 (by rfl) ⟨63224871, by rfl⟩ : syracuseStep 168599657 = 126449743) B126449743
theorem B119939591 : Blo 1731066 119939591 := bstep (se 1 (by rfl) ⟨89954693, by rfl⟩ : syracuseStep 119939591 = 179909387) B179909387
theorem B53338985 : Blo 1731066 53338985 := bstep (se 2 (by rfl) ⟨20002119, by rfl⟩ : syracuseStep 53338985 = 40004239) B40004239
theorem B3286955 : Blo 1731066 3286955 := bstep (se 1 (by rfl) ⟨2465216, by rfl⟩ : syracuseStep 3286955 = 4930433) B4930433
theorem B6244607 : Blo 1731066 6244607 := bstep (se 1 (by rfl) ⟨4683455, by rfl⟩ : syracuseStep 6244607 = 9366911) B9366911
theorem B14232193 : Blo 1731066 14232193 := bstep (se 2 (by rfl) ⟨5337072, by rfl⟩ : syracuseStep 14232193 = 10674145) B10674145
theorem B5843879 : Blo 1731066 5843879 := bstep (se 1 (by rfl) ⟨4382909, by rfl⟩ : syracuseStep 5843879 = 8765819) B8765819
theorem B1731743 : Blo 1731066 1731743 := bstep (se 1 (by rfl) ⟨1298807, by rfl⟩ : syracuseStep 1731743 = 2597615) B2597615
theorem B1731835 : Blo 1731066 1731835 := bstep (se 1 (by rfl) ⟨1298876, by rfl⟩ : syracuseStep 1731835 = 2597753) B2597753
theorem B1731943 : Blo 1731066 1731943 := bstep (se 1 (by rfl) ⟨1298957, by rfl⟩ : syracuseStep 1731943 = 2597915) B2597915
theorem B3894911 : Blo 1731066 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B8441687 : Blo 1731066 8441687 := bstep (se 1 (by rfl) ⟨6331265, by rfl⟩ : syracuseStep 8441687 = 12662531) B12662531
theorem B8769383 : Blo 1731066 8769383 := bstep (se 1 (by rfl) ⟨6577037, by rfl⟩ : syracuseStep 8769383 = 13154075) B13154075
theorem B3895199 : Blo 1731066 3895199 := bstep (se 1 (by rfl) ⟨2921399, by rfl⟩ : syracuseStep 3895199 = 5842799) B5842799
theorem B2109691 : Blo 1731066 2109691 := bstep (se 1 (by rfl) ⟨1582268, by rfl⟩ : syracuseStep 2109691 = 3164537) B3164537
theorem B1732859 : Blo 1731066 1732859 := bstep (se 1 (by rfl) ⟨1299644, by rfl⟩ : syracuseStep 1732859 = 2599289) B2599289
theorem B5845499 : Blo 1731066 5845499 := bstep (se 1 (by rfl) ⟨4384124, by rfl⟩ : syracuseStep 5845499 = 8768249) B8768249
theorem B9867905 : Blo 1731066 9867905 := bstep (se 2 (by rfl) ⟨3700464, by rfl⟩ : syracuseStep 9867905 = 7400929) B7400929
theorem B30012065 : Blo 1731066 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B3289825 : Blo 1731066 3289825 := bstep (se 2 (by rfl) ⟨1233684, by rfl⟩ : syracuseStep 3289825 = 2467369) B2467369
theorem B3896351 : Blo 1731066 3896351 := bstep (se 1 (by rfl) ⟨2922263, by rfl⟩ : syracuseStep 3896351 = 5844527) B5844527
theorem B126375011 : Blo 1731066 126375011 := bstep (se 1 (by rfl) ⟨94781258, by rfl⟩ : syracuseStep 126375011 = 189562517) B189562517
theorem B45004027 : Blo 1731066 45004027 := bstep (se 1 (by rfl) ⟨33753020, by rfl⟩ : syracuseStep 45004027 = 67506041) B67506041
theorem B1947559 : Blo 1731066 1947559 := bstep (se 1 (by rfl) ⟨1460669, by rfl⟩ : syracuseStep 1947559 = 2921339) B2921339
theorem B227908673 : Blo 1731066 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B45604133 : Blo 1731066 45604133 := bstep (se 4 (by rfl) ⟨4275387, by rfl⟩ : syracuseStep 45604133 = 8550775) B8550775
theorem B8322527 : Blo 1731066 8322527 := bstep (se 1 (by rfl) ⟨6241895, by rfl⟩ : syracuseStep 8322527 = 12483791) B12483791
theorem B6578131 : Blo 1731066 6578131 := bstep (se 1 (by rfl) ⟨4933598, by rfl⟩ : syracuseStep 6578131 = 9867197) B9867197
theorem B6578603 : Blo 1731066 6578603 := bstep (se 1 (by rfl) ⟨4933952, by rfl⟩ : syracuseStep 6578603 = 9867905) B9867905
theorem B2597567 : Blo 1731066 2597567 := bstep (se 1 (by rfl) ⟨1948175, by rfl⟩ : syracuseStep 2597567 = 3896351) B3896351
theorem B4163071 : Blo 1731066 4163071 := bstep (se 1 (by rfl) ⟨3122303, by rfl⟩ : syracuseStep 4163071 = 6244607) B6244607
theorem B151939115 : Blo 1731066 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B30402755 : Blo 1731066 30402755 := bstep (se 1 (by rfl) ⟨22802066, by rfl⟩ : syracuseStep 30402755 = 45604133) B45604133
theorem B5548351 : Blo 1731066 5548351 := bstep (se 1 (by rfl) ⟨4161263, by rfl⟩ : syracuseStep 5548351 = 8322527) B8322527
theorem B2812921 : Blo 1731066 2812921 := bstep (se 2 (by rfl) ⟨1054845, by rfl⟩ : syracuseStep 2812921 = 2109691) B2109691
theorem B20008043 : Blo 1731066 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B84250007 : Blo 1731066 84250007 := bstep (se 1 (by rfl) ⟨63187505, by rfl⟩ : syracuseStep 84250007 = 126375011) B126375011
theorem B4386433 : Blo 1731066 4386433 := bstep (se 2 (by rfl) ⟨1644912, by rfl⟩ : syracuseStep 4386433 = 3289825) B3289825
theorem B2191303 : Blo 1731066 2191303 := bstep (se 1 (by rfl) ⟨1643477, by rfl⟩ : syracuseStep 2191303 = 3286955) B3286955
theorem B3895919 : Blo 1731066 3895919 := bstep (se 1 (by rfl) ⟨2921939, by rfl⟩ : syracuseStep 3895919 = 5843879) B5843879
theorem B5846255 : Blo 1731066 5846255 := bstep (se 1 (by rfl) ⟨4384691, by rfl⟩ : syracuseStep 5846255 = 8769383) B8769383
theorem B8770841 : Blo 1731066 8770841 := bstep (se 2 (by rfl) ⟨3289065, by rfl⟩ : syracuseStep 8770841 = 6578131) B6578131
theorem B112399771 : Blo 1731066 112399771 := bstep (se 1 (by rfl) ⟨84299828, by rfl⟩ : syracuseStep 112399771 = 168599657) B168599657
theorem B3896999 : Blo 1731066 3896999 := bstep (se 1 (by rfl) ⟨2922749, by rfl⟩ : syracuseStep 3896999 = 5845499) B5845499
theorem B79959727 : Blo 1731066 79959727 := bstep (se 1 (by rfl) ⟨59969795, by rfl⟩ : syracuseStep 79959727 = 119939591) B119939591
theorem B35559323 : Blo 1731066 35559323 := bstep (se 1 (by rfl) ⟨26669492, by rfl⟩ : syracuseStep 35559323 = 53338985) B53338985
theorem B75905029 : Blo 1731066 75905029 := bstep (se 4 (by rfl) ⟨7116096, by rfl⟩ : syracuseStep 75905029 = 14232193) B14232193
theorem B60005369 : Blo 1731066 60005369 := bstep (se 2 (by rfl) ⟨22502013, by rfl⟩ : syracuseStep 60005369 = 45004027) B45004027
theorem B2596607 : Blo 1731066 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B2596745 : Blo 1731066 2596745 := bstep (se 2 (by rfl) ⟨973779, by rfl⟩ : syracuseStep 2596745 = 1947559) B1947559
theorem B5627791 : Blo 1731066 5627791 := bstep (se 1 (by rfl) ⟨4220843, by rfl⟩ : syracuseStep 5627791 = 8441687) B8441687
theorem B2596799 : Blo 1731066 2596799 := bstep (se 1 (by rfl) ⟨1947599, by rfl⟩ : syracuseStep 2596799 = 3895199) B3895199
theorem B2597279 : Blo 1731066 2597279 := bstep (se 1 (by rfl) ⟨1947959, by rfl⟩ : syracuseStep 2597279 = 3895919) B3895919
theorem B7397801 : Blo 1731066 7397801 := bstep (se 2 (by rfl) ⟨2774175, by rfl⟩ : syracuseStep 7397801 = 5548351) B5548351
theorem B2597999 : Blo 1731066 2597999 := bstep (se 1 (by rfl) ⟨1948499, by rfl⟩ : syracuseStep 2597999 = 3896999) B3896999
theorem B20268503 : Blo 1731066 20268503 := bstep (se 1 (by rfl) ⟨15201377, by rfl⟩ : syracuseStep 20268503 = 30402755) B30402755
theorem B149866361 : Blo 1731066 149866361 := bstep (se 2 (by rfl) ⟨56199885, by rfl⟩ : syracuseStep 149866361 = 112399771) B112399771
theorem B40003579 : Blo 1731066 40003579 := bstep (se 1 (by rfl) ⟨30002684, by rfl⟩ : syracuseStep 40003579 = 60005369) B60005369
theorem B13338695 : Blo 1731066 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B106612969 : Blo 1731066 106612969 := bstep (se 2 (by rfl) ⟨39979863, by rfl⟩ : syracuseStep 106612969 = 79959727) B79959727
theorem B56166671 : Blo 1731066 56166671 := bstep (se 1 (by rfl) ⟨42125003, by rfl⟩ : syracuseStep 56166671 = 84250007) B84250007
theorem B1731071 : Blo 1731066 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B1731163 : Blo 1731066 1731163 := bstep (se 1 (by rfl) ⟨1298372, by rfl⟩ : syracuseStep 1731163 = 2596745) B2596745
theorem B1731199 : Blo 1731066 1731199 := bstep (se 1 (by rfl) ⟨1298399, by rfl⟩ : syracuseStep 1731199 = 2596799) B2596799
theorem B15002245 : Blo 1731066 15002245 := bstep (se 4 (by rfl) ⟨1406460, by rfl⟩ : syracuseStep 15002245 = 2812921) B2812921
theorem B101206705 : Blo 1731066 101206705 := bstep (se 2 (by rfl) ⟨37952514, by rfl⟩ : syracuseStep 101206705 = 75905029) B75905029
theorem B4385735 : Blo 1731066 4385735 := bstep (se 1 (by rfl) ⟨3289301, by rfl⟩ : syracuseStep 4385735 = 6578603) B6578603
theorem B1731711 : Blo 1731066 1731711 := bstep (se 1 (by rfl) ⟨1298783, by rfl⟩ : syracuseStep 1731711 = 2597567) B2597567
theorem B5550761 : Blo 1731066 5550761 := bstep (se 2 (by rfl) ⟨2081535, by rfl⟩ : syracuseStep 5550761 = 4163071) B4163071
theorem B2921737 : Blo 1731066 2921737 := bstep (se 2 (by rfl) ⟨1095651, by rfl⟩ : syracuseStep 2921737 = 2191303) B2191303
theorem B3897503 : Blo 1731066 3897503 := bstep (se 1 (by rfl) ⟨2923127, by rfl⟩ : syracuseStep 3897503 = 5846255) B5846255
theorem B5847227 : Blo 1731066 5847227 := bstep (se 1 (by rfl) ⟨4385420, by rfl⟩ : syracuseStep 5847227 = 8770841) B8770841
theorem B23706215 : Blo 1731066 23706215 := bstep (se 1 (by rfl) ⟨17779661, by rfl⟩ : syracuseStep 23706215 = 35559323) B35559323
theorem B101292743 : Blo 1731066 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B5848577 : Blo 1731066 5848577 := bstep (se 2 (by rfl) ⟨2193216, by rfl⟩ : syracuseStep 5848577 = 4386433) B4386433
theorem B7503721 : Blo 1731066 7503721 := bstep (se 2 (by rfl) ⟨2813895, by rfl⟩ : syracuseStep 7503721 = 5627791) B5627791
theorem B4931867 : Blo 1731066 4931867 := bstep (se 1 (by rfl) ⟨3698900, by rfl⟩ : syracuseStep 4931867 = 7397801) B7397801
theorem B99910907 : Blo 1731066 99910907 := bstep (se 1 (by rfl) ⟨74933180, by rfl⟩ : syracuseStep 99910907 = 149866361) B149866361
theorem B2598335 : Blo 1731066 2598335 := bstep (se 1 (by rfl) ⟨1948751, by rfl⟩ : syracuseStep 2598335 = 3897503) B3897503
theorem B15804143 : Blo 1731066 15804143 := bstep (se 1 (by rfl) ⟨11853107, by rfl⟩ : syracuseStep 15804143 = 23706215) B23706215
theorem B67528495 : Blo 1731066 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B40019845 : Blo 1731066 40019845 := bstep (se 4 (by rfl) ⟨3751860, by rfl⟩ : syracuseStep 40019845 = 7503721) B7503721
theorem B1731519 : Blo 1731066 1731519 := bstep (se 1 (by rfl) ⟨1298639, by rfl⟩ : syracuseStep 1731519 = 2597279) B2597279
theorem B142150625 : Blo 1731066 142150625 := bstep (se 2 (by rfl) ⟨53306484, by rfl⟩ : syracuseStep 142150625 = 106612969) B106612969
theorem B1731999 : Blo 1731066 1731999 := bstep (se 1 (by rfl) ⟨1298999, by rfl⟩ : syracuseStep 1731999 = 2597999) B2597999
theorem B134942273 : Blo 1731066 134942273 := bstep (se 2 (by rfl) ⟨50603352, by rfl⟩ : syracuseStep 134942273 = 101206705) B101206705
theorem B13512335 : Blo 1731066 13512335 := bstep (se 1 (by rfl) ⟨10134251, by rfl⟩ : syracuseStep 13512335 = 20268503) B20268503
theorem B8892463 : Blo 1731066 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B3895649 : Blo 1731066 3895649 := bstep (se 2 (by rfl) ⟨1460868, by rfl⟩ : syracuseStep 3895649 = 2921737) B2921737
theorem B3700507 : Blo 1731066 3700507 := bstep (se 1 (by rfl) ⟨2775380, by rfl⟩ : syracuseStep 3700507 = 5550761) B5550761
theorem B20002993 : Blo 1731066 20002993 := bstep (se 2 (by rfl) ⟨7501122, by rfl⟩ : syracuseStep 20002993 = 15002245) B15002245
theorem B3898151 : Blo 1731066 3898151 := bstep (se 1 (by rfl) ⟨2923613, by rfl⟩ : syracuseStep 3898151 = 5847227) B5847227
theorem B37444447 : Blo 1731066 37444447 := bstep (se 1 (by rfl) ⟨28083335, by rfl⟩ : syracuseStep 37444447 = 56166671) B56166671
theorem B2923823 : Blo 1731066 2923823 := bstep (se 1 (by rfl) ⟨2192867, by rfl⟩ : syracuseStep 2923823 = 4385735) B4385735
theorem B3899051 : Blo 1731066 3899051 := bstep (se 1 (by rfl) ⟨2924288, by rfl⟩ : syracuseStep 3899051 = 5848577) B5848577
theorem B53338105 : Blo 1731066 53338105 := bstep (se 2 (by rfl) ⟨20001789, by rfl⟩ : syracuseStep 53338105 = 40003579) B40003579
theorem B2597099 : Blo 1731066 2597099 := bstep (se 1 (by rfl) ⟨1947824, by rfl⟩ : syracuseStep 2597099 = 3895649) B3895649
theorem B426730517 : Blo 1731066 426730517 := bstep (se 6 (by rfl) ⟨10001496, by rfl⟩ : syracuseStep 426730517 = 20002993) B20002993
theorem B10536095 : Blo 1731066 10536095 := bstep (se 1 (by rfl) ⟨7902071, by rfl⟩ : syracuseStep 10536095 = 15804143) B15804143
theorem B2598767 : Blo 1731066 2598767 := bstep (se 1 (by rfl) ⟨1949075, by rfl⟩ : syracuseStep 2598767 = 3898151) B3898151
theorem B94767083 : Blo 1731066 94767083 := bstep (se 1 (by rfl) ⟨71075312, by rfl⟩ : syracuseStep 94767083 = 142150625) B142150625
theorem B4934009 : Blo 1731066 4934009 := bstep (se 2 (by rfl) ⟨1850253, by rfl⟩ : syracuseStep 4934009 = 3700507) B3700507
theorem B2599367 : Blo 1731066 2599367 := bstep (se 1 (by rfl) ⟨1949525, by rfl⟩ : syracuseStep 2599367 = 3899051) B3899051
theorem B284469893 : Blo 1731066 284469893 := bstep (se 4 (by rfl) ⟨26669052, by rfl⟩ : syracuseStep 284469893 = 53338105) B53338105
theorem B11856617 : Blo 1731066 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B13151645 : Blo 1731066 13151645 := bstep (se 3 (by rfl) ⟨2465933, by rfl⟩ : syracuseStep 13151645 = 4931867) B4931867
theorem B1732223 : Blo 1731066 1732223 := bstep (se 1 (by rfl) ⟨1299167, by rfl⟩ : syracuseStep 1732223 = 2598335) B2598335
theorem B49925929 : Blo 1731066 49925929 := bstep (se 2 (by rfl) ⟨18722223, by rfl⟩ : syracuseStep 49925929 = 37444447) B37444447
theorem B36032893 : Blo 1731066 36032893 := bstep (se 3 (by rfl) ⟨6756167, by rfl⟩ : syracuseStep 36032893 = 13512335) B13512335
theorem B89961515 : Blo 1731066 89961515 := bstep (se 1 (by rfl) ⟨67471136, by rfl⟩ : syracuseStep 89961515 = 134942273) B134942273
theorem B53359793 : Blo 1731066 53359793 := bstep (se 2 (by rfl) ⟨20009922, by rfl⟩ : syracuseStep 53359793 = 40019845) B40019845
theorem B66607271 : Blo 1731066 66607271 := bstep (se 1 (by rfl) ⟨49955453, by rfl⟩ : syracuseStep 66607271 = 99910907) B99910907
theorem B1949215 : Blo 1731066 1949215 := bstep (se 1 (by rfl) ⟨1461911, by rfl⟩ : syracuseStep 1949215 = 2923823) B2923823
theorem B90037993 : Blo 1731066 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B59974343 : Blo 1731066 59974343 := bstep (se 1 (by rfl) ⟨44980757, by rfl⟩ : syracuseStep 59974343 = 89961515) B89961515
theorem B63178055 : Blo 1731066 63178055 := bstep (se 1 (by rfl) ⟨47383541, by rfl⟩ : syracuseStep 63178055 = 94767083) B94767083
theorem B189646595 : Blo 1731066 189646595 := bstep (se 1 (by rfl) ⟨142234946, by rfl⟩ : syracuseStep 189646595 = 284469893) B284469893
theorem B2598953 : Blo 1731066 2598953 := bstep (se 2 (by rfl) ⟨974607, by rfl⟩ : syracuseStep 2598953 = 1949215) B1949215
theorem B8767763 : Blo 1731066 8767763 := bstep (se 1 (by rfl) ⟨6575822, by rfl⟩ : syracuseStep 8767763 = 13151645) B13151645
theorem B1731399 : Blo 1731066 1731399 := bstep (se 1 (by rfl) ⟨1298549, by rfl⟩ : syracuseStep 1731399 = 2597099) B2597099
theorem B284487011 : Blo 1731066 284487011 := bstep (se 1 (by rfl) ⟨213365258, by rfl⟩ : syracuseStep 284487011 = 426730517) B426730517
theorem B35573195 : Blo 1731066 35573195 := bstep (se 1 (by rfl) ⟨26679896, by rfl⟩ : syracuseStep 35573195 = 53359793) B53359793
theorem B1732511 : Blo 1731066 1732511 := bstep (se 1 (by rfl) ⟨1299383, by rfl⟩ : syracuseStep 1732511 = 2598767) B2598767
theorem B44404847 : Blo 1731066 44404847 := bstep (se 1 (by rfl) ⟨33303635, by rfl⟩ : syracuseStep 44404847 = 66607271) B66607271
theorem B3289339 : Blo 1731066 3289339 := bstep (se 1 (by rfl) ⟨2467004, by rfl⟩ : syracuseStep 3289339 = 4934009) B4934009
theorem B1732911 : Blo 1731066 1732911 := bstep (se 1 (by rfl) ⟨1299683, by rfl⟩ : syracuseStep 1732911 = 2599367) B2599367
theorem B120050657 : Blo 1731066 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B28096253 : Blo 1731066 28096253 := bstep (se 3 (by rfl) ⟨5268047, by rfl⟩ : syracuseStep 28096253 = 10536095) B10536095
theorem B7904411 : Blo 1731066 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B192175429 : Blo 1731066 192175429 := bstep (se 4 (by rfl) ⟨18016446, by rfl⟩ : syracuseStep 192175429 = 36032893) B36032893
theorem B66567905 : Blo 1731066 66567905 := bstep (se 2 (by rfl) ⟨24962964, by rfl⟩ : syracuseStep 66567905 = 49925929) B49925929
theorem B5269607 : Blo 1731066 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B44378603 : Blo 1731066 44378603 := bstep (se 1 (by rfl) ⟨33283952, by rfl⟩ : syracuseStep 44378603 = 66567905) B66567905
theorem B4385785 : Blo 1731066 4385785 := bstep (se 2 (by rfl) ⟨1644669, by rfl⟩ : syracuseStep 4385785 = 3289339) B3289339
theorem B42118703 : Blo 1731066 42118703 := bstep (se 1 (by rfl) ⟨31589027, by rfl⟩ : syracuseStep 42118703 = 63178055) B63178055
theorem B18730835 : Blo 1731066 18730835 := bstep (se 1 (by rfl) ⟨14048126, by rfl⟩ : syracuseStep 18730835 = 28096253) B28096253
theorem B126431063 : Blo 1731066 126431063 := bstep (se 1 (by rfl) ⟨94823297, by rfl⟩ : syracuseStep 126431063 = 189646595) B189646595
theorem B1732635 : Blo 1731066 1732635 := bstep (se 1 (by rfl) ⟨1299476, by rfl⟩ : syracuseStep 1732635 = 2598953) B2598953
theorem B5845175 : Blo 1731066 5845175 := bstep (se 1 (by rfl) ⟨4383881, by rfl⟩ : syracuseStep 5845175 = 8767763) B8767763
theorem B256233905 : Blo 1731066 256233905 := bstep (se 2 (by rfl) ⟨96087714, by rfl⟩ : syracuseStep 256233905 = 192175429) B192175429
theorem B189658007 : Blo 1731066 189658007 := bstep (se 1 (by rfl) ⟨142243505, by rfl⟩ : syracuseStep 189658007 = 284487011) B284487011
theorem B29603231 : Blo 1731066 29603231 := bstep (se 1 (by rfl) ⟨22202423, by rfl⟩ : syracuseStep 29603231 = 44404847) B44404847
theorem B39982895 : Blo 1731066 39982895 := bstep (se 1 (by rfl) ⟨29987171, by rfl⟩ : syracuseStep 39982895 = 59974343) B59974343
theorem B80033771 : Blo 1731066 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B23715463 : Blo 1731066 23715463 := bstep (se 1 (by rfl) ⟨17786597, by rfl⟩ : syracuseStep 23715463 = 35573195) B35573195
theorem B19735487 : Blo 1731066 19735487 := bstep (se 1 (by rfl) ⟨14801615, by rfl⟩ : syracuseStep 19735487 = 29603231) B29603231
theorem B53355847 : Blo 1731066 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B12487223 : Blo 1731066 12487223 := bstep (se 1 (by rfl) ⟨9365417, by rfl⟩ : syracuseStep 12487223 = 18730835) B18730835
theorem B170822603 : Blo 1731066 170822603 := bstep (se 1 (by rfl) ⟨128116952, by rfl⟩ : syracuseStep 170822603 = 256233905) B256233905
theorem B126438671 : Blo 1731066 126438671 := bstep (se 1 (by rfl) ⟨94829003, by rfl⟩ : syracuseStep 126438671 = 189658007) B189658007
theorem B29585735 : Blo 1731066 29585735 := bstep (se 1 (by rfl) ⟨22189301, by rfl⟩ : syracuseStep 29585735 = 44378603) B44378603
theorem B28079135 : Blo 1731066 28079135 := bstep (se 1 (by rfl) ⟨21059351, by rfl⟩ : syracuseStep 28079135 = 42118703) B42118703
theorem B3896783 : Blo 1731066 3896783 := bstep (se 1 (by rfl) ⟨2922587, by rfl⟩ : syracuseStep 3896783 = 5845175) B5845175
theorem B26655263 : Blo 1731066 26655263 := bstep (se 1 (by rfl) ⟨19991447, by rfl⟩ : syracuseStep 26655263 = 39982895) B39982895
theorem B5847713 : Blo 1731066 5847713 := bstep (se 2 (by rfl) ⟨2192892, by rfl⟩ : syracuseStep 5847713 = 4385785) B4385785
theorem B3513071 : Blo 1731066 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B31620617 : Blo 1731066 31620617 := bstep (se 2 (by rfl) ⟨11857731, by rfl⟩ : syracuseStep 31620617 = 23715463) B23715463
theorem B84287375 : Blo 1731066 84287375 := bstep (se 1 (by rfl) ⟨63215531, by rfl⟩ : syracuseStep 84287375 = 126431063) B126431063
theorem B13156991 : Blo 1731066 13156991 := bstep (se 1 (by rfl) ⟨9867743, by rfl⟩ : syracuseStep 13156991 = 19735487) B19735487
theorem B18719423 : Blo 1731066 18719423 := bstep (se 1 (by rfl) ⟨14039567, by rfl⟩ : syracuseStep 18719423 = 28079135) B28079135
theorem B2597855 : Blo 1731066 2597855 := bstep (se 1 (by rfl) ⟨1948391, by rfl⟩ : syracuseStep 2597855 = 3896783) B3896783
theorem B17770175 : Blo 1731066 17770175 := bstep (se 1 (by rfl) ⟨13327631, by rfl⟩ : syracuseStep 17770175 = 26655263) B26655263
theorem B71141129 : Blo 1731066 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B21080411 : Blo 1731066 21080411 := bstep (se 1 (by rfl) ⟨15810308, by rfl⟩ : syracuseStep 21080411 = 31620617) B31620617
theorem B56191583 : Blo 1731066 56191583 := bstep (se 1 (by rfl) ⟨42143687, by rfl⟩ : syracuseStep 56191583 = 84287375) B84287375
theorem B113881735 : Blo 1731066 113881735 := bstep (se 1 (by rfl) ⟨85411301, by rfl⟩ : syracuseStep 113881735 = 170822603) B170822603
theorem B84292447 : Blo 1731066 84292447 := bstep (se 1 (by rfl) ⟨63219335, by rfl⟩ : syracuseStep 84292447 = 126438671) B126438671
theorem B19723823 : Blo 1731066 19723823 := bstep (se 1 (by rfl) ⟨14792867, by rfl⟩ : syracuseStep 19723823 = 29585735) B29585735
theorem B33299261 : Blo 1731066 33299261 := bstep (se 3 (by rfl) ⟨6243611, by rfl⟩ : syracuseStep 33299261 = 12487223) B12487223
theorem B3898475 : Blo 1731066 3898475 := bstep (se 1 (by rfl) ⟨2923856, by rfl⟩ : syracuseStep 3898475 = 5847713) B5847713
theorem B2342047 : Blo 1731066 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B13149215 : Blo 1731066 13149215 := bstep (se 1 (by rfl) ⟨9861911, by rfl⟩ : syracuseStep 13149215 = 19723823) B19723823
theorem B11846783 : Blo 1731066 11846783 := bstep (se 1 (by rfl) ⟨8885087, by rfl⟩ : syracuseStep 11846783 = 17770175) B17770175
theorem B3122729 : Blo 1731066 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B2598983 : Blo 1731066 2598983 := bstep (se 1 (by rfl) ⟨1949237, by rfl⟩ : syracuseStep 2598983 = 3898475) B3898475
theorem B12479615 : Blo 1731066 12479615 := bstep (se 1 (by rfl) ⟨9359711, by rfl⟩ : syracuseStep 12479615 = 18719423) B18719423
theorem B1731903 : Blo 1731066 1731903 := bstep (se 1 (by rfl) ⟨1298927, by rfl⟩ : syracuseStep 1731903 = 2597855) B2597855
theorem B151842313 : Blo 1731066 151842313 := bstep (se 2 (by rfl) ⟨56940867, by rfl⟩ : syracuseStep 151842313 = 113881735) B113881735
theorem B112389929 : Blo 1731066 112389929 := bstep (se 2 (by rfl) ⟨42146223, by rfl⟩ : syracuseStep 112389929 = 84292447) B84292447
theorem B47427419 : Blo 1731066 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B14053607 : Blo 1731066 14053607 := bstep (se 1 (by rfl) ⟨10540205, by rfl⟩ : syracuseStep 14053607 = 21080411) B21080411
theorem B8771327 : Blo 1731066 8771327 := bstep (se 1 (by rfl) ⟨6578495, by rfl⟩ : syracuseStep 8771327 = 13156991) B13156991
theorem B37461055 : Blo 1731066 37461055 := bstep (se 1 (by rfl) ⟨28095791, by rfl⟩ : syracuseStep 37461055 = 56191583) B56191583
theorem B22199507 : Blo 1731066 22199507 := bstep (se 1 (by rfl) ⟨16649630, by rfl⟩ : syracuseStep 22199507 = 33299261) B33299261
theorem B8766143 : Blo 1731066 8766143 := bstep (se 1 (by rfl) ⟨6574607, by rfl⟩ : syracuseStep 8766143 = 13149215) B13149215
theorem B2081819 : Blo 1731066 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B49948073 : Blo 1731066 49948073 := bstep (se 2 (by rfl) ⟨18730527, by rfl⟩ : syracuseStep 49948073 = 37461055) B37461055
theorem B74926619 : Blo 1731066 74926619 := bstep (se 1 (by rfl) ⟨56194964, by rfl⟩ : syracuseStep 74926619 = 112389929) B112389929
theorem B31591421 : Blo 1731066 31591421 := bstep (se 3 (by rfl) ⟨5923391, by rfl⟩ : syracuseStep 31591421 = 11846783) B11846783
theorem B1732655 : Blo 1731066 1732655 := bstep (se 1 (by rfl) ⟨1299491, by rfl⟩ : syracuseStep 1732655 = 2598983) B2598983
theorem B8319743 : Blo 1731066 8319743 := bstep (se 1 (by rfl) ⟨6239807, by rfl⟩ : syracuseStep 8319743 = 12479615) B12479615
theorem B14799671 : Blo 1731066 14799671 := bstep (se 1 (by rfl) ⟨11099753, by rfl⟩ : syracuseStep 14799671 = 22199507) B22199507
theorem B31618279 : Blo 1731066 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B9369071 : Blo 1731066 9369071 := bstep (se 1 (by rfl) ⟨7026803, by rfl⟩ : syracuseStep 9369071 = 14053607) B14053607
theorem B5847551 : Blo 1731066 5847551 := bstep (se 1 (by rfl) ⟨4385663, by rfl⟩ : syracuseStep 5847551 = 8771327) B8771327
theorem B202456417 : Blo 1731066 202456417 := bstep (se 2 (by rfl) ⟨75921156, by rfl⟩ : syracuseStep 202456417 = 151842313) B151842313
theorem B5546495 : Blo 1731066 5546495 := bstep (se 1 (by rfl) ⟨4159871, by rfl⟩ : syracuseStep 5546495 = 8319743) B8319743
theorem B42157705 : Blo 1731066 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B5844095 : Blo 1731066 5844095 := bstep (se 1 (by rfl) ⟨4383071, by rfl⟩ : syracuseStep 5844095 = 8766143) B8766143
theorem B9866447 : Blo 1731066 9866447 := bstep (se 1 (by rfl) ⟨7399835, by rfl⟩ : syracuseStep 9866447 = 14799671) B14799671
theorem B6246047 : Blo 1731066 6246047 := bstep (se 1 (by rfl) ⟨4684535, by rfl⟩ : syracuseStep 6246047 = 9369071) B9369071
theorem B49951079 : Blo 1731066 49951079 := bstep (se 1 (by rfl) ⟨37463309, by rfl⟩ : syracuseStep 49951079 = 74926619) B74926619
theorem B5551517 : Blo 1731066 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B33298715 : Blo 1731066 33298715 := bstep (se 1 (by rfl) ⟨24974036, by rfl⟩ : syracuseStep 33298715 = 49948073) B49948073
theorem B3898367 : Blo 1731066 3898367 := bstep (se 1 (by rfl) ⟨2923775, by rfl⟩ : syracuseStep 3898367 = 5847551) B5847551
theorem B269941889 : Blo 1731066 269941889 := bstep (se 2 (by rfl) ⟨101228208, by rfl⟩ : syracuseStep 269941889 = 202456417) B202456417
theorem B21060947 : Blo 1731066 21060947 := bstep (se 1 (by rfl) ⟨15795710, by rfl⟩ : syracuseStep 21060947 = 31591421) B31591421
theorem B33300719 : Blo 1731066 33300719 := bstep (se 1 (by rfl) ⟨24975539, by rfl⟩ : syracuseStep 33300719 = 49951079) B49951079
theorem B14804045 : Blo 1731066 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B2598911 : Blo 1731066 2598911 := bstep (se 1 (by rfl) ⟨1949183, by rfl⟩ : syracuseStep 2598911 = 3898367) B3898367
theorem B4164031 : Blo 1731066 4164031 := bstep (se 1 (by rfl) ⟨3123023, by rfl⟩ : syracuseStep 4164031 = 6246047) B6246047
theorem B3697663 : Blo 1731066 3697663 := bstep (se 1 (by rfl) ⟨2773247, by rfl⟩ : syracuseStep 3697663 = 5546495) B5546495
theorem B3896063 : Blo 1731066 3896063 := bstep (se 1 (by rfl) ⟨2922047, by rfl⟩ : syracuseStep 3896063 = 5844095) B5844095
theorem B56210273 : Blo 1731066 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B22199143 : Blo 1731066 22199143 := bstep (se 1 (by rfl) ⟨16649357, by rfl⟩ : syracuseStep 22199143 = 33298715) B33298715
theorem B179961259 : Blo 1731066 179961259 := bstep (se 1 (by rfl) ⟨134970944, by rfl⟩ : syracuseStep 179961259 = 269941889) B269941889
theorem B6577631 : Blo 1731066 6577631 := bstep (se 1 (by rfl) ⟨4933223, by rfl⟩ : syracuseStep 6577631 = 9866447) B9866447
theorem B14040631 : Blo 1731066 14040631 := bstep (se 1 (by rfl) ⟨10530473, by rfl⟩ : syracuseStep 14040631 = 21060947) B21060947
theorem B22200479 : Blo 1731066 22200479 := bstep (se 1 (by rfl) ⟨16650359, by rfl⟩ : syracuseStep 22200479 = 33300719) B33300719
theorem B2597375 : Blo 1731066 2597375 := bstep (se 1 (by rfl) ⟨1948031, by rfl⟩ : syracuseStep 2597375 = 3896063) B3896063
theorem B29598857 : Blo 1731066 29598857 := bstep (se 2 (by rfl) ⟨11099571, by rfl⟩ : syracuseStep 29598857 = 22199143) B22199143
theorem B18720841 : Blo 1731066 18720841 := bstep (se 2 (by rfl) ⟨7020315, by rfl⟩ : syracuseStep 18720841 = 14040631) B14040631
theorem B4385087 : Blo 1731066 4385087 := bstep (se 1 (by rfl) ⟨3288815, by rfl⟩ : syracuseStep 4385087 = 6577631) B6577631
theorem B37473515 : Blo 1731066 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B1732607 : Blo 1731066 1732607 := bstep (se 1 (by rfl) ⟨1299455, by rfl⟩ : syracuseStep 1732607 = 2598911) B2598911
theorem B239948345 : Blo 1731066 239948345 := bstep (se 2 (by rfl) ⟨89980629, by rfl⟩ : syracuseStep 239948345 = 179961259) B179961259
theorem B9869363 : Blo 1731066 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B4930217 : Blo 1731066 4930217 := bstep (se 2 (by rfl) ⟨1848831, by rfl⟩ : syracuseStep 4930217 = 3697663) B3697663
theorem B22208165 : Blo 1731066 22208165 := bstep (se 4 (by rfl) ⟨2082015, by rfl⟩ : syracuseStep 22208165 = 4164031) B4164031
theorem B24961121 : Blo 1731066 24961121 := bstep (se 2 (by rfl) ⟨9360420, by rfl⟩ : syracuseStep 24961121 = 18720841) B18720841
theorem B159965563 : Blo 1731066 159965563 := bstep (se 1 (by rfl) ⟨119974172, by rfl⟩ : syracuseStep 159965563 = 239948345) B239948345
theorem B6579575 : Blo 1731066 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B3286811 : Blo 1731066 3286811 := bstep (se 1 (by rfl) ⟨2465108, by rfl⟩ : syracuseStep 3286811 = 4930217) B4930217
theorem B14805443 : Blo 1731066 14805443 := bstep (se 1 (by rfl) ⟨11104082, by rfl⟩ : syracuseStep 14805443 = 22208165) B22208165
theorem B1731583 : Blo 1731066 1731583 := bstep (se 1 (by rfl) ⟨1298687, by rfl⟩ : syracuseStep 1731583 = 2597375) B2597375
theorem B24982343 : Blo 1731066 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B14800319 : Blo 1731066 14800319 := bstep (se 1 (by rfl) ⟨11100239, by rfl⟩ : syracuseStep 14800319 = 22200479) B22200479
theorem B19732571 : Blo 1731066 19732571 := bstep (se 1 (by rfl) ⟨14799428, by rfl⟩ : syracuseStep 19732571 = 29598857) B29598857
theorem B2923391 : Blo 1731066 2923391 := bstep (se 1 (by rfl) ⟨2192543, by rfl⟩ : syracuseStep 2923391 = 4385087) B4385087
theorem B213287417 : Blo 1731066 213287417 := bstep (se 2 (by rfl) ⟨79982781, by rfl⟩ : syracuseStep 213287417 = 159965563) B159965563
theorem B16654895 : Blo 1731066 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B16640747 : Blo 1731066 16640747 := bstep (se 1 (by rfl) ⟨12480560, by rfl⟩ : syracuseStep 16640747 = 24961121) B24961121
theorem B4386383 : Blo 1731066 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B9866879 : Blo 1731066 9866879 := bstep (se 1 (by rfl) ⟨7400159, by rfl⟩ : syracuseStep 9866879 = 14800319) B14800319
theorem B2191207 : Blo 1731066 2191207 := bstep (se 1 (by rfl) ⟨1643405, by rfl⟩ : syracuseStep 2191207 = 3286811) B3286811
theorem B13155047 : Blo 1731066 13155047 := bstep (se 1 (by rfl) ⟨9866285, by rfl⟩ : syracuseStep 13155047 = 19732571) B19732571
theorem B9870295 : Blo 1731066 9870295 := bstep (se 1 (by rfl) ⟨7402721, by rfl⟩ : syracuseStep 9870295 = 14805443) B14805443
theorem B1948927 : Blo 1731066 1948927 := bstep (se 1 (by rfl) ⟨1461695, by rfl⟩ : syracuseStep 1948927 = 2923391) B2923391
theorem B2598569 : Blo 1731066 2598569 := bstep (se 2 (by rfl) ⟨974463, by rfl⟩ : syracuseStep 2598569 = 1948927) B1948927
theorem B11093831 : Blo 1731066 11093831 := bstep (se 1 (by rfl) ⟨8320373, by rfl⟩ : syracuseStep 11093831 = 16640747) B16640747
theorem B142191611 : Blo 1731066 142191611 := bstep (se 1 (by rfl) ⟨106643708, by rfl⟩ : syracuseStep 142191611 = 213287417) B213287417
theorem B11103263 : Blo 1731066 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B13160393 : Blo 1731066 13160393 := bstep (se 2 (by rfl) ⟨4935147, by rfl⟩ : syracuseStep 13160393 = 9870295) B9870295
theorem B8770031 : Blo 1731066 8770031 := bstep (se 1 (by rfl) ⟨6577523, by rfl⟩ : syracuseStep 8770031 = 13155047) B13155047
theorem B2921609 : Blo 1731066 2921609 := bstep (se 2 (by rfl) ⟨1095603, by rfl⟩ : syracuseStep 2921609 = 2191207) B2191207
theorem B2924255 : Blo 1731066 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B6577919 : Blo 1731066 6577919 := bstep (se 1 (by rfl) ⟨4933439, by rfl⟩ : syracuseStep 6577919 = 9866879) B9866879
theorem B4385279 : Blo 1731066 4385279 := bstep (se 1 (by rfl) ⟨3288959, by rfl⟩ : syracuseStep 4385279 = 6577919) B6577919
theorem B1732379 : Blo 1731066 1732379 := bstep (se 1 (by rfl) ⟨1299284, by rfl⟩ : syracuseStep 1732379 = 2598569) B2598569
theorem B94794407 : Blo 1731066 94794407 := bstep (se 1 (by rfl) ⟨71095805, by rfl⟩ : syracuseStep 94794407 = 142191611) B142191611
theorem B7402175 : Blo 1731066 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B5846687 : Blo 1731066 5846687 := bstep (se 1 (by rfl) ⟨4385015, by rfl⟩ : syracuseStep 5846687 = 8770031) B8770031
theorem B1947739 : Blo 1731066 1947739 := bstep (se 1 (by rfl) ⟨1460804, by rfl⟩ : syracuseStep 1947739 = 2921609) B2921609
theorem B7395887 : Blo 1731066 7395887 := bstep (se 1 (by rfl) ⟨5546915, by rfl⟩ : syracuseStep 7395887 = 11093831) B11093831
theorem B1949503 : Blo 1731066 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B8773595 : Blo 1731066 8773595 := bstep (se 1 (by rfl) ⟨6580196, by rfl⟩ : syracuseStep 8773595 = 13160393) B13160393
theorem B2596985 : Blo 1731066 2596985 := bstep (se 2 (by rfl) ⟨973869, by rfl⟩ : syracuseStep 2596985 = 1947739) B1947739
theorem B2599337 : Blo 1731066 2599337 := bstep (se 2 (by rfl) ⟨974751, by rfl⟩ : syracuseStep 2599337 = 1949503) B1949503
theorem B63196271 : Blo 1731066 63196271 := bstep (se 1 (by rfl) ⟨47397203, by rfl⟩ : syracuseStep 63196271 = 94794407) B94794407
theorem B4934783 : Blo 1731066 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B19722365 : Blo 1731066 19722365 := bstep (se 3 (by rfl) ⟨3697943, by rfl⟩ : syracuseStep 19722365 = 7395887) B7395887
theorem B3897791 : Blo 1731066 3897791 := bstep (se 1 (by rfl) ⟨2923343, by rfl⟩ : syracuseStep 3897791 = 5846687) B5846687
theorem B2923519 : Blo 1731066 2923519 := bstep (se 1 (by rfl) ⟨2192639, by rfl⟩ : syracuseStep 2923519 = 4385279) B4385279
theorem B5849063 : Blo 1731066 5849063 := bstep (se 1 (by rfl) ⟨4386797, by rfl⟩ : syracuseStep 5849063 = 8773595) B8773595
theorem B13148243 : Blo 1731066 13148243 := bstep (se 1 (by rfl) ⟨9861182, by rfl⟩ : syracuseStep 13148243 = 19722365) B19722365
theorem B2598527 : Blo 1731066 2598527 := bstep (se 1 (by rfl) ⟨1948895, by rfl⟩ : syracuseStep 2598527 = 3897791) B3897791
theorem B1731323 : Blo 1731066 1731323 := bstep (se 1 (by rfl) ⟨1298492, by rfl⟩ : syracuseStep 1731323 = 2596985) B2596985
theorem B13159421 : Blo 1731066 13159421 := bstep (se 3 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 13159421 = 4934783) B4934783
theorem B1732891 : Blo 1731066 1732891 := bstep (se 1 (by rfl) ⟨1299668, by rfl⟩ : syracuseStep 1732891 = 2599337) B2599337
theorem B3898025 : Blo 1731066 3898025 := bstep (se 2 (by rfl) ⟨1461759, by rfl⟩ : syracuseStep 3898025 = 2923519) B2923519
theorem B42130847 : Blo 1731066 42130847 := bstep (se 1 (by rfl) ⟨31598135, by rfl⟩ : syracuseStep 42130847 = 63196271) B63196271
theorem B3899375 : Blo 1731066 3899375 := bstep (se 1 (by rfl) ⟨2924531, by rfl⟩ : syracuseStep 3899375 = 5849063) B5849063
theorem B8765495 : Blo 1731066 8765495 := bstep (se 1 (by rfl) ⟨6574121, by rfl⟩ : syracuseStep 8765495 = 13148243) B13148243
theorem B2598683 : Blo 1731066 2598683 := bstep (se 1 (by rfl) ⟨1949012, by rfl⟩ : syracuseStep 2598683 = 3898025) B3898025
theorem B2599583 : Blo 1731066 2599583 := bstep (se 1 (by rfl) ⟨1949687, by rfl⟩ : syracuseStep 2599583 = 3899375) B3899375
theorem B1732351 : Blo 1731066 1732351 := bstep (se 1 (by rfl) ⟨1299263, by rfl⟩ : syracuseStep 1732351 = 2598527) B2598527
theorem B28087231 : Blo 1731066 28087231 := bstep (se 1 (by rfl) ⟨21065423, by rfl⟩ : syracuseStep 28087231 = 42130847) B42130847
theorem B8772947 : Blo 1731066 8772947 := bstep (se 1 (by rfl) ⟨6579710, by rfl⟩ : syracuseStep 8772947 = 13159421) B13159421
theorem B5843663 : Blo 1731066 5843663 := bstep (se 1 (by rfl) ⟨4382747, by rfl⟩ : syracuseStep 5843663 = 8765495) B8765495
theorem B1732455 : Blo 1731066 1732455 := bstep (se 1 (by rfl) ⟨1299341, by rfl⟩ : syracuseStep 1732455 = 2598683) B2598683
theorem B37449641 : Blo 1731066 37449641 := bstep (se 2 (by rfl) ⟨14043615, by rfl⟩ : syracuseStep 37449641 = 28087231) B28087231
theorem B1733055 : Blo 1731066 1733055 := bstep (se 1 (by rfl) ⟨1299791, by rfl⟩ : syracuseStep 1733055 = 2599583) B2599583
theorem B5848631 : Blo 1731066 5848631 := bstep (se 1 (by rfl) ⟨4386473, by rfl⟩ : syracuseStep 5848631 = 8772947) B8772947
theorem B3895775 : Blo 1731066 3895775 := bstep (se 1 (by rfl) ⟨2921831, by rfl⟩ : syracuseStep 3895775 = 5843663) B5843663
theorem B24966427 : Blo 1731066 24966427 := bstep (se 1 (by rfl) ⟨18724820, by rfl⟩ : syracuseStep 24966427 = 37449641) B37449641
theorem B3899087 : Blo 1731066 3899087 := bstep (se 1 (by rfl) ⟨2924315, by rfl⟩ : syracuseStep 3899087 = 5848631) B5848631
theorem B2597183 : Blo 1731066 2597183 := bstep (se 1 (by rfl) ⟨1947887, by rfl⟩ : syracuseStep 2597183 = 3895775) B3895775
theorem B2599391 : Blo 1731066 2599391 := bstep (se 1 (by rfl) ⟨1949543, by rfl⟩ : syracuseStep 2599391 = 3899087) B3899087
theorem B33288569 : Blo 1731066 33288569 := bstep (se 2 (by rfl) ⟨12483213, by rfl⟩ : syracuseStep 33288569 = 24966427) B24966427
theorem B22192379 : Blo 1731066 22192379 := bstep (se 1 (by rfl) ⟨16644284, by rfl⟩ : syracuseStep 22192379 = 33288569) B33288569
theorem B1731455 : Blo 1731066 1731455 := bstep (se 1 (by rfl) ⟨1298591, by rfl⟩ : syracuseStep 1731455 = 2597183) B2597183
theorem B1732927 : Blo 1731066 1732927 := bstep (se 1 (by rfl) ⟨1299695, by rfl⟩ : syracuseStep 1732927 = 2599391) B2599391
theorem B14794919 : Blo 1731066 14794919 := bstep (se 1 (by rfl) ⟨11096189, by rfl⟩ : syracuseStep 14794919 = 22192379) B22192379
theorem B9863279 : Blo 1731066 9863279 := bstep (se 1 (by rfl) ⟨7397459, by rfl⟩ : syracuseStep 9863279 = 14794919) B14794919
theorem B6575519 : Blo 1731066 6575519 := bstep (se 1 (by rfl) ⟨4931639, by rfl⟩ : syracuseStep 6575519 = 9863279) B9863279
theorem B4383679 : Blo 1731066 4383679 := bstep (se 1 (by rfl) ⟨3287759, by rfl⟩ : syracuseStep 4383679 = 6575519) B6575519
theorem B5844905 : Blo 1731066 5844905 := bstep (se 2 (by rfl) ⟨2191839, by rfl⟩ : syracuseStep 5844905 = 4383679) B4383679
theorem B3896603 : Blo 1731066 3896603 := bstep (se 1 (by rfl) ⟨2922452, by rfl⟩ : syracuseStep 3896603 = 5844905) B5844905
theorem B2597735 : Blo 1731066 2597735 := bstep (se 1 (by rfl) ⟨1948301, by rfl⟩ : syracuseStep 2597735 = 3896603) B3896603
theorem B1731823 : Blo 1731066 1731823 := bstep (se 1 (by rfl) ⟨1298867, by rfl⟩ : syracuseStep 1731823 = 2597735) B2597735

theorem C0 (j : ℕ) (h1 : 432766 ≤ j) (h2 : j ≤ 433265) : Blo 1731066 (4 * j + 3) := by
  interval_cases j
  · exact B1731067
  · exact B1731071
  · exact B1731075
  · exact B1731079
  · exact B1731083
  · exact B1731087
  · exact B1731091
  · exact B1731095
  · exact B1731099
  · exact B1731103
  · exact B1731107
  · exact B1731111
  · exact B1731115
  · exact B1731119
  · exact B1731123
  · exact B1731127
  · exact B1731131
  · exact B1731135
  · exact B1731139
  · exact B1731143
  · exact B1731147
  · exact B1731151
  · exact B1731155
  · exact B1731159
  · exact B1731163
  · exact B1731167
  · exact B1731171
  · exact B1731175
  · exact B1731179
  · exact B1731183
  · exact B1731187
  · exact B1731191
  · exact B1731195
  · exact B1731199
  · exact B1731203
  · exact B1731207
  · exact B1731211
  · exact B1731215
  · exact B1731219
  · exact B1731223
  · exact B1731227
  · exact B1731231
  · exact B1731235
  · exact B1731239
  · exact B1731243
  · exact B1731247
  · exact B1731251
  · exact B1731255
  · exact B1731259
  · exact B1731263
  · exact B1731267
  · exact B1731271
  · exact B1731275
  · exact B1731279
  · exact B1731283
  · exact B1731287
  · exact B1731291
  · exact B1731295
  · exact B1731299
  · exact B1731303
  · exact B1731307
  · exact B1731311
  · exact B1731315
  · exact B1731319
  · exact B1731323
  · exact B1731327
  · exact B1731331
  · exact B1731335
  · exact B1731339
  · exact B1731343
  · exact B1731347
  · exact B1731351
  · exact B1731355
  · exact B1731359
  · exact B1731363
  · exact B1731367
  · exact B1731371
  · exact B1731375
  · exact B1731379
  · exact B1731383
  · exact B1731387
  · exact B1731391
  · exact B1731395
  · exact B1731399
  · exact B1731403
  · exact B1731407
  · exact B1731411
  · exact B1731415
  · exact B1731419
  · exact B1731423
  · exact B1731427
  · exact B1731431
  · exact B1731435
  · exact B1731439
  · exact B1731443
  · exact B1731447
  · exact B1731451
  · exact B1731455
  · exact B1731459
  · exact B1731463
  · exact B1731467
  · exact B1731471
  · exact B1731475
  · exact B1731479
  · exact B1731483
  · exact B1731487
  · exact B1731491
  · exact B1731495
  · exact B1731499
  · exact B1731503
  · exact B1731507
  · exact B1731511
  · exact B1731515
  · exact B1731519
  · exact B1731523
  · exact B1731527
  · exact B1731531
  · exact B1731535
  · exact B1731539
  · exact B1731543
  · exact B1731547
  · exact B1731551
  · exact B1731555
  · exact B1731559
  · exact B1731563
  · exact B1731567
  · exact B1731571
  · exact B1731575
  · exact B1731579
  · exact B1731583
  · exact B1731587
  · exact B1731591
  · exact B1731595
  · exact B1731599
  · exact B1731603
  · exact B1731607
  · exact B1731611
  · exact B1731615
  · exact B1731619
  · exact B1731623
  · exact B1731627
  · exact B1731631
  · exact B1731635
  · exact B1731639
  · exact B1731643
  · exact B1731647
  · exact B1731651
  · exact B1731655
  · exact B1731659
  · exact B1731663
  · exact B1731667
  · exact B1731671
  · exact B1731675
  · exact B1731679
  · exact B1731683
  · exact B1731687
  · exact B1731691
  · exact B1731695
  · exact B1731699
  · exact B1731703
  · exact B1731707
  · exact B1731711
  · exact B1731715
  · exact B1731719
  · exact B1731723
  · exact B1731727
  · exact B1731731
  · exact B1731735
  · exact B1731739
  · exact B1731743
  · exact B1731747
  · exact B1731751
  · exact B1731755
  · exact B1731759
  · exact B1731763
  · exact B1731767
  · exact B1731771
  · exact B1731775
  · exact B1731779
  · exact B1731783
  · exact B1731787
  · exact B1731791
  · exact B1731795
  · exact B1731799
  · exact B1731803
  · exact B1731807
  · exact B1731811
  · exact B1731815
  · exact B1731819
  · exact B1731823
  · exact B1731827
  · exact B1731831
  · exact B1731835
  · exact B1731839
  · exact B1731843
  · exact B1731847
  · exact B1731851
  · exact B1731855
  · exact B1731859
  · exact B1731863
  · exact B1731867
  · exact B1731871
  · exact B1731875
  · exact B1731879
  · exact B1731883
  · exact B1731887
  · exact B1731891
  · exact B1731895
  · exact B1731899
  · exact B1731903
  · exact B1731907
  · exact B1731911
  · exact B1731915
  · exact B1731919
  · exact B1731923
  · exact B1731927
  · exact B1731931
  · exact B1731935
  · exact B1731939
  · exact B1731943
  · exact B1731947
  · exact B1731951
  · exact B1731955
  · exact B1731959
  · exact B1731963
  · exact B1731967
  · exact B1731971
  · exact B1731975
  · exact B1731979
  · exact B1731983
  · exact B1731987
  · exact B1731991
  · exact B1731995
  · exact B1731999
  · exact B1732003
  · exact B1732007
  · exact B1732011
  · exact B1732015
  · exact B1732019
  · exact B1732023
  · exact B1732027
  · exact B1732031
  · exact B1732035
  · exact B1732039
  · exact B1732043
  · exact B1732047
  · exact B1732051
  · exact B1732055
  · exact B1732059
  · exact B1732063
  · exact B1732067
  · exact B1732071
  · exact B1732075
  · exact B1732079
  · exact B1732083
  · exact B1732087
  · exact B1732091
  · exact B1732095
  · exact B1732099
  · exact B1732103
  · exact B1732107
  · exact B1732111
  · exact B1732115
  · exact B1732119
  · exact B1732123
  · exact B1732127
  · exact B1732131
  · exact B1732135
  · exact B1732139
  · exact B1732143
  · exact B1732147
  · exact B1732151
  · exact B1732155
  · exact B1732159
  · exact B1732163
  · exact B1732167
  · exact B1732171
  · exact B1732175
  · exact B1732179
  · exact B1732183
  · exact B1732187
  · exact B1732191
  · exact B1732195
  · exact B1732199
  · exact B1732203
  · exact B1732207
  · exact B1732211
  · exact B1732215
  · exact B1732219
  · exact B1732223
  · exact B1732227
  · exact B1732231
  · exact B1732235
  · exact B1732239
  · exact B1732243
  · exact B1732247
  · exact B1732251
  · exact B1732255
  · exact B1732259
  · exact B1732263
  · exact B1732267
  · exact B1732271
  · exact B1732275
  · exact B1732279
  · exact B1732283
  · exact B1732287
  · exact B1732291
  · exact B1732295
  · exact B1732299
  · exact B1732303
  · exact B1732307
  · exact B1732311
  · exact B1732315
  · exact B1732319
  · exact B1732323
  · exact B1732327
  · exact B1732331
  · exact B1732335
  · exact B1732339
  · exact B1732343
  · exact B1732347
  · exact B1732351
  · exact B1732355
  · exact B1732359
  · exact B1732363
  · exact B1732367
  · exact B1732371
  · exact B1732375
  · exact B1732379
  · exact B1732383
  · exact B1732387
  · exact B1732391
  · exact B1732395
  · exact B1732399
  · exact B1732403
  · exact B1732407
  · exact B1732411
  · exact B1732415
  · exact B1732419
  · exact B1732423
  · exact B1732427
  · exact B1732431
  · exact B1732435
  · exact B1732439
  · exact B1732443
  · exact B1732447
  · exact B1732451
  · exact B1732455
  · exact B1732459
  · exact B1732463
  · exact B1732467
  · exact B1732471
  · exact B1732475
  · exact B1732479
  · exact B1732483
  · exact B1732487
  · exact B1732491
  · exact B1732495
  · exact B1732499
  · exact B1732503
  · exact B1732507
  · exact B1732511
  · exact B1732515
  · exact B1732519
  · exact B1732523
  · exact B1732527
  · exact B1732531
  · exact B1732535
  · exact B1732539
  · exact B1732543
  · exact B1732547
  · exact B1732551
  · exact B1732555
  · exact B1732559
  · exact B1732563
  · exact B1732567
  · exact B1732571
  · exact B1732575
  · exact B1732579
  · exact B1732583
  · exact B1732587
  · exact B1732591
  · exact B1732595
  · exact B1732599
  · exact B1732603
  · exact B1732607
  · exact B1732611
  · exact B1732615
  · exact B1732619
  · exact B1732623
  · exact B1732627
  · exact B1732631
  · exact B1732635
  · exact B1732639
  · exact B1732643
  · exact B1732647
  · exact B1732651
  · exact B1732655
  · exact B1732659
  · exact B1732663
  · exact B1732667
  · exact B1732671
  · exact B1732675
  · exact B1732679
  · exact B1732683
  · exact B1732687
  · exact B1732691
  · exact B1732695
  · exact B1732699
  · exact B1732703
  · exact B1732707
  · exact B1732711
  · exact B1732715
  · exact B1732719
  · exact B1732723
  · exact B1732727
  · exact B1732731
  · exact B1732735
  · exact B1732739
  · exact B1732743
  · exact B1732747
  · exact B1732751
  · exact B1732755
  · exact B1732759
  · exact B1732763
  · exact B1732767
  · exact B1732771
  · exact B1732775
  · exact B1732779
  · exact B1732783
  · exact B1732787
  · exact B1732791
  · exact B1732795
  · exact B1732799
  · exact B1732803
  · exact B1732807
  · exact B1732811
  · exact B1732815
  · exact B1732819
  · exact B1732823
  · exact B1732827
  · exact B1732831
  · exact B1732835
  · exact B1732839
  · exact B1732843
  · exact B1732847
  · exact B1732851
  · exact B1732855
  · exact B1732859
  · exact B1732863
  · exact B1732867
  · exact B1732871
  · exact B1732875
  · exact B1732879
  · exact B1732883
  · exact B1732887
  · exact B1732891
  · exact B1732895
  · exact B1732899
  · exact B1732903
  · exact B1732907
  · exact B1732911
  · exact B1732915
  · exact B1732919
  · exact B1732923
  · exact B1732927
  · exact B1732931
  · exact B1732935
  · exact B1732939
  · exact B1732943
  · exact B1732947
  · exact B1732951
  · exact B1732955
  · exact B1732959
  · exact B1732963
  · exact B1732967
  · exact B1732971
  · exact B1732975
  · exact B1732979
  · exact B1732983
  · exact B1732987
  · exact B1732991
  · exact B1732995
  · exact B1732999
  · exact B1733003
  · exact B1733007
  · exact B1733011
  · exact B1733015
  · exact B1733019
  · exact B1733023
  · exact B1733027
  · exact B1733031
  · exact B1733035
  · exact B1733039
  · exact B1733043
  · exact B1733047
  · exact B1733051
  · exact B1733055
  · exact B1733059
  · exact B1733063

theorem solution (m : ℕ) (hlo : 1731066 ≤ m) (hhi : m ≤ 1733066) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 432766 ≤ j := by omega
    have hj2 : j ≤ 433265 := by omega
    have hb : Blo 1731066 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
