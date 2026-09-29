-- Prove2me | solution 1 for syracuse_descends_range_424774_428774
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:53.529081+00:00
-- url     : https://prove2.me/submissions/57ca9a11-40c5-44b4-b9d0-1a1393075a24

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


theorem B819245 : Blo 424774 819245 := bbase (se 3 (by rfl) ⟨153608, by rfl⟩ : syracuseStep 819245 = 307217) (by norm_num)
theorem B1081421 : Blo 424774 1081421 := bbase (se 3 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 1081421 = 405533) (by norm_num)
theorem B1212533 : Blo 424774 1212533 := bbase (se 5 (by rfl) ⟨56837, by rfl⟩ : syracuseStep 1212533 = 113675) (by norm_num)
theorem B721021 : Blo 424774 721021 := bbase (se 3 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 721021 = 270383) (by norm_num)
theorem B721109 : Blo 424774 721109 := bbase (se 7 (by rfl) ⟨8450, by rfl⟩ : syracuseStep 721109 = 16901) (by norm_num)
theorem B1081613 : Blo 424774 1081613 := bbase (se 3 (by rfl) ⟨202802, by rfl⟩ : syracuseStep 1081613 = 405605) (by norm_num)
theorem B1442069 : Blo 424774 1442069 := bbase (se 6 (by rfl) ⟨33798, by rfl⟩ : syracuseStep 1442069 = 67597) (by norm_num)
theorem B721237 : Blo 424774 721237 := bbase (se 10 (by rfl) ⟨1056, by rfl⟩ : syracuseStep 721237 = 2113) (by norm_num)
theorem B721325 : Blo 424774 721325 := bbase (se 3 (by rfl) ⟨135248, by rfl⟩ : syracuseStep 721325 = 270497) (by norm_num)
theorem B1212965 : Blo 424774 1212965 := bbase (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) (by norm_num)
theorem B721453 : Blo 424774 721453 := bbase (se 3 (by rfl) ⟨135272, by rfl⟩ : syracuseStep 721453 = 270545) (by norm_num)
theorem B1081957 : Blo 424774 1081957 := bbase (se 4 (by rfl) ⟨101433, by rfl⟩ : syracuseStep 1081957 = 202867) (by norm_num)
theorem B721541 : Blo 424774 721541 := bbase (se 4 (by rfl) ⟨67644, by rfl⟩ : syracuseStep 721541 = 135289) (by norm_num)
theorem B1442501 : Blo 424774 1442501 := bbase (se 4 (by rfl) ⟨135234, by rfl⟩ : syracuseStep 1442501 = 270469) (by norm_num)
theorem B1082069 : Blo 424774 1082069 := bbase (se 7 (by rfl) ⟨12680, by rfl⟩ : syracuseStep 1082069 = 25361) (by norm_num)
theorem B721669 : Blo 424774 721669 := bbase (se 4 (by rfl) ⟨67656, by rfl⟩ : syracuseStep 721669 = 135313) (by norm_num)
theorem B2163509 : Blo 424774 2163509 := bbase (se 5 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 2163509 = 202829) (by norm_num)
theorem B721757 : Blo 424774 721757 := bbase (se 3 (by rfl) ⟨135329, by rfl⟩ : syracuseStep 721757 = 270659) (by norm_num)
theorem B1082261 : Blo 424774 1082261 := bbase (se 6 (by rfl) ⟨25365, by rfl⟩ : syracuseStep 1082261 = 50731) (by norm_num)
theorem B721885 : Blo 424774 721885 := bbase (se 3 (by rfl) ⟨135353, by rfl⟩ : syracuseStep 721885 = 270707) (by norm_num)
theorem B721973 : Blo 424774 721973 := bbase (se 5 (by rfl) ⟨33842, by rfl⟩ : syracuseStep 721973 = 67685) (by norm_num)
theorem B459857 : Blo 424774 459857 := bbase (se 2 (by rfl) ⟨172446, by rfl⟩ : syracuseStep 459857 = 344893) (by norm_num)
theorem B4097141 : Blo 424774 4097141 := bbase (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) (by norm_num)
theorem B1442933 : Blo 424774 1442933 := bbase (se 5 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 1442933 = 135275) (by norm_num)
theorem B722101 : Blo 424774 722101 := bbase (se 5 (by rfl) ⟨33848, by rfl⟩ : syracuseStep 722101 = 67697) (by norm_num)
theorem B1082605 : Blo 424774 1082605 := bbase (se 3 (by rfl) ⟨202988, by rfl⟩ : syracuseStep 1082605 = 405977) (by norm_num)
theorem B722189 : Blo 424774 722189 := bbase (se 3 (by rfl) ⟨135410, by rfl⟩ : syracuseStep 722189 = 270821) (by norm_num)
theorem B1213717 : Blo 424774 1213717 := bbase (se 6 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 1213717 = 56893) (by norm_num)
theorem B1082717 : Blo 424774 1082717 := bbase (se 3 (by rfl) ⟨203009, by rfl⟩ : syracuseStep 1082717 = 406019) (by norm_num)
theorem B722317 : Blo 424774 722317 := bbase (se 3 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 722317 = 270869) (by norm_num)
theorem B722405 : Blo 424774 722405 := bbase (se 4 (by rfl) ⟨67725, by rfl⟩ : syracuseStep 722405 = 135451) (by norm_num)
theorem B1082909 : Blo 424774 1082909 := bbase (se 3 (by rfl) ⟨203045, by rfl⟩ : syracuseStep 1082909 = 406091) (by norm_num)
theorem B1443365 : Blo 424774 1443365 := bbase (se 4 (by rfl) ⟨135315, by rfl⟩ : syracuseStep 1443365 = 270631) (by norm_num)
theorem B722533 : Blo 424774 722533 := bbase (se 4 (by rfl) ⟨67737, by rfl⟩ : syracuseStep 722533 = 135475) (by norm_num)
theorem B722621 : Blo 424774 722621 := bbase (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) (by norm_num)
theorem B984797 : Blo 424774 984797 := bbase (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) (by norm_num)
theorem B722749 : Blo 424774 722749 := bbase (se 3 (by rfl) ⟨135515, by rfl⟩ : syracuseStep 722749 = 271031) (by norm_num)
theorem B1083253 : Blo 424774 1083253 := bbase (se 5 (by rfl) ⟨50777, by rfl⟩ : syracuseStep 1083253 = 101555) (by norm_num)
theorem B722837 : Blo 424774 722837 := bbase (se 6 (by rfl) ⟨16941, by rfl⟩ : syracuseStep 722837 = 33883) (by norm_num)
theorem B1443797 : Blo 424774 1443797 := bbase (se 7 (by rfl) ⟨16919, by rfl⟩ : syracuseStep 1443797 = 33839) (by norm_num)
theorem B1083365 : Blo 424774 1083365 := bbase (se 4 (by rfl) ⟨101565, by rfl⟩ : syracuseStep 1083365 = 203131) (by norm_num)
theorem B722965 : Blo 424774 722965 := bbase (se 6 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 722965 = 33889) (by norm_num)
theorem B2164805 : Blo 424774 2164805 := bbase (se 4 (by rfl) ⟨202950, by rfl⟩ : syracuseStep 2164805 = 405901) (by norm_num)
theorem B723053 : Blo 424774 723053 := bbase (se 3 (by rfl) ⟨135572, by rfl⟩ : syracuseStep 723053 = 271145) (by norm_num)
theorem B1083557 : Blo 424774 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B1542341 : Blo 424774 1542341 := bbase (se 4 (by rfl) ⟨144594, by rfl⟩ : syracuseStep 1542341 = 289189) (by norm_num)
theorem B723181 : Blo 424774 723181 := bbase (se 3 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 723181 = 271193) (by norm_num)
theorem B723269 : Blo 424774 723269 := bbase (se 4 (by rfl) ⟨67806, by rfl⟩ : syracuseStep 723269 = 135613) (by norm_num)
theorem B1444229 : Blo 424774 1444229 := bbase (se 4 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 1444229 = 270793) (by norm_num)
theorem B723397 : Blo 424774 723397 := bbase (se 4 (by rfl) ⟨67818, by rfl⟩ : syracuseStep 723397 = 135637) (by norm_num)
theorem B1083901 : Blo 424774 1083901 := bbase (se 3 (by rfl) ⟨203231, by rfl⟩ : syracuseStep 1083901 = 406463) (by norm_num)
theorem B723485 : Blo 424774 723485 := bbase (se 3 (by rfl) ⟨135653, by rfl⟩ : syracuseStep 723485 = 271307) (by norm_num)
theorem B1084013 : Blo 424774 1084013 := bbase (se 3 (by rfl) ⟨203252, by rfl⟩ : syracuseStep 1084013 = 406505) (by norm_num)
theorem B1084205 : Blo 424774 1084205 := bbase (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) (by norm_num)
theorem B1444661 : Blo 424774 1444661 := bbase (se 5 (by rfl) ⟨67718, by rfl⟩ : syracuseStep 1444661 = 135437) (by norm_num)
theorem B461657 : Blo 424774 461657 := bbase (se 2 (by rfl) ⟨173121, by rfl⟩ : syracuseStep 461657 = 346243) (by norm_num)
theorem B3246965 : Blo 424774 3246965 := bbase (se 5 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 3246965 = 304403) (by norm_num)
theorem B1084549 : Blo 424774 1084549 := bbase (se 4 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 1084549 = 203353) (by norm_num)
theorem B2722997 : Blo 424774 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B1445093 : Blo 424774 1445093 := bbase (se 4 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 1445093 = 270955) (by norm_num)
theorem B1084661 : Blo 424774 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B2166101 : Blo 424774 2166101 := bbase (se 11 (by rfl) ⟨1586, by rfl⟩ : syracuseStep 2166101 = 3173) (by norm_num)
theorem B1084853 : Blo 424774 1084853 := bbase (se 5 (by rfl) ⟨50852, by rfl⟩ : syracuseStep 1084853 = 101705) (by norm_num)
theorem B7769557 : Blo 424774 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B1641941 : Blo 424774 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B4918805 : Blo 424774 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1445525 : Blo 424774 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B1085197 : Blo 424774 1085197 := bbase (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) (by norm_num)
theorem B1150757 : Blo 424774 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1085309 : Blo 424774 1085309 := bbase (se 3 (by rfl) ⟨203495, by rfl⟩ : syracuseStep 1085309 = 406991) (by norm_num)
theorem B1216565 : Blo 424774 1216565 := bbase (se 5 (by rfl) ⟨57026, by rfl⟩ : syracuseStep 1216565 = 114053) (by norm_num)
theorem B1445957 : Blo 424774 1445957 := bbase (se 4 (by rfl) ⟨135558, by rfl⟩ : syracuseStep 1445957 = 271117) (by norm_num)
theorem B3117365 : Blo 424774 3117365 := bbase (se 5 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 3117365 = 292253) (by norm_num)
theorem B1446389 : Blo 424774 1446389 := bbase (se 5 (by rfl) ⟨67799, by rfl⟩ : syracuseStep 1446389 = 135599) (by norm_num)
theorem B2167397 : Blo 424774 2167397 := bbase (se 4 (by rfl) ⟨203193, by rfl⟩ : syracuseStep 2167397 = 406387) (by norm_num)
theorem B463493 : Blo 424774 463493 := bbase (se 4 (by rfl) ⟨43452, by rfl⟩ : syracuseStep 463493 = 86905) (by norm_num)
theorem B1151653 : Blo 424774 1151653 := bbase (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) (by norm_num)
theorem B2429621 : Blo 424774 2429621 := bbase (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) (by norm_num)
theorem B1446821 : Blo 424774 1446821 := bbase (se 4 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 1446821 = 271279) (by norm_num)
theorem B463849 : Blo 424774 463849 := bbase (se 2 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 463849 = 347887) (by norm_num)
theorem B693317 : Blo 424774 693317 := bbase (se 4 (by rfl) ⟨64998, by rfl⟩ : syracuseStep 693317 = 129997) (by norm_num)
theorem B1021133 : Blo 424774 1021133 := bbase (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) (by norm_num)
theorem B1217749 : Blo 424774 1217749 := bbase (se 7 (by rfl) ⟨14270, by rfl⟩ : syracuseStep 1217749 = 28541) (by norm_num)
theorem B1217909 : Blo 424774 1217909 := bbase (se 5 (by rfl) ⟨57089, by rfl⟩ : syracuseStep 1217909 = 114179) (by norm_num)
theorem B955781 : Blo 424774 955781 := bbase (se 4 (by rfl) ⟨89604, by rfl⟩ : syracuseStep 955781 = 179209) (by norm_num)
theorem B955853 : Blo 424774 955853 := bbase (se 3 (by rfl) ⟨179222, by rfl⟩ : syracuseStep 955853 = 358445) (by norm_num)
theorem B955925 : Blo 424774 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B955997 : Blo 424774 955997 := bbase (se 3 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 955997 = 358499) (by norm_num)
theorem B1218149 : Blo 424774 1218149 := bbase (se 4 (by rfl) ⟨114201, by rfl⟩ : syracuseStep 1218149 = 228403) (by norm_num)
theorem B956069 : Blo 424774 956069 := bbase (se 4 (by rfl) ⟨89631, by rfl⟩ : syracuseStep 956069 = 179263) (by norm_num)
theorem B431825 : Blo 424774 431825 := bbase (se 2 (by rfl) ⟨161934, by rfl⟩ : syracuseStep 431825 = 323869) (by norm_num)
theorem B956141 : Blo 424774 956141 := bbase (se 3 (by rfl) ⟨179276, by rfl⟩ : syracuseStep 956141 = 358553) (by norm_num)
theorem B1218341 : Blo 424774 1218341 := bbase (se 4 (by rfl) ⟨114219, by rfl⟩ : syracuseStep 1218341 = 228439) (by norm_num)
theorem B956213 : Blo 424774 956213 := bbase (se 5 (by rfl) ⟨44822, by rfl⟩ : syracuseStep 956213 = 89645) (by norm_num)
theorem B2168693 : Blo 424774 2168693 := bbase (se 5 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 2168693 = 203315) (by norm_num)
theorem B956285 : Blo 424774 956285 := bbase (se 3 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 956285 = 358607) (by norm_num)
theorem B4626325 : Blo 424774 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B956357 : Blo 424774 956357 := bbase (se 4 (by rfl) ⟨89658, by rfl⟩ : syracuseStep 956357 = 179317) (by norm_num)
theorem B923653 : Blo 424774 923653 := bbase (se 4 (by rfl) ⟨86592, by rfl⟩ : syracuseStep 923653 = 173185) (by norm_num)
theorem B956429 : Blo 424774 956429 := bbase (se 3 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 956429 = 358661) (by norm_num)
theorem B956501 : Blo 424774 956501 := bbase (se 8 (by rfl) ⟨5604, by rfl⟩ : syracuseStep 956501 = 11209) (by norm_num)
theorem B956573 : Blo 424774 956573 := bbase (se 3 (by rfl) ⟨179357, by rfl⟩ : syracuseStep 956573 = 358715) (by norm_num)
theorem B956645 : Blo 424774 956645 := bbase (se 4 (by rfl) ⟨89685, by rfl⟩ : syracuseStep 956645 = 179371) (by norm_num)
theorem B956717 : Blo 424774 956717 := bbase (se 3 (by rfl) ⟨179384, by rfl⟩ : syracuseStep 956717 = 358769) (by norm_num)
theorem B989525 : Blo 424774 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B956789 : Blo 424774 956789 := bbase (se 5 (by rfl) ⟨44849, by rfl⟩ : syracuseStep 956789 = 89699) (by norm_num)
theorem B956861 : Blo 424774 956861 := bbase (se 3 (by rfl) ⟨179411, by rfl⟩ : syracuseStep 956861 = 358823) (by norm_num)
theorem B956933 : Blo 424774 956933 := bbase (se 4 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 956933 = 179425) (by norm_num)
theorem B957005 : Blo 424774 957005 := bbase (se 3 (by rfl) ⟨179438, by rfl⟩ : syracuseStep 957005 = 358877) (by norm_num)
theorem B957077 : Blo 424774 957077 := bbase (se 6 (by rfl) ⟨22431, by rfl⟩ : syracuseStep 957077 = 44863) (by norm_num)
theorem B957149 : Blo 424774 957149 := bbase (se 3 (by rfl) ⟨179465, by rfl⟩ : syracuseStep 957149 = 358931) (by norm_num)
theorem B1219333 : Blo 424774 1219333 := bbase (se 4 (by rfl) ⟨114312, by rfl⟩ : syracuseStep 1219333 = 228625) (by norm_num)
theorem B4856597 : Blo 424774 4856597 := bbase (se 6 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 4856597 = 227653) (by norm_num)
theorem B957221 : Blo 424774 957221 := bbase (se 4 (by rfl) ⟨89739, by rfl⟩ : syracuseStep 957221 = 179479) (by norm_num)
theorem B957293 : Blo 424774 957293 := bbase (se 3 (by rfl) ⟨179492, by rfl⟩ : syracuseStep 957293 = 358985) (by norm_num)
theorem B2923381 : Blo 424774 2923381 := bbase (se 5 (by rfl) ⟨137033, by rfl⟩ : syracuseStep 2923381 = 274067) (by norm_num)
theorem B957365 : Blo 424774 957365 := bbase (se 5 (by rfl) ⟨44876, by rfl⟩ : syracuseStep 957365 = 89753) (by norm_num)
theorem B957437 : Blo 424774 957437 := bbase (se 3 (by rfl) ⟨179519, by rfl⟩ : syracuseStep 957437 = 359039) (by norm_num)
theorem B1514501 : Blo 424774 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B957509 : Blo 424774 957509 := bbase (se 4 (by rfl) ⟨89766, by rfl⟩ : syracuseStep 957509 = 179533) (by norm_num)
theorem B2169989 : Blo 424774 2169989 := bbase (se 4 (by rfl) ⟨203436, by rfl⟩ : syracuseStep 2169989 = 406873) (by norm_num)
theorem B957581 : Blo 424774 957581 := bbase (se 3 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 957581 = 359093) (by norm_num)
theorem B957653 : Blo 424774 957653 := bbase (se 7 (by rfl) ⟨11222, by rfl⟩ : syracuseStep 957653 = 22445) (by norm_num)
theorem B1252565 : Blo 424774 1252565 := bbase (se 7 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 1252565 = 29357) (by norm_num)
theorem B1187093 : Blo 424774 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B957725 : Blo 424774 957725 := bbase (se 3 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 957725 = 359147) (by norm_num)
theorem B1613141 : Blo 424774 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B957797 : Blo 424774 957797 := bbase (se 4 (by rfl) ⟨89793, by rfl⟩ : syracuseStep 957797 = 179587) (by norm_num)
theorem B957869 : Blo 424774 957869 := bbase (se 3 (by rfl) ⟨179600, by rfl⟩ : syracuseStep 957869 = 359201) (by norm_num)
theorem B957941 : Blo 424774 957941 := bbase (se 5 (by rfl) ⟨44903, by rfl⟩ : syracuseStep 957941 = 89807) (by norm_num)
theorem B1023509 : Blo 424774 1023509 := bbase (se 6 (by rfl) ⟨23988, by rfl⟩ : syracuseStep 1023509 = 47977) (by norm_num)
theorem B958013 : Blo 424774 958013 := bbase (se 3 (by rfl) ⟨179627, by rfl⟩ : syracuseStep 958013 = 359255) (by norm_num)
theorem B1613429 : Blo 424774 1613429 := bbase (se 5 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 1613429 = 151259) (by norm_num)
theorem B958085 : Blo 424774 958085 := bbase (se 4 (by rfl) ⟨89820, by rfl⟩ : syracuseStep 958085 = 179641) (by norm_num)
theorem B958157 : Blo 424774 958157 := bbase (se 3 (by rfl) ⟨179654, by rfl⟩ : syracuseStep 958157 = 359309) (by norm_num)
theorem B958229 : Blo 424774 958229 := bbase (se 6 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 958229 = 44917) (by norm_num)
theorem B1220437 : Blo 424774 1220437 := bbase (se 9 (by rfl) ⟨3575, by rfl⟩ : syracuseStep 1220437 = 7151) (by norm_num)
theorem B958301 : Blo 424774 958301 := bbase (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) (by norm_num)
theorem B1023893 : Blo 424774 1023893 := bbase (se 6 (by rfl) ⟨23997, by rfl⟩ : syracuseStep 1023893 = 47995) (by norm_num)
theorem B958373 : Blo 424774 958373 := bbase (se 4 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 958373 = 179695) (by norm_num)
theorem B958445 : Blo 424774 958445 := bbase (se 3 (by rfl) ⟨179708, by rfl⟩ : syracuseStep 958445 = 359417) (by norm_num)
theorem B7282709 : Blo 424774 7282709 := bbase (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) (by norm_num)
theorem B434197 : Blo 424774 434197 := bbase (se 6 (by rfl) ⟨10176, by rfl⟩ : syracuseStep 434197 = 20353) (by norm_num)
theorem B958517 : Blo 424774 958517 := bbase (se 5 (by rfl) ⟨44930, by rfl⟩ : syracuseStep 958517 = 89861) (by norm_num)
theorem B7610453 : Blo 424774 7610453 := bbase (se 8 (by rfl) ⟨44592, by rfl⟩ : syracuseStep 7610453 = 89185) (by norm_num)
theorem B1024093 : Blo 424774 1024093 := bbase (se 3 (by rfl) ⟨192017, by rfl⟩ : syracuseStep 1024093 = 384035) (by norm_num)
theorem B958589 : Blo 424774 958589 := bbase (se 3 (by rfl) ⟨179735, by rfl⟩ : syracuseStep 958589 = 359471) (by norm_num)
theorem B958661 : Blo 424774 958661 := bbase (se 4 (by rfl) ⟨89874, by rfl⟩ : syracuseStep 958661 = 179749) (by norm_num)
theorem B4923605 : Blo 424774 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B958733 : Blo 424774 958733 := bbase (se 3 (by rfl) ⟨179762, by rfl⟩ : syracuseStep 958733 = 359525) (by norm_num)
theorem B958805 : Blo 424774 958805 := bbase (se 10 (by rfl) ⟨1404, by rfl⟩ : syracuseStep 958805 = 2809) (by norm_num)
theorem B434521 : Blo 424774 434521 := bbase (se 2 (by rfl) ⟨162945, by rfl⟩ : syracuseStep 434521 = 325891) (by norm_num)
theorem B958877 : Blo 424774 958877 := bbase (se 3 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 958877 = 359579) (by norm_num)
theorem B958949 : Blo 424774 958949 := bbase (se 4 (by rfl) ⟨89901, by rfl⟩ : syracuseStep 958949 = 179803) (by norm_num)
theorem B959021 : Blo 424774 959021 := bbase (se 3 (by rfl) ⟨179816, by rfl⟩ : syracuseStep 959021 = 359633) (by norm_num)
theorem B959093 : Blo 424774 959093 := bbase (se 5 (by rfl) ⟨44957, by rfl⟩ : syracuseStep 959093 = 89915) (by norm_num)
theorem B959165 : Blo 424774 959165 := bbase (se 3 (by rfl) ⟨179843, by rfl⟩ : syracuseStep 959165 = 359687) (by norm_num)
theorem B959237 : Blo 424774 959237 := bbase (se 4 (by rfl) ⟨89928, by rfl⟩ : syracuseStep 959237 = 179857) (by norm_num)
theorem B1614613 : Blo 424774 1614613 := bbase (se 6 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 1614613 = 75685) (by norm_num)
theorem B959309 : Blo 424774 959309 := bbase (se 3 (by rfl) ⟨179870, by rfl⟩ : syracuseStep 959309 = 359741) (by norm_num)
theorem B959381 : Blo 424774 959381 := bbase (se 6 (by rfl) ⟨22485, by rfl⟩ : syracuseStep 959381 = 44971) (by norm_num)
theorem B959453 : Blo 424774 959453 := bbase (se 3 (by rfl) ⟨179897, by rfl⟩ : syracuseStep 959453 = 359795) (by norm_num)
theorem B1942501 : Blo 424774 1942501 := bbase (se 4 (by rfl) ⟨182109, by rfl⟩ : syracuseStep 1942501 = 364219) (by norm_num)
theorem B959525 : Blo 424774 959525 := bbase (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) (by norm_num)
theorem B1614917 : Blo 424774 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B959597 : Blo 424774 959597 := bbase (se 3 (by rfl) ⟨179924, by rfl⟩ : syracuseStep 959597 = 359849) (by norm_num)
theorem B959669 : Blo 424774 959669 := bbase (se 5 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 959669 = 89969) (by norm_num)
theorem B1090789 : Blo 424774 1090789 := bbase (se 4 (by rfl) ⟨102261, by rfl⟩ : syracuseStep 1090789 = 204523) (by norm_num)
theorem B959741 : Blo 424774 959741 := bbase (se 3 (by rfl) ⟨179951, by rfl⟩ : syracuseStep 959741 = 359903) (by norm_num)
theorem B959813 : Blo 424774 959813 := bbase (se 4 (by rfl) ⟨89982, by rfl⟩ : syracuseStep 959813 = 179965) (by norm_num)
theorem B959885 : Blo 424774 959885 := bbase (se 3 (by rfl) ⟨179978, by rfl⟩ : syracuseStep 959885 = 359957) (by norm_num)
theorem B959957 : Blo 424774 959957 := bbase (se 7 (by rfl) ⟨11249, by rfl⟩ : syracuseStep 959957 = 22499) (by norm_num)
theorem B2303477 : Blo 424774 2303477 := bbase (se 5 (by rfl) ⟨107975, by rfl⟩ : syracuseStep 2303477 = 215951) (by norm_num)
theorem B960029 : Blo 424774 960029 := bbase (se 3 (by rfl) ⟨180005, by rfl⟩ : syracuseStep 960029 = 360011) (by norm_num)
theorem B960101 : Blo 424774 960101 := bbase (se 4 (by rfl) ⟨90009, by rfl⟩ : syracuseStep 960101 = 180019) (by norm_num)
theorem B1025669 : Blo 424774 1025669 := bbase (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) (by norm_num)
theorem B960173 : Blo 424774 960173 := bbase (se 3 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 960173 = 360065) (by norm_num)
theorem B960245 : Blo 424774 960245 := bbase (se 5 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 960245 = 90023) (by norm_num)
theorem B960317 : Blo 424774 960317 := bbase (se 3 (by rfl) ⟨180059, by rfl⟩ : syracuseStep 960317 = 360119) (by norm_num)
theorem B2074501 : Blo 424774 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B960389 : Blo 424774 960389 := bbase (se 4 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 960389 = 180073) (by norm_num)
theorem B862093 : Blo 424774 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B960461 : Blo 424774 960461 := bbase (se 3 (by rfl) ⟨180086, by rfl⟩ : syracuseStep 960461 = 360173) (by norm_num)
theorem B469009 : Blo 424774 469009 := bbase (se 2 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 469009 = 351757) (by norm_num)
theorem B960533 : Blo 424774 960533 := bbase (se 6 (by rfl) ⟨22512, by rfl⟩ : syracuseStep 960533 = 45025) (by norm_num)
theorem B960605 : Blo 424774 960605 := bbase (se 3 (by rfl) ⟨180113, by rfl⟩ : syracuseStep 960605 = 360227) (by norm_num)
theorem B960677 : Blo 424774 960677 := bbase (se 4 (by rfl) ⟨90063, by rfl⟩ : syracuseStep 960677 = 180127) (by norm_num)
theorem B960749 : Blo 424774 960749 := bbase (se 3 (by rfl) ⟨180140, by rfl⟩ : syracuseStep 960749 = 360281) (by norm_num)
theorem B1943813 : Blo 424774 1943813 := bbase (se 4 (by rfl) ⟨182232, by rfl⟩ : syracuseStep 1943813 = 364465) (by norm_num)
theorem B960821 : Blo 424774 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B3451253 : Blo 424774 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B960893 : Blo 424774 960893 := bbase (se 3 (by rfl) ⟨180167, by rfl⟩ : syracuseStep 960893 = 360335) (by norm_num)
theorem B960965 : Blo 424774 960965 := bbase (se 4 (by rfl) ⟨90090, by rfl⟩ : syracuseStep 960965 = 180181) (by norm_num)
theorem B3254741 : Blo 424774 3254741 := bbase (se 7 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 3254741 = 76283) (by norm_num)
theorem B961037 : Blo 424774 961037 := bbase (se 3 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 961037 = 360389) (by norm_num)
theorem B1878565 : Blo 424774 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B961109 : Blo 424774 961109 := bbase (se 8 (by rfl) ⟨5631, by rfl⟩ : syracuseStep 961109 = 11263) (by norm_num)
theorem B961181 : Blo 424774 961181 := bbase (se 3 (by rfl) ⟨180221, by rfl⟩ : syracuseStep 961181 = 360443) (by norm_num)
theorem B961253 : Blo 424774 961253 := bbase (se 4 (by rfl) ⟨90117, by rfl⟩ : syracuseStep 961253 = 180235) (by norm_num)
theorem B961325 : Blo 424774 961325 := bbase (se 3 (by rfl) ⟨180248, by rfl⟩ : syracuseStep 961325 = 360497) (by norm_num)
theorem B961397 : Blo 424774 961397 := bbase (se 5 (by rfl) ⟨45065, by rfl⟩ : syracuseStep 961397 = 90131) (by norm_num)
theorem B961469 : Blo 424774 961469 := bbase (se 3 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 961469 = 360551) (by norm_num)
theorem B961541 : Blo 424774 961541 := bbase (se 4 (by rfl) ⟨90144, by rfl⟩ : syracuseStep 961541 = 180289) (by norm_num)
theorem B1027093 : Blo 424774 1027093 := bbase (se 6 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 1027093 = 48145) (by norm_num)
theorem B961613 : Blo 424774 961613 := bbase (se 3 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 961613 = 360605) (by norm_num)
theorem B1617029 : Blo 424774 1617029 := bbase (se 4 (by rfl) ⟨151596, by rfl⟩ : syracuseStep 1617029 = 303193) (by norm_num)
theorem B961685 : Blo 424774 961685 := bbase (se 6 (by rfl) ⟨22539, by rfl⟩ : syracuseStep 961685 = 45079) (by norm_num)
theorem B961757 : Blo 424774 961757 := bbase (se 3 (by rfl) ⟨180329, by rfl⟩ : syracuseStep 961757 = 360659) (by norm_num)
theorem B961829 : Blo 424774 961829 := bbase (se 4 (by rfl) ⟨90171, by rfl⟩ : syracuseStep 961829 = 180343) (by norm_num)
theorem B961901 : Blo 424774 961901 := bbase (se 3 (by rfl) ⟨180356, by rfl⟩ : syracuseStep 961901 = 360713) (by norm_num)
theorem B1617317 : Blo 424774 1617317 := bbase (se 4 (by rfl) ⟨151623, by rfl⟩ : syracuseStep 1617317 = 303247) (by norm_num)
theorem B961973 : Blo 424774 961973 := bbase (se 5 (by rfl) ⟨45092, by rfl⟩ : syracuseStep 961973 = 90185) (by norm_num)
theorem B962045 : Blo 424774 962045 := bbase (se 3 (by rfl) ⟨180383, by rfl⟩ : syracuseStep 962045 = 360767) (by norm_num)
theorem B962117 : Blo 424774 962117 := bbase (se 4 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 962117 = 180397) (by norm_num)
theorem B962189 : Blo 424774 962189 := bbase (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) (by norm_num)
theorem B1748645 : Blo 424774 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B1027765 : Blo 424774 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B700093 : Blo 424774 700093 := bbase (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) (by norm_num)
theorem B962261 : Blo 424774 962261 := bbase (se 7 (by rfl) ⟨11276, by rfl⟩ : syracuseStep 962261 = 22553) (by norm_num)
theorem B437981 : Blo 424774 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B765677 : Blo 424774 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B962333 : Blo 424774 962333 := bbase (se 3 (by rfl) ⟨180437, by rfl⟩ : syracuseStep 962333 = 360875) (by norm_num)
theorem B962405 : Blo 424774 962405 := bbase (se 4 (by rfl) ⟨90225, by rfl⟩ : syracuseStep 962405 = 180451) (by norm_num)
theorem B1027997 : Blo 424774 1027997 := bbase (se 3 (by rfl) ⟨192749, by rfl⟩ : syracuseStep 1027997 = 385499) (by norm_num)
theorem B962477 : Blo 424774 962477 := bbase (se 3 (by rfl) ⟨180464, by rfl⟩ : syracuseStep 962477 = 360929) (by norm_num)
theorem B1028045 : Blo 424774 1028045 := bbase (se 3 (by rfl) ⟨192758, by rfl⟩ : syracuseStep 1028045 = 385517) (by norm_num)
theorem B962549 : Blo 424774 962549 := bbase (se 5 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 962549 = 90239) (by norm_num)
theorem B962621 : Blo 424774 962621 := bbase (se 3 (by rfl) ⟨180491, by rfl⟩ : syracuseStep 962621 = 360983) (by norm_num)
theorem B962693 : Blo 424774 962693 := bbase (se 4 (by rfl) ⟨90252, by rfl⟩ : syracuseStep 962693 = 180505) (by norm_num)
theorem B962765 : Blo 424774 962765 := bbase (se 3 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 962765 = 361037) (by norm_num)
theorem B1454357 : Blo 424774 1454357 := bbase (se 6 (by rfl) ⟨34086, by rfl⟩ : syracuseStep 1454357 = 68173) (by norm_num)
theorem B962837 : Blo 424774 962837 := bbase (se 6 (by rfl) ⟨22566, by rfl⟩ : syracuseStep 962837 = 45133) (by norm_num)
theorem B962909 : Blo 424774 962909 := bbase (se 3 (by rfl) ⟨180545, by rfl⟩ : syracuseStep 962909 = 361091) (by norm_num)
theorem B962981 : Blo 424774 962981 := bbase (se 4 (by rfl) ⟨90279, by rfl⟩ : syracuseStep 962981 = 180559) (by norm_num)
theorem B963053 : Blo 424774 963053 := bbase (se 3 (by rfl) ⟨180572, by rfl⟩ : syracuseStep 963053 = 361145) (by norm_num)
theorem B1749509 : Blo 424774 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B2437685 : Blo 424774 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B963125 : Blo 424774 963125 := bbase (se 5 (by rfl) ⟨45146, by rfl⟩ : syracuseStep 963125 = 90293) (by norm_num)
theorem B1618501 : Blo 424774 1618501 := bbase (se 4 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 1618501 = 303469) (by norm_num)
theorem B963197 : Blo 424774 963197 := bbase (se 3 (by rfl) ⟨180599, by rfl⟩ : syracuseStep 963197 = 361199) (by norm_num)
theorem B1389221 : Blo 424774 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B963269 : Blo 424774 963269 := bbase (se 4 (by rfl) ⟨90306, by rfl⟩ : syracuseStep 963269 = 180613) (by norm_num)
theorem B963341 : Blo 424774 963341 := bbase (se 3 (by rfl) ⟨180626, by rfl⟩ : syracuseStep 963341 = 361253) (by norm_num)
theorem B2044709 : Blo 424774 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B963413 : Blo 424774 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B865117 : Blo 424774 865117 := bbase (se 3 (by rfl) ⟨162209, by rfl⟩ : syracuseStep 865117 = 324419) (by norm_num)
theorem B1618805 : Blo 424774 1618805 := bbase (se 5 (by rfl) ⟨75881, by rfl⟩ : syracuseStep 1618805 = 151763) (by norm_num)
theorem B963485 : Blo 424774 963485 := bbase (se 3 (by rfl) ⟨180653, by rfl⟩ : syracuseStep 963485 = 361307) (by norm_num)
theorem B3683285 : Blo 424774 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B963557 : Blo 424774 963557 := bbase (se 4 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 963557 = 180667) (by norm_num)
theorem B1782773 : Blo 424774 1782773 := bbase (se 5 (by rfl) ⟨83567, by rfl⟩ : syracuseStep 1782773 = 167135) (by norm_num)
theorem B537617 : Blo 424774 537617 := bbase (se 2 (by rfl) ⟨201606, by rfl⟩ : syracuseStep 537617 = 403213) (by norm_num)
theorem B766997 : Blo 424774 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B963629 : Blo 424774 963629 := bbase (se 3 (by rfl) ⟨180680, by rfl⟩ : syracuseStep 963629 = 361361) (by norm_num)
theorem B1815605 : Blo 424774 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B537673 : Blo 424774 537673 := bbase (se 2 (by rfl) ⟨201627, by rfl⟩ : syracuseStep 537673 = 403255) (by norm_num)
theorem B963701 : Blo 424774 963701 := bbase (se 5 (by rfl) ⟨45173, by rfl⟩ : syracuseStep 963701 = 90347) (by norm_num)
theorem B537769 : Blo 424774 537769 := bbase (se 2 (by rfl) ⟨201663, by rfl⟩ : syracuseStep 537769 = 403327) (by norm_num)
theorem B963773 : Blo 424774 963773 := bbase (se 3 (by rfl) ⟨180707, by rfl⟩ : syracuseStep 963773 = 361415) (by norm_num)
theorem B963845 : Blo 424774 963845 := bbase (se 4 (by rfl) ⟨90360, by rfl⟩ : syracuseStep 963845 = 180721) (by norm_num)
theorem B1029437 : Blo 424774 1029437 := bbase (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) (by norm_num)
theorem B963917 : Blo 424774 963917 := bbase (se 3 (by rfl) ⟨180734, by rfl⟩ : syracuseStep 963917 = 361469) (by norm_num)
theorem B537941 : Blo 424774 537941 := bbase (se 13 (by rfl) ⟨98, by rfl⟩ : syracuseStep 537941 = 197) (by norm_num)
theorem B865637 : Blo 424774 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B1095029 : Blo 424774 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B537997 : Blo 424774 537997 := bbase (se 3 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 537997 = 201749) (by norm_num)
theorem B963989 : Blo 424774 963989 := bbase (se 6 (by rfl) ⟨22593, by rfl⟩ : syracuseStep 963989 = 45187) (by norm_num)
theorem B865733 : Blo 424774 865733 := bbase (se 4 (by rfl) ⟨81162, by rfl⟩ : syracuseStep 865733 = 162325) (by norm_num)
theorem B964061 : Blo 424774 964061 := bbase (se 3 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 964061 = 361523) (by norm_num)
theorem B538093 : Blo 424774 538093 := bbase (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) (by norm_num)
theorem B1029629 : Blo 424774 1029629 := bbase (se 3 (by rfl) ⟨193055, by rfl⟩ : syracuseStep 1029629 = 386111) (by norm_num)
theorem B964133 : Blo 424774 964133 := bbase (se 4 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 964133 = 180775) (by norm_num)
theorem B964205 : Blo 424774 964205 := bbase (se 3 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 964205 = 361577) (by norm_num)
theorem B538265 : Blo 424774 538265 := bbase (se 2 (by rfl) ⟨201849, by rfl⟩ : syracuseStep 538265 = 403699) (by norm_num)
theorem B964277 : Blo 424774 964277 := bbase (se 5 (by rfl) ⟨45200, by rfl⟩ : syracuseStep 964277 = 90401) (by norm_num)
theorem B538321 : Blo 424774 538321 := bbase (se 2 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 538321 = 403741) (by norm_num)
theorem B2438869 : Blo 424774 2438869 := bbase (se 7 (by rfl) ⟨28580, by rfl⟩ : syracuseStep 2438869 = 57161) (by norm_num)
theorem B964349 : Blo 424774 964349 := bbase (se 3 (by rfl) ⟨180815, by rfl⟩ : syracuseStep 964349 = 361631) (by norm_num)
theorem B538417 : Blo 424774 538417 := bbase (se 2 (by rfl) ⟨201906, by rfl⟩ : syracuseStep 538417 = 403813) (by norm_num)
theorem B1947461 : Blo 424774 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B964421 : Blo 424774 964421 := bbase (se 4 (by rfl) ⟨90414, by rfl⟩ : syracuseStep 964421 = 180829) (by norm_num)
theorem B964493 : Blo 424774 964493 := bbase (se 3 (by rfl) ⟨180842, by rfl⟩ : syracuseStep 964493 = 361685) (by norm_num)
theorem B964565 : Blo 424774 964565 := bbase (se 7 (by rfl) ⟨11303, by rfl⟩ : syracuseStep 964565 = 22607) (by norm_num)
theorem B538589 : Blo 424774 538589 := bbase (se 3 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 538589 = 201971) (by norm_num)
theorem B538645 : Blo 424774 538645 := bbase (se 6 (by rfl) ⟨12624, by rfl⟩ : syracuseStep 538645 = 25249) (by norm_num)
theorem B964637 : Blo 424774 964637 := bbase (se 3 (by rfl) ⟨180869, by rfl⟩ : syracuseStep 964637 = 361739) (by norm_num)
theorem B1816613 : Blo 424774 1816613 := bbase (se 4 (by rfl) ⟨170307, by rfl⟩ : syracuseStep 1816613 = 340615) (by norm_num)
theorem B964709 : Blo 424774 964709 := bbase (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) (by norm_num)
theorem B538741 : Blo 424774 538741 := bbase (se 5 (by rfl) ⟨25253, by rfl⟩ : syracuseStep 538741 = 50507) (by norm_num)
theorem B2308277 : Blo 424774 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B637181 : Blo 424774 637181 := bbase (se 3 (by rfl) ⟨119471, by rfl⟩ : syracuseStep 637181 = 238943) (by norm_num)
theorem B637205 : Blo 424774 637205 := bbase (se 6 (by rfl) ⟨14934, by rfl⟩ : syracuseStep 637205 = 29869) (by norm_num)
theorem B538913 : Blo 424774 538913 := bbase (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) (by norm_num)
theorem B637229 : Blo 424774 637229 := bbase (se 3 (by rfl) ⟨119480, by rfl⟩ : syracuseStep 637229 = 238961) (by norm_num)
theorem B637253 : Blo 424774 637253 := bbase (se 4 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 637253 = 119485) (by norm_num)
theorem B538969 : Blo 424774 538969 := bbase (se 2 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 538969 = 404227) (by norm_num)
theorem B637277 : Blo 424774 637277 := bbase (se 3 (by rfl) ⟨119489, by rfl⟩ : syracuseStep 637277 = 238979) (by norm_num)
theorem B637301 : Blo 424774 637301 := bbase (se 5 (by rfl) ⟨29873, by rfl⟩ : syracuseStep 637301 = 59747) (by norm_num)
theorem B637325 : Blo 424774 637325 := bbase (se 3 (by rfl) ⟨119498, by rfl⟩ : syracuseStep 637325 = 238997) (by norm_num)
theorem B637349 : Blo 424774 637349 := bbase (se 4 (by rfl) ⟨59751, by rfl⟩ : syracuseStep 637349 = 119503) (by norm_num)
theorem B539065 : Blo 424774 539065 := bbase (se 2 (by rfl) ⟨202149, by rfl⟩ : syracuseStep 539065 = 404299) (by norm_num)
theorem B637373 : Blo 424774 637373 := bbase (se 3 (by rfl) ⟨119507, by rfl⟩ : syracuseStep 637373 = 239015) (by norm_num)
theorem B637397 : Blo 424774 637397 := bbase (se 7 (by rfl) ⟨7469, by rfl⟩ : syracuseStep 637397 = 14939) (by norm_num)
theorem B637421 : Blo 424774 637421 := bbase (se 3 (by rfl) ⟨119516, by rfl⟩ : syracuseStep 637421 = 239033) (by norm_num)
theorem B637445 : Blo 424774 637445 := bbase (se 4 (by rfl) ⟨59760, by rfl⟩ : syracuseStep 637445 = 119521) (by norm_num)
theorem B637469 : Blo 424774 637469 := bbase (se 3 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 637469 = 239051) (by norm_num)
theorem B637493 : Blo 424774 637493 := bbase (se 5 (by rfl) ⟨29882, by rfl⟩ : syracuseStep 637493 = 59765) (by norm_num)
theorem B637517 : Blo 424774 637517 := bbase (se 3 (by rfl) ⟨119534, by rfl⟩ : syracuseStep 637517 = 239069) (by norm_num)
theorem B637541 : Blo 424774 637541 := bbase (se 4 (by rfl) ⟨59769, by rfl⟩ : syracuseStep 637541 = 119539) (by norm_num)
theorem B539237 : Blo 424774 539237 := bbase (se 4 (by rfl) ⟨50553, by rfl⟩ : syracuseStep 539237 = 101107) (by norm_num)
theorem B637565 : Blo 424774 637565 := bbase (se 3 (by rfl) ⟨119543, by rfl⟩ : syracuseStep 637565 = 239087) (by norm_num)
theorem B637589 : Blo 424774 637589 := bbase (se 6 (by rfl) ⟨14943, by rfl⟩ : syracuseStep 637589 = 29887) (by norm_num)
theorem B539293 : Blo 424774 539293 := bbase (se 3 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 539293 = 202235) (by norm_num)
theorem B604837 : Blo 424774 604837 := bbase (se 4 (by rfl) ⟨56703, by rfl⟩ : syracuseStep 604837 = 113407) (by norm_num)
theorem B637613 : Blo 424774 637613 := bbase (se 3 (by rfl) ⟨119552, by rfl⟩ : syracuseStep 637613 = 239105) (by norm_num)
theorem B637637 : Blo 424774 637637 := bbase (se 4 (by rfl) ⟨59778, by rfl⟩ : syracuseStep 637637 = 119557) (by norm_num)
theorem B637661 : Blo 424774 637661 := bbase (se 3 (by rfl) ⟨119561, by rfl⟩ : syracuseStep 637661 = 239123) (by norm_num)
theorem B637685 : Blo 424774 637685 := bbase (se 5 (by rfl) ⟨29891, by rfl⟩ : syracuseStep 637685 = 59783) (by norm_num)
theorem B539389 : Blo 424774 539389 := bbase (se 3 (by rfl) ⟨101135, by rfl⟩ : syracuseStep 539389 = 202271) (by norm_num)
theorem B2046725 : Blo 424774 2046725 := bbase (se 4 (by rfl) ⟨191880, by rfl⟩ : syracuseStep 2046725 = 383761) (by norm_num)
theorem B637709 : Blo 424774 637709 := bbase (se 3 (by rfl) ⟨119570, by rfl⟩ : syracuseStep 637709 = 239141) (by norm_num)
theorem B637733 : Blo 424774 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B473897 : Blo 424774 473897 := bbase (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) (by norm_num)
theorem B637757 : Blo 424774 637757 := bbase (se 3 (by rfl) ⟨119579, by rfl⟩ : syracuseStep 637757 = 239159) (by norm_num)
theorem B2308949 : Blo 424774 2308949 := bbase (se 9 (by rfl) ⟨6764, by rfl⟩ : syracuseStep 2308949 = 13529) (by norm_num)
theorem B637781 : Blo 424774 637781 := bbase (se 9 (by rfl) ⟨1868, by rfl⟩ : syracuseStep 637781 = 3737) (by norm_num)
theorem B637805 : Blo 424774 637805 := bbase (se 3 (by rfl) ⟨119588, by rfl⟩ : syracuseStep 637805 = 239177) (by norm_num)
theorem B637829 : Blo 424774 637829 := bbase (se 4 (by rfl) ⟨59796, by rfl⟩ : syracuseStep 637829 = 119593) (by norm_num)
theorem B1096597 : Blo 424774 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B637853 : Blo 424774 637853 := bbase (se 3 (by rfl) ⟨119597, by rfl⟩ : syracuseStep 637853 = 239195) (by norm_num)
theorem B539561 : Blo 424774 539561 := bbase (se 2 (by rfl) ⟨202335, by rfl⟩ : syracuseStep 539561 = 404671) (by norm_num)
theorem B932789 : Blo 424774 932789 := bbase (se 5 (by rfl) ⟨43724, by rfl⟩ : syracuseStep 932789 = 87449) (by norm_num)
theorem B637877 : Blo 424774 637877 := bbase (se 5 (by rfl) ⟨29900, by rfl⟩ : syracuseStep 637877 = 59801) (by norm_num)
theorem B1620917 : Blo 424774 1620917 := bbase (se 5 (by rfl) ⟨75980, by rfl⟩ : syracuseStep 1620917 = 151961) (by norm_num)
theorem B637901 : Blo 424774 637901 := bbase (se 3 (by rfl) ⟨119606, by rfl⟩ : syracuseStep 637901 = 239213) (by norm_num)
theorem B539617 : Blo 424774 539617 := bbase (se 2 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 539617 = 404713) (by norm_num)
theorem B637925 : Blo 424774 637925 := bbase (se 4 (by rfl) ⟨59805, by rfl⟩ : syracuseStep 637925 = 119611) (by norm_num)
theorem B605173 : Blo 424774 605173 := bbase (se 5 (by rfl) ⟨28367, by rfl⟩ : syracuseStep 605173 = 56735) (by norm_num)
theorem B637949 : Blo 424774 637949 := bbase (se 3 (by rfl) ⟨119615, by rfl⟩ : syracuseStep 637949 = 239231) (by norm_num)
theorem B769021 : Blo 424774 769021 := bbase (se 3 (by rfl) ⟨144191, by rfl⟩ : syracuseStep 769021 = 288383) (by norm_num)
theorem B637973 : Blo 424774 637973 := bbase (se 6 (by rfl) ⟨14952, by rfl⟩ : syracuseStep 637973 = 29905) (by norm_num)
theorem B637997 : Blo 424774 637997 := bbase (se 3 (by rfl) ⟨119624, by rfl⟩ : syracuseStep 637997 = 239249) (by norm_num)
theorem B539713 : Blo 424774 539713 := bbase (se 2 (by rfl) ⟨202392, by rfl⟩ : syracuseStep 539713 = 404785) (by norm_num)
theorem B638021 : Blo 424774 638021 := bbase (se 4 (by rfl) ⟨59814, by rfl⟩ : syracuseStep 638021 = 119629) (by norm_num)
theorem B638045 : Blo 424774 638045 := bbase (se 3 (by rfl) ⟨119633, by rfl⟩ : syracuseStep 638045 = 239267) (by norm_num)
theorem B638069 : Blo 424774 638069 := bbase (se 5 (by rfl) ⟨29909, by rfl⟩ : syracuseStep 638069 = 59819) (by norm_num)
theorem B638093 : Blo 424774 638093 := bbase (se 3 (by rfl) ⟨119642, by rfl⟩ : syracuseStep 638093 = 239285) (by norm_num)
theorem B867485 : Blo 424774 867485 := bbase (se 3 (by rfl) ⟨162653, by rfl⟩ : syracuseStep 867485 = 325307) (by norm_num)
theorem B638117 : Blo 424774 638117 := bbase (se 4 (by rfl) ⟨59823, by rfl⟩ : syracuseStep 638117 = 119647) (by norm_num)
theorem B769189 : Blo 424774 769189 := bbase (se 4 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 769189 = 144223) (by norm_num)
theorem B638141 : Blo 424774 638141 := bbase (se 3 (by rfl) ⟨119651, by rfl⟩ : syracuseStep 638141 = 239303) (by norm_num)
theorem B605389 : Blo 424774 605389 := bbase (se 3 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 605389 = 227021) (by norm_num)
theorem B638165 : Blo 424774 638165 := bbase (se 7 (by rfl) ⟨7478, by rfl⟩ : syracuseStep 638165 = 14957) (by norm_num)
theorem B1621205 : Blo 424774 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B638189 : Blo 424774 638189 := bbase (se 3 (by rfl) ⟨119660, by rfl⟩ : syracuseStep 638189 = 239321) (by norm_num)
theorem B539885 : Blo 424774 539885 := bbase (se 3 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 539885 = 202457) (by norm_num)
theorem B638213 : Blo 424774 638213 := bbase (se 4 (by rfl) ⟨59832, by rfl⟩ : syracuseStep 638213 = 119665) (by norm_num)
theorem B638237 : Blo 424774 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B539941 : Blo 424774 539941 := bbase (se 4 (by rfl) ⟨50619, by rfl⟩ : syracuseStep 539941 = 101239) (by norm_num)
theorem B638261 : Blo 424774 638261 := bbase (se 5 (by rfl) ⟨29918, by rfl⟩ : syracuseStep 638261 = 59837) (by norm_num)
theorem B638285 : Blo 424774 638285 := bbase (se 3 (by rfl) ⟨119678, by rfl⟩ : syracuseStep 638285 = 239357) (by norm_num)
theorem B11124053 : Blo 424774 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B638309 : Blo 424774 638309 := bbase (se 4 (by rfl) ⟨59841, by rfl⟩ : syracuseStep 638309 = 119683) (by norm_num)
theorem B638333 : Blo 424774 638333 := bbase (se 3 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 638333 = 239375) (by norm_num)
theorem B540037 : Blo 424774 540037 := bbase (se 4 (by rfl) ⟨50628, by rfl⟩ : syracuseStep 540037 = 101257) (by norm_num)
theorem B638357 : Blo 424774 638357 := bbase (se 6 (by rfl) ⟨14961, by rfl⟩ : syracuseStep 638357 = 29923) (by norm_num)
theorem B638381 : Blo 424774 638381 := bbase (se 3 (by rfl) ⟨119696, by rfl⟩ : syracuseStep 638381 = 239393) (by norm_num)
theorem B638405 : Blo 424774 638405 := bbase (se 4 (by rfl) ⟨59850, by rfl⟩ : syracuseStep 638405 = 119701) (by norm_num)
theorem B638429 : Blo 424774 638429 := bbase (se 3 (by rfl) ⟨119705, by rfl⟩ : syracuseStep 638429 = 239411) (by norm_num)
theorem B638453 : Blo 424774 638453 := bbase (se 5 (by rfl) ⟨29927, by rfl⟩ : syracuseStep 638453 = 59855) (by norm_num)
theorem B2047477 : Blo 424774 2047477 := bbase (se 5 (by rfl) ⟨95975, by rfl⟩ : syracuseStep 2047477 = 191951) (by norm_num)
theorem B638477 : Blo 424774 638477 := bbase (se 3 (by rfl) ⟨119714, by rfl⟩ : syracuseStep 638477 = 239429) (by norm_num)
theorem B638501 : Blo 424774 638501 := bbase (se 4 (by rfl) ⟨59859, by rfl⟩ : syracuseStep 638501 = 119719) (by norm_num)
theorem B540209 : Blo 424774 540209 := bbase (se 2 (by rfl) ⟨202578, by rfl⟩ : syracuseStep 540209 = 405157) (by norm_num)
theorem B638525 : Blo 424774 638525 := bbase (se 3 (by rfl) ⟨119723, by rfl⟩ : syracuseStep 638525 = 239447) (by norm_num)
theorem B605765 : Blo 424774 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B638549 : Blo 424774 638549 := bbase (se 8 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 638549 = 7483) (by norm_num)
theorem B540265 : Blo 424774 540265 := bbase (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) (by norm_num)
theorem B638573 : Blo 424774 638573 := bbase (se 3 (by rfl) ⟨119732, by rfl⟩ : syracuseStep 638573 = 239465) (by norm_num)
theorem B638597 : Blo 424774 638597 := bbase (se 4 (by rfl) ⟨59868, by rfl⟩ : syracuseStep 638597 = 119737) (by norm_num)
theorem B2440853 : Blo 424774 2440853 := bbase (se 6 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 2440853 = 114415) (by norm_num)
theorem B638621 : Blo 424774 638621 := bbase (se 3 (by rfl) ⟨119741, by rfl⟩ : syracuseStep 638621 = 239483) (by norm_num)
theorem B638645 : Blo 424774 638645 := bbase (se 5 (by rfl) ⟨29936, by rfl⟩ : syracuseStep 638645 = 59873) (by norm_num)
theorem B540361 : Blo 424774 540361 := bbase (se 2 (by rfl) ⟨202635, by rfl⟩ : syracuseStep 540361 = 405271) (by norm_num)
theorem B638669 : Blo 424774 638669 := bbase (se 3 (by rfl) ⟨119750, by rfl⟩ : syracuseStep 638669 = 239501) (by norm_num)
theorem B638693 : Blo 424774 638693 := bbase (se 4 (by rfl) ⟨59877, by rfl⟩ : syracuseStep 638693 = 119755) (by norm_num)
theorem B769765 : Blo 424774 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B2244341 : Blo 424774 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B638717 : Blo 424774 638717 := bbase (se 3 (by rfl) ⟨119759, by rfl⟩ : syracuseStep 638717 = 239519) (by norm_num)
theorem B1818389 : Blo 424774 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B638741 : Blo 424774 638741 := bbase (se 6 (by rfl) ⟨14970, by rfl⟩ : syracuseStep 638741 = 29941) (by norm_num)
theorem B638765 : Blo 424774 638765 := bbase (se 3 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 638765 = 239537) (by norm_num)
theorem B638789 : Blo 424774 638789 := bbase (se 4 (by rfl) ⟨59886, by rfl⟩ : syracuseStep 638789 = 119773) (by norm_num)
theorem B638813 : Blo 424774 638813 := bbase (se 3 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 638813 = 239555) (by norm_num)
theorem B638837 : Blo 424774 638837 := bbase (se 5 (by rfl) ⟨29945, by rfl⟩ : syracuseStep 638837 = 59891) (by norm_num)
theorem B540533 : Blo 424774 540533 := bbase (se 5 (by rfl) ⟨25337, by rfl⟩ : syracuseStep 540533 = 50675) (by norm_num)
theorem B638861 : Blo 424774 638861 := bbase (se 3 (by rfl) ⟨119786, by rfl⟩ : syracuseStep 638861 = 239573) (by norm_num)
theorem B638885 : Blo 424774 638885 := bbase (se 4 (by rfl) ⟨59895, by rfl⟩ : syracuseStep 638885 = 119791) (by norm_num)
theorem B540589 : Blo 424774 540589 := bbase (se 3 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 540589 = 202721) (by norm_num)
theorem B638909 : Blo 424774 638909 := bbase (se 3 (by rfl) ⟨119795, by rfl⟩ : syracuseStep 638909 = 239591) (by norm_num)
theorem B638933 : Blo 424774 638933 := bbase (se 7 (by rfl) ⟨7487, by rfl⟩ : syracuseStep 638933 = 14975) (by norm_num)
theorem B638957 : Blo 424774 638957 := bbase (se 3 (by rfl) ⟨119804, by rfl⟩ : syracuseStep 638957 = 239609) (by norm_num)
theorem B638981 : Blo 424774 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B540685 : Blo 424774 540685 := bbase (se 3 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 540685 = 202757) (by norm_num)
theorem B639005 : Blo 424774 639005 := bbase (se 3 (by rfl) ⟨119813, by rfl⟩ : syracuseStep 639005 = 239627) (by norm_num)
theorem B639029 : Blo 424774 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B639053 : Blo 424774 639053 := bbase (se 3 (by rfl) ⟨119822, by rfl⟩ : syracuseStep 639053 = 239645) (by norm_num)
theorem B639077 : Blo 424774 639077 := bbase (se 4 (by rfl) ⟨59913, by rfl⟩ : syracuseStep 639077 = 119827) (by norm_num)
theorem B639101 : Blo 424774 639101 := bbase (se 3 (by rfl) ⟨119831, by rfl⟩ : syracuseStep 639101 = 239663) (by norm_num)
theorem B639125 : Blo 424774 639125 := bbase (se 6 (by rfl) ⟨14979, by rfl⟩ : syracuseStep 639125 = 29959) (by norm_num)
theorem B639149 : Blo 424774 639149 := bbase (se 3 (by rfl) ⟨119840, by rfl⟩ : syracuseStep 639149 = 239681) (by norm_num)
theorem B540857 : Blo 424774 540857 := bbase (se 2 (by rfl) ⟨202821, by rfl⟩ : syracuseStep 540857 = 405643) (by norm_num)
theorem B639173 : Blo 424774 639173 := bbase (se 4 (by rfl) ⟨59922, by rfl⟩ : syracuseStep 639173 = 119845) (by norm_num)
theorem B639197 : Blo 424774 639197 := bbase (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) (by norm_num)
theorem B540913 : Blo 424774 540913 := bbase (se 2 (by rfl) ⟨202842, by rfl⟩ : syracuseStep 540913 = 405685) (by norm_num)
theorem B639221 : Blo 424774 639221 := bbase (se 5 (by rfl) ⟨29963, by rfl⟩ : syracuseStep 639221 = 59927) (by norm_num)
theorem B639245 : Blo 424774 639245 := bbase (se 3 (by rfl) ⟨119858, by rfl⟩ : syracuseStep 639245 = 239717) (by norm_num)
theorem B639269 : Blo 424774 639269 := bbase (se 4 (by rfl) ⟨59931, by rfl⟩ : syracuseStep 639269 = 119863) (by norm_num)
theorem B639293 : Blo 424774 639293 := bbase (se 3 (by rfl) ⟨119867, by rfl⟩ : syracuseStep 639293 = 239735) (by norm_num)
theorem B541009 : Blo 424774 541009 := bbase (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) (by norm_num)
theorem B639317 : Blo 424774 639317 := bbase (se 10 (by rfl) ⟨936, by rfl⟩ : syracuseStep 639317 = 1873) (by norm_num)
theorem B770405 : Blo 424774 770405 := bbase (se 4 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 770405 = 144451) (by norm_num)
theorem B639341 : Blo 424774 639341 := bbase (se 3 (by rfl) ⟨119876, by rfl⟩ : syracuseStep 639341 = 239753) (by norm_num)
theorem B1622389 : Blo 424774 1622389 := bbase (se 5 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 1622389 = 152099) (by norm_num)
theorem B639365 : Blo 424774 639365 := bbase (se 4 (by rfl) ⟨59940, by rfl⟩ : syracuseStep 639365 = 119881) (by norm_num)
theorem B639389 : Blo 424774 639389 := bbase (se 3 (by rfl) ⟨119885, by rfl⟩ : syracuseStep 639389 = 239771) (by norm_num)
theorem B639413 : Blo 424774 639413 := bbase (se 5 (by rfl) ⟨29972, by rfl⟩ : syracuseStep 639413 = 59945) (by norm_num)
theorem B639437 : Blo 424774 639437 := bbase (se 3 (by rfl) ⟨119894, by rfl⟩ : syracuseStep 639437 = 239789) (by norm_num)
theorem B639461 : Blo 424774 639461 := bbase (se 4 (by rfl) ⟨59949, by rfl⟩ : syracuseStep 639461 = 119899) (by norm_num)
theorem B639485 : Blo 424774 639485 := bbase (se 3 (by rfl) ⟨119903, by rfl⟩ : syracuseStep 639485 = 239807) (by norm_num)
theorem B541181 : Blo 424774 541181 := bbase (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) (by norm_num)
theorem B770573 : Blo 424774 770573 := bbase (se 3 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 770573 = 288965) (by norm_num)
theorem B639509 : Blo 424774 639509 := bbase (se 6 (by rfl) ⟨14988, by rfl⟩ : syracuseStep 639509 = 29977) (by norm_num)
theorem B639533 : Blo 424774 639533 := bbase (se 3 (by rfl) ⟨119912, by rfl⟩ : syracuseStep 639533 = 239825) (by norm_num)
theorem B541237 : Blo 424774 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B639557 : Blo 424774 639557 := bbase (se 4 (by rfl) ⟨59958, by rfl⟩ : syracuseStep 639557 = 119917) (by norm_num)
theorem B639581 : Blo 424774 639581 := bbase (se 3 (by rfl) ⟨119921, by rfl⟩ : syracuseStep 639581 = 239843) (by norm_num)
theorem B639605 : Blo 424774 639605 := bbase (se 5 (by rfl) ⟨29981, by rfl⟩ : syracuseStep 639605 = 59963) (by norm_num)
theorem B2736757 : Blo 424774 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B639629 : Blo 424774 639629 := bbase (se 3 (by rfl) ⟨119930, by rfl⟩ : syracuseStep 639629 = 239861) (by norm_num)
theorem B541333 : Blo 424774 541333 := bbase (se 6 (by rfl) ⟨12687, by rfl⟩ : syracuseStep 541333 = 25375) (by norm_num)
theorem B639653 : Blo 424774 639653 := bbase (se 4 (by rfl) ⟨59967, by rfl⟩ : syracuseStep 639653 = 119935) (by norm_num)
theorem B1622693 : Blo 424774 1622693 := bbase (se 4 (by rfl) ⟨152127, by rfl⟩ : syracuseStep 1622693 = 304255) (by norm_num)
theorem B639677 : Blo 424774 639677 := bbase (se 3 (by rfl) ⟨119939, by rfl⟩ : syracuseStep 639677 = 239879) (by norm_num)
theorem B639701 : Blo 424774 639701 := bbase (se 7 (by rfl) ⟨7496, by rfl⟩ : syracuseStep 639701 = 14993) (by norm_num)
theorem B639725 : Blo 424774 639725 := bbase (se 3 (by rfl) ⟨119948, by rfl⟩ : syracuseStep 639725 = 239897) (by norm_num)
theorem B639749 : Blo 424774 639749 := bbase (se 4 (by rfl) ⟨59976, by rfl⟩ : syracuseStep 639749 = 119953) (by norm_num)
theorem B639773 : Blo 424774 639773 := bbase (se 3 (by rfl) ⟨119957, by rfl⟩ : syracuseStep 639773 = 239915) (by norm_num)
theorem B639797 : Blo 424774 639797 := bbase (se 5 (by rfl) ⟨29990, by rfl⟩ : syracuseStep 639797 = 59981) (by norm_num)
theorem B541505 : Blo 424774 541505 := bbase (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) (by norm_num)
theorem B639821 : Blo 424774 639821 := bbase (se 3 (by rfl) ⟨119966, by rfl⟩ : syracuseStep 639821 = 239933) (by norm_num)
theorem B639845 : Blo 424774 639845 := bbase (se 4 (by rfl) ⟨59985, by rfl⟩ : syracuseStep 639845 = 119971) (by norm_num)
theorem B541561 : Blo 424774 541561 := bbase (se 2 (by rfl) ⟨203085, by rfl⟩ : syracuseStep 541561 = 406171) (by norm_num)
theorem B639869 : Blo 424774 639869 := bbase (se 3 (by rfl) ⟨119975, by rfl⟩ : syracuseStep 639869 = 239951) (by norm_num)
theorem B639893 : Blo 424774 639893 := bbase (se 6 (by rfl) ⟨14997, by rfl⟩ : syracuseStep 639893 = 29995) (by norm_num)
theorem B639917 : Blo 424774 639917 := bbase (se 3 (by rfl) ⟨119984, by rfl⟩ : syracuseStep 639917 = 239969) (by norm_num)
theorem B639941 : Blo 424774 639941 := bbase (se 4 (by rfl) ⟨59994, by rfl⟩ : syracuseStep 639941 = 119989) (by norm_num)
theorem B15516629 : Blo 424774 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B607189 : Blo 424774 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B541657 : Blo 424774 541657 := bbase (se 2 (by rfl) ⟨203121, by rfl⟩ : syracuseStep 541657 = 406243) (by norm_num)
theorem B639965 : Blo 424774 639965 := bbase (se 3 (by rfl) ⟨119993, by rfl⟩ : syracuseStep 639965 = 239987) (by norm_num)
theorem B639989 : Blo 424774 639989 := bbase (se 5 (by rfl) ⟨29999, by rfl⟩ : syracuseStep 639989 = 59999) (by norm_num)
theorem B640013 : Blo 424774 640013 := bbase (se 3 (by rfl) ⟨120002, by rfl⟩ : syracuseStep 640013 = 240005) (by norm_num)
theorem B640037 : Blo 424774 640037 := bbase (se 4 (by rfl) ⟨60003, by rfl⟩ : syracuseStep 640037 = 120007) (by norm_num)
theorem B574517 : Blo 424774 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B640061 : Blo 424774 640061 := bbase (se 3 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 640061 = 240023) (by norm_num)
theorem B640085 : Blo 424774 640085 := bbase (se 8 (by rfl) ⟨3750, by rfl⟩ : syracuseStep 640085 = 7501) (by norm_num)
theorem B640109 : Blo 424774 640109 := bbase (se 3 (by rfl) ⟨120020, by rfl⟩ : syracuseStep 640109 = 240041) (by norm_num)
theorem B640133 : Blo 424774 640133 := bbase (se 4 (by rfl) ⟨60012, by rfl⟩ : syracuseStep 640133 = 120025) (by norm_num)
theorem B541829 : Blo 424774 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B640157 : Blo 424774 640157 := bbase (se 3 (by rfl) ⟨120029, by rfl⟩ : syracuseStep 640157 = 240059) (by norm_num)
theorem B2802869 : Blo 424774 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B640181 : Blo 424774 640181 := bbase (se 5 (by rfl) ⟨30008, by rfl⟩ : syracuseStep 640181 = 60017) (by norm_num)
theorem B541885 : Blo 424774 541885 := bbase (se 3 (by rfl) ⟨101603, by rfl⟩ : syracuseStep 541885 = 203207) (by norm_num)
theorem B640205 : Blo 424774 640205 := bbase (se 3 (by rfl) ⟨120038, by rfl⟩ : syracuseStep 640205 = 240077) (by norm_num)
theorem B640229 : Blo 424774 640229 := bbase (se 4 (by rfl) ⟨60021, by rfl⟩ : syracuseStep 640229 = 120043) (by norm_num)
theorem B640253 : Blo 424774 640253 := bbase (se 3 (by rfl) ⟨120047, by rfl⟩ : syracuseStep 640253 = 240095) (by norm_num)
theorem B640277 : Blo 424774 640277 := bbase (se 6 (by rfl) ⟨15006, by rfl⟩ : syracuseStep 640277 = 30013) (by norm_num)
theorem B541981 : Blo 424774 541981 := bbase (se 3 (by rfl) ⟨101621, by rfl⟩ : syracuseStep 541981 = 203243) (by norm_num)
theorem B640301 : Blo 424774 640301 := bbase (se 3 (by rfl) ⟨120056, by rfl⟩ : syracuseStep 640301 = 240113) (by norm_num)
theorem B640325 : Blo 424774 640325 := bbase (se 4 (by rfl) ⟨60030, by rfl⟩ : syracuseStep 640325 = 120061) (by norm_num)
theorem B640349 : Blo 424774 640349 := bbase (se 3 (by rfl) ⟨120065, by rfl⟩ : syracuseStep 640349 = 240131) (by norm_num)
theorem B640373 : Blo 424774 640373 := bbase (se 5 (by rfl) ⟨30017, by rfl⟩ : syracuseStep 640373 = 60035) (by norm_num)
theorem B640397 : Blo 424774 640397 := bbase (se 3 (by rfl) ⟨120074, by rfl⟩ : syracuseStep 640397 = 240149) (by norm_num)
theorem B1099165 : Blo 424774 1099165 := bbase (se 3 (by rfl) ⟨206093, by rfl⟩ : syracuseStep 1099165 = 412187) (by norm_num)
theorem B640421 : Blo 424774 640421 := bbase (se 4 (by rfl) ⟨60039, by rfl⟩ : syracuseStep 640421 = 120079) (by norm_num)
theorem B640445 : Blo 424774 640445 := bbase (se 3 (by rfl) ⟨120083, by rfl⟩ : syracuseStep 640445 = 240167) (by norm_num)
theorem B542153 : Blo 424774 542153 := bbase (se 2 (by rfl) ⟨203307, by rfl⟩ : syracuseStep 542153 = 406615) (by norm_num)
theorem B640469 : Blo 424774 640469 := bbase (se 7 (by rfl) ⟨7505, by rfl⟩ : syracuseStep 640469 = 15011) (by norm_num)
theorem B640493 : Blo 424774 640493 := bbase (se 3 (by rfl) ⟨120092, by rfl⟩ : syracuseStep 640493 = 240185) (by norm_num)
theorem B542209 : Blo 424774 542209 := bbase (se 2 (by rfl) ⟨203328, by rfl⟩ : syracuseStep 542209 = 406657) (by norm_num)
theorem B640517 : Blo 424774 640517 := bbase (se 4 (by rfl) ⟨60048, by rfl⟩ : syracuseStep 640517 = 120097) (by norm_num)
theorem B640541 : Blo 424774 640541 := bbase (se 3 (by rfl) ⟨120101, by rfl⟩ : syracuseStep 640541 = 240203) (by norm_num)
theorem B607781 : Blo 424774 607781 := bbase (se 4 (by rfl) ⟨56979, by rfl⟩ : syracuseStep 607781 = 113959) (by norm_num)
theorem B640565 : Blo 424774 640565 := bbase (se 5 (by rfl) ⟨30026, by rfl⟩ : syracuseStep 640565 = 60053) (by norm_num)
theorem B640589 : Blo 424774 640589 := bbase (se 3 (by rfl) ⟨120110, by rfl⟩ : syracuseStep 640589 = 240221) (by norm_num)
theorem B542305 : Blo 424774 542305 := bbase (se 2 (by rfl) ⟨203364, by rfl⟩ : syracuseStep 542305 = 406729) (by norm_num)
theorem B640613 : Blo 424774 640613 := bbase (se 4 (by rfl) ⟨60057, by rfl⟩ : syracuseStep 640613 = 120115) (by norm_num)
theorem B607861 : Blo 424774 607861 := bbase (se 5 (by rfl) ⟨28493, by rfl⟩ : syracuseStep 607861 = 56987) (by norm_num)
theorem B640637 : Blo 424774 640637 := bbase (se 3 (by rfl) ⟨120119, by rfl⟩ : syracuseStep 640637 = 240239) (by norm_num)
theorem B640661 : Blo 424774 640661 := bbase (se 6 (by rfl) ⟨15015, by rfl⟩ : syracuseStep 640661 = 30031) (by norm_num)
theorem B640685 : Blo 424774 640685 := bbase (se 3 (by rfl) ⟨120128, by rfl⟩ : syracuseStep 640685 = 240257) (by norm_num)
theorem B640709 : Blo 424774 640709 := bbase (se 4 (by rfl) ⟨60066, by rfl⟩ : syracuseStep 640709 = 120133) (by norm_num)
theorem B640733 : Blo 424774 640733 := bbase (se 3 (by rfl) ⟨120137, by rfl⟩ : syracuseStep 640733 = 240275) (by norm_num)
theorem B607981 : Blo 424774 607981 := bbase (se 3 (by rfl) ⟨113996, by rfl⟩ : syracuseStep 607981 = 227993) (by norm_num)
theorem B640757 : Blo 424774 640757 := bbase (se 5 (by rfl) ⟨30035, by rfl⟩ : syracuseStep 640757 = 60071) (by norm_num)
theorem B640781 : Blo 424774 640781 := bbase (se 3 (by rfl) ⟨120146, by rfl⟩ : syracuseStep 640781 = 240293) (by norm_num)
theorem B542477 : Blo 424774 542477 := bbase (se 3 (by rfl) ⟨101714, by rfl⟩ : syracuseStep 542477 = 203429) (by norm_num)
theorem B640805 : Blo 424774 640805 := bbase (se 4 (by rfl) ⟨60075, by rfl⟩ : syracuseStep 640805 = 120151) (by norm_num)
theorem B640829 : Blo 424774 640829 := bbase (se 3 (by rfl) ⟨120155, by rfl⟩ : syracuseStep 640829 = 240311) (by norm_num)
theorem B542533 : Blo 424774 542533 := bbase (se 4 (by rfl) ⟨50862, by rfl⟩ : syracuseStep 542533 = 101725) (by norm_num)
theorem B608077 : Blo 424774 608077 := bbase (se 3 (by rfl) ⟨114014, by rfl⟩ : syracuseStep 608077 = 228029) (by norm_num)
theorem B640853 : Blo 424774 640853 := bbase (se 9 (by rfl) ⟨1877, by rfl⟩ : syracuseStep 640853 = 3755) (by norm_num)
theorem B640877 : Blo 424774 640877 := bbase (se 3 (by rfl) ⟨120164, by rfl⟩ : syracuseStep 640877 = 240329) (by norm_num)
theorem B640901 : Blo 424774 640901 := bbase (se 4 (by rfl) ⟨60084, by rfl⟩ : syracuseStep 640901 = 120169) (by norm_num)
theorem B640925 : Blo 424774 640925 := bbase (se 3 (by rfl) ⟨120173, by rfl⟩ : syracuseStep 640925 = 240347) (by norm_num)
theorem B542629 : Blo 424774 542629 := bbase (se 4 (by rfl) ⟨50871, by rfl⟩ : syracuseStep 542629 = 101743) (by norm_num)
theorem B640949 : Blo 424774 640949 := bbase (se 5 (by rfl) ⟨30044, by rfl⟩ : syracuseStep 640949 = 60089) (by norm_num)
theorem B640973 : Blo 424774 640973 := bbase (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) (by norm_num)
theorem B640997 : Blo 424774 640997 := bbase (se 4 (by rfl) ⟨60093, by rfl⟩ : syracuseStep 640997 = 120187) (by norm_num)
theorem B1361909 : Blo 424774 1361909 := bbase (se 5 (by rfl) ⟨63839, by rfl⟩ : syracuseStep 1361909 = 127679) (by norm_num)
theorem B641021 : Blo 424774 641021 := bbase (se 3 (by rfl) ⟨120191, by rfl⟩ : syracuseStep 641021 = 240383) (by norm_num)
theorem B641045 : Blo 424774 641045 := bbase (se 6 (by rfl) ⟨15024, by rfl⟩ : syracuseStep 641045 = 30049) (by norm_num)
theorem B641069 : Blo 424774 641069 := bbase (se 3 (by rfl) ⟨120200, by rfl⟩ : syracuseStep 641069 = 240401) (by norm_num)
theorem B641093 : Blo 424774 641093 := bbase (se 4 (by rfl) ⟨60102, by rfl⟩ : syracuseStep 641093 = 120205) (by norm_num)
theorem B641117 : Blo 424774 641117 := bbase (se 3 (by rfl) ⟨120209, by rfl⟩ : syracuseStep 641117 = 240419) (by norm_num)
theorem B641141 : Blo 424774 641141 := bbase (se 5 (by rfl) ⟨30053, by rfl⟩ : syracuseStep 641141 = 60107) (by norm_num)
theorem B641165 : Blo 424774 641165 := bbase (se 3 (by rfl) ⟨120218, by rfl⟩ : syracuseStep 641165 = 240437) (by norm_num)
theorem B1230997 : Blo 424774 1230997 := bbase (se 6 (by rfl) ⟨28851, by rfl⟩ : syracuseStep 1230997 = 57703) (by norm_num)
theorem B968861 : Blo 424774 968861 := bbase (se 3 (by rfl) ⟨181661, by rfl⟩ : syracuseStep 968861 = 363323) (by norm_num)
theorem B641189 : Blo 424774 641189 := bbase (se 4 (by rfl) ⟨60111, by rfl⟩ : syracuseStep 641189 = 120223) (by norm_num)
theorem B641213 : Blo 424774 641213 := bbase (se 3 (by rfl) ⟨120227, by rfl⟩ : syracuseStep 641213 = 240455) (by norm_num)
theorem B641237 : Blo 424774 641237 := bbase (se 7 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 641237 = 15029) (by norm_num)
theorem B641261 : Blo 424774 641261 := bbase (se 3 (by rfl) ⟨120236, by rfl⟩ : syracuseStep 641261 = 240473) (by norm_num)
theorem B641285 : Blo 424774 641285 := bbase (se 4 (by rfl) ⟨60120, by rfl⟩ : syracuseStep 641285 = 120241) (by norm_num)
theorem B641309 : Blo 424774 641309 := bbase (se 3 (by rfl) ⟨120245, by rfl⟩ : syracuseStep 641309 = 240491) (by norm_num)
theorem B641333 : Blo 424774 641333 := bbase (se 5 (by rfl) ⟨30062, by rfl⟩ : syracuseStep 641333 = 60125) (by norm_num)
theorem B608573 : Blo 424774 608573 := bbase (se 3 (by rfl) ⟨114107, by rfl⟩ : syracuseStep 608573 = 228215) (by norm_num)
theorem B641357 : Blo 424774 641357 := bbase (se 3 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 641357 = 240509) (by norm_num)
theorem B641381 : Blo 424774 641381 := bbase (se 4 (by rfl) ⟨60129, by rfl⟩ : syracuseStep 641381 = 120259) (by norm_num)
theorem B772453 : Blo 424774 772453 := bbase (se 4 (by rfl) ⟨72417, by rfl⟩ : syracuseStep 772453 = 144835) (by norm_num)
theorem B641405 : Blo 424774 641405 := bbase (se 3 (by rfl) ⟨120263, by rfl⟩ : syracuseStep 641405 = 240527) (by norm_num)
theorem B641429 : Blo 424774 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B641453 : Blo 424774 641453 := bbase (se 3 (by rfl) ⟨120272, by rfl⟩ : syracuseStep 641453 = 240545) (by norm_num)
theorem B3656117 : Blo 424774 3656117 := bbase (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) (by norm_num)
theorem B641477 : Blo 424774 641477 := bbase (se 4 (by rfl) ⟨60138, by rfl⟩ : syracuseStep 641477 = 120277) (by norm_num)
theorem B641501 : Blo 424774 641501 := bbase (se 3 (by rfl) ⟨120281, by rfl⟩ : syracuseStep 641501 = 240563) (by norm_num)
theorem B641525 : Blo 424774 641525 := bbase (se 5 (by rfl) ⟨30071, by rfl⟩ : syracuseStep 641525 = 60143) (by norm_num)
theorem B641549 : Blo 424774 641549 := bbase (se 3 (by rfl) ⟨120290, by rfl⟩ : syracuseStep 641549 = 240581) (by norm_num)
theorem B641573 : Blo 424774 641573 := bbase (se 4 (by rfl) ⟨60147, by rfl⟩ : syracuseStep 641573 = 120295) (by norm_num)
theorem B510509 : Blo 424774 510509 := bbase (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) (by norm_num)
theorem B641597 : Blo 424774 641597 := bbase (se 3 (by rfl) ⟨120299, by rfl⟩ : syracuseStep 641597 = 240599) (by norm_num)
theorem B641621 : Blo 424774 641621 := bbase (se 8 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 641621 = 7519) (by norm_num)
theorem B641645 : Blo 424774 641645 := bbase (se 3 (by rfl) ⟨120308, by rfl⟩ : syracuseStep 641645 = 240617) (by norm_num)
theorem B641669 : Blo 424774 641669 := bbase (se 4 (by rfl) ⟨60156, by rfl⟩ : syracuseStep 641669 = 120313) (by norm_num)
theorem B641693 : Blo 424774 641693 := bbase (se 3 (by rfl) ⟨120317, by rfl⟩ : syracuseStep 641693 = 240635) (by norm_num)
theorem B477877 : Blo 424774 477877 := bbase (se 5 (by rfl) ⟨22400, by rfl⟩ : syracuseStep 477877 = 44801) (by norm_num)
theorem B641717 : Blo 424774 641717 := bbase (se 5 (by rfl) ⟨30080, by rfl⟩ : syracuseStep 641717 = 60161) (by norm_num)
theorem B1297093 : Blo 424774 1297093 := bbase (se 4 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 1297093 = 243205) (by norm_num)
theorem B641741 : Blo 424774 641741 := bbase (se 3 (by rfl) ⟨120326, by rfl⟩ : syracuseStep 641741 = 240653) (by norm_num)
theorem B7785173 : Blo 424774 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B477913 : Blo 424774 477913 := bbase (se 2 (by rfl) ⟨179217, by rfl⟩ : syracuseStep 477913 = 358435) (by norm_num)
theorem B641765 : Blo 424774 641765 := bbase (se 4 (by rfl) ⟨60165, by rfl⟩ : syracuseStep 641765 = 120331) (by norm_num)
theorem B1624805 : Blo 424774 1624805 := bbase (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) (by norm_num)
theorem B477949 : Blo 424774 477949 := bbase (se 3 (by rfl) ⟨89615, by rfl⟩ : syracuseStep 477949 = 179231) (by norm_num)
theorem B641789 : Blo 424774 641789 := bbase (se 3 (by rfl) ⟨120335, by rfl⟩ : syracuseStep 641789 = 240671) (by norm_num)
theorem B641813 : Blo 424774 641813 := bbase (se 6 (by rfl) ⟨15042, by rfl⟩ : syracuseStep 641813 = 30085) (by norm_num)
theorem B477985 : Blo 424774 477985 := bbase (se 2 (by rfl) ⟨179244, by rfl⟩ : syracuseStep 477985 = 358489) (by norm_num)
theorem B641837 : Blo 424774 641837 := bbase (se 3 (by rfl) ⟨120344, by rfl⟩ : syracuseStep 641837 = 240689) (by norm_num)
theorem B478021 : Blo 424774 478021 := bbase (se 4 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 478021 = 89629) (by norm_num)
theorem B641861 : Blo 424774 641861 := bbase (se 4 (by rfl) ⟨60174, by rfl⟩ : syracuseStep 641861 = 120349) (by norm_num)
theorem B641885 : Blo 424774 641885 := bbase (se 3 (by rfl) ⟨120353, by rfl⟩ : syracuseStep 641885 = 240707) (by norm_num)
theorem B609125 : Blo 424774 609125 := bbase (se 4 (by rfl) ⟨57105, by rfl⟩ : syracuseStep 609125 = 114211) (by norm_num)
theorem B478057 : Blo 424774 478057 := bbase (se 2 (by rfl) ⟨179271, by rfl⟩ : syracuseStep 478057 = 358543) (by norm_num)
theorem B641909 : Blo 424774 641909 := bbase (se 5 (by rfl) ⟨30089, by rfl⟩ : syracuseStep 641909 = 60179) (by norm_num)
theorem B478093 : Blo 424774 478093 := bbase (se 3 (by rfl) ⟨89642, by rfl⟩ : syracuseStep 478093 = 179285) (by norm_num)
theorem B641933 : Blo 424774 641933 := bbase (se 3 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 641933 = 240725) (by norm_num)
theorem B641957 : Blo 424774 641957 := bbase (se 4 (by rfl) ⟨60183, by rfl⟩ : syracuseStep 641957 = 120367) (by norm_num)
theorem B478129 : Blo 424774 478129 := bbase (se 2 (by rfl) ⟨179298, by rfl⟩ : syracuseStep 478129 = 358597) (by norm_num)
theorem B641981 : Blo 424774 641981 := bbase (se 3 (by rfl) ⟨120371, by rfl⟩ : syracuseStep 641981 = 240743) (by norm_num)
theorem B478165 : Blo 424774 478165 := bbase (se 7 (by rfl) ⟨5603, by rfl⟩ : syracuseStep 478165 = 11207) (by norm_num)
theorem B642005 : Blo 424774 642005 := bbase (se 7 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 642005 = 15047) (by norm_num)
theorem B642029 : Blo 424774 642029 := bbase (se 3 (by rfl) ⟨120380, by rfl⟩ : syracuseStep 642029 = 240761) (by norm_num)
theorem B478201 : Blo 424774 478201 := bbase (se 2 (by rfl) ⟨179325, by rfl⟩ : syracuseStep 478201 = 358651) (by norm_num)
theorem B1625093 : Blo 424774 1625093 := bbase (se 4 (by rfl) ⟨152352, by rfl⟩ : syracuseStep 1625093 = 304705) (by norm_num)
theorem B642053 : Blo 424774 642053 := bbase (se 4 (by rfl) ⟨60192, by rfl⟩ : syracuseStep 642053 = 120385) (by norm_num)
theorem B478237 : Blo 424774 478237 := bbase (se 3 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 478237 = 179339) (by norm_num)
theorem B642077 : Blo 424774 642077 := bbase (se 3 (by rfl) ⟨120389, by rfl⟩ : syracuseStep 642077 = 240779) (by norm_num)
theorem B1362997 : Blo 424774 1362997 := bbase (se 5 (by rfl) ⟨63890, by rfl⟩ : syracuseStep 1362997 = 127781) (by norm_num)
theorem B642101 : Blo 424774 642101 := bbase (se 5 (by rfl) ⟨30098, by rfl⟩ : syracuseStep 642101 = 60197) (by norm_num)
theorem B478273 : Blo 424774 478273 := bbase (se 2 (by rfl) ⟨179352, by rfl⟩ : syracuseStep 478273 = 358705) (by norm_num)
theorem B642125 : Blo 424774 642125 := bbase (se 3 (by rfl) ⟨120398, by rfl⟩ : syracuseStep 642125 = 240797) (by norm_num)
theorem B478309 : Blo 424774 478309 := bbase (se 4 (by rfl) ⟨44841, by rfl⟩ : syracuseStep 478309 = 89683) (by norm_num)
theorem B642149 : Blo 424774 642149 := bbase (se 4 (by rfl) ⟨60201, by rfl⟩ : syracuseStep 642149 = 120403) (by norm_num)
theorem B1461365 : Blo 424774 1461365 := bbase (se 5 (by rfl) ⟨68501, by rfl⟩ : syracuseStep 1461365 = 137003) (by norm_num)
theorem B642173 : Blo 424774 642173 := bbase (se 3 (by rfl) ⟨120407, by rfl⟩ : syracuseStep 642173 = 240815) (by norm_num)
theorem B511105 : Blo 424774 511105 := bbase (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) (by norm_num)
theorem B2182277 : Blo 424774 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B478345 : Blo 424774 478345 := bbase (se 2 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 478345 = 358759) (by norm_num)
theorem B642197 : Blo 424774 642197 := bbase (se 6 (by rfl) ⟨15051, by rfl⟩ : syracuseStep 642197 = 30103) (by norm_num)
theorem B478381 : Blo 424774 478381 := bbase (se 3 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 478381 = 179393) (by norm_num)
theorem B642221 : Blo 424774 642221 := bbase (se 3 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 642221 = 240833) (by norm_num)
theorem B642245 : Blo 424774 642245 := bbase (se 4 (by rfl) ⟨60210, by rfl⟩ : syracuseStep 642245 = 120421) (by norm_num)
theorem B478417 : Blo 424774 478417 := bbase (se 2 (by rfl) ⟨179406, by rfl⟩ : syracuseStep 478417 = 358813) (by norm_num)
theorem B642269 : Blo 424774 642269 := bbase (se 3 (by rfl) ⟨120425, by rfl⟩ : syracuseStep 642269 = 240851) (by norm_num)
theorem B511201 : Blo 424774 511201 := bbase (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) (by norm_num)
theorem B478453 : Blo 424774 478453 := bbase (se 5 (by rfl) ⟨22427, by rfl⟩ : syracuseStep 478453 = 44855) (by norm_num)
theorem B642293 : Blo 424774 642293 := bbase (se 5 (by rfl) ⟨30107, by rfl⟩ : syracuseStep 642293 = 60215) (by norm_num)
theorem B642317 : Blo 424774 642317 := bbase (se 3 (by rfl) ⟨120434, by rfl⟩ : syracuseStep 642317 = 240869) (by norm_num)
theorem B478489 : Blo 424774 478489 := bbase (se 2 (by rfl) ⟨179433, by rfl⟩ : syracuseStep 478489 = 358867) (by norm_num)
theorem B642341 : Blo 424774 642341 := bbase (se 4 (by rfl) ⟨60219, by rfl⟩ : syracuseStep 642341 = 120439) (by norm_num)
theorem B478525 : Blo 424774 478525 := bbase (se 3 (by rfl) ⟨89723, by rfl⟩ : syracuseStep 478525 = 179447) (by norm_num)
theorem B642365 : Blo 424774 642365 := bbase (se 3 (by rfl) ⟨120443, by rfl⟩ : syracuseStep 642365 = 240887) (by norm_num)
theorem B1035605 : Blo 424774 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B642389 : Blo 424774 642389 := bbase (se 11 (by rfl) ⟨470, by rfl⟩ : syracuseStep 642389 = 941) (by norm_num)
theorem B478561 : Blo 424774 478561 := bbase (se 2 (by rfl) ⟨179460, by rfl⟩ : syracuseStep 478561 = 358921) (by norm_num)
theorem B642413 : Blo 424774 642413 := bbase (se 3 (by rfl) ⟨120452, by rfl⟩ : syracuseStep 642413 = 240905) (by norm_num)
theorem B478597 : Blo 424774 478597 := bbase (se 4 (by rfl) ⟨44868, by rfl⟩ : syracuseStep 478597 = 89737) (by norm_num)
theorem B642437 : Blo 424774 642437 := bbase (se 4 (by rfl) ⟨60228, by rfl⟩ : syracuseStep 642437 = 120457) (by norm_num)
theorem B642461 : Blo 424774 642461 := bbase (se 3 (by rfl) ⟨120461, by rfl⟩ : syracuseStep 642461 = 240923) (by norm_num)
theorem B2182565 : Blo 424774 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B478633 : Blo 424774 478633 := bbase (se 2 (by rfl) ⟨179487, by rfl⟩ : syracuseStep 478633 = 358975) (by norm_num)
theorem B642485 : Blo 424774 642485 := bbase (se 5 (by rfl) ⟨30116, by rfl⟩ : syracuseStep 642485 = 60233) (by norm_num)
theorem B478669 : Blo 424774 478669 := bbase (se 3 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 478669 = 179501) (by norm_num)
theorem B642509 : Blo 424774 642509 := bbase (se 3 (by rfl) ⟨120470, by rfl⟩ : syracuseStep 642509 = 240941) (by norm_num)
theorem B642533 : Blo 424774 642533 := bbase (se 4 (by rfl) ⟨60237, by rfl⟩ : syracuseStep 642533 = 120475) (by norm_num)
theorem B478705 : Blo 424774 478705 := bbase (se 2 (by rfl) ⟨179514, by rfl⟩ : syracuseStep 478705 = 359029) (by norm_num)
theorem B642557 : Blo 424774 642557 := bbase (se 3 (by rfl) ⟨120479, by rfl⟩ : syracuseStep 642557 = 240959) (by norm_num)
theorem B478741 : Blo 424774 478741 := bbase (se 6 (by rfl) ⟨11220, by rfl⟩ : syracuseStep 478741 = 22441) (by norm_num)
theorem B642581 : Blo 424774 642581 := bbase (se 6 (by rfl) ⟨15060, by rfl⟩ : syracuseStep 642581 = 30121) (by norm_num)
theorem B642605 : Blo 424774 642605 := bbase (se 3 (by rfl) ⟨120488, by rfl⟩ : syracuseStep 642605 = 240977) (by norm_num)
theorem B478777 : Blo 424774 478777 := bbase (se 2 (by rfl) ⟨179541, by rfl⟩ : syracuseStep 478777 = 359083) (by norm_num)
theorem B642629 : Blo 424774 642629 := bbase (se 4 (by rfl) ⟨60246, by rfl⟩ : syracuseStep 642629 = 120493) (by norm_num)
theorem B609877 : Blo 424774 609877 := bbase (se 8 (by rfl) ⟨3573, by rfl⟩ : syracuseStep 609877 = 7147) (by norm_num)
theorem B478813 : Blo 424774 478813 := bbase (se 3 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 478813 = 179555) (by norm_num)
theorem B642653 : Blo 424774 642653 := bbase (se 3 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 642653 = 240995) (by norm_num)
theorem B642677 : Blo 424774 642677 := bbase (se 5 (by rfl) ⟨30125, by rfl⟩ : syracuseStep 642677 = 60251) (by norm_num)
theorem B478849 : Blo 424774 478849 := bbase (se 2 (by rfl) ⟨179568, by rfl⟩ : syracuseStep 478849 = 359137) (by norm_num)
theorem B642701 : Blo 424774 642701 := bbase (se 3 (by rfl) ⟨120506, by rfl⟩ : syracuseStep 642701 = 241013) (by norm_num)
theorem B478885 : Blo 424774 478885 := bbase (se 4 (by rfl) ⟨44895, by rfl⟩ : syracuseStep 478885 = 89791) (by norm_num)
theorem B642725 : Blo 424774 642725 := bbase (se 4 (by rfl) ⟨60255, by rfl⟩ : syracuseStep 642725 = 120511) (by norm_num)
theorem B3231413 : Blo 424774 3231413 := bbase (se 5 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 3231413 = 302945) (by norm_num)
theorem B642749 : Blo 424774 642749 := bbase (se 3 (by rfl) ⟨120515, by rfl⟩ : syracuseStep 642749 = 241031) (by norm_num)
theorem B478921 : Blo 424774 478921 := bbase (se 2 (by rfl) ⟨179595, by rfl⟩ : syracuseStep 478921 = 359191) (by norm_num)
theorem B642773 : Blo 424774 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B577253 : Blo 424774 577253 := bbase (se 4 (by rfl) ⟨54117, by rfl⟩ : syracuseStep 577253 = 108235) (by norm_num)
theorem B478957 : Blo 424774 478957 := bbase (se 3 (by rfl) ⟨89804, by rfl⟩ : syracuseStep 478957 = 179609) (by norm_num)
theorem B642797 : Blo 424774 642797 := bbase (se 3 (by rfl) ⟨120524, by rfl⟩ : syracuseStep 642797 = 241049) (by norm_num)
theorem B642821 : Blo 424774 642821 := bbase (se 4 (by rfl) ⟨60264, by rfl⟩ : syracuseStep 642821 = 120529) (by norm_num)
theorem B806669 : Blo 424774 806669 := bbase (se 3 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 806669 = 302501) (by norm_num)
theorem B478993 : Blo 424774 478993 := bbase (se 2 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 478993 = 359245) (by norm_num)
theorem B642845 : Blo 424774 642845 := bbase (se 3 (by rfl) ⟨120533, by rfl⟩ : syracuseStep 642845 = 241067) (by norm_num)
theorem B1298213 : Blo 424774 1298213 := bbase (se 4 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 1298213 = 243415) (by norm_num)
theorem B479029 : Blo 424774 479029 := bbase (se 5 (by rfl) ⟨22454, by rfl⟩ : syracuseStep 479029 = 44909) (by norm_num)
theorem B642869 : Blo 424774 642869 := bbase (se 5 (by rfl) ⟨30134, by rfl⟩ : syracuseStep 642869 = 60269) (by norm_num)
theorem B642893 : Blo 424774 642893 := bbase (se 3 (by rfl) ⟨120542, by rfl⟩ : syracuseStep 642893 = 241085) (by norm_num)
theorem B479065 : Blo 424774 479065 := bbase (se 2 (by rfl) ⟨179649, by rfl⟩ : syracuseStep 479065 = 359299) (by norm_num)
theorem B642917 : Blo 424774 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B970613 : Blo 424774 970613 := bbase (se 5 (by rfl) ⟨45497, by rfl⟩ : syracuseStep 970613 = 90995) (by norm_num)
theorem B479101 : Blo 424774 479101 := bbase (se 3 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 479101 = 179663) (by norm_num)
theorem B642941 : Blo 424774 642941 := bbase (se 3 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 642941 = 241103) (by norm_num)
theorem B642965 : Blo 424774 642965 := bbase (se 6 (by rfl) ⟨15069, by rfl⟩ : syracuseStep 642965 = 30139) (by norm_num)
theorem B479137 : Blo 424774 479137 := bbase (se 2 (by rfl) ⟨179676, by rfl⟩ : syracuseStep 479137 = 359353) (by norm_num)
theorem B642989 : Blo 424774 642989 := bbase (se 3 (by rfl) ⟨120560, by rfl⟩ : syracuseStep 642989 = 241121) (by norm_num)
theorem B479173 : Blo 424774 479173 := bbase (se 4 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 479173 = 89845) (by norm_num)
theorem B1822661 : Blo 424774 1822661 := bbase (se 4 (by rfl) ⟨170874, by rfl⟩ : syracuseStep 1822661 = 341749) (by norm_num)
theorem B643013 : Blo 424774 643013 := bbase (se 4 (by rfl) ⟨60282, by rfl⟩ : syracuseStep 643013 = 120565) (by norm_num)
theorem B643037 : Blo 424774 643037 := bbase (se 3 (by rfl) ⟨120569, by rfl⟩ : syracuseStep 643037 = 241139) (by norm_num)
theorem B479209 : Blo 424774 479209 := bbase (se 2 (by rfl) ⟨179703, by rfl⟩ : syracuseStep 479209 = 359407) (by norm_num)
theorem B643061 : Blo 424774 643061 := bbase (se 5 (by rfl) ⟨30143, by rfl⟩ : syracuseStep 643061 = 60287) (by norm_num)
theorem B479245 : Blo 424774 479245 := bbase (se 3 (by rfl) ⟨89858, by rfl⟩ : syracuseStep 479245 = 179717) (by norm_num)
theorem B643085 : Blo 424774 643085 := bbase (se 3 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 643085 = 241157) (by norm_num)
theorem B643109 : Blo 424774 643109 := bbase (se 4 (by rfl) ⟨60291, by rfl⟩ : syracuseStep 643109 = 120583) (by norm_num)
theorem B479281 : Blo 424774 479281 := bbase (se 2 (by rfl) ⟨179730, by rfl⟩ : syracuseStep 479281 = 359461) (by norm_num)
theorem B643133 : Blo 424774 643133 := bbase (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) (by norm_num)
theorem B479317 : Blo 424774 479317 := bbase (se 8 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 479317 = 5617) (by norm_num)
theorem B643157 : Blo 424774 643157 := bbase (se 8 (by rfl) ⟨3768, by rfl⟩ : syracuseStep 643157 = 7537) (by norm_num)
theorem B479353 : Blo 424774 479353 := bbase (se 2 (by rfl) ⟨179757, by rfl⟩ : syracuseStep 479353 = 359515) (by norm_num)
theorem B2150549 : Blo 424774 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B479389 : Blo 424774 479389 := bbase (se 3 (by rfl) ⟨89885, by rfl⟩ : syracuseStep 479389 = 179771) (by norm_num)
theorem B1626277 : Blo 424774 1626277 := bbase (se 4 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 1626277 = 304927) (by norm_num)
theorem B479425 : Blo 424774 479425 := bbase (se 2 (by rfl) ⟨179784, by rfl⟩ : syracuseStep 479425 = 359569) (by norm_num)
theorem B1364165 : Blo 424774 1364165 := bbase (se 4 (by rfl) ⟨127890, by rfl⟩ : syracuseStep 1364165 = 255781) (by norm_num)
theorem B479461 : Blo 424774 479461 := bbase (se 4 (by rfl) ⟨44949, by rfl⟩ : syracuseStep 479461 = 89899) (by norm_num)
theorem B479497 : Blo 424774 479497 := bbase (se 2 (by rfl) ⟨179811, by rfl⟩ : syracuseStep 479497 = 359623) (by norm_num)
theorem B479533 : Blo 424774 479533 := bbase (se 3 (by rfl) ⟨89912, by rfl⟩ : syracuseStep 479533 = 179825) (by norm_num)
theorem B479569 : Blo 424774 479569 := bbase (se 2 (by rfl) ⟨179838, by rfl⟩ : syracuseStep 479569 = 359677) (by norm_num)
theorem B708949 : Blo 424774 708949 := bbase (se 10 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 708949 = 2077) (by norm_num)
theorem B512345 : Blo 424774 512345 := bbase (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) (by norm_num)
theorem B479605 : Blo 424774 479605 := bbase (se 5 (by rfl) ⟨22481, by rfl⟩ : syracuseStep 479605 = 44963) (by norm_num)
theorem B479641 : Blo 424774 479641 := bbase (se 2 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 479641 = 359731) (by norm_num)
theorem B479677 : Blo 424774 479677 := bbase (se 3 (by rfl) ⟨89939, by rfl⟩ : syracuseStep 479677 = 179879) (by norm_num)
theorem B1626581 : Blo 424774 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B479713 : Blo 424774 479713 := bbase (se 2 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 479713 = 359785) (by norm_num)
theorem B807421 : Blo 424774 807421 := bbase (se 3 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 807421 = 302783) (by norm_num)
theorem B479749 : Blo 424774 479749 := bbase (se 4 (by rfl) ⟨44976, by rfl⟩ : syracuseStep 479749 = 89953) (by norm_num)
theorem B479785 : Blo 424774 479785 := bbase (se 2 (by rfl) ⟨179919, by rfl⟩ : syracuseStep 479785 = 359839) (by norm_num)
theorem B479821 : Blo 424774 479821 := bbase (se 3 (by rfl) ⟨89966, by rfl⟩ : syracuseStep 479821 = 179933) (by norm_num)
theorem B479857 : Blo 424774 479857 := bbase (se 2 (by rfl) ⟨179946, by rfl⟩ : syracuseStep 479857 = 359893) (by norm_num)
theorem B807565 : Blo 424774 807565 := bbase (se 3 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 807565 = 302837) (by norm_num)
theorem B479893 : Blo 424774 479893 := bbase (se 6 (by rfl) ⟨11247, by rfl⟩ : syracuseStep 479893 = 22495) (by norm_num)
theorem B512677 : Blo 424774 512677 := bbase (se 4 (by rfl) ⟨48063, by rfl⟩ : syracuseStep 512677 = 96127) (by norm_num)
theorem B1954469 : Blo 424774 1954469 := bbase (se 4 (by rfl) ⟨183231, by rfl⟩ : syracuseStep 1954469 = 366463) (by norm_num)
theorem B479929 : Blo 424774 479929 := bbase (se 2 (by rfl) ⟨179973, by rfl⟩ : syracuseStep 479929 = 359947) (by norm_num)
theorem B479965 : Blo 424774 479965 := bbase (se 3 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 479965 = 179987) (by norm_num)
theorem B480001 : Blo 424774 480001 := bbase (se 2 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 480001 = 360001) (by norm_num)
theorem B480037 : Blo 424774 480037 := bbase (se 4 (by rfl) ⟨45003, by rfl⟩ : syracuseStep 480037 = 90007) (by norm_num)
theorem B807725 : Blo 424774 807725 := bbase (se 3 (by rfl) ⟨151448, by rfl⟩ : syracuseStep 807725 = 302897) (by norm_num)
theorem B480073 : Blo 424774 480073 := bbase (se 2 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 480073 = 360055) (by norm_num)
theorem B480109 : Blo 424774 480109 := bbase (se 3 (by rfl) ⟨90020, by rfl⟩ : syracuseStep 480109 = 180041) (by norm_num)
theorem B480145 : Blo 424774 480145 := bbase (se 2 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 480145 = 360109) (by norm_num)
theorem B480181 : Blo 424774 480181 := bbase (se 5 (by rfl) ⟨22508, by rfl⟩ : syracuseStep 480181 = 45017) (by norm_num)
theorem B807869 : Blo 424774 807869 := bbase (se 3 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 807869 = 302951) (by norm_num)
theorem B545753 : Blo 424774 545753 := bbase (se 2 (by rfl) ⟨204657, by rfl⟩ : syracuseStep 545753 = 409315) (by norm_num)
theorem B480217 : Blo 424774 480217 := bbase (se 2 (by rfl) ⟨180081, by rfl⟩ : syracuseStep 480217 = 360163) (by norm_num)
theorem B480253 : Blo 424774 480253 := bbase (se 3 (by rfl) ⟨90047, by rfl⟩ : syracuseStep 480253 = 180095) (by norm_num)
theorem B480289 : Blo 424774 480289 := bbase (se 2 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 480289 = 360217) (by norm_num)
theorem B578621 : Blo 424774 578621 := bbase (se 3 (by rfl) ⟨108491, by rfl⟩ : syracuseStep 578621 = 216983) (by norm_num)
theorem B480325 : Blo 424774 480325 := bbase (se 4 (by rfl) ⟨45030, by rfl⟩ : syracuseStep 480325 = 90061) (by norm_num)
theorem B480361 : Blo 424774 480361 := bbase (se 2 (by rfl) ⟨180135, by rfl⟩ : syracuseStep 480361 = 360271) (by norm_num)
theorem B578669 : Blo 424774 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B480397 : Blo 424774 480397 := bbase (se 3 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 480397 = 180149) (by norm_num)
theorem B480433 : Blo 424774 480433 := bbase (se 2 (by rfl) ⟨180162, by rfl⟩ : syracuseStep 480433 = 360325) (by norm_num)
theorem B480469 : Blo 424774 480469 := bbase (se 7 (by rfl) ⟨5630, by rfl⟩ : syracuseStep 480469 = 11261) (by norm_num)
theorem B808157 : Blo 424774 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B480505 : Blo 424774 480505 := bbase (se 2 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 480505 = 360379) (by norm_num)
theorem B480541 : Blo 424774 480541 := bbase (se 3 (by rfl) ⟨90101, by rfl⟩ : syracuseStep 480541 = 180203) (by norm_num)
theorem B480577 : Blo 424774 480577 := bbase (se 2 (by rfl) ⟨180216, by rfl⟩ : syracuseStep 480577 = 360433) (by norm_num)
theorem B3659093 : Blo 424774 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B513373 : Blo 424774 513373 := bbase (se 3 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 513373 = 192515) (by norm_num)
theorem B480613 : Blo 424774 480613 := bbase (se 4 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 480613 = 90115) (by norm_num)
theorem B808309 : Blo 424774 808309 := bbase (se 5 (by rfl) ⟨37889, by rfl⟩ : syracuseStep 808309 = 75779) (by norm_num)
theorem B480649 : Blo 424774 480649 := bbase (se 2 (by rfl) ⟨180243, by rfl⟩ : syracuseStep 480649 = 360487) (by norm_num)
theorem B513421 : Blo 424774 513421 := bbase (se 3 (by rfl) ⟨96266, by rfl⟩ : syracuseStep 513421 = 192533) (by norm_num)
theorem B2151845 : Blo 424774 2151845 := bbase (se 4 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 2151845 = 403471) (by norm_num)
theorem B480685 : Blo 424774 480685 := bbase (se 3 (by rfl) ⟨90128, by rfl⟩ : syracuseStep 480685 = 180257) (by norm_num)
theorem B480721 : Blo 424774 480721 := bbase (se 2 (by rfl) ⟨180270, by rfl⟩ : syracuseStep 480721 = 360541) (by norm_num)
theorem B480757 : Blo 424774 480757 := bbase (se 5 (by rfl) ⟨22535, by rfl⟩ : syracuseStep 480757 = 45071) (by norm_num)
theorem B1299989 : Blo 424774 1299989 := bbase (se 6 (by rfl) ⟨30468, by rfl⟩ : syracuseStep 1299989 = 60937) (by norm_num)
theorem B480793 : Blo 424774 480793 := bbase (se 2 (by rfl) ⟨180297, by rfl⟩ : syracuseStep 480793 = 360595) (by norm_num)
theorem B480829 : Blo 424774 480829 := bbase (se 3 (by rfl) ⟨90155, by rfl⟩ : syracuseStep 480829 = 180311) (by norm_num)
theorem B1037893 : Blo 424774 1037893 := bbase (se 4 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 1037893 = 194605) (by norm_num)
theorem B480865 : Blo 424774 480865 := bbase (se 2 (by rfl) ⟨180324, by rfl⟩ : syracuseStep 480865 = 360649) (by norm_num)
theorem B480901 : Blo 424774 480901 := bbase (se 4 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 480901 = 90169) (by norm_num)
theorem B808613 : Blo 424774 808613 := bbase (se 4 (by rfl) ⟨75807, by rfl⟩ : syracuseStep 808613 = 151615) (by norm_num)
theorem B546473 : Blo 424774 546473 := bbase (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) (by norm_num)
theorem B480937 : Blo 424774 480937 := bbase (se 2 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 480937 = 360703) (by norm_num)
theorem B1824437 : Blo 424774 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B480973 : Blo 424774 480973 := bbase (se 3 (by rfl) ⟨90182, by rfl⟩ : syracuseStep 480973 = 180365) (by norm_num)
theorem B481009 : Blo 424774 481009 := bbase (se 2 (by rfl) ⟨180378, by rfl⟩ : syracuseStep 481009 = 360757) (by norm_num)
theorem B481045 : Blo 424774 481045 := bbase (se 6 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 481045 = 22549) (by norm_num)
theorem B481081 : Blo 424774 481081 := bbase (se 2 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 481081 = 360811) (by norm_num)
theorem B481117 : Blo 424774 481117 := bbase (se 3 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 481117 = 180419) (by norm_num)
theorem B481153 : Blo 424774 481153 := bbase (se 2 (by rfl) ⟨180432, by rfl⟩ : syracuseStep 481153 = 360865) (by norm_num)
theorem B2250629 : Blo 424774 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B1824677 : Blo 424774 1824677 := bbase (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) (by norm_num)
theorem B481189 : Blo 424774 481189 := bbase (se 4 (by rfl) ⟨45111, by rfl⟩ : syracuseStep 481189 = 90223) (by norm_num)
theorem B481225 : Blo 424774 481225 := bbase (se 2 (by rfl) ⟨180459, by rfl⟩ : syracuseStep 481225 = 360919) (by norm_num)
theorem B907213 : Blo 424774 907213 := bbase (se 3 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 907213 = 340205) (by norm_num)
theorem B481261 : Blo 424774 481261 := bbase (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) (by norm_num)
theorem B546817 : Blo 424774 546817 := bbase (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) (by norm_num)
theorem B1366021 : Blo 424774 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B481297 : Blo 424774 481297 := bbase (se 2 (by rfl) ⟨180486, by rfl⟩ : syracuseStep 481297 = 360973) (by norm_num)
theorem B776237 : Blo 424774 776237 := bbase (se 3 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 776237 = 291089) (by norm_num)
theorem B481333 : Blo 424774 481333 := bbase (se 5 (by rfl) ⟨22562, by rfl⟩ : syracuseStep 481333 = 45125) (by norm_num)
theorem B481369 : Blo 424774 481369 := bbase (se 2 (by rfl) ⟨180513, by rfl⟩ : syracuseStep 481369 = 361027) (by norm_num)
theorem B2054261 : Blo 424774 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B481405 : Blo 424774 481405 := bbase (se 3 (by rfl) ⟨90263, by rfl⟩ : syracuseStep 481405 = 180527) (by norm_num)
theorem B481441 : Blo 424774 481441 := bbase (se 2 (by rfl) ⟨180540, by rfl⟩ : syracuseStep 481441 = 361081) (by norm_num)
theorem B481477 : Blo 424774 481477 := bbase (se 4 (by rfl) ⟨45138, by rfl⟩ : syracuseStep 481477 = 90277) (by norm_num)
theorem B547021 : Blo 424774 547021 := bbase (se 3 (by rfl) ⟨102566, by rfl⟩ : syracuseStep 547021 = 205133) (by norm_num)
theorem B1300693 : Blo 424774 1300693 := bbase (se 7 (by rfl) ⟨15242, by rfl⟩ : syracuseStep 1300693 = 30485) (by norm_num)
theorem B481513 : Blo 424774 481513 := bbase (se 2 (by rfl) ⟨180567, by rfl⟩ : syracuseStep 481513 = 361135) (by norm_num)
theorem B481549 : Blo 424774 481549 := bbase (se 3 (by rfl) ⟨90290, by rfl⟩ : syracuseStep 481549 = 180581) (by norm_num)
theorem B481585 : Blo 424774 481585 := bbase (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) (by norm_num)
theorem B481621 : Blo 424774 481621 := bbase (se 10 (by rfl) ⟨705, by rfl⟩ : syracuseStep 481621 = 1411) (by norm_num)
theorem B481657 : Blo 424774 481657 := bbase (se 2 (by rfl) ⟨180621, by rfl⟩ : syracuseStep 481657 = 361243) (by norm_num)
theorem B809365 : Blo 424774 809365 := bbase (se 6 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 809365 = 37939) (by norm_num)
theorem B481693 : Blo 424774 481693 := bbase (se 3 (by rfl) ⟨90317, by rfl⟩ : syracuseStep 481693 = 180635) (by norm_num)
theorem B514469 : Blo 424774 514469 := bbase (se 4 (by rfl) ⟨48231, by rfl⟩ : syracuseStep 514469 = 96463) (by norm_num)
theorem B481729 : Blo 424774 481729 := bbase (se 2 (by rfl) ⟨180648, by rfl⟩ : syracuseStep 481729 = 361297) (by norm_num)
theorem B481765 : Blo 424774 481765 := bbase (se 4 (by rfl) ⟨45165, by rfl⟩ : syracuseStep 481765 = 90331) (by norm_num)
theorem B481801 : Blo 424774 481801 := bbase (se 2 (by rfl) ⟨180675, by rfl⟩ : syracuseStep 481801 = 361351) (by norm_num)
theorem B809509 : Blo 424774 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B481837 : Blo 424774 481837 := bbase (se 3 (by rfl) ⟨90344, by rfl⟩ : syracuseStep 481837 = 180689) (by norm_num)
theorem B481873 : Blo 424774 481873 := bbase (se 2 (by rfl) ⟨180702, by rfl⟩ : syracuseStep 481873 = 361405) (by norm_num)
theorem B481909 : Blo 424774 481909 := bbase (se 5 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 481909 = 45179) (by norm_num)
theorem B1399445 : Blo 424774 1399445 := bbase (se 6 (by rfl) ⟨32799, by rfl⟩ : syracuseStep 1399445 = 65599) (by norm_num)
theorem B481945 : Blo 424774 481945 := bbase (se 2 (by rfl) ⟨180729, by rfl⟩ : syracuseStep 481945 = 361459) (by norm_num)
theorem B2153141 : Blo 424774 2153141 := bbase (se 5 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 2153141 = 201857) (by norm_num)
theorem B481981 : Blo 424774 481981 := bbase (se 3 (by rfl) ⟨90371, by rfl⟩ : syracuseStep 481981 = 180743) (by norm_num)
theorem B809669 : Blo 424774 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B514777 : Blo 424774 514777 := bbase (se 2 (by rfl) ⟨193041, by rfl⟩ : syracuseStep 514777 = 386083) (by norm_num)
theorem B482017 : Blo 424774 482017 := bbase (se 2 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 482017 = 361513) (by norm_num)
theorem B482053 : Blo 424774 482053 := bbase (se 4 (by rfl) ⟨45192, by rfl⟩ : syracuseStep 482053 = 90385) (by norm_num)
theorem B482089 : Blo 424774 482089 := bbase (se 2 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 482089 = 361567) (by norm_num)
theorem B908101 : Blo 424774 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B482125 : Blo 424774 482125 := bbase (se 3 (by rfl) ⟨90398, by rfl⟩ : syracuseStep 482125 = 180797) (by norm_num)
theorem B809813 : Blo 424774 809813 := bbase (se 9 (by rfl) ⟨2372, by rfl⟩ : syracuseStep 809813 = 4745) (by norm_num)
theorem B482161 : Blo 424774 482161 := bbase (se 2 (by rfl) ⟨180810, by rfl⟩ : syracuseStep 482161 = 361621) (by norm_num)
theorem B514945 : Blo 424774 514945 := bbase (se 2 (by rfl) ⟨193104, by rfl⟩ : syracuseStep 514945 = 386209) (by norm_num)
theorem B1727381 : Blo 424774 1727381 := bbase (se 6 (by rfl) ⟨40485, by rfl⟩ : syracuseStep 1727381 = 80971) (by norm_num)
theorem B482197 : Blo 424774 482197 := bbase (se 6 (by rfl) ⟨11301, by rfl⟩ : syracuseStep 482197 = 22603) (by norm_num)
theorem B482233 : Blo 424774 482233 := bbase (se 2 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 482233 = 361675) (by norm_num)
theorem B482269 : Blo 424774 482269 := bbase (se 3 (by rfl) ⟨90425, by rfl⟩ : syracuseStep 482269 = 180851) (by norm_num)
theorem B482305 : Blo 424774 482305 := bbase (se 2 (by rfl) ⟨180864, by rfl⟩ : syracuseStep 482305 = 361729) (by norm_num)
theorem B482341 : Blo 424774 482341 := bbase (se 4 (by rfl) ⟨45219, by rfl⟩ : syracuseStep 482341 = 90439) (by norm_num)
theorem B810101 : Blo 424774 810101 := bbase (se 5 (by rfl) ⟨37973, by rfl⟩ : syracuseStep 810101 = 75947) (by norm_num)
theorem B810253 : Blo 424774 810253 := bbase (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) (by norm_num)
theorem B908597 : Blo 424774 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B1367381 : Blo 424774 1367381 := bbase (se 11 (by rfl) ⟨1001, by rfl⟩ : syracuseStep 1367381 = 2003) (by norm_num)
theorem B1564085 : Blo 424774 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B810557 : Blo 424774 810557 := bbase (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) (by norm_num)
theorem B1040045 : Blo 424774 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B974525 : Blo 424774 974525 := bbase (se 3 (by rfl) ⟨182723, by rfl⟩ : syracuseStep 974525 = 365447) (by norm_num)
theorem B2744117 : Blo 424774 2744117 := bbase (se 5 (by rfl) ⟨128630, by rfl⟩ : syracuseStep 2744117 = 257261) (by norm_num)
theorem B2154437 : Blo 424774 2154437 := bbase (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) (by norm_num)
theorem B1826965 : Blo 424774 1826965 := bbase (se 6 (by rfl) ⟨42819, by rfl⟩ : syracuseStep 1826965 = 85639) (by norm_num)
theorem B909485 : Blo 424774 909485 := bbase (se 3 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 909485 = 341057) (by norm_num)
theorem B1138933 : Blo 424774 1138933 := bbase (se 5 (by rfl) ⟨53387, by rfl⟩ : syracuseStep 1138933 = 106775) (by norm_num)
theorem B1433861 : Blo 424774 1433861 := bbase (se 4 (by rfl) ⟨134424, by rfl⟩ : syracuseStep 1433861 = 268849) (by norm_num)
theorem B909605 : Blo 424774 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B811309 : Blo 424774 811309 := bbase (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) (by norm_num)
theorem B811453 : Blo 424774 811453 := bbase (se 3 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 811453 = 304295) (by norm_num)
theorem B811613 : Blo 424774 811613 := bbase (se 3 (by rfl) ⟨152177, by rfl⟩ : syracuseStep 811613 = 304355) (by norm_num)
theorem B1434293 : Blo 424774 1434293 := bbase (se 5 (by rfl) ⟨67232, by rfl⟩ : syracuseStep 1434293 = 134465) (by norm_num)
theorem B680653 : Blo 424774 680653 := bbase (se 3 (by rfl) ⟨127622, by rfl⟩ : syracuseStep 680653 = 255245) (by norm_num)
theorem B811757 : Blo 424774 811757 := bbase (se 3 (by rfl) ⟨152204, by rfl⟩ : syracuseStep 811757 = 304409) (by norm_num)
theorem B549649 : Blo 424774 549649 := bbase (se 2 (by rfl) ⟨206118, by rfl⟩ : syracuseStep 549649 = 412237) (by norm_num)
theorem B3072917 : Blo 424774 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B910237 : Blo 424774 910237 := bbase (se 3 (by rfl) ⟨170669, by rfl⟩ : syracuseStep 910237 = 341339) (by norm_num)
theorem B615325 : Blo 424774 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B812045 : Blo 424774 812045 := bbase (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) (by norm_num)
theorem B1434725 : Blo 424774 1434725 := bbase (se 4 (by rfl) ⟨134505, by rfl⟩ : syracuseStep 1434725 = 269011) (by norm_num)
theorem B1729637 : Blo 424774 1729637 := bbase (se 4 (by rfl) ⟨162153, by rfl⟩ : syracuseStep 1729637 = 324307) (by norm_num)
theorem B812197 : Blo 424774 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B2057413 : Blo 424774 2057413 := bbase (se 4 (by rfl) ⟨192882, by rfl⟩ : syracuseStep 2057413 = 385765) (by norm_num)
theorem B2155733 : Blo 424774 2155733 := bbase (se 7 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 2155733 = 50525) (by norm_num)
theorem B681365 : Blo 424774 681365 := bbase (se 6 (by rfl) ⟨15969, by rfl⟩ : syracuseStep 681365 = 31939) (by norm_num)
theorem B5203349 : Blo 424774 5203349 := bbase (se 6 (by rfl) ⟨121953, by rfl⟩ : syracuseStep 5203349 = 243907) (by norm_num)
theorem B517573 : Blo 424774 517573 := bbase (se 4 (by rfl) ⟨48522, by rfl⟩ : syracuseStep 517573 = 97045) (by norm_num)
theorem B812501 : Blo 424774 812501 := bbase (se 7 (by rfl) ⟨9521, by rfl⟩ : syracuseStep 812501 = 19043) (by norm_num)
theorem B484877 : Blo 424774 484877 := bbase (se 3 (by rfl) ⟨90914, by rfl⟩ : syracuseStep 484877 = 181829) (by norm_num)
theorem B1435157 : Blo 424774 1435157 := bbase (se 6 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 1435157 = 67273) (by norm_num)
theorem B1828453 : Blo 424774 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B484969 : Blo 424774 484969 := bbase (se 2 (by rfl) ⟨181863, by rfl⟩ : syracuseStep 484969 = 363727) (by norm_num)
theorem B1828469 : Blo 424774 1828469 := bbase (se 5 (by rfl) ⟨85709, by rfl⟩ : syracuseStep 1828469 = 171419) (by norm_num)
theorem B911125 : Blo 424774 911125 := bbase (se 6 (by rfl) ⟨21354, by rfl⟩ : syracuseStep 911125 = 42709) (by norm_num)
theorem B911245 : Blo 424774 911245 := bbase (se 3 (by rfl) ⟨170858, by rfl⟩ : syracuseStep 911245 = 341717) (by norm_num)
theorem B1435589 : Blo 424774 1435589 := bbase (se 4 (by rfl) ⟨134586, by rfl⟩ : syracuseStep 1435589 = 269173) (by norm_num)
theorem B682037 : Blo 424774 682037 := bbase (se 5 (by rfl) ⟨31970, by rfl⟩ : syracuseStep 682037 = 63941) (by norm_num)
theorem B485461 : Blo 424774 485461 := bbase (se 8 (by rfl) ⟨2844, by rfl⟩ : syracuseStep 485461 = 5689) (by norm_num)
theorem B911501 : Blo 424774 911501 := bbase (se 3 (by rfl) ⟨170906, by rfl⟩ : syracuseStep 911501 = 341813) (by norm_num)
theorem B813253 : Blo 424774 813253 := bbase (se 4 (by rfl) ⟨76242, by rfl⟩ : syracuseStep 813253 = 152485) (by norm_num)
theorem B1075477 : Blo 424774 1075477 := bbase (se 6 (by rfl) ⟨25206, by rfl⟩ : syracuseStep 1075477 = 50413) (by norm_num)
theorem B4811093 : Blo 424774 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B813397 : Blo 424774 813397 := bbase (se 10 (by rfl) ⟨1191, by rfl⟩ : syracuseStep 813397 = 2383) (by norm_num)
theorem B1436021 : Blo 424774 1436021 := bbase (se 5 (by rfl) ⟨67313, by rfl⟩ : syracuseStep 1436021 = 134627) (by norm_num)
theorem B1075589 : Blo 424774 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B2157029 : Blo 424774 2157029 := bbase (se 4 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 2157029 = 404443) (by norm_num)
theorem B813557 : Blo 424774 813557 := bbase (se 5 (by rfl) ⟨38135, by rfl⟩ : syracuseStep 813557 = 76271) (by norm_num)
theorem B682549 : Blo 424774 682549 := bbase (se 5 (by rfl) ⟨31994, by rfl⟩ : syracuseStep 682549 = 63989) (by norm_num)
theorem B1075781 : Blo 424774 1075781 := bbase (se 4 (by rfl) ⟨100854, by rfl⟩ : syracuseStep 1075781 = 201709) (by norm_num)
theorem B3467861 : Blo 424774 3467861 := bbase (se 8 (by rfl) ⟨20319, by rfl⟩ : syracuseStep 3467861 = 40639) (by norm_num)
theorem B813701 : Blo 424774 813701 := bbase (se 4 (by rfl) ⟨76284, by rfl⟩ : syracuseStep 813701 = 152569) (by norm_num)
theorem B1370789 : Blo 424774 1370789 := bbase (se 4 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 1370789 = 257023) (by norm_num)
theorem B1174181 : Blo 424774 1174181 := bbase (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) (by norm_num)
theorem B1436453 : Blo 424774 1436453 := bbase (se 4 (by rfl) ⟨134667, by rfl⟩ : syracuseStep 1436453 = 269335) (by norm_num)
theorem B1076125 : Blo 424774 1076125 := bbase (se 3 (by rfl) ⟨201773, by rfl⟩ : syracuseStep 1076125 = 403547) (by norm_num)
theorem B813989 : Blo 424774 813989 := bbase (se 4 (by rfl) ⟨76311, by rfl⟩ : syracuseStep 813989 = 152623) (by norm_num)
theorem B486337 : Blo 424774 486337 := bbase (se 2 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 486337 = 364753) (by norm_num)
theorem B650189 : Blo 424774 650189 := bbase (se 3 (by rfl) ⟨121910, by rfl⟩ : syracuseStep 650189 = 243821) (by norm_num)
theorem B683005 : Blo 424774 683005 := bbase (se 3 (by rfl) ⟨128063, by rfl⟩ : syracuseStep 683005 = 256127) (by norm_num)
theorem B912389 : Blo 424774 912389 := bbase (se 4 (by rfl) ⟨85536, by rfl⟩ : syracuseStep 912389 = 171073) (by norm_num)
theorem B1076237 : Blo 424774 1076237 := bbase (se 3 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 1076237 = 403589) (by norm_num)
theorem B453649 : Blo 424774 453649 := bbase (se 2 (by rfl) ⟨170118, by rfl⟩ : syracuseStep 453649 = 340237) (by norm_num)
theorem B2419733 : Blo 424774 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B453709 : Blo 424774 453709 := bbase (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) (by norm_num)
theorem B1076429 : Blo 424774 1076429 := bbase (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) (by norm_num)
theorem B1436885 : Blo 424774 1436885 := bbase (se 7 (by rfl) ⟨16838, by rfl⟩ : syracuseStep 1436885 = 33677) (by norm_num)
theorem B912629 : Blo 424774 912629 := bbase (se 5 (by rfl) ⟨42779, by rfl⟩ : syracuseStep 912629 = 85559) (by norm_num)
theorem B3239189 : Blo 424774 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B454025 : Blo 424774 454025 := bbase (se 2 (by rfl) ⟨170259, by rfl⟩ : syracuseStep 454025 = 340519) (by norm_num)
theorem B7925141 : Blo 424774 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B1076773 : Blo 424774 1076773 := bbase (se 4 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 1076773 = 201895) (by norm_num)
theorem B1437317 : Blo 424774 1437317 := bbase (se 4 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 1437317 = 269497) (by norm_num)
theorem B1076885 : Blo 424774 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B683677 : Blo 424774 683677 := bbase (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) (by norm_num)
theorem B1732309 : Blo 424774 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B913133 : Blo 424774 913133 := bbase (se 3 (by rfl) ⟨171212, by rfl⟩ : syracuseStep 913133 = 342425) (by norm_num)
theorem B2158325 : Blo 424774 2158325 := bbase (se 5 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 2158325 = 202343) (by norm_num)
theorem B913141 : Blo 424774 913141 := bbase (se 5 (by rfl) ⟨42803, by rfl⟩ : syracuseStep 913141 = 85607) (by norm_num)
theorem B454469 : Blo 424774 454469 := bbase (se 4 (by rfl) ⟨42606, by rfl⟩ : syracuseStep 454469 = 85213) (by norm_num)
theorem B1830725 : Blo 424774 1830725 := bbase (se 4 (by rfl) ⟨171630, by rfl⟩ : syracuseStep 1830725 = 343261) (by norm_num)
theorem B1077077 : Blo 424774 1077077 := bbase (se 9 (by rfl) ⟨3155, by rfl⟩ : syracuseStep 1077077 = 6311) (by norm_num)
theorem B454529 : Blo 424774 454529 := bbase (se 2 (by rfl) ⟨170448, by rfl⟩ : syracuseStep 454529 = 340897) (by norm_num)
theorem B651173 : Blo 424774 651173 := bbase (se 4 (by rfl) ⟨61047, by rfl⟩ : syracuseStep 651173 = 122095) (by norm_num)
theorem B1372069 : Blo 424774 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B3502037 : Blo 424774 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B454657 : Blo 424774 454657 := bbase (se 2 (by rfl) ⟨170496, by rfl⟩ : syracuseStep 454657 = 340993) (by norm_num)
theorem B6582293 : Blo 424774 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B1437749 : Blo 424774 1437749 := bbase (se 5 (by rfl) ⟨67394, by rfl⟩ : syracuseStep 1437749 = 134789) (by norm_num)
theorem B684101 : Blo 424774 684101 := bbase (se 4 (by rfl) ⟨64134, by rfl⟩ : syracuseStep 684101 = 128269) (by norm_num)
theorem B487505 : Blo 424774 487505 := bbase (se 2 (by rfl) ⟨182814, by rfl⟩ : syracuseStep 487505 = 365629) (by norm_num)
theorem B716917 : Blo 424774 716917 := bbase (se 5 (by rfl) ⟨33605, by rfl⟩ : syracuseStep 716917 = 67211) (by norm_num)
theorem B782453 : Blo 424774 782453 := bbase (se 5 (by rfl) ⟨36677, by rfl⟩ : syracuseStep 782453 = 73355) (by norm_num)
theorem B1077421 : Blo 424774 1077421 := bbase (se 3 (by rfl) ⟨202016, by rfl⟩ : syracuseStep 1077421 = 404033) (by norm_num)
theorem B717005 : Blo 424774 717005 := bbase (se 3 (by rfl) ⟨134438, by rfl⟩ : syracuseStep 717005 = 268877) (by norm_num)
theorem B618725 : Blo 424774 618725 := bbase (se 4 (by rfl) ⟨58005, by rfl⟩ : syracuseStep 618725 = 116011) (by norm_num)
theorem B487705 : Blo 424774 487705 := bbase (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) (by norm_num)
theorem B1077533 : Blo 424774 1077533 := bbase (se 3 (by rfl) ⟨202037, by rfl⟩ : syracuseStep 1077533 = 404075) (by norm_num)
theorem B717133 : Blo 424774 717133 := bbase (se 3 (by rfl) ⟨134462, by rfl⟩ : syracuseStep 717133 = 268925) (by norm_num)
theorem B684389 : Blo 424774 684389 := bbase (se 4 (by rfl) ⟨64161, by rfl⟩ : syracuseStep 684389 = 128323) (by norm_num)
theorem B717221 : Blo 424774 717221 := bbase (se 4 (by rfl) ⟨67239, by rfl⟩ : syracuseStep 717221 = 134479) (by norm_num)
theorem B455101 : Blo 424774 455101 := bbase (se 3 (by rfl) ⟨85331, by rfl⟩ : syracuseStep 455101 = 170663) (by norm_num)
theorem B1077725 : Blo 424774 1077725 := bbase (se 3 (by rfl) ⟨202073, by rfl⟩ : syracuseStep 1077725 = 404147) (by norm_num)
theorem B1438181 : Blo 424774 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B717349 : Blo 424774 717349 := bbase (se 4 (by rfl) ⟨67251, by rfl⟩ : syracuseStep 717349 = 134503) (by norm_num)
theorem B455221 : Blo 424774 455221 := bbase (se 5 (by rfl) ⟨21338, by rfl⟩ : syracuseStep 455221 = 42677) (by norm_num)
theorem B717437 : Blo 424774 717437 := bbase (se 3 (by rfl) ⟨134519, by rfl⟩ : syracuseStep 717437 = 269039) (by norm_num)
theorem B717565 : Blo 424774 717565 := bbase (se 3 (by rfl) ⟨134543, by rfl⟩ : syracuseStep 717565 = 269087) (by norm_num)
theorem B455473 : Blo 424774 455473 := bbase (se 2 (by rfl) ⟨170802, by rfl⟩ : syracuseStep 455473 = 341605) (by norm_num)
theorem B1078069 : Blo 424774 1078069 := bbase (se 5 (by rfl) ⟨50534, by rfl⟩ : syracuseStep 1078069 = 101069) (by norm_num)
theorem B455477 : Blo 424774 455477 := bbase (se 5 (by rfl) ⟨21350, by rfl⟩ : syracuseStep 455477 = 42701) (by norm_num)
theorem B717653 : Blo 424774 717653 := bbase (se 9 (by rfl) ⟨2102, by rfl⟩ : syracuseStep 717653 = 4205) (by norm_num)
theorem B914269 : Blo 424774 914269 := bbase (se 3 (by rfl) ⟨171425, by rfl⟩ : syracuseStep 914269 = 342851) (by norm_num)
theorem B1438613 : Blo 424774 1438613 := bbase (se 6 (by rfl) ⟨33717, by rfl⟩ : syracuseStep 1438613 = 67435) (by norm_num)
theorem B1078181 : Blo 424774 1078181 := bbase (se 4 (by rfl) ⟨101079, by rfl⟩ : syracuseStep 1078181 = 202159) (by norm_num)
theorem B717781 : Blo 424774 717781 := bbase (se 7 (by rfl) ⟨8411, by rfl⟩ : syracuseStep 717781 = 16823) (by norm_num)
theorem B3109877 : Blo 424774 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2159621 : Blo 424774 2159621 := bbase (se 4 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 2159621 = 404929) (by norm_num)
theorem B717869 : Blo 424774 717869 := bbase (se 3 (by rfl) ⟨134600, by rfl⟩ : syracuseStep 717869 = 269201) (by norm_num)
theorem B1078373 : Blo 424774 1078373 := bbase (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) (by norm_num)
theorem B685189 : Blo 424774 685189 := bbase (se 4 (by rfl) ⟨64236, by rfl⟩ : syracuseStep 685189 = 128473) (by norm_num)
theorem B717997 : Blo 424774 717997 := bbase (se 3 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 717997 = 269249) (by norm_num)
theorem B914645 : Blo 424774 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B1373429 : Blo 424774 1373429 := bbase (se 5 (by rfl) ⟨64379, by rfl⟩ : syracuseStep 1373429 = 128759) (by norm_num)
theorem B718085 : Blo 424774 718085 := bbase (se 4 (by rfl) ⟨67320, by rfl⟩ : syracuseStep 718085 = 134641) (by norm_num)
theorem B1439045 : Blo 424774 1439045 := bbase (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) (by norm_num)
theorem B456041 : Blo 424774 456041 := bbase (se 2 (by rfl) ⟨171015, by rfl⟩ : syracuseStep 456041 = 342031) (by norm_num)
theorem B1373557 : Blo 424774 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B718213 : Blo 424774 718213 := bbase (se 4 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 718213 = 134665) (by norm_num)
theorem B1078717 : Blo 424774 1078717 := bbase (se 3 (by rfl) ⟨202259, by rfl⟩ : syracuseStep 1078717 = 404519) (by norm_num)
theorem B718301 : Blo 424774 718301 := bbase (se 3 (by rfl) ⟨134681, by rfl⟩ : syracuseStep 718301 = 269363) (by norm_num)
theorem B456229 : Blo 424774 456229 := bbase (se 4 (by rfl) ⟨42771, by rfl⟩ : syracuseStep 456229 = 85543) (by norm_num)
theorem B1078829 : Blo 424774 1078829 := bbase (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) (by norm_num)
theorem B718429 : Blo 424774 718429 := bbase (se 3 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 718429 = 269411) (by norm_num)
theorem B685741 : Blo 424774 685741 := bbase (se 3 (by rfl) ⟨128576, by rfl⟩ : syracuseStep 685741 = 257153) (by norm_num)
theorem B718517 : Blo 424774 718517 := bbase (se 5 (by rfl) ⟨33680, by rfl⟩ : syracuseStep 718517 = 67361) (by norm_num)
theorem B2291381 : Blo 424774 2291381 := bbase (se 5 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 2291381 = 214817) (by norm_num)
theorem B1079021 : Blo 424774 1079021 := bbase (se 3 (by rfl) ⟨202316, by rfl⟩ : syracuseStep 1079021 = 404633) (by norm_num)
theorem B1439477 : Blo 424774 1439477 := bbase (se 5 (by rfl) ⟨67475, by rfl⟩ : syracuseStep 1439477 = 134951) (by norm_num)
theorem B718645 : Blo 424774 718645 := bbase (se 5 (by rfl) ⟨33686, by rfl⟩ : syracuseStep 718645 = 67373) (by norm_num)
theorem B718733 : Blo 424774 718733 := bbase (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) (by norm_num)
theorem B1210277 : Blo 424774 1210277 := bbase (se 4 (by rfl) ⟨113463, by rfl⟩ : syracuseStep 1210277 = 226927) (by norm_num)
theorem B1537957 : Blo 424774 1537957 := bbase (se 4 (by rfl) ⟨144183, by rfl⟩ : syracuseStep 1537957 = 288367) (by norm_num)
theorem B685997 : Blo 424774 685997 := bbase (se 3 (by rfl) ⟨128624, by rfl⟩ : syracuseStep 685997 = 257249) (by norm_num)
theorem B718861 : Blo 424774 718861 := bbase (se 3 (by rfl) ⟨134786, by rfl⟩ : syracuseStep 718861 = 269573) (by norm_num)
theorem B1079365 : Blo 424774 1079365 := bbase (se 4 (by rfl) ⟨101190, by rfl⟩ : syracuseStep 1079365 = 202381) (by norm_num)
theorem B718949 : Blo 424774 718949 := bbase (se 4 (by rfl) ⟨67401, by rfl⟩ : syracuseStep 718949 = 134803) (by norm_num)
theorem B1439909 : Blo 424774 1439909 := bbase (se 4 (by rfl) ⟨134991, by rfl⟩ : syracuseStep 1439909 = 269983) (by norm_num)
theorem B1079477 : Blo 424774 1079477 := bbase (se 5 (by rfl) ⟨50600, by rfl⟩ : syracuseStep 1079477 = 101201) (by norm_num)
theorem B719077 : Blo 424774 719077 := bbase (se 4 (by rfl) ⟨67413, by rfl⟩ : syracuseStep 719077 = 134827) (by norm_num)
theorem B2160917 : Blo 424774 2160917 := bbase (se 6 (by rfl) ⟨50646, by rfl⟩ : syracuseStep 2160917 = 101293) (by norm_num)
theorem B719165 : Blo 424774 719165 := bbase (se 3 (by rfl) ⟨134843, by rfl⟩ : syracuseStep 719165 = 269687) (by norm_num)
theorem B457049 : Blo 424774 457049 := bbase (se 2 (by rfl) ⟨171393, by rfl⟩ : syracuseStep 457049 = 342787) (by norm_num)
theorem B1079669 : Blo 424774 1079669 := bbase (se 5 (by rfl) ⟨50609, by rfl⟩ : syracuseStep 1079669 = 101219) (by norm_num)
theorem B719293 : Blo 424774 719293 := bbase (se 3 (by rfl) ⟨134867, by rfl⟩ : syracuseStep 719293 = 269735) (by norm_num)
theorem B719381 : Blo 424774 719381 := bbase (se 6 (by rfl) ⟨16860, by rfl⟩ : syracuseStep 719381 = 33721) (by norm_num)
theorem B1440341 : Blo 424774 1440341 := bbase (se 8 (by rfl) ⟨8439, by rfl⟩ : syracuseStep 1440341 = 16879) (by norm_num)
theorem B686701 : Blo 424774 686701 := bbase (se 3 (by rfl) ⟨128756, by rfl⟩ : syracuseStep 686701 = 257513) (by norm_num)
theorem B719509 : Blo 424774 719509 := bbase (se 6 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 719509 = 33727) (by norm_num)
theorem B555709 : Blo 424774 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B1080013 : Blo 424774 1080013 := bbase (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) (by norm_num)
theorem B719597 : Blo 424774 719597 := bbase (se 3 (by rfl) ⟨134924, by rfl⟩ : syracuseStep 719597 = 269849) (by norm_num)
theorem B457493 : Blo 424774 457493 := bbase (se 6 (by rfl) ⟨10722, by rfl⟩ : syracuseStep 457493 = 21445) (by norm_num)
theorem B1080125 : Blo 424774 1080125 := bbase (se 3 (by rfl) ⟨202523, by rfl⟩ : syracuseStep 1080125 = 405047) (by norm_num)
theorem B719725 : Blo 424774 719725 := bbase (se 3 (by rfl) ⟨134948, by rfl⟩ : syracuseStep 719725 = 269897) (by norm_num)
theorem B719813 : Blo 424774 719813 := bbase (se 4 (by rfl) ⟨67482, by rfl⟩ : syracuseStep 719813 = 134965) (by norm_num)
theorem B1080317 : Blo 424774 1080317 := bbase (se 3 (by rfl) ⟨202559, by rfl⟩ : syracuseStep 1080317 = 405119) (by norm_num)
theorem B1440773 : Blo 424774 1440773 := bbase (se 4 (by rfl) ⟨135072, by rfl⟩ : syracuseStep 1440773 = 270145) (by norm_num)
theorem B457741 : Blo 424774 457741 := bbase (se 3 (by rfl) ⟨85826, by rfl⟩ : syracuseStep 457741 = 171653) (by norm_num)
theorem B719941 : Blo 424774 719941 := bbase (se 4 (by rfl) ⟨67494, by rfl⟩ : syracuseStep 719941 = 134989) (by norm_num)
theorem B720029 : Blo 424774 720029 := bbase (se 3 (by rfl) ⟨135005, by rfl⟩ : syracuseStep 720029 = 270011) (by norm_num)
theorem B720157 : Blo 424774 720157 := bbase (se 3 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 720157 = 270059) (by norm_num)
theorem B1080661 : Blo 424774 1080661 := bbase (se 11 (by rfl) ⟨791, by rfl⟩ : syracuseStep 1080661 = 1583) (by norm_num)
theorem B720245 : Blo 424774 720245 := bbase (se 5 (by rfl) ⟨33761, by rfl⟩ : syracuseStep 720245 = 67523) (by norm_num)
theorem B1441205 : Blo 424774 1441205 := bbase (se 5 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 1441205 = 135113) (by norm_num)
theorem B1080773 : Blo 424774 1080773 := bbase (se 4 (by rfl) ⟨101322, by rfl⟩ : syracuseStep 1080773 = 202645) (by norm_num)
theorem B1211861 : Blo 424774 1211861 := bbase (se 7 (by rfl) ⟨14201, by rfl⟩ : syracuseStep 1211861 = 28403) (by norm_num)
theorem B720373 : Blo 424774 720373 := bbase (se 5 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 720373 = 67535) (by norm_num)
theorem B2162213 : Blo 424774 2162213 := bbase (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) (by norm_num)
theorem B720461 : Blo 424774 720461 := bbase (se 3 (by rfl) ⟨135086, by rfl⟩ : syracuseStep 720461 = 270173) (by norm_num)
theorem B1080965 : Blo 424774 1080965 := bbase (se 4 (by rfl) ⟨101340, by rfl⟩ : syracuseStep 1080965 = 202681) (by norm_num)
theorem B720589 : Blo 424774 720589 := bbase (se 3 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 720589 = 270221) (by norm_num)
theorem B720677 : Blo 424774 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B1441637 : Blo 424774 1441637 := bbase (se 4 (by rfl) ⟨135153, by rfl⟩ : syracuseStep 1441637 = 270307) (by norm_num)
theorem B720805 : Blo 424774 720805 := bbase (se 4 (by rfl) ⟨67575, by rfl⟩ : syracuseStep 720805 = 135151) (by norm_num)
theorem B1081309 : Blo 424774 1081309 := bbase (se 3 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 1081309 = 405491) (by norm_num)
theorem B720893 : Blo 424774 720893 := bbase (se 3 (by rfl) ⟨135167, by rfl⟩ : syracuseStep 720893 = 270335) (by norm_num)
theorem B425987 : Blo 424774 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B720913 : Blo 424774 720913 := bstep (se 2 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 720913 = 540685) B540685
theorem B426003 : Blo 424774 426003 := bstep (se 1 (by rfl) ⟨319502, by rfl⟩ : syracuseStep 426003 = 639005) B639005
theorem B426019 : Blo 424774 426019 := bstep (se 1 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 426019 = 639029) B639029
theorem B426035 : Blo 424774 426035 := bstep (se 1 (by rfl) ⟨319526, by rfl⟩ : syracuseStep 426035 = 639053) B639053
theorem B720947 : Blo 424774 720947 := bstep (se 1 (by rfl) ⟨540710, by rfl⟩ : syracuseStep 720947 = 1081421) B1081421
theorem B426051 : Blo 424774 426051 := bstep (se 1 (by rfl) ⟨319538, by rfl⟩ : syracuseStep 426051 = 639077) B639077
theorem B426067 : Blo 424774 426067 := bstep (se 1 (by rfl) ⟨319550, by rfl⟩ : syracuseStep 426067 = 639101) B639101
theorem B426083 : Blo 424774 426083 := bstep (se 1 (by rfl) ⟨319562, by rfl⟩ : syracuseStep 426083 = 639125) B639125
theorem B426099 : Blo 424774 426099 := bstep (se 1 (by rfl) ⟨319574, by rfl⟩ : syracuseStep 426099 = 639149) B639149
theorem B426115 : Blo 424774 426115 := bstep (se 1 (by rfl) ⟨319586, by rfl⟩ : syracuseStep 426115 = 639173) B639173
theorem B426131 : Blo 424774 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B426147 : Blo 424774 426147 := bstep (se 1 (by rfl) ⟨319610, by rfl⟩ : syracuseStep 426147 = 639221) B639221
theorem B426163 : Blo 424774 426163 := bstep (se 1 (by rfl) ⟨319622, by rfl⟩ : syracuseStep 426163 = 639245) B639245
theorem B721075 : Blo 424774 721075 := bstep (se 1 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 721075 = 1081613) B1081613
theorem B426179 : Blo 424774 426179 := bstep (se 1 (by rfl) ⟨319634, by rfl⟩ : syracuseStep 426179 = 639269) B639269
theorem B426195 : Blo 424774 426195 := bstep (se 1 (by rfl) ⟨319646, by rfl⟩ : syracuseStep 426195 = 639293) B639293
theorem B426211 : Blo 424774 426211 := bstep (se 1 (by rfl) ⟨319658, by rfl⟩ : syracuseStep 426211 = 639317) B639317
theorem B426227 : Blo 424774 426227 := bstep (se 1 (by rfl) ⟨319670, by rfl⟩ : syracuseStep 426227 = 639341) B639341
theorem B426243 : Blo 424774 426243 := bstep (se 1 (by rfl) ⟨319682, by rfl⟩ : syracuseStep 426243 = 639365) B639365
theorem B426259 : Blo 424774 426259 := bstep (se 1 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 426259 = 639389) B639389
theorem B426275 : Blo 424774 426275 := bstep (se 1 (by rfl) ⟨319706, by rfl⟩ : syracuseStep 426275 = 639413) B639413
theorem B426291 : Blo 424774 426291 := bstep (se 1 (by rfl) ⟨319718, by rfl⟩ : syracuseStep 426291 = 639437) B639437
theorem B721217 : Blo 424774 721217 := bstep (se 2 (by rfl) ⟨270456, by rfl⟩ : syracuseStep 721217 = 540913) B540913
theorem B426307 : Blo 424774 426307 := bstep (se 1 (by rfl) ⟨319730, by rfl⟩ : syracuseStep 426307 = 639461) B639461
theorem B426323 : Blo 424774 426323 := bstep (se 1 (by rfl) ⟨319742, by rfl⟩ : syracuseStep 426323 = 639485) B639485
theorem B426339 : Blo 424774 426339 := bstep (se 1 (by rfl) ⟨319754, by rfl⟩ : syracuseStep 426339 = 639509) B639509
theorem B426355 : Blo 424774 426355 := bstep (se 1 (by rfl) ⟨319766, by rfl⟩ : syracuseStep 426355 = 639533) B639533
theorem B426371 : Blo 424774 426371 := bstep (se 1 (by rfl) ⟨319778, by rfl⟩ : syracuseStep 426371 = 639557) B639557
theorem B1081745 : Blo 424774 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B426387 : Blo 424774 426387 := bstep (se 1 (by rfl) ⟨319790, by rfl⟩ : syracuseStep 426387 = 639581) B639581
theorem B426403 : Blo 424774 426403 := bstep (se 1 (by rfl) ⟨319802, by rfl⟩ : syracuseStep 426403 = 639605) B639605
theorem B426419 : Blo 424774 426419 := bstep (se 1 (by rfl) ⟨319814, by rfl⟩ : syracuseStep 426419 = 639629) B639629
theorem B721345 : Blo 424774 721345 := bstep (se 2 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 721345 = 541009) B541009
theorem B426435 : Blo 424774 426435 := bstep (se 1 (by rfl) ⟨319826, by rfl⟩ : syracuseStep 426435 = 639653) B639653
theorem B1081795 : Blo 424774 1081795 := bstep (se 1 (by rfl) ⟨811346, by rfl⟩ : syracuseStep 1081795 = 1622693) B1622693
theorem B426451 : Blo 424774 426451 := bstep (se 1 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 426451 = 639677) B639677
theorem B426467 : Blo 424774 426467 := bstep (se 1 (by rfl) ⟨319850, by rfl⟩ : syracuseStep 426467 = 639701) B639701
theorem B721379 : Blo 424774 721379 := bstep (se 1 (by rfl) ⟨541034, by rfl⟩ : syracuseStep 721379 = 1082069) B1082069
theorem B1442285 : Blo 424774 1442285 := bstep (se 3 (by rfl) ⟨270428, by rfl⟩ : syracuseStep 1442285 = 540857) B540857
theorem B2163185 : Blo 424774 2163185 := bstep (se 2 (by rfl) ⟨811194, by rfl⟩ : syracuseStep 2163185 = 1622389) B1622389
theorem B426483 : Blo 424774 426483 := bstep (se 1 (by rfl) ⟨319862, by rfl⟩ : syracuseStep 426483 = 639725) B639725
theorem B426499 : Blo 424774 426499 := bstep (se 1 (by rfl) ⟨319874, by rfl⟩ : syracuseStep 426499 = 639749) B639749
theorem B426515 : Blo 424774 426515 := bstep (se 1 (by rfl) ⟨319886, by rfl⟩ : syracuseStep 426515 = 639773) B639773
theorem B426531 : Blo 424774 426531 := bstep (se 1 (by rfl) ⟨319898, by rfl⟩ : syracuseStep 426531 = 639797) B639797
theorem B1442339 : Blo 424774 1442339 := bstep (se 1 (by rfl) ⟨1081754, by rfl⟩ : syracuseStep 1442339 = 2163509) B2163509
theorem B426547 : Blo 424774 426547 := bstep (se 1 (by rfl) ⟨319910, by rfl⟩ : syracuseStep 426547 = 639821) B639821
theorem B426563 : Blo 424774 426563 := bstep (se 1 (by rfl) ⟨319922, by rfl⟩ : syracuseStep 426563 = 639845) B639845
theorem B1081937 : Blo 424774 1081937 := bstep (se 2 (by rfl) ⟨405726, by rfl⟩ : syracuseStep 1081937 = 811453) B811453
theorem B426579 : Blo 424774 426579 := bstep (se 1 (by rfl) ⟨319934, by rfl⟩ : syracuseStep 426579 = 639869) B639869
theorem B426595 : Blo 424774 426595 := bstep (se 1 (by rfl) ⟨319946, by rfl⟩ : syracuseStep 426595 = 639893) B639893
theorem B721507 : Blo 424774 721507 := bstep (se 1 (by rfl) ⟨541130, by rfl⟩ : syracuseStep 721507 = 1082261) B1082261
theorem B426611 : Blo 424774 426611 := bstep (se 1 (by rfl) ⟨319958, by rfl⟩ : syracuseStep 426611 = 639917) B639917
theorem B426627 : Blo 424774 426627 := bstep (se 1 (by rfl) ⟨319970, by rfl⟩ : syracuseStep 426627 = 639941) B639941
theorem B426643 : Blo 424774 426643 := bstep (se 1 (by rfl) ⟨319982, by rfl⟩ : syracuseStep 426643 = 639965) B639965
theorem B426659 : Blo 424774 426659 := bstep (se 1 (by rfl) ⟨319994, by rfl⟩ : syracuseStep 426659 = 639989) B639989
theorem B426675 : Blo 424774 426675 := bstep (se 1 (by rfl) ⟨320006, by rfl⟩ : syracuseStep 426675 = 640013) B640013
theorem B426691 : Blo 424774 426691 := bstep (se 1 (by rfl) ⟨320018, by rfl⟩ : syracuseStep 426691 = 640037) B640037
theorem B426707 : Blo 424774 426707 := bstep (se 1 (by rfl) ⟨320030, by rfl⟩ : syracuseStep 426707 = 640061) B640061
theorem B426723 : Blo 424774 426723 := bstep (se 1 (by rfl) ⟨320042, by rfl⟩ : syracuseStep 426723 = 640085) B640085
theorem B721649 : Blo 424774 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B426739 : Blo 424774 426739 := bstep (se 1 (by rfl) ⟨320054, by rfl⟩ : syracuseStep 426739 = 640109) B640109
theorem B426755 : Blo 424774 426755 := bstep (se 1 (by rfl) ⟨320066, by rfl⟩ : syracuseStep 426755 = 640133) B640133
theorem B426771 : Blo 424774 426771 := bstep (se 1 (by rfl) ⟨320078, by rfl⟩ : syracuseStep 426771 = 640157) B640157
theorem B1868579 : Blo 424774 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B426787 : Blo 424774 426787 := bstep (se 1 (by rfl) ⟨320090, by rfl⟩ : syracuseStep 426787 = 640181) B640181
theorem B1442609 : Blo 424774 1442609 := bstep (se 2 (by rfl) ⟨540978, by rfl⟩ : syracuseStep 1442609 = 1081957) B1081957
theorem B426803 : Blo 424774 426803 := bstep (se 1 (by rfl) ⟨320102, by rfl⟩ : syracuseStep 426803 = 640205) B640205
theorem B426819 : Blo 424774 426819 := bstep (se 1 (by rfl) ⟨320114, by rfl⟩ : syracuseStep 426819 = 640229) B640229
theorem B426835 : Blo 424774 426835 := bstep (se 1 (by rfl) ⟨320126, by rfl⟩ : syracuseStep 426835 = 640253) B640253
theorem B426851 : Blo 424774 426851 := bstep (se 1 (by rfl) ⟨320138, by rfl⟩ : syracuseStep 426851 = 640277) B640277
theorem B721777 : Blo 424774 721777 := bstep (se 2 (by rfl) ⟨270666, by rfl⟩ : syracuseStep 721777 = 541333) B541333
theorem B426867 : Blo 424774 426867 := bstep (se 1 (by rfl) ⟨320150, by rfl⟩ : syracuseStep 426867 = 640301) B640301
theorem B426883 : Blo 424774 426883 := bstep (se 1 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 426883 = 640325) B640325
theorem B426899 : Blo 424774 426899 := bstep (se 1 (by rfl) ⟨320174, by rfl⟩ : syracuseStep 426899 = 640349) B640349
theorem B721811 : Blo 424774 721811 := bstep (se 1 (by rfl) ⟨541358, by rfl⟩ : syracuseStep 721811 = 1082717) B1082717
theorem B426915 : Blo 424774 426915 := bstep (se 1 (by rfl) ⟨320186, by rfl⟩ : syracuseStep 426915 = 640373) B640373
theorem B426931 : Blo 424774 426931 := bstep (se 1 (by rfl) ⟨320198, by rfl⟩ : syracuseStep 426931 = 640397) B640397
theorem B426947 : Blo 424774 426947 := bstep (se 1 (by rfl) ⟨320210, by rfl⟩ : syracuseStep 426947 = 640421) B640421
theorem B426963 : Blo 424774 426963 := bstep (se 1 (by rfl) ⟨320222, by rfl⟩ : syracuseStep 426963 = 640445) B640445
theorem B426979 : Blo 424774 426979 := bstep (se 1 (by rfl) ⟨320234, by rfl⟩ : syracuseStep 426979 = 640469) B640469
theorem B426995 : Blo 424774 426995 := bstep (se 1 (by rfl) ⟨320246, by rfl⟩ : syracuseStep 426995 = 640493) B640493
theorem B427011 : Blo 424774 427011 := bstep (se 1 (by rfl) ⟨320258, by rfl⟩ : syracuseStep 427011 = 640517) B640517
theorem B427027 : Blo 424774 427027 := bstep (se 1 (by rfl) ⟨320270, by rfl⟩ : syracuseStep 427027 = 640541) B640541
theorem B721939 : Blo 424774 721939 := bstep (se 1 (by rfl) ⟨541454, by rfl⟩ : syracuseStep 721939 = 1082909) B1082909
theorem B427043 : Blo 424774 427043 := bstep (se 1 (by rfl) ⟨320282, by rfl⟩ : syracuseStep 427043 = 640565) B640565
theorem B427059 : Blo 424774 427059 := bstep (se 1 (by rfl) ⟨320294, by rfl⟩ : syracuseStep 427059 = 640589) B640589
theorem B427075 : Blo 424774 427075 := bstep (se 1 (by rfl) ⟨320306, by rfl⟩ : syracuseStep 427075 = 640613) B640613
theorem B427091 : Blo 424774 427091 := bstep (se 1 (by rfl) ⟨320318, by rfl⟩ : syracuseStep 427091 = 640637) B640637
theorem B427107 : Blo 424774 427107 := bstep (se 1 (by rfl) ⟨320330, by rfl⟩ : syracuseStep 427107 = 640661) B640661
theorem B427123 : Blo 424774 427123 := bstep (se 1 (by rfl) ⟨320342, by rfl⟩ : syracuseStep 427123 = 640685) B640685
theorem B427139 : Blo 424774 427139 := bstep (se 1 (by rfl) ⟨320354, by rfl⟩ : syracuseStep 427139 = 640709) B640709
theorem B656531 : Blo 424774 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B427155 : Blo 424774 427155 := bstep (se 1 (by rfl) ⟨320366, by rfl⟩ : syracuseStep 427155 = 640733) B640733
theorem B722081 : Blo 424774 722081 := bstep (se 2 (by rfl) ⟨270780, by rfl⟩ : syracuseStep 722081 = 541561) B541561
theorem B427171 : Blo 424774 427171 := bstep (se 1 (by rfl) ⟨320378, by rfl⟩ : syracuseStep 427171 = 640757) B640757
theorem B427187 : Blo 424774 427187 := bstep (se 1 (by rfl) ⟨320390, by rfl⟩ : syracuseStep 427187 = 640781) B640781
theorem B427203 : Blo 424774 427203 := bstep (se 1 (by rfl) ⟨320402, by rfl⟩ : syracuseStep 427203 = 640805) B640805
theorem B1213649 : Blo 424774 1213649 := bstep (se 2 (by rfl) ⟨455118, by rfl⟩ : syracuseStep 1213649 = 910237) B910237
theorem B820433 : Blo 424774 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B427219 : Blo 424774 427219 := bstep (se 1 (by rfl) ⟨320414, by rfl⟩ : syracuseStep 427219 = 640829) B640829
theorem B427235 : Blo 424774 427235 := bstep (se 1 (by rfl) ⟨320426, by rfl⟩ : syracuseStep 427235 = 640853) B640853
theorem B427251 : Blo 424774 427251 := bstep (se 1 (by rfl) ⟨320438, by rfl⟩ : syracuseStep 427251 = 640877) B640877
theorem B427267 : Blo 424774 427267 := bstep (se 1 (by rfl) ⟨320450, by rfl⟩ : syracuseStep 427267 = 640901) B640901
theorem B427283 : Blo 424774 427283 := bstep (se 1 (by rfl) ⟨320462, by rfl⟩ : syracuseStep 427283 = 640925) B640925
theorem B722209 : Blo 424774 722209 := bstep (se 2 (by rfl) ⟨270828, by rfl⟩ : syracuseStep 722209 = 541657) B541657
theorem B427299 : Blo 424774 427299 := bstep (se 1 (by rfl) ⟨320474, by rfl⟩ : syracuseStep 427299 = 640949) B640949
theorem B2590001 : Blo 424774 2590001 := bstep (se 2 (by rfl) ⟨971250, by rfl⟩ : syracuseStep 2590001 = 1942501) B1942501
theorem B427315 : Blo 424774 427315 := bstep (se 1 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 427315 = 640973) B640973
theorem B427331 : Blo 424774 427331 := bstep (se 1 (by rfl) ⟨320498, by rfl⟩ : syracuseStep 427331 = 640997) B640997
theorem B722243 : Blo 424774 722243 := bstep (se 1 (by rfl) ⟨541682, by rfl⟩ : syracuseStep 722243 = 1083365) B1083365
theorem B1443149 : Blo 424774 1443149 := bstep (se 3 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 1443149 = 541181) B541181
theorem B427347 : Blo 424774 427347 := bstep (se 1 (by rfl) ⟨320510, by rfl⟩ : syracuseStep 427347 = 641021) B641021
theorem B427363 : Blo 424774 427363 := bstep (se 1 (by rfl) ⟨320522, by rfl⟩ : syracuseStep 427363 = 641045) B641045
theorem B427379 : Blo 424774 427379 := bstep (se 1 (by rfl) ⟨320534, by rfl⟩ : syracuseStep 427379 = 641069) B641069
theorem B427395 : Blo 424774 427395 := bstep (se 1 (by rfl) ⟨320546, by rfl⟩ : syracuseStep 427395 = 641093) B641093
theorem B1443203 : Blo 424774 1443203 := bstep (se 1 (by rfl) ⟨1082402, by rfl⟩ : syracuseStep 1443203 = 2164805) B2164805
theorem B427411 : Blo 424774 427411 := bstep (se 1 (by rfl) ⟨320558, by rfl⟩ : syracuseStep 427411 = 641117) B641117
theorem B427427 : Blo 424774 427427 := bstep (se 1 (by rfl) ⟨320570, by rfl⟩ : syracuseStep 427427 = 641141) B641141
theorem B427443 : Blo 424774 427443 := bstep (se 1 (by rfl) ⟨320582, by rfl⟩ : syracuseStep 427443 = 641165) B641165
theorem B427459 : Blo 424774 427459 := bstep (se 1 (by rfl) ⟨320594, by rfl⟩ : syracuseStep 427459 = 641189) B641189
theorem B722371 : Blo 424774 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B427475 : Blo 424774 427475 := bstep (se 1 (by rfl) ⟨320606, by rfl⟩ : syracuseStep 427475 = 641213) B641213
theorem B427491 : Blo 424774 427491 := bstep (se 1 (by rfl) ⟨320618, by rfl⟩ : syracuseStep 427491 = 641237) B641237
theorem B427507 : Blo 424774 427507 := bstep (se 1 (by rfl) ⟨320630, by rfl⟩ : syracuseStep 427507 = 641261) B641261
theorem B427523 : Blo 424774 427523 := bstep (se 1 (by rfl) ⟨320642, by rfl⟩ : syracuseStep 427523 = 641285) B641285
theorem B427539 : Blo 424774 427539 := bstep (se 1 (by rfl) ⟨320654, by rfl⟩ : syracuseStep 427539 = 641309) B641309
theorem B427555 : Blo 424774 427555 := bstep (se 1 (by rfl) ⟨320666, by rfl⟩ : syracuseStep 427555 = 641333) B641333
theorem B1082929 : Blo 424774 1082929 := bstep (se 2 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 1082929 = 812197) B812197
theorem B427571 : Blo 424774 427571 := bstep (se 1 (by rfl) ⟨320678, by rfl⟩ : syracuseStep 427571 = 641357) B641357
theorem B427587 : Blo 424774 427587 := bstep (se 1 (by rfl) ⟨320690, by rfl⟩ : syracuseStep 427587 = 641381) B641381
theorem B722513 : Blo 424774 722513 := bstep (se 2 (by rfl) ⟨270942, by rfl⟩ : syracuseStep 722513 = 541885) B541885
theorem B427603 : Blo 424774 427603 := bstep (se 1 (by rfl) ⟨320702, by rfl⟩ : syracuseStep 427603 = 641405) B641405
theorem B427619 : Blo 424774 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B427635 : Blo 424774 427635 := bstep (se 1 (by rfl) ⟨320726, by rfl⟩ : syracuseStep 427635 = 641453) B641453
theorem B427651 : Blo 424774 427651 := bstep (se 1 (by rfl) ⟨320738, by rfl⟩ : syracuseStep 427651 = 641477) B641477
theorem B1443473 : Blo 424774 1443473 := bstep (se 2 (by rfl) ⟨541302, by rfl⟩ : syracuseStep 1443473 = 1082605) B1082605
theorem B427667 : Blo 424774 427667 := bstep (se 1 (by rfl) ⟨320750, by rfl⟩ : syracuseStep 427667 = 641501) B641501
theorem B427683 : Blo 424774 427683 := bstep (se 1 (by rfl) ⟨320762, by rfl⟩ : syracuseStep 427683 = 641525) B641525
theorem B427699 : Blo 424774 427699 := bstep (se 1 (by rfl) ⟨320774, by rfl⟩ : syracuseStep 427699 = 641549) B641549
theorem B427715 : Blo 424774 427715 := bstep (se 1 (by rfl) ⟨320786, by rfl⟩ : syracuseStep 427715 = 641573) B641573
theorem B722641 : Blo 424774 722641 := bstep (se 2 (by rfl) ⟨270990, by rfl⟩ : syracuseStep 722641 = 541981) B541981
theorem B427731 : Blo 424774 427731 := bstep (se 1 (by rfl) ⟨320798, by rfl⟩ : syracuseStep 427731 = 641597) B641597
theorem B427747 : Blo 424774 427747 := bstep (se 1 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 427747 = 641621) B641621
theorem B427763 : Blo 424774 427763 := bstep (se 1 (by rfl) ⟨320822, by rfl⟩ : syracuseStep 427763 = 641645) B641645
theorem B722675 : Blo 424774 722675 := bstep (se 1 (by rfl) ⟨542006, by rfl⟩ : syracuseStep 722675 = 1084013) B1084013
theorem B427779 : Blo 424774 427779 := bstep (se 1 (by rfl) ⟨320834, by rfl⟩ : syracuseStep 427779 = 641669) B641669
theorem B427795 : Blo 424774 427795 := bstep (se 1 (by rfl) ⟨320846, by rfl⟩ : syracuseStep 427795 = 641693) B641693
theorem B427811 : Blo 424774 427811 := bstep (se 1 (by rfl) ⟨320858, by rfl⟩ : syracuseStep 427811 = 641717) B641717
theorem B427827 : Blo 424774 427827 := bstep (se 1 (by rfl) ⟨320870, by rfl⟩ : syracuseStep 427827 = 641741) B641741
theorem B427843 : Blo 424774 427843 := bstep (se 1 (by rfl) ⟨320882, by rfl⟩ : syracuseStep 427843 = 641765) B641765
theorem B1083203 : Blo 424774 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B427859 : Blo 424774 427859 := bstep (se 1 (by rfl) ⟨320894, by rfl⟩ : syracuseStep 427859 = 641789) B641789
theorem B427875 : Blo 424774 427875 := bstep (se 1 (by rfl) ⟨320906, by rfl⟩ : syracuseStep 427875 = 641813) B641813
theorem B427891 : Blo 424774 427891 := bstep (se 1 (by rfl) ⟨320918, by rfl⟩ : syracuseStep 427891 = 641837) B641837
theorem B722803 : Blo 424774 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B427907 : Blo 424774 427907 := bstep (se 1 (by rfl) ⟨320930, by rfl⟩ : syracuseStep 427907 = 641861) B641861
theorem B427923 : Blo 424774 427923 := bstep (se 1 (by rfl) ⟨320942, by rfl⟩ : syracuseStep 427923 = 641885) B641885
theorem B2164643 : Blo 424774 2164643 := bstep (se 1 (by rfl) ⟨1623482, by rfl⟩ : syracuseStep 2164643 = 3246965) B3246965
theorem B427939 : Blo 424774 427939 := bstep (se 1 (by rfl) ⟨320954, by rfl⟩ : syracuseStep 427939 = 641909) B641909
theorem B690097 : Blo 424774 690097 := bstep (se 2 (by rfl) ⟨258786, by rfl⟩ : syracuseStep 690097 = 517573) B517573
theorem B427955 : Blo 424774 427955 := bstep (se 1 (by rfl) ⟨320966, by rfl⟩ : syracuseStep 427955 = 641933) B641933
theorem B427971 : Blo 424774 427971 := bstep (se 1 (by rfl) ⟨320978, by rfl⟩ : syracuseStep 427971 = 641957) B641957
theorem B427987 : Blo 424774 427987 := bstep (se 1 (by rfl) ⟨320990, by rfl⟩ : syracuseStep 427987 = 641981) B641981
theorem B428003 : Blo 424774 428003 := bstep (se 1 (by rfl) ⟨321002, by rfl⟩ : syracuseStep 428003 = 642005) B642005
theorem B428019 : Blo 424774 428019 := bstep (se 1 (by rfl) ⟨321014, by rfl⟩ : syracuseStep 428019 = 642029) B642029
theorem B722945 : Blo 424774 722945 := bstep (se 2 (by rfl) ⟨271104, by rfl⟩ : syracuseStep 722945 = 542209) B542209
theorem B1083395 : Blo 424774 1083395 := bstep (se 1 (by rfl) ⟨812546, by rfl⟩ : syracuseStep 1083395 = 1625093) B1625093
theorem B428035 : Blo 424774 428035 := bstep (se 1 (by rfl) ⟨321026, by rfl⟩ : syracuseStep 428035 = 642053) B642053
theorem B428051 : Blo 424774 428051 := bstep (se 1 (by rfl) ⟨321038, by rfl⟩ : syracuseStep 428051 = 642077) B642077
theorem B428067 : Blo 424774 428067 := bstep (se 1 (by rfl) ⟨321050, by rfl⟩ : syracuseStep 428067 = 642101) B642101
theorem B428083 : Blo 424774 428083 := bstep (se 1 (by rfl) ⟨321062, by rfl⟩ : syracuseStep 428083 = 642125) B642125
theorem B428099 : Blo 424774 428099 := bstep (se 1 (by rfl) ⟨321074, by rfl⟩ : syracuseStep 428099 = 642149) B642149
theorem B428115 : Blo 424774 428115 := bstep (se 1 (by rfl) ⟨321086, by rfl⟩ : syracuseStep 428115 = 642173) B642173
theorem B428131 : Blo 424774 428131 := bstep (se 1 (by rfl) ⟨321098, by rfl⟩ : syracuseStep 428131 = 642197) B642197
theorem B428147 : Blo 424774 428147 := bstep (se 1 (by rfl) ⟨321110, by rfl⟩ : syracuseStep 428147 = 642221) B642221
theorem B723073 : Blo 424774 723073 := bstep (se 2 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 723073 = 542305) B542305
theorem B428163 : Blo 424774 428163 := bstep (se 1 (by rfl) ⟨321122, by rfl⟩ : syracuseStep 428163 = 642245) B642245
theorem B1214605 : Blo 424774 1214605 := bstep (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) B455477
theorem B428179 : Blo 424774 428179 := bstep (se 1 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 428179 = 642269) B642269
theorem B428195 : Blo 424774 428195 := bstep (se 1 (by rfl) ⟨321146, by rfl⟩ : syracuseStep 428195 = 642293) B642293
theorem B723107 : Blo 424774 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B1444013 : Blo 424774 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B428211 : Blo 424774 428211 := bstep (se 1 (by rfl) ⟨321158, by rfl⟩ : syracuseStep 428211 = 642317) B642317
theorem B428227 : Blo 424774 428227 := bstep (se 1 (by rfl) ⟨321170, by rfl⟩ : syracuseStep 428227 = 642341) B642341
theorem B428243 : Blo 424774 428243 := bstep (se 1 (by rfl) ⟨321182, by rfl⟩ : syracuseStep 428243 = 642365) B642365
theorem B1444067 : Blo 424774 1444067 := bstep (se 1 (by rfl) ⟨1083050, by rfl⟩ : syracuseStep 1444067 = 2166101) B2166101
theorem B428259 : Blo 424774 428259 := bstep (se 1 (by rfl) ⟨321194, by rfl⟩ : syracuseStep 428259 = 642389) B642389
theorem B428275 : Blo 424774 428275 := bstep (se 1 (by rfl) ⟨321206, by rfl⟩ : syracuseStep 428275 = 642413) B642413
theorem B428291 : Blo 424774 428291 := bstep (se 1 (by rfl) ⟨321218, by rfl⟩ : syracuseStep 428291 = 642437) B642437
theorem B428307 : Blo 424774 428307 := bstep (se 1 (by rfl) ⟨321230, by rfl⟩ : syracuseStep 428307 = 642461) B642461
theorem B428323 : Blo 424774 428323 := bstep (se 1 (by rfl) ⟨321242, by rfl⟩ : syracuseStep 428323 = 642485) B642485
theorem B723235 : Blo 424774 723235 := bstep (se 1 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 723235 = 1084853) B1084853
theorem B428339 : Blo 424774 428339 := bstep (se 1 (by rfl) ⟨321254, by rfl⟩ : syracuseStep 428339 = 642509) B642509
theorem B428355 : Blo 424774 428355 := bstep (se 1 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 428355 = 642533) B642533
theorem B2427205 : Blo 424774 2427205 := bstep (se 4 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 2427205 = 455101) B455101
theorem B428371 : Blo 424774 428371 := bstep (se 1 (by rfl) ⟨321278, by rfl⟩ : syracuseStep 428371 = 642557) B642557
theorem B3279203 : Blo 424774 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B428387 : Blo 424774 428387 := bstep (se 1 (by rfl) ⟨321290, by rfl⟩ : syracuseStep 428387 = 642581) B642581
theorem B1214833 : Blo 424774 1214833 := bstep (se 2 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 1214833 = 911125) B911125
theorem B428403 : Blo 424774 428403 := bstep (se 1 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 428403 = 642605) B642605
theorem B428419 : Blo 424774 428419 := bstep (se 1 (by rfl) ⟨321314, by rfl⟩ : syracuseStep 428419 = 642629) B642629
theorem B428435 : Blo 424774 428435 := bstep (se 1 (by rfl) ⟨321326, by rfl⟩ : syracuseStep 428435 = 642653) B642653
theorem B428451 : Blo 424774 428451 := bstep (se 1 (by rfl) ⟨321338, by rfl⟩ : syracuseStep 428451 = 642677) B642677
theorem B723377 : Blo 424774 723377 := bstep (se 2 (by rfl) ⟨271266, by rfl⟩ : syracuseStep 723377 = 542533) B542533
theorem B428467 : Blo 424774 428467 := bstep (se 1 (by rfl) ⟨321350, by rfl⟩ : syracuseStep 428467 = 642701) B642701
theorem B428483 : Blo 424774 428483 := bstep (se 1 (by rfl) ⟨321362, by rfl⟩ : syracuseStep 428483 = 642725) B642725
theorem B428499 : Blo 424774 428499 := bstep (se 1 (by rfl) ⟨321374, by rfl⟩ : syracuseStep 428499 = 642749) B642749
theorem B428515 : Blo 424774 428515 := bstep (se 1 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 428515 = 642773) B642773
theorem B1444337 : Blo 424774 1444337 := bstep (se 2 (by rfl) ⟨541626, by rfl⟩ : syracuseStep 1444337 = 1083253) B1083253
theorem B428531 : Blo 424774 428531 := bstep (se 1 (by rfl) ⟨321398, by rfl⟩ : syracuseStep 428531 = 642797) B642797
theorem B428547 : Blo 424774 428547 := bstep (se 1 (by rfl) ⟨321410, by rfl⟩ : syracuseStep 428547 = 642821) B642821
theorem B1149457 : Blo 424774 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B1214993 : Blo 424774 1214993 := bstep (se 2 (by rfl) ⟨455622, by rfl⟩ : syracuseStep 1214993 = 911245) B911245
theorem B428563 : Blo 424774 428563 := bstep (se 1 (by rfl) ⟨321422, by rfl⟩ : syracuseStep 428563 = 642845) B642845
theorem B428579 : Blo 424774 428579 := bstep (se 1 (by rfl) ⟨321434, by rfl⟩ : syracuseStep 428579 = 642869) B642869
theorem B723505 : Blo 424774 723505 := bstep (se 2 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 723505 = 542629) B542629
theorem B428595 : Blo 424774 428595 := bstep (se 1 (by rfl) ⟨321446, by rfl⟩ : syracuseStep 428595 = 642893) B642893
theorem B428611 : Blo 424774 428611 := bstep (se 1 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 428611 = 642917) B642917
theorem B428627 : Blo 424774 428627 := bstep (se 1 (by rfl) ⟨321470, by rfl⟩ : syracuseStep 428627 = 642941) B642941
theorem B723539 : Blo 424774 723539 := bstep (se 1 (by rfl) ⟨542654, by rfl⟩ : syracuseStep 723539 = 1085309) B1085309
theorem B428643 : Blo 424774 428643 := bstep (se 1 (by rfl) ⟨321482, by rfl⟩ : syracuseStep 428643 = 642965) B642965
theorem B428659 : Blo 424774 428659 := bstep (se 1 (by rfl) ⟨321494, by rfl⟩ : syracuseStep 428659 = 642989) B642989
theorem B1215107 : Blo 424774 1215107 := bstep (se 1 (by rfl) ⟨911330, by rfl⟩ : syracuseStep 1215107 = 1822661) B1822661
theorem B428675 : Blo 424774 428675 := bstep (se 1 (by rfl) ⟨321506, by rfl⟩ : syracuseStep 428675 = 643013) B643013
theorem B428691 : Blo 424774 428691 := bstep (se 1 (by rfl) ⟨321518, by rfl⟩ : syracuseStep 428691 = 643037) B643037
theorem B428707 : Blo 424774 428707 := bstep (se 1 (by rfl) ⟨321530, by rfl⟩ : syracuseStep 428707 = 643061) B643061
theorem B428723 : Blo 424774 428723 := bstep (se 1 (by rfl) ⟨321542, by rfl⟩ : syracuseStep 428723 = 643085) B643085
theorem B428739 : Blo 424774 428739 := bstep (se 1 (by rfl) ⟨321554, by rfl⟩ : syracuseStep 428739 = 643109) B643109
theorem B2165453 : Blo 424774 2165453 := bstep (se 3 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 2165453 = 812045) B812045
theorem B428755 : Blo 424774 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B428771 : Blo 424774 428771 := bstep (se 1 (by rfl) ⟨321578, by rfl⟩ : syracuseStep 428771 = 643157) B643157
theorem B1542989 : Blo 424774 1542989 := bstep (se 3 (by rfl) ⟨289310, by rfl⟩ : syracuseStep 1542989 = 578621) B578621
theorem B1641329 : Blo 424774 1641329 := bstep (se 2 (by rfl) ⟨615498, by rfl⟩ : syracuseStep 1641329 = 1230997) B1230997
theorem B1084337 : Blo 424774 1084337 := bstep (se 2 (by rfl) ⟨406626, by rfl⟩ : syracuseStep 1084337 = 813253) B813253
theorem B3640261 : Blo 424774 3640261 := bstep (se 4 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 3640261 = 682549) B682549
theorem B1543117 : Blo 424774 1543117 := bstep (se 3 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 1543117 = 578669) B578669
theorem B1084387 : Blo 424774 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B1444877 : Blo 424774 1444877 := bstep (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) B541829
theorem B1444931 : Blo 424774 1444931 := bstep (se 1 (by rfl) ⟨1083698, by rfl⟩ : syracuseStep 1444931 = 2167397) B2167397
theorem B1084529 : Blo 424774 1084529 := bstep (se 2 (by rfl) ⟨406698, by rfl⟩ : syracuseStep 1084529 = 813397) B813397
theorem B2723021 : Blo 424774 2723021 := bstep (se 3 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 2723021 = 1021133) B1021133
theorem B1445201 : Blo 424774 1445201 := bstep (se 2 (by rfl) ⟨541950, by rfl⟩ : syracuseStep 1445201 = 1083901) B1083901
theorem B1216109 : Blo 424774 1216109 := bstep (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) B456041
theorem B1216291 : Blo 424774 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B1445741 : Blo 424774 1445741 := bstep (se 3 (by rfl) ⟨271076, by rfl⟩ : syracuseStep 1445741 = 542153) B542153
theorem B1445795 : Blo 424774 1445795 := bstep (se 1 (by rfl) ⟨1084346, by rfl⟩ : syracuseStep 1445795 = 2168693) B2168693
theorem B1216451 : Blo 424774 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B1446065 : Blo 424774 1446065 := bstep (se 2 (by rfl) ⟨542274, by rfl⟩ : syracuseStep 1446065 = 1084549) B1084549
theorem B659683 : Blo 424774 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B2429189 : Blo 424774 2429189 := bstep (se 4 (by rfl) ⟨227736, by rfl⟩ : syracuseStep 2429189 = 455473) B455473
theorem B1151533 : Blo 424774 1151533 := bstep (se 3 (by rfl) ⟨215912, by rfl⟩ : syracuseStep 1151533 = 431825) B431825
theorem B1151587 : Blo 424774 1151587 := bstep (se 1 (by rfl) ⟨863690, by rfl⟩ : syracuseStep 1151587 = 1727381) B1727381
theorem B10359409 : Blo 424774 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B1446605 : Blo 424774 1446605 := bstep (se 3 (by rfl) ⟨271238, by rfl⟩ : syracuseStep 1446605 = 542477) B542477
theorem B1446659 : Blo 424774 1446659 := bstep (se 1 (by rfl) ⟨1084994, by rfl⟩ : syracuseStep 1446659 = 2169989) B2169989
theorem B3248909 : Blo 424774 3248909 := bstep (se 3 (by rfl) ⟨609170, by rfl⟩ : syracuseStep 3248909 = 1218341) B1218341
theorem B1217521 : Blo 424774 1217521 := bstep (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) B913141
theorem B1446929 : Blo 424774 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B4101445 : Blo 424774 4101445 := bstep (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) B769021
theorem B4855139 : Blo 424774 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B2069965 : Blo 424774 2069965 := bstep (se 3 (by rfl) ⟨388118, by rfl⟩ : syracuseStep 2069965 = 776237) B776237
theorem B3282403 : Blo 424774 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B955889 : Blo 424774 955889 := bstep (se 2 (by rfl) ⟨358458, by rfl⟩ : syracuseStep 955889 = 716917) B716917
theorem B955907 : Blo 424774 955907 := bstep (se 1 (by rfl) ⟨716930, by rfl⟩ : syracuseStep 955907 = 1433861) B1433861
theorem B2168369 : Blo 424774 2168369 := bstep (se 2 (by rfl) ⟨813138, by rfl⟩ : syracuseStep 2168369 = 1626277) B1626277
theorem B956177 : Blo 424774 956177 := bstep (se 2 (by rfl) ⟨358566, by rfl⟩ : syracuseStep 956177 = 717133) B717133
theorem B956195 : Blo 424774 956195 := bstep (se 1 (by rfl) ⟨717146, by rfl⟩ : syracuseStep 956195 = 1434293) B1434293
theorem B956465 : Blo 424774 956465 := bstep (se 2 (by rfl) ⟨358674, by rfl⟩ : syracuseStep 956465 = 717349) B717349
theorem B956483 : Blo 424774 956483 := bstep (se 1 (by rfl) ⟨717362, by rfl⟩ : syracuseStep 956483 = 1434725) B1434725
theorem B1153091 : Blo 424774 1153091 := bstep (se 1 (by rfl) ⟨864818, by rfl⟩ : syracuseStep 1153091 = 1729637) B1729637
theorem B1218797 : Blo 424774 1218797 := bstep (se 3 (by rfl) ⟨228524, by rfl⟩ : syracuseStep 1218797 = 457049) B457049
theorem B956753 : Blo 424774 956753 := bstep (se 2 (by rfl) ⟨358782, by rfl⟩ : syracuseStep 956753 = 717565) B717565
theorem B956771 : Blo 424774 956771 := bstep (se 1 (by rfl) ⟨717578, by rfl⟩ : syracuseStep 956771 = 1435157) B1435157
theorem B1218979 : Blo 424774 1218979 := bstep (se 1 (by rfl) ⟨914234, by rfl⟩ : syracuseStep 1218979 = 1828469) B1828469
theorem B1153489 : Blo 424774 1153489 := bstep (se 2 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 1153489 = 865117) B865117
theorem B1219025 : Blo 424774 1219025 := bstep (se 2 (by rfl) ⟨457134, by rfl⟩ : syracuseStep 1219025 = 914269) B914269
theorem B2726405 : Blo 424774 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B957041 : Blo 424774 957041 := bstep (se 2 (by rfl) ⟨358890, by rfl⟩ : syracuseStep 957041 = 717781) B717781
theorem B957059 : Blo 424774 957059 := bstep (se 1 (by rfl) ⟨717794, by rfl⟩ : syracuseStep 957059 = 1435589) B1435589
theorem B957329 : Blo 424774 957329 := bstep (se 2 (by rfl) ⟨358998, by rfl⟩ : syracuseStep 957329 = 717997) B717997
theorem B957347 : Blo 424774 957347 := bstep (se 1 (by rfl) ⟨718010, by rfl⟩ : syracuseStep 957347 = 1436021) B1436021
theorem B2169827 : Blo 424774 2169827 := bstep (se 1 (by rfl) ⟨1627370, by rfl⟩ : syracuseStep 2169827 = 3254741) B3254741
theorem B957617 : Blo 424774 957617 := bstep (se 2 (by rfl) ⟨359106, by rfl⟩ : syracuseStep 957617 = 718213) B718213
theorem B957635 : Blo 424774 957635 := bstep (se 1 (by rfl) ⟨718226, by rfl⟩ : syracuseStep 957635 = 1436453) B1436453
theorem B433459 : Blo 424774 433459 := bstep (se 1 (by rfl) ⟨325094, by rfl⟩ : syracuseStep 433459 = 650189) B650189
theorem B1613155 : Blo 424774 1613155 := bstep (se 1 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 1613155 = 2419733) B2419733
theorem B1383857 : Blo 424774 1383857 := bstep (se 2 (by rfl) ⟨518946, by rfl⟩ : syracuseStep 1383857 = 1037893) B1037893
theorem B957905 : Blo 424774 957905 := bstep (se 2 (by rfl) ⟨359214, by rfl⟩ : syracuseStep 957905 = 718429) B718429
theorem B957923 : Blo 424774 957923 := bstep (se 1 (by rfl) ⟨718442, by rfl⟩ : syracuseStep 957923 = 1436885) B1436885
theorem B5283427 : Blo 424774 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B3251825 : Blo 424774 3251825 := bstep (se 2 (by rfl) ⟨1219434, by rfl⟩ : syracuseStep 3251825 = 2438869) B2438869
theorem B958193 : Blo 424774 958193 := bstep (se 2 (by rfl) ⟨359322, by rfl⟩ : syracuseStep 958193 = 718645) B718645
theorem B958211 : Blo 424774 958211 := bstep (se 1 (by rfl) ⟨718658, by rfl⟩ : syracuseStep 958211 = 1437317) B1437317
theorem B2170637 : Blo 424774 2170637 := bstep (se 3 (by rfl) ⟨406994, by rfl⟩ : syracuseStep 2170637 = 813989) B813989
theorem B6168433 : Blo 424774 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B1220483 : Blo 424774 1220483 := bstep (se 1 (by rfl) ⟨915362, by rfl⟩ : syracuseStep 1220483 = 1830725) B1830725
theorem B2334691 : Blo 424774 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B729089 : Blo 424774 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B2433037 : Blo 424774 2433037 := bstep (se 3 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 2433037 = 912389) B912389
theorem B958481 : Blo 424774 958481 := bstep (se 2 (by rfl) ⟨359430, by rfl⟩ : syracuseStep 958481 = 718861) B718861
theorem B958499 : Blo 424774 958499 := bstep (se 1 (by rfl) ⟨718874, by rfl⟩ : syracuseStep 958499 = 1437749) B1437749
theorem B729361 : Blo 424774 729361 := bstep (se 2 (by rfl) ⟨273510, by rfl⟩ : syracuseStep 729361 = 547021) B547021
theorem B958769 : Blo 424774 958769 := bstep (se 2 (by rfl) ⟨359538, by rfl⟩ : syracuseStep 958769 = 719077) B719077
theorem B958787 : Blo 424774 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B926147 : Blo 424774 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B959057 : Blo 424774 959057 := bstep (se 2 (by rfl) ⟨359646, by rfl⟩ : syracuseStep 959057 = 719293) B719293
theorem B959075 : Blo 424774 959075 := bstep (se 1 (by rfl) ⟨719306, by rfl⟩ : syracuseStep 959075 = 1438613) B1438613
theorem B2073251 : Blo 424774 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B1188515 : Blo 424774 1188515 := bstep (se 1 (by rfl) ⟨891386, by rfl⟩ : syracuseStep 1188515 = 1782773) B1782773
theorem B959345 : Blo 424774 959345 := bstep (se 2 (by rfl) ⟨359754, by rfl⟩ : syracuseStep 959345 = 719509) B719509
theorem B959363 : Blo 424774 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B2761613 : Blo 424774 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B730019 : Blo 424774 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B959633 : Blo 424774 959633 := bstep (se 2 (by rfl) ⟨359862, by rfl⟩ : syracuseStep 959633 = 719725) B719725
theorem B959651 : Blo 424774 959651 := bstep (se 1 (by rfl) ⟨719738, by rfl⟩ : syracuseStep 959651 = 1439477) B1439477
theorem B959921 : Blo 424774 959921 := bstep (se 2 (by rfl) ⟨359970, by rfl⟩ : syracuseStep 959921 = 719941) B719941
theorem B959939 : Blo 424774 959939 := bstep (se 1 (by rfl) ⟨719954, by rfl⟩ : syracuseStep 959939 = 1439909) B1439909
theorem B1615373 : Blo 424774 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B1025585 : Blo 424774 1025585 := bstep (se 2 (by rfl) ⟨384594, by rfl⟩ : syracuseStep 1025585 = 769189) B769189
theorem B960209 : Blo 424774 960209 := bstep (se 2 (by rfl) ⟨360078, by rfl⟩ : syracuseStep 960209 = 720157) B720157
theorem B960227 : Blo 424774 960227 := bstep (se 1 (by rfl) ⟨720170, by rfl⟩ : syracuseStep 960227 = 1440341) B1440341
theorem B2598733 : Blo 424774 2598733 := bstep (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) B974525
theorem B2435021 : Blo 424774 2435021 := bstep (se 3 (by rfl) ⟨456566, by rfl⟩ : syracuseStep 2435021 = 913133) B913133
theorem B2729969 : Blo 424774 2729969 := bstep (se 2 (by rfl) ⟨1023738, by rfl⟩ : syracuseStep 2729969 = 2047477) B2047477
theorem B960497 : Blo 424774 960497 := bstep (se 2 (by rfl) ⟨360186, by rfl⟩ : syracuseStep 960497 = 720373) B720373
theorem B960515 : Blo 424774 960515 := bstep (se 1 (by rfl) ⟨720386, by rfl⟩ : syracuseStep 960515 = 1440773) B1440773
theorem B7317701 : Blo 424774 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B7416035 : Blo 424774 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B960785 : Blo 424774 960785 := bstep (se 2 (by rfl) ⟨360294, by rfl⟩ : syracuseStep 960785 = 720589) B720589
theorem B960803 : Blo 424774 960803 := bstep (se 1 (by rfl) ⟨720602, by rfl⟩ : syracuseStep 960803 = 1441205) B1441205
theorem B1026353 : Blo 424774 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B961073 : Blo 424774 961073 := bstep (se 2 (by rfl) ⟨360402, by rfl⟩ : syracuseStep 961073 = 720805) B720805
theorem B961091 : Blo 424774 961091 := bstep (se 1 (by rfl) ⟨720818, by rfl⟩ : syracuseStep 961091 = 1441637) B1441637
theorem B2501381 : Blo 424774 2501381 := bstep (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) B469009
theorem B961361 : Blo 424774 961361 := bstep (se 2 (by rfl) ⟨360510, by rfl⟩ : syracuseStep 961361 = 721021) B721021
theorem B961379 : Blo 424774 961379 := bstep (se 1 (by rfl) ⟨721034, by rfl⟩ : syracuseStep 961379 = 1442069) B1442069
theorem B2435953 : Blo 424774 2435953 := bstep (se 2 (by rfl) ⟨913482, by rfl⟩ : syracuseStep 2435953 = 1826965) B1826965
theorem B961649 : Blo 424774 961649 := bstep (se 2 (by rfl) ⟨360618, by rfl⟩ : syracuseStep 961649 = 721237) B721237
theorem B961667 : Blo 424774 961667 := bstep (se 1 (by rfl) ⟨721250, by rfl⟩ : syracuseStep 961667 = 1442501) B1442501
theorem B1649933 : Blo 424774 1649933 := bstep (se 3 (by rfl) ⟨309362, by rfl⟩ : syracuseStep 1649933 = 618725) B618725
theorem B961937 : Blo 424774 961937 := bstep (se 2 (by rfl) ⟨360726, by rfl⟩ : syracuseStep 961937 = 721453) B721453
theorem B2731427 : Blo 424774 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B961955 : Blo 424774 961955 := bstep (se 1 (by rfl) ⟨721466, by rfl⟩ : syracuseStep 961955 = 1442933) B1442933
theorem B3649009 : Blo 424774 3649009 := bstep (se 2 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 3649009 = 2736757) B2736757
theorem B962225 : Blo 424774 962225 := bstep (se 2 (by rfl) ⟨360834, by rfl⟩ : syracuseStep 962225 = 721669) B721669
theorem B962243 : Blo 424774 962243 := bstep (se 1 (by rfl) ⟨721682, by rfl⟩ : syracuseStep 962243 = 1443365) B1443365
theorem B6074309 : Blo 424774 6074309 := bstep (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) B1138933
theorem B962513 : Blo 424774 962513 := bstep (se 2 (by rfl) ⟨360942, by rfl⟩ : syracuseStep 962513 = 721885) B721885
theorem B962531 : Blo 424774 962531 := bstep (se 1 (by rfl) ⟨721898, by rfl⟩ : syracuseStep 962531 = 1443797) B1443797
theorem B1028227 : Blo 424774 1028227 := bstep (se 1 (by rfl) ⟨771170, by rfl⟩ : syracuseStep 1028227 = 1542341) B1542341
theorem B962801 : Blo 424774 962801 := bstep (se 2 (by rfl) ⟨361050, by rfl⟩ : syracuseStep 962801 = 722101) B722101
theorem B962819 : Blo 424774 962819 := bstep (se 1 (by rfl) ⟨722114, by rfl⟩ : syracuseStep 962819 = 1444229) B1444229
theorem B2437411 : Blo 424774 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B1618289 : Blo 424774 1618289 := bstep (se 2 (by rfl) ⟨606858, by rfl⟩ : syracuseStep 1618289 = 1213717) B1213717
theorem B963089 : Blo 424774 963089 := bstep (se 2 (by rfl) ⟨361158, by rfl⟩ : syracuseStep 963089 = 722317) B722317
theorem B963107 : Blo 424774 963107 := bstep (se 1 (by rfl) ⟨722330, by rfl⟩ : syracuseStep 963107 = 1444661) B1444661
theorem B1454851 : Blo 424774 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B1815331 : Blo 424774 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B2437937 : Blo 424774 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B963377 : Blo 424774 963377 := bstep (se 2 (by rfl) ⟨361266, by rfl⟩ : syracuseStep 963377 = 722533) B722533
theorem B963395 : Blo 424774 963395 := bstep (se 1 (by rfl) ⟨722546, by rfl⟩ : syracuseStep 963395 = 1445093) B1445093
theorem B1455043 : Blo 424774 1455043 := bstep (se 1 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 1455043 = 2182565) B2182565
theorem B1094627 : Blo 424774 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B963665 : Blo 424774 963665 := bstep (se 2 (by rfl) ⟨361374, by rfl⟩ : syracuseStep 963665 = 722749) B722749
theorem B963683 : Blo 424774 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B2766001 : Blo 424774 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B537779 : Blo 424774 537779 := bstep (se 1 (by rfl) ⟨403334, by rfl⟩ : syracuseStep 537779 = 806669) B806669
theorem B767171 : Blo 424774 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B865475 : Blo 424774 865475 := bstep (se 1 (by rfl) ⟨649106, by rfl⟩ : syracuseStep 865475 = 1298213) B1298213
theorem B1455341 : Blo 424774 1455341 := bstep (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) B545753
theorem B963953 : Blo 424774 963953 := bstep (se 2 (by rfl) ⟨361482, by rfl⟩ : syracuseStep 963953 = 722965) B722965
theorem B963971 : Blo 424774 963971 := bstep (se 1 (by rfl) ⟨722978, by rfl⟩ : syracuseStep 963971 = 1445957) B1445957
theorem B1848845 : Blo 424774 1848845 := bstep (se 3 (by rfl) ⟨346658, by rfl⟩ : syracuseStep 1848845 = 693317) B693317
theorem B2078243 : Blo 424774 2078243 := bstep (se 1 (by rfl) ⟨1558682, by rfl⟩ : syracuseStep 2078243 = 3117365) B3117365
theorem B1226285 : Blo 424774 1226285 := bstep (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) B459857
theorem B964241 : Blo 424774 964241 := bstep (se 2 (by rfl) ⟨361590, by rfl⟩ : syracuseStep 964241 = 723181) B723181
theorem B964259 : Blo 424774 964259 := bstep (se 1 (by rfl) ⟨723194, by rfl⟩ : syracuseStep 964259 = 1446389) B1446389
theorem B1619747 : Blo 424774 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B1029937 : Blo 424774 1029937 := bstep (se 2 (by rfl) ⟨386226, by rfl⟩ : syracuseStep 1029937 = 772453) B772453
theorem B538483 : Blo 424774 538483 := bstep (se 1 (by rfl) ⟨403862, by rfl⟩ : syracuseStep 538483 = 807725) B807725
theorem B964529 : Blo 424774 964529 := bstep (se 2 (by rfl) ⟨361698, by rfl⟩ : syracuseStep 964529 = 723397) B723397
theorem B964547 : Blo 424774 964547 := bstep (se 1 (by rfl) ⟨723410, by rfl⟩ : syracuseStep 964547 = 1446821) B1446821
theorem B538579 : Blo 424774 538579 := bstep (se 1 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 538579 = 807869) B807869
theorem B2504753 : Blo 424774 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B2439395 : Blo 424774 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B637169 : Blo 424774 637169 := bstep (se 2 (by rfl) ⟨238938, by rfl⟩ : syracuseStep 637169 = 477877) B477877
theorem B637187 : Blo 424774 637187 := bstep (se 1 (by rfl) ⟨477890, by rfl⟩ : syracuseStep 637187 = 955781) B955781
theorem B637217 : Blo 424774 637217 := bstep (se 2 (by rfl) ⟨238956, by rfl⟩ : syracuseStep 637217 = 477913) B477913
theorem B637235 : Blo 424774 637235 := bstep (se 1 (by rfl) ⟨477926, by rfl⟩ : syracuseStep 637235 = 955853) B955853
theorem B637265 : Blo 424774 637265 := bstep (se 2 (by rfl) ⟨238974, by rfl⟩ : syracuseStep 637265 = 477949) B477949
theorem B637283 : Blo 424774 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B637313 : Blo 424774 637313 := bstep (se 2 (by rfl) ⟨238992, by rfl⟩ : syracuseStep 637313 = 477985) B477985
theorem B637331 : Blo 424774 637331 := bstep (se 1 (by rfl) ⟨477998, by rfl⟩ : syracuseStep 637331 = 955997) B955997
theorem B637361 : Blo 424774 637361 := bstep (se 2 (by rfl) ⟨239010, by rfl⟩ : syracuseStep 637361 = 478021) B478021
theorem B637379 : Blo 424774 637379 := bstep (se 1 (by rfl) ⟨478034, by rfl⟩ : syracuseStep 637379 = 956069) B956069
theorem B539075 : Blo 424774 539075 := bstep (se 1 (by rfl) ⟨404306, by rfl⟩ : syracuseStep 539075 = 808613) B808613
theorem B637409 : Blo 424774 637409 := bstep (se 2 (by rfl) ⟨239028, by rfl⟩ : syracuseStep 637409 = 478057) B478057
theorem B637427 : Blo 424774 637427 := bstep (se 1 (by rfl) ⟨478070, by rfl⟩ : syracuseStep 637427 = 956141) B956141
theorem B637457 : Blo 424774 637457 := bstep (se 2 (by rfl) ⟨239046, by rfl⟩ : syracuseStep 637457 = 478093) B478093
theorem B637475 : Blo 424774 637475 := bstep (se 1 (by rfl) ⟨478106, by rfl⟩ : syracuseStep 637475 = 956213) B956213
theorem B637505 : Blo 424774 637505 := bstep (se 2 (by rfl) ⟨239064, by rfl⟩ : syracuseStep 637505 = 478129) B478129
theorem B637523 : Blo 424774 637523 := bstep (se 1 (by rfl) ⟨478142, by rfl⟩ : syracuseStep 637523 = 956285) B956285
theorem B637553 : Blo 424774 637553 := bstep (se 2 (by rfl) ⟨239082, by rfl⟩ : syracuseStep 637553 = 478165) B478165
theorem B637571 : Blo 424774 637571 := bstep (se 1 (by rfl) ⟨478178, by rfl⟩ : syracuseStep 637571 = 956357) B956357
theorem B637601 : Blo 424774 637601 := bstep (se 2 (by rfl) ⟨239100, by rfl⟩ : syracuseStep 637601 = 478201) B478201
theorem B637619 : Blo 424774 637619 := bstep (se 1 (by rfl) ⟨478214, by rfl⟩ : syracuseStep 637619 = 956429) B956429
theorem B604865 : Blo 424774 604865 := bstep (se 2 (by rfl) ⟨226824, by rfl⟩ : syracuseStep 604865 = 453649) B453649
theorem B1293005 : Blo 424774 1293005 := bstep (se 3 (by rfl) ⟨242438, by rfl⟩ : syracuseStep 1293005 = 484877) B484877
theorem B637649 : Blo 424774 637649 := bstep (se 2 (by rfl) ⟨239118, by rfl⟩ : syracuseStep 637649 = 478237) B478237
theorem B637667 : Blo 424774 637667 := bstep (se 1 (by rfl) ⟨478250, by rfl⟩ : syracuseStep 637667 = 956501) B956501
theorem B1817329 : Blo 424774 1817329 := bstep (se 2 (by rfl) ⟨681498, by rfl⟩ : syracuseStep 1817329 = 1362997) B1362997
theorem B637697 : Blo 424774 637697 := bstep (se 2 (by rfl) ⟨239136, by rfl⟩ : syracuseStep 637697 = 478273) B478273
theorem B2931461 : Blo 424774 2931461 := bstep (se 4 (by rfl) ⟨274824, by rfl⟩ : syracuseStep 2931461 = 549649) B549649
theorem B1620749 : Blo 424774 1620749 := bstep (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) B607781
theorem B604945 : Blo 424774 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B637715 : Blo 424774 637715 := bstep (se 1 (by rfl) ⟨478286, by rfl⟩ : syracuseStep 637715 = 956573) B956573
theorem B637745 : Blo 424774 637745 := bstep (se 2 (by rfl) ⟨239154, by rfl⟩ : syracuseStep 637745 = 478309) B478309
theorem B637763 : Blo 424774 637763 := bstep (se 1 (by rfl) ⟨478322, by rfl⟩ : syracuseStep 637763 = 956645) B956645
theorem B637793 : Blo 424774 637793 := bstep (se 2 (by rfl) ⟨239172, by rfl⟩ : syracuseStep 637793 = 478345) B478345
theorem B637811 : Blo 424774 637811 := bstep (se 1 (by rfl) ⟨478358, by rfl⟩ : syracuseStep 637811 = 956717) B956717
theorem B637841 : Blo 424774 637841 := bstep (se 2 (by rfl) ⟨239190, by rfl⟩ : syracuseStep 637841 = 478381) B478381
theorem B637859 : Blo 424774 637859 := bstep (se 1 (by rfl) ⟨478394, by rfl⟩ : syracuseStep 637859 = 956789) B956789
theorem B637889 : Blo 424774 637889 := bstep (se 2 (by rfl) ⟨239208, by rfl⟩ : syracuseStep 637889 = 478417) B478417
theorem B637907 : Blo 424774 637907 := bstep (se 1 (by rfl) ⟨478430, by rfl⟩ : syracuseStep 637907 = 956861) B956861
theorem B637937 : Blo 424774 637937 := bstep (se 2 (by rfl) ⟨239226, by rfl⟩ : syracuseStep 637937 = 478453) B478453
theorem B637955 : Blo 424774 637955 := bstep (se 1 (by rfl) ⟨478466, by rfl⟩ : syracuseStep 637955 = 956933) B956933
theorem B2735117 : Blo 424774 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B637985 : Blo 424774 637985 := bstep (se 2 (by rfl) ⟨239244, by rfl⟩ : syracuseStep 637985 = 478489) B478489
theorem B638003 : Blo 424774 638003 := bstep (se 1 (by rfl) ⟨478502, by rfl⟩ : syracuseStep 638003 = 957005) B957005
theorem B638033 : Blo 424774 638033 := bstep (se 2 (by rfl) ⟨239262, by rfl⟩ : syracuseStep 638033 = 478525) B478525
theorem B932963 : Blo 424774 932963 := bstep (se 1 (by rfl) ⟨699722, by rfl⟩ : syracuseStep 932963 = 1399445) B1399445
theorem B638051 : Blo 424774 638051 := bstep (se 1 (by rfl) ⟨478538, by rfl⟩ : syracuseStep 638051 = 957077) B957077
theorem B1457261 : Blo 424774 1457261 := bstep (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) B546473
theorem B638081 : Blo 424774 638081 := bstep (se 2 (by rfl) ⟨239280, by rfl⟩ : syracuseStep 638081 = 478561) B478561
theorem B539779 : Blo 424774 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B638099 : Blo 424774 638099 := bstep (se 1 (by rfl) ⟨478574, by rfl⟩ : syracuseStep 638099 = 957149) B957149
theorem B638129 : Blo 424774 638129 := bstep (se 2 (by rfl) ⟨239298, by rfl⟩ : syracuseStep 638129 = 478597) B478597
theorem B638147 : Blo 424774 638147 := bstep (se 1 (by rfl) ⟨478610, by rfl⟩ : syracuseStep 638147 = 957221) B957221
theorem B638177 : Blo 424774 638177 := bstep (se 2 (by rfl) ⟨239316, by rfl⟩ : syracuseStep 638177 = 478633) B478633
theorem B539875 : Blo 424774 539875 := bstep (se 1 (by rfl) ⟨404906, by rfl⟩ : syracuseStep 539875 = 809813) B809813
theorem B638195 : Blo 424774 638195 := bstep (se 1 (by rfl) ⟨478646, by rfl⟩ : syracuseStep 638195 = 957293) B957293
theorem B638225 : Blo 424774 638225 := bstep (se 2 (by rfl) ⟨239334, by rfl⟩ : syracuseStep 638225 = 478669) B478669
theorem B638243 : Blo 424774 638243 := bstep (se 1 (by rfl) ⟨478682, by rfl⟩ : syracuseStep 638243 = 957365) B957365
theorem B638273 : Blo 424774 638273 := bstep (se 2 (by rfl) ⟨239352, by rfl⟩ : syracuseStep 638273 = 478705) B478705
theorem B638291 : Blo 424774 638291 := bstep (se 1 (by rfl) ⟨478718, by rfl⟩ : syracuseStep 638291 = 957437) B957437
theorem B638321 : Blo 424774 638321 := bstep (se 2 (by rfl) ⟨239370, by rfl⟩ : syracuseStep 638321 = 478741) B478741
theorem B638339 : Blo 424774 638339 := bstep (se 1 (by rfl) ⟨478754, by rfl⟩ : syracuseStep 638339 = 957509) B957509
theorem B638369 : Blo 424774 638369 := bstep (se 2 (by rfl) ⟨239388, by rfl⟩ : syracuseStep 638369 = 478777) B478777
theorem B638387 : Blo 424774 638387 := bstep (se 1 (by rfl) ⟨478790, by rfl⟩ : syracuseStep 638387 = 957581) B957581
theorem B5848517 : Blo 424774 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B638417 : Blo 424774 638417 := bstep (se 2 (by rfl) ⟨239406, by rfl⟩ : syracuseStep 638417 = 478813) B478813
theorem B638435 : Blo 424774 638435 := bstep (se 1 (by rfl) ⟨478826, by rfl⟩ : syracuseStep 638435 = 957653) B957653
theorem B835043 : Blo 424774 835043 := bstep (se 1 (by rfl) ⟨626282, by rfl⟩ : syracuseStep 835043 = 1252565) B1252565
theorem B638465 : Blo 424774 638465 := bstep (se 2 (by rfl) ⟨239424, by rfl⟩ : syracuseStep 638465 = 478849) B478849
theorem B5193229 : Blo 424774 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B638483 : Blo 424774 638483 := bstep (se 1 (by rfl) ⟨478862, by rfl⟩ : syracuseStep 638483 = 957725) B957725
theorem B605731 : Blo 424774 605731 := bstep (se 1 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 605731 = 908597) B908597
theorem B638513 : Blo 424774 638513 := bstep (se 2 (by rfl) ⟨239442, by rfl⟩ : syracuseStep 638513 = 478885) B478885
theorem B638531 : Blo 424774 638531 := bstep (se 1 (by rfl) ⟨478898, by rfl⟩ : syracuseStep 638531 = 957797) B957797
theorem B933457 : Blo 424774 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B638561 : Blo 424774 638561 := bstep (se 2 (by rfl) ⟨239460, by rfl⟩ : syracuseStep 638561 = 478921) B478921
theorem B638579 : Blo 424774 638579 := bstep (se 1 (by rfl) ⟨478934, by rfl⟩ : syracuseStep 638579 = 957869) B957869
theorem B638609 : Blo 424774 638609 := bstep (se 2 (by rfl) ⟨239478, by rfl⟩ : syracuseStep 638609 = 478957) B478957
theorem B638627 : Blo 424774 638627 := bstep (se 1 (by rfl) ⟨478970, by rfl⟩ : syracuseStep 638627 = 957941) B957941
theorem B638657 : Blo 424774 638657 := bstep (se 2 (by rfl) ⟨239496, by rfl⟩ : syracuseStep 638657 = 478993) B478993
theorem B638675 : Blo 424774 638675 := bstep (se 1 (by rfl) ⟨479006, by rfl⟩ : syracuseStep 638675 = 958013) B958013
theorem B540371 : Blo 424774 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B638705 : Blo 424774 638705 := bstep (se 2 (by rfl) ⟨239514, by rfl⟩ : syracuseStep 638705 = 479029) B479029
theorem B638723 : Blo 424774 638723 := bstep (se 1 (by rfl) ⟨479042, by rfl⟩ : syracuseStep 638723 = 958085) B958085
theorem B638753 : Blo 424774 638753 := bstep (se 2 (by rfl) ⟨239532, by rfl⟩ : syracuseStep 638753 = 479065) B479065
theorem B638771 : Blo 424774 638771 := bstep (se 1 (by rfl) ⟨479078, by rfl⟩ : syracuseStep 638771 = 958157) B958157
theorem B638801 : Blo 424774 638801 := bstep (se 2 (by rfl) ⟨239550, by rfl⟩ : syracuseStep 638801 = 479101) B479101
theorem B638819 : Blo 424774 638819 := bstep (se 1 (by rfl) ⟨479114, by rfl⟩ : syracuseStep 638819 = 958229) B958229
theorem B638849 : Blo 424774 638849 := bstep (se 2 (by rfl) ⟨239568, by rfl⟩ : syracuseStep 638849 = 479137) B479137
theorem B638867 : Blo 424774 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B638897 : Blo 424774 638897 := bstep (se 2 (by rfl) ⟨239586, by rfl⟩ : syracuseStep 638897 = 479173) B479173
theorem B638915 : Blo 424774 638915 := bstep (se 1 (by rfl) ⟨479186, by rfl⟩ : syracuseStep 638915 = 958373) B958373
theorem B638945 : Blo 424774 638945 := bstep (se 2 (by rfl) ⟨239604, by rfl⟩ : syracuseStep 638945 = 479209) B479209
theorem B638963 : Blo 424774 638963 := bstep (se 1 (by rfl) ⟨479222, by rfl⟩ : syracuseStep 638963 = 958445) B958445
theorem B606209 : Blo 424774 606209 := bstep (se 2 (by rfl) ⟨227328, by rfl⟩ : syracuseStep 606209 = 454657) B454657
theorem B638993 : Blo 424774 638993 := bstep (se 2 (by rfl) ⟨239622, by rfl⟩ : syracuseStep 638993 = 479245) B479245
theorem B639011 : Blo 424774 639011 := bstep (se 1 (by rfl) ⟨479258, by rfl⟩ : syracuseStep 639011 = 958517) B958517
theorem B639041 : Blo 424774 639041 := bstep (se 2 (by rfl) ⟨239640, by rfl⟩ : syracuseStep 639041 = 479281) B479281
theorem B2441285 : Blo 424774 2441285 := bstep (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) B457741
theorem B639059 : Blo 424774 639059 := bstep (se 1 (by rfl) ⟨479294, by rfl⟩ : syracuseStep 639059 = 958589) B958589
theorem B639089 : Blo 424774 639089 := bstep (se 2 (by rfl) ⟨239658, by rfl⟩ : syracuseStep 639089 = 479317) B479317
theorem B606323 : Blo 424774 606323 := bstep (se 1 (by rfl) ⟨454742, by rfl⟩ : syracuseStep 606323 = 909485) B909485
theorem B639107 : Blo 424774 639107 := bstep (se 1 (by rfl) ⟨479330, by rfl⟩ : syracuseStep 639107 = 958661) B958661
theorem B639137 : Blo 424774 639137 := bstep (se 2 (by rfl) ⟨239676, by rfl⟩ : syracuseStep 639137 = 479353) B479353
theorem B639155 : Blo 424774 639155 := bstep (se 1 (by rfl) ⟨479366, by rfl⟩ : syracuseStep 639155 = 958733) B958733
theorem B606403 : Blo 424774 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B639185 : Blo 424774 639185 := bstep (se 2 (by rfl) ⟨239694, by rfl⟩ : syracuseStep 639185 = 479389) B479389
theorem B639203 : Blo 424774 639203 := bstep (se 1 (by rfl) ⟨479402, by rfl⟩ : syracuseStep 639203 = 958805) B958805
theorem B639233 : Blo 424774 639233 := bstep (se 2 (by rfl) ⟨239712, by rfl⟩ : syracuseStep 639233 = 479425) B479425
theorem B639251 : Blo 424774 639251 := bstep (se 1 (by rfl) ⟨479438, by rfl⟩ : syracuseStep 639251 = 958877) B958877
theorem B639281 : Blo 424774 639281 := bstep (se 2 (by rfl) ⟨239730, by rfl⟩ : syracuseStep 639281 = 479461) B479461
theorem B639299 : Blo 424774 639299 := bstep (se 1 (by rfl) ⟨479474, by rfl⟩ : syracuseStep 639299 = 958949) B958949
theorem B639329 : Blo 424774 639329 := bstep (se 2 (by rfl) ⟨239748, by rfl⟩ : syracuseStep 639329 = 479497) B479497
theorem B639347 : Blo 424774 639347 := bstep (se 1 (by rfl) ⟨479510, by rfl⟩ : syracuseStep 639347 = 959021) B959021
theorem B639377 : Blo 424774 639377 := bstep (se 2 (by rfl) ⟨239766, by rfl⟩ : syracuseStep 639377 = 479533) B479533
theorem B541075 : Blo 424774 541075 := bstep (se 1 (by rfl) ⟨405806, by rfl⟩ : syracuseStep 541075 = 811613) B811613
theorem B639395 : Blo 424774 639395 := bstep (se 1 (by rfl) ⟨479546, by rfl⟩ : syracuseStep 639395 = 959093) B959093
theorem B639425 : Blo 424774 639425 := bstep (se 2 (by rfl) ⟨239784, by rfl⟩ : syracuseStep 639425 = 479569) B479569
theorem B639443 : Blo 424774 639443 := bstep (se 1 (by rfl) ⟨479582, by rfl⟩ : syracuseStep 639443 = 959165) B959165
theorem B639473 : Blo 424774 639473 := bstep (se 2 (by rfl) ⟨239802, by rfl⟩ : syracuseStep 639473 = 479605) B479605
theorem B541171 : Blo 424774 541171 := bstep (se 1 (by rfl) ⟨405878, by rfl⟩ : syracuseStep 541171 = 811757) B811757
theorem B639491 : Blo 424774 639491 := bstep (se 1 (by rfl) ⟨479618, by rfl⟩ : syracuseStep 639491 = 959237) B959237
theorem B639521 : Blo 424774 639521 := bstep (se 2 (by rfl) ⟨239820, by rfl⟩ : syracuseStep 639521 = 479641) B479641
theorem B639539 : Blo 424774 639539 := bstep (se 1 (by rfl) ⟨479654, by rfl⟩ : syracuseStep 639539 = 959309) B959309
theorem B639569 : Blo 424774 639569 := bstep (se 2 (by rfl) ⟨239838, by rfl⟩ : syracuseStep 639569 = 479677) B479677
theorem B2048611 : Blo 424774 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B639587 : Blo 424774 639587 := bstep (se 1 (by rfl) ⟨479690, by rfl⟩ : syracuseStep 639587 = 959381) B959381
theorem B639617 : Blo 424774 639617 := bstep (se 2 (by rfl) ⟨239856, by rfl⟩ : syracuseStep 639617 = 479713) B479713
theorem B639635 : Blo 424774 639635 := bstep (se 1 (by rfl) ⟨479726, by rfl⟩ : syracuseStep 639635 = 959453) B959453
theorem B639665 : Blo 424774 639665 := bstep (se 2 (by rfl) ⟨239874, by rfl⟩ : syracuseStep 639665 = 479749) B479749
theorem B639683 : Blo 424774 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B3654341 : Blo 424774 3654341 := bstep (se 4 (by rfl) ⟨342594, by rfl⟩ : syracuseStep 3654341 = 685189) B685189
theorem B639713 : Blo 424774 639713 := bstep (se 2 (by rfl) ⟨239892, by rfl⟩ : syracuseStep 639713 = 479785) B479785
theorem B606961 : Blo 424774 606961 := bstep (se 2 (by rfl) ⟨227610, by rfl⟩ : syracuseStep 606961 = 455221) B455221
theorem B639731 : Blo 424774 639731 := bstep (se 1 (by rfl) ⟨479798, by rfl⟩ : syracuseStep 639731 = 959597) B959597
theorem B639761 : Blo 424774 639761 := bstep (se 2 (by rfl) ⟨239910, by rfl⟩ : syracuseStep 639761 = 479821) B479821
theorem B639779 : Blo 424774 639779 := bstep (se 1 (by rfl) ⟨479834, by rfl⟩ : syracuseStep 639779 = 959669) B959669
theorem B639809 : Blo 424774 639809 := bstep (se 2 (by rfl) ⟨239928, by rfl⟩ : syracuseStep 639809 = 479857) B479857
theorem B1622861 : Blo 424774 1622861 := bstep (se 3 (by rfl) ⟨304286, by rfl⟩ : syracuseStep 1622861 = 608573) B608573
theorem B639827 : Blo 424774 639827 := bstep (se 1 (by rfl) ⟨479870, by rfl⟩ : syracuseStep 639827 = 959741) B959741
theorem B639857 : Blo 424774 639857 := bstep (se 2 (by rfl) ⟨239946, by rfl⟩ : syracuseStep 639857 = 479893) B479893
theorem B639875 : Blo 424774 639875 := bstep (se 1 (by rfl) ⟨479906, by rfl⟩ : syracuseStep 639875 = 959813) B959813
theorem B639905 : Blo 424774 639905 := bstep (se 2 (by rfl) ⟨239964, by rfl⟩ : syracuseStep 639905 = 479929) B479929
theorem B639923 : Blo 424774 639923 := bstep (se 1 (by rfl) ⟨479942, by rfl⟩ : syracuseStep 639923 = 959885) B959885
theorem B639953 : Blo 424774 639953 := bstep (se 2 (by rfl) ⟨239982, by rfl⟩ : syracuseStep 639953 = 479965) B479965
theorem B639971 : Blo 424774 639971 := bstep (se 1 (by rfl) ⟨479978, by rfl⟩ : syracuseStep 639971 = 959957) B959957
theorem B541667 : Blo 424774 541667 := bstep (se 1 (by rfl) ⟨406250, by rfl⟩ : syracuseStep 541667 = 812501) B812501
theorem B640001 : Blo 424774 640001 := bstep (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) B480001
theorem B640019 : Blo 424774 640019 := bstep (se 1 (by rfl) ⟨480014, by rfl⟩ : syracuseStep 640019 = 960029) B960029
theorem B640049 : Blo 424774 640049 := bstep (se 2 (by rfl) ⟨240018, by rfl⟩ : syracuseStep 640049 = 480037) B480037
theorem B640067 : Blo 424774 640067 := bstep (se 1 (by rfl) ⟨480050, by rfl⟩ : syracuseStep 640067 = 960101) B960101
theorem B640097 : Blo 424774 640097 := bstep (se 2 (by rfl) ⟨240036, by rfl⟩ : syracuseStep 640097 = 480073) B480073
theorem B640115 : Blo 424774 640115 := bstep (se 1 (by rfl) ⟨480086, by rfl⟩ : syracuseStep 640115 = 960173) B960173
theorem B640145 : Blo 424774 640145 := bstep (se 2 (by rfl) ⟨240054, by rfl⟩ : syracuseStep 640145 = 480109) B480109
theorem B640163 : Blo 424774 640163 := bstep (se 1 (by rfl) ⟨480122, by rfl⟩ : syracuseStep 640163 = 960245) B960245
theorem B640193 : Blo 424774 640193 := bstep (se 2 (by rfl) ⟨240072, by rfl⟩ : syracuseStep 640193 = 480145) B480145
theorem B5817541 : Blo 424774 5817541 := bstep (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) B1090789
theorem B640211 : Blo 424774 640211 := bstep (se 1 (by rfl) ⟨480158, by rfl⟩ : syracuseStep 640211 = 960317) B960317
theorem B640241 : Blo 424774 640241 := bstep (se 2 (by rfl) ⟨240090, by rfl⟩ : syracuseStep 640241 = 480181) B480181
theorem B640259 : Blo 424774 640259 := bstep (se 1 (by rfl) ⟨480194, by rfl⟩ : syracuseStep 640259 = 960389) B960389
theorem B640289 : Blo 424774 640289 := bstep (se 2 (by rfl) ⟨240108, by rfl⟩ : syracuseStep 640289 = 480217) B480217
theorem B640307 : Blo 424774 640307 := bstep (se 1 (by rfl) ⟨480230, by rfl⟩ : syracuseStep 640307 = 960461) B960461
theorem B640337 : Blo 424774 640337 := bstep (se 2 (by rfl) ⟨240126, by rfl⟩ : syracuseStep 640337 = 480253) B480253
theorem B640355 : Blo 424774 640355 := bstep (se 1 (by rfl) ⟨480266, by rfl⟩ : syracuseStep 640355 = 960533) B960533
theorem B640385 : Blo 424774 640385 := bstep (se 2 (by rfl) ⟨240144, by rfl⟩ : syracuseStep 640385 = 480289) B480289
theorem B640403 : Blo 424774 640403 := bstep (se 1 (by rfl) ⟨480302, by rfl⟩ : syracuseStep 640403 = 960605) B960605
theorem B640433 : Blo 424774 640433 := bstep (se 2 (by rfl) ⟨240162, by rfl⟩ : syracuseStep 640433 = 480325) B480325
theorem B607667 : Blo 424774 607667 := bstep (se 1 (by rfl) ⟨455750, by rfl⟩ : syracuseStep 607667 = 911501) B911501
theorem B640451 : Blo 424774 640451 := bstep (se 1 (by rfl) ⟨480338, by rfl⟩ : syracuseStep 640451 = 960677) B960677
theorem B1361357 : Blo 424774 1361357 := bstep (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) B510509
theorem B640481 : Blo 424774 640481 := bstep (se 2 (by rfl) ⟨240180, by rfl⟩ : syracuseStep 640481 = 480361) B480361
theorem B640499 : Blo 424774 640499 := bstep (se 1 (by rfl) ⟨480374, by rfl⟩ : syracuseStep 640499 = 960749) B960749
theorem B1295875 : Blo 424774 1295875 := bstep (se 1 (by rfl) ⟨971906, by rfl⟩ : syracuseStep 1295875 = 1943813) B1943813
theorem B640529 : Blo 424774 640529 := bstep (se 2 (by rfl) ⟨240198, by rfl⟩ : syracuseStep 640529 = 480397) B480397
theorem B640547 : Blo 424774 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B640577 : Blo 424774 640577 := bstep (se 2 (by rfl) ⟨240216, by rfl⟩ : syracuseStep 640577 = 480433) B480433
theorem B640595 : Blo 424774 640595 := bstep (se 1 (by rfl) ⟨480446, by rfl⟩ : syracuseStep 640595 = 960893) B960893
theorem B640625 : Blo 424774 640625 := bstep (se 2 (by rfl) ⟨240234, by rfl⟩ : syracuseStep 640625 = 480469) B480469
theorem B1623665 : Blo 424774 1623665 := bstep (se 2 (by rfl) ⟨608874, by rfl⟩ : syracuseStep 1623665 = 1217749) B1217749
theorem B640643 : Blo 424774 640643 := bstep (se 1 (by rfl) ⟨480482, by rfl⟩ : syracuseStep 640643 = 960965) B960965
theorem B640673 : Blo 424774 640673 := bstep (se 2 (by rfl) ⟨240252, by rfl⟩ : syracuseStep 640673 = 480505) B480505
theorem B542371 : Blo 424774 542371 := bstep (se 1 (by rfl) ⟨406778, by rfl⟩ : syracuseStep 542371 = 813557) B813557
theorem B640691 : Blo 424774 640691 := bstep (se 1 (by rfl) ⟨480518, by rfl⟩ : syracuseStep 640691 = 961037) B961037
theorem B640721 : Blo 424774 640721 := bstep (se 2 (by rfl) ⟨240270, by rfl⟩ : syracuseStep 640721 = 480541) B480541
theorem B640739 : Blo 424774 640739 := bstep (se 1 (by rfl) ⟨480554, by rfl⟩ : syracuseStep 640739 = 961109) B961109
theorem B2311907 : Blo 424774 2311907 := bstep (se 1 (by rfl) ⟨1733930, by rfl⟩ : syracuseStep 2311907 = 3467861) B3467861
theorem B640769 : Blo 424774 640769 := bstep (se 2 (by rfl) ⟨240288, by rfl⟩ : syracuseStep 640769 = 480577) B480577
theorem B542467 : Blo 424774 542467 := bstep (se 1 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 542467 = 813701) B813701
theorem B3131149 : Blo 424774 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B640787 : Blo 424774 640787 := bstep (se 1 (by rfl) ⟨480590, by rfl⟩ : syracuseStep 640787 = 961181) B961181
theorem B640817 : Blo 424774 640817 := bstep (se 2 (by rfl) ⟨240306, by rfl⟩ : syracuseStep 640817 = 480613) B480613
theorem B640835 : Blo 424774 640835 := bstep (se 1 (by rfl) ⟨480626, by rfl⟩ : syracuseStep 640835 = 961253) B961253
theorem B640865 : Blo 424774 640865 := bstep (se 2 (by rfl) ⟨240324, by rfl⟩ : syracuseStep 640865 = 480649) B480649
theorem B640883 : Blo 424774 640883 := bstep (se 1 (by rfl) ⟨480662, by rfl⟩ : syracuseStep 640883 = 961325) B961325
theorem B20760461 : Blo 424774 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B640913 : Blo 424774 640913 := bstep (se 2 (by rfl) ⟨240342, by rfl⟩ : syracuseStep 640913 = 480685) B480685
theorem B640931 : Blo 424774 640931 := bstep (se 1 (by rfl) ⟨480698, by rfl⟩ : syracuseStep 640931 = 961397) B961397
theorem B640961 : Blo 424774 640961 := bstep (se 2 (by rfl) ⟨240360, by rfl⟩ : syracuseStep 640961 = 480721) B480721
theorem B640979 : Blo 424774 640979 := bstep (se 1 (by rfl) ⟨480734, by rfl⟩ : syracuseStep 640979 = 961469) B961469
theorem B641009 : Blo 424774 641009 := bstep (se 2 (by rfl) ⟨240378, by rfl⟩ : syracuseStep 641009 = 480757) B480757
theorem B641027 : Blo 424774 641027 := bstep (se 1 (by rfl) ⟨480770, by rfl⟩ : syracuseStep 641027 = 961541) B961541
theorem B641057 : Blo 424774 641057 := bstep (se 2 (by rfl) ⟨240396, by rfl⟩ : syracuseStep 641057 = 480793) B480793
theorem B608305 : Blo 424774 608305 := bstep (se 2 (by rfl) ⟨228114, by rfl⟩ : syracuseStep 608305 = 456229) B456229
theorem B641075 : Blo 424774 641075 := bstep (se 1 (by rfl) ⟨480806, by rfl⟩ : syracuseStep 641075 = 961613) B961613
theorem B2738245 : Blo 424774 2738245 := bstep (se 4 (by rfl) ⟨256710, by rfl⟩ : syracuseStep 2738245 = 513421) B513421
theorem B641105 : Blo 424774 641105 := bstep (se 2 (by rfl) ⟨240414, by rfl⟩ : syracuseStep 641105 = 480829) B480829
theorem B641123 : Blo 424774 641123 := bstep (se 1 (by rfl) ⟨480842, by rfl⟩ : syracuseStep 641123 = 961685) B961685
theorem B1263725 : Blo 424774 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B641153 : Blo 424774 641153 := bstep (se 2 (by rfl) ⟨240432, by rfl⟩ : syracuseStep 641153 = 480865) B480865
theorem B641171 : Blo 424774 641171 := bstep (se 1 (by rfl) ⟨480878, by rfl⟩ : syracuseStep 641171 = 961757) B961757
theorem B608419 : Blo 424774 608419 := bstep (se 1 (by rfl) ⟨456314, by rfl⟩ : syracuseStep 608419 = 912629) B912629
theorem B641201 : Blo 424774 641201 := bstep (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) B480901
theorem B641219 : Blo 424774 641219 := bstep (se 1 (by rfl) ⟨480914, by rfl⟩ : syracuseStep 641219 = 961829) B961829
theorem B641249 : Blo 424774 641249 := bstep (se 2 (by rfl) ⟨240468, by rfl⟩ : syracuseStep 641249 = 480937) B480937
theorem B1231085 : Blo 424774 1231085 := bstep (se 3 (by rfl) ⟨230828, by rfl⟩ : syracuseStep 1231085 = 461657) B461657
theorem B641267 : Blo 424774 641267 := bstep (se 1 (by rfl) ⟨480950, by rfl⟩ : syracuseStep 641267 = 961901) B961901
theorem B1624333 : Blo 424774 1624333 := bstep (se 3 (by rfl) ⟨304562, by rfl⟩ : syracuseStep 1624333 = 609125) B609125
theorem B641297 : Blo 424774 641297 := bstep (se 2 (by rfl) ⟨240486, by rfl⟩ : syracuseStep 641297 = 480973) B480973
theorem B641315 : Blo 424774 641315 := bstep (se 1 (by rfl) ⟨480986, by rfl⟩ : syracuseStep 641315 = 961973) B961973
theorem B641345 : Blo 424774 641345 := bstep (se 2 (by rfl) ⟨240504, by rfl⟩ : syracuseStep 641345 = 481009) B481009
theorem B641363 : Blo 424774 641363 := bstep (se 1 (by rfl) ⟨481022, by rfl⟩ : syracuseStep 641363 = 962045) B962045
theorem B641393 : Blo 424774 641393 := bstep (se 2 (by rfl) ⟨240522, by rfl⟩ : syracuseStep 641393 = 481045) B481045
theorem B641411 : Blo 424774 641411 := bstep (se 1 (by rfl) ⟨481058, by rfl⟩ : syracuseStep 641411 = 962117) B962117
theorem B641441 : Blo 424774 641441 := bstep (se 2 (by rfl) ⟨240540, by rfl⟩ : syracuseStep 641441 = 481081) B481081
theorem B641459 : Blo 424774 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B1165763 : Blo 424774 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B641489 : Blo 424774 641489 := bstep (se 2 (by rfl) ⟨240558, by rfl⟩ : syracuseStep 641489 = 481117) B481117
theorem B641507 : Blo 424774 641507 := bstep (se 1 (by rfl) ⟨481130, by rfl⟩ : syracuseStep 641507 = 962261) B962261
theorem B510451 : Blo 424774 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B641537 : Blo 424774 641537 := bstep (se 2 (by rfl) ⟨240576, by rfl⟩ : syracuseStep 641537 = 481153) B481153
theorem B641555 : Blo 424774 641555 := bstep (se 1 (by rfl) ⟨481166, by rfl⟩ : syracuseStep 641555 = 962333) B962333
theorem B2050609 : Blo 424774 2050609 := bstep (se 2 (by rfl) ⟨768978, by rfl⟩ : syracuseStep 2050609 = 1537957) B1537957
theorem B641585 : Blo 424774 641585 := bstep (se 2 (by rfl) ⟨240594, by rfl⟩ : syracuseStep 641585 = 481189) B481189
theorem B641603 : Blo 424774 641603 := bstep (se 1 (by rfl) ⟨481202, by rfl⟩ : syracuseStep 641603 = 962405) B962405
theorem B641633 : Blo 424774 641633 := bstep (se 2 (by rfl) ⟨240612, by rfl⟩ : syracuseStep 641633 = 481225) B481225
theorem B641651 : Blo 424774 641651 := bstep (se 1 (by rfl) ⟨481238, by rfl⟩ : syracuseStep 641651 = 962477) B962477
theorem B641681 : Blo 424774 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B641699 : Blo 424774 641699 := bstep (se 1 (by rfl) ⟨481274, by rfl⟩ : syracuseStep 641699 = 962549) B962549
theorem B1821361 : Blo 424774 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B1231537 : Blo 424774 1231537 := bstep (se 2 (by rfl) ⟨461826, by rfl⟩ : syracuseStep 1231537 = 923653) B923653
theorem B641729 : Blo 424774 641729 := bstep (se 2 (by rfl) ⟨240648, by rfl⟩ : syracuseStep 641729 = 481297) B481297
theorem B641747 : Blo 424774 641747 := bstep (se 1 (by rfl) ⟨481310, by rfl⟩ : syracuseStep 641747 = 962621) B962621
theorem B641777 : Blo 424774 641777 := bstep (se 2 (by rfl) ⟨240666, by rfl⟩ : syracuseStep 641777 = 481333) B481333
theorem B641795 : Blo 424774 641795 := bstep (se 1 (by rfl) ⟨481346, by rfl⟩ : syracuseStep 641795 = 962693) B962693
theorem B641825 : Blo 424774 641825 := bstep (se 2 (by rfl) ⟨240684, by rfl⟩ : syracuseStep 641825 = 481369) B481369
theorem B478003 : Blo 424774 478003 := bstep (se 1 (by rfl) ⟨358502, by rfl⟩ : syracuseStep 478003 = 717005) B717005
theorem B641843 : Blo 424774 641843 := bstep (se 1 (by rfl) ⟨481382, by rfl⟩ : syracuseStep 641843 = 962765) B962765
theorem B641873 : Blo 424774 641873 := bstep (se 2 (by rfl) ⟨240702, by rfl⟩ : syracuseStep 641873 = 481405) B481405
theorem B969571 : Blo 424774 969571 := bstep (se 1 (by rfl) ⟨727178, by rfl⟩ : syracuseStep 969571 = 1454357) B1454357
theorem B641891 : Blo 424774 641891 := bstep (se 1 (by rfl) ⟨481418, by rfl⟩ : syracuseStep 641891 = 962837) B962837
theorem B641921 : Blo 424774 641921 := bstep (se 2 (by rfl) ⟨240720, by rfl⟩ : syracuseStep 641921 = 481441) B481441
theorem B641939 : Blo 424774 641939 := bstep (se 1 (by rfl) ⟨481454, by rfl⟩ : syracuseStep 641939 = 962909) B962909
theorem B641969 : Blo 424774 641969 := bstep (se 2 (by rfl) ⟨240738, by rfl⟩ : syracuseStep 641969 = 481477) B481477
theorem B478147 : Blo 424774 478147 := bstep (se 1 (by rfl) ⟨358610, by rfl⟩ : syracuseStep 478147 = 717221) B717221
theorem B641987 : Blo 424774 641987 := bstep (se 1 (by rfl) ⟨481490, by rfl⟩ : syracuseStep 641987 = 962981) B962981
theorem B642017 : Blo 424774 642017 := bstep (se 2 (by rfl) ⟨240756, by rfl⟩ : syracuseStep 642017 = 481513) B481513
theorem B642035 : Blo 424774 642035 := bstep (se 1 (by rfl) ⟨481526, by rfl⟩ : syracuseStep 642035 = 963053) B963053
theorem B1166339 : Blo 424774 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B642065 : Blo 424774 642065 := bstep (se 2 (by rfl) ⟨240774, by rfl⟩ : syracuseStep 642065 = 481549) B481549
theorem B1625123 : Blo 424774 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B642083 : Blo 424774 642083 := bstep (se 1 (by rfl) ⟨481562, by rfl⟩ : syracuseStep 642083 = 963125) B963125
theorem B642113 : Blo 424774 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B478291 : Blo 424774 478291 := bstep (se 1 (by rfl) ⟨358718, by rfl⟩ : syracuseStep 478291 = 717437) B717437
theorem B642131 : Blo 424774 642131 := bstep (se 1 (by rfl) ⟨481598, by rfl⟩ : syracuseStep 642131 = 963197) B963197
theorem B642161 : Blo 424774 642161 := bstep (se 2 (by rfl) ⟨240810, by rfl⟩ : syracuseStep 642161 = 481621) B481621
theorem B642179 : Blo 424774 642179 := bstep (se 1 (by rfl) ⟨481634, by rfl⟩ : syracuseStep 642179 = 963269) B963269
theorem B642209 : Blo 424774 642209 := bstep (se 2 (by rfl) ⟨240828, by rfl⟩ : syracuseStep 642209 = 481657) B481657
theorem B642227 : Blo 424774 642227 := bstep (se 1 (by rfl) ⟨481670, by rfl⟩ : syracuseStep 642227 = 963341) B963341
theorem B1363139 : Blo 424774 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B642257 : Blo 424774 642257 := bstep (se 2 (by rfl) ⟨240846, by rfl⟩ : syracuseStep 642257 = 481693) B481693
theorem B478435 : Blo 424774 478435 := bstep (se 1 (by rfl) ⟨358826, by rfl⟩ : syracuseStep 478435 = 717653) B717653
theorem B642275 : Blo 424774 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B642305 : Blo 424774 642305 := bstep (se 2 (by rfl) ⟨240864, by rfl⟩ : syracuseStep 642305 = 481729) B481729
theorem B642323 : Blo 424774 642323 := bstep (se 1 (by rfl) ⟨481742, by rfl⟩ : syracuseStep 642323 = 963485) B963485
theorem B642353 : Blo 424774 642353 := bstep (se 2 (by rfl) ⟨240882, by rfl⟩ : syracuseStep 642353 = 481765) B481765
theorem B642371 : Blo 424774 642371 := bstep (se 1 (by rfl) ⟨481778, by rfl⟩ : syracuseStep 642371 = 963557) B963557
theorem B642401 : Blo 424774 642401 := bstep (se 2 (by rfl) ⟨240900, by rfl⟩ : syracuseStep 642401 = 481801) B481801
theorem B511331 : Blo 424774 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B478579 : Blo 424774 478579 := bstep (se 1 (by rfl) ⟨358934, by rfl⟩ : syracuseStep 478579 = 717869) B717869
theorem B642419 : Blo 424774 642419 := bstep (se 1 (by rfl) ⟨481814, by rfl⟩ : syracuseStep 642419 = 963629) B963629
theorem B3165581 : Blo 424774 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B642449 : Blo 424774 642449 := bstep (se 2 (by rfl) ⟨240918, by rfl⟩ : syracuseStep 642449 = 481837) B481837
theorem B642467 : Blo 424774 642467 := bstep (se 1 (by rfl) ⟨481850, by rfl⟩ : syracuseStep 642467 = 963701) B963701
theorem B642497 : Blo 424774 642497 := bstep (se 2 (by rfl) ⟨240936, by rfl⟩ : syracuseStep 642497 = 481873) B481873
theorem B642515 : Blo 424774 642515 := bstep (se 1 (by rfl) ⟨481886, by rfl⟩ : syracuseStep 642515 = 963773) B963773
theorem B609763 : Blo 424774 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B642545 : Blo 424774 642545 := bstep (se 2 (by rfl) ⟨240954, by rfl⟩ : syracuseStep 642545 = 481909) B481909
theorem B478723 : Blo 424774 478723 := bstep (se 1 (by rfl) ⟨359042, by rfl⟩ : syracuseStep 478723 = 718085) B718085
theorem B642563 : Blo 424774 642563 := bstep (se 1 (by rfl) ⟨481922, by rfl⟩ : syracuseStep 642563 = 963845) B963845
theorem B642593 : Blo 424774 642593 := bstep (se 2 (by rfl) ⟨240972, by rfl⟩ : syracuseStep 642593 = 481945) B481945
theorem B806449 : Blo 424774 806449 := bstep (se 2 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 806449 = 604837) B604837
theorem B642611 : Blo 424774 642611 := bstep (se 1 (by rfl) ⟨481958, by rfl⟩ : syracuseStep 642611 = 963917) B963917
theorem B577091 : Blo 424774 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B740945 : Blo 424774 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B642641 : Blo 424774 642641 := bstep (se 2 (by rfl) ⟨240990, by rfl⟩ : syracuseStep 642641 = 481981) B481981
theorem B642659 : Blo 424774 642659 := bstep (se 1 (by rfl) ⟨481994, by rfl⟩ : syracuseStep 642659 = 963989) B963989
theorem B642689 : Blo 424774 642689 := bstep (se 2 (by rfl) ⟨241008, by rfl⟩ : syracuseStep 642689 = 482017) B482017
theorem B478867 : Blo 424774 478867 := bstep (se 1 (by rfl) ⟨359150, by rfl⟩ : syracuseStep 478867 = 718301) B718301
theorem B642707 : Blo 424774 642707 := bstep (se 1 (by rfl) ⟨482030, by rfl⟩ : syracuseStep 642707 = 964061) B964061
theorem B1625777 : Blo 424774 1625777 := bstep (se 2 (by rfl) ⟨609666, by rfl⟩ : syracuseStep 1625777 = 1219333) B1219333
theorem B642737 : Blo 424774 642737 := bstep (se 2 (by rfl) ⟨241026, by rfl⟩ : syracuseStep 642737 = 482053) B482053
theorem B642755 : Blo 424774 642755 := bstep (se 1 (by rfl) ⟨482066, by rfl⟩ : syracuseStep 642755 = 964133) B964133
theorem B642785 : Blo 424774 642785 := bstep (se 2 (by rfl) ⟨241044, by rfl⟩ : syracuseStep 642785 = 482089) B482089
theorem B642803 : Blo 424774 642803 := bstep (se 1 (by rfl) ⟨482102, by rfl⟩ : syracuseStep 642803 = 964205) B964205
theorem B642833 : Blo 424774 642833 := bstep (se 2 (by rfl) ⟨241062, by rfl⟩ : syracuseStep 642833 = 482125) B482125
theorem B479011 : Blo 424774 479011 := bstep (se 1 (by rfl) ⟨359258, by rfl⟩ : syracuseStep 479011 = 718517) B718517
theorem B642851 : Blo 424774 642851 := bstep (se 1 (by rfl) ⟨482138, by rfl⟩ : syracuseStep 642851 = 964277) B964277
theorem B1527587 : Blo 424774 1527587 := bstep (se 1 (by rfl) ⟨1145690, by rfl⟩ : syracuseStep 1527587 = 2291381) B2291381
theorem B642881 : Blo 424774 642881 := bstep (se 2 (by rfl) ⟨241080, by rfl⟩ : syracuseStep 642881 = 482161) B482161
theorem B642899 : Blo 424774 642899 := bstep (se 1 (by rfl) ⟨482174, by rfl⟩ : syracuseStep 642899 = 964349) B964349
theorem B642929 : Blo 424774 642929 := bstep (se 2 (by rfl) ⟨241098, by rfl⟩ : syracuseStep 642929 = 482197) B482197
theorem B642947 : Blo 424774 642947 := bstep (se 1 (by rfl) ⟨482210, by rfl⟩ : syracuseStep 642947 = 964421) B964421
theorem B642977 : Blo 424774 642977 := bstep (se 2 (by rfl) ⟨241116, by rfl⟩ : syracuseStep 642977 = 482233) B482233
theorem B479155 : Blo 424774 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B642995 : Blo 424774 642995 := bstep (se 1 (by rfl) ⟨482246, by rfl⟩ : syracuseStep 642995 = 964493) B964493
theorem B806851 : Blo 424774 806851 := bstep (se 1 (by rfl) ⟨605138, by rfl⟩ : syracuseStep 806851 = 1210277) B1210277
theorem B643025 : Blo 424774 643025 := bstep (se 2 (by rfl) ⟨241134, by rfl⟩ : syracuseStep 643025 = 482269) B482269
theorem B643043 : Blo 424774 643043 := bstep (se 1 (by rfl) ⟨482282, by rfl⟩ : syracuseStep 643043 = 964565) B964565
theorem B806897 : Blo 424774 806897 := bstep (se 2 (by rfl) ⟨302586, by rfl⟩ : syracuseStep 806897 = 605173) B605173
theorem B643073 : Blo 424774 643073 := bstep (se 2 (by rfl) ⟨241152, by rfl⟩ : syracuseStep 643073 = 482305) B482305
theorem B643091 : Blo 424774 643091 := bstep (se 1 (by rfl) ⟨482318, by rfl⟩ : syracuseStep 643091 = 964637) B964637
theorem B643121 : Blo 424774 643121 := bstep (se 2 (by rfl) ⟨241170, by rfl⟩ : syracuseStep 643121 = 482341) B482341
theorem B479299 : Blo 424774 479299 := bstep (se 1 (by rfl) ⟨359474, by rfl⟩ : syracuseStep 479299 = 718949) B718949
theorem B643139 : Blo 424774 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B479443 : Blo 424774 479443 := bstep (se 1 (by rfl) ⟨359582, by rfl⟩ : syracuseStep 479443 = 719165) B719165
theorem B807185 : Blo 424774 807185 := bstep (se 2 (by rfl) ⟨302694, by rfl⟩ : syracuseStep 807185 = 605389) B605389
theorem B479587 : Blo 424774 479587 := bstep (se 1 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 479587 = 719381) B719381
theorem B2773453 : Blo 424774 2773453 := bstep (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) B1040045
theorem B479731 : Blo 424774 479731 := bstep (se 1 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 479731 = 719597) B719597
theorem B1364483 : Blo 424774 1364483 := bstep (se 1 (by rfl) ⟨1023362, by rfl⟩ : syracuseStep 1364483 = 2046725) B2046725
theorem B1167949 : Blo 424774 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B479875 : Blo 424774 479875 := bstep (se 1 (by rfl) ⟨359906, by rfl⟩ : syracuseStep 479875 = 719813) B719813
theorem B480019 : Blo 424774 480019 := bstep (se 1 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 480019 = 720029) B720029
theorem B578323 : Blo 424774 578323 := bstep (se 1 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 578323 = 867485) B867485
theorem B480163 : Blo 424774 480163 := bstep (se 1 (by rfl) ⟨360122, by rfl⟩ : syracuseStep 480163 = 720245) B720245
theorem B807907 : Blo 424774 807907 := bstep (se 1 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 807907 = 1211861) B1211861
theorem B480307 : Blo 424774 480307 := bstep (se 1 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 480307 = 720461) B720461
theorem B1627235 : Blo 424774 1627235 := bstep (se 1 (by rfl) ⟨1220426, by rfl⟩ : syracuseStep 1627235 = 2440853) B2440853
theorem B1627249 : Blo 424774 1627249 := bstep (se 2 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 1627249 = 1220437) B1220437
theorem B1496227 : Blo 424774 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B480451 : Blo 424774 480451 := bstep (se 1 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 480451 = 720677) B720677
theorem B480595 : Blo 424774 480595 := bstep (se 1 (by rfl) ⟨360446, by rfl⟩ : syracuseStep 480595 = 720893) B720893
theorem B578929 : Blo 424774 578929 := bstep (se 2 (by rfl) ⟨217098, by rfl⟩ : syracuseStep 578929 = 434197) B434197
theorem B808355 : Blo 424774 808355 := bstep (se 1 (by rfl) ⟨606266, by rfl⟩ : syracuseStep 808355 = 1212533) B1212533
theorem B2184653 : Blo 424774 2184653 := bstep (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) B819245
theorem B480739 : Blo 424774 480739 := bstep (se 1 (by rfl) ⟨360554, by rfl⟩ : syracuseStep 480739 = 721109) B721109
theorem B1300013 : Blo 424774 1300013 := bstep (se 3 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 1300013 = 487505) B487505
theorem B480883 : Blo 424774 480883 := bstep (se 1 (by rfl) ⟨360662, by rfl⟩ : syracuseStep 480883 = 721325) B721325
theorem B513715 : Blo 424774 513715 := bstep (se 1 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 513715 = 770573) B770573
theorem B808643 : Blo 424774 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B481027 : Blo 424774 481027 := bstep (se 1 (by rfl) ⟨360770, by rfl⟩ : syracuseStep 481027 = 721541) B721541
theorem B579361 : Blo 424774 579361 := bstep (se 2 (by rfl) ⟨217260, by rfl⟩ : syracuseStep 579361 = 434521) B434521
theorem B5461829 : Blo 424774 5461829 := bstep (se 4 (by rfl) ⟨512046, by rfl⟩ : syracuseStep 5461829 = 1024093) B1024093
theorem B481171 : Blo 424774 481171 := bstep (se 1 (by rfl) ⟨360878, by rfl⟩ : syracuseStep 481171 = 721757) B721757
theorem B10344419 : Blo 424774 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B481315 : Blo 424774 481315 := bstep (se 1 (by rfl) ⟨360986, by rfl⟩ : syracuseStep 481315 = 721973) B721973
theorem B481459 : Blo 424774 481459 := bstep (se 1 (by rfl) ⟨361094, by rfl⟩ : syracuseStep 481459 = 722189) B722189
theorem B1366253 : Blo 424774 1366253 := bstep (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) B512345
theorem B1825037 : Blo 424774 1825037 := bstep (se 3 (by rfl) ⟨342194, by rfl⟩ : syracuseStep 1825037 = 684389) B684389
theorem B2054413 : Blo 424774 2054413 := bstep (se 3 (by rfl) ⟨385202, by rfl⟩ : syracuseStep 2054413 = 770405) B770405
theorem B907537 : Blo 424774 907537 := bstep (se 2 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 907537 = 680653) B680653
theorem B481603 : Blo 424774 481603 := bstep (se 1 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 481603 = 722405) B722405
theorem B2152817 : Blo 424774 2152817 := bstep (se 2 (by rfl) ⟨807306, by rfl⟩ : syracuseStep 2152817 = 1614613) B1614613
theorem B481747 : Blo 424774 481747 := bstep (se 1 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 481747 = 722621) B722621
theorem B481891 : Blo 424774 481891 := bstep (se 1 (by rfl) ⟨361418, by rfl⟩ : syracuseStep 481891 = 722837) B722837
theorem B809585 : Blo 424774 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B907939 : Blo 424774 907939 := bstep (se 1 (by rfl) ⟨680954, by rfl⟩ : syracuseStep 907939 = 1361909) B1361909
theorem B482035 : Blo 424774 482035 := bstep (se 1 (by rfl) ⟨361526, by rfl⟩ : syracuseStep 482035 = 723053) B723053
theorem B645907 : Blo 424774 645907 := bstep (se 1 (by rfl) ⟨484430, by rfl⟩ : syracuseStep 645907 = 968861) B968861
theorem B482179 : Blo 424774 482179 := bstep (se 1 (by rfl) ⟨361634, by rfl⟩ : syracuseStep 482179 = 723269) B723269
theorem B2743217 : Blo 424774 2743217 := bstep (se 2 (by rfl) ⟨1028706, by rfl⟩ : syracuseStep 2743217 = 2057413) B2057413
theorem B1235981 : Blo 424774 1235981 := bstep (se 3 (by rfl) ⟨231746, by rfl⟩ : syracuseStep 1235981 = 463493) B463493
theorem B482323 : Blo 424774 482323 := bstep (se 1 (by rfl) ⟨361742, by rfl⟩ : syracuseStep 482323 = 723485) B723485
theorem B1465553 : Blo 424774 1465553 := bstep (se 2 (by rfl) ⟨549582, by rfl⟩ : syracuseStep 1465553 = 1099165) B1099165
theorem B974243 : Blo 424774 974243 := bstep (se 1 (by rfl) ⟨730682, by rfl⟩ : syracuseStep 974243 = 1461365) B1461365
theorem B646625 : Blo 424774 646625 := bstep (se 2 (by rfl) ⟨242484, by rfl⟩ : syracuseStep 646625 = 484969) B484969
theorem B810481 : Blo 424774 810481 := bstep (se 2 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 810481 = 607861) B607861
theorem B810641 : Blo 424774 810641 := bstep (se 2 (by rfl) ⟨303990, by rfl⟩ : syracuseStep 810641 = 607981) B607981
theorem B2154275 : Blo 424774 2154275 := bstep (se 1 (by rfl) ⟨1615706, by rfl⟩ : syracuseStep 2154275 = 3231413) B3231413
theorem B647075 : Blo 424774 647075 := bstep (se 1 (by rfl) ⟨485306, by rfl⟩ : syracuseStep 647075 = 970613) B970613
theorem B811043 : Blo 424774 811043 := bstep (se 1 (by rfl) ⟨608282, by rfl⟩ : syracuseStep 811043 = 1216565) B1216565
theorem B1433645 : Blo 424774 1433645 := bstep (se 3 (by rfl) ⟨268808, by rfl⟩ : syracuseStep 1433645 = 537617) B537617
theorem B1433699 : Blo 424774 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B647281 : Blo 424774 647281 := bstep (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) B485461
theorem B909443 : Blo 424774 909443 := bstep (se 1 (by rfl) ⟨682082, by rfl⟩ : syracuseStep 909443 = 1364165) B1364165
theorem B1532045 : Blo 424774 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B1433969 : Blo 424774 1433969 := bstep (se 2 (by rfl) ⟨537738, by rfl⟩ : syracuseStep 1433969 = 1075477) B1075477
theorem B1302979 : Blo 424774 1302979 := bstep (se 1 (by rfl) ⟨977234, by rfl⟩ : syracuseStep 1302979 = 1954469) B1954469
theorem B3662405 : Blo 424774 3662405 := bstep (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) B686701
theorem B2155085 : Blo 424774 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B1434509 : Blo 424774 1434509 := bstep (se 3 (by rfl) ⟨268970, by rfl⟩ : syracuseStep 1434509 = 537941) B537941
theorem B811939 : Blo 424774 811939 := bstep (se 1 (by rfl) ⟨608954, by rfl⟩ : syracuseStep 811939 = 1217909) B1217909
theorem B1729457 : Blo 424774 1729457 := bstep (se 2 (by rfl) ⟨648546, by rfl⟩ : syracuseStep 1729457 = 1297093) B1297093
theorem B1434563 : Blo 424774 1434563 := bstep (se 1 (by rfl) ⟨1075922, by rfl⟩ : syracuseStep 1434563 = 2151845) B2151845
theorem B812099 : Blo 424774 812099 := bstep (se 1 (by rfl) ⟨609074, by rfl⟩ : syracuseStep 812099 = 1218149) B1218149
theorem B1434833 : Blo 424774 1434833 := bstep (se 2 (by rfl) ⟨538062, by rfl⟩ : syracuseStep 1434833 = 1076125) B1076125
theorem B648449 : Blo 424774 648449 := bstep (se 2 (by rfl) ⟨243168, by rfl⟩ : syracuseStep 648449 = 486337) B486337
theorem B1500419 : Blo 424774 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B2745677 : Blo 424774 2745677 := bstep (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) B1029629
theorem B910673 : Blo 424774 910673 := bstep (se 2 (by rfl) ⟨341502, by rfl⟩ : syracuseStep 910673 = 683005) B683005
theorem B1369457 : Blo 424774 1369457 := bstep (se 2 (by rfl) ⟨513546, by rfl⟩ : syracuseStep 1369457 = 1027093) B1027093
theorem B3466637 : Blo 424774 3466637 := bstep (se 3 (by rfl) ⟨649994, by rfl⟩ : syracuseStep 3466637 = 1299989) B1299989
theorem B1369507 : Blo 424774 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B681473 : Blo 424774 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B1435373 : Blo 424774 1435373 := bstep (se 3 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 1435373 = 538265) B538265
theorem B1435427 : Blo 424774 1435427 := bstep (se 1 (by rfl) ⟨1076570, by rfl⟩ : syracuseStep 1435427 = 2153141) B2153141
theorem B3237731 : Blo 424774 3237731 := bstep (se 1 (by rfl) ⟨2428298, by rfl⟩ : syracuseStep 3237731 = 4856597) B4856597
theorem B15591365 : Blo 424774 15591365 := bstep (se 4 (by rfl) ⟨1461690, by rfl⟩ : syracuseStep 15591365 = 2923381) B2923381
theorem B1009667 : Blo 424774 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1435697 : Blo 424774 1435697 := bstep (se 2 (by rfl) ⟨538386, by rfl⟩ : syracuseStep 1435697 = 1076773) B1076773
theorem B9234485 : Blo 424774 9234485 := bstep (se 5 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 9234485 = 865733) B865733
theorem B813169 : Blo 424774 813169 := bstep (se 2 (by rfl) ⟨304938, by rfl⟩ : syracuseStep 813169 = 609877) B609877
theorem B911569 : Blo 424774 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B1075427 : Blo 424774 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B911587 : Blo 424774 911587 := bstep (se 1 (by rfl) ⟨683690, by rfl⟩ : syracuseStep 911587 = 1367381) B1367381
theorem B1370353 : Blo 424774 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B1042723 : Blo 424774 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B682339 : Blo 424774 682339 := bstep (se 1 (by rfl) ⟨511754, by rfl⟩ : syracuseStep 682339 = 1023509) B1023509
theorem B1075619 : Blo 424774 1075619 := bstep (se 1 (by rfl) ⟨806714, by rfl⟩ : syracuseStep 1075619 = 1613429) B1613429
theorem B1829411 : Blo 424774 1829411 := bstep (se 1 (by rfl) ⟨1372058, by rfl⟩ : syracuseStep 1829411 = 2744117) B2744117
theorem B1436237 : Blo 424774 1436237 := bstep (se 3 (by rfl) ⟨269294, by rfl⟩ : syracuseStep 1436237 = 538589) B538589
theorem B682595 : Blo 424774 682595 := bstep (se 1 (by rfl) ⟨511946, by rfl⟩ : syracuseStep 682595 = 1023893) B1023893
theorem B1436291 : Blo 424774 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B5073635 : Blo 424774 5073635 := bstep (se 1 (by rfl) ⟨3805226, by rfl⟩ : syracuseStep 5073635 = 7610453) B7610453
theorem B1436561 : Blo 424774 1436561 := bstep (se 2 (by rfl) ⟨538710, by rfl⟩ : syracuseStep 1436561 = 1077421) B1077421
theorem B650273 : Blo 424774 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B945265 : Blo 424774 945265 := bstep (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) B708949
theorem B1076561 : Blo 424774 1076561 := bstep (se 2 (by rfl) ⟨403710, by rfl⟩ : syracuseStep 1076561 = 807421) B807421
theorem B1076611 : Blo 424774 1076611 := bstep (se 1 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 1076611 = 1614917) B1614917
theorem B1437101 : Blo 424774 1437101 := bstep (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) B538913
theorem B2158001 : Blo 424774 2158001 := bstep (se 2 (by rfl) ⟨809250, by rfl⟩ : syracuseStep 2158001 = 1618501) B1618501
theorem B1437155 : Blo 424774 1437155 := bstep (se 1 (by rfl) ⟨1077866, by rfl⟩ : syracuseStep 1437155 = 2155733) B2155733
theorem B1076753 : Blo 424774 1076753 := bstep (se 2 (by rfl) ⟨403782, by rfl⟩ : syracuseStep 1076753 = 807565) B807565
theorem B1535537 : Blo 424774 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B683569 : Blo 424774 683569 := bstep (se 2 (by rfl) ⟨256338, by rfl⟩ : syracuseStep 683569 = 512677) B512677
theorem B454243 : Blo 424774 454243 := bstep (se 1 (by rfl) ⟨340682, by rfl⟩ : syracuseStep 454243 = 681365) B681365
theorem B3468899 : Blo 424774 3468899 := bstep (se 1 (by rfl) ⟨2601674, by rfl⟩ : syracuseStep 3468899 = 5203349) B5203349
theorem B9203341 : Blo 424774 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B1535651 : Blo 424774 1535651 := bstep (se 1 (by rfl) ⟨1151738, by rfl⟩ : syracuseStep 1535651 = 2303477) B2303477
theorem B1437425 : Blo 424774 1437425 := bstep (se 2 (by rfl) ⟨539034, by rfl⟩ : syracuseStep 1437425 = 1078069) B1078069
theorem B1371917 : Blo 424774 1371917 := bstep (se 3 (by rfl) ⟨257234, by rfl⟩ : syracuseStep 1371917 = 514469) B514469
theorem B454691 : Blo 424774 454691 := bstep (se 1 (by rfl) ⟨341018, by rfl⟩ : syracuseStep 454691 = 682037) B682037
theorem B716897 : Blo 424774 716897 := bstep (se 2 (by rfl) ⟨268836, by rfl⟩ : syracuseStep 716897 = 537673) B537673
theorem B717025 : Blo 424774 717025 := bstep (se 2 (by rfl) ⟨268884, by rfl⟩ : syracuseStep 717025 = 537769) B537769
theorem B3207395 : Blo 424774 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B717059 : Blo 424774 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B1437965 : Blo 424774 1437965 := bstep (se 3 (by rfl) ⟨269618, by rfl⟩ : syracuseStep 1437965 = 539237) B539237
theorem B1438019 : Blo 424774 1438019 := bstep (se 1 (by rfl) ⟨1078514, by rfl⟩ : syracuseStep 1438019 = 2157029) B2157029
theorem B717187 : Blo 424774 717187 := bstep (se 1 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 717187 = 1075781) B1075781
theorem B913859 : Blo 424774 913859 := bstep (se 1 (by rfl) ⟨685394, by rfl⟩ : syracuseStep 913859 = 1370789) B1370789
theorem B684497 : Blo 424774 684497 := bstep (se 2 (by rfl) ⟨256686, by rfl⟩ : syracuseStep 684497 = 513373) B513373
theorem B1077745 : Blo 424774 1077745 := bstep (se 2 (by rfl) ⟨404154, by rfl⟩ : syracuseStep 1077745 = 808309) B808309
theorem B1831409 : Blo 424774 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B717329 : Blo 424774 717329 := bstep (se 2 (by rfl) ⟨268998, by rfl⟩ : syracuseStep 717329 = 537997) B537997
theorem B1438289 : Blo 424774 1438289 := bstep (se 2 (by rfl) ⟨539358, by rfl⟩ : syracuseStep 1438289 = 1078717) B1078717
theorem B717457 : Blo 424774 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B717491 : Blo 424774 717491 := bstep (se 1 (by rfl) ⟨538118, by rfl⟩ : syracuseStep 717491 = 1076237) B1076237
theorem B1078019 : Blo 424774 1078019 := bstep (se 1 (by rfl) ⟨808514, by rfl⟩ : syracuseStep 1078019 = 1617029) B1617029
theorem B717619 : Blo 424774 717619 := bstep (se 1 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 717619 = 1076429) B1076429
theorem B2159459 : Blo 424774 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B914321 : Blo 424774 914321 := bstep (se 2 (by rfl) ⟨342870, by rfl⟩ : syracuseStep 914321 = 685741) B685741
theorem B717761 : Blo 424774 717761 := bstep (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) B538321
theorem B1078211 : Blo 424774 1078211 := bstep (se 1 (by rfl) ⟨808658, by rfl⟩ : syracuseStep 1078211 = 1617317) B1617317
theorem B717889 : Blo 424774 717889 := bstep (se 2 (by rfl) ⟨269208, by rfl⟩ : syracuseStep 717889 = 538417) B538417
theorem B717923 : Blo 424774 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B1438829 : Blo 424774 1438829 := bstep (se 3 (by rfl) ⟨269780, by rfl⟩ : syracuseStep 1438829 = 539561) B539561
theorem B1438883 : Blo 424774 1438883 := bstep (se 1 (by rfl) ⟨1079162, by rfl⟩ : syracuseStep 1438883 = 2158325) B2158325
theorem B718051 : Blo 424774 718051 := bstep (se 1 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 718051 = 1077077) B1077077
theorem B1209617 : Blo 424774 1209617 := bstep (se 2 (by rfl) ⟨453606, by rfl⟩ : syracuseStep 1209617 = 907213) B907213
theorem B685331 : Blo 424774 685331 := bstep (se 1 (by rfl) ⟨513998, by rfl⟩ : syracuseStep 685331 = 1027997) B1027997
theorem B685363 : Blo 424774 685363 := bstep (se 1 (by rfl) ⟨514022, by rfl⟩ : syracuseStep 685363 = 1028045) B1028045
theorem B4388195 : Blo 424774 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B718193 : Blo 424774 718193 := bstep (se 2 (by rfl) ⟨269322, by rfl⟩ : syracuseStep 718193 = 538645) B538645
theorem B456067 : Blo 424774 456067 := bstep (se 1 (by rfl) ⟨342050, by rfl⟩ : syracuseStep 456067 = 684101) B684101
theorem B521635 : Blo 424774 521635 := bstep (se 1 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 521635 = 782453) B782453
theorem B1439153 : Blo 424774 1439153 := bstep (se 2 (by rfl) ⟨539682, by rfl⟩ : syracuseStep 1439153 = 1079365) B1079365
theorem B718321 : Blo 424774 718321 := bstep (se 2 (by rfl) ⟨269370, by rfl⟩ : syracuseStep 718321 = 538741) B538741
theorem B718355 : Blo 424774 718355 := bstep (se 1 (by rfl) ⟨538766, by rfl⟩ : syracuseStep 718355 = 1077533) B1077533
theorem B4879925 : Blo 424774 4879925 := bstep (se 5 (by rfl) ⟨228746, by rfl⟩ : syracuseStep 4879925 = 457493) B457493
theorem B1734257 : Blo 424774 1734257 := bstep (se 2 (by rfl) ⟨650346, by rfl⟩ : syracuseStep 1734257 = 1300693) B1300693
theorem B2160269 : Blo 424774 2160269 := bstep (se 3 (by rfl) ⟨405050, by rfl⟩ : syracuseStep 2160269 = 810101) B810101
theorem B718483 : Blo 424774 718483 := bstep (se 1 (by rfl) ⟨538862, by rfl⟩ : syracuseStep 718483 = 1077725) B1077725
theorem B718625 : Blo 424774 718625 := bstep (se 2 (by rfl) ⟨269484, by rfl⟩ : syracuseStep 718625 = 538969) B538969
theorem B1079153 : Blo 424774 1079153 := bstep (se 2 (by rfl) ⟨404682, by rfl⟩ : syracuseStep 1079153 = 809365) B809365
theorem B718753 : Blo 424774 718753 := bstep (se 2 (by rfl) ⟨269532, by rfl⟩ : syracuseStep 718753 = 539065) B539065
theorem B1079203 : Blo 424774 1079203 := bstep (se 1 (by rfl) ⟨809402, by rfl⟩ : syracuseStep 1079203 = 1618805) B1618805
theorem B718787 : Blo 424774 718787 := bstep (se 1 (by rfl) ⟨539090, by rfl⟩ : syracuseStep 718787 = 1078181) B1078181
theorem B1439693 : Blo 424774 1439693 := bstep (se 3 (by rfl) ⟨269942, by rfl⟩ : syracuseStep 1439693 = 539885) B539885
theorem B2455523 : Blo 424774 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B1439747 : Blo 424774 1439747 := bstep (se 1 (by rfl) ⟨1079810, by rfl⟩ : syracuseStep 1439747 = 2159621) B2159621
theorem B1210403 : Blo 424774 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B1079345 : Blo 424774 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B718915 : Blo 424774 718915 := bstep (se 1 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 718915 = 1078373) B1078373
theorem B915619 : Blo 424774 915619 := bstep (se 1 (by rfl) ⟨686714, by rfl⟩ : syracuseStep 915619 = 1373429) B1373429
theorem B719057 : Blo 424774 719057 := bstep (se 2 (by rfl) ⟨269646, by rfl⟩ : syracuseStep 719057 = 539293) B539293
theorem B686291 : Blo 424774 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B1440017 : Blo 424774 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B686369 : Blo 424774 686369 := bstep (se 2 (by rfl) ⟨257388, by rfl⟩ : syracuseStep 686369 = 514777) B514777
theorem B719185 : Blo 424774 719185 := bstep (se 2 (by rfl) ⟨269694, by rfl⟩ : syracuseStep 719185 = 539389) B539389
theorem B1210733 : Blo 424774 1210733 := bstep (se 3 (by rfl) ⟨227012, by rfl⟩ : syracuseStep 1210733 = 454025) B454025
theorem B719219 : Blo 424774 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1210801 : Blo 424774 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B9238981 : Blo 424774 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B719347 : Blo 424774 719347 := bstep (se 1 (by rfl) ⟨539510, by rfl⟩ : syracuseStep 719347 = 1079021) B1079021
theorem B686593 : Blo 424774 686593 := bstep (se 2 (by rfl) ⟨257472, by rfl⟩ : syracuseStep 686593 = 514945) B514945
theorem B457331 : Blo 424774 457331 := bstep (se 1 (by rfl) ⟨342998, by rfl⟩ : syracuseStep 457331 = 685997) B685997
theorem B719489 : Blo 424774 719489 := bstep (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) B539617
theorem B1211075 : Blo 424774 1211075 := bstep (se 1 (by rfl) ⟨908306, by rfl⟩ : syracuseStep 1211075 = 1816613) B1816613
theorem B719617 : Blo 424774 719617 := bstep (se 2 (by rfl) ⟨269856, by rfl⟩ : syracuseStep 719617 = 539713) B539713
theorem B719651 : Blo 424774 719651 := bstep (se 1 (by rfl) ⟨539738, by rfl⟩ : syracuseStep 719651 = 1079477) B1079477
theorem B1538851 : Blo 424774 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B1440557 : Blo 424774 1440557 := bstep (se 3 (by rfl) ⟨270104, by rfl⟩ : syracuseStep 1440557 = 540209) B540209
theorem B424787 : Blo 424774 424787 := bstep (se 1 (by rfl) ⟨318590, by rfl⟩ : syracuseStep 424787 = 637181) B637181
theorem B424803 : Blo 424774 424803 := bstep (se 1 (by rfl) ⟨318602, by rfl⟩ : syracuseStep 424803 = 637205) B637205
theorem B1440611 : Blo 424774 1440611 := bstep (se 1 (by rfl) ⟨1080458, by rfl⟩ : syracuseStep 1440611 = 2160917) B2160917
theorem B424819 : Blo 424774 424819 := bstep (se 1 (by rfl) ⟨318614, by rfl⟩ : syracuseStep 424819 = 637229) B637229
theorem B424835 : Blo 424774 424835 := bstep (se 1 (by rfl) ⟨318626, by rfl⟩ : syracuseStep 424835 = 637253) B637253
theorem B424851 : Blo 424774 424851 := bstep (se 1 (by rfl) ⟨318638, by rfl⟩ : syracuseStep 424851 = 637277) B637277
theorem B424867 : Blo 424774 424867 := bstep (se 1 (by rfl) ⟨318650, by rfl⟩ : syracuseStep 424867 = 637301) B637301
theorem B719779 : Blo 424774 719779 := bstep (se 1 (by rfl) ⟨539834, by rfl⟩ : syracuseStep 719779 = 1079669) B1079669
theorem B424883 : Blo 424774 424883 := bstep (se 1 (by rfl) ⟨318662, by rfl⟩ : syracuseStep 424883 = 637325) B637325
theorem B424899 : Blo 424774 424899 := bstep (se 1 (by rfl) ⟨318674, by rfl⟩ : syracuseStep 424899 = 637349) B637349
theorem B424915 : Blo 424774 424915 := bstep (se 1 (by rfl) ⟨318686, by rfl⟩ : syracuseStep 424915 = 637373) B637373
theorem B424931 : Blo 424774 424931 := bstep (se 1 (by rfl) ⟨318698, by rfl⟩ : syracuseStep 424931 = 637397) B637397
theorem B424947 : Blo 424774 424947 := bstep (se 1 (by rfl) ⟨318710, by rfl⟩ : syracuseStep 424947 = 637421) B637421
theorem B424963 : Blo 424774 424963 := bstep (se 1 (by rfl) ⟨318722, by rfl⟩ : syracuseStep 424963 = 637445) B637445
theorem B1080337 : Blo 424774 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B424979 : Blo 424774 424979 := bstep (se 1 (by rfl) ⟨318734, by rfl⟩ : syracuseStep 424979 = 637469) B637469
theorem B424995 : Blo 424774 424995 := bstep (se 1 (by rfl) ⟨318746, by rfl⟩ : syracuseStep 424995 = 637493) B637493
theorem B719921 : Blo 424774 719921 := bstep (se 2 (by rfl) ⟨269970, by rfl⟩ : syracuseStep 719921 = 539941) B539941
theorem B425011 : Blo 424774 425011 := bstep (se 1 (by rfl) ⟨318758, by rfl⟩ : syracuseStep 425011 = 637517) B637517
theorem B425027 : Blo 424774 425027 := bstep (se 1 (by rfl) ⟨318770, by rfl⟩ : syracuseStep 425027 = 637541) B637541
theorem B3243077 : Blo 424774 3243077 := bstep (se 4 (by rfl) ⟨304038, by rfl⟩ : syracuseStep 3243077 = 608077) B608077
theorem B425043 : Blo 424774 425043 := bstep (se 1 (by rfl) ⟨318782, by rfl⟩ : syracuseStep 425043 = 637565) B637565
theorem B425059 : Blo 424774 425059 := bstep (se 1 (by rfl) ⟨318794, by rfl⟩ : syracuseStep 425059 = 637589) B637589
theorem B1440881 : Blo 424774 1440881 := bstep (se 2 (by rfl) ⟨540330, by rfl⟩ : syracuseStep 1440881 = 1080661) B1080661
theorem B425075 : Blo 424774 425075 := bstep (se 1 (by rfl) ⟨318806, by rfl⟩ : syracuseStep 425075 = 637613) B637613
theorem B425091 : Blo 424774 425091 := bstep (se 1 (by rfl) ⟨318818, by rfl⟩ : syracuseStep 425091 = 637637) B637637
theorem B425107 : Blo 424774 425107 := bstep (se 1 (by rfl) ⟨318830, by rfl⟩ : syracuseStep 425107 = 637661) B637661
theorem B425123 : Blo 424774 425123 := bstep (se 1 (by rfl) ⟨318842, by rfl⟩ : syracuseStep 425123 = 637685) B637685
theorem B720049 : Blo 424774 720049 := bstep (se 2 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 720049 = 540037) B540037
theorem B425139 : Blo 424774 425139 := bstep (se 1 (by rfl) ⟨318854, by rfl⟩ : syracuseStep 425139 = 637709) B637709
theorem B425155 : Blo 424774 425155 := bstep (se 1 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 425155 = 637733) B637733
theorem B425171 : Blo 424774 425171 := bstep (se 1 (by rfl) ⟨318878, by rfl⟩ : syracuseStep 425171 = 637757) B637757
theorem B720083 : Blo 424774 720083 := bstep (se 1 (by rfl) ⟨540062, by rfl⟩ : syracuseStep 720083 = 1080125) B1080125
theorem B425187 : Blo 424774 425187 := bstep (se 1 (by rfl) ⟨318890, by rfl⟩ : syracuseStep 425187 = 637781) B637781
theorem B1539299 : Blo 424774 1539299 := bstep (se 1 (by rfl) ⟨1154474, by rfl⟩ : syracuseStep 1539299 = 2308949) B2308949
theorem B425203 : Blo 424774 425203 := bstep (se 1 (by rfl) ⟨318902, by rfl⟩ : syracuseStep 425203 = 637805) B637805
theorem B425219 : Blo 424774 425219 := bstep (se 1 (by rfl) ⟨318914, by rfl⟩ : syracuseStep 425219 = 637829) B637829
theorem B1539341 : Blo 424774 1539341 := bstep (se 3 (by rfl) ⟨288626, by rfl⟩ : syracuseStep 1539341 = 577253) B577253
theorem B425235 : Blo 424774 425235 := bstep (se 1 (by rfl) ⟨318926, by rfl⟩ : syracuseStep 425235 = 637853) B637853
theorem B1080611 : Blo 424774 1080611 := bstep (se 1 (by rfl) ⟨810458, by rfl⟩ : syracuseStep 1080611 = 1620917) B1620917
theorem B621859 : Blo 424774 621859 := bstep (se 1 (by rfl) ⟨466394, by rfl⟩ : syracuseStep 621859 = 932789) B932789
theorem B425251 : Blo 424774 425251 := bstep (se 1 (by rfl) ⟨318938, by rfl⟩ : syracuseStep 425251 = 637877) B637877
theorem B425267 : Blo 424774 425267 := bstep (se 1 (by rfl) ⟨318950, by rfl⟩ : syracuseStep 425267 = 637901) B637901
theorem B425283 : Blo 424774 425283 := bstep (se 1 (by rfl) ⟨318962, by rfl⟩ : syracuseStep 425283 = 637925) B637925
theorem B720211 : Blo 424774 720211 := bstep (se 1 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 720211 = 1080317) B1080317
theorem B425299 : Blo 424774 425299 := bstep (se 1 (by rfl) ⟨318974, by rfl⟩ : syracuseStep 425299 = 637949) B637949
theorem B425315 : Blo 424774 425315 := bstep (se 1 (by rfl) ⟨318986, by rfl⟩ : syracuseStep 425315 = 637973) B637973
theorem B425331 : Blo 424774 425331 := bstep (se 1 (by rfl) ⟨318998, by rfl⟩ : syracuseStep 425331 = 637997) B637997
theorem B425347 : Blo 424774 425347 := bstep (se 1 (by rfl) ⟨319010, by rfl⟩ : syracuseStep 425347 = 638021) B638021
theorem B425363 : Blo 424774 425363 := bstep (se 1 (by rfl) ⟨319022, by rfl⟩ : syracuseStep 425363 = 638045) B638045
theorem B425379 : Blo 424774 425379 := bstep (se 1 (by rfl) ⟨319034, by rfl⟩ : syracuseStep 425379 = 638069) B638069
theorem B425395 : Blo 424774 425395 := bstep (se 1 (by rfl) ⟨319046, by rfl⟩ : syracuseStep 425395 = 638093) B638093
theorem B425411 : Blo 424774 425411 := bstep (se 1 (by rfl) ⟨319058, by rfl⟩ : syracuseStep 425411 = 638117) B638117
theorem B425427 : Blo 424774 425427 := bstep (se 1 (by rfl) ⟨319070, by rfl⟩ : syracuseStep 425427 = 638141) B638141
theorem B720353 : Blo 424774 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B1080803 : Blo 424774 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B425443 : Blo 424774 425443 := bstep (se 1 (by rfl) ⟨319082, by rfl⟩ : syracuseStep 425443 = 638165) B638165
theorem B425459 : Blo 424774 425459 := bstep (se 1 (by rfl) ⟨319094, by rfl⟩ : syracuseStep 425459 = 638189) B638189
theorem B425475 : Blo 424774 425475 := bstep (se 1 (by rfl) ⟨319106, by rfl⟩ : syracuseStep 425475 = 638213) B638213
theorem B1211917 : Blo 424774 1211917 := bstep (se 3 (by rfl) ⟨227234, by rfl⟩ : syracuseStep 1211917 = 454469) B454469
theorem B425491 : Blo 424774 425491 := bstep (se 1 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 425491 = 638237) B638237
theorem B9895445 : Blo 424774 9895445 := bstep (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) B463849
theorem B425507 : Blo 424774 425507 := bstep (se 1 (by rfl) ⟨319130, by rfl⟩ : syracuseStep 425507 = 638261) B638261
theorem B425523 : Blo 424774 425523 := bstep (se 1 (by rfl) ⟨319142, by rfl⟩ : syracuseStep 425523 = 638285) B638285
theorem B425539 : Blo 424774 425539 := bstep (se 1 (by rfl) ⟨319154, by rfl⟩ : syracuseStep 425539 = 638309) B638309
theorem B425555 : Blo 424774 425555 := bstep (se 1 (by rfl) ⟨319166, by rfl⟩ : syracuseStep 425555 = 638333) B638333
theorem B720481 : Blo 424774 720481 := bstep (se 2 (by rfl) ⟨270180, by rfl⟩ : syracuseStep 720481 = 540361) B540361
theorem B425571 : Blo 424774 425571 := bstep (se 1 (by rfl) ⟨319178, by rfl⟩ : syracuseStep 425571 = 638357) B638357
theorem B425587 : Blo 424774 425587 := bstep (se 1 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 425587 = 638381) B638381
theorem B425603 : Blo 424774 425603 := bstep (se 1 (by rfl) ⟨319202, by rfl⟩ : syracuseStep 425603 = 638405) B638405
theorem B720515 : Blo 424774 720515 := bstep (se 1 (by rfl) ⟨540386, by rfl⟩ : syracuseStep 720515 = 1080773) B1080773
theorem B1441421 : Blo 424774 1441421 := bstep (se 3 (by rfl) ⟨270266, by rfl⟩ : syracuseStep 1441421 = 540533) B540533
theorem B425619 : Blo 424774 425619 := bstep (se 1 (by rfl) ⟨319214, by rfl⟩ : syracuseStep 425619 = 638429) B638429
theorem B425635 : Blo 424774 425635 := bstep (se 1 (by rfl) ⟨319226, by rfl⟩ : syracuseStep 425635 = 638453) B638453
theorem B1212077 : Blo 424774 1212077 := bstep (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) B454529
theorem B425651 : Blo 424774 425651 := bstep (se 1 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 425651 = 638477) B638477
theorem B425667 : Blo 424774 425667 := bstep (se 1 (by rfl) ⟨319250, by rfl⟩ : syracuseStep 425667 = 638501) B638501
theorem B1441475 : Blo 424774 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B425683 : Blo 424774 425683 := bstep (se 1 (by rfl) ⟨319262, by rfl⟩ : syracuseStep 425683 = 638525) B638525
theorem B425699 : Blo 424774 425699 := bstep (se 1 (by rfl) ⟨319274, by rfl⟩ : syracuseStep 425699 = 638549) B638549
theorem B425715 : Blo 424774 425715 := bstep (se 1 (by rfl) ⟨319286, by rfl⟩ : syracuseStep 425715 = 638573) B638573
theorem B425731 : Blo 424774 425731 := bstep (se 1 (by rfl) ⟨319298, by rfl⟩ : syracuseStep 425731 = 638597) B638597
theorem B720643 : Blo 424774 720643 := bstep (se 1 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 720643 = 1080965) B1080965
theorem B1736461 : Blo 424774 1736461 := bstep (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) B651173
theorem B425747 : Blo 424774 425747 := bstep (se 1 (by rfl) ⟨319310, by rfl⟩ : syracuseStep 425747 = 638621) B638621
theorem B425763 : Blo 424774 425763 := bstep (se 1 (by rfl) ⟨319322, by rfl⟩ : syracuseStep 425763 = 638645) B638645
theorem B425779 : Blo 424774 425779 := bstep (se 1 (by rfl) ⟨319334, by rfl⟩ : syracuseStep 425779 = 638669) B638669
theorem B425795 : Blo 424774 425795 := bstep (se 1 (by rfl) ⟨319346, by rfl⟩ : syracuseStep 425795 = 638693) B638693
theorem B425811 : Blo 424774 425811 := bstep (se 1 (by rfl) ⟨319358, by rfl⟩ : syracuseStep 425811 = 638717) B638717
theorem B1212259 : Blo 424774 1212259 := bstep (se 1 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 1212259 = 1818389) B1818389
theorem B425827 : Blo 424774 425827 := bstep (se 1 (by rfl) ⟨319370, by rfl⟩ : syracuseStep 425827 = 638741) B638741
theorem B425843 : Blo 424774 425843 := bstep (se 1 (by rfl) ⟨319382, by rfl⟩ : syracuseStep 425843 = 638765) B638765
theorem B425859 : Blo 424774 425859 := bstep (se 1 (by rfl) ⟨319394, by rfl⟩ : syracuseStep 425859 = 638789) B638789
theorem B720785 : Blo 424774 720785 := bstep (se 2 (by rfl) ⟨270294, by rfl⟩ : syracuseStep 720785 = 540589) B540589
theorem B425875 : Blo 424774 425875 := bstep (se 1 (by rfl) ⟨319406, by rfl⟩ : syracuseStep 425875 = 638813) B638813
theorem B425891 : Blo 424774 425891 := bstep (se 1 (by rfl) ⟨319418, by rfl⟩ : syracuseStep 425891 = 638837) B638837
theorem B425907 : Blo 424774 425907 := bstep (se 1 (by rfl) ⟨319430, by rfl⟩ : syracuseStep 425907 = 638861) B638861
theorem B425923 : Blo 424774 425923 := bstep (se 1 (by rfl) ⟨319442, by rfl⟩ : syracuseStep 425923 = 638885) B638885
theorem B1441745 : Blo 424774 1441745 := bstep (se 2 (by rfl) ⟨540654, by rfl⟩ : syracuseStep 1441745 = 1081309) B1081309
theorem B425939 : Blo 424774 425939 := bstep (se 1 (by rfl) ⟨319454, by rfl⟩ : syracuseStep 425939 = 638909) B638909
theorem B425955 : Blo 424774 425955 := bstep (se 1 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 425955 = 638933) B638933
theorem B425971 : Blo 424774 425971 := bstep (se 1 (by rfl) ⟨319478, by rfl⟩ : syracuseStep 425971 = 638957) B638957
theorem B425995 : Blo 424774 425995 := bstep (se 1 (by rfl) ⟨319496, by rfl⟩ : syracuseStep 425995 = 638993) B638993
theorem B3244049 : Blo 424774 3244049 := bstep (se 2 (by rfl) ⟨1216518, by rfl⟩ : syracuseStep 3244049 = 2433037) B2433037
theorem B426007 : Blo 424774 426007 := bstep (se 1 (by rfl) ⟨319505, by rfl⟩ : syracuseStep 426007 = 639011) B639011
theorem B426027 : Blo 424774 426027 := bstep (se 1 (by rfl) ⟨319520, by rfl⟩ : syracuseStep 426027 = 639041) B639041
theorem B426039 : Blo 424774 426039 := bstep (se 1 (by rfl) ⟨319529, by rfl⟩ : syracuseStep 426039 = 639059) B639059
theorem B426059 : Blo 424774 426059 := bstep (se 1 (by rfl) ⟨319544, by rfl⟩ : syracuseStep 426059 = 639089) B639089
theorem B426071 : Blo 424774 426071 := bstep (se 1 (by rfl) ⟨319553, by rfl⟩ : syracuseStep 426071 = 639107) B639107
theorem B1212509 : Blo 424774 1212509 := bstep (se 3 (by rfl) ⟨227345, by rfl⟩ : syracuseStep 1212509 = 454691) B454691
theorem B426091 : Blo 424774 426091 := bstep (se 1 (by rfl) ⟨319568, by rfl⟩ : syracuseStep 426091 = 639137) B639137
theorem B426103 : Blo 424774 426103 := bstep (se 1 (by rfl) ⟨319577, by rfl⟩ : syracuseStep 426103 = 639155) B639155
theorem B426123 : Blo 424774 426123 := bstep (se 1 (by rfl) ⟨319592, by rfl⟩ : syracuseStep 426123 = 639185) B639185
theorem B426135 : Blo 424774 426135 := bstep (se 1 (by rfl) ⟨319601, by rfl⟩ : syracuseStep 426135 = 639203) B639203
theorem B426155 : Blo 424774 426155 := bstep (se 1 (by rfl) ⟨319616, by rfl⟩ : syracuseStep 426155 = 639233) B639233
theorem B426167 : Blo 424774 426167 := bstep (se 1 (by rfl) ⟨319625, by rfl⟩ : syracuseStep 426167 = 639251) B639251
theorem B426187 : Blo 424774 426187 := bstep (se 1 (by rfl) ⟨319640, by rfl⟩ : syracuseStep 426187 = 639281) B639281
theorem B426199 : Blo 424774 426199 := bstep (se 1 (by rfl) ⟨319649, by rfl⟩ : syracuseStep 426199 = 639299) B639299
theorem B426219 : Blo 424774 426219 := bstep (se 1 (by rfl) ⟨319664, by rfl⟩ : syracuseStep 426219 = 639329) B639329
theorem B426231 : Blo 424774 426231 := bstep (se 1 (by rfl) ⟨319673, by rfl⟩ : syracuseStep 426231 = 639347) B639347
theorem B426251 : Blo 424774 426251 := bstep (se 1 (by rfl) ⟨319688, by rfl⟩ : syracuseStep 426251 = 639377) B639377
theorem B721163 : Blo 424774 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B426263 : Blo 424774 426263 := bstep (se 1 (by rfl) ⟨319697, by rfl⟩ : syracuseStep 426263 = 639395) B639395
theorem B426283 : Blo 424774 426283 := bstep (se 1 (by rfl) ⟨319712, by rfl⟩ : syracuseStep 426283 = 639425) B639425
theorem B426295 : Blo 424774 426295 := bstep (se 1 (by rfl) ⟨319721, by rfl⟩ : syracuseStep 426295 = 639443) B639443
theorem B426315 : Blo 424774 426315 := bstep (se 1 (by rfl) ⟨319736, by rfl⟩ : syracuseStep 426315 = 639473) B639473
theorem B1442123 : Blo 424774 1442123 := bstep (se 1 (by rfl) ⟨1081592, by rfl⟩ : syracuseStep 1442123 = 2163185) B2163185
theorem B426327 : Blo 424774 426327 := bstep (se 1 (by rfl) ⟨319745, by rfl⟩ : syracuseStep 426327 = 639491) B639491
theorem B426347 : Blo 424774 426347 := bstep (se 1 (by rfl) ⟨319760, by rfl⟩ : syracuseStep 426347 = 639521) B639521
theorem B426359 : Blo 424774 426359 := bstep (se 1 (by rfl) ⟨319769, by rfl⟩ : syracuseStep 426359 = 639539) B639539
theorem B426379 : Blo 424774 426379 := bstep (se 1 (by rfl) ⟨319784, by rfl⟩ : syracuseStep 426379 = 639569) B639569
theorem B721291 : Blo 424774 721291 := bstep (se 1 (by rfl) ⟨540968, by rfl⟩ : syracuseStep 721291 = 1081937) B1081937
theorem B426391 : Blo 424774 426391 := bstep (se 1 (by rfl) ⟨319793, by rfl⟩ : syracuseStep 426391 = 639587) B639587
theorem B426411 : Blo 424774 426411 := bstep (se 1 (by rfl) ⟨319808, by rfl⟩ : syracuseStep 426411 = 639617) B639617
theorem B426423 : Blo 424774 426423 := bstep (se 1 (by rfl) ⟨319817, by rfl⟩ : syracuseStep 426423 = 639635) B639635
theorem B426443 : Blo 424774 426443 := bstep (se 1 (by rfl) ⟨319832, by rfl⟩ : syracuseStep 426443 = 639665) B639665
theorem B426455 : Blo 424774 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B426475 : Blo 424774 426475 := bstep (se 1 (by rfl) ⟨319856, by rfl⟩ : syracuseStep 426475 = 639713) B639713
theorem B426487 : Blo 424774 426487 := bstep (se 1 (by rfl) ⟨319865, by rfl⟩ : syracuseStep 426487 = 639731) B639731
theorem B426507 : Blo 424774 426507 := bstep (se 1 (by rfl) ⟨319880, by rfl⟩ : syracuseStep 426507 = 639761) B639761
theorem B1245719 : Blo 424774 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B426519 : Blo 424774 426519 := bstep (se 1 (by rfl) ⟨319889, by rfl⟩ : syracuseStep 426519 = 639779) B639779
theorem B721433 : Blo 424774 721433 := bstep (se 2 (by rfl) ⟨270537, by rfl⟩ : syracuseStep 721433 = 541075) B541075
theorem B426539 : Blo 424774 426539 := bstep (se 1 (by rfl) ⟨319904, by rfl⟩ : syracuseStep 426539 = 639809) B639809
theorem B1081907 : Blo 424774 1081907 := bstep (se 1 (by rfl) ⟨811430, by rfl⟩ : syracuseStep 1081907 = 1622861) B1622861
theorem B426551 : Blo 424774 426551 := bstep (se 1 (by rfl) ⟨319913, by rfl⟩ : syracuseStep 426551 = 639827) B639827
theorem B426571 : Blo 424774 426571 := bstep (se 1 (by rfl) ⟨319928, by rfl⟩ : syracuseStep 426571 = 639857) B639857
theorem B426583 : Blo 424774 426583 := bstep (se 1 (by rfl) ⟨319937, by rfl⟩ : syracuseStep 426583 = 639875) B639875
theorem B1442393 : Blo 424774 1442393 := bstep (se 2 (by rfl) ⟨540897, by rfl⟩ : syracuseStep 1442393 = 1081795) B1081795
theorem B1737305 : Blo 424774 1737305 := bstep (se 2 (by rfl) ⟨651489, by rfl⟩ : syracuseStep 1737305 = 1302979) B1302979
theorem B8553053 : Blo 424774 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B426603 : Blo 424774 426603 := bstep (se 1 (by rfl) ⟨319952, by rfl⟩ : syracuseStep 426603 = 639905) B639905
theorem B426615 : Blo 424774 426615 := bstep (se 1 (by rfl) ⟨319961, by rfl⟩ : syracuseStep 426615 = 639923) B639923
theorem B426635 : Blo 424774 426635 := bstep (se 1 (by rfl) ⟨319976, by rfl⟩ : syracuseStep 426635 = 639953) B639953
theorem B426647 : Blo 424774 426647 := bstep (se 1 (by rfl) ⟨319985, by rfl⟩ : syracuseStep 426647 = 639971) B639971
theorem B721561 : Blo 424774 721561 := bstep (se 2 (by rfl) ⟨270585, by rfl⟩ : syracuseStep 721561 = 541171) B541171
theorem B426667 : Blo 424774 426667 := bstep (se 1 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 426667 = 640001) B640001
theorem B426679 : Blo 424774 426679 := bstep (se 1 (by rfl) ⟨320009, by rfl⟩ : syracuseStep 426679 = 640019) B640019
theorem B426699 : Blo 424774 426699 := bstep (se 1 (by rfl) ⟨320024, by rfl⟩ : syracuseStep 426699 = 640049) B640049
theorem B426711 : Blo 424774 426711 := bstep (se 1 (by rfl) ⟨320033, by rfl⟩ : syracuseStep 426711 = 640067) B640067
theorem B426731 : Blo 424774 426731 := bstep (se 1 (by rfl) ⟨320048, by rfl⟩ : syracuseStep 426731 = 640097) B640097
theorem B426743 : Blo 424774 426743 := bstep (se 1 (by rfl) ⟨320057, by rfl⟩ : syracuseStep 426743 = 640115) B640115
theorem B426763 : Blo 424774 426763 := bstep (se 1 (by rfl) ⟨320072, by rfl⟩ : syracuseStep 426763 = 640145) B640145
theorem B426775 : Blo 424774 426775 := bstep (se 1 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 426775 = 640163) B640163
theorem B426795 : Blo 424774 426795 := bstep (se 1 (by rfl) ⟨320096, by rfl⟩ : syracuseStep 426795 = 640193) B640193
theorem B426807 : Blo 424774 426807 := bstep (se 1 (by rfl) ⟨320105, by rfl⟩ : syracuseStep 426807 = 640211) B640211
theorem B426827 : Blo 424774 426827 := bstep (se 1 (by rfl) ⟨320120, by rfl⟩ : syracuseStep 426827 = 640241) B640241
theorem B426839 : Blo 424774 426839 := bstep (se 1 (by rfl) ⟨320129, by rfl⟩ : syracuseStep 426839 = 640259) B640259
theorem B426859 : Blo 424774 426859 := bstep (se 1 (by rfl) ⟨320144, by rfl⟩ : syracuseStep 426859 = 640289) B640289
theorem B426871 : Blo 424774 426871 := bstep (se 1 (by rfl) ⟨320153, by rfl⟩ : syracuseStep 426871 = 640307) B640307
theorem B426891 : Blo 424774 426891 := bstep (se 1 (by rfl) ⟨320168, by rfl⟩ : syracuseStep 426891 = 640337) B640337
theorem B426903 : Blo 424774 426903 := bstep (se 1 (by rfl) ⟨320177, by rfl⟩ : syracuseStep 426903 = 640355) B640355
theorem B426923 : Blo 424774 426923 := bstep (se 1 (by rfl) ⟨320192, by rfl⟩ : syracuseStep 426923 = 640385) B640385
theorem B426935 : Blo 424774 426935 := bstep (se 1 (by rfl) ⟨320201, by rfl⟩ : syracuseStep 426935 = 640403) B640403
theorem B426955 : Blo 424774 426955 := bstep (se 1 (by rfl) ⟨320216, by rfl⟩ : syracuseStep 426955 = 640433) B640433
theorem B426967 : Blo 424774 426967 := bstep (se 1 (by rfl) ⟨320225, by rfl⟩ : syracuseStep 426967 = 640451) B640451
theorem B426987 : Blo 424774 426987 := bstep (se 1 (by rfl) ⟨320240, by rfl⟩ : syracuseStep 426987 = 640481) B640481
theorem B426999 : Blo 424774 426999 := bstep (se 1 (by rfl) ⟨320249, by rfl⟩ : syracuseStep 426999 = 640499) B640499
theorem B427019 : Blo 424774 427019 := bstep (se 1 (by rfl) ⟨320264, by rfl⟩ : syracuseStep 427019 = 640529) B640529
theorem B427031 : Blo 424774 427031 := bstep (se 1 (by rfl) ⟨320273, by rfl⟩ : syracuseStep 427031 = 640547) B640547
theorem B427051 : Blo 424774 427051 := bstep (se 1 (by rfl) ⟨320288, by rfl⟩ : syracuseStep 427051 = 640577) B640577
theorem B427063 : Blo 424774 427063 := bstep (se 1 (by rfl) ⟨320297, by rfl⟩ : syracuseStep 427063 = 640595) B640595
theorem B427083 : Blo 424774 427083 := bstep (se 1 (by rfl) ⟨320312, by rfl⟩ : syracuseStep 427083 = 640625) B640625
theorem B1082443 : Blo 424774 1082443 := bstep (se 1 (by rfl) ⟨811832, by rfl⟩ : syracuseStep 1082443 = 1623665) B1623665
theorem B427095 : Blo 424774 427095 := bstep (se 1 (by rfl) ⟨320321, by rfl⟩ : syracuseStep 427095 = 640643) B640643
theorem B427115 : Blo 424774 427115 := bstep (se 1 (by rfl) ⟨320336, by rfl⟩ : syracuseStep 427115 = 640673) B640673
theorem B427127 : Blo 424774 427127 := bstep (se 1 (by rfl) ⟨320345, by rfl⟩ : syracuseStep 427127 = 640691) B640691
theorem B427147 : Blo 424774 427147 := bstep (se 1 (by rfl) ⟨320360, by rfl⟩ : syracuseStep 427147 = 640721) B640721
theorem B427159 : Blo 424774 427159 := bstep (se 1 (by rfl) ⟨320369, by rfl⟩ : syracuseStep 427159 = 640739) B640739
theorem B427179 : Blo 424774 427179 := bstep (se 1 (by rfl) ⟨320384, by rfl⟩ : syracuseStep 427179 = 640769) B640769
theorem B427191 : Blo 424774 427191 := bstep (se 1 (by rfl) ⟨320393, by rfl⟩ : syracuseStep 427191 = 640787) B640787
theorem B427211 : Blo 424774 427211 := bstep (se 1 (by rfl) ⟨320408, by rfl⟩ : syracuseStep 427211 = 640817) B640817
theorem B427223 : Blo 424774 427223 := bstep (se 1 (by rfl) ⟨320417, by rfl⟩ : syracuseStep 427223 = 640835) B640835
theorem B722135 : Blo 424774 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B1082585 : Blo 424774 1082585 := bstep (se 2 (by rfl) ⟨405969, by rfl⟩ : syracuseStep 1082585 = 811939) B811939
theorem B427243 : Blo 424774 427243 := bstep (se 1 (by rfl) ⟨320432, by rfl⟩ : syracuseStep 427243 = 640865) B640865
theorem B427255 : Blo 424774 427255 := bstep (se 1 (by rfl) ⟨320441, by rfl⟩ : syracuseStep 427255 = 640883) B640883
theorem B427275 : Blo 424774 427275 := bstep (se 1 (by rfl) ⟨320456, by rfl⟩ : syracuseStep 427275 = 640913) B640913
theorem B427287 : Blo 424774 427287 := bstep (se 1 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 427287 = 640931) B640931
theorem B1443095 : Blo 424774 1443095 := bstep (se 1 (by rfl) ⟨1082321, by rfl⟩ : syracuseStep 1443095 = 2164643) B2164643
theorem B427307 : Blo 424774 427307 := bstep (se 1 (by rfl) ⟨320480, by rfl⟩ : syracuseStep 427307 = 640961) B640961
theorem B427319 : Blo 424774 427319 := bstep (se 1 (by rfl) ⟨320489, by rfl⟩ : syracuseStep 427319 = 640979) B640979
theorem B427339 : Blo 424774 427339 := bstep (se 1 (by rfl) ⟨320504, by rfl⟩ : syracuseStep 427339 = 641009) B641009
theorem B427351 : Blo 424774 427351 := bstep (se 1 (by rfl) ⟨320513, by rfl⟩ : syracuseStep 427351 = 641027) B641027
theorem B722263 : Blo 424774 722263 := bstep (se 1 (by rfl) ⟨541697, by rfl⟩ : syracuseStep 722263 = 1083395) B1083395
theorem B3638621 : Blo 424774 3638621 := bstep (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) B1364483
theorem B427371 : Blo 424774 427371 := bstep (se 1 (by rfl) ⟨320528, by rfl⟩ : syracuseStep 427371 = 641057) B641057
theorem B427383 : Blo 424774 427383 := bstep (se 1 (by rfl) ⟨320537, by rfl⟩ : syracuseStep 427383 = 641075) B641075
theorem B427403 : Blo 424774 427403 := bstep (se 1 (by rfl) ⟨320552, by rfl⟩ : syracuseStep 427403 = 641105) B641105
theorem B427415 : Blo 424774 427415 := bstep (se 1 (by rfl) ⟨320561, by rfl⟩ : syracuseStep 427415 = 641123) B641123
theorem B427435 : Blo 424774 427435 := bstep (se 1 (by rfl) ⟨320576, by rfl⟩ : syracuseStep 427435 = 641153) B641153
theorem B427447 : Blo 424774 427447 := bstep (se 1 (by rfl) ⟨320585, by rfl⟩ : syracuseStep 427447 = 641171) B641171
theorem B427467 : Blo 424774 427467 := bstep (se 1 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 427467 = 641201) B641201
theorem B427479 : Blo 424774 427479 := bstep (se 1 (by rfl) ⟨320609, by rfl⟩ : syracuseStep 427479 = 641219) B641219
theorem B427499 : Blo 424774 427499 := bstep (se 1 (by rfl) ⟨320624, by rfl⟩ : syracuseStep 427499 = 641249) B641249
theorem B427511 : Blo 424774 427511 := bstep (se 1 (by rfl) ⟨320633, by rfl⟩ : syracuseStep 427511 = 641267) B641267
theorem B427531 : Blo 424774 427531 := bstep (se 1 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 427531 = 641297) B641297
theorem B427543 : Blo 424774 427543 := bstep (se 1 (by rfl) ⟨320657, by rfl⟩ : syracuseStep 427543 = 641315) B641315
theorem B427563 : Blo 424774 427563 := bstep (se 1 (by rfl) ⟨320672, by rfl⟩ : syracuseStep 427563 = 641345) B641345
theorem B427575 : Blo 424774 427575 := bstep (se 1 (by rfl) ⟨320681, by rfl⟩ : syracuseStep 427575 = 641363) B641363
theorem B427595 : Blo 424774 427595 := bstep (se 1 (by rfl) ⟨320696, by rfl⟩ : syracuseStep 427595 = 641393) B641393
theorem B427607 : Blo 424774 427607 := bstep (se 1 (by rfl) ⟨320705, by rfl⟩ : syracuseStep 427607 = 641411) B641411
theorem B427627 : Blo 424774 427627 := bstep (se 1 (by rfl) ⟨320720, by rfl⟩ : syracuseStep 427627 = 641441) B641441
theorem B427639 : Blo 424774 427639 := bstep (se 1 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 427639 = 641459) B641459
theorem B427659 : Blo 424774 427659 := bstep (se 1 (by rfl) ⟨320744, by rfl⟩ : syracuseStep 427659 = 641489) B641489
theorem B427671 : Blo 424774 427671 := bstep (se 1 (by rfl) ⟨320753, by rfl⟩ : syracuseStep 427671 = 641507) B641507
theorem B427691 : Blo 424774 427691 := bstep (se 1 (by rfl) ⟨320768, by rfl⟩ : syracuseStep 427691 = 641537) B641537
theorem B427703 : Blo 424774 427703 := bstep (se 1 (by rfl) ⟨320777, by rfl⟩ : syracuseStep 427703 = 641555) B641555
theorem B427723 : Blo 424774 427723 := bstep (se 1 (by rfl) ⟨320792, by rfl⟩ : syracuseStep 427723 = 641585) B641585
theorem B427735 : Blo 424774 427735 := bstep (se 1 (by rfl) ⟨320801, by rfl⟩ : syracuseStep 427735 = 641603) B641603
theorem B427755 : Blo 424774 427755 := bstep (se 1 (by rfl) ⟨320816, by rfl⟩ : syracuseStep 427755 = 641633) B641633
theorem B427767 : Blo 424774 427767 := bstep (se 1 (by rfl) ⟨320825, by rfl⟩ : syracuseStep 427767 = 641651) B641651
theorem B427787 : Blo 424774 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B427799 : Blo 424774 427799 := bstep (se 1 (by rfl) ⟨320849, by rfl⟩ : syracuseStep 427799 = 641699) B641699
theorem B427819 : Blo 424774 427819 := bstep (se 1 (by rfl) ⟨320864, by rfl⟩ : syracuseStep 427819 = 641729) B641729
theorem B1443635 : Blo 424774 1443635 := bstep (se 1 (by rfl) ⟨1082726, by rfl⟩ : syracuseStep 1443635 = 2165453) B2165453
theorem B427831 : Blo 424774 427831 := bstep (se 1 (by rfl) ⟨320873, by rfl⟩ : syracuseStep 427831 = 641747) B641747
theorem B427851 : Blo 424774 427851 := bstep (se 1 (by rfl) ⟨320888, by rfl⟩ : syracuseStep 427851 = 641777) B641777
theorem B427863 : Blo 424774 427863 := bstep (se 1 (by rfl) ⟨320897, by rfl⟩ : syracuseStep 427863 = 641795) B641795
theorem B427883 : Blo 424774 427883 := bstep (se 1 (by rfl) ⟨320912, by rfl⟩ : syracuseStep 427883 = 641825) B641825
theorem B427895 : Blo 424774 427895 := bstep (se 1 (by rfl) ⟨320921, by rfl⟩ : syracuseStep 427895 = 641843) B641843
theorem B427915 : Blo 424774 427915 := bstep (se 1 (by rfl) ⟨320936, by rfl⟩ : syracuseStep 427915 = 641873) B641873
theorem B427927 : Blo 424774 427927 := bstep (se 1 (by rfl) ⟨320945, by rfl⟩ : syracuseStep 427927 = 641891) B641891
theorem B427947 : Blo 424774 427947 := bstep (se 1 (by rfl) ⟨320960, by rfl⟩ : syracuseStep 427947 = 641921) B641921
theorem B427959 : Blo 424774 427959 := bstep (se 1 (by rfl) ⟨320969, by rfl⟩ : syracuseStep 427959 = 641939) B641939
theorem B427979 : Blo 424774 427979 := bstep (se 1 (by rfl) ⟨320984, by rfl⟩ : syracuseStep 427979 = 641969) B641969
theorem B722891 : Blo 424774 722891 := bstep (se 1 (by rfl) ⟨542168, by rfl⟩ : syracuseStep 722891 = 1084337) B1084337
theorem B427991 : Blo 424774 427991 := bstep (se 1 (by rfl) ⟨320993, by rfl⟩ : syracuseStep 427991 = 641987) B641987
theorem B428011 : Blo 424774 428011 := bstep (se 1 (by rfl) ⟨321008, by rfl⟩ : syracuseStep 428011 = 642017) B642017
theorem B428023 : Blo 424774 428023 := bstep (se 1 (by rfl) ⟨321017, by rfl⟩ : syracuseStep 428023 = 642035) B642035
theorem B428043 : Blo 424774 428043 := bstep (se 1 (by rfl) ⟨321032, by rfl⟩ : syracuseStep 428043 = 642065) B642065
theorem B1083415 : Blo 424774 1083415 := bstep (se 1 (by rfl) ⟨812561, by rfl⟩ : syracuseStep 1083415 = 1625123) B1625123
theorem B428055 : Blo 424774 428055 := bstep (se 1 (by rfl) ⟨321041, by rfl⟩ : syracuseStep 428055 = 642083) B642083
theorem B428075 : Blo 424774 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B428087 : Blo 424774 428087 := bstep (se 1 (by rfl) ⟨321065, by rfl⟩ : syracuseStep 428087 = 642131) B642131
theorem B1443905 : Blo 424774 1443905 := bstep (se 2 (by rfl) ⟨541464, by rfl⟩ : syracuseStep 1443905 = 1082929) B1082929
theorem B428107 : Blo 424774 428107 := bstep (se 1 (by rfl) ⟨321080, by rfl⟩ : syracuseStep 428107 = 642161) B642161
theorem B723019 : Blo 424774 723019 := bstep (se 1 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 723019 = 1084529) B1084529
theorem B428119 : Blo 424774 428119 := bstep (se 1 (by rfl) ⟨321089, by rfl⟩ : syracuseStep 428119 = 642179) B642179
theorem B428139 : Blo 424774 428139 := bstep (se 1 (by rfl) ⟨321104, by rfl⟩ : syracuseStep 428139 = 642209) B642209
theorem B428151 : Blo 424774 428151 := bstep (se 1 (by rfl) ⟨321113, by rfl⟩ : syracuseStep 428151 = 642227) B642227
theorem B428171 : Blo 424774 428171 := bstep (se 1 (by rfl) ⟨321128, by rfl⟩ : syracuseStep 428171 = 642257) B642257
theorem B428183 : Blo 424774 428183 := bstep (se 1 (by rfl) ⟨321137, by rfl⟩ : syracuseStep 428183 = 642275) B642275
theorem B428203 : Blo 424774 428203 := bstep (se 1 (by rfl) ⟨321152, by rfl⟩ : syracuseStep 428203 = 642305) B642305
theorem B428215 : Blo 424774 428215 := bstep (se 1 (by rfl) ⟨321161, by rfl⟩ : syracuseStep 428215 = 642323) B642323
theorem B428235 : Blo 424774 428235 := bstep (se 1 (by rfl) ⟨321176, by rfl⟩ : syracuseStep 428235 = 642353) B642353
theorem B428247 : Blo 424774 428247 := bstep (se 1 (by rfl) ⟨321185, by rfl⟩ : syracuseStep 428247 = 642371) B642371
theorem B723161 : Blo 424774 723161 := bstep (se 2 (by rfl) ⟨271185, by rfl⟩ : syracuseStep 723161 = 542371) B542371
theorem B428267 : Blo 424774 428267 := bstep (se 1 (by rfl) ⟨321200, by rfl⟩ : syracuseStep 428267 = 642401) B642401
theorem B428279 : Blo 424774 428279 := bstep (se 1 (by rfl) ⟨321209, by rfl⟩ : syracuseStep 428279 = 642419) B642419
theorem B428299 : Blo 424774 428299 := bstep (se 1 (by rfl) ⟨321224, by rfl⟩ : syracuseStep 428299 = 642449) B642449
theorem B428311 : Blo 424774 428311 := bstep (se 1 (by rfl) ⟨321233, by rfl⟩ : syracuseStep 428311 = 642467) B642467
theorem B428331 : Blo 424774 428331 := bstep (se 1 (by rfl) ⟨321248, by rfl⟩ : syracuseStep 428331 = 642497) B642497
theorem B428343 : Blo 424774 428343 := bstep (se 1 (by rfl) ⟨321257, by rfl⟩ : syracuseStep 428343 = 642515) B642515
theorem B428363 : Blo 424774 428363 := bstep (se 1 (by rfl) ⟨321272, by rfl⟩ : syracuseStep 428363 = 642545) B642545
theorem B428375 : Blo 424774 428375 := bstep (se 1 (by rfl) ⟨321281, by rfl⟩ : syracuseStep 428375 = 642563) B642563
theorem B723289 : Blo 424774 723289 := bstep (se 2 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 723289 = 542467) B542467
theorem B428395 : Blo 424774 428395 := bstep (se 1 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 428395 = 642593) B642593
theorem B428407 : Blo 424774 428407 := bstep (se 1 (by rfl) ⟨321305, by rfl⟩ : syracuseStep 428407 = 642611) B642611
theorem B428427 : Blo 424774 428427 := bstep (se 1 (by rfl) ⟨321320, by rfl⟩ : syracuseStep 428427 = 642641) B642641
theorem B428439 : Blo 424774 428439 := bstep (se 1 (by rfl) ⟨321329, by rfl⟩ : syracuseStep 428439 = 642659) B642659
theorem B428459 : Blo 424774 428459 := bstep (se 1 (by rfl) ⟨321344, by rfl⟩ : syracuseStep 428459 = 642689) B642689
theorem B428471 : Blo 424774 428471 := bstep (se 1 (by rfl) ⟨321353, by rfl⟩ : syracuseStep 428471 = 642707) B642707
theorem B1083851 : Blo 424774 1083851 := bstep (se 1 (by rfl) ⟨812888, by rfl⟩ : syracuseStep 1083851 = 1625777) B1625777
theorem B428491 : Blo 424774 428491 := bstep (se 1 (by rfl) ⟨321368, by rfl⟩ : syracuseStep 428491 = 642737) B642737
theorem B428503 : Blo 424774 428503 := bstep (se 1 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 428503 = 642755) B642755
theorem B428523 : Blo 424774 428523 := bstep (se 1 (by rfl) ⟨321392, by rfl⟩ : syracuseStep 428523 = 642785) B642785
theorem B428535 : Blo 424774 428535 := bstep (se 1 (by rfl) ⟨321401, by rfl⟩ : syracuseStep 428535 = 642803) B642803
theorem B428555 : Blo 424774 428555 := bstep (se 1 (by rfl) ⟨321416, by rfl⟩ : syracuseStep 428555 = 642833) B642833
theorem B428567 : Blo 424774 428567 := bstep (se 1 (by rfl) ⟨321425, by rfl⟩ : syracuseStep 428567 = 642851) B642851
theorem B1018391 : Blo 424774 1018391 := bstep (se 1 (by rfl) ⟨763793, by rfl⟩ : syracuseStep 1018391 = 1527587) B1527587
theorem B428587 : Blo 424774 428587 := bstep (se 1 (by rfl) ⟨321440, by rfl⟩ : syracuseStep 428587 = 642881) B642881
theorem B428599 : Blo 424774 428599 := bstep (se 1 (by rfl) ⟨321449, by rfl⟩ : syracuseStep 428599 = 642899) B642899
theorem B920129 : Blo 424774 920129 := bstep (se 2 (by rfl) ⟨345048, by rfl⟩ : syracuseStep 920129 = 690097) B690097
theorem B428619 : Blo 424774 428619 := bstep (se 1 (by rfl) ⟨321464, by rfl⟩ : syracuseStep 428619 = 642929) B642929
theorem B428631 : Blo 424774 428631 := bstep (se 1 (by rfl) ⟨321473, by rfl⟩ : syracuseStep 428631 = 642947) B642947
theorem B1444445 : Blo 424774 1444445 := bstep (se 3 (by rfl) ⟨270833, by rfl⟩ : syracuseStep 1444445 = 541667) B541667
theorem B2722405 : Blo 424774 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B428651 : Blo 424774 428651 := bstep (se 1 (by rfl) ⟨321488, by rfl⟩ : syracuseStep 428651 = 642977) B642977
theorem B428663 : Blo 424774 428663 := bstep (se 1 (by rfl) ⟨321497, by rfl⟩ : syracuseStep 428663 = 642995) B642995
theorem B428683 : Blo 424774 428683 := bstep (se 1 (by rfl) ⟨321512, by rfl⟩ : syracuseStep 428683 = 643025) B643025
theorem B428695 : Blo 424774 428695 := bstep (se 1 (by rfl) ⟨321521, by rfl⟩ : syracuseStep 428695 = 643043) B643043
theorem B428715 : Blo 424774 428715 := bstep (se 1 (by rfl) ⟨321536, by rfl⟩ : syracuseStep 428715 = 643073) B643073
theorem B428727 : Blo 424774 428727 := bstep (se 1 (by rfl) ⟨321545, by rfl⟩ : syracuseStep 428727 = 643091) B643091
theorem B428747 : Blo 424774 428747 := bstep (se 1 (by rfl) ⟨321560, by rfl⟩ : syracuseStep 428747 = 643121) B643121
theorem B428759 : Blo 424774 428759 := bstep (se 1 (by rfl) ⟨321569, by rfl⟩ : syracuseStep 428759 = 643139) B643139
theorem B1084225 : Blo 424774 1084225 := bstep (se 2 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 1084225 = 813169) B813169
theorem B1215425 : Blo 424774 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B1215449 : Blo 424774 1215449 := bstep (se 2 (by rfl) ⟨455793, by rfl⟩ : syracuseStep 1215449 = 911587) B911587
theorem B2165777 : Blo 424774 2165777 := bstep (se 2 (by rfl) ⟨812166, by rfl⟩ : syracuseStep 2165777 = 1624333) B1624333
theorem B2165939 : Blo 424774 2165939 := bstep (se 1 (by rfl) ⟨1624454, by rfl⟩ : syracuseStep 2165939 = 3248909) B3248909
theorem B1084823 : Blo 424774 1084823 := bstep (se 1 (by rfl) ⟨813617, by rfl⟩ : syracuseStep 1084823 = 1627235) B1627235
theorem B2428481 : Blo 424774 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1642049 : Blo 424774 1642049 := bstep (se 2 (by rfl) ⟨615768, by rfl⟩ : syracuseStep 1642049 = 1231537) B1231537
theorem B11701853 : Blo 424774 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B1445579 : Blo 424774 1445579 := bstep (se 1 (by rfl) ⟨1084184, by rfl⟩ : syracuseStep 1445579 = 2168369) B2168369
theorem B3247937 : Blo 424774 3247937 := bstep (se 2 (by rfl) ⟨1217976, by rfl⟩ : syracuseStep 3247937 = 2435953) B2435953
theorem B3641219 : Blo 424774 3641219 := bstep (se 1 (by rfl) ⟨2730914, by rfl⟩ : syracuseStep 3641219 = 5461829) B5461829
theorem B4853681 : Blo 424774 4853681 := bstep (se 2 (by rfl) ⟨1820130, by rfl⟩ : syracuseStep 4853681 = 3640261) B3640261
theorem B1445849 : Blo 424774 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B3084389 : Blo 424774 3084389 := bstep (se 4 (by rfl) ⟨289161, by rfl⟩ : syracuseStep 3084389 = 578323) B578323
theorem B1216691 : Blo 424774 1216691 := bstep (se 1 (by rfl) ⟨912518, by rfl⟩ : syracuseStep 1216691 = 1825037) B1825037
theorem B4624685 : Blo 424774 4624685 := bstep (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) B1734257
theorem B6165085 : Blo 424774 6165085 := bstep (se 3 (by rfl) ⟨1155953, by rfl⟩ : syracuseStep 6165085 = 2311907) B2311907
theorem B1446551 : Blo 424774 1446551 := bstep (se 1 (by rfl) ⟨1084913, by rfl⟩ : syracuseStep 1446551 = 2169827) B2169827
theorem B823987 : Blo 424774 823987 := bstep (se 1 (by rfl) ⟨617990, by rfl⟩ : syracuseStep 823987 = 1235981) B1235981
theorem B922571 : Blo 424774 922571 := bstep (se 1 (by rfl) ⟨691928, by rfl⟩ : syracuseStep 922571 = 1383857) B1383857
theorem B431083 : Blo 424774 431083 := bstep (se 1 (by rfl) ⟨323312, by rfl⟩ : syracuseStep 431083 = 646625) B646625
theorem B2167883 : Blo 424774 2167883 := bstep (se 1 (by rfl) ⟨1625912, by rfl⟩ : syracuseStep 2167883 = 3251825) B3251825
theorem B1447091 : Blo 424774 1447091 := bstep (se 1 (by rfl) ⟨1085318, by rfl⟩ : syracuseStep 1447091 = 2170637) B2170637
theorem B2692445 : Blo 424774 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B955763 : Blo 424774 955763 := bstep (se 1 (by rfl) ⟨716822, by rfl⟩ : syracuseStep 955763 = 1433645) B1433645
theorem B955799 : Blo 424774 955799 := bstep (se 1 (by rfl) ⟨716849, by rfl⟩ : syracuseStep 955799 = 1433699) B1433699
theorem B955979 : Blo 424774 955979 := bstep (se 1 (by rfl) ⟨716984, by rfl⟩ : syracuseStep 955979 = 1433969) B1433969
theorem B956033 : Blo 424774 956033 := bstep (se 2 (by rfl) ⟨358512, by rfl⟩ : syracuseStep 956033 = 717025) B717025
theorem B3249881 : Blo 424774 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B1382167 : Blo 424774 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B956249 : Blo 424774 956249 := bstep (se 2 (by rfl) ⟨358593, by rfl⟩ : syracuseStep 956249 = 717187) B717187
theorem B956339 : Blo 424774 956339 := bstep (se 1 (by rfl) ⟨717254, by rfl⟩ : syracuseStep 956339 = 1434509) B1434509
theorem B1841075 : Blo 424774 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1152971 : Blo 424774 1152971 := bstep (se 1 (by rfl) ⟨864728, by rfl⟩ : syracuseStep 1152971 = 1729457) B1729457
theorem B3282893 : Blo 424774 3282893 := bstep (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) B1231085
theorem B956375 : Blo 424774 956375 := bstep (se 1 (by rfl) ⟨717281, by rfl⟩ : syracuseStep 956375 = 1434563) B1434563
theorem B956555 : Blo 424774 956555 := bstep (se 1 (by rfl) ⟨717416, by rfl⟩ : syracuseStep 956555 = 1434833) B1434833
theorem B432299 : Blo 424774 432299 := bstep (se 1 (by rfl) ⟨324224, by rfl⟩ : syracuseStep 432299 = 648449) B648449
theorem B956609 : Blo 424774 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B1939801 : Blo 424774 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B956825 : Blo 424774 956825 := bstep (se 2 (by rfl) ⟨358809, by rfl⟩ : syracuseStep 956825 = 717619) B717619
theorem B956915 : Blo 424774 956915 := bstep (se 1 (by rfl) ⟨717686, by rfl⟩ : syracuseStep 956915 = 1435373) B1435373
theorem B956951 : Blo 424774 956951 := bstep (se 1 (by rfl) ⟨717713, by rfl⟩ : syracuseStep 956951 = 1435427) B1435427
theorem B1940057 : Blo 424774 1940057 := bstep (se 2 (by rfl) ⟨727521, by rfl⟩ : syracuseStep 1940057 = 1455043) B1455043
theorem B10394243 : Blo 424774 10394243 := bstep (se 1 (by rfl) ⟨7795682, by rfl⟩ : syracuseStep 10394243 = 15591365) B15591365
theorem B957131 : Blo 424774 957131 := bstep (se 1 (by rfl) ⟨717848, by rfl⟩ : syracuseStep 957131 = 1435697) B1435697
theorem B957185 : Blo 424774 957185 := bstep (se 2 (by rfl) ⟨358944, by rfl⟩ : syracuseStep 957185 = 717889) B717889
theorem B2169665 : Blo 424774 2169665 := bstep (se 2 (by rfl) ⟨813624, by rfl⟩ : syracuseStep 2169665 = 1627249) B1627249
theorem B957401 : Blo 424774 957401 := bstep (se 2 (by rfl) ⟨359025, by rfl⟩ : syracuseStep 957401 = 718051) B718051
theorem B1219549 : Blo 424774 1219549 := bstep (se 3 (by rfl) ⟨228665, by rfl⟩ : syracuseStep 1219549 = 457331) B457331
theorem B1219607 : Blo 424774 1219607 := bstep (se 1 (by rfl) ⟨914705, by rfl⟩ : syracuseStep 1219607 = 1829411) B1829411
theorem B957491 : Blo 424774 957491 := bstep (se 1 (by rfl) ⟨718118, by rfl⟩ : syracuseStep 957491 = 1436237) B1436237
theorem B957527 : Blo 424774 957527 := bstep (se 1 (by rfl) ⟨718145, by rfl⟩ : syracuseStep 957527 = 1436291) B1436291
theorem B1612973 : Blo 424774 1612973 := bstep (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) B604865
theorem B695513 : Blo 424774 695513 := bstep (se 2 (by rfl) ⟨260817, by rfl⟩ : syracuseStep 695513 = 521635) B521635
theorem B957707 : Blo 424774 957707 := bstep (se 1 (by rfl) ⟨718280, by rfl⟩ : syracuseStep 957707 = 1436561) B1436561
theorem B2759953 : Blo 424774 2759953 := bstep (se 2 (by rfl) ⟨1034982, by rfl⟩ : syracuseStep 2759953 = 2069965) B2069965
theorem B957761 : Blo 424774 957761 := bstep (se 2 (by rfl) ⟨359160, by rfl⟩ : syracuseStep 957761 = 718321) B718321
theorem B957977 : Blo 424774 957977 := bstep (se 2 (by rfl) ⟨359241, by rfl⟩ : syracuseStep 957977 = 718483) B718483
theorem B958067 : Blo 424774 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B958103 : Blo 424774 958103 := bstep (se 1 (by rfl) ⟨718577, by rfl⟩ : syracuseStep 958103 = 1437155) B1437155
theorem B1023691 : Blo 424774 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B1023767 : Blo 424774 1023767 := bstep (se 1 (by rfl) ⟨767825, by rfl⟩ : syracuseStep 1023767 = 1535651) B1535651
theorem B958283 : Blo 424774 958283 := bstep (se 1 (by rfl) ⟨718712, by rfl⟩ : syracuseStep 958283 = 1437425) B1437425
theorem B958337 : Blo 424774 958337 := bstep (se 2 (by rfl) ⟨359376, by rfl⟩ : syracuseStep 958337 = 718753) B718753
theorem B958553 : Blo 424774 958553 := bstep (se 2 (by rfl) ⟨359457, by rfl⟩ : syracuseStep 958553 = 718915) B718915
theorem B958643 : Blo 424774 958643 := bstep (se 1 (by rfl) ⟨718982, by rfl⟩ : syracuseStep 958643 = 1437965) B1437965
theorem B958679 : Blo 424774 958679 := bstep (se 1 (by rfl) ⟨719009, by rfl⟩ : syracuseStep 958679 = 1438019) B1438019
theorem B1220825 : Blo 424774 1220825 := bstep (se 2 (by rfl) ⟨457809, by rfl⟩ : syracuseStep 1220825 = 915619) B915619
theorem B1220939 : Blo 424774 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B958859 : Blo 424774 958859 := bstep (se 1 (by rfl) ⟨719144, by rfl⟩ : syracuseStep 958859 = 1438289) B1438289
theorem B958913 : Blo 424774 958913 := bstep (se 2 (by rfl) ⟨359592, by rfl⟩ : syracuseStep 958913 = 719185) B719185
theorem B1614401 : Blo 424774 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B729751 : Blo 424774 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B959129 : Blo 424774 959129 := bstep (se 2 (by rfl) ⟨359673, by rfl⟩ : syracuseStep 959129 = 719347) B719347
theorem B959219 : Blo 424774 959219 := bstep (se 1 (by rfl) ⟨719414, by rfl⟩ : syracuseStep 959219 = 1438829) B1438829
theorem B959255 : Blo 424774 959255 := bstep (se 1 (by rfl) ⟨719441, by rfl⟩ : syracuseStep 959255 = 1438883) B1438883
theorem B959435 : Blo 424774 959435 := bstep (se 1 (by rfl) ⟨719576, by rfl⟩ : syracuseStep 959435 = 1439153) B1439153
theorem B959489 : Blo 424774 959489 := bstep (se 2 (by rfl) ⟨359808, by rfl⟩ : syracuseStep 959489 = 719617) B719617
theorem B1385495 : Blo 424774 1385495 := bstep (se 1 (by rfl) ⟨1039121, by rfl⟩ : syracuseStep 1385495 = 2078243) B2078243
theorem B861209 : Blo 424774 861209 := bstep (se 2 (by rfl) ⟨322953, by rfl⟩ : syracuseStep 861209 = 645907) B645907
theorem B3253283 : Blo 424774 3253283 := bstep (se 1 (by rfl) ⟨2439962, by rfl⟩ : syracuseStep 3253283 = 4879925) B4879925
theorem B959705 : Blo 424774 959705 := bstep (se 2 (by rfl) ⟨359889, by rfl⟩ : syracuseStep 959705 = 719779) B719779
theorem B959795 : Blo 424774 959795 := bstep (se 1 (by rfl) ⟨719846, by rfl⟩ : syracuseStep 959795 = 1439693) B1439693
theorem B959831 : Blo 424774 959831 := bstep (se 1 (by rfl) ⟨719873, by rfl⟩ : syracuseStep 959831 = 1439747) B1439747
theorem B960011 : Blo 424774 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B1975853 : Blo 424774 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B960065 : Blo 424774 960065 := bstep (se 2 (by rfl) ⟨360024, by rfl⟩ : syracuseStep 960065 = 720049) B720049
theorem B829145 : Blo 424774 829145 := bstep (se 2 (by rfl) ⟨310929, by rfl⟩ : syracuseStep 829145 = 621859) B621859
theorem B960281 : Blo 424774 960281 := bstep (se 2 (by rfl) ⟨360105, by rfl⟩ : syracuseStep 960281 = 720211) B720211
theorem B862003 : Blo 424774 862003 := bstep (se 1 (by rfl) ⟨646502, by rfl⟩ : syracuseStep 862003 = 1293005) B1293005
theorem B960371 : Blo 424774 960371 := bstep (se 1 (by rfl) ⟨720278, by rfl⟩ : syracuseStep 960371 = 1440557) B1440557
theorem B960407 : Blo 424774 960407 := bstep (se 1 (by rfl) ⟨720305, by rfl⟩ : syracuseStep 960407 = 1440611) B1440611
theorem B1615889 : Blo 424774 1615889 := bstep (se 2 (by rfl) ⟨605958, by rfl⟩ : syracuseStep 1615889 = 1211917) B1211917
theorem B6924305 : Blo 424774 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B960587 : Blo 424774 960587 := bstep (se 1 (by rfl) ⟨720440, by rfl⟩ : syracuseStep 960587 = 1440881) B1440881
theorem B960641 : Blo 424774 960641 := bstep (se 2 (by rfl) ⟨360240, by rfl⟩ : syracuseStep 960641 = 720481) B720481
theorem B1026199 : Blo 424774 1026199 := bstep (se 1 (by rfl) ⟨769649, by rfl⟩ : syracuseStep 1026199 = 1539299) B1539299
theorem B1026227 : Blo 424774 1026227 := bstep (se 1 (by rfl) ⟨769670, by rfl⟩ : syracuseStep 1026227 = 1539341) B1539341
theorem B960857 : Blo 424774 960857 := bstep (se 2 (by rfl) ⟨360321, by rfl⟩ : syracuseStep 960857 = 720643) B720643
theorem B6596963 : Blo 424774 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B960947 : Blo 424774 960947 := bstep (se 1 (by rfl) ⟨720710, by rfl⟩ : syracuseStep 960947 = 1441421) B1441421
theorem B960983 : Blo 424774 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B1616345 : Blo 424774 1616345 := bstep (se 2 (by rfl) ⟨606129, by rfl⟩ : syracuseStep 1616345 = 1212259) B1212259
theorem B16198157 : Blo 424774 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B961163 : Blo 424774 961163 := bstep (se 1 (by rfl) ⟨720872, by rfl⟩ : syracuseStep 961163 = 1441745) B1441745
theorem B1616557 : Blo 424774 1616557 := bstep (se 3 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 1616557 = 606209) B606209
theorem B961217 : Blo 424774 961217 := bstep (se 2 (by rfl) ⟨360456, by rfl⟩ : syracuseStep 961217 = 720913) B720913
theorem B961433 : Blo 424774 961433 := bstep (se 2 (by rfl) ⟨360537, by rfl⟩ : syracuseStep 961433 = 721075) B721075
theorem B1616861 : Blo 424774 1616861 := bstep (se 3 (by rfl) ⟨303161, by rfl⟩ : syracuseStep 1616861 = 606323) B606323
theorem B961523 : Blo 424774 961523 := bstep (se 1 (by rfl) ⟨721142, by rfl⟩ : syracuseStep 961523 = 1442285) B1442285
theorem B961559 : Blo 424774 961559 := bstep (se 1 (by rfl) ⟨721169, by rfl⟩ : syracuseStep 961559 = 1442339) B1442339
theorem B2436227 : Blo 424774 2436227 := bstep (se 1 (by rfl) ⟨1827170, by rfl⟩ : syracuseStep 2436227 = 3654341) B3654341
theorem B961739 : Blo 424774 961739 := bstep (se 1 (by rfl) ⟨721304, by rfl⟩ : syracuseStep 961739 = 1442609) B1442609
theorem B961793 : Blo 424774 961793 := bstep (se 2 (by rfl) ⟨360672, by rfl⟩ : syracuseStep 961793 = 721345) B721345
theorem B3452165 : Blo 424774 3452165 := bstep (se 4 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 3452165 = 647281) B647281
theorem B437687 : Blo 424774 437687 := bstep (se 1 (by rfl) ⟨328265, by rfl⟩ : syracuseStep 437687 = 656531) B656531
theorem B2731481 : Blo 424774 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B962009 : Blo 424774 962009 := bstep (se 2 (by rfl) ⟨360753, by rfl⟩ : syracuseStep 962009 = 721507) B721507
theorem B962099 : Blo 424774 962099 := bstep (se 1 (by rfl) ⟨721574, by rfl⟩ : syracuseStep 962099 = 1443149) B1443149
theorem B962135 : Blo 424774 962135 := bstep (se 1 (by rfl) ⟨721601, by rfl⟩ : syracuseStep 962135 = 1443203) B1443203
theorem B962315 : Blo 424774 962315 := bstep (se 1 (by rfl) ⟨721736, by rfl⟩ : syracuseStep 962315 = 1443473) B1443473
theorem B962369 : Blo 424774 962369 := bstep (se 2 (by rfl) ⟨360888, by rfl⟩ : syracuseStep 962369 = 721777) B721777
theorem B3518309 : Blo 424774 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B13840307 : Blo 424774 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B962585 : Blo 424774 962585 := bstep (se 2 (by rfl) ⟨360969, by rfl⟩ : syracuseStep 962585 = 721939) B721939
theorem B10956869 : Blo 424774 10956869 := bstep (se 4 (by rfl) ⟨1027206, by rfl⟩ : syracuseStep 10956869 = 2054413) B2054413
theorem B962675 : Blo 424774 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B962711 : Blo 424774 962711 := bstep (se 1 (by rfl) ⟨722033, by rfl⟩ : syracuseStep 962711 = 1444067) B1444067
theorem B962891 : Blo 424774 962891 := bstep (se 1 (by rfl) ⟨722168, by rfl⟩ : syracuseStep 962891 = 1444337) B1444337
theorem B962945 : Blo 424774 962945 := bstep (se 2 (by rfl) ⟨361104, by rfl⟩ : syracuseStep 962945 = 722209) B722209
theorem B1094219 : Blo 424774 1094219 := bstep (se 1 (by rfl) ⟨820664, by rfl⟩ : syracuseStep 1094219 = 1641329) B1641329
theorem B963161 : Blo 424774 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B963251 : Blo 424774 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B963287 : Blo 424774 963287 := bstep (se 1 (by rfl) ⟨722465, by rfl⟩ : syracuseStep 963287 = 1444931) B1444931
theorem B1815347 : Blo 424774 1815347 := bstep (se 1 (by rfl) ⟨1361510, by rfl⟩ : syracuseStep 1815347 = 2723021) B2723021
theorem B963467 : Blo 424774 963467 := bstep (se 1 (by rfl) ⟨722600, by rfl⟩ : syracuseStep 963467 = 1445201) B1445201
theorem B2110387 : Blo 424774 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B963521 : Blo 424774 963521 := bstep (se 2 (by rfl) ⟨361320, by rfl⟩ : syracuseStep 963521 = 722641) B722641
theorem B4174865 : Blo 424774 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B963737 : Blo 424774 963737 := bstep (se 2 (by rfl) ⟨361401, by rfl⟩ : syracuseStep 963737 = 722803) B722803
theorem B963827 : Blo 424774 963827 := bstep (se 1 (by rfl) ⟨722870, by rfl⟩ : syracuseStep 963827 = 1445741) B1445741
theorem B963863 : Blo 424774 963863 := bstep (se 1 (by rfl) ⟨722897, by rfl⟩ : syracuseStep 963863 = 1445795) B1445795
theorem B537931 : Blo 424774 537931 := bstep (se 1 (by rfl) ⟨403448, by rfl⟩ : syracuseStep 537931 = 806897) B806897
theorem B3650993 : Blo 424774 3650993 := bstep (se 2 (by rfl) ⟨1369122, by rfl⟩ : syracuseStep 3650993 = 2738245) B2738245
theorem B964043 : Blo 424774 964043 := bstep (se 1 (by rfl) ⟨723032, by rfl⟩ : syracuseStep 964043 = 1446065) B1446065
theorem B964097 : Blo 424774 964097 := bstep (se 2 (by rfl) ⟨361536, by rfl⟩ : syracuseStep 964097 = 723073) B723073
theorem B1619459 : Blo 424774 1619459 := bstep (se 1 (by rfl) ⟨1214594, by rfl⟩ : syracuseStep 1619459 = 2429189) B2429189
theorem B1619473 : Blo 424774 1619473 := bstep (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) B1214605
theorem B964313 : Blo 424774 964313 := bstep (se 2 (by rfl) ⟨361617, by rfl⟩ : syracuseStep 964313 = 723235) B723235
theorem B964403 : Blo 424774 964403 := bstep (se 1 (by rfl) ⟨723302, by rfl⟩ : syracuseStep 964403 = 1446605) B1446605
theorem B1619777 : Blo 424774 1619777 := bstep (se 2 (by rfl) ⟨607416, by rfl⟩ : syracuseStep 1619777 = 1214833) B1214833
theorem B964439 : Blo 424774 964439 := bstep (se 1 (by rfl) ⟨723329, by rfl⟩ : syracuseStep 964439 = 1446659) B1446659
theorem B3880909 : Blo 424774 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B964619 : Blo 424774 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B2734145 : Blo 424774 2734145 := bstep (se 2 (by rfl) ⟨1025304, by rfl⟩ : syracuseStep 2734145 = 2050609) B2050609
theorem B964673 : Blo 424774 964673 := bstep (se 2 (by rfl) ⟨361752, by rfl⟩ : syracuseStep 964673 = 723505) B723505
theorem B538903 : Blo 424774 538903 := bstep (se 1 (by rfl) ⟨404177, by rfl⟩ : syracuseStep 538903 = 808355) B808355
theorem B637259 : Blo 424774 637259 := bstep (se 1 (by rfl) ⟨477944, by rfl⟩ : syracuseStep 637259 = 955889) B955889
theorem B637271 : Blo 424774 637271 := bstep (se 1 (by rfl) ⟨477953, by rfl⟩ : syracuseStep 637271 = 955907) B955907
theorem B866675 : Blo 424774 866675 := bstep (se 1 (by rfl) ⟨650006, by rfl⟩ : syracuseStep 866675 = 1300013) B1300013
theorem B637337 : Blo 424774 637337 := bstep (se 2 (by rfl) ⟨239001, by rfl⟩ : syracuseStep 637337 = 478003) B478003
theorem B1292761 : Blo 424774 1292761 := bstep (se 2 (by rfl) ⟨484785, by rfl⟩ : syracuseStep 1292761 = 969571) B969571
theorem B1620445 : Blo 424774 1620445 := bstep (se 3 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 1620445 = 607667) B607667
theorem B637451 : Blo 424774 637451 := bstep (se 1 (by rfl) ⟨478088, by rfl⟩ : syracuseStep 637451 = 956177) B956177
theorem B637463 : Blo 424774 637463 := bstep (se 1 (by rfl) ⟨478097, by rfl⟩ : syracuseStep 637463 = 956195) B956195
theorem B637529 : Blo 424774 637529 := bstep (se 2 (by rfl) ⟨239073, by rfl⟩ : syracuseStep 637529 = 478147) B478147
theorem B6896279 : Blo 424774 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1817261 : Blo 424774 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B637643 : Blo 424774 637643 := bstep (se 1 (by rfl) ⟨478232, by rfl⟩ : syracuseStep 637643 = 956465) B956465
theorem B637655 : Blo 424774 637655 := bstep (se 1 (by rfl) ⟨478241, by rfl⟩ : syracuseStep 637655 = 956483) B956483
theorem B768727 : Blo 424774 768727 := bstep (se 1 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 768727 = 1153091) B1153091
theorem B637721 : Blo 424774 637721 := bstep (se 2 (by rfl) ⟨239145, by rfl⟩ : syracuseStep 637721 = 478291) B478291
theorem B1260353 : Blo 424774 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B637835 : Blo 424774 637835 := bstep (se 1 (by rfl) ⟨478376, by rfl⟩ : syracuseStep 637835 = 956753) B956753
theorem B637847 : Blo 424774 637847 := bstep (se 1 (by rfl) ⟨478385, by rfl⟩ : syracuseStep 637847 = 956771) B956771
theorem B637913 : Blo 424774 637913 := bstep (se 2 (by rfl) ⟨239217, by rfl⟩ : syracuseStep 637913 = 478435) B478435
theorem B1817603 : Blo 424774 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B638027 : Blo 424774 638027 := bstep (se 1 (by rfl) ⟨478520, by rfl⟩ : syracuseStep 638027 = 957041) B957041
theorem B539723 : Blo 424774 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B638039 : Blo 424774 638039 := bstep (se 1 (by rfl) ⟨478529, by rfl⟩ : syracuseStep 638039 = 957059) B957059
theorem B638105 : Blo 424774 638105 := bstep (se 2 (by rfl) ⟨239289, by rfl⟩ : syracuseStep 638105 = 478579) B478579
theorem B638219 : Blo 424774 638219 := bstep (se 1 (by rfl) ⟨478664, by rfl⟩ : syracuseStep 638219 = 957329) B957329
theorem B638231 : Blo 424774 638231 := bstep (se 1 (by rfl) ⟨478673, by rfl⟩ : syracuseStep 638231 = 957347) B957347
theorem B4865345 : Blo 424774 4865345 := bstep (se 2 (by rfl) ⟨1824504, by rfl⟩ : syracuseStep 4865345 = 3649009) B3649009
theorem B638297 : Blo 424774 638297 := bstep (se 2 (by rfl) ⟨239361, by rfl⟩ : syracuseStep 638297 = 478723) B478723
theorem B638411 : Blo 424774 638411 := bstep (se 1 (by rfl) ⟨478808, by rfl⟩ : syracuseStep 638411 = 957617) B957617
theorem B638423 : Blo 424774 638423 := bstep (se 1 (by rfl) ⟨478817, by rfl⟩ : syracuseStep 638423 = 957635) B957635
theorem B605657 : Blo 424774 605657 := bstep (se 2 (by rfl) ⟨227121, by rfl⟩ : syracuseStep 605657 = 454243) B454243
theorem B12271121 : Blo 424774 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B638489 : Blo 424774 638489 := bstep (se 2 (by rfl) ⟨239433, by rfl⟩ : syracuseStep 638489 = 478867) B478867
theorem B638603 : Blo 424774 638603 := bstep (se 1 (by rfl) ⟨478952, by rfl⟩ : syracuseStep 638603 = 957905) B957905
theorem B638615 : Blo 424774 638615 := bstep (se 1 (by rfl) ⟨478961, by rfl⟩ : syracuseStep 638615 = 957923) B957923
theorem B638681 : Blo 424774 638681 := bstep (se 2 (by rfl) ⟨239505, by rfl⟩ : syracuseStep 638681 = 479011) B479011
theorem B1621721 : Blo 424774 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B540427 : Blo 424774 540427 := bstep (se 1 (by rfl) ⟨405320, by rfl⟩ : syracuseStep 540427 = 810641) B810641
theorem B638795 : Blo 424774 638795 := bstep (se 1 (by rfl) ⟨479096, by rfl⟩ : syracuseStep 638795 = 958193) B958193
theorem B638807 : Blo 424774 638807 := bstep (se 1 (by rfl) ⟨479105, by rfl⟩ : syracuseStep 638807 = 958211) B958211
theorem B638873 : Blo 424774 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B638987 : Blo 424774 638987 := bstep (se 1 (by rfl) ⟨479240, by rfl⟩ : syracuseStep 638987 = 958481) B958481
theorem B638999 : Blo 424774 638999 := bstep (se 1 (by rfl) ⟨479249, by rfl⟩ : syracuseStep 638999 = 958499) B958499
theorem B540695 : Blo 424774 540695 := bstep (se 1 (by rfl) ⟨405521, by rfl⟩ : syracuseStep 540695 = 811043) B811043
theorem B606295 : Blo 424774 606295 := bstep (se 1 (by rfl) ⟨454721, by rfl⟩ : syracuseStep 606295 = 909443) B909443
theorem B639065 : Blo 424774 639065 := bstep (se 2 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 639065 = 479299) B479299
theorem B639179 : Blo 424774 639179 := bstep (se 1 (by rfl) ⟨479384, by rfl⟩ : syracuseStep 639179 = 958769) B958769
theorem B639191 : Blo 424774 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B639257 : Blo 424774 639257 := bstep (se 2 (by rfl) ⟨239721, by rfl⟩ : syracuseStep 639257 = 479443) B479443
theorem B2441603 : Blo 424774 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B639371 : Blo 424774 639371 := bstep (se 1 (by rfl) ⟨479528, by rfl⟩ : syracuseStep 639371 = 959057) B959057
theorem B639383 : Blo 424774 639383 := bstep (se 1 (by rfl) ⟨479537, by rfl⟩ : syracuseStep 639383 = 959075) B959075
theorem B639449 : Blo 424774 639449 := bstep (se 2 (by rfl) ⟨239793, by rfl⟩ : syracuseStep 639449 = 479587) B479587
theorem B639563 : Blo 424774 639563 := bstep (se 1 (by rfl) ⟨479672, by rfl⟩ : syracuseStep 639563 = 959345) B959345
theorem B639575 : Blo 424774 639575 := bstep (se 1 (by rfl) ⟨479681, by rfl⟩ : syracuseStep 639575 = 959363) B959363
theorem B639641 : Blo 424774 639641 := bstep (se 2 (by rfl) ⟨239865, by rfl⟩ : syracuseStep 639641 = 479731) B479731
theorem B541399 : Blo 424774 541399 := bstep (se 1 (by rfl) ⟨406049, by rfl⟩ : syracuseStep 541399 = 812099) B812099
theorem B639755 : Blo 424774 639755 := bstep (se 1 (by rfl) ⟨479816, by rfl⟩ : syracuseStep 639755 = 959633) B959633
theorem B1557265 : Blo 424774 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B639767 : Blo 424774 639767 := bstep (se 1 (by rfl) ⟨479825, by rfl⟩ : syracuseStep 639767 = 959651) B959651
theorem B13812545 : Blo 424774 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B1000279 : Blo 424774 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B639833 : Blo 424774 639833 := bstep (se 2 (by rfl) ⟨239937, by rfl⟩ : syracuseStep 639833 = 479875) B479875
theorem B607115 : Blo 424774 607115 := bstep (se 1 (by rfl) ⟨455336, by rfl⟩ : syracuseStep 607115 = 910673) B910673
theorem B2311091 : Blo 424774 2311091 := bstep (se 1 (by rfl) ⟨1733318, by rfl⟩ : syracuseStep 2311091 = 3466637) B3466637
theorem B639947 : Blo 424774 639947 := bstep (se 1 (by rfl) ⟨479960, by rfl⟩ : syracuseStep 639947 = 959921) B959921
theorem B639959 : Blo 424774 639959 := bstep (se 1 (by rfl) ⟨479969, by rfl⟩ : syracuseStep 639959 = 959939) B959939
theorem B640025 : Blo 424774 640025 := bstep (se 2 (by rfl) ⟨240009, by rfl⟩ : syracuseStep 640025 = 480019) B480019
theorem B640139 : Blo 424774 640139 := bstep (se 1 (by rfl) ⟨480104, by rfl⟩ : syracuseStep 640139 = 960209) B960209
theorem B640151 : Blo 424774 640151 := bstep (se 1 (by rfl) ⟨480113, by rfl⟩ : syracuseStep 640151 = 960227) B960227
theorem B640217 : Blo 424774 640217 := bstep (se 2 (by rfl) ⟨240081, by rfl⟩ : syracuseStep 640217 = 480163) B480163
theorem B1623347 : Blo 424774 1623347 := bstep (se 1 (by rfl) ⟨1217510, by rfl⟩ : syracuseStep 1623347 = 2435021) B2435021
theorem B1623361 : Blo 424774 1623361 := bstep (se 2 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 1623361 = 1217521) B1217521
theorem B1819979 : Blo 424774 1819979 := bstep (se 1 (by rfl) ⟨1364984, by rfl⟩ : syracuseStep 1819979 = 2729969) B2729969
theorem B640331 : Blo 424774 640331 := bstep (se 1 (by rfl) ⟨480248, by rfl⟩ : syracuseStep 640331 = 960497) B960497
theorem B640343 : Blo 424774 640343 := bstep (se 1 (by rfl) ⟨480257, by rfl⟩ : syracuseStep 640343 = 960515) B960515
theorem B640409 : Blo 424774 640409 := bstep (se 2 (by rfl) ⟨240153, by rfl⟩ : syracuseStep 640409 = 480307) B480307
theorem B640523 : Blo 424774 640523 := bstep (se 1 (by rfl) ⟨480392, by rfl⟩ : syracuseStep 640523 = 960785) B960785
theorem B640535 : Blo 424774 640535 := bstep (se 1 (by rfl) ⟨480401, by rfl⟩ : syracuseStep 640535 = 960803) B960803
theorem B3688001 : Blo 424774 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B640601 : Blo 424774 640601 := bstep (se 2 (by rfl) ⟨240225, by rfl⟩ : syracuseStep 640601 = 480451) B480451
theorem B640715 : Blo 424774 640715 := bstep (se 1 (by rfl) ⟨480536, by rfl⟩ : syracuseStep 640715 = 961073) B961073
theorem B640727 : Blo 424774 640727 := bstep (se 1 (by rfl) ⟨480545, by rfl⟩ : syracuseStep 640727 = 961091) B961091
theorem B640793 : Blo 424774 640793 := bstep (se 2 (by rfl) ⟨240297, by rfl⟩ : syracuseStep 640793 = 480595) B480595
theorem B771905 : Blo 424774 771905 := bstep (se 2 (by rfl) ⟨289464, by rfl⟩ : syracuseStep 771905 = 578929) B578929
theorem B608089 : Blo 424774 608089 := bstep (se 2 (by rfl) ⟨228033, by rfl⟩ : syracuseStep 608089 = 456067) B456067
theorem B640907 : Blo 424774 640907 := bstep (se 1 (by rfl) ⟨480680, by rfl⟩ : syracuseStep 640907 = 961361) B961361
theorem B640919 : Blo 424774 640919 := bstep (se 1 (by rfl) ⟨480689, by rfl⟩ : syracuseStep 640919 = 961379) B961379
theorem B4376537 : Blo 424774 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B640985 : Blo 424774 640985 := bstep (se 2 (by rfl) ⟨240369, by rfl⟩ : syracuseStep 640985 = 480739) B480739
theorem B6670349 : Blo 424774 6670349 := bstep (se 3 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 6670349 = 2501381) B2501381
theorem B641099 : Blo 424774 641099 := bstep (se 1 (by rfl) ⟨480824, by rfl⟩ : syracuseStep 641099 = 961649) B961649
theorem B641111 : Blo 424774 641111 := bstep (se 1 (by rfl) ⟨480833, by rfl⟩ : syracuseStep 641111 = 961667) B961667
theorem B641177 : Blo 424774 641177 := bstep (se 2 (by rfl) ⟨240441, by rfl⟩ : syracuseStep 641177 = 480883) B480883
theorem B1099955 : Blo 424774 1099955 := bstep (se 1 (by rfl) ⟨824966, by rfl⟩ : syracuseStep 1099955 = 1649933) B1649933
theorem B4114637 : Blo 424774 4114637 := bstep (se 3 (by rfl) ⟨771494, by rfl⟩ : syracuseStep 4114637 = 1542989) B1542989
theorem B641291 : Blo 424774 641291 := bstep (se 1 (by rfl) ⟨480968, by rfl⟩ : syracuseStep 641291 = 961937) B961937
theorem B1820951 : Blo 424774 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B641303 : Blo 424774 641303 := bstep (se 1 (by rfl) ⟨480977, by rfl⟩ : syracuseStep 641303 = 961955) B961955
theorem B641369 : Blo 424774 641369 := bstep (se 2 (by rfl) ⟨240513, by rfl⟩ : syracuseStep 641369 = 481027) B481027
theorem B772481 : Blo 424774 772481 := bstep (se 2 (by rfl) ⟨289680, by rfl⟩ : syracuseStep 772481 = 579361) B579361
theorem B2312599 : Blo 424774 2312599 := bstep (se 1 (by rfl) ⟨1734449, by rfl⟩ : syracuseStep 2312599 = 3468899) B3468899
theorem B641483 : Blo 424774 641483 := bstep (se 1 (by rfl) ⟨481112, by rfl⟩ : syracuseStep 641483 = 962225) B962225
theorem B641495 : Blo 424774 641495 := bstep (se 1 (by rfl) ⟨481121, by rfl⟩ : syracuseStep 641495 = 962243) B962243
theorem B641561 : Blo 424774 641561 := bstep (se 2 (by rfl) ⟨240585, by rfl⟩ : syracuseStep 641561 = 481171) B481171
theorem B641675 : Blo 424774 641675 := bstep (se 1 (by rfl) ⟨481256, by rfl⟩ : syracuseStep 641675 = 962513) B962513
theorem B641687 : Blo 424774 641687 := bstep (se 1 (by rfl) ⟨481265, by rfl⟩ : syracuseStep 641687 = 962531) B962531
theorem B641753 : Blo 424774 641753 := bstep (se 2 (by rfl) ⟨240657, by rfl⟩ : syracuseStep 641753 = 481315) B481315
theorem B477931 : Blo 424774 477931 := bstep (se 1 (by rfl) ⟨358448, by rfl⟩ : syracuseStep 477931 = 716897) B716897
theorem B641867 : Blo 424774 641867 := bstep (se 1 (by rfl) ⟨481400, by rfl⟩ : syracuseStep 641867 = 962801) B962801
theorem B478039 : Blo 424774 478039 := bstep (se 1 (by rfl) ⟨358529, by rfl⟩ : syracuseStep 478039 = 717059) B717059
theorem B641879 : Blo 424774 641879 := bstep (se 1 (by rfl) ⟨481409, by rfl⟩ : syracuseStep 641879 = 962819) B962819
theorem B641945 : Blo 424774 641945 := bstep (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) B481459
theorem B609239 : Blo 424774 609239 := bstep (se 1 (by rfl) ⟨456929, by rfl⟩ : syracuseStep 609239 = 913859) B913859
theorem B478219 : Blo 424774 478219 := bstep (se 1 (by rfl) ⟨358664, by rfl⟩ : syracuseStep 478219 = 717329) B717329
theorem B642059 : Blo 424774 642059 := bstep (se 1 (by rfl) ⟨481544, by rfl⟩ : syracuseStep 642059 = 963089) B963089
theorem B642071 : Blo 424774 642071 := bstep (se 1 (by rfl) ⟨481553, by rfl⟩ : syracuseStep 642071 = 963107) B963107
theorem B642137 : Blo 424774 642137 := bstep (se 2 (by rfl) ⟨240801, by rfl⟩ : syracuseStep 642137 = 481603) B481603
theorem B478327 : Blo 424774 478327 := bstep (se 1 (by rfl) ⟨358745, by rfl⟩ : syracuseStep 478327 = 717491) B717491
theorem B1625291 : Blo 424774 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B642251 : Blo 424774 642251 := bstep (se 1 (by rfl) ⟨481688, by rfl⟩ : syracuseStep 642251 = 963377) B963377
theorem B642263 : Blo 424774 642263 := bstep (se 1 (by rfl) ⟨481697, by rfl⟩ : syracuseStep 642263 = 963395) B963395
theorem B1625305 : Blo 424774 1625305 := bstep (se 2 (by rfl) ⟨609489, by rfl⟩ : syracuseStep 1625305 = 1218979) B1218979
theorem B609547 : Blo 424774 609547 := bstep (se 1 (by rfl) ⟨457160, by rfl⟩ : syracuseStep 609547 = 914321) B914321
theorem B642329 : Blo 424774 642329 := bstep (se 2 (by rfl) ⟨240873, by rfl⟩ : syracuseStep 642329 = 481747) B481747
theorem B478507 : Blo 424774 478507 := bstep (se 1 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 478507 = 717761) B717761
theorem B642443 : Blo 424774 642443 := bstep (se 1 (by rfl) ⟨481832, by rfl⟩ : syracuseStep 642443 = 963665) B963665
theorem B478615 : Blo 424774 478615 := bstep (se 1 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 478615 = 717923) B717923
theorem B642455 : Blo 424774 642455 := bstep (se 1 (by rfl) ⟨481841, by rfl⟩ : syracuseStep 642455 = 963683) B963683
theorem B511447 : Blo 424774 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B576983 : Blo 424774 576983 := bstep (se 1 (by rfl) ⟨432737, by rfl⟩ : syracuseStep 576983 = 865475) B865475
theorem B642521 : Blo 424774 642521 := bstep (se 2 (by rfl) ⟨240945, by rfl⟩ : syracuseStep 642521 = 481891) B481891
theorem B806411 : Blo 424774 806411 := bstep (se 1 (by rfl) ⟨604808, by rfl⟩ : syracuseStep 806411 = 1209617) B1209617
theorem B478795 : Blo 424774 478795 := bstep (se 1 (by rfl) ⟨359096, by rfl⟩ : syracuseStep 478795 = 718193) B718193
theorem B642635 : Blo 424774 642635 := bstep (se 1 (by rfl) ⟨481976, by rfl⟩ : syracuseStep 642635 = 963953) B963953
theorem B642647 : Blo 424774 642647 := bstep (se 1 (by rfl) ⟨481985, by rfl⟩ : syracuseStep 642647 = 963971) B963971
theorem B1363549 : Blo 424774 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B642713 : Blo 424774 642713 := bstep (se 2 (by rfl) ⟨241017, by rfl⟩ : syracuseStep 642713 = 482035) B482035
theorem B1232563 : Blo 424774 1232563 := bstep (se 1 (by rfl) ⟨924422, by rfl⟩ : syracuseStep 1232563 = 1848845) B1848845
theorem B478903 : Blo 424774 478903 := bstep (se 1 (by rfl) ⟨359177, by rfl⟩ : syracuseStep 478903 = 718355) B718355
theorem B806593 : Blo 424774 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B2051801 : Blo 424774 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B642827 : Blo 424774 642827 := bstep (se 1 (by rfl) ⟨482120, by rfl⟩ : syracuseStep 642827 = 964241) B964241
theorem B642839 : Blo 424774 642839 := bstep (se 1 (by rfl) ⟨482129, by rfl⟩ : syracuseStep 642839 = 964259) B964259
theorem B642905 : Blo 424774 642905 := bstep (se 2 (by rfl) ⟨241089, by rfl⟩ : syracuseStep 642905 = 482179) B482179
theorem B479083 : Blo 424774 479083 := bstep (se 1 (by rfl) ⟨359312, by rfl⟩ : syracuseStep 479083 = 718625) B718625
theorem B643019 : Blo 424774 643019 := bstep (se 1 (by rfl) ⟨482264, by rfl⟩ : syracuseStep 643019 = 964529) B964529
theorem B479191 : Blo 424774 479191 := bstep (se 1 (by rfl) ⟨359393, by rfl⟩ : syracuseStep 479191 = 718787) B718787
theorem B643031 : Blo 424774 643031 := bstep (se 1 (by rfl) ⟨482273, by rfl⟩ : syracuseStep 643031 = 964547) B964547
theorem B806935 : Blo 424774 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B643097 : Blo 424774 643097 := bstep (se 2 (by rfl) ⟨241161, by rfl⟩ : syracuseStep 643097 = 482323) B482323
theorem B9261125 : Blo 424774 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B479371 : Blo 424774 479371 := bstep (se 1 (by rfl) ⟨359528, by rfl⟩ : syracuseStep 479371 = 719057) B719057
theorem B1626263 : Blo 424774 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B807155 : Blo 424774 807155 := bstep (se 1 (by rfl) ⟨605366, by rfl⟩ : syracuseStep 807155 = 1210733) B1210733
theorem B479479 : Blo 424774 479479 := bstep (se 1 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 479479 = 719219) B719219
theorem B577945 : Blo 424774 577945 := bstep (se 2 (by rfl) ⟨216729, by rfl⟩ : syracuseStep 577945 = 433459) B433459
theorem B479659 : Blo 424774 479659 := bstep (se 1 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 479659 = 719489) B719489
theorem B807383 : Blo 424774 807383 := bstep (se 1 (by rfl) ⟨605537, by rfl⟩ : syracuseStep 807383 = 1211075) B1211075
theorem B2150873 : Blo 424774 2150873 := bstep (se 2 (by rfl) ⟨806577, by rfl⟩ : syracuseStep 2150873 = 1613155) B1613155
theorem B1954307 : Blo 424774 1954307 := bstep (se 1 (by rfl) ⟨1465730, by rfl⟩ : syracuseStep 1954307 = 2931461) B2931461
theorem B479767 : Blo 424774 479767 := bstep (se 1 (by rfl) ⟨359825, by rfl⟩ : syracuseStep 479767 = 719651) B719651
theorem B1823411 : Blo 424774 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B479947 : Blo 424774 479947 := bstep (se 1 (by rfl) ⟨359960, by rfl⟩ : syracuseStep 479947 = 719921) B719921
theorem B807641 : Blo 424774 807641 := bstep (se 2 (by rfl) ⟨302865, by rfl⟩ : syracuseStep 807641 = 605731) B605731
theorem B971507 : Blo 424774 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B480055 : Blo 424774 480055 := bstep (se 1 (by rfl) ⟨360041, by rfl⟩ : syracuseStep 480055 = 720083) B720083
theorem B480235 : Blo 424774 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B480343 : Blo 424774 480343 := bstep (se 1 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 480343 = 720515) B720515
theorem B1725533 : Blo 424774 1725533 := bstep (se 3 (by rfl) ⟨323537, by rfl⟩ : syracuseStep 1725533 = 647075) B647075
theorem B808051 : Blo 424774 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B480523 : Blo 424774 480523 := bstep (se 1 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 480523 = 720785) B720785
theorem B480631 : Blo 424774 480631 := bstep (se 1 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 480631 = 720947) B720947
theorem B1627523 : Blo 424774 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B480811 : Blo 424774 480811 := bstep (se 1 (by rfl) ⟨360608, by rfl⟩ : syracuseStep 480811 = 721217) B721217
theorem B808537 : Blo 424774 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B480919 : Blo 424774 480919 := bstep (se 1 (by rfl) ⟨360689, by rfl⟩ : syracuseStep 480919 = 721379) B721379
theorem B972481 : Blo 424774 972481 := bstep (se 2 (by rfl) ⟨364680, by rfl⟩ : syracuseStep 972481 = 729361) B729361
theorem B4085453 : Blo 424774 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B481099 : Blo 424774 481099 := bstep (se 1 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 481099 = 721649) B721649
theorem B481207 : Blo 424774 481207 := bstep (se 1 (by rfl) ⟨360905, by rfl⟩ : syracuseStep 481207 = 721811) B721811
theorem B2152493 : Blo 424774 2152493 := bstep (se 3 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 2152493 = 807185) B807185
theorem B481387 : Blo 424774 481387 := bstep (se 1 (by rfl) ⟨361040, by rfl⟩ : syracuseStep 481387 = 722081) B722081
theorem B809099 : Blo 424774 809099 := bstep (se 1 (by rfl) ⟨606824, by rfl⟩ : syracuseStep 809099 = 1213649) B1213649
theorem B546955 : Blo 424774 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B1726667 : Blo 424774 1726667 := bstep (se 1 (by rfl) ⟨1295000, by rfl⟩ : syracuseStep 1726667 = 2590001) B2590001
theorem B481495 : Blo 424774 481495 := bstep (se 1 (by rfl) ⟨361121, by rfl⟩ : syracuseStep 481495 = 722243) B722243
theorem B907571 : Blo 424774 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B809281 : Blo 424774 809281 := bstep (se 2 (by rfl) ⟨303480, by rfl⟩ : syracuseStep 809281 = 606961) B606961
theorem B481675 : Blo 424774 481675 := bstep (se 1 (by rfl) ⟨361256, by rfl⟩ : syracuseStep 481675 = 722513) B722513
theorem B481783 : Blo 424774 481783 := bstep (se 1 (by rfl) ⟨361337, by rfl⟩ : syracuseStep 481783 = 722675) B722675
theorem B1825325 : Blo 424774 1825325 := bstep (se 3 (by rfl) ⟨342248, by rfl⟩ : syracuseStep 1825325 = 684497) B684497
theorem B481963 : Blo 424774 481963 := bstep (se 1 (by rfl) ⟨361472, by rfl⟩ : syracuseStep 481963 = 722945) B722945
theorem B842483 : Blo 424774 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B482071 : Blo 424774 482071 := bstep (se 1 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 482071 = 723107) B723107
theorem B5561189 : Blo 424774 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B2186135 : Blo 424774 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B7756721 : Blo 424774 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B482251 : Blo 424774 482251 := bstep (se 1 (by rfl) ⟨361688, by rfl⟩ : syracuseStep 482251 = 723377) B723377
theorem B809995 : Blo 424774 809995 := bstep (se 1 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 809995 = 1214993) B1214993
theorem B482359 : Blo 424774 482359 := bstep (se 1 (by rfl) ⟨361769, by rfl⟩ : syracuseStep 482359 = 723539) B723539
theorem B810071 : Blo 424774 810071 := bstep (se 1 (by rfl) ⟨607553, by rfl⟩ : syracuseStep 810071 = 1215107) B1215107
theorem B3169373 : Blo 424774 3169373 := bstep (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) B1188515
theorem B1826009 : Blo 424774 1826009 := bstep (se 2 (by rfl) ⟨684753, by rfl⟩ : syracuseStep 1826009 = 1369507) B1369507
theorem B777559 : Blo 424774 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B1727833 : Blo 424774 1727833 := bstep (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) B1295875
theorem B908759 : Blo 424774 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B810739 : Blo 424774 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B810967 : Blo 424774 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B811073 : Blo 424774 811073 := bstep (se 2 (by rfl) ⟨304152, by rfl⟩ : syracuseStep 811073 = 608305) B608305
theorem B811225 : Blo 424774 811225 := bstep (se 2 (by rfl) ⟨304209, by rfl⟩ : syracuseStep 811225 = 608419) B608419
theorem B1827137 : Blo 424774 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B3236273 : Blo 424774 3236273 := bstep (se 2 (by rfl) ⟨1213602, by rfl⟩ : syracuseStep 3236273 = 2427205) B2427205
theorem B909785 : Blo 424774 909785 := bstep (se 2 (by rfl) ⟨341169, by rfl⟩ : syracuseStep 909785 = 682339) B682339
theorem B1434077 : Blo 424774 1434077 := bstep (se 3 (by rfl) ⟨268889, by rfl⟩ : syracuseStep 1434077 = 537779) B537779
theorem B1532609 : Blo 424774 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B3236759 : Blo 424774 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B5825741 : Blo 424774 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B2057489 : Blo 424774 2057489 := bstep (se 2 (by rfl) ⟨771558, by rfl⟩ : syracuseStep 2057489 = 1543117) B1543117
theorem B910835 : Blo 424774 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B812531 : Blo 424774 812531 := bstep (se 1 (by rfl) ⟨609398, by rfl⟩ : syracuseStep 812531 = 1218797) B1218797
theorem B1435211 : Blo 424774 1435211 := bstep (se 1 (by rfl) ⟨1076408, by rfl⟩ : syracuseStep 1435211 = 2152817) B2152817
theorem B812683 : Blo 424774 812683 := bstep (se 1 (by rfl) ⟨609512, by rfl⟩ : syracuseStep 812683 = 1219025) B1219025
theorem B1435481 : Blo 424774 1435481 := bstep (se 2 (by rfl) ⟨538305, by rfl⟩ : syracuseStep 1435481 = 1076611) B1076611
theorem B2156381 : Blo 424774 2156381 := bstep (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) B808643
theorem B1828811 : Blo 424774 1828811 := bstep (se 1 (by rfl) ⟨1371608, by rfl⟩ : syracuseStep 1828811 = 2743217) B2743217
theorem B813017 : Blo 424774 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B1075265 : Blo 424774 1075265 := bstep (se 2 (by rfl) ⟨403224, by rfl⟩ : syracuseStep 1075265 = 806449) B806449
theorem B911425 : Blo 424774 911425 := bstep (se 2 (by rfl) ⟨341784, by rfl⟩ : syracuseStep 911425 = 683569) B683569
theorem B977035 : Blo 424774 977035 := bstep (se 1 (by rfl) ⟨732776, by rfl⟩ : syracuseStep 977035 = 1465553) B1465553
theorem B649495 : Blo 424774 649495 := bstep (se 1 (by rfl) ⟨487121, by rfl⟩ : syracuseStep 649495 = 974243) B974243
theorem B1436183 : Blo 424774 1436183 := bstep (se 1 (by rfl) ⟨1077137, by rfl⟩ : syracuseStep 1436183 = 2154275) B2154275
theorem B813655 : Blo 424774 813655 := bstep (se 1 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 813655 = 1220483) B1220483
theorem B1075801 : Blo 424774 1075801 := bstep (se 2 (by rfl) ⟨403425, by rfl⟩ : syracuseStep 1075801 = 806851) B806851
theorem B486059 : Blo 424774 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B1370969 : Blo 424774 1370969 := bstep (se 2 (by rfl) ⟨514113, by rfl⟩ : syracuseStep 1370969 = 1028227) B1028227
theorem B617431 : Blo 424774 617431 := bstep (se 1 (by rfl) ⟨463073, by rfl⟩ : syracuseStep 617431 = 926147) B926147
theorem B1436723 : Blo 424774 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1830109 : Blo 424774 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B3697937 : Blo 424774 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B486679 : Blo 424774 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B1436993 : Blo 424774 1436993 := bstep (se 2 (by rfl) ⟨538872, by rfl⟩ : syracuseStep 1436993 = 1077745) B1077745
theorem B1535377 : Blo 424774 1535377 := bstep (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) B1151533
theorem B1535449 : Blo 424774 1535449 := bstep (se 2 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 1535449 = 1151587) B1151587
theorem B1830451 : Blo 424774 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B912971 : Blo 424774 912971 := bstep (se 1 (by rfl) ⟨684728, by rfl⟩ : syracuseStep 912971 = 1369457) B1369457
theorem B1076915 : Blo 424774 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B683723 : Blo 424774 683723 := bstep (se 1 (by rfl) ⟨512792, by rfl⟩ : syracuseStep 683723 = 1025585) B1025585
theorem B2420441 : Blo 424774 2420441 := bstep (se 2 (by rfl) ⟨907665, by rfl⟩ : syracuseStep 2420441 = 1815331) B1815331
theorem B3108701 : Blo 424774 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B1437533 : Blo 424774 1437533 := bstep (se 3 (by rfl) ⟨269537, by rfl⟩ : syracuseStep 1437533 = 539075) B539075
theorem B2158487 : Blo 424774 2158487 := bstep (se 1 (by rfl) ⟨1618865, by rfl⟩ : syracuseStep 2158487 = 3237731) B3237731
theorem B1077209 : Blo 424774 1077209 := bstep (se 2 (by rfl) ⟨403953, by rfl⟩ : syracuseStep 1077209 = 807907) B807907
theorem B6156323 : Blo 424774 6156323 := bstep (se 1 (by rfl) ⟨4617242, by rfl⟩ : syracuseStep 6156323 = 9234485) B9234485
theorem B4878467 : Blo 424774 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B716951 : Blo 424774 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B4944023 : Blo 424774 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B684235 : Blo 424774 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B1994969 : Blo 424774 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B717079 : Blo 424774 717079 := bstep (se 1 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 717079 = 1075619) B1075619
theorem B455063 : Blo 424774 455063 := bstep (se 1 (by rfl) ⟨341297, by rfl⟩ : syracuseStep 455063 = 682595) B682595
theorem B913817 : Blo 424774 913817 := bstep (se 2 (by rfl) ⟨342681, by rfl⟩ : syracuseStep 913817 = 685363) B685363
theorem B5468593 : Blo 424774 5468593 := bstep (se 2 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 5468593 = 4101445) B4101445
theorem B13529693 : Blo 424774 13529693 := bstep (se 3 (by rfl) ⟨2536817, by rfl⟩ : syracuseStep 13529693 = 5073635) B5073635
theorem B717707 : Blo 424774 717707 := bstep (se 1 (by rfl) ⟨538280, by rfl⟩ : syracuseStep 717707 = 1076561) B1076561
theorem B684953 : Blo 424774 684953 := bstep (se 2 (by rfl) ⟨256857, by rfl⟩ : syracuseStep 684953 = 513715) B513715
theorem B1438667 : Blo 424774 1438667 := bstep (se 1 (by rfl) ⟨1079000, by rfl⟩ : syracuseStep 1438667 = 2158001) B2158001
theorem B717835 : Blo 424774 717835 := bstep (se 1 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 717835 = 1076753) B1076753
theorem B1373249 : Blo 424774 1373249 := bstep (se 2 (by rfl) ⟨514968, by rfl⟩ : syracuseStep 1373249 = 1029937) B1029937
theorem B717977 : Blo 424774 717977 := bstep (se 2 (by rfl) ⟨269241, by rfl⟩ : syracuseStep 717977 = 538483) B538483
theorem B914611 : Blo 424774 914611 := bstep (se 1 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 914611 = 1371917) B1371917
theorem B1438937 : Blo 424774 1438937 := bstep (se 2 (by rfl) ⟨539601, by rfl⟩ : syracuseStep 1438937 = 1079203) B1079203
theorem B718105 : Blo 424774 718105 := bstep (se 2 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 718105 = 538579) B538579
theorem B1734061 : Blo 424774 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B1078859 : Blo 424774 1078859 := bstep (se 1 (by rfl) ⟨809144, by rfl⟩ : syracuseStep 1078859 = 1618289) B1618289
theorem B2487901 : Blo 424774 2487901 := bstep (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) B932963
theorem B1210049 : Blo 424774 1210049 := bstep (se 2 (by rfl) ⟨453768, by rfl⟩ : syracuseStep 1210049 = 907537) B907537
theorem B718679 : Blo 424774 718679 := bstep (se 1 (by rfl) ⟨539009, by rfl⟩ : syracuseStep 718679 = 1078019) B1078019
theorem B1439639 : Blo 424774 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B12318641 : Blo 424774 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B1537985 : Blo 424774 1537985 := bstep (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) B1153489
theorem B718807 : Blo 424774 718807 := bstep (se 1 (by rfl) ⟨539105, by rfl⟩ : syracuseStep 718807 = 1078211) B1078211
theorem B915457 : Blo 424774 915457 := bstep (se 2 (by rfl) ⟨343296, by rfl⟩ : syracuseStep 915457 = 686593) B686593
theorem B456887 : Blo 424774 456887 := bstep (se 1 (by rfl) ⟨342665, by rfl⟩ : syracuseStep 456887 = 685331) B685331
theorem B1210585 : Blo 424774 1210585 := bstep (se 2 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 1210585 = 907939) B907939
theorem B2423105 : Blo 424774 2423105 := bstep (se 2 (by rfl) ⟨908664, by rfl⟩ : syracuseStep 2423105 = 1817329) B1817329
theorem B817523 : Blo 424774 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B1440179 : Blo 424774 1440179 := bstep (se 1 (by rfl) ⟨1080134, by rfl⟩ : syracuseStep 1440179 = 2160269) B2160269
theorem B1079831 : Blo 424774 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B719435 : Blo 424774 719435 := bstep (se 1 (by rfl) ⟨539576, by rfl⟩ : syracuseStep 719435 = 1079153) B1079153
theorem B2226781 : Blo 424774 2226781 := bstep (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) B835043
theorem B1637015 : Blo 424774 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B1440449 : Blo 424774 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B719563 : Blo 424774 719563 := bstep (se 1 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 719563 = 1079345) B1079345
theorem B1669835 : Blo 424774 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B424779 : Blo 424774 424779 := bstep (se 1 (by rfl) ⟨318584, by rfl⟩ : syracuseStep 424779 = 637169) B637169
theorem B424791 : Blo 424774 424791 := bstep (se 1 (by rfl) ⟨318593, by rfl⟩ : syracuseStep 424791 = 637187) B637187
theorem B719705 : Blo 424774 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1538909 : Blo 424774 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B424811 : Blo 424774 424811 := bstep (se 1 (by rfl) ⟨318608, by rfl⟩ : syracuseStep 424811 = 637217) B637217
theorem B457579 : Blo 424774 457579 := bstep (se 1 (by rfl) ⟨343184, by rfl⟩ : syracuseStep 457579 = 686369) B686369
theorem B424823 : Blo 424774 424823 := bstep (se 1 (by rfl) ⟨318617, by rfl⟩ : syracuseStep 424823 = 637235) B637235
theorem B424843 : Blo 424774 424843 := bstep (se 1 (by rfl) ⟨318632, by rfl⟩ : syracuseStep 424843 = 637265) B637265
theorem B424855 : Blo 424774 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B424875 : Blo 424774 424875 := bstep (se 1 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 424875 = 637313) B637313
theorem B424887 : Blo 424774 424887 := bstep (se 1 (by rfl) ⟨318665, by rfl⟩ : syracuseStep 424887 = 637331) B637331
theorem B424907 : Blo 424774 424907 := bstep (se 1 (by rfl) ⟨318680, by rfl⟩ : syracuseStep 424907 = 637361) B637361
theorem B424919 : Blo 424774 424919 := bstep (se 1 (by rfl) ⟨318689, by rfl⟩ : syracuseStep 424919 = 637379) B637379
theorem B719833 : Blo 424774 719833 := bstep (se 2 (by rfl) ⟨269937, by rfl⟩ : syracuseStep 719833 = 539875) B539875
theorem B424939 : Blo 424774 424939 := bstep (se 1 (by rfl) ⟨318704, by rfl⟩ : syracuseStep 424939 = 637409) B637409
theorem B424951 : Blo 424774 424951 := bstep (se 1 (by rfl) ⟨318713, by rfl⟩ : syracuseStep 424951 = 637427) B637427
theorem B424971 : Blo 424774 424971 := bstep (se 1 (by rfl) ⟨318728, by rfl⟩ : syracuseStep 424971 = 637457) B637457
theorem B424983 : Blo 424774 424983 := bstep (se 1 (by rfl) ⟨318737, by rfl⟩ : syracuseStep 424983 = 637475) B637475
theorem B425003 : Blo 424774 425003 := bstep (se 1 (by rfl) ⟨318752, by rfl⟩ : syracuseStep 425003 = 637505) B637505
theorem B425015 : Blo 424774 425015 := bstep (se 1 (by rfl) ⟨318761, by rfl⟩ : syracuseStep 425015 = 637523) B637523
theorem B13859909 : Blo 424774 13859909 := bstep (se 4 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 13859909 = 2598733) B2598733
theorem B425035 : Blo 424774 425035 := bstep (se 1 (by rfl) ⟨318776, by rfl⟩ : syracuseStep 425035 = 637553) B637553
theorem B425047 : Blo 424774 425047 := bstep (se 1 (by rfl) ⟨318785, by rfl⟩ : syracuseStep 425047 = 637571) B637571
theorem B425067 : Blo 424774 425067 := bstep (se 1 (by rfl) ⟨318800, by rfl⟩ : syracuseStep 425067 = 637601) B637601
theorem B425079 : Blo 424774 425079 := bstep (se 1 (by rfl) ⟨318809, by rfl⟩ : syracuseStep 425079 = 637619) B637619
theorem B425099 : Blo 424774 425099 := bstep (se 1 (by rfl) ⟨318824, by rfl⟩ : syracuseStep 425099 = 637649) B637649
theorem B425111 : Blo 424774 425111 := bstep (se 1 (by rfl) ⟨318833, by rfl⟩ : syracuseStep 425111 = 637667) B637667
theorem B425131 : Blo 424774 425131 := bstep (se 1 (by rfl) ⟨318848, by rfl⟩ : syracuseStep 425131 = 637697) B637697
theorem B1080499 : Blo 424774 1080499 := bstep (se 1 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 1080499 = 1620749) B1620749
theorem B425143 : Blo 424774 425143 := bstep (se 1 (by rfl) ⟨318857, by rfl⟩ : syracuseStep 425143 = 637715) B637715
theorem B425163 : Blo 424774 425163 := bstep (se 1 (by rfl) ⟨318872, by rfl⟩ : syracuseStep 425163 = 637745) B637745
theorem B425175 : Blo 424774 425175 := bstep (se 1 (by rfl) ⟨318881, by rfl⟩ : syracuseStep 425175 = 637763) B637763
theorem B1440989 : Blo 424774 1440989 := bstep (se 3 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 1440989 = 540371) B540371
theorem B425195 : Blo 424774 425195 := bstep (se 1 (by rfl) ⟨318896, by rfl⟩ : syracuseStep 425195 = 637793) B637793
theorem B425207 : Blo 424774 425207 := bstep (se 1 (by rfl) ⟨318905, by rfl⟩ : syracuseStep 425207 = 637811) B637811
theorem B425227 : Blo 424774 425227 := bstep (se 1 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 425227 = 637841) B637841
theorem B425239 : Blo 424774 425239 := bstep (se 1 (by rfl) ⟨318929, by rfl⟩ : syracuseStep 425239 = 637859) B637859
theorem B425259 : Blo 424774 425259 := bstep (se 1 (by rfl) ⟨318944, by rfl⟩ : syracuseStep 425259 = 637889) B637889
theorem B425271 : Blo 424774 425271 := bstep (se 1 (by rfl) ⟨318953, by rfl⟩ : syracuseStep 425271 = 637907) B637907
theorem B1080641 : Blo 424774 1080641 := bstep (se 2 (by rfl) ⟨405240, by rfl⟩ : syracuseStep 1080641 = 810481) B810481
theorem B425291 : Blo 424774 425291 := bstep (se 1 (by rfl) ⟨318968, by rfl⟩ : syracuseStep 425291 = 637937) B637937
theorem B425303 : Blo 424774 425303 := bstep (se 1 (by rfl) ⟨318977, by rfl⟩ : syracuseStep 425303 = 637955) B637955
theorem B425323 : Blo 424774 425323 := bstep (se 1 (by rfl) ⟨318992, by rfl⟩ : syracuseStep 425323 = 637985) B637985
theorem B425335 : Blo 424774 425335 := bstep (se 1 (by rfl) ⟨319001, by rfl⟩ : syracuseStep 425335 = 638003) B638003
theorem B2162051 : Blo 424774 2162051 := bstep (se 1 (by rfl) ⟨1621538, by rfl⟩ : syracuseStep 2162051 = 3243077) B3243077
theorem B425355 : Blo 424774 425355 := bstep (se 1 (by rfl) ⟨319016, by rfl⟩ : syracuseStep 425355 = 638033) B638033
theorem B425367 : Blo 424774 425367 := bstep (se 1 (by rfl) ⟨319025, by rfl⟩ : syracuseStep 425367 = 638051) B638051
theorem B425387 : Blo 424774 425387 := bstep (se 1 (by rfl) ⟨319040, by rfl⟩ : syracuseStep 425387 = 638081) B638081
theorem B425399 : Blo 424774 425399 := bstep (se 1 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 425399 = 638099) B638099
theorem B1244609 : Blo 424774 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B425419 : Blo 424774 425419 := bstep (se 1 (by rfl) ⟨319064, by rfl⟩ : syracuseStep 425419 = 638129) B638129
theorem B425431 : Blo 424774 425431 := bstep (se 1 (by rfl) ⟨319073, by rfl⟩ : syracuseStep 425431 = 638147) B638147
theorem B7044569 : Blo 424774 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B425451 : Blo 424774 425451 := bstep (se 1 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 425451 = 638177) B638177
theorem B425463 : Blo 424774 425463 := bstep (se 1 (by rfl) ⟨319097, by rfl⟩ : syracuseStep 425463 = 638195) B638195
theorem B425483 : Blo 424774 425483 := bstep (se 1 (by rfl) ⟨319112, by rfl⟩ : syracuseStep 425483 = 638225) B638225
theorem B425495 : Blo 424774 425495 := bstep (se 1 (by rfl) ⟨319121, by rfl⟩ : syracuseStep 425495 = 638243) B638243
theorem B720407 : Blo 424774 720407 := bstep (se 1 (by rfl) ⟨540305, by rfl⟩ : syracuseStep 720407 = 1080611) B1080611
theorem B425515 : Blo 424774 425515 := bstep (se 1 (by rfl) ⟨319136, by rfl⟩ : syracuseStep 425515 = 638273) B638273
theorem B425527 : Blo 424774 425527 := bstep (se 1 (by rfl) ⟨319145, by rfl⟩ : syracuseStep 425527 = 638291) B638291
theorem B425547 : Blo 424774 425547 := bstep (se 1 (by rfl) ⟨319160, by rfl⟩ : syracuseStep 425547 = 638321) B638321
theorem B425559 : Blo 424774 425559 := bstep (se 1 (by rfl) ⟨319169, by rfl⟩ : syracuseStep 425559 = 638339) B638339
theorem B425579 : Blo 424774 425579 := bstep (se 1 (by rfl) ⟨319184, by rfl⟩ : syracuseStep 425579 = 638369) B638369
theorem B425591 : Blo 424774 425591 := bstep (se 1 (by rfl) ⟨319193, by rfl⟩ : syracuseStep 425591 = 638387) B638387
theorem B3899011 : Blo 424774 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B425611 : Blo 424774 425611 := bstep (se 1 (by rfl) ⟨319208, by rfl⟩ : syracuseStep 425611 = 638417) B638417
theorem B425623 : Blo 424774 425623 := bstep (se 1 (by rfl) ⟨319217, by rfl⟩ : syracuseStep 425623 = 638435) B638435
theorem B720535 : Blo 424774 720535 := bstep (se 1 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 720535 = 1080803) B1080803
theorem B425643 : Blo 424774 425643 := bstep (se 1 (by rfl) ⟨319232, by rfl⟩ : syracuseStep 425643 = 638465) B638465
theorem B425655 : Blo 424774 425655 := bstep (se 1 (by rfl) ⟨319241, by rfl⟩ : syracuseStep 425655 = 638483) B638483
theorem B425675 : Blo 424774 425675 := bstep (se 1 (by rfl) ⟨319256, by rfl⟩ : syracuseStep 425675 = 638513) B638513
theorem B425687 : Blo 424774 425687 := bstep (se 1 (by rfl) ⟨319265, by rfl⟩ : syracuseStep 425687 = 638531) B638531
theorem B425707 : Blo 424774 425707 := bstep (se 1 (by rfl) ⟨319280, by rfl⟩ : syracuseStep 425707 = 638561) B638561
theorem B425719 : Blo 424774 425719 := bstep (se 1 (by rfl) ⟨319289, by rfl⟩ : syracuseStep 425719 = 638579) B638579
theorem B425739 : Blo 424774 425739 := bstep (se 1 (by rfl) ⟨319304, by rfl⟩ : syracuseStep 425739 = 638609) B638609
theorem B425751 : Blo 424774 425751 := bstep (se 1 (by rfl) ⟨319313, by rfl⟩ : syracuseStep 425751 = 638627) B638627
theorem B425771 : Blo 424774 425771 := bstep (se 1 (by rfl) ⟨319328, by rfl⟩ : syracuseStep 425771 = 638657) B638657
theorem B425783 : Blo 424774 425783 := bstep (se 1 (by rfl) ⟨319337, by rfl⟩ : syracuseStep 425783 = 638675) B638675
theorem B8224577 : Blo 424774 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B425803 : Blo 424774 425803 := bstep (se 1 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 425803 = 638705) B638705
theorem B425815 : Blo 424774 425815 := bstep (se 1 (by rfl) ⟨319361, by rfl⟩ : syracuseStep 425815 = 638723) B638723
theorem B425835 : Blo 424774 425835 := bstep (se 1 (by rfl) ⟨319376, by rfl⟩ : syracuseStep 425835 = 638753) B638753
theorem B425847 : Blo 424774 425847 := bstep (se 1 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 425847 = 638771) B638771
theorem B425867 : Blo 424774 425867 := bstep (se 1 (by rfl) ⟨319400, by rfl⟩ : syracuseStep 425867 = 638801) B638801
theorem B425879 : Blo 424774 425879 := bstep (se 1 (by rfl) ⟨319409, by rfl⟩ : syracuseStep 425879 = 638819) B638819
theorem B425899 : Blo 424774 425899 := bstep (se 1 (by rfl) ⟨319424, by rfl⟩ : syracuseStep 425899 = 638849) B638849
theorem B425911 : Blo 424774 425911 := bstep (se 1 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 425911 = 638867) B638867
theorem B425931 : Blo 424774 425931 := bstep (se 1 (by rfl) ⟨319448, by rfl⟩ : syracuseStep 425931 = 638897) B638897
theorem B425943 : Blo 424774 425943 := bstep (se 1 (by rfl) ⟨319457, by rfl⟩ : syracuseStep 425943 = 638915) B638915
theorem B3112921 : Blo 424774 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B425963 : Blo 424774 425963 := bstep (se 1 (by rfl) ⟨319472, by rfl⟩ : syracuseStep 425963 = 638945) B638945
theorem B425975 : Blo 424774 425975 := bstep (se 1 (by rfl) ⟨319481, by rfl⟩ : syracuseStep 425975 = 638963) B638963
theorem B425991 : Blo 424774 425991 := bstep (se 1 (by rfl) ⟨319493, by rfl⟩ : syracuseStep 425991 = 638987) B638987
theorem B2162699 : Blo 424774 2162699 := bstep (se 1 (by rfl) ⟨1622024, by rfl⟩ : syracuseStep 2162699 = 3244049) B3244049
theorem B425999 : Blo 424774 425999 := bstep (se 1 (by rfl) ⟨319499, by rfl⟩ : syracuseStep 425999 = 638999) B638999
theorem B426043 : Blo 424774 426043 := bstep (se 1 (by rfl) ⟨319532, by rfl⟩ : syracuseStep 426043 = 639065) B639065
theorem B1441853 : Blo 424774 1441853 := bstep (se 3 (by rfl) ⟨270347, by rfl⟩ : syracuseStep 1441853 = 540695) B540695
theorem B426119 : Blo 424774 426119 := bstep (se 1 (by rfl) ⟨319589, by rfl⟩ : syracuseStep 426119 = 639179) B639179
theorem B426127 : Blo 424774 426127 := bstep (se 1 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 426127 = 639191) B639191
theorem B2162861 : Blo 424774 2162861 := bstep (se 3 (by rfl) ⟨405536, by rfl⟩ : syracuseStep 2162861 = 811073) B811073
theorem B426171 : Blo 424774 426171 := bstep (se 1 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 426171 = 639257) B639257
theorem B426247 : Blo 424774 426247 := bstep (se 1 (by rfl) ⟨319685, by rfl⟩ : syracuseStep 426247 = 639371) B639371
theorem B426255 : Blo 424774 426255 := bstep (se 1 (by rfl) ⟨319691, by rfl⟩ : syracuseStep 426255 = 639383) B639383
theorem B1081633 : Blo 424774 1081633 := bstep (se 2 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 1081633 = 811225) B811225
theorem B426299 : Blo 424774 426299 := bstep (se 1 (by rfl) ⟨319724, by rfl⟩ : syracuseStep 426299 = 639449) B639449
theorem B721271 : Blo 424774 721271 := bstep (se 1 (by rfl) ⟨540953, by rfl⟩ : syracuseStep 721271 = 1081907) B1081907
theorem B426375 : Blo 424774 426375 := bstep (se 1 (by rfl) ⟨319781, by rfl⟩ : syracuseStep 426375 = 639563) B639563
theorem B426383 : Blo 424774 426383 := bstep (se 1 (by rfl) ⟨319787, by rfl⟩ : syracuseStep 426383 = 639575) B639575
theorem B426427 : Blo 424774 426427 := bstep (se 1 (by rfl) ⟨319820, by rfl⟩ : syracuseStep 426427 = 639641) B639641
theorem B426503 : Blo 424774 426503 := bstep (se 1 (by rfl) ⟨319877, by rfl⟩ : syracuseStep 426503 = 639755) B639755
theorem B426511 : Blo 424774 426511 := bstep (se 1 (by rfl) ⟨319883, by rfl⟩ : syracuseStep 426511 = 639767) B639767
theorem B9208363 : Blo 424774 9208363 := bstep (se 1 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 9208363 = 13812545) B13812545
theorem B426555 : Blo 424774 426555 := bstep (se 1 (by rfl) ⟨319916, by rfl⟩ : syracuseStep 426555 = 639833) B639833
theorem B1540727 : Blo 424774 1540727 := bstep (se 1 (by rfl) ⟨1155545, by rfl⟩ : syracuseStep 1540727 = 2311091) B2311091
theorem B426631 : Blo 424774 426631 := bstep (se 1 (by rfl) ⟨319973, by rfl⟩ : syracuseStep 426631 = 639947) B639947
theorem B426639 : Blo 424774 426639 := bstep (se 1 (by rfl) ⟨319979, by rfl⟩ : syracuseStep 426639 = 639959) B639959
theorem B426683 : Blo 424774 426683 := bstep (se 1 (by rfl) ⟨320012, by rfl⟩ : syracuseStep 426683 = 640025) B640025
theorem B2917093 : Blo 424774 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B426759 : Blo 424774 426759 := bstep (se 1 (by rfl) ⟨320069, by rfl⟩ : syracuseStep 426759 = 640139) B640139
theorem B426767 : Blo 424774 426767 := bstep (se 1 (by rfl) ⟨320075, by rfl⟩ : syracuseStep 426767 = 640151) B640151
theorem B426811 : Blo 424774 426811 := bstep (se 1 (by rfl) ⟨320108, by rfl⟩ : syracuseStep 426811 = 640217) B640217
theorem B721723 : Blo 424774 721723 := bstep (se 1 (by rfl) ⟨541292, by rfl⟩ : syracuseStep 721723 = 1082585) B1082585
theorem B1082231 : Blo 424774 1082231 := bstep (se 1 (by rfl) ⟨811673, by rfl⟩ : syracuseStep 1082231 = 1623347) B1623347
theorem B1213319 : Blo 424774 1213319 := bstep (se 1 (by rfl) ⟨909989, by rfl⟩ : syracuseStep 1213319 = 1819979) B1819979
theorem B426887 : Blo 424774 426887 := bstep (se 1 (by rfl) ⟨320165, by rfl⟩ : syracuseStep 426887 = 640331) B640331
theorem B426895 : Blo 424774 426895 := bstep (se 1 (by rfl) ⟨320171, by rfl⟩ : syracuseStep 426895 = 640343) B640343
theorem B2425747 : Blo 424774 2425747 := bstep (se 1 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 2425747 = 3638621) B3638621
theorem B426939 : Blo 424774 426939 := bstep (se 1 (by rfl) ⟨320204, by rfl⟩ : syracuseStep 426939 = 640409) B640409
theorem B721865 : Blo 424774 721865 := bstep (se 2 (by rfl) ⟨270699, by rfl⟩ : syracuseStep 721865 = 541399) B541399
theorem B427015 : Blo 424774 427015 := bstep (se 1 (by rfl) ⟨320261, by rfl⟩ : syracuseStep 427015 = 640523) B640523
theorem B427023 : Blo 424774 427023 := bstep (se 1 (by rfl) ⟨320267, by rfl⟩ : syracuseStep 427023 = 640535) B640535
theorem B2458667 : Blo 424774 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B427067 : Blo 424774 427067 := bstep (se 1 (by rfl) ⟨320300, by rfl⟩ : syracuseStep 427067 = 640601) B640601
theorem B1213501 : Blo 424774 1213501 := bstep (se 3 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 1213501 = 455063) B455063
theorem B427143 : Blo 424774 427143 := bstep (se 1 (by rfl) ⟨320357, by rfl⟩ : syracuseStep 427143 = 640715) B640715
theorem B427151 : Blo 424774 427151 := bstep (se 1 (by rfl) ⟨320363, by rfl⟩ : syracuseStep 427151 = 640727) B640727
theorem B427195 : Blo 424774 427195 := bstep (se 1 (by rfl) ⟨320396, by rfl⟩ : syracuseStep 427195 = 640793) B640793
theorem B427271 : Blo 424774 427271 := bstep (se 1 (by rfl) ⟨320453, by rfl⟩ : syracuseStep 427271 = 640907) B640907
theorem B427279 : Blo 424774 427279 := bstep (se 1 (by rfl) ⟨320459, by rfl⟩ : syracuseStep 427279 = 640919) B640919
theorem B2917691 : Blo 424774 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B427323 : Blo 424774 427323 := bstep (se 1 (by rfl) ⟨320492, by rfl⟩ : syracuseStep 427323 = 640985) B640985
theorem B5211485 : Blo 424774 5211485 := bstep (se 3 (by rfl) ⟨977153, by rfl⟩ : syracuseStep 5211485 = 1954307) B1954307
theorem B427399 : Blo 424774 427399 := bstep (se 1 (by rfl) ⟨320549, by rfl⟩ : syracuseStep 427399 = 641099) B641099
theorem B427407 : Blo 424774 427407 := bstep (se 1 (by rfl) ⟨320555, by rfl⟩ : syracuseStep 427407 = 641111) B641111
theorem B1443257 : Blo 424774 1443257 := bstep (se 2 (by rfl) ⟨541221, by rfl⟩ : syracuseStep 1443257 = 1082443) B1082443
theorem B427451 : Blo 424774 427451 := bstep (se 1 (by rfl) ⟨320588, by rfl⟩ : syracuseStep 427451 = 641177) B641177
theorem B427527 : Blo 424774 427527 := bstep (se 1 (by rfl) ⟨320645, by rfl⟩ : syracuseStep 427527 = 641291) B641291
theorem B1213967 : Blo 424774 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B427535 : Blo 424774 427535 := bstep (se 1 (by rfl) ⟨320651, by rfl⟩ : syracuseStep 427535 = 641303) B641303
theorem B427579 : Blo 424774 427579 := bstep (se 1 (by rfl) ⟨320684, by rfl⟩ : syracuseStep 427579 = 641369) B641369
theorem B22808141 : Blo 424774 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B36079181 : Blo 424774 36079181 := bstep (se 3 (by rfl) ⟨6764846, by rfl⟩ : syracuseStep 36079181 = 13529693) B13529693
theorem B427655 : Blo 424774 427655 := bstep (se 1 (by rfl) ⟨320741, by rfl⟩ : syracuseStep 427655 = 641483) B641483
theorem B722567 : Blo 424774 722567 := bstep (se 1 (by rfl) ⟨541925, by rfl⟩ : syracuseStep 722567 = 1083851) B1083851
theorem B427663 : Blo 424774 427663 := bstep (se 1 (by rfl) ⟨320747, by rfl⟩ : syracuseStep 427663 = 641495) B641495
theorem B427707 : Blo 424774 427707 := bstep (se 1 (by rfl) ⟨320780, by rfl⟩ : syracuseStep 427707 = 641561) B641561
theorem B2164481 : Blo 424774 2164481 := bstep (se 2 (by rfl) ⟨811680, by rfl⟩ : syracuseStep 2164481 = 1623361) B1623361
theorem B427783 : Blo 424774 427783 := bstep (se 1 (by rfl) ⟨320837, by rfl⟩ : syracuseStep 427783 = 641675) B641675
theorem B427791 : Blo 424774 427791 := bstep (se 1 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 427791 = 641687) B641687
theorem B427835 : Blo 424774 427835 := bstep (se 1 (by rfl) ⟨320876, by rfl⟩ : syracuseStep 427835 = 641753) B641753
theorem B427911 : Blo 424774 427911 := bstep (se 1 (by rfl) ⟨320933, by rfl⟩ : syracuseStep 427911 = 641867) B641867
theorem B427919 : Blo 424774 427919 := bstep (se 1 (by rfl) ⟨320939, by rfl⟩ : syracuseStep 427919 = 641879) B641879
theorem B427963 : Blo 424774 427963 := bstep (se 1 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 427963 = 641945) B641945
theorem B428039 : Blo 424774 428039 := bstep (se 1 (by rfl) ⟨321029, by rfl⟩ : syracuseStep 428039 = 642059) B642059
theorem B1443851 : Blo 424774 1443851 := bstep (se 1 (by rfl) ⟨1082888, by rfl⟩ : syracuseStep 1443851 = 2165777) B2165777
theorem B428047 : Blo 424774 428047 := bstep (se 1 (by rfl) ⟨321035, by rfl⟩ : syracuseStep 428047 = 642071) B642071
theorem B428091 : Blo 424774 428091 := bstep (se 1 (by rfl) ⟨321068, by rfl⟩ : syracuseStep 428091 = 642137) B642137
theorem B1443959 : Blo 424774 1443959 := bstep (se 1 (by rfl) ⟨1082969, by rfl⟩ : syracuseStep 1443959 = 2165939) B2165939
theorem B3082373 : Blo 424774 3082373 := bstep (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) B577945
theorem B1083527 : Blo 424774 1083527 := bstep (se 1 (by rfl) ⟨812645, by rfl⟩ : syracuseStep 1083527 = 1625291) B1625291
theorem B428167 : Blo 424774 428167 := bstep (se 1 (by rfl) ⟨321125, by rfl⟩ : syracuseStep 428167 = 642251) B642251
theorem B428175 : Blo 424774 428175 := bstep (se 1 (by rfl) ⟨321131, by rfl⟩ : syracuseStep 428175 = 642263) B642263
theorem B1083577 : Blo 424774 1083577 := bstep (se 2 (by rfl) ⟨406341, by rfl⟩ : syracuseStep 1083577 = 812683) B812683
theorem B428219 : Blo 424774 428219 := bstep (se 1 (by rfl) ⟨321164, by rfl⟩ : syracuseStep 428219 = 642329) B642329
theorem B428295 : Blo 424774 428295 := bstep (se 1 (by rfl) ⟨321221, by rfl⟩ : syracuseStep 428295 = 642443) B642443
theorem B428303 : Blo 424774 428303 := bstep (se 1 (by rfl) ⟨321227, by rfl⟩ : syracuseStep 428303 = 642455) B642455
theorem B723215 : Blo 424774 723215 := bstep (se 1 (by rfl) ⟨542411, by rfl⟩ : syracuseStep 723215 = 1084823) B1084823
theorem B428347 : Blo 424774 428347 := bstep (se 1 (by rfl) ⟨321260, by rfl⟩ : syracuseStep 428347 = 642521) B642521
theorem B428423 : Blo 424774 428423 := bstep (se 1 (by rfl) ⟨321317, by rfl⟩ : syracuseStep 428423 = 642635) B642635
theorem B428431 : Blo 424774 428431 := bstep (se 1 (by rfl) ⟨321323, by rfl⟩ : syracuseStep 428431 = 642647) B642647
theorem B7801235 : Blo 424774 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B1149337 : Blo 424774 1149337 := bstep (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) B862003
theorem B428475 : Blo 424774 428475 := bstep (se 1 (by rfl) ⟨321356, by rfl⟩ : syracuseStep 428475 = 642713) B642713
theorem B428551 : Blo 424774 428551 := bstep (se 1 (by rfl) ⟨321413, by rfl⟩ : syracuseStep 428551 = 642827) B642827
theorem B428559 : Blo 424774 428559 := bstep (se 1 (by rfl) ⟨321419, by rfl⟩ : syracuseStep 428559 = 642839) B642839
theorem B2165291 : Blo 424774 2165291 := bstep (se 1 (by rfl) ⟨1623968, by rfl⟩ : syracuseStep 2165291 = 3247937) B3247937
theorem B428603 : Blo 424774 428603 := bstep (se 1 (by rfl) ⟨321452, by rfl⟩ : syracuseStep 428603 = 642905) B642905
theorem B2427479 : Blo 424774 2427479 := bstep (se 1 (by rfl) ⟨1820609, by rfl⟩ : syracuseStep 2427479 = 3641219) B3641219
theorem B428679 : Blo 424774 428679 := bstep (se 1 (by rfl) ⟨321509, by rfl⟩ : syracuseStep 428679 = 643019) B643019
theorem B428687 : Blo 424774 428687 := bstep (se 1 (by rfl) ⟨321515, by rfl⟩ : syracuseStep 428687 = 643031) B643031
theorem B428731 : Blo 424774 428731 := bstep (se 1 (by rfl) ⟨321548, by rfl⟩ : syracuseStep 428731 = 643097) B643097
theorem B1444553 : Blo 424774 1444553 := bstep (se 2 (by rfl) ⟨541707, by rfl⟩ : syracuseStep 1444553 = 1083415) B1083415
theorem B1215233 : Blo 424774 1215233 := bstep (se 2 (by rfl) ⟨455712, by rfl⟩ : syracuseStep 1215233 = 911425) B911425
theorem B1084175 : Blo 424774 1084175 := bstep (se 1 (by rfl) ⟨813131, by rfl⟩ : syracuseStep 1084175 = 1626263) B1626263
theorem B3083123 : Blo 424774 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B3083465 : Blo 424774 3083465 := bstep (se 2 (by rfl) ⟨1156299, by rfl⟩ : syracuseStep 3083465 = 2312599) B2312599
theorem B15535309 : Blo 424774 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B1445255 : Blo 424774 1445255 := bstep (se 1 (by rfl) ⟨1083941, by rfl⟩ : syracuseStep 1445255 = 2167883) B2167883
theorem B1150355 : Blo 424774 1150355 := bstep (se 1 (by rfl) ⟨862766, by rfl⟩ : syracuseStep 1150355 = 1725533) B1725533
theorem B1084873 : Blo 424774 1084873 := bstep (se 2 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 1084873 = 813655) B813655
theorem B7179853 : Blo 424774 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B1085015 : Blo 424774 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B1445633 : Blo 424774 1445633 := bstep (se 2 (by rfl) ⟨542112, by rfl⟩ : syracuseStep 1445633 = 1084225) B1084225
theorem B2723635 : Blo 424774 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B2166587 : Blo 424774 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B823241 : Blo 424774 823241 := bstep (se 2 (by rfl) ⟨308715, by rfl⟩ : syracuseStep 823241 = 617431) B617431
theorem B2166749 : Blo 424774 2166749 := bstep (se 3 (by rfl) ⟨406265, by rfl⟩ : syracuseStep 2166749 = 812531) B812531
theorem B1151111 : Blo 424774 1151111 := bstep (se 1 (by rfl) ⟨863333, by rfl⟩ : syracuseStep 1151111 = 1726667) B1726667
theorem B2167073 : Blo 424774 2167073 := bstep (se 2 (by rfl) ⟨812652, by rfl⟩ : syracuseStep 2167073 = 1625305) B1625305
theorem B1216883 : Blo 424774 1216883 := bstep (se 1 (by rfl) ⟨912662, by rfl⟩ : syracuseStep 1216883 = 1825325) B1825325
theorem B561655 : Blo 424774 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B1446443 : Blo 424774 1446443 := bstep (se 1 (by rfl) ⟨1084832, by rfl⟩ : syracuseStep 1446443 = 2169665) B2169665
theorem B3707459 : Blo 424774 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B1217339 : Blo 424774 1217339 := bstep (se 1 (by rfl) ⟨913004, by rfl⟩ : syracuseStep 1217339 = 1826009) B1826009
theorem B463675 : Blo 424774 463675 := bstep (se 1 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 463675 = 695513) B695513
theorem B1643417 : Blo 424774 1643417 := bstep (se 2 (by rfl) ⟨616281, by rfl⟩ : syracuseStep 1643417 = 1232563) B1232563
theorem B4101293 : Blo 424774 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B2168045 : Blo 424774 2168045 := bstep (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) B813017
theorem B1218091 : Blo 424774 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B956051 : Blo 424774 956051 := bstep (se 1 (by rfl) ⟨717038, by rfl⟩ : syracuseStep 956051 = 1434077) B1434077
theorem B956105 : Blo 424774 956105 := bstep (se 2 (by rfl) ⟨358539, by rfl⟩ : syracuseStep 956105 = 717079) B717079
theorem B1152797 : Blo 424774 1152797 := bstep (se 3 (by rfl) ⟨216149, by rfl⟩ : syracuseStep 1152797 = 432299) B432299
theorem B1021739 : Blo 424774 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B1218365 : Blo 424774 1218365 := bstep (se 3 (by rfl) ⟨228443, by rfl⟩ : syracuseStep 1218365 = 456887) B456887
theorem B923663 : Blo 424774 923663 := bstep (se 1 (by rfl) ⟨692747, by rfl⟩ : syracuseStep 923663 = 1385495) B1385495
theorem B2168855 : Blo 424774 2168855 := bstep (se 1 (by rfl) ⟨1626641, by rfl⟩ : syracuseStep 2168855 = 3253283) B3253283
theorem B1317235 : Blo 424774 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B956807 : Blo 424774 956807 := bstep (se 1 (by rfl) ⟨717605, by rfl⟩ : syracuseStep 956807 = 1435211) B1435211
theorem B956987 : Blo 424774 956987 := bstep (se 1 (by rfl) ⟨717740, by rfl⟩ : syracuseStep 956987 = 1435481) B1435481
theorem B1219207 : Blo 424774 1219207 := bstep (se 1 (by rfl) ⟨914405, by rfl⟩ : syracuseStep 1219207 = 1828811) B1828811
theorem B957113 : Blo 424774 957113 := bstep (se 2 (by rfl) ⟨358917, by rfl⟩ : syracuseStep 957113 = 717835) B717835
theorem B4397975 : Blo 424774 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B1219481 : Blo 424774 1219481 := bstep (se 2 (by rfl) ⟨457305, by rfl⟩ : syracuseStep 1219481 = 914611) B914611
theorem B957455 : Blo 424774 957455 := bstep (se 1 (by rfl) ⟨718091, by rfl⟩ : syracuseStep 957455 = 1436183) B1436183
theorem B957473 : Blo 424774 957473 := bstep (se 2 (by rfl) ⟨359052, by rfl⟩ : syracuseStep 957473 = 718105) B718105
theorem B4365373 : Blo 424774 4365373 := bstep (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) B1637015
theorem B957815 : Blo 424774 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B3317201 : Blo 424774 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B2301443 : Blo 424774 2301443 := bstep (se 1 (by rfl) ⟨1726082, by rfl⟩ : syracuseStep 2301443 = 3452165) B3452165
theorem B2465291 : Blo 424774 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B957995 : Blo 424774 957995 := bstep (se 1 (by rfl) ⟨718496, by rfl⟩ : syracuseStep 957995 = 1436993) B1436993
theorem B1613627 : Blo 424774 1613627 := bstep (se 1 (by rfl) ⟨1210220, by rfl⟩ : syracuseStep 1613627 = 2420441) B2420441
theorem B958355 : Blo 424774 958355 := bstep (se 1 (by rfl) ⟨718766, by rfl⟩ : syracuseStep 958355 = 1437533) B1437533
theorem B958409 : Blo 424774 958409 := bstep (se 2 (by rfl) ⟨359403, by rfl⟩ : syracuseStep 958409 = 718807) B718807
theorem B1220609 : Blo 424774 1220609 := bstep (se 2 (by rfl) ⟨457728, by rfl⟩ : syracuseStep 1220609 = 915457) B915457
theorem B4104215 : Blo 424774 4104215 := bstep (se 1 (by rfl) ⟨3078161, by rfl⟩ : syracuseStep 4104215 = 6156323) B6156323
theorem B3252311 : Blo 424774 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B1614113 : Blo 424774 1614113 := bstep (se 2 (by rfl) ⟨605292, by rfl⟩ : syracuseStep 1614113 = 1210585) B1210585
theorem B729479 : Blo 424774 729479 := bstep (se 1 (by rfl) ⟨547109, by rfl⟩ : syracuseStep 729479 = 1094219) B1094219
theorem B959111 : Blo 424774 959111 := bstep (se 1 (by rfl) ⟨719333, by rfl⟩ : syracuseStep 959111 = 1438667) B1438667
theorem B959291 : Blo 424774 959291 := bstep (se 1 (by rfl) ⟨719468, by rfl⟩ : syracuseStep 959291 = 1438937) B1438937
theorem B959417 : Blo 424774 959417 := bstep (se 2 (by rfl) ⟨359781, by rfl⟩ : syracuseStep 959417 = 719563) B719563
theorem B1024969 : Blo 424774 1024969 := bstep (se 2 (by rfl) ⟨384363, by rfl⟩ : syracuseStep 1024969 = 768727) B768727
theorem B2433995 : Blo 424774 2433995 := bstep (se 1 (by rfl) ⟨1825496, by rfl⟩ : syracuseStep 2433995 = 3650993) B3650993
theorem B1615085 : Blo 424774 1615085 := bstep (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) B605657
theorem B959759 : Blo 424774 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B959777 : Blo 424774 959777 := bstep (se 2 (by rfl) ⟨359916, by rfl⟩ : syracuseStep 959777 = 719833) B719833
theorem B1615403 : Blo 424774 1615403 := bstep (se 1 (by rfl) ⟨1211552, by rfl⟩ : syracuseStep 1615403 = 2423105) B2423105
theorem B960119 : Blo 424774 960119 := bstep (se 1 (by rfl) ⟨720089, by rfl⟩ : syracuseStep 960119 = 1440179) B1440179
theorem B3679937 : Blo 424774 3679937 := bstep (se 2 (by rfl) ⟨1379976, by rfl⟩ : syracuseStep 3679937 = 2759953) B2759953
theorem B4597519 : Blo 424774 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B2303777 : Blo 424774 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B960299 : Blo 424774 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B1025939 : Blo 424774 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B960659 : Blo 424774 960659 := bstep (se 1 (by rfl) ⟨720494, by rfl⟩ : syracuseStep 960659 = 1440989) B1440989
theorem B960713 : Blo 424774 960713 := bstep (se 2 (by rfl) ⟨360267, by rfl⟩ : syracuseStep 960713 = 720535) B720535
theorem B829739 : Blo 424774 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B4696379 : Blo 424774 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B5483051 : Blo 424774 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B961415 : Blo 424774 961415 := bstep (se 1 (by rfl) ⟨721061, by rfl⟩ : syracuseStep 961415 = 1442123) B1442123
theorem B961595 : Blo 424774 961595 := bstep (se 1 (by rfl) ⟨721196, by rfl⟩ : syracuseStep 961595 = 1442393) B1442393
theorem B1158203 : Blo 424774 1158203 := bstep (se 1 (by rfl) ⟨868652, by rfl⟩ : syracuseStep 1158203 = 1737305) B1737305
theorem B961721 : Blo 424774 961721 := bstep (se 2 (by rfl) ⟨360645, by rfl⟩ : syracuseStep 961721 = 721291) B721291
theorem B962063 : Blo 424774 962063 := bstep (se 1 (by rfl) ⟨721547, by rfl⟩ : syracuseStep 962063 = 1443095) B1443095
theorem B962081 : Blo 424774 962081 := bstep (se 2 (by rfl) ⟨360780, by rfl⟩ : syracuseStep 962081 = 721561) B721561
theorem B2076353 : Blo 424774 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B962423 : Blo 424774 962423 := bstep (se 1 (by rfl) ⟨721817, by rfl⟩ : syracuseStep 962423 = 1443635) B1443635
theorem B962603 : Blo 424774 962603 := bstep (se 1 (by rfl) ⟨721952, by rfl⟩ : syracuseStep 962603 = 1443905) B1443905
theorem B3321917 : Blo 424774 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B733303 : Blo 424774 733303 := bstep (se 1 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 733303 = 1099955) B1099955
theorem B962963 : Blo 424774 962963 := bstep (se 1 (by rfl) ⟨722222, by rfl⟩ : syracuseStep 962963 = 1444445) B1444445
theorem B963017 : Blo 424774 963017 := bstep (se 2 (by rfl) ⟨361131, by rfl⟩ : syracuseStep 963017 = 722263) B722263
theorem B4862429 : Blo 424774 4862429 := bstep (se 3 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 4862429 = 1823411) B1823411
theorem B537607 : Blo 424774 537607 := bstep (se 1 (by rfl) ⟨403205, by rfl⟩ : syracuseStep 537607 = 806411) B806411
theorem B1618973 : Blo 424774 1618973 := bstep (se 3 (by rfl) ⟨303557, by rfl⟩ : syracuseStep 1618973 = 607115) B607115
theorem B1618987 : Blo 424774 1618987 := bstep (se 1 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 1618987 = 2428481) B2428481
theorem B1094699 : Blo 424774 1094699 := bstep (se 1 (by rfl) ⟨821024, by rfl⟩ : syracuseStep 1094699 = 1642049) B1642049
theorem B963719 : Blo 424774 963719 := bstep (se 1 (by rfl) ⟨722789, by rfl⟩ : syracuseStep 963719 = 1445579) B1445579
theorem B963899 : Blo 424774 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B6174083 : Blo 424774 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B964025 : Blo 424774 964025 := bstep (se 2 (by rfl) ⟨361509, by rfl⟩ : syracuseStep 964025 = 723019) B723019
theorem B538103 : Blo 424774 538103 := bstep (se 1 (by rfl) ⟨403577, by rfl⟩ : syracuseStep 538103 = 807155) B807155
theorem B538255 : Blo 424774 538255 := bstep (se 1 (by rfl) ⟨403691, by rfl⟩ : syracuseStep 538255 = 807383) B807383
theorem B865993 : Blo 424774 865993 := bstep (se 2 (by rfl) ⟨324747, by rfl⟩ : syracuseStep 865993 = 649495) B649495
theorem B964367 : Blo 424774 964367 := bstep (se 1 (by rfl) ⟨723275, by rfl⟩ : syracuseStep 964367 = 1446551) B1446551
theorem B964385 : Blo 424774 964385 := bstep (se 2 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 964385 = 723289) B723289
theorem B538427 : Blo 424774 538427 := bstep (se 1 (by rfl) ⟨403820, by rfl⟩ : syracuseStep 538427 = 807641) B807641
theorem B964727 : Blo 424774 964727 := bstep (se 1 (by rfl) ⟨723545, by rfl⟩ : syracuseStep 964727 = 1447091) B1447091
theorem B637175 : Blo 424774 637175 := bstep (se 1 (by rfl) ⟨477881, by rfl⟩ : syracuseStep 637175 = 955763) B955763
theorem B637199 : Blo 424774 637199 := bstep (se 1 (by rfl) ⟨477899, by rfl⟩ : syracuseStep 637199 = 955799) B955799
theorem B637241 : Blo 424774 637241 := bstep (se 2 (by rfl) ⟨238965, by rfl⟩ : syracuseStep 637241 = 477931) B477931
theorem B637319 : Blo 424774 637319 := bstep (se 1 (by rfl) ⟨477989, by rfl⟩ : syracuseStep 637319 = 955979) B955979
theorem B637355 : Blo 424774 637355 := bstep (se 1 (by rfl) ⟨478016, by rfl⟩ : syracuseStep 637355 = 956033) B956033
theorem B637385 : Blo 424774 637385 := bstep (se 2 (by rfl) ⟨239019, by rfl⟩ : syracuseStep 637385 = 478039) B478039
theorem B637499 : Blo 424774 637499 := bstep (se 1 (by rfl) ⟨478124, by rfl⟩ : syracuseStep 637499 = 956249) B956249
theorem B637559 : Blo 424774 637559 := bstep (se 1 (by rfl) ⟨478169, by rfl⟩ : syracuseStep 637559 = 956339) B956339
theorem B1227383 : Blo 424774 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B768647 : Blo 424774 768647 := bstep (se 1 (by rfl) ⟨576485, by rfl⟩ : syracuseStep 768647 = 1152971) B1152971
theorem B637583 : Blo 424774 637583 := bstep (se 1 (by rfl) ⟨478187, by rfl⟩ : syracuseStep 637583 = 956375) B956375
theorem B637625 : Blo 424774 637625 := bstep (se 2 (by rfl) ⟨239109, by rfl⟩ : syracuseStep 637625 = 478219) B478219
theorem B637703 : Blo 424774 637703 := bstep (se 1 (by rfl) ⟨478277, by rfl⟩ : syracuseStep 637703 = 956555) B956555
theorem B539399 : Blo 424774 539399 := bstep (se 1 (by rfl) ⟨404549, by rfl⟩ : syracuseStep 539399 = 809099) B809099
theorem B637739 : Blo 424774 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B637769 : Blo 424774 637769 := bstep (se 2 (by rfl) ⟨239163, by rfl⟩ : syracuseStep 637769 = 478327) B478327
theorem B637883 : Blo 424774 637883 := bstep (se 1 (by rfl) ⟨478412, by rfl⟩ : syracuseStep 637883 = 956825) B956825
theorem B2440145 : Blo 424774 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B637943 : Blo 424774 637943 := bstep (se 1 (by rfl) ⟨478457, by rfl⟩ : syracuseStep 637943 = 956915) B956915
theorem B637967 : Blo 424774 637967 := bstep (se 1 (by rfl) ⟨478475, by rfl⟩ : syracuseStep 637967 = 956951) B956951
theorem B638009 : Blo 424774 638009 := bstep (se 2 (by rfl) ⟨239253, by rfl⟩ : syracuseStep 638009 = 478507) B478507
theorem B1293371 : Blo 424774 1293371 := bstep (se 1 (by rfl) ⟨970028, by rfl⟩ : syracuseStep 1293371 = 1940057) B1940057
theorem B6929495 : Blo 424774 6929495 := bstep (se 1 (by rfl) ⟨5197121, by rfl⟩ : syracuseStep 6929495 = 10394243) B10394243
theorem B638087 : Blo 424774 638087 := bstep (se 1 (by rfl) ⟨478565, by rfl⟩ : syracuseStep 638087 = 957131) B957131
theorem B638123 : Blo 424774 638123 := bstep (se 1 (by rfl) ⟨478592, by rfl⟩ : syracuseStep 638123 = 957185) B957185
theorem B2047169 : Blo 424774 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B638153 : Blo 424774 638153 := bstep (se 2 (by rfl) ⟨239307, by rfl⟩ : syracuseStep 638153 = 478615) B478615
theorem B4668661 : Blo 424774 4668661 := bstep (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) B437687
theorem B1457423 : Blo 424774 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B2047265 : Blo 424774 2047265 := bstep (se 2 (by rfl) ⟨767724, by rfl⟩ : syracuseStep 2047265 = 1535449) B1535449
theorem B638267 : Blo 424774 638267 := bstep (se 1 (by rfl) ⟨478700, by rfl⟩ : syracuseStep 638267 = 957401) B957401
theorem B638327 : Blo 424774 638327 := bstep (se 1 (by rfl) ⟨478745, by rfl⟩ : syracuseStep 638327 = 957491) B957491
theorem B638351 : Blo 424774 638351 := bstep (se 1 (by rfl) ⟨478763, by rfl⟩ : syracuseStep 638351 = 957527) B957527
theorem B540047 : Blo 424774 540047 := bstep (se 1 (by rfl) ⟨405035, by rfl⟩ : syracuseStep 540047 = 810071) B810071
theorem B2440601 : Blo 424774 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B638393 : Blo 424774 638393 := bstep (se 2 (by rfl) ⟨239397, by rfl⟩ : syracuseStep 638393 = 478795) B478795
theorem B1818065 : Blo 424774 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B638471 : Blo 424774 638471 := bstep (se 1 (by rfl) ⟨478853, by rfl⟩ : syracuseStep 638471 = 957707) B957707
theorem B638507 : Blo 424774 638507 := bstep (se 1 (by rfl) ⟨478880, by rfl⟩ : syracuseStep 638507 = 957761) B957761
theorem B638537 : Blo 424774 638537 := bstep (se 2 (by rfl) ⟨239451, by rfl⟩ : syracuseStep 638537 = 478903) B478903
theorem B638651 : Blo 424774 638651 := bstep (se 1 (by rfl) ⟨478988, by rfl⟩ : syracuseStep 638651 = 957977) B957977
theorem B638711 : Blo 424774 638711 := bstep (se 1 (by rfl) ⟨479033, by rfl⟩ : syracuseStep 638711 = 958067) B958067
theorem B638735 : Blo 424774 638735 := bstep (se 1 (by rfl) ⟨479051, by rfl⟩ : syracuseStep 638735 = 958103) B958103
theorem B638777 : Blo 424774 638777 := bstep (se 2 (by rfl) ⟨239541, by rfl⟩ : syracuseStep 638777 = 479083) B479083
theorem B638855 : Blo 424774 638855 := bstep (se 1 (by rfl) ⟨479141, by rfl⟩ : syracuseStep 638855 = 958283) B958283
theorem B638891 : Blo 424774 638891 := bstep (se 1 (by rfl) ⟨479168, by rfl⟩ : syracuseStep 638891 = 958337) B958337
theorem B638921 : Blo 424774 638921 := bstep (se 2 (by rfl) ⟨239595, by rfl⟩ : syracuseStep 638921 = 479191) B479191
theorem B639035 : Blo 424774 639035 := bstep (se 1 (by rfl) ⟨479276, by rfl⟩ : syracuseStep 639035 = 958553) B958553
theorem B639095 : Blo 424774 639095 := bstep (se 1 (by rfl) ⟨479321, by rfl⟩ : syracuseStep 639095 = 958643) B958643
theorem B639119 : Blo 424774 639119 := bstep (se 1 (by rfl) ⟨479339, by rfl⟩ : syracuseStep 639119 = 958679) B958679
theorem B639161 : Blo 424774 639161 := bstep (se 2 (by rfl) ⟨239685, by rfl⟩ : syracuseStep 639161 = 479371) B479371
theorem B639239 : Blo 424774 639239 := bstep (se 1 (by rfl) ⟨479429, by rfl⟩ : syracuseStep 639239 = 958859) B958859
theorem B639275 : Blo 424774 639275 := bstep (se 1 (by rfl) ⟨479456, by rfl⟩ : syracuseStep 639275 = 958913) B958913
theorem B606523 : Blo 424774 606523 := bstep (se 1 (by rfl) ⟨454892, by rfl⟩ : syracuseStep 606523 = 909785) B909785
theorem B639305 : Blo 424774 639305 := bstep (se 2 (by rfl) ⟨239739, by rfl⟩ : syracuseStep 639305 = 479479) B479479
theorem B639419 : Blo 424774 639419 := bstep (se 1 (by rfl) ⟨479564, by rfl⟩ : syracuseStep 639419 = 959129) B959129
theorem B2736605 : Blo 424774 2736605 := bstep (se 3 (by rfl) ⟨513113, by rfl⟩ : syracuseStep 2736605 = 1026227) B1026227
theorem B639479 : Blo 424774 639479 := bstep (se 1 (by rfl) ⟨479609, by rfl⟩ : syracuseStep 639479 = 959219) B959219
theorem B639503 : Blo 424774 639503 := bstep (se 1 (by rfl) ⟨479627, by rfl⟩ : syracuseStep 639503 = 959255) B959255
theorem B639545 : Blo 424774 639545 := bstep (se 2 (by rfl) ⟨239829, by rfl⟩ : syracuseStep 639545 = 479659) B479659
theorem B7291457 : Blo 424774 7291457 := bstep (se 2 (by rfl) ⟨2734296, by rfl⟩ : syracuseStep 7291457 = 5468593) B5468593
theorem B639623 : Blo 424774 639623 := bstep (se 1 (by rfl) ⟨479717, by rfl⟩ : syracuseStep 639623 = 959435) B959435
theorem B639659 : Blo 424774 639659 := bstep (se 1 (by rfl) ⟨479744, by rfl⟩ : syracuseStep 639659 = 959489) B959489
theorem B9814709 : Blo 424774 9814709 := bstep (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) B920129
theorem B574139 : Blo 424774 574139 := bstep (se 1 (by rfl) ⟨430604, by rfl⟩ : syracuseStep 574139 = 861209) B861209
theorem B639689 : Blo 424774 639689 := bstep (se 2 (by rfl) ⟨239883, by rfl⟩ : syracuseStep 639689 = 479767) B479767
theorem B639803 : Blo 424774 639803 := bstep (se 1 (by rfl) ⟨479852, by rfl⟩ : syracuseStep 639803 = 959705) B959705
theorem B639863 : Blo 424774 639863 := bstep (se 1 (by rfl) ⟨479897, by rfl⟩ : syracuseStep 639863 = 959795) B959795
theorem B639887 : Blo 424774 639887 := bstep (se 1 (by rfl) ⟨479915, by rfl⟩ : syracuseStep 639887 = 959831) B959831
theorem B1098649 : Blo 424774 1098649 := bstep (se 2 (by rfl) ⟨411993, by rfl⟩ : syracuseStep 1098649 = 823987) B823987
theorem B639929 : Blo 424774 639929 := bstep (se 2 (by rfl) ⟨239973, by rfl⟩ : syracuseStep 639929 = 479947) B479947
theorem B607223 : Blo 424774 607223 := bstep (se 1 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 607223 = 910835) B910835
theorem B640007 : Blo 424774 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B640043 : Blo 424774 640043 := bstep (se 1 (by rfl) ⟨480032, by rfl⟩ : syracuseStep 640043 = 960065) B960065
theorem B640073 : Blo 424774 640073 := bstep (se 2 (by rfl) ⟨240027, by rfl⟩ : syracuseStep 640073 = 480055) B480055
theorem B640187 : Blo 424774 640187 := bstep (se 1 (by rfl) ⟨480140, by rfl⟩ : syracuseStep 640187 = 960281) B960281
theorem B640247 : Blo 424774 640247 := bstep (se 1 (by rfl) ⟨480185, by rfl⟩ : syracuseStep 640247 = 960371) B960371
theorem B640271 : Blo 424774 640271 := bstep (se 1 (by rfl) ⟨480203, by rfl⟩ : syracuseStep 640271 = 960407) B960407
theorem B574777 : Blo 424774 574777 := bstep (se 2 (by rfl) ⟨215541, by rfl⟩ : syracuseStep 574777 = 431083) B431083
theorem B640313 : Blo 424774 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B640391 : Blo 424774 640391 := bstep (se 1 (by rfl) ⟨480293, by rfl⟩ : syracuseStep 640391 = 960587) B960587
theorem B640427 : Blo 424774 640427 := bstep (se 1 (by rfl) ⟨480320, by rfl⟩ : syracuseStep 640427 = 960641) B960641
theorem B640457 : Blo 424774 640457 := bstep (se 2 (by rfl) ⟨240171, by rfl⟩ : syracuseStep 640457 = 480343) B480343
theorem B640571 : Blo 424774 640571 := bstep (se 1 (by rfl) ⟨480428, by rfl⟩ : syracuseStep 640571 = 960857) B960857
theorem B640631 : Blo 424774 640631 := bstep (se 1 (by rfl) ⟨480473, by rfl⟩ : syracuseStep 640631 = 960947) B960947
theorem B640655 : Blo 424774 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B10798771 : Blo 424774 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B640697 : Blo 424774 640697 := bstep (se 2 (by rfl) ⟨240261, by rfl⟩ : syracuseStep 640697 = 480523) B480523
theorem B640775 : Blo 424774 640775 := bstep (se 1 (by rfl) ⟨480581, by rfl⟩ : syracuseStep 640775 = 961163) B961163
theorem B1296157 : Blo 424774 1296157 := bstep (se 3 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 1296157 = 486059) B486059
theorem B640811 : Blo 424774 640811 := bstep (se 1 (by rfl) ⟨480608, by rfl⟩ : syracuseStep 640811 = 961217) B961217
theorem B640841 : Blo 424774 640841 := bstep (se 2 (by rfl) ⟨240315, by rfl⟩ : syracuseStep 640841 = 480631) B480631
theorem B2312081 : Blo 424774 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B640955 : Blo 424774 640955 := bstep (se 1 (by rfl) ⟨480716, by rfl⟩ : syracuseStep 640955 = 961433) B961433
theorem B641015 : Blo 424774 641015 := bstep (se 1 (by rfl) ⟨480761, by rfl⟩ : syracuseStep 641015 = 961523) B961523
theorem B641039 : Blo 424774 641039 := bstep (se 1 (by rfl) ⟨480779, by rfl⟩ : syracuseStep 641039 = 961559) B961559
theorem B641081 : Blo 424774 641081 := bstep (se 2 (by rfl) ⟨240405, by rfl⟩ : syracuseStep 641081 = 480811) B480811
theorem B1624151 : Blo 424774 1624151 := bstep (se 1 (by rfl) ⟨1218113, by rfl⟩ : syracuseStep 1624151 = 2436227) B2436227
theorem B641159 : Blo 424774 641159 := bstep (se 1 (by rfl) ⟨480869, by rfl⟩ : syracuseStep 641159 = 961739) B961739
theorem B641195 : Blo 424774 641195 := bstep (se 1 (by rfl) ⟨480896, by rfl⟩ : syracuseStep 641195 = 961793) B961793
theorem B3360941 : Blo 424774 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B641225 : Blo 424774 641225 := bstep (se 2 (by rfl) ⟨240459, by rfl⟩ : syracuseStep 641225 = 480919) B480919
theorem B1296641 : Blo 424774 1296641 := bstep (se 2 (by rfl) ⟨486240, by rfl⟩ : syracuseStep 1296641 = 972481) B972481
theorem B1820987 : Blo 424774 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B641339 : Blo 424774 641339 := bstep (se 1 (by rfl) ⟨481004, by rfl⟩ : syracuseStep 641339 = 962009) B962009
theorem B641399 : Blo 424774 641399 := bstep (se 1 (by rfl) ⟨481049, by rfl⟩ : syracuseStep 641399 = 962099) B962099
theorem B608647 : Blo 424774 608647 := bstep (se 1 (by rfl) ⟨456485, by rfl⟩ : syracuseStep 608647 = 912971) B912971
theorem B641423 : Blo 424774 641423 := bstep (se 1 (by rfl) ⟨481067, by rfl⟩ : syracuseStep 641423 = 962135) B962135
theorem B641465 : Blo 424774 641465 := bstep (se 2 (by rfl) ⟨240549, by rfl⟩ : syracuseStep 641465 = 481099) B481099
theorem B641543 : Blo 424774 641543 := bstep (se 1 (by rfl) ⟨481157, by rfl⟩ : syracuseStep 641543 = 962315) B962315
theorem B641579 : Blo 424774 641579 := bstep (se 1 (by rfl) ⟨481184, by rfl⟩ : syracuseStep 641579 = 962369) B962369
theorem B1624637 : Blo 424774 1624637 := bstep (se 3 (by rfl) ⟨304619, by rfl⟩ : syracuseStep 1624637 = 609239) B609239
theorem B2345539 : Blo 424774 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B641609 : Blo 424774 641609 := bstep (se 2 (by rfl) ⟨240603, by rfl⟩ : syracuseStep 641609 = 481207) B481207
theorem B9226871 : Blo 424774 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B641723 : Blo 424774 641723 := bstep (se 1 (by rfl) ⟨481292, by rfl⟩ : syracuseStep 641723 = 962585) B962585
theorem B641783 : Blo 424774 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B477967 : Blo 424774 477967 := bstep (se 1 (by rfl) ⟨358475, by rfl⟩ : syracuseStep 477967 = 716951) B716951
theorem B641807 : Blo 424774 641807 := bstep (se 1 (by rfl) ⟨481355, by rfl⟩ : syracuseStep 641807 = 962711) B962711
theorem B3296015 : Blo 424774 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B641849 : Blo 424774 641849 := bstep (se 2 (by rfl) ⟨240693, by rfl⟩ : syracuseStep 641849 = 481387) B481387
theorem B1329979 : Blo 424774 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B641927 : Blo 424774 641927 := bstep (se 1 (by rfl) ⟨481445, by rfl⟩ : syracuseStep 641927 = 962891) B962891
theorem B641963 : Blo 424774 641963 := bstep (se 1 (by rfl) ⟨481472, by rfl⟩ : syracuseStep 641963 = 962945) B962945
theorem B609211 : Blo 424774 609211 := bstep (se 1 (by rfl) ⟨456908, by rfl⟩ : syracuseStep 609211 = 913817) B913817
theorem B641993 : Blo 424774 641993 := bstep (se 2 (by rfl) ⟨240747, by rfl⟩ : syracuseStep 641993 = 481495) B481495
theorem B642107 : Blo 424774 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B642167 : Blo 424774 642167 := bstep (se 1 (by rfl) ⟨481625, by rfl⟩ : syracuseStep 642167 = 963251) B963251
theorem B642191 : Blo 424774 642191 := bstep (se 1 (by rfl) ⟨481643, by rfl⟩ : syracuseStep 642191 = 963287) B963287
theorem B642233 : Blo 424774 642233 := bstep (se 2 (by rfl) ⟨240837, by rfl⟩ : syracuseStep 642233 = 481675) B481675
theorem B478471 : Blo 424774 478471 := bstep (se 1 (by rfl) ⟨358853, by rfl⟩ : syracuseStep 478471 = 717707) B717707
theorem B642311 : Blo 424774 642311 := bstep (se 1 (by rfl) ⟨481733, by rfl⟩ : syracuseStep 642311 = 963467) B963467
theorem B1723681 : Blo 424774 1723681 := bstep (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) B1292761
theorem B642347 : Blo 424774 642347 := bstep (se 1 (by rfl) ⟨481760, by rfl⟩ : syracuseStep 642347 = 963521) B963521
theorem B642377 : Blo 424774 642377 := bstep (se 2 (by rfl) ⟨240891, by rfl⟩ : syracuseStep 642377 = 481783) B481783
theorem B478651 : Blo 424774 478651 := bstep (se 1 (by rfl) ⟨358988, by rfl⟩ : syracuseStep 478651 = 717977) B717977
theorem B642491 : Blo 424774 642491 := bstep (se 1 (by rfl) ⟨481868, by rfl⟩ : syracuseStep 642491 = 963737) B963737
theorem B2969041 : Blo 424774 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B642551 : Blo 424774 642551 := bstep (se 1 (by rfl) ⟨481913, by rfl⟩ : syracuseStep 642551 = 963827) B963827
theorem B642575 : Blo 424774 642575 := bstep (se 1 (by rfl) ⟨481931, by rfl⟩ : syracuseStep 642575 = 963863) B963863
theorem B642617 : Blo 424774 642617 := bstep (se 2 (by rfl) ⟨240981, by rfl⟩ : syracuseStep 642617 = 481963) B481963
theorem B642695 : Blo 424774 642695 := bstep (se 1 (by rfl) ⟨482021, by rfl⟩ : syracuseStep 642695 = 964043) B964043
theorem B642731 : Blo 424774 642731 := bstep (se 1 (by rfl) ⟨482048, by rfl⟩ : syracuseStep 642731 = 964097) B964097
theorem B642761 : Blo 424774 642761 := bstep (se 2 (by rfl) ⟨241035, by rfl⟩ : syracuseStep 642761 = 482071) B482071
theorem B806699 : Blo 424774 806699 := bstep (se 1 (by rfl) ⟨605024, by rfl⟩ : syracuseStep 806699 = 1210049) B1210049
theorem B610105 : Blo 424774 610105 := bstep (se 2 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 610105 = 457579) B457579
theorem B642875 : Blo 424774 642875 := bstep (se 1 (by rfl) ⟨482156, by rfl⟩ : syracuseStep 642875 = 964313) B964313
theorem B642935 : Blo 424774 642935 := bstep (se 1 (by rfl) ⟨482201, by rfl⟩ : syracuseStep 642935 = 964403) B964403
theorem B479119 : Blo 424774 479119 := bstep (se 1 (by rfl) ⟨359339, by rfl⟩ : syracuseStep 479119 = 718679) B718679
theorem B642959 : Blo 424774 642959 := bstep (se 1 (by rfl) ⟨482219, by rfl⟩ : syracuseStep 642959 = 964439) B964439
theorem B643001 : Blo 424774 643001 := bstep (se 2 (by rfl) ⟨241125, by rfl⟩ : syracuseStep 643001 = 482251) B482251
theorem B8212427 : Blo 424774 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B1626065 : Blo 424774 1626065 := bstep (se 2 (by rfl) ⟨609774, by rfl⟩ : syracuseStep 1626065 = 1219549) B1219549
theorem B643079 : Blo 424774 643079 := bstep (se 1 (by rfl) ⟨482309, by rfl⟩ : syracuseStep 643079 = 964619) B964619
theorem B1822763 : Blo 424774 1822763 := bstep (se 1 (by rfl) ⟨1367072, by rfl⟩ : syracuseStep 1822763 = 2734145) B2734145
theorem B643115 : Blo 424774 643115 := bstep (se 1 (by rfl) ⟨482336, by rfl⟩ : syracuseStep 643115 = 964673) B964673
theorem B643145 : Blo 424774 643145 := bstep (se 2 (by rfl) ⟨241179, by rfl⟩ : syracuseStep 643145 = 482359) B482359
theorem B545015 : Blo 424774 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B577783 : Blo 424774 577783 := bstep (se 1 (by rfl) ⟨433337, by rfl⟩ : syracuseStep 577783 = 866675) B866675
theorem B479623 : Blo 424774 479623 := bstep (se 1 (by rfl) ⟨359717, by rfl⟩ : syracuseStep 479623 = 719435) B719435
theorem B1036745 : Blo 424774 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B479803 : Blo 424774 479803 := bstep (se 1 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 479803 = 719705) B719705
theorem B5198681 : Blo 424774 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B1364921 : Blo 424774 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B8180747 : Blo 424774 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B480271 : Blo 424774 480271 := bstep (se 1 (by rfl) ⟨360203, by rfl⟩ : syracuseStep 480271 = 720407) B720407
theorem B4150561 : Blo 424774 4150561 := bstep (se 2 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 4150561 = 3112921) B3112921
theorem B808393 : Blo 424774 808393 := bstep (se 2 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 808393 = 606295) B606295
theorem B480775 : Blo 424774 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B3233357 : Blo 424774 3233357 := bstep (se 3 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 3233357 = 1212509) B1212509
theorem B1627735 : Blo 424774 1627735 := bstep (se 1 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 1627735 = 2441603) B2441603
theorem B480955 : Blo 424774 480955 := bstep (se 1 (by rfl) ⟨360716, by rfl⟩ : syracuseStep 480955 = 721433) B721433
theorem B481423 : Blo 424774 481423 := bstep (se 1 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 481423 = 722135) B722135
theorem B973001 : Blo 424774 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B514603 : Blo 424774 514603 := bstep (se 1 (by rfl) ⟨385952, by rfl⟩ : syracuseStep 514603 = 771905) B771905
theorem B481927 : Blo 424774 481927 := bstep (se 1 (by rfl) ⟨361445, by rfl⟩ : syracuseStep 481927 = 722891) B722891
theorem B4446899 : Blo 424774 4446899 := bstep (se 1 (by rfl) ⟨3335174, by rfl⟩ : syracuseStep 4446899 = 6670349) B6670349
theorem B2743091 : Blo 424774 2743091 := bstep (se 1 (by rfl) ⟨2057318, by rfl⟩ : syracuseStep 2743091 = 4114637) B4114637
theorem B482107 : Blo 424774 482107 := bstep (se 1 (by rfl) ⟨361580, by rfl⟩ : syracuseStep 482107 = 723161) B723161
theorem B810299 : Blo 424774 810299 := bstep (se 1 (by rfl) ⟨607724, by rfl⟩ : syracuseStep 810299 = 1215449) B1215449
theorem B810785 : Blo 424774 810785 := bstep (se 2 (by rfl) ⟨304044, by rfl⟩ : syracuseStep 810785 = 608089) B608089
theorem B1367867 : Blo 424774 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B3235787 : Blo 424774 3235787 := bstep (se 1 (by rfl) ⟨2426840, by rfl⟩ : syracuseStep 3235787 = 4853681) B4853681
theorem B2056259 : Blo 424774 2056259 := bstep (se 1 (by rfl) ⟨1542194, by rfl⟩ : syracuseStep 2056259 = 3084389) B3084389
theorem B811127 : Blo 424774 811127 := bstep (se 1 (by rfl) ⟨608345, by rfl⟩ : syracuseStep 811127 = 1216691) B1216691
theorem B1302713 : Blo 424774 1302713 := bstep (se 2 (by rfl) ⟨488517, by rfl⟩ : syracuseStep 1302713 = 977035) B977035
theorem B1368265 : Blo 424774 1368265 := bstep (se 2 (by rfl) ⟨513099, by rfl⟩ : syracuseStep 1368265 = 1026199) B1026199
theorem B1433915 : Blo 424774 1433915 := bstep (se 1 (by rfl) ⟨1075436, by rfl⟩ : syracuseStep 1433915 = 2150873) B2150873
theorem B647671 : Blo 424774 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B615047 : Blo 424774 615047 := bstep (se 1 (by rfl) ⟨461285, by rfl⟩ : syracuseStep 615047 = 922571) B922571
theorem B1434401 : Blo 424774 1434401 := bstep (se 2 (by rfl) ⟨537900, by rfl⟩ : syracuseStep 1434401 = 1075801) B1075801
theorem B3629873 : Blo 424774 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B2155409 : Blo 424774 2155409 := bstep (se 2 (by rfl) ⟨808278, by rfl⟩ : syracuseStep 2155409 = 1616557) B1616557
theorem B2188595 : Blo 424774 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B1434995 : Blo 424774 1434995 := bstep (se 1 (by rfl) ⟨1076246, by rfl⟩ : syracuseStep 1434995 = 2152493) B2152493
theorem B812729 : Blo 424774 812729 := bstep (se 2 (by rfl) ⟨304773, by rfl⟩ : syracuseStep 812729 = 609547) B609547
theorem B648905 : Blo 424774 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B5334821 : Blo 424774 5334821 := bstep (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) B1000279
theorem B681929 : Blo 424774 681929 := bstep (se 2 (by rfl) ⟨255723, by rfl⟩ : syracuseStep 681929 = 511447) B511447
theorem B5171147 : Blo 424774 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B813071 : Blo 424774 813071 := bstep (se 1 (by rfl) ⟨609803, by rfl⟩ : syracuseStep 813071 = 1219607) B1219607
theorem B1075315 : Blo 424774 1075315 := bstep (se 1 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 1075315 = 1612973) B1612973
theorem B1075457 : Blo 424774 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B682511 : Blo 424774 682511 := bstep (se 1 (by rfl) ⟨511883, by rfl⟩ : syracuseStep 682511 = 1023767) B1023767
theorem B1075913 : Blo 424774 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B813883 : Blo 424774 813883 := bstep (se 1 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 813883 = 1220825) B1220825
theorem B813959 : Blo 424774 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B912313 : Blo 424774 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B2157515 : Blo 424774 2157515 := bstep (se 1 (by rfl) ⟨1618136, by rfl⟩ : syracuseStep 2157515 = 3236273) B3236273
theorem B1076267 : Blo 424774 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B2157839 : Blo 424774 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B8220113 : Blo 424774 8220113 := bstep (se 2 (by rfl) ⟨3082542, by rfl⟩ : syracuseStep 8220113 = 6165085) B6165085
theorem B2420189 : Blo 424774 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B1371659 : Blo 424774 1371659 := bstep (se 1 (by rfl) ⟨1028744, by rfl⟩ : syracuseStep 1371659 = 2057489) B2057489
theorem B2059949 : Blo 424774 2059949 := bstep (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) B772481
theorem B552763 : Blo 424774 552763 := bstep (se 1 (by rfl) ⟨414572, by rfl⟩ : syracuseStep 552763 = 829145) B829145
theorem B1437587 : Blo 424774 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B2813849 : Blo 424774 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1077259 : Blo 424774 1077259 := bstep (se 1 (by rfl) ⟨807944, by rfl⟩ : syracuseStep 1077259 = 1615889) B1615889
theorem B4616203 : Blo 424774 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B716843 : Blo 424774 716843 := bstep (se 1 (by rfl) ⟨537632, by rfl⟩ : syracuseStep 716843 = 1075265) B1075265
theorem B2715709 : Blo 424774 2715709 := bstep (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) B1018391
theorem B1077401 : Blo 424774 1077401 := bstep (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) B808051
theorem B1077563 : Blo 424774 1077563 := bstep (se 1 (by rfl) ⟨808172, by rfl⟩ : syracuseStep 1077563 = 1616345) B1616345
theorem B717241 : Blo 424774 717241 := bstep (se 2 (by rfl) ⟨268965, by rfl⟩ : syracuseStep 717241 = 537931) B537931
theorem B4452893 : Blo 424774 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B913979 : Blo 424774 913979 := bstep (se 1 (by rfl) ⟨685484, by rfl⟩ : syracuseStep 913979 = 1370969) B1370969
theorem B1077907 : Blo 424774 1077907 := bstep (se 1 (by rfl) ⟨808430, by rfl⟩ : syracuseStep 1077907 = 1616861) B1616861
theorem B2159297 : Blo 424774 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B1078049 : Blo 424774 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B717943 : Blo 424774 717943 := bstep (se 1 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 717943 = 1076915) B1076915
theorem B455815 : Blo 424774 455815 := bstep (se 1 (by rfl) ⟨341861, by rfl⟩ : syracuseStep 455815 = 683723) B683723
theorem B3241133 : Blo 424774 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B1438991 : Blo 424774 1438991 := bstep (se 1 (by rfl) ⟨1079243, by rfl⟩ : syracuseStep 1438991 = 2158487) B2158487
theorem B5174545 : Blo 424774 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B718139 : Blo 424774 718139 := bstep (se 1 (by rfl) ⟨538604, by rfl⟩ : syracuseStep 718139 = 1077209) B1077209
theorem B7304579 : Blo 424774 7304579 := bstep (se 1 (by rfl) ⟨5478434, by rfl⟩ : syracuseStep 7304579 = 10956869) B10956869
theorem B1439261 : Blo 424774 1439261 := bstep (se 3 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 1439261 = 539723) B539723
theorem B8451661 : Blo 424774 8451661 := bstep (se 3 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 8451661 = 3169373) B3169373
theorem B718537 : Blo 424774 718537 := bstep (se 2 (by rfl) ⟨269451, by rfl⟩ : syracuseStep 718537 = 538903) B538903
theorem B1079041 : Blo 424774 1079041 := bstep (se 2 (by rfl) ⟨404640, by rfl⟩ : syracuseStep 1079041 = 809281) B809281
theorem B2586401 : Blo 424774 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B1210231 : Blo 424774 1210231 := bstep (se 1 (by rfl) ⟨907673, by rfl⟩ : syracuseStep 1210231 = 1815347) B1815347
theorem B456635 : Blo 424774 456635 := bstep (se 1 (by rfl) ⟨342476, by rfl⟩ : syracuseStep 456635 = 684953) B684953
theorem B2160593 : Blo 424774 2160593 := bstep (se 2 (by rfl) ⟨810222, by rfl⟩ : syracuseStep 2160593 = 1620445) B1620445
theorem B2783243 : Blo 424774 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B915499 : Blo 424774 915499 := bstep (se 1 (by rfl) ⟨686624, by rfl⟩ : syracuseStep 915499 = 1373249) B1373249
theorem B1079639 : Blo 424774 1079639 := bstep (se 1 (by rfl) ⟨809729, by rfl⟩ : syracuseStep 1079639 = 1619459) B1619459
theorem B719239 : Blo 424774 719239 := bstep (se 1 (by rfl) ⟨539429, by rfl⟩ : syracuseStep 719239 = 1078859) B1078859
theorem B1079851 : Blo 424774 1079851 := bstep (se 1 (by rfl) ⟨809888, by rfl⟩ : syracuseStep 1079851 = 1619777) B1619777
theorem B2423357 : Blo 424774 2423357 := bstep (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) B908759
theorem B1538621 : Blo 424774 1538621 := bstep (se 3 (by rfl) ⟨288491, by rfl⟩ : syracuseStep 1538621 = 576983) B576983
theorem B1079993 : Blo 424774 1079993 := bstep (se 2 (by rfl) ⟨404997, by rfl⟩ : syracuseStep 1079993 = 809995) B809995
theorem B7371557 : Blo 424774 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B424839 : Blo 424774 424839 := bstep (se 1 (by rfl) ⟨318629, by rfl⟩ : syracuseStep 424839 = 637259) B637259
theorem B424847 : Blo 424774 424847 := bstep (se 1 (by rfl) ⟨318635, by rfl⟩ : syracuseStep 424847 = 637271) B637271
theorem B1440665 : Blo 424774 1440665 := bstep (se 2 (by rfl) ⟨540249, by rfl⟩ : syracuseStep 1440665 = 1080499) B1080499
theorem B424891 : Blo 424774 424891 := bstep (se 1 (by rfl) ⟨318668, by rfl⟩ : syracuseStep 424891 = 637337) B637337
theorem B424967 : Blo 424774 424967 := bstep (se 1 (by rfl) ⟨318725, by rfl⟩ : syracuseStep 424967 = 637451) B637451
theorem B424975 : Blo 424774 424975 := bstep (se 1 (by rfl) ⟨318731, by rfl⟩ : syracuseStep 424975 = 637463) B637463
theorem B719887 : Blo 424774 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B425019 : Blo 424774 425019 := bstep (se 1 (by rfl) ⟨318764, by rfl⟩ : syracuseStep 425019 = 637529) B637529
theorem B1211507 : Blo 424774 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B425095 : Blo 424774 425095 := bstep (se 1 (by rfl) ⟨318821, by rfl⟩ : syracuseStep 425095 = 637643) B637643
theorem B425103 : Blo 424774 425103 := bstep (se 1 (by rfl) ⟨318827, by rfl⟩ : syracuseStep 425103 = 637655) B637655
theorem B425147 : Blo 424774 425147 := bstep (se 1 (by rfl) ⟨318860, by rfl⟩ : syracuseStep 425147 = 637721) B637721
theorem B425223 : Blo 424774 425223 := bstep (se 1 (by rfl) ⟨318917, by rfl⟩ : syracuseStep 425223 = 637835) B637835
theorem B425231 : Blo 424774 425231 := bstep (se 1 (by rfl) ⟨318923, by rfl⟩ : syracuseStep 425231 = 637847) B637847
theorem B425275 : Blo 424774 425275 := bstep (se 1 (by rfl) ⟨318956, by rfl⟩ : syracuseStep 425275 = 637913) B637913
theorem B1211735 : Blo 424774 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B9239939 : Blo 424774 9239939 := bstep (se 1 (by rfl) ⟨6929954, by rfl⟩ : syracuseStep 9239939 = 13859909) B13859909
theorem B425351 : Blo 424774 425351 := bstep (se 1 (by rfl) ⟨319013, by rfl⟩ : syracuseStep 425351 = 638027) B638027
theorem B425359 : Blo 424774 425359 := bstep (se 1 (by rfl) ⟨319019, by rfl⟩ : syracuseStep 425359 = 638039) B638039
theorem B425403 : Blo 424774 425403 := bstep (se 1 (by rfl) ⟨319052, by rfl⟩ : syracuseStep 425403 = 638105) B638105
theorem B425479 : Blo 424774 425479 := bstep (se 1 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 425479 = 638219) B638219
theorem B425487 : Blo 424774 425487 := bstep (se 1 (by rfl) ⟨319115, by rfl⟩ : syracuseStep 425487 = 638231) B638231
theorem B720427 : Blo 424774 720427 := bstep (se 1 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 720427 = 1080641) B1080641
theorem B3243563 : Blo 424774 3243563 := bstep (se 1 (by rfl) ⟨2432672, by rfl⟩ : syracuseStep 3243563 = 4865345) B4865345
theorem B425531 : Blo 424774 425531 := bstep (se 1 (by rfl) ⟨319148, by rfl⟩ : syracuseStep 425531 = 638297) B638297
theorem B8289869 : Blo 424774 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1441367 : Blo 424774 1441367 := bstep (se 1 (by rfl) ⟨1081025, by rfl⟩ : syracuseStep 1441367 = 2162051) B2162051
theorem B425607 : Blo 424774 425607 := bstep (se 1 (by rfl) ⟨319205, by rfl⟩ : syracuseStep 425607 = 638411) B638411
theorem B425615 : Blo 424774 425615 := bstep (se 1 (by rfl) ⟨319211, by rfl⟩ : syracuseStep 425615 = 638423) B638423
theorem B1080985 : Blo 424774 1080985 := bstep (se 2 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 1080985 = 810739) B810739
theorem B720569 : Blo 424774 720569 := bstep (se 2 (by rfl) ⟨270213, by rfl⟩ : syracuseStep 720569 = 540427) B540427
theorem B425659 : Blo 424774 425659 := bstep (se 1 (by rfl) ⟨319244, by rfl⟩ : syracuseStep 425659 = 638489) B638489
theorem B425735 : Blo 424774 425735 := bstep (se 1 (by rfl) ⟨319301, by rfl⟩ : syracuseStep 425735 = 638603) B638603
theorem B425743 : Blo 424774 425743 := bstep (se 1 (by rfl) ⟨319307, by rfl⟩ : syracuseStep 425743 = 638615) B638615
theorem B425787 : Blo 424774 425787 := bstep (se 1 (by rfl) ⟨319340, by rfl⟩ : syracuseStep 425787 = 638681) B638681
theorem B1081147 : Blo 424774 1081147 := bstep (se 1 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 1081147 = 1621721) B1621721
theorem B425863 : Blo 424774 425863 := bstep (se 1 (by rfl) ⟨319397, by rfl⟩ : syracuseStep 425863 = 638795) B638795
theorem B425871 : Blo 424774 425871 := bstep (se 1 (by rfl) ⟨319403, by rfl⟩ : syracuseStep 425871 = 638807) B638807
theorem B425915 : Blo 424774 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1081289 : Blo 424774 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B1441799 : Blo 424774 1441799 := bstep (se 1 (by rfl) ⟨1081349, by rfl⟩ : syracuseStep 1441799 = 2162699) B2162699
theorem B426023 : Blo 424774 426023 := bstep (se 1 (by rfl) ⟨319517, by rfl⟩ : syracuseStep 426023 = 639035) B639035
theorem B426063 : Blo 424774 426063 := bstep (se 1 (by rfl) ⟨319547, by rfl⟩ : syracuseStep 426063 = 639095) B639095
theorem B426079 : Blo 424774 426079 := bstep (se 1 (by rfl) ⟨319559, by rfl⟩ : syracuseStep 426079 = 639119) B639119
theorem B1441907 : Blo 424774 1441907 := bstep (se 1 (by rfl) ⟨1081430, by rfl⟩ : syracuseStep 1441907 = 2162861) B2162861
theorem B426107 : Blo 424774 426107 := bstep (se 1 (by rfl) ⟨319580, by rfl⟩ : syracuseStep 426107 = 639161) B639161
theorem B426159 : Blo 424774 426159 := bstep (se 1 (by rfl) ⟨319619, by rfl⟩ : syracuseStep 426159 = 639239) B639239
theorem B426183 : Blo 424774 426183 := bstep (se 1 (by rfl) ⟨319637, by rfl⟩ : syracuseStep 426183 = 639275) B639275
theorem B426203 : Blo 424774 426203 := bstep (se 1 (by rfl) ⟨319652, by rfl⟩ : syracuseStep 426203 = 639305) B639305
theorem B426279 : Blo 424774 426279 := bstep (se 1 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 426279 = 639419) B639419
theorem B426319 : Blo 424774 426319 := bstep (se 1 (by rfl) ⟨319739, by rfl⟩ : syracuseStep 426319 = 639479) B639479
theorem B426335 : Blo 424774 426335 := bstep (se 1 (by rfl) ⟨319751, by rfl⟩ : syracuseStep 426335 = 639503) B639503
theorem B426363 : Blo 424774 426363 := bstep (se 1 (by rfl) ⟨319772, by rfl⟩ : syracuseStep 426363 = 639545) B639545
theorem B1442177 : Blo 424774 1442177 := bstep (se 2 (by rfl) ⟨540816, by rfl⟩ : syracuseStep 1442177 = 1081633) B1081633
theorem B426415 : Blo 424774 426415 := bstep (se 1 (by rfl) ⟨319811, by rfl⟩ : syracuseStep 426415 = 639623) B639623
theorem B426439 : Blo 424774 426439 := bstep (se 1 (by rfl) ⟨319829, by rfl⟩ : syracuseStep 426439 = 639659) B639659
theorem B426459 : Blo 424774 426459 := bstep (se 1 (by rfl) ⟨319844, by rfl⟩ : syracuseStep 426459 = 639689) B639689
theorem B426535 : Blo 424774 426535 := bstep (se 1 (by rfl) ⟨319901, by rfl⟩ : syracuseStep 426535 = 639803) B639803
theorem B426575 : Blo 424774 426575 := bstep (se 1 (by rfl) ⟨319931, by rfl⟩ : syracuseStep 426575 = 639863) B639863
theorem B721487 : Blo 424774 721487 := bstep (se 1 (by rfl) ⟨541115, by rfl⟩ : syracuseStep 721487 = 1082231) B1082231
theorem B426591 : Blo 424774 426591 := bstep (se 1 (by rfl) ⟨319943, by rfl⟩ : syracuseStep 426591 = 639887) B639887
theorem B426619 : Blo 424774 426619 := bstep (se 1 (by rfl) ⟨319964, by rfl⟩ : syracuseStep 426619 = 639929) B639929
theorem B426671 : Blo 424774 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B1639111 : Blo 424774 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B426695 : Blo 424774 426695 := bstep (se 1 (by rfl) ⟨320021, by rfl⟩ : syracuseStep 426695 = 640043) B640043
theorem B426715 : Blo 424774 426715 := bstep (se 1 (by rfl) ⟨320036, by rfl⟩ : syracuseStep 426715 = 640073) B640073
theorem B426791 : Blo 424774 426791 := bstep (se 1 (by rfl) ⟨320093, by rfl⟩ : syracuseStep 426791 = 640187) B640187
theorem B426831 : Blo 424774 426831 := bstep (se 1 (by rfl) ⟨320123, by rfl⟩ : syracuseStep 426831 = 640247) B640247
theorem B426847 : Blo 424774 426847 := bstep (se 1 (by rfl) ⟨320135, by rfl⟩ : syracuseStep 426847 = 640271) B640271
theorem B426875 : Blo 424774 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B3474323 : Blo 424774 3474323 := bstep (se 1 (by rfl) ⟨2605742, by rfl⟩ : syracuseStep 3474323 = 5211485) B5211485
theorem B426927 : Blo 424774 426927 := bstep (se 1 (by rfl) ⟨320195, by rfl⟩ : syracuseStep 426927 = 640391) B640391
theorem B426951 : Blo 424774 426951 := bstep (se 1 (by rfl) ⟨320213, by rfl⟩ : syracuseStep 426951 = 640427) B640427
theorem B426971 : Blo 424774 426971 := bstep (se 1 (by rfl) ⟨320228, by rfl⟩ : syracuseStep 426971 = 640457) B640457
theorem B3245021 : Blo 424774 3245021 := bstep (se 3 (by rfl) ⟨608441, by rfl⟩ : syracuseStep 3245021 = 1216883) B1216883
theorem B427047 : Blo 424774 427047 := bstep (se 1 (by rfl) ⟨320285, by rfl⟩ : syracuseStep 427047 = 640571) B640571
theorem B15205427 : Blo 424774 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B24052787 : Blo 424774 24052787 := bstep (se 1 (by rfl) ⟨18039590, by rfl⟩ : syracuseStep 24052787 = 36079181) B36079181
theorem B427087 : Blo 424774 427087 := bstep (se 1 (by rfl) ⟨320315, by rfl⟩ : syracuseStep 427087 = 640631) B640631
theorem B427103 : Blo 424774 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B427131 : Blo 424774 427131 := bstep (se 1 (by rfl) ⟨320348, by rfl⟩ : syracuseStep 427131 = 640697) B640697
theorem B1442987 : Blo 424774 1442987 := bstep (se 1 (by rfl) ⟨1082240, by rfl⟩ : syracuseStep 1442987 = 2164481) B2164481
theorem B427183 : Blo 424774 427183 := bstep (se 1 (by rfl) ⟨320387, by rfl⟩ : syracuseStep 427183 = 640775) B640775
theorem B427207 : Blo 424774 427207 := bstep (se 1 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 427207 = 640811) B640811
theorem B427227 : Blo 424774 427227 := bstep (se 1 (by rfl) ⟨320420, by rfl⟩ : syracuseStep 427227 = 640841) B640841
theorem B1541387 : Blo 424774 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B427303 : Blo 424774 427303 := bstep (se 1 (by rfl) ⟨320477, by rfl⟩ : syracuseStep 427303 = 640955) B640955
theorem B427343 : Blo 424774 427343 := bstep (se 1 (by rfl) ⟨320507, by rfl⟩ : syracuseStep 427343 = 641015) B641015
theorem B427359 : Blo 424774 427359 := bstep (se 1 (by rfl) ⟨320519, by rfl⟩ : syracuseStep 427359 = 641039) B641039
theorem B427387 : Blo 424774 427387 := bstep (se 1 (by rfl) ⟨320540, by rfl⟩ : syracuseStep 427387 = 641081) B641081
theorem B1082767 : Blo 424774 1082767 := bstep (se 1 (by rfl) ⟨812075, by rfl⟩ : syracuseStep 1082767 = 1624151) B1624151
theorem B427439 : Blo 424774 427439 := bstep (se 1 (by rfl) ⟨320579, by rfl⟩ : syracuseStep 427439 = 641159) B641159
theorem B722351 : Blo 424774 722351 := bstep (se 1 (by rfl) ⟨541763, by rfl⟩ : syracuseStep 722351 = 1083527) B1083527
theorem B427463 : Blo 424774 427463 := bstep (se 1 (by rfl) ⟨320597, by rfl⟩ : syracuseStep 427463 = 641195) B641195
theorem B427483 : Blo 424774 427483 := bstep (se 1 (by rfl) ⟨320612, by rfl⟩ : syracuseStep 427483 = 641225) B641225
theorem B1213991 : Blo 424774 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B427559 : Blo 424774 427559 := bstep (se 1 (by rfl) ⟨320669, by rfl⟩ : syracuseStep 427559 = 641339) B641339
theorem B427599 : Blo 424774 427599 := bstep (se 1 (by rfl) ⟨320699, by rfl⟩ : syracuseStep 427599 = 641399) B641399
theorem B427615 : Blo 424774 427615 := bstep (se 1 (by rfl) ⟨320711, by rfl⟩ : syracuseStep 427615 = 641423) B641423
theorem B427643 : Blo 424774 427643 := bstep (se 1 (by rfl) ⟨320732, by rfl⟩ : syracuseStep 427643 = 641465) B641465
theorem B427695 : Blo 424774 427695 := bstep (se 1 (by rfl) ⟨320771, by rfl⟩ : syracuseStep 427695 = 641543) B641543
theorem B1640125 : Blo 424774 1640125 := bstep (se 3 (by rfl) ⟨307523, by rfl⟩ : syracuseStep 1640125 = 615047) B615047
theorem B1443527 : Blo 424774 1443527 := bstep (se 1 (by rfl) ⟨1082645, by rfl⟩ : syracuseStep 1443527 = 2165291) B2165291
theorem B427719 : Blo 424774 427719 := bstep (se 1 (by rfl) ⟨320789, by rfl⟩ : syracuseStep 427719 = 641579) B641579
theorem B1083091 : Blo 424774 1083091 := bstep (se 1 (by rfl) ⟨812318, by rfl⟩ : syracuseStep 1083091 = 1624637) B1624637
theorem B427739 : Blo 424774 427739 := bstep (se 1 (by rfl) ⟨320804, by rfl⟩ : syracuseStep 427739 = 641609) B641609
theorem B427815 : Blo 424774 427815 := bstep (se 1 (by rfl) ⟨320861, by rfl⟩ : syracuseStep 427815 = 641723) B641723
theorem B427855 : Blo 424774 427855 := bstep (se 1 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 427855 = 641783) B641783
theorem B427871 : Blo 424774 427871 := bstep (se 1 (by rfl) ⟨320903, by rfl⟩ : syracuseStep 427871 = 641807) B641807
theorem B2197343 : Blo 424774 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B722783 : Blo 424774 722783 := bstep (se 1 (by rfl) ⟨542087, by rfl⟩ : syracuseStep 722783 = 1084175) B1084175
theorem B427899 : Blo 424774 427899 := bstep (se 1 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 427899 = 641849) B641849
theorem B427951 : Blo 424774 427951 := bstep (se 1 (by rfl) ⟨320963, by rfl⟩ : syracuseStep 427951 = 641927) B641927
theorem B427975 : Blo 424774 427975 := bstep (se 1 (by rfl) ⟨320981, by rfl⟩ : syracuseStep 427975 = 641963) B641963
theorem B427995 : Blo 424774 427995 := bstep (se 1 (by rfl) ⟨320996, by rfl⟩ : syracuseStep 427995 = 641993) B641993
theorem B428071 : Blo 424774 428071 := bstep (se 1 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 428071 = 642107) B642107
theorem B428111 : Blo 424774 428111 := bstep (se 1 (by rfl) ⟨321083, by rfl⟩ : syracuseStep 428111 = 642167) B642167
theorem B428127 : Blo 424774 428127 := bstep (se 1 (by rfl) ⟨321095, by rfl⟩ : syracuseStep 428127 = 642191) B642191
theorem B428155 : Blo 424774 428155 := bstep (se 1 (by rfl) ⟨321116, by rfl⟩ : syracuseStep 428155 = 642233) B642233
theorem B428207 : Blo 424774 428207 := bstep (se 1 (by rfl) ⟨321155, by rfl⟩ : syracuseStep 428207 = 642311) B642311
theorem B428231 : Blo 424774 428231 := bstep (se 1 (by rfl) ⟨321173, by rfl⟩ : syracuseStep 428231 = 642347) B642347
theorem B428251 : Blo 424774 428251 := bstep (se 1 (by rfl) ⟨321188, by rfl⟩ : syracuseStep 428251 = 642377) B642377
theorem B428327 : Blo 424774 428327 := bstep (se 1 (by rfl) ⟨321245, by rfl⟩ : syracuseStep 428327 = 642491) B642491
theorem B428367 : Blo 424774 428367 := bstep (se 1 (by rfl) ⟨321275, by rfl⟩ : syracuseStep 428367 = 642551) B642551
theorem B428383 : Blo 424774 428383 := bstep (se 1 (by rfl) ⟨321287, by rfl⟩ : syracuseStep 428383 = 642575) B642575
theorem B6130025 : Blo 424774 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B428411 : Blo 424774 428411 := bstep (se 1 (by rfl) ⟨321308, by rfl⟩ : syracuseStep 428411 = 642617) B642617
theorem B723343 : Blo 424774 723343 := bstep (se 1 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 723343 = 1085015) B1085015
theorem B428463 : Blo 424774 428463 := bstep (se 1 (by rfl) ⟨321347, by rfl⟩ : syracuseStep 428463 = 642695) B642695
theorem B428487 : Blo 424774 428487 := bstep (se 1 (by rfl) ⟨321365, by rfl⟩ : syracuseStep 428487 = 642731) B642731
theorem B428507 : Blo 424774 428507 := bstep (se 1 (by rfl) ⟨321380, by rfl⟩ : syracuseStep 428507 = 642761) B642761
theorem B1444391 : Blo 424774 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B428583 : Blo 424774 428583 := bstep (se 1 (by rfl) ⟨321437, by rfl⟩ : syracuseStep 428583 = 642875) B642875
theorem B428623 : Blo 424774 428623 := bstep (se 1 (by rfl) ⟨321467, by rfl⟩ : syracuseStep 428623 = 642935) B642935
theorem B428639 : Blo 424774 428639 := bstep (se 1 (by rfl) ⟨321479, by rfl⟩ : syracuseStep 428639 = 642959) B642959
theorem B428667 : Blo 424774 428667 := bstep (se 1 (by rfl) ⟨321500, by rfl⟩ : syracuseStep 428667 = 643001) B643001
theorem B5474951 : Blo 424774 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B1084043 : Blo 424774 1084043 := bstep (se 1 (by rfl) ⟨813032, by rfl⟩ : syracuseStep 1084043 = 1626065) B1626065
theorem B1444499 : Blo 424774 1444499 := bstep (se 1 (by rfl) ⟨1083374, by rfl⟩ : syracuseStep 1444499 = 2166749) B2166749
theorem B428719 : Blo 424774 428719 := bstep (se 1 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 428719 = 643079) B643079
theorem B1215175 : Blo 424774 1215175 := bstep (se 1 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 1215175 = 1822763) B1822763
theorem B428743 : Blo 424774 428743 := bstep (se 1 (by rfl) ⟨321557, by rfl⟩ : syracuseStep 428743 = 643115) B643115
theorem B428763 : Blo 424774 428763 := bstep (se 1 (by rfl) ⟨321572, by rfl⟩ : syracuseStep 428763 = 643145) B643145
theorem B2919197 : Blo 424774 2919197 := bstep (se 3 (by rfl) ⟨547349, by rfl⟩ : syracuseStep 2919197 = 1094699) B1094699
theorem B1444715 : Blo 424774 1444715 := bstep (se 1 (by rfl) ⟨1083536, by rfl⟩ : syracuseStep 1444715 = 2167073) B2167073
theorem B1444769 : Blo 424774 1444769 := bstep (se 2 (by rfl) ⟨541788, by rfl⟩ : syracuseStep 1444769 = 1083577) B1083577
theorem B691163 : Blo 424774 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B1445363 : Blo 424774 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B1773305 : Blo 424774 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1085177 : Blo 424774 1085177 := bstep (se 2 (by rfl) ⟨406941, by rfl⟩ : syracuseStep 1085177 = 813883) B813883
theorem B1216417 : Blo 424774 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B1445903 : Blo 424774 1445903 := bstep (se 1 (by rfl) ⟨1084427, by rfl⟩ : syracuseStep 1445903 = 2168855) B2168855
theorem B20713745 : Blo 424774 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B2298241 : Blo 424774 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B1446497 : Blo 424774 1446497 := bstep (se 2 (by rfl) ⟨542436, by rfl⟩ : syracuseStep 1446497 = 1084873) B1084873
theorem B9573137 : Blo 424774 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2724637 : Blo 424774 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B1643527 : Blo 424774 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B1217693 : Blo 424774 1217693 := bstep (se 3 (by rfl) ⟨228317, by rfl⟩ : syracuseStep 1217693 = 456635) B456635
theorem B2168207 : Blo 424774 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B955943 : Blo 424774 955943 := bstep (se 1 (by rfl) ⟨716957, by rfl⟩ : syracuseStep 955943 = 1433915) B1433915
theorem B956267 : Blo 424774 956267 := bstep (se 1 (by rfl) ⟨717200, by rfl⟩ : syracuseStep 956267 = 1434401) B1434401
theorem B956321 : Blo 424774 956321 := bstep (se 2 (by rfl) ⟨358620, by rfl⟩ : syracuseStep 956321 = 717241) B717241
theorem B956663 : Blo 424774 956663 := bstep (se 1 (by rfl) ⟨717497, by rfl⟩ : syracuseStep 956663 = 1434995) B1434995
theorem B3447431 : Blo 424774 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B957257 : Blo 424774 957257 := bstep (se 2 (by rfl) ⟨358971, by rfl⟩ : syracuseStep 957257 = 717943) B717943
theorem B2170313 : Blo 424774 2170313 := bstep (se 2 (by rfl) ⟨813867, by rfl⟩ : syracuseStep 2170313 = 1627735) B1627735
theorem B958049 : Blo 424774 958049 := bstep (se 2 (by rfl) ⟨359268, by rfl⟩ : syracuseStep 958049 = 718537) B718537
theorem B1154657 : Blo 424774 1154657 := bstep (se 2 (by rfl) ⟨432996, by rfl⟩ : syracuseStep 1154657 = 865993) B865993
theorem B5480075 : Blo 424774 5480075 := bstep (se 1 (by rfl) ⟨4110056, by rfl⟩ : syracuseStep 5480075 = 8220113) B8220113
theorem B1613459 : Blo 424774 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B1384235 : Blo 424774 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B1613641 : Blo 424774 1613641 := bstep (se 2 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 1613641 = 1210231) B1210231
theorem B958391 : Blo 424774 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B1875899 : Blo 424774 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B1220665 : Blo 424774 1220665 := bstep (se 2 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 1220665 = 915499) B915499
theorem B958985 : Blo 424774 958985 := bstep (se 2 (by rfl) ⟨359619, by rfl⟩ : syracuseStep 958985 = 719239) B719239
theorem B959327 : Blo 424774 959327 := bstep (se 1 (by rfl) ⟨719495, by rfl⟩ : syracuseStep 959327 = 1438991) B1438991
theorem B959507 : Blo 424774 959507 := bstep (se 1 (by rfl) ⟨719630, by rfl⟩ : syracuseStep 959507 = 1439261) B1439261
theorem B959849 : Blo 424774 959849 := bstep (se 2 (by rfl) ⟨359943, by rfl⟩ : syracuseStep 959849 = 719887) B719887
theorem B1615571 : Blo 424774 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B1025747 : Blo 424774 1025747 := bstep (se 1 (by rfl) ⟨769310, by rfl⟩ : syracuseStep 1025747 = 1538621) B1538621
theorem B960443 : Blo 424774 960443 := bstep (se 1 (by rfl) ⟨720332, by rfl⟩ : syracuseStep 960443 = 1440665) B1440665
theorem B862247 : Blo 424774 862247 := bstep (se 1 (by rfl) ⟨646685, by rfl⟩ : syracuseStep 862247 = 1293371) B1293371
theorem B960569 : Blo 424774 960569 := bstep (se 2 (by rfl) ⟨360213, by rfl⟩ : syracuseStep 960569 = 720427) B720427
theorem B960911 : Blo 424774 960911 := bstep (se 1 (by rfl) ⟨720683, by rfl⟩ : syracuseStep 960911 = 1441367) B1441367
theorem B961235 : Blo 424774 961235 := bstep (se 1 (by rfl) ⟨720926, by rfl⟩ : syracuseStep 961235 = 1441853) B1441853
theorem B4860971 : Blo 424774 4860971 := bstep (se 1 (by rfl) ⟨3645728, by rfl⟩ : syracuseStep 4860971 = 7291457) B7291457
theorem B1027151 : Blo 424774 1027151 := bstep (se 1 (by rfl) ⟨770363, by rfl⟩ : syracuseStep 1027151 = 1540727) B1540727
theorem B3910949 : Blo 424774 3910949 := bstep (se 4 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 3910949 = 733303) B733303
theorem B1453373 : Blo 424774 1453373 := bstep (se 3 (by rfl) ⟨272507, by rfl⟩ : syracuseStep 1453373 = 545015) B545015
theorem B863561 : Blo 424774 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B1945127 : Blo 424774 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B962171 : Blo 424774 962171 := bstep (se 1 (by rfl) ⟨721628, by rfl⟩ : syracuseStep 962171 = 1443257) B1443257
theorem B962297 : Blo 424774 962297 := bstep (se 2 (by rfl) ⟨360861, by rfl⟩ : syracuseStep 962297 = 721723) B721723
theorem B962567 : Blo 424774 962567 := bstep (se 1 (by rfl) ⟨721925, by rfl⟩ : syracuseStep 962567 = 1443851) B1443851
theorem B962639 : Blo 424774 962639 := bstep (se 1 (by rfl) ⟨721979, by rfl⟩ : syracuseStep 962639 = 1443959) B1443959
theorem B1618001 : Blo 424774 1618001 := bstep (se 2 (by rfl) ⟨606750, by rfl⟩ : syracuseStep 1618001 = 1213501) B1213501
theorem B2240627 : Blo 424774 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B864427 : Blo 424774 864427 := bstep (se 1 (by rfl) ⟨648320, by rfl⟩ : syracuseStep 864427 = 1296641) B1296641
theorem B1618319 : Blo 424774 1618319 := bstep (se 1 (by rfl) ⟨1213739, by rfl⟩ : syracuseStep 1618319 = 2427479) B2427479
theorem B766369 : Blo 424774 766369 := bstep (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) B574777
theorem B963035 : Blo 424774 963035 := bstep (se 1 (by rfl) ⟨722276, by rfl⟩ : syracuseStep 963035 = 1444553) B1444553
theorem B14398361 : Blo 424774 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B963503 : Blo 424774 963503 := bstep (se 1 (by rfl) ⟨722627, by rfl⟩ : syracuseStep 963503 = 1445255) B1445255
theorem B766903 : Blo 424774 766903 := bstep (se 1 (by rfl) ⟨575177, by rfl⟩ : syracuseStep 766903 = 1150355) B1150355
theorem B963755 : Blo 424774 963755 := bstep (se 1 (by rfl) ⟨722816, by rfl⟩ : syracuseStep 963755 = 1445633) B1445633
theorem B1619261 : Blo 424774 1619261 := bstep (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) B607223
theorem B767407 : Blo 424774 767407 := bstep (se 1 (by rfl) ⟨575555, by rfl⟩ : syracuseStep 767407 = 1151111) B1151111
theorem B964295 : Blo 424774 964295 := bstep (se 1 (by rfl) ⟨723221, by rfl⟩ : syracuseStep 964295 = 1446443) B1446443
theorem B2471639 : Blo 424774 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B1095611 : Blo 424774 1095611 := bstep (se 1 (by rfl) ⟨821708, by rfl⟩ : syracuseStep 1095611 = 1643417) B1643417
theorem B5453831 : Blo 424774 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B3127385 : Blo 424774 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B2734195 : Blo 424774 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B637289 : Blo 424774 637289 := bstep (se 2 (by rfl) ⟨238983, by rfl⟩ : syracuseStep 637289 = 477967) B477967
theorem B637367 : Blo 424774 637367 := bstep (se 1 (by rfl) ⟨478025, by rfl⟩ : syracuseStep 637367 = 956051) B956051
theorem B637403 : Blo 424774 637403 := bstep (se 1 (by rfl) ⟨478052, by rfl⟩ : syracuseStep 637403 = 956105) B956105
theorem B637871 : Blo 424774 637871 := bstep (se 1 (by rfl) ⟨478403, by rfl⟩ : syracuseStep 637871 = 956807) B956807
theorem B637961 : Blo 424774 637961 := bstep (se 2 (by rfl) ⟨239235, by rfl⟩ : syracuseStep 637961 = 478471) B478471
theorem B637991 : Blo 424774 637991 := bstep (se 1 (by rfl) ⟨478493, by rfl⟩ : syracuseStep 637991 = 956987) B956987
theorem B2964599 : Blo 424774 2964599 := bstep (se 1 (by rfl) ⟨2223449, by rfl⟩ : syracuseStep 2964599 = 4446899) B4446899
theorem B638075 : Blo 424774 638075 := bstep (se 1 (by rfl) ⟨478556, by rfl⟩ : syracuseStep 638075 = 957113) B957113
theorem B638201 : Blo 424774 638201 := bstep (se 2 (by rfl) ⟨239325, by rfl⟩ : syracuseStep 638201 = 478651) B478651
theorem B2931983 : Blo 424774 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B638303 : Blo 424774 638303 := bstep (se 1 (by rfl) ⟨478727, by rfl⟩ : syracuseStep 638303 = 957455) B957455
theorem B638315 : Blo 424774 638315 := bstep (se 1 (by rfl) ⟨478736, by rfl⟩ : syracuseStep 638315 = 957473) B957473
theorem B540199 : Blo 424774 540199 := bstep (se 1 (by rfl) ⟨405149, by rfl⟩ : syracuseStep 540199 = 810299) B810299
theorem B638543 : Blo 424774 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B2211467 : Blo 424774 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B638663 : Blo 424774 638663 := bstep (se 1 (by rfl) ⟨478997, by rfl⟩ : syracuseStep 638663 = 957995) B957995
theorem B638825 : Blo 424774 638825 := bstep (se 2 (by rfl) ⟨239559, by rfl⟩ : syracuseStep 638825 = 479119) B479119
theorem B540523 : Blo 424774 540523 := bstep (se 1 (by rfl) ⟨405392, by rfl⟩ : syracuseStep 540523 = 810785) B810785
theorem B638903 : Blo 424774 638903 := bstep (se 1 (by rfl) ⟨479177, by rfl⟩ : syracuseStep 638903 = 958355) B958355
theorem B638939 : Blo 424774 638939 := bstep (se 1 (by rfl) ⟨479204, by rfl⟩ : syracuseStep 638939 = 958409) B958409
theorem B2736143 : Blo 424774 2736143 := bstep (se 1 (by rfl) ⟨2052107, by rfl⟩ : syracuseStep 2736143 = 4104215) B4104215
theorem B540751 : Blo 424774 540751 := bstep (se 1 (by rfl) ⟨405563, by rfl⟩ : syracuseStep 540751 = 811127) B811127
theorem B3620945 : Blo 424774 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B868475 : Blo 424774 868475 := bstep (se 1 (by rfl) ⟨651356, by rfl⟩ : syracuseStep 868475 = 1302713) B1302713
theorem B770377 : Blo 424774 770377 := bstep (se 2 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 770377 = 577783) B577783
theorem B639407 : Blo 424774 639407 := bstep (se 1 (by rfl) ⟨479555, by rfl⟩ : syracuseStep 639407 = 959111) B959111
theorem B639497 : Blo 424774 639497 := bstep (se 2 (by rfl) ⟨239811, by rfl⟩ : syracuseStep 639497 = 479623) B479623
theorem B639527 : Blo 424774 639527 := bstep (se 1 (by rfl) ⟨479645, by rfl⟩ : syracuseStep 639527 = 959291) B959291
theorem B639611 : Blo 424774 639611 := bstep (se 1 (by rfl) ⟨479708, by rfl⟩ : syracuseStep 639611 = 959417) B959417
theorem B1622663 : Blo 424774 1622663 := bstep (se 1 (by rfl) ⟨1216997, by rfl⟩ : syracuseStep 1622663 = 2433995) B2433995
theorem B639737 : Blo 424774 639737 := bstep (se 2 (by rfl) ⟨239901, by rfl⟩ : syracuseStep 639737 = 479803) B479803
theorem B639839 : Blo 424774 639839 := bstep (se 1 (by rfl) ⟨479879, by rfl⟩ : syracuseStep 639839 = 959759) B959759
theorem B639851 : Blo 424774 639851 := bstep (se 1 (by rfl) ⟨479888, by rfl⟩ : syracuseStep 639851 = 959777) B959777
theorem B1459063 : Blo 424774 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B640079 : Blo 424774 640079 := bstep (se 1 (by rfl) ⟨480059, by rfl⟩ : syracuseStep 640079 = 960119) B960119
theorem B541819 : Blo 424774 541819 := bstep (se 1 (by rfl) ⟨406364, by rfl⟩ : syracuseStep 541819 = 812729) B812729
theorem B3556547 : Blo 424774 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B640199 : Blo 424774 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B542047 : Blo 424774 542047 := bstep (se 1 (by rfl) ⟨406535, by rfl⟩ : syracuseStep 542047 = 813071) B813071
theorem B640361 : Blo 424774 640361 := bstep (se 2 (by rfl) ⟨240135, by rfl⟩ : syracuseStep 640361 = 480271) B480271
theorem B1820029 : Blo 424774 1820029 := bstep (se 3 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 1820029 = 682511) B682511
theorem B640439 : Blo 424774 640439 := bstep (se 1 (by rfl) ⟨480329, by rfl⟩ : syracuseStep 640439 = 960659) B960659
theorem B640475 : Blo 424774 640475 := bstep (se 1 (by rfl) ⟨480356, by rfl⟩ : syracuseStep 640475 = 960713) B960713
theorem B607753 : Blo 424774 607753 := bstep (se 2 (by rfl) ⟨227907, by rfl⟩ : syracuseStep 607753 = 455815) B455815
theorem B3130919 : Blo 424774 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2049725 : Blo 424774 2049725 := bstep (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) B768647
theorem B6899393 : Blo 424774 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B3655367 : Blo 424774 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B640943 : Blo 424774 640943 := bstep (se 1 (by rfl) ⟨480707, by rfl⟩ : syracuseStep 640943 = 961415) B961415
theorem B542639 : Blo 424774 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B641033 : Blo 424774 641033 := bstep (se 2 (by rfl) ⟨240387, by rfl⟩ : syracuseStep 641033 = 480775) B480775
theorem B641063 : Blo 424774 641063 := bstep (se 1 (by rfl) ⟨480797, by rfl⟩ : syracuseStep 641063 = 961595) B961595
theorem B772135 : Blo 424774 772135 := bstep (se 1 (by rfl) ⟨579101, by rfl⟩ : syracuseStep 772135 = 1158203) B1158203
theorem B1624121 : Blo 424774 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B641147 : Blo 424774 641147 := bstep (se 1 (by rfl) ⟨480860, by rfl⟩ : syracuseStep 641147 = 961721) B961721
theorem B641273 : Blo 424774 641273 := bstep (se 2 (by rfl) ⟨240477, by rfl⟩ : syracuseStep 641273 = 480955) B480955
theorem B641375 : Blo 424774 641375 := bstep (se 1 (by rfl) ⟨481031, by rfl⟩ : syracuseStep 641375 = 962063) B962063
theorem B641387 : Blo 424774 641387 := bstep (se 1 (by rfl) ⟨481040, by rfl⟩ : syracuseStep 641387 = 962081) B962081
theorem B641615 : Blo 424774 641615 := bstep (se 1 (by rfl) ⟨481211, by rfl⟩ : syracuseStep 641615 = 962423) B962423
theorem B477895 : Blo 424774 477895 := bstep (se 1 (by rfl) ⟨358421, by rfl⟩ : syracuseStep 477895 = 716843) B716843
theorem B641735 : Blo 424774 641735 := bstep (se 1 (by rfl) ⟨481301, by rfl⟩ : syracuseStep 641735 = 962603) B962603
theorem B2214611 : Blo 424774 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B641897 : Blo 424774 641897 := bstep (se 2 (by rfl) ⟨240711, by rfl⟩ : syracuseStep 641897 = 481423) B481423
theorem B641975 : Blo 424774 641975 := bstep (se 1 (by rfl) ⟨481481, by rfl⟩ : syracuseStep 641975 = 962963) B962963
theorem B642011 : Blo 424774 642011 := bstep (se 1 (by rfl) ⟨481508, by rfl⟩ : syracuseStep 642011 = 963017) B963017
theorem B2968595 : Blo 424774 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B609319 : Blo 424774 609319 := bstep (se 1 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 609319 = 913979) B913979
theorem B1756313 : Blo 424774 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B642479 : Blo 424774 642479 := bstep (se 1 (by rfl) ⟨481859, by rfl⟩ : syracuseStep 642479 = 963719) B963719
theorem B1625609 : Blo 424774 1625609 := bstep (se 2 (by rfl) ⟨609603, by rfl⟩ : syracuseStep 1625609 = 1219207) B1219207
theorem B642569 : Blo 424774 642569 := bstep (se 2 (by rfl) ⟨240963, by rfl⟩ : syracuseStep 642569 = 481927) B481927
theorem B478759 : Blo 424774 478759 := bstep (se 1 (by rfl) ⟨359069, by rfl⟩ : syracuseStep 478759 = 718139) B718139
theorem B642599 : Blo 424774 642599 := bstep (se 1 (by rfl) ⟨481949, by rfl⟩ : syracuseStep 642599 = 963899) B963899
theorem B4869719 : Blo 424774 4869719 := bstep (se 1 (by rfl) ⟨3652289, by rfl⟩ : syracuseStep 4869719 = 7304579) B7304579
theorem B4116055 : Blo 424774 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B642683 : Blo 424774 642683 := bstep (se 1 (by rfl) ⟨482012, by rfl⟩ : syracuseStep 642683 = 964025) B964025
theorem B642809 : Blo 424774 642809 := bstep (se 2 (by rfl) ⟨241053, by rfl⟩ : syracuseStep 642809 = 482107) B482107
theorem B642911 : Blo 424774 642911 := bstep (se 1 (by rfl) ⟨482183, by rfl⟩ : syracuseStep 642911 = 964367) B964367
theorem B1724267 : Blo 424774 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B642923 : Blo 424774 642923 := bstep (se 1 (by rfl) ⟨482192, by rfl⟩ : syracuseStep 642923 = 964385) B964385
theorem B1855495 : Blo 424774 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B3657757 : Blo 424774 3657757 := bstep (se 3 (by rfl) ⟨685829, by rfl⟩ : syracuseStep 3657757 = 1371659) B1371659
theorem B643151 : Blo 424774 643151 := bstep (se 1 (by rfl) ⟨482363, by rfl⟩ : syracuseStep 643151 = 964727) B964727
theorem B5820497 : Blo 424774 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B22106317 : Blo 424774 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B5493197 : Blo 424774 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B1626763 : Blo 424774 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B807671 : Blo 424774 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B2151197 : Blo 424774 2151197 := bstep (se 3 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 2151197 = 806699) B806699
theorem B1364779 : Blo 424774 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B971615 : Blo 424774 971615 := bstep (se 1 (by rfl) ⟨728711, by rfl⟩ : syracuseStep 971615 = 1457423) B1457423
theorem B1364843 : Blo 424774 1364843 := bstep (se 1 (by rfl) ⟨1023632, by rfl⟩ : syracuseStep 1364843 = 2047265) B2047265
theorem B807823 : Blo 424774 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B1627067 : Blo 424774 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B480379 : Blo 424774 480379 := bstep (se 1 (by rfl) ⟨360284, by rfl⟩ : syracuseStep 480379 = 720569) B720569
theorem B480847 : Blo 424774 480847 := bstep (se 1 (by rfl) ⟨360635, by rfl⟩ : syracuseStep 480847 = 721271) B721271
theorem B1824353 : Blo 424774 1824353 := bstep (se 2 (by rfl) ⟨684132, by rfl⟩ : syracuseStep 1824353 = 1368265) B1368265
theorem B1824403 : Blo 424774 1824403 := bstep (se 1 (by rfl) ⟨1368302, by rfl⟩ : syracuseStep 1824403 = 2736605) B2736605
theorem B808697 : Blo 424774 808697 := bstep (se 2 (by rfl) ⟨303261, by rfl⟩ : syracuseStep 808697 = 606523) B606523
theorem B6543139 : Blo 424774 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B808879 : Blo 424774 808879 := bstep (se 1 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 808879 = 1213319) B1213319
theorem B481243 : Blo 424774 481243 := bstep (se 1 (by rfl) ⟨360932, by rfl⟩ : syracuseStep 481243 = 721865) B721865
theorem B12277817 : Blo 424774 12277817 := bstep (se 2 (by rfl) ⟨4604181, by rfl⟩ : syracuseStep 12277817 = 9208363) B9208363
theorem B3889457 : Blo 424774 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B481711 : Blo 424774 481711 := bstep (se 1 (by rfl) ⟨361283, by rfl⟩ : syracuseStep 481711 = 722567) B722567
theorem B3234329 : Blo 424774 3234329 := bstep (se 2 (by rfl) ⟨1212873, by rfl⟩ : syracuseStep 3234329 = 2425747) B2425747
theorem B1366625 : Blo 424774 1366625 := bstep (se 2 (by rfl) ⟨512484, by rfl⟩ : syracuseStep 1366625 = 1024969) B1024969
theorem B2054915 : Blo 424774 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B482143 : Blo 424774 482143 := bstep (se 1 (by rfl) ⟨361607, by rfl⟩ : syracuseStep 482143 = 723215) B723215
theorem B5200823 : Blo 424774 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B6151247 : Blo 424774 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B1531037 : Blo 424774 1531037 := bstep (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) B574139
theorem B810155 : Blo 424774 810155 := bstep (se 1 (by rfl) ⟨607616, by rfl⟩ : syracuseStep 810155 = 1215233) B1215233
theorem B2055415 : Blo 424774 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B1728209 : Blo 424774 1728209 := bstep (se 2 (by rfl) ⟨648078, by rfl⟩ : syracuseStep 1728209 = 1296157) B1296157
theorem B1433753 : Blo 424774 1433753 := bstep (se 2 (by rfl) ⟨537657, by rfl⟩ : syracuseStep 1433753 = 1075315) B1075315
theorem B2744549 : Blo 424774 2744549 := bstep (se 4 (by rfl) ⟨257301, by rfl⟩ : syracuseStep 2744549 = 514603) B514603
theorem B811529 : Blo 424774 811529 := bstep (se 2 (by rfl) ⟨304323, by rfl⟩ : syracuseStep 811529 = 608647) B608647
theorem B1532449 : Blo 424774 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B811559 : Blo 424774 811559 := bstep (se 1 (by rfl) ⟨608669, by rfl⟩ : syracuseStep 811559 = 1217339) B1217339
theorem B3465787 : Blo 424774 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B909947 : Blo 424774 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B2155571 : Blo 424774 2155571 := bstep (se 1 (by rfl) ⟨1616678, by rfl⟩ : syracuseStep 2155571 = 3233357) B3233357
theorem B812243 : Blo 424774 812243 := bstep (se 1 (by rfl) ⟨609182, by rfl⟩ : syracuseStep 812243 = 1218365) B1218365
theorem B812281 : Blo 424774 812281 := bstep (se 2 (by rfl) ⟨304605, by rfl⟩ : syracuseStep 812281 = 609211) B609211
theorem B1434941 : Blo 424774 1434941 := bstep (se 3 (by rfl) ⟨269051, by rfl⟩ : syracuseStep 1434941 = 538103) B538103
theorem B615775 : Blo 424774 615775 := bstep (se 1 (by rfl) ⟨461831, by rfl⟩ : syracuseStep 615775 = 923663) B923663
theorem B3237245 : Blo 424774 3237245 := bstep (se 3 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 3237245 = 1213967) B1213967
theorem B648667 : Blo 424774 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B1730413 : Blo 424774 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B1828727 : Blo 424774 1828727 := bstep (se 1 (by rfl) ⟨1371545, by rfl⟩ : syracuseStep 1828727 = 2743091) B2743091
theorem B812987 : Blo 424774 812987 := bstep (se 1 (by rfl) ⟨609740, by rfl⟩ : syracuseStep 812987 = 1219481) B1219481
theorem B3958721 : Blo 424774 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B3074125 : Blo 424774 3074125 := bstep (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) B1152797
theorem B5859461 : Blo 424774 5859461 := bstep (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) B1098649
theorem B1435805 : Blo 424774 1435805 := bstep (se 3 (by rfl) ⟨269213, by rfl⟩ : syracuseStep 1435805 = 538427) B538427
theorem B1534295 : Blo 424774 1534295 := bstep (se 1 (by rfl) ⟨1150721, by rfl⟩ : syracuseStep 1534295 = 2301443) B2301443
theorem B3631513 : Blo 424774 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B813473 : Blo 424774 813473 := bstep (se 2 (by rfl) ⟨305052, by rfl⟩ : syracuseStep 813473 = 610105) B610105
theorem B1075751 : Blo 424774 1075751 := bstep (se 1 (by rfl) ⟨806813, by rfl⟩ : syracuseStep 1075751 = 1613627) B1613627
theorem B911911 : Blo 424774 911911 := bstep (se 1 (by rfl) ⟨683933, by rfl⟩ : syracuseStep 911911 = 1367867) B1367867
theorem B2157191 : Blo 424774 2157191 := bstep (se 1 (by rfl) ⟨1617893, by rfl⟩ : syracuseStep 2157191 = 3235787) B3235787
theorem B813739 : Blo 424774 813739 := bstep (se 1 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 813739 = 1220609) B1220609
theorem B1436345 : Blo 424774 1436345 := bstep (se 2 (by rfl) ⟨538629, by rfl⟩ : syracuseStep 1436345 = 1077259) B1077259
theorem B6154937 : Blo 424774 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B1370839 : Blo 424774 1370839 := bstep (se 1 (by rfl) ⟨1028129, by rfl⟩ : syracuseStep 1370839 = 2056259) B2056259
theorem B1076075 : Blo 424774 1076075 := bstep (se 1 (by rfl) ⟨807056, by rfl⟩ : syracuseStep 1076075 = 1614113) B1614113
theorem B486319 : Blo 424774 486319 := bstep (se 1 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 486319 = 729479) B729479
theorem B2419915 : Blo 424774 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B1436939 : Blo 424774 1436939 := bstep (se 1 (by rfl) ⟨1077704, by rfl⟩ : syracuseStep 1436939 = 2155409) B2155409
theorem B748873 : Blo 424774 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B1076723 : Blo 424774 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1437209 : Blo 424774 1437209 := bstep (se 2 (by rfl) ⟨538953, by rfl⟩ : syracuseStep 1437209 = 1077907) B1077907
theorem B1076935 : Blo 424774 1076935 := bstep (se 1 (by rfl) ⟨807701, by rfl⟩ : syracuseStep 1076935 = 1615403) B1615403
theorem B2453291 : Blo 424774 2453291 := bstep (se 1 (by rfl) ⟨1839968, by rfl⟩ : syracuseStep 2453291 = 3679937) B3679937
theorem B1535851 : Blo 424774 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B9891733 : Blo 424774 9891733 := bstep (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) B463675
theorem B683959 : Blo 424774 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B454619 : Blo 424774 454619 := bstep (se 1 (by rfl) ⟨340964, by rfl⟩ : syracuseStep 454619 = 681929) B681929
theorem B716809 : Blo 424774 716809 := bstep (se 2 (by rfl) ⟨268803, by rfl⟩ : syracuseStep 716809 = 537607) B537607
theorem B2158649 : Blo 424774 2158649 := bstep (se 2 (by rfl) ⟨809493, by rfl⟩ : syracuseStep 2158649 = 1618987) B1618987
theorem B716971 : Blo 424774 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B553159 : Blo 424774 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B5534081 : Blo 424774 5534081 := bstep (se 2 (by rfl) ⟨2075280, by rfl⟩ : syracuseStep 5534081 = 4150561) B4150561
theorem B717275 : Blo 424774 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B1077857 : Blo 424774 1077857 := bstep (se 2 (by rfl) ⟨404196, by rfl⟩ : syracuseStep 1077857 = 808393) B808393
theorem B1438343 : Blo 424774 1438343 := bstep (se 1 (by rfl) ⟨1078757, by rfl⟩ : syracuseStep 1438343 = 2157515) B2157515
theorem B1438397 : Blo 424774 1438397 := bstep (se 3 (by rfl) ⟨269699, by rfl⟩ : syracuseStep 1438397 = 539399) B539399
theorem B717511 : Blo 424774 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B11268881 : Blo 424774 11268881 := bstep (se 2 (by rfl) ⟨4225830, by rfl⟩ : syracuseStep 11268881 = 8451661) B8451661
theorem B1438559 : Blo 424774 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B717673 : Blo 424774 717673 := bstep (se 2 (by rfl) ⟨269127, by rfl⟩ : syracuseStep 717673 = 538255) B538255
theorem B1438721 : Blo 424774 1438721 := bstep (se 2 (by rfl) ⟨539520, by rfl⟩ : syracuseStep 1438721 = 1079041) B1079041
theorem B718267 : Blo 424774 718267 := bstep (se 1 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 718267 = 1077401) B1077401
theorem B718375 : Blo 424774 718375 := bstep (se 1 (by rfl) ⟨538781, by rfl⟩ : syracuseStep 718375 = 1077563) B1077563
theorem B3241619 : Blo 424774 3241619 := bstep (se 1 (by rfl) ⟨2431214, by rfl⟩ : syracuseStep 3241619 = 4862429) B4862429
theorem B1439531 : Blo 424774 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B718699 : Blo 424774 718699 := bstep (se 1 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 718699 = 1078049) B1078049
theorem B8222573 : Blo 424774 8222573 := bstep (se 3 (by rfl) ⟨1541732, by rfl⟩ : syracuseStep 8222573 = 3083465) B3083465
theorem B1079315 : Blo 424774 1079315 := bstep (se 1 (by rfl) ⟨809486, by rfl⟩ : syracuseStep 1079315 = 1618973) B1618973
theorem B1439801 : Blo 424774 1439801 := bstep (se 2 (by rfl) ⟨539925, by rfl⟩ : syracuseStep 1439801 = 1079851) B1079851
theorem B2160755 : Blo 424774 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B1440125 : Blo 424774 1440125 := bstep (se 3 (by rfl) ⟨270023, by rfl⟩ : syracuseStep 1440125 = 540047) B540047
theorem B1440395 : Blo 424774 1440395 := bstep (se 1 (by rfl) ⟨1080296, by rfl⟩ : syracuseStep 1440395 = 2160593) B2160593
theorem B424783 : Blo 424774 424783 := bstep (se 1 (by rfl) ⟨318587, by rfl⟩ : syracuseStep 424783 = 637175) B637175
theorem B424799 : Blo 424774 424799 := bstep (se 1 (by rfl) ⟨318599, by rfl⟩ : syracuseStep 424799 = 637199) B637199
theorem B424827 : Blo 424774 424827 := bstep (se 1 (by rfl) ⟨318620, by rfl⟩ : syracuseStep 424827 = 637241) B637241
theorem B719759 : Blo 424774 719759 := bstep (se 1 (by rfl) ⟨539819, by rfl⟩ : syracuseStep 719759 = 1079639) B1079639
theorem B424879 : Blo 424774 424879 := bstep (se 1 (by rfl) ⟨318659, by rfl⟩ : syracuseStep 424879 = 637319) B637319
theorem B424903 : Blo 424774 424903 := bstep (se 1 (by rfl) ⟨318677, by rfl⟩ : syracuseStep 424903 = 637355) B637355
theorem B424923 : Blo 424774 424923 := bstep (se 1 (by rfl) ⟨318692, by rfl⟩ : syracuseStep 424923 = 637385) B637385
theorem B2948069 : Blo 424774 2948069 := bstep (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) B552763
theorem B6224881 : Blo 424774 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B424999 : Blo 424774 424999 := bstep (se 1 (by rfl) ⟨318749, by rfl⟩ : syracuseStep 424999 = 637499) B637499
theorem B425039 : Blo 424774 425039 := bstep (se 1 (by rfl) ⟨318779, by rfl⟩ : syracuseStep 425039 = 637559) B637559
theorem B818255 : Blo 424774 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B425055 : Blo 424774 425055 := bstep (se 1 (by rfl) ⟨318791, by rfl⟩ : syracuseStep 425055 = 637583) B637583
theorem B425083 : Blo 424774 425083 := bstep (se 1 (by rfl) ⟨318812, by rfl⟩ : syracuseStep 425083 = 637625) B637625
theorem B719995 : Blo 424774 719995 := bstep (se 1 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 719995 = 1079993) B1079993
theorem B425135 : Blo 424774 425135 := bstep (se 1 (by rfl) ⟨318851, by rfl⟩ : syracuseStep 425135 = 637703) B637703
theorem B4914371 : Blo 424774 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B425159 : Blo 424774 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B425179 : Blo 424774 425179 := bstep (se 1 (by rfl) ⟨318884, by rfl⟩ : syracuseStep 425179 = 637769) B637769
theorem B425255 : Blo 424774 425255 := bstep (se 1 (by rfl) ⟨318941, by rfl⟩ : syracuseStep 425255 = 637883) B637883
theorem B425295 : Blo 424774 425295 := bstep (se 1 (by rfl) ⟨318971, by rfl⟩ : syracuseStep 425295 = 637943) B637943
theorem B425311 : Blo 424774 425311 := bstep (se 1 (by rfl) ⟨318983, by rfl⟩ : syracuseStep 425311 = 637967) B637967
theorem B425339 : Blo 424774 425339 := bstep (se 1 (by rfl) ⟨319004, by rfl⟩ : syracuseStep 425339 = 638009) B638009
theorem B4619663 : Blo 424774 4619663 := bstep (se 1 (by rfl) ⟨3464747, by rfl⟩ : syracuseStep 4619663 = 6929495) B6929495
theorem B425391 : Blo 424774 425391 := bstep (se 1 (by rfl) ⟨319043, by rfl⟩ : syracuseStep 425391 = 638087) B638087
theorem B425415 : Blo 424774 425415 := bstep (se 1 (by rfl) ⟨319061, by rfl⟩ : syracuseStep 425415 = 638123) B638123
theorem B425435 : Blo 424774 425435 := bstep (se 1 (by rfl) ⟨319076, by rfl⟩ : syracuseStep 425435 = 638153) B638153
theorem B1441313 : Blo 424774 1441313 := bstep (se 2 (by rfl) ⟨540492, by rfl⟩ : syracuseStep 1441313 = 1080985) B1080985
theorem B425511 : Blo 424774 425511 := bstep (se 1 (by rfl) ⟨319133, by rfl⟩ : syracuseStep 425511 = 638267) B638267
theorem B425551 : Blo 424774 425551 := bstep (se 1 (by rfl) ⟨319163, by rfl⟩ : syracuseStep 425551 = 638327) B638327
theorem B6159959 : Blo 424774 6159959 := bstep (se 1 (by rfl) ⟨4619969, by rfl⟩ : syracuseStep 6159959 = 9239939) B9239939
theorem B425567 : Blo 424774 425567 := bstep (se 1 (by rfl) ⟨319175, by rfl⟩ : syracuseStep 425567 = 638351) B638351
theorem B425595 : Blo 424774 425595 := bstep (se 1 (by rfl) ⟨319196, by rfl⟩ : syracuseStep 425595 = 638393) B638393
theorem B1212043 : Blo 424774 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B425647 : Blo 424774 425647 := bstep (se 1 (by rfl) ⟨319235, by rfl⟩ : syracuseStep 425647 = 638471) B638471
theorem B425671 : Blo 424774 425671 := bstep (se 1 (by rfl) ⟨319253, by rfl⟩ : syracuseStep 425671 = 638507) B638507
theorem B2162375 : Blo 424774 2162375 := bstep (se 1 (by rfl) ⟨1621781, by rfl⟩ : syracuseStep 2162375 = 3243563) B3243563
theorem B425691 : Blo 424774 425691 := bstep (se 1 (by rfl) ⟨319268, by rfl⟩ : syracuseStep 425691 = 638537) B638537
theorem B1441529 : Blo 424774 1441529 := bstep (se 2 (by rfl) ⟨540573, by rfl⟩ : syracuseStep 1441529 = 1081147) B1081147
theorem B425767 : Blo 424774 425767 := bstep (se 1 (by rfl) ⟨319325, by rfl⟩ : syracuseStep 425767 = 638651) B638651
theorem B425807 : Blo 424774 425807 := bstep (se 1 (by rfl) ⟨319355, by rfl⟩ : syracuseStep 425807 = 638711) B638711
theorem B425823 : Blo 424774 425823 := bstep (se 1 (by rfl) ⟨319367, by rfl⟩ : syracuseStep 425823 = 638735) B638735
theorem B2195309 : Blo 424774 2195309 := bstep (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) B823241
theorem B425851 : Blo 424774 425851 := bstep (se 1 (by rfl) ⟨319388, by rfl⟩ : syracuseStep 425851 = 638777) B638777
theorem B425903 : Blo 424774 425903 := bstep (se 1 (by rfl) ⟨319427, by rfl⟩ : syracuseStep 425903 = 638855) B638855
theorem B425927 : Blo 424774 425927 := bstep (se 1 (by rfl) ⟨319445, by rfl⟩ : syracuseStep 425927 = 638891) B638891
theorem B425947 : Blo 424774 425947 := bstep (se 1 (by rfl) ⟨319460, by rfl⟩ : syracuseStep 425947 = 638921) B638921
theorem B720859 : Blo 424774 720859 := bstep (se 1 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 720859 = 1081289) B1081289
theorem B721001 : Blo 424774 721001 := bstep (se 2 (by rfl) ⟨270375, by rfl⟩ : syracuseStep 721001 = 540751) B540751
theorem B426271 : Blo 424774 426271 := bstep (se 1 (by rfl) ⟨319703, by rfl⟩ : syracuseStep 426271 = 639407) B639407
theorem B426331 : Blo 424774 426331 := bstep (se 1 (by rfl) ⟨319748, by rfl⟩ : syracuseStep 426331 = 639497) B639497
theorem B426351 : Blo 424774 426351 := bstep (se 1 (by rfl) ⟨319763, by rfl⟩ : syracuseStep 426351 = 639527) B639527
theorem B426407 : Blo 424774 426407 := bstep (se 1 (by rfl) ⟨319805, by rfl⟩ : syracuseStep 426407 = 639611) B639611
theorem B1081775 : Blo 424774 1081775 := bstep (se 1 (by rfl) ⟨811331, by rfl⟩ : syracuseStep 1081775 = 1622663) B1622663
theorem B426491 : Blo 424774 426491 := bstep (se 1 (by rfl) ⟨319868, by rfl⟩ : syracuseStep 426491 = 639737) B639737
theorem B426559 : Blo 424774 426559 := bstep (se 1 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 426559 = 639839) B639839
theorem B426567 : Blo 424774 426567 := bstep (se 1 (by rfl) ⟨319925, by rfl⟩ : syracuseStep 426567 = 639851) B639851
theorem B2163347 : Blo 424774 2163347 := bstep (se 1 (by rfl) ⟨1622510, by rfl⟩ : syracuseStep 2163347 = 3245021) B3245021
theorem B426719 : Blo 424774 426719 := bstep (se 1 (by rfl) ⟨320039, by rfl⟩ : syracuseStep 426719 = 640079) B640079
theorem B4621049 : Blo 424774 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B426799 : Blo 424774 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B426907 : Blo 424774 426907 := bstep (se 1 (by rfl) ⟨320180, by rfl⟩ : syracuseStep 426907 = 640361) B640361
theorem B426959 : Blo 424774 426959 := bstep (se 1 (by rfl) ⟨320219, by rfl⟩ : syracuseStep 426959 = 640439) B640439
theorem B426983 : Blo 424774 426983 := bstep (se 1 (by rfl) ⟨320237, by rfl⟩ : syracuseStep 426983 = 640475) B640475
theorem B2950181 : Blo 424774 2950181 := bstep (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) B553159
theorem B427295 : Blo 424774 427295 := bstep (se 1 (by rfl) ⟨320471, by rfl⟩ : syracuseStep 427295 = 640943) B640943
theorem B427355 : Blo 424774 427355 := bstep (se 1 (by rfl) ⟨320516, by rfl⟩ : syracuseStep 427355 = 641033) B641033
theorem B427375 : Blo 424774 427375 := bstep (se 1 (by rfl) ⟨320531, by rfl⟩ : syracuseStep 427375 = 641063) B641063
theorem B1082747 : Blo 424774 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B427431 : Blo 424774 427431 := bstep (se 1 (by rfl) ⟨320573, by rfl⟩ : syracuseStep 427431 = 641147) B641147
theorem B2164157 : Blo 424774 2164157 := bstep (se 3 (by rfl) ⟨405779, by rfl⟩ : syracuseStep 2164157 = 811559) B811559
theorem B722425 : Blo 424774 722425 := bstep (se 2 (by rfl) ⟨270909, by rfl⟩ : syracuseStep 722425 = 541819) B541819
theorem B427515 : Blo 424774 427515 := bstep (se 1 (by rfl) ⟨320636, by rfl⟩ : syracuseStep 427515 = 641273) B641273
theorem B427583 : Blo 424774 427583 := bstep (se 1 (by rfl) ⟨320687, by rfl⟩ : syracuseStep 427583 = 641375) B641375
theorem B427591 : Blo 424774 427591 := bstep (se 1 (by rfl) ⟨320693, by rfl⟩ : syracuseStep 427591 = 641387) B641387
theorem B1083041 : Blo 424774 1083041 := bstep (se 2 (by rfl) ⟨406140, by rfl⟩ : syracuseStep 1083041 = 812281) B812281
theorem B427743 : Blo 424774 427743 := bstep (se 1 (by rfl) ⟨320807, by rfl⟩ : syracuseStep 427743 = 641615) B641615
theorem B722695 : Blo 424774 722695 := bstep (se 1 (by rfl) ⟨542021, by rfl⟩ : syracuseStep 722695 = 1084043) B1084043
theorem B821033 : Blo 424774 821033 := bstep (se 2 (by rfl) ⟨307887, by rfl⟩ : syracuseStep 821033 = 615775) B615775
theorem B722729 : Blo 424774 722729 := bstep (se 2 (by rfl) ⟨271023, by rfl⟩ : syracuseStep 722729 = 542047) B542047
theorem B427823 : Blo 424774 427823 := bstep (se 1 (by rfl) ⟨320867, by rfl⟩ : syracuseStep 427823 = 641735) B641735
theorem B1476407 : Blo 424774 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2426705 : Blo 424774 2426705 := bstep (se 2 (by rfl) ⟨910014, by rfl⟩ : syracuseStep 2426705 = 1820029) B1820029
theorem B1443689 : Blo 424774 1443689 := bstep (se 2 (by rfl) ⟨541383, by rfl⟩ : syracuseStep 1443689 = 1082767) B1082767
theorem B427931 : Blo 424774 427931 := bstep (se 1 (by rfl) ⟨320948, by rfl⟩ : syracuseStep 427931 = 641897) B641897
theorem B427983 : Blo 424774 427983 := bstep (se 1 (by rfl) ⟨320987, by rfl⟩ : syracuseStep 427983 = 641975) B641975
theorem B460775 : Blo 424774 460775 := bstep (se 1 (by rfl) ⟨345581, by rfl⟩ : syracuseStep 460775 = 691163) B691163
theorem B428007 : Blo 424774 428007 := bstep (se 1 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 428007 = 642011) B642011
theorem B2590973 : Blo 424774 2590973 := bstep (se 3 (by rfl) ⟨485807, by rfl⟩ : syracuseStep 2590973 = 971615) B971615
theorem B1444121 : Blo 424774 1444121 := bstep (se 2 (by rfl) ⟨541545, by rfl⟩ : syracuseStep 1444121 = 1083091) B1083091
theorem B428319 : Blo 424774 428319 := bstep (se 1 (by rfl) ⟨321239, by rfl⟩ : syracuseStep 428319 = 642479) B642479
theorem B1083739 : Blo 424774 1083739 := bstep (se 1 (by rfl) ⟨812804, by rfl⟩ : syracuseStep 1083739 = 1625609) B1625609
theorem B428379 : Blo 424774 428379 := bstep (se 1 (by rfl) ⟨321284, by rfl⟩ : syracuseStep 428379 = 642569) B642569
theorem B428399 : Blo 424774 428399 := bstep (se 1 (by rfl) ⟨321299, by rfl⟩ : syracuseStep 428399 = 642599) B642599
theorem B3246479 : Blo 424774 3246479 := bstep (se 1 (by rfl) ⟨2434859, by rfl⟩ : syracuseStep 3246479 = 4869719) B4869719
theorem B428455 : Blo 424774 428455 := bstep (se 1 (by rfl) ⟨321341, by rfl⟩ : syracuseStep 428455 = 642683) B642683
theorem B1182203 : Blo 424774 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B428539 : Blo 424774 428539 := bstep (se 1 (by rfl) ⟨321404, by rfl⟩ : syracuseStep 428539 = 642809) B642809
theorem B723451 : Blo 424774 723451 := bstep (se 1 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 723451 = 1085177) B1085177
theorem B428607 : Blo 424774 428607 := bstep (se 1 (by rfl) ⟨321455, by rfl⟩ : syracuseStep 428607 = 642911) B642911
theorem B428615 : Blo 424774 428615 := bstep (se 1 (by rfl) ⟨321461, by rfl⟩ : syracuseStep 428615 = 642923) B642923
theorem B428767 : Blo 424774 428767 := bstep (se 1 (by rfl) ⟨321575, by rfl⟩ : syracuseStep 428767 = 643151) B643151
theorem B4098833 : Blo 424774 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B1084711 : Blo 424774 1084711 := bstep (se 1 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 1084711 = 1627067) B1627067
theorem B1215881 : Blo 424774 1215881 := bstep (se 2 (by rfl) ⟨455955, by rfl⟩ : syracuseStep 1215881 = 911911) B911911
theorem B1084985 : Blo 424774 1084985 := bstep (se 2 (by rfl) ⟨406869, by rfl⟩ : syracuseStep 1084985 = 813739) B813739
theorem B1445471 : Blo 424774 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B1216235 : Blo 424774 1216235 := bstep (se 1 (by rfl) ⟨912176, by rfl⟩ : syracuseStep 1216235 = 1824353) B1824353
theorem B2592971 : Blo 424774 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B2298287 : Blo 424774 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B4100831 : Blo 424774 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1020691 : Blo 424774 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1446875 : Blo 424774 1446875 := bstep (se 1 (by rfl) ⟨1085156, by rfl⟩ : syracuseStep 1446875 = 2170313) B2170313
theorem B1447037 : Blo 424774 1447037 := bstep (se 3 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 1447037 = 542639) B542639
theorem B1152139 : Blo 424774 1152139 := bstep (se 1 (by rfl) ⟨864104, by rfl⟩ : syracuseStep 1152139 = 1728209) B1728209
theorem B922823 : Blo 424774 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B955745 : Blo 424774 955745 := bstep (se 2 (by rfl) ⟨358404, by rfl⟩ : syracuseStep 955745 = 716809) B716809
theorem B955835 : Blo 424774 955835 := bstep (se 1 (by rfl) ⟨716876, by rfl⟩ : syracuseStep 955835 = 1433753) B1433753
theorem B955961 : Blo 424774 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B1152569 : Blo 424774 1152569 := bstep (se 2 (by rfl) ⟨432213, by rfl⟩ : syracuseStep 1152569 = 864427) B864427
theorem B1021825 : Blo 424774 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B2169017 : Blo 424774 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B956627 : Blo 424774 956627 := bstep (se 1 (by rfl) ⟨717470, by rfl⟩ : syracuseStep 956627 = 1434941) B1434941
theorem B956681 : Blo 424774 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B956897 : Blo 424774 956897 := bstep (se 2 (by rfl) ⟨358836, by rfl⟩ : syracuseStep 956897 = 717673) B717673
theorem B1022537 : Blo 424774 1022537 := bstep (se 2 (by rfl) ⟨383451, by rfl⟩ : syracuseStep 1022537 = 766903) B766903
theorem B1219151 : Blo 424774 1219151 := bstep (se 1 (by rfl) ⟨914363, by rfl⟩ : syracuseStep 1219151 = 1828727) B1828727
theorem B3906307 : Blo 424774 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B957203 : Blo 424774 957203 := bstep (se 1 (by rfl) ⟨717902, by rfl⟩ : syracuseStep 957203 = 1435805) B1435805
theorem B1022863 : Blo 424774 1022863 := bstep (se 1 (by rfl) ⟨767147, by rfl⟩ : syracuseStep 1022863 = 1534295) B1534295
theorem B957563 : Blo 424774 957563 := bstep (se 1 (by rfl) ⟨718172, by rfl⟩ : syracuseStep 957563 = 1436345) B1436345
theorem B4103291 : Blo 424774 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B1023209 : Blo 424774 1023209 := bstep (se 2 (by rfl) ⟨383703, by rfl⟩ : syracuseStep 1023209 = 767407) B767407
theorem B957689 : Blo 424774 957689 := bstep (se 2 (by rfl) ⟨359133, by rfl⟩ : syracuseStep 957689 = 718267) B718267
theorem B957833 : Blo 424774 957833 := bstep (se 2 (by rfl) ⟨359187, by rfl⟩ : syracuseStep 957833 = 718375) B718375
theorem B957959 : Blo 424774 957959 := bstep (se 1 (by rfl) ⟨718469, by rfl⟩ : syracuseStep 957959 = 1436939) B1436939
theorem B2432537 : Blo 424774 2432537 := bstep (se 2 (by rfl) ⟨912201, by rfl⟩ : syracuseStep 2432537 = 1824403) B1824403
theorem B958139 : Blo 424774 958139 := bstep (se 1 (by rfl) ⟨718604, by rfl⟩ : syracuseStep 958139 = 1437209) B1437209
theorem B8724185 : Blo 424774 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B958265 : Blo 424774 958265 := bstep (se 2 (by rfl) ⟨359349, by rfl⟩ : syracuseStep 958265 = 718699) B718699
theorem B3645593 : Blo 424774 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B958895 : Blo 424774 958895 := bstep (se 1 (by rfl) ⟨719171, by rfl⟩ : syracuseStep 958895 = 1438343) B1438343
theorem B958931 : Blo 424774 958931 := bstep (se 1 (by rfl) ⟨719198, by rfl⟩ : syracuseStep 958931 = 1438397) B1438397
theorem B7512587 : Blo 424774 7512587 := bstep (se 1 (by rfl) ⟨5634440, by rfl⟩ : syracuseStep 7512587 = 11268881) B11268881
theorem B959039 : Blo 424774 959039 := bstep (se 1 (by rfl) ⟨719279, by rfl⟩ : syracuseStep 959039 = 1438559) B1438559
theorem B959147 : Blo 424774 959147 := bstep (se 1 (by rfl) ⟨719360, by rfl⟩ : syracuseStep 959147 = 1438721) B1438721
theorem B2302829 : Blo 424774 2302829 := bstep (se 3 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 2302829 = 863561) B863561
theorem B959687 : Blo 424774 959687 := bstep (se 1 (by rfl) ⟨719765, by rfl⟩ : syracuseStep 959687 = 1439531) B1439531
theorem B5481715 : Blo 424774 5481715 := bstep (se 1 (by rfl) ⟨4111286, by rfl⟩ : syracuseStep 5481715 = 8222573) B8222573
theorem B8299841 : Blo 424774 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B959867 : Blo 424774 959867 := bstep (se 1 (by rfl) ⟨719900, by rfl⟩ : syracuseStep 959867 = 1439801) B1439801
theorem B959993 : Blo 424774 959993 := bstep (se 2 (by rfl) ⟨359997, by rfl⟩ : syracuseStep 959993 = 719995) B719995
theorem B960083 : Blo 424774 960083 := bstep (se 1 (by rfl) ⟨720062, by rfl⟩ : syracuseStep 960083 = 1440125) B1440125
theorem B960263 : Blo 424774 960263 := bstep (se 1 (by rfl) ⟨720197, by rfl⟩ : syracuseStep 960263 = 1440395) B1440395
theorem B1976399 : Blo 424774 1976399 := bstep (se 1 (by rfl) ⟨1482299, by rfl⟩ : syracuseStep 1976399 = 2964599) B2964599
theorem B1616057 : Blo 424774 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B4598045 : Blo 424774 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B960875 : Blo 424774 960875 := bstep (se 1 (by rfl) ⟨720656, by rfl⟩ : syracuseStep 960875 = 1441313) B1441313
theorem B4106639 : Blo 424774 4106639 := bstep (se 1 (by rfl) ⟨3079979, by rfl⟩ : syracuseStep 4106639 = 6159959) B6159959
theorem B961019 : Blo 424774 961019 := bstep (se 1 (by rfl) ⟨720764, by rfl⟩ : syracuseStep 961019 = 1441529) B1441529
theorem B961145 : Blo 424774 961145 := bstep (se 2 (by rfl) ⟨360429, by rfl⟩ : syracuseStep 961145 = 720859) B720859
theorem B961199 : Blo 424774 961199 := bstep (se 1 (by rfl) ⟨720899, by rfl⟩ : syracuseStep 961199 = 1441799) B1441799
theorem B961271 : Blo 424774 961271 := bstep (se 1 (by rfl) ⟨720953, by rfl⟩ : syracuseStep 961271 = 1441907) B1441907
theorem B961451 : Blo 424774 961451 := bstep (se 1 (by rfl) ⟨721088, by rfl⟩ : syracuseStep 961451 = 1442177) B1442177
theorem B5975005 : Blo 424774 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B1027169 : Blo 424774 1027169 := bstep (se 2 (by rfl) ⟨385188, by rfl⟩ : syracuseStep 1027169 = 770377) B770377
theorem B10136951 : Blo 424774 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B16035191 : Blo 424774 16035191 := bstep (se 1 (by rfl) ⟨12026393, by rfl⟩ : syracuseStep 16035191 = 24052787) B24052787
theorem B961991 : Blo 424774 961991 := bstep (se 1 (by rfl) ⟨721493, by rfl⟩ : syracuseStep 961991 = 1442987) B1442987
theorem B2371031 : Blo 424774 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B4599595 : Blo 424774 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B962351 : Blo 424774 962351 := bstep (se 1 (by rfl) ⟨721763, by rfl⟩ : syracuseStep 962351 = 1443527) B1443527
theorem B2436911 : Blo 424774 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B962927 : Blo 424774 962927 := bstep (se 1 (by rfl) ⟨722195, by rfl⟩ : syracuseStep 962927 = 1444391) B1444391
theorem B3649967 : Blo 424774 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B962999 : Blo 424774 962999 := bstep (se 1 (by rfl) ⟨722249, by rfl⟩ : syracuseStep 962999 = 1444499) B1444499
theorem B963143 : Blo 424774 963143 := bstep (se 1 (by rfl) ⟨722357, by rfl⟩ : syracuseStep 963143 = 1444715) B1444715
theorem B963179 : Blo 424774 963179 := bstep (se 1 (by rfl) ⟨722384, by rfl⟩ : syracuseStep 963179 = 1444769) B1444769
theorem B1979063 : Blo 424774 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B963575 : Blo 424774 963575 := bstep (se 1 (by rfl) ⟨722681, by rfl⟩ : syracuseStep 963575 = 1445363) B1445363
theorem B2307217 : Blo 424774 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B963935 : Blo 424774 963935 := bstep (se 1 (by rfl) ⟨722951, by rfl⟩ : syracuseStep 963935 = 1445903) B1445903
theorem B3880331 : Blo 424774 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B8173061 : Blo 424774 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B13809163 : Blo 424774 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B964331 : Blo 424774 964331 := bstep (se 1 (by rfl) ⟨723248, by rfl⟩ : syracuseStep 964331 = 1446497) B1446497
theorem B964457 : Blo 424774 964457 := bstep (se 2 (by rfl) ⟨361671, by rfl⟩ : syracuseStep 964457 = 723343) B723343
theorem B4110365 : Blo 424774 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B637193 : Blo 424774 637193 := bstep (se 2 (by rfl) ⟨238947, by rfl⟩ : syracuseStep 637193 = 477895) B477895
theorem B1620233 : Blo 424774 1620233 := bstep (se 2 (by rfl) ⟨607587, by rfl⟩ : syracuseStep 1620233 = 1215175) B1215175
theorem B637295 : Blo 424774 637295 := bstep (se 1 (by rfl) ⟨477971, by rfl⟩ : syracuseStep 637295 = 955943) B955943
theorem B539131 : Blo 424774 539131 := bstep (se 1 (by rfl) ⟨404348, by rfl⟩ : syracuseStep 539131 = 808697) B808697
theorem B637511 : Blo 424774 637511 := bstep (se 1 (by rfl) ⟨478133, by rfl⟩ : syracuseStep 637511 = 956267) B956267
theorem B637547 : Blo 424774 637547 := bstep (se 1 (by rfl) ⟨478160, by rfl⟩ : syracuseStep 637547 = 956321) B956321
theorem B637775 : Blo 424774 637775 := bstep (se 1 (by rfl) ⟨478331, by rfl⟩ : syracuseStep 637775 = 956663) B956663
theorem B3226553 : Blo 424774 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B998497 : Blo 424774 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B638171 : Blo 424774 638171 := bstep (se 1 (by rfl) ⟨478628, by rfl⟩ : syracuseStep 638171 = 957257) B957257
theorem B7781669 : Blo 424774 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B638345 : Blo 424774 638345 := bstep (se 2 (by rfl) ⟨239379, by rfl⟩ : syracuseStep 638345 = 478759) B478759
theorem B540103 : Blo 424774 540103 := bstep (se 1 (by rfl) ⟨405077, by rfl⟩ : syracuseStep 540103 = 810155) B810155
theorem B5488073 : Blo 424774 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B638699 : Blo 424774 638699 := bstep (se 1 (by rfl) ⟨479024, by rfl⟩ : syracuseStep 638699 = 958049) B958049
theorem B769771 : Blo 424774 769771 := bstep (se 1 (by rfl) ⟨577328, by rfl⟩ : syracuseStep 769771 = 1154657) B1154657
theorem B3653383 : Blo 424774 3653383 := bstep (se 1 (by rfl) ⟨2740037, by rfl⟩ : syracuseStep 3653383 = 5480075) B5480075
theorem B13188977 : Blo 424774 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B1621889 : Blo 424774 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B638927 : Blo 424774 638927 := bstep (se 1 (by rfl) ⟨479195, by rfl⟩ : syracuseStep 638927 = 958391) B958391
theorem B2473993 : Blo 424774 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B29475089 : Blo 424774 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B639323 : Blo 424774 639323 := bstep (se 1 (by rfl) ⟨479492, by rfl⟩ : syracuseStep 639323 = 958985) B958985
theorem B541019 : Blo 424774 541019 := bstep (se 1 (by rfl) ⟨405764, by rfl⟩ : syracuseStep 541019 = 811529) B811529
theorem B606631 : Blo 424774 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B3064321 : Blo 424774 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B639551 : Blo 424774 639551 := bstep (se 1 (by rfl) ⟨479663, by rfl⟩ : syracuseStep 639551 = 959327) B959327
theorem B639671 : Blo 424774 639671 := bstep (se 1 (by rfl) ⟨479753, by rfl⟩ : syracuseStep 639671 = 959507) B959507
theorem B541495 : Blo 424774 541495 := bstep (se 1 (by rfl) ⟨406121, by rfl⟩ : syracuseStep 541495 = 812243) B812243
theorem B639899 : Blo 424774 639899 := bstep (se 1 (by rfl) ⟨479924, by rfl⟩ : syracuseStep 639899 = 959849) B959849
theorem B1819705 : Blo 424774 1819705 := bstep (se 2 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 1819705 = 1364779) B1364779
theorem B640295 : Blo 424774 640295 := bstep (se 1 (by rfl) ⟨480221, by rfl⟩ : syracuseStep 640295 = 960443) B960443
theorem B541991 : Blo 424774 541991 := bstep (se 1 (by rfl) ⟨406493, by rfl⟩ : syracuseStep 541991 = 812987) B812987
theorem B2639147 : Blo 424774 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B574831 : Blo 424774 574831 := bstep (se 1 (by rfl) ⟨431123, by rfl⟩ : syracuseStep 574831 = 862247) B862247
theorem B640379 : Blo 424774 640379 := bstep (se 1 (by rfl) ⟨480284, by rfl⟩ : syracuseStep 640379 = 960569) B960569
theorem B640505 : Blo 424774 640505 := bstep (se 2 (by rfl) ⟨240189, by rfl⟩ : syracuseStep 640505 = 480379) B480379
theorem B640607 : Blo 424774 640607 := bstep (se 1 (by rfl) ⟨480455, by rfl⟩ : syracuseStep 640607 = 960911) B960911
theorem B542315 : Blo 424774 542315 := bstep (se 1 (by rfl) ⟨406736, by rfl⟩ : syracuseStep 542315 = 813473) B813473
theorem B640823 : Blo 424774 640823 := bstep (se 1 (by rfl) ⟨480617, by rfl⟩ : syracuseStep 640823 = 961235) B961235
theorem B7784525 : Blo 424774 7784525 := bstep (se 3 (by rfl) ⟨1459598, by rfl⟩ : syracuseStep 7784525 = 2919197) B2919197
theorem B641129 : Blo 424774 641129 := bstep (se 2 (by rfl) ⟨240423, by rfl⟩ : syracuseStep 641129 = 480847) B480847
theorem B2607299 : Blo 424774 2607299 := bstep (se 1 (by rfl) ⟨1955474, by rfl⟩ : syracuseStep 2607299 = 3910949) B3910949
theorem B968915 : Blo 424774 968915 := bstep (se 1 (by rfl) ⟨726686, by rfl⟩ : syracuseStep 968915 = 1453373) B1453373
theorem B26364149 : Blo 424774 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1296751 : Blo 424774 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B641447 : Blo 424774 641447 := bstep (se 1 (by rfl) ⟨481085, by rfl⟩ : syracuseStep 641447 = 962171) B962171
theorem B3459557 : Blo 424774 3459557 := bstep (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) B648667
theorem B641531 : Blo 424774 641531 := bstep (se 1 (by rfl) ⟨481148, by rfl⟩ : syracuseStep 641531 = 962297) B962297
theorem B641657 : Blo 424774 641657 := bstep (se 2 (by rfl) ⟨240621, by rfl⟩ : syracuseStep 641657 = 481243) B481243
theorem B641711 : Blo 424774 641711 := bstep (se 1 (by rfl) ⟨481283, by rfl⟩ : syracuseStep 641711 = 962567) B962567
theorem B641759 : Blo 424774 641759 := bstep (se 1 (by rfl) ⟨481319, by rfl⟩ : syracuseStep 641759 = 962639) B962639
theorem B3689387 : Blo 424774 3689387 := bstep (se 1 (by rfl) ⟨2767040, by rfl⟩ : syracuseStep 3689387 = 5534081) B5534081
theorem B478183 : Blo 424774 478183 := bstep (se 1 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 478183 = 717275) B717275
theorem B642023 : Blo 424774 642023 := bstep (se 1 (by rfl) ⟨481517, by rfl⟩ : syracuseStep 642023 = 963035) B963035
theorem B642281 : Blo 424774 642281 := bstep (se 2 (by rfl) ⟨240855, by rfl⟩ : syracuseStep 642281 = 481711) B481711
theorem B642335 : Blo 424774 642335 := bstep (se 1 (by rfl) ⟨481751, by rfl⟩ : syracuseStep 642335 = 963503) B963503
theorem B642503 : Blo 424774 642503 := bstep (se 1 (by rfl) ⟨481877, by rfl⟩ : syracuseStep 642503 = 963755) B963755
theorem B642857 : Blo 424774 642857 := bstep (se 2 (by rfl) ⟨241071, by rfl⟩ : syracuseStep 642857 = 482143) B482143
theorem B642863 : Blo 424774 642863 := bstep (se 1 (by rfl) ⟨482147, by rfl⟩ : syracuseStep 642863 = 964295) B964295
theorem B2084923 : Blo 424774 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B2740553 : Blo 424774 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B479839 : Blo 424774 479839 := bstep (se 1 (by rfl) ⟨359879, by rfl⟩ : syracuseStep 479839 = 719759) B719759
theorem B11686517 : Blo 424774 11686517 := bstep (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) B1095611
theorem B545503 : Blo 424774 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B1954655 : Blo 424774 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2151521 : Blo 424774 2151521 := bstep (se 2 (by rfl) ⟨806820, by rfl⟩ : syracuseStep 2151521 = 1613641) B1613641
theorem B5002397 : Blo 424774 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B1463539 : Blo 424774 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B1824095 : Blo 424774 1824095 := bstep (se 1 (by rfl) ⟨1368071, by rfl⟩ : syracuseStep 1824095 = 2736143) B2736143
theorem B1627553 : Blo 424774 1627553 := bstep (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) B1220665
theorem B578983 : Blo 424774 578983 := bstep (se 1 (by rfl) ⟨434237, by rfl⟩ : syracuseStep 578983 = 868475) B868475
theorem B4118053 : Blo 424774 4118053 := bstep (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) B772135
theorem B9655853 : Blo 424774 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B480991 : Blo 424774 480991 := bstep (se 1 (by rfl) ⟨360743, by rfl⟩ : syracuseStep 480991 = 721487) B721487
theorem B2316215 : Blo 424774 2316215 := bstep (se 1 (by rfl) ⟨1737161, by rfl⟩ : syracuseStep 2316215 = 3474323) B3474323
theorem B2185481 : Blo 424774 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B481567 : Blo 424774 481567 := bstep (se 1 (by rfl) ⟨361175, by rfl⟩ : syracuseStep 481567 = 722351) B722351
theorem B809327 : Blo 424774 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B2087279 : Blo 424774 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1366483 : Blo 424774 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B1464895 : Blo 424774 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B481855 : Blo 424774 481855 := bstep (se 1 (by rfl) ⟨361391, by rfl⟩ : syracuseStep 481855 = 722783) B722783
theorem B4086683 : Blo 424774 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B2153789 : Blo 424774 2153789 := bstep (se 3 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 2153789 = 807671) B807671
theorem B810337 : Blo 424774 810337 := bstep (se 2 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 810337 = 607753) B607753
theorem B1170875 : Blo 424774 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B2186833 : Blo 424774 2186833 := bstep (se 2 (by rfl) ⟨820062, by rfl⟩ : syracuseStep 2186833 = 1640125) B1640125
theorem B3662131 : Blo 424774 3662131 := bstep (se 1 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 3662131 = 5493197) B5493197
theorem B6382091 : Blo 424774 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1434131 : Blo 424774 1434131 := bstep (se 1 (by rfl) ⟨1075598, by rfl⟩ : syracuseStep 1434131 = 2151197) B2151197
theorem B4842017 : Blo 424774 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B909895 : Blo 424774 909895 := bstep (se 1 (by rfl) ⟨682421, by rfl⟩ : syracuseStep 909895 = 1364843) B1364843
theorem B811795 : Blo 424774 811795 := bstep (se 1 (by rfl) ⟨608846, by rfl⟩ : syracuseStep 811795 = 1217693) B1217693
theorem B1827785 : Blo 424774 1827785 := bstep (se 2 (by rfl) ⟨685419, by rfl⟩ : syracuseStep 1827785 = 1370839) B1370839
theorem B648425 : Blo 424774 648425 := bstep (se 2 (by rfl) ⟨243159, by rfl⟩ : syracuseStep 648425 = 486319) B486319
theorem B8185211 : Blo 424774 8185211 := bstep (se 1 (by rfl) ⟨6138908, by rfl⟩ : syracuseStep 8185211 = 12277817) B12277817
theorem B812425 : Blo 424774 812425 := bstep (se 2 (by rfl) ⟨304659, by rfl⟩ : syracuseStep 812425 = 609319) B609319
theorem B2156219 : Blo 424774 2156219 := bstep (se 1 (by rfl) ⟨1617164, by rfl⟩ : syracuseStep 2156219 = 3234329) B3234329
theorem B911083 : Blo 424774 911083 := bstep (se 1 (by rfl) ⟨683312, by rfl⟩ : syracuseStep 911083 = 1366625) B1366625
theorem B1369943 : Blo 424774 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B3467215 : Blo 424774 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B1435913 : Blo 424774 1435913 := bstep (se 2 (by rfl) ⟨538467, by rfl⟩ : syracuseStep 1435913 = 1076935) B1076935
theorem B1075639 : Blo 424774 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B911945 : Blo 424774 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B4877009 : Blo 424774 4877009 := bstep (se 2 (by rfl) ⟨1828878, by rfl⟩ : syracuseStep 4877009 = 3657757) B3657757
theorem B1829699 : Blo 424774 1829699 := bstep (se 1 (by rfl) ⟨1372274, by rfl⟩ : syracuseStep 1829699 = 2744549) B2744549
theorem B1437047 : Blo 424774 1437047 := bstep (se 1 (by rfl) ⟨1077785, by rfl⟩ : syracuseStep 1437047 = 2155571) B2155571
theorem B2158163 : Blo 424774 2158163 := bstep (se 1 (by rfl) ⟨1618622, by rfl⟩ : syracuseStep 2158163 = 3237245) B3237245
theorem B3632849 : Blo 424774 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B1077047 : Blo 424774 1077047 := bstep (se 1 (by rfl) ⟨807785, by rfl⟩ : syracuseStep 1077047 = 1615571) B1615571
theorem B683831 : Blo 424774 683831 := bstep (se 1 (by rfl) ⟨512873, by rfl⟩ : syracuseStep 683831 = 1025747) B1025747
theorem B1077097 : Blo 424774 1077097 := bstep (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) B807823
theorem B2191369 : Blo 424774 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B23588981 : Blo 424774 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B717167 : Blo 424774 717167 := bstep (se 1 (by rfl) ⟨537875, by rfl⟩ : syracuseStep 717167 = 1075751) B1075751
theorem B1438127 : Blo 424774 1438127 := bstep (se 1 (by rfl) ⟨1078595, by rfl⟩ : syracuseStep 1438127 = 2157191) B2157191
theorem B717383 : Blo 424774 717383 := bstep (se 1 (by rfl) ⟨538037, by rfl⟩ : syracuseStep 717383 = 1076075) B1076075
theorem B3240647 : Blo 424774 3240647 := bstep (se 1 (by rfl) ⟨2430485, by rfl⟩ : syracuseStep 3240647 = 4860971) B4860971
theorem B684767 : Blo 424774 684767 := bstep (se 1 (by rfl) ⟨513575, by rfl⟩ : syracuseStep 684767 = 1027151) B1027151
theorem B717815 : Blo 424774 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B1635527 : Blo 424774 1635527 := bstep (se 1 (by rfl) ⟨1226645, by rfl⟩ : syracuseStep 1635527 = 2453291) B2453291
theorem B1078505 : Blo 424774 1078505 := bstep (se 2 (by rfl) ⟨404439, by rfl⟩ : syracuseStep 1078505 = 808879) B808879
theorem B1439099 : Blo 424774 1439099 := bstep (se 1 (by rfl) ⟨1079324, by rfl⟩ : syracuseStep 1439099 = 2158649) B2158649
theorem B1078667 : Blo 424774 1078667 := bstep (se 1 (by rfl) ⟨809000, by rfl⟩ : syracuseStep 1078667 = 1618001) B1618001
theorem B1078879 : Blo 424774 1078879 := bstep (se 1 (by rfl) ⟨809159, by rfl⟩ : syracuseStep 1078879 = 1618319) B1618319
theorem B718571 : Blo 424774 718571 := bstep (se 1 (by rfl) ⟨538928, by rfl⟩ : syracuseStep 718571 = 1077857) B1077857
theorem B9598907 : Blo 424774 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B1079507 : Blo 424774 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B2161079 : Blo 424774 2161079 := bstep (se 1 (by rfl) ⟨1620809, by rfl⟩ : syracuseStep 2161079 = 3241619) B3241619
theorem B3635887 : Blo 424774 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B719543 : Blo 424774 719543 := bstep (se 1 (by rfl) ⟨539657, by rfl⟩ : syracuseStep 719543 = 1079315) B1079315
theorem B1440503 : Blo 424774 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B424859 : Blo 424774 424859 := bstep (se 1 (by rfl) ⟨318644, by rfl⟩ : syracuseStep 424859 = 637289) B637289
theorem B424911 : Blo 424774 424911 := bstep (se 1 (by rfl) ⟨318683, by rfl⟩ : syracuseStep 424911 = 637367) B637367
theorem B424935 : Blo 424774 424935 := bstep (se 1 (by rfl) ⟨318701, by rfl⟩ : syracuseStep 424935 = 637403) B637403
theorem B8191205 : Blo 424774 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B425247 : Blo 424774 425247 := bstep (se 1 (by rfl) ⟨318935, by rfl⟩ : syracuseStep 425247 = 637871) B637871
theorem B1965379 : Blo 424774 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B425307 : Blo 424774 425307 := bstep (se 1 (by rfl) ⟨318980, by rfl⟩ : syracuseStep 425307 = 637961) B637961
theorem B425327 : Blo 424774 425327 := bstep (se 1 (by rfl) ⟨318995, by rfl⟩ : syracuseStep 425327 = 637991) B637991
theorem B720265 : Blo 424774 720265 := bstep (se 2 (by rfl) ⟨270099, by rfl⟩ : syracuseStep 720265 = 540199) B540199
theorem B425383 : Blo 424774 425383 := bstep (se 1 (by rfl) ⟨319037, by rfl⟩ : syracuseStep 425383 = 638075) B638075
theorem B3276247 : Blo 424774 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B425467 : Blo 424774 425467 := bstep (se 1 (by rfl) ⟨319100, by rfl⟩ : syracuseStep 425467 = 638201) B638201
theorem B425535 : Blo 424774 425535 := bstep (se 1 (by rfl) ⟨319151, by rfl⟩ : syracuseStep 425535 = 638303) B638303
theorem B425543 : Blo 424774 425543 := bstep (se 1 (by rfl) ⟨319157, by rfl⟩ : syracuseStep 425543 = 638315) B638315
theorem B3079775 : Blo 424774 3079775 := bstep (se 1 (by rfl) ⟨2309831, by rfl⟩ : syracuseStep 3079775 = 4619663) B4619663
theorem B425695 : Blo 424774 425695 := bstep (se 1 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 425695 = 638543) B638543
theorem B425775 : Blo 424774 425775 := bstep (se 1 (by rfl) ⟨319331, by rfl⟩ : syracuseStep 425775 = 638663) B638663
theorem B1441583 : Blo 424774 1441583 := bstep (se 1 (by rfl) ⟨1081187, by rfl⟩ : syracuseStep 1441583 = 2162375) B2162375
theorem B720697 : Blo 424774 720697 := bstep (se 2 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 720697 = 540523) B540523
theorem B425883 : Blo 424774 425883 := bstep (se 1 (by rfl) ⟨319412, by rfl⟩ : syracuseStep 425883 = 638825) B638825
theorem B1212317 : Blo 424774 1212317 := bstep (se 3 (by rfl) ⟨227309, by rfl⟩ : syracuseStep 1212317 = 454619) B454619
theorem B425935 : Blo 424774 425935 := bstep (se 1 (by rfl) ⟨319451, by rfl⟩ : syracuseStep 425935 = 638903) B638903
theorem B425959 : Blo 424774 425959 := bstep (se 1 (by rfl) ⟨319469, by rfl⟩ : syracuseStep 425959 = 638939) B638939
theorem B426215 : Blo 424774 426215 := bstep (se 1 (by rfl) ⟨319661, by rfl⟩ : syracuseStep 426215 = 639323) B639323
theorem B721183 : Blo 424774 721183 := bstep (se 1 (by rfl) ⟨540887, by rfl⟩ : syracuseStep 721183 = 1081775) B1081775
theorem B426367 : Blo 424774 426367 := bstep (se 1 (by rfl) ⟨319775, by rfl⟩ : syracuseStep 426367 = 639551) B639551
theorem B4882841 : Blo 424774 4882841 := bstep (se 2 (by rfl) ⟨1831065, by rfl⟩ : syracuseStep 4882841 = 3662131) B3662131
theorem B1442231 : Blo 424774 1442231 := bstep (se 1 (by rfl) ⟨1081673, by rfl⟩ : syracuseStep 1442231 = 2163347) B2163347
theorem B426447 : Blo 424774 426447 := bstep (se 1 (by rfl) ⟨319835, by rfl⟩ : syracuseStep 426447 = 639671) B639671
theorem B3080699 : Blo 424774 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B426599 : Blo 424774 426599 := bstep (se 1 (by rfl) ⟨319949, by rfl⟩ : syracuseStep 426599 = 639899) B639899
theorem B1966787 : Blo 424774 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B1213193 : Blo 424774 1213193 := bstep (se 2 (by rfl) ⟨454947, by rfl⟩ : syracuseStep 1213193 = 909895) B909895
theorem B426863 : Blo 424774 426863 := bstep (se 1 (by rfl) ⟨320147, by rfl⟩ : syracuseStep 426863 = 640295) B640295
theorem B1442717 : Blo 424774 1442717 := bstep (se 3 (by rfl) ⟨270509, by rfl⟩ : syracuseStep 1442717 = 541019) B541019
theorem B426919 : Blo 424774 426919 := bstep (se 1 (by rfl) ⟨320189, by rfl⟩ : syracuseStep 426919 = 640379) B640379
theorem B721831 : Blo 424774 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B1442771 : Blo 424774 1442771 := bstep (se 1 (by rfl) ⟨1082078, by rfl⟩ : syracuseStep 1442771 = 2164157) B2164157
theorem B427003 : Blo 424774 427003 := bstep (se 1 (by rfl) ⟨320252, by rfl⟩ : syracuseStep 427003 = 640505) B640505
theorem B1082393 : Blo 424774 1082393 := bstep (se 2 (by rfl) ⟨405897, by rfl⟩ : syracuseStep 1082393 = 811795) B811795
theorem B427071 : Blo 424774 427071 := bstep (se 1 (by rfl) ⟨320303, by rfl⟩ : syracuseStep 427071 = 640607) B640607
theorem B721993 : Blo 424774 721993 := bstep (se 2 (by rfl) ⟨270747, by rfl⟩ : syracuseStep 721993 = 541495) B541495
theorem B722027 : Blo 424774 722027 := bstep (se 1 (by rfl) ⟨541520, by rfl⟩ : syracuseStep 722027 = 1083041) B1083041
theorem B427215 : Blo 424774 427215 := bstep (se 1 (by rfl) ⟨320411, by rfl⟩ : syracuseStep 427215 = 640823) B640823
theorem B427419 : Blo 424774 427419 := bstep (se 1 (by rfl) ⟨320564, by rfl⟩ : syracuseStep 427419 = 641129) B641129
theorem B2426273 : Blo 424774 2426273 := bstep (se 2 (by rfl) ⟨909852, by rfl⟩ : syracuseStep 2426273 = 1819705) B1819705
theorem B1738199 : Blo 424774 1738199 := bstep (se 1 (by rfl) ⟨1303649, by rfl⟩ : syracuseStep 1738199 = 2607299) B2607299
theorem B2164319 : Blo 424774 2164319 := bstep (se 1 (by rfl) ⟨1623239, by rfl⟩ : syracuseStep 2164319 = 3246479) B3246479
theorem B427631 : Blo 424774 427631 := bstep (se 1 (by rfl) ⟨320723, by rfl⟩ : syracuseStep 427631 = 641447) B641447
theorem B7308953 : Blo 424774 7308953 := bstep (se 2 (by rfl) ⟨2740857, by rfl⟩ : syracuseStep 7308953 = 5481715) B5481715
theorem B788135 : Blo 424774 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B427687 : Blo 424774 427687 := bstep (se 1 (by rfl) ⟨320765, by rfl⟩ : syracuseStep 427687 = 641531) B641531
theorem B427771 : Blo 424774 427771 := bstep (se 1 (by rfl) ⟨320828, by rfl⟩ : syracuseStep 427771 = 641657) B641657
theorem B427807 : Blo 424774 427807 := bstep (se 1 (by rfl) ⟨320855, by rfl⟩ : syracuseStep 427807 = 641711) B641711
theorem B427839 : Blo 424774 427839 := bstep (se 1 (by rfl) ⟨320879, by rfl⟩ : syracuseStep 427839 = 641759) B641759
theorem B1083233 : Blo 424774 1083233 := bstep (se 2 (by rfl) ⟨406212, by rfl⟩ : syracuseStep 1083233 = 812425) B812425
theorem B2459591 : Blo 424774 2459591 := bstep (se 1 (by rfl) ⟨1844693, by rfl⟩ : syracuseStep 2459591 = 3689387) B3689387
theorem B428015 : Blo 424774 428015 := bstep (se 1 (by rfl) ⟨321011, by rfl⟩ : syracuseStep 428015 = 642023) B642023
theorem B428187 : Blo 424774 428187 := bstep (se 1 (by rfl) ⟨321140, by rfl⟩ : syracuseStep 428187 = 642281) B642281
theorem B428223 : Blo 424774 428223 := bstep (se 1 (by rfl) ⟨321167, by rfl⟩ : syracuseStep 428223 = 642335) B642335
theorem B428335 : Blo 424774 428335 := bstep (se 1 (by rfl) ⟨321251, by rfl⟩ : syracuseStep 428335 = 642503) B642503
theorem B1214777 : Blo 424774 1214777 := bstep (se 2 (by rfl) ⟨455541, by rfl⟩ : syracuseStep 1214777 = 911083) B911083
theorem B723323 : Blo 424774 723323 := bstep (se 1 (by rfl) ⟨542492, by rfl⟩ : syracuseStep 723323 = 1084985) B1084985
theorem B428571 : Blo 424774 428571 := bstep (se 1 (by rfl) ⟨321428, by rfl⟩ : syracuseStep 428571 = 642857) B642857
theorem B428575 : Blo 424774 428575 := bstep (se 1 (by rfl) ⟨321431, by rfl⟩ : syracuseStep 428575 = 642863) B642863
theorem B4622953 : Blo 424774 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B1444985 : Blo 424774 1444985 := bstep (se 2 (by rfl) ⟨541869, by rfl⟩ : syracuseStep 1444985 = 1083739) B1083739
theorem B1445309 : Blo 424774 1445309 := bstep (se 3 (by rfl) ⟨270995, by rfl⟩ : syracuseStep 1445309 = 541991) B541991
theorem B1216063 : Blo 424774 1216063 := bstep (se 1 (by rfl) ⟨912047, by rfl⟩ : syracuseStep 1216063 = 1824095) B1824095
theorem B1085035 : Blo 424774 1085035 := bstep (se 1 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 1085035 = 1627553) B1627553
theorem B1544143 : Blo 424774 1544143 := bstep (se 1 (by rfl) ⟨1158107, by rfl⟩ : syracuseStep 1544143 = 2316215) B2316215
theorem B7966673 : Blo 424774 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B5443685 : Blo 424774 5443685 := bstep (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) B1020691
theorem B1446011 : Blo 424774 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B1446173 : Blo 424774 1446173 := bstep (se 3 (by rfl) ⟨271157, by rfl⟩ : syracuseStep 1446173 = 542315) B542315
theorem B1446281 : Blo 424774 1446281 := bstep (se 2 (by rfl) ⟨542355, by rfl⟩ : syracuseStep 1446281 = 1084711) B1084711
theorem B2724455 : Blo 424774 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B3937085 : Blo 424774 3937085 := bstep (se 3 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 3937085 = 1476407) B1476407
theorem B6132793 : Blo 424774 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B2921825 : Blo 424774 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B2430395 : Blo 424774 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B956087 : Blo 424774 956087 := bstep (se 1 (by rfl) ⟨717065, by rfl⟩ : syracuseStep 956087 = 1434131) B1434131
theorem B727337 : Blo 424774 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B1317599 : Blo 424774 1317599 := bstep (se 1 (by rfl) ⟨988199, by rfl⟩ : syracuseStep 1317599 = 1976399) B1976399
theorem B957275 : Blo 424774 957275 := bstep (se 1 (by rfl) ⟨717956, by rfl⟩ : syracuseStep 957275 = 1435913) B1435913
theorem B2431853 : Blo 424774 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B3251339 : Blo 424774 3251339 := bstep (se 1 (by rfl) ⟨2438504, by rfl⟩ : syracuseStep 3251339 = 4877009) B4877009
theorem B1219799 : Blo 424774 1219799 := bstep (se 1 (by rfl) ⟨914849, by rfl⟩ : syracuseStep 1219799 = 1829699) B1829699
theorem B10690127 : Blo 424774 10690127 := bstep (se 1 (by rfl) ⟨8017595, by rfl⟩ : syracuseStep 10690127 = 16035191) B16035191
theorem B958031 : Blo 424774 958031 := bstep (se 1 (by rfl) ⟨718523, by rfl⟩ : syracuseStep 958031 = 1437047) B1437047
theorem B6757967 : Blo 424774 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1580687 : Blo 424774 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B958751 : Blo 424774 958751 := bstep (se 1 (by rfl) ⟨719063, by rfl⟩ : syracuseStep 958751 = 1438127) B1438127
theorem B2433311 : Blo 424774 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B1319375 : Blo 424774 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B1090351 : Blo 424774 1090351 := bstep (se 1 (by rfl) ⟨817763, by rfl⟩ : syracuseStep 1090351 = 1635527) B1635527
theorem B959399 : Blo 424774 959399 := bstep (se 1 (by rfl) ⟨719549, by rfl⟩ : syracuseStep 959399 = 1439099) B1439099
theorem B5448707 : Blo 424774 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B3122333 : Blo 424774 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B6399271 : Blo 424774 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B960335 : Blo 424774 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B960353 : Blo 424774 960353 := bstep (se 2 (by rfl) ⟨360132, by rfl⟩ : syracuseStep 960353 = 720265) B720265
theorem B4368329 : Blo 424774 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B5187779 : Blo 424774 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B1026361 : Blo 424774 1026361 := bstep (se 2 (by rfl) ⟨384885, by rfl⟩ : syracuseStep 1026361 = 769771) B769771
theorem B960929 : Blo 424774 960929 := bstep (se 2 (by rfl) ⟨360348, by rfl⟩ : syracuseStep 960929 = 720697) B720697
theorem B961055 : Blo 424774 961055 := bstep (se 1 (by rfl) ⟨720791, by rfl⟩ : syracuseStep 961055 = 1441583) B1441583
theorem B8792651 : Blo 424774 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B11119589 : Blo 424774 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B1617803 : Blo 424774 1617803 := bstep (se 1 (by rfl) ⟨1213352, by rfl⟩ : syracuseStep 1617803 = 2426705) B2426705
theorem B962459 : Blo 424774 962459 := bstep (se 1 (by rfl) ⟨721844, by rfl⟩ : syracuseStep 962459 = 1443689) B1443689
theorem B17018909 : Blo 424774 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B5189683 : Blo 424774 5189683 := bstep (se 1 (by rfl) ⟨3892262, by rfl⟩ : syracuseStep 5189683 = 7784525) B7784525
theorem B17576099 : Blo 424774 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B962747 : Blo 424774 962747 := bstep (se 1 (by rfl) ⟨722060, by rfl⟩ : syracuseStep 962747 = 1444121) B1444121
theorem B766441 : Blo 424774 766441 := bstep (se 2 (by rfl) ⟨287415, by rfl⟩ : syracuseStep 766441 = 574831) B574831
theorem B2732555 : Blo 424774 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B963233 : Blo 424774 963233 := bstep (se 2 (by rfl) ⟨361212, by rfl⟩ : syracuseStep 963233 = 722425) B722425
theorem B963593 : Blo 424774 963593 := bstep (se 2 (by rfl) ⟨361347, by rfl⟩ : syracuseStep 963593 = 722695) B722695
theorem B963647 : Blo 424774 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B2733887 : Blo 424774 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B964583 : Blo 424774 964583 := bstep (se 1 (by rfl) ⟨723437, by rfl⟩ : syracuseStep 964583 = 1446875) B1446875
theorem B964601 : Blo 424774 964601 := bstep (se 2 (by rfl) ⟨361725, by rfl⟩ : syracuseStep 964601 = 723451) B723451
theorem B964691 : Blo 424774 964691 := bstep (se 1 (by rfl) ⟨723518, by rfl⟩ : syracuseStep 964691 = 1447037) B1447037
theorem B22132909 : Blo 424774 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B637163 : Blo 424774 637163 := bstep (se 1 (by rfl) ⟨477872, by rfl⟩ : syracuseStep 637163 = 955745) B955745
theorem B637223 : Blo 424774 637223 := bstep (se 1 (by rfl) ⟨477917, by rfl⟩ : syracuseStep 637223 = 955835) B955835
theorem B637307 : Blo 424774 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B768379 : Blo 424774 768379 := bstep (se 1 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 768379 = 1152569) B1152569
theorem B637577 : Blo 424774 637577 := bstep (se 2 (by rfl) ⟨239091, by rfl⟩ : syracuseStep 637577 = 478183) B478183
theorem B637751 : Blo 424774 637751 := bstep (se 1 (by rfl) ⟨478313, by rfl⟩ : syracuseStep 637751 = 956627) B956627
theorem B637787 : Blo 424774 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B1456987 : Blo 424774 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B539551 : Blo 424774 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B1391519 : Blo 424774 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B637931 : Blo 424774 637931 := bstep (se 1 (by rfl) ⟨478448, by rfl⟩ : syracuseStep 637931 = 956897) B956897
theorem B638135 : Blo 424774 638135 := bstep (se 1 (by rfl) ⟨478601, by rfl⟩ : syracuseStep 638135 = 957203) B957203
theorem B638375 : Blo 424774 638375 := bstep (se 1 (by rfl) ⟨478781, by rfl⟩ : syracuseStep 638375 = 957563) B957563
theorem B2735527 : Blo 424774 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B638459 : Blo 424774 638459 := bstep (se 1 (by rfl) ⟨478844, by rfl⟩ : syracuseStep 638459 = 957689) B957689
theorem B638555 : Blo 424774 638555 := bstep (se 1 (by rfl) ⟨478916, by rfl⟩ : syracuseStep 638555 = 957833) B957833
theorem B638639 : Blo 424774 638639 := bstep (se 1 (by rfl) ⟨478979, by rfl⟩ : syracuseStep 638639 = 957959) B957959
theorem B1621691 : Blo 424774 1621691 := bstep (se 1 (by rfl) ⟨1216268, by rfl⟩ : syracuseStep 1621691 = 2432537) B2432537
theorem B638759 : Blo 424774 638759 := bstep (se 1 (by rfl) ⟨479069, by rfl⟩ : syracuseStep 638759 = 958139) B958139
theorem B5816123 : Blo 424774 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B638843 : Blo 424774 638843 := bstep (se 1 (by rfl) ⟨479132, by rfl⟩ : syracuseStep 638843 = 958265) B958265
theorem B1228733 : Blo 424774 1228733 := bstep (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) B460775
theorem B639263 : Blo 424774 639263 := bstep (se 1 (by rfl) ⟨479447, by rfl⟩ : syracuseStep 639263 = 958895) B958895
theorem B639287 : Blo 424774 639287 := bstep (se 1 (by rfl) ⟨479465, by rfl⟩ : syracuseStep 639287 = 958931) B958931
theorem B3228011 : Blo 424774 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B639359 : Blo 424774 639359 := bstep (se 1 (by rfl) ⟨479519, by rfl⟩ : syracuseStep 639359 = 959039) B959039
theorem B639431 : Blo 424774 639431 := bstep (se 1 (by rfl) ⟨479573, by rfl⟩ : syracuseStep 639431 = 959147) B959147
theorem B639785 : Blo 424774 639785 := bstep (se 2 (by rfl) ⟨239919, by rfl⟩ : syracuseStep 639785 = 479839) B479839
theorem B639791 : Blo 424774 639791 := bstep (se 1 (by rfl) ⟨479843, by rfl⟩ : syracuseStep 639791 = 959687) B959687
theorem B5456807 : Blo 424774 5456807 := bstep (se 1 (by rfl) ⟨4092605, by rfl⟩ : syracuseStep 5456807 = 8185211) B8185211
theorem B639911 : Blo 424774 639911 := bstep (se 1 (by rfl) ⟨479933, by rfl⟩ : syracuseStep 639911 = 959867) B959867
theorem B639995 : Blo 424774 639995 := bstep (se 1 (by rfl) ⟨479996, by rfl⟩ : syracuseStep 639995 = 959993) B959993
theorem B640055 : Blo 424774 640055 := bstep (se 1 (by rfl) ⟨480041, by rfl⟩ : syracuseStep 640055 = 960083) B960083
theorem B640175 : Blo 424774 640175 := bstep (se 1 (by rfl) ⟨480131, by rfl⟩ : syracuseStep 640175 = 960263) B960263
theorem B9225485 : Blo 424774 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B3065363 : Blo 424774 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B640583 : Blo 424774 640583 := bstep (se 1 (by rfl) ⟨480437, by rfl⟩ : syracuseStep 640583 = 960875) B960875
theorem B2737759 : Blo 424774 2737759 := bstep (se 1 (by rfl) ⟨2053319, by rfl⟩ : syracuseStep 2737759 = 4106639) B4106639
theorem B1951385 : Blo 424774 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B640679 : Blo 424774 640679 := bstep (se 1 (by rfl) ⟨480509, by rfl⟩ : syracuseStep 640679 = 961019) B961019
theorem B640763 : Blo 424774 640763 := bstep (se 1 (by rfl) ⟨480572, by rfl⟩ : syracuseStep 640763 = 961145) B961145
theorem B640799 : Blo 424774 640799 := bstep (se 1 (by rfl) ⟨480599, by rfl⟩ : syracuseStep 640799 = 961199) B961199
theorem B640847 : Blo 424774 640847 := bstep (se 1 (by rfl) ⟨480635, by rfl⟩ : syracuseStep 640847 = 961271) B961271
theorem B771977 : Blo 424774 771977 := bstep (se 2 (by rfl) ⟨289491, by rfl⟩ : syracuseStep 771977 = 578983) B578983
theorem B640967 : Blo 424774 640967 := bstep (se 1 (by rfl) ⟨480725, by rfl⟩ : syracuseStep 640967 = 961451) B961451
theorem B5490737 : Blo 424774 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B641321 : Blo 424774 641321 := bstep (se 2 (by rfl) ⟨240495, by rfl⟩ : syracuseStep 641321 = 480991) B480991
theorem B641327 : Blo 424774 641327 := bstep (se 1 (by rfl) ⟨480995, by rfl⟩ : syracuseStep 641327 = 961991) B961991
theorem B1362433 : Blo 424774 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B641567 : Blo 424774 641567 := bstep (se 1 (by rfl) ⟨481175, by rfl⟩ : syracuseStep 641567 = 962351) B962351
theorem B1624607 : Blo 424774 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B478111 : Blo 424774 478111 := bstep (se 1 (by rfl) ⟨358583, by rfl⟩ : syracuseStep 478111 = 717167) B717167
theorem B641951 : Blo 424774 641951 := bstep (se 1 (by rfl) ⟨481463, by rfl⟩ : syracuseStep 641951 = 962927) B962927
theorem B641999 : Blo 424774 641999 := bstep (se 1 (by rfl) ⟨481499, by rfl⟩ : syracuseStep 641999 = 962999) B962999
theorem B642089 : Blo 424774 642089 := bstep (se 2 (by rfl) ⟨240783, by rfl⟩ : syracuseStep 642089 = 481567) B481567
theorem B478255 : Blo 424774 478255 := bstep (se 1 (by rfl) ⟨358691, by rfl⟩ : syracuseStep 478255 = 717383) B717383
theorem B642095 : Blo 424774 642095 := bstep (se 1 (by rfl) ⟨481571, by rfl⟩ : syracuseStep 642095 = 963143) B963143
theorem B642119 : Blo 424774 642119 := bstep (se 1 (by rfl) ⟨481589, by rfl⟩ : syracuseStep 642119 = 963179) B963179
theorem B1821977 : Blo 424774 1821977 := bstep (se 2 (by rfl) ⟨683241, by rfl⟩ : syracuseStep 1821977 = 1366483) B1366483
theorem B478543 : Blo 424774 478543 := bstep (se 1 (by rfl) ⟨358907, by rfl⟩ : syracuseStep 478543 = 717815) B717815
theorem B642383 : Blo 424774 642383 := bstep (se 1 (by rfl) ⟨481787, by rfl⟩ : syracuseStep 642383 = 963575) B963575
theorem B1953193 : Blo 424774 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B642473 : Blo 424774 642473 := bstep (se 2 (by rfl) ⟨240927, by rfl⟩ : syracuseStep 642473 = 481855) B481855
theorem B642623 : Blo 424774 642623 := bstep (se 1 (by rfl) ⟨481967, by rfl⟩ : syracuseStep 642623 = 963935) B963935
theorem B479047 : Blo 424774 479047 := bstep (se 1 (by rfl) ⟨359285, by rfl⟩ : syracuseStep 479047 = 718571) B718571
theorem B642887 : Blo 424774 642887 := bstep (se 1 (by rfl) ⟨482165, by rfl⟩ : syracuseStep 642887 = 964331) B964331
theorem B1363817 : Blo 424774 1363817 := bstep (se 2 (by rfl) ⟨511431, by rfl⟩ : syracuseStep 1363817 = 1022863) B1022863
theorem B642971 : Blo 424774 642971 := bstep (se 1 (by rfl) ⟨482228, by rfl⟩ : syracuseStep 642971 = 964457) B964457
theorem B2740243 : Blo 424774 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B1331329 : Blo 424774 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B479695 : Blo 424774 479695 := bstep (se 1 (by rfl) ⟨359771, by rfl⟩ : syracuseStep 479695 = 719543) B719543
theorem B2151035 : Blo 424774 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B5460803 : Blo 424774 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B3658715 : Blo 424774 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B4871177 : Blo 424774 4871177 := bstep (se 2 (by rfl) ⟨1826691, by rfl⟩ : syracuseStep 4871177 = 3653383) B3653383
theorem B2053183 : Blo 424774 2053183 := bstep (se 1 (by rfl) ⟨1539887, by rfl⟩ : syracuseStep 2053183 = 3079775) B3079775
theorem B808211 : Blo 424774 808211 := bstep (se 1 (by rfl) ⟨606158, by rfl⟩ : syracuseStep 808211 = 1212317) B1212317
theorem B3298657 : Blo 424774 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B480667 : Blo 424774 480667 := bstep (se 1 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 480667 = 721001) B721001
theorem B19650059 : Blo 424774 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B808841 : Blo 424774 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B4085761 : Blo 424774 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B547355 : Blo 424774 547355 := bstep (se 1 (by rfl) ⟨410516, by rfl⟩ : syracuseStep 547355 = 821033) B821033
theorem B481819 : Blo 424774 481819 := bstep (se 1 (by rfl) ⟨361364, by rfl⟩ : syracuseStep 481819 = 722729) B722729
theorem B645943 : Blo 424774 645943 := bstep (se 1 (by rfl) ⟨484457, by rfl⟩ : syracuseStep 645943 = 968915) B968915
theorem B1727315 : Blo 424774 1727315 := bstep (se 1 (by rfl) ⟨1295486, by rfl⟩ : syracuseStep 1727315 = 2590973) B2590973
theorem B810587 : Blo 424774 810587 := bstep (se 1 (by rfl) ⟨607940, by rfl⟩ : syracuseStep 810587 = 1215881) B1215881
theorem B810823 : Blo 424774 810823 := bstep (se 1 (by rfl) ⟨608117, by rfl⟩ : syracuseStep 810823 = 1216235) B1216235
theorem B4874093 : Blo 424774 4874093 := bstep (se 3 (by rfl) ⟨913892, by rfl⟩ : syracuseStep 4874093 = 1827785) B1827785
theorem B1728647 : Blo 424774 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B1827035 : Blo 424774 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B1532191 : Blo 424774 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B7791011 : Blo 424774 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B1729001 : Blo 424774 1729001 := bstep (se 2 (by rfl) ⟨648375, by rfl⟩ : syracuseStep 1729001 = 1296751) B1296751
theorem B1303103 : Blo 424774 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B1434185 : Blo 424774 1434185 := bstep (se 2 (by rfl) ⟨537819, by rfl⟩ : syracuseStep 1434185 = 1075639) B1075639
theorem B1729133 : Blo 424774 1729133 := bstep (se 3 (by rfl) ⟨324212, by rfl⟩ : syracuseStep 1729133 = 648425) B648425
theorem B1434347 : Blo 424774 1434347 := bstep (se 1 (by rfl) ⟨1075760, by rfl⟩ : syracuseStep 1434347 = 2151521) B2151521
theorem B3334931 : Blo 424774 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B7037725 : Blo 424774 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B615215 : Blo 424774 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B25748941 : Blo 424774 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B681691 : Blo 424774 681691 := bstep (se 1 (by rfl) ⟨511268, by rfl⟩ : syracuseStep 681691 = 1022537) B1022537
theorem B812767 : Blo 424774 812767 := bstep (se 1 (by rfl) ⟨609575, by rfl⟩ : syracuseStep 812767 = 1219151) B1219151
theorem B682139 : Blo 424774 682139 := bstep (se 1 (by rfl) ⟨511604, by rfl⟩ : syracuseStep 682139 = 1023209) B1023209
theorem B1435859 : Blo 424774 1435859 := bstep (se 1 (by rfl) ⟨1076894, by rfl⟩ : syracuseStep 1435859 = 2153789) B2153789
theorem B1436129 : Blo 424774 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B5008391 : Blo 424774 5008391 := bstep (se 1 (by rfl) ⟨3756293, by rfl⟩ : syracuseStep 5008391 = 7512587) B7512587
theorem B1535219 : Blo 424774 1535219 := bstep (se 1 (by rfl) ⟨1151414, by rfl⟩ : syracuseStep 1535219 = 2302829) B2302829
theorem B1437479 : Blo 424774 1437479 := bstep (se 1 (by rfl) ⟨1078109, by rfl⟩ : syracuseStep 1437479 = 2156219) B2156219
theorem B913295 : Blo 424774 913295 := bstep (se 1 (by rfl) ⟨684971, by rfl⟩ : syracuseStep 913295 = 1369943) B1369943
theorem B1077371 : Blo 424774 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B1536185 : Blo 424774 1536185 := bstep (se 2 (by rfl) ⟨576069, by rfl⟩ : syracuseStep 1536185 = 1152139) B1152139
theorem B3076289 : Blo 424774 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B18412217 : Blo 424774 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B684779 : Blo 424774 684779 := bstep (se 1 (by rfl) ⟨513584, by rfl⟩ : syracuseStep 684779 = 1027169) B1027169
theorem B1438505 : Blo 424774 1438505 := bstep (se 2 (by rfl) ⟨539439, by rfl⟩ : syracuseStep 1438505 = 1078879) B1078879
theorem B1438775 : Blo 424774 1438775 := bstep (se 1 (by rfl) ⟨1079081, by rfl⟩ : syracuseStep 1438775 = 2158163) B2158163
theorem B2421899 : Blo 424774 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B718031 : Blo 424774 718031 := bstep (se 1 (by rfl) ⟨538523, by rfl⟩ : syracuseStep 718031 = 1077047) B1077047
theorem B455887 : Blo 424774 455887 := bstep (se 1 (by rfl) ⟨341915, by rfl⟩ : syracuseStep 455887 = 683831) B683831
theorem B15725987 : Blo 424774 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B2160431 : Blo 424774 2160431 := bstep (se 1 (by rfl) ⟨1620323, by rfl⟩ : syracuseStep 2160431 = 3240647) B3240647
theorem B456511 : Blo 424774 456511 := bstep (se 1 (by rfl) ⟨342383, by rfl⟩ : syracuseStep 456511 = 684767) B684767
theorem B718841 : Blo 424774 718841 := bstep (se 2 (by rfl) ⟨269565, by rfl⟩ : syracuseStep 718841 = 539131) B539131
theorem B719003 : Blo 424774 719003 := bstep (se 1 (by rfl) ⟨539252, by rfl⟩ : syracuseStep 719003 = 1078505) B1078505
theorem B4847849 : Blo 424774 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B2586887 : Blo 424774 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B719111 : Blo 424774 719111 := bstep (se 1 (by rfl) ⟨539333, by rfl⟩ : syracuseStep 719111 = 1078667) B1078667
theorem B5208409 : Blo 424774 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B719671 : Blo 424774 719671 := bstep (se 1 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 719671 = 1079507) B1079507
theorem B424795 : Blo 424774 424795 := bstep (se 1 (by rfl) ⟨318596, by rfl⟩ : syracuseStep 424795 = 637193) B637193
theorem B1080155 : Blo 424774 1080155 := bstep (se 1 (by rfl) ⟨810116, by rfl⟩ : syracuseStep 1080155 = 1620233) B1620233
theorem B424863 : Blo 424774 424863 := bstep (se 1 (by rfl) ⟨318647, by rfl⟩ : syracuseStep 424863 = 637295) B637295
theorem B1440719 : Blo 424774 1440719 := bstep (se 1 (by rfl) ⟨1080539, by rfl⟩ : syracuseStep 1440719 = 2161079) B2161079
theorem B425007 : Blo 424774 425007 := bstep (se 1 (by rfl) ⟨318755, by rfl⟩ : syracuseStep 425007 = 637511) B637511
theorem B425031 : Blo 424774 425031 := bstep (se 1 (by rfl) ⟨318773, by rfl⟩ : syracuseStep 425031 = 637547) B637547
theorem B2620505 : Blo 424774 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B1080449 : Blo 424774 1080449 := bstep (se 2 (by rfl) ⟨405168, by rfl⟩ : syracuseStep 1080449 = 810337) B810337
theorem B425183 : Blo 424774 425183 := bstep (se 1 (by rfl) ⟨318887, by rfl⟩ : syracuseStep 425183 = 637775) B637775
theorem B720137 : Blo 424774 720137 := bstep (se 2 (by rfl) ⟨270051, by rfl⟩ : syracuseStep 720137 = 540103) B540103
theorem B2915777 : Blo 424774 2915777 := bstep (se 2 (by rfl) ⟨1093416, by rfl⟩ : syracuseStep 2915777 = 2186833) B2186833
theorem B425447 : Blo 424774 425447 := bstep (se 1 (by rfl) ⟨319085, by rfl⟩ : syracuseStep 425447 = 638171) B638171
theorem B425563 : Blo 424774 425563 := bstep (se 1 (by rfl) ⟨319172, by rfl⟩ : syracuseStep 425563 = 638345) B638345
theorem B425799 : Blo 424774 425799 := bstep (se 1 (by rfl) ⟨319349, by rfl⟩ : syracuseStep 425799 = 638699) B638699
theorem B1081259 : Blo 424774 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B425951 : Blo 424774 425951 := bstep (se 1 (by rfl) ⟨319463, by rfl⟩ : syracuseStep 425951 = 638927) B638927
theorem B426175 : Blo 424774 426175 := bstep (se 1 (by rfl) ⟨319631, by rfl⟩ : syracuseStep 426175 = 639263) B639263
theorem B426191 : Blo 424774 426191 := bstep (se 1 (by rfl) ⟨319643, by rfl⟩ : syracuseStep 426191 = 639287) B639287
theorem B426239 : Blo 424774 426239 := bstep (se 1 (by rfl) ⟨319679, by rfl⟩ : syracuseStep 426239 = 639359) B639359
theorem B426287 : Blo 424774 426287 := bstep (se 1 (by rfl) ⟨319715, by rfl⟩ : syracuseStep 426287 = 639431) B639431
theorem B1311191 : Blo 424774 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B4096493 : Blo 424774 4096493 := bstep (se 3 (by rfl) ⟨768092, by rfl⟩ : syracuseStep 4096493 = 1536185) B1536185
theorem B426523 : Blo 424774 426523 := bstep (se 1 (by rfl) ⟨319892, by rfl⟩ : syracuseStep 426523 = 639785) B639785
theorem B426527 : Blo 424774 426527 := bstep (se 1 (by rfl) ⟨319895, by rfl⟩ : syracuseStep 426527 = 639791) B639791
theorem B3637871 : Blo 424774 3637871 := bstep (se 1 (by rfl) ⟨2728403, by rfl⟩ : syracuseStep 3637871 = 5456807) B5456807
theorem B426607 : Blo 424774 426607 := bstep (se 1 (by rfl) ⟨319955, by rfl⟩ : syracuseStep 426607 = 639911) B639911
theorem B426663 : Blo 424774 426663 := bstep (se 1 (by rfl) ⟨319997, by rfl⟩ : syracuseStep 426663 = 639995) B639995
theorem B721595 : Blo 424774 721595 := bstep (se 1 (by rfl) ⟨541196, by rfl⟩ : syracuseStep 721595 = 1082393) B1082393
theorem B426703 : Blo 424774 426703 := bstep (se 1 (by rfl) ⟨320027, by rfl⟩ : syracuseStep 426703 = 640055) B640055
theorem B426783 : Blo 424774 426783 := bstep (se 1 (by rfl) ⟨320087, by rfl⟩ : syracuseStep 426783 = 640175) B640175
theorem B427055 : Blo 424774 427055 := bstep (se 1 (by rfl) ⟨320291, by rfl⟩ : syracuseStep 427055 = 640583) B640583
theorem B1442879 : Blo 424774 1442879 := bstep (se 1 (by rfl) ⟨1082159, by rfl⟩ : syracuseStep 1442879 = 2164319) B2164319
theorem B427119 : Blo 424774 427119 := bstep (se 1 (by rfl) ⟨320339, by rfl⟩ : syracuseStep 427119 = 640679) B640679
theorem B427175 : Blo 424774 427175 := bstep (se 1 (by rfl) ⟨320381, by rfl⟩ : syracuseStep 427175 = 640763) B640763
theorem B427199 : Blo 424774 427199 := bstep (se 1 (by rfl) ⟨320399, by rfl⟩ : syracuseStep 427199 = 640799) B640799
theorem B427231 : Blo 424774 427231 := bstep (se 1 (by rfl) ⟨320423, by rfl⟩ : syracuseStep 427231 = 640847) B640847
theorem B722155 : Blo 424774 722155 := bstep (se 1 (by rfl) ⟨541616, by rfl⟩ : syracuseStep 722155 = 1083233) B1083233
theorem B1639727 : Blo 424774 1639727 := bstep (se 1 (by rfl) ⟨1229795, by rfl⟩ : syracuseStep 1639727 = 2459591) B2459591
theorem B427311 : Blo 424774 427311 := bstep (se 1 (by rfl) ⟨320483, by rfl⟩ : syracuseStep 427311 = 640967) B640967
theorem B427547 : Blo 424774 427547 := bstep (se 1 (by rfl) ⟨320660, by rfl⟩ : syracuseStep 427547 = 641321) B641321
theorem B427551 : Blo 424774 427551 := bstep (se 1 (by rfl) ⟨320663, by rfl⟩ : syracuseStep 427551 = 641327) B641327
theorem B5473925 : Blo 424774 5473925 := bstep (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) B1026361
theorem B427711 : Blo 424774 427711 := bstep (se 1 (by rfl) ⟨320783, by rfl⟩ : syracuseStep 427711 = 641567) B641567
theorem B1083071 : Blo 424774 1083071 := bstep (se 1 (by rfl) ⟨812303, by rfl⟩ : syracuseStep 1083071 = 1624607) B1624607
theorem B427967 : Blo 424774 427967 := bstep (se 1 (by rfl) ⟨320975, by rfl⟩ : syracuseStep 427967 = 641951) B641951
theorem B427999 : Blo 424774 427999 := bstep (se 1 (by rfl) ⟨320999, by rfl⟩ : syracuseStep 427999 = 641999) B641999
theorem B428059 : Blo 424774 428059 := bstep (se 1 (by rfl) ⟨321044, by rfl⟩ : syracuseStep 428059 = 642089) B642089
theorem B428063 : Blo 424774 428063 := bstep (se 1 (by rfl) ⟨321047, by rfl⟩ : syracuseStep 428063 = 642095) B642095
theorem B428079 : Blo 424774 428079 := bstep (se 1 (by rfl) ⟨321059, by rfl⟩ : syracuseStep 428079 = 642119) B642119
theorem B1640573 : Blo 424774 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B1214651 : Blo 424774 1214651 := bstep (se 1 (by rfl) ⟨910988, by rfl⟩ : syracuseStep 1214651 = 1821977) B1821977
theorem B428255 : Blo 424774 428255 := bstep (se 1 (by rfl) ⟨321191, by rfl⟩ : syracuseStep 428255 = 642383) B642383
theorem B428315 : Blo 424774 428315 := bstep (se 1 (by rfl) ⟨321236, by rfl⟩ : syracuseStep 428315 = 642473) B642473
theorem B1083689 : Blo 424774 1083689 := bstep (se 2 (by rfl) ⟨406383, by rfl⟩ : syracuseStep 1083689 = 812767) B812767
theorem B428415 : Blo 424774 428415 := bstep (se 1 (by rfl) ⟨321311, by rfl⟩ : syracuseStep 428415 = 642623) B642623
theorem B428591 : Blo 424774 428591 := bstep (se 1 (by rfl) ⟨321443, by rfl⟩ : syracuseStep 428591 = 642887) B642887
theorem B428647 : Blo 424774 428647 := bstep (se 1 (by rfl) ⟨321485, by rfl⟩ : syracuseStep 428647 = 642971) B642971
theorem B5311115 : Blo 424774 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B2624723 : Blo 424774 2624723 := bstep (se 1 (by rfl) ⟨1968542, by rfl⟩ : syracuseStep 2624723 = 3937085) B3937085
theorem B3640535 : Blo 424774 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B3247451 : Blo 424774 3247451 := bstep (se 1 (by rfl) ⟨2435588, by rfl⟩ : syracuseStep 3247451 = 4871177) B4871177
theorem B6163937 : Blo 424774 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B1151543 : Blo 424774 1151543 := bstep (se 1 (by rfl) ⟨863657, by rfl⟩ : syracuseStep 1151543 = 1727315) B1727315
theorem B2167559 : Blo 424774 2167559 := bstep (se 1 (by rfl) ⟨1625669, by rfl⟩ : syracuseStep 2167559 = 3251339) B3251339
theorem B1446713 : Blo 424774 1446713 := bstep (se 2 (by rfl) ⟨542517, by rfl⟩ : syracuseStep 1446713 = 1085035) B1085035
theorem B1053791 : Blo 424774 1053791 := bstep (se 1 (by rfl) ⟨790343, by rfl⟩ : syracuseStep 1053791 = 1580687) B1580687
theorem B3249395 : Blo 424774 3249395 := bstep (se 1 (by rfl) ⟨2437046, by rfl⟩ : syracuseStep 3249395 = 4874093) B4874093
theorem B6919577 : Blo 424774 6919577 := bstep (se 2 (by rfl) ⟨2594841, by rfl⟩ : syracuseStep 6919577 = 5189683) B5189683
theorem B1152431 : Blo 424774 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B1218023 : Blo 424774 1218023 := bstep (se 1 (by rfl) ⟨913517, by rfl⟩ : syracuseStep 1218023 = 1827035) B1827035
theorem B1775105 : Blo 424774 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1152667 : Blo 424774 1152667 := bstep (se 1 (by rfl) ⟨864500, by rfl⟩ : syracuseStep 1152667 = 1729001) B1729001
theorem B956123 : Blo 424774 956123 := bstep (se 1 (by rfl) ⟨717092, by rfl⟩ : syracuseStep 956123 = 1434185) B1434185
theorem B1152755 : Blo 424774 1152755 := bstep (se 1 (by rfl) ⟨864566, by rfl⟩ : syracuseStep 1152755 = 1729133) B1729133
theorem B956231 : Blo 424774 956231 := bstep (se 1 (by rfl) ⟨717173, by rfl⟩ : syracuseStep 956231 = 1434347) B1434347
theorem B1939565 : Blo 424774 1939565 := bstep (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) B727337
theorem B2431397 : Blo 424774 2431397 := bstep (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) B455887
theorem B957239 : Blo 424774 957239 := bstep (se 1 (by rfl) ⟨717929, by rfl⟩ : syracuseStep 957239 = 1435859) B1435859
theorem B957419 : Blo 424774 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B4398209 : Blo 424774 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B7413059 : Blo 424774 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B1023479 : Blo 424774 1023479 := bstep (se 1 (by rfl) ⟨767609, by rfl⟩ : syracuseStep 1023479 = 1535219) B1535219
theorem B958319 : Blo 424774 958319 := bstep (se 1 (by rfl) ⟨718739, by rfl⟩ : syracuseStep 958319 = 1437479) B1437479
theorem B5447681 : Blo 424774 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B11345939 : Blo 424774 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B1024505 : Blo 424774 1024505 := bstep (se 2 (by rfl) ⟨384189, by rfl⟩ : syracuseStep 1024505 = 768379) B768379
theorem B959003 : Blo 424774 959003 := bstep (se 1 (by rfl) ⟨719252, by rfl⟩ : syracuseStep 959003 = 1438505) B1438505
theorem B3252797 : Blo 424774 3252797 := bstep (se 3 (by rfl) ⟨609899, by rfl⟩ : syracuseStep 3252797 = 1219799) B1219799
theorem B959183 : Blo 424774 959183 := bstep (se 1 (by rfl) ⟨719387, by rfl⟩ : syracuseStep 959183 = 1438775) B1438775
theorem B1614599 : Blo 424774 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B861257 : Blo 424774 861257 := bstep (se 2 (by rfl) ⟨322971, by rfl⟩ : syracuseStep 861257 = 645943) B645943
theorem B959561 : Blo 424774 959561 := bstep (se 2 (by rfl) ⟨359835, by rfl⟩ : syracuseStep 959561 = 719671) B719671
theorem B1942649 : Blo 424774 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B3647369 : Blo 424774 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B927679 : Blo 424774 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B960479 : Blo 424774 960479 := bstep (se 1 (by rfl) ⟨720359, by rfl⟩ : syracuseStep 960479 = 1440719) B1440719
theorem B1747003 : Blo 424774 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1943851 : Blo 424774 1943851 := bstep (se 1 (by rfl) ⟨1457888, by rfl⟩ : syracuseStep 1943851 = 2915777) B2915777
theorem B2435453 : Blo 424774 2435453 := bstep (se 3 (by rfl) ⟨456647, by rfl⟩ : syracuseStep 2435453 = 913295) B913295
theorem B3877415 : Blo 424774 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B3255227 : Blo 424774 3255227 := bstep (se 1 (by rfl) ⟨2441420, by rfl⟩ : syracuseStep 3255227 = 4882841) B4882841
theorem B961487 : Blo 424774 961487 := bstep (se 1 (by rfl) ⟨721115, by rfl⟩ : syracuseStep 961487 = 1442231) B1442231
theorem B2042921 : Blo 424774 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B961577 : Blo 424774 961577 := bstep (se 2 (by rfl) ⟨360591, by rfl⟩ : syracuseStep 961577 = 721183) B721183
theorem B961811 : Blo 424774 961811 := bstep (se 1 (by rfl) ⟨721358, by rfl⟩ : syracuseStep 961811 = 1442717) B1442717
theorem B961847 : Blo 424774 961847 := bstep (se 1 (by rfl) ⟨721385, by rfl⟩ : syracuseStep 961847 = 1442771) B1442771
theorem B118042181 : Blo 424774 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B1617515 : Blo 424774 1617515 := bstep (se 1 (by rfl) ⟨1213136, by rfl⟩ : syracuseStep 1617515 = 2426273) B2426273
theorem B1158799 : Blo 424774 1158799 := bstep (se 1 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 1158799 = 1738199) B1738199
theorem B2043575 : Blo 424774 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B9383633 : Blo 424774 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B1453801 : Blo 424774 1453801 := bstep (se 2 (by rfl) ⟨545175, by rfl⟩ : syracuseStep 1453801 = 1090351) B1090351
theorem B3518333 : Blo 424774 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B962441 : Blo 424774 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B962657 : Blo 424774 962657 := bstep (se 2 (by rfl) ⟨360996, by rfl⟩ : syracuseStep 962657 = 721993) B721993
theorem B8532361 : Blo 424774 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B963323 : Blo 424774 963323 := bstep (se 1 (by rfl) ⟨722492, by rfl⟩ : syracuseStep 963323 = 1444985) B1444985
theorem B3650345 : Blo 424774 3650345 := bstep (se 2 (by rfl) ⟨1368879, by rfl⟩ : syracuseStep 3650345 = 2737759) B2737759
theorem B963539 : Blo 424774 963539 := bstep (se 1 (by rfl) ⟨722654, by rfl⟩ : syracuseStep 963539 = 1445309) B1445309
theorem B964007 : Blo 424774 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B964115 : Blo 424774 964115 := bstep (se 1 (by rfl) ⟨723086, by rfl⟩ : syracuseStep 964115 = 1446173) B1446173
theorem B964187 : Blo 424774 964187 := bstep (se 1 (by rfl) ⟨723140, by rfl⟩ : syracuseStep 964187 = 1446281) B1446281
theorem B2439143 : Blo 424774 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B1816577 : Blo 424774 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B538807 : Blo 424774 538807 := bstep (se 1 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 538807 = 808211) B808211
theorem B1947883 : Blo 424774 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B1620263 : Blo 424774 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B637391 : Blo 424774 637391 := bstep (se 1 (by rfl) ⟨478043, by rfl⟩ : syracuseStep 637391 = 956087) B956087
theorem B637481 : Blo 424774 637481 := bstep (se 2 (by rfl) ⟨239055, by rfl⟩ : syracuseStep 637481 = 478111) B478111
theorem B539227 : Blo 424774 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B637673 : Blo 424774 637673 := bstep (se 2 (by rfl) ⟨239127, by rfl⟩ : syracuseStep 637673 = 478255) B478255
theorem B638057 : Blo 424774 638057 := bstep (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) B478543
theorem B2604257 : Blo 424774 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B638183 : Blo 424774 638183 := bstep (se 1 (by rfl) ⟨478637, by rfl⟩ : syracuseStep 638183 = 957275) B957275
theorem B1621235 : Blo 424774 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B1621417 : Blo 424774 1621417 := bstep (se 2 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 1621417 = 1216063) B1216063
theorem B638687 : Blo 424774 638687 := bstep (se 1 (by rfl) ⟨479015, by rfl⟩ : syracuseStep 638687 = 958031) B958031
theorem B4505311 : Blo 424774 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B7126751 : Blo 424774 7126751 := bstep (se 1 (by rfl) ⟨5345063, by rfl⟩ : syracuseStep 7126751 = 10690127) B10690127
theorem B638729 : Blo 424774 638729 := bstep (se 2 (by rfl) ⟨239523, by rfl⟩ : syracuseStep 638729 = 479047) B479047
theorem B3653657 : Blo 424774 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B639167 : Blo 424774 639167 := bstep (se 1 (by rfl) ⟨479375, by rfl⟩ : syracuseStep 639167 = 958751) B958751
theorem B1622207 : Blo 424774 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B5194007 : Blo 424774 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B868735 : Blo 424774 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B1819037 : Blo 424774 1819037 := bstep (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) B682139
theorem B639593 : Blo 424774 639593 := bstep (se 2 (by rfl) ⟨239847, by rfl⟩ : syracuseStep 639593 = 479695) B479695
theorem B639599 : Blo 424774 639599 := bstep (se 1 (by rfl) ⟨479699, by rfl⟩ : syracuseStep 639599 = 959399) B959399
theorem B2081555 : Blo 424774 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B640223 : Blo 424774 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B640235 : Blo 424774 640235 := bstep (se 1 (by rfl) ⟨480176, by rfl⟩ : syracuseStep 640235 = 960353) B960353
theorem B1459613 : Blo 424774 1459613 := bstep (se 3 (by rfl) ⟨273677, by rfl⟩ : syracuseStep 1459613 = 547355) B547355
theorem B8177057 : Blo 424774 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B2737577 : Blo 424774 2737577 := bstep (se 2 (by rfl) ⟨1026591, by rfl⟩ : syracuseStep 2737577 = 2053183) B2053183
theorem B3458519 : Blo 424774 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B23447069 : Blo 424774 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B640619 : Blo 424774 640619 := bstep (se 1 (by rfl) ⟨480464, by rfl⟩ : syracuseStep 640619 = 960929) B960929
theorem B640703 : Blo 424774 640703 := bstep (se 1 (by rfl) ⟨480527, by rfl⟩ : syracuseStep 640703 = 961055) B961055
theorem B8406773 : Blo 424774 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B640889 : Blo 424774 640889 := bstep (se 2 (by rfl) ⟨240333, by rfl⟩ : syracuseStep 640889 = 480667) B480667
theorem B608681 : Blo 424774 608681 := bstep (se 2 (by rfl) ⟨228255, by rfl⟩ : syracuseStep 608681 = 456511) B456511
theorem B641639 : Blo 424774 641639 := bstep (se 1 (by rfl) ⟨481229, by rfl⟩ : syracuseStep 641639 = 962459) B962459
theorem B11717399 : Blo 424774 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B641831 : Blo 424774 641831 := bstep (se 1 (by rfl) ⟨481373, by rfl⟩ : syracuseStep 641831 = 962747) B962747
theorem B2050859 : Blo 424774 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B1821703 : Blo 424774 1821703 := bstep (se 1 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 1821703 = 2732555) B2732555
theorem B642155 : Blo 424774 642155 := bstep (se 1 (by rfl) ⟨481616, by rfl⟩ : syracuseStep 642155 = 963233) B963233
theorem B12274811 : Blo 424774 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B642395 : Blo 424774 642395 := bstep (se 1 (by rfl) ⟨481796, by rfl⟩ : syracuseStep 642395 = 963593) B963593
theorem B642425 : Blo 424774 642425 := bstep (se 2 (by rfl) ⟨240909, by rfl⟩ : syracuseStep 642425 = 481819) B481819
theorem B642431 : Blo 424774 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B478687 : Blo 424774 478687 := bstep (se 1 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 478687 = 718031) B718031
theorem B1822591 : Blo 424774 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B643055 : Blo 424774 643055 := bstep (se 1 (by rfl) ⟨482291, by rfl⟩ : syracuseStep 643055 = 964583) B964583
theorem B479227 : Blo 424774 479227 := bstep (se 1 (by rfl) ⟨359420, by rfl⟩ : syracuseStep 479227 = 718841) B718841
theorem B643067 : Blo 424774 643067 := bstep (se 1 (by rfl) ⟨482300, by rfl⟩ : syracuseStep 643067 = 964601) B964601
theorem B643127 : Blo 424774 643127 := bstep (se 1 (by rfl) ⟨482345, by rfl⟩ : syracuseStep 643127 = 964691) B964691
theorem B479335 : Blo 424774 479335 := bstep (se 1 (by rfl) ⟨359501, by rfl⟩ : syracuseStep 479335 = 719003) B719003
theorem B3231899 : Blo 424774 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B1724591 : Blo 424774 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B479407 : Blo 424774 479407 := bstep (se 1 (by rfl) ⟨359555, by rfl⟩ : syracuseStep 479407 = 719111) B719111
theorem B480091 : Blo 424774 480091 := bstep (se 1 (by rfl) ⟨360068, by rfl⟩ : syracuseStep 480091 = 720137) B720137
theorem B2152007 : Blo 424774 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B2053799 : Blo 424774 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B808795 : Blo 424774 808795 := bstep (se 1 (by rfl) ⟨606596, by rfl⟩ : syracuseStep 808795 = 1213193) B1213193
theorem B481351 : Blo 424774 481351 := bstep (se 1 (by rfl) ⟨361013, by rfl⟩ : syracuseStep 481351 = 722027) B722027
theorem B6150323 : Blo 424774 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4872635 : Blo 424774 4872635 := bstep (se 1 (by rfl) ⟨3654476, by rfl⟩ : syracuseStep 4872635 = 7308953) B7308953
theorem B3660491 : Blo 424774 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B809851 : Blo 424774 809851 := bstep (se 1 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 809851 = 1214777) B1214777
theorem B482215 : Blo 424774 482215 := bstep (se 1 (by rfl) ⟨361661, by rfl⟩ : syracuseStep 482215 = 723323) B723323
theorem B7265213 : Blo 424774 7265213 := bstep (se 3 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 7265213 = 2724455) B2724455
theorem B34331921 : Blo 424774 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B1826077 : Blo 424774 1826077 := bstep (se 3 (by rfl) ⟨342389, by rfl⟩ : syracuseStep 1826077 = 684779) B684779
theorem B908921 : Blo 424774 908921 := bstep (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) B681691
theorem B4087685 : Blo 424774 4087685 := bstep (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) B766441
theorem B3629123 : Blo 424774 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B1434023 : Blo 424774 1434023 := bstep (se 1 (by rfl) ⟨1075517, by rfl⟩ : syracuseStep 1434023 = 2151035) B2151035
theorem B13100039 : Blo 424774 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B5203693 : Blo 424774 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B878399 : Blo 424774 878399 := bstep (se 1 (by rfl) ⟨658799, by rfl⟩ : syracuseStep 878399 = 1317599) B1317599
theorem B2058605 : Blo 424774 2058605 := bstep (se 3 (by rfl) ⟨385988, by rfl⟩ : syracuseStep 2058605 = 771977) B771977
theorem B2058857 : Blo 424774 2058857 := bstep (se 2 (by rfl) ⟨772071, by rfl⟩ : syracuseStep 2058857 = 1544143) B1544143
theorem B2223287 : Blo 424774 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B3632471 : Blo 424774 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B2912219 : Blo 424774 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B3338927 : Blo 424774 3338927 := bstep (se 1 (by rfl) ⟨2504195, by rfl⟩ : syracuseStep 3338927 = 5008391) B5008391
theorem B1078535 : Blo 424774 1078535 := bstep (se 1 (by rfl) ⟨808901, by rfl⟩ : syracuseStep 1078535 = 1617803) B1617803
theorem B718247 : Blo 424774 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B6944545 : Blo 424774 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B10483991 : Blo 424774 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B1440287 : Blo 424774 1440287 := bstep (se 1 (by rfl) ⟨1080215, by rfl⟩ : syracuseStep 1440287 = 2160431) B2160431
theorem B719401 : Blo 424774 719401 := bstep (se 2 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 719401 = 539551) B539551
theorem B424775 : Blo 424774 424775 := bstep (se 1 (by rfl) ⟨318581, by rfl⟩ : syracuseStep 424775 = 637163) B637163
theorem B424815 : Blo 424774 424815 := bstep (se 1 (by rfl) ⟨318611, by rfl⟩ : syracuseStep 424815 = 637223) B637223
theorem B2161565 : Blo 424774 2161565 := bstep (se 3 (by rfl) ⟨405293, by rfl⟩ : syracuseStep 2161565 = 810587) B810587
theorem B424871 : Blo 424774 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B425051 : Blo 424774 425051 := bstep (se 1 (by rfl) ⟨318788, by rfl⟩ : syracuseStep 425051 = 637577) B637577
theorem B425167 : Blo 424774 425167 := bstep (se 1 (by rfl) ⟨318875, by rfl⟩ : syracuseStep 425167 = 637751) B637751
theorem B425191 : Blo 424774 425191 := bstep (se 1 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 425191 = 637787) B637787
theorem B720103 : Blo 424774 720103 := bstep (se 1 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 720103 = 1080155) B1080155
theorem B425287 : Blo 424774 425287 := bstep (se 1 (by rfl) ⟨318965, by rfl⟩ : syracuseStep 425287 = 637931) B637931
theorem B720299 : Blo 424774 720299 := bstep (se 1 (by rfl) ⟨540224, by rfl⟩ : syracuseStep 720299 = 1080449) B1080449
theorem B425423 : Blo 424774 425423 := bstep (se 1 (by rfl) ⟨319067, by rfl⟩ : syracuseStep 425423 = 638135) B638135
theorem B3636845 : Blo 424774 3636845 := bstep (se 3 (by rfl) ⟨681908, by rfl⟩ : syracuseStep 3636845 = 1363817) B1363817
theorem B425583 : Blo 424774 425583 := bstep (se 1 (by rfl) ⟨319187, by rfl⟩ : syracuseStep 425583 = 638375) B638375
theorem B425639 : Blo 424774 425639 := bstep (se 1 (by rfl) ⟨319229, by rfl⟩ : syracuseStep 425639 = 638459) B638459
theorem B425703 : Blo 424774 425703 := bstep (se 1 (by rfl) ⟨319277, by rfl⟩ : syracuseStep 425703 = 638555) B638555
theorem B1081097 : Blo 424774 1081097 := bstep (se 2 (by rfl) ⟨405411, by rfl⟩ : syracuseStep 1081097 = 810823) B810823
theorem B425759 : Blo 424774 425759 := bstep (se 1 (by rfl) ⟨319319, by rfl⟩ : syracuseStep 425759 = 638639) B638639
theorem B1081127 : Blo 424774 1081127 := bstep (se 1 (by rfl) ⟨810845, by rfl⟩ : syracuseStep 1081127 = 1621691) B1621691
theorem B425839 : Blo 424774 425839 := bstep (se 1 (by rfl) ⟨319379, by rfl⟩ : syracuseStep 425839 = 638759) B638759
theorem B425895 : Blo 424774 425895 := bstep (se 1 (by rfl) ⟨319421, by rfl⟩ : syracuseStep 425895 = 638843) B638843
theorem B720839 : Blo 424774 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B819155 : Blo 424774 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B426111 : Blo 424774 426111 := bstep (se 1 (by rfl) ⟨319583, by rfl⟩ : syracuseStep 426111 = 639167) B639167
theorem B1081471 : Blo 424774 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B426395 : Blo 424774 426395 := bstep (se 1 (by rfl) ⟨319796, by rfl⟩ : syracuseStep 426395 = 639593) B639593
theorem B2425247 : Blo 424774 2425247 := bstep (se 1 (by rfl) ⟨1818935, by rfl⟩ : syracuseStep 2425247 = 3637871) B3637871
theorem B426399 : Blo 424774 426399 := bstep (se 1 (by rfl) ⟨319799, by rfl⟩ : syracuseStep 426399 = 639599) B639599
theorem B426815 : Blo 424774 426815 := bstep (se 1 (by rfl) ⟨320111, by rfl⟩ : syracuseStep 426815 = 640223) B640223
theorem B426823 : Blo 424774 426823 := bstep (se 1 (by rfl) ⟨320117, by rfl⟩ : syracuseStep 426823 = 640235) B640235
theorem B15631379 : Blo 424774 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B427079 : Blo 424774 427079 := bstep (se 1 (by rfl) ⟨320309, by rfl⟩ : syracuseStep 427079 = 640619) B640619
theorem B4850765 : Blo 424774 4850765 := bstep (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) B1819037
theorem B427135 : Blo 424774 427135 := bstep (se 1 (by rfl) ⟨320351, by rfl⟩ : syracuseStep 427135 = 640703) B640703
theorem B722047 : Blo 424774 722047 := bstep (se 1 (by rfl) ⟨541535, by rfl⟩ : syracuseStep 722047 = 1083071) B1083071
theorem B5604515 : Blo 424774 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B427259 : Blo 424774 427259 := bstep (se 1 (by rfl) ⟨320444, by rfl⟩ : syracuseStep 427259 = 640889) B640889
theorem B722459 : Blo 424774 722459 := bstep (se 1 (by rfl) ⟨541844, by rfl⟩ : syracuseStep 722459 = 1083689) B1083689
theorem B427759 : Blo 424774 427759 := bstep (se 1 (by rfl) ⟨320819, by rfl⟩ : syracuseStep 427759 = 641639) B641639
theorem B3540743 : Blo 424774 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B427887 : Blo 424774 427887 := bstep (se 1 (by rfl) ⟨320915, by rfl⟩ : syracuseStep 427887 = 641831) B641831
theorem B428103 : Blo 424774 428103 := bstep (se 1 (by rfl) ⟨321077, by rfl⟩ : syracuseStep 428103 = 642155) B642155
theorem B2427023 : Blo 424774 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B2164967 : Blo 424774 2164967 := bstep (se 1 (by rfl) ⟨1623725, by rfl⟩ : syracuseStep 2164967 = 3247451) B3247451
theorem B428263 : Blo 424774 428263 := bstep (se 1 (by rfl) ⟨321197, by rfl⟩ : syracuseStep 428263 = 642395) B642395
theorem B428283 : Blo 424774 428283 := bstep (se 1 (by rfl) ⟨321212, by rfl⟩ : syracuseStep 428283 = 642425) B642425
theorem B428287 : Blo 424774 428287 := bstep (se 1 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 428287 = 642431) B642431
theorem B428703 : Blo 424774 428703 := bstep (se 1 (by rfl) ⟨321527, by rfl⟩ : syracuseStep 428703 = 643055) B643055
theorem B428711 : Blo 424774 428711 := bstep (se 1 (by rfl) ⟨321533, by rfl⟩ : syracuseStep 428711 = 643067) B643067
theorem B428751 : Blo 424774 428751 := bstep (se 1 (by rfl) ⟨321563, by rfl⟩ : syracuseStep 428751 = 643127) B643127
theorem B2329337 : Blo 424774 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B1149727 : Blo 424774 1149727 := bstep (se 1 (by rfl) ⟨862295, by rfl⟩ : syracuseStep 1149727 = 1724591) B1724591
theorem B2591801 : Blo 424774 2591801 := bstep (se 2 (by rfl) ⟨971925, by rfl⟩ : syracuseStep 2591801 = 1943851) B1943851
theorem B1445039 : Blo 424774 1445039 := bstep (se 1 (by rfl) ⟨1083779, by rfl⟩ : syracuseStep 1445039 = 2167559) B2167559
theorem B2166263 : Blo 424774 2166263 := bstep (se 1 (by rfl) ⟨1624697, by rfl⟩ : syracuseStep 2166263 = 3249395) B3249395
theorem B1183403 : Blo 424774 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B2428937 : Blo 424774 2428937 := bstep (se 2 (by rfl) ⟨910851, by rfl⟩ : syracuseStep 2428937 = 1821703) B1821703
theorem B4100215 : Blo 424774 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B3248423 : Blo 424774 3248423 := bstep (se 1 (by rfl) ⟨2436317, by rfl⟩ : syracuseStep 3248423 = 4872635) B4872635
theorem B1545065 : Blo 424774 1545065 := bstep (se 2 (by rfl) ⟨579399, by rfl⟩ : syracuseStep 1545065 = 1158799) B1158799
theorem B1938401 : Blo 424774 1938401 := bstep (se 2 (by rfl) ⟨726900, by rfl⟩ : syracuseStep 1938401 = 1453801) B1453801
theorem B2430121 : Blo 424774 2430121 := bstep (se 2 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 2430121 = 1822591) B1822591
theorem B2725123 : Blo 424774 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B956015 : Blo 424774 956015 := bstep (se 1 (by rfl) ⟨717011, by rfl⟩ : syracuseStep 956015 = 1434023) B1434023
theorem B2168531 : Blo 424774 2168531 := bstep (se 1 (by rfl) ⟨1626398, by rfl⟩ : syracuseStep 2168531 = 3252797) B3252797
theorem B2431579 : Blo 424774 2431579 := bstep (se 1 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 2431579 = 3647369) B3647369
theorem B2170151 : Blo 424774 2170151 := bstep (se 1 (by rfl) ⟨1627613, by rfl⟩ : syracuseStep 2170151 = 3255227) B3255227
theorem B1482191 : Blo 424774 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B1941479 : Blo 424774 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B2597177 : Blo 424774 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B2433563 : Blo 424774 2433563 := bstep (se 1 (by rfl) ⟨1825172, by rfl⟩ : syracuseStep 2433563 = 3650345) B3650345
theorem B959201 : Blo 424774 959201 := bstep (se 2 (by rfl) ⟨359700, by rfl⟩ : syracuseStep 959201 = 719401) B719401
theorem B19768157 : Blo 424774 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B6989327 : Blo 424774 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B960137 : Blo 424774 960137 := bstep (se 2 (by rfl) ⟨360051, by rfl⟩ : syracuseStep 960137 = 720103) B720103
theorem B960191 : Blo 424774 960191 := bstep (se 1 (by rfl) ⟨720143, by rfl⟩ : syracuseStep 960191 = 1440287) B1440287
theorem B2434769 : Blo 424774 2434769 := bstep (se 2 (by rfl) ⟨913038, by rfl⟩ : syracuseStep 2434769 = 1826077) B1826077
theorem B6007081 : Blo 424774 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B2435771 : Blo 424774 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B2730995 : Blo 424774 2730995 := bstep (se 1 (by rfl) ⟨2048246, by rfl⟩ : syracuseStep 2730995 = 4096493) B4096493
theorem B1158313 : Blo 424774 1158313 := bstep (se 2 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 1158313 = 868735) B868735
theorem B1387703 : Blo 424774 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B961919 : Blo 424774 961919 := bstep (se 1 (by rfl) ⟨721439, by rfl⟩ : syracuseStep 961919 = 1442879) B1442879
theorem B1093151 : Blo 424774 1093151 := bstep (se 1 (by rfl) ⟨819863, by rfl⟩ : syracuseStep 1093151 = 1639727) B1639727
theorem B5451371 : Blo 424774 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B2305679 : Blo 424774 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B3649283 : Blo 424774 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B1093715 : Blo 424774 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B962873 : Blo 424774 962873 := bstep (se 2 (by rfl) ⟨361077, by rfl⟩ : syracuseStep 962873 = 722155) B722155
theorem B7811599 : Blo 424774 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B1749815 : Blo 424774 1749815 := bstep (se 1 (by rfl) ⟨1312361, by rfl⟩ : syracuseStep 1749815 = 2624723) B2624723
theorem B4109291 : Blo 424774 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B964475 : Blo 424774 964475 := bstep (se 1 (by rfl) ⟨723356, by rfl⟩ : syracuseStep 964475 = 1446713) B1446713
theorem B702527 : Blo 424774 702527 := bstep (se 1 (by rfl) ⟨526895, by rfl⟩ : syracuseStep 702527 = 1053791) B1053791
theorem B768287 : Blo 424774 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B637415 : Blo 424774 637415 := bstep (se 1 (by rfl) ⟨478061, by rfl⟩ : syracuseStep 637415 = 956123) B956123
theorem B768503 : Blo 424774 768503 := bstep (se 1 (by rfl) ⟨576377, by rfl⟩ : syracuseStep 768503 = 1152755) B1152755
theorem B637487 : Blo 424774 637487 := bstep (se 1 (by rfl) ⟨478115, by rfl⟩ : syracuseStep 637487 = 956231) B956231
theorem B1620931 : Blo 424774 1620931 := bstep (se 1 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 1620931 = 2431397) B2431397
theorem B2440327 : Blo 424774 2440327 := bstep (se 1 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 2440327 = 3660491) B3660491
theorem B638159 : Blo 424774 638159 := bstep (se 1 (by rfl) ⟨478619, by rfl⟩ : syracuseStep 638159 = 957239) B957239
theorem B638249 : Blo 424774 638249 := bstep (se 2 (by rfl) ⟨239343, by rfl⟩ : syracuseStep 638249 = 478687) B478687
theorem B638279 : Blo 424774 638279 := bstep (se 1 (by rfl) ⟨478709, by rfl⟩ : syracuseStep 638279 = 957419) B957419
theorem B2932139 : Blo 424774 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B22887947 : Blo 424774 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B638879 : Blo 424774 638879 := bstep (se 1 (by rfl) ⟨479159, by rfl⟩ : syracuseStep 638879 = 958319) B958319
theorem B638969 : Blo 424774 638969 := bstep (se 2 (by rfl) ⟨239613, by rfl⟩ : syracuseStep 638969 = 479227) B479227
theorem B639113 : Blo 424774 639113 := bstep (se 2 (by rfl) ⟨239667, by rfl⟩ : syracuseStep 639113 = 479335) B479335
theorem B639209 : Blo 424774 639209 := bstep (se 2 (by rfl) ⟨239703, by rfl⟩ : syracuseStep 639209 = 479407) B479407
theorem B639335 : Blo 424774 639335 := bstep (se 1 (by rfl) ⟨479501, by rfl⟩ : syracuseStep 639335 = 959003) B959003
theorem B639455 : Blo 424774 639455 := bstep (se 1 (by rfl) ⟨479591, by rfl⟩ : syracuseStep 639455 = 959183) B959183
theorem B8733359 : Blo 424774 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B574171 : Blo 424774 574171 := bstep (se 1 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 574171 = 861257) B861257
theorem B639707 : Blo 424774 639707 := bstep (se 1 (by rfl) ⟨479780, by rfl⟩ : syracuseStep 639707 = 959561) B959561
theorem B1295099 : Blo 424774 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B1623149 : Blo 424774 1623149 := bstep (se 3 (by rfl) ⟨304340, by rfl⟩ : syracuseStep 1623149 = 608681) B608681
theorem B640121 : Blo 424774 640121 := bstep (se 2 (by rfl) ⟨240045, by rfl⟩ : syracuseStep 640121 = 480091) B480091
theorem B640319 : Blo 424774 640319 := bstep (se 1 (by rfl) ⟨480239, by rfl⟩ : syracuseStep 640319 = 960479) B960479
theorem B1623635 : Blo 424774 1623635 := bstep (se 1 (by rfl) ⟨1217726, by rfl⟩ : syracuseStep 1623635 = 2435453) B2435453
theorem B640991 : Blo 424774 640991 := bstep (se 1 (by rfl) ⟨480743, by rfl⟩ : syracuseStep 640991 = 961487) B961487
theorem B1361947 : Blo 424774 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B641051 : Blo 424774 641051 := bstep (se 1 (by rfl) ⟨480788, by rfl⟩ : syracuseStep 641051 = 961577) B961577
theorem B641207 : Blo 424774 641207 := bstep (se 1 (by rfl) ⟨480905, by rfl⟩ : syracuseStep 641207 = 961811) B961811
theorem B641231 : Blo 424774 641231 := bstep (se 1 (by rfl) ⟨480923, by rfl⟩ : syracuseStep 641231 = 961847) B961847
theorem B9259393 : Blo 424774 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B78694787 : Blo 424774 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B1362383 : Blo 424774 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B2345555 : Blo 424774 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B641627 : Blo 424774 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B641771 : Blo 424774 641771 := bstep (se 1 (by rfl) ⟨481328, by rfl⟩ : syracuseStep 641771 = 962657) B962657
theorem B641801 : Blo 424774 641801 := bstep (se 2 (by rfl) ⟨240675, by rfl⟩ : syracuseStep 641801 = 481351) B481351
theorem B642215 : Blo 424774 642215 := bstep (se 1 (by rfl) ⟨481661, by rfl⟩ : syracuseStep 642215 = 963323) B963323
theorem B642359 : Blo 424774 642359 := bstep (se 1 (by rfl) ⟨481769, by rfl⟩ : syracuseStep 642359 = 963539) B963539
theorem B478831 : Blo 424774 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B642671 : Blo 424774 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B642743 : Blo 424774 642743 := bstep (se 1 (by rfl) ⟨482057, by rfl⟩ : syracuseStep 642743 = 964115) B964115
theorem B642791 : Blo 424774 642791 := bstep (se 1 (by rfl) ⟨482093, by rfl⟩ : syracuseStep 642791 = 964187) B964187
theorem B642953 : Blo 424774 642953 := bstep (se 2 (by rfl) ⟨241107, by rfl⟩ : syracuseStep 642953 = 482215) B482215
theorem B1626095 : Blo 424774 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B480199 : Blo 424774 480199 := bstep (se 1 (by rfl) ⟨360149, by rfl⟩ : syracuseStep 480199 = 720299) B720299
theorem B480559 : Blo 424774 480559 := bstep (se 1 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 480559 = 720839) B720839
theorem B546103 : Blo 424774 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B3462671 : Blo 424774 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B874127 : Blo 424774 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B481063 : Blo 424774 481063 := bstep (se 1 (by rfl) ⟨360797, by rfl⟩ : syracuseStep 481063 = 721595) B721595
theorem B973075 : Blo 424774 973075 := bstep (se 1 (by rfl) ⟨729806, by rfl⟩ : syracuseStep 973075 = 1459613) B1459613
theorem B809767 : Blo 424774 809767 := bstep (se 1 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 809767 = 1214651) B1214651
theorem B3070781 : Blo 424774 3070781 := bstep (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) B1151543
theorem B45505925 : Blo 424774 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B8183207 : Blo 424774 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B1236905 : Blo 424774 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B2154599 : Blo 424774 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B4613051 : Blo 424774 4613051 := bstep (se 1 (by rfl) ⟨3459788, by rfl⟩ : syracuseStep 4613051 = 6919577) B6919577
theorem B812015 : Blo 424774 812015 := bstep (se 1 (by rfl) ⟨609011, by rfl⟩ : syracuseStep 812015 = 1218023) B1218023
theorem B1434671 : Blo 424774 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B7300205 : Blo 424774 7300205 := bstep (se 3 (by rfl) ⟨1368788, by rfl⟩ : syracuseStep 7300205 = 2737577) B2737577
theorem B1369199 : Blo 424774 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B4843475 : Blo 424774 4843475 := bstep (se 1 (by rfl) ⟨3632606, by rfl⟩ : syracuseStep 4843475 = 7265213) B7265213
theorem B682319 : Blo 424774 682319 := bstep (se 1 (by rfl) ⟨511739, by rfl⟩ : syracuseStep 682319 = 1023479) B1023479
theorem B3631787 : Blo 424774 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B7563959 : Blo 424774 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B2419415 : Blo 424774 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B5172173 : Blo 424774 5172173 := bstep (se 3 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 5172173 = 1939565) B1939565
theorem B683003 : Blo 424774 683003 := bstep (se 1 (by rfl) ⟨512252, by rfl⟩ : syracuseStep 683003 = 1024505) B1024505
theorem B1076399 : Blo 424774 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B1372403 : Blo 424774 1372403 := bstep (se 1 (by rfl) ⟨1029302, by rfl⟩ : syracuseStep 1372403 = 2058605) B2058605
theorem B2584943 : Blo 424774 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B1372571 : Blo 424774 1372571 := bstep (se 1 (by rfl) ⟨1029428, by rfl⟩ : syracuseStep 1372571 = 2058857) B2058857
theorem B5468957 : Blo 424774 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B1536889 : Blo 424774 1536889 := bstep (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) B1152667
theorem B2421647 : Blo 424774 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B1078343 : Blo 424774 1078343 := bstep (se 1 (by rfl) ⟨808757, by rfl⟩ : syracuseStep 1078343 = 1617515) B1617515
theorem B1078393 : Blo 424774 1078393 := bstep (se 2 (by rfl) ⟨404397, by rfl⟩ : syracuseStep 1078393 = 808795) B808795
theorem B6255755 : Blo 424774 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B718409 : Blo 424774 718409 := bstep (se 2 (by rfl) ⟨269403, by rfl⟩ : syracuseStep 718409 = 538807) B538807
theorem B2225951 : Blo 424774 2225951 := bstep (se 1 (by rfl) ⟨1669463, by rfl⟩ : syracuseStep 2225951 = 3338927) B3338927
theorem B9369589 : Blo 424774 9369589 := bstep (se 5 (by rfl) ⟨439199, by rfl⟩ : syracuseStep 9369589 = 878399) B878399
theorem B718969 : Blo 424774 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B719023 : Blo 424774 719023 := bstep (se 1 (by rfl) ⟨539267, by rfl⟩ : syracuseStep 719023 = 1078535) B1078535
theorem B1079801 : Blo 424774 1079801 := bstep (se 2 (by rfl) ⟨404925, by rfl⟩ : syracuseStep 1079801 = 809851) B809851
theorem B27753029 : Blo 424774 27753029 := bstep (se 4 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 27753029 = 5203693) B5203693
theorem B1211051 : Blo 424774 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B1080175 : Blo 424774 1080175 := bstep (se 1 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 1080175 = 1620263) B1620263
theorem B424927 : Blo 424774 424927 := bstep (se 1 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 424927 = 637391) B637391
theorem B2423789 : Blo 424774 2423789 := bstep (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) B908921
theorem B424987 : Blo 424774 424987 := bstep (se 1 (by rfl) ⟨318740, by rfl⟩ : syracuseStep 424987 = 637481) B637481
theorem B425115 : Blo 424774 425115 := bstep (se 1 (by rfl) ⟨318836, by rfl⟩ : syracuseStep 425115 = 637673) B637673
theorem B2161889 : Blo 424774 2161889 := bstep (se 2 (by rfl) ⟨810708, by rfl⟩ : syracuseStep 2161889 = 1621417) B1621417
theorem B19004669 : Blo 424774 19004669 := bstep (se 3 (by rfl) ⟨3563375, by rfl⟩ : syracuseStep 19004669 = 7126751) B7126751
theorem B1441043 : Blo 424774 1441043 := bstep (se 1 (by rfl) ⟨1080782, by rfl⟩ : syracuseStep 1441043 = 2161565) B2161565
theorem B425371 : Blo 424774 425371 := bstep (se 1 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 425371 = 638057) B638057
theorem B1736171 : Blo 424774 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B425455 : Blo 424774 425455 := bstep (se 1 (by rfl) ⟨319091, by rfl⟩ : syracuseStep 425455 = 638183) B638183
theorem B1080823 : Blo 424774 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B2424563 : Blo 424774 2424563 := bstep (se 1 (by rfl) ⟨1818422, by rfl⟩ : syracuseStep 2424563 = 3636845) B3636845
theorem B425791 : Blo 424774 425791 := bstep (se 1 (by rfl) ⟨319343, by rfl⟩ : syracuseStep 425791 = 638687) B638687
theorem B425819 : Blo 424774 425819 := bstep (se 1 (by rfl) ⟨319364, by rfl⟩ : syracuseStep 425819 = 638729) B638729
theorem B720731 : Blo 424774 720731 := bstep (se 1 (by rfl) ⟨540548, by rfl⟩ : syracuseStep 720731 = 1081097) B1081097
theorem B720751 : Blo 424774 720751 := bstep (se 1 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 720751 = 1081127) B1081127
theorem B426075 : Blo 424774 426075 := bstep (se 1 (by rfl) ⟨319556, by rfl⟩ : syracuseStep 426075 = 639113) B639113
theorem B426139 : Blo 424774 426139 := bstep (se 1 (by rfl) ⟨319604, by rfl⟩ : syracuseStep 426139 = 639209) B639209
theorem B1441961 : Blo 424774 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B426223 : Blo 424774 426223 := bstep (se 1 (by rfl) ⟨319667, by rfl⟩ : syracuseStep 426223 = 639335) B639335
theorem B426303 : Blo 424774 426303 := bstep (se 1 (by rfl) ⟨319727, by rfl⟩ : syracuseStep 426303 = 639455) B639455
theorem B426471 : Blo 424774 426471 := bstep (se 1 (by rfl) ⟨319853, by rfl⟩ : syracuseStep 426471 = 639707) B639707
theorem B10420919 : Blo 424774 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B1082099 : Blo 424774 1082099 := bstep (se 1 (by rfl) ⟨811574, by rfl⟩ : syracuseStep 1082099 = 1623149) B1623149
theorem B426747 : Blo 424774 426747 := bstep (se 1 (by rfl) ⟨320060, by rfl⟩ : syracuseStep 426747 = 640121) B640121
theorem B3736343 : Blo 424774 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B426879 : Blo 424774 426879 := bstep (se 1 (by rfl) ⟨320159, by rfl⟩ : syracuseStep 426879 = 640319) B640319
theorem B1082423 : Blo 424774 1082423 := bstep (se 1 (by rfl) ⟨811817, by rfl⟩ : syracuseStep 1082423 = 1623635) B1623635
theorem B2360495 : Blo 424774 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B427327 : Blo 424774 427327 := bstep (se 1 (by rfl) ⟨320495, by rfl⟩ : syracuseStep 427327 = 640991) B640991
theorem B427367 : Blo 424774 427367 := bstep (se 1 (by rfl) ⟨320525, by rfl⟩ : syracuseStep 427367 = 641051) B641051
theorem B427471 : Blo 424774 427471 := bstep (se 1 (by rfl) ⟨320603, by rfl⟩ : syracuseStep 427471 = 641207) B641207
theorem B427487 : Blo 424774 427487 := bstep (se 1 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 427487 = 641231) B641231
theorem B1443311 : Blo 424774 1443311 := bstep (se 1 (by rfl) ⟨1082483, by rfl⟩ : syracuseStep 1443311 = 2164967) B2164967
theorem B427751 : Blo 424774 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B427847 : Blo 424774 427847 := bstep (se 1 (by rfl) ⟨320885, by rfl⟩ : syracuseStep 427847 = 641771) B641771
theorem B427867 : Blo 424774 427867 := bstep (se 1 (by rfl) ⟨320900, by rfl⟩ : syracuseStep 427867 = 641801) B641801
theorem B428143 : Blo 424774 428143 := bstep (se 1 (by rfl) ⟨321107, by rfl⟩ : syracuseStep 428143 = 642215) B642215
theorem B428239 : Blo 424774 428239 := bstep (se 1 (by rfl) ⟨321179, by rfl⟩ : syracuseStep 428239 = 642359) B642359
theorem B1444175 : Blo 424774 1444175 := bstep (se 1 (by rfl) ⟨1083131, by rfl⟩ : syracuseStep 1444175 = 2166263) B2166263
theorem B428447 : Blo 424774 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B788935 : Blo 424774 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B428495 : Blo 424774 428495 := bstep (se 1 (by rfl) ⟨321371, by rfl⟩ : syracuseStep 428495 = 642743) B642743
theorem B428527 : Blo 424774 428527 := bstep (se 1 (by rfl) ⟨321395, by rfl⟩ : syracuseStep 428527 = 642791) B642791
theorem B428635 : Blo 424774 428635 := bstep (se 1 (by rfl) ⟨321476, by rfl⟩ : syracuseStep 428635 = 642953) B642953
theorem B1084063 : Blo 424774 1084063 := bstep (se 1 (by rfl) ⟨813047, by rfl⟩ : syracuseStep 1084063 = 1626095) B1626095
theorem B2165615 : Blo 424774 2165615 := bstep (se 1 (by rfl) ⟨1624211, by rfl⟩ : syracuseStep 2165615 = 3248423) B3248423
theorem B1445687 : Blo 424774 1445687 := bstep (se 1 (by rfl) ⟨1084265, by rfl⟩ : syracuseStep 1445687 = 2168531) B2168531
theorem B1544417 : Blo 424774 1544417 := bstep (se 2 (by rfl) ⟨579156, by rfl⟩ : syracuseStep 1544417 = 1158313) B1158313
theorem B1446767 : Blo 424774 1446767 := bstep (se 1 (by rfl) ⟨1085075, by rfl⟩ : syracuseStep 1446767 = 2170151) B2170151
theorem B988127 : Blo 424774 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B824603 : Blo 424774 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B1873405 : Blo 424774 1873405 := bstep (se 3 (by rfl) ⟨351263, by rfl⟩ : syracuseStep 1873405 = 702527) B702527
theorem B13178771 : Blo 424774 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B956447 : Blo 424774 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B209852765 : Blo 424774 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B4659551 : Blo 424774 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B728137 : Blo 424774 728137 := bstep (se 2 (by rfl) ⟨273051, by rfl⟩ : syracuseStep 728137 = 546103) B546103
theorem B1612943 : Blo 424774 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B3448115 : Blo 424774 3448115 := bstep (se 1 (by rfl) ⟨2586086, by rfl⟩ : syracuseStep 3448115 = 5172173) B5172173
theorem B728767 : Blo 424774 728767 := bstep (se 1 (by rfl) ⟨546575, by rfl⟩ : syracuseStep 728767 = 1093151) B1093151
theorem B2432855 : Blo 424774 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B12492785 : Blo 424774 12492785 := bstep (se 2 (by rfl) ⟨4684794, by rfl⟩ : syracuseStep 12492785 = 9369589) B9369589
theorem B729143 : Blo 424774 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B958625 : Blo 424774 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B958697 : Blo 424774 958697 := bstep (se 2 (by rfl) ⟨359511, by rfl⟩ : syracuseStep 958697 = 719023) B719023
theorem B3645971 : Blo 424774 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B1614431 : Blo 424774 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B4170503 : Blo 424774 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B1483967 : Blo 424774 1483967 := bstep (se 1 (by rfl) ⟨1112975, by rfl⟩ : syracuseStep 1483967 = 2225951) B2225951
theorem B3253769 : Blo 424774 3253769 := bstep (se 2 (by rfl) ⟨1220163, by rfl⟩ : syracuseStep 3253769 = 2440327) B2440327
theorem B1615859 : Blo 424774 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B960695 : Blo 424774 960695 := bstep (se 1 (by rfl) ⟨720521, by rfl⟩ : syracuseStep 960695 = 1441043) B1441043
theorem B1157447 : Blo 424774 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B961001 : Blo 424774 961001 := bstep (se 2 (by rfl) ⟨360375, by rfl⟩ : syracuseStep 961001 = 720751) B720751
theorem B1616375 : Blo 424774 1616375 := bstep (se 1 (by rfl) ⟨1212281, by rfl⟩ : syracuseStep 1616375 = 2424563) B2424563
theorem B1616831 : Blo 424774 1616831 := bstep (se 1 (by rfl) ⟨1212623, by rfl⟩ : syracuseStep 1616831 = 2425247) B2425247
theorem B863399 : Blo 424774 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B1618015 : Blo 424774 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B962729 : Blo 424774 962729 := bstep (se 2 (by rfl) ⟨361023, by rfl⟩ : syracuseStep 962729 = 722047) B722047
theorem B963359 : Blo 424774 963359 := bstep (se 1 (by rfl) ⟨722519, by rfl⟩ : syracuseStep 963359 = 1445039) B1445039
theorem B1619291 : Blo 424774 1619291 := bstep (se 1 (by rfl) ⟨1214468, by rfl⟩ : syracuseStep 1619291 = 2428937) B2428937
theorem B1815929 : Blo 424774 1815929 := bstep (se 2 (by rfl) ⟨680973, by rfl⟩ : syracuseStep 1815929 = 1361947) B1361947
theorem B8009441 : Blo 424774 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B1030043 : Blo 424774 1030043 := bstep (se 1 (by rfl) ⟨772532, by rfl⟩ : syracuseStep 1030043 = 1545065) B1545065
theorem B1292267 : Blo 424774 1292267 := bstep (se 1 (by rfl) ⟨969200, by rfl⟩ : syracuseStep 1292267 = 1938401) B1938401
theorem B2308447 : Blo 424774 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B637343 : Blo 424774 637343 := bstep (se 1 (by rfl) ⟨478007, by rfl⟩ : syracuseStep 637343 = 956015) B956015
theorem B3062245 : Blo 424774 3062245 := bstep (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) B574171
theorem B2047187 : Blo 424774 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B638441 : Blo 424774 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B5455471 : Blo 424774 5455471 := bstep (se 1 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 5455471 = 8183207) B8183207
theorem B1294319 : Blo 424774 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B1622375 : Blo 424774 1622375 := bstep (se 1 (by rfl) ⟨1216781, by rfl⟩ : syracuseStep 1622375 = 2433563) B2433563
theorem B639467 : Blo 424774 639467 := bstep (se 1 (by rfl) ⟨479600, by rfl⟩ : syracuseStep 639467 = 959201) B959201
theorem B541343 : Blo 424774 541343 := bstep (se 1 (by rfl) ⟨406007, by rfl⟩ : syracuseStep 541343 = 812015) B812015
theorem B4866803 : Blo 424774 4866803 := bstep (se 1 (by rfl) ⟨3650102, by rfl⟩ : syracuseStep 4866803 = 7300205) B7300205
theorem B640091 : Blo 424774 640091 := bstep (se 1 (by rfl) ⟨480068, by rfl⟩ : syracuseStep 640091 = 960137) B960137
theorem B640127 : Blo 424774 640127 := bstep (se 1 (by rfl) ⟨480095, by rfl⟩ : syracuseStep 640127 = 960191) B960191
theorem B1623179 : Blo 424774 1623179 := bstep (se 1 (by rfl) ⟨1217384, by rfl⟩ : syracuseStep 1623179 = 2434769) B2434769
theorem B2049185 : Blo 424774 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B640265 : Blo 424774 640265 := bstep (se 2 (by rfl) ⟨240099, by rfl⟩ : syracuseStep 640265 = 480199) B480199
theorem B3228983 : Blo 424774 3228983 := bstep (se 1 (by rfl) ⟨2421737, by rfl⟩ : syracuseStep 3228983 = 4843475) B4843475
theorem B640745 : Blo 424774 640745 := bstep (se 2 (by rfl) ⟨240279, by rfl⟩ : syracuseStep 640745 = 480559) B480559
theorem B3229469 : Blo 424774 3229469 := bstep (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) B1211051
theorem B1623847 : Blo 424774 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B6211565 : Blo 424774 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B1820663 : Blo 424774 1820663 := bstep (se 1 (by rfl) ⟨1365497, by rfl⟩ : syracuseStep 1820663 = 2730995) B2730995
theorem B641279 : Blo 424774 641279 := bstep (se 1 (by rfl) ⟨480959, by rfl⟩ : syracuseStep 641279 = 961919) B961919
theorem B641417 : Blo 424774 641417 := bstep (se 2 (by rfl) ⟨240531, by rfl⟩ : syracuseStep 641417 = 481063) B481063
theorem B641915 : Blo 424774 641915 := bstep (se 1 (by rfl) ⟨481436, by rfl⟩ : syracuseStep 641915 = 962873) B962873
theorem B1723295 : Blo 424774 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B1297433 : Blo 424774 1297433 := bstep (se 2 (by rfl) ⟨486537, by rfl⟩ : syracuseStep 1297433 = 973075) B973075
theorem B1166543 : Blo 424774 1166543 := bstep (se 1 (by rfl) ⟨874907, by rfl⟩ : syracuseStep 1166543 = 1749815) B1749815
theorem B2739527 : Blo 424774 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B478939 : Blo 424774 478939 := bstep (se 1 (by rfl) ⟨359204, by rfl⟩ : syracuseStep 478939 = 718409) B718409
theorem B642983 : Blo 424774 642983 := bstep (se 1 (by rfl) ⟨482237, by rfl⟩ : syracuseStep 642983 = 964475) B964475
theorem B512191 : Blo 424774 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B512335 : Blo 424774 512335 := bstep (se 1 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 512335 = 768503) B768503
theorem B6148477 : Blo 424774 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B18502019 : Blo 424774 18502019 := bstep (se 1 (by rfl) ⟨13876514, by rfl⟩ : syracuseStep 18502019 = 27753029) B27753029
theorem B12669779 : Blo 424774 12669779 := bstep (se 1 (by rfl) ⟨9502334, by rfl⟩ : syracuseStep 12669779 = 19004669) B19004669
theorem B1954759 : Blo 424774 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B15258631 : Blo 424774 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B480487 : Blo 424774 480487 := bstep (se 1 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 480487 = 720731) B720731
theorem B5822239 : Blo 424774 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B3659741 : Blo 424774 3659741 := bstep (se 3 (by rfl) ⟨686201, by rfl⟩ : syracuseStep 3659741 = 1372403) B1372403
theorem B3233843 : Blo 424774 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B481639 : Blo 424774 481639 := bstep (se 1 (by rfl) ⟨361229, by rfl⟩ : syracuseStep 481639 = 722459) B722459
theorem B908255 : Blo 424774 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B1727867 : Blo 424774 1727867 := bstep (se 1 (by rfl) ⟨1295900, by rfl⟩ : syracuseStep 1727867 = 2591801) B2591801
theorem B12345857 : Blo 424774 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B1532969 : Blo 424774 1532969 := bstep (se 2 (by rfl) ⟨574863, by rfl⟩ : syracuseStep 1532969 = 1149727) B1149727
theorem B582751 : Blo 424774 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B30337283 : Blo 424774 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B1436399 : Blo 424774 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B5466953 : Blo 424774 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B1731451 : Blo 424774 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B3075367 : Blo 424774 3075367 := bstep (se 1 (by rfl) ⟨2306525, by rfl⟩ : syracuseStep 3075367 = 4613051) B4613051
theorem B10415465 : Blo 424774 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B912799 : Blo 424774 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B1437857 : Blo 424774 1437857 := bstep (se 2 (by rfl) ⟨539196, by rfl⟩ : syracuseStep 1437857 = 1078393) B1078393
theorem B6254813 : Blo 424774 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B454879 : Blo 424774 454879 := bstep (se 1 (by rfl) ⟨341159, by rfl⟩ : syracuseStep 454879 = 682319) B682319
theorem B3240161 : Blo 424774 3240161 := bstep (se 2 (by rfl) ⟨1215060, by rfl⟩ : syracuseStep 3240161 = 2430121) B2430121
theorem B3633497 : Blo 424774 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B2421191 : Blo 424774 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B5042639 : Blo 424774 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B455335 : Blo 424774 455335 := bstep (se 1 (by rfl) ⟨341501, by rfl⟩ : syracuseStep 455335 = 683003) B683003
theorem B717599 : Blo 424774 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B3634247 : Blo 424774 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B915047 : Blo 424774 915047 := bstep (se 1 (by rfl) ⟨686285, by rfl⟩ : syracuseStep 915047 = 1372571) B1372571
theorem B3700541 : Blo 424774 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B718895 : Blo 424774 718895 := bstep (se 1 (by rfl) ⟨539171, by rfl⟩ : syracuseStep 718895 = 1078343) B1078343
theorem B3242105 : Blo 424774 3242105 := bstep (se 2 (by rfl) ⟨1215789, by rfl⟩ : syracuseStep 3242105 = 2431579) B2431579
theorem B1079689 : Blo 424774 1079689 := bstep (se 2 (by rfl) ⟨404883, by rfl⟩ : syracuseStep 1079689 = 809767) B809767
theorem B1440233 : Blo 424774 1440233 := bstep (se 2 (by rfl) ⟨540087, by rfl⟩ : syracuseStep 1440233 = 1080175) B1080175
theorem B2161241 : Blo 424774 2161241 := bstep (se 2 (by rfl) ⟨810465, by rfl⟩ : syracuseStep 2161241 = 1620931) B1620931
theorem B424943 : Blo 424774 424943 := bstep (se 1 (by rfl) ⟨318707, by rfl⟩ : syracuseStep 424943 = 637415) B637415
theorem B719867 : Blo 424774 719867 := bstep (se 1 (by rfl) ⟨539900, by rfl⟩ : syracuseStep 719867 = 1079801) B1079801
theorem B424991 : Blo 424774 424991 := bstep (se 1 (by rfl) ⟨318743, by rfl⟩ : syracuseStep 424991 = 637487) B637487
theorem B1441097 : Blo 424774 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B425439 : Blo 424774 425439 := bstep (se 1 (by rfl) ⟨319079, by rfl⟩ : syracuseStep 425439 = 638159) B638159
theorem B1441259 : Blo 424774 1441259 := bstep (se 1 (by rfl) ⟨1080944, by rfl⟩ : syracuseStep 1441259 = 2161889) B2161889
theorem B425499 : Blo 424774 425499 := bstep (se 1 (by rfl) ⟨319124, by rfl⟩ : syracuseStep 425499 = 638249) B638249
theorem B425519 : Blo 424774 425519 := bstep (se 1 (by rfl) ⟨319139, by rfl⟩ : syracuseStep 425519 = 638279) B638279
theorem B425919 : Blo 424774 425919 := bstep (se 1 (by rfl) ⟨319439, by rfl⟩ : syracuseStep 425919 = 638879) B638879
theorem B425979 : Blo 424774 425979 := bstep (se 1 (by rfl) ⟨319484, by rfl⟩ : syracuseStep 425979 = 638969) B638969
theorem B1081583 : Blo 424774 1081583 := bstep (se 1 (by rfl) ⟨811187, by rfl⟩ : syracuseStep 1081583 = 1622375) B1622375
theorem B426311 : Blo 424774 426311 := bstep (se 1 (by rfl) ⟨319733, by rfl⟩ : syracuseStep 426311 = 639467) B639467
theorem B6947279 : Blo 424774 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B721399 : Blo 424774 721399 := bstep (se 1 (by rfl) ⟨541049, by rfl⟩ : syracuseStep 721399 = 1082099) B1082099
theorem B3244535 : Blo 424774 3244535 := bstep (se 1 (by rfl) ⟨2433401, by rfl⟩ : syracuseStep 3244535 = 4866803) B4866803
theorem B2490895 : Blo 424774 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B721615 : Blo 424774 721615 := bstep (se 1 (by rfl) ⟨541211, by rfl⟩ : syracuseStep 721615 = 1082423) B1082423
theorem B426727 : Blo 424774 426727 := bstep (se 1 (by rfl) ⟨320045, by rfl⟩ : syracuseStep 426727 = 640091) B640091
theorem B426751 : Blo 424774 426751 := bstep (se 1 (by rfl) ⟨320063, by rfl⟩ : syracuseStep 426751 = 640127) B640127
theorem B1082119 : Blo 424774 1082119 := bstep (se 1 (by rfl) ⟨811589, by rfl⟩ : syracuseStep 1082119 = 1623179) B1623179
theorem B1573663 : Blo 424774 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B426843 : Blo 424774 426843 := bstep (se 1 (by rfl) ⟨320132, by rfl⟩ : syracuseStep 426843 = 640265) B640265
theorem B427163 : Blo 424774 427163 := bstep (se 1 (by rfl) ⟨320372, by rfl⟩ : syracuseStep 427163 = 640745) B640745
theorem B2426021 : Blo 424774 2426021 := bstep (se 4 (by rfl) ⟨227439, by rfl⟩ : syracuseStep 2426021 = 454879) B454879
theorem B1213775 : Blo 424774 1213775 := bstep (se 1 (by rfl) ⟨910331, by rfl⟩ : syracuseStep 1213775 = 1820663) B1820663
theorem B427519 : Blo 424774 427519 := bstep (se 1 (by rfl) ⟨320639, by rfl⟩ : syracuseStep 427519 = 641279) B641279
theorem B427611 : Blo 424774 427611 := bstep (se 1 (by rfl) ⟨320708, by rfl⟩ : syracuseStep 427611 = 641417) B641417
theorem B1443581 : Blo 424774 1443581 := bstep (se 3 (by rfl) ⟨270671, by rfl⟩ : syracuseStep 1443581 = 541343) B541343
theorem B1443743 : Blo 424774 1443743 := bstep (se 1 (by rfl) ⟨1082807, by rfl⟩ : syracuseStep 1443743 = 2165615) B2165615
theorem B427943 : Blo 424774 427943 := bstep (se 1 (by rfl) ⟨320957, by rfl⟩ : syracuseStep 427943 = 641915) B641915
theorem B1148863 : Blo 424774 1148863 := bstep (se 1 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 1148863 = 1723295) B1723295
theorem B2165129 : Blo 424774 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B428655 : Blo 424774 428655 := bstep (se 1 (by rfl) ⟨321491, by rfl⟩ : syracuseStep 428655 = 642983) B642983
theorem B1051913 : Blo 424774 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B658751 : Blo 424774 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B2428453 : Blo 424774 2428453 := bstep (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) B455335
theorem B1445417 : Blo 424774 1445417 := bstep (se 2 (by rfl) ⟨542031, by rfl⟩ : syracuseStep 1445417 = 1084063) B1084063
theorem B8785847 : Blo 424774 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B4100489 : Blo 424774 4100489 := bstep (se 2 (by rfl) ⟨1537683, by rfl⟩ : syracuseStep 4100489 = 3075367) B3075367
theorem B2298743 : Blo 424774 2298743 := bstep (se 1 (by rfl) ⟨1724057, by rfl⟩ : syracuseStep 2298743 = 3448115) B3448115
theorem B1151911 : Blo 424774 1151911 := bstep (se 1 (by rfl) ⟨863933, by rfl⟩ : syracuseStep 1151911 = 1727867) B1727867
theorem B8230571 : Blo 424774 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B2430647 : Blo 424774 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B8197969 : Blo 424774 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B1021979 : Blo 424774 1021979 := bstep (se 1 (by rfl) ⟨766484, by rfl⟩ : syracuseStep 1021979 = 1532969) B1532969
theorem B3086525 : Blo 424774 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B2169179 : Blo 424774 2169179 := bstep (se 1 (by rfl) ⟨1626884, by rfl⟩ : syracuseStep 2169179 = 3253769) B3253769
theorem B20224855 : Blo 424774 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B957599 : Blo 424774 957599 := bstep (se 1 (by rfl) ⟨718199, by rfl⟩ : syracuseStep 957599 = 1436399) B1436399
theorem B3644635 : Blo 424774 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B2497873 : Blo 424774 2497873 := bstep (se 2 (by rfl) ⟨936702, by rfl⟩ : syracuseStep 2497873 = 1873405) B1873405
theorem B958571 : Blo 424774 958571 := bstep (se 1 (by rfl) ⟨718928, by rfl⟩ : syracuseStep 958571 = 1437857) B1437857
theorem B4169875 : Blo 424774 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B1614127 : Blo 424774 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B2467027 : Blo 424774 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B861511 : Blo 424774 861511 := bstep (se 1 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 861511 = 1292267) B1292267
theorem B960155 : Blo 424774 960155 := bstep (se 1 (by rfl) ⟨720116, by rfl⟩ : syracuseStep 960155 = 1440233) B1440233
theorem B960731 : Blo 424774 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B960839 : Blo 424774 960839 := bstep (se 1 (by rfl) ⟨720629, by rfl⟩ : syracuseStep 960839 = 1441259) B1441259
theorem B862879 : Blo 424774 862879 := bstep (se 1 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 862879 = 1294319) B1294319
theorem B961307 : Blo 424774 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B962207 : Blo 424774 962207 := bstep (se 1 (by rfl) ⟨721655, by rfl⟩ : syracuseStep 962207 = 1443311) B1443311
theorem B13447037 : Blo 424774 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B4141043 : Blo 424774 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B962783 : Blo 424774 962783 := bstep (se 1 (by rfl) ⟨722087, by rfl⟩ : syracuseStep 962783 = 1444175) B1444175
theorem B2732453 : Blo 424774 2732453 := bstep (se 4 (by rfl) ⟨256167, by rfl⟩ : syracuseStep 2732453 = 512335) B512335
theorem B864955 : Blo 424774 864955 := bstep (se 1 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 864955 = 1297433) B1297433
theorem B963791 : Blo 424774 963791 := bstep (se 1 (by rfl) ⟨722843, by rfl⟩ : syracuseStep 963791 = 1445687) B1445687
theorem B1029611 : Blo 424774 1029611 := bstep (se 1 (by rfl) ⟨772208, by rfl⟩ : syracuseStep 1029611 = 1544417) B1544417
theorem B12334679 : Blo 424774 12334679 := bstep (se 1 (by rfl) ⟨9251009, by rfl⟩ : syracuseStep 12334679 = 18502019) B18502019
theorem B8795765 : Blo 424774 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B964511 : Blo 424774 964511 := bstep (se 1 (by rfl) ⟨723383, by rfl⟩ : syracuseStep 964511 = 1446767) B1446767
theorem B2308601 : Blo 424774 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B2439827 : Blo 424774 2439827 := bstep (se 1 (by rfl) ⟨1829870, by rfl⟩ : syracuseStep 2439827 = 3659741) B3659741
theorem B637631 : Blo 424774 637631 := bstep (se 1 (by rfl) ⟨478223, by rfl⟩ : syracuseStep 637631 = 956447) B956447
theorem B139901843 : Blo 424774 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B605503 : Blo 424774 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B638585 : Blo 424774 638585 := bstep (se 2 (by rfl) ⟨239469, by rfl⟩ : syracuseStep 638585 = 478939) B478939
theorem B1621903 : Blo 424774 1621903 := bstep (se 1 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 1621903 = 2432855) B2432855
theorem B639083 : Blo 424774 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B639131 : Blo 424774 639131 := bstep (se 1 (by rfl) ⟨479348, by rfl⟩ : syracuseStep 639131 = 958697) B958697
theorem B2606345 : Blo 424774 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B640463 : Blo 424774 640463 := bstep (se 1 (by rfl) ⟨480347, by rfl⟩ : syracuseStep 640463 = 960695) B960695
theorem B640649 : Blo 424774 640649 := bstep (se 2 (by rfl) ⟨240243, by rfl⟩ : syracuseStep 640649 = 480487) B480487
theorem B640667 : Blo 424774 640667 := bstep (se 1 (by rfl) ⟨480500, by rfl⟩ : syracuseStep 640667 = 961001) B961001
theorem B575599 : Blo 424774 575599 := bstep (se 1 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 575599 = 863399) B863399
theorem B4868261 : Blo 424774 4868261 := bstep (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) B912799
theorem B641819 : Blo 424774 641819 := bstep (se 1 (by rfl) ⟨481364, by rfl⟩ : syracuseStep 641819 = 962729) B962729
theorem B642185 : Blo 424774 642185 := bstep (se 2 (by rfl) ⟨240819, by rfl⟩ : syracuseStep 642185 = 481639) B481639
theorem B478399 : Blo 424774 478399 := bstep (se 1 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 478399 = 717599) B717599
theorem B642239 : Blo 424774 642239 := bstep (se 1 (by rfl) ⟨481679, by rfl⟩ : syracuseStep 642239 = 963359) B963359
theorem B4082993 : Blo 424774 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B610031 : Blo 424774 610031 := bstep (se 1 (by rfl) ⟨457523, by rfl⟩ : syracuseStep 610031 = 915047) B915047
theorem B479263 : Blo 424774 479263 := bstep (se 1 (by rfl) ⟨359447, by rfl⟩ : syracuseStep 479263 = 718895) B718895
theorem B970849 : Blo 424774 970849 := bstep (se 2 (by rfl) ⟨364068, by rfl⟩ : syracuseStep 970849 = 728137) B728137
theorem B479911 : Blo 424774 479911 := bstep (se 1 (by rfl) ⟨359933, by rfl⟩ : syracuseStep 479911 = 719867) B719867
theorem B1364791 : Blo 424774 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B971689 : Blo 424774 971689 := bstep (se 2 (by rfl) ⟨364383, by rfl⟩ : syracuseStep 971689 = 728767) B728767
theorem B33314093 : Blo 424774 33314093 := bstep (se 3 (by rfl) ⟨6246392, by rfl⟩ : syracuseStep 33314093 = 12492785) B12492785
theorem B2152655 : Blo 424774 2152655 := bstep (se 1 (by rfl) ⟨1614491, by rfl⟩ : syracuseStep 2152655 = 3228983) B3228983
theorem B2152979 : Blo 424774 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B777001 : Blo 424774 777001 := bstep (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) B582751
theorem B777695 : Blo 424774 777695 := bstep (se 1 (by rfl) ⟨583271, by rfl⟩ : syracuseStep 777695 = 1166543) B1166543
theorem B1826351 : Blo 424774 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B5464493 : Blo 424774 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B3957245 : Blo 424774 3957245 := bstep (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) B1483967
theorem B8446519 : Blo 424774 8446519 := bstep (se 1 (by rfl) ⟨6334889, by rfl⟩ : syracuseStep 8446519 = 12669779) B12669779
theorem B2155895 : Blo 424774 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B3106367 : Blo 424774 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B1075295 : Blo 424774 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B2746781 : Blo 424774 2746781 := bstep (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) B1030043
theorem B486095 : Blo 424774 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B2157353 : Blo 424774 2157353 := bstep (se 2 (by rfl) ⟨809007, by rfl⟩ : syracuseStep 2157353 = 1618015) B1618015
theorem B682921 : Blo 424774 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B1076287 : Blo 424774 1076287 := bstep (se 1 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 1076287 = 1614431) B1614431
theorem B2780335 : Blo 424774 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B1077239 : Blo 424774 1077239 := bstep (se 1 (by rfl) ⟨807929, by rfl⟩ : syracuseStep 1077239 = 1615859) B1615859
theorem B20344841 : Blo 424774 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B1077583 : Blo 424774 1077583 := bstep (se 1 (by rfl) ⟨808187, by rfl⟩ : syracuseStep 1077583 = 1616375) B1616375
theorem B1077887 : Blo 424774 1077887 := bstep (se 1 (by rfl) ⟨808415, by rfl⟩ : syracuseStep 1077887 = 1616831) B1616831
theorem B6943643 : Blo 424774 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B7762985 : Blo 424774 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B2160107 : Blo 424774 2160107 := bstep (se 1 (by rfl) ⟨1620080, by rfl⟩ : syracuseStep 2160107 = 3240161) B3240161
theorem B2422331 : Blo 424774 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B3077929 : Blo 424774 3077929 := bstep (se 2 (by rfl) ⟨1154223, by rfl⟩ : syracuseStep 3077929 = 2308447) B2308447
theorem B1439585 : Blo 424774 1439585 := bstep (se 2 (by rfl) ⟨539844, by rfl⟩ : syracuseStep 1439585 = 1079689) B1079689
theorem B2422831 : Blo 424774 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B1079527 : Blo 424774 1079527 := bstep (se 1 (by rfl) ⟨809645, by rfl⟩ : syracuseStep 1079527 = 1619291) B1619291
theorem B1210619 : Blo 424774 1210619 := bstep (se 1 (by rfl) ⟨907964, by rfl⟩ : syracuseStep 1210619 = 1815929) B1815929
theorem B5339627 : Blo 424774 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B2161403 : Blo 424774 2161403 := bstep (se 1 (by rfl) ⟨1621052, by rfl⟩ : syracuseStep 2161403 = 3242105) B3242105
theorem B424895 : Blo 424774 424895 := bstep (se 1 (by rfl) ⟨318671, by rfl⟩ : syracuseStep 424895 = 637343) B637343
theorem B1440827 : Blo 424774 1440827 := bstep (se 1 (by rfl) ⟨1080620, by rfl⟩ : syracuseStep 1440827 = 2161241) B2161241
theorem B7273961 : Blo 424774 7273961 := bstep (se 2 (by rfl) ⟨2727735, by rfl⟩ : syracuseStep 7273961 = 5455471) B5455471
theorem B425627 : Blo 424774 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B426055 : Blo 424774 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B426087 : Blo 424774 426087 := bstep (se 1 (by rfl) ⟨319565, by rfl⟩ : syracuseStep 426087 = 639131) B639131
theorem B721055 : Blo 424774 721055 := bstep (se 1 (by rfl) ⟨540791, by rfl⟩ : syracuseStep 721055 = 1081583) B1081583
theorem B2163023 : Blo 424774 2163023 := bstep (se 1 (by rfl) ⟨1622267, by rfl⟩ : syracuseStep 2163023 = 3244535) B3244535
theorem B1737563 : Blo 424774 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B426975 : Blo 424774 426975 := bstep (se 1 (by rfl) ⟨320231, by rfl⟩ : syracuseStep 426975 = 640463) B640463
theorem B1442825 : Blo 424774 1442825 := bstep (se 2 (by rfl) ⟨541059, by rfl⟩ : syracuseStep 1442825 = 1082119) B1082119
theorem B2098217 : Blo 424774 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B427099 : Blo 424774 427099 := bstep (se 1 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 427099 = 640649) B640649
theorem B427111 : Blo 424774 427111 := bstep (se 1 (by rfl) ⟨320333, by rfl⟩ : syracuseStep 427111 = 640667) B640667
theorem B3245507 : Blo 424774 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B1443419 : Blo 424774 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B1148681 : Blo 424774 1148681 := bstep (se 2 (by rfl) ⟨430755, by rfl⟩ : syracuseStep 1148681 = 861511) B861511
theorem B427879 : Blo 424774 427879 := bstep (se 1 (by rfl) ⟨320909, by rfl⟩ : syracuseStep 427879 = 641819) B641819
theorem B428123 : Blo 424774 428123 := bstep (se 1 (by rfl) ⟨321092, by rfl⟩ : syracuseStep 428123 = 642185) B642185
theorem B428159 : Blo 424774 428159 := bstep (se 1 (by rfl) ⟨321119, by rfl⟩ : syracuseStep 428159 = 642239) B642239
theorem B2721995 : Blo 424774 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B1150505 : Blo 424774 1150505 := bstep (se 2 (by rfl) ⟨431439, by rfl⟩ : syracuseStep 1150505 = 862879) B862879
theorem B1446119 : Blo 424774 1446119 := bstep (se 1 (by rfl) ⟨1084589, by rfl⟩ : syracuseStep 1446119 = 2169179) B2169179
theorem B3642245 : Blo 424774 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1217567 : Blo 424774 1217567 := bstep (se 1 (by rfl) ⟨913175, by rfl⟩ : syracuseStep 1217567 = 1826351) B1826351
theorem B3642995 : Blo 424774 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B1153273 : Blo 424774 1153273 := bstep (se 2 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 1153273 = 864955) B864955
theorem B2070911 : Blo 424774 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B2760695 : Blo 424774 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B4629095 : Blo 424774 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1614887 : Blo 424774 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B959723 : Blo 424774 959723 := bstep (se 1 (by rfl) ⟨719792, by rfl⟩ : syracuseStep 959723 = 1439585) B1439585
theorem B2073853 : Blo 424774 2073853 := bstep (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) B777695
theorem B4859513 : Blo 424774 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B93267895 : Blo 424774 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B960551 : Blo 424774 960551 := bstep (se 1 (by rfl) ⟨720413, by rfl⟩ : syracuseStep 960551 = 1440827) B1440827
theorem B35858765 : Blo 424774 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B4631519 : Blo 424774 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B961865 : Blo 424774 961865 := bstep (se 2 (by rfl) ⟨360699, by rfl⟩ : syracuseStep 961865 = 721399) B721399
theorem B1617347 : Blo 424774 1617347 := bstep (se 1 (by rfl) ⟨1213010, by rfl⟩ : syracuseStep 1617347 = 2426021) B2426021
theorem B962153 : Blo 424774 962153 := bstep (se 2 (by rfl) ⟨360807, by rfl⟩ : syracuseStep 962153 = 721615) B721615
theorem B962387 : Blo 424774 962387 := bstep (se 1 (by rfl) ⟨721790, by rfl⟩ : syracuseStep 962387 = 1443581) B1443581
theorem B962495 : Blo 424774 962495 := bstep (se 1 (by rfl) ⟨721871, by rfl⟩ : syracuseStep 962495 = 1443743) B1443743
theorem B3289369 : Blo 424774 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B963611 : Blo 424774 963611 := bstep (se 1 (by rfl) ⟨722708, by rfl⟩ : syracuseStep 963611 = 1445417) B1445417
theorem B13284773 : Blo 424774 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B767465 : Blo 424774 767465 := bstep (se 2 (by rfl) ⟨287799, by rfl⟩ : syracuseStep 767465 = 575599) B575599
theorem B2733659 : Blo 424774 2733659 := bstep (se 1 (by rfl) ⟨2050244, by rfl⟩ : syracuseStep 2733659 = 4100489) B4100489
theorem B5487047 : Blo 424774 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B1620431 : Blo 424774 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B637865 : Blo 424774 637865 := bstep (se 2 (by rfl) ⟨239199, by rfl⟩ : syracuseStep 637865 = 478399) B478399
theorem B638399 : Blo 424774 638399 := bstep (se 1 (by rfl) ⟨478799, by rfl⟩ : syracuseStep 638399 = 957599) B957599
theorem B6143525 : Blo 424774 6143525 := bstep (se 4 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 6143525 = 1151911) B1151911
theorem B639017 : Blo 424774 639017 := bstep (se 2 (by rfl) ⟨239631, by rfl⟩ : syracuseStep 639017 = 479263) B479263
theorem B639047 : Blo 424774 639047 := bstep (se 1 (by rfl) ⟨479285, by rfl⟩ : syracuseStep 639047 = 958571) B958571
theorem B1294465 : Blo 424774 1294465 := bstep (se 2 (by rfl) ⟨485424, by rfl⟩ : syracuseStep 1294465 = 970849) B970849
theorem B2638163 : Blo 424774 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B639881 : Blo 424774 639881 := bstep (se 2 (by rfl) ⟨239955, by rfl⟩ : syracuseStep 639881 = 479911) B479911
theorem B14828453 : Blo 424774 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B1819721 : Blo 424774 1819721 := bstep (se 2 (by rfl) ⟨682395, by rfl⟩ : syracuseStep 1819721 = 1364791) B1364791
theorem B640103 : Blo 424774 640103 := bstep (se 1 (by rfl) ⟨480077, by rfl⟩ : syracuseStep 640103 = 960155) B960155
theorem B1295585 : Blo 424774 1295585 := bstep (se 2 (by rfl) ⟨485844, by rfl⟩ : syracuseStep 1295585 = 971689) B971689
theorem B640487 : Blo 424774 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B640559 : Blo 424774 640559 := bstep (se 1 (by rfl) ⟨480419, by rfl⟩ : syracuseStep 640559 = 960839) B960839
theorem B640871 : Blo 424774 640871 := bstep (se 1 (by rfl) ⟨480653, by rfl⟩ : syracuseStep 640871 = 961307) B961307
theorem B1296253 : Blo 424774 1296253 := bstep (se 3 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 1296253 = 486095) B486095
theorem B641471 : Blo 424774 641471 := bstep (se 1 (by rfl) ⟨481103, by rfl⟩ : syracuseStep 641471 = 962207) B962207
theorem B10930625 : Blo 424774 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B3230441 : Blo 424774 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B641855 : Blo 424774 641855 := bstep (se 1 (by rfl) ⟨481391, by rfl⟩ : syracuseStep 641855 = 962783) B962783
theorem B1821635 : Blo 424774 1821635 := bstep (se 1 (by rfl) ⟨1366226, by rfl⟩ : syracuseStep 1821635 = 2732453) B2732453
theorem B2805101 : Blo 424774 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B642527 : Blo 424774 642527 := bstep (se 1 (by rfl) ⟨481895, by rfl⟩ : syracuseStep 642527 = 963791) B963791
theorem B1756669 : Blo 424774 1756669 := bstep (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) B658751
theorem B1036001 : Blo 424774 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B643007 : Blo 424774 643007 := bstep (se 1 (by rfl) ⟨482255, by rfl⟩ : syracuseStep 643007 = 964511) B964511
theorem B807079 : Blo 424774 807079 := bstep (se 1 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 807079 = 1210619) B1210619
theorem B3559751 : Blo 424774 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B807337 : Blo 424774 807337 := bstep (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) B605503
theorem B1626551 : Blo 424774 1626551 := bstep (se 1 (by rfl) ⟨1219913, by rfl⟩ : syracuseStep 1626551 = 2439827) B2439827
theorem B3330497 : Blo 424774 3330497 := bstep (se 2 (by rfl) ⟨1248936, by rfl⟩ : syracuseStep 3330497 = 2497873) B2497873
theorem B1626749 : Blo 424774 1626749 := bstep (se 3 (by rfl) ⟨305015, by rfl⟩ : syracuseStep 1626749 = 610031) B610031
theorem B5559833 : Blo 424774 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B2152169 : Blo 424774 2152169 := bstep (se 2 (by rfl) ⟨807063, by rfl⟩ : syracuseStep 2152169 = 1614127) B1614127
theorem B11262025 : Blo 424774 11262025 := bstep (se 2 (by rfl) ⟨4223259, by rfl⟩ : syracuseStep 11262025 = 8446519) B8446519
theorem B809183 : Blo 424774 809183 := bstep (se 1 (by rfl) ⟨606887, by rfl⟩ : syracuseStep 809183 = 1213775) B1213775
theorem B1531817 : Blo 424774 1531817 := bstep (se 2 (by rfl) ⟨574431, by rfl⟩ : syracuseStep 1531817 = 1148863) B1148863
theorem B5857231 : Blo 424774 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B1532495 : Blo 424774 1532495 := bstep (se 1 (by rfl) ⟨1149371, by rfl⟩ : syracuseStep 1532495 = 2298743) B2298743
theorem B22209395 : Blo 424774 22209395 := bstep (se 1 (by rfl) ⟨16657046, by rfl⟩ : syracuseStep 22209395 = 33314093) B33314093
theorem B681319 : Blo 424774 681319 := bstep (se 1 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 681319 = 1021979) B1021979
theorem B1435049 : Blo 424774 1435049 := bstep (se 2 (by rfl) ⟨538143, by rfl⟩ : syracuseStep 1435049 = 1076287) B1076287
theorem B2057683 : Blo 424774 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B1435103 : Blo 424774 1435103 := bstep (se 1 (by rfl) ⟨1076327, by rfl⟩ : syracuseStep 1435103 = 2152655) B2152655
theorem B1435319 : Blo 424774 1435319 := bstep (se 1 (by rfl) ⟨1076489, by rfl⟩ : syracuseStep 1435319 = 2152979) B2152979
theorem B107865893 : Blo 424774 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B3237937 : Blo 424774 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B1436777 : Blo 424774 1436777 := bstep (se 2 (by rfl) ⟨538791, by rfl⟩ : syracuseStep 1436777 = 1077583) B1077583
theorem B1437263 : Blo 424774 1437263 := bstep (se 1 (by rfl) ⟨1077947, by rfl⟩ : syracuseStep 1437263 = 2155895) B2155895
theorem B6156269 : Blo 424774 6156269 := bstep (se 3 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 6156269 = 2308601) B2308601
theorem B716863 : Blo 424774 716863 := bstep (se 1 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 716863 = 1075295) B1075295
theorem B1831187 : Blo 424774 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B1438235 : Blo 424774 1438235 := bstep (se 1 (by rfl) ⟨1078676, by rfl⟩ : syracuseStep 1438235 = 2157353) B2157353
theorem B718159 : Blo 424774 718159 := bstep (se 1 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 718159 = 1077239) B1077239
theorem B13563227 : Blo 424774 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B1439369 : Blo 424774 1439369 := bstep (se 2 (by rfl) ⟨539763, by rfl⟩ : syracuseStep 1439369 = 1079527) B1079527
theorem B718591 : Blo 424774 718591 := bstep (se 1 (by rfl) ⟨538943, by rfl⟩ : syracuseStep 718591 = 1077887) B1077887
theorem B5175323 : Blo 424774 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B1440071 : Blo 424774 1440071 := bstep (se 1 (by rfl) ⟨1080053, by rfl⟩ : syracuseStep 1440071 = 2160107) B2160107
theorem B686407 : Blo 424774 686407 := bstep (se 1 (by rfl) ⟨514805, by rfl⟩ : syracuseStep 686407 = 1029611) B1029611
theorem B8223119 : Blo 424774 8223119 := bstep (se 1 (by rfl) ⟨6167339, by rfl⟩ : syracuseStep 8223119 = 12334679) B12334679
theorem B5863843 : Blo 424774 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B16415621 : Blo 424774 16415621 := bstep (se 4 (by rfl) ⟨1538964, by rfl⟩ : syracuseStep 16415621 = 3077929) B3077929
theorem B425087 : Blo 424774 425087 := bstep (se 1 (by rfl) ⟨318815, by rfl⟩ : syracuseStep 425087 = 637631) B637631
theorem B1440935 : Blo 424774 1440935 := bstep (se 1 (by rfl) ⟨1080701, by rfl⟩ : syracuseStep 1440935 = 2161403) B2161403
theorem B4849307 : Blo 424774 4849307 := bstep (se 1 (by rfl) ⟨3636980, by rfl⟩ : syracuseStep 4849307 = 7273961) B7273961
theorem B425723 : Blo 424774 425723 := bstep (se 1 (by rfl) ⟨319292, by rfl⟩ : syracuseStep 425723 = 638585) B638585
theorem B2162537 : Blo 424774 2162537 := bstep (se 2 (by rfl) ⟨810951, by rfl⟩ : syracuseStep 2162537 = 1621903) B1621903
theorem B426011 : Blo 424774 426011 := bstep (se 1 (by rfl) ⟨319508, by rfl⟩ : syracuseStep 426011 = 639017) B639017
theorem B426031 : Blo 424774 426031 := bstep (se 1 (by rfl) ⟨319523, by rfl⟩ : syracuseStep 426031 = 639047) B639047
theorem B1442015 : Blo 424774 1442015 := bstep (se 1 (by rfl) ⟨1081511, by rfl⟩ : syracuseStep 1442015 = 2163023) B2163023
theorem B17268997 : Blo 424774 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B426587 : Blo 424774 426587 := bstep (se 1 (by rfl) ⟨319940, by rfl⟩ : syracuseStep 426587 = 639881) B639881
theorem B1213147 : Blo 424774 1213147 := bstep (se 1 (by rfl) ⟨909860, by rfl⟩ : syracuseStep 1213147 = 1819721) B1819721
theorem B426735 : Blo 424774 426735 := bstep (se 1 (by rfl) ⟨320051, by rfl⟩ : syracuseStep 426735 = 640103) B640103
theorem B2163671 : Blo 424774 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B426991 : Blo 424774 426991 := bstep (se 1 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 426991 = 640487) B640487
theorem B427039 : Blo 424774 427039 := bstep (se 1 (by rfl) ⟨320279, by rfl⟩ : syracuseStep 427039 = 640559) B640559
theorem B8881325 : Blo 424774 8881325 := bstep (se 3 (by rfl) ⟨1665248, by rfl⟩ : syracuseStep 8881325 = 3330497) B3330497
theorem B427247 : Blo 424774 427247 := bstep (se 1 (by rfl) ⟨320435, by rfl⟩ : syracuseStep 427247 = 640871) B640871
theorem B427647 : Blo 424774 427647 := bstep (se 1 (by rfl) ⟨320735, by rfl⟩ : syracuseStep 427647 = 641471) B641471
theorem B427903 : Blo 424774 427903 := bstep (se 1 (by rfl) ⟨320927, by rfl⟩ : syracuseStep 427903 = 641855) B641855
theorem B1214423 : Blo 424774 1214423 := bstep (se 1 (by rfl) ⟨910817, by rfl⟩ : syracuseStep 1214423 = 1821635) B1821635
theorem B1870067 : Blo 424774 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B428351 : Blo 424774 428351 := bstep (se 1 (by rfl) ⟨321263, by rfl⟩ : syracuseStep 428351 = 642527) B642527
theorem B124357193 : Blo 424774 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B428671 : Blo 424774 428671 := bstep (se 1 (by rfl) ⟨321503, by rfl⟩ : syracuseStep 428671 = 643007) B643007
theorem B1084367 : Blo 424774 1084367 := bstep (se 1 (by rfl) ⟨813275, by rfl⟩ : syracuseStep 1084367 = 1626551) B1626551
theorem B1084499 : Blo 424774 1084499 := bstep (se 1 (by rfl) ⟨813374, by rfl⟩ : syracuseStep 1084499 = 1626749) B1626749
theorem B2428163 : Blo 424774 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B3706555 : Blo 424774 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B2428663 : Blo 424774 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B1380607 : Blo 424774 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B1021211 : Blo 424774 1021211 := bstep (se 1 (by rfl) ⟨765908, by rfl⟩ : syracuseStep 1021211 = 1531817) B1531817
theorem B1840463 : Blo 424774 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B955817 : Blo 424774 955817 := bstep (se 2 (by rfl) ⟨358431, by rfl⟩ : syracuseStep 955817 = 716863) B716863
theorem B1021663 : Blo 424774 1021663 := bstep (se 1 (by rfl) ⟨766247, by rfl⟩ : syracuseStep 1021663 = 1532495) B1532495
theorem B3086063 : Blo 424774 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B956699 : Blo 424774 956699 := bstep (se 1 (by rfl) ⟨717524, by rfl⟩ : syracuseStep 956699 = 1435049) B1435049
theorem B956735 : Blo 424774 956735 := bstep (se 1 (by rfl) ⟨717551, by rfl⟩ : syracuseStep 956735 = 1435103) B1435103
theorem B956879 : Blo 424774 956879 := bstep (se 1 (by rfl) ⟨717659, by rfl⟩ : syracuseStep 956879 = 1435319) B1435319
theorem B957545 : Blo 424774 957545 := bstep (se 2 (by rfl) ⟨359079, by rfl⟩ : syracuseStep 957545 = 718159) B718159
theorem B3087679 : Blo 424774 3087679 := bstep (se 1 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 3087679 = 4631519) B4631519
theorem B957851 : Blo 424774 957851 := bstep (se 1 (by rfl) ⟨718388, by rfl⟩ : syracuseStep 957851 = 1436777) B1436777
theorem B958121 : Blo 424774 958121 := bstep (se 2 (by rfl) ⟨359295, by rfl⟩ : syracuseStep 958121 = 718591) B718591
theorem B958175 : Blo 424774 958175 := bstep (se 1 (by rfl) ⟨718631, by rfl⟩ : syracuseStep 958175 = 1437263) B1437263
theorem B4104179 : Blo 424774 4104179 := bstep (se 1 (by rfl) ⟨3078134, by rfl⟩ : syracuseStep 4104179 = 6156269) B6156269
theorem B15016033 : Blo 424774 15016033 := bstep (se 2 (by rfl) ⟨5631012, by rfl⟩ : syracuseStep 15016033 = 11262025) B11262025
theorem B1220791 : Blo 424774 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B958823 : Blo 424774 958823 := bstep (se 1 (by rfl) ⟨719117, by rfl⟩ : syracuseStep 958823 = 1438235) B1438235
theorem B8856515 : Blo 424774 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B959579 : Blo 424774 959579 := bstep (se 1 (by rfl) ⟨719684, by rfl⟩ : syracuseStep 959579 = 1439369) B1439369
theorem B3450215 : Blo 424774 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B960047 : Blo 424774 960047 := bstep (se 1 (by rfl) ⟨720035, by rfl⟩ : syracuseStep 960047 = 1440071) B1440071
theorem B5482079 : Blo 424774 5482079 := bstep (se 1 (by rfl) ⟨4111559, by rfl⟩ : syracuseStep 5482079 = 8223119) B8223119
theorem B2762669 : Blo 424774 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B960623 : Blo 424774 960623 := bstep (se 1 (by rfl) ⟨720467, by rfl⟩ : syracuseStep 960623 = 1440935) B1440935
theorem B7809641 : Blo 424774 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B961883 : Blo 424774 961883 := bstep (se 1 (by rfl) ⟨721412, by rfl⟩ : syracuseStep 961883 = 1442825) B1442825
theorem B863723 : Blo 424774 863723 := bstep (se 1 (by rfl) ⟨647792, by rfl⟩ : syracuseStep 863723 = 1295585) B1295585
theorem B962279 : Blo 424774 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B765787 : Blo 424774 765787 := bstep (se 1 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 765787 = 1148681) B1148681
theorem B1814663 : Blo 424774 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B7287083 : Blo 424774 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B767003 : Blo 424774 767003 := bstep (se 1 (by rfl) ⟨575252, by rfl⟩ : syracuseStep 767003 = 1150505) B1150505
theorem B964079 : Blo 424774 964079 := bstep (se 1 (by rfl) ⟨723059, by rfl⟩ : syracuseStep 964079 = 1446119) B1446119
theorem B2373167 : Blo 424774 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B539455 : Blo 424774 539455 := bstep (se 1 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 539455 = 809183) B809183
theorem B2342225 : Blo 424774 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B639815 : Blo 424774 639815 := bstep (se 1 (by rfl) ⟨479861, by rfl⟩ : syracuseStep 639815 = 959723) B959723
theorem B71910595 : Blo 424774 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B11060549 : Blo 424774 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B640367 : Blo 424774 640367 := bstep (se 1 (by rfl) ⟨480275, by rfl⟩ : syracuseStep 640367 = 960551) B960551
theorem B23905843 : Blo 424774 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B641243 : Blo 424774 641243 := bstep (se 1 (by rfl) ⟨480932, by rfl⟩ : syracuseStep 641243 = 961865) B961865
theorem B641435 : Blo 424774 641435 := bstep (se 1 (by rfl) ⟨481076, by rfl⟩ : syracuseStep 641435 = 962153) B962153
theorem B641591 : Blo 424774 641591 := bstep (se 1 (by rfl) ⟨481193, by rfl⟩ : syracuseStep 641591 = 962387) B962387
theorem B641663 : Blo 424774 641663 := bstep (se 1 (by rfl) ⟨481247, by rfl⟩ : syracuseStep 641663 = 962495) B962495
theorem B7818457 : Blo 424774 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B642407 : Blo 424774 642407 := bstep (se 1 (by rfl) ⟨481805, by rfl⟩ : syracuseStep 642407 = 963611) B963611
theorem B18534005 : Blo 424774 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B511643 : Blo 424774 511643 := bstep (se 1 (by rfl) ⟨383732, by rfl⟩ : syracuseStep 511643 = 767465) B767465
theorem B1822439 : Blo 424774 1822439 := bstep (se 1 (by rfl) ⟨1366829, by rfl⟩ : syracuseStep 1822439 = 2733659) B2733659
theorem B236900213 : Blo 424774 236900213 := bstep (se 5 (by rfl) ⟨11104697, by rfl⟩ : syracuseStep 236900213 = 22209395) B22209395
theorem B3658031 : Blo 424774 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B3232871 : Blo 424774 3232871 := bstep (se 1 (by rfl) ⟨2424653, by rfl⟩ : syracuseStep 3232871 = 4849307) B4849307
theorem B480703 : Blo 424774 480703 := bstep (se 1 (by rfl) ⟨360527, by rfl⟩ : syracuseStep 480703 = 721055) B721055
theorem B1725953 : Blo 424774 1725953 := bstep (se 2 (by rfl) ⟨647232, by rfl⟩ : syracuseStep 1725953 = 1294465) B1294465
theorem B1758775 : Blo 424774 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B9885635 : Blo 424774 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B1398811 : Blo 424774 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B908425 : Blo 424774 908425 := bstep (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) B681319
theorem B2153627 : Blo 424774 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B2743577 : Blo 424774 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B811711 : Blo 424774 811711 := bstep (se 1 (by rfl) ⟨608783, by rfl⟩ : syracuseStep 811711 = 1217567) B1217567
theorem B1434779 : Blo 424774 1434779 := bstep (se 1 (by rfl) ⟨1076084, by rfl⟩ : syracuseStep 1434779 = 2152169) B2152169
theorem B1076105 : Blo 424774 1076105 := bstep (se 2 (by rfl) ⟨403539, by rfl⟩ : syracuseStep 1076105 = 807079) B807079
theorem B4385825 : Blo 424774 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B1076449 : Blo 424774 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B1076591 : Blo 424774 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B3239675 : Blo 424774 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B1078231 : Blo 424774 1078231 := bstep (se 1 (by rfl) ⟨808673, by rfl⟩ : syracuseStep 1078231 = 1617347) B1617347
theorem B1537697 : Blo 424774 1537697 := bstep (se 2 (by rfl) ⟨576636, by rfl⟩ : syracuseStep 1537697 = 1153273) B1153273
theorem B915209 : Blo 424774 915209 := bstep (se 2 (by rfl) ⟨343203, by rfl⟩ : syracuseStep 915209 = 686407) B686407
theorem B9042151 : Blo 424774 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B1080287 : Blo 424774 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B10943747 : Blo 424774 10943747 := bstep (se 1 (by rfl) ⟨8207810, by rfl⟩ : syracuseStep 10943747 = 16415621) B16415621
theorem B425243 : Blo 424774 425243 := bstep (se 1 (by rfl) ⟨318932, by rfl⟩ : syracuseStep 425243 = 637865) B637865
theorem B6913349 : Blo 424774 6913349 := bstep (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) B1296253
theorem B425599 : Blo 424774 425599 := bstep (se 1 (by rfl) ⟨319199, by rfl⟩ : syracuseStep 425599 = 638399) B638399
theorem B4095683 : Blo 424774 4095683 := bstep (se 1 (by rfl) ⟨3071762, by rfl⟩ : syracuseStep 4095683 = 6143525) B6143525
theorem B1441691 : Blo 424774 1441691 := bstep (se 1 (by rfl) ⟨1081268, by rfl⟩ : syracuseStep 1441691 = 2162537) B2162537
theorem B20021377 : Blo 424774 20021377 := bstep (se 2 (by rfl) ⟨7508016, by rfl⟩ : syracuseStep 20021377 = 15016033) B15016033
theorem B426543 : Blo 424774 426543 := bstep (se 1 (by rfl) ⟨319907, by rfl⟩ : syracuseStep 426543 = 639815) B639815
theorem B1442447 : Blo 424774 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B7373699 : Blo 424774 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B426911 : Blo 424774 426911 := bstep (se 1 (by rfl) ⟨320183, by rfl⟩ : syracuseStep 426911 = 640367) B640367
theorem B1082281 : Blo 424774 1082281 := bstep (se 2 (by rfl) ⟨405855, by rfl⟩ : syracuseStep 1082281 = 811711) B811711
theorem B427495 : Blo 424774 427495 := bstep (se 1 (by rfl) ⟨320621, by rfl⟩ : syracuseStep 427495 = 641243) B641243
theorem B427623 : Blo 424774 427623 := bstep (se 1 (by rfl) ⟨320717, by rfl⟩ : syracuseStep 427623 = 641435) B641435
theorem B427727 : Blo 424774 427727 := bstep (se 1 (by rfl) ⟨320795, by rfl⟩ : syracuseStep 427727 = 641591) B641591
theorem B82904795 : Blo 424774 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B427775 : Blo 424774 427775 := bstep (se 1 (by rfl) ⟨320831, by rfl⟩ : syracuseStep 427775 = 641663) B641663
theorem B722911 : Blo 424774 722911 := bstep (se 1 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 722911 = 1084367) B1084367
theorem B722999 : Blo 424774 722999 := bstep (se 1 (by rfl) ⟨542249, by rfl⟩ : syracuseStep 722999 = 1084499) B1084499
theorem B428271 : Blo 424774 428271 := bstep (se 1 (by rfl) ⟨321203, by rfl⟩ : syracuseStep 428271 = 642407) B642407
theorem B12356003 : Blo 424774 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B1214959 : Blo 424774 1214959 := bstep (se 1 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 1214959 = 1822439) B1822439
theorem B19631605 : Blo 424774 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B6590423 : Blo 424774 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B10424609 : Blo 424774 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B1021049 : Blo 424774 1021049 := bstep (se 2 (by rfl) ⟨382893, by rfl⟩ : syracuseStep 1021049 = 765787) B765787
theorem B5904343 : Blo 424774 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B4986845 : Blo 424774 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B956519 : Blo 424774 956519 := bstep (se 1 (by rfl) ⟨717389, by rfl⟩ : syracuseStep 956519 = 1434779) B1434779
theorem B383523173 : Blo 424774 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B1841779 : Blo 424774 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B2923883 : Blo 424774 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B4858055 : Blo 424774 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B1582111 : Blo 424774 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1025131 : Blo 424774 1025131 := bstep (se 1 (by rfl) ⟨768848, by rfl⟩ : syracuseStep 1025131 = 1537697) B1537697
theorem B2303261 : Blo 424774 2303261 := bstep (se 3 (by rfl) ⟨431861, by rfl⟩ : syracuseStep 2303261 = 863723) B863723
theorem B2730455 : Blo 424774 2730455 := bstep (se 1 (by rfl) ⟨2047841, by rfl⟩ : syracuseStep 2730455 = 4095683) B4095683
theorem B961127 : Blo 424774 961127 := bstep (se 1 (by rfl) ⟨720845, by rfl⟩ : syracuseStep 961127 = 1441691) B1441691
theorem B961343 : Blo 424774 961343 := bstep (se 1 (by rfl) ⟨721007, by rfl⟩ : syracuseStep 961343 = 1442015) B1442015
theorem B1617529 : Blo 424774 1617529 := bstep (se 2 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 1617529 = 1213147) B1213147
theorem B1618775 : Blo 424774 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B2045341 : Blo 424774 2045341 := bstep (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) B767003
theorem B2438687 : Blo 424774 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B637211 : Blo 424774 637211 := bstep (se 1 (by rfl) ⟨477908, by rfl⟩ : syracuseStep 637211 = 955817) B955817
theorem B4602541 : Blo 424774 4602541 := bstep (se 3 (by rfl) ⟨862976, by rfl⟩ : syracuseStep 4602541 = 1725953) B1725953
theorem B637799 : Blo 424774 637799 := bstep (se 1 (by rfl) ⟨478349, by rfl⟩ : syracuseStep 637799 = 956699) B956699
theorem B637823 : Blo 424774 637823 := bstep (se 1 (by rfl) ⟨478367, by rfl⟩ : syracuseStep 637823 = 956735) B956735
theorem B637919 : Blo 424774 637919 := bstep (se 1 (by rfl) ⟨478439, by rfl⟩ : syracuseStep 637919 = 956879) B956879
theorem B638363 : Blo 424774 638363 := bstep (se 1 (by rfl) ⟨478772, by rfl⟩ : syracuseStep 638363 = 957545) B957545
theorem B638567 : Blo 424774 638567 := bstep (se 1 (by rfl) ⟨478925, by rfl⟩ : syracuseStep 638567 = 957851) B957851
theorem B638747 : Blo 424774 638747 := bstep (se 1 (by rfl) ⟨479060, by rfl⟩ : syracuseStep 638747 = 958121) B958121
theorem B638783 : Blo 424774 638783 := bstep (se 1 (by rfl) ⟨479087, by rfl⟩ : syracuseStep 638783 = 958175) B958175
theorem B2736119 : Blo 424774 2736119 := bstep (se 1 (by rfl) ⟨2052089, by rfl⟩ : syracuseStep 2736119 = 4104179) B4104179
theorem B639215 : Blo 424774 639215 := bstep (se 1 (by rfl) ⟨479411, by rfl⟩ : syracuseStep 639215 = 958823) B958823
theorem B639719 : Blo 424774 639719 := bstep (se 1 (by rfl) ⟨479789, by rfl⟩ : syracuseStep 639719 = 959579) B959579
theorem B640031 : Blo 424774 640031 := bstep (se 1 (by rfl) ⟨480023, by rfl⟩ : syracuseStep 640031 = 960047) B960047
theorem B3654719 : Blo 424774 3654719 := bstep (se 1 (by rfl) ⟨2741039, by rfl⟩ : syracuseStep 3654719 = 5482079) B5482079
theorem B640415 : Blo 424774 640415 := bstep (se 1 (by rfl) ⟨480311, by rfl⟩ : syracuseStep 640415 = 960623) B960623
theorem B640937 : Blo 424774 640937 := bstep (se 2 (by rfl) ⟨240351, by rfl⟩ : syracuseStep 640937 = 480703) B480703
theorem B2345033 : Blo 424774 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B641255 : Blo 424774 641255 := bstep (se 1 (by rfl) ⟨480941, by rfl⟩ : syracuseStep 641255 = 961883) B961883
theorem B1362217 : Blo 424774 1362217 := bstep (se 2 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 1362217 = 1021663) B1021663
theorem B641519 : Blo 424774 641519 := bstep (se 1 (by rfl) ⟨481139, by rfl⟩ : syracuseStep 641519 = 962279) B962279
theorem B642719 : Blo 424774 642719 := bstep (se 1 (by rfl) ⟨482039, by rfl⟩ : syracuseStep 642719 = 964079) B964079
theorem B610139 : Blo 424774 610139 := bstep (se 1 (by rfl) ⟨457604, by rfl⟩ : syracuseStep 610139 = 915209) B915209
theorem B1364381 : Blo 424774 1364381 := bstep (se 3 (by rfl) ⟨255821, by rfl⟩ : syracuseStep 1364381 = 511643) B511643
theorem B4116905 : Blo 424774 4116905 := bstep (se 2 (by rfl) ⟨1543839, by rfl⟩ : syracuseStep 4116905 = 3087679) B3087679
theorem B7295831 : Blo 424774 7295831 := bstep (se 1 (by rfl) ⟨5471873, by rfl⟩ : syracuseStep 7295831 = 10943747) B10943747
theorem B4608899 : Blo 424774 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1561483 : Blo 424774 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B1627721 : Blo 424774 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B23025329 : Blo 424774 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B4839101 : Blo 424774 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B5920883 : Blo 424774 5920883 := bstep (se 1 (by rfl) ⟨4440662, by rfl⟩ : syracuseStep 5920883 = 8881325) B8881325
theorem B809615 : Blo 424774 809615 := bstep (se 1 (by rfl) ⟨607211, by rfl⟩ : syracuseStep 809615 = 1214423) B1214423
theorem B7363237 : Blo 424774 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B157933475 : Blo 424774 157933475 := bstep (se 1 (by rfl) ⟨118450106, by rfl⟩ : syracuseStep 157933475 = 236900213) B236900213
theorem B2155247 : Blo 424774 2155247 := bstep (se 1 (by rfl) ⟨1616435, by rfl⟩ : syracuseStep 2155247 = 3232871) B3232871
theorem B680807 : Blo 424774 680807 := bstep (se 1 (by rfl) ⟨510605, by rfl⟩ : syracuseStep 680807 = 1021211) B1021211
theorem B9200573 : Blo 424774 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B2057375 : Blo 424774 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1435265 : Blo 424774 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B1435751 : Blo 424774 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1829051 : Blo 424774 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B4942073 : Blo 424774 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B3238217 : Blo 424774 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B4844933 : Blo 424774 4844933 := bstep (se 4 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 4844933 = 908425) B908425
theorem B1437641 : Blo 424774 1437641 := bstep (se 2 (by rfl) ⟨539115, by rfl⟩ : syracuseStep 1437641 = 1078231) B1078231
theorem B5206427 : Blo 424774 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B717403 : Blo 424774 717403 := bstep (se 1 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 717403 = 1076105) B1076105
theorem B717727 : Blo 424774 717727 := bstep (se 1 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 717727 = 1076591) B1076591
theorem B2159783 : Blo 424774 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B1865081 : Blo 424774 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B127497829 : Blo 424774 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B12056201 : Blo 424774 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B719273 : Blo 424774 719273 := bstep (se 2 (by rfl) ⟨269727, by rfl⟩ : syracuseStep 719273 = 539455) B539455
theorem B720191 : Blo 424774 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B426143 : Blo 424774 426143 := bstep (se 1 (by rfl) ⟨319607, by rfl⟩ : syracuseStep 426143 = 639215) B639215
theorem B426479 : Blo 424774 426479 := bstep (se 1 (by rfl) ⟨319859, by rfl⟩ : syracuseStep 426479 = 639719) B639719
theorem B4915799 : Blo 424774 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B426687 : Blo 424774 426687 := bstep (se 1 (by rfl) ⟨320015, by rfl⟩ : syracuseStep 426687 = 640031) B640031
theorem B426943 : Blo 424774 426943 := bstep (se 1 (by rfl) ⟨320207, by rfl⟩ : syracuseStep 426943 = 640415) B640415
theorem B1443041 : Blo 424774 1443041 := bstep (se 2 (by rfl) ⟨541140, by rfl⟩ : syracuseStep 1443041 = 1082281) B1082281
theorem B427291 : Blo 424774 427291 := bstep (se 1 (by rfl) ⟨320468, by rfl⟩ : syracuseStep 427291 = 640937) B640937
theorem B427503 : Blo 424774 427503 := bstep (se 1 (by rfl) ⟨320627, by rfl⟩ : syracuseStep 427503 = 641255) B641255
theorem B427679 : Blo 424774 427679 := bstep (se 1 (by rfl) ⟨320759, by rfl⟩ : syracuseStep 427679 = 641519) B641519
theorem B428479 : Blo 424774 428479 := bstep (se 1 (by rfl) ⟨321359, by rfl⟩ : syracuseStep 428479 = 642719) B642719
theorem B4393615 : Blo 424774 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B6949739 : Blo 424774 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B1085147 : Blo 424774 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B8327909 : Blo 424774 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B105288983 : Blo 424774 105288983 := bstep (se 1 (by rfl) ⟨78966737, by rfl⟩ : syracuseStep 105288983 = 157933475) B157933475
theorem B6133715 : Blo 424774 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B13178861 : Blo 424774 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B956537 : Blo 424774 956537 := bstep (se 2 (by rfl) ⟨358701, by rfl⟩ : syracuseStep 956537 = 717403) B717403
theorem B956843 : Blo 424774 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B956969 : Blo 424774 956969 := bstep (se 2 (by rfl) ⟨358863, by rfl⟩ : syracuseStep 956969 = 717727) B717727
theorem B957167 : Blo 424774 957167 := bstep (se 1 (by rfl) ⟨717875, by rfl⟩ : syracuseStep 957167 = 1435751) B1435751
theorem B1219367 : Blo 424774 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B2727121 : Blo 424774 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B958427 : Blo 424774 958427 := bstep (se 1 (by rfl) ⟨718820, by rfl⟩ : syracuseStep 958427 = 1437641) B1437641
theorem B6136721 : Blo 424774 6136721 := bstep (se 2 (by rfl) ⟨2301270, by rfl⟩ : syracuseStep 6136721 = 4602541) B4602541
theorem B8037467 : Blo 424774 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B961631 : Blo 424774 961631 := bstep (se 1 (by rfl) ⟨721223, by rfl⟩ : syracuseStep 961631 = 1442447) B1442447
theorem B2436479 : Blo 424774 2436479 := bstep (se 1 (by rfl) ⟨1827359, by rfl⟩ : syracuseStep 2436479 = 3654719) B3654719
theorem B8237335 : Blo 424774 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B963881 : Blo 424774 963881 := bstep (se 2 (by rfl) ⟨361455, by rfl⟩ : syracuseStep 963881 = 722911) B722911
theorem B1816289 : Blo 424774 1816289 := bstep (se 2 (by rfl) ⟨681108, by rfl⟩ : syracuseStep 1816289 = 1362217) B1362217
theorem B4863887 : Blo 424774 4863887 := bstep (se 1 (by rfl) ⟨3647915, by rfl⟩ : syracuseStep 4863887 = 7295831) B7295831
theorem B1619945 : Blo 424774 1619945 := bstep (se 2 (by rfl) ⟨607479, by rfl⟩ : syracuseStep 1619945 = 1214959) B1214959
theorem B15350219 : Blo 424774 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B3226067 : Blo 424774 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B3324563 : Blo 424774 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B637679 : Blo 424774 637679 := bstep (se 1 (by rfl) ⟨478259, by rfl⟩ : syracuseStep 637679 = 956519) B956519
theorem B3947255 : Blo 424774 3947255 := bstep (se 1 (by rfl) ⟨2960441, by rfl⟩ : syracuseStep 3947255 = 5920883) B5920883
theorem B1949255 : Blo 424774 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B8437925 : Blo 424774 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1820303 : Blo 424774 1820303 := bstep (se 1 (by rfl) ⟨1365227, by rfl⟩ : syracuseStep 1820303 = 2730455) B2730455
theorem B640751 : Blo 424774 640751 := bstep (se 1 (by rfl) ⟨480563, by rfl⟩ : syracuseStep 640751 = 961127) B961127
theorem B640895 : Blo 424774 640895 := bstep (se 1 (by rfl) ⟨480671, by rfl⟩ : syracuseStep 640895 = 961343) B961343
theorem B3229955 : Blo 424774 3229955 := bstep (se 1 (by rfl) ⟨2422466, by rfl⟩ : syracuseStep 3229955 = 4844933) B4844933
theorem B9817649 : Blo 424774 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B1625791 : Blo 424774 1625791 := bstep (se 1 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 1625791 = 2438687) B2438687
theorem B479515 : Blo 424774 479515 := bstep (se 1 (by rfl) ⟨359636, by rfl⟩ : syracuseStep 479515 = 719273) B719273
theorem B480127 : Blo 424774 480127 := bstep (se 1 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 480127 = 720191) B720191
theorem B1627037 : Blo 424774 1627037 := bstep (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) B610139
theorem B1824079 : Blo 424774 1824079 := bstep (se 1 (by rfl) ⟨1368059, by rfl⟩ : syracuseStep 1824079 = 2736119) B2736119
theorem B26695169 : Blo 424774 26695169 := bstep (se 2 (by rfl) ⟨10010688, by rfl⟩ : syracuseStep 26695169 = 20021377) B20021377
theorem B55269863 : Blo 424774 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B481999 : Blo 424774 481999 := bstep (se 1 (by rfl) ⟨361499, by rfl⟩ : syracuseStep 481999 = 722999) B722999
theorem B1563355 : Blo 424774 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B1366841 : Blo 424774 1366841 := bstep (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) B1025131
theorem B909587 : Blo 424774 909587 := bstep (se 1 (by rfl) ⟨682190, by rfl⟩ : syracuseStep 909587 = 1364381) B1364381
theorem B2744603 : Blo 424774 2744603 := bstep (se 1 (by rfl) ⟨2058452, by rfl⟩ : syracuseStep 2744603 = 4116905) B4116905
theorem B3072599 : Blo 424774 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B680699 : Blo 424774 680699 := bstep (se 1 (by rfl) ⟨510524, by rfl⟩ : syracuseStep 680699 = 1021049) B1021049
theorem B255682115 : Blo 424774 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B26175473 : Blo 424774 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B2156705 : Blo 424774 2156705 := bstep (se 2 (by rfl) ⟨808764, by rfl⟩ : syracuseStep 2156705 = 1617529) B1617529
theorem B3238703 : Blo 424774 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B1436831 : Blo 424774 1436831 := bstep (se 1 (by rfl) ⟨1077623, by rfl⟩ : syracuseStep 1436831 = 2155247) B2155247
theorem B453871 : Blo 424774 453871 := bstep (se 1 (by rfl) ⟨340403, by rfl⟩ : syracuseStep 453871 = 680807) B680807
theorem B1371583 : Blo 424774 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B1535507 : Blo 424774 1535507 := bstep (se 1 (by rfl) ⟨1151630, by rfl⟩ : syracuseStep 1535507 = 2303261) B2303261
theorem B2158811 : Blo 424774 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B2158973 : Blo 424774 2158973 := bstep (se 3 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 2158973 = 809615) B809615
theorem B169997105 : Blo 424774 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B3470951 : Blo 424774 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B1079183 : Blo 424774 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B1439855 : Blo 424774 1439855 := bstep (se 1 (by rfl) ⟨1079891, by rfl⟩ : syracuseStep 1439855 = 2159783) B2159783
theorem B2455705 : Blo 424774 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1243387 : Blo 424774 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B424807 : Blo 424774 424807 := bstep (se 1 (by rfl) ⟨318605, by rfl⟩ : syracuseStep 424807 = 637211) B637211
theorem B425199 : Blo 424774 425199 := bstep (se 1 (by rfl) ⟨318899, by rfl⟩ : syracuseStep 425199 = 637799) B637799
theorem B425215 : Blo 424774 425215 := bstep (se 1 (by rfl) ⟨318911, by rfl⟩ : syracuseStep 425215 = 637823) B637823
theorem B425279 : Blo 424774 425279 := bstep (se 1 (by rfl) ⟨318959, by rfl⟩ : syracuseStep 425279 = 637919) B637919
theorem B425575 : Blo 424774 425575 := bstep (se 1 (by rfl) ⟨319181, by rfl⟩ : syracuseStep 425575 = 638363) B638363
theorem B425711 : Blo 424774 425711 := bstep (se 1 (by rfl) ⟨319283, by rfl⟩ : syracuseStep 425711 = 638567) B638567
theorem B31489829 : Blo 424774 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B425831 : Blo 424774 425831 := bstep (se 1 (by rfl) ⟨319373, by rfl⟩ : syracuseStep 425831 = 638747) B638747
theorem B425855 : Blo 424774 425855 := bstep (se 1 (by rfl) ⟨319391, by rfl⟩ : syracuseStep 425855 = 638783) B638783
theorem B3277199 : Blo 424774 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B2425565 : Blo 424774 2425565 := bstep (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) B909587
theorem B1213535 : Blo 424774 1213535 := bstep (se 1 (by rfl) ⟨910151, by rfl⟩ : syracuseStep 1213535 = 1820303) B1820303
theorem B427167 : Blo 424774 427167 := bstep (se 1 (by rfl) ⟨320375, by rfl⟩ : syracuseStep 427167 = 640751) B640751
theorem B427263 : Blo 424774 427263 := bstep (se 1 (by rfl) ⟨320447, by rfl⟩ : syracuseStep 427263 = 640895) B640895
theorem B723431 : Blo 424774 723431 := bstep (se 1 (by rfl) ⟨542573, by rfl⟩ : syracuseStep 723431 = 1085147) B1085147
theorem B1084691 : Blo 424774 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B70192655 : Blo 424774 70192655 := bstep (se 1 (by rfl) ⟨52644491, by rfl⟩ : syracuseStep 70192655 = 105288983) B105288983
theorem B17796779 : Blo 424774 17796779 := bstep (se 1 (by rfl) ⟨13347584, by rfl⟩ : syracuseStep 17796779 = 26695169) B26695169
theorem B8785907 : Blo 424774 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B2167721 : Blo 424774 2167721 := bstep (se 2 (by rfl) ⟨812895, by rfl⟩ : syracuseStep 2167721 = 1625791) B1625791
theorem B10983113 : Blo 424774 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B2432105 : Blo 424774 2432105 := bstep (se 2 (by rfl) ⟨912039, by rfl⟩ : syracuseStep 2432105 = 1824079) B1824079
theorem B957887 : Blo 424774 957887 := bstep (se 1 (by rfl) ⟨718415, by rfl⟩ : syracuseStep 957887 = 1436831) B1436831
theorem B3644909 : Blo 424774 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B1023671 : Blo 424774 1023671 := bstep (se 1 (by rfl) ⟨767753, by rfl⟩ : syracuseStep 1023671 = 1535507) B1535507
theorem B959903 : Blo 424774 959903 := bstep (se 1 (by rfl) ⟨719927, by rfl⟩ : syracuseStep 959903 = 1439855) B1439855
theorem B10233479 : Blo 424774 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B2631503 : Blo 424774 2631503 := bstep (se 1 (by rfl) ⟨1973627, by rfl⟩ : syracuseStep 2631503 = 3947255) B3947255
theorem B962027 : Blo 424774 962027 := bstep (se 1 (by rfl) ⟨721520, by rfl⟩ : syracuseStep 962027 = 1443041) B1443041
theorem B4633159 : Blo 424774 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B5551939 : Blo 424774 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B637691 : Blo 424774 637691 := bstep (se 1 (by rfl) ⟨478268, by rfl⟩ : syracuseStep 637691 = 956537) B956537
theorem B637895 : Blo 424774 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B605161 : Blo 424774 605161 := bstep (se 2 (by rfl) ⟨226935, by rfl⟩ : syracuseStep 605161 = 453871) B453871
theorem B36846575 : Blo 424774 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B637979 : Blo 424774 637979 := bstep (se 1 (by rfl) ⟨478484, by rfl⟩ : syracuseStep 637979 = 956969) B956969
theorem B638111 : Blo 424774 638111 := bstep (se 1 (by rfl) ⟨478583, by rfl⟩ : syracuseStep 638111 = 957167) B957167
theorem B638951 : Blo 424774 638951 := bstep (se 1 (by rfl) ⟨479213, by rfl⟩ : syracuseStep 638951 = 958427) B958427
theorem B639353 : Blo 424774 639353 := bstep (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) B479515
theorem B2048399 : Blo 424774 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B5358311 : Blo 424774 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B640169 : Blo 424774 640169 := bstep (se 2 (by rfl) ⟨240063, by rfl⟩ : syracuseStep 640169 = 480127) B480127
theorem B17450315 : Blo 424774 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B641087 : Blo 424774 641087 := bstep (se 1 (by rfl) ⟨480815, by rfl⟩ : syracuseStep 641087 = 961631) B961631
theorem B1624319 : Blo 424774 1624319 := bstep (se 1 (by rfl) ⟨1218239, by rfl⟩ : syracuseStep 1624319 = 2436479) B2436479
theorem B1657849 : Blo 424774 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B113331403 : Blo 424774 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B642587 : Blo 424774 642587 := bstep (se 1 (by rfl) ⟨481940, by rfl⟩ : syracuseStep 642587 = 963881) B963881
theorem B642665 : Blo 424774 642665 := bstep (se 2 (by rfl) ⟨240999, by rfl⟩ : syracuseStep 642665 = 481999) B481999
theorem B2084473 : Blo 424774 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B2313967 : Blo 424774 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B2150711 : Blo 424774 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B2216375 : Blo 424774 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B1299503 : Blo 424774 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B20993219 : Blo 424774 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B5625283 : Blo 424774 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B2153303 : Blo 424774 2153303 := bstep (se 1 (by rfl) ⟨1614977, by rfl⟩ : syracuseStep 2153303 = 3229955) B3229955
theorem B6545099 : Blo 424774 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B5858153 : Blo 424774 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B4089143 : Blo 424774 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B812911 : Blo 424774 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B1828777 : Blo 424774 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1829735 : Blo 424774 1829735 := bstep (se 1 (by rfl) ⟨1372301, by rfl⟩ : syracuseStep 1829735 = 2744603) B2744603
theorem B453799 : Blo 424774 453799 := bstep (se 1 (by rfl) ⟨340349, by rfl⟩ : syracuseStep 453799 = 680699) B680699
theorem B4091147 : Blo 424774 4091147 := bstep (se 1 (by rfl) ⟨3068360, by rfl⟩ : syracuseStep 4091147 = 6136721) B6136721
theorem B170454743 : Blo 424774 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B1437803 : Blo 424774 1437803 := bstep (se 1 (by rfl) ⟨1078352, by rfl⟩ : syracuseStep 1437803 = 2156705) B2156705
theorem B2159135 : Blo 424774 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B1439207 : Blo 424774 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B3274273 : Blo 424774 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B1439315 : Blo 424774 1439315 := bstep (se 1 (by rfl) ⟨1079486, by rfl⟩ : syracuseStep 1439315 = 2158973) B2158973
theorem B1210859 : Blo 424774 1210859 := bstep (se 1 (by rfl) ⟨908144, by rfl⟩ : syracuseStep 1210859 = 1816289) B1816289
theorem B719455 : Blo 424774 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B3242591 : Blo 424774 3242591 := bstep (se 1 (by rfl) ⟨2431943, by rfl⟩ : syracuseStep 3242591 = 4863887) B4863887
theorem B1079963 : Blo 424774 1079963 := bstep (se 1 (by rfl) ⟨809972, by rfl⟩ : syracuseStep 1079963 = 1619945) B1619945
theorem B3636161 : Blo 424774 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B425119 : Blo 424774 425119 := bstep (se 1 (by rfl) ⟨318839, by rfl⟩ : syracuseStep 425119 = 637679) B637679
theorem B426235 : Blo 424774 426235 := bstep (se 1 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 426235 = 639353) B639353
theorem B3572207 : Blo 424774 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B426779 : Blo 424774 426779 := bstep (se 1 (by rfl) ⟨320084, by rfl⟩ : syracuseStep 426779 = 640169) B640169
theorem B11633543 : Blo 424774 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B427391 : Blo 424774 427391 := bstep (se 1 (by rfl) ⟨320543, by rfl⟩ : syracuseStep 427391 = 641087) B641087
theorem B1082879 : Blo 424774 1082879 := bstep (se 1 (by rfl) ⟨812159, by rfl⟩ : syracuseStep 1082879 = 1624319) B1624319
theorem B723127 : Blo 424774 723127 := bstep (se 1 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 723127 = 1084691) B1084691
theorem B46795103 : Blo 424774 46795103 := bstep (se 1 (by rfl) ⟨35096327, by rfl⟩ : syracuseStep 46795103 = 70192655) B70192655
theorem B428391 : Blo 424774 428391 := bstep (se 1 (by rfl) ⟨321293, by rfl⟩ : syracuseStep 428391 = 642587) B642587
theorem B428443 : Blo 424774 428443 := bstep (se 1 (by rfl) ⟨321332, by rfl⟩ : syracuseStep 428443 = 642665) B642665
theorem B11864519 : Blo 424774 11864519 := bstep (se 1 (by rfl) ⟨8898389, by rfl⟩ : syracuseStep 11864519 = 17796779) B17796779
theorem B1083881 : Blo 424774 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B1445147 : Blo 424774 1445147 := bstep (se 1 (by rfl) ⟨1083860, by rfl⟩ : syracuseStep 1445147 = 2167721) B2167721
theorem B13995479 : Blo 424774 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B3085289 : Blo 424774 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B2429939 : Blo 424774 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B4363399 : Blo 424774 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B3905435 : Blo 424774 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B6822319 : Blo 424774 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B1219823 : Blo 424774 1219823 := bstep (se 1 (by rfl) ⟨914867, by rfl⟩ : syracuseStep 1219823 = 1829735) B1829735
theorem B4365697 : Blo 424774 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B2727431 : Blo 424774 2727431 := bstep (se 1 (by rfl) ⟨2045573, by rfl⟩ : syracuseStep 2727431 = 4091147) B4091147
theorem B958535 : Blo 424774 958535 := bstep (se 1 (by rfl) ⟨718901, by rfl⟩ : syracuseStep 958535 = 1437803) B1437803
theorem B11117189 : Blo 424774 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B959273 : Blo 424774 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B959471 : Blo 424774 959471 := bstep (se 1 (by rfl) ⟨719603, by rfl⟩ : syracuseStep 959471 = 1439207) B1439207
theorem B959543 : Blo 424774 959543 := bstep (se 1 (by rfl) ⟨719657, by rfl⟩ : syracuseStep 959543 = 1439315) B1439315
theorem B1617043 : Blo 424774 1617043 := bstep (se 1 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 1617043 = 2425565) B2425565
theorem B2438369 : Blo 424774 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B866335 : Blo 424774 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B7322075 : Blo 424774 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B2210465 : Blo 424774 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B605065 : Blo 424774 605065 := bstep (se 2 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 605065 = 453799) B453799
theorem B151108537 : Blo 424774 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B1621403 : Blo 424774 1621403 := bstep (se 1 (by rfl) ⟨1216052, by rfl⟩ : syracuseStep 1621403 = 2432105) B2432105
theorem B638591 : Blo 424774 638591 := bstep (se 1 (by rfl) ⟨478943, by rfl⟩ : syracuseStep 638591 = 957887) B957887
theorem B3227525 : Blo 424774 3227525 := bstep (se 4 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 3227525 = 605161) B605161
theorem B6177545 : Blo 424774 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B639935 : Blo 424774 639935 := bstep (se 1 (by rfl) ⟨479951, by rfl⟩ : syracuseStep 639935 = 959903) B959903
theorem B1754335 : Blo 424774 1754335 := bstep (se 1 (by rfl) ⟨1315751, by rfl⟩ : syracuseStep 1754335 = 2631503) B2631503
theorem B641351 : Blo 424774 641351 := bstep (se 1 (by rfl) ⟨481013, by rfl⟩ : syracuseStep 641351 = 962027) B962027
theorem B807239 : Blo 424774 807239 := bstep (se 1 (by rfl) ⟨605429, by rfl⟩ : syracuseStep 807239 = 1210859) B1210859
theorem B24564383 : Blo 424774 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B1365599 : Blo 424774 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B809023 : Blo 424774 809023 := bstep (se 1 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 809023 = 1213535) B1213535
theorem B8739197 : Blo 424774 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B482287 : Blo 424774 482287 := bstep (se 1 (by rfl) ⟨361715, by rfl⟩ : syracuseStep 482287 = 723431) B723431
theorem B5857271 : Blo 424774 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B1433807 : Blo 424774 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B10904381 : Blo 424774 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B1435535 : Blo 424774 1435535 := bstep (se 1 (by rfl) ⟨1076651, by rfl⟩ : syracuseStep 1435535 = 2153303) B2153303
theorem B682447 : Blo 424774 682447 := bstep (se 1 (by rfl) ⟨511835, by rfl⟩ : syracuseStep 682447 = 1023671) B1023671
theorem B7500377 : Blo 424774 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B94565333 : Blo 424774 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B7402585 : Blo 424774 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B113636495 : Blo 424774 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B1439423 : Blo 424774 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B2161727 : Blo 424774 2161727 := bstep (se 1 (by rfl) ⟨1621295, by rfl⟩ : syracuseStep 2161727 = 3242591) B3242591
theorem B719975 : Blo 424774 719975 := bstep (se 1 (by rfl) ⟨539981, by rfl⟩ : syracuseStep 719975 = 1079963) B1079963
theorem B425127 : Blo 424774 425127 := bstep (se 1 (by rfl) ⟨318845, by rfl⟩ : syracuseStep 425127 = 637691) B637691
theorem B2424107 : Blo 424774 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B425263 : Blo 424774 425263 := bstep (se 1 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 425263 = 637895) B637895
theorem B425319 : Blo 424774 425319 := bstep (se 1 (by rfl) ⟨318989, by rfl⟩ : syracuseStep 425319 = 637979) B637979
theorem B425407 : Blo 424774 425407 := bstep (se 1 (by rfl) ⟨319055, by rfl⟩ : syracuseStep 425407 = 638111) B638111
theorem B425967 : Blo 424774 425967 := bstep (se 1 (by rfl) ⟨319475, by rfl⟩ : syracuseStep 425967 = 638951) B638951
theorem B426623 : Blo 424774 426623 := bstep (se 1 (by rfl) ⟨319967, by rfl⟩ : syracuseStep 426623 = 639935) B639935
theorem B721919 : Blo 424774 721919 := bstep (se 1 (by rfl) ⟨541439, by rfl⟩ : syracuseStep 721919 = 1082879) B1082879
theorem B427567 : Blo 424774 427567 := bstep (se 1 (by rfl) ⟨320675, by rfl⟩ : syracuseStep 427567 = 641351) B641351
theorem B31196735 : Blo 424774 31196735 := bstep (se 1 (by rfl) ⟨23397551, by rfl⟩ : syracuseStep 31196735 = 46795103) B46795103
theorem B722587 : Blo 424774 722587 := bstep (se 1 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 722587 = 1083881) B1083881
theorem B3641597 : Blo 424774 3641597 := bstep (se 3 (by rfl) ⟨682799, by rfl⟩ : syracuseStep 3641597 = 1365599) B1365599
theorem B3904847 : Blo 424774 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B955871 : Blo 424774 955871 := bstep (se 1 (by rfl) ⟨716903, by rfl⟩ : syracuseStep 955871 = 1433807) B1433807
theorem B7411459 : Blo 424774 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B957023 : Blo 424774 957023 := bstep (se 1 (by rfl) ⟨717767, by rfl⟩ : syracuseStep 957023 = 1435535) B1435535
theorem B9870113 : Blo 424774 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B1155113 : Blo 424774 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B959615 : Blo 424774 959615 := bstep (se 1 (by rfl) ⟨719711, by rfl⟩ : syracuseStep 959615 = 1439423) B1439423
theorem B1616071 : Blo 424774 1616071 := bstep (se 1 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 1616071 = 2424107) B2424107
theorem B20001005 : Blo 424774 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B2339113 : Blo 424774 2339113 := bstep (se 2 (by rfl) ⟨877167, by rfl⟩ : syracuseStep 2339113 = 1754335) B1754335
theorem B7909679 : Blo 424774 7909679 := bstep (se 1 (by rfl) ⟨5932259, by rfl⟩ : syracuseStep 7909679 = 11864519) B11864519
theorem B963431 : Blo 424774 963431 := bstep (se 1 (by rfl) ⟨722573, by rfl⟩ : syracuseStep 963431 = 1445147) B1445147
theorem B538159 : Blo 424774 538159 := bstep (se 1 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 538159 = 807239) B807239
theorem B964169 : Blo 424774 964169 := bstep (se 2 (by rfl) ⟨361563, by rfl⟩ : syracuseStep 964169 = 723127) B723127
theorem B1619959 : Blo 424774 1619959 := bstep (se 1 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 1619959 = 2429939) B2429939
theorem B1818287 : Blo 424774 1818287 := bstep (se 1 (by rfl) ⟨1363715, by rfl⟩ : syracuseStep 1818287 = 2727431) B2727431
theorem B639023 : Blo 424774 639023 := bstep (se 1 (by rfl) ⟨479267, by rfl⟩ : syracuseStep 639023 = 958535) B958535
theorem B639515 : Blo 424774 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B639647 : Blo 424774 639647 := bstep (se 1 (by rfl) ⟨479735, by rfl⟩ : syracuseStep 639647 = 959471) B959471
theorem B639695 : Blo 424774 639695 := bstep (se 1 (by rfl) ⟨479771, by rfl⟩ : syracuseStep 639695 = 959543) B959543
theorem B5817865 : Blo 424774 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B9096425 : Blo 424774 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B1625579 : Blo 424774 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B806753 : Blo 424774 806753 := bstep (se 2 (by rfl) ⟨302532, by rfl⟩ : syracuseStep 806753 = 605065) B605065
theorem B201478049 : Blo 424774 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B643049 : Blo 424774 643049 := bstep (se 2 (by rfl) ⟨241143, by rfl⟩ : syracuseStep 643049 = 482287) B482287
theorem B5820929 : Blo 424774 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B479983 : Blo 424774 479983 := bstep (se 1 (by rfl) ⟨359987, by rfl⟩ : syracuseStep 479983 = 719975) B719975
theorem B2151683 : Blo 424774 2151683 := bstep (se 1 (by rfl) ⟨1613762, by rfl⟩ : syracuseStep 2151683 = 3227525) B3227525
theorem B2381471 : Blo 424774 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B4118363 : Blo 424774 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B7755695 : Blo 424774 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B9330319 : Blo 424774 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B252174221 : Blo 424774 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B16376255 : Blo 424774 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B909929 : Blo 424774 909929 := bstep (se 2 (by rfl) ⟨341223, by rfl⟩ : syracuseStep 909929 = 682447) B682447
theorem B2056859 : Blo 424774 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B2156057 : Blo 424774 2156057 := bstep (se 2 (by rfl) ⟨808521, by rfl⟩ : syracuseStep 2156057 = 1617043) B1617043
theorem B5826131 : Blo 424774 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B813215 : Blo 424774 813215 := bstep (se 1 (by rfl) ⟨609911, by rfl⟩ : syracuseStep 813215 = 1219823) B1219823
theorem B10414493 : Blo 424774 10414493 := bstep (se 3 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 10414493 = 3905435) B3905435
theorem B7269587 : Blo 424774 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B1078697 : Blo 424774 1078697 := bstep (se 2 (by rfl) ⟨404511, by rfl⟩ : syracuseStep 1078697 = 809023) B809023
theorem B75757663 : Blo 424774 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B4881383 : Blo 424774 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B1473643 : Blo 424774 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1441151 : Blo 424774 1441151 := bstep (se 1 (by rfl) ⟨1080863, by rfl⟩ : syracuseStep 1441151 = 2161727) B2161727
theorem B1080935 : Blo 424774 1080935 := bstep (se 1 (by rfl) ⟨810701, by rfl⟩ : syracuseStep 1080935 = 1621403) B1621403
theorem B425727 : Blo 424774 425727 := bstep (se 1 (by rfl) ⟨319295, by rfl⟩ : syracuseStep 425727 = 638591) B638591
theorem B426015 : Blo 424774 426015 := bstep (se 1 (by rfl) ⟨319511, by rfl⟩ : syracuseStep 426015 = 639023) B639023
theorem B426343 : Blo 424774 426343 := bstep (se 1 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 426343 = 639515) B639515
theorem B426431 : Blo 424774 426431 := bstep (se 1 (by rfl) ⟨319823, by rfl⟩ : syracuseStep 426431 = 639647) B639647
theorem B426463 : Blo 424774 426463 := bstep (se 1 (by rfl) ⟨319847, by rfl⟩ : syracuseStep 426463 = 639695) B639695
theorem B6064283 : Blo 424774 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B1083719 : Blo 424774 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B134318699 : Blo 424774 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B428699 : Blo 424774 428699 := bstep (se 1 (by rfl) ⟨321524, by rfl⟩ : syracuseStep 428699 = 643049) B643049
theorem B2427731 : Blo 424774 2427731 := bstep (se 1 (by rfl) ⟨1820798, by rfl⟩ : syracuseStep 2427731 = 3641597) B3641597
theorem B10917503 : Blo 424774 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B3118817 : Blo 424774 3118817 := bstep (se 2 (by rfl) ⟨1169556, by rfl⟩ : syracuseStep 3118817 = 2339113) B2339113
theorem B3254255 : Blo 424774 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B960767 : Blo 424774 960767 := bstep (se 1 (by rfl) ⟨720575, by rfl⟩ : syracuseStep 960767 = 1441151) B1441151
theorem B404040869 : Blo 424774 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B963449 : Blo 424774 963449 := bstep (se 2 (by rfl) ⟨361293, by rfl⟩ : syracuseStep 963449 = 722587) B722587
theorem B537835 : Blo 424774 537835 := bstep (se 1 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 537835 = 806753) B806753
theorem B3880619 : Blo 424774 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2603231 : Blo 424774 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B637247 : Blo 424774 637247 := bstep (se 1 (by rfl) ⟨477935, by rfl⟩ : syracuseStep 637247 = 955871) B955871
theorem B1587647 : Blo 424774 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B638015 : Blo 424774 638015 := bstep (se 1 (by rfl) ⟨478511, by rfl⟩ : syracuseStep 638015 = 957023) B957023
theorem B168116147 : Blo 424774 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B770075 : Blo 424774 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B606619 : Blo 424774 606619 := bstep (se 1 (by rfl) ⟨454964, by rfl⟩ : syracuseStep 606619 = 909929) B909929
theorem B639743 : Blo 424774 639743 := bstep (se 1 (by rfl) ⟨479807, by rfl⟩ : syracuseStep 639743 = 959615) B959615
theorem B639977 : Blo 424774 639977 := bstep (se 2 (by rfl) ⟨239991, by rfl⟩ : syracuseStep 639977 = 479983) B479983
theorem B3884087 : Blo 424774 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B542143 : Blo 424774 542143 := bstep (se 1 (by rfl) ⟨406607, by rfl⟩ : syracuseStep 542143 = 813215) B813215
theorem B9881945 : Blo 424774 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B642287 : Blo 424774 642287 := bstep (se 1 (by rfl) ⟨481715, by rfl⟩ : syracuseStep 642287 = 963431) B963431
theorem B49761701 : Blo 424774 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B642779 : Blo 424774 642779 := bstep (se 1 (by rfl) ⟨482084, by rfl⟩ : syracuseStep 642779 = 964169) B964169
theorem B481279 : Blo 424774 481279 := bstep (se 1 (by rfl) ⟨360959, by rfl⟩ : syracuseStep 481279 = 721919) B721919
theorem B20797823 : Blo 424774 20797823 := bstep (se 1 (by rfl) ⟨15598367, by rfl⟩ : syracuseStep 20797823 = 31196735) B31196735
theorem B7757153 : Blo 424774 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B2154761 : Blo 424774 2154761 := bstep (se 2 (by rfl) ⟨808035, by rfl⟩ : syracuseStep 2154761 = 1616071) B1616071
theorem B1434455 : Blo 424774 1434455 := bstep (se 1 (by rfl) ⟨1075841, by rfl⟩ : syracuseStep 1434455 = 2151683) B2151683
theorem B2745575 : Blo 424774 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B5170463 : Blo 424774 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B6580075 : Blo 424774 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B1371239 : Blo 424774 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B7859429 : Blo 424774 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B1437371 : Blo 424774 1437371 := bstep (se 1 (by rfl) ⟨1078028, by rfl⟩ : syracuseStep 1437371 = 2156057) B2156057
theorem B6942995 : Blo 424774 6942995 := bstep (se 1 (by rfl) ⟨5207246, by rfl⟩ : syracuseStep 6942995 = 10414493) B10414493
theorem B717545 : Blo 424774 717545 := bstep (se 2 (by rfl) ⟨269079, by rfl⟩ : syracuseStep 717545 = 538159) B538159
theorem B4846391 : Blo 424774 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B2159945 : Blo 424774 2159945 := bstep (se 2 (by rfl) ⟨809979, by rfl⟩ : syracuseStep 2159945 = 1619959) B1619959
theorem B13334003 : Blo 424774 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B5273119 : Blo 424774 5273119 := bstep (se 1 (by rfl) ⟨3954839, by rfl⟩ : syracuseStep 5273119 = 7909679) B7909679
theorem B719131 : Blo 424774 719131 := bstep (se 1 (by rfl) ⟨539348, by rfl⟩ : syracuseStep 719131 = 1078697) B1078697
theorem B720623 : Blo 424774 720623 := bstep (se 1 (by rfl) ⟨540467, by rfl⟩ : syracuseStep 720623 = 1080935) B1080935
theorem B1212191 : Blo 424774 1212191 := bstep (se 1 (by rfl) ⟨909143, by rfl⟩ : syracuseStep 1212191 = 1818287) B1818287
theorem B426495 : Blo 424774 426495 := bstep (se 1 (by rfl) ⟨319871, by rfl⟩ : syracuseStep 426495 = 639743) B639743
theorem B426651 : Blo 424774 426651 := bstep (se 1 (by rfl) ⟨319988, by rfl⟩ : syracuseStep 426651 = 639977) B639977
theorem B2589391 : Blo 424774 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B722479 : Blo 424774 722479 := bstep (se 1 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 722479 = 1083719) B1083719
theorem B6587963 : Blo 424774 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B722857 : Blo 424774 722857 := bstep (se 2 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 722857 = 542143) B542143
theorem B428191 : Blo 424774 428191 := bstep (se 1 (by rfl) ⟨321143, by rfl⟩ : syracuseStep 428191 = 642287) B642287
theorem B428519 : Blo 424774 428519 := bstep (se 1 (by rfl) ⟨321389, by rfl⟩ : syracuseStep 428519 = 642779) B642779
theorem B7278335 : Blo 424774 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B13865215 : Blo 424774 13865215 := bstep (se 1 (by rfl) ⟨10398911, by rfl⟩ : syracuseStep 13865215 = 20797823) B20797823
theorem B956303 : Blo 424774 956303 := bstep (se 1 (by rfl) ⟨717227, by rfl⟩ : syracuseStep 956303 = 1434455) B1434455
theorem B3446975 : Blo 424774 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B4233725 : Blo 424774 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B2169503 : Blo 424774 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B269360579 : Blo 424774 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B958247 : Blo 424774 958247 := bstep (se 1 (by rfl) ⟨718685, by rfl⟩ : syracuseStep 958247 = 1437371) B1437371
theorem B28123301 : Blo 424774 28123301 := bstep (se 4 (by rfl) ⟨2636559, by rfl⟩ : syracuseStep 28123301 = 5273119) B5273119
theorem B4628663 : Blo 424774 4628663 := bstep (se 1 (by rfl) ⟨3471497, by rfl⟩ : syracuseStep 4628663 = 6942995) B6942995
theorem B958841 : Blo 424774 958841 := bstep (se 2 (by rfl) ⟨359565, by rfl⟩ : syracuseStep 958841 = 719131) B719131
theorem B8889335 : Blo 424774 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B112077431 : Blo 424774 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B4042855 : Blo 424774 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B1618487 : Blo 424774 1618487 := bstep (se 1 (by rfl) ⟨1213865, by rfl⟩ : syracuseStep 1618487 = 2427731) B2427731
theorem B33174467 : Blo 424774 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B2079211 : Blo 424774 2079211 := bstep (se 1 (by rfl) ⟨1559408, by rfl⟩ : syracuseStep 2079211 = 3118817) B3118817
theorem B640511 : Blo 424774 640511 := bstep (se 1 (by rfl) ⟨480383, by rfl⟩ : syracuseStep 640511 = 960767) B960767
theorem B641705 : Blo 424774 641705 := bstep (se 2 (by rfl) ⟨240639, by rfl⟩ : syracuseStep 641705 = 481279) B481279
theorem B478363 : Blo 424774 478363 := bstep (se 1 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 478363 = 717545) B717545
theorem B3230927 : Blo 424774 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B642299 : Blo 424774 642299 := bstep (se 1 (by rfl) ⟨481724, by rfl⟩ : syracuseStep 642299 = 963449) B963449
theorem B480415 : Blo 424774 480415 := bstep (se 1 (by rfl) ⟨360311, by rfl⟩ : syracuseStep 480415 = 720623) B720623
theorem B808127 : Blo 424774 808127 := bstep (se 1 (by rfl) ⟨606095, by rfl⟩ : syracuseStep 808127 = 1212191) B1212191
theorem B513383 : Blo 424774 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B89545799 : Blo 424774 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B3235301 : Blo 424774 3235301 := bstep (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) B606619
theorem B8773433 : Blo 424774 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B5171435 : Blo 424774 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B1436507 : Blo 424774 1436507 := bstep (se 1 (by rfl) ⟨1077380, by rfl⟩ : syracuseStep 1436507 = 2154761) B2154761
theorem B1830383 : Blo 424774 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B717113 : Blo 424774 717113 := bstep (se 2 (by rfl) ⟨268917, by rfl⟩ : syracuseStep 717113 = 537835) B537835
theorem B914159 : Blo 424774 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B5239619 : Blo 424774 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B1439963 : Blo 424774 1439963 := bstep (se 1 (by rfl) ⟨1079972, by rfl⟩ : syracuseStep 1439963 = 2159945) B2159945
theorem B2587079 : Blo 424774 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B1735487 : Blo 424774 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B424831 : Blo 424774 424831 := bstep (se 1 (by rfl) ⟨318623, by rfl⟩ : syracuseStep 424831 = 637247) B637247
theorem B425343 : Blo 424774 425343 := bstep (se 1 (by rfl) ⟨319007, by rfl⟩ : syracuseStep 425343 = 638015) B638015
theorem B427007 : Blo 424774 427007 := bstep (se 1 (by rfl) ⟨320255, by rfl⟩ : syracuseStep 427007 = 640511) B640511
theorem B4391975 : Blo 424774 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B427803 : Blo 424774 427803 := bstep (se 1 (by rfl) ⟨320852, by rfl⟩ : syracuseStep 427803 = 641705) B641705
theorem B428199 : Blo 424774 428199 := bstep (se 1 (by rfl) ⟨321149, by rfl⟩ : syracuseStep 428199 = 642299) B642299
theorem B4852223 : Blo 424774 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B2297983 : Blo 424774 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B2822483 : Blo 424774 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B1446335 : Blo 424774 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B18748867 : Blo 424774 18748867 := bstep (se 1 (by rfl) ⟨14061650, by rfl⟩ : syracuseStep 18748867 = 28123301) B28123301
theorem B3085775 : Blo 424774 3085775 := bstep (se 1 (by rfl) ⟨2314331, by rfl⟩ : syracuseStep 3085775 = 4628663) B4628663
theorem B18486953 : Blo 424774 18486953 := bstep (se 2 (by rfl) ⟨6932607, by rfl⟩ : syracuseStep 18486953 = 13865215) B13865215
theorem B3447623 : Blo 424774 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B74718287 : Blo 424774 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B957671 : Blo 424774 957671 := bstep (se 1 (by rfl) ⟨718253, by rfl⟩ : syracuseStep 957671 = 1436507) B1436507
theorem B1220255 : Blo 424774 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B959975 : Blo 424774 959975 := bstep (se 1 (by rfl) ⟨719981, by rfl⟩ : syracuseStep 959975 = 1439963) B1439963
theorem B963305 : Blo 424774 963305 := bstep (se 2 (by rfl) ⟨361239, by rfl⟩ : syracuseStep 963305 = 722479) B722479
theorem B963809 : Blo 424774 963809 := bstep (se 2 (by rfl) ⟨361428, by rfl⟩ : syracuseStep 963809 = 722857) B722857
theorem B538751 : Blo 424774 538751 := bstep (se 1 (by rfl) ⟨404063, by rfl⟩ : syracuseStep 538751 = 808127) B808127
theorem B13810085 : Blo 424774 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B637535 : Blo 424774 637535 := bstep (se 1 (by rfl) ⟨478151, by rfl⟩ : syracuseStep 637535 = 956303) B956303
theorem B637817 : Blo 424774 637817 := bstep (se 2 (by rfl) ⟨239181, by rfl⟩ : syracuseStep 637817 = 478363) B478363
theorem B638831 : Blo 424774 638831 := bstep (se 1 (by rfl) ⟨479123, by rfl⟩ : syracuseStep 638831 = 958247) B958247
theorem B5848955 : Blo 424774 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B5390473 : Blo 424774 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B639227 : Blo 424774 639227 := bstep (se 1 (by rfl) ⟨479420, by rfl⟩ : syracuseStep 639227 = 958841) B958841
theorem B6898877 : Blo 424774 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B640553 : Blo 424774 640553 := bstep (se 2 (by rfl) ⟨240207, by rfl⟩ : syracuseStep 640553 = 480415) B480415
theorem B478075 : Blo 424774 478075 := bstep (se 1 (by rfl) ⟨358556, by rfl⟩ : syracuseStep 478075 = 717113) B717113
theorem B609439 : Blo 424774 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B3493079 : Blo 424774 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B2772281 : Blo 424774 2772281 := bstep (se 2 (by rfl) ⟨1039605, by rfl⟩ : syracuseStep 2772281 = 2079211) B2079211
theorem B718294877 : Blo 424774 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B2153951 : Blo 424774 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B1369021 : Blo 424774 1369021 := bstep (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) B513383
theorem B59697199 : Blo 424774 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B2156867 : Blo 424774 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B5926223 : Blo 424774 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B1078991 : Blo 424774 1078991 := bstep (se 1 (by rfl) ⟨809243, by rfl⟩ : syracuseStep 1078991 = 1618487) B1618487
theorem B22116311 : Blo 424774 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B18511861 : Blo 424774 18511861 := bstep (se 5 (by rfl) ⟨867743, by rfl⟩ : syracuseStep 18511861 = 1735487) B1735487
theorem B426151 : Blo 424774 426151 := bstep (se 1 (by rfl) ⟨319613, by rfl⟩ : syracuseStep 426151 = 639227) B639227
theorem B427035 : Blo 424774 427035 := bstep (se 1 (by rfl) ⟨320276, by rfl⟩ : syracuseStep 427035 = 640553) B640553
theorem B37259509 : Blo 424774 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B79596265 : Blo 424774 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B12324635 : Blo 424774 12324635 := bstep (se 1 (by rfl) ⟨9243476, by rfl⟩ : syracuseStep 12324635 = 18486953) B18486953
theorem B2298415 : Blo 424774 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B49812191 : Blo 424774 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B24682481 : Blo 424774 24682481 := bstep (se 2 (by rfl) ⟨9255930, by rfl⟩ : syracuseStep 24682481 = 18511861) B18511861
theorem B7187297 : Blo 424774 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B2927983 : Blo 424774 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B4599251 : Blo 424774 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B1848187 : Blo 424774 1848187 := bstep (se 1 (by rfl) ⟨1386140, by rfl⟩ : syracuseStep 1848187 = 2772281) B2772281
theorem B964223 : Blo 424774 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B637433 : Blo 424774 637433 := bstep (se 2 (by rfl) ⟨239037, by rfl⟩ : syracuseStep 637433 = 478075) B478075
theorem B638447 : Blo 424774 638447 := bstep (se 1 (by rfl) ⟨478835, by rfl⟩ : syracuseStep 638447 = 957671) B957671
theorem B3063977 : Blo 424774 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B639983 : Blo 424774 639983 := bstep (se 1 (by rfl) ⟨479987, by rfl⟩ : syracuseStep 639983 = 959975) B959975
theorem B3950815 : Blo 424774 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B642203 : Blo 424774 642203 := bstep (se 1 (by rfl) ⟨481652, by rfl⟩ : syracuseStep 642203 = 963305) B963305
theorem B642539 : Blo 424774 642539 := bstep (se 1 (by rfl) ⟨481904, by rfl⟩ : syracuseStep 642539 = 963809) B963809
theorem B7526621 : Blo 424774 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B1825361 : Blo 424774 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B3234815 : Blo 424774 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B478863251 : Blo 424774 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B2057183 : Blo 424774 2057183 := bstep (se 1 (by rfl) ⟨1542887, by rfl⟩ : syracuseStep 2057183 = 3085775) B3085775
theorem B812585 : Blo 424774 812585 := bstep (se 2 (by rfl) ⟨304719, by rfl⟩ : syracuseStep 812585 = 609439) B609439
theorem B1435967 : Blo 424774 1435967 := bstep (se 1 (by rfl) ⟨1076975, by rfl⟩ : syracuseStep 1435967 = 2153951) B2153951
theorem B813503 : Blo 424774 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B1436669 : Blo 424774 1436669 := bstep (se 3 (by rfl) ⟨269375, by rfl⟩ : syracuseStep 1436669 = 538751) B538751
theorem B1437911 : Blo 424774 1437911 := bstep (se 1 (by rfl) ⟨1078433, by rfl⟩ : syracuseStep 1437911 = 2156867) B2156867
theorem B24998489 : Blo 424774 24998489 := bstep (se 2 (by rfl) ⟨9374433, by rfl⟩ : syracuseStep 24998489 = 18748867) B18748867
theorem B719327 : Blo 424774 719327 := bstep (se 1 (by rfl) ⟨539495, by rfl⟩ : syracuseStep 719327 = 1078991) B1078991
theorem B14744207 : Blo 424774 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B9206723 : Blo 424774 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B425023 : Blo 424774 425023 := bstep (se 1 (by rfl) ⟨318767, by rfl⟩ : syracuseStep 425023 = 637535) B637535
theorem B425211 : Blo 424774 425211 := bstep (se 1 (by rfl) ⟨318908, by rfl⟩ : syracuseStep 425211 = 637817) B637817
theorem B425887 : Blo 424774 425887 := bstep (se 1 (by rfl) ⟨319415, by rfl⟩ : syracuseStep 425887 = 638831) B638831
theorem B3899303 : Blo 424774 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B426655 : Blo 424774 426655 := bstep (se 1 (by rfl) ⟨319991, by rfl⟩ : syracuseStep 426655 = 639983) B639983
theorem B428135 : Blo 424774 428135 := bstep (se 1 (by rfl) ⟨321101, by rfl⟩ : syracuseStep 428135 = 642203) B642203
theorem B428359 : Blo 424774 428359 := bstep (se 1 (by rfl) ⟨321269, by rfl⟩ : syracuseStep 428359 = 642539) B642539
theorem B49679345 : Blo 424774 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B1216907 : Blo 424774 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B3903977 : Blo 424774 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B16454987 : Blo 424774 16454987 := bstep (se 1 (by rfl) ⟨12341240, by rfl⟩ : syracuseStep 16454987 = 24682481) B24682481
theorem B2464249 : Blo 424774 2464249 := bstep (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) B1848187
theorem B2169341 : Blo 424774 2169341 := bstep (se 3 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 2169341 = 813503) B813503
theorem B957311 : Blo 424774 957311 := bstep (se 1 (by rfl) ⟨717983, by rfl⟩ : syracuseStep 957311 = 1435967) B1435967
theorem B957779 : Blo 424774 957779 := bstep (se 1 (by rfl) ⟨718334, by rfl⟩ : syracuseStep 957779 = 1436669) B1436669
theorem B958607 : Blo 424774 958607 := bstep (se 1 (by rfl) ⟨718955, by rfl⟩ : syracuseStep 958607 = 1437911) B1437911
theorem B6137815 : Blo 424774 6137815 := bstep (se 1 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 6137815 = 9206723) B9206723
theorem B2599535 : Blo 424774 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B2042651 : Blo 424774 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B33208127 : Blo 424774 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B319242167 : Blo 424774 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B20070989 : Blo 424774 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B3064553 : Blo 424774 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B541723 : Blo 424774 541723 := bstep (se 1 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 541723 = 812585) B812585
theorem B3066167 : Blo 424774 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B16665659 : Blo 424774 16665659 := bstep (se 1 (by rfl) ⟨12499244, by rfl⟩ : syracuseStep 16665659 = 24998489) B24998489
theorem B76664501 : Blo 424774 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B642815 : Blo 424774 642815 := bstep (se 1 (by rfl) ⟨482111, by rfl⟩ : syracuseStep 642815 = 964223) B964223
theorem B479551 : Blo 424774 479551 := bstep (se 1 (by rfl) ⟨359663, by rfl⟩ : syracuseStep 479551 = 719327) B719327
theorem B8216423 : Blo 424774 8216423 := bstep (se 1 (by rfl) ⟨6162317, by rfl⟩ : syracuseStep 8216423 = 12324635) B12324635
theorem B5267753 : Blo 424774 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B106128353 : Blo 424774 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B2156543 : Blo 424774 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B1371455 : Blo 424774 1371455 := bstep (se 1 (by rfl) ⟨1028591, by rfl⟩ : syracuseStep 1371455 = 2057183) B2057183
theorem B424955 : Blo 424774 424955 := bstep (se 1 (by rfl) ⟨318716, by rfl⟩ : syracuseStep 424955 = 637433) B637433
theorem B9829471 : Blo 424774 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B425631 : Blo 424774 425631 := bstep (se 1 (by rfl) ⟨319223, by rfl⟩ : syracuseStep 425631 = 638447) B638447
theorem B722297 : Blo 424774 722297 := bstep (se 2 (by rfl) ⟨270861, by rfl⟩ : syracuseStep 722297 = 541723) B541723
theorem B11110439 : Blo 424774 11110439 := bstep (se 1 (by rfl) ⟨8332829, by rfl⟩ : syracuseStep 11110439 = 16665659) B16665659
theorem B428543 : Blo 424774 428543 := bstep (se 1 (by rfl) ⟨321407, by rfl⟩ : syracuseStep 428543 = 642815) B642815
theorem B1446227 : Blo 424774 1446227 := bstep (se 1 (by rfl) ⟨1084670, by rfl⟩ : syracuseStep 1446227 = 2169341) B2169341
theorem B5477615 : Blo 424774 5477615 := bstep (se 1 (by rfl) ⟨4108211, by rfl⟩ : syracuseStep 5477615 = 8216423) B8216423
theorem B3511835 : Blo 424774 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B3285665 : Blo 424774 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B13380659 : Blo 424774 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B2043035 : Blo 424774 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B2044111 : Blo 424774 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B2602651 : Blo 424774 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B638207 : Blo 424774 638207 := bstep (se 1 (by rfl) ⟨478655, by rfl⟩ : syracuseStep 638207 = 957311) B957311
theorem B638519 : Blo 424774 638519 := bstep (se 1 (by rfl) ⟨478889, by rfl⟩ : syracuseStep 638519 = 957779) B957779
theorem B639071 : Blo 424774 639071 := bstep (se 1 (by rfl) ⟨479303, by rfl⟩ : syracuseStep 639071 = 958607) B958607
theorem B639401 : Blo 424774 639401 := bstep (se 2 (by rfl) ⟨239775, by rfl⟩ : syracuseStep 639401 = 479551) B479551
theorem B1361767 : Blo 424774 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B22138751 : Blo 424774 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B33119563 : Blo 424774 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B51109667 : Blo 424774 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B283008941 : Blo 424774 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B8183753 : Blo 424774 8183753 := bstep (se 2 (by rfl) ⟨3068907, by rfl⟩ : syracuseStep 8183753 = 6137815) B6137815
theorem B811271 : Blo 424774 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B10969991 : Blo 424774 10969991 := bstep (se 1 (by rfl) ⟨8227493, by rfl⟩ : syracuseStep 10969991 = 16454987) B16454987
theorem B1437695 : Blo 424774 1437695 := bstep (se 1 (by rfl) ⟨1078271, by rfl⟩ : syracuseStep 1437695 = 2156543) B2156543
theorem B1733023 : Blo 424774 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B914303 : Blo 424774 914303 := bstep (se 1 (by rfl) ⟨685727, by rfl⟩ : syracuseStep 914303 = 1371455) B1371455
theorem B13105961 : Blo 424774 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B212828111 : Blo 424774 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B426047 : Blo 424774 426047 := bstep (se 1 (by rfl) ⟨319535, by rfl⟩ : syracuseStep 426047 = 639071) B639071
theorem B426267 : Blo 424774 426267 := bstep (se 1 (by rfl) ⟨319700, by rfl⟩ : syracuseStep 426267 = 639401) B639401
theorem B7406959 : Blo 424774 7406959 := bstep (se 1 (by rfl) ⟨5555219, by rfl⟩ : syracuseStep 7406959 = 11110439) B11110439
theorem B2725481 : Blo 424774 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B7313327 : Blo 424774 7313327 := bstep (se 1 (by rfl) ⟨5484995, by rfl⟩ : syracuseStep 7313327 = 10969991) B10969991
theorem B8920439 : Blo 424774 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B958463 : Blo 424774 958463 := bstep (se 1 (by rfl) ⟨718847, by rfl⟩ : syracuseStep 958463 = 1437695) B1437695
theorem B1815689 : Blo 424774 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B14759167 : Blo 424774 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B964151 : Blo 424774 964151 := bstep (se 1 (by rfl) ⟨723113, by rfl⟩ : syracuseStep 964151 = 1446227) B1446227
theorem B3651743 : Blo 424774 3651743 := bstep (se 1 (by rfl) ⟨2738807, by rfl⟩ : syracuseStep 3651743 = 5477615) B5477615
theorem B2341223 : Blo 424774 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B5455835 : Blo 424774 5455835 := bstep (se 1 (by rfl) ⟨4091876, by rfl⟩ : syracuseStep 5455835 = 8183753) B8183753
theorem B540847 : Blo 424774 540847 := bstep (se 1 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 540847 = 811271) B811271
theorem B2310697 : Blo 424774 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B1362023 : Blo 424774 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B609535 : Blo 424774 609535 := bstep (se 1 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 609535 = 914303) B914303
theorem B44159417 : Blo 424774 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B8737307 : Blo 424774 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B481531 : Blo 424774 481531 := bstep (se 1 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 481531 = 722297) B722297
theorem B34073111 : Blo 424774 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B188672627 : Blo 424774 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B2190443 : Blo 424774 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B3470201 : Blo 424774 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B425471 : Blo 424774 425471 := bstep (se 1 (by rfl) ⟨319103, by rfl⟩ : syracuseStep 425471 = 638207) B638207
theorem B425679 : Blo 424774 425679 := bstep (se 1 (by rfl) ⟨319259, by rfl⟩ : syracuseStep 425679 = 638519) B638519
theorem B141885407 : Blo 424774 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B721129 : Blo 424774 721129 := bstep (se 2 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 721129 = 540847) B540847
theorem B3080929 : Blo 424774 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B3250853 : Blo 424774 3250853 := bstep (se 4 (by rfl) ⟨304767, by rfl⟩ : syracuseStep 3250853 = 609535) B609535
theorem B22715407 : Blo 424774 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B5841181 : Blo 424774 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B2434495 : Blo 424774 2434495 := bstep (se 1 (by rfl) ⟨1825871, by rfl⟩ : syracuseStep 2434495 = 3651743) B3651743
theorem B9875945 : Blo 424774 9875945 := bstep (se 2 (by rfl) ⟨3703479, by rfl⟩ : syracuseStep 9875945 = 7406959) B7406959
theorem B29439611 : Blo 424774 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B1816987 : Blo 424774 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B5946959 : Blo 424774 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B638975 : Blo 424774 638975 := bstep (se 1 (by rfl) ⟨479231, by rfl⟩ : syracuseStep 638975 = 958463) B958463
theorem B19678889 : Blo 424774 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B125781751 : Blo 424774 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B642041 : Blo 424774 642041 := bstep (se 2 (by rfl) ⟨240765, by rfl⟩ : syracuseStep 642041 = 481531) B481531
theorem B2313467 : Blo 424774 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B642767 : Blo 424774 642767 := bstep (se 1 (by rfl) ⟨482075, by rfl⟩ : syracuseStep 642767 = 964151) B964151
theorem B1560815 : Blo 424774 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B94590271 : Blo 424774 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B908015 : Blo 424774 908015 := bstep (se 1 (by rfl) ⟨681011, by rfl⟩ : syracuseStep 908015 = 1362023) B1362023
theorem B5824871 : Blo 424774 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B4875551 : Blo 424774 4875551 := bstep (se 1 (by rfl) ⟨3656663, by rfl⟩ : syracuseStep 4875551 = 7313327) B7313327
theorem B1210459 : Blo 424774 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B3637223 : Blo 424774 3637223 := bstep (se 1 (by rfl) ⟨2727917, by rfl⟩ : syracuseStep 3637223 = 5455835) B5455835
theorem B3245993 : Blo 424774 3245993 := bstep (se 2 (by rfl) ⟨1217247, by rfl⟩ : syracuseStep 3245993 = 2434495) B2434495
theorem B428027 : Blo 424774 428027 := bstep (se 1 (by rfl) ⟨321020, by rfl⟩ : syracuseStep 428027 = 642041) B642041
theorem B1542311 : Blo 424774 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B167709001 : Blo 424774 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B428511 : Blo 424774 428511 := bstep (se 1 (by rfl) ⟨321383, by rfl⟩ : syracuseStep 428511 = 642767) B642767
theorem B2167235 : Blo 424774 2167235 := bstep (se 1 (by rfl) ⟨1625426, by rfl⟩ : syracuseStep 2167235 = 3250853) B3250853
theorem B3250367 : Blo 424774 3250367 := bstep (se 1 (by rfl) ⟨2437775, by rfl⟩ : syracuseStep 3250367 = 4875551) B4875551
theorem B1613945 : Blo 424774 1613945 := bstep (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) B1210459
theorem B30287209 : Blo 424774 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B961505 : Blo 424774 961505 := bstep (se 2 (by rfl) ⟨360564, by rfl⟩ : syracuseStep 961505 = 721129) B721129
theorem B4107905 : Blo 424774 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B13119259 : Blo 424774 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B3883247 : Blo 424774 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B7788241 : Blo 424774 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B26335853 : Blo 424774 26335853 := bstep (se 3 (by rfl) ⟨4937972, by rfl⟩ : syracuseStep 26335853 = 9875945) B9875945
theorem B1040543 : Blo 424774 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B126120361 : Blo 424774 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B2421373 : Blo 424774 2421373 := bstep (se 3 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 2421373 = 908015) B908015
theorem B2422649 : Blo 424774 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B19626407 : Blo 424774 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B3964639 : Blo 424774 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B2424815 : Blo 424774 2424815 := bstep (se 1 (by rfl) ⟨1818611, by rfl⟩ : syracuseStep 2424815 = 3637223) B3637223
theorem B425983 : Blo 424774 425983 := bstep (se 1 (by rfl) ⟨319487, by rfl⟩ : syracuseStep 425983 = 638975) B638975
theorem B2588831 : Blo 424774 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B2163995 : Blo 424774 2163995 := bstep (se 1 (by rfl) ⟨1622996, by rfl⟩ : syracuseStep 2163995 = 3245993) B3245993
theorem B1444823 : Blo 424774 1444823 := bstep (se 1 (by rfl) ⟨1083617, by rfl⟩ : syracuseStep 1444823 = 2167235) B2167235
theorem B223612001 : Blo 424774 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B2166911 : Blo 424774 2166911 := bstep (se 1 (by rfl) ⟨1625183, by rfl⟩ : syracuseStep 2166911 = 3250367) B3250367
theorem B693695 : Blo 424774 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B1615099 : Blo 424774 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B13084271 : Blo 424774 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B5286185 : Blo 424774 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B1616543 : Blo 424774 1616543 := bstep (se 1 (by rfl) ⟨1212407, by rfl⟩ : syracuseStep 1616543 = 2424815) B2424815
theorem B1028207 : Blo 424774 1028207 := bstep (se 1 (by rfl) ⟨771155, by rfl⟩ : syracuseStep 1028207 = 1542311) B1542311
theorem B40382945 : Blo 424774 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B3228497 : Blo 424774 3228497 := bstep (se 2 (by rfl) ⟨1210686, by rfl⟩ : syracuseStep 3228497 = 2421373) B2421373
theorem B641003 : Blo 424774 641003 := bstep (se 1 (by rfl) ⟨480752, by rfl⟩ : syracuseStep 641003 = 961505) B961505
theorem B2738603 : Blo 424774 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B17557235 : Blo 424774 17557235 := bstep (se 1 (by rfl) ⟨13167926, by rfl⟩ : syracuseStep 17557235 = 26335853) B26335853
theorem B17492345 : Blo 424774 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1075963 : Blo 424774 1075963 := bstep (se 1 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 1075963 = 1613945) B1613945
theorem B168160481 : Blo 424774 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B10384321 : Blo 424774 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B1442663 : Blo 424774 1442663 := bstep (se 1 (by rfl) ⟨1081997, by rfl⟩ : syracuseStep 1442663 = 2163995) B2163995
theorem B427335 : Blo 424774 427335 := bstep (se 1 (by rfl) ⟨320501, by rfl⟩ : syracuseStep 427335 = 641003) B641003
theorem B1444607 : Blo 424774 1444607 := bstep (se 1 (by rfl) ⟨1083455, by rfl⟩ : syracuseStep 1444607 = 2166911) B2166911
theorem B8722847 : Blo 424774 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B11704823 : Blo 424774 11704823 := bstep (se 1 (by rfl) ⟨8778617, by rfl⟩ : syracuseStep 11704823 = 17557235) B17557235
theorem B112106987 : Blo 424774 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B963215 : Blo 424774 963215 := bstep (se 1 (by rfl) ⟨722411, by rfl⟩ : syracuseStep 963215 = 1444823) B1444823
theorem B149074667 : Blo 424774 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1849853 : Blo 424774 1849853 := bstep (se 3 (by rfl) ⟨346847, by rfl⟩ : syracuseStep 1849853 = 693695) B693695
theorem B13845761 : Blo 424774 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B3524123 : Blo 424774 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B26921963 : Blo 424774 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B1725887 : Blo 424774 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B2152331 : Blo 424774 2152331 := bstep (se 1 (by rfl) ⟨1614248, by rfl⟩ : syracuseStep 2152331 = 3228497) B3228497
theorem B1825735 : Blo 424774 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B2153465 : Blo 424774 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B1434617 : Blo 424774 1434617 := bstep (se 2 (by rfl) ⟨537981, by rfl⟩ : syracuseStep 1434617 = 1075963) B1075963
theorem B11661563 : Blo 424774 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B1077695 : Blo 424774 1077695 := bstep (se 1 (by rfl) ⟨808271, by rfl⟩ : syracuseStep 1077695 = 1616543) B1616543
theorem B685471 : Blo 424774 685471 := bstep (se 1 (by rfl) ⟨514103, by rfl⟩ : syracuseStep 685471 = 1028207) B1028207
theorem B7803215 : Blo 424774 7803215 := bstep (se 1 (by rfl) ⟨5852411, by rfl⟩ : syracuseStep 7803215 = 11704823) B11704823
theorem B956411 : Blo 424774 956411 := bstep (se 1 (by rfl) ⟨717308, by rfl⟩ : syracuseStep 956411 = 1434617) B1434617
theorem B7774375 : Blo 424774 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B2434313 : Blo 424774 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B961775 : Blo 424774 961775 := bstep (se 1 (by rfl) ⟨721331, by rfl⟩ : syracuseStep 961775 = 1442663) B1442663
theorem B963071 : Blo 424774 963071 := bstep (se 1 (by rfl) ⟨722303, by rfl⟩ : syracuseStep 963071 = 1444607) B1444607
theorem B4602365 : Blo 424774 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B642143 : Blo 424774 642143 := bstep (se 1 (by rfl) ⟨481607, by rfl⟩ : syracuseStep 642143 = 963215) B963215
theorem B1233235 : Blo 424774 1233235 := bstep (se 1 (by rfl) ⟨924926, by rfl⟩ : syracuseStep 1233235 = 1849853) B1849853
theorem B9230507 : Blo 424774 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B2349415 : Blo 424774 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B17947975 : Blo 424774 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1434887 : Blo 424774 1434887 := bstep (se 1 (by rfl) ⟨1076165, by rfl⟩ : syracuseStep 1434887 = 2152331) B2152331
theorem B1435643 : Blo 424774 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B74737991 : Blo 424774 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B23260925 : Blo 424774 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B913961 : Blo 424774 913961 := bstep (se 2 (by rfl) ⟨342735, by rfl⟩ : syracuseStep 913961 = 685471) B685471
theorem B718463 : Blo 424774 718463 := bstep (se 1 (by rfl) ⟨538847, by rfl⟩ : syracuseStep 718463 = 1077695) B1077695
theorem B99383111 : Blo 424774 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B428095 : Blo 424774 428095 := bstep (se 1 (by rfl) ⟨321071, by rfl⟩ : syracuseStep 428095 = 642143) B642143
theorem B1644313 : Blo 424774 1644313 := bstep (se 2 (by rfl) ⟨616617, by rfl⟩ : syracuseStep 1644313 = 1233235) B1233235
theorem B956591 : Blo 424774 956591 := bstep (se 1 (by rfl) ⟨717443, by rfl⟩ : syracuseStep 956591 = 1434887) B1434887
theorem B957095 : Blo 424774 957095 := bstep (se 1 (by rfl) ⟨717821, by rfl⟩ : syracuseStep 957095 = 1435643) B1435643
theorem B15507283 : Blo 424774 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B23930633 : Blo 424774 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B10365833 : Blo 424774 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B2437229 : Blo 424774 2437229 := bstep (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) B913961
theorem B12530213 : Blo 424774 12530213 := bstep (se 4 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 12530213 = 2349415) B2349415
theorem B637607 : Blo 424774 637607 := bstep (se 1 (by rfl) ⟨478205, by rfl⟩ : syracuseStep 637607 = 956411) B956411
theorem B1622875 : Blo 424774 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B49825327 : Blo 424774 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B641183 : Blo 424774 641183 := bstep (se 1 (by rfl) ⟨480887, by rfl⟩ : syracuseStep 641183 = 961775) B961775
theorem B642047 : Blo 424774 642047 := bstep (se 1 (by rfl) ⟨481535, by rfl⟩ : syracuseStep 642047 = 963071) B963071
theorem B478975 : Blo 424774 478975 := bstep (se 1 (by rfl) ⟨359231, by rfl⟩ : syracuseStep 478975 = 718463) B718463
theorem B3068243 : Blo 424774 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B5202143 : Blo 424774 5202143 := bstep (se 1 (by rfl) ⟨3901607, by rfl⟩ : syracuseStep 5202143 = 7803215) B7803215
theorem B6153671 : Blo 424774 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B66255407 : Blo 424774 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B2163833 : Blo 424774 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B427455 : Blo 424774 427455 := bstep (se 1 (by rfl) ⟨320591, by rfl⟩ : syracuseStep 427455 = 641183) B641183
theorem B428031 : Blo 424774 428031 := bstep (se 1 (by rfl) ⟨321023, by rfl⟩ : syracuseStep 428031 = 642047) B642047
theorem B4102447 : Blo 424774 4102447 := bstep (se 1 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 4102447 = 6153671) B6153671
theorem B66433769 : Blo 424774 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B2045495 : Blo 424774 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B637727 : Blo 424774 637727 := bstep (se 1 (by rfl) ⟨478295, by rfl⟩ : syracuseStep 637727 = 956591) B956591
theorem B638063 : Blo 424774 638063 := bstep (se 1 (by rfl) ⟨478547, by rfl⟩ : syracuseStep 638063 = 957095) B957095
theorem B638633 : Blo 424774 638633 := bstep (se 2 (by rfl) ⟨239487, by rfl⟩ : syracuseStep 638633 = 478975) B478975
theorem B1624819 : Blo 424774 1624819 := bstep (se 1 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 1624819 = 2437229) B2437229
theorem B3468095 : Blo 424774 3468095 := bstep (se 1 (by rfl) ⟨2601071, by rfl⟩ : syracuseStep 3468095 = 5202143) B5202143
theorem B15953755 : Blo 424774 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B6910555 : Blo 424774 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B2192417 : Blo 424774 2192417 := bstep (se 2 (by rfl) ⟨822156, by rfl⟩ : syracuseStep 2192417 = 1644313) B1644313
theorem B8353475 : Blo 424774 8353475 := bstep (se 1 (by rfl) ⟨6265106, by rfl⟩ : syracuseStep 8353475 = 12530213) B12530213
theorem B44170271 : Blo 424774 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B425071 : Blo 424774 425071 := bstep (se 1 (by rfl) ⟨318803, by rfl⟩ : syracuseStep 425071 = 637607) B637607
theorem B20676377 : Blo 424774 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B1442555 : Blo 424774 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B2166425 : Blo 424774 2166425 := bstep (se 2 (by rfl) ⟨812409, by rfl⟩ : syracuseStep 2166425 = 1624819) B1624819
theorem B21271673 : Blo 424774 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B9214073 : Blo 424774 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B2312063 : Blo 424774 2312063 := bstep (se 1 (by rfl) ⟨1734047, by rfl⟩ : syracuseStep 2312063 = 3468095) B3468095
theorem B44289179 : Blo 424774 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B1461611 : Blo 424774 1461611 := bstep (se 1 (by rfl) ⟨1096208, by rfl⟩ : syracuseStep 1461611 = 2192417) B2192417
theorem B1363663 : Blo 424774 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B29446847 : Blo 424774 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B13784251 : Blo 424774 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B5469929 : Blo 424774 5469929 := bstep (se 2 (by rfl) ⟨2051223, by rfl⟩ : syracuseStep 5469929 = 4102447) B4102447
theorem B5568983 : Blo 424774 5568983 := bstep (se 1 (by rfl) ⟨4176737, by rfl⟩ : syracuseStep 5568983 = 8353475) B8353475
theorem B425151 : Blo 424774 425151 := bstep (se 1 (by rfl) ⟨318863, by rfl⟩ : syracuseStep 425151 = 637727) B637727
theorem B425375 : Blo 424774 425375 := bstep (se 1 (by rfl) ⟨319031, by rfl⟩ : syracuseStep 425375 = 638063) B638063
theorem B425755 : Blo 424774 425755 := bstep (se 1 (by rfl) ⟨319316, by rfl⟩ : syracuseStep 425755 = 638633) B638633
theorem B1541375 : Blo 424774 1541375 := bstep (se 1 (by rfl) ⟨1156031, by rfl⟩ : syracuseStep 1541375 = 2312063) B2312063
theorem B29526119 : Blo 424774 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B1444283 : Blo 424774 1444283 := bstep (se 1 (by rfl) ⟨1083212, by rfl⟩ : syracuseStep 1444283 = 2166425) B2166425
theorem B56724461 : Blo 424774 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B19631231 : Blo 424774 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B3646619 : Blo 424774 3646619 := bstep (se 1 (by rfl) ⟨2734964, by rfl⟩ : syracuseStep 3646619 = 5469929) B5469929
theorem B3712655 : Blo 424774 3712655 := bstep (se 1 (by rfl) ⟨2784491, by rfl⟩ : syracuseStep 3712655 = 5568983) B5568983
theorem B961703 : Blo 424774 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B6142715 : Blo 424774 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B1818217 : Blo 424774 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B18379001 : Blo 424774 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B3897629 : Blo 424774 3897629 := bstep (se 3 (by rfl) ⟨730805, by rfl⟩ : syracuseStep 3897629 = 1461611) B1461611
theorem B37816307 : Blo 424774 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B9900413 : Blo 424774 9900413 := bstep (se 3 (by rfl) ⟨1856327, by rfl⟩ : syracuseStep 9900413 = 3712655) B3712655
theorem B2431079 : Blo 424774 2431079 := bstep (se 1 (by rfl) ⟨1823309, by rfl⟩ : syracuseStep 2431079 = 3646619) B3646619
theorem B2598419 : Blo 424774 2598419 := bstep (se 1 (by rfl) ⟨1948814, by rfl⟩ : syracuseStep 2598419 = 3897629) B3897629
theorem B1027583 : Blo 424774 1027583 := bstep (se 1 (by rfl) ⟨770687, by rfl⟩ : syracuseStep 1027583 = 1541375) B1541375
theorem B962855 : Blo 424774 962855 := bstep (se 1 (by rfl) ⟨722141, by rfl⟩ : syracuseStep 962855 = 1444283) B1444283
theorem B13087487 : Blo 424774 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B641135 : Blo 424774 641135 := bstep (se 1 (by rfl) ⟨480851, by rfl⟩ : syracuseStep 641135 = 961703) B961703
theorem B19684079 : Blo 424774 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B12252667 : Blo 424774 12252667 := bstep (se 1 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 12252667 = 18379001) B18379001
theorem B4095143 : Blo 424774 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2424289 : Blo 424774 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B427423 : Blo 424774 427423 := bstep (se 1 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 427423 = 641135) B641135
theorem B8724991 : Blo 424774 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B2730095 : Blo 424774 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B25210871 : Blo 424774 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B6600275 : Blo 424774 6600275 := bstep (se 1 (by rfl) ⟨4950206, by rfl⟩ : syracuseStep 6600275 = 9900413) B9900413
theorem B1620719 : Blo 424774 1620719 := bstep (se 1 (by rfl) ⟨1215539, by rfl⟩ : syracuseStep 1620719 = 2431079) B2431079
theorem B13122719 : Blo 424774 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B16336889 : Blo 424774 16336889 := bstep (se 2 (by rfl) ⟨6126333, by rfl⟩ : syracuseStep 16336889 = 12252667) B12252667
theorem B641903 : Blo 424774 641903 := bstep (se 1 (by rfl) ⟨481427, by rfl⟩ : syracuseStep 641903 = 962855) B962855
theorem B3232385 : Blo 424774 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B1732279 : Blo 424774 1732279 := bstep (se 1 (by rfl) ⟨1299209, by rfl⟩ : syracuseStep 1732279 = 2598419) B2598419
theorem B685055 : Blo 424774 685055 := bstep (se 1 (by rfl) ⟨513791, by rfl⟩ : syracuseStep 685055 = 1027583) B1027583
theorem B11633321 : Blo 424774 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B427935 : Blo 424774 427935 := bstep (se 1 (by rfl) ⟨320951, by rfl⟩ : syracuseStep 427935 = 641903) B641903
theorem B4400183 : Blo 424774 4400183 := bstep (se 1 (by rfl) ⟨3300137, by rfl⟩ : syracuseStep 4400183 = 6600275) B6600275
theorem B10891259 : Blo 424774 10891259 := bstep (se 1 (by rfl) ⟨8168444, by rfl⟩ : syracuseStep 10891259 = 16336889) B16336889
theorem B2309705 : Blo 424774 2309705 := bstep (se 2 (by rfl) ⟨866139, by rfl⟩ : syracuseStep 2309705 = 1732279) B1732279
theorem B1820063 : Blo 424774 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1826813 : Blo 424774 1826813 := bstep (se 3 (by rfl) ⟨342527, by rfl⟩ : syracuseStep 1826813 = 685055) B685055
theorem B2154923 : Blo 424774 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B16807247 : Blo 424774 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B1080479 : Blo 424774 1080479 := bstep (se 1 (by rfl) ⟨810359, by rfl⟩ : syracuseStep 1080479 = 1620719) B1620719
theorem B8748479 : Blo 424774 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B1213375 : Blo 424774 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B1217875 : Blo 424774 1217875 := bstep (se 1 (by rfl) ⟨913406, by rfl⟩ : syracuseStep 1217875 = 1826813) B1826813
theorem B2933455 : Blo 424774 2933455 := bstep (se 1 (by rfl) ⟨2200091, by rfl⟩ : syracuseStep 2933455 = 4400183) B4400183
theorem B7260839 : Blo 424774 7260839 := bstep (se 1 (by rfl) ⟨5445629, by rfl⟩ : syracuseStep 7260839 = 10891259) B10891259
theorem B7755547 : Blo 424774 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B1436615 : Blo 424774 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B11204831 : Blo 424774 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B720319 : Blo 424774 720319 := bstep (se 1 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 720319 = 1080479) B1080479
theorem B5832319 : Blo 424774 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B1539803 : Blo 424774 1539803 := bstep (se 1 (by rfl) ⟨1154852, by rfl⟩ : syracuseStep 1539803 = 2309705) B2309705
theorem B957743 : Blo 424774 957743 := bstep (se 1 (by rfl) ⟨718307, by rfl⟩ : syracuseStep 957743 = 1436615) B1436615
theorem B960425 : Blo 424774 960425 := bstep (se 2 (by rfl) ⟨360159, by rfl⟩ : syracuseStep 960425 = 720319) B720319
theorem B7776425 : Blo 424774 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B1026535 : Blo 424774 1026535 := bstep (se 1 (by rfl) ⟨769901, by rfl⟩ : syracuseStep 1026535 = 1539803) B1539803
theorem B3911273 : Blo 424774 3911273 := bstep (se 2 (by rfl) ⟨1466727, by rfl⟩ : syracuseStep 3911273 = 2933455) B2933455
theorem B1617833 : Blo 424774 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B1623833 : Blo 424774 1623833 := bstep (se 2 (by rfl) ⟨608937, by rfl⟩ : syracuseStep 1623833 = 1217875) B1217875
theorem B10340729 : Blo 424774 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B4840559 : Blo 424774 4840559 := bstep (se 1 (by rfl) ⟨3630419, by rfl⟩ : syracuseStep 4840559 = 7260839) B7260839
theorem B7469887 : Blo 424774 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B1082555 : Blo 424774 1082555 := bstep (se 1 (by rfl) ⟨811916, by rfl⟩ : syracuseStep 1082555 = 1623833) B1623833
theorem B5184283 : Blo 424774 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B6893819 : Blo 424774 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B3227039 : Blo 424774 3227039 := bstep (se 1 (by rfl) ⟨2420279, by rfl⟩ : syracuseStep 3227039 = 4840559) B4840559
theorem B638495 : Blo 424774 638495 := bstep (se 1 (by rfl) ⟨478871, by rfl⟩ : syracuseStep 638495 = 957743) B957743
theorem B640283 : Blo 424774 640283 := bstep (se 1 (by rfl) ⟨480212, by rfl⟩ : syracuseStep 640283 = 960425) B960425
theorem B2607515 : Blo 424774 2607515 := bstep (se 1 (by rfl) ⟨1955636, by rfl⟩ : syracuseStep 2607515 = 3911273) B3911273
theorem B1368713 : Blo 424774 1368713 := bstep (se 2 (by rfl) ⟨513267, by rfl⟩ : syracuseStep 1368713 = 1026535) B1026535
theorem B1078555 : Blo 424774 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B9959849 : Blo 424774 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B721703 : Blo 424774 721703 := bstep (se 1 (by rfl) ⟨541277, by rfl⟩ : syracuseStep 721703 = 1082555) B1082555
theorem B426855 : Blo 424774 426855 := bstep (se 1 (by rfl) ⟨320141, by rfl⟩ : syracuseStep 426855 = 640283) B640283
theorem B1738343 : Blo 424774 1738343 := bstep (se 1 (by rfl) ⟨1303757, by rfl⟩ : syracuseStep 1738343 = 2607515) B2607515
theorem B4595879 : Blo 424774 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B6639899 : Blo 424774 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B2151359 : Blo 424774 2151359 := bstep (se 1 (by rfl) ⟨1613519, by rfl⟩ : syracuseStep 2151359 = 3227039) B3227039
theorem B912475 : Blo 424774 912475 := bstep (se 1 (by rfl) ⟨684356, by rfl⟩ : syracuseStep 912475 = 1368713) B1368713
theorem B1438073 : Blo 424774 1438073 := bstep (se 2 (by rfl) ⟨539277, by rfl⟩ : syracuseStep 1438073 = 1078555) B1078555
theorem B6912377 : Blo 424774 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B425663 : Blo 424774 425663 := bstep (se 1 (by rfl) ⟨319247, by rfl⟩ : syracuseStep 425663 = 638495) B638495
theorem B1216633 : Blo 424774 1216633 := bstep (se 2 (by rfl) ⟨456237, by rfl⟩ : syracuseStep 1216633 = 912475) B912475
theorem B958715 : Blo 424774 958715 := bstep (se 1 (by rfl) ⟨719036, by rfl⟩ : syracuseStep 958715 = 1438073) B1438073
theorem B17706397 : Blo 424774 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B1158895 : Blo 424774 1158895 := bstep (se 1 (by rfl) ⟨869171, by rfl⟩ : syracuseStep 1158895 = 1738343) B1738343
theorem B3063919 : Blo 424774 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B4608251 : Blo 424774 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B481135 : Blo 424774 481135 := bstep (se 1 (by rfl) ⟨360851, by rfl⟩ : syracuseStep 481135 = 721703) B721703
theorem B1434239 : Blo 424774 1434239 := bstep (se 1 (by rfl) ⟨1075679, by rfl⟩ : syracuseStep 1434239 = 2151359) B2151359
theorem B1545193 : Blo 424774 1545193 := bstep (se 2 (by rfl) ⟨579447, by rfl⟩ : syracuseStep 1545193 = 1158895) B1158895
theorem B956159 : Blo 424774 956159 := bstep (se 1 (by rfl) ⟨717119, by rfl⟩ : syracuseStep 956159 = 1434239) B1434239
theorem B23608529 : Blo 424774 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B1622177 : Blo 424774 1622177 := bstep (se 2 (by rfl) ⟨608316, by rfl⟩ : syracuseStep 1622177 = 1216633) B1216633
theorem B639143 : Blo 424774 639143 := bstep (se 1 (by rfl) ⟨479357, by rfl⟩ : syracuseStep 639143 = 958715) B958715
theorem B641513 : Blo 424774 641513 := bstep (se 2 (by rfl) ⟨240567, by rfl⟩ : syracuseStep 641513 = 481135) B481135
theorem B4085225 : Blo 424774 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B3072167 : Blo 424774 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B1081451 : Blo 424774 1081451 := bstep (se 1 (by rfl) ⟨811088, by rfl⟩ : syracuseStep 1081451 = 1622177) B1622177
theorem B426095 : Blo 424774 426095 := bstep (se 1 (by rfl) ⟨319571, by rfl⟩ : syracuseStep 426095 = 639143) B639143
theorem B427675 : Blo 424774 427675 := bstep (se 1 (by rfl) ⟨320756, by rfl⟩ : syracuseStep 427675 = 641513) B641513
theorem B2723483 : Blo 424774 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B15739019 : Blo 424774 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B637439 : Blo 424774 637439 := bstep (se 1 (by rfl) ⟨478079, by rfl⟩ : syracuseStep 637439 = 956159) B956159
theorem B2048111 : Blo 424774 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B2060257 : Blo 424774 2060257 := bstep (se 2 (by rfl) ⟨772596, by rfl⟩ : syracuseStep 2060257 = 1545193) B1545193
theorem B720967 : Blo 424774 720967 := bstep (se 1 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 720967 = 1081451) B1081451
theorem B10492679 : Blo 424774 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B1815655 : Blo 424774 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1365407 : Blo 424774 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111
theorem B2747009 : Blo 424774 2747009 := bstep (se 2 (by rfl) ⟨1030128, by rfl⟩ : syracuseStep 2747009 = 2060257) B2060257
theorem B424959 : Blo 424774 424959 := bstep (se 1 (by rfl) ⟨318719, by rfl⟩ : syracuseStep 424959 = 637439) B637439
theorem B961289 : Blo 424774 961289 := bstep (se 2 (by rfl) ⟨360483, by rfl⟩ : syracuseStep 961289 = 720967) B720967
theorem B6995119 : Blo 424774 6995119 := bstep (se 1 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 6995119 = 10492679) B10492679
theorem B910271 : Blo 424774 910271 := bstep (se 1 (by rfl) ⟨682703, by rfl⟩ : syracuseStep 910271 = 1365407) B1365407
theorem B2420873 : Blo 424774 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1831339 : Blo 424774 1831339 := bstep (se 1 (by rfl) ⟨1373504, by rfl⟩ : syracuseStep 1831339 = 2747009) B2747009
theorem B1613915 : Blo 424774 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B2441785 : Blo 424774 2441785 := bstep (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) B1831339
theorem B606847 : Blo 424774 606847 := bstep (se 1 (by rfl) ⟨455135, by rfl⟩ : syracuseStep 606847 = 910271) B910271
theorem B640859 : Blo 424774 640859 := bstep (se 1 (by rfl) ⟨480644, by rfl⟩ : syracuseStep 640859 = 961289) B961289
theorem B9326825 : Blo 424774 9326825 := bstep (se 2 (by rfl) ⟨3497559, by rfl⟩ : syracuseStep 9326825 = 6995119) B6995119
theorem B427239 : Blo 424774 427239 := bstep (se 1 (by rfl) ⟨320429, by rfl⟩ : syracuseStep 427239 = 640859) B640859
theorem B3255713 : Blo 424774 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B809129 : Blo 424774 809129 := bstep (se 2 (by rfl) ⟨303423, by rfl⟩ : syracuseStep 809129 = 606847) B606847
theorem B6217883 : Blo 424774 6217883 := bstep (se 1 (by rfl) ⟨4663412, by rfl⟩ : syracuseStep 6217883 = 9326825) B9326825
theorem B1075943 : Blo 424774 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B2170475 : Blo 424774 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B4145255 : Blo 424774 4145255 := bstep (se 1 (by rfl) ⟨3108941, by rfl⟩ : syracuseStep 4145255 = 6217883) B6217883
theorem B2157677 : Blo 424774 2157677 := bstep (se 3 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 2157677 = 809129) B809129
theorem B717295 : Blo 424774 717295 := bstep (se 1 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 717295 = 1075943) B1075943
theorem B1446983 : Blo 424774 1446983 := bstep (se 1 (by rfl) ⟨1085237, by rfl⟩ : syracuseStep 1446983 = 2170475) B2170475
theorem B956393 : Blo 424774 956393 := bstep (se 2 (by rfl) ⟨358647, by rfl⟩ : syracuseStep 956393 = 717295) B717295
theorem B2763503 : Blo 424774 2763503 := bstep (se 1 (by rfl) ⟨2072627, by rfl⟩ : syracuseStep 2763503 = 4145255) B4145255
theorem B1438451 : Blo 424774 1438451 := bstep (se 1 (by rfl) ⟨1078838, by rfl⟩ : syracuseStep 1438451 = 2157677) B2157677
theorem B1842335 : Blo 424774 1842335 := bstep (se 1 (by rfl) ⟨1381751, by rfl⟩ : syracuseStep 1842335 = 2763503) B2763503
theorem B958967 : Blo 424774 958967 := bstep (se 1 (by rfl) ⟨719225, by rfl⟩ : syracuseStep 958967 = 1438451) B1438451
theorem B964655 : Blo 424774 964655 := bstep (se 1 (by rfl) ⟨723491, by rfl⟩ : syracuseStep 964655 = 1446983) B1446983
theorem B637595 : Blo 424774 637595 := bstep (se 1 (by rfl) ⟨478196, by rfl⟩ : syracuseStep 637595 = 956393) B956393
theorem B1228223 : Blo 424774 1228223 := bstep (se 1 (by rfl) ⟨921167, by rfl⟩ : syracuseStep 1228223 = 1842335) B1842335
theorem B639311 : Blo 424774 639311 := bstep (se 1 (by rfl) ⟨479483, by rfl⟩ : syracuseStep 639311 = 958967) B958967
theorem B643103 : Blo 424774 643103 := bstep (se 1 (by rfl) ⟨482327, by rfl⟩ : syracuseStep 643103 = 964655) B964655
theorem B425063 : Blo 424774 425063 := bstep (se 1 (by rfl) ⟨318797, by rfl⟩ : syracuseStep 425063 = 637595) B637595
theorem B426207 : Blo 424774 426207 := bstep (se 1 (by rfl) ⟨319655, by rfl⟩ : syracuseStep 426207 = 639311) B639311
theorem B428735 : Blo 424774 428735 := bstep (se 1 (by rfl) ⟨321551, by rfl⟩ : syracuseStep 428735 = 643103) B643103
theorem B3275261 : Blo 424774 3275261 := bstep (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) B1228223
theorem B2183507 : Blo 424774 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B1455671 : Blo 424774 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B3881789 : Blo 424774 3881789 := bstep (se 3 (by rfl) ⟨727835, by rfl⟩ : syracuseStep 3881789 = 1455671) B1455671
theorem B2587859 : Blo 424774 2587859 := bstep (se 1 (by rfl) ⟨1940894, by rfl⟩ : syracuseStep 2587859 = 3881789) B3881789
theorem B1725239 : Blo 424774 1725239 := bstep (se 1 (by rfl) ⟨1293929, by rfl⟩ : syracuseStep 1725239 = 2587859) B2587859
theorem B4600637 : Blo 424774 4600637 := bstep (se 3 (by rfl) ⟨862619, by rfl⟩ : syracuseStep 4600637 = 1725239) B1725239
theorem B3067091 : Blo 424774 3067091 := bstep (se 1 (by rfl) ⟨2300318, by rfl⟩ : syracuseStep 3067091 = 4600637) B4600637
theorem B2044727 : Blo 424774 2044727 := bstep (se 1 (by rfl) ⟨1533545, by rfl⟩ : syracuseStep 2044727 = 3067091) B3067091
theorem B1363151 : Blo 424774 1363151 := bstep (se 1 (by rfl) ⟨1022363, by rfl⟩ : syracuseStep 1363151 = 2044727) B2044727
theorem B908767 : Blo 424774 908767 := bstep (se 1 (by rfl) ⟨681575, by rfl⟩ : syracuseStep 908767 = 1363151) B1363151
theorem B1211689 : Blo 424774 1211689 := bstep (se 2 (by rfl) ⟨454383, by rfl⟩ : syracuseStep 1211689 = 908767) B908767
theorem B1615585 : Blo 424774 1615585 := bstep (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) B1211689
theorem B2154113 : Blo 424774 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B1436075 : Blo 424774 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B957383 : Blo 424774 957383 := bstep (se 1 (by rfl) ⟨718037, by rfl⟩ : syracuseStep 957383 = 1436075) B1436075
theorem B638255 : Blo 424774 638255 := bstep (se 1 (by rfl) ⟨478691, by rfl⟩ : syracuseStep 638255 = 957383) B957383
theorem B425503 : Blo 424774 425503 := bstep (se 1 (by rfl) ⟨319127, by rfl⟩ : syracuseStep 425503 = 638255) B638255

theorem C0 (j : ℕ) (h1 : 106193 ≤ j) (h2 : j ≤ 106892) : Blo 424774 (4 * j + 3) := by
  interval_cases j
  · exact B424775
  · exact B424779
  · exact B424783
  · exact B424787
  · exact B424791
  · exact B424795
  · exact B424799
  · exact B424803
  · exact B424807
  · exact B424811
  · exact B424815
  · exact B424819
  · exact B424823
  · exact B424827
  · exact B424831
  · exact B424835
  · exact B424839
  · exact B424843
  · exact B424847
  · exact B424851
  · exact B424855
  · exact B424859
  · exact B424863
  · exact B424867
  · exact B424871
  · exact B424875
  · exact B424879
  · exact B424883
  · exact B424887
  · exact B424891
  · exact B424895
  · exact B424899
  · exact B424903
  · exact B424907
  · exact B424911
  · exact B424915
  · exact B424919
  · exact B424923
  · exact B424927
  · exact B424931
  · exact B424935
  · exact B424939
  · exact B424943
  · exact B424947
  · exact B424951
  · exact B424955
  · exact B424959
  · exact B424963
  · exact B424967
  · exact B424971
  · exact B424975
  · exact B424979
  · exact B424983
  · exact B424987
  · exact B424991
  · exact B424995
  · exact B424999
  · exact B425003
  · exact B425007
  · exact B425011
  · exact B425015
  · exact B425019
  · exact B425023
  · exact B425027
  · exact B425031
  · exact B425035
  · exact B425039
  · exact B425043
  · exact B425047
  · exact B425051
  · exact B425055
  · exact B425059
  · exact B425063
  · exact B425067
  · exact B425071
  · exact B425075
  · exact B425079
  · exact B425083
  · exact B425087
  · exact B425091
  · exact B425095
  · exact B425099
  · exact B425103
  · exact B425107
  · exact B425111
  · exact B425115
  · exact B425119
  · exact B425123
  · exact B425127
  · exact B425131
  · exact B425135
  · exact B425139
  · exact B425143
  · exact B425147
  · exact B425151
  · exact B425155
  · exact B425159
  · exact B425163
  · exact B425167
  · exact B425171
  · exact B425175
  · exact B425179
  · exact B425183
  · exact B425187
  · exact B425191
  · exact B425195
  · exact B425199
  · exact B425203
  · exact B425207
  · exact B425211
  · exact B425215
  · exact B425219
  · exact B425223
  · exact B425227
  · exact B425231
  · exact B425235
  · exact B425239
  · exact B425243
  · exact B425247
  · exact B425251
  · exact B425255
  · exact B425259
  · exact B425263
  · exact B425267
  · exact B425271
  · exact B425275
  · exact B425279
  · exact B425283
  · exact B425287
  · exact B425291
  · exact B425295
  · exact B425299
  · exact B425303
  · exact B425307
  · exact B425311
  · exact B425315
  · exact B425319
  · exact B425323
  · exact B425327
  · exact B425331
  · exact B425335
  · exact B425339
  · exact B425343
  · exact B425347
  · exact B425351
  · exact B425355
  · exact B425359
  · exact B425363
  · exact B425367
  · exact B425371
  · exact B425375
  · exact B425379
  · exact B425383
  · exact B425387
  · exact B425391
  · exact B425395
  · exact B425399
  · exact B425403
  · exact B425407
  · exact B425411
  · exact B425415
  · exact B425419
  · exact B425423
  · exact B425427
  · exact B425431
  · exact B425435
  · exact B425439
  · exact B425443
  · exact B425447
  · exact B425451
  · exact B425455
  · exact B425459
  · exact B425463
  · exact B425467
  · exact B425471
  · exact B425475
  · exact B425479
  · exact B425483
  · exact B425487
  · exact B425491
  · exact B425495
  · exact B425499
  · exact B425503
  · exact B425507
  · exact B425511
  · exact B425515
  · exact B425519
  · exact B425523
  · exact B425527
  · exact B425531
  · exact B425535
  · exact B425539
  · exact B425543
  · exact B425547
  · exact B425551
  · exact B425555
  · exact B425559
  · exact B425563
  · exact B425567
  · exact B425571
  · exact B425575
  · exact B425579
  · exact B425583
  · exact B425587
  · exact B425591
  · exact B425595
  · exact B425599
  · exact B425603
  · exact B425607
  · exact B425611
  · exact B425615
  · exact B425619
  · exact B425623
  · exact B425627
  · exact B425631
  · exact B425635
  · exact B425639
  · exact B425643
  · exact B425647
  · exact B425651
  · exact B425655
  · exact B425659
  · exact B425663
  · exact B425667
  · exact B425671
  · exact B425675
  · exact B425679
  · exact B425683
  · exact B425687
  · exact B425691
  · exact B425695
  · exact B425699
  · exact B425703
  · exact B425707
  · exact B425711
  · exact B425715
  · exact B425719
  · exact B425723
  · exact B425727
  · exact B425731
  · exact B425735
  · exact B425739
  · exact B425743
  · exact B425747
  · exact B425751
  · exact B425755
  · exact B425759
  · exact B425763
  · exact B425767
  · exact B425771
  · exact B425775
  · exact B425779
  · exact B425783
  · exact B425787
  · exact B425791
  · exact B425795
  · exact B425799
  · exact B425803
  · exact B425807
  · exact B425811
  · exact B425815
  · exact B425819
  · exact B425823
  · exact B425827
  · exact B425831
  · exact B425835
  · exact B425839
  · exact B425843
  · exact B425847
  · exact B425851
  · exact B425855
  · exact B425859
  · exact B425863
  · exact B425867
  · exact B425871
  · exact B425875
  · exact B425879
  · exact B425883
  · exact B425887
  · exact B425891
  · exact B425895
  · exact B425899
  · exact B425903
  · exact B425907
  · exact B425911
  · exact B425915
  · exact B425919
  · exact B425923
  · exact B425927
  · exact B425931
  · exact B425935
  · exact B425939
  · exact B425943
  · exact B425947
  · exact B425951
  · exact B425955
  · exact B425959
  · exact B425963
  · exact B425967
  · exact B425971
  · exact B425975
  · exact B425979
  · exact B425983
  · exact B425987
  · exact B425991
  · exact B425995
  · exact B425999
  · exact B426003
  · exact B426007
  · exact B426011
  · exact B426015
  · exact B426019
  · exact B426023
  · exact B426027
  · exact B426031
  · exact B426035
  · exact B426039
  · exact B426043
  · exact B426047
  · exact B426051
  · exact B426055
  · exact B426059
  · exact B426063
  · exact B426067
  · exact B426071
  · exact B426075
  · exact B426079
  · exact B426083
  · exact B426087
  · exact B426091
  · exact B426095
  · exact B426099
  · exact B426103
  · exact B426107
  · exact B426111
  · exact B426115
  · exact B426119
  · exact B426123
  · exact B426127
  · exact B426131
  · exact B426135
  · exact B426139
  · exact B426143
  · exact B426147
  · exact B426151
  · exact B426155
  · exact B426159
  · exact B426163
  · exact B426167
  · exact B426171
  · exact B426175
  · exact B426179
  · exact B426183
  · exact B426187
  · exact B426191
  · exact B426195
  · exact B426199
  · exact B426203
  · exact B426207
  · exact B426211
  · exact B426215
  · exact B426219
  · exact B426223
  · exact B426227
  · exact B426231
  · exact B426235
  · exact B426239
  · exact B426243
  · exact B426247
  · exact B426251
  · exact B426255
  · exact B426259
  · exact B426263
  · exact B426267
  · exact B426271
  · exact B426275
  · exact B426279
  · exact B426283
  · exact B426287
  · exact B426291
  · exact B426295
  · exact B426299
  · exact B426303
  · exact B426307
  · exact B426311
  · exact B426315
  · exact B426319
  · exact B426323
  · exact B426327
  · exact B426331
  · exact B426335
  · exact B426339
  · exact B426343
  · exact B426347
  · exact B426351
  · exact B426355
  · exact B426359
  · exact B426363
  · exact B426367
  · exact B426371
  · exact B426375
  · exact B426379
  · exact B426383
  · exact B426387
  · exact B426391
  · exact B426395
  · exact B426399
  · exact B426403
  · exact B426407
  · exact B426411
  · exact B426415
  · exact B426419
  · exact B426423
  · exact B426427
  · exact B426431
  · exact B426435
  · exact B426439
  · exact B426443
  · exact B426447
  · exact B426451
  · exact B426455
  · exact B426459
  · exact B426463
  · exact B426467
  · exact B426471
  · exact B426475
  · exact B426479
  · exact B426483
  · exact B426487
  · exact B426491
  · exact B426495
  · exact B426499
  · exact B426503
  · exact B426507
  · exact B426511
  · exact B426515
  · exact B426519
  · exact B426523
  · exact B426527
  · exact B426531
  · exact B426535
  · exact B426539
  · exact B426543
  · exact B426547
  · exact B426551
  · exact B426555
  · exact B426559
  · exact B426563
  · exact B426567
  · exact B426571
  · exact B426575
  · exact B426579
  · exact B426583
  · exact B426587
  · exact B426591
  · exact B426595
  · exact B426599
  · exact B426603
  · exact B426607
  · exact B426611
  · exact B426615
  · exact B426619
  · exact B426623
  · exact B426627
  · exact B426631
  · exact B426635
  · exact B426639
  · exact B426643
  · exact B426647
  · exact B426651
  · exact B426655
  · exact B426659
  · exact B426663
  · exact B426667
  · exact B426671
  · exact B426675
  · exact B426679
  · exact B426683
  · exact B426687
  · exact B426691
  · exact B426695
  · exact B426699
  · exact B426703
  · exact B426707
  · exact B426711
  · exact B426715
  · exact B426719
  · exact B426723
  · exact B426727
  · exact B426731
  · exact B426735
  · exact B426739
  · exact B426743
  · exact B426747
  · exact B426751
  · exact B426755
  · exact B426759
  · exact B426763
  · exact B426767
  · exact B426771
  · exact B426775
  · exact B426779
  · exact B426783
  · exact B426787
  · exact B426791
  · exact B426795
  · exact B426799
  · exact B426803
  · exact B426807
  · exact B426811
  · exact B426815
  · exact B426819
  · exact B426823
  · exact B426827
  · exact B426831
  · exact B426835
  · exact B426839
  · exact B426843
  · exact B426847
  · exact B426851
  · exact B426855
  · exact B426859
  · exact B426863
  · exact B426867
  · exact B426871
  · exact B426875
  · exact B426879
  · exact B426883
  · exact B426887
  · exact B426891
  · exact B426895
  · exact B426899
  · exact B426903
  · exact B426907
  · exact B426911
  · exact B426915
  · exact B426919
  · exact B426923
  · exact B426927
  · exact B426931
  · exact B426935
  · exact B426939
  · exact B426943
  · exact B426947
  · exact B426951
  · exact B426955
  · exact B426959
  · exact B426963
  · exact B426967
  · exact B426971
  · exact B426975
  · exact B426979
  · exact B426983
  · exact B426987
  · exact B426991
  · exact B426995
  · exact B426999
  · exact B427003
  · exact B427007
  · exact B427011
  · exact B427015
  · exact B427019
  · exact B427023
  · exact B427027
  · exact B427031
  · exact B427035
  · exact B427039
  · exact B427043
  · exact B427047
  · exact B427051
  · exact B427055
  · exact B427059
  · exact B427063
  · exact B427067
  · exact B427071
  · exact B427075
  · exact B427079
  · exact B427083
  · exact B427087
  · exact B427091
  · exact B427095
  · exact B427099
  · exact B427103
  · exact B427107
  · exact B427111
  · exact B427115
  · exact B427119
  · exact B427123
  · exact B427127
  · exact B427131
  · exact B427135
  · exact B427139
  · exact B427143
  · exact B427147
  · exact B427151
  · exact B427155
  · exact B427159
  · exact B427163
  · exact B427167
  · exact B427171
  · exact B427175
  · exact B427179
  · exact B427183
  · exact B427187
  · exact B427191
  · exact B427195
  · exact B427199
  · exact B427203
  · exact B427207
  · exact B427211
  · exact B427215
  · exact B427219
  · exact B427223
  · exact B427227
  · exact B427231
  · exact B427235
  · exact B427239
  · exact B427243
  · exact B427247
  · exact B427251
  · exact B427255
  · exact B427259
  · exact B427263
  · exact B427267
  · exact B427271
  · exact B427275
  · exact B427279
  · exact B427283
  · exact B427287
  · exact B427291
  · exact B427295
  · exact B427299
  · exact B427303
  · exact B427307
  · exact B427311
  · exact B427315
  · exact B427319
  · exact B427323
  · exact B427327
  · exact B427331
  · exact B427335
  · exact B427339
  · exact B427343
  · exact B427347
  · exact B427351
  · exact B427355
  · exact B427359
  · exact B427363
  · exact B427367
  · exact B427371
  · exact B427375
  · exact B427379
  · exact B427383
  · exact B427387
  · exact B427391
  · exact B427395
  · exact B427399
  · exact B427403
  · exact B427407
  · exact B427411
  · exact B427415
  · exact B427419
  · exact B427423
  · exact B427427
  · exact B427431
  · exact B427435
  · exact B427439
  · exact B427443
  · exact B427447
  · exact B427451
  · exact B427455
  · exact B427459
  · exact B427463
  · exact B427467
  · exact B427471
  · exact B427475
  · exact B427479
  · exact B427483
  · exact B427487
  · exact B427491
  · exact B427495
  · exact B427499
  · exact B427503
  · exact B427507
  · exact B427511
  · exact B427515
  · exact B427519
  · exact B427523
  · exact B427527
  · exact B427531
  · exact B427535
  · exact B427539
  · exact B427543
  · exact B427547
  · exact B427551
  · exact B427555
  · exact B427559
  · exact B427563
  · exact B427567
  · exact B427571

theorem C1 (j : ℕ) (h1 : 106893 ≤ j) (h2 : j ≤ 107192) : Blo 424774 (4 * j + 3) := by
  interval_cases j
  · exact B427575
  · exact B427579
  · exact B427583
  · exact B427587
  · exact B427591
  · exact B427595
  · exact B427599
  · exact B427603
  · exact B427607
  · exact B427611
  · exact B427615
  · exact B427619
  · exact B427623
  · exact B427627
  · exact B427631
  · exact B427635
  · exact B427639
  · exact B427643
  · exact B427647
  · exact B427651
  · exact B427655
  · exact B427659
  · exact B427663
  · exact B427667
  · exact B427671
  · exact B427675
  · exact B427679
  · exact B427683
  · exact B427687
  · exact B427691
  · exact B427695
  · exact B427699
  · exact B427703
  · exact B427707
  · exact B427711
  · exact B427715
  · exact B427719
  · exact B427723
  · exact B427727
  · exact B427731
  · exact B427735
  · exact B427739
  · exact B427743
  · exact B427747
  · exact B427751
  · exact B427755
  · exact B427759
  · exact B427763
  · exact B427767
  · exact B427771
  · exact B427775
  · exact B427779
  · exact B427783
  · exact B427787
  · exact B427791
  · exact B427795
  · exact B427799
  · exact B427803
  · exact B427807
  · exact B427811
  · exact B427815
  · exact B427819
  · exact B427823
  · exact B427827
  · exact B427831
  · exact B427835
  · exact B427839
  · exact B427843
  · exact B427847
  · exact B427851
  · exact B427855
  · exact B427859
  · exact B427863
  · exact B427867
  · exact B427871
  · exact B427875
  · exact B427879
  · exact B427883
  · exact B427887
  · exact B427891
  · exact B427895
  · exact B427899
  · exact B427903
  · exact B427907
  · exact B427911
  · exact B427915
  · exact B427919
  · exact B427923
  · exact B427927
  · exact B427931
  · exact B427935
  · exact B427939
  · exact B427943
  · exact B427947
  · exact B427951
  · exact B427955
  · exact B427959
  · exact B427963
  · exact B427967
  · exact B427971
  · exact B427975
  · exact B427979
  · exact B427983
  · exact B427987
  · exact B427991
  · exact B427995
  · exact B427999
  · exact B428003
  · exact B428007
  · exact B428011
  · exact B428015
  · exact B428019
  · exact B428023
  · exact B428027
  · exact B428031
  · exact B428035
  · exact B428039
  · exact B428043
  · exact B428047
  · exact B428051
  · exact B428055
  · exact B428059
  · exact B428063
  · exact B428067
  · exact B428071
  · exact B428075
  · exact B428079
  · exact B428083
  · exact B428087
  · exact B428091
  · exact B428095
  · exact B428099
  · exact B428103
  · exact B428107
  · exact B428111
  · exact B428115
  · exact B428119
  · exact B428123
  · exact B428127
  · exact B428131
  · exact B428135
  · exact B428139
  · exact B428143
  · exact B428147
  · exact B428151
  · exact B428155
  · exact B428159
  · exact B428163
  · exact B428167
  · exact B428171
  · exact B428175
  · exact B428179
  · exact B428183
  · exact B428187
  · exact B428191
  · exact B428195
  · exact B428199
  · exact B428203
  · exact B428207
  · exact B428211
  · exact B428215
  · exact B428219
  · exact B428223
  · exact B428227
  · exact B428231
  · exact B428235
  · exact B428239
  · exact B428243
  · exact B428247
  · exact B428251
  · exact B428255
  · exact B428259
  · exact B428263
  · exact B428267
  · exact B428271
  · exact B428275
  · exact B428279
  · exact B428283
  · exact B428287
  · exact B428291
  · exact B428295
  · exact B428299
  · exact B428303
  · exact B428307
  · exact B428311
  · exact B428315
  · exact B428319
  · exact B428323
  · exact B428327
  · exact B428331
  · exact B428335
  · exact B428339
  · exact B428343
  · exact B428347
  · exact B428351
  · exact B428355
  · exact B428359
  · exact B428363
  · exact B428367
  · exact B428371
  · exact B428375
  · exact B428379
  · exact B428383
  · exact B428387
  · exact B428391
  · exact B428395
  · exact B428399
  · exact B428403
  · exact B428407
  · exact B428411
  · exact B428415
  · exact B428419
  · exact B428423
  · exact B428427
  · exact B428431
  · exact B428435
  · exact B428439
  · exact B428443
  · exact B428447
  · exact B428451
  · exact B428455
  · exact B428459
  · exact B428463
  · exact B428467
  · exact B428471
  · exact B428475
  · exact B428479
  · exact B428483
  · exact B428487
  · exact B428491
  · exact B428495
  · exact B428499
  · exact B428503
  · exact B428507
  · exact B428511
  · exact B428515
  · exact B428519
  · exact B428523
  · exact B428527
  · exact B428531
  · exact B428535
  · exact B428539
  · exact B428543
  · exact B428547
  · exact B428551
  · exact B428555
  · exact B428559
  · exact B428563
  · exact B428567
  · exact B428571
  · exact B428575
  · exact B428579
  · exact B428583
  · exact B428587
  · exact B428591
  · exact B428595
  · exact B428599
  · exact B428603
  · exact B428607
  · exact B428611
  · exact B428615
  · exact B428619
  · exact B428623
  · exact B428627
  · exact B428631
  · exact B428635
  · exact B428639
  · exact B428643
  · exact B428647
  · exact B428651
  · exact B428655
  · exact B428659
  · exact B428663
  · exact B428667
  · exact B428671
  · exact B428675
  · exact B428679
  · exact B428683
  · exact B428687
  · exact B428691
  · exact B428695
  · exact B428699
  · exact B428703
  · exact B428707
  · exact B428711
  · exact B428715
  · exact B428719
  · exact B428723
  · exact B428727
  · exact B428731
  · exact B428735
  · exact B428739
  · exact B428743
  · exact B428747
  · exact B428751
  · exact B428755
  · exact B428759
  · exact B428763
  · exact B428767
  · exact B428771

theorem solution (m : ℕ) (hlo : 424774 ≤ m) (hhi : m ≤ 428774) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 106193 ≤ j := by omega
    have hj2 : j ≤ 107192 := by omega
    have hb : Blo 424774 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 106893 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
