-- Prove2me | solution 1 for syracuse_descends_range_1508951_1510951
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:08.154211+00:00
-- url     : https://prove2.me/submissions/6b37b7b9-970c-4d78-addd-ad688e8158c6

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


theorem B2547733 : Blo 1508951 2547733 := bbase (se 6 (by rfl) ⟨59712, by rfl⟩ : syracuseStep 2547733 = 119425) (by norm_num)
theorem B5734421 : Blo 1508951 5734421 := bbase (se 6 (by rfl) ⟨134400, by rfl⟩ : syracuseStep 5734421 = 268801) (by norm_num)
theorem B8601653 : Blo 1508951 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B5095493 : Blo 1508951 5095493 := bbase (se 4 (by rfl) ⟨477702, by rfl⟩ : syracuseStep 5095493 = 955405) (by norm_num)
theorem B4358213 : Blo 1508951 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B2547821 : Blo 1508951 2547821 := bbase (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) (by norm_num)
theorem B2867309 : Blo 1508951 2867309 := bbase (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) (by norm_num)
theorem B4358261 : Blo 1508951 4358261 := bbase (se 5 (by rfl) ⟨204293, by rfl⟩ : syracuseStep 4358261 = 408587) (by norm_num)
theorem B7258261 : Blo 1508951 7258261 := bbase (se 6 (by rfl) ⟨170115, by rfl⟩ : syracuseStep 7258261 = 340231) (by norm_num)
theorem B2547949 : Blo 1508951 2547949 := bbase (se 3 (by rfl) ⟨477740, by rfl⟩ : syracuseStep 2547949 = 955481) (by norm_num)
theorem B27541781 : Blo 1508951 27541781 := bbase (se 6 (by rfl) ⟨645510, by rfl⟩ : syracuseStep 27541781 = 1291021) (by norm_num)
theorem B4079909 : Blo 1508951 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B6447397 : Blo 1508951 6447397 := bbase (se 4 (by rfl) ⟨604443, by rfl⟩ : syracuseStep 6447397 = 1208887) (by norm_num)
theorem B6447413 : Blo 1508951 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B5734709 : Blo 1508951 5734709 := bbase (se 5 (by rfl) ⟨268814, by rfl⟩ : syracuseStep 5734709 = 537629) (by norm_num)
theorem B2548037 : Blo 1508951 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B4301237 : Blo 1508951 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B2548165 : Blo 1508951 2548165 := bbase (se 4 (by rfl) ⟨238890, by rfl⟩ : syracuseStep 2548165 = 477781) (by norm_num)
theorem B5095925 : Blo 1508951 5095925 := bbase (se 5 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 5095925 = 477743) (by norm_num)
theorem B2548253 : Blo 1508951 2548253 := bbase (se 3 (by rfl) ⟨477797, by rfl⟩ : syracuseStep 2548253 = 955595) (by norm_num)
theorem B8168053 : Blo 1508951 8168053 := bbase (se 5 (by rfl) ⟨382877, by rfl⟩ : syracuseStep 8168053 = 765755) (by norm_num)
theorem B2417293 : Blo 1508951 2417293 := bbase (se 3 (by rfl) ⟨453242, by rfl⟩ : syracuseStep 2417293 = 906485) (by norm_num)
theorem B2548381 : Blo 1508951 2548381 := bbase (se 3 (by rfl) ⟨477821, by rfl⟩ : syracuseStep 2548381 = 955643) (by norm_num)
theorem B2548469 : Blo 1508951 2548469 := bbase (se 5 (by rfl) ⟨119459, by rfl⟩ : syracuseStep 2548469 = 238919) (by norm_num)
theorem B11027285 : Blo 1508951 11027285 := bbase (se 9 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 11027285 = 64613) (by norm_num)
theorem B2868061 : Blo 1508951 2868061 := bbase (se 3 (by rfl) ⟨537761, by rfl⟩ : syracuseStep 2868061 = 1075523) (by norm_num)
theorem B2548597 : Blo 1508951 2548597 := bbase (se 5 (by rfl) ⟨119465, by rfl⟩ : syracuseStep 2548597 = 238931) (by norm_num)
theorem B5096357 : Blo 1508951 5096357 := bbase (se 4 (by rfl) ⟨477783, by rfl⟩ : syracuseStep 5096357 = 955567) (by norm_num)
theorem B2548685 : Blo 1508951 2548685 := bbase (se 3 (by rfl) ⟨477878, by rfl⟩ : syracuseStep 2548685 = 955757) (by norm_num)
theorem B6202325 : Blo 1508951 6202325 := bbase (se 7 (by rfl) ⟨72683, by rfl⟩ : syracuseStep 6202325 = 145367) (by norm_num)
theorem B9675733 : Blo 1508951 9675733 := bbase (se 7 (by rfl) ⟨113387, by rfl⟩ : syracuseStep 9675733 = 226775) (by norm_num)
theorem B3441629 : Blo 1508951 3441629 := bbase (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) (by norm_num)
theorem B3630053 : Blo 1508951 3630053 := bbase (se 4 (by rfl) ⟨340317, by rfl⟩ : syracuseStep 3630053 = 680635) (by norm_num)
theorem B2868205 : Blo 1508951 2868205 := bbase (se 3 (by rfl) ⟨537788, by rfl⟩ : syracuseStep 2868205 = 1075577) (by norm_num)
theorem B2327549 : Blo 1508951 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B2294821 : Blo 1508951 2294821 := bbase (se 4 (by rfl) ⟨215139, by rfl⟩ : syracuseStep 2294821 = 430279) (by norm_num)
theorem B1909813 : Blo 1508951 1909813 := bbase (se 5 (by rfl) ⟨89522, by rfl⟩ : syracuseStep 1909813 = 179045) (by norm_num)
theorem B4138037 : Blo 1508951 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B2548813 : Blo 1508951 2548813 := bbase (se 3 (by rfl) ⟨477902, by rfl⟩ : syracuseStep 2548813 = 955805) (by norm_num)
theorem B7644293 : Blo 1508951 7644293 := bbase (se 4 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 7644293 = 1433305) (by norm_num)
theorem B2868365 : Blo 1508951 2868365 := bbase (se 3 (by rfl) ⟨537818, by rfl⟩ : syracuseStep 2868365 = 1075637) (by norm_num)
theorem B1721489 : Blo 1508951 1721489 := bbase (se 2 (by rfl) ⟨645558, by rfl⟩ : syracuseStep 1721489 = 1291117) (by norm_num)
theorem B1909909 : Blo 1508951 1909909 := bbase (se 6 (by rfl) ⟨44763, by rfl⟩ : syracuseStep 1909909 = 89527) (by norm_num)
theorem B2040997 : Blo 1508951 2040997 := bbase (se 4 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 2040997 = 382687) (by norm_num)
theorem B2548901 : Blo 1508951 2548901 := bbase (se 4 (by rfl) ⟨238959, by rfl⟩ : syracuseStep 2548901 = 477919) (by norm_num)
theorem B2417845 : Blo 1508951 2417845 := bbase (se 5 (by rfl) ⟨113336, by rfl⟩ : syracuseStep 2417845 = 226673) (by norm_num)
theorem B3269837 : Blo 1508951 3269837 := bbase (se 3 (by rfl) ⟨613094, by rfl⟩ : syracuseStep 3269837 = 1226189) (by norm_num)
theorem B3679445 : Blo 1508951 3679445 := bbase (se 7 (by rfl) ⟨43118, by rfl⟩ : syracuseStep 3679445 = 86237) (by norm_num)
theorem B2549029 : Blo 1508951 2549029 := bbase (se 4 (by rfl) ⟨238971, by rfl⟩ : syracuseStep 2549029 = 477943) (by norm_num)
theorem B1910081 : Blo 1508951 1910081 := bbase (se 2 (by rfl) ⟨716280, by rfl⟩ : syracuseStep 1910081 = 1432561) (by norm_num)
theorem B2295125 : Blo 1508951 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B5096789 : Blo 1508951 5096789 := bbase (se 12 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 5096789 = 3733) (by norm_num)
theorem B1910137 : Blo 1508951 1910137 := bbase (se 2 (by rfl) ⟨716301, by rfl⟩ : syracuseStep 1910137 = 1432603) (by norm_num)
theorem B2549117 : Blo 1508951 2549117 := bbase (se 3 (by rfl) ⟨477959, by rfl⟩ : syracuseStep 2549117 = 955919) (by norm_num)
theorem B1721773 : Blo 1508951 1721773 := bbase (se 3 (by rfl) ⟨322832, by rfl⟩ : syracuseStep 1721773 = 645665) (by norm_num)
theorem B2418101 : Blo 1508951 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B5735893 : Blo 1508951 5735893 := bbase (se 7 (by rfl) ⟨67217, by rfl⟩ : syracuseStep 5735893 = 134435) (by norm_num)
theorem B1910233 : Blo 1508951 1910233 := bbase (se 2 (by rfl) ⟨716337, by rfl⟩ : syracuseStep 1910233 = 1432675) (by norm_num)
theorem B5514725 : Blo 1508951 5514725 := bbase (se 4 (by rfl) ⟨517005, by rfl⟩ : syracuseStep 5514725 = 1034011) (by norm_num)
theorem B2549245 : Blo 1508951 2549245 := bbase (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) (by norm_num)
theorem B3442213 : Blo 1508951 3442213 := bbase (se 4 (by rfl) ⟨322707, by rfl⟩ : syracuseStep 3442213 = 645415) (by norm_num)
theorem B2041381 : Blo 1508951 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B2549333 : Blo 1508951 2549333 := bbase (se 8 (by rfl) ⟨14937, by rfl⟩ : syracuseStep 2549333 = 29875) (by norm_num)
theorem B2983541 : Blo 1508951 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B1910405 : Blo 1508951 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B4834997 : Blo 1508951 4834997 := bbase (se 5 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 4834997 = 453281) (by norm_num)
theorem B14345909 : Blo 1508951 14345909 := bbase (se 5 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 14345909 = 1344929) (by norm_num)
theorem B1910461 : Blo 1508951 1910461 := bbase (se 3 (by rfl) ⟨358211, by rfl⟩ : syracuseStep 1910461 = 716423) (by norm_num)
theorem B2549461 : Blo 1508951 2549461 := bbase (se 7 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 2549461 = 59753) (by norm_num)
theorem B5097221 : Blo 1508951 5097221 := bbase (se 4 (by rfl) ⟨477864, by rfl⟩ : syracuseStep 5097221 = 955729) (by norm_num)
theorem B5736197 : Blo 1508951 5736197 := bbase (se 4 (by rfl) ⟨537768, by rfl⟩ : syracuseStep 5736197 = 1075537) (by norm_num)
theorem B1910557 : Blo 1508951 1910557 := bbase (se 3 (by rfl) ⟨358229, by rfl⟩ : syracuseStep 1910557 = 716459) (by norm_num)
theorem B2549549 : Blo 1508951 2549549 := bbase (se 3 (by rfl) ⟨478040, by rfl⟩ : syracuseStep 2549549 = 956081) (by norm_num)
theorem B1697593 : Blo 1508951 1697593 := bbase (se 2 (by rfl) ⟨636597, by rfl⟩ : syracuseStep 1697593 = 1273195) (by norm_num)
theorem B1697629 : Blo 1508951 1697629 := bbase (se 3 (by rfl) ⟨318305, by rfl⟩ : syracuseStep 1697629 = 636611) (by norm_num)
theorem B1697665 : Blo 1508951 1697665 := bbase (se 2 (by rfl) ⟨636624, by rfl⟩ : syracuseStep 1697665 = 1273249) (by norm_num)
theorem B1697701 : Blo 1508951 1697701 := bbase (se 4 (by rfl) ⟨159159, by rfl⟩ : syracuseStep 1697701 = 318319) (by norm_num)
theorem B2549677 : Blo 1508951 2549677 := bbase (se 3 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 2549677 = 956129) (by norm_num)
theorem B1697737 : Blo 1508951 1697737 := bbase (se 2 (by rfl) ⟨636651, by rfl⟩ : syracuseStep 1697737 = 1273303) (by norm_num)
theorem B1910729 : Blo 1508951 1910729 := bbase (se 2 (by rfl) ⟨716523, by rfl⟩ : syracuseStep 1910729 = 1433047) (by norm_num)
theorem B4900837 : Blo 1508951 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B1697773 : Blo 1508951 1697773 := bbase (se 3 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 1697773 = 636665) (by norm_num)
theorem B1722365 : Blo 1508951 1722365 := bbase (se 3 (by rfl) ⟨322943, by rfl⟩ : syracuseStep 1722365 = 645887) (by norm_num)
theorem B1910785 : Blo 1508951 1910785 := bbase (se 2 (by rfl) ⟨716544, by rfl⟩ : syracuseStep 1910785 = 1433089) (by norm_num)
theorem B1697809 : Blo 1508951 1697809 := bbase (se 2 (by rfl) ⟨636678, by rfl⟩ : syracuseStep 1697809 = 1273357) (by norm_num)
theorem B1697845 : Blo 1508951 1697845 := bbase (se 5 (by rfl) ⟨79586, by rfl⟩ : syracuseStep 1697845 = 159173) (by norm_num)
theorem B1697881 : Blo 1508951 1697881 := bbase (se 2 (by rfl) ⟨636705, by rfl⟩ : syracuseStep 1697881 = 1273411) (by norm_num)
theorem B1910881 : Blo 1508951 1910881 := bbase (se 2 (by rfl) ⟨716580, by rfl⟩ : syracuseStep 1910881 = 1433161) (by norm_num)
theorem B2418805 : Blo 1508951 2418805 := bbase (se 5 (by rfl) ⟨113381, by rfl⟩ : syracuseStep 2418805 = 226763) (by norm_num)
theorem B1697917 : Blo 1508951 1697917 := bbase (se 3 (by rfl) ⟨318359, by rfl⟩ : syracuseStep 1697917 = 636719) (by norm_num)
theorem B1697953 : Blo 1508951 1697953 := bbase (se 2 (by rfl) ⟨636732, by rfl⟩ : syracuseStep 1697953 = 1273465) (by norm_num)
theorem B1722529 : Blo 1508951 1722529 := bbase (se 2 (by rfl) ⟨645948, by rfl⟩ : syracuseStep 1722529 = 1291897) (by norm_num)
theorem B5097653 : Blo 1508951 5097653 := bbase (se 5 (by rfl) ⟨238952, by rfl⟩ : syracuseStep 5097653 = 477905) (by norm_num)
theorem B1697989 : Blo 1508951 1697989 := bbase (se 4 (by rfl) ⟨159186, by rfl⟩ : syracuseStep 1697989 = 318373) (by norm_num)
theorem B1698025 : Blo 1508951 1698025 := bbase (se 2 (by rfl) ⟨636759, by rfl⟩ : syracuseStep 1698025 = 1273519) (by norm_num)
theorem B3819757 : Blo 1508951 3819757 := bbase (se 3 (by rfl) ⟨716204, by rfl⟩ : syracuseStep 3819757 = 1432409) (by norm_num)
theorem B1698061 : Blo 1508951 1698061 := bbase (se 3 (by rfl) ⟨318386, by rfl⟩ : syracuseStep 1698061 = 636773) (by norm_num)
theorem B1911053 : Blo 1508951 1911053 := bbase (se 3 (by rfl) ⟨358322, by rfl⟩ : syracuseStep 1911053 = 716645) (by norm_num)
theorem B1698097 : Blo 1508951 1698097 := bbase (se 2 (by rfl) ⟨636786, by rfl⟩ : syracuseStep 1698097 = 1273573) (by norm_num)
theorem B2296117 : Blo 1508951 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B1812793 : Blo 1508951 1812793 := bbase (se 2 (by rfl) ⟨679797, by rfl⟩ : syracuseStep 1812793 = 1359595) (by norm_num)
theorem B1911109 : Blo 1508951 1911109 := bbase (se 4 (by rfl) ⟨179166, by rfl⟩ : syracuseStep 1911109 = 358333) (by norm_num)
theorem B1698133 : Blo 1508951 1698133 := bbase (se 10 (by rfl) ⟨2487, by rfl⟩ : syracuseStep 1698133 = 4975) (by norm_num)
theorem B3819869 : Blo 1508951 3819869 := bbase (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) (by norm_num)
theorem B9185653 : Blo 1508951 9185653 := bbase (se 5 (by rfl) ⟨430577, by rfl⟩ : syracuseStep 9185653 = 861155) (by norm_num)
theorem B1698169 : Blo 1508951 1698169 := bbase (se 2 (by rfl) ⟨636813, by rfl⟩ : syracuseStep 1698169 = 1273627) (by norm_num)
theorem B2263445 : Blo 1508951 2263445 := bbase (se 6 (by rfl) ⟨53049, by rfl⟩ : syracuseStep 2263445 = 106099) (by norm_num)
theorem B7645589 : Blo 1508951 7645589 := bbase (se 6 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 7645589 = 358387) (by norm_num)
theorem B1698205 : Blo 1508951 1698205 := bbase (se 3 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 1698205 = 636827) (by norm_num)
theorem B2148773 : Blo 1508951 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B1911205 : Blo 1508951 1911205 := bbase (se 4 (by rfl) ⟨179175, by rfl⟩ : syracuseStep 1911205 = 358351) (by norm_num)
theorem B2263469 : Blo 1508951 2263469 := bbase (se 3 (by rfl) ⟨424400, by rfl⟩ : syracuseStep 2263469 = 848801) (by norm_num)
theorem B1698241 : Blo 1508951 1698241 := bbase (se 2 (by rfl) ⟨636840, by rfl⟩ : syracuseStep 1698241 = 1273681) (by norm_num)
theorem B2263493 : Blo 1508951 2263493 := bbase (se 4 (by rfl) ⟨212202, by rfl⟩ : syracuseStep 2263493 = 424405) (by norm_num)
theorem B2263517 : Blo 1508951 2263517 := bbase (se 3 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 2263517 = 848819) (by norm_num)
theorem B1698277 : Blo 1508951 1698277 := bbase (se 4 (by rfl) ⟨159213, by rfl⟩ : syracuseStep 1698277 = 318427) (by norm_num)
theorem B2263541 : Blo 1508951 2263541 := bbase (se 5 (by rfl) ⟨106103, by rfl⟩ : syracuseStep 2263541 = 212207) (by norm_num)
theorem B6449669 : Blo 1508951 6449669 := bbase (se 4 (by rfl) ⟨604656, by rfl⟩ : syracuseStep 6449669 = 1209313) (by norm_num)
theorem B1698313 : Blo 1508951 1698313 := bbase (se 2 (by rfl) ⟨636867, by rfl⟩ : syracuseStep 1698313 = 1273735) (by norm_num)
theorem B2263565 : Blo 1508951 2263565 := bbase (se 3 (by rfl) ⟨424418, by rfl⟩ : syracuseStep 2263565 = 848837) (by norm_num)
theorem B3820061 : Blo 1508951 3820061 := bbase (se 3 (by rfl) ⟨716261, by rfl⟩ : syracuseStep 3820061 = 1432523) (by norm_num)
theorem B2419229 : Blo 1508951 2419229 := bbase (se 3 (by rfl) ⟨453605, by rfl⟩ : syracuseStep 2419229 = 907211) (by norm_num)
theorem B2263589 : Blo 1508951 2263589 := bbase (se 4 (by rfl) ⟨212211, by rfl⟩ : syracuseStep 2263589 = 424423) (by norm_num)
theorem B1698349 : Blo 1508951 1698349 := bbase (se 3 (by rfl) ⟨318440, by rfl⟩ : syracuseStep 1698349 = 636881) (by norm_num)
theorem B2263613 : Blo 1508951 2263613 := bbase (se 3 (by rfl) ⟨424427, by rfl⟩ : syracuseStep 2263613 = 848855) (by norm_num)
theorem B1698385 : Blo 1508951 1698385 := bbase (se 2 (by rfl) ⟨636894, by rfl⟩ : syracuseStep 1698385 = 1273789) (by norm_num)
theorem B1911377 : Blo 1508951 1911377 := bbase (se 2 (by rfl) ⟨716766, by rfl⟩ : syracuseStep 1911377 = 1433533) (by norm_num)
theorem B2263637 : Blo 1508951 2263637 := bbase (se 8 (by rfl) ⟨13263, by rfl⟩ : syracuseStep 2263637 = 26527) (by norm_num)
theorem B14510677 : Blo 1508951 14510677 := bbase (se 8 (by rfl) ⟨85023, by rfl⟩ : syracuseStep 14510677 = 170047) (by norm_num)
theorem B5098085 : Blo 1508951 5098085 := bbase (se 4 (by rfl) ⟨477945, by rfl⟩ : syracuseStep 5098085 = 955891) (by norm_num)
theorem B2263661 : Blo 1508951 2263661 := bbase (se 3 (by rfl) ⟨424436, by rfl⟩ : syracuseStep 2263661 = 848873) (by norm_num)
theorem B1698421 : Blo 1508951 1698421 := bbase (se 5 (by rfl) ⟨79613, by rfl⟩ : syracuseStep 1698421 = 159227) (by norm_num)
theorem B2263685 : Blo 1508951 2263685 := bbase (se 4 (by rfl) ⟨212220, by rfl⟩ : syracuseStep 2263685 = 424441) (by norm_num)
theorem B1911433 : Blo 1508951 1911433 := bbase (se 2 (by rfl) ⟨716787, by rfl⟩ : syracuseStep 1911433 = 1433575) (by norm_num)
theorem B1698457 : Blo 1508951 1698457 := bbase (se 2 (by rfl) ⟨636921, by rfl⟩ : syracuseStep 1698457 = 1273843) (by norm_num)
theorem B2263709 : Blo 1508951 2263709 := bbase (se 3 (by rfl) ⟨424445, by rfl⟩ : syracuseStep 2263709 = 848891) (by norm_num)
theorem B2263733 : Blo 1508951 2263733 := bbase (se 5 (by rfl) ⟨106112, by rfl⟩ : syracuseStep 2263733 = 212225) (by norm_num)
theorem B3443381 : Blo 1508951 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B1698493 : Blo 1508951 1698493 := bbase (se 3 (by rfl) ⟨318467, by rfl⟩ : syracuseStep 1698493 = 636935) (by norm_num)
theorem B2263757 : Blo 1508951 2263757 := bbase (se 3 (by rfl) ⟨424454, by rfl⟩ : syracuseStep 2263757 = 848909) (by norm_num)
theorem B12896981 : Blo 1508951 12896981 := bbase (se 7 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 12896981 = 302273) (by norm_num)
theorem B1698529 : Blo 1508951 1698529 := bbase (se 2 (by rfl) ⟨636948, by rfl⟩ : syracuseStep 1698529 = 1273897) (by norm_num)
theorem B2263781 : Blo 1508951 2263781 := bbase (se 4 (by rfl) ⟨212229, by rfl⟩ : syracuseStep 2263781 = 424459) (by norm_num)
theorem B1911529 : Blo 1508951 1911529 := bbase (se 2 (by rfl) ⟨716823, by rfl⟩ : syracuseStep 1911529 = 1433647) (by norm_num)
theorem B2263805 : Blo 1508951 2263805 := bbase (se 3 (by rfl) ⟨424463, by rfl⟩ : syracuseStep 2263805 = 848927) (by norm_num)
theorem B1698565 : Blo 1508951 1698565 := bbase (se 4 (by rfl) ⟨159240, by rfl⟩ : syracuseStep 1698565 = 318481) (by norm_num)
theorem B2263829 : Blo 1508951 2263829 := bbase (se 6 (by rfl) ⟨53058, by rfl⟩ : syracuseStep 2263829 = 106117) (by norm_num)
theorem B1698601 : Blo 1508951 1698601 := bbase (se 2 (by rfl) ⟨636975, by rfl⟩ : syracuseStep 1698601 = 1273951) (by norm_num)
theorem B2263853 : Blo 1508951 2263853 := bbase (se 3 (by rfl) ⟨424472, by rfl⟩ : syracuseStep 2263853 = 848945) (by norm_num)
theorem B8596277 : Blo 1508951 8596277 := bbase (se 5 (by rfl) ⟨402950, by rfl⟩ : syracuseStep 8596277 = 805901) (by norm_num)
theorem B11627317 : Blo 1508951 11627317 := bbase (se 5 (by rfl) ⟨545030, by rfl⟩ : syracuseStep 11627317 = 1090061) (by norm_num)
theorem B2419517 : Blo 1508951 2419517 := bbase (se 3 (by rfl) ⟨453659, by rfl⟩ : syracuseStep 2419517 = 907319) (by norm_num)
theorem B2263877 : Blo 1508951 2263877 := bbase (se 4 (by rfl) ⟨212238, by rfl⟩ : syracuseStep 2263877 = 424477) (by norm_num)
theorem B1698637 : Blo 1508951 1698637 := bbase (se 3 (by rfl) ⟨318494, by rfl⟩ : syracuseStep 1698637 = 636989) (by norm_num)
theorem B2263901 : Blo 1508951 2263901 := bbase (se 3 (by rfl) ⟨424481, by rfl⟩ : syracuseStep 2263901 = 848963) (by norm_num)
theorem B1698673 : Blo 1508951 1698673 := bbase (se 2 (by rfl) ⟨637002, by rfl⟩ : syracuseStep 1698673 = 1274005) (by norm_num)
theorem B2263925 : Blo 1508951 2263925 := bbase (se 5 (by rfl) ⟨106121, by rfl⟩ : syracuseStep 2263925 = 212243) (by norm_num)
theorem B3820405 : Blo 1508951 3820405 := bbase (se 5 (by rfl) ⟨179081, by rfl⟩ : syracuseStep 3820405 = 358163) (by norm_num)
theorem B2263949 : Blo 1508951 2263949 := bbase (se 3 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 2263949 = 848981) (by norm_num)
theorem B1698709 : Blo 1508951 1698709 := bbase (se 6 (by rfl) ⟨39813, by rfl⟩ : syracuseStep 1698709 = 79627) (by norm_num)
theorem B1911701 : Blo 1508951 1911701 := bbase (se 6 (by rfl) ⟨44805, by rfl⟩ : syracuseStep 1911701 = 89611) (by norm_num)
theorem B2263973 : Blo 1508951 2263973 := bbase (se 4 (by rfl) ⟨212247, by rfl⟩ : syracuseStep 2263973 = 424495) (by norm_num)
theorem B4836277 : Blo 1508951 4836277 := bbase (se 5 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 4836277 = 453401) (by norm_num)
theorem B1698745 : Blo 1508951 1698745 := bbase (se 2 (by rfl) ⟨637029, by rfl⟩ : syracuseStep 1698745 = 1274059) (by norm_num)
theorem B2263997 : Blo 1508951 2263997 := bbase (se 3 (by rfl) ⟨424499, by rfl⟩ : syracuseStep 2263997 = 848999) (by norm_num)
theorem B1911757 : Blo 1508951 1911757 := bbase (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) (by norm_num)
theorem B2264021 : Blo 1508951 2264021 := bbase (se 7 (by rfl) ⟨26531, by rfl⟩ : syracuseStep 2264021 = 53063) (by norm_num)
theorem B1698781 : Blo 1508951 1698781 := bbase (se 3 (by rfl) ⟨318521, by rfl⟩ : syracuseStep 1698781 = 637043) (by norm_num)
theorem B3820517 : Blo 1508951 3820517 := bbase (se 4 (by rfl) ⟨358173, by rfl⟩ : syracuseStep 3820517 = 716347) (by norm_num)
theorem B2264045 : Blo 1508951 2264045 := bbase (se 3 (by rfl) ⟨424508, by rfl⟩ : syracuseStep 2264045 = 849017) (by norm_num)
theorem B2296829 : Blo 1508951 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B1698817 : Blo 1508951 1698817 := bbase (se 2 (by rfl) ⟨637056, by rfl⟩ : syracuseStep 1698817 = 1274113) (by norm_num)
theorem B2264069 : Blo 1508951 2264069 := bbase (se 4 (by rfl) ⟨212256, by rfl⟩ : syracuseStep 2264069 = 424513) (by norm_num)
theorem B5098517 : Blo 1508951 5098517 := bbase (se 6 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 5098517 = 238993) (by norm_num)
theorem B2264093 : Blo 1508951 2264093 := bbase (se 3 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 2264093 = 849035) (by norm_num)
theorem B2419741 : Blo 1508951 2419741 := bbase (se 3 (by rfl) ⟨453701, by rfl⟩ : syracuseStep 2419741 = 907403) (by norm_num)
theorem B1698853 : Blo 1508951 1698853 := bbase (se 4 (by rfl) ⟨159267, by rfl⟩ : syracuseStep 1698853 = 318535) (by norm_num)
theorem B1911853 : Blo 1508951 1911853 := bbase (se 3 (by rfl) ⟨358472, by rfl⟩ : syracuseStep 1911853 = 716945) (by norm_num)
theorem B2264117 : Blo 1508951 2264117 := bbase (se 5 (by rfl) ⟨106130, by rfl⟩ : syracuseStep 2264117 = 212261) (by norm_num)
theorem B1698889 : Blo 1508951 1698889 := bbase (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) (by norm_num)
theorem B2264141 : Blo 1508951 2264141 := bbase (se 3 (by rfl) ⟨424526, by rfl⟩ : syracuseStep 2264141 = 849053) (by norm_num)
theorem B2264165 : Blo 1508951 2264165 := bbase (se 4 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 2264165 = 424531) (by norm_num)
theorem B1698925 : Blo 1508951 1698925 := bbase (se 3 (by rfl) ⟨318548, by rfl⟩ : syracuseStep 1698925 = 637097) (by norm_num)
theorem B2264189 : Blo 1508951 2264189 := bbase (se 3 (by rfl) ⟨424535, by rfl⟩ : syracuseStep 2264189 = 849071) (by norm_num)
theorem B1698961 : Blo 1508951 1698961 := bbase (se 2 (by rfl) ⟨637110, by rfl⟩ : syracuseStep 1698961 = 1274221) (by norm_num)
theorem B2264213 : Blo 1508951 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B2149525 : Blo 1508951 2149525 := bbase (se 6 (by rfl) ⟨50379, by rfl⟩ : syracuseStep 2149525 = 100759) (by norm_num)
theorem B19614869 : Blo 1508951 19614869 := bbase (se 6 (by rfl) ⟨459723, by rfl⟩ : syracuseStep 19614869 = 919447) (by norm_num)
theorem B10890389 : Blo 1508951 10890389 := bbase (se 6 (by rfl) ⟨255243, by rfl⟩ : syracuseStep 10890389 = 510487) (by norm_num)
theorem B3820709 : Blo 1508951 3820709 := bbase (se 4 (by rfl) ⟨358191, by rfl⟩ : syracuseStep 3820709 = 716383) (by norm_num)
theorem B2264237 : Blo 1508951 2264237 := bbase (se 3 (by rfl) ⟨424544, by rfl⟩ : syracuseStep 2264237 = 849089) (by norm_num)
theorem B1813681 : Blo 1508951 1813681 := bbase (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) (by norm_num)
theorem B1698997 : Blo 1508951 1698997 := bbase (se 5 (by rfl) ⟨79640, by rfl⟩ : syracuseStep 1698997 = 159281) (by norm_num)
theorem B2264261 : Blo 1508951 2264261 := bbase (se 4 (by rfl) ⟨212274, by rfl⟩ : syracuseStep 2264261 = 424549) (by norm_num)
theorem B1699033 : Blo 1508951 1699033 := bbase (se 2 (by rfl) ⟨637137, by rfl⟩ : syracuseStep 1699033 = 1274275) (by norm_num)
theorem B1912025 : Blo 1508951 1912025 := bbase (se 2 (by rfl) ⟨717009, by rfl⟩ : syracuseStep 1912025 = 1434019) (by norm_num)
theorem B2264285 : Blo 1508951 2264285 := bbase (se 3 (by rfl) ⟨424553, by rfl⟩ : syracuseStep 2264285 = 849107) (by norm_num)
theorem B2264309 : Blo 1508951 2264309 := bbase (se 5 (by rfl) ⟨106139, by rfl⟩ : syracuseStep 2264309 = 212279) (by norm_num)
theorem B1699069 : Blo 1508951 1699069 := bbase (se 3 (by rfl) ⟨318575, by rfl⟩ : syracuseStep 1699069 = 637151) (by norm_num)
theorem B2264333 : Blo 1508951 2264333 := bbase (se 3 (by rfl) ⟨424562, by rfl⟩ : syracuseStep 2264333 = 849125) (by norm_num)
theorem B1912081 : Blo 1508951 1912081 := bbase (se 2 (by rfl) ⟨717030, by rfl⟩ : syracuseStep 1912081 = 1434061) (by norm_num)
theorem B1699105 : Blo 1508951 1699105 := bbase (se 2 (by rfl) ⟨637164, by rfl⟩ : syracuseStep 1699105 = 1274329) (by norm_num)
theorem B2264357 : Blo 1508951 2264357 := bbase (se 4 (by rfl) ⟨212283, by rfl⟩ : syracuseStep 2264357 = 424567) (by norm_num)
theorem B2452789 : Blo 1508951 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B2264381 : Blo 1508951 2264381 := bbase (se 3 (by rfl) ⟨424571, by rfl⟩ : syracuseStep 2264381 = 849143) (by norm_num)
theorem B1699141 : Blo 1508951 1699141 := bbase (se 4 (by rfl) ⟨159294, by rfl⟩ : syracuseStep 1699141 = 318589) (by norm_num)
theorem B2264405 : Blo 1508951 2264405 := bbase (se 11 (by rfl) ⟨1658, by rfl⟩ : syracuseStep 2264405 = 3317) (by norm_num)
theorem B1699177 : Blo 1508951 1699177 := bbase (se 2 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 1699177 = 1274383) (by norm_num)
theorem B2264429 : Blo 1508951 2264429 := bbase (se 3 (by rfl) ⟨424580, by rfl⟩ : syracuseStep 2264429 = 849161) (by norm_num)
theorem B1912177 : Blo 1508951 1912177 := bbase (se 2 (by rfl) ⟨717066, by rfl⟩ : syracuseStep 1912177 = 1434133) (by norm_num)
theorem B2264453 : Blo 1508951 2264453 := bbase (se 4 (by rfl) ⟨212292, by rfl⟩ : syracuseStep 2264453 = 424585) (by norm_num)
theorem B1699213 : Blo 1508951 1699213 := bbase (se 3 (by rfl) ⟨318602, by rfl⟩ : syracuseStep 1699213 = 637205) (by norm_num)
theorem B2264477 : Blo 1508951 2264477 := bbase (se 3 (by rfl) ⟨424589, by rfl⟩ : syracuseStep 2264477 = 849179) (by norm_num)
theorem B1699249 : Blo 1508951 1699249 := bbase (se 2 (by rfl) ⟨637218, by rfl⟩ : syracuseStep 1699249 = 1274437) (by norm_num)
theorem B2264501 : Blo 1508951 2264501 := bbase (se 5 (by rfl) ⟨106148, by rfl⟩ : syracuseStep 2264501 = 212297) (by norm_num)
theorem B4656565 : Blo 1508951 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B5098949 : Blo 1508951 5098949 := bbase (se 4 (by rfl) ⟨478026, by rfl⟩ : syracuseStep 5098949 = 956053) (by norm_num)
theorem B2264525 : Blo 1508951 2264525 := bbase (se 3 (by rfl) ⟨424598, by rfl⟩ : syracuseStep 2264525 = 849197) (by norm_num)
theorem B1699285 : Blo 1508951 1699285 := bbase (se 7 (by rfl) ⟨19913, by rfl⟩ : syracuseStep 1699285 = 39827) (by norm_num)
theorem B2264549 : Blo 1508951 2264549 := bbase (se 4 (by rfl) ⟨212301, by rfl⟩ : syracuseStep 2264549 = 424603) (by norm_num)
theorem B2944493 : Blo 1508951 2944493 := bbase (se 3 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 2944493 = 1104185) (by norm_num)
theorem B1699321 : Blo 1508951 1699321 := bbase (se 2 (by rfl) ⟨637245, by rfl⟩ : syracuseStep 1699321 = 1274491) (by norm_num)
theorem B3821053 : Blo 1508951 3821053 := bbase (se 3 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 3821053 = 1432895) (by norm_num)
theorem B2264573 : Blo 1508951 2264573 := bbase (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) (by norm_num)
theorem B4083205 : Blo 1508951 4083205 := bbase (se 4 (by rfl) ⟨382800, by rfl⟩ : syracuseStep 4083205 = 765601) (by norm_num)
theorem B2264597 : Blo 1508951 2264597 := bbase (se 6 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 2264597 = 106153) (by norm_num)
theorem B1699357 : Blo 1508951 1699357 := bbase (se 3 (by rfl) ⟨318629, by rfl⟩ : syracuseStep 1699357 = 637259) (by norm_num)
theorem B2264621 : Blo 1508951 2264621 := bbase (se 3 (by rfl) ⟨424616, by rfl⟩ : syracuseStep 2264621 = 849233) (by norm_num)
theorem B1699393 : Blo 1508951 1699393 := bbase (se 2 (by rfl) ⟨637272, by rfl⟩ : syracuseStep 1699393 = 1274545) (by norm_num)
theorem B3395141 : Blo 1508951 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B2264645 : Blo 1508951 2264645 := bbase (se 4 (by rfl) ⟨212310, by rfl⟩ : syracuseStep 2264645 = 424621) (by norm_num)
theorem B2264669 : Blo 1508951 2264669 := bbase (se 3 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 2264669 = 849251) (by norm_num)
theorem B1699429 : Blo 1508951 1699429 := bbase (se 4 (by rfl) ⟨159321, by rfl⟩ : syracuseStep 1699429 = 318643) (by norm_num)
theorem B3821165 : Blo 1508951 3821165 := bbase (se 3 (by rfl) ⟨716468, by rfl⟩ : syracuseStep 3821165 = 1432937) (by norm_num)
theorem B2264693 : Blo 1508951 2264693 := bbase (se 5 (by rfl) ⟨106157, by rfl⟩ : syracuseStep 2264693 = 212315) (by norm_num)
theorem B1699465 : Blo 1508951 1699465 := bbase (se 2 (by rfl) ⟨637299, by rfl⟩ : syracuseStep 1699465 = 1274599) (by norm_num)
theorem B3395213 : Blo 1508951 3395213 := bbase (se 3 (by rfl) ⟨636602, by rfl⟩ : syracuseStep 3395213 = 1273205) (by norm_num)
theorem B2264717 : Blo 1508951 2264717 := bbase (se 3 (by rfl) ⟨424634, by rfl⟩ : syracuseStep 2264717 = 849269) (by norm_num)
theorem B2264741 : Blo 1508951 2264741 := bbase (se 4 (by rfl) ⟨212319, by rfl⟩ : syracuseStep 2264741 = 424639) (by norm_num)
theorem B7646885 : Blo 1508951 7646885 := bbase (se 4 (by rfl) ⟨716895, by rfl⟩ : syracuseStep 7646885 = 1433791) (by norm_num)
theorem B1699501 : Blo 1508951 1699501 := bbase (se 3 (by rfl) ⟨318656, by rfl⟩ : syracuseStep 1699501 = 637313) (by norm_num)
theorem B2264765 : Blo 1508951 2264765 := bbase (se 3 (by rfl) ⟨424643, by rfl⟩ : syracuseStep 2264765 = 849287) (by norm_num)
theorem B1699537 : Blo 1508951 1699537 := bbase (se 2 (by rfl) ⟨637326, by rfl⟩ : syracuseStep 1699537 = 1274653) (by norm_num)
theorem B3395285 : Blo 1508951 3395285 := bbase (se 7 (by rfl) ⟨39788, by rfl⟩ : syracuseStep 3395285 = 79577) (by norm_num)
theorem B2264789 : Blo 1508951 2264789 := bbase (se 7 (by rfl) ⟨26540, by rfl⟩ : syracuseStep 2264789 = 53081) (by norm_num)
theorem B2264813 : Blo 1508951 2264813 := bbase (se 3 (by rfl) ⟨424652, by rfl⟩ : syracuseStep 2264813 = 849305) (by norm_num)
theorem B1699573 : Blo 1508951 1699573 := bbase (se 5 (by rfl) ⟨79667, by rfl⟩ : syracuseStep 1699573 = 159335) (by norm_num)
theorem B2264837 : Blo 1508951 2264837 := bbase (se 4 (by rfl) ⟨212328, by rfl⟩ : syracuseStep 2264837 = 424657) (by norm_num)
theorem B1699609 : Blo 1508951 1699609 := bbase (se 2 (by rfl) ⟨637353, by rfl⟩ : syracuseStep 1699609 = 1274707) (by norm_num)
theorem B3395357 : Blo 1508951 3395357 := bbase (se 3 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 3395357 = 1273259) (by norm_num)
theorem B2264861 : Blo 1508951 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B3821357 : Blo 1508951 3821357 := bbase (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) (by norm_num)
theorem B2264885 : Blo 1508951 2264885 := bbase (se 5 (by rfl) ⟨106166, by rfl⟩ : syracuseStep 2264885 = 212333) (by norm_num)
theorem B4083509 : Blo 1508951 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B1699645 : Blo 1508951 1699645 := bbase (se 3 (by rfl) ⟨318683, by rfl⟩ : syracuseStep 1699645 = 637367) (by norm_num)
theorem B2264909 : Blo 1508951 2264909 := bbase (se 3 (by rfl) ⟨424670, by rfl⟩ : syracuseStep 2264909 = 849341) (by norm_num)
theorem B1699681 : Blo 1508951 1699681 := bbase (se 2 (by rfl) ⟨637380, by rfl⟩ : syracuseStep 1699681 = 1274761) (by norm_num)
theorem B3395429 : Blo 1508951 3395429 := bbase (se 4 (by rfl) ⟨318321, by rfl⟩ : syracuseStep 3395429 = 636643) (by norm_num)
theorem B2264933 : Blo 1508951 2264933 := bbase (se 4 (by rfl) ⟨212337, by rfl⟩ : syracuseStep 2264933 = 424675) (by norm_num)
theorem B5099381 : Blo 1508951 5099381 := bbase (se 5 (by rfl) ⟨239033, by rfl⟩ : syracuseStep 5099381 = 478067) (by norm_num)
theorem B2264957 : Blo 1508951 2264957 := bbase (se 3 (by rfl) ⟨424679, by rfl⟩ : syracuseStep 2264957 = 849359) (by norm_num)
theorem B1699717 : Blo 1508951 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B2264981 : Blo 1508951 2264981 := bbase (se 6 (by rfl) ⟨53085, by rfl⟩ : syracuseStep 2264981 = 106171) (by norm_num)
theorem B6123413 : Blo 1508951 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B1699753 : Blo 1508951 1699753 := bbase (se 2 (by rfl) ⟨637407, by rfl⟩ : syracuseStep 1699753 = 1274815) (by norm_num)
theorem B3395501 : Blo 1508951 3395501 := bbase (se 3 (by rfl) ⟨636656, by rfl⟩ : syracuseStep 3395501 = 1273313) (by norm_num)
theorem B2265005 : Blo 1508951 2265005 := bbase (se 3 (by rfl) ⟨424688, by rfl⟩ : syracuseStep 2265005 = 849377) (by norm_num)
theorem B2150317 : Blo 1508951 2150317 := bbase (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) (by norm_num)
theorem B2265029 : Blo 1508951 2265029 := bbase (se 4 (by rfl) ⟨212346, by rfl⟩ : syracuseStep 2265029 = 424693) (by norm_num)
theorem B1699789 : Blo 1508951 1699789 := bbase (se 3 (by rfl) ⟨318710, by rfl⟩ : syracuseStep 1699789 = 637421) (by norm_num)
theorem B8597461 : Blo 1508951 8597461 := bbase (se 7 (by rfl) ⟨100751, by rfl⟩ : syracuseStep 8597461 = 201503) (by norm_num)
theorem B2265053 : Blo 1508951 2265053 := bbase (se 3 (by rfl) ⟨424697, by rfl⟩ : syracuseStep 2265053 = 849395) (by norm_num)
theorem B1937389 : Blo 1508951 1937389 := bbase (se 3 (by rfl) ⟨363260, by rfl⟩ : syracuseStep 1937389 = 726521) (by norm_num)
theorem B3395573 : Blo 1508951 3395573 := bbase (se 5 (by rfl) ⟨159167, by rfl⟩ : syracuseStep 3395573 = 318335) (by norm_num)
theorem B2265077 : Blo 1508951 2265077 := bbase (se 5 (by rfl) ⟨106175, by rfl⟩ : syracuseStep 2265077 = 212351) (by norm_num)
theorem B2265101 : Blo 1508951 2265101 := bbase (se 3 (by rfl) ⟨424706, by rfl⟩ : syracuseStep 2265101 = 849413) (by norm_num)
theorem B15486997 : Blo 1508951 15486997 := bbase (se 6 (by rfl) ⟨362976, by rfl⟩ : syracuseStep 15486997 = 725953) (by norm_num)
theorem B2265125 : Blo 1508951 2265125 := bbase (se 4 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 2265125 = 424711) (by norm_num)
theorem B3395645 : Blo 1508951 3395645 := bbase (se 3 (by rfl) ⟨636683, by rfl⟩ : syracuseStep 3395645 = 1273367) (by norm_num)
theorem B2265149 : Blo 1508951 2265149 := bbase (se 3 (by rfl) ⟨424715, by rfl⟩ : syracuseStep 2265149 = 849431) (by norm_num)
theorem B7639109 : Blo 1508951 7639109 := bbase (se 4 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 7639109 = 1432333) (by norm_num)
theorem B2265173 : Blo 1508951 2265173 := bbase (se 8 (by rfl) ⟨13272, by rfl⟩ : syracuseStep 2265173 = 26545) (by norm_num)
theorem B2265197 : Blo 1508951 2265197 := bbase (se 3 (by rfl) ⟨424724, by rfl⟩ : syracuseStep 2265197 = 849449) (by norm_num)
theorem B3395717 : Blo 1508951 3395717 := bbase (se 4 (by rfl) ⟨318348, by rfl⟩ : syracuseStep 3395717 = 636697) (by norm_num)
theorem B3821701 : Blo 1508951 3821701 := bbase (se 4 (by rfl) ⟨358284, by rfl⟩ : syracuseStep 3821701 = 716569) (by norm_num)
theorem B2265221 : Blo 1508951 2265221 := bbase (se 4 (by rfl) ⟨212364, by rfl⟩ : syracuseStep 2265221 = 424729) (by norm_num)
theorem B2265245 : Blo 1508951 2265245 := bbase (se 3 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 2265245 = 849467) (by norm_num)
theorem B2265269 : Blo 1508951 2265269 := bbase (se 5 (by rfl) ⟨106184, by rfl⟩ : syracuseStep 2265269 = 212369) (by norm_num)
theorem B3223741 : Blo 1508951 3223741 := bbase (se 3 (by rfl) ⟨604451, by rfl⟩ : syracuseStep 3223741 = 1208903) (by norm_num)
theorem B1814729 : Blo 1508951 1814729 := bbase (se 2 (by rfl) ⟨680523, by rfl⟩ : syracuseStep 1814729 = 1361047) (by norm_num)
theorem B3395789 : Blo 1508951 3395789 := bbase (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) (by norm_num)
theorem B2265293 : Blo 1508951 2265293 := bbase (se 3 (by rfl) ⟨424742, by rfl⟩ : syracuseStep 2265293 = 849485) (by norm_num)
theorem B5730533 : Blo 1508951 5730533 := bbase (se 4 (by rfl) ⟨537237, by rfl⟩ : syracuseStep 5730533 = 1074475) (by norm_num)
theorem B2265317 : Blo 1508951 2265317 := bbase (se 4 (by rfl) ⟨212373, by rfl⟩ : syracuseStep 2265317 = 424747) (by norm_num)
theorem B3821813 : Blo 1508951 3821813 := bbase (se 5 (by rfl) ⟨179147, by rfl⟩ : syracuseStep 3821813 = 358295) (by norm_num)
theorem B2265341 : Blo 1508951 2265341 := bbase (se 3 (by rfl) ⟨424751, by rfl⟩ : syracuseStep 2265341 = 849503) (by norm_num)
theorem B2150653 : Blo 1508951 2150653 := bbase (se 3 (by rfl) ⟨403247, by rfl⟩ : syracuseStep 2150653 = 806495) (by norm_num)
theorem B4837637 : Blo 1508951 4837637 := bbase (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) (by norm_num)
theorem B3395861 : Blo 1508951 3395861 := bbase (se 6 (by rfl) ⟨79590, by rfl⟩ : syracuseStep 3395861 = 159181) (by norm_num)
theorem B2265365 : Blo 1508951 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B2265389 : Blo 1508951 2265389 := bbase (se 3 (by rfl) ⟨424760, by rfl⟩ : syracuseStep 2265389 = 849521) (by norm_num)
theorem B2265413 : Blo 1508951 2265413 := bbase (se 4 (by rfl) ⟨212382, by rfl⟩ : syracuseStep 2265413 = 424765) (by norm_num)
theorem B4297045 : Blo 1508951 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B3395933 : Blo 1508951 3395933 := bbase (se 3 (by rfl) ⟨636737, by rfl⟩ : syracuseStep 3395933 = 1273475) (by norm_num)
theorem B2265437 : Blo 1508951 2265437 := bbase (se 3 (by rfl) ⟨424769, by rfl⟩ : syracuseStep 2265437 = 849539) (by norm_num)
theorem B4084069 : Blo 1508951 4084069 := bbase (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) (by norm_num)
theorem B2265461 : Blo 1508951 2265461 := bbase (se 5 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 2265461 = 212387) (by norm_num)
theorem B4837765 : Blo 1508951 4837765 := bbase (se 4 (by rfl) ⟨453540, by rfl⟩ : syracuseStep 4837765 = 907081) (by norm_num)
theorem B2265485 : Blo 1508951 2265485 := bbase (se 3 (by rfl) ⟨424778, by rfl⟩ : syracuseStep 2265485 = 849557) (by norm_num)
theorem B3396005 : Blo 1508951 3396005 := bbase (se 4 (by rfl) ⟨318375, by rfl⟩ : syracuseStep 3396005 = 636751) (by norm_num)
theorem B2265509 : Blo 1508951 2265509 := bbase (se 4 (by rfl) ⟨212391, by rfl⟩ : syracuseStep 2265509 = 424783) (by norm_num)
theorem B3822005 : Blo 1508951 3822005 := bbase (se 5 (by rfl) ⟨179156, by rfl⟩ : syracuseStep 3822005 = 358313) (by norm_num)
theorem B2265533 : Blo 1508951 2265533 := bbase (se 3 (by rfl) ⟨424787, by rfl⟩ : syracuseStep 2265533 = 849575) (by norm_num)
theorem B7746005 : Blo 1508951 7746005 := bbase (se 7 (by rfl) ⟨90773, by rfl⟩ : syracuseStep 7746005 = 181547) (by norm_num)
theorem B2265557 : Blo 1508951 2265557 := bbase (se 7 (by rfl) ⟨26549, by rfl⟩ : syracuseStep 2265557 = 53099) (by norm_num)
theorem B2150869 : Blo 1508951 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B20672981 : Blo 1508951 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B3396077 : Blo 1508951 3396077 := bbase (se 3 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 3396077 = 1273529) (by norm_num)
theorem B2265581 : Blo 1508951 2265581 := bbase (se 3 (by rfl) ⟨424796, by rfl⟩ : syracuseStep 2265581 = 849593) (by norm_num)
theorem B4297205 : Blo 1508951 4297205 := bbase (se 5 (by rfl) ⟨201431, by rfl⟩ : syracuseStep 4297205 = 402863) (by norm_num)
theorem B5730821 : Blo 1508951 5730821 := bbase (se 4 (by rfl) ⟨537264, by rfl⟩ : syracuseStep 5730821 = 1074529) (by norm_num)
theorem B2265605 : Blo 1508951 2265605 := bbase (se 4 (by rfl) ⟨212400, by rfl⟩ : syracuseStep 2265605 = 424801) (by norm_num)
theorem B2265629 : Blo 1508951 2265629 := bbase (se 3 (by rfl) ⟨424805, by rfl⟩ : syracuseStep 2265629 = 849611) (by norm_num)
theorem B1815085 : Blo 1508951 1815085 := bbase (se 3 (by rfl) ⟨340328, by rfl⟩ : syracuseStep 1815085 = 680657) (by norm_num)
theorem B3396149 : Blo 1508951 3396149 := bbase (se 5 (by rfl) ⟨159194, by rfl⟩ : syracuseStep 3396149 = 318389) (by norm_num)
theorem B3224117 : Blo 1508951 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B2265653 : Blo 1508951 2265653 := bbase (se 5 (by rfl) ⟨106202, by rfl⟩ : syracuseStep 2265653 = 212405) (by norm_num)
theorem B2265677 : Blo 1508951 2265677 := bbase (se 3 (by rfl) ⟨424814, by rfl⟩ : syracuseStep 2265677 = 849629) (by norm_num)
theorem B2265701 : Blo 1508951 2265701 := bbase (se 4 (by rfl) ⟨212409, by rfl⟩ : syracuseStep 2265701 = 424819) (by norm_num)
theorem B3396221 : Blo 1508951 3396221 := bbase (se 3 (by rfl) ⟨636791, by rfl⟩ : syracuseStep 3396221 = 1273583) (by norm_num)
theorem B2265725 : Blo 1508951 2265725 := bbase (se 3 (by rfl) ⟨424823, by rfl⟩ : syracuseStep 2265725 = 849647) (by norm_num)
theorem B4838021 : Blo 1508951 4838021 := bbase (se 4 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 4838021 = 907129) (by norm_num)
theorem B16323221 : Blo 1508951 16323221 := bbase (se 6 (by rfl) ⟨382575, by rfl⟩ : syracuseStep 16323221 = 765151) (by norm_num)
theorem B2265749 : Blo 1508951 2265749 := bbase (se 6 (by rfl) ⟨53103, by rfl⟩ : syracuseStep 2265749 = 106207) (by norm_num)
theorem B2265773 : Blo 1508951 2265773 := bbase (se 3 (by rfl) ⟨424832, by rfl⟩ : syracuseStep 2265773 = 849665) (by norm_num)
theorem B3396293 : Blo 1508951 3396293 := bbase (se 4 (by rfl) ⟨318402, by rfl⟩ : syracuseStep 3396293 = 636805) (by norm_num)
theorem B2265797 : Blo 1508951 2265797 := bbase (se 4 (by rfl) ⟨212418, by rfl⟩ : syracuseStep 2265797 = 424837) (by norm_num)
theorem B2265821 : Blo 1508951 2265821 := bbase (se 3 (by rfl) ⟨424841, by rfl⟩ : syracuseStep 2265821 = 849683) (by norm_num)
theorem B4297445 : Blo 1508951 4297445 := bbase (se 4 (by rfl) ⟨402885, by rfl⟩ : syracuseStep 4297445 = 805771) (by norm_num)
theorem B2265845 : Blo 1508951 2265845 := bbase (se 5 (by rfl) ⟨106211, by rfl⟩ : syracuseStep 2265845 = 212423) (by norm_num)
theorem B3396365 : Blo 1508951 3396365 := bbase (se 3 (by rfl) ⟨636818, by rfl⟩ : syracuseStep 3396365 = 1273637) (by norm_num)
theorem B3822349 : Blo 1508951 3822349 := bbase (se 3 (by rfl) ⟨716690, by rfl⟩ : syracuseStep 3822349 = 1433381) (by norm_num)
theorem B2265869 : Blo 1508951 2265869 := bbase (se 3 (by rfl) ⟨424850, by rfl⟩ : syracuseStep 2265869 = 849701) (by norm_num)
theorem B3445517 : Blo 1508951 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2265893 : Blo 1508951 2265893 := bbase (se 4 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 2265893 = 424855) (by norm_num)
theorem B2265917 : Blo 1508951 2265917 := bbase (se 3 (by rfl) ⟨424859, by rfl⟩ : syracuseStep 2265917 = 849719) (by norm_num)
theorem B2151245 : Blo 1508951 2151245 := bbase (se 3 (by rfl) ⟨403358, by rfl⟩ : syracuseStep 2151245 = 806717) (by norm_num)
theorem B3396437 : Blo 1508951 3396437 := bbase (se 9 (by rfl) ⟨9950, by rfl⟩ : syracuseStep 3396437 = 19901) (by norm_num)
theorem B2265941 : Blo 1508951 2265941 := bbase (se 9 (by rfl) ⟨6638, by rfl⟩ : syracuseStep 2265941 = 13277) (by norm_num)
theorem B2265965 : Blo 1508951 2265965 := bbase (se 3 (by rfl) ⟨424868, by rfl⟩ : syracuseStep 2265965 = 849737) (by norm_num)
theorem B3822461 : Blo 1508951 3822461 := bbase (se 3 (by rfl) ⟨716711, by rfl⟩ : syracuseStep 3822461 = 1433423) (by norm_num)
theorem B7254917 : Blo 1508951 7254917 := bbase (se 4 (by rfl) ⟨680148, by rfl⟩ : syracuseStep 7254917 = 1360297) (by norm_num)
theorem B2265989 : Blo 1508951 2265989 := bbase (se 4 (by rfl) ⟨212436, by rfl⟩ : syracuseStep 2265989 = 424873) (by norm_num)
theorem B3396509 : Blo 1508951 3396509 := bbase (se 3 (by rfl) ⟨636845, by rfl⟩ : syracuseStep 3396509 = 1273691) (by norm_num)
theorem B2266013 : Blo 1508951 2266013 := bbase (se 3 (by rfl) ⟨424877, by rfl⟩ : syracuseStep 2266013 = 849755) (by norm_num)
theorem B4297637 : Blo 1508951 4297637 := bbase (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) (by norm_num)
theorem B2266037 : Blo 1508951 2266037 := bbase (se 5 (by rfl) ⟨106220, by rfl⟩ : syracuseStep 2266037 = 212441) (by norm_num)
theorem B7648181 : Blo 1508951 7648181 := bbase (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) (by norm_num)
theorem B2266061 : Blo 1508951 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B24474581 : Blo 1508951 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B3396581 : Blo 1508951 3396581 := bbase (se 4 (by rfl) ⟨318429, by rfl⟩ : syracuseStep 3396581 = 636859) (by norm_num)
theorem B2266085 : Blo 1508951 2266085 := bbase (se 4 (by rfl) ⟨212445, by rfl⟩ : syracuseStep 2266085 = 424891) (by norm_num)
theorem B3314677 : Blo 1508951 3314677 := bbase (se 5 (by rfl) ⟨155375, by rfl⟩ : syracuseStep 3314677 = 310751) (by norm_num)
theorem B2266109 : Blo 1508951 2266109 := bbase (se 3 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 2266109 = 849791) (by norm_num)
theorem B2266133 : Blo 1508951 2266133 := bbase (se 6 (by rfl) ⟨53112, by rfl⟩ : syracuseStep 2266133 = 106225) (by norm_num)
theorem B3396653 : Blo 1508951 3396653 := bbase (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) (by norm_num)
theorem B2266157 : Blo 1508951 2266157 := bbase (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) (by norm_num)
theorem B3822653 : Blo 1508951 3822653 := bbase (se 3 (by rfl) ⟨716747, by rfl⟩ : syracuseStep 3822653 = 1433495) (by norm_num)
theorem B2266181 : Blo 1508951 2266181 := bbase (se 4 (by rfl) ⟨212454, by rfl⟩ : syracuseStep 2266181 = 424909) (by norm_num)
theorem B2266205 : Blo 1508951 2266205 := bbase (se 3 (by rfl) ⟨424913, by rfl⟩ : syracuseStep 2266205 = 849827) (by norm_num)
theorem B3396725 : Blo 1508951 3396725 := bbase (se 5 (by rfl) ⟨159221, by rfl⟩ : syracuseStep 3396725 = 318443) (by norm_num)
theorem B2266229 : Blo 1508951 2266229 := bbase (se 5 (by rfl) ⟨106229, by rfl⟩ : syracuseStep 2266229 = 212459) (by norm_num)
theorem B2266253 : Blo 1508951 2266253 := bbase (se 3 (by rfl) ⟨424922, by rfl⟩ : syracuseStep 2266253 = 849845) (by norm_num)
theorem B2266277 : Blo 1508951 2266277 := bbase (se 4 (by rfl) ⟨212463, by rfl⟩ : syracuseStep 2266277 = 424927) (by norm_num)
theorem B1635509 : Blo 1508951 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B3396797 : Blo 1508951 3396797 := bbase (se 3 (by rfl) ⟨636899, by rfl⟩ : syracuseStep 3396797 = 1273799) (by norm_num)
theorem B2266301 : Blo 1508951 2266301 := bbase (se 3 (by rfl) ⟨424931, by rfl⟩ : syracuseStep 2266301 = 849863) (by norm_num)
theorem B2266325 : Blo 1508951 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B2266349 : Blo 1508951 2266349 := bbase (se 3 (by rfl) ⟨424940, by rfl⟩ : syracuseStep 2266349 = 849881) (by norm_num)
theorem B3396869 : Blo 1508951 3396869 := bbase (se 4 (by rfl) ⟨318456, by rfl⟩ : syracuseStep 3396869 = 636913) (by norm_num)
theorem B2266373 : Blo 1508951 2266373 := bbase (se 4 (by rfl) ⟨212472, by rfl⟩ : syracuseStep 2266373 = 424945) (by norm_num)
theorem B2266397 : Blo 1508951 2266397 := bbase (se 3 (by rfl) ⟨424949, by rfl⟩ : syracuseStep 2266397 = 849899) (by norm_num)
theorem B2266421 : Blo 1508951 2266421 := bbase (se 5 (by rfl) ⟨106238, by rfl⟩ : syracuseStep 2266421 = 212477) (by norm_num)
theorem B3396941 : Blo 1508951 3396941 := bbase (se 3 (by rfl) ⟨636926, by rfl⟩ : syracuseStep 3396941 = 1273853) (by norm_num)
theorem B7640405 : Blo 1508951 7640405 := bbase (se 14 (by rfl) ⟨699, by rfl⟩ : syracuseStep 7640405 = 1399) (by norm_num)
theorem B14513525 : Blo 1508951 14513525 := bbase (se 5 (by rfl) ⟨680321, by rfl⟩ : syracuseStep 14513525 = 1360643) (by norm_num)
theorem B3397013 : Blo 1508951 3397013 := bbase (se 6 (by rfl) ⟨79617, by rfl⟩ : syracuseStep 3397013 = 159235) (by norm_num)
theorem B3822997 : Blo 1508951 3822997 := bbase (se 6 (by rfl) ⟨89601, by rfl⟩ : syracuseStep 3822997 = 179203) (by norm_num)
theorem B3061165 : Blo 1508951 3061165 := bbase (se 3 (by rfl) ⟨573968, by rfl⟩ : syracuseStep 3061165 = 1147937) (by norm_num)
theorem B11466197 : Blo 1508951 11466197 := bbase (se 7 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 11466197 = 268739) (by norm_num)
theorem B3397085 : Blo 1508951 3397085 := bbase (se 3 (by rfl) ⟨636953, by rfl⟩ : syracuseStep 3397085 = 1273907) (by norm_num)
theorem B3823109 : Blo 1508951 3823109 := bbase (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) (by norm_num)
theorem B5092901 : Blo 1508951 5092901 := bbase (se 4 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 5092901 = 954919) (by norm_num)
theorem B3397157 : Blo 1508951 3397157 := bbase (se 4 (by rfl) ⟨318483, by rfl⟩ : syracuseStep 3397157 = 636967) (by norm_num)
theorem B3397229 : Blo 1508951 3397229 := bbase (se 3 (by rfl) ⟨636980, by rfl⟩ : syracuseStep 3397229 = 1273961) (by norm_num)
theorem B5732005 : Blo 1508951 5732005 := bbase (se 4 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 5732005 = 1074751) (by norm_num)
theorem B10327733 : Blo 1508951 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B3397301 : Blo 1508951 3397301 := bbase (se 5 (by rfl) ⟨159248, by rfl⟩ : syracuseStep 3397301 = 318497) (by norm_num)
theorem B3823301 : Blo 1508951 3823301 := bbase (se 4 (by rfl) ⟨358434, by rfl⟩ : syracuseStep 3823301 = 716869) (by norm_num)
theorem B3397373 : Blo 1508951 3397373 := bbase (se 3 (by rfl) ⟨637007, by rfl⟩ : syracuseStep 3397373 = 1274015) (by norm_num)
theorem B1529609 : Blo 1508951 1529609 := bbase (se 2 (by rfl) ⟨573603, by rfl⟩ : syracuseStep 1529609 = 1147207) (by norm_num)
theorem B2864909 : Blo 1508951 2864909 := bbase (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) (by norm_num)
theorem B2389813 : Blo 1508951 2389813 := bbase (se 5 (by rfl) ⟨112022, by rfl⟩ : syracuseStep 2389813 = 224045) (by norm_num)
theorem B3397445 : Blo 1508951 3397445 := bbase (se 4 (by rfl) ⟨318510, by rfl⟩ : syracuseStep 3397445 = 637021) (by norm_num)
theorem B9672533 : Blo 1508951 9672533 := bbase (se 9 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 9672533 = 56675) (by norm_num)
theorem B10327925 : Blo 1508951 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B4298629 : Blo 1508951 4298629 := bbase (se 4 (by rfl) ⟨402996, by rfl⟩ : syracuseStep 4298629 = 805993) (by norm_num)
theorem B3397517 : Blo 1508951 3397517 := bbase (se 3 (by rfl) ⟨637034, by rfl⟩ : syracuseStep 3397517 = 1274069) (by norm_num)
theorem B8599445 : Blo 1508951 8599445 := bbase (se 6 (by rfl) ⟨201549, by rfl⟩ : syracuseStep 8599445 = 403099) (by norm_num)
theorem B2865061 : Blo 1508951 2865061 := bbase (se 4 (by rfl) ⟨268599, by rfl⟩ : syracuseStep 2865061 = 537199) (by norm_num)
theorem B5093333 : Blo 1508951 5093333 := bbase (se 7 (by rfl) ⟨59687, by rfl⟩ : syracuseStep 5093333 = 119375) (by norm_num)
theorem B5732309 : Blo 1508951 5732309 := bbase (se 7 (by rfl) ⟨67175, by rfl⟩ : syracuseStep 5732309 = 134351) (by norm_num)
theorem B3397589 : Blo 1508951 3397589 := bbase (se 7 (by rfl) ⟨39815, by rfl⟩ : syracuseStep 3397589 = 79631) (by norm_num)
theorem B7747589 : Blo 1508951 7747589 := bbase (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) (by norm_num)
theorem B1611785 : Blo 1508951 1611785 := bbase (se 2 (by rfl) ⟨604419, by rfl⟩ : syracuseStep 1611785 = 1208839) (by norm_num)
theorem B14710805 : Blo 1508951 14710805 := bbase (se 6 (by rfl) ⟨344784, by rfl⟩ : syracuseStep 14710805 = 689569) (by norm_num)
theorem B3397661 : Blo 1508951 3397661 := bbase (se 3 (by rfl) ⟨637061, by rfl⟩ : syracuseStep 3397661 = 1274123) (by norm_num)
theorem B3823645 : Blo 1508951 3823645 := bbase (se 3 (by rfl) ⟨716933, by rfl⟩ : syracuseStep 3823645 = 1433867) (by norm_num)
theorem B3397733 : Blo 1508951 3397733 := bbase (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) (by norm_num)
theorem B3823757 : Blo 1508951 3823757 := bbase (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) (by norm_num)
theorem B3225757 : Blo 1508951 3225757 := bbase (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) (by norm_num)
theorem B3397805 : Blo 1508951 3397805 := bbase (se 3 (by rfl) ⟨637088, by rfl⟩ : syracuseStep 3397805 = 1274177) (by norm_num)
theorem B7256261 : Blo 1508951 7256261 := bbase (se 4 (by rfl) ⟨680274, by rfl⟩ : syracuseStep 7256261 = 1360549) (by norm_num)
theorem B2865365 : Blo 1508951 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B3397877 : Blo 1508951 3397877 := bbase (se 5 (by rfl) ⟨159275, by rfl⟩ : syracuseStep 3397877 = 318551) (by norm_num)
theorem B3397949 : Blo 1508951 3397949 := bbase (se 3 (by rfl) ⟨637115, by rfl⟩ : syracuseStep 3397949 = 1274231) (by norm_num)
theorem B1530181 : Blo 1508951 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B3823949 : Blo 1508951 3823949 := bbase (se 3 (by rfl) ⟨716990, by rfl⟩ : syracuseStep 3823949 = 1433981) (by norm_num)
theorem B5093765 : Blo 1508951 5093765 := bbase (se 4 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 5093765 = 955081) (by norm_num)
theorem B3398021 : Blo 1508951 3398021 := bbase (se 4 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 3398021 = 637129) (by norm_num)
theorem B1612229 : Blo 1508951 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B6453701 : Blo 1508951 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B3398093 : Blo 1508951 3398093 := bbase (se 3 (by rfl) ⟨637142, by rfl⟩ : syracuseStep 3398093 = 1274285) (by norm_num)
theorem B3398165 : Blo 1508951 3398165 := bbase (se 6 (by rfl) ⟨79644, by rfl⟩ : syracuseStep 3398165 = 159289) (by norm_num)
theorem B5167685 : Blo 1508951 5167685 := bbase (se 4 (by rfl) ⟨484470, by rfl⟩ : syracuseStep 5167685 = 968941) (by norm_num)
theorem B3398237 : Blo 1508951 3398237 := bbase (se 3 (by rfl) ⟨637169, by rfl⟩ : syracuseStep 3398237 = 1274339) (by norm_num)
theorem B7641701 : Blo 1508951 7641701 := bbase (se 4 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 7641701 = 1432819) (by norm_num)
theorem B3398309 : Blo 1508951 3398309 := bbase (se 4 (by rfl) ⟨318591, by rfl⟩ : syracuseStep 3398309 = 637183) (by norm_num)
theorem B3824293 : Blo 1508951 3824293 := bbase (se 4 (by rfl) ⟨358527, by rfl⟩ : syracuseStep 3824293 = 717055) (by norm_num)
theorem B1612477 : Blo 1508951 1612477 := bbase (se 3 (by rfl) ⟨302339, by rfl⟩ : syracuseStep 1612477 = 604679) (by norm_num)
theorem B3062501 : Blo 1508951 3062501 := bbase (se 4 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 3062501 = 574219) (by norm_num)
theorem B3398381 : Blo 1508951 3398381 := bbase (se 3 (by rfl) ⟨637196, by rfl⟩ : syracuseStep 3398381 = 1274393) (by norm_num)
theorem B2546437 : Blo 1508951 2546437 := bbase (se 4 (by rfl) ⟨238728, by rfl⟩ : syracuseStep 2546437 = 477457) (by norm_num)
theorem B3062533 : Blo 1508951 3062533 := bbase (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) (by norm_num)
theorem B3824405 : Blo 1508951 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B5094197 : Blo 1508951 5094197 := bbase (se 5 (by rfl) ⟨238790, by rfl⟩ : syracuseStep 5094197 = 477581) (by norm_num)
theorem B3398453 : Blo 1508951 3398453 := bbase (se 5 (by rfl) ⟨159302, by rfl⟩ : syracuseStep 3398453 = 318605) (by norm_num)
theorem B6445909 : Blo 1508951 6445909 := bbase (se 9 (by rfl) ⟨18884, by rfl⟩ : syracuseStep 6445909 = 37769) (by norm_num)
theorem B2546525 : Blo 1508951 2546525 := bbase (se 3 (by rfl) ⟨477473, by rfl⟩ : syracuseStep 2546525 = 954947) (by norm_num)
theorem B3398525 : Blo 1508951 3398525 := bbase (se 3 (by rfl) ⟨637223, by rfl⟩ : syracuseStep 3398525 = 1274447) (by norm_num)
theorem B3726229 : Blo 1508951 3726229 := bbase (se 6 (by rfl) ⟨87333, by rfl⟩ : syracuseStep 3726229 = 174667) (by norm_num)
theorem B2866117 : Blo 1508951 2866117 := bbase (se 4 (by rfl) ⟨268698, by rfl⟩ : syracuseStep 2866117 = 537397) (by norm_num)
theorem B3398597 : Blo 1508951 3398597 := bbase (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) (by norm_num)
theorem B4299733 : Blo 1508951 4299733 := bbase (se 7 (by rfl) ⟨50387, by rfl⟩ : syracuseStep 4299733 = 100775) (by norm_num)
theorem B3824597 : Blo 1508951 3824597 := bbase (se 7 (by rfl) ⟨44819, by rfl⟩ : syracuseStep 3824597 = 89639) (by norm_num)
theorem B2546653 : Blo 1508951 2546653 := bbase (se 3 (by rfl) ⟨477497, by rfl⟩ : syracuseStep 2546653 = 954995) (by norm_num)
theorem B3398669 : Blo 1508951 3398669 := bbase (se 3 (by rfl) ⟨637250, by rfl⟩ : syracuseStep 3398669 = 1274501) (by norm_num)
theorem B3226645 : Blo 1508951 3226645 := bbase (se 6 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 3226645 = 151249) (by norm_num)
theorem B4840469 : Blo 1508951 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B2546741 : Blo 1508951 2546741 := bbase (se 5 (by rfl) ⟨119378, by rfl⟩ : syracuseStep 2546741 = 238757) (by norm_num)
theorem B3628093 : Blo 1508951 3628093 := bbase (se 3 (by rfl) ⟨680267, by rfl⟩ : syracuseStep 3628093 = 1360535) (by norm_num)
theorem B2866261 : Blo 1508951 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B3398741 : Blo 1508951 3398741 := bbase (se 8 (by rfl) ⟨19914, by rfl⟩ : syracuseStep 3398741 = 39829) (by norm_num)
theorem B1612909 : Blo 1508951 1612909 := bbase (se 3 (by rfl) ⟨302420, by rfl⟩ : syracuseStep 1612909 = 604841) (by norm_num)
theorem B3398813 : Blo 1508951 3398813 := bbase (se 3 (by rfl) ⟨637277, by rfl⟩ : syracuseStep 3398813 = 1274555) (by norm_num)
theorem B2546869 : Blo 1508951 2546869 := bbase (se 5 (by rfl) ⟨119384, by rfl⟩ : syracuseStep 2546869 = 238769) (by norm_num)
theorem B1612981 : Blo 1508951 1612981 := bbase (se 5 (by rfl) ⟨75608, by rfl⟩ : syracuseStep 1612981 = 151217) (by norm_num)
theorem B5094629 : Blo 1508951 5094629 := bbase (se 4 (by rfl) ⟨477621, by rfl⟩ : syracuseStep 5094629 = 955243) (by norm_num)
theorem B3398885 : Blo 1508951 3398885 := bbase (se 4 (by rfl) ⟨318645, by rfl⟩ : syracuseStep 3398885 = 637291) (by norm_num)
theorem B1531121 : Blo 1508951 1531121 := bbase (se 2 (by rfl) ⟨574170, by rfl⟩ : syracuseStep 1531121 = 1148341) (by norm_num)
theorem B2866421 : Blo 1508951 2866421 := bbase (se 5 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 2866421 = 268727) (by norm_num)
theorem B2546957 : Blo 1508951 2546957 := bbase (se 3 (by rfl) ⟨477554, by rfl⟩ : syracuseStep 2546957 = 955109) (by norm_num)
theorem B3398957 : Blo 1508951 3398957 := bbase (se 3 (by rfl) ⟨637304, by rfl⟩ : syracuseStep 3398957 = 1274609) (by norm_num)
theorem B3399029 : Blo 1508951 3399029 := bbase (se 5 (by rfl) ⟨159329, by rfl⟩ : syracuseStep 3399029 = 318659) (by norm_num)
theorem B2866565 : Blo 1508951 2866565 := bbase (se 4 (by rfl) ⟨268740, by rfl⟩ : syracuseStep 2866565 = 537481) (by norm_num)
theorem B2547085 : Blo 1508951 2547085 := bbase (se 3 (by rfl) ⟨477578, by rfl⟩ : syracuseStep 2547085 = 955157) (by norm_num)
theorem B9182645 : Blo 1508951 9182645 := bbase (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) (by norm_num)
theorem B3399101 : Blo 1508951 3399101 := bbase (se 3 (by rfl) ⟨637331, by rfl⟩ : syracuseStep 3399101 = 1274663) (by norm_num)
theorem B2547173 : Blo 1508951 2547173 := bbase (se 4 (by rfl) ⟨238797, by rfl⟩ : syracuseStep 2547173 = 477595) (by norm_num)
theorem B3399173 : Blo 1508951 3399173 := bbase (se 4 (by rfl) ⟨318672, by rfl⟩ : syracuseStep 3399173 = 637345) (by norm_num)
theorem B18357781 : Blo 1508951 18357781 := bbase (se 6 (by rfl) ⟨430260, by rfl⟩ : syracuseStep 18357781 = 860521) (by norm_num)
theorem B1613353 : Blo 1508951 1613353 := bbase (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) (by norm_num)
theorem B3628613 : Blo 1508951 3628613 := bbase (se 4 (by rfl) ⟨340182, by rfl⟩ : syracuseStep 3628613 = 680365) (by norm_num)
theorem B3399245 : Blo 1508951 3399245 := bbase (se 3 (by rfl) ⟨637358, by rfl⟩ : syracuseStep 3399245 = 1274717) (by norm_num)
theorem B2547301 : Blo 1508951 2547301 := bbase (se 4 (by rfl) ⟨238809, by rfl⟩ : syracuseStep 2547301 = 477619) (by norm_num)
theorem B5095061 : Blo 1508951 5095061 := bbase (se 6 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 5095061 = 238831) (by norm_num)
theorem B3399317 : Blo 1508951 3399317 := bbase (se 6 (by rfl) ⟨79671, by rfl⟩ : syracuseStep 3399317 = 159343) (by norm_num)
theorem B2866853 : Blo 1508951 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B3628709 : Blo 1508951 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B2547389 : Blo 1508951 2547389 := bbase (se 3 (by rfl) ⟨477635, by rfl⟩ : syracuseStep 2547389 = 955271) (by norm_num)
theorem B3399389 : Blo 1508951 3399389 := bbase (se 3 (by rfl) ⟨637385, by rfl⟩ : syracuseStep 3399389 = 1274771) (by norm_num)
theorem B2039581 : Blo 1508951 2039581 := bbase (se 3 (by rfl) ⟨382421, by rfl⟩ : syracuseStep 2039581 = 764843) (by norm_num)
theorem B3399461 : Blo 1508951 3399461 := bbase (se 4 (by rfl) ⟨318699, by rfl⟩ : syracuseStep 3399461 = 637399) (by norm_num)
theorem B12894005 : Blo 1508951 12894005 := bbase (se 5 (by rfl) ⟨604406, by rfl⟩ : syracuseStep 12894005 = 1208813) (by norm_num)
theorem B2547517 : Blo 1508951 2547517 := bbase (se 3 (by rfl) ⟨477659, by rfl⟩ : syracuseStep 2547517 = 955319) (by norm_num)
theorem B2867005 : Blo 1508951 2867005 := bbase (se 3 (by rfl) ⟨537563, by rfl⟩ : syracuseStep 2867005 = 1075127) (by norm_num)
theorem B3399533 : Blo 1508951 3399533 := bbase (se 3 (by rfl) ⟨637412, by rfl⟩ : syracuseStep 3399533 = 1274825) (by norm_num)
theorem B4079477 : Blo 1508951 4079477 := bbase (se 5 (by rfl) ⟨191225, by rfl⟩ : syracuseStep 4079477 = 382451) (by norm_num)
theorem B7642997 : Blo 1508951 7642997 := bbase (se 5 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 7642997 = 716531) (by norm_num)
theorem B2547605 : Blo 1508951 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B3399605 : Blo 1508951 3399605 := bbase (se 5 (by rfl) ⟨159356, by rfl⟩ : syracuseStep 3399605 = 318713) (by norm_num)
theorem B2547713 : Blo 1508951 2547713 := bstep (se 2 (by rfl) ⟨955392, by rfl⟩ : syracuseStep 2547713 = 1910785) B1910785
theorem B5734435 : Blo 1508951 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B2547841 : Blo 1508951 2547841 := bstep (se 2 (by rfl) ⟨955440, by rfl⟩ : syracuseStep 2547841 = 1910881) B1910881
theorem B2547875 : Blo 1508951 2547875 := bstep (se 1 (by rfl) ⟨1910906, by rfl⟩ : syracuseStep 2547875 = 3821813) B3821813
theorem B5095601 : Blo 1508951 5095601 := bstep (se 2 (by rfl) ⟨1910850, by rfl⟩ : syracuseStep 5095601 = 3821701) B3821701
theorem B12239045 : Blo 1508951 12239045 := bstep (se 4 (by rfl) ⟨1147410, by rfl⟩ : syracuseStep 12239045 = 2294821) B2294821
theorem B10887365 : Blo 1508951 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B4301009 : Blo 1508951 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2548003 : Blo 1508951 2548003 := bstep (se 1 (by rfl) ⟨1911002, by rfl⟩ : syracuseStep 2548003 = 3822005) B3822005
theorem B2867491 : Blo 1508951 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B2867537 : Blo 1508951 2867537 := bstep (se 2 (by rfl) ⟨1075326, by rfl⟩ : syracuseStep 2867537 = 2150653) B2150653
theorem B29041037 : Blo 1508951 29041037 := bstep (se 3 (by rfl) ⟨5445194, by rfl⟩ : syracuseStep 29041037 = 10890389) B10890389
theorem B2417057 : Blo 1508951 2417057 := bstep (se 2 (by rfl) ⟨906396, by rfl⟩ : syracuseStep 2417057 = 1812793) B1812793
theorem B2040241 : Blo 1508951 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B2548145 : Blo 1508951 2548145 := bstep (se 2 (by rfl) ⟨955554, by rfl⟩ : syracuseStep 2548145 = 1911109) B1911109
theorem B12247537 : Blo 1508951 12247537 := bstep (se 2 (by rfl) ⟨4592826, by rfl⟩ : syracuseStep 12247537 = 9185653) B9185653
theorem B19350029 : Blo 1508951 19350029 := bstep (se 3 (by rfl) ⟨3628130, by rfl⟩ : syracuseStep 19350029 = 7256261) B7256261
theorem B2548273 : Blo 1508951 2548273 := bstep (se 2 (by rfl) ⟨955602, by rfl⟩ : syracuseStep 2548273 = 1911205) B1911205
theorem B2548307 : Blo 1508951 2548307 := bstep (se 1 (by rfl) ⟨1911230, by rfl⟩ : syracuseStep 2548307 = 3822461) B3822461
theorem B2867825 : Blo 1508951 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B2294419 : Blo 1508951 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B5096141 : Blo 1508951 5096141 := bstep (se 3 (by rfl) ⟨955526, by rfl⟩ : syracuseStep 5096141 = 1911053) B1911053
theorem B2548435 : Blo 1508951 2548435 := bstep (se 1 (by rfl) ⟨1911326, by rfl⟩ : syracuseStep 2548435 = 3822653) B3822653
theorem B5096195 : Blo 1508951 5096195 := bstep (se 1 (by rfl) ⟨3822146, by rfl⟩ : syracuseStep 5096195 = 7644293) B7644293
theorem B10879757 : Blo 1508951 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B2179891 : Blo 1508951 2179891 := bstep (se 1 (by rfl) ⟨1634918, by rfl⟩ : syracuseStep 2179891 = 3269837) B3269837
theorem B2548577 : Blo 1508951 2548577 := bstep (se 2 (by rfl) ⟨955716, by rfl⟩ : syracuseStep 2548577 = 1911433) B1911433
theorem B9675683 : Blo 1508951 9675683 := bstep (se 1 (by rfl) ⟨7256762, by rfl⟩ : syracuseStep 9675683 = 14513525) B14513525
theorem B2548705 : Blo 1508951 2548705 := bstep (se 2 (by rfl) ⟨955764, by rfl⟩ : syracuseStep 2548705 = 1911529) B1911529
theorem B7644131 : Blo 1508951 7644131 := bstep (se 1 (by rfl) ⟨5733098, by rfl⟩ : syracuseStep 7644131 = 11466197) B11466197
theorem B2548739 : Blo 1508951 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B5096465 : Blo 1508951 5096465 := bstep (se 2 (by rfl) ⟨1911174, by rfl⟩ : syracuseStep 5096465 = 3822349) B3822349
theorem B8594545 : Blo 1508951 8594545 := bstep (se 2 (by rfl) ⟨3222954, by rfl⟩ : syracuseStep 8594545 = 6445909) B6445909
theorem B2548867 : Blo 1508951 2548867 := bstep (se 1 (by rfl) ⟨1911650, by rfl⟩ : syracuseStep 2548867 = 3823301) B3823301
theorem B6448355 : Blo 1508951 6448355 := bstep (se 1 (by rfl) ⟨4836266, by rfl⟩ : syracuseStep 6448355 = 9672533) B9672533
theorem B2549009 : Blo 1508951 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B9807203 : Blo 1508951 9807203 := bstep (se 1 (by rfl) ⟨7355402, by rfl⟩ : syracuseStep 9807203 = 14710805) B14710805
theorem B2549137 : Blo 1508951 2549137 := bstep (se 2 (by rfl) ⟨955926, by rfl⟩ : syracuseStep 2549137 = 1911853) B1911853
theorem B2549171 : Blo 1508951 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B1910243 : Blo 1508951 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B13780493 : Blo 1508951 13780493 := bstep (se 3 (by rfl) ⟨2583842, by rfl⟩ : syracuseStep 13780493 = 5167685) B5167685
theorem B5097005 : Blo 1508951 5097005 := bstep (se 3 (by rfl) ⟨955688, by rfl⟩ : syracuseStep 5097005 = 1911377) B1911377
theorem B2721329 : Blo 1508951 2721329 := bstep (se 2 (by rfl) ⟨1020498, by rfl⟩ : syracuseStep 2721329 = 2040997) B2040997
theorem B2549299 : Blo 1508951 2549299 := bstep (se 1 (by rfl) ⟨1911974, by rfl⟩ : syracuseStep 2549299 = 3823949) B3823949
theorem B1508963 : Blo 1508951 1508963 := bstep (se 1 (by rfl) ⟨1131722, by rfl⟩ : syracuseStep 1508963 = 2263445) B2263445
theorem B5097059 : Blo 1508951 5097059 := bstep (se 1 (by rfl) ⟨3822794, by rfl⟩ : syracuseStep 5097059 = 7645589) B7645589
theorem B1508979 : Blo 1508951 1508979 := bstep (se 1 (by rfl) ⟨1131734, by rfl⟩ : syracuseStep 1508979 = 2263469) B2263469
theorem B1508995 : Blo 1508951 1508995 := bstep (se 1 (by rfl) ⟨1131746, by rfl⟩ : syracuseStep 1508995 = 2263493) B2263493
theorem B4302467 : Blo 1508951 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B7956109 : Blo 1508951 7956109 := bstep (se 3 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 7956109 = 2983541) B2983541
theorem B1509011 : Blo 1508951 1509011 := bstep (se 1 (by rfl) ⟨1131758, by rfl⟩ : syracuseStep 1509011 = 2263517) B2263517
theorem B1509027 : Blo 1508951 1509027 := bstep (se 1 (by rfl) ⟨1131770, by rfl⟩ : syracuseStep 1509027 = 2263541) B2263541
theorem B1509043 : Blo 1508951 1509043 := bstep (se 1 (by rfl) ⟨1131782, by rfl⟩ : syracuseStep 1509043 = 2263565) B2263565
theorem B2549441 : Blo 1508951 2549441 := bstep (se 2 (by rfl) ⟨956040, by rfl⟩ : syracuseStep 2549441 = 1912081) B1912081
theorem B1509059 : Blo 1508951 1509059 := bstep (se 1 (by rfl) ⟨1131794, by rfl⟩ : syracuseStep 1509059 = 2263589) B2263589
theorem B1509075 : Blo 1508951 1509075 := bstep (se 1 (by rfl) ⟨1131806, by rfl⟩ : syracuseStep 1509075 = 2263613) B2263613
theorem B1509091 : Blo 1508951 1509091 := bstep (se 1 (by rfl) ⟨1131818, by rfl⟩ : syracuseStep 1509091 = 2263637) B2263637
theorem B3270385 : Blo 1508951 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B1509107 : Blo 1508951 1509107 := bstep (se 1 (by rfl) ⟨1131830, by rfl⟩ : syracuseStep 1509107 = 2263661) B2263661
theorem B1509123 : Blo 1508951 1509123 := bstep (se 1 (by rfl) ⟨1131842, by rfl⟩ : syracuseStep 1509123 = 2263685) B2263685
theorem B7644941 : Blo 1508951 7644941 := bstep (se 3 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 7644941 = 2866853) B2866853
theorem B1509139 : Blo 1508951 1509139 := bstep (se 1 (by rfl) ⟨1131854, by rfl⟩ : syracuseStep 1509139 = 2263709) B2263709
theorem B1509155 : Blo 1508951 1509155 := bstep (se 1 (by rfl) ⟨1131866, by rfl⟩ : syracuseStep 1509155 = 2263733) B2263733
theorem B2295587 : Blo 1508951 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B1509171 : Blo 1508951 1509171 := bstep (se 1 (by rfl) ⟨1131878, by rfl⟩ : syracuseStep 1509171 = 2263757) B2263757
theorem B2549569 : Blo 1508951 2549569 := bstep (se 2 (by rfl) ⟨956088, by rfl⟩ : syracuseStep 2549569 = 1912177) B1912177
theorem B1509187 : Blo 1508951 1509187 := bstep (se 1 (by rfl) ⟨1131890, by rfl⟩ : syracuseStep 1509187 = 2263781) B2263781
theorem B2041667 : Blo 1508951 2041667 := bstep (se 1 (by rfl) ⟨1531250, by rfl⟩ : syracuseStep 2041667 = 3062501) B3062501
theorem B1509203 : Blo 1508951 1509203 := bstep (se 1 (by rfl) ⟨1131902, by rfl⟩ : syracuseStep 1509203 = 2263805) B2263805
theorem B1509219 : Blo 1508951 1509219 := bstep (se 1 (by rfl) ⟨1131914, by rfl⟩ : syracuseStep 1509219 = 2263829) B2263829
theorem B2549603 : Blo 1508951 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B1509235 : Blo 1508951 1509235 := bstep (se 1 (by rfl) ⟨1131926, by rfl⟩ : syracuseStep 1509235 = 2263853) B2263853
theorem B5097329 : Blo 1508951 5097329 := bstep (se 2 (by rfl) ⟨1911498, by rfl⟩ : syracuseStep 5097329 = 3822997) B3822997
theorem B1509251 : Blo 1508951 1509251 := bstep (se 1 (by rfl) ⟨1131938, by rfl⟩ : syracuseStep 1509251 = 2263877) B2263877
theorem B2295697 : Blo 1508951 2295697 := bstep (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) B1721773
theorem B4081553 : Blo 1508951 4081553 := bstep (se 2 (by rfl) ⟨1530582, by rfl⟩ : syracuseStep 4081553 = 3061165) B3061165
theorem B1697683 : Blo 1508951 1697683 := bstep (se 1 (by rfl) ⟨1273262, by rfl⟩ : syracuseStep 1697683 = 2546525) B2546525
theorem B1509267 : Blo 1508951 1509267 := bstep (se 1 (by rfl) ⟨1131950, by rfl⟩ : syracuseStep 1509267 = 2263901) B2263901
theorem B1509283 : Blo 1508951 1509283 := bstep (se 1 (by rfl) ⟨1131962, by rfl⟩ : syracuseStep 1509283 = 2263925) B2263925
theorem B1509299 : Blo 1508951 1509299 := bstep (se 1 (by rfl) ⟨1131974, by rfl⟩ : syracuseStep 1509299 = 2263949) B2263949
theorem B1509315 : Blo 1508951 1509315 := bstep (se 1 (by rfl) ⟨1131986, by rfl⟩ : syracuseStep 1509315 = 2263973) B2263973
theorem B1509331 : Blo 1508951 1509331 := bstep (se 1 (by rfl) ⟨1131998, by rfl⟩ : syracuseStep 1509331 = 2263997) B2263997
theorem B1509347 : Blo 1508951 1509347 := bstep (se 1 (by rfl) ⟨1132010, by rfl⟩ : syracuseStep 1509347 = 2264021) B2264021
theorem B2549731 : Blo 1508951 2549731 := bstep (se 1 (by rfl) ⟨1912298, by rfl⟩ : syracuseStep 2549731 = 3824597) B3824597
theorem B1509363 : Blo 1508951 1509363 := bstep (se 1 (by rfl) ⟨1132022, by rfl⟩ : syracuseStep 1509363 = 2264045) B2264045
theorem B1509379 : Blo 1508951 1509379 := bstep (se 1 (by rfl) ⟨1132034, by rfl⟩ : syracuseStep 1509379 = 2264069) B2264069
theorem B1509395 : Blo 1508951 1509395 := bstep (se 1 (by rfl) ⟨1132046, by rfl⟩ : syracuseStep 1509395 = 2264093) B2264093
theorem B1697827 : Blo 1508951 1697827 := bstep (se 1 (by rfl) ⟨1273370, by rfl⟩ : syracuseStep 1697827 = 2546741) B2546741
theorem B1509411 : Blo 1508951 1509411 := bstep (se 1 (by rfl) ⟨1132058, by rfl⟩ : syracuseStep 1509411 = 2264117) B2264117
theorem B4589617 : Blo 1508951 4589617 := bstep (se 2 (by rfl) ⟨1721106, by rfl⟩ : syracuseStep 4589617 = 3442213) B3442213
theorem B1509427 : Blo 1508951 1509427 := bstep (se 1 (by rfl) ⟨1132070, by rfl⟩ : syracuseStep 1509427 = 2264141) B2264141
theorem B17197109 : Blo 1508951 17197109 := bstep (se 5 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 17197109 = 1612229) B1612229
theorem B1509443 : Blo 1508951 1509443 := bstep (se 1 (by rfl) ⟨1132082, by rfl⟩ : syracuseStep 1509443 = 2264165) B2264165
theorem B1509459 : Blo 1508951 1509459 := bstep (se 1 (by rfl) ⟨1132094, by rfl⟩ : syracuseStep 1509459 = 2264189) B2264189
theorem B1509475 : Blo 1508951 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B13076579 : Blo 1508951 13076579 := bstep (se 1 (by rfl) ⟨9807434, by rfl⟩ : syracuseStep 13076579 = 19614869) B19614869
theorem B1509491 : Blo 1508951 1509491 := bstep (se 1 (by rfl) ⟨1132118, by rfl⟩ : syracuseStep 1509491 = 2264237) B2264237
theorem B1509507 : Blo 1508951 1509507 := bstep (se 1 (by rfl) ⟨1132130, by rfl⟩ : syracuseStep 1509507 = 2264261) B2264261
theorem B1509523 : Blo 1508951 1509523 := bstep (se 1 (by rfl) ⟨1132142, by rfl⟩ : syracuseStep 1509523 = 2264285) B2264285
theorem B1509539 : Blo 1508951 1509539 := bstep (se 1 (by rfl) ⟨1132154, by rfl⟩ : syracuseStep 1509539 = 2264309) B2264309
theorem B1910947 : Blo 1508951 1910947 := bstep (se 1 (by rfl) ⟨1433210, by rfl⟩ : syracuseStep 1910947 = 2866421) B2866421
theorem B1697971 : Blo 1508951 1697971 := bstep (se 1 (by rfl) ⟨1273478, by rfl⟩ : syracuseStep 1697971 = 2546957) B2546957
theorem B1509555 : Blo 1508951 1509555 := bstep (se 1 (by rfl) ⟨1132166, by rfl⟩ : syracuseStep 1509555 = 2264333) B2264333
theorem B1509571 : Blo 1508951 1509571 := bstep (se 1 (by rfl) ⟨1132178, by rfl⟩ : syracuseStep 1509571 = 2264357) B2264357
theorem B5736653 : Blo 1508951 5736653 := bstep (se 3 (by rfl) ⟨1075622, by rfl⟩ : syracuseStep 5736653 = 2151245) B2151245
theorem B1509587 : Blo 1508951 1509587 := bstep (se 1 (by rfl) ⟨1132190, by rfl⟩ : syracuseStep 1509587 = 2264381) B2264381
theorem B1509603 : Blo 1508951 1509603 := bstep (se 1 (by rfl) ⟨1132202, by rfl⟩ : syracuseStep 1509603 = 2264405) B2264405
theorem B1509619 : Blo 1508951 1509619 := bstep (se 1 (by rfl) ⟨1132214, by rfl⟩ : syracuseStep 1509619 = 2264429) B2264429
theorem B1509635 : Blo 1508951 1509635 := bstep (se 1 (by rfl) ⟨1132226, by rfl⟩ : syracuseStep 1509635 = 2264453) B2264453
theorem B1911043 : Blo 1508951 1911043 := bstep (se 1 (by rfl) ⟨1433282, by rfl⟩ : syracuseStep 1911043 = 2866565) B2866565
theorem B1509651 : Blo 1508951 1509651 := bstep (se 1 (by rfl) ⟨1132238, by rfl⟩ : syracuseStep 1509651 = 2264477) B2264477
theorem B1509667 : Blo 1508951 1509667 := bstep (se 1 (by rfl) ⟨1132250, by rfl⟩ : syracuseStep 1509667 = 2264501) B2264501
theorem B6121763 : Blo 1508951 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B1509683 : Blo 1508951 1509683 := bstep (se 1 (by rfl) ⟨1132262, by rfl⟩ : syracuseStep 1509683 = 2264525) B2264525
theorem B1698115 : Blo 1508951 1698115 := bstep (se 1 (by rfl) ⟨1273586, by rfl⟩ : syracuseStep 1698115 = 2547173) B2547173
theorem B1509699 : Blo 1508951 1509699 := bstep (se 1 (by rfl) ⟨1132274, by rfl⟩ : syracuseStep 1509699 = 2264549) B2264549
theorem B1509715 : Blo 1508951 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B1509731 : Blo 1508951 1509731 := bstep (se 1 (by rfl) ⟨1132298, by rfl⟩ : syracuseStep 1509731 = 2264597) B2264597
theorem B1509747 : Blo 1508951 1509747 := bstep (se 1 (by rfl) ⟨1132310, by rfl⟩ : syracuseStep 1509747 = 2264621) B2264621
theorem B2263427 : Blo 1508951 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B1509763 : Blo 1508951 1509763 := bstep (se 1 (by rfl) ⟨1132322, by rfl⟩ : syracuseStep 1509763 = 2264645) B2264645
theorem B2419075 : Blo 1508951 2419075 := bstep (se 1 (by rfl) ⟨1814306, by rfl⟩ : syracuseStep 2419075 = 3628613) B3628613
theorem B5097869 : Blo 1508951 5097869 := bstep (se 3 (by rfl) ⟨955850, by rfl⟩ : syracuseStep 5097869 = 1911701) B1911701
theorem B1509779 : Blo 1508951 1509779 := bstep (se 1 (by rfl) ⟨1132334, by rfl⟩ : syracuseStep 1509779 = 2264669) B2264669
theorem B2263457 : Blo 1508951 2263457 := bstep (se 2 (by rfl) ⟨848796, by rfl⟩ : syracuseStep 2263457 = 1697593) B1697593
theorem B1509795 : Blo 1508951 1509795 := bstep (se 1 (by rfl) ⟨1132346, by rfl⟩ : syracuseStep 1509795 = 2264693) B2264693
theorem B2263475 : Blo 1508951 2263475 := bstep (se 1 (by rfl) ⟨1697606, by rfl⟩ : syracuseStep 2263475 = 3395213) B3395213
theorem B1509811 : Blo 1508951 1509811 := bstep (se 1 (by rfl) ⟨1132358, by rfl⟩ : syracuseStep 1509811 = 2264717) B2264717
theorem B1509827 : Blo 1508951 1509827 := bstep (se 1 (by rfl) ⟨1132370, by rfl⟩ : syracuseStep 1509827 = 2264741) B2264741
theorem B2419139 : Blo 1508951 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B5097923 : Blo 1508951 5097923 := bstep (se 1 (by rfl) ⟨3823442, by rfl⟩ : syracuseStep 5097923 = 7646885) B7646885
theorem B2263505 : Blo 1508951 2263505 := bstep (se 2 (by rfl) ⟨848814, by rfl⟩ : syracuseStep 2263505 = 1697629) B1697629
theorem B1698259 : Blo 1508951 1698259 := bstep (se 1 (by rfl) ⟨1273694, by rfl⟩ : syracuseStep 1698259 = 2547389) B2547389
theorem B1509843 : Blo 1508951 1509843 := bstep (se 1 (by rfl) ⟨1132382, by rfl⟩ : syracuseStep 1509843 = 2264765) B2264765
theorem B2263523 : Blo 1508951 2263523 := bstep (se 1 (by rfl) ⟨1697642, by rfl⟩ : syracuseStep 2263523 = 3395285) B3395285
theorem B1509859 : Blo 1508951 1509859 := bstep (se 1 (by rfl) ⟨1132394, by rfl⟩ : syracuseStep 1509859 = 2264789) B2264789
theorem B1509875 : Blo 1508951 1509875 := bstep (se 1 (by rfl) ⟨1132406, by rfl⟩ : syracuseStep 1509875 = 2264813) B2264813
theorem B2263553 : Blo 1508951 2263553 := bstep (se 2 (by rfl) ⟨848832, by rfl⟩ : syracuseStep 2263553 = 1697665) B1697665
theorem B1509891 : Blo 1508951 1509891 := bstep (se 1 (by rfl) ⟨1132418, by rfl⟩ : syracuseStep 1509891 = 2264837) B2264837
theorem B2263571 : Blo 1508951 2263571 := bstep (se 1 (by rfl) ⟨1697678, by rfl⟩ : syracuseStep 2263571 = 3395357) B3395357
theorem B1509907 : Blo 1508951 1509907 := bstep (se 1 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 1509907 = 2264861) B2264861
theorem B8596003 : Blo 1508951 8596003 := bstep (se 1 (by rfl) ⟨6447002, by rfl⟩ : syracuseStep 8596003 = 12894005) B12894005
theorem B1509923 : Blo 1508951 1509923 := bstep (se 1 (by rfl) ⟨1132442, by rfl⟩ : syracuseStep 1509923 = 2264885) B2264885
theorem B2722339 : Blo 1508951 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B2263601 : Blo 1508951 2263601 := bstep (se 2 (by rfl) ⟨848850, by rfl⟩ : syracuseStep 2263601 = 1697701) B1697701
theorem B3820081 : Blo 1508951 3820081 := bstep (se 2 (by rfl) ⟨1432530, by rfl⟩ : syracuseStep 3820081 = 2865061) B2865061
theorem B1509939 : Blo 1508951 1509939 := bstep (se 1 (by rfl) ⟨1132454, by rfl⟩ : syracuseStep 1509939 = 2264909) B2264909
theorem B2263619 : Blo 1508951 2263619 := bstep (se 1 (by rfl) ⟨1697714, by rfl⟩ : syracuseStep 2263619 = 3395429) B3395429
theorem B1509955 : Blo 1508951 1509955 := bstep (se 1 (by rfl) ⟨1132466, by rfl⟩ : syracuseStep 1509955 = 2264933) B2264933
theorem B1509971 : Blo 1508951 1509971 := bstep (se 1 (by rfl) ⟨1132478, by rfl⟩ : syracuseStep 1509971 = 2264957) B2264957
theorem B2263649 : Blo 1508951 2263649 := bstep (se 2 (by rfl) ⟨848868, by rfl⟩ : syracuseStep 2263649 = 1697737) B1697737
theorem B1698403 : Blo 1508951 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1509987 : Blo 1508951 1509987 := bstep (se 1 (by rfl) ⟨1132490, by rfl⟩ : syracuseStep 1509987 = 2264981) B2264981
theorem B4082275 : Blo 1508951 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B11463281 : Blo 1508951 11463281 := bstep (se 2 (by rfl) ⟨4298730, by rfl⟩ : syracuseStep 11463281 = 8597461) B8597461
theorem B2263667 : Blo 1508951 2263667 := bstep (se 1 (by rfl) ⟨1697750, by rfl⟩ : syracuseStep 2263667 = 3395501) B3395501
theorem B1510003 : Blo 1508951 1510003 := bstep (se 1 (by rfl) ⟨1132502, by rfl⟩ : syracuseStep 1510003 = 2265005) B2265005
theorem B1510019 : Blo 1508951 1510019 := bstep (se 1 (by rfl) ⟨1132514, by rfl⟩ : syracuseStep 1510019 = 2265029) B2265029
theorem B2263697 : Blo 1508951 2263697 := bstep (se 2 (by rfl) ⟨848886, by rfl⟩ : syracuseStep 2263697 = 1697773) B1697773
theorem B2583185 : Blo 1508951 2583185 := bstep (se 2 (by rfl) ⟨968694, by rfl⟩ : syracuseStep 2583185 = 1937389) B1937389
theorem B1510035 : Blo 1508951 1510035 := bstep (se 1 (by rfl) ⟨1132526, by rfl⟩ : syracuseStep 1510035 = 2265053) B2265053
theorem B2263715 : Blo 1508951 2263715 := bstep (se 1 (by rfl) ⟨1697786, by rfl⟩ : syracuseStep 2263715 = 3395573) B3395573
theorem B1510051 : Blo 1508951 1510051 := bstep (se 1 (by rfl) ⟨1132538, by rfl⟩ : syracuseStep 1510051 = 2265077) B2265077
theorem B1510067 : Blo 1508951 1510067 := bstep (se 1 (by rfl) ⟨1132550, by rfl⟩ : syracuseStep 1510067 = 2265101) B2265101
theorem B2263745 : Blo 1508951 2263745 := bstep (se 2 (by rfl) ⟨848904, by rfl⟩ : syracuseStep 2263745 = 1697809) B1697809
theorem B1510083 : Blo 1508951 1510083 := bstep (se 1 (by rfl) ⟨1132562, by rfl⟩ : syracuseStep 1510083 = 2265125) B2265125
theorem B5098193 : Blo 1508951 5098193 := bstep (se 2 (by rfl) ⟨1911822, by rfl⟩ : syracuseStep 5098193 = 3823645) B3823645
theorem B2263763 : Blo 1508951 2263763 := bstep (se 1 (by rfl) ⟨1697822, by rfl⟩ : syracuseStep 2263763 = 3395645) B3395645
theorem B1510099 : Blo 1508951 1510099 := bstep (se 1 (by rfl) ⟨1132574, by rfl⟩ : syracuseStep 1510099 = 2265149) B2265149
theorem B1510115 : Blo 1508951 1510115 := bstep (se 1 (by rfl) ⟨1132586, by rfl⟩ : syracuseStep 1510115 = 2265173) B2265173
theorem B2263793 : Blo 1508951 2263793 := bstep (se 2 (by rfl) ⟨848922, by rfl⟩ : syracuseStep 2263793 = 1697845) B1697845
theorem B1698547 : Blo 1508951 1698547 := bstep (se 1 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 1698547 = 2547821) B2547821
theorem B1510131 : Blo 1508951 1510131 := bstep (se 1 (by rfl) ⟨1132598, by rfl⟩ : syracuseStep 1510131 = 2265197) B2265197
theorem B1911539 : Blo 1508951 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B2263811 : Blo 1508951 2263811 := bstep (se 1 (by rfl) ⟨1697858, by rfl⟩ : syracuseStep 2263811 = 3395717) B3395717
theorem B1510147 : Blo 1508951 1510147 := bstep (se 1 (by rfl) ⟨1132610, by rfl⟩ : syracuseStep 1510147 = 2265221) B2265221
theorem B1510163 : Blo 1508951 1510163 := bstep (se 1 (by rfl) ⟨1132622, by rfl⟩ : syracuseStep 1510163 = 2265245) B2265245
theorem B2263841 : Blo 1508951 2263841 := bstep (se 2 (by rfl) ⟨848940, by rfl⟩ : syracuseStep 2263841 = 1697881) B1697881
theorem B1510179 : Blo 1508951 1510179 := bstep (se 1 (by rfl) ⟨1132634, by rfl⟩ : syracuseStep 1510179 = 2265269) B2265269
theorem B2263859 : Blo 1508951 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B1510195 : Blo 1508951 1510195 := bstep (se 1 (by rfl) ⟨1132646, by rfl⟩ : syracuseStep 1510195 = 2265293) B2265293
theorem B3820355 : Blo 1508951 3820355 := bstep (se 1 (by rfl) ⟨2865266, by rfl⟩ : syracuseStep 3820355 = 5730533) B5730533
theorem B1510211 : Blo 1508951 1510211 := bstep (se 1 (by rfl) ⟨1132658, by rfl⟩ : syracuseStep 1510211 = 2265317) B2265317
theorem B2263889 : Blo 1508951 2263889 := bstep (se 2 (by rfl) ⟨848958, by rfl⟩ : syracuseStep 2263889 = 1697917) B1697917
theorem B1510227 : Blo 1508951 1510227 := bstep (se 1 (by rfl) ⟨1132670, by rfl⟩ : syracuseStep 1510227 = 2265341) B2265341
theorem B2263907 : Blo 1508951 2263907 := bstep (se 1 (by rfl) ⟨1697930, by rfl⟩ : syracuseStep 2263907 = 3395861) B3395861
theorem B18361187 : Blo 1508951 18361187 := bstep (se 1 (by rfl) ⟨13770890, by rfl⟩ : syracuseStep 18361187 = 27541781) B27541781
theorem B1510243 : Blo 1508951 1510243 := bstep (se 1 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 1510243 = 2265365) B2265365
theorem B9677681 : Blo 1508951 9677681 := bstep (se 2 (by rfl) ⟨3629130, by rfl⟩ : syracuseStep 9677681 = 7258261) B7258261
theorem B1510259 : Blo 1508951 1510259 := bstep (se 1 (by rfl) ⟨1132694, by rfl⟩ : syracuseStep 1510259 = 2265389) B2265389
theorem B2263937 : Blo 1508951 2263937 := bstep (se 2 (by rfl) ⟨848976, by rfl⟩ : syracuseStep 2263937 = 1697953) B1697953
theorem B1698691 : Blo 1508951 1698691 := bstep (se 1 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 1698691 = 2548037) B2548037
theorem B1510275 : Blo 1508951 1510275 := bstep (se 1 (by rfl) ⟨1132706, by rfl⟩ : syracuseStep 1510275 = 2265413) B2265413
theorem B2263955 : Blo 1508951 2263955 := bstep (se 1 (by rfl) ⟨1697966, by rfl⟩ : syracuseStep 2263955 = 3395933) B3395933
theorem B1510291 : Blo 1508951 1510291 := bstep (se 1 (by rfl) ⟨1132718, by rfl⟩ : syracuseStep 1510291 = 2265437) B2265437
theorem B1510307 : Blo 1508951 1510307 := bstep (se 1 (by rfl) ⟨1132730, by rfl⟩ : syracuseStep 1510307 = 2265461) B2265461
theorem B2263985 : Blo 1508951 2263985 := bstep (se 2 (by rfl) ⟨848994, by rfl⟩ : syracuseStep 2263985 = 1697989) B1697989
theorem B1510323 : Blo 1508951 1510323 := bstep (se 1 (by rfl) ⟨1132742, by rfl⟩ : syracuseStep 1510323 = 2265485) B2265485
theorem B2264003 : Blo 1508951 2264003 := bstep (se 1 (by rfl) ⟨1698002, by rfl⟩ : syracuseStep 2264003 = 3396005) B3396005
theorem B1510339 : Blo 1508951 1510339 := bstep (se 1 (by rfl) ⟨1132754, by rfl⟩ : syracuseStep 1510339 = 2265509) B2265509
theorem B1510355 : Blo 1508951 1510355 := bstep (se 1 (by rfl) ⟨1132766, by rfl⟩ : syracuseStep 1510355 = 2265533) B2265533
theorem B2264033 : Blo 1508951 2264033 := bstep (se 2 (by rfl) ⟨849012, by rfl⟩ : syracuseStep 2264033 = 1698025) B1698025
theorem B5164003 : Blo 1508951 5164003 := bstep (se 1 (by rfl) ⟨3873002, by rfl⟩ : syracuseStep 5164003 = 7746005) B7746005
theorem B1510371 : Blo 1508951 1510371 := bstep (se 1 (by rfl) ⟨1132778, by rfl⟩ : syracuseStep 1510371 = 2265557) B2265557
theorem B13781987 : Blo 1508951 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B2264051 : Blo 1508951 2264051 := bstep (se 1 (by rfl) ⟨1698038, by rfl⟩ : syracuseStep 2264051 = 3396077) B3396077
theorem B1510387 : Blo 1508951 1510387 := bstep (se 1 (by rfl) ⟨1132790, by rfl⟩ : syracuseStep 1510387 = 2265581) B2265581
theorem B3820547 : Blo 1508951 3820547 := bstep (se 1 (by rfl) ⟨2865410, by rfl⟩ : syracuseStep 3820547 = 5730821) B5730821
theorem B1510403 : Blo 1508951 1510403 := bstep (se 1 (by rfl) ⟨1132802, by rfl⟩ : syracuseStep 1510403 = 2265605) B2265605
theorem B2264081 : Blo 1508951 2264081 := bstep (se 2 (by rfl) ⟨849030, by rfl⟩ : syracuseStep 2264081 = 1698061) B1698061
theorem B1698835 : Blo 1508951 1698835 := bstep (se 1 (by rfl) ⟨1274126, by rfl⟩ : syracuseStep 1698835 = 2548253) B2548253
theorem B1510419 : Blo 1508951 1510419 := bstep (se 1 (by rfl) ⟨1132814, by rfl⟩ : syracuseStep 1510419 = 2265629) B2265629
theorem B2264099 : Blo 1508951 2264099 := bstep (se 1 (by rfl) ⟨1698074, by rfl⟩ : syracuseStep 2264099 = 3396149) B3396149
theorem B2149411 : Blo 1508951 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B1510435 : Blo 1508951 1510435 := bstep (se 1 (by rfl) ⟨1132826, by rfl⟩ : syracuseStep 1510435 = 2265653) B2265653
theorem B4590637 : Blo 1508951 4590637 := bstep (se 3 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 4590637 = 1721489) B1721489
theorem B8596529 : Blo 1508951 8596529 := bstep (se 2 (by rfl) ⟨3223698, by rfl⟩ : syracuseStep 8596529 = 6447397) B6447397
theorem B1510451 : Blo 1508951 1510451 := bstep (se 1 (by rfl) ⟨1132838, by rfl⟩ : syracuseStep 1510451 = 2265677) B2265677
theorem B2264129 : Blo 1508951 2264129 := bstep (se 2 (by rfl) ⟨849048, by rfl⟩ : syracuseStep 2264129 = 1698097) B1698097
theorem B1510467 : Blo 1508951 1510467 := bstep (se 1 (by rfl) ⟨1132850, by rfl⟩ : syracuseStep 1510467 = 2265701) B2265701
theorem B2264147 : Blo 1508951 2264147 := bstep (se 1 (by rfl) ⟨1698110, by rfl⟩ : syracuseStep 2264147 = 3396221) B3396221
theorem B1510483 : Blo 1508951 1510483 := bstep (se 1 (by rfl) ⟨1132862, by rfl⟩ : syracuseStep 1510483 = 2265725) B2265725
theorem B10882147 : Blo 1508951 10882147 := bstep (se 1 (by rfl) ⟨8161610, by rfl⟩ : syracuseStep 10882147 = 16323221) B16323221
theorem B1510499 : Blo 1508951 1510499 := bstep (se 1 (by rfl) ⟨1132874, by rfl⟩ : syracuseStep 1510499 = 2265749) B2265749
theorem B5729393 : Blo 1508951 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B2264177 : Blo 1508951 2264177 := bstep (se 2 (by rfl) ⟨849066, by rfl⟩ : syracuseStep 2264177 = 1698133) B1698133
theorem B1510515 : Blo 1508951 1510515 := bstep (se 1 (by rfl) ⟨1132886, by rfl⟩ : syracuseStep 1510515 = 2265773) B2265773
theorem B2264195 : Blo 1508951 2264195 := bstep (se 1 (by rfl) ⟨1698146, by rfl⟩ : syracuseStep 2264195 = 3396293) B3396293
theorem B1510531 : Blo 1508951 1510531 := bstep (se 1 (by rfl) ⟨1132898, by rfl⟩ : syracuseStep 1510531 = 2265797) B2265797
theorem B4361357 : Blo 1508951 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B1510547 : Blo 1508951 1510547 := bstep (se 1 (by rfl) ⟨1132910, by rfl⟩ : syracuseStep 1510547 = 2265821) B2265821
theorem B2264225 : Blo 1508951 2264225 := bstep (se 2 (by rfl) ⟨849084, by rfl⟩ : syracuseStep 2264225 = 1698169) B1698169
theorem B1698979 : Blo 1508951 1698979 := bstep (se 1 (by rfl) ⟨1274234, by rfl⟩ : syracuseStep 1698979 = 2548469) B2548469
theorem B1510563 : Blo 1508951 1510563 := bstep (se 1 (by rfl) ⟨1132922, by rfl⟩ : syracuseStep 1510563 = 2265845) B2265845
theorem B6450353 : Blo 1508951 6450353 := bstep (se 2 (by rfl) ⟨2418882, by rfl⟩ : syracuseStep 6450353 = 4837765) B4837765
theorem B2264243 : Blo 1508951 2264243 := bstep (se 1 (by rfl) ⟨1698182, by rfl⟩ : syracuseStep 2264243 = 3396365) B3396365
theorem B1510579 : Blo 1508951 1510579 := bstep (se 1 (by rfl) ⟨1132934, by rfl⟩ : syracuseStep 1510579 = 2265869) B2265869
theorem B1510595 : Blo 1508951 1510595 := bstep (se 1 (by rfl) ⟨1132946, by rfl⟩ : syracuseStep 1510595 = 2265893) B2265893
theorem B2264273 : Blo 1508951 2264273 := bstep (se 2 (by rfl) ⟨849102, by rfl⟩ : syracuseStep 2264273 = 1698205) B1698205
theorem B1510611 : Blo 1508951 1510611 := bstep (se 1 (by rfl) ⟨1132958, by rfl⟩ : syracuseStep 1510611 = 2265917) B2265917
theorem B7351523 : Blo 1508951 7351523 := bstep (se 1 (by rfl) ⟨5513642, by rfl⟩ : syracuseStep 7351523 = 11027285) B11027285
theorem B2264291 : Blo 1508951 2264291 := bstep (se 1 (by rfl) ⟨1698218, by rfl⟩ : syracuseStep 2264291 = 3396437) B3396437
theorem B1510627 : Blo 1508951 1510627 := bstep (se 1 (by rfl) ⟨1132970, by rfl⟩ : syracuseStep 1510627 = 2265941) B2265941
theorem B5098733 : Blo 1508951 5098733 := bstep (se 3 (by rfl) ⟨956012, by rfl⟩ : syracuseStep 5098733 = 1912025) B1912025
theorem B1510643 : Blo 1508951 1510643 := bstep (se 1 (by rfl) ⟨1132982, by rfl⟩ : syracuseStep 1510643 = 2265965) B2265965
theorem B2264321 : Blo 1508951 2264321 := bstep (se 2 (by rfl) ⟨849120, by rfl⟩ : syracuseStep 2264321 = 1698241) B1698241
theorem B4836611 : Blo 1508951 4836611 := bstep (se 1 (by rfl) ⟨3627458, by rfl⟩ : syracuseStep 4836611 = 7254917) B7254917
theorem B1510659 : Blo 1508951 1510659 := bstep (se 1 (by rfl) ⟨1132994, by rfl⟩ : syracuseStep 1510659 = 2265989) B2265989
theorem B2264339 : Blo 1508951 2264339 := bstep (se 1 (by rfl) ⟨1698254, by rfl⟩ : syracuseStep 2264339 = 3396509) B3396509
theorem B1510675 : Blo 1508951 1510675 := bstep (se 1 (by rfl) ⟨1133006, by rfl⟩ : syracuseStep 1510675 = 2266013) B2266013
theorem B1510691 : Blo 1508951 1510691 := bstep (se 1 (by rfl) ⟨1133018, by rfl⟩ : syracuseStep 1510691 = 2266037) B2266037
theorem B5098787 : Blo 1508951 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B4082989 : Blo 1508951 4082989 := bstep (se 3 (by rfl) ⟨765560, by rfl⟩ : syracuseStep 4082989 = 1531121) B1531121
theorem B2264369 : Blo 1508951 2264369 := bstep (se 2 (by rfl) ⟨849138, by rfl⟩ : syracuseStep 2264369 = 1698277) B1698277
theorem B1699123 : Blo 1508951 1699123 := bstep (se 1 (by rfl) ⟨1274342, by rfl⟩ : syracuseStep 1699123 = 2548685) B2548685
theorem B1510707 : Blo 1508951 1510707 := bstep (se 1 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 1510707 = 2266061) B2266061
theorem B2264387 : Blo 1508951 2264387 := bstep (se 1 (by rfl) ⟨1698290, by rfl⟩ : syracuseStep 2264387 = 3396581) B3396581
theorem B1510723 : Blo 1508951 1510723 := bstep (se 1 (by rfl) ⟨1133042, by rfl⟩ : syracuseStep 1510723 = 2266085) B2266085
theorem B1510739 : Blo 1508951 1510739 := bstep (se 1 (by rfl) ⟨1133054, by rfl⟩ : syracuseStep 1510739 = 2266109) B2266109
theorem B2264417 : Blo 1508951 2264417 := bstep (se 2 (by rfl) ⟨849156, by rfl⟩ : syracuseStep 2264417 = 1698313) B1698313
theorem B1510755 : Blo 1508951 1510755 := bstep (se 1 (by rfl) ⟨1133066, by rfl⟩ : syracuseStep 1510755 = 2266133) B2266133
theorem B2264435 : Blo 1508951 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B1510771 : Blo 1508951 1510771 := bstep (se 1 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 1510771 = 2266157) B2266157
theorem B1510787 : Blo 1508951 1510787 := bstep (se 1 (by rfl) ⟨1133090, by rfl⟩ : syracuseStep 1510787 = 2266181) B2266181
theorem B2264465 : Blo 1508951 2264465 := bstep (se 2 (by rfl) ⟨849174, by rfl⟩ : syracuseStep 2264465 = 1698349) B1698349
theorem B2420113 : Blo 1508951 2420113 := bstep (se 2 (by rfl) ⟨907542, by rfl⟩ : syracuseStep 2420113 = 1815085) B1815085
theorem B1510803 : Blo 1508951 1510803 := bstep (se 1 (by rfl) ⟨1133102, by rfl⟩ : syracuseStep 1510803 = 2266205) B2266205
theorem B2264483 : Blo 1508951 2264483 := bstep (se 1 (by rfl) ⟨1698362, by rfl⟩ : syracuseStep 2264483 = 3396725) B3396725
theorem B1510819 : Blo 1508951 1510819 := bstep (se 1 (by rfl) ⟨1133114, by rfl⟩ : syracuseStep 1510819 = 2266229) B2266229
theorem B1510835 : Blo 1508951 1510835 := bstep (se 1 (by rfl) ⟨1133126, by rfl⟩ : syracuseStep 1510835 = 2266253) B2266253
theorem B1912243 : Blo 1508951 1912243 := bstep (se 1 (by rfl) ⟨1434182, by rfl⟩ : syracuseStep 1912243 = 2868365) B2868365
theorem B2264513 : Blo 1508951 2264513 := bstep (se 2 (by rfl) ⟨849192, by rfl⟩ : syracuseStep 2264513 = 1698385) B1698385
theorem B1699267 : Blo 1508951 1699267 := bstep (se 1 (by rfl) ⟨1274450, by rfl⟩ : syracuseStep 1699267 = 2548901) B2548901
theorem B1510851 : Blo 1508951 1510851 := bstep (se 1 (by rfl) ⟨1133138, by rfl⟩ : syracuseStep 1510851 = 2266277) B2266277
theorem B2264531 : Blo 1508951 2264531 := bstep (se 1 (by rfl) ⟨1698398, by rfl⟩ : syracuseStep 2264531 = 3396797) B3396797
theorem B1510867 : Blo 1508951 1510867 := bstep (se 1 (by rfl) ⟨1133150, by rfl⟩ : syracuseStep 1510867 = 2266301) B2266301
theorem B1510883 : Blo 1508951 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B2264561 : Blo 1508951 2264561 := bstep (se 2 (by rfl) ⟨849210, by rfl⟩ : syracuseStep 2264561 = 1698421) B1698421
theorem B10890737 : Blo 1508951 10890737 := bstep (se 2 (by rfl) ⟨4084026, by rfl⟩ : syracuseStep 10890737 = 8168053) B8168053
theorem B1510899 : Blo 1508951 1510899 := bstep (se 1 (by rfl) ⟨1133174, by rfl⟩ : syracuseStep 1510899 = 2266349) B2266349
theorem B2264579 : Blo 1508951 2264579 := bstep (se 1 (by rfl) ⟨1698434, by rfl⟩ : syracuseStep 2264579 = 3396869) B3396869
theorem B9186821 : Blo 1508951 9186821 := bstep (se 4 (by rfl) ⟨861264, by rfl⟩ : syracuseStep 9186821 = 1722529) B1722529
theorem B1510915 : Blo 1508951 1510915 := bstep (se 1 (by rfl) ⟨1133186, by rfl⟩ : syracuseStep 1510915 = 2266373) B2266373
theorem B1510931 : Blo 1508951 1510931 := bstep (se 1 (by rfl) ⟨1133198, by rfl⟩ : syracuseStep 1510931 = 2266397) B2266397
theorem B2264609 : Blo 1508951 2264609 := bstep (se 2 (by rfl) ⟨849228, by rfl⟩ : syracuseStep 2264609 = 1698457) B1698457
theorem B1510947 : Blo 1508951 1510947 := bstep (se 1 (by rfl) ⟨1133210, by rfl⟩ : syracuseStep 1510947 = 2266421) B2266421
theorem B5099057 : Blo 1508951 5099057 := bstep (se 2 (by rfl) ⟨1912146, by rfl⟩ : syracuseStep 5099057 = 3824293) B3824293
theorem B2264627 : Blo 1508951 2264627 := bstep (se 1 (by rfl) ⟨1698470, by rfl⟩ : syracuseStep 2264627 = 3396941) B3396941
theorem B2264657 : Blo 1508951 2264657 := bstep (se 2 (by rfl) ⟨849246, by rfl⟩ : syracuseStep 2264657 = 1698493) B1698493
theorem B1699411 : Blo 1508951 1699411 := bstep (se 1 (by rfl) ⟨1274558, by rfl⟩ : syracuseStep 1699411 = 2549117) B2549117
theorem B2264675 : Blo 1508951 2264675 := bstep (se 1 (by rfl) ⟨1698506, by rfl⟩ : syracuseStep 2264675 = 3397013) B3397013
theorem B2264705 : Blo 1508951 2264705 := bstep (se 2 (by rfl) ⟨849264, by rfl⟩ : syracuseStep 2264705 = 1698529) B1698529
theorem B2264723 : Blo 1508951 2264723 := bstep (se 1 (by rfl) ⟨1698542, by rfl⟩ : syracuseStep 2264723 = 3397085) B3397085
theorem B3395249 : Blo 1508951 3395249 := bstep (se 2 (by rfl) ⟨1273218, by rfl⟩ : syracuseStep 3395249 = 2546437) B2546437
theorem B2264753 : Blo 1508951 2264753 := bstep (se 2 (by rfl) ⟨849282, by rfl⟩ : syracuseStep 2264753 = 1698565) B1698565
theorem B4083377 : Blo 1508951 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B3395267 : Blo 1508951 3395267 := bstep (se 1 (by rfl) ⟨2546450, by rfl⟩ : syracuseStep 3395267 = 5092901) B5092901
theorem B2264771 : Blo 1508951 2264771 := bstep (se 1 (by rfl) ⟨1698578, by rfl⟩ : syracuseStep 2264771 = 3397157) B3397157
theorem B2264801 : Blo 1508951 2264801 := bstep (se 2 (by rfl) ⟨849300, by rfl⟩ : syracuseStep 2264801 = 1698601) B1698601
theorem B1699555 : Blo 1508951 1699555 := bstep (se 1 (by rfl) ⟨1274666, by rfl⟩ : syracuseStep 1699555 = 2549333) B2549333
theorem B15503089 : Blo 1508951 15503089 := bstep (se 2 (by rfl) ⟨5813658, by rfl⟩ : syracuseStep 15503089 = 11627317) B11627317
theorem B2264819 : Blo 1508951 2264819 := bstep (se 1 (by rfl) ⟨1698614, by rfl⟩ : syracuseStep 2264819 = 3397229) B3397229
theorem B5730061 : Blo 1508951 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B2264849 : Blo 1508951 2264849 := bstep (se 2 (by rfl) ⟨849318, by rfl⟩ : syracuseStep 2264849 = 1698637) B1698637
theorem B3223331 : Blo 1508951 3223331 := bstep (se 1 (by rfl) ⟨2417498, by rfl⟩ : syracuseStep 3223331 = 4834997) B4834997
theorem B6885155 : Blo 1508951 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B9563939 : Blo 1508951 9563939 := bstep (se 1 (by rfl) ⟨7172954, by rfl⟩ : syracuseStep 9563939 = 14345909) B14345909
theorem B2264867 : Blo 1508951 2264867 := bstep (se 1 (by rfl) ⟨1698650, by rfl⟩ : syracuseStep 2264867 = 3397301) B3397301
theorem B2264897 : Blo 1508951 2264897 := bstep (se 2 (by rfl) ⟨849336, by rfl⟩ : syracuseStep 2264897 = 1698673) B1698673
theorem B2264915 : Blo 1508951 2264915 := bstep (se 1 (by rfl) ⟨1698686, by rfl⟩ : syracuseStep 2264915 = 3397373) B3397373
theorem B4968305 : Blo 1508951 4968305 := bstep (se 2 (by rfl) ⟨1863114, by rfl⟩ : syracuseStep 4968305 = 3726229) B3726229
theorem B2264945 : Blo 1508951 2264945 := bstep (se 2 (by rfl) ⟨849354, by rfl⟩ : syracuseStep 2264945 = 1698709) B1698709
theorem B1699699 : Blo 1508951 1699699 := bstep (se 1 (by rfl) ⟨1274774, by rfl⟩ : syracuseStep 1699699 = 2549549) B2549549
theorem B2264963 : Blo 1508951 2264963 := bstep (se 1 (by rfl) ⟨1698722, by rfl⟩ : syracuseStep 2264963 = 3397445) B3397445
theorem B2264993 : Blo 1508951 2264993 := bstep (se 2 (by rfl) ⟨849372, by rfl⟩ : syracuseStep 2264993 = 1698745) B1698745
theorem B3821489 : Blo 1508951 3821489 := bstep (se 2 (by rfl) ⟨1433058, by rfl⟩ : syracuseStep 3821489 = 2866117) B2866117
theorem B2265011 : Blo 1508951 2265011 := bstep (se 1 (by rfl) ⟨1698758, by rfl⟩ : syracuseStep 2265011 = 3397517) B3397517
theorem B3395537 : Blo 1508951 3395537 := bstep (se 2 (by rfl) ⟨1273326, by rfl⟩ : syracuseStep 3395537 = 2546653) B2546653
theorem B2265041 : Blo 1508951 2265041 := bstep (se 2 (by rfl) ⟨849390, by rfl⟩ : syracuseStep 2265041 = 1698781) B1698781
theorem B3395555 : Blo 1508951 3395555 := bstep (se 1 (by rfl) ⟨2546666, by rfl⟩ : syracuseStep 3395555 = 5093333) B5093333
theorem B3821539 : Blo 1508951 3821539 := bstep (se 1 (by rfl) ⟨2866154, by rfl⟩ : syracuseStep 3821539 = 5732309) B5732309
theorem B2265059 : Blo 1508951 2265059 := bstep (se 1 (by rfl) ⟨1698794, by rfl⟩ : syracuseStep 2265059 = 3397589) B3397589
theorem B4419569 : Blo 1508951 4419569 := bstep (se 2 (by rfl) ⟨1657338, by rfl⟩ : syracuseStep 4419569 = 3314677) B3314677
theorem B2265089 : Blo 1508951 2265089 := bstep (se 2 (by rfl) ⟨849408, by rfl⟩ : syracuseStep 2265089 = 1698817) B1698817
theorem B5165059 : Blo 1508951 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B2265107 : Blo 1508951 2265107 := bstep (se 1 (by rfl) ⟨1698830, by rfl⟩ : syracuseStep 2265107 = 3397661) B3397661
theorem B2265137 : Blo 1508951 2265137 := bstep (se 2 (by rfl) ⟨849426, by rfl⟩ : syracuseStep 2265137 = 1698853) B1698853
theorem B2265155 : Blo 1508951 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B4837457 : Blo 1508951 4837457 := bstep (se 2 (by rfl) ⟨1814046, by rfl⟩ : syracuseStep 4837457 = 3628093) B3628093
theorem B2265185 : Blo 1508951 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B3821681 : Blo 1508951 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B2265203 : Blo 1508951 2265203 := bstep (se 1 (by rfl) ⟨1698902, by rfl⟩ : syracuseStep 2265203 = 3397805) B3397805
theorem B2265233 : Blo 1508951 2265233 := bstep (se 2 (by rfl) ⟨849462, by rfl⟩ : syracuseStep 2265233 = 1698925) B1698925
theorem B2150545 : Blo 1508951 2150545 := bstep (se 2 (by rfl) ⟨806454, by rfl⟩ : syracuseStep 2150545 = 1612909) B1612909
theorem B2265251 : Blo 1508951 2265251 := bstep (se 1 (by rfl) ⟨1698938, by rfl⟩ : syracuseStep 2265251 = 3397877) B3397877
theorem B2265281 : Blo 1508951 2265281 := bstep (se 2 (by rfl) ⟨849480, by rfl⟩ : syracuseStep 2265281 = 1698961) B1698961
theorem B2265299 : Blo 1508951 2265299 := bstep (se 1 (by rfl) ⟨1698974, by rfl⟩ : syracuseStep 2265299 = 3397949) B3397949
theorem B3395825 : Blo 1508951 3395825 := bstep (se 2 (by rfl) ⟨1273434, by rfl⟩ : syracuseStep 3395825 = 2546869) B2546869
theorem B3223793 : Blo 1508951 3223793 := bstep (se 2 (by rfl) ⟨1208922, by rfl⟩ : syracuseStep 3223793 = 2417845) B2417845
theorem B2265329 : Blo 1508951 2265329 := bstep (se 2 (by rfl) ⟨849498, by rfl⟩ : syracuseStep 2265329 = 1698997) B1698997
theorem B2150641 : Blo 1508951 2150641 := bstep (se 2 (by rfl) ⟨806490, by rfl⟩ : syracuseStep 2150641 = 1612981) B1612981
theorem B3395843 : Blo 1508951 3395843 := bstep (se 1 (by rfl) ⟨2546882, by rfl⟩ : syracuseStep 3395843 = 5093765) B5093765
theorem B2265347 : Blo 1508951 2265347 := bstep (se 1 (by rfl) ⟨1699010, by rfl⟩ : syracuseStep 2265347 = 3398021) B3398021
theorem B2265377 : Blo 1508951 2265377 := bstep (se 2 (by rfl) ⟨849516, by rfl⟩ : syracuseStep 2265377 = 1699033) B1699033
theorem B2265395 : Blo 1508951 2265395 := bstep (se 1 (by rfl) ⟨1699046, by rfl⟩ : syracuseStep 2265395 = 3398093) B3398093
theorem B2265425 : Blo 1508951 2265425 := bstep (se 2 (by rfl) ⟨849534, by rfl⟩ : syracuseStep 2265425 = 1699069) B1699069
theorem B2265443 : Blo 1508951 2265443 := bstep (se 1 (by rfl) ⟨1699082, by rfl⟩ : syracuseStep 2265443 = 3398165) B3398165
theorem B2265473 : Blo 1508951 2265473 := bstep (se 2 (by rfl) ⟨849552, by rfl⟩ : syracuseStep 2265473 = 1699105) B1699105
theorem B2265491 : Blo 1508951 2265491 := bstep (se 1 (by rfl) ⟨1699118, by rfl⟩ : syracuseStep 2265491 = 3398237) B3398237
theorem B2265521 : Blo 1508951 2265521 := bstep (se 2 (by rfl) ⟨849570, by rfl⟩ : syracuseStep 2265521 = 1699141) B1699141
theorem B2265539 : Blo 1508951 2265539 := bstep (se 1 (by rfl) ⟨1699154, by rfl⟩ : syracuseStep 2265539 = 3398309) B3398309
theorem B2265569 : Blo 1508951 2265569 := bstep (se 2 (by rfl) ⟨849588, by rfl⟩ : syracuseStep 2265569 = 1699177) B1699177
theorem B8597987 : Blo 1508951 8597987 := bstep (se 1 (by rfl) ⟨6448490, by rfl⟩ : syracuseStep 8597987 = 12896981) B12896981
theorem B2265587 : Blo 1508951 2265587 := bstep (se 1 (by rfl) ⟨1699190, by rfl⟩ : syracuseStep 2265587 = 3398381) B3398381
theorem B3396113 : Blo 1508951 3396113 := bstep (se 2 (by rfl) ⟨1273542, by rfl⟩ : syracuseStep 3396113 = 2547085) B2547085
theorem B2265617 : Blo 1508951 2265617 := bstep (se 2 (by rfl) ⟨849606, by rfl⟩ : syracuseStep 2265617 = 1699213) B1699213
theorem B5730851 : Blo 1508951 5730851 := bstep (se 1 (by rfl) ⟨4298138, by rfl⟩ : syracuseStep 5730851 = 8596277) B8596277
theorem B3396131 : Blo 1508951 3396131 := bstep (se 1 (by rfl) ⟨2547098, by rfl⟩ : syracuseStep 3396131 = 5094197) B5094197
theorem B2265635 : Blo 1508951 2265635 := bstep (se 1 (by rfl) ⟨1699226, by rfl⟩ : syracuseStep 2265635 = 3398453) B3398453
theorem B2265665 : Blo 1508951 2265665 := bstep (se 2 (by rfl) ⟨849624, by rfl⟩ : syracuseStep 2265665 = 1699249) B1699249
theorem B2265683 : Blo 1508951 2265683 := bstep (se 1 (by rfl) ⟨1699262, by rfl⟩ : syracuseStep 2265683 = 3398525) B3398525
theorem B2265713 : Blo 1508951 2265713 := bstep (se 2 (by rfl) ⟨849642, by rfl⟩ : syracuseStep 2265713 = 1699285) B1699285
theorem B7647857 : Blo 1508951 7647857 := bstep (se 2 (by rfl) ⟨2867946, by rfl⟩ : syracuseStep 7647857 = 5735893) B5735893
theorem B2265731 : Blo 1508951 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B2265761 : Blo 1508951 2265761 := bstep (se 2 (by rfl) ⟨849660, by rfl⟩ : syracuseStep 2265761 = 1699321) B1699321
theorem B5444273 : Blo 1508951 5444273 := bstep (se 2 (by rfl) ⟨2041602, by rfl⟩ : syracuseStep 5444273 = 4083205) B4083205
theorem B2265779 : Blo 1508951 2265779 := bstep (se 1 (by rfl) ⟨1699334, by rfl⟩ : syracuseStep 2265779 = 3398669) B3398669
theorem B7639757 : Blo 1508951 7639757 := bstep (se 3 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 7639757 = 2864909) B2864909
theorem B2265809 : Blo 1508951 2265809 := bstep (se 2 (by rfl) ⟨849678, by rfl⟩ : syracuseStep 2265809 = 1699357) B1699357
theorem B2151137 : Blo 1508951 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B2265827 : Blo 1508951 2265827 := bstep (se 1 (by rfl) ⟨1699370, by rfl⟩ : syracuseStep 2265827 = 3398741) B3398741
theorem B2265857 : Blo 1508951 2265857 := bstep (se 2 (by rfl) ⟨849696, by rfl⟩ : syracuseStep 2265857 = 1699393) B1699393
theorem B2265875 : Blo 1508951 2265875 := bstep (se 1 (by rfl) ⟨1699406, by rfl⟩ : syracuseStep 2265875 = 3398813) B3398813
theorem B3396401 : Blo 1508951 3396401 := bstep (se 2 (by rfl) ⟨1273650, by rfl⟩ : syracuseStep 3396401 = 2547301) B2547301
theorem B2265905 : Blo 1508951 2265905 := bstep (se 2 (by rfl) ⟨849714, by rfl⟩ : syracuseStep 2265905 = 1699429) B1699429
theorem B3396419 : Blo 1508951 3396419 := bstep (se 1 (by rfl) ⟨2547314, by rfl⟩ : syracuseStep 3396419 = 5094629) B5094629
theorem B2265923 : Blo 1508951 2265923 := bstep (se 1 (by rfl) ⟨1699442, by rfl⟩ : syracuseStep 2265923 = 3398885) B3398885
theorem B6452045 : Blo 1508951 6452045 := bstep (se 3 (by rfl) ⟨1209758, by rfl⟩ : syracuseStep 6452045 = 2419517) B2419517
theorem B2265953 : Blo 1508951 2265953 := bstep (se 2 (by rfl) ⟨849732, by rfl⟩ : syracuseStep 2265953 = 1699465) B1699465
theorem B2265971 : Blo 1508951 2265971 := bstep (se 1 (by rfl) ⟨1699478, by rfl⟩ : syracuseStep 2265971 = 3398957) B3398957
theorem B2266001 : Blo 1508951 2266001 := bstep (se 2 (by rfl) ⟨849750, by rfl⟩ : syracuseStep 2266001 = 1699501) B1699501
theorem B2266019 : Blo 1508951 2266019 := bstep (se 1 (by rfl) ⟨1699514, by rfl⟩ : syracuseStep 2266019 = 3399029) B3399029
theorem B2266049 : Blo 1508951 2266049 := bstep (se 2 (by rfl) ⟨849768, by rfl⟩ : syracuseStep 2266049 = 1699537) B1699537
theorem B25793477 : Blo 1508951 25793477 := bstep (se 4 (by rfl) ⟨2418138, by rfl⟩ : syracuseStep 25793477 = 4836277) B4836277
theorem B2266067 : Blo 1508951 2266067 := bstep (se 1 (by rfl) ⟨1699550, by rfl⟩ : syracuseStep 2266067 = 3399101) B3399101
theorem B2266097 : Blo 1508951 2266097 := bstep (se 2 (by rfl) ⟨849786, by rfl⟩ : syracuseStep 2266097 = 1699573) B1699573
theorem B1962995 : Blo 1508951 1962995 := bstep (se 1 (by rfl) ⟨1472246, by rfl⟩ : syracuseStep 1962995 = 2944493) B2944493
theorem B2266115 : Blo 1508951 2266115 := bstep (se 1 (by rfl) ⟨1699586, by rfl⟩ : syracuseStep 2266115 = 3399173) B3399173
theorem B2266145 : Blo 1508951 2266145 := bstep (se 2 (by rfl) ⟨849804, by rfl⟩ : syracuseStep 2266145 = 1699609) B1699609
theorem B2266163 : Blo 1508951 2266163 := bstep (se 1 (by rfl) ⟨1699622, by rfl⟩ : syracuseStep 2266163 = 3399245) B3399245
theorem B3396689 : Blo 1508951 3396689 := bstep (se 2 (by rfl) ⟨1273758, by rfl⟩ : syracuseStep 3396689 = 2547517) B2547517
theorem B3822673 : Blo 1508951 3822673 := bstep (se 2 (by rfl) ⟨1433502, by rfl⟩ : syracuseStep 3822673 = 2867005) B2867005
theorem B2266193 : Blo 1508951 2266193 := bstep (se 2 (by rfl) ⟨849822, by rfl⟩ : syracuseStep 2266193 = 1699645) B1699645
theorem B3396707 : Blo 1508951 3396707 := bstep (se 1 (by rfl) ⟨2547530, by rfl⟩ : syracuseStep 3396707 = 5095061) B5095061
theorem B2266211 : Blo 1508951 2266211 := bstep (se 1 (by rfl) ⟨1699658, by rfl⟩ : syracuseStep 2266211 = 3399317) B3399317
theorem B2266241 : Blo 1508951 2266241 := bstep (se 2 (by rfl) ⟨849840, by rfl⟩ : syracuseStep 2266241 = 1699681) B1699681
theorem B2266259 : Blo 1508951 2266259 := bstep (se 1 (by rfl) ⟨1699694, by rfl⟩ : syracuseStep 2266259 = 3399389) B3399389
theorem B5731505 : Blo 1508951 5731505 := bstep (se 2 (by rfl) ⟨2149314, by rfl⟩ : syracuseStep 5731505 = 4298629) B4298629
theorem B2266289 : Blo 1508951 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B2266307 : Blo 1508951 2266307 := bstep (se 1 (by rfl) ⟨1699730, by rfl⟩ : syracuseStep 2266307 = 3399461) B3399461
theorem B2266337 : Blo 1508951 2266337 := bstep (se 2 (by rfl) ⟨849876, by rfl⟩ : syracuseStep 2266337 = 1699753) B1699753
theorem B2266355 : Blo 1508951 2266355 := bstep (se 1 (by rfl) ⟨1699766, by rfl⟩ : syracuseStep 2266355 = 3399533) B3399533
theorem B9680141 : Blo 1508951 9680141 := bstep (se 3 (by rfl) ⟨1815026, by rfl⟩ : syracuseStep 9680141 = 3630053) B3630053
theorem B2266385 : Blo 1508951 2266385 := bstep (se 2 (by rfl) ⟨849894, by rfl⟩ : syracuseStep 2266385 = 1699789) B1699789
theorem B2266403 : Blo 1508951 2266403 := bstep (se 1 (by rfl) ⟨1699802, by rfl⟩ : syracuseStep 2266403 = 3399605) B3399605
theorem B6534449 : Blo 1508951 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B18371893 : Blo 1508951 18371893 := bstep (se 5 (by rfl) ⟨861182, by rfl⟩ : syracuseStep 18371893 = 1722365) B1722365
theorem B6206797 : Blo 1508951 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B3822947 : Blo 1508951 3822947 := bstep (se 1 (by rfl) ⟨2867210, by rfl⟩ : syracuseStep 3822947 = 5734421) B5734421
theorem B4298093 : Blo 1508951 4298093 := bstep (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) B1611785
theorem B20649329 : Blo 1508951 20649329 := bstep (se 2 (by rfl) ⟨7743498, by rfl⟩ : syracuseStep 20649329 = 15486997) B15486997
theorem B3396977 : Blo 1508951 3396977 := bstep (se 2 (by rfl) ⟨1273866, by rfl⟩ : syracuseStep 3396977 = 2547733) B2547733
theorem B5092739 : Blo 1508951 5092739 := bstep (se 1 (by rfl) ⟨3819554, by rfl⟩ : syracuseStep 5092739 = 7639109) B7639109
theorem B3396995 : Blo 1508951 3396995 := bstep (se 1 (by rfl) ⟨2547746, by rfl⟩ : syracuseStep 3396995 = 5095493) B5095493
theorem B2905475 : Blo 1508951 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B2905507 : Blo 1508951 2905507 := bstep (se 1 (by rfl) ⟨2179130, by rfl⟩ : syracuseStep 2905507 = 4358261) B4358261
theorem B17208773 : Blo 1508951 17208773 := bstep (se 4 (by rfl) ⟨1613322, by rfl⟩ : syracuseStep 17208773 = 3226645) B3226645
theorem B3225091 : Blo 1508951 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B4298275 : Blo 1508951 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B3823139 : Blo 1508951 3823139 := bstep (se 1 (by rfl) ⟨2867354, by rfl⟩ : syracuseStep 3823139 = 5734709) B5734709
theorem B4298321 : Blo 1508951 4298321 := bstep (se 2 (by rfl) ⟨1611870, by rfl⟩ : syracuseStep 4298321 = 3223741) B3223741
theorem B5093009 : Blo 1508951 5093009 := bstep (se 2 (by rfl) ⟨1909878, by rfl⟩ : syracuseStep 5093009 = 3819757) B3819757
theorem B3397265 : Blo 1508951 3397265 := bstep (se 2 (by rfl) ⟨1273974, by rfl⟩ : syracuseStep 3397265 = 2547949) B2547949
theorem B2864803 : Blo 1508951 2864803 := bstep (se 1 (by rfl) ⟨2148602, by rfl⟩ : syracuseStep 2864803 = 4297205) B4297205
theorem B3397283 : Blo 1508951 3397283 := bstep (se 1 (by rfl) ⟨2547962, by rfl⟩ : syracuseStep 3397283 = 5095925) B5095925
theorem B3061489 : Blo 1508951 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B3225347 : Blo 1508951 3225347 := bstep (se 1 (by rfl) ⟨2419010, by rfl⟩ : syracuseStep 3225347 = 4838021) B4838021
theorem B5445425 : Blo 1508951 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B2864963 : Blo 1508951 2864963 := bstep (se 1 (by rfl) ⟨2148722, by rfl⟩ : syracuseStep 2864963 = 4297445) B4297445
theorem B4839277 : Blo 1508951 4839277 := bstep (se 3 (by rfl) ⟨907364, by rfl⟩ : syracuseStep 4839277 = 1814729) B1814729
theorem B9811853 : Blo 1508951 9811853 := bstep (se 3 (by rfl) ⟨1839722, by rfl⟩ : syracuseStep 9811853 = 3679445) B3679445
theorem B3397553 : Blo 1508951 3397553 := bstep (se 2 (by rfl) ⟨1274082, by rfl⟩ : syracuseStep 3397553 = 2548165) B2548165
theorem B3397571 : Blo 1508951 3397571 := bstep (se 1 (by rfl) ⟨2548178, by rfl⟩ : syracuseStep 3397571 = 5096357) B5096357
theorem B12900293 : Blo 1508951 12900293 := bstep (se 4 (by rfl) ⟨1209402, by rfl⟩ : syracuseStep 12900293 = 2418805) B2418805
theorem B16316387 : Blo 1508951 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B4134883 : Blo 1508951 4134883 := bstep (se 1 (by rfl) ⟨3101162, by rfl⟩ : syracuseStep 4134883 = 6202325) B6202325
theorem B2297011 : Blo 1508951 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B2758691 : Blo 1508951 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B12892229 : Blo 1508951 12892229 := bstep (se 4 (by rfl) ⟨1208646, by rfl⟩ : syracuseStep 12892229 = 2417293) B2417293
theorem B19347569 : Blo 1508951 19347569 := bstep (se 2 (by rfl) ⟨7255338, by rfl⟩ : syracuseStep 19347569 = 14510677) B14510677
theorem B5093549 : Blo 1508951 5093549 := bstep (se 3 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 5093549 = 1910081) B1910081
theorem B3397841 : Blo 1508951 3397841 := bstep (se 2 (by rfl) ⟨1274190, by rfl⟩ : syracuseStep 3397841 = 2548381) B2548381
theorem B5093603 : Blo 1508951 5093603 := bstep (se 1 (by rfl) ⟨3820202, by rfl⟩ : syracuseStep 5093603 = 7640405) B7640405
theorem B1530083 : Blo 1508951 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B3397859 : Blo 1508951 3397859 := bstep (se 1 (by rfl) ⟨2548394, by rfl⟩ : syracuseStep 3397859 = 5096789) B5096789
theorem B9672965 : Blo 1508951 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B1612067 : Blo 1508951 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B3676483 : Blo 1508951 3676483 := bstep (se 1 (by rfl) ⟨2757362, by rfl⟩ : syracuseStep 3676483 = 5514725) B5514725
theorem B8599877 : Blo 1508951 8599877 := bstep (se 4 (by rfl) ⟨806238, by rfl⟩ : syracuseStep 8599877 = 1612477) B1612477
theorem B3824081 : Blo 1508951 3824081 := bstep (se 2 (by rfl) ⟨1434030, by rfl⟩ : syracuseStep 3824081 = 2868061) B2868061
theorem B5093873 : Blo 1508951 5093873 := bstep (se 2 (by rfl) ⟨1910202, by rfl⟩ : syracuseStep 5093873 = 3820405) B3820405
theorem B3398129 : Blo 1508951 3398129 := bstep (se 2 (by rfl) ⟨1274298, by rfl⟩ : syracuseStep 3398129 = 2548597) B2548597
theorem B3398147 : Blo 1508951 3398147 := bstep (se 1 (by rfl) ⟨2548610, by rfl⟩ : syracuseStep 3398147 = 5097221) B5097221
theorem B3824131 : Blo 1508951 3824131 := bstep (se 1 (by rfl) ⟨2868098, by rfl⟩ : syracuseStep 3824131 = 5736197) B5736197
theorem B5732963 : Blo 1508951 5732963 := bstep (se 1 (by rfl) ⟨4299722, by rfl⟩ : syracuseStep 5732963 = 8599445) B8599445
theorem B5732977 : Blo 1508951 5732977 := bstep (se 2 (by rfl) ⟨2149866, by rfl⟩ : syracuseStep 5732977 = 4299733) B4299733
theorem B12900977 : Blo 1508951 12900977 := bstep (se 2 (by rfl) ⟨4837866, by rfl⟩ : syracuseStep 12900977 = 9675733) B9675733
theorem B3824273 : Blo 1508951 3824273 := bstep (se 2 (by rfl) ⟨1434102, by rfl⟩ : syracuseStep 3824273 = 2868205) B2868205
theorem B3226321 : Blo 1508951 3226321 := bstep (se 2 (by rfl) ⟨1209870, by rfl⟩ : syracuseStep 3226321 = 2419741) B2419741
theorem B2546417 : Blo 1508951 2546417 := bstep (se 2 (by rfl) ⟨954906, by rfl⟩ : syracuseStep 2546417 = 1909813) B1909813
theorem B3398417 : Blo 1508951 3398417 := bstep (se 2 (by rfl) ⟨1274406, by rfl⟩ : syracuseStep 3398417 = 2548813) B2548813
theorem B3398435 : Blo 1508951 3398435 := bstep (se 1 (by rfl) ⟨2548826, by rfl⟩ : syracuseStep 3398435 = 5097653) B5097653
theorem B2546545 : Blo 1508951 2546545 := bstep (se 2 (by rfl) ⟨954954, by rfl⟩ : syracuseStep 2546545 = 1909909) B1909909
theorem B2866033 : Blo 1508951 2866033 := bstep (se 2 (by rfl) ⟨1074762, by rfl⟩ : syracuseStep 2866033 = 2149525) B2149525
theorem B2546579 : Blo 1508951 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B12745669 : Blo 1508951 12745669 := bstep (se 4 (by rfl) ⟨1194906, by rfl⟩ : syracuseStep 12745669 = 2389813) B2389813
theorem B4299779 : Blo 1508951 4299779 := bstep (se 1 (by rfl) ⟨3224834, by rfl⟩ : syracuseStep 4299779 = 6449669) B6449669
theorem B5094413 : Blo 1508951 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B2546707 : Blo 1508951 2546707 := bstep (se 1 (by rfl) ⟨1910030, by rfl⟩ : syracuseStep 2546707 = 3820061) B3820061
theorem B1612819 : Blo 1508951 1612819 := bstep (se 1 (by rfl) ⟨1209614, by rfl⟩ : syracuseStep 1612819 = 2419229) B2419229
theorem B3398705 : Blo 1508951 3398705 := bstep (se 2 (by rfl) ⟨1274514, by rfl⟩ : syracuseStep 3398705 = 2549029) B2549029
theorem B5094467 : Blo 1508951 5094467 := bstep (se 1 (by rfl) ⟨3820850, by rfl⟩ : syracuseStep 5094467 = 7641701) B7641701
theorem B3398723 : Blo 1508951 3398723 := bstep (se 1 (by rfl) ⟨2549042, by rfl⟩ : syracuseStep 3398723 = 5098085) B5098085
theorem B2546849 : Blo 1508951 2546849 := bstep (se 2 (by rfl) ⟨955068, by rfl⟩ : syracuseStep 2546849 = 1910137) B1910137
theorem B6208753 : Blo 1508951 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B2546977 : Blo 1508951 2546977 := bstep (se 2 (by rfl) ⟨955116, by rfl⟩ : syracuseStep 2546977 = 1910233) B1910233
theorem B2547011 : Blo 1508951 2547011 := bstep (se 1 (by rfl) ⟨1910258, by rfl⟩ : syracuseStep 2547011 = 3820517) B3820517
theorem B5094737 : Blo 1508951 5094737 := bstep (se 2 (by rfl) ⟨1910526, by rfl⟩ : syracuseStep 5094737 = 3821053) B3821053
theorem B1531219 : Blo 1508951 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B3398993 : Blo 1508951 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B3399011 : Blo 1508951 3399011 := bstep (se 1 (by rfl) ⟨2549258, by rfl⟩ : syracuseStep 3399011 = 5098517) B5098517
theorem B3226979 : Blo 1508951 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B4078957 : Blo 1508951 4078957 := bstep (se 3 (by rfl) ⟨764804, by rfl⟩ : syracuseStep 4078957 = 1529609) B1529609
theorem B24477041 : Blo 1508951 24477041 := bstep (se 2 (by rfl) ⟨9178890, by rfl⟩ : syracuseStep 24477041 = 18357781) B18357781
theorem B2547139 : Blo 1508951 2547139 := bstep (se 1 (by rfl) ⟨1910354, by rfl⟩ : syracuseStep 2547139 = 3820709) B3820709
theorem B7642673 : Blo 1508951 7642673 := bstep (se 2 (by rfl) ⟨2866002, by rfl⟩ : syracuseStep 7642673 = 5732005) B5732005
theorem B2547281 : Blo 1508951 2547281 := bstep (se 2 (by rfl) ⟨955230, by rfl⟩ : syracuseStep 2547281 = 1910461) B1910461
theorem B3399281 : Blo 1508951 3399281 := bstep (se 2 (by rfl) ⟨1274730, by rfl⟩ : syracuseStep 3399281 = 2549461) B2549461
theorem B3399299 : Blo 1508951 3399299 := bstep (se 1 (by rfl) ⟨2549474, by rfl⟩ : syracuseStep 3399299 = 5098949) B5098949
theorem B27541133 : Blo 1508951 27541133 := bstep (se 3 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 27541133 = 10327925) B10327925
theorem B2719441 : Blo 1508951 2719441 := bstep (se 2 (by rfl) ⟨1019790, by rfl⟩ : syracuseStep 2719441 = 2039581) B2039581
theorem B2547409 : Blo 1508951 2547409 := bstep (se 2 (by rfl) ⟨955278, by rfl⟩ : syracuseStep 2547409 = 1910557) B1910557
theorem B2547443 : Blo 1508951 2547443 := bstep (se 1 (by rfl) ⟨1910582, by rfl⟩ : syracuseStep 2547443 = 3821165) B3821165
theorem B11460365 : Blo 1508951 11460365 := bstep (se 3 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 11460365 = 4297637) B4297637
theorem B5095277 : Blo 1508951 5095277 := bstep (se 3 (by rfl) ⟨955364, by rfl⟩ : syracuseStep 5095277 = 1910729) B1910729
theorem B2547571 : Blo 1508951 2547571 := bstep (se 1 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 2547571 = 3821357) B3821357
theorem B2867089 : Blo 1508951 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B3399569 : Blo 1508951 3399569 := bstep (se 2 (by rfl) ⟨1274838, by rfl⟩ : syracuseStep 3399569 = 2549677) B2549677
theorem B5095331 : Blo 1508951 5095331 := bstep (se 1 (by rfl) ⟨3821498, by rfl⟩ : syracuseStep 5095331 = 7642997) B7642997
theorem B2719651 : Blo 1508951 2719651 := bstep (se 1 (by rfl) ⟨2039738, by rfl⟩ : syracuseStep 2719651 = 4079477) B4079477
theorem B3399587 : Blo 1508951 3399587 := bstep (se 1 (by rfl) ⟨2549690, by rfl⟩ : syracuseStep 3399587 = 5099381) B5099381
theorem B6119489 : Blo 1508951 6119489 := bstep (se 2 (by rfl) ⟨2294808, by rfl⟩ : syracuseStep 6119489 = 4589617) B4589617
theorem B2547787 : Blo 1508951 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B7356509 : Blo 1508951 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B8159363 : Blo 1508951 8159363 := bstep (se 1 (by rfl) ⟨6119522, by rfl⟩ : syracuseStep 8159363 = 12239045) B12239045
theorem B7258243 : Blo 1508951 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B2867339 : Blo 1508951 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B2867393 : Blo 1508951 2867393 := bstep (se 2 (by rfl) ⟨1075272, by rfl⟩ : syracuseStep 2867393 = 2150545) B2150545
theorem B2547929 : Blo 1508951 2547929 := bstep (se 2 (by rfl) ⟨955473, by rfl⟩ : syracuseStep 2547929 = 1910947) B1910947
theorem B2548057 : Blo 1508951 2548057 := bstep (se 2 (by rfl) ⟨955521, by rfl⟩ : syracuseStep 2548057 = 1911043) B1911043
theorem B3629515 : Blo 1508951 3629515 := bstep (se 1 (by rfl) ⟨2722136, by rfl⟩ : syracuseStep 3629515 = 5444273) B5444273
theorem B4301363 : Blo 1508951 4301363 := bstep (se 1 (by rfl) ⟨3226022, by rfl⟩ : syracuseStep 4301363 = 6452045) B6452045
theorem B2720321 : Blo 1508951 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B4080221 : Blo 1508951 4080221 := bstep (se 3 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 4080221 = 1530083) B1530083
theorem B17195651 : Blo 1508951 17195651 := bstep (se 1 (by rfl) ⟨12896738, by rfl⟩ : syracuseStep 17195651 = 25793477) B25793477
theorem B5096087 : Blo 1508951 5096087 := bstep (se 1 (by rfl) ⟨3822065, by rfl⟩ : syracuseStep 5096087 = 7644131) B7644131
theorem B11461337 : Blo 1508951 11461337 := bstep (se 2 (by rfl) ⟨4298001, by rfl⟩ : syracuseStep 11461337 = 8596003) B8596003
theorem B3629785 : Blo 1508951 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B7643969 : Blo 1508951 7643969 := bstep (se 2 (by rfl) ⟨2866488, by rfl⟩ : syracuseStep 7643969 = 5732977) B5732977
theorem B2548631 : Blo 1508951 2548631 := bstep (se 1 (by rfl) ⟨1911473, by rfl⟩ : syracuseStep 2548631 = 3822947) B3822947
theorem B4301761 : Blo 1508951 4301761 := bstep (se 2 (by rfl) ⟨1613160, by rfl⟩ : syracuseStep 4301761 = 3226321) B3226321
theorem B2548759 : Blo 1508951 2548759 := bstep (se 1 (by rfl) ⟨1911569, by rfl⟩ : syracuseStep 2548759 = 3823139) B3823139
theorem B2868311 : Blo 1508951 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B5096627 : Blo 1508951 5096627 := bstep (se 1 (by rfl) ⟨3822470, by rfl⟩ : syracuseStep 5096627 = 7644941) B7644941
theorem B1909975 : Blo 1508951 1909975 := bstep (se 1 (by rfl) ⟨1432481, by rfl⟩ : syracuseStep 1909975 = 2864963) B2864963
theorem B11470085 : Blo 1508951 11470085 := bstep (se 4 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 11470085 = 2150641) B2150641
theorem B17442053 : Blo 1508951 17442053 := bstep (se 4 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 17442053 = 3270385) B3270385
theorem B2721035 : Blo 1508951 2721035 := bstep (se 1 (by rfl) ⟨2040776, by rfl⟩ : syracuseStep 2721035 = 4081553) B4081553
theorem B30991733 : Blo 1508951 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B8594819 : Blo 1508951 8594819 := bstep (se 1 (by rfl) ⟨6446114, by rfl⟩ : syracuseStep 8594819 = 12892229) B12892229
theorem B8717719 : Blo 1508951 8717719 := bstep (se 1 (by rfl) ⟨6538289, by rfl⟩ : syracuseStep 8717719 = 13076579) B13076579
theorem B5096897 : Blo 1508951 5096897 := bstep (se 2 (by rfl) ⟨1911336, by rfl⟩ : syracuseStep 5096897 = 3822673) B3822673
theorem B14509529 : Blo 1508951 14509529 := bstep (se 2 (by rfl) ⟨5441073, by rfl⟩ : syracuseStep 14509529 = 10882147) B10882147
theorem B6448643 : Blo 1508951 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B4081175 : Blo 1508951 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B1508951 : Blo 1508951 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B11626085 : Blo 1508951 11626085 := bstep (se 4 (by rfl) ⟨1089945, by rfl⟩ : syracuseStep 11626085 = 2179891) B2179891
theorem B1508971 : Blo 1508951 1508971 := bstep (se 1 (by rfl) ⟨1131728, by rfl⟩ : syracuseStep 1508971 = 2263457) B2263457
theorem B1508983 : Blo 1508951 1508983 := bstep (se 1 (by rfl) ⟨1131737, by rfl⟩ : syracuseStep 1508983 = 2263475) B2263475
theorem B1509003 : Blo 1508951 1509003 := bstep (se 1 (by rfl) ⟨1131752, by rfl⟩ : syracuseStep 1509003 = 2263505) B2263505
theorem B2549387 : Blo 1508951 2549387 := bstep (se 1 (by rfl) ⟨1912040, by rfl⟩ : syracuseStep 2549387 = 3824081) B3824081
theorem B1509015 : Blo 1508951 1509015 := bstep (se 1 (by rfl) ⟨1131761, by rfl⟩ : syracuseStep 1509015 = 2263523) B2263523
theorem B1509035 : Blo 1508951 1509035 := bstep (se 1 (by rfl) ⟨1131776, by rfl⟩ : syracuseStep 1509035 = 2263553) B2263553
theorem B1509047 : Blo 1508951 1509047 := bstep (se 1 (by rfl) ⟨1131785, by rfl⟩ : syracuseStep 1509047 = 2263571) B2263571
theorem B1509067 : Blo 1508951 1509067 := bstep (se 1 (by rfl) ⟨1131800, by rfl⟩ : syracuseStep 1509067 = 2263601) B2263601
theorem B1509079 : Blo 1508951 1509079 := bstep (se 1 (by rfl) ⟨1131809, by rfl⟩ : syracuseStep 1509079 = 2263619) B2263619
theorem B1509099 : Blo 1508951 1509099 := bstep (se 1 (by rfl) ⟨1131824, by rfl⟩ : syracuseStep 1509099 = 2263649) B2263649
theorem B24495857 : Blo 1508951 24495857 := bstep (se 2 (by rfl) ⟨9185946, by rfl⟩ : syracuseStep 24495857 = 18371893) B18371893
theorem B1509111 : Blo 1508951 1509111 := bstep (se 1 (by rfl) ⟨1131833, by rfl⟩ : syracuseStep 1509111 = 2263667) B2263667
theorem B1509131 : Blo 1508951 1509131 := bstep (se 1 (by rfl) ⟨1131848, by rfl⟩ : syracuseStep 1509131 = 2263697) B2263697
theorem B2549515 : Blo 1508951 2549515 := bstep (se 1 (by rfl) ⟨1912136, by rfl⟩ : syracuseStep 2549515 = 3824273) B3824273
theorem B8275729 : Blo 1508951 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B1509143 : Blo 1508951 1509143 := bstep (se 1 (by rfl) ⟨1131857, by rfl⟩ : syracuseStep 1509143 = 2263715) B2263715
theorem B2041625 : Blo 1508951 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B1509163 : Blo 1508951 1509163 := bstep (se 1 (by rfl) ⟨1131872, by rfl⟩ : syracuseStep 1509163 = 2263745) B2263745
theorem B10889005 : Blo 1508951 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B1509175 : Blo 1508951 1509175 := bstep (se 1 (by rfl) ⟨1131881, by rfl⟩ : syracuseStep 1509175 = 2263763) B2263763
theorem B1697611 : Blo 1508951 1697611 := bstep (se 1 (by rfl) ⟨1273208, by rfl⟩ : syracuseStep 1697611 = 2546417) B2546417
theorem B1509195 : Blo 1508951 1509195 := bstep (se 1 (by rfl) ⟨1131896, by rfl⟩ : syracuseStep 1509195 = 2263793) B2263793
theorem B1509207 : Blo 1508951 1509207 := bstep (se 1 (by rfl) ⟨1131905, by rfl⟩ : syracuseStep 1509207 = 2263811) B2263811
theorem B1509227 : Blo 1508951 1509227 := bstep (se 1 (by rfl) ⟨1131920, by rfl⟩ : syracuseStep 1509227 = 2263841) B2263841
theorem B1509239 : Blo 1508951 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B1509259 : Blo 1508951 1509259 := bstep (se 1 (by rfl) ⟨1131944, by rfl⟩ : syracuseStep 1509259 = 2263889) B2263889
theorem B1509271 : Blo 1508951 1509271 := bstep (se 1 (by rfl) ⟨1131953, by rfl⟩ : syracuseStep 1509271 = 2263907) B2263907
theorem B12240791 : Blo 1508951 12240791 := bstep (se 1 (by rfl) ⟨9180593, by rfl⟩ : syracuseStep 12240791 = 18361187) B18361187
theorem B2549657 : Blo 1508951 2549657 := bstep (se 2 (by rfl) ⟨956121, by rfl⟩ : syracuseStep 2549657 = 1912243) B1912243
theorem B1509291 : Blo 1508951 1509291 := bstep (se 1 (by rfl) ⟨1131968, by rfl⟩ : syracuseStep 1509291 = 2263937) B2263937
theorem B5736365 : Blo 1508951 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B1697719 : Blo 1508951 1697719 := bstep (se 1 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 1697719 = 2546579) B2546579
theorem B1509303 : Blo 1508951 1509303 := bstep (se 1 (by rfl) ⟨1131977, by rfl⟩ : syracuseStep 1509303 = 2263955) B2263955
theorem B1509323 : Blo 1508951 1509323 := bstep (se 1 (by rfl) ⟨1131992, by rfl⟩ : syracuseStep 1509323 = 2263985) B2263985
theorem B1509335 : Blo 1508951 1509335 := bstep (se 1 (by rfl) ⟨1132001, by rfl⟩ : syracuseStep 1509335 = 2264003) B2264003
theorem B5097437 : Blo 1508951 5097437 := bstep (se 3 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 5097437 = 1911539) B1911539
theorem B1509355 : Blo 1508951 1509355 := bstep (se 1 (by rfl) ⟨1132016, by rfl⟩ : syracuseStep 1509355 = 2264033) B2264033
theorem B1509367 : Blo 1508951 1509367 := bstep (se 1 (by rfl) ⟨1132025, by rfl⟩ : syracuseStep 1509367 = 2264051) B2264051
theorem B1509387 : Blo 1508951 1509387 := bstep (se 1 (by rfl) ⟨1132040, by rfl⟩ : syracuseStep 1509387 = 2264081) B2264081
theorem B1509399 : Blo 1508951 1509399 := bstep (se 1 (by rfl) ⟨1132049, by rfl⟩ : syracuseStep 1509399 = 2264099) B2264099
theorem B1509419 : Blo 1508951 1509419 := bstep (se 1 (by rfl) ⟨1132064, by rfl⟩ : syracuseStep 1509419 = 2264129) B2264129
theorem B1509431 : Blo 1508951 1509431 := bstep (se 1 (by rfl) ⟨1132073, by rfl⟩ : syracuseStep 1509431 = 2264147) B2264147
theorem B3819595 : Blo 1508951 3819595 := bstep (se 1 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 3819595 = 5729393) B5729393
theorem B1509451 : Blo 1508951 1509451 := bstep (se 1 (by rfl) ⟨1132088, by rfl⟩ : syracuseStep 1509451 = 2264177) B2264177
theorem B1509463 : Blo 1508951 1509463 := bstep (se 1 (by rfl) ⟨1132097, by rfl⟩ : syracuseStep 1509463 = 2264195) B2264195
theorem B6121565 : Blo 1508951 6121565 := bstep (se 3 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 6121565 = 2295587) B2295587
theorem B1697899 : Blo 1508951 1697899 := bstep (se 1 (by rfl) ⟨1273424, by rfl⟩ : syracuseStep 1697899 = 2546849) B2546849
theorem B1509483 : Blo 1508951 1509483 := bstep (se 1 (by rfl) ⟨1132112, by rfl⟩ : syracuseStep 1509483 = 2264225) B2264225
theorem B1509495 : Blo 1508951 1509495 := bstep (se 1 (by rfl) ⟨1132121, by rfl⟩ : syracuseStep 1509495 = 2264243) B2264243
theorem B1509515 : Blo 1508951 1509515 := bstep (se 1 (by rfl) ⟨1132136, by rfl⟩ : syracuseStep 1509515 = 2264273) B2264273
theorem B4901015 : Blo 1508951 4901015 := bstep (se 1 (by rfl) ⟨3675761, by rfl⟩ : syracuseStep 4901015 = 7351523) B7351523
theorem B1509527 : Blo 1508951 1509527 := bstep (se 1 (by rfl) ⟨1132145, by rfl⟩ : syracuseStep 1509527 = 2264291) B2264291
theorem B1509547 : Blo 1508951 1509547 := bstep (se 1 (by rfl) ⟨1132160, by rfl⟩ : syracuseStep 1509547 = 2264321) B2264321
theorem B1509559 : Blo 1508951 1509559 := bstep (se 1 (by rfl) ⟨1132169, by rfl⟩ : syracuseStep 1509559 = 2264339) B2264339
theorem B1509579 : Blo 1508951 1509579 := bstep (se 1 (by rfl) ⟨1132184, by rfl⟩ : syracuseStep 1509579 = 2264369) B2264369
theorem B1698007 : Blo 1508951 1698007 := bstep (se 1 (by rfl) ⟨1273505, by rfl⟩ : syracuseStep 1698007 = 2547011) B2547011
theorem B1509591 : Blo 1508951 1509591 := bstep (se 1 (by rfl) ⟨1132193, by rfl⟩ : syracuseStep 1509591 = 2264387) B2264387
theorem B3819737 : Blo 1508951 3819737 := bstep (se 2 (by rfl) ⟨1432401, by rfl⟩ : syracuseStep 3819737 = 2864803) B2864803
theorem B1509611 : Blo 1508951 1509611 := bstep (se 1 (by rfl) ⟨1132208, by rfl⟩ : syracuseStep 1509611 = 2264417) B2264417
theorem B1509623 : Blo 1508951 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B1509643 : Blo 1508951 1509643 := bstep (se 1 (by rfl) ⟨1132232, by rfl⟩ : syracuseStep 1509643 = 2264465) B2264465
theorem B1509655 : Blo 1508951 1509655 := bstep (se 1 (by rfl) ⟨1132241, by rfl⟩ : syracuseStep 1509655 = 2264483) B2264483
theorem B1509675 : Blo 1508951 1509675 := bstep (se 1 (by rfl) ⟨1132256, by rfl⟩ : syracuseStep 1509675 = 2264513) B2264513
theorem B1509687 : Blo 1508951 1509687 := bstep (se 1 (by rfl) ⟨1132265, by rfl⟩ : syracuseStep 1509687 = 2264531) B2264531
theorem B4081985 : Blo 1508951 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B20670785 : Blo 1508951 20670785 := bstep (se 2 (by rfl) ⟨7751544, by rfl⟩ : syracuseStep 20670785 = 15503089) B15503089
theorem B1509707 : Blo 1508951 1509707 := bstep (se 1 (by rfl) ⟨1132280, by rfl⟩ : syracuseStep 1509707 = 2264561) B2264561
theorem B7260491 : Blo 1508951 7260491 := bstep (se 1 (by rfl) ⟨5445368, by rfl⟩ : syracuseStep 7260491 = 10890737) B10890737
theorem B1509719 : Blo 1508951 1509719 := bstep (se 1 (by rfl) ⟨1132289, by rfl⟩ : syracuseStep 1509719 = 2264579) B2264579
theorem B1509739 : Blo 1508951 1509739 := bstep (se 1 (by rfl) ⟨1132304, by rfl⟩ : syracuseStep 1509739 = 2264609) B2264609
theorem B1509751 : Blo 1508951 1509751 := bstep (se 1 (by rfl) ⟨1132313, by rfl⟩ : syracuseStep 1509751 = 2264627) B2264627
theorem B1698187 : Blo 1508951 1698187 := bstep (se 1 (by rfl) ⟨1273640, by rfl⟩ : syracuseStep 1698187 = 2547281) B2547281
theorem B1509771 : Blo 1508951 1509771 := bstep (se 1 (by rfl) ⟨1132328, by rfl⟩ : syracuseStep 1509771 = 2264657) B2264657
theorem B1509783 : Blo 1508951 1509783 := bstep (se 1 (by rfl) ⟨1132337, by rfl⟩ : syracuseStep 1509783 = 2264675) B2264675
theorem B1509803 : Blo 1508951 1509803 := bstep (se 1 (by rfl) ⟨1132352, by rfl⟩ : syracuseStep 1509803 = 2264705) B2264705
theorem B18360755 : Blo 1508951 18360755 := bstep (se 1 (by rfl) ⟨13770566, by rfl⟩ : syracuseStep 18360755 = 27541133) B27541133
theorem B1509815 : Blo 1508951 1509815 := bstep (se 1 (by rfl) ⟨1132361, by rfl⟩ : syracuseStep 1509815 = 2264723) B2264723
theorem B2263499 : Blo 1508951 2263499 := bstep (se 1 (by rfl) ⟨1697624, by rfl⟩ : syracuseStep 2263499 = 3395249) B3395249
theorem B1509835 : Blo 1508951 1509835 := bstep (se 1 (by rfl) ⟨1132376, by rfl⟩ : syracuseStep 1509835 = 2264753) B2264753
theorem B2263511 : Blo 1508951 2263511 := bstep (se 1 (by rfl) ⟨1697633, by rfl⟩ : syracuseStep 2263511 = 3395267) B3395267
theorem B1509847 : Blo 1508951 1509847 := bstep (se 1 (by rfl) ⟨1132385, by rfl⟩ : syracuseStep 1509847 = 2264771) B2264771
theorem B1509867 : Blo 1508951 1509867 := bstep (se 1 (by rfl) ⟨1132400, by rfl⟩ : syracuseStep 1509867 = 2264801) B2264801
theorem B1698295 : Blo 1508951 1698295 := bstep (se 1 (by rfl) ⟨1273721, by rfl⟩ : syracuseStep 1698295 = 2547443) B2547443
theorem B1509879 : Blo 1508951 1509879 := bstep (se 1 (by rfl) ⟨1132409, by rfl⟩ : syracuseStep 1509879 = 2264819) B2264819
theorem B1509899 : Blo 1508951 1509899 := bstep (se 1 (by rfl) ⟨1132424, by rfl⟩ : syracuseStep 1509899 = 2264849) B2264849
theorem B2148887 : Blo 1508951 2148887 := bstep (se 1 (by rfl) ⟨1611665, by rfl⟩ : syracuseStep 2148887 = 3223331) B3223331
theorem B4590103 : Blo 1508951 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B2263577 : Blo 1508951 2263577 := bstep (se 2 (by rfl) ⟨848841, by rfl⟩ : syracuseStep 2263577 = 1697683) B1697683
theorem B6375959 : Blo 1508951 6375959 := bstep (se 1 (by rfl) ⟨4781969, by rfl⟩ : syracuseStep 6375959 = 9563939) B9563939
theorem B1509911 : Blo 1508951 1509911 := bstep (se 1 (by rfl) ⟨1132433, by rfl⟩ : syracuseStep 1509911 = 2264867) B2264867
theorem B1509931 : Blo 1508951 1509931 := bstep (se 1 (by rfl) ⟨1132448, by rfl⟩ : syracuseStep 1509931 = 2264897) B2264897
theorem B1509943 : Blo 1508951 1509943 := bstep (se 1 (by rfl) ⟨1132457, by rfl⟩ : syracuseStep 1509943 = 2264915) B2264915
theorem B3312203 : Blo 1508951 3312203 := bstep (se 1 (by rfl) ⟨2484152, by rfl⟩ : syracuseStep 3312203 = 4968305) B4968305
theorem B1509963 : Blo 1508951 1509963 := bstep (se 1 (by rfl) ⟨1132472, by rfl⟩ : syracuseStep 1509963 = 2264945) B2264945
theorem B1509975 : Blo 1508951 1509975 := bstep (se 1 (by rfl) ⟨1132481, by rfl⟩ : syracuseStep 1509975 = 2264963) B2264963
theorem B1509995 : Blo 1508951 1509995 := bstep (se 1 (by rfl) ⟨1132496, by rfl⟩ : syracuseStep 1509995 = 2264993) B2264993
theorem B1510007 : Blo 1508951 1510007 := bstep (se 1 (by rfl) ⟨1132505, by rfl⟩ : syracuseStep 1510007 = 2265011) B2265011
theorem B2263691 : Blo 1508951 2263691 := bstep (se 1 (by rfl) ⟨1697768, by rfl⟩ : syracuseStep 2263691 = 3395537) B3395537
theorem B1510027 : Blo 1508951 1510027 := bstep (se 1 (by rfl) ⟨1132520, by rfl⟩ : syracuseStep 1510027 = 2265041) B2265041
theorem B2263703 : Blo 1508951 2263703 := bstep (se 1 (by rfl) ⟨1697777, by rfl⟩ : syracuseStep 2263703 = 3395555) B3395555
theorem B1510039 : Blo 1508951 1510039 := bstep (se 1 (by rfl) ⟨1132529, by rfl⟩ : syracuseStep 1510039 = 2265059) B2265059
theorem B1698475 : Blo 1508951 1698475 := bstep (se 1 (by rfl) ⟨1273856, by rfl⟩ : syracuseStep 1698475 = 2547713) B2547713
theorem B1510059 : Blo 1508951 1510059 := bstep (se 1 (by rfl) ⟨1132544, by rfl⟩ : syracuseStep 1510059 = 2265089) B2265089
theorem B1510071 : Blo 1508951 1510071 := bstep (se 1 (by rfl) ⟨1132553, by rfl⟩ : syracuseStep 1510071 = 2265107) B2265107
theorem B1510091 : Blo 1508951 1510091 := bstep (se 1 (by rfl) ⟨1132568, by rfl⟩ : syracuseStep 1510091 = 2265137) B2265137
theorem B1510103 : Blo 1508951 1510103 := bstep (se 1 (by rfl) ⟨1132577, by rfl⟩ : syracuseStep 1510103 = 2265155) B2265155
theorem B2263769 : Blo 1508951 2263769 := bstep (se 2 (by rfl) ⟨848913, by rfl⟩ : syracuseStep 2263769 = 1697827) B1697827
theorem B7645913 : Blo 1508951 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B1510123 : Blo 1508951 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B1510135 : Blo 1508951 1510135 := bstep (se 1 (by rfl) ⟨1132601, by rfl⟩ : syracuseStep 1510135 = 2265203) B2265203
theorem B1510155 : Blo 1508951 1510155 := bstep (se 1 (by rfl) ⟨1132616, by rfl⟩ : syracuseStep 1510155 = 2265233) B2265233
theorem B1698583 : Blo 1508951 1698583 := bstep (se 1 (by rfl) ⟨1273937, by rfl⟩ : syracuseStep 1698583 = 2547875) B2547875
theorem B1510167 : Blo 1508951 1510167 := bstep (se 1 (by rfl) ⟨1132625, by rfl⟩ : syracuseStep 1510167 = 2265251) B2265251
theorem B1510187 : Blo 1508951 1510187 := bstep (se 1 (by rfl) ⟨1132640, by rfl⟩ : syracuseStep 1510187 = 2265281) B2265281
theorem B1510199 : Blo 1508951 1510199 := bstep (se 1 (by rfl) ⟨1132649, by rfl⟩ : syracuseStep 1510199 = 2265299) B2265299
theorem B2263883 : Blo 1508951 2263883 := bstep (se 1 (by rfl) ⟨1697912, by rfl⟩ : syracuseStep 2263883 = 3395825) B3395825
theorem B2149195 : Blo 1508951 2149195 := bstep (se 1 (by rfl) ⟨1611896, by rfl⟩ : syracuseStep 2149195 = 3223793) B3223793
theorem B1510219 : Blo 1508951 1510219 := bstep (se 1 (by rfl) ⟨1132664, by rfl⟩ : syracuseStep 1510219 = 2265329) B2265329
theorem B2263895 : Blo 1508951 2263895 := bstep (se 1 (by rfl) ⟨1697921, by rfl⟩ : syracuseStep 2263895 = 3395843) B3395843
theorem B1510231 : Blo 1508951 1510231 := bstep (se 1 (by rfl) ⟨1132673, by rfl⟩ : syracuseStep 1510231 = 2265347) B2265347
theorem B1510251 : Blo 1508951 1510251 := bstep (se 1 (by rfl) ⟨1132688, by rfl⟩ : syracuseStep 1510251 = 2265377) B2265377
theorem B1510263 : Blo 1508951 1510263 := bstep (se 1 (by rfl) ⟨1132697, by rfl⟩ : syracuseStep 1510263 = 2265395) B2265395
theorem B1510283 : Blo 1508951 1510283 := bstep (se 1 (by rfl) ⟨1132712, by rfl⟩ : syracuseStep 1510283 = 2265425) B2265425
theorem B1911691 : Blo 1508951 1911691 := bstep (se 1 (by rfl) ⟨1433768, by rfl⟩ : syracuseStep 1911691 = 2867537) B2867537
theorem B1510295 : Blo 1508951 1510295 := bstep (se 1 (by rfl) ⟨1132721, by rfl⟩ : syracuseStep 1510295 = 2265443) B2265443
theorem B2263961 : Blo 1508951 2263961 := bstep (se 2 (by rfl) ⟨848985, by rfl⟩ : syracuseStep 2263961 = 1697971) B1697971
theorem B1510315 : Blo 1508951 1510315 := bstep (se 1 (by rfl) ⟨1132736, by rfl⟩ : syracuseStep 1510315 = 2265473) B2265473
theorem B19360691 : Blo 1508951 19360691 := bstep (se 1 (by rfl) ⟨14520518, by rfl⟩ : syracuseStep 19360691 = 29041037) B29041037
theorem B1510327 : Blo 1508951 1510327 := bstep (se 1 (by rfl) ⟨1132745, by rfl⟩ : syracuseStep 1510327 = 2265491) B2265491
theorem B1698763 : Blo 1508951 1698763 := bstep (se 1 (by rfl) ⟨1274072, by rfl⟩ : syracuseStep 1698763 = 2548145) B2548145
theorem B1510347 : Blo 1508951 1510347 := bstep (se 1 (by rfl) ⟨1132760, by rfl⟩ : syracuseStep 1510347 = 2265521) B2265521
theorem B1510359 : Blo 1508951 1510359 := bstep (se 1 (by rfl) ⟨1132769, by rfl⟩ : syracuseStep 1510359 = 2265539) B2265539
theorem B1510379 : Blo 1508951 1510379 := bstep (se 1 (by rfl) ⟨1132784, by rfl⟩ : syracuseStep 1510379 = 2265569) B2265569
theorem B1510391 : Blo 1508951 1510391 := bstep (se 1 (by rfl) ⟨1132793, by rfl⟩ : syracuseStep 1510391 = 2265587) B2265587
theorem B2264075 : Blo 1508951 2264075 := bstep (se 1 (by rfl) ⟨1698056, by rfl⟩ : syracuseStep 2264075 = 3396113) B3396113
theorem B1510411 : Blo 1508951 1510411 := bstep (se 1 (by rfl) ⟨1132808, by rfl⟩ : syracuseStep 1510411 = 2265617) B2265617
theorem B3820567 : Blo 1508951 3820567 := bstep (se 1 (by rfl) ⟨2865425, by rfl⟩ : syracuseStep 3820567 = 5730851) B5730851
theorem B2264087 : Blo 1508951 2264087 := bstep (se 1 (by rfl) ⟨1698065, by rfl⟩ : syracuseStep 2264087 = 3396131) B3396131
theorem B1510423 : Blo 1508951 1510423 := bstep (se 1 (by rfl) ⟨1132817, by rfl⟩ : syracuseStep 1510423 = 2265635) B2265635
theorem B1510443 : Blo 1508951 1510443 := bstep (se 1 (by rfl) ⟨1132832, by rfl⟩ : syracuseStep 1510443 = 2265665) B2265665
theorem B1698871 : Blo 1508951 1698871 := bstep (se 1 (by rfl) ⟨1274153, by rfl⟩ : syracuseStep 1698871 = 2548307) B2548307
theorem B1510455 : Blo 1508951 1510455 := bstep (se 1 (by rfl) ⟨1132841, by rfl⟩ : syracuseStep 1510455 = 2265683) B2265683
theorem B1510475 : Blo 1508951 1510475 := bstep (se 1 (by rfl) ⟨1132856, by rfl⟩ : syracuseStep 1510475 = 2265713) B2265713
theorem B5098571 : Blo 1508951 5098571 := bstep (se 1 (by rfl) ⟨3823928, by rfl⟩ : syracuseStep 5098571 = 7647857) B7647857
theorem B1510487 : Blo 1508951 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B2264153 : Blo 1508951 2264153 := bstep (se 2 (by rfl) ⟨849057, by rfl⟩ : syracuseStep 2264153 = 1698115) B1698115
theorem B4901977 : Blo 1508951 4901977 := bstep (se 2 (by rfl) ⟨1838241, by rfl⟩ : syracuseStep 4901977 = 3676483) B3676483
theorem B1510507 : Blo 1508951 1510507 := bstep (se 1 (by rfl) ⟨1132880, by rfl⟩ : syracuseStep 1510507 = 2265761) B2265761
theorem B1510519 : Blo 1508951 1510519 := bstep (se 1 (by rfl) ⟨1132889, by rfl⟩ : syracuseStep 1510519 = 2265779) B2265779
theorem B1510539 : Blo 1508951 1510539 := bstep (se 1 (by rfl) ⟨1132904, by rfl⟩ : syracuseStep 1510539 = 2265809) B2265809
theorem B1510551 : Blo 1508951 1510551 := bstep (se 1 (by rfl) ⟨1132913, by rfl⟩ : syracuseStep 1510551 = 2265827) B2265827
theorem B1510571 : Blo 1508951 1510571 := bstep (se 1 (by rfl) ⟨1132928, by rfl⟩ : syracuseStep 1510571 = 2265857) B2265857
theorem B7253171 : Blo 1508951 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B1510583 : Blo 1508951 1510583 := bstep (se 1 (by rfl) ⟨1132937, by rfl⟩ : syracuseStep 1510583 = 2265875) B2265875
theorem B2264267 : Blo 1508951 2264267 := bstep (se 1 (by rfl) ⟨1698200, by rfl⟩ : syracuseStep 2264267 = 3396401) B3396401
theorem B1510603 : Blo 1508951 1510603 := bstep (se 1 (by rfl) ⟨1132952, by rfl⟩ : syracuseStep 1510603 = 2265905) B2265905
theorem B2264279 : Blo 1508951 2264279 := bstep (se 1 (by rfl) ⟨1698209, by rfl⟩ : syracuseStep 2264279 = 3396419) B3396419
theorem B1510615 : Blo 1508951 1510615 := bstep (se 1 (by rfl) ⟨1132961, by rfl⟩ : syracuseStep 1510615 = 2265923) B2265923
theorem B1699051 : Blo 1508951 1699051 := bstep (se 1 (by rfl) ⟨1274288, by rfl⟩ : syracuseStep 1699051 = 2548577) B2548577
theorem B1510635 : Blo 1508951 1510635 := bstep (se 1 (by rfl) ⟨1132976, by rfl⟩ : syracuseStep 1510635 = 2265953) B2265953
theorem B1510647 : Blo 1508951 1510647 := bstep (se 1 (by rfl) ⟨1132985, by rfl⟩ : syracuseStep 1510647 = 2265971) B2265971
theorem B1510667 : Blo 1508951 1510667 := bstep (se 1 (by rfl) ⟨1133000, by rfl⟩ : syracuseStep 1510667 = 2266001) B2266001
theorem B6450455 : Blo 1508951 6450455 := bstep (se 1 (by rfl) ⟨4837841, by rfl⟩ : syracuseStep 6450455 = 9675683) B9675683
theorem B2264345 : Blo 1508951 2264345 := bstep (se 2 (by rfl) ⟨849129, by rfl⟩ : syracuseStep 2264345 = 1698259) B1698259
theorem B1510679 : Blo 1508951 1510679 := bstep (se 1 (by rfl) ⟨1133009, by rfl⟩ : syracuseStep 1510679 = 2266019) B2266019
theorem B1510699 : Blo 1508951 1510699 := bstep (se 1 (by rfl) ⟨1133024, by rfl⟩ : syracuseStep 1510699 = 2266049) B2266049
theorem B1510711 : Blo 1508951 1510711 := bstep (se 1 (by rfl) ⟨1133033, by rfl⟩ : syracuseStep 1510711 = 2266067) B2266067
theorem B16330049 : Blo 1508951 16330049 := bstep (se 2 (by rfl) ⟨6123768, by rfl⟩ : syracuseStep 16330049 = 12247537) B12247537
theorem B1510731 : Blo 1508951 1510731 := bstep (se 1 (by rfl) ⟨1133048, by rfl⟩ : syracuseStep 1510731 = 2266097) B2266097
theorem B1699159 : Blo 1508951 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B1510743 : Blo 1508951 1510743 := bstep (se 1 (by rfl) ⟨1133057, by rfl⟩ : syracuseStep 1510743 = 2266115) B2266115
theorem B5098841 : Blo 1508951 5098841 := bstep (se 2 (by rfl) ⟨1912065, by rfl⟩ : syracuseStep 5098841 = 3824131) B3824131
theorem B12897629 : Blo 1508951 12897629 := bstep (se 3 (by rfl) ⟨2418305, by rfl⟩ : syracuseStep 12897629 = 4836611) B4836611
theorem B1510763 : Blo 1508951 1510763 := bstep (se 1 (by rfl) ⟨1133072, by rfl⟩ : syracuseStep 1510763 = 2266145) B2266145
theorem B21777781 : Blo 1508951 21777781 := bstep (se 5 (by rfl) ⟨1020833, by rfl⟩ : syracuseStep 21777781 = 2041667) B2041667
theorem B1510775 : Blo 1508951 1510775 := bstep (se 1 (by rfl) ⟨1133081, by rfl⟩ : syracuseStep 1510775 = 2266163) B2266163
theorem B2264459 : Blo 1508951 2264459 := bstep (se 1 (by rfl) ⟨1698344, by rfl⟩ : syracuseStep 2264459 = 3396689) B3396689
theorem B1510795 : Blo 1508951 1510795 := bstep (se 1 (by rfl) ⟨1133096, by rfl⟩ : syracuseStep 1510795 = 2266193) B2266193
theorem B2264471 : Blo 1508951 2264471 := bstep (se 1 (by rfl) ⟨1698353, by rfl⟩ : syracuseStep 2264471 = 3396707) B3396707
theorem B1510807 : Blo 1508951 1510807 := bstep (se 1 (by rfl) ⟨1133105, by rfl⟩ : syracuseStep 1510807 = 2266211) B2266211
theorem B1510827 : Blo 1508951 1510827 := bstep (se 1 (by rfl) ⟨1133120, by rfl⟩ : syracuseStep 1510827 = 2266241) B2266241
theorem B1510839 : Blo 1508951 1510839 := bstep (se 1 (by rfl) ⟨1133129, by rfl⟩ : syracuseStep 1510839 = 2266259) B2266259
theorem B3821003 : Blo 1508951 3821003 := bstep (se 1 (by rfl) ⟨2865752, by rfl⟩ : syracuseStep 3821003 = 5731505) B5731505
theorem B1510859 : Blo 1508951 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1510871 : Blo 1508951 1510871 := bstep (se 1 (by rfl) ⟨1133153, by rfl⟩ : syracuseStep 1510871 = 2266307) B2266307
theorem B2264537 : Blo 1508951 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B5443033 : Blo 1508951 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B1510891 : Blo 1508951 1510891 := bstep (se 1 (by rfl) ⟨1133168, by rfl⟩ : syracuseStep 1510891 = 2266337) B2266337
theorem B1510903 : Blo 1508951 1510903 := bstep (se 1 (by rfl) ⟨1133177, by rfl⟩ : syracuseStep 1510903 = 2266355) B2266355
theorem B1699339 : Blo 1508951 1699339 := bstep (se 1 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 1699339 = 2549009) B2549009
theorem B1510923 : Blo 1508951 1510923 := bstep (se 1 (by rfl) ⟨1133192, by rfl⟩ : syracuseStep 1510923 = 2266385) B2266385
theorem B1510935 : Blo 1508951 1510935 := bstep (se 1 (by rfl) ⟨1133201, by rfl⟩ : syracuseStep 1510935 = 2266403) B2266403
theorem B3059225 : Blo 1508951 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B13766219 : Blo 1508951 13766219 := bstep (se 1 (by rfl) ⟨10324664, by rfl⟩ : syracuseStep 13766219 = 20649329) B20649329
theorem B2264651 : Blo 1508951 2264651 := bstep (se 1 (by rfl) ⟨1698488, by rfl⟩ : syracuseStep 2264651 = 3396977) B3396977
theorem B3395159 : Blo 1508951 3395159 := bstep (se 1 (by rfl) ⟨2546369, by rfl⟩ : syracuseStep 3395159 = 5092739) B5092739
theorem B2264663 : Blo 1508951 2264663 := bstep (se 1 (by rfl) ⟨1698497, by rfl⟩ : syracuseStep 2264663 = 3396995) B3396995
theorem B26152541 : Blo 1508951 26152541 := bstep (se 3 (by rfl) ⟨4903601, by rfl⟩ : syracuseStep 26152541 = 9807203) B9807203
theorem B8605277 : Blo 1508951 8605277 := bstep (se 3 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 8605277 = 3226979) B3226979
theorem B1699447 : Blo 1508951 1699447 := bstep (se 1 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 1699447 = 2549171) B2549171
theorem B11472515 : Blo 1508951 11472515 := bstep (se 1 (by rfl) ⟨8604386, by rfl⟩ : syracuseStep 11472515 = 17208773) B17208773
theorem B2264729 : Blo 1508951 2264729 := bstep (se 2 (by rfl) ⟨849273, by rfl⟩ : syracuseStep 2264729 = 1698547) B1698547
theorem B9186995 : Blo 1508951 9186995 := bstep (se 1 (by rfl) ⟨6890246, by rfl⟩ : syracuseStep 9186995 = 13780493) B13780493
theorem B1814219 : Blo 1508951 1814219 := bstep (se 1 (by rfl) ⟨1360664, by rfl⟩ : syracuseStep 1814219 = 2721329) B2721329
theorem B3395339 : Blo 1508951 3395339 := bstep (se 1 (by rfl) ⟨2546504, by rfl⟩ : syracuseStep 3395339 = 5093009) B5093009
theorem B2264843 : Blo 1508951 2264843 := bstep (se 1 (by rfl) ⟨1698632, by rfl⟩ : syracuseStep 2264843 = 3397265) B3397265
theorem B2264855 : Blo 1508951 2264855 := bstep (se 1 (by rfl) ⟨1698641, by rfl⟩ : syracuseStep 2264855 = 3397283) B3397283
theorem B1699627 : Blo 1508951 1699627 := bstep (se 1 (by rfl) ⟨1274720, by rfl⟩ : syracuseStep 1699627 = 2549441) B2549441
theorem B3395393 : Blo 1508951 3395393 := bstep (se 2 (by rfl) ⟨1273272, by rfl⟩ : syracuseStep 3395393 = 2546545) B2546545
theorem B3821377 : Blo 1508951 3821377 := bstep (se 2 (by rfl) ⟨1433016, by rfl⟩ : syracuseStep 3821377 = 2866033) B2866033
theorem B2150231 : Blo 1508951 2150231 := bstep (se 1 (by rfl) ⟨1612673, by rfl⟩ : syracuseStep 2150231 = 3225347) B3225347
theorem B2264921 : Blo 1508951 2264921 := bstep (se 2 (by rfl) ⟨849345, by rfl⟩ : syracuseStep 2264921 = 1698691) B1698691
theorem B1699735 : Blo 1508951 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B16994225 : Blo 1508951 16994225 := bstep (se 2 (by rfl) ⟨6372834, by rfl⟩ : syracuseStep 16994225 = 12745669) B12745669
theorem B6541235 : Blo 1508951 6541235 := bstep (se 1 (by rfl) ⟨4905926, by rfl⟩ : syracuseStep 6541235 = 9811853) B9811853
theorem B2265035 : Blo 1508951 2265035 := bstep (se 1 (by rfl) ⟨1698776, by rfl⟩ : syracuseStep 2265035 = 3397553) B3397553
theorem B2265047 : Blo 1508951 2265047 := bstep (se 1 (by rfl) ⟨1698785, by rfl⟩ : syracuseStep 2265047 = 3397571) B3397571
theorem B6885337 : Blo 1508951 6885337 := bstep (se 2 (by rfl) ⟨2582001, by rfl⟩ : syracuseStep 6885337 = 5164003) B5164003
theorem B3395609 : Blo 1508951 3395609 := bstep (se 2 (by rfl) ⟨1273353, by rfl⟩ : syracuseStep 3395609 = 2546707) B2546707
theorem B2265113 : Blo 1508951 2265113 := bstep (se 2 (by rfl) ⟨849417, by rfl⟩ : syracuseStep 2265113 = 1698835) B1698835
theorem B2150425 : Blo 1508951 2150425 := bstep (se 2 (by rfl) ⟨806409, by rfl⟩ : syracuseStep 2150425 = 1612819) B1612819
theorem B11464739 : Blo 1508951 11464739 := bstep (se 1 (by rfl) ⟨8598554, by rfl⟩ : syracuseStep 11464739 = 17197109) B17197109
theorem B12898379 : Blo 1508951 12898379 := bstep (se 1 (by rfl) ⟨9673784, by rfl⟩ : syracuseStep 12898379 = 19347569) B19347569
theorem B3395699 : Blo 1508951 3395699 := bstep (se 1 (by rfl) ⟨2546774, by rfl⟩ : syracuseStep 3395699 = 5093549) B5093549
theorem B2265227 : Blo 1508951 2265227 := bstep (se 1 (by rfl) ⟨1698920, by rfl⟩ : syracuseStep 2265227 = 3397841) B3397841
theorem B3395735 : Blo 1508951 3395735 := bstep (se 1 (by rfl) ⟨2546801, by rfl⟩ : syracuseStep 3395735 = 5093603) B5093603
theorem B2265239 : Blo 1508951 2265239 := bstep (se 1 (by rfl) ⟨1698929, by rfl⟩ : syracuseStep 2265239 = 3397859) B3397859
theorem B2265305 : Blo 1508951 2265305 := bstep (se 2 (by rfl) ⟨849489, by rfl⟩ : syracuseStep 2265305 = 1698979) B1698979
theorem B7647533 : Blo 1508951 7647533 := bstep (se 3 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 7647533 = 2867825) B2867825
theorem B8278337 : Blo 1508951 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B3395915 : Blo 1508951 3395915 := bstep (se 1 (by rfl) ⟨2546936, by rfl⟩ : syracuseStep 3395915 = 5093873) B5093873
theorem B2265419 : Blo 1508951 2265419 := bstep (se 1 (by rfl) ⟨1699064, by rfl⟩ : syracuseStep 2265419 = 3398129) B3398129
theorem B2265431 : Blo 1508951 2265431 := bstep (se 1 (by rfl) ⟨1699073, by rfl⟩ : syracuseStep 2265431 = 3398147) B3398147
theorem B3395969 : Blo 1508951 3395969 := bstep (se 2 (by rfl) ⟨1273488, by rfl⟩ : syracuseStep 3395969 = 2546977) B2546977
theorem B5443985 : Blo 1508951 5443985 := bstep (se 2 (by rfl) ⟨2041494, by rfl⟩ : syracuseStep 5443985 = 4082989) B4082989
theorem B3821975 : Blo 1508951 3821975 := bstep (se 1 (by rfl) ⟨2866481, by rfl⟩ : syracuseStep 3821975 = 5732963) B5732963
theorem B2265497 : Blo 1508951 2265497 := bstep (se 2 (by rfl) ⟨849561, by rfl⟩ : syracuseStep 2265497 = 1699123) B1699123
theorem B2265611 : Blo 1508951 2265611 := bstep (se 1 (by rfl) ⟨1699208, by rfl⟩ : syracuseStep 2265611 = 3398417) B3398417
theorem B2265623 : Blo 1508951 2265623 := bstep (se 1 (by rfl) ⟨1699217, by rfl⟩ : syracuseStep 2265623 = 3398435) B3398435
theorem B6451787 : Blo 1508951 6451787 := bstep (se 1 (by rfl) ⟨4838840, by rfl⟩ : syracuseStep 6451787 = 9677681) B9677681
theorem B3396185 : Blo 1508951 3396185 := bstep (se 2 (by rfl) ⟨1273569, by rfl⟩ : syracuseStep 3396185 = 2547139) B2547139
theorem B2265689 : Blo 1508951 2265689 := bstep (se 2 (by rfl) ⟨849633, by rfl⟩ : syracuseStep 2265689 = 1699267) B1699267
theorem B9187991 : Blo 1508951 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B3396275 : Blo 1508951 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B5731019 : Blo 1508951 5731019 := bstep (se 1 (by rfl) ⟨4298264, by rfl⟩ : syracuseStep 5731019 = 8596529) B8596529
theorem B2265803 : Blo 1508951 2265803 := bstep (se 1 (by rfl) ⟨1699352, by rfl⟩ : syracuseStep 2265803 = 3398705) B3398705
theorem B3396311 : Blo 1508951 3396311 := bstep (se 1 (by rfl) ⟨2547233, by rfl⟩ : syracuseStep 3396311 = 5094467) B5094467
theorem B2265815 : Blo 1508951 2265815 := bstep (se 1 (by rfl) ⟨1699361, by rfl⟩ : syracuseStep 2265815 = 3398723) B3398723
theorem B5731033 : Blo 1508951 5731033 := bstep (se 2 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 5731033 = 4298275) B4298275
theorem B2265881 : Blo 1508951 2265881 := bstep (se 2 (by rfl) ⟨849705, by rfl⟩ : syracuseStep 2265881 = 1699411) B1699411
theorem B14521133 : Blo 1508951 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B3396491 : Blo 1508951 3396491 := bstep (se 1 (by rfl) ⟨2547368, by rfl⟩ : syracuseStep 3396491 = 5094737) B5094737
theorem B2265995 : Blo 1508951 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B2266007 : Blo 1508951 2266007 := bstep (se 1 (by rfl) ⟨1699505, by rfl⟩ : syracuseStep 2266007 = 3399011) B3399011
theorem B3625921 : Blo 1508951 3625921 := bstep (se 2 (by rfl) ⟨1359720, by rfl⟩ : syracuseStep 3625921 = 2719441) B2719441
theorem B3396545 : Blo 1508951 3396545 := bstep (se 2 (by rfl) ⟨1273704, by rfl⟩ : syracuseStep 3396545 = 2547409) B2547409
theorem B2266073 : Blo 1508951 2266073 := bstep (se 2 (by rfl) ⟨849777, by rfl⟩ : syracuseStep 2266073 = 1699555) B1699555
theorem B6124547 : Blo 1508951 6124547 := bstep (se 1 (by rfl) ⟨4593410, by rfl⟩ : syracuseStep 6124547 = 9186821) B9186821
theorem B7640081 : Blo 1508951 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B2266187 : Blo 1508951 2266187 := bstep (se 1 (by rfl) ⟨1699640, by rfl⟩ : syracuseStep 2266187 = 3399281) B3399281
theorem B2266199 : Blo 1508951 2266199 := bstep (se 1 (by rfl) ⟨1699649, by rfl⟩ : syracuseStep 2266199 = 3399299) B3399299
theorem B6452369 : Blo 1508951 6452369 := bstep (se 2 (by rfl) ⟨2419638, by rfl⟩ : syracuseStep 6452369 = 4839277) B4839277
theorem B3396761 : Blo 1508951 3396761 := bstep (se 2 (by rfl) ⟨1273785, by rfl⟩ : syracuseStep 3396761 = 2547571) B2547571
theorem B2266265 : Blo 1508951 2266265 := bstep (se 2 (by rfl) ⟨849849, by rfl⟩ : syracuseStep 2266265 = 1699699) B1699699
theorem B7640243 : Blo 1508951 7640243 := bstep (se 1 (by rfl) ⟨5730182, by rfl⟩ : syracuseStep 7640243 = 11460365) B11460365
theorem B3060929 : Blo 1508951 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B3822785 : Blo 1508951 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B3626201 : Blo 1508951 3626201 := bstep (se 2 (by rfl) ⟨1359825, by rfl⟩ : syracuseStep 3626201 = 2719651) B2719651
theorem B3396851 : Blo 1508951 3396851 := bstep (se 1 (by rfl) ⟨2547638, by rfl⟩ : syracuseStep 3396851 = 5095277) B5095277
theorem B2266379 : Blo 1508951 2266379 := bstep (se 1 (by rfl) ⟨1699784, by rfl⟩ : syracuseStep 2266379 = 3399569) B3399569
theorem B3396887 : Blo 1508951 3396887 := bstep (se 1 (by rfl) ⟨2547665, by rfl⟩ : syracuseStep 3396887 = 5095331) B5095331
theorem B2266391 : Blo 1508951 2266391 := bstep (se 1 (by rfl) ⟨1699793, by rfl⟩ : syracuseStep 2266391 = 3399587) B3399587
theorem B11785517 : Blo 1508951 11785517 := bstep (se 3 (by rfl) ⟨2209784, by rfl⟩ : syracuseStep 11785517 = 4419569) B4419569
theorem B6886745 : Blo 1508951 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B3224971 : Blo 1508951 3224971 := bstep (se 1 (by rfl) ⟨2418728, by rfl⟩ : syracuseStep 3224971 = 4837457) B4837457
theorem B3397067 : Blo 1508951 3397067 := bstep (se 1 (by rfl) ⟨2547800, by rfl⟩ : syracuseStep 3397067 = 5095601) B5095601
theorem B3397121 : Blo 1508951 3397121 := bstep (se 2 (by rfl) ⟨1273920, by rfl⟩ : syracuseStep 3397121 = 2547841) B2547841
theorem B24483397 : Blo 1508951 24483397 := bstep (se 4 (by rfl) ⟨2295318, by rfl⟩ : syracuseStep 24483397 = 4590637) B4590637
theorem B1611371 : Blo 1508951 1611371 := bstep (se 1 (by rfl) ⟨1208528, by rfl⟩ : syracuseStep 1611371 = 2417057) B2417057
theorem B5731991 : Blo 1508951 5731991 := bstep (se 1 (by rfl) ⟨4298993, by rfl⟩ : syracuseStep 5731991 = 8597987) B8597987
theorem B12900019 : Blo 1508951 12900019 := bstep (se 1 (by rfl) ⟨9675014, by rfl⟩ : syracuseStep 12900019 = 19350029) B19350029
theorem B3397337 : Blo 1508951 3397337 := bstep (se 2 (by rfl) ⟨1274001, by rfl⟩ : syracuseStep 3397337 = 2548003) B2548003
theorem B3823321 : Blo 1508951 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B5093171 : Blo 1508951 5093171 := bstep (se 1 (by rfl) ⟨3819878, by rfl⟩ : syracuseStep 5093171 = 7639757) B7639757
theorem B3397427 : Blo 1508951 3397427 := bstep (se 1 (by rfl) ⟨2548070, by rfl⟩ : syracuseStep 3397427 = 5096141) B5096141
theorem B3397463 : Blo 1508951 3397463 := bstep (se 1 (by rfl) ⟨2548097, by rfl⟩ : syracuseStep 3397463 = 5096195) B5096195
theorem B3225433 : Blo 1508951 3225433 := bstep (se 2 (by rfl) ⟨1209537, by rfl⟩ : syracuseStep 3225433 = 2419075) B2419075
theorem B3397643 : Blo 1508951 3397643 := bstep (se 1 (by rfl) ⟨2548232, by rfl⟩ : syracuseStep 3397643 = 5096465) B5096465
theorem B5093441 : Blo 1508951 5093441 := bstep (se 2 (by rfl) ⟨1910040, by rfl⟩ : syracuseStep 5093441 = 3820081) B3820081
theorem B3397697 : Blo 1508951 3397697 := bstep (se 2 (by rfl) ⟨1274136, by rfl⟩ : syracuseStep 3397697 = 2548273) B2548273
theorem B42432581 : Blo 1508951 42432581 := bstep (se 4 (by rfl) ⟨3978054, by rfl⟩ : syracuseStep 42432581 = 7956109) B7956109
theorem B4298845 : Blo 1508951 4298845 := bstep (se 3 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 4298845 = 1612067) B1612067
theorem B4298903 : Blo 1508951 4298903 := bstep (se 1 (by rfl) ⟨3224177, by rfl⟩ : syracuseStep 4298903 = 6448355) B6448355
theorem B6453427 : Blo 1508951 6453427 := bstep (se 1 (by rfl) ⟨4840070, by rfl⟩ : syracuseStep 6453427 = 9680141) B9680141
theorem B4356299 : Blo 1508951 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B2865395 : Blo 1508951 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B3397913 : Blo 1508951 3397913 := bstep (se 2 (by rfl) ⟨1274217, by rfl⟩ : syracuseStep 3397913 = 2548435) B2548435
theorem B3398003 : Blo 1508951 3398003 := bstep (se 1 (by rfl) ⟨2548502, by rfl⟩ : syracuseStep 3398003 = 5097005) B5097005
theorem B2865547 : Blo 1508951 2865547 := bstep (se 1 (by rfl) ⟨2149160, by rfl⟩ : syracuseStep 2865547 = 4298321) B4298321
theorem B3398039 : Blo 1508951 3398039 := bstep (se 1 (by rfl) ⟨2548529, by rfl⟩ : syracuseStep 3398039 = 5097059) B5097059
theorem B3398219 : Blo 1508951 3398219 := bstep (se 1 (by rfl) ⟨2548664, by rfl⟩ : syracuseStep 3398219 = 5097329) B5097329
theorem B5093981 : Blo 1508951 5093981 := bstep (se 3 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 5093981 = 1910243) B1910243
theorem B3398273 : Blo 1508951 3398273 := bstep (se 2 (by rfl) ⟨1274352, by rfl⟩ : syracuseStep 3398273 = 2548705) B2548705
theorem B8600195 : Blo 1508951 8600195 := bstep (se 1 (by rfl) ⟨6450146, by rfl⟩ : syracuseStep 8600195 = 12900293) B12900293
theorem B10877591 : Blo 1508951 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B2865881 : Blo 1508951 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B3824435 : Blo 1508951 3824435 := bstep (se 1 (by rfl) ⟨2868326, by rfl⟩ : syracuseStep 3824435 = 5736653) B5736653
theorem B11459393 : Blo 1508951 11459393 := bstep (se 2 (by rfl) ⟨4297272, by rfl⟩ : syracuseStep 11459393 = 8594545) B8594545
theorem B3398489 : Blo 1508951 3398489 := bstep (se 2 (by rfl) ⟨1274433, by rfl⟩ : syracuseStep 3398489 = 2548867) B2548867
theorem B5733251 : Blo 1508951 5733251 := bstep (se 1 (by rfl) ⟨4299938, by rfl⟩ : syracuseStep 5733251 = 8599877) B8599877
theorem B3062681 : Blo 1508951 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B3398579 : Blo 1508951 3398579 := bstep (se 1 (by rfl) ⟨2548934, by rfl⟩ : syracuseStep 3398579 = 5097869) B5097869
theorem B1612759 : Blo 1508951 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B3398615 : Blo 1508951 3398615 := bstep (se 1 (by rfl) ⟨2548961, by rfl⟩ : syracuseStep 3398615 = 5097923) B5097923
theorem B6888493 : Blo 1508951 6888493 := bstep (se 3 (by rfl) ⟨1291592, by rfl⟩ : syracuseStep 6888493 = 2583185) B2583185
theorem B7642187 : Blo 1508951 7642187 := bstep (se 1 (by rfl) ⟨5731640, by rfl⟩ : syracuseStep 7642187 = 11463281) B11463281
theorem B8600651 : Blo 1508951 8600651 := bstep (se 1 (by rfl) ⟨6450488, by rfl⟩ : syracuseStep 8600651 = 12900977) B12900977
theorem B3398795 : Blo 1508951 3398795 := bstep (se 1 (by rfl) ⟨2549096, by rfl⟩ : syracuseStep 3398795 = 5098193) B5098193
theorem B5438609 : Blo 1508951 5438609 := bstep (se 2 (by rfl) ⟨2039478, by rfl⟩ : syracuseStep 5438609 = 4078957) B4078957
theorem B3398849 : Blo 1508951 3398849 := bstep (se 2 (by rfl) ⟨1274568, by rfl⟩ : syracuseStep 3398849 = 2549137) B2549137
theorem B3226817 : Blo 1508951 3226817 := bstep (se 2 (by rfl) ⟨1210056, by rfl⟩ : syracuseStep 3226817 = 2420113) B2420113
theorem B2546903 : Blo 1508951 2546903 := bstep (se 1 (by rfl) ⟨1910177, by rfl⟩ : syracuseStep 2546903 = 3820355) B3820355
theorem B3874009 : Blo 1508951 3874009 := bstep (se 2 (by rfl) ⟨1452753, by rfl⟩ : syracuseStep 3874009 = 2905507) B2905507
theorem B2547031 : Blo 1508951 2547031 := bstep (se 1 (by rfl) ⟨1910273, by rfl⟩ : syracuseStep 2547031 = 3820547) B3820547
theorem B2866519 : Blo 1508951 2866519 := bstep (se 1 (by rfl) ⟨2149889, by rfl⟩ : syracuseStep 2866519 = 4299779) B4299779
theorem B4300121 : Blo 1508951 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B3399065 : Blo 1508951 3399065 := bstep (se 2 (by rfl) ⟨1274649, by rfl⟩ : syracuseStep 3399065 = 2549299) B2549299
theorem B2907571 : Blo 1508951 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B4300235 : Blo 1508951 4300235 := bstep (se 1 (by rfl) ⟨3225176, by rfl⟩ : syracuseStep 4300235 = 6450353) B6450353
theorem B3399155 : Blo 1508951 3399155 := bstep (se 1 (by rfl) ⟨2549366, by rfl⟩ : syracuseStep 3399155 = 5098733) B5098733
theorem B3399191 : Blo 1508951 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B16318027 : Blo 1508951 16318027 := bstep (se 1 (by rfl) ⟨12238520, by rfl⟩ : syracuseStep 16318027 = 24477041) B24477041
theorem B5095115 : Blo 1508951 5095115 := bstep (se 1 (by rfl) ⟨3821336, by rfl⟩ : syracuseStep 5095115 = 7642673) B7642673
theorem B3399371 : Blo 1508951 3399371 := bstep (se 1 (by rfl) ⟨2549528, by rfl⟩ : syracuseStep 3399371 = 5099057) B5099057
theorem B3399425 : Blo 1508951 3399425 := bstep (se 2 (by rfl) ⟨1274784, by rfl⟩ : syracuseStep 3399425 = 2549569) B2549569
theorem B2547659 : Blo 1508951 2547659 := bstep (se 1 (by rfl) ⟨1910744, by rfl⟩ : syracuseStep 2547659 = 3821489) B3821489
theorem B5095385 : Blo 1508951 5095385 := bstep (se 2 (by rfl) ⟨1910769, by rfl⟩ : syracuseStep 5095385 = 3821539) B3821539
theorem B5513177 : Blo 1508951 5513177 := bstep (se 2 (by rfl) ⟨2067441, by rfl⟩ : syracuseStep 5513177 = 4134883) B4134883
theorem B3399641 : Blo 1508951 3399641 := bstep (se 2 (by rfl) ⟨1274865, by rfl⟩ : syracuseStep 3399641 = 2549731) B2549731
theorem B5234653 : Blo 1508951 5234653 := bstep (se 3 (by rfl) ⟨981497, by rfl⟩ : syracuseStep 5234653 = 1962995) B1962995
theorem B7643159 : Blo 1508951 7643159 := bstep (se 1 (by rfl) ⟨5732369, by rfl⟩ : syracuseStep 7643159 = 11464739) B11464739
theorem B2867233 : Blo 1508951 2867233 := bstep (se 2 (by rfl) ⟨1075212, by rfl⟩ : syracuseStep 2867233 = 2150425) B2150425
theorem B4079659 : Blo 1508951 4079659 := bstep (se 1 (by rfl) ⟨3059744, by rfl⟩ : syracuseStep 4079659 = 6119489) B6119489
theorem B5439575 : Blo 1508951 5439575 := bstep (se 1 (by rfl) ⟨4079681, by rfl⟩ : syracuseStep 5439575 = 8159363) B8159363
theorem B3629323 : Blo 1508951 3629323 := bstep (se 1 (by rfl) ⟨2721992, by rfl⟩ : syracuseStep 3629323 = 5443985) B5443985
theorem B2547983 : Blo 1508951 2547983 := bstep (se 1 (by rfl) ⟨1910987, by rfl⟩ : syracuseStep 2547983 = 3821975) B3821975
theorem B2867575 : Blo 1508951 2867575 := bstep (se 1 (by rfl) ⟨2150681, by rfl⟩ : syracuseStep 2867575 = 4301363) B4301363
theorem B4301191 : Blo 1508951 4301191 := bstep (se 1 (by rfl) ⟨3225893, by rfl⟩ : syracuseStep 4301191 = 6451787) B6451787
theorem B2720147 : Blo 1508951 2720147 := bstep (se 1 (by rfl) ⟨2040110, by rfl⟩ : syracuseStep 2720147 = 4080221) B4080221
theorem B11616797 : Blo 1508951 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B5095979 : Blo 1508951 5095979 := bstep (se 1 (by rfl) ⟨3821984, by rfl⟩ : syracuseStep 5095979 = 7643969) B7643969
theorem B6120137 : Blo 1508951 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B4301579 : Blo 1508951 4301579 := bstep (se 1 (by rfl) ⟨3226184, by rfl⟩ : syracuseStep 4301579 = 6452369) B6452369
theorem B2548523 : Blo 1508951 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B2417467 : Blo 1508951 2417467 := bstep (se 1 (by rfl) ⟨1813100, by rfl⟩ : syracuseStep 2417467 = 3626201) B3626201
theorem B7857011 : Blo 1508951 7857011 := bstep (se 1 (by rfl) ⟨5892758, by rfl⟩ : syracuseStep 7857011 = 11785517) B11785517
theorem B20661155 : Blo 1508951 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B2720783 : Blo 1508951 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B7750723 : Blo 1508951 7750723 := bstep (se 1 (by rfl) ⟨5813042, by rfl⟩ : syracuseStep 7750723 = 11626085) B11626085
theorem B2548921 : Blo 1508951 2548921 := bstep (se 2 (by rfl) ⟨955845, by rfl⟩ : syracuseStep 2548921 = 1911691) B1911691
theorem B4834561 : Blo 1508951 4834561 := bstep (se 2 (by rfl) ⟨1812960, by rfl⟩ : syracuseStep 4834561 = 3625921) B3625921
theorem B5735681 : Blo 1508951 5735681 := bstep (se 2 (by rfl) ⟨2150880, by rfl⟩ : syracuseStep 5735681 = 4301761) B4301761
theorem B8160527 : Blo 1508951 8160527 := bstep (se 1 (by rfl) ⟨6120395, by rfl⟩ : syracuseStep 8160527 = 12240791) B12240791
theorem B28288387 : Blo 1508951 28288387 := bstep (se 1 (by rfl) ⟨21216290, by rfl⟩ : syracuseStep 28288387 = 42432581) B42432581
theorem B4081043 : Blo 1508951 4081043 := bstep (se 1 (by rfl) ⟨3060782, by rfl⟩ : syracuseStep 4081043 = 6121565) B6121565
theorem B2721323 : Blo 1508951 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B13780523 : Blo 1508951 13780523 := bstep (se 1 (by rfl) ⟨10335392, by rfl⟩ : syracuseStep 13780523 = 20670785) B20670785
theorem B12240503 : Blo 1508951 12240503 := bstep (se 1 (by rfl) ⟨9180377, by rfl⟩ : syracuseStep 12240503 = 18360755) B18360755
theorem B1508999 : Blo 1508951 1508999 := bstep (se 1 (by rfl) ⟨1131749, by rfl⟩ : syracuseStep 1508999 = 2263499) B2263499
theorem B1509007 : Blo 1508951 1509007 := bstep (se 1 (by rfl) ⟨1131755, by rfl⟩ : syracuseStep 1509007 = 2263511) B2263511
theorem B1509051 : Blo 1508951 1509051 := bstep (se 1 (by rfl) ⟨1131788, by rfl⟩ : syracuseStep 1509051 = 2263577) B2263577
theorem B1509127 : Blo 1508951 1509127 := bstep (se 1 (by rfl) ⟨1131845, by rfl⟩ : syracuseStep 1509127 = 2263691) B2263691
theorem B7251727 : Blo 1508951 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B1509135 : Blo 1508951 1509135 := bstep (se 1 (by rfl) ⟨1131851, by rfl⟩ : syracuseStep 1509135 = 2263703) B2263703
theorem B1509179 : Blo 1508951 1509179 := bstep (se 1 (by rfl) ⟨1131884, by rfl⟩ : syracuseStep 1509179 = 2263769) B2263769
theorem B5097275 : Blo 1508951 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B2549623 : Blo 1508951 2549623 := bstep (se 1 (by rfl) ⟨1912217, by rfl⟩ : syracuseStep 2549623 = 3824435) B3824435
theorem B1509255 : Blo 1508951 1509255 := bstep (se 1 (by rfl) ⟨1131941, by rfl⟩ : syracuseStep 1509255 = 2263883) B2263883
theorem B1509263 : Blo 1508951 1509263 := bstep (se 1 (by rfl) ⟨1131947, by rfl⟩ : syracuseStep 1509263 = 2263895) B2263895
theorem B3876761 : Blo 1508951 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B1509307 : Blo 1508951 1509307 := bstep (se 1 (by rfl) ⟨1131980, by rfl⟩ : syracuseStep 1509307 = 2263961) B2263961
theorem B2041787 : Blo 1508951 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B1509383 : Blo 1508951 1509383 := bstep (se 1 (by rfl) ⟨1132037, by rfl⟩ : syracuseStep 1509383 = 2264075) B2264075
theorem B1509391 : Blo 1508951 1509391 := bstep (se 1 (by rfl) ⟨1132043, by rfl⟩ : syracuseStep 1509391 = 2264087) B2264087
theorem B1509435 : Blo 1508951 1509435 := bstep (se 1 (by rfl) ⟨1132076, by rfl⟩ : syracuseStep 1509435 = 2264153) B2264153
theorem B19351669 : Blo 1508951 19351669 := bstep (se 5 (by rfl) ⟨907109, by rfl⟩ : syracuseStep 19351669 = 1814219) B1814219
theorem B4835447 : Blo 1508951 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B1509511 : Blo 1508951 1509511 := bstep (se 1 (by rfl) ⟨1132133, by rfl⟩ : syracuseStep 1509511 = 2264267) B2264267
theorem B1697935 : Blo 1508951 1697935 := bstep (se 1 (by rfl) ⟨1273451, by rfl⟩ : syracuseStep 1697935 = 2546903) B2546903
theorem B1509519 : Blo 1508951 1509519 := bstep (se 1 (by rfl) ⟨1132139, by rfl⟩ : syracuseStep 1509519 = 2264279) B2264279
theorem B1509563 : Blo 1508951 1509563 := bstep (se 1 (by rfl) ⟨1132172, by rfl⟩ : syracuseStep 1509563 = 2264345) B2264345
theorem B1509639 : Blo 1508951 1509639 := bstep (se 1 (by rfl) ⟨1132229, by rfl⟩ : syracuseStep 1509639 = 2264459) B2264459
theorem B1509647 : Blo 1508951 1509647 := bstep (se 1 (by rfl) ⟨1132235, by rfl⟩ : syracuseStep 1509647 = 2264471) B2264471
theorem B5097761 : Blo 1508951 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B1509691 : Blo 1508951 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B9177479 : Blo 1508951 9177479 := bstep (se 1 (by rfl) ⟨6883109, by rfl⟩ : syracuseStep 9177479 = 13766219) B13766219
theorem B1509767 : Blo 1508951 1509767 := bstep (se 1 (by rfl) ⟨1132325, by rfl⟩ : syracuseStep 1509767 = 2264651) B2264651
theorem B2263439 : Blo 1508951 2263439 := bstep (se 1 (by rfl) ⟨1697579, by rfl⟩ : syracuseStep 2263439 = 3395159) B3395159
theorem B1509775 : Blo 1508951 1509775 := bstep (se 1 (by rfl) ⟨1132331, by rfl⟩ : syracuseStep 1509775 = 2264663) B2264663
theorem B17435027 : Blo 1508951 17435027 := bstep (se 1 (by rfl) ⟨13076270, by rfl⟩ : syracuseStep 17435027 = 26152541) B26152541
theorem B14518673 : Blo 1508951 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B5736851 : Blo 1508951 5736851 := bstep (se 1 (by rfl) ⟨4302638, by rfl⟩ : syracuseStep 5736851 = 8605277) B8605277
theorem B2263481 : Blo 1508951 2263481 := bstep (se 2 (by rfl) ⟨848805, by rfl⟩ : syracuseStep 2263481 = 1697611) B1697611
theorem B1509819 : Blo 1508951 1509819 := bstep (se 1 (by rfl) ⟨1132364, by rfl⟩ : syracuseStep 1509819 = 2264729) B2264729
theorem B2263559 : Blo 1508951 2263559 := bstep (se 1 (by rfl) ⟨1697669, by rfl⟩ : syracuseStep 2263559 = 3395339) B3395339
theorem B1509895 : Blo 1508951 1509895 := bstep (se 1 (by rfl) ⟨1132421, by rfl⟩ : syracuseStep 1509895 = 2264843) B2264843
theorem B1509903 : Blo 1508951 1509903 := bstep (se 1 (by rfl) ⟨1132427, by rfl⟩ : syracuseStep 1509903 = 2264855) B2264855
theorem B2263595 : Blo 1508951 2263595 := bstep (se 1 (by rfl) ⟨1697696, by rfl⟩ : syracuseStep 2263595 = 3395393) B3395393
theorem B1509947 : Blo 1508951 1509947 := bstep (se 1 (by rfl) ⟨1132460, by rfl⟩ : syracuseStep 1509947 = 2264921) B2264921
theorem B2263625 : Blo 1508951 2263625 := bstep (se 2 (by rfl) ⟨848859, by rfl⟩ : syracuseStep 2263625 = 1697719) B1697719
theorem B4360823 : Blo 1508951 4360823 := bstep (se 1 (by rfl) ⟨3270617, by rfl⟩ : syracuseStep 4360823 = 6541235) B6541235
theorem B1698439 : Blo 1508951 1698439 := bstep (se 1 (by rfl) ⟨1273829, by rfl⟩ : syracuseStep 1698439 = 2547659) B2547659
theorem B1510023 : Blo 1508951 1510023 := bstep (se 1 (by rfl) ⟨1132517, by rfl⟩ : syracuseStep 1510023 = 2265035) B2265035
theorem B1510031 : Blo 1508951 1510031 := bstep (se 1 (by rfl) ⟨1132523, by rfl⟩ : syracuseStep 1510031 = 2265047) B2265047
theorem B2263739 : Blo 1508951 2263739 := bstep (se 1 (by rfl) ⟨1697804, by rfl⟩ : syracuseStep 2263739 = 3395609) B3395609
theorem B1510075 : Blo 1508951 1510075 := bstep (se 1 (by rfl) ⟨1132556, by rfl⟩ : syracuseStep 1510075 = 2265113) B2265113
theorem B2263799 : Blo 1508951 2263799 := bstep (se 1 (by rfl) ⟨1697849, by rfl⟩ : syracuseStep 2263799 = 3395699) B3395699
theorem B1510151 : Blo 1508951 1510151 := bstep (se 1 (by rfl) ⟨1132613, by rfl⟩ : syracuseStep 1510151 = 2265227) B2265227
theorem B2263823 : Blo 1508951 2263823 := bstep (se 1 (by rfl) ⟨1697867, by rfl⟩ : syracuseStep 2263823 = 3395735) B3395735
theorem B1510159 : Blo 1508951 1510159 := bstep (se 1 (by rfl) ⟨1132619, by rfl⟩ : syracuseStep 1510159 = 2265239) B2265239
theorem B1911595 : Blo 1508951 1911595 := bstep (se 1 (by rfl) ⟨1433696, by rfl⟩ : syracuseStep 1911595 = 2867393) B2867393
theorem B2263865 : Blo 1508951 2263865 := bstep (se 2 (by rfl) ⟨848949, by rfl⟩ : syracuseStep 2263865 = 1697899) B1697899
theorem B1698619 : Blo 1508951 1698619 := bstep (se 1 (by rfl) ⟨1273964, by rfl⟩ : syracuseStep 1698619 = 2547929) B2547929
theorem B1510203 : Blo 1508951 1510203 := bstep (se 1 (by rfl) ⟨1132652, by rfl⟩ : syracuseStep 1510203 = 2265305) B2265305
theorem B9677657 : Blo 1508951 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B5098355 : Blo 1508951 5098355 := bstep (se 1 (by rfl) ⟨3823766, by rfl⟩ : syracuseStep 5098355 = 7647533) B7647533
theorem B2263943 : Blo 1508951 2263943 := bstep (se 1 (by rfl) ⟨1697957, by rfl⟩ : syracuseStep 2263943 = 3395915) B3395915
theorem B1510279 : Blo 1508951 1510279 := bstep (se 1 (by rfl) ⟨1132709, by rfl⟩ : syracuseStep 1510279 = 2265419) B2265419
theorem B1510287 : Blo 1508951 1510287 := bstep (se 1 (by rfl) ⟨1132715, by rfl⟩ : syracuseStep 1510287 = 2265431) B2265431
theorem B8604569 : Blo 1508951 8604569 := bstep (se 2 (by rfl) ⟨3226713, by rfl⟩ : syracuseStep 8604569 = 6453427) B6453427
theorem B2263979 : Blo 1508951 2263979 := bstep (se 1 (by rfl) ⟨1697984, by rfl⟩ : syracuseStep 2263979 = 3395969) B3395969
theorem B1510331 : Blo 1508951 1510331 := bstep (se 1 (by rfl) ⟨1132748, by rfl⟩ : syracuseStep 1510331 = 2265497) B2265497
theorem B2264009 : Blo 1508951 2264009 := bstep (se 2 (by rfl) ⟨849003, by rfl⟩ : syracuseStep 2264009 = 1698007) B1698007
theorem B1510407 : Blo 1508951 1510407 := bstep (se 1 (by rfl) ⟨1132805, by rfl⟩ : syracuseStep 1510407 = 2265611) B2265611
theorem B1510415 : Blo 1508951 1510415 := bstep (se 1 (by rfl) ⟨1132811, by rfl⟩ : syracuseStep 1510415 = 2265623) B2265623
theorem B7646237 : Blo 1508951 7646237 := bstep (se 3 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 7646237 = 2867339) B2867339
theorem B1813547 : Blo 1508951 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B2264123 : Blo 1508951 2264123 := bstep (se 1 (by rfl) ⟨1698092, by rfl⟩ : syracuseStep 2264123 = 3396185) B3396185
theorem B1510459 : Blo 1508951 1510459 := bstep (se 1 (by rfl) ⟨1132844, by rfl⟩ : syracuseStep 1510459 = 2265689) B2265689
theorem B11463767 : Blo 1508951 11463767 := bstep (se 1 (by rfl) ⟨8597825, by rfl⟩ : syracuseStep 11463767 = 17195651) B17195651
theorem B2264183 : Blo 1508951 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B26143877 : Blo 1508951 26143877 := bstep (se 4 (by rfl) ⟨2450988, by rfl⟩ : syracuseStep 26143877 = 4901977) B4901977
theorem B3820679 : Blo 1508951 3820679 := bstep (se 1 (by rfl) ⟨2865509, by rfl⟩ : syracuseStep 3820679 = 5731019) B5731019
theorem B1510535 : Blo 1508951 1510535 := bstep (se 1 (by rfl) ⟨1132901, by rfl⟩ : syracuseStep 1510535 = 2265803) B2265803
theorem B2264207 : Blo 1508951 2264207 := bstep (se 1 (by rfl) ⟨1698155, by rfl⟩ : syracuseStep 2264207 = 3396311) B3396311
theorem B1510543 : Blo 1508951 1510543 := bstep (se 1 (by rfl) ⟨1132907, by rfl⟩ : syracuseStep 1510543 = 2265815) B2265815
theorem B8162477 : Blo 1508951 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B3820729 : Blo 1508951 3820729 := bstep (se 2 (by rfl) ⟨1432773, by rfl⟩ : syracuseStep 3820729 = 2865547) B2865547
theorem B2264249 : Blo 1508951 2264249 := bstep (se 2 (by rfl) ⟨849093, by rfl⟩ : syracuseStep 2264249 = 1698187) B1698187
theorem B1510587 : Blo 1508951 1510587 := bstep (se 1 (by rfl) ⟨1132940, by rfl⟩ : syracuseStep 1510587 = 2265881) B2265881
theorem B2264327 : Blo 1508951 2264327 := bstep (se 1 (by rfl) ⟨1698245, by rfl⟩ : syracuseStep 2264327 = 3396491) B3396491
theorem B1510663 : Blo 1508951 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B1699087 : Blo 1508951 1699087 := bstep (se 1 (by rfl) ⟨1274315, by rfl⟩ : syracuseStep 1699087 = 2548631) B2548631
theorem B1510671 : Blo 1508951 1510671 := bstep (se 1 (by rfl) ⟨1133003, by rfl⟩ : syracuseStep 1510671 = 2266007) B2266007
theorem B2264363 : Blo 1508951 2264363 := bstep (se 1 (by rfl) ⟨1698272, by rfl⟩ : syracuseStep 2264363 = 3396545) B3396545
theorem B1510715 : Blo 1508951 1510715 := bstep (se 1 (by rfl) ⟨1133036, by rfl⟩ : syracuseStep 1510715 = 2266073) B2266073
theorem B2264393 : Blo 1508951 2264393 := bstep (se 2 (by rfl) ⟨849147, by rfl⟩ : syracuseStep 2264393 = 1698295) B1698295
theorem B4083031 : Blo 1508951 4083031 := bstep (se 1 (by rfl) ⟨3062273, by rfl⟩ : syracuseStep 4083031 = 6124547) B6124547
theorem B1510791 : Blo 1508951 1510791 := bstep (se 1 (by rfl) ⟨1133093, by rfl⟩ : syracuseStep 1510791 = 2266187) B2266187
theorem B1510799 : Blo 1508951 1510799 := bstep (se 1 (by rfl) ⟨1133099, by rfl⟩ : syracuseStep 1510799 = 2266199) B2266199
theorem B2264507 : Blo 1508951 2264507 := bstep (se 1 (by rfl) ⟨1698380, by rfl⟩ : syracuseStep 2264507 = 3396761) B3396761
theorem B1510843 : Blo 1508951 1510843 := bstep (se 1 (by rfl) ⟨1133132, by rfl⟩ : syracuseStep 1510843 = 2266265) B2266265
theorem B2264567 : Blo 1508951 2264567 := bstep (se 1 (by rfl) ⟨1698425, by rfl⟩ : syracuseStep 2264567 = 3396851) B3396851
theorem B7646723 : Blo 1508951 7646723 := bstep (se 1 (by rfl) ⟨5735042, by rfl⟩ : syracuseStep 7646723 = 11470085) B11470085
theorem B1814023 : Blo 1508951 1814023 := bstep (se 1 (by rfl) ⟨1360517, by rfl⟩ : syracuseStep 1814023 = 2721035) B2721035
theorem B11628035 : Blo 1508951 11628035 := bstep (se 1 (by rfl) ⟨8721026, by rfl⟩ : syracuseStep 11628035 = 17442053) B17442053
theorem B1510919 : Blo 1508951 1510919 := bstep (se 1 (by rfl) ⟨1133189, by rfl⟩ : syracuseStep 1510919 = 2266379) B2266379
theorem B2264591 : Blo 1508951 2264591 := bstep (se 1 (by rfl) ⟨1698443, by rfl⟩ : syracuseStep 2264591 = 3396887) B3396887
theorem B1510927 : Blo 1508951 1510927 := bstep (se 1 (by rfl) ⟨1133195, by rfl⟩ : syracuseStep 1510927 = 2266391) B2266391
theorem B2264633 : Blo 1508951 2264633 := bstep (se 2 (by rfl) ⟨849237, by rfl⟩ : syracuseStep 2264633 = 1698475) B1698475
theorem B4591163 : Blo 1508951 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B5729879 : Blo 1508951 5729879 := bstep (se 1 (by rfl) ⟨4297409, by rfl⟩ : syracuseStep 5729879 = 8594819) B8594819
theorem B2264711 : Blo 1508951 2264711 := bstep (se 1 (by rfl) ⟨1698533, by rfl⟩ : syracuseStep 2264711 = 3397067) B3397067
theorem B2264747 : Blo 1508951 2264747 := bstep (se 1 (by rfl) ⟨1698560, by rfl⟩ : syracuseStep 2264747 = 3397121) B3397121
theorem B2264777 : Blo 1508951 2264777 := bstep (se 2 (by rfl) ⟨849291, by rfl⟩ : syracuseStep 2264777 = 1698583) B1698583
theorem B1699591 : Blo 1508951 1699591 := bstep (se 1 (by rfl) ⟨1274693, by rfl⟩ : syracuseStep 1699591 = 2549387) B2549387
theorem B3821327 : Blo 1508951 3821327 := bstep (se 1 (by rfl) ⟨2865995, by rfl⟩ : syracuseStep 3821327 = 5731991) B5731991
theorem B2264891 : Blo 1508951 2264891 := bstep (se 1 (by rfl) ⟨1698668, by rfl⟩ : syracuseStep 2264891 = 3397337) B3397337
theorem B16330571 : Blo 1508951 16330571 := bstep (se 1 (by rfl) ⟨12247928, by rfl⟩ : syracuseStep 16330571 = 24495857) B24495857
theorem B3395447 : Blo 1508951 3395447 := bstep (se 1 (by rfl) ⟨2546585, by rfl⟩ : syracuseStep 3395447 = 5093171) B5093171
theorem B2264951 : Blo 1508951 2264951 := bstep (se 1 (by rfl) ⟨1698713, by rfl⟩ : syracuseStep 2264951 = 3397427) B3397427
theorem B2264975 : Blo 1508951 2264975 := bstep (se 1 (by rfl) ⟨1698731, by rfl⟩ : syracuseStep 2264975 = 3397463) B3397463
theorem B2265017 : Blo 1508951 2265017 := bstep (se 2 (by rfl) ⟨849381, by rfl⟩ : syracuseStep 2265017 = 1698763) B1698763
theorem B1699771 : Blo 1508951 1699771 := bstep (se 1 (by rfl) ⟨1274828, by rfl⟩ : syracuseStep 1699771 = 2549657) B2549657
theorem B2150345 : Blo 1508951 2150345 := bstep (se 2 (by rfl) ⟨806379, by rfl⟩ : syracuseStep 2150345 = 1612759) B1612759
theorem B2265095 : Blo 1508951 2265095 := bstep (se 1 (by rfl) ⟨1698821, by rfl⟩ : syracuseStep 2265095 = 3397643) B3397643
theorem B3395627 : Blo 1508951 3395627 := bstep (se 1 (by rfl) ⟨2546720, by rfl⟩ : syracuseStep 3395627 = 5093441) B5093441
theorem B2265131 : Blo 1508951 2265131 := bstep (se 1 (by rfl) ⟨1698848, by rfl⟩ : syracuseStep 2265131 = 3397697) B3397697
theorem B5730365 : Blo 1508951 5730365 := bstep (se 3 (by rfl) ⟨1074443, by rfl⟩ : syracuseStep 5730365 = 2148887) B2148887
theorem B2265161 : Blo 1508951 2265161 := bstep (se 2 (by rfl) ⟨849435, by rfl⟩ : syracuseStep 2265161 = 1698871) B1698871
theorem B2265275 : Blo 1508951 2265275 := bstep (se 1 (by rfl) ⟨1698956, by rfl⟩ : syracuseStep 2265275 = 3397913) B3397913
theorem B2265335 : Blo 1508951 2265335 := bstep (se 1 (by rfl) ⟨1699001, by rfl⟩ : syracuseStep 2265335 = 3398003) B3398003
theorem B2265359 : Blo 1508951 2265359 := bstep (se 1 (by rfl) ⟨1699019, by rfl⟩ : syracuseStep 2265359 = 3398039) B3398039
theorem B4296989 : Blo 1508951 4296989 := bstep (se 3 (by rfl) ⟨805685, by rfl⟩ : syracuseStep 4296989 = 1611371) B1611371
theorem B5165345 : Blo 1508951 5165345 := bstep (se 2 (by rfl) ⟨1937004, by rfl⟩ : syracuseStep 5165345 = 3874009) B3874009
theorem B2265401 : Blo 1508951 2265401 := bstep (se 2 (by rfl) ⟨849525, by rfl⟩ : syracuseStep 2265401 = 1699051) B1699051
theorem B2265479 : Blo 1508951 2265479 := bstep (se 1 (by rfl) ⟨1699109, by rfl⟩ : syracuseStep 2265479 = 3398219) B3398219
theorem B3395987 : Blo 1508951 3395987 := bstep (se 1 (by rfl) ⟨2546990, by rfl⟩ : syracuseStep 3395987 = 5093981) B5093981
theorem B2265515 : Blo 1508951 2265515 := bstep (se 1 (by rfl) ⟨1699136, by rfl⟩ : syracuseStep 2265515 = 3398273) B3398273
theorem B3396041 : Blo 1508951 3396041 := bstep (se 2 (by rfl) ⟨1273515, by rfl⟩ : syracuseStep 3396041 = 2547031) B2547031
theorem B3822025 : Blo 1508951 3822025 := bstep (se 2 (by rfl) ⟨1433259, by rfl⟩ : syracuseStep 3822025 = 2866519) B2866519
theorem B2265545 : Blo 1508951 2265545 := bstep (se 2 (by rfl) ⟨849579, by rfl⟩ : syracuseStep 2265545 = 1699159) B1699159
theorem B29037041 : Blo 1508951 29037041 := bstep (se 2 (by rfl) ⟨10888890, by rfl⟩ : syracuseStep 29037041 = 21777781) B21777781
theorem B7639595 : Blo 1508951 7639595 := bstep (se 1 (by rfl) ⟨5729696, by rfl⟩ : syracuseStep 7639595 = 11459393) B11459393
theorem B2265659 : Blo 1508951 2265659 := bstep (se 1 (by rfl) ⟨1699244, by rfl⟩ : syracuseStep 2265659 = 3398489) B3398489
theorem B3822167 : Blo 1508951 3822167 := bstep (se 1 (by rfl) ⟨2866625, by rfl⟩ : syracuseStep 3822167 = 5733251) B5733251
theorem B2265719 : Blo 1508951 2265719 := bstep (se 1 (by rfl) ⟨1699289, by rfl⟩ : syracuseStep 2265719 = 3398579) B3398579
theorem B12907127 : Blo 1508951 12907127 := bstep (se 1 (by rfl) ⟨9680345, by rfl⟩ : syracuseStep 12907127 = 19360691) B19360691
theorem B2265743 : Blo 1508951 2265743 := bstep (se 1 (by rfl) ⟨1699307, by rfl⟩ : syracuseStep 2265743 = 3398615) B3398615
theorem B2265785 : Blo 1508951 2265785 := bstep (se 2 (by rfl) ⟨849669, by rfl⟩ : syracuseStep 2265785 = 1699339) B1699339
theorem B5444333 : Blo 1508951 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B2265863 : Blo 1508951 2265863 := bstep (se 1 (by rfl) ⟨1699397, by rfl⟩ : syracuseStep 2265863 = 3398795) B3398795
theorem B3625739 : Blo 1508951 3625739 := bstep (se 1 (by rfl) ⟨2719304, by rfl⟩ : syracuseStep 3625739 = 5438609) B5438609
theorem B2265899 : Blo 1508951 2265899 := bstep (se 1 (by rfl) ⟨1699424, by rfl⟩ : syracuseStep 2265899 = 3398849) B3398849
theorem B2151211 : Blo 1508951 2151211 := bstep (se 1 (by rfl) ⟨1613408, by rfl⟩ : syracuseStep 2151211 = 3226817) B3226817
theorem B2265929 : Blo 1508951 2265929 := bstep (se 2 (by rfl) ⟨849723, by rfl⟩ : syracuseStep 2265929 = 1699447) B1699447
theorem B8598419 : Blo 1508951 8598419 := bstep (se 1 (by rfl) ⟨6448814, by rfl⟩ : syracuseStep 8598419 = 12897629) B12897629
theorem B17200025 : Blo 1508951 17200025 := bstep (se 2 (by rfl) ⟨6450009, by rfl⟩ : syracuseStep 17200025 = 12900019) B12900019
theorem B2266043 : Blo 1508951 2266043 := bstep (se 1 (by rfl) ⟨1699532, by rfl⟩ : syracuseStep 2266043 = 3399065) B3399065
theorem B2266103 : Blo 1508951 2266103 := bstep (se 1 (by rfl) ⟨1699577, by rfl⟩ : syracuseStep 2266103 = 3399155) B3399155
theorem B2266127 : Blo 1508951 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B2266169 : Blo 1508951 2266169 := bstep (se 2 (by rfl) ⟨849813, by rfl⟩ : syracuseStep 2266169 = 1699627) B1699627
theorem B7648343 : Blo 1508951 7648343 := bstep (se 1 (by rfl) ⟨5736257, by rfl⟩ : syracuseStep 7648343 = 11472515) B11472515
theorem B6124663 : Blo 1508951 6124663 := bstep (se 1 (by rfl) ⟨4593497, by rfl⟩ : syracuseStep 6124663 = 9186995) B9186995
theorem B3396743 : Blo 1508951 3396743 := bstep (se 1 (by rfl) ⟨2547557, by rfl⟩ : syracuseStep 3396743 = 5095115) B5095115
theorem B2266247 : Blo 1508951 2266247 := bstep (se 1 (by rfl) ⟨1699685, by rfl⟩ : syracuseStep 2266247 = 3399371) B3399371
theorem B2266283 : Blo 1508951 2266283 := bstep (se 1 (by rfl) ⟨1699712, by rfl⟩ : syracuseStep 2266283 = 3399425) B3399425
theorem B2266313 : Blo 1508951 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B9180449 : Blo 1508951 9180449 := bstep (se 2 (by rfl) ⟨3442668, by rfl⟩ : syracuseStep 9180449 = 6885337) B6885337
theorem B3675451 : Blo 1508951 3675451 := bstep (se 1 (by rfl) ⟨2756588, by rfl⟩ : syracuseStep 3675451 = 5513177) B5513177
theorem B3396923 : Blo 1508951 3396923 := bstep (se 1 (by rfl) ⟨2547692, by rfl⟩ : syracuseStep 3396923 = 5095385) B5095385
theorem B2266427 : Blo 1508951 2266427 := bstep (se 1 (by rfl) ⟨1699820, by rfl⟩ : syracuseStep 2266427 = 3399641) B3399641
theorem B8598919 : Blo 1508951 8598919 := bstep (se 1 (by rfl) ⟨6449189, by rfl⟩ : syracuseStep 8598919 = 12898379) B12898379
theorem B4904339 : Blo 1508951 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B5092793 : Blo 1508951 5092793 := bstep (se 2 (by rfl) ⟨1909797, by rfl⟩ : syracuseStep 5092793 = 3819595) B3819595
theorem B3397049 : Blo 1508951 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B5731793 : Blo 1508951 5731793 := bstep (se 2 (by rfl) ⟨2149422, by rfl⟩ : syracuseStep 5731793 = 4298845) B4298845
theorem B5518891 : Blo 1508951 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B7648829 : Blo 1508951 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B36738629 : Blo 1508951 36738629 := bstep (se 4 (by rfl) ⟨3444246, by rfl⟩ : syracuseStep 36738629 = 6888493) B6888493
theorem B3397391 : Blo 1508951 3397391 := bstep (se 1 (by rfl) ⟨2548043, by rfl⟩ : syracuseStep 3397391 = 5096087) B5096087
theorem B6125327 : Blo 1508951 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B3397409 : Blo 1508951 3397409 := bstep (se 2 (by rfl) ⟨1274028, by rfl⟩ : syracuseStep 3397409 = 2548057) B2548057
theorem B7640891 : Blo 1508951 7640891 := bstep (se 1 (by rfl) ⟨5730668, by rfl⟩ : syracuseStep 7640891 = 11461337) B11461337
theorem B4839353 : Blo 1508951 4839353 := bstep (se 2 (by rfl) ⟨1814757, by rfl⟩ : syracuseStep 4839353 = 3629515) B3629515
theorem B7641053 : Blo 1508951 7641053 := bstep (se 3 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 7641053 = 2865395) B2865395
theorem B5093387 : Blo 1508951 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B35330165 : Blo 1508951 35330165 := bstep (se 5 (by rfl) ⟨1656101, by rfl⟩ : syracuseStep 35330165 = 3312203) B3312203
theorem B5093495 : Blo 1508951 5093495 := bstep (se 1 (by rfl) ⟨3820121, by rfl⟩ : syracuseStep 5093495 = 7640243) B7640243
theorem B3397751 : Blo 1508951 3397751 := bstep (se 1 (by rfl) ⟨2548313, by rfl⟩ : syracuseStep 3397751 = 5096627) B5096627
theorem B7641377 : Blo 1508951 7641377 := bstep (se 2 (by rfl) ⟨2865516, by rfl⟩ : syracuseStep 7641377 = 5731033) B5731033
theorem B4839713 : Blo 1508951 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B3397931 : Blo 1508951 3397931 := bstep (se 1 (by rfl) ⟨2548448, by rfl⟩ : syracuseStep 3397931 = 5096897) B5096897
theorem B9673019 : Blo 1508951 9673019 := bstep (se 1 (by rfl) ⟨7254764, by rfl⟩ : syracuseStep 9673019 = 14509529) B14509529
theorem B4299095 : Blo 1508951 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B2865593 : Blo 1508951 2865593 := bstep (se 2 (by rfl) ⟨1074597, by rfl⟩ : syracuseStep 2865593 = 2149195) B2149195
theorem B3824243 : Blo 1508951 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B3398291 : Blo 1508951 3398291 := bstep (se 1 (by rfl) ⟨2548718, by rfl⟩ : syracuseStep 3398291 = 5097437) B5097437
theorem B5094089 : Blo 1508951 5094089 := bstep (se 2 (by rfl) ⟨1910283, by rfl⟩ : syracuseStep 5094089 = 3820567) B3820567
theorem B3398345 : Blo 1508951 3398345 := bstep (se 2 (by rfl) ⟨1274379, by rfl⟩ : syracuseStep 3398345 = 2548759) B2548759
theorem B3267343 : Blo 1508951 3267343 := bstep (se 1 (by rfl) ⟨2450507, by rfl⟩ : syracuseStep 3267343 = 4901015) B4901015
theorem B2865935 : Blo 1508951 2865935 := bstep (se 1 (by rfl) ⟨2149451, by rfl⟩ : syracuseStep 2865935 = 4298903) B4298903
theorem B2546491 : Blo 1508951 2546491 := bstep (se 1 (by rfl) ⟨1909868, by rfl⟩ : syracuseStep 2546491 = 3819737) B3819737
theorem B4840327 : Blo 1508951 4840327 := bstep (se 1 (by rfl) ⟨3630245, by rfl⟩ : syracuseStep 4840327 = 7260491) B7260491
theorem B2546633 : Blo 1508951 2546633 := bstep (se 2 (by rfl) ⟨954987, by rfl⟩ : syracuseStep 2546633 = 1909975) B1909975
theorem B4250639 : Blo 1508951 4250639 := bstep (se 1 (by rfl) ⟨3187979, by rfl⟩ : syracuseStep 4250639 = 6375959) B6375959
theorem B5733463 : Blo 1508951 5733463 := bstep (se 1 (by rfl) ⟨4300097, by rfl⟩ : syracuseStep 5733463 = 8600195) B8600195
theorem B4299961 : Blo 1508951 4299961 := bstep (se 2 (by rfl) ⟨1612485, by rfl⟩ : syracuseStep 4299961 = 3224971) B3224971
theorem B11623625 : Blo 1508951 11623625 := bstep (se 2 (by rfl) ⟨4358859, by rfl⟩ : syracuseStep 11623625 = 8717719) B8717719
theorem B7642349 : Blo 1508951 7642349 := bstep (se 3 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 7642349 = 2865881) B2865881
theorem B7257377 : Blo 1508951 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B5094791 : Blo 1508951 5094791 := bstep (se 1 (by rfl) ⟨3821093, by rfl⟩ : syracuseStep 5094791 = 7642187) B7642187
theorem B5733767 : Blo 1508951 5733767 := bstep (se 1 (by rfl) ⟨4300325, by rfl⟩ : syracuseStep 5733767 = 8600651) B8600651
theorem B3399047 : Blo 1508951 3399047 := bstep (se 1 (by rfl) ⟨2549285, by rfl⟩ : syracuseStep 3399047 = 5098571) B5098571
theorem B32644529 : Blo 1508951 32644529 := bstep (se 2 (by rfl) ⟨12241698, by rfl⟩ : syracuseStep 32644529 = 24483397) B24483397
theorem B21757369 : Blo 1508951 21757369 := bstep (se 2 (by rfl) ⟨8159013, by rfl⟩ : syracuseStep 21757369 = 16318027) B16318027
theorem B38723021 : Blo 1508951 38723021 := bstep (se 3 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 38723021 = 14521133) B14521133
theorem B4300303 : Blo 1508951 4300303 := bstep (se 1 (by rfl) ⟨3225227, by rfl⟩ : syracuseStep 4300303 = 6450455) B6450455
theorem B10886699 : Blo 1508951 10886699 := bstep (se 1 (by rfl) ⟨8165024, by rfl⟩ : syracuseStep 10886699 = 16330049) B16330049
theorem B2866747 : Blo 1508951 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B3399227 : Blo 1508951 3399227 := bstep (se 1 (by rfl) ⟨2549420, by rfl⟩ : syracuseStep 3399227 = 5098841) B5098841
theorem B5733949 : Blo 1508951 5733949 := bstep (se 3 (by rfl) ⟨1075115, by rfl⟩ : syracuseStep 5733949 = 2150231) B2150231
theorem B2547335 : Blo 1508951 2547335 := bstep (se 1 (by rfl) ⟨1910501, by rfl⟩ : syracuseStep 2547335 = 3821003) B3821003
theorem B2866823 : Blo 1508951 2866823 := bstep (se 1 (by rfl) ⟨2150117, by rfl⟩ : syracuseStep 2866823 = 4300235) B4300235
theorem B3399353 : Blo 1508951 3399353 := bstep (se 2 (by rfl) ⟨1274757, by rfl⟩ : syracuseStep 3399353 = 2549515) B2549515
theorem B2039483 : Blo 1508951 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B11034305 : Blo 1508951 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B5095169 : Blo 1508951 5095169 := bstep (se 2 (by rfl) ⟨1910688, by rfl⟩ : syracuseStep 5095169 = 3821377) B3821377
theorem B4300577 : Blo 1508951 4300577 := bstep (se 2 (by rfl) ⟨1612716, by rfl⟩ : syracuseStep 4300577 = 3225433) B3225433
theorem B45317933 : Blo 1508951 45317933 := bstep (se 3 (by rfl) ⟨8497112, by rfl⟩ : syracuseStep 45317933 = 16994225) B16994225
theorem B6979537 : Blo 1508951 6979537 := bstep (se 2 (by rfl) ⟨2617326, by rfl⟩ : syracuseStep 6979537 = 5234653) B5234653
theorem B5095439 : Blo 1508951 5095439 := bstep (se 1 (by rfl) ⟨3821579, by rfl⟩ : syracuseStep 5095439 = 7643159) B7643159
theorem B5439545 : Blo 1508951 5439545 := bstep (se 2 (by rfl) ⟨2039829, by rfl⟩ : syracuseStep 5439545 = 4079659) B4079659
theorem B19358027 : Blo 1508951 19358027 := bstep (se 1 (by rfl) ⟨14518520, by rfl⟩ : syracuseStep 19358027 = 29037041) B29037041
theorem B2548111 : Blo 1508951 2548111 := bstep (se 1 (by rfl) ⟨1911083, by rfl⟩ : syracuseStep 2548111 = 3822167) B3822167
theorem B3629555 : Blo 1508951 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B2417159 : Blo 1508951 2417159 := bstep (se 1 (by rfl) ⟨1812869, by rfl⟩ : syracuseStep 2417159 = 3625739) B3625739
theorem B2867719 : Blo 1508951 2867719 := bstep (se 1 (by rfl) ⟨2150789, by rfl⟩ : syracuseStep 2867719 = 4301579) B4301579
theorem B5734921 : Blo 1508951 5734921 := bstep (se 2 (by rfl) ⟨2150595, by rfl⟩ : syracuseStep 5734921 = 4301191) B4301191
theorem B5096033 : Blo 1508951 5096033 := bstep (se 2 (by rfl) ⟨1911012, by rfl⟩ : syracuseStep 5096033 = 3822025) B3822025
theorem B5440351 : Blo 1508951 5440351 := bstep (se 1 (by rfl) ⟨4080263, by rfl⟩ : syracuseStep 5440351 = 8160527) B8160527
theorem B6120299 : Blo 1508951 6120299 := bstep (se 1 (by rfl) ⟨4590224, by rfl⟩ : syracuseStep 6120299 = 9180449) B9180449
theorem B2720695 : Blo 1508951 2720695 := bstep (se 1 (by rfl) ⟨2040521, by rfl⟩ : syracuseStep 2720695 = 4081043) B4081043
theorem B2548793 : Blo 1508951 2548793 := bstep (se 2 (by rfl) ⟨955797, by rfl⟩ : syracuseStep 2548793 = 1911595) B1911595
theorem B2868281 : Blo 1508951 2868281 := bstep (se 2 (by rfl) ⟨1075605, by rfl⟩ : syracuseStep 2868281 = 2151211) B2151211
theorem B8160335 : Blo 1508951 8160335 := bstep (se 1 (by rfl) ⟨6120251, by rfl⟩ : syracuseStep 8160335 = 12240503) B12240503
theorem B23553443 : Blo 1508951 23553443 := bstep (se 1 (by rfl) ⟨17665082, by rfl⟩ : syracuseStep 23553443 = 35330165) B35330165
theorem B17425829 : Blo 1508951 17425829 := bstep (se 4 (by rfl) ⟨1633671, by rfl⟩ : syracuseStep 17425829 = 3267343) B3267343
theorem B7644617 : Blo 1508951 7644617 := bstep (se 2 (by rfl) ⟨2866731, by rfl⟩ : syracuseStep 7644617 = 5733463) B5733463
theorem B6448679 : Blo 1508951 6448679 := bstep (se 1 (by rfl) ⟨4836509, by rfl⟩ : syracuseStep 6448679 = 9673019) B9673019
theorem B1508959 : Blo 1508951 1508959 := bstep (se 1 (by rfl) ⟨1131719, by rfl⟩ : syracuseStep 1508959 = 2263439) B2263439
theorem B1508987 : Blo 1508951 1508987 := bstep (se 1 (by rfl) ⟨1131740, by rfl⟩ : syracuseStep 1508987 = 2263481) B2263481
theorem B1910395 : Blo 1508951 1910395 := bstep (se 1 (by rfl) ⟨1432796, by rfl⟩ : syracuseStep 1910395 = 2865593) B2865593
theorem B1509039 : Blo 1508951 1509039 := bstep (se 1 (by rfl) ⟨1131779, by rfl⟩ : syracuseStep 1509039 = 2263559) B2263559
theorem B1509063 : Blo 1508951 1509063 := bstep (se 1 (by rfl) ⟨1131797, by rfl⟩ : syracuseStep 1509063 = 2263595) B2263595
theorem B1509083 : Blo 1508951 1509083 := bstep (se 1 (by rfl) ⟨1131812, by rfl⟩ : syracuseStep 1509083 = 2263625) B2263625
theorem B2549495 : Blo 1508951 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B4900601 : Blo 1508951 4900601 := bstep (se 2 (by rfl) ⟨1837725, by rfl⟩ : syracuseStep 4900601 = 3675451) B3675451
theorem B21776165 : Blo 1508951 21776165 := bstep (se 4 (by rfl) ⟨2041515, by rfl⟩ : syracuseStep 21776165 = 4083031) B4083031
theorem B1509159 : Blo 1508951 1509159 := bstep (se 1 (by rfl) ⟨1131869, by rfl⟩ : syracuseStep 1509159 = 2263739) B2263739
theorem B1509199 : Blo 1508951 1509199 := bstep (se 1 (by rfl) ⟨1131899, by rfl⟩ : syracuseStep 1509199 = 2263799) B2263799
theorem B37717849 : Blo 1508951 37717849 := bstep (se 2 (by rfl) ⟨14144193, by rfl⟩ : syracuseStep 37717849 = 28288387) B28288387
theorem B1509215 : Blo 1508951 1509215 := bstep (se 1 (by rfl) ⟨1131911, by rfl⟩ : syracuseStep 1509215 = 2263823) B2263823
theorem B1910623 : Blo 1508951 1910623 := bstep (se 1 (by rfl) ⟨1432967, by rfl⟩ : syracuseStep 1910623 = 2865935) B2865935
theorem B16320365 : Blo 1508951 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B1509243 : Blo 1508951 1509243 := bstep (se 1 (by rfl) ⟨1131932, by rfl⟩ : syracuseStep 1509243 = 2263865) B2263865
theorem B29009825 : Blo 1508951 29009825 := bstep (se 2 (by rfl) ⟨10878684, by rfl⟩ : syracuseStep 29009825 = 21757369) B21757369
theorem B1509295 : Blo 1508951 1509295 := bstep (se 1 (by rfl) ⟨1131971, by rfl⟩ : syracuseStep 1509295 = 2263943) B2263943
theorem B5736379 : Blo 1508951 5736379 := bstep (se 1 (by rfl) ⟨4302284, by rfl⟩ : syracuseStep 5736379 = 8604569) B8604569
theorem B1509319 : Blo 1508951 1509319 := bstep (se 1 (by rfl) ⟨1131989, by rfl⟩ : syracuseStep 1509319 = 2263979) B2263979
theorem B1697755 : Blo 1508951 1697755 := bstep (se 1 (by rfl) ⟨1273316, by rfl⟩ : syracuseStep 1697755 = 2546633) B2546633
theorem B1509339 : Blo 1508951 1509339 := bstep (se 1 (by rfl) ⟨1132004, by rfl⟩ : syracuseStep 1509339 = 2264009) B2264009
theorem B2418697 : Blo 1508951 2418697 := bstep (se 2 (by rfl) ⟨907011, by rfl⟩ : syracuseStep 2418697 = 1814023) B1814023
theorem B5097491 : Blo 1508951 5097491 := bstep (se 1 (by rfl) ⟨3823118, by rfl⟩ : syracuseStep 5097491 = 7646237) B7646237
theorem B1509415 : Blo 1508951 1509415 := bstep (se 1 (by rfl) ⟨1132061, by rfl⟩ : syracuseStep 1509415 = 2264123) B2264123
theorem B7358521 : Blo 1508951 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B1509455 : Blo 1508951 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B7645265 : Blo 1508951 7645265 := bstep (se 2 (by rfl) ⟨2866974, by rfl⟩ : syracuseStep 7645265 = 5733949) B5733949
theorem B1509471 : Blo 1508951 1509471 := bstep (se 1 (by rfl) ⟨1132103, by rfl⟩ : syracuseStep 1509471 = 2264207) B2264207
theorem B5441651 : Blo 1508951 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B1509499 : Blo 1508951 1509499 := bstep (se 1 (by rfl) ⟨1132124, by rfl⟩ : syracuseStep 1509499 = 2264249) B2264249
theorem B1509551 : Blo 1508951 1509551 := bstep (se 1 (by rfl) ⟨1132163, by rfl⟩ : syracuseStep 1509551 = 2264327) B2264327
theorem B1509575 : Blo 1508951 1509575 := bstep (se 1 (by rfl) ⟨1132181, by rfl⟩ : syracuseStep 1509575 = 2264363) B2264363
theorem B1509595 : Blo 1508951 1509595 := bstep (se 1 (by rfl) ⟨1132196, by rfl⟩ : syracuseStep 1509595 = 2264393) B2264393
theorem B1509671 : Blo 1508951 1509671 := bstep (se 1 (by rfl) ⟨1132253, by rfl⟩ : syracuseStep 1509671 = 2264507) B2264507
theorem B25815347 : Blo 1508951 25815347 := bstep (se 1 (by rfl) ⟨19361510, by rfl⟩ : syracuseStep 25815347 = 38723021) B38723021
theorem B1509711 : Blo 1508951 1509711 := bstep (se 1 (by rfl) ⟨1132283, by rfl⟩ : syracuseStep 1509711 = 2264567) B2264567
theorem B5097815 : Blo 1508951 5097815 := bstep (se 1 (by rfl) ⟨3823361, by rfl⟩ : syracuseStep 5097815 = 7646723) B7646723
theorem B7752023 : Blo 1508951 7752023 := bstep (se 1 (by rfl) ⟨5814017, by rfl⟩ : syracuseStep 7752023 = 11628035) B11628035
theorem B1509727 : Blo 1508951 1509727 := bstep (se 1 (by rfl) ⟨1132295, by rfl⟩ : syracuseStep 1509727 = 2264591) B2264591
theorem B9668969 : Blo 1508951 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B1509755 : Blo 1508951 1509755 := bstep (se 1 (by rfl) ⟨1132316, by rfl⟩ : syracuseStep 1509755 = 2264633) B2264633
theorem B3819919 : Blo 1508951 3819919 := bstep (se 1 (by rfl) ⟨2864939, by rfl⟩ : syracuseStep 3819919 = 5729879) B5729879
theorem B1698223 : Blo 1508951 1698223 := bstep (se 1 (by rfl) ⟨1273667, by rfl⟩ : syracuseStep 1698223 = 2547335) B2547335
theorem B1509807 : Blo 1508951 1509807 := bstep (se 1 (by rfl) ⟨1132355, by rfl⟩ : syracuseStep 1509807 = 2264711) B2264711
theorem B1911215 : Blo 1508951 1911215 := bstep (se 1 (by rfl) ⟨1433411, by rfl⟩ : syracuseStep 1911215 = 2866823) B2866823
theorem B1509831 : Blo 1508951 1509831 := bstep (se 1 (by rfl) ⟨1132373, by rfl⟩ : syracuseStep 1509831 = 2264747) B2264747
theorem B1509851 : Blo 1508951 1509851 := bstep (se 1 (by rfl) ⟨1132388, by rfl⟩ : syracuseStep 1509851 = 2264777) B2264777
theorem B1509927 : Blo 1508951 1509927 := bstep (se 1 (by rfl) ⟨1132445, by rfl⟩ : syracuseStep 1509927 = 2264891) B2264891
theorem B2263631 : Blo 1508951 2263631 := bstep (se 1 (by rfl) ⟨1697723, by rfl⟩ : syracuseStep 2263631 = 3395447) B3395447
theorem B1509967 : Blo 1508951 1509967 := bstep (se 1 (by rfl) ⟨1132475, by rfl⟩ : syracuseStep 1509967 = 2264951) B2264951
theorem B1509983 : Blo 1508951 1509983 := bstep (se 1 (by rfl) ⟨1132487, by rfl⟩ : syracuseStep 1509983 = 2264975) B2264975
theorem B1510011 : Blo 1508951 1510011 := bstep (se 1 (by rfl) ⟨1132508, by rfl⟩ : syracuseStep 1510011 = 2265017) B2265017
theorem B1510063 : Blo 1508951 1510063 := bstep (se 1 (by rfl) ⟨1132547, by rfl⟩ : syracuseStep 1510063 = 2265095) B2265095
theorem B2263751 : Blo 1508951 2263751 := bstep (se 1 (by rfl) ⟨1697813, by rfl⟩ : syracuseStep 2263751 = 3395627) B3395627
theorem B1510087 : Blo 1508951 1510087 := bstep (se 1 (by rfl) ⟨1132565, by rfl⟩ : syracuseStep 1510087 = 2265131) B2265131
theorem B3820243 : Blo 1508951 3820243 := bstep (se 1 (by rfl) ⟨2865182, by rfl⟩ : syracuseStep 3820243 = 5730365) B5730365
theorem B1510107 : Blo 1508951 1510107 := bstep (se 1 (by rfl) ⟨1132580, by rfl⟩ : syracuseStep 1510107 = 2265161) B2265161
theorem B4836125 : Blo 1508951 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B1510183 : Blo 1508951 1510183 := bstep (se 1 (by rfl) ⟨1132637, by rfl⟩ : syracuseStep 1510183 = 2265275) B2265275
theorem B1510223 : Blo 1508951 1510223 := bstep (se 1 (by rfl) ⟨1132667, by rfl⟩ : syracuseStep 1510223 = 2265335) B2265335
theorem B1698655 : Blo 1508951 1698655 := bstep (se 1 (by rfl) ⟨1273991, by rfl⟩ : syracuseStep 1698655 = 2547983) B2547983
theorem B1510239 : Blo 1508951 1510239 := bstep (se 1 (by rfl) ⟨1132679, by rfl⟩ : syracuseStep 1510239 = 2265359) B2265359
theorem B2263913 : Blo 1508951 2263913 := bstep (se 2 (by rfl) ⟨848967, by rfl⟩ : syracuseStep 2263913 = 1697935) B1697935
theorem B3443563 : Blo 1508951 3443563 := bstep (se 1 (by rfl) ⟨2582672, by rfl⟩ : syracuseStep 3443563 = 5165345) B5165345
theorem B1510267 : Blo 1508951 1510267 := bstep (se 1 (by rfl) ⟨1132700, by rfl⟩ : syracuseStep 1510267 = 2265401) B2265401
theorem B1510319 : Blo 1508951 1510319 := bstep (se 1 (by rfl) ⟨1132739, by rfl⟩ : syracuseStep 1510319 = 2265479) B2265479
theorem B2263991 : Blo 1508951 2263991 := bstep (se 1 (by rfl) ⟨1697993, by rfl⟩ : syracuseStep 2263991 = 3395987) B3395987
theorem B1510343 : Blo 1508951 1510343 := bstep (se 1 (by rfl) ⟨1132757, by rfl⟩ : syracuseStep 1510343 = 2265515) B2265515
theorem B2264027 : Blo 1508951 2264027 := bstep (se 1 (by rfl) ⟨1698020, by rfl⟩ : syracuseStep 2264027 = 3396041) B3396041
theorem B1510363 : Blo 1508951 1510363 := bstep (se 1 (by rfl) ⟨1132772, by rfl⟩ : syracuseStep 1510363 = 2265545) B2265545
theorem B1510439 : Blo 1508951 1510439 := bstep (se 1 (by rfl) ⟨1132829, by rfl⟩ : syracuseStep 1510439 = 2265659) B2265659
theorem B1510479 : Blo 1508951 1510479 := bstep (se 1 (by rfl) ⟨1132859, by rfl⟩ : syracuseStep 1510479 = 2265719) B2265719
theorem B8604751 : Blo 1508951 8604751 := bstep (se 1 (by rfl) ⟨6453563, by rfl⟩ : syracuseStep 8604751 = 12907127) B12907127
theorem B1510495 : Blo 1508951 1510495 := bstep (se 1 (by rfl) ⟨1132871, by rfl⟩ : syracuseStep 1510495 = 2265743) B2265743
theorem B1510523 : Blo 1508951 1510523 := bstep (se 1 (by rfl) ⟨1132892, by rfl⟩ : syracuseStep 1510523 = 2265785) B2265785
theorem B1510575 : Blo 1508951 1510575 := bstep (se 1 (by rfl) ⟨1132931, by rfl⟩ : syracuseStep 1510575 = 2265863) B2265863
theorem B1699015 : Blo 1508951 1699015 := bstep (se 1 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 1699015 = 2548523) B2548523
theorem B1510599 : Blo 1508951 1510599 := bstep (se 1 (by rfl) ⟨1132949, by rfl⟩ : syracuseStep 1510599 = 2265899) B2265899
theorem B1510619 : Blo 1508951 1510619 := bstep (se 1 (by rfl) ⟨1132964, by rfl⟩ : syracuseStep 1510619 = 2265929) B2265929
theorem B13774103 : Blo 1508951 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B1510695 : Blo 1508951 1510695 := bstep (se 1 (by rfl) ⟨1133021, by rfl⟩ : syracuseStep 1510695 = 2266043) B2266043
theorem B1510735 : Blo 1508951 1510735 := bstep (se 1 (by rfl) ⟨1133051, by rfl⟩ : syracuseStep 1510735 = 2266103) B2266103
theorem B1813855 : Blo 1508951 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B1510751 : Blo 1508951 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B1510779 : Blo 1508951 1510779 := bstep (se 1 (by rfl) ⟨1133084, by rfl⟩ : syracuseStep 1510779 = 2266169) B2266169
theorem B5098895 : Blo 1508951 5098895 := bstep (se 1 (by rfl) ⟨3824171, by rfl⟩ : syracuseStep 5098895 = 7648343) B7648343
theorem B19353005 : Blo 1508951 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B2264495 : Blo 1508951 2264495 := bstep (se 1 (by rfl) ⟨1698371, by rfl⟩ : syracuseStep 2264495 = 3396743) B3396743
theorem B1510831 : Blo 1508951 1510831 := bstep (se 1 (by rfl) ⟨1133123, by rfl⟩ : syracuseStep 1510831 = 2266247) B2266247
theorem B1510855 : Blo 1508951 1510855 := bstep (se 1 (by rfl) ⟨1133141, by rfl⟩ : syracuseStep 1510855 = 2266283) B2266283
theorem B1510875 : Blo 1508951 1510875 := bstep (se 1 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 1510875 = 2266313) B2266313
theorem B2264585 : Blo 1508951 2264585 := bstep (se 2 (by rfl) ⟨849219, by rfl⟩ : syracuseStep 2264585 = 1698439) B1698439
theorem B2264615 : Blo 1508951 2264615 := bstep (se 1 (by rfl) ⟨1698461, by rfl⟩ : syracuseStep 2264615 = 3396923) B3396923
theorem B1510951 : Blo 1508951 1510951 := bstep (se 1 (by rfl) ⟨1133213, by rfl⟩ : syracuseStep 1510951 = 2266427) B2266427
theorem B11464253 : Blo 1508951 11464253 := bstep (se 3 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 11464253 = 4299095) B4299095
theorem B3395195 : Blo 1508951 3395195 := bstep (se 1 (by rfl) ⟨2546396, by rfl⟩ : syracuseStep 3395195 = 5092793) B5092793
theorem B2264699 : Blo 1508951 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B3821195 : Blo 1508951 3821195 := bstep (se 1 (by rfl) ⟨2865896, by rfl⟩ : syracuseStep 3821195 = 5731793) B5731793
theorem B9187015 : Blo 1508951 9187015 := bstep (se 1 (by rfl) ⟨6890261, by rfl⟩ : syracuseStep 9187015 = 13780523) B13780523
theorem B5099219 : Blo 1508951 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B7253725 : Blo 1508951 7253725 := bstep (se 3 (by rfl) ⟨1360073, by rfl⟩ : syracuseStep 7253725 = 2720147) B2720147
theorem B3395321 : Blo 1508951 3395321 := bstep (se 2 (by rfl) ⟨1273245, by rfl⟩ : syracuseStep 3395321 = 2546491) B2546491
theorem B3223289 : Blo 1508951 3223289 := bstep (se 2 (by rfl) ⟨1208733, by rfl⟩ : syracuseStep 3223289 = 2417467) B2417467
theorem B2264825 : Blo 1508951 2264825 := bstep (se 2 (by rfl) ⟨849309, by rfl⟩ : syracuseStep 2264825 = 1698619) B1698619
theorem B2264927 : Blo 1508951 2264927 := bstep (se 1 (by rfl) ⟨1698695, by rfl⟩ : syracuseStep 2264927 = 3397391) B3397391
theorem B4083551 : Blo 1508951 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B2264939 : Blo 1508951 2264939 := bstep (se 1 (by rfl) ⟨1698704, by rfl⟩ : syracuseStep 2264939 = 3397409) B3397409
theorem B2584507 : Blo 1508951 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B3395591 : Blo 1508951 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B30978125 : Blo 1508951 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B3395663 : Blo 1508951 3395663 := bstep (se 1 (by rfl) ⟨2546747, by rfl⟩ : syracuseStep 3395663 = 5093495) B5093495
theorem B3223631 : Blo 1508951 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B2265167 : Blo 1508951 2265167 := bstep (se 1 (by rfl) ⟨1698875, by rfl⟩ : syracuseStep 2265167 = 3397751) B3397751
theorem B10334297 : Blo 1508951 10334297 := bstep (se 2 (by rfl) ⟨3875361, by rfl⟩ : syracuseStep 10334297 = 7750723) B7750723
theorem B2265287 : Blo 1508951 2265287 := bstep (se 1 (by rfl) ⟨1698965, by rfl⟩ : syracuseStep 2265287 = 3397931) B3397931
theorem B9679115 : Blo 1508951 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B2265449 : Blo 1508951 2265449 := bstep (se 2 (by rfl) ⟨849543, by rfl⟩ : syracuseStep 2265449 = 1699087) B1699087
theorem B2265527 : Blo 1508951 2265527 := bstep (se 1 (by rfl) ⟨1699145, by rfl⟩ : syracuseStep 2265527 = 3398291) B3398291
theorem B3396059 : Blo 1508951 3396059 := bstep (se 1 (by rfl) ⟨2547044, by rfl⟩ : syracuseStep 3396059 = 5094089) B5094089
theorem B2265563 : Blo 1508951 2265563 := bstep (se 1 (by rfl) ⟨1699172, by rfl⟩ : syracuseStep 2265563 = 3398345) B3398345
theorem B11465225 : Blo 1508951 11465225 := bstep (se 2 (by rfl) ⟨4299459, by rfl⟩ : syracuseStep 11465225 = 8598919) B8598919
theorem B6451771 : Blo 1508951 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B3822329 : Blo 1508951 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B17429251 : Blo 1508951 17429251 := bstep (se 1 (by rfl) ⟨13071938, by rfl⟩ : syracuseStep 17429251 = 26143877) B26143877
theorem B3396527 : Blo 1508951 3396527 := bstep (se 1 (by rfl) ⟨2547395, by rfl⟩ : syracuseStep 3396527 = 5094791) B5094791
theorem B3822511 : Blo 1508951 3822511 := bstep (se 1 (by rfl) ⟨2866883, by rfl⟩ : syracuseStep 3822511 = 5733767) B5733767
theorem B2266031 : Blo 1508951 2266031 := bstep (se 1 (by rfl) ⟨1699523, by rfl⟩ : syracuseStep 2266031 = 3399047) B3399047
theorem B21763019 : Blo 1508951 21763019 := bstep (se 1 (by rfl) ⟨16322264, by rfl⟩ : syracuseStep 21763019 = 32644529) B32644529
theorem B20952029 : Blo 1508951 20952029 := bstep (se 3 (by rfl) ⟨3928505, by rfl⟩ : syracuseStep 20952029 = 7857011) B7857011
theorem B2266121 : Blo 1508951 2266121 := bstep (se 2 (by rfl) ⟨849795, by rfl⟩ : syracuseStep 2266121 = 1699591) B1699591
theorem B3060775 : Blo 1508951 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B2266151 : Blo 1508951 2266151 := bstep (se 1 (by rfl) ⟨1699613, by rfl⟩ : syracuseStep 2266151 = 3399227) B3399227
theorem B2266235 : Blo 1508951 2266235 := bstep (se 1 (by rfl) ⟨1699676, by rfl⟩ : syracuseStep 2266235 = 3399353) B3399353
theorem B5444765 : Blo 1508951 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B3396779 : Blo 1508951 3396779 := bstep (se 1 (by rfl) ⟨2547584, by rfl⟩ : syracuseStep 3396779 = 5095169) B5095169
theorem B2266361 : Blo 1508951 2266361 := bstep (se 2 (by rfl) ⟨849885, by rfl⟩ : syracuseStep 2266361 = 1699771) B1699771
theorem B3822977 : Blo 1508951 3822977 := bstep (se 2 (by rfl) ⟨1433616, by rfl⟩ : syracuseStep 3822977 = 2867233) B2867233
theorem B3626383 : Blo 1508951 3626383 := bstep (se 1 (by rfl) ⟨2719787, by rfl⟩ : syracuseStep 3626383 = 5439575) B5439575
theorem B25802225 : Blo 1508951 25802225 := bstep (se 2 (by rfl) ⟨9675834, by rfl⟩ : syracuseStep 25802225 = 19351669) B19351669
theorem B2864659 : Blo 1508951 2864659 := bstep (se 1 (by rfl) ⟨2148494, by rfl⟩ : syracuseStep 2864659 = 4296989) B4296989
theorem B4839097 : Blo 1508951 4839097 := bstep (se 2 (by rfl) ⟨1814661, by rfl⟩ : syracuseStep 4839097 = 3629323) B3629323
theorem B5093063 : Blo 1508951 5093063 := bstep (se 1 (by rfl) ⟨3819797, by rfl⟩ : syracuseStep 5093063 = 7639595) B7639595
theorem B3397319 : Blo 1508951 3397319 := bstep (se 1 (by rfl) ⟨2547989, by rfl⟩ : syracuseStep 3397319 = 5095979) B5095979
theorem B3823433 : Blo 1508951 3823433 := bstep (se 2 (by rfl) ⟨1433787, by rfl⟩ : syracuseStep 3823433 = 2867575) B2867575
theorem B5732279 : Blo 1508951 5732279 := bstep (se 1 (by rfl) ⟨4299209, by rfl⟩ : syracuseStep 5732279 = 8598419) B8598419
theorem B11466683 : Blo 1508951 11466683 := bstep (se 1 (by rfl) ⟨8600012, by rfl⟩ : syracuseStep 11466683 = 17200025) B17200025
theorem B3823787 : Blo 1508951 3823787 := bstep (se 1 (by rfl) ⟨2867840, by rfl⟩ : syracuseStep 3823787 = 5735681) B5735681
theorem B24492419 : Blo 1508951 24492419 := bstep (se 1 (by rfl) ⟨18369314, by rfl⟩ : syracuseStep 24492419 = 36738629) B36738629
theorem B6453769 : Blo 1508951 6453769 := bstep (se 2 (by rfl) ⟨2420163, by rfl⟩ : syracuseStep 6453769 = 4840327) B4840327
theorem B5093927 : Blo 1508951 5093927 := bstep (se 1 (by rfl) ⟨3820445, by rfl⟩ : syracuseStep 5093927 = 7640891) B7640891
theorem B3398183 : Blo 1508951 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B3226235 : Blo 1508951 3226235 := bstep (se 1 (by rfl) ⟨2419676, by rfl⟩ : syracuseStep 3226235 = 4839353) B4839353
theorem B5094035 : Blo 1508951 5094035 := bstep (se 1 (by rfl) ⟨3820526, by rfl⟩ : syracuseStep 5094035 = 7641053) B7641053
theorem B7256861 : Blo 1508951 7256861 := bstep (se 3 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 7256861 = 2721323) B2721323
theorem B8166217 : Blo 1508951 8166217 := bstep (se 2 (by rfl) ⟨3062331, by rfl⟩ : syracuseStep 8166217 = 6124663) B6124663
theorem B5094251 : Blo 1508951 5094251 := bstep (se 1 (by rfl) ⟨3820688, by rfl⟩ : syracuseStep 5094251 = 7641377) B7641377
theorem B3398507 : Blo 1508951 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B3226475 : Blo 1508951 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B52312949 : Blo 1508951 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B5094305 : Blo 1508951 5094305 := bstep (se 2 (by rfl) ⟨1910364, by rfl⟩ : syracuseStep 5094305 = 3820729) B3820729
theorem B5733281 : Blo 1508951 5733281 := bstep (se 2 (by rfl) ⟨2149980, by rfl⟩ : syracuseStep 5733281 = 4299961) B4299961
theorem B3398561 : Blo 1508951 3398561 := bstep (se 2 (by rfl) ⟨1274460, by rfl⟩ : syracuseStep 3398561 = 2548921) B2548921
theorem B6118319 : Blo 1508951 6118319 := bstep (se 1 (by rfl) ⟨4588739, by rfl⟩ : syracuseStep 6118319 = 9177479) B9177479
theorem B11623351 : Blo 1508951 11623351 := bstep (se 1 (by rfl) ⟨8717513, by rfl⟩ : syracuseStep 11623351 = 17435027) B17435027
theorem B3824567 : Blo 1508951 3824567 := bstep (se 1 (by rfl) ⟨2868425, by rfl⟩ : syracuseStep 3824567 = 5736851) B5736851
theorem B6446081 : Blo 1508951 6446081 := bstep (se 2 (by rfl) ⟨2417280, by rfl⟩ : syracuseStep 6446081 = 4834561) B4834561
theorem B2907215 : Blo 1508951 2907215 := bstep (se 1 (by rfl) ⟨2180411, by rfl⟩ : syracuseStep 2907215 = 4360823) B4360823
theorem B5438621 : Blo 1508951 5438621 := bstep (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) B2039483
theorem B3398903 : Blo 1508951 3398903 := bstep (se 1 (by rfl) ⟨2549177, by rfl⟩ : syracuseStep 3398903 = 5098355) B5098355
theorem B2833759 : Blo 1508951 2833759 := bstep (se 1 (by rfl) ⟨2125319, by rfl⟩ : syracuseStep 2833759 = 4250639) B4250639
theorem B5733737 : Blo 1508951 5733737 := bstep (se 2 (by rfl) ⟨2150151, by rfl⟩ : syracuseStep 5733737 = 4300303) B4300303
theorem B7642511 : Blo 1508951 7642511 := bstep (se 1 (by rfl) ⟨5731883, by rfl⟩ : syracuseStep 7642511 = 11463767) B11463767
theorem B2547119 : Blo 1508951 2547119 := bstep (se 1 (by rfl) ⟨1910339, by rfl⟩ : syracuseStep 2547119 = 3820679) B3820679
theorem B7749083 : Blo 1508951 7749083 := bstep (se 1 (by rfl) ⟨5811812, by rfl⟩ : syracuseStep 7749083 = 11623625) B11623625
theorem B5094899 : Blo 1508951 5094899 := bstep (se 1 (by rfl) ⟨3821174, by rfl⟩ : syracuseStep 5094899 = 7642349) B7642349
theorem B7257799 : Blo 1508951 7257799 := bstep (se 1 (by rfl) ⟨5443349, by rfl⟩ : syracuseStep 7257799 = 10886699) B10886699
theorem B37224197 : Blo 1508951 37224197 := bstep (se 4 (by rfl) ⟨3489768, by rfl⟩ : syracuseStep 37224197 = 6979537) B6979537
theorem B7356203 : Blo 1508951 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B3399497 : Blo 1508951 3399497 := bstep (se 2 (by rfl) ⟨1274811, by rfl⟩ : syracuseStep 3399497 = 2549623) B2549623
theorem B2547551 : Blo 1508951 2547551 := bstep (se 1 (by rfl) ⟨1910663, by rfl⟩ : syracuseStep 2547551 = 3821327) B3821327
theorem B2867051 : Blo 1508951 2867051 := bstep (se 1 (by rfl) ⟨2150288, by rfl⟩ : syracuseStep 2867051 = 4300577) B4300577
theorem B5734253 : Blo 1508951 5734253 := bstep (se 3 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 5734253 = 2150345) B2150345
theorem B30211955 : Blo 1508951 30211955 := bstep (se 1 (by rfl) ⟨22658966, by rfl⟩ : syracuseStep 30211955 = 45317933) B45317933
theorem B10887047 : Blo 1508951 10887047 := bstep (se 1 (by rfl) ⟨8165285, by rfl⟩ : syracuseStep 10887047 = 16330571) B16330571
theorem B20652083 : Blo 1508951 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B6889531 : Blo 1508951 6889531 := bstep (se 1 (by rfl) ⟨5167148, by rfl⟩ : syracuseStep 6889531 = 10334297) B10334297
theorem B7643483 : Blo 1508951 7643483 := bstep (se 1 (by rfl) ⟨5732612, by rfl⟩ : syracuseStep 7643483 = 11465225) B11465225
theorem B2548219 : Blo 1508951 2548219 := bstep (se 1 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 2548219 = 3822329) B3822329
theorem B14508679 : Blo 1508951 14508679 := bstep (se 1 (by rfl) ⟨10881509, by rfl⟩ : syracuseStep 14508679 = 21763019) B21763019
theorem B13968019 : Blo 1508951 13968019 := bstep (se 1 (by rfl) ⟨10476014, by rfl⟩ : syracuseStep 13968019 = 20952029) B20952029
theorem B5440223 : Blo 1508951 5440223 := bstep (se 1 (by rfl) ⟨4080167, by rfl⟩ : syracuseStep 5440223 = 8160335) B8160335
theorem B8602361 : Blo 1508951 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B3629843 : Blo 1508951 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B2548651 : Blo 1508951 2548651 := bstep (se 1 (by rfl) ⟨1911488, by rfl⟩ : syracuseStep 2548651 = 3822977) B3822977
theorem B11617219 : Blo 1508951 11617219 := bstep (se 1 (by rfl) ⟨8712914, by rfl⟩ : syracuseStep 11617219 = 17425829) B17425829
theorem B5096411 : Blo 1508951 5096411 := bstep (se 1 (by rfl) ⟨3822308, by rfl⟩ : syracuseStep 5096411 = 7644617) B7644617
theorem B10888289 : Blo 1508951 10888289 := bstep (se 2 (by rfl) ⟨4083108, by rfl⟩ : syracuseStep 10888289 = 8166217) B8166217
theorem B5096573 : Blo 1508951 5096573 := bstep (se 3 (by rfl) ⟨955607, by rfl⟩ : syracuseStep 5096573 = 1911215) B1911215
theorem B14517443 : Blo 1508951 14517443 := bstep (se 1 (by rfl) ⟨10888082, by rfl⟩ : syracuseStep 14517443 = 21776165) B21776165
theorem B2548955 : Blo 1508951 2548955 := bstep (se 1 (by rfl) ⟨1911716, by rfl⟩ : syracuseStep 2548955 = 3823433) B3823433
theorem B5096681 : Blo 1508951 5096681 := bstep (se 2 (by rfl) ⟨1911255, by rfl⟩ : syracuseStep 5096681 = 3822511) B3822511
theorem B10880243 : Blo 1508951 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B7644455 : Blo 1508951 7644455 := bstep (se 1 (by rfl) ⟨5733341, by rfl⟩ : syracuseStep 7644455 = 11466683) B11466683
theorem B4081033 : Blo 1508951 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B5096843 : Blo 1508951 5096843 := bstep (se 1 (by rfl) ⟨3822632, by rfl⟩ : syracuseStep 5096843 = 7645265) B7645265
theorem B2549191 : Blo 1508951 2549191 := bstep (se 1 (by rfl) ⟨1911893, by rfl⟩ : syracuseStep 2549191 = 3823787) B3823787
theorem B16328279 : Blo 1508951 16328279 := bstep (se 1 (by rfl) ⟨12246209, by rfl⟩ : syracuseStep 16328279 = 24492419) B24492419
theorem B8603293 : Blo 1508951 8603293 := bstep (se 3 (by rfl) ⟨1613117, by rfl⟩ : syracuseStep 8603293 = 3226235) B3226235
theorem B1509087 : Blo 1508951 1509087 := bstep (se 1 (by rfl) ⟨1131815, by rfl⟩ : syracuseStep 1509087 = 2263631) B2263631
theorem B2418473 : Blo 1508951 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B3778345 : Blo 1508951 3778345 := bstep (se 2 (by rfl) ⟨1416879, by rfl⟩ : syracuseStep 3778345 = 2833759) B2833759
theorem B1509167 : Blo 1508951 1509167 := bstep (se 1 (by rfl) ⟨1131875, by rfl⟩ : syracuseStep 1509167 = 2263751) B2263751
theorem B4835177 : Blo 1508951 4835177 := bstep (se 2 (by rfl) ⟨1813191, by rfl⟩ : syracuseStep 4835177 = 3626383) B3626383
theorem B1509275 : Blo 1508951 1509275 := bstep (se 1 (by rfl) ⟨1131956, by rfl⟩ : syracuseStep 1509275 = 2263913) B2263913
theorem B34875299 : Blo 1508951 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B1509327 : Blo 1508951 1509327 := bstep (se 1 (by rfl) ⟨1131995, by rfl⟩ : syracuseStep 1509327 = 2263991) B2263991
theorem B2549711 : Blo 1508951 2549711 := bstep (se 1 (by rfl) ⟨1912283, by rfl⟩ : syracuseStep 2549711 = 3824567) B3824567
theorem B1509351 : Blo 1508951 1509351 := bstep (se 1 (by rfl) ⟨1132013, by rfl⟩ : syracuseStep 1509351 = 2264027) B2264027
theorem B3819545 : Blo 1508951 3819545 := bstep (se 2 (by rfl) ⟨1432329, by rfl⟩ : syracuseStep 3819545 = 2864659) B2864659
theorem B9677065 : Blo 1508951 9677065 := bstep (se 2 (by rfl) ⟨3628899, by rfl⟩ : syracuseStep 9677065 = 7257799) B7257799
theorem B12249353 : Blo 1508951 12249353 := bstep (se 2 (by rfl) ⟨4593507, by rfl⟩ : syracuseStep 12249353 = 9187015) B9187015
theorem B16320797 : Blo 1508951 16320797 := bstep (se 3 (by rfl) ⟨3060149, by rfl⟩ : syracuseStep 16320797 = 6120299) B6120299
theorem B1698079 : Blo 1508951 1698079 := bstep (se 1 (by rfl) ⟨1273559, by rfl⟩ : syracuseStep 1698079 = 2547119) B2547119
theorem B1509663 : Blo 1508951 1509663 := bstep (se 1 (by rfl) ⟨1132247, by rfl⟩ : syracuseStep 1509663 = 2264495) B2264495
theorem B1509723 : Blo 1508951 1509723 := bstep (se 1 (by rfl) ⟨1132292, by rfl⟩ : syracuseStep 1509723 = 2264585) B2264585
theorem B1509743 : Blo 1508951 1509743 := bstep (se 1 (by rfl) ⟨1132307, by rfl⟩ : syracuseStep 1509743 = 2264615) B2264615
theorem B2263463 : Blo 1508951 2263463 := bstep (se 1 (by rfl) ⟨1697597, by rfl⟩ : syracuseStep 2263463 = 3395195) B3395195
theorem B1509799 : Blo 1508951 1509799 := bstep (se 1 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 1509799 = 2264699) B2264699
theorem B2263547 : Blo 1508951 2263547 := bstep (se 1 (by rfl) ⟨1697660, by rfl⟩ : syracuseStep 2263547 = 3395321) B3395321
theorem B2148859 : Blo 1508951 2148859 := bstep (se 1 (by rfl) ⟨1611644, by rfl⟩ : syracuseStep 2148859 = 3223289) B3223289
theorem B1509883 : Blo 1508951 1509883 := bstep (se 1 (by rfl) ⟨1132412, by rfl⟩ : syracuseStep 1509883 = 2264825) B2264825
theorem B24816131 : Blo 1508951 24816131 := bstep (se 1 (by rfl) ⟨18612098, by rfl⟩ : syracuseStep 24816131 = 37224197) B37224197
theorem B1698367 : Blo 1508951 1698367 := bstep (se 1 (by rfl) ⟨1273775, by rfl⟩ : syracuseStep 1698367 = 2547551) B2547551
theorem B1509951 : Blo 1508951 1509951 := bstep (se 1 (by rfl) ⟨1132463, by rfl⟩ : syracuseStep 1509951 = 2264927) B2264927
theorem B2722367 : Blo 1508951 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B1509959 : Blo 1508951 1509959 := bstep (se 1 (by rfl) ⟨1132469, by rfl⟩ : syracuseStep 1509959 = 2264939) B2264939
theorem B1911367 : Blo 1508951 1911367 := bstep (se 1 (by rfl) ⟨1433525, by rfl⟩ : syracuseStep 1911367 = 2867051) B2867051
theorem B2263673 : Blo 1508951 2263673 := bstep (se 2 (by rfl) ⟨848877, by rfl⟩ : syracuseStep 2263673 = 1697755) B1697755
theorem B2263727 : Blo 1508951 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B2263775 : Blo 1508951 2263775 := bstep (se 1 (by rfl) ⟨1697831, by rfl⟩ : syracuseStep 2263775 = 3395663) B3395663
theorem B2149087 : Blo 1508951 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B1510111 : Blo 1508951 1510111 := bstep (se 1 (by rfl) ⟨1132583, by rfl⟩ : syracuseStep 1510111 = 2265167) B2265167
theorem B1510191 : Blo 1508951 1510191 := bstep (se 1 (by rfl) ⟨1132643, by rfl⟩ : syracuseStep 1510191 = 2265287) B2265287
theorem B12905351 : Blo 1508951 12905351 := bstep (se 1 (by rfl) ⟨9679013, by rfl⟩ : syracuseStep 12905351 = 19358027) B19358027
theorem B1510299 : Blo 1508951 1510299 := bstep (se 1 (by rfl) ⟨1132724, by rfl⟩ : syracuseStep 1510299 = 2265449) B2265449
theorem B1510351 : Blo 1508951 1510351 := bstep (se 1 (by rfl) ⟨1132763, by rfl⟩ : syracuseStep 1510351 = 2265527) B2265527
theorem B2264039 : Blo 1508951 2264039 := bstep (se 1 (by rfl) ⟨1698029, by rfl⟩ : syracuseStep 2264039 = 3396059) B3396059
theorem B1510375 : Blo 1508951 1510375 := bstep (se 1 (by rfl) ⟨1132781, by rfl⟩ : syracuseStep 1510375 = 2265563) B2265563
theorem B2419703 : Blo 1508951 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B14502989 : Blo 1508951 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B2264297 : Blo 1508951 2264297 := bstep (se 2 (by rfl) ⟨849111, by rfl⟩ : syracuseStep 2264297 = 1698223) B1698223
theorem B2264351 : Blo 1508951 2264351 := bstep (se 1 (by rfl) ⟨1698263, by rfl⟩ : syracuseStep 2264351 = 3396527) B3396527
theorem B1510687 : Blo 1508951 1510687 := bstep (se 1 (by rfl) ⟨1133015, by rfl⟩ : syracuseStep 1510687 = 2266031) B2266031
theorem B1510747 : Blo 1508951 1510747 := bstep (se 1 (by rfl) ⟨1133060, by rfl⟩ : syracuseStep 1510747 = 2266121) B2266121
theorem B7646561 : Blo 1508951 7646561 := bstep (se 2 (by rfl) ⟨2867460, by rfl⟩ : syracuseStep 7646561 = 5734921) B5734921
theorem B8605025 : Blo 1508951 8605025 := bstep (se 2 (by rfl) ⟨3226884, by rfl⟩ : syracuseStep 8605025 = 6453769) B6453769
theorem B1510767 : Blo 1508951 1510767 := bstep (se 1 (by rfl) ⟨1133075, by rfl⟩ : syracuseStep 1510767 = 2266151) B2266151
theorem B1699195 : Blo 1508951 1699195 := bstep (se 1 (by rfl) ⟨1274396, by rfl⟩ : syracuseStep 1699195 = 2548793) B2548793
theorem B1912187 : Blo 1508951 1912187 := bstep (se 1 (by rfl) ⟨1434140, by rfl⟩ : syracuseStep 1912187 = 2868281) B2868281
theorem B1510823 : Blo 1508951 1510823 := bstep (se 1 (by rfl) ⟨1133117, by rfl⟩ : syracuseStep 1510823 = 2266235) B2266235
theorem B2264519 : Blo 1508951 2264519 := bstep (se 1 (by rfl) ⟨1698389, by rfl⟩ : syracuseStep 2264519 = 3396779) B3396779
theorem B1510907 : Blo 1508951 1510907 := bstep (se 1 (by rfl) ⟨1133180, by rfl⟩ : syracuseStep 1510907 = 2266361) B2266361
theorem B7253801 : Blo 1508951 7253801 := bstep (se 2 (by rfl) ⟨2720175, by rfl⟩ : syracuseStep 7253801 = 5440351) B5440351
theorem B2264873 : Blo 1508951 2264873 := bstep (se 2 (by rfl) ⟨849327, by rfl⟩ : syracuseStep 2264873 = 1698655) B1698655
theorem B3395375 : Blo 1508951 3395375 := bstep (se 1 (by rfl) ⟨2546531, by rfl⟩ : syracuseStep 3395375 = 5093063) B5093063
theorem B2264879 : Blo 1508951 2264879 := bstep (se 1 (by rfl) ⟨1698659, by rfl⟩ : syracuseStep 2264879 = 3397319) B3397319
theorem B4591417 : Blo 1508951 4591417 := bstep (se 2 (by rfl) ⟨1721781, by rfl⟩ : syracuseStep 4591417 = 3443563) B3443563
theorem B1699663 : Blo 1508951 1699663 := bstep (se 1 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 1699663 = 2549495) B2549495
theorem B3821519 : Blo 1508951 3821519 := bstep (se 1 (by rfl) ⟨2866139, by rfl⟩ : syracuseStep 3821519 = 5732279) B5732279
theorem B11473001 : Blo 1508951 11473001 := bstep (se 2 (by rfl) ⟨4302375, by rfl⟩ : syracuseStep 11473001 = 8604751) B8604751
theorem B2265353 : Blo 1508951 2265353 := bstep (se 2 (by rfl) ⟨849507, by rfl⟩ : syracuseStep 2265353 = 1699015) B1699015
theorem B3395951 : Blo 1508951 3395951 := bstep (se 1 (by rfl) ⟨2546963, by rfl⟩ : syracuseStep 3395951 = 5093927) B5093927
theorem B2265455 : Blo 1508951 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B3396023 : Blo 1508951 3396023 := bstep (se 1 (by rfl) ⟨2547017, by rfl⟩ : syracuseStep 3396023 = 5094035) B5094035
theorem B3224083 : Blo 1508951 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B4837907 : Blo 1508951 4837907 := bstep (se 1 (by rfl) ⟨3628430, by rfl⟩ : syracuseStep 4837907 = 7256861) B7256861
theorem B3396167 : Blo 1508951 3396167 := bstep (se 1 (by rfl) ⟨2547125, by rfl⟩ : syracuseStep 3396167 = 5094251) B5094251
theorem B2265671 : Blo 1508951 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B2150983 : Blo 1508951 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B3396203 : Blo 1508951 3396203 := bstep (se 1 (by rfl) ⟨2547152, by rfl⟩ : syracuseStep 3396203 = 5094305) B5094305
theorem B3822187 : Blo 1508951 3822187 := bstep (se 1 (by rfl) ⟨2866640, by rfl⟩ : syracuseStep 3822187 = 5733281) B5733281
theorem B2265707 : Blo 1508951 2265707 := bstep (se 1 (by rfl) ⟨1699280, by rfl⟩ : syracuseStep 2265707 = 3398561) B3398561
theorem B4297387 : Blo 1508951 4297387 := bstep (se 1 (by rfl) ⟨3223040, by rfl⟩ : syracuseStep 4297387 = 6446081) B6446081
theorem B1938143 : Blo 1508951 1938143 := bstep (se 1 (by rfl) ⟨1453607, by rfl⟩ : syracuseStep 1938143 = 2907215) B2907215
theorem B2265935 : Blo 1508951 2265935 := bstep (se 1 (by rfl) ⟨1699451, by rfl⟩ : syracuseStep 2265935 = 3398903) B3398903
theorem B3822491 : Blo 1508951 3822491 := bstep (se 1 (by rfl) ⟨2866868, by rfl⟩ : syracuseStep 3822491 = 5733737) B5733737
theorem B6452129 : Blo 1508951 6452129 := bstep (se 2 (by rfl) ⟨2419548, by rfl⟩ : syracuseStep 6452129 = 4839097) B4839097
theorem B9671633 : Blo 1508951 9671633 := bstep (se 2 (by rfl) ⟨3626862, by rfl⟩ : syracuseStep 9671633 = 7253725) B7253725
theorem B5166055 : Blo 1508951 5166055 := bstep (se 1 (by rfl) ⟨3874541, by rfl⟩ : syracuseStep 5166055 = 7749083) B7749083
theorem B3396599 : Blo 1508951 3396599 := bstep (se 1 (by rfl) ⟨2547449, by rfl⟩ : syracuseStep 3396599 = 5094899) B5094899
theorem B4904135 : Blo 1508951 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B2266331 : Blo 1508951 2266331 := bstep (se 1 (by rfl) ⟨1699748, by rfl⟩ : syracuseStep 2266331 = 3399497) B3399497
theorem B3822835 : Blo 1508951 3822835 := bstep (se 1 (by rfl) ⟨2867126, by rfl⟩ : syracuseStep 3822835 = 5734253) B5734253
theorem B20141303 : Blo 1508951 20141303 := bstep (se 1 (by rfl) ⟨15105977, by rfl⟩ : syracuseStep 20141303 = 30211955) B30211955
theorem B7648505 : Blo 1508951 7648505 := bstep (se 2 (by rfl) ⟨2868189, by rfl⟩ : syracuseStep 7648505 = 5736379) B5736379
theorem B3446009 : Blo 1508951 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B3396959 : Blo 1508951 3396959 := bstep (se 1 (by rfl) ⟨2547719, by rfl⟩ : syracuseStep 3396959 = 5095439) B5095439
theorem B3224929 : Blo 1508951 3224929 := bstep (se 2 (by rfl) ⟨1209348, by rfl⟩ : syracuseStep 3224929 = 2418697) B2418697
theorem B3626363 : Blo 1508951 3626363 := bstep (se 1 (by rfl) ⟨2719772, by rfl⟩ : syracuseStep 3626363 = 5439545) B5439545
theorem B9811361 : Blo 1508951 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B3397355 : Blo 1508951 3397355 := bstep (se 1 (by rfl) ⟨2548016, by rfl⟩ : syracuseStep 3397355 = 5096033) B5096033
theorem B5093225 : Blo 1508951 5093225 := bstep (se 2 (by rfl) ⟨1909959, by rfl⟩ : syracuseStep 5093225 = 3819919) B3819919
theorem B3397481 : Blo 1508951 3397481 := bstep (se 2 (by rfl) ⟨1274055, by rfl⟩ : syracuseStep 3397481 = 2548111) B2548111
theorem B3823625 : Blo 1508951 3823625 := bstep (se 2 (by rfl) ⟨1433859, by rfl⟩ : syracuseStep 3823625 = 2867719) B2867719
theorem B25810973 : Blo 1508951 25810973 := bstep (se 3 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 25810973 = 9679115) B9679115
theorem B15702295 : Blo 1508951 15702295 := bstep (se 1 (by rfl) ⟨11776721, by rfl⟩ : syracuseStep 15702295 = 23553443) B23553443
theorem B5093657 : Blo 1508951 5093657 := bstep (se 2 (by rfl) ⟨1910121, by rfl⟩ : syracuseStep 5093657 = 3820243) B3820243
theorem B17201483 : Blo 1508951 17201483 := bstep (se 1 (by rfl) ⟨12901112, by rfl⟩ : syracuseStep 17201483 = 25802225) B25802225
theorem B23239001 : Blo 1508951 23239001 := bstep (se 2 (by rfl) ⟨8714625, by rfl⟩ : syracuseStep 23239001 = 17429251) B17429251
theorem B4299119 : Blo 1508951 4299119 := bstep (se 1 (by rfl) ⟨3224339, by rfl⟩ : syracuseStep 4299119 = 6448679) B6448679
theorem B3267067 : Blo 1508951 3267067 := bstep (se 1 (by rfl) ⟨2450300, by rfl⟩ : syracuseStep 3267067 = 4900601) B4900601
theorem B3627593 : Blo 1508951 3627593 := bstep (se 2 (by rfl) ⟨1360347, by rfl⟩ : syracuseStep 3627593 = 2720695) B2720695
theorem B15497801 : Blo 1508951 15497801 := bstep (se 2 (by rfl) ⟨5811675, by rfl⟩ : syracuseStep 15497801 = 11623351) B11623351
theorem B19339883 : Blo 1508951 19339883 := bstep (se 1 (by rfl) ⟨14504912, by rfl⟩ : syracuseStep 19339883 = 29009825) B29009825
theorem B3398327 : Blo 1508951 3398327 := bstep (se 1 (by rfl) ⟨2548745, by rfl⟩ : syracuseStep 3398327 = 5097491) B5097491
theorem B6445757 : Blo 1508951 6445757 := bstep (se 3 (by rfl) ⟨1208579, by rfl⟩ : syracuseStep 6445757 = 2417159) B2417159
theorem B3627767 : Blo 1508951 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B17210231 : Blo 1508951 17210231 := bstep (se 1 (by rfl) ⟨12907673, by rfl⟩ : syracuseStep 17210231 = 25815347) B25815347
theorem B3398543 : Blo 1508951 3398543 := bstep (se 1 (by rfl) ⟨2548907, by rfl⟩ : syracuseStep 3398543 = 5097815) B5097815
theorem B5168015 : Blo 1508951 5168015 := bstep (se 1 (by rfl) ⟨3876011, by rfl⟩ : syracuseStep 5168015 = 7752023) B7752023
theorem B6445979 : Blo 1508951 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B4078879 : Blo 1508951 4078879 := bstep (se 1 (by rfl) ⟨3059159, by rfl⟩ : syracuseStep 4078879 = 6118319) B6118319
theorem B2547193 : Blo 1508951 2547193 := bstep (se 2 (by rfl) ⟨955197, by rfl⟩ : syracuseStep 2547193 = 1910395) B1910395
theorem B9182735 : Blo 1508951 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B5095007 : Blo 1508951 5095007 := bstep (se 1 (by rfl) ⟨3821255, by rfl⟩ : syracuseStep 5095007 = 7642511) B7642511
theorem B3399263 : Blo 1508951 3399263 := bstep (se 1 (by rfl) ⟨2549447, by rfl⟩ : syracuseStep 3399263 = 5098895) B5098895
theorem B12902003 : Blo 1508951 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B7642835 : Blo 1508951 7642835 := bstep (se 1 (by rfl) ⟨5732126, by rfl⟩ : syracuseStep 7642835 = 11464253) B11464253
theorem B2547463 : Blo 1508951 2547463 := bstep (se 1 (by rfl) ⟨1910597, by rfl⟩ : syracuseStep 2547463 = 3821195) B3821195
theorem B50290465 : Blo 1508951 50290465 := bstep (se 2 (by rfl) ⟨18858924, by rfl⟩ : syracuseStep 50290465 = 37717849) B37717849
theorem B2547497 : Blo 1508951 2547497 := bstep (se 2 (by rfl) ⟨955311, by rfl⟩ : syracuseStep 2547497 = 1910623) B1910623
theorem B3399479 : Blo 1508951 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B7258031 : Blo 1508951 7258031 := bstep (se 1 (by rfl) ⟨5443523, by rfl⟩ : syracuseStep 7258031 = 10887047) B10887047
theorem B5095655 : Blo 1508951 5095655 := bstep (se 1 (by rfl) ⟨3821741, by rfl⟩ : syracuseStep 5095655 = 7643483) B7643483
theorem B12902753 : Blo 1508951 12902753 := bstep (se 2 (by rfl) ⟨4838532, by rfl⟩ : syracuseStep 12902753 = 9677065) B9677065
theorem B5734907 : Blo 1508951 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B2548327 : Blo 1508951 2548327 := bstep (se 1 (by rfl) ⟨1911245, by rfl⟩ : syracuseStep 2548327 = 3822491) B3822491
theorem B4301419 : Blo 1508951 4301419 := bstep (se 1 (by rfl) ⟨3226064, by rfl⟩ : syracuseStep 4301419 = 6452129) B6452129
theorem B6447755 : Blo 1508951 6447755 := bstep (se 1 (by rfl) ⟨4835816, by rfl⟩ : syracuseStep 6447755 = 9671633) B9671633
theorem B7258859 : Blo 1508951 7258859 := bstep (se 1 (by rfl) ⟨5444144, by rfl⟩ : syracuseStep 7258859 = 10888289) B10888289
theorem B2548489 : Blo 1508951 2548489 := bstep (se 2 (by rfl) ⟨955683, by rfl⟩ : syracuseStep 2548489 = 1911367) B1911367
theorem B2867977 : Blo 1508951 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B3269423 : Blo 1508951 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B5096249 : Blo 1508951 5096249 := bstep (se 2 (by rfl) ⟨1911093, by rfl⟩ : syracuseStep 5096249 = 3822187) B3822187
theorem B5096303 : Blo 1508951 5096303 := bstep (se 1 (by rfl) ⟨3822227, by rfl⟩ : syracuseStep 5096303 = 7644455) B7644455
theorem B2417575 : Blo 1508951 2417575 := bstep (se 1 (by rfl) ⟨1813181, by rfl⟩ : syracuseStep 2417575 = 3626363) B3626363
theorem B23250199 : Blo 1508951 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B2549083 : Blo 1508951 2549083 := bstep (se 1 (by rfl) ⟨1911812, by rfl⟩ : syracuseStep 2549083 = 3823625) B3823625
theorem B7259645 : Blo 1508951 7259645 := bstep (se 3 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 7259645 = 2722367) B2722367
theorem B10880531 : Blo 1508951 10880531 := bstep (se 1 (by rfl) ⟨8160398, by rfl⟩ : syracuseStep 10880531 = 16320797) B16320797
theorem B15492667 : Blo 1508951 15492667 := bstep (se 1 (by rfl) ⟨11619500, by rfl⟩ : syracuseStep 15492667 = 23239001) B23239001
theorem B1508975 : Blo 1508951 1508975 := bstep (se 1 (by rfl) ⟨1131731, by rfl⟩ : syracuseStep 1508975 = 2263463) B2263463
theorem B5097113 : Blo 1508951 5097113 := bstep (se 2 (by rfl) ⟨1911417, by rfl⟩ : syracuseStep 5097113 = 3822835) B3822835
theorem B1509031 : Blo 1508951 1509031 := bstep (se 1 (by rfl) ⟨1131773, by rfl⟩ : syracuseStep 1509031 = 2263547) B2263547
theorem B2418395 : Blo 1508951 2418395 := bstep (se 1 (by rfl) ⟨1813796, by rfl⟩ : syracuseStep 2418395 = 3627593) B3627593
theorem B10331867 : Blo 1508951 10331867 := bstep (se 1 (by rfl) ⟨7748900, by rfl⟩ : syracuseStep 10331867 = 15497801) B15497801
theorem B1509115 : Blo 1508951 1509115 := bstep (se 1 (by rfl) ⟨1131836, by rfl⟩ : syracuseStep 1509115 = 2263673) B2263673
theorem B1509151 : Blo 1508951 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B1509183 : Blo 1508951 1509183 := bstep (se 1 (by rfl) ⟨1131887, by rfl⟩ : syracuseStep 1509183 = 2263775) B2263775
theorem B2418511 : Blo 1508951 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B5441377 : Blo 1508951 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B8603567 : Blo 1508951 8603567 := bstep (se 1 (by rfl) ⟨6452675, by rfl⟩ : syracuseStep 8603567 = 12905351) B12905351
theorem B1509359 : Blo 1508951 1509359 := bstep (se 1 (by rfl) ⟨1132019, by rfl⟩ : syracuseStep 1509359 = 2264039) B2264039
theorem B9668659 : Blo 1508951 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B1509531 : Blo 1508951 1509531 := bstep (se 1 (by rfl) ⟨1132148, by rfl⟩ : syracuseStep 1509531 = 2264297) B2264297
theorem B1509567 : Blo 1508951 1509567 := bstep (se 1 (by rfl) ⟨1132175, by rfl⟩ : syracuseStep 1509567 = 2264351) B2264351
theorem B11471057 : Blo 1508951 11471057 := bstep (se 2 (by rfl) ⟨4301646, by rfl⟩ : syracuseStep 11471057 = 8603293) B8603293
theorem B5097707 : Blo 1508951 5097707 := bstep (se 1 (by rfl) ⟨3823280, by rfl⟩ : syracuseStep 5097707 = 7646561) B7646561
theorem B5736683 : Blo 1508951 5736683 := bstep (se 1 (by rfl) ⟨4302512, by rfl⟩ : syracuseStep 5736683 = 8605025) B8605025
theorem B1509679 : Blo 1508951 1509679 := bstep (se 1 (by rfl) ⟨1132259, by rfl⟩ : syracuseStep 1509679 = 2264519) B2264519
theorem B6121823 : Blo 1508951 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B67053953 : Blo 1508951 67053953 := bstep (se 2 (by rfl) ⟨25145232, by rfl⟩ : syracuseStep 67053953 = 50290465) B50290465
theorem B6121889 : Blo 1508951 6121889 := bstep (se 2 (by rfl) ⟨2295708, by rfl⟩ : syracuseStep 6121889 = 4591417) B4591417
theorem B4835867 : Blo 1508951 4835867 := bstep (se 1 (by rfl) ⟨3626900, by rfl⟩ : syracuseStep 4835867 = 7253801) B7253801
theorem B1698331 : Blo 1508951 1698331 := bstep (se 1 (by rfl) ⟨1273748, by rfl⟩ : syracuseStep 1698331 = 2547497) B2547497
theorem B2263583 : Blo 1508951 2263583 := bstep (se 1 (by rfl) ⟨1697687, by rfl⟩ : syracuseStep 2263583 = 3395375) B3395375
theorem B1509915 : Blo 1508951 1509915 := bstep (se 1 (by rfl) ⟨1132436, by rfl⟩ : syracuseStep 1509915 = 2264873) B2264873
theorem B1509919 : Blo 1508951 1509919 := bstep (se 1 (by rfl) ⟨1132439, by rfl⟩ : syracuseStep 1509919 = 2264879) B2264879
theorem B9186041 : Blo 1508951 9186041 := bstep (se 2 (by rfl) ⟨3444765, by rfl⟩ : syracuseStep 9186041 = 6889531) B6889531
theorem B1510235 : Blo 1508951 1510235 := bstep (se 1 (by rfl) ⟨1132676, by rfl⟩ : syracuseStep 1510235 = 2265353) B2265353
theorem B2263967 : Blo 1508951 2263967 := bstep (se 1 (by rfl) ⟨1697975, by rfl⟩ : syracuseStep 2263967 = 3395951) B3395951
theorem B1510303 : Blo 1508951 1510303 := bstep (se 1 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 1510303 = 2265455) B2265455
theorem B2264015 : Blo 1508951 2264015 := bstep (se 1 (by rfl) ⟨1698011, by rfl⟩ : syracuseStep 2264015 = 3396023) B3396023
theorem B2264105 : Blo 1508951 2264105 := bstep (se 2 (by rfl) ⟨849039, by rfl⟩ : syracuseStep 2264105 = 1698079) B1698079
theorem B2264111 : Blo 1508951 2264111 := bstep (se 1 (by rfl) ⟨1698083, by rfl⟩ : syracuseStep 2264111 = 3396167) B3396167
theorem B1510447 : Blo 1508951 1510447 := bstep (se 1 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 1510447 = 2265671) B2265671
theorem B2264135 : Blo 1508951 2264135 := bstep (se 1 (by rfl) ⟨1698101, by rfl⟩ : syracuseStep 2264135 = 3396203) B3396203
theorem B1510471 : Blo 1508951 1510471 := bstep (se 1 (by rfl) ⟨1132853, by rfl⟩ : syracuseStep 1510471 = 2265707) B2265707
theorem B2419895 : Blo 1508951 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B1510623 : Blo 1508951 1510623 := bstep (se 1 (by rfl) ⟨1132967, by rfl⟩ : syracuseStep 1510623 = 2265935) B2265935
theorem B53710141 : Blo 1508951 53710141 := bstep (se 3 (by rfl) ⟨10070651, by rfl⟩ : syracuseStep 53710141 = 20141303) B20141303
theorem B2264399 : Blo 1508951 2264399 := bstep (se 1 (by rfl) ⟨1698299, by rfl⟩ : syracuseStep 2264399 = 3396599) B3396599
theorem B32664941 : Blo 1508951 32664941 := bstep (se 3 (by rfl) ⟨6124676, by rfl⟩ : syracuseStep 32664941 = 12249353) B12249353
theorem B2264489 : Blo 1508951 2264489 := bstep (se 2 (by rfl) ⟨849183, by rfl⟩ : syracuseStep 2264489 = 1698367) B1698367
theorem B9678295 : Blo 1508951 9678295 := bstep (se 1 (by rfl) ⟨7258721, by rfl⟩ : syracuseStep 9678295 = 14517443) B14517443
theorem B1699303 : Blo 1508951 1699303 := bstep (se 1 (by rfl) ⟨1274477, by rfl⟩ : syracuseStep 1699303 = 2548955) B2548955
theorem B1510887 : Blo 1508951 1510887 := bstep (se 1 (by rfl) ⟨1133165, by rfl⟩ : syracuseStep 1510887 = 2266331) B2266331
theorem B7253495 : Blo 1508951 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B5099003 : Blo 1508951 5099003 := bstep (se 1 (by rfl) ⟨3824252, by rfl⟩ : syracuseStep 5099003 = 7648505) B7648505
theorem B2297339 : Blo 1508951 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B19344905 : Blo 1508951 19344905 := bstep (se 2 (by rfl) ⟨7254339, by rfl⟩ : syracuseStep 19344905 = 14508679) B14508679
theorem B18624025 : Blo 1508951 18624025 := bstep (se 2 (by rfl) ⟨6984009, by rfl⟩ : syracuseStep 18624025 = 13968019) B13968019
theorem B5729849 : Blo 1508951 5729849 := bstep (se 2 (by rfl) ⟨2148693, by rfl⟩ : syracuseStep 5729849 = 4297387) B4297387
theorem B2264639 : Blo 1508951 2264639 := bstep (se 1 (by rfl) ⟨1698479, by rfl⟩ : syracuseStep 2264639 = 3396959) B3396959
theorem B6540907 : Blo 1508951 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B5099165 : Blo 1508951 5099165 := bstep (se 3 (by rfl) ⟨956093, by rfl⟩ : syracuseStep 5099165 = 1912187) B1912187
theorem B2264903 : Blo 1508951 2264903 := bstep (se 1 (by rfl) ⟨1698677, by rfl⟩ : syracuseStep 2264903 = 3397355) B3397355
theorem B3395483 : Blo 1508951 3395483 := bstep (se 1 (by rfl) ⟨2546612, by rfl⟩ : syracuseStep 3395483 = 5093225) B5093225
theorem B3223451 : Blo 1508951 3223451 := bstep (se 1 (by rfl) ⟨2417588, by rfl⟩ : syracuseStep 3223451 = 4835177) B4835177
theorem B2264987 : Blo 1508951 2264987 := bstep (se 1 (by rfl) ⟨1698740, by rfl⟩ : syracuseStep 2264987 = 3397481) B3397481
theorem B1699807 : Blo 1508951 1699807 := bstep (se 1 (by rfl) ⟨1274855, by rfl⟩ : syracuseStep 1699807 = 2549711) B2549711
theorem B17207315 : Blo 1508951 17207315 := bstep (se 1 (by rfl) ⟨12905486, by rfl⟩ : syracuseStep 17207315 = 25810973) B25810973
theorem B21754021 : Blo 1508951 21754021 := bstep (se 4 (by rfl) ⟨2039439, by rfl⟩ : syracuseStep 21754021 = 4078879) B4078879
theorem B3395771 : Blo 1508951 3395771 := bstep (se 1 (by rfl) ⟨2546828, by rfl⟩ : syracuseStep 3395771 = 5093657) B5093657
theorem B16544087 : Blo 1508951 16544087 := bstep (se 1 (by rfl) ⟨12408065, by rfl⟩ : syracuseStep 16544087 = 24816131) B24816131
theorem B2265551 : Blo 1508951 2265551 := bstep (se 1 (by rfl) ⟨1699163, by rfl⟩ : syracuseStep 2265551 = 3398327) B3398327
theorem B4297171 : Blo 1508951 4297171 := bstep (se 1 (by rfl) ⟨3222878, by rfl⟩ : syracuseStep 4297171 = 6445757) B6445757
theorem B2265593 : Blo 1508951 2265593 := bstep (se 2 (by rfl) ⟨849597, by rfl⟩ : syracuseStep 2265593 = 1699195) B1699195
theorem B11473487 : Blo 1508951 11473487 := bstep (se 1 (by rfl) ⟨8605115, by rfl⟩ : syracuseStep 11473487 = 17210231) B17210231
theorem B2265695 : Blo 1508951 2265695 := bstep (se 1 (by rfl) ⟨1699271, by rfl⟩ : syracuseStep 2265695 = 3398543) B3398543
theorem B3445343 : Blo 1508951 3445343 := bstep (se 1 (by rfl) ⟨2584007, by rfl⟩ : syracuseStep 3445343 = 5168015) B5168015
theorem B4297319 : Blo 1508951 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B3396257 : Blo 1508951 3396257 := bstep (se 2 (by rfl) ⟨1273596, by rfl⟩ : syracuseStep 3396257 = 2547193) B2547193
theorem B3396617 : Blo 1508951 3396617 := bstep (se 2 (by rfl) ⟨1273731, by rfl⟩ : syracuseStep 3396617 = 2547463) B2547463
theorem B3396671 : Blo 1508951 3396671 := bstep (se 1 (by rfl) ⟨2547503, by rfl⟩ : syracuseStep 3396671 = 5095007) B5095007
theorem B2266175 : Blo 1508951 2266175 := bstep (se 1 (by rfl) ⟨1699631, by rfl⟩ : syracuseStep 2266175 = 3399263) B3399263
theorem B2266217 : Blo 1508951 2266217 := bstep (se 2 (by rfl) ⟨849831, by rfl⟩ : syracuseStep 2266217 = 1699663) B1699663
theorem B2266319 : Blo 1508951 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B4838687 : Blo 1508951 4838687 := bstep (se 1 (by rfl) ⟨3629015, by rfl⟩ : syracuseStep 4838687 = 7258031) B7258031
theorem B13768055 : Blo 1508951 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B7648667 : Blo 1508951 7648667 := bstep (se 1 (by rfl) ⟨5736500, by rfl⟩ : syracuseStep 7648667 = 11473001) B11473001
theorem B3225271 : Blo 1508951 3225271 := bstep (se 1 (by rfl) ⟨2418953, by rfl⟩ : syracuseStep 3225271 = 4837907) B4837907
theorem B20936393 : Blo 1508951 20936393 := bstep (se 2 (by rfl) ⟨7851147, by rfl⟩ : syracuseStep 20936393 = 15702295) B15702295
theorem B3397607 : Blo 1508951 3397607 := bstep (se 1 (by rfl) ⟨2548205, by rfl⟩ : syracuseStep 3397607 = 5096411) B5096411
theorem B2865145 : Blo 1508951 2865145 := bstep (se 2 (by rfl) ⟨1074429, by rfl⟩ : syracuseStep 2865145 = 2148859) B2148859
theorem B4356089 : Blo 1508951 4356089 := bstep (se 2 (by rfl) ⟨1633533, by rfl⟩ : syracuseStep 4356089 = 3267067) B3267067
theorem B3397625 : Blo 1508951 3397625 := bstep (se 2 (by rfl) ⟨1274109, by rfl⟩ : syracuseStep 3397625 = 2548219) B2548219
theorem B4298777 : Blo 1508951 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B3397715 : Blo 1508951 3397715 := bstep (se 1 (by rfl) ⟨2548286, by rfl⟩ : syracuseStep 3397715 = 5096573) B5096573
theorem B3397787 : Blo 1508951 3397787 := bstep (se 1 (by rfl) ⟨2548340, by rfl⟩ : syracuseStep 3397787 = 5096681) B5096681
theorem B3397895 : Blo 1508951 3397895 := bstep (se 1 (by rfl) ⟨2548421, by rfl⟩ : syracuseStep 3397895 = 5096843) B5096843
theorem B2865449 : Blo 1508951 2865449 := bstep (se 2 (by rfl) ⟨1074543, by rfl⟩ : syracuseStep 2865449 = 2149087) B2149087
theorem B10885519 : Blo 1508951 10885519 := bstep (se 1 (by rfl) ⟨8164139, by rfl⟩ : syracuseStep 10885519 = 16328279) B16328279
theorem B1612315 : Blo 1508951 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B3398201 : Blo 1508951 3398201 := bstep (se 2 (by rfl) ⟨1274325, by rfl⟩ : syracuseStep 3398201 = 2548651) B2548651
theorem B15489625 : Blo 1508951 15489625 := bstep (se 2 (by rfl) ⟨5808609, by rfl⟩ : syracuseStep 15489625 = 11617219) B11617219
theorem B6888073 : Blo 1508951 6888073 := bstep (se 2 (by rfl) ⟨2583027, by rfl⟩ : syracuseStep 6888073 = 5166055) B5166055
theorem B2546363 : Blo 1508951 2546363 := bstep (se 1 (by rfl) ⟨1909772, by rfl⟩ : syracuseStep 2546363 = 3819545) B3819545
theorem B20151173 : Blo 1508951 20151173 := bstep (se 4 (by rfl) ⟨1889172, by rfl⟩ : syracuseStep 20151173 = 3778345) B3778345
theorem B11467655 : Blo 1508951 11467655 := bstep (se 1 (by rfl) ⟨8600741, by rfl⟩ : syracuseStep 11467655 = 17201483) B17201483
theorem B2866079 : Blo 1508951 2866079 := bstep (se 1 (by rfl) ⟨2149559, by rfl⟩ : syracuseStep 2866079 = 4299119) B4299119
theorem B12893255 : Blo 1508951 12893255 := bstep (se 1 (by rfl) ⟨9669941, by rfl⟩ : syracuseStep 12893255 = 19339883) B19339883
theorem B4299905 : Blo 1508951 4299905 := bstep (se 2 (by rfl) ⟨1612464, by rfl⟩ : syracuseStep 4299905 = 3224929) B3224929
theorem B14507261 : Blo 1508951 14507261 := bstep (se 3 (by rfl) ⟨2720111, by rfl⟩ : syracuseStep 14507261 = 5440223) B5440223
theorem B5168381 : Blo 1508951 5168381 := bstep (se 3 (by rfl) ⟨969071, by rfl⟩ : syracuseStep 5168381 = 1938143) B1938143
theorem B3398921 : Blo 1508951 3398921 := bstep (se 2 (by rfl) ⟨1274595, by rfl⟩ : syracuseStep 3398921 = 2549191) B2549191
theorem B1613135 : Blo 1508951 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B8601335 : Blo 1508951 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B5095223 : Blo 1508951 5095223 := bstep (se 1 (by rfl) ⟨3821417, by rfl⟩ : syracuseStep 5095223 = 7642835) B7642835
theorem B2547679 : Blo 1508951 2547679 := bstep (se 1 (by rfl) ⟨1910759, by rfl⟩ : syracuseStep 2547679 = 3821519) B3821519
theorem B99328133 : Blo 1508951 99328133 := bstep (se 4 (by rfl) ⟨9312012, by rfl⟩ : syracuseStep 99328133 = 18624025) B18624025
theorem B8601835 : Blo 1508951 8601835 := bstep (se 1 (by rfl) ⟨6451376, by rfl⟩ : syracuseStep 8601835 = 12902753) B12902753
theorem B20652833 : Blo 1508951 20652833 := bstep (se 2 (by rfl) ⟨7744812, by rfl⟩ : syracuseStep 20652833 = 15489625) B15489625
theorem B5735225 : Blo 1508951 5735225 := bstep (se 2 (by rfl) ⟨2150709, by rfl⟩ : syracuseStep 5735225 = 4301419) B4301419
theorem B9184097 : Blo 1508951 9184097 := bstep (se 2 (by rfl) ⟨3444036, by rfl⟩ : syracuseStep 9184097 = 6888073) B6888073
theorem B4301693 : Blo 1508951 4301693 := bstep (se 3 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 4301693 = 1613135) B1613135
theorem B5735711 : Blo 1508951 5735711 := bstep (se 1 (by rfl) ⟨4301783, by rfl⟩ : syracuseStep 5735711 = 8603567) B8603567
theorem B12895645 : Blo 1508951 12895645 := bstep (se 3 (by rfl) ⟨2417933, by rfl⟩ : syracuseStep 12895645 = 4835867) B4835867
theorem B1910299 : Blo 1508951 1910299 := bstep (se 1 (by rfl) ⟨1432724, by rfl⟩ : syracuseStep 1910299 = 2865449) B2865449
theorem B4081259 : Blo 1508951 4081259 := bstep (se 1 (by rfl) ⟨3060944, by rfl⟩ : syracuseStep 4081259 = 6121889) B6121889
theorem B1509055 : Blo 1508951 1509055 := bstep (se 1 (by rfl) ⟨1131791, by rfl⟩ : syracuseStep 1509055 = 2263583) B2263583
theorem B31000265 : Blo 1508951 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B1697575 : Blo 1508951 1697575 := bstep (se 1 (by rfl) ⟨1273181, by rfl⟩ : syracuseStep 1697575 = 2546363) B2546363
theorem B6449053 : Blo 1508951 6449053 := bstep (se 3 (by rfl) ⟨1209197, by rfl⟩ : syracuseStep 6449053 = 2418395) B2418395
theorem B7645103 : Blo 1508951 7645103 := bstep (se 1 (by rfl) ⟨5733827, by rfl⟩ : syracuseStep 7645103 = 11467655) B11467655
theorem B1509311 : Blo 1508951 1509311 := bstep (se 1 (by rfl) ⟨1131983, by rfl⟩ : syracuseStep 1509311 = 2263967) B2263967
theorem B1910719 : Blo 1508951 1910719 := bstep (se 1 (by rfl) ⟨1433039, by rfl⟩ : syracuseStep 1910719 = 2866079) B2866079
theorem B12904393 : Blo 1508951 12904393 := bstep (se 2 (by rfl) ⟨4839147, by rfl⟩ : syracuseStep 12904393 = 9678295) B9678295
theorem B1509343 : Blo 1508951 1509343 := bstep (se 1 (by rfl) ⟨1132007, by rfl⟩ : syracuseStep 1509343 = 2264015) B2264015
theorem B24496109 : Blo 1508951 24496109 := bstep (se 3 (by rfl) ⟨4593020, by rfl⟩ : syracuseStep 24496109 = 9186041) B9186041
theorem B1509403 : Blo 1508951 1509403 := bstep (se 1 (by rfl) ⟨1132052, by rfl⟩ : syracuseStep 1509403 = 2264105) B2264105
theorem B1509407 : Blo 1508951 1509407 := bstep (se 1 (by rfl) ⟨1132055, by rfl⟩ : syracuseStep 1509407 = 2264111) B2264111
theorem B8595503 : Blo 1508951 8595503 := bstep (se 1 (by rfl) ⟨6446627, by rfl⟩ : syracuseStep 8595503 = 12893255) B12893255
theorem B1509423 : Blo 1508951 1509423 := bstep (se 1 (by rfl) ⟨1132067, by rfl⟩ : syracuseStep 1509423 = 2264135) B2264135
theorem B8718461 : Blo 1508951 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B1509599 : Blo 1508951 1509599 := bstep (se 1 (by rfl) ⟨1132199, by rfl⟩ : syracuseStep 1509599 = 2264399) B2264399
theorem B21776627 : Blo 1508951 21776627 := bstep (se 1 (by rfl) ⟨16332470, by rfl⟩ : syracuseStep 21776627 = 32664941) B32664941
theorem B1509659 : Blo 1508951 1509659 := bstep (se 1 (by rfl) ⟨1132244, by rfl⟩ : syracuseStep 1509659 = 2264489) B2264489
theorem B4835663 : Blo 1508951 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B12896603 : Blo 1508951 12896603 := bstep (se 1 (by rfl) ⟨9672452, by rfl⟩ : syracuseStep 12896603 = 19344905) B19344905
theorem B3819899 : Blo 1508951 3819899 := bstep (se 1 (by rfl) ⟨2864924, by rfl⟩ : syracuseStep 3819899 = 5729849) B5729849
theorem B1509759 : Blo 1508951 1509759 := bstep (se 1 (by rfl) ⟨1132319, by rfl⟩ : syracuseStep 1509759 = 2264639) B2264639
theorem B1509935 : Blo 1508951 1509935 := bstep (se 1 (by rfl) ⟨1132451, by rfl⟩ : syracuseStep 1509935 = 2264903) B2264903
theorem B2263655 : Blo 1508951 2263655 := bstep (se 1 (by rfl) ⟨1697741, by rfl⟩ : syracuseStep 2263655 = 3395483) B3395483
theorem B2148967 : Blo 1508951 2148967 := bstep (se 1 (by rfl) ⟨1611725, by rfl⟩ : syracuseStep 2148967 = 3223451) B3223451
theorem B1509991 : Blo 1508951 1509991 := bstep (se 1 (by rfl) ⟨1132493, by rfl⟩ : syracuseStep 1509991 = 2264987) B2264987
theorem B3820193 : Blo 1508951 3820193 := bstep (se 2 (by rfl) ⟨1432572, by rfl⟩ : syracuseStep 3820193 = 2865145) B2865145
theorem B11471543 : Blo 1508951 11471543 := bstep (se 1 (by rfl) ⟨8603657, by rfl⟩ : syracuseStep 11471543 = 17207315) B17207315
theorem B2263847 : Blo 1508951 2263847 := bstep (se 1 (by rfl) ⟨1697885, by rfl⟩ : syracuseStep 2263847 = 3395771) B3395771
theorem B11029391 : Blo 1508951 11029391 := bstep (se 1 (by rfl) ⟨8272043, by rfl⟩ : syracuseStep 11029391 = 16544087) B16544087
theorem B1510367 : Blo 1508951 1510367 := bstep (se 1 (by rfl) ⟨1132775, by rfl⟩ : syracuseStep 1510367 = 2265551) B2265551
theorem B1510395 : Blo 1508951 1510395 := bstep (se 1 (by rfl) ⟨1132796, by rfl⟩ : syracuseStep 1510395 = 2265593) B2265593
theorem B1510463 : Blo 1508951 1510463 := bstep (se 1 (by rfl) ⟨1132847, by rfl⟩ : syracuseStep 1510463 = 2265695) B2265695
theorem B2296895 : Blo 1508951 2296895 := bstep (se 1 (by rfl) ⟨1722671, by rfl⟩ : syracuseStep 2296895 = 3445343) B3445343
theorem B2264171 : Blo 1508951 2264171 := bstep (se 1 (by rfl) ⟨1698128, by rfl⟩ : syracuseStep 2264171 = 3396257) B3396257
theorem B5729561 : Blo 1508951 5729561 := bstep (se 2 (by rfl) ⟨2148585, by rfl⟩ : syracuseStep 5729561 = 4297171) B4297171
theorem B13782349 : Blo 1508951 13782349 := bstep (se 3 (by rfl) ⟨2584190, by rfl⟩ : syracuseStep 13782349 = 5168381) B5168381
theorem B2264411 : Blo 1508951 2264411 := bstep (se 1 (by rfl) ⟨1698308, by rfl⟩ : syracuseStep 2264411 = 3396617) B3396617
theorem B2264441 : Blo 1508951 2264441 := bstep (se 2 (by rfl) ⟨849165, by rfl⟩ : syracuseStep 2264441 = 1698331) B1698331
theorem B2149753 : Blo 1508951 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B2264447 : Blo 1508951 2264447 := bstep (se 1 (by rfl) ⟨1698335, by rfl⟩ : syracuseStep 2264447 = 3396671) B3396671
theorem B1510783 : Blo 1508951 1510783 := bstep (se 1 (by rfl) ⟨1133087, by rfl⟩ : syracuseStep 1510783 = 2266175) B2266175
theorem B1510811 : Blo 1508951 1510811 := bstep (se 1 (by rfl) ⟨1133108, by rfl⟩ : syracuseStep 1510811 = 2266217) B2266217
theorem B1510879 : Blo 1508951 1510879 := bstep (se 1 (by rfl) ⟨1133159, by rfl⟩ : syracuseStep 1510879 = 2266319) B2266319
theorem B9178703 : Blo 1508951 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B5099111 : Blo 1508951 5099111 := bstep (se 1 (by rfl) ⟨3824333, by rfl⟩ : syracuseStep 5099111 = 7648667) B7648667
theorem B178810541 : Blo 1508951 178810541 := bstep (se 3 (by rfl) ⟨33526976, by rfl⟩ : syracuseStep 178810541 = 67053953) B67053953
theorem B7253687 : Blo 1508951 7253687 := bstep (se 1 (by rfl) ⟨5440265, by rfl⟩ : syracuseStep 7253687 = 10880531) B10880531
theorem B3223433 : Blo 1508951 3223433 := bstep (se 2 (by rfl) ⟨1208787, by rfl⟩ : syracuseStep 3223433 = 2417575) B2417575
theorem B2265071 : Blo 1508951 2265071 := bstep (se 1 (by rfl) ⟨1698803, by rfl⟩ : syracuseStep 2265071 = 3397607) B3397607
theorem B2904059 : Blo 1508951 2904059 := bstep (se 1 (by rfl) ⟨2178044, by rfl⟩ : syracuseStep 2904059 = 4356089) B4356089
theorem B2265083 : Blo 1508951 2265083 := bstep (se 1 (by rfl) ⟨1698812, by rfl⟩ : syracuseStep 2265083 = 3397625) B3397625
theorem B2265143 : Blo 1508951 2265143 := bstep (se 1 (by rfl) ⟨1698857, by rfl⟩ : syracuseStep 2265143 = 3397715) B3397715
theorem B2265191 : Blo 1508951 2265191 := bstep (se 1 (by rfl) ⟨1698893, by rfl⟩ : syracuseStep 2265191 = 3397787) B3397787
theorem B7647371 : Blo 1508951 7647371 := bstep (se 1 (by rfl) ⟨5735528, by rfl⟩ : syracuseStep 7647371 = 11471057) B11471057
theorem B2265263 : Blo 1508951 2265263 := bstep (se 1 (by rfl) ⟨1698947, by rfl⟩ : syracuseStep 2265263 = 3397895) B3397895
theorem B2265467 : Blo 1508951 2265467 := bstep (se 1 (by rfl) ⟨1699100, by rfl⟩ : syracuseStep 2265467 = 3398201) B3398201
theorem B2265737 : Blo 1508951 2265737 := bstep (se 2 (by rfl) ⟨849651, by rfl⟩ : syracuseStep 2265737 = 1699303) B1699303
theorem B20656889 : Blo 1508951 20656889 := bstep (se 2 (by rfl) ⟨7746333, by rfl⟩ : syracuseStep 20656889 = 15492667) B15492667
theorem B8721209 : Blo 1508951 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B9671507 : Blo 1508951 9671507 := bstep (se 1 (by rfl) ⟨7253630, by rfl⟩ : syracuseStep 9671507 = 14507261) B14507261
theorem B2265947 : Blo 1508951 2265947 := bstep (se 1 (by rfl) ⟨1699460, by rfl⟩ : syracuseStep 2265947 = 3398921) B3398921
theorem B3224681 : Blo 1508951 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B7255169 : Blo 1508951 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B3396815 : Blo 1508951 3396815 := bstep (se 1 (by rfl) ⟨2547611, by rfl⟩ : syracuseStep 3396815 = 5095223) B5095223
theorem B3396905 : Blo 1508951 3396905 := bstep (se 2 (by rfl) ⟨1273839, by rfl⟩ : syracuseStep 3396905 = 2547679) B2547679
theorem B2266409 : Blo 1508951 2266409 := bstep (se 2 (by rfl) ⟨849903, by rfl⟩ : syracuseStep 2266409 = 1699807) B1699807
theorem B12891545 : Blo 1508951 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B3397103 : Blo 1508951 3397103 := bstep (se 1 (by rfl) ⟨2547827, by rfl⟩ : syracuseStep 3397103 = 5095655) B5095655
theorem B29005361 : Blo 1508951 29005361 := bstep (se 2 (by rfl) ⟨10877010, by rfl⟩ : syracuseStep 29005361 = 21754021) B21754021
theorem B3823271 : Blo 1508951 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B7648991 : Blo 1508951 7648991 := bstep (se 1 (by rfl) ⟨5736743, by rfl⟩ : syracuseStep 7648991 = 11473487) B11473487
theorem B2864879 : Blo 1508951 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B4298503 : Blo 1508951 4298503 := bstep (se 1 (by rfl) ⟨3223877, by rfl⟩ : syracuseStep 4298503 = 6447755) B6447755
theorem B6453053 : Blo 1508951 6453053 := bstep (se 3 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 6453053 = 2419895) B2419895
theorem B4839239 : Blo 1508951 4839239 := bstep (se 1 (by rfl) ⟨3629429, by rfl⟩ : syracuseStep 4839239 = 7258859) B7258859
theorem B14514025 : Blo 1508951 14514025 := bstep (se 2 (by rfl) ⟨5442759, by rfl⟩ : syracuseStep 14514025 = 10885519) B10885519
theorem B3397499 : Blo 1508951 3397499 := bstep (se 1 (by rfl) ⟨2548124, by rfl⟩ : syracuseStep 3397499 = 5096249) B5096249
theorem B3397535 : Blo 1508951 3397535 := bstep (se 1 (by rfl) ⟨2548151, by rfl⟩ : syracuseStep 3397535 = 5096303) B5096303
theorem B3397769 : Blo 1508951 3397769 := bstep (se 2 (by rfl) ⟨1274163, by rfl⟩ : syracuseStep 3397769 = 2548327) B2548327
theorem B3225791 : Blo 1508951 3225791 := bstep (se 1 (by rfl) ⟨2419343, by rfl⟩ : syracuseStep 3225791 = 4838687) B4838687
theorem B16324861 : Blo 1508951 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B4839763 : Blo 1508951 4839763 := bstep (se 1 (by rfl) ⟨3629822, by rfl⟩ : syracuseStep 4839763 = 7259645) B7259645
theorem B3397985 : Blo 1508951 3397985 := bstep (se 2 (by rfl) ⟨1274244, by rfl⟩ : syracuseStep 3397985 = 2548489) B2548489
theorem B3823969 : Blo 1508951 3823969 := bstep (se 2 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 3823969 = 2867977) B2867977
theorem B3398075 : Blo 1508951 3398075 := bstep (se 1 (by rfl) ⟨2548556, by rfl⟩ : syracuseStep 3398075 = 5097113) B5097113
theorem B13957595 : Blo 1508951 13957595 := bstep (se 1 (by rfl) ⟨10468196, by rfl⟩ : syracuseStep 13957595 = 20936393) B20936393
theorem B6887911 : Blo 1508951 6887911 := bstep (se 1 (by rfl) ⟨5165933, by rfl⟩ : syracuseStep 6887911 = 10331867) B10331867
theorem B2865851 : Blo 1508951 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B3398471 : Blo 1508951 3398471 := bstep (se 1 (by rfl) ⟨2548853, by rfl⟩ : syracuseStep 3398471 = 5097707) B5097707
theorem B3824455 : Blo 1508951 3824455 := bstep (se 1 (by rfl) ⟨2868341, by rfl⟩ : syracuseStep 3824455 = 5736683) B5736683
theorem B71613521 : Blo 1508951 71613521 := bstep (se 2 (by rfl) ⟨26855070, by rfl⟩ : syracuseStep 71613521 = 53710141) B53710141
theorem B3398777 : Blo 1508951 3398777 := bstep (se 2 (by rfl) ⟨1274541, by rfl⟩ : syracuseStep 3398777 = 2549083) B2549083
theorem B13434115 : Blo 1508951 13434115 := bstep (se 1 (by rfl) ⟨10075586, by rfl⟩ : syracuseStep 13434115 = 20151173) B20151173
theorem B2866603 : Blo 1508951 2866603 := bstep (se 1 (by rfl) ⟨2149952, by rfl⟩ : syracuseStep 2866603 = 4299905) B4299905
theorem B4300361 : Blo 1508951 4300361 := bstep (se 2 (by rfl) ⟨1612635, by rfl⟩ : syracuseStep 4300361 = 3225271) B3225271
theorem B3399335 : Blo 1508951 3399335 := bstep (se 1 (by rfl) ⟨2549501, by rfl⟩ : syracuseStep 3399335 = 5099003) B5099003
theorem B1531559 : Blo 1508951 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B3399443 : Blo 1508951 3399443 := bstep (se 1 (by rfl) ⟨2549582, by rfl⟩ : syracuseStep 3399443 = 5099165) B5099165
theorem B5734223 : Blo 1508951 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B11469113 : Blo 1508951 11469113 := bstep (se 2 (by rfl) ⟨4300917, by rfl⟩ : syracuseStep 11469113 = 8601835) B8601835
theorem B21766481 : Blo 1508951 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B13771259 : Blo 1508951 13771259 := bstep (se 1 (by rfl) ⟨10328444, by rfl⟩ : syracuseStep 13771259 = 20656889) B20656889
theorem B8602109 : Blo 1508951 8602109 := bstep (se 3 (by rfl) ⟨1612895, by rfl⟩ : syracuseStep 8602109 = 3225791) B3225791
theorem B6447671 : Blo 1508951 6447671 := bstep (se 1 (by rfl) ⟨4835753, by rfl⟩ : syracuseStep 6447671 = 9671507) B9671507
theorem B2867795 : Blo 1508951 2867795 := bstep (se 1 (by rfl) ⟨2150846, by rfl⟩ : syracuseStep 2867795 = 4301693) B4301693
theorem B9183881 : Blo 1508951 9183881 := bstep (se 2 (by rfl) ⟨3443955, by rfl⟩ : syracuseStep 9183881 = 6887911) B6887911
theorem B8594363 : Blo 1508951 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B2720839 : Blo 1508951 2720839 := bstep (se 1 (by rfl) ⟨2040629, by rfl⟩ : syracuseStep 2720839 = 4081259) B4081259
theorem B2548847 : Blo 1508951 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B1909919 : Blo 1508951 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B4302035 : Blo 1508951 4302035 := bstep (se 1 (by rfl) ⟨3226526, by rfl⟩ : syracuseStep 4302035 = 6453053) B6453053
theorem B5096735 : Blo 1508951 5096735 := bstep (se 1 (by rfl) ⟨3822551, by rfl⟩ : syracuseStep 5096735 = 7645103) B7645103
theorem B14517751 : Blo 1508951 14517751 := bstep (se 1 (by rfl) ⟨10888313, by rfl⟩ : syracuseStep 14517751 = 21776627) B21776627
theorem B1509103 : Blo 1508951 1509103 := bstep (se 1 (by rfl) ⟨1131827, by rfl⟩ : syracuseStep 1509103 = 2263655) B2263655
theorem B18376465 : Blo 1508951 18376465 := bstep (se 2 (by rfl) ⟨6891174, by rfl⟩ : syracuseStep 18376465 = 13782349) B13782349
theorem B1910567 : Blo 1508951 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B1509231 : Blo 1508951 1509231 := bstep (se 1 (by rfl) ⟨1131923, by rfl⟩ : syracuseStep 1509231 = 2263847) B2263847
theorem B1509447 : Blo 1508951 1509447 := bstep (se 1 (by rfl) ⟨1132085, by rfl⟩ : syracuseStep 1509447 = 2264171) B2264171
theorem B3819707 : Blo 1508951 3819707 := bstep (se 1 (by rfl) ⟨2864780, by rfl⟩ : syracuseStep 3819707 = 5729561) B5729561
theorem B1509607 : Blo 1508951 1509607 := bstep (se 1 (by rfl) ⟨1132205, by rfl⟩ : syracuseStep 1509607 = 2264411) B2264411
theorem B1509627 : Blo 1508951 1509627 := bstep (se 1 (by rfl) ⟨1132220, by rfl⟩ : syracuseStep 1509627 = 2264441) B2264441
theorem B1509631 : Blo 1508951 1509631 := bstep (se 1 (by rfl) ⟨1132223, by rfl⟩ : syracuseStep 1509631 = 2264447) B2264447
theorem B8595821 : Blo 1508951 8595821 := bstep (se 3 (by rfl) ⟨1611716, by rfl⟩ : syracuseStep 8595821 = 3223433) B3223433
theorem B2263433 : Blo 1508951 2263433 := bstep (se 2 (by rfl) ⟨848787, by rfl⟩ : syracuseStep 2263433 = 1697575) B1697575
theorem B4835791 : Blo 1508951 4835791 := bstep (se 1 (by rfl) ⟨3626843, by rfl⟩ : syracuseStep 4835791 = 7253687) B7253687
theorem B19352033 : Blo 1508951 19352033 := bstep (se 2 (by rfl) ⟨7257012, by rfl⟩ : syracuseStep 19352033 = 14514025) B14514025
theorem B17205857 : Blo 1508951 17205857 := bstep (se 2 (by rfl) ⟨6452196, by rfl⟩ : syracuseStep 17205857 = 12904393) B12904393
theorem B7744157 : Blo 1508951 7744157 := bstep (se 3 (by rfl) ⟨1452029, by rfl⟩ : syracuseStep 7744157 = 2904059) B2904059
theorem B1510047 : Blo 1508951 1510047 := bstep (se 1 (by rfl) ⟨1132535, by rfl⟩ : syracuseStep 1510047 = 2265071) B2265071
theorem B1510055 : Blo 1508951 1510055 := bstep (se 1 (by rfl) ⟨1132541, by rfl⟩ : syracuseStep 1510055 = 2265083) B2265083
theorem B1510095 : Blo 1508951 1510095 := bstep (se 1 (by rfl) ⟨1132571, by rfl⟩ : syracuseStep 1510095 = 2265143) B2265143
theorem B1510127 : Blo 1508951 1510127 := bstep (se 1 (by rfl) ⟨1132595, by rfl⟩ : syracuseStep 1510127 = 2265191) B2265191
theorem B5098247 : Blo 1508951 5098247 := bstep (se 1 (by rfl) ⟨3823685, by rfl⟩ : syracuseStep 5098247 = 7647371) B7647371
theorem B1510175 : Blo 1508951 1510175 := bstep (se 1 (by rfl) ⟨1132631, by rfl⟩ : syracuseStep 1510175 = 2265263) B2265263
theorem B1510311 : Blo 1508951 1510311 := bstep (se 1 (by rfl) ⟨1132733, by rfl⟩ : syracuseStep 1510311 = 2265467) B2265467
theorem B264875021 : Blo 1508951 264875021 := bstep (se 3 (by rfl) ⟨49664066, by rfl⟩ : syracuseStep 264875021 = 99328133) B99328133
theorem B1510491 : Blo 1508951 1510491 := bstep (se 1 (by rfl) ⟨1132868, by rfl⟩ : syracuseStep 1510491 = 2265737) B2265737
theorem B5098625 : Blo 1508951 5098625 := bstep (se 2 (by rfl) ⟨1911984, by rfl⟩ : syracuseStep 5098625 = 3823969) B3823969
theorem B1510631 : Blo 1508951 1510631 := bstep (se 1 (by rfl) ⟨1132973, by rfl⟩ : syracuseStep 1510631 = 2265947) B2265947
theorem B6122731 : Blo 1508951 6122731 := bstep (se 1 (by rfl) ⟨4592048, by rfl⟩ : syracuseStep 6122731 = 9184097) B9184097
theorem B2149787 : Blo 1508951 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B4836779 : Blo 1508951 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B2264543 : Blo 1508951 2264543 := bstep (se 1 (by rfl) ⟨1698407, by rfl⟩ : syracuseStep 2264543 = 3396815) B3396815
theorem B2264603 : Blo 1508951 2264603 := bstep (se 1 (by rfl) ⟨1698452, by rfl⟩ : syracuseStep 2264603 = 3396905) B3396905
theorem B1510939 : Blo 1508951 1510939 := bstep (se 1 (by rfl) ⟨1133204, by rfl⟩ : syracuseStep 1510939 = 2266409) B2266409
theorem B2264735 : Blo 1508951 2264735 := bstep (se 1 (by rfl) ⟨1698551, by rfl⟩ : syracuseStep 2264735 = 3397103) B3397103
theorem B19336907 : Blo 1508951 19336907 := bstep (se 1 (by rfl) ⟨14502680, by rfl⟩ : syracuseStep 19336907 = 29005361) B29005361
theorem B5099273 : Blo 1508951 5099273 := bstep (se 2 (by rfl) ⟨1912227, by rfl⟩ : syracuseStep 5099273 = 3824455) B3824455
theorem B5099327 : Blo 1508951 5099327 := bstep (se 1 (by rfl) ⟨3824495, by rfl⟩ : syracuseStep 5099327 = 7648991) B7648991
theorem B2264999 : Blo 1508951 2264999 := bstep (se 1 (by rfl) ⟨1698749, by rfl⟩ : syracuseStep 2264999 = 3397499) B3397499
theorem B2265023 : Blo 1508951 2265023 := bstep (se 1 (by rfl) ⟨1698767, by rfl⟩ : syracuseStep 2265023 = 3397535) B3397535
theorem B16330739 : Blo 1508951 16330739 := bstep (se 1 (by rfl) ⟨12248054, by rfl⟩ : syracuseStep 16330739 = 24496109) B24496109
theorem B5730335 : Blo 1508951 5730335 := bstep (se 1 (by rfl) ⟨4297751, by rfl⟩ : syracuseStep 5730335 = 8595503) B8595503
theorem B5812307 : Blo 1508951 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B2265179 : Blo 1508951 2265179 := bstep (se 1 (by rfl) ⟨1698884, by rfl⟩ : syracuseStep 2265179 = 3397769) B3397769
theorem B3223775 : Blo 1508951 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B8597735 : Blo 1508951 8597735 := bstep (se 1 (by rfl) ⟨6448301, by rfl⟩ : syracuseStep 8597735 = 12896603) B12896603
theorem B2265323 : Blo 1508951 2265323 := bstep (se 1 (by rfl) ⟨1698992, by rfl⟩ : syracuseStep 2265323 = 3397985) B3397985
theorem B2265383 : Blo 1508951 2265383 := bstep (se 1 (by rfl) ⟨1699037, by rfl⟩ : syracuseStep 2265383 = 3398075) B3398075
theorem B4084157 : Blo 1508951 4084157 := bstep (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) B1531559
theorem B7647695 : Blo 1508951 7647695 := bstep (se 1 (by rfl) ⟨5735771, by rfl⟩ : syracuseStep 7647695 = 11471543) B11471543
theorem B2265647 : Blo 1508951 2265647 := bstep (se 1 (by rfl) ⟨1699235, by rfl⟩ : syracuseStep 2265647 = 3398471) B3398471
theorem B3822137 : Blo 1508951 3822137 := bstep (se 2 (by rfl) ⟨1433301, by rfl⟩ : syracuseStep 3822137 = 2866603) B2866603
theorem B7352927 : Blo 1508951 7352927 := bstep (se 1 (by rfl) ⟨5514695, by rfl⟩ : syracuseStep 7352927 = 11029391) B11029391
theorem B2265851 : Blo 1508951 2265851 := bstep (se 1 (by rfl) ⟨1699388, by rfl⟩ : syracuseStep 2265851 = 3398777) B3398777
theorem B5731337 : Blo 1508951 5731337 := bstep (se 2 (by rfl) ⟨2149251, by rfl⟩ : syracuseStep 5731337 = 4298503) B4298503
theorem B2266223 : Blo 1508951 2266223 := bstep (se 1 (by rfl) ⟨1699667, by rfl⟩ : syracuseStep 2266223 = 3399335) B3399335
theorem B119207027 : Blo 1508951 119207027 := bstep (se 1 (by rfl) ⟨89405270, by rfl⟩ : syracuseStep 119207027 = 178810541) B178810541
theorem B2266295 : Blo 1508951 2266295 := bstep (se 1 (by rfl) ⟨1699721, by rfl⟩ : syracuseStep 2266295 = 3399443) B3399443
theorem B8598737 : Blo 1508951 8598737 := bstep (se 2 (by rfl) ⟨3224526, by rfl⟩ : syracuseStep 8598737 = 6449053) B6449053
theorem B3822815 : Blo 1508951 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B286594453 : Blo 1508951 286594453 := bstep (se 6 (by rfl) ⟨6717057, by rfl⟩ : syracuseStep 286594453 = 13434115) B13434115
theorem B6125053 : Blo 1508951 6125053 := bstep (se 3 (by rfl) ⟨1148447, by rfl⟩ : syracuseStep 6125053 = 2296895) B2296895
theorem B6453017 : Blo 1508951 6453017 := bstep (se 2 (by rfl) ⟨2419881, by rfl⟩ : syracuseStep 6453017 = 4839763) B4839763
theorem B13768555 : Blo 1508951 13768555 := bstep (se 1 (by rfl) ⟨10326416, by rfl⟩ : syracuseStep 13768555 = 20652833) B20652833
theorem B3823483 : Blo 1508951 3823483 := bstep (se 1 (by rfl) ⟨2867612, by rfl⟩ : syracuseStep 3823483 = 5735225) B5735225
theorem B2865289 : Blo 1508951 2865289 := bstep (se 2 (by rfl) ⟨1074483, by rfl⟩ : syracuseStep 2865289 = 2148967) B2148967
theorem B3823807 : Blo 1508951 3823807 := bstep (se 1 (by rfl) ⟨2867855, by rfl⟩ : syracuseStep 3823807 = 5735711) B5735711
theorem B20666843 : Blo 1508951 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B3226159 : Blo 1508951 3226159 := bstep (se 1 (by rfl) ⟨2419619, by rfl⟩ : syracuseStep 3226159 = 4839239) B4839239
theorem B2546599 : Blo 1508951 2546599 := bstep (se 1 (by rfl) ⟨1909949, by rfl⟩ : syracuseStep 2546599 = 3819899) B3819899
theorem B9305063 : Blo 1508951 9305063 := bstep (se 1 (by rfl) ⟨6978797, by rfl⟩ : syracuseStep 9305063 = 13957595) B13957595
theorem B2546795 : Blo 1508951 2546795 := bstep (se 1 (by rfl) ⟨1910096, by rfl⟩ : syracuseStep 2546795 = 3820193) B3820193
theorem B2866337 : Blo 1508951 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B17194193 : Blo 1508951 17194193 := bstep (se 2 (by rfl) ⟨6447822, by rfl⟩ : syracuseStep 17194193 = 12895645) B12895645
theorem B2547065 : Blo 1508951 2547065 := bstep (se 2 (by rfl) ⟨955149, by rfl⟩ : syracuseStep 2547065 = 1910299) B1910299
theorem B47742347 : Blo 1508951 47742347 := bstep (se 1 (by rfl) ⟨35806760, by rfl⟩ : syracuseStep 47742347 = 71613521) B71613521
theorem B23256557 : Blo 1508951 23256557 := bstep (se 3 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 23256557 = 8721209) B8721209
theorem B2866907 : Blo 1508951 2866907 := bstep (se 1 (by rfl) ⟨2150180, by rfl⟩ : syracuseStep 2866907 = 4300361) B4300361
theorem B6119135 : Blo 1508951 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B3399407 : Blo 1508951 3399407 := bstep (se 1 (by rfl) ⟨2549555, by rfl⟩ : syracuseStep 3399407 = 5099111) B5099111
theorem B2547625 : Blo 1508951 2547625 := bstep (se 2 (by rfl) ⟨955359, by rfl⟩ : syracuseStep 2547625 = 1910719) B1910719
theorem B3874871 : Blo 1508951 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B5734739 : Blo 1508951 5734739 := bstep (se 1 (by rfl) ⟨4301054, by rfl⟩ : syracuseStep 5734739 = 8602109) B8602109
theorem B2548091 : Blo 1508951 2548091 := bstep (se 1 (by rfl) ⟨1911068, by rfl⟩ : syracuseStep 2548091 = 3822137) B3822137
theorem B6447721 : Blo 1508951 6447721 := bstep (se 2 (by rfl) ⟨2417895, by rfl⟩ : syracuseStep 6447721 = 4835791) B4835791
theorem B4301545 : Blo 1508951 4301545 := bstep (se 2 (by rfl) ⟨1613079, by rfl⟩ : syracuseStep 4301545 = 3226159) B3226159
theorem B2868023 : Blo 1508951 2868023 := bstep (se 1 (by rfl) ⟨2151017, by rfl⟩ : syracuseStep 2868023 = 4302035) B4302035
theorem B2548543 : Blo 1508951 2548543 := bstep (se 1 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 2548543 = 3822815) B3822815
theorem B4302011 : Blo 1508951 4302011 := bstep (se 1 (by rfl) ⟨3226508, by rfl⟩ : syracuseStep 4302011 = 6453017) B6453017
theorem B1508955 : Blo 1508951 1508955 := bstep (se 1 (by rfl) ⟨1131716, by rfl⟩ : syracuseStep 1508955 = 2263433) B2263433
theorem B11470571 : Blo 1508951 11470571 := bstep (se 1 (by rfl) ⟨8602928, by rfl⟩ : syracuseStep 11470571 = 17205857) B17205857
theorem B5162771 : Blo 1508951 5162771 := bstep (se 1 (by rfl) ⟨3872078, by rfl⟩ : syracuseStep 5162771 = 7744157) B7744157
theorem B382125937 : Blo 1508951 382125937 := bstep (se 2 (by rfl) ⟨143297226, by rfl⟩ : syracuseStep 382125937 = 286594453) B286594453
theorem B6203375 : Blo 1508951 6203375 := bstep (se 1 (by rfl) ⟨4652531, by rfl⟩ : syracuseStep 6203375 = 9305063) B9305063
theorem B1697863 : Blo 1508951 1697863 := bstep (se 1 (by rfl) ⟨1273397, by rfl⟩ : syracuseStep 1697863 = 2546795) B2546795
theorem B1910891 : Blo 1508951 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B11462795 : Blo 1508951 11462795 := bstep (se 1 (by rfl) ⟨8597096, by rfl⟩ : syracuseStep 11462795 = 17194193) B17194193
theorem B1698043 : Blo 1508951 1698043 := bstep (se 1 (by rfl) ⟨1273532, by rfl⟩ : syracuseStep 1698043 = 2547065) B2547065
theorem B31828231 : Blo 1508951 31828231 := bstep (se 1 (by rfl) ⟨23871173, by rfl⟩ : syracuseStep 31828231 = 47742347) B47742347
theorem B1509695 : Blo 1508951 1509695 := bstep (se 1 (by rfl) ⟨1132271, by rfl⟩ : syracuseStep 1509695 = 2264543) B2264543
theorem B1509735 : Blo 1508951 1509735 := bstep (se 1 (by rfl) ⟨1132301, by rfl⟩ : syracuseStep 1509735 = 2264603) B2264603
theorem B1509823 : Blo 1508951 1509823 := bstep (se 1 (by rfl) ⟨1132367, by rfl⟩ : syracuseStep 1509823 = 2264735) B2264735
theorem B1911271 : Blo 1508951 1911271 := bstep (se 1 (by rfl) ⟨1433453, by rfl⟩ : syracuseStep 1911271 = 2866907) B2866907
theorem B5097977 : Blo 1508951 5097977 := bstep (se 2 (by rfl) ⟨1911741, by rfl⟩ : syracuseStep 5097977 = 3823483) B3823483
theorem B1509999 : Blo 1508951 1509999 := bstep (se 1 (by rfl) ⟨1132499, by rfl⟩ : syracuseStep 1509999 = 2264999) B2264999
theorem B1510015 : Blo 1508951 1510015 := bstep (se 1 (by rfl) ⟨1132511, by rfl⟩ : syracuseStep 1510015 = 2265023) B2265023
theorem B3820223 : Blo 1508951 3820223 := bstep (se 1 (by rfl) ⟨2865167, by rfl⟩ : syracuseStep 3820223 = 5730335) B5730335
theorem B1510119 : Blo 1508951 1510119 := bstep (se 1 (by rfl) ⟨1132589, by rfl⟩ : syracuseStep 1510119 = 2265179) B2265179
theorem B2149183 : Blo 1508951 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B1510215 : Blo 1508951 1510215 := bstep (se 1 (by rfl) ⟨1132661, by rfl⟩ : syracuseStep 1510215 = 2265323) B2265323
theorem B3820385 : Blo 1508951 3820385 := bstep (se 2 (by rfl) ⟨1432644, by rfl⟩ : syracuseStep 3820385 = 2865289) B2865289
theorem B1510255 : Blo 1508951 1510255 := bstep (se 1 (by rfl) ⟨1132691, by rfl⟩ : syracuseStep 1510255 = 2265383) B2265383
theorem B7646075 : Blo 1508951 7646075 := bstep (se 1 (by rfl) ⟨5734556, by rfl⟩ : syracuseStep 7646075 = 11469113) B11469113
theorem B14510987 : Blo 1508951 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B5098409 : Blo 1508951 5098409 := bstep (se 2 (by rfl) ⟨1911903, by rfl⟩ : syracuseStep 5098409 = 3823807) B3823807
theorem B2722771 : Blo 1508951 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B317885405 : Blo 1508951 317885405 := bstep (se 3 (by rfl) ⟨59603513, by rfl⟩ : syracuseStep 317885405 = 119207027) B119207027
theorem B5098463 : Blo 1508951 5098463 := bstep (se 1 (by rfl) ⟨3823847, by rfl⟩ : syracuseStep 5098463 = 7647695) B7647695
theorem B1510431 : Blo 1508951 1510431 := bstep (se 1 (by rfl) ⟨1132823, by rfl⟩ : syracuseStep 1510431 = 2265647) B2265647
theorem B1911863 : Blo 1508951 1911863 := bstep (se 1 (by rfl) ⟨1433897, by rfl⟩ : syracuseStep 1911863 = 2867795) B2867795
theorem B4901951 : Blo 1508951 4901951 := bstep (se 1 (by rfl) ⟨3676463, by rfl⟩ : syracuseStep 4901951 = 7352927) B7352927
theorem B6122587 : Blo 1508951 6122587 := bstep (se 1 (by rfl) ⟨4591940, by rfl⟩ : syracuseStep 6122587 = 9183881) B9183881
theorem B1510567 : Blo 1508951 1510567 := bstep (se 1 (by rfl) ⟨1132925, by rfl⟩ : syracuseStep 1510567 = 2265851) B2265851
theorem B5729575 : Blo 1508951 5729575 := bstep (se 1 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 5729575 = 8594363) B8594363
theorem B3820891 : Blo 1508951 3820891 := bstep (se 1 (by rfl) ⟨2865668, by rfl⟩ : syracuseStep 3820891 = 5731337) B5731337
theorem B1699231 : Blo 1508951 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B1510815 : Blo 1508951 1510815 := bstep (se 1 (by rfl) ⟨1133111, by rfl⟩ : syracuseStep 1510815 = 2266223) B2266223
theorem B1510863 : Blo 1508951 1510863 := bstep (se 1 (by rfl) ⟨1133147, by rfl⟩ : syracuseStep 1510863 = 2266295) B2266295
theorem B3395465 : Blo 1508951 3395465 := bstep (se 2 (by rfl) ⟨1273299, by rfl⟩ : syracuseStep 3395465 = 2546599) B2546599
theorem B5730547 : Blo 1508951 5730547 := bstep (se 1 (by rfl) ⟨4297910, by rfl⟩ : syracuseStep 5730547 = 8595821) B8595821
theorem B8163641 : Blo 1508951 8163641 := bstep (se 2 (by rfl) ⟨3061365, by rfl⟩ : syracuseStep 8163641 = 6122731) B6122731
theorem B176583347 : Blo 1508951 176583347 := bstep (se 1 (by rfl) ⟨132437510, by rfl⟩ : syracuseStep 176583347 = 264875021) B264875021
theorem B3224519 : Blo 1508951 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B15504371 : Blo 1508951 15504371 := bstep (se 1 (by rfl) ⟨11628278, by rfl⟩ : syracuseStep 15504371 = 23256557) B23256557
theorem B12891271 : Blo 1508951 12891271 := bstep (se 1 (by rfl) ⟨9668453, by rfl⟩ : syracuseStep 12891271 = 19336907) B19336907
theorem B2266271 : Blo 1508951 2266271 := bstep (se 1 (by rfl) ⟨1699703, by rfl⟩ : syracuseStep 2266271 = 3399407) B3399407
theorem B3396833 : Blo 1508951 3396833 := bstep (se 2 (by rfl) ⟨1273812, by rfl⟩ : syracuseStep 3396833 = 2547625) B2547625
theorem B5731823 : Blo 1508951 5731823 := bstep (se 1 (by rfl) ⟨4298867, by rfl⟩ : syracuseStep 5731823 = 8597735) B8597735
theorem B9180839 : Blo 1508951 9180839 := bstep (se 1 (by rfl) ⟨6885629, by rfl⟩ : syracuseStep 9180839 = 13771259) B13771259
theorem B4298447 : Blo 1508951 4298447 := bstep (se 1 (by rfl) ⟨3223835, by rfl⟩ : syracuseStep 4298447 = 6447671) B6447671
theorem B5093117 : Blo 1508951 5093117 := bstep (se 3 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 5093117 = 1909919) B1909919
theorem B5732491 : Blo 1508951 5732491 := bstep (se 1 (by rfl) ⟨4299368, by rfl⟩ : syracuseStep 5732491 = 8598737) B8598737
theorem B3397823 : Blo 1508951 3397823 := bstep (se 1 (by rfl) ⟨2548367, by rfl⟩ : syracuseStep 3397823 = 5096735) B5096735
theorem B5732765 : Blo 1508951 5732765 := bstep (se 3 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 5732765 = 2149787) B2149787
theorem B3627785 : Blo 1508951 3627785 := bstep (se 2 (by rfl) ⟨1360419, by rfl⟩ : syracuseStep 3627785 = 2720839) B2720839
theorem B2546471 : Blo 1508951 2546471 := bstep (se 1 (by rfl) ⟨1909853, by rfl⟩ : syracuseStep 2546471 = 3819707) B3819707
theorem B13777895 : Blo 1508951 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B12901355 : Blo 1508951 12901355 := bstep (se 1 (by rfl) ⟨9676016, by rfl⟩ : syracuseStep 12901355 = 19352033) B19352033
theorem B3398831 : Blo 1508951 3398831 := bstep (se 1 (by rfl) ⟨2549123, by rfl⟩ : syracuseStep 3398831 = 5098247) B5098247
theorem B19357001 : Blo 1508951 19357001 := bstep (se 2 (by rfl) ⟨7258875, by rfl⟩ : syracuseStep 19357001 = 14517751) B14517751
theorem B8166737 : Blo 1508951 8166737 := bstep (se 2 (by rfl) ⟨3062526, by rfl⟩ : syracuseStep 8166737 = 6125053) B6125053
theorem B3399083 : Blo 1508951 3399083 := bstep (se 1 (by rfl) ⟨2549312, by rfl⟩ : syracuseStep 3399083 = 5098625) B5098625
theorem B5094845 : Blo 1508951 5094845 := bstep (se 3 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 5094845 = 1910567) B1910567
theorem B24501953 : Blo 1508951 24501953 := bstep (se 2 (by rfl) ⟨9188232, by rfl⟩ : syracuseStep 24501953 = 18376465) B18376465
theorem B18358073 : Blo 1508951 18358073 := bstep (se 2 (by rfl) ⟨6884277, by rfl⟩ : syracuseStep 18358073 = 13768555) B13768555
theorem B4079423 : Blo 1508951 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B3399515 : Blo 1508951 3399515 := bstep (se 1 (by rfl) ⟨2549636, by rfl⟩ : syracuseStep 3399515 = 5099273) B5099273
theorem B3399551 : Blo 1508951 3399551 := bstep (se 1 (by rfl) ⟨2549663, by rfl⟩ : syracuseStep 3399551 = 5099327) B5099327
theorem B43548637 : Blo 1508951 43548637 := bstep (se 3 (by rfl) ⟨8165369, by rfl⟩ : syracuseStep 43548637 = 16330739) B16330739
theorem B7643321 : Blo 1508951 7643321 := bstep (se 2 (by rfl) ⟨2866245, by rfl⟩ : syracuseStep 7643321 = 5732491) B5732491
theorem B5095709 : Blo 1508951 5095709 := bstep (se 3 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 5095709 = 1910891) B1910891
theorem B2548361 : Blo 1508951 2548361 := bstep (se 2 (by rfl) ⟨955635, by rfl⟩ : syracuseStep 2548361 = 1911271) B1911271
theorem B5735393 : Blo 1508951 5735393 := bstep (se 2 (by rfl) ⟨2150772, by rfl⟩ : syracuseStep 5735393 = 4301545) B4301545
theorem B6120559 : Blo 1508951 6120559 := bstep (se 1 (by rfl) ⟨4590419, by rfl⟩ : syracuseStep 6120559 = 9180839) B9180839
theorem B3441847 : Blo 1508951 3441847 := bstep (se 1 (by rfl) ⟨2581385, by rfl⟩ : syracuseStep 3441847 = 5162771) B5162771
theorem B3630361 : Blo 1508951 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B17188361 : Blo 1508951 17188361 := bstep (se 2 (by rfl) ⟨6445635, by rfl⟩ : syracuseStep 17188361 = 12891271) B12891271
theorem B11462309 : Blo 1508951 11462309 := bstep (se 4 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 11462309 = 2149183) B2149183
theorem B1697647 : Blo 1508951 1697647 := bstep (se 1 (by rfl) ⟨1273235, by rfl⟩ : syracuseStep 1697647 = 2546471) B2546471
theorem B5097383 : Blo 1508951 5097383 := bstep (se 1 (by rfl) ⟨3823037, by rfl⟩ : syracuseStep 5097383 = 7646075) B7646075
theorem B12904667 : Blo 1508951 12904667 := bstep (se 1 (by rfl) ⟨9678500, by rfl⟩ : syracuseStep 12904667 = 19357001) B19357001
theorem B847694413 : Blo 1508951 847694413 := bstep (se 3 (by rfl) ⟨158942702, by rfl⟩ : syracuseStep 847694413 = 317885405) B317885405
theorem B2263643 : Blo 1508951 2263643 := bstep (se 1 (by rfl) ⟨1697732, by rfl⟩ : syracuseStep 2263643 = 3395465) B3395465
theorem B2583247 : Blo 1508951 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B2263817 : Blo 1508951 2263817 := bstep (se 2 (by rfl) ⟨848931, by rfl⟩ : syracuseStep 2263817 = 1697863) B1697863
theorem B5098301 : Blo 1508951 5098301 := bstep (se 3 (by rfl) ⟨955931, by rfl⟩ : syracuseStep 5098301 = 1911863) B1911863
theorem B5442427 : Blo 1508951 5442427 := bstep (se 1 (by rfl) ⟨4081820, by rfl⟩ : syracuseStep 5442427 = 8163641) B8163641
theorem B1698727 : Blo 1508951 1698727 := bstep (se 1 (by rfl) ⟨1274045, by rfl⟩ : syracuseStep 1698727 = 2548091) B2548091
theorem B2264057 : Blo 1508951 2264057 := bstep (se 2 (by rfl) ⟨849021, by rfl⟩ : syracuseStep 2264057 = 1698043) B1698043
theorem B42437641 : Blo 1508951 42437641 := bstep (se 2 (by rfl) ⟨15914115, by rfl⟩ : syracuseStep 42437641 = 31828231) B31828231
theorem B117722231 : Blo 1508951 117722231 := bstep (se 1 (by rfl) ⟨88291673, by rfl⟩ : syracuseStep 117722231 = 176583347) B176583347
theorem B11472029 : Blo 1508951 11472029 := bstep (se 3 (by rfl) ⟨2151005, by rfl⟩ : syracuseStep 11472029 = 4302011) B4302011
theorem B1912015 : Blo 1508951 1912015 := bstep (se 1 (by rfl) ⟨1434011, by rfl⟩ : syracuseStep 1912015 = 2868023) B2868023
theorem B2149679 : Blo 1508951 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B1510847 : Blo 1508951 1510847 := bstep (se 1 (by rfl) ⟨1133135, by rfl⟩ : syracuseStep 1510847 = 2266271) B2266271
theorem B8596961 : Blo 1508951 8596961 := bstep (se 2 (by rfl) ⟨3223860, by rfl⟩ : syracuseStep 8596961 = 6447721) B6447721
theorem B2264555 : Blo 1508951 2264555 := bstep (se 1 (by rfl) ⟨1698416, by rfl⟩ : syracuseStep 2264555 = 3396833) B3396833
theorem B3821215 : Blo 1508951 3821215 := bstep (se 1 (by rfl) ⟨2865911, by rfl⟩ : syracuseStep 3821215 = 5731823) B5731823
theorem B7647047 : Blo 1508951 7647047 := bstep (se 1 (by rfl) ⟨5735285, by rfl⟩ : syracuseStep 7647047 = 11470571) B11470571
theorem B3395411 : Blo 1508951 3395411 := bstep (se 1 (by rfl) ⟨2546558, by rfl⟩ : syracuseStep 3395411 = 5093117) B5093117
theorem B8163449 : Blo 1508951 8163449 := bstep (se 2 (by rfl) ⟨3061293, by rfl⟩ : syracuseStep 8163449 = 6122587) B6122587
theorem B2265215 : Blo 1508951 2265215 := bstep (se 1 (by rfl) ⟨1698911, by rfl⟩ : syracuseStep 2265215 = 3397823) B3397823
theorem B3821843 : Blo 1508951 3821843 := bstep (se 1 (by rfl) ⟨2866382, by rfl⟩ : syracuseStep 3821843 = 5732765) B5732765
theorem B7639433 : Blo 1508951 7639433 := bstep (se 2 (by rfl) ⟨2864787, by rfl⟩ : syracuseStep 7639433 = 5729575) B5729575
theorem B2265641 : Blo 1508951 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B2265887 : Blo 1508951 2265887 := bstep (se 1 (by rfl) ⟨1699415, by rfl⟩ : syracuseStep 2265887 = 3398831) B3398831
theorem B5444491 : Blo 1508951 5444491 := bstep (se 1 (by rfl) ⟨4083368, by rfl⟩ : syracuseStep 5444491 = 8166737) B8166737
theorem B2266055 : Blo 1508951 2266055 := bstep (se 1 (by rfl) ⟨1699541, by rfl⟩ : syracuseStep 2266055 = 3399083) B3399083
theorem B3396563 : Blo 1508951 3396563 := bstep (se 1 (by rfl) ⟨2547422, by rfl⟩ : syracuseStep 3396563 = 5094845) B5094845
theorem B2266343 : Blo 1508951 2266343 := bstep (se 1 (by rfl) ⟨1699757, by rfl⟩ : syracuseStep 2266343 = 3399515) B3399515
theorem B2266367 : Blo 1508951 2266367 := bstep (se 1 (by rfl) ⟨1699775, by rfl⟩ : syracuseStep 2266367 = 3399551) B3399551
theorem B3823159 : Blo 1508951 3823159 := bstep (se 1 (by rfl) ⟨2867369, by rfl⟩ : syracuseStep 3823159 = 5734739) B5734739
theorem B7640729 : Blo 1508951 7640729 := bstep (se 2 (by rfl) ⟨2865273, by rfl⟩ : syracuseStep 7640729 = 5730547) B5730547
theorem B10336247 : Blo 1508951 10336247 := bstep (se 1 (by rfl) ⟨7752185, by rfl⟩ : syracuseStep 10336247 = 15504371) B15504371
theorem B3398057 : Blo 1508951 3398057 := bstep (se 2 (by rfl) ⟨1274271, by rfl⟩ : syracuseStep 3398057 = 2548543) B2548543
theorem B2865631 : Blo 1508951 2865631 := bstep (se 1 (by rfl) ⟨2149223, by rfl⟩ : syracuseStep 2865631 = 4298447) B4298447
theorem B4135583 : Blo 1508951 4135583 := bstep (se 1 (by rfl) ⟨3101687, by rfl⟩ : syracuseStep 4135583 = 6203375) B6203375
theorem B7641863 : Blo 1508951 7641863 := bstep (se 1 (by rfl) ⟨5731397, by rfl⟩ : syracuseStep 7641863 = 11462795) B11462795
theorem B3398651 : Blo 1508951 3398651 := bstep (se 1 (by rfl) ⟨2548988, by rfl⟩ : syracuseStep 3398651 = 5097977) B5097977
theorem B5094521 : Blo 1508951 5094521 := bstep (se 2 (by rfl) ⟨1910445, by rfl⟩ : syracuseStep 5094521 = 3820891) B3820891
theorem B2546815 : Blo 1508951 2546815 := bstep (se 1 (by rfl) ⟨1910111, by rfl⟩ : syracuseStep 2546815 = 3820223) B3820223
theorem B2546923 : Blo 1508951 2546923 := bstep (se 1 (by rfl) ⟨1910192, by rfl⟩ : syracuseStep 2546923 = 3820385) B3820385
theorem B9673991 : Blo 1508951 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B3398939 : Blo 1508951 3398939 := bstep (se 1 (by rfl) ⟨2549204, by rfl⟩ : syracuseStep 3398939 = 5098409) B5098409
theorem B3398975 : Blo 1508951 3398975 := bstep (se 1 (by rfl) ⟨2549231, by rfl⟩ : syracuseStep 3398975 = 5098463) B5098463
theorem B8600903 : Blo 1508951 8600903 := bstep (se 1 (by rfl) ⟨6450677, by rfl⟩ : syracuseStep 8600903 = 12901355) B12901355
theorem B9674093 : Blo 1508951 9674093 := bstep (se 3 (by rfl) ⟨1813892, by rfl⟩ : syracuseStep 9674093 = 3627785) B3627785
theorem B3267967 : Blo 1508951 3267967 := bstep (se 1 (by rfl) ⟨2450975, by rfl⟩ : syracuseStep 3267967 = 4901951) B4901951
theorem B16334635 : Blo 1508951 16334635 := bstep (se 1 (by rfl) ⟨12250976, by rfl⟩ : syracuseStep 16334635 = 24501953) B24501953
theorem B509501249 : Blo 1508951 509501249 := bstep (se 2 (by rfl) ⟨191062968, by rfl⟩ : syracuseStep 509501249 = 382125937) B382125937
theorem B12238715 : Blo 1508951 12238715 := bstep (se 1 (by rfl) ⟨9179036, by rfl⟩ : syracuseStep 12238715 = 18358073) B18358073
theorem B2719615 : Blo 1508951 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B36741053 : Blo 1508951 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B58064849 : Blo 1508951 58064849 := bstep (se 2 (by rfl) ⟨21774318, by rfl⟩ : syracuseStep 58064849 = 43548637) B43548637
theorem B5095547 : Blo 1508951 5095547 := bstep (se 1 (by rfl) ⟨3821660, by rfl⟩ : syracuseStep 5095547 = 7643321) B7643321
theorem B2547895 : Blo 1508951 2547895 := bstep (se 1 (by rfl) ⟨1910921, by rfl⟩ : syracuseStep 2547895 = 3821843) B3821843
theorem B1130259217 : Blo 1508951 1130259217 := bstep (se 2 (by rfl) ⟨423847206, by rfl⟩ : syracuseStep 1130259217 = 847694413) B847694413
theorem B7259321 : Blo 1508951 7259321 := bstep (se 2 (by rfl) ⟨2722245, by rfl⟩ : syracuseStep 7259321 = 5444491) B5444491
theorem B6890831 : Blo 1508951 6890831 := bstep (se 1 (by rfl) ⟨5168123, by rfl⟩ : syracuseStep 6890831 = 10336247) B10336247
theorem B56583521 : Blo 1508951 56583521 := bstep (se 2 (by rfl) ⟨21218820, by rfl⟩ : syracuseStep 56583521 = 42437641) B42437641
theorem B8603111 : Blo 1508951 8603111 := bstep (se 1 (by rfl) ⟨6452333, by rfl⟩ : syracuseStep 8603111 = 12904667) B12904667
theorem B8160745 : Blo 1508951 8160745 := bstep (se 2 (by rfl) ⟨3060279, by rfl⟩ : syracuseStep 8160745 = 6120559) B6120559
theorem B4589129 : Blo 1508951 4589129 := bstep (se 2 (by rfl) ⟨1720923, by rfl⟩ : syracuseStep 4589129 = 3441847) B3441847
theorem B2549353 : Blo 1508951 2549353 := bstep (se 2 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 2549353 = 1912015) B1912015
theorem B1509095 : Blo 1508951 1509095 := bstep (se 1 (by rfl) ⟨1131821, by rfl⟩ : syracuseStep 1509095 = 2263643) B2263643
theorem B11028221 : Blo 1508951 11028221 := bstep (se 3 (by rfl) ⟨2067791, by rfl⟩ : syracuseStep 11028221 = 4135583) B4135583
theorem B1509211 : Blo 1508951 1509211 := bstep (se 1 (by rfl) ⟨1131908, by rfl⟩ : syracuseStep 1509211 = 2263817) B2263817
theorem B1509371 : Blo 1508951 1509371 := bstep (se 1 (by rfl) ⟨1132028, by rfl⟩ : syracuseStep 1509371 = 2264057) B2264057
theorem B5097545 : Blo 1508951 5097545 := bstep (se 2 (by rfl) ⟨1911579, by rfl⟩ : syracuseStep 5097545 = 3823159) B3823159
theorem B78481487 : Blo 1508951 78481487 := bstep (se 1 (by rfl) ⟨58861115, by rfl⟩ : syracuseStep 78481487 = 117722231) B117722231
theorem B6449327 : Blo 1508951 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B6449395 : Blo 1508951 6449395 := bstep (se 1 (by rfl) ⟨4837046, by rfl⟩ : syracuseStep 6449395 = 9674093) B9674093
theorem B1509703 : Blo 1508951 1509703 := bstep (se 1 (by rfl) ⟨1132277, by rfl⟩ : syracuseStep 1509703 = 2264555) B2264555
theorem B2263529 : Blo 1508951 2263529 := bstep (se 2 (by rfl) ⟨848823, by rfl⟩ : syracuseStep 2263529 = 1697647) B1697647
theorem B339667499 : Blo 1508951 339667499 := bstep (se 1 (by rfl) ⟨254750624, by rfl⟩ : syracuseStep 339667499 = 509501249) B509501249
theorem B5098031 : Blo 1508951 5098031 := bstep (se 1 (by rfl) ⟨3823523, by rfl⟩ : syracuseStep 5098031 = 7647047) B7647047
theorem B2263607 : Blo 1508951 2263607 := bstep (se 1 (by rfl) ⟨1697705, by rfl⟩ : syracuseStep 2263607 = 3395411) B3395411
theorem B38709899 : Blo 1508951 38709899 := bstep (se 1 (by rfl) ⟨29032424, by rfl⟩ : syracuseStep 38709899 = 58064849) B58064849
theorem B5442299 : Blo 1508951 5442299 := bstep (se 1 (by rfl) ⟨4081724, by rfl⟩ : syracuseStep 5442299 = 8163449) B8163449
theorem B1510143 : Blo 1508951 1510143 := bstep (se 1 (by rfl) ⟨1132607, by rfl⟩ : syracuseStep 1510143 = 2265215) B2265215
theorem B1510427 : Blo 1508951 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B1698907 : Blo 1508951 1698907 := bstep (se 1 (by rfl) ⟨1274180, by rfl⟩ : syracuseStep 1698907 = 2548361) B2548361
theorem B1510591 : Blo 1508951 1510591 := bstep (se 1 (by rfl) ⟨1132943, by rfl⟩ : syracuseStep 1510591 = 2265887) B2265887
theorem B3820841 : Blo 1508951 3820841 := bstep (se 2 (by rfl) ⟨1432815, by rfl⟩ : syracuseStep 3820841 = 2865631) B2865631
theorem B1510703 : Blo 1508951 1510703 := bstep (se 1 (by rfl) ⟨1133027, by rfl⟩ : syracuseStep 1510703 = 2266055) B2266055
theorem B2264375 : Blo 1508951 2264375 := bstep (se 1 (by rfl) ⟨1698281, by rfl⟩ : syracuseStep 2264375 = 3396563) B3396563
theorem B1510895 : Blo 1508951 1510895 := bstep (se 1 (by rfl) ⟨1133171, by rfl⟩ : syracuseStep 1510895 = 2266343) B2266343
theorem B1510911 : Blo 1508951 1510911 := bstep (se 1 (by rfl) ⟨1133183, by rfl⟩ : syracuseStep 1510911 = 2266367) B2266367
theorem B3444329 : Blo 1508951 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B2264969 : Blo 1508951 2264969 := bstep (se 2 (by rfl) ⟨849363, by rfl⟩ : syracuseStep 2264969 = 1698727) B1698727
theorem B3395753 : Blo 1508951 3395753 := bstep (se 2 (by rfl) ⟨1273407, by rfl⟩ : syracuseStep 3395753 = 2546815) B2546815
theorem B2265371 : Blo 1508951 2265371 := bstep (se 1 (by rfl) ⟨1699028, by rfl⟩ : syracuseStep 2265371 = 3398057) B3398057
theorem B3395897 : Blo 1508951 3395897 := bstep (se 2 (by rfl) ⟨1273461, by rfl⟩ : syracuseStep 3395897 = 2546923) B2546923
theorem B2265767 : Blo 1508951 2265767 := bstep (se 1 (by rfl) ⟨1699325, by rfl⟩ : syracuseStep 2265767 = 3398651) B3398651
theorem B3396347 : Blo 1508951 3396347 := bstep (se 1 (by rfl) ⟨2547260, by rfl⟩ : syracuseStep 3396347 = 5094521) B5094521
theorem B7648019 : Blo 1508951 7648019 := bstep (se 1 (by rfl) ⟨5736014, by rfl⟩ : syracuseStep 7648019 = 11472029) B11472029
theorem B2265959 : Blo 1508951 2265959 := bstep (se 1 (by rfl) ⟨1699469, by rfl⟩ : syracuseStep 2265959 = 3398939) B3398939
theorem B2265983 : Blo 1508951 2265983 := bstep (se 1 (by rfl) ⟨1699487, by rfl⟩ : syracuseStep 2265983 = 3398975) B3398975
theorem B5731307 : Blo 1508951 5731307 := bstep (se 1 (by rfl) ⟨4298480, by rfl⟩ : syracuseStep 5731307 = 8596961) B8596961
theorem B21779513 : Blo 1508951 21779513 := bstep (se 2 (by rfl) ⟨8167317, by rfl⟩ : syracuseStep 21779513 = 16334635) B16334635
theorem B3626153 : Blo 1508951 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B3397139 : Blo 1508951 3397139 := bstep (se 1 (by rfl) ⟨2547854, by rfl⟩ : syracuseStep 3397139 = 5095709) B5095709
theorem B5092955 : Blo 1508951 5092955 := bstep (se 1 (by rfl) ⟨3819716, by rfl⟩ : syracuseStep 5092955 = 7639433) B7639433
theorem B3823595 : Blo 1508951 3823595 := bstep (se 1 (by rfl) ⟨2867696, by rfl⟩ : syracuseStep 3823595 = 5735393) B5735393
theorem B5732477 : Blo 1508951 5732477 := bstep (se 3 (by rfl) ⟨1074839, by rfl⟩ : syracuseStep 5732477 = 2149679) B2149679
theorem B11458907 : Blo 1508951 11458907 := bstep (se 1 (by rfl) ⟨8594180, by rfl⟩ : syracuseStep 11458907 = 17188361) B17188361
theorem B5093819 : Blo 1508951 5093819 := bstep (se 1 (by rfl) ⟨3820364, by rfl⟩ : syracuseStep 5093819 = 7640729) B7640729
theorem B7641539 : Blo 1508951 7641539 := bstep (se 1 (by rfl) ⟨5731154, by rfl⟩ : syracuseStep 7641539 = 11462309) B11462309
theorem B7256569 : Blo 1508951 7256569 := bstep (se 2 (by rfl) ⟨2721213, by rfl⟩ : syracuseStep 7256569 = 5442427) B5442427
theorem B3398255 : Blo 1508951 3398255 := bstep (se 1 (by rfl) ⟨2548691, by rfl⟩ : syracuseStep 3398255 = 5097383) B5097383
theorem B4840481 : Blo 1508951 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B4357289 : Blo 1508951 4357289 := bstep (se 2 (by rfl) ⟨1633983, by rfl⟩ : syracuseStep 4357289 = 3267967) B3267967
theorem B5094575 : Blo 1508951 5094575 := bstep (se 1 (by rfl) ⟨3820931, by rfl⟩ : syracuseStep 5094575 = 7641863) B7641863
theorem B3398867 : Blo 1508951 3398867 := bstep (se 1 (by rfl) ⟨2549150, by rfl⟩ : syracuseStep 3398867 = 5098301) B5098301
theorem B5094953 : Blo 1508951 5094953 := bstep (se 2 (by rfl) ⟨1910607, by rfl⟩ : syracuseStep 5094953 = 3821215) B3821215
theorem B5733935 : Blo 1508951 5733935 := bstep (se 1 (by rfl) ⟨4300451, by rfl⟩ : syracuseStep 5733935 = 8600903) B8600903
theorem B8159143 : Blo 1508951 8159143 := bstep (se 1 (by rfl) ⟨6119357, by rfl⟩ : syracuseStep 8159143 = 12238715) B12238715
theorem B24494035 : Blo 1508951 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B9675425 : Blo 1508951 9675425 := bstep (se 2 (by rfl) ⟨3628284, by rfl⟩ : syracuseStep 9675425 = 7256569) B7256569
theorem B2417435 : Blo 1508951 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B5735407 : Blo 1508951 5735407 := bstep (se 1 (by rfl) ⟨4301555, by rfl⟩ : syracuseStep 5735407 = 8603111) B8603111
theorem B2549063 : Blo 1508951 2549063 := bstep (se 1 (by rfl) ⟨1911797, by rfl⟩ : syracuseStep 2549063 = 3823595) B3823595
theorem B9184877 : Blo 1508951 9184877 := bstep (se 3 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 9184877 = 3444329) B3444329
theorem B1509019 : Blo 1508951 1509019 := bstep (se 1 (by rfl) ⟨1131764, by rfl⟩ : syracuseStep 1509019 = 2263529) B2263529
theorem B226444999 : Blo 1508951 226444999 := bstep (se 1 (by rfl) ⟨169833749, by rfl⟩ : syracuseStep 226444999 = 339667499) B339667499
theorem B1509071 : Blo 1508951 1509071 := bstep (se 1 (by rfl) ⟨1131803, by rfl⟩ : syracuseStep 1509071 = 2263607) B2263607
theorem B25806599 : Blo 1508951 25806599 := bstep (se 1 (by rfl) ⟨19354949, by rfl⟩ : syracuseStep 25806599 = 38709899) B38709899
theorem B10880993 : Blo 1508951 10880993 := bstep (se 2 (by rfl) ⟨4080372, by rfl⟩ : syracuseStep 10880993 = 8160745) B8160745
theorem B1509583 : Blo 1508951 1509583 := bstep (se 1 (by rfl) ⟨1132187, by rfl⟩ : syracuseStep 1509583 = 2264375) B2264375
theorem B1509979 : Blo 1508951 1509979 := bstep (se 1 (by rfl) ⟨1132484, by rfl⟩ : syracuseStep 1509979 = 2264969) B2264969
theorem B2263835 : Blo 1508951 2263835 := bstep (se 1 (by rfl) ⟨1697876, by rfl⟩ : syracuseStep 2263835 = 3395753) B3395753
theorem B1510247 : Blo 1508951 1510247 := bstep (se 1 (by rfl) ⟨1132685, by rfl⟩ : syracuseStep 1510247 = 2265371) B2265371
theorem B2263931 : Blo 1508951 2263931 := bstep (se 1 (by rfl) ⟨1697948, by rfl⟩ : syracuseStep 2263931 = 3395897) B3395897
theorem B1510511 : Blo 1508951 1510511 := bstep (se 1 (by rfl) ⟨1132883, by rfl⟩ : syracuseStep 1510511 = 2265767) B2265767
theorem B2264231 : Blo 1508951 2264231 := bstep (se 1 (by rfl) ⟨1698173, by rfl⟩ : syracuseStep 2264231 = 3396347) B3396347
theorem B5098679 : Blo 1508951 5098679 := bstep (se 1 (by rfl) ⟨3824009, by rfl⟩ : syracuseStep 5098679 = 7648019) B7648019
theorem B1510639 : Blo 1508951 1510639 := bstep (se 1 (by rfl) ⟨1132979, by rfl⟩ : syracuseStep 1510639 = 2265959) B2265959
theorem B1510655 : Blo 1508951 1510655 := bstep (se 1 (by rfl) ⟨1132991, by rfl⟩ : syracuseStep 1510655 = 2265983) B2265983
theorem B3820871 : Blo 1508951 3820871 := bstep (se 1 (by rfl) ⟨2865653, by rfl⟩ : syracuseStep 3820871 = 5731307) B5731307
theorem B14519675 : Blo 1508951 14519675 := bstep (se 1 (by rfl) ⟨10889756, by rfl⟩ : syracuseStep 14519675 = 21779513) B21779513
theorem B2264759 : Blo 1508951 2264759 := bstep (se 1 (by rfl) ⟨1698569, by rfl⟩ : syracuseStep 2264759 = 3397139) B3397139
theorem B1507012289 : Blo 1508951 1507012289 := bstep (se 2 (by rfl) ⟨565129608, by rfl⟩ : syracuseStep 1507012289 = 1130259217) B1130259217
theorem B3059419 : Blo 1508951 3059419 := bstep (se 1 (by rfl) ⟨2294564, by rfl⟩ : syracuseStep 3059419 = 4589129) B4589129
theorem B3395303 : Blo 1508951 3395303 := bstep (se 1 (by rfl) ⟨2546477, by rfl⟩ : syracuseStep 3395303 = 5092955) B5092955
theorem B7352147 : Blo 1508951 7352147 := bstep (se 1 (by rfl) ⟨5514110, by rfl⟩ : syracuseStep 7352147 = 11028221) B11028221
theorem B3821651 : Blo 1508951 3821651 := bstep (se 1 (by rfl) ⟨2866238, by rfl⟩ : syracuseStep 3821651 = 5732477) B5732477
theorem B2265209 : Blo 1508951 2265209 := bstep (se 2 (by rfl) ⟨849453, by rfl⟩ : syracuseStep 2265209 = 1698907) B1698907
theorem B7639271 : Blo 1508951 7639271 := bstep (se 1 (by rfl) ⟨5729453, by rfl⟩ : syracuseStep 7639271 = 11458907) B11458907
theorem B3395879 : Blo 1508951 3395879 := bstep (se 1 (by rfl) ⟨2546909, by rfl⟩ : syracuseStep 3395879 = 5093819) B5093819
theorem B2265503 : Blo 1508951 2265503 := bstep (se 1 (by rfl) ⟨1699127, by rfl⟩ : syracuseStep 2265503 = 3398255) B3398255
theorem B2904859 : Blo 1508951 2904859 := bstep (se 1 (by rfl) ⟨2178644, by rfl⟩ : syracuseStep 2904859 = 4357289) B4357289
theorem B3396383 : Blo 1508951 3396383 := bstep (se 1 (by rfl) ⟨2547287, by rfl⟩ : syracuseStep 3396383 = 5094575) B5094575
theorem B2265911 : Blo 1508951 2265911 := bstep (se 1 (by rfl) ⟨1699433, by rfl⟩ : syracuseStep 2265911 = 3398867) B3398867
theorem B3396635 : Blo 1508951 3396635 := bstep (se 1 (by rfl) ⟨2547476, by rfl⟩ : syracuseStep 3396635 = 5094953) B5094953
theorem B3822623 : Blo 1508951 3822623 := bstep (se 1 (by rfl) ⟨2866967, by rfl⟩ : syracuseStep 3822623 = 5733935) B5733935
theorem B32658713 : Blo 1508951 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B3397031 : Blo 1508951 3397031 := bstep (se 1 (by rfl) ⟨2547773, by rfl⟩ : syracuseStep 3397031 = 5095547) B5095547
theorem B3397193 : Blo 1508951 3397193 := bstep (se 2 (by rfl) ⟨1273947, by rfl⟩ : syracuseStep 3397193 = 2547895) B2547895
theorem B8599193 : Blo 1508951 8599193 := bstep (se 2 (by rfl) ⟨3224697, by rfl⟩ : syracuseStep 8599193 = 6449395) B6449395
theorem B4839547 : Blo 1508951 4839547 := bstep (se 1 (by rfl) ⟨3629660, by rfl⟩ : syracuseStep 4839547 = 7259321) B7259321
theorem B4593887 : Blo 1508951 4593887 := bstep (se 1 (by rfl) ⟨3445415, by rfl⟩ : syracuseStep 4593887 = 6890831) B6890831
theorem B37722347 : Blo 1508951 37722347 := bstep (se 1 (by rfl) ⟨28291760, by rfl⟩ : syracuseStep 37722347 = 56583521) B56583521
theorem B3398363 : Blo 1508951 3398363 := bstep (se 1 (by rfl) ⟨2548772, by rfl⟩ : syracuseStep 3398363 = 5097545) B5097545
theorem B52320991 : Blo 1508951 52320991 := bstep (se 1 (by rfl) ⟨39240743, by rfl⟩ : syracuseStep 52320991 = 78481487) B78481487
theorem B4299551 : Blo 1508951 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B5094359 : Blo 1508951 5094359 := bstep (se 1 (by rfl) ⟨3820769, by rfl⟩ : syracuseStep 5094359 = 7641539) B7641539
theorem B3398687 : Blo 1508951 3398687 := bstep (se 1 (by rfl) ⟨2549015, by rfl⟩ : syracuseStep 3398687 = 5098031) B5098031
theorem B3628199 : Blo 1508951 3628199 := bstep (se 1 (by rfl) ⟨2721149, by rfl⟩ : syracuseStep 3628199 = 5442299) B5442299
theorem B3226987 : Blo 1508951 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B3399137 : Blo 1508951 3399137 := bstep (se 2 (by rfl) ⟨1274676, by rfl⟩ : syracuseStep 3399137 = 2549353) B2549353
theorem B2547227 : Blo 1508951 2547227 := bstep (se 1 (by rfl) ⟨1910420, by rfl⟩ : syracuseStep 2547227 = 3820841) B3820841
theorem B10878857 : Blo 1508951 10878857 := bstep (se 2 (by rfl) ⟨4079571, by rfl⟩ : syracuseStep 10878857 = 8159143) B8159143
theorem B2547767 : Blo 1508951 2547767 := bstep (se 1 (by rfl) ⟨1910825, by rfl⟩ : syracuseStep 2547767 = 3821651) B3821651
theorem B9675197 : Blo 1508951 9675197 := bstep (se 3 (by rfl) ⟨1814099, by rfl⟩ : syracuseStep 9675197 = 3628199) B3628199
theorem B2548415 : Blo 1508951 2548415 := bstep (se 1 (by rfl) ⟨1911311, by rfl⟩ : syracuseStep 2548415 = 3822623) B3822623
theorem B17204399 : Blo 1508951 17204399 := bstep (se 1 (by rfl) ⟨12903299, by rfl⟩ : syracuseStep 17204399 = 25806599) B25806599
theorem B4302649 : Blo 1508951 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B1509223 : Blo 1508951 1509223 := bstep (se 1 (by rfl) ⟨1131917, by rfl⟩ : syracuseStep 1509223 = 2263835) B2263835
theorem B1509287 : Blo 1508951 1509287 := bstep (se 1 (by rfl) ⟨1131965, by rfl⟩ : syracuseStep 1509287 = 2263931) B2263931
theorem B1509487 : Blo 1508951 1509487 := bstep (se 1 (by rfl) ⟨1132115, by rfl⟩ : syracuseStep 1509487 = 2264231) B2264231
theorem B19605725 : Blo 1508951 19605725 := bstep (se 3 (by rfl) ⟨3676073, by rfl⟩ : syracuseStep 19605725 = 7352147) B7352147
theorem B301926665 : Blo 1508951 301926665 := bstep (se 2 (by rfl) ⟨113222499, by rfl⟩ : syracuseStep 301926665 = 226444999) B226444999
theorem B1698151 : Blo 1508951 1698151 := bstep (se 1 (by rfl) ⟨1273613, by rfl⟩ : syracuseStep 1698151 = 2547227) B2547227
theorem B1509839 : Blo 1508951 1509839 := bstep (se 1 (by rfl) ⟨1132379, by rfl⟩ : syracuseStep 1509839 = 2264759) B2264759
theorem B2263535 : Blo 1508951 2263535 := bstep (se 1 (by rfl) ⟨1697651, by rfl⟩ : syracuseStep 2263535 = 3395303) B3395303
theorem B7252571 : Blo 1508951 7252571 := bstep (se 1 (by rfl) ⟨5439428, by rfl⟩ : syracuseStep 7252571 = 10878857) B10878857
theorem B1510139 : Blo 1508951 1510139 := bstep (se 1 (by rfl) ⟨1132604, by rfl⟩ : syracuseStep 1510139 = 2265209) B2265209
theorem B2263919 : Blo 1508951 2263919 := bstep (se 1 (by rfl) ⟨1697939, by rfl⟩ : syracuseStep 2263919 = 3395879) B3395879
theorem B1510335 : Blo 1508951 1510335 := bstep (se 1 (by rfl) ⟨1132751, by rfl⟩ : syracuseStep 1510335 = 2265503) B2265503
theorem B6450283 : Blo 1508951 6450283 := bstep (se 1 (by rfl) ⟨4837712, by rfl⟩ : syracuseStep 6450283 = 9675425) B9675425
theorem B2264255 : Blo 1508951 2264255 := bstep (se 1 (by rfl) ⟨1698191, by rfl⟩ : syracuseStep 2264255 = 3396383) B3396383
theorem B1510607 : Blo 1508951 1510607 := bstep (se 1 (by rfl) ⟨1132955, by rfl⟩ : syracuseStep 1510607 = 2265911) B2265911
theorem B2264423 : Blo 1508951 2264423 := bstep (se 1 (by rfl) ⟨1698317, by rfl⟩ : syracuseStep 2264423 = 3396635) B3396635
theorem B1699375 : Blo 1508951 1699375 := bstep (se 1 (by rfl) ⟨1274531, by rfl⟩ : syracuseStep 1699375 = 2549063) B2549063
theorem B2264687 : Blo 1508951 2264687 := bstep (se 1 (by rfl) ⟨1698515, by rfl⟩ : syracuseStep 2264687 = 3397031) B3397031
theorem B2264795 : Blo 1508951 2264795 := bstep (se 1 (by rfl) ⟨1698596, by rfl⟩ : syracuseStep 2264795 = 3397193) B3397193
theorem B6123251 : Blo 1508951 6123251 := bstep (se 1 (by rfl) ⟨4592438, by rfl⟩ : syracuseStep 6123251 = 9184877) B9184877
theorem B7647209 : Blo 1508951 7647209 := bstep (se 2 (by rfl) ⟨2867703, by rfl⟩ : syracuseStep 7647209 = 5735407) B5735407
theorem B7253995 : Blo 1508951 7253995 := bstep (se 1 (by rfl) ⟨5440496, by rfl⟩ : syracuseStep 7253995 = 10880993) B10880993
theorem B2265575 : Blo 1508951 2265575 := bstep (se 1 (by rfl) ⟨1699181, by rfl⟩ : syracuseStep 2265575 = 3398363) B3398363
theorem B3396239 : Blo 1508951 3396239 := bstep (se 1 (by rfl) ⟨2547179, by rfl⟩ : syracuseStep 3396239 = 5094359) B5094359
theorem B2265791 : Blo 1508951 2265791 := bstep (se 1 (by rfl) ⟨1699343, by rfl⟩ : syracuseStep 2265791 = 3398687) B3398687
theorem B9679783 : Blo 1508951 9679783 := bstep (se 1 (by rfl) ⟨7259837, by rfl⟩ : syracuseStep 9679783 = 14519675) B14519675
theorem B2266091 : Blo 1508951 2266091 := bstep (se 1 (by rfl) ⟨1699568, by rfl⟩ : syracuseStep 2266091 = 3399137) B3399137
theorem B5092847 : Blo 1508951 5092847 := bstep (se 1 (by rfl) ⟨3819635, by rfl⟩ : syracuseStep 5092847 = 7639271) B7639271
theorem B6452729 : Blo 1508951 6452729 := bstep (se 2 (by rfl) ⟨2419773, by rfl⟩ : syracuseStep 6452729 = 4839547) B4839547
theorem B1611623 : Blo 1508951 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B21772475 : Blo 1508951 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B69761321 : Blo 1508951 69761321 := bstep (se 2 (by rfl) ⟨26160495, by rfl⟩ : syracuseStep 69761321 = 52320991) B52320991
theorem B3873145 : Blo 1508951 3873145 := bstep (se 2 (by rfl) ⟨1452429, by rfl⟩ : syracuseStep 3873145 = 2904859) B2904859
theorem B5732795 : Blo 1508951 5732795 := bstep (se 1 (by rfl) ⟨4299596, by rfl⟩ : syracuseStep 5732795 = 8599193) B8599193
theorem B3062591 : Blo 1508951 3062591 := bstep (se 1 (by rfl) ⟨2296943, by rfl⟩ : syracuseStep 3062591 = 4593887) B4593887
theorem B25148231 : Blo 1508951 25148231 := bstep (se 1 (by rfl) ⟨18861173, by rfl⟩ : syracuseStep 25148231 = 37722347) B37722347
theorem B2866367 : Blo 1508951 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B3399119 : Blo 1508951 3399119 := bstep (se 1 (by rfl) ⟨2549339, by rfl⟩ : syracuseStep 3399119 = 5098679) B5098679
theorem B2547247 : Blo 1508951 2547247 := bstep (se 1 (by rfl) ⟨1910435, by rfl⟩ : syracuseStep 2547247 = 3820871) B3820871
theorem B4079225 : Blo 1508951 4079225 := bstep (se 2 (by rfl) ⟨1529709, by rfl⟩ : syracuseStep 4079225 = 3059419) B3059419
theorem B1004674859 : Blo 1508951 1004674859 := bstep (se 1 (by rfl) ⟨753506144, by rfl⟩ : syracuseStep 1004674859 = 1507012289) B1507012289
theorem B7643645 : Blo 1508951 7643645 := bstep (se 3 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 7643645 = 2866367) B2866367
theorem B11469599 : Blo 1508951 11469599 := bstep (se 1 (by rfl) ⟨8602199, by rfl⟩ : syracuseStep 11469599 = 17204399) B17204399
theorem B4301819 : Blo 1508951 4301819 := bstep (se 1 (by rfl) ⟨3226364, by rfl⟩ : syracuseStep 4301819 = 6452729) B6452729
theorem B46507547 : Blo 1508951 46507547 := bstep (se 1 (by rfl) ⟨34880660, by rfl⟩ : syracuseStep 46507547 = 69761321) B69761321
theorem B1509023 : Blo 1508951 1509023 := bstep (se 1 (by rfl) ⟨1131767, by rfl⟩ : syracuseStep 1509023 = 2263535) B2263535
theorem B4835047 : Blo 1508951 4835047 := bstep (se 1 (by rfl) ⟨3626285, by rfl⟩ : syracuseStep 4835047 = 7252571) B7252571
theorem B2041727 : Blo 1508951 2041727 := bstep (se 1 (by rfl) ⟨1531295, by rfl⟩ : syracuseStep 2041727 = 3062591) B3062591
theorem B1509279 : Blo 1508951 1509279 := bstep (se 1 (by rfl) ⟨1131959, by rfl⟩ : syracuseStep 1509279 = 2263919) B2263919
theorem B1509503 : Blo 1508951 1509503 := bstep (se 1 (by rfl) ⟨1132127, by rfl⟩ : syracuseStep 1509503 = 2264255) B2264255
theorem B1509615 : Blo 1508951 1509615 := bstep (se 1 (by rfl) ⟨1132211, by rfl⟩ : syracuseStep 1509615 = 2264423) B2264423
theorem B1509791 : Blo 1508951 1509791 := bstep (se 1 (by rfl) ⟨1132343, by rfl⟩ : syracuseStep 1509791 = 2264687) B2264687
theorem B5736865 : Blo 1508951 5736865 := bstep (se 2 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 5736865 = 4302649) B4302649
theorem B1509863 : Blo 1508951 1509863 := bstep (se 1 (by rfl) ⟨1132397, by rfl⟩ : syracuseStep 1509863 = 2264795) B2264795
theorem B4082167 : Blo 1508951 4082167 := bstep (se 1 (by rfl) ⟨3061625, by rfl⟩ : syracuseStep 4082167 = 6123251) B6123251
theorem B5098139 : Blo 1508951 5098139 := bstep (se 1 (by rfl) ⟨3823604, by rfl⟩ : syracuseStep 5098139 = 7647209) B7647209
theorem B1698511 : Blo 1508951 1698511 := bstep (se 1 (by rfl) ⟨1273883, by rfl⟩ : syracuseStep 1698511 = 2547767) B2547767
theorem B6450131 : Blo 1508951 6450131 := bstep (se 1 (by rfl) ⟨4837598, by rfl⟩ : syracuseStep 6450131 = 9675197) B9675197
theorem B1510383 : Blo 1508951 1510383 := bstep (se 1 (by rfl) ⟨1132787, by rfl⟩ : syracuseStep 1510383 = 2265575) B2265575
theorem B2264159 : Blo 1508951 2264159 := bstep (se 1 (by rfl) ⟨1698119, by rfl⟩ : syracuseStep 2264159 = 3396239) B3396239
theorem B1698943 : Blo 1508951 1698943 := bstep (se 1 (by rfl) ⟨1274207, by rfl⟩ : syracuseStep 1698943 = 2548415) B2548415
theorem B1510527 : Blo 1508951 1510527 := bstep (se 1 (by rfl) ⟨1132895, by rfl⟩ : syracuseStep 1510527 = 2265791) B2265791
theorem B2264201 : Blo 1508951 2264201 := bstep (se 2 (by rfl) ⟨849075, by rfl⟩ : syracuseStep 2264201 = 1698151) B1698151
theorem B5164193 : Blo 1508951 5164193 := bstep (se 2 (by rfl) ⟨1936572, by rfl⟩ : syracuseStep 5164193 = 3873145) B3873145
theorem B1510727 : Blo 1508951 1510727 := bstep (se 1 (by rfl) ⟨1133045, by rfl⟩ : syracuseStep 1510727 = 2266091) B2266091
theorem B3395231 : Blo 1508951 3395231 := bstep (se 1 (by rfl) ⟨2546423, by rfl⟩ : syracuseStep 3395231 = 5092847) B5092847
theorem B12906377 : Blo 1508951 12906377 := bstep (se 2 (by rfl) ⟨4839891, by rfl⟩ : syracuseStep 12906377 = 9679783) B9679783
theorem B13070483 : Blo 1508951 13070483 := bstep (se 1 (by rfl) ⟨9802862, by rfl⟩ : syracuseStep 13070483 = 19605725) B19605725
theorem B3821863 : Blo 1508951 3821863 := bstep (se 1 (by rfl) ⟨2866397, by rfl⟩ : syracuseStep 3821863 = 5732795) B5732795
theorem B16765487 : Blo 1508951 16765487 := bstep (se 1 (by rfl) ⟨12574115, by rfl⟩ : syracuseStep 16765487 = 25148231) B25148231
theorem B3396329 : Blo 1508951 3396329 := bstep (se 2 (by rfl) ⟨1273623, by rfl⟩ : syracuseStep 3396329 = 2547247) B2547247
theorem B2265833 : Blo 1508951 2265833 := bstep (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) B1699375
theorem B4297661 : Blo 1508951 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B2266079 : Blo 1508951 2266079 := bstep (se 1 (by rfl) ⟨1699559, by rfl⟩ : syracuseStep 2266079 = 3399119) B3399119
theorem B669783239 : Blo 1508951 669783239 := bstep (se 1 (by rfl) ⟨502337429, by rfl⟩ : syracuseStep 669783239 = 1004674859) B1004674859
theorem B9671993 : Blo 1508951 9671993 := bstep (se 2 (by rfl) ⟨3626997, by rfl⟩ : syracuseStep 9671993 = 7253995) B7253995
theorem B14514983 : Blo 1508951 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B8600377 : Blo 1508951 8600377 := bstep (se 2 (by rfl) ⟨3225141, by rfl⟩ : syracuseStep 8600377 = 6450283) B6450283
theorem B201284443 : Blo 1508951 201284443 := bstep (se 1 (by rfl) ⟨150963332, by rfl⟩ : syracuseStep 201284443 = 301926665) B301926665
theorem B10877933 : Blo 1508951 10877933 := bstep (se 3 (by rfl) ⟨2039612, by rfl⟩ : syracuseStep 10877933 = 4079225) B4079225
theorem B5095763 : Blo 1508951 5095763 := bstep (se 1 (by rfl) ⟨3821822, by rfl⟩ : syracuseStep 5095763 = 7643645) B7643645
theorem B5095817 : Blo 1508951 5095817 := bstep (se 2 (by rfl) ⟨1910931, by rfl⟩ : syracuseStep 5095817 = 3821863) B3821863
theorem B13771181 : Blo 1508951 13771181 := bstep (se 3 (by rfl) ⟨2582096, by rfl⟩ : syracuseStep 13771181 = 5164193) B5164193
theorem B2867879 : Blo 1508951 2867879 := bstep (se 1 (by rfl) ⟨2150909, by rfl⟩ : syracuseStep 2867879 = 4301819) B4301819
theorem B446522159 : Blo 1508951 446522159 := bstep (se 1 (by rfl) ⟨334891619, by rfl⟩ : syracuseStep 446522159 = 669783239) B669783239
theorem B6447995 : Blo 1508951 6447995 := bstep (se 1 (by rfl) ⟨4835996, by rfl⟩ : syracuseStep 6447995 = 9671993) B9671993
theorem B268379257 : Blo 1508951 268379257 := bstep (se 2 (by rfl) ⟨100642221, by rfl⟩ : syracuseStep 268379257 = 201284443) B201284443
theorem B9676655 : Blo 1508951 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B1509439 : Blo 1508951 1509439 := bstep (se 1 (by rfl) ⟨1132079, by rfl⟩ : syracuseStep 1509439 = 2264159) B2264159
theorem B1509467 : Blo 1508951 1509467 := bstep (se 1 (by rfl) ⟨1132100, by rfl⟩ : syracuseStep 1509467 = 2264201) B2264201
theorem B2263487 : Blo 1508951 2263487 := bstep (se 1 (by rfl) ⟨1697615, by rfl⟩ : syracuseStep 2263487 = 3395231) B3395231
theorem B8604251 : Blo 1508951 8604251 := bstep (se 1 (by rfl) ⟨6453188, by rfl⟩ : syracuseStep 8604251 = 12906377) B12906377
theorem B11176991 : Blo 1508951 11176991 := bstep (se 1 (by rfl) ⟨8382743, by rfl⟩ : syracuseStep 11176991 = 16765487) B16765487
theorem B2264219 : Blo 1508951 2264219 := bstep (se 1 (by rfl) ⟨1698164, by rfl⟩ : syracuseStep 2264219 = 3396329) B3396329
theorem B1510555 : Blo 1508951 1510555 := bstep (se 1 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 1510555 = 2265833) B2265833
theorem B7646399 : Blo 1508951 7646399 := bstep (se 1 (by rfl) ⟨5734799, by rfl⟩ : syracuseStep 7646399 = 11469599) B11469599
theorem B1510719 : Blo 1508951 1510719 := bstep (se 1 (by rfl) ⟨1133039, by rfl⟩ : syracuseStep 1510719 = 2266079) B2266079
theorem B5442889 : Blo 1508951 5442889 := bstep (se 2 (by rfl) ⟨2041083, by rfl⟩ : syracuseStep 5442889 = 4082167) B4082167
theorem B2264681 : Blo 1508951 2264681 := bstep (se 2 (by rfl) ⟨849255, by rfl⟩ : syracuseStep 2264681 = 1698511) B1698511
theorem B2265257 : Blo 1508951 2265257 := bstep (se 2 (by rfl) ⟨849471, by rfl⟩ : syracuseStep 2265257 = 1698943) B1698943
theorem B5444605 : Blo 1508951 5444605 := bstep (se 3 (by rfl) ⟨1020863, by rfl⟩ : syracuseStep 5444605 = 2041727) B2041727
theorem B8713655 : Blo 1508951 8713655 := bstep (se 1 (by rfl) ⟨6535241, by rfl⟩ : syracuseStep 8713655 = 13070483) B13070483
theorem B7649153 : Blo 1508951 7649153 := bstep (se 2 (by rfl) ⟨2868432, by rfl⟩ : syracuseStep 7649153 = 5736865) B5736865
theorem B2865107 : Blo 1508951 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B31005031 : Blo 1508951 31005031 := bstep (se 1 (by rfl) ⟨23253773, by rfl⟩ : syracuseStep 31005031 = 46507547) B46507547
theorem B11467169 : Blo 1508951 11467169 := bstep (se 2 (by rfl) ⟨4300188, by rfl⟩ : syracuseStep 11467169 = 8600377) B8600377
theorem B3398759 : Blo 1508951 3398759 := bstep (se 1 (by rfl) ⟨2549069, by rfl⟩ : syracuseStep 3398759 = 5098139) B5098139
theorem B4300087 : Blo 1508951 4300087 := bstep (se 1 (by rfl) ⟨3225065, by rfl⟩ : syracuseStep 4300087 = 6450131) B6450131
theorem B6446729 : Blo 1508951 6446729 := bstep (se 2 (by rfl) ⟨2417523, by rfl⟩ : syracuseStep 6446729 = 4835047) B4835047
theorem B29007821 : Blo 1508951 29007821 := bstep (se 3 (by rfl) ⟨5438966, by rfl⟩ : syracuseStep 29007821 = 10877933) B10877933
theorem B297681439 : Blo 1508951 297681439 := bstep (se 1 (by rfl) ⟨223261079, by rfl⟩ : syracuseStep 297681439 = 446522159) B446522159
theorem B5809103 : Blo 1508951 5809103 := bstep (se 1 (by rfl) ⟨4356827, by rfl⟩ : syracuseStep 5809103 = 8713655) B8713655
theorem B1910071 : Blo 1508951 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B7259473 : Blo 1508951 7259473 := bstep (se 2 (by rfl) ⟨2722302, by rfl⟩ : syracuseStep 7259473 = 5444605) B5444605
theorem B7644779 : Blo 1508951 7644779 := bstep (se 1 (by rfl) ⟨5733584, by rfl⟩ : syracuseStep 7644779 = 11467169) B11467169
theorem B1508991 : Blo 1508951 1508991 := bstep (se 1 (by rfl) ⟨1131743, by rfl⟩ : syracuseStep 1508991 = 2263487) B2263487
theorem B5736167 : Blo 1508951 5736167 := bstep (se 1 (by rfl) ⟨4302125, by rfl⟩ : syracuseStep 5736167 = 8604251) B8604251
theorem B1509479 : Blo 1508951 1509479 := bstep (se 1 (by rfl) ⟨1132109, by rfl⟩ : syracuseStep 1509479 = 2264219) B2264219
theorem B5097599 : Blo 1508951 5097599 := bstep (se 1 (by rfl) ⟨3823199, by rfl⟩ : syracuseStep 5097599 = 7646399) B7646399
theorem B1509787 : Blo 1508951 1509787 := bstep (se 1 (by rfl) ⟨1132340, by rfl⟩ : syracuseStep 1509787 = 2264681) B2264681
theorem B1510171 : Blo 1508951 1510171 := bstep (se 1 (by rfl) ⟨1132628, by rfl⟩ : syracuseStep 1510171 = 2265257) B2265257
theorem B1911919 : Blo 1508951 1911919 := bstep (se 1 (by rfl) ⟨1433939, by rfl⟩ : syracuseStep 1911919 = 2867879) B2867879
theorem B41340041 : Blo 1508951 41340041 := bstep (se 2 (by rfl) ⟨15502515, by rfl⟩ : syracuseStep 41340041 = 31005031) B31005031
theorem B6451103 : Blo 1508951 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B5099435 : Blo 1508951 5099435 := bstep (se 1 (by rfl) ⟨3824576, by rfl⟩ : syracuseStep 5099435 = 7649153) B7649153
theorem B357839009 : Blo 1508951 357839009 := bstep (se 2 (by rfl) ⟨134189628, by rfl⟩ : syracuseStep 357839009 = 268379257) B268379257
theorem B17191277 : Blo 1508951 17191277 := bstep (se 3 (by rfl) ⟨3223364, by rfl⟩ : syracuseStep 17191277 = 6446729) B6446729
theorem B7451327 : Blo 1508951 7451327 := bstep (se 1 (by rfl) ⟨5588495, by rfl⟩ : syracuseStep 7451327 = 11176991) B11176991
theorem B2265839 : Blo 1508951 2265839 := bstep (se 1 (by rfl) ⟨1699379, by rfl⟩ : syracuseStep 2265839 = 3398759) B3398759
theorem B19338547 : Blo 1508951 19338547 := bstep (se 1 (by rfl) ⟨14503910, by rfl⟩ : syracuseStep 19338547 = 29007821) B29007821
theorem B3397175 : Blo 1508951 3397175 := bstep (se 1 (by rfl) ⟨2547881, by rfl⟩ : syracuseStep 3397175 = 5095763) B5095763
theorem B3397211 : Blo 1508951 3397211 := bstep (se 1 (by rfl) ⟨2547908, by rfl⟩ : syracuseStep 3397211 = 5095817) B5095817
theorem B9180787 : Blo 1508951 9180787 := bstep (se 1 (by rfl) ⟨6885590, by rfl⟩ : syracuseStep 9180787 = 13771181) B13771181
theorem B4298663 : Blo 1508951 4298663 := bstep (se 1 (by rfl) ⟨3223997, by rfl⟩ : syracuseStep 4298663 = 6447995) B6447995
theorem B5733449 : Blo 1508951 5733449 := bstep (se 2 (by rfl) ⟨2150043, by rfl⟩ : syracuseStep 5733449 = 4300087) B4300087
theorem B7257185 : Blo 1508951 7257185 := bstep (se 2 (by rfl) ⟨2721444, by rfl⟩ : syracuseStep 7257185 = 5442889) B5442889
theorem B238559339 : Blo 1508951 238559339 := bstep (se 1 (by rfl) ⟨178919504, by rfl⟩ : syracuseStep 238559339 = 357839009) B357839009
theorem B11460851 : Blo 1508951 11460851 := bstep (se 1 (by rfl) ⟨8595638, by rfl⟩ : syracuseStep 11460851 = 17191277) B17191277
theorem B5096519 : Blo 1508951 5096519 := bstep (se 1 (by rfl) ⟨3822389, by rfl⟩ : syracuseStep 5096519 = 7644779) B7644779
theorem B2549225 : Blo 1508951 2549225 := bstep (se 2 (by rfl) ⟨955959, by rfl⟩ : syracuseStep 2549225 = 1911919) B1911919
theorem B27560027 : Blo 1508951 27560027 := bstep (se 1 (by rfl) ⟨20670020, by rfl⟩ : syracuseStep 27560027 = 41340041) B41340041
theorem B12241049 : Blo 1508951 12241049 := bstep (se 2 (by rfl) ⟨4590393, by rfl⟩ : syracuseStep 12241049 = 9180787) B9180787
theorem B1510559 : Blo 1508951 1510559 := bstep (se 1 (by rfl) ⟨1132919, by rfl⟩ : syracuseStep 1510559 = 2265839) B2265839
theorem B2264783 : Blo 1508951 2264783 := bstep (se 1 (by rfl) ⟨1698587, by rfl⟩ : syracuseStep 2264783 = 3397175) B3397175
theorem B2264807 : Blo 1508951 2264807 := bstep (se 1 (by rfl) ⟨1698605, by rfl⟩ : syracuseStep 2264807 = 3397211) B3397211
theorem B25784729 : Blo 1508951 25784729 := bstep (se 2 (by rfl) ⟨9669273, by rfl⟩ : syracuseStep 25784729 = 19338547) B19338547
theorem B9679297 : Blo 1508951 9679297 := bstep (se 2 (by rfl) ⟨3629736, by rfl⟩ : syracuseStep 9679297 = 7259473) B7259473
theorem B19870205 : Blo 1508951 19870205 := bstep (se 3 (by rfl) ⟨3725663, by rfl⟩ : syracuseStep 19870205 = 7451327) B7451327
theorem B3822299 : Blo 1508951 3822299 := bstep (se 1 (by rfl) ⟨2866724, by rfl⟩ : syracuseStep 3822299 = 5733449) B5733449
theorem B4838123 : Blo 1508951 4838123 := bstep (se 1 (by rfl) ⟨3628592, by rfl⟩ : syracuseStep 4838123 = 7257185) B7257185
theorem B3872735 : Blo 1508951 3872735 := bstep (se 1 (by rfl) ⟨2904551, by rfl⟩ : syracuseStep 3872735 = 5809103) B5809103
theorem B396908585 : Blo 1508951 396908585 := bstep (se 2 (by rfl) ⟨148840719, by rfl⟩ : syracuseStep 396908585 = 297681439) B297681439
theorem B3824111 : Blo 1508951 3824111 := bstep (se 1 (by rfl) ⟨2868083, by rfl⟩ : syracuseStep 3824111 = 5736167) B5736167
theorem B2865775 : Blo 1508951 2865775 := bstep (se 1 (by rfl) ⟨2149331, by rfl⟩ : syracuseStep 2865775 = 4298663) B4298663
theorem B3398399 : Blo 1508951 3398399 := bstep (se 1 (by rfl) ⟨2548799, by rfl⟩ : syracuseStep 3398399 = 5097599) B5097599
theorem B2546761 : Blo 1508951 2546761 := bstep (se 2 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 2546761 = 1910071) B1910071
theorem B17202941 : Blo 1508951 17202941 := bstep (se 3 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 17202941 = 6451103) B6451103
theorem B3399623 : Blo 1508951 3399623 := bstep (se 1 (by rfl) ⟨2549717, by rfl⟩ : syracuseStep 3399623 = 5099435) B5099435
theorem B159039559 : Blo 1508951 159039559 := bstep (se 1 (by rfl) ⟨119279669, by rfl⟩ : syracuseStep 159039559 = 238559339) B238559339
theorem B2548199 : Blo 1508951 2548199 := bstep (se 1 (by rfl) ⟨1911149, by rfl⟩ : syracuseStep 2548199 = 3822299) B3822299
theorem B2581823 : Blo 1508951 2581823 := bstep (se 1 (by rfl) ⟨1936367, by rfl⟩ : syracuseStep 2581823 = 3872735) B3872735
theorem B52987213 : Blo 1508951 52987213 := bstep (se 3 (by rfl) ⟨9935102, by rfl⟩ : syracuseStep 52987213 = 19870205) B19870205
theorem B2549407 : Blo 1508951 2549407 := bstep (se 1 (by rfl) ⟨1912055, by rfl⟩ : syracuseStep 2549407 = 3824111) B3824111
theorem B1509855 : Blo 1508951 1509855 := bstep (se 1 (by rfl) ⟨1132391, by rfl⟩ : syracuseStep 1509855 = 2264783) B2264783
theorem B1509871 : Blo 1508951 1509871 := bstep (se 1 (by rfl) ⟨1132403, by rfl⟩ : syracuseStep 1509871 = 2264807) B2264807
theorem B73493405 : Blo 1508951 73493405 := bstep (se 3 (by rfl) ⟨13780013, by rfl⟩ : syracuseStep 73493405 = 27560027) B27560027
theorem B17189819 : Blo 1508951 17189819 := bstep (se 1 (by rfl) ⟨12892364, by rfl⟩ : syracuseStep 17189819 = 25784729) B25784729
theorem B12905729 : Blo 1508951 12905729 := bstep (se 2 (by rfl) ⟨4839648, by rfl⟩ : syracuseStep 12905729 = 9679297) B9679297
theorem B3821033 : Blo 1508951 3821033 := bstep (se 2 (by rfl) ⟨1432887, by rfl⟩ : syracuseStep 3821033 = 2865775) B2865775
theorem B1699483 : Blo 1508951 1699483 := bstep (se 1 (by rfl) ⟨1274612, by rfl⟩ : syracuseStep 1699483 = 2549225) B2549225
theorem B264605723 : Blo 1508951 264605723 := bstep (se 1 (by rfl) ⟨198454292, by rfl⟩ : syracuseStep 264605723 = 396908585) B396908585
theorem B3395681 : Blo 1508951 3395681 := bstep (se 2 (by rfl) ⟨1273380, by rfl⟩ : syracuseStep 3395681 = 2546761) B2546761
theorem B2265599 : Blo 1508951 2265599 := bstep (se 1 (by rfl) ⟨1699199, by rfl⟩ : syracuseStep 2265599 = 3398399) B3398399
theorem B2266415 : Blo 1508951 2266415 := bstep (se 1 (by rfl) ⟨1699811, by rfl⟩ : syracuseStep 2266415 = 3399623) B3399623
theorem B7640567 : Blo 1508951 7640567 := bstep (se 1 (by rfl) ⟨5730425, by rfl⟩ : syracuseStep 7640567 = 11460851) B11460851
theorem B32642797 : Blo 1508951 32642797 := bstep (se 3 (by rfl) ⟨6120524, by rfl⟩ : syracuseStep 32642797 = 12241049) B12241049
theorem B3225415 : Blo 1508951 3225415 := bstep (se 1 (by rfl) ⟨2419061, by rfl⟩ : syracuseStep 3225415 = 4838123) B4838123
theorem B3397679 : Blo 1508951 3397679 := bstep (se 1 (by rfl) ⟨2548259, by rfl⟩ : syracuseStep 3397679 = 5096519) B5096519
theorem B11468627 : Blo 1508951 11468627 := bstep (se 1 (by rfl) ⟨8601470, by rfl⟩ : syracuseStep 11468627 = 17202941) B17202941
theorem B1721215 : Blo 1508951 1721215 := bstep (se 1 (by rfl) ⟨1290911, by rfl⟩ : syracuseStep 1721215 = 2581823) B2581823
theorem B8603819 : Blo 1508951 8603819 := bstep (se 1 (by rfl) ⟨6452864, by rfl⟩ : syracuseStep 8603819 = 12905729) B12905729
theorem B7645751 : Blo 1508951 7645751 := bstep (se 1 (by rfl) ⟨5734313, by rfl⟩ : syracuseStep 7645751 = 11468627) B11468627
theorem B2263787 : Blo 1508951 2263787 := bstep (se 1 (by rfl) ⟨1697840, by rfl⟩ : syracuseStep 2263787 = 3395681) B3395681
theorem B212052745 : Blo 1508951 212052745 := bstep (se 2 (by rfl) ⟨79519779, by rfl⟩ : syracuseStep 212052745 = 159039559) B159039559
theorem B1698799 : Blo 1508951 1698799 := bstep (se 1 (by rfl) ⟨1274099, by rfl⟩ : syracuseStep 1698799 = 2548199) B2548199
theorem B1510399 : Blo 1508951 1510399 := bstep (se 1 (by rfl) ⟨1132799, by rfl⟩ : syracuseStep 1510399 = 2265599) B2265599
theorem B1510943 : Blo 1508951 1510943 := bstep (se 1 (by rfl) ⟨1133207, by rfl⟩ : syracuseStep 1510943 = 2266415) B2266415
theorem B2265119 : Blo 1508951 2265119 := bstep (se 1 (by rfl) ⟨1698839, by rfl⟩ : syracuseStep 2265119 = 3397679) B3397679
theorem B2265977 : Blo 1508951 2265977 := bstep (se 2 (by rfl) ⟨849741, by rfl⟩ : syracuseStep 2265977 = 1699483) B1699483
theorem B176403815 : Blo 1508951 176403815 := bstep (se 1 (by rfl) ⟨132302861, by rfl⟩ : syracuseStep 176403815 = 264605723) B264605723
theorem B5093711 : Blo 1508951 5093711 := bstep (se 1 (by rfl) ⟨3820283, by rfl⟩ : syracuseStep 5093711 = 7640567) B7640567
theorem B282598469 : Blo 1508951 282598469 := bstep (se 4 (by rfl) ⟨26493606, by rfl⟩ : syracuseStep 282598469 = 52987213) B52987213
theorem B48995603 : Blo 1508951 48995603 := bstep (se 1 (by rfl) ⟨36746702, by rfl⟩ : syracuseStep 48995603 = 73493405) B73493405
theorem B11459879 : Blo 1508951 11459879 := bstep (se 1 (by rfl) ⟨8594909, by rfl⟩ : syracuseStep 11459879 = 17189819) B17189819
theorem B3399209 : Blo 1508951 3399209 := bstep (se 2 (by rfl) ⟨1274703, by rfl⟩ : syracuseStep 3399209 = 2549407) B2549407
theorem B43523729 : Blo 1508951 43523729 := bstep (se 2 (by rfl) ⟨16321398, by rfl⟩ : syracuseStep 43523729 = 32642797) B32642797
theorem B2547355 : Blo 1508951 2547355 := bstep (se 1 (by rfl) ⟨1910516, by rfl⟩ : syracuseStep 2547355 = 3821033) B3821033
theorem B4300553 : Blo 1508951 4300553 := bstep (se 2 (by rfl) ⟨1612707, by rfl⟩ : syracuseStep 4300553 = 3225415) B3225415
theorem B5735879 : Blo 1508951 5735879 := bstep (se 1 (by rfl) ⟨4301909, by rfl⟩ : syracuseStep 5735879 = 8603819) B8603819
theorem B5097167 : Blo 1508951 5097167 := bstep (se 1 (by rfl) ⟨3822875, by rfl⟩ : syracuseStep 5097167 = 7645751) B7645751
theorem B1509191 : Blo 1508951 1509191 := bstep (se 1 (by rfl) ⟨1131893, by rfl⟩ : syracuseStep 1509191 = 2263787) B2263787
theorem B32663735 : Blo 1508951 32663735 := bstep (se 1 (by rfl) ⟨24497801, by rfl⟩ : syracuseStep 32663735 = 48995603) B48995603
theorem B1510079 : Blo 1508951 1510079 := bstep (se 1 (by rfl) ⟨1132559, by rfl⟩ : syracuseStep 1510079 = 2265119) B2265119
theorem B1510651 : Blo 1508951 1510651 := bstep (se 1 (by rfl) ⟨1132988, by rfl⟩ : syracuseStep 1510651 = 2265977) B2265977
theorem B2265065 : Blo 1508951 2265065 := bstep (se 2 (by rfl) ⟨849399, by rfl⟩ : syracuseStep 2265065 = 1698799) B1698799
theorem B3395807 : Blo 1508951 3395807 := bstep (se 1 (by rfl) ⟨2546855, by rfl⟩ : syracuseStep 3395807 = 5093711) B5093711
theorem B9179813 : Blo 1508951 9179813 := bstep (se 4 (by rfl) ⟨860607, by rfl⟩ : syracuseStep 9179813 = 1721215) B1721215
theorem B7639919 : Blo 1508951 7639919 := bstep (se 1 (by rfl) ⟨5729939, by rfl⟩ : syracuseStep 7639919 = 11459879) B11459879
theorem B3396473 : Blo 1508951 3396473 := bstep (se 2 (by rfl) ⟨1273677, by rfl⟩ : syracuseStep 3396473 = 2547355) B2547355
theorem B2266139 : Blo 1508951 2266139 := bstep (se 1 (by rfl) ⟨1699604, by rfl⟩ : syracuseStep 2266139 = 3399209) B3399209
theorem B117602543 : Blo 1508951 117602543 := bstep (se 1 (by rfl) ⟨88201907, by rfl⟩ : syracuseStep 117602543 = 176403815) B176403815
theorem B282736993 : Blo 1508951 282736993 := bstep (se 2 (by rfl) ⟨106026372, by rfl⟩ : syracuseStep 282736993 = 212052745) B212052745
theorem B11468141 : Blo 1508951 11468141 := bstep (se 3 (by rfl) ⟨2150276, by rfl⟩ : syracuseStep 11468141 = 4300553) B4300553
theorem B188398979 : Blo 1508951 188398979 := bstep (se 1 (by rfl) ⟨141299234, by rfl⟩ : syracuseStep 188398979 = 282598469) B282598469
theorem B29015819 : Blo 1508951 29015819 := bstep (se 1 (by rfl) ⟨21761864, by rfl⟩ : syracuseStep 29015819 = 43523729) B43523729
theorem B21775823 : Blo 1508951 21775823 := bstep (se 1 (by rfl) ⟨16331867, by rfl⟩ : syracuseStep 21775823 = 32663735) B32663735
theorem B24479501 : Blo 1508951 24479501 := bstep (se 3 (by rfl) ⟨4589906, by rfl⟩ : syracuseStep 24479501 = 9179813) B9179813
theorem B7645427 : Blo 1508951 7645427 := bstep (se 1 (by rfl) ⟨5734070, by rfl⟩ : syracuseStep 7645427 = 11468141) B11468141
theorem B19343879 : Blo 1508951 19343879 := bstep (se 1 (by rfl) ⟨14507909, by rfl⟩ : syracuseStep 19343879 = 29015819) B29015819
theorem B1510043 : Blo 1508951 1510043 := bstep (se 1 (by rfl) ⟨1132532, by rfl⟩ : syracuseStep 1510043 = 2265065) B2265065
theorem B2263871 : Blo 1508951 2263871 := bstep (se 1 (by rfl) ⟨1697903, by rfl⟩ : syracuseStep 2263871 = 3395807) B3395807
theorem B376982657 : Blo 1508951 376982657 := bstep (se 2 (by rfl) ⟨141368496, by rfl⟩ : syracuseStep 376982657 = 282736993) B282736993
theorem B2264315 : Blo 1508951 2264315 := bstep (se 1 (by rfl) ⟨1698236, by rfl⟩ : syracuseStep 2264315 = 3396473) B3396473
theorem B1510759 : Blo 1508951 1510759 := bstep (se 1 (by rfl) ⟨1133069, by rfl⟩ : syracuseStep 1510759 = 2266139) B2266139
theorem B78401695 : Blo 1508951 78401695 := bstep (se 1 (by rfl) ⟨58801271, by rfl⟩ : syracuseStep 78401695 = 117602543) B117602543
theorem B5093279 : Blo 1508951 5093279 := bstep (se 1 (by rfl) ⟨3819959, by rfl⟩ : syracuseStep 5093279 = 7639919) B7639919
theorem B3823919 : Blo 1508951 3823919 := bstep (se 1 (by rfl) ⟨2867939, by rfl⟩ : syracuseStep 3823919 = 5735879) B5735879
theorem B3398111 : Blo 1508951 3398111 := bstep (se 1 (by rfl) ⟨2548583, by rfl⟩ : syracuseStep 3398111 = 5097167) B5097167
theorem B125599319 : Blo 1508951 125599319 := bstep (se 1 (by rfl) ⟨94199489, by rfl⟩ : syracuseStep 125599319 = 188398979) B188398979
theorem B14517215 : Blo 1508951 14517215 := bstep (se 1 (by rfl) ⟨10887911, by rfl⟩ : syracuseStep 14517215 = 21775823) B21775823
theorem B5096951 : Blo 1508951 5096951 := bstep (se 1 (by rfl) ⟨3822713, by rfl⟩ : syracuseStep 5096951 = 7645427) B7645427
theorem B2549279 : Blo 1508951 2549279 := bstep (se 1 (by rfl) ⟨1911959, by rfl⟩ : syracuseStep 2549279 = 3823919) B3823919
theorem B12895919 : Blo 1508951 12895919 := bstep (se 1 (by rfl) ⟨9671939, by rfl⟩ : syracuseStep 12895919 = 19343879) B19343879
theorem B1509247 : Blo 1508951 1509247 := bstep (se 1 (by rfl) ⟨1131935, by rfl⟩ : syracuseStep 1509247 = 2263871) B2263871
theorem B1509543 : Blo 1508951 1509543 := bstep (se 1 (by rfl) ⟨1132157, by rfl⟩ : syracuseStep 1509543 = 2264315) B2264315
theorem B83732879 : Blo 1508951 83732879 := bstep (se 1 (by rfl) ⟨62799659, by rfl⟩ : syracuseStep 83732879 = 125599319) B125599319
theorem B3395519 : Blo 1508951 3395519 := bstep (se 1 (by rfl) ⟨2546639, by rfl⟩ : syracuseStep 3395519 = 5093279) B5093279
theorem B2265407 : Blo 1508951 2265407 := bstep (se 1 (by rfl) ⟨1699055, by rfl⟩ : syracuseStep 2265407 = 3398111) B3398111
theorem B65278669 : Blo 1508951 65278669 := bstep (se 3 (by rfl) ⟨12239750, by rfl⟩ : syracuseStep 65278669 = 24479501) B24479501
theorem B104535593 : Blo 1508951 104535593 := bstep (se 2 (by rfl) ⟨39200847, by rfl⟩ : syracuseStep 104535593 = 78401695) B78401695
theorem B251321771 : Blo 1508951 251321771 := bstep (se 1 (by rfl) ⟨188491328, by rfl⟩ : syracuseStep 251321771 = 376982657) B376982657
theorem B69690395 : Blo 1508951 69690395 := bstep (se 1 (by rfl) ⟨52267796, by rfl⟩ : syracuseStep 69690395 = 104535593) B104535593
theorem B55821919 : Blo 1508951 55821919 := bstep (se 1 (by rfl) ⟨41866439, by rfl⟩ : syracuseStep 55821919 = 83732879) B83732879
theorem B2263679 : Blo 1508951 2263679 := bstep (se 1 (by rfl) ⟨1697759, by rfl⟩ : syracuseStep 2263679 = 3395519) B3395519
theorem B1510271 : Blo 1508951 1510271 := bstep (se 1 (by rfl) ⟨1132703, by rfl⟩ : syracuseStep 1510271 = 2265407) B2265407
theorem B9678143 : Blo 1508951 9678143 := bstep (se 1 (by rfl) ⟨7258607, by rfl⟩ : syracuseStep 9678143 = 14517215) B14517215
theorem B1699519 : Blo 1508951 1699519 := bstep (se 1 (by rfl) ⟨1274639, by rfl⟩ : syracuseStep 1699519 = 2549279) B2549279
theorem B8597279 : Blo 1508951 8597279 := bstep (se 1 (by rfl) ⟨6447959, by rfl⟩ : syracuseStep 8597279 = 12895919) B12895919
theorem B167547847 : Blo 1508951 167547847 := bstep (se 1 (by rfl) ⟨125660885, by rfl⟩ : syracuseStep 167547847 = 251321771) B251321771
theorem B87038225 : Blo 1508951 87038225 := bstep (se 2 (by rfl) ⟨32639334, by rfl⟩ : syracuseStep 87038225 = 65278669) B65278669
theorem B3397967 : Blo 1508951 3397967 := bstep (se 1 (by rfl) ⟨2548475, by rfl⟩ : syracuseStep 3397967 = 5096951) B5096951
theorem B223397129 : Blo 1508951 223397129 := bstep (se 2 (by rfl) ⟨83773923, by rfl⟩ : syracuseStep 223397129 = 167547847) B167547847
theorem B58025483 : Blo 1508951 58025483 := bstep (se 1 (by rfl) ⟨43519112, by rfl⟩ : syracuseStep 58025483 = 87038225) B87038225
theorem B1509119 : Blo 1508951 1509119 := bstep (se 1 (by rfl) ⟨1131839, by rfl⟩ : syracuseStep 1509119 = 2263679) B2263679
theorem B46460263 : Blo 1508951 46460263 := bstep (se 1 (by rfl) ⟨34845197, by rfl⟩ : syracuseStep 46460263 = 69690395) B69690395
theorem B2265311 : Blo 1508951 2265311 := bstep (se 1 (by rfl) ⟨1698983, by rfl⟩ : syracuseStep 2265311 = 3397967) B3397967
theorem B74429225 : Blo 1508951 74429225 := bstep (se 2 (by rfl) ⟨27910959, by rfl⟩ : syracuseStep 74429225 = 55821919) B55821919
theorem B6452095 : Blo 1508951 6452095 := bstep (se 1 (by rfl) ⟨4839071, by rfl⟩ : syracuseStep 6452095 = 9678143) B9678143
theorem B2266025 : Blo 1508951 2266025 := bstep (se 2 (by rfl) ⟨849759, by rfl⟩ : syracuseStep 2266025 = 1699519) B1699519
theorem B5731519 : Blo 1508951 5731519 := bstep (se 1 (by rfl) ⟨4298639, by rfl⟩ : syracuseStep 5731519 = 8597279) B8597279
theorem B49619483 : Blo 1508951 49619483 := bstep (se 1 (by rfl) ⟨37214612, by rfl⟩ : syracuseStep 49619483 = 74429225) B74429225
theorem B148931419 : Blo 1508951 148931419 := bstep (se 1 (by rfl) ⟨111698564, by rfl⟩ : syracuseStep 148931419 = 223397129) B223397129
theorem B38683655 : Blo 1508951 38683655 := bstep (se 1 (by rfl) ⟨29012741, by rfl⟩ : syracuseStep 38683655 = 58025483) B58025483
theorem B8602793 : Blo 1508951 8602793 := bstep (se 2 (by rfl) ⟨3226047, by rfl⟩ : syracuseStep 8602793 = 6452095) B6452095
theorem B1510207 : Blo 1508951 1510207 := bstep (se 1 (by rfl) ⟨1132655, by rfl⟩ : syracuseStep 1510207 = 2265311) B2265311
theorem B1510683 : Blo 1508951 1510683 := bstep (se 1 (by rfl) ⟨1133012, by rfl⟩ : syracuseStep 1510683 = 2266025) B2266025
theorem B7642025 : Blo 1508951 7642025 := bstep (se 2 (by rfl) ⟨2865759, by rfl⟩ : syracuseStep 7642025 = 5731519) B5731519
theorem B61947017 : Blo 1508951 61947017 := bstep (se 2 (by rfl) ⟨23230131, by rfl⟩ : syracuseStep 61947017 = 46460263) B46460263
theorem B33079655 : Blo 1508951 33079655 := bstep (se 1 (by rfl) ⟨24809741, by rfl⟩ : syracuseStep 33079655 = 49619483) B49619483
theorem B25789103 : Blo 1508951 25789103 := bstep (se 1 (by rfl) ⟨19341827, by rfl⟩ : syracuseStep 25789103 = 38683655) B38683655
theorem B5735195 : Blo 1508951 5735195 := bstep (se 1 (by rfl) ⟨4301396, by rfl⟩ : syracuseStep 5735195 = 8602793) B8602793
theorem B198575225 : Blo 1508951 198575225 := bstep (se 2 (by rfl) ⟨74465709, by rfl⟩ : syracuseStep 198575225 = 148931419) B148931419
theorem B41298011 : Blo 1508951 41298011 := bstep (se 1 (by rfl) ⟨30973508, by rfl⟩ : syracuseStep 41298011 = 61947017) B61947017
theorem B5094683 : Blo 1508951 5094683 := bstep (se 1 (by rfl) ⟨3821012, by rfl⟩ : syracuseStep 5094683 = 7642025) B7642025
theorem B22053103 : Blo 1508951 22053103 := bstep (se 1 (by rfl) ⟨16539827, by rfl⟩ : syracuseStep 22053103 = 33079655) B33079655
theorem B132383483 : Blo 1508951 132383483 := bstep (se 1 (by rfl) ⟨99287612, by rfl⟩ : syracuseStep 132383483 = 198575225) B198575225
theorem B3396455 : Blo 1508951 3396455 := bstep (se 1 (by rfl) ⟨2547341, by rfl⟩ : syracuseStep 3396455 = 5094683) B5094683
theorem B17192735 : Blo 1508951 17192735 := bstep (se 1 (by rfl) ⟨12894551, by rfl⟩ : syracuseStep 17192735 = 25789103) B25789103
theorem B3823463 : Blo 1508951 3823463 := bstep (se 1 (by rfl) ⟨2867597, by rfl⟩ : syracuseStep 3823463 = 5735195) B5735195
theorem B27532007 : Blo 1508951 27532007 := bstep (se 1 (by rfl) ⟨20649005, by rfl⟩ : syracuseStep 27532007 = 41298011) B41298011
theorem B11461823 : Blo 1508951 11461823 := bstep (se 1 (by rfl) ⟨8596367, by rfl⟩ : syracuseStep 11461823 = 17192735) B17192735
theorem B2548975 : Blo 1508951 2548975 := bstep (se 1 (by rfl) ⟨1911731, by rfl⟩ : syracuseStep 2548975 = 3823463) B3823463
theorem B88255655 : Blo 1508951 88255655 := bstep (se 1 (by rfl) ⟨66191741, by rfl⟩ : syracuseStep 88255655 = 132383483) B132383483
theorem B2264303 : Blo 1508951 2264303 := bstep (se 1 (by rfl) ⟨1698227, by rfl⟩ : syracuseStep 2264303 = 3396455) B3396455
theorem B117616549 : Blo 1508951 117616549 := bstep (se 4 (by rfl) ⟨11026551, by rfl⟩ : syracuseStep 117616549 = 22053103) B22053103
theorem B18354671 : Blo 1508951 18354671 := bstep (se 1 (by rfl) ⟨13766003, by rfl⟩ : syracuseStep 18354671 = 27532007) B27532007
theorem B58837103 : Blo 1508951 58837103 := bstep (se 1 (by rfl) ⟨44127827, by rfl⟩ : syracuseStep 58837103 = 88255655) B88255655
theorem B1509535 : Blo 1508951 1509535 := bstep (se 1 (by rfl) ⟨1132151, by rfl⟩ : syracuseStep 1509535 = 2264303) B2264303
theorem B156822065 : Blo 1508951 156822065 := bstep (se 2 (by rfl) ⟨58808274, by rfl⟩ : syracuseStep 156822065 = 117616549) B117616549
theorem B12236447 : Blo 1508951 12236447 := bstep (se 1 (by rfl) ⟨9177335, by rfl⟩ : syracuseStep 12236447 = 18354671) B18354671
theorem B7641215 : Blo 1508951 7641215 := bstep (se 1 (by rfl) ⟨5730911, by rfl⟩ : syracuseStep 7641215 = 11461823) B11461823
theorem B3398633 : Blo 1508951 3398633 := bstep (se 2 (by rfl) ⟨1274487, by rfl⟩ : syracuseStep 3398633 = 2548975) B2548975
theorem B39224735 : Blo 1508951 39224735 := bstep (se 1 (by rfl) ⟨29418551, by rfl⟩ : syracuseStep 39224735 = 58837103) B58837103
theorem B104548043 : Blo 1508951 104548043 := bstep (se 1 (by rfl) ⟨78411032, by rfl⟩ : syracuseStep 104548043 = 156822065) B156822065
theorem B2265755 : Blo 1508951 2265755 := bstep (se 1 (by rfl) ⟨1699316, by rfl⟩ : syracuseStep 2265755 = 3398633) B3398633
theorem B8157631 : Blo 1508951 8157631 := bstep (se 1 (by rfl) ⟨6118223, by rfl⟩ : syracuseStep 8157631 = 12236447) B12236447
theorem B5094143 : Blo 1508951 5094143 := bstep (se 1 (by rfl) ⟨3820607, by rfl⟩ : syracuseStep 5094143 = 7641215) B7641215
theorem B26149823 : Blo 1508951 26149823 := bstep (se 1 (by rfl) ⟨19612367, by rfl⟩ : syracuseStep 26149823 = 39224735) B39224735
theorem B1510503 : Blo 1508951 1510503 := bstep (se 1 (by rfl) ⟨1132877, by rfl⟩ : syracuseStep 1510503 = 2265755) B2265755
theorem B3396095 : Blo 1508951 3396095 := bstep (se 1 (by rfl) ⟨2547071, by rfl⟩ : syracuseStep 3396095 = 5094143) B5094143
theorem B278794781 : Blo 1508951 278794781 := bstep (se 3 (by rfl) ⟨52274021, by rfl⟩ : syracuseStep 278794781 = 104548043) B104548043
theorem B10876841 : Blo 1508951 10876841 := bstep (se 2 (by rfl) ⟨4078815, by rfl⟩ : syracuseStep 10876841 = 8157631) B8157631
theorem B17433215 : Blo 1508951 17433215 := bstep (se 1 (by rfl) ⟨13074911, by rfl⟩ : syracuseStep 17433215 = 26149823) B26149823
theorem B7251227 : Blo 1508951 7251227 := bstep (se 1 (by rfl) ⟨5438420, by rfl⟩ : syracuseStep 7251227 = 10876841) B10876841
theorem B2264063 : Blo 1508951 2264063 := bstep (se 1 (by rfl) ⟨1698047, by rfl⟩ : syracuseStep 2264063 = 3396095) B3396095
theorem B185863187 : Blo 1508951 185863187 := bstep (se 1 (by rfl) ⟨139397390, by rfl⟩ : syracuseStep 185863187 = 278794781) B278794781
theorem B4834151 : Blo 1508951 4834151 := bstep (se 1 (by rfl) ⟨3625613, by rfl⟩ : syracuseStep 4834151 = 7251227) B7251227
theorem B1509375 : Blo 1508951 1509375 := bstep (se 1 (by rfl) ⟨1132031, by rfl⟩ : syracuseStep 1509375 = 2264063) B2264063
theorem B123908791 : Blo 1508951 123908791 := bstep (se 1 (by rfl) ⟨92931593, by rfl⟩ : syracuseStep 123908791 = 185863187) B185863187
theorem B11622143 : Blo 1508951 11622143 := bstep (se 1 (by rfl) ⟨8716607, by rfl⟩ : syracuseStep 11622143 = 17433215) B17433215
theorem B30992381 : Blo 1508951 30992381 := bstep (se 3 (by rfl) ⟨5811071, by rfl⟩ : syracuseStep 30992381 = 11622143) B11622143
theorem B3222767 : Blo 1508951 3222767 := bstep (se 1 (by rfl) ⟨2417075, by rfl⟩ : syracuseStep 3222767 = 4834151) B4834151
theorem B165211721 : Blo 1508951 165211721 := bstep (se 2 (by rfl) ⟨61954395, by rfl⟩ : syracuseStep 165211721 = 123908791) B123908791
theorem B8594045 : Blo 1508951 8594045 := bstep (se 3 (by rfl) ⟨1611383, by rfl⟩ : syracuseStep 8594045 = 3222767) B3222767
theorem B20661587 : Blo 1508951 20661587 := bstep (se 1 (by rfl) ⟨15496190, by rfl⟩ : syracuseStep 20661587 = 30992381) B30992381
theorem B110141147 : Blo 1508951 110141147 := bstep (se 1 (by rfl) ⟨82605860, by rfl⟩ : syracuseStep 110141147 = 165211721) B165211721
theorem B73427431 : Blo 1508951 73427431 := bstep (se 1 (by rfl) ⟨55070573, by rfl⟩ : syracuseStep 73427431 = 110141147) B110141147
theorem B5729363 : Blo 1508951 5729363 := bstep (se 1 (by rfl) ⟨4297022, by rfl⟩ : syracuseStep 5729363 = 8594045) B8594045
theorem B13774391 : Blo 1508951 13774391 := bstep (se 1 (by rfl) ⟨10330793, by rfl⟩ : syracuseStep 13774391 = 20661587) B20661587
theorem B97903241 : Blo 1508951 97903241 := bstep (se 2 (by rfl) ⟨36713715, by rfl⟩ : syracuseStep 97903241 = 73427431) B73427431
theorem B3819575 : Blo 1508951 3819575 := bstep (se 1 (by rfl) ⟨2864681, by rfl⟩ : syracuseStep 3819575 = 5729363) B5729363
theorem B9182927 : Blo 1508951 9182927 := bstep (se 1 (by rfl) ⟨6887195, by rfl⟩ : syracuseStep 9182927 = 13774391) B13774391
theorem B24487805 : Blo 1508951 24487805 := bstep (se 3 (by rfl) ⟨4591463, by rfl⟩ : syracuseStep 24487805 = 9182927) B9182927
theorem B65268827 : Blo 1508951 65268827 := bstep (se 1 (by rfl) ⟨48951620, by rfl⟩ : syracuseStep 65268827 = 97903241) B97903241
theorem B2546383 : Blo 1508951 2546383 := bstep (se 1 (by rfl) ⟨1909787, by rfl⟩ : syracuseStep 2546383 = 3819575) B3819575
theorem B65300813 : Blo 1508951 65300813 := bstep (se 3 (by rfl) ⟨12243902, by rfl⟩ : syracuseStep 65300813 = 24487805) B24487805
theorem B3395177 : Blo 1508951 3395177 := bstep (se 2 (by rfl) ⟨1273191, by rfl⟩ : syracuseStep 3395177 = 2546383) B2546383
theorem B43512551 : Blo 1508951 43512551 := bstep (se 1 (by rfl) ⟨32634413, by rfl⟩ : syracuseStep 43512551 = 65268827) B65268827
theorem B29008367 : Blo 1508951 29008367 := bstep (se 1 (by rfl) ⟨21756275, by rfl⟩ : syracuseStep 29008367 = 43512551) B43512551
theorem B43533875 : Blo 1508951 43533875 := bstep (se 1 (by rfl) ⟨32650406, by rfl⟩ : syracuseStep 43533875 = 65300813) B65300813
theorem B2263451 : Blo 1508951 2263451 := bstep (se 1 (by rfl) ⟨1697588, by rfl⟩ : syracuseStep 2263451 = 3395177) B3395177
theorem B1508967 : Blo 1508951 1508967 := bstep (se 1 (by rfl) ⟨1131725, by rfl⟩ : syracuseStep 1508967 = 2263451) B2263451
theorem B19338911 : Blo 1508951 19338911 := bstep (se 1 (by rfl) ⟨14504183, by rfl⟩ : syracuseStep 19338911 = 29008367) B29008367
theorem B29022583 : Blo 1508951 29022583 := bstep (se 1 (by rfl) ⟨21766937, by rfl⟩ : syracuseStep 29022583 = 43533875) B43533875
theorem B38696777 : Blo 1508951 38696777 := bstep (se 2 (by rfl) ⟨14511291, by rfl⟩ : syracuseStep 38696777 = 29022583) B29022583
theorem B12892607 : Blo 1508951 12892607 := bstep (se 1 (by rfl) ⟨9669455, by rfl⟩ : syracuseStep 12892607 = 19338911) B19338911
theorem B25797851 : Blo 1508951 25797851 := bstep (se 1 (by rfl) ⟨19348388, by rfl⟩ : syracuseStep 25797851 = 38696777) B38696777
theorem B8595071 : Blo 1508951 8595071 := bstep (se 1 (by rfl) ⟨6446303, by rfl⟩ : syracuseStep 8595071 = 12892607) B12892607
theorem B17198567 : Blo 1508951 17198567 := bstep (se 1 (by rfl) ⟨12898925, by rfl⟩ : syracuseStep 17198567 = 25797851) B25797851
theorem B5730047 : Blo 1508951 5730047 := bstep (se 1 (by rfl) ⟨4297535, by rfl⟩ : syracuseStep 5730047 = 8595071) B8595071
theorem B3820031 : Blo 1508951 3820031 := bstep (se 1 (by rfl) ⟨2865023, by rfl⟩ : syracuseStep 3820031 = 5730047) B5730047
theorem B11465711 : Blo 1508951 11465711 := bstep (se 1 (by rfl) ⟨8599283, by rfl⟩ : syracuseStep 11465711 = 17198567) B17198567
theorem B7643807 : Blo 1508951 7643807 := bstep (se 1 (by rfl) ⟨5732855, by rfl⟩ : syracuseStep 7643807 = 11465711) B11465711
theorem B2546687 : Blo 1508951 2546687 := bstep (se 1 (by rfl) ⟨1910015, by rfl⟩ : syracuseStep 2546687 = 3820031) B3820031
theorem B5095871 : Blo 1508951 5095871 := bstep (se 1 (by rfl) ⟨3821903, by rfl⟩ : syracuseStep 5095871 = 7643807) B7643807
theorem B1697791 : Blo 1508951 1697791 := bstep (se 1 (by rfl) ⟨1273343, by rfl⟩ : syracuseStep 1697791 = 2546687) B2546687
theorem B2263721 : Blo 1508951 2263721 := bstep (se 2 (by rfl) ⟨848895, by rfl⟩ : syracuseStep 2263721 = 1697791) B1697791
theorem B3397247 : Blo 1508951 3397247 := bstep (se 1 (by rfl) ⟨2547935, by rfl⟩ : syracuseStep 3397247 = 5095871) B5095871
theorem B1509147 : Blo 1508951 1509147 := bstep (se 1 (by rfl) ⟨1131860, by rfl⟩ : syracuseStep 1509147 = 2263721) B2263721
theorem B2264831 : Blo 1508951 2264831 := bstep (se 1 (by rfl) ⟨1698623, by rfl⟩ : syracuseStep 2264831 = 3397247) B3397247
theorem B1509887 : Blo 1508951 1509887 := bstep (se 1 (by rfl) ⟨1132415, by rfl⟩ : syracuseStep 1509887 = 2264831) B2264831

theorem C0 (j : ℕ) (h1 : 377237 ≤ j) (h2 : j ≤ 377737) : Blo 1508951 (4 * j + 3) := by
  interval_cases j
  · exact B1508951
  · exact B1508955
  · exact B1508959
  · exact B1508963
  · exact B1508967
  · exact B1508971
  · exact B1508975
  · exact B1508979
  · exact B1508983
  · exact B1508987
  · exact B1508991
  · exact B1508995
  · exact B1508999
  · exact B1509003
  · exact B1509007
  · exact B1509011
  · exact B1509015
  · exact B1509019
  · exact B1509023
  · exact B1509027
  · exact B1509031
  · exact B1509035
  · exact B1509039
  · exact B1509043
  · exact B1509047
  · exact B1509051
  · exact B1509055
  · exact B1509059
  · exact B1509063
  · exact B1509067
  · exact B1509071
  · exact B1509075
  · exact B1509079
  · exact B1509083
  · exact B1509087
  · exact B1509091
  · exact B1509095
  · exact B1509099
  · exact B1509103
  · exact B1509107
  · exact B1509111
  · exact B1509115
  · exact B1509119
  · exact B1509123
  · exact B1509127
  · exact B1509131
  · exact B1509135
  · exact B1509139
  · exact B1509143
  · exact B1509147
  · exact B1509151
  · exact B1509155
  · exact B1509159
  · exact B1509163
  · exact B1509167
  · exact B1509171
  · exact B1509175
  · exact B1509179
  · exact B1509183
  · exact B1509187
  · exact B1509191
  · exact B1509195
  · exact B1509199
  · exact B1509203
  · exact B1509207
  · exact B1509211
  · exact B1509215
  · exact B1509219
  · exact B1509223
  · exact B1509227
  · exact B1509231
  · exact B1509235
  · exact B1509239
  · exact B1509243
  · exact B1509247
  · exact B1509251
  · exact B1509255
  · exact B1509259
  · exact B1509263
  · exact B1509267
  · exact B1509271
  · exact B1509275
  · exact B1509279
  · exact B1509283
  · exact B1509287
  · exact B1509291
  · exact B1509295
  · exact B1509299
  · exact B1509303
  · exact B1509307
  · exact B1509311
  · exact B1509315
  · exact B1509319
  · exact B1509323
  · exact B1509327
  · exact B1509331
  · exact B1509335
  · exact B1509339
  · exact B1509343
  · exact B1509347
  · exact B1509351
  · exact B1509355
  · exact B1509359
  · exact B1509363
  · exact B1509367
  · exact B1509371
  · exact B1509375
  · exact B1509379
  · exact B1509383
  · exact B1509387
  · exact B1509391
  · exact B1509395
  · exact B1509399
  · exact B1509403
  · exact B1509407
  · exact B1509411
  · exact B1509415
  · exact B1509419
  · exact B1509423
  · exact B1509427
  · exact B1509431
  · exact B1509435
  · exact B1509439
  · exact B1509443
  · exact B1509447
  · exact B1509451
  · exact B1509455
  · exact B1509459
  · exact B1509463
  · exact B1509467
  · exact B1509471
  · exact B1509475
  · exact B1509479
  · exact B1509483
  · exact B1509487
  · exact B1509491
  · exact B1509495
  · exact B1509499
  · exact B1509503
  · exact B1509507
  · exact B1509511
  · exact B1509515
  · exact B1509519
  · exact B1509523
  · exact B1509527
  · exact B1509531
  · exact B1509535
  · exact B1509539
  · exact B1509543
  · exact B1509547
  · exact B1509551
  · exact B1509555
  · exact B1509559
  · exact B1509563
  · exact B1509567
  · exact B1509571
  · exact B1509575
  · exact B1509579
  · exact B1509583
  · exact B1509587
  · exact B1509591
  · exact B1509595
  · exact B1509599
  · exact B1509603
  · exact B1509607
  · exact B1509611
  · exact B1509615
  · exact B1509619
  · exact B1509623
  · exact B1509627
  · exact B1509631
  · exact B1509635
  · exact B1509639
  · exact B1509643
  · exact B1509647
  · exact B1509651
  · exact B1509655
  · exact B1509659
  · exact B1509663
  · exact B1509667
  · exact B1509671
  · exact B1509675
  · exact B1509679
  · exact B1509683
  · exact B1509687
  · exact B1509691
  · exact B1509695
  · exact B1509699
  · exact B1509703
  · exact B1509707
  · exact B1509711
  · exact B1509715
  · exact B1509719
  · exact B1509723
  · exact B1509727
  · exact B1509731
  · exact B1509735
  · exact B1509739
  · exact B1509743
  · exact B1509747
  · exact B1509751
  · exact B1509755
  · exact B1509759
  · exact B1509763
  · exact B1509767
  · exact B1509771
  · exact B1509775
  · exact B1509779
  · exact B1509783
  · exact B1509787
  · exact B1509791
  · exact B1509795
  · exact B1509799
  · exact B1509803
  · exact B1509807
  · exact B1509811
  · exact B1509815
  · exact B1509819
  · exact B1509823
  · exact B1509827
  · exact B1509831
  · exact B1509835
  · exact B1509839
  · exact B1509843
  · exact B1509847
  · exact B1509851
  · exact B1509855
  · exact B1509859
  · exact B1509863
  · exact B1509867
  · exact B1509871
  · exact B1509875
  · exact B1509879
  · exact B1509883
  · exact B1509887
  · exact B1509891
  · exact B1509895
  · exact B1509899
  · exact B1509903
  · exact B1509907
  · exact B1509911
  · exact B1509915
  · exact B1509919
  · exact B1509923
  · exact B1509927
  · exact B1509931
  · exact B1509935
  · exact B1509939
  · exact B1509943
  · exact B1509947
  · exact B1509951
  · exact B1509955
  · exact B1509959
  · exact B1509963
  · exact B1509967
  · exact B1509971
  · exact B1509975
  · exact B1509979
  · exact B1509983
  · exact B1509987
  · exact B1509991
  · exact B1509995
  · exact B1509999
  · exact B1510003
  · exact B1510007
  · exact B1510011
  · exact B1510015
  · exact B1510019
  · exact B1510023
  · exact B1510027
  · exact B1510031
  · exact B1510035
  · exact B1510039
  · exact B1510043
  · exact B1510047
  · exact B1510051
  · exact B1510055
  · exact B1510059
  · exact B1510063
  · exact B1510067
  · exact B1510071
  · exact B1510075
  · exact B1510079
  · exact B1510083
  · exact B1510087
  · exact B1510091
  · exact B1510095
  · exact B1510099
  · exact B1510103
  · exact B1510107
  · exact B1510111
  · exact B1510115
  · exact B1510119
  · exact B1510123
  · exact B1510127
  · exact B1510131
  · exact B1510135
  · exact B1510139
  · exact B1510143
  · exact B1510147
  · exact B1510151
  · exact B1510155
  · exact B1510159
  · exact B1510163
  · exact B1510167
  · exact B1510171
  · exact B1510175
  · exact B1510179
  · exact B1510183
  · exact B1510187
  · exact B1510191
  · exact B1510195
  · exact B1510199
  · exact B1510203
  · exact B1510207
  · exact B1510211
  · exact B1510215
  · exact B1510219
  · exact B1510223
  · exact B1510227
  · exact B1510231
  · exact B1510235
  · exact B1510239
  · exact B1510243
  · exact B1510247
  · exact B1510251
  · exact B1510255
  · exact B1510259
  · exact B1510263
  · exact B1510267
  · exact B1510271
  · exact B1510275
  · exact B1510279
  · exact B1510283
  · exact B1510287
  · exact B1510291
  · exact B1510295
  · exact B1510299
  · exact B1510303
  · exact B1510307
  · exact B1510311
  · exact B1510315
  · exact B1510319
  · exact B1510323
  · exact B1510327
  · exact B1510331
  · exact B1510335
  · exact B1510339
  · exact B1510343
  · exact B1510347
  · exact B1510351
  · exact B1510355
  · exact B1510359
  · exact B1510363
  · exact B1510367
  · exact B1510371
  · exact B1510375
  · exact B1510379
  · exact B1510383
  · exact B1510387
  · exact B1510391
  · exact B1510395
  · exact B1510399
  · exact B1510403
  · exact B1510407
  · exact B1510411
  · exact B1510415
  · exact B1510419
  · exact B1510423
  · exact B1510427
  · exact B1510431
  · exact B1510435
  · exact B1510439
  · exact B1510443
  · exact B1510447
  · exact B1510451
  · exact B1510455
  · exact B1510459
  · exact B1510463
  · exact B1510467
  · exact B1510471
  · exact B1510475
  · exact B1510479
  · exact B1510483
  · exact B1510487
  · exact B1510491
  · exact B1510495
  · exact B1510499
  · exact B1510503
  · exact B1510507
  · exact B1510511
  · exact B1510515
  · exact B1510519
  · exact B1510523
  · exact B1510527
  · exact B1510531
  · exact B1510535
  · exact B1510539
  · exact B1510543
  · exact B1510547
  · exact B1510551
  · exact B1510555
  · exact B1510559
  · exact B1510563
  · exact B1510567
  · exact B1510571
  · exact B1510575
  · exact B1510579
  · exact B1510583
  · exact B1510587
  · exact B1510591
  · exact B1510595
  · exact B1510599
  · exact B1510603
  · exact B1510607
  · exact B1510611
  · exact B1510615
  · exact B1510619
  · exact B1510623
  · exact B1510627
  · exact B1510631
  · exact B1510635
  · exact B1510639
  · exact B1510643
  · exact B1510647
  · exact B1510651
  · exact B1510655
  · exact B1510659
  · exact B1510663
  · exact B1510667
  · exact B1510671
  · exact B1510675
  · exact B1510679
  · exact B1510683
  · exact B1510687
  · exact B1510691
  · exact B1510695
  · exact B1510699
  · exact B1510703
  · exact B1510707
  · exact B1510711
  · exact B1510715
  · exact B1510719
  · exact B1510723
  · exact B1510727
  · exact B1510731
  · exact B1510735
  · exact B1510739
  · exact B1510743
  · exact B1510747
  · exact B1510751
  · exact B1510755
  · exact B1510759
  · exact B1510763
  · exact B1510767
  · exact B1510771
  · exact B1510775
  · exact B1510779
  · exact B1510783
  · exact B1510787
  · exact B1510791
  · exact B1510795
  · exact B1510799
  · exact B1510803
  · exact B1510807
  · exact B1510811
  · exact B1510815
  · exact B1510819
  · exact B1510823
  · exact B1510827
  · exact B1510831
  · exact B1510835
  · exact B1510839
  · exact B1510843
  · exact B1510847
  · exact B1510851
  · exact B1510855
  · exact B1510859
  · exact B1510863
  · exact B1510867
  · exact B1510871
  · exact B1510875
  · exact B1510879
  · exact B1510883
  · exact B1510887
  · exact B1510891
  · exact B1510895
  · exact B1510899
  · exact B1510903
  · exact B1510907
  · exact B1510911
  · exact B1510915
  · exact B1510919
  · exact B1510923
  · exact B1510927
  · exact B1510931
  · exact B1510935
  · exact B1510939
  · exact B1510943
  · exact B1510947
  · exact B1510951

theorem solution (m : ℕ) (hlo : 1508951 ≤ m) (hhi : m ≤ 1510951) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 377237 ≤ j := by omega
    have hj2 : j ≤ 377737 := by omega
    have hb : Blo 1508951 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
