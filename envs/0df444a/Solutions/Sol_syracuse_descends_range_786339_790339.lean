-- Prove2me | solution 1 for syracuse_descends_range_786339_790339
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:33.011736+00:00
-- url     : https://prove2.me/submissions/3245f02c-c8e1-4097-957c-d9a210f31f92

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


theorem B1179653 : Blo 786339 1179653 := bbase (se 4 (by rfl) ⟨110592, by rfl⟩ : syracuseStep 1179653 = 221185) (by norm_num)
theorem B884749 : Blo 786339 884749 := bbase (se 3 (by rfl) ⟨165890, by rfl⟩ : syracuseStep 884749 = 331781) (by norm_num)
theorem B1179677 : Blo 786339 1179677 := bbase (se 3 (by rfl) ⟨221189, by rfl⟩ : syracuseStep 1179677 = 442379) (by norm_num)
theorem B1998877 : Blo 786339 1998877 := bbase (se 3 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 1998877 = 749579) (by norm_num)
theorem B884785 : Blo 786339 884785 := bbase (se 2 (by rfl) ⟨331794, by rfl⟩ : syracuseStep 884785 = 663589) (by norm_num)
theorem B2654261 : Blo 786339 2654261 := bbase (se 5 (by rfl) ⟨124418, by rfl⟩ : syracuseStep 2654261 = 248837) (by norm_num)
theorem B1769525 : Blo 786339 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B1179701 : Blo 786339 1179701 := bbase (se 5 (by rfl) ⟨55298, by rfl⟩ : syracuseStep 1179701 = 110597) (by norm_num)
theorem B1179725 : Blo 786339 1179725 := bbase (se 3 (by rfl) ⟨221198, by rfl⟩ : syracuseStep 1179725 = 442397) (by norm_num)
theorem B884821 : Blo 786339 884821 := bbase (se 8 (by rfl) ⟨5184, by rfl⟩ : syracuseStep 884821 = 10369) (by norm_num)
theorem B1179749 : Blo 786339 1179749 := bbase (se 4 (by rfl) ⟨110601, by rfl⟩ : syracuseStep 1179749 = 221203) (by norm_num)
theorem B884857 : Blo 786339 884857 := bbase (se 2 (by rfl) ⟨331821, by rfl⟩ : syracuseStep 884857 = 663643) (by norm_num)
theorem B1769597 : Blo 786339 1769597 := bbase (se 3 (by rfl) ⟨331799, by rfl⟩ : syracuseStep 1769597 = 663599) (by norm_num)
theorem B1179773 : Blo 786339 1179773 := bbase (se 3 (by rfl) ⟨221207, by rfl⟩ : syracuseStep 1179773 = 442415) (by norm_num)
theorem B1998989 : Blo 786339 1998989 := bbase (se 3 (by rfl) ⟨374810, by rfl⟩ : syracuseStep 1998989 = 749621) (by norm_num)
theorem B1179797 : Blo 786339 1179797 := bbase (se 6 (by rfl) ⟨27651, by rfl⟩ : syracuseStep 1179797 = 55303) (by norm_num)
theorem B884893 : Blo 786339 884893 := bbase (se 3 (by rfl) ⟨165917, by rfl⟩ : syracuseStep 884893 = 331835) (by norm_num)
theorem B1179821 : Blo 786339 1179821 := bbase (se 3 (by rfl) ⟨221216, by rfl⟩ : syracuseStep 1179821 = 442433) (by norm_num)
theorem B884929 : Blo 786339 884929 := bbase (se 2 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 884929 = 663697) (by norm_num)
theorem B1769669 : Blo 786339 1769669 := bbase (se 4 (by rfl) ⟨165906, by rfl⟩ : syracuseStep 1769669 = 331813) (by norm_num)
theorem B1179845 : Blo 786339 1179845 := bbase (se 4 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 1179845 = 221221) (by norm_num)
theorem B1179869 : Blo 786339 1179869 := bbase (se 3 (by rfl) ⟨221225, by rfl⟩ : syracuseStep 1179869 = 442451) (by norm_num)
theorem B884965 : Blo 786339 884965 := bbase (se 4 (by rfl) ⟨82965, by rfl⟩ : syracuseStep 884965 = 165931) (by norm_num)
theorem B1179893 : Blo 786339 1179893 := bbase (se 5 (by rfl) ⟨55307, by rfl⟩ : syracuseStep 1179893 = 110615) (by norm_num)
theorem B885001 : Blo 786339 885001 := bbase (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) (by norm_num)
theorem B1769741 : Blo 786339 1769741 := bbase (se 3 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 1769741 = 663653) (by norm_num)
theorem B1179917 : Blo 786339 1179917 := bbase (se 3 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 1179917 = 442469) (by norm_num)
theorem B1179941 : Blo 786339 1179941 := bbase (se 4 (by rfl) ⟨110619, by rfl⟩ : syracuseStep 1179941 = 221239) (by norm_num)
theorem B885037 : Blo 786339 885037 := bbase (se 3 (by rfl) ⟨165944, by rfl⟩ : syracuseStep 885037 = 331889) (by norm_num)
theorem B1179965 : Blo 786339 1179965 := bbase (se 3 (by rfl) ⟨221243, by rfl⟩ : syracuseStep 1179965 = 442487) (by norm_num)
theorem B1999181 : Blo 786339 1999181 := bbase (se 3 (by rfl) ⟨374846, by rfl⟩ : syracuseStep 1999181 = 749693) (by norm_num)
theorem B885073 : Blo 786339 885073 := bbase (se 2 (by rfl) ⟨331902, by rfl⟩ : syracuseStep 885073 = 663805) (by norm_num)
theorem B1769813 : Blo 786339 1769813 := bbase (se 10 (by rfl) ⟨2592, by rfl⟩ : syracuseStep 1769813 = 5185) (by norm_num)
theorem B1179989 : Blo 786339 1179989 := bbase (se 10 (by rfl) ⟨1728, by rfl⟩ : syracuseStep 1179989 = 3457) (by norm_num)
theorem B1180013 : Blo 786339 1180013 := bbase (se 3 (by rfl) ⟨221252, by rfl⟩ : syracuseStep 1180013 = 442505) (by norm_num)
theorem B885109 : Blo 786339 885109 := bbase (se 5 (by rfl) ⟨41489, by rfl⟩ : syracuseStep 885109 = 82979) (by norm_num)
theorem B1180037 : Blo 786339 1180037 := bbase (se 4 (by rfl) ⟨110628, by rfl⟩ : syracuseStep 1180037 = 221257) (by norm_num)
theorem B885145 : Blo 786339 885145 := bbase (se 2 (by rfl) ⟨331929, by rfl⟩ : syracuseStep 885145 = 663859) (by norm_num)
theorem B1769885 : Blo 786339 1769885 := bbase (se 3 (by rfl) ⟨331853, by rfl⟩ : syracuseStep 1769885 = 663707) (by norm_num)
theorem B1180061 : Blo 786339 1180061 := bbase (se 3 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 1180061 = 442523) (by norm_num)
theorem B1180085 : Blo 786339 1180085 := bbase (se 5 (by rfl) ⟨55316, by rfl⟩ : syracuseStep 1180085 = 110633) (by norm_num)
theorem B885181 : Blo 786339 885181 := bbase (se 3 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 885181 = 331943) (by norm_num)
theorem B1180109 : Blo 786339 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B885217 : Blo 786339 885217 := bbase (se 2 (by rfl) ⟨331956, by rfl⟩ : syracuseStep 885217 = 663913) (by norm_num)
theorem B2654693 : Blo 786339 2654693 := bbase (se 4 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 2654693 = 497755) (by norm_num)
theorem B1769957 : Blo 786339 1769957 := bbase (se 4 (by rfl) ⟨165933, by rfl⟩ : syracuseStep 1769957 = 331867) (by norm_num)
theorem B1180133 : Blo 786339 1180133 := bbase (se 4 (by rfl) ⟨110637, by rfl⟩ : syracuseStep 1180133 = 221275) (by norm_num)
theorem B1180157 : Blo 786339 1180157 := bbase (se 3 (by rfl) ⟨221279, by rfl⟩ : syracuseStep 1180157 = 442559) (by norm_num)
theorem B885253 : Blo 786339 885253 := bbase (se 4 (by rfl) ⟨82992, by rfl⟩ : syracuseStep 885253 = 165985) (by norm_num)
theorem B1180181 : Blo 786339 1180181 := bbase (se 6 (by rfl) ⟨27660, by rfl⟩ : syracuseStep 1180181 = 55321) (by norm_num)
theorem B885289 : Blo 786339 885289 := bbase (se 2 (by rfl) ⟨331983, by rfl⟩ : syracuseStep 885289 = 663967) (by norm_num)
theorem B1770029 : Blo 786339 1770029 := bbase (se 3 (by rfl) ⟨331880, by rfl⟩ : syracuseStep 1770029 = 663761) (by norm_num)
theorem B1180205 : Blo 786339 1180205 := bbase (se 3 (by rfl) ⟨221288, by rfl⟩ : syracuseStep 1180205 = 442577) (by norm_num)
theorem B1180229 : Blo 786339 1180229 := bbase (se 4 (by rfl) ⟨110646, by rfl⟩ : syracuseStep 1180229 = 221293) (by norm_num)
theorem B885325 : Blo 786339 885325 := bbase (se 3 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 885325 = 331997) (by norm_num)
theorem B1180253 : Blo 786339 1180253 := bbase (se 3 (by rfl) ⟨221297, by rfl⟩ : syracuseStep 1180253 = 442595) (by norm_num)
theorem B885361 : Blo 786339 885361 := bbase (se 2 (by rfl) ⟨332010, by rfl⟩ : syracuseStep 885361 = 664021) (by norm_num)
theorem B1770101 : Blo 786339 1770101 := bbase (se 5 (by rfl) ⟨82973, by rfl⟩ : syracuseStep 1770101 = 165947) (by norm_num)
theorem B1180277 : Blo 786339 1180277 := bbase (se 5 (by rfl) ⟨55325, by rfl⟩ : syracuseStep 1180277 = 110651) (by norm_num)
theorem B1180301 : Blo 786339 1180301 := bbase (se 3 (by rfl) ⟨221306, by rfl⟩ : syracuseStep 1180301 = 442613) (by norm_num)
theorem B885397 : Blo 786339 885397 := bbase (se 6 (by rfl) ⟨20751, by rfl⟩ : syracuseStep 885397 = 41503) (by norm_num)
theorem B1180325 : Blo 786339 1180325 := bbase (se 4 (by rfl) ⟨110655, by rfl⟩ : syracuseStep 1180325 = 221311) (by norm_num)
theorem B1999525 : Blo 786339 1999525 := bbase (se 4 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 1999525 = 374911) (by norm_num)
theorem B885433 : Blo 786339 885433 := bbase (se 2 (by rfl) ⟨332037, by rfl⟩ : syracuseStep 885433 = 664075) (by norm_num)
theorem B1770173 : Blo 786339 1770173 := bbase (se 3 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 1770173 = 663815) (by norm_num)
theorem B1180349 : Blo 786339 1180349 := bbase (se 3 (by rfl) ⟨221315, by rfl⟩ : syracuseStep 1180349 = 442631) (by norm_num)
theorem B1180373 : Blo 786339 1180373 := bbase (se 7 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 1180373 = 27665) (by norm_num)
theorem B885469 : Blo 786339 885469 := bbase (se 3 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 885469 = 332051) (by norm_num)
theorem B1180397 : Blo 786339 1180397 := bbase (se 3 (by rfl) ⟨221324, by rfl⟩ : syracuseStep 1180397 = 442649) (by norm_num)
theorem B885505 : Blo 786339 885505 := bbase (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) (by norm_num)
theorem B1770245 : Blo 786339 1770245 := bbase (se 4 (by rfl) ⟨165960, by rfl⟩ : syracuseStep 1770245 = 331921) (by norm_num)
theorem B1180421 : Blo 786339 1180421 := bbase (se 4 (by rfl) ⟨110664, by rfl⟩ : syracuseStep 1180421 = 221329) (by norm_num)
theorem B1999637 : Blo 786339 1999637 := bbase (se 6 (by rfl) ⟨46866, by rfl⟩ : syracuseStep 1999637 = 93733) (by norm_num)
theorem B1180445 : Blo 786339 1180445 := bbase (se 3 (by rfl) ⟨221333, by rfl⟩ : syracuseStep 1180445 = 442667) (by norm_num)
theorem B885541 : Blo 786339 885541 := bbase (se 4 (by rfl) ⟨83019, by rfl⟩ : syracuseStep 885541 = 166039) (by norm_num)
theorem B1180469 : Blo 786339 1180469 := bbase (se 5 (by rfl) ⟨55334, by rfl⟩ : syracuseStep 1180469 = 110669) (by norm_num)
theorem B885577 : Blo 786339 885577 := bbase (se 2 (by rfl) ⟨332091, by rfl⟩ : syracuseStep 885577 = 664183) (by norm_num)
theorem B1770317 : Blo 786339 1770317 := bbase (se 3 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 1770317 = 663869) (by norm_num)
theorem B1180493 : Blo 786339 1180493 := bbase (se 3 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 1180493 = 442685) (by norm_num)
theorem B951133 : Blo 786339 951133 := bbase (se 3 (by rfl) ⟨178337, by rfl⟩ : syracuseStep 951133 = 356675) (by norm_num)
theorem B1180517 : Blo 786339 1180517 := bbase (se 4 (by rfl) ⟨110673, by rfl⟩ : syracuseStep 1180517 = 221347) (by norm_num)
theorem B885613 : Blo 786339 885613 := bbase (se 3 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 885613 = 332105) (by norm_num)
theorem B1180541 : Blo 786339 1180541 := bbase (se 3 (by rfl) ⟨221351, by rfl⟩ : syracuseStep 1180541 = 442703) (by norm_num)
theorem B885649 : Blo 786339 885649 := bbase (se 2 (by rfl) ⟨332118, by rfl⟩ : syracuseStep 885649 = 664237) (by norm_num)
theorem B2655125 : Blo 786339 2655125 := bbase (se 6 (by rfl) ⟨62229, by rfl⟩ : syracuseStep 2655125 = 124459) (by norm_num)
theorem B1770389 : Blo 786339 1770389 := bbase (se 6 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 1770389 = 82987) (by norm_num)
theorem B1180565 : Blo 786339 1180565 := bbase (se 6 (by rfl) ⟨27669, by rfl⟩ : syracuseStep 1180565 = 55339) (by norm_num)
theorem B1180589 : Blo 786339 1180589 := bbase (se 3 (by rfl) ⟨221360, by rfl⟩ : syracuseStep 1180589 = 442721) (by norm_num)
theorem B885685 : Blo 786339 885685 := bbase (se 5 (by rfl) ⟨41516, by rfl⟩ : syracuseStep 885685 = 83033) (by norm_num)
theorem B3998645 : Blo 786339 3998645 := bbase (se 5 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 3998645 = 374873) (by norm_num)
theorem B1180613 : Blo 786339 1180613 := bbase (se 4 (by rfl) ⟨110682, by rfl⟩ : syracuseStep 1180613 = 221365) (by norm_num)
theorem B1999829 : Blo 786339 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B885721 : Blo 786339 885721 := bbase (se 2 (by rfl) ⟨332145, by rfl⟩ : syracuseStep 885721 = 664291) (by norm_num)
theorem B1770461 : Blo 786339 1770461 := bbase (se 3 (by rfl) ⟨331961, by rfl⟩ : syracuseStep 1770461 = 663923) (by norm_num)
theorem B1180637 : Blo 786339 1180637 := bbase (se 3 (by rfl) ⟨221369, by rfl⟩ : syracuseStep 1180637 = 442739) (by norm_num)
theorem B1180661 : Blo 786339 1180661 := bbase (se 5 (by rfl) ⟨55343, by rfl⟩ : syracuseStep 1180661 = 110687) (by norm_num)
theorem B2556917 : Blo 786339 2556917 := bbase (se 5 (by rfl) ⟨119855, by rfl⟩ : syracuseStep 2556917 = 239711) (by norm_num)
theorem B885757 : Blo 786339 885757 := bbase (se 3 (by rfl) ⟨166079, by rfl⟩ : syracuseStep 885757 = 332159) (by norm_num)
theorem B1180685 : Blo 786339 1180685 := bbase (se 3 (by rfl) ⟨221378, by rfl⟩ : syracuseStep 1180685 = 442757) (by norm_num)
theorem B885793 : Blo 786339 885793 := bbase (se 2 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 885793 = 664345) (by norm_num)
theorem B1770533 : Blo 786339 1770533 := bbase (se 4 (by rfl) ⟨165987, by rfl⟩ : syracuseStep 1770533 = 331975) (by norm_num)
theorem B1180709 : Blo 786339 1180709 := bbase (se 4 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 1180709 = 221383) (by norm_num)
theorem B1180733 : Blo 786339 1180733 := bbase (se 3 (by rfl) ⟨221387, by rfl⟩ : syracuseStep 1180733 = 442775) (by norm_num)
theorem B885829 : Blo 786339 885829 := bbase (se 4 (by rfl) ⟨83046, by rfl⟩ : syracuseStep 885829 = 166093) (by norm_num)
theorem B1180757 : Blo 786339 1180757 := bbase (se 8 (by rfl) ⟨6918, by rfl⟩ : syracuseStep 1180757 = 13837) (by norm_num)
theorem B885865 : Blo 786339 885865 := bbase (se 2 (by rfl) ⟨332199, by rfl⟩ : syracuseStep 885865 = 664399) (by norm_num)
theorem B1770605 : Blo 786339 1770605 := bbase (se 3 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 1770605 = 663977) (by norm_num)
theorem B1180781 : Blo 786339 1180781 := bbase (se 3 (by rfl) ⟨221396, by rfl⟩ : syracuseStep 1180781 = 442793) (by norm_num)
theorem B1180805 : Blo 786339 1180805 := bbase (se 4 (by rfl) ⟨110700, by rfl⟩ : syracuseStep 1180805 = 221401) (by norm_num)
theorem B885901 : Blo 786339 885901 := bbase (se 3 (by rfl) ⟨166106, by rfl⟩ : syracuseStep 885901 = 332213) (by norm_num)
theorem B1180829 : Blo 786339 1180829 := bbase (se 3 (by rfl) ⟨221405, by rfl⟩ : syracuseStep 1180829 = 442811) (by norm_num)
theorem B885937 : Blo 786339 885937 := bbase (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) (by norm_num)
theorem B1770677 : Blo 786339 1770677 := bbase (se 5 (by rfl) ⟨83000, by rfl⟩ : syracuseStep 1770677 = 166001) (by norm_num)
theorem B1180853 : Blo 786339 1180853 := bbase (se 5 (by rfl) ⟨55352, by rfl⟩ : syracuseStep 1180853 = 110705) (by norm_num)
theorem B1180877 : Blo 786339 1180877 := bbase (se 3 (by rfl) ⟨221414, by rfl⟩ : syracuseStep 1180877 = 442829) (by norm_num)
theorem B885973 : Blo 786339 885973 := bbase (se 7 (by rfl) ⟨10382, by rfl⟩ : syracuseStep 885973 = 20765) (by norm_num)
theorem B1180901 : Blo 786339 1180901 := bbase (se 4 (by rfl) ⟨110709, by rfl⟩ : syracuseStep 1180901 = 221419) (by norm_num)
theorem B886009 : Blo 786339 886009 := bbase (se 2 (by rfl) ⟨332253, by rfl⟩ : syracuseStep 886009 = 664507) (by norm_num)
theorem B1770749 : Blo 786339 1770749 := bbase (se 3 (by rfl) ⟨332015, by rfl⟩ : syracuseStep 1770749 = 664031) (by norm_num)
theorem B1180925 : Blo 786339 1180925 := bbase (se 3 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 1180925 = 442847) (by norm_num)
theorem B1180949 : Blo 786339 1180949 := bbase (se 6 (by rfl) ⟨27678, by rfl⟩ : syracuseStep 1180949 = 55357) (by norm_num)
theorem B886045 : Blo 786339 886045 := bbase (se 3 (by rfl) ⟨166133, by rfl⟩ : syracuseStep 886045 = 332267) (by norm_num)
theorem B1180973 : Blo 786339 1180973 := bbase (se 3 (by rfl) ⟨221432, by rfl⟩ : syracuseStep 1180973 = 442865) (by norm_num)
theorem B2000173 : Blo 786339 2000173 := bbase (se 3 (by rfl) ⟨375032, by rfl⟩ : syracuseStep 2000173 = 750065) (by norm_num)
theorem B4490549 : Blo 786339 4490549 := bbase (se 5 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 4490549 = 420989) (by norm_num)
theorem B886081 : Blo 786339 886081 := bbase (se 2 (by rfl) ⟨332280, by rfl⟩ : syracuseStep 886081 = 664561) (by norm_num)
theorem B2655557 : Blo 786339 2655557 := bbase (se 4 (by rfl) ⟨248958, by rfl⟩ : syracuseStep 2655557 = 497917) (by norm_num)
theorem B1770821 : Blo 786339 1770821 := bbase (se 4 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 1770821 = 332029) (by norm_num)
theorem B1180997 : Blo 786339 1180997 := bbase (se 4 (by rfl) ⟨110718, by rfl⟩ : syracuseStep 1180997 = 221437) (by norm_num)
theorem B1181021 : Blo 786339 1181021 := bbase (se 3 (by rfl) ⟨221441, by rfl⟩ : syracuseStep 1181021 = 442883) (by norm_num)
theorem B886117 : Blo 786339 886117 := bbase (se 4 (by rfl) ⟨83073, by rfl⟩ : syracuseStep 886117 = 166147) (by norm_num)
theorem B1181045 : Blo 786339 1181045 := bbase (se 5 (by rfl) ⟨55361, by rfl⟩ : syracuseStep 1181045 = 110723) (by norm_num)
theorem B886153 : Blo 786339 886153 := bbase (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) (by norm_num)
theorem B1770893 : Blo 786339 1770893 := bbase (se 3 (by rfl) ⟨332042, by rfl⟩ : syracuseStep 1770893 = 664085) (by norm_num)
theorem B1181069 : Blo 786339 1181069 := bbase (se 3 (by rfl) ⟨221450, by rfl⟩ : syracuseStep 1181069 = 442901) (by norm_num)
theorem B2000285 : Blo 786339 2000285 := bbase (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) (by norm_num)
theorem B1181093 : Blo 786339 1181093 := bbase (se 4 (by rfl) ⟨110727, by rfl⟩ : syracuseStep 1181093 = 221455) (by norm_num)
theorem B886189 : Blo 786339 886189 := bbase (se 3 (by rfl) ⟨166160, by rfl⟩ : syracuseStep 886189 = 332321) (by norm_num)
theorem B1181117 : Blo 786339 1181117 := bbase (se 3 (by rfl) ⟨221459, by rfl⟩ : syracuseStep 1181117 = 442919) (by norm_num)
theorem B886225 : Blo 786339 886225 := bbase (se 2 (by rfl) ⟨332334, by rfl⟩ : syracuseStep 886225 = 664669) (by norm_num)
theorem B1770965 : Blo 786339 1770965 := bbase (se 7 (by rfl) ⟨20753, by rfl⟩ : syracuseStep 1770965 = 41507) (by norm_num)
theorem B1181141 : Blo 786339 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B1705445 : Blo 786339 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B1181165 : Blo 786339 1181165 := bbase (se 3 (by rfl) ⟨221468, by rfl⟩ : syracuseStep 1181165 = 442937) (by norm_num)
theorem B886261 : Blo 786339 886261 := bbase (se 5 (by rfl) ⟨41543, by rfl⟩ : syracuseStep 886261 = 83087) (by norm_num)
theorem B1181189 : Blo 786339 1181189 := bbase (se 4 (by rfl) ⟨110736, by rfl⟩ : syracuseStep 1181189 = 221473) (by norm_num)
theorem B886297 : Blo 786339 886297 := bbase (se 2 (by rfl) ⟨332361, by rfl⟩ : syracuseStep 886297 = 664723) (by norm_num)
theorem B1771037 : Blo 786339 1771037 := bbase (se 3 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 1771037 = 664139) (by norm_num)
theorem B1181213 : Blo 786339 1181213 := bbase (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) (by norm_num)
theorem B1181237 : Blo 786339 1181237 := bbase (se 5 (by rfl) ⟨55370, by rfl⟩ : syracuseStep 1181237 = 110741) (by norm_num)
theorem B886333 : Blo 786339 886333 := bbase (se 3 (by rfl) ⟨166187, by rfl⟩ : syracuseStep 886333 = 332375) (by norm_num)
theorem B1181261 : Blo 786339 1181261 := bbase (se 3 (by rfl) ⟨221486, by rfl⟩ : syracuseStep 1181261 = 442973) (by norm_num)
theorem B8619605 : Blo 786339 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B23004757 : Blo 786339 23004757 := bbase (se 8 (by rfl) ⟨134793, by rfl⟩ : syracuseStep 23004757 = 269587) (by norm_num)
theorem B2000477 : Blo 786339 2000477 := bbase (se 3 (by rfl) ⟨375089, by rfl⟩ : syracuseStep 2000477 = 750179) (by norm_num)
theorem B886369 : Blo 786339 886369 := bbase (se 2 (by rfl) ⟨332388, by rfl⟩ : syracuseStep 886369 = 664777) (by norm_num)
theorem B1771109 : Blo 786339 1771109 := bbase (se 4 (by rfl) ⟨166041, by rfl⟩ : syracuseStep 1771109 = 332083) (by norm_num)
theorem B1181285 : Blo 786339 1181285 := bbase (se 4 (by rfl) ⟨110745, by rfl⟩ : syracuseStep 1181285 = 221491) (by norm_num)
theorem B1181309 : Blo 786339 1181309 := bbase (se 3 (by rfl) ⟨221495, by rfl⟩ : syracuseStep 1181309 = 442991) (by norm_num)
theorem B886405 : Blo 786339 886405 := bbase (se 4 (by rfl) ⟨83100, by rfl⟩ : syracuseStep 886405 = 166201) (by norm_num)
theorem B2393749 : Blo 786339 2393749 := bbase (se 6 (by rfl) ⟨56103, by rfl⟩ : syracuseStep 2393749 = 112207) (by norm_num)
theorem B1181333 : Blo 786339 1181333 := bbase (se 6 (by rfl) ⟨27687, by rfl⟩ : syracuseStep 1181333 = 55375) (by norm_num)
theorem B886441 : Blo 786339 886441 := bbase (se 2 (by rfl) ⟨332415, by rfl⟩ : syracuseStep 886441 = 664831) (by norm_num)
theorem B1771181 : Blo 786339 1771181 := bbase (se 3 (by rfl) ⟨332096, by rfl⟩ : syracuseStep 1771181 = 664193) (by norm_num)
theorem B1181357 : Blo 786339 1181357 := bbase (se 3 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 1181357 = 443009) (by norm_num)
theorem B1181381 : Blo 786339 1181381 := bbase (se 4 (by rfl) ⟨110754, by rfl⟩ : syracuseStep 1181381 = 221509) (by norm_num)
theorem B886477 : Blo 786339 886477 := bbase (se 3 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 886477 = 332429) (by norm_num)
theorem B2393813 : Blo 786339 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B1181405 : Blo 786339 1181405 := bbase (se 3 (by rfl) ⟨221513, by rfl⟩ : syracuseStep 1181405 = 443027) (by norm_num)
theorem B886513 : Blo 786339 886513 := bbase (se 2 (by rfl) ⟨332442, by rfl⟩ : syracuseStep 886513 = 664885) (by norm_num)
theorem B2655989 : Blo 786339 2655989 := bbase (se 5 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 2655989 = 248999) (by norm_num)
theorem B1771253 : Blo 786339 1771253 := bbase (se 5 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 1771253 = 166055) (by norm_num)
theorem B1181429 : Blo 786339 1181429 := bbase (se 5 (by rfl) ⟨55379, by rfl⟩ : syracuseStep 1181429 = 110759) (by norm_num)
theorem B1181453 : Blo 786339 1181453 := bbase (se 3 (by rfl) ⟨221522, by rfl⟩ : syracuseStep 1181453 = 443045) (by norm_num)
theorem B886549 : Blo 786339 886549 := bbase (se 6 (by rfl) ⟨20778, by rfl⟩ : syracuseStep 886549 = 41557) (by norm_num)
theorem B1181477 : Blo 786339 1181477 := bbase (se 4 (by rfl) ⟨110763, by rfl⟩ : syracuseStep 1181477 = 221527) (by norm_num)
theorem B886585 : Blo 786339 886585 := bbase (se 2 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 886585 = 664939) (by norm_num)
theorem B1771325 : Blo 786339 1771325 := bbase (se 3 (by rfl) ⟨332123, by rfl⟩ : syracuseStep 1771325 = 664247) (by norm_num)
theorem B1181501 : Blo 786339 1181501 := bbase (se 3 (by rfl) ⟨221531, by rfl⟩ : syracuseStep 1181501 = 443063) (by norm_num)
theorem B1181525 : Blo 786339 1181525 := bbase (se 9 (by rfl) ⟨3461, by rfl⟩ : syracuseStep 1181525 = 6923) (by norm_num)
theorem B886621 : Blo 786339 886621 := bbase (se 3 (by rfl) ⟨166241, by rfl⟩ : syracuseStep 886621 = 332483) (by norm_num)
theorem B1181549 : Blo 786339 1181549 := bbase (se 3 (by rfl) ⟨221540, by rfl⟩ : syracuseStep 1181549 = 443081) (by norm_num)
theorem B886657 : Blo 786339 886657 := bbase (se 2 (by rfl) ⟨332496, by rfl⟩ : syracuseStep 886657 = 664993) (by norm_num)
theorem B1771397 : Blo 786339 1771397 := bbase (se 4 (by rfl) ⟨166068, by rfl⟩ : syracuseStep 1771397 = 332137) (by norm_num)
theorem B1181573 : Blo 786339 1181573 := bbase (se 4 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 1181573 = 221545) (by norm_num)
theorem B1181597 : Blo 786339 1181597 := bbase (se 3 (by rfl) ⟨221549, by rfl⟩ : syracuseStep 1181597 = 443099) (by norm_num)
theorem B886693 : Blo 786339 886693 := bbase (se 4 (by rfl) ⟨83127, by rfl⟩ : syracuseStep 886693 = 166255) (by norm_num)
theorem B1181621 : Blo 786339 1181621 := bbase (se 5 (by rfl) ⟨55388, by rfl⟩ : syracuseStep 1181621 = 110777) (by norm_num)
theorem B886729 : Blo 786339 886729 := bbase (se 2 (by rfl) ⟨332523, by rfl⟩ : syracuseStep 886729 = 665047) (by norm_num)
theorem B1771469 : Blo 786339 1771469 := bbase (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) (by norm_num)
theorem B1181645 : Blo 786339 1181645 := bbase (se 3 (by rfl) ⟨221558, by rfl⟩ : syracuseStep 1181645 = 443117) (by norm_num)
theorem B1181669 : Blo 786339 1181669 := bbase (se 4 (by rfl) ⟨110781, by rfl⟩ : syracuseStep 1181669 = 221563) (by norm_num)
theorem B886765 : Blo 786339 886765 := bbase (se 3 (by rfl) ⟨166268, by rfl⟩ : syracuseStep 886765 = 332537) (by norm_num)
theorem B1181693 : Blo 786339 1181693 := bbase (se 3 (by rfl) ⟨221567, by rfl⟩ : syracuseStep 1181693 = 443135) (by norm_num)
theorem B886801 : Blo 786339 886801 := bbase (se 2 (by rfl) ⟨332550, by rfl⟩ : syracuseStep 886801 = 665101) (by norm_num)
theorem B1771541 : Blo 786339 1771541 := bbase (se 6 (by rfl) ⟨41520, by rfl⟩ : syracuseStep 1771541 = 83041) (by norm_num)
theorem B1181717 : Blo 786339 1181717 := bbase (se 6 (by rfl) ⟨27696, by rfl⟩ : syracuseStep 1181717 = 55393) (by norm_num)
theorem B4261909 : Blo 786339 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B1181741 : Blo 786339 1181741 := bbase (se 3 (by rfl) ⟨221576, by rfl⟩ : syracuseStep 1181741 = 443153) (by norm_num)
theorem B886837 : Blo 786339 886837 := bbase (se 5 (by rfl) ⟨41570, by rfl⟩ : syracuseStep 886837 = 83141) (by norm_num)
theorem B1181765 : Blo 786339 1181765 := bbase (se 4 (by rfl) ⟨110790, by rfl⟩ : syracuseStep 1181765 = 221581) (by norm_num)
theorem B886873 : Blo 786339 886873 := bbase (se 2 (by rfl) ⟨332577, by rfl⟩ : syracuseStep 886873 = 665155) (by norm_num)
theorem B1771613 : Blo 786339 1771613 := bbase (se 3 (by rfl) ⟨332177, by rfl⟩ : syracuseStep 1771613 = 664355) (by norm_num)
theorem B1181789 : Blo 786339 1181789 := bbase (se 3 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 1181789 = 443171) (by norm_num)
theorem B1181813 : Blo 786339 1181813 := bbase (se 5 (by rfl) ⟨55397, by rfl⟩ : syracuseStep 1181813 = 110795) (by norm_num)
theorem B886909 : Blo 786339 886909 := bbase (se 3 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 886909 = 332591) (by norm_num)
theorem B1181837 : Blo 786339 1181837 := bbase (se 3 (by rfl) ⟨221594, by rfl⟩ : syracuseStep 1181837 = 443189) (by norm_num)
theorem B886945 : Blo 786339 886945 := bbase (se 2 (by rfl) ⟨332604, by rfl⟩ : syracuseStep 886945 = 665209) (by norm_num)
theorem B2656421 : Blo 786339 2656421 := bbase (se 4 (by rfl) ⟨249039, by rfl⟩ : syracuseStep 2656421 = 498079) (by norm_num)
theorem B1771685 : Blo 786339 1771685 := bbase (se 4 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 1771685 = 332191) (by norm_num)
theorem B1181861 : Blo 786339 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B1181885 : Blo 786339 1181885 := bbase (se 3 (by rfl) ⟨221603, by rfl⟩ : syracuseStep 1181885 = 443207) (by norm_num)
theorem B886981 : Blo 786339 886981 := bbase (se 4 (by rfl) ⟨83154, by rfl⟩ : syracuseStep 886981 = 166309) (by norm_num)
theorem B3999941 : Blo 786339 3999941 := bbase (se 4 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 3999941 = 749989) (by norm_num)
theorem B1181909 : Blo 786339 1181909 := bbase (se 7 (by rfl) ⟨13850, by rfl⟩ : syracuseStep 1181909 = 27701) (by norm_num)
theorem B887017 : Blo 786339 887017 := bbase (se 2 (by rfl) ⟨332631, by rfl⟩ : syracuseStep 887017 = 665263) (by norm_num)
theorem B1771757 : Blo 786339 1771757 := bbase (se 3 (by rfl) ⟨332204, by rfl⟩ : syracuseStep 1771757 = 664409) (by norm_num)
theorem B1181933 : Blo 786339 1181933 := bbase (se 3 (by rfl) ⟨221612, by rfl⟩ : syracuseStep 1181933 = 443225) (by norm_num)
theorem B1181957 : Blo 786339 1181957 := bbase (se 4 (by rfl) ⟨110808, by rfl⟩ : syracuseStep 1181957 = 221617) (by norm_num)
theorem B887053 : Blo 786339 887053 := bbase (se 3 (by rfl) ⟨166322, by rfl⟩ : syracuseStep 887053 = 332645) (by norm_num)
theorem B1181981 : Blo 786339 1181981 := bbase (se 3 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 1181981 = 443243) (by norm_num)
theorem B887089 : Blo 786339 887089 := bbase (se 2 (by rfl) ⟨332658, by rfl⟩ : syracuseStep 887089 = 665317) (by norm_num)
theorem B1771829 : Blo 786339 1771829 := bbase (se 5 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 1771829 = 166109) (by norm_num)
theorem B1182005 : Blo 786339 1182005 := bbase (se 5 (by rfl) ⟨55406, by rfl⟩ : syracuseStep 1182005 = 110813) (by norm_num)
theorem B1706309 : Blo 786339 1706309 := bbase (se 4 (by rfl) ⟨159966, by rfl⟩ : syracuseStep 1706309 = 319933) (by norm_num)
theorem B1182029 : Blo 786339 1182029 := bbase (se 3 (by rfl) ⟨221630, by rfl⟩ : syracuseStep 1182029 = 443261) (by norm_num)
theorem B2525525 : Blo 786339 2525525 := bbase (se 10 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 2525525 = 7399) (by norm_num)
theorem B887125 : Blo 786339 887125 := bbase (se 10 (by rfl) ⟨1299, by rfl⟩ : syracuseStep 887125 = 2599) (by norm_num)
theorem B1182053 : Blo 786339 1182053 := bbase (se 4 (by rfl) ⟨110817, by rfl⟩ : syracuseStep 1182053 = 221635) (by norm_num)
theorem B887161 : Blo 786339 887161 := bbase (se 2 (by rfl) ⟨332685, by rfl⟩ : syracuseStep 887161 = 665371) (by norm_num)
theorem B1771901 : Blo 786339 1771901 := bbase (se 3 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 1771901 = 664463) (by norm_num)
theorem B1182077 : Blo 786339 1182077 := bbase (se 3 (by rfl) ⟨221639, by rfl⟩ : syracuseStep 1182077 = 443279) (by norm_num)
theorem B1182101 : Blo 786339 1182101 := bbase (se 6 (by rfl) ⟨27705, by rfl⟩ : syracuseStep 1182101 = 55411) (by norm_num)
theorem B887197 : Blo 786339 887197 := bbase (se 3 (by rfl) ⟨166349, by rfl⟩ : syracuseStep 887197 = 332699) (by norm_num)
theorem B1182125 : Blo 786339 1182125 := bbase (se 3 (by rfl) ⟨221648, by rfl⟩ : syracuseStep 1182125 = 443297) (by norm_num)
theorem B854453 : Blo 786339 854453 := bbase (se 5 (by rfl) ⟨40052, by rfl⟩ : syracuseStep 854453 = 80105) (by norm_num)
theorem B887233 : Blo 786339 887233 := bbase (se 2 (by rfl) ⟨332712, by rfl⟩ : syracuseStep 887233 = 665425) (by norm_num)
theorem B1771973 : Blo 786339 1771973 := bbase (se 4 (by rfl) ⟨166122, by rfl⟩ : syracuseStep 1771973 = 332245) (by norm_num)
theorem B1182149 : Blo 786339 1182149 := bbase (se 4 (by rfl) ⟨110826, by rfl⟩ : syracuseStep 1182149 = 221653) (by norm_num)
theorem B4491733 : Blo 786339 4491733 := bbase (se 7 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 4491733 = 105275) (by norm_num)
theorem B1182173 : Blo 786339 1182173 := bbase (se 3 (by rfl) ⟨221657, by rfl⟩ : syracuseStep 1182173 = 443315) (by norm_num)
theorem B887269 : Blo 786339 887269 := bbase (se 4 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 887269 = 166363) (by norm_num)
theorem B1182197 : Blo 786339 1182197 := bbase (se 5 (by rfl) ⟨55415, by rfl⟩ : syracuseStep 1182197 = 110831) (by norm_num)
theorem B887305 : Blo 786339 887305 := bbase (se 2 (by rfl) ⟨332739, by rfl⟩ : syracuseStep 887305 = 665479) (by norm_num)
theorem B1772045 : Blo 786339 1772045 := bbase (se 3 (by rfl) ⟨332258, by rfl⟩ : syracuseStep 1772045 = 664517) (by norm_num)
theorem B1182221 : Blo 786339 1182221 := bbase (se 3 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 1182221 = 443333) (by norm_num)
theorem B1182245 : Blo 786339 1182245 := bbase (se 4 (by rfl) ⟨110835, by rfl⟩ : syracuseStep 1182245 = 221671) (by norm_num)
theorem B887341 : Blo 786339 887341 := bbase (se 3 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 887341 = 332753) (by norm_num)
theorem B1182269 : Blo 786339 1182269 := bbase (se 3 (by rfl) ⟨221675, by rfl⟩ : syracuseStep 1182269 = 443351) (by norm_num)
theorem B887377 : Blo 786339 887377 := bbase (se 2 (by rfl) ⟨332766, by rfl⟩ : syracuseStep 887377 = 665533) (by norm_num)
theorem B2656853 : Blo 786339 2656853 := bbase (se 8 (by rfl) ⟨15567, by rfl⟩ : syracuseStep 2656853 = 31135) (by norm_num)
theorem B1772117 : Blo 786339 1772117 := bbase (se 8 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 1772117 = 20767) (by norm_num)
theorem B1182293 : Blo 786339 1182293 := bbase (se 8 (by rfl) ⟨6927, by rfl⟩ : syracuseStep 1182293 = 13855) (by norm_num)
theorem B1182317 : Blo 786339 1182317 := bbase (se 3 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 1182317 = 443369) (by norm_num)
theorem B887413 : Blo 786339 887413 := bbase (se 5 (by rfl) ⟨41597, by rfl⟩ : syracuseStep 887413 = 83195) (by norm_num)
theorem B1182341 : Blo 786339 1182341 := bbase (se 4 (by rfl) ⟨110844, by rfl⟩ : syracuseStep 1182341 = 221689) (by norm_num)
theorem B887449 : Blo 786339 887449 := bbase (se 2 (by rfl) ⟨332793, by rfl⟩ : syracuseStep 887449 = 665587) (by norm_num)
theorem B1772189 : Blo 786339 1772189 := bbase (se 3 (by rfl) ⟨332285, by rfl⟩ : syracuseStep 1772189 = 664571) (by norm_num)
theorem B1182365 : Blo 786339 1182365 := bbase (se 3 (by rfl) ⟨221693, by rfl⟩ : syracuseStep 1182365 = 443387) (by norm_num)
theorem B1182389 : Blo 786339 1182389 := bbase (se 5 (by rfl) ⟨55424, by rfl⟩ : syracuseStep 1182389 = 110849) (by norm_num)
theorem B887485 : Blo 786339 887485 := bbase (se 3 (by rfl) ⟨166403, by rfl⟩ : syracuseStep 887485 = 332807) (by norm_num)
theorem B1182413 : Blo 786339 1182413 := bbase (se 3 (by rfl) ⟨221702, by rfl⟩ : syracuseStep 1182413 = 443405) (by norm_num)
theorem B887521 : Blo 786339 887521 := bbase (se 2 (by rfl) ⟨332820, by rfl⟩ : syracuseStep 887521 = 665641) (by norm_num)
theorem B1772261 : Blo 786339 1772261 := bbase (se 4 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 1772261 = 332299) (by norm_num)
theorem B1182437 : Blo 786339 1182437 := bbase (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) (by norm_num)
theorem B1182461 : Blo 786339 1182461 := bbase (se 3 (by rfl) ⟨221711, by rfl⟩ : syracuseStep 1182461 = 443423) (by norm_num)
theorem B887557 : Blo 786339 887557 := bbase (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) (by norm_num)
theorem B1182485 : Blo 786339 1182485 := bbase (se 6 (by rfl) ⟨27714, by rfl⟩ : syracuseStep 1182485 = 55429) (by norm_num)
theorem B2394917 : Blo 786339 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B887593 : Blo 786339 887593 := bbase (se 2 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 887593 = 665695) (by norm_num)
theorem B1772333 : Blo 786339 1772333 := bbase (se 3 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 1772333 = 664625) (by norm_num)
theorem B1182509 : Blo 786339 1182509 := bbase (se 3 (by rfl) ⟨221720, by rfl⟩ : syracuseStep 1182509 = 443441) (by norm_num)
theorem B1182533 : Blo 786339 1182533 := bbase (se 4 (by rfl) ⟨110862, by rfl⟩ : syracuseStep 1182533 = 221725) (by norm_num)
theorem B887629 : Blo 786339 887629 := bbase (se 3 (by rfl) ⟨166430, by rfl⟩ : syracuseStep 887629 = 332861) (by norm_num)
theorem B1182557 : Blo 786339 1182557 := bbase (se 3 (by rfl) ⟨221729, by rfl⟩ : syracuseStep 1182557 = 443459) (by norm_num)
theorem B887665 : Blo 786339 887665 := bbase (se 2 (by rfl) ⟨332874, by rfl⟩ : syracuseStep 887665 = 665749) (by norm_num)
theorem B1772405 : Blo 786339 1772405 := bbase (se 5 (by rfl) ⟨83081, by rfl⟩ : syracuseStep 1772405 = 166163) (by norm_num)
theorem B1182581 : Blo 786339 1182581 := bbase (se 5 (by rfl) ⟨55433, by rfl⟩ : syracuseStep 1182581 = 110867) (by norm_num)
theorem B1182605 : Blo 786339 1182605 := bbase (se 3 (by rfl) ⟨221738, by rfl⟩ : syracuseStep 1182605 = 443477) (by norm_num)
theorem B887701 : Blo 786339 887701 := bbase (se 6 (by rfl) ⟨20805, by rfl⟩ : syracuseStep 887701 = 41611) (by norm_num)
theorem B1182629 : Blo 786339 1182629 := bbase (se 4 (by rfl) ⟨110871, by rfl⟩ : syracuseStep 1182629 = 221743) (by norm_num)
theorem B887737 : Blo 786339 887737 := bbase (se 2 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 887737 = 665803) (by norm_num)
theorem B1772477 : Blo 786339 1772477 := bbase (se 3 (by rfl) ⟨332339, by rfl⟩ : syracuseStep 1772477 = 664679) (by norm_num)
theorem B1182653 : Blo 786339 1182653 := bbase (se 3 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 1182653 = 443495) (by norm_num)
theorem B1182677 : Blo 786339 1182677 := bbase (se 7 (by rfl) ⟨13859, by rfl⟩ : syracuseStep 1182677 = 27719) (by norm_num)
theorem B887773 : Blo 786339 887773 := bbase (se 3 (by rfl) ⟨166457, by rfl⟩ : syracuseStep 887773 = 332915) (by norm_num)
theorem B1215461 : Blo 786339 1215461 := bbase (se 4 (by rfl) ⟨113949, by rfl⟩ : syracuseStep 1215461 = 227899) (by norm_num)
theorem B1182701 : Blo 786339 1182701 := bbase (se 3 (by rfl) ⟨221756, by rfl⟩ : syracuseStep 1182701 = 443513) (by norm_num)
theorem B887809 : Blo 786339 887809 := bbase (se 2 (by rfl) ⟨332928, by rfl⟩ : syracuseStep 887809 = 665857) (by norm_num)
theorem B2657285 : Blo 786339 2657285 := bbase (se 4 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 2657285 = 498241) (by norm_num)
theorem B1772549 : Blo 786339 1772549 := bbase (se 4 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 1772549 = 332353) (by norm_num)
theorem B1182725 : Blo 786339 1182725 := bbase (se 4 (by rfl) ⟨110880, by rfl⟩ : syracuseStep 1182725 = 221761) (by norm_num)
theorem B1182749 : Blo 786339 1182749 := bbase (se 3 (by rfl) ⟨221765, by rfl⟩ : syracuseStep 1182749 = 443531) (by norm_num)
theorem B887845 : Blo 786339 887845 := bbase (se 4 (by rfl) ⟨83235, by rfl⟩ : syracuseStep 887845 = 166471) (by norm_num)
theorem B1182773 : Blo 786339 1182773 := bbase (se 5 (by rfl) ⟨55442, by rfl⟩ : syracuseStep 1182773 = 110885) (by norm_num)
theorem B5999669 : Blo 786339 5999669 := bbase (se 5 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 5999669 = 562469) (by norm_num)
theorem B887881 : Blo 786339 887881 := bbase (se 2 (by rfl) ⟨332955, by rfl⟩ : syracuseStep 887881 = 665911) (by norm_num)
theorem B1772621 : Blo 786339 1772621 := bbase (se 3 (by rfl) ⟨332366, by rfl⟩ : syracuseStep 1772621 = 664733) (by norm_num)
theorem B1182797 : Blo 786339 1182797 := bbase (se 3 (by rfl) ⟨221774, by rfl⟩ : syracuseStep 1182797 = 443549) (by norm_num)
theorem B1182821 : Blo 786339 1182821 := bbase (se 4 (by rfl) ⟨110889, by rfl⟩ : syracuseStep 1182821 = 221779) (by norm_num)
theorem B887917 : Blo 786339 887917 := bbase (se 3 (by rfl) ⟨166484, by rfl⟩ : syracuseStep 887917 = 332969) (by norm_num)
theorem B1182845 : Blo 786339 1182845 := bbase (se 3 (by rfl) ⟨221783, by rfl⟩ : syracuseStep 1182845 = 443567) (by norm_num)
theorem B887953 : Blo 786339 887953 := bbase (se 2 (by rfl) ⟨332982, by rfl⟩ : syracuseStep 887953 = 665965) (by norm_num)
theorem B1772693 : Blo 786339 1772693 := bbase (se 6 (by rfl) ⟨41547, by rfl⟩ : syracuseStep 1772693 = 83095) (by norm_num)
theorem B1182869 : Blo 786339 1182869 := bbase (se 6 (by rfl) ⟨27723, by rfl⟩ : syracuseStep 1182869 = 55447) (by norm_num)
theorem B1182893 : Blo 786339 1182893 := bbase (se 3 (by rfl) ⟨221792, by rfl⟩ : syracuseStep 1182893 = 443585) (by norm_num)
theorem B887989 : Blo 786339 887989 := bbase (se 5 (by rfl) ⟨41624, by rfl⟩ : syracuseStep 887989 = 83249) (by norm_num)
theorem B1182917 : Blo 786339 1182917 := bbase (se 4 (by rfl) ⟨110898, by rfl⟩ : syracuseStep 1182917 = 221797) (by norm_num)
theorem B888025 : Blo 786339 888025 := bbase (se 2 (by rfl) ⟨333009, by rfl⟩ : syracuseStep 888025 = 666019) (by norm_num)
theorem B1772765 : Blo 786339 1772765 := bbase (se 3 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 1772765 = 664787) (by norm_num)
theorem B1182941 : Blo 786339 1182941 := bbase (se 3 (by rfl) ⟨221801, by rfl⟩ : syracuseStep 1182941 = 443603) (by norm_num)
theorem B1182965 : Blo 786339 1182965 := bbase (se 5 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 1182965 = 110903) (by norm_num)
theorem B888061 : Blo 786339 888061 := bbase (se 3 (by rfl) ⟨166511, by rfl⟩ : syracuseStep 888061 = 333023) (by norm_num)
theorem B1182989 : Blo 786339 1182989 := bbase (se 3 (by rfl) ⟨221810, by rfl⟩ : syracuseStep 1182989 = 443621) (by norm_num)
theorem B888097 : Blo 786339 888097 := bbase (se 2 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 888097 = 666073) (by norm_num)
theorem B1772837 : Blo 786339 1772837 := bbase (se 4 (by rfl) ⟨166203, by rfl⟩ : syracuseStep 1772837 = 332407) (by norm_num)
theorem B1183013 : Blo 786339 1183013 := bbase (se 4 (by rfl) ⟨110907, by rfl⟩ : syracuseStep 1183013 = 221815) (by norm_num)
theorem B1183037 : Blo 786339 1183037 := bbase (se 3 (by rfl) ⟨221819, by rfl⟩ : syracuseStep 1183037 = 443639) (by norm_num)
theorem B888133 : Blo 786339 888133 := bbase (se 4 (by rfl) ⟨83262, by rfl⟩ : syracuseStep 888133 = 166525) (by norm_num)
theorem B1183061 : Blo 786339 1183061 := bbase (se 11 (by rfl) ⟨866, by rfl⟩ : syracuseStep 1183061 = 1733) (by norm_num)
theorem B888169 : Blo 786339 888169 := bbase (se 2 (by rfl) ⟨333063, by rfl⟩ : syracuseStep 888169 = 666127) (by norm_num)
theorem B1772909 : Blo 786339 1772909 := bbase (se 3 (by rfl) ⟨332420, by rfl⟩ : syracuseStep 1772909 = 664841) (by norm_num)
theorem B1183085 : Blo 786339 1183085 := bbase (se 3 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 1183085 = 443657) (by norm_num)
theorem B1183109 : Blo 786339 1183109 := bbase (se 4 (by rfl) ⟨110916, by rfl⟩ : syracuseStep 1183109 = 221833) (by norm_num)
theorem B888205 : Blo 786339 888205 := bbase (se 3 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 888205 = 333077) (by norm_num)
theorem B1183133 : Blo 786339 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B888241 : Blo 786339 888241 := bbase (se 2 (by rfl) ⟨333090, by rfl⟩ : syracuseStep 888241 = 666181) (by norm_num)
theorem B2657717 : Blo 786339 2657717 := bbase (se 5 (by rfl) ⟨124580, by rfl⟩ : syracuseStep 2657717 = 249161) (by norm_num)
theorem B1772981 : Blo 786339 1772981 := bbase (se 5 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 1772981 = 166217) (by norm_num)
theorem B1183157 : Blo 786339 1183157 := bbase (se 5 (by rfl) ⟨55460, by rfl⟩ : syracuseStep 1183157 = 110921) (by norm_num)
theorem B1183181 : Blo 786339 1183181 := bbase (se 3 (by rfl) ⟨221846, by rfl⟩ : syracuseStep 1183181 = 443693) (by norm_num)
theorem B888277 : Blo 786339 888277 := bbase (se 7 (by rfl) ⟨10409, by rfl⟩ : syracuseStep 888277 = 20819) (by norm_num)
theorem B1183205 : Blo 786339 1183205 := bbase (se 4 (by rfl) ⟨110925, by rfl⟩ : syracuseStep 1183205 = 221851) (by norm_num)
theorem B888313 : Blo 786339 888313 := bbase (se 2 (by rfl) ⟨333117, by rfl⟩ : syracuseStep 888313 = 666235) (by norm_num)
theorem B1773053 : Blo 786339 1773053 := bbase (se 3 (by rfl) ⟨332447, by rfl⟩ : syracuseStep 1773053 = 664895) (by norm_num)
theorem B1183229 : Blo 786339 1183229 := bbase (se 3 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 1183229 = 443711) (by norm_num)
theorem B1183253 : Blo 786339 1183253 := bbase (se 6 (by rfl) ⟨27732, by rfl⟩ : syracuseStep 1183253 = 55465) (by norm_num)
theorem B888349 : Blo 786339 888349 := bbase (se 3 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 888349 = 333131) (by norm_num)
theorem B1183277 : Blo 786339 1183277 := bbase (se 3 (by rfl) ⟨221864, by rfl⟩ : syracuseStep 1183277 = 443729) (by norm_num)
theorem B888385 : Blo 786339 888385 := bbase (se 2 (by rfl) ⟨333144, by rfl⟩ : syracuseStep 888385 = 666289) (by norm_num)
theorem B1773125 : Blo 786339 1773125 := bbase (se 4 (by rfl) ⟨166230, by rfl⟩ : syracuseStep 1773125 = 332461) (by norm_num)
theorem B1183301 : Blo 786339 1183301 := bbase (se 4 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 1183301 = 221869) (by norm_num)
theorem B2526805 : Blo 786339 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B1183325 : Blo 786339 1183325 := bbase (se 3 (by rfl) ⟨221873, by rfl⟩ : syracuseStep 1183325 = 443747) (by norm_num)
theorem B888421 : Blo 786339 888421 := bbase (se 4 (by rfl) ⟨83289, by rfl⟩ : syracuseStep 888421 = 166579) (by norm_num)
theorem B1183349 : Blo 786339 1183349 := bbase (se 5 (by rfl) ⟨55469, by rfl⟩ : syracuseStep 1183349 = 110939) (by norm_num)
theorem B888457 : Blo 786339 888457 := bbase (se 2 (by rfl) ⟨333171, by rfl⟩ : syracuseStep 888457 = 666343) (by norm_num)
theorem B1773197 : Blo 786339 1773197 := bbase (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) (by norm_num)
theorem B1183373 : Blo 786339 1183373 := bbase (se 3 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 1183373 = 443765) (by norm_num)
theorem B1183397 : Blo 786339 1183397 := bbase (se 4 (by rfl) ⟨110943, by rfl⟩ : syracuseStep 1183397 = 221887) (by norm_num)
theorem B888493 : Blo 786339 888493 := bbase (se 3 (by rfl) ⟨166592, by rfl⟩ : syracuseStep 888493 = 333185) (by norm_num)
theorem B1183421 : Blo 786339 1183421 := bbase (se 3 (by rfl) ⟨221891, by rfl⟩ : syracuseStep 1183421 = 443783) (by norm_num)
theorem B888529 : Blo 786339 888529 := bbase (se 2 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 888529 = 666397) (by norm_num)
theorem B1773269 : Blo 786339 1773269 := bbase (se 7 (by rfl) ⟨20780, by rfl⟩ : syracuseStep 1773269 = 41561) (by norm_num)
theorem B1183445 : Blo 786339 1183445 := bbase (se 7 (by rfl) ⟨13868, by rfl⟩ : syracuseStep 1183445 = 27737) (by norm_num)
theorem B1183469 : Blo 786339 1183469 := bbase (se 3 (by rfl) ⟨221900, by rfl⟩ : syracuseStep 1183469 = 443801) (by norm_num)
theorem B888565 : Blo 786339 888565 := bbase (se 5 (by rfl) ⟨41651, by rfl⟩ : syracuseStep 888565 = 83303) (by norm_num)
theorem B1183493 : Blo 786339 1183493 := bbase (se 4 (by rfl) ⟨110952, by rfl⟩ : syracuseStep 1183493 = 221905) (by norm_num)
theorem B888601 : Blo 786339 888601 := bbase (se 2 (by rfl) ⟨333225, by rfl⟩ : syracuseStep 888601 = 666451) (by norm_num)
theorem B1773341 : Blo 786339 1773341 := bbase (se 3 (by rfl) ⟨332501, by rfl⟩ : syracuseStep 1773341 = 665003) (by norm_num)
theorem B1183517 : Blo 786339 1183517 := bbase (se 3 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 1183517 = 443819) (by norm_num)
theorem B1183541 : Blo 786339 1183541 := bbase (se 5 (by rfl) ⟨55478, by rfl⟩ : syracuseStep 1183541 = 110957) (by norm_num)
theorem B888637 : Blo 786339 888637 := bbase (se 3 (by rfl) ⟨166619, by rfl⟩ : syracuseStep 888637 = 333239) (by norm_num)
theorem B1183565 : Blo 786339 1183565 := bbase (se 3 (by rfl) ⟨221918, by rfl⟩ : syracuseStep 1183565 = 443837) (by norm_num)
theorem B888673 : Blo 786339 888673 := bbase (se 2 (by rfl) ⟨333252, by rfl⟩ : syracuseStep 888673 = 666505) (by norm_num)
theorem B2658149 : Blo 786339 2658149 := bbase (se 4 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 2658149 = 498403) (by norm_num)
theorem B1773413 : Blo 786339 1773413 := bbase (se 4 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 1773413 = 332515) (by norm_num)
theorem B1183589 : Blo 786339 1183589 := bbase (se 4 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 1183589 = 221923) (by norm_num)
theorem B1183613 : Blo 786339 1183613 := bbase (se 3 (by rfl) ⟨221927, by rfl⟩ : syracuseStep 1183613 = 443855) (by norm_num)
theorem B888709 : Blo 786339 888709 := bbase (se 4 (by rfl) ⟨83316, by rfl⟩ : syracuseStep 888709 = 166633) (by norm_num)
theorem B1183637 : Blo 786339 1183637 := bbase (se 6 (by rfl) ⟨27741, by rfl⟩ : syracuseStep 1183637 = 55483) (by norm_num)
theorem B2985893 : Blo 786339 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B888745 : Blo 786339 888745 := bbase (se 2 (by rfl) ⟨333279, by rfl⟩ : syracuseStep 888745 = 666559) (by norm_num)
theorem B1773485 : Blo 786339 1773485 := bbase (se 3 (by rfl) ⟨332528, by rfl⟩ : syracuseStep 1773485 = 665057) (by norm_num)
theorem B1183661 : Blo 786339 1183661 := bbase (se 3 (by rfl) ⟨221936, by rfl⟩ : syracuseStep 1183661 = 443873) (by norm_num)
theorem B1183685 : Blo 786339 1183685 := bbase (se 4 (by rfl) ⟨110970, by rfl⟩ : syracuseStep 1183685 = 221941) (by norm_num)
theorem B888781 : Blo 786339 888781 := bbase (se 3 (by rfl) ⟨166646, by rfl⟩ : syracuseStep 888781 = 333293) (by norm_num)
theorem B1183709 : Blo 786339 1183709 := bbase (se 3 (by rfl) ⟨221945, by rfl⟩ : syracuseStep 1183709 = 443891) (by norm_num)
theorem B888817 : Blo 786339 888817 := bbase (se 2 (by rfl) ⟨333306, by rfl⟩ : syracuseStep 888817 = 666613) (by norm_num)
theorem B1773557 : Blo 786339 1773557 := bbase (se 5 (by rfl) ⟨83135, by rfl⟩ : syracuseStep 1773557 = 166271) (by norm_num)
theorem B1183733 : Blo 786339 1183733 := bbase (se 5 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 1183733 = 110975) (by norm_num)
theorem B1183757 : Blo 786339 1183757 := bbase (se 3 (by rfl) ⟨221954, by rfl⟩ : syracuseStep 1183757 = 443909) (by norm_num)
theorem B888853 : Blo 786339 888853 := bbase (se 6 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 888853 = 41665) (by norm_num)
theorem B1183781 : Blo 786339 1183781 := bbase (se 4 (by rfl) ⟨110979, by rfl⟩ : syracuseStep 1183781 = 221959) (by norm_num)
theorem B888889 : Blo 786339 888889 := bbase (se 2 (by rfl) ⟨333333, by rfl⟩ : syracuseStep 888889 = 666667) (by norm_num)
theorem B1773629 : Blo 786339 1773629 := bbase (se 3 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 1773629 = 665111) (by norm_num)
theorem B1183805 : Blo 786339 1183805 := bbase (se 3 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 1183805 = 443927) (by norm_num)
theorem B1183829 : Blo 786339 1183829 := bbase (se 8 (by rfl) ⟨6936, by rfl⟩ : syracuseStep 1183829 = 13873) (by norm_num)
theorem B888925 : Blo 786339 888925 := bbase (se 3 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 888925 = 333347) (by norm_num)
theorem B1183853 : Blo 786339 1183853 := bbase (se 3 (by rfl) ⟨221972, by rfl⟩ : syracuseStep 1183853 = 443945) (by norm_num)
theorem B888961 : Blo 786339 888961 := bbase (se 2 (by rfl) ⟨333360, by rfl⟩ : syracuseStep 888961 = 666721) (by norm_num)
theorem B1773701 : Blo 786339 1773701 := bbase (se 4 (by rfl) ⟨166284, by rfl⟩ : syracuseStep 1773701 = 332569) (by norm_num)
theorem B1183877 : Blo 786339 1183877 := bbase (se 4 (by rfl) ⟨110988, by rfl⟩ : syracuseStep 1183877 = 221977) (by norm_num)
theorem B1183901 : Blo 786339 1183901 := bbase (se 3 (by rfl) ⟨221981, by rfl⟩ : syracuseStep 1183901 = 443963) (by norm_num)
theorem B888997 : Blo 786339 888997 := bbase (se 4 (by rfl) ⟨83343, by rfl⟩ : syracuseStep 888997 = 166687) (by norm_num)
theorem B1183925 : Blo 786339 1183925 := bbase (se 5 (by rfl) ⟨55496, by rfl⟩ : syracuseStep 1183925 = 110993) (by norm_num)
theorem B889033 : Blo 786339 889033 := bbase (se 2 (by rfl) ⟨333387, by rfl⟩ : syracuseStep 889033 = 666775) (by norm_num)
theorem B1773773 : Blo 786339 1773773 := bbase (se 3 (by rfl) ⟨332582, by rfl⟩ : syracuseStep 1773773 = 665165) (by norm_num)
theorem B1183949 : Blo 786339 1183949 := bbase (se 3 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 1183949 = 443981) (by norm_num)
theorem B1183973 : Blo 786339 1183973 := bbase (se 4 (by rfl) ⟨110997, by rfl⟩ : syracuseStep 1183973 = 221995) (by norm_num)
theorem B889069 : Blo 786339 889069 := bbase (se 3 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 889069 = 333401) (by norm_num)
theorem B1183997 : Blo 786339 1183997 := bbase (se 3 (by rfl) ⟨221999, by rfl⟩ : syracuseStep 1183997 = 443999) (by norm_num)
theorem B889105 : Blo 786339 889105 := bbase (se 2 (by rfl) ⟨333414, by rfl⟩ : syracuseStep 889105 = 666829) (by norm_num)
theorem B2658581 : Blo 786339 2658581 := bbase (se 6 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 2658581 = 124621) (by norm_num)
theorem B1773845 : Blo 786339 1773845 := bbase (se 6 (by rfl) ⟨41574, by rfl⟩ : syracuseStep 1773845 = 83149) (by norm_num)
theorem B1184021 : Blo 786339 1184021 := bbase (se 6 (by rfl) ⟨27750, by rfl⟩ : syracuseStep 1184021 = 55501) (by norm_num)
theorem B1184045 : Blo 786339 1184045 := bbase (se 3 (by rfl) ⟨222008, by rfl⟩ : syracuseStep 1184045 = 444017) (by norm_num)
theorem B1184069 : Blo 786339 1184069 := bbase (se 4 (by rfl) ⟨111006, by rfl⟩ : syracuseStep 1184069 = 222013) (by norm_num)
theorem B1773917 : Blo 786339 1773917 := bbase (se 3 (by rfl) ⟨332609, by rfl⟩ : syracuseStep 1773917 = 665219) (by norm_num)
theorem B1184093 : Blo 786339 1184093 := bbase (se 3 (by rfl) ⟨222017, by rfl⟩ : syracuseStep 1184093 = 444035) (by norm_num)
theorem B1184117 : Blo 786339 1184117 := bbase (se 5 (by rfl) ⟨55505, by rfl⟩ : syracuseStep 1184117 = 111011) (by norm_num)
theorem B1184141 : Blo 786339 1184141 := bbase (se 3 (by rfl) ⟨222026, by rfl⟩ : syracuseStep 1184141 = 444053) (by norm_num)
theorem B4493717 : Blo 786339 4493717 := bbase (se 6 (by rfl) ⟨105321, by rfl⟩ : syracuseStep 4493717 = 210643) (by norm_num)
theorem B1773989 : Blo 786339 1773989 := bbase (se 4 (by rfl) ⟨166311, by rfl⟩ : syracuseStep 1773989 = 332623) (by norm_num)
theorem B1184165 : Blo 786339 1184165 := bbase (se 4 (by rfl) ⟨111015, by rfl⟩ : syracuseStep 1184165 = 222031) (by norm_num)
theorem B1184189 : Blo 786339 1184189 := bbase (se 3 (by rfl) ⟨222035, by rfl⟩ : syracuseStep 1184189 = 444071) (by norm_num)
theorem B1184213 : Blo 786339 1184213 := bbase (se 7 (by rfl) ⟨13877, by rfl⟩ : syracuseStep 1184213 = 27755) (by norm_num)
theorem B1774061 : Blo 786339 1774061 := bbase (se 3 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 1774061 = 665273) (by norm_num)
theorem B1184237 : Blo 786339 1184237 := bbase (se 3 (by rfl) ⟨222044, by rfl⟩ : syracuseStep 1184237 = 444089) (by norm_num)
theorem B1184261 : Blo 786339 1184261 := bbase (se 4 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 1184261 = 222049) (by norm_num)
theorem B1184285 : Blo 786339 1184285 := bbase (se 3 (by rfl) ⟨222053, by rfl⟩ : syracuseStep 1184285 = 444107) (by norm_num)
theorem B1774133 : Blo 786339 1774133 := bbase (se 5 (by rfl) ⟨83162, by rfl⟩ : syracuseStep 1774133 = 166325) (by norm_num)
theorem B1184309 : Blo 786339 1184309 := bbase (se 5 (by rfl) ⟨55514, by rfl⟩ : syracuseStep 1184309 = 111029) (by norm_num)
theorem B1184333 : Blo 786339 1184333 := bbase (se 3 (by rfl) ⟨222062, by rfl⟩ : syracuseStep 1184333 = 444125) (by norm_num)
theorem B1184357 : Blo 786339 1184357 := bbase (se 4 (by rfl) ⟨111033, by rfl⟩ : syracuseStep 1184357 = 222067) (by norm_num)
theorem B1774205 : Blo 786339 1774205 := bbase (se 3 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 1774205 = 665327) (by norm_num)
theorem B1184381 : Blo 786339 1184381 := bbase (se 3 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 1184381 = 444143) (by norm_num)
theorem B1184405 : Blo 786339 1184405 := bbase (se 6 (by rfl) ⟨27759, by rfl⟩ : syracuseStep 1184405 = 55519) (by norm_num)
theorem B1184429 : Blo 786339 1184429 := bbase (se 3 (by rfl) ⟨222080, by rfl⟩ : syracuseStep 1184429 = 444161) (by norm_num)
theorem B2659013 : Blo 786339 2659013 := bbase (se 4 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 2659013 = 498565) (by norm_num)
theorem B1774277 : Blo 786339 1774277 := bbase (se 4 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 1774277 = 332677) (by norm_num)
theorem B1184453 : Blo 786339 1184453 := bbase (se 4 (by rfl) ⟨111042, by rfl⟩ : syracuseStep 1184453 = 222085) (by norm_num)
theorem B1184477 : Blo 786339 1184477 := bbase (se 3 (by rfl) ⟨222089, by rfl⟩ : syracuseStep 1184477 = 444179) (by norm_num)
theorem B1184501 : Blo 786339 1184501 := bbase (se 5 (by rfl) ⟨55523, by rfl⟩ : syracuseStep 1184501 = 111047) (by norm_num)
theorem B1774349 : Blo 786339 1774349 := bbase (se 3 (by rfl) ⟨332690, by rfl⟩ : syracuseStep 1774349 = 665381) (by norm_num)
theorem B1184525 : Blo 786339 1184525 := bbase (se 3 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 1184525 = 444197) (by norm_num)
theorem B1184549 : Blo 786339 1184549 := bbase (se 4 (by rfl) ⟨111051, by rfl⟩ : syracuseStep 1184549 = 222103) (by norm_num)
theorem B2134837 : Blo 786339 2134837 := bbase (se 5 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 2134837 = 200141) (by norm_num)
theorem B1184573 : Blo 786339 1184573 := bbase (se 3 (by rfl) ⟨222107, by rfl⟩ : syracuseStep 1184573 = 444215) (by norm_num)
theorem B1774421 : Blo 786339 1774421 := bbase (se 9 (by rfl) ⟨5198, by rfl⟩ : syracuseStep 1774421 = 10397) (by norm_num)
theorem B1184597 : Blo 786339 1184597 := bbase (se 9 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 1184597 = 6941) (by norm_num)
theorem B1184621 : Blo 786339 1184621 := bbase (se 3 (by rfl) ⟨222116, by rfl⟩ : syracuseStep 1184621 = 444233) (by norm_num)
theorem B1184645 : Blo 786339 1184645 := bbase (se 4 (by rfl) ⟨111060, by rfl⟩ : syracuseStep 1184645 = 222121) (by norm_num)
theorem B1774493 : Blo 786339 1774493 := bbase (se 3 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 1774493 = 665435) (by norm_num)
theorem B1184669 : Blo 786339 1184669 := bbase (se 3 (by rfl) ⟨222125, by rfl⟩ : syracuseStep 1184669 = 444251) (by norm_num)
theorem B2528165 : Blo 786339 2528165 := bbase (se 4 (by rfl) ⟨237015, by rfl⟩ : syracuseStep 2528165 = 474031) (by norm_num)
theorem B1184693 : Blo 786339 1184693 := bbase (se 5 (by rfl) ⟨55532, by rfl⟩ : syracuseStep 1184693 = 111065) (by norm_num)
theorem B1184717 : Blo 786339 1184717 := bbase (se 3 (by rfl) ⟨222134, by rfl⟩ : syracuseStep 1184717 = 444269) (by norm_num)
theorem B1774565 : Blo 786339 1774565 := bbase (se 4 (by rfl) ⟨166365, by rfl⟩ : syracuseStep 1774565 = 332731) (by norm_num)
theorem B1184741 : Blo 786339 1184741 := bbase (se 4 (by rfl) ⟨111069, by rfl⟩ : syracuseStep 1184741 = 222139) (by norm_num)
theorem B1184765 : Blo 786339 1184765 := bbase (se 3 (by rfl) ⟨222143, by rfl⟩ : syracuseStep 1184765 = 444287) (by norm_num)
theorem B1184789 : Blo 786339 1184789 := bbase (se 6 (by rfl) ⟨27768, by rfl⟩ : syracuseStep 1184789 = 55537) (by norm_num)
theorem B2528293 : Blo 786339 2528293 := bbase (se 4 (by rfl) ⟨237027, by rfl⟩ : syracuseStep 2528293 = 474055) (by norm_num)
theorem B1774637 : Blo 786339 1774637 := bbase (se 3 (by rfl) ⟨332744, by rfl⟩ : syracuseStep 1774637 = 665489) (by norm_num)
theorem B1184813 : Blo 786339 1184813 := bbase (se 3 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 1184813 = 444305) (by norm_num)
theorem B2987077 : Blo 786339 2987077 := bbase (se 4 (by rfl) ⟨280038, by rfl⟩ : syracuseStep 2987077 = 560077) (by norm_num)
theorem B1184837 : Blo 786339 1184837 := bbase (se 4 (by rfl) ⟨111078, by rfl⟩ : syracuseStep 1184837 = 222157) (by norm_num)
theorem B1709149 : Blo 786339 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B1184861 : Blo 786339 1184861 := bbase (se 3 (by rfl) ⟨222161, by rfl⟩ : syracuseStep 1184861 = 444323) (by norm_num)
theorem B2659445 : Blo 786339 2659445 := bbase (se 5 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 2659445 = 249323) (by norm_num)
theorem B1774709 : Blo 786339 1774709 := bbase (se 5 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 1774709 = 166379) (by norm_num)
theorem B1184885 : Blo 786339 1184885 := bbase (se 5 (by rfl) ⟨55541, by rfl⟩ : syracuseStep 1184885 = 111083) (by norm_num)
theorem B1184909 : Blo 786339 1184909 := bbase (se 3 (by rfl) ⟨222170, by rfl⟩ : syracuseStep 1184909 = 444341) (by norm_num)
theorem B1184933 : Blo 786339 1184933 := bbase (se 4 (by rfl) ⟨111087, by rfl⟩ : syracuseStep 1184933 = 222175) (by norm_num)
theorem B1774781 : Blo 786339 1774781 := bbase (se 3 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 1774781 = 665543) (by norm_num)
theorem B1184957 : Blo 786339 1184957 := bbase (se 3 (by rfl) ⟨222179, by rfl⟩ : syracuseStep 1184957 = 444359) (by norm_num)
theorem B1184981 : Blo 786339 1184981 := bbase (se 7 (by rfl) ⟨13886, by rfl⟩ : syracuseStep 1184981 = 27773) (by norm_num)
theorem B1185005 : Blo 786339 1185005 := bbase (se 3 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 1185005 = 444377) (by norm_num)
theorem B1774853 : Blo 786339 1774853 := bbase (se 4 (by rfl) ⟨166392, by rfl⟩ : syracuseStep 1774853 = 332785) (by norm_num)
theorem B1185029 : Blo 786339 1185029 := bbase (se 4 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 1185029 = 222193) (by norm_num)
theorem B1185053 : Blo 786339 1185053 := bbase (se 3 (by rfl) ⟨222197, by rfl⟩ : syracuseStep 1185053 = 444395) (by norm_num)
theorem B2528549 : Blo 786339 2528549 := bbase (se 4 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 2528549 = 474103) (by norm_num)
theorem B1185077 : Blo 786339 1185077 := bbase (se 5 (by rfl) ⟨55550, by rfl⟩ : syracuseStep 1185077 = 111101) (by norm_num)
theorem B1774925 : Blo 786339 1774925 := bbase (se 3 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 1774925 = 665597) (by norm_num)
theorem B1185101 : Blo 786339 1185101 := bbase (se 3 (by rfl) ⟨222206, by rfl⟩ : syracuseStep 1185101 = 444413) (by norm_num)
theorem B1185125 : Blo 786339 1185125 := bbase (se 4 (by rfl) ⟨111105, by rfl⟩ : syracuseStep 1185125 = 222211) (by norm_num)
theorem B2987381 : Blo 786339 2987381 := bbase (se 5 (by rfl) ⟨140033, by rfl⟩ : syracuseStep 2987381 = 280067) (by norm_num)
theorem B1185149 : Blo 786339 1185149 := bbase (se 3 (by rfl) ⟨222215, by rfl⟩ : syracuseStep 1185149 = 444431) (by norm_num)
theorem B1774997 : Blo 786339 1774997 := bbase (se 6 (by rfl) ⟨41601, by rfl⟩ : syracuseStep 1774997 = 83203) (by norm_num)
theorem B1185173 : Blo 786339 1185173 := bbase (se 6 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 1185173 = 55555) (by norm_num)
theorem B1185197 : Blo 786339 1185197 := bbase (se 3 (by rfl) ⟨222224, by rfl⟩ : syracuseStep 1185197 = 444449) (by norm_num)
theorem B1185221 : Blo 786339 1185221 := bbase (se 4 (by rfl) ⟨111114, by rfl⟩ : syracuseStep 1185221 = 222229) (by norm_num)
theorem B1775069 : Blo 786339 1775069 := bbase (se 3 (by rfl) ⟨332825, by rfl⟩ : syracuseStep 1775069 = 665651) (by norm_num)
theorem B1185245 : Blo 786339 1185245 := bbase (se 3 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 1185245 = 444467) (by norm_num)
theorem B1185269 : Blo 786339 1185269 := bbase (se 5 (by rfl) ⟨55559, by rfl⟩ : syracuseStep 1185269 = 111119) (by norm_num)
theorem B1185293 : Blo 786339 1185293 := bbase (se 3 (by rfl) ⟨222242, by rfl⟩ : syracuseStep 1185293 = 444485) (by norm_num)
theorem B2659877 : Blo 786339 2659877 := bbase (se 4 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 2659877 = 498727) (by norm_num)
theorem B1775141 : Blo 786339 1775141 := bbase (se 4 (by rfl) ⟨166419, by rfl⟩ : syracuseStep 1775141 = 332839) (by norm_num)
theorem B1185317 : Blo 786339 1185317 := bbase (se 4 (by rfl) ⟨111123, by rfl⟩ : syracuseStep 1185317 = 222247) (by norm_num)
theorem B1185341 : Blo 786339 1185341 := bbase (se 3 (by rfl) ⟨222251, by rfl⟩ : syracuseStep 1185341 = 444503) (by norm_num)
theorem B1185365 : Blo 786339 1185365 := bbase (se 8 (by rfl) ⟨6945, by rfl⟩ : syracuseStep 1185365 = 13891) (by norm_num)
theorem B2692709 : Blo 786339 2692709 := bbase (se 4 (by rfl) ⟨252441, by rfl⟩ : syracuseStep 2692709 = 504883) (by norm_num)
theorem B1775213 : Blo 786339 1775213 := bbase (se 3 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 1775213 = 665705) (by norm_num)
theorem B1185389 : Blo 786339 1185389 := bbase (se 3 (by rfl) ⟨222260, by rfl⟩ : syracuseStep 1185389 = 444521) (by norm_num)
theorem B1185413 : Blo 786339 1185413 := bbase (se 4 (by rfl) ⟨111132, by rfl⟩ : syracuseStep 1185413 = 222265) (by norm_num)
theorem B1185437 : Blo 786339 1185437 := bbase (se 3 (by rfl) ⟨222269, by rfl⟩ : syracuseStep 1185437 = 444539) (by norm_num)
theorem B1775285 : Blo 786339 1775285 := bbase (se 5 (by rfl) ⟨83216, by rfl⟩ : syracuseStep 1775285 = 166433) (by norm_num)
theorem B8099509 : Blo 786339 8099509 := bbase (se 5 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 8099509 = 759329) (by norm_num)
theorem B1185461 : Blo 786339 1185461 := bbase (se 5 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 1185461 = 111137) (by norm_num)
theorem B1185485 : Blo 786339 1185485 := bbase (se 3 (by rfl) ⟨222278, by rfl⟩ : syracuseStep 1185485 = 444557) (by norm_num)
theorem B1185509 : Blo 786339 1185509 := bbase (se 4 (by rfl) ⟨111141, by rfl⟩ : syracuseStep 1185509 = 222283) (by norm_num)
theorem B1775357 : Blo 786339 1775357 := bbase (se 3 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 1775357 = 665759) (by norm_num)
theorem B1775429 : Blo 786339 1775429 := bbase (se 4 (by rfl) ⟨166446, by rfl⟩ : syracuseStep 1775429 = 332893) (by norm_num)
theorem B2135909 : Blo 786339 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B1513333 : Blo 786339 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B1775501 : Blo 786339 1775501 := bbase (se 3 (by rfl) ⟨332906, by rfl⟩ : syracuseStep 1775501 = 665813) (by norm_num)
theorem B2660309 : Blo 786339 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B1775573 : Blo 786339 1775573 := bbase (se 7 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 1775573 = 41615) (by norm_num)
theorem B1775645 : Blo 786339 1775645 := bbase (se 3 (by rfl) ⟨332933, by rfl⟩ : syracuseStep 1775645 = 665867) (by norm_num)
theorem B1775717 : Blo 786339 1775717 := bbase (se 4 (by rfl) ⟨166473, by rfl⟩ : syracuseStep 1775717 = 332947) (by norm_num)
theorem B1120405 : Blo 786339 1120405 := bbase (se 6 (by rfl) ⟨26259, by rfl⟩ : syracuseStep 1120405 = 52519) (by norm_num)
theorem B1775789 : Blo 786339 1775789 := bbase (se 3 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 1775789 = 665921) (by norm_num)
theorem B4856021 : Blo 786339 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B1775861 : Blo 786339 1775861 := bbase (se 5 (by rfl) ⟨83243, by rfl⟩ : syracuseStep 1775861 = 166487) (by norm_num)
theorem B13441301 : Blo 786339 13441301 := bbase (se 6 (by rfl) ⟨315030, by rfl⟩ : syracuseStep 13441301 = 630061) (by norm_num)
theorem B1775933 : Blo 786339 1775933 := bbase (se 3 (by rfl) ⟨332987, by rfl⟩ : syracuseStep 1775933 = 665975) (by norm_num)
theorem B2660741 : Blo 786339 2660741 := bbase (se 4 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 2660741 = 498889) (by norm_num)
theorem B1776005 : Blo 786339 1776005 := bbase (se 4 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 1776005 = 333001) (by norm_num)
theorem B1350029 : Blo 786339 1350029 := bbase (se 3 (by rfl) ⟨253130, by rfl⟩ : syracuseStep 1350029 = 506261) (by norm_num)
theorem B1776077 : Blo 786339 1776077 := bbase (se 3 (by rfl) ⟨333014, by rfl⟩ : syracuseStep 1776077 = 666029) (by norm_num)
theorem B1776149 : Blo 786339 1776149 := bbase (se 6 (by rfl) ⟨41628, by rfl⟩ : syracuseStep 1776149 = 83257) (by norm_num)
theorem B4495925 : Blo 786339 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B1776221 : Blo 786339 1776221 := bbase (se 3 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 1776221 = 666083) (by norm_num)
theorem B6396565 : Blo 786339 6396565 := bbase (se 6 (by rfl) ⟨149919, by rfl⟩ : syracuseStep 6396565 = 299839) (by norm_num)
theorem B1776293 : Blo 786339 1776293 := bbase (se 4 (by rfl) ⟨166527, by rfl⟩ : syracuseStep 1776293 = 333055) (by norm_num)
theorem B1120997 : Blo 786339 1120997 := bbase (se 4 (by rfl) ⟨105093, by rfl⟩ : syracuseStep 1120997 = 210187) (by norm_num)
theorem B1776365 : Blo 786339 1776365 := bbase (se 3 (by rfl) ⟨333068, by rfl⟩ : syracuseStep 1776365 = 666137) (by norm_num)
theorem B1121077 : Blo 786339 1121077 := bbase (se 5 (by rfl) ⟨52550, by rfl⟩ : syracuseStep 1121077 = 105101) (by norm_num)
theorem B2661173 : Blo 786339 2661173 := bbase (se 5 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 2661173 = 249485) (by norm_num)
theorem B1776437 : Blo 786339 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B1776509 : Blo 786339 1776509 := bbase (se 3 (by rfl) ⟨333095, by rfl⟩ : syracuseStep 1776509 = 666191) (by norm_num)
theorem B11344789 : Blo 786339 11344789 := bbase (se 6 (by rfl) ⟨265893, by rfl⟩ : syracuseStep 11344789 = 531787) (by norm_num)
theorem B1121197 : Blo 786339 1121197 := bbase (se 3 (by rfl) ⟨210224, by rfl⟩ : syracuseStep 1121197 = 420449) (by norm_num)
theorem B1776581 : Blo 786339 1776581 := bbase (se 4 (by rfl) ⟨166554, by rfl⟩ : syracuseStep 1776581 = 333109) (by norm_num)
theorem B1121293 : Blo 786339 1121293 := bbase (se 3 (by rfl) ⟨210242, by rfl⟩ : syracuseStep 1121293 = 420485) (by norm_num)
theorem B1776653 : Blo 786339 1776653 := bbase (se 3 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 1776653 = 666245) (by norm_num)
theorem B1350685 : Blo 786339 1350685 := bbase (se 3 (by rfl) ⟨253253, by rfl⟩ : syracuseStep 1350685 = 506507) (by norm_num)
theorem B5676085 : Blo 786339 5676085 := bbase (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) (by norm_num)
theorem B1776725 : Blo 786339 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B5053589 : Blo 786339 5053589 := bbase (se 6 (by rfl) ⟨118443, by rfl⟩ : syracuseStep 5053589 = 236887) (by norm_num)
theorem B1776797 : Blo 786339 1776797 := bbase (se 3 (by rfl) ⟨333149, by rfl⟩ : syracuseStep 1776797 = 666299) (by norm_num)
theorem B1350877 : Blo 786339 1350877 := bbase (se 3 (by rfl) ⟨253289, by rfl⟩ : syracuseStep 1350877 = 506579) (by norm_num)
theorem B2661605 : Blo 786339 2661605 := bbase (se 4 (by rfl) ⟨249525, by rfl⟩ : syracuseStep 2661605 = 499051) (by norm_num)
theorem B1776869 : Blo 786339 1776869 := bbase (se 4 (by rfl) ⟨166581, by rfl⟩ : syracuseStep 1776869 = 333163) (by norm_num)
theorem B957673 : Blo 786339 957673 := bbase (se 2 (by rfl) ⟨359127, by rfl⟩ : syracuseStep 957673 = 718255) (by norm_num)
theorem B1776941 : Blo 786339 1776941 := bbase (se 3 (by rfl) ⟨333176, by rfl⟩ : syracuseStep 1776941 = 666353) (by norm_num)
theorem B1777013 : Blo 786339 1777013 := bbase (se 5 (by rfl) ⟨83297, by rfl⟩ : syracuseStep 1777013 = 166595) (by norm_num)
theorem B2989493 : Blo 786339 2989493 := bbase (se 5 (by rfl) ⟨140132, by rfl⟩ : syracuseStep 2989493 = 280265) (by norm_num)
theorem B1777085 : Blo 786339 1777085 := bbase (se 3 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 1777085 = 666407) (by norm_num)
theorem B1121789 : Blo 786339 1121789 := bbase (se 3 (by rfl) ⟨210335, by rfl⟩ : syracuseStep 1121789 = 420671) (by norm_num)
theorem B1777157 : Blo 786339 1777157 := bbase (se 4 (by rfl) ⟨166608, by rfl⟩ : syracuseStep 1777157 = 333217) (by norm_num)
theorem B1777229 : Blo 786339 1777229 := bbase (se 3 (by rfl) ⟨333230, by rfl⟩ : syracuseStep 1777229 = 666461) (by norm_num)
theorem B2662037 : Blo 786339 2662037 := bbase (se 6 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 2662037 = 124783) (by norm_num)
theorem B1777301 : Blo 786339 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B2530997 : Blo 786339 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B3546821 : Blo 786339 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2989781 : Blo 786339 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B1777373 : Blo 786339 1777373 := bbase (se 3 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 1777373 = 666515) (by norm_num)
theorem B1777445 : Blo 786339 1777445 := bbase (se 4 (by rfl) ⟨166635, by rfl⟩ : syracuseStep 1777445 = 333271) (by norm_num)
theorem B1417061 : Blo 786339 1417061 := bbase (se 4 (by rfl) ⟨132849, by rfl⟩ : syracuseStep 1417061 = 265699) (by norm_num)
theorem B1777517 : Blo 786339 1777517 := bbase (se 3 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 1777517 = 666569) (by norm_num)
theorem B1777589 : Blo 786339 1777589 := bbase (se 5 (by rfl) ⟨83324, by rfl⟩ : syracuseStep 1777589 = 166649) (by norm_num)
theorem B2400245 : Blo 786339 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B1777661 : Blo 786339 1777661 := bbase (se 3 (by rfl) ⟨333311, by rfl⟩ : syracuseStep 1777661 = 666623) (by norm_num)
theorem B1122341 : Blo 786339 1122341 := bbase (se 4 (by rfl) ⟨105219, by rfl⟩ : syracuseStep 1122341 = 210439) (by norm_num)
theorem B1679429 : Blo 786339 1679429 := bbase (se 4 (by rfl) ⟨157446, by rfl⟩ : syracuseStep 1679429 = 314893) (by norm_num)
theorem B2662469 : Blo 786339 2662469 := bbase (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) (by norm_num)
theorem B1777733 : Blo 786339 1777733 := bbase (se 4 (by rfl) ⟨166662, by rfl⟩ : syracuseStep 1777733 = 333325) (by norm_num)
theorem B16162901 : Blo 786339 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B1777805 : Blo 786339 1777805 := bbase (se 3 (by rfl) ⟨333338, by rfl⟩ : syracuseStep 1777805 = 666677) (by norm_num)
theorem B1351829 : Blo 786339 1351829 := bbase (se 6 (by rfl) ⟨31683, by rfl⟩ : syracuseStep 1351829 = 63367) (by norm_num)
theorem B2695349 : Blo 786339 2695349 := bbase (se 5 (by rfl) ⟨126344, by rfl⟩ : syracuseStep 2695349 = 252689) (by norm_num)
theorem B1777877 : Blo 786339 1777877 := bbase (se 7 (by rfl) ⟨20834, by rfl⟩ : syracuseStep 1777877 = 41669) (by norm_num)
theorem B1515781 : Blo 786339 1515781 := bbase (se 4 (by rfl) ⟨142104, by rfl⟩ : syracuseStep 1515781 = 284209) (by norm_num)
theorem B1777949 : Blo 786339 1777949 := bbase (se 3 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 1777949 = 666731) (by norm_num)
theorem B1778021 : Blo 786339 1778021 := bbase (se 4 (by rfl) ⟨166689, by rfl⟩ : syracuseStep 1778021 = 333379) (by norm_num)
theorem B1778093 : Blo 786339 1778093 := bbase (se 3 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 1778093 = 666785) (by norm_num)
theorem B2662901 : Blo 786339 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B1778165 : Blo 786339 1778165 := bbase (se 5 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 1778165 = 166703) (by norm_num)
theorem B1778237 : Blo 786339 1778237 := bbase (se 3 (by rfl) ⟨333419, by rfl⟩ : syracuseStep 1778237 = 666839) (by norm_num)
theorem B1680061 : Blo 786339 1680061 := bbase (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) (by norm_num)
theorem B1516229 : Blo 786339 1516229 := bbase (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) (by norm_num)
theorem B1123093 : Blo 786339 1123093 := bbase (se 6 (by rfl) ⟨26322, by rfl⟩ : syracuseStep 1123093 = 52645) (by norm_num)
theorem B2990965 : Blo 786339 2990965 := bbase (se 5 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 2990965 = 280403) (by norm_num)
theorem B2663333 : Blo 786339 2663333 := bbase (se 4 (by rfl) ⟨249687, by rfl⟩ : syracuseStep 2663333 = 499375) (by norm_num)
theorem B2991269 : Blo 786339 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B2663765 : Blo 786339 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B1123885 : Blo 786339 1123885 := bbase (se 3 (by rfl) ⟨210728, by rfl⟩ : syracuseStep 1123885 = 421457) (by norm_num)
theorem B1680949 : Blo 786339 1680949 := bbase (se 5 (by rfl) ⟨78794, by rfl⟩ : syracuseStep 1680949 = 157589) (by norm_num)
theorem B960169 : Blo 786339 960169 := bbase (se 2 (by rfl) ⟨360063, by rfl⟩ : syracuseStep 960169 = 720127) (by norm_num)
theorem B1681069 : Blo 786339 1681069 := bbase (se 3 (by rfl) ⟨315200, by rfl⟩ : syracuseStep 1681069 = 630401) (by norm_num)
theorem B7186133 : Blo 786339 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B2664197 : Blo 786339 2664197 := bbase (se 4 (by rfl) ⟨249768, by rfl⟩ : syracuseStep 2664197 = 499537) (by norm_num)
theorem B1124221 : Blo 786339 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B1681325 : Blo 786339 1681325 := bbase (se 3 (by rfl) ⟨315248, by rfl⟩ : syracuseStep 1681325 = 630497) (by norm_num)
theorem B1124437 : Blo 786339 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B2664629 : Blo 786339 2664629 := bbase (se 5 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 2664629 = 249809) (by norm_num)
theorem B5056789 : Blo 786339 5056789 := bbase (se 6 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 5056789 = 237037) (by norm_num)
theorem B1124813 : Blo 786339 1124813 := bbase (se 3 (by rfl) ⟨210902, by rfl⟩ : syracuseStep 1124813 = 421805) (by norm_num)
theorem B2599445 : Blo 786339 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B2665061 : Blo 786339 2665061 := bbase (se 4 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 2665061 = 499699) (by norm_num)
theorem B797321 : Blo 786339 797321 := bbase (se 2 (by rfl) ⟨298995, by rfl⟩ : syracuseStep 797321 = 597991) (by norm_num)
theorem B1682213 : Blo 786339 1682213 := bbase (se 4 (by rfl) ⟨157707, by rfl⟩ : syracuseStep 1682213 = 315415) (by norm_num)
theorem B3189557 : Blo 786339 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2239397 : Blo 786339 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B1682453 : Blo 786339 1682453 := bbase (se 6 (by rfl) ⟨39432, by rfl⟩ : syracuseStep 1682453 = 78865) (by norm_num)
theorem B2665493 : Blo 786339 2665493 := bbase (se 6 (by rfl) ⟨62472, by rfl⟩ : syracuseStep 2665493 = 124945) (by norm_num)
theorem B4500629 : Blo 786339 4500629 := bbase (se 6 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 4500629 = 210967) (by norm_num)
theorem B2993381 : Blo 786339 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B797969 : Blo 786339 797969 := bbase (se 2 (by rfl) ⟨299238, by rfl⟩ : syracuseStep 797969 = 598477) (by norm_num)
theorem B1420573 : Blo 786339 1420573 := bbase (se 3 (by rfl) ⟨266357, by rfl⟩ : syracuseStep 1420573 = 532715) (by norm_num)
theorem B32320853 : Blo 786339 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B2665925 : Blo 786339 2665925 := bbase (se 4 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 2665925 = 499861) (by norm_num)
theorem B2993669 : Blo 786339 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B1682957 : Blo 786339 1682957 := bbase (se 3 (by rfl) ⟨315554, by rfl⟩ : syracuseStep 1682957 = 631109) (by norm_num)
theorem B1682965 : Blo 786339 1682965 := bbase (se 6 (by rfl) ⟨39444, by rfl⟩ : syracuseStep 1682965 = 78889) (by norm_num)
theorem B2240149 : Blo 786339 2240149 := bbase (se 6 (by rfl) ⟨52503, by rfl⟩ : syracuseStep 2240149 = 105007) (by norm_num)
theorem B12136085 : Blo 786339 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B1421069 : Blo 786339 1421069 := bbase (se 3 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 1421069 = 532901) (by norm_num)
theorem B2273093 : Blo 786339 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B896881 : Blo 786339 896881 := bbase (se 2 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 896881 = 672661) (by norm_num)
theorem B2666357 : Blo 786339 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B995257 : Blo 786339 995257 := bbase (se 2 (by rfl) ⟨373221, by rfl⟩ : syracuseStep 995257 = 746443) (by norm_num)
theorem B995429 : Blo 786339 995429 := bbase (se 4 (by rfl) ⟨93321, by rfl⟩ : syracuseStep 995429 = 186643) (by norm_num)
theorem B995485 : Blo 786339 995485 := bbase (se 3 (by rfl) ⟨186653, by rfl⟩ : syracuseStep 995485 = 373307) (by norm_num)
theorem B798881 : Blo 786339 798881 := bbase (se 2 (by rfl) ⟨299580, by rfl⟩ : syracuseStep 798881 = 599161) (by norm_num)
theorem B995581 : Blo 786339 995581 := bbase (se 3 (by rfl) ⟨186671, by rfl⟩ : syracuseStep 995581 = 373343) (by norm_num)
theorem B5976341 : Blo 786339 5976341 := bbase (se 6 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 5976341 = 280141) (by norm_num)
theorem B2666789 : Blo 786339 2666789 := bbase (se 4 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 2666789 = 500023) (by norm_num)
theorem B897365 : Blo 786339 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B13873493 : Blo 786339 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B897373 : Blo 786339 897373 := bbase (se 3 (by rfl) ⟨168257, by rfl⟩ : syracuseStep 897373 = 336515) (by norm_num)
theorem B799141 : Blo 786339 799141 := bbase (se 4 (by rfl) ⟨74919, by rfl⟩ : syracuseStep 799141 = 149839) (by norm_num)
theorem B995753 : Blo 786339 995753 := bbase (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) (by norm_num)
theorem B5681621 : Blo 786339 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B995809 : Blo 786339 995809 := bbase (se 2 (by rfl) ⟨373428, by rfl⟩ : syracuseStep 995809 = 746857) (by norm_num)
theorem B7582261 : Blo 786339 7582261 := bbase (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) (by norm_num)
theorem B995905 : Blo 786339 995905 := bbase (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) (by norm_num)
theorem B1684093 : Blo 786339 1684093 := bbase (se 3 (by rfl) ⟨315767, by rfl⟩ : syracuseStep 1684093 = 631535) (by norm_num)
theorem B1421957 : Blo 786339 1421957 := bbase (se 4 (by rfl) ⟨133308, by rfl⟩ : syracuseStep 1421957 = 266617) (by norm_num)
theorem B2994853 : Blo 786339 2994853 := bbase (se 4 (by rfl) ⟨280767, by rfl⟩ : syracuseStep 2994853 = 561535) (by norm_num)
theorem B2667221 : Blo 786339 2667221 := bbase (se 7 (by rfl) ⟨31256, by rfl⟩ : syracuseStep 2667221 = 62513) (by norm_num)
theorem B996077 : Blo 786339 996077 := bbase (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) (by norm_num)
theorem B996133 : Blo 786339 996133 := bbase (se 4 (by rfl) ⟨93387, by rfl⟩ : syracuseStep 996133 = 186775) (by norm_num)
theorem B996229 : Blo 786339 996229 := bbase (se 4 (by rfl) ⟨93396, by rfl⟩ : syracuseStep 996229 = 186793) (by norm_num)
theorem B1422245 : Blo 786339 1422245 := bbase (se 4 (by rfl) ⟨133335, by rfl⟩ : syracuseStep 1422245 = 266671) (by norm_num)
theorem B2995157 : Blo 786339 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B2274293 : Blo 786339 2274293 := bbase (se 5 (by rfl) ⟨106607, by rfl⟩ : syracuseStep 2274293 = 213215) (by norm_num)
theorem B1684469 : Blo 786339 1684469 := bbase (se 5 (by rfl) ⟨78959, by rfl⟩ : syracuseStep 1684469 = 157919) (by norm_num)
theorem B799741 : Blo 786339 799741 := bbase (se 3 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 799741 = 299903) (by norm_num)
theorem B3027989 : Blo 786339 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B996401 : Blo 786339 996401 := bbase (se 2 (by rfl) ⟨373650, by rfl⟩ : syracuseStep 996401 = 747301) (by norm_num)
theorem B996457 : Blo 786339 996457 := bbase (se 2 (by rfl) ⟨373671, by rfl⟩ : syracuseStep 996457 = 747343) (by norm_num)
theorem B3781829 : Blo 786339 3781829 := bbase (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) (by norm_num)
theorem B996553 : Blo 786339 996553 := bbase (se 2 (by rfl) ⟨373707, by rfl⟩ : syracuseStep 996553 = 747415) (by norm_num)
theorem B996725 : Blo 786339 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B996781 : Blo 786339 996781 := bbase (se 3 (by rfl) ⟨186896, by rfl⟩ : syracuseStep 996781 = 373793) (by norm_num)
theorem B996877 : Blo 786339 996877 := bbase (se 3 (by rfl) ⟨186914, by rfl⟩ : syracuseStep 996877 = 373829) (by norm_num)
theorem B6305365 : Blo 786339 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B898705 : Blo 786339 898705 := bbase (se 2 (by rfl) ⟨337014, by rfl⟩ : syracuseStep 898705 = 674029) (by norm_num)
theorem B997049 : Blo 786339 997049 := bbase (se 2 (by rfl) ⟨373893, by rfl⟩ : syracuseStep 997049 = 747787) (by norm_num)
theorem B997105 : Blo 786339 997105 := bbase (se 2 (by rfl) ⟨373914, by rfl⟩ : syracuseStep 997105 = 747829) (by norm_num)
theorem B997201 : Blo 786339 997201 := bbase (se 2 (by rfl) ⟨373950, by rfl⟩ : syracuseStep 997201 = 747901) (by norm_num)
theorem B800609 : Blo 786339 800609 := bbase (se 2 (by rfl) ⟨300228, by rfl⟩ : syracuseStep 800609 = 600457) (by norm_num)
theorem B1423261 : Blo 786339 1423261 := bbase (se 3 (by rfl) ⟨266861, by rfl⟩ : syracuseStep 1423261 = 533723) (by norm_num)
theorem B997373 : Blo 786339 997373 := bbase (se 3 (by rfl) ⟨187007, by rfl⟩ : syracuseStep 997373 = 374015) (by norm_num)
theorem B11548693 : Blo 786339 11548693 := bbase (se 6 (by rfl) ⟨270672, by rfl⟩ : syracuseStep 11548693 = 541345) (by norm_num)
theorem B997429 : Blo 786339 997429 := bbase (se 5 (by rfl) ⟨46754, by rfl⟩ : syracuseStep 997429 = 93509) (by norm_num)
theorem B4110421 : Blo 786339 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B997525 : Blo 786339 997525 := bbase (se 6 (by rfl) ⟨23379, by rfl⟩ : syracuseStep 997525 = 46759) (by norm_num)
theorem B5683445 : Blo 786339 5683445 := bbase (se 5 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 5683445 = 532823) (by norm_num)
theorem B899381 : Blo 786339 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B997697 : Blo 786339 997697 := bbase (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) (by norm_num)
theorem B1423693 : Blo 786339 1423693 := bbase (se 3 (by rfl) ⟨266942, by rfl⟩ : syracuseStep 1423693 = 533885) (by norm_num)
theorem B997753 : Blo 786339 997753 := bbase (se 2 (by rfl) ⟨374157, by rfl⟩ : syracuseStep 997753 = 748315) (by norm_num)
theorem B1259917 : Blo 786339 1259917 := bbase (se 3 (by rfl) ⟨236234, by rfl⟩ : syracuseStep 1259917 = 472469) (by norm_num)
theorem B2242997 : Blo 786339 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B997849 : Blo 786339 997849 := bbase (se 2 (by rfl) ⟨374193, by rfl⟩ : syracuseStep 997849 = 748387) (by norm_num)
theorem B7191061 : Blo 786339 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B1686109 : Blo 786339 1686109 := bbase (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) (by norm_num)
theorem B1423981 : Blo 786339 1423981 := bbase (se 3 (by rfl) ⟨266996, by rfl⟩ : syracuseStep 1423981 = 533993) (by norm_num)
theorem B998021 : Blo 786339 998021 := bbase (se 4 (by rfl) ⟨93564, by rfl⟩ : syracuseStep 998021 = 187129) (by norm_num)
theorem B998077 : Blo 786339 998077 := bbase (se 3 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 998077 = 374279) (by norm_num)
theorem B998173 : Blo 786339 998173 := bbase (se 3 (by rfl) ⟨187157, by rfl⟩ : syracuseStep 998173 = 374315) (by norm_num)
theorem B1260373 : Blo 786339 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B998345 : Blo 786339 998345 := bbase (se 2 (by rfl) ⟨374379, by rfl⟩ : syracuseStep 998345 = 748759) (by norm_num)
theorem B998401 : Blo 786339 998401 := bbase (se 2 (by rfl) ⟨374400, by rfl⟩ : syracuseStep 998401 = 748801) (by norm_num)
theorem B2997269 : Blo 786339 2997269 := bbase (se 6 (by rfl) ⟨70248, by rfl⟩ : syracuseStep 2997269 = 140497) (by norm_num)
theorem B998497 : Blo 786339 998497 := bbase (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) (by norm_num)
theorem B998669 : Blo 786339 998669 := bbase (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) (by norm_num)
theorem B2997557 : Blo 786339 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B998725 : Blo 786339 998725 := bbase (se 4 (by rfl) ⟨93630, by rfl⟩ : syracuseStep 998725 = 187261) (by norm_num)
theorem B7585109 : Blo 786339 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B3194261 : Blo 786339 3194261 := bbase (se 6 (by rfl) ⟨74865, by rfl⟩ : syracuseStep 3194261 = 149731) (by norm_num)
theorem B998821 : Blo 786339 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B1686997 : Blo 786339 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B1261045 : Blo 786339 1261045 := bbase (se 5 (by rfl) ⟨59111, by rfl⟩ : syracuseStep 1261045 = 118223) (by norm_num)
theorem B998993 : Blo 786339 998993 := bbase (se 2 (by rfl) ⟨374622, by rfl⟩ : syracuseStep 998993 = 749245) (by norm_num)
theorem B2244181 : Blo 786339 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B999049 : Blo 786339 999049 := bbase (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) (by norm_num)
theorem B999145 : Blo 786339 999145 := bbase (se 2 (by rfl) ⟨374679, by rfl⟩ : syracuseStep 999145 = 749359) (by norm_num)
theorem B2244341 : Blo 786339 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1326989 : Blo 786339 1326989 := bbase (se 3 (by rfl) ⟨248810, by rfl⟩ : syracuseStep 1326989 = 497621) (by norm_num)
theorem B999317 : Blo 786339 999317 := bbase (se 6 (by rfl) ⟨23421, by rfl⟩ : syracuseStep 999317 = 46843) (by norm_num)
theorem B1261469 : Blo 786339 1261469 := bbase (se 3 (by rfl) ⟨236525, by rfl⟩ : syracuseStep 1261469 = 473051) (by norm_num)
theorem B1687493 : Blo 786339 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B999373 : Blo 786339 999373 := bbase (se 3 (by rfl) ⟨187382, by rfl⟩ : syracuseStep 999373 = 374765) (by norm_num)
theorem B2244581 : Blo 786339 2244581 := bbase (se 4 (by rfl) ⟨210429, by rfl⟩ : syracuseStep 2244581 = 420859) (by norm_num)
theorem B1327117 : Blo 786339 1327117 := bbase (se 3 (by rfl) ⟨248834, by rfl⟩ : syracuseStep 1327117 = 497669) (by norm_num)
theorem B2768933 : Blo 786339 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B999469 : Blo 786339 999469 := bbase (se 3 (by rfl) ⟨187400, by rfl⟩ : syracuseStep 999469 = 374801) (by norm_num)
theorem B6406229 : Blo 786339 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B1327205 : Blo 786339 1327205 := bbase (se 4 (by rfl) ⟨124425, by rfl⟩ : syracuseStep 1327205 = 248851) (by norm_num)
theorem B2244773 : Blo 786339 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B5062837 : Blo 786339 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B1261757 : Blo 786339 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B1851589 : Blo 786339 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B999641 : Blo 786339 999641 := bbase (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) (by norm_num)
theorem B1327333 : Blo 786339 1327333 := bbase (se 4 (by rfl) ⟨124437, by rfl⟩ : syracuseStep 1327333 = 248875) (by norm_num)
theorem B999697 : Blo 786339 999697 := bbase (se 2 (by rfl) ⟨374886, by rfl⟩ : syracuseStep 999697 = 749773) (by norm_num)
theorem B8962325 : Blo 786339 8962325 := bbase (se 6 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 8962325 = 420109) (by norm_num)
theorem B1327421 : Blo 786339 1327421 := bbase (se 3 (by rfl) ⟨248891, by rfl⟩ : syracuseStep 1327421 = 497783) (by norm_num)
theorem B999793 : Blo 786339 999793 := bbase (se 2 (by rfl) ⟨374922, by rfl⟩ : syracuseStep 999793 = 749845) (by norm_num)
theorem B1327549 : Blo 786339 1327549 := bbase (se 3 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 1327549 = 497831) (by norm_num)
theorem B2998741 : Blo 786339 2998741 := bbase (se 7 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 2998741 = 70283) (by norm_num)
theorem B3981797 : Blo 786339 3981797 := bbase (se 4 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 3981797 = 746587) (by norm_num)
theorem B1327637 : Blo 786339 1327637 := bbase (se 6 (by rfl) ⟨31116, by rfl⟩ : syracuseStep 1327637 = 62233) (by norm_num)
theorem B999965 : Blo 786339 999965 := bbase (se 3 (by rfl) ⟨187493, by rfl⟩ : syracuseStep 999965 = 374987) (by norm_num)
theorem B1000021 : Blo 786339 1000021 := bbase (se 8 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 1000021 = 11719) (by norm_num)
theorem B1327765 : Blo 786339 1327765 := bbase (se 6 (by rfl) ⟨31119, by rfl⟩ : syracuseStep 1327765 = 62239) (by norm_num)
theorem B1000117 : Blo 786339 1000117 := bbase (se 5 (by rfl) ⟨46880, by rfl⟩ : syracuseStep 1000117 = 93761) (by norm_num)
theorem B1327853 : Blo 786339 1327853 := bbase (se 3 (by rfl) ⟨248972, by rfl⟩ : syracuseStep 1327853 = 497945) (by norm_num)
theorem B2999045 : Blo 786339 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1327981 : Blo 786339 1327981 := bbase (se 3 (by rfl) ⟨248996, by rfl⟩ : syracuseStep 1327981 = 497993) (by norm_num)
theorem B1328069 : Blo 786339 1328069 := bbase (se 4 (by rfl) ⟨124506, by rfl⟩ : syracuseStep 1328069 = 249013) (by norm_num)
theorem B1262557 : Blo 786339 1262557 := bbase (se 3 (by rfl) ⟨236729, by rfl⟩ : syracuseStep 1262557 = 473459) (by norm_num)
theorem B1328197 : Blo 786339 1328197 := bbase (se 4 (by rfl) ⟨124518, by rfl⟩ : syracuseStep 1328197 = 249037) (by norm_num)
theorem B2245765 : Blo 786339 2245765 := bbase (se 4 (by rfl) ⟨210540, by rfl⟩ : syracuseStep 2245765 = 421081) (by norm_num)
theorem B1328285 : Blo 786339 1328285 := bbase (se 3 (by rfl) ⟨249053, by rfl⟩ : syracuseStep 1328285 = 498107) (by norm_num)
theorem B3884213 : Blo 786339 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1066213 : Blo 786339 1066213 := bbase (se 4 (by rfl) ⟨99957, by rfl⟩ : syracuseStep 1066213 = 199915) (by norm_num)
theorem B1328413 : Blo 786339 1328413 := bbase (se 3 (by rfl) ⟨249077, by rfl⟩ : syracuseStep 1328413 = 498155) (by norm_num)
theorem B1328501 : Blo 786339 1328501 := bbase (se 5 (by rfl) ⟨62273, by rfl⟩ : syracuseStep 1328501 = 124547) (by norm_num)
theorem B3032549 : Blo 786339 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1328629 : Blo 786339 1328629 := bbase (se 5 (by rfl) ⟨62279, by rfl⟩ : syracuseStep 1328629 = 124559) (by norm_num)
theorem B1263109 : Blo 786339 1263109 := bbase (se 4 (by rfl) ⟨118416, by rfl⟩ : syracuseStep 1263109 = 236833) (by norm_num)
theorem B6735413 : Blo 786339 6735413 := bbase (se 5 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 6735413 = 631445) (by norm_num)
theorem B1328717 : Blo 786339 1328717 := bbase (se 3 (by rfl) ⟨249134, by rfl⟩ : syracuseStep 1328717 = 498269) (by norm_num)
theorem B2737781 : Blo 786339 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B3196597 : Blo 786339 3196597 := bbase (se 5 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 3196597 = 299681) (by norm_num)
theorem B1328845 : Blo 786339 1328845 := bbase (se 3 (by rfl) ⟨249158, by rfl⟩ : syracuseStep 1328845 = 498317) (by norm_num)
theorem B3983093 : Blo 786339 3983093 := bbase (se 5 (by rfl) ⟨186707, by rfl⟩ : syracuseStep 3983093 = 373415) (by norm_num)
theorem B3032821 : Blo 786339 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B1263365 : Blo 786339 1263365 := bbase (se 4 (by rfl) ⟨118440, by rfl⟩ : syracuseStep 1263365 = 236881) (by norm_num)
theorem B3786517 : Blo 786339 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B1328933 : Blo 786339 1328933 := bbase (se 4 (by rfl) ⟨124587, by rfl⟩ : syracuseStep 1328933 = 249175) (by norm_num)
theorem B1066829 : Blo 786339 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B1492901 : Blo 786339 1492901 := bbase (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) (by norm_num)
theorem B1329061 : Blo 786339 1329061 := bbase (se 4 (by rfl) ⟨124599, by rfl⟩ : syracuseStep 1329061 = 249199) (by norm_num)
theorem B1329149 : Blo 786339 1329149 := bbase (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) (by norm_num)
theorem B1329277 : Blo 786339 1329277 := bbase (se 3 (by rfl) ⟨249239, by rfl⟩ : syracuseStep 1329277 = 498479) (by norm_num)
theorem B1198237 : Blo 786339 1198237 := bbase (se 3 (by rfl) ⟨224669, by rfl⟩ : syracuseStep 1198237 = 449339) (by norm_num)
theorem B1329365 : Blo 786339 1329365 := bbase (se 7 (by rfl) ⟨15578, by rfl⟩ : syracuseStep 1329365 = 31157) (by norm_num)
theorem B2246869 : Blo 786339 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B1329493 : Blo 786339 1329493 := bbase (se 10 (by rfl) ⟨1947, by rfl⟩ : syracuseStep 1329493 = 3895) (by norm_num)
theorem B1329581 : Blo 786339 1329581 := bbase (se 3 (by rfl) ⟨249296, by rfl⟩ : syracuseStep 1329581 = 498593) (by norm_num)
theorem B1264069 : Blo 786339 1264069 := bbase (se 4 (by rfl) ⟨118506, by rfl⟩ : syracuseStep 1264069 = 237013) (by norm_num)
theorem B1329709 : Blo 786339 1329709 := bbase (se 3 (by rfl) ⟨249320, by rfl⟩ : syracuseStep 1329709 = 498641) (by norm_num)
theorem B1329797 : Blo 786339 1329797 := bbase (se 4 (by rfl) ⟨124668, by rfl⟩ : syracuseStep 1329797 = 249337) (by norm_num)
theorem B1493653 : Blo 786339 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B1329925 : Blo 786339 1329925 := bbase (se 4 (by rfl) ⟨124680, by rfl⟩ : syracuseStep 1329925 = 249361) (by norm_num)
theorem B8506133 : Blo 786339 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B1493797 : Blo 786339 1493797 := bbase (se 4 (by rfl) ⟨140043, by rfl⟩ : syracuseStep 1493797 = 280087) (by norm_num)
theorem B1330013 : Blo 786339 1330013 := bbase (se 3 (by rfl) ⟨249377, by rfl⟩ : syracuseStep 1330013 = 498755) (by norm_num)
theorem B1264493 : Blo 786339 1264493 := bbase (se 3 (by rfl) ⟨237092, by rfl⟩ : syracuseStep 1264493 = 474185) (by norm_num)
theorem B1493957 : Blo 786339 1493957 := bbase (se 4 (by rfl) ⟨140058, by rfl⟩ : syracuseStep 1493957 = 280117) (by norm_num)
theorem B1330141 : Blo 786339 1330141 := bbase (se 3 (by rfl) ⟨249401, by rfl⟩ : syracuseStep 1330141 = 498803) (by norm_num)
theorem B3984389 : Blo 786339 3984389 := bbase (se 4 (by rfl) ⟨373536, by rfl⟩ : syracuseStep 3984389 = 747073) (by norm_num)
theorem B1330229 : Blo 786339 1330229 := bbase (se 5 (by rfl) ⟨62354, by rfl⟩ : syracuseStep 1330229 = 124709) (by norm_num)
theorem B1494101 : Blo 786339 1494101 := bbase (se 8 (by rfl) ⟨8754, by rfl⟩ : syracuseStep 1494101 = 17509) (by norm_num)
theorem B1264765 : Blo 786339 1264765 := bbase (se 3 (by rfl) ⟨237143, by rfl⟩ : syracuseStep 1264765 = 474287) (by norm_num)
theorem B1264781 : Blo 786339 1264781 := bbase (se 3 (by rfl) ⟨237146, by rfl⟩ : syracuseStep 1264781 = 474293) (by norm_num)
theorem B3591317 : Blo 786339 3591317 := bbase (se 6 (by rfl) ⟨84171, by rfl⟩ : syracuseStep 3591317 = 168343) (by norm_num)
theorem B1330357 : Blo 786339 1330357 := bbase (se 5 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 1330357 = 124721) (by norm_num)
theorem B1330445 : Blo 786339 1330445 := bbase (se 3 (by rfl) ⟨249458, by rfl⟩ : syracuseStep 1330445 = 498917) (by norm_num)
theorem B1265005 : Blo 786339 1265005 := bbase (se 3 (by rfl) ⟨237188, by rfl⟩ : syracuseStep 1265005 = 474377) (by norm_num)
theorem B1494389 : Blo 786339 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B1330573 : Blo 786339 1330573 := bbase (se 3 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 1330573 = 498965) (by norm_num)
theorem B1330661 : Blo 786339 1330661 := bbase (se 4 (by rfl) ⟨124749, by rfl⟩ : syracuseStep 1330661 = 249499) (by norm_num)
theorem B3362309 : Blo 786339 3362309 := bbase (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) (by norm_num)
theorem B1494541 : Blo 786339 1494541 := bbase (se 3 (by rfl) ⟨280226, by rfl⟩ : syracuseStep 1494541 = 560453) (by norm_num)
theorem B1330789 : Blo 786339 1330789 := bbase (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) (by norm_num)
theorem B2248373 : Blo 786339 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B1330877 : Blo 786339 1330877 := bbase (se 3 (by rfl) ⟨249539, by rfl⟩ : syracuseStep 1330877 = 499079) (by norm_num)
theorem B1494845 : Blo 786339 1494845 := bbase (se 3 (by rfl) ⟨280283, by rfl⟩ : syracuseStep 1494845 = 560567) (by norm_num)
theorem B1331005 : Blo 786339 1331005 := bbase (se 3 (by rfl) ⟨249563, by rfl⟩ : syracuseStep 1331005 = 499127) (by norm_num)
theorem B5984117 : Blo 786339 5984117 := bbase (se 5 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 5984117 = 561011) (by norm_num)
theorem B1331093 : Blo 786339 1331093 := bbase (se 6 (by rfl) ⟨31197, by rfl⟩ : syracuseStep 1331093 = 62395) (by norm_num)
theorem B970741 : Blo 786339 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B1331221 : Blo 786339 1331221 := bbase (se 6 (by rfl) ⟨31200, by rfl⟩ : syracuseStep 1331221 = 62401) (by norm_num)
theorem B6377525 : Blo 786339 6377525 := bbase (se 5 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 6377525 = 597893) (by norm_num)
theorem B1331309 : Blo 786339 1331309 := bbase (se 3 (by rfl) ⟨249620, by rfl⟩ : syracuseStep 1331309 = 499241) (by norm_num)
theorem B2019541 : Blo 786339 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B25972949 : Blo 786339 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B1331437 : Blo 786339 1331437 := bbase (se 3 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 1331437 = 499289) (by norm_num)
theorem B3985685 : Blo 786339 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B1331525 : Blo 786339 1331525 := bbase (se 4 (by rfl) ⟨124830, by rfl⟩ : syracuseStep 1331525 = 249661) (by norm_num)
theorem B840013 : Blo 786339 840013 := bbase (se 3 (by rfl) ⟨157502, by rfl⟩ : syracuseStep 840013 = 315005) (by norm_num)
theorem B2773333 : Blo 786339 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B840133 : Blo 786339 840133 := bbase (se 4 (by rfl) ⟨78762, by rfl⟩ : syracuseStep 840133 = 157525) (by norm_num)
theorem B1331653 : Blo 786339 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B6738389 : Blo 786339 6738389 := bbase (se 7 (by rfl) ⟨78965, by rfl⟩ : syracuseStep 6738389 = 157931) (by norm_num)
theorem B1331741 : Blo 786339 1331741 := bbase (se 3 (by rfl) ⟨249701, by rfl⟩ : syracuseStep 1331741 = 499403) (by norm_num)
theorem B1495597 : Blo 786339 1495597 := bbase (se 3 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 1495597 = 560849) (by norm_num)
theorem B1331869 : Blo 786339 1331869 := bbase (se 3 (by rfl) ⟨249725, by rfl⟩ : syracuseStep 1331869 = 499451) (by norm_num)
theorem B1495741 : Blo 786339 1495741 := bbase (se 3 (by rfl) ⟨280451, by rfl⟩ : syracuseStep 1495741 = 560903) (by norm_num)
theorem B840385 : Blo 786339 840385 := bbase (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) (by norm_num)
theorem B3232453 : Blo 786339 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B840389 : Blo 786339 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B1331957 : Blo 786339 1331957 := bbase (se 5 (by rfl) ⟨62435, by rfl⟩ : syracuseStep 1331957 = 124871) (by norm_num)
theorem B1200901 : Blo 786339 1200901 := bbase (se 4 (by rfl) ⟨112584, by rfl⟩ : syracuseStep 1200901 = 225169) (by norm_num)
theorem B1495901 : Blo 786339 1495901 := bbase (se 3 (by rfl) ⟨280481, by rfl⟩ : syracuseStep 1495901 = 560963) (by norm_num)
theorem B3232613 : Blo 786339 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B1332085 : Blo 786339 1332085 := bbase (se 5 (by rfl) ⟨62441, by rfl⟩ : syracuseStep 1332085 = 124883) (by norm_num)
theorem B1332173 : Blo 786339 1332173 := bbase (se 3 (by rfl) ⟨249782, by rfl⟩ : syracuseStep 1332173 = 499565) (by norm_num)
theorem B1496045 : Blo 786339 1496045 := bbase (se 3 (by rfl) ⟨280508, by rfl⟩ : syracuseStep 1496045 = 561017) (by norm_num)
theorem B1332301 : Blo 786339 1332301 := bbase (se 3 (by rfl) ⟨249806, by rfl⟩ : syracuseStep 1332301 = 499613) (by norm_num)
theorem B1332389 : Blo 786339 1332389 := bbase (se 4 (by rfl) ⟨124911, by rfl⟩ : syracuseStep 1332389 = 249823) (by norm_num)
theorem B2249957 : Blo 786339 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B3364085 : Blo 786339 3364085 := bbase (se 5 (by rfl) ⟨157691, by rfl⟩ : syracuseStep 3364085 = 315383) (by norm_num)
theorem B840953 : Blo 786339 840953 := bbase (se 2 (by rfl) ⟨315357, by rfl⟩ : syracuseStep 840953 = 630715) (by norm_num)
theorem B1496333 : Blo 786339 1496333 := bbase (se 3 (by rfl) ⟨280562, by rfl⟩ : syracuseStep 1496333 = 561125) (by norm_num)
theorem B5395733 : Blo 786339 5395733 := bbase (se 6 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 5395733 = 252925) (by norm_num)
theorem B1332517 : Blo 786339 1332517 := bbase (se 4 (by rfl) ⟨124923, by rfl⟩ : syracuseStep 1332517 = 249847) (by norm_num)
theorem B1332605 : Blo 786339 1332605 := bbase (se 3 (by rfl) ⟨249863, by rfl⟩ : syracuseStep 1332605 = 499727) (by norm_num)
theorem B1496485 : Blo 786339 1496485 := bbase (se 4 (by rfl) ⟨140295, by rfl⟩ : syracuseStep 1496485 = 280591) (by norm_num)
theorem B841141 : Blo 786339 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B3364325 : Blo 786339 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B1332733 : Blo 786339 1332733 := bbase (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) (by norm_num)
theorem B3986981 : Blo 786339 3986981 := bbase (se 4 (by rfl) ⟨373779, by rfl⟩ : syracuseStep 3986981 = 747559) (by norm_num)
theorem B1332821 : Blo 786339 1332821 := bbase (se 8 (by rfl) ⟨7809, by rfl⟩ : syracuseStep 1332821 = 15619) (by norm_num)
theorem B4806229 : Blo 786339 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B1594973 : Blo 786339 1594973 := bbase (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) (by norm_num)
theorem B1496789 : Blo 786339 1496789 := bbase (se 7 (by rfl) ⟨17540, by rfl⟩ : syracuseStep 1496789 = 35081) (by norm_num)
theorem B1332949 : Blo 786339 1332949 := bbase (se 7 (by rfl) ⟨15620, by rfl⟩ : syracuseStep 1332949 = 31241) (by norm_num)
theorem B1333037 : Blo 786339 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B3790709 : Blo 786339 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B2840453 : Blo 786339 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B1333165 : Blo 786339 1333165 := bbase (se 3 (by rfl) ⟨249968, by rfl⟩ : syracuseStep 1333165 = 499937) (by norm_num)
theorem B1333253 : Blo 786339 1333253 := bbase (se 4 (by rfl) ⟨124992, by rfl⟩ : syracuseStep 1333253 = 249985) (by norm_num)
theorem B2021429 : Blo 786339 2021429 := bbase (se 5 (by rfl) ⟨94754, by rfl⟩ : syracuseStep 2021429 = 189509) (by norm_num)
theorem B1333381 : Blo 786339 1333381 := bbase (se 4 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 1333381 = 250009) (by norm_num)
theorem B1333469 : Blo 786339 1333469 := bbase (se 3 (by rfl) ⟨250025, by rfl⟩ : syracuseStep 1333469 = 500051) (by norm_num)
theorem B841961 : Blo 786339 841961 := bbase (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) (by norm_num)
theorem B1333597 : Blo 786339 1333597 := bbase (se 3 (by rfl) ⟨250049, by rfl⟩ : syracuseStep 1333597 = 500099) (by norm_num)
theorem B1333685 : Blo 786339 1333685 := bbase (se 5 (by rfl) ⟨62516, by rfl⟩ : syracuseStep 1333685 = 125033) (by norm_num)
theorem B1497541 : Blo 786339 1497541 := bbase (se 4 (by rfl) ⟨140394, by rfl⟩ : syracuseStep 1497541 = 280789) (by norm_num)
theorem B1497685 : Blo 786339 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B842405 : Blo 786339 842405 := bbase (se 4 (by rfl) ⟨78975, by rfl⟩ : syracuseStep 842405 = 157951) (by norm_num)
theorem B1891021 : Blo 786339 1891021 := bbase (se 3 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 1891021 = 709133) (by norm_num)
theorem B1497845 : Blo 786339 1497845 := bbase (se 5 (by rfl) ⟨70211, by rfl⟩ : syracuseStep 1497845 = 140423) (by norm_num)
theorem B3988277 : Blo 786339 3988277 := bbase (se 5 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 3988277 = 373901) (by norm_num)
theorem B1497989 : Blo 786339 1497989 := bbase (se 4 (by rfl) ⟨140436, by rfl⟩ : syracuseStep 1497989 = 280873) (by norm_num)
theorem B842653 : Blo 786339 842653 := bbase (se 3 (by rfl) ⟨157997, by rfl⟩ : syracuseStep 842653 = 315995) (by norm_num)
theorem B973873 : Blo 786339 973873 := bbase (se 2 (by rfl) ⟨365202, by rfl⟩ : syracuseStep 973873 = 730405) (by norm_num)
theorem B1498277 : Blo 786339 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B3792053 : Blo 786339 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B810209 : Blo 786339 810209 := bbase (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) (by norm_num)
theorem B5692693 : Blo 786339 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B1891637 : Blo 786339 1891637 := bbase (se 5 (by rfl) ⟨88670, by rfl⟩ : syracuseStep 1891637 = 177341) (by norm_num)
theorem B1498429 : Blo 786339 1498429 := bbase (se 3 (by rfl) ⟨280955, by rfl⟩ : syracuseStep 1498429 = 561911) (by norm_num)
theorem B843085 : Blo 786339 843085 := bbase (se 3 (by rfl) ⟨158078, by rfl⟩ : syracuseStep 843085 = 316157) (by norm_num)
theorem B810389 : Blo 786339 810389 := bbase (se 6 (by rfl) ⟨18993, by rfl⟩ : syracuseStep 810389 = 37987) (by norm_num)
theorem B843157 : Blo 786339 843157 := bbase (se 6 (by rfl) ⟨19761, by rfl⟩ : syracuseStep 843157 = 39523) (by norm_num)
theorem B1498733 : Blo 786339 1498733 := bbase (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) (by norm_num)
theorem B4546165 : Blo 786339 4546165 := bbase (se 5 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 4546165 = 426203) (by norm_num)
theorem B3366613 : Blo 786339 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B843529 : Blo 786339 843529 := bbase (se 2 (by rfl) ⟨316323, by rfl⟩ : syracuseStep 843529 = 632647) (by norm_num)
theorem B1990453 : Blo 786339 1990453 := bbase (se 5 (by rfl) ⟨93302, by rfl⟩ : syracuseStep 1990453 = 186605) (by norm_num)
theorem B2023309 : Blo 786339 2023309 := bbase (se 3 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 2023309 = 758741) (by norm_num)
theorem B1990565 : Blo 786339 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B974845 : Blo 786339 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B1892405 : Blo 786339 1892405 := bbase (se 5 (by rfl) ⟨88706, by rfl⟩ : syracuseStep 1892405 = 177413) (by norm_num)
theorem B1892413 : Blo 786339 1892413 := bbase (se 3 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 1892413 = 709655) (by norm_num)
theorem B3989573 : Blo 786339 3989573 := bbase (se 4 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 3989573 = 748045) (by norm_num)
theorem B1990757 : Blo 786339 1990757 := bbase (se 4 (by rfl) ⟨186633, by rfl⟩ : syracuseStep 1990757 = 373267) (by norm_num)
theorem B843905 : Blo 786339 843905 := bbase (se 2 (by rfl) ⟨316464, by rfl⟩ : syracuseStep 843905 = 632929) (by norm_num)
theorem B843977 : Blo 786339 843977 := bbase (se 2 (by rfl) ⟨316491, by rfl⟩ : syracuseStep 843977 = 632983) (by norm_num)
theorem B3465461 : Blo 786339 3465461 := bbase (se 5 (by rfl) ⟨162443, by rfl⟩ : syracuseStep 3465461 = 324887) (by norm_num)
theorem B1499485 : Blo 786339 1499485 := bbase (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) (by norm_num)
theorem B1991101 : Blo 786339 1991101 := bbase (se 3 (by rfl) ⟨373331, by rfl⟩ : syracuseStep 1991101 = 746663) (by norm_num)
theorem B1597909 : Blo 786339 1597909 := bbase (se 7 (by rfl) ⟨18725, by rfl⟩ : syracuseStep 1597909 = 37451) (by norm_num)
theorem B1499629 : Blo 786339 1499629 := bbase (se 3 (by rfl) ⟨281180, by rfl⟩ : syracuseStep 1499629 = 562361) (by norm_num)
theorem B1991213 : Blo 786339 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B2843221 : Blo 786339 2843221 := bbase (se 8 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 2843221 = 33319) (by norm_num)
theorem B1499789 : Blo 786339 1499789 := bbase (se 3 (by rfl) ⟨281210, by rfl⟩ : syracuseStep 1499789 = 562421) (by norm_num)
theorem B3203813 : Blo 786339 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B1991405 : Blo 786339 1991405 := bbase (se 3 (by rfl) ⟨373388, by rfl⟩ : syracuseStep 1991405 = 746777) (by norm_num)
theorem B1499933 : Blo 786339 1499933 := bbase (se 3 (by rfl) ⟨281237, by rfl⟩ : syracuseStep 1499933 = 562475) (by norm_num)
theorem B1893221 : Blo 786339 1893221 := bbase (se 4 (by rfl) ⟨177489, by rfl⟩ : syracuseStep 1893221 = 354979) (by norm_num)
theorem B1500221 : Blo 786339 1500221 := bbase (se 3 (by rfl) ⟨281291, by rfl⟩ : syracuseStep 1500221 = 562583) (by norm_num)
theorem B1991749 : Blo 786339 1991749 := bbase (se 4 (by rfl) ⟨186726, by rfl⟩ : syracuseStep 1991749 = 373453) (by norm_num)
theorem B3794053 : Blo 786339 3794053 := bbase (se 4 (by rfl) ⟨355692, by rfl⟩ : syracuseStep 3794053 = 711385) (by norm_num)
theorem B3368101 : Blo 786339 3368101 := bbase (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) (by norm_num)
theorem B1991861 : Blo 786339 1991861 := bbase (se 5 (by rfl) ⟨93368, by rfl⟩ : syracuseStep 1991861 = 186737) (by norm_num)
theorem B3368117 : Blo 786339 3368117 := bbase (se 5 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 3368117 = 315761) (by norm_num)
theorem B1500373 : Blo 786339 1500373 := bbase (se 7 (by rfl) ⟨17582, by rfl⟩ : syracuseStep 1500373 = 35165) (by norm_num)
theorem B3990869 : Blo 786339 3990869 := bbase (se 12 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 3990869 = 2923) (by norm_num)
theorem B1992053 : Blo 786339 1992053 := bbase (se 5 (by rfl) ⟨93377, by rfl⟩ : syracuseStep 1992053 = 186755) (by norm_num)
theorem B4482485 : Blo 786339 4482485 := bbase (se 5 (by rfl) ⟨210116, by rfl⟩ : syracuseStep 4482485 = 420233) (by norm_num)
theorem B1009217 : Blo 786339 1009217 := bbase (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) (by norm_num)
theorem B1795733 : Blo 786339 1795733 := bbase (se 6 (by rfl) ⟨42087, by rfl⟩ : syracuseStep 1795733 = 84175) (by norm_num)
theorem B1992397 : Blo 786339 1992397 := bbase (se 3 (by rfl) ⟨373574, by rfl⟩ : syracuseStep 1992397 = 747149) (by norm_num)
theorem B1992509 : Blo 786339 1992509 := bbase (se 3 (by rfl) ⟨373595, by rfl⟩ : syracuseStep 1992509 = 747191) (by norm_num)
theorem B1992701 : Blo 786339 1992701 := bbase (se 3 (by rfl) ⟨373631, by rfl⟩ : syracuseStep 1992701 = 747263) (by norm_num)
theorem B1009729 : Blo 786339 1009729 := bbase (se 2 (by rfl) ⟨378648, by rfl⟩ : syracuseStep 1009729 = 757297) (by norm_num)
theorem B1009873 : Blo 786339 1009873 := bbase (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) (by norm_num)
theorem B2025773 : Blo 786339 2025773 := bbase (se 3 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 2025773 = 759665) (by norm_num)
theorem B1993045 : Blo 786339 1993045 := bbase (se 10 (by rfl) ⟨2919, by rfl⟩ : syracuseStep 1993045 = 5839) (by norm_num)
theorem B1993157 : Blo 786339 1993157 := bbase (se 4 (by rfl) ⟨186858, by rfl⟩ : syracuseStep 1993157 = 373717) (by norm_num)
theorem B7694837 : Blo 786339 7694837 := bbase (se 5 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 7694837 = 721391) (by norm_num)
theorem B3992165 : Blo 786339 3992165 := bbase (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) (by norm_num)
theorem B2026109 : Blo 786339 2026109 := bbase (se 3 (by rfl) ⟨379895, by rfl⟩ : syracuseStep 2026109 = 759791) (by norm_num)
theorem B1993349 : Blo 786339 1993349 := bbase (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) (by norm_num)
theorem B1010341 : Blo 786339 1010341 := bbase (se 4 (by rfl) ⟨94719, by rfl⟩ : syracuseStep 1010341 = 189439) (by norm_num)
theorem B1993693 : Blo 786339 1993693 := bbase (se 3 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 1993693 = 747635) (by norm_num)
theorem B945217 : Blo 786339 945217 := bbase (se 2 (by rfl) ⟨354456, by rfl⟩ : syracuseStep 945217 = 708913) (by norm_num)
theorem B1993805 : Blo 786339 1993805 := bbase (se 3 (by rfl) ⟨373838, by rfl⟩ : syracuseStep 1993805 = 747677) (by norm_num)
theorem B2845829 : Blo 786339 2845829 := bbase (se 4 (by rfl) ⟨266796, by rfl⟩ : syracuseStep 2845829 = 533593) (by norm_num)
theorem B945361 : Blo 786339 945361 := bbase (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) (by norm_num)
theorem B1993997 : Blo 786339 1993997 := bbase (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) (by norm_num)
theorem B3370373 : Blo 786339 3370373 := bbase (se 4 (by rfl) ⟨315972, by rfl⟩ : syracuseStep 3370373 = 631945) (by norm_num)
theorem B2846117 : Blo 786339 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B5991893 : Blo 786339 5991893 := bbase (se 7 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 5991893 = 140435) (by norm_num)
theorem B1895989 : Blo 786339 1895989 := bbase (se 5 (by rfl) ⟨88874, by rfl⟩ : syracuseStep 1895989 = 177749) (by norm_num)
theorem B1994341 : Blo 786339 1994341 := bbase (se 4 (by rfl) ⟨186969, by rfl⟩ : syracuseStep 1994341 = 373939) (by norm_num)
theorem B1994453 : Blo 786339 1994453 := bbase (se 7 (by rfl) ⟨23372, by rfl⟩ : syracuseStep 1994453 = 46745) (by norm_num)
theorem B1797869 : Blo 786339 1797869 := bbase (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) (by norm_num)
theorem B9596693 : Blo 786339 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B3993461 : Blo 786339 3993461 := bbase (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) (by norm_num)
theorem B1994645 : Blo 786339 1994645 := bbase (se 6 (by rfl) ⟨46749, by rfl⟩ : syracuseStep 1994645 = 93499) (by norm_num)
theorem B1896509 : Blo 786339 1896509 := bbase (se 3 (by rfl) ⟨355595, by rfl⟩ : syracuseStep 1896509 = 711191) (by norm_num)
theorem B1896605 : Blo 786339 1896605 := bbase (se 3 (by rfl) ⟨355613, by rfl⟩ : syracuseStep 1896605 = 711227) (by norm_num)
theorem B946409 : Blo 786339 946409 := bbase (se 2 (by rfl) ⟨354903, by rfl⟩ : syracuseStep 946409 = 709807) (by norm_num)
theorem B1994989 : Blo 786339 1994989 := bbase (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) (by norm_num)
theorem B5402933 : Blo 786339 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B7565653 : Blo 786339 7565653 := bbase (se 10 (by rfl) ⟨11082, by rfl⟩ : syracuseStep 7565653 = 22165) (by norm_num)
theorem B1995101 : Blo 786339 1995101 := bbase (se 3 (by rfl) ⟨374081, by rfl⟩ : syracuseStep 1995101 = 748163) (by norm_num)
theorem B2126197 : Blo 786339 2126197 := bbase (se 5 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 2126197 = 199331) (by norm_num)
theorem B1012133 : Blo 786339 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B1798669 : Blo 786339 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B1995293 : Blo 786339 1995293 := bbase (se 3 (by rfl) ⟨374117, by rfl⟩ : syracuseStep 1995293 = 748235) (by norm_num)
theorem B2847269 : Blo 786339 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B946741 : Blo 786339 946741 := bbase (se 5 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 946741 = 88757) (by norm_num)
theorem B3600949 : Blo 786339 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1995637 : Blo 786339 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B6157237 : Blo 786339 6157237 := bbase (se 5 (by rfl) ⟨288620, by rfl⟩ : syracuseStep 6157237 = 577241) (by norm_num)
theorem B1995749 : Blo 786339 1995749 := bbase (se 4 (by rfl) ⟨187101, by rfl⟩ : syracuseStep 1995749 = 374203) (by norm_num)
theorem B3994757 : Blo 786339 3994757 := bbase (se 4 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 3994757 = 749017) (by norm_num)
theorem B1995941 : Blo 786339 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B4256981 : Blo 786339 4256981 := bbase (se 7 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 4256981 = 99773) (by norm_num)
theorem B947629 : Blo 786339 947629 := bbase (se 3 (by rfl) ⟨177680, by rfl⟩ : syracuseStep 947629 = 355361) (by norm_num)
theorem B10221013 : Blo 786339 10221013 := bbase (se 7 (by rfl) ⟨119777, by rfl⟩ : syracuseStep 10221013 = 239555) (by norm_num)
theorem B1897949 : Blo 786339 1897949 := bbase (se 3 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 1897949 = 711731) (by norm_num)
theorem B1996285 : Blo 786339 1996285 := bbase (se 3 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 1996285 = 748607) (by norm_num)
theorem B1996397 : Blo 786339 1996397 := bbase (se 3 (by rfl) ⟨374324, by rfl⟩ : syracuseStep 1996397 = 748649) (by norm_num)
theorem B2520757 : Blo 786339 2520757 := bbase (se 5 (by rfl) ⟨118160, by rfl⟩ : syracuseStep 2520757 = 236321) (by norm_num)
theorem B1996589 : Blo 786339 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1800101 : Blo 786339 1800101 := bbase (se 4 (by rfl) ⟨168759, by rfl⟩ : syracuseStep 1800101 = 337519) (by norm_num)
theorem B3405797 : Blo 786339 3405797 := bbase (se 4 (by rfl) ⟨319293, by rfl⟩ : syracuseStep 3405797 = 638587) (by norm_num)
theorem B1996933 : Blo 786339 1996933 := bbase (se 4 (by rfl) ⟨187212, by rfl⟩ : syracuseStep 1996933 = 374425) (by norm_num)
theorem B1997045 : Blo 786339 1997045 := bbase (se 5 (by rfl) ⟨93611, by rfl⟩ : syracuseStep 1997045 = 187223) (by norm_num)
theorem B3996053 : Blo 786339 3996053 := bbase (se 6 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 3996053 = 187315) (by norm_num)
theorem B1997237 : Blo 786339 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B948677 : Blo 786339 948677 := bbase (se 4 (by rfl) ⟨88938, by rfl⟩ : syracuseStep 948677 = 177877) (by norm_num)
theorem B1997581 : Blo 786339 1997581 := bbase (se 3 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 1997581 = 749093) (by norm_num)
theorem B949033 : Blo 786339 949033 := bbase (se 2 (by rfl) ⟨355887, by rfl⟩ : syracuseStep 949033 = 711775) (by norm_num)
theorem B1997693 : Blo 786339 1997693 := bbase (se 3 (by rfl) ⟨374567, by rfl⟩ : syracuseStep 1997693 = 749135) (by norm_num)
theorem B949225 : Blo 786339 949225 := bbase (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) (by norm_num)
theorem B2522117 : Blo 786339 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B1997885 : Blo 786339 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B949369 : Blo 786339 949369 := bbase (se 2 (by rfl) ⟨356013, by rfl⟩ : syracuseStep 949369 = 712027) (by norm_num)
theorem B3374405 : Blo 786339 3374405 := bbase (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) (by norm_num)
theorem B1998229 : Blo 786339 1998229 := bbase (se 6 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 1998229 = 93667) (by norm_num)
theorem B1998341 : Blo 786339 1998341 := bbase (se 4 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 1998341 = 374689) (by norm_num)
theorem B3276389 : Blo 786339 3276389 := bbase (se 4 (by rfl) ⟨307161, by rfl⟩ : syracuseStep 3276389 = 614323) (by norm_num)
theorem B3997349 : Blo 786339 3997349 := bbase (se 4 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 3997349 = 749503) (by norm_num)
theorem B1998533 : Blo 786339 1998533 := bbase (se 4 (by rfl) ⟨187362, by rfl⟩ : syracuseStep 1998533 = 374725) (by norm_num)
theorem B1769309 : Blo 786339 1769309 := bbase (se 3 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 1769309 = 663491) (by norm_num)
theorem B1179509 : Blo 786339 1179509 := bbase (se 5 (by rfl) ⟨55289, by rfl⟩ : syracuseStep 1179509 = 110579) (by norm_num)
theorem B1179533 : Blo 786339 1179533 := bbase (se 3 (by rfl) ⟨221162, by rfl⟩ : syracuseStep 1179533 = 442325) (by norm_num)
theorem B884641 : Blo 786339 884641 := bbase (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) (by norm_num)
theorem B1179557 : Blo 786339 1179557 := bbase (se 4 (by rfl) ⟨110583, by rfl⟩ : syracuseStep 1179557 = 221167) (by norm_num)
theorem B1769381 : Blo 786339 1769381 := bbase (se 4 (by rfl) ⟨165879, by rfl⟩ : syracuseStep 1769381 = 331759) (by norm_num)
theorem B1179581 : Blo 786339 1179581 := bbase (se 3 (by rfl) ⟨221171, by rfl⟩ : syracuseStep 1179581 = 442343) (by norm_num)
theorem B884677 : Blo 786339 884677 := bbase (se 4 (by rfl) ⟨82938, by rfl⟩ : syracuseStep 884677 = 165877) (by norm_num)
theorem B1179605 : Blo 786339 1179605 := bbase (se 7 (by rfl) ⟨13823, by rfl⟩ : syracuseStep 1179605 = 27647) (by norm_num)
theorem B5046229 : Blo 786339 5046229 := bbase (se 7 (by rfl) ⟨59135, by rfl⟩ : syracuseStep 5046229 = 118271) (by norm_num)
theorem B884713 : Blo 786339 884713 := bbase (se 2 (by rfl) ⟨331767, by rfl⟩ : syracuseStep 884713 = 663535) (by norm_num)
theorem B1179629 : Blo 786339 1179629 := bbase (se 3 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 1179629 = 442361) (by norm_num)
theorem B1769453 : Blo 786339 1769453 := bbase (se 3 (by rfl) ⟨331772, by rfl⟩ : syracuseStep 1769453 = 663545) (by norm_num)
theorem B786435 : Blo 786339 786435 := bstep (se 1 (by rfl) ⟨589826, by rfl⟩ : syracuseStep 786435 = 1179653) B1179653
theorem B1769489 : Blo 786339 1769489 := bstep (se 2 (by rfl) ⟨663558, by rfl⟩ : syracuseStep 1769489 = 1327117) B1327117
theorem B1179665 : Blo 786339 1179665 := bstep (se 2 (by rfl) ⟨442374, by rfl⟩ : syracuseStep 1179665 = 884749) B884749
theorem B786451 : Blo 786339 786451 := bstep (se 1 (by rfl) ⟨589838, by rfl⟩ : syracuseStep 786451 = 1179677) B1179677
theorem B1769507 : Blo 786339 1769507 := bstep (se 1 (by rfl) ⟨1327130, by rfl⟩ : syracuseStep 1769507 = 2654261) B2654261
theorem B1179683 : Blo 786339 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B786467 : Blo 786339 786467 := bstep (se 1 (by rfl) ⟨589850, by rfl⟩ : syracuseStep 786467 = 1179701) B1179701
theorem B786483 : Blo 786339 786483 := bstep (se 1 (by rfl) ⟨589862, by rfl⟩ : syracuseStep 786483 = 1179725) B1179725
theorem B1179713 : Blo 786339 1179713 := bstep (se 2 (by rfl) ⟨442392, by rfl⟩ : syracuseStep 1179713 = 884785) B884785
theorem B884803 : Blo 786339 884803 := bstep (se 1 (by rfl) ⟨663602, by rfl⟩ : syracuseStep 884803 = 1327205) B1327205
theorem B786499 : Blo 786339 786499 := bstep (se 1 (by rfl) ⟨589874, by rfl⟩ : syracuseStep 786499 = 1179749) B1179749
theorem B1179731 : Blo 786339 1179731 := bstep (se 1 (by rfl) ⟨884798, by rfl⟩ : syracuseStep 1179731 = 1769597) B1769597
theorem B786515 : Blo 786339 786515 := bstep (se 1 (by rfl) ⟨589886, by rfl⟩ : syracuseStep 786515 = 1179773) B1179773
theorem B786531 : Blo 786339 786531 := bstep (se 1 (by rfl) ⟨589898, by rfl⟩ : syracuseStep 786531 = 1179797) B1179797
theorem B1179761 : Blo 786339 1179761 := bstep (se 2 (by rfl) ⟨442410, by rfl⟩ : syracuseStep 1179761 = 884821) B884821
theorem B786547 : Blo 786339 786547 := bstep (se 1 (by rfl) ⟨589910, by rfl⟩ : syracuseStep 786547 = 1179821) B1179821
theorem B1179779 : Blo 786339 1179779 := bstep (se 1 (by rfl) ⟨884834, by rfl⟩ : syracuseStep 1179779 = 1769669) B1769669
theorem B786563 : Blo 786339 786563 := bstep (se 1 (by rfl) ⟨589922, by rfl⟩ : syracuseStep 786563 = 1179845) B1179845
theorem B786579 : Blo 786339 786579 := bstep (se 1 (by rfl) ⟨589934, by rfl⟩ : syracuseStep 786579 = 1179869) B1179869
theorem B1179809 : Blo 786339 1179809 := bstep (se 2 (by rfl) ⟨442428, by rfl⟩ : syracuseStep 1179809 = 884857) B884857
theorem B786595 : Blo 786339 786595 := bstep (se 1 (by rfl) ⟨589946, by rfl⟩ : syracuseStep 786595 = 1179893) B1179893
theorem B1179827 : Blo 786339 1179827 := bstep (se 1 (by rfl) ⟨884870, by rfl⟩ : syracuseStep 1179827 = 1769741) B1769741
theorem B786611 : Blo 786339 786611 := bstep (se 1 (by rfl) ⟨589958, by rfl⟩ : syracuseStep 786611 = 1179917) B1179917
theorem B786627 : Blo 786339 786627 := bstep (se 1 (by rfl) ⟨589970, by rfl⟩ : syracuseStep 786627 = 1179941) B1179941
theorem B1179857 : Blo 786339 1179857 := bstep (se 2 (by rfl) ⟨442446, by rfl⟩ : syracuseStep 1179857 = 884893) B884893
theorem B884947 : Blo 786339 884947 := bstep (se 1 (by rfl) ⟨663710, by rfl⟩ : syracuseStep 884947 = 1327421) B1327421
theorem B786643 : Blo 786339 786643 := bstep (se 1 (by rfl) ⟨589982, by rfl⟩ : syracuseStep 786643 = 1179965) B1179965
theorem B1179875 : Blo 786339 1179875 := bstep (se 1 (by rfl) ⟨884906, by rfl⟩ : syracuseStep 1179875 = 1769813) B1769813
theorem B786659 : Blo 786339 786659 := bstep (se 1 (by rfl) ⟨589994, by rfl⟩ : syracuseStep 786659 = 1179989) B1179989
theorem B6750449 : Blo 786339 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B786675 : Blo 786339 786675 := bstep (se 1 (by rfl) ⟨590006, by rfl⟩ : syracuseStep 786675 = 1180013) B1180013
theorem B1179905 : Blo 786339 1179905 := bstep (se 2 (by rfl) ⟨442464, by rfl⟩ : syracuseStep 1179905 = 884929) B884929
theorem B786691 : Blo 786339 786691 := bstep (se 1 (by rfl) ⟨590018, by rfl⟩ : syracuseStep 786691 = 1180037) B1180037
theorem B2654477 : Blo 786339 2654477 := bstep (se 3 (by rfl) ⟨497714, by rfl⟩ : syracuseStep 2654477 = 995429) B995429
theorem B1179923 : Blo 786339 1179923 := bstep (se 1 (by rfl) ⟨884942, by rfl⟩ : syracuseStep 1179923 = 1769885) B1769885
theorem B786707 : Blo 786339 786707 := bstep (se 1 (by rfl) ⟨590030, by rfl⟩ : syracuseStep 786707 = 1180061) B1180061
theorem B786723 : Blo 786339 786723 := bstep (se 1 (by rfl) ⟨590042, by rfl⟩ : syracuseStep 786723 = 1180085) B1180085
theorem B1769777 : Blo 786339 1769777 := bstep (se 2 (by rfl) ⟨663666, by rfl⟩ : syracuseStep 1769777 = 1327333) B1327333
theorem B1179953 : Blo 786339 1179953 := bstep (se 2 (by rfl) ⟨442482, by rfl⟩ : syracuseStep 1179953 = 884965) B884965
theorem B786739 : Blo 786339 786739 := bstep (se 1 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 786739 = 1180109) B1180109
theorem B2654531 : Blo 786339 2654531 := bstep (se 1 (by rfl) ⟨1990898, by rfl⟩ : syracuseStep 2654531 = 3981797) B3981797
theorem B1769795 : Blo 786339 1769795 := bstep (se 1 (by rfl) ⟨1327346, by rfl⟩ : syracuseStep 1769795 = 2654693) B2654693
theorem B1179971 : Blo 786339 1179971 := bstep (se 1 (by rfl) ⟨884978, by rfl⟩ : syracuseStep 1179971 = 1769957) B1769957
theorem B786755 : Blo 786339 786755 := bstep (se 1 (by rfl) ⟨590066, by rfl⟩ : syracuseStep 786755 = 1180133) B1180133
theorem B10092869 : Blo 786339 10092869 := bstep (se 4 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 10092869 = 1892413) B1892413
theorem B786771 : Blo 786339 786771 := bstep (se 1 (by rfl) ⟨590078, by rfl⟩ : syracuseStep 786771 = 1180157) B1180157
theorem B1180001 : Blo 786339 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B885091 : Blo 786339 885091 := bstep (se 1 (by rfl) ⟨663818, by rfl⟩ : syracuseStep 885091 = 1327637) B1327637
theorem B786787 : Blo 786339 786787 := bstep (se 1 (by rfl) ⟨590090, by rfl⟩ : syracuseStep 786787 = 1180181) B1180181
theorem B1180019 : Blo 786339 1180019 := bstep (se 1 (by rfl) ⟨885014, by rfl⟩ : syracuseStep 1180019 = 1770029) B1770029
theorem B786803 : Blo 786339 786803 := bstep (se 1 (by rfl) ⟨590102, by rfl⟩ : syracuseStep 786803 = 1180205) B1180205
theorem B786819 : Blo 786339 786819 := bstep (se 1 (by rfl) ⟨590114, by rfl⟩ : syracuseStep 786819 = 1180229) B1180229
theorem B1180049 : Blo 786339 1180049 := bstep (se 2 (by rfl) ⟨442518, by rfl⟩ : syracuseStep 1180049 = 885037) B885037
theorem B786835 : Blo 786339 786835 := bstep (se 1 (by rfl) ⟨590126, by rfl⟩ : syracuseStep 786835 = 1180253) B1180253
theorem B1180067 : Blo 786339 1180067 := bstep (se 1 (by rfl) ⟨885050, by rfl⟩ : syracuseStep 1180067 = 1770101) B1770101
theorem B786851 : Blo 786339 786851 := bstep (se 1 (by rfl) ⟨590138, by rfl⟩ : syracuseStep 786851 = 1180277) B1180277
theorem B2130349 : Blo 786339 2130349 := bstep (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) B798881
theorem B786867 : Blo 786339 786867 := bstep (se 1 (by rfl) ⟨590150, by rfl⟩ : syracuseStep 786867 = 1180301) B1180301
theorem B1180097 : Blo 786339 1180097 := bstep (se 2 (by rfl) ⟨442536, by rfl⟩ : syracuseStep 1180097 = 885073) B885073
theorem B786883 : Blo 786339 786883 := bstep (se 1 (by rfl) ⟨590162, by rfl⟩ : syracuseStep 786883 = 1180325) B1180325
theorem B1999313 : Blo 786339 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B1180115 : Blo 786339 1180115 := bstep (se 1 (by rfl) ⟨885086, by rfl⟩ : syracuseStep 1180115 = 1770173) B1770173
theorem B786899 : Blo 786339 786899 := bstep (se 1 (by rfl) ⟨590174, by rfl⟩ : syracuseStep 786899 = 1180349) B1180349
theorem B786915 : Blo 786339 786915 := bstep (se 1 (by rfl) ⟨590186, by rfl⟩ : syracuseStep 786915 = 1180373) B1180373
theorem B1180145 : Blo 786339 1180145 := bstep (se 2 (by rfl) ⟨442554, by rfl⟩ : syracuseStep 1180145 = 885109) B885109
theorem B885235 : Blo 786339 885235 := bstep (se 1 (by rfl) ⟨663926, by rfl⟩ : syracuseStep 885235 = 1327853) B1327853
theorem B786931 : Blo 786339 786931 := bstep (se 1 (by rfl) ⟨590198, by rfl⟩ : syracuseStep 786931 = 1180397) B1180397
theorem B1180163 : Blo 786339 1180163 := bstep (se 1 (by rfl) ⟨885122, by rfl⟩ : syracuseStep 1180163 = 1770245) B1770245
theorem B786947 : Blo 786339 786947 := bstep (se 1 (by rfl) ⟨590210, by rfl⟩ : syracuseStep 786947 = 1180421) B1180421
theorem B1999363 : Blo 786339 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B786963 : Blo 786339 786963 := bstep (se 1 (by rfl) ⟨590222, by rfl⟩ : syracuseStep 786963 = 1180445) B1180445
theorem B1180193 : Blo 786339 1180193 := bstep (se 2 (by rfl) ⟨442572, by rfl⟩ : syracuseStep 1180193 = 885145) B885145
theorem B786979 : Blo 786339 786979 := bstep (se 1 (by rfl) ⟨590234, by rfl⟩ : syracuseStep 786979 = 1180469) B1180469
theorem B1180211 : Blo 786339 1180211 := bstep (se 1 (by rfl) ⟨885158, by rfl⟩ : syracuseStep 1180211 = 1770317) B1770317
theorem B786995 : Blo 786339 786995 := bstep (se 1 (by rfl) ⟨590246, by rfl⟩ : syracuseStep 786995 = 1180493) B1180493
theorem B787011 : Blo 786339 787011 := bstep (se 1 (by rfl) ⟨590258, by rfl⟩ : syracuseStep 787011 = 1180517) B1180517
theorem B2654801 : Blo 786339 2654801 := bstep (se 2 (by rfl) ⟨995550, by rfl⟩ : syracuseStep 2654801 = 1991101) B1991101
theorem B1770065 : Blo 786339 1770065 := bstep (se 2 (by rfl) ⟨663774, by rfl⟩ : syracuseStep 1770065 = 1327549) B1327549
theorem B1180241 : Blo 786339 1180241 := bstep (se 2 (by rfl) ⟨442590, by rfl⟩ : syracuseStep 1180241 = 885181) B885181
theorem B787027 : Blo 786339 787027 := bstep (se 1 (by rfl) ⟨590270, by rfl⟩ : syracuseStep 787027 = 1180541) B1180541
theorem B1770083 : Blo 786339 1770083 := bstep (se 1 (by rfl) ⟨1327562, by rfl⟩ : syracuseStep 1770083 = 2655125) B2655125
theorem B1180259 : Blo 786339 1180259 := bstep (se 1 (by rfl) ⟨885194, by rfl⟩ : syracuseStep 1180259 = 1770389) B1770389
theorem B787043 : Blo 786339 787043 := bstep (se 1 (by rfl) ⟨590282, by rfl⟩ : syracuseStep 787043 = 1180565) B1180565
theorem B2523757 : Blo 786339 2523757 := bstep (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) B946409
theorem B2130545 : Blo 786339 2130545 := bstep (se 2 (by rfl) ⟨798954, by rfl⟩ : syracuseStep 2130545 = 1597909) B1597909
theorem B787059 : Blo 786339 787059 := bstep (se 1 (by rfl) ⟨590294, by rfl⟩ : syracuseStep 787059 = 1180589) B1180589
theorem B3998321 : Blo 786339 3998321 := bstep (se 2 (by rfl) ⟨1499370, by rfl⟩ : syracuseStep 3998321 = 2998741) B2998741
theorem B1180289 : Blo 786339 1180289 := bstep (se 2 (by rfl) ⟨442608, by rfl⟩ : syracuseStep 1180289 = 885217) B885217
theorem B787075 : Blo 786339 787075 := bstep (se 1 (by rfl) ⟨590306, by rfl⟩ : syracuseStep 787075 = 1180613) B1180613
theorem B885379 : Blo 786339 885379 := bstep (se 1 (by rfl) ⟨664034, by rfl⟩ : syracuseStep 885379 = 1328069) B1328069
theorem B9241229 : Blo 786339 9241229 := bstep (se 3 (by rfl) ⟨1732730, by rfl⟩ : syracuseStep 9241229 = 3465461) B3465461
theorem B1999505 : Blo 786339 1999505 := bstep (se 2 (by rfl) ⟨749814, by rfl⟩ : syracuseStep 1999505 = 1499629) B1499629
theorem B1180307 : Blo 786339 1180307 := bstep (se 1 (by rfl) ⟨885230, by rfl⟩ : syracuseStep 1180307 = 1770461) B1770461
theorem B787091 : Blo 786339 787091 := bstep (se 1 (by rfl) ⟨590318, by rfl⟩ : syracuseStep 787091 = 1180637) B1180637
theorem B787107 : Blo 786339 787107 := bstep (se 1 (by rfl) ⟨590330, by rfl⟩ : syracuseStep 787107 = 1180661) B1180661
theorem B1704611 : Blo 786339 1704611 := bstep (se 1 (by rfl) ⟨1278458, by rfl⟩ : syracuseStep 1704611 = 2556917) B2556917
theorem B1180337 : Blo 786339 1180337 := bstep (se 2 (by rfl) ⟨442626, by rfl⟩ : syracuseStep 1180337 = 885253) B885253
theorem B787123 : Blo 786339 787123 := bstep (se 1 (by rfl) ⟨590342, by rfl⟩ : syracuseStep 787123 = 1180685) B1180685
theorem B1180355 : Blo 786339 1180355 := bstep (se 1 (by rfl) ⟨885266, by rfl⟩ : syracuseStep 1180355 = 1770533) B1770533
theorem B787139 : Blo 786339 787139 := bstep (se 1 (by rfl) ⟨590354, by rfl⟩ : syracuseStep 787139 = 1180709) B1180709
theorem B787155 : Blo 786339 787155 := bstep (se 1 (by rfl) ⟨590366, by rfl⟩ : syracuseStep 787155 = 1180733) B1180733
theorem B1180385 : Blo 786339 1180385 := bstep (se 2 (by rfl) ⟨442644, by rfl⟩ : syracuseStep 1180385 = 885289) B885289
theorem B787171 : Blo 786339 787171 := bstep (se 1 (by rfl) ⟨590378, by rfl⟩ : syracuseStep 787171 = 1180757) B1180757
theorem B1180403 : Blo 786339 1180403 := bstep (se 1 (by rfl) ⟨885302, by rfl⟩ : syracuseStep 1180403 = 1770605) B1770605
theorem B787187 : Blo 786339 787187 := bstep (se 1 (by rfl) ⟨590390, by rfl⟩ : syracuseStep 787187 = 1180781) B1180781
theorem B787203 : Blo 786339 787203 := bstep (se 1 (by rfl) ⟨590402, by rfl⟩ : syracuseStep 787203 = 1180805) B1180805
theorem B1180433 : Blo 786339 1180433 := bstep (se 2 (by rfl) ⟨442662, by rfl⟩ : syracuseStep 1180433 = 885325) B885325
theorem B885523 : Blo 786339 885523 := bstep (se 1 (by rfl) ⟨664142, by rfl⟩ : syracuseStep 885523 = 1328285) B1328285
theorem B787219 : Blo 786339 787219 := bstep (se 1 (by rfl) ⟨590414, by rfl⟩ : syracuseStep 787219 = 1180829) B1180829
theorem B2589475 : Blo 786339 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B1180451 : Blo 786339 1180451 := bstep (se 1 (by rfl) ⟨885338, by rfl⟩ : syracuseStep 1180451 = 1770677) B1770677
theorem B787235 : Blo 786339 787235 := bstep (se 1 (by rfl) ⟨590426, by rfl⟩ : syracuseStep 787235 = 1180853) B1180853
theorem B787251 : Blo 786339 787251 := bstep (se 1 (by rfl) ⟨590438, by rfl⟩ : syracuseStep 787251 = 1180877) B1180877
theorem B1180481 : Blo 786339 1180481 := bstep (se 2 (by rfl) ⟨442680, by rfl⟩ : syracuseStep 1180481 = 885361) B885361
theorem B787267 : Blo 786339 787267 := bstep (se 1 (by rfl) ⟨590450, by rfl⟩ : syracuseStep 787267 = 1180901) B1180901
theorem B1180499 : Blo 786339 1180499 := bstep (se 1 (by rfl) ⟨885374, by rfl⟩ : syracuseStep 1180499 = 1770749) B1770749
theorem B787283 : Blo 786339 787283 := bstep (se 1 (by rfl) ⟨590462, by rfl⟩ : syracuseStep 787283 = 1180925) B1180925
theorem B787299 : Blo 786339 787299 := bstep (se 1 (by rfl) ⟨590474, by rfl⟩ : syracuseStep 787299 = 1180949) B1180949
theorem B1770353 : Blo 786339 1770353 := bstep (se 2 (by rfl) ⟨663882, by rfl⟩ : syracuseStep 1770353 = 1327765) B1327765
theorem B1180529 : Blo 786339 1180529 := bstep (se 2 (by rfl) ⟨442698, by rfl⟩ : syracuseStep 1180529 = 885397) B885397
theorem B787315 : Blo 786339 787315 := bstep (se 1 (by rfl) ⟨590486, by rfl⟩ : syracuseStep 787315 = 1180973) B1180973
theorem B1770371 : Blo 786339 1770371 := bstep (se 1 (by rfl) ⟨1327778, by rfl⟩ : syracuseStep 1770371 = 2655557) B2655557
theorem B1180547 : Blo 786339 1180547 := bstep (se 1 (by rfl) ⟨885410, by rfl⟩ : syracuseStep 1180547 = 1770821) B1770821
theorem B787331 : Blo 786339 787331 := bstep (se 1 (by rfl) ⟨590498, by rfl⟩ : syracuseStep 787331 = 1180997) B1180997
theorem B2392973 : Blo 786339 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B787347 : Blo 786339 787347 := bstep (se 1 (by rfl) ⟨590510, by rfl⟩ : syracuseStep 787347 = 1181021) B1181021
theorem B1180577 : Blo 786339 1180577 := bstep (se 2 (by rfl) ⟨442716, by rfl⟩ : syracuseStep 1180577 = 885433) B885433
theorem B885667 : Blo 786339 885667 := bstep (se 1 (by rfl) ⟨664250, by rfl⟩ : syracuseStep 885667 = 1328501) B1328501
theorem B787363 : Blo 786339 787363 := bstep (se 1 (by rfl) ⟨590522, by rfl⟩ : syracuseStep 787363 = 1181045) B1181045
theorem B1180595 : Blo 786339 1180595 := bstep (se 1 (by rfl) ⟨885446, by rfl⟩ : syracuseStep 1180595 = 1770893) B1770893
theorem B787379 : Blo 786339 787379 := bstep (se 1 (by rfl) ⟨590534, by rfl⟩ : syracuseStep 787379 = 1181069) B1181069
theorem B787395 : Blo 786339 787395 := bstep (se 1 (by rfl) ⟨590546, by rfl⟩ : syracuseStep 787395 = 1181093) B1181093
theorem B1180625 : Blo 786339 1180625 := bstep (se 2 (by rfl) ⟨442734, by rfl⟩ : syracuseStep 1180625 = 885469) B885469
theorem B787411 : Blo 786339 787411 := bstep (se 1 (by rfl) ⟨590558, by rfl⟩ : syracuseStep 787411 = 1181117) B1181117
theorem B1180643 : Blo 786339 1180643 := bstep (se 1 (by rfl) ⟨885482, by rfl⟩ : syracuseStep 1180643 = 1770965) B1770965
theorem B787427 : Blo 786339 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B787443 : Blo 786339 787443 := bstep (se 1 (by rfl) ⟨590582, by rfl⟩ : syracuseStep 787443 = 1181165) B1181165
theorem B1180673 : Blo 786339 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B787459 : Blo 786339 787459 := bstep (se 1 (by rfl) ⟨590594, by rfl⟩ : syracuseStep 787459 = 1181189) B1181189
theorem B1180691 : Blo 786339 1180691 := bstep (se 1 (by rfl) ⟨885518, by rfl⟩ : syracuseStep 1180691 = 1771037) B1771037
theorem B787475 : Blo 786339 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B787491 : Blo 786339 787491 := bstep (se 1 (by rfl) ⟨590618, by rfl⟩ : syracuseStep 787491 = 1181237) B1181237
theorem B4490275 : Blo 786339 4490275 := bstep (se 1 (by rfl) ⟨3367706, by rfl⟩ : syracuseStep 4490275 = 6735413) B6735413
theorem B1180721 : Blo 786339 1180721 := bstep (se 2 (by rfl) ⟨442770, by rfl⟩ : syracuseStep 1180721 = 885541) B885541
theorem B885811 : Blo 786339 885811 := bstep (se 1 (by rfl) ⟨664358, by rfl⟩ : syracuseStep 885811 = 1328717) B1328717
theorem B787507 : Blo 786339 787507 := bstep (se 1 (by rfl) ⟨590630, by rfl⟩ : syracuseStep 787507 = 1181261) B1181261
theorem B1180739 : Blo 786339 1180739 := bstep (se 1 (by rfl) ⟨885554, by rfl⟩ : syracuseStep 1180739 = 1771109) B1771109
theorem B787523 : Blo 786339 787523 := bstep (se 1 (by rfl) ⟨590642, by rfl⟩ : syracuseStep 787523 = 1181285) B1181285
theorem B787539 : Blo 786339 787539 := bstep (se 1 (by rfl) ⟨590654, by rfl⟩ : syracuseStep 787539 = 1181309) B1181309
theorem B1180769 : Blo 786339 1180769 := bstep (se 2 (by rfl) ⟨442788, by rfl⟩ : syracuseStep 1180769 = 885577) B885577
theorem B787555 : Blo 786339 787555 := bstep (se 1 (by rfl) ⟨590666, by rfl⟩ : syracuseStep 787555 = 1181333) B1181333
theorem B2655341 : Blo 786339 2655341 := bstep (se 3 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 2655341 = 995753) B995753
theorem B1180787 : Blo 786339 1180787 := bstep (se 1 (by rfl) ⟨885590, by rfl⟩ : syracuseStep 1180787 = 1771181) B1771181
theorem B787571 : Blo 786339 787571 := bstep (se 1 (by rfl) ⟨590678, by rfl⟩ : syracuseStep 787571 = 1181357) B1181357
theorem B787587 : Blo 786339 787587 := bstep (se 1 (by rfl) ⟨590690, by rfl⟩ : syracuseStep 787587 = 1181381) B1181381
theorem B1770641 : Blo 786339 1770641 := bstep (se 2 (by rfl) ⟨663990, by rfl⟩ : syracuseStep 1770641 = 1327981) B1327981
theorem B1180817 : Blo 786339 1180817 := bstep (se 2 (by rfl) ⟨442806, by rfl⟩ : syracuseStep 1180817 = 885613) B885613
theorem B787603 : Blo 786339 787603 := bstep (se 1 (by rfl) ⟨590702, by rfl⟩ : syracuseStep 787603 = 1181405) B1181405
theorem B2655395 : Blo 786339 2655395 := bstep (se 1 (by rfl) ⟨1991546, by rfl⟩ : syracuseStep 2655395 = 3983093) B3983093
theorem B1770659 : Blo 786339 1770659 := bstep (se 1 (by rfl) ⟨1327994, by rfl⟩ : syracuseStep 1770659 = 2655989) B2655989
theorem B1180835 : Blo 786339 1180835 := bstep (se 1 (by rfl) ⟨885626, by rfl⟩ : syracuseStep 1180835 = 1771253) B1771253
theorem B787619 : Blo 786339 787619 := bstep (se 1 (by rfl) ⟨590714, by rfl⟩ : syracuseStep 787619 = 1181429) B1181429
theorem B787635 : Blo 786339 787635 := bstep (se 1 (by rfl) ⟨590726, by rfl⟩ : syracuseStep 787635 = 1181453) B1181453
theorem B1180865 : Blo 786339 1180865 := bstep (se 2 (by rfl) ⟨442824, by rfl⟩ : syracuseStep 1180865 = 885649) B885649
theorem B885955 : Blo 786339 885955 := bstep (se 1 (by rfl) ⟨664466, by rfl⟩ : syracuseStep 885955 = 1328933) B1328933
theorem B787651 : Blo 786339 787651 := bstep (se 1 (by rfl) ⟨590738, by rfl⟩ : syracuseStep 787651 = 1181477) B1181477
theorem B1180883 : Blo 786339 1180883 := bstep (se 1 (by rfl) ⟨885662, by rfl⟩ : syracuseStep 1180883 = 1771325) B1771325
theorem B787667 : Blo 786339 787667 := bstep (se 1 (by rfl) ⟨590750, by rfl⟩ : syracuseStep 787667 = 1181501) B1181501
theorem B787683 : Blo 786339 787683 := bstep (se 1 (by rfl) ⟨590762, by rfl⟩ : syracuseStep 787683 = 1181525) B1181525
theorem B1180913 : Blo 786339 1180913 := bstep (se 2 (by rfl) ⟨442842, by rfl⟩ : syracuseStep 1180913 = 885685) B885685
theorem B787699 : Blo 786339 787699 := bstep (se 1 (by rfl) ⟨590774, by rfl⟩ : syracuseStep 787699 = 1181549) B1181549
theorem B1180931 : Blo 786339 1180931 := bstep (se 1 (by rfl) ⟨885698, by rfl⟩ : syracuseStep 1180931 = 1771397) B1771397
theorem B787715 : Blo 786339 787715 := bstep (se 1 (by rfl) ⟨590786, by rfl⟩ : syracuseStep 787715 = 1181573) B1181573
theorem B787731 : Blo 786339 787731 := bstep (se 1 (by rfl) ⟨590798, by rfl⟩ : syracuseStep 787731 = 1181597) B1181597
theorem B1180961 : Blo 786339 1180961 := bstep (se 2 (by rfl) ⟨442860, by rfl⟩ : syracuseStep 1180961 = 885721) B885721
theorem B787747 : Blo 786339 787747 := bstep (se 1 (by rfl) ⟨590810, by rfl⟩ : syracuseStep 787747 = 1181621) B1181621
theorem B1180979 : Blo 786339 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B787763 : Blo 786339 787763 := bstep (se 1 (by rfl) ⟨590822, by rfl⟩ : syracuseStep 787763 = 1181645) B1181645
theorem B787779 : Blo 786339 787779 := bstep (se 1 (by rfl) ⟨590834, by rfl⟩ : syracuseStep 787779 = 1181669) B1181669
theorem B1181009 : Blo 786339 1181009 := bstep (se 2 (by rfl) ⟨442878, by rfl⟩ : syracuseStep 1181009 = 885757) B885757
theorem B886099 : Blo 786339 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B787795 : Blo 786339 787795 := bstep (se 1 (by rfl) ⟨590846, by rfl⟩ : syracuseStep 787795 = 1181693) B1181693
theorem B1181027 : Blo 786339 1181027 := bstep (se 1 (by rfl) ⟨885770, by rfl⟩ : syracuseStep 1181027 = 1771541) B1771541
theorem B787811 : Blo 786339 787811 := bstep (se 1 (by rfl) ⟨590858, by rfl⟩ : syracuseStep 787811 = 1181717) B1181717
theorem B787827 : Blo 786339 787827 := bstep (se 1 (by rfl) ⟨590870, by rfl⟩ : syracuseStep 787827 = 1181741) B1181741
theorem B1181057 : Blo 786339 1181057 := bstep (se 2 (by rfl) ⟨442896, by rfl⟩ : syracuseStep 1181057 = 885793) B885793
theorem B787843 : Blo 786339 787843 := bstep (se 1 (by rfl) ⟨590882, by rfl⟩ : syracuseStep 787843 = 1181765) B1181765
theorem B1181075 : Blo 786339 1181075 := bstep (se 1 (by rfl) ⟨885806, by rfl⟩ : syracuseStep 1181075 = 1771613) B1771613
theorem B787859 : Blo 786339 787859 := bstep (se 1 (by rfl) ⟨590894, by rfl⟩ : syracuseStep 787859 = 1181789) B1181789
theorem B787875 : Blo 786339 787875 := bstep (se 1 (by rfl) ⟨590906, by rfl⟩ : syracuseStep 787875 = 1181813) B1181813
theorem B2655665 : Blo 786339 2655665 := bstep (se 2 (by rfl) ⟨995874, by rfl⟩ : syracuseStep 2655665 = 1991749) B1991749
theorem B1770929 : Blo 786339 1770929 := bstep (se 2 (by rfl) ⟨664098, by rfl⟩ : syracuseStep 1770929 = 1328197) B1328197
theorem B1181105 : Blo 786339 1181105 := bstep (se 2 (by rfl) ⟨442914, by rfl⟩ : syracuseStep 1181105 = 885829) B885829
theorem B787891 : Blo 786339 787891 := bstep (se 1 (by rfl) ⟨590918, by rfl⟩ : syracuseStep 787891 = 1181837) B1181837
theorem B1770947 : Blo 786339 1770947 := bstep (se 1 (by rfl) ⟨1328210, by rfl⟩ : syracuseStep 1770947 = 2656421) B2656421
theorem B1181123 : Blo 786339 1181123 := bstep (se 1 (by rfl) ⟨885842, by rfl⟩ : syracuseStep 1181123 = 1771685) B1771685
theorem B787907 : Blo 786339 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B787923 : Blo 786339 787923 := bstep (se 1 (by rfl) ⟨590942, by rfl⟩ : syracuseStep 787923 = 1181885) B1181885
theorem B1181153 : Blo 786339 1181153 := bstep (se 2 (by rfl) ⟨442932, by rfl⟩ : syracuseStep 1181153 = 885865) B885865
theorem B886243 : Blo 786339 886243 := bstep (se 1 (by rfl) ⟨664682, by rfl⟩ : syracuseStep 886243 = 1329365) B1329365
theorem B787939 : Blo 786339 787939 := bstep (se 1 (by rfl) ⟨590954, by rfl⟩ : syracuseStep 787939 = 1181909) B1181909
theorem B1181171 : Blo 786339 1181171 := bstep (se 1 (by rfl) ⟨885878, by rfl⟩ : syracuseStep 1181171 = 1771757) B1771757
theorem B787955 : Blo 786339 787955 := bstep (se 1 (by rfl) ⟨590966, by rfl⟩ : syracuseStep 787955 = 1181933) B1181933
theorem B787971 : Blo 786339 787971 := bstep (se 1 (by rfl) ⟨590978, by rfl⟩ : syracuseStep 787971 = 1181957) B1181957
theorem B1181201 : Blo 786339 1181201 := bstep (se 2 (by rfl) ⟨442950, by rfl⟩ : syracuseStep 1181201 = 885901) B885901
theorem B787987 : Blo 786339 787987 := bstep (se 1 (by rfl) ⟨590990, by rfl⟩ : syracuseStep 787987 = 1181981) B1181981
theorem B1181219 : Blo 786339 1181219 := bstep (se 1 (by rfl) ⟨885914, by rfl⟩ : syracuseStep 1181219 = 1771829) B1771829
theorem B788003 : Blo 786339 788003 := bstep (se 1 (by rfl) ⟨591002, by rfl⟩ : syracuseStep 788003 = 1182005) B1182005
theorem B4490801 : Blo 786339 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B788019 : Blo 786339 788019 := bstep (se 1 (by rfl) ⟨591014, by rfl⟩ : syracuseStep 788019 = 1182029) B1182029
theorem B1181249 : Blo 786339 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B788035 : Blo 786339 788035 := bstep (se 1 (by rfl) ⟨591026, by rfl⟩ : syracuseStep 788035 = 1182053) B1182053
theorem B1181267 : Blo 786339 1181267 := bstep (se 1 (by rfl) ⟨885950, by rfl⟩ : syracuseStep 1181267 = 1771901) B1771901
theorem B788051 : Blo 786339 788051 := bstep (se 1 (by rfl) ⟨591038, by rfl⟩ : syracuseStep 788051 = 1182077) B1182077
theorem B788067 : Blo 786339 788067 := bstep (se 1 (by rfl) ⟨591050, by rfl⟩ : syracuseStep 788067 = 1182101) B1182101
theorem B1181297 : Blo 786339 1181297 := bstep (se 2 (by rfl) ⟨442986, by rfl⟩ : syracuseStep 1181297 = 885973) B885973
theorem B2000497 : Blo 786339 2000497 := bstep (se 2 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 2000497 = 1500373) B1500373
theorem B886387 : Blo 786339 886387 := bstep (se 1 (by rfl) ⟨664790, by rfl⟩ : syracuseStep 886387 = 1329581) B1329581
theorem B788083 : Blo 786339 788083 := bstep (se 1 (by rfl) ⟨591062, by rfl⟩ : syracuseStep 788083 = 1182125) B1182125
theorem B1181315 : Blo 786339 1181315 := bstep (se 1 (by rfl) ⟨885986, by rfl⟩ : syracuseStep 1181315 = 1771973) B1771973
theorem B788099 : Blo 786339 788099 := bstep (se 1 (by rfl) ⟨591074, by rfl⟩ : syracuseStep 788099 = 1182149) B1182149
theorem B788115 : Blo 786339 788115 := bstep (se 1 (by rfl) ⟨591086, by rfl⟩ : syracuseStep 788115 = 1182173) B1182173
theorem B1181345 : Blo 786339 1181345 := bstep (se 2 (by rfl) ⟨443004, by rfl⟩ : syracuseStep 1181345 = 886009) B886009
theorem B788131 : Blo 786339 788131 := bstep (se 1 (by rfl) ⟨591098, by rfl⟩ : syracuseStep 788131 = 1182197) B1182197
theorem B1181363 : Blo 786339 1181363 := bstep (se 1 (by rfl) ⟨886022, by rfl⟩ : syracuseStep 1181363 = 1772045) B1772045
theorem B788147 : Blo 786339 788147 := bstep (se 1 (by rfl) ⟨591110, by rfl⟩ : syracuseStep 788147 = 1182221) B1182221
theorem B788163 : Blo 786339 788163 := bstep (se 1 (by rfl) ⟨591122, by rfl⟩ : syracuseStep 788163 = 1182245) B1182245
theorem B1771217 : Blo 786339 1771217 := bstep (se 2 (by rfl) ⟨664206, by rfl⟩ : syracuseStep 1771217 = 1328413) B1328413
theorem B1181393 : Blo 786339 1181393 := bstep (se 2 (by rfl) ⟨443022, by rfl⟩ : syracuseStep 1181393 = 886045) B886045
theorem B788179 : Blo 786339 788179 := bstep (se 1 (by rfl) ⟨591134, by rfl⟩ : syracuseStep 788179 = 1182269) B1182269
theorem B1771235 : Blo 786339 1771235 := bstep (se 1 (by rfl) ⟨1328426, by rfl⟩ : syracuseStep 1771235 = 2656853) B2656853
theorem B1181411 : Blo 786339 1181411 := bstep (se 1 (by rfl) ⟨886058, by rfl⟩ : syracuseStep 1181411 = 1772117) B1772117
theorem B788195 : Blo 786339 788195 := bstep (se 1 (by rfl) ⟨591146, by rfl⟩ : syracuseStep 788195 = 1182293) B1182293
theorem B788211 : Blo 786339 788211 := bstep (se 1 (by rfl) ⟨591158, by rfl⟩ : syracuseStep 788211 = 1182317) B1182317
theorem B1181441 : Blo 786339 1181441 := bstep (se 2 (by rfl) ⟨443040, by rfl⟩ : syracuseStep 1181441 = 886081) B886081
theorem B886531 : Blo 786339 886531 := bstep (se 1 (by rfl) ⟨664898, by rfl⟩ : syracuseStep 886531 = 1329797) B1329797
theorem B788227 : Blo 786339 788227 := bstep (se 1 (by rfl) ⟨591170, by rfl⟩ : syracuseStep 788227 = 1182341) B1182341
theorem B1181459 : Blo 786339 1181459 := bstep (se 1 (by rfl) ⟨886094, by rfl⟩ : syracuseStep 1181459 = 1772189) B1772189
theorem B788243 : Blo 786339 788243 := bstep (se 1 (by rfl) ⟨591182, by rfl⟩ : syracuseStep 788243 = 1182365) B1182365
theorem B788259 : Blo 786339 788259 := bstep (se 1 (by rfl) ⟨591194, by rfl⟩ : syracuseStep 788259 = 1182389) B1182389
theorem B1181489 : Blo 786339 1181489 := bstep (se 2 (by rfl) ⟨443058, by rfl⟩ : syracuseStep 1181489 = 886117) B886117
theorem B788275 : Blo 786339 788275 := bstep (se 1 (by rfl) ⟨591206, by rfl⟩ : syracuseStep 788275 = 1182413) B1182413
theorem B1181507 : Blo 786339 1181507 := bstep (se 1 (by rfl) ⟨886130, by rfl⟩ : syracuseStep 1181507 = 1772261) B1772261
theorem B788291 : Blo 786339 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B788307 : Blo 786339 788307 := bstep (se 1 (by rfl) ⟨591230, by rfl⟩ : syracuseStep 788307 = 1182461) B1182461
theorem B5670755 : Blo 786339 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B1181537 : Blo 786339 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B788323 : Blo 786339 788323 := bstep (se 1 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 788323 = 1182485) B1182485
theorem B1181555 : Blo 786339 1181555 := bstep (se 1 (by rfl) ⟨886166, by rfl⟩ : syracuseStep 1181555 = 1772333) B1772333
theorem B788339 : Blo 786339 788339 := bstep (se 1 (by rfl) ⟨591254, by rfl⟩ : syracuseStep 788339 = 1182509) B1182509
theorem B788355 : Blo 786339 788355 := bstep (se 1 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 788355 = 1182533) B1182533
theorem B1181585 : Blo 786339 1181585 := bstep (se 2 (by rfl) ⟨443094, by rfl⟩ : syracuseStep 1181585 = 886189) B886189
theorem B886675 : Blo 786339 886675 := bstep (se 1 (by rfl) ⟨665006, by rfl⟩ : syracuseStep 886675 = 1330013) B1330013
theorem B788371 : Blo 786339 788371 := bstep (se 1 (by rfl) ⟨591278, by rfl⟩ : syracuseStep 788371 = 1182557) B1182557
theorem B1181603 : Blo 786339 1181603 := bstep (se 1 (by rfl) ⟨886202, by rfl⟩ : syracuseStep 1181603 = 1772405) B1772405
theorem B788387 : Blo 786339 788387 := bstep (se 1 (by rfl) ⟨591290, by rfl⟩ : syracuseStep 788387 = 1182581) B1182581
theorem B788403 : Blo 786339 788403 := bstep (se 1 (by rfl) ⟨591302, by rfl⟩ : syracuseStep 788403 = 1182605) B1182605
theorem B1181633 : Blo 786339 1181633 := bstep (se 2 (by rfl) ⟨443112, by rfl⟩ : syracuseStep 1181633 = 886225) B886225
theorem B788419 : Blo 786339 788419 := bstep (se 1 (by rfl) ⟨591314, by rfl⟩ : syracuseStep 788419 = 1182629) B1182629
theorem B2656205 : Blo 786339 2656205 := bstep (se 3 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 2656205 = 996077) B996077
theorem B1181651 : Blo 786339 1181651 := bstep (se 1 (by rfl) ⟨886238, by rfl⟩ : syracuseStep 1181651 = 1772477) B1772477
theorem B788435 : Blo 786339 788435 := bstep (se 1 (by rfl) ⟨591326, by rfl⟩ : syracuseStep 788435 = 1182653) B1182653
theorem B788451 : Blo 786339 788451 := bstep (se 1 (by rfl) ⟨591338, by rfl⟩ : syracuseStep 788451 = 1182677) B1182677
theorem B1771505 : Blo 786339 1771505 := bstep (se 2 (by rfl) ⟨664314, by rfl⟩ : syracuseStep 1771505 = 1328629) B1328629
theorem B1181681 : Blo 786339 1181681 := bstep (se 2 (by rfl) ⟨443130, by rfl⟩ : syracuseStep 1181681 = 886261) B886261
theorem B788467 : Blo 786339 788467 := bstep (se 1 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 788467 = 1182701) B1182701
theorem B2656259 : Blo 786339 2656259 := bstep (se 1 (by rfl) ⟨1992194, by rfl⟩ : syracuseStep 2656259 = 3984389) B3984389
theorem B1771523 : Blo 786339 1771523 := bstep (se 1 (by rfl) ⟨1328642, by rfl⟩ : syracuseStep 1771523 = 2657285) B2657285
theorem B1181699 : Blo 786339 1181699 := bstep (se 1 (by rfl) ⟨886274, by rfl⟩ : syracuseStep 1181699 = 1772549) B1772549
theorem B788483 : Blo 786339 788483 := bstep (se 1 (by rfl) ⟨591362, by rfl⟩ : syracuseStep 788483 = 1182725) B1182725
theorem B788499 : Blo 786339 788499 := bstep (se 1 (by rfl) ⟨591374, by rfl⟩ : syracuseStep 788499 = 1182749) B1182749
theorem B1181729 : Blo 786339 1181729 := bstep (se 2 (by rfl) ⟨443148, by rfl⟩ : syracuseStep 1181729 = 886297) B886297
theorem B886819 : Blo 786339 886819 := bstep (se 1 (by rfl) ⟨665114, by rfl⟩ : syracuseStep 886819 = 1330229) B1330229
theorem B788515 : Blo 786339 788515 := bstep (se 1 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 788515 = 1182773) B1182773
theorem B3999779 : Blo 786339 3999779 := bstep (se 1 (by rfl) ⟨2999834, by rfl⟩ : syracuseStep 3999779 = 5999669) B5999669
theorem B1181747 : Blo 786339 1181747 := bstep (se 1 (by rfl) ⟨886310, by rfl⟩ : syracuseStep 1181747 = 1772621) B1772621
theorem B788531 : Blo 786339 788531 := bstep (se 1 (by rfl) ⟨591398, by rfl⟩ : syracuseStep 788531 = 1182797) B1182797
theorem B788547 : Blo 786339 788547 := bstep (se 1 (by rfl) ⟨591410, by rfl⟩ : syracuseStep 788547 = 1182821) B1182821
theorem B6719557 : Blo 786339 6719557 := bstep (se 4 (by rfl) ⟨629958, by rfl⟩ : syracuseStep 6719557 = 1259917) B1259917
theorem B1181777 : Blo 786339 1181777 := bstep (se 2 (by rfl) ⟨443166, by rfl⟩ : syracuseStep 1181777 = 886333) B886333
theorem B788563 : Blo 786339 788563 := bstep (se 1 (by rfl) ⟨591422, by rfl⟩ : syracuseStep 788563 = 1182845) B1182845
theorem B2394211 : Blo 786339 2394211 := bstep (se 1 (by rfl) ⟨1795658, by rfl⟩ : syracuseStep 2394211 = 3591317) B3591317
theorem B1181795 : Blo 786339 1181795 := bstep (se 1 (by rfl) ⟨886346, by rfl⟩ : syracuseStep 1181795 = 1772693) B1772693
theorem B788579 : Blo 786339 788579 := bstep (se 1 (by rfl) ⟨591434, by rfl⟩ : syracuseStep 788579 = 1182869) B1182869
theorem B30673009 : Blo 786339 30673009 := bstep (se 2 (by rfl) ⟨11502378, by rfl⟩ : syracuseStep 30673009 = 23004757) B23004757
theorem B788595 : Blo 786339 788595 := bstep (se 1 (by rfl) ⟨591446, by rfl⟩ : syracuseStep 788595 = 1182893) B1182893
theorem B1181825 : Blo 786339 1181825 := bstep (se 2 (by rfl) ⟨443184, by rfl⟩ : syracuseStep 1181825 = 886369) B886369
theorem B788611 : Blo 786339 788611 := bstep (se 1 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 788611 = 1182917) B1182917
theorem B1181843 : Blo 786339 1181843 := bstep (se 1 (by rfl) ⟨886382, by rfl⟩ : syracuseStep 1181843 = 1772765) B1772765
theorem B788627 : Blo 786339 788627 := bstep (se 1 (by rfl) ⟨591470, by rfl⟩ : syracuseStep 788627 = 1182941) B1182941
theorem B788643 : Blo 786339 788643 := bstep (se 1 (by rfl) ⟨591482, by rfl⟩ : syracuseStep 788643 = 1182965) B1182965
theorem B1181873 : Blo 786339 1181873 := bstep (se 2 (by rfl) ⟨443202, by rfl⟩ : syracuseStep 1181873 = 886405) B886405
theorem B886963 : Blo 786339 886963 := bstep (se 1 (by rfl) ⟨665222, by rfl⟩ : syracuseStep 886963 = 1330445) B1330445
theorem B788659 : Blo 786339 788659 := bstep (se 1 (by rfl) ⟨591494, by rfl⟩ : syracuseStep 788659 = 1182989) B1182989
theorem B1181891 : Blo 786339 1181891 := bstep (se 1 (by rfl) ⟨886418, by rfl⟩ : syracuseStep 1181891 = 1772837) B1772837
theorem B788675 : Blo 786339 788675 := bstep (se 1 (by rfl) ⟨591506, by rfl⟩ : syracuseStep 788675 = 1183013) B1183013
theorem B788691 : Blo 786339 788691 := bstep (se 1 (by rfl) ⟨591518, by rfl⟩ : syracuseStep 788691 = 1183037) B1183037
theorem B1181921 : Blo 786339 1181921 := bstep (se 2 (by rfl) ⟨443220, by rfl⟩ : syracuseStep 1181921 = 886441) B886441
theorem B1280225 : Blo 786339 1280225 := bstep (se 2 (by rfl) ⟨480084, by rfl⟩ : syracuseStep 1280225 = 960169) B960169
theorem B788707 : Blo 786339 788707 := bstep (se 1 (by rfl) ⟨591530, by rfl⟩ : syracuseStep 788707 = 1183061) B1183061
theorem B4262129 : Blo 786339 4262129 := bstep (se 2 (by rfl) ⟨1598298, by rfl⟩ : syracuseStep 4262129 = 3196597) B3196597
theorem B1181939 : Blo 786339 1181939 := bstep (se 1 (by rfl) ⟨886454, by rfl⟩ : syracuseStep 1181939 = 1772909) B1772909
theorem B788723 : Blo 786339 788723 := bstep (se 1 (by rfl) ⟨591542, by rfl⟩ : syracuseStep 788723 = 1183085) B1183085
theorem B788739 : Blo 786339 788739 := bstep (se 1 (by rfl) ⟨591554, by rfl⟩ : syracuseStep 788739 = 1183109) B1183109
theorem B2656529 : Blo 786339 2656529 := bstep (se 2 (by rfl) ⟨996198, by rfl⟩ : syracuseStep 2656529 = 1992397) B1992397
theorem B1771793 : Blo 786339 1771793 := bstep (se 2 (by rfl) ⟨664422, by rfl⟩ : syracuseStep 1771793 = 1328845) B1328845
theorem B1181969 : Blo 786339 1181969 := bstep (se 2 (by rfl) ⟨443238, by rfl⟩ : syracuseStep 1181969 = 886477) B886477
theorem B788755 : Blo 786339 788755 := bstep (se 1 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 788755 = 1183133) B1183133
theorem B1771811 : Blo 786339 1771811 := bstep (se 1 (by rfl) ⟨1328858, by rfl⟩ : syracuseStep 1771811 = 2657717) B2657717
theorem B1181987 : Blo 786339 1181987 := bstep (se 1 (by rfl) ⟨886490, by rfl⟩ : syracuseStep 1181987 = 1772981) B1772981
theorem B788771 : Blo 786339 788771 := bstep (se 1 (by rfl) ⟨591578, by rfl⟩ : syracuseStep 788771 = 1183157) B1183157
theorem B788787 : Blo 786339 788787 := bstep (se 1 (by rfl) ⟨591590, by rfl⟩ : syracuseStep 788787 = 1183181) B1183181
theorem B1182017 : Blo 786339 1182017 := bstep (se 2 (by rfl) ⟨443256, by rfl⟩ : syracuseStep 1182017 = 886513) B886513
theorem B887107 : Blo 786339 887107 := bstep (se 1 (by rfl) ⟨665330, by rfl⟩ : syracuseStep 887107 = 1330661) B1330661
theorem B788803 : Blo 786339 788803 := bstep (se 1 (by rfl) ⟨591602, by rfl⟩ : syracuseStep 788803 = 1183205) B1183205
theorem B1182035 : Blo 786339 1182035 := bstep (se 1 (by rfl) ⟨886526, by rfl⟩ : syracuseStep 1182035 = 1773053) B1773053
theorem B788819 : Blo 786339 788819 := bstep (se 1 (by rfl) ⟨591614, by rfl⟩ : syracuseStep 788819 = 1183229) B1183229
theorem B788835 : Blo 786339 788835 := bstep (se 1 (by rfl) ⟨591626, by rfl⟩ : syracuseStep 788835 = 1183253) B1183253
theorem B1182065 : Blo 786339 1182065 := bstep (se 2 (by rfl) ⟨443274, by rfl⟩ : syracuseStep 1182065 = 886549) B886549
theorem B788851 : Blo 786339 788851 := bstep (se 1 (by rfl) ⟨591638, by rfl⟩ : syracuseStep 788851 = 1183277) B1183277
theorem B1182083 : Blo 786339 1182083 := bstep (se 1 (by rfl) ⟨886562, by rfl⟩ : syracuseStep 1182083 = 1773125) B1773125
theorem B788867 : Blo 786339 788867 := bstep (se 1 (by rfl) ⟨591650, by rfl⟩ : syracuseStep 788867 = 1183301) B1183301
theorem B788883 : Blo 786339 788883 := bstep (se 1 (by rfl) ⟨591662, by rfl⟩ : syracuseStep 788883 = 1183325) B1183325
theorem B1182113 : Blo 786339 1182113 := bstep (se 2 (by rfl) ⟨443292, by rfl⟩ : syracuseStep 1182113 = 886585) B886585
theorem B788899 : Blo 786339 788899 := bstep (se 1 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 788899 = 1183349) B1183349
theorem B1182131 : Blo 786339 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B788915 : Blo 786339 788915 := bstep (se 1 (by rfl) ⟨591686, by rfl⟩ : syracuseStep 788915 = 1183373) B1183373
theorem B788931 : Blo 786339 788931 := bstep (se 1 (by rfl) ⟨591698, by rfl⟩ : syracuseStep 788931 = 1183397) B1183397
theorem B1182161 : Blo 786339 1182161 := bstep (se 2 (by rfl) ⟨443310, by rfl⟩ : syracuseStep 1182161 = 886621) B886621
theorem B887251 : Blo 786339 887251 := bstep (se 1 (by rfl) ⟨665438, by rfl⟩ : syracuseStep 887251 = 1330877) B1330877
theorem B788947 : Blo 786339 788947 := bstep (se 1 (by rfl) ⟨591710, by rfl⟩ : syracuseStep 788947 = 1183421) B1183421
theorem B1182179 : Blo 786339 1182179 := bstep (se 1 (by rfl) ⟨886634, by rfl⟩ : syracuseStep 1182179 = 1773269) B1773269
theorem B788963 : Blo 786339 788963 := bstep (se 1 (by rfl) ⟨591722, by rfl⟩ : syracuseStep 788963 = 1183445) B1183445
theorem B788979 : Blo 786339 788979 := bstep (se 1 (by rfl) ⟨591734, by rfl⟩ : syracuseStep 788979 = 1183469) B1183469
theorem B1182209 : Blo 786339 1182209 := bstep (se 2 (by rfl) ⟨443328, by rfl⟩ : syracuseStep 1182209 = 886657) B886657
theorem B788995 : Blo 786339 788995 := bstep (se 1 (by rfl) ⟨591746, by rfl⟩ : syracuseStep 788995 = 1183493) B1183493
theorem B1182227 : Blo 786339 1182227 := bstep (se 1 (by rfl) ⟨886670, by rfl⟩ : syracuseStep 1182227 = 1773341) B1773341
theorem B789011 : Blo 786339 789011 := bstep (se 1 (by rfl) ⟨591758, by rfl⟩ : syracuseStep 789011 = 1183517) B1183517
theorem B789027 : Blo 786339 789027 := bstep (se 1 (by rfl) ⟨591770, by rfl⟩ : syracuseStep 789027 = 1183541) B1183541
theorem B1772081 : Blo 786339 1772081 := bstep (se 2 (by rfl) ⟨664530, by rfl⟩ : syracuseStep 1772081 = 1329061) B1329061
theorem B1182257 : Blo 786339 1182257 := bstep (se 2 (by rfl) ⟨443346, by rfl⟩ : syracuseStep 1182257 = 886693) B886693
theorem B789043 : Blo 786339 789043 := bstep (se 1 (by rfl) ⟨591782, by rfl⟩ : syracuseStep 789043 = 1183565) B1183565
theorem B1772099 : Blo 786339 1772099 := bstep (se 1 (by rfl) ⟨1329074, by rfl⟩ : syracuseStep 1772099 = 2658149) B2658149
theorem B1182275 : Blo 786339 1182275 := bstep (se 1 (by rfl) ⟨886706, by rfl⟩ : syracuseStep 1182275 = 1773413) B1773413
theorem B789059 : Blo 786339 789059 := bstep (se 1 (by rfl) ⟨591794, by rfl⟩ : syracuseStep 789059 = 1183589) B1183589
theorem B789075 : Blo 786339 789075 := bstep (se 1 (by rfl) ⟨591806, by rfl⟩ : syracuseStep 789075 = 1183613) B1183613
theorem B1182305 : Blo 786339 1182305 := bstep (se 2 (by rfl) ⟨443364, by rfl⟩ : syracuseStep 1182305 = 886729) B886729
theorem B887395 : Blo 786339 887395 := bstep (se 1 (by rfl) ⟨665546, by rfl⟩ : syracuseStep 887395 = 1331093) B1331093
theorem B789091 : Blo 786339 789091 := bstep (se 1 (by rfl) ⟨591818, by rfl⟩ : syracuseStep 789091 = 1183637) B1183637
theorem B1182323 : Blo 786339 1182323 := bstep (se 1 (by rfl) ⟨886742, by rfl⟩ : syracuseStep 1182323 = 1773485) B1773485
theorem B789107 : Blo 786339 789107 := bstep (se 1 (by rfl) ⟨591830, by rfl⟩ : syracuseStep 789107 = 1183661) B1183661
theorem B789123 : Blo 786339 789123 := bstep (se 1 (by rfl) ⟨591842, by rfl⟩ : syracuseStep 789123 = 1183685) B1183685
theorem B1182353 : Blo 786339 1182353 := bstep (se 2 (by rfl) ⟨443382, by rfl⟩ : syracuseStep 1182353 = 886765) B886765
theorem B789139 : Blo 786339 789139 := bstep (se 1 (by rfl) ⟨591854, by rfl⟩ : syracuseStep 789139 = 1183709) B1183709
theorem B1182371 : Blo 786339 1182371 := bstep (se 1 (by rfl) ⟨886778, by rfl⟩ : syracuseStep 1182371 = 1773557) B1773557
theorem B789155 : Blo 786339 789155 := bstep (se 1 (by rfl) ⟨591866, by rfl⟩ : syracuseStep 789155 = 1183733) B1183733
theorem B789171 : Blo 786339 789171 := bstep (se 1 (by rfl) ⟨591878, by rfl⟩ : syracuseStep 789171 = 1183757) B1183757
theorem B1182401 : Blo 786339 1182401 := bstep (se 2 (by rfl) ⟨443400, by rfl⟩ : syracuseStep 1182401 = 886801) B886801
theorem B789187 : Blo 786339 789187 := bstep (se 1 (by rfl) ⟨591890, by rfl⟩ : syracuseStep 789187 = 1183781) B1183781
theorem B1182419 : Blo 786339 1182419 := bstep (se 1 (by rfl) ⟨886814, by rfl⟩ : syracuseStep 1182419 = 1773629) B1773629
theorem B789203 : Blo 786339 789203 := bstep (se 1 (by rfl) ⟨591902, by rfl⟩ : syracuseStep 789203 = 1183805) B1183805
theorem B789219 : Blo 786339 789219 := bstep (se 1 (by rfl) ⟨591914, by rfl⟩ : syracuseStep 789219 = 1183829) B1183829
theorem B1182449 : Blo 786339 1182449 := bstep (se 2 (by rfl) ⟨443418, by rfl⟩ : syracuseStep 1182449 = 886837) B886837
theorem B887539 : Blo 786339 887539 := bstep (se 1 (by rfl) ⟨665654, by rfl⟩ : syracuseStep 887539 = 1331309) B1331309
theorem B789235 : Blo 786339 789235 := bstep (se 1 (by rfl) ⟨591926, by rfl⟩ : syracuseStep 789235 = 1183853) B1183853
theorem B1182467 : Blo 786339 1182467 := bstep (se 1 (by rfl) ⟨886850, by rfl⟩ : syracuseStep 1182467 = 1773701) B1773701
theorem B789251 : Blo 786339 789251 := bstep (se 1 (by rfl) ⟨591938, by rfl⟩ : syracuseStep 789251 = 1183877) B1183877
theorem B789267 : Blo 786339 789267 := bstep (se 1 (by rfl) ⟨591950, by rfl⟩ : syracuseStep 789267 = 1183901) B1183901
theorem B1182497 : Blo 786339 1182497 := bstep (se 2 (by rfl) ⟨443436, by rfl⟩ : syracuseStep 1182497 = 886873) B886873
theorem B789283 : Blo 786339 789283 := bstep (se 1 (by rfl) ⟨591962, by rfl⟩ : syracuseStep 789283 = 1183925) B1183925
theorem B2657069 : Blo 786339 2657069 := bstep (se 3 (by rfl) ⟨498200, by rfl⟩ : syracuseStep 2657069 = 996401) B996401
theorem B1182515 : Blo 786339 1182515 := bstep (se 1 (by rfl) ⟨886886, by rfl⟩ : syracuseStep 1182515 = 1773773) B1773773
theorem B789299 : Blo 786339 789299 := bstep (se 1 (by rfl) ⟨591974, by rfl⟩ : syracuseStep 789299 = 1183949) B1183949
theorem B789315 : Blo 786339 789315 := bstep (se 1 (by rfl) ⟨591986, by rfl⟩ : syracuseStep 789315 = 1183973) B1183973
theorem B4000589 : Blo 786339 4000589 := bstep (se 3 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 4000589 = 1500221) B1500221
theorem B1772369 : Blo 786339 1772369 := bstep (se 2 (by rfl) ⟨664638, by rfl⟩ : syracuseStep 1772369 = 1329277) B1329277
theorem B1182545 : Blo 786339 1182545 := bstep (se 2 (by rfl) ⟨443454, by rfl⟩ : syracuseStep 1182545 = 886909) B886909
theorem B789331 : Blo 786339 789331 := bstep (se 1 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 789331 = 1183997) B1183997
theorem B2657123 : Blo 786339 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B1772387 : Blo 786339 1772387 := bstep (se 1 (by rfl) ⟨1329290, by rfl⟩ : syracuseStep 1772387 = 2658581) B2658581
theorem B1182563 : Blo 786339 1182563 := bstep (se 1 (by rfl) ⟨886922, by rfl⟩ : syracuseStep 1182563 = 1773845) B1773845
theorem B789347 : Blo 786339 789347 := bstep (se 1 (by rfl) ⟨592010, by rfl⟩ : syracuseStep 789347 = 1184021) B1184021
theorem B789363 : Blo 786339 789363 := bstep (se 1 (by rfl) ⟨592022, by rfl⟩ : syracuseStep 789363 = 1184045) B1184045
theorem B1182593 : Blo 786339 1182593 := bstep (se 2 (by rfl) ⟨443472, by rfl⟩ : syracuseStep 1182593 = 886945) B886945
theorem B887683 : Blo 786339 887683 := bstep (se 1 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 887683 = 1331525) B1331525
theorem B789379 : Blo 786339 789379 := bstep (se 1 (by rfl) ⟨592034, by rfl⟩ : syracuseStep 789379 = 1184069) B1184069
theorem B1182611 : Blo 786339 1182611 := bstep (se 1 (by rfl) ⟨886958, by rfl⟩ : syracuseStep 1182611 = 1773917) B1773917
theorem B789395 : Blo 786339 789395 := bstep (se 1 (by rfl) ⟨592046, by rfl⟩ : syracuseStep 789395 = 1184093) B1184093
theorem B789411 : Blo 786339 789411 := bstep (se 1 (by rfl) ⟨592058, by rfl⟩ : syracuseStep 789411 = 1184117) B1184117
theorem B1182641 : Blo 786339 1182641 := bstep (se 2 (by rfl) ⟨443490, by rfl⟩ : syracuseStep 1182641 = 886981) B886981
theorem B789427 : Blo 786339 789427 := bstep (se 1 (by rfl) ⟨592070, by rfl⟩ : syracuseStep 789427 = 1184141) B1184141
theorem B1182659 : Blo 786339 1182659 := bstep (se 1 (by rfl) ⟨886994, by rfl⟩ : syracuseStep 1182659 = 1773989) B1773989
theorem B789443 : Blo 786339 789443 := bstep (se 1 (by rfl) ⟨592082, by rfl⟩ : syracuseStep 789443 = 1184165) B1184165
theorem B789459 : Blo 786339 789459 := bstep (se 1 (by rfl) ⟨592094, by rfl⟩ : syracuseStep 789459 = 1184189) B1184189
theorem B1182689 : Blo 786339 1182689 := bstep (se 2 (by rfl) ⟨443508, by rfl⟩ : syracuseStep 1182689 = 887017) B887017
theorem B4492259 : Blo 786339 4492259 := bstep (se 1 (by rfl) ⟨3369194, by rfl⟩ : syracuseStep 4492259 = 6738389) B6738389
theorem B789475 : Blo 786339 789475 := bstep (se 1 (by rfl) ⟨592106, by rfl⟩ : syracuseStep 789475 = 1184213) B1184213
theorem B1182707 : Blo 786339 1182707 := bstep (se 1 (by rfl) ⟨887030, by rfl⟩ : syracuseStep 1182707 = 1774061) B1774061
theorem B789491 : Blo 786339 789491 := bstep (se 1 (by rfl) ⟨592118, by rfl⟩ : syracuseStep 789491 = 1184237) B1184237
theorem B789507 : Blo 786339 789507 := bstep (se 1 (by rfl) ⟨592130, by rfl⟩ : syracuseStep 789507 = 1184261) B1184261
theorem B1182737 : Blo 786339 1182737 := bstep (se 2 (by rfl) ⟨443526, by rfl⟩ : syracuseStep 1182737 = 887053) B887053
theorem B887827 : Blo 786339 887827 := bstep (se 1 (by rfl) ⟨665870, by rfl⟩ : syracuseStep 887827 = 1331741) B1331741
theorem B789523 : Blo 786339 789523 := bstep (se 1 (by rfl) ⟨592142, by rfl⟩ : syracuseStep 789523 = 1184285) B1184285
theorem B1182755 : Blo 786339 1182755 := bstep (se 1 (by rfl) ⟨887066, by rfl⟩ : syracuseStep 1182755 = 1774133) B1774133
theorem B789539 : Blo 786339 789539 := bstep (se 1 (by rfl) ⟨592154, by rfl⟩ : syracuseStep 789539 = 1184309) B1184309
theorem B789555 : Blo 786339 789555 := bstep (se 1 (by rfl) ⟨592166, by rfl⟩ : syracuseStep 789555 = 1184333) B1184333
theorem B1182785 : Blo 786339 1182785 := bstep (se 2 (by rfl) ⟨443544, by rfl⟩ : syracuseStep 1182785 = 887089) B887089
theorem B789571 : Blo 786339 789571 := bstep (se 1 (by rfl) ⟨592178, by rfl⟩ : syracuseStep 789571 = 1184357) B1184357
theorem B1182803 : Blo 786339 1182803 := bstep (se 1 (by rfl) ⟨887102, by rfl⟩ : syracuseStep 1182803 = 1774205) B1774205
theorem B789587 : Blo 786339 789587 := bstep (se 1 (by rfl) ⟨592190, by rfl⟩ : syracuseStep 789587 = 1184381) B1184381
theorem B789603 : Blo 786339 789603 := bstep (se 1 (by rfl) ⟨592202, by rfl⟩ : syracuseStep 789603 = 1184405) B1184405
theorem B2657393 : Blo 786339 2657393 := bstep (se 2 (by rfl) ⟨996522, by rfl⟩ : syracuseStep 2657393 = 1993045) B1993045
theorem B1772657 : Blo 786339 1772657 := bstep (se 2 (by rfl) ⟨664746, by rfl⟩ : syracuseStep 1772657 = 1329493) B1329493
theorem B1182833 : Blo 786339 1182833 := bstep (se 2 (by rfl) ⟨443562, by rfl⟩ : syracuseStep 1182833 = 887125) B887125
theorem B789619 : Blo 786339 789619 := bstep (se 1 (by rfl) ⟨592214, by rfl⟩ : syracuseStep 789619 = 1184429) B1184429
theorem B1772675 : Blo 786339 1772675 := bstep (se 1 (by rfl) ⟨1329506, by rfl⟩ : syracuseStep 1772675 = 2659013) B2659013
theorem B1182851 : Blo 786339 1182851 := bstep (se 1 (by rfl) ⟨887138, by rfl⟩ : syracuseStep 1182851 = 1774277) B1774277
theorem B789635 : Blo 786339 789635 := bstep (se 1 (by rfl) ⟨592226, by rfl⟩ : syracuseStep 789635 = 1184453) B1184453
theorem B789651 : Blo 786339 789651 := bstep (se 1 (by rfl) ⟨592238, by rfl⟩ : syracuseStep 789651 = 1184477) B1184477
theorem B1182881 : Blo 786339 1182881 := bstep (se 2 (by rfl) ⟨443580, by rfl⟩ : syracuseStep 1182881 = 887161) B887161
theorem B887971 : Blo 786339 887971 := bstep (se 1 (by rfl) ⟨665978, by rfl⟩ : syracuseStep 887971 = 1331957) B1331957
theorem B789667 : Blo 786339 789667 := bstep (se 1 (by rfl) ⟨592250, by rfl⟩ : syracuseStep 789667 = 1184501) B1184501
theorem B1182899 : Blo 786339 1182899 := bstep (se 1 (by rfl) ⟨887174, by rfl⟩ : syracuseStep 1182899 = 1774349) B1774349
theorem B789683 : Blo 786339 789683 := bstep (se 1 (by rfl) ⟨592262, by rfl⟩ : syracuseStep 789683 = 1184525) B1184525
theorem B789699 : Blo 786339 789699 := bstep (se 1 (by rfl) ⟨592274, by rfl⟩ : syracuseStep 789699 = 1184549) B1184549
theorem B1182929 : Blo 786339 1182929 := bstep (se 2 (by rfl) ⟨443598, by rfl⟩ : syracuseStep 1182929 = 887197) B887197
theorem B789715 : Blo 786339 789715 := bstep (se 1 (by rfl) ⟨592286, by rfl⟩ : syracuseStep 789715 = 1184573) B1184573
theorem B1182947 : Blo 786339 1182947 := bstep (se 1 (by rfl) ⟨887210, by rfl⟩ : syracuseStep 1182947 = 1774421) B1774421
theorem B789731 : Blo 786339 789731 := bstep (se 1 (by rfl) ⟨592298, by rfl⟩ : syracuseStep 789731 = 1184597) B1184597
theorem B789747 : Blo 786339 789747 := bstep (se 1 (by rfl) ⟨592310, by rfl⟩ : syracuseStep 789747 = 1184621) B1184621
theorem B1182977 : Blo 786339 1182977 := bstep (se 2 (by rfl) ⟨443616, by rfl⟩ : syracuseStep 1182977 = 887233) B887233
theorem B789763 : Blo 786339 789763 := bstep (se 1 (by rfl) ⟨592322, by rfl⟩ : syracuseStep 789763 = 1184645) B1184645
theorem B1182995 : Blo 786339 1182995 := bstep (se 1 (by rfl) ⟨887246, by rfl⟩ : syracuseStep 1182995 = 1774493) B1774493
theorem B789779 : Blo 786339 789779 := bstep (se 1 (by rfl) ⟨592334, by rfl⟩ : syracuseStep 789779 = 1184669) B1184669
theorem B789795 : Blo 786339 789795 := bstep (se 1 (by rfl) ⟨592346, by rfl⟩ : syracuseStep 789795 = 1184693) B1184693
theorem B1183025 : Blo 786339 1183025 := bstep (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) B887269
theorem B888115 : Blo 786339 888115 := bstep (se 1 (by rfl) ⟨666086, by rfl⟩ : syracuseStep 888115 = 1332173) B1332173
theorem B789811 : Blo 786339 789811 := bstep (se 1 (by rfl) ⟨592358, by rfl⟩ : syracuseStep 789811 = 1184717) B1184717
theorem B1183043 : Blo 786339 1183043 := bstep (se 1 (by rfl) ⟨887282, by rfl⟩ : syracuseStep 1183043 = 1774565) B1774565
theorem B789827 : Blo 786339 789827 := bstep (se 1 (by rfl) ⟨592370, by rfl⟩ : syracuseStep 789827 = 1184741) B1184741
theorem B789843 : Blo 786339 789843 := bstep (se 1 (by rfl) ⟨592382, by rfl⟩ : syracuseStep 789843 = 1184765) B1184765
theorem B1183073 : Blo 786339 1183073 := bstep (se 2 (by rfl) ⟨443652, by rfl⟩ : syracuseStep 1183073 = 887305) B887305
theorem B789859 : Blo 786339 789859 := bstep (se 1 (by rfl) ⟨592394, by rfl⟩ : syracuseStep 789859 = 1184789) B1184789
theorem B1183091 : Blo 786339 1183091 := bstep (se 1 (by rfl) ⟨887318, by rfl⟩ : syracuseStep 1183091 = 1774637) B1774637
theorem B789875 : Blo 786339 789875 := bstep (se 1 (by rfl) ⟨592406, by rfl⟩ : syracuseStep 789875 = 1184813) B1184813
theorem B789891 : Blo 786339 789891 := bstep (se 1 (by rfl) ⟨592418, by rfl⟩ : syracuseStep 789891 = 1184837) B1184837
theorem B1772945 : Blo 786339 1772945 := bstep (se 2 (by rfl) ⟨664854, by rfl⟩ : syracuseStep 1772945 = 1329709) B1329709
theorem B1183121 : Blo 786339 1183121 := bstep (se 2 (by rfl) ⟨443670, by rfl⟩ : syracuseStep 1183121 = 887341) B887341
theorem B789907 : Blo 786339 789907 := bstep (se 1 (by rfl) ⟨592430, by rfl⟩ : syracuseStep 789907 = 1184861) B1184861
theorem B1772963 : Blo 786339 1772963 := bstep (se 1 (by rfl) ⟨1329722, by rfl⟩ : syracuseStep 1772963 = 2659445) B2659445
theorem B1183139 : Blo 786339 1183139 := bstep (se 1 (by rfl) ⟨887354, by rfl⟩ : syracuseStep 1183139 = 1774709) B1774709
theorem B789923 : Blo 786339 789923 := bstep (se 1 (by rfl) ⟨592442, by rfl⟩ : syracuseStep 789923 = 1184885) B1184885
theorem B789939 : Blo 786339 789939 := bstep (se 1 (by rfl) ⟨592454, by rfl⟩ : syracuseStep 789939 = 1184909) B1184909
theorem B1183169 : Blo 786339 1183169 := bstep (se 2 (by rfl) ⟨443688, by rfl⟩ : syracuseStep 1183169 = 887377) B887377
theorem B888259 : Blo 786339 888259 := bstep (se 1 (by rfl) ⟨666194, by rfl⟩ : syracuseStep 888259 = 1332389) B1332389
theorem B789955 : Blo 786339 789955 := bstep (se 1 (by rfl) ⟨592466, by rfl⟩ : syracuseStep 789955 = 1184933) B1184933
theorem B1183187 : Blo 786339 1183187 := bstep (se 1 (by rfl) ⟨887390, by rfl⟩ : syracuseStep 1183187 = 1774781) B1774781
theorem B789971 : Blo 786339 789971 := bstep (se 1 (by rfl) ⟨592478, by rfl⟩ : syracuseStep 789971 = 1184957) B1184957
theorem B789987 : Blo 786339 789987 := bstep (se 1 (by rfl) ⟨592490, by rfl⟩ : syracuseStep 789987 = 1184981) B1184981
theorem B1183217 : Blo 786339 1183217 := bstep (se 2 (by rfl) ⟨443706, by rfl⟩ : syracuseStep 1183217 = 887413) B887413
theorem B790003 : Blo 786339 790003 := bstep (se 1 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 790003 = 1185005) B1185005
theorem B1183235 : Blo 786339 1183235 := bstep (se 1 (by rfl) ⟨887426, by rfl⟩ : syracuseStep 1183235 = 1774853) B1774853
theorem B790019 : Blo 786339 790019 := bstep (se 1 (by rfl) ⟨592514, by rfl⟩ : syracuseStep 790019 = 1185029) B1185029
theorem B790035 : Blo 786339 790035 := bstep (se 1 (by rfl) ⟨592526, by rfl⟩ : syracuseStep 790035 = 1185053) B1185053
theorem B1183265 : Blo 786339 1183265 := bstep (se 2 (by rfl) ⟨443724, by rfl⟩ : syracuseStep 1183265 = 887449) B887449
theorem B790051 : Blo 786339 790051 := bstep (se 1 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 790051 = 1185077) B1185077
theorem B1347121 : Blo 786339 1347121 := bstep (se 2 (by rfl) ⟨505170, by rfl⟩ : syracuseStep 1347121 = 1010341) B1010341
theorem B1183283 : Blo 786339 1183283 := bstep (se 1 (by rfl) ⟨887462, by rfl⟩ : syracuseStep 1183283 = 1774925) B1774925
theorem B790067 : Blo 786339 790067 := bstep (se 1 (by rfl) ⟨592550, by rfl⟩ : syracuseStep 790067 = 1185101) B1185101
theorem B790083 : Blo 786339 790083 := bstep (se 1 (by rfl) ⟨592562, by rfl⟩ : syracuseStep 790083 = 1185125) B1185125
theorem B1183313 : Blo 786339 1183313 := bstep (se 2 (by rfl) ⟨443742, by rfl⟩ : syracuseStep 1183313 = 887485) B887485
theorem B888403 : Blo 786339 888403 := bstep (se 1 (by rfl) ⟨666302, by rfl⟩ : syracuseStep 888403 = 1332605) B1332605
theorem B790099 : Blo 786339 790099 := bstep (se 1 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 790099 = 1185149) B1185149
theorem B1183331 : Blo 786339 1183331 := bstep (se 1 (by rfl) ⟨887498, by rfl⟩ : syracuseStep 1183331 = 1774997) B1774997
theorem B790115 : Blo 786339 790115 := bstep (se 1 (by rfl) ⟨592586, by rfl⟩ : syracuseStep 790115 = 1185173) B1185173
theorem B790131 : Blo 786339 790131 := bstep (se 1 (by rfl) ⟨592598, by rfl⟩ : syracuseStep 790131 = 1185197) B1185197
theorem B1183361 : Blo 786339 1183361 := bstep (se 2 (by rfl) ⟨443760, by rfl⟩ : syracuseStep 1183361 = 887521) B887521
theorem B790147 : Blo 786339 790147 := bstep (se 1 (by rfl) ⟨592610, by rfl⟩ : syracuseStep 790147 = 1185221) B1185221
theorem B2657933 : Blo 786339 2657933 := bstep (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) B996725
theorem B1183379 : Blo 786339 1183379 := bstep (se 1 (by rfl) ⟨887534, by rfl⟩ : syracuseStep 1183379 = 1775069) B1775069
theorem B790163 : Blo 786339 790163 := bstep (se 1 (by rfl) ⟨592622, by rfl⟩ : syracuseStep 790163 = 1185245) B1185245
theorem B790179 : Blo 786339 790179 := bstep (se 1 (by rfl) ⟨592634, by rfl⟩ : syracuseStep 790179 = 1185269) B1185269
theorem B1773233 : Blo 786339 1773233 := bstep (se 2 (by rfl) ⟨664962, by rfl⟩ : syracuseStep 1773233 = 1329925) B1329925
theorem B1183409 : Blo 786339 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B790195 : Blo 786339 790195 := bstep (se 1 (by rfl) ⟨592646, by rfl⟩ : syracuseStep 790195 = 1185293) B1185293
theorem B2657987 : Blo 786339 2657987 := bstep (se 1 (by rfl) ⟨1993490, by rfl⟩ : syracuseStep 2657987 = 3986981) B3986981
theorem B1773251 : Blo 786339 1773251 := bstep (se 1 (by rfl) ⟨1329938, by rfl⟩ : syracuseStep 1773251 = 2659877) B2659877
theorem B1183427 : Blo 786339 1183427 := bstep (se 1 (by rfl) ⟨887570, by rfl⟩ : syracuseStep 1183427 = 1775141) B1775141
theorem B790211 : Blo 786339 790211 := bstep (se 1 (by rfl) ⟨592658, by rfl⟩ : syracuseStep 790211 = 1185317) B1185317
theorem B790227 : Blo 786339 790227 := bstep (se 1 (by rfl) ⟨592670, by rfl⟩ : syracuseStep 790227 = 1185341) B1185341
theorem B1183457 : Blo 786339 1183457 := bstep (se 2 (by rfl) ⟨443796, by rfl⟩ : syracuseStep 1183457 = 887593) B887593
theorem B888547 : Blo 786339 888547 := bstep (se 1 (by rfl) ⟨666410, by rfl⟩ : syracuseStep 888547 = 1332821) B1332821
theorem B790243 : Blo 786339 790243 := bstep (se 1 (by rfl) ⟨592682, by rfl⟩ : syracuseStep 790243 = 1185365) B1185365
theorem B1183475 : Blo 786339 1183475 := bstep (se 1 (by rfl) ⟨887606, by rfl⟩ : syracuseStep 1183475 = 1775213) B1775213
theorem B790259 : Blo 786339 790259 := bstep (se 1 (by rfl) ⟨592694, by rfl⟩ : syracuseStep 790259 = 1185389) B1185389
theorem B790275 : Blo 786339 790275 := bstep (se 1 (by rfl) ⟨592706, by rfl⟩ : syracuseStep 790275 = 1185413) B1185413
theorem B1183505 : Blo 786339 1183505 := bstep (se 2 (by rfl) ⟨443814, by rfl⟩ : syracuseStep 1183505 = 887629) B887629
theorem B790291 : Blo 786339 790291 := bstep (se 1 (by rfl) ⟨592718, by rfl⟩ : syracuseStep 790291 = 1185437) B1185437
theorem B1183523 : Blo 786339 1183523 := bstep (se 1 (by rfl) ⟨887642, by rfl⟩ : syracuseStep 1183523 = 1775285) B1775285
theorem B790307 : Blo 786339 790307 := bstep (se 1 (by rfl) ⟨592730, by rfl⟩ : syracuseStep 790307 = 1185461) B1185461
theorem B790323 : Blo 786339 790323 := bstep (se 1 (by rfl) ⟨592742, by rfl⟩ : syracuseStep 790323 = 1185485) B1185485
theorem B1183553 : Blo 786339 1183553 := bstep (se 2 (by rfl) ⟨443832, by rfl⟩ : syracuseStep 1183553 = 887665) B887665
theorem B790339 : Blo 786339 790339 := bstep (se 1 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 790339 = 1185509) B1185509
theorem B1183571 : Blo 786339 1183571 := bstep (se 1 (by rfl) ⟨887678, by rfl⟩ : syracuseStep 1183571 = 1775357) B1775357
theorem B1183601 : Blo 786339 1183601 := bstep (se 2 (by rfl) ⟨443850, by rfl⟩ : syracuseStep 1183601 = 887701) B887701
theorem B888691 : Blo 786339 888691 := bstep (se 1 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 888691 = 1333037) B1333037
theorem B1183619 : Blo 786339 1183619 := bstep (se 1 (by rfl) ⟨887714, by rfl⟩ : syracuseStep 1183619 = 1775429) B1775429
theorem B1183649 : Blo 786339 1183649 := bstep (se 2 (by rfl) ⟨443868, by rfl⟩ : syracuseStep 1183649 = 887737) B887737
theorem B2527139 : Blo 786339 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B1183667 : Blo 786339 1183667 := bstep (se 1 (by rfl) ⟨887750, by rfl⟩ : syracuseStep 1183667 = 1775501) B1775501
theorem B2658257 : Blo 786339 2658257 := bstep (se 2 (by rfl) ⟨996846, by rfl⟩ : syracuseStep 2658257 = 1993693) B1993693
theorem B1773521 : Blo 786339 1773521 := bstep (se 2 (by rfl) ⟨665070, by rfl⟩ : syracuseStep 1773521 = 1330141) B1330141
theorem B1183697 : Blo 786339 1183697 := bstep (se 2 (by rfl) ⟨443886, by rfl⟩ : syracuseStep 1183697 = 887773) B887773
theorem B1773539 : Blo 786339 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B1183715 : Blo 786339 1183715 := bstep (se 1 (by rfl) ⟨887786, by rfl⟩ : syracuseStep 1183715 = 1775573) B1775573
theorem B1183745 : Blo 786339 1183745 := bstep (se 2 (by rfl) ⟨443904, by rfl⟩ : syracuseStep 1183745 = 887809) B887809
theorem B888835 : Blo 786339 888835 := bstep (se 1 (by rfl) ⟨666626, by rfl⟩ : syracuseStep 888835 = 1333253) B1333253
theorem B1183763 : Blo 786339 1183763 := bstep (se 1 (by rfl) ⟨887822, by rfl⟩ : syracuseStep 1183763 = 1775645) B1775645
theorem B1183793 : Blo 786339 1183793 := bstep (se 2 (by rfl) ⟨443922, by rfl⟩ : syracuseStep 1183793 = 887845) B887845
theorem B1183811 : Blo 786339 1183811 := bstep (se 1 (by rfl) ⟨887858, by rfl⟩ : syracuseStep 1183811 = 1775717) B1775717
theorem B1183841 : Blo 786339 1183841 := bstep (se 2 (by rfl) ⟨443940, by rfl⟩ : syracuseStep 1183841 = 887881) B887881
theorem B1183859 : Blo 786339 1183859 := bstep (se 1 (by rfl) ⟨887894, by rfl⟩ : syracuseStep 1183859 = 1775789) B1775789
theorem B1183889 : Blo 786339 1183889 := bstep (se 2 (by rfl) ⟨443958, by rfl⟩ : syracuseStep 1183889 = 887917) B887917
theorem B888979 : Blo 786339 888979 := bstep (se 1 (by rfl) ⟨666734, by rfl⟩ : syracuseStep 888979 = 1333469) B1333469
theorem B1183907 : Blo 786339 1183907 := bstep (se 1 (by rfl) ⟨887930, by rfl⟩ : syracuseStep 1183907 = 1775861) B1775861
theorem B2691245 : Blo 786339 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B1183937 : Blo 786339 1183937 := bstep (se 2 (by rfl) ⟨443976, by rfl⟩ : syracuseStep 1183937 = 887953) B887953
theorem B1183955 : Blo 786339 1183955 := bstep (se 1 (by rfl) ⟨887966, by rfl⟩ : syracuseStep 1183955 = 1775933) B1775933
theorem B1773809 : Blo 786339 1773809 := bstep (se 2 (by rfl) ⟨665178, by rfl⟩ : syracuseStep 1773809 = 1330357) B1330357
theorem B1183985 : Blo 786339 1183985 := bstep (se 2 (by rfl) ⟨443994, by rfl⟩ : syracuseStep 1183985 = 887989) B887989
theorem B1773827 : Blo 786339 1773827 := bstep (se 1 (by rfl) ⟨1330370, by rfl⟩ : syracuseStep 1773827 = 2660741) B2660741
theorem B1184003 : Blo 786339 1184003 := bstep (se 1 (by rfl) ⟨888002, by rfl⟩ : syracuseStep 1184003 = 1776005) B1776005
theorem B1184033 : Blo 786339 1184033 := bstep (se 2 (by rfl) ⟨444012, by rfl⟩ : syracuseStep 1184033 = 888025) B888025
theorem B889123 : Blo 786339 889123 := bstep (se 1 (by rfl) ⟨666842, by rfl⟩ : syracuseStep 889123 = 1333685) B1333685
theorem B1184051 : Blo 786339 1184051 := bstep (se 1 (by rfl) ⟨888038, by rfl⟩ : syracuseStep 1184051 = 1776077) B1776077
theorem B1184081 : Blo 786339 1184081 := bstep (se 2 (by rfl) ⟨444030, by rfl⟩ : syracuseStep 1184081 = 888061) B888061
theorem B1184099 : Blo 786339 1184099 := bstep (se 1 (by rfl) ⟨888074, by rfl⟩ : syracuseStep 1184099 = 1776149) B1776149
theorem B1184129 : Blo 786339 1184129 := bstep (se 2 (by rfl) ⟨444048, by rfl⟩ : syracuseStep 1184129 = 888097) B888097
theorem B1184147 : Blo 786339 1184147 := bstep (se 1 (by rfl) ⟨888110, by rfl⟩ : syracuseStep 1184147 = 1776221) B1776221
theorem B1184177 : Blo 786339 1184177 := bstep (se 2 (by rfl) ⟨444066, by rfl⟩ : syracuseStep 1184177 = 888133) B888133
theorem B1184195 : Blo 786339 1184195 := bstep (se 1 (by rfl) ⟨888146, by rfl⟩ : syracuseStep 1184195 = 1776293) B1776293
theorem B1184225 : Blo 786339 1184225 := bstep (se 2 (by rfl) ⟨444084, by rfl⟩ : syracuseStep 1184225 = 888169) B888169
theorem B2658797 : Blo 786339 2658797 := bstep (se 3 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 2658797 = 997049) B997049
theorem B1184243 : Blo 786339 1184243 := bstep (se 1 (by rfl) ⟨888182, by rfl⟩ : syracuseStep 1184243 = 1776365) B1776365
theorem B1774097 : Blo 786339 1774097 := bstep (se 2 (by rfl) ⟨665286, by rfl⟩ : syracuseStep 1774097 = 1330573) B1330573
theorem B1184273 : Blo 786339 1184273 := bstep (se 2 (by rfl) ⟨444102, by rfl⟩ : syracuseStep 1184273 = 888205) B888205
theorem B2658851 : Blo 786339 2658851 := bstep (se 1 (by rfl) ⟨1994138, by rfl⟩ : syracuseStep 2658851 = 3988277) B3988277
theorem B1774115 : Blo 786339 1774115 := bstep (se 1 (by rfl) ⟨1330586, by rfl⟩ : syracuseStep 1774115 = 2661173) B2661173
theorem B1184291 : Blo 786339 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B1184321 : Blo 786339 1184321 := bstep (se 2 (by rfl) ⟨444120, by rfl⟩ : syracuseStep 1184321 = 888241) B888241
theorem B1184339 : Blo 786339 1184339 := bstep (se 1 (by rfl) ⟨888254, by rfl⟩ : syracuseStep 1184339 = 1776509) B1776509
theorem B1184369 : Blo 786339 1184369 := bstep (se 2 (by rfl) ⟨444138, by rfl⟩ : syracuseStep 1184369 = 888277) B888277
theorem B1184387 : Blo 786339 1184387 := bstep (se 1 (by rfl) ⟨888290, by rfl⟩ : syracuseStep 1184387 = 1776581) B1776581
theorem B1184417 : Blo 786339 1184417 := bstep (se 2 (by rfl) ⟨444156, by rfl⟩ : syracuseStep 1184417 = 888313) B888313
theorem B1184435 : Blo 786339 1184435 := bstep (se 1 (by rfl) ⟨888326, by rfl⟩ : syracuseStep 1184435 = 1776653) B1776653
theorem B1184465 : Blo 786339 1184465 := bstep (se 2 (by rfl) ⟨444174, by rfl⟩ : syracuseStep 1184465 = 888349) B888349
theorem B1184483 : Blo 786339 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B2527985 : Blo 786339 2527985 := bstep (se 2 (by rfl) ⟨947994, by rfl⟩ : syracuseStep 2527985 = 1895989) B1895989
theorem B1184513 : Blo 786339 1184513 := bstep (se 2 (by rfl) ⟨444192, by rfl⟩ : syracuseStep 1184513 = 888385) B888385
theorem B1184531 : Blo 786339 1184531 := bstep (se 1 (by rfl) ⟨888398, by rfl⟩ : syracuseStep 1184531 = 1776797) B1776797
theorem B2659121 : Blo 786339 2659121 := bstep (se 2 (by rfl) ⟨997170, by rfl⟩ : syracuseStep 2659121 = 1994341) B1994341
theorem B1774385 : Blo 786339 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B1184561 : Blo 786339 1184561 := bstep (se 2 (by rfl) ⟨444210, by rfl⟩ : syracuseStep 1184561 = 888421) B888421
theorem B1774403 : Blo 786339 1774403 := bstep (se 1 (by rfl) ⟨1330802, by rfl⟩ : syracuseStep 1774403 = 2661605) B2661605
theorem B1184579 : Blo 786339 1184579 := bstep (se 1 (by rfl) ⟨888434, by rfl⟩ : syracuseStep 1184579 = 1776869) B1776869
theorem B4494149 : Blo 786339 4494149 := bstep (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) B842653
theorem B1184609 : Blo 786339 1184609 := bstep (se 2 (by rfl) ⟨444228, by rfl⟩ : syracuseStep 1184609 = 888457) B888457
theorem B2986865 : Blo 786339 2986865 := bstep (se 2 (by rfl) ⟨1120074, by rfl⟩ : syracuseStep 2986865 = 2240149) B2240149
theorem B1184627 : Blo 786339 1184627 := bstep (se 1 (by rfl) ⟨888470, by rfl⟩ : syracuseStep 1184627 = 1776941) B1776941
theorem B1184657 : Blo 786339 1184657 := bstep (se 2 (by rfl) ⟨444246, by rfl⟩ : syracuseStep 1184657 = 888493) B888493
theorem B1184675 : Blo 786339 1184675 := bstep (se 1 (by rfl) ⟨888506, by rfl⟩ : syracuseStep 1184675 = 1777013) B1777013
theorem B2134957 : Blo 786339 2134957 := bstep (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) B800609
theorem B1184705 : Blo 786339 1184705 := bstep (se 2 (by rfl) ⟨444264, by rfl⟩ : syracuseStep 1184705 = 888529) B888529
theorem B1184723 : Blo 786339 1184723 := bstep (se 1 (by rfl) ⟨888542, by rfl⟩ : syracuseStep 1184723 = 1777085) B1777085
theorem B1184753 : Blo 786339 1184753 := bstep (se 2 (by rfl) ⟨444282, by rfl⟩ : syracuseStep 1184753 = 888565) B888565
theorem B1184771 : Blo 786339 1184771 := bstep (se 1 (by rfl) ⟨888578, by rfl⟩ : syracuseStep 1184771 = 1777157) B1777157
theorem B1184801 : Blo 786339 1184801 := bstep (se 2 (by rfl) ⟨444300, by rfl⟩ : syracuseStep 1184801 = 888601) B888601
theorem B1184819 : Blo 786339 1184819 := bstep (se 1 (by rfl) ⟨888614, by rfl⟩ : syracuseStep 1184819 = 1777229) B1777229
theorem B1774673 : Blo 786339 1774673 := bstep (se 2 (by rfl) ⟨665502, by rfl⟩ : syracuseStep 1774673 = 1331005) B1331005
theorem B1184849 : Blo 786339 1184849 := bstep (se 2 (by rfl) ⟨444318, by rfl⟩ : syracuseStep 1184849 = 888637) B888637
theorem B1774691 : Blo 786339 1774691 := bstep (se 1 (by rfl) ⟨1331018, by rfl⟩ : syracuseStep 1774691 = 2662037) B2662037
theorem B1184867 : Blo 786339 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B1184897 : Blo 786339 1184897 := bstep (se 2 (by rfl) ⟨444336, by rfl⟩ : syracuseStep 1184897 = 888673) B888673
theorem B2364547 : Blo 786339 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B1184915 : Blo 786339 1184915 := bstep (se 1 (by rfl) ⟨888686, by rfl⟩ : syracuseStep 1184915 = 1777373) B1777373
theorem B1184945 : Blo 786339 1184945 := bstep (se 2 (by rfl) ⟨444354, by rfl⟩ : syracuseStep 1184945 = 888709) B888709
theorem B1184963 : Blo 786339 1184963 := bstep (se 1 (by rfl) ⟨888722, by rfl⟩ : syracuseStep 1184963 = 1777445) B1777445
theorem B1184993 : Blo 786339 1184993 := bstep (se 2 (by rfl) ⟨444372, by rfl⟩ : syracuseStep 1184993 = 888745) B888745
theorem B1185011 : Blo 786339 1185011 := bstep (se 1 (by rfl) ⟨888758, by rfl⟩ : syracuseStep 1185011 = 1777517) B1777517
theorem B1185041 : Blo 786339 1185041 := bstep (se 2 (by rfl) ⟨444390, by rfl⟩ : syracuseStep 1185041 = 888781) B888781
theorem B1185059 : Blo 786339 1185059 := bstep (se 1 (by rfl) ⟨888794, by rfl⟩ : syracuseStep 1185059 = 1777589) B1777589
theorem B1185089 : Blo 786339 1185089 := bstep (se 2 (by rfl) ⟨444408, by rfl⟩ : syracuseStep 1185089 = 888817) B888817
theorem B2659661 : Blo 786339 2659661 := bstep (se 3 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 2659661 = 997373) B997373
theorem B1185107 : Blo 786339 1185107 := bstep (se 1 (by rfl) ⟨888830, by rfl⟩ : syracuseStep 1185107 = 1777661) B1777661
theorem B1774961 : Blo 786339 1774961 := bstep (se 2 (by rfl) ⟨665610, by rfl⟩ : syracuseStep 1774961 = 1331221) B1331221
theorem B1185137 : Blo 786339 1185137 := bstep (se 2 (by rfl) ⟨444426, by rfl⟩ : syracuseStep 1185137 = 888853) B888853
theorem B1119619 : Blo 786339 1119619 := bstep (se 1 (by rfl) ⟨839714, by rfl⟩ : syracuseStep 1119619 = 1679429) B1679429
theorem B2659715 : Blo 786339 2659715 := bstep (se 1 (by rfl) ⟨1994786, by rfl⟩ : syracuseStep 2659715 = 3989573) B3989573
theorem B1774979 : Blo 786339 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B1185155 : Blo 786339 1185155 := bstep (se 1 (by rfl) ⟨888866, by rfl⟩ : syracuseStep 1185155 = 1777733) B1777733
theorem B1185185 : Blo 786339 1185185 := bstep (se 2 (by rfl) ⟨444444, by rfl⟩ : syracuseStep 1185185 = 888889) B888889
theorem B1185203 : Blo 786339 1185203 := bstep (se 1 (by rfl) ⟨888902, by rfl⟩ : syracuseStep 1185203 = 1777805) B1777805
theorem B1185233 : Blo 786339 1185233 := bstep (se 2 (by rfl) ⟨444462, by rfl⟩ : syracuseStep 1185233 = 888925) B888925
theorem B1185251 : Blo 786339 1185251 := bstep (se 1 (by rfl) ⟨888938, by rfl⟩ : syracuseStep 1185251 = 1777877) B1777877
theorem B1185281 : Blo 786339 1185281 := bstep (se 2 (by rfl) ⟨444480, by rfl⟩ : syracuseStep 1185281 = 888961) B888961
theorem B1185299 : Blo 786339 1185299 := bstep (se 1 (by rfl) ⟨888974, by rfl⟩ : syracuseStep 1185299 = 1777949) B1777949
theorem B1185329 : Blo 786339 1185329 := bstep (se 2 (by rfl) ⟨444498, by rfl⟩ : syracuseStep 1185329 = 888997) B888997
theorem B1185347 : Blo 786339 1185347 := bstep (se 1 (by rfl) ⟨889010, by rfl⟩ : syracuseStep 1185347 = 1778021) B1778021
theorem B1185377 : Blo 786339 1185377 := bstep (se 2 (by rfl) ⟨444516, by rfl⟩ : syracuseStep 1185377 = 889033) B889033
theorem B2692721 : Blo 786339 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B1185395 : Blo 786339 1185395 := bstep (se 1 (by rfl) ⟨889046, by rfl⟩ : syracuseStep 1185395 = 1778093) B1778093
theorem B2659985 : Blo 786339 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B1775249 : Blo 786339 1775249 := bstep (se 2 (by rfl) ⟨665718, by rfl⟩ : syracuseStep 1775249 = 1331437) B1331437
theorem B1185425 : Blo 786339 1185425 := bstep (se 2 (by rfl) ⟨444534, by rfl⟩ : syracuseStep 1185425 = 889069) B889069
theorem B1775267 : Blo 786339 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B1185443 : Blo 786339 1185443 := bstep (se 1 (by rfl) ⟨889082, by rfl⟩ : syracuseStep 1185443 = 1778165) B1778165
theorem B1185473 : Blo 786339 1185473 := bstep (se 2 (by rfl) ⟨444552, by rfl⟩ : syracuseStep 1185473 = 889105) B889105
theorem B1185491 : Blo 786339 1185491 := bstep (se 1 (by rfl) ⟨889118, by rfl⟩ : syracuseStep 1185491 = 1778237) B1778237
theorem B1120177 : Blo 786339 1120177 := bstep (se 2 (by rfl) ⟨420066, by rfl⟩ : syracuseStep 1120177 = 840133) B840133
theorem B1775537 : Blo 786339 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1775555 : Blo 786339 1775555 := bstep (se 1 (by rfl) ⟨1331666, by rfl⟩ : syracuseStep 1775555 = 2663333) B2663333
theorem B2398349 : Blo 786339 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B2660525 : Blo 786339 2660525 := bstep (se 3 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 2660525 = 997697) B997697
theorem B1775825 : Blo 786339 1775825 := bstep (se 2 (by rfl) ⟨665934, by rfl⟩ : syracuseStep 1775825 = 1331869) B1331869
theorem B2660579 : Blo 786339 2660579 := bstep (se 1 (by rfl) ⟨1995434, by rfl⟩ : syracuseStep 2660579 = 3990869) B3990869
theorem B1775843 : Blo 786339 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B2988323 : Blo 786339 2988323 := bstep (se 1 (by rfl) ⟨2241242, by rfl⟩ : syracuseStep 2988323 = 4482485) B4482485
theorem B4790755 : Blo 786339 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B2660849 : Blo 786339 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B1776113 : Blo 786339 1776113 := bstep (se 2 (by rfl) ⟨666042, by rfl⟩ : syracuseStep 1776113 = 1332085) B1332085
theorem B1776131 : Blo 786339 1776131 := bstep (se 1 (by rfl) ⟨1332098, by rfl⟩ : syracuseStep 1776131 = 2664197) B2664197
theorem B2529805 : Blo 786339 2529805 := bstep (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) B948677
theorem B1120883 : Blo 786339 1120883 := bstep (se 1 (by rfl) ⟨840662, by rfl⟩ : syracuseStep 1120883 = 1681325) B1681325
theorem B1776401 : Blo 786339 1776401 := bstep (se 2 (by rfl) ⟨666150, by rfl⟩ : syracuseStep 1776401 = 1332301) B1332301
theorem B1776419 : Blo 786339 1776419 := bstep (se 1 (by rfl) ⟨1332314, by rfl⟩ : syracuseStep 1776419 = 2664629) B2664629
theorem B1350515 : Blo 786339 1350515 := bstep (se 1 (by rfl) ⟨1012886, by rfl⟩ : syracuseStep 1350515 = 2025773) B2025773
theorem B2661389 : Blo 786339 2661389 := bstep (se 3 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 2661389 = 998021) B998021
theorem B1776689 : Blo 786339 1776689 := bstep (se 2 (by rfl) ⟨666258, by rfl⟩ : syracuseStep 1776689 = 1332517) B1332517
theorem B8985653 : Blo 786339 8985653 := bstep (se 5 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 8985653 = 842405) B842405
theorem B2661443 : Blo 786339 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1776707 : Blo 786339 1776707 := bstep (se 1 (by rfl) ⟨1332530, by rfl⟩ : syracuseStep 1776707 = 2665061) B2665061
theorem B1350739 : Blo 786339 1350739 := bstep (se 1 (by rfl) ⟨1013054, by rfl⟩ : syracuseStep 1350739 = 2026109) B2026109
theorem B1121521 : Blo 786339 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B2989325 : Blo 786339 2989325 := bstep (se 3 (by rfl) ⟨560498, by rfl⟩ : syracuseStep 2989325 = 1120997) B1120997
theorem B2661713 : Blo 786339 2661713 := bstep (se 2 (by rfl) ⟨998142, by rfl⟩ : syracuseStep 2661713 = 1996285) B1996285
theorem B1776977 : Blo 786339 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B1121635 : Blo 786339 1121635 := bstep (se 1 (by rfl) ⟨841226, by rfl⟩ : syracuseStep 1121635 = 1682453) B1682453
theorem B1776995 : Blo 786339 1776995 := bstep (se 1 (by rfl) ⟨1332746, by rfl⟩ : syracuseStep 1776995 = 2665493) B2665493
theorem B5054021 : Blo 786339 5054021 := bstep (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) B947629
theorem B1777265 : Blo 786339 1777265 := bstep (se 2 (by rfl) ⟨666474, by rfl⟩ : syracuseStep 1777265 = 1332949) B1332949
theorem B1777283 : Blo 786339 1777283 := bstep (se 1 (by rfl) ⟨1332962, by rfl⟩ : syracuseStep 1777283 = 2665925) B2665925
theorem B6397795 : Blo 786339 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B2662253 : Blo 786339 2662253 := bstep (se 3 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 2662253 = 998345) B998345
theorem B1515395 : Blo 786339 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B1777553 : Blo 786339 1777553 := bstep (se 2 (by rfl) ⟨666582, by rfl⟩ : syracuseStep 1777553 = 1333165) B1333165
theorem B2662307 : Blo 786339 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B1777571 : Blo 786339 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B5480561 : Blo 786339 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B2662577 : Blo 786339 2662577 := bstep (se 2 (by rfl) ⟨998466, by rfl⟩ : syracuseStep 2662577 = 1996933) B1996933
theorem B1777841 : Blo 786339 1777841 := bstep (se 2 (by rfl) ⟨666690, by rfl⟩ : syracuseStep 1777841 = 1333381) B1333381
theorem B1777859 : Blo 786339 1777859 := bstep (se 1 (by rfl) ⟨1333394, by rfl⟩ : syracuseStep 1777859 = 2666789) B2666789
theorem B9248995 : Blo 786339 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B13476293 : Blo 786339 13476293 := bstep (se 4 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 13476293 = 2526805) B2526805
theorem B1778129 : Blo 786339 1778129 := bstep (se 2 (by rfl) ⟨666798, by rfl⟩ : syracuseStep 1778129 = 1333597) B1333597
theorem B1778147 : Blo 786339 1778147 := bstep (se 1 (by rfl) ⟨1333610, by rfl⟩ : syracuseStep 1778147 = 2667221) B2667221
theorem B1516195 : Blo 786339 1516195 := bstep (se 1 (by rfl) ⟨1137146, by rfl⟩ : syracuseStep 1516195 = 2274293) B2274293
theorem B1122979 : Blo 786339 1122979 := bstep (se 1 (by rfl) ⟨842234, by rfl⟩ : syracuseStep 1122979 = 1684469) B1684469
theorem B2663117 : Blo 786339 2663117 := bstep (se 3 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 2663117 = 998669) B998669
theorem B2663171 : Blo 786339 2663171 := bstep (se 1 (by rfl) ⟨1997378, by rfl⟩ : syracuseStep 2663171 = 3994757) B3994757
theorem B8528753 : Blo 786339 8528753 := bstep (se 2 (by rfl) ⟨3198282, by rfl⟩ : syracuseStep 8528753 = 6396565) B6396565
theorem B2663441 : Blo 786339 2663441 := bstep (se 2 (by rfl) ⟨998790, by rfl⟩ : syracuseStep 2663441 = 1997581) B1997581
theorem B1680497 : Blo 786339 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B2270531 : Blo 786339 2270531 := bstep (se 1 (by rfl) ⟨1702898, by rfl⟩ : syracuseStep 2270531 = 3405797) B3405797
theorem B2991437 : Blo 786339 2991437 := bstep (se 3 (by rfl) ⟨560894, by rfl⟩ : syracuseStep 2991437 = 1121789) B1121789
theorem B20194757 : Blo 786339 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B2663981 : Blo 786339 2663981 := bstep (se 3 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 2663981 = 998993) B998993
theorem B2664035 : Blo 786339 2664035 := bstep (se 1 (by rfl) ⟨1998026, by rfl⟩ : syracuseStep 2664035 = 3996053) B3996053
theorem B1124113 : Blo 786339 1124113 := bstep (se 2 (by rfl) ⟨421542, by rfl⟩ : syracuseStep 1124113 = 843085) B843085
theorem B2664305 : Blo 786339 2664305 := bstep (se 2 (by rfl) ⟨999114, by rfl⟩ : syracuseStep 2664305 = 1998229) B1998229
theorem B1124209 : Blo 786339 1124209 := bstep (se 2 (by rfl) ⟨421578, by rfl⟩ : syracuseStep 1124209 = 843157) B843157
theorem B8071109 : Blo 786339 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B1681393 : Blo 786339 1681393 := bstep (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) B1261045
theorem B1681411 : Blo 786339 1681411 := bstep (se 1 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 1681411 = 2522117) B2522117
theorem B2992241 : Blo 786339 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B5056739 : Blo 786339 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B3778829 : Blo 786339 3778829 := bstep (se 3 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 3778829 = 1417061) B1417061
theorem B1124705 : Blo 786339 1124705 := bstep (se 2 (by rfl) ⟨421764, by rfl⟩ : syracuseStep 1124705 = 843529) B843529
theorem B2664845 : Blo 786339 2664845 := bstep (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) B999317
theorem B2664899 : Blo 786339 2664899 := bstep (se 1 (by rfl) ⟨1998674, by rfl⟩ : syracuseStep 2664899 = 3997349) B3997349
theorem B4499981 : Blo 786339 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B2697745 : Blo 786339 2697745 := bstep (se 2 (by rfl) ⟨1011654, by rfl⟩ : syracuseStep 2697745 = 2023309) B2023309
theorem B6728305 : Blo 786339 6728305 := bstep (se 2 (by rfl) ⟨2523114, by rfl⟩ : syracuseStep 6728305 = 5046229) B5046229
theorem B2665169 : Blo 786339 2665169 := bstep (se 2 (by rfl) ⟨999438, by rfl⟩ : syracuseStep 2665169 = 1998877) B1998877
theorem B4270819 : Blo 786339 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B7383821 : Blo 786339 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B2992909 : Blo 786339 2992909 := bstep (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) B1122341
theorem B5974883 : Blo 786339 5974883 := bstep (se 1 (by rfl) ⟨4481162, by rfl⟩ : syracuseStep 5974883 = 8962325) B8962325
theorem B5385221 : Blo 786339 5385221 := bstep (se 4 (by rfl) ⟨504864, by rfl⟩ : syracuseStep 5385221 = 1009729) B1009729
theorem B2665709 : Blo 786339 2665709 := bstep (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) B999641
theorem B2665763 : Blo 786339 2665763 := bstep (se 1 (by rfl) ⟨1999322, by rfl⟩ : syracuseStep 2665763 = 3998645) B3998645
theorem B2993699 : Blo 786339 2993699 := bstep (se 1 (by rfl) ⟨2245274, by rfl⟩ : syracuseStep 2993699 = 4490549) B4490549
theorem B2666033 : Blo 786339 2666033 := bstep (se 2 (by rfl) ⟨999762, by rfl⟩ : syracuseStep 2666033 = 1999525) B1999525
theorem B2240081 : Blo 786339 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B9875141 : Blo 786339 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B5746403 : Blo 786339 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B5385989 : Blo 786339 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B2699021 : Blo 786339 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B15150989 : Blo 786339 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B995267 : Blo 786339 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B2666573 : Blo 786339 2666573 := bstep (se 3 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 2666573 = 999965) B999965
theorem B2666627 : Blo 786339 2666627 := bstep (se 1 (by rfl) ⟨1999970, by rfl⟩ : syracuseStep 2666627 = 3999941) B3999941
theorem B2994353 : Blo 786339 2994353 := bstep (se 2 (by rfl) ⟨1122882, by rfl⟩ : syracuseStep 2994353 = 2245765) B2245765
theorem B5058737 : Blo 786339 5058737 := bstep (se 2 (by rfl) ⟨1897026, by rfl⟩ : syracuseStep 5058737 = 3794053) B3794053
theorem B1683683 : Blo 786339 1683683 := bstep (se 1 (by rfl) ⟨1262762, by rfl⟩ : syracuseStep 1683683 = 2525525) B2525525
theorem B1421617 : Blo 786339 1421617 := bstep (se 2 (by rfl) ⟨533106, by rfl⟩ : syracuseStep 1421617 = 1066213) B1066213
theorem B2666897 : Blo 786339 2666897 := bstep (se 2 (by rfl) ⟨1000086, by rfl⟩ : syracuseStep 2666897 = 2000173) B2000173
theorem B2241037 : Blo 786339 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B995971 : Blo 786339 995971 := bstep (se 1 (by rfl) ⟨746978, by rfl⟩ : syracuseStep 995971 = 1493957) B1493957
theorem B1684145 : Blo 786339 1684145 := bstep (se 2 (by rfl) ⟨631554, by rfl⟩ : syracuseStep 1684145 = 1263109) B1263109
theorem B996067 : Blo 786339 996067 := bstep (se 1 (by rfl) ⟨747050, by rfl⟩ : syracuseStep 996067 = 1494101) B1494101
theorem B2241265 : Blo 786339 2241265 := bstep (se 2 (by rfl) ⟨840474, by rfl⟩ : syracuseStep 2241265 = 1680949) B1680949
theorem B3191665 : Blo 786339 3191665 := bstep (se 2 (by rfl) ⟨1196874, by rfl⟩ : syracuseStep 3191665 = 2393749) B2393749
theorem B2241425 : Blo 786339 2241425 := bstep (se 2 (by rfl) ⟨840534, by rfl⟩ : syracuseStep 2241425 = 1681069) B1681069
theorem B2241539 : Blo 786339 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B996563 : Blo 786339 996563 := bstep (se 1 (by rfl) ⟨747422, by rfl⟩ : syracuseStep 996563 = 1494845) B1494845
theorem B5682545 : Blo 786339 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B8074637 : Blo 786339 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B38352325 : Blo 786339 38352325 := bstep (se 4 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 38352325 = 7191061) B7191061
theorem B17315299 : Blo 786339 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B2995811 : Blo 786339 2995811 := bstep (se 1 (by rfl) ⟨2246858, by rfl⟩ : syracuseStep 2995811 = 4493717) B4493717
theorem B2995825 : Blo 786339 2995825 := bstep (se 2 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 2995825 = 2246869) B2246869
theorem B997267 : Blo 786339 997267 := bstep (se 1 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 997267 = 1495901) B1495901
theorem B1685443 : Blo 786339 1685443 := bstep (se 1 (by rfl) ⟨1264082, by rfl⟩ : syracuseStep 1685443 = 2528165) B2528165
theorem B2242541 : Blo 786339 2242541 := bstep (se 3 (by rfl) ⟨420476, by rfl⟩ : syracuseStep 2242541 = 840953) B840953
theorem B997363 : Blo 786339 997363 := bstep (se 1 (by rfl) ⟨748022, by rfl⟩ : syracuseStep 997363 = 1496045) B1496045
theorem B2242723 : Blo 786339 2242723 := bstep (se 1 (by rfl) ⟨1682042, by rfl⟩ : syracuseStep 2242723 = 3364085) B3364085
theorem B1685699 : Blo 786339 1685699 := bstep (se 1 (by rfl) ⟨1264274, by rfl⟩ : syracuseStep 1685699 = 2528549) B2528549
theorem B2242883 : Blo 786339 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B1063315 : Blo 786339 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B997859 : Blo 786339 997859 := bstep (se 1 (by rfl) ⟨748394, by rfl⟩ : syracuseStep 997859 = 1496789) B1496789
theorem B1423939 : Blo 786339 1423939 := bstep (se 1 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 1423939 = 2135909) B2135909
theorem B5061197 : Blo 786339 5061197 := bstep (se 3 (by rfl) ⟨948974, by rfl⟩ : syracuseStep 5061197 = 1897949) B1897949
theorem B1260289 : Blo 786339 1260289 := bstep (se 2 (by rfl) ⟨472608, by rfl⟩ : syracuseStep 1260289 = 945217) B945217
theorem B1686353 : Blo 786339 1686353 := bstep (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) B1264765
theorem B8960867 : Blo 786339 8960867 := bstep (se 1 (by rfl) ⟨6720650, by rfl⟩ : syracuseStep 8960867 = 13441301) B13441301
theorem B900019 : Blo 786339 900019 := bstep (se 1 (by rfl) ⟨675014, by rfl⟩ : syracuseStep 900019 = 1350029) B1350029
theorem B2997283 : Blo 786339 2997283 := bstep (se 1 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 2997283 = 4495925) B4495925
theorem B1686673 : Blo 786339 1686673 := bstep (se 2 (by rfl) ⟨632502, by rfl⟩ : syracuseStep 1686673 = 1265005) B1265005
theorem B998563 : Blo 786339 998563 := bstep (se 1 (by rfl) ⟨748922, by rfl⟩ : syracuseStep 998563 = 1497845) B1497845
theorem B998659 : Blo 786339 998659 := bstep (se 1 (by rfl) ⟨748994, by rfl⟩ : syracuseStep 998659 = 1497989) B1497989
theorem B2243953 : Blo 786339 2243953 := bstep (se 2 (by rfl) ⟨841482, by rfl⟩ : syracuseStep 2243953 = 1682965) B1682965
theorem B1261091 : Blo 786339 1261091 := bstep (se 1 (by rfl) ⟨945818, by rfl⟩ : syracuseStep 1261091 = 1891637) B1891637
theorem B999155 : Blo 786339 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B4800269 : Blo 786339 4800269 := bstep (se 3 (by rfl) ⟨900050, by rfl⟩ : syracuseStep 4800269 = 1800101) B1800101
theorem B1687331 : Blo 786339 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B1195841 : Blo 786339 1195841 := bstep (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) B896881
theorem B6733637 : Blo 786339 6733637 := bstep (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) B1262557
theorem B1327009 : Blo 786339 1327009 := bstep (se 2 (by rfl) ⟨497628, by rfl⟩ : syracuseStep 1327009 = 995257) B995257
theorem B1327043 : Blo 786339 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B1294321 : Blo 786339 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B1261603 : Blo 786339 1261603 := bstep (se 1 (by rfl) ⟨946202, by rfl⟩ : syracuseStep 1261603 = 1892405) B1892405
theorem B1327171 : Blo 786339 1327171 := bstep (se 1 (by rfl) ⟨995378, by rfl⟩ : syracuseStep 1327171 = 1990757) B1990757
theorem B5980229 : Blo 786339 5980229 := bstep (se 4 (by rfl) ⟨560646, by rfl⟩ : syracuseStep 5980229 = 1121293) B1121293
theorem B901219 : Blo 786339 901219 := bstep (se 1 (by rfl) ⟨675914, by rfl⟩ : syracuseStep 901219 = 1351829) B1351829
theorem B5390477 : Blo 786339 5390477 := bstep (se 3 (by rfl) ⟨1010714, by rfl⟩ : syracuseStep 5390477 = 2021429) B2021429
theorem B1327313 : Blo 786339 1327313 := bstep (se 2 (by rfl) ⟨497742, by rfl⟩ : syracuseStep 1327313 = 995485) B995485
theorem B5193989 : Blo 786339 5193989 := bstep (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) B973873
theorem B1327441 : Blo 786339 1327441 := bstep (se 2 (by rfl) ⟨497790, by rfl⟩ : syracuseStep 1327441 = 995581) B995581
theorem B1327475 : Blo 786339 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B999859 : Blo 786339 999859 := bstep (se 1 (by rfl) ⟨749894, by rfl⟩ : syracuseStep 999859 = 1499789) B1499789
theorem B1196497 : Blo 786339 1196497 := bstep (se 2 (by rfl) ⟨448686, by rfl⟩ : syracuseStep 1196497 = 897373) B897373
theorem B2834929 : Blo 786339 2834929 := bstep (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) B2126197
theorem B1327603 : Blo 786339 1327603 := bstep (se 1 (by rfl) ⟨995702, by rfl⟩ : syracuseStep 1327603 = 1991405) B1991405
theorem B999955 : Blo 786339 999955 := bstep (se 1 (by rfl) ⟨749966, by rfl⟩ : syracuseStep 999955 = 1499933) B1499933
theorem B1065521 : Blo 786339 1065521 := bstep (se 2 (by rfl) ⟨399570, by rfl⟩ : syracuseStep 1065521 = 799141) B799141
theorem B1262147 : Blo 786339 1262147 := bstep (se 1 (by rfl) ⟨946610, by rfl⟩ : syracuseStep 1262147 = 1893221) B1893221
theorem B2245229 : Blo 786339 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B1327745 : Blo 786339 1327745 := bstep (se 2 (by rfl) ⟨497904, by rfl⟩ : syracuseStep 1327745 = 995809) B995809
theorem B10109681 : Blo 786339 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B1262321 : Blo 786339 1262321 := bstep (se 2 (by rfl) ⟨473370, by rfl⟩ : syracuseStep 1262321 = 946741) B946741
theorem B4801265 : Blo 786339 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B1327873 : Blo 786339 1327873 := bstep (se 2 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 1327873 = 995905) B995905
theorem B2245411 : Blo 786339 2245411 := bstep (se 1 (by rfl) ⟨1684058, by rfl⟩ : syracuseStep 2245411 = 3368117) B3368117
theorem B1327907 : Blo 786339 1327907 := bstep (se 1 (by rfl) ⟨995930, by rfl⟩ : syracuseStep 1327907 = 1991861) B1991861
theorem B2245457 : Blo 786339 2245457 := bstep (se 2 (by rfl) ⟨842046, by rfl⟩ : syracuseStep 2245457 = 1684093) B1684093
theorem B1328035 : Blo 786339 1328035 := bstep (se 1 (by rfl) ⟨996026, by rfl⟩ : syracuseStep 1328035 = 1992053) B1992053
theorem B4309937 : Blo 786339 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B1328177 : Blo 786339 1328177 := bstep (se 2 (by rfl) ⟨498066, by rfl⟩ : syracuseStep 1328177 = 996133) B996133
theorem B1197155 : Blo 786339 1197155 := bstep (se 1 (by rfl) ⟨897866, by rfl⟩ : syracuseStep 1197155 = 1795733) B1795733
theorem B2278541 : Blo 786339 2278541 := bstep (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) B854453
theorem B1328305 : Blo 786339 1328305 := bstep (se 2 (by rfl) ⟨498114, by rfl⟩ : syracuseStep 1328305 = 996229) B996229
theorem B2999501 : Blo 786339 2999501 := bstep (se 3 (by rfl) ⟨562406, by rfl⟩ : syracuseStep 2999501 = 1124813) B1124813
theorem B1328339 : Blo 786339 1328339 := bstep (se 1 (by rfl) ⟨996254, by rfl⟩ : syracuseStep 1328339 = 1992509) B1992509
theorem B8209649 : Blo 786339 8209649 := bstep (se 2 (by rfl) ⟨3078618, by rfl⟩ : syracuseStep 8209649 = 6157237) B6157237
theorem B1066321 : Blo 786339 1066321 := bstep (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) B799741
theorem B1328467 : Blo 786339 1328467 := bstep (se 1 (by rfl) ⟨996350, by rfl⟩ : syracuseStep 1328467 = 1992701) B1992701
theorem B3982769 : Blo 786339 3982769 := bstep (se 2 (by rfl) ⟨1493538, by rfl⟩ : syracuseStep 3982769 = 2987077) B2987077
theorem B2278865 : Blo 786339 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B1328609 : Blo 786339 1328609 := bstep (se 2 (by rfl) ⟨498228, by rfl⟩ : syracuseStep 1328609 = 996457) B996457
theorem B1328737 : Blo 786339 1328737 := bstep (se 2 (by rfl) ⟨498276, by rfl⟩ : syracuseStep 1328737 = 996553) B996553
theorem B1328771 : Blo 786339 1328771 := bstep (se 1 (by rfl) ⟨996578, by rfl⟩ : syracuseStep 1328771 = 1993157) B1993157
theorem B5129891 : Blo 786339 5129891 := bstep (se 1 (by rfl) ⟨3847418, by rfl⟩ : syracuseStep 5129891 = 7694837) B7694837
theorem B1328899 : Blo 786339 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B1329041 : Blo 786339 1329041 := bstep (se 2 (by rfl) ⟨498390, by rfl⟩ : syracuseStep 1329041 = 996781) B996781
theorem B1492931 : Blo 786339 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B1329169 : Blo 786339 1329169 := bstep (se 2 (by rfl) ⟨498438, by rfl⟩ : syracuseStep 1329169 = 996877) B996877
theorem B1329203 : Blo 786339 1329203 := bstep (se 1 (by rfl) ⟨996902, by rfl⟩ : syracuseStep 1329203 = 1993805) B1993805
theorem B3000419 : Blo 786339 3000419 := bstep (se 1 (by rfl) ⟨2250314, by rfl⟩ : syracuseStep 3000419 = 4500629) B4500629
theorem B8407153 : Blo 786339 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B6408305 : Blo 786339 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B8505485 : Blo 786339 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1329331 : Blo 786339 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1198273 : Blo 786339 1198273 := bstep (se 2 (by rfl) ⟨449352, by rfl⟩ : syracuseStep 1198273 = 898705) B898705
theorem B21547235 : Blo 786339 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B3361009 : Blo 786339 3361009 := bstep (se 2 (by rfl) ⟨1260378, by rfl⟩ : syracuseStep 3361009 = 2520757) B2520757
theorem B10799345 : Blo 786339 10799345 := bstep (se 2 (by rfl) ⟨4049754, by rfl⟩ : syracuseStep 10799345 = 8099509) B8099509
theorem B2246915 : Blo 786339 2246915 := bstep (se 1 (by rfl) ⟨1685186, by rfl⟩ : syracuseStep 2246915 = 3370373) B3370373
theorem B1329473 : Blo 786339 1329473 := bstep (se 2 (by rfl) ⟨498552, by rfl⟩ : syracuseStep 1329473 = 997105) B997105
theorem B1329601 : Blo 786339 1329601 := bstep (se 2 (by rfl) ⟨498600, by rfl⟩ : syracuseStep 1329601 = 997201) B997201
theorem B8997317 : Blo 786339 8997317 := bstep (se 4 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 8997317 = 1686997) B1686997
theorem B1329635 : Blo 786339 1329635 := bstep (se 1 (by rfl) ⟨997226, by rfl⟩ : syracuseStep 1329635 = 1994453) B1994453
theorem B1198579 : Blo 786339 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B1329763 : Blo 786339 1329763 := bstep (se 1 (by rfl) ⟨997322, by rfl⟩ : syracuseStep 1329763 = 1994645) B1994645
theorem B1264339 : Blo 786339 1264339 := bstep (se 1 (by rfl) ⟨948254, by rfl⟩ : syracuseStep 1264339 = 1896509) B1896509
theorem B1329905 : Blo 786339 1329905 := bstep (se 2 (by rfl) ⟨498714, by rfl⟩ : syracuseStep 1329905 = 997429) B997429
theorem B1264403 : Blo 786339 1264403 := bstep (se 1 (by rfl) ⟨948302, by rfl⟩ : syracuseStep 1264403 = 1896605) B1896605
theorem B3984227 : Blo 786339 3984227 := bstep (se 1 (by rfl) ⟨2988170, by rfl⟩ : syracuseStep 3984227 = 5976341) B5976341
theorem B1493873 : Blo 786339 1493873 := bstep (se 2 (by rfl) ⟨560202, by rfl⟩ : syracuseStep 1493873 = 1120405) B1120405
theorem B1330033 : Blo 786339 1330033 := bstep (se 2 (by rfl) ⟨498762, by rfl⟩ : syracuseStep 1330033 = 997525) B997525
theorem B1330067 : Blo 786339 1330067 := bstep (se 1 (by rfl) ⟨997550, by rfl⟩ : syracuseStep 1330067 = 1995101) B1995101
theorem B1330195 : Blo 786339 1330195 := bstep (se 1 (by rfl) ⟨997646, by rfl⟩ : syracuseStep 1330195 = 1995293) B1995293
theorem B10112141 : Blo 786339 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B1330337 : Blo 786339 1330337 := bstep (se 2 (by rfl) ⟨498876, by rfl⟩ : syracuseStep 1330337 = 997753) B997753
theorem B1330465 : Blo 786339 1330465 := bstep (se 2 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 1330465 = 997849) B997849
theorem B1330499 : Blo 786339 1330499 := bstep (se 1 (by rfl) ⟨997874, by rfl⟩ : syracuseStep 1330499 = 1995749) B1995749
theorem B1330627 : Blo 786339 1330627 := bstep (se 1 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 1330627 = 1995941) B1995941
theorem B2248145 : Blo 786339 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B2837987 : Blo 786339 2837987 := bstep (se 1 (by rfl) ⟨2128490, by rfl⟩ : syracuseStep 2837987 = 4256981) B4256981
theorem B1330769 : Blo 786339 1330769 := bstep (se 2 (by rfl) ⟨499038, by rfl⟩ : syracuseStep 1330769 = 998077) B998077
theorem B3985037 : Blo 786339 3985037 := bstep (se 3 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 3985037 = 1494389) B1494389
theorem B1330897 : Blo 786339 1330897 := bstep (se 2 (by rfl) ⟨499086, by rfl⟩ : syracuseStep 1330897 = 998173) B998173
theorem B1265377 : Blo 786339 1265377 := bstep (se 2 (by rfl) ⟨474516, by rfl⟩ : syracuseStep 1265377 = 949033) B949033
theorem B1494769 : Blo 786339 1494769 := bstep (se 2 (by rfl) ⟨560538, by rfl⟩ : syracuseStep 1494769 = 1121077) B1121077
theorem B1330931 : Blo 786339 1330931 := bstep (se 1 (by rfl) ⟨998198, by rfl⟩ : syracuseStep 1330931 = 1996397) B1996397
theorem B15126385 : Blo 786339 15126385 := bstep (se 2 (by rfl) ⟨5672394, by rfl⟩ : syracuseStep 15126385 = 11344789) B11344789
theorem B1331059 : Blo 786339 1331059 := bstep (se 1 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 1331059 = 1996589) B1996589
theorem B1494929 : Blo 786339 1494929 := bstep (se 2 (by rfl) ⟨560598, by rfl⟩ : syracuseStep 1494929 = 1121197) B1121197
theorem B16175045 : Blo 786339 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1265633 : Blo 786339 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B1331201 : Blo 786339 1331201 := bstep (se 2 (by rfl) ⟨499200, by rfl⟩ : syracuseStep 1331201 = 998401) B998401
theorem B1331329 : Blo 786339 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B1265825 : Blo 786339 1265825 := bstep (se 2 (by rfl) ⟨474684, by rfl⟩ : syracuseStep 1265825 = 949369) B949369
theorem B3788963 : Blo 786339 3788963 := bstep (se 1 (by rfl) ⟨2841722, by rfl⟩ : syracuseStep 3788963 = 5683445) B5683445
theorem B1331363 : Blo 786339 1331363 := bstep (se 1 (by rfl) ⟨998522, by rfl⟩ : syracuseStep 1331363 = 1997045) B1997045
theorem B1495331 : Blo 786339 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B1331491 : Blo 786339 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B7590257 : Blo 786339 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B1331633 : Blo 786339 1331633 := bstep (se 2 (by rfl) ⟨499362, by rfl⟩ : syracuseStep 1331633 = 998725) B998725
theorem B1331761 : Blo 786339 1331761 := bstep (se 2 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 1331761 = 998821) B998821
theorem B1331795 : Blo 786339 1331795 := bstep (se 1 (by rfl) ⟨998846, by rfl⟩ : syracuseStep 1331795 = 1997693) B1997693
theorem B3789517 : Blo 786339 3789517 := bstep (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) B1421069
theorem B1331923 : Blo 786339 1331923 := bstep (se 1 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 1331923 = 1997885) B1997885
theorem B1332065 : Blo 786339 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B2249603 : Blo 786339 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B1332193 : Blo 786339 1332193 := bstep (se 2 (by rfl) ⟨499572, by rfl⟩ : syracuseStep 1332193 = 999145) B999145
theorem B1332227 : Blo 786339 1332227 := bstep (se 1 (by rfl) ⟨999170, by rfl⟩ : syracuseStep 1332227 = 1998341) B1998341
theorem B2184259 : Blo 786339 2184259 := bstep (se 1 (by rfl) ⟨1638194, by rfl⟩ : syracuseStep 2184259 = 3276389) B3276389
theorem B1332355 : Blo 786339 1332355 := bstep (se 1 (by rfl) ⟨999266, by rfl⟩ : syracuseStep 1332355 = 1998533) B1998533
theorem B1496227 : Blo 786339 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B1332497 : Blo 786339 1332497 := bstep (se 2 (by rfl) ⟨499686, by rfl⟩ : syracuseStep 1332497 = 999373) B999373
theorem B840979 : Blo 786339 840979 := bstep (se 1 (by rfl) ⟨630734, by rfl⟩ : syracuseStep 840979 = 1261469) B1261469
theorem B1496387 : Blo 786339 1496387 := bstep (se 1 (by rfl) ⟨1122290, by rfl⟩ : syracuseStep 1496387 = 2244581) B2244581
theorem B5199173 : Blo 786339 5199173 := bstep (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) B974845
theorem B1332625 : Blo 786339 1332625 := bstep (se 2 (by rfl) ⟨499734, by rfl⟩ : syracuseStep 1332625 = 999469) B999469
theorem B1332659 : Blo 786339 1332659 := bstep (se 1 (by rfl) ⟨999494, by rfl⟩ : syracuseStep 1332659 = 1998989) B1998989
theorem B1332787 : Blo 786339 1332787 := bstep (se 1 (by rfl) ⟨999590, by rfl⟩ : syracuseStep 1332787 = 1999181) B1999181
theorem B2250413 : Blo 786339 2250413 := bstep (se 3 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 2250413 = 843905) B843905
theorem B2021041 : Blo 786339 2021041 := bstep (se 2 (by rfl) ⟨757890, by rfl⟩ : syracuseStep 2021041 = 1515781) B1515781
theorem B1332929 : Blo 786339 1332929 := bstep (se 2 (by rfl) ⟨499848, by rfl⟩ : syracuseStep 1332929 = 999697) B999697
theorem B5986061 : Blo 786339 5986061 := bstep (se 3 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 5986061 = 2244773) B2244773
theorem B1333057 : Blo 786339 1333057 := bstep (se 2 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 1333057 = 999793) B999793
theorem B3364685 : Blo 786339 3364685 := bstep (se 3 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 3364685 = 1261757) B1261757
theorem B1333091 : Blo 786339 1333091 := bstep (se 1 (by rfl) ⟨999818, by rfl⟩ : syracuseStep 1333091 = 1999637) B1999637
theorem B2250605 : Blo 786339 2250605 := bstep (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) B843977
theorem B1333219 : Blo 786339 1333219 := bstep (se 1 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 1333219 = 1999829) B1999829
theorem B3790961 : Blo 786339 3790961 := bstep (se 2 (by rfl) ⟨1421610, by rfl⟩ : syracuseStep 3790961 = 2843221) B2843221
theorem B1333361 : Blo 786339 1333361 := bstep (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) B1000021
theorem B1333489 : Blo 786339 1333489 := bstep (se 2 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 1333489 = 1000117) B1000117
theorem B1333523 : Blo 786339 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B1136963 : Blo 786339 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2021699 : Blo 786339 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B1497457 : Blo 786339 1497457 := bstep (se 2 (by rfl) ⟨561546, by rfl⟩ : syracuseStep 1497457 = 1123093) B1123093
theorem B1333651 : Blo 786339 1333651 := bstep (se 1 (by rfl) ⟨1000238, by rfl⟩ : syracuseStep 1333651 = 2000477) B2000477
theorem B1825187 : Blo 786339 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1268177 : Blo 786339 1268177 := bstep (se 2 (by rfl) ⟨475566, by rfl⟩ : syracuseStep 1268177 = 951133) B951133
theorem B1595875 : Blo 786339 1595875 := bstep (se 1 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 1595875 = 2393813) B2393813
theorem B3987953 : Blo 786339 3987953 := bstep (se 2 (by rfl) ⟨1495482, by rfl⟩ : syracuseStep 3987953 = 2990965) B2990965
theorem B842243 : Blo 786339 842243 := bstep (se 1 (by rfl) ⟨631682, by rfl⟩ : syracuseStep 842243 = 1263365) B1263365
theorem B7592717 : Blo 786339 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B1137539 : Blo 786339 1137539 := bstep (se 1 (by rfl) ⟨853154, by rfl⟩ : syracuseStep 1137539 = 1706309) B1706309
theorem B4480069 : Blo 786339 4480069 := bstep (se 4 (by rfl) ⟨420006, by rfl⟩ : syracuseStep 4480069 = 840013) B840013
theorem B1596611 : Blo 786339 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B842995 : Blo 786339 842995 := bstep (se 1 (by rfl) ⟨632246, by rfl⟩ : syracuseStep 842995 = 1264493) B1264493
theorem B8543501 : Blo 786339 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B810307 : Blo 786339 810307 := bstep (se 1 (by rfl) ⟨607730, by rfl⟩ : syracuseStep 810307 = 1215461) B1215461
theorem B1498513 : Blo 786339 1498513 := bstep (se 2 (by rfl) ⟨561942, by rfl⟩ : syracuseStep 1498513 = 1123885) B1123885
theorem B6741701 : Blo 786339 6741701 := bstep (se 4 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 6741701 = 1264069) B1264069
theorem B3792653 : Blo 786339 3792653 := bstep (se 3 (by rfl) ⟨711122, by rfl⟩ : syracuseStep 3792653 = 1422245) B1422245
theorem B1498915 : Blo 786339 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B1498961 : Blo 786339 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B3989411 : Blo 786339 3989411 := bstep (se 1 (by rfl) ⟨2992058, by rfl⟩ : syracuseStep 3989411 = 5984117) B5984117
theorem B1990595 : Blo 786339 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B4251683 : Blo 786339 4251683 := bstep (se 1 (by rfl) ⟨3188762, by rfl⟩ : syracuseStep 4251683 = 6377525) B6377525
theorem B9592901 : Blo 786339 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B1499249 : Blo 786339 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B1597649 : Blo 786339 1597649 := bstep (se 2 (by rfl) ⟨599118, by rfl⟩ : syracuseStep 1597649 = 1198237) B1198237
theorem B6742385 : Blo 786339 6742385 := bstep (se 2 (by rfl) ⟨2528394, by rfl⟩ : syracuseStep 6742385 = 5056789) B5056789
theorem B2155075 : Blo 786339 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B5988977 : Blo 786339 5988977 := bstep (se 2 (by rfl) ⟨2245866, by rfl⟩ : syracuseStep 5988977 = 4491733) B4491733
theorem B3990221 : Blo 786339 3990221 := bstep (se 3 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 3990221 = 1496333) B1496333
theorem B1499971 : Blo 786339 1499971 := bstep (se 1 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 1499971 = 2249957) B2249957
theorem B3597155 : Blo 786339 3597155 := bstep (se 1 (by rfl) ⟨2697866, by rfl⟩ : syracuseStep 3597155 = 5395733) B5395733
theorem B1991537 : Blo 786339 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B1991587 : Blo 786339 1991587 := bstep (se 1 (by rfl) ⟨1493690, by rfl⟩ : syracuseStep 1991587 = 2987381) B2987381
theorem B4482053 : Blo 786339 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B1991729 : Blo 786339 1991729 := bstep (se 2 (by rfl) ⟨746898, by rfl⟩ : syracuseStep 1991729 = 1493797) B1493797
theorem B1795139 : Blo 786339 1795139 := bstep (se 1 (by rfl) ⟨1346354, by rfl⟩ : syracuseStep 1795139 = 2692709) B2692709
theorem B1893635 : Blo 786339 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B3237347 : Blo 786339 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B1894097 : Blo 786339 1894097 := bstep (se 2 (by rfl) ⟨710286, by rfl⟩ : syracuseStep 1894097 = 1420573) B1420573
theorem B1992721 : Blo 786339 1992721 := bstep (se 2 (by rfl) ⟨747270, by rfl⟩ : syracuseStep 1992721 = 1494541) B1494541
theorem B3369059 : Blo 786339 3369059 := bstep (se 1 (by rfl) ⟨2526794, by rfl⟩ : syracuseStep 3369059 = 5053589) B5053589
theorem B2844877 : Blo 786339 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B1992995 : Blo 786339 1992995 := bstep (se 1 (by rfl) ⟨1494746, by rfl⟩ : syracuseStep 1992995 = 2989493) B2989493
theorem B1993187 : Blo 786339 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1600163 : Blo 786339 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B10775267 : Blo 786339 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B1796899 : Blo 786339 1796899 := bstep (se 1 (by rfl) ⟨1347674, by rfl⟩ : syracuseStep 1796899 = 2695349) B2695349
theorem B30272453 : Blo 786339 30272453 := bstep (se 4 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 30272453 = 5676085) B5676085
theorem B10087537 : Blo 786339 10087537 := bstep (se 2 (by rfl) ⟨3782826, by rfl⟩ : syracuseStep 10087537 = 7565653) B7565653
theorem B3697777 : Blo 786339 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B1010819 : Blo 786339 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B1994129 : Blo 786339 1994129 := bstep (se 2 (by rfl) ⟨747798, by rfl⟩ : syracuseStep 1994129 = 1495597) B1495597
theorem B1994179 : Blo 786339 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B3993137 : Blo 786339 3993137 := bstep (se 2 (by rfl) ⟨1497426, by rfl⟩ : syracuseStep 3993137 = 2994853) B2994853
theorem B1994321 : Blo 786339 1994321 := bstep (se 2 (by rfl) ⟨747870, by rfl⟩ : syracuseStep 1994321 = 1495741) B1495741
theorem B1601201 : Blo 786339 1601201 := bstep (se 2 (by rfl) ⟨600450, by rfl⟩ : syracuseStep 1601201 = 1200901) B1200901
theorem B2846449 : Blo 786339 2846449 := bstep (se 2 (by rfl) ⟨1067418, by rfl⟩ : syracuseStep 2846449 = 2134837) B2134837
theorem B5041925 : Blo 786339 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B3371057 : Blo 786339 3371057 := bstep (se 2 (by rfl) ⟨1264146, by rfl⟩ : syracuseStep 3371057 = 2528293) B2528293
theorem B1732963 : Blo 786339 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B2126189 : Blo 786339 2126189 := bstep (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) B797321
theorem B1995313 : Blo 786339 1995313 := bstep (se 2 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 1995313 = 1496485) B1496485
theorem B13628017 : Blo 786339 13628017 := bstep (se 2 (by rfl) ⟨5110506, by rfl⟩ : syracuseStep 13628017 = 10221013) B10221013
theorem B1897219 : Blo 786339 1897219 := bstep (se 1 (by rfl) ⟨1422914, by rfl⟩ : syracuseStep 1897219 = 2845829) B2845829
theorem B4485901 : Blo 786339 4485901 := bstep (se 3 (by rfl) ⟨841106, by rfl⟩ : syracuseStep 4485901 = 1682213) B1682213
theorem B1995587 : Blo 786339 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1897411 : Blo 786339 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B3994595 : Blo 786339 3994595 := bstep (se 1 (by rfl) ⟨2995946, by rfl⟩ : syracuseStep 3994595 = 5991893) B5991893
theorem B1995779 : Blo 786339 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B8090723 : Blo 786339 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B1897681 : Blo 786339 1897681 := bstep (se 2 (by rfl) ⟨711630, by rfl⟩ : syracuseStep 1897681 = 1423261) B1423261
theorem B15398257 : Blo 786339 15398257 := bstep (se 2 (by rfl) ⟨5774346, by rfl⟩ : syracuseStep 15398257 = 11548693) B11548693
theorem B3601955 : Blo 786339 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B3372749 : Blo 786339 3372749 := bstep (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) B1264781
theorem B947971 : Blo 786339 947971 := bstep (se 1 (by rfl) ⟨710978, by rfl⟩ : syracuseStep 947971 = 1421957) B1421957
theorem B3995405 : Blo 786339 3995405 := bstep (se 3 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 3995405 = 1498277) B1498277
theorem B1898257 : Blo 786339 1898257 := bstep (se 2 (by rfl) ⟨711846, by rfl⟩ : syracuseStep 1898257 = 1423693) B1423693
theorem B2160557 : Blo 786339 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B1996721 : Blo 786339 1996721 := bstep (se 2 (by rfl) ⟨748770, by rfl⟩ : syracuseStep 1996721 = 1497541) B1497541
theorem B1996771 : Blo 786339 1996771 := bstep (se 1 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 1996771 = 2995157) B2995157
theorem B2127917 : Blo 786339 2127917 := bstep (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) B797969
theorem B1996913 : Blo 786339 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B2521219 : Blo 786339 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B1898641 : Blo 786339 1898641 := bstep (se 2 (by rfl) ⟨711990, by rfl⟩ : syracuseStep 1898641 = 1423981) B1423981
theorem B2521361 : Blo 786339 2521361 := bstep (se 2 (by rfl) ⟨945510, by rfl⟩ : syracuseStep 2521361 = 1891021) B1891021
theorem B2161037 : Blo 786339 2161037 := bstep (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) B810389
theorem B4487885 : Blo 786339 4487885 := bstep (se 3 (by rfl) ⟨841478, by rfl⟩ : syracuseStep 4487885 = 1682957) B1682957
theorem B1800913 : Blo 786339 1800913 := bstep (se 2 (by rfl) ⟨675342, by rfl⟩ : syracuseStep 1800913 = 1350685) B1350685
theorem B1801169 : Blo 786339 1801169 := bstep (se 2 (by rfl) ⟨675438, by rfl⟩ : syracuseStep 1801169 = 1350877) B1350877
theorem B1276897 : Blo 786339 1276897 := bstep (se 2 (by rfl) ⟨478836, by rfl⟩ : syracuseStep 1276897 = 957673) B957673
theorem B1997905 : Blo 786339 1997905 := bstep (se 2 (by rfl) ⟨749214, by rfl⟩ : syracuseStep 1997905 = 1498429) B1498429
theorem B1998179 : Blo 786339 1998179 := bstep (se 1 (by rfl) ⟨1498634, by rfl⟩ : syracuseStep 1998179 = 2997269) B2997269
theorem B6061553 : Blo 786339 6061553 := bstep (se 2 (by rfl) ⟨2273082, by rfl⟩ : syracuseStep 6061553 = 4546165) B4546165
theorem B1998371 : Blo 786339 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B2129507 : Blo 786339 2129507 := bstep (se 1 (by rfl) ⟨1597130, by rfl⟩ : syracuseStep 2129507 = 3194261) B3194261
theorem B4488817 : Blo 786339 4488817 := bstep (se 2 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 4488817 = 3366613) B3366613
theorem B2653937 : Blo 786339 2653937 := bstep (se 2 (by rfl) ⟨995226, by rfl⟩ : syracuseStep 2653937 = 1990453) B1990453
theorem B1179521 : Blo 786339 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B1179539 : Blo 786339 1179539 := bstep (se 1 (by rfl) ⟨884654, by rfl⟩ : syracuseStep 1179539 = 1769309) B1769309
theorem B786339 : Blo 786339 786339 := bstep (se 1 (by rfl) ⟨589754, by rfl⟩ : syracuseStep 786339 = 1179509) B1179509
theorem B1179569 : Blo 786339 1179569 := bstep (se 2 (by rfl) ⟨442338, by rfl⟩ : syracuseStep 1179569 = 884677) B884677
theorem B786355 : Blo 786339 786355 := bstep (se 1 (by rfl) ⟨589766, by rfl⟩ : syracuseStep 786355 = 1179533) B1179533
theorem B884659 : Blo 786339 884659 := bstep (se 1 (by rfl) ⟨663494, by rfl⟩ : syracuseStep 884659 = 1326989) B1326989
theorem B786371 : Blo 786339 786371 := bstep (se 1 (by rfl) ⟨589778, by rfl⟩ : syracuseStep 786371 = 1179557) B1179557
theorem B1179587 : Blo 786339 1179587 := bstep (se 1 (by rfl) ⟨884690, by rfl⟩ : syracuseStep 1179587 = 1769381) B1769381
theorem B786387 : Blo 786339 786387 := bstep (se 1 (by rfl) ⟨589790, by rfl⟩ : syracuseStep 786387 = 1179581) B1179581
theorem B1179617 : Blo 786339 1179617 := bstep (se 2 (by rfl) ⟨442356, by rfl⟩ : syracuseStep 1179617 = 884713) B884713
theorem B786403 : Blo 786339 786403 := bstep (se 1 (by rfl) ⟨589802, by rfl⟩ : syracuseStep 786403 = 1179605) B1179605
theorem B786419 : Blo 786339 786419 := bstep (se 1 (by rfl) ⟨589814, by rfl⟩ : syracuseStep 786419 = 1179629) B1179629
theorem B1179635 : Blo 786339 1179635 := bstep (se 1 (by rfl) ⟨884726, by rfl⟩ : syracuseStep 1179635 = 1769453) B1769453
theorem B1179659 : Blo 786339 1179659 := bstep (se 1 (by rfl) ⟨884744, by rfl⟩ : syracuseStep 1179659 = 1769489) B1769489
theorem B786443 : Blo 786339 786443 := bstep (se 1 (by rfl) ⟨589832, by rfl⟩ : syracuseStep 786443 = 1179665) B1179665
theorem B1179671 : Blo 786339 1179671 := bstep (se 1 (by rfl) ⟨884753, by rfl⟩ : syracuseStep 1179671 = 1769507) B1769507
theorem B786455 : Blo 786339 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B786475 : Blo 786339 786475 := bstep (se 1 (by rfl) ⟨589856, by rfl⟩ : syracuseStep 786475 = 1179713) B1179713
theorem B786487 : Blo 786339 786487 := bstep (se 1 (by rfl) ⟨589865, by rfl⟩ : syracuseStep 786487 = 1179731) B1179731
theorem B786507 : Blo 786339 786507 := bstep (se 1 (by rfl) ⟨589880, by rfl⟩ : syracuseStep 786507 = 1179761) B1179761
theorem B786519 : Blo 786339 786519 := bstep (se 1 (by rfl) ⟨589889, by rfl⟩ : syracuseStep 786519 = 1179779) B1179779
theorem B1769561 : Blo 786339 1769561 := bstep (se 2 (by rfl) ⟨663585, by rfl⟩ : syracuseStep 1769561 = 1327171) B1327171
theorem B1179737 : Blo 786339 1179737 := bstep (se 2 (by rfl) ⟨442401, by rfl⟩ : syracuseStep 1179737 = 884803) B884803
theorem B786539 : Blo 786339 786539 := bstep (se 1 (by rfl) ⟨589904, by rfl⟩ : syracuseStep 786539 = 1179809) B1179809
theorem B786551 : Blo 786339 786551 := bstep (se 1 (by rfl) ⟨589913, by rfl⟩ : syracuseStep 786551 = 1179827) B1179827
theorem B884875 : Blo 786339 884875 := bstep (se 1 (by rfl) ⟨663656, by rfl⟩ : syracuseStep 884875 = 1327313) B1327313
theorem B786571 : Blo 786339 786571 := bstep (se 1 (by rfl) ⟨589928, by rfl⟩ : syracuseStep 786571 = 1179857) B1179857
theorem B786583 : Blo 786339 786583 := bstep (se 1 (by rfl) ⟨589937, by rfl⟩ : syracuseStep 786583 = 1179875) B1179875
theorem B786603 : Blo 786339 786603 := bstep (se 1 (by rfl) ⟨589952, by rfl⟩ : syracuseStep 786603 = 1179905) B1179905
theorem B1769651 : Blo 786339 1769651 := bstep (se 1 (by rfl) ⟨1327238, by rfl⟩ : syracuseStep 1769651 = 2654477) B2654477
theorem B786615 : Blo 786339 786615 := bstep (se 1 (by rfl) ⟨589961, by rfl⟩ : syracuseStep 786615 = 1179923) B1179923
theorem B1179851 : Blo 786339 1179851 := bstep (se 1 (by rfl) ⟨884888, by rfl⟩ : syracuseStep 1179851 = 1769777) B1769777
theorem B786635 : Blo 786339 786635 := bstep (se 1 (by rfl) ⟨589976, by rfl⟩ : syracuseStep 786635 = 1179953) B1179953
theorem B1769687 : Blo 786339 1769687 := bstep (se 1 (by rfl) ⟨1327265, by rfl⟩ : syracuseStep 1769687 = 2654531) B2654531
theorem B1179863 : Blo 786339 1179863 := bstep (se 1 (by rfl) ⟨884897, by rfl⟩ : syracuseStep 1179863 = 1769795) B1769795
theorem B786647 : Blo 786339 786647 := bstep (se 1 (by rfl) ⟨589985, by rfl⟩ : syracuseStep 786647 = 1179971) B1179971
theorem B786667 : Blo 786339 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B884983 : Blo 786339 884983 := bstep (se 1 (by rfl) ⟨663737, by rfl⟩ : syracuseStep 884983 = 1327475) B1327475
theorem B786679 : Blo 786339 786679 := bstep (se 1 (by rfl) ⟨590009, by rfl⟩ : syracuseStep 786679 = 1180019) B1180019
theorem B786699 : Blo 786339 786699 := bstep (se 1 (by rfl) ⟨590024, by rfl⟩ : syracuseStep 786699 = 1180049) B1180049
theorem B786711 : Blo 786339 786711 := bstep (se 1 (by rfl) ⟨590033, by rfl⟩ : syracuseStep 786711 = 1180067) B1180067
theorem B1179929 : Blo 786339 1179929 := bstep (se 2 (by rfl) ⟨442473, by rfl⟩ : syracuseStep 1179929 = 884947) B884947
theorem B786731 : Blo 786339 786731 := bstep (se 1 (by rfl) ⟨590048, by rfl⟩ : syracuseStep 786731 = 1180097) B1180097
theorem B3997997 : Blo 786339 3997997 := bstep (se 3 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 3997997 = 1499249) B1499249
theorem B786743 : Blo 786339 786743 := bstep (se 1 (by rfl) ⟨590057, by rfl⟩ : syracuseStep 786743 = 1180115) B1180115
theorem B786763 : Blo 786339 786763 := bstep (se 1 (by rfl) ⟨590072, by rfl⟩ : syracuseStep 786763 = 1180145) B1180145
theorem B786775 : Blo 786339 786775 := bstep (se 1 (by rfl) ⟨590081, by rfl⟩ : syracuseStep 786775 = 1180163) B1180163
theorem B786795 : Blo 786339 786795 := bstep (se 1 (by rfl) ⟨590096, by rfl⟩ : syracuseStep 786795 = 1180193) B1180193
theorem B786807 : Blo 786339 786807 := bstep (se 1 (by rfl) ⟨590105, by rfl⟩ : syracuseStep 786807 = 1180211) B1180211
theorem B1769867 : Blo 786339 1769867 := bstep (se 1 (by rfl) ⟨1327400, by rfl⟩ : syracuseStep 1769867 = 2654801) B2654801
theorem B1180043 : Blo 786339 1180043 := bstep (se 1 (by rfl) ⟨885032, by rfl⟩ : syracuseStep 1180043 = 1770065) B1770065
theorem B786827 : Blo 786339 786827 := bstep (se 1 (by rfl) ⟨590120, by rfl⟩ : syracuseStep 786827 = 1180241) B1180241
theorem B1180055 : Blo 786339 1180055 := bstep (se 1 (by rfl) ⟨885041, by rfl⟩ : syracuseStep 1180055 = 1770083) B1770083
theorem B786839 : Blo 786339 786839 := bstep (se 1 (by rfl) ⟨590129, by rfl⟩ : syracuseStep 786839 = 1180259) B1180259
theorem B885163 : Blo 786339 885163 := bstep (se 1 (by rfl) ⟨663872, by rfl⟩ : syracuseStep 885163 = 1327745) B1327745
theorem B786859 : Blo 786339 786859 := bstep (se 1 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 786859 = 1180289) B1180289
theorem B3375533 : Blo 786339 3375533 := bstep (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) B1265825
theorem B786871 : Blo 786339 786871 := bstep (se 1 (by rfl) ⟨590153, by rfl⟩ : syracuseStep 786871 = 1180307) B1180307
theorem B1769921 : Blo 786339 1769921 := bstep (se 2 (by rfl) ⟨663720, by rfl⟩ : syracuseStep 1769921 = 1327441) B1327441
theorem B786891 : Blo 786339 786891 := bstep (se 1 (by rfl) ⟨590168, by rfl⟩ : syracuseStep 786891 = 1180337) B1180337
theorem B786903 : Blo 786339 786903 := bstep (se 1 (by rfl) ⟨590177, by rfl⟩ : syracuseStep 786903 = 1180355) B1180355
theorem B1180121 : Blo 786339 1180121 := bstep (se 2 (by rfl) ⟨442545, by rfl⟩ : syracuseStep 1180121 = 885091) B885091
theorem B786923 : Blo 786339 786923 := bstep (se 1 (by rfl) ⟨590192, by rfl⟩ : syracuseStep 786923 = 1180385) B1180385
theorem B786935 : Blo 786339 786935 := bstep (se 1 (by rfl) ⟨590201, by rfl⟩ : syracuseStep 786935 = 1180403) B1180403
theorem B786955 : Blo 786339 786955 := bstep (se 1 (by rfl) ⟨590216, by rfl⟩ : syracuseStep 786955 = 1180433) B1180433
theorem B885271 : Blo 786339 885271 := bstep (se 1 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 885271 = 1327907) B1327907
theorem B786967 : Blo 786339 786967 := bstep (se 1 (by rfl) ⟨590225, by rfl⟩ : syracuseStep 786967 = 1180451) B1180451
theorem B786987 : Blo 786339 786987 := bstep (se 1 (by rfl) ⟨590240, by rfl⟩ : syracuseStep 786987 = 1180481) B1180481
theorem B4260397 : Blo 786339 4260397 := bstep (se 3 (by rfl) ⟨798824, by rfl⟩ : syracuseStep 4260397 = 1597649) B1597649
theorem B786999 : Blo 786339 786999 := bstep (se 1 (by rfl) ⟨590249, by rfl⟩ : syracuseStep 786999 = 1180499) B1180499
theorem B1180235 : Blo 786339 1180235 := bstep (se 1 (by rfl) ⟨885176, by rfl⟩ : syracuseStep 1180235 = 1770353) B1770353
theorem B787019 : Blo 786339 787019 := bstep (se 1 (by rfl) ⟨590264, by rfl⟩ : syracuseStep 787019 = 1180529) B1180529
theorem B1180247 : Blo 786339 1180247 := bstep (se 1 (by rfl) ⟨885185, by rfl⟩ : syracuseStep 1180247 = 1770371) B1770371
theorem B787031 : Blo 786339 787031 := bstep (se 1 (by rfl) ⟨590273, by rfl⟩ : syracuseStep 787031 = 1180547) B1180547
theorem B787051 : Blo 786339 787051 := bstep (se 1 (by rfl) ⟨590288, by rfl⟩ : syracuseStep 787051 = 1180577) B1180577
theorem B787063 : Blo 786339 787063 := bstep (se 1 (by rfl) ⟨590297, by rfl⟩ : syracuseStep 787063 = 1180595) B1180595
theorem B787083 : Blo 786339 787083 := bstep (se 1 (by rfl) ⟨590312, by rfl⟩ : syracuseStep 787083 = 1180625) B1180625
theorem B787095 : Blo 786339 787095 := bstep (se 1 (by rfl) ⟨590321, by rfl⟩ : syracuseStep 787095 = 1180643) B1180643
theorem B1770137 : Blo 786339 1770137 := bstep (se 2 (by rfl) ⟨663801, by rfl⟩ : syracuseStep 1770137 = 1327603) B1327603
theorem B1180313 : Blo 786339 1180313 := bstep (se 2 (by rfl) ⟨442617, by rfl⟩ : syracuseStep 1180313 = 885235) B885235
theorem B787115 : Blo 786339 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B787127 : Blo 786339 787127 := bstep (se 1 (by rfl) ⟨590345, by rfl⟩ : syracuseStep 787127 = 1180691) B1180691
theorem B885451 : Blo 786339 885451 := bstep (se 1 (by rfl) ⟨664088, by rfl⟩ : syracuseStep 885451 = 1328177) B1328177
theorem B787147 : Blo 786339 787147 := bstep (se 1 (by rfl) ⟨590360, by rfl⟩ : syracuseStep 787147 = 1180721) B1180721
theorem B787159 : Blo 786339 787159 := bstep (se 1 (by rfl) ⟨590369, by rfl⟩ : syracuseStep 787159 = 1180739) B1180739
theorem B787179 : Blo 786339 787179 := bstep (se 1 (by rfl) ⟨590384, by rfl⟩ : syracuseStep 787179 = 1180769) B1180769
theorem B1770227 : Blo 786339 1770227 := bstep (se 1 (by rfl) ⟨1327670, by rfl⟩ : syracuseStep 1770227 = 2655341) B2655341
theorem B787191 : Blo 786339 787191 := bstep (se 1 (by rfl) ⟨590393, by rfl⟩ : syracuseStep 787191 = 1180787) B1180787
theorem B1180427 : Blo 786339 1180427 := bstep (se 1 (by rfl) ⟨885320, by rfl⟩ : syracuseStep 1180427 = 1770641) B1770641
theorem B787211 : Blo 786339 787211 := bstep (se 1 (by rfl) ⟨590408, by rfl⟩ : syracuseStep 787211 = 1180817) B1180817
theorem B1770263 : Blo 786339 1770263 := bstep (se 1 (by rfl) ⟨1327697, by rfl⟩ : syracuseStep 1770263 = 2655395) B2655395
theorem B1180439 : Blo 786339 1180439 := bstep (se 1 (by rfl) ⟨885329, by rfl⟩ : syracuseStep 1180439 = 1770659) B1770659
theorem B787223 : Blo 786339 787223 := bstep (se 1 (by rfl) ⟨590417, by rfl⟩ : syracuseStep 787223 = 1180835) B1180835
theorem B787243 : Blo 786339 787243 := bstep (se 1 (by rfl) ⟨590432, by rfl⟩ : syracuseStep 787243 = 1180865) B1180865
theorem B1999667 : Blo 786339 1999667 := bstep (se 1 (by rfl) ⟨1499750, by rfl⟩ : syracuseStep 1999667 = 2999501) B2999501
theorem B885559 : Blo 786339 885559 := bstep (se 1 (by rfl) ⟨664169, by rfl⟩ : syracuseStep 885559 = 1328339) B1328339
theorem B787255 : Blo 786339 787255 := bstep (se 1 (by rfl) ⟨590441, by rfl⟩ : syracuseStep 787255 = 1180883) B1180883
theorem B787275 : Blo 786339 787275 := bstep (se 1 (by rfl) ⟨590456, by rfl⟩ : syracuseStep 787275 = 1180913) B1180913
theorem B5473099 : Blo 786339 5473099 := bstep (se 1 (by rfl) ⟨4104824, by rfl⟩ : syracuseStep 5473099 = 8209649) B8209649
theorem B787287 : Blo 786339 787287 := bstep (se 1 (by rfl) ⟨590465, by rfl⟩ : syracuseStep 787287 = 1180931) B1180931
theorem B1180505 : Blo 786339 1180505 := bstep (se 2 (by rfl) ⟨442689, by rfl⟩ : syracuseStep 1180505 = 885379) B885379
theorem B787307 : Blo 786339 787307 := bstep (se 1 (by rfl) ⟨590480, by rfl⟩ : syracuseStep 787307 = 1180961) B1180961
theorem B787319 : Blo 786339 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B787339 : Blo 786339 787339 := bstep (se 1 (by rfl) ⟨590504, by rfl⟩ : syracuseStep 787339 = 1181009) B1181009
theorem B787351 : Blo 786339 787351 := bstep (se 1 (by rfl) ⟨590513, by rfl⟩ : syracuseStep 787351 = 1181027) B1181027
theorem B787371 : Blo 786339 787371 := bstep (se 1 (by rfl) ⟨590528, by rfl⟩ : syracuseStep 787371 = 1181057) B1181057
theorem B787383 : Blo 786339 787383 := bstep (se 1 (by rfl) ⟨590537, by rfl⟩ : syracuseStep 787383 = 1181075) B1181075
theorem B2655179 : Blo 786339 2655179 := bstep (se 1 (by rfl) ⟨1991384, by rfl⟩ : syracuseStep 2655179 = 3982769) B3982769
theorem B1770443 : Blo 786339 1770443 := bstep (se 1 (by rfl) ⟨1327832, by rfl⟩ : syracuseStep 1770443 = 2655665) B2655665
theorem B1180619 : Blo 786339 1180619 := bstep (se 1 (by rfl) ⟨885464, by rfl⟩ : syracuseStep 1180619 = 1770929) B1770929
theorem B787403 : Blo 786339 787403 := bstep (se 1 (by rfl) ⟨590552, by rfl⟩ : syracuseStep 787403 = 1181105) B1181105
theorem B1180631 : Blo 786339 1180631 := bstep (se 1 (by rfl) ⟨885473, by rfl⟩ : syracuseStep 1180631 = 1770947) B1770947
theorem B787415 : Blo 786339 787415 := bstep (se 1 (by rfl) ⟨590561, by rfl⟩ : syracuseStep 787415 = 1181123) B1181123
theorem B885739 : Blo 786339 885739 := bstep (se 1 (by rfl) ⟨664304, by rfl⟩ : syracuseStep 885739 = 1328609) B1328609
theorem B787435 : Blo 786339 787435 := bstep (se 1 (by rfl) ⟨590576, by rfl⟩ : syracuseStep 787435 = 1181153) B1181153
theorem B787447 : Blo 786339 787447 := bstep (se 1 (by rfl) ⟨590585, by rfl⟩ : syracuseStep 787447 = 1181171) B1181171
theorem B1770497 : Blo 786339 1770497 := bstep (se 2 (by rfl) ⟨663936, by rfl⟩ : syracuseStep 1770497 = 1327873) B1327873
theorem B787467 : Blo 786339 787467 := bstep (se 1 (by rfl) ⟨590600, by rfl⟩ : syracuseStep 787467 = 1181201) B1181201
theorem B787479 : Blo 786339 787479 := bstep (se 1 (by rfl) ⟨590609, by rfl⟩ : syracuseStep 787479 = 1181219) B1181219
theorem B1180697 : Blo 786339 1180697 := bstep (se 2 (by rfl) ⟨442761, by rfl⟩ : syracuseStep 1180697 = 885523) B885523
theorem B787499 : Blo 786339 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B787511 : Blo 786339 787511 := bstep (se 1 (by rfl) ⟨590633, by rfl⟩ : syracuseStep 787511 = 1181267) B1181267
theorem B787531 : Blo 786339 787531 := bstep (se 1 (by rfl) ⟨590648, by rfl⟩ : syracuseStep 787531 = 1181297) B1181297
theorem B885847 : Blo 786339 885847 := bstep (se 1 (by rfl) ⟨664385, by rfl⟩ : syracuseStep 885847 = 1328771) B1328771
theorem B787543 : Blo 786339 787543 := bstep (se 1 (by rfl) ⟨590657, by rfl⟩ : syracuseStep 787543 = 1181315) B1181315
theorem B1999961 : Blo 786339 1999961 := bstep (se 2 (by rfl) ⟨749985, by rfl⟩ : syracuseStep 1999961 = 1499971) B1499971
theorem B787563 : Blo 786339 787563 := bstep (se 1 (by rfl) ⟨590672, by rfl⟩ : syracuseStep 787563 = 1181345) B1181345
theorem B787575 : Blo 786339 787575 := bstep (se 1 (by rfl) ⟨590681, by rfl⟩ : syracuseStep 787575 = 1181363) B1181363
theorem B1180811 : Blo 786339 1180811 := bstep (se 1 (by rfl) ⟨885608, by rfl⟩ : syracuseStep 1180811 = 1771217) B1771217
theorem B787595 : Blo 786339 787595 := bstep (se 1 (by rfl) ⟨590696, by rfl⟩ : syracuseStep 787595 = 1181393) B1181393
theorem B1180823 : Blo 786339 1180823 := bstep (se 1 (by rfl) ⟨885617, by rfl⟩ : syracuseStep 1180823 = 1771235) B1771235
theorem B787607 : Blo 786339 787607 := bstep (se 1 (by rfl) ⟨590705, by rfl⟩ : syracuseStep 787607 = 1181411) B1181411
theorem B787627 : Blo 786339 787627 := bstep (se 1 (by rfl) ⟨590720, by rfl⟩ : syracuseStep 787627 = 1181441) B1181441
theorem B787639 : Blo 786339 787639 := bstep (se 1 (by rfl) ⟨590729, by rfl⟩ : syracuseStep 787639 = 1181459) B1181459
theorem B787659 : Blo 786339 787659 := bstep (se 1 (by rfl) ⟨590744, by rfl⟩ : syracuseStep 787659 = 1181489) B1181489
theorem B787671 : Blo 786339 787671 := bstep (se 1 (by rfl) ⟨590753, by rfl⟩ : syracuseStep 787671 = 1181507) B1181507
theorem B2655449 : Blo 786339 2655449 := bstep (se 2 (by rfl) ⟨995793, by rfl⟩ : syracuseStep 2655449 = 1991587) B1991587
theorem B1770713 : Blo 786339 1770713 := bstep (se 2 (by rfl) ⟨664017, by rfl⟩ : syracuseStep 1770713 = 1328035) B1328035
theorem B1180889 : Blo 786339 1180889 := bstep (se 2 (by rfl) ⟨442833, by rfl⟩ : syracuseStep 1180889 = 885667) B885667
theorem B787691 : Blo 786339 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B787703 : Blo 786339 787703 := bstep (se 1 (by rfl) ⟨590777, by rfl⟩ : syracuseStep 787703 = 1181555) B1181555
theorem B886027 : Blo 786339 886027 := bstep (se 1 (by rfl) ⟨664520, by rfl⟩ : syracuseStep 886027 = 1329041) B1329041
theorem B787723 : Blo 786339 787723 := bstep (se 1 (by rfl) ⟨590792, by rfl⟩ : syracuseStep 787723 = 1181585) B1181585
theorem B787735 : Blo 786339 787735 := bstep (se 1 (by rfl) ⟨590801, by rfl⟩ : syracuseStep 787735 = 1181603) B1181603
theorem B787755 : Blo 786339 787755 := bstep (se 1 (by rfl) ⟨590816, by rfl⟩ : syracuseStep 787755 = 1181633) B1181633
theorem B1770803 : Blo 786339 1770803 := bstep (se 1 (by rfl) ⟨1328102, by rfl⟩ : syracuseStep 1770803 = 2656205) B2656205
theorem B787767 : Blo 786339 787767 := bstep (se 1 (by rfl) ⟨590825, by rfl⟩ : syracuseStep 787767 = 1181651) B1181651
theorem B1181003 : Blo 786339 1181003 := bstep (se 1 (by rfl) ⟨885752, by rfl⟩ : syracuseStep 1181003 = 1771505) B1771505
theorem B787787 : Blo 786339 787787 := bstep (se 1 (by rfl) ⟨590840, by rfl⟩ : syracuseStep 787787 = 1181681) B1181681
theorem B1770839 : Blo 786339 1770839 := bstep (se 1 (by rfl) ⟨1328129, by rfl⟩ : syracuseStep 1770839 = 2656259) B2656259
theorem B1181015 : Blo 786339 1181015 := bstep (se 1 (by rfl) ⟨885761, by rfl⟩ : syracuseStep 1181015 = 1771523) B1771523
theorem B787799 : Blo 786339 787799 := bstep (se 1 (by rfl) ⟨590849, by rfl⟩ : syracuseStep 787799 = 1181699) B1181699
theorem B787819 : Blo 786339 787819 := bstep (se 1 (by rfl) ⟨590864, by rfl⟩ : syracuseStep 787819 = 1181729) B1181729
theorem B886135 : Blo 786339 886135 := bstep (se 1 (by rfl) ⟨664601, by rfl⟩ : syracuseStep 886135 = 1329203) B1329203
theorem B787831 : Blo 786339 787831 := bstep (se 1 (by rfl) ⟨590873, by rfl⟩ : syracuseStep 787831 = 1181747) B1181747
theorem B787851 : Blo 786339 787851 := bstep (se 1 (by rfl) ⟨590888, by rfl⟩ : syracuseStep 787851 = 1181777) B1181777
theorem B787863 : Blo 786339 787863 := bstep (se 1 (by rfl) ⟨590897, by rfl⟩ : syracuseStep 787863 = 1181795) B1181795
theorem B2000279 : Blo 786339 2000279 := bstep (se 1 (by rfl) ⟨1500209, by rfl⟩ : syracuseStep 2000279 = 3000419) B3000419
theorem B1181081 : Blo 786339 1181081 := bstep (se 2 (by rfl) ⟨442905, by rfl⟩ : syracuseStep 1181081 = 885811) B885811
theorem B787883 : Blo 786339 787883 := bstep (se 1 (by rfl) ⟨590912, by rfl⟩ : syracuseStep 787883 = 1181825) B1181825
theorem B5670323 : Blo 786339 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B787895 : Blo 786339 787895 := bstep (se 1 (by rfl) ⟨590921, by rfl⟩ : syracuseStep 787895 = 1181843) B1181843
theorem B787915 : Blo 786339 787915 := bstep (se 1 (by rfl) ⟨590936, by rfl⟩ : syracuseStep 787915 = 1181873) B1181873
theorem B787927 : Blo 786339 787927 := bstep (se 1 (by rfl) ⟨590945, by rfl⟩ : syracuseStep 787927 = 1181891) B1181891
theorem B787947 : Blo 786339 787947 := bstep (se 1 (by rfl) ⟨590960, by rfl⟩ : syracuseStep 787947 = 1181921) B1181921
theorem B787959 : Blo 786339 787959 := bstep (se 1 (by rfl) ⟨590969, by rfl⟩ : syracuseStep 787959 = 1181939) B1181939
theorem B1771019 : Blo 786339 1771019 := bstep (se 1 (by rfl) ⟨1328264, by rfl⟩ : syracuseStep 1771019 = 2656529) B2656529
theorem B1181195 : Blo 786339 1181195 := bstep (se 1 (by rfl) ⟨885896, by rfl⟩ : syracuseStep 1181195 = 1771793) B1771793
theorem B787979 : Blo 786339 787979 := bstep (se 1 (by rfl) ⟨590984, by rfl⟩ : syracuseStep 787979 = 1181969) B1181969
theorem B1181207 : Blo 786339 1181207 := bstep (se 1 (by rfl) ⟨885905, by rfl⟩ : syracuseStep 1181207 = 1771811) B1771811
theorem B787991 : Blo 786339 787991 := bstep (se 1 (by rfl) ⟨590993, by rfl⟩ : syracuseStep 787991 = 1181987) B1181987
theorem B886315 : Blo 786339 886315 := bstep (se 1 (by rfl) ⟨664736, by rfl⟩ : syracuseStep 886315 = 1329473) B1329473
theorem B788011 : Blo 786339 788011 := bstep (se 1 (by rfl) ⟨591008, by rfl⟩ : syracuseStep 788011 = 1182017) B1182017
theorem B788023 : Blo 786339 788023 := bstep (se 1 (by rfl) ⟨591017, by rfl⟩ : syracuseStep 788023 = 1182035) B1182035
theorem B1771073 : Blo 786339 1771073 := bstep (se 2 (by rfl) ⟨664152, by rfl⟩ : syracuseStep 1771073 = 1328305) B1328305
theorem B788043 : Blo 786339 788043 := bstep (se 1 (by rfl) ⟨591032, by rfl⟩ : syracuseStep 788043 = 1182065) B1182065
theorem B1181273 : Blo 786339 1181273 := bstep (se 2 (by rfl) ⟨442977, by rfl⟩ : syracuseStep 1181273 = 885955) B885955
theorem B788055 : Blo 786339 788055 := bstep (se 1 (by rfl) ⟨591041, by rfl⟩ : syracuseStep 788055 = 1182083) B1182083
theorem B788075 : Blo 786339 788075 := bstep (se 1 (by rfl) ⟨591056, by rfl⟩ : syracuseStep 788075 = 1182113) B1182113
theorem B788087 : Blo 786339 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B5998211 : Blo 786339 5998211 := bstep (se 1 (by rfl) ⟨4498658, by rfl⟩ : syracuseStep 5998211 = 8997317) B8997317
theorem B788107 : Blo 786339 788107 := bstep (se 1 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 788107 = 1182161) B1182161
theorem B886423 : Blo 786339 886423 := bstep (se 1 (by rfl) ⟨664817, by rfl⟩ : syracuseStep 886423 = 1329635) B1329635
theorem B788119 : Blo 786339 788119 := bstep (se 1 (by rfl) ⟨591089, by rfl⟩ : syracuseStep 788119 = 1182179) B1182179
theorem B788139 : Blo 786339 788139 := bstep (se 1 (by rfl) ⟨591104, by rfl⟩ : syracuseStep 788139 = 1182209) B1182209
theorem B788151 : Blo 786339 788151 := bstep (se 1 (by rfl) ⟨591113, by rfl⟩ : syracuseStep 788151 = 1182227) B1182227
theorem B1181387 : Blo 786339 1181387 := bstep (se 1 (by rfl) ⟨886040, by rfl⟩ : syracuseStep 1181387 = 1772081) B1772081
theorem B788171 : Blo 786339 788171 := bstep (se 1 (by rfl) ⟨591128, by rfl⟩ : syracuseStep 788171 = 1182257) B1182257
theorem B24643277 : Blo 786339 24643277 := bstep (se 3 (by rfl) ⟨4620614, by rfl⟩ : syracuseStep 24643277 = 9241229) B9241229
theorem B1181399 : Blo 786339 1181399 := bstep (se 1 (by rfl) ⟨886049, by rfl⟩ : syracuseStep 1181399 = 1772099) B1772099
theorem B788183 : Blo 786339 788183 := bstep (se 1 (by rfl) ⟨591137, by rfl⟩ : syracuseStep 788183 = 1182275) B1182275
theorem B788203 : Blo 786339 788203 := bstep (se 1 (by rfl) ⟨591152, by rfl⟩ : syracuseStep 788203 = 1182305) B1182305
theorem B788215 : Blo 786339 788215 := bstep (se 1 (by rfl) ⟨591161, by rfl⟩ : syracuseStep 788215 = 1182323) B1182323
theorem B788235 : Blo 786339 788235 := bstep (se 1 (by rfl) ⟨591176, by rfl⟩ : syracuseStep 788235 = 1182353) B1182353
theorem B788247 : Blo 786339 788247 := bstep (se 1 (by rfl) ⟨591185, by rfl⟩ : syracuseStep 788247 = 1182371) B1182371
theorem B1771289 : Blo 786339 1771289 := bstep (se 2 (by rfl) ⟨664233, by rfl⟩ : syracuseStep 1771289 = 1328467) B1328467
theorem B1181465 : Blo 786339 1181465 := bstep (se 2 (by rfl) ⟨443049, by rfl⟩ : syracuseStep 1181465 = 886099) B886099
theorem B788267 : Blo 786339 788267 := bstep (se 1 (by rfl) ⟨591200, by rfl⟩ : syracuseStep 788267 = 1182401) B1182401
theorem B788279 : Blo 786339 788279 := bstep (se 1 (by rfl) ⟨591209, by rfl⟩ : syracuseStep 788279 = 1182419) B1182419
theorem B886603 : Blo 786339 886603 := bstep (se 1 (by rfl) ⟨664952, by rfl⟩ : syracuseStep 886603 = 1329905) B1329905
theorem B788299 : Blo 786339 788299 := bstep (se 1 (by rfl) ⟨591224, by rfl⟩ : syracuseStep 788299 = 1182449) B1182449
theorem B788311 : Blo 786339 788311 := bstep (se 1 (by rfl) ⟨591233, by rfl⟩ : syracuseStep 788311 = 1182467) B1182467
theorem B788331 : Blo 786339 788331 := bstep (se 1 (by rfl) ⟨591248, by rfl⟩ : syracuseStep 788331 = 1182497) B1182497
theorem B1771379 : Blo 786339 1771379 := bstep (se 1 (by rfl) ⟨1328534, by rfl⟩ : syracuseStep 1771379 = 2657069) B2657069
theorem B788343 : Blo 786339 788343 := bstep (se 1 (by rfl) ⟨591257, by rfl⟩ : syracuseStep 788343 = 1182515) B1182515
theorem B1181579 : Blo 786339 1181579 := bstep (se 1 (by rfl) ⟨886184, by rfl⟩ : syracuseStep 1181579 = 1772369) B1772369
theorem B788363 : Blo 786339 788363 := bstep (se 1 (by rfl) ⟨591272, by rfl⟩ : syracuseStep 788363 = 1182545) B1182545
theorem B2656151 : Blo 786339 2656151 := bstep (se 1 (by rfl) ⟨1992113, by rfl⟩ : syracuseStep 2656151 = 3984227) B3984227
theorem B1771415 : Blo 786339 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B1181591 : Blo 786339 1181591 := bstep (se 1 (by rfl) ⟨886193, by rfl⟩ : syracuseStep 1181591 = 1772387) B1772387
theorem B788375 : Blo 786339 788375 := bstep (se 1 (by rfl) ⟨591281, by rfl⟩ : syracuseStep 788375 = 1182563) B1182563
theorem B788395 : Blo 786339 788395 := bstep (se 1 (by rfl) ⟨591296, by rfl⟩ : syracuseStep 788395 = 1182593) B1182593
theorem B886711 : Blo 786339 886711 := bstep (se 1 (by rfl) ⟨665033, by rfl⟩ : syracuseStep 886711 = 1330067) B1330067
theorem B788407 : Blo 786339 788407 := bstep (se 1 (by rfl) ⟨591305, by rfl⟩ : syracuseStep 788407 = 1182611) B1182611
theorem B788427 : Blo 786339 788427 := bstep (se 1 (by rfl) ⟨591320, by rfl⟩ : syracuseStep 788427 = 1182641) B1182641
theorem B788439 : Blo 786339 788439 := bstep (se 1 (by rfl) ⟨591329, by rfl⟩ : syracuseStep 788439 = 1182659) B1182659
theorem B1181657 : Blo 786339 1181657 := bstep (se 2 (by rfl) ⟨443121, by rfl⟩ : syracuseStep 1181657 = 886243) B886243
theorem B788459 : Blo 786339 788459 := bstep (se 1 (by rfl) ⟨591344, by rfl⟩ : syracuseStep 788459 = 1182689) B1182689
theorem B788471 : Blo 786339 788471 := bstep (se 1 (by rfl) ⟨591353, by rfl⟩ : syracuseStep 788471 = 1182707) B1182707
theorem B788491 : Blo 786339 788491 := bstep (se 1 (by rfl) ⟨591368, by rfl⟩ : syracuseStep 788491 = 1182737) B1182737
theorem B788503 : Blo 786339 788503 := bstep (se 1 (by rfl) ⟨591377, by rfl⟩ : syracuseStep 788503 = 1182755) B1182755
theorem B788523 : Blo 786339 788523 := bstep (se 1 (by rfl) ⟨591392, by rfl⟩ : syracuseStep 788523 = 1182785) B1182785
theorem B788535 : Blo 786339 788535 := bstep (se 1 (by rfl) ⟨591401, by rfl⟩ : syracuseStep 788535 = 1182803) B1182803
theorem B1771595 : Blo 786339 1771595 := bstep (se 1 (by rfl) ⟨1328696, by rfl⟩ : syracuseStep 1771595 = 2657393) B2657393
theorem B1181771 : Blo 786339 1181771 := bstep (se 1 (by rfl) ⟨886328, by rfl⟩ : syracuseStep 1181771 = 1772657) B1772657
theorem B788555 : Blo 786339 788555 := bstep (se 1 (by rfl) ⟨591416, by rfl⟩ : syracuseStep 788555 = 1182833) B1182833
theorem B1181783 : Blo 786339 1181783 := bstep (se 1 (by rfl) ⟨886337, by rfl⟩ : syracuseStep 1181783 = 1772675) B1772675
theorem B788567 : Blo 786339 788567 := bstep (se 1 (by rfl) ⟨591425, by rfl⟩ : syracuseStep 788567 = 1182851) B1182851
theorem B886891 : Blo 786339 886891 := bstep (se 1 (by rfl) ⟨665168, by rfl⟩ : syracuseStep 886891 = 1330337) B1330337
theorem B788587 : Blo 786339 788587 := bstep (se 1 (by rfl) ⟨591440, by rfl⟩ : syracuseStep 788587 = 1182881) B1182881
theorem B788599 : Blo 786339 788599 := bstep (se 1 (by rfl) ⟨591449, by rfl⟩ : syracuseStep 788599 = 1182899) B1182899
theorem B1771649 : Blo 786339 1771649 := bstep (se 2 (by rfl) ⟨664368, by rfl⟩ : syracuseStep 1771649 = 1328737) B1328737
theorem B788619 : Blo 786339 788619 := bstep (se 1 (by rfl) ⟨591464, by rfl⟩ : syracuseStep 788619 = 1182929) B1182929
theorem B788631 : Blo 786339 788631 := bstep (se 1 (by rfl) ⟨591473, by rfl⟩ : syracuseStep 788631 = 1182947) B1182947
theorem B1181849 : Blo 786339 1181849 := bstep (se 2 (by rfl) ⟨443193, by rfl⟩ : syracuseStep 1181849 = 886387) B886387
theorem B788651 : Blo 786339 788651 := bstep (se 1 (by rfl) ⟨591488, by rfl⟩ : syracuseStep 788651 = 1182977) B1182977
theorem B788663 : Blo 786339 788663 := bstep (se 1 (by rfl) ⟨591497, by rfl⟩ : syracuseStep 788663 = 1182995) B1182995
theorem B788683 : Blo 786339 788683 := bstep (se 1 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 788683 = 1183025) B1183025
theorem B886999 : Blo 786339 886999 := bstep (se 1 (by rfl) ⟨665249, by rfl⟩ : syracuseStep 886999 = 1330499) B1330499
theorem B788695 : Blo 786339 788695 := bstep (se 1 (by rfl) ⟨591521, by rfl⟩ : syracuseStep 788695 = 1183043) B1183043
theorem B788715 : Blo 786339 788715 := bstep (se 1 (by rfl) ⟨591536, by rfl⟩ : syracuseStep 788715 = 1183073) B1183073
theorem B788727 : Blo 786339 788727 := bstep (se 1 (by rfl) ⟨591545, by rfl⟩ : syracuseStep 788727 = 1183091) B1183091
theorem B1181963 : Blo 786339 1181963 := bstep (se 1 (by rfl) ⟨886472, by rfl⟩ : syracuseStep 1181963 = 1772945) B1772945
theorem B788747 : Blo 786339 788747 := bstep (se 1 (by rfl) ⟨591560, by rfl⟩ : syracuseStep 788747 = 1183121) B1183121
theorem B1181975 : Blo 786339 1181975 := bstep (se 1 (by rfl) ⟨886481, by rfl⟩ : syracuseStep 1181975 = 1772963) B1772963
theorem B788759 : Blo 786339 788759 := bstep (se 1 (by rfl) ⟨591569, by rfl⟩ : syracuseStep 788759 = 1183139) B1183139
theorem B788779 : Blo 786339 788779 := bstep (se 1 (by rfl) ⟨591584, by rfl⟩ : syracuseStep 788779 = 1183169) B1183169
theorem B788791 : Blo 786339 788791 := bstep (se 1 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 788791 = 1183187) B1183187
theorem B788811 : Blo 786339 788811 := bstep (se 1 (by rfl) ⟨591608, by rfl⟩ : syracuseStep 788811 = 1183217) B1183217
theorem B788823 : Blo 786339 788823 := bstep (se 1 (by rfl) ⟨591617, by rfl⟩ : syracuseStep 788823 = 1183235) B1183235
theorem B1771865 : Blo 786339 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B1182041 : Blo 786339 1182041 := bstep (se 2 (by rfl) ⟨443265, by rfl⟩ : syracuseStep 1182041 = 886531) B886531
theorem B788843 : Blo 786339 788843 := bstep (se 1 (by rfl) ⟨591632, by rfl⟩ : syracuseStep 788843 = 1183265) B1183265
theorem B788855 : Blo 786339 788855 := bstep (se 1 (by rfl) ⟨591641, by rfl⟩ : syracuseStep 788855 = 1183283) B1183283
theorem B887179 : Blo 786339 887179 := bstep (se 1 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 887179 = 1330769) B1330769
theorem B788875 : Blo 786339 788875 := bstep (se 1 (by rfl) ⟨591656, by rfl⟩ : syracuseStep 788875 = 1183313) B1183313
theorem B788887 : Blo 786339 788887 := bstep (se 1 (by rfl) ⟨591665, by rfl⟩ : syracuseStep 788887 = 1183331) B1183331
theorem B788907 : Blo 786339 788907 := bstep (se 1 (by rfl) ⟨591680, by rfl⟩ : syracuseStep 788907 = 1183361) B1183361
theorem B2656691 : Blo 786339 2656691 := bstep (se 1 (by rfl) ⟨1992518, by rfl⟩ : syracuseStep 2656691 = 3985037) B3985037
theorem B1771955 : Blo 786339 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B788919 : Blo 786339 788919 := bstep (se 1 (by rfl) ⟨591689, by rfl⟩ : syracuseStep 788919 = 1183379) B1183379
theorem B1182155 : Blo 786339 1182155 := bstep (se 1 (by rfl) ⟨886616, by rfl⟩ : syracuseStep 1182155 = 1773233) B1773233
theorem B788939 : Blo 786339 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B1771991 : Blo 786339 1771991 := bstep (se 1 (by rfl) ⟨1328993, by rfl⟩ : syracuseStep 1771991 = 2657987) B2657987
theorem B1182167 : Blo 786339 1182167 := bstep (se 1 (by rfl) ⟨886625, by rfl⟩ : syracuseStep 1182167 = 1773251) B1773251
theorem B788951 : Blo 786339 788951 := bstep (se 1 (by rfl) ⟨591713, by rfl⟩ : syracuseStep 788951 = 1183427) B1183427
theorem B788971 : Blo 786339 788971 := bstep (se 1 (by rfl) ⟨591728, by rfl⟩ : syracuseStep 788971 = 1183457) B1183457
theorem B887287 : Blo 786339 887287 := bstep (se 1 (by rfl) ⟨665465, by rfl⟩ : syracuseStep 887287 = 1330931) B1330931
theorem B788983 : Blo 786339 788983 := bstep (se 1 (by rfl) ⟨591737, by rfl⟩ : syracuseStep 788983 = 1183475) B1183475
theorem B789003 : Blo 786339 789003 := bstep (se 1 (by rfl) ⟨591752, by rfl⟩ : syracuseStep 789003 = 1183505) B1183505
theorem B789015 : Blo 786339 789015 := bstep (se 1 (by rfl) ⟨591761, by rfl⟩ : syracuseStep 789015 = 1183523) B1183523
theorem B1182233 : Blo 786339 1182233 := bstep (se 2 (by rfl) ⟨443337, by rfl⟩ : syracuseStep 1182233 = 886675) B886675
theorem B789035 : Blo 786339 789035 := bstep (se 1 (by rfl) ⟨591776, by rfl⟩ : syracuseStep 789035 = 1183553) B1183553
theorem B789047 : Blo 786339 789047 := bstep (se 1 (by rfl) ⟨591785, by rfl⟩ : syracuseStep 789047 = 1183571) B1183571
theorem B789067 : Blo 786339 789067 := bstep (se 1 (by rfl) ⟨591800, by rfl⟩ : syracuseStep 789067 = 1183601) B1183601
theorem B789079 : Blo 786339 789079 := bstep (se 1 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 789079 = 1183619) B1183619
theorem B789099 : Blo 786339 789099 := bstep (se 1 (by rfl) ⟨591824, by rfl⟩ : syracuseStep 789099 = 1183649) B1183649
theorem B789111 : Blo 786339 789111 := bstep (se 1 (by rfl) ⟨591833, by rfl⟩ : syracuseStep 789111 = 1183667) B1183667
theorem B10783363 : Blo 786339 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1772171 : Blo 786339 1772171 := bstep (se 1 (by rfl) ⟨1329128, by rfl⟩ : syracuseStep 1772171 = 2658257) B2658257
theorem B1182347 : Blo 786339 1182347 := bstep (se 1 (by rfl) ⟨886760, by rfl⟩ : syracuseStep 1182347 = 1773521) B1773521
theorem B789131 : Blo 786339 789131 := bstep (se 1 (by rfl) ⟨591848, by rfl⟩ : syracuseStep 789131 = 1183697) B1183697
theorem B1182359 : Blo 786339 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B789143 : Blo 786339 789143 := bstep (se 1 (by rfl) ⟨591857, by rfl⟩ : syracuseStep 789143 = 1183715) B1183715
theorem B887467 : Blo 786339 887467 := bstep (se 1 (by rfl) ⟨665600, by rfl⟩ : syracuseStep 887467 = 1331201) B1331201
theorem B789163 : Blo 786339 789163 := bstep (se 1 (by rfl) ⟨591872, by rfl⟩ : syracuseStep 789163 = 1183745) B1183745
theorem B789175 : Blo 786339 789175 := bstep (se 1 (by rfl) ⟨591881, by rfl⟩ : syracuseStep 789175 = 1183763) B1183763
theorem B2656961 : Blo 786339 2656961 := bstep (se 2 (by rfl) ⟨996360, by rfl⟩ : syracuseStep 2656961 = 1992721) B1992721
theorem B1772225 : Blo 786339 1772225 := bstep (se 2 (by rfl) ⟨664584, by rfl⟩ : syracuseStep 1772225 = 1329169) B1329169
theorem B789195 : Blo 786339 789195 := bstep (se 1 (by rfl) ⟨591896, by rfl⟩ : syracuseStep 789195 = 1183793) B1183793
theorem B789207 : Blo 786339 789207 := bstep (se 1 (by rfl) ⟨591905, by rfl⟩ : syracuseStep 789207 = 1183811) B1183811
theorem B1182425 : Blo 786339 1182425 := bstep (se 2 (by rfl) ⟨443409, by rfl⟩ : syracuseStep 1182425 = 886819) B886819
theorem B789227 : Blo 786339 789227 := bstep (se 1 (by rfl) ⟨591920, by rfl⟩ : syracuseStep 789227 = 1183841) B1183841
theorem B789239 : Blo 786339 789239 := bstep (se 1 (by rfl) ⟨591929, by rfl⟩ : syracuseStep 789239 = 1183859) B1183859
theorem B789259 : Blo 786339 789259 := bstep (se 1 (by rfl) ⟨591944, by rfl⟩ : syracuseStep 789259 = 1183889) B1183889
theorem B2525975 : Blo 786339 2525975 := bstep (se 1 (by rfl) ⟨1894481, by rfl⟩ : syracuseStep 2525975 = 3788963) B3788963
theorem B887575 : Blo 786339 887575 := bstep (se 1 (by rfl) ⟨665681, by rfl⟩ : syracuseStep 887575 = 1331363) B1331363
theorem B789271 : Blo 786339 789271 := bstep (se 1 (by rfl) ⟨591953, by rfl⟩ : syracuseStep 789271 = 1183907) B1183907
theorem B789291 : Blo 786339 789291 := bstep (se 1 (by rfl) ⟨591968, by rfl⟩ : syracuseStep 789291 = 1183937) B1183937
theorem B789303 : Blo 786339 789303 := bstep (se 1 (by rfl) ⟨591977, by rfl⟩ : syracuseStep 789303 = 1183955) B1183955
theorem B11209537 : Blo 786339 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B40897345 : Blo 786339 40897345 := bstep (se 2 (by rfl) ⟨15336504, by rfl⟩ : syracuseStep 40897345 = 30673009) B30673009
theorem B1182539 : Blo 786339 1182539 := bstep (se 1 (by rfl) ⟨886904, by rfl⟩ : syracuseStep 1182539 = 1773809) B1773809
theorem B789323 : Blo 786339 789323 := bstep (se 1 (by rfl) ⟨591992, by rfl⟩ : syracuseStep 789323 = 1183985) B1183985
theorem B1182551 : Blo 786339 1182551 := bstep (se 1 (by rfl) ⟨886913, by rfl⟩ : syracuseStep 1182551 = 1773827) B1773827
theorem B789335 : Blo 786339 789335 := bstep (se 1 (by rfl) ⟨592001, by rfl⟩ : syracuseStep 789335 = 1184003) B1184003
theorem B789355 : Blo 786339 789355 := bstep (se 1 (by rfl) ⟨592016, by rfl⟩ : syracuseStep 789355 = 1184033) B1184033
theorem B789367 : Blo 786339 789367 := bstep (se 1 (by rfl) ⟨592025, by rfl⟩ : syracuseStep 789367 = 1184051) B1184051
theorem B789387 : Blo 786339 789387 := bstep (se 1 (by rfl) ⟨592040, by rfl⟩ : syracuseStep 789387 = 1184081) B1184081
theorem B789399 : Blo 786339 789399 := bstep (se 1 (by rfl) ⟨592049, by rfl⟩ : syracuseStep 789399 = 1184099) B1184099
theorem B1772441 : Blo 786339 1772441 := bstep (se 2 (by rfl) ⟨664665, by rfl⟩ : syracuseStep 1772441 = 1329331) B1329331
theorem B1182617 : Blo 786339 1182617 := bstep (se 2 (by rfl) ⟨443481, by rfl⟩ : syracuseStep 1182617 = 886963) B886963
theorem B789419 : Blo 786339 789419 := bstep (se 1 (by rfl) ⟨592064, by rfl⟩ : syracuseStep 789419 = 1184129) B1184129
theorem B789431 : Blo 786339 789431 := bstep (se 1 (by rfl) ⟨592073, by rfl⟩ : syracuseStep 789431 = 1184147) B1184147
theorem B887755 : Blo 786339 887755 := bstep (se 1 (by rfl) ⟨665816, by rfl⟩ : syracuseStep 887755 = 1331633) B1331633
theorem B789451 : Blo 786339 789451 := bstep (se 1 (by rfl) ⟨592088, by rfl⟩ : syracuseStep 789451 = 1184177) B1184177
theorem B789463 : Blo 786339 789463 := bstep (se 1 (by rfl) ⟨592097, by rfl⟩ : syracuseStep 789463 = 1184195) B1184195
theorem B789483 : Blo 786339 789483 := bstep (se 1 (by rfl) ⟨592112, by rfl⟩ : syracuseStep 789483 = 1184225) B1184225
theorem B1772531 : Blo 786339 1772531 := bstep (se 1 (by rfl) ⟨1329398, by rfl⟩ : syracuseStep 1772531 = 2658797) B2658797
theorem B789495 : Blo 786339 789495 := bstep (se 1 (by rfl) ⟨592121, by rfl⟩ : syracuseStep 789495 = 1184243) B1184243
theorem B1182731 : Blo 786339 1182731 := bstep (se 1 (by rfl) ⟨887048, by rfl⟩ : syracuseStep 1182731 = 1774097) B1774097
theorem B789515 : Blo 786339 789515 := bstep (se 1 (by rfl) ⟨592136, by rfl⟩ : syracuseStep 789515 = 1184273) B1184273
theorem B1772567 : Blo 786339 1772567 := bstep (se 1 (by rfl) ⟨1329425, by rfl⟩ : syracuseStep 1772567 = 2658851) B2658851
theorem B1182743 : Blo 786339 1182743 := bstep (se 1 (by rfl) ⟨887057, by rfl⟩ : syracuseStep 1182743 = 1774115) B1774115
theorem B789527 : Blo 786339 789527 := bstep (se 1 (by rfl) ⟨592145, by rfl⟩ : syracuseStep 789527 = 1184291) B1184291
theorem B789547 : Blo 786339 789547 := bstep (se 1 (by rfl) ⟨592160, by rfl⟩ : syracuseStep 789547 = 1184321) B1184321
theorem B887863 : Blo 786339 887863 := bstep (se 1 (by rfl) ⟨665897, by rfl⟩ : syracuseStep 887863 = 1331795) B1331795
theorem B789559 : Blo 786339 789559 := bstep (se 1 (by rfl) ⟨592169, by rfl⟩ : syracuseStep 789559 = 1184339) B1184339
theorem B789579 : Blo 786339 789579 := bstep (se 1 (by rfl) ⟨592184, by rfl⟩ : syracuseStep 789579 = 1184369) B1184369
theorem B789591 : Blo 786339 789591 := bstep (se 1 (by rfl) ⟨592193, by rfl⟩ : syracuseStep 789591 = 1184387) B1184387
theorem B1182809 : Blo 786339 1182809 := bstep (se 2 (by rfl) ⟨443553, by rfl⟩ : syracuseStep 1182809 = 887107) B887107
theorem B789611 : Blo 786339 789611 := bstep (se 1 (by rfl) ⟨592208, by rfl⟩ : syracuseStep 789611 = 1184417) B1184417
theorem B789623 : Blo 786339 789623 := bstep (se 1 (by rfl) ⟨592217, by rfl⟩ : syracuseStep 789623 = 1184435) B1184435
theorem B789643 : Blo 786339 789643 := bstep (se 1 (by rfl) ⟨592232, by rfl⟩ : syracuseStep 789643 = 1184465) B1184465
theorem B789655 : Blo 786339 789655 := bstep (se 1 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 789655 = 1184483) B1184483
theorem B789675 : Blo 786339 789675 := bstep (se 1 (by rfl) ⟨592256, by rfl⟩ : syracuseStep 789675 = 1184513) B1184513
theorem B789687 : Blo 786339 789687 := bstep (se 1 (by rfl) ⟨592265, by rfl⟩ : syracuseStep 789687 = 1184531) B1184531
theorem B1772747 : Blo 786339 1772747 := bstep (se 1 (by rfl) ⟨1329560, by rfl⟩ : syracuseStep 1772747 = 2659121) B2659121
theorem B1182923 : Blo 786339 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B789707 : Blo 786339 789707 := bstep (se 1 (by rfl) ⟨592280, by rfl⟩ : syracuseStep 789707 = 1184561) B1184561
theorem B1182935 : Blo 786339 1182935 := bstep (se 1 (by rfl) ⟨887201, by rfl⟩ : syracuseStep 1182935 = 1774403) B1774403
theorem B789719 : Blo 786339 789719 := bstep (se 1 (by rfl) ⟨592289, by rfl⟩ : syracuseStep 789719 = 1184579) B1184579
theorem B2657501 : Blo 786339 2657501 := bstep (se 3 (by rfl) ⟨498281, by rfl⟩ : syracuseStep 2657501 = 996563) B996563
theorem B888043 : Blo 786339 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B789739 : Blo 786339 789739 := bstep (se 1 (by rfl) ⟨592304, by rfl⟩ : syracuseStep 789739 = 1184609) B1184609
theorem B789751 : Blo 786339 789751 := bstep (se 1 (by rfl) ⟨592313, by rfl⟩ : syracuseStep 789751 = 1184627) B1184627
theorem B1772801 : Blo 786339 1772801 := bstep (se 2 (by rfl) ⟨664800, by rfl⟩ : syracuseStep 1772801 = 1329601) B1329601
theorem B72682757 : Blo 786339 72682757 := bstep (se 4 (by rfl) ⟨6814008, by rfl⟩ : syracuseStep 72682757 = 13628017) B13628017
theorem B789771 : Blo 786339 789771 := bstep (se 1 (by rfl) ⟨592328, by rfl⟩ : syracuseStep 789771 = 1184657) B1184657
theorem B789783 : Blo 786339 789783 := bstep (se 1 (by rfl) ⟨592337, by rfl⟩ : syracuseStep 789783 = 1184675) B1184675
theorem B1183001 : Blo 786339 1183001 := bstep (se 2 (by rfl) ⟨443625, by rfl⟩ : syracuseStep 1183001 = 887251) B887251
theorem B789803 : Blo 786339 789803 := bstep (se 1 (by rfl) ⟨592352, by rfl⟩ : syracuseStep 789803 = 1184705) B1184705
theorem B789815 : Blo 786339 789815 := bstep (se 1 (by rfl) ⟨592361, by rfl⟩ : syracuseStep 789815 = 1184723) B1184723
theorem B789835 : Blo 786339 789835 := bstep (se 1 (by rfl) ⟨592376, by rfl⟩ : syracuseStep 789835 = 1184753) B1184753
theorem B888151 : Blo 786339 888151 := bstep (se 1 (by rfl) ⟨666113, by rfl⟩ : syracuseStep 888151 = 1332227) B1332227
theorem B789847 : Blo 786339 789847 := bstep (se 1 (by rfl) ⟨592385, by rfl⟩ : syracuseStep 789847 = 1184771) B1184771
theorem B789867 : Blo 786339 789867 := bstep (se 1 (by rfl) ⟨592400, by rfl⟩ : syracuseStep 789867 = 1184801) B1184801
theorem B789879 : Blo 786339 789879 := bstep (se 1 (by rfl) ⟨592409, by rfl⟩ : syracuseStep 789879 = 1184819) B1184819
theorem B1183115 : Blo 786339 1183115 := bstep (se 1 (by rfl) ⟨887336, by rfl⟩ : syracuseStep 1183115 = 1774673) B1774673
theorem B789899 : Blo 786339 789899 := bstep (se 1 (by rfl) ⟨592424, by rfl⟩ : syracuseStep 789899 = 1184849) B1184849
theorem B1183127 : Blo 786339 1183127 := bstep (se 1 (by rfl) ⟨887345, by rfl⟩ : syracuseStep 1183127 = 1774691) B1774691
theorem B789911 : Blo 786339 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B789931 : Blo 786339 789931 := bstep (se 1 (by rfl) ⟨592448, by rfl⟩ : syracuseStep 789931 = 1184897) B1184897
theorem B789943 : Blo 786339 789943 := bstep (se 1 (by rfl) ⟨592457, by rfl⟩ : syracuseStep 789943 = 1184915) B1184915
theorem B789963 : Blo 786339 789963 := bstep (se 1 (by rfl) ⟨592472, by rfl⟩ : syracuseStep 789963 = 1184945) B1184945
theorem B789975 : Blo 786339 789975 := bstep (se 1 (by rfl) ⟨592481, by rfl⟩ : syracuseStep 789975 = 1184963) B1184963
theorem B1773017 : Blo 786339 1773017 := bstep (se 2 (by rfl) ⟨664881, by rfl⟩ : syracuseStep 1773017 = 1329763) B1329763
theorem B1183193 : Blo 786339 1183193 := bstep (se 2 (by rfl) ⟨443697, by rfl⟩ : syracuseStep 1183193 = 887395) B887395
theorem B789995 : Blo 786339 789995 := bstep (se 1 (by rfl) ⟨592496, by rfl⟩ : syracuseStep 789995 = 1184993) B1184993
theorem B790007 : Blo 786339 790007 := bstep (se 1 (by rfl) ⟨592505, by rfl⟩ : syracuseStep 790007 = 1185011) B1185011
theorem B888331 : Blo 786339 888331 := bstep (se 1 (by rfl) ⟨666248, by rfl⟩ : syracuseStep 888331 = 1332497) B1332497
theorem B790027 : Blo 786339 790027 := bstep (se 1 (by rfl) ⟨592520, by rfl⟩ : syracuseStep 790027 = 1185041) B1185041
theorem B790039 : Blo 786339 790039 := bstep (se 1 (by rfl) ⟨592529, by rfl⟩ : syracuseStep 790039 = 1185059) B1185059
theorem B790059 : Blo 786339 790059 := bstep (se 1 (by rfl) ⟨592544, by rfl⟩ : syracuseStep 790059 = 1185089) B1185089
theorem B1773107 : Blo 786339 1773107 := bstep (se 1 (by rfl) ⟨1329830, by rfl⟩ : syracuseStep 1773107 = 2659661) B2659661
theorem B790071 : Blo 786339 790071 := bstep (se 1 (by rfl) ⟨592553, by rfl⟩ : syracuseStep 790071 = 1185107) B1185107
theorem B1183307 : Blo 786339 1183307 := bstep (se 1 (by rfl) ⟨887480, by rfl⟩ : syracuseStep 1183307 = 1774961) B1774961
theorem B790091 : Blo 786339 790091 := bstep (se 1 (by rfl) ⟨592568, by rfl⟩ : syracuseStep 790091 = 1185137) B1185137
theorem B1773143 : Blo 786339 1773143 := bstep (se 1 (by rfl) ⟨1329857, by rfl⟩ : syracuseStep 1773143 = 2659715) B2659715
theorem B1183319 : Blo 786339 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B790103 : Blo 786339 790103 := bstep (se 1 (by rfl) ⟨592577, by rfl⟩ : syracuseStep 790103 = 1185155) B1185155
theorem B790123 : Blo 786339 790123 := bstep (se 1 (by rfl) ⟨592592, by rfl⟩ : syracuseStep 790123 = 1185185) B1185185
theorem B888439 : Blo 786339 888439 := bstep (se 1 (by rfl) ⟨666329, by rfl⟩ : syracuseStep 888439 = 1332659) B1332659
theorem B790135 : Blo 786339 790135 := bstep (se 1 (by rfl) ⟨592601, by rfl⟩ : syracuseStep 790135 = 1185203) B1185203
theorem B790155 : Blo 786339 790155 := bstep (se 1 (by rfl) ⟨592616, by rfl⟩ : syracuseStep 790155 = 1185233) B1185233
theorem B790167 : Blo 786339 790167 := bstep (se 1 (by rfl) ⟨592625, by rfl⟩ : syracuseStep 790167 = 1185251) B1185251
theorem B1183385 : Blo 786339 1183385 := bstep (se 2 (by rfl) ⟨443769, by rfl⟩ : syracuseStep 1183385 = 887539) B887539
theorem B790187 : Blo 786339 790187 := bstep (se 1 (by rfl) ⟨592640, by rfl⟩ : syracuseStep 790187 = 1185281) B1185281
theorem B790199 : Blo 786339 790199 := bstep (se 1 (by rfl) ⟨592649, by rfl⟩ : syracuseStep 790199 = 1185299) B1185299
theorem B790219 : Blo 786339 790219 := bstep (se 1 (by rfl) ⟨592664, by rfl⟩ : syracuseStep 790219 = 1185329) B1185329
theorem B790231 : Blo 786339 790231 := bstep (se 1 (by rfl) ⟨592673, by rfl⟩ : syracuseStep 790231 = 1185347) B1185347
theorem B2395865 : Blo 786339 2395865 := bstep (se 2 (by rfl) ⟨898449, by rfl⟩ : syracuseStep 2395865 = 1796899) B1796899
theorem B790251 : Blo 786339 790251 := bstep (se 1 (by rfl) ⟨592688, by rfl⟩ : syracuseStep 790251 = 1185377) B1185377
theorem B790263 : Blo 786339 790263 := bstep (se 1 (by rfl) ⟨592697, by rfl⟩ : syracuseStep 790263 = 1185395) B1185395
theorem B1773323 : Blo 786339 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B1183499 : Blo 786339 1183499 := bstep (se 1 (by rfl) ⟨887624, by rfl⟩ : syracuseStep 1183499 = 1775249) B1775249
theorem B790283 : Blo 786339 790283 := bstep (se 1 (by rfl) ⟨592712, by rfl⟩ : syracuseStep 790283 = 1185425) B1185425
theorem B1183511 : Blo 786339 1183511 := bstep (se 1 (by rfl) ⟨887633, by rfl⟩ : syracuseStep 1183511 = 1775267) B1775267
theorem B790295 : Blo 786339 790295 := bstep (se 1 (by rfl) ⟨592721, by rfl⟩ : syracuseStep 790295 = 1185443) B1185443
theorem B888619 : Blo 786339 888619 := bstep (se 1 (by rfl) ⟨666464, by rfl⟩ : syracuseStep 888619 = 1332929) B1332929
theorem B790315 : Blo 786339 790315 := bstep (se 1 (by rfl) ⟨592736, by rfl⟩ : syracuseStep 790315 = 1185473) B1185473
theorem B790327 : Blo 786339 790327 := bstep (se 1 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 790327 = 1185491) B1185491
theorem B1773377 : Blo 786339 1773377 := bstep (se 2 (by rfl) ⟨665016, by rfl⟩ : syracuseStep 1773377 = 1330033) B1330033
theorem B1183577 : Blo 786339 1183577 := bstep (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) B887683
theorem B888727 : Blo 786339 888727 := bstep (se 1 (by rfl) ⟨666545, by rfl⟩ : syracuseStep 888727 = 1333091) B1333091
theorem B1183691 : Blo 786339 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B1183703 : Blo 786339 1183703 := bstep (se 1 (by rfl) ⟨887777, by rfl⟩ : syracuseStep 1183703 = 1775555) B1775555
theorem B6721541 : Blo 786339 6721541 := bstep (se 4 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 6721541 = 1260289) B1260289
theorem B1773593 : Blo 786339 1773593 := bstep (se 2 (by rfl) ⟨665097, by rfl⟩ : syracuseStep 1773593 = 1330195) B1330195
theorem B1183769 : Blo 786339 1183769 := bstep (se 2 (by rfl) ⟨443913, by rfl⟩ : syracuseStep 1183769 = 887827) B887827
theorem B2527307 : Blo 786339 2527307 := bstep (se 1 (by rfl) ⟨1895480, by rfl⟩ : syracuseStep 2527307 = 3790961) B3790961
theorem B888907 : Blo 786339 888907 := bstep (se 1 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 888907 = 1333361) B1333361
theorem B9605213 : Blo 786339 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1773683 : Blo 786339 1773683 := bstep (se 1 (by rfl) ⟨1330262, by rfl⟩ : syracuseStep 1773683 = 2660525) B2660525
theorem B1183883 : Blo 786339 1183883 := bstep (se 1 (by rfl) ⟨887912, by rfl⟩ : syracuseStep 1183883 = 1775825) B1775825
theorem B1773719 : Blo 786339 1773719 := bstep (se 1 (by rfl) ⟨1330289, by rfl⟩ : syracuseStep 1773719 = 2660579) B2660579
theorem B1183895 : Blo 786339 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B889015 : Blo 786339 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B1183961 : Blo 786339 1183961 := bstep (se 2 (by rfl) ⟨443985, by rfl⟩ : syracuseStep 1183961 = 887971) B887971
theorem B7180589 : Blo 786339 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B2658635 : Blo 786339 2658635 := bstep (se 1 (by rfl) ⟨1993976, by rfl⟩ : syracuseStep 2658635 = 3987953) B3987953
theorem B1773899 : Blo 786339 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B1184075 : Blo 786339 1184075 := bstep (se 1 (by rfl) ⟨888056, by rfl⟩ : syracuseStep 1184075 = 1776113) B1776113
theorem B1184087 : Blo 786339 1184087 := bstep (se 1 (by rfl) ⟨888065, by rfl⟩ : syracuseStep 1184087 = 1776131) B1776131
theorem B1773953 : Blo 786339 1773953 := bstep (se 2 (by rfl) ⟨665232, by rfl⟩ : syracuseStep 1773953 = 1330465) B1330465
theorem B1184153 : Blo 786339 1184153 := bstep (se 2 (by rfl) ⟨444057, by rfl⟩ : syracuseStep 1184153 = 888115) B888115
theorem B1184267 : Blo 786339 1184267 := bstep (se 1 (by rfl) ⟨888200, by rfl⟩ : syracuseStep 1184267 = 1776401) B1776401
theorem B1184279 : Blo 786339 1184279 := bstep (se 1 (by rfl) ⟨888209, by rfl⟩ : syracuseStep 1184279 = 1776419) B1776419
theorem B2658905 : Blo 786339 2658905 := bstep (se 2 (by rfl) ⟨997089, by rfl⟩ : syracuseStep 2658905 = 1994179) B1994179
theorem B1774169 : Blo 786339 1774169 := bstep (se 2 (by rfl) ⟨665313, by rfl⟩ : syracuseStep 1774169 = 1330627) B1330627
theorem B1184345 : Blo 786339 1184345 := bstep (se 2 (by rfl) ⟨444129, by rfl⟩ : syracuseStep 1184345 = 888259) B888259
theorem B1774259 : Blo 786339 1774259 := bstep (se 1 (by rfl) ⟨1330694, by rfl⟩ : syracuseStep 1774259 = 2661389) B2661389
theorem B1184459 : Blo 786339 1184459 := bstep (se 1 (by rfl) ⟨888344, by rfl⟩ : syracuseStep 1184459 = 1776689) B1776689
theorem B1774295 : Blo 786339 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1184471 : Blo 786339 1184471 := bstep (se 1 (by rfl) ⟨888353, by rfl⟩ : syracuseStep 1184471 = 1776707) B1776707
theorem B1184537 : Blo 786339 1184537 := bstep (se 2 (by rfl) ⟨444201, by rfl⟩ : syracuseStep 1184537 = 888403) B888403
theorem B1774475 : Blo 786339 1774475 := bstep (se 1 (by rfl) ⟨1330856, by rfl⟩ : syracuseStep 1774475 = 2661713) B2661713
theorem B1184651 : Blo 786339 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B1184663 : Blo 786339 1184663 := bstep (se 1 (by rfl) ⟨888497, by rfl⟩ : syracuseStep 1184663 = 1776995) B1776995
theorem B1774529 : Blo 786339 1774529 := bstep (se 2 (by rfl) ⟨665448, by rfl⟩ : syracuseStep 1774529 = 1330897) B1330897
theorem B6001613 : Blo 786339 6001613 := bstep (se 3 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 6001613 = 2250605) B2250605
theorem B1184729 : Blo 786339 1184729 := bstep (se 2 (by rfl) ⟨444273, by rfl⟩ : syracuseStep 1184729 = 888547) B888547
theorem B1184843 : Blo 786339 1184843 := bstep (se 1 (by rfl) ⟨888632, by rfl⟩ : syracuseStep 1184843 = 1777265) B1777265
theorem B1184855 : Blo 786339 1184855 := bstep (se 1 (by rfl) ⟨888641, by rfl⟩ : syracuseStep 1184855 = 1777283) B1777283
theorem B4494467 : Blo 786339 4494467 := bstep (se 1 (by rfl) ⟨3370850, by rfl⟩ : syracuseStep 4494467 = 6741701) B6741701
theorem B1774745 : Blo 786339 1774745 := bstep (se 2 (by rfl) ⟨665529, by rfl⟩ : syracuseStep 1774745 = 1331059) B1331059
theorem B1184921 : Blo 786339 1184921 := bstep (se 2 (by rfl) ⟨444345, by rfl⟩ : syracuseStep 1184921 = 888691) B888691
theorem B2528435 : Blo 786339 2528435 := bstep (se 1 (by rfl) ⟨1896326, by rfl⟩ : syracuseStep 2528435 = 3792653) B3792653
theorem B1774835 : Blo 786339 1774835 := bstep (se 1 (by rfl) ⟨1331126, by rfl⟩ : syracuseStep 1774835 = 2662253) B2662253
theorem B1185035 : Blo 786339 1185035 := bstep (se 1 (by rfl) ⟨888776, by rfl⟩ : syracuseStep 1185035 = 1777553) B1777553
theorem B2659607 : Blo 786339 2659607 := bstep (se 1 (by rfl) ⟨1994705, by rfl⟩ : syracuseStep 2659607 = 3989411) B3989411
theorem B1774871 : Blo 786339 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B1185047 : Blo 786339 1185047 := bstep (se 1 (by rfl) ⟨888785, by rfl⟩ : syracuseStep 1185047 = 1777571) B1777571
theorem B1185113 : Blo 786339 1185113 := bstep (se 2 (by rfl) ⟨444417, by rfl⟩ : syracuseStep 1185113 = 888835) B888835
theorem B6395267 : Blo 786339 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B1775051 : Blo 786339 1775051 := bstep (se 1 (by rfl) ⟨1331288, by rfl⟩ : syracuseStep 1775051 = 2662577) B2662577
theorem B1185227 : Blo 786339 1185227 := bstep (se 1 (by rfl) ⟨888920, by rfl⟩ : syracuseStep 1185227 = 1777841) B1777841
theorem B5674445 : Blo 786339 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B48534997 : Blo 786339 48534997 := bstep (se 7 (by rfl) ⟨568769, by rfl⟩ : syracuseStep 48534997 = 1137539) B1137539
theorem B1185239 : Blo 786339 1185239 := bstep (se 1 (by rfl) ⟨888929, by rfl⟩ : syracuseStep 1185239 = 1777859) B1777859
theorem B1775105 : Blo 786339 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B1185305 : Blo 786339 1185305 := bstep (se 2 (by rfl) ⟨444489, by rfl⟩ : syracuseStep 1185305 = 888979) B888979
theorem B4494923 : Blo 786339 4494923 := bstep (se 1 (by rfl) ⟨3371192, by rfl⟩ : syracuseStep 4494923 = 6742385) B6742385
theorem B8984195 : Blo 786339 8984195 := bstep (se 1 (by rfl) ⟨6738146, by rfl⟩ : syracuseStep 8984195 = 13476293) B13476293
theorem B1185419 : Blo 786339 1185419 := bstep (se 1 (by rfl) ⟨889064, by rfl⟩ : syracuseStep 1185419 = 1778129) B1778129
theorem B1185431 : Blo 786339 1185431 := bstep (se 1 (by rfl) ⟨889073, by rfl⟩ : syracuseStep 1185431 = 1778147) B1778147
theorem B1775321 : Blo 786339 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B1185497 : Blo 786339 1185497 := bstep (se 2 (by rfl) ⟨444561, by rfl⟩ : syracuseStep 1185497 = 889123) B889123
theorem B2660147 : Blo 786339 2660147 := bstep (se 1 (by rfl) ⟨1995110, by rfl⟩ : syracuseStep 2660147 = 3990221) B3990221
theorem B1775411 : Blo 786339 1775411 := bstep (se 1 (by rfl) ⟨1331558, by rfl⟩ : syracuseStep 1775411 = 2663117) B2663117
theorem B1775447 : Blo 786339 1775447 := bstep (se 1 (by rfl) ⟨1331585, by rfl⟩ : syracuseStep 1775447 = 2663171) B2663171
theorem B2398103 : Blo 786339 2398103 := bstep (se 1 (by rfl) ⟨1798577, by rfl⟩ : syracuseStep 2398103 = 3597155) B3597155
theorem B3413933 : Blo 786339 3413933 := bstep (se 3 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 3413933 = 1280225) B1280225
theorem B2988035 : Blo 786339 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B1775627 : Blo 786339 1775627 := bstep (se 1 (by rfl) ⟨1331720, by rfl⟩ : syracuseStep 1775627 = 2663441) B2663441
theorem B2988049 : Blo 786339 2988049 := bstep (se 2 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 2988049 = 2241037) B2241037
theorem B2660417 : Blo 786339 2660417 := bstep (se 2 (by rfl) ⟨997656, by rfl⟩ : syracuseStep 2660417 = 1995313) B1995313
theorem B1775681 : Blo 786339 1775681 := bstep (se 2 (by rfl) ⟨665880, by rfl⟩ : syracuseStep 1775681 = 1331761) B1331761
theorem B1120331 : Blo 786339 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B1513687 : Blo 786339 1513687 := bstep (se 1 (by rfl) ⟨1135265, by rfl⟩ : syracuseStep 1513687 = 2270531) B2270531
theorem B5052689 : Blo 786339 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B1775897 : Blo 786339 1775897 := bstep (se 2 (by rfl) ⟨665961, by rfl⟩ : syracuseStep 1775897 = 1331923) B1331923
theorem B2988353 : Blo 786339 2988353 := bstep (se 2 (by rfl) ⟨1120632, by rfl⟩ : syracuseStep 2988353 = 2241265) B2241265
theorem B2529625 : Blo 786339 2529625 := bstep (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) B1897219
theorem B1775987 : Blo 786339 1775987 := bstep (se 1 (by rfl) ⟨1331990, by rfl⟩ : syracuseStep 1775987 = 2663981) B2663981
theorem B1776023 : Blo 786339 1776023 := bstep (se 1 (by rfl) ⟨1332017, by rfl⟩ : syracuseStep 1776023 = 2664035) B2664035
theorem B3381805 : Blo 786339 3381805 := bstep (se 3 (by rfl) ⟨634088, by rfl⟩ : syracuseStep 3381805 = 1268177) B1268177
theorem B1776203 : Blo 786339 1776203 := bstep (se 1 (by rfl) ⟨1332152, by rfl⟩ : syracuseStep 1776203 = 2664305) B2664305
theorem B2529881 : Blo 786339 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B2660957 : Blo 786339 2660957 := bstep (se 3 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 2660957 = 997859) B997859
theorem B1776257 : Blo 786339 1776257 := bstep (se 2 (by rfl) ⟨666096, by rfl⟩ : syracuseStep 1776257 = 1332193) B1332193
theorem B5380739 : Blo 786339 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B3152729 : Blo 786339 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B1776473 : Blo 786339 1776473 := bstep (se 2 (by rfl) ⟨666177, by rfl⟩ : syracuseStep 1776473 = 1332355) B1332355
theorem B1776563 : Blo 786339 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B2530241 : Blo 786339 2530241 := bstep (se 2 (by rfl) ⟨948840, by rfl⟩ : syracuseStep 2530241 = 1897681) B1897681
theorem B1776599 : Blo 786339 1776599 := bstep (se 1 (by rfl) ⟨1332449, by rfl⟩ : syracuseStep 1776599 = 2664899) B2664899
theorem B2989021 : Blo 786339 2989021 := bstep (se 3 (by rfl) ⟨560441, by rfl⟩ : syracuseStep 2989021 = 1120883) B1120883
theorem B1121305 : Blo 786339 1121305 := bstep (se 2 (by rfl) ⟨420489, by rfl⟩ : syracuseStep 1121305 = 840979) B840979
theorem B1776779 : Blo 786339 1776779 := bstep (se 1 (by rfl) ⟨1332584, by rfl⟩ : syracuseStep 1776779 = 2665169) B2665169
theorem B7183511 : Blo 786339 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B1776833 : Blo 786339 1776833 := bstep (se 2 (by rfl) ⟨666312, by rfl⟩ : syracuseStep 1776833 = 1332625) B1332625
theorem B1777049 : Blo 786339 1777049 := bstep (se 2 (by rfl) ⟨666393, by rfl⟩ : syracuseStep 1777049 = 1332787) B1332787
theorem B1777139 : Blo 786339 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B1777175 : Blo 786339 1777175 := bstep (se 1 (by rfl) ⟨1332881, by rfl⟩ : syracuseStep 1777175 = 2665763) B2665763
theorem B4496941 : Blo 786339 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B2694721 : Blo 786339 2694721 := bstep (se 2 (by rfl) ⟨1010520, by rfl⟩ : syracuseStep 2694721 = 2021041) B2021041
theorem B2531009 : Blo 786339 2531009 := bstep (se 2 (by rfl) ⟨949128, by rfl⟩ : syracuseStep 2531009 = 1898257) B1898257
theorem B2662091 : Blo 786339 2662091 := bstep (se 1 (by rfl) ⟨1996568, by rfl⟩ : syracuseStep 2662091 = 3993137) B3993137
theorem B1777355 : Blo 786339 1777355 := bstep (se 1 (by rfl) ⟨1333016, by rfl⟩ : syracuseStep 1777355 = 2666033) B2666033
theorem B1777409 : Blo 786339 1777409 := bstep (se 2 (by rfl) ⟨666528, by rfl⟩ : syracuseStep 1777409 = 1333057) B1333057
theorem B92348261 : Blo 786339 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B10100659 : Blo 786339 10100659 := bstep (se 1 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 10100659 = 15150989) B15150989
theorem B2662361 : Blo 786339 2662361 := bstep (se 2 (by rfl) ⟨998385, by rfl⟩ : syracuseStep 2662361 = 1996771) B1996771
theorem B1777625 : Blo 786339 1777625 := bstep (se 2 (by rfl) ⟨666609, by rfl⟩ : syracuseStep 1777625 = 1333219) B1333219
theorem B1777715 : Blo 786339 1777715 := bstep (se 1 (by rfl) ⟨1333286, by rfl⟩ : syracuseStep 1777715 = 2666573) B2666573
theorem B1777751 : Blo 786339 1777751 := bstep (se 1 (by rfl) ⟨1333313, by rfl⟩ : syracuseStep 1777751 = 2666627) B2666627
theorem B1122455 : Blo 786339 1122455 := bstep (se 1 (by rfl) ⟨841841, by rfl⟩ : syracuseStep 1122455 = 1683683) B1683683
theorem B2531521 : Blo 786339 2531521 := bstep (se 2 (by rfl) ⟨949320, by rfl⟩ : syracuseStep 2531521 = 1898641) B1898641
theorem B2990297 : Blo 786339 2990297 := bstep (se 2 (by rfl) ⟨1121361, by rfl⟩ : syracuseStep 2990297 = 2242723) B2242723
theorem B1417459 : Blo 786339 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B7184645 : Blo 786339 7184645 := bstep (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) B1347121
theorem B1777931 : Blo 786339 1777931 := bstep (se 1 (by rfl) ⟨1333448, by rfl⟩ : syracuseStep 1777931 = 2666897) B2666897
theorem B1777985 : Blo 786339 1777985 := bstep (se 2 (by rfl) ⟨666744, by rfl⟩ : syracuseStep 1777985 = 1333489) B1333489
theorem B2695517 : Blo 786339 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B1122763 : Blo 786339 1122763 := bstep (se 1 (by rfl) ⟨842072, by rfl⟩ : syracuseStep 1122763 = 1684145) B1684145
theorem B1417753 : Blo 786339 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B1778201 : Blo 786339 1778201 := bstep (se 2 (by rfl) ⟨666825, by rfl⟩ : syracuseStep 1778201 = 1333651) B1333651
theorem B2663063 : Blo 786339 2663063 := bstep (se 1 (by rfl) ⟨1997297, by rfl⟩ : syracuseStep 2663063 = 3994595) B3994595
theorem B5383091 : Blo 786339 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B2401217 : Blo 786339 2401217 := bstep (se 2 (by rfl) ⟨900456, by rfl⟩ : syracuseStep 2401217 = 1800913) B1800913
theorem B2663603 : Blo 786339 2663603 := bstep (se 1 (by rfl) ⟨1997702, by rfl⟩ : syracuseStep 2663603 = 3995405) B3995405
theorem B5973425 : Blo 786339 5973425 := bstep (se 2 (by rfl) ⟨2240034, by rfl⟩ : syracuseStep 5973425 = 4480069) B4480069
theorem B2663873 : Blo 786339 2663873 := bstep (se 2 (by rfl) ⟨998952, by rfl⟩ : syracuseStep 2663873 = 1997905) B1997905
theorem B1123799 : Blo 786339 1123799 := bstep (se 1 (by rfl) ⟨842849, by rfl⟩ : syracuseStep 1123799 = 1685699) B1685699
theorem B1680907 : Blo 786339 1680907 := bstep (se 1 (by rfl) ⟨1260680, by rfl⟩ : syracuseStep 1680907 = 2521361) B2521361
theorem B1123993 : Blo 786339 1123993 := bstep (se 2 (by rfl) ⟨421497, by rfl⟩ : syracuseStep 1123993 = 842995) B842995
theorem B2991923 : Blo 786339 2991923 := bstep (se 1 (by rfl) ⟨2243942, by rfl⟩ : syracuseStep 2991923 = 4487885) B4487885
theorem B2991937 : Blo 786339 2991937 := bstep (se 2 (by rfl) ⟨1121976, by rfl⟩ : syracuseStep 2991937 = 2243953) B2243953
theorem B5973911 : Blo 786339 5973911 := bstep (se 1 (by rfl) ⟨4480433, by rfl⟩ : syracuseStep 5973911 = 8960867) B8960867
theorem B2664413 : Blo 786339 2664413 := bstep (se 3 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 2664413 = 999155) B999155
theorem B4499549 : Blo 786339 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B3188909 : Blo 786339 3188909 := bstep (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) B1195841
theorem B4041035 : Blo 786339 4041035 := bstep (se 1 (by rfl) ⟨3030776, by rfl⟩ : syracuseStep 4041035 = 6061553) B6061553
theorem B1419671 : Blo 786339 1419671 := bstep (se 1 (by rfl) ⟨1064753, by rfl⟩ : syracuseStep 1419671 = 2129507) B2129507
theorem B8530393 : Blo 786339 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B1682137 : Blo 786339 1682137 := bstep (se 2 (by rfl) ⟨630801, by rfl⟩ : syracuseStep 1682137 = 1261603) B1261603
theorem B4500299 : Blo 786339 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B6728579 : Blo 786339 6728579 := bstep (se 1 (by rfl) ⟨5046434, by rfl⟩ : syracuseStep 6728579 = 10092869) B10092869
theorem B12331993 : Blo 786339 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B1420363 : Blo 786339 1420363 := bstep (se 1 (by rfl) ⟨1065272, by rfl⟩ : syracuseStep 1420363 = 2130545) B2130545
theorem B2665547 : Blo 786339 2665547 := bstep (se 1 (by rfl) ⟨1999160, by rfl⟩ : syracuseStep 2665547 = 3998321) B3998321
theorem B2665817 : Blo 786339 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B798103 : Blo 786339 798103 := bstep (se 1 (by rfl) ⟨598577, by rfl⟩ : syracuseStep 798103 = 1197155) B1197155
theorem B2993867 : Blo 786339 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B3452633 : Blo 786339 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2993881 : Blo 786339 2993881 := bstep (se 2 (by rfl) ⟨1122705, by rfl⟩ : syracuseStep 2993881 = 2245411) B2245411
theorem B3419927 : Blo 786339 3419927 := bstep (se 1 (by rfl) ⟨2564945, by rfl⟩ : syracuseStep 3419927 = 5129891) B5129891
theorem B3780503 : Blo 786339 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B2666519 : Blo 786339 2666519 := bstep (se 1 (by rfl) ⟨1999889, by rfl⟩ : syracuseStep 2666519 = 3999779) B3999779
theorem B4272203 : Blo 786339 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B1421761 : Blo 786339 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B2667059 : Blo 786339 2667059 := bstep (se 1 (by rfl) ⟨2000294, by rfl⟩ : syracuseStep 2667059 = 4000589) B4000589
theorem B995915 : Blo 786339 995915 := bstep (se 1 (by rfl) ⟨746936, by rfl⟩ : syracuseStep 995915 = 1493873) B1493873
theorem B2994839 : Blo 786339 2994839 := bstep (se 1 (by rfl) ⟨2246129, by rfl⟩ : syracuseStep 2994839 = 4492259) B4492259
theorem B2667329 : Blo 786339 2667329 := bstep (se 2 (by rfl) ⟨1000248, by rfl⟩ : syracuseStep 2667329 = 2000497) B2000497
theorem B15119621 : Blo 786339 15119621 := bstep (se 4 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 15119621 = 2834929) B2834929
theorem B996619 : Blo 786339 996619 := bstep (se 1 (by rfl) ⟨747464, by rfl⟩ : syracuseStep 996619 = 1494929) B1494929
theorem B2241857 : Blo 786339 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B2241881 : Blo 786339 2241881 := bstep (se 2 (by rfl) ⟨840705, by rfl⟩ : syracuseStep 2241881 = 1681411) B1681411
theorem B8959409 : Blo 786339 8959409 := bstep (se 2 (by rfl) ⟨3359778, by rfl⟩ : syracuseStep 8959409 = 6719557) B6719557
theorem B3192281 : Blo 786339 3192281 := bstep (se 2 (by rfl) ⟨1197105, by rfl⟩ : syracuseStep 3192281 = 2394211) B2394211
theorem B996887 : Blo 786339 996887 := bstep (se 1 (by rfl) ⟨747665, by rfl⟩ : syracuseStep 996887 = 1495331) B1495331
theorem B5060171 : Blo 786339 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B21575261 : Blo 786339 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B6076109 : Blo 786339 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B1685323 : Blo 786339 1685323 := bstep (se 1 (by rfl) ⟨1263992, by rfl⟩ : syracuseStep 1685323 = 2527985) B2527985
theorem B2996099 : Blo 786339 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B997591 : Blo 786339 997591 := bstep (se 1 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 997591 = 1496387) B1496387
theorem B1685785 : Blo 786339 1685785 := bstep (se 2 (by rfl) ⟨632169, by rfl⟩ : syracuseStep 1685785 = 1264339) B1264339
theorem B6076973 : Blo 786339 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B2243123 : Blo 786339 2243123 := bstep (se 1 (by rfl) ⟨1682342, by rfl⟩ : syracuseStep 2243123 = 3364685) B3364685
theorem B8632925 : Blo 786339 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B13450049 : Blo 786339 13450049 := bstep (se 2 (by rfl) ⟨5043768, by rfl⟩ : syracuseStep 13450049 = 10087537) B10087537
theorem B900343 : Blo 786339 900343 := bstep (se 1 (by rfl) ⟨675257, by rfl⟩ : syracuseStep 900343 = 1350515) B1350515
theorem B1687169 : Blo 786339 1687169 := bstep (se 2 (by rfl) ⟨632688, by rfl⟩ : syracuseStep 1687169 = 1265377) B1265377
theorem B20168513 : Blo 786339 20168513 := bstep (se 2 (by rfl) ⟨7563192, by rfl⟩ : syracuseStep 20168513 = 15126385) B15126385
theorem B3981149 : Blo 786339 3981149 := bstep (se 3 (by rfl) ⟨746465, by rfl⟩ : syracuseStep 3981149 = 1492931) B1492931
theorem B999307 : Blo 786339 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B1327063 : Blo 786339 1327063 := bstep (se 1 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 1327063 = 1990595) B1990595
theorem B2834455 : Blo 786339 2834455 := bstep (se 1 (by rfl) ⟨2125841, by rfl⟩ : syracuseStep 2834455 = 4251683) B4251683
theorem B3653707 : Blo 786339 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B2310617 : Blo 786339 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1327691 : Blo 786339 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B5685835 : Blo 786339 5685835 := bstep (se 1 (by rfl) ⟨4264376, by rfl⟩ : syracuseStep 5685835 = 8528753) B8528753
theorem B57459293 : Blo 786339 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B1327819 : Blo 786339 1327819 := bstep (se 1 (by rfl) ⟨995864, by rfl⟩ : syracuseStep 1327819 = 1991729) B1991729
theorem B1196759 : Blo 786339 1196759 := bstep (se 1 (by rfl) ⟨897569, by rfl⟩ : syracuseStep 1196759 = 1795139) B1795139
theorem B1262423 : Blo 786339 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B1327961 : Blo 786339 1327961 := bstep (se 2 (by rfl) ⟨497985, by rfl⟩ : syracuseStep 1327961 = 995971) B995971
theorem B3031901 : Blo 786339 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5391197 : Blo 786339 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B2999213 : Blo 786339 2999213 := bstep (se 3 (by rfl) ⟨562352, by rfl⟩ : syracuseStep 2999213 = 1124705) B1124705
theorem B1328089 : Blo 786339 1328089 := bstep (se 2 (by rfl) ⟨498033, by rfl⟩ : syracuseStep 1328089 = 996067) B996067
theorem B5981201 : Blo 786339 5981201 := bstep (se 2 (by rfl) ⟨2242950, by rfl⟩ : syracuseStep 5981201 = 4485901) B4485901
theorem B4867165 : Blo 786339 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B1262731 : Blo 786339 1262731 := bstep (se 1 (by rfl) ⟨947048, by rfl⟩ : syracuseStep 1262731 = 1894097) B1894097
theorem B2245981 : Blo 786339 2245981 := bstep (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) B842243
theorem B2246039 : Blo 786339 2246039 := bstep (se 1 (by rfl) ⟨1684529, by rfl⟩ : syracuseStep 2246039 = 3369059) B3369059
theorem B1328663 : Blo 786339 1328663 := bstep (se 1 (by rfl) ⟨996497, by rfl⟩ : syracuseStep 1328663 = 1992995) B1992995
theorem B1328791 : Blo 786339 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B2999987 : Blo 786339 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B1066775 : Blo 786339 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B20531009 : Blo 786339 20531009 := bstep (se 2 (by rfl) ⟨7699128, by rfl⟩ : syracuseStep 20531009 = 15398257) B15398257
theorem B1492825 : Blo 786339 1492825 := bstep (se 2 (by rfl) ⟨559809, by rfl⟩ : syracuseStep 1492825 = 1119619) B1119619
theorem B3983255 : Blo 786339 3983255 := bstep (se 1 (by rfl) ⟨2987441, by rfl⟩ : syracuseStep 3983255 = 5974883) B5974883
theorem B51136433 : Blo 786339 51136433 := bstep (se 2 (by rfl) ⟨19176162, by rfl⟩ : syracuseStep 51136433 = 38352325) B38352325
theorem B3590147 : Blo 786339 3590147 := bstep (se 1 (by rfl) ⟨2692610, by rfl⟩ : syracuseStep 3590147 = 5385221) B5385221
theorem B1329419 : Blo 786339 1329419 := bstep (se 1 (by rfl) ⟨997064, by rfl⟩ : syracuseStep 1329419 = 1994129) B1994129
theorem B1263961 : Blo 786339 1263961 := bstep (se 2 (by rfl) ⟨473985, by rfl⟩ : syracuseStep 1263961 = 947971) B947971
theorem B1493387 : Blo 786339 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B1329547 : Blo 786339 1329547 := bstep (se 1 (by rfl) ⟨997160, by rfl⟩ : syracuseStep 1329547 = 1994321) B1994321
theorem B1067467 : Blo 786339 1067467 := bstep (se 1 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 1067467 = 1601201) B1601201
theorem B3361283 : Blo 786339 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B3590659 : Blo 786339 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1329689 : Blo 786339 1329689 := bstep (se 2 (by rfl) ⟨498633, by rfl⟩ : syracuseStep 1329689 = 997267) B997267
theorem B1493569 : Blo 786339 1493569 := bstep (se 2 (by rfl) ⟨560088, by rfl⟩ : syracuseStep 1493569 = 1120177) B1120177
theorem B2247257 : Blo 786339 2247257 := bstep (se 2 (by rfl) ⟨842721, by rfl⟩ : syracuseStep 2247257 = 1685443) B1685443
theorem B1329817 : Blo 786339 1329817 := bstep (se 2 (by rfl) ⟨498681, by rfl⟩ : syracuseStep 1329817 = 997363) B997363
theorem B2247371 : Blo 786339 2247371 := bstep (se 1 (by rfl) ⟨1685528, by rfl⟩ : syracuseStep 2247371 = 3371057) B3371057
theorem B3361625 : Blo 786339 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B1330391 : Blo 786339 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B1494283 : Blo 786339 1494283 := bstep (se 1 (by rfl) ⟨1120712, by rfl⟩ : syracuseStep 1494283 = 2241425) B2241425
theorem B1494359 : Blo 786339 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B1330519 : Blo 786339 1330519 := bstep (se 1 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 1330519 = 1995779) B1995779
theorem B3788363 : Blo 786339 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B2248499 : Blo 786339 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B1200025 : Blo 786339 1200025 := bstep (se 2 (by rfl) ⟨450009, by rfl⟩ : syracuseStep 1200025 = 900019) B900019
theorem B1331147 : Blo 786339 1331147 := bstep (se 1 (by rfl) ⟨998360, by rfl⟩ : syracuseStep 1331147 = 1996721) B1996721
theorem B1495027 : Blo 786339 1495027 := bstep (se 1 (by rfl) ⟨1121270, by rfl⟩ : syracuseStep 1495027 = 2242541) B2242541
theorem B1331275 : Blo 786339 1331275 := bstep (se 1 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 1331275 = 1996913) B1996913
theorem B2248897 : Blo 786339 2248897 := bstep (se 2 (by rfl) ⟨843336, by rfl⟩ : syracuseStep 2248897 = 1686673) B1686673
theorem B1495255 : Blo 786339 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1331417 : Blo 786339 1331417 := bstep (se 2 (by rfl) ⟨499281, by rfl⟩ : syracuseStep 1331417 = 998563) B998563
theorem B1495361 : Blo 786339 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B1331545 : Blo 786339 1331545 := bstep (se 2 (by rfl) ⟨499329, by rfl⟩ : syracuseStep 1331545 = 998659) B998659
theorem B1495513 : Blo 786339 1495513 := bstep (se 2 (by rfl) ⟨560817, by rfl⟩ : syracuseStep 1495513 = 1121635) B1121635
theorem B15323741 : Blo 786339 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B1200779 : Blo 786339 1200779 := bstep (se 1 (by rfl) ⟨900584, by rfl⟩ : syracuseStep 1200779 = 1801169) B1801169
theorem B12800717 : Blo 786339 12800717 := bstep (se 3 (by rfl) ⟨2400134, by rfl⟩ : syracuseStep 12800717 = 4800269) B4800269
theorem B5985089 : Blo 786339 5985089 := bstep (se 2 (by rfl) ⟨2244408, by rfl⟩ : syracuseStep 5985089 = 4488817) B4488817
theorem B1332119 : Blo 786339 1332119 := bstep (se 1 (by rfl) ⟨999089, by rfl⟩ : syracuseStep 1332119 = 1998179) B1998179
theorem B840727 : Blo 786339 840727 := bstep (se 1 (by rfl) ⟨630545, by rfl⟩ : syracuseStep 840727 = 1261091) B1261091
theorem B1332247 : Blo 786339 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B6739037 : Blo 786339 6739037 := bstep (se 3 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 6739037 = 2527139) B2527139
theorem B1725761 : Blo 786339 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B3986819 : Blo 786339 3986819 := bstep (se 1 (by rfl) ⟨2990114, by rfl⟩ : syracuseStep 3986819 = 5980229) B5980229
theorem B3593651 : Blo 786339 3593651 := bstep (se 1 (by rfl) ⟨2695238, by rfl⟩ : syracuseStep 3593651 = 5390477) B5390477
theorem B1201625 : Blo 786339 1201625 := bstep (se 2 (by rfl) ⟨450609, by rfl⟩ : syracuseStep 1201625 = 901219) B901219
theorem B3462659 : Blo 786339 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B1332875 : Blo 786339 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B1496819 : Blo 786339 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B1333003 : Blo 786339 1333003 := bstep (se 1 (by rfl) ⟨999752, by rfl⟩ : syracuseStep 1333003 = 1999505) B1999505
theorem B841547 : Blo 786339 841547 := bstep (se 1 (by rfl) ⟨631160, by rfl⟩ : syracuseStep 841547 = 1262321) B1262321
theorem B6739787 : Blo 786339 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B3200843 : Blo 786339 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1496971 : Blo 786339 1496971 := bstep (se 1 (by rfl) ⟨1122728, by rfl⟩ : syracuseStep 1496971 = 2245457) B2245457
theorem B2840465 : Blo 786339 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B1333145 : Blo 786339 1333145 := bstep (se 2 (by rfl) ⟨499929, by rfl⟩ : syracuseStep 1333145 = 999859) B999859
theorem B1595315 : Blo 786339 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B2873291 : Blo 786339 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1333273 : Blo 786339 1333273 := bstep (se 2 (by rfl) ⟨499977, by rfl⟩ : syracuseStep 1333273 = 999955) B999955
theorem B3365009 : Blo 786339 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B2021593 : Blo 786339 2021593 := bstep (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) B1516195
theorem B1497305 : Blo 786339 1497305 := bstep (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) B1122979
theorem B5987033 : Blo 786339 5987033 := bstep (se 2 (by rfl) ⟨2245137, by rfl⟩ : syracuseStep 5987033 = 4490275) B4490275
theorem B2841389 : Blo 786339 2841389 := bstep (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) B1065521
theorem B2841419 : Blo 786339 2841419 := bstep (se 1 (by rfl) ⟨2131064, by rfl⟩ : syracuseStep 2841419 = 4262129) B4262129
theorem B7199563 : Blo 786339 7199563 := bstep (se 1 (by rfl) ⟨5399672, by rfl⟩ : syracuseStep 7199563 = 10799345) B10799345
theorem B1497943 : Blo 786339 1497943 := bstep (se 1 (by rfl) ⟨1123457, by rfl⟩ : syracuseStep 1497943 = 2246915) B2246915
theorem B3365725 : Blo 786339 3365725 := bstep (se 3 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 3365725 = 1262147) B1262147
theorem B4545629 : Blo 786339 4545629 := bstep (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) B1704611
theorem B842935 : Blo 786339 842935 := bstep (se 1 (by rfl) ⟨632201, by rfl⟩ : syracuseStep 842935 = 1264403) B1264403
theorem B6741427 : Blo 786339 6741427 := bstep (se 1 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 6741427 = 10112141) B10112141
theorem B1498763 : Blo 786339 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B1891991 : Blo 786339 1891991 := bstep (se 1 (by rfl) ⟨1418993, by rfl⟩ : syracuseStep 1891991 = 2837987) B2837987
theorem B1498817 : Blo 786339 1498817 := bstep (se 2 (by rfl) ⟨562056, by rfl⟩ : syracuseStep 1498817 = 1124113) B1124113
theorem B6381317 : Blo 786339 6381317 := bstep (se 4 (by rfl) ⟨598248, by rfl⟩ : syracuseStep 6381317 = 1196497) B1196497
theorem B843755 : Blo 786339 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B1794163 : Blo 786339 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B1597697 : Blo 786339 1597697 := bstep (se 2 (by rfl) ⟨599136, by rfl⟩ : syracuseStep 1597697 = 1198273) B1198273
theorem B3793169 : Blo 786339 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B4481345 : Blo 786339 4481345 := bstep (se 2 (by rfl) ⟨1680504, by rfl⟩ : syracuseStep 4481345 = 3361009) B3361009
theorem B11493733 : Blo 786339 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B1991243 : Blo 786339 1991243 := bstep (se 1 (by rfl) ⟨1493432, by rfl⟩ : syracuseStep 1991243 = 2986865) B2986865
theorem B1499735 : Blo 786339 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B1598105 : Blo 786339 1598105 := bstep (se 2 (by rfl) ⟨599289, by rfl⟩ : syracuseStep 1598105 = 1198579) B1198579
theorem B3596993 : Blo 786339 3596993 := bstep (se 2 (by rfl) ⟨1348872, by rfl⟩ : syracuseStep 3596993 = 2697745) B2697745
theorem B8971073 : Blo 786339 8971073 := bstep (se 2 (by rfl) ⟨3364152, by rfl⟩ : syracuseStep 8971073 = 6728305) B6728305
theorem B3466115 : Blo 786339 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B5694425 : Blo 786339 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B3990545 : Blo 786339 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B1500275 : Blo 786339 1500275 := bstep (se 1 (by rfl) ⟨1125206, by rfl⟩ : syracuseStep 1500275 = 2250413) B2250413
theorem B3990707 : Blo 786339 3990707 := bstep (se 1 (by rfl) ⟨2993030, by rfl⟩ : syracuseStep 3990707 = 5986061) B5986061
theorem B1598899 : Blo 786339 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1992215 : Blo 786339 1992215 := bstep (se 1 (by rfl) ⟨1494161, by rfl⟩ : syracuseStep 1992215 = 2988323) B2988323
theorem B5990435 : Blo 786339 5990435 := bstep (se 1 (by rfl) ⟨4492826, by rfl⟩ : syracuseStep 5990435 = 8985653) B8985653
theorem B1992883 : Blo 786339 1992883 := bstep (se 1 (by rfl) ⟨1494662, by rfl⟩ : syracuseStep 1992883 = 2989325) B2989325
theorem B5695667 : Blo 786339 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B1993025 : Blo 786339 1993025 := bstep (se 2 (by rfl) ⟨747384, by rfl⟩ : syracuseStep 1993025 = 1494769) B1494769
theorem B3795265 : Blo 786339 3795265 := bstep (se 2 (by rfl) ⟨1423224, by rfl⟩ : syracuseStep 3795265 = 2846449) B2846449
theorem B3369347 : Blo 786339 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B1010263 : Blo 786339 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B1895489 : Blo 786339 1895489 := bstep (se 2 (by rfl) ⟨710808, by rfl⟩ : syracuseStep 1895489 = 1421617) B1421617
theorem B3992651 : Blo 786339 3992651 := bstep (se 1 (by rfl) ⟨2994488, by rfl⟩ : syracuseStep 3992651 = 5988977) B5988977
theorem B7203941 : Blo 786339 7203941 := bstep (se 4 (by rfl) ⟨675369, by rfl⟩ : syracuseStep 7203941 = 1350739) B1350739
theorem B19721477 : Blo 786339 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B1994291 : Blo 786339 1994291 := bstep (se 1 (by rfl) ⟨1495718, by rfl⟩ : syracuseStep 1994291 = 2991437) B2991437
theorem B13463171 : Blo 786339 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B5762765 : Blo 786339 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B4255553 : Blo 786339 4255553 := bstep (se 2 (by rfl) ⟨1595832, by rfl⟩ : syracuseStep 4255553 = 3191665) B3191665
theorem B2846609 : Blo 786339 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B1994827 : Blo 786339 1994827 := bstep (se 1 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 1994827 = 2992241) B2992241
theorem B2912345 : Blo 786339 2912345 := bstep (se 2 (by rfl) ⟨1092129, by rfl⟩ : syracuseStep 2912345 = 2184259) B2184259
theorem B3371159 : Blo 786339 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B2519219 : Blo 786339 2519219 := bstep (se 1 (by rfl) ⟨1889414, by rfl⟩ : syracuseStep 2519219 = 3778829) B3778829
theorem B1994969 : Blo 786339 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B20181635 : Blo 786339 20181635 := bstep (se 1 (by rfl) ⟨15136226, by rfl⟩ : syracuseStep 20181635 = 30272453) B30272453
theorem B19690189 : Blo 786339 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B20247245 : Blo 786339 20247245 := bstep (se 3 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 20247245 = 7592717) B7592717
theorem B3994433 : Blo 786339 3994433 := bstep (se 2 (by rfl) ⟨1497912, by rfl⟩ : syracuseStep 3994433 = 2995825) B2995825
theorem B1995799 : Blo 786339 1995799 := bstep (se 1 (by rfl) ⟨1496849, by rfl⟩ : syracuseStep 1995799 = 2993699) B2993699
theorem B6583427 : Blo 786339 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B1799347 : Blo 786339 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B1996235 : Blo 786339 1996235 := bstep (se 1 (by rfl) ⟨1497176, by rfl⟩ : syracuseStep 1996235 = 2994353) B2994353
theorem B3372491 : Blo 786339 3372491 := bstep (se 1 (by rfl) ⟨2529368, by rfl⟩ : syracuseStep 3372491 = 5058737) B5058737
theorem B1996609 : Blo 786339 1996609 := bstep (se 2 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 1996609 = 1497457) B1497457
theorem B4257629 : Blo 786339 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B2127833 : Blo 786339 2127833 := bstep (se 2 (by rfl) ⟨797937, by rfl⟩ : syracuseStep 2127833 = 1595875) B1595875
theorem B6387673 : Blo 786339 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B3373073 : Blo 786339 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B1898585 : Blo 786339 1898585 := bstep (se 2 (by rfl) ⟨711969, by rfl⟩ : syracuseStep 1898585 = 1423939) B1423939
theorem B1997207 : Blo 786339 1997207 := bstep (se 1 (by rfl) ⟨1497905, by rfl⟩ : syracuseStep 1997207 = 2995811) B2995811
theorem B1440371 : Blo 786339 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B1702529 : Blo 786339 1702529 := bstep (se 2 (by rfl) ⟨638448, by rfl⟩ : syracuseStep 1702529 = 1276897) B1276897
theorem B3996377 : Blo 786339 3996377 := bstep (se 2 (by rfl) ⟨1498641, by rfl⟩ : syracuseStep 3996377 = 2997283) B2997283
theorem B3374131 : Blo 786339 3374131 := bstep (se 1 (by rfl) ⟨2530598, by rfl⟩ : syracuseStep 3374131 = 5061197) B5061197
theorem B1080409 : Blo 786339 1080409 := bstep (se 2 (by rfl) ⟨405153, by rfl⟩ : syracuseStep 1080409 = 810307) B810307
theorem B1998017 : Blo 786339 1998017 := bstep (se 2 (by rfl) ⟨749256, by rfl⟩ : syracuseStep 1998017 = 1498513) B1498513
theorem B5995781 : Blo 786339 5995781 := bstep (se 4 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 5995781 = 1124209) B1124209
theorem B1998553 : Blo 786339 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B1769291 : Blo 786339 1769291 := bstep (se 1 (by rfl) ⟨1326968, by rfl⟩ : syracuseStep 1769291 = 2653937) B2653937
theorem B2654045 : Blo 786339 2654045 := bstep (se 3 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 2654045 = 995267) B995267
theorem B1769345 : Blo 786339 1769345 := bstep (se 2 (by rfl) ⟨663504, by rfl⟩ : syracuseStep 1769345 = 1327009) B1327009
theorem B4489091 : Blo 786339 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B1179545 : Blo 786339 1179545 := bstep (se 2 (by rfl) ⟨442329, by rfl⟩ : syracuseStep 1179545 = 884659) B884659
theorem B786347 : Blo 786339 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B786359 : Blo 786339 786359 := bstep (se 1 (by rfl) ⟨589769, by rfl⟩ : syracuseStep 786359 = 1179539) B1179539
theorem B786379 : Blo 786339 786379 := bstep (se 1 (by rfl) ⟨589784, by rfl⟩ : syracuseStep 786379 = 1179569) B1179569
theorem B786391 : Blo 786339 786391 := bstep (se 1 (by rfl) ⟨589793, by rfl⟩ : syracuseStep 786391 = 1179587) B1179587
theorem B884695 : Blo 786339 884695 := bstep (se 1 (by rfl) ⟨663521, by rfl⟩ : syracuseStep 884695 = 1327043) B1327043
theorem B786411 : Blo 786339 786411 := bstep (se 1 (by rfl) ⟨589808, by rfl⟩ : syracuseStep 786411 = 1179617) B1179617
theorem B786423 : Blo 786339 786423 := bstep (se 1 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 786423 = 1179635) B1179635
theorem B786439 : Blo 786339 786439 := bstep (se 1 (by rfl) ⟨589829, by rfl⟩ : syracuseStep 786439 = 1179659) B1179659
theorem B786447 : Blo 786339 786447 := bstep (se 1 (by rfl) ⟨589835, by rfl⟩ : syracuseStep 786447 = 1179671) B1179671
theorem B1179707 : Blo 786339 1179707 := bstep (se 1 (by rfl) ⟨884780, by rfl⟩ : syracuseStep 1179707 = 1769561) B1769561
theorem B786491 : Blo 786339 786491 := bstep (se 1 (by rfl) ⟨589868, by rfl⟩ : syracuseStep 786491 = 1179737) B1179737
theorem B1179767 : Blo 786339 1179767 := bstep (se 1 (by rfl) ⟨884825, by rfl⟩ : syracuseStep 1179767 = 1769651) B1769651
theorem B786567 : Blo 786339 786567 := bstep (se 1 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 786567 = 1179851) B1179851
theorem B1179791 : Blo 786339 1179791 := bstep (se 1 (by rfl) ⟨884843, by rfl⟩ : syracuseStep 1179791 = 1769687) B1769687
theorem B786575 : Blo 786339 786575 := bstep (se 1 (by rfl) ⟨589931, by rfl⟩ : syracuseStep 786575 = 1179863) B1179863
theorem B2392217 : Blo 786339 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B1179833 : Blo 786339 1179833 := bstep (se 2 (by rfl) ⟨442437, by rfl⟩ : syracuseStep 1179833 = 884875) B884875
theorem B786619 : Blo 786339 786619 := bstep (se 1 (by rfl) ⟨589964, by rfl⟩ : syracuseStep 786619 = 1179929) B1179929
theorem B3375361 : Blo 786339 3375361 := bstep (se 2 (by rfl) ⟨1265760, by rfl⟩ : syracuseStep 3375361 = 2531521) B2531521
theorem B1179911 : Blo 786339 1179911 := bstep (se 1 (by rfl) ⟨884933, by rfl⟩ : syracuseStep 1179911 = 1769867) B1769867
theorem B786695 : Blo 786339 786695 := bstep (se 1 (by rfl) ⟨590021, by rfl⟩ : syracuseStep 786695 = 1180043) B1180043
theorem B786703 : Blo 786339 786703 := bstep (se 1 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 786703 = 1180055) B1180055
theorem B1179947 : Blo 786339 1179947 := bstep (se 1 (by rfl) ⟨884960, by rfl⟩ : syracuseStep 1179947 = 1769921) B1769921
theorem B786747 : Blo 786339 786747 := bstep (se 1 (by rfl) ⟨590060, by rfl⟩ : syracuseStep 786747 = 1180121) B1180121
theorem B1179977 : Blo 786339 1179977 := bstep (se 2 (by rfl) ⟨442491, by rfl⟩ : syracuseStep 1179977 = 884983) B884983
theorem B885127 : Blo 786339 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B786823 : Blo 786339 786823 := bstep (se 1 (by rfl) ⟨590117, by rfl⟩ : syracuseStep 786823 = 1180235) B1180235
theorem B786831 : Blo 786339 786831 := bstep (se 1 (by rfl) ⟨590123, by rfl⟩ : syracuseStep 786831 = 1180247) B1180247
theorem B38306195 : Blo 786339 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B1180091 : Blo 786339 1180091 := bstep (se 1 (by rfl) ⟨885068, by rfl⟩ : syracuseStep 1180091 = 1770137) B1770137
theorem B786875 : Blo 786339 786875 := bstep (se 1 (by rfl) ⟨590156, by rfl⟩ : syracuseStep 786875 = 1180313) B1180313
theorem B6717917 : Blo 786339 6717917 := bstep (se 3 (by rfl) ⟨1259609, by rfl⟩ : syracuseStep 6717917 = 2519219) B2519219
theorem B1180151 : Blo 786339 1180151 := bstep (se 1 (by rfl) ⟨885113, by rfl⟩ : syracuseStep 1180151 = 1770227) B1770227
theorem B786951 : Blo 786339 786951 := bstep (se 1 (by rfl) ⟨590213, by rfl⟩ : syracuseStep 786951 = 1180427) B1180427
theorem B1180175 : Blo 786339 1180175 := bstep (se 1 (by rfl) ⟨885131, by rfl⟩ : syracuseStep 1180175 = 1770263) B1770263
theorem B786959 : Blo 786339 786959 := bstep (se 1 (by rfl) ⟨590219, by rfl⟩ : syracuseStep 786959 = 1180439) B1180439
theorem B1180217 : Blo 786339 1180217 := bstep (se 2 (by rfl) ⟨442581, by rfl⟩ : syracuseStep 1180217 = 885163) B885163
theorem B885307 : Blo 786339 885307 := bstep (se 1 (by rfl) ⟨663980, by rfl⟩ : syracuseStep 885307 = 1327961) B1327961
theorem B787003 : Blo 786339 787003 := bstep (se 1 (by rfl) ⟨590252, by rfl⟩ : syracuseStep 787003 = 1180505) B1180505
theorem B1999475 : Blo 786339 1999475 := bstep (se 1 (by rfl) ⟨1499606, by rfl⟩ : syracuseStep 1999475 = 2999213) B2999213
theorem B1770119 : Blo 786339 1770119 := bstep (se 1 (by rfl) ⟨1327589, by rfl⟩ : syracuseStep 1770119 = 2655179) B2655179
theorem B1180295 : Blo 786339 1180295 := bstep (se 1 (by rfl) ⟨885221, by rfl⟩ : syracuseStep 1180295 = 1770443) B1770443
theorem B787079 : Blo 786339 787079 := bstep (se 1 (by rfl) ⟨590309, by rfl⟩ : syracuseStep 787079 = 1180619) B1180619
theorem B787087 : Blo 786339 787087 := bstep (se 1 (by rfl) ⟨590315, by rfl⟩ : syracuseStep 787087 = 1180631) B1180631
theorem B1180331 : Blo 786339 1180331 := bstep (se 1 (by rfl) ⟨885248, by rfl⟩ : syracuseStep 1180331 = 1770497) B1770497
theorem B787131 : Blo 786339 787131 := bstep (se 1 (by rfl) ⟨590348, by rfl⟩ : syracuseStep 787131 = 1180697) B1180697
theorem B1180361 : Blo 786339 1180361 := bstep (se 2 (by rfl) ⟨442635, by rfl⟩ : syracuseStep 1180361 = 885271) B885271
theorem B787207 : Blo 786339 787207 := bstep (se 1 (by rfl) ⟨590405, by rfl⟩ : syracuseStep 787207 = 1180811) B1180811
theorem B787215 : Blo 786339 787215 := bstep (se 1 (by rfl) ⟨590411, by rfl⟩ : syracuseStep 787215 = 1180823) B1180823
theorem B1770299 : Blo 786339 1770299 := bstep (se 1 (by rfl) ⟨1327724, by rfl⟩ : syracuseStep 1770299 = 2655449) B2655449
theorem B1180475 : Blo 786339 1180475 := bstep (se 1 (by rfl) ⟨885356, by rfl⟩ : syracuseStep 1180475 = 1770713) B1770713
theorem B787259 : Blo 786339 787259 := bstep (se 1 (by rfl) ⟨590444, by rfl⟩ : syracuseStep 787259 = 1180889) B1180889
theorem B1180535 : Blo 786339 1180535 := bstep (se 1 (by rfl) ⟨885401, by rfl⟩ : syracuseStep 1180535 = 1770803) B1770803
theorem B787335 : Blo 786339 787335 := bstep (se 1 (by rfl) ⟨590501, by rfl⟩ : syracuseStep 787335 = 1181003) B1181003
theorem B1180559 : Blo 786339 1180559 := bstep (se 1 (by rfl) ⟨885419, by rfl⟩ : syracuseStep 1180559 = 1770839) B1770839
theorem B787343 : Blo 786339 787343 := bstep (se 1 (by rfl) ⟨590507, by rfl⟩ : syracuseStep 787343 = 1181015) B1181015
theorem B1770425 : Blo 786339 1770425 := bstep (se 2 (by rfl) ⟨663909, by rfl⟩ : syracuseStep 1770425 = 1327819) B1327819
theorem B1180601 : Blo 786339 1180601 := bstep (se 2 (by rfl) ⟨442725, by rfl⟩ : syracuseStep 1180601 = 885451) B885451
theorem B787387 : Blo 786339 787387 := bstep (se 1 (by rfl) ⟨590540, by rfl⟩ : syracuseStep 787387 = 1181081) B1181081
theorem B1180679 : Blo 786339 1180679 := bstep (se 1 (by rfl) ⟨885509, by rfl⟩ : syracuseStep 1180679 = 1771019) B1771019
theorem B787463 : Blo 786339 787463 := bstep (se 1 (by rfl) ⟨590597, by rfl⟩ : syracuseStep 787463 = 1181195) B1181195
theorem B885775 : Blo 786339 885775 := bstep (se 1 (by rfl) ⟨664331, by rfl⟩ : syracuseStep 885775 = 1328663) B1328663
theorem B787471 : Blo 786339 787471 := bstep (se 1 (by rfl) ⟨590603, by rfl⟩ : syracuseStep 787471 = 1181207) B1181207
theorem B1180715 : Blo 786339 1180715 := bstep (se 1 (by rfl) ⟨885536, by rfl⟩ : syracuseStep 1180715 = 1771073) B1771073
theorem B787515 : Blo 786339 787515 := bstep (se 1 (by rfl) ⟨590636, by rfl⟩ : syracuseStep 787515 = 1181273) B1181273
theorem B1180745 : Blo 786339 1180745 := bstep (se 2 (by rfl) ⟨442779, by rfl⟩ : syracuseStep 1180745 = 885559) B885559
theorem B3998807 : Blo 786339 3998807 := bstep (se 1 (by rfl) ⟨2999105, by rfl⟩ : syracuseStep 3998807 = 5998211) B5998211
theorem B1999991 : Blo 786339 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B787591 : Blo 786339 787591 := bstep (se 1 (by rfl) ⟨590693, by rfl⟩ : syracuseStep 787591 = 1181387) B1181387
theorem B787599 : Blo 786339 787599 := bstep (se 1 (by rfl) ⟨590699, by rfl⟩ : syracuseStep 787599 = 1181399) B1181399
theorem B1180859 : Blo 786339 1180859 := bstep (se 1 (by rfl) ⟨885644, by rfl⟩ : syracuseStep 1180859 = 1771289) B1771289
theorem B787643 : Blo 786339 787643 := bstep (se 1 (by rfl) ⟨590732, by rfl⟩ : syracuseStep 787643 = 1181465) B1181465
theorem B6161645 : Blo 786339 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B1180919 : Blo 786339 1180919 := bstep (se 1 (by rfl) ⟨885689, by rfl⟩ : syracuseStep 1180919 = 1771379) B1771379
theorem B787719 : Blo 786339 787719 := bstep (se 1 (by rfl) ⟨590789, by rfl⟩ : syracuseStep 787719 = 1181579) B1181579
theorem B2655503 : Blo 786339 2655503 := bstep (se 1 (by rfl) ⟨1991627, by rfl⟩ : syracuseStep 2655503 = 3983255) B3983255
theorem B1770767 : Blo 786339 1770767 := bstep (se 1 (by rfl) ⟨1328075, by rfl⟩ : syracuseStep 1770767 = 2656151) B2656151
theorem B1180943 : Blo 786339 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B787727 : Blo 786339 787727 := bstep (se 1 (by rfl) ⟨590795, by rfl⟩ : syracuseStep 787727 = 1181591) B1181591
theorem B1770785 : Blo 786339 1770785 := bstep (se 2 (by rfl) ⟨664044, by rfl⟩ : syracuseStep 1770785 = 1328089) B1328089
theorem B1180985 : Blo 786339 1180985 := bstep (se 2 (by rfl) ⟨442869, by rfl⟩ : syracuseStep 1180985 = 885739) B885739
theorem B787771 : Blo 786339 787771 := bstep (se 1 (by rfl) ⟨590828, by rfl⟩ : syracuseStep 787771 = 1181657) B1181657
theorem B2393431 : Blo 786339 2393431 := bstep (se 1 (by rfl) ⟨1795073, by rfl⟩ : syracuseStep 2393431 = 3590147) B3590147
theorem B1181063 : Blo 786339 1181063 := bstep (se 1 (by rfl) ⟨885797, by rfl⟩ : syracuseStep 1181063 = 1771595) B1771595
theorem B787847 : Blo 786339 787847 := bstep (se 1 (by rfl) ⟨590885, by rfl⟩ : syracuseStep 787847 = 1181771) B1181771
theorem B787855 : Blo 786339 787855 := bstep (se 1 (by rfl) ⟨590891, by rfl⟩ : syracuseStep 787855 = 1181783) B1181783
theorem B1181099 : Blo 786339 1181099 := bstep (se 1 (by rfl) ⟨885824, by rfl⟩ : syracuseStep 1181099 = 1771649) B1771649
theorem B787899 : Blo 786339 787899 := bstep (se 1 (by rfl) ⟨590924, by rfl⟩ : syracuseStep 787899 = 1181849) B1181849
theorem B1181129 : Blo 786339 1181129 := bstep (se 2 (by rfl) ⟨442923, by rfl⟩ : syracuseStep 1181129 = 885847) B885847
theorem B6489553 : Blo 786339 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B886279 : Blo 786339 886279 := bstep (se 1 (by rfl) ⟨664709, by rfl⟩ : syracuseStep 886279 = 1329419) B1329419
theorem B787975 : Blo 786339 787975 := bstep (se 1 (by rfl) ⟨590981, by rfl⟩ : syracuseStep 787975 = 1181963) B1181963
theorem B787983 : Blo 786339 787983 := bstep (se 1 (by rfl) ⟨590987, by rfl⟩ : syracuseStep 787983 = 1181975) B1181975
theorem B2655773 : Blo 786339 2655773 := bstep (se 3 (by rfl) ⟨497957, by rfl⟩ : syracuseStep 2655773 = 995915) B995915
theorem B1181243 : Blo 786339 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B788027 : Blo 786339 788027 := bstep (se 1 (by rfl) ⟨591020, by rfl⟩ : syracuseStep 788027 = 1182041) B1182041
theorem B3999293 : Blo 786339 3999293 := bstep (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) B1499735
theorem B1771127 : Blo 786339 1771127 := bstep (se 1 (by rfl) ⟨1328345, by rfl⟩ : syracuseStep 1771127 = 2656691) B2656691
theorem B1181303 : Blo 786339 1181303 := bstep (se 1 (by rfl) ⟨885977, by rfl⟩ : syracuseStep 1181303 = 1771955) B1771955
theorem B788103 : Blo 786339 788103 := bstep (se 1 (by rfl) ⟨591077, by rfl⟩ : syracuseStep 788103 = 1182155) B1182155
theorem B1181327 : Blo 786339 1181327 := bstep (se 1 (by rfl) ⟨885995, by rfl⟩ : syracuseStep 1181327 = 1771991) B1771991
theorem B788111 : Blo 786339 788111 := bstep (se 1 (by rfl) ⟨591083, by rfl⟩ : syracuseStep 788111 = 1182167) B1182167
theorem B1181369 : Blo 786339 1181369 := bstep (se 2 (by rfl) ⟨443013, by rfl⟩ : syracuseStep 1181369 = 886027) B886027
theorem B886459 : Blo 786339 886459 := bstep (se 1 (by rfl) ⟨664844, by rfl⟩ : syracuseStep 886459 = 1329689) B1329689
theorem B788155 : Blo 786339 788155 := bstep (se 1 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 788155 = 1182233) B1182233
theorem B1181447 : Blo 786339 1181447 := bstep (se 1 (by rfl) ⟨886085, by rfl⟩ : syracuseStep 1181447 = 1772171) B1772171
theorem B788231 : Blo 786339 788231 := bstep (se 1 (by rfl) ⟨591173, by rfl⟩ : syracuseStep 788231 = 1182347) B1182347
theorem B788239 : Blo 786339 788239 := bstep (se 1 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 788239 = 1182359) B1182359
theorem B1771307 : Blo 786339 1771307 := bstep (se 1 (by rfl) ⟨1328480, by rfl⟩ : syracuseStep 1771307 = 2656961) B2656961
theorem B1181483 : Blo 786339 1181483 := bstep (se 1 (by rfl) ⟨886112, by rfl⟩ : syracuseStep 1181483 = 1772225) B1772225
theorem B788283 : Blo 786339 788283 := bstep (se 1 (by rfl) ⟨591212, by rfl⟩ : syracuseStep 788283 = 1182425) B1182425
theorem B1181513 : Blo 786339 1181513 := bstep (se 2 (by rfl) ⟨443067, by rfl⟩ : syracuseStep 1181513 = 886135) B886135
theorem B788359 : Blo 786339 788359 := bstep (se 1 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 788359 = 1182539) B1182539
theorem B788367 : Blo 786339 788367 := bstep (se 1 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 788367 = 1182551) B1182551
theorem B2131865 : Blo 786339 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B1181627 : Blo 786339 1181627 := bstep (se 1 (by rfl) ⟨886220, by rfl⟩ : syracuseStep 1181627 = 1772441) B1772441
theorem B788411 : Blo 786339 788411 := bstep (se 1 (by rfl) ⟨591308, by rfl⟩ : syracuseStep 788411 = 1182617) B1182617
theorem B1181687 : Blo 786339 1181687 := bstep (se 1 (by rfl) ⟨886265, by rfl⟩ : syracuseStep 1181687 = 1772531) B1772531
theorem B788487 : Blo 786339 788487 := bstep (se 1 (by rfl) ⟨591365, by rfl⟩ : syracuseStep 788487 = 1182731) B1182731
theorem B1181711 : Blo 786339 1181711 := bstep (se 1 (by rfl) ⟨886283, by rfl⟩ : syracuseStep 1181711 = 1772567) B1772567
theorem B788495 : Blo 786339 788495 := bstep (se 1 (by rfl) ⟨591371, by rfl⟩ : syracuseStep 788495 = 1182743) B1182743
theorem B1181753 : Blo 786339 1181753 := bstep (se 2 (by rfl) ⟨443157, by rfl⟩ : syracuseStep 1181753 = 886315) B886315
theorem B788539 : Blo 786339 788539 := bstep (se 1 (by rfl) ⟨591404, by rfl⟩ : syracuseStep 788539 = 1182809) B1182809
theorem B1181831 : Blo 786339 1181831 := bstep (se 1 (by rfl) ⟨886373, by rfl⟩ : syracuseStep 1181831 = 1772747) B1772747
theorem B788615 : Blo 786339 788615 := bstep (se 1 (by rfl) ⟨591461, by rfl⟩ : syracuseStep 788615 = 1182923) B1182923
theorem B886927 : Blo 786339 886927 := bstep (se 1 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 886927 = 1330391) B1330391
theorem B788623 : Blo 786339 788623 := bstep (se 1 (by rfl) ⟨591467, by rfl⟩ : syracuseStep 788623 = 1182935) B1182935
theorem B1771667 : Blo 786339 1771667 := bstep (se 1 (by rfl) ⟨1328750, by rfl⟩ : syracuseStep 1771667 = 2657501) B2657501
theorem B1181867 : Blo 786339 1181867 := bstep (se 1 (by rfl) ⟨886400, by rfl⟩ : syracuseStep 1181867 = 1772801) B1772801
theorem B788667 : Blo 786339 788667 := bstep (se 1 (by rfl) ⟨591500, by rfl⟩ : syracuseStep 788667 = 1183001) B1183001
theorem B1771721 : Blo 786339 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B1181897 : Blo 786339 1181897 := bstep (se 2 (by rfl) ⟨443211, by rfl⟩ : syracuseStep 1181897 = 886423) B886423
theorem B788743 : Blo 786339 788743 := bstep (se 1 (by rfl) ⟨591557, by rfl⟩ : syracuseStep 788743 = 1183115) B1183115
theorem B788751 : Blo 786339 788751 := bstep (se 1 (by rfl) ⟨591563, by rfl⟩ : syracuseStep 788751 = 1183127) B1183127
theorem B1182011 : Blo 786339 1182011 := bstep (se 1 (by rfl) ⟨886508, by rfl⟩ : syracuseStep 1182011 = 1773017) B1773017
theorem B788795 : Blo 786339 788795 := bstep (se 1 (by rfl) ⟨591596, by rfl⟩ : syracuseStep 788795 = 1183193) B1183193
theorem B1182071 : Blo 786339 1182071 := bstep (se 1 (by rfl) ⟨886553, by rfl⟩ : syracuseStep 1182071 = 1773107) B1773107
theorem B2525575 : Blo 786339 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B788871 : Blo 786339 788871 := bstep (se 1 (by rfl) ⟨591653, by rfl⟩ : syracuseStep 788871 = 1183307) B1183307
theorem B1182095 : Blo 786339 1182095 := bstep (se 1 (by rfl) ⟨886571, by rfl⟩ : syracuseStep 1182095 = 1773143) B1773143
theorem B788879 : Blo 786339 788879 := bstep (se 1 (by rfl) ⟨591659, by rfl⟩ : syracuseStep 788879 = 1183319) B1183319
theorem B1182137 : Blo 786339 1182137 := bstep (se 2 (by rfl) ⟨443301, by rfl⟩ : syracuseStep 1182137 = 886603) B886603
theorem B788923 : Blo 786339 788923 := bstep (se 1 (by rfl) ⟨591692, by rfl⟩ : syracuseStep 788923 = 1183385) B1183385
theorem B1182215 : Blo 786339 1182215 := bstep (se 1 (by rfl) ⟨886661, by rfl⟩ : syracuseStep 1182215 = 1773323) B1773323
theorem B788999 : Blo 786339 788999 := bstep (se 1 (by rfl) ⟨591749, by rfl⟩ : syracuseStep 788999 = 1183499) B1183499
theorem B789007 : Blo 786339 789007 := bstep (se 1 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 789007 = 1183511) B1183511
theorem B1182251 : Blo 786339 1182251 := bstep (se 1 (by rfl) ⟨886688, by rfl⟩ : syracuseStep 1182251 = 1773377) B1773377
theorem B789051 : Blo 786339 789051 := bstep (se 1 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 789051 = 1183577) B1183577
theorem B1182281 : Blo 786339 1182281 := bstep (se 2 (by rfl) ⟨443355, by rfl⟩ : syracuseStep 1182281 = 886711) B886711
theorem B887431 : Blo 786339 887431 := bstep (se 1 (by rfl) ⟨665573, by rfl⟩ : syracuseStep 887431 = 1331147) B1331147
theorem B789127 : Blo 786339 789127 := bstep (se 1 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 789127 = 1183691) B1183691
theorem B789135 : Blo 786339 789135 := bstep (se 1 (by rfl) ⟨591851, by rfl⟩ : syracuseStep 789135 = 1183703) B1183703
theorem B1182395 : Blo 786339 1182395 := bstep (se 1 (by rfl) ⟨886796, by rfl⟩ : syracuseStep 1182395 = 1773593) B1773593
theorem B789179 : Blo 786339 789179 := bstep (se 1 (by rfl) ⟨591884, by rfl⟩ : syracuseStep 789179 = 1183769) B1183769
theorem B1182455 : Blo 786339 1182455 := bstep (se 1 (by rfl) ⟨886841, by rfl⟩ : syracuseStep 1182455 = 1773683) B1773683
theorem B789255 : Blo 786339 789255 := bstep (se 1 (by rfl) ⟨591941, by rfl⟩ : syracuseStep 789255 = 1183883) B1183883
theorem B1182479 : Blo 786339 1182479 := bstep (se 1 (by rfl) ⟨886859, by rfl⟩ : syracuseStep 1182479 = 1773719) B1773719
theorem B789263 : Blo 786339 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B1182521 : Blo 786339 1182521 := bstep (se 2 (by rfl) ⟨443445, by rfl⟩ : syracuseStep 1182521 = 886891) B886891
theorem B887611 : Blo 786339 887611 := bstep (se 1 (by rfl) ⟨665708, by rfl⟩ : syracuseStep 887611 = 1331417) B1331417
theorem B789307 : Blo 786339 789307 := bstep (se 1 (by rfl) ⟨591980, by rfl⟩ : syracuseStep 789307 = 1183961) B1183961
theorem B4787059 : Blo 786339 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1772423 : Blo 786339 1772423 := bstep (se 1 (by rfl) ⟨1329317, by rfl⟩ : syracuseStep 1772423 = 2658635) B2658635
theorem B1182599 : Blo 786339 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B789383 : Blo 786339 789383 := bstep (se 1 (by rfl) ⟨592037, by rfl⟩ : syracuseStep 789383 = 1184075) B1184075
theorem B789391 : Blo 786339 789391 := bstep (se 1 (by rfl) ⟨592043, by rfl⟩ : syracuseStep 789391 = 1184087) B1184087
theorem B2657177 : Blo 786339 2657177 := bstep (se 2 (by rfl) ⟨996441, by rfl⟩ : syracuseStep 2657177 = 1992883) B1992883
theorem B1182635 : Blo 786339 1182635 := bstep (se 1 (by rfl) ⟨886976, by rfl⟩ : syracuseStep 1182635 = 1773953) B1773953
theorem B789435 : Blo 786339 789435 := bstep (se 1 (by rfl) ⟨592076, by rfl⟩ : syracuseStep 789435 = 1184153) B1184153
theorem B1182665 : Blo 786339 1182665 := bstep (se 2 (by rfl) ⟨443499, by rfl⟩ : syracuseStep 1182665 = 886999) B886999
theorem B789511 : Blo 786339 789511 := bstep (se 1 (by rfl) ⟨592133, by rfl⟩ : syracuseStep 789511 = 1184267) B1184267
theorem B789519 : Blo 786339 789519 := bstep (se 1 (by rfl) ⟨592139, by rfl⟩ : syracuseStep 789519 = 1184279) B1184279
theorem B1772603 : Blo 786339 1772603 := bstep (se 1 (by rfl) ⟨1329452, by rfl⟩ : syracuseStep 1772603 = 2658905) B2658905
theorem B1182779 : Blo 786339 1182779 := bstep (se 1 (by rfl) ⟨887084, by rfl⟩ : syracuseStep 1182779 = 1774169) B1774169
theorem B789563 : Blo 786339 789563 := bstep (se 1 (by rfl) ⟨592172, by rfl⟩ : syracuseStep 789563 = 1184345) B1184345
theorem B1182839 : Blo 786339 1182839 := bstep (se 1 (by rfl) ⟨887129, by rfl⟩ : syracuseStep 1182839 = 1774259) B1774259
theorem B789639 : Blo 786339 789639 := bstep (se 1 (by rfl) ⟨592229, by rfl⟩ : syracuseStep 789639 = 1184459) B1184459
theorem B1182863 : Blo 786339 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B789647 : Blo 786339 789647 := bstep (se 1 (by rfl) ⟨592235, by rfl⟩ : syracuseStep 789647 = 1184471) B1184471
theorem B1772729 : Blo 786339 1772729 := bstep (se 2 (by rfl) ⟨664773, by rfl⟩ : syracuseStep 1772729 = 1329547) B1329547
theorem B1182905 : Blo 786339 1182905 := bstep (se 2 (by rfl) ⟨443589, by rfl⟩ : syracuseStep 1182905 = 887179) B887179
theorem B789691 : Blo 786339 789691 := bstep (se 1 (by rfl) ⟨592268, by rfl⟩ : syracuseStep 789691 = 1184537) B1184537
theorem B1182983 : Blo 786339 1182983 := bstep (se 1 (by rfl) ⟨887237, by rfl⟩ : syracuseStep 1182983 = 1774475) B1774475
theorem B789767 : Blo 786339 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B888079 : Blo 786339 888079 := bstep (se 1 (by rfl) ⟨666059, by rfl⟩ : syracuseStep 888079 = 1332119) B1332119
theorem B789775 : Blo 786339 789775 := bstep (se 1 (by rfl) ⟨592331, by rfl⟩ : syracuseStep 789775 = 1184663) B1184663
theorem B11373857 : Blo 786339 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B1183019 : Blo 786339 1183019 := bstep (se 1 (by rfl) ⟨887264, by rfl⟩ : syracuseStep 1183019 = 1774529) B1774529
theorem B4001075 : Blo 786339 4001075 := bstep (se 1 (by rfl) ⟨3000806, by rfl⟩ : syracuseStep 4001075 = 6001613) B6001613
theorem B789819 : Blo 786339 789819 := bstep (se 1 (by rfl) ⟨592364, by rfl⟩ : syracuseStep 789819 = 1184729) B1184729
theorem B1183049 : Blo 786339 1183049 := bstep (se 2 (by rfl) ⟨443643, by rfl⟩ : syracuseStep 1183049 = 887287) B887287
theorem B4787545 : Blo 786339 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B789895 : Blo 786339 789895 := bstep (se 1 (by rfl) ⟨592421, by rfl⟩ : syracuseStep 789895 = 1184843) B1184843
theorem B789903 : Blo 786339 789903 := bstep (se 1 (by rfl) ⟨592427, by rfl⟩ : syracuseStep 789903 = 1184855) B1184855
theorem B4492691 : Blo 786339 4492691 := bstep (se 1 (by rfl) ⟨3369518, by rfl⟩ : syracuseStep 4492691 = 6739037) B6739037
theorem B1183163 : Blo 786339 1183163 := bstep (se 1 (by rfl) ⟨887372, by rfl⟩ : syracuseStep 1183163 = 1774745) B1774745
theorem B789947 : Blo 786339 789947 := bstep (se 1 (by rfl) ⟨592460, by rfl⟩ : syracuseStep 789947 = 1184921) B1184921
theorem B1347017 : Blo 786339 1347017 := bstep (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) B1010263
theorem B1183223 : Blo 786339 1183223 := bstep (se 1 (by rfl) ⟨887417, by rfl⟩ : syracuseStep 1183223 = 1774835) B1774835
theorem B790023 : Blo 786339 790023 := bstep (se 1 (by rfl) ⟨592517, by rfl⟩ : syracuseStep 790023 = 1185035) B1185035
theorem B1773071 : Blo 786339 1773071 := bstep (se 1 (by rfl) ⟨1329803, by rfl⟩ : syracuseStep 1773071 = 2659607) B2659607
theorem B1183247 : Blo 786339 1183247 := bstep (se 1 (by rfl) ⟨887435, by rfl⟩ : syracuseStep 1183247 = 1774871) B1774871
theorem B790031 : Blo 786339 790031 := bstep (se 1 (by rfl) ⟨592523, by rfl⟩ : syracuseStep 790031 = 1185047) B1185047
theorem B1773089 : Blo 786339 1773089 := bstep (se 2 (by rfl) ⟨664908, by rfl⟩ : syracuseStep 1773089 = 1329817) B1329817
theorem B1150507 : Blo 786339 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B1183289 : Blo 786339 1183289 := bstep (se 2 (by rfl) ⟨443733, by rfl⟩ : syracuseStep 1183289 = 887467) B887467
theorem B790075 : Blo 786339 790075 := bstep (se 1 (by rfl) ⟨592556, by rfl⟩ : syracuseStep 790075 = 1185113) B1185113
theorem B2657879 : Blo 786339 2657879 := bstep (se 1 (by rfl) ⟨1993409, by rfl⟩ : syracuseStep 2657879 = 3986819) B3986819
theorem B4263511 : Blo 786339 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B1183367 : Blo 786339 1183367 := bstep (se 1 (by rfl) ⟨887525, by rfl⟩ : syracuseStep 1183367 = 1775051) B1775051
theorem B790151 : Blo 786339 790151 := bstep (se 1 (by rfl) ⟨592613, by rfl⟩ : syracuseStep 790151 = 1185227) B1185227
theorem B790159 : Blo 786339 790159 := bstep (se 1 (by rfl) ⟨592619, by rfl⟩ : syracuseStep 790159 = 1185239) B1185239
theorem B1183403 : Blo 786339 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B790203 : Blo 786339 790203 := bstep (se 1 (by rfl) ⟨592652, by rfl⟩ : syracuseStep 790203 = 1185305) B1185305
theorem B1183433 : Blo 786339 1183433 := bstep (se 2 (by rfl) ⟨443787, by rfl⟩ : syracuseStep 1183433 = 887575) B887575
theorem B14946049 : Blo 786339 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B54529793 : Blo 786339 54529793 := bstep (se 2 (by rfl) ⟨20448672, by rfl⟩ : syracuseStep 54529793 = 40897345) B40897345
theorem B888583 : Blo 786339 888583 := bstep (se 1 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 888583 = 1332875) B1332875
theorem B790279 : Blo 786339 790279 := bstep (se 1 (by rfl) ⟨592709, by rfl⟩ : syracuseStep 790279 = 1185419) B1185419
theorem B790287 : Blo 786339 790287 := bstep (se 1 (by rfl) ⟨592715, by rfl⟩ : syracuseStep 790287 = 1185431) B1185431
theorem B1183547 : Blo 786339 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B790331 : Blo 786339 790331 := bstep (se 1 (by rfl) ⟨592748, by rfl⟩ : syracuseStep 790331 = 1185497) B1185497
theorem B1773431 : Blo 786339 1773431 := bstep (se 1 (by rfl) ⟨1330073, by rfl⟩ : syracuseStep 1773431 = 2660147) B2660147
theorem B1183607 : Blo 786339 1183607 := bstep (se 1 (by rfl) ⟨887705, by rfl⟩ : syracuseStep 1183607 = 1775411) B1775411
theorem B4493191 : Blo 786339 4493191 := bstep (se 1 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 4493191 = 6739787) B6739787
theorem B1183631 : Blo 786339 1183631 := bstep (se 1 (by rfl) ⟨887723, by rfl⟩ : syracuseStep 1183631 = 1775447) B1775447
theorem B1183673 : Blo 786339 1183673 := bstep (se 2 (by rfl) ⟨443877, by rfl⟩ : syracuseStep 1183673 = 887755) B887755
theorem B888763 : Blo 786339 888763 := bstep (se 1 (by rfl) ⟨666572, by rfl⟩ : syracuseStep 888763 = 1333145) B1333145
theorem B1183751 : Blo 786339 1183751 := bstep (se 1 (by rfl) ⟨887813, by rfl⟩ : syracuseStep 1183751 = 1775627) B1775627
theorem B1773611 : Blo 786339 1773611 := bstep (se 1 (by rfl) ⟨1330208, by rfl⟩ : syracuseStep 1773611 = 2660417) B2660417
theorem B1183787 : Blo 786339 1183787 := bstep (se 1 (by rfl) ⟨887840, by rfl⟩ : syracuseStep 1183787 = 1775681) B1775681
theorem B2658365 : Blo 786339 2658365 := bstep (se 3 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 2658365 = 996887) B996887
theorem B1183817 : Blo 786339 1183817 := bstep (se 2 (by rfl) ⟨443931, by rfl⟩ : syracuseStep 1183817 = 887863) B887863
theorem B1183931 : Blo 786339 1183931 := bstep (se 1 (by rfl) ⟨887948, by rfl⟩ : syracuseStep 1183931 = 1775897) B1775897
theorem B1183991 : Blo 786339 1183991 := bstep (se 1 (by rfl) ⟨887993, by rfl⟩ : syracuseStep 1183991 = 1775987) B1775987
theorem B1184015 : Blo 786339 1184015 := bstep (se 1 (by rfl) ⟨888011, by rfl⟩ : syracuseStep 1184015 = 1776023) B1776023
theorem B1184057 : Blo 786339 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B1184135 : Blo 786339 1184135 := bstep (se 1 (by rfl) ⟨888101, by rfl⟩ : syracuseStep 1184135 = 1776203) B1776203
theorem B1773971 : Blo 786339 1773971 := bstep (se 1 (by rfl) ⟨1330478, by rfl⟩ : syracuseStep 1773971 = 2660957) B2660957
theorem B1184171 : Blo 786339 1184171 := bstep (se 1 (by rfl) ⟨888128, by rfl⟩ : syracuseStep 1184171 = 1776257) B1776257
theorem B1774025 : Blo 786339 1774025 := bstep (se 2 (by rfl) ⟨665259, by rfl⟩ : syracuseStep 1774025 = 1330519) B1330519
theorem B1184201 : Blo 786339 1184201 := bstep (se 2 (by rfl) ⟨444075, by rfl⟩ : syracuseStep 1184201 = 888151) B888151
theorem B1184315 : Blo 786339 1184315 := bstep (se 1 (by rfl) ⟨888236, by rfl⟩ : syracuseStep 1184315 = 1776473) B1776473
theorem B1184375 : Blo 786339 1184375 := bstep (se 1 (by rfl) ⟨888281, by rfl⟩ : syracuseStep 1184375 = 1776563) B1776563
theorem B1184399 : Blo 786339 1184399 := bstep (se 1 (by rfl) ⟨888299, by rfl⟩ : syracuseStep 1184399 = 1776599) B1776599
theorem B1184441 : Blo 786339 1184441 := bstep (se 2 (by rfl) ⟨444165, by rfl⟩ : syracuseStep 1184441 = 888331) B888331
theorem B1184519 : Blo 786339 1184519 := bstep (se 1 (by rfl) ⟨888389, by rfl⟩ : syracuseStep 1184519 = 1776779) B1776779
theorem B4789007 : Blo 786339 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1184555 : Blo 786339 1184555 := bstep (se 1 (by rfl) ⟨888416, by rfl⟩ : syracuseStep 1184555 = 1776833) B1776833
theorem B1184585 : Blo 786339 1184585 := bstep (se 2 (by rfl) ⟨444219, by rfl⟩ : syracuseStep 1184585 = 888439) B888439
theorem B1184699 : Blo 786339 1184699 := bstep (se 1 (by rfl) ⟨888524, by rfl⟩ : syracuseStep 1184699 = 1777049) B1777049
theorem B1184759 : Blo 786339 1184759 := bstep (se 1 (by rfl) ⟨888569, by rfl⟩ : syracuseStep 1184759 = 1777139) B1777139
theorem B1184783 : Blo 786339 1184783 := bstep (se 1 (by rfl) ⟨888587, by rfl⟩ : syracuseStep 1184783 = 1777175) B1777175
theorem B7574573 : Blo 786339 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B1184825 : Blo 786339 1184825 := bstep (se 2 (by rfl) ⟨444309, by rfl⟩ : syracuseStep 1184825 = 888619) B888619
theorem B1774727 : Blo 786339 1774727 := bstep (se 1 (by rfl) ⟨1331045, by rfl⟩ : syracuseStep 1774727 = 2662091) B2662091
theorem B1184903 : Blo 786339 1184903 := bstep (se 1 (by rfl) ⟨888677, by rfl⟩ : syracuseStep 1184903 = 1777355) B1777355
theorem B1184939 : Blo 786339 1184939 := bstep (se 1 (by rfl) ⟨888704, by rfl⟩ : syracuseStep 1184939 = 1777409) B1777409
theorem B1184969 : Blo 786339 1184969 := bstep (se 2 (by rfl) ⟨444363, by rfl⟩ : syracuseStep 1184969 = 888727) B888727
theorem B1774907 : Blo 786339 1774907 := bstep (se 1 (by rfl) ⟨1331180, by rfl⟩ : syracuseStep 1774907 = 2662361) B2662361
theorem B1185083 : Blo 786339 1185083 := bstep (se 1 (by rfl) ⟨888812, by rfl⟩ : syracuseStep 1185083 = 1777625) B1777625
theorem B1185143 : Blo 786339 1185143 := bstep (se 1 (by rfl) ⟨888857, by rfl⟩ : syracuseStep 1185143 = 1777715) B1777715
theorem B1185167 : Blo 786339 1185167 := bstep (se 1 (by rfl) ⟨888875, by rfl⟩ : syracuseStep 1185167 = 1777751) B1777751
theorem B2659769 : Blo 786339 2659769 := bstep (se 2 (by rfl) ⟨997413, by rfl⟩ : syracuseStep 2659769 = 1994827) B1994827
theorem B1775033 : Blo 786339 1775033 := bstep (se 2 (by rfl) ⟨665637, by rfl⟩ : syracuseStep 1775033 = 1331275) B1331275
theorem B1185209 : Blo 786339 1185209 := bstep (se 2 (by rfl) ⟨444453, by rfl⟩ : syracuseStep 1185209 = 888907) B888907
theorem B4789763 : Blo 786339 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B1185287 : Blo 786339 1185287 := bstep (se 1 (by rfl) ⟨888965, by rfl⟩ : syracuseStep 1185287 = 1777931) B1777931
theorem B2987549 : Blo 786339 2987549 := bstep (se 3 (by rfl) ⟨560165, by rfl⟩ : syracuseStep 2987549 = 1120331) B1120331
theorem B2987563 : Blo 786339 2987563 := bstep (se 1 (by rfl) ⟨2240672, by rfl⟩ : syracuseStep 2987563 = 4481345) B4481345
theorem B1185323 : Blo 786339 1185323 := bstep (se 1 (by rfl) ⟨888992, by rfl⟩ : syracuseStep 1185323 = 1777985) B1777985
theorem B1185353 : Blo 786339 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B1185467 : Blo 786339 1185467 := bstep (se 1 (by rfl) ⟨889100, by rfl⟩ : syracuseStep 1185467 = 1778201) B1778201
theorem B1775375 : Blo 786339 1775375 := bstep (se 1 (by rfl) ⟨1331531, by rfl⟩ : syracuseStep 1775375 = 2663063) B2663063
theorem B1775393 : Blo 786339 1775393 := bstep (se 2 (by rfl) ⟨665772, by rfl⟩ : syracuseStep 1775393 = 1331545) B1331545
theorem B2397995 : Blo 786339 2397995 := bstep (se 1 (by rfl) ⟨1798496, by rfl⟩ : syracuseStep 2397995 = 3596993) B3596993
theorem B2660363 : Blo 786339 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B2660471 : Blo 786339 2660471 := bstep (se 1 (by rfl) ⟨1995353, by rfl⟩ : syracuseStep 2660471 = 3990707) B3990707
theorem B1775735 : Blo 786339 1775735 := bstep (se 1 (by rfl) ⟨1331801, by rfl⟩ : syracuseStep 1775735 = 2663603) B2663603
theorem B1775915 : Blo 786339 1775915 := bstep (se 1 (by rfl) ⟨1331936, by rfl⟩ : syracuseStep 1775915 = 2663873) B2663873
theorem B1776275 : Blo 786339 1776275 := bstep (se 1 (by rfl) ⟨1332206, by rfl⟩ : syracuseStep 1776275 = 2664413) B2664413
theorem B1120969 : Blo 786339 1120969 := bstep (se 2 (by rfl) ⟨420363, by rfl⟩ : syracuseStep 1120969 = 840727) B840727
theorem B2661065 : Blo 786339 2661065 := bstep (se 2 (by rfl) ⟨997899, by rfl⟩ : syracuseStep 2661065 = 1995799) B1995799
theorem B1776329 : Blo 786339 1776329 := bstep (se 2 (by rfl) ⟨666123, by rfl⟩ : syracuseStep 1776329 = 1332247) B1332247
theorem B2694023 : Blo 786339 2694023 := bstep (se 1 (by rfl) ⟨2020517, by rfl⟩ : syracuseStep 2694023 = 4041035) B4041035
theorem B2399129 : Blo 786339 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B2661767 : Blo 786339 2661767 := bstep (se 1 (by rfl) ⟨1996325, by rfl⟩ : syracuseStep 2661767 = 3992651) B3992651
theorem B1777031 : Blo 786339 1777031 := bstep (se 1 (by rfl) ⟨1332773, by rfl⟩ : syracuseStep 1777031 = 2665547) B2665547
theorem B13147651 : Blo 786339 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B1777211 : Blo 786339 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B1777337 : Blo 786339 1777337 := bstep (se 2 (by rfl) ⟨666501, by rfl⟩ : syracuseStep 1777337 = 1333003) B1333003
theorem B2662145 : Blo 786339 2662145 := bstep (se 2 (by rfl) ⟨998304, by rfl⟩ : syracuseStep 2662145 = 1996609) B1996609
theorem B3841843 : Blo 786339 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B2301755 : Blo 786339 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1777679 : Blo 786339 1777679 := bstep (se 1 (by rfl) ⟨1333259, by rfl⟩ : syracuseStep 1777679 = 2666519) B2666519
theorem B1777697 : Blo 786339 1777697 := bstep (se 2 (by rfl) ⟨666636, by rfl⟩ : syracuseStep 1777697 = 1333273) B1333273
theorem B1941563 : Blo 786339 1941563 := bstep (se 1 (by rfl) ⟨1456172, by rfl⟩ : syracuseStep 1941563 = 2912345) B2912345
theorem B2695457 : Blo 786339 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B1778039 : Blo 786339 1778039 := bstep (se 1 (by rfl) ⟨1333529, by rfl⟩ : syracuseStep 1778039 = 2667059) B2667059
theorem B2662955 : Blo 786339 2662955 := bstep (se 1 (by rfl) ⟨1997216, by rfl⟩ : syracuseStep 2662955 = 3994433) B3994433
theorem B1778219 : Blo 786339 1778219 := bstep (se 1 (by rfl) ⟨1333664, by rfl⟩ : syracuseStep 1778219 = 2667329) B2667329
theorem B5972939 : Blo 786339 5972939 := bstep (se 1 (by rfl) ⟨4479704, by rfl⟩ : syracuseStep 5972939 = 8959409) B8959409
theorem B1418555 : Blo 786339 1418555 := bstep (se 1 (by rfl) ⟨1063916, by rfl⟩ : syracuseStep 1418555 = 2127833) B2127833
theorem B4498841 : Blo 786339 4498841 := bstep (se 2 (by rfl) ⟨1687065, by rfl⟩ : syracuseStep 4498841 = 3374131) B3374131
theorem B1123913 : Blo 786339 1123913 := bstep (se 2 (by rfl) ⟨421467, by rfl⟩ : syracuseStep 1123913 = 842935) B842935
theorem B960247 : Blo 786339 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B2664251 : Blo 786339 2664251 := bstep (se 1 (by rfl) ⟨1998188, by rfl⟩ : syracuseStep 2664251 = 3996377) B3996377
theorem B8988569 : Blo 786339 8988569 := bstep (se 2 (by rfl) ⟨3370713, by rfl⟩ : syracuseStep 8988569 = 6741427) B6741427
theorem B2664737 : Blo 786339 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B1124779 : Blo 786339 1124779 := bstep (se 1 (by rfl) ⟨843584, by rfl⟩ : syracuseStep 1124779 = 1687169) B1687169
theorem B13445675 : Blo 786339 13445675 := bstep (se 1 (by rfl) ⟨10084256, by rfl⟩ : syracuseStep 13445675 = 20168513) B20168513
theorem B2992727 : Blo 786339 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B3779273 : Blo 786339 3779273 := bstep (se 2 (by rfl) ⟨1417227, by rfl⟩ : syracuseStep 3779273 = 2834455) B2834455
theorem B2665331 : Blo 786339 2665331 := bstep (se 1 (by rfl) ⟨1998998, by rfl⟩ : syracuseStep 2665331 = 3997997) B3997997
theorem B2993213 : Blo 786339 2993213 := bstep (se 3 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 2993213 = 1122455) B1122455
theorem B5680529 : Blo 786339 5680529 := bstep (se 2 (by rfl) ⟨2130198, by rfl⟩ : syracuseStep 5680529 = 4260397) B4260397
theorem B7581113 : Blo 786339 7581113 := bstep (se 2 (by rfl) ⟨2842917, by rfl⟩ : syracuseStep 7581113 = 5685835) B5685835
theorem B3780215 : Blo 786339 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B16428851 : Blo 786339 16428851 := bstep (se 1 (by rfl) ⟨12321638, by rfl⟩ : syracuseStep 16428851 = 24643277) B24643277
theorem B34090955 : Blo 786339 34090955 := bstep (se 1 (by rfl) ⟨25568216, by rfl⟩ : syracuseStep 34090955 = 51136433) B51136433
theorem B1683641 : Blo 786339 1683641 := bstep (se 2 (by rfl) ⟨631365, by rfl⟩ : syracuseStep 1683641 = 1262731) B1262731
theorem B995591 : Blo 786339 995591 := bstep (se 1 (by rfl) ⟨746693, by rfl⟩ : syracuseStep 995591 = 1493387) B1493387
theorem B2240855 : Blo 786339 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B2994641 : Blo 786339 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1683983 : Blo 786339 1683983 := bstep (se 1 (by rfl) ⟨1262987, by rfl⟩ : syracuseStep 1683983 = 2525975) B2525975
theorem B2241083 : Blo 786339 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B3191357 : Blo 786339 3191357 := bstep (se 3 (by rfl) ⟨598379, by rfl⟩ : syracuseStep 3191357 = 1196759) B1196759
theorem B2241209 : Blo 786339 2241209 := bstep (se 2 (by rfl) ⟨840453, by rfl⟩ : syracuseStep 2241209 = 1680907) B1680907
theorem B996239 : Blo 786339 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B1684871 : Blo 786339 1684871 := bstep (se 1 (by rfl) ⟨1263653, by rfl⟩ : syracuseStep 1684871 = 2527307) B2527307
theorem B6403475 : Blo 786339 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B5060353 : Blo 786339 5060353 := bstep (se 2 (by rfl) ⟨1897632, by rfl⟩ : syracuseStep 5060353 = 3795265) B3795265
theorem B800519 : Blo 786339 800519 := bstep (se 1 (by rfl) ⟨600389, by rfl⟩ : syracuseStep 800519 = 1200779) B1200779
theorem B1685281 : Blo 786339 1685281 := bstep (se 2 (by rfl) ⟨631980, by rfl⟩ : syracuseStep 1685281 = 1263961) B1263961
theorem B8533811 : Blo 786339 8533811 := bstep (se 1 (by rfl) ⟨6400358, by rfl⟩ : syracuseStep 8533811 = 12800717) B12800717
theorem B1423289 : Blo 786339 1423289 := bstep (se 2 (by rfl) ⟨533733, by rfl⟩ : syracuseStep 1423289 = 1067467) B1067467
theorem B2996311 : Blo 786339 2996311 := bstep (se 1 (by rfl) ⟨2247233, by rfl⟩ : syracuseStep 2996311 = 4494467) B4494467
theorem B1685623 : Blo 786339 1685623 := bstep (se 1 (by rfl) ⟨1264217, by rfl⟩ : syracuseStep 1685623 = 2528435) B2528435
theorem B5978285 : Blo 786339 5978285 := bstep (se 3 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 5978285 = 2241857) B2241857
theorem B2242849 : Blo 786339 2242849 := bstep (se 2 (by rfl) ⟨841068, by rfl⟩ : syracuseStep 2242849 = 1682137) B1682137
theorem B3782963 : Blo 786339 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B801083 : Blo 786339 801083 := bstep (se 1 (by rfl) ⟨600812, by rfl⟩ : syracuseStep 801083 = 1201625) B1201625
theorem B2308439 : Blo 786339 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B2996615 : Blo 786339 2996615 := bstep (se 1 (by rfl) ⟨2247461, by rfl⟩ : syracuseStep 2996615 = 4494923) B4494923
theorem B9583069 : Blo 786339 9583069 := bstep (se 3 (by rfl) ⟨1796825, by rfl⟩ : syracuseStep 9583069 = 3593651) B3593651
theorem B2996797 : Blo 786339 2996797 := bstep (se 3 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 2996797 = 1123799) B1123799
theorem B2275955 : Blo 786339 2275955 := bstep (se 1 (by rfl) ⟨1706966, by rfl⟩ : syracuseStep 2275955 = 3413933) B3413933
theorem B1063543 : Blo 786339 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B2243339 : Blo 786339 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B1686587 : Blo 786339 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B3587159 : Blo 786339 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B1686827 : Blo 786339 1686827 := bstep (se 1 (by rfl) ⟨1265120, by rfl⟩ : syracuseStep 1686827 = 2530241) B2530241
theorem B3030419 : Blo 786339 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B2244125 : Blo 786339 2244125 := bstep (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) B841547
theorem B8535581 : Blo 786339 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B1261327 : Blo 786339 1261327 := bstep (se 1 (by rfl) ⟨945995, by rfl⟩ : syracuseStep 1261327 = 1891991) B1891991
theorem B999211 : Blo 786339 999211 := bstep (se 1 (by rfl) ⟨749408, by rfl⟩ : syracuseStep 999211 = 1498817) B1498817
theorem B1687339 : Blo 786339 1687339 := bstep (se 1 (by rfl) ⟨1265504, by rfl⟩ : syracuseStep 1687339 = 2531009) B2531009
theorem B1065131 : Blo 786339 1065131 := bstep (se 1 (by rfl) ⟨798848, by rfl⟩ : syracuseStep 1065131 = 1597697) B1597697
theorem B2998529 : Blo 786339 2998529 := bstep (se 2 (by rfl) ⟨1124448, by rfl⟩ : syracuseStep 2998529 = 2248897) B2248897
theorem B1327495 : Blo 786339 1327495 := bstep (se 1 (by rfl) ⟨995621, by rfl⟩ : syracuseStep 1327495 = 1991243) B1991243
theorem B1065403 : Blo 786339 1065403 := bstep (se 1 (by rfl) ⟨799052, by rfl⟩ : syracuseStep 1065403 = 1598105) B1598105
theorem B5980715 : Blo 786339 5980715 := bstep (se 1 (by rfl) ⟨4485536, by rfl⟩ : syracuseStep 5980715 = 8971073) B8971073
theorem B2310743 : Blo 786339 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B3588727 : Blo 786339 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B1000183 : Blo 786339 1000183 := bstep (se 1 (by rfl) ⟨750137, by rfl⟩ : syracuseStep 1000183 = 1500275) B1500275
theorem B3982283 : Blo 786339 3982283 := bstep (se 1 (by rfl) ⟨2986712, by rfl⟩ : syracuseStep 3982283 = 5973425) B5973425
theorem B1328143 : Blo 786339 1328143 := bstep (se 1 (by rfl) ⟨996107, by rfl⟩ : syracuseStep 1328143 = 1992215) B1992215
theorem B3982607 : Blo 786339 3982607 := bstep (se 1 (by rfl) ⟨2986955, by rfl⟩ : syracuseStep 3982607 = 5973911) B5973911
theorem B2999699 : Blo 786339 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B1328683 : Blo 786339 1328683 := bstep (se 1 (by rfl) ⟨996512, by rfl⟩ : syracuseStep 1328683 = 1993025) B1993025
theorem B2246231 : Blo 786339 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B1328825 : Blo 786339 1328825 := bstep (se 2 (by rfl) ⟨498309, by rfl⟩ : syracuseStep 1328825 = 996619) B996619
theorem B3000199 : Blo 786339 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B1263659 : Blo 786339 1263659 := bstep (se 1 (by rfl) ⟨947744, by rfl⟩ : syracuseStep 1263659 = 1895489) B1895489
theorem B4802627 : Blo 786339 4802627 := bstep (se 1 (by rfl) ⟨3601970, by rfl⟩ : syracuseStep 4802627 = 7203941) B7203941
theorem B8407277 : Blo 786339 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B1329527 : Blo 786339 1329527 := bstep (se 1 (by rfl) ⟨997145, by rfl⟩ : syracuseStep 1329527 = 1994291) B1994291
theorem B2247097 : Blo 786339 2247097 := bstep (se 2 (by rfl) ⟨842661, by rfl⟩ : syracuseStep 2247097 = 1685323) B1685323
theorem B2279951 : Blo 786339 2279951 := bstep (se 1 (by rfl) ⟨1709963, by rfl⟩ : syracuseStep 2279951 = 3419927) B3419927
theorem B2837035 : Blo 786339 2837035 := bstep (se 1 (by rfl) ⟨2127776, by rfl⟩ : syracuseStep 2837035 = 4255553) B4255553
theorem B3984065 : Blo 786339 3984065 := bstep (se 2 (by rfl) ⟨1494024, by rfl⟩ : syracuseStep 3984065 = 2988049) B2988049
theorem B2247439 : Blo 786339 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B1329979 : Blo 786339 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B2018249 : Blo 786339 2018249 := bstep (se 2 (by rfl) ⟨756843, by rfl⟩ : syracuseStep 2018249 = 1513687) B1513687
theorem B1330121 : Blo 786339 1330121 := bstep (se 2 (by rfl) ⟨498795, by rfl⟩ : syracuseStep 1330121 = 997591) B997591
theorem B2247713 : Blo 786339 2247713 := bstep (se 2 (by rfl) ⟨842892, by rfl⟩ : syracuseStep 2247713 = 1685785) B1685785
theorem B13454423 : Blo 786339 13454423 := bstep (se 1 (by rfl) ⟨10090817, by rfl⟩ : syracuseStep 13454423 = 20181635) B20181635
theorem B4509073 : Blo 786339 4509073 := bstep (se 2 (by rfl) ⟨1690902, by rfl⟩ : syracuseStep 4509073 = 3381805) B3381805
theorem B10079747 : Blo 786339 10079747 := bstep (se 1 (by rfl) ⟨7559810, by rfl⟩ : syracuseStep 10079747 = 15119621) B15119621
theorem B1494587 : Blo 786339 1494587 := bstep (se 1 (by rfl) ⟨1120940, by rfl⟩ : syracuseStep 1494587 = 2241881) B2241881
theorem B1330823 : Blo 786339 1330823 := bstep (se 1 (by rfl) ⟨998117, by rfl⟩ : syracuseStep 1330823 = 1996235) B1996235
theorem B2248327 : Blo 786339 2248327 := bstep (se 1 (by rfl) ⟨1686245, by rfl⟩ : syracuseStep 2248327 = 3372491) B3372491
theorem B4050739 : Blo 786339 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B2838419 : Blo 786339 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B3985361 : Blo 786339 3985361 := bstep (se 2 (by rfl) ⟨1494510, by rfl⟩ : syracuseStep 3985361 = 2989021) B2989021
theorem B2248715 : Blo 786339 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B1495073 : Blo 786339 1495073 := bstep (se 2 (by rfl) ⟨560652, by rfl⟩ : syracuseStep 1495073 = 1121305) B1121305
theorem B1265723 : Blo 786339 1265723 := bstep (se 1 (by rfl) ⟨949292, by rfl⟩ : syracuseStep 1265723 = 1898585) B1898585
theorem B1331471 : Blo 786339 1331471 := bstep (se 1 (by rfl) ⟨998603, by rfl⟩ : syracuseStep 1331471 = 1997207) B1997207
theorem B1200457 : Blo 786339 1200457 := bstep (se 2 (by rfl) ⟨450171, by rfl⟩ : syracuseStep 1200457 = 900343) B900343
theorem B4051315 : Blo 786339 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B1495415 : Blo 786339 1495415 := bstep (se 1 (by rfl) ⟨1121561, by rfl⟩ : syracuseStep 1495415 = 2243123) B2243123
theorem B5755283 : Blo 786339 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B1135019 : Blo 786339 1135019 := bstep (se 1 (by rfl) ⟨851264, by rfl⟩ : syracuseStep 1135019 = 1702529) B1702529
theorem B8966699 : Blo 786339 8966699 := bstep (se 1 (by rfl) ⟨6725024, by rfl⟩ : syracuseStep 8966699 = 13450049) B13450049
theorem B3592961 : Blo 786339 3592961 := bstep (se 2 (by rfl) ⟨1347360, by rfl⟩ : syracuseStep 3592961 = 2694721) B2694721
theorem B1332011 : Blo 786339 1332011 := bstep (se 1 (by rfl) ⟨999008, by rfl⟩ : syracuseStep 1332011 = 1998017) B1998017
theorem B1332409 : Blo 786339 1332409 := bstep (se 2 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 1332409 = 999307) B999307
theorem B2250013 : Blo 786339 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B4871609 : Blo 786339 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B2250355 : Blo 786339 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B1889945 : Blo 786339 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B15324977 : Blo 786339 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B1333111 : Blo 786339 1333111 := bstep (se 1 (by rfl) ⟨999833, by rfl⟩ : syracuseStep 1333111 = 1999667) B1999667
theorem B2021267 : Blo 786339 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3594131 : Blo 786339 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1497017 : Blo 786339 1497017 := bstep (se 2 (by rfl) ⟨561381, by rfl⟩ : syracuseStep 1497017 = 1122763) B1122763
theorem B3987467 : Blo 786339 3987467 := bstep (se 1 (by rfl) ⟨2990600, by rfl⟩ : syracuseStep 3987467 = 5981201) B5981201
theorem B10115117 : Blo 786339 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B1333307 : Blo 786339 1333307 := bstep (se 1 (by rfl) ⟨999980, by rfl⟩ : syracuseStep 1333307 = 1999961) B1999961
theorem B3987629 : Blo 786339 3987629 := bstep (se 3 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 3987629 = 1495361) B1495361
theorem B1333519 : Blo 786339 1333519 := bstep (se 1 (by rfl) ⟨1000139, by rfl⟩ : syracuseStep 1333519 = 2000279) B2000279
theorem B1497359 : Blo 786339 1497359 := bstep (se 1 (by rfl) ⟨1123019, by rfl⟩ : syracuseStep 1497359 = 2246039) B2246039
theorem B7297465 : Blo 786339 7297465 := bstep (se 2 (by rfl) ⟨2736549, by rfl⟩ : syracuseStep 7297465 = 5473099) B5473099
theorem B13687339 : Blo 786339 13687339 := bstep (se 1 (by rfl) ⟨10265504, by rfl⟩ : syracuseStep 13687339 = 20531009) B20531009
theorem B1498171 : Blo 786339 1498171 := bstep (se 1 (by rfl) ⟨1123628, by rfl⟩ : syracuseStep 1498171 = 2247257) B2247257
theorem B1498247 : Blo 786339 1498247 := bstep (se 1 (by rfl) ⟨1123685, by rfl⟩ : syracuseStep 1498247 = 2247371) B2247371
theorem B48455171 : Blo 786339 48455171 := bstep (se 1 (by rfl) ⟨36341378, by rfl⟩ : syracuseStep 48455171 = 72682757) B72682757
theorem B1498657 : Blo 786339 1498657 := bstep (se 2 (by rfl) ⟨561996, by rfl⟩ : syracuseStep 1498657 = 1123993) B1123993
theorem B3366461 : Blo 786339 3366461 := bstep (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) B1262423
theorem B3989249 : Blo 786339 3989249 := bstep (se 2 (by rfl) ⟨1495968, by rfl⟩ : syracuseStep 3989249 = 2991937) B2991937
theorem B1990433 : Blo 786339 1990433 := bstep (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) B1492825
theorem B1597243 : Blo 786339 1597243 := bstep (se 1 (by rfl) ⟨1197932, by rfl⟩ : syracuseStep 1597243 = 2395865) B2395865
theorem B1498999 : Blo 786339 1498999 := bstep (se 1 (by rfl) ⟨1124249, by rfl⟩ : syracuseStep 1498999 = 2248499) B2248499
theorem B4481027 : Blo 786339 4481027 := bstep (se 1 (by rfl) ⟨3360770, by rfl⟩ : syracuseStep 4481027 = 6721541) B6721541
theorem B7561349 : Blo 786339 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B10215827 : Blo 786339 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B3990059 : Blo 786339 3990059 := bstep (se 1 (by rfl) ⟨2992544, by rfl⟩ : syracuseStep 3990059 = 5985089) B5985089
theorem B1991425 : Blo 786339 1991425 := bstep (se 2 (by rfl) ⟨746784, by rfl⟩ : syracuseStep 1991425 = 1493569) B1493569
theorem B14377817 : Blo 786339 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B105014341 : Blo 786339 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B5989463 : Blo 786339 5989463 := bstep (se 1 (by rfl) ⟨4492097, by rfl⟩ : syracuseStep 5989463 = 8984195) B8984195
theorem B1598735 : Blo 786339 1598735 := bstep (se 1 (by rfl) ⟨1199051, by rfl⟩ : syracuseStep 1598735 = 2398103) B2398103
theorem B16442657 : Blo 786339 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B1992023 : Blo 786339 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B1893817 : Blo 786339 1893817 := bstep (se 2 (by rfl) ⟨710181, by rfl⟩ : syracuseStep 1893817 = 1420363) B1420363
theorem B3368459 : Blo 786339 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B13493789 : Blo 786339 13493789 := bstep (se 3 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 13493789 = 5060171) B5060171
theorem B1992235 : Blo 786339 1992235 := bstep (se 1 (by rfl) ⟨1494176, by rfl⟩ : syracuseStep 1992235 = 2988353) B2988353
theorem B1992377 : Blo 786339 1992377 := bstep (se 2 (by rfl) ⟨747141, by rfl⟩ : syracuseStep 1992377 = 1494283) B1494283
theorem B3991355 : Blo 786339 3991355 := bstep (se 1 (by rfl) ⟨2993516, by rfl⟩ : syracuseStep 3991355 = 5987033) B5987033
theorem B1894259 : Blo 786339 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B1894279 : Blo 786339 1894279 := bstep (se 1 (by rfl) ⟨1420709, by rfl⟩ : syracuseStep 1894279 = 2841419) B2841419
theorem B3991517 : Blo 786339 3991517 := bstep (se 3 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 3991517 = 1496819) B1496819
theorem B2844733 : Blo 786339 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B3991841 : Blo 786339 3991841 := bstep (se 2 (by rfl) ⟨1496940, by rfl⟩ : syracuseStep 3991841 = 2993881) B2993881
theorem B4254211 : Blo 786339 4254211 := bstep (se 1 (by rfl) ⟨3190658, by rfl⟩ : syracuseStep 4254211 = 6381317) B6381317
theorem B7662109 : Blo 786339 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B1600033 : Blo 786339 1600033 := bstep (se 2 (by rfl) ⟨600012, by rfl⟩ : syracuseStep 1600033 = 1200025) B1200025
theorem B61565507 : Blo 786339 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B1993369 : Blo 786339 1993369 := bstep (se 2 (by rfl) ⟨747513, by rfl⟩ : syracuseStep 1993369 = 1495027) B1495027
theorem B1993531 : Blo 786339 1993531 := bstep (se 1 (by rfl) ⟨1495148, by rfl⟩ : syracuseStep 1993531 = 2990297) B2990297
theorem B1797011 : Blo 786339 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B1993673 : Blo 786339 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B3992813 : Blo 786339 3992813 := bstep (se 3 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 3992813 = 1497305) B1497305
theorem B1895681 : Blo 786339 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B1994017 : Blo 786339 1994017 := bstep (se 2 (by rfl) ⟨747756, by rfl⟩ : syracuseStep 1994017 = 1495513) B1495513
theorem B1600811 : Blo 786339 1600811 := bstep (se 1 (by rfl) ⟨1200608, by rfl⟩ : syracuseStep 1600811 = 2401217) B2401217
theorem B3796283 : Blo 786339 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B1994615 : Blo 786339 1994615 := bstep (se 1 (by rfl) ⟨1495961, by rfl⟩ : syracuseStep 1994615 = 2991923) B2991923
theorem B3993623 : Blo 786339 3993623 := bstep (se 1 (by rfl) ⟨2995217, by rfl⟩ : syracuseStep 3993623 = 5990435) B5990435
theorem B2125939 : Blo 786339 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B3797111 : Blo 786339 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B946447 : Blo 786339 946447 := bstep (se 1 (by rfl) ⟨709835, by rfl⟩ : syracuseStep 946447 = 1419671) B1419671
theorem B4485719 : Blo 786339 4485719 := bstep (se 1 (by rfl) ⟨3364289, by rfl⟩ : syracuseStep 4485719 = 6728579) B6728579
theorem B64713329 : Blo 786339 64713329 := bstep (se 2 (by rfl) ⟨24267498, by rfl⟩ : syracuseStep 64713329 = 48534997) B48534997
theorem B4256549 : Blo 786339 4256549 := bstep (se 4 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 4256549 = 798103) B798103
theorem B8975447 : Blo 786339 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B1995911 : Blo 786339 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B1995961 : Blo 786339 1995961 := bstep (se 2 (by rfl) ⟨748485, by rfl⟩ : syracuseStep 1995961 = 1496971) B1496971
theorem B1897739 : Blo 786339 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B2520335 : Blo 786339 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B8516897 : Blo 786339 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B2848135 : Blo 786339 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B23983685 : Blo 786339 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B1996559 : Blo 786339 1996559 := bstep (se 1 (by rfl) ⟨1497419, by rfl⟩ : syracuseStep 1996559 = 2994839) B2994839
theorem B3372833 : Blo 786339 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B13498163 : Blo 786339 13498163 := bstep (se 1 (by rfl) ⟨10123622, by rfl⟩ : syracuseStep 13498163 = 20247245) B20247245
theorem B4388951 : Blo 786339 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B2128187 : Blo 786339 2128187 := bstep (se 1 (by rfl) ⟨1596140, by rfl⟩ : syracuseStep 2128187 = 3192281) B3192281
theorem B14383507 : Blo 786339 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B9599417 : Blo 786339 9599417 := bstep (se 2 (by rfl) ⟨3599781, by rfl⟩ : syracuseStep 9599417 = 7199563) B7199563
theorem B1997257 : Blo 786339 1997257 := bstep (se 2 (by rfl) ⟨748971, by rfl⟩ : syracuseStep 1997257 = 1497943) B1497943
theorem B4487633 : Blo 786339 4487633 := bstep (se 2 (by rfl) ⟨1682862, by rfl⟩ : syracuseStep 4487633 = 3365725) B3365725
theorem B1997399 : Blo 786339 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B1440545 : Blo 786339 1440545 := bstep (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) B1080409
theorem B3996701 : Blo 786339 3996701 := bstep (se 3 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 3996701 = 1498763) B1498763
theorem B3997187 : Blo 786339 3997187 := bstep (se 1 (by rfl) ⟨2997890, by rfl⟩ : syracuseStep 3997187 = 5995781) B5995781
theorem B1179527 : Blo 786339 1179527 := bstep (se 1 (by rfl) ⟨884645, by rfl⟩ : syracuseStep 1179527 = 1769291) B1769291
theorem B1769363 : Blo 786339 1769363 := bstep (se 1 (by rfl) ⟨1327022, by rfl⟩ : syracuseStep 1769363 = 2654045) B2654045
theorem B2654099 : Blo 786339 2654099 := bstep (se 1 (by rfl) ⟨1990574, by rfl⟩ : syracuseStep 2654099 = 3981149) B3981149
theorem B13467545 : Blo 786339 13467545 := bstep (se 2 (by rfl) ⟨5050329, by rfl⟩ : syracuseStep 13467545 = 10100659) B10100659
theorem B1179563 : Blo 786339 1179563 := bstep (se 1 (by rfl) ⟨884672, by rfl⟩ : syracuseStep 1179563 = 1769345) B1769345
theorem B786363 : Blo 786339 786363 := bstep (se 1 (by rfl) ⟨589772, by rfl⟩ : syracuseStep 786363 = 1179545) B1179545
theorem B1179593 : Blo 786339 1179593 := bstep (se 2 (by rfl) ⟨442347, by rfl⟩ : syracuseStep 1179593 = 884695) B884695
theorem B1769417 : Blo 786339 1769417 := bstep (se 2 (by rfl) ⟨663531, by rfl⟩ : syracuseStep 1769417 = 1327063) B1327063
theorem B786471 : Blo 786339 786471 := bstep (se 1 (by rfl) ⟨589853, by rfl⟩ : syracuseStep 786471 = 1179707) B1179707
theorem B786511 : Blo 786339 786511 := bstep (se 1 (by rfl) ⟨589883, by rfl⟩ : syracuseStep 786511 = 1179767) B1179767
theorem B786527 : Blo 786339 786527 := bstep (se 1 (by rfl) ⟨589895, by rfl⟩ : syracuseStep 786527 = 1179791) B1179791
theorem B786555 : Blo 786339 786555 := bstep (se 1 (by rfl) ⟨589916, by rfl⟩ : syracuseStep 786555 = 1179833) B1179833
theorem B1999019 : Blo 786339 1999019 := bstep (se 1 (by rfl) ⟨1499264, by rfl⟩ : syracuseStep 1999019 = 2998529) B2998529
theorem B786607 : Blo 786339 786607 := bstep (se 1 (by rfl) ⟨589955, by rfl⟩ : syracuseStep 786607 = 1179911) B1179911
theorem B786631 : Blo 786339 786631 := bstep (se 1 (by rfl) ⟨589973, by rfl⟩ : syracuseStep 786631 = 1179947) B1179947
theorem B786651 : Blo 786339 786651 := bstep (se 1 (by rfl) ⟨589988, by rfl⟩ : syracuseStep 786651 = 1179977) B1179977
theorem B786727 : Blo 786339 786727 := bstep (se 1 (by rfl) ⟨590045, by rfl⟩ : syracuseStep 786727 = 1180091) B1180091
theorem B786767 : Blo 786339 786767 := bstep (se 1 (by rfl) ⟨590075, by rfl⟩ : syracuseStep 786767 = 1180151) B1180151
theorem B786783 : Blo 786339 786783 := bstep (se 1 (by rfl) ⟨590087, by rfl⟩ : syracuseStep 786783 = 1180175) B1180175
theorem B786811 : Blo 786339 786811 := bstep (se 1 (by rfl) ⟨590108, by rfl⟩ : syracuseStep 786811 = 1180217) B1180217
theorem B1540495 : Blo 786339 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B1180079 : Blo 786339 1180079 := bstep (se 1 (by rfl) ⟨885059, by rfl⟩ : syracuseStep 1180079 = 1770119) B1770119
theorem B786863 : Blo 786339 786863 := bstep (se 1 (by rfl) ⟨590147, by rfl⟩ : syracuseStep 786863 = 1180295) B1180295
theorem B786887 : Blo 786339 786887 := bstep (se 1 (by rfl) ⟨590165, by rfl⟩ : syracuseStep 786887 = 1180331) B1180331
theorem B786907 : Blo 786339 786907 := bstep (se 1 (by rfl) ⟨590180, by rfl⟩ : syracuseStep 786907 = 1180361) B1180361
theorem B1769993 : Blo 786339 1769993 := bstep (se 2 (by rfl) ⟨663747, by rfl⟩ : syracuseStep 1769993 = 1327495) B1327495
theorem B1180169 : Blo 786339 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B1180199 : Blo 786339 1180199 := bstep (se 1 (by rfl) ⟨885149, by rfl⟩ : syracuseStep 1180199 = 1770299) B1770299
theorem B786983 : Blo 786339 786983 := bstep (se 1 (by rfl) ⟨590237, by rfl⟩ : syracuseStep 786983 = 1180475) B1180475
theorem B787023 : Blo 786339 787023 := bstep (se 1 (by rfl) ⟨590267, by rfl⟩ : syracuseStep 787023 = 1180535) B1180535
theorem B787039 : Blo 786339 787039 := bstep (se 1 (by rfl) ⟨590279, by rfl⟩ : syracuseStep 787039 = 1180559) B1180559
theorem B1180283 : Blo 786339 1180283 := bstep (se 1 (by rfl) ⟨885212, by rfl⟩ : syracuseStep 1180283 = 1770425) B1770425
theorem B787067 : Blo 786339 787067 := bstep (se 1 (by rfl) ⟨590300, by rfl⟩ : syracuseStep 787067 = 1180601) B1180601
theorem B2654855 : Blo 786339 2654855 := bstep (se 1 (by rfl) ⟨1991141, by rfl⟩ : syracuseStep 2654855 = 3982283) B3982283
theorem B787119 : Blo 786339 787119 := bstep (se 1 (by rfl) ⟨590339, by rfl⟩ : syracuseStep 787119 = 1180679) B1180679
theorem B2654909 : Blo 786339 2654909 := bstep (se 3 (by rfl) ⟨497795, by rfl⟩ : syracuseStep 2654909 = 995591) B995591
theorem B787143 : Blo 786339 787143 := bstep (se 1 (by rfl) ⟨590357, by rfl⟩ : syracuseStep 787143 = 1180715) B1180715
theorem B787163 : Blo 786339 787163 := bstep (se 1 (by rfl) ⟨590372, by rfl⟩ : syracuseStep 787163 = 1180745) B1180745
theorem B1180409 : Blo 786339 1180409 := bstep (se 2 (by rfl) ⟨442653, by rfl⟩ : syracuseStep 1180409 = 885307) B885307
theorem B787239 : Blo 786339 787239 := bstep (se 1 (by rfl) ⟨590429, by rfl⟩ : syracuseStep 787239 = 1180859) B1180859
theorem B4784969 : Blo 786339 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B787279 : Blo 786339 787279 := bstep (se 1 (by rfl) ⟨590459, by rfl⟩ : syracuseStep 787279 = 1180919) B1180919
theorem B2655071 : Blo 786339 2655071 := bstep (se 1 (by rfl) ⟨1991303, by rfl⟩ : syracuseStep 2655071 = 3982607) B3982607
theorem B1770335 : Blo 786339 1770335 := bstep (se 1 (by rfl) ⟨1327751, by rfl⟩ : syracuseStep 1770335 = 2655503) B2655503
theorem B1180511 : Blo 786339 1180511 := bstep (se 1 (by rfl) ⟨885383, by rfl⟩ : syracuseStep 1180511 = 1770767) B1770767
theorem B787295 : Blo 786339 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B1180523 : Blo 786339 1180523 := bstep (se 1 (by rfl) ⟨885392, by rfl⟩ : syracuseStep 1180523 = 1770785) B1770785
theorem B787323 : Blo 786339 787323 := bstep (se 1 (by rfl) ⟨590492, by rfl⟩ : syracuseStep 787323 = 1180985) B1180985
theorem B787375 : Blo 786339 787375 := bstep (se 1 (by rfl) ⟨590531, by rfl⟩ : syracuseStep 787375 = 1181063) B1181063
theorem B1999799 : Blo 786339 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B787399 : Blo 786339 787399 := bstep (se 1 (by rfl) ⟨590549, by rfl⟩ : syracuseStep 787399 = 1181099) B1181099
theorem B787419 : Blo 786339 787419 := bstep (se 1 (by rfl) ⟨590564, by rfl⟩ : syracuseStep 787419 = 1181129) B1181129
theorem B2655233 : Blo 786339 2655233 := bstep (se 2 (by rfl) ⟨995712, by rfl⟩ : syracuseStep 2655233 = 1991425) B1991425
theorem B1770515 : Blo 786339 1770515 := bstep (se 1 (by rfl) ⟨1327886, by rfl⟩ : syracuseStep 1770515 = 2655773) B2655773
theorem B787495 : Blo 786339 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B1180751 : Blo 786339 1180751 := bstep (se 1 (by rfl) ⟨885563, by rfl⟩ : syracuseStep 1180751 = 1771127) B1771127
theorem B787535 : Blo 786339 787535 := bstep (se 1 (by rfl) ⟨590651, by rfl⟩ : syracuseStep 787535 = 1181303) B1181303
theorem B787551 : Blo 786339 787551 := bstep (se 1 (by rfl) ⟨590663, by rfl⟩ : syracuseStep 787551 = 1181327) B1181327
theorem B885883 : Blo 786339 885883 := bstep (se 1 (by rfl) ⟨664412, by rfl⟩ : syracuseStep 885883 = 1328825) B1328825
theorem B787579 : Blo 786339 787579 := bstep (se 1 (by rfl) ⟨590684, by rfl⟩ : syracuseStep 787579 = 1181369) B1181369
theorem B787631 : Blo 786339 787631 := bstep (se 1 (by rfl) ⟨590723, by rfl⟩ : syracuseStep 787631 = 1181447) B1181447
theorem B1180871 : Blo 786339 1180871 := bstep (se 1 (by rfl) ⟨885653, by rfl⟩ : syracuseStep 1180871 = 1771307) B1771307
theorem B787655 : Blo 786339 787655 := bstep (se 1 (by rfl) ⟨590741, by rfl⟩ : syracuseStep 787655 = 1181483) B1181483
theorem B787675 : Blo 786339 787675 := bstep (se 1 (by rfl) ⟨590756, by rfl⟩ : syracuseStep 787675 = 1181513) B1181513
theorem B787751 : Blo 786339 787751 := bstep (se 1 (by rfl) ⟨590813, by rfl⟩ : syracuseStep 787751 = 1181627) B1181627
theorem B787791 : Blo 786339 787791 := bstep (se 1 (by rfl) ⟨590843, by rfl⟩ : syracuseStep 787791 = 1181687) B1181687
theorem B787807 : Blo 786339 787807 := bstep (se 1 (by rfl) ⟨590855, by rfl⟩ : syracuseStep 787807 = 1181711) B1181711
theorem B1770857 : Blo 786339 1770857 := bstep (se 2 (by rfl) ⟨664071, by rfl⟩ : syracuseStep 1770857 = 1328143) B1328143
theorem B1181033 : Blo 786339 1181033 := bstep (se 2 (by rfl) ⟨442887, by rfl⟩ : syracuseStep 1181033 = 885775) B885775
theorem B787835 : Blo 786339 787835 := bstep (se 1 (by rfl) ⟨590876, by rfl⟩ : syracuseStep 787835 = 1181753) B1181753
theorem B5047717 : Blo 786339 5047717 := bstep (se 4 (by rfl) ⟨473223, by rfl⟩ : syracuseStep 5047717 = 946447) B946447
theorem B787887 : Blo 786339 787887 := bstep (se 1 (by rfl) ⟨590915, by rfl⟩ : syracuseStep 787887 = 1181831) B1181831
theorem B140019121 : Blo 786339 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B1181111 : Blo 786339 1181111 := bstep (se 1 (by rfl) ⟨885833, by rfl⟩ : syracuseStep 1181111 = 1771667) B1771667
theorem B787911 : Blo 786339 787911 := bstep (se 1 (by rfl) ⟨590933, by rfl⟩ : syracuseStep 787911 = 1181867) B1181867
theorem B1181147 : Blo 786339 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B787931 : Blo 786339 787931 := bstep (se 1 (by rfl) ⟨590948, by rfl⟩ : syracuseStep 787931 = 1181897) B1181897
theorem B5604851 : Blo 786339 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B788007 : Blo 786339 788007 := bstep (se 1 (by rfl) ⟨591005, by rfl⟩ : syracuseStep 788007 = 1182011) B1182011
theorem B886351 : Blo 786339 886351 := bstep (se 1 (by rfl) ⟨664763, by rfl⟩ : syracuseStep 886351 = 1329527) B1329527
theorem B788047 : Blo 786339 788047 := bstep (se 1 (by rfl) ⟨591035, by rfl⟩ : syracuseStep 788047 = 1182071) B1182071
theorem B788063 : Blo 786339 788063 := bstep (se 1 (by rfl) ⟨591047, by rfl⟩ : syracuseStep 788063 = 1182095) B1182095
theorem B788091 : Blo 786339 788091 := bstep (se 1 (by rfl) ⟨591068, by rfl⟩ : syracuseStep 788091 = 1182137) B1182137
theorem B788143 : Blo 786339 788143 := bstep (se 1 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 788143 = 1182215) B1182215
theorem B788167 : Blo 786339 788167 := bstep (se 1 (by rfl) ⟨591125, by rfl⟩ : syracuseStep 788167 = 1182251) B1182251
theorem B788187 : Blo 786339 788187 := bstep (se 1 (by rfl) ⟨591140, by rfl⟩ : syracuseStep 788187 = 1182281) B1182281
theorem B788263 : Blo 786339 788263 := bstep (se 1 (by rfl) ⟨591197, by rfl⟩ : syracuseStep 788263 = 1182395) B1182395
theorem B2656043 : Blo 786339 2656043 := bstep (se 1 (by rfl) ⟨1992032, by rfl⟩ : syracuseStep 2656043 = 3984065) B3984065
theorem B788303 : Blo 786339 788303 := bstep (se 1 (by rfl) ⟨591227, by rfl⟩ : syracuseStep 788303 = 1182455) B1182455
theorem B788319 : Blo 786339 788319 := bstep (se 1 (by rfl) ⟨591239, by rfl⟩ : syracuseStep 788319 = 1182479) B1182479
theorem B788347 : Blo 786339 788347 := bstep (se 1 (by rfl) ⟨591260, by rfl⟩ : syracuseStep 788347 = 1182521) B1182521
theorem B2525089 : Blo 786339 2525089 := bstep (se 2 (by rfl) ⟨946908, by rfl⟩ : syracuseStep 2525089 = 1893817) B1893817
theorem B1181615 : Blo 786339 1181615 := bstep (se 1 (by rfl) ⟨886211, by rfl⟩ : syracuseStep 1181615 = 1772423) B1772423
theorem B788399 : Blo 786339 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B1771451 : Blo 786339 1771451 := bstep (se 1 (by rfl) ⟨1328588, by rfl⟩ : syracuseStep 1771451 = 2657177) B2657177
theorem B8652737 : Blo 786339 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B788423 : Blo 786339 788423 := bstep (se 1 (by rfl) ⟨591317, by rfl⟩ : syracuseStep 788423 = 1182635) B1182635
theorem B1345499 : Blo 786339 1345499 := bstep (se 1 (by rfl) ⟨1009124, by rfl⟩ : syracuseStep 1345499 = 2018249) B2018249
theorem B886747 : Blo 786339 886747 := bstep (se 1 (by rfl) ⟨665060, by rfl⟩ : syracuseStep 886747 = 1330121) B1330121
theorem B788443 : Blo 786339 788443 := bstep (se 1 (by rfl) ⟨591332, by rfl⟩ : syracuseStep 788443 = 1182665) B1182665
theorem B1181705 : Blo 786339 1181705 := bstep (se 2 (by rfl) ⟨443139, by rfl⟩ : syracuseStep 1181705 = 886279) B886279
theorem B1181735 : Blo 786339 1181735 := bstep (se 1 (by rfl) ⟨886301, by rfl⟩ : syracuseStep 1181735 = 1772603) B1772603
theorem B788519 : Blo 786339 788519 := bstep (se 1 (by rfl) ⟨591389, by rfl⟩ : syracuseStep 788519 = 1182779) B1182779
theorem B2656313 : Blo 786339 2656313 := bstep (se 2 (by rfl) ⟨996117, by rfl⟩ : syracuseStep 2656313 = 1992235) B1992235
theorem B1771577 : Blo 786339 1771577 := bstep (se 2 (by rfl) ⟨664341, by rfl⟩ : syracuseStep 1771577 = 1328683) B1328683
theorem B788559 : Blo 786339 788559 := bstep (se 1 (by rfl) ⟨591419, by rfl⟩ : syracuseStep 788559 = 1182839) B1182839
theorem B788575 : Blo 786339 788575 := bstep (se 1 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 788575 = 1182863) B1182863
theorem B1181819 : Blo 786339 1181819 := bstep (se 1 (by rfl) ⟨886364, by rfl⟩ : syracuseStep 1181819 = 1772729) B1772729
theorem B788603 : Blo 786339 788603 := bstep (se 1 (by rfl) ⟨591452, by rfl⟩ : syracuseStep 788603 = 1182905) B1182905
theorem B788655 : Blo 786339 788655 := bstep (se 1 (by rfl) ⟨591491, by rfl⟩ : syracuseStep 788655 = 1182983) B1182983
theorem B788679 : Blo 786339 788679 := bstep (se 1 (by rfl) ⟨591509, by rfl⟩ : syracuseStep 788679 = 1183019) B1183019
theorem B788699 : Blo 786339 788699 := bstep (se 1 (by rfl) ⟨591524, by rfl⟩ : syracuseStep 788699 = 1183049) B1183049
theorem B1181945 : Blo 786339 1181945 := bstep (se 2 (by rfl) ⟨443229, by rfl⟩ : syracuseStep 1181945 = 886459) B886459
theorem B788775 : Blo 786339 788775 := bstep (se 1 (by rfl) ⟨591581, by rfl⟩ : syracuseStep 788775 = 1183163) B1183163
theorem B1280329 : Blo 786339 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B788815 : Blo 786339 788815 := bstep (se 1 (by rfl) ⟨591611, by rfl⟩ : syracuseStep 788815 = 1183223) B1183223
theorem B6719831 : Blo 786339 6719831 := bstep (se 1 (by rfl) ⟨5039873, by rfl⟩ : syracuseStep 6719831 = 10079747) B10079747
theorem B1182047 : Blo 786339 1182047 := bstep (se 1 (by rfl) ⟨886535, by rfl⟩ : syracuseStep 1182047 = 1773071) B1773071
theorem B788831 : Blo 786339 788831 := bstep (se 1 (by rfl) ⟨591623, by rfl⟩ : syracuseStep 788831 = 1183247) B1183247
theorem B1182059 : Blo 786339 1182059 := bstep (se 1 (by rfl) ⟨886544, by rfl⟩ : syracuseStep 1182059 = 1773089) B1773089
theorem B788859 : Blo 786339 788859 := bstep (se 1 (by rfl) ⟨591644, by rfl⟩ : syracuseStep 788859 = 1183289) B1183289
theorem B2656637 : Blo 786339 2656637 := bstep (se 3 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 2656637 = 996239) B996239
theorem B1771919 : Blo 786339 1771919 := bstep (se 1 (by rfl) ⟨1328939, by rfl⟩ : syracuseStep 1771919 = 2657879) B2657879
theorem B887215 : Blo 786339 887215 := bstep (se 1 (by rfl) ⟨665411, by rfl⟩ : syracuseStep 887215 = 1330823) B1330823
theorem B788911 : Blo 786339 788911 := bstep (se 1 (by rfl) ⟨591683, by rfl⟩ : syracuseStep 788911 = 1183367) B1183367
theorem B788935 : Blo 786339 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B788955 : Blo 786339 788955 := bstep (se 1 (by rfl) ⟨591716, by rfl⟩ : syracuseStep 788955 = 1183433) B1183433
theorem B2525705 : Blo 786339 2525705 := bstep (se 2 (by rfl) ⟨947139, by rfl⟩ : syracuseStep 2525705 = 1894279) B1894279
theorem B4000265 : Blo 786339 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B789031 : Blo 786339 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B1182287 : Blo 786339 1182287 := bstep (se 1 (by rfl) ⟨886715, by rfl⟩ : syracuseStep 1182287 = 1773431) B1773431
theorem B789071 : Blo 786339 789071 := bstep (se 1 (by rfl) ⟨591803, by rfl⟩ : syracuseStep 789071 = 1183607) B1183607
theorem B789087 : Blo 786339 789087 := bstep (se 1 (by rfl) ⟨591815, by rfl⟩ : syracuseStep 789087 = 1183631) B1183631
theorem B789115 : Blo 786339 789115 := bstep (se 1 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 789115 = 1183673) B1183673
theorem B2656907 : Blo 786339 2656907 := bstep (se 1 (by rfl) ⟨1992680, by rfl⟩ : syracuseStep 2656907 = 3985361) B3985361
theorem B789167 : Blo 786339 789167 := bstep (se 1 (by rfl) ⟨591875, by rfl⟩ : syracuseStep 789167 = 1183751) B1183751
theorem B1182407 : Blo 786339 1182407 := bstep (se 1 (by rfl) ⟨886805, by rfl⟩ : syracuseStep 1182407 = 1773611) B1773611
theorem B789191 : Blo 786339 789191 := bstep (se 1 (by rfl) ⟨591893, by rfl⟩ : syracuseStep 789191 = 1183787) B1183787
theorem B1772243 : Blo 786339 1772243 := bstep (se 1 (by rfl) ⟨1329182, by rfl⟩ : syracuseStep 1772243 = 2658365) B2658365
theorem B789211 : Blo 786339 789211 := bstep (se 1 (by rfl) ⟨591908, by rfl⟩ : syracuseStep 789211 = 1183817) B1183817
theorem B789287 : Blo 786339 789287 := bstep (se 1 (by rfl) ⟨591965, by rfl⟩ : syracuseStep 789287 = 1183931) B1183931
theorem B789327 : Blo 786339 789327 := bstep (se 1 (by rfl) ⟨591995, by rfl⟩ : syracuseStep 789327 = 1183991) B1183991
theorem B887647 : Blo 786339 887647 := bstep (se 1 (by rfl) ⟨665735, by rfl⟩ : syracuseStep 887647 = 1331471) B1331471
theorem B789343 : Blo 786339 789343 := bstep (se 1 (by rfl) ⟨592007, by rfl⟩ : syracuseStep 789343 = 1184015) B1184015
theorem B1182569 : Blo 786339 1182569 := bstep (se 2 (by rfl) ⟨443463, by rfl⟩ : syracuseStep 1182569 = 886927) B886927
theorem B789371 : Blo 786339 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B789423 : Blo 786339 789423 := bstep (se 1 (by rfl) ⟨592067, by rfl⟩ : syracuseStep 789423 = 1184135) B1184135
theorem B3836855 : Blo 786339 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B1182647 : Blo 786339 1182647 := bstep (se 1 (by rfl) ⟨886985, by rfl⟩ : syracuseStep 1182647 = 1773971) B1773971
theorem B789447 : Blo 786339 789447 := bstep (se 1 (by rfl) ⟨592085, by rfl⟩ : syracuseStep 789447 = 1184171) B1184171
theorem B1182683 : Blo 786339 1182683 := bstep (se 1 (by rfl) ⟨887012, by rfl⟩ : syracuseStep 1182683 = 1774025) B1774025
theorem B789467 : Blo 786339 789467 := bstep (se 1 (by rfl) ⟨592100, by rfl⟩ : syracuseStep 789467 = 1184201) B1184201
theorem B789543 : Blo 786339 789543 := bstep (se 1 (by rfl) ⟨592157, by rfl⟩ : syracuseStep 789543 = 1184315) B1184315
theorem B789583 : Blo 786339 789583 := bstep (se 1 (by rfl) ⟨592187, by rfl⟩ : syracuseStep 789583 = 1184375) B1184375
theorem B789599 : Blo 786339 789599 := bstep (se 1 (by rfl) ⟨592199, by rfl⟩ : syracuseStep 789599 = 1184399) B1184399
theorem B789627 : Blo 786339 789627 := bstep (se 1 (by rfl) ⟨592220, by rfl⟩ : syracuseStep 789627 = 1184441) B1184441
theorem B2395307 : Blo 786339 2395307 := bstep (se 1 (by rfl) ⟨1796480, by rfl⟩ : syracuseStep 2395307 = 3592961) B3592961
theorem B789679 : Blo 786339 789679 := bstep (se 1 (by rfl) ⟨592259, by rfl⟩ : syracuseStep 789679 = 1184519) B1184519
theorem B888007 : Blo 786339 888007 := bstep (se 1 (by rfl) ⟨666005, by rfl⟩ : syracuseStep 888007 = 1332011) B1332011
theorem B789703 : Blo 786339 789703 := bstep (se 1 (by rfl) ⟨592277, by rfl⟩ : syracuseStep 789703 = 1184555) B1184555
theorem B789723 : Blo 786339 789723 := bstep (se 1 (by rfl) ⟨592292, by rfl⟩ : syracuseStep 789723 = 1184585) B1184585
theorem B789799 : Blo 786339 789799 := bstep (se 1 (by rfl) ⟨592349, by rfl⟩ : syracuseStep 789799 = 1184699) B1184699
theorem B789839 : Blo 786339 789839 := bstep (se 1 (by rfl) ⟨592379, by rfl⟩ : syracuseStep 789839 = 1184759) B1184759
theorem B5672281 : Blo 786339 5672281 := bstep (se 2 (by rfl) ⟨2127105, by rfl⟩ : syracuseStep 5672281 = 4254211) B4254211
theorem B789855 : Blo 786339 789855 := bstep (se 1 (by rfl) ⟨592391, by rfl⟩ : syracuseStep 789855 = 1184783) B1184783
theorem B5049715 : Blo 786339 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B789883 : Blo 786339 789883 := bstep (se 1 (by rfl) ⟨592412, by rfl⟩ : syracuseStep 789883 = 1184825) B1184825
theorem B6720893 : Blo 786339 6720893 := bstep (se 3 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 6720893 = 2520335) B2520335
theorem B4263293 : Blo 786339 4263293 := bstep (se 3 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 4263293 = 1598735) B1598735
theorem B2133377 : Blo 786339 2133377 := bstep (se 2 (by rfl) ⟨800016, by rfl⟩ : syracuseStep 2133377 = 1600033) B1600033
theorem B1183151 : Blo 786339 1183151 := bstep (se 1 (by rfl) ⟨887363, by rfl⟩ : syracuseStep 1183151 = 1774727) B1774727
theorem B789935 : Blo 786339 789935 := bstep (se 1 (by rfl) ⟨592451, by rfl⟩ : syracuseStep 789935 = 1184903) B1184903
theorem B789959 : Blo 786339 789959 := bstep (se 1 (by rfl) ⟨592469, by rfl⟩ : syracuseStep 789959 = 1184939) B1184939
theorem B789979 : Blo 786339 789979 := bstep (se 1 (by rfl) ⟨592484, by rfl⟩ : syracuseStep 789979 = 1184969) B1184969
theorem B1183241 : Blo 786339 1183241 := bstep (se 2 (by rfl) ⟨443715, by rfl⟩ : syracuseStep 1183241 = 887431) B887431
theorem B2657825 : Blo 786339 2657825 := bstep (se 2 (by rfl) ⟨996684, by rfl⟩ : syracuseStep 2657825 = 1993369) B1993369
theorem B1183271 : Blo 786339 1183271 := bstep (se 1 (by rfl) ⟨887453, by rfl⟩ : syracuseStep 1183271 = 1774907) B1774907
theorem B790055 : Blo 786339 790055 := bstep (se 1 (by rfl) ⟨592541, by rfl⟩ : syracuseStep 790055 = 1185083) B1185083
theorem B790095 : Blo 786339 790095 := bstep (se 1 (by rfl) ⟨592571, by rfl⟩ : syracuseStep 790095 = 1185143) B1185143
theorem B790111 : Blo 786339 790111 := bstep (se 1 (by rfl) ⟨592583, by rfl⟩ : syracuseStep 790111 = 1185167) B1185167
theorem B1773179 : Blo 786339 1773179 := bstep (se 1 (by rfl) ⟨1329884, by rfl⟩ : syracuseStep 1773179 = 2659769) B2659769
theorem B1183355 : Blo 786339 1183355 := bstep (se 1 (by rfl) ⟨887516, by rfl⟩ : syracuseStep 1183355 = 1775033) B1775033
theorem B790139 : Blo 786339 790139 := bstep (se 1 (by rfl) ⟨592604, by rfl⟩ : syracuseStep 790139 = 1185209) B1185209
theorem B3247739 : Blo 786339 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B790191 : Blo 786339 790191 := bstep (se 1 (by rfl) ⟨592643, by rfl⟩ : syracuseStep 790191 = 1185287) B1185287
theorem B790215 : Blo 786339 790215 := bstep (se 1 (by rfl) ⟨592661, by rfl⟩ : syracuseStep 790215 = 1185323) B1185323
theorem B790235 : Blo 786339 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B2658041 : Blo 786339 2658041 := bstep (se 2 (by rfl) ⟨996765, by rfl⟩ : syracuseStep 2658041 = 1993531) B1993531
theorem B1773305 : Blo 786339 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1183481 : Blo 786339 1183481 := bstep (se 2 (by rfl) ⟨443805, by rfl⟩ : syracuseStep 1183481 = 887611) B887611
theorem B790311 : Blo 786339 790311 := bstep (se 1 (by rfl) ⟨592733, by rfl⟩ : syracuseStep 790311 = 1185467) B1185467
theorem B1183583 : Blo 786339 1183583 := bstep (se 1 (by rfl) ⟨887687, by rfl⟩ : syracuseStep 1183583 = 1775375) B1775375
theorem B1183595 : Blo 786339 1183595 := bstep (se 1 (by rfl) ⟨887696, by rfl⟩ : syracuseStep 1183595 = 1775393) B1775393
theorem B1347511 : Blo 786339 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2396087 : Blo 786339 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B2658311 : Blo 786339 2658311 := bstep (se 1 (by rfl) ⟨1993733, by rfl⟩ : syracuseStep 2658311 = 3987467) B3987467
theorem B1773575 : Blo 786339 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B888871 : Blo 786339 888871 := bstep (se 1 (by rfl) ⟨666653, by rfl⟩ : syracuseStep 888871 = 1333307) B1333307
theorem B1773647 : Blo 786339 1773647 := bstep (se 1 (by rfl) ⟨1330235, by rfl⟩ : syracuseStep 1773647 = 2660471) B2660471
theorem B1183823 : Blo 786339 1183823 := bstep (se 1 (by rfl) ⟨887867, by rfl⟩ : syracuseStep 1183823 = 1775735) B1775735
theorem B2658419 : Blo 786339 2658419 := bstep (se 1 (by rfl) ⟨1993814, by rfl⟩ : syracuseStep 2658419 = 3987629) B3987629
theorem B1183943 : Blo 786339 1183943 := bstep (se 1 (by rfl) ⟨887957, by rfl⟩ : syracuseStep 1183943 = 1775915) B1775915
theorem B1184105 : Blo 786339 1184105 := bstep (se 2 (by rfl) ⟨444039, by rfl⟩ : syracuseStep 1184105 = 888079) B888079
theorem B2658689 : Blo 786339 2658689 := bstep (se 2 (by rfl) ⟨997008, by rfl⟩ : syracuseStep 2658689 = 1994017) B1994017
theorem B1184183 : Blo 786339 1184183 := bstep (se 1 (by rfl) ⟨888137, by rfl⟩ : syracuseStep 1184183 = 1776275) B1776275
theorem B1774043 : Blo 786339 1774043 := bstep (se 1 (by rfl) ⟨1330532, by rfl⟩ : syracuseStep 1774043 = 2661065) B2661065
theorem B1184219 : Blo 786339 1184219 := bstep (se 1 (by rfl) ⟨888164, by rfl⟩ : syracuseStep 1184219 = 1776329) B1776329
theorem B2134717 : Blo 786339 2134717 := bstep (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) B800519
theorem B1774511 : Blo 786339 1774511 := bstep (se 1 (by rfl) ⟨1330883, by rfl⟩ : syracuseStep 1774511 = 2661767) B2661767
theorem B1184687 : Blo 786339 1184687 := bstep (se 1 (by rfl) ⟨888515, by rfl⟩ : syracuseStep 1184687 = 1777031) B1777031
theorem B19928065 : Blo 786339 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B1184777 : Blo 786339 1184777 := bstep (se 2 (by rfl) ⟨444291, by rfl⟩ : syracuseStep 1184777 = 888583) B888583
theorem B1184807 : Blo 786339 1184807 := bstep (se 1 (by rfl) ⟨888605, by rfl⟩ : syracuseStep 1184807 = 1777211) B1777211
theorem B1184891 : Blo 786339 1184891 := bstep (se 1 (by rfl) ⟨888668, by rfl⟩ : syracuseStep 1184891 = 1777337) B1777337
theorem B2659499 : Blo 786339 2659499 := bstep (se 1 (by rfl) ⟨1994624, by rfl⟩ : syracuseStep 2659499 = 3989249) B3989249
theorem B1774763 : Blo 786339 1774763 := bstep (se 1 (by rfl) ⟨1331072, by rfl⟩ : syracuseStep 1774763 = 2662145) B2662145
theorem B1185017 : Blo 786339 1185017 := bstep (se 2 (by rfl) ⟨444381, by rfl⟩ : syracuseStep 1185017 = 888763) B888763
theorem B2987351 : Blo 786339 2987351 := bstep (se 1 (by rfl) ⟨2240513, by rfl⟩ : syracuseStep 2987351 = 4481027) B4481027
theorem B1185119 : Blo 786339 1185119 := bstep (se 1 (by rfl) ⟨888839, by rfl⟩ : syracuseStep 1185119 = 1777679) B1777679
theorem B1185131 : Blo 786339 1185131 := bstep (se 1 (by rfl) ⟨888848, by rfl⟩ : syracuseStep 1185131 = 1777697) B1777697
theorem B1185359 : Blo 786339 1185359 := bstep (se 1 (by rfl) ⟨889019, by rfl⟩ : syracuseStep 1185359 = 1778039) B1778039
theorem B28448405 : Blo 786339 28448405 := bstep (se 6 (by rfl) ⟨666759, by rfl⟩ : syracuseStep 28448405 = 1333519) B1333519
theorem B2660039 : Blo 786339 2660039 := bstep (se 1 (by rfl) ⟨1995029, by rfl⟩ : syracuseStep 2660039 = 3990059) B3990059
theorem B1775303 : Blo 786339 1775303 := bstep (se 1 (by rfl) ⟨1331477, by rfl⟩ : syracuseStep 1775303 = 2662955) B2662955
theorem B1185479 : Blo 786339 1185479 := bstep (se 1 (by rfl) ⟨889109, by rfl⟩ : syracuseStep 1185479 = 1778219) B1778219
theorem B2136221 : Blo 786339 2136221 := bstep (se 3 (by rfl) ⟨400541, by rfl⟩ : syracuseStep 2136221 = 801083) B801083
theorem B2660903 : Blo 786339 2660903 := bstep (se 1 (by rfl) ⟨1995677, by rfl⟩ : syracuseStep 2660903 = 3991355) B3991355
theorem B1776167 : Blo 786339 1776167 := bstep (se 1 (by rfl) ⟨1332125, by rfl⟩ : syracuseStep 1776167 = 2664251) B2664251
theorem B2661011 : Blo 786339 2661011 := bstep (se 1 (by rfl) ⟨1995758, by rfl⟩ : syracuseStep 2661011 = 3991517) B3991517
theorem B2661227 : Blo 786339 2661227 := bstep (se 1 (by rfl) ⟨1995920, by rfl⟩ : syracuseStep 2661227 = 3991841) B3991841
theorem B1776491 : Blo 786339 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B2661281 : Blo 786339 2661281 := bstep (se 2 (by rfl) ⟨997980, by rfl⟩ : syracuseStep 2661281 = 1995961) B1995961
theorem B1776545 : Blo 786339 1776545 := bstep (se 2 (by rfl) ⟨666204, by rfl⟩ : syracuseStep 1776545 = 1332409) B1332409
theorem B1776887 : Blo 786339 1776887 := bstep (se 1 (by rfl) ⟨1332665, by rfl⟩ : syracuseStep 1776887 = 2665331) B2665331
theorem B3841453 : Blo 786339 3841453 := bstep (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) B1440545
theorem B2661875 : Blo 786339 2661875 := bstep (se 1 (by rfl) ⟨1996406, by rfl⟩ : syracuseStep 2661875 = 3992813) B3992813
theorem B2530855 : Blo 786339 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B5054075 : Blo 786339 5054075 := bstep (se 1 (by rfl) ⟨3790556, by rfl⟩ : syracuseStep 5054075 = 7581113) B7581113
theorem B1777481 : Blo 786339 1777481 := bstep (se 2 (by rfl) ⟨666555, by rfl⟩ : syracuseStep 1777481 = 1333111) B1333111
theorem B10952567 : Blo 786339 10952567 := bstep (se 1 (by rfl) ⟨8214425, by rfl⟩ : syracuseStep 10952567 = 16428851) B16428851
theorem B2662415 : Blo 786339 2662415 := bstep (se 1 (by rfl) ⟨1996811, by rfl⟩ : syracuseStep 2662415 = 3993623) B3993623
theorem B2531407 : Blo 786339 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B1122427 : Blo 786339 1122427 := bstep (se 1 (by rfl) ⟨841820, by rfl⟩ : syracuseStep 1122427 = 1683641) B1683641
theorem B4497565 : Blo 786339 4497565 := bstep (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) B1686587
theorem B1122655 : Blo 786339 1122655 := bstep (se 1 (by rfl) ⟨841991, by rfl⟩ : syracuseStep 1122655 = 1683983) B1683983
theorem B2990465 : Blo 786339 2990465 := bstep (se 2 (by rfl) ⟨1121424, by rfl⟩ : syracuseStep 2990465 = 2242849) B2242849
theorem B2990479 : Blo 786339 2990479 := bstep (se 1 (by rfl) ⟨2242859, by rfl⟩ : syracuseStep 2990479 = 4485719) B4485719
theorem B19178009 : Blo 786339 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B2663009 : Blo 786339 2663009 := bstep (se 2 (by rfl) ⟨998628, by rfl⟩ : syracuseStep 2663009 = 1997257) B1997257
theorem B5055149 : Blo 786339 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B1418057 : Blo 786339 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B5677931 : Blo 786339 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B1123247 : Blo 786339 1123247 := bstep (se 1 (by rfl) ⟨842435, by rfl⟩ : syracuseStep 1123247 = 1684871) B1684871
theorem B4268983 : Blo 786339 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B2925967 : Blo 786339 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B1418791 : Blo 786339 1418791 := bstep (se 1 (by rfl) ⟨1064093, by rfl⟩ : syracuseStep 1418791 = 2128187) B2128187
theorem B6399611 : Blo 786339 6399611 := bstep (se 1 (by rfl) ⟨4799708, by rfl⟩ : syracuseStep 6399611 = 9599417) B9599417
theorem B2991755 : Blo 786339 2991755 := bstep (se 1 (by rfl) ⟨2243816, by rfl⟩ : syracuseStep 2991755 = 4487633) B4487633
theorem B1517303 : Blo 786339 1517303 := bstep (se 1 (by rfl) ⟨1137977, by rfl⟩ : syracuseStep 1517303 = 2275955) B2275955
theorem B2664467 : Blo 786339 2664467 := bstep (se 1 (by rfl) ⟨1998350, by rfl⟩ : syracuseStep 2664467 = 3996701) B3996701
theorem B6138013 : Blo 786339 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B1124551 : Blo 786339 1124551 := bstep (se 1 (by rfl) ⟨843413, by rfl⟩ : syracuseStep 1124551 = 1686827) B1686827
theorem B2664791 : Blo 786339 2664791 := bstep (se 1 (by rfl) ⟨1998593, by rfl⟩ : syracuseStep 2664791 = 3997187) B3997187
theorem B1681769 : Blo 786339 1681769 := bstep (se 2 (by rfl) ⟨630663, by rfl⟩ : syracuseStep 1681769 = 1261327) B1261327
theorem B5122457 : Blo 786339 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B25537463 : Blo 786339 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B4500481 : Blo 786339 4500481 := bstep (se 2 (by rfl) ⟨1687680, by rfl⟩ : syracuseStep 4500481 = 3375361) B3375361
theorem B1420537 : Blo 786339 1420537 := bstep (se 2 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 1420537 = 1065403) B1065403
theorem B2665871 : Blo 786339 2665871 := bstep (se 1 (by rfl) ⟨1999403, by rfl⟩ : syracuseStep 2665871 = 3998807) B3998807
theorem B4107763 : Blo 786339 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B2666195 : Blo 786339 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B3026717 : Blo 786339 3026717 := bstep (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) B1135019
theorem B1421243 : Blo 786339 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B1519967 : Blo 786339 1519967 := bstep (se 1 (by rfl) ⟨1139975, by rfl⟩ : syracuseStep 1519967 = 2279951) B2279951
theorem B21607013 : Blo 786339 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B7582571 : Blo 786339 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B2667383 : Blo 786339 2667383 := bstep (se 1 (by rfl) ⟨2000537, by rfl⟩ : syracuseStep 2667383 = 4001075) B4001075
theorem B2995127 : Blo 786339 2995127 := bstep (se 1 (by rfl) ⟨2246345, by rfl⟩ : syracuseStep 2995127 = 4492691) B4492691
theorem B996391 : Blo 786339 996391 := bstep (se 1 (by rfl) ⟨747293, by rfl⟩ : syracuseStep 996391 = 1494587) B1494587
theorem B36353195 : Blo 786339 36353195 := bstep (se 1 (by rfl) ⟨27264896, by rfl⟩ : syracuseStep 36353195 = 54529793) B54529793
theorem B996715 : Blo 786339 996715 := bstep (se 1 (by rfl) ⟨747536, by rfl⟩ : syracuseStep 996715 = 1495073) B1495073
theorem B996943 : Blo 786339 996943 := bstep (se 1 (by rfl) ⟨747707, by rfl⟩ : syracuseStep 996943 = 1495415) B1495415
theorem B5977799 : Blo 786339 5977799 := bstep (se 1 (by rfl) ⟨4483349, by rfl⟩ : syracuseStep 5977799 = 8966699) B8966699
theorem B3192671 : Blo 786339 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B2996129 : Blo 786339 2996129 := bstep (se 2 (by rfl) ⟨1123548, by rfl⟩ : syracuseStep 2996129 = 2247097) B2247097
theorem B3782713 : Blo 786339 3782713 := bstep (se 2 (by rfl) ⟨1418517, by rfl⟩ : syracuseStep 3782713 = 2837035) B2837035
theorem B3193175 : Blo 786339 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B2996585 : Blo 786339 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B1259963 : Blo 786339 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B998011 : Blo 786339 998011 := bstep (se 1 (by rfl) ⟨748508, by rfl⟩ : syracuseStep 998011 = 1497017) B1497017
theorem B998239 : Blo 786339 998239 := bstep (se 1 (by rfl) ⟨748679, by rfl⟩ : syracuseStep 998239 = 1497359) B1497359
theorem B2997101 : Blo 786339 2997101 := bstep (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) B1123913
theorem B998831 : Blo 786339 998831 := bstep (se 1 (by rfl) ⟨749123, by rfl⟩ : syracuseStep 998831 = 1498247) B1498247
theorem B5684681 : Blo 786339 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B2997769 : Blo 786339 2997769 := bstep (se 2 (by rfl) ⟨1124163, by rfl⟩ : syracuseStep 2997769 = 2248327) B2248327
theorem B2244307 : Blo 786339 2244307 := bstep (se 1 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 2244307 = 3366461) B3366461
theorem B1326955 : Blo 786339 1326955 := bstep (se 1 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 1326955 = 1990433) B1990433
theorem B1294375 : Blo 786339 1294375 := bstep (se 1 (by rfl) ⟨970781, by rfl⟩ : syracuseStep 1294375 = 1941563) B1941563
theorem B2834585 : Blo 786339 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B9585211 : Blo 786339 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B3981959 : Blo 786339 3981959 := bstep (se 1 (by rfl) ⟨2986469, by rfl⟩ : syracuseStep 3981959 = 5972939) B5972939
theorem B10961771 : Blo 786339 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B1328015 : Blo 786339 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B2999227 : Blo 786339 2999227 := bstep (se 1 (by rfl) ⟨2249420, by rfl⟩ : syracuseStep 2999227 = 4498841) B4498841
theorem B2245639 : Blo 786339 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B8995859 : Blo 786339 8995859 := bstep (se 1 (by rfl) ⟨6746894, by rfl⟩ : syracuseStep 8995859 = 13493789) B13493789
theorem B1328251 : Blo 786339 1328251 := bstep (se 1 (by rfl) ⟨996188, by rfl⟩ : syracuseStep 1328251 = 1992377) B1992377
theorem B1262839 : Blo 786339 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B8963783 : Blo 786339 8963783 := bstep (se 1 (by rfl) ⟨6722837, by rfl⟩ : syracuseStep 8963783 = 13445675) B13445675
theorem B3000017 : Blo 786339 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B41043671 : Blo 786339 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B12764965 : Blo 786339 12764965 := bstep (se 4 (by rfl) ⟨1196715, by rfl⟩ : syracuseStep 12764965 = 2393431) B2393431
theorem B1198007 : Blo 786339 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1329115 : Blo 786339 1329115 := bstep (se 1 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 1329115 = 1993673) B1993673
theorem B3983417 : Blo 786339 3983417 := bstep (se 2 (by rfl) ⟨1493781, by rfl⟩ : syracuseStep 3983417 = 2987563) B2987563
theorem B3000473 : Blo 786339 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B1067207 : Blo 786339 1067207 := bstep (se 1 (by rfl) ⟨800405, by rfl⟩ : syracuseStep 1067207 = 1600811) B1600811
theorem B3787019 : Blo 786339 3787019 := bstep (se 1 (by rfl) ⟨2840264, by rfl⟩ : syracuseStep 3787019 = 5680529) B5680529
theorem B2247041 : Blo 786339 2247041 := bstep (se 2 (by rfl) ⟨842640, by rfl⟩ : syracuseStep 2247041 = 1685281) B1685281
theorem B1329743 : Blo 786339 1329743 := bstep (se 1 (by rfl) ⟨997307, by rfl⟩ : syracuseStep 1329743 = 1994615) B1994615
theorem B22727303 : Blo 786339 22727303 := bstep (se 1 (by rfl) ⟨17045477, by rfl⟩ : syracuseStep 22727303 = 34090955) B34090955
theorem B2247497 : Blo 786339 2247497 := bstep (se 2 (by rfl) ⟨842811, by rfl⟩ : syracuseStep 2247497 = 1685623) B1685623
theorem B1493903 : Blo 786339 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B1494055 : Blo 786339 1494055 := bstep (se 1 (by rfl) ⟨1120541, by rfl⟩ : syracuseStep 1494055 = 2241083) B2241083
theorem B43142219 : Blo 786339 43142219 := bstep (se 1 (by rfl) ⟨32356664, by rfl⟩ : syracuseStep 43142219 = 64713329) B64713329
theorem B1494139 : Blo 786339 1494139 := bstep (se 1 (by rfl) ⟨1120604, by rfl⟩ : syracuseStep 1494139 = 2241209) B2241209
theorem B2837699 : Blo 786339 2837699 := bstep (se 1 (by rfl) ⟨2128274, by rfl⟩ : syracuseStep 2837699 = 4256549) B4256549
theorem B5983631 : Blo 786339 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B1330607 : Blo 786339 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B1265159 : Blo 786339 1265159 := bstep (se 1 (by rfl) ⟨948869, by rfl⟩ : syracuseStep 1265159 = 1897739) B1897739
theorem B1494625 : Blo 786339 1494625 := bstep (se 2 (by rfl) ⟨560484, by rfl⟩ : syracuseStep 1494625 = 1120969) B1120969
theorem B8081117 : Blo 786339 8081117 := bstep (se 3 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 8081117 = 3030419) B3030419
theorem B1331039 : Blo 786339 1331039 := bstep (se 1 (by rfl) ⟨998279, by rfl⟩ : syracuseStep 1331039 = 1996559) B1996559
theorem B2248555 : Blo 786339 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B3592045 : Blo 786339 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B5689207 : Blo 786339 5689207 := bstep (se 1 (by rfl) ⟨4266905, by rfl⟩ : syracuseStep 5689207 = 8533811) B8533811
theorem B8998775 : Blo 786339 8998775 := bstep (se 1 (by rfl) ⟨6749081, by rfl⟩ : syracuseStep 8998775 = 13498163) B13498163
theorem B3985523 : Blo 786339 3985523 := bstep (se 1 (by rfl) ⟨2989142, by rfl⟩ : syracuseStep 3985523 = 5978285) B5978285
theorem B1331599 : Blo 786339 1331599 := bstep (se 1 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 1331599 = 1997399) B1997399
theorem B1495559 : Blo 786339 1495559 := bstep (se 1 (by rfl) ⟨1121669, by rfl⟩ : syracuseStep 1495559 = 2243339) B2243339
theorem B1496083 : Blo 786339 1496083 := bstep (se 1 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 1496083 = 2244125) B2244125
theorem B5690387 : Blo 786339 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B1332281 : Blo 786339 1332281 := bstep (se 2 (by rfl) ⟨499605, by rfl⟩ : syracuseStep 1332281 = 999211) B999211
theorem B2249785 : Blo 786339 2249785 := bstep (se 2 (by rfl) ⟨843669, by rfl⟩ : syracuseStep 2249785 = 1687339) B1687339
theorem B1594811 : Blo 786339 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B4478611 : Blo 786339 4478611 := bstep (se 1 (by rfl) ⟨3358958, by rfl⟩ : syracuseStep 4478611 = 6717917) B6717917
theorem B3987143 : Blo 786339 3987143 := bstep (se 1 (by rfl) ⟨2990357, by rfl⟩ : syracuseStep 3987143 = 5980715) B5980715
theorem B1332983 : Blo 786339 1332983 := bstep (se 1 (by rfl) ⟨999737, by rfl⟩ : syracuseStep 1332983 = 1999475) B1999475
theorem B1333327 : Blo 786339 1333327 := bstep (se 1 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 1333327 = 1999991) B1999991
theorem B1333577 : Blo 786339 1333577 := bstep (se 2 (by rfl) ⟨500091, by rfl⟩ : syracuseStep 1333577 = 1000183) B1000183
theorem B3201751 : Blo 786339 3201751 := bstep (se 1 (by rfl) ⟨2401313, by rfl⟩ : syracuseStep 3201751 = 4802627) B4802627
theorem B8510285 : Blo 786339 8510285 := bstep (se 3 (by rfl) ⟨1595678, by rfl⟩ : syracuseStep 8510285 = 3191357) B3191357
theorem B11361397 : Blo 786339 11361397 := bstep (se 5 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 11361397 = 1065131) B1065131
theorem B1498475 : Blo 786339 1498475 := bstep (se 1 (by rfl) ⟨1123856, by rfl⟩ : syracuseStep 1498475 = 2247713) B2247713
theorem B8969615 : Blo 786339 8969615 := bstep (se 1 (by rfl) ⟨6727211, by rfl⟩ : syracuseStep 8969615 = 13454423) B13454423
theorem B1892279 : Blo 786339 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B1499143 : Blo 786339 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B843815 : Blo 786339 843815 := bstep (se 1 (by rfl) ⟨632861, by rfl⟩ : syracuseStep 843815 = 1265723) B1265723
theorem B3792977 : Blo 786339 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B3367433 : Blo 786339 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B1499705 : Blo 786339 1499705 := bstep (se 2 (by rfl) ⟨562389, by rfl⟩ : syracuseStep 1499705 = 1124779) B1124779
theorem B10216145 : Blo 786339 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B1991699 : Blo 786339 1991699 := bstep (se 1 (by rfl) ⟨1493774, by rfl⟩ : syracuseStep 1991699 = 2987549) B2987549
theorem B6382745 : Blo 786339 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B1598663 : Blo 786339 1598663 := bstep (se 1 (by rfl) ⟨1198997, by rfl⟩ : syracuseStep 1598663 = 2397995) B2397995
theorem B10216651 : Blo 786339 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B6743411 : Blo 786339 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B5989949 : Blo 786339 5989949 := bstep (se 3 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 5989949 = 2246231) B2246231
theorem B6383393 : Blo 786339 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B1796015 : Blo 786339 1796015 := bstep (se 1 (by rfl) ⟨1347011, by rfl⟩ : syracuseStep 1796015 = 2694023) B2694023
theorem B1599419 : Blo 786339 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B1534009 : Blo 786339 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B32303447 : Blo 786339 32303447 := bstep (se 1 (by rfl) ⟨24227585, by rfl⟩ : syracuseStep 32303447 = 48455171) B48455171
theorem B5400985 : Blo 786339 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B3795437 : Blo 786339 3795437 := bstep (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) B1423289
theorem B5990921 : Blo 786339 5990921 := bstep (se 2 (by rfl) ⟨2246595, by rfl⟩ : syracuseStep 5990921 = 4493191) B4493191
theorem B5040899 : Blo 786339 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B3369757 : Blo 786339 3369757 := bstep (se 3 (by rfl) ⟨631829, by rfl⟩ : syracuseStep 3369757 = 1263659) B1263659
theorem B1796971 : Blo 786339 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B6810551 : Blo 786339 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B1600609 : Blo 786339 1600609 := bstep (se 2 (by rfl) ⟨600228, by rfl⟩ : syracuseStep 1600609 = 1200457) B1200457
theorem B3992975 : Blo 786339 3992975 := bstep (se 1 (by rfl) ⟨2994731, by rfl⟩ : syracuseStep 3992975 = 5989463) B5989463
theorem B10087901 : Blo 786339 10087901 := bstep (se 3 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 10087901 = 3782963) B3782963
theorem B945703 : Blo 786339 945703 := bstep (se 1 (by rfl) ⟨709277, by rfl⟩ : syracuseStep 945703 = 1418555) B1418555
theorem B6155837 : Blo 786339 6155837 := bstep (se 3 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 6155837 = 2308439) B2308439
theorem B5992379 : Blo 786339 5992379 := bstep (se 1 (by rfl) ⟨4494284, by rfl⟩ : syracuseStep 5992379 = 8988569) B8988569
theorem B1995151 : Blo 786339 1995151 := bstep (se 1 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 1995151 = 2992727) B2992727
theorem B2519515 : Blo 786339 2519515 := bstep (se 1 (by rfl) ⟨1889636, by rfl⟩ : syracuseStep 2519515 = 3779273) B3779273
theorem B3797513 : Blo 786339 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B1995475 : Blo 786339 1995475 := bstep (se 1 (by rfl) ⟨1496606, by rfl⟩ : syracuseStep 1995475 = 2993213) B2993213
theorem B24048389 : Blo 786339 24048389 := bstep (se 4 (by rfl) ⟨2254536, by rfl⟩ : syracuseStep 24048389 = 4509073) B4509073
theorem B6747137 : Blo 786339 6747137 := bstep (se 2 (by rfl) ⟨2530176, by rfl⟩ : syracuseStep 6747137 = 5060353) B5060353
theorem B2520143 : Blo 786339 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B3995081 : Blo 786339 3995081 := bstep (se 2 (by rfl) ⟨1498155, by rfl⟩ : syracuseStep 3995081 = 2996311) B2996311
theorem B1996427 : Blo 786339 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B9729953 : Blo 786339 9729953 := bstep (se 2 (by rfl) ⟨3648732, by rfl⟩ : syracuseStep 9729953 = 7297465) B7297465
theorem B12777425 : Blo 786339 12777425 := bstep (se 2 (by rfl) ⟨4791534, by rfl⟩ : syracuseStep 12777425 = 9583069) B9583069
theorem B18249785 : Blo 786339 18249785 := bstep (se 2 (by rfl) ⟨6843669, by rfl⟩ : syracuseStep 18249785 = 13687339) B13687339
theorem B3995729 : Blo 786339 3995729 := bstep (se 2 (by rfl) ⟨1498398, by rfl⟩ : syracuseStep 3995729 = 2996797) B2996797
theorem B15989123 : Blo 786339 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B1997561 : Blo 786339 1997561 := bstep (se 2 (by rfl) ⟨749085, by rfl⟩ : syracuseStep 1997561 = 1498171) B1498171
theorem B1997743 : Blo 786339 1997743 := bstep (se 1 (by rfl) ⟨1498307, by rfl⟩ : syracuseStep 1997743 = 2996615) B2996615
theorem B17530201 : Blo 786339 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B1998209 : Blo 786339 1998209 := bstep (se 2 (by rfl) ⟨749328, by rfl⟩ : syracuseStep 1998209 = 1498657) B1498657
theorem B2391439 : Blo 786339 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B2129657 : Blo 786339 2129657 := bstep (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) B1597243
theorem B1998665 : Blo 786339 1998665 := bstep (se 2 (by rfl) ⟨749499, by rfl⟩ : syracuseStep 1998665 = 1498999) B1498999
theorem B786351 : Blo 786339 786351 := bstep (se 1 (by rfl) ⟨589763, by rfl⟩ : syracuseStep 786351 = 1179527) B1179527
theorem B1179575 : Blo 786339 1179575 := bstep (se 1 (by rfl) ⟨884681, by rfl⟩ : syracuseStep 1179575 = 1769363) B1769363
theorem B1769399 : Blo 786339 1769399 := bstep (se 1 (by rfl) ⟨1327049, by rfl⟩ : syracuseStep 1769399 = 2654099) B2654099
theorem B8978363 : Blo 786339 8978363 := bstep (se 1 (by rfl) ⟨6733772, by rfl⟩ : syracuseStep 8978363 = 13467545) B13467545
theorem B786375 : Blo 786339 786375 := bstep (se 1 (by rfl) ⟨589781, by rfl⟩ : syracuseStep 786375 = 1179563) B1179563
theorem B786395 : Blo 786339 786395 := bstep (se 1 (by rfl) ⟨589796, by rfl⟩ : syracuseStep 786395 = 1179593) B1179593
theorem B1179611 : Blo 786339 1179611 := bstep (se 1 (by rfl) ⟨884708, by rfl⟩ : syracuseStep 1179611 = 1769417) B1769417
theorem B1998857 : Blo 786339 1998857 := bstep (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) B1499143
theorem B3375209 : Blo 786339 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B5996753 : Blo 786339 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B786719 : Blo 786339 786719 := bstep (se 1 (by rfl) ⟨590039, by rfl⟩ : syracuseStep 786719 = 1180079) B1180079
theorem B1179995 : Blo 786339 1179995 := bstep (se 1 (by rfl) ⟨884996, by rfl⟩ : syracuseStep 1179995 = 1769993) B1769993
theorem B786779 : Blo 786339 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B786799 : Blo 786339 786799 := bstep (se 1 (by rfl) ⟨590099, by rfl⟩ : syracuseStep 786799 = 1180199) B1180199
theorem B786855 : Blo 786339 786855 := bstep (se 1 (by rfl) ⟨590141, by rfl⟩ : syracuseStep 786855 = 1180283) B1180283
theorem B2654639 : Blo 786339 2654639 := bstep (se 1 (by rfl) ⟨1990979, by rfl⟩ : syracuseStep 2654639 = 3981959) B3981959
theorem B1769903 : Blo 786339 1769903 := bstep (se 1 (by rfl) ⟨1327427, by rfl⟩ : syracuseStep 1769903 = 2654855) B2654855
theorem B1769939 : Blo 786339 1769939 := bstep (se 1 (by rfl) ⟨1327454, by rfl⟩ : syracuseStep 1769939 = 2654909) B2654909
theorem B786939 : Blo 786339 786939 := bstep (se 1 (by rfl) ⟨590204, by rfl⟩ : syracuseStep 786939 = 1180409) B1180409
theorem B1770047 : Blo 786339 1770047 := bstep (se 1 (by rfl) ⟨1327535, by rfl⟩ : syracuseStep 1770047 = 2655071) B2655071
theorem B1180223 : Blo 786339 1180223 := bstep (se 1 (by rfl) ⟨885167, by rfl⟩ : syracuseStep 1180223 = 1770335) B1770335
theorem B787007 : Blo 786339 787007 := bstep (se 1 (by rfl) ⟨590255, by rfl⟩ : syracuseStep 787007 = 1180511) B1180511
theorem B787015 : Blo 786339 787015 := bstep (se 1 (by rfl) ⟨590261, by rfl⟩ : syracuseStep 787015 = 1180523) B1180523
theorem B885343 : Blo 786339 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B1770155 : Blo 786339 1770155 := bstep (se 1 (by rfl) ⟨1327616, by rfl⟩ : syracuseStep 1770155 = 2655233) B2655233
theorem B1180343 : Blo 786339 1180343 := bstep (se 1 (by rfl) ⟨885257, by rfl⟩ : syracuseStep 1180343 = 1770515) B1770515
theorem B5997239 : Blo 786339 5997239 := bstep (se 1 (by rfl) ⟨4497929, by rfl⟩ : syracuseStep 5997239 = 8995859) B8995859
theorem B787167 : Blo 786339 787167 := bstep (se 1 (by rfl) ⟨590375, by rfl⟩ : syracuseStep 787167 = 1180751) B1180751
theorem B12780281 : Blo 786339 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B787247 : Blo 786339 787247 := bstep (se 1 (by rfl) ⟨590435, by rfl⟩ : syracuseStep 787247 = 1180871) B1180871
theorem B1180571 : Blo 786339 1180571 := bstep (se 1 (by rfl) ⟨885428, by rfl⟩ : syracuseStep 1180571 = 1770857) B1770857
theorem B787355 : Blo 786339 787355 := bstep (se 1 (by rfl) ⟨590516, by rfl⟩ : syracuseStep 787355 = 1181033) B1181033
theorem B787407 : Blo 786339 787407 := bstep (se 1 (by rfl) ⟨590555, by rfl⟩ : syracuseStep 787407 = 1181111) B1181111
theorem B787431 : Blo 786339 787431 := bstep (se 1 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 787431 = 1181147) B1181147
theorem B3736567 : Blo 786339 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B2000011 : Blo 786339 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B27362447 : Blo 786339 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B1770695 : Blo 786339 1770695 := bstep (se 1 (by rfl) ⟨1328021, by rfl⟩ : syracuseStep 1770695 = 2656043) B2656043
theorem B3998969 : Blo 786339 3998969 := bstep (se 2 (by rfl) ⟨1499613, by rfl⟩ : syracuseStep 3998969 = 2999227) B2999227
theorem B787743 : Blo 786339 787743 := bstep (se 1 (by rfl) ⟨590807, by rfl⟩ : syracuseStep 787743 = 1181615) B1181615
theorem B1180967 : Blo 786339 1180967 := bstep (se 1 (by rfl) ⟨885725, by rfl⟩ : syracuseStep 1180967 = 1771451) B1771451
theorem B5768491 : Blo 786339 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B787803 : Blo 786339 787803 := bstep (se 1 (by rfl) ⟨590852, by rfl⟩ : syracuseStep 787803 = 1181705) B1181705
theorem B8979821 : Blo 786339 8979821 := bstep (se 3 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 8979821 = 3367433) B3367433
theorem B787823 : Blo 786339 787823 := bstep (se 1 (by rfl) ⟨590867, by rfl⟩ : syracuseStep 787823 = 1181735) B1181735
theorem B2655611 : Blo 786339 2655611 := bstep (se 1 (by rfl) ⟨1991708, by rfl⟩ : syracuseStep 2655611 = 3983417) B3983417
theorem B1770875 : Blo 786339 1770875 := bstep (se 1 (by rfl) ⟨1328156, by rfl⟩ : syracuseStep 1770875 = 2656313) B2656313
theorem B1181051 : Blo 786339 1181051 := bstep (se 1 (by rfl) ⟨885788, by rfl⟩ : syracuseStep 1181051 = 1771577) B1771577
theorem B787879 : Blo 786339 787879 := bstep (se 1 (by rfl) ⟨590909, by rfl⟩ : syracuseStep 787879 = 1181819) B1181819
theorem B2000315 : Blo 786339 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B1771001 : Blo 786339 1771001 := bstep (se 2 (by rfl) ⟨664125, by rfl⟩ : syracuseStep 1771001 = 1328251) B1328251
theorem B1181177 : Blo 786339 1181177 := bstep (se 2 (by rfl) ⟨442941, by rfl⟩ : syracuseStep 1181177 = 885883) B885883
theorem B787963 : Blo 786339 787963 := bstep (se 1 (by rfl) ⟨590972, by rfl⟩ : syracuseStep 787963 = 1181945) B1181945
theorem B2524679 : Blo 786339 2524679 := bstep (se 1 (by rfl) ⟨1893509, by rfl⟩ : syracuseStep 2524679 = 3787019) B3787019
theorem B788031 : Blo 786339 788031 := bstep (se 1 (by rfl) ⟨591023, by rfl⟩ : syracuseStep 788031 = 1182047) B1182047
theorem B788039 : Blo 786339 788039 := bstep (se 1 (by rfl) ⟨591029, by rfl⟩ : syracuseStep 788039 = 1182059) B1182059
theorem B1771091 : Blo 786339 1771091 := bstep (se 1 (by rfl) ⟨1328318, by rfl⟩ : syracuseStep 1771091 = 2656637) B2656637
theorem B1181279 : Blo 786339 1181279 := bstep (se 1 (by rfl) ⟨885959, by rfl⟩ : syracuseStep 1181279 = 1771919) B1771919
theorem B886495 : Blo 786339 886495 := bstep (se 1 (by rfl) ⟨664871, by rfl⟩ : syracuseStep 886495 = 1329743) B1329743
theorem B788191 : Blo 786339 788191 := bstep (se 1 (by rfl) ⟨591143, by rfl⟩ : syracuseStep 788191 = 1182287) B1182287
theorem B1771271 : Blo 786339 1771271 := bstep (se 1 (by rfl) ⟨1328453, by rfl⟩ : syracuseStep 1771271 = 2656907) B2656907
theorem B788271 : Blo 786339 788271 := bstep (se 1 (by rfl) ⟨591203, by rfl⟩ : syracuseStep 788271 = 1182407) B1182407
theorem B1181495 : Blo 786339 1181495 := bstep (se 1 (by rfl) ⟨886121, by rfl⟩ : syracuseStep 1181495 = 1772243) B1772243
theorem B3901289 : Blo 786339 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B788379 : Blo 786339 788379 := bstep (se 1 (by rfl) ⟨591284, by rfl⟩ : syracuseStep 788379 = 1182569) B1182569
theorem B2557903 : Blo 786339 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B788431 : Blo 786339 788431 := bstep (se 1 (by rfl) ⟨591323, by rfl⟩ : syracuseStep 788431 = 1182647) B1182647
theorem B788455 : Blo 786339 788455 := bstep (se 1 (by rfl) ⟨591341, by rfl⟩ : syracuseStep 788455 = 1182683) B1182683
theorem B1181801 : Blo 786339 1181801 := bstep (se 2 (by rfl) ⟨443175, by rfl⟩ : syracuseStep 1181801 = 886351) B886351
theorem B29231389 : Blo 786339 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B887071 : Blo 786339 887071 := bstep (se 1 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 887071 = 1330607) B1330607
theorem B788767 : Blo 786339 788767 := bstep (se 1 (by rfl) ⟨591575, by rfl⟩ : syracuseStep 788767 = 1183151) B1183151
theorem B788827 : Blo 786339 788827 := bstep (se 1 (by rfl) ⟨591620, by rfl⟩ : syracuseStep 788827 = 1183241) B1183241
theorem B1771883 : Blo 786339 1771883 := bstep (se 1 (by rfl) ⟨1328912, by rfl⟩ : syracuseStep 1771883 = 2657825) B2657825
theorem B788847 : Blo 786339 788847 := bstep (se 1 (by rfl) ⟨591635, by rfl⟩ : syracuseStep 788847 = 1183271) B1183271
theorem B1182119 : Blo 786339 1182119 := bstep (se 1 (by rfl) ⟨886589, by rfl⟩ : syracuseStep 1182119 = 1773179) B1773179
theorem B788903 : Blo 786339 788903 := bstep (se 1 (by rfl) ⟨591677, by rfl⟩ : syracuseStep 788903 = 1183355) B1183355
theorem B2165159 : Blo 786339 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B1772027 : Blo 786339 1772027 := bstep (se 1 (by rfl) ⟨1329020, by rfl⟩ : syracuseStep 1772027 = 2658041) B2658041
theorem B1182203 : Blo 786339 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B788987 : Blo 786339 788987 := bstep (se 1 (by rfl) ⟨591740, by rfl⟩ : syracuseStep 788987 = 1183481) B1183481
theorem B887359 : Blo 786339 887359 := bstep (se 1 (by rfl) ⟨665519, by rfl⟩ : syracuseStep 887359 = 1331039) B1331039
theorem B789055 : Blo 786339 789055 := bstep (se 1 (by rfl) ⟨591791, by rfl⟩ : syracuseStep 789055 = 1183583) B1183583
theorem B789063 : Blo 786339 789063 := bstep (se 1 (by rfl) ⟨591797, by rfl⟩ : syracuseStep 789063 = 1183595) B1183595
theorem B5999183 : Blo 786339 5999183 := bstep (se 1 (by rfl) ⟨4499387, by rfl⟩ : syracuseStep 5999183 = 8998775) B8998775
theorem B1772153 : Blo 786339 1772153 := bstep (se 2 (by rfl) ⟨664557, by rfl⟩ : syracuseStep 1772153 = 1329115) B1329115
theorem B1182329 : Blo 786339 1182329 := bstep (se 2 (by rfl) ⟨443373, by rfl⟩ : syracuseStep 1182329 = 886747) B886747
theorem B1772207 : Blo 786339 1772207 := bstep (se 1 (by rfl) ⟨1329155, by rfl⟩ : syracuseStep 1772207 = 2658311) B2658311
theorem B1182383 : Blo 786339 1182383 := bstep (se 1 (by rfl) ⟨886787, by rfl⟩ : syracuseStep 1182383 = 1773575) B1773575
theorem B1182431 : Blo 786339 1182431 := bstep (se 1 (by rfl) ⟨886823, by rfl⟩ : syracuseStep 1182431 = 1773647) B1773647
theorem B789215 : Blo 786339 789215 := bstep (se 1 (by rfl) ⟨591911, by rfl⟩ : syracuseStep 789215 = 1183823) B1183823
theorem B2657015 : Blo 786339 2657015 := bstep (se 1 (by rfl) ⟨1992761, by rfl⟩ : syracuseStep 2657015 = 3985523) B3985523
theorem B1772279 : Blo 786339 1772279 := bstep (se 1 (by rfl) ⟨1329209, by rfl⟩ : syracuseStep 1772279 = 2658419) B2658419
theorem B789295 : Blo 786339 789295 := bstep (se 1 (by rfl) ⟨591971, by rfl⟩ : syracuseStep 789295 = 1183943) B1183943
theorem B789403 : Blo 786339 789403 := bstep (se 1 (by rfl) ⟨592052, by rfl⟩ : syracuseStep 789403 = 1184105) B1184105
theorem B1772459 : Blo 786339 1772459 := bstep (se 1 (by rfl) ⟨1329344, by rfl⟩ : syracuseStep 1772459 = 2658689) B2658689
theorem B789455 : Blo 786339 789455 := bstep (se 1 (by rfl) ⟨592091, by rfl⟩ : syracuseStep 789455 = 1184183) B1184183
theorem B1182695 : Blo 786339 1182695 := bstep (se 1 (by rfl) ⟨887021, by rfl⟩ : syracuseStep 1182695 = 1774043) B1774043
theorem B789479 : Blo 786339 789479 := bstep (se 1 (by rfl) ⟨592109, by rfl⟩ : syracuseStep 789479 = 1184219) B1184219
theorem B4263101 : Blo 786339 4263101 := bstep (se 3 (by rfl) ⟨799331, by rfl⟩ : syracuseStep 4263101 = 1598663) B1598663
theorem B1182953 : Blo 786339 1182953 := bstep (se 2 (by rfl) ⟨443607, by rfl⟩ : syracuseStep 1182953 = 887215) B887215
theorem B1183007 : Blo 786339 1183007 := bstep (se 1 (by rfl) ⟨887255, by rfl⟩ : syracuseStep 1183007 = 1774511) B1774511
theorem B789791 : Blo 786339 789791 := bstep (se 1 (by rfl) ⟨592343, by rfl⟩ : syracuseStep 789791 = 1184687) B1184687
theorem B789851 : Blo 786339 789851 := bstep (se 1 (by rfl) ⟨592388, by rfl⟩ : syracuseStep 789851 = 1184777) B1184777
theorem B789871 : Blo 786339 789871 := bstep (se 1 (by rfl) ⟨592403, by rfl⟩ : syracuseStep 789871 = 1184807) B1184807
theorem B888187 : Blo 786339 888187 := bstep (se 1 (by rfl) ⟨666140, by rfl⟩ : syracuseStep 888187 = 1332281) B1332281
theorem B789927 : Blo 786339 789927 := bstep (se 1 (by rfl) ⟨592445, by rfl⟩ : syracuseStep 789927 = 1184891) B1184891
theorem B1772999 : Blo 786339 1772999 := bstep (se 1 (by rfl) ⟨1329749, by rfl⟩ : syracuseStep 1772999 = 2659499) B2659499
theorem B1183175 : Blo 786339 1183175 := bstep (se 1 (by rfl) ⟨887381, by rfl⟩ : syracuseStep 1183175 = 1774763) B1774763
theorem B790011 : Blo 786339 790011 := bstep (se 1 (by rfl) ⟨592508, by rfl⟩ : syracuseStep 790011 = 1185017) B1185017
theorem B790079 : Blo 786339 790079 := bstep (se 1 (by rfl) ⟨592559, by rfl⟩ : syracuseStep 790079 = 1185119) B1185119
theorem B790087 : Blo 786339 790087 := bstep (se 1 (by rfl) ⟨592565, by rfl⟩ : syracuseStep 790087 = 1185131) B1185131
theorem B4493009 : Blo 786339 4493009 := bstep (se 2 (by rfl) ⟨1684878, by rfl⟩ : syracuseStep 4493009 = 3369757) B3369757
theorem B790239 : Blo 786339 790239 := bstep (se 1 (by rfl) ⟨592679, by rfl⟩ : syracuseStep 790239 = 1185359) B1185359
theorem B17076005 : Blo 786339 17076005 := bstep (se 4 (by rfl) ⟨1600875, by rfl⟩ : syracuseStep 17076005 = 3201751) B3201751
theorem B1183529 : Blo 786339 1183529 := bstep (se 2 (by rfl) ⟨443823, by rfl⟩ : syracuseStep 1183529 = 887647) B887647
theorem B2658095 : Blo 786339 2658095 := bstep (se 1 (by rfl) ⟨1993571, by rfl⟩ : syracuseStep 2658095 = 3987143) B3987143
theorem B1773359 : Blo 786339 1773359 := bstep (se 1 (by rfl) ⟨1330019, by rfl⟩ : syracuseStep 1773359 = 2660039) B2660039
theorem B1183535 : Blo 786339 1183535 := bstep (se 1 (by rfl) ⟨887651, by rfl⟩ : syracuseStep 1183535 = 1775303) B1775303
theorem B790319 : Blo 786339 790319 := bstep (se 1 (by rfl) ⟨592739, by rfl⟩ : syracuseStep 790319 = 1185479) B1185479
theorem B2395961 : Blo 786339 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B888655 : Blo 786339 888655 := bstep (se 1 (by rfl) ⟨666491, by rfl⟩ : syracuseStep 888655 = 1332983) B1332983
theorem B6000641 : Blo 786339 6000641 := bstep (se 2 (by rfl) ⟨2250240, by rfl⟩ : syracuseStep 6000641 = 4500481) B4500481
theorem B2134145 : Blo 786339 2134145 := bstep (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) B1600609
theorem B889051 : Blo 786339 889051 := bstep (se 1 (by rfl) ⟨666788, by rfl⟩ : syracuseStep 889051 = 1333577) B1333577
theorem B1184009 : Blo 786339 1184009 := bstep (se 2 (by rfl) ⟨444003, by rfl⟩ : syracuseStep 1184009 = 888007) B888007
theorem B1773935 : Blo 786339 1773935 := bstep (se 1 (by rfl) ⟨1330451, by rfl⟩ : syracuseStep 1773935 = 2660903) B2660903
theorem B1184111 : Blo 786339 1184111 := bstep (se 1 (by rfl) ⟨888083, by rfl⟩ : syracuseStep 1184111 = 1776167) B1776167
theorem B1774007 : Blo 786339 1774007 := bstep (se 1 (by rfl) ⟨1330505, by rfl⟩ : syracuseStep 1774007 = 2661011) B2661011
theorem B5673523 : Blo 786339 5673523 := bstep (se 1 (by rfl) ⟨4255142, by rfl⟩ : syracuseStep 5673523 = 8510285) B8510285
theorem B1774151 : Blo 786339 1774151 := bstep (se 1 (by rfl) ⟨1330613, by rfl⟩ : syracuseStep 1774151 = 2661227) B2661227
theorem B1184327 : Blo 786339 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B1774187 : Blo 786339 1774187 := bstep (se 1 (by rfl) ⟨1330640, by rfl⟩ : syracuseStep 1774187 = 2661281) B2661281
theorem B1184363 : Blo 786339 1184363 := bstep (se 1 (by rfl) ⟨888272, by rfl⟩ : syracuseStep 1184363 = 1776545) B1776545
theorem B1184591 : Blo 786339 1184591 := bstep (se 1 (by rfl) ⟨888443, by rfl⟩ : syracuseStep 1184591 = 1776887) B1776887
theorem B1774583 : Blo 786339 1774583 := bstep (se 1 (by rfl) ⟨1330937, by rfl⟩ : syracuseStep 1774583 = 2661875) B2661875
theorem B1184987 : Blo 786339 1184987 := bstep (se 1 (by rfl) ⟨888740, by rfl⟩ : syracuseStep 1184987 = 1777481) B1777481
theorem B1774943 : Blo 786339 1774943 := bstep (se 1 (by rfl) ⟨1331207, by rfl⟩ : syracuseStep 1774943 = 2662415) B2662415
theorem B1185161 : Blo 786339 1185161 := bstep (se 2 (by rfl) ⟨444435, by rfl⟩ : syracuseStep 1185161 = 888871) B888871
theorem B2528651 : Blo 786339 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B12785339 : Blo 786339 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B1775339 : Blo 786339 1775339 := bstep (se 1 (by rfl) ⟨1331504, by rfl⟩ : syracuseStep 1775339 = 2663009) B2663009
theorem B2660201 : Blo 786339 2660201 := bstep (se 2 (by rfl) ⟨997575, by rfl⟩ : syracuseStep 2660201 = 1995151) B1995151
theorem B1775465 : Blo 786339 1775465 := bstep (se 2 (by rfl) ⟨665799, by rfl⟩ : syracuseStep 1775465 = 1331599) B1331599
theorem B4495607 : Blo 786339 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B2660633 : Blo 786339 2660633 := bstep (se 2 (by rfl) ⟨997737, by rfl⟩ : syracuseStep 2660633 = 1995475) B1995475
theorem B42637661 : Blo 786339 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B4266407 : Blo 786339 4266407 := bstep (se 1 (by rfl) ⟨3199805, by rfl⟩ : syracuseStep 4266407 = 6399611) B6399611
theorem B1776311 : Blo 786339 1776311 := bstep (se 1 (by rfl) ⟨1332233, by rfl⟩ : syracuseStep 1776311 = 2664467) B2664467
theorem B21535631 : Blo 786339 21535631 := bstep (se 1 (by rfl) ⟨16151723, by rfl⟩ : syracuseStep 21535631 = 32303447) B32303447
theorem B1776527 : Blo 786339 1776527 := bstep (se 1 (by rfl) ⟨1332395, by rfl⟩ : syracuseStep 1776527 = 2664791) B2664791
theorem B3414971 : Blo 786339 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B2530291 : Blo 786339 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B93494405 : Blo 786339 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B5971481 : Blo 786339 5971481 := bstep (se 2 (by rfl) ⟨2239305, by rfl⟩ : syracuseStep 5971481 = 4478611) B4478611
theorem B2661983 : Blo 786339 2661983 := bstep (se 1 (by rfl) ⟨1996487, by rfl⟩ : syracuseStep 2661983 = 3992975) B3992975
theorem B1777247 : Blo 786339 1777247 := bstep (se 1 (by rfl) ⟨1332935, by rfl⟩ : syracuseStep 1777247 = 2665871) B2665871
theorem B6725267 : Blo 786339 6725267 := bstep (se 1 (by rfl) ⟨5043950, by rfl⟩ : syracuseStep 6725267 = 10087901) B10087901
theorem B4103891 : Blo 786339 4103891 := bstep (se 1 (by rfl) ⟨3077918, by rfl⟩ : syracuseStep 4103891 = 6155837) B6155837
theorem B1777463 : Blo 786339 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B1777769 : Blo 786339 1777769 := bstep (se 2 (by rfl) ⟨666663, by rfl⟩ : syracuseStep 1777769 = 1333327) B1333327
theorem B2531675 : Blo 786339 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B16032259 : Blo 786339 16032259 := bstep (se 1 (by rfl) ⟨12024194, by rfl⟩ : syracuseStep 16032259 = 24048389) B24048389
theorem B5055047 : Blo 786339 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B1778255 : Blo 786339 1778255 := bstep (se 1 (by rfl) ⟨1333691, by rfl⟩ : syracuseStep 1778255 = 2667383) B2667383
theorem B4498091 : Blo 786339 4498091 := bstep (se 1 (by rfl) ⟨3373568, by rfl⟩ : syracuseStep 4498091 = 6747137) B6747137
theorem B1680095 : Blo 786339 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B2663387 : Blo 786339 2663387 := bstep (se 1 (by rfl) ⟨1997540, by rfl⟩ : syracuseStep 2663387 = 3995081) B3995081
theorem B2663549 : Blo 786339 2663549 := bstep (se 3 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 2663549 = 998831) B998831
theorem B2663657 : Blo 786339 2663657 := bstep (se 2 (by rfl) ⟨998871, by rfl⟩ : syracuseStep 2663657 = 1997743) B1997743
theorem B12166523 : Blo 786339 12166523 := bstep (se 1 (by rfl) ⟨9124892, by rfl⟩ : syracuseStep 12166523 = 18249785) B18249785
theorem B2663819 : Blo 786339 2663819 := bstep (se 1 (by rfl) ⟨1997864, by rfl⟩ : syracuseStep 2663819 = 3995729) B3995729
theorem B15148529 : Blo 786339 15148529 := bstep (se 2 (by rfl) ⟨5680698, by rfl⟩ : syracuseStep 15148529 = 11361397) B11361397
theorem B3188585 : Blo 786339 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B5121937 : Blo 786339 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B5679085 : Blo 786339 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B2992409 : Blo 786339 2992409 := bstep (se 2 (by rfl) ⟨1122153, by rfl⟩ : syracuseStep 2992409 = 2244307) B2244307
theorem B3189979 : Blo 786339 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B5975855 : Blo 786339 5975855 := bstep (se 1 (by rfl) ⟨4481891, by rfl⟩ : syracuseStep 5975855 = 8963783) B8963783
theorem B798671 : Blo 786339 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B896999 : Blo 786339 896999 := bstep (se 1 (by rfl) ⟨672749, by rfl⟩ : syracuseStep 896999 = 1345499) B1345499
theorem B2994185 : Blo 786339 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B1683785 : Blo 786339 1683785 := bstep (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) B1262839
theorem B1683803 : Blo 786339 1683803 := bstep (se 1 (by rfl) ⟨1262852, by rfl⟩ : syracuseStep 1683803 = 2525705) B2525705
theorem B2666843 : Blo 786339 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B15151535 : Blo 786339 15151535 := bstep (se 1 (by rfl) ⟨11363651, by rfl⟩ : syracuseStep 15151535 = 22727303) B22727303
theorem B6730289 : Blo 786339 6730289 := bstep (se 2 (by rfl) ⟨2523858, by rfl⟩ : syracuseStep 6730289 = 5047717) B5047717
theorem B11383541 : Blo 786339 11383541 := bstep (se 5 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 11383541 = 1067207) B1067207
theorem B1422251 : Blo 786339 1422251 := bstep (se 1 (by rfl) ⟨1066688, by rfl⟩ : syracuseStep 1422251 = 2133377) B2133377
theorem B17019953 : Blo 786339 17019953 := bstep (se 2 (by rfl) ⟨6382482, by rfl⟩ : syracuseStep 17019953 = 12764965) B12764965
theorem B2995325 : Blo 786339 2995325 := bstep (se 3 (by rfl) ⟨561623, by rfl⟩ : syracuseStep 2995325 = 1123247) B1123247
theorem B5387411 : Blo 786339 5387411 := bstep (se 1 (by rfl) ⟨4040558, by rfl⟩ : syracuseStep 5387411 = 8081117) B8081117
theorem B2045345 : Blo 786339 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B997039 : Blo 786339 997039 := bstep (se 1 (by rfl) ⟨747779, by rfl⟩ : syracuseStep 997039 = 1495559) B1495559
theorem B1063207 : Blo 786339 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B11385157 : Blo 786339 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B1424147 : Blo 786339 1424147 := bstep (se 1 (by rfl) ⟨1068110, by rfl⟩ : syracuseStep 1424147 = 2136221) B2136221
theorem B6732953 : Blo 786339 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B1260937 : Blo 786339 1260937 := bstep (se 2 (by rfl) ⟨472851, by rfl⟩ : syracuseStep 1260937 = 945703) B945703
theorem B998983 : Blo 786339 998983 := bstep (se 1 (by rfl) ⟨749237, by rfl⟩ : syracuseStep 998983 = 1498475) B1498475
theorem B5979743 : Blo 786339 5979743 := bstep (se 1 (by rfl) ⟨4484807, by rfl⟩ : syracuseStep 5979743 = 8969615) B8969615
theorem B2998073 : Blo 786339 2998073 := bstep (se 2 (by rfl) ⟨1124277, by rfl⟩ : syracuseStep 2998073 = 2248555) B2248555
theorem B7585609 : Blo 786339 7585609 := bstep (se 2 (by rfl) ⟨2844603, by rfl⟩ : syracuseStep 7585609 = 5689207) B5689207
theorem B999803 : Blo 786339 999803 := bstep (se 1 (by rfl) ⟨749852, by rfl⟩ : syracuseStep 999803 = 1499705) B1499705
theorem B3785287 : Blo 786339 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B3359353 : Blo 786339 3359353 := bstep (se 2 (by rfl) ⟨1259757, by rfl⟩ : syracuseStep 3359353 = 2519515) B2519515
theorem B1327799 : Blo 786339 1327799 := bstep (se 1 (by rfl) ⟨995849, by rfl⟩ : syracuseStep 1327799 = 1991699) B1991699
theorem B1197343 : Blo 786339 1197343 := bstep (se 1 (by rfl) ⟨898007, by rfl⟩ : syracuseStep 1197343 = 1796015) B1796015
theorem B1066279 : Blo 786339 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B1328521 : Blo 786339 1328521 := bstep (se 2 (by rfl) ⟨498195, by rfl⟩ : syracuseStep 1328521 = 996391) B996391
theorem B2999713 : Blo 786339 2999713 := bstep (se 2 (by rfl) ⟨1124892, by rfl⟩ : syracuseStep 2999713 = 2249785) B2249785
theorem B27313685 : Blo 786339 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B1328953 : Blo 786339 1328953 := bstep (se 2 (by rfl) ⟨498357, by rfl⟩ : syracuseStep 1328953 = 996715) B996715
theorem B3360599 : Blo 786339 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B4540367 : Blo 786339 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B17024975 : Blo 786339 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B1329257 : Blo 786339 1329257 := bstep (se 2 (by rfl) ⟨498471, by rfl⟩ : syracuseStep 1329257 = 996943) B996943
theorem B746768645 : Blo 786339 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B3983741 : Blo 786339 3983741 := bstep (se 3 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 3983741 = 1493903) B1493903
theorem B2017811 : Blo 786339 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B21908069 : Blo 786339 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B14404675 : Blo 786339 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B24235463 : Blo 786339 24235463 := bstep (se 1 (by rfl) ⟨18176597, by rfl⟩ : syracuseStep 24235463 = 36353195) B36353195
theorem B1330681 : Blo 786339 1330681 := bstep (se 2 (by rfl) ⟨499005, by rfl⟩ : syracuseStep 1330681 = 998011) B998011
theorem B1330951 : Blo 786339 1330951 := bstep (se 1 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 1330951 = 1996427) B1996427
theorem B1330985 : Blo 786339 1330985 := bstep (se 2 (by rfl) ⟨499119, by rfl⟩ : syracuseStep 1330985 = 998239) B998239
theorem B3985199 : Blo 786339 3985199 := bstep (se 1 (by rfl) ⟨2988899, by rfl⟩ : syracuseStep 3985199 = 5977799) B5977799
theorem B839975 : Blo 786339 839975 := bstep (se 1 (by rfl) ⟨629981, by rfl⟩ : syracuseStep 839975 = 1259963) B1259963
theorem B1331707 : Blo 786339 1331707 := bstep (se 1 (by rfl) ⟨998780, by rfl⟩ : syracuseStep 1331707 = 1997561) B1997561
theorem B19157573 : Blo 786339 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B1332139 : Blo 786339 1332139 := bstep (se 1 (by rfl) ⟨999104, by rfl⟩ : syracuseStep 1332139 = 1998209) B1998209
theorem B3789787 : Blo 786339 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B1332443 : Blo 786339 1332443 := bstep (se 1 (by rfl) ⟨999332, by rfl⟩ : syracuseStep 1332443 = 1998665) B1998665
theorem B5985575 : Blo 786339 5985575 := bstep (se 1 (by rfl) ⟨4489181, by rfl⟩ : syracuseStep 5985575 = 8978363) B8978363
theorem B1725833 : Blo 786339 1725833 := bstep (se 2 (by rfl) ⟨647187, by rfl⟩ : syracuseStep 1725833 = 1294375) B1294375
theorem B1889723 : Blo 786339 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B2250173 : Blo 786339 2250173 := bstep (se 3 (by rfl) ⟨421907, by rfl⟩ : syracuseStep 2250173 = 843815) B843815
theorem B1332679 : Blo 786339 1332679 := bstep (se 1 (by rfl) ⟨999509, by rfl⟩ : syracuseStep 1332679 = 1999019) B1999019
theorem B1496569 : Blo 786339 1496569 := bstep (se 2 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 1496569 = 1122427) B1122427
theorem B1496873 : Blo 786339 1496873 := bstep (se 2 (by rfl) ⟨561327, by rfl⟩ : syracuseStep 1496873 = 1122655) B1122655
theorem B3987305 : Blo 786339 3987305 := bstep (se 2 (by rfl) ⟨1495239, by rfl⟩ : syracuseStep 3987305 = 2990479) B2990479
theorem B2053993 : Blo 786339 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B1333199 : Blo 786339 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B5691977 : Blo 786339 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B4479887 : Blo 786339 4479887 := bstep (se 1 (by rfl) ⟨3359915, by rfl⟩ : syracuseStep 4479887 = 6719831) B6719831
theorem B1498027 : Blo 786339 1498027 := bstep (se 1 (by rfl) ⟨1123520, by rfl⟩ : syracuseStep 1498027 = 2247041) B2247041
theorem B13622201 : Blo 786339 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B1498331 : Blo 786339 1498331 := bstep (se 1 (by rfl) ⟨1123748, by rfl⟩ : syracuseStep 1498331 = 2247497) B2247497
theorem B28761479 : Blo 786339 28761479 := bstep (se 1 (by rfl) ⟨21571109, by rfl⟩ : syracuseStep 28761479 = 43142219) B43142219
theorem B1891721 : Blo 786339 1891721 := bstep (se 2 (by rfl) ⟨709395, by rfl⟩ : syracuseStep 1891721 = 1418791) B1418791
theorem B1596871 : Blo 786339 1596871 := bstep (se 1 (by rfl) ⟨1197653, by rfl⟩ : syracuseStep 1596871 = 2395307) B2395307
theorem B1891799 : Blo 786339 1891799 := bstep (se 1 (by rfl) ⟨1418849, by rfl⟩ : syracuseStep 1891799 = 2837699) B2837699
theorem B4480595 : Blo 786339 4480595 := bstep (se 1 (by rfl) ⟨3360446, by rfl⟩ : syracuseStep 4480595 = 6720893) B6720893
theorem B2842195 : Blo 786339 2842195 := bstep (se 1 (by rfl) ⟨2131646, by rfl⟩ : syracuseStep 2842195 = 4263293) B4263293
theorem B3989087 : Blo 786339 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B3366785 : Blo 786339 3366785 := bstep (se 2 (by rfl) ⟨1262544, by rfl⟩ : syracuseStep 3366785 = 2525089) B2525089
theorem B1597391 : Blo 786339 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B8184017 : Blo 786339 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1499401 : Blo 786339 1499401 := bstep (se 2 (by rfl) ⟨562275, by rfl⟩ : syracuseStep 1499401 = 1124551) B1124551
theorem B7201313 : Blo 786339 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B3793591 : Blo 786339 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B1991567 : Blo 786339 1991567 := bstep (se 1 (by rfl) ⟨1493675, by rfl⟩ : syracuseStep 1991567 = 2987351) B2987351
theorem B18965603 : Blo 786339 18965603 := bstep (se 1 (by rfl) ⟨14224202, by rfl⟩ : syracuseStep 18965603 = 28448405) B28448405
theorem B1992073 : Blo 786339 1992073 := bstep (se 2 (by rfl) ⟨747027, by rfl⟩ : syracuseStep 1992073 = 1494055) B1494055
theorem B1992185 : Blo 786339 1992185 := bstep (se 2 (by rfl) ⟨747069, by rfl⟩ : syracuseStep 1992185 = 1494139) B1494139
theorem B1894049 : Blo 786339 1894049 := bstep (se 2 (by rfl) ⟨710268, by rfl⟩ : syracuseStep 1894049 = 1420537) B1420537
theorem B7563041 : Blo 786339 7563041 := bstep (se 2 (by rfl) ⟨2836140, by rfl⟩ : syracuseStep 7563041 = 5672281) B5672281
theorem B1992833 : Blo 786339 1992833 := bstep (se 2 (by rfl) ⟨747312, by rfl⟩ : syracuseStep 1992833 = 1494625) B1494625
theorem B3369383 : Blo 786339 3369383 := bstep (se 1 (by rfl) ⟨2527037, by rfl⟩ : syracuseStep 3369383 = 5054075) B5054075
theorem B1796681 : Blo 786339 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B7301711 : Blo 786339 7301711 := bstep (se 1 (by rfl) ⟨5476283, by rfl⟩ : syracuseStep 7301711 = 10952567) B10952567
theorem B1993643 : Blo 786339 1993643 := bstep (se 1 (by rfl) ⟨1495232, by rfl⟩ : syracuseStep 1993643 = 2990465) B2990465
theorem B3370099 : Blo 786339 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B6810763 : Blo 786339 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B945371 : Blo 786339 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B4255163 : Blo 786339 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B4484717 : Blo 786339 4484717 := bstep (se 3 (by rfl) ⟨840884, by rfl⟩ : syracuseStep 4484717 = 1681769) B1681769
theorem B3993299 : Blo 786339 3993299 := bstep (se 1 (by rfl) ⟨2994974, by rfl⟩ : syracuseStep 3993299 = 5989949) B5989949
theorem B1994503 : Blo 786339 1994503 := bstep (se 1 (by rfl) ⟨1495877, by rfl⟩ : syracuseStep 1994503 = 2991755) B2991755
theorem B1011535 : Blo 786339 1011535 := bstep (se 1 (by rfl) ⟨758651, by rfl⟩ : syracuseStep 1011535 = 1517303) B1517303
theorem B4255595 : Blo 786339 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B26570753 : Blo 786339 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B1994777 : Blo 786339 1994777 := bstep (se 2 (by rfl) ⟨748041, by rfl⟩ : syracuseStep 1994777 = 1496083) B1496083
theorem B3993947 : Blo 786339 3993947 := bstep (se 1 (by rfl) ⟨2995460, by rfl⟩ : syracuseStep 3993947 = 5990921) B5990921
theorem B947495 : Blo 786339 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B3994919 : Blo 786339 3994919 := bstep (se 1 (by rfl) ⟨2996189, by rfl⟩ : syracuseStep 3994919 = 5992379) B5992379
theorem B5043617 : Blo 786339 5043617 := bstep (se 2 (by rfl) ⟨1891356, by rfl⟩ : syracuseStep 5043617 = 3782713) B3782713
theorem B1013311 : Blo 786339 1013311 := bstep (se 1 (by rfl) ⟨759983, by rfl⟩ : syracuseStep 1013311 = 1519967) B1519967
theorem B1996751 : Blo 786339 1996751 := bstep (se 1 (by rfl) ⟨1497563, by rfl⟩ : syracuseStep 1996751 = 2995127) B2995127
theorem B2128447 : Blo 786339 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B1997419 : Blo 786339 1997419 := bstep (se 1 (by rfl) ⟨1498064, by rfl⟩ : syracuseStep 1997419 = 2996129) B2996129
theorem B6486635 : Blo 786339 6486635 := bstep (se 1 (by rfl) ⟨4864976, by rfl⟩ : syracuseStep 6486635 = 9729953) B9729953
theorem B8518283 : Blo 786339 8518283 := bstep (se 1 (by rfl) ⟨6388712, by rfl⟩ : syracuseStep 8518283 = 12777425) B12777425
theorem B3373757 : Blo 786339 3373757 := bstep (se 3 (by rfl) ⟨632579, by rfl⟩ : syracuseStep 3373757 = 1265159) B1265159
theorem B2128783 : Blo 786339 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B1997723 : Blo 786339 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B1998067 : Blo 786339 1998067 := bstep (se 1 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 1998067 = 2997101) B2997101
theorem B3997025 : Blo 786339 3997025 := bstep (se 2 (by rfl) ⟨1498884, by rfl⟩ : syracuseStep 3997025 = 2997769) B2997769
theorem B3374473 : Blo 786339 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B1769273 : Blo 786339 1769273 := bstep (se 2 (by rfl) ⟨663477, by rfl⟩ : syracuseStep 1769273 = 1326955) B1326955
theorem B5046077 : Blo 786339 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B786383 : Blo 786339 786383 := bstep (se 1 (by rfl) ⟨589787, by rfl⟩ : syracuseStep 786383 = 1179575) B1179575
theorem B1179599 : Blo 786339 1179599 := bstep (se 1 (by rfl) ⟨884699, by rfl⟩ : syracuseStep 1179599 = 1769399) B1769399
theorem B786407 : Blo 786339 786407 := bstep (se 1 (by rfl) ⟨589805, by rfl⟩ : syracuseStep 786407 = 1179611) B1179611
theorem B3997835 : Blo 786339 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B786663 : Blo 786339 786663 := bstep (se 1 (by rfl) ⟨589997, by rfl⟩ : syracuseStep 786663 = 1179995) B1179995
theorem B1769759 : Blo 786339 1769759 := bstep (se 1 (by rfl) ⟨1327319, by rfl⟩ : syracuseStep 1769759 = 2654639) B2654639
theorem B1179935 : Blo 786339 1179935 := bstep (se 1 (by rfl) ⟨884951, by rfl⟩ : syracuseStep 1179935 = 1769903) B1769903
theorem B1179959 : Blo 786339 1179959 := bstep (se 1 (by rfl) ⟨884969, by rfl⟩ : syracuseStep 1179959 = 1769939) B1769939
theorem B1999201 : Blo 786339 1999201 := bstep (se 2 (by rfl) ⟨749700, by rfl⟩ : syracuseStep 1999201 = 1499401) B1499401
theorem B1180031 : Blo 786339 1180031 := bstep (se 1 (by rfl) ⟨885023, by rfl⟩ : syracuseStep 1180031 = 1770047) B1770047
theorem B786815 : Blo 786339 786815 := bstep (se 1 (by rfl) ⟨590111, by rfl⟩ : syracuseStep 786815 = 1180223) B1180223
theorem B1180103 : Blo 786339 1180103 := bstep (se 1 (by rfl) ⟨885077, by rfl⟩ : syracuseStep 1180103 = 1770155) B1770155
theorem B885199 : Blo 786339 885199 := bstep (se 1 (by rfl) ⟨663899, by rfl⟩ : syracuseStep 885199 = 1327799) B1327799
theorem B786895 : Blo 786339 786895 := bstep (se 1 (by rfl) ⟨590171, by rfl⟩ : syracuseStep 786895 = 1180343) B1180343
theorem B3998159 : Blo 786339 3998159 := bstep (se 1 (by rfl) ⟨2998619, by rfl⟩ : syracuseStep 3998159 = 5997239) B5997239
theorem B8520187 : Blo 786339 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B787047 : Blo 786339 787047 := bstep (se 1 (by rfl) ⟨590285, by rfl⟩ : syracuseStep 787047 = 1180571) B1180571
theorem B5047049 : Blo 786339 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B1180457 : Blo 786339 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B1180463 : Blo 786339 1180463 := bstep (se 1 (by rfl) ⟨885347, by rfl⟩ : syracuseStep 1180463 = 1770695) B1770695
theorem B4490093 : Blo 786339 4490093 := bstep (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) B1683785
theorem B787311 : Blo 786339 787311 := bstep (se 1 (by rfl) ⟨590483, by rfl⟩ : syracuseStep 787311 = 1180967) B1180967
theorem B6751133 : Blo 786339 6751133 := bstep (se 3 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 6751133 = 2531675) B2531675
theorem B1770407 : Blo 786339 1770407 := bstep (se 1 (by rfl) ⟨1327805, by rfl⟩ : syracuseStep 1770407 = 2655611) B2655611
theorem B1180583 : Blo 786339 1180583 := bstep (se 1 (by rfl) ⟨885437, by rfl⟩ : syracuseStep 1180583 = 1770875) B1770875
theorem B787367 : Blo 786339 787367 := bstep (se 1 (by rfl) ⟨590525, by rfl⟩ : syracuseStep 787367 = 1181051) B1181051
theorem B1180667 : Blo 786339 1180667 := bstep (se 1 (by rfl) ⟨885500, by rfl⟩ : syracuseStep 1180667 = 1771001) B1771001
theorem B787451 : Blo 786339 787451 := bstep (se 1 (by rfl) ⟨590588, by rfl⟩ : syracuseStep 787451 = 1181177) B1181177
theorem B1180727 : Blo 786339 1180727 := bstep (se 1 (by rfl) ⟨885545, by rfl⟩ : syracuseStep 1180727 = 1771091) B1771091
theorem B787519 : Blo 786339 787519 := bstep (se 1 (by rfl) ⟨590639, by rfl⟩ : syracuseStep 787519 = 1181279) B1181279
theorem B1180847 : Blo 786339 1180847 := bstep (se 1 (by rfl) ⟨885635, by rfl⟩ : syracuseStep 1180847 = 1771271) B1771271
theorem B787663 : Blo 786339 787663 := bstep (se 1 (by rfl) ⟨590747, by rfl⟩ : syracuseStep 787663 = 1181495) B1181495
theorem B886171 : Blo 786339 886171 := bstep (se 1 (by rfl) ⟨664628, by rfl⟩ : syracuseStep 886171 = 1329257) B1329257
theorem B787867 : Blo 786339 787867 := bstep (se 1 (by rfl) ⟨590900, by rfl⟩ : syracuseStep 787867 = 1181801) B1181801
theorem B497845763 : Blo 786339 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B1181255 : Blo 786339 1181255 := bstep (se 1 (by rfl) ⟨885941, by rfl⟩ : syracuseStep 1181255 = 1771883) B1771883
theorem B2655827 : Blo 786339 2655827 := bstep (se 1 (by rfl) ⟨1991870, by rfl⟩ : syracuseStep 2655827 = 3983741) B3983741
theorem B788079 : Blo 786339 788079 := bstep (se 1 (by rfl) ⟨591059, by rfl⟩ : syracuseStep 788079 = 1182119) B1182119
theorem B1443439 : Blo 786339 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B1181351 : Blo 786339 1181351 := bstep (se 1 (by rfl) ⟨886013, by rfl⟩ : syracuseStep 1181351 = 1772027) B1772027
theorem B788135 : Blo 786339 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B1345207 : Blo 786339 1345207 := bstep (se 1 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 1345207 = 2017811) B2017811
theorem B3999455 : Blo 786339 3999455 := bstep (se 1 (by rfl) ⟨2999591, by rfl⟩ : syracuseStep 3999455 = 5999183) B5999183
theorem B1181435 : Blo 786339 1181435 := bstep (se 1 (by rfl) ⟨886076, by rfl⟩ : syracuseStep 1181435 = 1772153) B1772153
theorem B788219 : Blo 786339 788219 := bstep (se 1 (by rfl) ⟨591164, by rfl⟩ : syracuseStep 788219 = 1182329) B1182329
theorem B1181471 : Blo 786339 1181471 := bstep (se 1 (by rfl) ⟨886103, by rfl⟩ : syracuseStep 1181471 = 1772207) B1772207
theorem B788255 : Blo 786339 788255 := bstep (se 1 (by rfl) ⟨591191, by rfl⟩ : syracuseStep 788255 = 1182383) B1182383
theorem B788287 : Blo 786339 788287 := bstep (se 1 (by rfl) ⟨591215, by rfl⟩ : syracuseStep 788287 = 1182431) B1182431
theorem B1771343 : Blo 786339 1771343 := bstep (se 1 (by rfl) ⟨1328507, by rfl⟩ : syracuseStep 1771343 = 2657015) B2657015
theorem B1181519 : Blo 786339 1181519 := bstep (se 1 (by rfl) ⟨886139, by rfl⟩ : syracuseStep 1181519 = 1772279) B1772279
theorem B2656097 : Blo 786339 2656097 := bstep (se 2 (by rfl) ⟨996036, by rfl⟩ : syracuseStep 2656097 = 1992073) B1992073
theorem B1771361 : Blo 786339 1771361 := bstep (se 2 (by rfl) ⟨664260, by rfl⟩ : syracuseStep 1771361 = 1328521) B1328521
theorem B3999617 : Blo 786339 3999617 := bstep (se 2 (by rfl) ⟨1499856, by rfl⟩ : syracuseStep 3999617 = 2999713) B2999713
theorem B1181639 : Blo 786339 1181639 := bstep (se 1 (by rfl) ⟨886229, by rfl⟩ : syracuseStep 1181639 = 1772459) B1772459
theorem B788463 : Blo 786339 788463 := bstep (se 1 (by rfl) ⟨591347, by rfl⟩ : syracuseStep 788463 = 1182695) B1182695
theorem B788635 : Blo 786339 788635 := bstep (se 1 (by rfl) ⟨591476, by rfl⟩ : syracuseStep 788635 = 1182953) B1182953
theorem B788671 : Blo 786339 788671 := bstep (se 1 (by rfl) ⟨591503, by rfl⟩ : syracuseStep 788671 = 1183007) B1183007
theorem B1181993 : Blo 786339 1181993 := bstep (se 2 (by rfl) ⟨443247, by rfl⟩ : syracuseStep 1181993 = 886495) B886495
theorem B1181999 : Blo 786339 1181999 := bstep (se 1 (by rfl) ⟨886499, by rfl⟩ : syracuseStep 1181999 = 1772999) B1772999
theorem B788783 : Blo 786339 788783 := bstep (se 1 (by rfl) ⟨591587, by rfl⟩ : syracuseStep 788783 = 1183175) B1183175
theorem B1771937 : Blo 786339 1771937 := bstep (se 2 (by rfl) ⟨664476, by rfl⟩ : syracuseStep 1771937 = 1328953) B1328953
theorem B887323 : Blo 786339 887323 := bstep (se 1 (by rfl) ⟨665492, by rfl⟩ : syracuseStep 887323 = 1330985) B1330985
theorem B789019 : Blo 786339 789019 := bstep (se 1 (by rfl) ⟨591764, by rfl⟩ : syracuseStep 789019 = 1183529) B1183529
theorem B2656799 : Blo 786339 2656799 := bstep (se 1 (by rfl) ⟨1992599, by rfl⟩ : syracuseStep 2656799 = 3985199) B3985199
theorem B1772063 : Blo 786339 1772063 := bstep (se 1 (by rfl) ⟨1329047, by rfl⟩ : syracuseStep 1772063 = 2658095) B2658095
theorem B1182239 : Blo 786339 1182239 := bstep (se 1 (by rfl) ⟨886679, by rfl⟩ : syracuseStep 1182239 = 1773359) B1773359
theorem B789023 : Blo 786339 789023 := bstep (se 1 (by rfl) ⟨591767, by rfl⟩ : syracuseStep 789023 = 1183535) B1183535
theorem B3410537 : Blo 786339 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B7572113 : Blo 786339 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B4000427 : Blo 786339 4000427 := bstep (se 1 (by rfl) ⟨3000320, by rfl⟩ : syracuseStep 4000427 = 6000641) B6000641
theorem B789339 : Blo 786339 789339 := bstep (se 1 (by rfl) ⟨592004, by rfl⟩ : syracuseStep 789339 = 1184009) B1184009
theorem B1182623 : Blo 786339 1182623 := bstep (se 1 (by rfl) ⟨886967, by rfl⟩ : syracuseStep 1182623 = 1773935) B1773935
theorem B789407 : Blo 786339 789407 := bstep (se 1 (by rfl) ⟨592055, by rfl⟩ : syracuseStep 789407 = 1184111) B1184111
theorem B1182671 : Blo 786339 1182671 := bstep (se 1 (by rfl) ⟨887003, by rfl⟩ : syracuseStep 1182671 = 1774007) B1774007
theorem B1182761 : Blo 786339 1182761 := bstep (se 2 (by rfl) ⟨443535, by rfl⟩ : syracuseStep 1182761 = 887071) B887071
theorem B1182767 : Blo 786339 1182767 := bstep (se 1 (by rfl) ⟨887075, by rfl⟩ : syracuseStep 1182767 = 1774151) B1774151
theorem B789551 : Blo 786339 789551 := bstep (se 1 (by rfl) ⟨592163, by rfl⟩ : syracuseStep 789551 = 1184327) B1184327
theorem B1182791 : Blo 786339 1182791 := bstep (se 1 (by rfl) ⟨887093, by rfl⟩ : syracuseStep 1182791 = 1774187) B1774187
theorem B789575 : Blo 786339 789575 := bstep (se 1 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 789575 = 1184363) B1184363
theorem B789727 : Blo 786339 789727 := bstep (se 1 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 789727 = 1184591) B1184591
theorem B1183055 : Blo 786339 1183055 := bstep (se 1 (by rfl) ⟨887291, by rfl⟩ : syracuseStep 1183055 = 1774583) B1774583
theorem B1183145 : Blo 786339 1183145 := bstep (se 2 (by rfl) ⟨443679, by rfl⟩ : syracuseStep 1183145 = 887359) B887359
theorem B2526653 : Blo 786339 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B888295 : Blo 786339 888295 := bstep (se 1 (by rfl) ⟨666221, by rfl⟩ : syracuseStep 888295 = 1332443) B1332443
theorem B789991 : Blo 786339 789991 := bstep (se 1 (by rfl) ⟨592493, by rfl⟩ : syracuseStep 789991 = 1184987) B1184987
theorem B1183295 : Blo 786339 1183295 := bstep (se 1 (by rfl) ⟨887471, by rfl⟩ : syracuseStep 1183295 = 1774943) B1774943
theorem B1150555 : Blo 786339 1150555 := bstep (se 1 (by rfl) ⟨862916, by rfl⟩ : syracuseStep 1150555 = 1725833) B1725833
theorem B790107 : Blo 786339 790107 := bstep (se 1 (by rfl) ⟨592580, by rfl⟩ : syracuseStep 790107 = 1185161) B1185161
theorem B8523559 : Blo 786339 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1183559 : Blo 786339 1183559 := bstep (se 1 (by rfl) ⟨887669, by rfl⟩ : syracuseStep 1183559 = 1775339) B1775339
theorem B2658203 : Blo 786339 2658203 := bstep (se 1 (by rfl) ⟨1993652, by rfl⟩ : syracuseStep 2658203 = 3987305) B3987305
theorem B1773467 : Blo 786339 1773467 := bstep (se 1 (by rfl) ⟨1330100, by rfl⟩ : syracuseStep 1773467 = 2660201) B2660201
theorem B1183643 : Blo 786339 1183643 := bstep (se 1 (by rfl) ⟨887732, by rfl⟩ : syracuseStep 1183643 = 1775465) B1775465
theorem B888799 : Blo 786339 888799 := bstep (se 1 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 888799 = 1333199) B1333199
theorem B19206233 : Blo 786339 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B4493465 : Blo 786339 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B9081017 : Blo 786339 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B1773755 : Blo 786339 1773755 := bstep (se 1 (by rfl) ⟨1330316, by rfl⟩ : syracuseStep 1773755 = 2660633) B2660633
theorem B1184207 : Blo 786339 1184207 := bstep (se 1 (by rfl) ⟨888155, by rfl⟩ : syracuseStep 1184207 = 1776311) B1776311
theorem B1184249 : Blo 786339 1184249 := bstep (se 2 (by rfl) ⟨444093, by rfl⟩ : syracuseStep 1184249 = 888187) B888187
theorem B2986591 : Blo 786339 2986591 := bstep (se 1 (by rfl) ⟨2239943, by rfl⟩ : syracuseStep 2986591 = 4479887) B4479887
theorem B14357087 : Blo 786339 14357087 := bstep (se 1 (by rfl) ⟨10767815, by rfl⟩ : syracuseStep 14357087 = 21535631) B21535631
theorem B1184351 : Blo 786339 1184351 := bstep (se 1 (by rfl) ⟨888263, by rfl⟩ : syracuseStep 1184351 = 1776527) B1776527
theorem B9081467 : Blo 786339 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B1774241 : Blo 786339 1774241 := bstep (se 2 (by rfl) ⟨665340, by rfl⟩ : syracuseStep 1774241 = 1330681) B1330681
theorem B62329603 : Blo 786339 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B19174319 : Blo 786339 19174319 := bstep (se 1 (by rfl) ⟨14380739, by rfl⟩ : syracuseStep 19174319 = 28761479) B28761479
theorem B2659337 : Blo 786339 2659337 := bstep (se 2 (by rfl) ⟨997251, by rfl⟩ : syracuseStep 2659337 = 1994503) B1994503
theorem B1774601 : Blo 786339 1774601 := bstep (se 2 (by rfl) ⟨665475, by rfl⟩ : syracuseStep 1774601 = 1330951) B1330951
theorem B2987063 : Blo 786339 2987063 := bstep (se 1 (by rfl) ⟨2240297, by rfl⟩ : syracuseStep 2987063 = 4480595) B4480595
theorem B2659391 : Blo 786339 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B1774655 : Blo 786339 1774655 := bstep (se 1 (by rfl) ⟨1330991, by rfl⟩ : syracuseStep 1774655 = 2661983) B2661983
theorem B1184831 : Blo 786339 1184831 := bstep (se 1 (by rfl) ⟨888623, by rfl⟩ : syracuseStep 1184831 = 1777247) B1777247
theorem B1184873 : Blo 786339 1184873 := bstep (se 2 (by rfl) ⟨444327, by rfl⟩ : syracuseStep 1184873 = 888655) B888655
theorem B1184975 : Blo 786339 1184975 := bstep (se 1 (by rfl) ⟨888731, by rfl⟩ : syracuseStep 1184975 = 1777463) B1777463
theorem B19928357 : Blo 786339 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B1185179 : Blo 786339 1185179 := bstep (se 1 (by rfl) ⟨888884, by rfl⟩ : syracuseStep 1185179 = 1777769) B1777769
theorem B1185401 : Blo 786339 1185401 := bstep (se 2 (by rfl) ⟨444525, by rfl⟩ : syracuseStep 1185401 = 889051) B889051
theorem B1185503 : Blo 786339 1185503 := bstep (se 1 (by rfl) ⟨889127, by rfl⟩ : syracuseStep 1185503 = 1778255) B1778255
theorem B1120063 : Blo 786339 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B1775591 : Blo 786339 1775591 := bstep (se 1 (by rfl) ⟨1331693, by rfl⟩ : syracuseStep 1775591 = 2663387) B2663387
theorem B1775609 : Blo 786339 1775609 := bstep (se 2 (by rfl) ⟨665853, by rfl⟩ : syracuseStep 1775609 = 1331707) B1331707
theorem B1775699 : Blo 786339 1775699 := bstep (se 1 (by rfl) ⟨1331774, by rfl⟩ : syracuseStep 1775699 = 2663549) B2663549
theorem B1775771 : Blo 786339 1775771 := bstep (se 1 (by rfl) ⟨1331828, by rfl⟩ : syracuseStep 1775771 = 2663657) B2663657
theorem B1775879 : Blo 786339 1775879 := bstep (se 1 (by rfl) ⟨1331909, by rfl⟩ : syracuseStep 1775879 = 2663819) B2663819
theorem B10099019 : Blo 786339 10099019 := bstep (se 1 (by rfl) ⟨7574264, by rfl⟩ : syracuseStep 10099019 = 15148529) B15148529
theorem B1776185 : Blo 786339 1776185 := bstep (se 2 (by rfl) ⟨666069, by rfl⟩ : syracuseStep 1776185 = 1332139) B1332139
theorem B5053049 : Blo 786339 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B4791149 : Blo 786339 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B1776905 : Blo 786339 1776905 := bstep (se 2 (by rfl) ⟨666339, by rfl⟩ : syracuseStep 1776905 = 1332679) B1332679
theorem B2989811 : Blo 786339 2989811 := bstep (se 1 (by rfl) ⟨2242358, by rfl⟩ : syracuseStep 2989811 = 4484717) B4484717
theorem B2662199 : Blo 786339 2662199 := bstep (se 1 (by rfl) ⟨1996649, by rfl⟩ : syracuseStep 2662199 = 3993299) B3993299
theorem B1122535 : Blo 786339 1122535 := bstep (se 1 (by rfl) ⟨841901, by rfl⟩ : syracuseStep 1122535 = 1683803) B1683803
theorem B2662631 : Blo 786339 2662631 := bstep (se 1 (by rfl) ⟨1996973, by rfl⟩ : syracuseStep 2662631 = 3993947) B3993947
theorem B1777895 : Blo 786339 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B10101023 : Blo 786339 10101023 := bstep (se 1 (by rfl) ⟨7575767, by rfl⟩ : syracuseStep 10101023 = 15151535) B15151535
theorem B1417609 : Blo 786339 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B15180209 : Blo 786339 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B11346635 : Blo 786339 11346635 := bstep (se 1 (by rfl) ⟨8509976, by rfl⟩ : syracuseStep 11346635 = 17019953) B17019953
theorem B2663225 : Blo 786339 2663225 := bstep (se 2 (by rfl) ⟨998709, by rfl⟩ : syracuseStep 2663225 = 1997419) B1997419
theorem B2663279 : Blo 786339 2663279 := bstep (se 1 (by rfl) ⟨1997459, by rfl⟩ : syracuseStep 2663279 = 3994919) B3994919
theorem B64627901 : Blo 786339 64627901 := bstep (se 3 (by rfl) ⟨12117731, by rfl⟩ : syracuseStep 64627901 = 24235463) B24235463
theorem B2664089 : Blo 786339 2664089 := bstep (se 2 (by rfl) ⟨999033, by rfl⟩ : syracuseStep 2664089 = 1998067) B1998067
theorem B5678855 : Blo 786339 5678855 := bstep (se 1 (by rfl) ⟨4259141, by rfl⟩ : syracuseStep 5678855 = 8518283) B8518283
theorem B1681249 : Blo 786339 1681249 := bstep (se 2 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 1681249 = 1260937) B1260937
theorem B4499297 : Blo 786339 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B2664683 : Blo 786339 2664683 := bstep (se 1 (by rfl) ⟨1998512, by rfl⟩ : syracuseStep 2664683 = 3997025) B3997025
theorem B2239933 : Blo 786339 2239933 := bstep (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) B839975
theorem B2665979 : Blo 786339 2665979 := bstep (se 1 (by rfl) ⟨1999484, by rfl⟩ : syracuseStep 2665979 = 3998969) B3998969
theorem B5058121 : Blo 786339 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B2666141 : Blo 786339 2666141 := bstep (se 3 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 2666141 = 999803) B999803
theorem B1683119 : Blo 786339 1683119 := bstep (se 1 (by rfl) ⟨1262339, by rfl⟩ : syracuseStep 1683119 = 2524679) B2524679
theorem B2240399 : Blo 786339 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B3026911 : Blo 786339 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B11349983 : Blo 786339 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B2666681 : Blo 786339 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B1421705 : Blo 786339 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B2995339 : Blo 786339 2995339 := bstep (se 1 (by rfl) ⟨2246504, by rfl⟩ : syracuseStep 2995339 = 4493009) B4493009
theorem B11384003 : Blo 786339 11384003 := bstep (se 1 (by rfl) ⟨8538002, by rfl⟩ : syracuseStep 11384003 = 17076005) B17076005
theorem B85505381 : Blo 786339 85505381 := bstep (se 4 (by rfl) ⟨8016129, by rfl⟩ : syracuseStep 85505381 = 16032259) B16032259
theorem B38975185 : Blo 786339 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B1685767 : Blo 786339 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B1259815 : Blo 786339 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B5454253 : Blo 786339 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B997915 : Blo 786339 997915 := bstep (se 1 (by rfl) ⟨748436, by rfl⟩ : syracuseStep 997915 = 1496873) B1496873
theorem B2997071 : Blo 786339 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B28425107 : Blo 786339 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B998887 : Blo 786339 998887 := bstep (se 1 (by rfl) ⟨749165, by rfl⟩ : syracuseStep 998887 = 1498331) B1498331
theorem B1261199 : Blo 786339 1261199 := bstep (se 1 (by rfl) ⟨945899, by rfl⟩ : syracuseStep 1261199 = 1891799) B1891799
theorem B3980987 : Blo 786339 3980987 := bstep (se 1 (by rfl) ⟨2985740, by rfl⟩ : syracuseStep 3980987 = 5971481) B5971481
theorem B2735927 : Blo 786339 2735927 := bstep (se 1 (by rfl) ⟨2051945, by rfl⟩ : syracuseStep 2735927 = 4103891) B4103891
theorem B2244523 : Blo 786339 2244523 := bstep (se 1 (by rfl) ⟨1683392, by rfl⟩ : syracuseStep 2244523 = 3366785) B3366785
theorem B1064927 : Blo 786339 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B5456011 : Blo 786339 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B4800875 : Blo 786339 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B2998727 : Blo 786339 2998727 := bstep (se 1 (by rfl) ⟨2249045, by rfl⟩ : syracuseStep 2998727 = 4498091) B4498091
theorem B1327711 : Blo 786339 1327711 := bstep (se 1 (by rfl) ⟨995783, by rfl⟩ : syracuseStep 1327711 = 1991567) B1991567
theorem B8111015 : Blo 786339 8111015 := bstep (se 1 (by rfl) ⟨6083261, by rfl⟩ : syracuseStep 8111015 = 12166523) B12166523
theorem B1328123 : Blo 786339 1328123 := bstep (se 1 (by rfl) ⟨996092, by rfl⟩ : syracuseStep 1328123 = 1992185) B1992185
theorem B1262699 : Blo 786339 1262699 := bstep (se 1 (by rfl) ⟨947024, by rfl⟩ : syracuseStep 1262699 = 1894049) B1894049
theorem B1328555 : Blo 786339 1328555 := bstep (se 1 (by rfl) ⟨996416, by rfl⟩ : syracuseStep 1328555 = 1992833) B1992833
theorem B2246255 : Blo 786339 2246255 := bstep (se 1 (by rfl) ⟨1684691, by rfl⟩ : syracuseStep 2246255 = 3369383) B3369383
theorem B4867807 : Blo 786339 4867807 := bstep (se 1 (by rfl) ⟨3650855, by rfl⟩ : syracuseStep 4867807 = 7301711) B7301711
theorem B1329095 : Blo 786339 1329095 := bstep (se 1 (by rfl) ⟨996821, by rfl⟩ : syracuseStep 1329095 = 1993643) B1993643
theorem B1329385 : Blo 786339 1329385 := bstep (se 2 (by rfl) ⟨498519, by rfl⟩ : syracuseStep 1329385 = 997039) B997039
theorem B2836775 : Blo 786339 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B2738657 : Blo 786339 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B3983903 : Blo 786339 3983903 := bstep (se 1 (by rfl) ⟨2987927, by rfl⟩ : syracuseStep 3983903 = 5975855) B5975855
theorem B2837063 : Blo 786339 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B17713835 : Blo 786339 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B1329851 : Blo 786339 1329851 := bstep (se 1 (by rfl) ⟨997388, by rfl⟩ : syracuseStep 1329851 = 1994777) B1994777
theorem B15190901 : Blo 786339 15190901 := bstep (se 5 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 15190901 = 1424147) B1424147
theorem B7589027 : Blo 786339 7589027 := bstep (se 1 (by rfl) ⟨5691770, by rfl⟩ : syracuseStep 7589027 = 11383541) B11383541
theorem B2837929 : Blo 786339 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B3591607 : Blo 786339 3591607 := bstep (se 1 (by rfl) ⟨2693705, by rfl⟩ : syracuseStep 3591607 = 5387411) B5387411
theorem B3362411 : Blo 786339 3362411 := bstep (se 1 (by rfl) ⟨2521808, by rfl⟩ : syracuseStep 3362411 = 5043617) B5043617
theorem B2838377 : Blo 786339 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1331167 : Blo 786339 1331167 := bstep (se 1 (by rfl) ⟨998375, by rfl⟩ : syracuseStep 1331167 = 1996751) B1996751
theorem B5394853 : Blo 786339 5394853 := bstep (se 4 (by rfl) ⟨505767, by rfl⟩ : syracuseStep 5394853 = 1011535) B1011535
theorem B2249171 : Blo 786339 2249171 := bstep (se 1 (by rfl) ⟨1686878, by rfl⟩ : syracuseStep 2249171 = 3373757) B3373757
theorem B1331815 : Blo 786339 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B27316997 : Blo 786339 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1331977 : Blo 786339 1331977 := bstep (se 2 (by rfl) ⟨499491, by rfl⟩ : syracuseStep 1331977 = 998983) B998983
theorem B3789593 : Blo 786339 3789593 := bstep (se 2 (by rfl) ⟨1421097, by rfl⟩ : syracuseStep 3789593 = 2842195) B2842195
theorem B3986495 : Blo 786339 3986495 := bstep (se 1 (by rfl) ⟨2989871, by rfl⟩ : syracuseStep 3986495 = 5979743) B5979743
theorem B10114145 : Blo 786339 10114145 := bstep (se 2 (by rfl) ⟨3792804, by rfl⟩ : syracuseStep 10114145 = 7585609) B7585609
theorem B3364051 : Blo 786339 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1332571 : Blo 786339 1332571 := bstep (se 1 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 1332571 = 1998857) B1998857
theorem B2250139 : Blo 786339 2250139 := bstep (se 1 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 2250139 = 3375209) B3375209
theorem B5691053 : Blo 786339 5691053 := bstep (se 3 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 5691053 = 2134145) B2134145
theorem B18241631 : Blo 786339 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B4479137 : Blo 786339 4479137 := bstep (se 2 (by rfl) ⟨1679676, by rfl⟩ : syracuseStep 4479137 = 3359353) B3359353
theorem B5986547 : Blo 786339 5986547 := bstep (se 1 (by rfl) ⟨4489910, by rfl⟩ : syracuseStep 5986547 = 8979821) B8979821
theorem B1333543 : Blo 786339 1333543 := bstep (se 1 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 1333543 = 2000315) B2000315
theorem B18209123 : Blo 786339 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B1596457 : Blo 786339 1596457 := bstep (se 2 (by rfl) ⟨598671, by rfl⟩ : syracuseStep 1596457 = 1197343) B1197343
theorem B7691321 : Blo 786339 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B14605379 : Blo 786339 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B2842067 : Blo 786339 2842067 := bstep (se 1 (by rfl) ⟨2131550, by rfl⟩ : syracuseStep 2842067 = 4263101) B4263101
theorem B12771715 : Blo 786339 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B3990383 : Blo 786339 3990383 := bstep (se 1 (by rfl) ⟨2992787, by rfl⟩ : syracuseStep 3990383 = 5985575) B5985575
theorem B1500115 : Blo 786339 1500115 := bstep (se 1 (by rfl) ⟨1125086, by rfl⟩ : syracuseStep 1500115 = 2250173) B2250173
theorem B2844271 : Blo 786339 2844271 := bstep (se 1 (by rfl) ⟨2133203, by rfl⟩ : syracuseStep 2844271 = 4266407) B4266407
theorem B4253305 : Blo 786339 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B3794651 : Blo 786339 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B4483511 : Blo 786339 4483511 := bstep (se 1 (by rfl) ⟨3362633, by rfl⟩ : syracuseStep 4483511 = 6725267) B6725267
theorem B3370031 : Blo 786339 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B12643735 : Blo 786339 12643735 := bstep (se 1 (by rfl) ⟨9482801, by rfl⟩ : syracuseStep 12643735 = 18965603) B18965603
theorem B7564697 : Blo 786339 7564697 := bstep (se 2 (by rfl) ⟨2836761, by rfl⟩ : syracuseStep 7564697 = 5673523) B5673523
theorem B5042027 : Blo 786339 5042027 := bstep (se 1 (by rfl) ⟨3781520, by rfl⟩ : syracuseStep 5042027 = 7563041) B7563041
theorem B2125723 : Blo 786339 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B1994939 : Blo 786339 1994939 := bstep (se 1 (by rfl) ⟨1496204, by rfl⟩ : syracuseStep 1994939 = 2992409) B2992409
theorem B1995425 : Blo 786339 1995425 := bstep (se 2 (by rfl) ⟨748284, by rfl⟩ : syracuseStep 1995425 = 1496569) B1496569
theorem B9106589 : Blo 786339 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B1996123 : Blo 786339 1996123 := bstep (se 1 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 1996123 = 2994185) B2994185
theorem B5404325 : Blo 786339 5404325 := bstep (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) B1013311
theorem B4486859 : Blo 786339 4486859 := bstep (se 1 (by rfl) ⟨3365144, by rfl⟩ : syracuseStep 4486859 = 6730289) B6730289
theorem B2520989 : Blo 786339 2520989 := bstep (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) B945371
theorem B25556917 : Blo 786339 25556917 := bstep (se 5 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 25556917 = 2395961) B2395961
theorem B948167 : Blo 786339 948167 := bstep (se 1 (by rfl) ⟨711125, by rfl⟩ : syracuseStep 948167 = 1422251) B1422251
theorem B1996883 : Blo 786339 1996883 := bstep (se 1 (by rfl) ⟨1497662, by rfl⟩ : syracuseStep 1996883 = 2995325) B2995325
theorem B5044589 : Blo 786339 5044589 := bstep (se 3 (by rfl) ⟨945860, by rfl⟩ : syracuseStep 5044589 = 1891721) B1891721
theorem B41613749 : Blo 786339 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B1997369 : Blo 786339 1997369 := bstep (se 2 (by rfl) ⟨749013, by rfl⟩ : syracuseStep 1997369 = 1498027) B1498027
theorem B3373721 : Blo 786339 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B4324423 : Blo 786339 4324423 := bstep (se 1 (by rfl) ⟨3243317, by rfl⟩ : syracuseStep 4324423 = 6486635) B6486635
theorem B2129161 : Blo 786339 2129161 := bstep (se 2 (by rfl) ⟨798435, by rfl⟩ : syracuseStep 2129161 = 1596871) B1596871
theorem B4488635 : Blo 786339 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B9567989 : Blo 786339 9567989 := bstep (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) B896999
theorem B1179515 : Blo 786339 1179515 := bstep (se 1 (by rfl) ⟨884636, by rfl⟩ : syracuseStep 1179515 = 1769273) B1769273
theorem B1998715 : Blo 786339 1998715 := bstep (se 1 (by rfl) ⟨1499036, by rfl⟩ : syracuseStep 1998715 = 2998073) B2998073
theorem B2129789 : Blo 786339 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B786399 : Blo 786339 786399 := bstep (se 1 (by rfl) ⟨589799, by rfl⟩ : syracuseStep 786399 = 1179599) B1179599
theorem B7274681 : Blo 786339 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B1179839 : Blo 786339 1179839 := bstep (se 1 (by rfl) ⟨884879, by rfl⟩ : syracuseStep 1179839 = 1769759) B1769759
theorem B786623 : Blo 786339 786623 := bstep (se 1 (by rfl) ⟨589967, by rfl⟩ : syracuseStep 786623 = 1179935) B1179935
theorem B786639 : Blo 786339 786639 := bstep (se 1 (by rfl) ⟨589979, by rfl⟩ : syracuseStep 786639 = 1179959) B1179959
theorem B786687 : Blo 786339 786687 := bstep (se 1 (by rfl) ⟨590015, by rfl⟩ : syracuseStep 786687 = 1180031) B1180031
theorem B786735 : Blo 786339 786735 := bstep (se 1 (by rfl) ⟨590051, by rfl⟩ : syracuseStep 786735 = 1180103) B1180103
theorem B1999151 : Blo 786339 1999151 := bstep (se 1 (by rfl) ⟨1499363, by rfl⟩ : syracuseStep 1999151 = 2998727) B2998727
theorem B786971 : Blo 786339 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B786975 : Blo 786339 786975 := bstep (se 1 (by rfl) ⟨590231, by rfl⟩ : syracuseStep 786975 = 1180463) B1180463
theorem B1180265 : Blo 786339 1180265 := bstep (se 2 (by rfl) ⟨442599, by rfl⟩ : syracuseStep 1180265 = 885199) B885199
theorem B1180271 : Blo 786339 1180271 := bstep (se 1 (by rfl) ⟨885203, by rfl⟩ : syracuseStep 1180271 = 1770407) B1770407
theorem B787055 : Blo 786339 787055 := bstep (se 1 (by rfl) ⟨590291, by rfl⟩ : syracuseStep 787055 = 1180583) B1180583
theorem B885415 : Blo 786339 885415 := bstep (se 1 (by rfl) ⟨664061, by rfl⟩ : syracuseStep 885415 = 1328123) B1328123
theorem B787111 : Blo 786339 787111 := bstep (se 1 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 787111 = 1180667) B1180667
theorem B787151 : Blo 786339 787151 := bstep (se 1 (by rfl) ⟨590363, by rfl⟩ : syracuseStep 787151 = 1180727) B1180727
theorem B787231 : Blo 786339 787231 := bstep (se 1 (by rfl) ⟨590423, by rfl⟩ : syracuseStep 787231 = 1180847) B1180847
theorem B1770281 : Blo 786339 1770281 := bstep (se 2 (by rfl) ⟨663855, by rfl⟩ : syracuseStep 1770281 = 1327711) B1327711
theorem B885703 : Blo 786339 885703 := bstep (se 1 (by rfl) ⟨664277, by rfl⟩ : syracuseStep 885703 = 1328555) B1328555
theorem B787503 : Blo 786339 787503 := bstep (se 1 (by rfl) ⟨590627, by rfl⟩ : syracuseStep 787503 = 1181255) B1181255
theorem B1770551 : Blo 786339 1770551 := bstep (se 1 (by rfl) ⟨1327913, by rfl⟩ : syracuseStep 1770551 = 2655827) B2655827
theorem B787567 : Blo 786339 787567 := bstep (se 1 (by rfl) ⟨590675, by rfl⟩ : syracuseStep 787567 = 1181351) B1181351
theorem B787623 : Blo 786339 787623 := bstep (se 1 (by rfl) ⟨590717, by rfl⟩ : syracuseStep 787623 = 1181435) B1181435
theorem B787647 : Blo 786339 787647 := bstep (se 1 (by rfl) ⟨590735, by rfl⟩ : syracuseStep 787647 = 1181471) B1181471
theorem B1180895 : Blo 786339 1180895 := bstep (se 1 (by rfl) ⟨885671, by rfl⟩ : syracuseStep 1180895 = 1771343) B1771343
theorem B787679 : Blo 786339 787679 := bstep (se 1 (by rfl) ⟨590759, by rfl⟩ : syracuseStep 787679 = 1181519) B1181519
theorem B1770731 : Blo 786339 1770731 := bstep (se 1 (by rfl) ⟨1328048, by rfl⟩ : syracuseStep 1770731 = 2656097) B2656097
theorem B1180907 : Blo 786339 1180907 := bstep (se 1 (by rfl) ⟨885680, by rfl⟩ : syracuseStep 1180907 = 1771361) B1771361
theorem B2000153 : Blo 786339 2000153 := bstep (se 2 (by rfl) ⟨750057, by rfl⟩ : syracuseStep 2000153 = 1500115) B1500115
theorem B886063 : Blo 786339 886063 := bstep (se 1 (by rfl) ⟨664547, by rfl⟩ : syracuseStep 886063 = 1329095) B1329095
theorem B787759 : Blo 786339 787759 := bstep (se 1 (by rfl) ⟨590819, by rfl⟩ : syracuseStep 787759 = 1181639) B1181639
theorem B787995 : Blo 786339 787995 := bstep (se 1 (by rfl) ⟨590996, by rfl⟩ : syracuseStep 787995 = 1181993) B1181993
theorem B787999 : Blo 786339 787999 := bstep (se 1 (by rfl) ⟨590999, by rfl⟩ : syracuseStep 787999 = 1181999) B1181999
theorem B1181291 : Blo 786339 1181291 := bstep (se 1 (by rfl) ⟨885968, by rfl⟩ : syracuseStep 1181291 = 1771937) B1771937
theorem B2655935 : Blo 786339 2655935 := bstep (se 1 (by rfl) ⟨1991951, by rfl⟩ : syracuseStep 2655935 = 3983903) B3983903
theorem B1771199 : Blo 786339 1771199 := bstep (se 1 (by rfl) ⟨1328399, by rfl⟩ : syracuseStep 1771199 = 2656799) B2656799
theorem B1181375 : Blo 786339 1181375 := bstep (se 1 (by rfl) ⟨886031, by rfl⟩ : syracuseStep 1181375 = 1772063) B1772063
theorem B788159 : Blo 786339 788159 := bstep (se 1 (by rfl) ⟨591119, by rfl⟩ : syracuseStep 788159 = 1182239) B1182239
theorem B5048075 : Blo 786339 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B886567 : Blo 786339 886567 := bstep (se 1 (by rfl) ⟨664925, by rfl⟩ : syracuseStep 886567 = 1329851) B1329851
theorem B1181561 : Blo 786339 1181561 := bstep (se 2 (by rfl) ⟨443085, by rfl⟩ : syracuseStep 1181561 = 886171) B886171
theorem B10127267 : Blo 786339 10127267 := bstep (se 1 (by rfl) ⟨7595450, by rfl⟩ : syracuseStep 10127267 = 15190901) B15190901
theorem B788415 : Blo 786339 788415 := bstep (se 1 (by rfl) ⟨591311, by rfl⟩ : syracuseStep 788415 = 1182623) B1182623
theorem B788447 : Blo 786339 788447 := bstep (se 1 (by rfl) ⟨591335, by rfl⟩ : syracuseStep 788447 = 1182671) B1182671
theorem B788507 : Blo 786339 788507 := bstep (se 1 (by rfl) ⟨591380, by rfl⟩ : syracuseStep 788507 = 1182761) B1182761
theorem B788511 : Blo 786339 788511 := bstep (se 1 (by rfl) ⟨591383, by rfl⟩ : syracuseStep 788511 = 1182767) B1182767
theorem B788527 : Blo 786339 788527 := bstep (se 1 (by rfl) ⟨591395, by rfl⟩ : syracuseStep 788527 = 1182791) B1182791
theorem B5671073 : Blo 786339 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B28772549 : Blo 786339 28772549 := bstep (se 4 (by rfl) ⟨2697426, by rfl⟩ : syracuseStep 28772549 = 5394853) B5394853
theorem B788703 : Blo 786339 788703 := bstep (se 1 (by rfl) ⟨591527, by rfl⟩ : syracuseStep 788703 = 1183055) B1183055
theorem B788763 : Blo 786339 788763 := bstep (se 1 (by rfl) ⟨591572, by rfl⟩ : syracuseStep 788763 = 1183145) B1183145
theorem B6490409 : Blo 786339 6490409 := bstep (se 2 (by rfl) ⟨2433903, by rfl⟩ : syracuseStep 6490409 = 4867807) B4867807
theorem B788863 : Blo 786339 788863 := bstep (se 1 (by rfl) ⟨591647, by rfl⟩ : syracuseStep 788863 = 1183295) B1183295
theorem B789039 : Blo 786339 789039 := bstep (se 1 (by rfl) ⟨591779, by rfl⟩ : syracuseStep 789039 = 1183559) B1183559
theorem B1772135 : Blo 786339 1772135 := bstep (se 1 (by rfl) ⟨1329101, by rfl⟩ : syracuseStep 1772135 = 2658203) B2658203
theorem B1182311 : Blo 786339 1182311 := bstep (se 1 (by rfl) ⟨886733, by rfl⟩ : syracuseStep 1182311 = 1773467) B1773467
theorem B789095 : Blo 786339 789095 := bstep (se 1 (by rfl) ⟨591821, by rfl⟩ : syracuseStep 789095 = 1183643) B1183643
theorem B1182503 : Blo 786339 1182503 := bstep (se 1 (by rfl) ⟨886877, by rfl⟩ : syracuseStep 1182503 = 1773755) B1773755
theorem B789471 : Blo 786339 789471 := bstep (se 1 (by rfl) ⟨592103, by rfl⟩ : syracuseStep 789471 = 1184207) B1184207
theorem B1772513 : Blo 786339 1772513 := bstep (se 2 (by rfl) ⟨664692, by rfl⟩ : syracuseStep 1772513 = 1329385) B1329385
theorem B789499 : Blo 786339 789499 := bstep (se 1 (by rfl) ⟨592124, by rfl⟩ : syracuseStep 789499 = 1184249) B1184249
theorem B9571391 : Blo 786339 9571391 := bstep (se 1 (by rfl) ⟨7178543, by rfl⟩ : syracuseStep 9571391 = 14357087) B14357087
theorem B789567 : Blo 786339 789567 := bstep (se 1 (by rfl) ⟨592175, by rfl⟩ : syracuseStep 789567 = 1184351) B1184351
theorem B1182827 : Blo 786339 1182827 := bstep (se 1 (by rfl) ⟨887120, by rfl⟩ : syracuseStep 1182827 = 1774241) B1774241
theorem B2526395 : Blo 786339 2526395 := bstep (se 1 (by rfl) ⟨1894796, by rfl⟩ : syracuseStep 2526395 = 3789593) B3789593
theorem B12782879 : Blo 786339 12782879 := bstep (se 1 (by rfl) ⟨9587159, by rfl⟩ : syracuseStep 12782879 = 19174319) B19174319
theorem B1772891 : Blo 786339 1772891 := bstep (se 1 (by rfl) ⟨1329668, by rfl⟩ : syracuseStep 1772891 = 2659337) B2659337
theorem B1183067 : Blo 786339 1183067 := bstep (se 1 (by rfl) ⟨887300, by rfl⟩ : syracuseStep 1183067 = 1774601) B1774601
theorem B1183097 : Blo 786339 1183097 := bstep (se 2 (by rfl) ⟨443661, by rfl⟩ : syracuseStep 1183097 = 887323) B887323
theorem B2657663 : Blo 786339 2657663 := bstep (se 1 (by rfl) ⟨1993247, by rfl⟩ : syracuseStep 2657663 = 3986495) B3986495
theorem B1772927 : Blo 786339 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B1183103 : Blo 786339 1183103 := bstep (se 1 (by rfl) ⟨887327, by rfl⟩ : syracuseStep 1183103 = 1774655) B1774655
theorem B789887 : Blo 786339 789887 := bstep (se 1 (by rfl) ⟨592415, by rfl⟩ : syracuseStep 789887 = 1184831) B1184831
theorem B789915 : Blo 786339 789915 := bstep (se 1 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 789915 = 1184873) B1184873
theorem B789983 : Blo 786339 789983 := bstep (se 1 (by rfl) ⟨592487, by rfl⟩ : syracuseStep 789983 = 1184975) B1184975
theorem B790119 : Blo 786339 790119 := bstep (se 1 (by rfl) ⟨592589, by rfl⟩ : syracuseStep 790119 = 1185179) B1185179
theorem B790267 : Blo 786339 790267 := bstep (se 1 (by rfl) ⟨592700, by rfl⟩ : syracuseStep 790267 = 1185401) B1185401
theorem B790335 : Blo 786339 790335 := bstep (se 1 (by rfl) ⟨592751, by rfl⟩ : syracuseStep 790335 = 1185503) B1185503
theorem B1183727 : Blo 786339 1183727 := bstep (se 1 (by rfl) ⟨887795, by rfl⟩ : syracuseStep 1183727 = 1775591) B1775591
theorem B1183739 : Blo 786339 1183739 := bstep (se 1 (by rfl) ⟨887804, by rfl⟩ : syracuseStep 1183739 = 1775609) B1775609
theorem B1183799 : Blo 786339 1183799 := bstep (se 1 (by rfl) ⟨887849, by rfl⟩ : syracuseStep 1183799 = 1775699) B1775699
theorem B12161087 : Blo 786339 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B1183847 : Blo 786339 1183847 := bstep (se 1 (by rfl) ⟨887885, by rfl⟩ : syracuseStep 1183847 = 1775771) B1775771
theorem B2986091 : Blo 786339 2986091 := bstep (se 1 (by rfl) ⟨2239568, by rfl⟩ : syracuseStep 2986091 = 4479137) B4479137
theorem B1183919 : Blo 786339 1183919 := bstep (se 1 (by rfl) ⟨887939, by rfl⟩ : syracuseStep 1183919 = 1775879) B1775879
theorem B1184123 : Blo 786339 1184123 := bstep (se 1 (by rfl) ⟨888092, by rfl⟩ : syracuseStep 1184123 = 1776185) B1776185
theorem B4788809 : Blo 786339 4788809 := bstep (se 2 (by rfl) ⟨1795803, by rfl⟩ : syracuseStep 4788809 = 3591607) B3591607
theorem B2986577 : Blo 786339 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B1184393 : Blo 786339 1184393 := bstep (se 2 (by rfl) ⟨444147, by rfl⟩ : syracuseStep 1184393 = 888295) B888295
theorem B9736919 : Blo 786339 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B1184603 : Blo 786339 1184603 := bstep (se 1 (by rfl) ⟨888452, by rfl⟩ : syracuseStep 1184603 = 1776905) B1776905
theorem B1774799 : Blo 786339 1774799 := bstep (se 1 (by rfl) ⟨1331099, by rfl⟩ : syracuseStep 1774799 = 2662199) B2662199
theorem B4035881 : Blo 786339 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B1774889 : Blo 786339 1774889 := bstep (se 2 (by rfl) ⟨665583, by rfl⟩ : syracuseStep 1774889 = 1331167) B1331167
theorem B1185065 : Blo 786339 1185065 := bstep (se 2 (by rfl) ⟨444399, by rfl⟩ : syracuseStep 1185065 = 888799) B888799
theorem B1775087 : Blo 786339 1775087 := bstep (se 1 (by rfl) ⟨1331315, by rfl⟩ : syracuseStep 1775087 = 2662631) B2662631
theorem B1185263 : Blo 786339 1185263 := bstep (se 1 (by rfl) ⟨888947, by rfl⟩ : syracuseStep 1185263 = 1777895) B1777895
theorem B1775483 : Blo 786339 1775483 := bstep (se 1 (by rfl) ⟨1331612, by rfl⟩ : syracuseStep 1775483 = 2663225) B2663225
theorem B2660255 : Blo 786339 2660255 := bstep (se 1 (by rfl) ⟨1995191, by rfl⟩ : syracuseStep 2660255 = 3990383) B3990383
theorem B1775519 : Blo 786339 1775519 := bstep (se 1 (by rfl) ⟨1331639, by rfl⟩ : syracuseStep 1775519 = 2663279) B2663279
theorem B1775753 : Blo 786339 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B83106137 : Blo 786339 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B1775969 : Blo 786339 1775969 := bstep (se 2 (by rfl) ⟨665988, by rfl⟩ : syracuseStep 1775969 = 1331977) B1331977
theorem B1776059 : Blo 786339 1776059 := bstep (se 1 (by rfl) ⟨1332044, by rfl⟩ : syracuseStep 1776059 = 2664089) B2664089
theorem B2529767 : Blo 786339 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B1776455 : Blo 786339 1776455 := bstep (se 1 (by rfl) ⟨1332341, by rfl⟩ : syracuseStep 1776455 = 2664683) B2664683
theorem B2989007 : Blo 786339 2989007 := bstep (se 1 (by rfl) ⟨2241755, by rfl⟩ : syracuseStep 2989007 = 4483511) B4483511
theorem B2661497 : Blo 786339 2661497 := bstep (se 2 (by rfl) ⟨998061, by rfl⟩ : syracuseStep 2661497 = 1996123) B1996123
theorem B1776761 : Blo 786339 1776761 := bstep (se 2 (by rfl) ⟨666285, by rfl⟩ : syracuseStep 1776761 = 1332571) B1332571
theorem B1777319 : Blo 786339 1777319 := bstep (se 1 (by rfl) ⟨1332989, by rfl⟩ : syracuseStep 1777319 = 2665979) B2665979
theorem B1777427 : Blo 786339 1777427 := bstep (se 1 (by rfl) ⟨1333070, by rfl⟩ : syracuseStep 1777427 = 2666141) B2666141
theorem B5407343 : Blo 786339 5407343 := bstep (se 1 (by rfl) ⟨4055507, by rfl⟩ : syracuseStep 5407343 = 8111015) B8111015
theorem B1777787 : Blo 786339 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B1679753 : Blo 786339 1679753 := bstep (se 2 (by rfl) ⟨629907, by rfl⟩ : syracuseStep 1679753 = 1259815) B1259815
theorem B1778057 : Blo 786339 1778057 := bstep (se 2 (by rfl) ⟨666771, by rfl⟩ : syracuseStep 1778057 = 1333543) B1333543
theorem B6071059 : Blo 786339 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B2991239 : Blo 786339 2991239 := bstep (se 1 (by rfl) ⟨2243429, by rfl⟩ : syracuseStep 2991239 = 4486859) B4486859
theorem B7578845 : Blo 786339 7578845 := bstep (se 3 (by rfl) ⟨1421033, by rfl⟩ : syracuseStep 7578845 = 2842067) B2842067
theorem B1680659 : Blo 786339 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B18950071 : Blo 786339 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B2992423 : Blo 786339 2992423 := bstep (se 1 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 2992423 = 4488635) B4488635
theorem B5974397 : Blo 786339 5974397 := bstep (se 3 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 5974397 = 2240399) B2240399
theorem B2664953 : Blo 786339 2664953 := bstep (se 2 (by rfl) ⟨999357, by rfl⟩ : syracuseStep 2664953 = 1998715) B1998715
theorem B2992697 : Blo 786339 2992697 := bstep (se 2 (by rfl) ⟨1122261, by rfl⟩ : syracuseStep 2992697 = 2244523) B2244523
theorem B1419859 : Blo 786339 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B2665223 : Blo 786339 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B2665439 : Blo 786339 2665439 := bstep (se 1 (by rfl) ⟨1999079, by rfl⟩ : syracuseStep 2665439 = 3998159) B3998159
theorem B2665601 : Blo 786339 2665601 := bstep (se 2 (by rfl) ⟨999600, by rfl⟩ : syracuseStep 2665601 = 1999201) B1999201
theorem B2993395 : Blo 786339 2993395 := bstep (se 1 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 2993395 = 4490093) B4490093
theorem B4500755 : Blo 786339 4500755 := bstep (se 1 (by rfl) ⟨3375566, by rfl⟩ : syracuseStep 4500755 = 6751133) B6751133
theorem B2666303 : Blo 786339 2666303 := bstep (se 1 (by rfl) ⟨1999727, by rfl⟩ : syracuseStep 2666303 = 3999455) B3999455
theorem B2666411 : Blo 786339 2666411 := bstep (se 1 (by rfl) ⟨1999808, by rfl⟩ : syracuseStep 2666411 = 3999617) B3999617
theorem B11809223 : Blo 786339 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B2666951 : Blo 786339 2666951 := bstep (se 1 (by rfl) ⟨2000213, by rfl⟩ : syracuseStep 2666951 = 4000427) B4000427
theorem B5059351 : Blo 786339 5059351 := bstep (se 1 (by rfl) ⟨3794513, by rfl⟩ : syracuseStep 5059351 = 7589027) B7589027
theorem B1684435 : Blo 786339 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B2241607 : Blo 786339 2241607 := bstep (se 1 (by rfl) ⟨1681205, by rfl⟩ : syracuseStep 2241607 = 3362411) B3362411
theorem B2241665 : Blo 786339 2241665 := bstep (se 2 (by rfl) ⟨840624, by rfl⟩ : syracuseStep 2241665 = 1681249) B1681249
theorem B2995643 : Blo 786339 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B13285571 : Blo 786339 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B6732679 : Blo 786339 6732679 := bstep (se 1 (by rfl) ⟨5049509, by rfl⟩ : syracuseStep 6732679 = 10099019) B10099019
theorem B12139415 : Blo 786339 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B16858313 : Blo 786339 16858313 := bstep (se 2 (by rfl) ⟨6321867, by rfl⟩ : syracuseStep 16858313 = 12643735) B12643735
theorem B3783905 : Blo 786339 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B3194099 : Blo 786339 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B5127547 : Blo 786339 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B2834297 : Blo 786339 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B6734015 : Blo 786339 6734015 := bstep (se 1 (by rfl) ⟨5050511, by rfl⟩ : syracuseStep 6734015 = 10101023) B10101023
theorem B3982121 : Blo 786339 3982121 := bstep (se 2 (by rfl) ⟨1493295, by rfl⟩ : syracuseStep 3982121 = 2986591) B2986591
theorem B3785903 : Blo 786339 3785903 := bstep (se 1 (by rfl) ⟨2839427, by rfl⟩ : syracuseStep 3785903 = 5678855) B5678855
theorem B2999531 : Blo 786339 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B9094765 : Blo 786339 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B3000185 : Blo 786339 3000185 := bstep (se 2 (by rfl) ⟨1125069, by rfl⟩ : syracuseStep 3000185 = 2250139) B2250139
theorem B2246687 : Blo 786339 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B1493417 : Blo 786339 1493417 := bstep (se 2 (by rfl) ⟨560031, by rfl⟩ : syracuseStep 1493417 = 1120063) B1120063
theorem B3361351 : Blo 786339 3361351 := bstep (se 1 (by rfl) ⟨2521013, by rfl⟩ : syracuseStep 3361351 = 5042027) B5042027
theorem B1329959 : Blo 786339 1329959 := bstep (se 1 (by rfl) ⟨997469, by rfl⟩ : syracuseStep 1329959 = 1994939) B1994939
theorem B2247689 : Blo 786339 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B1330283 : Blo 786339 1330283 := bstep (se 1 (by rfl) ⟨997712, by rfl⟩ : syracuseStep 1330283 = 1995425) B1995425
theorem B1330553 : Blo 786339 1330553 := bstep (se 2 (by rfl) ⟨498957, by rfl⟩ : syracuseStep 1330553 = 997915) B997915
theorem B7589335 : Blo 786339 7589335 := bstep (se 1 (by rfl) ⟨5692001, by rfl⟩ : syracuseStep 7589335 = 11384003) B11384003
theorem B57003587 : Blo 786339 57003587 := bstep (se 1 (by rfl) ⟨42752690, by rfl⟩ : syracuseStep 57003587 = 85505381) B85505381
theorem B207867653 : Blo 786339 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B1331255 : Blo 786339 1331255 := bstep (se 1 (by rfl) ⟨998441, by rfl⟩ : syracuseStep 1331255 = 1996883) B1996883
theorem B3363059 : Blo 786339 3363059 := bstep (se 1 (by rfl) ⟨2522294, by rfl⟩ : syracuseStep 3363059 = 5044589) B5044589
theorem B27742499 : Blo 786339 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B2838881 : Blo 786339 2838881 := bstep (se 2 (by rfl) ⟨1064580, by rfl⟩ : syracuseStep 2838881 = 2129161) B2129161
theorem B1331579 : Blo 786339 1331579 := bstep (se 1 (by rfl) ⟨998684, by rfl⟩ : syracuseStep 1331579 = 1997369) B1997369
theorem B2249147 : Blo 786339 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B1331849 : Blo 786339 1331849 := bstep (se 2 (by rfl) ⟨499443, by rfl⟩ : syracuseStep 1331849 = 998887) B998887
theorem B10113781 : Blo 786339 10113781 := bstep (se 5 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 10113781 = 948167) B948167
theorem B840799 : Blo 786339 840799 := bstep (se 1 (by rfl) ⟨630599, by rfl⟩ : syracuseStep 840799 = 1261199) B1261199
theorem B6378659 : Blo 786339 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B1823951 : Blo 786339 1823951 := bstep (se 1 (by rfl) ⟨1367963, by rfl⟩ : syracuseStep 1823951 = 2735927) B2735927
theorem B2839805 : Blo 786339 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B1496713 : Blo 786339 1496713 := bstep (se 2 (by rfl) ⟨561267, by rfl⟩ : syracuseStep 1496713 = 1122535) B1122535
theorem B17028953 : Blo 786339 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B1890145 : Blo 786339 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B11360249 : Blo 786339 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B841799 : Blo 786339 841799 := bstep (se 1 (by rfl) ⟨631349, by rfl⟩ : syracuseStep 841799 = 1262699) B1262699
theorem B12802333 : Blo 786339 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B331897175 : Blo 786339 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B1497503 : Blo 786339 1497503 := bstep (se 1 (by rfl) ⟨1123127, by rfl⟩ : syracuseStep 1497503 = 2246255) B2246255
theorem B1891183 : Blo 786339 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B13458797 : Blo 786339 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B3792361 : Blo 786339 3792361 := bstep (se 2 (by rfl) ⟨1422135, by rfl⟩ : syracuseStep 3792361 = 2844271) B2844271
theorem B1793609 : Blo 786339 1793609 := bstep (se 2 (by rfl) ⟨672603, by rfl⟩ : syracuseStep 1793609 = 1345207) B1345207
theorem B1892251 : Blo 786339 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B12804155 : Blo 786339 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B6054011 : Blo 786339 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B1499447 : Blo 786339 1499447 := bstep (se 1 (by rfl) ⟨1124585, by rfl⟩ : syracuseStep 1499447 = 2249171) B2249171
theorem B6054311 : Blo 786339 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B18211331 : Blo 786339 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B1991375 : Blo 786339 1991375 := bstep (se 1 (by rfl) ⟨1493531, by rfl⟩ : syracuseStep 1991375 = 2987063) B2987063
theorem B6742763 : Blo 786339 6742763 := bstep (se 1 (by rfl) ⟨5057072, by rfl⟩ : syracuseStep 6742763 = 10114145) B10114145
theorem B3794035 : Blo 786339 3794035 := bstep (se 1 (by rfl) ⟨2845526, by rfl⟩ : syracuseStep 3794035 = 5691053) B5691053
theorem B3991031 : Blo 786339 3991031 := bstep (se 1 (by rfl) ⟨2993273, by rfl⟩ : syracuseStep 3991031 = 5986547) B5986547
theorem B3368699 : Blo 786339 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B14411533 : Blo 786339 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B6744161 : Blo 786339 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B1534073 : Blo 786339 1534073 := bstep (se 2 (by rfl) ⟨575277, by rfl⟩ : syracuseStep 1534073 = 1150555) B1150555
theorem B11364745 : Blo 786339 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B1993207 : Blo 786339 1993207 := bstep (se 1 (by rfl) ⟨1494905, by rfl⟩ : syracuseStep 1993207 = 2989811) B2989811
theorem B10120139 : Blo 786339 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B7564423 : Blo 786339 7564423 := bstep (se 1 (by rfl) ⟨5673317, by rfl⟩ : syracuseStep 7564423 = 11346635) B11346635
theorem B43085267 : Blo 786339 43085267 := bstep (se 1 (by rfl) ⟨32313950, by rfl⟩ : syracuseStep 43085267 = 64627901) B64627901
theorem B7303085 : Blo 786339 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B3993785 : Blo 786339 3993785 := bstep (se 2 (by rfl) ⟨1497669, by rfl⟩ : syracuseStep 3993785 = 2995339) B2995339
theorem B7565501 : Blo 786339 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B4485401 : Blo 786339 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B5043131 : Blo 786339 5043131 := bstep (se 1 (by rfl) ⟨3782348, by rfl⟩ : syracuseStep 5043131 = 7564697) B7564697
theorem B34075889 : Blo 786339 34075889 := bstep (se 2 (by rfl) ⟨12778458, by rfl⟩ : syracuseStep 34075889 = 25556917) B25556917
theorem B7566655 : Blo 786339 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B947803 : Blo 786339 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B7272337 : Blo 786339 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B7698341 : Blo 786339 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B2128609 : Blo 786339 2128609 := bstep (se 2 (by rfl) ⟨798228, by rfl⟩ : syracuseStep 2128609 = 1596457) B1596457
theorem B5765897 : Blo 786339 5765897 := bstep (se 2 (by rfl) ⟨2162211, by rfl⟩ : syracuseStep 5765897 = 4324423) B4324423
theorem B4488317 : Blo 786339 4488317 := bstep (se 3 (by rfl) ⟨841559, by rfl⟩ : syracuseStep 4488317 = 1683119) B1683119
theorem B1998047 : Blo 786339 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B2653991 : Blo 786339 2653991 := bstep (se 1 (by rfl) ⟨1990493, by rfl⟩ : syracuseStep 2653991 = 3980987) B3980987
theorem B786343 : Blo 786339 786343 := bstep (se 1 (by rfl) ⟨589757, by rfl⟩ : syracuseStep 786343 = 1179515) B1179515
theorem B4849787 : Blo 786339 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B786559 : Blo 786339 786559 := bstep (se 1 (by rfl) ⟨589919, by rfl⟩ : syracuseStep 786559 = 1179839) B1179839
theorem B4489343 : Blo 786339 4489343 := bstep (se 1 (by rfl) ⟨3367007, by rfl⟩ : syracuseStep 4489343 = 6734015) B6734015
theorem B786843 : Blo 786339 786843 := bstep (se 1 (by rfl) ⟨590132, by rfl⟩ : syracuseStep 786843 = 1180265) B1180265
theorem B786847 : Blo 786339 786847 := bstep (se 1 (by rfl) ⟨590135, by rfl⟩ : syracuseStep 786847 = 1180271) B1180271
theorem B3604895 : Blo 786339 3604895 := bstep (se 1 (by rfl) ⟨2703671, by rfl⟩ : syracuseStep 3604895 = 5407343) B5407343
theorem B2654747 : Blo 786339 2654747 := bstep (se 1 (by rfl) ⟨1991060, by rfl⟩ : syracuseStep 2654747 = 3982121) B3982121
theorem B1180187 : Blo 786339 1180187 := bstep (se 1 (by rfl) ⟨885140, by rfl⟩ : syracuseStep 1180187 = 1770281) B1770281
theorem B1180367 : Blo 786339 1180367 := bstep (se 1 (by rfl) ⟨885275, by rfl⟩ : syracuseStep 1180367 = 1770551) B1770551
theorem B2523935 : Blo 786339 2523935 := bstep (se 1 (by rfl) ⟨1892951, by rfl⟩ : syracuseStep 2523935 = 3785903) B3785903
theorem B787263 : Blo 786339 787263 := bstep (se 1 (by rfl) ⟨590447, by rfl⟩ : syracuseStep 787263 = 1180895) B1180895
theorem B1180487 : Blo 786339 1180487 := bstep (se 1 (by rfl) ⟨885365, by rfl⟩ : syracuseStep 1180487 = 1770731) B1770731
theorem B787271 : Blo 786339 787271 := bstep (se 1 (by rfl) ⟨590453, by rfl⟩ : syracuseStep 787271 = 1180907) B1180907
theorem B1999687 : Blo 786339 1999687 := bstep (se 1 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 1999687 = 2999531) B2999531
theorem B1180553 : Blo 786339 1180553 := bstep (se 2 (by rfl) ⟨442707, by rfl⟩ : syracuseStep 1180553 = 885415) B885415
theorem B8094745 : Blo 786339 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B787527 : Blo 786339 787527 := bstep (se 1 (by rfl) ⟨590645, by rfl⟩ : syracuseStep 787527 = 1181291) B1181291
theorem B1770623 : Blo 786339 1770623 := bstep (se 1 (by rfl) ⟨1327967, by rfl⟩ : syracuseStep 1770623 = 2655935) B2655935
theorem B1180799 : Blo 786339 1180799 := bstep (se 1 (by rfl) ⟨885599, by rfl⟩ : syracuseStep 1180799 = 1771199) B1771199
theorem B787583 : Blo 786339 787583 := bstep (se 1 (by rfl) ⟨590687, by rfl⟩ : syracuseStep 787583 = 1181375) B1181375
theorem B5997725 : Blo 786339 5997725 := bstep (se 3 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 5997725 = 2249147) B2249147
theorem B787707 : Blo 786339 787707 := bstep (se 1 (by rfl) ⟨590780, by rfl⟩ : syracuseStep 787707 = 1181561) B1181561
theorem B2000123 : Blo 786339 2000123 := bstep (se 1 (by rfl) ⟨1500092, by rfl⟩ : syracuseStep 2000123 = 3000185) B3000185
theorem B1180937 : Blo 786339 1180937 := bstep (se 2 (by rfl) ⟨442851, by rfl⟩ : syracuseStep 1180937 = 885703) B885703
theorem B6751511 : Blo 786339 6751511 := bstep (se 1 (by rfl) ⟨5063633, by rfl⟩ : syracuseStep 6751511 = 10127267) B10127267
theorem B1181417 : Blo 786339 1181417 := bstep (se 2 (by rfl) ⟨443031, by rfl⟩ : syracuseStep 1181417 = 886063) B886063
theorem B1181423 : Blo 786339 1181423 := bstep (se 1 (by rfl) ⟨886067, by rfl⟩ : syracuseStep 1181423 = 1772135) B1772135
theorem B788207 : Blo 786339 788207 := bstep (se 1 (by rfl) ⟨591155, by rfl⟩ : syracuseStep 788207 = 1182311) B1182311
theorem B886639 : Blo 786339 886639 := bstep (se 1 (by rfl) ⟨664979, by rfl⟩ : syracuseStep 886639 = 1329959) B1329959
theorem B788335 : Blo 786339 788335 := bstep (se 1 (by rfl) ⟨591251, by rfl⟩ : syracuseStep 788335 = 1182503) B1182503
theorem B1181675 : Blo 786339 1181675 := bstep (se 1 (by rfl) ⟨886256, by rfl⟩ : syracuseStep 1181675 = 1772513) B1772513
theorem B886855 : Blo 786339 886855 := bstep (se 1 (by rfl) ⟨665141, by rfl⟩ : syracuseStep 886855 = 1330283) B1330283
theorem B788551 : Blo 786339 788551 := bstep (se 1 (by rfl) ⟨591413, by rfl⟩ : syracuseStep 788551 = 1182827) B1182827
theorem B12126353 : Blo 786339 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B8521919 : Blo 786339 8521919 := bstep (se 1 (by rfl) ⟨6391439, by rfl⟩ : syracuseStep 8521919 = 12782879) B12782879
theorem B1181927 : Blo 786339 1181927 := bstep (se 1 (by rfl) ⟨886445, by rfl⟩ : syracuseStep 1181927 = 1772891) B1772891
theorem B788711 : Blo 786339 788711 := bstep (se 1 (by rfl) ⟨591533, by rfl⟩ : syracuseStep 788711 = 1183067) B1183067
theorem B887035 : Blo 786339 887035 := bstep (se 1 (by rfl) ⟨665276, by rfl⟩ : syracuseStep 887035 = 1330553) B1330553
theorem B788731 : Blo 786339 788731 := bstep (se 1 (by rfl) ⟨591548, by rfl⟩ : syracuseStep 788731 = 1183097) B1183097
theorem B1771775 : Blo 786339 1771775 := bstep (se 1 (by rfl) ⟨1328831, by rfl⟩ : syracuseStep 1771775 = 2657663) B2657663
theorem B1181951 : Blo 786339 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B788735 : Blo 786339 788735 := bstep (se 1 (by rfl) ⟨591551, by rfl⟩ : syracuseStep 788735 = 1183103) B1183103
theorem B1182089 : Blo 786339 1182089 := bstep (se 2 (by rfl) ⟨443283, by rfl⟩ : syracuseStep 1182089 = 886567) B886567
theorem B138578435 : Blo 786339 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B25266761 : Blo 786339 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B789151 : Blo 786339 789151 := bstep (se 1 (by rfl) ⟨591863, by rfl⟩ : syracuseStep 789151 = 1183727) B1183727
theorem B789159 : Blo 786339 789159 := bstep (se 1 (by rfl) ⟨591869, by rfl⟩ : syracuseStep 789159 = 1183739) B1183739
theorem B887503 : Blo 786339 887503 := bstep (se 1 (by rfl) ⟨665627, by rfl⟩ : syracuseStep 887503 = 1331255) B1331255
theorem B789199 : Blo 786339 789199 := bstep (se 1 (by rfl) ⟨591899, by rfl⟩ : syracuseStep 789199 = 1183799) B1183799
theorem B789231 : Blo 786339 789231 := bstep (se 1 (by rfl) ⟨591923, by rfl⟩ : syracuseStep 789231 = 1183847) B1183847
theorem B789279 : Blo 786339 789279 := bstep (se 1 (by rfl) ⟨591959, by rfl⟩ : syracuseStep 789279 = 1183919) B1183919
theorem B887719 : Blo 786339 887719 := bstep (se 1 (by rfl) ⟨665789, by rfl⟩ : syracuseStep 887719 = 1331579) B1331579
theorem B789415 : Blo 786339 789415 := bstep (se 1 (by rfl) ⟨592061, by rfl⟩ : syracuseStep 789415 = 1184123) B1184123
theorem B887899 : Blo 786339 887899 := bstep (se 1 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 887899 = 1331849) B1331849
theorem B789595 : Blo 786339 789595 := bstep (se 1 (by rfl) ⟨592196, by rfl⟩ : syracuseStep 789595 = 1184393) B1184393
theorem B6491279 : Blo 786339 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B789735 : Blo 786339 789735 := bstep (se 1 (by rfl) ⟨592301, by rfl⟩ : syracuseStep 789735 = 1184603) B1184603
theorem B2657609 : Blo 786339 2657609 := bstep (se 2 (by rfl) ⟨996603, by rfl⟩ : syracuseStep 2657609 = 1993207) B1993207
theorem B1183199 : Blo 786339 1183199 := bstep (se 1 (by rfl) ⟨887399, by rfl⟩ : syracuseStep 1183199 = 1774799) B1774799
theorem B1215967 : Blo 786339 1215967 := bstep (se 1 (by rfl) ⟨911975, by rfl⟩ : syracuseStep 1215967 = 1823951) B1823951
theorem B2690587 : Blo 786339 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B1183259 : Blo 786339 1183259 := bstep (se 1 (by rfl) ⟨887444, by rfl⟩ : syracuseStep 1183259 = 1774889) B1774889
theorem B790043 : Blo 786339 790043 := bstep (se 1 (by rfl) ⟨592532, by rfl⟩ : syracuseStep 790043 = 1185065) B1185065
theorem B1183391 : Blo 786339 1183391 := bstep (se 1 (by rfl) ⟨887543, by rfl⟩ : syracuseStep 1183391 = 1775087) B1775087
theorem B790175 : Blo 786339 790175 := bstep (se 1 (by rfl) ⟨592631, by rfl⟩ : syracuseStep 790175 = 1185263) B1185263
theorem B1183655 : Blo 786339 1183655 := bstep (se 1 (by rfl) ⟨887741, by rfl⟩ : syracuseStep 1183655 = 1775483) B1775483
theorem B1773503 : Blo 786339 1773503 := bstep (se 1 (by rfl) ⟨1330127, by rfl⟩ : syracuseStep 1773503 = 2660255) B2660255
theorem B1183679 : Blo 786339 1183679 := bstep (se 1 (by rfl) ⟨887759, by rfl⟩ : syracuseStep 1183679 = 1775519) B1775519
theorem B7573499 : Blo 786339 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1183835 : Blo 786339 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B1183979 : Blo 786339 1183979 := bstep (se 1 (by rfl) ⟨887984, by rfl⟩ : syracuseStep 1183979 = 1775969) B1775969
theorem B1184039 : Blo 786339 1184039 := bstep (se 1 (by rfl) ⟨888029, by rfl⟩ : syracuseStep 1184039 = 1776059) B1776059
theorem B1184303 : Blo 786339 1184303 := bstep (se 1 (by rfl) ⟨888227, by rfl⟩ : syracuseStep 1184303 = 1776455) B1776455
theorem B1774331 : Blo 786339 1774331 := bstep (se 1 (by rfl) ⟨1330748, by rfl⟩ : syracuseStep 1774331 = 2661497) B2661497
theorem B1184507 : Blo 786339 1184507 := bstep (se 1 (by rfl) ⟨888380, by rfl⟩ : syracuseStep 1184507 = 1776761) B1776761
theorem B1184879 : Blo 786339 1184879 := bstep (se 1 (by rfl) ⟨888659, by rfl⟩ : syracuseStep 1184879 = 1777319) B1777319
theorem B1184951 : Blo 786339 1184951 := bstep (se 1 (by rfl) ⟨888713, by rfl⟩ : syracuseStep 1184951 = 1777427) B1777427
theorem B4036007 : Blo 786339 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B1185191 : Blo 786339 1185191 := bstep (se 1 (by rfl) ⟨888893, by rfl⟩ : syracuseStep 1185191 = 1777787) B1777787
theorem B1119835 : Blo 786339 1119835 := bstep (se 1 (by rfl) ⟨839876, by rfl⟩ : syracuseStep 1119835 = 1679753) B1679753
theorem B1185371 : Blo 786339 1185371 := bstep (se 1 (by rfl) ⟨889028, by rfl⟩ : syracuseStep 1185371 = 1778057) B1778057
theorem B4495175 : Blo 786339 4495175 := bstep (se 1 (by rfl) ⟨3371381, by rfl⟩ : syracuseStep 4495175 = 6742763) B6742763
theorem B17307757 : Blo 786339 17307757 := bstep (se 3 (by rfl) ⟨3245204, by rfl⟩ : syracuseStep 17307757 = 6490409) B6490409
theorem B5052563 : Blo 786339 5052563 := bstep (se 1 (by rfl) ⟨3789422, by rfl⟩ : syracuseStep 5052563 = 7578845) B7578845
theorem B1120439 : Blo 786339 1120439 := bstep (se 1 (by rfl) ⟨840329, by rfl⟩ : syracuseStep 1120439 = 1680659) B1680659
theorem B2660687 : Blo 786339 2660687 := bstep (se 1 (by rfl) ⟨1995515, by rfl⟩ : syracuseStep 2660687 = 3991031) B3991031
theorem B4496107 : Blo 786339 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B2988809 : Blo 786339 2988809 := bstep (se 2 (by rfl) ⟨1120803, by rfl⟩ : syracuseStep 2988809 = 2241607) B2241607
theorem B1776635 : Blo 786339 1776635 := bstep (se 1 (by rfl) ⟨1332476, by rfl⟩ : syracuseStep 1776635 = 2664953) B2664953
theorem B1776815 : Blo 786339 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B1776959 : Blo 786339 1776959 := bstep (se 1 (by rfl) ⟨1332719, by rfl⟩ : syracuseStep 1776959 = 2665439) B2665439
theorem B1777067 : Blo 786339 1777067 := bstep (se 1 (by rfl) ⟨1332800, by rfl⟩ : syracuseStep 1777067 = 2665601) B2665601
theorem B1777535 : Blo 786339 1777535 := bstep (se 1 (by rfl) ⟨1333151, by rfl⟩ : syracuseStep 1777535 = 2666303) B2666303
theorem B1777607 : Blo 786339 1777607 := bstep (se 1 (by rfl) ⟨1333205, by rfl⟩ : syracuseStep 1777607 = 2666411) B2666411
theorem B2662523 : Blo 786339 2662523 := bstep (se 1 (by rfl) ⟨1996892, by rfl⟩ : syracuseStep 2662523 = 3993785) B3993785
theorem B2990267 : Blo 786339 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B7872815 : Blo 786339 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B1777967 : Blo 786339 1777967 := bstep (se 1 (by rfl) ⟨1333475, by rfl⟩ : syracuseStep 1777967 = 2666951) B2666951
theorem B22717259 : Blo 786339 22717259 := bstep (se 1 (by rfl) ⟨17037944, by rfl⟩ : syracuseStep 22717259 = 34075889) B34075889
theorem B77899573 : Blo 786339 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B3843931 : Blo 786339 3843931 := bstep (se 1 (by rfl) ⟨2882948, by rfl⟩ : syracuseStep 3843931 = 5765897) B5765897
theorem B5056481 : Blo 786339 5056481 := bstep (se 2 (by rfl) ⟨1896180, by rfl⟩ : syracuseStep 5056481 = 3792361) B3792361
theorem B2992211 : Blo 786339 2992211 := bstep (se 1 (by rfl) ⟨2244158, by rfl⟩ : syracuseStep 2992211 = 4488317) B4488317
theorem B3780715 : Blo 786339 3780715 := bstep (se 1 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 3780715 = 5671073) B5671073
theorem B19181699 : Blo 786339 19181699 := bstep (se 1 (by rfl) ⟨14386274, by rfl⟩ : syracuseStep 19181699 = 28772549) B28772549
theorem B5058713 : Blo 786339 5058713 := bstep (se 2 (by rfl) ⟨1897017, by rfl⟩ : syracuseStep 5058713 = 3794035) B3794035
theorem B19215377 : Blo 786339 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B8107391 : Blo 786339 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B18494999 : Blo 786339 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B3192539 : Blo 786339 3192539 := bstep (se 1 (by rfl) ⟨2394404, by rfl⟩ : syracuseStep 3192539 = 4788809) B4788809
theorem B15152993 : Blo 786339 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B11352581 : Blo 786339 11352581 := bstep (se 4 (by rfl) ⟨1064304, by rfl⟩ : syracuseStep 11352581 = 2128609) B2128609
theorem B11352635 : Blo 786339 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B221264783 : Blo 786339 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B998335 : Blo 786339 998335 := bstep (se 1 (by rfl) ⟨748751, by rfl⟩ : syracuseStep 998335 = 1497503) B1497503
theorem B1686511 : Blo 786339 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B1195739 : Blo 786339 1195739 := bstep (se 1 (by rfl) ⟨896804, by rfl⟩ : syracuseStep 1195739 = 1793609) B1793609
theorem B20528909 : Blo 786339 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B8536103 : Blo 786339 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B2244797 : Blo 786339 2244797 := bstep (se 3 (by rfl) ⟨420899, by rfl⟩ : syracuseStep 2244797 = 841799) B841799
theorem B999631 : Blo 786339 999631 := bstep (se 1 (by rfl) ⟨749723, by rfl⟩ : syracuseStep 999631 = 1499447) B1499447
theorem B12140887 : Blo 786339 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B1327583 : Blo 786339 1327583 := bstep (se 1 (by rfl) ⟨995687, by rfl⟩ : syracuseStep 1327583 = 1991375) B1991375
theorem B13485041 : Blo 786339 13485041 := bstep (se 2 (by rfl) ⟨5056890, by rfl⟩ : syracuseStep 13485041 = 10113781) B10113781
theorem B3982445 : Blo 786339 3982445 := bstep (se 3 (by rfl) ⟨746708, by rfl⟩ : syracuseStep 3982445 = 1493417) B1493417
theorem B2245799 : Blo 786339 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B2245913 : Blo 786339 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B3982931 : Blo 786339 3982931 := bstep (se 1 (by rfl) ⟨2987198, by rfl⟩ : syracuseStep 3982931 = 5974397) B5974397
theorem B1263737 : Blo 786339 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B3000503 : Blo 786339 3000503 := bstep (se 1 (by rfl) ⟨2250377, by rfl⟩ : syracuseStep 3000503 = 4500755) B4500755
theorem B28723511 : Blo 786339 28723511 := bstep (se 1 (by rfl) ⟨21542633, by rfl⟩ : syracuseStep 28723511 = 43085267) B43085267
theorem B6737053 : Blo 786339 6737053 := bstep (se 3 (by rfl) ⟨1263197, by rfl⟩ : syracuseStep 6737053 = 2526395) B2526395
theorem B3362087 : Blo 786339 3362087 := bstep (se 1 (by rfl) ⟨2521565, by rfl⟩ : syracuseStep 3362087 = 5043131) B5043131
theorem B1494443 : Blo 786339 1494443 := bstep (se 1 (by rfl) ⟨1120832, by rfl⟩ : syracuseStep 1494443 = 2241665) B2241665
theorem B6836729 : Blo 786339 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B10080773 : Blo 786339 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B1332031 : Blo 786339 1332031 := bstep (se 1 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 1332031 = 1998047) B1998047
theorem B1889531 : Blo 786339 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B1332767 : Blo 786339 1332767 := bstep (se 1 (by rfl) ⟨999575, by rfl⟩ : syracuseStep 1332767 = 1999151) B1999151
theorem B8968157 : Blo 786339 8968157 := bstep (se 3 (by rfl) ⟨1681529, by rfl⟩ : syracuseStep 8968157 = 3363059) B3363059
theorem B1333435 : Blo 786339 1333435 := bstep (se 1 (by rfl) ⟨1000076, by rfl⟩ : syracuseStep 1333435 = 2000153) B2000153
theorem B16144829 : Blo 786339 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B3365383 : Blo 786339 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B1497791 : Blo 786339 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B141712757 : Blo 786339 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B6380927 : Blo 786339 6380927 := bstep (se 1 (by rfl) ⟨4785695, by rfl⟩ : syracuseStep 6380927 = 9571391) B9571391
theorem B38002391 : Blo 786339 38002391 := bstep (se 1 (by rfl) ⟨28501793, by rfl⟩ : syracuseStep 38002391 = 57003587) B57003587
theorem B1990727 : Blo 786339 1990727 := bstep (se 1 (by rfl) ⟨1493045, by rfl⟩ : syracuseStep 1990727 = 2986091) B2986091
theorem B1892587 : Blo 786339 1892587 := bstep (se 1 (by rfl) ⟨1419440, by rfl⟩ : syracuseStep 1892587 = 2838881) B2838881
theorem B3989897 : Blo 786339 3989897 := bstep (se 2 (by rfl) ⟨1496211, by rfl⟩ : syracuseStep 3989897 = 2992423) B2992423
theorem B1991051 : Blo 786339 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B4481801 : Blo 786339 4481801 := bstep (se 2 (by rfl) ⟨1680675, by rfl⟩ : syracuseStep 4481801 = 3361351) B3361351
theorem B4252439 : Blo 786339 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B1893145 : Blo 786339 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B1893203 : Blo 786339 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B10085897 : Blo 786339 10085897 := bstep (se 2 (by rfl) ⟨3782211, by rfl⟩ : syracuseStep 10085897 = 7564423) B7564423
theorem B55404091 : Blo 786339 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B3991193 : Blo 786339 3991193 := bstep (se 2 (by rfl) ⟨1496697, by rfl⟩ : syracuseStep 3991193 = 2993395) B2993395
theorem B10119113 : Blo 786339 10119113 := bstep (se 2 (by rfl) ⟨3794667, by rfl⟩ : syracuseStep 10119113 = 7589335) B7589335
theorem B1992671 : Blo 786339 1992671 := bstep (se 1 (by rfl) ⟨1494503, by rfl⟩ : syracuseStep 1992671 = 2989007) B2989007
theorem B8972531 : Blo 786339 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B4090861 : Blo 786339 4090861 := bstep (se 3 (by rfl) ⟨767036, by rfl⟩ : syracuseStep 4090861 = 1534073) B1534073
theorem B4484261 : Blo 786339 4484261 := bstep (se 4 (by rfl) ⟨420399, by rfl⟩ : syracuseStep 4484261 = 840799) B840799
theorem B1994159 : Blo 786339 1994159 := bstep (se 1 (by rfl) ⟨1495619, by rfl⟩ : syracuseStep 1994159 = 2991239) B2991239
theorem B6745801 : Blo 786339 6745801 := bstep (se 2 (by rfl) ⟨2529675, by rfl⟩ : syracuseStep 6745801 = 5059351) B5059351
theorem B1995131 : Blo 786339 1995131 := bstep (se 1 (by rfl) ⟨1496348, by rfl⟩ : syracuseStep 1995131 = 2992697) B2992697
theorem B10088873 : Blo 786339 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B6746759 : Blo 786339 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B1995617 : Blo 786339 1995617 := bstep (se 2 (by rfl) ⟨748356, by rfl⟩ : syracuseStep 1995617 = 1496713) B1496713
theorem B9696449 : Blo 786339 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B5993837 : Blo 786339 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B5043667 : Blo 786339 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B17069777 : Blo 786339 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B1997095 : Blo 786339 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B2521577 : Blo 786339 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B8976905 : Blo 786339 8976905 := bstep (se 2 (by rfl) ⟨3366339, by rfl⟩ : syracuseStep 8976905 = 6732679) B6732679
theorem B8092943 : Blo 786339 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B11238875 : Blo 786339 11238875 := bstep (se 1 (by rfl) ⟨8429156, by rfl⟩ : syracuseStep 11238875 = 16858313) B16858313
theorem B2522603 : Blo 786339 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B2129399 : Blo 786339 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B1769327 : Blo 786339 1769327 := bstep (se 1 (by rfl) ⟨1326995, by rfl⟩ : syracuseStep 1769327 = 2653991) B2653991
theorem B2523001 : Blo 786339 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B2523449 : Blo 786339 2523449 := bstep (se 2 (by rfl) ⟨946293, by rfl⟩ : syracuseStep 2523449 = 1892587) B1892587
theorem B885055 : Blo 786339 885055 := bstep (se 1 (by rfl) ⟨663791, by rfl⟩ : syracuseStep 885055 = 1327583) B1327583
theorem B1769831 : Blo 786339 1769831 := bstep (se 1 (by rfl) ⟨1327373, by rfl⟩ : syracuseStep 1769831 = 2654747) B2654747
theorem B786791 : Blo 786339 786791 := bstep (se 1 (by rfl) ⟨590093, by rfl⟩ : syracuseStep 786791 = 1180187) B1180187
theorem B16187849 : Blo 786339 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B786911 : Blo 786339 786911 := bstep (se 1 (by rfl) ⟨590183, by rfl⟩ : syracuseStep 786911 = 1180367) B1180367
theorem B786991 : Blo 786339 786991 := bstep (se 1 (by rfl) ⟨590243, by rfl⟩ : syracuseStep 786991 = 1180487) B1180487
theorem B787035 : Blo 786339 787035 := bstep (se 1 (by rfl) ⟨590276, by rfl⟩ : syracuseStep 787035 = 1180553) B1180553
theorem B2654963 : Blo 786339 2654963 := bstep (se 1 (by rfl) ⟨1991222, by rfl⟩ : syracuseStep 2654963 = 3982445) B3982445
theorem B1180415 : Blo 786339 1180415 := bstep (se 1 (by rfl) ⟨885311, by rfl⟩ : syracuseStep 1180415 = 1770623) B1770623
theorem B787199 : Blo 786339 787199 := bstep (se 1 (by rfl) ⟨590399, by rfl⟩ : syracuseStep 787199 = 1180799) B1180799
theorem B3998483 : Blo 786339 3998483 := bstep (se 1 (by rfl) ⟨2998862, by rfl⟩ : syracuseStep 3998483 = 5997725) B5997725
theorem B787291 : Blo 786339 787291 := bstep (se 1 (by rfl) ⟨590468, by rfl⟩ : syracuseStep 787291 = 1180937) B1180937
theorem B2524193 : Blo 786339 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B2655287 : Blo 786339 2655287 := bstep (se 1 (by rfl) ⟨1991465, by rfl⟩ : syracuseStep 2655287 = 3982931) B3982931
theorem B787611 : Blo 786339 787611 := bstep (se 1 (by rfl) ⟨590708, by rfl⟩ : syracuseStep 787611 = 1181417) B1181417
theorem B787615 : Blo 786339 787615 := bstep (se 1 (by rfl) ⟨590711, by rfl⟩ : syracuseStep 787615 = 1181423) B1181423
theorem B787783 : Blo 786339 787783 := bstep (se 1 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 787783 = 1181675) B1181675
theorem B2000335 : Blo 786339 2000335 := bstep (se 1 (by rfl) ⟨1500251, by rfl⟩ : syracuseStep 2000335 = 3000503) B3000503
theorem B787951 : Blo 786339 787951 := bstep (se 1 (by rfl) ⟨590963, by rfl⟩ : syracuseStep 787951 = 1181927) B1181927
theorem B1181183 : Blo 786339 1181183 := bstep (se 1 (by rfl) ⟨885887, by rfl⟩ : syracuseStep 1181183 = 1771775) B1771775
theorem B787967 : Blo 786339 787967 := bstep (se 1 (by rfl) ⟨590975, by rfl⟩ : syracuseStep 787967 = 1181951) B1181951
theorem B788059 : Blo 786339 788059 := bstep (se 1 (by rfl) ⟨591044, by rfl⟩ : syracuseStep 788059 = 1182089) B1182089
theorem B16844507 : Blo 786339 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B11339837 : Blo 786339 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B4327519 : Blo 786339 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B1771739 : Blo 786339 1771739 := bstep (se 1 (by rfl) ⟨1328804, by rfl⟩ : syracuseStep 1771739 = 2657609) B2657609
theorem B788799 : Blo 786339 788799 := bstep (se 1 (by rfl) ⟨591599, by rfl⟩ : syracuseStep 788799 = 1183199) B1183199
theorem B788839 : Blo 786339 788839 := bstep (se 1 (by rfl) ⟨591629, by rfl⟩ : syracuseStep 788839 = 1183259) B1183259
theorem B788927 : Blo 786339 788927 := bstep (se 1 (by rfl) ⟨591695, by rfl⟩ : syracuseStep 788927 = 1183391) B1183391
theorem B1182185 : Blo 786339 1182185 := bstep (se 2 (by rfl) ⟨443319, by rfl⟩ : syracuseStep 1182185 = 886639) B886639
theorem B789103 : Blo 786339 789103 := bstep (se 1 (by rfl) ⟨591827, by rfl⟩ : syracuseStep 789103 = 1183655) B1183655
theorem B1182335 : Blo 786339 1182335 := bstep (se 1 (by rfl) ⟨886751, by rfl⟩ : syracuseStep 1182335 = 1773503) B1773503
theorem B789119 : Blo 786339 789119 := bstep (se 1 (by rfl) ⟨591839, by rfl⟩ : syracuseStep 789119 = 1183679) B1183679
theorem B5048999 : Blo 786339 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B789223 : Blo 786339 789223 := bstep (se 1 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 789223 = 1183835) B1183835
theorem B1182473 : Blo 786339 1182473 := bstep (se 2 (by rfl) ⟨443427, by rfl⟩ : syracuseStep 1182473 = 886855) B886855
theorem B789319 : Blo 786339 789319 := bstep (se 1 (by rfl) ⟨591989, by rfl⟩ : syracuseStep 789319 = 1183979) B1183979
theorem B789359 : Blo 786339 789359 := bstep (se 1 (by rfl) ⟨592019, by rfl⟩ : syracuseStep 789359 = 1184039) B1184039
theorem B1182713 : Blo 786339 1182713 := bstep (se 2 (by rfl) ⟨443517, by rfl⟩ : syracuseStep 1182713 = 887035) B887035
theorem B6720515 : Blo 786339 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B789535 : Blo 786339 789535 := bstep (se 1 (by rfl) ⟨592151, by rfl⟩ : syracuseStep 789535 = 1184303) B1184303
theorem B1182887 : Blo 786339 1182887 := bstep (se 1 (by rfl) ⟨887165, by rfl⟩ : syracuseStep 1182887 = 1774331) B1774331
theorem B789671 : Blo 786339 789671 := bstep (se 1 (by rfl) ⟨592253, by rfl⟩ : syracuseStep 789671 = 1184507) B1184507
theorem B25857197 : Blo 786339 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B789919 : Blo 786339 789919 := bstep (se 1 (by rfl) ⟨592439, by rfl⟩ : syracuseStep 789919 = 1184879) B1184879
theorem B789967 : Blo 786339 789967 := bstep (se 1 (by rfl) ⟨592475, by rfl⟩ : syracuseStep 789967 = 1184951) B1184951
theorem B1183337 : Blo 786339 1183337 := bstep (se 2 (by rfl) ⟨443751, by rfl⟩ : syracuseStep 1183337 = 887503) B887503
theorem B2690671 : Blo 786339 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B790127 : Blo 786339 790127 := bstep (se 1 (by rfl) ⟨592595, by rfl⟩ : syracuseStep 790127 = 1185191) B1185191
theorem B888511 : Blo 786339 888511 := bstep (se 1 (by rfl) ⟨666383, by rfl⟩ : syracuseStep 888511 = 1332767) B1332767
theorem B790247 : Blo 786339 790247 := bstep (se 1 (by rfl) ⟨592685, by rfl⟩ : syracuseStep 790247 = 1185371) B1185371
theorem B1183625 : Blo 786339 1183625 := bstep (se 2 (by rfl) ⟨443859, by rfl⟩ : syracuseStep 1183625 = 887719) B887719
theorem B1183865 : Blo 786339 1183865 := bstep (se 2 (by rfl) ⟨443949, by rfl⟩ : syracuseStep 1183865 = 887899) B887899
theorem B8982737 : Blo 786339 8982737 := bstep (se 2 (by rfl) ⟨3368526, by rfl⟩ : syracuseStep 8982737 = 6737053) B6737053
theorem B1773791 : Blo 786339 1773791 := bstep (se 1 (by rfl) ⟨1330343, by rfl⟩ : syracuseStep 1773791 = 2660687) B2660687
theorem B1184423 : Blo 786339 1184423 := bstep (se 1 (by rfl) ⟨888317, by rfl⟩ : syracuseStep 1184423 = 1776635) B1776635
theorem B1184543 : Blo 786339 1184543 := bstep (se 1 (by rfl) ⟨888407, by rfl⟩ : syracuseStep 1184543 = 1776815) B1776815
theorem B1184639 : Blo 786339 1184639 := bstep (se 1 (by rfl) ⟨888479, by rfl⟩ : syracuseStep 1184639 = 1776959) B1776959
theorem B94475171 : Blo 786339 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B1184711 : Blo 786339 1184711 := bstep (se 1 (by rfl) ⟨888533, by rfl⟩ : syracuseStep 1184711 = 1777067) B1777067
theorem B25334927 : Blo 786339 25334927 := bstep (se 1 (by rfl) ⟨19001195, by rfl⟩ : syracuseStep 25334927 = 38002391) B38002391
theorem B1185023 : Blo 786339 1185023 := bstep (se 1 (by rfl) ⟨888767, by rfl⟩ : syracuseStep 1185023 = 1777535) B1777535
theorem B1185071 : Blo 786339 1185071 := bstep (se 1 (by rfl) ⟨888803, by rfl⟩ : syracuseStep 1185071 = 1777607) B1777607
theorem B1775015 : Blo 786339 1775015 := bstep (se 1 (by rfl) ⟨1331261, by rfl⟩ : syracuseStep 1775015 = 2662523) B2662523
theorem B5248543 : Blo 786339 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B1185311 : Blo 786339 1185311 := bstep (se 1 (by rfl) ⟨888983, by rfl⟩ : syracuseStep 1185311 = 1777967) B1777967
theorem B2659931 : Blo 786339 2659931 := bstep (se 1 (by rfl) ⟨1994948, by rfl⟩ : syracuseStep 2659931 = 3989897) B3989897
theorem B2987837 : Blo 786339 2987837 := bstep (se 3 (by rfl) ⟨560219, by rfl⟩ : syracuseStep 2987837 = 1120439) B1120439
theorem B2987867 : Blo 786339 2987867 := bstep (se 1 (by rfl) ⟨2240900, by rfl⟩ : syracuseStep 2987867 = 4481801) B4481801
theorem B15144839 : Blo 786339 15144839 := bstep (se 1 (by rfl) ⟨11358629, by rfl⟩ : syracuseStep 15144839 = 22717259) B22717259
theorem B6723931 : Blo 786339 6723931 := bstep (se 1 (by rfl) ⟨5042948, by rfl⟩ : syracuseStep 6723931 = 10085897) B10085897
theorem B1776041 : Blo 786339 1776041 := bstep (se 2 (by rfl) ⟨666015, by rfl⟩ : syracuseStep 1776041 = 1332031) B1332031
theorem B2660795 : Blo 786339 2660795 := bstep (se 1 (by rfl) ⟨1995596, by rfl⟩ : syracuseStep 2660795 = 3991193) B3991193
theorem B6724205 : Blo 786339 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B6724889 : Blo 786339 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B2989507 : Blo 786339 2989507 := bstep (se 1 (by rfl) ⟨2242130, by rfl⟩ : syracuseStep 2989507 = 4484261) B4484261
theorem B12787799 : Blo 786339 12787799 := bstep (se 1 (by rfl) ⟨9590849, by rfl⟩ : syracuseStep 12787799 = 19181699) B19181699
theorem B23077009 : Blo 786339 23077009 := bstep (se 2 (by rfl) ⟨8653878, by rfl⟩ : syracuseStep 23077009 = 17307757) B17307757
theorem B1777913 : Blo 786339 1777913 := bstep (se 2 (by rfl) ⟨666717, by rfl⟩ : syracuseStep 1777913 = 1333435) B1333435
theorem B6725915 : Blo 786339 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B2662793 : Blo 786339 2662793 := bstep (se 2 (by rfl) ⟨998547, by rfl⟩ : syracuseStep 2662793 = 1997095) B1997095
theorem B4497839 : Blo 786339 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B5972453 : Blo 786339 5972453 := bstep (se 4 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 5972453 = 1119835) B1119835
theorem B12329999 : Blo 786339 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B11379851 : Blo 786339 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B10101995 : Blo 786339 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B1681735 : Blo 786339 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B1419599 : Blo 786339 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B797159 : Blo 786339 797159 := bstep (se 1 (by rfl) ⟨597869, by rfl⟩ : syracuseStep 797159 = 1195739) B1195739
theorem B2992895 : Blo 786339 2992895 := bstep (se 1 (by rfl) ⟨2244671, by rfl⟩ : syracuseStep 2992895 = 4489343) B4489343
theorem B2403263 : Blo 786339 2403263 := bstep (se 1 (by rfl) ⟨1802447, by rfl⟩ : syracuseStep 2403263 = 3604895) B3604895
theorem B1682623 : Blo 786339 1682623 := bstep (se 1 (by rfl) ⟨1261967, by rfl⟩ : syracuseStep 1682623 = 2523935) B2523935
theorem B8990027 : Blo 786339 8990027 := bstep (se 1 (by rfl) ⟨6742520, by rfl⟩ : syracuseStep 8990027 = 13485041) B13485041
theorem B4501007 : Blo 786339 4501007 := bstep (se 1 (by rfl) ⟨3375755, by rfl⟩ : syracuseStep 4501007 = 6751511) B6751511
theorem B2666249 : Blo 786339 2666249 := bstep (se 2 (by rfl) ⟨999843, by rfl⟩ : syracuseStep 2666249 = 1999687) B1999687
theorem B18231277 : Blo 786339 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B5681279 : Blo 786339 5681279 := bstep (se 1 (by rfl) ⟨4260959, by rfl⟩ : syracuseStep 5681279 = 8521919) B8521919
theorem B19149007 : Blo 786339 19149007 := bstep (se 1 (by rfl) ⟨14361755, by rfl⟩ : syracuseStep 19149007 = 28723511) B28723511
theorem B92385623 : Blo 786339 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B73872121 : Blo 786339 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B2241391 : Blo 786339 2241391 := bstep (se 1 (by rfl) ⟨1681043, by rfl⟩ : syracuseStep 2241391 = 3362087) B3362087
theorem B996295 : Blo 786339 996295 := bstep (se 1 (by rfl) ⟨747221, by rfl⟩ : syracuseStep 996295 = 1494443) B1494443
theorem B5125241 : Blo 786339 5125241 := bstep (se 2 (by rfl) ⟨1921965, by rfl⟩ : syracuseStep 5125241 = 3843931) B3843931
theorem B1259687 : Blo 786339 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B2996783 : Blo 786339 2996783 := bstep (se 1 (by rfl) ⟨2247587, by rfl⟩ : syracuseStep 2996783 = 4495175) B4495175
theorem B5454481 : Blo 786339 5454481 := bstep (se 2 (by rfl) ⟨2045430, by rfl⟩ : syracuseStep 5454481 = 4090861) B4090861
theorem B5978771 : Blo 786339 5978771 := bstep (se 1 (by rfl) ⟨4484078, by rfl⟩ : syracuseStep 5978771 = 8968157) B8968157
theorem B10763219 : Blo 786339 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B1621289 : Blo 786339 1621289 := bstep (se 2 (by rfl) ⟨607983, by rfl⟩ : syracuseStep 1621289 = 1215967) B1215967
theorem B8994401 : Blo 786339 8994401 := bstep (se 2 (by rfl) ⟨3372900, by rfl⟩ : syracuseStep 8994401 = 6745801) B6745801
theorem B1327151 : Blo 786339 1327151 := bstep (se 1 (by rfl) ⟨995363, by rfl⟩ : syracuseStep 1327151 = 1990727) B1990727
theorem B43171973 : Blo 786339 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B1327367 : Blo 786339 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B1262135 : Blo 786339 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B1328447 : Blo 786339 1328447 := bstep (se 1 (by rfl) ⟨996335, by rfl⟩ : syracuseStep 1328447 = 1992671) B1992671
theorem B5981687 : Blo 786339 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B1329439 : Blo 786339 1329439 := bstep (se 1 (by rfl) ⟨997079, by rfl⟩ : syracuseStep 1329439 = 1994159) B1994159
theorem B1330087 : Blo 786339 1330087 := bstep (se 1 (by rfl) ⟨997565, by rfl⟩ : syracuseStep 1330087 = 1995131) B1995131
theorem B1330411 : Blo 786339 1330411 := bstep (se 1 (by rfl) ⟨997808, by rfl⟩ : syracuseStep 1330411 = 1995617) B1995617
theorem B1331113 : Blo 786339 1331113 := bstep (se 2 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 1331113 = 998335) B998335
theorem B2248681 : Blo 786339 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B5984603 : Blo 786339 5984603 := bstep (se 1 (by rfl) ⟨4488452, by rfl⟩ : syracuseStep 5984603 = 8976905) B8976905
theorem B147509855 : Blo 786339 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B5395295 : Blo 786339 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B7492583 : Blo 786339 7492583 := bstep (se 1 (by rfl) ⟨5619437, by rfl⟩ : syracuseStep 7492583 = 11238875) B11238875
theorem B3364001 : Blo 786339 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B13685939 : Blo 786339 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B5690735 : Blo 786339 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B3233191 : Blo 786339 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B1496531 : Blo 786339 1496531 := bstep (se 1 (by rfl) ⟨1122398, by rfl⟩ : syracuseStep 1496531 = 2244797) B2244797
theorem B1332841 : Blo 786339 1332841 := bstep (se 2 (by rfl) ⟨499815, by rfl⟩ : syracuseStep 1332841 = 999631) B999631
theorem B1497199 : Blo 786339 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B1333415 : Blo 786339 1333415 := bstep (se 1 (by rfl) ⟨1000061, by rfl⟩ : syracuseStep 1333415 = 2000123) B2000123
theorem B1497275 : Blo 786339 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B842491 : Blo 786339 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B3368375 : Blo 786339 3368375 := bstep (se 1 (by rfl) ⟨2526281, by rfl⟩ : syracuseStep 3368375 = 5052563) B5052563
theorem B1992539 : Blo 786339 1992539 := bstep (se 1 (by rfl) ⟨1494404, by rfl⟩ : syracuseStep 1992539 = 2988809) B2988809
theorem B8513437 : Blo 786339 8513437 := bstep (se 3 (by rfl) ⟨1596269, by rfl⟩ : syracuseStep 8513437 = 3192539) B3192539
theorem B4253951 : Blo 786339 4253951 := bstep (se 1 (by rfl) ⟨3190463, by rfl⟩ : syracuseStep 4253951 = 6380927) B6380927
theorem B1993511 : Blo 786339 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B5040953 : Blo 786339 5040953 := bstep (se 2 (by rfl) ⟨1890357, by rfl⟩ : syracuseStep 5040953 = 3780715) B3780715
theorem B32336941 : Blo 786339 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B6746075 : Blo 786339 6746075 := bstep (se 1 (by rfl) ⟨5059556, by rfl⟩ : syracuseStep 6746075 = 10119113) B10119113
theorem B3370987 : Blo 786339 3370987 := bstep (se 1 (by rfl) ⟨2528240, by rfl⟩ : syracuseStep 3370987 = 5056481) B5056481
theorem B1994807 : Blo 786339 1994807 := bstep (se 1 (by rfl) ⟨1496105, by rfl⟩ : syracuseStep 1994807 = 2992211) B2992211
theorem B3994109 : Blo 786339 3994109 := bstep (se 3 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 3994109 = 1497791) B1497791
theorem B3372475 : Blo 786339 3372475 := bstep (se 1 (by rfl) ⟨2529356, by rfl⟩ : syracuseStep 3372475 = 5058713) B5058713
theorem B14349797 : Blo 786339 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B4487177 : Blo 786339 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B12810251 : Blo 786339 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B3995891 : Blo 786339 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B5404927 : Blo 786339 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B5994809 : Blo 786339 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B415464389 : Blo 786339 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B7568387 : Blo 786339 7568387 := bstep (se 1 (by rfl) ⟨5676290, by rfl⟩ : syracuseStep 7568387 = 11352581) B11352581
theorem B7568423 : Blo 786339 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B1179551 : Blo 786339 1179551 := bstep (se 1 (by rfl) ⟨884663, by rfl⟩ : syracuseStep 1179551 = 1769327) B1769327
theorem B884767 : Blo 786339 884767 := bstep (se 1 (by rfl) ⟨663575, by rfl⟩ : syracuseStep 884767 = 1327151) B1327151
theorem B884911 : Blo 786339 884911 := bstep (se 1 (by rfl) ⟨663683, by rfl⟩ : syracuseStep 884911 = 1327367) B1327367
theorem B30769345 : Blo 786339 30769345 := bstep (se 2 (by rfl) ⟨11538504, by rfl⟩ : syracuseStep 30769345 = 23077009) B23077009
theorem B1179887 : Blo 786339 1179887 := bstep (se 1 (by rfl) ⟨884915, by rfl⟩ : syracuseStep 1179887 = 1769831) B1769831
theorem B1180073 : Blo 786339 1180073 := bstep (se 2 (by rfl) ⟨442527, by rfl⟩ : syracuseStep 1180073 = 885055) B885055
theorem B1769975 : Blo 786339 1769975 := bstep (se 1 (by rfl) ⟨1327481, by rfl⟩ : syracuseStep 1769975 = 2654963) B2654963
theorem B786943 : Blo 786339 786943 := bstep (se 1 (by rfl) ⟨590207, by rfl⟩ : syracuseStep 786943 = 1180415) B1180415
theorem B1770191 : Blo 786339 1770191 := bstep (se 1 (by rfl) ⟨1327643, by rfl⟩ : syracuseStep 1770191 = 2655287) B2655287
theorem B885631 : Blo 786339 885631 := bstep (se 1 (by rfl) ⟨664223, by rfl⟩ : syracuseStep 885631 = 1328447) B1328447
theorem B787455 : Blo 786339 787455 := bstep (se 1 (by rfl) ⟨590591, by rfl⟩ : syracuseStep 787455 = 1181183) B1181183
theorem B1181159 : Blo 786339 1181159 := bstep (se 1 (by rfl) ⟨885869, by rfl⟩ : syracuseStep 1181159 = 1771739) B1771739
theorem B788123 : Blo 786339 788123 := bstep (se 1 (by rfl) ⟨591092, by rfl⟩ : syracuseStep 788123 = 1182185) B1182185
theorem B788223 : Blo 786339 788223 := bstep (se 1 (by rfl) ⟨591167, by rfl⟩ : syracuseStep 788223 = 1182335) B1182335
theorem B788315 : Blo 786339 788315 := bstep (se 1 (by rfl) ⟨591236, by rfl⟩ : syracuseStep 788315 = 1182473) B1182473
theorem B788475 : Blo 786339 788475 := bstep (se 1 (by rfl) ⟨591356, by rfl⟩ : syracuseStep 788475 = 1182713) B1182713
theorem B17238131 : Blo 786339 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B788591 : Blo 786339 788591 := bstep (se 1 (by rfl) ⟨591443, by rfl⟩ : syracuseStep 788591 = 1182887) B1182887
theorem B14387453 : Blo 786339 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B788891 : Blo 786339 788891 := bstep (se 1 (by rfl) ⟨591668, by rfl⟩ : syracuseStep 788891 = 1183337) B1183337
theorem B789083 : Blo 786339 789083 := bstep (se 1 (by rfl) ⟨591812, by rfl⟩ : syracuseStep 789083 = 1183625) B1183625
theorem B789243 : Blo 786339 789243 := bstep (se 1 (by rfl) ⟨591932, by rfl⟩ : syracuseStep 789243 = 1183865) B1183865
theorem B5770025 : Blo 786339 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1182527 : Blo 786339 1182527 := bstep (se 1 (by rfl) ⟨886895, by rfl⟩ : syracuseStep 1182527 = 1773791) B1773791
theorem B1772585 : Blo 786339 1772585 := bstep (se 2 (by rfl) ⟨664719, by rfl⟩ : syracuseStep 1772585 = 1329439) B1329439
theorem B98339903 : Blo 786339 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B789615 : Blo 786339 789615 := bstep (se 1 (by rfl) ⟨592211, by rfl⟩ : syracuseStep 789615 = 1184423) B1184423
theorem B789695 : Blo 786339 789695 := bstep (se 1 (by rfl) ⟨592271, by rfl⟩ : syracuseStep 789695 = 1184543) B1184543
theorem B789759 : Blo 786339 789759 := bstep (se 1 (by rfl) ⟨592319, by rfl⟩ : syracuseStep 789759 = 1184639) B1184639
theorem B789807 : Blo 786339 789807 := bstep (se 1 (by rfl) ⟨592355, by rfl⟩ : syracuseStep 789807 = 1184711) B1184711
theorem B790015 : Blo 786339 790015 := bstep (se 1 (by rfl) ⟨592511, by rfl⟩ : syracuseStep 790015 = 1185023) B1185023
theorem B790047 : Blo 786339 790047 := bstep (se 1 (by rfl) ⟨592535, by rfl⟩ : syracuseStep 790047 = 1185071) B1185071
theorem B1183343 : Blo 786339 1183343 := bstep (se 1 (by rfl) ⟨887507, by rfl⟩ : syracuseStep 1183343 = 1775015) B1775015
theorem B790207 : Blo 786339 790207 := bstep (se 1 (by rfl) ⟨592655, by rfl⟩ : syracuseStep 790207 = 1185311) B1185311
theorem B1773287 : Blo 786339 1773287 := bstep (se 1 (by rfl) ⟨1329965, by rfl⟩ : syracuseStep 1773287 = 2659931) B2659931
theorem B1773449 : Blo 786339 1773449 := bstep (se 2 (by rfl) ⟨665043, by rfl⟩ : syracuseStep 1773449 = 1330087) B1330087
theorem B10096559 : Blo 786339 10096559 := bstep (se 1 (by rfl) ⟨7572419, by rfl⟩ : syracuseStep 10096559 = 15144839) B15144839
theorem B888943 : Blo 786339 888943 := bstep (se 1 (by rfl) ⟨666707, by rfl⟩ : syracuseStep 888943 = 1333415) B1333415
theorem B1184027 : Blo 786339 1184027 := bstep (se 1 (by rfl) ⟨888020, by rfl⟩ : syracuseStep 1184027 = 1776041) B1776041
theorem B1773863 : Blo 786339 1773863 := bstep (se 1 (by rfl) ⟨1330397, by rfl⟩ : syracuseStep 1773863 = 2660795) B2660795
theorem B1773881 : Blo 786339 1773881 := bstep (se 2 (by rfl) ⟨665205, by rfl⟩ : syracuseStep 1773881 = 1330411) B1330411
theorem B1184681 : Blo 786339 1184681 := bstep (se 2 (by rfl) ⟨444255, by rfl⟩ : syracuseStep 1184681 = 888511) B888511
theorem B1774817 : Blo 786339 1774817 := bstep (se 2 (by rfl) ⟨665556, by rfl⟩ : syracuseStep 1774817 = 1331113) B1331113
theorem B4494649 : Blo 786339 4494649 := bstep (se 2 (by rfl) ⟨1685493, by rfl⟩ : syracuseStep 4494649 = 3370987) B3370987
theorem B1185275 : Blo 786339 1185275 := bstep (se 1 (by rfl) ⟨888956, by rfl⟩ : syracuseStep 1185275 = 1777913) B1777913
theorem B1775195 : Blo 786339 1775195 := bstep (se 1 (by rfl) ⟨1331396, by rfl⟩ : syracuseStep 1775195 = 2662793) B2662793
theorem B25532009 : Blo 786339 25532009 := bstep (se 2 (by rfl) ⟨9574503, by rfl⟩ : syracuseStep 25532009 = 19149007) B19149007
theorem B2988521 : Blo 786339 2988521 := bstep (se 2 (by rfl) ⟨1120695, by rfl⟩ : syracuseStep 2988521 = 2241391) B2241391
theorem B4496633 : Blo 786339 4496633 := bstep (se 2 (by rfl) ⟨1686237, by rfl⟩ : syracuseStep 4496633 = 3372475) B3372475
theorem B1777121 : Blo 786339 1777121 := bstep (se 2 (by rfl) ⟨666420, by rfl⟩ : syracuseStep 1777121 = 1332841) B1332841
theorem B1777499 : Blo 786339 1777499 := bstep (se 1 (by rfl) ⟨1333124, by rfl⟩ : syracuseStep 1777499 = 2666249) B2666249
theorem B4497383 : Blo 786339 4497383 := bstep (se 1 (by rfl) ⟨3373037, by rfl⟩ : syracuseStep 4497383 = 6746075) B6746075
theorem B2662739 : Blo 786339 2662739 := bstep (se 1 (by rfl) ⟨1997054, by rfl⟩ : syracuseStep 2662739 = 3994109) B3994109
theorem B3416827 : Blo 786339 3416827 := bstep (se 1 (by rfl) ⟨2562620, by rfl⟩ : syracuseStep 3416827 = 5125241) B5125241
theorem B1123321 : Blo 786339 1123321 := bstep (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) B842491
theorem B2991451 : Blo 786339 2991451 := bstep (se 1 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 2991451 = 4487177) B4487177
theorem B2663927 : Blo 786339 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B28781315 : Blo 786339 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B1682299 : Blo 786339 1682299 := bstep (se 1 (by rfl) ⟨1261724, by rfl⟩ : syracuseStep 1682299 = 2523449) B2523449
theorem B10791899 : Blo 786339 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B2665655 : Blo 786339 2665655 := bstep (se 1 (by rfl) ⟨1999241, by rfl⟩ : syracuseStep 2665655 = 3998483) B3998483
theorem B1682795 : Blo 786339 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B2667113 : Blo 786339 2667113 := bstep (se 2 (by rfl) ⟨1000167, by rfl⟩ : syracuseStep 2667113 = 2000335) B2000335
theorem B251933789 : Blo 786339 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B11351249 : Blo 786339 11351249 := bstep (se 2 (by rfl) ⟨4256718, by rfl⟩ : syracuseStep 11351249 = 8513437) B8513437
theorem B2242313 : Blo 786339 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B4995055 : Blo 786339 4995055 := bstep (se 1 (by rfl) ⟨3746291, by rfl⟩ : syracuseStep 4995055 = 7492583) B7492583
theorem B16889951 : Blo 786339 16889951 := bstep (se 1 (by rfl) ⟨12667463, by rfl⟩ : syracuseStep 16889951 = 25334927) B25334927
theorem B2242667 : Blo 786339 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B9123959 : Blo 786339 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B997687 : Blo 786339 997687 := bstep (se 1 (by rfl) ⟨748265, by rfl⟩ : syracuseStep 997687 = 1496531) B1496531
theorem B998183 : Blo 786339 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B3587561 : Blo 786339 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B2998241 : Blo 786339 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B2998559 : Blo 786339 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B3981635 : Blo 786339 3981635 := bstep (se 1 (by rfl) ⟨2986226, by rfl⟩ : syracuseStep 3981635 = 5972453) B5972453
theorem B7586567 : Blo 786339 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B6734663 : Blo 786339 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B2245583 : Blo 786339 2245583 := bstep (se 1 (by rfl) ⟨1684187, by rfl⟩ : syracuseStep 2245583 = 3368375) B3368375
theorem B1328359 : Blo 786339 1328359 := bstep (se 1 (by rfl) ⟨996269, by rfl⟩ : syracuseStep 1328359 = 1992539) B1992539
theorem B1328393 : Blo 786339 1328393 := bstep (se 2 (by rfl) ⟨498147, by rfl⟩ : syracuseStep 1328393 = 996295) B996295
theorem B2835967 : Blo 786339 2835967 := bstep (se 1 (by rfl) ⟨2126975, by rfl⟩ : syracuseStep 2835967 = 4253951) B4253951
theorem B1329007 : Blo 786339 1329007 := bstep (se 1 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 1329007 = 1993511) B1993511
theorem B3360635 : Blo 786339 3360635 := bstep (se 1 (by rfl) ⟨2520476, by rfl⟩ : syracuseStep 3360635 = 5040953) B5040953
theorem B4310921 : Blo 786339 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B6998057 : Blo 786339 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B3000671 : Blo 786339 3000671 := bstep (se 1 (by rfl) ⟨2250503, by rfl⟩ : syracuseStep 3000671 = 4501007) B4501007
theorem B1329871 : Blo 786339 1329871 := bstep (se 1 (by rfl) ⟨997403, by rfl⟩ : syracuseStep 1329871 = 1994807) B1994807
theorem B3787519 : Blo 786339 3787519 := bstep (se 1 (by rfl) ⟨2840639, by rfl⟩ : syracuseStep 3787519 = 5681279) B5681279
theorem B61590415 : Blo 786339 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B8965241 : Blo 786339 8965241 := bstep (se 2 (by rfl) ⟨3361965, by rfl⟩ : syracuseStep 8965241 = 6723931) B6723931
theorem B8540167 : Blo 786339 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B839791 : Blo 786339 839791 := bstep (se 1 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 839791 = 1259687) B1259687
theorem B3985847 : Blo 786339 3985847 := bstep (se 1 (by rfl) ⟨2989385, by rfl⟩ : syracuseStep 3985847 = 5978771) B5978771
theorem B3986009 : Blo 786339 3986009 := bstep (se 2 (by rfl) ⟨1494753, by rfl⟩ : syracuseStep 3986009 = 2989507) B2989507
theorem B276976259 : Blo 786339 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B34100797 : Blo 786339 34100797 := bstep (se 3 (by rfl) ⟨6393899, by rfl⟩ : syracuseStep 34100797 = 12787799) B12787799
theorem B841423 : Blo 786339 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B3987791 : Blo 786339 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B11229671 : Blo 786339 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B7559891 : Blo 786339 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B3365999 : Blo 786339 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B4480343 : Blo 786339 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B5988491 : Blo 786339 5988491 := bstep (se 1 (by rfl) ⟨4491368, by rfl⟩ : syracuseStep 5988491 = 8982737) B8982737
theorem B3989735 : Blo 786339 3989735 := bstep (se 1 (by rfl) ⟨2992301, by rfl⟩ : syracuseStep 3989735 = 5984603) B5984603
theorem B3793823 : Blo 786339 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B1991891 : Blo 786339 1991891 := bstep (se 1 (by rfl) ⟨1493918, by rfl⟩ : syracuseStep 1991891 = 2987837) B2987837
theorem B1991911 : Blo 786339 1991911 := bstep (se 1 (by rfl) ⟨1493933, by rfl⟩ : syracuseStep 1991911 = 2987867) B2987867
theorem B43115921 : Blo 786339 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B4482803 : Blo 786339 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B4483259 : Blo 786339 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B24308369 : Blo 786339 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B4483943 : Blo 786339 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B8219999 : Blo 786339 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B98496161 : Blo 786339 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B8973989 : Blo 786339 8973989 := bstep (se 4 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 8973989 = 1682623) B1682623
theorem B2125757 : Blo 786339 2125757 := bstep (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) B797159
theorem B946399 : Blo 786339 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B1995263 : Blo 786339 1995263 := bstep (se 1 (by rfl) ⟨1496447, by rfl⟩ : syracuseStep 1995263 = 2992895) B2992895
theorem B1602175 : Blo 786339 1602175 := bstep (se 1 (by rfl) ⟨1201631, by rfl⟩ : syracuseStep 1602175 = 2403263) B2403263
theorem B5993351 : Blo 786339 5993351 := bstep (se 1 (by rfl) ⟨4495013, by rfl⟩ : syracuseStep 5993351 = 8990027) B8990027
theorem B1996265 : Blo 786339 1996265 := bstep (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) B1497199
theorem B7206569 : Blo 786339 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B4323437 : Blo 786339 4323437 := bstep (se 3 (by rfl) ⟨810644, by rfl⟩ : syracuseStep 4323437 = 1621289) B1621289
theorem B7272641 : Blo 786339 7272641 := bstep (se 2 (by rfl) ⟨2727240, by rfl⟩ : syracuseStep 7272641 = 5454481) B5454481
theorem B9566531 : Blo 786339 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B3996539 : Blo 786339 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B1997855 : Blo 786339 1997855 := bstep (se 1 (by rfl) ⟨1498391, by rfl⟩ : syracuseStep 1997855 = 2996783) B2996783
theorem B7175479 : Blo 786339 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B5045591 : Blo 786339 5045591 := bstep (se 1 (by rfl) ⟨3784193, by rfl⟩ : syracuseStep 5045591 = 7568387) B7568387
theorem B5045615 : Blo 786339 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B5996267 : Blo 786339 5996267 := bstep (se 1 (by rfl) ⟨4497200, by rfl⟩ : syracuseStep 5996267 = 8994401) B8994401
theorem B786367 : Blo 786339 786367 := bstep (se 1 (by rfl) ⟨589775, by rfl⟩ : syracuseStep 786367 = 1179551) B1179551
theorem B1179689 : Blo 786339 1179689 := bstep (se 2 (by rfl) ⟨442383, by rfl⟩ : syracuseStep 1179689 = 884767) B884767
theorem B786591 : Blo 786339 786591 := bstep (se 1 (by rfl) ⟨589943, by rfl⟩ : syracuseStep 786591 = 1179887) B1179887
theorem B1999039 : Blo 786339 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B2654423 : Blo 786339 2654423 := bstep (se 1 (by rfl) ⟨1990817, by rfl⟩ : syracuseStep 2654423 = 3981635) B3981635
theorem B1179881 : Blo 786339 1179881 := bstep (se 2 (by rfl) ⟨442455, by rfl⟩ : syracuseStep 1179881 = 884911) B884911
theorem B41025793 : Blo 786339 41025793 := bstep (se 2 (by rfl) ⟨15384672, by rfl⟩ : syracuseStep 41025793 = 30769345) B30769345
theorem B786715 : Blo 786339 786715 := bstep (se 1 (by rfl) ⟨590036, by rfl⟩ : syracuseStep 786715 = 1180073) B1180073
theorem B1179983 : Blo 786339 1179983 := bstep (se 1 (by rfl) ⟨884987, by rfl⟩ : syracuseStep 1179983 = 1769975) B1769975
theorem B1180127 : Blo 786339 1180127 := bstep (se 1 (by rfl) ⟨885095, by rfl⟩ : syracuseStep 1180127 = 1770191) B1770191
theorem B4489775 : Blo 786339 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B885595 : Blo 786339 885595 := bstep (se 1 (by rfl) ⟨664196, by rfl⟩ : syracuseStep 885595 = 1328393) B1328393
theorem B787439 : Blo 786339 787439 := bstep (se 1 (by rfl) ⟨590579, by rfl⟩ : syracuseStep 787439 = 1181159) B1181159
theorem B4555769 : Blo 786339 4555769 := bstep (se 2 (by rfl) ⟨1708413, by rfl⟩ : syracuseStep 4555769 = 3416827) B3416827
theorem B1180841 : Blo 786339 1180841 := bstep (se 2 (by rfl) ⟨442815, by rfl⟩ : syracuseStep 1180841 = 885631) B885631
theorem B2000447 : Blo 786339 2000447 := bstep (se 1 (by rfl) ⟨1500335, by rfl⟩ : syracuseStep 2000447 = 3000671) B3000671
theorem B2655881 : Blo 786339 2655881 := bstep (se 2 (by rfl) ⟨995955, by rfl⟩ : syracuseStep 2655881 = 1991911) B1991911
theorem B1771145 : Blo 786339 1771145 := bstep (se 2 (by rfl) ⟨664179, by rfl⟩ : syracuseStep 1771145 = 1328359) B1328359
theorem B788351 : Blo 786339 788351 := bstep (se 1 (by rfl) ⟨591263, by rfl⟩ : syracuseStep 788351 = 1182527) B1182527
theorem B1181723 : Blo 786339 1181723 := bstep (se 1 (by rfl) ⟨886292, by rfl⟩ : syracuseStep 1181723 = 1772585) B1772585
theorem B788895 : Blo 786339 788895 := bstep (se 1 (by rfl) ⟨591671, by rfl⟩ : syracuseStep 788895 = 1183343) B1183343
theorem B1772009 : Blo 786339 1772009 := bstep (se 2 (by rfl) ⟨664503, by rfl⟩ : syracuseStep 1772009 = 1329007) B1329007
theorem B1182191 : Blo 786339 1182191 := bstep (se 1 (by rfl) ⟨886643, by rfl⟩ : syracuseStep 1182191 = 1773287) B1773287
theorem B1182299 : Blo 786339 1182299 := bstep (se 1 (by rfl) ⟨886724, by rfl⟩ : syracuseStep 1182299 = 1773449) B1773449
theorem B789351 : Blo 786339 789351 := bstep (se 1 (by rfl) ⟨592013, by rfl⟩ : syracuseStep 789351 = 1184027) B1184027
theorem B1182575 : Blo 786339 1182575 := bstep (se 1 (by rfl) ⟨886931, by rfl⟩ : syracuseStep 1182575 = 1773863) B1773863
theorem B1182587 : Blo 786339 1182587 := bstep (se 1 (by rfl) ⟨886940, by rfl⟩ : syracuseStep 1182587 = 1773881) B1773881
theorem B2657231 : Blo 786339 2657231 := bstep (se 1 (by rfl) ⟨1992923, by rfl⟩ : syracuseStep 2657231 = 3985847) B3985847
theorem B2657339 : Blo 786339 2657339 := bstep (se 1 (by rfl) ⟨1993004, by rfl⟩ : syracuseStep 2657339 = 3986009) B3986009
theorem B184650839 : Blo 786339 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B789787 : Blo 786339 789787 := bstep (se 1 (by rfl) ⟨592340, by rfl⟩ : syracuseStep 789787 = 1184681) B1184681
theorem B1183211 : Blo 786339 1183211 := bstep (se 1 (by rfl) ⟨887408, by rfl⟩ : syracuseStep 1183211 = 1774817) B1774817
theorem B1773161 : Blo 786339 1773161 := bstep (se 2 (by rfl) ⟨664935, by rfl⟩ : syracuseStep 1773161 = 1329871) B1329871
theorem B790183 : Blo 786339 790183 := bstep (se 1 (by rfl) ⟨592637, by rfl⟩ : syracuseStep 790183 = 1185275) B1185275
theorem B5050025 : Blo 786339 5050025 := bstep (se 2 (by rfl) ⟨1893759, by rfl⟩ : syracuseStep 5050025 = 3787519) B3787519
theorem B1183463 : Blo 786339 1183463 := bstep (se 1 (by rfl) ⟨887597, by rfl⟩ : syracuseStep 1183463 = 1775195) B1775195
theorem B82120553 : Blo 786339 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B2658527 : Blo 786339 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B2986895 : Blo 786339 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B1184747 : Blo 786339 1184747 := bstep (se 1 (by rfl) ⟨888560, by rfl⟩ : syracuseStep 1184747 = 1777121) B1777121
theorem B1184999 : Blo 786339 1184999 := bstep (se 1 (by rfl) ⟨888749, by rfl⟩ : syracuseStep 1184999 = 1777499) B1777499
theorem B1185257 : Blo 786339 1185257 := bstep (se 2 (by rfl) ⟨444471, by rfl⟩ : syracuseStep 1185257 = 888943) B888943
theorem B2659823 : Blo 786339 2659823 := bstep (se 1 (by rfl) ⟨1994867, by rfl⟩ : syracuseStep 2659823 = 3989735) B3989735
theorem B1775159 : Blo 786339 1775159 := bstep (se 1 (by rfl) ⟨1331369, by rfl⟩ : syracuseStep 1775159 = 2662739) B2662739
theorem B2529215 : Blo 786339 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B2136233 : Blo 786339 2136233 := bstep (se 2 (by rfl) ⟨801087, by rfl⟩ : syracuseStep 2136233 = 1602175) B1602175
theorem B28743947 : Blo 786339 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B1775951 : Blo 786339 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B2988535 : Blo 786339 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B2988839 : Blo 786339 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B2989295 : Blo 786339 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B2661821 : Blo 786339 2661821 := bstep (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) B998183
theorem B1777103 : Blo 786339 1777103 := bstep (se 1 (by rfl) ⟨1332827, by rfl⟩ : syracuseStep 1777103 = 2665655) B2665655
theorem B1121863 : Blo 786339 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B1121897 : Blo 786339 1121897 := bstep (se 2 (by rfl) ⟨420711, by rfl⟩ : syracuseStep 1121897 = 841423) B841423
theorem B1417171 : Blo 786339 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B6660073 : Blo 786339 6660073 := bstep (se 2 (by rfl) ⟨2497527, by rfl⟩ : syracuseStep 6660073 = 4995055) B4995055
theorem B1778075 : Blo 786339 1778075 := bstep (se 1 (by rfl) ⟨1333556, by rfl⟩ : syracuseStep 1778075 = 2667113) B2667113
theorem B2664359 : Blo 786339 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B5057711 : Blo 786339 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B183873397 : Blo 786339 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B2240423 : Blo 786339 2240423 := bstep (se 1 (by rfl) ⟨1680317, by rfl⟩ : syracuseStep 2240423 = 3360635) B3360635
theorem B4665371 : Blo 786339 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B3846683 : Blo 786339 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B3781289 : Blo 786339 3781289 := bstep (se 2 (by rfl) ⟨1417983, by rfl⟩ : syracuseStep 3781289 = 2835967) B2835967
theorem B5976827 : Blo 786339 5976827 := bstep (se 1 (by rfl) ⟨4482620, by rfl⟩ : syracuseStep 5976827 = 8965241) B8965241
theorem B6731039 : Blo 786339 6731039 := bstep (se 1 (by rfl) ⟨5048279, by rfl⟩ : syracuseStep 6731039 = 10096559) B10096559
theorem B17021339 : Blo 786339 17021339 := bstep (se 1 (by rfl) ⟨12766004, by rfl⟩ : syracuseStep 17021339 = 25532009) B25532009
theorem B2243065 : Blo 786339 2243065 := bstep (se 2 (by rfl) ⟨841149, by rfl⟩ : syracuseStep 2243065 = 1682299) B1682299
theorem B7486447 : Blo 786339 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B2243999 : Blo 786339 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B2997755 : Blo 786339 2997755 := bstep (se 1 (by rfl) ⟨2248316, by rfl⟩ : syracuseStep 2997755 = 4496633) B4496633
theorem B2998255 : Blo 786339 2998255 := bstep (se 1 (by rfl) ⟨2248691, by rfl⟩ : syracuseStep 2998255 = 4497383) B4497383
theorem B11386889 : Blo 786339 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B1261865 : Blo 786339 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B24330557 : Blo 786339 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B1327927 : Blo 786339 1327927 := bstep (se 1 (by rfl) ⟨995945, by rfl⟩ : syracuseStep 1327927 = 1991891) B1991891
theorem B16205579 : Blo 786339 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B19187543 : Blo 786339 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B7194599 : Blo 786339 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B45467729 : Blo 786339 45467729 := bstep (se 2 (by rfl) ⟨17050398, by rfl⟩ : syracuseStep 45467729 = 34100797) B34100797
theorem B5982659 : Blo 786339 5982659 := bstep (se 1 (by rfl) ⟨4486994, by rfl⟩ : syracuseStep 5982659 = 8973989) B8973989
theorem B1330175 : Blo 786339 1330175 := bstep (se 1 (by rfl) ⟨997631, by rfl⟩ : syracuseStep 1330175 = 1995263) B1995263
theorem B1330249 : Blo 786339 1330249 := bstep (se 2 (by rfl) ⟨498843, by rfl⟩ : syracuseStep 1330249 = 997687) B997687
theorem B167955859 : Blo 786339 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B1330843 : Blo 786339 1330843 := bstep (se 1 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 1330843 = 1996265) B1996265
theorem B4804379 : Blo 786339 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B1494875 : Blo 786339 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B11259967 : Blo 786339 11259967 := bstep (se 1 (by rfl) ⟨8444975, by rfl⟩ : syracuseStep 11259967 = 16889951) B16889951
theorem B1495111 : Blo 786339 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B6377687 : Blo 786339 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B1331903 : Blo 786339 1331903 := bstep (se 1 (by rfl) ⟨998927, by rfl⟩ : syracuseStep 1331903 = 1997855) B1997855
theorem B3363727 : Blo 786339 3363727 := bstep (se 1 (by rfl) ⟨2522795, by rfl⟩ : syracuseStep 3363727 = 5045591) B5045591
theorem B3363743 : Blo 786339 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B4478885 : Blo 786339 4478885 := bstep (se 4 (by rfl) ⟨419895, by rfl⟩ : syracuseStep 4478885 = 839791) B839791
theorem B1497055 : Blo 786339 1497055 := bstep (se 1 (by rfl) ⟨1122791, by rfl⟩ : syracuseStep 1497055 = 2245583) B2245583
theorem B1497761 : Blo 786339 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B9591635 : Blo 786339 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B3988601 : Blo 786339 3988601 := bstep (se 2 (by rfl) ⟨1495725, by rfl⟩ : syracuseStep 3988601 = 2991451) B2991451
theorem B65559935 : Blo 786339 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B1992347 : Blo 786339 1992347 := bstep (se 1 (by rfl) ⟨1494260, by rfl⟩ : syracuseStep 1992347 = 2988521) B2988521
theorem B5039927 : Blo 786339 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B11495789 : Blo 786339 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B3992327 : Blo 786339 3992327 := bstep (se 1 (by rfl) ⟨2994245, by rfl⟩ : syracuseStep 3992327 = 5988491) B5988491
theorem B5992865 : Blo 786339 5992865 := bstep (se 2 (by rfl) ⟨2247324, by rfl⟩ : syracuseStep 5992865 = 4494649) B4494649
theorem B65664107 : Blo 786339 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B3995567 : Blo 786339 3995567 := bstep (se 1 (by rfl) ⟨2996675, by rfl⟩ : syracuseStep 3995567 = 5993351) B5993351
theorem B7567499 : Blo 786339 7567499 := bstep (se 1 (by rfl) ⟨5675624, by rfl⟩ : syracuseStep 7567499 = 11351249) B11351249
theorem B21919997 : Blo 786339 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B2882291 : Blo 786339 2882291 := bstep (se 1 (by rfl) ⟨2161718, by rfl⟩ : syracuseStep 2882291 = 4323437) B4323437
theorem B4848427 : Blo 786339 4848427 := bstep (se 1 (by rfl) ⟨3636320, by rfl⟩ : syracuseStep 4848427 = 7272641) B7272641
theorem B9567305 : Blo 786339 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B2391707 : Blo 786339 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B3997511 : Blo 786339 3997511 := bstep (se 1 (by rfl) ⟨2998133, by rfl⟩ : syracuseStep 3997511 = 5996267) B5996267
theorem B1998827 : Blo 786339 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B786459 : Blo 786339 786459 := bstep (se 1 (by rfl) ⟨589844, by rfl⟩ : syracuseStep 786459 = 1179689) B1179689
theorem B1769615 : Blo 786339 1769615 := bstep (se 1 (by rfl) ⟨1327211, by rfl⟩ : syracuseStep 1769615 = 2654423) B2654423
theorem B786587 : Blo 786339 786587 := bstep (se 1 (by rfl) ⟨589940, by rfl⟩ : syracuseStep 786587 = 1179881) B1179881
theorem B16220371 : Blo 786339 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B786655 : Blo 786339 786655 := bstep (se 1 (by rfl) ⟨589991, by rfl⟩ : syracuseStep 786655 = 1179983) B1179983
theorem B786751 : Blo 786339 786751 := bstep (se 1 (by rfl) ⟨590063, by rfl⟩ : syracuseStep 786751 = 1180127) B1180127
theorem B787227 : Blo 786339 787227 := bstep (se 1 (by rfl) ⟨590420, by rfl⟩ : syracuseStep 787227 = 1180841) B1180841
theorem B1770569 : Blo 786339 1770569 := bstep (se 2 (by rfl) ⟨663963, by rfl⟩ : syracuseStep 1770569 = 1327927) B1327927
theorem B1770587 : Blo 786339 1770587 := bstep (se 1 (by rfl) ⟨1327940, by rfl⟩ : syracuseStep 1770587 = 2655881) B2655881
theorem B1180763 : Blo 786339 1180763 := bstep (se 1 (by rfl) ⟨885572, by rfl⟩ : syracuseStep 1180763 = 1771145) B1771145
theorem B1180793 : Blo 786339 1180793 := bstep (se 2 (by rfl) ⟨442797, by rfl⟩ : syracuseStep 1180793 = 885595) B885595
theorem B787815 : Blo 786339 787815 := bstep (se 1 (by rfl) ⟨590861, by rfl⟩ : syracuseStep 787815 = 1181723) B1181723
theorem B30311819 : Blo 786339 30311819 := bstep (se 1 (by rfl) ⟨22733864, by rfl⟩ : syracuseStep 30311819 = 45467729) B45467729
theorem B1181339 : Blo 786339 1181339 := bstep (se 1 (by rfl) ⟨886004, by rfl⟩ : syracuseStep 1181339 = 1772009) B1772009
theorem B788127 : Blo 786339 788127 := bstep (se 1 (by rfl) ⟨591095, by rfl⟩ : syracuseStep 788127 = 1182191) B1182191
theorem B788199 : Blo 786339 788199 := bstep (se 1 (by rfl) ⟨591149, by rfl⟩ : syracuseStep 788199 = 1182299) B1182299
theorem B788383 : Blo 786339 788383 := bstep (se 1 (by rfl) ⟨591287, by rfl⟩ : syracuseStep 788383 = 1182575) B1182575
theorem B788391 : Blo 786339 788391 := bstep (se 1 (by rfl) ⟨591293, by rfl⟩ : syracuseStep 788391 = 1182587) B1182587
theorem B1771487 : Blo 786339 1771487 := bstep (se 1 (by rfl) ⟨1328615, by rfl⟩ : syracuseStep 1771487 = 2657231) B2657231
theorem B886783 : Blo 786339 886783 := bstep (se 1 (by rfl) ⟨665087, by rfl⟩ : syracuseStep 886783 = 1330175) B1330175
theorem B1771559 : Blo 786339 1771559 := bstep (se 1 (by rfl) ⟨1328669, by rfl⟩ : syracuseStep 1771559 = 2657339) B2657339
theorem B788807 : Blo 786339 788807 := bstep (se 1 (by rfl) ⟨591605, by rfl⟩ : syracuseStep 788807 = 1183211) B1183211
theorem B1182107 : Blo 786339 1182107 := bstep (se 1 (by rfl) ⟨886580, by rfl⟩ : syracuseStep 1182107 = 1773161) B1773161
theorem B788975 : Blo 786339 788975 := bstep (se 1 (by rfl) ⟨591731, by rfl⟩ : syracuseStep 788975 = 1183463) B1183463
theorem B1772351 : Blo 786339 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B887935 : Blo 786339 887935 := bstep (se 1 (by rfl) ⟨665951, by rfl⟩ : syracuseStep 887935 = 1331903) B1331903
theorem B789831 : Blo 786339 789831 := bstep (se 1 (by rfl) ⟨592373, by rfl⟩ : syracuseStep 789831 = 1184747) B1184747
theorem B789999 : Blo 786339 789999 := bstep (se 1 (by rfl) ⟨592499, by rfl⟩ : syracuseStep 789999 = 1184999) B1184999
theorem B790171 : Blo 786339 790171 := bstep (se 1 (by rfl) ⟨592628, by rfl⟩ : syracuseStep 790171 = 1185257) B1185257
theorem B1773215 : Blo 786339 1773215 := bstep (se 1 (by rfl) ⟨1329911, by rfl⟩ : syracuseStep 1773215 = 2659823) B2659823
theorem B1183439 : Blo 786339 1183439 := bstep (se 1 (by rfl) ⟨887579, by rfl⟩ : syracuseStep 1183439 = 1775159) B1775159
theorem B2985923 : Blo 786339 2985923 := bstep (se 1 (by rfl) ⟨2239442, by rfl⟩ : syracuseStep 2985923 = 4478885) B4478885
theorem B1773665 : Blo 786339 1773665 := bstep (se 2 (by rfl) ⟨665124, by rfl⟩ : syracuseStep 1773665 = 1330249) B1330249
theorem B1183967 : Blo 786339 1183967 := bstep (se 1 (by rfl) ⟨887975, by rfl⟩ : syracuseStep 1183967 = 1775951) B1775951
theorem B25858277 : Blo 786339 25858277 := bstep (se 4 (by rfl) ⟨2424213, by rfl⟩ : syracuseStep 25858277 = 4848427) B4848427
theorem B223941145 : Blo 786339 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B6394423 : Blo 786339 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B2659067 : Blo 786339 2659067 := bstep (se 1 (by rfl) ⟨1994300, by rfl⟩ : syracuseStep 2659067 = 3988601) B3988601
theorem B1774457 : Blo 786339 1774457 := bstep (se 2 (by rfl) ⟨665421, by rfl⟩ : syracuseStep 1774457 = 1330843) B1330843
theorem B1774547 : Blo 786339 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B1184735 : Blo 786339 1184735 := bstep (se 1 (by rfl) ⟨888551, by rfl⟩ : syracuseStep 1184735 = 1777103) B1777103
theorem B15013289 : Blo 786339 15013289 := bstep (se 2 (by rfl) ⟨5629983, by rfl⟩ : syracuseStep 15013289 = 11259967) B11259967
theorem B1185383 : Blo 786339 1185383 := bstep (se 1 (by rfl) ⟨889037, by rfl⟩ : syracuseStep 1185383 = 1778075) B1778075
theorem B1776239 : Blo 786339 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B2661551 : Blo 786339 2661551 := bstep (se 1 (by rfl) ⟨1996163, by rfl⟩ : syracuseStep 2661551 = 3992327) B3992327
theorem B2564455 : Blo 786339 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B2990753 : Blo 786339 2990753 := bstep (se 2 (by rfl) ⟨1121532, by rfl⟩ : syracuseStep 2990753 = 2243065) B2243065
theorem B2663711 : Blo 786339 2663711 := bstep (se 1 (by rfl) ⟨1997783, by rfl⟩ : syracuseStep 2663711 = 3995567) B3995567
theorem B11347559 : Blo 786339 11347559 := bstep (se 1 (by rfl) ⟨8510669, by rfl⟩ : syracuseStep 11347559 = 17021339) B17021339
theorem B2991725 : Blo 786339 2991725 := bstep (se 3 (by rfl) ⟨560948, by rfl⟩ : syracuseStep 2991725 = 1121897) B1121897
theorem B2665007 : Blo 786339 2665007 := bstep (se 1 (by rfl) ⟨1998755, by rfl⟩ : syracuseStep 2665007 = 3997511) B3997511
theorem B2665385 : Blo 786339 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B54701057 : Blo 786339 54701057 := bstep (se 2 (by rfl) ⟨20512896, by rfl⟩ : syracuseStep 54701057 = 41025793) B41025793
theorem B2993183 : Blo 786339 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B12791695 : Blo 786339 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B4796399 : Blo 786339 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B2242495 : Blo 786339 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B1686143 : Blo 786339 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B1424155 : Blo 786339 1424155 := bstep (se 1 (by rfl) ⟨1068116, by rfl⟩ : syracuseStep 1424155 = 2136233) B2136233
theorem B998507 : Blo 786339 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B1328231 : Blo 786339 1328231 := bstep (se 1 (by rfl) ⟨996173, by rfl⟩ : syracuseStep 1328231 = 1992347) B1992347
theorem B3359951 : Blo 786339 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B7686109 : Blo 786339 7686109 := bstep (se 3 (by rfl) ⟨1441145, by rfl⟩ : syracuseStep 7686109 = 2882291) B2882291
theorem B1493615 : Blo 786339 1493615 := bstep (se 1 (by rfl) ⟨1120211, by rfl⟩ : syracuseStep 1493615 = 2240423) B2240423
theorem B3984551 : Blo 786339 3984551 := bstep (se 1 (by rfl) ⟨2988413, by rfl⟩ : syracuseStep 3984551 = 5976827) B5976827
theorem B3984713 : Blo 786339 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B9981929 : Blo 786339 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B6377885 : Blo 786339 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B6378203 : Blo 786339 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B1495817 : Blo 786339 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B3986333 : Blo 786339 3986333 := bstep (se 3 (by rfl) ⟨747437, by rfl⟩ : syracuseStep 3986333 = 1494875) B1494875
theorem B1495999 : Blo 786339 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B1889561 : Blo 786339 1889561 := bstep (se 2 (by rfl) ⟨708585, by rfl⟩ : syracuseStep 1889561 = 1417171) B1417171
theorem B1332551 : Blo 786339 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B7591259 : Blo 786339 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B12440989 : Blo 786339 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B3364973 : Blo 786339 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B1333631 : Blo 786339 1333631 := bstep (se 1 (by rfl) ⟨1000223, by rfl⟩ : syracuseStep 1333631 = 2000447) B2000447
theorem B10803719 : Blo 786339 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B3988439 : Blo 786339 3988439 := bstep (se 1 (by rfl) ⟨2991329, by rfl⟩ : syracuseStep 3988439 = 5982659) B5982659
theorem B10083437 : Blo 786339 10083437 := bstep (se 3 (by rfl) ⟨1890644, by rfl⟩ : syracuseStep 10083437 = 3781289) B3781289
theorem B123100559 : Blo 786339 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B3366683 : Blo 786339 3366683 := bstep (se 1 (by rfl) ⟨2525012, by rfl⟩ : syracuseStep 3366683 = 5050025) B5050025
theorem B3202919 : Blo 786339 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B54747035 : Blo 786339 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B12148717 : Blo 786339 12148717 := bstep (se 3 (by rfl) ⟨2277884, by rfl⟩ : syracuseStep 12148717 = 4555769) B4555769
theorem B4251791 : Blo 786339 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B1991263 : Blo 786339 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B19162631 : Blo 786339 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B1992559 : Blo 786339 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B1992863 : Blo 786339 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B43706623 : Blo 786339 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B245164529 : Blo 786339 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B1993481 : Blo 786339 1993481 := bstep (se 2 (by rfl) ⟨747555, by rfl⟩ : syracuseStep 1993481 = 1495111) B1495111
theorem B58453325 : Blo 786339 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B4484969 : Blo 786339 4484969 := bstep (se 2 (by rfl) ⟨1681863, by rfl⟩ : syracuseStep 4484969 = 3363727) B3363727
theorem B7663859 : Blo 786339 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B3371807 : Blo 786339 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B1996073 : Blo 786339 1996073 := bstep (se 2 (by rfl) ⟨748527, by rfl⟩ : syracuseStep 1996073 = 1497055) B1497055
theorem B3995243 : Blo 786339 3995243 := bstep (se 1 (by rfl) ⟨2996432, by rfl⟩ : syracuseStep 3995243 = 5992865) B5992865
theorem B43776071 : Blo 786339 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B4487359 : Blo 786339 4487359 := bstep (se 1 (by rfl) ⟨3365519, by rfl⟩ : syracuseStep 4487359 = 6731039) B6731039
theorem B5044999 : Blo 786339 5044999 := bstep (se 1 (by rfl) ⟨3783749, by rfl⟩ : syracuseStep 5044999 = 7567499) B7567499
theorem B1998503 : Blo 786339 1998503 := bstep (se 1 (by rfl) ⟨1498877, by rfl⟩ : syracuseStep 1998503 = 2997755) B2997755
theorem B8880097 : Blo 786339 8880097 := bstep (se 2 (by rfl) ⟨3330036, by rfl⟩ : syracuseStep 8880097 = 6660073) B6660073
theorem B3997673 : Blo 786339 3997673 := bstep (se 2 (by rfl) ⟨1499127, by rfl⟩ : syracuseStep 3997673 = 2998255) B2998255
theorem B1179743 : Blo 786339 1179743 := bstep (se 1 (by rfl) ⟨884807, by rfl⟩ : syracuseStep 1179743 = 1769615) B1769615
theorem B21627161 : Blo 786339 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B1180379 : Blo 786339 1180379 := bstep (se 1 (by rfl) ⟨885284, by rfl⟩ : syracuseStep 1180379 = 1770569) B1770569
theorem B1180391 : Blo 786339 1180391 := bstep (se 1 (by rfl) ⟨885293, by rfl⟩ : syracuseStep 1180391 = 1770587) B1770587
theorem B787175 : Blo 786339 787175 := bstep (se 1 (by rfl) ⟨590381, by rfl⟩ : syracuseStep 787175 = 1180763) B1180763
theorem B885487 : Blo 786339 885487 := bstep (se 1 (by rfl) ⟨664115, by rfl⟩ : syracuseStep 885487 = 1328231) B1328231
theorem B787195 : Blo 786339 787195 := bstep (se 1 (by rfl) ⟨590396, by rfl⟩ : syracuseStep 787195 = 1180793) B1180793
theorem B2655017 : Blo 786339 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B787559 : Blo 786339 787559 := bstep (se 1 (by rfl) ⟨590669, by rfl⟩ : syracuseStep 787559 = 1181339) B1181339
theorem B1180991 : Blo 786339 1180991 := bstep (se 1 (by rfl) ⟨885743, by rfl⟩ : syracuseStep 1180991 = 1771487) B1771487
theorem B1181039 : Blo 786339 1181039 := bstep (se 1 (by rfl) ⟨885779, by rfl⟩ : syracuseStep 1181039 = 1771559) B1771559
theorem B788071 : Blo 786339 788071 := bstep (se 1 (by rfl) ⟨591053, by rfl⟩ : syracuseStep 788071 = 1182107) B1182107
theorem B1181567 : Blo 786339 1181567 := bstep (se 1 (by rfl) ⟨886175, by rfl⟩ : syracuseStep 1181567 = 1772351) B1772351
theorem B17008541 : Blo 786339 17008541 := bstep (se 3 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 17008541 = 6378203) B6378203
theorem B2656367 : Blo 786339 2656367 := bstep (se 1 (by rfl) ⟨1992275, by rfl⟩ : syracuseStep 2656367 = 3984551) B3984551
theorem B2656475 : Blo 786339 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B1182143 : Blo 786339 1182143 := bstep (se 1 (by rfl) ⟨886607, by rfl⟩ : syracuseStep 1182143 = 1773215) B1773215
theorem B788959 : Blo 786339 788959 := bstep (se 1 (by rfl) ⟨591719, by rfl⟩ : syracuseStep 788959 = 1183439) B1183439
theorem B2656745 : Blo 786339 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B6654619 : Blo 786339 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B1182377 : Blo 786339 1182377 := bstep (se 2 (by rfl) ⟨443391, by rfl⟩ : syracuseStep 1182377 = 886783) B886783
theorem B1182443 : Blo 786339 1182443 := bstep (se 1 (by rfl) ⟨886832, by rfl⟩ : syracuseStep 1182443 = 1773665) B1773665
theorem B17238851 : Blo 786339 17238851 := bstep (se 1 (by rfl) ⟨12929138, by rfl⟩ : syracuseStep 17238851 = 25858277) B25858277
theorem B789311 : Blo 786339 789311 := bstep (se 1 (by rfl) ⟨591983, by rfl⟩ : syracuseStep 789311 = 1183967) B1183967
theorem B1772711 : Blo 786339 1772711 := bstep (se 1 (by rfl) ⟨1329533, by rfl⟩ : syracuseStep 1772711 = 2659067) B2659067
theorem B1182971 : Blo 786339 1182971 := bstep (se 1 (by rfl) ⟨887228, by rfl⟩ : syracuseStep 1182971 = 1774457) B1774457
theorem B2657555 : Blo 786339 2657555 := bstep (se 1 (by rfl) ⟨1993166, by rfl⟩ : syracuseStep 2657555 = 3986333) B3986333
theorem B1183031 : Blo 786339 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B789823 : Blo 786339 789823 := bstep (se 1 (by rfl) ⟨592367, by rfl⟩ : syracuseStep 789823 = 1184735) B1184735
theorem B888367 : Blo 786339 888367 := bstep (se 1 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 888367 = 1332551) B1332551
theorem B790255 : Blo 786339 790255 := bstep (se 1 (by rfl) ⟨592691, by rfl⟩ : syracuseStep 790255 = 1185383) B1185383
theorem B1183913 : Blo 786339 1183913 := bstep (se 2 (by rfl) ⟨443967, by rfl⟩ : syracuseStep 1183913 = 887935) B887935
theorem B889087 : Blo 786339 889087 := bstep (se 1 (by rfl) ⟨666815, by rfl⟩ : syracuseStep 889087 = 1333631) B1333631
theorem B1184159 : Blo 786339 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B2658959 : Blo 786339 2658959 := bstep (se 1 (by rfl) ⟨1994219, by rfl⟩ : syracuseStep 2658959 = 3988439) B3988439
theorem B6722291 : Blo 786339 6722291 := bstep (se 1 (by rfl) ⟨5041718, by rfl⟩ : syracuseStep 6722291 = 10083437) B10083437
theorem B1774367 : Blo 786339 1774367 := bstep (se 1 (by rfl) ⟨1330775, by rfl⟩ : syracuseStep 1774367 = 2661551) B2661551
theorem B2135279 : Blo 786339 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B298588193 : Blo 786339 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B8525897 : Blo 786339 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1775807 : Blo 786339 1775807 := bstep (se 1 (by rfl) ⟨1331855, by rfl⟩ : syracuseStep 1775807 = 2663711) B2663711
theorem B28809917 : Blo 786339 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B4496381 : Blo 786339 4496381 := bstep (se 3 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 4496381 = 1686143) B1686143
theorem B1776671 : Blo 786339 1776671 := bstep (se 1 (by rfl) ⟨1332503, by rfl⟩ : syracuseStep 1776671 = 2665007) B2665007
theorem B16587985 : Blo 786339 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B1776923 : Blo 786339 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B38968883 : Blo 786339 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B2989979 : Blo 786339 2989979 := bstep (se 1 (by rfl) ⟨2242484, by rfl⟩ : syracuseStep 2989979 = 4484969) B4484969
theorem B2989993 : Blo 786339 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B2662685 : Blo 786339 2662685 := bstep (se 3 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 2662685 = 998507) B998507
theorem B6726665 : Blo 786339 6726665 := bstep (se 2 (by rfl) ⟨2522499, by rfl⟩ : syracuseStep 6726665 = 5044999) B5044999
theorem B2663495 : Blo 786339 2663495 := bstep (se 1 (by rfl) ⟨1997621, by rfl⟩ : syracuseStep 2663495 = 3995243) B3995243
theorem B11840129 : Blo 786339 11840129 := bstep (se 2 (by rfl) ⟨4440048, by rfl⟩ : syracuseStep 11840129 = 8880097) B8880097
theorem B16198289 : Blo 786339 16198289 := bstep (se 2 (by rfl) ⟨6074358, by rfl⟩ : syracuseStep 16198289 = 12148717) B12148717
theorem B2665115 : Blo 786339 2665115 := bstep (se 1 (by rfl) ⟨1998836, by rfl⟩ : syracuseStep 2665115 = 3997673) B3997673
theorem B3419273 : Blo 786339 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B2239967 : Blo 786339 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B995743 : Blo 786339 995743 := bstep (se 1 (by rfl) ⟨746807, by rfl⟩ : syracuseStep 995743 = 1493615) B1493615
theorem B8991485 : Blo 786339 8991485 := bstep (se 3 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 8991485 = 3371807) B3371807
theorem B58275497 : Blo 786339 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B997211 : Blo 786339 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B1259707 : Blo 786339 1259707 := bstep (se 1 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 1259707 = 1889561) B1889561
theorem B5060839 : Blo 786339 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B2243315 : Blo 786339 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B82067039 : Blo 786339 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B2244455 : Blo 786339 2244455 := bstep (se 1 (by rfl) ⟨1683341, by rfl⟩ : syracuseStep 2244455 = 3366683) B3366683
theorem B17055593 : Blo 786339 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B2834527 : Blo 786339 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B1328575 : Blo 786339 1328575 := bstep (se 1 (by rfl) ⟨996431, by rfl⟩ : syracuseStep 1328575 = 1992863) B1992863
theorem B1328987 : Blo 786339 1328987 := bstep (se 1 (by rfl) ⟨996740, by rfl⟩ : syracuseStep 1328987 = 1993481) B1993481
theorem B3197599 : Blo 786339 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B5983145 : Blo 786339 5983145 := bstep (se 2 (by rfl) ⟨2243679, by rfl⟩ : syracuseStep 5983145 = 4487359) B4487359
theorem B1330715 : Blo 786339 1330715 := bstep (se 1 (by rfl) ⟨998036, by rfl⟩ : syracuseStep 1330715 = 1996073) B1996073
theorem B29184047 : Blo 786339 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B1332335 : Blo 786339 1332335 := bstep (se 1 (by rfl) ⟨999251, by rfl⟩ : syracuseStep 1332335 = 1998503) B1998503
theorem B20207879 : Blo 786339 20207879 := bstep (se 1 (by rfl) ⟨15155909, by rfl⟩ : syracuseStep 20207879 = 30311819) B30311819
theorem B1990615 : Blo 786339 1990615 := bstep (se 1 (by rfl) ⟨1492961, by rfl⟩ : syracuseStep 1990615 = 2985923) B2985923
theorem B4251923 : Blo 786339 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B40035437 : Blo 786339 40035437 := bstep (se 3 (by rfl) ⟨7506644, by rfl⟩ : syracuseStep 40035437 = 15013289) B15013289
theorem B36498023 : Blo 786339 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B1993835 : Blo 786339 1993835 := bstep (se 1 (by rfl) ⟨1495376, by rfl⟩ : syracuseStep 1993835 = 2990753) B2990753
theorem B12775087 : Blo 786339 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B7565039 : Blo 786339 7565039 := bstep (se 1 (by rfl) ⟨5673779, by rfl⟩ : syracuseStep 7565039 = 11347559) B11347559
theorem B1994483 : Blo 786339 1994483 := bstep (se 1 (by rfl) ⟨1495862, by rfl⟩ : syracuseStep 1994483 = 2991725) B2991725
theorem B1994665 : Blo 786339 1994665 := bstep (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) B1495999
theorem B163443019 : Blo 786339 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B36467371 : Blo 786339 36467371 := bstep (se 1 (by rfl) ⟨27350528, by rfl⟩ : syracuseStep 36467371 = 54701057) B54701057
theorem B1995455 : Blo 786339 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B5109239 : Blo 786339 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B1898873 : Blo 786339 1898873 := bstep (se 2 (by rfl) ⟨712077, by rfl⟩ : syracuseStep 1898873 = 1424155) B1424155
theorem B40992581 : Blo 786339 40992581 := bstep (se 4 (by rfl) ⟨3843054, by rfl⟩ : syracuseStep 40992581 = 7686109) B7686109
theorem B786495 : Blo 786339 786495 := bstep (se 1 (by rfl) ⟨589871, by rfl⟩ : syracuseStep 786495 = 1179743) B1179743
theorem B14418107 : Blo 786339 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B786919 : Blo 786339 786919 := bstep (se 1 (by rfl) ⟨590189, by rfl⟩ : syracuseStep 786919 = 1180379) B1180379
theorem B786927 : Blo 786339 786927 := bstep (se 1 (by rfl) ⟨590195, by rfl⟩ : syracuseStep 786927 = 1180391) B1180391
theorem B1770011 : Blo 786339 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B787327 : Blo 786339 787327 := bstep (se 1 (by rfl) ⟨590495, by rfl⟩ : syracuseStep 787327 = 1180991) B1180991
theorem B787359 : Blo 786339 787359 := bstep (se 1 (by rfl) ⟨590519, by rfl⟩ : syracuseStep 787359 = 1181039) B1181039
theorem B1180649 : Blo 786339 1180649 := bstep (se 2 (by rfl) ⟨442743, by rfl⟩ : syracuseStep 1180649 = 885487) B885487
theorem B885991 : Blo 786339 885991 := bstep (se 1 (by rfl) ⟨664493, by rfl⟩ : syracuseStep 885991 = 1328987) B1328987
theorem B787711 : Blo 786339 787711 := bstep (se 1 (by rfl) ⟨590783, by rfl⟩ : syracuseStep 787711 = 1181567) B1181567
theorem B11339027 : Blo 786339 11339027 := bstep (se 1 (by rfl) ⟨8504270, by rfl⟩ : syracuseStep 11339027 = 17008541) B17008541
theorem B1770911 : Blo 786339 1770911 := bstep (se 1 (by rfl) ⟨1328183, by rfl⟩ : syracuseStep 1770911 = 2656367) B2656367
theorem B1770983 : Blo 786339 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B788095 : Blo 786339 788095 := bstep (se 1 (by rfl) ⟨591071, by rfl⟩ : syracuseStep 788095 = 1182143) B1182143
theorem B1771163 : Blo 786339 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B788251 : Blo 786339 788251 := bstep (se 1 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 788251 = 1182377) B1182377
theorem B788295 : Blo 786339 788295 := bstep (se 1 (by rfl) ⟨591221, by rfl⟩ : syracuseStep 788295 = 1182443) B1182443
theorem B1771433 : Blo 786339 1771433 := bstep (se 2 (by rfl) ⟨664287, by rfl⟩ : syracuseStep 1771433 = 1328575) B1328575
theorem B1181807 : Blo 786339 1181807 := bstep (se 1 (by rfl) ⟨886355, by rfl⟩ : syracuseStep 1181807 = 1772711) B1772711
theorem B788647 : Blo 786339 788647 := bstep (se 1 (by rfl) ⟨591485, by rfl⟩ : syracuseStep 788647 = 1182971) B1182971
theorem B1771703 : Blo 786339 1771703 := bstep (se 1 (by rfl) ⟨1328777, by rfl⟩ : syracuseStep 1771703 = 2657555) B2657555
theorem B788687 : Blo 786339 788687 := bstep (se 1 (by rfl) ⟨591515, by rfl⟩ : syracuseStep 788687 = 1183031) B1183031
theorem B887143 : Blo 786339 887143 := bstep (se 1 (by rfl) ⟨665357, by rfl⟩ : syracuseStep 887143 = 1330715) B1330715
theorem B789275 : Blo 786339 789275 := bstep (se 1 (by rfl) ⟨591956, by rfl⟩ : syracuseStep 789275 = 1183913) B1183913
theorem B789439 : Blo 786339 789439 := bstep (se 1 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 789439 = 1184159) B1184159
theorem B1772639 : Blo 786339 1772639 := bstep (se 1 (by rfl) ⟨1329479, by rfl⟩ : syracuseStep 1772639 = 2658959) B2658959
theorem B1182911 : Blo 786339 1182911 := bstep (se 1 (by rfl) ⟨887183, by rfl⟩ : syracuseStep 1182911 = 1774367) B1774367
theorem B888223 : Blo 786339 888223 := bstep (se 1 (by rfl) ⟨666167, by rfl⟩ : syracuseStep 888223 = 1332335) B1332335
theorem B35491301 : Blo 786339 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B1183871 : Blo 786339 1183871 := bstep (se 1 (by rfl) ⟨887903, by rfl⟩ : syracuseStep 1183871 = 1775807) B1775807
theorem B13471919 : Blo 786339 13471919 := bstep (se 1 (by rfl) ⟨10103939, by rfl⟩ : syracuseStep 13471919 = 20207879) B20207879
theorem B19206611 : Blo 786339 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B1184447 : Blo 786339 1184447 := bstep (se 1 (by rfl) ⟨888335, by rfl⟩ : syracuseStep 1184447 = 1776671) B1776671
theorem B1184489 : Blo 786339 1184489 := bstep (se 2 (by rfl) ⟨444183, by rfl⟩ : syracuseStep 1184489 = 888367) B888367
theorem B1184615 : Blo 786339 1184615 := bstep (se 1 (by rfl) ⟨888461, by rfl⟩ : syracuseStep 1184615 = 1776923) B1776923
theorem B2659229 : Blo 786339 2659229 := bstep (se 3 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 2659229 = 997211) B997211
theorem B2659553 : Blo 786339 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B1775123 : Blo 786339 1775123 := bstep (se 1 (by rfl) ⟨1331342, by rfl⟩ : syracuseStep 1775123 = 2662685) B2662685
theorem B1185449 : Blo 786339 1185449 := bstep (se 2 (by rfl) ⟨444543, by rfl⟩ : syracuseStep 1185449 = 889087) B889087
theorem B1775663 : Blo 786339 1775663 := bstep (se 1 (by rfl) ⟨1331747, by rfl⟩ : syracuseStep 1775663 = 2663495) B2663495
theorem B126294709 : Blo 786339 126294709 := bstep (se 5 (by rfl) ⟨5920064, by rfl⟩ : syracuseStep 126294709 = 11840129) B11840129
theorem B1776743 : Blo 786339 1776743 := bstep (se 1 (by rfl) ⟨1332557, by rfl⟩ : syracuseStep 1776743 = 2665115) B2665115
theorem B1679609 : Blo 786339 1679609 := bstep (se 2 (by rfl) ⟨629853, by rfl⟩ : syracuseStep 1679609 = 1259707) B1259707
theorem B3779369 : Blo 786339 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B17053861 : Blo 786339 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B5683931 : Blo 786339 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B155401325 : Blo 786339 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B2997587 : Blo 786339 2997587 := bstep (se 1 (by rfl) ⟨2248190, by rfl⟩ : syracuseStep 2997587 = 4496381) B4496381
theorem B2834615 : Blo 786339 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B217924025 : Blo 786339 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1327657 : Blo 786339 1327657 := bstep (se 2 (by rfl) ⟨497871, by rfl⟩ : syracuseStep 1327657 = 995743) B995743
theorem B26690291 : Blo 786339 26690291 := bstep (se 1 (by rfl) ⟨20017718, by rfl⟩ : syracuseStep 26690291 = 40035437) B40035437
theorem B24332015 : Blo 786339 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B10798859 : Blo 786339 10798859 := bstep (se 1 (by rfl) ⟨8099144, by rfl⟩ : syracuseStep 10798859 = 16198289) B16198289
theorem B5982173 : Blo 786339 5982173 := bstep (se 3 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 5982173 = 2243315) B2243315
theorem B1329223 : Blo 786339 1329223 := bstep (se 1 (by rfl) ⟨996917, by rfl⟩ : syracuseStep 1329223 = 1993835) B1993835
theorem B2279515 : Blo 786339 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B1493311 : Blo 786339 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B1329655 : Blo 786339 1329655 := bstep (se 1 (by rfl) ⟨997241, by rfl⟩ : syracuseStep 1329655 = 1994483) B1994483
theorem B1330303 : Blo 786339 1330303 := bstep (se 1 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 1330303 = 1995455) B1995455
theorem B1265915 : Blo 786339 1265915 := bstep (se 1 (by rfl) ⟨949436, by rfl⟩ : syracuseStep 1265915 = 1898873) B1898873
theorem B54711359 : Blo 786339 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B3986657 : Blo 786339 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B1496303 : Blo 786339 1496303 := bstep (se 1 (by rfl) ⟨1122227, by rfl⟩ : syracuseStep 1496303 = 2244455) B2244455
theorem B11492567 : Blo 786339 11492567 := bstep (se 1 (by rfl) ⟨8619425, by rfl⟩ : syracuseStep 11492567 = 17238851) B17238851
theorem B3988763 : Blo 786339 3988763 := bstep (se 1 (by rfl) ⟨2991572, by rfl⟩ : syracuseStep 3988763 = 5983145) B5983145
theorem B19456031 : Blo 786339 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B4481527 : Blo 786339 4481527 := bstep (se 1 (by rfl) ⟨3361145, by rfl⟩ : syracuseStep 4481527 = 6722291) B6722291
theorem B5694077 : Blo 786339 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B199058795 : Blo 786339 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B17033449 : Blo 786339 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B25979255 : Blo 786339 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B1993319 : Blo 786339 1993319 := bstep (se 1 (by rfl) ⟨1494989, by rfl⟩ : syracuseStep 1993319 = 2989979) B2989979
theorem B4484443 : Blo 786339 4484443 := bstep (se 1 (by rfl) ⟨3363332, by rfl⟩ : syracuseStep 4484443 = 6726665) B6726665
theorem B48623161 : Blo 786339 48623161 := bstep (se 2 (by rfl) ⟨18233685, by rfl⟩ : syracuseStep 48623161 = 36467371) B36467371
theorem B5043359 : Blo 786339 5043359 := bstep (se 1 (by rfl) ⟨3782519, by rfl⟩ : syracuseStep 5043359 = 7565039) B7565039
theorem B6747785 : Blo 786339 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B5994323 : Blo 786339 5994323 := bstep (se 1 (by rfl) ⟨4495742, by rfl⟩ : syracuseStep 5994323 = 8991485) B8991485
theorem B3406159 : Blo 786339 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B22117313 : Blo 786339 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B27328387 : Blo 786339 27328387 := bstep (se 1 (by rfl) ⟨20496290, by rfl⟩ : syracuseStep 27328387 = 40992581) B40992581
theorem B11370395 : Blo 786339 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B2654153 : Blo 786339 2654153 := bstep (se 2 (by rfl) ⟨995307, by rfl⟩ : syracuseStep 2654153 = 1990615) B1990615
theorem B1180007 : Blo 786339 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B17793527 : Blo 786339 17793527 := bstep (se 1 (by rfl) ⟨13345145, by rfl⟩ : syracuseStep 17793527 = 26690291) B26690291
theorem B787099 : Blo 786339 787099 := bstep (se 1 (by rfl) ⟨590324, by rfl⟩ : syracuseStep 787099 = 1180649) B1180649
theorem B1770209 : Blo 786339 1770209 := bstep (se 2 (by rfl) ⟨663828, by rfl⟩ : syracuseStep 1770209 = 1327657) B1327657
theorem B1180607 : Blo 786339 1180607 := bstep (se 1 (by rfl) ⟨885455, by rfl⟩ : syracuseStep 1180607 = 1770911) B1770911
theorem B1180655 : Blo 786339 1180655 := bstep (se 1 (by rfl) ⟨885491, by rfl⟩ : syracuseStep 1180655 = 1770983) B1770983
theorem B1180775 : Blo 786339 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B1180955 : Blo 786339 1180955 := bstep (se 1 (by rfl) ⟨885716, by rfl⟩ : syracuseStep 1180955 = 1771433) B1771433
theorem B787871 : Blo 786339 787871 := bstep (se 1 (by rfl) ⟨590903, by rfl⟩ : syracuseStep 787871 = 1181807) B1181807
theorem B1181135 : Blo 786339 1181135 := bstep (se 1 (by rfl) ⟨885851, by rfl⟩ : syracuseStep 1181135 = 1771703) B1771703
theorem B1181321 : Blo 786339 1181321 := bstep (se 2 (by rfl) ⟨442995, by rfl⟩ : syracuseStep 1181321 = 885991) B885991
theorem B1181759 : Blo 786339 1181759 := bstep (se 1 (by rfl) ⟨886319, by rfl⟩ : syracuseStep 1181759 = 1772639) B1772639
theorem B788607 : Blo 786339 788607 := bstep (se 1 (by rfl) ⟨591455, by rfl⟩ : syracuseStep 788607 = 1182911) B1182911
theorem B23660867 : Blo 786339 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B789247 : Blo 786339 789247 := bstep (se 1 (by rfl) ⟨591935, by rfl⟩ : syracuseStep 789247 = 1183871) B1183871
theorem B1772297 : Blo 786339 1772297 := bstep (se 2 (by rfl) ⟨664611, by rfl⟩ : syracuseStep 1772297 = 1329223) B1329223
theorem B8981279 : Blo 786339 8981279 := bstep (se 1 (by rfl) ⟨6735959, by rfl⟩ : syracuseStep 8981279 = 13471919) B13471919
theorem B22711265 : Blo 786339 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B789631 : Blo 786339 789631 := bstep (se 1 (by rfl) ⟨592223, by rfl⟩ : syracuseStep 789631 = 1184447) B1184447
theorem B1182857 : Blo 786339 1182857 := bstep (se 2 (by rfl) ⟨443571, by rfl⟩ : syracuseStep 1182857 = 887143) B887143
theorem B789659 : Blo 786339 789659 := bstep (se 1 (by rfl) ⟨592244, by rfl⟩ : syracuseStep 789659 = 1184489) B1184489
theorem B789743 : Blo 786339 789743 := bstep (se 1 (by rfl) ⟨592307, by rfl⟩ : syracuseStep 789743 = 1184615) B1184615
theorem B1772819 : Blo 786339 1772819 := bstep (se 1 (by rfl) ⟨1329614, by rfl⟩ : syracuseStep 1772819 = 2659229) B2659229
theorem B1772873 : Blo 786339 1772873 := bstep (se 2 (by rfl) ⟨664827, by rfl⟩ : syracuseStep 1772873 = 1329655) B1329655
theorem B36474239 : Blo 786339 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B2657771 : Blo 786339 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B1773035 : Blo 786339 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B1183415 : Blo 786339 1183415 := bstep (se 1 (by rfl) ⟨887561, by rfl⟩ : syracuseStep 1183415 = 1775123) B1775123
theorem B790299 : Blo 786339 790299 := bstep (se 1 (by rfl) ⟨592724, by rfl⟩ : syracuseStep 790299 = 1185449) B1185449
theorem B1183775 : Blo 786339 1183775 := bstep (se 1 (by rfl) ⟨887831, by rfl⟩ : syracuseStep 1183775 = 1775663) B1775663
theorem B1773737 : Blo 786339 1773737 := bstep (se 2 (by rfl) ⟨665151, by rfl⟩ : syracuseStep 1773737 = 1330303) B1330303
theorem B1184297 : Blo 786339 1184297 := bstep (se 2 (by rfl) ⟨444111, by rfl⟩ : syracuseStep 1184297 = 888223) B888223
theorem B64885373 : Blo 786339 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B1184495 : Blo 786339 1184495 := bstep (se 1 (by rfl) ⟨888371, by rfl⟩ : syracuseStep 1184495 = 1776743) B1776743
theorem B2659175 : Blo 786339 2659175 := bstep (se 1 (by rfl) ⟨1994381, by rfl⟩ : syracuseStep 2659175 = 3988763) B3988763
theorem B1119739 : Blo 786339 1119739 := bstep (se 1 (by rfl) ⟨839804, by rfl⟩ : syracuseStep 1119739 = 1679609) B1679609
theorem B4498523 : Blo 786339 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B7580263 : Blo 786339 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B9612071 : Blo 786339 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B5975369 : Blo 786339 5975369 := bstep (se 2 (by rfl) ⟨2240763, by rfl⟩ : syracuseStep 5975369 = 4481527) B4481527
theorem B15184205 : Blo 786339 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B997535 : Blo 786339 997535 := bstep (se 1 (by rfl) ⟨748151, by rfl⟩ : syracuseStep 997535 = 1496303) B1496303
theorem B5979257 : Blo 786339 5979257 := bstep (se 2 (by rfl) ⟨2242221, by rfl⟩ : syracuseStep 5979257 = 4484443) B4484443
theorem B64830881 : Blo 786339 64830881 := bstep (se 2 (by rfl) ⟨24311580, by rfl⟩ : syracuseStep 64830881 = 48623161) B48623161
theorem B17319503 : Blo 786339 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B1328879 : Blo 786339 1328879 := bstep (se 1 (by rfl) ⟨996659, by rfl⟩ : syracuseStep 1328879 = 1993319) B1993319
theorem B4541545 : Blo 786339 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B3362239 : Blo 786339 3362239 := bstep (se 1 (by rfl) ⟨2521679, by rfl⟩ : syracuseStep 3362239 = 5043359) B5043359
theorem B3789287 : Blo 786339 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B103600883 : Blo 786339 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B1889743 : Blo 786339 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B7559351 : Blo 786339 7559351 := bstep (se 1 (by rfl) ⟨5669513, by rfl⟩ : syracuseStep 7559351 = 11339027) B11339027
theorem B581130733 : Blo 786339 581130733 := bstep (se 3 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 581130733 = 217924025) B217924025
theorem B7199239 : Blo 786339 7199239 := bstep (se 1 (by rfl) ⟨5399429, by rfl⟩ : syracuseStep 7199239 = 10798859) B10798859
theorem B3988115 : Blo 786339 3988115 := bstep (se 1 (by rfl) ⟨2991086, by rfl⟩ : syracuseStep 3988115 = 5982173) B5982173
theorem B3039353 : Blo 786339 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B843943 : Blo 786339 843943 := bstep (se 1 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 843943 = 1265915) B1265915
theorem B12804407 : Blo 786339 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B1991081 : Blo 786339 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B7661711 : Blo 786339 7661711 := bstep (se 1 (by rfl) ⟨5746283, by rfl⟩ : syracuseStep 7661711 = 11492567) B11492567
theorem B12970687 : Blo 786339 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B132705863 : Blo 786339 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B2519579 : Blo 786339 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B22738481 : Blo 786339 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B168392945 : Blo 786339 168392945 := bstep (se 2 (by rfl) ⟨63147354, by rfl⟩ : syracuseStep 168392945 = 126294709) B126294709
theorem B3996215 : Blo 786339 3996215 := bstep (se 1 (by rfl) ⟨2997161, by rfl⟩ : syracuseStep 3996215 = 5994323) B5994323
theorem B14744875 : Blo 786339 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B1998391 : Blo 786339 1998391 := bstep (se 1 (by rfl) ⟨1498793, by rfl⟩ : syracuseStep 1998391 = 2997587) B2997587
theorem B36437849 : Blo 786339 36437849 := bstep (se 2 (by rfl) ⟨13664193, by rfl⟩ : syracuseStep 36437849 = 27328387) B27328387
theorem B1769435 : Blo 786339 1769435 := bstep (se 1 (by rfl) ⟨1327076, by rfl⟩ : syracuseStep 1769435 = 2654153) B2654153
theorem B786671 : Blo 786339 786671 := bstep (se 1 (by rfl) ⟨590003, by rfl⟩ : syracuseStep 786671 = 1180007) B1180007
theorem B1180139 : Blo 786339 1180139 := bstep (se 1 (by rfl) ⟨885104, by rfl⟩ : syracuseStep 1180139 = 1770209) B1770209
theorem B787071 : Blo 786339 787071 := bstep (se 1 (by rfl) ⟨590303, by rfl⟩ : syracuseStep 787071 = 1180607) B1180607
theorem B787103 : Blo 786339 787103 := bstep (se 1 (by rfl) ⟨590327, by rfl⟩ : syracuseStep 787103 = 1180655) B1180655
theorem B787183 : Blo 786339 787183 := bstep (se 1 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 787183 = 1180775) B1180775
theorem B787303 : Blo 786339 787303 := bstep (se 1 (by rfl) ⟨590477, by rfl⟩ : syracuseStep 787303 = 1180955) B1180955
theorem B787423 : Blo 786339 787423 := bstep (se 1 (by rfl) ⟨590567, by rfl⟩ : syracuseStep 787423 = 1181135) B1181135
theorem B787547 : Blo 786339 787547 := bstep (se 1 (by rfl) ⟨590660, by rfl⟩ : syracuseStep 787547 = 1181321) B1181321
theorem B885919 : Blo 786339 885919 := bstep (se 1 (by rfl) ⟨664439, by rfl⟩ : syracuseStep 885919 = 1328879) B1328879
theorem B47449405 : Blo 786339 47449405 := bstep (se 3 (by rfl) ⟨8896763, by rfl⟩ : syracuseStep 47449405 = 17793527) B17793527
theorem B787839 : Blo 786339 787839 := bstep (se 1 (by rfl) ⟨590879, by rfl⟩ : syracuseStep 787839 = 1181759) B1181759
theorem B1181531 : Blo 786339 1181531 := bstep (se 1 (by rfl) ⟨886148, by rfl⟩ : syracuseStep 1181531 = 1772297) B1772297
theorem B15140843 : Blo 786339 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B788571 : Blo 786339 788571 := bstep (se 1 (by rfl) ⟨591428, by rfl⟩ : syracuseStep 788571 = 1182857) B1182857
theorem B1181879 : Blo 786339 1181879 := bstep (se 1 (by rfl) ⟨886409, by rfl⟩ : syracuseStep 1181879 = 1772819) B1772819
theorem B1181915 : Blo 786339 1181915 := bstep (se 1 (by rfl) ⟨886436, by rfl⟩ : syracuseStep 1181915 = 1772873) B1772873
theorem B24316159 : Blo 786339 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B1771847 : Blo 786339 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B1182023 : Blo 786339 1182023 := bstep (se 1 (by rfl) ⟨886517, by rfl⟩ : syracuseStep 1182023 = 1773035) B1773035
theorem B788943 : Blo 786339 788943 := bstep (se 1 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 788943 = 1183415) B1183415
theorem B789183 : Blo 786339 789183 := bstep (se 1 (by rfl) ⟨591887, by rfl⟩ : syracuseStep 789183 = 1183775) B1183775
theorem B1182491 : Blo 786339 1182491 := bstep (se 1 (by rfl) ⟨886868, by rfl⟩ : syracuseStep 1182491 = 1773737) B1773737
theorem B2526191 : Blo 786339 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B789531 : Blo 786339 789531 := bstep (se 1 (by rfl) ⟨592148, by rfl⟩ : syracuseStep 789531 = 1184297) B1184297
theorem B43256915 : Blo 786339 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B789663 : Blo 786339 789663 := bstep (se 1 (by rfl) ⟨592247, by rfl⟩ : syracuseStep 789663 = 1184495) B1184495
theorem B1772783 : Blo 786339 1772783 := bstep (se 1 (by rfl) ⟨1329587, by rfl⟩ : syracuseStep 1772783 = 2659175) B2659175
theorem B2658743 : Blo 786339 2658743 := bstep (se 1 (by rfl) ⟨1994057, by rfl⟩ : syracuseStep 2658743 = 3988115) B3988115
theorem B2660093 : Blo 786339 2660093 := bstep (se 3 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 2660093 = 997535) B997535
theorem B1679719 : Blo 786339 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B774840977 : Blo 786339 774840977 := bstep (se 2 (by rfl) ⟨290565366, by rfl⟩ : syracuseStep 774840977 = 581130733) B581130733
theorem B2664143 : Blo 786339 2664143 := bstep (se 1 (by rfl) ⟨1998107, by rfl⟩ : syracuseStep 2664143 = 3996215) B3996215
theorem B2664521 : Blo 786339 2664521 := bstep (se 2 (by rfl) ⟨999195, by rfl⟩ : syracuseStep 2664521 = 1998391) B1998391
theorem B24291899 : Blo 786339 24291899 := bstep (se 1 (by rfl) ⟨18218924, by rfl⟩ : syracuseStep 24291899 = 36437849) B36437849
theorem B1125257 : Blo 786339 1125257 := bstep (se 2 (by rfl) ⟨421971, by rfl⟩ : syracuseStep 1125257 = 843943) B843943
theorem B11546335 : Blo 786339 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B10107017 : Blo 786339 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B8536271 : Blo 786339 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B1327387 : Blo 786339 1327387 := bstep (se 1 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 1327387 = 1991081) B1991081
theorem B2999015 : Blo 786339 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B63095645 : Blo 786339 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B6408047 : Blo 786339 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B1492985 : Blo 786339 1492985 := bstep (se 2 (by rfl) ⟨559869, by rfl⟩ : syracuseStep 1492985 = 1119739) B1119739
theorem B3983579 : Blo 786339 3983579 := bstep (se 1 (by rfl) ⟨2987684, by rfl⟩ : syracuseStep 3983579 = 5975369) B5975369
theorem B15158987 : Blo 786339 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B3986171 : Blo 786339 3986171 := bstep (se 1 (by rfl) ⟨2989628, by rfl⟩ : syracuseStep 3986171 = 5979257) B5979257
theorem B5987519 : Blo 786339 5987519 := bstep (se 1 (by rfl) ⟨4490639, by rfl⟩ : syracuseStep 5987519 = 8981279) B8981279
theorem B69067255 : Blo 786339 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B17294249 : Blo 786339 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B5039567 : Blo 786339 5039567 := bstep (se 1 (by rfl) ⟨3779675, by rfl⟩ : syracuseStep 5039567 = 7559351) B7559351
theorem B6055393 : Blo 786339 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B4482985 : Blo 786339 4482985 := bstep (se 2 (by rfl) ⟨1681119, by rfl⟩ : syracuseStep 4482985 = 3362239) B3362239
theorem B2026235 : Blo 786339 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B5107807 : Blo 786339 5107807 := bstep (se 1 (by rfl) ⟨3830855, by rfl⟩ : syracuseStep 5107807 = 7661711) B7661711
theorem B2519657 : Blo 786339 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B88470575 : Blo 786339 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B10122803 : Blo 786339 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B9598985 : Blo 786339 9598985 := bstep (se 2 (by rfl) ⟨3599619, by rfl⟩ : syracuseStep 9598985 = 7199239) B7199239
theorem B112261963 : Blo 786339 112261963 := bstep (se 1 (by rfl) ⟨84196472, by rfl⟩ : syracuseStep 112261963 = 168392945) B168392945
theorem B19659833 : Blo 786339 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B43220587 : Blo 786339 43220587 := bstep (se 1 (by rfl) ⟨32415440, by rfl⟩ : syracuseStep 43220587 = 64830881) B64830881
theorem B1179623 : Blo 786339 1179623 := bstep (se 1 (by rfl) ⟨884717, by rfl⟩ : syracuseStep 1179623 = 1769435) B1769435
theorem B786759 : Blo 786339 786759 := bstep (se 1 (by rfl) ⟨590069, by rfl⟩ : syracuseStep 786759 = 1180139) B1180139
theorem B1769849 : Blo 786339 1769849 := bstep (se 2 (by rfl) ⟨663693, by rfl⟩ : syracuseStep 1769849 = 1327387) B1327387
theorem B1999343 : Blo 786339 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B787687 : Blo 786339 787687 := bstep (se 1 (by rfl) ⟨590765, by rfl⟩ : syracuseStep 787687 = 1181531) B1181531
theorem B10093895 : Blo 786339 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B787919 : Blo 786339 787919 := bstep (se 1 (by rfl) ⟨590939, by rfl⟩ : syracuseStep 787919 = 1181879) B1181879
theorem B2655719 : Blo 786339 2655719 := bstep (se 1 (by rfl) ⟨1991789, by rfl⟩ : syracuseStep 2655719 = 3983579) B3983579
theorem B787943 : Blo 786339 787943 := bstep (se 1 (by rfl) ⟨590957, by rfl⟩ : syracuseStep 787943 = 1181915) B1181915
theorem B1181225 : Blo 786339 1181225 := bstep (se 2 (by rfl) ⟨442959, by rfl⟩ : syracuseStep 1181225 = 885919) B885919
theorem B1181231 : Blo 786339 1181231 := bstep (se 1 (by rfl) ⟨885923, by rfl⟩ : syracuseStep 1181231 = 1771847) B1771847
theorem B788015 : Blo 786339 788015 := bstep (se 1 (by rfl) ⟨591011, by rfl⟩ : syracuseStep 788015 = 1182023) B1182023
theorem B788327 : Blo 786339 788327 := bstep (se 1 (by rfl) ⟨591245, by rfl⟩ : syracuseStep 788327 = 1182491) B1182491
theorem B28837943 : Blo 786339 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B1181855 : Blo 786339 1181855 := bstep (se 1 (by rfl) ⟨886391, by rfl⟩ : syracuseStep 1181855 = 1772783) B1772783
theorem B1772495 : Blo 786339 1772495 := bstep (se 1 (by rfl) ⟨1329371, by rfl⟩ : syracuseStep 1772495 = 2658743) B2658743
theorem B2657447 : Blo 786339 2657447 := bstep (se 1 (by rfl) ⟨1993085, by rfl⟩ : syracuseStep 2657447 = 3986171) B3986171
theorem B1773395 : Blo 786339 1773395 := bstep (se 1 (by rfl) ⟨1330046, by rfl⟩ : syracuseStep 1773395 = 2660093) B2660093
theorem B516560651 : Blo 786339 516560651 := bstep (se 1 (by rfl) ⟨387420488, by rfl⟩ : syracuseStep 516560651 = 774840977) B774840977
theorem B1776095 : Blo 786339 1776095 := bstep (se 1 (by rfl) ⟨1332071, by rfl⟩ : syracuseStep 1776095 = 2664143) B2664143
theorem B1776347 : Blo 786339 1776347 := bstep (se 1 (by rfl) ⟨1332260, by rfl⟩ : syracuseStep 1776347 = 2664521) B2664521
theorem B16194599 : Blo 786339 16194599 := bstep (se 1 (by rfl) ⟨12145949, by rfl⟩ : syracuseStep 16194599 = 24291899) B24291899
theorem B1679771 : Blo 786339 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B6399323 : Blo 786339 6399323 := bstep (se 1 (by rfl) ⟨4799492, by rfl⟩ : syracuseStep 6399323 = 9598985) B9598985
theorem B2239625 : Blo 786339 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B92089673 : Blo 786339 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B4272031 : Blo 786339 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B995323 : Blo 786339 995323 := bstep (se 1 (by rfl) ⟨746492, by rfl⟩ : syracuseStep 995323 = 1492985) B1492985
theorem B8073857 : Blo 786339 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B1684127 : Blo 786339 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B46117997 : Blo 786339 46117997 := bstep (se 3 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 46117997 = 17294249) B17294249
theorem B10105991 : Blo 786339 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B5977313 : Blo 786339 5977313 := bstep (se 2 (by rfl) ⟨2241492, by rfl⟩ : syracuseStep 5977313 = 4482985) B4482985
theorem B32421545 : Blo 786339 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B3359711 : Blo 786339 3359711 := bstep (se 1 (by rfl) ⟨2519783, by rfl⟩ : syracuseStep 3359711 = 5039567) B5039567
theorem B3000685 : Blo 786339 3000685 := bstep (se 3 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 3000685 = 1125257) B1125257
theorem B6738011 : Blo 786339 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B57627449 : Blo 786339 57627449 := bstep (se 2 (by rfl) ⟨21610293, by rfl⟩ : syracuseStep 57627449 = 43220587) B43220587
theorem B22763389 : Blo 786339 22763389 := bstep (se 3 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 22763389 = 8536271) B8536271
theorem B63265873 : Blo 786339 63265873 := bstep (se 2 (by rfl) ⟨23724702, by rfl⟩ : syracuseStep 63265873 = 47449405) B47449405
theorem B168255053 : Blo 786339 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B3991679 : Blo 786339 3991679 := bstep (se 1 (by rfl) ⟨2993759, by rfl⟩ : syracuseStep 3991679 = 5987519) B5987519
theorem B15395113 : Blo 786339 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B6810409 : Blo 786339 6810409 := bstep (se 2 (by rfl) ⟨2553903, by rfl⟩ : syracuseStep 6810409 = 5107807) B5107807
theorem B5403293 : Blo 786339 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B58980383 : Blo 786339 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B6748535 : Blo 786339 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B149682617 : Blo 786339 149682617 := bstep (se 2 (by rfl) ⟨56130981, by rfl⟩ : syracuseStep 149682617 = 112261963) B112261963
theorem B13106555 : Blo 786339 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B786415 : Blo 786339 786415 := bstep (se 1 (by rfl) ⟨589811, by rfl⟩ : syracuseStep 786415 = 1179623) B1179623
theorem B1179899 : Blo 786339 1179899 := bstep (se 1 (by rfl) ⟨884924, by rfl⟩ : syracuseStep 1179899 = 1769849) B1769849
theorem B1770479 : Blo 786339 1770479 := bstep (se 1 (by rfl) ⟨1327859, by rfl⟩ : syracuseStep 1770479 = 2655719) B2655719
theorem B787483 : Blo 786339 787483 := bstep (se 1 (by rfl) ⟨590612, by rfl⟩ : syracuseStep 787483 = 1181225) B1181225
theorem B787487 : Blo 786339 787487 := bstep (se 1 (by rfl) ⟨590615, by rfl⟩ : syracuseStep 787487 = 1181231) B1181231
theorem B787903 : Blo 786339 787903 := bstep (se 1 (by rfl) ⟨590927, by rfl⟩ : syracuseStep 787903 = 1181855) B1181855
theorem B21530285 : Blo 786339 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B1181663 : Blo 786339 1181663 := bstep (se 1 (by rfl) ⟨886247, by rfl⟩ : syracuseStep 1181663 = 1772495) B1772495
theorem B1771631 : Blo 786339 1771631 := bstep (se 1 (by rfl) ⟨1328723, by rfl⟩ : syracuseStep 1771631 = 2657447) B2657447
theorem B1182263 : Blo 786339 1182263 := bstep (se 1 (by rfl) ⟨886697, by rfl⟩ : syracuseStep 1182263 = 1773395) B1773395
theorem B4492007 : Blo 786339 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B4000913 : Blo 786339 4000913 := bstep (se 2 (by rfl) ⟨1500342, by rfl⟩ : syracuseStep 4000913 = 3000685) B3000685
theorem B9080545 : Blo 786339 9080545 := bstep (se 2 (by rfl) ⟨3405204, by rfl⟩ : syracuseStep 9080545 = 6810409) B6810409
theorem B1184063 : Blo 786339 1184063 := bstep (se 1 (by rfl) ⟨888047, by rfl⟩ : syracuseStep 1184063 = 1776095) B1776095
theorem B1184231 : Blo 786339 1184231 := bstep (se 1 (by rfl) ⟨888173, by rfl⟩ : syracuseStep 1184231 = 1776347) B1776347
theorem B112170035 : Blo 786339 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B1119847 : Blo 786339 1119847 := bstep (se 1 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 1119847 = 1679771) B1679771
theorem B4266215 : Blo 786339 4266215 := bstep (se 1 (by rfl) ⟨3199661, by rfl⟩ : syracuseStep 4266215 = 6399323) B6399323
theorem B2661119 : Blo 786339 2661119 := bstep (se 1 (by rfl) ⟨1995839, by rfl⟩ : syracuseStep 2661119 = 3991679) B3991679
theorem B30351185 : Blo 786339 30351185 := bstep (se 2 (by rfl) ⟨11381694, by rfl⟩ : syracuseStep 30351185 = 22763389) B22763389
theorem B1122751 : Blo 786339 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B30745331 : Blo 786339 30745331 := bstep (se 1 (by rfl) ⟨23058998, by rfl⟩ : syracuseStep 30745331 = 46117997) B46117997
theorem B84354497 : Blo 786339 84354497 := bstep (se 2 (by rfl) ⟨31632936, by rfl⟩ : syracuseStep 84354497 = 63265873) B63265873
theorem B4499023 : Blo 786339 4499023 := bstep (se 1 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 4499023 = 6748535) B6748535
theorem B99788411 : Blo 786339 99788411 := bstep (se 1 (by rfl) ⟨74841308, by rfl⟩ : syracuseStep 99788411 = 149682617) B149682617
theorem B2239807 : Blo 786339 2239807 := bstep (se 1 (by rfl) ⟨1679855, by rfl⟩ : syracuseStep 2239807 = 3359711) B3359711
theorem B6729263 : Blo 786339 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B20526817 : Blo 786339 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B38418299 : Blo 786339 38418299 := bstep (se 1 (by rfl) ⟨28813724, by rfl⟩ : syracuseStep 38418299 = 57627449) B57627449
theorem B344373767 : Blo 786339 344373767 := bstep (se 1 (by rfl) ⟨258280325, by rfl⟩ : syracuseStep 344373767 = 516560651) B516560651
theorem B10796399 : Blo 786339 10796399 := bstep (se 1 (by rfl) ⟨8097299, by rfl⟩ : syracuseStep 10796399 = 16194599) B16194599
theorem B1327097 : Blo 786339 1327097 := bstep (se 2 (by rfl) ⟨497661, by rfl⟩ : syracuseStep 1327097 = 995323) B995323
theorem B1493083 : Blo 786339 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B61393115 : Blo 786339 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B6737327 : Blo 786339 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B3984875 : Blo 786339 3984875 := bstep (se 1 (by rfl) ⟨2988656, by rfl⟩ : syracuseStep 3984875 = 5977313) B5977313
theorem B21614363 : Blo 786339 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B8737703 : Blo 786339 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B1332895 : Blo 786339 1332895 := bstep (se 1 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 1332895 = 1999343) B1999343
theorem B19225295 : Blo 786339 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B5696041 : Blo 786339 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B3602195 : Blo 786339 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B39320255 : Blo 786339 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B786599 : Blo 786339 786599 := bstep (se 1 (by rfl) ⟨589949, by rfl⟩ : syracuseStep 786599 = 1179899) B1179899
theorem B1180319 : Blo 786339 1180319 := bstep (se 1 (by rfl) ⟨885239, by rfl⟩ : syracuseStep 1180319 = 1770479) B1770479
theorem B14353523 : Blo 786339 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B787775 : Blo 786339 787775 := bstep (se 1 (by rfl) ⟨590831, by rfl⟩ : syracuseStep 787775 = 1181663) B1181663
theorem B1181087 : Blo 786339 1181087 := bstep (se 1 (by rfl) ⟨885815, by rfl⟩ : syracuseStep 1181087 = 1771631) B1771631
theorem B40928743 : Blo 786339 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B788175 : Blo 786339 788175 := bstep (se 1 (by rfl) ⟨591131, by rfl⟩ : syracuseStep 788175 = 1182263) B1182263
theorem B5998697 : Blo 786339 5998697 := bstep (se 2 (by rfl) ⟨2249511, by rfl⟩ : syracuseStep 5998697 = 4499023) B4499023
theorem B4491551 : Blo 786339 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B2656583 : Blo 786339 2656583 := bstep (se 1 (by rfl) ⟨1992437, by rfl⟩ : syracuseStep 2656583 = 3984875) B3984875
theorem B789375 : Blo 786339 789375 := bstep (se 1 (by rfl) ⟨592031, by rfl⟩ : syracuseStep 789375 = 1184063) B1184063
theorem B789487 : Blo 786339 789487 := bstep (se 1 (by rfl) ⟨592115, by rfl⟩ : syracuseStep 789487 = 1184231) B1184231
theorem B74780023 : Blo 786339 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B2986409 : Blo 786339 2986409 := bstep (se 2 (by rfl) ⟨1119903, by rfl⟩ : syracuseStep 2986409 = 2239807) B2239807
theorem B12816863 : Blo 786339 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B1774079 : Blo 786339 1774079 := bstep (se 1 (by rfl) ⟨1330559, by rfl⟩ : syracuseStep 1774079 = 2661119) B2661119
theorem B56236331 : Blo 786339 56236331 := bstep (se 1 (by rfl) ⟨42177248, by rfl⟩ : syracuseStep 56236331 = 84354497) B84354497
theorem B66525607 : Blo 786339 66525607 := bstep (se 1 (by rfl) ⟨49894205, by rfl⟩ : syracuseStep 66525607 = 99788411) B99788411
theorem B1777193 : Blo 786339 1777193 := bstep (se 2 (by rfl) ⟨666447, by rfl⟩ : syracuseStep 1777193 = 1332895) B1332895
theorem B27369089 : Blo 786339 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B2401463 : Blo 786339 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B229582511 : Blo 786339 229582511 := bstep (se 1 (by rfl) ⟨172186883, by rfl⟩ : syracuseStep 229582511 = 344373767) B344373767
theorem B2994671 : Blo 786339 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B2667275 : Blo 786339 2667275 := bstep (se 1 (by rfl) ⟨2000456, by rfl⟩ : syracuseStep 2667275 = 4000913) B4000913
theorem B12107393 : Blo 786339 12107393 := bstep (se 2 (by rfl) ⟨4540272, by rfl⟩ : syracuseStep 12107393 = 9080545) B9080545
theorem B20234123 : Blo 786339 20234123 := bstep (se 1 (by rfl) ⟨15175592, by rfl⟩ : syracuseStep 20234123 = 30351185) B30351185
theorem B20496887 : Blo 786339 20496887 := bstep (se 1 (by rfl) ⟨15372665, by rfl⟩ : syracuseStep 20496887 = 30745331) B30745331
theorem B1493129 : Blo 786339 1493129 := bstep (se 2 (by rfl) ⟨559923, by rfl⟩ : syracuseStep 1493129 = 1119847) B1119847
theorem B25612199 : Blo 786339 25612199 := bstep (se 1 (by rfl) ⟨19209149, by rfl⟩ : syracuseStep 25612199 = 38418299) B38418299
theorem B7197599 : Blo 786339 7197599 := bstep (se 1 (by rfl) ⟨5398199, by rfl⟩ : syracuseStep 7197599 = 10796399) B10796399
theorem B5988005 : Blo 786339 5988005 := bstep (se 4 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 5988005 = 1122751) B1122751
theorem B14409575 : Blo 786339 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B1990777 : Blo 786339 1990777 := bstep (se 2 (by rfl) ⟨746541, by rfl⟩ : syracuseStep 1990777 = 1493083) B1493083
theorem B5825135 : Blo 786339 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B7594721 : Blo 786339 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B2844143 : Blo 786339 2844143 := bstep (se 1 (by rfl) ⟨2133107, by rfl⟩ : syracuseStep 2844143 = 4266215) B4266215
theorem B4486175 : Blo 786339 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B26213503 : Blo 786339 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B884731 : Blo 786339 884731 := bstep (se 1 (by rfl) ⟨663548, by rfl⟩ : syracuseStep 884731 = 1327097) B1327097
theorem B2654369 : Blo 786339 2654369 := bstep (se 2 (by rfl) ⟨995388, by rfl⟩ : syracuseStep 2654369 = 1990777) B1990777
theorem B13664591 : Blo 786339 13664591 := bstep (se 1 (by rfl) ⟨10248443, by rfl⟩ : syracuseStep 13664591 = 20496887) B20496887
theorem B786879 : Blo 786339 786879 := bstep (se 1 (by rfl) ⟨590159, by rfl⟩ : syracuseStep 786879 = 1180319) B1180319
theorem B9569015 : Blo 786339 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B787391 : Blo 786339 787391 := bstep (se 1 (by rfl) ⟨590543, by rfl⟩ : syracuseStep 787391 = 1181087) B1181087
theorem B3999131 : Blo 786339 3999131 := bstep (se 1 (by rfl) ⟨2999348, by rfl⟩ : syracuseStep 3999131 = 5998697) B5998697
theorem B1771055 : Blo 786339 1771055 := bstep (se 1 (by rfl) ⟨1328291, by rfl⟩ : syracuseStep 1771055 = 2656583) B2656583
theorem B15533693 : Blo 786339 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B17074799 : Blo 786339 17074799 := bstep (se 1 (by rfl) ⟨12806099, by rfl⟩ : syracuseStep 17074799 = 25612199) B25612199
theorem B1182719 : Blo 786339 1182719 := bstep (se 1 (by rfl) ⟨887039, by rfl⟩ : syracuseStep 1182719 = 1774079) B1774079
theorem B37490887 : Blo 786339 37490887 := bstep (se 1 (by rfl) ⟨28118165, by rfl⟩ : syracuseStep 37490887 = 56236331) B56236331
theorem B1184795 : Blo 786339 1184795 := bstep (se 1 (by rfl) ⟨888596, by rfl⟩ : syracuseStep 1184795 = 1777193) B1777193
theorem B9606383 : Blo 786339 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B1778183 : Blo 786339 1778183 := bstep (se 1 (by rfl) ⟨1333637, by rfl⟩ : syracuseStep 1778183 = 2667275) B2667275
theorem B2990783 : Blo 786339 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B8071595 : Blo 786339 8071595 := bstep (se 1 (by rfl) ⟨6053696, by rfl⟩ : syracuseStep 8071595 = 12107393) B12107393
theorem B995419 : Blo 786339 995419 := bstep (se 1 (by rfl) ⟨746564, by rfl⟩ : syracuseStep 995419 = 1493129) B1493129
theorem B2994367 : Blo 786339 2994367 := bstep (se 1 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 2994367 = 4491551) B4491551
theorem B54571657 : Blo 786339 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B4798399 : Blo 786339 4798399 := bstep (se 1 (by rfl) ⟨3598799, by rfl⟩ : syracuseStep 4798399 = 7197599) B7197599
theorem B5063147 : Blo 786339 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B34951337 : Blo 786339 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B13489415 : Blo 786339 13489415 := bstep (se 1 (by rfl) ⟨10117061, by rfl⟩ : syracuseStep 13489415 = 20234123) B20234123
theorem B354803237 : Blo 786339 354803237 := bstep (se 4 (by rfl) ⟨33262803, by rfl⟩ : syracuseStep 354803237 = 66525607) B66525607
theorem B1990939 : Blo 786339 1990939 := bstep (se 1 (by rfl) ⟨1493204, by rfl⟩ : syracuseStep 1990939 = 2986409) B2986409
theorem B8544575 : Blo 786339 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B99706697 : Blo 786339 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B18246059 : Blo 786339 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B3992003 : Blo 786339 3992003 := bstep (se 1 (by rfl) ⟨2994002, by rfl⟩ : syracuseStep 3992003 = 5988005) B5988005
theorem B1600975 : Blo 786339 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B1896095 : Blo 786339 1896095 := bstep (se 1 (by rfl) ⟨1422071, by rfl⟩ : syracuseStep 1896095 = 2844143) B2844143
theorem B153055007 : Blo 786339 153055007 := bstep (se 1 (by rfl) ⟨114791255, by rfl⟩ : syracuseStep 153055007 = 229582511) B229582511
theorem B1996447 : Blo 786339 1996447 := bstep (se 1 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 1996447 = 2994671) B2994671
theorem B1179641 : Blo 786339 1179641 := bstep (se 2 (by rfl) ⟨442365, by rfl⟩ : syracuseStep 1179641 = 884731) B884731
theorem B1769579 : Blo 786339 1769579 := bstep (se 1 (by rfl) ⟨1327184, by rfl⟩ : syracuseStep 1769579 = 2654369) B2654369
theorem B9109727 : Blo 786339 9109727 := bstep (se 1 (by rfl) ⟨6832295, by rfl⟩ : syracuseStep 9109727 = 13664591) B13664591
theorem B3375431 : Blo 786339 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B2654585 : Blo 786339 2654585 := bstep (se 2 (by rfl) ⟨995469, by rfl⟩ : syracuseStep 2654585 = 1990939) B1990939
theorem B1180703 : Blo 786339 1180703 := bstep (se 1 (by rfl) ⟨885527, by rfl⟩ : syracuseStep 1180703 = 1771055) B1771055
theorem B10355795 : Blo 786339 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B788479 : Blo 786339 788479 := bstep (se 1 (by rfl) ⟨591359, by rfl⟩ : syracuseStep 788479 = 1182719) B1182719
theorem B23300891 : Blo 786339 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B789863 : Blo 786339 789863 := bstep (se 1 (by rfl) ⟨592397, by rfl⟩ : syracuseStep 789863 = 1184795) B1184795
theorem B2134633 : Blo 786339 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B1185455 : Blo 786339 1185455 := bstep (se 1 (by rfl) ⟨889091, by rfl⟩ : syracuseStep 1185455 = 1778183) B1778183
theorem B5381063 : Blo 786339 5381063 := bstep (se 1 (by rfl) ⟨4035797, by rfl⟩ : syracuseStep 5381063 = 8071595) B8071595
theorem B12164039 : Blo 786339 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B2661335 : Blo 786339 2661335 := bstep (se 1 (by rfl) ⟨1996001, by rfl⟩ : syracuseStep 2661335 = 3992003) B3992003
theorem B2661929 : Blo 786339 2661929 := bstep (se 2 (by rfl) ⟨998223, by rfl⟩ : syracuseStep 2661929 = 1996447) B1996447
theorem B6397865 : Blo 786339 6397865 := bstep (se 2 (by rfl) ⟨2399199, by rfl⟩ : syracuseStep 6397865 = 4798399) B4798399
theorem B5056253 : Blo 786339 5056253 := bstep (se 3 (by rfl) ⟨948047, by rfl⟩ : syracuseStep 5056253 = 1896095) B1896095
theorem B22785533 : Blo 786339 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B2666087 : Blo 786339 2666087 := bstep (se 1 (by rfl) ⟨1999565, by rfl⟩ : syracuseStep 2666087 = 3999131) B3999131
theorem B11383199 : Blo 786339 11383199 := bstep (se 1 (by rfl) ⟨8537399, by rfl⟩ : syracuseStep 11383199 = 17074799) B17074799
theorem B6404255 : Blo 786339 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B8992943 : Blo 786339 8992943 := bstep (se 1 (by rfl) ⟨6744707, by rfl⟩ : syracuseStep 8992943 = 13489415) B13489415
theorem B236535491 : Blo 786339 236535491 := bstep (se 1 (by rfl) ⟨177401618, by rfl⟩ : syracuseStep 236535491 = 354803237) B354803237
theorem B1327225 : Blo 786339 1327225 := bstep (se 2 (by rfl) ⟨497709, by rfl⟩ : syracuseStep 1327225 = 995419) B995419
theorem B49987849 : Blo 786339 49987849 := bstep (se 2 (by rfl) ⟨18745443, by rfl⟩ : syracuseStep 49987849 = 37490887) B37490887
theorem B72762209 : Blo 786339 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B66471131 : Blo 786339 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B6379343 : Blo 786339 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B786427 : Blo 786339 786427 := bstep (se 1 (by rfl) ⟨589820, by rfl⟩ : syracuseStep 786427 = 1179641) B1179641
theorem B3992489 : Blo 786339 3992489 := bstep (se 2 (by rfl) ⟨1497183, by rfl⟩ : syracuseStep 3992489 = 2994367) B2994367
theorem B1993855 : Blo 786339 1993855 := bstep (se 1 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 1993855 = 2990783) B2990783
theorem B102036671 : Blo 786339 102036671 := bstep (se 1 (by rfl) ⟨76527503, by rfl⟩ : syracuseStep 102036671 = 153055007) B153055007
theorem B1179719 : Blo 786339 1179719 := bstep (se 1 (by rfl) ⟨884789, by rfl⟩ : syracuseStep 1179719 = 1769579) B1769579
theorem B1769633 : Blo 786339 1769633 := bstep (se 2 (by rfl) ⟨663612, by rfl⟩ : syracuseStep 1769633 = 1327225) B1327225
theorem B1769723 : Blo 786339 1769723 := bstep (se 1 (by rfl) ⟨1327292, by rfl⟩ : syracuseStep 1769723 = 2654585) B2654585
theorem B66650465 : Blo 786339 66650465 := bstep (se 2 (by rfl) ⟨24993924, by rfl⟩ : syracuseStep 66650465 = 49987849) B49987849
theorem B787135 : Blo 786339 787135 := bstep (se 1 (by rfl) ⟨590351, by rfl⟩ : syracuseStep 787135 = 1180703) B1180703
theorem B15533927 : Blo 786339 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B790303 : Blo 786339 790303 := bstep (se 1 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 790303 = 1185455) B1185455
theorem B2658473 : Blo 786339 2658473 := bstep (se 2 (by rfl) ⟨996927, by rfl⟩ : syracuseStep 2658473 = 1993855) B1993855
theorem B1774223 : Blo 786339 1774223 := bstep (se 1 (by rfl) ⟨1330667, by rfl⟩ : syracuseStep 1774223 = 2661335) B2661335
theorem B1774619 : Blo 786339 1774619 := bstep (se 1 (by rfl) ⟨1330964, by rfl⟩ : syracuseStep 1774619 = 2661929) B2661929
theorem B4265243 : Blo 786339 4265243 := bstep (se 1 (by rfl) ⟨3198932, by rfl⟩ : syracuseStep 4265243 = 6397865) B6397865
theorem B2661659 : Blo 786339 2661659 := bstep (se 1 (by rfl) ⟨1996244, by rfl⟩ : syracuseStep 2661659 = 3992489) B3992489
theorem B1777391 : Blo 786339 1777391 := bstep (se 1 (by rfl) ⟨1333043, by rfl⟩ : syracuseStep 1777391 = 2666087) B2666087
theorem B4269503 : Blo 786339 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B157690327 : Blo 786339 157690327 := bstep (se 1 (by rfl) ⟨118267745, by rfl⟩ : syracuseStep 157690327 = 236535491) B236535491
theorem B6073151 : Blo 786339 6073151 := bstep (se 1 (by rfl) ⟨4554863, by rfl⟩ : syracuseStep 6073151 = 9109727) B9109727
theorem B48508139 : Blo 786339 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B44314087 : Blo 786339 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B3587375 : Blo 786339 3587375 := bstep (se 1 (by rfl) ⟨2690531, by rfl⟩ : syracuseStep 3587375 = 5381063) B5381063
theorem B8109359 : Blo 786339 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B15190355 : Blo 786339 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B7588799 : Blo 786339 7588799 := bstep (se 1 (by rfl) ⟨5691599, by rfl⟩ : syracuseStep 7588799 = 11383199) B11383199
theorem B2250287 : Blo 786339 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B6903863 : Blo 786339 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B4252895 : Blo 786339 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B2846177 : Blo 786339 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B3370835 : Blo 786339 3370835 := bstep (se 1 (by rfl) ⟨2528126, by rfl⟩ : syracuseStep 3370835 = 5056253) B5056253
theorem B68024447 : Blo 786339 68024447 := bstep (se 1 (by rfl) ⟨51018335, by rfl⟩ : syracuseStep 68024447 = 102036671) B102036671
theorem B5995295 : Blo 786339 5995295 := bstep (se 1 (by rfl) ⟨4496471, by rfl⟩ : syracuseStep 5995295 = 8992943) B8992943
theorem B786479 : Blo 786339 786479 := bstep (se 1 (by rfl) ⟨589859, by rfl⟩ : syracuseStep 786479 = 1179719) B1179719
theorem B1179755 : Blo 786339 1179755 := bstep (se 1 (by rfl) ⟨884816, by rfl⟩ : syracuseStep 1179755 = 1769633) B1769633
theorem B1179815 : Blo 786339 1179815 := bstep (se 1 (by rfl) ⟨884861, by rfl⟩ : syracuseStep 1179815 = 1769723) B1769723
theorem B177734573 : Blo 786339 177734573 := bstep (se 3 (by rfl) ⟨33325232, by rfl⟩ : syracuseStep 177734573 = 66650465) B66650465
theorem B10355951 : Blo 786339 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B10126903 : Blo 786339 10126903 := bstep (se 1 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 10126903 = 15190355) B15190355
theorem B1772315 : Blo 786339 1772315 := bstep (se 1 (by rfl) ⟨1329236, by rfl⟩ : syracuseStep 1772315 = 2658473) B2658473
theorem B1182815 : Blo 786339 1182815 := bstep (se 1 (by rfl) ⟨887111, by rfl⟩ : syracuseStep 1182815 = 1774223) B1774223
theorem B1183079 : Blo 786339 1183079 := bstep (se 1 (by rfl) ⟨887309, by rfl⟩ : syracuseStep 1183079 = 1774619) B1774619
theorem B59085449 : Blo 786339 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B1774439 : Blo 786339 1774439 := bstep (se 1 (by rfl) ⟨1330829, by rfl⟩ : syracuseStep 1774439 = 2661659) B2661659
theorem B1184927 : Blo 786339 1184927 := bstep (se 1 (by rfl) ⟨888695, by rfl⟩ : syracuseStep 1184927 = 1777391) B1777391
theorem B16195069 : Blo 786339 16195069 := bstep (se 3 (by rfl) ⟨3036575, by rfl⟩ : syracuseStep 16195069 = 6073151) B6073151
theorem B5059199 : Blo 786339 5059199 := bstep (se 1 (by rfl) ⟨3794399, by rfl⟩ : syracuseStep 5059199 = 7588799) B7588799
theorem B210253769 : Blo 786339 210253769 := bstep (se 2 (by rfl) ⟨78845163, by rfl⟩ : syracuseStep 210253769 = 157690327) B157690327
theorem B4602575 : Blo 786339 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B2835263 : Blo 786339 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B2247223 : Blo 786339 2247223 := bstep (se 1 (by rfl) ⟨1685417, by rfl⟩ : syracuseStep 2247223 = 3370835) B3370835
theorem B2843495 : Blo 786339 2843495 := bstep (se 1 (by rfl) ⟨2132621, by rfl⟩ : syracuseStep 2843495 = 4265243) B4265243
theorem B1500191 : Blo 786339 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B2846335 : Blo 786339 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B32338759 : Blo 786339 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B1897451 : Blo 786339 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B9566333 : Blo 786339 9566333 := bstep (se 3 (by rfl) ⟨1793687, by rfl⟩ : syracuseStep 9566333 = 3587375) B3587375
theorem B45349631 : Blo 786339 45349631 := bstep (se 1 (by rfl) ⟨34012223, by rfl⟩ : syracuseStep 45349631 = 68024447) B68024447
theorem B3996863 : Blo 786339 3996863 := bstep (se 1 (by rfl) ⟨2997647, by rfl⟩ : syracuseStep 3996863 = 5995295) B5995295
theorem B5406239 : Blo 786339 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B786503 : Blo 786339 786503 := bstep (se 1 (by rfl) ⟨589877, by rfl⟩ : syracuseStep 786503 = 1179755) B1179755
theorem B786543 : Blo 786339 786543 := bstep (se 1 (by rfl) ⟨589907, by rfl⟩ : syracuseStep 786543 = 1179815) B1179815
theorem B118489715 : Blo 786339 118489715 := bstep (se 1 (by rfl) ⟨88867286, by rfl⟩ : syracuseStep 118489715 = 177734573) B177734573
theorem B1181543 : Blo 786339 1181543 := bstep (se 1 (by rfl) ⟨886157, by rfl⟩ : syracuseStep 1181543 = 1772315) B1772315
theorem B788543 : Blo 786339 788543 := bstep (se 1 (by rfl) ⟨591407, by rfl⟩ : syracuseStep 788543 = 1182815) B1182815
theorem B13502537 : Blo 786339 13502537 := bstep (se 2 (by rfl) ⟨5063451, by rfl⟩ : syracuseStep 13502537 = 10126903) B10126903
theorem B788719 : Blo 786339 788719 := bstep (se 1 (by rfl) ⟨591539, by rfl⟩ : syracuseStep 788719 = 1183079) B1183079
theorem B39390299 : Blo 786339 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B1182959 : Blo 786339 1182959 := bstep (se 1 (by rfl) ⟨887219, by rfl⟩ : syracuseStep 1182959 = 1774439) B1774439
theorem B789951 : Blo 786339 789951 := bstep (se 1 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 789951 = 1184927) B1184927
theorem B2664575 : Blo 786339 2664575 := bstep (se 1 (by rfl) ⟨1998431, by rfl⟩ : syracuseStep 2664575 = 3996863) B3996863
theorem B2996297 : Blo 786339 2996297 := bstep (se 2 (by rfl) ⟨1123611, by rfl⟩ : syracuseStep 2996297 = 2247223) B2247223
theorem B1000127 : Blo 786339 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B1264967 : Blo 786339 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B140169179 : Blo 786339 140169179 := bstep (se 1 (by rfl) ⟨105126884, by rfl⟩ : syracuseStep 140169179 = 210253769) B210253769
theorem B6377555 : Blo 786339 6377555 := bstep (se 1 (by rfl) ⟨4783166, by rfl⟩ : syracuseStep 6377555 = 9566333) B9566333
theorem B3068383 : Blo 786339 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B30233087 : Blo 786339 30233087 := bstep (se 1 (by rfl) ⟨22674815, by rfl⟩ : syracuseStep 30233087 = 45349631) B45349631
theorem B6903967 : Blo 786339 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B7560701 : Blo 786339 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B3795113 : Blo 786339 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B1895663 : Blo 786339 1895663 := bstep (se 1 (by rfl) ⟨1421747, by rfl⟩ : syracuseStep 1895663 = 2843495) B2843495
theorem B43118345 : Blo 786339 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B3372799 : Blo 786339 3372799 := bstep (se 1 (by rfl) ⟨2529599, by rfl⟩ : syracuseStep 3372799 = 5059199) B5059199
theorem B21593425 : Blo 786339 21593425 := bstep (se 2 (by rfl) ⟨8097534, by rfl⟩ : syracuseStep 21593425 = 16195069) B16195069
theorem B3604159 : Blo 786339 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B787695 : Blo 786339 787695 := bstep (se 1 (by rfl) ⟨590771, by rfl⟩ : syracuseStep 787695 = 1181543) B1181543
theorem B788639 : Blo 786339 788639 := bstep (se 1 (by rfl) ⟨591479, by rfl⟩ : syracuseStep 788639 = 1182959) B1182959
theorem B20155391 : Blo 786339 20155391 := bstep (se 1 (by rfl) ⟨15116543, by rfl⟩ : syracuseStep 20155391 = 30233087) B30233087
theorem B1776383 : Blo 786339 1776383 := bstep (se 1 (by rfl) ⟨1332287, by rfl⟩ : syracuseStep 1776383 = 2664575) B2664575
theorem B2530075 : Blo 786339 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B4497065 : Blo 786339 4497065 := bstep (se 2 (by rfl) ⟨1686399, by rfl⟩ : syracuseStep 4497065 = 3372799) B3372799
theorem B28745563 : Blo 786339 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B2667005 : Blo 786339 2667005 := bstep (se 3 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 2667005 = 1000127) B1000127
theorem B26260199 : Blo 786339 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B1263775 : Blo 786339 1263775 := bstep (se 1 (by rfl) ⟨947831, by rfl⟩ : syracuseStep 1263775 = 1895663) B1895663
theorem B19222181 : Blo 786339 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B28791233 : Blo 786339 28791233 := bstep (se 2 (by rfl) ⟨10796712, by rfl⟩ : syracuseStep 28791233 = 21593425) B21593425
theorem B78993143 : Blo 786339 78993143 := bstep (se 1 (by rfl) ⟨59244857, by rfl⟩ : syracuseStep 78993143 = 118489715) B118489715
theorem B9001691 : Blo 786339 9001691 := bstep (se 1 (by rfl) ⟨6751268, by rfl⟩ : syracuseStep 9001691 = 13502537) B13502537
theorem B843311 : Blo 786339 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B93446119 : Blo 786339 93446119 := bstep (se 1 (by rfl) ⟨70084589, by rfl⟩ : syracuseStep 93446119 = 140169179) B140169179
theorem B4251703 : Blo 786339 4251703 := bstep (se 1 (by rfl) ⟨3188777, by rfl⟩ : syracuseStep 4251703 = 6377555) B6377555
theorem B5040467 : Blo 786339 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B4091177 : Blo 786339 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B9205289 : Blo 786339 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B1997531 : Blo 786339 1997531 := bstep (se 1 (by rfl) ⟨1498148, by rfl⟩ : syracuseStep 1997531 = 2996297) B2996297
theorem B5668937 : Blo 786339 5668937 := bstep (se 2 (by rfl) ⟨2125851, by rfl⟩ : syracuseStep 5668937 = 4251703) B4251703
theorem B13436927 : Blo 786339 13436927 := bstep (se 1 (by rfl) ⟨10077695, by rfl⟩ : syracuseStep 13436927 = 20155391) B20155391
theorem B12814787 : Blo 786339 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B52662095 : Blo 786339 52662095 := bstep (se 1 (by rfl) ⟨39496571, by rfl⟩ : syracuseStep 52662095 = 78993143) B78993143
theorem B6001127 : Blo 786339 6001127 := bstep (se 1 (by rfl) ⟨4500845, by rfl⟩ : syracuseStep 6001127 = 9001691) B9001691
theorem B1184255 : Blo 786339 1184255 := bstep (se 1 (by rfl) ⟨888191, by rfl⟩ : syracuseStep 1184255 = 1776383) B1776383
theorem B2727451 : Blo 786339 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B1778003 : Blo 786339 1778003 := bstep (se 1 (by rfl) ⟨1333502, by rfl⟩ : syracuseStep 1778003 = 2667005) B2667005
theorem B17506799 : Blo 786339 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B6136859 : Blo 786339 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B498379301 : Blo 786339 498379301 := bstep (se 4 (by rfl) ⟨46723059, by rfl⟩ : syracuseStep 498379301 = 93446119) B93446119
theorem B1685033 : Blo 786339 1685033 := bstep (se 2 (by rfl) ⟨631887, by rfl⟩ : syracuseStep 1685033 = 1263775) B1263775
theorem B2998043 : Blo 786339 2998043 := bstep (se 1 (by rfl) ⟨2248532, by rfl⟩ : syracuseStep 2998043 = 4497065) B4497065
theorem B3360311 : Blo 786339 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B2248829 : Blo 786339 2248829 := bstep (se 3 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 2248829 = 843311) B843311
theorem B1331687 : Blo 786339 1331687 := bstep (se 1 (by rfl) ⟨998765, by rfl⟩ : syracuseStep 1331687 = 1997531) B1997531
theorem B38327417 : Blo 786339 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B19194155 : Blo 786339 19194155 := bstep (se 1 (by rfl) ⟨14395616, by rfl⟩ : syracuseStep 19194155 = 28791233) B28791233
theorem B3373433 : Blo 786339 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B887791 : Blo 786339 887791 := bstep (se 1 (by rfl) ⟨665843, by rfl⟩ : syracuseStep 887791 = 1331687) B1331687
theorem B4000751 : Blo 786339 4000751 := bstep (se 1 (by rfl) ⟨3000563, by rfl⟩ : syracuseStep 4000751 = 6001127) B6001127
theorem B789503 : Blo 786339 789503 := bstep (se 1 (by rfl) ⟨592127, by rfl⟩ : syracuseStep 789503 = 1184255) B1184255
theorem B1185335 : Blo 786339 1185335 := bstep (se 1 (by rfl) ⟨889001, by rfl⟩ : syracuseStep 1185335 = 1778003) B1778003
theorem B11671199 : Blo 786339 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B1123355 : Blo 786339 1123355 := bstep (se 1 (by rfl) ⟨842516, by rfl⟩ : syracuseStep 1123355 = 1685033) B1685033
theorem B3779291 : Blo 786339 3779291 := bstep (se 1 (by rfl) ⟨2834468, by rfl⟩ : syracuseStep 3779291 = 5668937) B5668937
theorem B2240207 : Blo 786339 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B8957951 : Blo 786339 8957951 := bstep (se 1 (by rfl) ⟨6718463, by rfl⟩ : syracuseStep 8957951 = 13436927) B13436927
theorem B35108063 : Blo 786339 35108063 := bstep (se 1 (by rfl) ⟨26331047, by rfl⟩ : syracuseStep 35108063 = 52662095) B52662095
theorem B12796103 : Blo 786339 12796103 := bstep (se 1 (by rfl) ⟨9597077, by rfl⟩ : syracuseStep 12796103 = 19194155) B19194155
theorem B332252867 : Blo 786339 332252867 := bstep (se 1 (by rfl) ⟨249189650, by rfl⟩ : syracuseStep 332252867 = 498379301) B498379301
theorem B2248955 : Blo 786339 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B1499219 : Blo 786339 1499219 := bstep (se 1 (by rfl) ⟨1124414, by rfl⟩ : syracuseStep 1499219 = 2248829) B2248829
theorem B25551611 : Blo 786339 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B4091239 : Blo 786339 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B34172765 : Blo 786339 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B14546405 : Blo 786339 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B1998695 : Blo 786339 1998695 := bstep (se 1 (by rfl) ⟨1499021, by rfl⟩ : syracuseStep 1998695 = 2998043) B2998043
theorem B790223 : Blo 786339 790223 := bstep (se 1 (by rfl) ⟨592667, by rfl⟩ : syracuseStep 790223 = 1185335) B1185335
theorem B1183721 : Blo 786339 1183721 := bstep (se 2 (by rfl) ⟨443895, by rfl⟩ : syracuseStep 1183721 = 887791) B887791
theorem B22781843 : Blo 786339 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B5971967 : Blo 786339 5971967 := bstep (se 1 (by rfl) ⟨4478975, by rfl⟩ : syracuseStep 5971967 = 8957951) B8957951
theorem B23405375 : Blo 786339 23405375 := bstep (se 1 (by rfl) ⟨17554031, by rfl⟩ : syracuseStep 23405375 = 35108063) B35108063
theorem B34122941 : Blo 786339 34122941 := bstep (se 3 (by rfl) ⟨6398051, by rfl⟩ : syracuseStep 34122941 = 12796103) B12796103
theorem B2667167 : Blo 786339 2667167 := bstep (se 1 (by rfl) ⟨2000375, by rfl⟩ : syracuseStep 2667167 = 4000751) B4000751
theorem B2995613 : Blo 786339 2995613 := bstep (se 3 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 2995613 = 1123355) B1123355
theorem B7780799 : Blo 786339 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B999479 : Blo 786339 999479 := bstep (se 1 (by rfl) ⟨749609, by rfl⟩ : syracuseStep 999479 = 1499219) B1499219
theorem B1493471 : Blo 786339 1493471 := bstep (se 1 (by rfl) ⟨1120103, by rfl⟩ : syracuseStep 1493471 = 2240207) B2240207
theorem B1332463 : Blo 786339 1332463 := bstep (se 1 (by rfl) ⟨999347, by rfl⟩ : syracuseStep 1332463 = 1998695) B1998695
theorem B1499303 : Blo 786339 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B886007645 : Blo 786339 886007645 := bstep (se 3 (by rfl) ⟨166126433, by rfl⟩ : syracuseStep 886007645 = 332252867) B332252867
theorem B17034407 : Blo 786339 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B2519527 : Blo 786339 2519527 := bstep (se 1 (by rfl) ⟨1889645, by rfl⟩ : syracuseStep 2519527 = 3779291) B3779291
theorem B21819941 : Blo 786339 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B9697603 : Blo 786339 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B789147 : Blo 786339 789147 := bstep (se 1 (by rfl) ⟨591860, by rfl⟩ : syracuseStep 789147 = 1183721) B1183721
theorem B1776617 : Blo 786339 1776617 := bstep (se 2 (by rfl) ⟨666231, by rfl⟩ : syracuseStep 1776617 = 1332463) B1332463
theorem B22748627 : Blo 786339 22748627 := bstep (se 1 (by rfl) ⟨17061470, by rfl⟩ : syracuseStep 22748627 = 34122941) B34122941
theorem B1778111 : Blo 786339 1778111 := bstep (se 1 (by rfl) ⟨1333583, by rfl⟩ : syracuseStep 1778111 = 2667167) B2667167
theorem B5187199 : Blo 786339 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B2665277 : Blo 786339 2665277 := bstep (se 3 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 2665277 = 999479) B999479
theorem B995647 : Blo 786339 995647 := bstep (se 1 (by rfl) ⟨746735, by rfl⟩ : syracuseStep 995647 = 1493471) B1493471
theorem B15187895 : Blo 786339 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B3981311 : Blo 786339 3981311 := bstep (se 1 (by rfl) ⟨2985983, by rfl⟩ : syracuseStep 3981311 = 5971967) B5971967
theorem B999535 : Blo 786339 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B3359369 : Blo 786339 3359369 := bstep (se 2 (by rfl) ⟨1259763, by rfl⟩ : syracuseStep 3359369 = 2519527) B2519527
theorem B11356271 : Blo 786339 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B12930137 : Blo 786339 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B62414333 : Blo 786339 62414333 := bstep (se 3 (by rfl) ⟨11702687, by rfl⟩ : syracuseStep 62414333 = 23405375) B23405375
theorem B590671763 : Blo 786339 590671763 := bstep (se 1 (by rfl) ⟨443003822, by rfl⟩ : syracuseStep 590671763 = 886007645) B886007645
theorem B14546627 : Blo 786339 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B1997075 : Blo 786339 1997075 := bstep (se 1 (by rfl) ⟨1497806, by rfl⟩ : syracuseStep 1997075 = 2995613) B2995613
theorem B7570847 : Blo 786339 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B8620091 : Blo 786339 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B6916265 : Blo 786339 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B1184411 : Blo 786339 1184411 := bstep (se 1 (by rfl) ⟨888308, by rfl⟩ : syracuseStep 1184411 = 1776617) B1776617
theorem B1185407 : Blo 786339 1185407 := bstep (se 1 (by rfl) ⟨889055, by rfl⟩ : syracuseStep 1185407 = 1778111) B1778111
theorem B1776851 : Blo 786339 1776851 := bstep (se 1 (by rfl) ⟨1332638, by rfl⟩ : syracuseStep 1776851 = 2665277) B2665277
theorem B393781175 : Blo 786339 393781175 := bstep (se 1 (by rfl) ⟨295335881, by rfl⟩ : syracuseStep 393781175 = 590671763) B590671763
theorem B2239579 : Blo 786339 2239579 := bstep (se 1 (by rfl) ⟨1679684, by rfl⟩ : syracuseStep 2239579 = 3359369) B3359369
theorem B1327529 : Blo 786339 1327529 := bstep (se 2 (by rfl) ⟨497823, by rfl⟩ : syracuseStep 1327529 = 995647) B995647
theorem B1331383 : Blo 786339 1331383 := bstep (se 1 (by rfl) ⟨998537, by rfl⟩ : syracuseStep 1331383 = 1997075) B1997075
theorem B1332713 : Blo 786339 1332713 := bstep (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) B999535
theorem B15165751 : Blo 786339 15165751 := bstep (se 1 (by rfl) ⟨11374313, by rfl⟩ : syracuseStep 15165751 = 22748627) B22748627
theorem B41609555 : Blo 786339 41609555 := bstep (se 1 (by rfl) ⟨31207166, by rfl⟩ : syracuseStep 41609555 = 62414333) B62414333
theorem B9697751 : Blo 786339 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B10125263 : Blo 786339 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B2654207 : Blo 786339 2654207 := bstep (se 1 (by rfl) ⟨1990655, by rfl⟩ : syracuseStep 2654207 = 3981311) B3981311
theorem B885019 : Blo 786339 885019 := bstep (se 1 (by rfl) ⟨663764, by rfl⟩ : syracuseStep 885019 = 1327529) B1327529
theorem B5047231 : Blo 786339 5047231 := bstep (se 1 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 5047231 = 7570847) B7570847
theorem B20221001 : Blo 786339 20221001 := bstep (se 2 (by rfl) ⟨7582875, by rfl⟩ : syracuseStep 20221001 = 15165751) B15165751
theorem B789607 : Blo 786339 789607 := bstep (se 1 (by rfl) ⟨592205, by rfl⟩ : syracuseStep 789607 = 1184411) B1184411
theorem B888475 : Blo 786339 888475 := bstep (se 1 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 888475 = 1332713) B1332713
theorem B790271 : Blo 786339 790271 := bstep (se 1 (by rfl) ⟨592703, by rfl⟩ : syracuseStep 790271 = 1185407) B1185407
theorem B2986105 : Blo 786339 2986105 := bstep (se 2 (by rfl) ⟨1119789, by rfl⟩ : syracuseStep 2986105 = 2239579) B2239579
theorem B1184567 : Blo 786339 1184567 := bstep (se 1 (by rfl) ⟨888425, by rfl⟩ : syracuseStep 1184567 = 1776851) B1776851
theorem B1775177 : Blo 786339 1775177 := bstep (se 2 (by rfl) ⟨665691, by rfl⟩ : syracuseStep 1775177 = 1331383) B1331383
theorem B6465167 : Blo 786339 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B5746727 : Blo 786339 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B262520783 : Blo 786339 262520783 := bstep (se 1 (by rfl) ⟨196890587, by rfl⟩ : syracuseStep 262520783 = 393781175) B393781175
theorem B27739703 : Blo 786339 27739703 := bstep (se 1 (by rfl) ⟨20804777, by rfl⟩ : syracuseStep 27739703 = 41609555) B41609555
theorem B1769471 : Blo 786339 1769471 := bstep (se 1 (by rfl) ⟨1327103, by rfl⟩ : syracuseStep 1769471 = 2654207) B2654207
theorem B4610843 : Blo 786339 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B6750175 : Blo 786339 6750175 := bstep (se 1 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 6750175 = 10125263) B10125263
theorem B1180025 : Blo 786339 1180025 := bstep (se 2 (by rfl) ⟨442509, by rfl⟩ : syracuseStep 1180025 = 885019) B885019
theorem B789711 : Blo 786339 789711 := bstep (se 1 (by rfl) ⟨592283, by rfl⟩ : syracuseStep 789711 = 1184567) B1184567
theorem B1183451 : Blo 786339 1183451 := bstep (se 1 (by rfl) ⟨887588, by rfl⟩ : syracuseStep 1183451 = 1775177) B1775177
theorem B1179647 : Blo 786339 1179647 := bstep (se 1 (by rfl) ⟨884735, by rfl⟩ : syracuseStep 1179647 = 1769471) B1769471
theorem B1184633 : Blo 786339 1184633 := bstep (se 2 (by rfl) ⟨444237, by rfl⟩ : syracuseStep 1184633 = 888475) B888475
theorem B6729641 : Blo 786339 6729641 := bstep (se 2 (by rfl) ⟨2523615, by rfl⟩ : syracuseStep 6729641 = 5047231) B5047231
theorem B13480667 : Blo 786339 13480667 := bstep (se 1 (by rfl) ⟨10110500, by rfl⟩ : syracuseStep 13480667 = 20221001) B20221001
theorem B73972541 : Blo 786339 73972541 := bstep (se 3 (by rfl) ⟨13869851, by rfl⟩ : syracuseStep 73972541 = 27739703) B27739703
theorem B3981473 : Blo 786339 3981473 := bstep (se 2 (by rfl) ⟨1493052, by rfl⟩ : syracuseStep 3981473 = 2986105) B2986105
theorem B4310111 : Blo 786339 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B9000233 : Blo 786339 9000233 := bstep (se 2 (by rfl) ⟨3375087, by rfl⟩ : syracuseStep 9000233 = 6750175) B6750175
theorem B3073895 : Blo 786339 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B3831151 : Blo 786339 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B175013855 : Blo 786339 175013855 := bstep (se 1 (by rfl) ⟨131260391, by rfl⟩ : syracuseStep 175013855 = 262520783) B262520783
theorem B2654315 : Blo 786339 2654315 := bstep (se 1 (by rfl) ⟨1990736, by rfl⟩ : syracuseStep 2654315 = 3981473) B3981473
theorem B786683 : Blo 786339 786683 := bstep (se 1 (by rfl) ⟨590012, by rfl⟩ : syracuseStep 786683 = 1180025) B1180025
theorem B788967 : Blo 786339 788967 := bstep (se 1 (by rfl) ⟨591725, by rfl⟩ : syracuseStep 788967 = 1183451) B1183451
theorem B789755 : Blo 786339 789755 := bstep (se 1 (by rfl) ⟨592316, by rfl⟩ : syracuseStep 789755 = 1184633) B1184633
theorem B6000155 : Blo 786339 6000155 := bstep (se 1 (by rfl) ⟨4500116, by rfl⟩ : syracuseStep 6000155 = 9000233) B9000233
theorem B8987111 : Blo 786339 8987111 := bstep (se 1 (by rfl) ⟨6740333, by rfl⟩ : syracuseStep 8987111 = 13480667) B13480667
theorem B2049263 : Blo 786339 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B116675903 : Blo 786339 116675903 := bstep (se 1 (by rfl) ⟨87506927, by rfl⟩ : syracuseStep 116675903 = 175013855) B175013855
theorem B2873407 : Blo 786339 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B786431 : Blo 786339 786431 := bstep (se 1 (by rfl) ⟨589823, by rfl⟩ : syracuseStep 786431 = 1179647) B1179647
theorem B5108201 : Blo 786339 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B197260109 : Blo 786339 197260109 := bstep (se 3 (by rfl) ⟨36986270, by rfl⟩ : syracuseStep 197260109 = 73972541) B73972541
theorem B4486427 : Blo 786339 4486427 := bstep (se 1 (by rfl) ⟨3364820, by rfl⟩ : syracuseStep 4486427 = 6729641) B6729641
theorem B1769543 : Blo 786339 1769543 := bstep (se 1 (by rfl) ⟨1327157, by rfl⟩ : syracuseStep 1769543 = 2654315) B2654315
theorem B4000103 : Blo 786339 4000103 := bstep (se 1 (by rfl) ⟨3000077, by rfl⟩ : syracuseStep 4000103 = 6000155) B6000155
theorem B131506739 : Blo 786339 131506739 := bstep (se 1 (by rfl) ⟨98630054, by rfl⟩ : syracuseStep 131506739 = 197260109) B197260109
theorem B2990951 : Blo 786339 2990951 := bstep (se 1 (by rfl) ⟨2243213, by rfl⟩ : syracuseStep 2990951 = 4486427) B4486427
theorem B1366175 : Blo 786339 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B77783935 : Blo 786339 77783935 := bstep (se 1 (by rfl) ⟨58337951, by rfl⟩ : syracuseStep 77783935 = 116675903) B116675903
theorem B5991407 : Blo 786339 5991407 := bstep (se 1 (by rfl) ⟨4493555, by rfl⟩ : syracuseStep 5991407 = 8987111) B8987111
theorem B3831209 : Blo 786339 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B3405467 : Blo 786339 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B1179695 : Blo 786339 1179695 := bstep (se 1 (by rfl) ⟨884771, by rfl⟩ : syracuseStep 1179695 = 1769543) B1769543
theorem B103711913 : Blo 786339 103711913 := bstep (se 2 (by rfl) ⟨38891967, by rfl⟩ : syracuseStep 103711913 = 77783935) B77783935
theorem B2270311 : Blo 786339 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B2666735 : Blo 786339 2666735 := bstep (se 1 (by rfl) ⟨2000051, by rfl⟩ : syracuseStep 2666735 = 4000103) B4000103
theorem B87671159 : Blo 786339 87671159 := bstep (se 1 (by rfl) ⟨65753369, by rfl⟩ : syracuseStep 87671159 = 131506739) B131506739
theorem B910783 : Blo 786339 910783 := bstep (se 1 (by rfl) ⟨683087, by rfl⟩ : syracuseStep 910783 = 1366175) B1366175
theorem B1993967 : Blo 786339 1993967 := bstep (se 1 (by rfl) ⟨1495475, by rfl⟩ : syracuseStep 1993967 = 2990951) B2990951
theorem B3994271 : Blo 786339 3994271 := bstep (se 1 (by rfl) ⟨2995703, by rfl⟩ : syracuseStep 3994271 = 5991407) B5991407
theorem B2554139 : Blo 786339 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B786463 : Blo 786339 786463 := bstep (se 1 (by rfl) ⟨589847, by rfl⟩ : syracuseStep 786463 = 1179695) B1179695
theorem B69141275 : Blo 786339 69141275 := bstep (se 1 (by rfl) ⟨51855956, by rfl⟩ : syracuseStep 69141275 = 103711913) B103711913
theorem B4857509 : Blo 786339 4857509 := bstep (se 4 (by rfl) ⟨455391, by rfl⟩ : syracuseStep 4857509 = 910783) B910783
theorem B1777823 : Blo 786339 1777823 := bstep (se 1 (by rfl) ⟨1333367, by rfl⟩ : syracuseStep 1777823 = 2666735) B2666735
theorem B2662847 : Blo 786339 2662847 := bstep (se 1 (by rfl) ⟨1997135, by rfl⟩ : syracuseStep 2662847 = 3994271) B3994271
theorem B12108325 : Blo 786339 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B1329311 : Blo 786339 1329311 := bstep (se 1 (by rfl) ⟨996983, by rfl⟩ : syracuseStep 1329311 = 1993967) B1993967
theorem B58447439 : Blo 786339 58447439 := bstep (se 1 (by rfl) ⟨43835579, by rfl⟩ : syracuseStep 58447439 = 87671159) B87671159
theorem B6811037 : Blo 786339 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B886207 : Blo 786339 886207 := bstep (se 1 (by rfl) ⟨664655, by rfl⟩ : syracuseStep 886207 = 1329311) B1329311
theorem B38964959 : Blo 786339 38964959 := bstep (se 1 (by rfl) ⟨29223719, by rfl⟩ : syracuseStep 38964959 = 58447439) B58447439
theorem B1185215 : Blo 786339 1185215 := bstep (se 1 (by rfl) ⟨888911, by rfl⟩ : syracuseStep 1185215 = 1777823) B1777823
theorem B1775231 : Blo 786339 1775231 := bstep (se 1 (by rfl) ⟨1331423, by rfl⟩ : syracuseStep 1775231 = 2662847) B2662847
theorem B4540691 : Blo 786339 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B46094183 : Blo 786339 46094183 := bstep (se 1 (by rfl) ⟨34570637, by rfl⟩ : syracuseStep 46094183 = 69141275) B69141275
theorem B16144433 : Blo 786339 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B3238339 : Blo 786339 3238339 := bstep (se 1 (by rfl) ⟨2428754, by rfl⟩ : syracuseStep 3238339 = 4857509) B4857509
theorem B1181609 : Blo 786339 1181609 := bstep (se 2 (by rfl) ⟨443103, by rfl⟩ : syracuseStep 1181609 = 886207) B886207
theorem B790143 : Blo 786339 790143 := bstep (se 1 (by rfl) ⟨592607, by rfl⟩ : syracuseStep 790143 = 1185215) B1185215
theorem B1183487 : Blo 786339 1183487 := bstep (se 1 (by rfl) ⟨887615, by rfl⟩ : syracuseStep 1183487 = 1775231) B1775231
theorem B3027127 : Blo 786339 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B10762955 : Blo 786339 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B25976639 : Blo 786339 25976639 := bstep (se 1 (by rfl) ⟨19482479, by rfl⟩ : syracuseStep 25976639 = 38964959) B38964959
theorem B4317785 : Blo 786339 4317785 := bstep (se 2 (by rfl) ⟨1619169, by rfl⟩ : syracuseStep 4317785 = 3238339) B3238339
theorem B30729455 : Blo 786339 30729455 := bstep (se 1 (by rfl) ⟨23047091, by rfl⟩ : syracuseStep 30729455 = 46094183) B46094183
theorem B787739 : Blo 786339 787739 := bstep (se 1 (by rfl) ⟨590804, by rfl⟩ : syracuseStep 787739 = 1181609) B1181609
theorem B788991 : Blo 786339 788991 := bstep (se 1 (by rfl) ⟨591743, by rfl⟩ : syracuseStep 788991 = 1183487) B1183487
theorem B4036169 : Blo 786339 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B20486303 : Blo 786339 20486303 := bstep (se 1 (by rfl) ⟨15364727, by rfl⟩ : syracuseStep 20486303 = 30729455) B30729455
theorem B2878523 : Blo 786339 2878523 := bstep (se 1 (by rfl) ⟨2158892, by rfl⟩ : syracuseStep 2878523 = 4317785) B4317785
theorem B7175303 : Blo 786339 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B69271037 : Blo 786339 69271037 := bstep (se 3 (by rfl) ⟨12988319, by rfl⟩ : syracuseStep 69271037 = 25976639) B25976639
theorem B46180691 : Blo 786339 46180691 := bstep (se 1 (by rfl) ⟨34635518, by rfl⟩ : syracuseStep 46180691 = 69271037) B69271037
theorem B10763117 : Blo 786339 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B1919015 : Blo 786339 1919015 := bstep (se 1 (by rfl) ⟨1439261, by rfl⟩ : syracuseStep 1919015 = 2878523) B2878523
theorem B13657535 : Blo 786339 13657535 := bstep (se 1 (by rfl) ⟨10243151, by rfl⟩ : syracuseStep 13657535 = 20486303) B20486303
theorem B4783535 : Blo 786339 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B1279343 : Blo 786339 1279343 := bstep (se 1 (by rfl) ⟨959507, by rfl⟩ : syracuseStep 1279343 = 1919015) B1919015
theorem B3189023 : Blo 786339 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B30787127 : Blo 786339 30787127 := bstep (se 1 (by rfl) ⟨23090345, by rfl⟩ : syracuseStep 30787127 = 46180691) B46180691
theorem B9105023 : Blo 786339 9105023 := bstep (se 1 (by rfl) ⟨6828767, by rfl⟩ : syracuseStep 9105023 = 13657535) B13657535
theorem B7175411 : Blo 786339 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B852895 : Blo 786339 852895 := bstep (se 1 (by rfl) ⟨639671, by rfl⟩ : syracuseStep 852895 = 1279343) B1279343
theorem B6070015 : Blo 786339 6070015 := bstep (se 1 (by rfl) ⟨4552511, by rfl⟩ : syracuseStep 6070015 = 9105023) B9105023
theorem B20524751 : Blo 786339 20524751 := bstep (se 1 (by rfl) ⟨15393563, by rfl⟩ : syracuseStep 20524751 = 30787127) B30787127
theorem B2126015 : Blo 786339 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B4783607 : Blo 786339 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B1417343 : Blo 786339 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B3189071 : Blo 786339 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B13683167 : Blo 786339 13683167 := bstep (se 1 (by rfl) ⟨10262375, by rfl⟩ : syracuseStep 13683167 = 20524751) B20524751
theorem B4548773 : Blo 786339 4548773 := bstep (se 4 (by rfl) ⟨426447, by rfl⟩ : syracuseStep 4548773 = 852895) B852895
theorem B8093353 : Blo 786339 8093353 := bstep (se 2 (by rfl) ⟨3035007, by rfl⟩ : syracuseStep 8093353 = 6070015) B6070015
theorem B10791137 : Blo 786339 10791137 := bstep (se 2 (by rfl) ⟨4046676, by rfl⟩ : syracuseStep 10791137 = 8093353) B8093353
theorem B3779581 : Blo 786339 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B9122111 : Blo 786339 9122111 := bstep (se 1 (by rfl) ⟨6841583, by rfl⟩ : syracuseStep 9122111 = 13683167) B13683167
theorem B3032515 : Blo 786339 3032515 := bstep (se 1 (by rfl) ⟨2274386, by rfl⟩ : syracuseStep 3032515 = 4548773) B4548773
theorem B2126047 : Blo 786339 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B4043353 : Blo 786339 4043353 := bstep (se 2 (by rfl) ⟨1516257, by rfl⟩ : syracuseStep 4043353 = 3032515) B3032515
theorem B2834729 : Blo 786339 2834729 := bstep (se 2 (by rfl) ⟨1063023, by rfl⟩ : syracuseStep 2834729 = 2126047) B2126047
theorem B7194091 : Blo 786339 7194091 := bstep (se 1 (by rfl) ⟨5395568, by rfl⟩ : syracuseStep 7194091 = 10791137) B10791137
theorem B6081407 : Blo 786339 6081407 := bstep (se 1 (by rfl) ⟨4561055, by rfl⟩ : syracuseStep 6081407 = 9122111) B9122111
theorem B5039441 : Blo 786339 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B5391137 : Blo 786339 5391137 := bstep (se 2 (by rfl) ⟨2021676, by rfl⟩ : syracuseStep 5391137 = 4043353) B4043353
theorem B3359627 : Blo 786339 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B1889819 : Blo 786339 1889819 := bstep (se 1 (by rfl) ⟨1417364, by rfl⟩ : syracuseStep 1889819 = 2834729) B2834729
theorem B4054271 : Blo 786339 4054271 := bstep (se 1 (by rfl) ⟨3040703, by rfl⟩ : syracuseStep 4054271 = 6081407) B6081407
theorem B9592121 : Blo 786339 9592121 := bstep (se 2 (by rfl) ⟨3597045, by rfl⟩ : syracuseStep 9592121 = 7194091) B7194091
theorem B6394747 : Blo 786339 6394747 := bstep (se 1 (by rfl) ⟨4796060, by rfl⟩ : syracuseStep 6394747 = 9592121) B9592121
theorem B2239751 : Blo 786339 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1259879 : Blo 786339 1259879 := bstep (se 1 (by rfl) ⟨944909, by rfl⟩ : syracuseStep 1259879 = 1889819) B1889819
theorem B3594091 : Blo 786339 3594091 := bstep (se 1 (by rfl) ⟨2695568, by rfl⟩ : syracuseStep 3594091 = 5391137) B5391137
theorem B10811389 : Blo 786339 10811389 := bstep (se 3 (by rfl) ⟨2027135, by rfl⟩ : syracuseStep 10811389 = 4054271) B4054271
theorem B8526329 : Blo 786339 8526329 := bstep (se 2 (by rfl) ⟨3197373, by rfl⟩ : syracuseStep 8526329 = 6394747) B6394747
theorem B4792121 : Blo 786339 4792121 := bstep (se 2 (by rfl) ⟨1797045, by rfl⟩ : syracuseStep 4792121 = 3594091) B3594091
theorem B3359677 : Blo 786339 3359677 := bstep (se 3 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 3359677 = 1259879) B1259879
theorem B1493167 : Blo 786339 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B14415185 : Blo 786339 14415185 := bstep (se 2 (by rfl) ⟨5405694, by rfl⟩ : syracuseStep 14415185 = 10811389) B10811389
theorem B9610123 : Blo 786339 9610123 := bstep (se 1 (by rfl) ⟨7207592, by rfl⟩ : syracuseStep 9610123 = 14415185) B14415185
theorem B5684219 : Blo 786339 5684219 := bstep (se 1 (by rfl) ⟨4263164, by rfl⟩ : syracuseStep 5684219 = 8526329) B8526329
theorem B3194747 : Blo 786339 3194747 := bstep (se 1 (by rfl) ⟨2396060, by rfl⟩ : syracuseStep 3194747 = 4792121) B4792121
theorem B4479569 : Blo 786339 4479569 := bstep (se 2 (by rfl) ⟨1679838, by rfl⟩ : syracuseStep 4479569 = 3359677) B3359677
theorem B1990889 : Blo 786339 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B12813497 : Blo 786339 12813497 := bstep (se 2 (by rfl) ⟨4805061, by rfl⟩ : syracuseStep 12813497 = 9610123) B9610123
theorem B2986379 : Blo 786339 2986379 := bstep (se 1 (by rfl) ⟨2239784, by rfl⟩ : syracuseStep 2986379 = 4479569) B4479569
theorem B1327259 : Blo 786339 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889
theorem B3789479 : Blo 786339 3789479 := bstep (se 1 (by rfl) ⟨2842109, by rfl⟩ : syracuseStep 3789479 = 5684219) B5684219
theorem B2129831 : Blo 786339 2129831 := bstep (se 1 (by rfl) ⟨1597373, by rfl⟩ : syracuseStep 2129831 = 3194747) B3194747
theorem B884839 : Blo 786339 884839 := bstep (se 1 (by rfl) ⟨663629, by rfl⟩ : syracuseStep 884839 = 1327259) B1327259
theorem B2526319 : Blo 786339 2526319 := bstep (se 1 (by rfl) ⟨1894739, by rfl⟩ : syracuseStep 2526319 = 3789479) B3789479
theorem B1419887 : Blo 786339 1419887 := bstep (se 1 (by rfl) ⟨1064915, by rfl⟩ : syracuseStep 1419887 = 2129831) B2129831
theorem B8542331 : Blo 786339 8542331 := bstep (se 1 (by rfl) ⟨6406748, by rfl⟩ : syracuseStep 8542331 = 12813497) B12813497
theorem B1990919 : Blo 786339 1990919 := bstep (se 1 (by rfl) ⟨1493189, by rfl⟩ : syracuseStep 1990919 = 2986379) B2986379
theorem B1179785 : Blo 786339 1179785 := bstep (se 2 (by rfl) ⟨442419, by rfl⟩ : syracuseStep 1179785 = 884839) B884839
theorem B1327279 : Blo 786339 1327279 := bstep (se 1 (by rfl) ⟨995459, by rfl⟩ : syracuseStep 1327279 = 1990919) B1990919
theorem B3786365 : Blo 786339 3786365 := bstep (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) B1419887
theorem B5694887 : Blo 786339 5694887 := bstep (se 1 (by rfl) ⟨4271165, by rfl⟩ : syracuseStep 5694887 = 8542331) B8542331
theorem B3368425 : Blo 786339 3368425 := bstep (se 2 (by rfl) ⟨1263159, by rfl⟩ : syracuseStep 3368425 = 2526319) B2526319
theorem B786523 : Blo 786339 786523 := bstep (se 1 (by rfl) ⟨589892, by rfl⟩ : syracuseStep 786523 = 1179785) B1179785
theorem B1769705 : Blo 786339 1769705 := bstep (se 2 (by rfl) ⟨663639, by rfl⟩ : syracuseStep 1769705 = 1327279) B1327279
theorem B2524243 : Blo 786339 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B4491233 : Blo 786339 4491233 := bstep (se 2 (by rfl) ⟨1684212, by rfl⟩ : syracuseStep 4491233 = 3368425) B3368425
theorem B3796591 : Blo 786339 3796591 := bstep (se 1 (by rfl) ⟨2847443, by rfl⟩ : syracuseStep 3796591 = 5694887) B5694887
theorem B1179803 : Blo 786339 1179803 := bstep (se 1 (by rfl) ⟨884852, by rfl⟩ : syracuseStep 1179803 = 1769705) B1769705
theorem B2994155 : Blo 786339 2994155 := bstep (se 1 (by rfl) ⟨2245616, by rfl⟩ : syracuseStep 2994155 = 4491233) B4491233
theorem B5062121 : Blo 786339 5062121 := bstep (se 2 (by rfl) ⟨1898295, by rfl⟩ : syracuseStep 5062121 = 3796591) B3796591
theorem B3365657 : Blo 786339 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B786535 : Blo 786339 786535 := bstep (se 1 (by rfl) ⟨589901, by rfl⟩ : syracuseStep 786535 = 1179803) B1179803
theorem B2243771 : Blo 786339 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B1996103 : Blo 786339 1996103 := bstep (se 1 (by rfl) ⟨1497077, by rfl⟩ : syracuseStep 1996103 = 2994155) B2994155
theorem B3374747 : Blo 786339 3374747 := bstep (se 1 (by rfl) ⟨2531060, by rfl⟩ : syracuseStep 3374747 = 5062121) B5062121
theorem B1330735 : Blo 786339 1330735 := bstep (se 1 (by rfl) ⟨998051, by rfl⟩ : syracuseStep 1330735 = 1996103) B1996103
theorem B1495847 : Blo 786339 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B2249831 : Blo 786339 2249831 := bstep (se 1 (by rfl) ⟨1687373, by rfl⟩ : syracuseStep 2249831 = 3374747) B3374747
theorem B1774313 : Blo 786339 1774313 := bstep (se 2 (by rfl) ⟨665367, by rfl⟩ : syracuseStep 1774313 = 1330735) B1330735
theorem B3988925 : Blo 786339 3988925 := bstep (se 3 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 3988925 = 1495847) B1495847
theorem B1499887 : Blo 786339 1499887 := bstep (se 1 (by rfl) ⟨1124915, by rfl⟩ : syracuseStep 1499887 = 2249831) B2249831
theorem B1999849 : Blo 786339 1999849 := bstep (se 2 (by rfl) ⟨749943, by rfl⟩ : syracuseStep 1999849 = 1499887) B1499887
theorem B1182875 : Blo 786339 1182875 := bstep (se 1 (by rfl) ⟨887156, by rfl⟩ : syracuseStep 1182875 = 1774313) B1774313
theorem B2659283 : Blo 786339 2659283 := bstep (se 1 (by rfl) ⟨1994462, by rfl⟩ : syracuseStep 2659283 = 3988925) B3988925
theorem B788583 : Blo 786339 788583 := bstep (se 1 (by rfl) ⟨591437, by rfl⟩ : syracuseStep 788583 = 1182875) B1182875
theorem B1772855 : Blo 786339 1772855 := bstep (se 1 (by rfl) ⟨1329641, by rfl⟩ : syracuseStep 1772855 = 2659283) B2659283
theorem B2666465 : Blo 786339 2666465 := bstep (se 2 (by rfl) ⟨999924, by rfl⟩ : syracuseStep 2666465 = 1999849) B1999849
theorem B1181903 : Blo 786339 1181903 := bstep (se 1 (by rfl) ⟨886427, by rfl⟩ : syracuseStep 1181903 = 1772855) B1772855
theorem B1777643 : Blo 786339 1777643 := bstep (se 1 (by rfl) ⟨1333232, by rfl⟩ : syracuseStep 1777643 = 2666465) B2666465
theorem B787935 : Blo 786339 787935 := bstep (se 1 (by rfl) ⟨590951, by rfl⟩ : syracuseStep 787935 = 1181903) B1181903
theorem B1185095 : Blo 786339 1185095 := bstep (se 1 (by rfl) ⟨888821, by rfl⟩ : syracuseStep 1185095 = 1777643) B1777643
theorem B790063 : Blo 786339 790063 := bstep (se 1 (by rfl) ⟨592547, by rfl⟩ : syracuseStep 790063 = 1185095) B1185095

theorem C0 (j : ℕ) (h1 : 196584 ≤ j) (h2 : j ≤ 197283) : Blo 786339 (4 * j + 3) := by
  interval_cases j
  · exact B786339
  · exact B786343
  · exact B786347
  · exact B786351
  · exact B786355
  · exact B786359
  · exact B786363
  · exact B786367
  · exact B786371
  · exact B786375
  · exact B786379
  · exact B786383
  · exact B786387
  · exact B786391
  · exact B786395
  · exact B786399
  · exact B786403
  · exact B786407
  · exact B786411
  · exact B786415
  · exact B786419
  · exact B786423
  · exact B786427
  · exact B786431
  · exact B786435
  · exact B786439
  · exact B786443
  · exact B786447
  · exact B786451
  · exact B786455
  · exact B786459
  · exact B786463
  · exact B786467
  · exact B786471
  · exact B786475
  · exact B786479
  · exact B786483
  · exact B786487
  · exact B786491
  · exact B786495
  · exact B786499
  · exact B786503
  · exact B786507
  · exact B786511
  · exact B786515
  · exact B786519
  · exact B786523
  · exact B786527
  · exact B786531
  · exact B786535
  · exact B786539
  · exact B786543
  · exact B786547
  · exact B786551
  · exact B786555
  · exact B786559
  · exact B786563
  · exact B786567
  · exact B786571
  · exact B786575
  · exact B786579
  · exact B786583
  · exact B786587
  · exact B786591
  · exact B786595
  · exact B786599
  · exact B786603
  · exact B786607
  · exact B786611
  · exact B786615
  · exact B786619
  · exact B786623
  · exact B786627
  · exact B786631
  · exact B786635
  · exact B786639
  · exact B786643
  · exact B786647
  · exact B786651
  · exact B786655
  · exact B786659
  · exact B786663
  · exact B786667
  · exact B786671
  · exact B786675
  · exact B786679
  · exact B786683
  · exact B786687
  · exact B786691
  · exact B786695
  · exact B786699
  · exact B786703
  · exact B786707
  · exact B786711
  · exact B786715
  · exact B786719
  · exact B786723
  · exact B786727
  · exact B786731
  · exact B786735
  · exact B786739
  · exact B786743
  · exact B786747
  · exact B786751
  · exact B786755
  · exact B786759
  · exact B786763
  · exact B786767
  · exact B786771
  · exact B786775
  · exact B786779
  · exact B786783
  · exact B786787
  · exact B786791
  · exact B786795
  · exact B786799
  · exact B786803
  · exact B786807
  · exact B786811
  · exact B786815
  · exact B786819
  · exact B786823
  · exact B786827
  · exact B786831
  · exact B786835
  · exact B786839
  · exact B786843
  · exact B786847
  · exact B786851
  · exact B786855
  · exact B786859
  · exact B786863
  · exact B786867
  · exact B786871
  · exact B786875
  · exact B786879
  · exact B786883
  · exact B786887
  · exact B786891
  · exact B786895
  · exact B786899
  · exact B786903
  · exact B786907
  · exact B786911
  · exact B786915
  · exact B786919
  · exact B786923
  · exact B786927
  · exact B786931
  · exact B786935
  · exact B786939
  · exact B786943
  · exact B786947
  · exact B786951
  · exact B786955
  · exact B786959
  · exact B786963
  · exact B786967
  · exact B786971
  · exact B786975
  · exact B786979
  · exact B786983
  · exact B786987
  · exact B786991
  · exact B786995
  · exact B786999
  · exact B787003
  · exact B787007
  · exact B787011
  · exact B787015
  · exact B787019
  · exact B787023
  · exact B787027
  · exact B787031
  · exact B787035
  · exact B787039
  · exact B787043
  · exact B787047
  · exact B787051
  · exact B787055
  · exact B787059
  · exact B787063
  · exact B787067
  · exact B787071
  · exact B787075
  · exact B787079
  · exact B787083
  · exact B787087
  · exact B787091
  · exact B787095
  · exact B787099
  · exact B787103
  · exact B787107
  · exact B787111
  · exact B787115
  · exact B787119
  · exact B787123
  · exact B787127
  · exact B787131
  · exact B787135
  · exact B787139
  · exact B787143
  · exact B787147
  · exact B787151
  · exact B787155
  · exact B787159
  · exact B787163
  · exact B787167
  · exact B787171
  · exact B787175
  · exact B787179
  · exact B787183
  · exact B787187
  · exact B787191
  · exact B787195
  · exact B787199
  · exact B787203
  · exact B787207
  · exact B787211
  · exact B787215
  · exact B787219
  · exact B787223
  · exact B787227
  · exact B787231
  · exact B787235
  · exact B787239
  · exact B787243
  · exact B787247
  · exact B787251
  · exact B787255
  · exact B787259
  · exact B787263
  · exact B787267
  · exact B787271
  · exact B787275
  · exact B787279
  · exact B787283
  · exact B787287
  · exact B787291
  · exact B787295
  · exact B787299
  · exact B787303
  · exact B787307
  · exact B787311
  · exact B787315
  · exact B787319
  · exact B787323
  · exact B787327
  · exact B787331
  · exact B787335
  · exact B787339
  · exact B787343
  · exact B787347
  · exact B787351
  · exact B787355
  · exact B787359
  · exact B787363
  · exact B787367
  · exact B787371
  · exact B787375
  · exact B787379
  · exact B787383
  · exact B787387
  · exact B787391
  · exact B787395
  · exact B787399
  · exact B787403
  · exact B787407
  · exact B787411
  · exact B787415
  · exact B787419
  · exact B787423
  · exact B787427
  · exact B787431
  · exact B787435
  · exact B787439
  · exact B787443
  · exact B787447
  · exact B787451
  · exact B787455
  · exact B787459
  · exact B787463
  · exact B787467
  · exact B787471
  · exact B787475
  · exact B787479
  · exact B787483
  · exact B787487
  · exact B787491
  · exact B787495
  · exact B787499
  · exact B787503
  · exact B787507
  · exact B787511
  · exact B787515
  · exact B787519
  · exact B787523
  · exact B787527
  · exact B787531
  · exact B787535
  · exact B787539
  · exact B787543
  · exact B787547
  · exact B787551
  · exact B787555
  · exact B787559
  · exact B787563
  · exact B787567
  · exact B787571
  · exact B787575
  · exact B787579
  · exact B787583
  · exact B787587
  · exact B787591
  · exact B787595
  · exact B787599
  · exact B787603
  · exact B787607
  · exact B787611
  · exact B787615
  · exact B787619
  · exact B787623
  · exact B787627
  · exact B787631
  · exact B787635
  · exact B787639
  · exact B787643
  · exact B787647
  · exact B787651
  · exact B787655
  · exact B787659
  · exact B787663
  · exact B787667
  · exact B787671
  · exact B787675
  · exact B787679
  · exact B787683
  · exact B787687
  · exact B787691
  · exact B787695
  · exact B787699
  · exact B787703
  · exact B787707
  · exact B787711
  · exact B787715
  · exact B787719
  · exact B787723
  · exact B787727
  · exact B787731
  · exact B787735
  · exact B787739
  · exact B787743
  · exact B787747
  · exact B787751
  · exact B787755
  · exact B787759
  · exact B787763
  · exact B787767
  · exact B787771
  · exact B787775
  · exact B787779
  · exact B787783
  · exact B787787
  · exact B787791
  · exact B787795
  · exact B787799
  · exact B787803
  · exact B787807
  · exact B787811
  · exact B787815
  · exact B787819
  · exact B787823
  · exact B787827
  · exact B787831
  · exact B787835
  · exact B787839
  · exact B787843
  · exact B787847
  · exact B787851
  · exact B787855
  · exact B787859
  · exact B787863
  · exact B787867
  · exact B787871
  · exact B787875
  · exact B787879
  · exact B787883
  · exact B787887
  · exact B787891
  · exact B787895
  · exact B787899
  · exact B787903
  · exact B787907
  · exact B787911
  · exact B787915
  · exact B787919
  · exact B787923
  · exact B787927
  · exact B787931
  · exact B787935
  · exact B787939
  · exact B787943
  · exact B787947
  · exact B787951
  · exact B787955
  · exact B787959
  · exact B787963
  · exact B787967
  · exact B787971
  · exact B787975
  · exact B787979
  · exact B787983
  · exact B787987
  · exact B787991
  · exact B787995
  · exact B787999
  · exact B788003
  · exact B788007
  · exact B788011
  · exact B788015
  · exact B788019
  · exact B788023
  · exact B788027
  · exact B788031
  · exact B788035
  · exact B788039
  · exact B788043
  · exact B788047
  · exact B788051
  · exact B788055
  · exact B788059
  · exact B788063
  · exact B788067
  · exact B788071
  · exact B788075
  · exact B788079
  · exact B788083
  · exact B788087
  · exact B788091
  · exact B788095
  · exact B788099
  · exact B788103
  · exact B788107
  · exact B788111
  · exact B788115
  · exact B788119
  · exact B788123
  · exact B788127
  · exact B788131
  · exact B788135
  · exact B788139
  · exact B788143
  · exact B788147
  · exact B788151
  · exact B788155
  · exact B788159
  · exact B788163
  · exact B788167
  · exact B788171
  · exact B788175
  · exact B788179
  · exact B788183
  · exact B788187
  · exact B788191
  · exact B788195
  · exact B788199
  · exact B788203
  · exact B788207
  · exact B788211
  · exact B788215
  · exact B788219
  · exact B788223
  · exact B788227
  · exact B788231
  · exact B788235
  · exact B788239
  · exact B788243
  · exact B788247
  · exact B788251
  · exact B788255
  · exact B788259
  · exact B788263
  · exact B788267
  · exact B788271
  · exact B788275
  · exact B788279
  · exact B788283
  · exact B788287
  · exact B788291
  · exact B788295
  · exact B788299
  · exact B788303
  · exact B788307
  · exact B788311
  · exact B788315
  · exact B788319
  · exact B788323
  · exact B788327
  · exact B788331
  · exact B788335
  · exact B788339
  · exact B788343
  · exact B788347
  · exact B788351
  · exact B788355
  · exact B788359
  · exact B788363
  · exact B788367
  · exact B788371
  · exact B788375
  · exact B788379
  · exact B788383
  · exact B788387
  · exact B788391
  · exact B788395
  · exact B788399
  · exact B788403
  · exact B788407
  · exact B788411
  · exact B788415
  · exact B788419
  · exact B788423
  · exact B788427
  · exact B788431
  · exact B788435
  · exact B788439
  · exact B788443
  · exact B788447
  · exact B788451
  · exact B788455
  · exact B788459
  · exact B788463
  · exact B788467
  · exact B788471
  · exact B788475
  · exact B788479
  · exact B788483
  · exact B788487
  · exact B788491
  · exact B788495
  · exact B788499
  · exact B788503
  · exact B788507
  · exact B788511
  · exact B788515
  · exact B788519
  · exact B788523
  · exact B788527
  · exact B788531
  · exact B788535
  · exact B788539
  · exact B788543
  · exact B788547
  · exact B788551
  · exact B788555
  · exact B788559
  · exact B788563
  · exact B788567
  · exact B788571
  · exact B788575
  · exact B788579
  · exact B788583
  · exact B788587
  · exact B788591
  · exact B788595
  · exact B788599
  · exact B788603
  · exact B788607
  · exact B788611
  · exact B788615
  · exact B788619
  · exact B788623
  · exact B788627
  · exact B788631
  · exact B788635
  · exact B788639
  · exact B788643
  · exact B788647
  · exact B788651
  · exact B788655
  · exact B788659
  · exact B788663
  · exact B788667
  · exact B788671
  · exact B788675
  · exact B788679
  · exact B788683
  · exact B788687
  · exact B788691
  · exact B788695
  · exact B788699
  · exact B788703
  · exact B788707
  · exact B788711
  · exact B788715
  · exact B788719
  · exact B788723
  · exact B788727
  · exact B788731
  · exact B788735
  · exact B788739
  · exact B788743
  · exact B788747
  · exact B788751
  · exact B788755
  · exact B788759
  · exact B788763
  · exact B788767
  · exact B788771
  · exact B788775
  · exact B788779
  · exact B788783
  · exact B788787
  · exact B788791
  · exact B788795
  · exact B788799
  · exact B788803
  · exact B788807
  · exact B788811
  · exact B788815
  · exact B788819
  · exact B788823
  · exact B788827
  · exact B788831
  · exact B788835
  · exact B788839
  · exact B788843
  · exact B788847
  · exact B788851
  · exact B788855
  · exact B788859
  · exact B788863
  · exact B788867
  · exact B788871
  · exact B788875
  · exact B788879
  · exact B788883
  · exact B788887
  · exact B788891
  · exact B788895
  · exact B788899
  · exact B788903
  · exact B788907
  · exact B788911
  · exact B788915
  · exact B788919
  · exact B788923
  · exact B788927
  · exact B788931
  · exact B788935
  · exact B788939
  · exact B788943
  · exact B788947
  · exact B788951
  · exact B788955
  · exact B788959
  · exact B788963
  · exact B788967
  · exact B788971
  · exact B788975
  · exact B788979
  · exact B788983
  · exact B788987
  · exact B788991
  · exact B788995
  · exact B788999
  · exact B789003
  · exact B789007
  · exact B789011
  · exact B789015
  · exact B789019
  · exact B789023
  · exact B789027
  · exact B789031
  · exact B789035
  · exact B789039
  · exact B789043
  · exact B789047
  · exact B789051
  · exact B789055
  · exact B789059
  · exact B789063
  · exact B789067
  · exact B789071
  · exact B789075
  · exact B789079
  · exact B789083
  · exact B789087
  · exact B789091
  · exact B789095
  · exact B789099
  · exact B789103
  · exact B789107
  · exact B789111
  · exact B789115
  · exact B789119
  · exact B789123
  · exact B789127
  · exact B789131
  · exact B789135

theorem C1 (j : ℕ) (h1 : 197284 ≤ j) (h2 : j ≤ 197584) : Blo 786339 (4 * j + 3) := by
  interval_cases j
  · exact B789139
  · exact B789143
  · exact B789147
  · exact B789151
  · exact B789155
  · exact B789159
  · exact B789163
  · exact B789167
  · exact B789171
  · exact B789175
  · exact B789179
  · exact B789183
  · exact B789187
  · exact B789191
  · exact B789195
  · exact B789199
  · exact B789203
  · exact B789207
  · exact B789211
  · exact B789215
  · exact B789219
  · exact B789223
  · exact B789227
  · exact B789231
  · exact B789235
  · exact B789239
  · exact B789243
  · exact B789247
  · exact B789251
  · exact B789255
  · exact B789259
  · exact B789263
  · exact B789267
  · exact B789271
  · exact B789275
  · exact B789279
  · exact B789283
  · exact B789287
  · exact B789291
  · exact B789295
  · exact B789299
  · exact B789303
  · exact B789307
  · exact B789311
  · exact B789315
  · exact B789319
  · exact B789323
  · exact B789327
  · exact B789331
  · exact B789335
  · exact B789339
  · exact B789343
  · exact B789347
  · exact B789351
  · exact B789355
  · exact B789359
  · exact B789363
  · exact B789367
  · exact B789371
  · exact B789375
  · exact B789379
  · exact B789383
  · exact B789387
  · exact B789391
  · exact B789395
  · exact B789399
  · exact B789403
  · exact B789407
  · exact B789411
  · exact B789415
  · exact B789419
  · exact B789423
  · exact B789427
  · exact B789431
  · exact B789435
  · exact B789439
  · exact B789443
  · exact B789447
  · exact B789451
  · exact B789455
  · exact B789459
  · exact B789463
  · exact B789467
  · exact B789471
  · exact B789475
  · exact B789479
  · exact B789483
  · exact B789487
  · exact B789491
  · exact B789495
  · exact B789499
  · exact B789503
  · exact B789507
  · exact B789511
  · exact B789515
  · exact B789519
  · exact B789523
  · exact B789527
  · exact B789531
  · exact B789535
  · exact B789539
  · exact B789543
  · exact B789547
  · exact B789551
  · exact B789555
  · exact B789559
  · exact B789563
  · exact B789567
  · exact B789571
  · exact B789575
  · exact B789579
  · exact B789583
  · exact B789587
  · exact B789591
  · exact B789595
  · exact B789599
  · exact B789603
  · exact B789607
  · exact B789611
  · exact B789615
  · exact B789619
  · exact B789623
  · exact B789627
  · exact B789631
  · exact B789635
  · exact B789639
  · exact B789643
  · exact B789647
  · exact B789651
  · exact B789655
  · exact B789659
  · exact B789663
  · exact B789667
  · exact B789671
  · exact B789675
  · exact B789679
  · exact B789683
  · exact B789687
  · exact B789691
  · exact B789695
  · exact B789699
  · exact B789703
  · exact B789707
  · exact B789711
  · exact B789715
  · exact B789719
  · exact B789723
  · exact B789727
  · exact B789731
  · exact B789735
  · exact B789739
  · exact B789743
  · exact B789747
  · exact B789751
  · exact B789755
  · exact B789759
  · exact B789763
  · exact B789767
  · exact B789771
  · exact B789775
  · exact B789779
  · exact B789783
  · exact B789787
  · exact B789791
  · exact B789795
  · exact B789799
  · exact B789803
  · exact B789807
  · exact B789811
  · exact B789815
  · exact B789819
  · exact B789823
  · exact B789827
  · exact B789831
  · exact B789835
  · exact B789839
  · exact B789843
  · exact B789847
  · exact B789851
  · exact B789855
  · exact B789859
  · exact B789863
  · exact B789867
  · exact B789871
  · exact B789875
  · exact B789879
  · exact B789883
  · exact B789887
  · exact B789891
  · exact B789895
  · exact B789899
  · exact B789903
  · exact B789907
  · exact B789911
  · exact B789915
  · exact B789919
  · exact B789923
  · exact B789927
  · exact B789931
  · exact B789935
  · exact B789939
  · exact B789943
  · exact B789947
  · exact B789951
  · exact B789955
  · exact B789959
  · exact B789963
  · exact B789967
  · exact B789971
  · exact B789975
  · exact B789979
  · exact B789983
  · exact B789987
  · exact B789991
  · exact B789995
  · exact B789999
  · exact B790003
  · exact B790007
  · exact B790011
  · exact B790015
  · exact B790019
  · exact B790023
  · exact B790027
  · exact B790031
  · exact B790035
  · exact B790039
  · exact B790043
  · exact B790047
  · exact B790051
  · exact B790055
  · exact B790059
  · exact B790063
  · exact B790067
  · exact B790071
  · exact B790075
  · exact B790079
  · exact B790083
  · exact B790087
  · exact B790091
  · exact B790095
  · exact B790099
  · exact B790103
  · exact B790107
  · exact B790111
  · exact B790115
  · exact B790119
  · exact B790123
  · exact B790127
  · exact B790131
  · exact B790135
  · exact B790139
  · exact B790143
  · exact B790147
  · exact B790151
  · exact B790155
  · exact B790159
  · exact B790163
  · exact B790167
  · exact B790171
  · exact B790175
  · exact B790179
  · exact B790183
  · exact B790187
  · exact B790191
  · exact B790195
  · exact B790199
  · exact B790203
  · exact B790207
  · exact B790211
  · exact B790215
  · exact B790219
  · exact B790223
  · exact B790227
  · exact B790231
  · exact B790235
  · exact B790239
  · exact B790243
  · exact B790247
  · exact B790251
  · exact B790255
  · exact B790259
  · exact B790263
  · exact B790267
  · exact B790271
  · exact B790275
  · exact B790279
  · exact B790283
  · exact B790287
  · exact B790291
  · exact B790295
  · exact B790299
  · exact B790303
  · exact B790307
  · exact B790311
  · exact B790315
  · exact B790319
  · exact B790323
  · exact B790327
  · exact B790331
  · exact B790335
  · exact B790339

theorem solution (m : ℕ) (hlo : 786339 ≤ m) (hhi : m ≤ 790339) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 196584 ≤ j := by omega
    have hj2 : j ≤ 197584 := by omega
    have hb : Blo 786339 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 197284 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
